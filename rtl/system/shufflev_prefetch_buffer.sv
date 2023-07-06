
module shufflev_prefetch_buffer import ibex_pkg::*; #(
  parameter bit             ResetAll          = 1'b0,
  parameter int unsigned    ShuffleBuffSize   = 4,
  parameter int unsigned    NumPhysicalRegs   = 64,
  parameter shufflev_rng_e  RngType           = RandomTkacik,
  parameter int unsigned    RngSeed           = 123456,
  parameter bit             EnableFetchId     = 1'b0,
  parameter bit             EnableFastBranch  = 1'b1
) (
  input  logic        clk_i,
  input  logic        rst_ni,   // asynchronous reset

  input  logic        req_i,    // logic high while the core is awake otherwise false
                                // we ignore req_i and fill the fetch buffer anyway until it is full

  input  logic        branch_i, // assert when the core want to change PC (branch, jump, exception, etc.)
  input  logic [31:0] addr_i,

  input  logic        ready_i, 
  output logic        valid_o,
  output logic        is_compress_o,
  output logic [31:0] rdata_o,
  output logic [NumPhysicalRegsNumBits-1:0] rdata_rd_o,
  output logic [NumPhysicalRegsNumBits-1:0] rdata_rs1_o,
  output logic [NumPhysicalRegsNumBits-1:0] rdata_rs2_o,
  output logic [31:0] addr_o,
  output logic        err_o,        
  output logic        err_plus2_o,  // error is caused by the second half of an unaligned uncompressed instruction

  // goes to instruction memory / instruction cache
  output logic        instr_req_o,
  input  logic        instr_gnt_i,
  output logic [31:0] instr_addr_o,
  input  logic [31:0] instr_rdata_i,
  input  logic        instr_err_i,
  input  logic        instr_rvalid_i,

  // Prefetch Buffer Status
  output logic        busy_o    // avoid clock gate
);

  localparam int unsigned ShuffleBuffSizeNumBits = $clog2(ShuffleBuffSize);
  localparam int unsigned NumPhysicalRegsNumBits = $clog2(NumPhysicalRegs);
  localparam int unsigned NumLogicalRegs = 32;
  localparam int unsigned NumLogicalRegsNumBits = 5; // RV32I contains 32 logical register

  /* Instantiate ibex prefetch buffer */

  logic         ibex_prefetch_buffer_ready_i;
  logic         ibex_prefetch_buffer_valid_o;
  logic [31:0]  ibex_prefetch_buffer_rdata_o;
  logic [31:0]  ibex_prefetch_buffer_addr_o;

  ibex_prefetch_buffer #(
    .ResetAll          (ResetAll)
  ) u_ibex_prefetch_buffer (
      .clk_i             (clk_i),
      .rst_ni            (rst_ni),
      .req_i             (req_i),

      .branch_i          (branch_i),
      .addr_i            (addr_i),

      .ready_i           (ibex_prefetch_buffer_ready_i),
      .valid_o           (ibex_prefetch_buffer_valid_o),
      .rdata_o           (ibex_prefetch_buffer_rdata_o),
      .addr_o            (ibex_prefetch_buffer_addr_o),
      .err_o             (),
      .err_plus2_o       (),
      // goes to instruction memory / instruction cache
      .instr_req_o       (instr_req_o),
      .instr_gnt_i       (instr_gnt_i),
      .instr_addr_o      (instr_addr_o),
      .instr_rdata_i     (instr_rdata_i),
      .instr_err_i       (instr_err_i),
      .instr_rvalid_i    (instr_rvalid_i),
      // Prefetch Buffer Status
      .busy_o            (busy_o)
  );

  /* Expand compress instruction as our shuffling logic only deal with uncompress instruction */

  logic [31:0] prefetch_buffer_rdata_uncompress;
  logic        prefetch_buffer_rdata_is_compress;

  ibex_compressed_decoder u_ibex_compressed_decoder (
      .clk_i              (clk_i),
      .rst_ni             (rst_ni),
      .valid_i            (ibex_prefetch_buffer_valid_o),
      .instr_i            (ibex_prefetch_buffer_rdata_o),
      .instr_o            (prefetch_buffer_rdata_uncompress),
      .is_compressed_o    (prefetch_buffer_rdata_is_compress),
      .illegal_instr_o    ()
  );

  /* Check instruction type and generate signal to halt/resume reading from prefetch buffer */

  logic prefetch_buffer_rdata_branch_or_jump;  // a signal to indicate whether the current instruction (head of prefetch buffer) may change the PC 
  assign prefetch_buffer_rdata_branch_or_jump = (prefetch_buffer_rdata_uncompress[6:0] == 7'b1101111) // jal
                                                  || (prefetch_buffer_rdata_uncompress[6:0] == 7'b1100111) // jalr
                                                  || (prefetch_buffer_rdata_uncompress[6:0] == 7'b1100011) // bxxx
                                                  || (prefetch_buffer_rdata_uncompress[6:0] == 7'b0001111) // fench
                                                  || (prefetch_buffer_rdata_uncompress[6:0] == 7'b1110011 
                                                      && prefetch_buffer_rdata_uncompress[14:12] == 3'd0
                                                      && (prefetch_buffer_rdata_uncompress[22:21] == 2'b00         // ecall / ebreak
                                                          || prefetch_buffer_rdata_uncompress[22:21] == 2'b01));   // sret / mret TODO: check sfence.vma  

  logic prefetch_buffer_rdata_load_or_store;
  assign prefetch_buffer_rdata_load_or_store = (prefetch_buffer_rdata_uncompress[6:0] == 7'b0000011)  // load 
                                            || (prefetch_buffer_rdata_uncompress[6:0] == 7'b0100011); // store
  
  logic prefetch_buffer_rdata_synch_env_csr;
  assign prefetch_buffer_rdata_synch_env_csr = (prefetch_buffer_rdata_uncompress[6:0] == 7'b1110011) || (prefetch_buffer_rdata_uncompress[6:0] == 7'b0001111);

  logic         discard_prefetch_buffer_d, discard_prefetch_buffer_q; // assert to prevent reading from the prefetch buffer as the previous instruction may change PC
  logic [31:0]  latest_branch_pc_d, latest_branch_pc_q;               // address of the last branch instruction that assert `discard_prefetch_buffer_q`
  logic         latest_branch_pc_just_executed_d, latest_branch_pc_just_executed_q; // assert to indicate that the last instruction recieved by the ID/EX stage matches `latest_branch_pc_q`
  
  logic         latest_branch_not_taken;  // assert to indicate that the last branch instruction executed by the ID/EX stage doesn't caused the PC to change (use for deassert `discard_prefetch_buffer_q`)
  assign latest_branch_not_taken = latest_branch_pc_just_executed_q && ready_i;     // ID/EX stage deasserts ready_i when the last received instruction is going to change PC e.g. taken branch, jump, etc.

  always_comb begin
    discard_prefetch_buffer_d = discard_prefetch_buffer_q;
    latest_branch_pc_d = latest_branch_pc_q;

    latest_branch_pc_just_executed_d = ready_i && valid_o && (addr_o == latest_branch_pc_q);

    // deassert `discard_prefetch_buffer_q` when 
    // 1) the ID/EX stage has determined the new PC value and has sent request to the prefetch buffer via `branch_i` and `addr_i` signals
    // or 2) the lastest branch doesn't caused the PC value to change
    if (branch_i) begin
      discard_prefetch_buffer_d = 1'b0;
    end else if (latest_branch_not_taken) begin
      discard_prefetch_buffer_d = 1'b0;
    end

    // assert `discard_prefetch_buffer_q` when the current instruction that is being retrieved from the prefetch buffer may change the PC value 
    // Note: we use a separate if statement since asserting `discard_prefetch_buffer_q` has higher precedence than deasserting e.g. when there
    // is a branch instruction right after another branch instruction
    if (prefetch_buffer_rdata_branch_or_jump && ibex_prefetch_buffer_ready_i) begin
      discard_prefetch_buffer_d = 1'b1;
      latest_branch_pc_d = ibex_prefetch_buffer_addr_o;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      discard_prefetch_buffer_q <= 1'b0;
    end else begin
      discard_prefetch_buffer_q <= discard_prefetch_buffer_d;
      latest_branch_pc_q <=latest_branch_pc_d;
      latest_branch_pc_just_executed_q <= latest_branch_pc_just_executed_d;
    end
  end

  /* Detect branch request due to interrupt or exception */

  logic branch_i_q;
  logic latest_branch_pc_just_executed_q2;
  
  always_ff @(posedge clk_i) begin
    branch_i_q <= branch_i;
    latest_branch_pc_just_executed_q2 <= latest_branch_pc_just_executed_q;
  end

  // branch_i will be asserted in the next cycle after jump instruction is sent to the ID/EX stage and in the next two cycle in case of a branch instruction.
  // branch_i will not be asserted in two consecutive cycle because when branch is taken, we must get the new PC, fetch new instruction and sent to ID/EX
  // TODO: can interrupt happen in the cycle that we expect branch?
  logic interrupt_or_exception_jump_request;
  assign interrupt_or_exception_jump_request = (branch_i && branch_i_q) || (branch_i && !latest_branch_pc_just_executed_q && !latest_branch_pc_just_executed_q2);

  /* Detect and handler wfi instruction */

  logic         pre_fetch_inst_is_wfi;  // assert when the previous instruction retrieve from the prefetch buffer is the wfi instruction
  logic [31:0]  next_pc_after_wfi;      // record the pc value of the instruction after wfi

  always_ff @(posedge clk_i) begin
    if (prefetch_buffer_to_inst_buffer) begin
      pre_fetch_inst_is_wfi <= (prefetch_buffer_rdata_uncompress == 32'h1050_0073);
    end
    if (pre_fetch_inst_is_wfi) begin
      next_pc_after_wfi <= ibex_prefetch_buffer_addr_o;
    end
  end

  logic prev_inst_to_idex_is_wfi;   // After the wfi instruction is executed, the core will be sleep until interrupt occur which will assert branch_i to jump to ISR
                                    // In the same cycle that branch_i is asserted, the core will record the PC value to mepc so that it knows where to return after MRET
                                    // Thus, we need to force addr_o to be the next PC value after the wfi instruction instead of some random instructions from the instruction buffer

  always_ff @(posedge clk_i) begin
    if (ready_i && valid_o) begin
      prev_inst_to_idex_is_wfi <= (rdata_o == 32'h1050_0073);
    end
    if (branch_i) begin
      prev_inst_to_idex_is_wfi <= 1'b0;
    end
  end

  /* Transfer from prefetch buffer to shuffling buffer (inst_buffer_...) and from shuffling buffer to the ID/EX stage */

  logic [ShuffleBuffSize-1:0] [31:0]    inst_buffer_addr_d, inst_buffer_addr_q;               // PC value
  logic [ShuffleBuffSize-1:0] [31:0]    inst_buffer_data_d, inst_buffer_data_q;               // uncompress instruction to be sent to the ID/EX stage
  logic [ShuffleBuffSize-1:0]           inst_buffer_is_compress_d, inst_buffer_is_compress_q; // indicate whether the instruction is originally a compress instruction or not
  logic [ShuffleBuffSize-1:0]           inst_buffer_valid_d, inst_buffer_valid_q;             // indicate whether the entry in the buffer is valid or not

  logic                       inst_buffer_full, inst_buffer_not_empty;
  assign inst_buffer_full = &inst_buffer_valid_q;
  assign inst_buffer_not_empty = |inst_buffer_valid_q;

  // retrieve new instruction from the prefetch buffer when the prefetch buffer has valid data, the instruction buffer is not full and `discard_prefetch_buffer_q` is not asserted
  // Note:
  // - we still accept new instruction when the instruction buffer is full if one entry is being removed (ready_i and valid_o are both asserted)
  // - we ignore `discard_prefetch_buffer_q` when `latest_branch_not_taken` is asserted to avoid waiting for `discard_prefetch_buffer_q` to be deasserted in the next clock cycle
  //   this additional or-gate is optional but can help improve performance
  // TODO: test the case when branch_i is assert due to exception or interrupt
  logic prefetch_buffer_to_inst_buffer;
  assign prefetch_buffer_to_inst_buffer = !branch_i && ibex_prefetch_buffer_valid_o && (!inst_buffer_full || (ready_i && valid_o)) && (!discard_prefetch_buffer_q || latest_branch_not_taken);

  logic inst_buffer_to_id_ex;
  assign inst_buffer_to_id_ex = ready_i && valid_o;

  always_comb begin
    for (int i=0; i<ShuffleBuffSize; i++) begin
      inst_buffer_addr_d[i] = inst_buffer_addr_q[i];
      inst_buffer_data_d[i] = inst_buffer_data_q[i];
      inst_buffer_is_compress_d[i] = inst_buffer_is_compress_q[i];
      inst_buffer_valid_d[i] = inst_buffer_valid_q[i];
    end

    ibex_prefetch_buffer_ready_i = 1'b0;

    // flush the instruction buffer when received branch request (branch_i=1) due to interrupt or exception
    if (interrupt_or_exception_jump_request) begin
      for (int i=0; i<ShuffleBuffSize; i++) begin
        inst_buffer_valid_d[i] = 1'b0;
      end
    end

    // remove entry from the instruction buffer after it was sent to the ID/EX stage. we should remove the instruction first before adding a new one 
    // as start_ptr and end_ptr may point to the same entry and the valid bit should end up being set when we remove and add instruction in the same cycle
    if (inst_buffer_to_id_ex) begin
      inst_buffer_valid_d[inst_buffer_remove_index] = 1'b0;
    end

    // retrieve new instruction from the prefetch buffer
    if (prefetch_buffer_to_inst_buffer) begin
      ibex_prefetch_buffer_ready_i = 1'b1;
      inst_buffer_addr_d[inst_buffer_insert_index] = ibex_prefetch_buffer_addr_o;
      inst_buffer_data_d[inst_buffer_insert_index] = prefetch_buffer_rdata_uncompress;
      inst_buffer_is_compress_d[inst_buffer_insert_index] = prefetch_buffer_rdata_is_compress;
      inst_buffer_valid_d[inst_buffer_insert_index] = 1'b1;
    end
  end

  // outputs to the ID/EX stage
  assign valid_o = (inst_buffer_full || (inst_buffer_not_empty && discard_prefetch_buffer_q)) && !branch_i && random_number_valid;  // instruction buffer may not be full if we are currently awaiting branch outcome
  assign is_compress_o = inst_buffer_is_compress_q[inst_buffer_remove_index];
  assign rdata_o = inst_buffer_data_q[inst_buffer_remove_index];
  assign rdata_rd_o = inst_buffer_rd_physical_q[inst_buffer_remove_index];
  assign rdata_rs1_o = inst_buffer_rs1_physical_q[inst_buffer_remove_index];
  assign rdata_rs2_o = inst_buffer_rs2_physical_q[inst_buffer_remove_index];
  assign addr_o = prev_inst_to_idex_is_wfi ? next_pc_after_wfi : inst_buffer_addr_q[inst_buffer_remove_index];  // see comment above regarding prev_inst_to_idex_is_wfi
  assign err_o = 1'b0;
  assign err_plus2_o = 1'b0;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      for (int i=0; i<ShuffleBuffSize; i++) begin
        inst_buffer_valid_q[i] <= 1'b0;
      end
    end else begin
      for (int i=0; i<ShuffleBuffSize; i++) begin
        inst_buffer_addr_q[i] <= inst_buffer_addr_d[i];
        inst_buffer_data_q[i] <= inst_buffer_data_d[i];
        inst_buffer_is_compress_q[i] <= inst_buffer_is_compress_d[i];
        inst_buffer_valid_q[i] <= inst_buffer_valid_d[i];
      end
    end
  end

  /* Dependency tracking logic */

  logic [NumLogicalRegsNumBits-1:0] current_uncompressed_opcode_rd, current_uncompressed_opcode_rs1, current_uncompressed_opcode_rs2;
  assign current_uncompressed_opcode_rd = prefetch_buffer_rdata_uncompress[11:7];
  assign current_uncompressed_opcode_rs1 = prefetch_buffer_rdata_uncompress[19:15];
  assign current_uncompressed_opcode_rs2 = prefetch_buffer_rdata_uncompress[24:20];

  logic current_uncompressed_opcode_has_rd, current_uncompressed_opcode_has_rs1, current_uncompressed_opcode_has_rs2;
  assign current_uncompressed_opcode_has_rd = (prefetch_buffer_rdata_uncompress[6:2] != 5'b11000) // B-type
                                           && (prefetch_buffer_rdata_uncompress[6:2] != 5'b01000) // S-type
                                           && (prefetch_buffer_rdata_uncompress[6:2] != 5'b00011) // fence
                                           && !((prefetch_buffer_rdata_uncompress[6:2] == 5'b11100) 
                                                && (prefetch_buffer_rdata_uncompress[14:12] == 3'b000)); // ecall/ebreak 
  assign current_uncompressed_opcode_has_rs1 = (prefetch_buffer_rdata_uncompress[6:2] != 5'b01101) // lui
                                            && (prefetch_buffer_rdata_uncompress[6:2] != 5'b00101) // auipc
                                            && (prefetch_buffer_rdata_uncompress[6:2] != 5'b11011) // jal
                                            && (prefetch_buffer_rdata_uncompress[6:2] != 5'b00011) // fence
                                            && !((prefetch_buffer_rdata_uncompress[6:2] == 5'b11100) 
                                                && (prefetch_buffer_rdata_uncompress[14:12] == 3'b000 || // ecall/ebreak
                                                    prefetch_buffer_rdata_uncompress[14:12] == 3'b101 || // csrrwi
                                                    prefetch_buffer_rdata_uncompress[14:12] == 3'b110 || // csrrsi
                                                    prefetch_buffer_rdata_uncompress[14:12] == 3'b111)); // csrrci
  assign current_uncompressed_opcode_has_rs2 = (prefetch_buffer_rdata_uncompress[6:2] == 5'b11000)  // B-type
                                            || (prefetch_buffer_rdata_uncompress[6:2] == 5'b01000)  // S-type
                                            || (prefetch_buffer_rdata_uncompress[6:2] == 5'b01100); // R-type

  logic [ShuffleBuffSize-1:0] [NumPhysicalRegsNumBits-1:0] inst_buffer_rd_physical_d, inst_buffer_rd_physical_q;     // physical RD index (binary format)
  logic [ShuffleBuffSize-1:0] [NumPhysicalRegsNumBits-1:0] inst_buffer_rs1_physical_d, inst_buffer_rs1_physical_q;   // physical RS1 index (binary format)
  logic [ShuffleBuffSize-1:0] [NumPhysicalRegsNumBits-1:0] inst_buffer_rs2_physical_d, inst_buffer_rs2_physical_q;   // physical RS2 index (binary format)
  logic [ShuffleBuffSize-1:0] [NumPhysicalRegs-1:0]         inst_buffer_physical_reg_usage_d, inst_buffer_physical_reg_usage_q; // indicate which physical register is begin used by this instruction (bit vector format)
  logic [ShuffleBuffSize-1:0] [ShuffleBuffSize-1:0]                     inst_buffer_dependency_d, inst_buffer_dependency_q;       // indicate which instruction does this instruction depends on
  logic [ShuffleBuffSize-1:0]                                 inst_buffer_may_change_pc_d, inst_buffer_may_change_pc_q; // indicate whether this instruction may change PC value (branch, jump, etc.)
  logic [ShuffleBuffSize-1:0]                                 inst_buffer_is_load_store_d, inst_buffer_is_load_store_q; // indicate whether this instruction is a load/store
  logic [ShuffleBuffSize-1:0]                                 inst_buffer_is_env_csr_d, inst_buffer_is_env_csr_q;       // indicate whether this instruction is an environment/csr instruction (ecall/ebreak/csr.../wfi)

  logic [NumLogicalRegs-1:0] [NumPhysicalRegsNumBits-1:0] logical_to_physical_reg_d, logical_to_physical_reg_q; // store the mapping between logical to physical register (binary format)
  logic [NumPhysicalRegs-1:0]                                physical_reg_reserved_d, physical_reg_reserved_q;     // keep track of physical registers currently reserved
                                                                                                                     // (this contain identical data to logical_to_physical_reg_* but in bit vector format)
                                                                                                                            

  // find the first avilable physical register by performing OR between physical_reg_reserved_q and each element of inst_buffer_physical_reg_usage_q and find the index of the rightmost 0
  // we perform OR because some physical registers might not be reserved currently but they stores data refer to by some instructions in the inst_buffer thus is not available
  logic [NumPhysicalRegs-1:0]         physical_reg_in_used;
  logic [NumPhysicalRegsNumBits-1:0] first_available_physical_reg_id;
  always_comb begin
    physical_reg_in_used = physical_reg_reserved_q;
    for (int i=0; i<ShuffleBuffSize; i++) begin
      // we can avoid AND with the valid bit as `inst_buffer_physical_reg_usage_` is clear when the instruction is removed from the buffer
      physical_reg_in_used |= inst_buffer_physical_reg_usage_q[i] /*& {NumPhysicalRegs{inst_buffer_valid_q[i]}}*/; 
    end

    first_available_physical_reg_id = 'd0;
    for (int i=NumPhysicalRegs-1; i>=0; i--) begin
      if (!physical_reg_in_used[i]) begin
        first_available_physical_reg_id = NumPhysicalRegsNumBits'(i);
      end
    end
  end

  always_comb begin
    for (int i=0; i<ShuffleBuffSize; i++) begin
      inst_buffer_rd_physical_d[i] = inst_buffer_rd_physical_q[i];
      inst_buffer_rs1_physical_d[i] = inst_buffer_rs1_physical_q[i];
      inst_buffer_rs2_physical_d[i] = inst_buffer_rs2_physical_q[i];
      inst_buffer_physical_reg_usage_d[i] = inst_buffer_physical_reg_usage_q[i];
      inst_buffer_dependency_d[i] = inst_buffer_dependency_q[i];
      inst_buffer_may_change_pc_d[i] = inst_buffer_may_change_pc_q[i];
      inst_buffer_is_load_store_d[i] = inst_buffer_is_load_store_q[i];
      inst_buffer_is_env_csr_d[i] = inst_buffer_is_env_csr_q[i];
    end
    for (int i=0; i<NumLogicalRegs; i++) begin
      logical_to_physical_reg_d[i] = logical_to_physical_reg_q[i];
    end
    physical_reg_reserved_d = physical_reg_reserved_q;

    if (interrupt_or_exception_jump_request) begin
      for (int i=0; i<ShuffleBuffSize; i++) begin
        inst_buffer_physical_reg_usage_d[i] = 'd0;
      end
    end

    if (inst_buffer_to_id_ex) begin
      // clear inst_buffer_physical_reg_usage_ so the system known which physical register is not being refer to by instruction in the instruction buffer 
      inst_buffer_physical_reg_usage_d[inst_buffer_remove_index] = 'd0;
      // clear the dependency bit of other instructions that depends on this instruction
      for (int i=0; i<ShuffleBuffSize; i++) begin
        inst_buffer_dependency_d[i][inst_buffer_remove_index] = 1'b0;
      end
    end
    
    if (prefetch_buffer_to_inst_buffer) begin
      // reserve new physical register for RD if needed
      if (current_uncompressed_opcode_has_rd && (current_uncompressed_opcode_rd != 'd0)) begin
        inst_buffer_rd_physical_d[inst_buffer_insert_index] = first_available_physical_reg_id;

        physical_reg_reserved_d[logical_to_physical_reg_d[current_uncompressed_opcode_rd]] = 1'b0;
        logical_to_physical_reg_d[current_uncompressed_opcode_rd] = first_available_physical_reg_id;
        physical_reg_reserved_d[first_available_physical_reg_id] = 1'b1;
      end else begin
        inst_buffer_rd_physical_d[inst_buffer_insert_index] = 'd0;
      end
      // rename rs1, rs2
      inst_buffer_rs1_physical_d[inst_buffer_insert_index] = current_uncompressed_opcode_has_rs1 ? logical_to_physical_reg_q[current_uncompressed_opcode_rs1] : 'd0;
      inst_buffer_rs2_physical_d[inst_buffer_insert_index] = current_uncompressed_opcode_has_rs2 ? logical_to_physical_reg_q[current_uncompressed_opcode_rs2] : 'd0;
      // store physical register usage in bit vector format
      inst_buffer_physical_reg_usage_d[inst_buffer_insert_index] = (1 << inst_buffer_rd_physical_d[inst_buffer_insert_index]) | 
                                                                (1 << inst_buffer_rs1_physical_d[inst_buffer_insert_index]) | 
                                                                (1 << inst_buffer_rs2_physical_d[inst_buffer_insert_index]);
      
      // check which instructions that this instruction depends on
      inst_buffer_dependency_d[inst_buffer_insert_index] = 'd0;
      for (int i=0; i<ShuffleBuffSize; i++) begin
        // TODO: handle syscall (rd2) and ecall/ebreak
        if (inst_buffer_valid_q[i]) begin
          if ((inst_buffer_rd_physical_q[i] != 'd0) && (inst_buffer_rd_physical_q[i] == inst_buffer_rs1_physical_d[inst_buffer_insert_index]
                                                      || inst_buffer_rd_physical_q[i] == inst_buffer_rs2_physical_d[inst_buffer_insert_index])) begin
            inst_buffer_dependency_d[inst_buffer_insert_index][i] = 1'b1;
          end
          // all load/store should be done in order
          if (inst_buffer_is_load_store_q[i] && prefetch_buffer_rdata_load_or_store) begin
            inst_buffer_dependency_d[inst_buffer_insert_index][i] = 1'b1;
          end
          // all synchronization/environment/csr instructions should be executed after all prior instructions has been completed
          if (prefetch_buffer_rdata_synch_env_csr) begin
            inst_buffer_dependency_d[inst_buffer_insert_index][i] = 1'b1;
          end
          // all instruction after synchronization/environment/csr instruction should be executed after the synchronization/environment/csr instruction
          if (inst_buffer_is_env_csr_q[i]) begin
            inst_buffer_dependency_d[inst_buffer_insert_index][i] = 1'b1;
          end
        end
      end 
      // do not depend on ourself (checking the valid bit in the for-loop is not enough as old instruction can be removed and new instruction can be added in the same cycle)
      inst_buffer_dependency_d[inst_buffer_insert_index][inst_buffer_insert_index] = 1'b0;

      inst_buffer_may_change_pc_d[inst_buffer_insert_index] = prefetch_buffer_rdata_branch_or_jump;
      inst_buffer_is_load_store_d[inst_buffer_insert_index] = prefetch_buffer_rdata_load_or_store;
      inst_buffer_is_env_csr_d[inst_buffer_insert_index] = prefetch_buffer_rdata_synch_env_csr;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      for (int i=0; i<ShuffleBuffSize; i++) begin
        inst_buffer_physical_reg_usage_q[i] <= 'd0;
      end
      for (int i=0; i<NumLogicalRegs; i++) begin
        logical_to_physical_reg_q[i] <= NumPhysicalRegsNumBits'(i);
        physical_reg_reserved_q[i] <= 1'b1;
      end
      for (int i=NumLogicalRegs; i<NumPhysicalRegs; i++) begin
        physical_reg_reserved_q[i] <= 1'b0;
      end
    end else begin
      for (int i=0; i<ShuffleBuffSize; i++) begin
        inst_buffer_rd_physical_q[i] <= inst_buffer_rd_physical_d[i];
        inst_buffer_rs1_physical_q[i] <= inst_buffer_rs1_physical_d[i];
        inst_buffer_rs2_physical_q[i] <= inst_buffer_rs2_physical_d[i];
        inst_buffer_physical_reg_usage_q[i] <= inst_buffer_physical_reg_usage_d[i];
        inst_buffer_dependency_q[i] <= inst_buffer_dependency_d[i];
        inst_buffer_may_change_pc_q[i] <= inst_buffer_may_change_pc_d[i];
        inst_buffer_is_load_store_q[i] <= inst_buffer_is_load_store_d[i];
        inst_buffer_is_env_csr_q[i] <= inst_buffer_is_env_csr_d[i];
      end
      for (int i=0; i<NumLogicalRegs; i++) begin
        logical_to_physical_reg_q[i] <= logical_to_physical_reg_d[i];
      end
      for (int i=0; i<NumPhysicalRegs; i++) begin
        physical_reg_reserved_q[i] <= physical_reg_reserved_d[i];
      end
    end
  end  

  /* Random logic */ 

  logic [ShuffleBuffSize-1:0] [ShuffleBuffSize-1:0] [ShuffleBuffSizeNumBits-1:0] distance_table;   // the random number generated can't be used directly as an index to select an instruction in the instruction
                                                                      // buffer as it may point to an invalid entry (blank or awaiting dependent instruction etc.). Thus, we select
                                                                      // the closest entry instead using the absolute distance pre-computed in this table

  initial begin
    //          Random Number   0   1   2   3   4  
    //  ---------------------- --- --- --- --- --- 
    //   Entry (|Dist| = 0)     0   1   2   3   4  
    //   Entry (|Dist| = 1)     1   2   3   4   0  
    //   Entry (|Dist| = 1)     4   0   1   2   3  
    //   Entry (|Dist| = 2)     2   3   4   0   1  
    //   Entry (|Dist| = 2)     3   4   0   1   2  
    for (int c=0; c<ShuffleBuffSize; c++) begin
      distance_table[0][c] = ShuffleBuffSizeNumBits'(c);
      for (int i=0; i<$ceil((ShuffleBuffSize-1)/2.0); i++) begin          // odd rows:  0 +1 X +2 X ...
        distance_table[1 + (i*2)][c] = ShuffleBuffSizeNumBits'((c + (i+1)) % ShuffleBuffSize);
      end
      for (int i=0; i<(ShuffleBuffSize-1)/2; i++) begin                 // even rows: 0 X -1 X -2 ...
        distance_table[2 + (i*2)][c] = ShuffleBuffSizeNumBits'((c - (i+1)) >= 0 ? (c - (i+1)) : (c + ShuffleBuffSize - (i+1)));
      end
    end
    // // log the content of the distance table
    // for (int c=0; c<ShuffleBuffSize; c++) begin
    //   $display("Column %0h", c);
    //   for (int r=0; r<ShuffleBuffSize; r++) begin
    //     $display(distance_table[r][c]);
    //   end
    // end
  end

  logic [ShuffleBuffSizeNumBits-1:0]   random_number;                  // random number used for selecting one column from the distance table
  logic                       random_number_valid;

  shufflev_rng #(
    .RngType    (RngType),
    .RngSeed    (RngSeed),
    .MaxValue   (ShuffleBuffSize-1)
  ) u_shufflev_rng (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .number_o   (random_number),
    .valid_o    (random_number_valid)
  );

  logic [ShuffleBuffSize-1:0]           random_valid_entry;             // bit vector indicating all ready entries in the instruction buffer
                                                              // the order of the bit follow the selected column in the distance table 
  logic [ShuffleBuffSizeNumBits-1:0]   random_first_valid_entry_index; // index in the `random_valid_entry` that are closest and valid 
  logic [ShuffleBuffSizeNumBits-1:0]   inst_buffer_remove_index;       // index of the instruction buffer to retrieve instruction and send to the ID/EX stage

  always_comb begin
    for (int i=0; i<ShuffleBuffSize; i++) begin
      random_valid_entry[i] = inst_buffer_valid_q[distance_table[i][random_number]] && !(|inst_buffer_dependency_q[distance_table[i][random_number]]); 
    end

    random_first_valid_entry_index = 'd0;
    for (int i=ShuffleBuffSize-1; i>=0; i--) begin
      if (random_valid_entry[i]) begin
        random_first_valid_entry_index = ShuffleBuffSizeNumBits'(i);
      end
    end
  end

  if (EnableFastBranch) begin
    logic [ShuffleBuffSize-1:0] inst_buffer_has_dependency;
    always_comb begin
      for (int i=0; i<ShuffleBuffSize; i++) begin
        inst_buffer_has_dependency[i] = |inst_buffer_dependency_q[i];
      end
    end

    logic [ShuffleBuffSize-1:0] inst_buffer_ready_branch;
    assign inst_buffer_ready_branch = inst_buffer_valid_q & ~inst_buffer_has_dependency & inst_buffer_may_change_pc_q;

    logic inst_buffer_has_ready_branch;
    assign inst_buffer_has_ready_branch = |inst_buffer_ready_branch;

    logic [ShuffleBuffSizeNumBits-1:0] inst_buffer_ready_branch_index;
    always_comb begin
      inst_buffer_ready_branch_index = 'd0;
      for (int i=ShuffleBuffSize-1; i>=0; i--) begin
        if (inst_buffer_ready_branch[i]) begin
          inst_buffer_ready_branch_index = ShuffleBuffSizeNumBits'(i);
        end
      end
    end

    assign inst_buffer_remove_index = inst_buffer_has_ready_branch ? inst_buffer_ready_branch_index : distance_table[random_first_valid_entry_index][random_number];
  end else begin
    assign inst_buffer_remove_index = distance_table[random_first_valid_entry_index][random_number];
  end

  logic [ShuffleBuffSizeNumBits-1:0]   inst_buffer_insert_index;      // index of the instruction buffer to insert new instruction into which will be identical to `inst_buffer_remove_index`
                                                             // if we are also removing an instruction in this cycle. Otherwise, we pick any unused entry (inst_buffer_valid_q[i] = 0)
                                                             // Note: checking the valid bit alone is not enough as the valid bit will not be updated until the next clock cycle which 
                                                             // prevent us from both removing and adding an instruction in the same cycle

  always_comb begin
    if (inst_buffer_to_id_ex) begin
      inst_buffer_insert_index = inst_buffer_remove_index;
    end else begin
      inst_buffer_insert_index = 'd0;
      for (int i=ShuffleBuffSize-1; i>=0; i--) begin
        if (!inst_buffer_valid_q[i]) begin
          inst_buffer_insert_index = ShuffleBuffSizeNumBits'(i);
        end
      end
    end
  end

  /* Debugging signals */

  /* verilator lint_off UNUSEDSIGNAL */
  logic [31:0] fetch_id_idex;
  /* verilator lint_off UNUSEDSIGNAL */

  if (EnableFetchId) begin
    logic [31:0]                fetch_id_d, fetch_id_q;
    logic [ShuffleBuffSize-1:0] [31:0]    inst_buffer_fetch_id_d, inst_buffer_fetch_id_q;       // unique sequential number for debugging purpose

    always_comb begin
      fetch_id_d = fetch_id_q;
      for (int i=0; i<ShuffleBuffSize; i++) begin
        inst_buffer_fetch_id_d[i] = inst_buffer_fetch_id_q[i];
      end

      if (prefetch_buffer_to_inst_buffer) begin
        inst_buffer_fetch_id_d[inst_buffer_insert_index] = fetch_id_q;
        fetch_id_d = fetch_id_q + 1;
      end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        fetch_id_q <= 'd0;
      end else begin
        fetch_id_q <= fetch_id_d;
        for (int i=0; i<ShuffleBuffSize; i++) begin
          inst_buffer_fetch_id_q[i] <= inst_buffer_fetch_id_d[i];
        end
      end
    end

    assign fetch_id_idex = inst_buffer_fetch_id_q[inst_buffer_remove_index];
  end else begin
    assign fetch_id_idex = 'd0;
  end

endmodule
