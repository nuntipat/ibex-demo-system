module shufflev_prefetch_buffer #(
  parameter bit ResetAll        = 1'b0,
  parameter int unsigned DEPTH  = 5,
  parameter int unsigned NUM_PHYSICAL_REGS = 64
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
  output logic [NUM_PHYSICAL_REGS_NUM_BIT-1:0] rdata_rd_o,
  output logic [NUM_PHYSICAL_REGS_NUM_BIT-1:0] rdata_rs1_o,
  output logic [NUM_PHYSICAL_REGS_NUM_BIT-1:0] rdata_rs2_o,
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

  localparam int unsigned DEPTH_NUM_BIT = $clog2(DEPTH);
  localparam int unsigned NUM_PHYSICAL_REGS_NUM_BIT = $clog2(NUM_PHYSICAL_REGS);
  localparam int unsigned NUM_LOGICAL_REGS = 32;
  localparam int unsigned NUM_LOGICAL_REGS_NUM_BIT = 5; // RV32I contains 32 logical register

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
                                                      && prefetch_buffer_rdata_uncompress[14:12] == 3'd0);  // ecall / ebreak

  logic prefetch_buffer_rdata_load_or_store;
  assign prefetch_buffer_rdata_load_or_store = (prefetch_buffer_rdata_uncompress[6:0] == 7'b0000011)  // load 
                                            || (prefetch_buffer_rdata_uncompress[6:0] == 7'b0100011); // store

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

  /* Transfer from prefetch buffer to shuffling buffer (inst_buffer_...) and from shuffling buffer to the ID/EX stage */

  logic [DEPTH-1:0] [31:0]    inst_buffer_addr_d, inst_buffer_addr_q;               // PC value
  logic [DEPTH-1:0] [31:0]    inst_buffer_data_d, inst_buffer_data_q;               // uncompress instruction to be sent to the ID/EX stage
  logic [DEPTH-1:0]           inst_buffer_is_compress_d, inst_buffer_is_compress_q; // indicate whether the instruction is originally a compress instruction or not
  logic [DEPTH-1:0]           inst_buffer_valid_d, inst_buffer_valid_q;             // indicate whether the entry in the buffer is valid or not
  logic [DEPTH_NUM_BIT-1:0]   inst_buffer_start_ptr_d, inst_buffer_start_ptr_q;     // TODO: replace with random logic
  logic [DEPTH_NUM_BIT-1:0]   inst_buffer_end_ptr_d, inst_buffer_end_ptr_q;         // TODO: replace with random logic

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
    for (int i=0; i<DEPTH; i++) begin
      inst_buffer_addr_d[i] = inst_buffer_addr_q[i];
      inst_buffer_data_d[i] = inst_buffer_data_q[i];
      inst_buffer_is_compress_d[i] = inst_buffer_is_compress_q[i];
      inst_buffer_valid_d[i] = inst_buffer_valid_q[i];
    end
    inst_buffer_start_ptr_d = inst_buffer_start_ptr_q;
    inst_buffer_end_ptr_d = inst_buffer_end_ptr_q;

    ibex_prefetch_buffer_ready_i = 1'b0;

    // remove entry from the instruction buffer after it was sent to the ID/EX stage. we should remove the instruction first before adding a new one 
    // as start_ptr and end_ptr may point to the same entry and the valid bit should end up being set when we remove and add instruction in the same cycle
    if (inst_buffer_to_id_ex) begin
      inst_buffer_valid_d[inst_buffer_start_ptr_q] = 1'b0;
      inst_buffer_start_ptr_d = inst_buffer_start_ptr_q + 'd1;
      if (inst_buffer_start_ptr_d == DEPTH_NUM_BIT'(DEPTH)) begin
        inst_buffer_start_ptr_d = 'd0;
      end
    end

    // retrieve new instruction from the prefetch buffer
    if (prefetch_buffer_to_inst_buffer) begin
      ibex_prefetch_buffer_ready_i = 1'b1;
      inst_buffer_addr_d[inst_buffer_end_ptr_q] = ibex_prefetch_buffer_addr_o;
      inst_buffer_data_d[inst_buffer_end_ptr_q] = prefetch_buffer_rdata_uncompress;
      inst_buffer_is_compress_d[inst_buffer_end_ptr_q] = prefetch_buffer_rdata_is_compress;
      inst_buffer_valid_d[inst_buffer_end_ptr_q] = 1'b1;
      inst_buffer_end_ptr_d = inst_buffer_end_ptr_q + 1;
      if (inst_buffer_end_ptr_d == DEPTH_NUM_BIT'(DEPTH)) begin
        inst_buffer_end_ptr_d = 'd0;
      end
    end
  end

  // outputs to the ID/EX stage
  assign valid_o = inst_buffer_full || (inst_buffer_not_empty && discard_prefetch_buffer_q);  // instruction buffer may not be full if we are currently awaiting branch outcome
  assign is_compress_o = inst_buffer_is_compress_q[inst_buffer_start_ptr_q];
  assign rdata_o = inst_buffer_data_q[inst_buffer_start_ptr_q];
  assign rdata_rd_o = inst_buffer_rd_physical_q[inst_buffer_start_ptr_q];
  assign rdata_rs1_o = inst_buffer_rs1_physical_q[inst_buffer_start_ptr_q];
  assign rdata_rs2_o = inst_buffer_rs2_physical_q[inst_buffer_start_ptr_q];
  assign addr_o = inst_buffer_addr_q[inst_buffer_start_ptr_q];
  assign err_o = 1'b0;
  assign err_plus2_o = 1'b0;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      for (int i=0; i<DEPTH; i++) begin
        inst_buffer_valid_q[i] <= 1'b0;
      end
      inst_buffer_start_ptr_q <= 'd0;
      inst_buffer_end_ptr_q <= 'd0;
    end else begin
      for (int i=0; i<DEPTH; i++) begin
        inst_buffer_addr_q[i] <= inst_buffer_addr_d[i];
        inst_buffer_data_q[i] <= inst_buffer_data_d[i];
        inst_buffer_is_compress_q[i] <= inst_buffer_is_compress_d[i];
        inst_buffer_valid_q[i] <= inst_buffer_valid_d[i];
      end
      inst_buffer_start_ptr_q <= inst_buffer_start_ptr_d;
      inst_buffer_end_ptr_q <= inst_buffer_end_ptr_d;
    end
  end

  /* Dependency tracking logic */

  logic [NUM_LOGICAL_REGS_NUM_BIT-1:0] current_uncompressed_opcode_rd, current_uncompressed_opcode_rs1, current_uncompressed_opcode_rs2;
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

  logic [DEPTH-1:0] [NUM_PHYSICAL_REGS_NUM_BIT-1:0] inst_buffer_rd_physical_d, inst_buffer_rd_physical_q;     // physical RD index (binary format)
  logic [DEPTH-1:0] [NUM_PHYSICAL_REGS_NUM_BIT-1:0] inst_buffer_rs1_physical_d, inst_buffer_rs1_physical_q;   // physical RS1 index (binary format)
  logic [DEPTH-1:0] [NUM_PHYSICAL_REGS_NUM_BIT-1:0] inst_buffer_rs2_physical_d, inst_buffer_rs2_physical_q;   // physical RS2 index (binary format)
  logic [DEPTH-1:0] [NUM_PHYSICAL_REGS-1:0]         inst_buffer_physical_reg_usage_d, inst_buffer_physical_reg_usage_q; // indicate which physical register is begin used by this instruction (bit vector format)
  logic [DEPTH-1:0] [DEPTH-1:0]                     inst_buffer_dependency_d, inst_buffer_dependency_q;       // indicate which instruction does this instruction depends on
  logic [DEPTH-1:0]                                 inst_buffer_is_load_store_d, inst_buffer_is_load_store_q; // indicate whether this instruction is a load/store

  logic [NUM_LOGICAL_REGS-1:0] [NUM_PHYSICAL_REGS_NUM_BIT-1:0] logical_to_physical_reg_d, logical_to_physical_reg_q; // store the mapping between logical to physical register (binary format)
  logic [NUM_PHYSICAL_REGS-1:0]                                physical_reg_reserved_d, physical_reg_reserved_q;     // keep track of physical registers currently reserved
                                                                                                                     // (this contain identical data to logical_to_physical_reg_* but in bit vector format)
                                                                                                                            

  // find the first avilable physical register by performing OR between physical_reg_reserved_q and each element of inst_buffer_physical_reg_usage_q and find the index of the rightmost 0
  // we perform OR because some physical registers might not be reserved currently but they stores data refer to by some instructions in the inst_buffer thus is not available
  logic [NUM_PHYSICAL_REGS-1:0]         physical_reg_in_used;
  logic [NUM_PHYSICAL_REGS_NUM_BIT-1:0] first_available_physical_reg_id;
  always_comb begin
    physical_reg_in_used = physical_reg_reserved_q;
    for (int i=0; i<DEPTH; i++) begin
      // we can avoid AND with the valid bit as `inst_buffer_physical_reg_usage_` is clear when the instruction is removed from the buffer
      physical_reg_in_used |= inst_buffer_physical_reg_usage_q[i] /*& {NUM_PHYSICAL_REGS{inst_buffer_valid_q[i]}}*/; 
    end

    first_available_physical_reg_id = 'd0;
    for (int i=NUM_PHYSICAL_REGS-1; i>=0; i--) begin
      if (!physical_reg_in_used[i]) begin
        first_available_physical_reg_id = NUM_PHYSICAL_REGS_NUM_BIT'(i);
      end
    end
  end

  always_comb begin
    for (int i=0; i<DEPTH; i++) begin
      inst_buffer_rd_physical_d[i] = inst_buffer_rd_physical_q[i];
      inst_buffer_rs1_physical_d[i] = inst_buffer_rs1_physical_q[i];
      inst_buffer_rs2_physical_d[i] = inst_buffer_rs2_physical_q[i];
      inst_buffer_physical_reg_usage_d[i] = inst_buffer_physical_reg_usage_q[i];
      inst_buffer_dependency_d[i] = inst_buffer_dependency_q[i];
      inst_buffer_is_load_store_d[i] = inst_buffer_is_load_store_q[i];
    end
    for (int i=0; i<NUM_LOGICAL_REGS; i++) begin
      logical_to_physical_reg_d[i] = logical_to_physical_reg_q[i];
    end
    physical_reg_reserved_d = physical_reg_reserved_q;

    if (inst_buffer_to_id_ex) begin
      // clear inst_buffer_physical_reg_usage_ so the system known which physical register is not being refer to by instruction in the instruction buffer 
      inst_buffer_physical_reg_usage_d[inst_buffer_start_ptr_q] = 'd0;
      // clear the dependency bit of other instructions that depends on this instruction
      for (int i=0; i<DEPTH; i++) begin
        inst_buffer_dependency_d[i][inst_buffer_start_ptr_q] = 1'b0;
      end
    end
    
    if (prefetch_buffer_to_inst_buffer) begin
      // reserve new physical register for RD if needed
      if (current_uncompressed_opcode_has_rd && (current_uncompressed_opcode_rd != 'd0)) begin
        inst_buffer_rd_physical_d[inst_buffer_end_ptr_q] = first_available_physical_reg_id;

        physical_reg_reserved_d[logical_to_physical_reg_d[current_uncompressed_opcode_rd]] = 1'b0;
        logical_to_physical_reg_d[current_uncompressed_opcode_rd] = first_available_physical_reg_id;
        physical_reg_reserved_d[first_available_physical_reg_id] = 1'b1;
      end else begin
        inst_buffer_rd_physical_d[inst_buffer_end_ptr_q] = 'd0;
      end
      // rename rs1, rs2
      inst_buffer_rs1_physical_d[inst_buffer_end_ptr_q] = current_uncompressed_opcode_has_rs1 ? logical_to_physical_reg_q[current_uncompressed_opcode_rs1] : 'd0;
      inst_buffer_rs2_physical_d[inst_buffer_end_ptr_q] = current_uncompressed_opcode_has_rs2 ? logical_to_physical_reg_q[current_uncompressed_opcode_rs2] : 'd0;
      // store physical register usage in bit vector format
      inst_buffer_physical_reg_usage_d[inst_buffer_end_ptr_q] = (1 << inst_buffer_rd_physical_d[inst_buffer_end_ptr_q]) | 
                                                                (1 << inst_buffer_rs1_physical_d[inst_buffer_end_ptr_q]) | 
                                                                (1 << inst_buffer_rs2_physical_d[inst_buffer_end_ptr_q]);
      
      // check which instructions that this instruction depends on
      inst_buffer_dependency_d[inst_buffer_end_ptr_q] = 'd0;
      for (int i=0; i<DEPTH; i++) begin
        // TODO: handle syscall (rd2) and ecall/ebreak
        if (inst_buffer_valid_q[i]) begin
          if ((inst_buffer_rd_physical_q[i] != 'd0) && (inst_buffer_rd_physical_q[i] == inst_buffer_rs1_physical_d[inst_buffer_end_ptr_q]
                                                      || inst_buffer_rd_physical_q[i] == inst_buffer_rs2_physical_d[inst_buffer_end_ptr_q])) begin
            inst_buffer_dependency_d[inst_buffer_end_ptr_q][i] = 1'b1;
          end
          if (inst_buffer_is_load_store_q[i] && prefetch_buffer_rdata_load_or_store) begin
            inst_buffer_dependency_d[inst_buffer_end_ptr_q][i] = 1'b1;
          end
        end
      end 
      // do not depend on ourself (checking the valid bit in the for-loop is not enough as old instruction can be removed and new instruction can be added in the same cycle)
      inst_buffer_dependency_d[inst_buffer_end_ptr_q][inst_buffer_end_ptr_q] = 1'b0;

      inst_buffer_is_load_store_d[inst_buffer_end_ptr_q] = prefetch_buffer_rdata_load_or_store;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      for (int i=0; i<DEPTH; i++) begin
        inst_buffer_physical_reg_usage_q[i] <= 'd0;
      end
      for (int i=0; i<NUM_LOGICAL_REGS; i++) begin
        logical_to_physical_reg_q[i] <= NUM_PHYSICAL_REGS_NUM_BIT'(i);
        physical_reg_reserved_q[i] <= 1'b1;
      end
      for (int i=NUM_LOGICAL_REGS; i<NUM_PHYSICAL_REGS; i++) begin
        physical_reg_reserved_q[i] <= 1'b0;
      end
    end else begin
      for (int i=0; i<DEPTH; i++) begin
        inst_buffer_rd_physical_q[i] <= inst_buffer_rd_physical_d[i];
        inst_buffer_rs1_physical_q[i] <= inst_buffer_rs1_physical_d[i];
        inst_buffer_rs2_physical_q[i] <= inst_buffer_rs2_physical_d[i];
        inst_buffer_physical_reg_usage_q[i] <= inst_buffer_physical_reg_usage_d[i];
        inst_buffer_dependency_q[i] <= inst_buffer_dependency_d[i];
        inst_buffer_is_load_store_q[i] <= inst_buffer_is_load_store_d[i];
      end
      for (int i=0; i<NUM_LOGICAL_REGS; i++) begin
        logical_to_physical_reg_q[i] <= logical_to_physical_reg_d[i];
      end
      for (int i=0; i<NUM_PHYSICAL_REGS; i++) begin
        physical_reg_reserved_q[i] <= physical_reg_reserved_d[i];
      end
    end
  end  

endmodule
