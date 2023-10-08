
module shufflev_prefetch_buffer import ibex_pkg::*; #(
  parameter bit             ResetAll          = 1'b0,
  parameter int unsigned    ShuffleBuffSize   = 4,
  parameter int unsigned    NumPhysicalRegs   = 64,
  parameter shufflev_rng_e  RngType           = RandomTkacik,
  parameter int unsigned    RngSeed           = 123456,
  parameter bit             EnableFetchId     = 1'b1,
  parameter bit             EnableFastBranch  = 1'b1,
  parameter bit             EnablePrefetch    = 1'b0,
  parameter bit             EnableBranchPredictor = 1'b0,
  parameter shufflev_branch_predictor_e BranchPredictorAlgorithm = BranchOffset,
  parameter bit             EnableOptimizeJal = 1'b0,
  parameter bit             EnableOptimizeMem = 1'b1,
  parameter int unsigned    NumBranchPredictorEntry = 16,
  parameter bit             DisplayBranchPredictionStat = 1'b0,
  parameter bit             DisplayRNGStat = 1'b0
) (
  input  logic        clk_i,
  input  logic        rst_ni,   // asynchronous reset

  input  logic        req_i,    // logic high while the core is awake otherwise false
                                // we ignore req_i and fill the fetch buffer anyway until it is full

  input  logic        branch_i, // assert when the core want to change PC (branch, jump, exception, etc.)
  input  logic [31:0] addr_i,

  input  logic        ready_i /*verilator public_flat_rw*/, 
  output logic        valid_o /*verilator public_flat_rw*/, 
  output logic        is_compress_o,
  output logic [31:0] rdata_o /*verilator public_flat_rw*/,
  output logic [NumPhysicalRegsNumBits-1:0] rdata_rd_o,
  output logic [NumPhysicalRegsNumBits-1:0] rdata_rs1_o,
  output logic [NumPhysicalRegsNumBits-1:0] rdata_rs2_o,
  output logic [31:0] addr_o /*verilator public_flat_rw*/,
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
  output logic        busy_o,    // avoid clock gate

  // goes to register file
  output logic [5:0] raddr_c_o,
  input logic [31:0] rdata_c_i,

  input logic [5:0]  waddr_a_i,
  input logic [31:0] wdata_a_i,
  input logic        we_a_i
);

  localparam int unsigned ShuffleBuffSizeNumBits = $clog2(ShuffleBuffSize);
  localparam int unsigned NumPhysicalRegsNumBits = $clog2(NumPhysicalRegs);
  localparam int unsigned NumLogicalRegs = 32;
  localparam int unsigned NumLogicalRegsNumBits = 5; // RV32I contains 32 logical register
  localparam int unsigned NumBranchPredictorEntryNumBits = $clog2(NumBranchPredictorEntry);

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

      .branch_i          (prefetch_predictor_branch_request),
      .addr_i            (prefetch_predictor_branch_addr),

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

  logic prefetch_buffer_rdata_branch;
  assign prefetch_buffer_rdata_branch = prefetch_buffer_rdata_uncompress[6:0] == 7'b1100011;

  logic prefetch_buffer_rdata_jal, prefetch_buffer_rdata_jalr;
  assign prefetch_buffer_rdata_jal = prefetch_buffer_rdata_uncompress[6:0] == 7'b1101111;
  assign prefetch_buffer_rdata_jalr = prefetch_buffer_rdata_uncompress[6:0] == 7'b1100111;

  logic prefetch_buffer_rdata_fence;
  assign prefetch_buffer_rdata_fence = prefetch_buffer_rdata_uncompress[6:0] == 7'b0001111;

  logic prefetch_buffer_rdata_env_trap;
  assign prefetch_buffer_rdata_env_trap = (prefetch_buffer_rdata_uncompress[6:0] == 7'b1110011         
                                          && prefetch_buffer_rdata_uncompress[14:12] == 3'd0
                                          && (prefetch_buffer_rdata_uncompress[22:21] == 2'b00        // ecall / ebreak
                                              || prefetch_buffer_rdata_uncompress[22:21] == 2'b01     // sret / mret  
                                              || prefetch_buffer_rdata_uncompress[22:21] == 2'b10));  // wfi
                                                                                                      // TODO: check sfence.vma 

  logic prefetch_buffer_rdata_may_change_pc;
  assign prefetch_buffer_rdata_may_change_pc = prefetch_buffer_rdata_branch || prefetch_buffer_rdata_jal || prefetch_buffer_rdata_jalr || prefetch_buffer_rdata_fence || prefetch_buffer_rdata_env_trap;

  logic prefetch_buffer_rdata_load;
  assign prefetch_buffer_rdata_load = (prefetch_buffer_rdata_uncompress[6:0] == 7'b0000011); // load 

  logic prefetch_buffer_rdata_store;
  assign prefetch_buffer_rdata_store = (prefetch_buffer_rdata_uncompress[6:0] == 7'b0100011); // store

  logic [2:0] prefetch_buffer_rdata_mem_access_num_byte;  // 1 (lb, lbu, sb), 2 (lh, lhu, sh) or 4 (lw, sw) 
  logic [31:0] prefetch_buffer_rdata_mem_access_offset;   // sign-extended version of the 12-bit offset of the load and store instruction
  logic prefetch_buffer_rdata_mem_access_address_valid;   // indicate whether the target memory address is valid or not (the address may be invalid if the source register hasn't been written by prior instruction)
  logic [31:0] prefetch_buffer_rdata_mem_access_address;  // target memory address of the load and store instruction 
  if (EnableOptimizeMem) begin
    // we can also assign 'raddr_c_o' to 'logical_to_physical_reg_q[current_uncompressed_opcode_rs1]' permanantly but doing it this way might save some power
    assign raddr_c_o = (prefetch_buffer_to_inst_buffer && (prefetch_buffer_rdata_load || prefetch_buffer_rdata_store)) ? logical_to_physical_reg_q[current_uncompressed_opcode_rs1] : 'd0;

    always_comb begin
      if (prefetch_buffer_rdata_uncompress[13:12] == 2'b00) begin
        prefetch_buffer_rdata_mem_access_num_byte = 3'd1;
      end else if (prefetch_buffer_rdata_uncompress[13:12] == 2'b01) begin
        prefetch_buffer_rdata_mem_access_num_byte = 3'd2;
      end else begin  // 2'b10
        prefetch_buffer_rdata_mem_access_num_byte = 3'd4;
      end

      if (prefetch_buffer_rdata_load) begin
        prefetch_buffer_rdata_mem_access_offset = {{20{prefetch_buffer_rdata_uncompress[31]}}, prefetch_buffer_rdata_uncompress[31:20]};
      end else begin
        prefetch_buffer_rdata_mem_access_offset = {{20{prefetch_buffer_rdata_uncompress[31]}}, prefetch_buffer_rdata_uncompress[31:25], prefetch_buffer_rdata_uncompress[11:7]};
      end

      prefetch_buffer_rdata_mem_access_address_valid = 1'b1;
      for (int i=0; i<ShuffleBuffSize; i++) begin
        // If there is another instruction that will write to our RS1, the target memory address calculated now is not valid.
        if (inst_buffer_valid_q[i] && (inst_buffer_rd_physical_q[i] != 0) && (inst_buffer_rd_physical_q[i] == logical_to_physical_reg_q[current_uncompressed_opcode_rs1])) begin
          prefetch_buffer_rdata_mem_access_address_valid = 1'b0;
        end
      end
      prefetch_buffer_rdata_mem_access_address = rdata_c_i + prefetch_buffer_rdata_mem_access_offset;
    end
  end else begin
    assign prefetch_buffer_rdata_mem_access_num_byte = 3'd0;
    assign prefetch_buffer_rdata_mem_access_offset = 32'd0;
    assign prefetch_buffer_rdata_mem_access_address_valid = 1'b0;
    assign prefetch_buffer_rdata_mem_access_address = 32'd0;

    logic [2:0] unused_prefetch_buffer_rdata_mem_access_num_byte;
    assign unused_prefetch_buffer_rdata_mem_access_num_byte = prefetch_buffer_rdata_mem_access_num_byte;

    logic [31:0] unused_prefetch_buffer_rdata_mem_access_offset;
    assign unused_prefetch_buffer_rdata_mem_access_offset = prefetch_buffer_rdata_mem_access_offset;

    logic unused_prefetch_buffer_rdata_mem_access_address_valid;
    assign unused_prefetch_buffer_rdata_mem_access_address_valid = prefetch_buffer_rdata_mem_access_address_valid;

    logic [31:0] unused_prefetch_buffer_rdata_mem_access_address;
    assign unused_prefetch_buffer_rdata_mem_access_address = prefetch_buffer_rdata_mem_access_address;
  end

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
    if (prefetch_buffer_rdata_may_change_pc && ibex_prefetch_buffer_ready_i) begin
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

  /* Branch predictor */
  
  logic [31:0] prefetch_buffer_rdata_branch_offset;
  assign prefetch_buffer_rdata_branch_offset =  { {19{prefetch_buffer_rdata_uncompress[31]}}, prefetch_buffer_rdata_uncompress[31], prefetch_buffer_rdata_uncompress[7], prefetch_buffer_rdata_uncompress[30:25], prefetch_buffer_rdata_uncompress[11:8], 1'b0 };

  logic branch_predictor_predict_taken;

  if (EnableBranchPredictor && BranchPredictorAlgorithm == AlwaysTaken) begin
    assign branch_predictor_predict_taken = 1'b1;
  end else if (EnableBranchPredictor && BranchPredictorAlgorithm == AlwaysNotTaken) begin
    assign branch_predictor_predict_taken = 1'b0;
  end else if (EnableBranchPredictor && BranchPredictorAlgorithm == BranchOffset) begin
    assign branch_predictor_predict_taken = prefetch_buffer_rdata_branch_offset[31];  // always predict branch with negative offset as taken and positive offset as not taken
  end else if (EnableBranchPredictor && BranchPredictorAlgorithm == TwoBits) begin
    logic [NumBranchPredictorEntry-1:0] [31:0] branch_predictor_entry_pc_d, branch_predictor_entry_pc_q;            // the pc value of the branch instruction in each entry
    logic [NumBranchPredictorEntry-1:0] [1:0]  branch_predictor_entry_state_d, branch_predictor_entry_state_q;      // state of the two-bits branch predictor (0 - Not taken, 1 - Weakly not taken, 2 - Weakly taken, 3 - Taken)
    logic [NumBranchPredictorEntry-1:0]        branch_predictor_entry_valid_d, branch_predictor_entry_valid_q;      // indicate whether the entry is valid
    logic [NumBranchPredictorEntryNumBits-1:0] branch_predictor_current_entry_d, branch_predictor_current_entry_q;  // index of the entry to be replace (FIFO replacement policy)

    logic [NumBranchPredictorEntryNumBits-1:0] branch_predictor_update_index;
    logic                                      branch_predictor_has_entry;
    always_comb begin
      branch_predictor_entry_pc_d = branch_predictor_entry_pc_q;
      branch_predictor_entry_state_d = branch_predictor_entry_state_q;
      branch_predictor_entry_valid_d = branch_predictor_entry_valid_q;
      branch_predictor_current_entry_d = branch_predictor_current_entry_q;
      branch_predictor_update_index = branch_predictor_current_entry_q;
      branch_predictor_has_entry = 1'b0;

      // branch_i can be asserted after executing branch, jump and any instruction that affect the PC so we need to check `prefetch_predictor_predict_branch_q` before updating entry in the branch predictor
      if (prefetch_predictor_predict_branch_q && (branch_i || latest_branch_not_taken)) begin
        // check whether entry for the current branch exist if not we will create new entry at `branch_predictor_current_entry_q` if needed
        for (int i=0; i<NumBranchPredictorEntry; i++) begin
          if (branch_predictor_entry_valid_q[i] && (branch_predictor_entry_pc_q[i] == prefetch_predictor_predict_pc_q)) begin
            branch_predictor_update_index = NumBranchPredictorEntryNumBits'(i);
            branch_predictor_has_entry = 1'b1;
          end
        end

        if (!branch_predictor_has_entry) begin
          if (branch_i) begin
            branch_predictor_entry_pc_d[branch_predictor_update_index] = prefetch_predictor_predict_pc_q;
            branch_predictor_entry_state_d[branch_predictor_update_index] = 2'b11;
            branch_predictor_entry_valid_d[branch_predictor_update_index] = 1'b1;
            branch_predictor_current_entry_d = branch_predictor_current_entry_q + 'd1;
            /* verilator lint_off CMPCONST */
            if (branch_predictor_current_entry_d > NumBranchPredictorEntryNumBits'(NumBranchPredictorEntry-1)) begin   // should be optimized out by the synthesis tool if NumBranchPredictorEntry is a power of two
              branch_predictor_current_entry_d = 'd0;
            end
            /* verilator lint_on CMPCONST */
          end
        end else begin
          if (branch_i) begin
            if (branch_predictor_entry_state_q[branch_predictor_update_index] == 2'b00) begin
              branch_predictor_entry_state_d[branch_predictor_update_index] = 2'b01;
            end else if (branch_predictor_entry_state_q[branch_predictor_update_index] == 2'b01) begin
              branch_predictor_entry_state_d[branch_predictor_update_index] = 2'b10;
            end if (branch_predictor_entry_state_q[branch_predictor_update_index] == 2'b10) begin
              branch_predictor_entry_state_d[branch_predictor_update_index] = 2'b11;
            end
          end else if (latest_branch_not_taken) begin
            if (branch_predictor_entry_state_q[branch_predictor_update_index] == 2'b01) begin
              branch_predictor_entry_state_d[branch_predictor_update_index] = 2'b00;
            end else if (branch_predictor_entry_state_q[branch_predictor_update_index] == 2'b10) begin
              branch_predictor_entry_state_d[branch_predictor_update_index] = 2'b01;
            end if (branch_predictor_entry_state_q[branch_predictor_update_index] == 2'b11) begin
              branch_predictor_entry_state_d[branch_predictor_update_index] = 2'b10;
            end
          end
        end
      end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        branch_predictor_entry_valid_q <= 'd0;
        branch_predictor_current_entry_q <= 'd0;
      end else begin
        branch_predictor_entry_pc_q <= branch_predictor_entry_pc_d;
        branch_predictor_entry_state_q <= branch_predictor_entry_state_d;
        branch_predictor_entry_valid_q <= branch_predictor_entry_valid_d;
        branch_predictor_current_entry_q <= branch_predictor_current_entry_d;
      end
    end

    logic [1:0] current_inst_predictor_state;

    always_comb begin
      current_inst_predictor_state = 'd0;
      for (int i=0; i<NumBranchPredictorEntry; i++) begin
        if (branch_predictor_entry_valid_q[i] && (branch_predictor_entry_pc_q[i] == ibex_prefetch_buffer_addr_o)) begin
          current_inst_predictor_state = branch_predictor_entry_state_q[i];
        end
      end
    end

    assign branch_predictor_predict_taken = current_inst_predictor_state == 2'b10 || current_inst_predictor_state == 2'b11;
  end else begin
    assign branch_predictor_predict_taken = 1'b0;

    logic unused_branch_predictor_predict_taken;
    assign unused_branch_predictor_predict_taken = branch_predictor_predict_taken;

    logic [31:0] unused_prefetch_buffer_rdata_branch_offset;
    assign unused_prefetch_buffer_rdata_branch_offset = prefetch_buffer_rdata_branch_offset;
  end

  /* Prefetch predictor */

  logic         prefetch_predictor_branch_request;  // request the prefetch buffer to fetch from new address in `prefetch_predictor_branch_addr`
  logic [31:0]  prefetch_predictor_branch_addr;     // a new address to fetch from when `prefetch_predictor_branch_request` is asserted

  logic         prefetch_predictor_predict_taken_d, prefetch_predictor_predict_taken_q;   // save the most recent prediction so that we can generate `prefetch_predictor_hit`/`prefetch_predictor_miss` 
                                                                                          // which is required for flushing the instruction buffer when we prefetch the wrong instruction
                                                                                          // (a better logic might be needed if we were to predict next branch before the previous one is resolved)
  logic [31:0]  prefetch_predictor_revert_pc_d, prefetch_predictor_revert_pc_q;           // save the next pc value to revert to if we mispredict the branch (current pc + 2 or +4)
  logic [31:0]  prefetch_predictor_predict_pc_d, prefetch_predictor_predict_pc_q;         // save the pc value that initiate the prefetch (need by the branch predictor to update its state)
  logic         prefetch_predictor_predict_branch_d, prefetch_predictor_predict_branch_q; // indicate whether the prefetch was caused by a branch instruction (need to trigger the branch predictor to update its state)

  logic         prefetch_predictor_hit;   // indicate whether the last prediction is a hit or miss
  logic         prefetch_predictor_miss;

  if (EnablePrefetch) begin
    always_comb begin
      prefetch_predictor_branch_request = 1'b0;
      prefetch_predictor_branch_addr = 'd0;
      prefetch_predictor_predict_taken_d =  prefetch_predictor_predict_taken_q;
      prefetch_predictor_revert_pc_d = prefetch_predictor_revert_pc_q;
      prefetch_predictor_predict_pc_d = prefetch_predictor_predict_pc_q;
      prefetch_predictor_predict_branch_d = prefetch_predictor_predict_branch_q;
      prefetch_predictor_hit = 1'b0;
      prefetch_predictor_miss = 1'b0;

      // the ID/EX stage request the PC value to change (branch taken, jump, interrupt, etc)
      if (branch_i) begin
        // if `branch_i` asserts as a result of a program instruction, check whether we predict the branch correctly and revert to fetch the correct instruction if need
        // otherwise we just signal the prefetch buffer to jump to the new PC (power-on reset, interupt after wfi instruction etc.)
        if (discard_prefetch_buffer_q) begin
          if (prefetch_predictor_predict_taken_q) begin
            prefetch_predictor_hit = 1'b1;
            prefetch_predictor_miss = 1'b0;
          end else begin
            prefetch_predictor_hit = 1'b0;
            prefetch_predictor_miss = 1'b1;
            prefetch_predictor_branch_request = 1'b1;
            prefetch_predictor_branch_addr = addr_i;
          end
        end else begin 
          prefetch_predictor_branch_request = 1'b1;
          prefetch_predictor_branch_addr = addr_i;
        end
      end

      // the previous branch instruction was not taken. in this case, check whether we predict the branch correctly and revert to fetch the correct instruction if need
      if (latest_branch_not_taken) begin
        if (prefetch_predictor_predict_taken_q) begin
          prefetch_predictor_hit = 1'b0;
          prefetch_predictor_miss = 1'b1;
          prefetch_predictor_branch_request = 1'b1;
          prefetch_predictor_branch_addr = prefetch_predictor_revert_pc_q;
        end else begin
          prefetch_predictor_hit = 1'b1;
          prefetch_predictor_miss = 1'b0;
        end
      end

      // if the current instruction being from the prefetch buffer into our shuffling buffer may change the PC value, we predict the next PC value depend on the type of the instruction
      if (prefetch_buffer_rdata_may_change_pc && ibex_prefetch_buffer_ready_i) begin
        if (EnableBranchPredictor && prefetch_buffer_rdata_branch) begin
          if (branch_predictor_predict_taken) begin
            prefetch_predictor_branch_request = prefetch_buffer_rdata_may_change_pc;
            prefetch_predictor_branch_addr = ibex_prefetch_buffer_addr_o + prefetch_buffer_rdata_branch_offset;
            prefetch_predictor_predict_taken_d = 1'b1;
            prefetch_predictor_revert_pc_d = ibex_prefetch_buffer_addr_o + (prefetch_buffer_rdata_is_compress ? 'd2 : 'd4);
          end else begin
            prefetch_predictor_predict_taken_d = 1'b0;
          end
          prefetch_predictor_predict_pc_d = ibex_prefetch_buffer_addr_o;
          prefetch_predictor_predict_branch_d = 1'b1;
        end else if (EnableOptimizeJal && prefetch_buffer_rdata_jal) begin
          prefetch_predictor_branch_request = prefetch_buffer_rdata_may_change_pc;
          prefetch_predictor_branch_addr = ibex_prefetch_buffer_addr_o + { {11{prefetch_buffer_rdata_uncompress[31]}}, prefetch_buffer_rdata_uncompress[31], prefetch_buffer_rdata_uncompress[19:12], prefetch_buffer_rdata_uncompress[20], prefetch_buffer_rdata_uncompress[30:21], 1'b0 };
          prefetch_predictor_predict_taken_d = 1'b1;
          prefetch_predictor_predict_branch_d = 1'b0;
        end else begin
          // Prediction logic for this instruction is not yet implemented so we can't perform prefetch
          prefetch_predictor_predict_taken_d = 1'b0;
          prefetch_predictor_predict_branch_d = 1'b0;
        end
      end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        prefetch_predictor_predict_taken_q <= 1'b0;
      end else begin
        prefetch_predictor_predict_taken_q <= prefetch_predictor_predict_taken_d;
        prefetch_predictor_revert_pc_q <= prefetch_predictor_revert_pc_d;
        prefetch_predictor_predict_pc_q <= prefetch_predictor_predict_pc_d;
        prefetch_predictor_predict_branch_q <= prefetch_predictor_predict_branch_d;
      end
    end
  end else begin
    assign prefetch_predictor_branch_request = branch_i;
    assign prefetch_predictor_branch_addr = addr_i;
    assign prefetch_predictor_predict_taken_d = 'd0;
    assign prefetch_predictor_predict_taken_q = 'd0;
    assign prefetch_predictor_revert_pc_d = 'd0;
    assign prefetch_predictor_revert_pc_q = 'd0;
    assign prefetch_predictor_predict_pc_d = 'd0;
    assign prefetch_predictor_predict_pc_q = 'd0;
    assign prefetch_predictor_predict_branch_d = 'd0;
    assign prefetch_predictor_predict_branch_q = 'd0;
    assign prefetch_predictor_hit = 1'b0;
    assign prefetch_predictor_miss = 1'b0;

    logic         unused_prefetch_predictor_predict_taken_d, unused_prefetch_predictor_predict_taken_q;
    logic [31:0]  unused_prefetch_predictor_revert_pc_d, unused_prefetch_predictor_revert_pc_q;
    logic [31:0]  unused_prefetch_predictor_predict_pc_d, unused_prefetch_predictor_predict_pc_q;
    logic         unused_prefetch_predictor_predict_branch_d, unused_prefetch_predictor_predict_branch_q;
    assign unused_prefetch_predictor_predict_taken_d = prefetch_predictor_predict_taken_d;
    assign unused_prefetch_predictor_predict_taken_q = prefetch_predictor_predict_taken_q;
    assign unused_prefetch_predictor_revert_pc_d = prefetch_predictor_revert_pc_d;
    assign unused_prefetch_predictor_revert_pc_q = prefetch_predictor_revert_pc_q;
    assign unused_prefetch_predictor_predict_pc_d = prefetch_predictor_predict_pc_d;
    assign unused_prefetch_predictor_predict_pc_q = prefetch_predictor_predict_pc_q;
    assign unused_prefetch_predictor_predict_branch_d = prefetch_predictor_predict_branch_d;
    assign unused_prefetch_predictor_predict_branch_q = prefetch_predictor_predict_branch_q;
  end

  /* Transfer from prefetch buffer to shuffling buffer (inst_buffer_...) and from shuffling buffer to the ID/EX stage */

  logic [ShuffleBuffSize-1:0] [31:0]    inst_buffer_addr_d, inst_buffer_addr_q;               // PC value
  logic [ShuffleBuffSize-1:0] [31:0]    inst_buffer_data_d, inst_buffer_data_q;               // uncompress instruction to be sent to the ID/EX stage
  logic [ShuffleBuffSize-1:0]           inst_buffer_is_compress_d, inst_buffer_is_compress_q; // indicate whether the instruction is originally a compress instruction or not
  logic [ShuffleBuffSize-1:0]           inst_buffer_valid_d, inst_buffer_valid_q;             // indicate whether the entry in the buffer is valid or not
  logic [ShuffleBuffSize-1:0]           inst_buffer_is_prefetch_d, inst_buffer_is_prefetch_q; // indicate whether the entry in the buffer is a prefetch instruction which should not be sent to the ID/EX stage 

  logic                       inst_buffer_full;             // indicate that all entry in the inst buffer is valid but some/all entries may not be ready as they are prefetch instructions
  logic [ShuffleBuffSize-1:0] inst_buffer_is_ready;         // indicate which entry is valid and is not a prefetch instruction (ready)
  logic                       inst_buffer_all_inst_ready;   // indicate that all entry in the inst buffer is ready
  logic                       inst_buffer_any_inst_ready;   // indicate that there is at least one ready entry in the inst buffer
  assign inst_buffer_full             =   &inst_buffer_valid_q;
  assign inst_buffer_is_ready         =   inst_buffer_valid_q & ~inst_buffer_is_prefetch_q;
  assign inst_buffer_all_inst_ready   =   &inst_buffer_is_ready;   
  assign inst_buffer_any_inst_ready   =   |inst_buffer_is_ready;

  // retrieve new instruction from the prefetch buffer when the prefetch buffer has valid data, the instruction buffer is not full and `discard_prefetch_buffer_q` is not asserted
  // Note:
  // - we still accept new instruction when the instruction buffer is full if one entry is being removed (ready_i and valid_o are both asserted)
  // - we don't accept new branch/jump instruction when the previous one hasn't been resolved
  logic prefetch_buffer_to_inst_buffer;
  if (EnablePrefetch) begin
    assign prefetch_buffer_to_inst_buffer = !prefetch_predictor_miss && ibex_prefetch_buffer_valid_o && (!inst_buffer_full || (ready_i && valid_o)) && !(discard_prefetch_buffer_q && prefetch_buffer_rdata_may_change_pc && !prefetch_predictor_hit);
  end else begin
    assign prefetch_buffer_to_inst_buffer = !branch_i && ibex_prefetch_buffer_valid_o && (!inst_buffer_full || (ready_i && valid_o)) && (!discard_prefetch_buffer_q || latest_branch_not_taken);
  end

  logic inst_buffer_to_id_ex;
  assign inst_buffer_to_id_ex = ready_i && valid_o;

  always_comb begin
    for (int i=0; i<ShuffleBuffSize; i++) begin
      inst_buffer_addr_d[i] = inst_buffer_addr_q[i];
      inst_buffer_data_d[i] = inst_buffer_data_q[i];
      inst_buffer_is_compress_d[i] = inst_buffer_is_compress_q[i];
      inst_buffer_valid_d[i] = inst_buffer_valid_q[i];
      inst_buffer_is_prefetch_d[i] = inst_buffer_is_prefetch_q[i];
    end

    ibex_prefetch_buffer_ready_i = 1'b0;

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
      inst_buffer_is_prefetch_d[inst_buffer_insert_index] = EnablePrefetch ? discard_prefetch_buffer_q : 1'b0;
    end

    // when we correctly predict the branch, deassert `inst_buffer_is_prefetch_` to make all prefetch instruction become ready
    if (prefetch_predictor_hit) begin
      for (int i=0; i<ShuffleBuffSize; i++) begin
        inst_buffer_is_prefetch_d[i] = 1'b0;
      end
    end

    // when we mispredict the branch, make all prefetch instructions invalid
    if (prefetch_predictor_miss) begin
      for (int i=0; i<ShuffleBuffSize; i++) begin
        if (inst_buffer_is_prefetch_q[i]) begin
          inst_buffer_valid_d[i] = 1'b0;
        end
        inst_buffer_is_prefetch_d[i] = 1'b0;
      end
    end
  end

  // outputs to the ID/EX stage
  assign valid_o = (inst_buffer_all_inst_ready || (inst_buffer_any_inst_ready && discard_prefetch_buffer_q)) && !branch_i && random_number_valid;  // instruction buffer may not be full if we are currently awaiting branch outcome
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
        inst_buffer_is_prefetch_q[i] <= inst_buffer_is_prefetch_d[i];
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
  logic [ShuffleBuffSize-1:0]                                 inst_buffer_is_load_d, inst_buffer_is_load_q; // indicate whether this instruction is a load
  logic [ShuffleBuffSize-1:0]                                 inst_buffer_is_store_d, inst_buffer_is_store_q; // indicate whether this instruction is a store
  logic [ShuffleBuffSize-1:0]                                 inst_buffer_mem_access_addr_valid_d, inst_buffer_mem_access_addr_valid_q; // indicate whether the target memory address is valid or not
  logic [ShuffleBuffSize-1:0] [31:0]                          inst_buffer_mem_access_addr_d, inst_buffer_mem_access_addr_q; // store the target memory address
  logic [ShuffleBuffSize-1:0] [2:0]                           inst_buffer_mem_access_num_byte_d, inst_buffer_mem_access_num_byte_q;   // 1 (lb, lbu, sb), 2 (lh, lhu, sh) or 4 (lw, sw) (valid only when inst_buffer_is_load_q/inst_buffer_is_store_q is asserted)
  logic [ShuffleBuffSize-1:0] [11:0]                          inst_buffer_mem_access_offset;  // temporary signal directly wired to bits in inst_buffer_data_q
  logic [ShuffleBuffSize-1:0]                                 inst_buffer_is_env_csr_d, inst_buffer_is_env_csr_q;       // indicate whether this instruction is an environment/csr instruction (ecall/ebreak/csr.../wfi)

  logic [NumLogicalRegs-1:0] [NumPhysicalRegsNumBits-1:0] logical_to_physical_reg_d, logical_to_physical_reg_q; // store the mapping between logical to physical register (binary format)
  logic [NumPhysicalRegs-1:0]                                physical_reg_reserved_d, physical_reg_reserved_q;     // keep track of physical registers currently reserved
                                                                                                                     // (this contain identical data to logical_to_physical_reg_* but in bit vector format)

  logic [NumLogicalRegs-1:0] [NumPhysicalRegsNumBits-1:0]   logical_to_physical_reg_checkpoint_d, logical_to_physical_reg_checkpoint_q; // save current physical register assignment before performing prefetch                                   
  logic [NumPhysicalRegs-1:0]                               physical_reg_reserved_checkpoint_d, physical_reg_reserved_checkpoint_q;

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
      inst_buffer_is_load_d[i] = inst_buffer_is_load_q[i];
      inst_buffer_is_store_d[i] = inst_buffer_is_store_q[i];
      if (EnableOptimizeMem) begin
        inst_buffer_mem_access_addr_valid_d[i] = inst_buffer_mem_access_addr_valid_q[i];
        inst_buffer_mem_access_addr_d[i] = inst_buffer_mem_access_addr_q[i];
        inst_buffer_mem_access_num_byte_d[i] = inst_buffer_mem_access_num_byte_q[i];
        if (inst_buffer_is_load_q[i]) begin
          inst_buffer_mem_access_offset[i] = inst_buffer_data_q[i][31:20];
        end else begin
          inst_buffer_mem_access_offset[i] = {inst_buffer_data_q[i][31:25], inst_buffer_data_q[i][11:7]};
        end  
      end else begin
        inst_buffer_mem_access_addr_valid_d[i] = 'd0;
        inst_buffer_mem_access_addr_d[i] = 'd0;
        inst_buffer_mem_access_num_byte_d[i] = 'd0;
        inst_buffer_mem_access_offset[i] = 'd0;
      end
      inst_buffer_is_env_csr_d[i] = inst_buffer_is_env_csr_q[i];
    end
    for (int i=0; i<NumLogicalRegs; i++) begin
      logical_to_physical_reg_d[i] = logical_to_physical_reg_q[i];
    end
    physical_reg_reserved_d = physical_reg_reserved_q;
    logical_to_physical_reg_checkpoint_d = logical_to_physical_reg_checkpoint_q;
    physical_reg_reserved_checkpoint_d = physical_reg_reserved_checkpoint_q;

    // revert physical register assignment when the branch we mispredict
    if (prefetch_predictor_miss) begin
      logical_to_physical_reg_d = logical_to_physical_reg_checkpoint_q;
      physical_reg_reserved_d = physical_reg_reserved_checkpoint_q;
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
          if (EnableOptimizeMem) begin
            if ((inst_buffer_is_load_q[i] || inst_buffer_is_store_q[i]) && (prefetch_buffer_rdata_load || prefetch_buffer_rdata_store)) begin
              if (!inst_buffer_mem_access_addr_valid_q[i] || !prefetch_buffer_rdata_mem_access_address_valid) begin // One of the address may be invalid
                if (inst_buffer_rs1_physical_q[i] != logical_to_physical_reg_q[current_uncompressed_opcode_rs1]) begin  // Assume dependency exist if rs1 doesn't match
                  inst_buffer_dependency_d[inst_buffer_insert_index][i] = 1'b1;
                end else begin
                  // If rs1 matches and address overlap, dependency exists
                  if (((prefetch_buffer_rdata_mem_access_offset[11:0] >= inst_buffer_mem_access_offset[i]) 
                      && (prefetch_buffer_rdata_mem_access_offset[11:0] < inst_buffer_mem_access_offset[i] + {9'd0, inst_buffer_mem_access_num_byte_q[i]}))
                    || ((prefetch_buffer_rdata_mem_access_offset[11:0] + {9'd0, prefetch_buffer_rdata_mem_access_num_byte} > inst_buffer_mem_access_offset[i]) 
                      && (prefetch_buffer_rdata_mem_access_offset[11:0] + {9'd0, prefetch_buffer_rdata_mem_access_num_byte} <= inst_buffer_mem_access_offset[i] + {9'd0, inst_buffer_mem_access_num_byte_q[i]}))) begin
                    inst_buffer_dependency_d[inst_buffer_insert_index][i] = 1'b1;
                  end else begin // dependency doesn't exist when rs1 matches but address doesn't overlap
                    // do nothing
                  end
                end
              end else if (inst_buffer_mem_access_addr_valid_q[i] && (inst_buffer_mem_access_addr_q[i] < 'h100000 || inst_buffer_mem_access_addr_q[i] > 'h200000)
                && prefetch_buffer_rdata_mem_access_address_valid && (prefetch_buffer_rdata_mem_access_address < 'h100000 || prefetch_buffer_rdata_mem_access_address > 'h200000)) begin  // Memory-mapped IO should be done sequentially
                inst_buffer_dependency_d[inst_buffer_insert_index][i] = 1'b1;
              end else  if (inst_buffer_is_load_q[i] && prefetch_buffer_rdata_load) begin   // Several load operations can be shuffled freely even though their addresses overlap
                // do nothing
              end else if (prefetch_buffer_rdata_mem_access_address >= inst_buffer_mem_access_addr_q[i]  
                        && prefetch_buffer_rdata_mem_access_address < inst_buffer_mem_access_addr_q[i] + {29'd0, inst_buffer_mem_access_num_byte_q[i]}) begin  // Check the address for possible overlap. 
                inst_buffer_dependency_d[inst_buffer_insert_index][i] = 1'b1;
              end else if (prefetch_buffer_rdata_mem_access_address + {29'd0, prefetch_buffer_rdata_mem_access_num_byte} > inst_buffer_mem_access_addr_q[i]  
                        && prefetch_buffer_rdata_mem_access_address + {29'd0, prefetch_buffer_rdata_mem_access_num_byte} <= inst_buffer_mem_access_addr_q[i] + {29'd0, inst_buffer_mem_access_num_byte_q[i]}) begin
                inst_buffer_dependency_d[inst_buffer_insert_index][i] = 1'b1;
              end
            end
          end else begin
            // all load/store should be done in order
            if ((inst_buffer_is_load_q[i] || inst_buffer_is_store_q[i]) && (prefetch_buffer_rdata_load || prefetch_buffer_rdata_store)) begin
              inst_buffer_dependency_d[inst_buffer_insert_index][i] = 1'b1;
            end
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

      inst_buffer_may_change_pc_d[inst_buffer_insert_index] = prefetch_buffer_rdata_may_change_pc;
      inst_buffer_is_load_d[inst_buffer_insert_index] = prefetch_buffer_rdata_load;
      inst_buffer_is_store_d[inst_buffer_insert_index] = prefetch_buffer_rdata_store;
      if (EnableOptimizeMem) begin
        inst_buffer_mem_access_addr_valid_d[inst_buffer_insert_index] = prefetch_buffer_rdata_mem_access_address_valid;
        inst_buffer_mem_access_addr_d[inst_buffer_insert_index] = prefetch_buffer_rdata_mem_access_address;
        inst_buffer_mem_access_num_byte_d[inst_buffer_insert_index] = prefetch_buffer_rdata_mem_access_num_byte;
      end
      inst_buffer_is_env_csr_d[inst_buffer_insert_index] = prefetch_buffer_rdata_synch_env_csr;
    
      // save current physical register assignment when performing prefetch as these instructions may be discarded in the future
      // the last instruction before prefetch is always be a branch or jump and we won't fetch other branch or jump during prefetch period thus checking `prefetch_buffer_rdata_may_change_pc` is adequate
      if (prefetch_buffer_rdata_may_change_pc) begin
        logical_to_physical_reg_checkpoint_d = logical_to_physical_reg_d;
        physical_reg_reserved_checkpoint_d = physical_reg_reserved_d;
      end
    end
  
    // if (EnableOptimizeMem) begin
    //   // when the ID/EX stage write to a register, we check to update the target memory address of all dependent instructions in the shuffle buffer
    //   if (we_a_i) begin
    //     for (int i=0; i<ShuffleBuffSize; i++) begin
    //       if (inst_buffer_valid_q[i] && (inst_buffer_is_load_q[i] || inst_buffer_is_store_q[i]) && (inst_buffer_rs1_physical_q[i] == waddr_a_i)) begin
    //         inst_buffer_mem_access_addr_valid_d[i] = 1'b1;
    //         if (inst_buffer_is_load_q[i]) begin
    //           inst_buffer_mem_access_addr_d[i] = wdata_a_i + {{20{inst_buffer_data_q[i][31]}}, inst_buffer_data_q[i][31:20]};
    //         end else begin
    //           inst_buffer_mem_access_addr_d[i] = wdata_a_i + {{20{inst_buffer_data_q[i][31]}}, inst_buffer_data_q[i][31:25], inst_buffer_data_q[i][11:7]};
    //         end
    //       end
    //     end
    //   end

    //   // reevaluate dependencies among memory operation
    //   for (int i=0; i<ShuffleBuffSize; i++) begin
    //     for (int j=0; j<ShuffleBuffSize; j++) begin
    //       if ((inst_buffer_valid_q[i] && (inst_buffer_is_load_q[i] || inst_buffer_is_store_q[i])) 
    //         && (inst_buffer_valid_q[j] && (inst_buffer_is_load_q[j] || inst_buffer_is_store_q[j]))
    //         && inst_buffer_dependency_q[i][j]) begin
    //         // We deassert the dependency bit if the following conditions are true
    //         //  1) when inst[i] is a store and inst[j] is a load, inst_buffer[j].rd != inst_buffer[i].rs1 / rs2 (normal data dependency not exist)
    //         //  2) the target address should not be overlapped
    //         if (inst_buffer_is_store_q[i] && inst_buffer_is_load_q[j]) begin
    //           if ((inst_buffer_rd_physical_q[j] == inst_buffer_rs1_physical_q[i]) || (inst_buffer_rd_physical_q[j] == inst_buffer_rs2_physical_q[i])) begin
    //             continue;
    //           end
    //         end
    //         if (inst_buffer_mem_access_addr_d[i] >= inst_buffer_mem_access_addr_q[j] 
    //             && inst_buffer_mem_access_addr_d[i] < inst_buffer_mem_access_addr_q[j] + {29'd0, inst_buffer_mem_access_num_byte_q[j]}) begin
    //           continue;
    //         end 
    //         if (inst_buffer_mem_access_addr_q[j] >= inst_buffer_mem_access_addr_d[i]
    //             && inst_buffer_mem_access_addr_q[j] < inst_buffer_mem_access_addr_d[i] + {29'd0, inst_buffer_mem_access_num_byte_q[i]}) begin
    //           continue;
    //         end
    //         inst_buffer_dependency_d[i][j] = 1'b0;
    //       end
    //     end
    //   end
    // end
  end

  // logic [31:0] unused_rdata_c_i;
  // assign raddr_c_o = 6'd0;
  // assign unused_rdata_c_i = rdata_c_i;

  logic [31:0] unused_wdata_a_i;
  logic unused_we_a_i;
  logic [5:0] unused_waddr_a_i;
  assign unused_wdata_a_i = wdata_a_i;
  assign unused_we_a_i = we_a_i;
  assign unused_waddr_a_i = waddr_a_i;

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
        inst_buffer_is_load_q[i] <= inst_buffer_is_load_d[i];
        inst_buffer_is_store_q[i] <= inst_buffer_is_store_d[i];
        if (EnableOptimizeMem) begin
          inst_buffer_mem_access_addr_valid_q[i] <= inst_buffer_mem_access_addr_valid_d[i];
          inst_buffer_mem_access_addr_q[i] <= inst_buffer_mem_access_addr_d[i];
          inst_buffer_mem_access_num_byte_q[i] <= inst_buffer_mem_access_num_byte_d[i];
        end
        inst_buffer_is_env_csr_q[i] <= inst_buffer_is_env_csr_d[i];
      end
      for (int i=0; i<NumLogicalRegs; i++) begin
        logical_to_physical_reg_q[i] <= logical_to_physical_reg_d[i];
      end
      for (int i=0; i<NumPhysicalRegs; i++) begin
        physical_reg_reserved_q[i] <= physical_reg_reserved_d[i];
      end
      logical_to_physical_reg_checkpoint_q <= logical_to_physical_reg_checkpoint_d;
      physical_reg_reserved_checkpoint_q <= physical_reg_reserved_checkpoint_d;
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
      random_valid_entry[i] = inst_buffer_is_ready[distance_table[i][random_number]] && !(|inst_buffer_dependency_q[distance_table[i][random_number]]); 
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
  logic [31:0] fetch_id_idex /*verilator public_flat_rw*/; 
  /* verilator lint_off UNUSEDSIGNAL */

  if (EnableFetchId) begin
    logic [31:0]                fetch_id_d, fetch_id_q;
    logic [31:0]                fetch_id_checkpoint_d, fetch_id_checkpoint_q;
    logic [ShuffleBuffSize-1:0] [31:0]    inst_buffer_fetch_id_d, inst_buffer_fetch_id_q;       // unique sequential number for debugging purpose

    always_comb begin
      fetch_id_d = fetch_id_q;
      fetch_id_checkpoint_d = fetch_id_checkpoint_q;
      for (int i=0; i<ShuffleBuffSize; i++) begin
        inst_buffer_fetch_id_d[i] = inst_buffer_fetch_id_q[i];
      end

      if (prefetch_predictor_miss) begin
        fetch_id_d = fetch_id_checkpoint_q;
      end 

      if (prefetch_buffer_to_inst_buffer) begin
        inst_buffer_fetch_id_d[inst_buffer_insert_index] = fetch_id_q;
        fetch_id_d = fetch_id_q + 1;

        // save current fetch_id when performing prefetch as these instructions may be discarded in the future
        // the last instruction before prefetch is always be a branch or jump and we won't fetch other branch or jump during prefetch period thus checking `prefetch_buffer_rdata_may_change_pc` is adequate
        if (prefetch_buffer_rdata_may_change_pc) begin
          fetch_id_checkpoint_d = fetch_id_d;
        end
      end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        fetch_id_q <= 'd0;
        fetch_id_checkpoint_q <= 'd0;
      end else begin
        fetch_id_q <= fetch_id_d;
        fetch_id_checkpoint_q <= fetch_id_checkpoint_d;
        for (int i=0; i<ShuffleBuffSize; i++) begin
          inst_buffer_fetch_id_q[i] <= inst_buffer_fetch_id_d[i];
        end
      end
    end

    assign fetch_id_idex = inst_buffer_fetch_id_q[inst_buffer_remove_index];
  end else begin
    assign fetch_id_idex = 'd0;
  end

  if (DisplayBranchPredictionStat) begin
    int hit = 0;
    int miss = 0;
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (prefetch_predictor_predict_branch_q) begin
        if (prefetch_predictor_hit) begin
          hit <= hit + 1;
        end
        if (prefetch_predictor_miss) begin
          miss <= miss + 1;
        end
      end
      $display("Branch prediction accuracy = %f (hit = %d, miss = %d)", hit / real'(hit + miss), hit, miss);
    end
  end

  if (DisplayRNGStat) begin
    int unsigned rng_stat_cycle_count;
    int unsigned random_number_distribution [0:ShuffleBuffSize-1];

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rng_stat_cycle_count <= 'd0;
        for (int i=0; i<ShuffleBuffSize; i++) begin
          random_number_distribution[i] <= 'd0;
        end
      end else if (random_number_valid) begin
        rng_stat_cycle_count <= rng_stat_cycle_count + 'd1;
        random_number_distribution[random_number] <= random_number_distribution[random_number] + 'd1;
      end

      if (rng_stat_cycle_count % 10000 == 'd0) begin
        $display("Summary @%dcycles", rng_stat_cycle_count);
        for (int i=0; i<ShuffleBuffSize; i++) begin
          $display("%d: ", random_number_distribution[i]);
        end
      end
    end
  end

endmodule
