module shufflev_prefetch_buffer #(
  parameter bit ResetAll        = 1'b0,
  parameter int unsigned DEPTH  = 5
) (
  input  logic        clk_i,
  input  logic        rst_ni,   // asynchronous reset

  input  logic        req_i,    // logic high while the core is awake otherwise false
                                // we ignore req_i and fill the fetch buffer anyway until it is full

  input  logic        branch_i, // assert when the core want to change PC (branch, jump, exception, etc.)
  input  logic [31:0] addr_i,

  input  logic        ready_i, 
  output logic        valid_o,
  output logic [31:0] rdata_o,
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

  localparam int unsigned DEPTH_NUM_BIT = $clog2(DEPTH+1);

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

  /* ............ */

  logic ibex_prefetch_buffer_rdata_branch_or_jump;  // a signal to indicate whether the current instruction (head of prefetch buffer) may change the PC 
  assign ibex_prefetch_buffer_rdata_branch_or_jump = (ibex_prefetch_buffer_rdata_o[6:0] == 7'b1101111) // jal
                                                  || (ibex_prefetch_buffer_rdata_o[6:0] == 7'b1100111) // jalr
                                                  || (ibex_prefetch_buffer_rdata_o[6:0] == 7'b1100011) // bxxx
                                                  || (ibex_prefetch_buffer_rdata_o[6:0] == 7'b0001111) // fench
                                                  || (ibex_prefetch_buffer_rdata_o[6:0] == 7'b1110011 
                                                      && ibex_prefetch_buffer_rdata_o[14:12] == 3'd0)  // ecall / ebreak
                                                  || (ibex_prefetch_buffer_rdata_o[1:0] == 2'b01 && ibex_prefetch_buffer_rdata_o[15:13] == 3'b001) // c.jal
                                                  || (ibex_prefetch_buffer_rdata_o[1:0] == 2'b01 && ibex_prefetch_buffer_rdata_o[15:13] == 3'b101) // c.j
                                                  || (ibex_prefetch_buffer_rdata_o[1:0] == 2'b01 && ibex_prefetch_buffer_rdata_o[15:13] == 3'b110) // c.beqz
                                                  || (ibex_prefetch_buffer_rdata_o[1:0] == 2'b01 && ibex_prefetch_buffer_rdata_o[15:13] == 3'b111) // c.bnez
                                                  || (ibex_prefetch_buffer_rdata_o[1:0] == 2'b10 && ibex_prefetch_buffer_rdata_o[15:13] == 3'b100 
                                                      && ibex_prefetch_buffer_rdata_o[6:2] == 5'b00000); // c.jr / c.ebreak / c.jalr
                                                  
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
    if (ibex_prefetch_buffer_rdata_branch_or_jump && ibex_prefetch_buffer_ready_i) begin
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

  /* Retrieve instruction from ibex prefetch buffer into our shuffling buffer */

  logic [DEPTH-1:0] [31:0]    inst_buffer_addr_d, inst_buffer_addr_q;
  logic [DEPTH-1:0] [31:0]    inst_buffer_data_d, inst_buffer_data_q;
  logic [DEPTH-1:0]           inst_buffer_valid_d, inst_buffer_valid_q;
  logic [DEPTH_NUM_BIT-1:0]   inst_buffer_start_ptr_d, inst_buffer_start_ptr_q; // TODO: replace with random logic
  logic [DEPTH_NUM_BIT-1:0]   inst_buffer_end_ptr_d, inst_buffer_end_ptr_q;     // TODO: replace with random logic

  logic                       inst_buffer_full, inst_buffer_not_empty;
  assign inst_buffer_full = &inst_buffer_valid_q;
  assign inst_buffer_not_empty = |inst_buffer_valid_q;

  always_comb begin
    for (int i=0; i<DEPTH; i++) begin
      inst_buffer_addr_d[i] = inst_buffer_addr_q[i];
      inst_buffer_data_d[i] = inst_buffer_data_q[i];
      inst_buffer_valid_d[i] = inst_buffer_valid_q[i];
    end
    inst_buffer_start_ptr_d = inst_buffer_start_ptr_q;
    inst_buffer_end_ptr_d = inst_buffer_end_ptr_q;

    ibex_prefetch_buffer_ready_i = 1'b0;

    // remove entry from the instruction buffer after it was sent to the ID/EX stage. we should remove the instruction first before adding a new one 
    // as start_ptr and end_ptr may point to the same entry and the valid bit should end up being set when we remove and add instruction in the same cycle
    if (ready_i && valid_o) begin
      inst_buffer_valid_d[inst_buffer_start_ptr_q] = 1'b0;
      inst_buffer_start_ptr_d = inst_buffer_start_ptr_q + 'd1;
      if (inst_buffer_start_ptr_d == DEPTH_NUM_BIT'(DEPTH)) begin
        inst_buffer_start_ptr_d = 'd0;
      end
    end

    // retrieve new instruction from the prefetch buffer when the prefetch buffer has valid data, the instruction buffer is not full and `discard_prefetch_buffer_q` is not asserted
    // Note:
    // - we still accept new instruction when the instruction buffer is full if one entry is being removed (ready_i and valid_o are both asserted)
    // - we ignore `discard_prefetch_buffer_q` when `latest_branch_not_taken` is asserted to avoid waiting for `discard_prefetch_buffer_q` to be deasserted in the next clock cycle
    //   this additional or-gate is optional but can help improve performance
    // TODO: test the case when branch_i is assert due to exception or interrupt
    if (!branch_i && ibex_prefetch_buffer_valid_o && (!inst_buffer_full || (ready_i && valid_o)) && (!discard_prefetch_buffer_q || latest_branch_not_taken)) begin
      ibex_prefetch_buffer_ready_i = 1'b1;
      inst_buffer_addr_d[inst_buffer_end_ptr_q] = ibex_prefetch_buffer_addr_o;
      inst_buffer_data_d[inst_buffer_end_ptr_q] = ibex_prefetch_buffer_rdata_o;
      inst_buffer_valid_d[inst_buffer_end_ptr_q] = 1'b1;
      inst_buffer_end_ptr_d = inst_buffer_end_ptr_q + 1;
      if (inst_buffer_end_ptr_d == DEPTH_NUM_BIT'(DEPTH)) begin
        inst_buffer_end_ptr_d = 'd0;
      end
    end
  end

  // other outputs to the ID/EX stage
  assign valid_o = inst_buffer_full || (inst_buffer_not_empty && discard_prefetch_buffer_q);  // instruction buffer may not be full if we are currently awaiting branch outcome
  assign rdata_o = inst_buffer_data_q[inst_buffer_start_ptr_q];
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
        inst_buffer_valid_q[i] <= inst_buffer_valid_d[i];
      end
      inst_buffer_start_ptr_q <= inst_buffer_start_ptr_d;
      inst_buffer_end_ptr_q <= inst_buffer_end_ptr_d;
    end
  end

endmodule
