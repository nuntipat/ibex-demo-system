`include "shufflev_constant.sv"

module shufflev_rng #(
    parameter shufflev_rng_e RngType  = RandomTkacik,
    parameter int            RngSeed  = 123456,
    parameter int            MaxValue = 4
) (
    input logic clk_i,
    input logic rst_ni,

    output logic [MAX_VALUE_NUM_BIT-1:0] number_o,
    output logic valid_o
);
  localparam int unsigned MAX_VALUE_NUM_BIT = $clog2(MaxValue + 1);

  if (RngType == RandomSim) begin
    always_ff @(posedge clk_i or negedge rst_ni) begin
      number_o <= MAX_VALUE_NUM_BIT'({$random} % (MaxValue + 1));
      valid_o <= 1'b1;
    end
  end else if (RngType == RandomTkacik) begin
    logic rng_load_seed;
    logic [31:0] rng_number_o;

    shufflev_rng_tkacik u_rng_tkacik (
        .clk       (clk_i),
        .reset     (rst_ni),
        .loadseed_i(rng_load_seed),
        .seed_i    (RngSeed),
        .number_o  (rng_number_o)
    );

    logic has_load_seed;
    logic rng_number_valid;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rng_number_valid <= 1'b0;
        rng_load_seed <= 1'b0;
        has_load_seed <= 1'b0;
      end else if (!rng_load_seed && !has_load_seed) begin
        rng_load_seed <= 1'b1;
      end else if (rng_load_seed && !has_load_seed) begin
        has_load_seed <= 1'b1;
        rng_load_seed <= 1'b0;
      end else begin
        rng_number_valid <= 1'b1;
      end
    end

    // if the MaxValue is less than any power of two by 1 e.g. 1, 3, 7, 15 etc. we use as many bits as needed to produce the random result
    // otherwise, TBD
    if (!(|(MaxValue & (MaxValue + 1)))) begin
      assign number_o = rng_number_o[MAX_VALUE_NUM_BIT-1:0];
      assign valid_o  = rng_number_valid;

      logic [31:MAX_VALUE_NUM_BIT] unused_rng_number_o;
      assign unused_rng_number_o = rng_number_o[31:MAX_VALUE_NUM_BIT];
    end
  end

endmodule
