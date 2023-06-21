// Adapt from OpenCores's systemc_rng by Javier Castillo
// See: https://opencores.org/projects/systemc_rng

module shufflev_rng_tkacik (
   input logic clk,
   input logic reset,
   input logic loadseed_i,
   input logic [31:0] seed_i,
   output logic [31:0] number_o
);
  logic [42:0] LFSR_reg;
  logic [36:0] CASR_reg;

  // CASR
  always @(posedge clk or negedge reset) begin
    if (!reset) begin
      CASR_reg <= 'd1;
    end else begin
      if (loadseed_i) begin
        CASR_reg <= {5'd0, seed_i};
      end else begin
        CASR_reg[36] <= CASR_reg[35] ^ CASR_reg[0];
        CASR_reg[35] <= CASR_reg[34] ^ CASR_reg[36];
        CASR_reg[34] <= CASR_reg[33] ^ CASR_reg[35];
        CASR_reg[33] <= CASR_reg[32] ^ CASR_reg[34];
        CASR_reg[32] <= CASR_reg[31] ^ CASR_reg[33];
        CASR_reg[31] <= CASR_reg[30] ^ CASR_reg[32];
        CASR_reg[30] <= CASR_reg[29] ^ CASR_reg[31];
        CASR_reg[29] <= CASR_reg[28] ^ CASR_reg[30];
        CASR_reg[28] <= CASR_reg[27] ^ CASR_reg[29];
        CASR_reg[27] <= CASR_reg[26] ^ CASR_reg[27] ^ CASR_reg[28];
        CASR_reg[26] <= CASR_reg[25] ^ CASR_reg[27];
        CASR_reg[25] <= CASR_reg[24] ^ CASR_reg[26];
        CASR_reg[24] <= CASR_reg[23] ^ CASR_reg[25];
        CASR_reg[23] <= CASR_reg[22] ^ CASR_reg[24];
        CASR_reg[22] <= CASR_reg[21] ^ CASR_reg[23];
        CASR_reg[21] <= CASR_reg[20] ^ CASR_reg[22];
        CASR_reg[20] <= CASR_reg[19] ^ CASR_reg[21];
        CASR_reg[19] <= CASR_reg[18] ^ CASR_reg[20];
        CASR_reg[18] <= CASR_reg[17] ^ CASR_reg[19];
        CASR_reg[17] <= CASR_reg[16] ^ CASR_reg[18];
        CASR_reg[16] <= CASR_reg[15] ^ CASR_reg[17];
        CASR_reg[15] <= CASR_reg[14] ^ CASR_reg[16];
        CASR_reg[14] <= CASR_reg[13] ^ CASR_reg[15];
        CASR_reg[13] <= CASR_reg[12] ^ CASR_reg[14];
        CASR_reg[12] <= CASR_reg[11] ^ CASR_reg[13];
        CASR_reg[11] <= CASR_reg[10] ^ CASR_reg[12];
        CASR_reg[10] <= CASR_reg[9] ^ CASR_reg[11];
        CASR_reg[9] <= CASR_reg[8] ^ CASR_reg[10];
        CASR_reg[8] <= CASR_reg[7] ^ CASR_reg[9];
        CASR_reg[7] <= CASR_reg[6] ^ CASR_reg[8];
        CASR_reg[6] <= CASR_reg[5] ^ CASR_reg[7];
        CASR_reg[5] <= CASR_reg[4] ^ CASR_reg[6];
        CASR_reg[4] <= CASR_reg[3] ^ CASR_reg[5];
        CASR_reg[3] <= CASR_reg[2] ^ CASR_reg[4];
        CASR_reg[2] <= CASR_reg[1] ^ CASR_reg[3];
        CASR_reg[1] <= CASR_reg[0] ^ CASR_reg[2];
        CASR_reg[0] <= CASR_reg[36] ^ CASR_reg[1];
      end
    end
  end
  
  //LFSR:
  always @(posedge clk or negedge reset) begin
    if (!reset) begin
      LFSR_reg <= 'd1;
    end else begin
      if (loadseed_i) begin
        LFSR_reg[42:32] <= 0;
        LFSR_reg[31:0] <= seed_i;
      end else begin
        LFSR_reg[42] <= LFSR_reg[41];
        LFSR_reg[41] <= LFSR_reg[40] ^ LFSR_reg[42];
        LFSR_reg[40] <= LFSR_reg[39];
        LFSR_reg[39] <= LFSR_reg[38];
        LFSR_reg[38] <= LFSR_reg[37];
        LFSR_reg[37] <= LFSR_reg[36];
        LFSR_reg[36] <= LFSR_reg[35];
        LFSR_reg[35] <= LFSR_reg[34];
        LFSR_reg[34] <= LFSR_reg[33];
        LFSR_reg[33] <= LFSR_reg[32];
        LFSR_reg[32] <= LFSR_reg[31];
        LFSR_reg[31] <= LFSR_reg[30];
        LFSR_reg[30] <= LFSR_reg[29];
        LFSR_reg[29] <= LFSR_reg[28];
        LFSR_reg[28] <= LFSR_reg[27];
        LFSR_reg[27] <= LFSR_reg[26];
        LFSR_reg[26] <= LFSR_reg[25];
        LFSR_reg[25] <= LFSR_reg[24];
        LFSR_reg[24] <= LFSR_reg[23];
        LFSR_reg[23] <= LFSR_reg[22];
        LFSR_reg[22] <= LFSR_reg[21];
        LFSR_reg[21] <= LFSR_reg[20];
        LFSR_reg[20] <= LFSR_reg[19] ^ LFSR_reg[42];
        LFSR_reg[19] <= LFSR_reg[18];
        LFSR_reg[18] <= LFSR_reg[17];
        LFSR_reg[17] <= LFSR_reg[16];
        LFSR_reg[16] <= LFSR_reg[15];
        LFSR_reg[15] <= LFSR_reg[14];
        LFSR_reg[14] <= LFSR_reg[13];
        LFSR_reg[13] <= LFSR_reg[12];
        LFSR_reg[12] <= LFSR_reg[11];
        LFSR_reg[11] <= LFSR_reg[10];
        LFSR_reg[10] <= LFSR_reg[9];
        LFSR_reg[9] <= LFSR_reg[8];
        LFSR_reg[8] <= LFSR_reg[7];
        LFSR_reg[7] <= LFSR_reg[6];
        LFSR_reg[6] <= LFSR_reg[5];
        LFSR_reg[5] <= LFSR_reg[4];
        LFSR_reg[4] <= LFSR_reg[3];
        LFSR_reg[3] <= LFSR_reg[2];
        LFSR_reg[2] <= LFSR_reg[1];
        LFSR_reg[1] <= LFSR_reg[0] ^ LFSR_reg[42];
        LFSR_reg[0] <= LFSR_reg[42];
      end
    end
  end

  always_ff @(posedge clk or negedge reset) begin
    if (!reset) begin
      number_o <= 'd0;
    end else begin
      number_o <= LFSR_reg[31:0] ^ CASR_reg[31:0];
    end
  end

endmodule
