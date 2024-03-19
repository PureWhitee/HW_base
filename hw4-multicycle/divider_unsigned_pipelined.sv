/* INSERT NAME AND PENNKEY HERE */
/*Langyu Wang*/
/*Nan Cao*/
`timescale 1ns / 1ns

// quotient = dividend / divisor

module REG(
    input wire clk,
    input wire rst,
    input wire [31:0] i_dividend,
    input wire [31:0] i_divisor,
    input wire [31:0] i_remainder,
    input wire [31:0] i_quotient,

    output logic [31:0] o_dividend,
    output logic [31:0] o_divisor,
    output logic [31:0] o_remainder,
    output logic [31:0] o_quotient
);

always_ff @(posedge clk) begin
        if(rst) begin
            o_dividend <= 0;
            o_divisor <= 0;
            o_remainder <= 0;
            o_quotient <= 0;
        end else begin
            o_dividend <= i_dividend;
            o_divisor <= i_divisor;
            o_quotient <= i_quotient;
            o_remainder <= i_remainder;
        end
    end

endmodule

    

module divider_unsigned_pipelined (
    input wire clk, rst,
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

    logic [31:0] divisor_temp;

    // TODO: your code here
    //temp to store the reg value
    reg [31:0] remainder_temp; 
    reg [31:0] quotient_temp;
    reg [31:0] dividend_temp;

    //Stage 1
    logic [31:0] dividend_1 [16:0];
    logic [31:0] remainder_1[16:0]; 
    logic [31:0] quotient_1 [16:0];

    assign dividend_1[0] = i_dividend;
    assign remainder_1[0] = 0;
    assign quotient_1[0] = 0;

    genvar  i;
    generate
        for (i = 0; i < 16; i = i + 1) begin:loop1
            divu_1iter stage1(
                .i_dividend(dividend_1[i]),
                .i_divisor(i_divisor),
                .i_remainder(remainder_1[i]),
                .i_quotient(quotient_1[i]),
                .o_dividend(dividend_1[i+1]),
                .o_remainder(remainder_1[i+1]),
                .o_quotient(quotient_1[i+1])
            );
        end
    endgenerate

    
    //reg
    REG r1(
        .clk(clk),
        .rst(rst),
        .i_dividend(dividend_1[16]),
        .i_divisor(i_divisor),
        .i_remainder(remainder_1[16]),
        .i_quotient(quotient_1[16]),
        .o_dividend(dividend_2[0]),
        .o_divisor(divisor_temp),
        .o_remainder(remainder_2[0]),
        .o_quotient(quotient_2[0])
);


    //Stage 2
    logic [31:0] dividend_2 [16:0];
    logic [31:0] remainder_2[16:0]; 
    logic [31:0] quotient_2 [16:0];
    
    assign dividend_2[0] = dividend_temp;
    assign remainder_2[0] = remainder_temp;
    assign quotient_2[0] = quotient_temp;

    genvar j;
    generate
        for (j = 0; j < 16; j = j + 1) begin: loop2
                divu_1iter stage2(
                    .i_dividend(dividend_2[j]),
                    .i_divisor(divisor_temp),
                    .i_remainder(remainder_2[j]),
                    .i_quotient(quotient_2[j]),
                    .o_dividend(dividend_2[j+1]),
                    .o_remainder(remainder_2[j+1]),
                    .o_quotient(quotient_2[j+1])
                );
        end
    endgenerate
    
    assign o_quotient  = quotient_2[16];
    assign o_remainder = remainder_2[16];

    

endmodule


module divu_1iter (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    input  wire [31:0] i_remainder,
    input  wire [31:0] i_quotient,
    output wire [31:0] o_dividend,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

  // TODO: copy your code from HW2A here
    // temporary variables for operation
    wire [31:0] new_remainder;
    wire [31:0] new_quotient;

    // do the logic calculation
    assign new_remainder = (i_remainder << 1) | ((i_dividend >> 31) & 32'h1);
    assign new_quotient = (new_remainder < i_divisor) ? (i_quotient << 1) : ((i_quotient << 1) | 32'h1);

    // calculate the output value
    assign o_dividend = i_dividend << 1;
    assign o_remainder = (new_remainder < i_divisor) ? new_remainder : (new_remainder - i_divisor);
    assign o_quotient = new_quotient;

endmodule
