/* INSERT NAME AND PENNKEY HERE */

`timescale 1ns / 1ns

// quotient = dividend / divisor

module divider_unsigned (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

    // TODO: your 
    
    wire [31:0] dividend[32:0];
    wire [31:0] remainder[32:0];
    wire [31:0] quotient[32:0];

    assign dividend[0] = i_dividend;
    assign remainder[0] = 0;
    assign quotient[0] = 0; 

    genvar i;
    generate
        for(i = 0; i < 33; i = i + 1) begin: div_loop
        divu_1iter div_i(
            .i_dividend(dividend[i]),
            .i_divisor(i_divisor),
            .i_remainder(remainder[i]),
            .i_quotient(quotient[i]),
            .o_dividend(dividend[i+1]),
            .o_remainder(remainder[i+1]),
            .o_quotient(quotient[i+1])
            );
    end
    endgenerate

    assign o_quotient = quotient[32];
    assign o_remainder = remainder[32];
    
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
  /*
    for (int i = 0; i < 32; i++) {
        remainder = (remainder << 1) | ((dividend >> 31) & 0x1);
        if (remainder < divisor) {
            quotient = (quotient << 1);
        } else {
            quotient = (quotient << 1) | 0x1;
            remainder = remainder - divisor;
        }
        dividend = dividend << 1;
    }
    */

    // TODO: your code here

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
