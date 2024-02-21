`timescale 1ns / 1ps

/**
 * @param a first 1-bit input
 * @param b second 1-bit input
 * @param g whether a and b generate a carry
 * @param p whether a and b would propagate an incoming carry
 */
module gp1(input wire a, b,
           output wire g, p);
   assign g = a & b;
   assign p = a | b;
endmodule

/**
 * Computes aggregate generate/propagate signals over a 4-bit window.
 * @param gin incoming generate signals
 * @param pin incoming propagate signals
 * @param cin the incoming carry
 * @param gout whether these 4 bits internally would generate a carry-out (independent of cin)
 * @param pout whether these 4 bits internally would propagate an incoming carry from cin
 * @param cout the carry outs for the low-order 3 bits
 */
module gp4(input wire [3:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [2:0] cout);

   // TODO: your code here
   assign cout[0] = gin[0]| pin[0]& cin;
   assign cout[1] = gin[1]| pin[1]& gin[0] | pin[1] & pin[0]& cin;
   assign cout[2] =
   gin[2]|
   pin[2] & gin[1]|
   pin[2] & pin[1]& gin[0]|
   pin[2]& pin[1] & pin[0] & cin;

   assign gout =
   gin[3] |
   pin[3] & gin[2]|
   pin[3] & pin[2] & gin[1]|
   pin[3] & pin[2] & pin[1] & gin[0];
   assign pout = & pin;

endmodule

/** Same as gp4 but for an 8-bit window instead */
module gp8(input wire [7:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [6:0] cout);

   // TODO: your code here
   wire g_tem0, p_tem0, g_tem1, p_tem1;
   gp4 cla0(
   .gin(gin[3:0]),
   .pin(pin[3:0]),
   .cin(cin),
   .gout(g_tem0),
   .pout(p_tem0),
   .cout(cout[2:0])
   );

   assign cout[3] = g_tem0 | p_tem0&cin;

   gp4 cla1(
   .gin(gin[7:4]),
   .pin(pin[7:4]),
   .cin(cout[3]),
   .gout(g_tem1),
   .pout(p_tem1),
   .cout(cout[6:4])
   );

   assign pout = p_tem1&p_tem0;
   assign gout = g_tem1 | p_tem1&g_tem0;

endmodule

module cla
  (input wire [31:0]  a, b,
   input wire         cin,
   output wire [31:0] sum);

   // TODO: your code here
   wire [31:0] gin, pin;
   wire [30:0] cout;
   wire gout_tem0, gout_tem1, gout_tem2, gout_tem3;
   wire pout_tem0, pout_tem1, pout_tem2, pout_tem3;
   wire ct1, ct2, ct3;

   genvar i;
   generate
   for(i = 0; i < 32; i++) begin: g_gp_loop
      gp1 gpi(
         .a(a[i]),
         .b(b[i]),
         .g(gin[i]),
         .p(pin[i])
      );
   end
   endgenerate

   gp8 cla0(
   .gin(gin[7:0]),
   .pin(pin[7:0]),
   .cin(cin),
   .gout(gout_tem0),
   .pout(pout_tem0),
   .cout(cout[6:0])
   );

   assign ct1 = gout_tem0 | pout_tem0&cin;
   assign cout[7] = ct1;
   gp8 cla1(
   .gin(gin[15:8]),
   .pin(pin[15:8]),
   .cin(ct1),
   .gout(gout_tem1),
   .pout(pout_tem1),
   .cout(cout[14:8])
   );

   assign ct2 = gout_tem1 | pout_tem1&ct1;
   assign cout[15] = ct2;
   gp8 cla2(
   .gin(gin[23:16]),
   .pin(pin[23:16]),
   .cin(ct2),
   .gout(gout_tem2),
   .pout(pout_tem2),
   .cout(cout[22:16])
   );

   assign ct3 = gout_tem2 | pout_tem2&ct2;
   assign cout[23] = ct3;
   gp8 cla3(
   .gin(gin[31:24]),
   .pin(pin[31:24]),
   .cin(ct3),
   .gout(gout_tem3),
   .pout(pout_tem3),
   .cout(cout[30:24])
   );

   genvar j;
   assign sum[0] = a[0] ^ b[0] ^ cin;
   generate
   for(j = 1; j < 32; j++) begin: g_sum_loop
      assign sum[j] = a[j] ^ b[j] ^ cout[j-1];
   end
   endgenerate

endmodule
