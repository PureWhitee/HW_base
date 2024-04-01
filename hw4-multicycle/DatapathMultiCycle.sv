/* INSERT NAME AND PENNKEY HERE */

`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

`ifndef RISCV_FORMAL
`include "../hw2b/cla.sv"
`include "divider_unsigned_pipelined.sv"
`include "../hw3-singlecycle/RvDisassembler.sv"
`endif

module RegFile (
    input logic [4:0] rd,
    input logic [`REG_SIZE] rd_data,
    input logic [4:0] rs1,
    output logic [`REG_SIZE] rs1_data,
    input logic [4:0] rs2,
    output logic [`REG_SIZE] rs2_data,

    input logic clk,
    input logic we,
    input logic rst
);

  // TODO: copy your HW3B code here
  localparam int NumRegs = 32;
  logic [`REG_SIZE] regs[NumRegs];

  // TODO: your code here
always_comb begin
  regs[0] = 32'd0;
  rs1_data = regs[rs1];
  rs2_data = regs[rs2];
end

always_ff @(posedge clk) begin
  if (rst) begin
      // Synchronous reset: set all registers to 0
      for (int i = 1; i < NumRegs; i = i + 1) begin
          regs[i] <= 32'd0;
      end
  end else if (we) begin
      // Write operation: write data to rd if we is high and rd is not 0
      if (rd != 0) begin
          regs[rd] <= rd_data;
      end
  end
end
endmodule

module DatapathMultiCycle (
    input wire clk,
    input wire rst,
    output logic halt,
    output logic [`REG_SIZE] pc_to_imem,
    input wire [`REG_SIZE] insn_from_imem,
    // addr_to_dmem is a read-write port
    output logic [`REG_SIZE] addr_to_dmem,
    input wire [`REG_SIZE] load_data_from_dmem,
    output logic [`REG_SIZE] store_data_to_dmem,
    output logic [3:0] store_we_to_dmem
);

  // TODO: your code here (largely based on HW3B)
  // components of the instruction
  wire [6:0] insn_funct7;
  wire [4:0] insn_rs2;
  wire [4:0] insn_rs1;
  wire [2:0] insn_funct3;
  wire [4:0] insn_rd;
  wire [`OPCODE_SIZE] insn_opcode;

  // split R-type instruction - see section 2.2 of RiscV spec
  assign {insn_funct7, insn_rs2, insn_rs1, insn_funct3, insn_rd, insn_opcode} = insn_from_imem;

  // setup for I, S, B & J type instructions
  // I - short immediates and loads
  wire [11:0] imm_i;
  assign imm_i = insn_from_imem[31:20];
  wire [4:0] imm_shamt = insn_from_imem[24:20];

  // S - stores
  wire [11:0] imm_s;
  assign imm_s[11:5] = insn_funct7, imm_s[4:0] = insn_rd;

  // B - conditionals
  wire [12:0] imm_b;
  assign {imm_b[12], imm_b[10:5]} = insn_funct7, {imm_b[4:1], imm_b[11]} = insn_rd, imm_b[0] = 1'b0;

  // J - unconditional jumps
  wire [20:0] imm_j;
  assign {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12], imm_j[0]} = {insn_from_imem[31:12], 1'b0};

  wire [`REG_SIZE] imm_i_sext = {{20{imm_i[11]}}, imm_i[11:0]};
  wire [`REG_SIZE] imm_s_sext = {{20{imm_s[11]}}, imm_s[11:0]};
  wire [`REG_SIZE] imm_b_sext = {{19{imm_b[12]}}, imm_b[12:0]};
  wire [`REG_SIZE] imm_j_sext = {{11{imm_j[20]}}, imm_j[20:0]};

  // opcodes - see section 19 of RiscV spec
  localparam bit [`OPCODE_SIZE] OpLoad = 7'b00_000_11;
  localparam bit [`OPCODE_SIZE] OpStore = 7'b01_000_11;
  localparam bit [`OPCODE_SIZE] OpBranch = 7'b11_000_11;
  localparam bit [`OPCODE_SIZE] OpJalr = 7'b11_001_11;
  localparam bit [`OPCODE_SIZE] OpMiscMem = 7'b00_011_11;
  localparam bit [`OPCODE_SIZE] OpJal = 7'b11_011_11;

  localparam bit [`OPCODE_SIZE] OpRegImm = 7'b00_100_11;
  localparam bit [`OPCODE_SIZE] OpRegReg = 7'b01_100_11;
  localparam bit [`OPCODE_SIZE] OpEnviron = 7'b11_100_11;

  localparam bit [`OPCODE_SIZE] OpAuipc = 7'b00_101_11;
  localparam bit [`OPCODE_SIZE] OpLui = 7'b01_101_11;

  wire insn_lui = insn_opcode == OpLui;
  wire insn_auipc = insn_opcode == OpAuipc;
  wire insn_jal = insn_opcode == OpJal;
  wire insn_jalr = insn_opcode == OpJalr;

  wire insn_beq = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b000;
  wire insn_bne = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b001;
  wire insn_blt = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b100;
  wire insn_bge = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b101;
  wire insn_bltu = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b110;
  wire insn_bgeu = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b111;

  wire insn_lb = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b000;
  wire insn_lh = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b001;
  wire insn_lw = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b010;
  wire insn_lbu = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b100;
  wire insn_lhu = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b101;

  wire insn_sb = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b000;
  wire insn_sh = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b001;
  wire insn_sw = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b010;

  wire insn_addi = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b000;
  wire insn_slti = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b010;
  wire insn_sltiu = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b011;
  wire insn_xori = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b100;
  wire insn_ori = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b110;
  wire insn_andi = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b111;

  wire insn_slli = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b001 && insn_from_imem[31:25] == 7'd0;
  wire insn_srli = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'd0;
  wire insn_srai = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'b0100000;

  wire insn_add = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b000 && insn_from_imem[31:25] == 7'd0;
  wire insn_sub  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b000 && insn_from_imem[31:25] == 7'b0100000;
  wire insn_sll = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b001 && insn_from_imem[31:25] == 7'd0;
  wire insn_slt = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b010 && insn_from_imem[31:25] == 7'd0;
  wire insn_sltu = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b011 && insn_from_imem[31:25] == 7'd0;
  wire insn_xor = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b100 && insn_from_imem[31:25] == 7'd0;
  wire insn_srl = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'd0;
  wire insn_sra  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'b0100000;
  wire insn_or = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b110 && insn_from_imem[31:25] == 7'd0;
  wire insn_and = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b111 && insn_from_imem[31:25] == 7'd0;

  wire insn_mul    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b000;
  wire insn_mulh   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b001;
  wire insn_mulhsu = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b010;
  wire insn_mulhu  = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b011;
  wire insn_div    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b100;
  wire insn_divu   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b101;
  wire insn_rem    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b110;
  wire insn_remu   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b111;

  wire insn_ecall = insn_opcode == OpEnviron && insn_from_imem[31:7] == 25'd0;
  wire insn_fence = insn_opcode == OpMiscMem;

  // synthesis translate_off
  // this code is only for simulation, not synthesis
  //`include "RvDisassembler.sv"
  string disasm_string;
  always_comb begin
    disasm_string = rv_disasm(insn_from_imem);
  end
  // HACK: get disasm_string to appear in GtkWave, which can apparently show only wire/logic...
  wire [(8*32)-1:0] disasm_wire;
  genvar i;
  for (i = 0; i < 32; i = i + 1) begin : gen_disasm
    assign disasm_wire[(((i+1))*8)-1:((i)*8)] = disasm_string[31-i];
  end
  // synthesis translate_on

  // program counter
  logic [`REG_SIZE] pcNext, pcCurrent;
  always @(posedge clk) begin
    if (rst) begin
      pcCurrent <= 32'd0;
    end else begin
      if (check_temp == 0) begin //normal
          pcCurrent <= pcNext;
          check = 0;
      end else if(check_temp == 1) begin 
          check = 1;             //div opration
      end
    end
  end
  assign pc_to_imem = pcCurrent;

  // cycle/insn_from_imem counters
  logic [`REG_SIZE] cycles_current, num_insns_current;
  always @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
      num_insns_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
      if (!rst) begin
        num_insns_current <= num_insns_current + 1;
      end
    end
  end

  //regfile part
  logic reg_wr_en;
  logic [`REG_SIZE] wb_data;
  logic [`REG_SIZE] rs1_data;
  logic [`REG_SIZE] rs2_data;
  logic check;
  logic check_temp;

  RegFile rf(
    .rd(insn_rd),
    .rd_data(wb_data),
    .rs1(insn_rs1),
    .rs1_data(rs1_data),
    .rs2(insn_rs2),
    .rs2_data(rs2_data),
    .clk(clk),
    .we(reg_wr_en),
    .rst(rst)
  );

  //cla part
  logic [`REG_SIZE] add1;
  logic [`REG_SIZE] add2;
  logic cin;
  logic [`REG_SIZE] sum;

  cla cla(
    .a(add1),
    .b(add2),
    .cin(cin),
    .sum(sum)
  );

  //muliply part
  logic [63:0] mul_result; 

  //divide part
  logic [`REG_SIZE] div_end;
  logic [`REG_SIZE] div_or;
  logic [`REG_SIZE] rem;
  logic [`REG_SIZE] quot;

  divider_unsigned_pipelined div(
    .clk(clk),
    .rst(rst),
    .i_dividend(div_end),
    .i_divisor(div_or),
    .o_remainder(rem),
    .o_quotient(quot)
  );

  logic illegal_insn;
  logic [`REG_SIZE] addr_temp;
  logic [`REG_SIZE] rs1_data_n;
  logic [1:0] byte_sel;

  logic [`REG_SIZE] my_store_data_to_dmem_logic;
  logic [`REG_SIZE] my_addr_to_dmem_logic;
  logic [3:0] my_store_we_to_dmem_logic;
  assign store_data_to_dmem = my_store_data_to_dmem_logic;
  assign addr_to_dmem = my_addr_to_dmem_logic;
  assign store_we_to_dmem = my_store_we_to_dmem_logic;

  always_comb begin
    illegal_insn = 1'b0;

    pcNext = pcCurrent + 32'd4;

    wb_data = 32'd0;
    reg_wr_en = 1'b0;

    add1 = 32'd0;
    add2 = 32'd0;
    cin = 1'b0;

    mul_result = 64'd0;
    rs1_data_n = 32'b0;

    div_end = 32'd0;
    div_or = 32'd0;

    halt = 1'b0;

    check_temp = 1'b0;

    addr_temp = 32'd0;
    my_addr_to_dmem_logic = 32'd0;
    my_store_data_to_dmem_logic = 32'd0;
    my_store_we_to_dmem_logic = 4'd0;
    byte_sel = 2'd0;

    case (insn_opcode)
      OpLui: begin
        // TODO: start here by implementing lui
        reg_wr_en = 1'b1;
        wb_data = {insn_from_imem[31:12],12'd0};
      end

      OpAuipc: begin
        reg_wr_en = 1;
        wb_data = pcCurrent + {insn_from_imem[31:12],12'd0};
      end

      OpRegImm: begin
        reg_wr_en = 1'b1;

        if(insn_addi) begin
          add1 = rs1_data;
          add2 = imm_i_sext;
          wb_data = sum;
        end else if(insn_slti) begin
          wb_data = ($signed(rs1_data) < $signed(imm_i_sext)) ? 1 : 0;
        end else if(insn_sltiu) begin
          wb_data = (rs1_data < imm_i_sext) ? 1 : 0;
        end else if(insn_xori) begin
          wb_data = rs1_data ^ imm_i_sext;
        end else if(insn_ori) begin
          wb_data = rs1_data | imm_i_sext;
        end else if(insn_andi) begin
          wb_data = rs1_data & imm_i_sext;
        end else if(insn_slli) begin
          wb_data = rs1_data << imm_shamt;
        end else if(insn_srli) begin
          wb_data = rs1_data >> imm_shamt;
        end else if(insn_srai) begin
          wb_data = $signed(rs1_data) >>> imm_shamt;
        end
      end

      OpRegReg: begin
        reg_wr_en = 1;
        if(insn_add) begin
          add1 = rs1_data;
          add2 = rs2_data;
          wb_data = sum;
        end else if(insn_sub) begin
          add1 = rs1_data;
          add2 = ~rs2_data + 32'd1;
          wb_data = sum;
        end else if(insn_sll) begin
          wb_data = rs1_data << rs2_data[4:0];
        end else if(insn_slt) begin
          wb_data = ($signed(rs1_data) < $signed(rs2_data)) ? 1 : 0;
        end else if(insn_sltu) begin
          wb_data = (rs1_data < rs2_data) ? 1 : 0;
        end else if(insn_xor) begin
          wb_data = rs1_data ^ rs2_data;
        end else if(insn_srl) begin
          wb_data = rs1_data >> rs2_data[4:0];
        end else if(insn_sra) begin
          wb_data = $signed(rs1_data) >>> rs2_data[4:0];
        end else if(insn_or) begin
          wb_data = rs1_data | rs2_data;
        end else if(insn_and) begin
          wb_data = rs1_data & rs2_data;
        end 

        //multiply
        else if (insn_mul) begin
          mul_result = rs1_data * rs2_data;
          wb_data = mul_result[31:0];
        end else if(insn_mulh) begin
          mul_result = {{32{rs1_data[31]}}, rs1_data} * {{32{rs2_data[31]}}, rs2_data};
          wb_data = mul_result[63:32];          
        end else if(insn_mulhsu) begin
          mul_result = {{32{rs1_data[31]}}, rs1_data} * {32'b0, rs2_data};
          wb_data = mul_result[63:32];
        end else if(insn_mulhu) begin
          mul_result = rs1_data * rs2_data;
          wb_data = mul_result[63:32];
        end

        //divide
        else if(insn_div) begin
          if (check == 0) begin 
            check_temp = 1;
          end else begin
            check_temp = 0;
          end

          div_end = rs1_data;
          if(rs2_data == 0) begin
            wb_data = 32'hFFFFFFFF;
          end else if (rs1_data == 32'h80000000) begin
            wb_data = 32'h80000000;
          end else if(rs1_data[31] == 1 && rs2_data[31] ==1) begin
            div_end = 32'h7FFFFFF & (~rs1_data +1);
            div_or = 32'h7FFFFFF & (~rs2_data + 1);
            wb_data = quot;            
          end else if(rs1_data[31] == 1 && rs2_data[31] == 0) begin
            div_end = 32'h7FFFFFF & (~rs1_data + 1);
            div_or = rs2_data;
            wb_data = ~quot + 1;
          end else if(rs1_data[31] == 0 && rs2_data[31] ==1) begin
            div_end = rs1_data;
            div_or = 32'h7FFFFFF & (~rs2_data + 1);
            wb_data = ~quot + 1;
          end else if(rs1_data[31] == 0 && rs2_data[31] ==0) begin
            div_end = rs1_data;
            div_or = rs2_data;
            wb_data = quot;
          end 
        end else if(insn_divu) begin
          if(check == 0) begin
            check_temp = 1;
          end else begin
            check_temp = 0;
          end

          div_end = rs1_data;
          div_or = rs2_data;
          wb_data = quot;
        end else if(insn_rem) begin
          if(check == 0) begin
            check_temp = 1;
          end else begin
            check_temp = 0;
          end

          if(rs2_data == 0) begin
            wb_data = rs1_data;
          end else if(rs1_data == 32'h80000000) begin
            wb_data = 0;
          end else if(rs1_data[31] == 1 && rs2_data[31] ==1) begin
            div_end = 32'h7FFFFFF & (~rs1_data + 1);
            div_or = 32'h7FFFFFF & (~rs2_data + 1);
            wb_data = ~rem + 1;            
          end else if(rs1_data[31] == 1 && rs2_data[31] == 0) begin
            div_end = 32'h7FFFFFF & (~rs1_data +1);
            div_or = rs2_data;
            wb_data = ~rem + 1;
          end else if(rs1_data[31] == 0 && rs2_data[31] ==1) begin
            div_end = rs1_data;
            div_or = 32'h7FFFFFF & (~rs2_data + 1);
            wb_data = rem;
          end else if(rs1_data[31] == 0 && rs2_data[31] == 0) begin
            div_end = rs1_data;
            div_or = rs2_data;
            wb_data = rem;
          end 
        end else if(insn_remu) begin
          if(check == 0) begin
            check_temp = 1;
          end else begin
            check_temp = 0;
          end

          div_end = rs1_data;
          div_or = rs2_data;
          wb_data =rem;
        end
      end  

        OpBranch: begin
          if(insn_beq) begin 
            pcNext = (rs1_data == rs2_data) ? ((pcCurrent + imm_b_sext) & ~3) : pcNext;
          end else if(insn_bne) begin
            pcNext = (rs1_data != rs2_data) ? ((pcCurrent + imm_b_sext) & ~3) : pcNext;
          end else if(insn_blt) begin
            pcNext = ($signed(rs1_data) < $signed(rs2_data)) ? ((pcCurrent + imm_b_sext) & ~3) : pcNext;
          end else if(insn_bge) begin
            pcNext = ($signed(rs1_data) >= $signed(rs2_data)) ? ((pcCurrent + imm_b_sext) & ~3) : pcNext;
          end else if(insn_bltu) begin
            pcNext = (rs1_data < rs2_data) ? ((pcCurrent + imm_b_sext) & ~3) : pcNext;
          end else if(insn_bgeu) begin
            pcNext = (rs1_data >= rs2_data) ? ((pcCurrent + imm_b_sext) & ~3) : pcNext;
          end 
        end

      OpEnviron: begin
        if(insn_ecall) begin
          halt = 1'b1;
        end
      end

      OpLoad: begin
        reg_wr_en = 1;
        addr_temp = rs1_data + imm_i_sext;
        byte_sel = addr_temp[1:0];
        my_addr_to_dmem_logic = addr_temp & ~3; 

        if(insn_lb) begin
          case(byte_sel)
            2'b00: begin
              wb_data = {{24{load_data_from_dmem[7]}}, load_data_from_dmem[7:0]};
            end
            2'b01: begin
              wb_data = {{24{load_data_from_dmem[15]}}, load_data_from_dmem[15:8]};
            end
            2'b10: begin
              wb_data = {{24{load_data_from_dmem[23]}}, load_data_from_dmem[23:16]};
            end
            2'b11: begin
              wb_data = {{24{load_data_from_dmem[31]}}, load_data_from_dmem[31:24]};
            end
          endcase
        end else if(insn_lh) begin
          case(byte_sel[1])
            1: begin
              wb_data = {{16{load_data_from_dmem[31]}}, load_data_from_dmem[31:16]};
            end
            0: begin
              wb_data = {{16{load_data_from_dmem[15]}}, load_data_from_dmem[15:0]};
            end
          endcase         
        end else if(insn_lw) begin
          wb_data = load_data_from_dmem;
        end else if(insn_lbu) begin
          case(byte_sel) 
            2'b00:begin
              wb_data = {24'b0, load_data_from_dmem[7:0]};
            end
            2'b01:begin
              wb_data = {24'b0, load_data_from_dmem[15:8]};
            end
            2'b10:begin
              wb_data = {24'b0, load_data_from_dmem[23:16]};
            end
            2'b11:begin
              wb_data = {24'b0, load_data_from_dmem[31:24]};
            end
          endcase
        end else if(insn_lhu) begin
          case(byte_sel[1])
            1: begin
              wb_data = {16'b0, load_data_from_dmem[31:16]};
            end
            0: begin
              wb_data = {16'b0, load_data_from_dmem[15:0]};
            end
          endcase   
        end        
      end      

      OpStore: begin
        addr_temp = rs1_data + imm_s_sext;
        byte_sel = addr_temp[1:0];
        my_addr_to_dmem_logic = addr_temp & ~3; 
        
        if(insn_sb) begin
          case (byte_sel) 
            2'b00: begin
              my_store_data_to_dmem_logic[7:0] = rs2_data[7:0];
              my_store_we_to_dmem_logic = 4'b0001;
            end
            2'b01: begin
              my_store_data_to_dmem_logic[15:8] = rs2_data[7:0];
              my_store_we_to_dmem_logic = 4'b0010;
            end
            2'b10: begin
              my_store_data_to_dmem_logic[23:16] = rs2_data[7:0];
              my_store_we_to_dmem_logic = 4'b0100;
            end
            2'b11: begin
              my_store_data_to_dmem_logic[31:24] = rs2_data[7:0];
              my_store_we_to_dmem_logic = 4'b1000;
            end
          endcase
        end if(insn_sh) begin
          case (byte_sel[1])
            1: begin
              my_store_data_to_dmem_logic[31:16] = rs2_data[15:0];
              my_store_we_to_dmem_logic = 4'b1100;
            end
            0: begin
              my_store_data_to_dmem_logic[15:0] = rs2_data[15:0];
              my_store_we_to_dmem_logic = 4'b0011;
            end
          endcase
        end else if(insn_sw) begin
          my_store_data_to_dmem_logic = rs2_data;
          my_store_we_to_dmem_logic = 4'b1111;
        end
      end

      OpJal: begin
        reg_wr_en = 1;
        wb_data = pcCurrent + 32'd4;
        pcNext = (pcCurrent + imm_j_sext) & ~3;
      end

      OpJalr: begin
        reg_wr_en = 1;
        wb_data = pcCurrent + 32'd4;
        pcNext = (rs1_data + imm_i_sext) & ~3;
      end

      OpMiscMem: begin
        if(insn_fence) begin

        end
      end
      
      default: begin
        illegal_insn = 1'b1;
      end
    endcase
  end
endmodule

module MemorySingleCycle #(
    parameter int NUM_WORDS = 512
) (
    // rst for both imem and dmem
    input wire rst,

    // clock for both imem and dmem. See RiscvProcessor for clock details.
    input wire clock_mem,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] pc_to_imem,

    // the value at memory location pc_to_imem
    output logic [`REG_SIZE] insn_from_imem,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] addr_to_dmem,

    // the value at memory location addr_to_dmem
    output logic [`REG_SIZE] load_data_from_dmem,

    // the value to be written to addr_to_dmem, controlled by store_we_to_dmem
    input wire [`REG_SIZE] store_data_to_dmem,

    // Each bit determines whether to write the corresponding byte of store_data_to_dmem to memory location addr_to_dmem.
    // E.g., 4'b1111 will write 4 bytes. 4'b0001 will write only the least-significant byte.
    input wire [3:0] store_we_to_dmem
);

  // memory is arranged as an array of 4B words
  logic [`REG_SIZE] mem[NUM_WORDS];

  initial begin
    $readmemh("mem_initial_contents.hex", mem, 0);
  end

  always_comb begin
    // memory addresses should always be 4B-aligned
    assert (pc_to_imem[1:0] == 2'b00);
    assert (addr_to_dmem[1:0] == 2'b00);
  end

  localparam int AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam int AddrLsb = 2;

  always @(posedge clock_mem) begin
    if (rst) begin
    end else begin
      insn_from_imem <= mem[{pc_to_imem[AddrMsb:AddrLsb]}];
    end
  end

  always @(negedge clock_mem) begin
    if (rst) begin
    end else begin
      if (store_we_to_dmem[0]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][7:0] <= store_data_to_dmem[7:0];
      end
      if (store_we_to_dmem[1]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][15:8] <= store_data_to_dmem[15:8];
      end
      if (store_we_to_dmem[2]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][23:16] <= store_data_to_dmem[23:16];
      end
      if (store_we_to_dmem[3]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][31:24] <= store_data_to_dmem[31:24];
      end
      // dmem is "read-first": read returns value before the write
      load_data_from_dmem <= mem[{addr_to_dmem[AddrMsb:AddrLsb]}];
    end
  end
endmodule

/*
This shows the relationship between clock_proc and clock_mem. The clock_mem is
phase-shifted 90° from clock_proc. You could think of one proc cycle being
broken down into 3 parts. During part 1 (which starts @posedge clock_proc)
the current PC is sent to the imem. In part 2 (starting @posedge clock_mem) we
read from imem. In part 3 (starting @negedge clock_mem) we read/write memory and
prepare register/PC updates, which occur at @posedge clock_proc.

        ____
 proc: |    |______
           ____
 mem:  ___|    |___
*/
module RiscvProcessor (
    input  wire  clock_proc,
    input  wire  clock_mem,
    input  wire  rst,
    output logic halt
);

  wire [`REG_SIZE] pc_to_imem, insn_from_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;

  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) mem (
      .rst      (rst),
      .clock_mem (clock_mem),
      // imem is read-only
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      // dmem is read-write
      .addr_to_dmem(mem_data_addr),
      .load_data_from_dmem(mem_data_loaded_value),
      .store_data_to_dmem (mem_data_to_write),
      .store_we_to_dmem  (mem_data_we)
  );

  DatapathMultiCycle datapath (
      .clk(clock_proc),
      .rst(rst),
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      .addr_to_dmem(mem_data_addr),
      .store_data_to_dmem(mem_data_to_write),
      .store_we_to_dmem(mem_data_we),
      .load_data_from_dmem(mem_data_loaded_value),
      .halt(halt)
  );

endmodule
