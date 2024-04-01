`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// insns are 32 bits in RV32IM
`define INSN_SIZE 31:0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

`ifndef RISCV_FORMAL
`include "../hw2b/cla.sv"
`include "../hw3-singlecycle/RvDisassembler.sv"
`include "../hw4-multicycle/divider_unsigned_pipelined.sv"
`endif

module Disasm #(
    byte PREFIX = "D"
) (
    input wire [31:0] insn,
    output wire [(8*32)-1:0] disasm
);
  // synthesis translate_off
  // this code is only for simulation, not synthesis
  string disasm_string;
  always_comb begin
    disasm_string = rv_disasm(insn);
  end
  // HACK: get disasm_string to appear in GtkWave, which can apparently show only wire/logic. Also,
  // string needs to be reversed to render correctly.
  genvar i;
  for (i = 3; i < 32; i = i + 1) begin : gen_disasm
    assign disasm[((i+1-3)*8)-1-:8] = disasm_string[31-i];
  end
  assign disasm[255-:8] = PREFIX;
  assign disasm[247-:8] = ":";
  assign disasm[239-:8] = " ";
  // synthesis translate_on
endmodule

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
  localparam int NumRegs = 32;
  //genvar i;
  logic [`REG_SIZE] regs[NumRegs];

  // TODO: your code here
  always_comb begin
    regs[0] = 32'd0;
    rs1_data = regs[rs1];
    rs2_data = regs[rs2];
  end

  always_ff @(posedge clk) begin 
    if(rst) begin
      for(int i = 1; i < NumRegs; i++) begin 
        regs[i] <= 32'd0;
      end
    end else if (we) begin 
      if (rd != 0) begin 
        regs[rd] <= rd_data; 
      end
    end
  end
endmodule

/**
 * This enum is used to classify each cycle as it comes through the Writeback stage, identifying
 * if a valid insn is present or, if it is a stall cycle instead, the reason for the stall. The
 * enum values are mutually exclusive: only one should be set for any given cycle. These values
 * are compared against the trace-*.json files to ensure that the datapath is running with the
 * correct timing.
 *
 * You will need to set these values at various places within your pipeline, and propagate them
 * through the stages until they reach Writeback where they can be checked.
 */
typedef enum {
  /** invalid value, this should never appear after the initial reset sequence completes */
  CYCLE_INVALID = 0,
  /** a stall cycle that arose from the initial reset signal */
  CYCLE_RESET = 1,
  /** not a stall cycle, a valid insn is in Writeback */
  CYCLE_NO_STALL = 2,
  /** a stall cycle that arose from a taken branch/jump */
  CYCLE_TAKEN_BRANCH = 4,

  // the values below are only needed in HW5B

  /** a stall cycle that arose from a load-to-use stall */
  CYCLE_LOAD2USE = 8,
  /** a stall cycle that arose from a div/rem-to-use stall */
  CYCLE_DIV2USE = 16,
  /** a stall cycle that arose from a fence.i insn */
  CYCLE_FENCEI = 32
} cycle_status_e;

/** state at the start of Decode stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
} stage_decode_t;

/** state at the start of Execute stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`REG_SIZE] rs1;
  logic [`REG_SIZE] rs2;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  logic [`OPCODE_SIZE] opcode;
  logic [4:0] rd;
  logic [4:0] rs1_addr;
  logic [4:0] rs2_addr;
  logic [11:0] imm_i;
  logic [4:0] imm_shamt;
  logic [11:0] imm_s;
  logic [12:0] imm_b;
  logic [20:0] imm_j;
} stage_execute_t;

/** state at the start of Memory stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`REG_SIZE] o;
  logic [`REG_SIZE] b;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  logic [`OPCODE_SIZE] opcode;
  logic [4:0] rd;
  logic w;
  logic [4:0] rs1_addr;
  logic [4:0] rs2_addr;
} stage_memory_t;

/** state at the start of Writeback stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`REG_SIZE] o;
  logic [`REG_SIZE] d;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  logic [`OPCODE_SIZE] opcode;
  logic [4:0] rd;
  logic w;  
  logic [4:0] rs1_addr;
  logic [4:0] rs2_addr;
} stage_writeback_t;


module DatapathPipelined (
    input wire clk,
    input wire rst,
    output logic [`REG_SIZE] pc_to_imem,
    input wire [`INSN_SIZE] insn_from_imem,
    // dmem is read/write
    output logic [`REG_SIZE] addr_to_dmem,
    input wire [`REG_SIZE] load_data_from_dmem,
    output logic [`REG_SIZE] store_data_to_dmem,
    output logic [3:0] store_we_to_dmem,

    output logic halt,

    // The PC of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`REG_SIZE] trace_writeback_pc,
    // The bits of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`INSN_SIZE] trace_writeback_insn,
    // The status of the insn (or stall) currently in Writeback. See cycle_status_e enum for valid values.
    output cycle_status_e trace_writeback_cycle_status
);

  // opcodes - see section 19 of RiscV spec
  localparam bit [`OPCODE_SIZE] OpcodeLoad = 7'b00_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeStore = 7'b01_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeBranch = 7'b11_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeJalr = 7'b11_001_11;
  localparam bit [`OPCODE_SIZE] OpcodeMiscMem = 7'b00_011_11;
  localparam bit [`OPCODE_SIZE] OpcodeJal = 7'b11_011_11;

  localparam bit [`OPCODE_SIZE] OpcodeRegImm = 7'b00_100_11;
  localparam bit [`OPCODE_SIZE] OpcodeRegReg = 7'b01_100_11;
  localparam bit [`OPCODE_SIZE] OpcodeEnviron = 7'b11_100_11;

  localparam bit [`OPCODE_SIZE] OpcodeAuipc = 7'b00_101_11;
  localparam bit [`OPCODE_SIZE] OpcodeLui = 7'b01_101_11;

  // cycle counter, not really part of any stage but useful for orienting within GtkWave
  // do not rename this as the testbench uses this value
  logic [`REG_SIZE] cycles_current;
  always_ff @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
    end
  end

  /***************/
  /* FETCH STAGE */
  /***************/

  logic [`REG_SIZE] f_pc_current, pc_next; //pc_next is for branch 
  wire [`REG_SIZE] f_insn;
  cycle_status_e f_cycle_status;

  // program counter
  always_ff @(posedge clk) begin
    if (rst) begin
      f_pc_current <= 32'd0;
      // NB: use CYCLE_NO_STALL since this is the value that will persist after the last reset cycle
      f_cycle_status <= CYCLE_NO_STALL;
    end else begin
      f_cycle_status <= CYCLE_NO_STALL;
      if(f_rst == 1'b1) begin
        f_pc_current <= pc_next;
      end else begin
        if(check_temp == 0) begin
          f_pc_current <= f_pc_current + 4;
          check <= 0;
        end else if(check_temp == 1) begin
          check <= 1;
        end
      end
    end
  end
  // send PC to imem
  assign pc_to_imem = f_pc_current;
  assign f_insn = insn_from_imem;

  // Here's how to disassemble an insn into a string you can view in GtkWave.
  // Use PREFIX to provide a 1-character tag to identify which stage the insn comes from.
  wire [255:0] f_disasm;
  Disasm #(
      .PREFIX("F")
  ) disasm_0fetch (
      .insn  (f_insn),
      .disasm(f_disasm)
  );

  /****************/
  /* DECODE STAGE */
  /****************/

  // this shows how to package up state in a `struct packed`, and how to pass it between stages
  stage_decode_t decode_state;

  always_ff @(posedge clk) begin
    if (rst) begin
      decode_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET
      };
    end else if (f_rst) begin
      decode_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_TAKEN_BRANCH
      };
    end else begin
      begin
        decode_state <= '{
          pc: f_pc_current,
          insn: f_insn,
          cycle_status: f_cycle_status
        };
      end
    end
  end
  wire [255:0] d_disasm;
  Disasm #(
      .PREFIX("D")
  ) disasm_1decode (
      .insn  (decode_state.insn),
      .disasm(d_disasm)
  );

  // TODO: your code here, though you will also need to modify some of the code above
  // TODO: the testbench requires that your register file instance is named `rf`
  cycle_status_e d_cycle_status;
  assign d_cycle_status = decode_state.cycle_status;

  logic [`REG_SIZE] d_pc_current;
  assign d_pc_current = decode_state.pc;

  wire  [`REG_SIZE] d_insn;  
  assign d_insn = decode_state.insn;
  
  logic [`OPCODE_SIZE] d_opcode;
  assign d_opcode = insn_opcode;
  
  wire [6:0] insn_funct7;
  wire [4:0] insn_rs2;
  wire [4:0] insn_rs1;
  wire [2:0] insn_funct3;
  wire [4:0] insn_rd;
  wire [`OPCODE_SIZE] insn_opcode;
  
  logic check;
  logic check_temp;

  // split R-type instruction - see section 2.2 of RiscV spec
  assign {insn_funct7, insn_rs2, insn_rs1, insn_funct3, insn_rd, insn_opcode} = d_insn;

  // instatiate the regfile
  logic [4:0] rd_addr, rs1_addr, rs2_addr;
  logic [`REG_SIZE] rd_data, rs1_data, rs2_data;
  logic w_en;

  RegFile rf(
    .rd(rd_addr),
    .rd_data(rd_data),
    .rs1(rs1_addr),
    .rs1_data(rs1_data),
    .rs2(rs2_addr),
    .rs2_data(rs2_data),
    .clk(clk),
    .we(w_en),
    .rst(rst)
  );


  // forwarding pass values from d to x
  logic  [`REG_SIZE] d_out_rs1_data;
  logic  [`REG_SIZE] d_out_rs2_data;
  logic  illegal_insn_d;
  logic [4:0] d_rd;
  logic d_we;

  logic [`REG_SIZE] rs1_data_temp, rs2_data_temp;

  always_comb begin 
    rs1_addr = 5'd0;
    rs2_addr = 5'd0;
    rs1_data_temp = 32'd0;
    rs2_data_temp = 32'd0;  
    illegal_insn_d = 1'b0;

    d_rd = 5'd0;
    d_we = 1'b0;

    case(insn_opcode)
      OpcodeLoad: begin 
        d_we = 1'b1;
        d_rd = insn_rd;
        rs1_addr = insn_rs1; 
        rs1_data_temp = rs1_data;
      end

      OpcodeStore: begin
        rs1_addr = insn_rs1;
        rs2_addr = insn_rs2;
        rs1_data_temp =  rs1_data;
        rs2_data_temp =  rs2_data;
      end

      OpcodeBranch: begin
        rs1_addr = insn_rs1;
        rs2_addr = insn_rs2;
        rs1_data_temp = rs1_data;
        rs2_data_temp = rs2_data;
      end

      OpcodeJalr: begin 
        d_we = 1'b1;
        d_rd = insn_rd;
        rs1_addr = insn_rs1;
        rs1_data_temp = rs1_data;
      end

      OpcodeMiscMem: begin
        //no need
      end

      OpcodeJal: begin 
        d_we = 1'b1;
        d_rd = insn_rd;
      end

      OpcodeRegImm: begin
        d_we = 1'b1;
        d_rd = insn_rd;
        rs1_addr = insn_rs1;
        rs1_data_temp = rs1_data;
      end

      OpcodeRegReg: begin
        d_we = 1'b1;
        d_rd = insn_rd;
        rs1_addr = insn_rs1;
        rs2_addr = insn_rs2;
        rs1_data_temp = rs1_data;
        rs2_data_temp = rs2_data;
      end

      OpcodeEnviron: begin
      // no deed
      end

      OpcodeAuipc: begin
        d_we = 1'b1;
        d_rd = insn_rd; 
      end

      OpcodeLui: begin
        d_we = 1'b1;
        d_rd = insn_rd;
      end

      default: begin
        illegal_insn_d = 1'b1;
      end
    endcase
    d_rd =  d_we ? d_rd : 5'b0; 
  end
  
  logic [4:0] d_rs1_addr, d_rs2_addr;
  assign d_rs1_addr = insn_rs1;
  assign d_rs2_addr = insn_rs2;

  always@* begin
    if(w_rd == d_rs1_addr && w_rd != 0) begin
      d_out_rs1_data = w_out;
    end else begin
      d_out_rs1_data = rs1_data_temp;
    end
    if(w_rd == d_rs2_addr && w_rd != 0) begin
      d_out_rs2_data = w_out;
    end else begin
      d_out_rs2_data = rs2_data_temp;
    end
  end

// setup for I, S, B & J type instructions
// I - short immediates and loads
wire [11:0] d_imm_i;
assign d_imm_i = d_insn[31:20];
wire [4:0] d_imm_shamt = d_insn[24:20];

// S - stores
wire [11:0] d_imm_s;
assign d_imm_s[11:5] = insn_funct7, d_imm_s[4:0] = insn_rd;

// B - conditionals
wire [12:0] d_imm_b;
assign {d_imm_b[12], d_imm_b[10:5]} = insn_funct7, {d_imm_b[4:1], d_imm_b[11]} = insn_rd, d_imm_b[0] = 1'b0;

// J - unconditional jumps
wire [20:0] d_imm_j;
assign {d_imm_j[20], d_imm_j[10:1], d_imm_j[11], d_imm_j[19:12], d_imm_j[0]} = {d_insn[31:12], 1'b0};



  /*****************/
  /* EXECUTE STAGE */
  /*****************/
  stage_execute_t execute_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      execute_state <= '{
        pc: 0,
        rs1: 0,
        rs2: 0,
        insn: 0,
        cycle_status: CYCLE_RESET,
        opcode: 0,
        rd: 0,
        rs1_addr: 0,
        rs2_addr: 0,
        imm_i: 0,
        imm_shamt: 0,
        imm_s: 0,
        imm_b: 0,
        imm_j: 0
      };
    end else if (d_rst) begin
      execute_state <= '{
        pc: 0,
        rs1: 0,
        rs2: 0,
        insn: 0,
        cycle_status: CYCLE_TAKEN_BRANCH,
        opcode: 0,
        rd: 0,
        rs1_addr: 0,
        rs2_addr: 0,
        imm_i: 0,
        imm_shamt: 0,
        imm_s: 0,
        imm_b: 0,
        imm_j: 0
      };
    end else begin
      begin
        execute_state <= '{
          pc: d_pc_current,
          rs1: d_out_rs1_data,
          rs2: d_out_rs2_data,
          insn: d_insn,
          cycle_status: d_cycle_status,
          opcode: d_opcode,
          rd: d_rd,
          rs1_addr: d_rs1_addr,
          rs2_addr: d_rs2_addr,
          imm_i: d_imm_i,
          imm_shamt: d_imm_shamt,
          imm_s: d_imm_s,
          imm_b: d_imm_b,
          imm_j: d_imm_j
        };
      end
    end
  end
  wire [255:0] x_disasm;
  Disasm #(
      .PREFIX("X")
  ) disasm_1execute (
      .insn  (execute_state.insn),
      .disasm(x_disasm)
  );

logic [`REG_SIZE] x_pc_current;
logic [`REG_SIZE] x_in_rs1_data;
logic [`REG_SIZE] x_in_rs2_data;
logic [`REG_SIZE] x_insn;
cycle_status_e x_cycle_status;
logic [`OPCODE_SIZE] x_opcode;
logic [4:0] x_rs1_addr, x_rs2_addr;

assign x_pc_current = execute_state.pc;
assign x_in_rs1_data = execute_state.rs1;
assign x_in_rs2_data = execute_state.rs2;
assign x_insn = execute_state.insn;
assign x_cycle_status = execute_state.cycle_status;
assign x_opcode = execute_state.opcode;
assign x_rs1_addr = execute_state.rs1_addr;
assign x_rs2_addr = execute_state.rs2_addr;

logic [`REG_SIZE] x_out_o;
logic [`REG_SIZE] x_out_b;
logic [4:0] x_rd;
logic x_we;

logic[`REG_SIZE] x_rs1, x_rs2;
logic f_rst;
logic d_rst;

logic [11:0] x_imm_i;
logic [4:0] x_imm_shamt;
logic [11:0] x_imm_s;
logic [12:0] x_imm_b;
logic [20:0] x_imm_j;

assign x_imm_i = execute_state.imm_i;
assign x_imm_shamt = execute_state.imm_shamt;
assign x_imm_s = execute_state.imm_s;
assign x_imm_b = execute_state.imm_b;
assign x_imm_j = execute_state.imm_j;

wire [`REG_SIZE] x_imm_i_sext = {{20{x_imm_i[11]}}, x_imm_i[11:0]};
wire [`REG_SIZE] x_imm_s_sext = {{20{x_imm_s[11]}}, x_imm_s[11:0]};
wire [`REG_SIZE] x_imm_b_sext = {{19{x_imm_b[12]}}, x_imm_b[12:0]};
wire [`REG_SIZE] x_imm_j_sext = {{11{x_imm_j[20]}}, x_imm_j[20:0]};

always@* begin
  if(m_rd == x_rs1_addr && m_rd != 0) begin
    x_rs1 = m_out_o;
  end else if (w_rd == x_rs1_addr && w_rd != 0) begin
    x_rs1 = w_out;
  end else begin 
    x_rs1 = x_in_rs1_data;
  end

  if(m_rd == x_rs2_addr && m_rd != 0) begin
    x_rs2 = m_out_o;
  end else if (w_rd == x_rs2_addr && w_rd != 0) begin
    x_rs2 = w_out;
  end else begin
    x_rs2 = x_in_rs2_data;
  end
end

//******************************************************************************************************//
//**************************************initial for execute*********************************************//
//******************************************************************************************************//

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
  logic [1:0] byte_sel;

  logic [`REG_SIZE] my_store_data_to_dmem_logic;
  logic [`REG_SIZE] my_addr_to_dmem_logic;
  logic [3:0] my_store_we_to_dmem_logic;
  assign store_data_to_dmem = my_store_data_to_dmem_logic;
  assign addr_to_dmem = my_addr_to_dmem_logic;
  assign store_we_to_dmem = my_store_we_to_dmem_logic;


//***************************************************************************************************************//
//***************************************************************************************************************//
//***************************************************************************************************************//
//***************************************************************************************************************//
// opcodes for specific insn - see section 19 of RiscV spec
wire insn_lui = x_opcode == OpcodeLui;
wire insn_auipc = x_opcode == OpcodeAuipc;
wire insn_jal = x_opcode == OpcodeJal;
wire insn_jalr = x_opcode == OpcodeJalr;

wire insn_beq = x_opcode == OpcodeBranch && x_insn[14:12] == 3'b000;
wire insn_bne = x_opcode == OpcodeBranch && x_insn[14:12] == 3'b001;
wire insn_blt = x_opcode == OpcodeBranch && x_insn[14:12] == 3'b100;
wire insn_bge = x_opcode == OpcodeBranch && x_insn[14:12] == 3'b101;
wire insn_bltu = x_opcode == OpcodeBranch && x_insn[14:12] == 3'b110;
wire insn_bgeu = x_opcode == OpcodeBranch && x_insn[14:12] == 3'b111;

wire insn_lb = x_opcode == OpcodeLoad && x_insn[14:12] == 3'b000;
wire insn_lh = x_opcode == OpcodeLoad && x_insn[14:12] == 3'b001;
wire insn_lw = x_opcode == OpcodeLoad && x_insn[14:12] == 3'b010;
wire insn_lbu = x_opcode == OpcodeLoad && x_insn[14:12] == 3'b100;
wire insn_lhu = x_opcode == OpcodeLoad && x_insn[14:12] == 3'b101;

wire insn_sb = x_opcode == OpcodeStore && x_insn[14:12] == 3'b000;
wire insn_sh = x_opcode == OpcodeStore && x_insn[14:12] == 3'b001;
wire insn_sw = x_opcode == OpcodeStore && x_insn[14:12] == 3'b010;

wire insn_addi = x_opcode == OpcodeRegImm && x_insn[14:12] == 3'b000;
wire insn_slti = x_opcode == OpcodeRegImm && x_insn[14:12] == 3'b010;
wire insn_sltiu = x_opcode == OpcodeRegImm && x_insn[14:12] == 3'b011;
wire insn_xori = x_opcode == OpcodeRegImm && x_insn[14:12] == 3'b100;
wire insn_ori = x_opcode == OpcodeRegImm && x_insn[14:12] == 3'b110;
wire insn_andi = x_opcode == OpcodeRegImm && x_insn[14:12] == 3'b111;

wire insn_slli = x_opcode == OpcodeRegImm && x_insn[14:12] == 3'b001 && x_insn[31:25] == 7'd0;
wire insn_srli = x_opcode == OpcodeRegImm && x_insn[14:12] == 3'b101 && x_insn[31:25] == 7'd0;
wire insn_srai = x_opcode == OpcodeRegImm && x_insn[14:12] == 3'b101 && x_insn[31:25] == 7'b0100000;

wire insn_add = x_opcode == OpcodeRegReg && x_insn[14:12] == 3'b000 && x_insn[31:25] == 7'd0;
wire insn_sub  = x_opcode == OpcodeRegReg && x_insn[14:12] == 3'b000 && x_insn[31:25] == 7'b0100000;
wire insn_sll = x_opcode == OpcodeRegReg && x_insn[14:12] == 3'b001 && x_insn[31:25] == 7'd0;
wire insn_slt = x_opcode == OpcodeRegReg && x_insn[14:12] == 3'b010 && x_insn[31:25] == 7'd0;
wire insn_sltu = x_opcode == OpcodeRegReg && x_insn[14:12] == 3'b011 && x_insn[31:25] == 7'd0;
wire insn_xor = x_opcode == OpcodeRegReg && x_insn[14:12] == 3'b100 && x_insn[31:25] == 7'd0;
wire insn_srl = x_opcode == OpcodeRegReg && x_insn[14:12] == 3'b101 && x_insn[31:25] == 7'd0;
wire insn_sra  = x_opcode == OpcodeRegReg && x_insn[14:12] == 3'b101 && x_insn[31:25] == 7'b0100000;
wire insn_or = x_opcode == OpcodeRegReg && x_insn[14:12] == 3'b110 && x_insn[31:25] == 7'd0;
wire insn_and = x_opcode == OpcodeRegReg && x_insn[14:12] == 3'b111 && x_insn[31:25] == 7'd0;

wire insn_mul    = x_opcode == OpcodeRegReg && x_insn[31:25] == 7'd1 && x_insn[14:12] == 3'b000;
wire insn_mulh   = x_opcode == OpcodeRegReg && x_insn[31:25] == 7'd1 && x_insn[14:12] == 3'b001;
wire insn_mulhsu = x_opcode == OpcodeRegReg && x_insn[31:25] == 7'd1 && x_insn[14:12] == 3'b010;
wire insn_mulhu  = x_opcode == OpcodeRegReg && x_insn[31:25] == 7'd1 && x_insn[14:12] == 3'b011;
wire insn_div    = x_opcode == OpcodeRegReg && x_insn[31:25] == 7'd1 && x_insn[14:12] == 3'b100;
wire insn_divu   = x_opcode == OpcodeRegReg && x_insn[31:25] == 7'd1 && x_insn[14:12] == 3'b101;
wire insn_rem    = x_opcode == OpcodeRegReg && x_insn[31:25] == 7'd1 && x_insn[14:12] == 3'b110;
wire insn_remu   = x_opcode == OpcodeRegReg && x_insn[31:25] == 7'd1 && x_insn[14:12] == 3'b111;

wire insn_ecall = x_opcode == OpcodeEnviron && x_insn[31:7] == 25'd0;
wire insn_fence = x_opcode == OpcodeMiscMem;
//***************************************************************************************************************//
//***************************************************************************************************************//
//***************************************************************************************************************//
//***************************************************************************************************************//

always_comb begin 
    illegal_insn = 1'b0;

    x_out_o = 32'd0;

    x_we = 1'b0;

    add1 = 32'd0;
    add2 = 32'd0;
    cin = 1'b0;

    mul_result = 64'd0;

    div_end = 32'd0;
    div_or = 32'd0;

    check_temp = 1'b0;

    addr_temp = 32'd0;
    my_addr_to_dmem_logic = 32'd0;
    my_store_data_to_dmem_logic = 32'd0;
    my_store_we_to_dmem_logic = 4'd0;
    byte_sel = 2'd0;

    pc_next = 32'd0;

    f_rst = 1'b0;
    d_rst = 1'b0;

case (x_opcode)
      OpcodeLui: begin
        x_we = 1'b1;
        x_out_o = {x_insn[31:12],12'd0};
      end

      OpcodeAuipc: begin
        x_we = 1'b1;
        x_out_o = x_pc_current + {x_insn[31:12],12'd0};
      end

      OpcodeRegImm: begin
        x_we = 1'b1;

        if(insn_addi) begin
          add1 = x_rs1;
          add2 = x_imm_i_sext;
          x_out_o = sum;
        end else if(insn_slti) begin
          x_out_o = ($signed(x_rs1) < $signed(x_imm_i_sext)) ? 1 : 0;
        end else if(insn_sltiu) begin
          x_out_o = (x_rs1 < x_imm_i_sext) ? 1 : 0;
        end else if(insn_xori) begin
          x_out_o = x_rs1 ^ x_imm_i_sext;
        end else if(insn_ori) begin
          x_out_o = x_rs1 | x_imm_i_sext;
        end else if(insn_andi) begin
          x_out_o = x_rs1 & x_imm_i_sext;
        end else if(insn_slli) begin
          x_out_o = x_rs1 << x_imm_shamt;
        end else if(insn_srli) begin
          x_out_o = x_rs1 >> x_imm_shamt;
        end else if(insn_srai) begin
          x_out_o = $signed(x_rs1) >>> x_imm_shamt;
        end
      end

      OpcodeRegReg: begin
        x_we = 1'b1;
        
        if(insn_add) begin
          add1 = x_rs1;
          add2 = x_rs2;
          x_out_o = sum;
        end else if(insn_sub) begin
          add1 = x_rs1;
          add2 = ~x_rs2 + 32'd1;
          x_out_o = sum;
        end else if(insn_sll) begin
          x_out_o = x_rs1 << x_rs2[4:0];
        end else if(insn_slt) begin
          x_out_o = ($signed(x_rs1) < $signed(x_rs2)) ? 1 : 0;
        end else if(insn_sltu) begin
          x_out_o = (x_rs1 < x_rs2) ? 1 : 0;
        end else if(insn_xor) begin
          x_out_o = x_rs1 ^ x_rs2;
        end else if(insn_srl) begin
          x_out_o = x_rs1 >> x_rs2[4:0];
        end else if(insn_sra) begin
          x_out_o = $signed(x_rs1) >>> x_rs2[4:0];
        end else if(insn_or) begin
          x_out_o = x_rs1 | x_rs2;
        end else if(insn_and) begin
          x_out_o = x_rs1 & x_rs2;
        end 

        //multiply
        else if (insn_mul) begin
          mul_result = x_rs1 * x_rs2;
          x_out_o = mul_result[31:0];
        end else if(insn_mulh) begin
          mul_result = {{32{x_rs1[31]}}, x_rs1} * {{32{x_rs2[31]}}, x_rs2};
          x_out_o = mul_result[63:32];          
        end else if(insn_mulhsu) begin
          mul_result = {{32{x_rs1[31]}}, x_rs1} * {32'b0, x_rs2};
          x_out_o = mul_result[63:32];
        end else if(insn_mulhu) begin
          mul_result = x_rs1 * x_rs2;
          x_out_o = mul_result[63:32];
        end

        //divide
        else if(insn_div) begin
          if (check == 0) begin 
            check_temp = 1;
          end else begin
            check_temp = 0;
          end

          div_end = x_rs1;
          if(x_rs2 == 0) begin
            x_out_o = 32'hFFFFFFFF;
          end else if (x_rs1 == 32'h80000000) begin
            x_out_o = 32'h80000000;
          end else if(x_rs1[31] == 1 && x_rs2[31] ==1) begin
            div_end = 32'h7FFFFFF & (~x_rs1 +1);
            div_or = 32'h7FFFFFF & (~x_rs2 + 1);
            x_out_o = quot;            
          end else if(x_rs1[31] == 1 && x_rs2[31] == 0) begin
            div_end = 32'h7FFFFFF & (~x_rs1 + 1);
            div_or = x_rs2;
            x_out_o = ~quot + 1;
          end else if(x_rs1[31] == 0 && x_rs2[31] ==1) begin
            div_end = x_rs1;
            div_or = 32'h7FFFFFF & (~x_rs2 + 1);
            x_out_o = ~quot + 1;
          end else if(x_rs1[31] == 0 && x_rs2[31] ==0) begin
            div_end = x_rs1;
            div_or = x_rs2;
            x_out_o = quot;
          end 
        end else if(insn_divu) begin
          if(check == 0) begin
            check_temp = 1;
          end else begin
            check_temp = 0;
          end

          div_end = x_rs1;
          div_or = x_rs2;
          x_out_o = quot;
        end else if(insn_rem) begin
          if(check == 0) begin
            check_temp = 1;
          end else begin
            check_temp = 0;
          end

          if(x_rs2 == 0) begin
            x_out_o = x_rs1;
          end else if(x_rs1 == 32'h80000000) begin
            x_out_o = 0;
          end else if(x_rs1[31] == 1 && x_rs2[31] ==1) begin
            div_end = 32'h7FFFFFF & (~x_rs1 + 1);
            div_or = 32'h7FFFFFF & (~x_rs2 + 1);
            x_out_o = ~rem + 1;            
          end else if(x_rs1[31] == 1 && x_rs2[31] == 0) begin
            div_end = 32'h7FFFFFF & (~x_rs1 +1);
            div_or = x_rs2;
            x_out_o = ~rem + 1;
          end else if(x_rs1[31] == 0 && x_rs2[31] ==1) begin
            div_end = x_rs1;
            div_or = 32'h7FFFFFF & (~x_rs2 + 1);
            x_out_o = rem;
          end else if(x_rs1[31] == 0 && x_rs2[31] == 0) begin
            div_end = x_rs1;
            div_or = x_rs2;
            x_out_o = rem;
          end 
        end else if(insn_remu) begin
          if(check == 0) begin
            check_temp = 1;
          end else begin
            check_temp = 0;
          end

          div_end = x_rs1;
          div_or = x_rs2;
          x_out_o =rem;
        end
      end  

      OpcodeMiscMem: begin
        if(insn_fence) begin

        end
      end

      OpcodeEnviron: begin

      end

      OpcodeBranch: begin
          if(insn_beq) begin 
            if(x_rs1 == x_rs2) begin
              pc_next = (x_pc_current + x_imm_b_sext) & ~3;
              f_rst = 1'b1;
              d_rst = 1'b1;
            end
          end else if(insn_bne) begin
            if(x_rs1 != x_rs2) begin
              pc_next = (x_pc_current + x_imm_b_sext) & ~3;
              f_rst = 1'b1;
              d_rst = 1'b1;
            end
          end else if(insn_blt) begin
            if($signed(x_rs1) < $signed(x_rs2)) begin
              pc_next = (x_pc_current + x_imm_b_sext) & ~3;
              f_rst = 1'b1;
              d_rst = 1'b1;
            end
          end else if(insn_bge) begin
            if($signed(x_rs1) >= $signed(x_rs2)) begin
              pc_next = (x_pc_current + x_imm_b_sext) & ~3;
              f_rst = 1'b1;
              d_rst = 1'b1;
            end
          end else if(insn_bltu) begin
            if(x_rs1 < x_rs2) begin
              pc_next = (x_pc_current + x_imm_b_sext) & ~3;
              f_rst = 1'b1;
              d_rst = 1'b1;
            end
          end else if(insn_bgeu) begin
            if(x_rs1 >= x_rs2) begin
              pc_next = (x_pc_current + x_imm_b_sext) & ~3;
              f_rst = 1'b1;
              d_rst = 1'b1;
            end
          end      
        end
      default: begin
        illegal_insn = 1'b1;
      end
  endcase
end


assign x_out_b = x_rs2;
assign x_rd = execute_state.rd;

  /****************/
  /* MEMORY STAGE */
  /****************/
  stage_memory_t memory_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      memory_state <= '{
        pc: 0,
        o: 0,
        b: 0,
        insn: 0,
        cycle_status: CYCLE_RESET,
        opcode: 0,
        rd: 0,
        w:0,
        rs1_addr: 0,
        rs2_addr: 0
      };
    end else begin
      begin
        memory_state <= '{
          pc: x_pc_current,
          o: x_out_o,
          b: x_out_b,
          insn: x_insn,
          cycle_status: x_cycle_status,
          opcode: x_opcode,
          rd: x_rd,
          w: x_we,
          rs1_addr: x_rs1_addr,
          rs2_addr: x_rs2_addr
        };
      end
    end
  end
  wire [255:0] m_disasm;
  Disasm #(
      .PREFIX("M")
  ) disasm_1memory (
      .insn  (memory_state.insn),
      .disasm(m_disasm)
  );

logic [`REG_SIZE] m_pc_current;
logic [`REG_SIZE] m_in_o;
logic [`REG_SIZE] m_in_b;
logic [`REG_SIZE] m_insn;
cycle_status_e m_cycle_status;
logic [`OPCODE_SIZE] m_opcode;
logic [4:0] m_rs1_addr, m_rs2_addr;

assign m_pc_current = memory_state.pc;
assign m_in_o = memory_state.o;
assign m_in_b = memory_state.b;
assign m_insn = memory_state.insn;
assign m_cycle_status = memory_state.cycle_status;
assign m_opcode = memory_state.opcode;
assign m_rs1_addr = memory_state.rs1_addr;
assign m_rs2_addr = memory_state.rs2_addr;

logic [`REG_SIZE] m_out_o;
logic [`REG_SIZE] m_out_d;
logic [4:0] m_rd;
logic m_we;

assign m_rd = memory_state.rd;
assign m_we = memory_state.w;
assign m_out_o = m_in_o;


//load logic      assign m_out_d = 



  /*******************/
  /* WRITEBACK STAGE */
  /*******************/
stage_writeback_t wb_state;
always_ff @(posedge clk) begin
  if (rst) begin
    wb_state <= '{
      pc: 0,
      o: 0,
      d: 0,
      insn: 0,
      cycle_status: CYCLE_RESET,
      opcode: 0,
      rd: 0,
      w: 0,
      rs1_addr: 0,
      rs2_addr: 0
    };
  end else begin
    begin
      wb_state <= '{
        pc: m_pc_current,
        o: m_out_o,
        d: m_out_d,
        insn: m_insn,
        cycle_status: m_cycle_status,
        opcode: m_opcode,
        rd: m_rd,
        w: m_we,
        rs1_addr: m_rs1_addr,
        rs2_addr: m_rs2_addr
      };
    end
  end
end
wire [255:0] w_disasm;
Disasm #(
    .PREFIX("W")
) disasm_1writeback (
    .insn  (wb_state.insn),
    .disasm(w_disasm)
);

logic [`REG_SIZE] w_pc_current;
assign w_pc_current = wb_state.pc;

logic [`REG_SIZE] w_in_o;
assign w_in_o = wb_state.o;

logic [`REG_SIZE] w_in_d;
assign w_in_d = wb_state.d;

logic [`REG_SIZE] w_out;

logic [`REG_SIZE] w_insn;
assign w_insn = wb_state.insn;

cycle_status_e wb_cycle_status;
assign wb_cycle_status = wb_state.cycle_status;


logic [`OPCODE_SIZE] wb_opcode;
assign wb_opcode = wb_state.opcode;

logic [4:0] w_rd;
assign w_rd = wb_state.rd;

logic w_we;
assign w_we = wb_state.w;

logic [4:0] w_rs1_addr, w_rs2_addr;
assign w_rs1_addr = wb_state.rs1_addr;
assign w_rs2_addr = wb_state.rs2_addr;

always_comb begin
  rd_data = 32'b0;
  rd_addr = 5'b0;
  w_en = w_we;
  w_out = 32'b0;
  halt = 1'b0;


  case(wb_opcode)
    OpcodeLui: begin
      w_out = w_in_o;
    end

    OpcodeAuipc: begin
      w_out = w_in_o;
    end

    OpcodeRegImm: begin
      w_out = w_in_o;
    end

    OpcodeRegReg: begin
      w_out = w_in_o;
    end

    OpcodeLoad: begin 
      w_out = w_in_d;
    end

    OpcodeEnviron: begin
      halt = 1'b1;
    end

    /*OpcodeJal: begin
    end

    OpcodeJalr: begin
    end*/

    default: begin
      rd_addr = 5'd0;
      rd_data = 32'd0;
    end      
  endcase
  rd_addr = w_rd;
  rd_data = w_out;
end


assign trace_writeback_pc =  w_pc_current;
assign trace_writeback_insn = w_insn;
assign trace_writeback_cycle_status = wb_cycle_status;

endmodule




























module MemorySingleCycle #(
    parameter int NUM_WORDS = 512
) (
    // rst for both imem and dmem
    input wire rst,

    // clock for both imem and dmem. The memory reads/writes on @(negedge clk)
    input wire clk,

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

  always @(negedge clk) begin
    if (rst) begin
    end else begin
      insn_from_imem <= mem[{pc_to_imem[AddrMsb:AddrLsb]}];
    end
  end

  always @(negedge clk) begin
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

/* This design has just one clock for both processor and memory. */
module RiscvProcessor (
    input  wire  clk,
    input  wire  rst,
    output logic halt,
    output wire [`REG_SIZE] trace_writeback_pc,
    output wire [`INSN_SIZE] trace_writeback_insn,
    output cycle_status_e trace_writeback_cycle_status
);

  wire [`INSN_SIZE] insn_from_imem;
  wire [`REG_SIZE] pc_to_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;

  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) the_mem (
      .rst                (rst),
      .clk                (clk),
      // imem is read-only
      .pc_to_imem         (pc_to_imem),
      .insn_from_imem     (insn_from_imem),
      // dmem is read-write
      .addr_to_dmem       (mem_data_addr),
      .load_data_from_dmem(mem_data_loaded_value),
      .store_data_to_dmem (mem_data_to_write),
      .store_we_to_dmem   (mem_data_we)
  );

  DatapathPipelined datapath (
      .clk(clk),
      .rst(rst),
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      .addr_to_dmem(mem_data_addr),
      .store_data_to_dmem(mem_data_to_write),
      .store_we_to_dmem(mem_data_we),
      .load_data_from_dmem(mem_data_loaded_value),
      .halt(halt),
      .trace_writeback_pc(trace_writeback_pc),
      .trace_writeback_insn(trace_writeback_insn),
      .trace_writeback_cycle_status(trace_writeback_cycle_status)
  );

endmodule
