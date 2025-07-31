# RISC_5_PROCESSOR

![1](https://github.com/user-attachments/assets/cca0d359-4075-41c6-9ac5-ecc449283aed)

# OBJECTIVE


To design, implement, and verify a simple 32-bit RISC-V processor core based on the RV32I instruction set architecture (ISA) using Verilog HDL, and simulate it using Xilinx Vivado for verification.


# PROJECT OVERVIEW

This project involves building a modular RISC-V processor from scratch. The processor executes basic instructions like arithmetic, logical, memory access, and control flow operations. It is based on the RV32I base integer instruction set, suitable for embedded systems.

# RISC_5_PROCESSOR ARCHITECTURE
<img width="475" height="358" alt="2" src="https://github.com/user-attachments/assets/ba7600e1-9b2f-4ed3-9510-8eba0907f7a1" />



# MAIN MODULES IN THE DESIGN 


1. # Instruction Fetch Unit (IFU)*

   * Fetches instructions from instruction memory based on the Program Counter (PC).

2. # Instruction Decode Unit (IDU)*

   * Decodes fetched instructions.
   * Extracts opcode, registers, and immediate values.

3. # Register File*

   * 32 general-purpose 32-bit registers.
   * Supports read and write operations.

4. # ALU (Arithmetic Logic Unit)*

   * Performs arithmetic (add, sub) and logic (and, or, xor) operations.
   * ALU control is based on funct3/funct7 fields.

5. # Control Unit*

   * Generates control signals based on the opcode.
   * Controls MUXes, memory access, and ALU operation.

6. # Immediate Generator*

   * Generates signed immediate values from instruction formats (I, S, B, U, J).

7. # Data Memory*

   * 32-bit memory for load/store instructions.
   * Supports byte/half/word operations.

8. # Program Counter (PC)*

   * Keeps track of the current instruction address.
   * Updated on branch, jump, or sequential execution.
  



# verilog code for RISC 5 PROCESSOR

// Module PC
module pc(input clk, input reset, input [31:0] next_pc, output reg [31:0] pc_out);
  always @(posedge clk or posedge reset) begin
    if (reset)
      pc_out <= 0;
    else
      pc_out <= next_pc;
  end
endmodule


// Module Instruction Memory

module instr_mem(input [31:0] addr, output [31:0] instr);
  reg [31:0] mem [0:255];
  initial $readmemh("instructions.mem", mem); // Load instructions

  assign instr = mem[addr[9:2]]; // Word-aligned access
endmodule



// Module Register File

module register_file(input clk, input reg_write,
                     input [4:0] rs1, rs2, rd,
                     input [31:0] write_data,
                     output [31:0] read_data1, read_data2);

  reg [31:0] regs[0:31];

  assign read_data1 = regs[rs1];
  assign read_data2 = regs[rs2];

  always @(posedge clk)
    if (reg_write && rd != 0)
      regs[rd] <= write_data;
endmodule


// Module ALU

module alu(input [31:0] a, b,
           input [3:0] alu_ctrl,
           output reg [31:0] result);

  always @(*) begin
    case (alu_ctrl)
      4'b0000: result = a + b;
      4'b0001: result = a - b;
      4'b0010: result = a & b;
      4'b0011: result = a | b;
      default: result = 0;
    endcase
  end
endmodule

// Module Data Memory
module data_mem(input clk,
                input [31:0] addr,
                input [31:0] write_data,
                input mem_write, mem_read,
                output reg [31:0] read_data);

  reg [31:0] mem [0:255];

  always @(posedge clk)
    if (mem_write)
      mem[addr[9:2]] <= write_data;

  always @(*)
    if (mem_read)
      read_data = mem[addr[9:2]];
    else
      read_data = 0;
endmodule


// Module Control Unit

module control_unit(input [6:0] opcode,
                    output reg reg_write, alu_src,
                    output reg mem_to_reg, mem_read, mem_write);

  always @(*) begin
    case (opcode)
      7'b0110011: begin // R-type
        reg_write = 1; alu_src = 0;
        mem_to_reg = 0; mem_read = 0; mem_write = 0;
      end
      7'b0000011: begin // lw
        reg_write = 1; alu_src = 1;
        mem_to_reg = 1; mem_read = 1; mem_write = 0;
      end
      7'b0100011: begin // sw
        reg_write = 0; alu_src = 1;
        mem_to_reg = 0; mem_read = 0; mem_write = 1;
      end
      default: begin
        reg_write = 0; alu_src = 0;
        mem_to_reg = 0; mem_read = 0; mem_write = 0;
      end
    endcase
  end
endmodule


// Top Module
module top_module(input clk, input reset);
  wire [31:0] pc_out, next_pc, instruction;
  wire [4:0] rs1, rs2, rd;
  wire [6:0] opcode;
  wire [31:0] read_data1, read_data2, alu_result, mem_data;
  wire reg_write, alu_src, mem_to_reg, mem_read, mem_write;

  assign opcode = instruction[6:0];
  assign rs1 = instruction[19:15];
  assign rs2 = instruction[24:20];
  assign rd = instruction[11:7];

  wire [31:0] alu_in2 = alu_src ? instruction[31:20] : read_data2;

  pc PC(clk, reset, next_pc, pc_out);
  instr_mem IM(pc_out, instruction);
  register_file RF(clk, reg_write, rs1, rs2, rd,
                   mem_to_reg ? mem_data : alu_result,
                   read_data1, read_data2);
  alu ALU(read_data1, alu_in2, 4'b0000, alu_result);
  data_mem DM(clk, alu_result, read_data2, mem_write, mem_read, mem_data);
  control_unit CU(opcode, reg_write, alu_src, mem_to_reg, mem_read, mem_write);

  assign next_pc = pc_out + 4;
endmodule




///testbench For Risc 5 Processor (system verilog)


`timescale 1ns/1ps

module tb_top_module;
  logic clk = 0;
  logic reset;

  // DUT instance
  top_module dut(.clk(clk), .reset(reset));

  // Clock generator
  always #5 clk = ~clk;

  // Simulation
  initial begin
    $display("Running RISC-V Testbench...");
    reset = 1;
    #20 reset = 0;

    #200 $finish;
  end
endmodule


// UVM CODE For Risc 5 Processor ( UVM verification )

class my_riscv_test extends uvm_test;
    `uvm_component_utils(my_riscv_test)
    riscv_env env;

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env = riscv_env::type_id::create("env", this);
    endfunction

    task run_phase(uvm_phase phase);
        // issue stimulus and check response
        // e.g. reset, instruction fetch, etc.
    endtask
endclass

