// riscvsingle.sv

// RISC-V single-cycle processor
// From Section 7.6 of Digital Design & Computer Architecture
// 27 April 2020
// David_Harris@hmc.edu 
// Sarah.Harris@unlv.edu

// run 210
// Expect simulator to print "Simulation succeeded"
// when the value 25 (0x19) is written to address 100 (0x64)

//   Instruction  opcode    funct3    funct7
//   add          0110011   000       0000000
//   sub          0110011   000       0100000
//   and          0110011   111       0000000
//   or           0110011   110       0000000
//   slt          0110011   010       0000000
//   addi         0010011   000       immediate
//   andi         0010011   111       immediate
//   ori          0010011   110       immediate
//   slti         0010011   010       immediate
//   beq          1100011   000       immediate
//   lw	          0000011   010       immediate
//   sw           0100011   010       immediate
//   jal          1101111   immediate immediate

module riscvsingle (input  logic        clk, reset,
		    output logic [31:0] PC,
		    input logic [31:0] 	Instr,
		    output logic 	MemWrite,
		    output logic [31:0] ALUResult, WriteData,
		    input logic [31:0] 	ReadData,
		    input logic 	PCReady,
		    output logic 	MemStrobe);
   
   logic 				ALUSrc, PCTargetSrc, RegWrite, Jump, Zero, res31, carry;
   logic [2:0] 				ResultSrc;
   logic [2:0] 				ImmSrc; 
   logic [3:0]        ALUControl;
   
   controller c (Instr[6:0], Instr[14:12], Instr[30], Zero, res31, carry,
		 ResultSrc, MemWrite, PCSrc,
		 ALUSrc, PCTargetSrc, RegWrite, Jump,
		 ImmSrc, ALUControl, MemStrobe);
   datapath dp (clk, reset, ResultSrc, PCSrc,
		ALUSrc, PCTargetSrc, RegWrite,
		ImmSrc, ALUControl,
		Zero, res31, carry, PC, Instr,
		ALUResult, WriteData, ReadData, PCReady);
   
endmodule // riscvsingle

module controller (input  logic [6:0] op,
		   input logic [2:0]  funct3,
		   input logic 	      funct7b5,
		   input logic 	      Zero, res31, carry,
		   output logic [2:0] ResultSrc,
		   output logic       MemWrite,
		   output logic       PCSrc, ALUSrc, PCTargetSrc,
		   output logic       RegWrite, Jump,
		   output logic [2:0] ImmSrc,
		   output logic [3:0] ALUControl,
		   output logic       MemStrobe);
   
   logic [1:0] 			      ALUOp;
   logic 			      Branch;
   
   maindec md (op, ResultSrc, MemWrite, Branch,
	       ALUSrc, PCTargetSrc, RegWrite, Jump, ImmSrc, ALUOp, MemStrobe);
   aludec ad (op[5], funct3, funct7b5, ALUOp, ALUControl);

  logic BranchControl;
  /*
  always_comb
    case(funct3)
      3'b000: assign BranchControl = Zero; // beq
      3'b001: assign BranchControl = ~Zero; // bne
      3'b100: assign BranchControl = res31; //blt
      3'b101: assign BranchControl = (~res31 | Zero); // bge
      3'b110: assign BranchControl = ~carry; // bltu
      3'b111: assign BranchControl = carry; // bgeu
      default: assign BranchControl = 1'b0;
    endcase // case (funct3)
   */
   assign BranchControl = (Zero & ~funct3[0]&~funct3[1]&~funct3[2]) |
			  (~Zero & funct3[0]&funct3[1]&funct3[2]) |
			  (res31 & ~funct3[0]&~funct3[1]&funct3[2]) |
			  ((~res31 | Zero) & funct3[0]&~funct3[1]&funct3[2]) |
			  (~carry & ~funct3[0]&funct3[1]&funct3[2]) |
			  (carry & funct3[0]&funct3[1]&funct3[2]);   

   assign PCSrc = Branch & BranchControl | Jump;
   
endmodule // controller

module maindec (input  logic [6:0] op,
		output logic [2:0] ResultSrc,
		output logic 	   MemWrite,
		output logic 	   Branch, ALUSrc, PCTargetSrc,
		output logic 	   RegWrite, Jump,
		output logic [2:0] ImmSrc,
		output logic [1:0] ALUOp,
		output logic 	   MemStrobe);
   
   logic [14:0] 		   controls;
   
   assign {RegWrite, ImmSrc, ALUSrc, MemWrite,
	   ResultSrc, Branch, ALUOp, Jump, PCTargetSrc, MemStrobe} = controls;
   
   always_comb
     case(op)
       // RegWrite_ImmSrc_ALUSrc_MemWrite_ResultSrc_Branch_ALUOp_Jump_PCTargetSrc_MemStrobe
       7'b0000011: controls = 15'b1_000_1_0_001_0_00_0_0_1; // lw
       7'b0100011: controls = 15'b0_001_1_1_xxx_0_00_0_0_1; // sw
       7'b0110011: controls = 15'b1_xxx_0_0_000_0_10_0_0_0; // R–type
       7'b1100011: controls = 15'b0_010_0_0_xxx_1_01_0_0_0; // beq
       7'b0010011: controls = 15'b1_000_1_0_000_0_10_0_x_0; // I–type ALU
       7'b1101111: controls = 15'b1_011_0_0_010_0_xx_1_0_0; // jal
       7'b0110111: controls = 15'b1_100_x_0_011_0_xx_0_0_0; // lui
       7'b1100111: controls = 15'b1_000_1_0_010_0_xx_1_1_0; // jalr
       7'b0010111: controls = 15'b1_100_x_0_100_0_xx_0_0_0; // auipc
       default: controls = 15'bx_xxx_x_x_xxx_x_xx_x_x_x; // ???
     endcase // case (op)
   
endmodule // maindec

module aludec (input  logic       opb5,
	       input  logic [2:0] funct3,
	       input  logic 	  funct7b5,
	       input  logic [1:0] ALUOp,
	       output logic [3:0] ALUControl);
   
   logic 			  RtypeSub;
   
   assign RtypeSub = funct7b5 & opb5; // TRUE for R–type subtract
   always_comb
     case(ALUOp)
      2'b00: case(funct3)
        3'b010: ALUControl = 4'b0000; // addition
        /*3'b001: ALUControl = 4'b1010; // lh, sh
        3'b000: ALUControl = 4'b1011; // lb, sb
        3'b100: ALUControl = 4'b1100; // lbu
        3'b101: ALUControl = 4'b1101; // lhu */
        default: ALUControl = 4'b0000;
      endcase
      2'b01: ALUControl = 4'b0001; // subtraction
       default: case(funct3) // R–type or I–type ALU
		  3'b000: if (RtypeSub)
		    ALUControl = 4'b0001; // sub
		  else
		    ALUControl = 4'b0000; // add, addi
		  3'b010: ALUControl = 4'b0101; // slt, slti
		  3'b110: ALUControl = 4'b0011; // or, ori
		  3'b111: ALUControl = 4'b0010; // and, andi
		  3'b100: ALUControl = 4'b0100; // xor, xori	
      3'b101: if (funct7b5)
        ALUControl = 4'b0110; // sra, srai
      else
        ALUControl = 4'b0111; // srl, srli
      3'b001: ALUControl = 4'b1000; // sll, slli
      3'b011: ALUControl = 4'b1001; // sltu, sltiu	  
		  default: ALUControl = 4'bxxxx; // ???
		endcase // case (funct3)       
     endcase // case (ALUOp)
   
endmodule // aludec

module datapath (input  logic        clk, reset,
		 input  logic [2:0]  ResultSrc,
		 input  logic 	     PCSrc, ALUSrc, PCTargetSrc,
		 input  logic 	     RegWrite,
		 input  logic [2:0]  ImmSrc,
		 input  logic [3:0]  ALUControl,
		 output logic 	     Zero, res31, carry,
		 output logic [31:0] PC,
		 input  logic [31:0] Instr,
		 output logic [31:0] ALUResult, WriteData,
		 input  logic [31:0] ReadData,
		 input logic         PCReady);
   
   logic [31:0] 		     PCNext, PCPlus4;
   logic [31:0]          PCTarget, PCTargetNew;
   logic [31:0] 		     ImmExt;
   logic [31:0] 		     SrcA, SrcB;
   logic [31:0] 		     Result;
   
   // next PC logic
   flopenr #(32) pcreg (clk, reset, PCReady, PCNext, PC);
   adder  pcadd4 (PC, 32'd4, PCPlus4);
   adder  pcaddbranch (PC, ImmExt, PCTarget);
   mux2 #(32)  pcmux (PCPlus4, PCTargetNew, PCSrc, PCNext);
   // register file logic
   regfile  rf (clk, RegWrite, Instr[19:15], Instr[24:20],
	       Instr[11:7], Result, SrcA, WriteData);
   extend  ext (Instr[31:7], ImmSrc, ImmExt);
   // ALU logic
   mux2 #(32)  srcbmux (WriteData, ImmExt, ALUSrc, SrcB);
   alu  alu (SrcA, SrcB, ALUControl, ALUResult, Zero, res31, carry);
   mux2 #(32) jalrmux (PCTarget, ALUResult, PCTargetSrc, PCTargetNew);
   mux5 #(32) resultmux (ALUResult, ReadData, PCPlus4, ImmExt, PCTargetNew, ResultSrc, Result);

endmodule // datapath

module adder (input  logic [31:0] a, b,
	      output logic [31:0] y);
   
   assign y = a + b;
   
endmodule

module extend (input  logic [31:7] instr,
	       input  logic [2:0]  immsrc,
	       output logic [31:0] immext);
   
   always_comb
     case(immsrc)
       // I−type
       3'b000:  immext = {{20{instr[31]}}, instr[31:20]};
       // S−type (stores)
       3'b001:  immext = {{20{instr[31]}}, instr[31:25], instr[11:7]};
       // B−type (branches)
       3'b010:  immext = {{20{instr[31]}}, instr[7], instr[30:25], instr[11:8], 1'b0};       
       // J−type (jal)
       3'b011:  immext = {{12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0};
	     // U-type (lui)
	     3'b100: immext = {instr[31:12], 12'b0};
       default: immext = 32'bx; // undefined
     endcase // case (immsrc)
   
endmodule // extend

module flopr #(parameter WIDTH = 8)
   (input  logic             clk, reset,
    input logic [WIDTH-1:0]  d,
    output logic [WIDTH-1:0] q);
   
   always_ff @(posedge clk, posedge reset)
     if (reset) q <= 0;
     else  q <= d;
   
endmodule // flopr

module flopenr #(parameter WIDTH = 8)
   (input  logic             clk, reset, en,
    input logic [WIDTH-1:0]  d,
    output logic [WIDTH-1:0] q);

   always_ff @(posedge clk, posedge reset)
     if (reset)  q <= 0;
     else if (en) q <= d;
   
endmodule // flopenr

module mux2 #(parameter WIDTH = 8)
   (input  logic [WIDTH-1:0] d0, d1,
    input logic 	     s,
    output logic [WIDTH-1:0] y);
   
  assign y = s ? d1 : d0;
   
endmodule // mux2

module mux3 #(parameter WIDTH = 8)
   (input  logic [WIDTH-1:0] d0, d1, d2,
    input logic [1:0] 	     s,
    output logic [WIDTH-1:0] y);
   
  assign y = s[1] ? d2 : (s[0] ? d1 : d0);
   
endmodule // mux3

module mux4 #(parameter WIDTH = 8) 
    (input logic [WIDTH-1:0] d0, d1, d2, d3,
     input logic [1:0] s,
     output logic [WIDTH-1:0] y);

  assign y = s[1] ? (s[0] ? d3 : d2) : (s[0] ? d1 : d0);

endmodule // mux4

module mux5 #(parameter WIDTH = 12) 
    (input logic [WIDTH-1:0] d0, d1, d2, d3, d4,
     input logic [2:0] s,
     output logic [WIDTH-1:0] y);

  assign y = s[2] ? d4 : (s[1] ? (s[0] ? d3 : d2) : (s[0] ? d1 : d0));

endmodule // mux5

module alu (input  logic [31:0] a, b,
            input  logic [3:0] 	alucontrol,
            output logic [31:0] result,
            output logic 	zero, res31, carry);

   logic [31:0] 	       condinvb, sum;
   logic 		       v;              // overflow
   logic 		       isAddSub;       // true when is add or subtract operation

   assign condinvb = alucontrol[0] ? ~b : b;
   assign sum = a + condinvb + alucontrol[0];
   assign isAddSub = ~alucontrol[2] & ~alucontrol[1] |
                     ~alucontrol[1] & alucontrol[0];   

   always_comb
     case (alucontrol)
       4'b0000:  result = sum;                   // add
       4'b0001:  result = sum;                   // subtract
       4'b0010:  result = a & b;                 // and
       4'b0011:  result = a | b;                 // or       
       4'b0100:  result = a ^ b;                 // xor
       4'b0101:  result = sum[31] ^ v;           // slt
       4'b0110:  result = $signed(a) >>> b[4:0]; // sra
       4'b0111:  result = a >> b[4:0];           // srl
       4'b1000:  result = a << b[4:0];           // sll
       4'b1001:  result = {31'b0,(a < b)};       // sltu
       /*4'b1010:  result = sum[15:0];
       4'b1011:  result = sum[7:0];
       4'b1100:  result = {16'b0, sum[15:0]};
       4'b1101:  result = {24'b0, sum[7:0]};*/
       default: result = 32'bx;
     endcase

   assign carry = ~(a < b);
   assign res31 = result[31];
   assign zero = (result == 32'b0);
   assign v = ~(alucontrol[0] ^ a[31] ^ b[31]) & (a[31] ^ sum[31]) & isAddSub;
   
endmodule // alu

module regfile (input  logic        clk, 
		input  logic 	    we3, 
		input  logic [4:0]  a1, a2, a3, 
		input  logic [31:0] wd3, 
		output logic [31:0] rd1, rd2);

   logic [31:0] 		    rf[31:0];

   // three ported register file
   // read two ports combinationally (A1/RD1, A2/RD2)
   // write third port on rising edge of clock (A3/WD3/WE3)
   // register 0 hardwired to 0

   always_ff @(posedge clk)
     if (we3) rf[a3] <= wd3;	

   assign rd1 = (a1 != 0) ? rf[a1] : 0;
   assign rd2 = (a2 != 0) ? rf[a2] : 0;
   
endmodule // regfile
