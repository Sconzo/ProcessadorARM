///////////////////////////////			MULTIPLEXADOR	
module mux2  (ent0,ent1,sel,saida);
	
	input [31:0]ent0,ent1;
	input sel;
	output [31:0]saida;
	
	assign saida = (sel==1) ? ent1 : ent0;
endmodule	

/////////////////////// 						 FLIP FLOP COM RESET

module ffres (clk,reset,d,q);
					
	input clk, reset;
	input [31:0]d;
	output reg[31:0]q;
	
	always @(posedge clk, posedge reset)
		
		if (reset)
			q<=0;
		else
			q<=d;
endmodule

////////////////////////					SOMADOR

module somador (ent0,ent1,saida);
					 
	input [31:0]ent0;
	input [31:0]ent1;
	output [31:0]saida;
	
	assign saida = ent0 + ent1;
	
endmodule

//////////////////////////					SHIFTER
module shift(srcB,rd2,sh,shamt5);
	
	input  [1:0]sh;
	input   signed [31:0] rd2;
	output reg signed[31:0] srcB; 
	input [4:0]shamt5;
	
	always@(posedge rd2 or posedge shamt5 or posedge sh) begin  
					case (sh)						
						2'b00:begin		//LSL
							srcB = rd2<<shamt5;
								end			
						2'b01:begin		//LSR
							srcB = rd2>>shamt5;
								end	
						2'b10:begin		//ASR
							srcB = rd2>>>shamt5;
								end 
						2'b11:begin		// ROR
							reg [63:0] temp;
							temp = {rd2,rd2}>>shamt5;
							srcB = temp[31:0];
								end
					endcase					        
				end
endmodule

/////////////////////////////////////////////////////      


module ALU(ALUcontrol,ALUflags,srcA,srcB,ALUresult,sh,shamt5,I);
	
	input  [1:0]sh;
	input  [3:0]ALUcontrol;
	input  I;
	output reg[3:0]ALUflags;
	input   signed [31:0] srcA, srcB;
	output reg signed[31:0] ALUresult; 
	input [4:0]shamt5;
	always@(posedge ALUcontrol or posedge srcA or posedge srcB) begin   // srcA e srcB soh para testar
		case (ALUcontrol)
			4'b0000: begin								// ADD
							ALUresult = srcA+srcB;
					 end				 
			4'b0001: begin								//SUB
							ALUresult = srcA-srcB;
					 end
			4'b0010: begin								//AND
							ALUresult = srcA&srcB;
					 end
			4'b0011: begin								//ORR
							ALUresult = srcA|srcB;
					 end
			4'b0100: begin	
							if (I == 1 || (sh == 0 && shamt5 == 0))	// MOV
								ALUresult = srcB;       
							else begin
									case (sh)						
										2'b00:begin				//LSL
											ALUresult = srcB<<shamt5;
												end					
										2'b01:begin				//LSR
											ALUresult = srcB>>shamt5;
												end					
										2'b10:begin				//ASR
											ALUresult = srcB>>>shamt5;
												end					
										2'b11:begin				//ROR 
											reg [63:0] temp;
											temp = {srcB,srcB}>>shamt5;
											ALUresult = temp[31:0];
												end
									endcase					        
								end
						end					 
			4'b0101: begin
							if (srcA - srcB == 0) begin		// CMP ====
								ALUflags = 4'b0100;
								ALUresult = 4'bxxxx;
							end
							else if (srcA - srcB > 0) begin		// a>>>>>
								ALUflags = 4'b0010;
								ALUresult = 4'bxxxx;
							end
							else if (srcA - srcB < 0) begin		// b>>>>>
								ALUflags = 4'b1010;
								ALUresult = 4'bxxxx;
							end
					 end
			4'b0110: begin
							if (srcA - srcB == 0) begin		// TEQ
								ALUflags = 4'b0100;     // 
							end
							else begin
								ALUflags = 4'b1000;
							end
						//ALUresult = 4'bxxxx;
					 end		
			4'b0111: begin										// XOR
							ALUresult = srcA^srcB;
					 end
			4'b1000: begin								// NOT
							ALUresult = ~srcB;      
					end
			default : ALUresult = 0;			
		endcase
	end
endmodule


/////////////////////////////////////// 			EXTENSOR
module Extend(Imm,Immext,rot,Immsrc);
	
	input [1:0]Immsrc;
	input [3:0]rot;
	input [23:0]Imm;
	output reg [31:0]Immext;
	reg [63:0]temp;
	reg [31:0]aux;
	always@(*) begin
		temp = 32'b00;
		aux  = 32'b00;
		case (Immsrc) 
			2'b00: begin
					aux = {24'b0,Imm[7:0]};
					temp = {aux,aux};
					if (rot != 4'b0000) 
					temp = {aux,aux}>>rot*2;
					Immext = temp[31:0];
					end
			2'b01:
					Immext = {20'b0,Imm[11:0]};
			2'b10:begin
					if (Imm[23] == 0)
					Immext = {6'b000000,Imm,2'b00};
					else
					Immext = {6'b111111,Imm,2'b00};
					end
			default: Immext = 32'b0;
		endcase
		end
endmodule

////////////////////////////////				BANCO DE REGISTRADORES


module BancoRegistradores (ra1,ra2,wa3,wd3,clk,we3,rd1,rd2);
	input [3:0]ra1,ra2,wa3;
	input [31:0]wd3;
	input clk,we3;
	output [31:0]rd1,rd2;
	
	reg [31:0] regs[14:0];
	
	always@(posedge clk)begin
		if (we3) regs[wa3]<=wd3;			//Sequencial
   end
		
	assign rd1 = regs[ra1];	//Combinacional
	assign rd2 = regs[ra2]; 	//assign rd2 = (ra2==4'b1111)?r15:regs[ra2]; 


endmodule 


/////////////////////////////////////////



//////////////////////////////////////

//////////////////////////////////////		MEMÓRIA DE DADOS


module MemDados(clk,MemWrite,DataAdr,WriteData,ReadData);  //HIBRIDAS
	input clk,MemWrite;
	input [31:0]DataAdr,WriteData;
	output [31:0]ReadData;
	
	reg [31:0] MEM [31:0];  // 31 é o suficiente? ou é demais?
	
	always @ (posedge clk) begin   
		if (MemWrite) MEM[DataAdr] = WriteData;
		
	end
	
	assign ReadData = MEM[DataAdr];            
	
endmodule


/////////////////////////////////////     MEMÓRIA DE INSTRUÇÕES

module MemInstr  (clk,PC,Instr);		// HIBRIDAS
	input clk;
	input [31:0]PC;
	output [31:0]Instr;
	
	reg [31:0] mem [21:0];
	integer controle =0;
	
	always @ (posedge clk) begin
		if (controle ==0) begin
		
		mem[1]	= 32'b10010010100000000111011000000001;									//mov							mem  [1] = 32'b10010010100000000011000000000000;									//mem [1]  = 32'b10010010100000000111000000010100;	// MOV
		mem[2]	= 32'b10010100000000000111000000000100;														//str							mem  [2] = 32'b10010010100000000000000000000011;									//mem [2]  = 32'b10010010100000001000000000001111;	// MOV
		mem[3]	= 32'b10010100000100001000000000000100;														//ldr							mem  [3] = 32'b10010010100000000001000000000001;									//mem [3]  = 32'b10010000000010001001000000000111;	// ADD
		mem[4]	= 32'b10010000110101110000000000001000	;													//teq							mem  [4] = 32'b10010010100000000010000000000001;									//mem [4]  = 32'b10010100000000001001000000000100;	// STR
		mem[5]	= 32'b00001010000000000000000000000001	;													//bleq						mem  [5] = 32'b10010010100000000100000000010100;									//mem [5]  = 32'b10011010000000000000000000000001;   // BL 1 + PC + 2 = 8 
		mem[6]	= 32'b10010010100000000001000101000001	;													//asr							
		
		mem[8]	= 32'b10010010100000000000000000000100	;													//mov							mem  [6] = 32'b10010000110001000000000000000000;									//mem [6]  = 32'b10011000000000000000000000000101;   // B  5 + PC + 2 = 13
		mem[9]	= 32'b10010010100000000001000000010000		;												//mov							mem  [7] = 32'b00001000000000000000000000000100;									//mem [8]  = 32'b10010100000100000010000000000100;	// LDR
		mem[10]	= 32'b10010010100000000010000000000010	;													//mov						mem  [8] = 32'b10010000000000010011000000000010;									//mem [9]  = 32'b10010010001000100011000000001010;	// SUB
		mem[11]	= 32'b10010000101000000000000000000001		;												//cmp							mem  [9] = 32'b10010000100000000001000000000010;									//mem [10] = 32'b10010000100000001111000000001110;   // MOV PC,LR 
		mem[12]	= 32'b00000000001000000011000000000001	;												//subeq							mem [10] = 32'b10010000100000000010000000000011;									//mem [13] = 32'b10010100000000000011000000001000;   // STR 
		mem[13]	= 32'b10000000001000000011000000000001	;													//subgt							mem [11] = 32'b10010010000000000000000000000001;
		mem[14]	= 32'b00010000001000000011000000000001	;													//subne							mem [12] = 32'b10011001111111111111111111111000;
		mem[15]	= 32'b10010000100000000000000010000000	;													//lsl							
		mem[16]	= 32'b10010000101100000000000000000001	;													//cmp	
		mem[17]	= 32'b00000000001000000011000000000001	;													//subeq							mem [13] = 32'b10010100000000000011000000000000;
		mem[18]	= 32'b10010000001100100100000000000001	;													//subs	
		mem[19]	= 32'b00100010000001000100000000001010	;													//addpl
		mem[20]	= 32'b00110010000001000100000000001010	;													//addmi
		mem[21]	= 32'b10010000100000001111000000001110;														//mov PC lR			
		
		controle <= 1;
		end
	end
	assign Instr = mem[PC/4];
	 
endmodule

/////////////////////////////  WAVEFORM 26 SEM MEM INSTR
/////////////////////////////  WAVEFORM 27 COM MEM INSTR
/////////////////////////////  WAVEFORM 28 COM MEM INSTR em ordem diferente

module datapath (A3aux,WD3aux,srcBaux,srcAaux,Resultaux,clk,reset,RegWrite,ALUsrc,MemtoReg,PCsrc,ReadData,Instr,Regsrc,Immsrc,ALUcontrol,ALUflags,PC,ALUresult,WriteData);

	input clk, reset;
	input RegWrite;
	input ALUsrc;
	input MemtoReg;
	input PCsrc;
	input [3:0]Regsrc;
	input [1:0]Immsrc;
	input [3:0]ALUcontrol;
	input [31:0]Instr;
	input [31:0]ReadData;
	output [3:0]ALUflags;
	output [31:0]PC;
	output [31:0]ALUresult;
	output [31:0]WriteData;
	output [31:0]A3aux,WD3aux,srcBaux,srcAaux,Resultaux;
	wire [31:0]PCprox, PC4, PC8;
	wire [31:0]Immext, srcA, srcB, Result,RD1;
	wire [3:0] A2, A3;
	wire [31:0] WDsh, WD3;
	
	
	//MemInstr mi(.clk(clk),.PC(PC),.Instr(Instr)); 
	
	mux2 pcmux(.ent0(PC4),.ent1(Result),.sel(PCsrc),.saida(PCprox));     //PC
	ffres regpc(.clk(clk),.reset(reset),.d(PCprox),.q(PC));
	somador add4(.ent0(PC), .ent1(32'b100), .saida(PC4));
	somador add8(.ent0(PC4), .ent1(32'b100), .saida(PC8));
	
	mux2 a2mux (.ent0(Instr[3:0]), .ent1(Instr[15:12]), .sel(Regsrc[2]), .saida(A2));    //Src Banco de REgistrador
	mux2 a3mux (.ent0(Instr[15:12]), .ent1(4'b1110), .sel(Regsrc[1]), .saida(A3));
	mux2 wd3mux(.ent0(Result), .ent1(PC4), .sel(Regsrc[0]), .saida(WD3));
	
	BancoRegistradores b(.ra1(Instr[19:16]),.ra2(A2),.wa3(A3),.wd3(WD3),.clk(clk),.we3(RegWrite),.rd1(RD1),.rd2(WriteData)); 
	
	Extend (.Imm(Instr[23:0]),.Immext(Immext),.rot(Instr[11:8]),.Immsrc(Immsrc));
	
	shift sh(.srcB(WDsh),.rd2(WriteData),.shamt5(Instr[11:7]),.sh(Instr[6:5]));

	mux2 srcAmux (.ent0(RD1), .ent1(PC8), .sel(Regsrc[3]), .saida(srcA)); 	// src ULA
	mux2 srcBmux(.ent0(WDsh), .ent1(Immext), .sel(ALUsrc), .saida(srcB));
	
	ALU alu(.ALUcontrol(ALUcontrol),.ALUflags(ALUflags),.srcA(srcA),.srcB(srcB),.ALUresult(ALUresult),.sh(Instr[6:5]),.shamt5(Instr[11:7]),.I(Instr[25]));

	//MemDados md(.clk(clk), .MemWrite(~Instr[20]),.DataAdr(ALUresult),.WriteData(WriteData),.ReadData(ReadData));
	
	mux2 toreg(.ent0(ALUresult), .ent1(ReadData), .sel(MemtoReg), .saida(Result));    // Retorno da Instrucao
	

	
endmodule






// unidade de controle

module decoder(OP,Funct,Rd,FlagW,PCS,RegW,MemW,MemtoReg,ALUsrc,Immsrc,ALUcontrol,Regsrc,Nowrite/*,Baux,ALUOPaux*/);

					
input [1:0]OP;
input [5:0]Funct;
input [3:0]Rd;
output reg [1:0]FlagW;  // [1]N,Z [0]C,V
output PCS,RegW,MemW,MemtoReg,ALUsrc;
output reg Nowrite;
output [1:0]Immsrc;
output reg[3:0]ALUcontrol;
output [3:0]Regsrc;
					
//output Baux,ALUOPaux;
					
					
wire Branch, ALUop;
reg [11:0]controls;
reg cod11;


// Decodificador
	always@* 
		
		case (OP)
		
			2'b00: if (Funct[5] == 1) 
						controls = 12'b000100100001; // PD Imm b00010010x001
					 else
						controls = 12'b000000100001; // PD Reg	b0000xx100001
			
			2'b01: if (Funct[0] == 1)
						controls = 12'b010101100000; // LDR Imm b01010110x000
					 else 
						controls = 12'b001101001000; // STR Imm b0x1101001xx0
					
			2'b10: if (Funct[5] == 1)
						controls = 12'b100110110110; //BL b10011011x110
					 else
						controls = 12'b100110010000; //B b10011001xxx0
			
			2'b11: cod11 = 1;
			
			default: controls = 12'b0;
		
		endcase
		
		
		assign {B,MemtoReg,MemW,ALUsrc,Immsrc,RegW,Regsrc,ALUop} = controls;
		
		//assign Baux = B;
		//assign ALUOPaux = ALUop;
	
// Decoder da ALU 
		always@*
		
			if (ALUop == 0) begin // Não PD				
				ALUcontrol = 4'b0000;
				FlagW = 2'b00;
				Nowrite = 0;
			end
			
			else if (ALUop == 1) begin	// Se for PD
					
				ALUcontrol = Funct[4:1];
				Nowrite = 0;
				
				//update das flags
				
				if (Funct[0] == 1) begin   //Depende de S
					
					if ((Funct[4:1] == 4'b0000) || (Funct[4:1] == 4'b0001) || (Funct[4:1] == 4'b0100))
						FlagW = 2'b11;
						
					else 
						FlagW = 2'b10;
						
					end
				else FlagW = 2'b00;    // Se Funct[0] == 0
				
				if ((Funct[4:1] == 4'b0101) || (Funct[4:1] == 4'b0110)) begin 
					FlagW = 2'b11;   			// Nao depende de S
					Nowrite = 1;
					end
				
				end
				
		
		
// Lógica PC 
		
	assign PCS = (((Rd == 4'b1111) & RegW) || B);
			
endmodule


/////////////////////////////////////////////  WAVEFORM 52

module condlogic ( clk, reset,Cond,ALUflags,FlagW,PCS,RegW, MemW,PCsrc, RegWrite, MemWrite,Nowrite);

input  clk, reset;
input  [3:0]Cond;
input  [3:0]ALUflags;
input  [1:0]FlagW;  // [1]N,Z [0]C,V
input  PCS;
input  RegW;
input  MemW;
input Nowrite;
output PCsrc;
output RegWrite;
output MemWrite;					
						
wire [3:0]FlagWrite;
wire [3:0]Flags;
wire CondEx;
						
	flipflop reg1(clk,reset,FlagWrite[1],ALUflags[3:2],Flags[3:2]);

	flipflop reg2(clk,reset,FlagWrite[0],ALUflags[1:0],Flags[1:0]);
							
// Controles de Escrita

	condcheck escrita(.Cond(Cond),.Flags(ALUflags),.CondEx(CondEx));

	assign FlagWrite = FlagW & {2{CondEx}}; 
	assign RegWrite  = RegW  & CondEx & ~Nowrite;
	assign MemWrite  = MemW  & CondEx;
	assign PCsrc     = PCS   & CondEx;
							
endmodule


///////////////////////////////////////////

module condcheck (Cond,Flags,CondEx);  // WAVEFORM 51
						
input  [3:0]Cond;
input  [3:0]Flags;
output reg CondEx;
wire neg,zero,carry,over,ge;
	
assign {neg,zero,carry,over} = Flags;
assign ge = (neg == over);
	
	always@*
		case(Cond)
			4'b0000 : CondEx = zero;			// EQ
			4'b0001 : CondEx = ~zero;			// NE
			4'b0010 : CondEx = ~neg;			// PL
			4'b0011 : CondEx = neg;				// MI
			4'b0100 : CondEx = over;			// VS
			4'b0101 : CondEx = (~zero)&neg;	// HI
			4'b0110 : CondEx = zero|~carry;	// LS
			4'b0111 : CondEx = (~zero)&(~ge);// GT
			4'b1000 : CondEx = ge;				// LT
			4'b1001 : CondEx = 1'b1;			// ALL	
				
			default : CondEx = 1'bx;
			
			endcase 
endmodule

///////////////////////////////////////////

module flipflop  (clk,res,en,d,q);
	input clk,res,en;
	input [1:0]d;
	output reg [1:0]q;

	always @(posedge clk, posedge res)
		if(res) 
			q<=2'b0;
		else 
			if(en) 
				q <= d;
endmodule

////////////////////////////////////////////////////

module Unidade_de_Controle(clk, reset,Instr,ALUflags,Regsrc,Immsrc,ALUcontrol, PCsrc, MemtoReg, MemWrite,ALUsrc, RegWrite);
	input clk, reset;								
	input [31:0]Instr;		
	input [3:0]ALUflags;
	
	output [3:0]Regsrc;
	output [1:0]Immsrc;
	output[3:0]ALUcontrol;
	
	output PCsrc, MemtoReg, MemWrite,ALUsrc, RegWrite;
	
	wire [3:0] FlagW;
	wire RegW, MemW, PCS,NoWrite;
	
	
	//module decoder(OP,Funct,Rd,FlagW,PCS,RegW,MemW,MemtoReg,ALUsrc,Immsrc,ALUcontrol,Regsrc);
	decoder dec(.OP(Instr[27:26]),.Funct(Instr[25:20]),.Rd(Instr[25:12]),.FlagW(FlagW),.PCS(PCS),.RegW(RegW),.MemW(MemW),.MemtoReg(MemtoReg),.ALUsrc(ALUsrc),.Immsrc(Immsrc),.ALUcontrol(ALUcontrol),.Regsrc(Regsrc),.Nowrite(Nowrite));	
	
	
	//module condlogic ( clk, reset,Cond,ALUflags,FlagW,PCS,RegW, MemW,PCsrc, RegWrite, MemWrite);
	condlogic ( .clk(clk), .reset(reset),.Cond(Instr[31:28]),.ALUflags(ALUflags),.FlagW(FlagW),.PCS(PCS),.RegW(RegW), .MemW(MemW), .PCsrc(PCsrc), .RegWrite(RegWrite), .MemWrite(MemWrite),.Nowrite(Nowrite));

endmodule 

///////////////////////////////////
///////////////////////////////////



module processador (clk,reset,Instr,ReadData, MemWrite,PC,ALUresult,WriteData,Regaux);

							
							
	input clk,reset;
	input [31:0]Instr;
	input [31:0]ReadData;
	output MemWrite;
	output [31:0]PC;
	output [31:0]ALUresult;
	output [31:0]WriteData;	
	output Regaux; //auxiliar

	wire [3:0] ALUflags,Regsrc,ALUcontrol;
	wire RegWrite, ALUsrc,MemtoReg,PCsrc,NoWrite;
	wire [1:0] Immsrc;
	
	assign Regaux = RegWrite;
	
	Unidade_de_Controle c(.clk(clk),.reset(reset),.Instr(Instr[31:0]),.ALUflags(ALUflags),.Regsrc(Regsrc),.Immsrc(Immsrc),.ALUcontrol(ALUcontrol),.PCsrc(PCsrc),.MemtoReg(MemtoReg),.MemWrite(MemWrite),.ALUsrc(ALUsrc),.RegWrite(RegWrite));
	
	
	datapath d(.clk(clk),.reset(reset),.RegWrite(RegWrite),.ALUsrc(ALUsrc),.MemtoReg(MemtoReg),.PCsrc(PCsrc),.ReadData(ReadData),.Instr(Instr),.Regsrc(Regsrc),.Immsrc(Immsrc),.ALUcontrol(ALUcontrol),.ALUflags(ALUflags),.PC(PC),.ALUresult(ALUresult),.WriteData(WriteData));
			  

endmodule

////////////////////////////////////////////////////// FIM

module ProcessadorMemoria (clk,reset,WriteData,DataAdr,MemWrite,PC,Instr,ReadData,Regaux);

input clk,reset;
output [31:0]WriteData,DataAdr;
output MemWrite;

output [31:0]PC,Instr,ReadData;
output Regaux; //auxiliar

processador processo(.clk(clk),.reset(reset),.Instr(Instr),.ReadData(ReadData),.MemWrite(MemWrite),.PC(PC),.ALUresult(DataAdr),.WriteData(WriteData),.Regaux(Regaux));


MemInstr mi(.clk(clk),.PC(PC),.Instr(Instr));

MemDados md(.clk(clk), .MemWrite(MemWrite),.DataAdr(DataAdr),.WriteData(WriteData),.ReadData(ReadData));



endmodule


