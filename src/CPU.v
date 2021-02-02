// Please include verilog file if you write module in other file

module CPU(
    input         clk,
    input         rst,
    output reg       instr_read,
    output reg [31:0] instr_addr,
    input  [31:0] instr_out,
    output        data_read,
    output        data_write,
    output [31:0] data_addr,
    output [31:0] data_in,
    input  [31:0] data_out
);

parameter [4:0] add_op = 5'b0,
                sub_op = 5'b00001,
                sl_op  = 5'b00010,
                sr_op  = 5'b00011,
                sru_op = 5'b00100,
                xor_op = 5'b00101,
                or_op  = 5'b00110,
                and_op = 5'b00111,
                slt_op = 5'b01000,
                sltu_op= 5'b01001,
                beq_op = 5'b01010,
                bne_op = 5'b01011,
                blt_op = 5'b01100,
                bgt_op = 5'b01101,
                bltu_op= 5'b01110,
                bgtu_op= 5'b01111,
                no_op  = 5'b10000;

wire [6:0] funct7;
reg  [6:0] opcode;
wire [2:0] funct3;
wire [4:0] rs2_addr, rs1_addr, rd_addr;
reg  [24:0] notOpcode;
wire [31:0] Imm_src;

wire RegWrite,
     ImmType,
     PCToRegSrc,
     RDSrc,
     MemRead,
     MemWrite,
     MemToReg,
     ALUSrc;

wire [2:0] ALUOp;
wire [1:0] BranchCtrl;
wire [31:0] rs1_data, rs2_data;
wire [31:0] rs2_or_imm_data;
wire [4:0] ALUCtrl;
wire [31:0] alu_out,
            pc_imm_out,
            pc_const_out,
            pc_to_reg,
            pc_or_alu_out,
            rd_data,
            pc_normal_out,
            pc_in;
reg [31:0] pc_out;
wire zero_flag;

initial begin
    instr_read = 1'b0;
    instr_addr = 32'b0;
end

adder normal_adder(
    .src        (instr_addr     ),
    .imm        ({29'b0, 3'b100}),
    .result     (pc_normal_out  )
);

distributer i_distributer(
    .notOpcode  (notOpcode      ),
    .rs1_addr   (rs1_addr       ),
    .rs2_addr   (rs2_addr       ),
    .rd_addr    (rd_addr        ),
    .funct7     (funct7         ),
    .funct3     (funct3         )
);

decoder i_decoder(
    .opcode     (opcode         ),
    .RegWrite   (RegWrite       ),
    .ImmType    (ImmType        ),
    .PCToRegSrc (PCToRegSrc     ),
    .RDSrc      (RDSrc          ),
    .MemRead    (MemRead        ),
    .MemWrite   (MemWrite       ),
    .MemToReg   (MemToReg       ),
    .ALUSrc     (ALUSrc         ),
    .ALUOp      (ALUOp          )
);

registerFile i_registerFile(
    .rs2_addr   (rs2_addr       ),
    .rs1_addr   (rs1_addr       ),
    .rd_addr    (rd_addr        ),
    .pc_out     (pc_out         ),
    .RegWrite   (RegWrite       ),
    .Din        (rd_data        ),
    .Rs1Data    (rs1_data       ),
    .Rs2Data    (rs2_data       )
);

ImmGen i_ImmGen(
    .opcode     (opcode         ),
    .funct7     (funct7         ),
    .rs2_addr   (rs2_addr       ),
    .rs1_addr   (rs1_addr       ),
    .funct3     (funct3         ),
    .rd_addr    (rd_addr        ),
    .ImmType    (ImmType        ),
    .Imm_src    (Imm_src        )
);


adder pc_imm_adder(
    .src        (pc_out         ),
    .imm        (Imm_src        ),
    .result     (pc_imm_out     )
);
adder pc_const_adder(
    .src        (pc_out         ),
    .imm        ({29'b0, 3'b100}),
    .result     (pc_const_out   )
);

mux_binary  after_two_adder_mux(
    .zero_path  (pc_const_out   ),
    .one_path   (pc_imm_out     ),
    .sel        (PCToRegSrc     ),
    .result     (pc_to_reg      )
);


mux_binary alu_mux(
    .zero_path  (Imm_src        ),
    .one_path   (rs2_data       ),
    .sel        (ALUSrc         ),
    .result     (rs2_or_imm_data)
);

ALUController i_aluController(
    .opcode     (opcode         ),
    .funct3     (funct3         ),
    .funct7     (funct7         ),
    .ALUOp      (ALUOp          ),
    .ALUCtrl    (ALUCtrl        )
);


ALU i_alu(
    .rs1_data           (rs1_data           ),
    .rs2_or_imm_data    (rs2_or_imm_data    ),
    .ALUCtrl            (ALUCtrl            ),
    .rd_addr            (rd_addr            ),
    .result             (alu_out            ),
    .zero_flag          (zero_flag          )
);

mux_binary alu_out_or_pc_to_reg_mux(
    .zero_path          (pc_to_reg          ),
    .one_path           (alu_out            ),
    .sel                (RDSrc              ),
    .result             (pc_or_alu_out      )
);



DataMem i_DataMem(
    .clk                (clk                ),
    .MemRead            (MemRead            ),
    .MemWrite           (MemWrite           ),
    .alu_out_addr       (alu_out            ),
    .rs2_data           (rs2_data           ),
    .data_addr          (data_addr          ),
    .data_in            (data_in            ),
    .data_read          (data_read          ),
    .data_write         (data_write         )
);


mux_binary rd_data_mux(
    .zero_path          (pc_or_alu_out      ),
    .one_path           (data_out           ),
    .sel                (MemToReg           ),
    .result             (rd_data            )
);

BranchController i_BranchController(
    .funct3             (funct3             ),
    .opcode             (opcode             ),
    .alu_out            (alu_out            ),
    .zero_flag          (zero_flag          ),
    .ALUOp              (ALUOp              ),
    .BranchCtrl         (BranchCtrl         )
);

mux_triple branch_triple_mux(
    .clk                (clk                ),
    .zero_path          (pc_normal_out      ),
    .one_path           (pc_imm_out         ),
    .two_path           (alu_out            ),
    .sel                (BranchCtrl         ),
    .result             (pc_in              )
);

always @(*) begin
    instr_addr <= pc_in;
end

/* Add your design */
always@(posedge clk) begin

    if (rst == 1) begin
        instr_read = 1'b0;
    end else begin

        if(instr_read == 1'b1) begin
            instr_read = 1'b0;
        end
        notOpcode = instr_out[31:7];
        opcode = instr_out[6:0];
        pc_out = instr_addr;
    end
end

endmodule


module distributer(
    input [24:0] notOpcode,
    output reg  [4:0] rs1_addr,
    output reg [4:0] rs2_addr,
    output reg [4:0] rd_addr,
    output reg [6:0] funct7,
    output reg [2:0] funct3
);


always @(notOpcode) begin

    funct7 = notOpcode[24:18];
    rs2_addr = notOpcode[17:13];
    rs1_addr = notOpcode[12:8];
    funct3 = notOpcode[7:5];
    rd_addr = notOpcode[4:0];

end

endmodule


module  decoder(
    input reg [6:0] opcode,
    output reg RegWrite,
    output reg ImmType,
    output reg PCToRegSrc,
    output reg RDSrc,
    output reg MemRead,
    output reg MemWrite,
    output reg MemToReg,
    output reg ALUSrc,
    output reg [2:0] ALUOp
);

always @(opcode) begin

    case( opcode )
    7'b0110011: begin // R-type
        RegWrite = 1'b1;
        ImmType = 1'b0;
        PCToRegSrc = 1'b0;
        RDSrc = 1'b1;
        MemRead = 1'b0;
        MemWrite = 1'b0;
        MemToReg = 1'b0;
        ALUSrc = 1'b1;
        ALUOp = 3'b000;
    end
    7'b0010011: begin // I-type normal
        RegWrite = 1'b1;
        ImmType = 1'b1;
        PCToRegSrc = 1'b0;
        RDSrc = 1'b1;
        MemRead = 1'b0;
        MemWrite = 1'b0;
        MemToReg = 1'b0;
        ALUSrc = 1'b0;
        ALUOp = 3'b001;
    end
    7'b0000011: begin // I-type Lw
        RegWrite = 1'b1;
        ImmType = 1'b1;
        PCToRegSrc = 1'b0;
        RDSrc = 1'b0;
        MemRead = 1'b1;
        MemWrite = 1'b0;
        MemToReg = 1'b1;
        ALUSrc = 1'b0;
        ALUOp = 3'b001;
    end
    7'b1100111: begin // I-type JALR
        RegWrite = 1'b1;
        ImmType = 1'b1;
        PCToRegSrc = 1'b0;
        RDSrc = 1'b0;
        MemRead = 1'b0;
        MemWrite = 1'b0;
        MemToReg = 1'b0;
        ALUSrc = 1'b0;
        ALUOp = 3'b001;
    end
    7'b0100011: begin // S-type
        RegWrite = 1'b0;
        ImmType = 1'b1;
        PCToRegSrc = 1'b0;
        RDSrc = 1'b1;
        MemRead = 1'b0;
        MemWrite = 1'b1;
        MemToReg = 1'b0;
        ALUSrc = 1'b0;
        ALUOp = 3'b010;
    end
    7'b1100011: begin // B-type
        RegWrite = 1'b0;
        ImmType = 1'b1;
        PCToRegSrc = 1'b0;
        RDSrc = 1'b0;
        MemRead = 1'b0;
        MemWrite = 1'b0;
        MemToReg = 1'b0;
        ALUSrc = 1'b1;// todo
        ALUOp = 3'b011;
    end
    7'b0010111: begin // U-type AUIPC
        RegWrite = 1'b1;
        ImmType = 1'b1;
        PCToRegSrc = 1'b1;
        RDSrc = 1'b0;
        MemRead = 1'b0;
        MemWrite = 1'b0;
        MemToReg = 1'b0;
        ALUSrc = 1'b0;
        ALUOp = 3'b111;
    end
    7'b0110111: begin // U-type LUI
        RegWrite = 1'b1;
        ImmType = 1'b1;
        PCToRegSrc = 1'b0;
        RDSrc = 1'b1;
        MemRead = 1'b0;
        MemWrite = 1'b0;
        MemToReg = 1'b0;
        ALUSrc = 1'b0;
        ALUOp = 3'b111;
    end
    7'b1101111: begin // J-type
        RegWrite = 1'b1;
        ImmType = 1'b1;
        PCToRegSrc = 1'b0;
        RDSrc = 1'b0;
        MemRead = 1'b0;
        MemWrite = 1'b0;
        MemToReg = 1'b0;
        ALUSrc = 1'b0;
        ALUOp = 3'b110;
    end
    endcase

end

endmodule

module registerFile(
    input [4:0] rs2_addr,
    input [4:0] rs1_addr,
    input [4:0] rd_addr,
    input [31:0] pc_out,
    input RegWrite,
    input [31:0] Din,
    output reg [31:0] Rs1Data,
    output reg [31:0] Rs2Data
);

reg [31:0] register [31:0];
integer i;

initial begin
    for(i=0;i<32;i=i+1) begin
        register[i] = 32'h00000000;
    end
end

always @(Din or rd_addr) begin

    if(RegWrite == 1 )begin
        if (rd_addr != 0) begin
            register[rd_addr] = Din;
        end else begin
            register[rd_addr] = 32'b0;
        end
    end

end


always @(rs1_addr or rs2_addr or pc_out) begin

    Rs1Data = register[rs1_addr];
    Rs2Data = register[rs2_addr];

end
endmodule



module ImmGen(
    input [6:0] opcode,
    input [6:0] funct7,
    input [4:0] rs2_addr,
    input [4:0] rs1_addr,
    input [2:0] funct3,
    input [4:0] rd_addr,
    input ImmType,
    output reg [31:0] Imm_src
);

always @(*) begin

    if(ImmType == 1) begin
        if (opcode == 7'b0000011 || opcode == 7'b0010011) begin // lw or i-type
            if (funct3 == 3'b001 || funct3 == 3'b101) begin
                Imm_src = {27'b0, rs2_addr};
            end else begin
                Imm_src = { (funct7[6] == 1 ? 20'hfffff : 20'b0), funct7, rs2_addr};
            end
        end else if (opcode == 7'b0100011) begin // sw
            Imm_src = { (funct7[6] == 1 ? 20'hfffff : 20'b0) , funct7, rd_addr};
        end else if (opcode == 7'b1100011) begin // Branch
            Imm_src = {19'b0, funct7[6], rd_addr[0], funct7[5:0], rd_addr[4:1], 1'b0 };
        end else if (opcode == 7'b0010111 || opcode == 7'b0110111) begin
            Imm_src = {funct7, rs2_addr, rs1_addr, funct3, 12'b0};
        end else if (opcode == 7'b1101111) begin // jal
            Imm_src = {11'b0, funct7[6], rs1_addr, funct3, rs2_addr[0], funct7[5:0], rs2_addr[4:1], 1'b0};
        end else if (opcode == 7'b1100111) begin  // jalr
            Imm_src = {  (funct7[6] == 1 ? 20'hfffff : 20'b0) , funct7, rs2_addr };
        end
    end

end

endmodule



module ALUController(
    input [6:0] opcode,
    input [2:0] funct3,
    input [6:0] funct7,
    input [2:0] ALUOp,
    output reg [4:0] ALUCtrl
);

parameter [4:0] add_op = 5'b0,
                sub_op = 5'b00001,
                sl_op  = 5'b00010,
                sr_op  = 5'b00011,
                sru_op = 5'b00100,
                xor_op = 5'b00101,
                or_op  = 5'b00110,
                and_op = 5'b00111,
                slt_op = 5'b01000,
                sltu_op= 5'b01001,
                beq_op = 5'b01010,
                bne_op = 5'b01011,
                blt_op = 5'b01100,
                bgt_op = 5'b01101,
                bltu_op= 5'b01110,
                bgtu_op= 5'b01111,
                no_op  = 5'b10000;


always@(*) begin

    case( { ALUOp, funct3} )
    6'b000000: begin // add or sub
        if(funct7[5] == 0) begin
            ALUCtrl = add_op; // add operation
        end else begin
            ALUCtrl = sub_op;// sub operation
        end
    end
    6'b000001: begin
        ALUCtrl = sl_op; // shift left
    end
    6'b000101: begin
         if(funct7[5] == 0) begin
            ALUCtrl = sru_op; // shift right unsigned operation
        end else begin
            ALUCtrl = sr_op; // shift right signed operation
        end
    end
    6'b000010: begin
        ALUCtrl = slt_op; // less than
    end
    6'b000011: begin
        ALUCtrl = sltu_op; // less than unsigned
    end
    6'b000100: begin
        ALUCtrl = xor_op; // xor
    end
    6'b000110: begin
        ALUCtrl = or_op; // or
    end
    6'b000111: begin
        ALUCtrl = and_op; // and
    end
    6'b001000: begin
        ALUCtrl = add_op; // add operation
    end
    6'b001010: begin
        if ( opcode == 7'b0000011 ) begin
            ALUCtrl = add_op;
        end else begin
            ALUCtrl = slt_op; // set less than
        end
    end
    6'b001011: begin
        ALUCtrl = sltu_op; // set less than unsigned
    end
    6'b001100: begin
        ALUCtrl = xor_op; // xor
    end
    6'b001110: begin
        ALUCtrl = or_op; // or
    end
    6'b001111: begin
        ALUCtrl = and_op; // and
    end
    6'b001001: begin
        ALUCtrl = sl_op; // shift left
    end
    6'b001101: begin
        if(funct7[5] == 0) begin
            ALUCtrl = sru_op; // shift right unisgned
        end else begin
            ALUCtrl = sr_op; // shift right signed
        end
    end
    6'b001000: begin
        ALUCtrl = add_op; // add
    end
    6'b010010: begin
        ALUCtrl = add_op; // sw uses add operation
    end
    6'b011000: begin
        ALUCtrl = beq_op; // branch equal
    end
    6'b011001: begin
        ALUCtrl = bne_op; // branch not equal
    end
    6'b011100: begin
        ALUCtrl = blt_op; // branch less than
    end
    6'b011101: begin
        ALUCtrl = bgt_op; // branch great than
    end
    6'b011110: begin
        ALUCtrl = bltu_op; // branch less than unsigned
    end
    6'b011111: begin
        ALUCtrl = bgtu_op; // branch greater than unsigned
    end
    default: begin
        ALUCtrl = no_op; // No operation
    end
    endcase
end

endmodule


module mux_binary(
    input [31:0] zero_path,
    input [31:0] one_path,
    input sel,
    output reg [31:0] result
);

always @(sel or zero_path or one_path) begin

    case(sel)
    1'b0: result = zero_path;
    1'b1: result = one_path;
    endcase
end

endmodule


module mux_triple(
    input clk,
    input [31:0] zero_path,
    input [31:0] one_path,
    input [31:0] two_path,
    input [1:0] sel,
    output reg [31:0] result
);

// initial begin

// end

always @(negedge clk ) begin
    case(sel)
    2'b00: result <= zero_path;
    2'b01: result <= one_path;
    2'b10: result <= two_path;
    endcase
end

endmodule


module adder(
    input [31:0] src,
    input [31:0] imm,
    output reg [31:0] result
);

always @(src or imm) begin
    result = src + imm;
end

endmodule


module ALU(
    input [31:0] rs1_data,
    input [31:0] rs2_or_imm_data,
    input [4:0] rd_addr,
    input [4:0] ALUCtrl,
    output reg [31:0] result,
    output reg zero_flag
);

parameter [4:0] add_op = 5'b0,
                sub_op = 5'b00001,
                sl_op  = 5'b00010,
                sr_op  = 5'b00011,
                sru_op = 5'b00100,
                xor_op = 5'b00101,
                or_op  = 5'b00110,
                and_op = 5'b00111,
                slt_op = 5'b01000,
                sltu_op= 5'b01001,
                beq_op = 5'b01010,
                bne_op = 5'b01011,
                blt_op = 5'b01100,
                bgt_op = 5'b01101,
                bltu_op= 5'b01110,
                bgtu_op= 5'b01111,
                no_op  = 5'b10000;

always @(rs1_data or rs2_or_imm_data or ALUCtrl or rd_addr) begin
    case(ALUCtrl)
    add_op  :     begin zero_flag = 0; result = rs1_data + rs2_or_imm_data; end
    sub_op  :     begin zero_flag = 0; result = rs1_data - rs2_or_imm_data; end
    sl_op   :     begin zero_flag = 0; result = rs1_data << rs2_or_imm_data[4:0]; end
    sr_op   :     begin zero_flag = 0; result = $signed(rs1_data) >>> rs2_or_imm_data[4:0]; end
    sru_op  :     begin zero_flag = 0; result = rs1_data >> rs2_or_imm_data[4:0]; end
    xor_op  :     begin zero_flag = 0; result = rs1_data ^ rs2_or_imm_data; end
    or_op   :     begin zero_flag = 0; result = rs1_data | rs2_or_imm_data; end
    and_op  :     begin zero_flag = 0; result = rs1_data & rs2_or_imm_data; end
    slt_op  :     begin zero_flag = 0; result = $signed(rs1_data) < $signed(rs2_or_imm_data) ? 1 : 0; end
    sltu_op :     begin zero_flag = 0; result = rs1_data < rs2_or_imm_data ? 1:0; end
    beq_op  :     zero_flag = rs1_data == rs2_or_imm_data ? 1 : 0;
    bne_op  :     zero_flag = rs1_data != rs2_or_imm_data ? 1 : 0;
    blt_op  :     zero_flag = $signed(rs1_data) < $signed(rs2_or_imm_data) ? 1 : 0;
    bgt_op  :     zero_flag = $signed(rs1_data) >= $signed(rs2_or_imm_data) ? 1 : 0;
    bltu_op :     zero_flag = rs1_data < rs2_or_imm_data ? 1 : 0;
    bgtu_op :     zero_flag = rs1_data >= rs2_or_imm_data ? 1 : 0;
    no_op   :     begin zero_flag = 0; result = rs2_or_imm_data; end
    default :     zero_flag = 0;
    endcase
end

endmodule



module DataMem(
    input clk,
    input MemRead,
    input MemWrite,
    input [31:0] alu_out_addr,
    input [31:0] rs2_data,
    output reg [31:0] data_addr, // represent the data address in DM
    output reg [31:0] data_in, // represent the data will be wrote into DM
    output reg data_read,
    output reg data_write
);

always @( negedge clk ) begin

    if ( MemRead == 1'b1) begin
        data_read <= 1'b1;
        data_addr <= alu_out_addr;
        data_in <= rs2_data;
    end else begin
        data_read <= 1'b0;
    end

    if (MemWrite == 1'b1) begin
        data_write <= 1'b1;
        data_addr <= alu_out_addr;
        data_in <= rs2_data;
    end else begin
        data_write <= 1'b0;
    end
end

endmodule


module BranchController(
    input [2:0] funct3,
    input [6:0] opcode,
    input [31:0] alu_out,
    input zero_flag,
    input [2:0] ALUOp,
    output reg [1:0] BranchCtrl
);

always @(*) begin

    if( {ALUOp, funct3} == 6'b001000 && opcode == 7'b1100111) begin
        BranchCtrl = 2'b10;
    end else if(zero_flag == 1'b1 || opcode == 7'b1101111) begin
        BranchCtrl = 2'b01;
    end else begin
        BranchCtrl = 2'b0;
    end
end

endmodule

