//=================================
//////////////Interface////////////
//=================================
`timescale 1ns / 1ps

interface Intf #(parameter 
				AddrBits = 12,
				RegAddrBits = 4
  )(input bit SysClk);

    // Inputs
	bit Reset;  
	bit SPI_CLK;
	bit SPI_MOSI;
	bit SPI_SS;
	logic [7:0] txMemData;
	logic [31:0] regReadData;
	logic [7:0] cmd_recvd; //saves firstbyte of the packet (command)

	// Outputs
	logic SPI_MISO;
	logic [AddrBits-1:0] txMemAddr;
	logic [AddrBits-1:0] rcMemAddr;
	logic [7:0] rcMemData;
	logic rcMemWE;
    logic [7:0] debug_out;
	logic [RegAddrBits-1:0] regAddr;
	logic regWriteEn;
	logic [31:0] regWriteData;
	
	reg SPI_CLK_en;
	
	initial begin
    #310
    SPI_CLK_en = 1;
	end
  
  initial begin
		SPI_CLK = 0;
		SPI_CLK_en = 0;
	end	
	
	always begin
    #10	if (SPI_CLK_en) #40 SPI_CLK = ~SPI_CLK;
	end 
  
  	clocking cb @(posedge SysClk);
      	output Reset;
		output SPI_CLK;
		output SPI_MOSI;
		output SPI_SS;
		output txMemData;
		output regReadData;
		
		input SPI_MISO;
		input txMemAddr;
		input rcMemAddr;
		input rcMemData;
		input rcMemWE;
		input debug_out;
		input regAddr;
		input regWriteEn;
		input regWriteData;
		
		endclocking

    modport TB(clocking cb);
	 
	
//=====================================
//========= Coverages =================
//=====================================

//covering Buffers addresses
 covergroup cg_buff_addr @(posedge SysClk);
  option.per_instance = 1;
  type_option.strobe = 1;
  cover_rc_addresses:  coverpoint uut.rcMemAddr
  { option.auto_bin_max = 4096; }  
  cover_tx_addresses: coverpoint uut.txMemAddr
  { option.auto_bin_max = 4096; } 
endgroup

  cg_buff_addr cvg_buf_addr = new(); 

//covering register addresses
 covergroup cg_reg_addr @(posedge SysClk);
  option.per_instance = 1;
  type_option.strobe = 1;
  cover_reg_addresses: coverpoint uut.regAddr
  { option.auto_bin_max = 16; }
endgroup
  
  cg_reg_addr cvg_reg_addr = new(); 
  
//covering CMD_REG_BIT
bit7_is_zero : cover property ( @(posedge SysClk) 
	$fell(SPI_SS) |=> first_match($rose(SPI_CLK)) |-> (uut.SPI_MOSI === 1'b0) );
bit7_is_one : cover property ( @(posedge SysClk) 
	$fell(SPI_SS) |=> first_match($rose(SPI_CLK)) |-> (uut.SPI_MOSI === 1'b1) );

//covering CMD_REG_WE_BIT
bit6_is_zero : cover property ( @(posedge SysClk) 
	$fell(SPI_SS) |=> first_match($rose(SPI_CLK) [=2]) |-> (uut.SPI_MOSI === 1'b0) );
bit6_is_one  : cover property ( @(posedge SysClk) 
	$fell(SPI_SS) |=> first_match($rose(SPI_CLK) [=2]) |-> (uut.SPI_MOSI === 1'b1) );
	
//covering all commands
sequence cmd_received;
 @(posedge SysClk) 
	$fell(SPI_SS) ##1 (first_match ($rose(SPI_CLK) [=8])) ;
endsequence: cmd_received

covergroup cg_cmd @(posedge SysClk);
  option.per_instance = 1;
  type_option.strobe = 1;
  cover_commands:  coverpoint cmd_recvd
  { bins CMD_READ_START  = {8'd1};
	bins CMD_READ_MORE   = {8'd2};
	bins CMD_WRITE_START = {8'd3};
	bins CMD_WRITE_MORE  = {8'd4};
	bins CMD_BUILD_WORD  = {[8'hC0:8'hCF]};
	bins CMD_SEND_WORD   = {[8'h80:8'h8F]};	
}  
 endgroup
 
 cg_cmd cvg_cmd = new();
 
always @ (cmd_received, posedge SPI_SS) begin
	if(SPI_SS) cmd_recvd <= 0;
	else begin
	cmd_recvd <= uut.rcMemData ;
	cvg_cmd.sample();
	end
end

//=====================================
//========= End of Coverages ==========
//=====================================
 
endinterface
 
