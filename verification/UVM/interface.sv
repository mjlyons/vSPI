//=================================
//////////////Interface////////////
//=================================
`timescale 1ns / 1ps

interface Intf  ();//input bit SysClk);
	
	parameter AddrBits = 12;
	parameter RegAddrBits = 4;
    
	// Inputs
	bit Reset;  
	bit SPI_CLK;
	bit SysClk;
	bit SPI_MOSI;
	bit SPI_SS;
	logic [7:0] txMemData;
	logic [7:0] cmnd; //saves firstbyte of the packet (command)
	static logic [7:0] cmd_recvd; //calculates current command
	static logic [7:0] cmd_recvd_temp;
	logic [7:0] data_in_temp; //saves current byte of the array data_in[pktlength] from the driver's transaction
	logic get_cmnd; //Flag to indicate the state Get Command
	bit   [7:0] MISO_reg;
	int i;
	
 	// Outputs
	bit SPI_MISO;
	logic [AddrBits-1:0] txMemAddr;
	logic [AddrBits-1:0] rcMemAddr;
	logic [7:0] rcMemData;
	bit rcMemWE;
    logic [7:0] debug_out;
	logic [RegAddrBits-1:0] regAddr;
	bit regWriteEn;
	logic [31:0] regReadData;
	logic [31:0] regWriteData;
    reg SPI_CLK_en;
	
	//Clocks
	always begin
		#20 SysClk = ~SysClk;
	end
	
	always begin
		#10 
		if (SPI_CLK_en) #40 SPI_CLK <= ~SPI_CLK;
	end
	
	initial begin
		SPI_CLK <= 0;
		SPI_CLK_en = 0;
		#310
		SPI_CLK_en = 1;
	end
  
	// Multiple sequences and variables will be used later in the scoreboard predictor.
	sequence receiving_cmnd; @(posedge SysClk) 
		$fell(SPI_SS) ;
	endsequence: receiving_cmnd
	
	sequence cmd_received; @(posedge SysClk) 
		$fell(SPI_SS) ##1 (first_match ($rose(SPI_CLK) [=8])) ;
	endsequence: cmd_received
	
	always @ (cmd_received) begin
		cmd_recvd <= uut.rcMemData ;
	end
	
	always @ (receiving_cmnd) begin
		get_cmnd <= 1; 
		#800;
		get_cmnd <= 0;
	end
	
	always@(posedge SysClk) begin
		if(cmnd !== 8'h03 && cmnd !== 8'h04 && cmnd[7:6] !== 2'b10) begin
		   if(get_cmnd) MISO_reg = (SPI_MISO == 1 ? 8'hff : 8'h00);
		   else MISO_reg = 8'h00;
		end
		else if((cmnd == 8'h03 || cmnd == 8'h04 || cmnd[7:6] == 2'b10) && !SPI_SS) begin
  		   for(i=0; i<8; i++) begin
					@(posedge SPI_CLK);
					MISO_reg[7-i] = SPI_MISO;
	       end
		end 
	end
	
endinterface
