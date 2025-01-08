`timescale 1ns / 1ps

module assertions(
  input Reset,
  input SysClk,
  input SPI_CLK,
  input SPI_MOSI,
  input SPI_SS,
  input rcMemWE
  );

parameter AddrBits = 12;
parameter RegAddrBits = 4;

`define CMD_READ_START    8'd1
`define CMD_READ_MORE     8'd2
`define CMD_WRITE_START   8'd3
`define CMD_WRITE_MORE    8'd4
`define CMD_SEND          8'h83


reg state_writing;
reg state_send;
reg state_build;
reg [AddrBits-1:0] pastTxMemAddr;
reg [31:0] currRcWord;
reg [RegAddrBits-1:0]  reg_addr;
reg validByte;

//reg for state build, will be used in assertions
always @(SysClk) begin
		if(intf.cmd_recvd[7] && !SPI_SS) begin// & uut.rcMemData[7] & uut.rcMemData[6]) begin
		state_build <= (intf.cmd_recvd[6] ? 1 : 0);
		state_send  <= (~intf.cmd_recvd[6] ? 1 : 0);
		end else begin
		state_build <= 0;
		state_send  <= 0;
		end
end

//setting sequences for multiple usage
sequence valid_Byte;
@(posedge SysClk)
		!SPI_SS throughout (first_match ($rose(SPI_CLK) [=8])) ;
endsequence:valid_Byte

sequence building_word;
@(posedge SysClk)
		// (!SPI_SS && state_build) throughout (first_match ($rose(SPI_CLK) [*8])) ;
		$fell(SPI_SS) ##1 valid_Byte ##1 (intf.cmd_recvd[7:6] == 2'b11);
endsequence:building_word


//=====================================
//======= rc Buffer Assertions ========
//=====================================
//-1 ---- tb byte to rcMem check ----
always @ (valid_Byte) begin
		rcMem_Data:  assert  (uut.rcMemData == tb1.currRcByte || uut.rcMemData == tb1.currCmnd)  else $error("passing currByte to rcMem"); 
		#800;
	end
//----------------------------------	

//-2 ----- rcMemAddr inc check -----
property rcMemAddr_incr;
 @(posedge SysClk) disable iff (Reset)
	rcMemWE |=> (uut.rcMemAddr == ($past(uut.rcMemAddr) + 1));
endproperty: rcMemAddr_incr

rcMem_Addr:  assert property (rcMemAddr_incr) else $error("incrementing rcMemAddr");
//----------------------------------

//-3 -------- rcMemWE check --------
property rcMemWE_check;
 @(posedge SysClk) 
	rcMemWE |=> valid_Byte |=> (intf.cmd_recvd === `CMD_READ_START) || (intf.cmd_recvd === `CMD_READ_MORE) || (intf.cmd_recvd === `CMD_SEND);
endproperty: rcMemWE_check

rcMem_WE:  assert property (rcMemWE_check)  else $error("in enabling rcMemWE"); 
//----------------------------------


//=====================================
//======= tx Buffer Assertions ========
//=====================================

//preparing data for following assertions
always @(posedge SPI_CLK, valid_Byte) begin
	pastTxMemAddr <= $past(uut.txMemAddr);
end

always @(SysClk) begin
	state_writing <= (intf.cmd_recvd == `CMD_WRITE_START) || (intf.cmd_recvd == `CMD_WRITE_MORE);
end

//-1 -------- txMem_Data ----------
reg [2:0]i = 3'd7;
always @(valid_Byte) begin
	if(intf.cmd_recvd == 8'h03 || intf.cmd_recvd == 8'h04) begin
		for(int j=0; j<8; j++) begin
		i <= i-1;
		#100;
		end
	end else i <= 7;  
	end

property txMem_Data; @(posedge SysClk)
	$rose(SPI_CLK) and (!SPI_SS) and (state_writing == 1'b1) |-> (uut.SPI_MISO === uut.txMemData[i]);
endproperty: txMem_Data

tx_Mem_Data: assert property (txMem_Data);
//---------------------------------

//-2 -------- txMem_Addr ----------
property txMemAddr; @(posedge SysClk)
	$fell(SPI_SS) |=> valid_Byte |=> (state_writing == 1'b1) |=> valid_Byte |=> (uut.txMemAddr == ($past(uut.txMemAddr) + 1));
endproperty: txMemAddr

txMem_Addr: assert property (txMemAddr);

//---------------------------------


//=====================================
//======= register Assertions ========
//=====================================
//-1 -------- regRead_Data ----------
reg [4:0] index = 5'd31;
always @(posedge SPI_CLK) begin
	if(state_send & (!SPI_SS) ) index <= index-1;
	else index <= 5'd32; 
end

property regRead_Data; @(posedge SysClk)
	state_send and $rose(SPI_CLK)  |-> uut.SPI_MISO === uut.regReadData[index];
endproperty: regRead_Data

reg_Read_Data: assert property (regRead_Data);
//------------------------------------

//-2 -------- regWrite_Data ----------
always @(building_word) begin
	for(int i=0; i<4; i++) begin
	#800;
	case(i) 
		0: currRcWord[31:24] <= intf.rcMemData;
		1: currRcWord[23:16] <= intf.rcMemData;
		2: currRcWord[15:8]  <= intf.rcMemData;
		3: currRcWord[7:0]   <= intf.rcMemData;
	endcase
	end
end

property regWrite_Data; @(posedge SysClk)
	$fell(SPI_SS)|=> valid_Byte |=> (intf.cmd_recvd[7:6] == 2'b11) |=> valid_Byte [*4] |=> ##3 (uut.regWriteData == currRcWord);
endproperty: regWrite_Data

reg_Write_Data: assert property (regWrite_Data) else $error("reading RegWriteData");
//----------------------------------

//-3 -------- regWrite_En ----------
property regWrite_En;
 @(posedge SysClk)
	 $fell(SPI_SS)|=> valid_Byte |=> (intf.cmd_recvd[7:6] == 2'b11) |=> valid_Byte [*4]	|=> (uut.regWriteEn == 1'b1);
endproperty: regWrite_En

reg_Write_En: assert property (regWrite_En) else $error("in enabling reg regWriteEn");
//---------------------------------

//-4 -------- regAddr ---------
property regAddr;
 @(posedge SysClk) 
	(!uut.state) && uut.rcByteValid && uut.rcByte[7] |=> (uut.regAddr == uut.rcByte[3:0]);
endproperty: regAddr

reg_Addr: assert property (regAddr) else $error("in passing reg addr");
//---------------------------------


//=====================================
//======== System Assertions ==========
//=====================================
//-1 ------ Buffs Addr check -------
property addr_is_reset;
 @(posedge SysClk) $rose(Reset) |=>  (uut.txMemAddr === 12'h000) and (uut.rcMemAddr === 12'h000);
endproperty: addr_is_reset

	addr_reset: assert property (addr_is_reset)  else $error("Buffers Addresses are not reset!");
//----------------------------------

// -2 -------- debug_out check -------
property debug_check;
 @(posedge SysClk) disable iff (Reset)
	(!SPI_SS) |=> valid_Byte   |-> (uut.debug_out === tb1.pastRcByte || uut.debug_out === tb1.currCmnd) ;
endproperty: debug_check

always @ (posedge SPI_CLK) begin
debug:    assert property (debug_check)    else $error("reading debug");
#800;
end
//----------------------------------

endmodule