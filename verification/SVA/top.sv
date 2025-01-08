//==============================================================================
///          **** Final Project Submission ****
/// Subject: CND-212 Digital Testing and Verification
/// Project: Verification of SPI slave IP with systemVerilog
/// RTL    : https://github.com/mjlyons/vSPI/blob/master/src/spi_base/spiifc.v
//==============================================================================

`timescale 1ns/1ns

  
//=================================
////////////////TOP////////////////
//=================================
module top();
   
//Main clock
bit SysClk;
always begin
    #20 SysClk = ~SysClk;
  end
 
 Intf intf(SysClk);
 
 spiifc uut (
		.Reset		 (intf.Reset), 
		.SysClk		 (SysClk),
		.SPI_CLK	 (intf.SPI_CLK), 
		.SPI_MISO	 (intf.SPI_MISO), 
		.SPI_MOSI	 (intf.SPI_MOSI), 
		.SPI_SS		 (intf.SPI_SS), 
		.txMemAddr   (intf.txMemAddr), 
		.txMemData   (intf.txMemData), 
		.rcMemAddr	 (intf.rcMemAddr), 
		.rcMemData	 (intf.rcMemData), 
		.rcMemWE	 (intf.rcMemWE),
		.regAddr	 (intf.regAddr),
		.regReadData (intf.regReadData),
		.regWriteEn	 (intf.regWriteEn),
		.regWriteData(intf.regWriteData),
		.debug_out	 (intf.debug_out)
		);
 
 tb tb1(intf.TB);
 
 bind uut assertions SVA_inst (Reset,
   SysClk,
   SPI_CLK,
   SPI_MOSI,
   SPI_SS,
   rcMemWE);
   
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
  end 
  
endmodule : top
 
