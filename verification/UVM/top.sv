//=========================================================================
///          **** Final Project Submission ****
/// Subject: CND-212 Digital Testing and Verification
/// Project: Verification of SPI slave IP with systemVerilog
/// Method : UVM 
/// RTL    : https://github.com/mjlyons/vSPI/blob/master/src/spi_base/spiifc.v
//=========================================================================

`timescale 1ns/1ps

  
//=================================
////////////////TOP////////////////
//=================================

`include "uvm_macros.svh"

module top;

	import uvm_pkg::*;
	import my_pkg::*;
  
	//interface instatiation 
	Intf intf();

	//dut instatiation  
	spiifc uut(
		.Reset(intf.Reset), 
		.SysClk(intf.SysClk),
		.SPI_CLK(intf.SPI_CLK), 
		.SPI_MISO(intf.SPI_MISO), 
		.SPI_MOSI(intf.SPI_MOSI), 
		.SPI_SS(intf.SPI_SS), 
		.txMemAddr(intf.txMemAddr), 
		.txMemData(intf.txMemData), 
		.rcMemAddr(intf.rcMemAddr), 
		.rcMemData(intf.rcMemData), 
		.rcMemWE(intf.rcMemWE),
		.regAddr(intf.regAddr),
		.regReadData(intf.regReadData),
		.regWriteEn(intf.regWriteEn),
		.regWriteData(intf.regWriteData),
		.debug_out(intf.debug_out)
	);

    initial begin
		uvm_config_db #(virtual Intf)::set(null, "*", "Intf", intf);
		uvm_top.finish_on_completion = 1;
		run_test("my_test");
		$finish;
	end

endmodule: top


