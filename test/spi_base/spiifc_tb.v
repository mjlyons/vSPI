`timescale 1ns / 1ps

////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer:
//
// Create Date:   19:46:21 10/18/2011
// Design Name:   spiifc
// Module Name:   C:/workspace/robobees/hbp/fpga/spiifc/spiifc_tb.v
// Project Name:  spiifc
// Target Device:  
// Tool versions:  
// Description: 
//
// Verilog Test Fixture created by ISE for module: spiifc
//
// Dependencies:
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
////////////////////////////////////////////////////////////////////////////////

module spiifc_tb;

	// Inputs
	reg Reset;
	reg SPI_CLK;
	reg SPI_MOSI;
	reg SPI_SS;
  reg [7:0] MemData;

	// Outputs
	wire SPI_MISO;
  wire [11:0] MemAddr;

  // Memory
  reg [7:0]  Mem [0:4095];
  
  integer i;
  
	// Instantiate the Unit Under Test (UUT)
	spiifc uut (
		.Reset(Reset), 
		.SPI_CLK(SPI_CLK), 
		.SPI_MISO(SPI_MISO), 
		.SPI_MOSI(SPI_MOSI), 
		.SPI_SS(SPI_SS),
    .MemAddr(MemAddr),
    .MemData(MemData)
	);

  always @(posedge SPI_CLK) begin
    MemData <= Mem[MemAddr];
  end

  always @(*) begin
    #50;
    SPI_CLK <= ~SPI_CLK;
  end

	initial begin
    // Initialize memory
    for (i = 0; i < 4096; i = i + 2) begin
//      Mem[i] <= i[7:0];
      Mem[i]   <= 8'hFF;
      Mem[i+1] <= 8'h00;
    end
  
		// Initialize Inputs
		Reset = 0;
		SPI_CLK = 0;
		SPI_MOSI = 0;
		SPI_SS = 1;

		// Wait 100 ns for global reset to finish
		#100;
        
		// Add stimulus here
    Reset <= 1'b1;
    #100;
    
    Reset <= 1'b0;
    #100;
    
    SPI_SS <= 1'b0;
    #4000;
    
    SPI_SS <= 1'b1;
    #400;
    
    $finish;

	end
      
endmodule

