`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:49:15 11/02/2011 
// Design Name: 
// Module Name:    spiwrap 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////
module spiloop(
    input Reset,
    input SysClk,
    input spi_ss,
    input spi_mosi,
    input spi_clk,
    output spi_miso,
    output [7:0] leds
    );

wire [7:0]  debug_out;
wire [11:0] txMemAddr;
wire [7:0]  txMemData;
wire [11:0] rcMemAddr;
wire [7:0]  rcMemData;
wire        rcMemWE;

spiloopmem your_instance_name (
  .clka(spi_clk), // input clka
  .ena(1'b1), // input ena
  .wea(rcMemWE), // input [0 : 0] wea
  .addra(rcMemAddr), // input [11 : 0] addra
  .dina(rcMemData), // input [7 : 0] dina
  .clkb(spi_clk), // input clkb
  .enb(1'b1), // input enb
  .addrb(txMemAddr), // input [11 : 0] addrb
  .doutb(txMemData) // output [7 : 0] doutb
);

spiifc mySpiIfc (
  .Reset(Reset),
  .SysClk(SysClk),
  .SPI_CLK(spi_clk),
  .SPI_MISO(spi_miso),
  .SPI_MOSI(spi_mosi),
  .SPI_SS(spi_ss),
  .txMemAddr(txMemAddr),
  .txMemData(txMemData),
  .rcMemAddr(rcMemAddr),
  .rcMemData(rcMemData),
  .rcMemWE(rcMemWE),
  .debug_out(debug_out)
);

assign leds = debug_out ;

endmodule
