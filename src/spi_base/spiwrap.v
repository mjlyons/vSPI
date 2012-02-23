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
module spiwrap(
    input Reset,
    input SysClk,
    input spi_ss,
    input spi_mosi,
    input spi_clk,
    output spi_miso,
    output [7:0] leds
    );

wire [31:0] douta_dummy;

wire [11:0] spi_addr;
wire [ 7:0] spi_data;

reg        initMem;
reg [ 9:0] initMemAddr;
reg [31:0] initMemData;

always @(posedge SysClk) begin
  if (Reset) begin
    initMem <= 1'b1;
    initMemAddr <= 10'h000;
    //initMemData <= 32'hFF00_FF00;
    initMemData <= 32'h5A6C_C6A5; /*32'h55CC_55CC*/;
    
  end else begin
    if (initMem == 1'b1) begin
      // Turn off init mem mode if formatted memory 
      if (initMemAddr == 10'h3FF) begin
        initMem <= 1'b0;
      end
    
      // Increment init mem addr/data
      initMemAddr <= initMemAddr + 10'h001;
      //initMemData <= ~initMemData;
    end
  end
end

spimem spiMemTx (
  .clka(SysClk), // input clka
  .ena(1'b1), // input ena
  .wea(initMem), // input [0 : 0] wea
  .addra(initMemAddr), // input [9 : 0] addra
  .dina(initMemData), // input [31 : 0] dina
  .douta(douta_dummy), // output [31 : 0] douta
  .clkb(spi_clk), // input clkb
  .enb(1'b1), // input enb
  .web(1'b0), // input [0 : 0] web
  .addrb(spi_addr), // input [11 : 0] addrb
  .dinb(8'h00), // input [7 : 0] dinb
  .doutb(spi_data) // output [7 : 0] doutb
);

wire        spi_rcMem_we;
wire [11:0] spi_rcMem_addr; 
wire [ 7:0] spi_rcMem_data;
wire [ 7:0] debug_out;
wire [ 7:0] spi_rcMem_doutb_dummy;
spimem spiMemRc (
  .clka(SysClk),
  .ena(1'b1),
  .wea(1'b0),
  .addra(10'h000),
  .douta(debug_out),
  .clkb(spi_clk),
  .enb(1'b1),
  .web(spi_rcMem_we),
  .addrb(spi_rcMem_addr),
  .dinb(spi_rcMem_data),
  .doutb(spi_rcMem_doutb_dummy)
);

spiifc mySpiIfc (
  .Reset(Reset),
  .SysClk(SysClk),
  .SPI_CLK(spi_clk),
  .SPI_MISO(spi_miso),
  .SPI_MOSI(spi_mosi),
  .SPI_SS(spi_ss),
  .txMemAddr(spi_addr),
  .txMemData(spi_data),
  .rcMemAddr(spi_rcMem_addr),
  .rcMemData(spi_rcMem_data),
  .rcMemWE(spi_rcMem_we),
  .debug_out(leds)
);



//assign leds = debug_out;

endmodule
