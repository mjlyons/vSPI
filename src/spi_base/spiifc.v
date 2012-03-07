`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    16:46:12 03/02/2012 
// Design Name: 
// Module Name:    spiifc 
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
module spiifc(
  Reset,
  SysClk,
  SPI_CLK,
  SPI_MISO,
  SPI_MOSI,
  SPI_SS,
  txMemAddr,
  txMemData,
  rcMemAddr,
  rcMemData,
  rcMemWE,
  debug_out
);

//
// Parameters
//
parameter AddrBits = 12;

//
// Defines
//
`define CMD_READ_START    8'd1
`define CMD_READ_MORE     8'd2
`define CMD_WRITE_START   8'd3
`define CMD_WRITE_MORE    8'd4
`define CMD_INTERRUPT     8'd5

`define STATE_GET_CMD     8'd0
`define STATE_READING     8'd1
`define STATE_WRITING     8'd2
`define STATE_WRITE_INTR  8'd3

//
// Input/Outputs
//
input                 Reset;
input                 SysClk;
input                 SPI_CLK;
output                SPI_MISO;     // outgoing (from respect of this module)
input                 SPI_MOSI;     // incoming (from respect of this module)
input                 SPI_SS;
output [AddrBits-1:0] txMemAddr;    // outgoing data
input           [7:0] txMemData;
output [AddrBits-1:0] rcMemAddr;    // incoming data
output          [7:0] rcMemData;
output                rcMemWE;
output          [7:0] debug_out;

//
// Registers
//
reg                   prev_spiClk;    // Value of SPI_CLK during last SysClk cycle
reg                   prev_spiSS;     // Value of SPI_SS during last SysClk cycle
reg             [7:0] state_reg;      // Register backing the 'state' wire
reg             [7:0] rcByte_reg;     // Register backing 'rcByte'
reg             [2:0] rcBitIndex_reg; // Register backing 'rcBitIndex'
reg    [AddrBits-1:0] rcMemAddr_reg;  // Byte addr to write MOSI data to

//
// Wires
//
wire                  risingSpiClk;   // Did the SPI_CLK rise since last SysClk cycle?
wire                  validSpiBit;    // Are the SPI MOSI/MISO bits new and valid?
reg                   state;          // Current state in the module's state machine (always @* effectively wire)
wire                  rcByteValid;    // rcByte is valid and new
wire            [7:0] rcByte;         // Byte received from master
wire            [2:0] rcBitIndex;     // Bit of rcByte to write to next

// Detect new valid bit
always @(posedge SysClk) begin
  prev_spiClk <= SPI_CLK;
end
assign risingSpiClk = SPI_CLK & (~prev_spiClk);
assign validSpiBit = risingSpiClk & (~SPI_SS);

// Detect new SPI packet (SS dropped low)
always @(posedge SysClk) begin
  prev_spiSS <= SPI_SS;
end
assign packetStart = prev_spiSS & (~SPI_SS);

// Build incoming byte
always @(posedge SysClk) begin
  if (validSpiBit) begin
    rcByte_reg[rcBitIndex] <= SPI_MOSI;
    rcBitIndex_reg <= (rcBitIndex > 0 ? rcBitIndex - 1 : 7);
  end else begin
    rcBitIndex_reg <= rcBitIndex;
  end
end
assign rcBitIndex = (Reset || packetStart ? 7 : rcBitIndex_reg); 
assign rcByte = {rcByte_reg[7:1], SPI_MOSI};
assign rcByteValid = (validSpiBit && rcBitIndex == 0 ? 1 : 0);

// Incoming MOSI data buffer management
assign rcMemAddr = rcMemAddr_reg;
assign rcMemData = rcByte;
assign rcMemWE = (state == `STATE_READING && rcByteValid ? 1 : 0);
always @(posedge SysClk) begin
  if (Reset || (`STATE_GET_CMD == state && rcByteValid)) begin
    rcMemAddr_reg <= 0;
  end else if (rcMemWE) begin
    rcMemAddr_reg <= rcMemAddr + 1;
  end else begin
    rcMemAddr_reg <= rcMemAddr;
  end
end

// State machine
always @(*) begin
  if (Reset || packetStart) begin
    state <= `STATE_GET_CMD;
  end else if (state_reg == `STATE_GET_CMD && rcByteValid) begin
    state <= rcByte;
  end else begin
    state <= state_reg;
  end
end
always @(posedge SysClk) begin
  if (`STATE_GET_CMD == state && rcByteValid) begin
    if (`CMD_READ_START == rcByte) begin
      state_reg <= `STATE_READING;
    end else if (`CMD_READ_MORE == rcByte) begin
      state_reg <= `STATE_READING;
    end else if (`CMD_WRITE_START == rcByte) begin
      state_reg <= `STATE_WRITING;
    end else if (`CMD_WRITE_MORE == rcByte) begin
      state_reg <= `STATE_WRITING;
    end else if (`CMD_INTERRUPT == rcByte) begin
      // TODO: NYI
    end   
  end else begin
    state_reg <= state;
  end
end

endmodule
