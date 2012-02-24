`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    19:24:33 10/18/2011 
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
  
  // Defines
  `define  CMD_READ_START   8'd1
  `define  CMD_READ_MORE    8'd2
  `define  CMD_WRITE_START  8'd3
  
  `define  STATE_GET_CMD    8'd0
  `define  STATE_READING    8'd1
  `define  STATE_WRITING    8'd2
  
  //
  // Input/Output defs
  //
  input  Reset;
  input  SysClk;
  
  input  SPI_CLK;
  output SPI_MISO;
  input  SPI_MOSI;
  input  SPI_SS;
  
  output [AddrBits-1:0] txMemAddr;
  input  [7:0]          txMemData;
  
  output  [AddrBits-1:0] rcMemAddr;
  output  [7:0]          rcMemData;
  output                 rcMemWE;
  
  output  [7:0]          debug_out;
  
  //
  // Registers
  // 
  
  reg  [ 7: 0] debug_reg;
  
  reg  [ 7: 0] rcByteReg;
  reg          rcStarted;
  reg  [ 2: 0] rcBitIndexReg;
  reg  [11: 0] rcMemAddrReg;
  reg  [11: 0] rcMemAddrNext;
  reg  [ 7: 0] rcMemDataReg;
  reg          rcMemWEReg;
  
  reg          ssPrev;
  
  reg          ssFastToggleReg;
  reg          ssSlowToggle;
  
  reg          ssTurnOnReg;
  reg          ssTurnOnHandled;
  
  reg  [ 7: 0] cmd;
  reg  [ 7: 0] stateReg;
  
  reg  [11: 0] txMemAddrReg;
  reg  [ 2: 0] txBitAddr;
  
  //
  // Wires
  //
  wire         rcByteValid; 
  wire [ 7: 0] rcByte;
  wire         rcStarting;
  wire [ 2: 0] rcBitIndex;
  
  wire         ssTurnOn;
  
  wire         ssFastToggle;
  
  wire [ 7: 0] state;
  
  wire         txMemAddrReset;
  
  //
  // Output assigns
  //
  assign debug_out = debug_reg;
  
  assign rcMemAddr = rcMemAddrReg;
  assign rcMemData = rcMemDataReg;
  assign rcMemWE = rcMemWEReg;
  
  assign txMemAddrReset = (rcByteValid && rcByte == `CMD_WRITE_START ? 1 : 0);
  assign txMemAddr = (txMemAddrReset ? 0 : txMemAddrReg);
  assign SPI_MISO = txMemData[txBitAddr];
  
  assign ssFastToggle = 
      (ssPrev == 1 && SPI_SS == 0 ? ~ssFastToggleReg : ssFastToggleReg);
  
  //
  // Wire assigns
  //
  assign rcByteValid = rcStarted && rcBitIndex == 0;
  assign rcByte = {rcByteReg[7:1], SPI_MOSI};
  assign rcStarting = ssTurnOn;
  assign rcBitIndex = (rcStarting ? 3'd7 : rcBitIndexReg);
  
  assign ssTurnOn = ssSlowToggle ^ ssFastToggle;
  assign state = (rcStarting ? `STATE_GET_CMD : stateReg);
  
  initial begin
    ssSlowToggle <= 0;
  end
  
  always @(posedge SysClk) begin
    ssPrev <= SPI_SS;
    
    if (Reset) begin
      ssTurnOnReg <= 0;
      ssFastToggleReg <= 0;

    end else begin
      if (ssPrev & (~SPI_SS)) begin
        ssTurnOnReg <= 1;
        ssFastToggleReg <= ~ssFastToggleReg;
        
      end else if (ssTurnOnHandled) begin
        ssTurnOnReg <= 0;
      end
    end
    
  end
  
  always @(posedge SPI_CLK) begin
    ssSlowToggle <= ssFastToggle;
  
    if (Reset) begin
      // Resetting
      rcByteReg <= 8'h00;
      rcStarted <= 0;
      rcBitIndexReg <= 3'd7;
      ssTurnOnHandled <= 0;
      debug_reg <= 8'hFF;
      
    end else begin
      // Not resetting
      
      ssTurnOnHandled <= ssTurnOn;
      stateReg <= state;
      rcMemAddrReg <= rcMemAddrNext;
          
      if (~SPI_SS) begin
        rcByteReg[rcBitIndex] <= SPI_MOSI;
        rcBitIndexReg <= rcBitIndex - 3'd1;
        rcStarted <= 1;
        
        // Update txBitAddr if writing out
        if (`STATE_WRITING == state) begin
          if (txBitAddr == 3'd1) begin
            txMemAddrReg <= txMemAddr + 1;
          end 
          txBitAddr <= txBitAddr - 1;
        end
      end
      
      // We've just received a byte (well, currently receiving the last bit)
      
      if (rcByteValid) begin
        // For now, just display on LEDs
        debug_reg <= rcByte;
      
        if (`STATE_GET_CMD == state) begin
          cmd <= rcByte;    // Will take effect next cycle
          
          if (`CMD_READ_START == rcByte) begin
            rcMemAddrNext <= 0;
            stateReg <= `STATE_READING;
          end else if (`CMD_READ_MORE == rcByte) begin
            stateReg <= `STATE_READING;
          end else if (`CMD_WRITE_START == rcByte) begin
            txBitAddr <= 3'd7;
            stateReg <= `STATE_WRITING;
            txMemAddrReg <= txMemAddr;  // Keep at 0
          end
         
        end else if (`STATE_READING == state) begin
          rcMemDataReg <= rcByte;
          rcMemAddrNext <= rcMemAddr + 1;
          rcMemWEReg <= 1;
        
//        end else if (`STATE_WRITING == state) begin
//          txBitAddr <= 3'd7;
//          stateReg <= `STATE_WRITING;
        end
      
      end else begin
        // Not a valid byte
        rcMemWEReg <= 0;
        
      end // valid/valid' byte
      
    end // Reset/Reset'
  end
  
/*
reg rcByte_valid;
wire rcClockBridgeEmpty;
wire readRcByte;
assign getRcByte = ~rcClockBridgeEmpty;
wire rcClockBridgeReadValid;
wire rcClockBridgeFull;
wire [7:0] rcByte;
clock_bridge recvClockBridge (
  .rst(Reset), // input rst
  .wr_clk(~SPI_CLK), // input wr_clk
  .rd_clk(SysClk), // input rd_clk
  .din(SPI_MOSI), // input [0 : 0] din
  .wr_en(~SPI_SS), // input wr_en
  .rd_en(getRcByte), // input rd_en
  .dout(rcByte), // output [7 : 0] dout
  .full(rcClockBridgeFull), // output full
  .empty(rcClockBridgeEmpty), // output empty
  .valid(rcClockBridgeReadValid) // output valid
);
always @(posedge SysClk) begin
  rcByte_valid <= getRcByte;
end

wire txCmdClkBridgeEmpty;
wire txCmdClkBridgeFull;
wire [7:0] txCmd;
wire txCmdValid;
assign txCmdValid = ~txCmdClkBridgeEmpty;
wire postTxCmd;
assign postTxCmd = 
fifo_8bit_to_8bit txCmdClkBridge(
  .rst(Reset), // input rst
  .wr_clk(SysClk), // input wr_clk
  .rd_clk(SPI_CLK), // input rd_clk
  .din(din), // input [7 : 0] din
  .wr_en(post), // input wr_en
  .rd_en(txCmdValid), // input rd_en
  .dout(txCmd), // output [7 : 0] dout
  .full(txCmdClkBridgeFull), // output full
  .empty(txCmdClkBridgeEmpty) // output empty
);



  //
  // TRANSMIT: FPGA TO PC
  //
  assign SPI_MISO = txMemData[bitIndex]; 
  
  reg [2:0]          bitIndex;
  reg [AddrBits-1:0] byteAddr;
  
  assign txMemAddr = byteAddr;
  
  reg [7:0] debug_reg;
  assign debug_out = debug_reg;

  initial begin
    debug_reg <= 8'h00;
    //rcState <= 0;
  end

  //
  // Clocked logic
  //
  always @(posedge SPI_CLK) begin
    if (Reset) begin
      bitIndex <= 3'd0;
      byteAddr <= 0;
      
    end else if (SPI_SS == 1'b0) begin
      bitIndex <= bitIndex - 3'd1;
      if (bitIndex == 3'd1) begin
        byteAddr <= byteAddr + 1;
      end
    end
  end
  
  //
  // RECEIVE: PC TO FPGA 
  //
   
  // Detect start of receive
  reg       ss_prev;
  wire      ss_negedge;
  always @(posedge SysClk) begin
    ss_prev <= SPI_SS;
  end
  assign ss_negedge = (ss_prev == 1'b1 && SPI_SS == 1'b0 ? 1'b1 : 1'b0); 
  
  `define RC_MODE_GET_STATUS  8'd0
  `define RC_MODE_GET_BUFFER  8'd1
  `define RC_MODE_PUT_BUFFER  8'd2
  reg [7:0] rcMode;
  
  `define RC_STATE_CMD        8'd0
  `define RC_STATE_SIZE       8'd1
  `define RC_STATE_PAYLOAD    8'd2
  reg [7:0] rcState;
  
  reg [31:0] rcByteCount;
  reg [31:0] rcByteSize;
  
  reg [7:0]          rcMemData_reg;
  reg [AddrBits-1:0] rcMemAddr_reg;
  reg                rcMemWE_reg;
  assign rcMemData = rcMemData_reg;
  assign rcMemAddr = rcMemAddr_reg;
  assign rcMemWE   = rcMemWE_reg;
  
  always @(posedge SysClk) begin
    
//    // About to receive
//    if (ss_negedge) begin
//      rcBitIndex <= 3'd7;
//      rcState <= `RC_STATE_CMD;
//      
//      debug_reg[0] <= 1;
//    end
//    
//    // Receiving
//    if (receiving) begin
//      rcByte[rcBitIndex] <= SPI_MOSI;
//      rcBitIndex <= rcBitIndex - 3'd1;
//    end
//    rcByte_valid <= (receiving && rcBitIndex == 3'd0 ? 1'b1 : 1'b0);
    
    
    // Handle the complete incoming byte
    if (rcByte_valid) begin
      
      debug_reg[7:4] <= rcByte[3:0];

      // First byte: the command
      if (`RC_STATE_CMD == rcState || ss_negedge) begin
        // Disable writing to the read buffer (will be left on if the prev
        // cycle was writing to it)
        rcMemWE_reg <= 1'b0;

        debug_reg[0] <= 1;
      
        // Decode the SPI command
        case (rcByte)
          `RC_MODE_GET_STATUS: begin end  // no status yet
          `RC_MODE_GET_BUFFER: begin rcMode <= `RC_MODE_GET_BUFFER; rcState <= `RC_STATE_SIZE; end  
          `RC_MODE_PUT_BUFFER: begin rcMode <= `RC_MODE_PUT_BUFFER; rcState <= `RC_STATE_SIZE; end
        endcase
          
        // Initialize counters
        rcByteCount <= 32'd0;
        rcByteSize <= 32'd0;
          
        end
        
      // Record size (in bytes) of payload
      if (`RC_STATE_SIZE == rcState) begin
        debug_reg[1] <= 1;
        case (rcByteCount)
          32'd0:  begin rcByteSize[31:24] <= rcByte; rcByteCount <= 32'd1; end
          32'd1:  begin rcByteSize[23:16] <= rcByte; rcByteCount <= 32'd2; end
          32'd2:  begin rcByteSize[15: 8] <= rcByte; rcByteCount <= 32'd3; end
          32'd3:  begin 
            rcByteSize[ 7: 0] <= rcByte; 
            rcByteCount <= 32'd0; 
            rcState <= `RC_STATE_PAYLOAD; 
            rcByteCount <= 32'd0;
            
            if (`RC_MODE_GET_BUFFER == rcMode) begin
              // TODO: want reset tx byte addr here probably
            end
          end
        endcase
      end
        
      // The payload
      if (rcState == `RC_STATE_PAYLOAD) begin
        debug_reg[2] <= 1;
        case (rcMode)
          `RC_MODE_GET_BUFFER: begin
            // IGNORE EVERYTHING SO STUFF CAN BE READ OUT
          end
          
          `RC_MODE_PUT_BUFFER: begin
            //debug_reg[4] <= 1;
            rcMemWE_reg <= 1'b1;
            rcMemData_reg <= rcByte;
            rcMemAddr_reg <= rcByteCount[AddrBits-1:0];
          end            
        endcase

        if (rcByteCount == rcByteSize - 1) begin
          rcState <= `RC_STATE_CMD;
          //debug_reg[5] <= 1;
        end else begin
          rcByteCount <= rcByteCount + 32'd1;
        end
      end
    end 
    
    else begin // not valid byte
      if (ss_negedge) begin
        rcState <= `RC_STATE_CMD;
      end
    end
  end
  
  //reg   [7:0]          rcByteReg;
  //wire  [7:0]          rcByte;
  //assign rcByte = {rcByteReg[7:1], (SPI_SS == 1'b0 && bitIndex == 
  

//  //
//  // Receive (GPU to SPI)
//  //
//  reg        SPI_SS_prev_cycle;
//  
//  // This is the register backing rcByteId. It is always one cycle
//  // behind the true value of rcByteId, which we have to do a little
//  // work to get instantaneously correct using wire logic.
//  reg   [31:0]  rcByteIdPrev;    
//  wire  [31:0]  rcByteId;
//  assign rcByteId = (SPI_SS_prev_cycle == 1 && SPI_SS == 0 ? 32'd0 : 32'd1 + rcByteIdPrev);
//
//  // 1 if we're receiving from GPC, 0 if not.
//  wire isRecv;
//  assign isRecv = ~SPI_SS;
//  
//  // Bits to Byte aggregator
//  reg [2:0] rcBitId;
//  reg [7:0] rcByte;
//  
//  
//  reg [31:0]    rcSizeBytes;
//  
//  always @(posedge SPI_CLK) begin
//    if (1 == isRecv) begin
//      case (rcByteId)
//        0: rcSizeBytes[ 7: 0] <= 
//    end
//    
//    // Update registers for next cycle
//    SPI_SS_prev_cycle <= SPI_SS;
//    rcByteId <= rcByteIdPrev;
//  end
*/
  
endmodule
