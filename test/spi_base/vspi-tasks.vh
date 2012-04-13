//
// Sends a byte to logic over spi, gets byte back
//

//
// Call before doing any multi-byte SPI transmission
//
task spiTxStart;
begin
  spi_ss = 0;
  #20;
end
endtask

//
// Call after doing a multi-byte SPI transmission
task spiTxStop;
begin
  spi_ss = 1;
  #20;
end
endtask

task spiExchByte;
input  [7:0] byteToSend;
output [7:0] recvByte;
reg    [7:0] recvByte;
integer bitIndex;
begin
  spi_clk = 1'b0;

  //$display("Sending byte via spi: 8'h%02X", byteToSend);
  bitIndex = 8;
  while (bitIndex > 0) begin
    #20
    bitIndex = bitIndex - 1;  
    //$display("Sending bit[%0d] via spi: %b", 
    //         bitIndex, byteToSend[bitIndex]);
    spi_mosi = byteToSend[bitIndex];
    recvByte[bitIndex] = spi_miso;
    spi_clk = 1'b1;
   
    #20 
    spi_clk = 1'b0;
  end
end
endtask

//
// Sends a byte to vSPI, but not receive anything
//
task spiSendByte;
input [7:0] byteToSend;
reg   [7:0] recvByte;
begin
  spiExchByte(byteToSend, recvByte);
end
endtask

//
// Receives a byte from vSPI, but does not send anything
//
task spiRecvByte;
output [7:0] recvByte;
reg    [7:0] recvByte;
begin
  spiExchByte(8'hFF, recvByte);
end
endtask

//
// Write register on vspi
//
task spiWriteReg;
input [ 3:0] regId;
input [31:0] regValue;
integer      byteId;
begin
  spiTxStart();
  spiSendByte({4'b1100, regId});	// Write spi.reg
  byteId = 4;
  while (byteId > 0) begin
    byteId = byteId - 1;
    spiSendByte(regValue[byteId*8 +: 8]);
  end
  spiTxStop();
end
endtask

//
// Read spi register
//
task spiReadReg;
input  [ 3:0] regId;
output [31:0] regValue;
reg    [31:0] regValue;
integer byteId;
begin
  spiTxStart();
  spiSendByte({4'h8, regId});
  byteId = 4;
  while (byteId > 0) begin
    byteId = byteId - 1;
    spiRecvByte(regValue[byteId*8 +: 8]);
  end
  spiTxStop();
end
endtask

//
// Initializes in preparation to write to spi memory buffer
//
task spiWriteMemStart;
begin
  spiTxStart();
  spiSendByte(8'h01);
end
endtask

//
// Writes a byte to a memory transfer in progress
//
task spiWriteMemNextByte;
input [7:0] writeByte;
begin
  spiSendByte(writeByte);
end
endtask

//
// Finishes writing to memory over spi
//
task spiWriteMemStop;
begin
  spiTxStop();
end
endtask

//
// Prepares to read a byte from spi memory
//
task spiReadMemStart;
begin
  spiTxStart();
  spiSendByte(8'h03);
end
endtask

//
// Read a byte from a memory transfer in progress
//
task spiReadMemNextByte;
output [7:0] recvByte;
reg    [7:0] recvByte;
begin
  spiRecvByte(recvByte);
end
endtask

//
// Finishes reading from spi memory
//
task spiReadMemStop;
begin
  spiTxStop();
end
endtask

