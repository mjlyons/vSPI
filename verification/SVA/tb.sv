`timescale 1ns / 1ps

module tb  #(parameter 
				AddrBits = 12,
				RegAddrBits = 4
			)(Intf.TB tb_if);

	parameter bytes_count = 200000;//200k for full cov
	parameter pkts_count = 50; //50 for full cov
	reg [7:0] currRcByte;
	reg [7:0] pastRcByte;
	reg [7:0] currCmnd;
	reg [7:0] pastCmnd;
	reg [7:0] currTxByte;
	int index;
	int pkt_length;
	
	//Data Randomization
	class ByteRandomizer;
	
	rand bit [7:0] data_in[bytes_count] ;
	rand bit [7:0] cmnd[pkts_count];
	rand bit [7:0] reg_cmnd[40];
	rand bit [31:0] regReadData[32];
	
	
	constraint read_first {foreach (cmnd[i])
							(i<10) -> cmnd[i] == 8'h01;} // let first ten packets read data only.
	constraint cmnd_value{foreach (cmnd[i])
			cmnd[i] dist{8'h01:=10, //CMD_READ_START 40
						 8'h02:=10, //CMD_READ_MORE 10
						 8'h03:=10, //CMD_WRITE_START 20
						 8'h04:=10  //CMD_WRITE_MORE 20
						 }; }

	constraint reg_cmnds {foreach (reg_cmnd[i])
						  reg_cmnd[i] dist{[8'hC0:8'hCF]:=1,  //CMD_BUILD_WORD
										   [8'h80:8'h8F]:=1};}//CMD_SEND_WORD

	endclass

	ByteRandomizer byteRandomizer;
	
	//task to send currRcByte bit by bit
	task recvByte;
		input   [7:0] rcByte;
		integer       rcBitIndex;
		begin
		//$display("%g - spiifc receiving byte '0x%h'", $time, rcByte);     
			for (rcBitIndex = 0; rcBitIndex < 8; rcBitIndex = rcBitIndex + 1) begin
				tb_if.cb.SPI_MOSI <= rcByte[7 - rcBitIndex];
				#100;
			end
		end
	endtask
	
	//Data Stimulus
	initial begin
	// Initialize Inputs
	tb_if.cb.Reset <= 0;
		 
	tb_if.cb.SPI_MOSI <= 0;
	tb_if.cb.SPI_SS <= 1;
	tb_if.cb.txMemData <= 0;

	// Wait for global reset to finish
	#100;
	tb_if.cb.Reset <= 1;
	#100;
	tb_if.cb.Reset <= 0;
	#100;
	
	// Initialize the randomizer
    byteRandomizer = new();
	void'(byteRandomizer.randomize());
	
	pkt_length = bytes_count / pkts_count;
	
	//Testing rc & tx Buffers
	for (int i=0; i<pkts_count ; i++) begin
		
		//Start of Packet	
		tb_if.cb.SPI_SS <= 0;
		
		//Sending the Command
		$display("%g - start of packet - command[%0d] = 0x%h",$time,i,byteRandomizer.cmnd[i]);
		pastCmnd = currCmnd;
		currCmnd = byteRandomizer.cmnd[i];
		recvByte(currCmnd);
		
		//Sending the Data
		for (int j=0 ; j<pkt_length; j++) begin
		index = (i*pkt_length)+j;
		$display("%g - randomized data_in[%0d] = 0x%h",$time,index,byteRandomizer.data_in[index]);
		pastRcByte = currRcByte;
		currRcByte = byteRandomizer.data_in[index];
		if(currCmnd == 8'h03 || currCmnd == 8'h04) begin
			recvByte(currRcByte);
			tb_if.cb.txMemData  <= currRcByte; end
		else recvByte(currRcByte);
		end
		
		//End of Packet
		tb_if.cb.SPI_SS <= 1; 
		#1000;
		
	end
		
	//Testing regbank
	for (int i=0; i<43 ; i++) begin
		
		//Start of Packet	
		tb_if.cb.SPI_SS <= 0;
		
		//Sending the Command
		$display("%g - start of packet - command[%0d] = 0x%h",$time,i,byteRandomizer.reg_cmnd[i]);
		pastCmnd = currCmnd;
		currCmnd = byteRandomizer.reg_cmnd[i];
		recvByte(currCmnd);
		
		//Sending the Data
		for (int j=0 ; j<4; j++) begin
		index = (i*4)+j;
		$display("%g - randomized reg_data_in[%0d] = 0x%h",$time,index,byteRandomizer.data_in[index]);
		pastRcByte = currRcByte;
		currRcByte = byteRandomizer.data_in[index];
		recvByte(currRcByte);
		if(currCmnd[7:6] == 2'b10) tb_if.cb.regReadData <= byteRandomizer.regReadData[i];
		end
		
		//End of Packet
		tb_if.cb.SPI_SS <= 1; 
		#1000;
		
	end
	
	$finish;
	
	end
    	
endmodule
