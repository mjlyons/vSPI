`include "uvm_macros.svh"
`timescale 1ns/1ps

package my_pkg;

  import uvm_pkg::*;


  class my_transaction extends uvm_sequence_item;
  
    `uvm_object_utils(my_transaction)
	
	parameter      pkt_length = 4000;//for full coverage generate 60 pkts of 4k bytes length
	
	//Inputs
	bit 	       Reset;
    bit       	   SPI_MOSI;
    bit            SPI_SS;
	rand bit [7:0] txMemData;
	rand bit [7:0] data_in[pkt_length];
	rand bit [7:0] cmnd;
	rand bit [7:0] reg_cmnd;
	rand bit [31:0]regReadData;
	bit      [7:0] data_in_temp;
	
	//Outputs
	bit            SPI_MISO;
	bit      [7:0] rcMemData;
	bit      [7:0] MISO_reg;//saves MISO output for ckecking
	bit      [11:0]rcMemAddr;
	bit      [11:0]txMemAddr;
	bit      [3:0] regAddr;
	bit      [7:0] cmd_recvd;
	bit            get_cmnd;
	bit            SPI_CLK;
	bit      [31:0]regWriteData;
	
    constraint cmnd_value{cmnd
					dist{
						 8'h01:=30,  //CMD_READ_START
						 8'h02:=20,  //CMD_READ_MORE
						 8'h03:=30,  //CMD_WRITE_START
						 8'h04:=20}; //CMD_WRITE_MORE
					    }
						
	constraint reg_cmnd_value{reg_cmnd
					dist{[8'hC0:8'hCF]:=16,  //CMD_BUILD_WORD
						 [8'h80:8'h8F]:=16}; //CMD_SEND_WORD
					    }
    
    function new (string name = "");
      super.new(name);
    endfunction
    
    function string convert2string;//Prints Inputs
      return $sformatf("rcMemData=8'h%0h, rcMemAddr=8'h%0h, cmnd=8'h%0h, MISO_reg=8'h%0h, txMemAddr=8`h%0h, regWriteData=8`h%0h, regAddr=8`h%0h",
						rcMemData       , rcMemAddr       , cmnd       , MISO_reg       , txMemAddr       , regWriteData       , regAddr);
    endfunction

	function string output2string;//Prints Outputs
      return $sformatf("rcMemData=8'h%0h, rcMemAddr=8'h%0h, cmnd=8'h%0h, MISO_reg=8'h%0h, txMemAddr=8`h%0h, regWriteData=8`h%0h, regAddr=8`h%0h",
                     	rcMemData       , rcMemAddr       , cmd_recvd  , MISO_reg       , txMemAddr       , regWriteData      , regAddr);
    endfunction
	
    function void do_copy(uvm_object rhs);
      my_transaction tx;
      $cast(tx, rhs);
      Reset        = tx.Reset;
      SPI_MOSI     = tx.SPI_MOSI;
      SPI_SS       = tx.SPI_SS;
	  txMemData    = tx.txMemData;
	  data_in      = tx.data_in;
	  data_in_temp = tx.data_in_temp;
	  cmnd         = tx.cmnd;
	  reg_cmnd     = tx.reg_cmnd;
	  regReadData  = tx.regReadData;
	  rcMemAddr    = tx.rcMemAddr;
	  txMemAddr    = tx.txMemAddr;
	  cmd_recvd    = tx.cmd_recvd;
	  regAddr      = tx.regAddr;
	  rcMemData    = tx.rcMemData;
	  get_cmnd     = tx.get_cmnd;
	  MISO_reg     = tx.MISO_reg;
	  SPI_MISO     = tx.SPI_MISO;
	  SPI_CLK      = tx.SPI_CLK;
	  regWriteData = tx.regWriteData;
    endfunction
    
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);//called in the comparator class in the scoreboard
      my_transaction tx;
      bit status = 1;
      $cast(tx, rhs);
	  
	  status &= (rcMemData == tx.rcMemData);
	  status &= (rcMemAddr == tx.rcMemAddr);
	  status &= (MISO_reg  == tx.MISO_reg);
	  status &= (txMemAddr == tx.txMemAddr);
	  status &= (regWriteData == tx.regWriteData);
	  status &= (regAddr   == tx.regAddr);
      return status;
    endfunction

  endclass: my_transaction

  class my_sequence    extends uvm_sequence  #(my_transaction);
  
    `uvm_object_utils(my_sequence)
    
	my_transaction pkt;
	parameter pkts_count = 60;

    function new (string name = "");
      super.new(name);
    endfunction

    task body;
        if (starting_phase != null)
		  starting_phase.raise_objection(this,"Start of sequence");
	
		repeat(pkts_count) begin
		/*1*/ pkt = my_transaction::type_id::create("pkt");
		/*2*/ start_item(pkt);
		/*3*/ if(!pkt.randomize()) 
				`uvm_error("", $sformatf("Randomization for packet[%0d] failed",pkts_count))
		/*4*/ finish_item(pkt);	
	    end
	
	    if (starting_phase != null)
    	  starting_phase.drop_objection(this,"End of sequence");
    endtask: body
   
  endclass: my_sequence


  class my_sequencer   extends uvm_sequencer #(my_transaction);

	`uvm_component_utils(my_sequencer)

	function new(string name = "my_sequencer", uvm_component parent = null);
	  super.new(name, parent);
	endfunction

  endclass: my_sequencer
  
  class my_driver      extends uvm_driver    #(my_transaction);
  
    `uvm_component_utils(my_driver)

	my_transaction pkt;
    virtual Intf dut_vi;
    
	function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
      if(! uvm_config_db #(virtual Intf)::get(this, "", "Intf", dut_vi) )
        `uvm_error("", "uvm_config_db::get failed")
    endfunction 
   
    task run_phase(uvm_phase phase);
      begin      
	
		//Initialize Inputs
		dut_vi.Reset     <= 0;
	    dut_vi.SPI_MOSI  <= 0;
	    dut_vi.SPI_SS    <= 1;
	    dut_vi.txMemData <= 0;

	    //Global Reset
     	#100;
	    dut_vi.Reset <= 1;
	    #100;
	    dut_vi.Reset <= 0;
	    #100;
		
		forever
			begin
			seq_item_port.get_next_item(pkt);//Unblock start_item(start randomization,driver is ready to get a trans)		

			//Packet start		
			dut_vi.SPI_SS    <= 0;
			
			/*** Testing rc & tx Buffers ***/
			//------------------------------
			//Sending the Command
			`uvm_info("Driver",$sformatf("@%0t *** Start of Packet *** command = 0x%h \n",$time,pkt.cmnd),UVM_LOW);
			dut_vi.cmnd = pkt.cmnd;
			recvByte(pkt.cmnd);

			//Sending the Data
			for (int j=0 ; j<pkt.pkt_length; j++) begin
				`uvm_info("Driver",$sformatf("@%0t - randomized data_in[%0d] = 0x%h \n",$time,j,pkt.data_in[j]),UVM_LOW);
				dut_vi.data_in_temp = pkt.data_in[j];
				if(pkt.cmnd == 8'h03 || pkt.cmnd == 8'h04) dut_vi.txMemData = pkt.data_in[j]; 
				recvByte(pkt.data_in[j]);
			end
			
			dut_vi.SPI_SS    <= 1;
			#1000;
			dut_vi.SPI_SS    <= 0;
			
			/*** Testing register bank ***/
			//-----------------------------
			//Sending the Command
			`uvm_info("Driver",$sformatf("@%0t *** Start of Packet *** command = 0x%h \n",$time,pkt.reg_cmnd),UVM_LOW);
			dut_vi.cmnd = pkt.reg_cmnd;
			recvByte(pkt.reg_cmnd);

			//Sending the Data
			for (int j=0 ; j<4; j++) begin
				`uvm_info("Driver",$sformatf("@%0t - randomized data_in[%0d] = 0x%h \n",$time,j,pkt.data_in[j]),UVM_LOW);
				dut_vi.data_in_temp = pkt.data_in[j];
				if(pkt.reg_cmnd == 8'h80) dut_vi.regReadData = pkt.regReadData;
				recvByte(pkt.data_in[j]);
			end
			
			//Packet finish
			dut_vi.SPI_SS    <= 1;
			#1000;
			
			seq_item_port.item_done();//Unblock finish_item(go for next seq, driver has finished wiggling the intf)
			end
		
	  end
    endtask: run_phase

    task recvByte;//Send the byte on MOSI bit by bit
    input   [7:0] rcByte;
    integer       rcBitIndex;
    begin
      // `uvm_info("Driver", $sformatf("%0t - spiifc receiving byte '0x%h'", $time, rcByte),UVM_LOW)
      for (rcBitIndex = 0; rcBitIndex < 8; rcBitIndex = rcBitIndex + 1) begin
        dut_vi.SPI_MOSI <= rcByte[7 - rcBitIndex];
        #100;
      end
    end
	endtask: recvByte
	
  endclass: my_driver
 
  class output_monitor extends uvm_monitor;

	`uvm_component_utils(output_monitor)

	virtual Intf dut_vi;
	uvm_analysis_port #(my_transaction) analysis_port;
	my_transaction m_trans;
	
	function new(string name, uvm_component parent);
	  super.new(name, parent);
	  analysis_port = new("analysis_port",this);
	  m_trans = new();
	endfunction
	
	function void build_phase(uvm_phase phase);
    super.build_phase(phase); 
		
	if( !uvm_config_db #(virtual Intf)::get(this, "", "Intf", dut_vi) )
        `uvm_fatal("OUTPUT MON", "uvm_config_db::get failed")
    endfunction 
	
	task run_phase(uvm_phase phase); 
		m_trans = my_transaction::type_id::create("m_trans");
		
		forever begin
		@(posedge dut_vi.SysClk && !dut_vi.SPI_SS); //Synchronized with the Input Monitor
			repeat (8) @(posedge dut_vi.SPI_CLK && !dut_vi.SPI_SS);//Sample every one Valid Byte
			@(posedge dut_vi.SysClk);
			m_trans.SPI_CLK   = dut_vi.SPI_CLK;
			m_trans.rcMemData = dut_vi.rcMemData;
			m_trans.rcMemAddr = dut_vi.rcMemAddr;
			m_trans.txMemData = dut_vi.txMemData;
			m_trans.txMemAddr = dut_vi.txMemAddr;
			m_trans.MISO_reg  = dut_vi.MISO_reg;
			m_trans.SPI_MISO  = dut_vi.SPI_MISO;
			m_trans.cmd_recvd = dut_vi.cmd_recvd;
			m_trans.cmnd      = dut_vi.cmnd;
			m_trans.get_cmnd  = dut_vi.get_cmnd;
			m_trans.regReadData = dut_vi.regReadData;
			m_trans.regWriteData = dut_vi.regWriteData;
			m_trans.regAddr   = dut_vi.regAddr;
			
			`uvm_info("OUTPUT MON", $sformatf("OUTPUTS: rcMemData=8'h%0h, rcMemAddr=8'h%0h, MISO_reg=8'h%0h, txMemAddr=8'h%0h", 
											          m_trans.rcMemData, m_trans.rcMemAddr, m_trans.MISO_reg, m_trans.txMemAddr), UVM_LOW)
			analysis_port.write(m_trans);
		end
	endtask	
	
  endclass: output_monitor

  class input_monitor  extends uvm_monitor;

	`uvm_component_utils(input_monitor)

	virtual Intf dut_vi;
	uvm_analysis_port #(my_transaction) analysis_port;
	my_transaction m_trans;
	
	function new(string name, uvm_component parent);
	  super.new(name, parent);
	  analysis_port = new("analysis_port",this);
	  m_trans = new();
	endfunction
	
	function void build_phase(uvm_phase phase);
      super.build_phase(phase); 
	  if( !uvm_config_db #(virtual Intf)::get(this, "", "Intf", dut_vi) )
        `uvm_fatal("INPUT MON", "uvm_config_db::get failed")
    endfunction 
	
	task run_phase(uvm_phase phase); 
		m_trans = my_transaction::type_id::create("m_trans");
		
		forever begin
		@ (posedge dut_vi.SysClk && !dut_vi.SPI_SS); //Synchronized with Output Monitor
			repeat (8) @(posedge dut_vi.SPI_CLK && !dut_vi.SPI_SS);//Sample every one Valid Byte
			@(posedge dut_vi.SysClk);
			m_trans.SPI_CLK      = dut_vi.SPI_CLK;
			m_trans.rcMemData    = dut_vi.rcMemData;
			m_trans.rcMemAddr    = dut_vi.rcMemAddr;
			m_trans.data_in_temp = dut_vi.data_in_temp;
			m_trans.txMemData    = dut_vi.txMemData;
			m_trans.cmd_recvd    = dut_vi.cmd_recvd;
			m_trans.cmnd         = dut_vi.cmnd;
			m_trans.get_cmnd     = dut_vi.get_cmnd;
			m_trans.MISO_reg     = dut_vi.MISO_reg;
			m_trans.SPI_MISO     = dut_vi.SPI_MISO;
			m_trans.regReadData  = dut_vi.regReadData;
			m_trans.regWriteData = dut_vi.regWriteData;
			m_trans.regAddr      = dut_vi.regAddr;
			
			`uvm_info("INPUT MON", $sformatf("INPUTS : data_in=8'h%0h, cmnd=8'h%0h,  txMemData=8'h%0h",
										      m_trans.data_in_temp,  m_trans.cmnd,  m_trans.txMemData), UVM_LOW)
			analysis_port.write(m_trans);
		end
	endtask	
	
  endclass: input_monitor
 
 
  class my_agent       extends uvm_agent;

    `uvm_component_utils(my_agent)
    
	my_sequencer   m_seqr;
    my_driver      m_driv;
	output_monitor op_monitor;
	uvm_analysis_port #(my_transaction) analysis_port;
	
    function new(string name, uvm_component parent);
      super.new(name, parent);
	  analysis_port = new("analysis_port",this);
    endfunction
 
	function void build_phase(uvm_phase phase);
      m_seqr    = my_sequencer::type_id::create("m_seqr", this);
      m_driv    = my_driver::type_id::create("m_driv", this);
	  op_monitor = output_monitor::type_id::create("m_monitor", this);
    endfunction
    
    function void connect_phase(uvm_phase phase);
	  m_driv.seq_item_port.connect(m_seqr.seq_item_export);
	  op_monitor.analysis_port.connect(analysis_port);
    endfunction

  endclass: my_agent	

  class passive_agent  extends uvm_agent;

    `uvm_component_utils(passive_agent)
    
	input_monitor   ip_monitor;
	uvm_analysis_port #(my_transaction) p_analysis_port;
	
    function new(string name, uvm_component parent);
      super.new(name, parent);
	  p_analysis_port = new("p_analysis_port",this);
    endfunction
 
	function void build_phase(uvm_phase phase);
	  ip_monitor = input_monitor::type_id::create("ip_monitor", this);
    endfunction
    
    function void connect_phase(uvm_phase phase);
	  ip_monitor.analysis_port.connect(p_analysis_port);
    endfunction

  endclass: passive_agent

  class my_coverage    extends uvm_subscriber  #(my_transaction);

	`uvm_component_utils(my_coverage)

	my_transaction pkt;
	
	//Covering Buffers addresses
	covergroup cg_buff;
		option.per_instance = 1;
	    cover_rc_addresses:  coverpoint pkt.rcMemAddr {option.auto_bin_max = 4096;}  
	    cover_tx_addresses:  coverpoint pkt.txMemAddr {option.auto_bin_max = 4096;} 
	endgroup
	
	//Covering all commands
	covergroup cg_cmd;
		option.per_instance = 1;
		cover_commands:  coverpoint pkt.cmd_recvd
	   {bins CMD_READ_START   = {8'd1};
	    bins CMD_READ_MORE    = {8'd2};
		bins CMD_WRITE_START  = {8'd3};
		bins CMD_WRITE_MORE   = {8'd4};
		bins CMD_BUILD_WORD[] = {[8'hC0:8'hCF]};
		bins CMD_SEND_WORD[]  = {[8'h80:8'h8F]};	
	}  
	endgroup
 
	//Covering register addresses
	covergroup cg_reg_addr;
	option.per_instance = 1;
	cover_reg_addresses: coverpoint pkt.regAddr
	{option.auto_bin_max = 16;}
	endgroup
  
    function new(string name, uvm_component parent);
	  super.new(name, parent);
	  cg_buff = new();
	  cg_cmd  = new();
	  cg_reg_addr = new();
	endfunction
	
	function void write(input my_transaction t);
		pkt = t;
		cg_buff.sample();
		cg_cmd.sample();
		cg_reg_addr.sample();
	endfunction

	function void report_phase(uvm_phase phase);
		`uvm_info(get_type_name(),$sformatf("Coverage of Commands = %3.1f%%",cg_cmd.get_inst_coverage()),UVM_MEDIUM)
        `uvm_info(get_type_name(),$sformatf("Coverage of Buffer Addresses = %3.1f%%",cg_buff.get_inst_coverage()),UVM_MEDIUM)
		`uvm_info(get_type_name(),$sformatf("Coverage of Register Addresses = %3.1f%%",cg_reg_addr.get_inst_coverage()),UVM_MEDIUM)
	endfunction
	
 endclass: my_coverage
 
  
  class my_comparator extends uvm_component;
	
	`uvm_component_utils(my_comparator)
	
	uvm_analysis_export #(my_transaction) axp_in;
	uvm_analysis_export #(my_transaction) axp_out;
	uvm_tlm_analysis_fifo #(my_transaction) expfifo;
	uvm_tlm_analysis_fifo #(my_transaction) outfifo;
	my_transaction exp_tr, out_tr;
	
	
	function new (string name, uvm_component parent);
		super.new(name, parent);
	endfunction
	
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		axp_in  = new("axp_in", this);
		axp_out = new("axp_out", this);
		expfifo = new("expfifo", this);
		outfifo = new("outfifo", this);
		
	endfunction
	
	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
		axp_in.connect (expfifo.analysis_export);
		axp_out.connect(outfifo.analysis_export);
	endfunction

	task run_phase(uvm_phase phase);
		my_transaction exp_tr, out_tr;
		forever begin
			`uvm_info("my_comparator run task", "WAITING for expected output", UVM_DEBUG)
			expfifo.get(exp_tr);
			`uvm_info("my_comparator run task", "WAITING for actual output", UVM_DEBUG)
			outfifo.get(out_tr);
			if (out_tr.compare(exp_tr)) begin
				PASS();
				`uvm_info ("PASS", $sformatf("\n Actual  : %s  \n Expected: %s \n", out_tr.output2string(), exp_tr.convert2string()), UVM_LOW)
			end
			else begin
				ERROR();
				`uvm_error("ERROR", $sformatf("\n Actual  : %s \n Expected: %s \n", out_tr.output2string(), exp_tr.convert2string()))
			end
		end
	endtask
	
	int VECT_CNT, PASS_CNT, ERROR_CNT;
	
	function void report_phase(uvm_phase phase);
		super.report_phase(phase);
		if (VECT_CNT && !ERROR_CNT)
		`uvm_info(get_type_name(),$sformatf("\n\n\n*** ALL PASSED! - %0d vectors ran, %0d vectors passed ***\n",VECT_CNT, PASS_CNT), UVM_LOW)
		else
		`uvm_info(get_type_name(),$sformatf("\n\n\n*** TEST RESULT - %0d vectors ran, %0d vectors passed, %0d vectors failed ***\n",VECT_CNT, PASS_CNT, ERROR_CNT), UVM_LOW)
	endfunction
 
	function void PASS();
		VECT_CNT++;
		PASS_CNT++;
	endfunction
 
	function void ERROR();
		VECT_CNT++;
		ERROR_CNT++;
	endfunction
	
  endclass: my_comparator

  class my_predictor extends uvm_subscriber #(my_transaction);
	`uvm_component_utils(my_predictor)

	uvm_analysis_port #(my_transaction) results_ap;
	
	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction
 
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		results_ap = new("results_ap", this);
	endfunction
 
	function void write(my_transaction t);
		my_transaction exp_tr;
		exp_tr = my_calc_exp(t);
		results_ap.write(exp_tr);
	endfunction
 
	extern function my_transaction my_calc_exp(my_transaction t);

  endclass: my_predictor

  function my_transaction my_predictor::my_calc_exp(my_transaction t);
 
	logic [7:0]  rcMemData_out;
	bit   [7:0]  MISO_reg_out;
	static logic [11:0] next_rcMemAddr_out;
	static logic [11:0] next_txMemAddr_out=0;
	logic [11:0] txMemAddr_out;
	logic [11:0] rcMemAddr_out;
	static bit   [1:0] reg_index=0;
	static logic [31:0]reg_Write_Data;
	static logic [3:0] reg_Addr_out;
	
	my_transaction tr = my_transaction::type_id::create("tr");
	`uvm_info(get_type_name(), t.convert2string(), UVM_HIGH)
	
	txMemAddr_out = next_txMemAddr_out;
	rcMemAddr_out = next_rcMemAddr_out;
	
	///*** Outputs Prediction ***///
	
	//STATE_GET_CMD
	if(t.get_cmnd) begin
		rcMemData_out = t.cmnd;
		tr.rcMemAddr = rcMemAddr_out;
		next_rcMemAddr_out = 0;
		if(t.cmnd == 8'h03 || t.cmnd[7:6] == 2'b11) next_txMemAddr_out = 0; 
		MISO_reg_out = (t.SPI_MISO == 1 ? 8'hff : 8'h00);
	
	//STATE_READING
	end	else if(t.cmnd == 8'h01 || t.cmnd == 8'h02) begin 
		rcMemData_out = t.data_in_temp;
		next_rcMemAddr_out++;
		tr.rcMemAddr = next_rcMemAddr_out;
		MISO_reg_out = 8'h00;
		next_txMemAddr_out = txMemAddr_out;
	
	//STATE_WRITING
	end	else if(t.cmnd == 8'h03 || t.cmnd == 8'h04) begin
		rcMemData_out = t.data_in_temp;
		next_txMemAddr_out++; 
		if(t.get_cmnd) MISO_reg_out = (t.SPI_MISO == 1 ? 8'hff : 8'h00);
		else MISO_reg_out = t.txMemData;
		  
	//STATE_BUILD_WORD
	end else if (t.cmnd[7:6] == 2'b11) begin
		rcMemData_out = t.data_in_temp;
		reg_Addr_out = t.cmnd & 8'h0F;
		if (reg_index == 0) begin
			reg_Write_Data[31:24] = t.data_in_temp;
			reg_index++;
		  end else if (reg_index == 1) begin
			reg_Write_Data[23:16] = t.data_in_temp;
			reg_index++;
		  end else if (reg_index == 2) begin
			reg_Write_Data[15:8] = t.data_in_temp;
			reg_index++;
		  end else if (reg_index == 3) begin
			reg_Write_Data[7:0] = t.data_in_temp;
			reg_index = 0;
			tr.regWriteData = reg_Write_Data;
		  end
		  
	//STATE_SEND_WORD
	end	else if(t.cmnd[7:6] == 2'b10) begin
		rcMemData_out = t.data_in_temp;
		next_txMemAddr_out++;
		reg_Addr_out = t.cmnd & 8'h0F;
		  if (reg_index == 0) begin
			MISO_reg_out = t.regReadData[31:24];
			reg_index++;
		  end else if (reg_index == 1) begin
			MISO_reg_out = t.regReadData[23:16];
			reg_index++;
		  end else if (reg_index == 2) begin
			MISO_reg_out = t.regReadData[15:8];
			reg_index++;
		  end else if (reg_index == 3) begin
			MISO_reg_out = t.regReadData[7:0];
			reg_index = 0;
		  end
	end
	
	//Copy all sampled inputs & outputs
	tr.copy(t);
	
	//Overwrite output values with the calculated ones
	tr.rcMemData = rcMemData_out;
	tr.MISO_reg  = MISO_reg_out;
	tr.txMemAddr = txMemAddr_out;
	tr.regAddr   = reg_Addr_out;
	
	return(tr);
  
  endfunction 
  
  class my_scoreboard  extends uvm_scoreboard;
	`uvm_component_utils(my_scoreboard)
	
	uvm_analysis_export #(my_transaction) axp_in;
	uvm_analysis_export #(my_transaction) axp_out;
	my_predictor prd;
	my_comparator cmp;
	
	function new(string name, uvm_component parent);
		super.new( name, parent );
	endfunction
	
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		axp_in = new("axp_in", this);
		axp_out = new("axp_out", this);
		prd = my_predictor::type_id::create("prd", this);
		cmp = my_comparator::type_id::create("cmp", this);
	endfunction
	
	function void connect_phase( uvm_phase phase );
		// Connect predictor & comparator to respective analysis exports
		axp_in.connect(prd.analysis_export);
		axp_out.connect(cmp.axp_out);
		// Connect predictor to comparator
		prd.results_ap.connect(cmp.axp_in);
	endfunction
  
  endclass: my_scoreboard


  class my_env         extends uvm_env;

    `uvm_component_utils(my_env)
    
	my_agent      m_agent;
	passive_agent p_agent;
	my_coverage   m_coverage;
	my_scoreboard m_scoreboard;
	
    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction
 
    function void build_phase(uvm_phase phase);
      m_agent      = my_agent::type_id::create("m_agent", this);
      p_agent      = passive_agent::type_id::create("p_agent", this);
	  m_coverage   = my_coverage::type_id::create("m_coverage", this);
	  m_scoreboard = my_scoreboard::type_id::create("my_scoreboard", this);
    endfunction
	
	function void connect_phase(uvm_phase phase);
      m_agent.analysis_port.connect(m_coverage.analysis_export);
      p_agent.p_analysis_port.connect(m_scoreboard.axp_in);
      m_agent.analysis_port.connect(m_scoreboard.axp_out);
    endfunction
	
  endclass: my_env
 
  class my_test        extends uvm_test;
  
    `uvm_component_utils(my_test)
    
    my_env m_env;
    my_sequence seq;
	
    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
      m_env = my_env::type_id::create("m_env", this);
    endfunction
    
	virtual function void end_of_elaboration_phase (uvm_phase phase);
		uvm_top.print_topology ();
	endfunction
	
	task run_phase(uvm_phase phase);
		//Initialize the system from the driver
		phase.raise_objection(this,"Start of initialization");
		`uvm_info("TEST","Start of initialization",UVM_LOW)
		#310;
		phase.drop_objection(this,"End of initialization");
		`uvm_info("TEST","End of initialization",UVM_LOW)
		
		//Start the sequence
        seq = my_sequence::type_id::create("seq");
        // seq.set_item_context(this,m_env.m_agent.m_seqr); //for randomization stability
		if(!seq.randomize())
  		  `uvm_error("", "Sequence Randomization failed")
        seq.starting_phase = phase;
        seq.start( m_env.m_agent.m_seqr); 
    endtask
	
  endclass: my_test

  
endpackage: my_pkg