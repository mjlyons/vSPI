#vlib work
#vlog +acc DUT.sv  spiifc_tb_rc.sv rcMem_SVA.sv
#.main clear
vsim -voptargs=\"+acc\" work.top -assertdebug
