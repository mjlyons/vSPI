//
// verifies that a variable matches its expected value 
// and displays it in hex
//
`define expect_h(name,expectedVal,actualVal) if ((expectedVal) !== (actualVal)) begin $display("[ERROR] %s expected='h%X actual='h%X", (name), (expectedVal), (actualVal)); $finish; end else begin $display("[PASS] %s='h%X", (name), (actualVal)); end

