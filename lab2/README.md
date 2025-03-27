# RISCV Assembly Instruction Testing

To change what test is being tested, change line 44 of riscv_single.sv:
memfilename = {"(chosen test.memfile)"};

To test riscv_single.sv for instructions, change directory to the directory that riscv_single.sv is in. Then type 
"vsim -do riscv_single"

For a full test of the instructions we have, use the updated "test_hw.memfile". This is because we did not complete the
sb, sh, lb, lbu, lh, and lhu instructions. The updated file replaces the prior files with an "addi t6, t6, 0x0" instructions
since t6 is not used by the rest of the instructions.

We didn't make any other testing files because we were able to test whether the instructions worked using the waveform of the
test files in the "testing" folder.

# Implementing onto the FPGA Board

To implement the code onto the FPGA board:
1. Make sure that Dr. Stine's github for lab 2 is copied onto whatever system you are testing on. Our .xpr file was out of
   date, so Dr. Stine asked use his recent copy of github to get the .xpr that works.
2. Save "riscv_single_v.sv" and "setup.tcl" together into a differnt area of your files. (setup.tcl can be found in
   Dr. Stine's github)
4. Open a terminal. Change directory into "../ecen4243S25/lab2/lab2".
5. Type "vivado" into the terminal to open vivado.
6. Open a new project.
7. Go to a the Tcl Console.
8. Change directory to where "riscv_single.sv" and "setup.tcl" are stored.
9. Type "source setup.tcl" and let vivado load the project.
10. Once it is finished, open hardware manager.
11. Make sure the fpga board is turned on. Then, while holding BTN0, use Program Device in vivado.
12. Once it load the waveform, let go of BTN0 to show the given waveform.

The waveform given should look like waveform.jpg from the other given files.
