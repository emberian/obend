// FABulous's own simulation of the configured fabric against the Lean model.
// The fabric (eFPGA_top and its tiles, as `run_fab` generates them) is configured through its
// self-write port with the committed bitstream, exactly as FABulous's demo testbench does; then
// every cycle drives the input pins and compares the output pins with the vector file that
// `obend fabric vectors` writes from `Obend.Hardware.Fabulous.moduleRun iceStickMac8`
// (entry 2t: {rst, c, b, a}; entry 2t+1: mac_out expected before edge t).
// Pin k of the pin map is pad k' = 49 - k of eFPGA_top (tile X0Y(1 + k/2), BEL A for even k).
`timescale 1ps / 1ps
`default_nettype none
module mac8_fabric_tb ();
    wire [49:0] I_top;
    wire [49:0] T_top;
    reg  [49:0] O_top = 0;
    wire [99:0] A_cfg, B_cfg;
    reg         CLK = 1'b0;
    reg         resetn = 1'b1;
    reg         self_write_strobe = 1'b0;
    reg  [31:0] self_write_data = 32'b0;
    wire        com_active, receive_led;

    eFPGA_top top_i (
        .I_top(I_top), .T_top(T_top), .O_top(O_top), .A_config_C(A_cfg), .B_config_C(B_cfg),
        .CLK(CLK), .resetn(resetn), .SelfWriteStrobe(self_write_strobe), .SelfWriteData(self_write_data),
        .Rx(1'b1), .ComActive(com_active), .ReceiveLED(receive_led), .s_clk(1'b0), .s_data(1'b0)
    );

    localparam integer MAX_BITBYTES = 16384;
    localparam integer MAX_VEC = 4096;
    reg [7:0]  bitstream [0:MAX_BITBYTES-1];
    reg [63:0] vec [0:MAX_VEC-1];
    reg [2047:0] bitstream_hex_arg, vectors_arg;
    integer i, t, ncycles, errors, checked, nbytes;
    reg [15:0] got;
    reg [63:0] in_word;

    always #500000 CLK = (CLK === 1'b0);

    // pin k <- bit k of {mac_out(unused), rst, c, b, a}; pad index 49 - k
    task drive(input [63:0] w);
        integer k;
        begin
            for (k = 0; k < 33; k = k + 1) O_top[49 - k] = w[k];
        end
    endtask

    initial begin
        for (i = 0; i < MAX_BITBYTES; i = i + 1) bitstream[i] = 8'h00;
        if (!$value$plusargs("bitstream_hex=%s", bitstream_hex_arg)) begin $display("no +bitstream_hex"); $fatal; end
        if (!$value$plusargs("vectors=%s", vectors_arg)) begin $display("no +vectors"); $fatal; end
        if (!$value$plusargs("cycles=%d", ncycles)) begin $display("no +cycles"); $fatal; end
        if (!$value$plusargs("bitbytes=%d", nbytes)) nbytes = MAX_BITBYTES;
        $readmemh(bitstream_hex_arg, bitstream);
        $readmemh(vectors_arg, vec);
        #100; resetn = 1'b0; #10000; resetn = 1'b1; #10000;
        repeat (20) @(posedge CLK);
        #2500;
        for (i = 0; i < nbytes; i = i + 4) begin
            self_write_data <= {bitstream[i], bitstream[i+1], bitstream[i+2], bitstream[i+3]};
            repeat (2) @(posedge CLK);
            self_write_strobe <= 1'b1;
            @(posedge CLK);
            self_write_strobe <= 1'b0;
            repeat (2) @(posedge CLK);
        end
        repeat (10) @(posedge CLK);
        errors = 0; checked = 0;
        for (t = 0; t < ncycles; t = t + 1) begin
            @(negedge CLK);
            in_word = vec[2*t];
            drive(in_word);
            #250000;
            for (i = 0; i < 16; i = i + 1) got[i] = I_top[49 - (33 + i)];
            // cycle 0 is the first reset: the flops hold whatever configuration left them
            if (t > 0) begin
                checked = checked + 1;
                if (got !== vec[2*t+1][15:0]) begin
                    errors = errors + 1;
                    if (errors <= 10) $display("cycle %0d: fabric mac_out=%h lean=%h", t, got, vec[2*t+1][15:0]);
                end
                if (T_top[49 - 33] !== 1'b1) begin errors = errors + 1; $display("cycle %0d: mac_out[0] pad not driven", t); end
            end
        end
        $display("fabric-sim: cycles=%0d checked=%0d mismatches=%0d", ncycles, checked, errors);
        if (errors != 0) $fatal;
        $finish;
    end
endmodule
`resetall
