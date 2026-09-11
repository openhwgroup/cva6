module trigger_napot_test;
  import triggers_pkg::*;

  initial begin
    assert (napot_match32(32'h0000_0017, 32'h0000_0010));
    assert (napot_match32(32'h0000_0017, 32'h0000_001f));
    assert (!napot_match32(32'h0000_0017, 32'h0000_0020));
    assert (napot_match64(64'h0000_0000_8000_1007, 64'h0000_0000_8000_100f));
    assert (!napot_match64(64'h0000_0000_8000_1007, 64'h0000_0000_8000_1010));
    $finish;
  end
endmodule
