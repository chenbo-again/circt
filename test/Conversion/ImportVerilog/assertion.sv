module tb;
  bit a, b, c, d;
  bit clk;


  initial begin
    for (int i = 0; i < 20; i++) begin
      @(posedge clk);
    end
  end

  sequence s_ab;
    a ##1 b;
  endsequence

  sequence s_cd;
    c ##2 d;
  endsequence

  property p_expr;
    @(posedge clk) s_ab ##1 s_cd;
  endproperty

  assert property (p_expr);
endmodule
