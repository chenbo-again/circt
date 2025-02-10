// CHECK-LABEL: moore.module @ConcurrentAssertion()
module ConcurrentAssertion();
  // CHECK: %a = moore.variable : <i1>
  bit a;
  // CHECK: %b = moore.variable : <l1>
  logic b;
  // CHECK: %clk = moore.net wire : <l1>  
  wire clk;
  // CHECK: moore.procedure always {
  // CHECK:   %0 = moore.read %a : <i1>
  // CHECK:   moore.assert.concurrent %0 i1
  // CHECK:   moore.return
  // CHECK: }  
  assert property(a);
  // CHECK: moore.procedure always {
  // CHECK:   %0 = moore.read %a : <i1>
  // CHECK:   moore.assume.concurrent %0 i1
  // CHECK:   moore.return
  // CHECK: }  
  assume property(a);
  // CHECK: moore.procedure always {
  // CHECK:   %0 = moore.read %a : <i1>
  // CHECK:   moore.cover.concurrent %0 i1
  // CHECK:   moore.return
  // CHECK: }
  cover property(a);
  // CHECK: moore.procedure always {
  // CHECK:   %0 = moore.read %a : <i1>
  // CHECK:   moore.cover.concurrent %0 i1
  // CHECK:   moore.return
  // CHECK: }
  cover sequence(a);
endmodule

// CHECK-LABEL: moore.module @BooleanAssertionExpression()
module BooleanAssertionExpression();
  wire clk;
  bit a;
  logic b;
  bit [31:0] c;
  logic [31:0] d;
  
  // CHECK: moore.procedure always {
  // CHECK:   %0 = moore.read %b : <l1>
  // CHECK:   %1 = moore.logic_to_bit %0 : l1 -> i1
  // CHECK:   moore.assert.concurrent %1 i1
  // CHECK:   moore.return
  // CHECK: }  
  assert property(b);
  // CHECK: moore.procedure always {
  // CHECK:   %0 = moore.read %c : <i32>
  // CHECK:   %1 = moore.bool_cast %0 : i32 -> i1
  // CHECK:   moore.assert.concurrent %1 i1
  // CHECK:   moore.return
  // CHECK: }
  assert property(c);
  // CHECK: moore.procedure always {
  // CHECK:   %0 = moore.read %d : <l32>
  // CHECK:   %1 = moore.bool_cast %0 : l32 -> l1
  // CHECK:   %2 = moore.logic_to_bit %1 : l1 -> i1
  // CHECK:   moore.assert.concurrent %2 i1
  // CHECK:   moore.return
  // CHECK: }
  assert property(d);
endmodule


// CHECK-LABEL: moore.module @DeclaringProperty()
module DeclaringProperty();
  // CHECK: %clk = moore.net wire : <l1>
  // CHECK: %a = moore.variable : <i1>
  wire clk;
  bit a, b, c;

  sequence s1;
    a;
  endsequence

  sequence s2(x, y, z);
    x;
  endsequence

  sequence s3(bit x, bit y, bit z);
    x;
  endsequence

  sequence s4;
    bit local_var = a;
    local_var;
  endsequence

  property p1;
    a;
  endproperty

  // CHECK: moore.procedure always {
  // CHECK:   %0 = moore.read %a : <i1>
  // CHECK:   moore.assert.concurrent %0 i1
  // CHECK:   moore.return
  // CHECK: }
  assert property(s1);

  // CHECK: moore.procedure always {
  // CHECK:   %0 = moore.read %a : <i1>
  // CHECK:   moore.assert.concurrent %0 i1
  // CHECK:   moore.return
  // CHECK: }
  assert property(s2(a, b, c));

  // CHECK: moore.procedure always {
  // CHECK:   %0 = moore.read %a : <i1>
  // CHECK:   moore.assert.concurrent %0 i1
  // CHECK:   moore.return
  // CHECK: }
  assert property(s3(a, b, c));

  // CHECK: moore.procedure always {
  // CHECK:   %0 = moore.assertion_instance "s4" {
  // CHECK:     %1 = moore.read %a : <i1>
  // CHECK:     %local_var = moore.variable %1 : <i1>
  // CHECK:     %2 = moore.read %local_var : <i1>
  // CHECK:     moore.lemma %2 : i1
  // CHECK:   } : sequence
  // CHECK:   moore.assert.concurrent %0 sequence
  // CHECK:   moore.return
  // CHECK: }
  assert property(s4);

  // CHECK: moore.procedure always {
  // CHECK:   %0 = moore.read %a : <i1>
  // CHECK:   moore.assert.concurrent %0 i1
  // CHECK:   moore.return
  // CHECK: }
  assert property(p1);
endmodule

// CHECK-LABEL: moore.module @ClockAndDisableAssertion()
module ClockAndDisableAssertion();
  wire clk, rst;
  bit a;
  
  // CHECK: moore.procedure always {
  // CHECK:   %0 = moore.read %a : <i1>
  // CHECK:   %1 = moore.read %clk : <l1>
  // CHECK:   %2 = moore.int.ltl.clock %0, posedge %1 : (!moore.i1, !moore.l1) -> !moore.i1
  // CHECK:   moore.assert.concurrent %2 i1
  // CHECK:   moore.return
  // CHECK: }
  assert property(@(posedge clk) a);
  // CHECK: moore.procedure always {
  // CHECK:   %0 = moore.read %a : <i1>
  // CHECK:   %1 = moore.read %clk : <l1>
  // CHECK:   %2 = moore.int.ltl.clock %0, negedge %1 : (!moore.i1, !moore.l1) -> !moore.i1
  // CHECK:   moore.assert.concurrent %2 i1
  // CHECK:   moore.return
  // CHECK: }
  assert property(@(negedge clk) a);
  // CHECK: moore.procedure always {
  // CHECK:   %0 = moore.read %a : <i1>
  // CHECK:   %1 = moore.read %clk : <l1>
  // CHECK:   %2 = moore.int.ltl.clock %0, any %1 : (!moore.i1, !moore.l1) -> !moore.i1
  // CHECK:   moore.assert.concurrent %2 i1
  // CHECK:   moore.return
  // CHECK: }
  assert property(@(clk) a);
  // CHECK: moore.procedure always {
  // CHECK:   %0 = moore.read %rst : <l1>
  // CHECK:   %1 = moore.read %a : <i1>
  // CHECK:   %2 = moore.int.ltl.disable %1, %0 : (!moore.i1, !moore.l1) -> !moore.property
  // CHECK:   %3 = moore.read %clk : <l1>
  // CHECK:   %4 = moore.int.ltl.clock %2, posedge %3 : (!moore.property, !moore.l1) -> !moore.property
  // CHECK:   moore.assert.concurrent %4 property
  // CHECK:   moore.return
  // CHECK: }
  assert property(@(posedge clk) disable iff (rst) a);
endmodule

// CHECK-LABEL: moore.module @SequenceOperation()
module SequenceOperation();
  bit a, b, c;
  // CHECK: %0 = moore.read %a : <i1>
  // CHECK: %1 = moore.int.ltl.delay %0, 2, 0 : (!moore.i1) -> !moore.sequence
  assert property (##2 a);
  // CHECK: %0 = moore.read %a : <i1>
  // CHECK: %1 = moore.int.ltl.delay %0, 2, 1 : (!moore.i1) -> !moore.sequence
  assert property (##[2:3] a);
  // CHECK: %0 = moore.read %a : <i1>
  // CHECK: %1 = moore.int.ltl.delay %0, 2 : (!moore.i1) -> !moore.sequence
  assert property (##[2:$] a);
  // CHECK: %0 = moore.read %a : <i1>
  // CHECK: %1 = moore.int.ltl.delay %0, 0 : (!moore.i1) -> !moore.sequence
  assert property (##[*] a);
  // CHECK: %0 = moore.read %a : <i1>
  // CHECK: %1 = moore.int.ltl.delay %0, 1 : (!moore.i1) -> !moore.sequence
  assert property (##[+] a);
  // CHECK: %0 = moore.read %a : <i1>
  // CHECK: %1 = moore.read %b : <i1>
  // CHECK: %2 = moore.int.ltl.delay %1, 2, 0 : (!moore.i1) -> !moore.sequence
  // CHECK: %3 = moore.int.ltl.concat %0, %2 : (!moore.i1, !moore.sequence) -> !moore.sequence
  assert property (a ##2 b);
  // CHECK: %0 = moore.read %a : <i1>
  // CHECK: %1 = moore.read %b : <i1>
  // CHECK: %2 = moore.int.ltl.delay %1, 0 : (!moore.i1) -> !moore.sequence
  // CHECK: %3 = moore.int.ltl.concat %0, %2 : (!moore.i1, !moore.sequence) -> !moore.sequence
  // CHECK: %4 = moore.read %c : <i1>
  // CHECK: %5 = moore.int.ltl.delay %4, 2, 1 : (!moore.i1) -> !moore.sequence
  // CHECK: %6 = moore.int.ltl.concat %3, %5 : (!moore.sequence, !moore.sequence) -> !moore.sequence
  assert property (a ##[*] b ##[2:3] c);
  // CHECK: %0 = moore.read %a : <i1>
  // CHECK: %1 = moore.int.ltl.repeat %0, 2, 0 : (!moore.i1) -> !moore.sequence
  assert property (a[*2]);
  // CHECK: %0 = moore.read %a : <i1>
  // CHECK: %1 = moore.int.ltl.repeat %0, 2, 1 : (!moore.i1) -> !moore.sequence
  assert property (a[*2:3]);
  // CHECK: %0 = moore.read %a : <i1>
  // CHECK: %1 = moore.int.ltl.repeat %0, 2 : (!moore.i1) -> !moore.sequence
  assert property (a[*2:$]);
  // CHECK: %0 = moore.read %a : <i1>
  // CHECK: %1 = moore.int.ltl.repeat %0, 0 : (!moore.i1) -> !moore.sequence
  assert property (b ##0 a[*]);
  // CHECK: %0 = moore.read %a : <i1>
  // CHECK: %1 = moore.int.ltl.repeat %0, 1 : (!moore.i1) -> !moore.sequence
  assert property (a[+]);
  // CHECK: %0 = moore.read %a : <i1>
  // CHECK: %1 = moore.int.ltl.goto_repeat %0, 2, 1 : (!moore.i1) -> !moore.sequence
  assert property (a[->2:3]);
  // CHECK: %0 = moore.read %a : <i1>
  // CHECK: %1 = moore.int.ltl.non_consecutive_repeat %0, 2, 1 : (!moore.i1) -> !moore.sequence
  assert property (a[=2:3]);
  // CHECK: %2 = moore.int.ltl.repeat %0, 0 : (!moore.i1) -> !moore.sequence
  // CHECK: %3 = moore.int.ltl.intersect %2, %1 : (!moore.sequence, !moore.i1) -> !moore.sequence
  assert property (a throughout b);
  // CHECK: %0 = moore.read %a : <i1>
  // CHECK: %1 = moore.read %b : <i1>
  // CHECK: %2 = moore.constant 1 : i1
  // CHECK: %3 = moore.int.ltl.repeat %2, 0 : (!moore.i1) -> !moore.sequence
  // CHECK: %4 = moore.int.ltl.concat %0, %3 : (!moore.i1, !moore.sequence) -> !moore.sequence
  // CHECK: %5 = moore.int.ltl.concat %3, %4 : (!moore.sequence, !moore.sequence) -> !moore.sequence
  // CHECK: %6 = moore.int.ltl.intersect %5, %1 : (!moore.sequence, !moore.i1) -> !moore.sequence  
  assert property (a within b);
  // CHECK: %2 = moore.int.ltl.intersect %0, %1 : (!moore.i1, !moore.i1) -> !moore.property
  assert property (a intersect b);
endmodule

// CHECK-LABEL: moore.module @PropertyOperation()
module PropertyOperation();
  bit a, b, c;
  // CHECK: %0 = moore.read %a : <i1>
  // CHECK: %1 = moore.int.ltl.not %0 : (!moore.i1) -> !moore.i1
  assert property(not a);
  // CHECK: %0 = moore.read %a : <i1>
  // CHECK: %1 = moore.read %b : <i1>
  // CHECK: %2 = moore.int.ltl.and %0, %1 : (!moore.i1, !moore.i1) -> !moore.property
  // CHECK: %3 = moore.int.ltl.not %0 : (!moore.i1) -> !moore.i1
  // CHECK: %4 = moore.int.ltl.not %1 : (!moore.i1) -> !moore.i1
  // CHECK: %5 = moore.int.ltl.and %3, %4 : (!moore.i1, !moore.i1) -> !moore.property
  // CHECK: %6 = moore.int.ltl.or %2, %5 : (!moore.property, !moore.property) -> !moore.property
  assert property(a iff b);
  // CHECK: %0 = moore.read %a : <i1>
  // CHECK: %1 = moore.read %b : <i1>
  // CHECK: %2 = moore.int.ltl.until %0, %1 : (!moore.i1, !moore.i1) -> !moore.property
  assert property(a until b);
  // CHECK: %0 = moore.read %a : <i1>
  // CHECK: %1 = moore.read %b : <i1>
  // CHECK: %2 = moore.int.ltl.until %0, %1 : (!moore.i1, !moore.i1) -> !moore.property
  assert property(a s_until b);
  // CHECK: %0 = moore.read %a : <i1>
  // CHECK: %1 = moore.read %b : <i1>
  // CHECK: %2 = moore.int.ltl.until %0, %1 : (!moore.i1, !moore.i1) -> !moore.property
  // CHECK: %3 = moore.int.ltl.and %0, %1 : (!moore.i1, !moore.i1) -> !moore.property
  // CHECK: %4 = moore.int.ltl.implication %2, %3 : (!moore.property, !moore.property) -> !moore.property
  assert property(a until_with b);
  // CHECK: %0 = moore.read %a : <i1>
  // CHECK: %1 = moore.read %b : <i1>
  // CHECK: %2 = moore.int.ltl.until %0, %1 : (!moore.i1, !moore.i1) -> !moore.property
  // CHECK: %3 = moore.int.ltl.and %0, %1 : (!moore.i1, !moore.i1) -> !moore.property
  // CHECK: %4 = moore.int.ltl.implication %2, %3 : (!moore.property, !moore.property) -> !moore.property
  assert property(a s_until_with b);
  // CHECK: %0 = moore.read %a : <i1>
  // CHECK: %1 = moore.read %b : <i1>
  // CHECK: %2 = moore.int.ltl.not %0 : (!moore.i1) -> !moore.i1
  // CHECK: %3 = moore.int.ltl.or %2, %1 : (!moore.i1, !moore.i1) -> !moore.property
  assert property(a implies b);
  // CHECK: %0 = moore.read %a : <i1>
  // CHECK: %1 = moore.read %b : <i1>
  // CHECK: %2 = moore.int.ltl.implication %0, %1 : (!moore.i1, !moore.i1) -> !moore.property
  assert property(a |-> b);
  // CHECK: %0 = moore.read %a : <i1>
  // CHECK: %1 = moore.read %b : <i1>
  // CHECK: %2 = moore.int.ltl.delay %1, 1, 0 : (!moore.i1) -> !moore.property
  // CHECK: %3 = moore.int.ltl.implication %0, %2 : (!moore.i1, !moore.property) -> !moore.property
  assert property(a |=> b);
  // CHECK: %0 = moore.read %a : <i1>
  // CHECK: %1 = moore.read %b : <i1>
  // CHECK: %2 = moore.int.ltl.not %1 : (!moore.i1) -> !moore.i1
  // CHECK: %3 = moore.int.ltl.implication %0, %2 : (!moore.i1, !moore.i1) -> !moore.property
  // CHECK: %4 = moore.int.ltl.not %3 : (!moore.property) -> !moore.property
  assert property(a #-# b);
  // CHECK: %0 = moore.read %a : <i1>
  // CHECK: %1 = moore.read %b : <i1>
  // CHECK: %2 = moore.int.ltl.not %1 : (!moore.i1) -> !moore.i1
  // CHECK: %3 = moore.int.ltl.delay %2, 1, 0 : (!moore.i1) -> !moore.sequence
  // CHECK: %4 = moore.int.ltl.implication %0, %3 : (!moore.i1, !moore.sequence) -> !moore.property
  // CHECK: %5 = moore.int.ltl.not %4 : (!moore.property) -> !moore.property
  assert property(a #=# b);
  // CHECK: %0 = moore.read %a : <i1>
  // CHECK: %1 = moore.int.ltl.eventually %0 : (!moore.i1) -> !moore.property
  assert property(s_eventually a);
  // CHECK: %0 = moore.read %a : <i1>
  // CHECK: %1 = moore.read %b : <i1>
  // CHECK: %2 = moore.int.ltl.and %0, %1 : (!moore.i1, !moore.i1) -> !moore.i1
  assert property(a and b);
  // CHECK: %0 = moore.read %a : <i1>
  // CHECK: %1 = moore.read %b : <i1>
  // CHECK: %2 = moore.int.ltl.or %0, %1 : (!moore.i1, !moore.i1) -> !moore.i1
  assert property(a or b);

endmodule