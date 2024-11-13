module streaming_pack();

//-------------------------------
// PACK Example
//-------------------------------
int j = { "A", "B", "C", "D" };

bit [31:0] stream;


// streaming_concatenation ::= { stream_operator [ slice_size ] stream_concatenation }
// stream_operator ::= >> | <<
// slice_size ::= simple_type | constant_expression
// stream_concatenation ::= { stream_expression { , stream_expression } }
// stream_expression ::= expression [ with [ array_range_expression ] ]
// array_range_expression ::=
// expression
// | expression : expression
// | expression +: expression
// | expression -: expression
// primary ::=
// ...
// | streaming_concatenation

initial begin
 $display("       PACK");
 $display("Value of j %0x",j);
//  $monitor("@%0dns stream value is %x",$time, stream);
//  stream = {32{1'b1}};
 stream = { << byte {j}}; 
 stream = { >> {j}} ;
 stream = { << { 8'b0011_0101 }};
 stream = { << 16 {j}}; 
 stream = { << 4 { 6'b11_0101 }};
 stream = { >> 4 { 6'b11_0101 }} ;
 stream = { << 2 { { << { 4'b1101 }} }};
end

endmodule
//-------------------------------
// UNPACK Example
//-------------------------------
module streaming_unpack();
int          a, b, c;
logic [10:0] up [3:0];
logic [11:1] p1, p2, p3, p4;
bit   [96:1] y;
int          j ;
bit   [99:0] d;

initial begin
  $display("       UNPACK");
  // Below line should give compile error
  // {>>{ a, b, c }} = 23'b1; 
  {>>{ a, b, c }} = 96'b1; 
  
  // $display("@%0dns a %x b %x c %x",$time,a,b,c);
  {>>{ a, b, c }} = 100'b1; 
  // $display("@%0dns a %x b %x c %x",$time,a,b,c);
  { >> {p1, p2, p3, p4}} = up; 
  // $display("@%0dns p1 %x p2 %x p3 %x p4 %x",$time,p1,p2,p3,p4);
  y = {>>{ a, b, c }};
  // $display("@%0dns y %x",$time,y);
  // Below line should give compile error
  //j = {>>{ a, b, c }};
  d = {>>{ a, b, c }};
  // $display("@%0dns d %x",$time,d);
end

endmodule