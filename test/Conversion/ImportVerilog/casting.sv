module errors();
  // Illegal conversion from 24-bit struct to 32 bit int - compile time error
  struct {bit[7:0] a; shortint b;} a0;
  int b0 = int'(a0);
  // Illegal conversion from 20-bit struct to int (32 bits) - run time error
  struct {bit a[$]; shortint b;} a1 = {{1,2,3,4}, 67};
  int b1 = int'(a1);
  // Illegal conversion from int (32 bits) to struct dest_t (25 or 33 bits),
  // compile time error
  typedef struct {byte a[$]; bit b;} dest_t;
  int a2;
  dest_t b2 = dest_t'(a2);

endmodule