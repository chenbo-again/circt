module Expressions;
  initial begin
  
  int j;
  int a, b, c;
  logic up [44:0];
  logic [11:1] p1, p2, p3, p4;
  bit [96:1] yy;
  bit [99:0] dd;

  // // CHECK: [[TMP0:%.+]] = moore.read %j : <i32>
  // // CHECK: moore.blocking_assign %a, [[TMP0]] : i32
  // a = { >> {j}};
  // // CHECK: [[TMP1:%.+]] = moore.read %j : <i32>
  // // CHECK: [[TMP2:%.+]] = moore.extract [[TMP1]] from 0 : i32 -> i8
  // // CHECK: [[TMP3:%.+]] = moore.extract [[TMP1]] from 8 : i32 -> i8
  // // CHECK: [[TMP4:%.+]] = moore.extract [[TMP1]] from 16 : i32 -> i8
  // // CHECK: [[TMP5:%.+]] = moore.extract [[TMP1]] from 24 : i32 -> i8
  // // CHECK: [[TMP6:%.+]] = moore.concat [[TMP2]], [[TMP3]], [[TMP4]], [[TMP5]] : (!moore.i8, !moore.i8, !moore.i8, !moore.i8) -> i32
  // // CHECK: moore.blocking_assign %a, [[TMP6]] : i32
  // a = { << byte {j}};
  // // CHECK: [[TMP7:%.+]] = moore.read %j : <i32>
  // // CHECK: [[TMP8:%.+]] = moore.extract [[TMP7]] from 0 : i32 -> i16
  // // CHECK: [[TMP9:%.+]] = moore.extract [[TMP7]] from 16 : i32 -> i16
  // // CHECK: [[TMP10:%.+]] = moore.concat [[TMP8]], [[TMP9]] : (!moore.i16, !moore.i16) -> i32
  // // CHECK: moore.blocking_assign %a, [[TMP10]] : i32
  // a = { << 16 {j}};
  // // CHECK: [[TMP11:%.+]] = moore.constant 53 : i8
  // // CHECK: [[TMP12:%.+]] = moore.extract [[TMP11]] from 0 : i8 -> i1
  // // CHECK: [[TMP13:%.+]] = moore.extract [[TMP11]] from 1 : i8 -> i1
  // // CHECK: [[TMP14:%.+]] = moore.extract [[TMP11]] from 2 : i8 -> i1
  // // CHECK: [[TMP15:%.+]] = moore.extract [[TMP11]] from 3 : i8 -> i1
  // // CHECK: [[TMP16:%.+]] = moore.extract [[TMP11]] from 4 : i8 -> i1
  // // CHECK: [[TMP17:%.+]] = moore.extract [[TMP11]] from 5 : i8 -> i1
  // // CHECK: [[TMP18:%.+]] = moore.extract [[TMP11]] from 6 : i8 -> i1
  // // CHECK: [[TMP19:%.+]] = moore.extract [[TMP11]] from 7 : i8 -> i1
  // // CHECK: [[TMP20:%.+]] = moore.concat [[TMP12]], [[TMP13]], [[TMP14]], [[TMP15]], [[TMP16]], [[TMP17]], [[TMP18]], [[TMP19]] : (!moore.i1, !moore.i1, !moore.i1, !moore.i1, !moore.i1, !moore.i1, !moore.i1, !moore.i1) -> i8
  // // CHECK: [[TMP21:%.+]] = moore.zext [[TMP20]] : i8 -> i32
  // // CHECK: moore.blocking_assign %a, [[TMP21]] : i32
  // a = { << { 8'b0011_0101 }};
  // // CHECK: [[TMP22:%.+]] = moore.constant -11 : i6
  // // CHECK: [[TMP23:%.+]] = moore.extract [[TMP22]] from 0 : i6 -> i4
  // // CHECK: [[TMP24:%.+]] = moore.extract [[TMP22]] from 4 : i6 -> i2
  // // CHECK: [[TMP25:%.+]] = moore.concat [[TMP23]], [[TMP24]] : (!moore.i4, !moore.i2) -> i6
  // // CHECK: [[TMP26:%.+]] = moore.zext [[TMP25]] : i6 -> i32
  // // CHECK: moore.blocking_assign %a, [[TMP26]] : i32
  // a = { << 4 { 6'b11_0101 }};
  // // CHECK: [[TMP27:%.+]] = moore.constant -11 : i6
  // // CHECK: [[TMP28:%.+]] = moore.zext [[TMP27]] : i6 -> i32
  // // CHECK: moore.blocking_assign %a, [[TMP28]] : i32
  // a = { >> 4 { 6'b11_0101 }};
  // // CHECK: [[TMP29:%.+]] = moore.constant -3 : i4
  // // CHECK: [[TMP30:%.+]] = moore.extract [[TMP29]] from 0 : i4 -> i1
  // // CHECK: [[TMP31:%.+]] = moore.extract [[TMP29]] from 1 : i4 -> i1
  // // CHECK: [[TMP32:%.+]] = moore.extract [[TMP29]] from 2 : i4 -> i1
  // // CHECK: [[TMP33:%.+]] = moore.extract [[TMP29]] from 3 : i4 -> i1
  // // CHECK: [[TMP34:%.+]] = moore.concat [[TMP30]], [[TMP31]], [[TMP32]], [[TMP33]] : (!moore.i1, !moore.i1, !moore.i1, !moore.i1) -> i4
  // // CHECK: [[TMP35:%.+]] = moore.extract [[TMP34]] from 0 : i4 -> i2
  // // CHECK: [[TMP36:%.+]] = moore.extract [[TMP34]] from 2 : i4 -> i2
  // // CHECK: [[TMP37:%.+]] = moore.concat [[TMP35]], [[TMP36]] : (!moore.i2, !moore.i2) -> i4
  // // CHECK: [[TMP38:%.+]] = moore.zext [[TMP37]] : i4 -> i32
  // // CHECK: moore.blocking_assign %a, [[TMP38]] : i32
  // a = { << 2 { { << { 4'b1101 }} }};
  // // CHECK: [[TMP39:%.+]] = moore.read %a : <i32>
  // // CHECK: [[TMP40:%.+]] = moore.read %b : <i32>
  // // CHECK: [[TMP41:%.+]] = moore.read %c : <i32>
  // // CHECK: [[TMP42:%.+]] = moore.concat [[TMP39]], [[TMP40]], [[TMP41]] : (!moore.i32, !moore.i32, !moore.i32) -> i96
  // // CHECK: moore.blocking_assign %yy, [[TMP42]] : i96
  // yy = {>>{ a, b, c }};

  // // CHECK: [[TMP43:%.+]] = moore.read %a : <i32>
  // // CHECK: [[TMP44:%.+]] = moore.read %b : <i32>
  // // CHECK: [[TMP45:%.+]] = moore.read %c : <i32>
  // // CHECK: [[TMP46:%.+]] = moore.concat [[TMP43]], [[TMP44]], [[TMP45]] : (!moore.i32, !moore.i32, !moore.i32) -> i96
  // // CHECK: [[TMP47:%.+]] = moore.zext [[TMP46]] : i96 -> i100
  // // CHECK: moore.blocking_assign %dd, [[TMP47]] : i100
  // dd = {>>{ a, b, c }};
  // // CHECK: [[TMP48:%.+]] = moore.concat_ref %a, %b, %c : (!moore.ref<i32>, !moore.ref<i32>, !moore.ref<i32>) -> <i96>
  // // CHECK: [[TMP49:%.+]] = moore.constant 1 : i96
  // // CHECK: moore.blocking_assign [[TMP48]], [[TMP49]] : i96
  // {>>{ a, b, c }} = 96'b1;
  // // CHECK: [[TMP50:%.+]] = moore.concat_ref %a, %b, %c : (!moore.ref<i32>, !moore.ref<i32>, !moore.ref<i32>) -> <i96>
  // // CHECK: [[TMP51:%.+]] = moore.constant 31 : i100
  // // CHECK: [[TMP52:%.+]] = moore.trunc [[TMP51]] : i100 -> i96
  // // CHECK: moore.blocking_assign [[TMP50]], [[TMP52]] : i96
  // {>>{ a, b, c }} = 100'b11111;
  // // CHECK: [[TMP53:%.+]] = moore.concat_ref %p1, %p2, %p3, %p4 : (!moore.ref<l11>, !moore.ref<l11>, !moore.ref<l11>, !moore.ref<l11>) -> <l44>
  // // CHECK: [[TMP54:%.+]] = moore.read %up : <uarray<4 x l11>>
  // // CHECK: [[TMP55:%.+]] = moore.conversion [[TMP54]] : !moore.uarray<4 x l11> -> !moore.l44
  // // CHECK: moore.blocking_assign [[TMP53]], [[TMP55]] : l44
  // { >> {p1, p2, p3, p4}} = up;
  // // CHECK: [[TMP56:%.+]] = moore.extract_ref %a from 0 : <i32> -> <i8>
  // // CHECK: [[TMP57:%.+]] = moore.extract_ref %a from 8 : <i32> -> <i8>
  // // CHECK: [[TMP58:%.+]] = moore.extract_ref %a from 16 : <i32> -> <i8>
  // // CHECK: [[TMP59:%.+]] = moore.extract_ref %a from 24 : <i32> -> <i8>
  // // CHECK: [[TMP60:%.+]] = moore.concat_ref [[TMP59]], [[TMP58]], [[TMP57]], [[TMP56]] : (!moore.ref<i8>, !moore.ref<i8>, !moore.ref<i8>, !moore.ref<i8>) -> <i32>
  // // CHECK: [[TMP61:%.+]] = moore.constant 1 : i32
  // // CHECK: moore.blocking_assign [[TMP60]], [[TMP61]] : i32
  // {<< byte {a}} = 32'b1;
  { >> {p1, p2, p3, p4}} = up;
  // {>> {up with [43:0]}} = { >> {p1, p2, p3, p4}};
  end

endmodule

module Top;
initial begin
  
    logic [31:0] vec_1;
    logic [15:0] vec_3;

    logic arr_1 [63:0];


    // CHECK: %[[TMP1:.*]] = moore.read %vec_3 : <l16>
    // CHECK: %[[TMP2:.*]] = moore.read %arr_1 : <uarray<64 x l1>>
    // CHECK: %[[TMP3:.*]] = moore.extract %[[TMP2]] from 0 : uarray<64 x l1> -> uarray<16 x l1>
    // CHECK: %[[TMP4:.*]] = moore.conversion %[[TMP3]] : !moore.uarray<16 x l1> -> !moore.l16
    // CHECK: %[[TMP5:.*]] = moore.concat %[[TMP1]], %[[TMP4]] : (!moore.l16, !moore.l16) -> l32
    // CHECK: %[[TMP6:.*]] = moore.extract %[[TMP5]] from 0 : l32 -> l8
    // CHECK: %[[TMP7:.*]] = moore.extract %[[TMP5]] from 8 : l32 -> l8
    // CHECK: %[[TMP8:.*]] = moore.extract %[[TMP5]] from 16 : l32 -> l8
    // CHECK: %[[TMP9:.*]] = moore.extract %[[TMP5]] from 24 : l32 -> l8
    // CHECK: %[[TMP10:.*]] = moore.concat %[[TMP6]], %[[TMP7]], %[[TMP8]], %[[TMP9]] : (!moore.l8, !moore.l8, !moore.l8, !moore.l8) -> l32
    // CHECK: moore.blocking_assign %vec_1, %[[TMP10]] : l32
    vec_1 = {<<byte{vec_3, arr_1 with [15:0]}};
  
    // CHECK: %[[TMP1:.*]] = moore.extract_ref %arr_1 from 0 : <uarray<64 x l1>> -> <uarray<16 x l1>>
    // CHECK: %[[TMP2:.*]] = moore.conversion %[[TMP1]] : !moore.ref<uarray<16 x l1>> -> !moore.ref<l16>
    // CHECK: %[[TMP3:.*]] = moore.concat_ref %vec_3, %[[TMP2]] : (!moore.ref<l16>, !moore.ref<l16>) -> <l32>
    // CHECK: %[[TMP4:.*]] = moore.extract_ref %[[TMP3]] from 0 : <l32> -> <l8>
    // CHECK: %[[TMP5:.*]] = moore.extract_ref %[[TMP3]] from 8 : <l32> -> <l8>
    // CHECK: %[[TMP6:.*]] = moore.extract_ref %[[TMP3]] from 16 : <l32> -> <l8>
    // CHECK: %[[TMP7:.*]] = moore.extract_ref %[[TMP3]] from 24 : <l32> -> <l8>
    // CHECK: %[[TMP8:.*]] = moore.concat_ref %[[TMP4]], %[[TMP5]], %[[TMP6]], %[[TMP7]] : (!moore.ref<l8>, !moore.ref<l8>, !moore.ref<l8>, !moore.ref<l8>) -> <l32>
    // CHECK: %[[TMP9:.*]] = moore.read %vec_1 : <l32>
    // CHECK: moore.blocking_assign %[[TMP8]], %[[TMP9]] : l32
    {<<byte{vec_3, arr_1 with [15:0]}} = vec_1;
end

endmodule