./llvm/build/bin/FileCheck

./build/bin/circt-translate --import-verilog test/Conversion/ImportVerilog/basic.sv | ./llvm/build/bin/FileCheck test/Conversion/ImportVerilog/basic.sv


./llvm/build/bin/mlir-tblgen -gen-op-decls -I /home/chenbo/mega2024/circt/include -I /home/chenbo/mega2024/circt/llvm/mlir/include/  /home/chenbo/mega2024/circt/include/circt/Dialect/Moore/MooreOps.td > result.out

module {
  moore.module @Expressions() {
    %a = moore.variable : <i32>
    %b = moore.variable : <i32>
    %c = moore.variable : <i32>
    %d = moore.variable : <l32>
    %e = moore.variable : <l32>
    %f = moore.variable : <l32>
    moore.procedure initial {
      %0 = moore.concat_ref %a, %b, %c : (!moore.ref<i32>, !moore.ref<i32>, !moore.ref<i32>) -> <i96>
      %1 = moore.extract_ref %0 from 0 : <i96> -> <i8>
      %2 = moore.extract_ref %0 from 8 : <i96> -> <i8>
      %3 = moore.extract_ref %0 from 16 : <i96> -> <i8>
      %4 = moore.extract_ref %0 from 24 : <i96> -> <i8>
      %5 = moore.extract_ref %0 from 32 : <i96> -> <i8>
      %6 = moore.extract_ref %0 from 40 : <i96> -> <i8>
      %7 = moore.extract_ref %0 from 48 : <i96> -> <i8>
      %8 = moore.extract_ref %0 from 56 : <i96> -> <i8>
      %9 = moore.extract_ref %0 from 64 : <i96> -> <i8>
      %10 = moore.extract_ref %0 from 72 : <i96> -> <i8>
      %11 = moore.extract_ref %0 from 80 : <i96> -> <i8>
      %12 = moore.extract_ref %0 from 88 : <i96> -> <i8>
      %13 = moore.concat_ref %12, %11, %10, %9, %8, %7, %6, %5, %4, %3, %2, %1 : (!moore.ref<i8>, !moore.ref<i8>, !moore.ref<i8>, !moore.ref<i8>, !moore.ref<i8>, !moore.ref<i8>, !moore.ref<i8>, !moore.ref<i8>, !moore.ref<i8>, !moore.ref<i8>, !moore.ref<i8>, !moore.ref<i8>) -> <i96>
      %14 = moore.read %a : <i32>
      %15 = moore.read %b : <i32>
      %16 = moore.read %c : <i32>
      %17 = moore.concat %14, %15, %16 : (!moore.i32, !moore.i32, !moore.i32) -> i96
      %18 = moore.extract %17 from 0 : i96 -> i8
      %19 = moore.extract %17 from 8 : i96 -> i8
      %20 = moore.extract %17 from 16 : i96 -> i8
      %21 = moore.extract %17 from 24 : i96 -> i8
      %22 = moore.extract %17 from 32 : i96 -> i8
      %23 = moore.extract %17 from 40 : i96 -> i8
      %24 = moore.extract %17 from 48 : i96 -> i8
      %25 = moore.extract %17 from 56 : i96 -> i8
      %26 = moore.extract %17 from 64 : i96 -> i8
      %27 = moore.extract %17 from 72 : i96 -> i8
      %28 = moore.extract %17 from 80 : i96 -> i8
      %29 = moore.extract %17 from 88 : i96 -> i8
      %30 = moore.concat %29, %28, %27, %26, %25, %24, %23, %22, %21, %20, %19, %18 : (!moore.i8, !moore.i8, !moore.i8, !moore.i8, !moore.i8, !moore.i8, !moore.i8, !moore.i8, !moore.i8, !moore.i8, !moore.i8, !moore.i8) -> i96
      moore.blocking_assign %13, %30 : i96
      moore.return
    }
    moore.output
  }
}

./test/Conversion/ImportVerilog/concat.sv:64:5: note: see current operation: %9 = "moore.concat_ref"(%2, %5, %8) : (!moore.ref<i32>, !moore.ref<i32>, !moore.ref<i32>) -> !moore.ref<i96>


module {
  moore.module @Expressions() {
    moore.procedure initial {
      %j = moore.variable : <i32>
      %a = moore.variable : <i32>
      %b = moore.variable : <i32>
      %c = moore.variable : <i32>
      %up = moore.variable : <uarray<4 x l11>>
      %p1 = moore.variable : <l11>
      %p2 = moore.variable : <l11>
      %p3 = moore.variable : <l11>
      %p4 = moore.variable : <l11>
      %yy = moore.variable : <i96>
      %dd = moore.variable : <i100>
      %0 = moore.read %j : <i32>
      %1 = moore.concat %0 : (!moore.i32) -> i32
      moore.blocking_assign %j, %1 : i32
      %2 = moore.read %j : <i32>
      %3 = moore.concat %2 : (!moore.i32) -> i32
      %4 = moore.extract %3 from 0 : i32 -> i8
      %5 = moore.extract %3 from 8 : i32 -> i8
      %6 = moore.extract %3 from 16 : i32 -> i8
      %7 = moore.extract %3 from 24 : i32 -> i8
      %8 = moore.concat %7, %6, %5, %4 : (!moore.i8, !moore.i8, !moore.i8, !moore.i8) -> i32
      moore.blocking_assign %j, %8 : i32
      %9 = moore.read %j : <i32>
      %10 = moore.concat %9 : (!moore.i32) -> i32
      %11 = moore.extract %10 from 0 : i32 -> i16
      %12 = moore.extract %10 from 16 : i32 -> i16
      %13 = moore.concat %12, %11 : (!moore.i16, !moore.i16) -> i32
      moore.blocking_assign %j, %13 : i32
      %14 = moore.constant 53 : i8
      %15 = moore.concat %14 : (!moore.i8) -> i8
      %16 = moore.extract %15 from 0 : i8 -> i1
      %17 = moore.extract %15 from 1 : i8 -> i1
      %18 = moore.extract %15 from 2 : i8 -> i1
      %19 = moore.extract %15 from 3 : i8 -> i1
      %20 = moore.extract %15 from 4 : i8 -> i1
      %21 = moore.extract %15 from 5 : i8 -> i1
      %22 = moore.extract %15 from 6 : i8 -> i1
      %23 = moore.extract %15 from 7 : i8 -> i1
      %24 = moore.concat %23, %22, %21, %20, %19, %18, %17, %16 : (!moore.i1, !moore.i1, !moore.i1, !moore.i1, !moore.i1, !moore.i1, !moore.i1, !moore.i1) -> i8
      %25 = moore.conversion %24 : !moore.i8 -> !moore.i32
      moore.blocking_assign %j, %25 : i32
      %26 = moore.constant -11 : i6
      %27 = moore.concat %26 : (!moore.i6) -> i6
      %28 = moore.extract %27 from 0 : i6 -> i4
      %29 = moore.extract %27 from 4 : i6 -> i2
      %30 = moore.concat %29, %28 : (!moore.i2, !moore.i4) -> i6
      %31 = moore.conversion %30 : !moore.i6 -> !moore.i32
      moore.blocking_assign %j, %31 : i32
      %32 = moore.constant -11 : i6
      %33 = moore.concat %32 : (!moore.i6) -> i6
      %34 = moore.conversion %33 : !moore.i6 -> !moore.i32
      moore.blocking_assign %j, %34 : i32
      %35 = moore.constant -3 : i4
      %36 = moore.concat %35 : (!moore.i4) -> i4
      %37 = moore.extract %36 from 0 : i4 -> i1
      %38 = moore.extract %36 from 1 : i4 -> i1
      %39 = moore.extract %36 from 2 : i4 -> i1
      %40 = moore.extract %36 from 3 : i4 -> i1
      %41 = moore.concat %40, %39, %38, %37 : (!moore.i1, !moore.i1, !moore.i1, !moore.i1) -> i4
      %42 = moore.concat %41 : (!moore.i4) -> i4
      %43 = moore.extract %42 from 0 : i4 -> i2
      %44 = moore.extract %42 from 2 : i4 -> i2
      %45 = moore.concat %44, %43 : (!moore.i2, !moore.i2) -> i4
      %46 = moore.conversion %45 : !moore.i4 -> !moore.i32
      moore.blocking_assign %j, %46 : i32
      %47 = moore.read %a : <i32>
      %48 = moore.read %b : <i32>
      %49 = moore.read %c : <i32>
      %50 = moore.concat %47, %48, %49 : (!moore.i32, !moore.i32, !moore.i32) -> i96
      moore.blocking_assign %yy, %50 : i96
      %51 = moore.read %a : <i32>
      %52 = moore.read %b : <i32>
      %53 = moore.read %c : <i32>
      %54 = moore.concat %51, %52, %53 : (!moore.i32, !moore.i32, !moore.i32) -> i96
      %55 = moore.conversion %54 : !moore.i96 -> !moore.i100
      moore.blocking_assign %dd, %55 : i100
      %56 = moore.concat_ref %a, %b, %c : (!moore.ref<i32>, !moore.ref<i32>, !moore.ref<i32>) -> <i96>
      %57 = moore.constant 1 : i96
      moore.blocking_assign %56, %57 : i96
      %58 = moore.concat_ref %a, %b, %c : (!moore.ref<i32>, !moore.ref<i32>, !moore.ref<i32>) -> <i96>
      %59 = moore.constant 31 : i100
      %60 = moore.conversion %59 : !moore.i100 -> !moore.i96
      moore.blocking_assign %58, %60 : i96
      %61 = moore.concat_ref %p1, %p2, %p3, %p4 : (!moore.ref<l11>, !moore.ref<l11>, !moore.ref<l11>, !moore.ref<l11>) -> <l44>
      %62 = moore.read %up : <uarray<4 x l11>>
      %63 = moore.conversion %62 : !moore.uarray<4 x l11> -> !moore.l44
      moore.blocking_assign %61, %63 : l44
      moore.return
    }
    moore.output
  }
}
module {
  moore.module @Expressions() {
    moore.procedure initial {
      %j = moore.variable : <i32>
      %a = moore.variable : <i32>
      %b = moore.variable : <i32>
      %c = moore.variable : <i32>
      %up = moore.variable : <uarray<4 x l11>>
      %p1 = moore.variable : <l11>
      %p2 = moore.variable : <l11>
      %p3 = moore.variable : <l11>
      %p4 = moore.variable : <l11>
      %yy = moore.variable : <i96>
      %dd = moore.variable : <i100>
      %0 = moore.read %j : <i32>
      moore.blocking_assign %j, %0 : i32
      %1 = moore.read %j : <i32>
      moore.blocking_assign %j, %1 : i32
      %2 = moore.read %j : <i32>
      %3 = moore.extract %2 from 0 : i32 -> i8
      %4 = moore.extract %2 from 8 : i32 -> i8
      %5 = moore.extract %2 from 16 : i32 -> i8
      %6 = moore.extract %2 from 24 : i32 -> i8
      %7 = moore.concat %6, %5, %4, %3 : (!moore.i8, !moore.i8, !moore.i8, !moore.i8) -> i32
      moore.blocking_assign %j, %7 : i32
      %8 = moore.read %j : <i32>
      %9 = moore.extract %8 from 0 : i32 -> i16
      %10 = moore.extract %8 from 16 : i32 -> i16
      %11 = moore.concat %10, %9 : (!moore.i16, !moore.i16) -> i32
      moore.blocking_assign %j, %11 : i32
      %12 = moore.constant 53 : i8
      %13 = moore.extract %12 from 0 : i8 -> i1
      %14 = moore.extract %12 from 1 : i8 -> i1
      %15 = moore.extract %12 from 2 : i8 -> i1
      %16 = moore.extract %12 from 3 : i8 -> i1
      %17 = moore.extract %12 from 4 : i8 -> i1
      %18 = moore.extract %12 from 5 : i8 -> i1
      %19 = moore.extract %12 from 6 : i8 -> i1
      %20 = moore.extract %12 from 7 : i8 -> i1
      %21 = moore.concat %20, %19, %18, %17, %16, %15, %14, %13 : (!moore.i1, !moore.i1, !moore.i1, !moore.i1, !moore.i1, !moore.i1, !moore.i1, !moore.i1) -> i8
      %22 = moore.conversion %21 : !moore.i8 -> !moore.i32
      moore.blocking_assign %j, %22 : i32
      %23 = moore.constant -11 : i6
      %24 = moore.extract %23 from 0 : i6 -> i4
      %25 = moore.extract %23 from 4 : i6 -> i2
      %26 = moore.concat %25, %24 : (!moore.i2, !moore.i4) -> i6
      %27 = moore.conversion %26 : !moore.i6 -> !moore.i32
      moore.blocking_assign %j, %27 : i32
      %28 = moore.constant -11 : i6
      %29 = moore.conversion %28 : !moore.i6 -> !moore.i32
      moore.blocking_assign %j, %29 : i32
      %30 = moore.constant -3 : i4
      %31 = moore.extract %30 from 0 : i4 -> i1
      %32 = moore.extract %30 from 1 : i4 -> i1
      %33 = moore.extract %30 from 2 : i4 -> i1
      %34 = moore.extract %30 from 3 : i4 -> i1
      %35 = moore.concat %34, %33, %32, %31 : (!moore.i1, !moore.i1, !moore.i1, !moore.i1) -> i4
      %36 = moore.extract %35 from 0 : i4 -> i2
      %37 = moore.extract %35 from 2 : i4 -> i2
      %38 = moore.concat %37, %36 : (!moore.i2, !moore.i2) -> i4
      %39 = moore.conversion %38 : !moore.i4 -> !moore.i32
      moore.blocking_assign %j, %39 : i32
      %40 = moore.read %a : <i32>
      %41 = moore.read %b : <i32>
      %42 = moore.read %c : <i32>
      %43 = moore.concat %40, %41, %42 : (!moore.i32, !moore.i32, !moore.i32) -> i96
      moore.blocking_assign %yy, %43 : i96
      %44 = moore.read %a : <i32>
      %45 = moore.read %b : <i32>
      %46 = moore.read %c : <i32>
      %47 = moore.concat %44, %45, %46 : (!moore.i32, !moore.i32, !moore.i32) -> i96
      %48 = moore.conversion %47 : !moore.i96 -> !moore.i100
      moore.blocking_assign %dd, %48 : i100
      %49 = moore.concat_ref %a, %b, %c : (!moore.ref<i32>, !moore.ref<i32>, !moore.ref<i32>) -> <i96>
      %50 = moore.constant 1 : i96
      moore.blocking_assign %49, %50 : i96
      %51 = moore.concat_ref %a, %b, %c : (!moore.ref<i32>, !moore.ref<i32>, !moore.ref<i32>) -> <i96>
      %52 = moore.constant 31 : i100
      %53 = moore.conversion %52 : !moore.i100 -> !moore.i96
      moore.blocking_assign %51, %53 : i96
      %54 = moore.concat_ref %p1, %p2, %p3, %p4 : (!moore.ref<l11>, !moore.ref<l11>, !moore.ref<l11>, !moore.ref<l11>) -> <l44>
      %55 = moore.read %up : <uarray<4 x l11>>
      %56 = moore.conversion %55 : !moore.uarray<4 x l11> -> !moore.l44
      moore.blocking_assign %54, %56 : l44
      moore.return
    }
    moore.output
  }
}
module {
  moore.module @Expressions() {
    moore.procedure initial {
      %j = moore.variable : <i32>
      %a = moore.variable : <i32>
      %b = moore.variable : <i32>
      %c = moore.variable : <i32>
      %up = moore.variable : <uarray<4 x l11>>
      %p1 = moore.variable : <l11>
      %p2 = moore.variable : <l11>
      %p3 = moore.variable : <l11>
      %p4 = moore.variable : <l11>
      %yy = moore.variable : <i96>
      %dd = moore.variable : <i100>
      %0 = moore.read %j : <i32>
      moore.blocking_assign %j, %0 : i32
      %1 = moore.read %j : <i32>
      moore.blocking_assign %j, %1 : i32
      %2 = moore.read %j : <i32>
      %3 = moore.extract %2 from 0 : i32 -> i8
      %4 = moore.extract %2 from 8 : i32 -> i8
      %5 = moore.extract %2 from 16 : i32 -> i8
      %6 = moore.extract %2 from 24 : i32 -> i8
      %7 = moore.concat %6, %5, %4, %3 : (!moore.i8, !moore.i8, !moore.i8, !moore.i8) -> i32
      moore.blocking_assign %j, %7 : i32
      %8 = moore.read %j : <i32>
      %9 = moore.extract %8 from 0 : i32 -> i16
      %10 = moore.extract %8 from 16 : i32 -> i16
      %11 = moore.concat %10, %9 : (!moore.i16, !moore.i16) -> i32
      moore.blocking_assign %j, %11 : i32
      %12 = moore.constant 53 : i8
      %13 = moore.extract %12 from 0 : i8 -> i1
      %14 = moore.extract %12 from 1 : i8 -> i1
      %15 = moore.extract %12 from 2 : i8 -> i1
      %16 = moore.extract %12 from 3 : i8 -> i1
      %17 = moore.extract %12 from 4 : i8 -> i1
      %18 = moore.extract %12 from 5 : i8 -> i1
      %19 = moore.extract %12 from 6 : i8 -> i1
      %20 = moore.extract %12 from 7 : i8 -> i1
      %21 = moore.concat %20, %19, %18, %17, %16, %15, %14, %13 : (!moore.i1, !moore.i1, !moore.i1, !moore.i1, !moore.i1, !moore.i1, !moore.i1, !moore.i1) -> i8
      %22 = moore.conversion %21 : !moore.i8 -> !moore.i32
      moore.blocking_assign %j, %22 : i32
      %23 = moore.constant -11 : i6
      %24 = moore.extract %23 from 0 : i6 -> i4
      %25 = moore.extract %23 from 4 : i6 -> i2
      %26 = moore.concat %25, %24 : (!moore.i2, !moore.i4) -> i6
      %27 = moore.conversion %26 : !moore.i6 -> !moore.i32
      moore.blocking_assign %j, %27 : i32
      %28 = moore.constant -11 : i6
      %29 = moore.conversion %28 : !moore.i6 -> !moore.i32
      moore.blocking_assign %j, %29 : i32
      %30 = moore.constant -3 : i4
      %31 = moore.extract %30 from 0 : i4 -> i1
      %32 = moore.extract %30 from 1 : i4 -> i1
      %33 = moore.extract %30 from 2 : i4 -> i1
      %34 = moore.extract %30 from 3 : i4 -> i1
      %35 = moore.concat %34, %33, %32, %31 : (!moore.i1, !moore.i1, !moore.i1, !moore.i1) -> i4
      %36 = moore.extract %35 from 0 : i4 -> i2
      %37 = moore.extract %35 from 2 : i4 -> i2
      %38 = moore.concat %37, %36 : (!moore.i2, !moore.i2) -> i4
      %39 = moore.conversion %38 : !moore.i4 -> !moore.i32
      moore.blocking_assign %j, %39 : i32
      %40 = moore.read %a : <i32>
      %41 = moore.read %b : <i32>
      %42 = moore.read %c : <i32>
      %43 = moore.concat %40, %41, %42 : (!moore.i32, !moore.i32, !moore.i32) -> i96
      moore.blocking_assign %yy, %43 : i96
      %44 = moore.read %a : <i32>
      %45 = moore.read %b : <i32>
      %46 = moore.read %c : <i32>
      %47 = moore.concat %44, %45, %46 : (!moore.i32, !moore.i32, !moore.i32) -> i96
      %48 = moore.conversion %47 : !moore.i96 -> !moore.i100
      moore.blocking_assign %dd, %48 : i100
      %49 = moore.concat_ref %a, %b, %c : (!moore.ref<i32>, !moore.ref<i32>, !moore.ref<i32>) -> <i96>
      %50 = moore.constant 1 : i96
      moore.blocking_assign %49, %50 : i96
      %51 = moore.concat_ref %a, %b, %c : (!moore.ref<i32>, !moore.ref<i32>, !moore.ref<i32>) -> <i96>
      %52 = moore.constant 31 : i100
      %53 = moore.conversion %52 : !moore.i100 -> !moore.i96
      moore.blocking_assign %51, %53 : i96
      %54 = moore.concat_ref %p1, %p2, %p3, %p4 : (!moore.ref<l11>, !moore.ref<l11>, !moore.ref<l11>, !moore.ref<l11>) -> <l44>
      %55 = moore.read %up : <uarray<4 x l11>>
      %56 = moore.conversion %55 : !moore.uarray<4 x l11> -> !moore.l44
      moore.blocking_assign %54, %56 : l44
      moore.return
    }
    moore.output
  }
}


           530:  %55 = moore.extract %54 from 0 : i6 -> i4 
           531:  %56 = moore.extract %54 from 4 : i6 -> i2 
           532:  %57 = moore.concat %56, %55 : (!moore.i2, !moore.i4) -> i6 
           533:  %58 = moore.zext %57 : i6 -> i32 
           534:  moore.blocking_assign %a, %58 : i32 
           535:  %59 = moore.constant -11 : i6 
check:744'0                                   X error: no match found
check:744'1                                     with "VAL_28" equal to "59"
           536:  %60 = moore.zext %59 : i6 -> i32 
check:744'0     ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
moore.zext %[[VAL_28]] : i6 -> i32 