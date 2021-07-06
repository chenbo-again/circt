//===- HWModule.cpp - HW API pybind module --------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "DialectModules.h"

#include "circt-c/Dialect/HW.h"

#include "mlir-c/BuiltinAttributes.h"
#include "mlir/Bindings/Python/PybindAdaptors.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Support/raw_ostream.h"

#include "PybindUtils.h"
#include <mlir-c/Support.h>
#include <pybind11/pybind11.h>
#include <pybind11/pytypes.h>
#include <pybind11/stl.h>
namespace py = pybind11;

using namespace circt;
using namespace mlir::python::adaptors;

/// Populate the hw python module.
void circt::python::populateDialectHWSubmodule(py::module &m) {
  m.doc() = "HW dialect Python native extension";

  mlir_type_subclass(m, "ArrayType", hwTypeIsAArrayType)
      .def_classmethod("get",
                       [](py::object cls, MlirType elementType, intptr_t size) {
                         return cls(hwArrayTypeGet(elementType, size));
                       })
      .def_property_readonly(
          "element_type",
          [](MlirType self) { return hwArrayTypeGetElementType(self); })
      .def_property_readonly(
          "size", [](MlirType self) { return hwArrayTypeGetSize(self); });

  mlir_type_subclass(m, "StructType", hwTypeIsAStructType)
      .def_classmethod(
          "get",
          [](py::object cls, py::list pyFieldInfos) {
            llvm::SmallVector<HWStructFieldInfo> mlirFieldInfos;
            MlirContext ctx;

            // Since we're just passing string refs to the type constructor,
            // copy them into a temporary vector to give them all new addresses.
            llvm::SmallVector<llvm::SmallString<8>> names;
            for (size_t i = 0, e = pyFieldInfos.size(); i < e; ++i) {
              auto tuple = pyFieldInfos[i].cast<py::tuple>();
              auto type = tuple[1].cast<MlirType>();
              ctx = mlirTypeGetContext(type);
              names.emplace_back(tuple[0].cast<std::string>());
              mlirFieldInfos.push_back(HWStructFieldInfo{
                  mlirStringRefCreate(names[i].data(), names[i].size()), type});
            }
            return cls(hwStructTypeGet(ctx, mlirFieldInfos.size(),
                                       mlirFieldInfos.data()));
          })
      .def("get_field", [](MlirType self, std::string fieldName) {
        return hwStructTypeGetField(
            self, mlirStringRefCreateFromCString(fieldName.c_str()));
      });

  mlir_type_subclass(m, "TypeAliasType", hwTypeIsATypeAliasType)
      .def_classmethod("get",
                       [](py::object cls, std::string scope, std::string name,
                          MlirType innerType) {
                         return cls(hwTypeAliasTypeGet(
                             mlirStringRefCreateFromCString(scope.c_str()),
                             mlirStringRefCreateFromCString(name.c_str()),
                             innerType));
                       })
      .def_property_readonly(
          "canonical_type",
          [](MlirType self) { return hwTypeAliasTypeGetCanonicalType(self); })
      .def_property_readonly(
          "inner_type",
          [](MlirType self) { return hwTypeAliasTypeGetInnerType(self); })
      .def_property_readonly("name",
                             [](MlirType self) {
                               MlirStringRef cStr =
                                   hwTypeAliasTypeGetName(self);
                               return std::string(cStr.data, cStr.length);
                             })
      .def_property_readonly("scope", [](MlirType self) {
        MlirStringRef cStr = hwTypeAliasTypeGetScope(self);
        return std::string(cStr.data, cStr.length);
      });
}
