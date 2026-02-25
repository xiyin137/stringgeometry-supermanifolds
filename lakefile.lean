import Lake
open Lake DSL

package "stringgeometry-supermanifolds" where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"


lean_lib SGSupermanifolds where
  roots := #[`StringGeometry.Supermanifolds]
