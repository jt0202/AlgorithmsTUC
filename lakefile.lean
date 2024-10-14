import Lake
open Lake DSL

package «AlgorithmsTUC» where
  -- add any package configuration options here


lean_lib «AlgorithmsTUC» {
  -- add library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"@"v4.10.0"
