import Lake
open Lake DSL

package «test_tesi» where
  -- add package configuration options here

require proofwidgets from git
  "https://github.com/leanprover-community/ProofWidgets4" @ "v0.0.60"

@[default_target]
lean_lib «TestTesi» where
  -- add library configuration options here
