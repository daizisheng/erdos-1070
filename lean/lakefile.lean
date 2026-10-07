import Lake
open Lake DSL

package Erdos1070 where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

/-- Verbatim copy of the import closure of OpenAI's five-colour theorem (openai/math @ adc7f12). -/
lean_lib OAI where
  globs := #[.andSubmodules `OAI]

@[default_target]
lean_lib Erdos1070 where
  roots := #[`Erdos1070]
