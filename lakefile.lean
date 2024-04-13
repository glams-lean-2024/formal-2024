import Lake
open Lake DSL

package Formal2024 {
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    -- ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]
}

lean_lib Library {
  srcDir:= "Tactics"
}

-- lean_lib «TruthTable» {
--  srcDir:= "Tactics"
-- }

lean_lib «MIL» {
  srcDir:= "References"
}

lean_lib «Tutorials» {
  srcDir:= "References"
}

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"
-- require Paperproof from git "https://github.com/Paper-Proof/paperproof.git"@"main"/"lean"
-- require autograder from git "https://github.com/robertylewis/lean4-autograder-main" @ "master"
-- require proofwidgets from git "https://github.com/EdAyers/ProofWidgets4"@"v0.0.28"

-- require std from git "https://github.com/leanprover/std4.git"

@[default_target]
lean_lib Formal2024 where -- {
-- globs := #[.submodules `Formal2024]
-- }
