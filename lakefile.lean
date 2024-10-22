import Lake
open Lake DSL

package MatroidDecompositionTheoremVerification {
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`pp.structureInstances, false⟩, ⟨`linter.oldObtain, false⟩]
}

require "leanprover-community" / "mathlib" @ git "master"

@[default_target]
lean_lib MatroidDecompositionTheoremVerification {
  globs := #[.submodules `MatroidDecompositionTheoremVerification]
}
