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

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"