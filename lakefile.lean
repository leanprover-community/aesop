import Lake

open Lake DSL

package aesop {
  precompileModules := false -- breaks mathlib cache
}

@[default_target]
lean_lib Aesop

lean_lib AesopTest {
  globs := #[.submodules `AesopTest]
  leanOptions := #[⟨`linter.unusedVariables, false⟩]
  -- moreServerOptions := #[⟨`linter.unusedVariables, false⟩]
}

require std from git "https://github.com/leanprover/std4" @ "main"
