import Lake

open Lake DSL

package aesop {
  precompileModules := false -- breaks mathlib cache
}

@[default_target]
lean_lib Aesop

lean_lib AesopTest {
  globs := #[.submodules "AesopTest"]
}

require std from git "https://github.com/leanprover/std4" @ "main"
