import Lake

open Lake DSL

package aesop {
  precompileModules := false -- breaks mathlib cache
  moreLinkArgs := #["-L./lake-packages/LeanInfer/build/lib", "-lonnxruntime", "-lstdc++"]
}

@[default_target]
lean_lib Aesop

lean_lib AesopTest {
  globs := #[.submodules "AesopTest"]
}

require std from git "https://github.com/leanprover/std4" @ "main"
require LeanInfer from git "https://github.com/lean-dojo/LeanInfer.git" @ "v0.0.7"