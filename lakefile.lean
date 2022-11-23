import Lake

open Lake DSL

package aesop {
  precompileModules := true
}

@[default_target]
lean_lib Aesop {}

require std from git "https://github.com/leanprover/std4" @ "main"
