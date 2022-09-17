import Lake

open Lake DSL

package aesop {
  precompileModules := true
}

@[defaultTarget]
lean_lib Aesop {}

require std from git "https://github.com/leanprover/std4"
