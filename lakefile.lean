import Lake

open Lake DSL

package aesop {
  precompileModules := true
}

@[defaultTarget]
lean_lib Aesop {}
