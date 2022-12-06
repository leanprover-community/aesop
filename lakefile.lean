import Lake

open Lake DSL

package aesop {
  precompileModules := true
  preferReleaseBuild := true
  buildArchive? := "aesop"
  releaseRepo? := "https://github.com/JLimperg/aesop-nightlies"
}

@[default_target]
lean_lib Aesop

require std from git "https://github.com/leanprover/std4" @ "main"
