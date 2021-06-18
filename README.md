# Aesop

This is a work-in-progress proof search tactic for Lean 4.

## Building

1. Install [elan](https://github.com/leanprover/elan).
2. Build our fork of Lean 4. Aesop currently doesn't build with the official
   Lean 4 nightly releases. Let `ROOT` be the directory containing this README.

   ```
   $ cd ROOT
   $ git submodule init
   $ git submodule update
   $ cd lean4-aesop # ROOT/lean4-aesop
   $ mkdir -p build/release
   $ cd build/release # ROOT/lean4-aesop/build/release
   $ cmake ../..
   $ make -j<threads>
   ```

   See the [Lean 4 build
   nstructions](https://leanprover.github.io/lean4/doc/make/index.html) for
   details.
3. Register the fork with elan.

   ```
   # still in ROOT/lean4-aesop/build/release
   $ elan toolchain link lean4-aesop stage1
   $ elan toolchain link lean4-aesop-stage0 stage0
   $ cd ../.. # ROOT/lean4-aesop
   $ elan override set lean4-aesop
   $ cd src # ROOT/lean4-aesop/src
   $ elan override set lean4-stage0
   $ cd ../.. # ROOT
   $ elan override set lean4-aesop
   ```
4. Now you should be able to build Aesop as usual.

   ```
   leanpkg build
   ```
