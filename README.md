# Aesop

This is a work-in-progress proof search tactic for Lean 4.

## Building

1. Install [elan](https://github.com/leanprover/elan).
2. Build our fork of Lean 4. Aesop currently doesn't build with the official
   Lean 4 nightly releases.

   ```
   $ cd <some directory>
   $ git clone --depth 1 https://github.com/JLimperg/lean4-aesop
   $ cd lean4-aesop
   $ mkdir -p build/release
   $ cd build/release
   $ cmake ../..
   $ make -j<threads>
   ```

   See the [Lean 4 build
   nstructions](https://leanprover.github.io/lean4/doc/make/index.html) for
   details.
3. Register the fork with elan.

   ```
   # still in lean4-aesop/build/release>
   $ elan toolchain link lean4-aesop stage1
   $ cd <the directory containing this README>
   $ elan override set lean4-aesop
   ```
4. Now you should be able to build Aesop as usual.

   ```
   <still in the directory containing this README>
   leanpkg build
   ```
