# Aesop

This is a work-in-progress proof search tactic for Lean 4.

## Building

With [elan](https://github.com/leanprover/elan) installed, `leanpkg build`
should suffice.

## Usage

To use Aesop in a Lean 4 project, first add this package as a dependency. In
your `leanpkg.toml`, add

```toml
[dependencies]
aesop = { git = "https://github.com/JLimperg/aesop", rev = "<current HEAD commit of this repo>" }
```

Now run `leanpkg configure`. Unless you use the exact same Lean 4 nightly as
this project (see our `leanpkg.toml`), you'll get a warning. If you use a later
nightly, you'll probably be fine and Aesop will compile anyway. If not, please
open an issue and we'll update the tactic.

You should now be able to use the `aesop` tactic:

```lean
import Aesop

def id' : α → α :=
  by aesop
```

There is currently no documentation on the tactic and it is very work in
progress. If you have questions, please ping me (Jannis Limperg) on Zulip.

TODO Document how to use Aesop as a plugin.
