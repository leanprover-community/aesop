# Aesop-LeanInfer

Aesop-LeanInfer is an enhanced version of [Aesop](https://github.com/JLimperg/aesop) (Automated Extensible Search for Obvious Proofs), a proof search tactic for Lean 4 similar to Isabelle's `auto`. In addition to the original Aesop, this version adds a new `RuleBuilder` and its corresponding `RuleTac`, which together enable fast plugin of machine learning models to assist with the proof search process, by seamlessly incorporating [LeanInfer](https://github.com/lean-dojo/LeanInfer)'s tactic suggestion feature into Aesop's workflow. 

This tool is in its alpha stage and we are actively working to further enhance it. It is based on an early version of LeanInfer, which will be enriched in the near future. We aim to always keep this tool updated with the latest LeanInfer and have it support more variations in machine learning models of choice and accompanying features.

## Requirements

* Supported platforms: Linux and macOS (:warning: maybe also Windows WSL, but untested)
* [elan](https://github.com/leanprover/elan)
* [Git LFS](https://git-lfs.com/)

## Building

A direct `lake build` in this directory should suffice. 

To quickly test its success, write a simple theorem and try to prove it `by aesop`. If the goal is closed (i.e., `No goals` displayed in the InfoView), `aesop` is likely to have been properly built. Then replace `by aesop` with `by suggest_tactics`. If a list of tactics is shown under `Tactic suggestions` in the InfoView while the goal is not closed, the LeanInfer part is successfully built as well. For the first time, should it ask you to download the model by running `suggest_tactics!`, following it will automatically download the model to `~/.cache/lean_infer/` by default, with the path overridable by setting the `LEAN_INFER_CACHE_DIR` environment variable. A simple guide of this testing process is available [here](./AesopTest/NeuralCheck.lean) as well.

## Usage

Users can opt to add a new rule that calls a pre-trained machine learning model under the hood, by simply defining a structure consisting of a model name and a set of hyperparameters (all optional, if any of them is not specified by the users, built-in default settings automatically apply), and then annotating it with our new rule builder `neural`. See [here](./AesopTest/NeuralProver.lean) for a quick example where the model is specified by the user while hyperparameters are not (thus inheriting the default settings).

Note that we always allow the users to choose using the machine learning power or not, as it can be easily turned on/off by adding such a new rule or sticking to the raw Aesop. 

## Questions and Bugs

* For general questions and discussions, please use [GitHub Discussions](https://github.com/Peiyang-Song/aesop/discussions).  
* To report a potential bug, please open an issue. In the issue, please include your OS information and the exact steps to reproduce the error. The more details you provide, the better we will be able to help you.

## Related Links

* [LeanDojo Website](https://leandojo.org/)
* [LeanInfer](https://github.com/lean-dojo/LeanInfer)
* [LeanDojo](https://github.com/lean-dojo/LeanDojo) 
* [ReProver](https://github.com/lean-dojo/ReProver)
* [Aesop](https://github.com/JLimperg/aesop)

## Acknowledgements

* We thank [Jannis Limperg](https://limperg.de/) for insightful discussions regarding the integration of Aesop and LeanInfer.
