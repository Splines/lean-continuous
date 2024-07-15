# Continuous Functions in Lean4

__By Felix Lentze & Dominic Plein as part of the [CompAssistedMath2024](https://github.com/matematiflo/CompAssistedMath2024) seminar by Florent Schaffhauser and Judith Ludwig at Heidelberg University.__

> [!warning]
> This is a research project and not stable code. We also don't maintain this code in the long run. It's mainly for educational purposes and for us to learn Lean4. Nevertheless, you might still find it useful to get started with Lean4 in the context of continuous functions.


## 🌟 About

In this repository, we give an introduction to **continuous functions** and formalize them in the functional programming language and mathematical proof-solver Lean4. Continuous functions play a crucial role in many math disciplines and are taught at the very beginning of math studies.

In this repo, you find:

- [**A LaTeX document**](./HandProof/main.pdf) that contains manual proofs. All proofs that were formalized in Lean4 are also written out in this document for reference. It's suggested to first comprehend the proof there, then look at the Lean4 code to see how it's formalized.

- The [**Lean4 code**](./Continuity/) with different files that correspond to the sections in the LaTeX document:
  - [Continuous Functions](./Continuity/continuous.lean): Here we give the definition of continuous functions.
  - [Examples](./Continuity/examples.lean): Here we give some examples of continuous functions.
  - [Algebraic properties](./Continuity/algebraic.lean): Here we prove that the sum and the product of two continuous functions are continuous again.
  - [Left- and right-continuity](./Continuity/leftright.lean): Here we define left- and right-continuity, and prove that they are equivalent to continuity. We also discuss the Heaviside function.


## 💻 Installation

See [this guide](https://lean-lang.org/lean4/doc/setup.html) for how to install Lean4 on your machine. It guides you through how to install `elan`, the Lean version manager, which also installs `Lake` for you, the Lean package manager.

Then run `lake exec cache get` in the root of this project. Don't run `lake update` as we want to stick with the specific version of Lean specified pinned via the `lake-manifest.json` file.


## 💻 Development

We use some **style guidelines** from the Lean community [here](https://leanprover-community.github.io/contribute/style.html) and [here](https://leanprover-community.github.io/contribute/doc.html). However, note that we are beginners in Lean and therefore our style used in the code might disagree with many "official" guidelines.

Our formatting aims at maximizing readability and understanding for beginners. We write out some tactics even if they could be compressed into a "one-liner". We also make use of excessive white space and comments to make the code more accessible and not a "hell of symbols".
