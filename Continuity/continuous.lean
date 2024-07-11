/-
# Continuity of real functions

By Judith Ludwig, Christian Merten and Florent Schaffhauser,
Proseminar on computer-assisted mathematics,
Heidelberg, Summer Semester 2024

Edited by Felix Lentze and Dominic Plein.

In this project, we show basic properties of continuous functions. The goal isto show that continuity is equivalent to left and right continuity combined.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-
The domain `D` of any function that we consider in this document
is a subset of the real numbers `ℝ`.
-/
-- variable {D : Set ℝ}

/-
We can find lemma names by using the library search tactic `exact?`.
-/
example (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  exact abs_add x y


-- # Definition of continuity

/-
Definition of a continuous function `f : D → ℝ` at a point `a ∈ D`.
-/
def IsContinuousAt (D : Set ℝ) (f : D → ℝ) (a : D) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : D,
  (|x.val - a.val| < δ  →  |f x - f a| < ε)

/-
Definition of a continuous function on a set `D`.
-/
def IsContinuous (D : Set ℝ) (f : D → ℝ) : Prop :=
  ∀ (a : D), IsContinuousAt D f a
