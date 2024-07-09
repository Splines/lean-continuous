/-
# Continuity of real functions

By Judith Ludwig, Christian Merten and Florent Schaffhauser,
Proseminar on computer-assisted mathematics,
Heidelberg, Summer Semester 2024

In this project, we show basic properties of continuous functions. The goal is to show that continuity is equivalent to left and right continuity combined.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-
We can find lemma names by using the library search tactic `exact?`.
-/

example (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  exact abs_add x y

/-
Definition of a continuous function `f : ℝ → ℝ` on a set `D` at a point `x ∈ D`.
-/

def IsContinuousAt (D : Set ℝ) (f : ℝ → ℝ) (x : ℝ) (_ : x ∈ D) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ y ∈ D, |x - y| < δ → |f x - f y| < ε

/-
Definition of a continuous function on a set `D`.
-/

def IsContinuous (D : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ (x : ℝ) (hx : x ∈ D), IsContinuousAt D f x hx

namespace IsContinuousAt

/-
The definition of `ConvergesTo` unwrapped.
-/

lemma iff (D : Set ℝ) (f : ℝ → ℝ) (x : ℝ) (hx : x ∈ D) :
    IsContinuousAt D f x hx ↔ ∀ ε > 0, ∃ δ > 0, ∀ y ∈ D, |x - y| < δ → |f x - f y| < ε := by
  rfl

/-
Constant sequences converge to the constant value.
-/

theorem of_constant (D : Set ℝ) (a x : ℝ) (hx : x ∈ D) : IsContinuousAt D (fun _ ↦ a) x hx := by
  -- The "definitional simplifier" `dsimp` is optional, but it can help you clarify what the goal is
  dsimp [IsContinuousAt]
  intro ε hε
  use 1
  -- Found with `simp?`
  simp only [gt_iff_lt, zero_lt_one, sub_self, abs_zero, true_and]
  intro y _ _
  assumption

/-
The function `x ↦ x ^ 2` is continuous at every point on all of `ℝ`
(which is the 'universal' set `Set.univ : Set ℝ`.

This proof is very verbose. Try to understand what is going on step by step and optimize the argument.
-/

--Simple start: Every linear Function is continuous

example (x a b : ℝ) (hx : x ∈ Set.univ): IsContinuousAt Set.univ (fun y ↦ a * y + b) x hx := by
  intro ε hε
  by_cases azero : a ≠ 0
  · let δ : ℝ := ε / |a|
    use δ
    have hd: 0 < δ := by positivity
    refine ⟨hd, ?_⟩
    intro y _ hyd
    --Useful "Haves"
    have h1: 0 < |a| := by positivity
    calc
     |(a * x + b) - (a * y + b)| = |a * x + b - a * y - b| := by ring_nf
      _ = |a * x - a * y| := by ring_nf
      _ = |a * (x - y)| := by ring_nf
      _ = |a| * |x - y| := abs_mul a (x - y)
      _ < |a| * δ := (mul_lt_mul_iff_of_pos_left h1).mpr hyd
      _ = |a| * (ε / |a|) := by exact rfl
      _ = ε := by field_simp
  · push_neg at azero
    have hf: (fun y => a * y + b) = (fun y => b) := by
      funext
      simp [azero]
    simp [hf, azero]
    sorry 
/-

-/
example (x : ℝ) : IsContinuousAt Set.univ (fun y ↦ y ^ 2) x trivial := by
  intro ε hε
  let δ : ℝ := ε / (2 * |x| + 1) ⊓ 1
  use δ
  -- the `positivity` tactic can solve many goals of the form `0 < a` or `0 ≤ a`.
  have hd : 0 < δ := by simp [δ]; positivity
  have hd' : δ ≤ 1 := inf_le_right
  have hd'' : δ ≤ ε / (2 * |x| + 1) := inf_le_left
  refine ⟨hd, ?_⟩
  intro y _ hyd
  have h0 : |y| < |x| + δ := by
    calc |y| = |x + (y - x)| := by ring_nf
          _  ≤ |x| + |y - x| := abs_add x (y - x)
          _  ≤ |x| + |x - y| := by rw [abs_sub_comm]
          _  < |x| + δ       := (Real.add_lt_add_iff_left |x|).mpr hyd
  have h1 : |x + y| ≤ |x| + |y| := abs_add x y
  have h2 : 0 ≤ |x - y| := abs_nonneg (x - y)
  have h3 : 0 ≤ |x| + |y| := by positivity
  have h4 : |x - y| ≤ δ := le_of_lt hyd
  have h5 : |x| + |y| < |x| + (|x| + δ) := (Real.add_lt_add_iff_left |x|).mpr h0
  have h6 : 2 * |x| + δ ≤ 2 * |x| + 1 := (add_le_add_iff_left (2 * |x|)).mpr hd'
  calc
    |x ^ 2 - y ^ 2| = |(x + y) * (x - y)|   := by ring_nf
                  _ = |x + y| * |x - y|     := abs_mul (x + y) (x - y)
                  _ ≤ (|x| + |y|) * |x - y| := mul_le_mul_of_nonneg_right h1 h2
                  _ ≤ (|x| + |y|) * δ       := mul_le_mul_of_nonneg_left h4 h3
                  _ < (|x| + (|x| + δ)) * δ := (mul_lt_mul_iff_of_pos_right hd).mpr h5
                  _ = (2 * |x| + δ) * δ     := by ring_nf
                  _ ≤ (2 * |x| + 1) * δ     := (mul_le_mul_iff_of_pos_right hd).mpr h6
                  _ ≤ (2 * |x| + 1) * (ε / (2 * |x| + 1)) :=
                      mul_le_mul_of_nonneg_left hd'' (by positivity)
                  _ = ε                     := by field_simp

/-
The function `x ↦ 1 / x` is continuous at `0` on the set `D = { x | x ≠ 0 }`.

Question: Can you prove this for `D = Set.univ` (i.e. `D` the set of all real numbers?)
Hint: In Lean `1 / x` is also defined for `x = 0`.
-/

example (x : ℝ) (hx : x ≠ 0) : IsContinuousAt { x | x ≠ 0} (fun y ↦ 1 / y) x hx := by
  intro ε hε
  let δ : ℝ := ε * |x| * |x| / 2 ⊓ |x|/2
  use δ
  have hd : 0 < δ := by
    simp [δ]
    constructor
    · exact by positivity
    · exact hx
  have hd' : δ ≤ ε * |x| * |x| / 2 := inf_le_left
  have hd'' : δ ≤ |x| / 2 := inf_le_right
  refine ⟨hd, ?_⟩
  intro y hy hyd
  have h1 : |x| > 0 := by positivity
  have h2 : |y| ≠ 0 := abs_ne_zero.mpr hy
  have h3 : |y| > 0 := by positivity
  have h4 : |x| * |y| > 0 := by exact Real.mul_pos h1 h3
  have h5 : |x| / 2 ≤ |y| := by
    calc |x| / 2 = |x| - |x| / 2 := by ring_nf
      _ ≤ |x| - δ := by linarith [hyd]
      _ ≤ |x| - |x - y| := by linarith [hd'']
      _ ≤ |x - (x - y)| := abs_sub_abs_le_abs_sub x (x - y)
      _ = |y| := by ring_nf
  have h6 : 0 < |x| * (|x| / 2) := by exact mul_pos h1 (half_pos h1)
  have h7 : |x| * (|x| / 2) ≤ |x| * |y| := mul_le_mul_of_nonneg_left h5 (le_of_lt h1)
  calc |1/x - 1/y| = |(1 * y - 1 * x) / (x * y)| := by rw [div_sub_div 1 1 hx hy]; ring_nf
    _ = |(y - x) / (x * y)| := by ring_nf
    _ = |y - x| / |x * y| := by rw [abs_div]
    _ = |x - y| / |x * y| := by rw [abs_sub_comm]
    _ = |x - y| / (|x| * |y|) := by rw [abs_mul]
    _ < δ / (|x| * |y|) := (div_lt_div_right h4).mpr hyd
    _ ≤ δ / (|x| * (|x|/2)) := (div_le_div_left hd h4 h6).mpr h7
    _ ≤ (ε * |x| * |x|/2) / (|x| * (|x|/2)) := (div_le_div_right h6).mpr hd'
    _ = ε * (|x| * |x|/2) / (|x| * (|x|/2)) := by ring_nf
    _ = ε := by field_simp
end IsContinuousAt
/-
The sum of continuous functions is continuous. Can you complete the proof below (remove the sorries)?
-/

theorem cont_sum (D : Set ℝ) (f: ℝ → ℝ) (g: ℝ → ℝ) (hf: IsContinuous D f) (hg: IsContinuous D g) : IsContinuous D (f + g) := by
  intro x hx
  intro ε hε
  have hf1 : ∃ δ₁ > 0, ∀ y ∈ D, |x - y| < δ₁ → |f x - f y| < ε/2 := by
    apply hf x hx (ε / 2)
    simp
    exact hε
  have hg1 : ∃ δ₂ > 0, ∀ y ∈ D, |x - y| < δ₂ → |g x - g y| < ε/2 := by
    apply hg x hx (ε / 2)
    simp
    exact hε
  choose δ₁ hδ₁ using hf1
  choose δ₂ hδ₂ using hg1
  use min δ₁ δ₂
  constructor
  · simp
    constructor
    · exact hδ₁.1
    · exact hδ₂.1
  · intro y hy hmin
    have f_con : |f x - f y| < ε/2 := by sorry
    have g_con : |g x - g y| < ε/2 := by sorry
    simp
    calc |f x + g x - (f y + g y)| = |(f x - f y) + (g x - g y)| := by ring_nf
      _ ≤ |f x - f y| + |g x - g y| := by exact abs_add (f x - f y) (g x - g y)
      _  < ε/2 + ε/2 := add_lt_add f_con g_con
      _ = ε := by linarith
/-
Definition of a right continuous function. Can you explain the definition?
-/
def IsRightContinuousAt (D : Set ℝ) (f : ℝ → ℝ) (x : ℝ) (_ : x ∈ D) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ y ∈ D, y > x → |x - y| < δ → |f x - f y| < ε

@[simp]
noncomputable def Heaviside (x : ℝ) : ℝ := if x < 0 then 0 else 1
/- The Heaviside function is right continuous. -/
example : IsRightContinuousAt Set.univ Heaviside 0 trivial := by
  intro ε hε
  use 1
  simp
  intro y hy _
  -- Try to do this with `split_ifs` instead.
  rw [if_neg]
  · simp only [sub_self, abs_zero]
    positivity
  · simp only [not_lt]
    exact le_of_lt hy

/-
But the Heaviside function is not continuous!
-/
example : ¬ IsContinuousAt Set.univ Heaviside 0 trivial := by
  intro h_cont
  let ε := (1:ℝ)/2
  have h0 : ε > 0 := by positivity
  choose δ δ_pos hδ using h_cont ε h0
  let x := -δ/2
  have h1 : x < 0 := by
    apply div_neg_of_neg_of_pos (neg_lt_zero.mpr δ_pos) zero_lt_two
  have h3 : |x - 0| < δ := by
    simp
    rewrite [abs_div, abs_neg, abs_of_nonneg, abs_of_nonneg]
    apply (div_lt_self δ_pos one_lt_two)
    exact zero_le_two
    exact le_of_lt δ_pos
  have h4 : |Heaviside x - Heaviside 0| ≥ ε := by
    simp[h1]
    norm_num
  have h5 : |Heaviside x - Heaviside 0| < ε := by
    rewrite [abs_sub_comm]
    apply hδ
    exact trivial
    rewrite [abs_sub_comm]
    exact h3
  have h6 : |Heaviside x - Heaviside 0| < |Heaviside x - Heaviside 0| := lt_of_lt_of_le h5 h4
  apply lt_irrefl |Heaviside x - Heaviside 0| h6
/-
Now define a left continuous function and prove that a function is continuous at `x` if and only if it is left and right continuous at `x`!

Hint: You might find the `by_cases` tactic helpful!
-/
def IsLeftContinuousAt (D : Set ℝ) (f : ℝ → ℝ) (x : ℝ) (_ : x ∈ D) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ y ∈ D, y < x → |x - y| < δ → |f x - f y| < ε
@[simp]
/-
-/
theorem LeftRightContinuousIffIsContinuous (D : Set ℝ) (f: ℝ → ℝ) (x : ℝ) (hx : x ∈ D): (IsContinuousAt D f x hx) ↔ (IsLeftContinuousAt D f x hx ∧ IsRightContinuousAt D f x hx) := by
  constructor
  -- left side implies right side
  · intro h
    constructor
    · intro ε hε
      obtain ⟨δ, hδ, hδ_prop⟩ := h (ε) (by linarith)--warum brauche ich hier linarith? Obtain nochmal untersuchen
      use δ
      constructor
      · exact hδ
      · intros y hy yltx
        exact hδ_prop y hy
    · intro ε hε
      obtain ⟨δ, hδ, hδ_prop⟩ := h (ε) (by linarith) --warum brauche ich hier linarith? Obtain nochmal untersuchen
      use δ
      constructor
      · exact hδ
      · intros y hy hyx
        exact hδ_prop y hy
  -- right side implies left side
  · intro h
    rcases h with ⟨l, r⟩
    intro ε hε
    obtain ⟨δ₁, hδ₁, hδ₁_prop⟩ := l (ε) (by linarith)
    obtain ⟨δ₂, hδ₂, hδ₂_prop⟩ := r (ε) (by linarith)
    use min δ₁ δ₂
    constructor
    · apply lt_min hδ₁ hδ₂
    · intro y hy hyδ
      by_cases hyx : y < x
      · apply hδ₁_prop y hy hyx
        apply lt_of_lt_of_le hyδ
        apply min_le_left
      · push_neg at hyx
        · by_cases hex : y = x
          · rewrite [hex]
            simp [abs_zero, hε]
          · have h0 : x < y := by
              push_neg at hex
              exact lt_of_le_of_ne hyx (id (Ne.symm hex))
            apply hδ₂_prop y hy h0
            apply lt_of_lt_of_le hyδ
            apply min_le_right
/-
Try to adapt the proof that the sum of continuous functions is continuous to show that the product of continuous functions is continuous.
-/
theorem cont_mul (D : Set ℝ) (f: ℝ → ℝ) (g: ℝ → ℝ) (hf: IsContinuous D f) (hg: IsContinuous D g) : IsContinuous D (f * g) := by
  sorry
