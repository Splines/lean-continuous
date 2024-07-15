import Continuity.continuous


--------------------------------------------------------------------------------
-- # Definition of left- and right-continuity.
--------------------------------------------------------------------------------

/-- Definition of a left-continuous function `f: D → ℝ`. -/
def IsLeftContinuousAt (D : Set ℝ) (f : D → ℝ) (a : D) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : D,
  x < a → (|x.val - a.val| < δ  →  |f x - f a| < ε)

/-- Definition of a right-continuous function `f: D → ℝ`. -/
def IsRightContinuousAt (D : Set ℝ) (f : D → ℝ) (a : D) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : D,
  x > a → (|x.val - a.val| < δ  →  |f x - f a| < ε)


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- TODO from hereon
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- # Heaviside function as example
--------------------------------------------------------------------------------

/--
  Definition of the Heaviside function, often denoted `Θ` in literature.

  By the keyword `noncomputable`, we signal Lean4 that this function does not have
  a constructive computational method within the confines of Lean's type theory
  and logic. You may want to look up "decidability in computer science" for more
  information on this topic, e.g. the halting problem and deterministic finite
  automata.

  The `@[simp]` attribute tells Lean to use this definition as a simplification rule
  when simplifying expressions via the `simp` tactic.
-/
@[simp]
noncomputable def Heaviside (x : ℝ) : ℝ := if x < 0 then 0 else 1

/-- The Heaviside function is right-continuous -/
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

/-- The Heaviside function is not continuous (at `a = 0`). -/
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


--------------------------------------------------------------------------------
-- # Equivalence of continuity and left- and right-continuity
--------------------------------------------------------------------------------

theorem LeftRightContinuousIffIsContinuous (D : Set ℝ) (f: D → ℝ) (x : D) : (IsContinuousAt D f x) ↔ (IsLeftContinuousAt D f x ∧ IsRightContinuousAt D f x) := by
  constructor
  -- left side implies right side
  · intro h
    constructor
    · intro ε hε
      obtain ⟨δ, hδ, hδ_prop⟩ := h (ε) (by linarith)
      use δ
      constructor
      · exact hδ
      · intros y hy yltx
        exact hδ_prop y hy
    · intro ε hε
      obtain ⟨δ, hδ, hδ_prop⟩ := h (ε) (by linarith)
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
