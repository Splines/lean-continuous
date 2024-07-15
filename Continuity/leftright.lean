import Continuity.continuous


--------------------------------------------------------------------------------
-- # Definition of left- and right-continuity
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

/-- The Heaviside function is right-continuous. -/
example : IsRightContinuousAt Set.univ (fun x ↦ Heaviside x) ⟨0, trivial⟩ := by
  intro ε hεbigger0
  use 1
  simp
  intro x h_x_gt_zero _h_xδ_criterion

  -- Variant 1: via `split_ifs`
  split_ifs with h_xvalue
  · linarith
  · simp only [sub_self, abs_zero]
    exact hεbigger0

  -- Variant 2: via `if_neg`
  -- rw [if_neg]
  -- · simp only [sub_self, abs_zero]
  --   exact hεbigger0
  -- · simp only [not_lt]
  --   exact le_of_lt h_x_gt_zero

/-- The Heaviside function is not continuous (at `a = 0`). -/
example : ¬IsContinuousAt Set.univ (fun x ↦ Heaviside x) ⟨0, trivial⟩ := by
  -- We proof by contradiction, so we assume that the function is continuous
  -- and show that this leads to a `False` truth-value.
  intro h_is_continuous

  let ε := (1:ℝ)/2
  choose δ δ_pos hδ using h_is_continuous ε (by positivity)

  let x := -δ/2
  have h_x_smaller_zero : x < 0 := by dsimp [x]; linarith
  have h_x_smaller_delta : x < δ := by dsimp [x]; linarith
  have h_x_smaller_delta' : |x| < δ := by
    dsimp [x]
    simp only [abs_lt]
    constructor
    · linarith
    · linarith

  -- Construct contradiction
  have h_heaviside : |Heaviside x  - Heaviside 0| = 1 := by
    simp [Heaviside, h_x_smaller_zero]

  have h_heaviside_ε : |Heaviside x - Heaviside 0| < ε := by
    simp [Heaviside] at hδ
    simp
    exact hδ x h_x_smaller_delta'

  have h_blow_up_math : 1 < 1/2 := by
    -- replace `1` by `|Heaviside x - Heaviside 0|`
    -- replace `1/2` by `ε`
    sorry

  -- Apply contradiction
  exact absurd h_blow_up_math (by norm_num)



--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- TODO from hereon
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

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
