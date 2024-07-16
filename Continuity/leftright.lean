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
  have _h_x_smaller_delta : x < δ := by dsimp [x]; linarith
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

  have h_blow_up_math : ε > 1 := by
    calc ε > |Heaviside x - Heaviside 0| := h_heaviside_ε
      _ = 1 := h_heaviside

  exact absurd h_blow_up_math (by norm_num)


--------------------------------------------------------------------------------
-- # Equivalence of continuity and left- and right-continuity
--------------------------------------------------------------------------------

theorem LeftRightContinuousIffIsContinuous
    (D : Set ℝ) (f: D → ℝ) (a : D)
    : (IsContinuousAt D f a)
      ↔ (IsLeftContinuousAt D f a ∧ IsRightContinuousAt D f a) := by

  constructor

  -- Left side implies right side,
  -- i.e. (continuity) → (left- and right-continuity)
  · intro h_continuous
    constructor

    -- Left-continuity
    · dsimp [IsLeftContinuousAt]
      intro ε h_εbigger0
      obtain ⟨δ, h_δbigger0, h_δ⟩ := h_continuous ε (by linarith)
      use δ
      use h_δbigger0
      intro x _h_x_smaller_a h_x_δ_criterion
      exact h_δ x h_x_δ_criterion

    -- Right-continuity
    · dsimp [IsLeftContinuousAt]
      intro ε h_εbigger0
      obtain ⟨δ, h_δbigger0, h_δ⟩ := h_continuous ε (by linarith)
      use δ
      use h_δbigger0
      intro x _h_x_bigger_a h_x_δ_criterion
      exact h_δ x h_x_δ_criterion

  -- Right side implies left side,
  -- i.e. (left- and right-continuity) → (continuity)
  · intro h_left_and_right_continuous
    rcases h_left_and_right_continuous with ⟨left_continuous, right_continuous⟩
    intro ε h_εbigger0

    -- `δ₁` and `δ₂` obtained from left- and right-continuity
    obtain ⟨δ₁, hδ₁, hδ₁_prop⟩ := left_continuous ε (by linarith)
    obtain ⟨δ₂, hδ₂, hδ₂_prop⟩ := right_continuous (ε) (by linarith)
    use min δ₁ δ₂
    use lt_min hδ₁ hδ₂

    intro x h_x_δ_criterion

    by_cases h_a_value : x < a
    -- x < a (use left-continuity)
    · apply hδ₁_prop x h_a_value
      apply lt_of_lt_of_le h_x_δ_criterion
      apply min_le_left

    -- x ≥ a
    · push_neg at h_a_value
      by_cases h_a_value' : x = a
      -- x = a
      · rewrite [h_a_value']
        simp [abs_zero, h_εbigger0]
      -- x > a (use right-continuity)
      · have h_x_bigger_a : x > a := by
          push_neg at h_a_value'
          exact lt_of_le_of_ne h_a_value (id (Ne.symm h_a_value'))
        apply hδ₂_prop x h_x_bigger_a
        apply lt_of_lt_of_le h_x_δ_criterion
        apply min_le_right
