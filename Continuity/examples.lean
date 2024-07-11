import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Continuity.continuous

-- # Constant function `x ↦ c` with `c ∈ ℝ`

/-- The constant function is continuous (at any given point). -/
theorem constant_function_is_continuous_at_any_point
    (D : Set ℝ) (c : ℝ) (a : D)
    : IsContinuousAt D (fun _ ↦ c) a := by
  dsimp [IsContinuousAt]
  intro ε hεbigger0
  exists 1
  exact ⟨by norm_num, by
    intro x _h_delta_criterion
    simp only [sub_self, abs_zero]
    exact hεbigger0⟩ -- or just put `assumption` here

  -- Alternative proof
  -- dsimp [IsContinuousAt]
  -- intro ε hεbigger0
  -- exists 1
  -- simp only [gt_iff_lt, zero_lt_one, sub_self, abs_zero, true_and]
  -- intro x _h_delta_criterion
  -- assumption

/-- The constant function is continuous. -/
theorem constant_function_is_continuous
    (D : Set ℝ) (c : ℝ)
    : IsContinuous D (fun _ ↦ c) := by
  intro a
  exact constant_function_is_continuous_at_any_point D c a


-- # Linear function `x ↦ a * x + b` with `a, b ∈ ℝ`





-- # Parabola `x ↦ x^2`

/-- The parabola `x ↦ x^2` is continuous. -/
