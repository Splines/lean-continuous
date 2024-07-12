import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Continuity.continuous

--------------------------------------------------------------------------------
-- # Constant function `x ↦ c` with `c ∈ ℝ`
--------------------------------------------------------------------------------

/-- The constant function is continuous (at any given point). -/
theorem constant_function_is_continuous_at_a_point
    (D : Set ℝ) (c : ℝ) (a : D)
    : IsContinuousAt D (fun _ ↦ c) a := by

  dsimp [IsContinuousAt]
  intro ε hεbigger0
  exists 1
  exact ⟨by norm_num, by
    intro x _h_x_δ_criterion
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
  exact constant_function_is_continuous_at_a_point D c a


--------------------------------------------------------------------------------
-- # Function `x ↦ m * x + y₀` with `m, y₀ ∈ ℝ`
--------------------------------------------------------------------------------

/-- The function `x ↦ m * x + y₀` is continuous (at any given point). -/
theorem lines_are_continuous_at_a_point
    (D : Set ℝ) (m y₀ : ℝ) (a : D)
    : IsContinuousAt D (fun x ↦ m * x + y₀) a := by

  by_cases m_cases : m = 0

  -- m = 0
  · subst m
    simp only [zero_mul, zero_add]
    exact constant_function_is_continuous_at_a_point D y₀ a

  -- m ≠ 0
  . push_neg at m_cases
    dsimp [IsContinuousAt]
    intro ε h_εbigger0
    let δ := ε / |m|
    have h_δbigger0 : δ > 0 := by positivity
    exists δ
    simp only [h_δbigger0, true_and]
    intro x h_x_δ_criterion
    simp
    calc |m * x - m * a| = |m * (x - a)| := by ring_nf
      _ = |m| * |x.val - a.val| := abs_mul m (x - a)
      _ < |m| * δ := (mul_lt_mul_iff_of_pos_left (by positivity)).mpr h_x_δ_criterion
      _ = |m| * (ε / |m|) := by rfl
      _ = ε := by field_simp

/-- The function `x ↦ m * x + y₀` is continuous. -/
theorem lines_are_continuous
    (D : Set ℝ) (m y₀ : ℝ)
    : IsContinuous D (fun x ↦ m * x + y₀) := by

  intro a
  exact lines_are_continuous_at_a_point D m y₀ a


--------------------------------------------------------------------------------
-- # Parabola `x ↦ x^2`
--------------------------------------------------------------------------------

-- /-- The parabola `x ↦ x^2` is continuous. -/
