import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Continuity.continuous


--------------------------------------------------------------------------------
-- # Constant function `x ↦ c` with `c ∈ ℝ`
--------------------------------------------------------------------------------

/-- The constant function is continuous (at a given point `a ∈ D ⊆ ℝ`). -/
theorem constant_function_is_continuous_at_a_point
    (D : Set ℝ) (c : ℝ) (a : D)
    : IsContinuousAt D (fun _ ↦ c) a := by

  dsimp [IsContinuousAt]
  intro ε hεbigger0
  exists 1
  exact ⟨by norm_num, by
    intro x _h_xδ_criterion
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

/-- The function `x ↦ m * x + y₀` is continuous (at a given point `a ∈ D ⊆ ℝ`). -/
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
    intro x h_xδ_criterion
    simp
    calc |m * x - m * a| = |m * (x - a)| := by ring_nf
      _ = |m| * |x.val - a.val| := abs_mul m (x - a)
      _ < |m| * δ := (mul_lt_mul_iff_of_pos_left (by positivity)).mpr h_xδ_criterion
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

/-- The function `x ↦ x^2` is continuous (at a given point `a ∈ D ⊆ ℝ`). -/
theorem parabola_is_continuous_at_a_point
    (D : Set ℝ) (a : D)
    : IsContinuousAt D (fun x ↦ x^2) a := by

  let a' := a.val
  dsimp [IsContinuousAt]
  intro ε h_εbigger0

  -- `δ` and its upper bounds
  let δ := ε / (2 * |a'| + 1) ⊓ 1
  use δ
  have h_δbigger0 : δ > 0 := by simp [δ]; positivity
  have h_δsmaller1 : δ ≤ 1 := inf_le_right
  have h_δsmallerε : δ ≤ ε / (2 * |a'| + 1) := inf_le_left
  simp only [h_δbigger0, true_and]

  intro x h_xδ_criterion
  let x' := x.val

  -- Some inequalities for the calculation
  have h_triangle_inequality : |x' + a'| ≤ |x'| + |a'| := abs_add x' a'
  have h_x_smaller : |x'| < (|a'| + δ) := by calc
    |x'| = |a' + (x' - a')|  := by ring_nf
      _ <= |a'| + |x' - a'|  := abs_add a' (x' - a')
      _ < |a'| + δ           := by linarith [h_xδ_criterion]
  have h_x_smaller_with_added_term : |x'| + |a'| < (|a'| + δ) + |a'|
    := by linarith [h_x_smaller]

  calc |x'^2 - a'^2|

    _ = |(x' + a') * (x' - a')|
      := by ring_nf

    _ = |x' + a'| * |x' - a'|
      := abs_mul (x' + a') (x' - a')

    _ ≤ (|x'| + |a'|) * |x' - a'|
      := mul_le_mul_of_nonneg_right h_triangle_inequality (abs_nonneg (x' - a'))

    _ ≤ (|x'| + |a'|) * δ
      := mul_le_mul_of_nonneg_left (le_of_lt h_xδ_criterion) (by positivity)

    _ < ((|a'| + δ) + |a'| ) * δ
      := (mul_lt_mul_iff_of_pos_right h_δbigger0).mpr h_x_smaller_with_added_term

    _ = (2 * |a'| + δ) * δ
      := by ring_nf

    _ ≤ (2 * |a'| + 1) * δ
      := (mul_le_mul_iff_of_pos_right h_δbigger0).mpr (by linarith [h_δsmaller1])

    _ ≤ (2 * |a'| + 1) * (ε / (2 * |a'| + 1))
      := mul_le_mul_of_nonneg_left h_δsmallerε (by positivity)

    _ = ε
      := by field_simp

/-- The function `x ↦ x^2` is continuous. -/
theorem parabola_is_continuous
    (D : Set ℝ)
    : IsContinuous D (fun x ↦ x^2) := by

  intro a
  exact parabola_is_continuous_at_a_point D a
