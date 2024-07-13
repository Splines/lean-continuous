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
    use δ
    have h_δbigger0 : δ > 0 := by positivity

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

  -- `∀ x ∈ D`
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


--------------------------------------------------------------------------------
-- # Hyperbola `x ↦ 1/x`
--------------------------------------------------------------------------------

/-- `a ∈ D` implies `a ≠ 0` since `D = { a | a ≠ 0 }` -/
lemma element_not_zero_if_set_has_no_zero
    (D : Set ℝ) (h_0notinD : 0 ∉ D) (a : D)
    : a.val ≠ 0 := by
  apply ne_of_mem_of_not_mem a.property
  exact h_0notinD

lemma reverse_triangle_inequality
    (a b : ℝ)
    : |a| - |b| ≤ |a + b| := by
  let m : ℝ := a + b
  let n : ℝ := -b
  have h_mn : m + n = a := by ring_nf
  calc
    |a| - |b| = |m + n| - |n| := by rw [h_mn, abs_neg]
            _ ≤ |m| := by linarith [abs_add m n]
            _ = |a + b| := by linarith [h_mn]


/-- The function `x ↦ 1/x` is continuous
(at a given point `a ∈ D ⊆ ℝ` with `0 ≠ D`) -/
theorem hyperbola_is_continuous_at_a_point
    (D : Set ℝ) (h_0notinD : 0 ∉ D) (a : D)
    : IsContinuousAt D (fun x ↦ 1/x) a := by

  let a' := a.val
  have h_a_not_0 : a' ≠ 0 := element_not_zero_if_set_has_no_zero D h_0notinD a
  dsimp [IsContinuousAt]
  intro ε h_εbigger0

  -- `δ` and its upper bounds
  let δ := ε * |a'|^2 / 2 ⊓ |a'| / 2
  use δ
  have h_δbigger0 : δ > 0 := by
    simp [δ]
    constructor
    . exact mul_pos h_εbigger0 (sq_pos_of_ne_zero h_a_not_0)
    . exact h_a_not_0
  have h_δsmallerfirst : δ ≤ ε * |a'|^2 / 2 := inf_le_left
  have h_δsmallersecond : δ ≤ |a'| / 2 := inf_le_right
  simp only [h_δbigger0, true_and]

  -- `∀ x ∈ D`
  intro x h_xδ_criterion
  let x' := x.val
  have h_x_not_0 : x' ≠ 0 := element_not_zero_if_set_has_no_zero D h_0notinD x

  -- Some inequalities for the calculation
  have h_x_bigger_a : |x'| > |a'| / 2 := by
    calc |x'| = |a' + (x' - a')|  := by ring_nf
      _ ≥ |a'| - |x' - a'|  := by linarith [reverse_triangle_inequality a' (x' - a')]
      _ > |a'| - δ          := by linarith [h_xδ_criterion]
      _ ≥ |a'| / 2          := by linarith [h_δsmallersecond]
  have h_x_bigger_a_with_factor : |a'| * |x'| > |a'| * (|a'| / 2) := by
    apply mul_lt_mul_of_pos_left h_x_bigger_a
    simp [h_a_not_0]

  calc |1/x' - 1/a'|

    _ = |(a' - x') / (a' * x')|
      := by rw [div_sub_div 1 1 h_x_not_0 h_a_not_0]; ring_nf

    _ = |x' - a'| / (|a'| * |x'|)
      := by rw [abs_div, abs_mul, abs_sub_comm]

    _ < δ / (|a'| * |x'|)
      := (div_lt_div_right (by positivity)).mpr h_xδ_criterion

    _ < δ / (|a'| * (|a'| / 2))
      := (div_lt_div_left h_δbigger0 (by positivity) (by positivity)).mpr
        h_x_bigger_a_with_factor

    _ ≤ (ε * |a'|^2 / 2) / (|a'| * (|a'| / 2))
      := (div_le_div_right (by positivity)).mpr h_δsmallerfirst

    _ = (ε * |a'|^2 / 2) / (|a'|^2 / 2)
      := by ring_nf

    _ = ε
      := by field_simp


/-
Question: Can you prove this for `D = Set.univ` (i.e. `D` the set of all real numbers?)
Hint: In Lean `1 / x` is also defined for `x = 0`.
-/
