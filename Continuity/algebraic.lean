import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Continuity.continuous

/-- The sum of two continuous functions is continuous. -/
theorem sum_of_two_continuous_functions_is_continuous
    (D : Set ℝ) (f: D → ℝ) (g: D → ℝ)
    (h_f_continuous: IsContinuous D f) (h_g_continuous: IsContinuous D g)
    : IsContinuous D (f + g) := by

  intro a
  dsimp [IsContinuousAt]
  intro ε h_εbigger0

  -- Individual continuity of f and g
  have h_f_inequality : ∃ δ₁ > 0, ∀ x : D,
      |x.val - a| < δ₁ → |f x - f a| < ε/2 := by
    apply h_f_continuous
    simp
    exact h_εbigger0

  have h_g_inequality : ∃ δ₂ > 0, ∀ x : D,
      |x.val - a| < δ₂ → |g x - g a| < ε/2 := by
    apply h_g_continuous
    simp
    exact h_εbigger0

  -- Choice of `δ`
  choose δ₁ h_δ₁ using h_f_inequality
  choose δ₂ h_δ₂ using h_g_inequality
  use min δ₁ δ₂

  constructor
  -- min δ₁ δ₂ > 0
  · simp
    constructor
    · exact h_δ₁.1
    · exact h_δ₂.1

  -- Continuity of f + g
  · intro x h_δ_criterion
    have f_estimate : |f x - f a| < ε/2 := by
      apply h_δ₁.2 x (lt_of_lt_of_le h_δ_criterion (min_le_left δ₁ δ₂))
    have g_estimate : |g x - g a| < ε/2 := by
      apply h_δ₂.2 x (lt_of_lt_of_le h_δ_criterion (min_le_right δ₁ δ₂))

    simp
    calc |f x + g x - (f a + g a)|

      _ = |(f x - f a) + (g x - g a)|
        := by ring_nf

      _ ≤ |f x - f a| + |g x - g a|
        := by exact abs_add (f x - f a) (g x - g a)

      _ < ε/2 + ε/2
        := add_lt_add f_estimate g_estimate

      _ = ε
        := by linarith

/-
Try to adapt the proof that the sum of continuous functions is continuous to show that the product of continuous functions is continuous.
-/
theorem cont_mul (D : Set ℝ) (f: D → ℝ) (g: D → ℝ) (hf: IsContinuous D f) (hg: IsContinuous D g) : IsContinuous D (f * g) := by
  intro x
  intro ε hε
  dsimp [IsContinuousAt]
  have hf1 : ∃ δ₁ > 0, ∀ y ∈ D, |x - y| < δ₁ → |f x - f y| < ε /(2 * |g y| + 1) := by
    apply hf x (ε / (2 * |g x| + 1))
    apply div_pos hε
    apply mul_pos zero_lt_two
    apply add_pos_of_nonneg_of_pos
    exact abs_nonneg _

  have hg1 : ∃ δ₂ > 0, ∀ y ∈ D, |x - y| < δ₂ → |g x - g y| < ε / (2 * (ε +|f y|)) := by
    apply hg x (ε / (2 * (ε +|f x|)))
    apply div_pos hε
    apply mul_pos zero_lt_two
    apply add_pos_of_pos_of_nonneg hε
    apply abs_nonneg _

  obtain ⟨δ₁, δ₁_pos, hδ₁⟩ := hf1
  obtain ⟨δ₂, δ₂_pos, hδ₂⟩ := hg1
  let δ := min δ₁ δ₂
  use δ
  constructor
  · apply lt_min δ₁_pos δ₂_pos
  · intro y hδ
    have h1 : |f x - f y| < (ε / (2 * |g y| + 1)) := by
     apply hδ₁ y
     exact lt_of_lt_of_le hδ (min_le_left δ₁ δ₂)
    have h2 : |g y - g x| < ε / (2 * (ε + |f y|)) := by
     apply hδ₂ y
     exact lt_of_lt_of_le hδ (min_le_right δ₁ δ₂)
    have h3 : |f x| - |f y| < ε := by
      calc |f x| - |f y| ≤ |f x - f y| := by exact abs_sub_abs_le_abs_sub (f x) (f y)
      _ < ε / (2 * |g y| + 1) := h1
      _ ≤ ε := by
        apply div_le_self
        · exact (le_of_lt hε)
        · simp
    have h4 : (ε + |f y|) * ε / (2 * (ε +|f y|)) + ε /(2 * |g y| + 1) * |g y| ≤ (ε + |f y|) * ε / (2 * (ε +|f y|)) + ε /(2 * |g y|) * |g y| := by
      by_cases g_equals_0 : |g y| = 0
      · apply add_le_add_left
        field_simp [g_equals_0]
      · push_neg at g_equals_0
        apply add_le_add_left
        apply mul_le_mul_of_nonneg_right
        · apply div_le_div_of_nonneg_left
          · exact le_of_lt hε
          · positivity
          · simp
        · exact abs_nonneg (g y)

    calc |(f * g) x - (f * g) y| = |f x * g x - f y * g y| := by simp [mul_sub]
       _ = |f x * g x - f x * g y + f x * g y - f y * g y| := by ring_nf
       _ = |f x * (g x - g y) + (f x - f y) * g y| := by ring_nf
       _ ≤ |f x * (g x - g y)| + |(f x - f y) * g y| := abs_add _ _
       _ = |f x| * |g x - g y| + |f x - f y| * |g y| := by simp [abs_mul]
       _ = (ε + |f y|) * |g x - g y| + |f x - f y| * |g y| := by simp [h3]
       _ < (ε + |f y|) * ε / (2 * (ε +|f y|)) + ε /(2 * |g y| + 1) * |g y| := by linarith
       _ ≤ (ε + |f y|) * ε / (2 * (ε +|f y|)) + ε /(2 * |g y|) * |g y| := h4
       _ = ε/2 + ε/2 := by field_simp
       _ = ε := by ring_nf
