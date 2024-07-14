import Continuity.continuous


--------------------------------------------------------------------------------
-- # Sum of two continuous functions `f` and `g`
--------------------------------------------------------------------------------

/-- The sum of two continuous functions is continuous. -/
theorem sum_of_two_continuous_functions_is_continuous
    (D : Set ℝ) (f: D → ℝ) (g: D → ℝ)
    (h_f_continuous: IsContinuous D f) (h_g_continuous: IsContinuous D g)
    : IsContinuous D (f + g) := by

  intro a
  dsimp [IsContinuousAt]
  intro ε h_εbigger0

  -- Individual continuity of f and g
  have h_f_continuous_short : ∃ δ₁ > 0, ∀ x : D,
      |x.val - a| < δ₁ → |f x - f a| < ε/2 := by
    apply h_f_continuous
    simp
    exact h_εbigger0

  have h_g_continuous_short : ∃ δ₂ > 0, ∀ x : D,
      |x.val - a| < δ₂ → |g x - g a| < ε/2 := by
    apply h_g_continuous
    simp
    exact h_εbigger0

  -- Choice of `δ`
  obtain ⟨δ₁, δ₁_positive, hδ₁⟩ := h_f_continuous_short
  obtain ⟨δ₂, δ₂_positive, hδ₂⟩ := h_g_continuous_short
  use min δ₁ δ₂

  constructor
  -- min δ₁ δ₂ > 0
  · apply lt_min δ₁_positive δ₂_positive

  -- Continuity of f + g
  · intro x h_δ_criterion

    have h_f_estimate : |f x - f a| < ε/2 := by
      apply hδ₁ x (lt_of_lt_of_le h_δ_criterion (min_le_left δ₁ δ₂))
    have h_g_estimate : |g x - g a| < ε/2 := by
      apply hδ₂ x (lt_of_lt_of_le h_δ_criterion (min_le_right δ₁ δ₂))

    simp
    calc |f x + g x - (f a + g a)|

      _ = |(f x - f a) + (g x - g a)|
        := by ring_nf

      _ ≤ |f x - f a| + |g x - g a|
        := by exact abs_add (f x - f a) (g x - g a)

      _ < ε/2 + ε/2
        := add_lt_add h_f_estimate h_g_estimate

      _ = ε
        := by linarith


--------------------------------------------------------------------------------
-- # Product of two continuous functions `f` and `g`
--------------------------------------------------------------------------------

/-- The product of two continuous functions is continuous -/
theorem product_of_two_continuous_functions_is_continuous
    (D : Set ℝ) (f: D → ℝ) (g: D → ℝ)
    (h_f_continuous: IsContinuous D f) (h_g_continuous: IsContinuous D g)
    : IsContinuous D (f * g) := by

  intro a
  dsimp [IsContinuousAt]
  intro ε h_εbigger0

  -- Individual continuity of f and g
  have h_f_continuous_short : ∃ δ₁ > 0, ∀ x : D,
      |x.val - a| < δ₁ → |f x - f a| < ε / (2 * |g a| + 1) := by
    apply h_f_continuous
    apply div_pos h_εbigger0
    apply add_pos_of_nonneg_of_pos
    simp [abs_nonneg]
    exact by field_simp

  have h_g_continuous_short : ∃ δ₂ > 0, ∀ x : D,
      |x.val - a| < δ₂ → |g x - g a| < ε / (2 * (ε + |f a|)) := by
    apply h_g_continuous
    apply div_pos h_εbigger0
    simp
    apply add_pos_of_pos_of_nonneg h_εbigger0
    simp [abs_nonneg]

  -- Choice of `δ`
  obtain ⟨δ₁, δ₁_positive, hδ₁⟩ := h_f_continuous_short
  obtain ⟨δ₂, δ₂_positive, hδ₂⟩ := h_g_continuous_short
  use min δ₁ δ₂

  constructor
  -- min δ₁ δ₂ > 0
  · apply lt_min δ₁_positive δ₂_positive

  -- Continuity of f * g
  · intro x h_δ_criterion

    have h_f_estimate : |f x - f a| < (ε / (2 * |g a| + 1)) := by
      apply hδ₁ x
      exact lt_of_lt_of_le h_δ_criterion (min_le_left δ₁ δ₂)

    have h_g_estimate : |g x - g a| < ε / (2 * (ε + |f a|)) := by
      apply hδ₂ x
      exact lt_of_lt_of_le h_δ_criterion (min_le_right δ₁ δ₂)

    have h_f_smaller_epsilon : |f x| - |f a| < ε := by
      calc |f x| - |f a|
        _ ≤ |f x - f a| := by exact abs_sub_abs_le_abs_sub (f x) (f a)
        _ < ε / (2 * |g a| + 1) := h_f_estimate
        _ ≤ ε := by
          apply div_le_self
          · exact (le_of_lt h_εbigger0) -- ε > 0
          · simp

    have h_frac_smaller_one : |g a| / (|g a| + 1/2) ≤ 1 := by
      rw [div_le_one]
      . exact by linarith
      . exact by field_simp

    have h_ε_for_g : ε / (2 * |g a| + 1) * |g a| ≤ ε/2 := by
      calc ε / (2 * |g a| + 1) * |g a|
        _ = ε / 2 * (|g a| / (|g a| + 1/2)) := by field_simp; linarith
        _ ≤ ε / 2 * 1 := by
          apply mul_le_mul_of_nonneg_left
          exact h_frac_smaller_one
          apply le_of_lt
          simp; exact h_εbigger0
        _ = ε / 2 := by linarith

    calc |(f * g) x - (f * g) a|

      _ = |f x * g x - f a * g a|
        := by simp [mul_sub]

      _ = |f x * g x - f x * g a + f x * g a - f a * g a|
        := by ring_nf

      _ = |f x * (g x - g a)  +  (f x - f a) * g a|
        := by ring_nf

      _ ≤ |f x * (g x - g a)| + |(f x - f a) * g a|
        := abs_add _ _

      _ = |f x| * |g x - g a| + |f x - f a| * |g a|
        := by simp [abs_mul]

      _ ≤ |f x| * (ε / (2 * (ε + |f a|))) + |f x - f a| * |g a|
        := by
          simp only [add_le_add_iff_right]
          apply mul_le_mul_of_nonneg_left
          apply le_of_lt
          apply h_g_estimate
          apply abs_nonneg

      _ ≤ |f x| * (ε / (2 * (ε + |f a|))) + ε / (2 * |g a| + 1) * |g a|
        := by
          simp only [add_le_add_iff_left]
          apply mul_le_mul_of_nonneg_right
          apply le_of_lt
          apply h_f_estimate
          apply abs_nonneg

      _ < (ε + |f a|) * (ε / (2 * (ε + |f a|))) + ε / (2 * |g a| + 1) * |g a|
        := by
          simp only [add_lt_add_iff_right]
          apply mul_lt_mul_of_pos_right
          exact by linarith [h_f_smaller_epsilon]
          apply div_pos h_εbigger0
          simp
          apply add_pos_of_pos_of_nonneg h_εbigger0
          simp [abs_nonneg]

      _ = ε / 2 + ε / (2 * |g a| + 1) * |g a|
        := by field_simp; linarith

      _ ≤ ε / 2 + ε / 2
        := by
          simp only [add_le_add_iff_left]
          exact h_ε_for_g

      _ = ε
        := by linarith
