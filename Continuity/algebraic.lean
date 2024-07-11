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
Try to adapt the proof that the sum of continuous functions is continuous to show that the product of continuous functions is continuous.
-/
theorem cont_mul (D : Set ℝ) (f: ℝ → ℝ) (g: ℝ → ℝ) (hf: IsContinuous D f) (hg: IsContinuous D g) : IsContinuous D (f * g) := by
  intro x hx
  intro ε hε
  dsimp [IsContinuousAt]
  have hf1 : ∃ δ₁ > 0, ∀ y ∈ D, |x - y| < δ₁ → |f x - f y| < ε /(2 * |g y| + 1) := by sorry
    /-apply hf x hx (ε / (2 * |g x| + 1))
    simp
    apply div_pos hε
    apply mul_pos zero_lt_two
    apply add_pos_of_nonneg_of_pos
    exact abs_nonneg (g x)
    exact zero_lt_one
    -/
  have hg1 : ∃ δ₂ > 0, ∀ y ∈ D, |x - y| < δ₂ → |g x - g y| < ε / (2 * (ε +|f y|)) := by sorry
    /- apply hg x hx (ε / (2 * (ε +|f x|)))
    simp
    apply div_pos hε
    apply mul_pos zero_lt_two
    apply add_pos_of_pos_of_nonneg hε
    apply abs_nonneg
    -/
  obtain ⟨δ₁, δ₁_pos, hδ₁⟩ := hf1
  obtain ⟨δ₂, δ₂_pos, hδ₂⟩ := hg1
  let δ := min δ₁ δ₂
  use δ
  constructor
  · apply lt_min δ₁_pos δ₂_pos
  · intros y hy hδ
    have h1 : |f x - f y| < ε / (2 * |g y| + 1) := by
      apply hδ₁ y hy
      exact lt_of_lt_of_le hδ (min_le_left δ₁ δ₂)
    have h2 : |g y - g x| < ε / (2 * (ε + |f y|)) := by sorry
      --apply hδ₂ y hy
      --exact lt_of_lt_of_le hδ (min_le_right δ₁ δ₂)
    have h3 : |f x| - |f y| < ε := by
      calc |f x| - |f y| ≤ |f x - f y| := by sorry
        --_ < ε / (2 * |g y| + 1) := h1
        --_ ≤ ε := div_le_div_left (le_of_lt hε)
    calc |(f * g) x - (f * g) y| = |f x * g x - f y * g y| := by sorry
       _ = |f x * g x - f x * g y + f x * g y - f y * g y| := by sorry
       _ = |f x * (g x - g y) + (f x - f y) * g y| := by sorry
       _ ≤ |f x * (g x - g y)| + |(f x - f y) * g y| := by sorry
       _ = |f x| * |g x - g y| + |f x - f y| * |g y| := by sorry
       _ = (ε + |f y|) * |g x - g y| + |f x - f y| * |g y| := by sorry
       _ < (ε + |f y|) * ε / (2 * (ε +|f y|)) + ε /(2 * |g y| + 1) * |g y| := by sorry
       _ < (ε + |f y|) * ε / (2 * (ε +|f y|)) + ε /(2 * |g y|) * |g y| := by sorry
       _ = ε/2 + ε/2 := by sorry
       _ = ε := by ring_nf
