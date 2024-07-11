/-
The function `x ↦ x ^ 2` is continuous at every point on all of `ℝ`
(which is the 'universal' set `Set.univ : Set ℝ`.

This proof is very verbose. Try to understand what is going on step by step and optimize the argument.
-/

--Simple start: Every linear Function is continuous

example (x a b : ℝ) (hx : x ∈ Set.univ): IsContinuousAt Set.univ (fun y ↦ a * y + b) x hx := by
  intro ε hε
  by_cases azero : a ≠ 0
  · let δ : ℝ := ε / |a|
    use δ
    have hd: 0 < δ := by positivity
    refine ⟨hd, ?_⟩
    intro y _ hyd
    --Useful "Haves"
    have h1: 0 < |a| := by positivity
    calc
     |(a * x + b) - (a * y + b)| = |a * x + b - a * y - b| := by ring_nf
      _ = |a * x - a * y| := by ring_nf
      _ = |a * (x - y)| := by ring_nf
      _ = |a| * |x - y| := abs_mul a (x - y)
      _ < |a| * δ := (mul_lt_mul_iff_of_pos_left h1).mpr hyd
      _ = |a| * (ε / |a|) := by exact rfl
      _ = ε := by field_simp
  · push_neg at azero
    have hf: (fun y => a * y + b) = (fun y => b) := by
      funext
      simp [azero]
    simp [hf, azero]
    sorry
/-

-/
example (x : ℝ) : IsContinuousAt Set.univ (fun y ↦ y ^ 2) x trivial := by
  intro ε hε
  let δ : ℝ := ε / (2 * |x| + 1) ⊓ 1
  use δ
  -- the `positivity` tactic can solve many goals of the form `0 < a` or `0 ≤ a`.
  have hd : 0 < δ := by simp [δ]; positivity
  have hd' : δ ≤ 1 := inf_le_right
  have hd'' : δ ≤ ε / (2 * |x| + 1) := inf_le_left
  refine ⟨hd, ?_⟩
  intro y _ hyd
  have h0 : |y| < |x| + δ := by
    calc |y| = |x + (y - x)| := by ring_nf
          _  ≤ |x| + |y - x| := abs_add x (y - x)
          _  ≤ |x| + |x - y| := by rw [abs_sub_comm]
          _  < |x| + δ       := (Real.add_lt_add_iff_left |x|).mpr hyd
  have h1 : |x + y| ≤ |x| + |y| := abs_add x y
  have h2 : 0 ≤ |x - y| := abs_nonneg (x - y)
  have h3 : 0 ≤ |x| + |y| := by positivity
  have h4 : |x - y| ≤ δ := le_of_lt hyd
  have h5 : |x| + |y| < |x| + (|x| + δ) := (Real.add_lt_add_iff_left |x|).mpr h0
  have h6 : 2 * |x| + δ ≤ 2 * |x| + 1 := (add_le_add_iff_left (2 * |x|)).mpr hd'
  calc
    |x ^ 2 - y ^ 2| = |(x + y) * (x - y)|   := by ring_nf
                  _ = |x + y| * |x - y|     := abs_mul (x + y) (x - y)
                  _ ≤ (|x| + |y|) * |x - y| := mul_le_mul_of_nonneg_right h1 h2
                  _ ≤ (|x| + |y|) * δ       := mul_le_mul_of_nonneg_left h4 h3
                  _ < (|x| + (|x| + δ)) * δ := (mul_lt_mul_iff_of_pos_right hd).mpr h5
                  _ = (2 * |x| + δ) * δ     := by ring_nf
                  _ ≤ (2 * |x| + 1) * δ     := (mul_le_mul_iff_of_pos_right hd).mpr h6
                  _ ≤ (2 * |x| + 1) * (ε / (2 * |x| + 1)) :=
                      mul_le_mul_of_nonneg_left hd'' (by positivity)
                  _ = ε                     := by field_simp

/-
The function `x ↦ 1 / x` is continuous at `0` on the set `D = { x | x ≠ 0 }`.

Question: Can you prove this for `D = Set.univ` (i.e. `D` the set of all real numbers?)
Hint: In Lean `1 / x` is also defined for `x = 0`.
-/

example (x : ℝ) (hx : x ≠ 0) : IsContinuousAt { x | x ≠ 0} (fun y ↦ 1 / y) x hx := by
  intro ε hε
  let δ : ℝ := ε * |x| * |x| / 2 ⊓ |x|/2
  use δ
  have hd : 0 < δ := by
    simp [δ]
    constructor
    · exact by positivity
    · exact hx
  have hd' : δ ≤ ε * |x| * |x| / 2 := inf_le_left
  have hd'' : δ ≤ |x| / 2 := inf_le_right
  refine ⟨hd, ?_⟩
  intro y hy hyd
  have h1 : |x| > 0 := by positivity
  have h2 : |y| ≠ 0 := abs_ne_zero.mpr hy
  have h3 : |y| > 0 := by positivity
  have h4 : |x| * |y| > 0 := by exact Real.mul_pos h1 h3
  have h5 : |x| / 2 ≤ |y| := by
    calc |x| / 2 = |x| - |x| / 2 := by ring_nf
      _ ≤ |x| - δ := by linarith [hyd]
      _ ≤ |x| - |x - y| := by linarith [hd'']
      _ ≤ |x - (x - y)| := abs_sub_abs_le_abs_sub x (x - y)
      _ = |y| := by ring_nf
  have h6 : 0 < |x| * (|x| / 2) := by exact mul_pos h1 (half_pos h1)
  have h7 : |x| * (|x| / 2) ≤ |x| * |y| := mul_le_mul_of_nonneg_left h5 (le_of_lt h1)
  calc |1/x - 1/y| = |(1 * y - 1 * x) / (x * y)| := by rw [div_sub_div 1 1 hx hy]; ring_nf
    _ = |(y - x) / (x * y)| := by ring_nf
    _ = |y - x| / |x * y| := by rw [abs_div]
    _ = |x - y| / |x * y| := by rw [abs_sub_comm]
    _ = |x - y| / (|x| * |y|) := by rw [abs_mul]
    _ < δ / (|x| * |y|) := (div_lt_div_right h4).mpr hyd
    _ ≤ δ / (|x| * (|x|/2)) := (div_le_div_left hd h4 h6).mpr h7
    _ ≤ (ε * |x| * |x|/2) / (|x| * (|x|/2)) := (div_le_div_right h6).mpr hd'
    _ = ε * (|x| * |x|/2) / (|x| * (|x|/2)) := by ring_nf
    _ = ε := by field_simp
end IsContinuousAt
