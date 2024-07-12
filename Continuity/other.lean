import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Continuity.continuous

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
