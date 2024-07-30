import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.Basic

open Filter

-- Beispiel: zeigen, dass 1/x an 0 nicht stetig ist
example : ¬ ContinuousAt (fun x ↦ 1 / x) 0 := by
  dsimp [ContinuousAt]
  intro h_cont
  let x_n := fun n => 1 / (n + 1 : ℝ)
  have h_tendsto_x_n : Filter.Tendsto x_n Filter.atTop (nhds 0) := by
    intro ε hε
  have h_not_tendsto : ¬Filter.Tendsto (fun n => 1 / x_n n) Filter.atTop (nhds 0) := by
    intro h_tendsto
    -- Berechne 1 / x_n n
    have h_diverges : Filter.Tendsto (fun n => n + 1) Filter.atTop Filter.atTop := by
      exact tendsto_add_atTop_nat 1
    -- Da h_tendsto eine Konvergenz gegen 0 verlangt, ist dies ein Widerspruch
    simp[x_n] at h_tendsto
    sorry 
  have h_not_cont : ¬Filter.Tendsto (fun x => 1 / x) (nhds 0) (nhds 0) := by
    sorry
  contradiction
