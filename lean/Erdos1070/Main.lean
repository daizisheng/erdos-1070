import Erdos1070.Elementary
import Erdos1070.Transfer

/-!
# Erdős #1070: `f(n) = (m₁ + o(1)) n`

`f n` is the largest number such that every `n` points of the plane contain `f n` points with
no two at distance `1`; `m1` is the supremum of the upper densities of measurable planar sets
with no two points at distance `1`.
-/

namespace Erdos1070

open Filter Topology

theorem alphaStar_eq_m1 : alphaStar = m1 := le_antisymm alphaStar_le_m1 m1_le_alphaStar

/-- **Main theorem.** `f(n)/n → m₁`. -/
theorem f_div_tendsto_m1 : Tendsto (fun n : ℕ => (f n : ℝ) / n) atTop (𝓝 m1) := by
  simpa [alphaStar_eq_m1] using f_div_tendsto_alphaStar

/-- Larman–Rogers lower bound, for every `n`: `m₁ n ≤ f(n)`. -/
theorem m1_mul_le_f (n : ℕ) : m1 * n ≤ f n := by
  simpa [alphaStar_eq_m1] using f_ge_alphaStar n

end Erdos1070
