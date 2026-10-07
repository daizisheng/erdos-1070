import Mathlib

/-!
# Erdős #1070: shared definitions

`f n` is the largest number such that every `n` points in the plane contain `f n` points
with no two at distance `1`.  `m1` is the supremum of the upper densities of measurable
planar sets with no two points at distance `1`.
-/

namespace Erdos1070

open MeasureTheory Filter Topology

/-- No two points of `S` are at distance exactly `1`. -/
def UnitFree (S : Set ℂ) : Prop := ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≠ 1

/-- Independence number of the unit-distance graph on a finite point set. -/
noncomputable def indepNum (P : Finset ℂ) : ℕ :=
  sSup {m | ∃ I ⊆ P, UnitFree (I : Set ℂ) ∧ I.card = m}

/-- `f n` = min over `n`-point sets of the independence number. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m | ∃ P : Finset ℂ, P.card = n ∧ indepNum P = m}

/-- The square `[-m,m]²` in `ℂ`. -/
def square (m : ℝ) : Set ℂ := {z | |z.re| ≤ m ∧ |z.im| ≤ m}

/-- Upper density along the squares `[-m,m]²`, `m ∈ ℕ`. -/
noncomputable def upperDensity (A : Set ℂ) : ℝ :=
  limsup (fun m : ℕ => (volume (A ∩ square m)).toReal / (volume (square m)).toReal) atTop

/-- `m₁`: the supremum of upper densities of measurable unit-distance-free sets. -/
noncomputable def m1 : ℝ :=
  sSup {d | ∃ A : Set ℂ, MeasurableSet A ∧ UnitFree A ∧ upperDensity A = d}

/-- `α*`: the infimum of independence ratios of nonempty finite point sets. -/
noncomputable def alphaStar : ℝ :=
  sInf {r | ∃ P : Finset ℂ, P.Nonempty ∧ r = (indepNum P : ℝ) / P.card}

end Erdos1070
