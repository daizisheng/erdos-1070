import Erdos1070.TransferKoopman
import Erdos1070.TransferSample

/-!
# Erdős #1070, Part 3: `alphaStar ≤ m1`

There is a measurable unit-distance-free planar set of upper density at least `alphaStar`.
Route: invariant random independent subset of the algebraic plane (`TransferSpace`),
projection of `1[0 ∈ ω]` onto the continuous factor and the Haar rigidity theorem of the
OpenAI five-colour development (`TransferKoopman`), sampling (`TransferSample`), and
one-class density points (`TransferDensity`).
-/

namespace Erdos1070

open MeasureTheory Filter Topology

theorem exists_unitFree_density_ge :
    ∃ A : Set ℂ, MeasurableSet A ∧ UnitFree A ∧ alphaStar ≤ upperDensity A := by
  obtain ⟨H, hHm, hH01, hHmean, hHcor⟩ := Transfer.exists_field
  obtain ⟨ω, hω1, hω2⟩ := Transfer.exists_good_sample Transfer.measure hHm
    (fun p => (hH01 p).1) (fun p => (hH01 p).2) hHmean hHcor
  obtain ⟨A, hAm, hAu, hAd⟩ := Transfer.exists_unitFree_of_field (fun x => H (x,ω))
    (hHm.comp (measurable_id.prodMk measurable_const)) (fun x => (hH01 _).1) (fun x => (hH01 _).2)
    hω1 hω2
  exact ⟨A, hAm, hAu, Transfer.integral_label.trans hAd⟩

theorem alphaStar_le_m1 : alphaStar ≤ m1 := by
  obtain ⟨A, hAm, hAu, hAd⟩ := exists_unitFree_density_ge
  refine hAd.trans (le_csSup ?_ ⟨A, hAm, hAu, rfl⟩)
  refine ⟨1, ?_⟩
  rintro d ⟨B, _, _, rfl⟩
  exact Transfer.upperDensity_le_one B

end Erdos1070
