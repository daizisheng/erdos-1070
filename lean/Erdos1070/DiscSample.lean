import Erdos1070.TransferDensity
import Erdos1070.TransferSample

/-!
# Sampling and one-class density points for an arbitrary averaging sequence

Copies of `exists_good_sample` (`TransferSample`) and `exists_unitFree_of_field`
(`TransferDensity`) in which the squares `square m` are replaced by an arbitrary sequence of
measurable regions `Q m` of positive finite measure (used with discs `Q m = ball 0 m`).
The original square-based statements are untouched.
-/

namespace Erdos1070.Transfer

open OAI OAI.EuclideanFiveColor MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

section Sample

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Average of a realisation over the region `Q m`. -/
def regAvg (Q : ℕ → Set ℂ) (H : ℂ × Ω → ℝ) (m : ℕ) (ω : Ω) : ℝ≥0∞ :=
  (∫⁻ x in Q m, ENNReal.ofReal (H (x,ω))) / volume (Q m)

lemma regAvg_measurable (Q : ℕ → Set ℂ) {H : ℂ × Ω → ℝ} (hH : Measurable H) (m : ℕ) :
    Measurable (regAvg Q H m) := by
  have : Measurable fun ω => ∫⁻ x in Q m, ENNReal.ofReal (H (x,ω)) :=
    (ENNReal.measurable_ofReal.comp hH).lintegral_prod_left'
  exact this.div_const _

omit [MeasurableSpace Ω] in
lemma regAvg_le_one (Q : ℕ → Set ℂ) {H : ℂ × Ω → ℝ} (h1 : ∀ p, H p ≤ 1) (m : ℕ) (ω : Ω) :
    regAvg Q H m ω ≤ 1 := by
  apply ENNReal.div_le_of_le_mul
  rw [one_mul]
  calc ∫⁻ x in Q m, ENNReal.ofReal (H (x,ω)) ≤ ∫⁻ _ in Q m, 1 :=
        lintegral_mono fun x => ENNReal.ofReal_le_one.mpr (h1 _)
    _ = volume (Q m) := by rw [setLIntegral_const, one_mul]

lemma regAvg_mean (Q : ℕ → Set ℂ) {H : ℂ × Ω → ℝ} (hH : Measurable H) (h0 : ∀ p, 0 ≤ H p)
    (h1 : ∀ p, H p ≤ 1) {c : ℝ} (hm : ∀ x, ∫ ω, H (x,ω) ∂μ = c) (m : ℕ)
    (hpos : volume (Q m) ≠ 0) (hfin : volume (Q m) ≠ ⊤) :
    ∫⁻ ω, regAvg Q H m ω ∂μ = ENNReal.ofReal c := by
  simp only [regAvg, div_eq_mul_inv]
  have hmeas : Measurable fun ω => ∫⁻ x in Q m, ENNReal.ofReal (H (x,ω)) :=
    (ENNReal.measurable_ofReal.comp hH).lintegral_prod_left'
  rw [lintegral_mul_const _ hmeas]
  have hswap : ∫⁻ ω, ∫⁻ x in Q m, ENNReal.ofReal (H (x,ω)) ∂volume ∂μ =
      ∫⁻ x in Q m, ∫⁻ ω, ENNReal.ofReal (H (x,ω)) ∂μ := by
    apply lintegral_lintegral_swap
    exact ((ENNReal.measurable_ofReal.comp hH).comp measurable_swap).aemeasurable
  have hin : ∀ x, ∫⁻ ω, ENNReal.ofReal (H (x,ω)) ∂μ = ENNReal.ofReal c := by
    intro x
    have hint : Integrable (fun ω => H (x,ω)) μ := by
      refine Integrable.of_bound (C := 1)
        (hH.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable ?_
      exact Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (h0 _)]; exact h1 _
    rw [← hm x, ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ω => h0 _)]
  rw [hswap]
  simp only [hin, setLIntegral_const]
  rw [mul_assoc, ENNReal.mul_inv_cancel hpos hfin, mul_one]

theorem exists_good_sample_reg (Q : ℕ → Set ℂ) (hQ0 : ∀ m, 1 ≤ m → volume (Q m) ≠ 0)
    (hQt : ∀ m, volume (Q m) ≠ ⊤) {H : ℂ × Ω → ℝ} (hH : Measurable H) (h0 : ∀ p, 0 ≤ H p)
    (h1 : ∀ p, H p ≤ 1) {c : ℝ} (hm : ∀ x, ∫ ω, H (x,ω) ∂μ = c)
    (ho : ∀ x : ℂ, ∀ u : Circle, ∀ᵐ ω ∂μ, H (x,ω) * H (x+u,ω) = 0) :
    ∃ ω : Ω, (∀ᵐ p ∂(volume : Measure ℂ).prod angularMeasure,
        H (p.1,ω) * H (p.1 + direction p.2,ω) = 0) ∧
      ENNReal.ofReal c ≤ limsup (fun m : ℕ => regAvg Q H m ω) atTop := by
  have hS : MeasurableSet {q : (ℂ × Angles) × Ω |
      H (q.1.1,q.2) * H (q.1.1 + direction q.1.2,q.2) = 0} := by
    apply measurableSet_eq_fun _ measurable_const
    exact (hH.comp (measurable_fst.fst.prodMk measurable_snd)).mul
      (hH.comp ((measurable_fst.fst.add (direction_continuous.measurable.comp measurable_fst.snd)).prodMk
        measurable_snd))
  have hG : ∀ᵐ ω ∂μ, ∀ᵐ p ∂(volume : Measure ℂ).prod angularMeasure,
      H (p.1,ω) * H (p.1 + direction p.2,ω) = 0 :=
    (Measure.ae_ae_comm hS).mp (.of_forall fun p => ho p.1 (AddCircle.toCircle p.2))
  let X : Ω → ℝ≥0∞ := fun ω => limsup (fun m : ℕ => regAvg Q H m ω) atTop
  have hX1 : ∀ ω, X ω ≤ 1 := fun ω =>
    limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall fun m => regAvg_le_one Q h1 m ω)
  have hfatou : ENNReal.ofReal c ≤ ∫⁻ ω, X ω ∂μ := by
    have hl := limsup_lintegral_le (μ := μ) (fun _ => 1) (fun m => regAvg_measurable Q hH m)
      (fun m => Eventually.of_forall fun ω => regAvg_le_one Q h1 m ω) (by simp)
    have hc : limsup (fun m => ∫⁻ ω, regAvg Q H m ω ∂μ) atTop = ENNReal.ofReal c := by
      rw [limsup_congr (eventually_atTop.mpr ⟨1, fun m hm1 =>
        regAvg_mean μ Q hH h0 h1 hm m (hQ0 m hm1) (hQt m)⟩)]
      exact limsup_const _
    rw [hc] at hl
    exact hl
  have hfreq : ∃ᵐ ω ∂μ, ENNReal.ofReal c ≤ X ω := by
    intro hn
    have hlt : ∀ᵐ ω ∂μ, X ω < ENNReal.ofReal c := by
      filter_upwards [hn] with ω hω
      exact not_le.mp hω
    have hs := lintegral_strict_mono (IsProbabilityMeasure.ne_zero μ) aemeasurable_const
      (ne_top_of_le_ne_top (b := ∫⁻ _, 1 ∂μ) (by simp) (lintegral_mono hX1)) hlt
    rw [lintegral_const, measure_univ, mul_one] at hs
    exact (not_le.mpr hs) hfatou
  obtain ⟨ω, hω1, hω2⟩ := (hfreq.and_eventually hG).exists
  exact ⟨ω, hω2, hω1⟩

end Sample

section Density

variable (h : ℂ → ℝ) (hh : Measurable h)
include hh

/-- Region version of `exists_unitFree_of_field`: the same set `A` (density-one points of
`{h > 0}` minus a null set), with the density measured along `Q m`. -/
theorem exists_unitFree_of_field_reg (Q : ℕ → Set ℂ) (h0 : ∀ x, 0 ≤ h x) (h1 : ∀ x, h x ≤ 1)
    (hw : ∀ᵐ p ∂(volume : Measure ℂ).prod angularMeasure, h p.1 * h (p.1 + direction p.2) = 0)
    {c : ℝ} (hc : ENNReal.ofReal c ≤ limsup (fun m : ℕ =>
      (∫⁻ x in Q m, ENNReal.ofReal (h x)) / volume (Q m)) atTop) :
    ∃ A : Set ℂ, MeasurableSet A ∧ UnitFree A ∧
      c ≤ limsup (fun m : ℕ => (volume (A ∩ Q m)).toReal / (volume (Q m)).toReal) atTop := by
  set A0 : Set ℂ := {z | 0 < h z} with hA0def
  have hA0 : MeasurableSet A0 := measurableSet_lt measurable_const hh
  have hdens : ∀ᵐ x ∂(volume : Measure ℂ), x ∈ A0 → DensityOne A0 x := by
    filter_upwards [Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume hA0]
      with x hx hxA
    simpa only [DensityOne, Set.indicator_of_mem hxA, Pi.one_apply] using hx
  set N : Set ℂ := toMeasurable volume {x | ¬ (x ∈ A0 → DensityOne A0 x)} with hNdef
  have hN0 : volume N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact ae_iff.mp hdens
  set A : Set ℂ := A0 \ N with hAdef
  have hAm : MeasurableSet A := hA0.diff (measurableSet_toMeasurable _ _)
  have hAd : ∀ x ∈ A, DensityOne A0 x := by
    intro x hx
    by_contra hn
    exact hx.2 (subset_toMeasurable _ _ (show ¬ (x ∈ A0 → DensityOne A0 x) from fun h' => hn (h' hx.1)))
  refine ⟨A, hAm, ?_, ?_⟩
  · intro x hx y hy hxy
    exact density_unitFree h hh hw hxy (hAd x hx) (hAd y hy)
  · have hAQ : ∀ m : ℕ, volume (A ∩ Q m) = volume (A0 ∩ Q m) := by
      intro m
      apply measure_congr
      have : A0 ∩ Q m =ᵐ[volume] (A0 ∩ Q m) \ N := (sdiff_null_ae_eq_self hN0).symm
      refine EventuallyEq.trans ?_ this.symm
      rw [hAdef, inter_sdiff_right_comm]
    let a : ℕ → ℝ≥0∞ := fun m => volume (A ∩ Q m) / volume (Q m)
    have ha1 : ∀ m, a m ≤ 1 := fun m =>
      ENNReal.div_le_of_le_mul (by rw [one_mul]; exact measure_mono inter_subset_right)
    have hle : ∀ m : ℕ, (∫⁻ x in Q m, ENNReal.ofReal (h x)) / volume (Q m) ≤ a m := by
      intro m
      have hI : ∫⁻ x in Q m, ENNReal.ofReal (h x) ≤ volume (A ∩ Q m) := by
        calc ∫⁻ x in Q m, ENNReal.ofReal (h x) ≤ ∫⁻ x in Q m, A0.indicator 1 x := by
              apply lintegral_mono
              intro x
              by_cases hx : x ∈ A0
              · rw [Set.indicator_of_mem hx]; exact ENNReal.ofReal_le_one.mpr (h1 x)
              · have : h x = 0 := le_antisymm (not_lt.mp hx) (h0 x)
                simp [Set.indicator_of_notMem hx, this]
          _ = volume (A0 ∩ Q m) := by
              rw [lintegral_indicator_one hA0, Measure.restrict_apply hA0]
          _ = volume (A ∩ Q m) := (hAQ m).symm
      exact ENNReal.div_le_div_right hI _
    have hlim : ENNReal.ofReal c ≤ limsup a atTop :=
      hc.trans (limsup_le_limsup (Eventually.of_forall hle))
    have hreal : limsup (fun m : ℕ => (volume (A ∩ Q m)).toReal / (volume (Q m)).toReal) atTop =
        (limsup a atTop).toReal := by
      rw [← ENNReal.limsup_toReal_eq ENNReal.one_ne_top (Eventually.of_forall ha1)]
      congr 1
      funext m
      simp only [a, ENNReal.toReal_div]
    rw [hreal]
    exact (ENNReal.ofReal_le_iff_le_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top
      (limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall ha1)))).mp hlim

end Density

end

end Erdos1070.Transfer
