import Erdos1070.TransferDensity

/-!
# Sampling one good realisation of a stationary field

Given a jointly measurable `H : ℂ × Ω → [0,1]` over a probability space with constant mean `c`
and pointwise-a.s. vanishing unit correlations, some sample `ω` has
(a) `H(x,ω) H(x+u,ω) = 0` for a.e. `(x,u) ∈ ℂ × S¹`, and
(b) `limsup_m |Q_m|⁻¹ ∫_{Q_m} H(·,ω) ≥ c` (reverse Fatou).
-/

namespace Erdos1070.Transfer

open OAI OAI.EuclideanFiveColor MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Square average of a realisation. -/
def sqAvg (H : ℂ × Ω → ℝ) (m : ℕ) (ω : Ω) : ℝ≥0∞ :=
  (∫⁻ x in square m, ENNReal.ofReal (H (x,ω))) / volume (square m)

lemma sqAvg_measurable {H : ℂ × Ω → ℝ} (hH : Measurable H) (m : ℕ) : Measurable (sqAvg H m) := by
  have : Measurable fun ω => ∫⁻ x in square m, ENNReal.ofReal (H (x,ω)) :=
    (ENNReal.measurable_ofReal.comp hH).lintegral_prod_left'
  exact this.div_const _

omit [MeasurableSpace Ω] in
lemma sqAvg_le_one {H : ℂ × Ω → ℝ} (h1 : ∀ p, H p ≤ 1) (m : ℕ) (ω : Ω) : sqAvg H m ω ≤ 1 := by
  apply ENNReal.div_le_of_le_mul
  rw [one_mul]
  calc ∫⁻ x in square m, ENNReal.ofReal (H (x,ω)) ≤ ∫⁻ _ in square m, 1 :=
        lintegral_mono fun x => ENNReal.ofReal_le_one.mpr (h1 _)
    _ = volume (square m) := by rw [setLIntegral_const, one_mul]

lemma sqAvg_mean {H : ℂ × Ω → ℝ} (hH : Measurable H) (h0 : ∀ p, 0 ≤ H p) (h1 : ∀ p, H p ≤ 1)
    {c : ℝ} (hm : ∀ x, ∫ ω, H (x,ω) ∂μ = c) (m : ℕ) (hm1 : 1 ≤ m) :
    ∫⁻ ω, sqAvg H m ω ∂μ = ENNReal.ofReal c := by
  have hpos : volume (square (m:ℝ)) ≠ 0 :=
    (volume_square_pos (by exact_mod_cast hm1 : (0:ℝ) < m)).ne'
  have hfin := volume_square_ne_top (m:ℝ)
  simp only [sqAvg, div_eq_mul_inv]
  have hmeas : Measurable fun ω => ∫⁻ x in square m, ENNReal.ofReal (H (x,ω)) :=
    (ENNReal.measurable_ofReal.comp hH).lintegral_prod_left'
  rw [lintegral_mul_const _ hmeas]
  have hswap : ∫⁻ ω, ∫⁻ x in square m, ENNReal.ofReal (H (x,ω)) ∂volume ∂μ =
      ∫⁻ x in square m, ∫⁻ ω, ENNReal.ofReal (H (x,ω)) ∂μ := by
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

theorem exists_good_sample {H : ℂ × Ω → ℝ} (hH : Measurable H) (h0 : ∀ p, 0 ≤ H p)
    (h1 : ∀ p, H p ≤ 1) {c : ℝ} (hm : ∀ x, ∫ ω, H (x,ω) ∂μ = c)
    (ho : ∀ x : ℂ, ∀ u : Circle, ∀ᵐ ω ∂μ, H (x,ω) * H (x+u,ω) = 0) :
    ∃ ω : Ω, (∀ᵐ p ∂(volume : Measure ℂ).prod angularMeasure,
        H (p.1,ω) * H (p.1 + direction p.2,ω) = 0) ∧
      ENNReal.ofReal c ≤ limsup (fun m : ℕ => sqAvg H m ω) atTop := by
  -- (a) the correlation holds for a.e. sample
  have hS : MeasurableSet {q : (ℂ × Angles) × Ω |
      H (q.1.1,q.2) * H (q.1.1 + direction q.1.2,q.2) = 0} := by
    apply measurableSet_eq_fun _ measurable_const
    exact (hH.comp (measurable_fst.fst.prodMk measurable_snd)).mul
      (hH.comp ((measurable_fst.fst.add (direction_continuous.measurable.comp measurable_fst.snd)).prodMk
        measurable_snd))
  have hG : ∀ᵐ ω ∂μ, ∀ᵐ p ∂(volume : Measure ℂ).prod angularMeasure,
      H (p.1,ω) * H (p.1 + direction p.2,ω) = 0 :=
    (Measure.ae_ae_comm hS).mp (.of_forall fun p => ho p.1 (AddCircle.toCircle p.2))
  -- (b) reverse Fatou
  let X : Ω → ℝ≥0∞ := fun ω => limsup (fun m : ℕ => sqAvg H m ω) atTop
  have hXm : Measurable X := Measurable.limsup fun m => sqAvg_measurable hH m
  have hX1 : ∀ ω, X ω ≤ 1 := fun ω =>
    limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall fun m => sqAvg_le_one h1 m ω)
  have hfatou : ENNReal.ofReal c ≤ ∫⁻ ω, X ω ∂μ := by
    have hl := limsup_lintegral_le (μ := μ) (fun _ => 1) (fun m => sqAvg_measurable hH m)
      (fun m => Eventually.of_forall fun ω => sqAvg_le_one h1 m ω) (by simp)
    have hc : limsup (fun m => ∫⁻ ω, sqAvg H m ω ∂μ) atTop = ENNReal.ofReal c := by
      rw [limsup_congr (eventually_atTop.mpr ⟨1, fun m hm1 => sqAvg_mean μ hH h0 h1 hm m hm1⟩)]
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

end

end Erdos1070.Transfer
