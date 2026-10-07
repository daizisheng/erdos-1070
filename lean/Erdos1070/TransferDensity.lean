import Erdos1070.Defs
import OAI.Geometry.PlaneColoring.WeakColoring

/-!
# From a weakly unit-free field to a unit-free measurable set (one-class density points)

Given a measurable `h : ℂ → [0,1]` with `h(x) h(x+u) = 0` for almost every
`(x, u) ∈ ℂ × S¹` and with square averages of upper limit `≥ c`, the density-one points of
`{h > 0}` (minus a measurable null set) form a measurable unit-free set of upper density `≥ c`.
-/

namespace Erdos1070.Transfer

open OAI OAI.EuclideanFiveColor MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

lemma square_subset_ball (m : ℝ) : square m ⊆ Metric.closedBall 0 (2*m) := by
  intro z hz
  simp only [square, mem_ofPred_eq] at hz
  simp only [Metric.mem_closedBall, dist_zero_right]
  have := Complex.norm_le_abs_re_add_abs_im z
  linarith [hz.1, hz.2]

lemma volume_square_ne_top (m : ℝ) : volume (square m) ≠ ⊤ :=
  ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono (square_subset_ball m))

lemma volume_square_pos {m : ℝ} (hm : 0 < m) : 0 < volume (square m) := by
  refine lt_of_lt_of_le (Metric.measure_ball_pos volume (0:ℂ) hm) (measure_mono ?_)
  intro z hz
  simp only [Metric.mem_ball, dist_zero_right] at hz
  exact ⟨(Complex.abs_re_le_norm z).trans hz.le, (Complex.abs_im_le_norm z).trans hz.le⟩

lemma measurableSet_square (m : ℝ) : MeasurableSet (square m) := by
  have h1 : Measurable (fun z : ℂ => |z.re|) := Complex.continuous_re.measurable.abs
  have h2 : Measurable (fun z : ℂ => |z.im|) := Complex.continuous_im.measurable.abs
  exact (measurableSet_le h1 measurable_const).inter (measurableSet_le h2 measurable_const)

/-- Upper density bounded by one; used for `BddAbove` of the set defining `m1`. -/
lemma upperDensity_le_one (A : Set ℂ) : upperDensity A ≤ 1 := by
  have hb : ∀ m : ℕ, (volume (A ∩ square m)).toReal / (volume (square m)).toReal ≤ 1 := by
    intro m
    rcases eq_or_ne (volume (square (m:ℝ))).toReal 0 with h | h
    · rw [h, div_zero]; exact zero_le_one
    · apply div_le_one_of_le₀ _ (ENNReal.toReal_nonneg)
      exact ENNReal.toReal_mono (volume_square_ne_top _) (measure_mono inter_subset_right)
  have hb0 : ∀ m : ℕ, 0 ≤ (volume (A ∩ square m)).toReal / (volume (square m)).toReal :=
    fun m => div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  unfold upperDensity
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_eventually_le atTop (Eventually.of_forall hb0)
  · exact Eventually.of_forall hb

variable (h : ℂ → ℝ) (hh : Measurable h)
include hh

lemma weak_directions (hw : ∀ᵐ p ∂(volume : Measure ℂ).prod angularMeasure,
      h p.1 * h (p.1 + direction p.2) = 0) :
    ∀ t : Angles, ∀ᵐ z ∂(volume : Measure ℂ), ¬ (0 < h z ∧ 0 < h (z + direction t)) := by
  let A0 : Set ℂ := {z | 0 < h z}
  have hA0 : MeasurableSet A0 := measurableSet_lt measurable_const hh
  have ho : ∀ᵐ t ∂angularMeasure, ∀ᵐ z ∂(volume : Measure ℂ), h z * h (z + direction t) = 0 := by
    apply (Measure.ae_ae_comm ?_).mp (Measure.ae_ae_of_ae_prod hw)
    exact measurableSet_eq_fun ((hh.comp measurable_fst).mul
      (hh.comp (measurable_fst.add (direction_continuous.measurable.comp measurable_snd))))
      measurable_const
  let T : ℕ → Set ℂ := fun n => A0 ∩ Metric.closedBall 0 n
  have hT : ∀ n, MeasurableSet (T n) := fun n => hA0.inter measurableSet_closedBall
  have hTf : ∀ n, volume (T n) ≠ ⊤ := fun n =>
    ne_top_of_le_ne_top ((isCompact_closedBall (0 : ℂ) (n : ℝ)).measure_ne_top)
      (measure_mono inter_subset_right)
  let V : ℕ → PlaneL2 := fun n =>
    (memLp_indicator_const 2 (hT n) (1 : ℝ) (Or.inr (hTf n))).toLp _
  have hV : ∀ n, V n =ᵐ[volume] (T n).indicator (fun _ => (1 : ℝ)) := fun n => MemLp.coeFn_toLp _
  have hz : ∀ n, ∀ t : Angles, ∀ᵐ z ∂(volume : Measure ℂ), V n z * V n (z + direction t) = 0 := by
    intro n
    apply all_parameters_product_zero angularMeasure direction direction_continuous
    · filter_upwards [hV n] with z hz
      rw [hz]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    · filter_upwards [ho] with t ht
      filter_upwards [ht, hV n,
        (measurePreserving_add_right volume (direction t)).quasiMeasurePreserving.ae (hV n)]
        with z hne h1 h2
      rw [h1, h2]
      by_cases hzT : z ∈ T n
      · have hh' : z + direction t ∉ T n := by
          intro hh'
          have : h z * h (z + direction t) > 0 := mul_pos hzT.1 hh'.1
          linarith
        simp [Set.indicator_of_notMem hh']
      · simp [Set.indicator_of_notMem hzT]
  intro t
  have hi : ∀ᵐ z ∂(volume : Measure ℂ), ∀ n : ℕ,
      ((T n).indicator (fun _ => (1 : ℝ)) z) *
      ((T n).indicator (fun _ => (1 : ℝ)) (z + direction t)) = 0 := by
    apply ae_all_iff.mpr
    intro n
    filter_upwards [hz n t, hV n,
      (measurePreserving_add_right volume (direction t)).quasiMeasurePreserving.ae (hV n)]
      with z h0 h1 h2
    simpa only [h1, h2] using h0
  filter_upwards [hi] with z hz
  rintro ⟨h1, h2⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (max ‖z‖ ‖z + direction t‖)
  have m1 : z ∈ T n := ⟨h1, by
    simpa only [Metric.mem_closedBall, dist_zero_right] using (lt_of_le_of_lt (le_max_left _ _) hn).le⟩
  have m2 : z + direction t ∈ T n := ⟨h2, by
    simpa only [Metric.mem_closedBall, dist_zero_right] using (lt_of_le_of_lt (le_max_right _ _) hn).le⟩
  have h0 := hz n
  simp [Set.indicator_of_mem m1, Set.indicator_of_mem m2] at h0

lemma density_unitFree (hw : ∀ᵐ p ∂(volume : Measure ℂ).prod angularMeasure,
      h p.1 * h (p.1 + direction p.2) = 0) {x y : ℂ} (hxy : ‖x - y‖ = 1)
    (hx : DensityOne {z | 0 < h z} x) : ¬ DensityOne {z | 0 < h z} y := by
  let u := y - x
  obtain ⟨t, ht⟩ := direction_exists (u := u) (by simpa only [u, norm_sub_rev] using hxy)
  have hA0 : MeasurableSet {z | 0 < h z} := measurableSet_lt measurable_const hh
  have hd : AEDisjoint volume {z | 0 < h z} ((fun z : ℂ => z + u) ⁻¹' {z | 0 < h z}) := by
    apply (measure_eq_zero_iff_ae_notMem).mpr
    filter_upwards [weak_directions h hh hw t] with z hz
    rintro ⟨h1, h2⟩
    exact hz ⟨h1, by rw [ht]; exact h2⟩
  have hh2 := densityOne_disjoint (hA0.preimage (measurable_id.add_const u)) hd hx
  simp only [id_eq] at hh2
  rw [densityOne_translate] at hh2
  simpa only [u, add_sub_cancel] using hh2

theorem exists_unitFree_of_field (h0 : ∀ x, 0 ≤ h x) (h1 : ∀ x, h x ≤ 1)
    (hw : ∀ᵐ p ∂(volume : Measure ℂ).prod angularMeasure, h p.1 * h (p.1 + direction p.2) = 0)
    {c : ℝ} (hc : ENNReal.ofReal c ≤ limsup (fun m : ℕ =>
      (∫⁻ x in square m, ENNReal.ofReal (h x)) / volume (square m)) atTop) :
    ∃ A : Set ℂ, MeasurableSet A ∧ UnitFree A ∧ c ≤ upperDensity A := by
  set A0 : Set ℂ := {z | 0 < h z} with hA0def
  have hA0 : MeasurableSet A0 := measurableSet_lt measurable_const hh
  -- density points
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
  · -- density
    have hAQ : ∀ m : ℕ, volume (A ∩ square m) = volume (A0 ∩ square m) := by
      intro m
      apply measure_congr
      have : A0 ∩ square m =ᵐ[volume] (A0 ∩ square m) \ N := (sdiff_null_ae_eq_self hN0).symm
      refine EventuallyEq.trans ?_ this.symm
      rw [hAdef, inter_sdiff_right_comm]
    let a : ℕ → ℝ≥0∞ := fun m => volume (A ∩ square m) / volume (square m)
    have ha1 : ∀ m, a m ≤ 1 := fun m =>
      ENNReal.div_le_of_le_mul (by rw [one_mul]; exact measure_mono inter_subset_right)
    have hle : ∀ m : ℕ, (∫⁻ x in square m, ENNReal.ofReal (h x)) / volume (square m) ≤ a m := by
      intro m
      have hI : ∫⁻ x in square m, ENNReal.ofReal (h x) ≤ volume (A ∩ square m) := by
        calc ∫⁻ x in square m, ENNReal.ofReal (h x) ≤ ∫⁻ x in square m, A0.indicator 1 x := by
              apply lintegral_mono
              intro x
              by_cases hx : x ∈ A0
              · rw [Set.indicator_of_mem hx]; exact ENNReal.ofReal_le_one.mpr (h1 x)
              · have : h x = 0 := le_antisymm (not_lt.mp hx) (h0 x)
                simp [Set.indicator_of_notMem hx, this]
          _ = volume (A0 ∩ square m) := by
              rw [lintegral_indicator_one hA0, Measure.restrict_apply hA0]
          _ = volume (A ∩ square m) := (hAQ m).symm
      exact ENNReal.div_le_div_right hI _
    have hlim : ENNReal.ofReal c ≤ limsup a atTop :=
      hc.trans (limsup_le_limsup (Eventually.of_forall hle))
    have hreal : upperDensity A = (limsup a atTop).toReal := by
      unfold upperDensity
      rw [← ENNReal.limsup_toReal_eq ENNReal.one_ne_top (Eventually.of_forall ha1)]
      congr 1
      funext m
      simp only [a, ENNReal.toReal_div]
    rw [hreal]
    exact (ENNReal.ofReal_le_iff_le_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top
      (limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall ha1)))).mp hlim

end

end Erdos1070.Transfer
