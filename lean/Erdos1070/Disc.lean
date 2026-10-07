import Erdos1070.Main
import Erdos1070.DiscSample

/-!
# Erdős #1070 with the disc definition of upper density

erdosproblems.com (#232, #1070) measures upper density on discs:
`δ̄(A) = limsup_{R→∞} λ(A ∩ B_R) / λ(B_R)`, with `R` real and `B_R` the open disc of radius `R`
about `0`.  We define this (`upperDensityBall`) and the corresponding `m1Ball`, and prove
`m1Ball = alphaStar`; hence `f(n)/n → m1Ball` and `m1Ball · n ≤ f(n)`.

* `≤`: Larman–Rogers with discs: all translates `P + x`, `x ∈ B_R`, lie in `B_{R+ρ}`.
* `≥`: the transfer construction, with the sampling (reverse Fatou) and density-point steps run
  along the discs `B_m`, `m ∈ ℕ` (`DiscSample`); the limsup over real `R` dominates the limsup
  over integer radii.
-/

namespace Erdos1070

open MeasureTheory Filter Topology

/-- Upper density along the open discs `B(0,R)`, `R → ∞` through the reals. -/
noncomputable def upperDensityBall (A : Set ℂ) : ℝ :=
  limsup (fun R : ℝ => (volume (A ∩ Metric.ball 0 R)).toReal /
    (volume (Metric.ball (0:ℂ) R)).toReal) atTop

/-- `m₁` with the disc definition of upper density. -/
noncomputable def m1Ball : ℝ :=
  sSup {d | ∃ A : Set ℂ, MeasurableSet A ∧ UnitFree A ∧ upperDensityBall A = d}

namespace Disc

/-- The disc density ratio. -/
noncomputable def ballRatio (A : Set ℂ) (R : ℝ) : ℝ :=
  (volume (A ∩ Metric.ball 0 R)).toReal / (volume (Metric.ball (0:ℂ) R)).toReal

lemma upperDensityBall_eq (A : Set ℂ) : upperDensityBall A = limsup (ballRatio A) atTop := rfl

lemma ballRatio_nonneg (A : Set ℂ) (R : ℝ) : 0 ≤ ballRatio A R := by
  unfold ballRatio; positivity

lemma ballRatio_le_one (A : Set ℂ) (R : ℝ) : ballRatio A R ≤ 1 := by
  unfold ballRatio
  rcases eq_or_ne (volume (Metric.ball (0:ℂ) R)).toReal 0 with h | h
  · rw [h, div_zero]; exact zero_le_one
  · apply div_le_one_of_le₀ _ ENNReal.toReal_nonneg
    exact ENNReal.toReal_mono measure_ball_lt_top.ne (measure_mono Set.inter_subset_right)

lemma upperDensityBall_le_one (A : Set ℂ) : upperDensityBall A ≤ 1 :=
  limsup_le_of_le (isCoboundedUnder_le_of_le atTop (ballRatio_nonneg A))
    (Eventually.of_forall (ballRatio_le_one A))

lemma volume_ball_toReal {R : ℝ} (hR : 0 ≤ R) :
    (volume (Metric.ball (0:ℂ) R)).toReal = R ^ 2 * Real.pi := by
  rw [Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hR,
    ENNReal.coe_toReal, NNReal.coe_real_pi]

/-- The limsup over real radii dominates the limsup over integer radii. -/
lemma limsup_nat_le (A : Set ℂ) :
    limsup (fun m : ℕ => ballRatio A m) atTop ≤ upperDensityBall A :=
  tendsto_natCast_atTop_atTop.limsup_comp_le_limsup (u := ballRatio A)
    (isCoboundedUnder_le_of_le _ (ballRatio_nonneg A))
    (isBoundedUnder_of ⟨1, ballRatio_le_one A⟩)

/-! ### Larman–Rogers with discs -/

section LR
open scoped Classical

lemma card_mul_volume_ball_le {A : Set ℂ} (hA : MeasurableSet A) (hu : UnitFree A)
    (P : Finset ℂ) {ρ : ℝ} (hρ : ∀ p ∈ P, ‖p‖ ≤ ρ) (R : ℝ) :
    (P.card : ENNReal) * volume (A ∩ Metric.ball 0 R) ≤
      (indepNum P : ENNReal) * volume (Metric.ball (0:ℂ) (R + ρ)) := by
  set M := Metric.ball (0:ℂ) (R + ρ)
  have hmeas : ∀ p : ℂ, MeasurableSet ((fun y => p + y) ⁻¹' A) :=
    fun p => hA.preimage (measurable_const_add p)
  have hterm : ∀ p ∈ P, volume (A ∩ Metric.ball 0 R) ≤
      volume ((fun y => p + y) ⁻¹' A ∩ M) := by
    intro p hp
    rw [← measure_preimage_add (μ := volume) p (A ∩ Metric.ball 0 R)]
    refine measure_mono ?_
    intro x hx
    simp only [Set.mem_preimage, Set.mem_inter_iff] at hx
    refine ⟨hx.1, ?_⟩
    have h1 := hx.2
    simp only [M, Metric.mem_ball, dist_zero_right] at h1 ⊢
    calc ‖x‖ = ‖(p + x) - p‖ := by ring_nf
      _ ≤ ‖p + x‖ + ‖p‖ := norm_sub_le _ _
      _ < R + ρ := by linarith [hρ p hp]
  have hsum : ∑ p ∈ P, volume ((fun y => p + y) ⁻¹' A ∩ M) =
      ∫⁻ x in M, ∑ p ∈ P, ((fun y => p + y) ⁻¹' A).indicator (1 : ℂ → ENNReal) x := by
    rw [lintegral_finsetSum]
    · refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [lintegral_indicator_one (hmeas p), Measure.restrict_apply (hmeas p)]
    · intro p _
      exact (measurable_one.indicator (hmeas p))
  have hint : ∫⁻ x in M, ∑ p ∈ P, ((fun y => p + y) ⁻¹' A).indicator (1 : ℂ → ENNReal) x ≤
      (indepNum P : ENNReal) * volume M := by
    rw [← setLIntegral_const]
    refine lintegral_mono (fun x => ?_)
    rw [sum_indicator_eq]
    exact Nat.cast_le.2 (by convert card_filter_translate_le hu P x)
  calc (P.card : ENNReal) * volume (A ∩ Metric.ball 0 R)
      = ∑ _p ∈ P, volume (A ∩ Metric.ball 0 R) := by simp
    _ ≤ ∑ p ∈ P, volume ((fun y => p + y) ⁻¹' A ∩ M) := Finset.sum_le_sum hterm
    _ ≤ _ := hsum ▸ hint

lemma card_mul_ballRatio_le {A : Set ℂ} (hA : MeasurableSet A) (hu : UnitFree A)
    (P : Finset ℂ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ∀ p ∈ P, ‖p‖ ≤ ρ) {R : ℝ} (hR : 0 < R) :
    (P.card : ℝ) * ballRatio A R ≤ (indepNum P : ℝ) * ((R + ρ) / R) ^ 2 := by
  have h := card_mul_volume_ball_le hA hu P hρ R
  have hfin : (indepNum P : ENNReal) * volume (Metric.ball (0:ℂ) (R + ρ)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) measure_ball_lt_top.ne
  have h' := ENNReal.toReal_mono hfin h
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    volume_ball_toReal (by linarith)] at h'
  unfold ballRatio
  rw [volume_ball_toReal hR.le, mul_div_assoc', div_le_iff₀ (by positivity)]
  calc (P.card : ℝ) * (volume (A ∩ Metric.ball 0 R)).toReal
      ≤ indepNum P * ((R + ρ) ^ 2 * Real.pi) := h'
    _ = _ := by field_simp

lemma tendsto_ratio_sq_real (ρ : ℝ) :
    Tendsto (fun R : ℝ => ((R + ρ) / R) ^ 2) atTop (𝓝 1) := by
  have h1 : Tendsto (fun R : ℝ => (1 + ρ / R) ^ 2) atTop (𝓝 ((1 + 0) ^ 2)) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)).pow 2
  simp only [add_zero, one_pow] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  congr 1; field_simp

/-- **Larman–Rogers, disc version.** -/
theorem upperDensityBall_mul_card_le (A : Set ℂ) (hA : MeasurableSet A) (hu : UnitFree A)
    (P : Finset ℂ) : upperDensityBall A * P.card ≤ indepNum P := by
  rcases P.eq_empty_or_nonempty with rfl | hP
  · simp
  have hn : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
  set ρ : ℝ := ∑ p ∈ P, ‖p‖
  have hρ0 : 0 ≤ ρ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hρ : ∀ p ∈ P, ‖p‖ ≤ ρ := fun p hp =>
    Finset.single_le_sum (f := fun q : ℂ => ‖q‖) (fun _ _ => norm_nonneg _) hp
  set g : ℝ → ℝ := fun R => (indepNum P : ℝ) / P.card * ((R + ρ) / R) ^ 2
  have hg : Tendsto g atTop (𝓝 ((indepNum P : ℝ) / P.card)) := by
    have := (tendsto_ratio_sq_real ρ).const_mul ((indepNum P : ℝ) / P.card)
    simpa [g] using this
  have hle : ∀ᶠ R in atTop, ballRatio A R ≤ g R := by
    filter_upwards [eventually_gt_atTop 0] with R hR
    have := card_mul_ballRatio_le hA hu P hρ0 hρ hR
    simp only [g]
    rw [div_mul_eq_mul_div, le_div_iff₀ hn]
    linarith
  have hlim : upperDensityBall A ≤ (indepNum P : ℝ) / P.card := by
    rw [upperDensityBall_eq, ← hg.limsup_eq]
    exact limsup_le_limsup hle
      (isCoboundedUnder_le_of_le atTop (ballRatio_nonneg A)) hg.isBoundedUnder_le
  rwa [le_div_iff₀ hn] at hlim

lemma upperDensityBall_le_alphaStar {A : Set ℂ} (hA : MeasurableSet A) (hu : UnitFree A) :
    upperDensityBall A ≤ alphaStar := by
  refine le_csInf ratioSet_nonempty ?_
  rintro r ⟨P, hP, rfl⟩
  have hn : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
  rw [le_div_iff₀ hn]
  exact upperDensityBall_mul_card_le A hA hu P

end LR

theorem m1Ball_le_alphaStar : m1Ball ≤ alphaStar := by
  refine csSup_le ⟨_, ∅, MeasurableSet.empty, by simp [UnitFree], rfl⟩ ?_
  rintro d ⟨A, hA, hu, rfl⟩
  exact upperDensityBall_le_alphaStar hA hu

/-! ### The transfer, measured on discs -/

theorem exists_unitFree_densityBall_ge :
    ∃ A : Set ℂ, MeasurableSet A ∧ UnitFree A ∧ alphaStar ≤ upperDensityBall A := by
  obtain ⟨H, hHm, hH01, hHmean, hHcor⟩ := Transfer.exists_field
  let Q : ℕ → Set ℂ := fun m => Metric.ball 0 (m : ℝ)
  have hQ0 : ∀ m, 1 ≤ m → volume (Q m) ≠ 0 := fun m hm =>
    (Metric.measure_ball_pos volume (0:ℂ) (by exact_mod_cast hm : (0:ℝ) < m)).ne'
  have hQt : ∀ m, volume (Q m) ≠ ⊤ := fun m => measure_ball_lt_top.ne
  obtain ⟨ω, hω1, hω2⟩ := Transfer.exists_good_sample_reg Transfer.measure Q hQ0 hQt hHm
    (fun p => (hH01 p).1) (fun p => (hH01 p).2) hHmean hHcor
  obtain ⟨A, hAm, hAu, hAd⟩ := Transfer.exists_unitFree_of_field_reg (fun x => H (x,ω))
    (hHm.comp (measurable_id.prodMk measurable_const)) Q (fun x => (hH01 _).1)
    (fun x => (hH01 _).2) hω1 hω2
  exact ⟨A, hAm, hAu, Transfer.integral_label.trans (hAd.trans (limsup_nat_le A))⟩

theorem alphaStar_le_m1Ball : alphaStar ≤ m1Ball := by
  obtain ⟨A, hAm, hAu, hAd⟩ := exists_unitFree_densityBall_ge
  refine hAd.trans (le_csSup ?_ ⟨A, hAm, hAu, rfl⟩)
  refine ⟨1, ?_⟩
  rintro d ⟨B, _, _, rfl⟩
  exact upperDensityBall_le_one B

end Disc

open Disc

theorem m1Ball_eq_alphaStar : m1Ball = alphaStar := le_antisymm m1Ball_le_alphaStar alphaStar_le_m1Ball

/-- The disc and square definitions of `m₁` agree. -/
theorem m1Ball_eq_m1 : m1Ball = m1 := m1Ball_eq_alphaStar.trans alphaStar_eq_m1

/-- **Main theorem, disc version.** `f(n)/n → m₁` with `m₁` defined via disc upper density. -/
theorem f_div_tendsto_m1Ball : Tendsto (fun n : ℕ => (f n : ℝ) / n) atTop (𝓝 m1Ball) := by
  simpa [m1Ball_eq_alphaStar] using f_div_tendsto_alphaStar

/-- Larman–Rogers lower bound, disc version: `m₁ n ≤ f(n)` for every `n`. -/
theorem m1Ball_mul_le_f (n : ℕ) : m1Ball * n ≤ f n := by
  simpa [m1Ball_eq_alphaStar] using f_ge_alphaStar n

end Erdos1070
