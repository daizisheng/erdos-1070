import Erdos1070.TransferSpace

/-!
# Koopman representation, projection onto continuous vectors, and the field

Single-label mirror of OAI `Representations` (LabelModel part) and `BorelTransfer`
for the label `f = 1[0 ∈ ω]` on the space of independent sets.  The only new ingredient
compared with OAI is the mean identity `E[T_x p] = E[f]`.
-/

namespace Erdos1070.Transfer

open OAI OAI.PlaneFiveColor.Spectral OAI.EuclideanFiveColor
open OAI.EuclideanFiveColor.ContinuousVectors MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate

noncomputable section

abbrev Hilbert := Lp ℂ 2 measure

def translation (a : E) : unitary (Hilbert →L[ℂ] Hilbert) :=
  Koopman.unitary measure (transHomeo a).toMeasurableEquiv (trans_preserving a)

def rotation (b : K) : unitary (Hilbert →L[ℂ] Hilbert) :=
  Koopman.unitary measure (rotateHomeo b).toMeasurableEquiv (rotate_preserving b)

lemma translation_apply (a : E) (v : Hilbert) :
    (translation a : Hilbert →L[ℂ] Hilbert) v =
      Lp.compMeasurePreserving (trans a) (trans_preserving a) v := rfl

lemma rotation_apply (b : K) (v : Hilbert) :
    (rotation b : Hilbert →L[ℂ] Hilbert) v =
      Lp.compMeasurePreserving (rotate b) (rotate_preserving b) v := rfl

def representation : DiscreteE →* unitary (Hilbert →L[ℂ] Hilbert) where
  toFun a := translation (Multiplicative.toAdd a)
  map_one' := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    change Lp.compMeasurePreserving (trans 0) (trans_preserving 0) v = v
    have he : trans 0 = id := funext trans_zero
    simp only [he,Lp.compMeasurePreserving_id_apply]
  map_mul' a b := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    change Lp.compMeasurePreserving (trans (Multiplicative.toAdd a+Multiplicative.toAdd b)) _ v =
      Lp.compMeasurePreserving (trans (Multiplicative.toAdd a)) _
        (Lp.compMeasurePreserving (trans (Multiplicative.toAdd b)) _ v)
    rw [← Lp.compMeasurePreserving_comp_apply]
    congr 2
    funext x
    exact (congrArg (fun c => trans c x) (add_comm _ _)).trans (trans_add _ _ x).symm

lemma op_apply (a : E) (v : Hilbert) : op representation a v =
    Lp.compMeasurePreserving (trans a) (trans_preserving a) v := rfl

lemma rotation_covariance (b : K) (a : E) (v : Hilbert) :
    (rotation b : Hilbert →L[ℂ] Hilbert) (op representation a v) =
      op representation (kCoeff b*a) ((rotation b : Hilbert →L[ℂ] Hilbert) v) := by
  simp only [rotation_apply,op_apply,← Lp.compMeasurePreserving_comp_apply]
  congr 2
  funext x
  exact covariance a b x

/-! ## The label vector -/

def labelValue (η : Space) : ℂ := if η.val 0 = true then 1 else 0

lemma labelValue_measurable : Measurable labelValue := by
  apply Measurable.ite _ measurable_const measurable_const
  exact (measurableSet_singleton true).preimage (show Measurable (fun η : Space => η.val 0) from
    ((continuous_apply (0 : E)).comp continuous_subtype_val).measurable)

lemma label_memLp : MemLp labelValue 2 measure := by
  refine MemLp.of_bound labelValue_measurable.aestronglyMeasurable 1 ?_
  exact .of_forall fun η => by dsimp [labelValue]; split_ifs <;> simp

abbrev labelVector : Hilbert := label_memLp.toLp labelValue

lemma label_ae : labelVector =ᵐ[measure] labelValue := label_memLp.coeFn_toLp

lemma label_rotation_fixed (b : K) :
    (rotation b : Hilbert →L[ℂ] Hilbert) labelVector = labelVector := by
  rw [rotation_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving labelVector (rotate_preserving b),
    (rotate_preserving b).quasiMeasurePreserving.ae label_ae, label_ae] with η h1 h2 h3
  simp only [Function.comp_apply,h1,h2,h3,labelValue,rotate_apply,mul_zero]

lemma label_unit_correlation (b : K) :
    ⟪labelVector,op representation (kCoeff b) labelVector⟫_ℂ = 0 := by
  rw [op_apply,L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [label_ae,Lp.coeFn_compMeasurePreserving labelVector (trans_preserving (kCoeff b)),
    (trans_preserving (kCoeff b)).quasiMeasurePreserving.ae label_ae] with η h1 h2 h3
  simp only [h1,h2,Function.comp_apply,h3,labelValue,trans_apply,zero_add]
  have hp := η.property 0 (kCoeff b) (by
    change ‖(0 : ℂ)-(b.val:ℂ)‖ = 1
    rw [zero_sub,norm_neg]
    exact Circle.norm_coe b.val)
  by_cases h0 : η.val 0 = true
  · have h1 : η.val (kCoeff b) ≠ true := fun h => hp ⟨h0, h⟩
    simp [h0,h1]
  · simp [h0]

instance continuous_complete : CompleteSpace (space (A := E) representation) :=
  (isClosed_space (A := E) representation).completeSpace_coe

def projected : Hilbert := (space (A := E) representation).starProjection labelVector

lemma projected_range : ∀ᵐ η ∂measure,
    (projected η).im = 0 ∧ 0 ≤ (projected η).re ∧ (projected η).re ≤ 1 := by
  apply projection_range measure representation trans trans_preserving op_apply
  filter_upwards [label_ae] with η h
  rw [h]
  dsimp [labelValue]
  split_ifs <;> norm_num

lemma projected_rotation_fixed (b : K) :
    (rotation b : Hilbert →L[ℂ] Hilbert) projected = projected := by
  exact projection_covariance_fixed representation (rotation b)
    (Homeomorph.mulLeft₀ (kCoeff b) (kCoeff_ne_zero b)) (mul_zero _)
    (rotation_covariance b) _ (label_rotation_fixed b)

lemma projected_unit_correlation (b : K) :
    ⟪projected,op representation (kCoeff b) projected⟫_ℂ = 0 := by
  have hb := residual_fourier representation rotation rotation_covariance
    (labelVector-projected)
    ((space (A := E) representation).sub_starProjection_mem_orthogonal labelVector)
    (fun b => by rw [map_sub,label_rotation_fixed,projected_rotation_fixed]) (kCoeff b)
    (kCoeff_ne_zero b)
  exact (projection_coefficient representation labelVector (kCoeff b) hb).trans
    (label_unit_correlation b)

/-! ## The constant vector and the mean -/

def oneVector : Hilbert := (memLp_const (1 : ℂ)).toLp (fun _ : Space => (1 : ℂ))

lemma one_ae : oneVector =ᵐ[measure] fun _ => (1 : ℂ) := MemLp.coeFn_toLp _

lemma one_fixed (a : E) : op representation a oneVector = oneVector := by
  rw [op_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving oneVector (trans_preserving a),
    (trans_preserving a).quasiMeasurePreserving.ae one_ae,one_ae] with η h1 h2 h3
  exact h1.trans (h2.trans h3.symm)

lemma one_continuous : oneVector ∈ space (A := E) representation := by
  change Tendsto (fun a : E => op representation a oneVector) (𝓝 0) (𝓝 oneVector)
  simpa only [one_fixed] using
    (tendsto_const_nhds : Tendsto (fun _ : E => oneVector) (𝓝 0) (𝓝 oneVector))

lemma projected_continuous : projected ∈ space (A := E) representation :=
  (space (A := E) representation).starProjection_apply_mem _

lemma inner_one_projected : ⟪oneVector, projected⟫_ℂ = ⟪oneVector, labelVector⟫_ℂ := by
  rw [projected, ← Submodule.inner_starProjection_left_eq_right,
    (space (A := E) representation).starProjection_eq_self_iff.mpr one_continuous]

lemma inner_one_re (v : Hilbert) : (⟪oneVector, v⟫_ℂ).re = ∫ η, (v η).re ∂measure := by
  rw [L2.inner_def]
  change RCLike.re (∫ a, ⟪oneVector a, v a⟫_ℂ ∂measure) = _
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) oneVector v)]
  apply integral_congr_ae
  filter_upwards [one_ae] with η h
  simp [h]

lemma inner_one_label : (⟪oneVector, labelVector⟫_ℂ).re = ∫ η, label η ∂measure := by
  rw [inner_one_re]
  apply integral_congr_ae
  filter_upwards [label_ae] with η h
  rw [h]
  simp only [labelValue, label_apply]
  split_ifs <;> simp

/-! ## The continuous field `x ↦ T_x p` -/

def fieldVector (x : ℂ) : Hilbert := orbitExtension representation projected x

lemma fieldVector_continuous : Continuous fieldVector :=
  orbitExtension_continuous _ projected_continuous

lemma fieldVector_algebraic (a : E) : fieldVector (a : ℂ) = op representation a projected :=
  orbitExtension_eq _ projected_continuous a

lemma fieldVector_range (x : ℂ) : ∀ᵐ η ∂measure,
    (fieldVector x η).im = 0 ∧ 0 ≤ (fieldVector x η).re ∧ (fieldVector x η).re ≤ 1 := by
  have he : clamp_lipschitz.compLp clamp_zero (fieldVector x) = fieldVector x := by
    refine dense_E.denseRange_val.induction_on x (isClosed_eq
      ((clamp_lipschitz.continuous_compLp clamp_zero).comp fieldVector_continuous)
        fieldVector_continuous) ?_
    intro a
    rw [fieldVector_algebraic,op_apply]
    apply Lp.ext
    filter_upwards [clamp_lipschitz.coeFn_compLp clamp_zero
        (Lp.compMeasurePreserving (trans a) (trans_preserving a) projected),
      Lp.coeFn_compMeasurePreserving projected (trans_preserving a),
      (trans_preserving a).quasiMeasurePreserving.ae projected_range] with η h1 h2 h3
    simp only [Function.comp_apply] at h1 h2
    rw [h1,h2]
    exact clamp_eq h3
  have ha := clamp_lipschitz.coeFn_compLp clamp_zero (fieldVector x)
  rw [he] at ha
  filter_upwards [ha] with η hη
  exact hη.symm ▸ clamp_range _

lemma fieldVector_unit_correlation (x : ℂ) (u : Circle) :
    ⟪fieldVector x,fieldVector (x+u)⟫_ℂ = 0 := by
  rw [show ⟪fieldVector x,fieldVector (x+u)⟫_ℂ = ⟪projected,fieldVector u⟫_ℂ from
    orbitExtension_inner _ projected_continuous projected_continuous x u]
  apply circle_closed_induction (isClosed_eq (continuous_const.inner fieldVector_continuous)
    continuous_const) _ u
  intro b
  change ⟪projected,fieldVector ((kCoeff b : E) : ℂ)⟫_ℂ = 0
  rw [fieldVector_algebraic]
  exact projected_unit_correlation b

lemma fieldVector_inner_one (x : ℂ) : ⟪oneVector, fieldVector x⟫_ℂ = ⟪oneVector, projected⟫_ℂ := by
  refine dense_E.denseRange_val.induction_on x
    (isClosed_eq (continuous_const.inner fieldVector_continuous) continuous_const) ?_
  intro a
  rw [fieldVector_algebraic]
  conv_lhs => rw [← one_fixed a]
  exact Unitary.inner_map_map (representation (Multiplicative.ofAdd a)) oneVector projected

lemma fieldVector_mean (x : ℂ) : ∫ η, (fieldVector x η).re ∂measure = ∫ η, label η ∂measure := by
  rw [← inner_one_re, fieldVector_inner_one, inner_one_projected, inner_one_label]

/-! ## A jointly measurable `[0,1]`-valued field -/

theorem exists_field : ∃ H : ℂ × Space → ℝ, Measurable H ∧ (∀ p, 0 ≤ H p ∧ H p ≤ 1) ∧
    (∀ x : ℂ, ∫ η, H (x,η) ∂measure = ∫ η, label η ∂measure) ∧
    (∀ x : ℂ, ∀ u : Circle, ∀ᵐ η ∂measure, H (x,η) * H (x+u,η) = 0) := by
  obtain ⟨F, hFm, hFae⟩ := exists_measurable_field measure fieldVector fieldVector_continuous
  let H : ℂ × Space → ℝ := fun p => max 0 (min 1 (F p).re)
  have hHae : ∀ x : ℂ, ∀ᵐ η ∂measure, H (x,η) = (fieldVector x η).re := by
    intro x
    filter_upwards [hFae x, fieldVector_range x] with η h1 h2
    simp only [H]
    rw [h1, min_eq_right h2.2.2, max_eq_right h2.2.1]
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · exact measurable_const.max (measurable_const.min (Complex.continuous_re.measurable.comp hFm))
  · intro p
    exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  · intro x
    rw [← fieldVector_mean x]
    exact integral_congr_ae (hHae x)
  · intro x u
    have hz := positive_orthogonal measure (fieldVector x) (fieldVector (x+u))
      ((fieldVector_range x).mono fun _ h => ⟨h.1,h.2.1⟩)
      ((fieldVector_range (x+u)).mono fun _ h => ⟨h.1,h.2.1⟩)
      (fieldVector_unit_correlation x u)
    filter_upwards [hHae x, hHae (x+u), hz] with η h1 h2 h3
    rw [h1, h2]
    exact h3

end

end Erdos1070.Transfer
