import Erdos1070.Defs
import Erdos1070.TransferFolner
import OAI.Geometry.PlaneColoring.BorelTransfer

/-!
# The space of independent subsets of `E` and an invariant law with `P(0 ∈ ω) ≥ α*`

`Space` is the compact space of subsets of the algebraic plane `E` with no two points at
distance `1`.  We build a positive normalized functional on `C(Space, ℝ)`, invariant under
all translations by `E` and rotations by `K`, whose value on `1[0 ∈ ω]` is at least `alphaStar`:

* stage 1: an ultrafilter limit of uniform averages of `φ (J_N - z)` over `z` in Følner sets
  `F_N ⊆ E`, with `J_N ⊆ F_N` a largest unit-free subset (`|J_N| ≥ α* |F_N|`);
* stage 2: the invariant mean (OAI) over the rotation group `Rot`.

The measure is then obtained by the Riesz–Markov–Kakutani theorem, as in OAI `StationaryMean`.
-/

namespace Erdos1070.Transfer

open OAI OAI.PlaneFiveColor.Spectral MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

noncomputable section

/-! ## The space -/

def Indep (ω : E → Bool) : Prop := ∀ x y : E, ‖(x:ℂ)-(y:ℂ)‖ = 1 → ¬ (ω x = true ∧ ω y = true)

abbrev Space := {ω : E → Bool // Indep ω}

lemma closed_indep : IsClosed {ω : E → Bool | Indep ω} := by
  unfold Indep
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun (x:E) => isClosed_iInter fun (y:E) => isClosed_iInter fun _ => ?_
  have hc : Continuous (fun ω : E → Bool => (ω x,ω y)) := (continuous_apply x).prodMk (continuous_apply y)
  exact (isClosed_discrete {p : Bool × Bool | ¬ (p.1 = true ∧ p.2 = true)}).preimage hc

instance : CompactSpace Space := isCompact_iff_compactSpace.mp closed_indep.isCompact

def trans (a : E) (ω : Space) : Space := ⟨fun x => ω.val (x+a),by
  intro x y h
  apply ω.property (x+a) (y+a)
  change ‖(x:ℂ)+(a:ℂ)-((y:ℂ)+(a:ℂ))‖ = 1
  simpa only [add_sub_add_right_eq_sub] using h⟩

def rotate (b : K) (ω : Space) : Space := ⟨fun x => ω.val (kCoeff b * x),by
  intro x y h
  apply ω.property (kCoeff b*x) (kCoeff b*y)
  change ‖(b.val:ℂ)*(x:ℂ)-(b.val:ℂ)*(y:ℂ)‖ = 1
  rw [← mul_sub,norm_mul,Circle.norm_coe,one_mul,h]⟩

@[simp] lemma trans_apply (a : E) (ω : Space) (x : E) : (trans a ω).val x = ω.val (x+a) := rfl
@[simp] lemma rotate_apply (b : K) (ω : Space) (x : E) : (rotate b ω).val x = ω.val (kCoeff b*x) := rfl

lemma trans_continuous (a : E) : Continuous (trans a) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun x => (continuous_apply (x+a)).comp continuous_subtype_val

lemma rotate_continuous (b : K) : Continuous (rotate b) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun x => (continuous_apply (kCoeff b*x)).comp continuous_subtype_val

@[simp] lemma trans_zero (ω : Space) : trans 0 ω = ω := by apply Subtype.ext; funext x; simp

lemma trans_add (a b : E) (ω : Space) : trans a (trans b ω) = trans (a+b) ω := by
  apply Subtype.ext; funext x; simp [add_assoc]

@[simp] lemma rotate_one (ω : Space) : rotate 1 ω = ω := by
  apply Subtype.ext
  funext x
  have h1 : kCoeff 1 = 1 := rfl
  simp [h1]

lemma rotate_mul (a b : K) (ω : Space) : rotate a (rotate b ω) = rotate (a*b) ω := by
  apply Subtype.ext
  funext x
  change ω.val (kCoeff b * (kCoeff a * x)) = ω.val (kCoeff (a*b)*x)
  have he : kCoeff (a*b) = kCoeff a * kCoeff b := by rfl
  rw [he]; ring_nf

lemma covariance (a : E) (b : K) (ω : Space) :
    trans a (rotate b ω) = rotate b (trans (kCoeff b*a) ω) := by
  apply Subtype.ext
  funext x
  simp only [trans_apply,rotate_apply,mul_add]

def transHomeo (a : E) : Space ≃ₜ Space where
  toFun := trans a
  invFun := trans (-a)
  left_inv ω := by rw [trans_add,neg_add_cancel,trans_zero]
  right_inv ω := by rw [trans_add,add_neg_cancel,trans_zero]
  continuous_toFun := trans_continuous a
  continuous_invFun := trans_continuous (-a)

def rotateHomeo (b : K) : Space ≃ₜ Space where
  toFun := rotate b
  invFun := rotate b⁻¹
  left_inv ω := by rw [rotate_mul,inv_mul_cancel,rotate_one]
  right_inv ω := by rw [rotate_mul,mul_inv_cancel,rotate_one]
  continuous_toFun := rotate_continuous b
  continuous_invFun := rotate_continuous b⁻¹

/-- The label `1[0 ∈ ω]` as a continuous function. -/
def label : C(Space, ℝ) :=
  ⟨fun ω => if ω.val 0 = true then 1 else 0, by
    have hc : Continuous (fun ω : Space => ω.val 0) :=
      (continuous_apply (0:E)).comp continuous_subtype_val
    exact (continuous_of_discreteTopology
      (f := fun b : Bool => if b = true then (1:ℝ) else 0)).comp hc⟩

@[simp] lemma label_apply (ω : Space) : label ω = if ω.val 0 = true then 1 else 0 := rfl

lemma label_rotate (b : K) (ω : Space) : label (rotate b ω) = label ω := by
  simp [mul_zero]

/-! ## Finite configurations -/

/-- A finite unit-free subset of `E`, as a point of `Space`. -/
def cfg (J : Finset E) (hJ : ∀ x ∈ J, ∀ y ∈ J, ‖(x:ℂ)-(y:ℂ)‖ ≠ 1) : Space :=
  ⟨fun x => decide (x ∈ J), by
    intro x y h ⟨hx, hy⟩
    exact hJ x (by simpa using hx) y (by simpa using hy) h⟩

lemma alphaStar_le_ratio (P : Finset ℂ) (hP : P.Nonempty) :
    alphaStar ≤ (indepNum P : ℝ) / P.card := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨Q, _, rfl⟩
    positivity
  · exact ⟨P, hP, rfl⟩

lemma exists_indepNum (P : Finset ℂ) :
    ∃ I ⊆ P, UnitFree (I : Set ℂ) ∧ I.card = indepNum P := by
  have hne : {m | ∃ I ⊆ P, UnitFree (I : Set ℂ) ∧ I.card = m}.Nonempty :=
    ⟨0, ∅, Finset.empty_subset _, by simp [UnitFree], rfl⟩
  have hbdd : BddAbove {m | ∃ I ⊆ P, UnitFree (I : Set ℂ) ∧ I.card = m} := by
    refine ⟨P.card, ?_⟩
    rintro m ⟨I, hI, _, rfl⟩
    exact Finset.card_le_card hI
  exact Nat.sSup_mem hne hbdd

lemma exists_large_indep (F : Finset E) (hF : F.Nonempty) :
    ∃ J ⊆ F, (∀ x ∈ J, ∀ y ∈ J, ‖(x:ℂ)-(y:ℂ)‖ ≠ 1) ∧ alphaStar * F.card ≤ J.card := by
  classical
  let P : Finset ℂ := F.map ⟨Subtype.val, Subtype.val_injective⟩
  have hP : P.Nonempty := hF.map
  obtain ⟨I, hIP, hIu, hIc⟩ := exists_indepNum P
  let J : Finset E := F.filter (fun x : E => (x:ℂ) ∈ I)
  have hJI : J.map ⟨Subtype.val, Subtype.val_injective⟩ = I := by
    ext z
    simp only [J, Finset.mem_map, Finset.mem_filter, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨x, ⟨_, hx⟩, rfl⟩; exact hx
    · intro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp (hIP hz)
      exact ⟨x, ⟨hx, hz⟩, rfl⟩
  refine ⟨J, Finset.filter_subset _ _, ?_, ?_⟩
  · intro x hx y hy
    exact hIu x (Finset.mem_filter.mp hx).2 y (Finset.mem_filter.mp hy).2
  · have hcard : J.card = indepNum P := by
      rw [← hIc, ← hJI, Finset.card_map]
    have hPc : P.card = F.card := Finset.card_map _
    have h := alphaStar_le_ratio P hP
    rw [hPc, ← hcard] at h
    have hpos : (0:ℝ) < F.card := by exact_mod_cast hF.card_pos
    rwa [le_div_iff₀ hpos] at h

/-! ## Stage 1: Følner averages -/

lemma sum_shift_diff {G : Type*} [AddCommGroup G] [DecidableEq G] (F : Finset G) (g : G → ℝ)
    {B : ℝ} (hg : ∀ z, |g z| ≤ B) (w : G) :
    |∑ z ∈ F, g (z+w) - ∑ z ∈ F, g z| ≤
      B * ((F.filter (fun z => z + w ∉ F)).card + (F.filter (fun z => z + (-w) ∉ F)).card) := by
  let e : G ↪ G := ⟨fun z => z + w, add_left_injective w⟩
  have h1 : ∑ z ∈ F, g (z+w) = ∑ y ∈ F.map e, g y := by
    rw [Finset.sum_map]; rfl
  have hm : ∀ y, y ∈ F.map e ↔ y + (-w) ∈ F := by
    intro y
    simp only [Finset.mem_map, e, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨z, hz, rfl⟩; simpa using hz
    · intro h; exact ⟨y + -w, h, by abel⟩
  have hA : F.map e \ F = (F.filter (fun z => z + w ∉ F)).map e := by
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_map, Finset.mem_filter, e, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hn⟩; exact ⟨z, ⟨hz, hn⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hn⟩, rfl⟩; exact ⟨⟨z, hz, rfl⟩, hn⟩
  have hB : F \ F.map e = F.filter (fun z => z + (-w) ∉ F) := by
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_filter, hm]
  rw [h1, ← Finset.sum_sdiff_sub_sum_sdiff, hA, hB]
  have hb0 : 0 ≤ B := (abs_nonneg _).trans (hg 0)
  calc
    _ ≤ |∑ y ∈ (F.filter (fun z => z + w ∉ F)).map e, g y| +
        |∑ y ∈ F.filter (fun z => z + (-w) ∉ F), g y| := abs_sub _ _
    _ ≤ ((F.filter (fun z => z + w ∉ F)).map e).card * B +
        (F.filter (fun z => z + (-w) ∉ F)).card * B := by
      gcongr
      · exact (Finset.abs_sum_le_sum_abs _ _).trans
          ((Finset.sum_le_card_nsmul _ _ B (fun y _ => hg y)).trans (by rw [nsmul_eq_mul]))
      · exact (Finset.abs_sum_le_sum_abs _ _).trans
          ((Finset.sum_le_card_nsmul _ _ B (fun y _ => hg y)).trans (by rw [nsmul_eq_mul]))
    _ = _ := by rw [Finset.card_map]; ring

section Stage1
open Classical

/-- Følner sets in `E`. -/
noncomputable def folner : ℕ → Finset E := (Folner.exists_folner (G := E)).choose

lemma folner_nonempty (N : ℕ) : (folner N).Nonempty :=
  (Folner.exists_folner (G := E)).choose_spec.1 N

lemma folner_tendsto (w : E) :
    Tendsto (fun N => (((folner N).filter (fun z => z + w ∉ folner N)).card : ℝ) / (folner N).card)
      atTop (𝓝 0) := by
  convert (Folner.exists_folner (G := E)).choose_spec.2 w <;> rfl

lemma exists_J (N : ℕ) : ∃ J ⊆ folner N, (∀ x ∈ J, ∀ y ∈ J, ‖(x:ℂ)-(y:ℂ)‖ ≠ 1) ∧
    alphaStar * (folner N).card ≤ J.card := exists_large_indep _ (folner_nonempty N)

noncomputable def bigJ (N : ℕ) : Finset E := (exists_J N).choose
lemma bigJ_sub (N : ℕ) : bigJ N ⊆ folner N := (exists_J N).choose_spec.1
lemma bigJ_free (N : ℕ) : ∀ x ∈ bigJ N, ∀ y ∈ bigJ N, ‖(x:ℂ)-(y:ℂ)‖ ≠ 1 :=
  (exists_J N).choose_spec.2.1
lemma bigJ_card (N : ℕ) : alphaStar * (folner N).card ≤ (bigJ N).card :=
  (exists_J N).choose_spec.2.2

noncomputable def base (N : ℕ) : Space := cfg (bigJ N) (bigJ_free N)

/-- Uniform average over the `N`-th Følner set. -/
noncomputable def seqAvg (φ : C(Space,ℝ)) (N : ℕ) : ℝ :=
  ((folner N).card : ℝ)⁻¹ * ∑ z ∈ folner N, φ (trans z (base N))

lemma seqAvg_abs_le (φ : C(Space,ℝ)) (N : ℕ) : |seqAvg φ N| ≤ ‖φ‖ := by
  have hpos : (0:ℝ) < (folner N).card := by exact_mod_cast (folner_nonempty N).card_pos
  rw [seqAvg, abs_mul, abs_inv, abs_of_pos hpos, inv_mul_le_iff₀ hpos]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  simpa [mul_comm] using Finset.sum_le_card_nsmul _ _ ‖φ‖
    (fun z _ => by simpa [Real.norm_eq_abs] using φ.norm_coe_le_norm (trans z (base N)))

/-- The ultrafilter used for the limits. -/
noncomputable def U : Ultrafilter ℕ := Ultrafilter.of atTop

lemma U_le : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le _

lemma seqAvg_has_limit (φ : C(Space,ℝ)) :
    ∃ r : ℝ, Tendsto (seqAvg φ) (U : Filter ℕ) (𝓝 r) := by
  have hb : (Ultrafilter.map (seqAvg φ) U : Filter ℝ) ≤ 𝓟 (Set.Icc (-‖φ‖) ‖φ‖) := by
    rw [Ultrafilter.coe_map, Filter.le_principal_iff, Filter.mem_map]
    apply Filter.Eventually.of_forall
    intro N
    exact abs_le.mp (seqAvg_abs_le φ N)
  obtain ⟨r, _, hr⟩ := isCompact_Icc.ultrafilter_le_nhds (Ultrafilter.map (seqAvg φ) U) hb
  exact ⟨r, hr⟩

/-- Stage-1 functional. -/
noncomputable def lim0 (φ : C(Space,ℝ)) : ℝ := (U : Filter ℕ).limUnder (seqAvg φ)

lemma tendsto_lim0 (φ : C(Space,ℝ)) : Tendsto (seqAvg φ) (U : Filter ℕ) (𝓝 (lim0 φ)) :=
  tendsto_nhds_limUnder (seqAvg_has_limit φ)

lemma lim0_add (φ ψ : C(Space,ℝ)) : lim0 (φ+ψ) = lim0 φ + lim0 ψ := by
  apply Tendsto.limUnder_eq
  convert (tendsto_lim0 φ).add (tendsto_lim0 ψ) using 1
  funext N
  simp only [seqAvg, ContinuousMap.add_apply, Finset.sum_add_distrib, Pi.add_apply, mul_add]

lemma lim0_smul (c : ℝ) (φ : C(Space,ℝ)) : lim0 (c • φ) = c * lim0 φ := by
  apply Tendsto.limUnder_eq
  convert (tendsto_lim0 φ).const_mul c using 1
  funext N
  simp only [seqAvg, ContinuousMap.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

lemma lim0_const (c : ℝ) : lim0 (ContinuousMap.const Space c) = c := by
  apply Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr
  intro N
  have hpos : (0:ℝ) < (folner N).card := by exact_mod_cast (folner_nonempty N).card_pos
  simp only [seqAvg, ContinuousMap.const_apply, Finset.sum_const, nsmul_eq_mul]
  field_simp

lemma lim0_nonneg (φ : C(Space,ℝ)) (hφ : 0 ≤ φ) : 0 ≤ lim0 φ := by
  apply ge_of_tendsto (tendsto_lim0 φ) (Filter.Eventually.of_forall fun N => ?_)
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun z _ => hφ _)

lemma lim0_abs_le (φ : C(Space,ℝ)) : |lim0 φ| ≤ ‖φ‖ :=
  le_of_tendsto (tendsto_lim0 φ).abs (Filter.Eventually.of_forall fun N => seqAvg_abs_le φ N)

lemma lim0_trans (w : E) (φ : C(Space,ℝ)) :
    lim0 (φ.comp ⟨trans w, trans_continuous w⟩) = lim0 φ := by
  have hz : Tendsto (fun N => seqAvg (φ.comp ⟨trans w, trans_continuous w⟩) N - seqAvg φ N)
      atTop (𝓝 0) := by
    have hb := ((folner_tendsto w).add (folner_tendsto (-w))).const_mul ‖φ‖
    simp only [add_zero, mul_zero] at hb
    apply squeeze_zero_norm _ hb
    intro N
    have hpos : (0:ℝ) < (folner N).card := by exact_mod_cast (folner_nonempty N).card_pos
    have hd := sum_shift_diff (folner N) (fun z => φ (trans z (base N)))
      (B := ‖φ‖) (fun z => by simpa [Real.norm_eq_abs] using φ.norm_coe_le_norm _) w
    have he : seqAvg (φ.comp ⟨trans w, trans_continuous w⟩) N - seqAvg φ N =
        ((folner N).card : ℝ)⁻¹ * (∑ z ∈ folner N, φ (trans (z+w) (base N)) -
          ∑ z ∈ folner N, φ (trans z (base N))) := by
      simp only [seqAvg, ContinuousMap.comp_apply, ContinuousMap.coe_mk, trans_add, add_comm w]
      ring
    rw [he, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hpos, inv_mul_le_iff₀ hpos]
    refine hd.trans (le_of_eq ?_)
    field_simp
  have h1 := (tendsto_lim0 φ).add (hz.mono_left U_le)
  simp only [add_zero, add_sub_cancel] at h1
  exact tendsto_nhds_unique (tendsto_lim0 _) h1

lemma lim0_label : alphaStar ≤ lim0 label := by
  apply ge_of_tendsto (tendsto_lim0 label) (Filter.Eventually.of_forall fun N => ?_)
  have hpos : (0:ℝ) < (folner N).card := by exact_mod_cast (folner_nonempty N).card_pos
  have hs : ∑ z ∈ folner N, label (trans z (base N)) = (bigJ N).card := by
    have : ∀ z, label (trans z (base N)) = if z ∈ bigJ N then 1 else 0 := by
      intro z
      simp [base, cfg]
    simp only [this]
    rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.inter_eq_right.mpr (bigJ_sub N)]
  rw [seqAvg, hs, le_inv_mul_iff₀ hpos, mul_comm]
  exact bigJ_card N

end Stage1

/-! ## Stage 2: averaging over rotations -/

noncomputable def ro (b : Rot) : Space → Space := rotate (rotMul b)

lemma ro_continuous (b : Rot) : Continuous (ro b) := rotate_continuous _

noncomputable def outer (φ : C(Space,ℝ)) : Rot →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun b => lim0 (φ.comp ⟨ro b, ro_continuous b⟩))
    continuous_of_discreteTopology ‖φ‖
    (fun b => (Real.norm_eq_abs _).le.trans ((lim0_abs_le _).trans
      (ContinuousMap.norm_le _ (norm_nonneg _) |>.mpr fun ω => φ.norm_coe_le_norm _)))

open PlaneFiveColor.InvariantMean in
/-- The full invariant functional. -/
noncomputable def average (φ : C(Space,ℝ)) : ℝ := mean (outer φ)

open PlaneFiveColor.InvariantMean

lemma outer_add (φ ψ : C(Space,ℝ)) : outer (φ+ψ) = outer φ + outer ψ := by
  refine BoundedContinuousFunction.ext fun b => ?_
  show lim0 ((φ+ψ).comp _) = lim0 (φ.comp _) + lim0 (ψ.comp _)
  rw [ContinuousMap.add_comp, lim0_add]

lemma outer_smul (c : ℝ) (φ : C(Space,ℝ)) : outer (c • φ) = c • outer φ := by
  refine BoundedContinuousFunction.ext fun b => ?_
  show lim0 ((c • φ).comp _) = c * lim0 (φ.comp _)
  rw [ContinuousMap.smul_comp, lim0_smul]

lemma average_add (φ ψ : C(Space,ℝ)) : average (φ+ψ) = average φ + average ψ := by
  simp only [average, outer_add, mean_add]

lemma average_smul (c : ℝ) (φ : C(Space,ℝ)) : average (c • φ) = c * average φ := by
  simp only [average, outer_smul, mean_smul]

lemma average_nonneg (φ : C(Space,ℝ)) (hφ : 0 ≤ φ) : 0 ≤ average φ :=
  mean_nonneg _ fun b => lim0_nonneg _ fun ω => by
    show (0:ℝ) ≤ φ (ro b ω)
    exact hφ (ro b ω)

lemma average_mono {φ ψ : C(Space,ℝ)} (h : φ ≤ ψ) : average φ ≤ average ψ := by
  have hp := average_nonneg (ψ - φ) (sub_nonneg.mpr h)
  have he : average (ψ - φ) = average ψ - average φ := by
    rw [sub_eq_add_neg, average_add, ← neg_one_smul ℝ φ, average_smul]; ring
  linarith

lemma average_const (c : ℝ) : average (ContinuousMap.const Space c) = c := by
  have ho : outer (ContinuousMap.const Space c) = BoundedContinuousFunction.const Rot c := by
    ext b
    exact lim0_const c
  rw [average, ho, mean_const]

lemma average_rotation (b : K) (φ : C(Space,ℝ)) :
    average (φ.comp ⟨rotate b, rotate_continuous b⟩) = average φ := by
  unfold average
  have he : outer (φ.comp ⟨rotate b, rotate_continuous b⟩) = shift (mulRot b) (outer φ) := by
    ext c
    change lim0 _ = lim0 _
    congr 1
    ext ω
    change φ (rotate b (rotate (rotMul c) ω)) = φ (rotate (rotMul (c + mulRot b)) ω)
    rw [rotate_mul]
    congr 2
    exact mul_comm _ _
  rw [he, mean_shift]

lemma average_translation (a : E) (φ : C(Space,ℝ)) :
    average (φ.comp ⟨trans a, trans_continuous a⟩) = average φ := by
  unfold average
  congr 1
  ext c
  change lim0 _ = lim0 _
  have he : (φ.comp ⟨trans a, trans_continuous a⟩).comp ⟨ro c, ro_continuous c⟩ =
      (φ.comp ⟨ro c, ro_continuous c⟩).comp
        ⟨trans (kCoeff (rotMul c) * a), trans_continuous _⟩ := by
    ext ω
    change φ (trans a (rotate (rotMul c) ω)) = φ (rotate (rotMul c) (trans _ ω))
    rw [covariance]
  rw [he, lim0_trans]

lemma average_label : alphaStar ≤ average label := by
  have ho : outer label = BoundedContinuousFunction.const Rot (lim0 label) := by
    ext c
    change lim0 _ = lim0 _
    congr 1
    ext ω
    exact label_rotate _ ω
  rw [average, ho, mean_const]
  exact lim0_label

/-! ## The measure -/

def functional : CompactlySupportedContinuousMap Space ℝ →ₚ[ℝ] ℝ where
  toFun f := average f.toContinuousMap
  map_add' f g := average_add f.toContinuousMap g.toContinuousMap
  map_smul' c f := average_smul c f.toContinuousMap
  monotone' _ _ h := average_mono h

noncomputable def measure : Measure Space := RealRMK.rieszMeasure functional

instance : IsFiniteMeasure measure := by dsimp [measure]; infer_instance
instance : measure.Regular := by dsimp [measure]; infer_instance

lemma integral_eq (f : C(Space,ℝ)) : ∫ x, f x ∂measure = average f :=
  RealRMK.integral_rieszMeasure functional (CompactlySupportedContinuousMap.continuousMapEquiv f)

instance : IsProbabilityMeasure measure := by
  have he := integral_eq (ContinuousMap.const Space 1)
  rw [average_const] at he
  change (∫ _ : Space, (1:ℝ) ∂measure) = 1 at he
  simp only [integral_const,smul_eq_mul,mul_one] at he
  constructor
  exact (ENNReal.toReal_eq_one_iff _).mp he

lemma preserving_of_average (s : Space ≃ₜ Space)
    (hav : ∀ f : C(Space,ℝ), average (f.comp ⟨s,s.continuous⟩) = average f) :
    MeasurePreserving s measure measure := by
  refine ⟨s.continuous.measurable,?_⟩
  have : (Measure.map s measure).Regular := Measure.Regular.map s
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  change (∫ x, f.toContinuousMap x ∂measure.map s) = ∫ x, f.toContinuousMap x ∂measure
  rw [integral_map s.continuous.measurable.aemeasurable f.continuous.measurable.aestronglyMeasurable]
  exact (integral_eq (f.toContinuousMap.comp ⟨s,s.continuous⟩)).trans
    ((hav f.toContinuousMap).trans (integral_eq f.toContinuousMap).symm)

lemma trans_preserving (a : E) : MeasurePreserving (trans a) measure measure :=
  preserving_of_average (transHomeo a) (fun f => average_translation a f)

lemma rotate_preserving (b : K) : MeasurePreserving (rotate b) measure measure :=
  preserving_of_average (rotateHomeo b) (fun f => average_rotation b f)

lemma integral_label : alphaStar ≤ ∫ ω, label ω ∂measure := by
  rw [integral_eq]; exact average_label

end

end Erdos1070.Transfer
