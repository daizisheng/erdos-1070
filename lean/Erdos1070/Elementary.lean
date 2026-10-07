import Mathlib
import Erdos1070.Defs

/-!
# Erdős #1070: elementary part

* `f n ≥ α* n`, `f n / n → α*` (PROOF.md §2);
* Larman–Rogers `m₁ ≤ α*` (PROOF.md §3).
-/

namespace Erdos1070

open MeasureTheory Filter Topology

/-! ### Basic facts on `indepNum` -/

/-- The set whose supremum defines `indepNum`. -/
def indepSet (P : Finset ℂ) : Set ℕ := {m | ∃ I ⊆ P, UnitFree (I : Set ℂ) ∧ I.card = m}

lemma indepNum_eq (P : Finset ℂ) : indepNum P = sSup (indepSet P) := rfl

lemma indepSet_bddAbove (P : Finset ℂ) : BddAbove (indepSet P) := by
  refine ⟨P.card, ?_⟩
  rintro m ⟨I, hI, -, rfl⟩
  exact Finset.card_le_card hI

lemma indepSet_nonempty (P : Finset ℂ) : (indepSet P).Nonempty :=
  ⟨0, ∅, Finset.empty_subset _, by simp [UnitFree], rfl⟩

lemma le_indepNum {P I : Finset ℂ} (hI : I ⊆ P) (hu : UnitFree (I : Set ℂ)) :
    I.card ≤ indepNum P :=
  le_csSup (indepSet_bddAbove P) ⟨I, hI, hu, rfl⟩

lemma exists_indep (P : Finset ℂ) :
    ∃ I ⊆ P, UnitFree (I : Set ℂ) ∧ I.card = indepNum P :=
  Nat.sSup_mem (indepSet_nonempty P) (indepSet_bddAbove P)

lemma indepNum_le_card (P : Finset ℂ) : indepNum P ≤ P.card := by
  obtain ⟨I, hI, -, h⟩ := exists_indep P
  rw [← h]; exact Finset.card_le_card hI

lemma UnitFree.mono {S T : Set ℂ} (h : UnitFree T) (hST : S ⊆ T) : UnitFree S :=
  fun x hx y hy => h x (hST hx) y (hST hy)

lemma indepNum_mono {P Q : Finset ℂ} (hPQ : P ⊆ Q) : indepNum P ≤ indepNum Q := by
  obtain ⟨I, hI, hu, h⟩ := exists_indep P
  rw [← h]; exact le_indepNum (hI.trans hPQ) hu

lemma indepNum_union_le (P Q : Finset ℂ) : indepNum (P ∪ Q) ≤ indepNum P + indepNum Q := by
  obtain ⟨I, hI, hu, h⟩ := exists_indep (P ∪ Q)
  rw [← h]
  have h1 : (I.filter (· ∈ P)).card ≤ indepNum P :=
    le_indepNum (fun x hx => (Finset.mem_filter.1 hx).2)
      (hu.mono (by intro x hx; exact (Finset.mem_filter.1 hx).1))
  have h2 : (I.filter (fun x => x ∉ P)).card ≤ indepNum Q := by
    refine le_indepNum (fun x hx => ?_) (hu.mono (by intro x hx; exact (Finset.mem_filter.1 hx).1))
    obtain ⟨hxI, hxP⟩ := Finset.mem_filter.1 hx
    rcases Finset.mem_union.1 (hI hxI) with h | h
    · exact absurd h hxP
    · exact h
  have := Finset.card_filter_add_card_filter_not (s := I) (fun x => x ∈ P)
  omega

lemma indepNum_translate_le (P : Finset ℂ) (t : ℂ) :
    indepNum (P.image (· + t)) ≤ indepNum P := by
  obtain ⟨I, hI, hu, h⟩ := exists_indep (P.image (· + t))
  rw [← h]
  have hinj : Function.Injective (fun x : ℂ => x - t) := sub_left_injective
  have hc : (I.image (fun x => x - t)).card = I.card := Finset.card_image_of_injective _ hinj
  rw [← hc]
  refine le_indepNum ?_ ?_
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 (hI hx)
    simpa using hp
  · intro x hx y hy
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have := hu a ha b hb
    simpa using this

lemma indepNum_translate (P : Finset ℂ) (t : ℂ) :
    indepNum (P.image (· + t)) = indepNum P := by
  refine le_antisymm (indepNum_translate_le P t) ?_
  have := indepNum_translate_le (P.image (· + t)) (-t)
  rw [Finset.image_image] at this
  simpa using this

/-! ### Basic facts on `f` and `alphaStar` -/

def fSet (n : ℕ) : Set ℕ := {m | ∃ P : Finset ℂ, P.card = n ∧ indepNum P = m}

lemma f_eq (n : ℕ) : f n = sInf (fSet n) := rfl

lemma fSet_nonempty (n : ℕ) : (fSet n).Nonempty := by
  obtain ⟨P, hP⟩ := Infinite.exists_subset_card_eq ℂ n
  exact ⟨_, P, hP, rfl⟩

/-- `f n` is attained. -/
lemma exists_f (n : ℕ) : ∃ P : Finset ℂ, P.card = n ∧ indepNum P = f n :=
  Nat.sInf_mem (fSet_nonempty n)

lemma f_le_indepNum {P : Finset ℂ} : f P.card ≤ indepNum P :=
  Nat.sInf_le ⟨P, rfl, rfl⟩

lemma f_le (n : ℕ) : f n ≤ n := by
  obtain ⟨P, hP, h⟩ := exists_f n
  rw [← h, ← hP]; exact indepNum_le_card P

/-- If `Q` has at least `n` points, `f n ≤ indepNum Q`. -/
lemma f_le_indepNum_of_le {n : ℕ} {Q : Finset ℂ} (h : n ≤ Q.card) : f n ≤ indepNum Q := by
  obtain ⟨P, hPQ, hP⟩ := Finset.exists_subset_card_eq h
  rw [← hP]; exact f_le_indepNum.trans (indepNum_mono hPQ)

def ratioSet : Set ℝ := {r | ∃ P : Finset ℂ, P.Nonempty ∧ r = (indepNum P : ℝ) / P.card}

lemma alphaStar_eq : alphaStar = sInf ratioSet := rfl

lemma ratioSet_nonempty : ratioSet.Nonempty := ⟨_, {0}, Finset.singleton_nonempty 0, rfl⟩

lemma ratioSet_nonneg : ∀ r ∈ ratioSet, 0 ≤ r := by
  rintro r ⟨P, -, rfl⟩; positivity

lemma ratioSet_bddBelow : BddBelow ratioSet := ⟨0, ratioSet_nonneg⟩

lemma alphaStar_le_ratio {P : Finset ℂ} (hP : P.Nonempty) :
    alphaStar ≤ (indepNum P : ℝ) / P.card :=
  csInf_le ratioSet_bddBelow ⟨P, hP, rfl⟩

lemma alphaStar_nonneg : 0 ≤ alphaStar := le_csInf ratioSet_nonempty ratioSet_nonneg

lemma ratio_le_one (P : Finset ℂ) : (indepNum P : ℝ) / P.card ≤ 1 := by
  rcases P.eq_empty_or_nonempty with rfl | hP
  · simp
  · rw [div_le_one (by exact_mod_cast hP.card_pos)]
    exact_mod_cast indepNum_le_card P

lemma alphaStar_le_one : alphaStar ≤ 1 :=
  (alphaStar_le_ratio (Finset.singleton_nonempty (0 : ℂ))).trans (ratio_le_one _)

lemma alphaStar_mul_card_le (P : Finset ℂ) : alphaStar * P.card ≤ indepNum P := by
  rcases P.eq_empty_or_nonempty with rfl | hP
  · simp
  · have hc : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
    have := alphaStar_le_ratio hP
    rwa [le_div_iff₀ hc] at this

theorem f_ge_alphaStar (n : ℕ) : alphaStar * n ≤ f n := by
  obtain ⟨P, hP, h⟩ := exists_f n
  rw [← h, ← hP]; exact alphaStar_mul_card_le P

/-! ### Upper bound: disjoint far-apart translates -/

/-- A real spacing larger than the horizontal spread of `P₀`. -/
noncomputable def spacing (P₀ : Finset ℂ) : ℝ := 1 + 2 * ∑ p ∈ P₀, |p.re|

lemma abs_re_sub_lt_spacing {P₀ : Finset ℂ} {p q : ℂ} (hp : p ∈ P₀) (hq : q ∈ P₀) :
    |p.re - q.re| < spacing P₀ := by
  have h1 : |p.re| ≤ ∑ x ∈ P₀, |x.re| :=
    Finset.single_le_sum (f := fun x : ℂ => |x.re|) (fun _ _ => abs_nonneg _) hp
  have h2 : |q.re| ≤ ∑ x ∈ P₀, |x.re| :=
    Finset.single_le_sum (f := fun x : ℂ => |x.re|) (fun _ _ => abs_nonneg _) hq
  unfold spacing
  calc |p.re - q.re| ≤ |p.re| + |q.re| := abs_sub _ _
    _ < _ := by linarith

/-- `k` translates of `P₀` spaced along the real axis. -/
noncomputable def translates (P₀ : Finset ℂ) (k : ℕ) : Finset ℂ :=
  (Finset.range k).biUnion (fun i => P₀.image (· + ((i : ℝ) * spacing P₀ : ℝ)))

lemma indepNum_translates_le (P₀ : Finset ℂ) (k : ℕ) :
    indepNum (translates P₀ k) ≤ k * indepNum P₀ := by
  induction k with
  | zero =>
    simp only [translates, Finset.range_zero, Finset.biUnion_empty, zero_mul]
    exact (indepNum_le_card ∅).trans (by simp)
  | succ k ih =>
    unfold translates at ih ⊢
    rw [Finset.range_add_one, Finset.biUnion_insert]
    refine (indepNum_union_le _ _).trans ?_
    rw [indepNum_translate]
    rw [Nat.succ_mul]; omega

lemma card_translates (P₀ : Finset ℂ) (k : ℕ) :
    (translates P₀ k).card = k * P₀.card := by
  unfold translates
  rw [Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (fun i _ => Finset.card_image_of_injective P₀ (add_left_injective _))]
    simp
  · intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro z hzi hzj
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hzi
    obtain ⟨q, hq, hpq⟩ := Finset.mem_image.1 hzj
    have hre := congrArg Complex.re hpq
    simp only [Complex.add_re, Complex.ofReal_re] at hre
    have hlt := abs_re_sub_lt_spacing hq hp
    have hS : 0 < spacing P₀ := by
      unfold spacing
      have : 0 ≤ ∑ p ∈ P₀, |p.re| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      linarith
    have hij' : (1 : ℝ) ≤ |(i : ℝ) - j| := by
      rcases lt_or_gt_of_ne hij with h | h
      · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
        rw [abs_of_nonpos (by linarith)]; linarith
      · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
        rw [abs_of_nonneg (by linarith)]; linarith
    have heq : q.re - p.re = ((i : ℝ) - j) * spacing P₀ := by linarith
    rw [heq, abs_mul, abs_of_pos hS] at hlt
    have := mul_le_mul_of_nonneg_right hij' hS.le
    linarith

lemma f_le_of_ratio {P₀ : Finset ℂ} (hP₀ : P₀.Nonempty) {N : ℕ} (hN : 0 < N) :
    (f N : ℝ) / N ≤ (indepNum P₀ : ℝ) / P₀.card + (indepNum P₀ : ℝ) / N := by
  obtain ⟨s, hs⟩ : ∃ s, s = P₀.card := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = indepNum P₀ := ⟨_, rfl⟩
  rw [← hs, ← ha]
  have hs0 : 0 < s := hs ▸ hP₀.card_pos
  obtain ⟨k, hkdef⟩ : ∃ k, k = N / s + 1 := ⟨_, rfl⟩
  have hk : N ≤ (translates P₀ k).card := by
    rw [card_translates, ← hs, hkdef]
    have := Nat.lt_div_mul_add (a := N) hs0
    rw [Nat.add_mul, one_mul]; omega
  have h1 : f N ≤ k * a := ha ▸ (f_le_indepNum_of_le hk).trans (indepNum_translates_le P₀ k)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsr : (0 : ℝ) < s := by exact_mod_cast hs0
  have hk' : (k : ℝ) ≤ N / s + 1 := by
    rw [hkdef, Nat.cast_add, Nat.cast_one]
    have := Nat.cast_div_le (α := ℝ) (m := N) (n := s)
    linarith
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  rw [div_le_iff₀ hNr]
  have h1' : (f N : ℝ) ≤ k * a := by exact_mod_cast h1
  calc (f N : ℝ) ≤ k * a := h1'
    _ ≤ (N / s + 1) * a := by gcongr
    _ = (a / s + a / N) * N := by field_simp

theorem f_div_tendsto_alphaStar :
    Tendsto (fun n : ℕ => (f n : ℝ) / n) atTop (𝓝 alphaStar) := by
  rw [tendsto_order]
  constructor
  · intro b hb
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    have := f_ge_alphaStar n
    rw [lt_div_iff₀ hnr]
    nlinarith
  · intro b hb
    obtain ⟨r, ⟨P₀, hP₀, rfl⟩, hr⟩ := exists_lt_of_csInf_lt ratioSet_nonempty hb
    have ht := tendsto_const_div_atTop_nhds_zero_nat (indepNum P₀ : ℝ)
    have hev := (tendsto_order.1 ht).2 (b - (indepNum P₀ : ℝ) / P₀.card) (by linarith)
    filter_upwards [hev, eventually_gt_atTop 0] with N hN hN0
    have := f_le_of_ratio hP₀ hN0
    linarith

/-! ### Larman–Rogers: `m₁ ≤ α*` -/

section LR
open scoped Classical

lemma isClosed_square (m : ℝ) : IsClosed (square m) := by
  have h1 : IsClosed {z : ℂ | |z.re| ≤ m} :=
    isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const
  have h2 : IsClosed {z : ℂ | |z.im| ≤ m} :=
    isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const
  exact h1.inter h2

lemma measurableSet_square (m : ℝ) : MeasurableSet (square m) :=
  (isClosed_square m).measurableSet

lemma square_eq_preimage (m : ℝ) :
    square m = Complex.measurableEquivRealProd ⁻¹' (Set.Icc (-m) m ×ˢ Set.Icc (-m) m) := by
  ext z
  simp [square, abs_le]; tauto

lemma volume_square {m : ℝ} (hm : 0 ≤ m) :
    volume (square m) = ENNReal.ofReal ((2 * m) ^ 2) := by
  rw [square_eq_preimage, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, ← ENNReal.ofReal_mul (by linarith)]
  congr 1; ring

lemma volume_square_toReal {m : ℝ} (hm : 0 ≤ m) :
    (volume (square m)).toReal = (2 * m) ^ 2 := by
  rw [volume_square hm, ENNReal.toReal_ofReal (by positivity)]

lemma volume_square_ne_top (m : ℝ) : volume (square m) ≠ ⊤ := by
  rcases le_or_gt 0 m with hm | hm
  · rw [volume_square hm]; exact ENNReal.ofReal_ne_top
  · have : square m = ∅ := by
      ext z; simp only [square, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro h; exact absurd ((abs_nonneg _).trans h) (not_le.2 hm)
    rw [this]; simp

/-- Pointwise: the number of points of `P + x` in a unit-free `A` is at most `indepNum P`. -/
lemma card_filter_translate_le {A : Set ℂ} (hu : UnitFree A) (P : Finset ℂ) (x : ℂ) :
    (P.filter (fun p => p + x ∈ A)).card ≤ indepNum P := by
  refine le_indepNum (Finset.filter_subset _ _) ?_
  intro a ha b hb
  simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha hb
  have := hu _ ha.2 _ hb.2
  simpa using this

lemma sum_indicator_eq (A : Set ℂ) (P : Finset ℂ) (x : ℂ) :
    ∑ p ∈ P, ((fun y => p + y) ⁻¹' A).indicator (1 : ℂ → ENNReal) x =
      ((P.filter (fun p => p + x ∈ A)).card : ENNReal) := by
  simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply]
  rw [Finset.sum_boole]

/-- The integrated Larman–Rogers inequality (in `ℝ≥0∞`). -/
lemma card_mul_volume_le {A : Set ℂ} (hA : MeasurableSet A) (hu : UnitFree A) (P : Finset ℂ)
    {R : ℕ} (hR : ∀ p ∈ P, |p.re| ≤ R ∧ |p.im| ≤ R) (k : ℕ) :
    (P.card : ENNReal) * volume (A ∩ square k) ≤
      (indepNum P : ENNReal) * volume (square ((k : ℝ) + R)) := by
  set M := square ((k : ℝ) + R)
  have hmeas : ∀ p : ℂ, MeasurableSet ((fun y => p + y) ⁻¹' A) :=
    fun p => hA.preimage (measurable_const_add p)
  -- each translate term is at least `vol (A ∩ square k)`
  have hterm : ∀ p ∈ P, volume (A ∩ square k) ≤ volume ((fun y => p + y) ⁻¹' A ∩ M) := by
    intro p hp
    rw [← measure_preimage_add (μ := volume) p (A ∩ square k)]
    refine measure_mono ?_
    intro x hx
    simp only [Set.mem_preimage, Set.mem_inter_iff] at hx
    refine ⟨hx.1, ?_⟩
    obtain ⟨-, h1, h2⟩ := hx
    obtain ⟨hr, hi⟩ := hR p hp
    simp only [M, square, Set.mem_ofPred_eq, Complex.add_re, Complex.add_im] at h1 h2 ⊢
    constructor
    · calc |x.re| = |(p.re + x.re) - p.re| := by ring_nf
        _ ≤ |p.re + x.re| + |p.re| := abs_sub _ _
        _ ≤ k + R := by linarith
    · calc |x.im| = |(p.im + x.im) - p.im| := by ring_nf
        _ ≤ |p.im + x.im| + |p.im| := abs_sub _ _
        _ ≤ k + R := by linarith
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
  calc (P.card : ENNReal) * volume (A ∩ square k)
      = ∑ _p ∈ P, volume (A ∩ square k) := by simp
    _ ≤ ∑ p ∈ P, volume ((fun y => p + y) ⁻¹' A ∩ M) := Finset.sum_le_sum hterm
    _ ≤ _ := hsum ▸ hint

/-- The density ratio along squares. -/
noncomputable def densRatio (A : Set ℂ) (m : ℕ) : ℝ :=
  (volume (A ∩ square m)).toReal / (volume (square m)).toReal

lemma upperDensity_eq (A : Set ℂ) : upperDensity A = limsup (densRatio A) atTop := rfl

lemma densRatio_nonneg (A : Set ℂ) (m : ℕ) : 0 ≤ densRatio A m := by
  unfold densRatio; positivity

lemma exists_bound (P : Finset ℂ) : ∃ R : ℕ, ∀ p ∈ P, |p.re| ≤ R ∧ |p.im| ≤ R := by
  refine ⟨⌈∑ p ∈ P, ‖p‖⌉₊, fun p hp => ?_⟩
  have h1 : ‖p‖ ≤ ∑ q ∈ P, ‖q‖ :=
    Finset.single_le_sum (f := fun q : ℂ => ‖q‖) (fun _ _ => norm_nonneg _) hp
  have h2 := Nat.le_ceil (∑ q ∈ P, ‖q‖)
  exact ⟨(Complex.abs_re_le_norm p).trans (h1.trans h2),
    (Complex.abs_im_le_norm p).trans (h1.trans h2)⟩

/-- Real form: `|P| · d_k ≤ α(P) · ((k+R)/k)²` for `k ≥ 1`. -/
lemma card_mul_densRatio_le {A : Set ℂ} (hA : MeasurableSet A) (hu : UnitFree A) (P : Finset ℂ)
    {R : ℕ} (hR : ∀ p ∈ P, |p.re| ≤ R ∧ |p.im| ≤ R) {k : ℕ} (hk : 0 < k) :
    (P.card : ℝ) * densRatio A k ≤ (indepNum P : ℝ) * (((k : ℝ) + R) / k) ^ 2 := by
  have h := card_mul_volume_le hA hu P hR k
  have hfin : (indepNum P : ENNReal) * volume (square ((k : ℝ) + R)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (volume_square_ne_top _)
  have h' := ENNReal.toReal_mono hfin h
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    volume_square_toReal (by positivity)] at h'
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  unfold densRatio
  rw [volume_square_toReal (by positivity)]
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  calc (P.card : ℝ) * (volume (A ∩ square k)).toReal ≤ indepNum P * (2 * ((k : ℝ) + R)) ^ 2 := h'
    _ = _ := by field_simp

lemma tendsto_ratio_sq (R : ℕ) :
    Tendsto (fun k : ℕ => (((k : ℝ) + R) / k) ^ 2) atTop (𝓝 1) := by
  have h1 : Tendsto (fun k : ℕ => (1 + (R : ℝ) / k) ^ 2) atTop (𝓝 ((1 + 0) ^ 2)) :=
    ((tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (R : ℝ))).pow 2)
  simp only [add_zero, one_pow] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  congr 1; field_simp

/-- **Larman–Rogers.** -/
theorem upperDensity_mul_card_le (A : Set ℂ) (hA : MeasurableSet A) (hu : UnitFree A)
    (P : Finset ℂ) : upperDensity A * P.card ≤ indepNum P := by
  rcases P.eq_empty_or_nonempty with rfl | hP
  · simp
  have hn : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
  obtain ⟨R, hR⟩ := exists_bound P
  set g : ℕ → ℝ := fun k => (indepNum P : ℝ) / P.card * (((k : ℝ) + R) / k) ^ 2
  have hg : Tendsto g atTop (𝓝 ((indepNum P : ℝ) / P.card)) := by
    have := (tendsto_ratio_sq R).const_mul ((indepNum P : ℝ) / P.card)
    simpa [g] using this
  have hle : ∀ᶠ k in atTop, densRatio A k ≤ g k := by
    filter_upwards [eventually_gt_atTop 0] with k hk
    have := card_mul_densRatio_le hA hu P hR hk
    simp only [g]
    rw [div_mul_eq_mul_div, le_div_iff₀ hn]
    linarith
  have hlim : upperDensity A ≤ (indepNum P : ℝ) / P.card := by
    rw [upperDensity_eq, ← hg.limsup_eq]
    exact limsup_le_limsup hle
      (isCoboundedUnder_le_of_le atTop (densRatio_nonneg A)) hg.isBoundedUnder_le
  rwa [le_div_iff₀ hn] at hlim

lemma upperDensity_le_alphaStar {A : Set ℂ} (hA : MeasurableSet A) (hu : UnitFree A) :
    upperDensity A ≤ alphaStar := by
  refine le_csInf ratioSet_nonempty ?_
  rintro r ⟨P, hP, rfl⟩
  have hn : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
  rw [le_div_iff₀ hn]
  exact upperDensity_mul_card_le A hA hu P

theorem m1_le_alphaStar : m1 ≤ alphaStar := by
  refine csSup_le ⟨_, ∅, MeasurableSet.empty, by simp [UnitFree], rfl⟩ ?_
  rintro d ⟨A, hA, hu, rfl⟩
  exact upperDensity_le_alphaStar hA hu

end LR

end Erdos1070
