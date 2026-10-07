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

end Erdos1070
