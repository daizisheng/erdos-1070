import Mathlib

/-!
# Følner sequences for countable torsion-free abelian groups

For a countable abelian group `G` with no `ℤ`-torsion we build finite sets `F N` such that
for every `w`, the proportion of `z ∈ F N` with `z + w ∉ F N` tends to `0`.

Construction: enumerate `G = {e 0, e 1, …}`; the `ℤ`-span of `e 0, …, e N` is a finitely
generated torsion-free, hence free, `ℤ`-module; `F N` is a large coordinate box in a basis.
-/

namespace Erdos1070.Folner

open Filter Topology Finset

section Box
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The box `[0,n)^ι` in `ℤ^ι`. -/
def box (n : ℕ) : Finset (ι → ℤ) := Fintype.piFinset fun _ => Finset.Ico (0:ℤ) n

lemma card_box (n : ℕ) : (box (ι := ι) n).card = n ^ Fintype.card ι := by
  simp [box, Fintype.card_piFinset, Int.card_Ico]

lemma box_nonempty {n : ℕ} (hn : 0 < n) : (box (ι := ι) n).Nonempty := by
  refine ⟨fun _ => 0, ?_⟩
  simp only [box, Fintype.mem_piFinset, Finset.mem_Ico, le_refl, true_and]
  intro _
  exact_mod_cast hn

omit [Fintype ι] [DecidableEq ι] in
lemma one_sub_prod_le (s : Finset ι) (x : ι → ℝ) (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) :
    1 - ∏ i ∈ s, x i ≤ ∑ i ∈ s, (1 - x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    have hP1 : ∏ i ∈ s, x i ≤ 1 := prod_le_one₀ (fun i _ => h0 i) (fun i _ => h1 i)
    have hh : (1 - x a) * ∏ i ∈ s, x i ≤ 1 - x a :=
      mul_le_of_le_one_right (sub_nonneg.mpr (h1 a)) hP1
    nlinarith

lemma ico_len (n : ℕ) (c : ℤ) : min (n:ℤ) (n - c) - max 0 (-c) = n - |c| := by
  rcases le_total 0 c with h | h
  · rw [abs_of_nonneg h, max_eq_left (by linarith), min_eq_right (by linarith), sub_zero]
  · rw [abs_of_nonpos h, max_eq_right (by linarith), min_eq_left (by linarith)]

lemma bad_ratio_le (n : ℕ) (hn : 0 < n) (c : ι → ℤ) :
    (((box n).filter (fun k => k + c ∉ box n)).card : ℝ) / (box (ι := ι) n).card ≤
      (∑ i, |(c i : ℝ)|) / n := by
  set Gd : Finset (ι → ℤ) :=
    Fintype.piFinset fun i => Finset.Ico (max 0 (-c i)) (min (n:ℤ) (n - c i)) with hGd
  have hG : Gd ⊆ (box n).filter (fun k => k + c ∈ box n) := by
    intro k hk
    simp only [hGd, Fintype.mem_piFinset, Finset.mem_Ico, max_le_iff, lt_min_iff] at hk
    simp only [box, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Ico, Pi.add_apply]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · obtain ⟨⟨h1, _⟩, h3, _⟩ := hk i; exact ⟨h1, h3⟩
    · obtain ⟨⟨_, h2⟩, _, h4⟩ := hk i; constructor <;> linarith
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := box (ι := ι) n) (fun k => k + c ∈ box n)
  have hGc : (Gd.card : ℝ) = ∏ i, (((min (n:ℤ) (n - c i) - max 0 (-c i)).toNat : ℕ) : ℝ) := by
    simp [hGd, Fintype.card_piFinset, Int.card_Ico]
  have hle : (Gd.card : ℝ) ≤ ((box n).filter (fun k => k + c ∈ box n)).card := by
    exact_mod_cast Finset.card_le_card hG
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hbox : ((box (ι := ι) n).card : ℝ) = ∏ _i : ι, (n:ℝ) := by
    simp [card_box]
  have hboxpos : (0:ℝ) < (box (ι := ι) n).card := by
    rw [hbox]; exact prod_pos fun _ _ => hnR
  set t : ι → ℝ := fun i => (((min (n:ℤ) (n - c i) - max 0 (-c i)).toNat : ℕ) : ℝ) / n with ht
  have ht0 : ∀ i, 0 ≤ t i := fun i => by positivity
  have ht1 : ∀ i, t i ≤ 1 := by
    intro i
    rw [ht, div_le_one hnR]
    have : (min (n:ℤ) (n - c i) - max 0 (-c i)).toNat ≤ n := by
      rw [ico_len]; have := abs_nonneg (c i); omega
    exact_mod_cast this
  have htc : ∀ i, 1 - t i ≤ |(c i : ℝ)| / n := by
    intro i
    simp only [ht, ico_len]
    have h1 : ((n:ℤ) - |c i|) ≤ (((n:ℤ) - |c i|).toNat : ℤ) := Int.self_le_toNat _
    have h2 : ((n:ℝ) - |(c i : ℝ)|) ≤ (((n:ℤ) - |c i|).toNat : ℝ) := by
      have := (Int.cast_le (R := ℝ)).mpr h1
      push_cast at this
      exact this
    have h3 : (1:ℝ) - |(c i:ℝ)|/n = ((n:ℝ) - |(c i:ℝ)|)/n := by field_simp
    rw [sub_le_comm, h3]; exact div_le_div_of_nonneg_right h2 hnR.le
  have hratio : (Gd.card : ℝ) / (box (ι := ι) n).card = ∏ i, t i := by
    rw [hGc, hbox, ← prod_div_distrib]
  calc
    (((box n).filter (fun k => k + c ∉ box n)).card : ℝ) / (box (ι := ι) n).card
        ≤ 1 - (Gd.card : ℝ) / (box (ι := ι) n).card := by
          rw [le_sub_iff_add_le, ← add_div, div_le_one hboxpos]
          have : (((box n).filter (fun k => k + c ∉ box n)).card : ℝ) +
              ((box n).filter (fun k => k + c ∈ box n)).card = (box (ι := ι) n).card := by
            exact_mod_cast (by omega : _ = _)
          linarith
    _ = 1 - ∏ i, t i := by rw [hratio]
    _ ≤ ∑ i, (1 - t i) := one_sub_prod_le _ t ht0 ht1
    _ ≤ ∑ i, |(c i : ℝ)| / n := sum_le_sum fun i _ => htc i
    _ = (∑ i, |(c i : ℝ)|) / n := by rw [sum_div]

end Box

section Group
variable {G : Type*} [AddCommGroup G] [Module.IsTorsionFree ℤ G]

instance spanFinite (s : Finset G) : Module.Finite ℤ (Submodule.span ℤ (s : Set G)) :=
  Module.Finite.span_of_finite ℤ s.finite_toSet

/-- The basis index of the span of `s`. -/
abbrev Idx (s : Finset G) := Module.Free.ChooseBasisIndex ℤ (Submodule.span ℤ (s : Set G))

/-- A chosen `ℤ`-basis of the span of `s`. -/
noncomputable def basis (s : Finset G) : Module.Basis (Idx s) ℤ (Submodule.span ℤ (s : Set G)) :=
  Module.Free.chooseBasis ℤ _

noncomputable def coordMap (s : Finset G) (k : Idx s → ℤ) : G :=
  ((basis s).equivFun.symm k : G)

lemma coordMap_injective (s : Finset G) : Function.Injective (coordMap s) := by
  intro a b h
  exact (basis s).equivFun.symm.injective (Subtype.ext h)

lemma coordMap_add (s : Finset G) (k c : Idx s → ℤ) :
    coordMap s (k + c) = coordMap s k + coordMap s c := by
  simp only [coordMap, map_add, Submodule.coe_add]

open Classical in
/-- Coordinates of `w` (zero if `w` is not in the span). -/
noncomputable def coords (s : Finset G) (w : G) : Idx s → ℤ :=
  if h : w ∈ Submodule.span ℤ (s : Set G) then (basis s).equivFun ⟨w, h⟩ else 0

lemma coordMap_coords (s : Finset G) {w : G} (hw : w ∈ Submodule.span ℤ (s : Set G)) :
    coordMap s (coords s w) = w := by
  simp [coordMap, coords, hw]

/-- The Følner box in `G`. -/
noncomputable def gbox (s : Finset G) (n : ℕ) : Finset G :=
  (box n).map ⟨coordMap s, coordMap_injective s⟩

lemma gbox_nonempty (s : Finset G) {n : ℕ} (hn : 0 < n) : (gbox s n).Nonempty :=
  (box_nonempty hn).map

open Classical in
lemma gbox_ratio (s : Finset G) (n : ℕ) (hn : 0 < n) {w : G}
    (hw : w ∈ Submodule.span ℤ (s : Set G)) :
    (((gbox s n).filter (fun z => z + w ∉ gbox s n)).card : ℝ) / (gbox s n).card ≤
      (∑ i, |(coords s w i : ℝ)|) / n := by
  classical
  have he : (gbox s n).filter (fun z => z + w ∉ gbox s n) =
      ((box n).filter (fun k => k + coords s w ∉ box n)).map
        ⟨coordMap s, coordMap_injective s⟩ := by
    rw [gbox, Finset.filter_map]
    congr 1
    apply Finset.filter_congr
    intro k _
    simp only [Function.comp_apply, Function.Embedding.coeFn_mk]
    have hx : coordMap s k + w = coordMap s (k + coords s w) := by
      rw [coordMap_add, coordMap_coords s hw]
    rw [hx]
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · intro h hk; exact h ⟨_, hk, rfl⟩
    · rintro h ⟨a, ha, hae⟩
      exact h (coordMap_injective s hae ▸ ha)
  rw [he, Finset.card_map, gbox, Finset.card_map]
  exact bad_ratio_le n hn (coords s w)

end Group

section Seq
variable {G : Type*} [AddCommGroup G] [Module.IsTorsionFree ℤ G] [Countable G]

open Classical in
theorem exists_folner : ∃ F : ℕ → Finset G, (∀ N, (F N).Nonempty) ∧
    ∀ w : G, Tendsto (fun N => (((F N).filter (fun z => z + w ∉ F N)).card : ℝ) / (F N).card)
      atTop (𝓝 0) := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat G
  let s : ℕ → Finset G := fun N => (Finset.range (N+1)).image e
  have hmem : ∀ N j, j ≤ N → e j ∈ Submodule.span ℤ (s N : Set G) := by
    intro N j hj
    apply Submodule.subset_span
    simp only [s, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    exact ⟨j, by omega, rfl⟩
  let C : ℕ → ℝ := fun N => ∑ j ∈ Finset.range (N+1), ∑ i, |(coords (s N) (e j) i : ℝ)|
  have hC0 : ∀ N, 0 ≤ C N := fun N => sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
  let n : ℕ → ℕ := fun N => (N+1) * (⌈C N⌉₊ + 1)
  have hn : ∀ N, 0 < n N := fun N => by positivity
  refine ⟨fun N => gbox (s N) (n N), fun N => gbox_nonempty _ (hn N), ?_⟩
  intro w
  obtain ⟨j, rfl⟩ := he w
  have hbound : ∀ N, j ≤ N →
      (((gbox (s N) (n N)).filter (fun z => z + e j ∉ gbox (s N) (n N))).card : ℝ) /
        (gbox (s N) (n N)).card ≤ 1 / ((N:ℝ) + 1) := by
    intro N hN
    refine (gbox_ratio (s N) (n N) (hn N) (hmem N j hN)).trans ?_
    have hj : ∑ i, |(coords (s N) (e j) i : ℝ)| ≤ C N :=
      single_le_sum (f := fun j => ∑ i, |(coords (s N) (e j) i : ℝ)|)
        (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (by omega))
    have hc : C N ≤ ⌈C N⌉₊ := Nat.le_ceil _
    have hnR : ((n N : ℕ) : ℝ) = ((N:ℝ)+1) * ((⌈C N⌉₊ : ℝ) + 1) := by
      simp [n]
    rw [hnR, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hC0 N]
  apply squeeze_zero' (Eventually.of_forall fun N => by positivity)
    (eventually_atTop.mpr ⟨j, hbound⟩)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

end Seq

end Erdos1070.Folner
