# Erdos1070/Elementary.lean — progress log

Status 2026-10-07: COMPLETE. No sorry/admit/axiom/native_decide. Compiles with zero warnings.
Axioms check: Erdos1070/CheckElementary.lean -> every theorem depends only on [propext, Classical.choice, Quot.sound].

## Main theorems
- `f_ge_alphaStar (n) : alphaStar * n ≤ f n`
- `f_div_tendsto_alphaStar : Tendsto (fun n => (f n : ℝ) / n) atTop (𝓝 alphaStar)`
  (upper bound: `translates P₀ k` = k copies of P₀ spaced along the real axis by `spacing P₀`;
  disjoint so card = k·|P₀|; indepNum subadditive under ∪ (no geometry needed) and translation invariant;
  f N ≤ indepNum of any superset of size ≥ N; gives f N / N ≤ a/s + a/N.)
- `upperDensity_mul_card_le (A) (hA : MeasurableSet A) (hu : UnitFree A) (P) : upperDensity A * P.card ≤ indepNum P`
  (lintegral over square (k+R) of Σ_p 1_{A-p}; pointwise ≤ indepNum P; each term ≥ vol(A ∩ square k);
  so |P|·d_k ≤ α(P)·((k+R)/k)², then limsup.)
- `m1_le_alphaStar : m1 ≤ alphaStar`, `upperDensity_le_alphaStar`

## Helper facts (reusable)
indepSet_bddAbove/nonempty, le_indepNum, exists_indep, indepNum_le_card, indepNum_mono,
indepNum_union_le, indepNum_translate, UnitFree.mono, fSet_nonempty, exists_f (f attained),
f_le_indepNum, f_le (f n ≤ n), f_le_indepNum_of_le, ratioSet_nonempty/bddBelow, alphaStar_le_ratio,
alphaStar_nonneg, alphaStar_le_one, alphaStar_mul_card_le, isClosed_square, measurableSet_square,
volume_square (= ofReal((2m)²) for m ≥ 0), volume_square_toReal, volume_square_ne_top,
densRatio (+ upperDensity_eq, densRatio_nonneg), exists_bound, tendsto_ratio_sq.
