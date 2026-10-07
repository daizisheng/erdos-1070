# #1070 Lean formalization plan (single-label transfer on top of OpenAI PlaneSpectrum)

Project: attack/1070/lean (Mathlib d13f23b, Lean v4.34.1; OAI/ = verbatim copy of openai/math's 70-file five-colour closure; DO NOT EDIT OAI/).
Our code goes in Erdos1070/*.lean, lib `Erdos1070` (add to lakefile).

## Target statements (Erdos1070/Main.lean), no sorry, axioms ⊆ {propext, Quot.sound, Classical.choice}

```lean
-- unit-distance-free finite sets, independence number of a finite point set
def UnitFree (S : Set ℂ) : Prop := ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≠ 1
noncomputable def indepNum (P : Finset ℂ) : ℕ := sSup {m | ∃ I ⊆ P, UnitFree (I : Set ℂ) ∧ I.card = m}
noncomputable def f (n : ℕ) : ℕ := sInf {m | ∃ P : Finset ℂ, P.card = n ∧ indepNum P = m}
-- upper density with squares [-m,m]^2 (also do balls if cheap)
noncomputable def upperDensity (A : Set ℂ) : ℝ := limsup (fun m : ℕ => (volume (A ∩ square m)).toReal / (volume (square m)).toReal) atTop
noncomputable def m1 : ℝ := sSup {d | ∃ A, MeasurableSet A ∧ UnitFree A ∧ upperDensity A = d}

theorem f_div_tendsto : Tendsto (fun n => (f n : ℝ) / n) atTop (𝓝 m1)
theorem f_ge : ∀ n, m1 * n ≤ f n
```

## Proof decomposition (see ../openai_transfer/PROOF.md for the paper proof)
1. `alphaStar := sInf {indepNum P / P.card | P nonempty}`; `f n ≥ alphaStar * n`; `f n / n → alphaStar` (disjoint far translates + padding). Elementary.
2. Larman–Rogers: `m1 ≤ alphaStar` (integrate |(P+x) ∩ A| over square; boundary loss). Elementary measure theory.
3. Transfer: `alphaStar ≤ m1`, i.e. ∃ measurable unit-free A with upperDensity ≥ alphaStar.
   3a. Space Ω = independent subsets of E (as E → Bool / Fin 2 with independence), compact; translations/rotations as homeos (mirror OAI Representations `Space`, `trans`, `rotate`, `covariance`).
   3b. Invariant probability μ on Ω, E- and K-invariant, with μ{0 ∈ ω} ≥ alphaStar. Two-stage: Følner sets F_N ⊂ E (E countable abelian ⇒ amenable), J_N max independent subset, functional φ ↦ lim_U |F_N|⁻¹ Σ_{z∈F_N} φ(J_N − z) (ultrafilter limit; positive functional on C(Ω) → RealRMK.rieszMeasure, as in OAI StationaryMean); then average over K with an invariant mean (OAI `Amenable.Mean` / MovingMean) — rotation averaging does not change μ{0∈ω}. Weighted E⋊K averaging of one configuration is NOT allowed (gives weighted ratio).
   3c. Reuse: representation / space / starProjection (`projected`), `projection_range`, `projection_covariance_fixed`, `residual_fourier`/`wild_fourier` (Thm 2.3), `orbitExtension`, `exists_measurable_field`, `positive_orthogonal`, `circle_closed_induction`, `all_parameters_product_zero`. Mirror BorelTransfer lines 1–260 for ONE label f = 1[0∈ω] (only change: Space; and no sum-to-one step).
   3d. Mean: E[p] = E[f] (1 ∈ space, projection self-adjoint). Sampling: reverse Fatou ⇒ ∃ ω with limsup square-averages of h ≥ alphaStar and zero unit correlation.
   3e. One-class density-point lemma: A = density-one points of {h>0} is unit-free; |A Δ {h>0}| = 0 (mirror WeakColoring `DensityOne`, `weak_density_proper`).
4. Combine.

## Rules
- All builds via `tools/sandbox.sh` (≤12 cpus, 32G). Never edit OAI/. No sorry in final; `#print axioms` check in Check1070.lean.
- Commit-free; keep a PROGRESS.md log in this directory.
