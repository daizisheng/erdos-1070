# Erdős Problem #1070: f(n) = (m₁ + o(1)) n

Authors: Shisheng Li and Yong Su

Let f(n) be the largest integer such that every n points in the plane contain f(n) points with no two at distance 1. Let m₁ be the supremum of the upper densities of measurable planar sets with no two points at distance 1.

**Theorem.** lim f(n)/n = m₁, and f(n) ≥ m₁ n for every n.

- The lower bound f(n) ≥ m₁ n is due to Larman–Rogers (1972).
- The new part is lim f(n)/n ≤ m₁. This is the first half of Conjecture 1 of Dúcz–Varga ([arXiv:2606.28157](https://arxiv.org/abs/2606.28157)).
- With Ambrus–Csiszárik–Matolcsi–Varga–Zsámboki's m₁ ≤ 0.247, it gives f(n) ≤ (0.247 + o(1)) n.
- Dúcz–Varga answered the second question of #1070 (f(n) ≥ n/4?) negatively. The exact value of m₁ (Erdős #232) remains open.

Contents:
- `paper/erdos1070.tex`, `paper/erdos1070.pdf` — the paper.
- `lean/` — a Lean 4 formalization of the theorem, with no `sorry`.

The one external input is the Haar rigidity theorem for wild character laws (Thm 2.3 of OpenAI's preprint *The Euclidean plane is not five-colorable*, 2026-09-23). It is machine-checked in OpenAI's Lean development as `OAI.PlaneFiveColor.Spectral.wild_fourier`. `lean/OAI/` is a verbatim copy of the 70-file import closure of that development, taken from [openai/math](https://github.com/openai/math) at `adc7f12` (Apache-2.0, see `lean/OAI/LICENSE`).

## Checking the Lean proof

```
cd lean
lake exe cache get      # Mathlib build cache (OAI/ and Erdos1070/ are compiled from source)
lake build
lake env lean Check.lean
```
`Check.lean` prints the definitions and statements, and
```
'Erdos1070.f_div_tendsto_m1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1070.m1_mul_le_f' depends on axioms: [propext, Classical.choice, Quot.sound]
'OAI.PlaneFiveColor.Spectral.wild_fourier' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1070.f_div_tendsto_m1Ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1070.m1Ball_mul_le_f' depends on axioms: [propext, Classical.choice, Quot.sound]
```
There is no `sorry` and there are no project axioms. To re-check every declaration of the import closure (Mathlib, `OAI/`, `Erdos1070/`) in the Lean kernel, run `lake env leanchecker Erdos1070` (single-threaded, about 40 minutes). Toolchain `leanprover/lean4:v4.34.1`, Mathlib `d13f23b`.

The main statements are:
```lean
theorem f_div_tendsto_m1 : Tendsto (fun n : ℕ => (f n : ℝ) / n) atTop (𝓝 m1)
theorem m1_mul_le_f (n : ℕ) : m1 * n ≤ f n
-- erdosproblems.com convention: open discs B(0,R), R ∈ ℝ, R → ∞
theorem f_div_tendsto_m1Ball : Tendsto (fun n : ℕ => (f n : ℝ) / n) atTop (𝓝 m1Ball)
theorem m1Ball_mul_le_f (n : ℕ) : m1Ball * n ≤ f n
theorem m1Ball_eq_m1 : m1Ball = m1
```
The definitions are in `Erdos1070/Defs.lean` (`m1`: upper density on squares [−m, m]², m ∈ ℕ) and `Erdos1070/Disc.lean` (`m1Ball`: upper density on open discs of real radius, the convention of Erdős #232 on erdosproblems.com). The two give the same m₁.

| file | content |
|---|---|
| `Defs.lean` | `UnitFree`, `indepNum`, `f`, `upperDensity`, `m1`, `alphaStar` (= inf over finite sets of the independence ratio) |
| `Elementary.lean` | f(n) ≥ α* n and f(n)/n → α* (disjoint far copies); Larman–Rogers m₁ ≤ α* |
| `TransferFolner.lean` | Følner sets in the algebraic numbers E |
| `TransferSpace.lean` | space of independent subsets of E; two-stage average (translations, then rotations) giving an invariant law with P(0 ∈ ω) ≥ α* |
| `TransferKoopman.lean` | projection of 1[0∈ω] onto the continuous factor; zero unit-distance correlation via `wild_fourier` |
| `TransferSample.lean` | one sample: a measurable field h : ℝ² → [0,1] with zero unit correlation and upper mean ≥ α* |
| `TransferDensity.lean` | density points of {h > 0}: a measurable unit-distance-free set of upper density ≥ α* |
| `Transfer.lean`, `Main.lean` | α* ≤ m₁; main theorem |
| `DiscSample.lean`, `Disc.lean` | the same with discs of real radius; `m1Ball = m1` |
