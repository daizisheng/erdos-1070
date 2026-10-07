# Erdős #1070: f(n) = (m₁ + o(1)) n

Let f(n) be the largest integer such that every n points in the plane contain f(n) points with no two at distance 1, and let m₁ be the supremum of the upper densities of measurable unit-distance-free planar sets.

**Claim.** m₁·n ≤ f(n) ≤ m₁·n + o(n). This is the first half of Conjecture 1 of Dúcz–Varga (arXiv 2606.28157). Combined with m₁ ≤ 0.247 (Ambrus–Csiszárik–Matolcsi–Varga–Zsámboki), it gives f(n) ≤ (0.247+o(1))n.

**Status: draft.** The author has not yet audited it.

- `paper/` holds the write-up (`erdos1070.tex`, `erdos1070.pdf`).
- The only external input is the Haar rigidity theorem (Thm 2.3) of OpenAI's preprint *The Euclidean plane is not five-colorable* (2026-09-23). It is machine-checked in Lean as `OAI.PlaneFiveColor.Spectral.wild_fourier`.
- `lean/` is a Lean 4 project (toolchain v4.34.1, Mathlib `d13f23b`):
  - `lean/OAI/` is a verbatim copy of the 70-file import closure of OpenAI's five-colour theorem, taken from github.com/openai/math at commit `adc7f12`. It is Apache-2.0 licensed; see `lean/OAI/LICENSE`.
  - `lean/Check.lean` checks `#print axioms` for `no_proper_five_coloring` and `wild_fourier`; both give only `[propext, Classical.choice, Quot.sound]`.
  - `lean/Erdos1070/` holds our formalization of the theorem. It is **in progress**; see `lean/FORMALIZATION_PLAN.md` and `lean/PROGRESS_*.md`.

Build:
```
cd lean && lake exe cache get && lake build OAI.Geometry.PlaneColoring.Five && lake env lean Check.lean
```
