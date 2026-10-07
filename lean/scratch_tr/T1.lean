import Mathlib
import OAI.Analysis.PlaneSpectrum.Basic
open OAI PlaneFiveColor.Spectral
example : Countable E := inferInstance
example : Module.IsTorsionFree ℤ E := inferInstance
example (s : Set E) (hs : s.Finite) : Module.Free ℤ (Submodule.span ℤ s) := by
  haveI : Module.Finite ℤ (Submodule.span ℤ s) := by exact?
  infer_instance
#check @exists_surjective_nat
