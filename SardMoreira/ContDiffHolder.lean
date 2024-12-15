import Mathlib

open scoped unitInterval Topology
open Asymptotics Filter

section NormedField

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable (𝕜) in
structure ContDiffHolderAt (k : ℕ) (α : I) (f : E → F) (a : E) : Prop where
  contDiffAt : ContDiffAt 𝕜 k f a
  isBigO : (iteratedFDeriv 𝕜 k f · - iteratedFDeriv 𝕜 k f a) =O[𝓝 a] fun x ↦ ‖x - a‖ ^ (α : ℝ)
