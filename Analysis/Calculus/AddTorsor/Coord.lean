/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases

/-!
# Barycentric coordinates are smooth
-/

public section

variable {ι 𝕜 E P : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [MetricSpace P] [NormedAddTorsor E P]
variable [FiniteDimensional 𝕜 E]

/--
theorem `smooth_barycentric_coord` / 定理 `smooth_barycentric_coord`

English:
theorem smooth_barycentric_coord
  given: (b : AffineBasis ι 𝕜 E) (i : ι)
  statement: ContDiff 𝕜 ⊤ (b.coord i)
  proof: (⟨b.coord i, continuous_barycentric_coord b i⟩ : E ->ᴬ[𝕜] 𝕜).contDiff

中文:
定理 smooth_barycentric_coord
  条件: (b : AffineBasis ι 𝕜 E) (i : ι)
  结论: ContDiff 𝕜 ⊤ (b.coord i)
  证明: (⟨b.coord i, continuous_barycentric_coord b i⟩ : E ->ᴬ[𝕜] 𝕜).contDiff

Depends on / 依赖: b.coord, contDiff, continuous_barycentric_coord
-/
theorem smooth_barycentric_coord (b : AffineBasis ι 𝕜 E) (i : ι) : ContDiff 𝕜 ⊤ (b.coord i) :=
  (⟨b.coord i, continuous_barycentric_coord b i⟩ : E ->ᴬ[𝕜] 𝕜).contDiff
