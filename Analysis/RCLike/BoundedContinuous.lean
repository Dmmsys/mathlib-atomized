/-
Copyright (c) 2025 Jakob Stiefel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Stiefel
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Star

/-! # Results on bounded continuous functions with `RCLike` values -/

public section

open Filter Real RCLike BoundedContinuousFunction

open scoped Topology

variable (𝕜 E : Type*) [RCLike 𝕜] [PseudoEMetricSpace E]

namespace RCLike

set_option backward.isDefEq.respectTransparency false in
/--
theorem `restrict_toContinuousMap_eq_toContinuousMapStar_restrict` / 定理 `restrict_toContinuousMap_eq_toContinuousMapStar_restrict`

English:
theorem restrict_toContinuousMap_eq_toContinuousMapStar_restrict
  proof: by
  ext g
  simp only [Subalgebra.mem_map, Subalgebra.mem_comap, Subalgebra.mem_restrictScalars,
    StarSubalgebra.mem_toSubalgebra, StarSubalgebra.mem_map]
  constructor
  · intro ⟨x, hxA, hxg⟩
    use (@ofRealAm 𝕜 _).compLeftContinuousBounded Real lipschitzWith_ofReal x, hxA
    ext a
    simp o

中文:
定理 restrict_toContinuousMap_eq_toContinuousMapStar_restrict
  证明: by
  ext g
  simp only [Subalgebra.mem_map, Subalgebra.mem_comap, Subalgebra.mem_restrictScalars,
    StarSubalgebra.mem_toSubalgebra, StarSubalgebra.mem_map]
  constructor
  · intro ⟨x, hxA, hxg⟩
    use (@ofRealAm 𝕜 _).compLeftContinuousBounded Real lipschitzWith_ofReal x, hxA
    ext a
    simp o

Depends on / 依赖: AlgHom, AlgHom.compLeftContinuousBounded_apply_apply, AlgHom.compLeftContinuous_apply_apply, DFunLike, DFunLike.congr_fun, StarSubalgebra, StarSubalgebra.mem_map, StarSubalgebra.mem_toSubalgebra, Subalgebra, Subalgebra.mem_comap, Subalgebra.mem_map, Subalgebra.mem_restrictScalars, algebraMap, algebraMap.coe_inj, coe_inj, compLeftContinuousBounded, compLeftContinuousBounded_apply_apply, compLeftContinuous_apply_apply, congr_fun, hg_apply
-/
theorem restrict_toContinuousMap_eq_toContinuousMapStar_restrict
    {A : StarSubalgebra 𝕜 (E ->ᵇ 𝕜)} :
    ((A.restrictScalars Real).comap
    (AlgHom.compLeftContinuousBounded Real ofRealAm lipschitzWith_ofReal)).map (toContinuousMapₐ Real) =
    ((A.map (toContinuousMapStarₐ 𝕜)).restrictScalars Real).comap
    (ofRealAm.compLeftContinuous Real continuous_ofReal) := by
  ext g
  simp only [Subalgebra.mem_map, Subalgebra.mem_comap, Subalgebra.mem_restrictScalars,
    StarSubalgebra.mem_toSubalgebra, StarSubalgebra.mem_map]
  constructor
  · intro ⟨x, hxA, hxg⟩
    use (@ofRealAm 𝕜 _).compLeftContinuousBounded Real lipschitzWith_ofReal x, hxA
    ext a
    simp only [toContinuousMapStarₐ_apply_apply, AlgHom.compLeftContinuousBounded_apply_apply,
      ofRealAm_coe, AlgHom.compLeftContinuous_apply_apply, algebraMap.coe_inj]
    exact DFunLike.congr_fun hxg a
  · intro ⟨x, hxA, hxg⟩
    have hg_apply (a : E) := DFunLike.congr_fun hxg a
    simp only [toContinuousMapStarₐ_apply_apply, AlgHom.compLeftContinuous_apply_apply,
      ofRealAm_coe] at hg_apply
    have h_comp_eq : (@ofRealAm 𝕜 _).compLeftContinuousBounded Real lipschitzWith_ofReal
        (x.comp reCLM (@reCLM 𝕜 _).lipschitz) = x := by
      ext a
      simp [hg_apply]
    use x.comp reCLM (@reCLM 𝕜 _).lipschitz
    refine ⟨by rwa [h_comp_eq], ?_⟩
    ext a
    simp [hg_apply]

end RCLike
