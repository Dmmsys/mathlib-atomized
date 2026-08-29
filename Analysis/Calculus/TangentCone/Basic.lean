/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.TangentCone.Defs
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Basic properties of tangent cones and sets with unique differentiability property

In this file we prove basic lemmas about `tangentConeAt`, `UniqueDiffWithinAt`,
and `UniqueDiffOn`.
-/

public section

open Filter Set Metric
open scoped Topology Pointwise

variable {𝕜 E : Type*}

section SMul

variable [AddCommGroup E] [SMul 𝕜 E] [TopologicalSpace E] {s t : Set E} {x : E}

@[gcongr]
/--
theorem `tangentConeAt_mono` / 定理 `tangentConeAt_mono`

English:
theorem tangentConeAt_mono
  given: (h : s subseteq t)
  statement: tangentConeAt 𝕜 s x subseteq tangentConeAt 𝕜 t x
  proof: by
  simp only [tangentConeAt_def, ofPred_subset_ofPred]
  refine fun y hy => hy.mono ?_
  gcongr

中文:
定理 tangentConeAt_mono
  条件: (h : s subseteq t)
  结论: tangentConeAt 𝕜 s x subseteq tangentConeAt 𝕜 t x
  证明: by
  simp only [tangentConeAt_def, ofPred_subset_ofPred]
  refine fun y hy => hy.mono ?_
  gcongr

Depends on / 依赖: hy.mono, ofPred_subset_ofPred, tangentConeAt_def
-/
theorem tangentConeAt_mono (h : s subseteq t) : tangentConeAt 𝕜 s x subseteq tangentConeAt 𝕜 t x := by
  simp only [tangentConeAt_def, ofPred_subset_ofPred]
  refine fun y hy => hy.mono ?_
  gcongr

/--
theorem `tangentConeAt_mono_field` / 定理 `tangentConeAt_mono_field`

English:
theorem tangentConeAt_mono_field
  proof: by
  simp only [tangentConeAt_def, ofPred_subset_ofPred]
  refine fun y hy => hy.mono ?_
  rw [← smul_one_smul (Filter 𝕜')]
  grw [le_top (a := ⊤ • 1)]

中文:
定理 tangentConeAt_mono_field
  证明: by
  simp only [tangentConeAt_def, ofPred_subset_ofPred]
  refine fun y hy => hy.mono ?_
  rw [← smul_one_smul (Filter 𝕜')]
  grw [le_top (a := ⊤ • 1)]

Depends on / 依赖: Filter, hy.mono, le_top, ofPred_subset_ofPred, smul_one_smul, tangentConeAt_def
-/
theorem tangentConeAt_mono_field
    {𝕜' : Type*} [Monoid 𝕜'] [SMul 𝕜 𝕜'] [MulAction 𝕜' E] [IsScalarTower 𝕜 𝕜' E] :
    tangentConeAt 𝕜 s x subseteq tangentConeAt 𝕜' s x := by
  simp only [tangentConeAt_def, ofPred_subset_ofPred]
  refine fun y hy => hy.mono ?_
  rw [← smul_one_smul (Filter 𝕜')]
  grw [le_top (a := ⊤ • 1)]

/--
theorem `Filter.HasBasis.tangentConeAt_eq_biInter_closure` / 定理 `Filter.HasBasis.tangentConeAt_eq_biInter_closure`

English:
theorem Filter.HasBasis.tangentConeAt_eq_biInter_closure
  statement: {ι} {p : ι -> Prop} {U : ι -> Set E}
  proof: by
  ext y
  simp only [tangentConeAt_def, mem_ofPred_eq, mem_iInter₂, ← map₂_smul, ← map_prod_eq_map₂,
    ((nhdsWithin_hasBasis h _).top_prod.map _).clusterPt_iff_forall_mem_closure, image_prod,
    image2_smul]

中文:
定理 滤子.有基.tangentConeAt_eq_bi整数er_closure
  结论: {ι} {p : ι -> 命题} {U : ι -> 集合 E}
  证明: by
  ext y
  simp only [tangentConeAt_def, mem_ofPred_eq, mem_iInter₂, ← map₂_smul, ← map_prod_eq_map₂,
    ((nhdsWithin_hasBasis h _).top_prod.map _).clusterPt_iff_forall_mem_closure, image_prod,
    image2_smul]

Depends on / 依赖: clusterPt_iff_forall_mem_closure, image2_smul, image_prod, mem_ofPred_eq, nhdsWithin_hasBasis, tangentConeAt_def, top_prod, top_prod.map
-/
theorem Filter.HasBasis.tangentConeAt_eq_biInter_closure {ι} {p : ι -> Prop} {U : ι -> Set E}
    (h : (𝓝 0).HasBasis p U) :
    tangentConeAt 𝕜 s x = ⋂ (i) (_ : p i), closure ((univ : Set 𝕜) • (U i inter (x + ·) ⁻¹' s)) := by
  ext y
  simp only [tangentConeAt_def, mem_ofPred_eq, mem_iInter₂, ← map₂_smul, ← map_prod_eq_map₂,
    ((nhdsWithin_hasBasis h _).top_prod.map _).clusterPt_iff_forall_mem_closure, image_prod,
    image2_smul]

/--
theorem `tangentConeAt_eq_biInter_closure` / 定理 `tangentConeAt_eq_biInter_closure`

English:
theorem tangentConeAt_eq_biInter_closure
  proof: (basis_sets _).tangentConeAt_eq_biInter_closure

中文:
定理 tangentConeAt_eq_bi整数er_closure
  证明: (basis_sets _).tangentConeAt_eq_biInter_closure

Depends on / 依赖: basis_sets, tangentConeAt_eq_biInter_closure
-/
theorem tangentConeAt_eq_biInter_closure :
    tangentConeAt 𝕜 s x = ⋂ U in 𝓝 0, closure ((univ : Set 𝕜) • (U inter (x + ·) ⁻¹' s)) :=
  (basis_sets _).tangentConeAt_eq_biInter_closure

variable [ContinuousAdd E]

/--
theorem `tangentConeAt_mono_nhds` / 定理 `tangentConeAt_mono_nhds`

English:
theorem tangentConeAt_mono_nhds
  given: (h : 𝓝[s] x <= 𝓝[t] x)
  proof: by
  simp only [tangentConeAt_def, ofPred_subset_ofPred]
  refine fun y hy => hy.mono ?_
  gcongr _ • ?_
  rw [nhdsWithin_le_iff]
  suffices Tendsto (x + ·) (𝓝[(x + ·) ⁻¹' s] 0) (𝓝[s] x) from
.2 tendsto_nhdsWithin_iff.mp this.mono_right h
  refine .inf ?_ (mapsTo_preimage _ _).tendsto
  exact (conti

中文:
定理 tangentConeAt_mono_nhds
  条件: (h : 𝓝[s] x <= 𝓝[t] x)
  证明: by
  simp only [tangentConeAt_def, ofPred_subset_ofPred]
  refine fun y hy => hy.mono ?_
  gcongr _ • ?_
  rw [nhdsWithin_le_iff]
  suffices Tendsto (x + ·) (𝓝[(x + ·) ⁻¹' s] 0) (𝓝[s] x) from
.2 tendsto_nhdsWithin_iff.mp this.mono_right h
  refine .inf ?_ (mapsTo_preimage _ _).tendsto
  exact (conti

Depends on / 依赖: Tendsto, add_zero, continuous_const_add, hy.mono, mapsTo_preimage, mono_right, nhdsWithin_le_iff, ofPred_subset_ofPred, tangentConeAt_def, tendsto, tendsto_nhdsWithin_iff, tendsto_nhdsWithin_iff.mp, this.mono_right
-/
theorem tangentConeAt_mono_nhds (h : 𝓝[s] x <= 𝓝[t] x) :
    tangentConeAt 𝕜 s x subseteq tangentConeAt 𝕜 t x := by
  simp only [tangentConeAt_def, ofPred_subset_ofPred]
  refine fun y hy => hy.mono ?_
  gcongr _ • ?_
  rw [nhdsWithin_le_iff]
  suffices Tendsto (x + ·) (𝓝[(x + ·) ⁻¹' s] 0) (𝓝[s] x) from
.2 tendsto_nhdsWithin_iff.mp this.mono_right h
  refine .inf ?_ (mapsTo_preimage _ _).tendsto
  exact (continuous_const_add x).tendsto' 0 x (add_zero _)

/--
theorem `tangentConeAt_congr` / 定理 `tangentConeAt_congr`

English:
theorem tangentConeAt_congr
  given: (h : 𝓝[s] x = 𝓝[t] x)
  statement: tangentConeAt 𝕜 s x = tangentConeAt 𝕜 t x
  proof: Subset.antisymm (tangentConeAt_mono_nhds h.le) (tangentConeAt_mono_nhds h.ge)

中文:
定理 tangentConeAt_congr
  条件: (h : 𝓝[s] x = 𝓝[t] x)
  结论: tangentConeAt 𝕜 s x = tangentConeAt 𝕜 t x
  证明: Subset.antisymm (tangentConeAt_mono_nhds h.le) (tangentConeAt_mono_nhds h.ge)

Depends on / 依赖: Subset, Subset.antisymm, antisymm, h.ge, h.le, tangentConeAt_mono_nhds
-/
theorem tangentConeAt_congr (h : 𝓝[s] x = 𝓝[t] x) : tangentConeAt 𝕜 s x = tangentConeAt 𝕜 t x :=
  Subset.antisymm (tangentConeAt_mono_nhds h.le) (tangentConeAt_mono_nhds h.ge)

/--
theorem `tangentConeAt_inter_nhds` / 定理 `tangentConeAt_inter_nhds`

English:
theorem tangentConeAt_inter_nhds
  given: (ht : t in 𝓝 x)
  statement: tangentConeAt 𝕜 (s inter t) x = tangentConeAt 𝕜 s x
  proof: tangentConeAt_congr (nhdsWithin_restrict' _ ht).symm

中文:
定理 tangentConeAt_inter_nhds
  条件: (ht : t in 𝓝 x)
  结论: tangentConeAt 𝕜 (s inter t) x = tangentConeAt 𝕜 s x
  证明: tangentConeAt_congr (nhdsWithin_restrict' _ ht).symm

Depends on / 依赖: nhdsWithin_restrict, tangentConeAt_congr
-/
theorem tangentConeAt_inter_nhds (ht : t in 𝓝 x) : tangentConeAt 𝕜 (s inter t) x = tangentConeAt 𝕜 s x :=
  tangentConeAt_congr (nhdsWithin_restrict' _ ht).symm

/--
theorem `mem_closure_of_nonempty_tangentConeAt` / 定理 `mem_closure_of_nonempty_tangentConeAt`

English:
theorem mem_closure_of_nonempty_tangentConeAt
  given: (h : (tangentConeAt 𝕜 s x).Nonempty)
  proof: by
  rcases h with ⟨y, hy⟩
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, -, d, hd, hds, -⟩
  refine mem_closure_of_tendsto ?_ hds
  simpa using tendsto_const_nhds.add hd

中文:
定理 mem_closure_of_nonempty_tangentConeAt
  条件: (h : (tangentConeAt 𝕜 s x).非空)
  证明: by
  rcases h with ⟨y, hy⟩
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, -, d, hd, hds, -⟩
  refine mem_closure_of_tendsto ?_ hds
  simpa using tendsto_const_nhds.add hd

Depends on / 依赖: exists_fun_of_mem_tangentConeAt, mem_closure_of_tendsto, tendsto_const_nhds, tendsto_const_nhds.add
-/
theorem mem_closure_of_nonempty_tangentConeAt (h : (tangentConeAt 𝕜 s x).Nonempty) :
    x in closure s := by
  rcases h with ⟨y, hy⟩
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, -, d, hd, hds, -⟩
  refine mem_closure_of_tendsto ?_ hds
  simpa using tendsto_const_nhds.add hd

variable [ContinuousConstSMul 𝕜 E]

@[simp]
/--
theorem `tangentConeAt_closure` / 定理 `tangentConeAt_closure`

English:
theorem tangentConeAt_closure
  statement: tangentConeAt 𝕜 (closure s) x = tangentConeAt 𝕜 s x
  proof: by
  refine Subset.antisymm ?_ (tangentConeAt_mono subset_closure)
  simp only [(nhds_basis_opens _).tangentConeAt_eq_biInter_closure]
  refine iInter₂_mono fun U hU => closure_minimal ?_ isClosed_closure
  grw [(isOpenMap_add_left x).preimage_closure_subset_closure_preimage, hU.2.inter_closure,
   

中文:
定理 tangentConeAt_closure
  结论: tangentConeAt 𝕜 (closure s) x = tangentConeAt 𝕜 s x
  证明: by
  refine Subset.antisymm ?_ (tangentConeAt_mono subset_closure)
  simp only [(nhds_basis_opens _).tangentConeAt_eq_biInter_closure]
  refine iInter₂_mono fun U hU => closure_minimal ?_ isClosed_closure
  grw [(isOpenMap_add_left x).preimage_closure_subset_closure_preimage, hU.2.inter_closure,
   

Depends on / 依赖: Subset, Subset.antisymm, antisymm, closure_minimal, inter_closure, isClosed_closure, isOpenMap_add_left, nhds_basis_opens, preimage_closure_subset_closure_preimage, set_smul_closure_subset, subset_closure, tangentConeAt_eq_biInter_closure, tangentConeAt_mono
-/
theorem tangentConeAt_closure : tangentConeAt 𝕜 (closure s) x = tangentConeAt 𝕜 s x := by
  refine Subset.antisymm ?_ (tangentConeAt_mono subset_closure)
  simp only [(nhds_basis_opens _).tangentConeAt_eq_biInter_closure]
  refine iInter₂_mono fun U hU => closure_minimal ?_ isClosed_closure
  grw [(isOpenMap_add_left x).preimage_closure_subset_closure_preimage, hU.2.inter_closure,
    set_smul_closure_subset]

end SMul

section Module

variable [AddCommGroup E] [Semiring 𝕜] [Module 𝕜 E] [TopologicalSpace E] [ContinuousAdd E]
  {s t : Set E} {x : E}

omit [ContinuousAdd E] in
/--
theorem `UniqueDiffWithinAt.mono` / 定理 `UniqueDiffWithinAt.mono`

English:
theorem UniqueDiffWithinAt.mono
  given: (h : UniqueDiffWithinAt 𝕜 s x) (st : s subseteq t)
  proof: by
  rw [uniqueDiffWithinAt_iff] at *
  grw [← st]
  exact h

omit [ContinuousAdd E] in

中文:
定理 UniqueDiffWithinAt.mono
  条件: (h : UniqueDiffWithinAt 𝕜 s x) (st : s subseteq t)
  证明: by
  rw [uniqueDiffWithinAt_iff] at *
  grw [← st]
  exact h

omit [ContinuousAdd E] in

Depends on / 依赖: uniqueDiffWithinAt_iff
-/
theorem UniqueDiffWithinAt.mono (h : UniqueDiffWithinAt 𝕜 s x) (st : s subseteq t) :
    UniqueDiffWithinAt 𝕜 t x := by
  rw [uniqueDiffWithinAt_iff] at *
  grw [← st]
  exact h

omit [ContinuousAdd E] in
/--
theorem `UniqueDiffWithinAt.closure` / 定理 `UniqueDiffWithinAt.closure`

English:
theorem UniqueDiffWithinAt.closure
  given: (h : UniqueDiffWithinAt 𝕜 s x)
  proof: h.mono subset_closure

中文:
定理 UniqueDiffWithinAt.closure
  条件: (h : UniqueDiffWithinAt 𝕜 s x)
  证明: h.mono subset_closure
-/
protected theorem UniqueDiffWithinAt.closure (h : UniqueDiffWithinAt 𝕜 s x) :
    UniqueDiffWithinAt 𝕜 (closure s) x :=
  h.mono subset_closure

/--
theorem `UniqueDiffWithinAt.mono_nhds` / 定理 `UniqueDiffWithinAt.mono_nhds`

English:
theorem UniqueDiffWithinAt.mono_nhds
  given: (h : UniqueDiffWithinAt 𝕜 s x) (st : 𝓝[s] x <= 𝓝[t] x)
  proof: by
  simp only [uniqueDiffWithinAt_iff] at *
  rw [mem_closure_iff_nhdsWithin_neBot] at h ⊢
exact ⟨h.1.mono Submodule.span_mono tangentConeAt_mono_nhds st, h.2.mono st⟩

中文:
定理 UniqueDiffWithinAt.mono_nhds
  条件: (h : UniqueDiffWithinAt 𝕜 s x) (st : 𝓝[s] x <= 𝓝[t] x)
  证明: by
  simp only [uniqueDiffWithinAt_iff] at *
  rw [mem_closure_iff_nhdsWithin_neBot] at h ⊢
exact ⟨h.1.mono Submodule.span_mono tangentConeAt_mono_nhds st, h.2.mono st⟩

Depends on / 依赖: Submodule, Submodule.span_mono, mem_closure_iff_nhdsWithin_neBot, span_mono, tangentConeAt_mono_nhds, uniqueDiffWithinAt_iff
-/
theorem UniqueDiffWithinAt.mono_nhds (h : UniqueDiffWithinAt 𝕜 s x) (st : 𝓝[s] x <= 𝓝[t] x) :
    UniqueDiffWithinAt 𝕜 t x := by
  simp only [uniqueDiffWithinAt_iff] at *
  rw [mem_closure_iff_nhdsWithin_neBot] at h ⊢
exact ⟨h.1.mono Submodule.span_mono tangentConeAt_mono_nhds st, h.2.mono st⟩

/--
theorem `uniqueDiffWithinAt_congr` / 定理 `uniqueDiffWithinAt_congr`

English:
theorem uniqueDiffWithinAt_congr
  given: (st : 𝓝[s] x = 𝓝[t] x)
  proof: ⟨fun h => h.mono_nhds le_of_eq st, fun h => h.mono_nhds le_of_eq st.symm⟩

中文:
定理 uniqueDiffWithinAt_congr
  条件: (st : 𝓝[s] x = 𝓝[t] x)
  证明: ⟨fun h => h.mono_nhds le_of_eq st, fun h => h.mono_nhds le_of_eq st.symm⟩

Depends on / 依赖: h.mono_nhds, le_of_eq, mono_nhds, st.symm
-/
theorem uniqueDiffWithinAt_congr (st : 𝓝[s] x = 𝓝[t] x) :
    UniqueDiffWithinAt 𝕜 s x ↔ UniqueDiffWithinAt 𝕜 t x :=
⟨fun h => h.mono_nhds le_of_eq st, fun h => h.mono_nhds le_of_eq st.symm⟩

/--
theorem `uniqueDiffWithinAt_inter` / 定理 `uniqueDiffWithinAt_inter`

English:
theorem uniqueDiffWithinAt_inter
  given: (ht : t in 𝓝 x)
  proof: uniqueDiffWithinAt_congr (nhdsWithin_restrict' _ ht).symm

中文:
定理 uniqueDiffWithinAt_inter
  条件: (ht : t in 𝓝 x)
  证明: uniqueDiffWithinAt_congr (nhdsWithin_restrict' _ ht).symm

Depends on / 依赖: nhdsWithin_restrict, uniqueDiffWithinAt_congr
-/
theorem uniqueDiffWithinAt_inter (ht : t in 𝓝 x) :
    UniqueDiffWithinAt 𝕜 (s inter t) x ↔ UniqueDiffWithinAt 𝕜 s x :=
uniqueDiffWithinAt_congr (nhdsWithin_restrict' _ ht).symm

/--
theorem `UniqueDiffWithinAt.inter` / 定理 `UniqueDiffWithinAt.inter`

English:
theorem UniqueDiffWithinAt.inter
  given: (hs : UniqueDiffWithinAt 𝕜 s x) (ht : t in 𝓝 x)
  proof: (uniqueDiffWithinAt_inter ht).2 hs

中文:
定理 UniqueDiffWithinAt.inter
  条件: (hs : UniqueDiffWithinAt 𝕜 s x) (ht : t in 𝓝 x)
  证明: (uniqueDiffWithinAt_inter ht).2 hs

Depends on / 依赖: uniqueDiffWithinAt_inter
-/
theorem UniqueDiffWithinAt.inter (hs : UniqueDiffWithinAt 𝕜 s x) (ht : t in 𝓝 x) :
    UniqueDiffWithinAt 𝕜 (s inter t) x :=
  (uniqueDiffWithinAt_inter ht).2 hs

/--
theorem `UniqueDiffOn.inter` / 定理 `UniqueDiffOn.inter`

English:
theorem UniqueDiffOn.inter
  given: (hs : UniqueDiffOn 𝕜 s) (ht : IsOpen t)
  statement: UniqueDiffOn 𝕜 (s inter t)
  proof: fun x hx => (hs x hx.1).inter (IsOpen.mem_nhds ht hx.2)

中文:
定理 UniqueDiffOn.inter
  条件: (hs : UniqueDiffOn 𝕜 s) (ht : 是开集 t)
  结论: UniqueDiffOn 𝕜 (s inter t)
  证明: fun x hx => (hs x hx.1).inter (IsOpen.mem_nhds ht hx.2)

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, mem_nhds
-/
theorem UniqueDiffOn.inter (hs : UniqueDiffOn 𝕜 s) (ht : IsOpen t) : UniqueDiffOn 𝕜 (s inter t) :=
  fun x hx => (hs x hx.1).inter (IsOpen.mem_nhds ht hx.2)

/--
theorem `uniqueDiffWithinAt_inter'` / 定理 `uniqueDiffWithinAt_inter'`

English:
theorem uniqueDiffWithinAt_inter'
  given: (ht : t in 𝓝[s] x)
  proof: uniqueDiffWithinAt_congr (nhdsWithin_restrict'' _ ht).symm

中文:
定理 uniqueDiffWithinAt_inter'
  条件: (ht : t in 𝓝[s] x)
  证明: uniqueDiffWithinAt_congr (nhdsWithin_restrict'' _ ht).symm

Depends on / 依赖: nhdsWithin_restrict, uniqueDiffWithinAt_congr
-/
theorem uniqueDiffWithinAt_inter' (ht : t in 𝓝[s] x) :
    UniqueDiffWithinAt 𝕜 (s inter t) x ↔ UniqueDiffWithinAt 𝕜 s x :=
uniqueDiffWithinAt_congr (nhdsWithin_restrict'' _ ht).symm

/--
theorem `UniqueDiffWithinAt.inter'` / 定理 `UniqueDiffWithinAt.inter'`

English:
theorem UniqueDiffWithinAt.inter'
  given: (hs : UniqueDiffWithinAt 𝕜 s x) (ht : t in 𝓝[s] x)
  proof: (uniqueDiffWithinAt_inter' ht).2 hs

中文:
定理 UniqueDiffWithinAt.inter'
  条件: (hs : UniqueDiffWithinAt 𝕜 s x) (ht : t in 𝓝[s] x)
  证明: (uniqueDiffWithinAt_inter' ht).2 hs

Depends on / 依赖: uniqueDiffWithinAt_inter
-/
theorem UniqueDiffWithinAt.inter' (hs : UniqueDiffWithinAt 𝕜 s x) (ht : t in 𝓝[s] x) :
    UniqueDiffWithinAt 𝕜 (s inter t) x :=
  (uniqueDiffWithinAt_inter' ht).2 hs

/--
theorem `zero_mem_tangentConeAt` / 定理 `zero_mem_tangentConeAt`

English:
theorem zero_mem_tangentConeAt
  given: (hx : x in closure s)
  proof: by
  rw [mem_closure_iff_frequently] at hx
  apply mem_tangentConeAt_of_frequently (𝓝 x) 1 (· + (-x))
  · exact Continuous.tendsto' (by fun_prop) _ _ (by simp)
  · simpa
  · simp only [Pi.one_apply, one_smul]
    exact Continuous.tendsto' (by fun_prop) _ _ (by simp)

@[deprecated (since := "2026-01-

中文:
定理 zero_mem_tangentConeAt
  条件: (hx : x in closure s)
  证明: by
  rw [mem_closure_iff_frequently] at hx
  apply mem_tangentConeAt_of_frequently (𝓝 x) 1 (· + (-x))
  · exact Continuous.tendsto' (by fun_prop) _ _ (by simp)
  · simpa
  · simp only [Pi.one_apply, one_smul]
    exact Continuous.tendsto' (by fun_prop) _ _ (by simp)

@[deprecated (since := "2026-01-

Depends on / 依赖: Continuous, Continuous.tendsto, Pi.one_apply, fun_prop, mem_closure_iff_frequently, mem_tangentConeAt_of_frequently, one_apply, one_smul, tendsto
-/
theorem zero_mem_tangentConeAt (hx : x in closure s) :
    0 in tangentConeAt 𝕜 s x := by
  rw [mem_closure_iff_frequently] at hx
  apply mem_tangentConeAt_of_frequently (𝓝 x) 1 (· + (-x))
  · exact Continuous.tendsto' (by fun_prop) _ _ (by simp)
  · simpa
  · simp only [Pi.one_apply, one_smul]
    exact Continuous.tendsto' (by fun_prop) _ _ (by simp)

@[deprecated (since := "2026-01-21")]
alias zero_mem_tangentCone := zero_mem_tangentConeAt

@[simp]
/--
theorem `zero_mem_tangentConeAt_iff` / 定理 `zero_mem_tangentConeAt_iff`

English:
theorem zero_mem_tangentConeAt_iff
  statement: 0 in tangentConeAt 𝕜 s x ↔ x in closure s
  proof: ⟨fun h => mem_closure_of_nonempty_tangentConeAt ⟨_, h⟩, zero_mem_tangentConeAt⟩

中文:
定理 zero_mem_tangentConeAt_iff
  结论: 0 in tangentConeAt 𝕜 s x ↔ x in closure s
  证明: ⟨fun h => mem_closure_of_nonempty_tangentConeAt ⟨_, h⟩, zero_mem_tangentConeAt⟩

Depends on / 依赖: mem_closure_of_nonempty_tangentConeAt, zero_mem_tangentConeAt
-/
theorem zero_mem_tangentConeAt_iff : 0 in tangentConeAt 𝕜 s x ↔ x in closure s :=
  ⟨fun h => mem_closure_of_nonempty_tangentConeAt ⟨_, h⟩, zero_mem_tangentConeAt⟩

/--
theorem `tangentConeAt_subset_zero` / 定理 `tangentConeAt_subset_zero`

English:
theorem tangentConeAt_subset_zero
  given: [T2Space E] (hx : ¬AccPt x (𝓟 s))
  statement: tangentConeAt 𝕜 s x subseteq 0
  proof: by
  intro y hy
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  have H₁ : Tendsto (x + d ·) l (𝓝 x) := by
    simpa using tendsto_const_nhds.add hd₀
  have H₂ : forallᶠ n in l, d n = 0 := by
    simp only [accPt_iff_frequently, not_frequently, not_and', ne_eq, not_

中文:
定理 tangentConeAt_subset_zero
  条件: [T2空间 E] (hx : ¬聚点 x (𝓟 s))
  结论: tangentConeAt 𝕜 s x subseteq 0
  证明: by
  intro y hy
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  have H₁ : Tendsto (x + d ·) l (𝓝 x) := by
    simpa using tendsto_const_nhds.add hd₀
  have H₂ : forallᶠ n in l, d n = 0 := by
    simp only [accPt_iff_frequently, not_frequently, not_and', ne_eq, not_

Depends on / 依赖: Tendsto, accPt_iff_frequently, eventually, exists_fun_of_mem_tangentConeAt, hds.mp, ne_eq, not_and, not_frequently, not_not, tendsto_const_nhds, tendsto_const_nhds.add, tendsto_nhds_unique_of_eventuallyEq
-/
theorem tangentConeAt_subset_zero [T2Space E] (hx : ¬AccPt x (𝓟 s)) : tangentConeAt 𝕜 s x subseteq 0 := by
  intro y hy
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  have H₁ : Tendsto (x + d ·) l (𝓝 x) := by
    simpa using tendsto_const_nhds.add hd₀
  have H₂ : forallᶠ n in l, d n = 0 := by
    simp only [accPt_iff_frequently, not_frequently, not_and', ne_eq, not_not] at hx
    simpa using hds.mp (H₁.eventually hx)
  have H₃ : forallᶠ n in l, c n • d n = 0 := H₂.mono fun n hn => by simp [hn]
  simpa using tendsto_nhds_unique_of_eventuallyEq hcd tendsto_const_nhds H₃

/--
theorem `AccPt.of_mem_tangentConeAt_ne_zero` / 定理 `AccPt.of_mem_tangentConeAt_ne_zero`

English:
theorem AccPt.of_mem_tangentConeAt_ne_zero
  statement: [T2Space E] {y : E} (hy : y in tangentConeAt 𝕜 s x)
  proof: by
  contrapose hy₀
  exact tangentConeAt_subset_zero hy₀ hy

中文:
定理 聚点.of_mem_tangentConeAt_ne_zero
  结论: [T2空间 E] {y : E} (hy : y in tangentConeAt 𝕜 s x)
  证明: by
  contrapose hy₀
  exact tangentConeAt_subset_zero hy₀ hy

Depends on / 依赖: contrapose, tangentConeAt_subset_zero
-/
theorem AccPt.of_mem_tangentConeAt_ne_zero [T2Space E] {y : E} (hy : y in tangentConeAt 𝕜 s x)
    (hy₀ : y != 0) : AccPt x (𝓟 s) := by
  contrapose hy₀
  exact tangentConeAt_subset_zero hy₀ hy

/--
theorem `UniqueDiffWithinAt.accPt` / 定理 `UniqueDiffWithinAt.accPt`

English:
theorem UniqueDiffWithinAt.accPt
  given: [T2Space E] [Nontrivial E] (h : UniqueDiffWithinAt 𝕜 s x)
  proof: by
  by_contra! h'
  have : Dense (Submodule.span 𝕜 (0 : Set E) : Set E) :=
h.1.mono by gcongr; exact tangentConeAt_subset_zero h'
  simp [dense_iff_closure_eq] at this

中文:
定理 UniqueDiffWithinAt.accPt
  条件: [T2空间 E] [非平凡 E] (h : UniqueDiffWithinAt 𝕜 s x)
  证明: by
  by_contra! h'
  have : Dense (Submodule.span 𝕜 (0 : Set E) : Set E) :=
h.1.mono by gcongr; exact tangentConeAt_subset_zero h'
  simp [dense_iff_closure_eq] at this

Depends on / 依赖: Submodule, Submodule.span, dense_iff_closure_eq, tangentConeAt_subset_zero
-/
theorem UniqueDiffWithinAt.accPt [T2Space E] [Nontrivial E] (h : UniqueDiffWithinAt 𝕜 s x) :
    AccPt x (𝓟 s) := by
  by_contra! h'
  have : Dense (Submodule.span 𝕜 (0 : Set E) : Set E) :=
h.1.mono by gcongr; exact tangentConeAt_subset_zero h'
  simp [dense_iff_closure_eq] at this

end Module

section TVS

variable [DivisionSemiring 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace 𝕜]
  [TopologicalSpace E] [ContinuousSMul 𝕜 E] {s : Set E} {x y : E}

/--
theorem `mem_tangentConeAt_of_add_smul_mem` / 定理 `mem_tangentConeAt_of_add_smul_mem`

English:
theorem mem_tangentConeAt_of_add_smul_mem
  statement: {α : Type*} {l : Filter α} [l.NeBot] {c : α -> 𝕜}
  proof: by
  rw [tendsto_nhdsWithin_iff] at hc₀
  refine mem_tangentConeAt_of_seq l c⁻¹ (c · • y) ?_ hmem ?_
  · simpa using hc₀.1.smul (tendsto_const_nhds (x := y))
· refine tendsto_nhds_of_eventually_eq hc₀.2.mono fun n hn => ?_
    simp_all

中文:
定理 mem_tangentConeAt_of_add_smul_mem
  结论: {α : 类型} {l : 滤子 α} [l.NeBot] {c : α -> 𝕜}
  证明: by
  rw [tendsto_nhdsWithin_iff] at hc₀
  refine mem_tangentConeAt_of_seq l c⁻¹ (c · • y) ?_ hmem ?_
  · simpa using hc₀.1.smul (tendsto_const_nhds (x := y))
· refine tendsto_nhds_of_eventually_eq hc₀.2.mono fun n hn => ?_
    simp_all

Depends on / 依赖: LinearMap, LinearMap.mkContinuousOfExistsBound, continuous, exists_norm_apply_le, hbound, mem_tangentConeAt_of_seq, mkContinuousOfExistsBound, ofClass, tendsto_const_nhds, tendsto_nhdsWithin_iff, tendsto_nhds_of_eventually_eq
-/
theorem mem_tangentConeAt_of_add_smul_mem {α : Type*} {l : Filter α} [l.NeBot] {c : α -> 𝕜}
    (hc₀ : Tendsto c l (𝓝[!=] 0)) (hmem : forallᶠ n in l, x + c n • y in s) :
    y in tangentConeAt 𝕜 s x := by
  rw [tendsto_nhdsWithin_iff] at hc₀
  refine mem_tangentConeAt_of_seq l c⁻¹ (c · • y) ?_ hmem ?_
  · simpa using hc₀.1.smul (tendsto_const_nhds (x := y))
· refine tendsto_nhds_of_eventually_eq hc₀.2.mono fun n hn => ?_
    simp_all

variable [(𝓝[!=] (0 : 𝕜)).NeBot]

@[simp]
/--
theorem `tangentConeAt_univ` / 定理 `tangentConeAt_univ`

English:
theorem tangentConeAt_univ
  statement: tangentConeAt 𝕜 univ x = univ
  proof: by
  simp [tangentConeAt]

中文:
定理 tangentConeAt_univ
  结论: tangentConeAt 𝕜 univ x = univ
  证明: by
  simp [tangentConeAt]

Depends on / 依赖: tangentConeAt
-/
theorem tangentConeAt_univ : tangentConeAt 𝕜 univ x = univ := by
  simp [tangentConeAt]

/--
theorem `tangentConeAt_of_mem_nhds` / 定理 `tangentConeAt_of_mem_nhds`

English:
theorem tangentConeAt_of_mem_nhds
  given: [ContinuousAdd E] (h : s in 𝓝 x)
  statement: tangentConeAt 𝕜 s x = univ
  proof: by
  rw [← s.univ_inter]; rw [tangentConeAt_inter_nhds h]; rw [tangentConeAt_univ]

中文:
定理 tangentConeAt_of_mem_nhds
  条件: [连续加法 E] (h : s in 𝓝 x)
  结论: tangentConeAt 𝕜 s x = univ
  证明: by
  rw [← s.univ_inter]; rw [tangentConeAt_inter_nhds h]; rw [tangentConeAt_univ]

Depends on / 依赖: s.univ_inter, tangentConeAt_inter_nhds, tangentConeAt_univ, univ_inter
-/
theorem tangentConeAt_of_mem_nhds [ContinuousAdd E] (h : s in 𝓝 x) : tangentConeAt 𝕜 s x = univ := by
  rw [← s.univ_inter]; rw [tangentConeAt_inter_nhds h]; rw [tangentConeAt_univ]

end TVS

section UniqueDiff

/-!
### Properties of `UniqueDiffWithinAt` and `UniqueDiffOn`

This section is devoted to properties of the predicates `UniqueDiffWithinAt` and `UniqueDiffOn`. -/

section Semiring
variable [Semiring 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {x y : E} {s t : Set E}

/--
theorem `uniqueDiffOn_empty` / 定理 `uniqueDiffOn_empty`

English:
theorem uniqueDiffOn_empty
  statement: UniqueDiffOn 𝕜 (∅ : Set E)
  proof: fun _ hx => hx.elim

中文:
定理 uniqueDiffOn_empty
  结论: UniqueDiffOn 𝕜 (∅ : 集合 E)
  证明: fun _ hx => hx.elim

Depends on / 依赖: hx.elim
-/
theorem uniqueDiffOn_empty : UniqueDiffOn 𝕜 (∅ : Set E) :=
  fun _ hx => hx.elim

/--
theorem `UniqueDiffWithinAt.congr_pt` / 定理 `UniqueDiffWithinAt.congr_pt`

English:
theorem UniqueDiffWithinAt.congr_pt
  given: (h : UniqueDiffWithinAt 𝕜 s x) (hy : x = y)
  proof: hy ▸ h

中文:
定理 UniqueDiffWithinAt.congr_pt
  条件: (h : UniqueDiffWithinAt 𝕜 s x) (hy : x = y)
  证明: hy ▸ h
-/
theorem UniqueDiffWithinAt.congr_pt (h : UniqueDiffWithinAt 𝕜 s x) (hy : x = y) :
    UniqueDiffWithinAt 𝕜 s y := hy ▸ h

variable {𝕜' : Type*} [Semiring 𝕜'] [SMul 𝕜 𝕜'] [Module 𝕜' E] [IsScalarTower 𝕜 𝕜' E]

/--
theorem `UniqueDiffWithinAt.mono_field` / 定理 `UniqueDiffWithinAt.mono_field`

English:
theorem UniqueDiffWithinAt.mono_field
  given: (hs : UniqueDiffWithinAt 𝕜 s x)
  proof: by
  simp_all only [uniqueDiffWithinAt_iff, and_true]
  apply Dense.mono _ hs.1
  trans ↑(Submodule.span 𝕜 (tangentConeAt 𝕜' s x)) <;>
    simp [Submodule.span_mono tangentConeAt_mono_field]

中文:
定理 UniqueDiffWithinAt.mono_field
  条件: (hs : UniqueDiffWithinAt 𝕜 s x)
  证明: by
  simp_all only [uniqueDiffWithinAt_iff, and_true]
  apply Dense.mono _ hs.1
  trans ↑(Submodule.span 𝕜 (tangentConeAt 𝕜' s x)) <;>
    simp [Submodule.span_mono tangentConeAt_mono_field]

Depends on / 依赖: Dense.mono, Submodule, Submodule.span, Submodule.span_mono, and_true, span_mono, tangentConeAt, tangentConeAt_mono_field, uniqueDiffWithinAt_iff
-/
theorem UniqueDiffWithinAt.mono_field (hs : UniqueDiffWithinAt 𝕜 s x) :
    UniqueDiffWithinAt 𝕜' s x := by
  simp_all only [uniqueDiffWithinAt_iff, and_true]
  apply Dense.mono _ hs.1
  trans ↑(Submodule.span 𝕜 (tangentConeAt 𝕜' s x)) <;>
    simp [Submodule.span_mono tangentConeAt_mono_field]

/--
theorem `UniqueDiffOn.mono_field` / 定理 `UniqueDiffOn.mono_field`

English:
theorem UniqueDiffOn.mono_field
  given: (hs : UniqueDiffOn 𝕜 s)
  statement: UniqueDiffOn 𝕜' s
  proof: fun x hx => (hs x hx).mono_field

中文:
定理 UniqueDiffOn.mono_field
  条件: (hs : UniqueDiffOn 𝕜 s)
  结论: UniqueDiffOn 𝕜' s
  证明: fun x hx => (hs x hx).mono_field

Depends on / 依赖: mono_field
-/
theorem UniqueDiffOn.mono_field (hs : UniqueDiffOn 𝕜 s) : UniqueDiffOn 𝕜' s :=
  fun x hx => (hs x hx).mono_field

variable [ContinuousAdd E] [ContinuousConstSMul 𝕜 E]

@[simp]
/--
theorem `uniqueDiffWithinAt_closure` / 定理 `uniqueDiffWithinAt_closure`

English:
theorem uniqueDiffWithinAt_closure
  proof: by
  simp [uniqueDiffWithinAt_iff]

protected alias ⟨UniqueDiffWithinAt.of_closure, _⟩ := uniqueDiffWithinAt_closure

中文:
定理 uniqueDiffWithinAt_closure
  证明: by
  simp [uniqueDiffWithinAt_iff]

protected alias ⟨UniqueDiffWithinAt.of_closure, _⟩ := uniqueDiffWithinAt_closure

Depends on / 依赖: uniqueDiffWithinAt_iff
-/
theorem uniqueDiffWithinAt_closure :
    UniqueDiffWithinAt 𝕜 (closure s) x ↔ UniqueDiffWithinAt 𝕜 s x := by
  simp [uniqueDiffWithinAt_iff]

protected alias ⟨UniqueDiffWithinAt.of_closure, _⟩ := uniqueDiffWithinAt_closure

/--
theorem `UniqueDiffWithinAt.mono_closure` / 定理 `UniqueDiffWithinAt.mono_closure`

English:
theorem UniqueDiffWithinAt.mono_closure
  given: (h : UniqueDiffWithinAt 𝕜 s x) (st : s subseteq closure t)
  proof: (h.mono st).of_closure

中文:
定理 UniqueDiffWithinAt.mono_closure
  条件: (h : UniqueDiffWithinAt 𝕜 s x) (st : s subseteq closure t)
  证明: (h.mono st).of_closure

Depends on / 依赖: h.mono, of_closure
-/
theorem UniqueDiffWithinAt.mono_closure (h : UniqueDiffWithinAt 𝕜 s x) (st : s subseteq closure t) :
    UniqueDiffWithinAt 𝕜 t x :=
  (h.mono st).of_closure

end Semiring

section DivisionSemiring

variable [DivisionSemiring 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [TopologicalSpace 𝕜] [(𝓝[!=] (0 : 𝕜)).NeBot] [ContinuousSMul 𝕜 E]
  {x y : E} {s t : Set E}

@[simp]
/--
theorem `uniqueDiffWithinAt_univ` / 定理 `uniqueDiffWithinAt_univ`

English:
theorem uniqueDiffWithinAt_univ
  statement: UniqueDiffWithinAt 𝕜 univ x
  proof: by
  rw [uniqueDiffWithinAt_iff]; rw [tangentConeAt_univ]
  simp

@[simp]

中文:
定理 uniqueDiffWithinAt_univ
  结论: UniqueDiffWithinAt 𝕜 univ x
  证明: by
  rw [uniqueDiffWithinAt_iff]; rw [tangentConeAt_univ]
  simp

@[simp]

Depends on / 依赖: tangentConeAt_univ, uniqueDiffWithinAt_iff
-/
theorem uniqueDiffWithinAt_univ : UniqueDiffWithinAt 𝕜 univ x := by
  rw [uniqueDiffWithinAt_iff]; rw [tangentConeAt_univ]
  simp

@[simp]
/--
theorem `uniqueDiffOn_univ` / 定理 `uniqueDiffOn_univ`

English:
theorem uniqueDiffOn_univ
  statement: UniqueDiffOn 𝕜 (univ : Set E)
  proof: fun _ _ => uniqueDiffWithinAt_univ

中文:
定理 uniqueDiffOn_univ
  结论: UniqueDiffOn 𝕜 (univ : 集合 E)
  证明: fun _ _ => uniqueDiffWithinAt_univ

Depends on / 依赖: uniqueDiffWithinAt_univ
-/
theorem uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E) :=
  fun _ _ => uniqueDiffWithinAt_univ

variable [ContinuousAdd E]

/--
theorem `uniqueDiffWithinAt_of_mem_nhds` / 定理 `uniqueDiffWithinAt_of_mem_nhds`

English:
theorem uniqueDiffWithinAt_of_mem_nhds
  given: (h : s in 𝓝 x)
  statement: UniqueDiffWithinAt 𝕜 s x
  proof: by
  simpa only [univ_inter] using uniqueDiffWithinAt_univ.inter h

中文:
定理 uniqueDiffWithinAt_of_mem_nhds
  条件: (h : s in 𝓝 x)
  结论: UniqueDiffWithinAt 𝕜 s x
  证明: by
  simpa only [univ_inter] using uniqueDiffWithinAt_univ.inter h

Depends on / 依赖: uniqueDiffWithinAt_univ, uniqueDiffWithinAt_univ.inter, univ_inter
-/
theorem uniqueDiffWithinAt_of_mem_nhds (h : s in 𝓝 x) : UniqueDiffWithinAt 𝕜 s x := by
  simpa only [univ_inter] using uniqueDiffWithinAt_univ.inter h

/--
theorem `IsOpen.uniqueDiffWithinAt` / 定理 `IsOpen.uniqueDiffWithinAt`

English:
theorem IsOpen.uniqueDiffWithinAt
  given: (hs : IsOpen s) (xs : x in s)
  statement: UniqueDiffWithinAt 𝕜 s x
  proof: uniqueDiffWithinAt_of_mem_nhds (IsOpen.mem_nhds hs xs)

中文:
定理 是开集.uniqueDiffWithinAt
  条件: (hs : 是开集 s) (xs : x in s)
  结论: UniqueDiffWithinAt 𝕜 s x
  证明: uniqueDiffWithinAt_of_mem_nhds (IsOpen.mem_nhds hs xs)

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, mem_nhds, uniqueDiffWithinAt_of_mem_nhds
-/
theorem IsOpen.uniqueDiffWithinAt (hs : IsOpen s) (xs : x in s) : UniqueDiffWithinAt 𝕜 s x :=
  uniqueDiffWithinAt_of_mem_nhds (IsOpen.mem_nhds hs xs)

/--
theorem `IsOpen.uniqueDiffOn` / 定理 `IsOpen.uniqueDiffOn`

English:
theorem IsOpen.uniqueDiffOn
  given: (hs : IsOpen s)
  statement: UniqueDiffOn 𝕜 s
  proof: fun _ hx => IsOpen.uniqueDiffWithinAt hs hx

中文:
定理 是开集.uniqueDiffOn
  条件: (hs : 是开集 s)
  结论: UniqueDiffOn 𝕜 s
  证明: fun _ hx => IsOpen.uniqueDiffWithinAt hs hx

Depends on / 依赖: IsOpen, IsOpen.uniqueDiffWithinAt, uniqueDiffWithinAt
-/
theorem IsOpen.uniqueDiffOn (hs : IsOpen s) : UniqueDiffOn 𝕜 s :=
  fun _ hx => IsOpen.uniqueDiffWithinAt hs hx

end DivisionSemiring

end UniqueDiff
