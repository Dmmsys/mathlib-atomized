/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Topology.Instances.Matrix

/-!
# Topology on matrix groups

Lemmas about the topology of matrix groups, such as `GL(n, R)` and `SL(n, R)` for a
topological ring `R`.
-/

public section

open Matrix Topology

variable {n R S : Type*} [Fintype n] [DecidableEq n]
  [CommRing R] [TopologicalSpace R] [CommRing S] [TopologicalSpace S] {f : R ->+* S}

/-!
### Topology of the general linear group
-/

namespace Matrix.GeneralLinearGroup

@[fun_prop]
/--
theorem `continuous_apply` / 定理 `continuous_apply`

English:
theorem continuous_apply
  statement: {α : Type*} [TopologicalSpace α]
  proof: (by fun_prop : Continuous fun A : Matrix n n R => A i).comp by fun_prop

@[fun_prop]

中文:
定理 continuous_apply
  结论: {α : 类型} [TopologicalSpace α]
  证明: (by fun_prop : Continuous fun A : Matrix n n R => A i).comp by fun_prop

@[fun_prop]

Depends on / 依赖: Continuous, Matrix, fun_prop
-/
theorem continuous_apply {α : Type*} [TopologicalSpace α]
    (f : α -> GL n R) (hf : Continuous f) (i : n) :
    Continuous (fun x => f x i) :=
(by fun_prop : Continuous fun A : Matrix n n R => A i).comp by fun_prop

@[fun_prop]
/--
lemma `_root_.Continuous.generalLinearGroup_map` / 引理 `_root_.Continuous.generalLinearGroup_map`

English:
lemma _root_.Continuous.generalLinearGroup_map
  given: (hf : Continuous f)
  proof: (continuous_id.matrix_map hf).units_map

中文:
引理 _root_.Continuous.generalLinearGroup_map
  条件: (hf : Continuous f)
  证明: (continuous_id.matrix_map hf).units_map
-/
lemma _root_.Continuous.generalLinearGroup_map (hf : Continuous f) :
    Continuous (map (n := n) f) :=
  (continuous_id.matrix_map hf).units_map

/--
lemma `_root_.Topology.IsInducing.generalLinearGroup_map` / 引理 `_root_.Topology.IsInducing.generalLinearGroup_map`

English:
lemma _root_.Topology.IsInducing.generalLinearGroup_map
  given: (hf : IsInducing f)
  proof: hf.matrix_map.units_map

中文:
引理 _root_.Topology.IsInducing.generalLinearGroup_map
  条件: (hf : IsInducing f)
  证明: hf.matrix_map.units_map
-/
lemma _root_.Topology.IsInducing.generalLinearGroup_map (hf : IsInducing f) :
    IsInducing (map (n := n) f) :=
  hf.matrix_map.units_map

/--
lemma `_root_.Topology.IsEmbedding.generalLinearGroup_map` / 引理 `_root_.Topology.IsEmbedding.generalLinearGroup_map`

English:
lemma _root_.Topology.IsEmbedding.generalLinearGroup_map
  given: (hf : IsEmbedding f)
  proof: hf.matrix_map.units_map

中文:
引理 _root_.Topology.IsEmbedding.generalLinearGroup_map
  条件: (hf : IsEmbedding f)
  证明: hf.matrix_map.units_map
-/
lemma _root_.Topology.IsEmbedding.generalLinearGroup_map (hf : IsEmbedding f) :
    IsEmbedding (map (n := n) f) :=
  hf.matrix_map.units_map

variable [IsTopologicalRing R]

/--
lemma `_root_.Topology.IsClosedEmbedding.generalLinearGroup_map` / 引理 `_root_.Topology.IsClosedEmbedding.generalLinearGroup_map`

English:
lemma _root_.Topology.IsClosedEmbedding.generalLinearGroup_map
  statement: [T0Space R]
  proof: hf.matrix_map.units_map

中文:
引理 _root_.Topology.IsClosedEmbedding.generalLinearGroup_map
  结论: [T0Space R]
  证明: hf.matrix_map.units_map
-/
lemma _root_.Topology.IsClosedEmbedding.generalLinearGroup_map [T0Space R]
    (hf : IsClosedEmbedding f) : IsClosedEmbedding (map (n := n) f) :=
  hf.matrix_map.units_map

/--
lemma `continuous_det` / 引理 `continuous_det`

English:
lemma continuous_det
  proof: by
  simp_rw [Units.continuous_iff, ← map_inv]
  constructor <;> fun_prop

@[continuity, fun_prop]

中文:
引理 continuous_det
  证明: by
  simp_rw [Units.continuous_iff, ← map_inv]
  constructor <;> fun_prop

@[continuity, fun_prop]
-/
@[continuity, fun_prop] protected lemma continuous_det :
    Continuous (det : GL n R -> Rˣ) := by
  simp_rw [Units.continuous_iff, ← map_inv]
  constructor <;> fun_prop

@[continuity, fun_prop]
/--
lemma `continuous_upperRightHom` / 引理 `continuous_upperRightHom`

English:
lemma continuous_upperRightHom
  given: {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
  proof: by
  simp only [continuous_induced_rng, Function.comp_def, upperRightHom_apply,
    Units.embedProduct_apply, Units.inv_mk, continuous_prodMk, MulOpposite.unop_op]
  constructor <;>
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [continuous_const, continuous_neg,

中文:
引理 continuous_upperRightHom
  条件: {R : 类型} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
  证明: by
  simp only [continuous_induced_rng, Function.comp_def, upperRightHom_apply,
    Units.embedProduct_apply, Units.inv_mk, continuous_prodMk, MulOpposite.unop_op]
  constructor <;>
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [continuous_const, continuous_neg,

Depends on / 依赖: Function, Function.comp_def, MulOpposite, MulOpposite.unop_op, Units.embedProduct_apply, Units.inv_mk, comp_def, continuous_const, continuous_id, continuous_induced_rng, continuous_matrix, continuous_neg, continuous_prodMk, embedProduct_apply, fin_cases, inv_mk, unop_op, upperRightHom_apply
-/
lemma continuous_upperRightHom {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (upperRightHom (R := R)) := by
  simp only [continuous_induced_rng, Function.comp_def, upperRightHom_apply,
    Units.embedProduct_apply, Units.inv_mk, continuous_prodMk, MulOpposite.unop_op]
  constructor <;>
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [continuous_const, continuous_neg, continuous_id']

end Matrix.GeneralLinearGroup

/-!
### Topology of the special linear group
-/
namespace Matrix.SpecialLinearGroup

local notation "SL" => SpecialLinearGroup

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace (SL n R)
  body: inferInstanceAs TopologicalSpace (Subtype _)

@[fun_prop]

中文:
实例 :
  签名: TopologicalSpace (SL n R)
  定义体: inferInstanceAs TopologicalSpace (Subtype _)

@[fun_prop]

Depends on / 依赖: Subtype, TopologicalSpace
-/
instance : TopologicalSpace (SL n R) :=
inferInstanceAs TopologicalSpace (Subtype _)

@[fun_prop]
/--
theorem `continuous_apply` / 定理 `continuous_apply`

English:
theorem continuous_apply
  statement: {α : Type*} [TopologicalSpace α]
  proof: (by fun_prop : Continuous fun A : Matrix n n R => A i).comp by fun_prop

中文:
定理 continuous_apply
  结论: {α : 类型} [TopologicalSpace α]
  证明: (by fun_prop : Continuous fun A : Matrix n n R => A i).comp by fun_prop

Depends on / 依赖: Continuous, Matrix, fun_prop
-/
theorem continuous_apply {α : Type*} [TopologicalSpace α]
    (f : α -> SL n R) (hf : Continuous f) (i) :
    Continuous (fun x => f x i) :=
(by fun_prop : Continuous fun A : Matrix n n R => A i).comp by fun_prop

/-- The topology on `SL n R` is functorial in `R`. -/
@[fun_prop]
/--
lemma `_root_.Continuous.specialLinearGroup_map` / 引理 `_root_.Continuous.specialLinearGroup_map`

English:
lemma _root_.Continuous.specialLinearGroup_map
  given: (hf : Continuous f)
  proof: by
  refine IsInducing.subtypeVal.continuous_iff.mpr ?_
  exact (continuous_id.matrix_map hf).comp continuous_subtype_val

中文:
引理 _root_.Continuous.specialLinearGroup_map
  条件: (hf : Continuous f)
  证明: by
  refine IsInducing.subtypeVal.continuous_iff.mpr ?_
  exact (continuous_id.matrix_map hf).comp continuous_subtype_val

Depends on / 依赖: IsInducing, IsInducing.subtypeVal.continuous_iff.mpr, continuous_id, continuous_id.matrix_map, continuous_iff, continuous_subtype_val, matrix_map, subtypeVal
-/
lemma _root_.Continuous.specialLinearGroup_map (hf : Continuous f) :
    Continuous (map (n := n) f) := by
  refine IsInducing.subtypeVal.continuous_iff.mpr ?_
  exact (continuous_id.matrix_map hf).comp continuous_subtype_val

/--
lemma `_root_.Topology.IsInducing.specialLinearGroup_map` / 引理 `_root_.Topology.IsInducing.specialLinearGroup_map`

English:
lemma _root_.Topology.IsInducing.specialLinearGroup_map
  given: (hf : IsInducing f)
  proof: (hf.matrix_map.comp .subtypeVal).of_comp (by fun_prop) continuous_subtype_val

中文:
引理 _root_.Topology.IsInducing.specialLinearGroup_map
  条件: (hf : IsInducing f)
  证明: (hf.matrix_map.comp .subtypeVal).of_comp (by fun_prop) continuous_subtype_val
-/
lemma _root_.Topology.IsInducing.specialLinearGroup_map (hf : IsInducing f) :
    IsInducing (map (n := n) f) :=
  (hf.matrix_map.comp .subtypeVal).of_comp (by fun_prop) continuous_subtype_val

/--
lemma `_root_.Topology.IsEmbedding.specialLinearGroup_map` / 引理 `_root_.Topology.IsEmbedding.specialLinearGroup_map`

English:
lemma _root_.Topology.IsEmbedding.specialLinearGroup_map
  given: (hf : IsEmbedding f)
  proof: (hf.matrix_map.comp .subtypeVal).of_comp (by fun_prop) continuous_subtype_val

中文:
引理 _root_.Topology.IsEmbedding.specialLinearGroup_map
  条件: (hf : IsEmbedding f)
  证明: (hf.matrix_map.comp .subtypeVal).of_comp (by fun_prop) continuous_subtype_val
-/
lemma _root_.Topology.IsEmbedding.specialLinearGroup_map (hf : IsEmbedding f) :
    IsEmbedding (map (n := n) f) :=
  (hf.matrix_map.comp .subtypeVal).of_comp (by fun_prop) continuous_subtype_val

variable [IsTopologicalRing R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DiscreteTopology
  signature: R] : DiscreteTopology (SL n R)
  body: inferInstanceAs DiscreteTopology (Subtype _)

中文:
实例 [DiscreteTopology
  签名: R] : DiscreteTopology (SL n R)
  定义体: inferInstanceAs DiscreteTopology (Subtype _)

Depends on / 依赖: DiscreteTopology, Subtype
-/
instance [DiscreteTopology R] : DiscreteTopology (SL n R) :=
inferInstanceAs DiscreteTopology (Subtype _)

/--
lemma `isClosedEmbedding_val` / 引理 `isClosedEmbedding_val`

English:
lemma isClosedEmbedding_val
  given: [T1Space R]
  proof: (isClosed_singleton.preimage continuous_id.matrix_det).isClosedEmbedding_subtypeVal

中文:
引理 isClosedEmbedding_val
  条件: [T1Space R]
  证明: (isClosed_singleton.preimage continuous_id.matrix_det).isClosedEmbedding_subtypeVal

Depends on / 依赖: continuous_id, continuous_id.matrix_det, isClosedEmbedding_subtypeVal, isClosed_singleton, isClosed_singleton.preimage, matrix_det, preimage
-/
lemma isClosedEmbedding_val [T1Space R] :
    IsClosedEmbedding ((↑) : SL n R -> Matrix n n R) :=
  (isClosed_singleton.preimage continuous_id.matrix_det).isClosedEmbedding_subtypeVal

/--
lemma `_root_.Topology.IsClosedEmbedding.specialLinearGroup_map` / 引理 `_root_.Topology.IsClosedEmbedding.specialLinearGroup_map`

English:
lemma _root_.Topology.IsClosedEmbedding.specialLinearGroup_map
  statement: [T1Space R]
  proof: (hf.matrix_map.comp isClosedEmbedding_val).of_comp .subtypeVal

中文:
引理 _root_.Topology.IsClosedEmbedding.specialLinearGroup_map
  结论: [T1Space R]
  证明: (hf.matrix_map.comp isClosedEmbedding_val).of_comp .subtypeVal
-/
lemma _root_.Topology.IsClosedEmbedding.specialLinearGroup_map [T1Space R]
    (hf : IsClosedEmbedding f) : IsClosedEmbedding (map (n := n) f) :=
  (hf.matrix_map.comp isClosedEmbedding_val).of_comp .subtypeVal

/--
Instance `instT1Space` / 实例 `instT1Space`

English:
instance instT1Space
  signature: [T1Space R]
  body: isClosedEmbedding_val.isEmbedding.t1Space

中文:
实例 instT1Space
  签名: [T1Space R]
  定义体: isClosedEmbedding_val.isEmbedding.t1Space

Depends on / 依赖: isClosedEmbedding_val, isClosedEmbedding_val.isEmbedding.t1Space, isEmbedding, t1Space
-/
instance instT1Space [T1Space R] : T1Space (SL n R) := isClosedEmbedding_val.isEmbedding.t1Space

/--
Instance `topologicalGroup` / 实例 `topologicalGroup`

English:
instance topologicalGroup
  signature: : IsTopologicalGroup (SL n R) where
  body: continuous_induced_rng.mpr continuous_induced_dom.matrix_adjugate
continuous_mul := continuous_induced_rng.mpr
    (continuous_induced_dom.comp continuous_fst).mul (continuous_induced_dom.comp continuous_snd)

中文:
实例 topologicalGroup
  签名: : IsTopologicalGroup (SL n R) where
  定义体: continuous_induced_rng.mpr continuous_induced_dom.matrix_adjugate
continuous_mul := continuous_induced_rng.mpr
    (continuous_induced_dom.comp continuous_fst).mul (continuous_induced_dom.comp continuous_snd)

Depends on / 依赖: continuous_induced_dom, continuous_induced_dom.matrix_adjugate, continuous_induced_rng, continuous_induced_rng.mpr, matrix_adjugate
-/
instance topologicalGroup : IsTopologicalGroup (SL n R) where
  continuous_inv := continuous_induced_rng.mpr continuous_induced_dom.matrix_adjugate
continuous_mul := continuous_induced_rng.mpr
    (continuous_induced_dom.comp continuous_fst).mul (continuous_induced_dom.comp continuous_snd)

/-!
### Mapping `SL(n, R)` to `GL(n, R)`
-/
section toGL

/-- The natural map from `SL n A` to `GL n A` is continuous. -/
@[fun_prop]
/--
lemma `continuous_toGL` / 引理 `continuous_toGL`

English:
lemma continuous_toGL
  statement: Continuous (toGL : SL n R -> GL n R)
  proof: by
  simp_rw [Units.continuous_iff, ← map_inv]
  constructor <;> fun_prop

中文:
引理 continuous_toGL
  结论: Continuous (toGL : SL n R -> GL n R)
  证明: by
  simp_rw [Units.continuous_iff, ← map_inv]
  constructor <;> fun_prop

Depends on / 依赖: Units.continuous_iff, continuous_iff, fun_prop, map_inv, simp_rw
-/
lemma continuous_toGL : Continuous (toGL : SL n R -> GL n R) := by
  simp_rw [Units.continuous_iff, ← map_inv]
  constructor <;> fun_prop

/--
lemma `isInducing_toGL` / 引理 `isInducing_toGL`

English:
lemma isInducing_toGL
  statement: IsInducing (toGL : SL n R -> GL n R)
  proof: .of_comp continuous_toGL Units.continuous_val (IsInducing.induced _)

中文:
引理 isInducing_toGL
  结论: IsInducing (toGL : SL n R -> GL n R)
  证明: .of_comp continuous_toGL Units.continuous_val (IsInducing.induced _)

Depends on / 依赖: IsInducing, IsInducing.induced, Units.continuous_val, continuous_toGL, continuous_val, induced, of_comp
-/
lemma isInducing_toGL : IsInducing (toGL : SL n R -> GL n R) :=
  .of_comp continuous_toGL Units.continuous_val (IsInducing.induced _)

/--
lemma `isEmbedding_toGL` / 引理 `isEmbedding_toGL`

English:
lemma isEmbedding_toGL
  statement: IsEmbedding (toGL : SL n R -> GL n R)
  proof: ⟨isInducing_toGL, toGL_injective⟩

中文:
引理 isEmbedding_toGL
  结论: IsEmbedding (toGL : SL n R -> GL n R)
  证明: ⟨isInducing_toGL, toGL_injective⟩

Depends on / 依赖: isInducing_toGL, toGL_injective
-/
lemma isEmbedding_toGL : IsEmbedding (toGL : SL n R -> GL n R) :=
  ⟨isInducing_toGL, toGL_injective⟩

/--
theorem `range_toGL` / 定理 `range_toGL`

English:
theorem range_toGL
  given: {A : Type*} [CommRing A]
  proof: by
  ext x
  simpa [Units.ext_iff] using ⟨fun ⟨y, hy⟩ => by simp [← hy], fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

中文:
定理 range_toGL
  条件: {A : 类型} [CommRing A]
  证明: by
  ext x
  simpa [Units.ext_iff] using ⟨fun ⟨y, hy⟩ => by simp [← hy], fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

Depends on / 依赖: Units.ext_iff, ext_iff
-/
theorem range_toGL {A : Type*} [CommRing A] :
    Set.range (toGL : SL n A -> GL n A) = GeneralLinearGroup.det ⁻¹' {1} := by
  ext x
  simpa [Units.ext_iff] using ⟨fun ⟨y, hy⟩ => by simp [← hy], fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

/--
lemma `isClosedEmbedding_toGL` / 引理 `isClosedEmbedding_toGL`

English:
lemma isClosedEmbedding_toGL
  given: [T0Space R]
  statement: IsClosedEmbedding (toGL : SL n R -> GL n R)
  proof: ⟨isEmbedding_toGL, by simpa [range_toGL] using isClosed_singleton.preimage by fun_prop⟩

中文:
引理 isClosedEmbedding_toGL
  条件: [T0Space R]
  结论: IsClosedEmbedding (toGL : SL n R -> GL n R)
  证明: ⟨isEmbedding_toGL, by simpa [range_toGL] using isClosed_singleton.preimage by fun_prop⟩

Depends on / 依赖: fun_prop, isClosed_singleton, isClosed_singleton.preimage, isEmbedding_toGL, preimage, range_toGL
-/
lemma isClosedEmbedding_toGL [T0Space R] : IsClosedEmbedding (toGL : SL n R -> GL n R) :=
⟨isEmbedding_toGL, by simpa [range_toGL] using isClosed_singleton.preimage by fun_prop⟩

end toGL

section mapGL

/-!
### Shortcuts for the composite `SL(n, R) → GL(n, S)`
-/
variable [Algebra R S] [IsTopologicalRing S]

omit [IsTopologicalRing R]

/--
lemma `continuous_mapGL` / 引理 `continuous_mapGL`

English:
lemma continuous_mapGL
  given: [ContinuousSMul R S]
  statement: Continuous (mapGL S : SL n R -> _)
  proof: continuous_toGL.comp
    (continuous_algebraMap_iff_smul R S |>.2 continuous_smul).specialLinearGroup_map

中文:
引理 continuous_mapGL
  条件: [ContinuousSMul R S]
  结论: Continuous (mapGL S : SL n R -> _)
  证明: continuous_toGL.comp
    (continuous_algebraMap_iff_smul R S |>.2 continuous_smul).specialLinearGroup_map

Depends on / 依赖: continuous_algebraMap_iff_smul, continuous_smul, continuous_toGL, continuous_toGL.comp, specialLinearGroup_map
-/
lemma continuous_mapGL [ContinuousSMul R S] : Continuous (mapGL S : SL n R -> _) :=
  continuous_toGL.comp
    (continuous_algebraMap_iff_smul R S |>.2 continuous_smul).specialLinearGroup_map

/--
lemma `isInducing_mapGL` / 引理 `isInducing_mapGL`

English:
lemma isInducing_mapGL
  given: (h : IsInducing (algebraMap R S))
  proof: isInducing_toGL.comp h.specialLinearGroup_map

中文:
引理 isInducing_mapGL
  条件: (h : IsInducing (algebraMap R S))
  证明: isInducing_toGL.comp h.specialLinearGroup_map

Depends on / 依赖: h.specialLinearGroup_map, isInducing_toGL, isInducing_toGL.comp, specialLinearGroup_map
-/
lemma isInducing_mapGL (h : IsInducing (algebraMap R S)) :
    IsInducing (mapGL S : SL n R -> _) :=
  isInducing_toGL.comp h.specialLinearGroup_map

/--
lemma `isEmbedding_mapGL` / 引理 `isEmbedding_mapGL`

English:
lemma isEmbedding_mapGL
  given: (h : IsEmbedding (algebraMap R S))
  proof: isEmbedding_toGL.comp h.specialLinearGroup_map

中文:
引理 isEmbedding_mapGL
  条件: (h : IsEmbedding (algebraMap R S))
  证明: isEmbedding_toGL.comp h.specialLinearGroup_map

Depends on / 依赖: h.specialLinearGroup_map, isEmbedding_toGL, isEmbedding_toGL.comp, specialLinearGroup_map
-/
lemma isEmbedding_mapGL (h : IsEmbedding (algebraMap R S)) :
    IsEmbedding (mapGL S : SL n R -> _) :=
  isEmbedding_toGL.comp h.specialLinearGroup_map

/--
lemma `isClosedEmbedding_mapGL` / 引理 `isClosedEmbedding_mapGL`

English:
lemma isClosedEmbedding_mapGL
  statement: [IsTopologicalRing R] [T1Space R] [T1Space S]
  proof: isClosedEmbedding_toGL.comp h.specialLinearGroup_map

中文:
引理 isClosedEmbedding_mapGL
  结论: [IsTopologicalRing R] [T1Space R] [T1Space S]
  证明: isClosedEmbedding_toGL.comp h.specialLinearGroup_map

Depends on / 依赖: h.specialLinearGroup_map, isClosedEmbedding_toGL, isClosedEmbedding_toGL.comp, specialLinearGroup_map
-/
lemma isClosedEmbedding_mapGL [IsTopologicalRing R] [T1Space R] [T1Space S]
    (h : IsClosedEmbedding (algebraMap R S)) :
    IsClosedEmbedding (mapGL S : SL n R -> _) :=
  isClosedEmbedding_toGL.comp h.specialLinearGroup_map

end mapGL

end Matrix.SpecialLinearGroup

end
