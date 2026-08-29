/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!

# Partially defined linear operators on Hilbert spaces

We will develop the basics of the theory of unbounded operators on Hilbert spaces.

## Main definitions

* `LinearPMap.IsFormalAdjoint`: An operator `T` is a formal adjoint of `S` if for all `x` in the
  domain of `T` and `y` in the domain of `S`, we have that `⟪T x, y⟫ = ⟪x, S y⟫`.
* `LinearPMap.adjoint`: The adjoint of a map `E →ₗ.[𝕜] F` as a map `F →ₗ.[𝕜] E`.

## Main statements

* `LinearPMap.adjoint_isFormalAdjoint`: The adjoint is a formal adjoint
* `LinearPMap.IsFormalAdjoint.le_adjoint`: Every formal adjoint is contained in the adjoint
* `ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense`: The adjoint on
  `ContinuousLinearMap` and `LinearPMap` coincide.
* `LinearPMap.adjoint_isClosed`: The adjoint is a closed operator.
* `IsSelfAdjoint.isClosed`: Every self-adjoint operator is closed.

## Notation

* For `T : E →ₗ.[𝕜] F` the adjoint can be written as `T†`.
  This notation is localized in `LinearPMap`.

## Implementation notes

We use the junk value pattern to define the adjoint for all `LinearPMap`s. In the case that
`T : E →ₗ.[𝕜] F` is not densely defined the adjoint `T†` is the zero map from `T.adjoint.domain` to
`E`.

## References

* [J. Weidmann, *Linear Operators in Hilbert Spaces*][weidmann_linear]

## Tags

Unbounded operators, closed operators
-/

@[expose] public section


noncomputable section

open RCLike LinearPMap WithLp

open scoped ComplexConjugate

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace LinearPMap

/--
Definition of `IsFormalAdjoint` / `IsFormalAdjoint` 的定义

English:
definition IsFormalAdjoint
  signature: (T : E ->ₗ.[𝕜] F) (S : F ->ₗ.[𝕜] E)
  body: forall (x : T.domain) (y : S.domain), ⟪T x, y⟫ = ⟪(x : E), S y⟫

中文:
定义 IsFormalAdjoint
  签名: (T : E ->ₗ.[𝕜] F) (S : F ->ₗ.[𝕜] E)
  定义体: forall (x : T.domain) (y : S.domain), ⟪T x, y⟫ = ⟪(x : E), S y⟫

Depends on / 依赖: S.domain, T.domain, domain
-/
def IsFormalAdjoint (T : E ->ₗ.[𝕜] F) (S : F ->ₗ.[𝕜] E) : Prop :=
  forall (x : T.domain) (y : S.domain), ⟪T x, y⟫ = ⟪(x : E), S y⟫

variable {T : E ->ₗ.[𝕜] F} {S : F ->ₗ.[𝕜] E}

@[symm]
/--
theorem `IsFormalAdjoint.symm` / 定理 `IsFormalAdjoint.symm`

English:
theorem IsFormalAdjoint.symm
  given: (h : T.IsFormalAdjoint S)
  proof: fun y _ => by
  rw [← inner_conj_symm]; rw [← inner_conj_symm (y : F)]; rw [h]

中文:
定理 IsFormalAdjoint.symm
  条件: (h : T.IsFormalAdjoint S)
  证明: fun y _ => by
  rw [← inner_conj_symm]; rw [← inner_conj_symm (y : F)]; rw [h]
-/
protected theorem IsFormalAdjoint.symm (h : T.IsFormalAdjoint S) :
    S.IsFormalAdjoint T := fun y _ => by
  rw [← inner_conj_symm]; rw [← inner_conj_symm (y : F)]; rw [h]

variable (T)

/--
Definition of `adjointDomain` / `adjointDomain` 的定义

English:
definition adjointDomain
  signature: : Submodule 𝕜 F where
  body: {y | Continuous ((innerₛₗ 𝕜 y).comp T.toFun)}
  zero_mem' := by
    rw [Set.mem_ofPred_eq]; rw [LinearMap.map_zero]; rw [LinearMap.zero_comp]
    exact continuous_zero
  add_mem' hx hy := by rw [Set.mem_ofPred_eq, LinearMap.map_add] at *; exact hx.add hy
  smul_mem' a x hx := by
    rw [Set.mem_ofPr

中文:
定义 adjointDomain
  签名: : 子模 𝕜 F where
  定义体: {y | Continuous ((innerₛₗ 𝕜 y).comp T.toFun)}
  zero_mem' := by
    rw [Set.mem_ofPred_eq]; rw [LinearMap.map_zero]; rw [LinearMap.zero_comp]
    exact continuous_zero
  add_mem' hx hy := by rw [Set.mem_ofPred_eq, LinearMap.map_add] at *; exact hx.add hy
  smul_mem' a x hx := by
    rw [Set.mem_ofPr

Depends on / 依赖: Continuous, T.toFun
-/
def adjointDomain : Submodule 𝕜 F where
  carrier := {y | Continuous ((innerₛₗ 𝕜 y).comp T.toFun)}
  zero_mem' := by
    rw [Set.mem_ofPred_eq]; rw [LinearMap.map_zero]; rw [LinearMap.zero_comp]
    exact continuous_zero
  add_mem' hx hy := by rw [Set.mem_ofPred_eq, LinearMap.map_add] at *; exact hx.add hy
  smul_mem' a x hx := by
    rw [Set.mem_ofPred_eq]; rw [LinearMap.map_smulₛₗ] at *
    exact hx.const_smul (conj a)

/--
Definition of `adjointDomainMkCLM` / `adjointDomainMkCLM` 的定义

English:
definition adjointDomainMkCLM
  signature: (y : T.adjointDomain)
  body: ⟨(innerₛₗ 𝕜 (y : F)).comp T.toFun, y.prop⟩

中文:
定义 adjointDomainMkCLM
  签名: (y : T.adjointDomain)
  定义体: ⟨(innerₛₗ 𝕜 (y : F)).comp T.toFun, y.prop⟩

Depends on / 依赖: T.toFun, y.prop
-/
def adjointDomainMkCLM (y : T.adjointDomain) : StrongDual 𝕜 T.domain :=
  ⟨(innerₛₗ 𝕜 (y : F)).comp T.toFun, y.prop⟩

/--
theorem `adjointDomainMkCLM_apply` / 定理 `adjointDomainMkCLM_apply`

English:
theorem adjointDomainMkCLM_apply
  given: (y : T.adjointDomain) (x : T.domain)
  proof: rfl

中文:
定理 adjointDomainMkCLM_apply
  条件: (y : T.adjointDomain) (x : T.domain)
  证明: rfl
-/
theorem adjointDomainMkCLM_apply (y : T.adjointDomain) (x : T.domain) :
    adjointDomainMkCLM T y x = ⟪(y : F), T x⟫ :=
  rfl

/--
Definition of `adjointDomainMkCLMExtend` / `adjointDomainMkCLMExtend` 的定义

English:
definition adjointDomainMkCLMExtend
  signature: (y : T.adjointDomain)
  body: (T.adjointDomainMkCLM y).extend (Submodule.subtypeL T.domain)

中文:
定义 adjointDomainMkCLMExtend
  签名: (y : T.adjointDomain)
  定义体: (T.adjointDomainMkCLM y).extend (Submodule.subtypeL T.domain)

Depends on / 依赖: Submodule, Submodule.subtypeL, T.adjointDomainMkCLM, T.domain, adjointDomainMkCLM, domain, extend, subtypeL
-/
def adjointDomainMkCLMExtend (y : T.adjointDomain) : StrongDual 𝕜 E :=
  (T.adjointDomainMkCLM y).extend (Submodule.subtypeL T.domain)

variable {T}

@[simp]
/--
theorem `adjointDomainMkCLMExtend_apply` / 定理 `adjointDomainMkCLMExtend_apply`

English:
theorem adjointDomainMkCLMExtend_apply
  statement: (hT : Dense (T.domain : Set E)) (y : T.adjointDomain)
  proof: ContinuousLinearMap.extend_eq _ hT.denseRange_val
    isUniformEmbedding_subtype_val.isUniformInducing _

中文:
定理 adjointDomainMkCLMExtend_apply
  结论: (hT : 稠密 (T.domain : 集合 E)) (y : T.adjointDomain)
  证明: ContinuousLinearMap.extend_eq _ hT.denseRange_val
    isUniformEmbedding_subtype_val.isUniformInducing _

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.extend_eq, denseRange_val, extend_eq, hT.denseRange_val, isUniformEmbedding_subtype_val, isUniformEmbedding_subtype_val.isUniformInducing, isUniformInducing
-/
theorem adjointDomainMkCLMExtend_apply (hT : Dense (T.domain : Set E)) (y : T.adjointDomain)
    (x : T.domain) : adjointDomainMkCLMExtend T y (x : E) = ⟪(y : F), T x⟫ :=
  ContinuousLinearMap.extend_eq _ hT.denseRange_val
    isUniformEmbedding_subtype_val.isUniformInducing _

variable [CompleteSpace E]

variable (hT : Dense (T.domain : Set E))

/--
Definition of `adjointAux` / `adjointAux` 的定义

English:
definition adjointAux
  signature: : T.adjointDomain ->ₗ[𝕜] E where
  body: (InnerProductSpace.toDual 𝕜 E).symm (adjointDomainMkCLMExtend T y)
  map_add' x y :=
    hT.eq_of_inner_left 𝕜 fun z zin => by
      simp [InnerProductSpace.toDual_symm_apply, inner_add_left,
        adjointDomainMkCLMExtend_apply hT _ ⟨z, zin⟩, inner_add_left]
  map_smul' _ _ :=
    hT.eq_of_inner_

中文:
定义 adjointAux
  签名: : T.adjointDomain ->ₗ[𝕜] E where
  定义体: (InnerProductSpace.toDual 𝕜 E).symm (adjointDomainMkCLMExtend T y)
  map_add' x y :=
    hT.eq_of_inner_left 𝕜 fun z zin => by
      simp [InnerProductSpace.toDual_symm_apply, inner_add_left,
        adjointDomainMkCLMExtend_apply hT _ ⟨z, zin⟩, inner_add_left]
  map_smul' _ _ :=
    hT.eq_of_inner_

Depends on / 依赖: InnerProductSpace, InnerProductSpace.toDual, adjointDomainMkCLMExtend, toDual
-/
def adjointAux : T.adjointDomain ->ₗ[𝕜] E where
  toFun y := (InnerProductSpace.toDual 𝕜 E).symm (adjointDomainMkCLMExtend T y)
  map_add' x y :=
    hT.eq_of_inner_left 𝕜 fun z zin => by
      simp [InnerProductSpace.toDual_symm_apply, inner_add_left,
        adjointDomainMkCLMExtend_apply hT _ ⟨z, zin⟩, inner_add_left]
  map_smul' _ _ :=
    hT.eq_of_inner_left 𝕜 fun z zin => by
      simp [inner_smul_left, RingHom.id_apply,
        InnerProductSpace.toDual_symm_apply, adjointDomainMkCLMExtend_apply hT _ ⟨z, zin⟩]

/--
theorem `adjointAux_inner` / 定理 `adjointAux_inner`

English:
theorem adjointAux_inner
  given: (y : T.adjointDomain) (x : T.domain)
  proof: by
  simp [adjointAux, hT]

中文:
定理 adjointAux_inner
  条件: (y : T.adjointDomain) (x : T.domain)
  证明: by
  simp [adjointAux, hT]

Depends on / 依赖: adjointAux
-/
theorem adjointAux_inner (y : T.adjointDomain) (x : T.domain) :
    ⟪adjointAux hT y, x⟫ = ⟪(y : F), T x⟫ := by
  simp [adjointAux, hT]

/--
theorem `adjointAux_unique` / 定理 `adjointAux_unique`

English:
theorem adjointAux_unique
  statement: (y : T.adjointDomain) {x₀ : E}
  proof: hT.eq_of_inner_left 𝕜 fun v vin => (adjointAux_inner hT _ _).trans (hx₀ ⟨v, vin⟩).symm

中文:
定理 adjointAux_unique
  结论: (y : T.adjointDomain) {x₀ : E}
  证明: hT.eq_of_inner_left 𝕜 fun v vin => (adjointAux_inner hT _ _).trans (hx₀ ⟨v, vin⟩).symm

Depends on / 依赖: adjointAux_inner, eq_of_inner_left, hT.eq_of_inner_left
-/
theorem adjointAux_unique (y : T.adjointDomain) {x₀ : E}
    (hx₀ : forall x : T.domain, ⟪x₀, x⟫ = ⟪(y : F), T x⟫) : adjointAux hT y = x₀ :=
  hT.eq_of_inner_left 𝕜 fun v vin => (adjointAux_inner hT _ _).trans (hx₀ ⟨v, vin⟩).symm

variable (T)

open scoped Classical in
/--
Definition of `adjoint` / `adjoint` 的定义

English:
definition adjoint
  signature: : F ->ₗ.[𝕜] E where
  body: T.adjointDomain
  toFun := if hT : Dense (T.domain : Set E) then adjointAux hT else 0

@[inherit_doc]
scoped postfix:1024 "†" => LinearPMap.adjoint

中文:
定义 adjoint
  签名: : F ->ₗ.[𝕜] E where
  定义体: T.adjointDomain
  toFun := if hT : Dense (T.domain : Set E) then adjointAux hT else 0

@[inherit_doc]
scoped postfix:1024 "†" => LinearPMap.adjoint

Depends on / 依赖: T.adjointDomain, adjointDomain
-/
def adjoint : F ->ₗ.[𝕜] E where
  domain := T.adjointDomain
  toFun := if hT : Dense (T.domain : Set E) then adjointAux hT else 0

@[inherit_doc]
scoped postfix:1024 "†" => LinearPMap.adjoint

/--
theorem `mem_adjoint_domain_iff` / 定理 `mem_adjoint_domain_iff`

English:
theorem mem_adjoint_domain_iff
  given: (y : F)
  statement: y in T†.domain ↔ Continuous ((innerₛₗ 𝕜 y).comp T.toFun)
  proof: Iff.rfl

中文:
定理 mem_adjoint_domain_iff
  条件: (y : F)
  结论: y in T†.domain ↔ 连续 ((innerₛₗ 𝕜 y).comp T.toFun)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_adjoint_domain_iff (y : F) : y in T†.domain ↔ Continuous ((innerₛₗ 𝕜 y).comp T.toFun) :=
  Iff.rfl

variable {T}

/--
theorem `mem_adjoint_domain_of_exists` / 定理 `mem_adjoint_domain_of_exists`

English:
theorem mem_adjoint_domain_of_exists
  given: (y : F) (h : exists w : E, forall x : T.domain, ⟪w, x⟫ = ⟪y, T x⟫)
  proof: by
  obtain ⟨w, hw⟩ := h
  rw [T.mem_adjoint_domain_iff]
  have : Continuous ((innerSL 𝕜 w).comp T.domain.subtypeL) := by fun_prop
  convert this
  exact funext fun x => (hw x).symm

中文:
定理 mem_adjoint_domain_of_存在
  条件: (y : F) (h : 存在 w : E, 对任意 x : T.domain, ⟪w, x⟫ = ⟪y, T x⟫)
  证明: by
  obtain ⟨w, hw⟩ := h
  rw [T.mem_adjoint_domain_iff]
  have : Continuous ((innerSL 𝕜 w).comp T.domain.subtypeL) := by fun_prop
  convert this
  exact funext fun x => (hw x).symm

Depends on / 依赖: Continuous, T.domain.subtypeL, T.mem_adjoint_domain_iff, convert, domain, fun_prop, innerSL, mem_adjoint_domain_iff, subtypeL
-/
theorem mem_adjoint_domain_of_exists (y : F) (h : exists w : E, forall x : T.domain, ⟪w, x⟫ = ⟪y, T x⟫) :
    y in T†.domain := by
  obtain ⟨w, hw⟩ := h
  rw [T.mem_adjoint_domain_iff]
  have : Continuous ((innerSL 𝕜 w).comp T.domain.subtypeL) := by fun_prop
  convert this
  exact funext fun x => (hw x).symm

set_option backward.isDefEq.respectTransparency false in
/--
theorem `adjoint_apply_of_not_dense` / 定理 `adjoint_apply_of_not_dense`

English:
theorem adjoint_apply_of_not_dense
  given: (hT : ¬Dense (T.domain : Set E)) (y : T†.domain)
  statement: T† y = 0
  proof: by
  classical
  change (if hT : Dense (T.domain : Set E) then adjointAux hT else 0) y = _
  simp only [hT, not_false_iff, dif_neg, LinearMap.zero_apply]

中文:
定理 adjoint_apply_of_not_dense
  条件: (hT : ¬稠密 (T.domain : 集合 E)) (y : T†.domain)
  结论: T† y = 0
  证明: by
  classical
  change (if hT : Dense (T.domain : Set E) then adjointAux hT else 0) y = _
  simp only [hT, not_false_iff, dif_neg, LinearMap.zero_apply]

Depends on / 依赖: LinearMap, LinearMap.zero_apply, T.domain, adjointAux, classical, dif_neg, domain, not_false_iff, zero_apply
-/
theorem adjoint_apply_of_not_dense (hT : ¬Dense (T.domain : Set E)) (y : T†.domain) : T† y = 0 := by
  classical
  change (if hT : Dense (T.domain : Set E) then adjointAux hT else 0) y = _
  simp only [hT, not_false_iff, dif_neg, LinearMap.zero_apply]

/--
theorem `adjoint_apply_of_dense` / 定理 `adjoint_apply_of_dense`

English:
theorem adjoint_apply_of_dense
  given: (y : T†.domain)
  statement: T† y = adjointAux hT y
  proof: by
  classical
  change (if hT : Dense (T.domain : Set E) then adjointAux hT else 0) y = _
  simp only [hT, dif_pos]

include hT in

中文:
定理 adjoint_apply_of_dense
  条件: (y : T†.domain)
  结论: T† y = adjointAux hT y
  证明: by
  classical
  change (if hT : Dense (T.domain : Set E) then adjointAux hT else 0) y = _
  simp only [hT, dif_pos]

include hT in

Depends on / 依赖: T.domain, adjointAux, classical, dif_pos, domain
-/
theorem adjoint_apply_of_dense (y : T†.domain) : T† y = adjointAux hT y := by
  classical
  change (if hT : Dense (T.domain : Set E) then adjointAux hT else 0) y = _
  simp only [hT, dif_pos]

include hT in
/--
theorem `adjoint_apply_eq` / 定理 `adjoint_apply_eq`

English:
theorem adjoint_apply_eq
  given: (y : T†.domain) {x₀ : E} (hx₀ : forall x : T.domain, ⟪x₀, x⟫ = ⟪(y : F), T x⟫)
  proof: (adjoint_apply_of_dense hT y).symm ▸ adjointAux_unique hT _ hx₀

include hT in

中文:
定理 adjoint_apply_eq
  条件: (y : T†.domain) {x₀ : E} (hx₀ : 对任意 x : T.domain, ⟪x₀, x⟫ = ⟪(y : F), T x⟫)
  证明: (adjoint_apply_of_dense hT y).symm ▸ adjointAux_unique hT _ hx₀

include hT in

Depends on / 依赖: adjointAux_unique, adjoint_apply_of_dense
-/
theorem adjoint_apply_eq (y : T†.domain) {x₀ : E} (hx₀ : forall x : T.domain, ⟪x₀, x⟫ = ⟪(y : F), T x⟫) :
    T† y = x₀ :=
  (adjoint_apply_of_dense hT y).symm ▸ adjointAux_unique hT _ hx₀

include hT in
/--
theorem `adjoint_isFormalAdjoint` / 定理 `adjoint_isFormalAdjoint`

English:
theorem adjoint_isFormalAdjoint
  statement: T†.IsFormalAdjoint T
  proof: fun x =>
  (adjoint_apply_of_dense hT x).symm ▸ adjointAux_inner hT x

include hT in

中文:
定理 adjoint_isFormalAdjoint
  结论: T†.IsFormalAdjoint T
  证明: fun x =>
  (adjoint_apply_of_dense hT x).symm ▸ adjointAux_inner hT x

include hT in
-/
theorem adjoint_isFormalAdjoint : T†.IsFormalAdjoint T := fun x =>
  (adjoint_apply_of_dense hT x).symm ▸ adjointAux_inner hT x

include hT in
/--
theorem `IsFormalAdjoint.le_adjoint` / 定理 `IsFormalAdjoint.le_adjoint`

English:
theorem IsFormalAdjoint.le_adjoint
  given: (h : T.IsFormalAdjoint S)
  statement: S <= T†
  proof: ⟨-- Trivially, every `x : S.domain` is in `T.adjoint.domain`
  fun x hx =>
    mem_adjoint_domain_of_exists _
      ⟨S ⟨x, hx⟩, h.symm ⟨x, hx⟩⟩,-- Equality on `S.domain` follows from equality
  -- `⟪v, S x⟫ = ⟪v, T.adjoint y⟫` for all `v : T.domain`:
  fun _ _ hxy => (adjoint_apply_eq hT _ fun _ => 

中文:
定理 IsFormalAdjoint.le_adjoint
  条件: (h : T.IsFormalAdjoint S)
  结论: S <= T†
  证明: ⟨-- Trivially, every `x : S.domain` is in `T.adjoint.domain`
  fun x hx =>
    mem_adjoint_domain_of_exists _
      ⟨S ⟨x, hx⟩, h.symm ⟨x, hx⟩⟩,-- Equality on `S.domain` follows from equality
  -- `⟪v, S x⟫ = ⟪v, T.adjoint y⟫` for all `v : T.domain`:
  fun _ _ hxy => (adjoint_apply_eq hT _ fun _ => 

Depends on / 依赖: Equality, S.domain, T.adjoint.domain, Trivially, adjoint, domain, equality, follows, h.symm, mem_adjoint_domain_of_exists
-/
theorem IsFormalAdjoint.le_adjoint (h : T.IsFormalAdjoint S) : S <= T† :=
  ⟨-- Trivially, every `x : S.domain` is in `T.adjoint.domain`
  fun x hx =>
    mem_adjoint_domain_of_exists _
      ⟨S ⟨x, hx⟩, h.symm ⟨x, hx⟩⟩,-- Equality on `S.domain` follows from equality
  -- `⟪v, S x⟫ = ⟪v, T.adjoint y⟫` for all `v : T.domain`:
  fun _ _ hxy => (adjoint_apply_eq hT _ fun _ => by rw [h.symm, hxy]).symm⟩

end LinearPMap

namespace ContinuousLinearMap

variable [CompleteSpace E] [CompleteSpace F]
variable (A : E ->L[𝕜] F) {p : Submodule 𝕜 E}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `toPMap_adjoint_eq_adjoint_toPMap_of_dense` / 定理 `toPMap_adjoint_eq_adjoint_toPMap_of_dense`

English:
theorem toPMap_adjoint_eq_adjoint_toPMap_of_dense
  given: (hp : Dense (p : Set E))
  proof: by
  ext x y hxy
  · simp only [LinearMap.toPMap_domain, Submodule.mem_top, iff_true,
      LinearPMap.mem_adjoint_domain_iff]
    exact ((innerSL 𝕜 x).comp <| A.comp <| Submodule.subtypeL _).cont
  refine LinearPMap.adjoint_apply_eq hp _ fun v => ?_
  simp only [adjoint_inner_left, LinearMap.toPMap

中文:
定理 toPMap_adjoint_eq_adjoint_toPMap_of_dense
  条件: (hp : 稠密 (p : 集合 E))
  证明: by
  ext x y hxy
  · simp only [LinearMap.toPMap_domain, Submodule.mem_top, iff_true,
      LinearPMap.mem_adjoint_domain_iff]
    exact ((innerSL 𝕜 x).comp <| A.comp <| Submodule.subtypeL _).cont
  refine LinearPMap.adjoint_apply_eq hp _ fun v => ?_
  simp only [adjoint_inner_left, LinearMap.toPMap

Depends on / 依赖: A.comp, LinearMap, LinearMap.toPMap_apply, LinearMap.toPMap_domain, LinearPMap, LinearPMap.adjoint_apply_eq, LinearPMap.mem_adjoint_domain_iff, Submodule, Submodule.mem_top, Submodule.subtypeL, adjoint_apply_eq, adjoint_inner_left, coe_coe, iff_true, innerSL, mem_adjoint_domain_iff, mem_top, subtypeL, toPMap_apply, toPMap_domain
-/
theorem toPMap_adjoint_eq_adjoint_toPMap_of_dense (hp : Dense (p : Set E)) :
    (A.toPMap p).adjoint = A.adjoint.toPMap ⊤ := by
  ext x y hxy
  · simp only [LinearMap.toPMap_domain, Submodule.mem_top, iff_true,
      LinearPMap.mem_adjoint_domain_iff]
    exact ((innerSL 𝕜 x).comp <| A.comp <| Submodule.subtypeL _).cont
  refine LinearPMap.adjoint_apply_eq hp _ fun v => ?_
  simp only [adjoint_inner_left, LinearMap.toPMap_apply, coe_coe]

end ContinuousLinearMap

section Star

namespace LinearPMap

variable [CompleteSpace E]

/--
Instance `instStar` / 实例 `instStar`

English:
instance instStar
  signature: : Star (E ->ₗ.[𝕜] E) where
  body: fun A => A.adjoint

中文:
实例 instStar
  签名: : 对合 (E ->ₗ.[𝕜] E) where
  定义体: fun A => A.adjoint

Depends on / 依赖: A.adjoint, adjoint
-/
instance instStar : Star (E ->ₗ.[𝕜] E) where
  star := fun A => A.adjoint

variable {A : E ->ₗ.[𝕜] E}

/--
theorem `isSelfAdjoint_def` / 定理 `isSelfAdjoint_def`

English:
theorem isSelfAdjoint_def
  statement: IsSelfAdjoint A ↔ A† = A
  proof: Iff.rfl

中文:
定理 isSelfAdjoint_def
  结论: IsSelfAdjoint A ↔ A† = A
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isSelfAdjoint_def : IsSelfAdjoint A ↔ A† = A := Iff.rfl

/--
theorem `_root_.IsSelfAdjoint.dense_domain` / 定理 `_root_.IsSelfAdjoint.dense_domain`

English:
theorem _root_.IsSelfAdjoint.dense_domain
  given: (hA : IsSelfAdjoint A)
  statement: Dense (A.domain : Set E)
  proof: by
  by_contra h
  rw [isSelfAdjoint_def] at hA
  have h' : A.domain = ⊤ := by
    rw [← hA]; rw [Submodule.eq_top_iff']
    intro x
    rw [mem_adjoint_domain_iff]; rw [← hA]
    refine (innerSL 𝕜 x).cont.comp ?_
    simp only [adjoint, h]
    exact continuous_const
  simp [h'] at h

中文:
定理 _root_.IsSelfAdjoint.dense_domain
  条件: (hA : IsSelfAdjoint A)
  结论: 稠密 (A.domain : 集合 E)
  证明: by
  by_contra h
  rw [isSelfAdjoint_def] at hA
  have h' : A.domain = ⊤ := by
    rw [← hA]; rw [Submodule.eq_top_iff']
    intro x
    rw [mem_adjoint_domain_iff]; rw [← hA]
    refine (innerSL 𝕜 x).cont.comp ?_
    simp only [adjoint, h]
    exact continuous_const
  simp [h'] at h

Depends on / 依赖: A.domain, Submodule, Submodule.eq_top_iff, adjoint, cont.comp, continuous_const, domain, eq_top_iff, innerSL, isSelfAdjoint_def, mem_adjoint_domain_iff
-/
theorem _root_.IsSelfAdjoint.dense_domain (hA : IsSelfAdjoint A) : Dense (A.domain : Set E) := by
  by_contra h
  rw [isSelfAdjoint_def] at hA
  have h' : A.domain = ⊤ := by
    rw [← hA]; rw [Submodule.eq_top_iff']
    intro x
    rw [mem_adjoint_domain_iff]; rw [← hA]
    refine (innerSL 𝕜 x).cont.comp ?_
    simp only [adjoint, h]
    exact continuous_const
  simp [h'] at h

end LinearPMap

end Star

/-! ### The graph of the adjoint -/

namespace Submodule

/-- The adjoint of a submodule

Note that the adjoint is taken with respect to the L^2 inner product on `E × F`, which is defined
as `WithLp 2 (E × F)`. -/
protected noncomputable
/--
Definition of `adjoint` / `adjoint` 的定义

English:
definition adjoint
  signature: (g : Submodule 𝕜 (E × F))
  body: (g.map ((LinearEquiv.skewSwap 𝕜 F E).symm.trans
    (WithLp.linearEquiv 2 𝕜 (F × E)).symm).toLinearMap).orthogonal.map
      (WithLp.linearEquiv 2 𝕜 (F × E) : WithLp 2 (F × E) ->ₗ[𝕜] F × E)

@[simp]

中文:
定义 adjoint
  签名: (g : 子模 𝕜 (E × F))
  定义体: (g.map ((LinearEquiv.skewSwap 𝕜 F E).symm.trans
    (WithLp.linearEquiv 2 𝕜 (F × E)).symm).toLinearMap).orthogonal.map
      (WithLp.linearEquiv 2 𝕜 (F × E) : WithLp 2 (F × E) ->ₗ[𝕜] F × E)

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.skewSwap, WithLp, WithLp.linearEquiv, g.map, linearEquiv, orthogonal, orthogonal.map, skewSwap, symm.trans, toLinearMap
-/
def adjoint (g : Submodule 𝕜 (E × F)) : Submodule 𝕜 (F × E) :=
  (g.map ((LinearEquiv.skewSwap 𝕜 F E).symm.trans
    (WithLp.linearEquiv 2 𝕜 (F × E)).symm).toLinearMap).orthogonal.map
      (WithLp.linearEquiv 2 𝕜 (F × E) : WithLp 2 (F × E) ->ₗ[𝕜] F × E)

@[simp]
/--
theorem `mem_adjoint_iff` / 定理 `mem_adjoint_iff`

English:
theorem mem_adjoint_iff
  given: (g : Submodule 𝕜 (E × F)) (x : F × E)
  proof: by
  simp only [Submodule.adjoint, mem_map, mem_orthogonal, LinearEquiv.coe_coe,
    LinearEquiv.trans_apply, LinearEquiv.skewSwap_symm_apply, coe_symm_linearEquiv, Prod.exists,
    prod_inner_apply, ofLp_fst, ofLp_snd, forall_exists_index, and_imp, coe_linearEquiv]
  constructor
  · rintro ⟨y, h1, 

中文:
定理 mem_adjoint_iff
  条件: (g : 子模 𝕜 (E × F)) (x : F × E)
  证明: by
  simp only [Submodule.adjoint, mem_map, mem_orthogonal, LinearEquiv.coe_coe,
    LinearEquiv.trans_apply, LinearEquiv.skewSwap_symm_apply, coe_symm_linearEquiv, Prod.exists,
    prod_inner_apply, ofLp_fst, ofLp_snd, forall_exists_index, and_imp, coe_linearEquiv]
  constructor
  · rintro ⟨y, h1, 

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_coe, LinearEquiv.skewSwap_symm_apply, LinearEquiv.trans_apply, Prod.exists, Submodule, Submodule.adjoint, WithLp, WithLp.ofLp_fst, WithLp.ofLp_snd, adjoint, and_imp, coe_coe, coe_linearEquiv, coe_symm_linearEquiv, forall_exists_index, inner_neg_left, mem_map, mem_orthogonal, ofLp_fst
-/
theorem mem_adjoint_iff (g : Submodule 𝕜 (E × F)) (x : F × E) :
    x in g.adjoint ↔
    forall a b, (a, b) in g -> inner 𝕜 b x.fst - inner 𝕜 a x.snd = 0 := by
  simp only [Submodule.adjoint, mem_map, mem_orthogonal, LinearEquiv.coe_coe,
    LinearEquiv.trans_apply, LinearEquiv.skewSwap_symm_apply, coe_symm_linearEquiv, Prod.exists,
    prod_inner_apply, ofLp_fst, ofLp_snd, forall_exists_index, and_imp, coe_linearEquiv]
  constructor
  · rintro ⟨y, h1, h2⟩ a b hab
    rw [← h2]; rw [WithLp.ofLp_fst]; rw [WithLp.ofLp_snd]
    specialize h1 (toLp 2 (b, -a)) a b hab rfl
    dsimp at h1
    simp only [inner_neg_left, ← sub_eq_add_neg] at h1
    exact h1
  · intro h
    refine ⟨toLp 2 x, ?_, rfl⟩
    intro u a b hab hu
    simp [← hu, ← sub_eq_add_neg, h a b hab]

variable {T : E ->ₗ.[𝕜] F} [CompleteSpace E]

/--
theorem `_root_.LinearPMap.adjoint_graph_eq_graph_adjoint` / 定理 `_root_.LinearPMap.adjoint_graph_eq_graph_adjoint`

English:
theorem _root_.LinearPMap.adjoint_graph_eq_graph_adjoint
  given: (hT : Dense (T.domain : Set E))
  proof: by
  ext x
  simp only [mem_graph_iff, Subtype.exists, exists_and_left, exists_eq_left, mem_adjoint_iff,
    forall_exists_index, forall_apply_eq_imp_iff]
  constructor
  · rintro ⟨hx, h⟩ a ha
    rw [← h]; rw [(adjoint_isFormalAdjoint hT).symm ⟨a]; rw [ha⟩ ⟨x.fst]; rw [hx⟩]; rw [sub_self]
  · intro

中文:
定理 _root_.LinearP映射.adjoint_graph_eq_graph_adjoint
  条件: (hT : 稠密 (T.domain : 集合 E))
  证明: by
  ext x
  simp only [mem_graph_iff, Subtype.exists, exists_and_left, exists_eq_left, mem_adjoint_iff,
    forall_exists_index, forall_apply_eq_imp_iff]
  constructor
  · rintro ⟨hx, h⟩ a ha
    rw [← h]; rw [(adjoint_isFormalAdjoint hT).symm ⟨a]; rw [ha⟩ ⟨x.fst]; rw [hx⟩]; rw [sub_self]
  · intro

Depends on / 依赖: Subtype, Subtype.exists, adjoint_isFormalAdjoint, domain, eq_of_inner_right, exists_and_left, exists_eq_left, forall_apply_eq_imp_iff, forall_exists_index, hT.eq_of_inner_right, inner_conj_symm, mem_adjoint_domain_of_exists, mem_adjoint_iff, mem_graph_iff, simp_rw, sub_eq_zero, sub_self, x.fst, x.snd
-/
theorem _root_.LinearPMap.adjoint_graph_eq_graph_adjoint (hT : Dense (T.domain : Set E)) :
    T†.graph = T.graph.adjoint := by
  ext x
  simp only [mem_graph_iff, Subtype.exists, exists_and_left, exists_eq_left, mem_adjoint_iff,
    forall_exists_index, forall_apply_eq_imp_iff]
  constructor
  · rintro ⟨hx, h⟩ a ha
    rw [← h]; rw [(adjoint_isFormalAdjoint hT).symm ⟨a]; rw [ha⟩ ⟨x.fst]; rw [hx⟩]; rw [sub_self]
  · intro h
    simp_rw [sub_eq_zero] at h
    have hx : x.fst in T†.domain := by
      apply mem_adjoint_domain_of_exists
      use x.snd
      rintro ⟨a, ha⟩
      rw [← inner_conj_symm]; rw [← h a ha]; rw [inner_conj_symm]
    use hx
    apply hT.eq_of_inner_right 𝕜
    rintro a ha
    rw [← h a ha]; rw [(adjoint_isFormalAdjoint hT).symm ⟨a]; rw [ha⟩ ⟨x.fst]; rw [hx⟩]

@[simp]
/--
theorem `_root_.LinearPMap.graph_adjoint_toLinearPMap_eq_adjoint` / 定理 `_root_.LinearPMap.graph_adjoint_toLinearPMap_eq_adjoint`

English:
theorem _root_.LinearPMap.graph_adjoint_toLinearPMap_eq_adjoint
  given: (hT : Dense (T.domain : Set E))
  proof: by
  apply eq_of_eq_graph
  rw [adjoint_graph_eq_graph_adjoint hT]
  apply Submodule.toLinearPMap_graph_eq
  intro x hx hx'
  simp only [mem_adjoint_iff, mem_graph_iff, Subtype.exists, exists_and_left, exists_eq_left, hx',
    inner_zero_right, zero_sub, neg_eq_zero, forall_exists_index, forall_appl

中文:
定理 _root_.LinearP映射.graph_adjoint_toLinearPMap_eq_adjoint
  条件: (hT : 稠密 (T.domain : 集合 E))
  证明: by
  apply eq_of_eq_graph
  rw [adjoint_graph_eq_graph_adjoint hT]
  apply Submodule.toLinearPMap_graph_eq
  intro x hx hx'
  simp only [mem_adjoint_iff, mem_graph_iff, Subtype.exists, exists_and_left, exists_eq_left, hx',
    inner_zero_right, zero_sub, neg_eq_zero, forall_exists_index, forall_appl

Depends on / 依赖: Submodule, Submodule.toLinearPMap_graph_eq, Subtype, Subtype.exists, adjoint_graph_eq_graph_adjoint, eq_of_eq_graph, eq_zero_of_inner_right, exists_and_left, exists_eq_left, forall_apply_eq_imp_iff, forall_exists_index, hT.eq_zero_of_inner_right, inner_zero_right, mem_adjoint_iff, mem_graph_iff, neg_eq_zero, toLinearPMap_graph_eq, zero_sub
-/
theorem _root_.LinearPMap.graph_adjoint_toLinearPMap_eq_adjoint (hT : Dense (T.domain : Set E)) :
    T.graph.adjoint.toLinearPMap = T† := by
  apply eq_of_eq_graph
  rw [adjoint_graph_eq_graph_adjoint hT]
  apply Submodule.toLinearPMap_graph_eq
  intro x hx hx'
  simp only [mem_adjoint_iff, mem_graph_iff, Subtype.exists, exists_and_left, exists_eq_left, hx',
    inner_zero_right, zero_sub, neg_eq_zero, forall_exists_index, forall_apply_eq_imp_iff] at hx
  apply hT.eq_zero_of_inner_right 𝕜
  exact fun a ha => hx a ha

end Submodule

/-! ### Closedness -/

namespace LinearPMap

variable {T : E ->ₗ.[𝕜] F} [CompleteSpace E]

/--
theorem `adjoint_isClosed` / 定理 `adjoint_isClosed`

English:
theorem adjoint_isClosed
  given: (hT : Dense (T.domain : Set E))
  proof: by
  rw [IsClosed]; rw [adjoint_graph_eq_graph_adjoint hT]; rw [Submodule.adjoint]
  simp only [Submodule.map_coe]
  rw [LinearEquiv.coe_coe]; rw [LinearEquiv.image_eq_preimage_symm]
  exact (Submodule.isClosed_orthogonal _).preimage (WithLp.prod_continuous_toLp _ _ _)

中文:
定理 adjoint_isClosed
  条件: (hT : 稠密 (T.domain : 集合 E))
  证明: by
  rw [IsClosed]; rw [adjoint_graph_eq_graph_adjoint hT]; rw [Submodule.adjoint]
  simp only [Submodule.map_coe]
  rw [LinearEquiv.coe_coe]; rw [LinearEquiv.image_eq_preimage_symm]
  exact (Submodule.isClosed_orthogonal _).preimage (WithLp.prod_continuous_toLp _ _ _)

Depends on / 依赖: IsClosed, LinearEquiv, LinearEquiv.coe_coe, LinearEquiv.image_eq_preimage_symm, Submodule, Submodule.adjoint, Submodule.isClosed_orthogonal, Submodule.map_coe, WithLp, WithLp.prod_continuous_toLp, adjoint, adjoint_graph_eq_graph_adjoint, coe_coe, image_eq_preimage_symm, isClosed_orthogonal, map_coe, preimage, prod_continuous_toLp
-/
theorem adjoint_isClosed (hT : Dense (T.domain : Set E)) :
    T†.IsClosed := by
  rw [IsClosed]; rw [adjoint_graph_eq_graph_adjoint hT]; rw [Submodule.adjoint]
  simp only [Submodule.map_coe]
  rw [LinearEquiv.coe_coe]; rw [LinearEquiv.image_eq_preimage_symm]
  exact (Submodule.isClosed_orthogonal _).preimage (WithLp.prod_continuous_toLp _ _ _)

/--
theorem `_root_.IsSelfAdjoint.isClosed` / 定理 `_root_.IsSelfAdjoint.isClosed`

English:
theorem _root_.IsSelfAdjoint.isClosed
  given: {A : E ->ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
  statement: A.IsClosed
  proof: by
  rw [← isSelfAdjoint_def.mp hA]
  exact adjoint_isClosed hA.dense_domain

中文:
定理 _root_.IsSelfAdjoint.isClosed
  条件: {A : E ->ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
  结论: A.是闭集
  证明: by
  rw [← isSelfAdjoint_def.mp hA]
  exact adjoint_isClosed hA.dense_domain

Depends on / 依赖: adjoint_isClosed, dense_domain, hA.dense_domain, isSelfAdjoint_def, isSelfAdjoint_def.mp
-/
theorem _root_.IsSelfAdjoint.isClosed {A : E ->ₗ.[𝕜] E} (hA : IsSelfAdjoint A) : A.IsClosed := by
  rw [← isSelfAdjoint_def.mp hA]
  exact adjoint_isClosed hA.dense_domain

end LinearPMap
