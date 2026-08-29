/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
-/
module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.MonoidAlgebra.Lift
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Finsupp.Supported

import Mathlib.LinearAlgebra.Span.Basic

/-!
# Module structure on monoid algebras

## Main results

* `MonoidAlgebra.module`, `AddMonoidAlgebra.module`: lift a module structure to monoid algebras

## Implementation notes

We do not state the equivalent of `DistribMulAction M (MonoidAlgebra S M)` for `AddMonoidAlgebra`
because mathlib does not have the notion of distributive actions of additive groups.
-/

@[expose] public section

assert_not_exists NonUnitalAlgHom AlgEquiv

noncomputable section

open Finsupp hiding single
open Module

variable {R S M N O G : Type*}

/-! ### Multiplicative monoids -/

namespace MonoidAlgebra

section SMul

section DistribMulAction
variable [Monoid S] [Semiring R] [DistribMulAction S R]

@[to_additive (dont_translate := S) distribMulAction]
/--
Instance `distribMulAction` / 实例 `distribMulAction`

English:
instance distribMulAction
  signature: : DistribMulAction S R[M]
  body: fast_instance% coeffEquiv.distribMulAction _

@[to_additive (dont_translate := S) (attr := simp)]

中文:
实例 distribMulAction
  签名: : DistribMulAction S R[M]
  定义体: fast_instance% coeffEquiv.distribMulAction _

@[to_additive (dont_translate := S) (attr := simp)]

Depends on / 依赖: coeffEquiv, coeffEquiv.distribMulAction, distribMulAction, fast_instance
-/
instance distribMulAction : DistribMulAction S R[M] := fast_instance% coeffEquiv.distribMulAction _

@[to_additive (dont_translate := S) (attr := simp)]
/--
lemma `mapDomain_smul` / 引理 `mapDomain_smul`

English:
lemma mapDomain_smul
  given: (f : M -> N) (s : S) (x : R[M])
  statement: mapDomain f (s • x) = s • mapDomain f x
  proof: by
  ext; simp [Finsupp.mapDomain_smul]

中文:
引理 mapDomain_smul
  条件: (f : M -> N) (s : S) (x : R[M])
  结论: mapDomain f (s • x) = s • mapDomain f x
  证明: by
  ext; simp [Finsupp.mapDomain_smul]

Depends on / 依赖: Finsupp, Finsupp.mapDomain_smul, mapDomain_smul
-/
lemma mapDomain_smul (f : M -> N) (s : S) (x : R[M]) : mapDomain f (s • x) = s • mapDomain f x := by
  ext; simp [Finsupp.mapDomain_smul]

end DistribMulAction

section Module
variable [Semiring R] [Semiring S] [Module R S] {s t : Set M} {x : S[M]}

@[to_additive (dont_translate := R)]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module R S[M]
  body: fast_instance% coeffEquiv.module _

@[to_additive]

中文:
实例 :
  签名: Module R S[M]
  定义体: fast_instance% coeffEquiv.module _

@[to_additive]

Depends on / 依赖: coeffEquiv, coeffEquiv.module, fast_instance, module
-/
instance : Module R S[M] := fast_instance% coeffEquiv.module _

@[to_additive]
/--
Instance `instIsTorsionFree` / 实例 `instIsTorsionFree`

English:
instance instIsTorsionFree
  signature: [IsTorsionFree R S]
  body: coeffEquiv.moduleIsTorsionFree _

中文:
实例 instIsTorsionFree
  签名: [IsTorsionFree R S]
  定义体: coeffEquiv.moduleIsTorsionFree _

Depends on / 依赖: coeffEquiv, coeffEquiv.moduleIsTorsionFree, moduleIsTorsionFree
-/
instance instIsTorsionFree [IsTorsionFree R S] : IsTorsionFree R S[M] :=
  coeffEquiv.moduleIsTorsionFree _

variable (R) in
/-- `MonoidAlgebra.coeff` as a linear equiv. -/
@[to_additive (attr := simps! apply symm_apply)
/-- `MonoidAlgebra.coeff` as a linear equiv. -/]
/--
Definition of `coeffLinearEquiv` / `coeffLinearEquiv` 的定义

English:
definition coeffLinearEquiv
  signature: : S[M] ≃ₗ[R] M ->₀ S
  body: coeffEquiv.linearEquiv _

中文:
定义 coeffLinearEquiv
  签名: : S[M] ≃ₗ[R] M ->₀ S
  定义体: coeffEquiv.linearEquiv _

Depends on / 依赖: coeffEquiv, coeffEquiv.linearEquiv, linearEquiv
-/
def coeffLinearEquiv : S[M] ≃ₗ[R] M ->₀ S := coeffEquiv.linearEquiv _

variable (R S) in
/-- `MonoidAlgebra.mapDomain` as a linear map. -/
@[to_additive /-- `AddMonoidAlgebra.mapDomain` as a linear map. -/]
/--
Definition of `mapDomainLinearMap` / `mapDomainLinearMap` 的定义

English:
definition mapDomainLinearMap
  signature: (f : M -> N)
  body: (coeffLinearEquiv _).symm.toLinearMap ∘ₗ Finsupp.lmapDomain _ _ f ∘ₗ
    (coeffLinearEquiv _).toLinearMap

@[to_additive (attr := simp)]

中文:
定义 mapDomainLinearMap
  签名: (f : M -> N)
  定义体: (coeffLinearEquiv _).symm.toLinearMap ∘ₗ Finsupp.lmapDomain _ _ f ∘ₗ
    (coeffLinearEquiv _).toLinearMap

@[to_additive (attr := simp)]

Depends on / 依赖: Finsupp, Finsupp.lmapDomain, coeffLinearEquiv, lmapDomain, symm.toLinearMap, toLinearMap
-/
def mapDomainLinearMap (f : M -> N) : S[M] ->ₗ[R] S[N] :=
  (coeffLinearEquiv _).symm.toLinearMap ∘ₗ Finsupp.lmapDomain _ _ f ∘ₗ
    (coeffLinearEquiv _).toLinearMap

@[to_additive (attr := simp)]
/--
lemma `coeff_mapDomainLinearMap` / 引理 `coeff_mapDomainLinearMap`

English:
lemma coeff_mapDomainLinearMap
  given: (f : M -> N) (x : S[M])
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 coeff_mapDomainLinearMap
  条件: (f : M -> N) (x : S[M])
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma coeff_mapDomainLinearMap (f : M -> N) (x : S[M]) :
    (mapDomainLinearMap R S f x).coeff = x.coeff.mapDomain f := rfl

@[to_additive (attr := simp)]
/--
lemma `mapDomainLinearMap_single` / 引理 `mapDomainLinearMap_single`

English:
lemma mapDomainLinearMap_single
  given: (f : M -> N) (s : S) (m : M)
  proof: by simp [mapDomainLinearMap]

@[to_additive (attr := simp)]

中文:
引理 mapDomainLinearMap_single
  条件: (f : M -> N) (s : S) (m : M)
  证明: by simp [mapDomainLinearMap]

@[to_additive (attr := simp)]

Depends on / 依赖: mapDomainLinearMap
-/
lemma mapDomainLinearMap_single (f : M -> N) (s : S) (m : M) :
    mapDomainLinearMap R S f (single m s) = single (f m) s := by simp [mapDomainLinearMap]

@[to_additive (attr := simp)]
/--
lemma `mapDomainLinearMap_comp` / 引理 `mapDomainLinearMap_comp`

English:
lemma mapDomainLinearMap_comp
  given: (f : M -> N) (g : N -> O)
  proof: by
  ext; simp [Finsupp.mapDomain_comp]

中文:
引理 mapDomainLinearMap_comp
  条件: (f : M -> N) (g : N -> O)
  证明: by
  ext; simp [Finsupp.mapDomain_comp]

Depends on / 依赖: Finsupp, Finsupp.mapDomain_comp, mapDomain_comp
-/
lemma mapDomainLinearMap_comp (f : M -> N) (g : N -> O) :
    mapDomainLinearMap R S (g ∘ f) = mapDomainLinearMap R S g ∘ₗ mapDomainLinearMap R S f := by
  ext; simp [Finsupp.mapDomain_comp]

variable (R S) in
/-- `MonoidAlgebra.mapDomain` as a linear equiv. -/
@[to_additive /-- `AddMonoidAlgebra.mapDomain` as a linear equiv. -/]
/--
Definition of `mapDomainLinearEquiv` / `mapDomainLinearEquiv` 的定义

English:
definition mapDomainLinearEquiv
  signature: (e : M ≃ N)
  body: (coeffLinearEquiv _).trans (Finsupp.domLCongr e).trans (coeffLinearEquiv _).symm

@[to_additive (attr := simp)]

中文:
定义 mapDomainLinearEquiv
  签名: (e : M ≃ N)
  定义体: (coeffLinearEquiv _).trans (Finsupp.domLCongr e).trans (coeffLinearEquiv _).symm

@[to_additive (attr := simp)]

Depends on / 依赖: Finsupp, Finsupp.domLCongr, coeffLinearEquiv, domLCongr
-/
def mapDomainLinearEquiv (e : M ≃ N) : S[M] ≃ₗ[R] S[N] :=
(coeffLinearEquiv _).trans (Finsupp.domLCongr e).trans (coeffLinearEquiv _).symm

@[to_additive (attr := simp)]
/--
lemma `coeff_mapDomainLinearEquiv` / 引理 `coeff_mapDomainLinearEquiv`

English:
lemma coeff_mapDomainLinearEquiv
  given: (e : M ≃ N) (x : S[M])
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 coeff_mapDomainLinearEquiv
  条件: (e : M ≃ N) (x : S[M])
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma coeff_mapDomainLinearEquiv (e : M ≃ N) (x : S[M]) :
    (mapDomainLinearEquiv R S e x).coeff = equivMapDomain e x.coeff := rfl

@[to_additive (attr := simp)]
/--
lemma `mapDomainLinearEquiv_single` / 引理 `mapDomainLinearEquiv_single`

English:
lemma mapDomainLinearEquiv_single
  given: (e : M ≃ N) (s : S) (m : M)
  proof: by simp [mapDomainLinearEquiv]

@[to_additive (attr := simp)]

中文:
引理 mapDomainLinearEquiv_single
  条件: (e : M ≃ N) (s : S) (m : M)
  证明: by simp [mapDomainLinearEquiv]

@[to_additive (attr := simp)]

Depends on / 依赖: mapDomainLinearEquiv
-/
lemma mapDomainLinearEquiv_single (e : M ≃ N) (s : S) (m : M) :
    mapDomainLinearEquiv R S e (single m s) = single (e m) s := by simp [mapDomainLinearEquiv]

@[to_additive (attr := simp)]
/--
lemma `symm_mapDomainLinearEquiv` / 引理 `symm_mapDomainLinearEquiv`

English:
lemma symm_mapDomainLinearEquiv
  given: (e : M ≃ N)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 symm_mapDomainLinearEquiv
  条件: (e : M ≃ N)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma symm_mapDomainLinearEquiv (e : M ≃ N) :
    (mapDomainLinearEquiv R S e).symm = mapDomainLinearEquiv R S e.symm := rfl

@[to_additive (attr := simp)]
/--
lemma `mapDomainLinearEquiv_trans` / 引理 `mapDomainLinearEquiv_trans`

English:
lemma mapDomainLinearEquiv_trans
  given: (e₁ : M ≃ N) (e₂ : N ≃ O)
  proof: by ext; simp

中文:
引理 mapDomainLinearEquiv_trans
  条件: (e₁ : M ≃ N) (e₂ : N ≃ O)
  证明: by ext; simp
-/
lemma mapDomainLinearEquiv_trans (e₁ : M ≃ N) (e₂ : N ≃ O) :
    mapDomainLinearEquiv R S (e₁.trans e₂) =
      (mapDomainLinearEquiv R S e₁).trans (mapDomainLinearEquiv R S e₂) := by ext; simp

variable (R M) in
/-- The trivial monoid algebra is the base ring. -/
@[to_additive (dont_translate := R)
/-- The trivial monoid algebra is the base ring. -/]
/--
Definition of `uniqueLinearEquiv` / `uniqueLinearEquiv` 的定义

English:
definition uniqueLinearEquiv
  signature: [One M] [Subsingleton M]
  body: coeffAddEquiv.trans Finsupp.uniqueAddEquiv 1
  map_smul' r x := by simp

中文:
定义 uniqueLinearEquiv
  签名: [One M] [Subsingleton M]
  定义体: coeffAddEquiv.trans Finsupp.uniqueAddEquiv 1
  map_smul' r x := by simp

Depends on / 依赖: Finsupp, Finsupp.uniqueAddEquiv, coeffAddEquiv, coeffAddEquiv.trans, uniqueAddEquiv
-/
def uniqueLinearEquiv [One M] [Subsingleton M] : S[M] ≃ₗ[R] S where
toAddEquiv := coeffAddEquiv.trans Finsupp.uniqueAddEquiv 1
  map_smul' r x := by simp

variable (R) in
@[to_additive (attr := simp)]
/--
lemma `uniqueLinearEquiv_apply` / 引理 `uniqueLinearEquiv_apply`

English:
lemma uniqueLinearEquiv_apply
  given: [One M] [Subsingleton M] (x : S[M])
  proof: rfl

中文:
引理 uniqueLinearEquiv_apply
  条件: [One M] [Subsingleton M] (x : S[M])
  证明: rfl
-/
lemma uniqueLinearEquiv_apply [One M] [Subsingleton M] (x : S[M]) :
    uniqueLinearEquiv R M x = x.coeff 1 := rfl

variable (R M) in
@[to_additive (attr := simp)]
/--
lemma `uniqueLinearEquiv_symm_apply` / 引理 `uniqueLinearEquiv_symm_apply`

English:
lemma uniqueLinearEquiv_symm_apply
  given: [One M] [Subsingleton M] (s : S)
  proof: rfl

中文:
引理 uniqueLinearEquiv_symm_apply
  条件: [One M] [Subsingleton M] (s : S)
  证明: rfl
-/
lemma uniqueLinearEquiv_symm_apply [One M] [Subsingleton M] (s : S) :
    (uniqueLinearEquiv R M).symm s = .single 1 s := rfl

variable (R S s) in
/-- The `R`-submodule of all elements of `S[M]` supported on a subset `s` of `M`. -/
@[to_additive
/-- The `R`-submodule of all elements of `S[M]` supported on a subset `s` of `M`. -/]
/--
Definition of `supported` / `supported` 的定义

English:
definition supported
  signature: : Submodule R S[M]
  body: (Finsupp.supported S R s).comap (coeffLinearEquiv R).toLinearMap

中文:
定义 supported
  签名: : Submodule R S[M]
  定义体: (Finsupp.supported S R s).comap (coeffLinearEquiv R).toLinearMap

Depends on / 依赖: Finsupp, Finsupp.supported, coeffLinearEquiv, supported, toLinearMap
-/
def supported : Submodule R S[M] := (Finsupp.supported S R s).comap (coeffLinearEquiv R).toLinearMap

/--
lemma `mem_supported` / 引理 `mem_supported`

English:
lemma mem_supported
  statement: x in supported R S s ↔ ↑x.coeff.support subseteq s
  proof: .rfl

@[to_additive]

中文:
引理 mem_supported
  结论: x in supported R S s ↔ ↑x.coeff.support subseteq s
  证明: .rfl

@[to_additive]
-/
@[to_additive] lemma mem_supported : x in supported R S s ↔ ↑x.coeff.support subseteq s := .rfl

@[to_additive]
/--
lemma `mem_supported'` / 引理 `mem_supported'`

English:
lemma mem_supported'
  statement: x in supported R S s ↔ forall m ∉ s, x.coeff m = 0
  proof: by
  simp [mem_supported, Set.subset_def, not_imp_comm]

中文:
引理 mem_supported'
  结论: x in supported R S s ↔ 对任意 m ∉ s, x.coeff m = 0
  证明: by
  simp [mem_supported, Set.subset_def, not_imp_comm]

Depends on / 依赖: Set.subset_def, mem_supported, not_imp_comm, subset_def
-/
lemma mem_supported' : x in supported R S s ↔ forall m ∉ s, x.coeff m = 0 := by
  simp [mem_supported, Set.subset_def, not_imp_comm]

variable (R S s) in
@[to_additive]
/--
lemma `supported_eq_map` / 引理 `supported_eq_map`

English:
lemma supported_eq_map
  proof: Submodule.comap_equiv_eq_map_symm ..

中文:
引理 supported_eq_map
  证明: Submodule.comap_equiv_eq_map_symm ..

Depends on / 依赖: Submodule, Submodule.comap_equiv_eq_map_symm, comap_equiv_eq_map_symm
-/
lemma supported_eq_map :
    supported R S s = (Finsupp.supported S R s).map (coeffLinearEquiv R).symm.toLinearMap :=
  Submodule.comap_equiv_eq_map_symm ..

set_option backward.isDefEq.respectTransparency false in
variable (R S s) in
@[to_additive (dont_translate := R)]
/--
lemma `supported_eq_span_single` / 引理 `supported_eq_span_single`

English:
lemma supported_eq_span_single
  statement: supported R R s = .span R ((fun m => single m 1) '' s)
  proof: by
  simp [supported_eq_map, Finsupp.supported_eq_span_single R s, Submodule.map_span,
    ← Set.image_comp]

@[to_additive (attr := gcongr)]

中文:
引理 supported_eq_span_single
  结论: supported R R s = .span R ((fun m => single m 1) '' s)
  证明: by
  simp [supported_eq_map, Finsupp.supported_eq_span_single R s, Submodule.map_span,
    ← Set.image_comp]

@[to_additive (attr := gcongr)]

Depends on / 依赖: Finsupp, Finsupp.supported_eq_span_single, Set.image_comp, Submodule, Submodule.map_span, image_comp, map_span, supported_eq_map, supported_eq_span_single
-/
lemma supported_eq_span_single : supported R R s = .span R ((fun m => single m 1) '' s) := by
  simp [supported_eq_map, Finsupp.supported_eq_span_single R s, Submodule.map_span,
    ← Set.image_comp]

@[to_additive (attr := gcongr)]
/--
lemma `supported_mono` / 引理 `supported_mono`

English:
lemma supported_mono
  given: (hst : s subseteq t)
  statement: supported R S s <= supported R S t
  proof: fun _ h => h.trans hst

#adaptation_note

中文:
引理 supported_mono
  条件: (hst : s subseteq t)
  结论: supported R S s <= supported R S t
  证明: fun _ h => h.trans hst

#adaptation_note

Depends on / 依赖: h.trans
-/
lemma supported_mono (hst : s subseteq t) : supported R S s <= supported R S t := fun _ h => h.trans hst

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Interpret `Finsupp.restrictSupportEquiv` as a linear equivalence between
`supported M R s` and `s →₀ M`. -/
@[to_additive (dont_translate := R) (attr := simps!)
/-- Interpret `Finsupp.restrictSupportEquiv` as a linear equivalence between
`supported M R s` and `s →₀ M`. -/]
/--
Definition of `supportedEquivFinsupp` / `supportedEquivFinsupp` 的定义

English:
definition supportedEquivFinsupp
  signature: (s : Set M)
  body: { toFun x := ⟨x.1.coeff, x.2⟩
    invFun x := ⟨.ofCoeff x.1, x.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
   ≪≫ₗ Finsupp.supportedEquivFinsupp s

中文:
定义 supportedEquivFinsupp
  签名: (s : Set M)
  定义体: { toFun x := ⟨x.1.coeff, x.2⟩
    invFun x := ⟨.ofCoeff x.1, x.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
   ≪≫ₗ Finsupp.supportedEquivFinsupp s

Depends on / 依赖: Finsupp, Finsupp.supportedEquivFinsupp, invFun, left_inv, map_add, map_smul, ofCoeff, right_inv, supportedEquivFinsupp
-/
def supportedEquivFinsupp (s : Set M) : supported R S s ≃ₗ[R] s ->₀ S :=
  { toFun x := ⟨x.1.coeff, x.2⟩
    invFun x := ⟨.ofCoeff x.1, x.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
   ≪≫ₗ Finsupp.supportedEquivFinsupp s

end Module

@[to_additive (dont_translate := R) faithfulSMul]
/--
Instance `faithfulSMul` / 实例 `faithfulSMul`

English:
instance faithfulSMul
  signature: [Semiring S] [SMulZeroClass R S] [FaithfulSMul R S] [Nonempty M]
  body: coeffEquiv.faithfulSMul _

中文:
实例 faithfulSMul
  签名: [Semiring S] [SMulZeroClass R S] [FaithfulSMul R S] [Nonempty M]
  定义体: coeffEquiv.faithfulSMul _

Depends on / 依赖: coeffEquiv, coeffEquiv.faithfulSMul, faithfulSMul
-/
instance faithfulSMul [Semiring S] [SMulZeroClass R S] [FaithfulSMul R S] [Nonempty M] :
    FaithfulSMul R S[M] := coeffEquiv.faithfulSMul _

/-- The standard basis for a monoid algebra. -/
@[to_additive /-- The standard basis for an additive monoid algebra. -/]
/--
Definition of `basis` / `basis` 的定义

English:
definition basis
  signature: (R k) [Semiring k]
  body: coeffLinearEquiv _

@[to_additive (dont_translate := k) (attr := simp)]

中文:
定义 basis
  签名: (R k) [Semiring k]
  定义体: coeffLinearEquiv _

@[to_additive (dont_translate := k) (attr := simp)]

Depends on / 依赖: coeffLinearEquiv
-/
def basis (R k) [Semiring k] : Module.Basis R k (MonoidAlgebra k R) where
  repr := coeffLinearEquiv _

@[to_additive (dont_translate := k) (attr := simp)]
/--
lemma `basis_apply` / 引理 `basis_apply`

English:
lemma basis_apply
  given: (k) [Semiring k] (r : R)
  proof: rfl

中文:
引理 basis_apply
  条件: (k) [Semiring k] (r : R)
  证明: rfl
-/
lemma basis_apply (k) [Semiring k] (r : R) :
    MonoidAlgebra.basis R k r = MonoidAlgebra.single r 1 :=
  rfl

/-- This is not an instance as it conflicts with `MonoidAlgebra.distribMulAction` when `M = kˣ`.

TODO: Change the type to `DistribMulAction Gᵈᵐᵃ S[M]` and then it can be an instance.
TODO: Generalise to a group acting on another, instead of just the left multiplication action.
-/
@[implicit_reducible]
/--
Definition of `comapDistribMulActionSelf` / `comapDistribMulActionSelf` 的定义

English:
definition comapDistribMulActionSelf
  signature: [Group G] [Semiring S]
  body: have := Finsupp.comapDistribMulAction (G := G) (α := G) (M := S)
  fast_instance% coeffEquiv.distribMulAction _

中文:
定义 comapDistribMulActionSelf
  签名: [Group G] [Semiring S]
  定义体: have := Finsupp.comapDistribMulAction (G := G) (α := G) (M := S)
  fast_instance% coeffEquiv.distribMulAction _

Depends on / 依赖: Finsupp, Finsupp.comapDistribMulAction, coeffEquiv, coeffEquiv.distribMulAction, comapDistribMulAction, distribMulAction, fast_instance
-/
def comapDistribMulActionSelf [Group G] [Semiring S] : DistribMulAction G S[G] :=
  have := Finsupp.comapDistribMulAction (G := G) (α := G) (M := S)
  fast_instance% coeffEquiv.distribMulAction _

set_option backward.isDefEq.respectTransparency.types false in
@[to_additive (dont_translate := R)]
/--
lemma `single_mem_span_single` / 引理 `single_mem_span_single`

English:
lemma single_mem_span_single
  given: [Semiring R] [Nontrivial R] {m : M} {s : Set M}
  proof: by
  refine (Set.mem_image_equiv (f := (coeffLinearEquiv R).toEquiv)).symm.trans ?_
  change _ in (Submodule.span R _).map (coeffLinearEquiv R).toLinearMap ↔ _
  simp [Submodule.map_span, ← Set.image_comp, Finsupp.single_mem_span_single]

中文:
引理 single_mem_span_single
  条件: [Semiring R] [Nontrivial R] {m : M} {s : Set M}
  证明: by
  refine (Set.mem_image_equiv (f := (coeffLinearEquiv R).toEquiv)).symm.trans ?_
  change _ in (Submodule.span R _).map (coeffLinearEquiv R).toLinearMap ↔ _
  simp [Submodule.map_span, ← Set.image_comp, Finsupp.single_mem_span_single]

Depends on / 依赖: Finsupp, Finsupp.single_mem_span_single, Set.image_comp, Set.mem_image_equiv, Submodule, Submodule.map_span, Submodule.span, coeffLinearEquiv, image_comp, map_span, mem_image_equiv, single_mem_span_single, symm.trans, toEquiv, toLinearMap
-/
lemma single_mem_span_single [Semiring R] [Nontrivial R] {m : M} {s : Set M} :
    single m 1 in Submodule.span R ((single · (1 : R)) '' s) ↔ m in s := by
  refine (Set.mem_image_equiv (f := (coeffLinearEquiv R).toEquiv)).symm.trans ?_
  change _ in (Submodule.span R _).map (coeffLinearEquiv R).toLinearMap ↔ _
  simp [Submodule.map_span, ← Set.image_comp, Finsupp.single_mem_span_single]

end SMul

/-! #### Copies of `ext` lemmas and bundled `single`s from `Finsupp` -/

section ExtLemmas
variable [Semiring S]

/-- `MonoidAlgebra.single` as a `DistribMulActionHom`. -/
@[to_additive (dont_translate := R) singleDistribMulActionHom
/-- `AddMonoidAlgebra.single` as a `DistribMulActionHom`. -/]
/--
Definition of `singleDistribMulActionHom` / `singleDistribMulActionHom` 的定义

English:
definition singleDistribMulActionHom
  signature: [Monoid R] [DistribMulAction R S] (a : M)
  body: singleAddHom a
  map_smul' S m := by simp

中文:
定义 singleDistribMulActionHom
  签名: [Monoid R] [DistribMulAction R S] (a : M)
  定义体: singleAddHom a
  map_smul' S m := by simp

Depends on / 依赖: singleAddHom
-/
def singleDistribMulActionHom [Monoid R] [DistribMulAction R S] (a : M) : S ->+[R] S[M] where
  __ := singleAddHom a
  map_smul' S m := by simp

/-- A copy of `Finsupp.distribMulActionHom_ext'` for `MonoidAlgebra`. -/
@[to_additive (dont_translate := R) (attr := ext) distribMulActionHom_ext'
/-- A copy of `Finsupp.distribMulActionHom_ext'` for `AddMonoidAlgebra`. -/]
/--
theorem `distribMulActionHom_ext'` / 定理 `distribMulActionHom_ext'`

English:
theorem distribMulActionHom_ext'
  statement: {N : Type*} [Monoid R] [AddMonoid N] [DistribMulAction R N]
  proof: DistribMulActionHom.toAddMonoidHom_injective addMonoidHom_ext fun a x => congr($(h a) x)

中文:
定理 distribMulActionHom_ext'
  结论: {N : 类型} [Monoid R] [AddMonoid N] [DistribMulAction R N]
  证明: DistribMulActionHom.toAddMonoidHom_injective addMonoidHom_ext fun a x => congr($(h a) x)

Depends on / 依赖: DistribMulActionHom, DistribMulActionHom.toAddMonoidHom_injective, addMonoidHom_ext, toAddMonoidHom_injective
-/
theorem distribMulActionHom_ext' {N : Type*} [Monoid R] [AddMonoid N] [DistribMulAction R N]
    [DistribMulAction R S] {f g : S[M] ->+[R] N}
    (h : forall a, f.comp (singleDistribMulActionHom a) = g.comp (singleDistribMulActionHom a)) :
    f = g :=
DistribMulActionHom.toAddMonoidHom_injective addMonoidHom_ext fun a x => congr($(h a) x)

/-- A copy of `Finsupp.lsingle` for `MonoidAlgebra`. -/
@[to_additive (dont_translate := R) /-- A copy of `Finsupp.lsingle` for `AddMonoidAlgebra`. -/]
/--
Definition of `lsingle` / `lsingle` 的定义

English:
definition lsingle
  signature: [Semiring R] [Module R S] (a : M)
  body: (coeffLinearEquiv _).symm.toLinearMap.comp Finsupp.lsingle a

@[to_additive (attr := simp)]

中文:
定义 lsingle
  签名: [Semiring R] [Module R S] (a : M)
  定义体: (coeffLinearEquiv _).symm.toLinearMap.comp Finsupp.lsingle a

@[to_additive (attr := simp)]

Depends on / 依赖: Finsupp, Finsupp.lsingle, coeffLinearEquiv, lsingle, symm.toLinearMap.comp, toLinearMap
-/
def lsingle [Semiring R] [Module R S] (a : M) : S ->ₗ[R] S[M] :=
(coeffLinearEquiv _).symm.toLinearMap.comp Finsupp.lsingle a

@[to_additive (attr := simp)]
/--
lemma `lsingle_apply` / 引理 `lsingle_apply`

English:
lemma lsingle_apply
  given: [Semiring R] [Module R S] (a : M) (b : S)
  proof: rfl

中文:
引理 lsingle_apply
  条件: [Semiring R] [Module R S] (a : M) (b : S)
  证明: rfl

Depends on / 依赖: single
-/
lemma lsingle_apply [Semiring R] [Module R S] (a : M) (b : S) :
    lsingle (R := R) a b = single a b :=
  rfl

/-- A copy of `Finsupp.lhom_ext'` for `MonoidAlgebra`. -/
@[to_additive (attr := ext high)]
/--
lemma `lhom_ext'` / 引理 `lhom_ext'`

English:
lemma lhom_ext'
  statement: {N : Type*} [Semiring R] [AddCommMonoid N] [Module R N] [Module R S]
  proof: LinearMap.toAddMonoidHom_injective addMonoidHom_ext fun a x => congr($(H a) x)

中文:
引理 lhom_ext'
  结论: {N : 类型} [Semiring R] [AddCommMonoid N] [Module R N] [Module R S]
  证明: LinearMap.toAddMonoidHom_injective addMonoidHom_ext fun a x => congr($(H a) x)

Depends on / 依赖: LinearMap, LinearMap.toAddMonoidHom_injective, addMonoidHom_ext, toAddMonoidHom_injective
-/
lemma lhom_ext' {N : Type*} [Semiring R] [AddCommMonoid N] [Module R N] [Module R S]
    ⦃f g : S[M] ->ₗ[R] N⦄
    (H : forall (x : M), LinearMap.comp f (lsingle x) = LinearMap.comp g (lsingle x)) : f = g :=
LinearMap.toAddMonoidHom_injective addMonoidHom_ext fun a x => congr($(H a) x)

end ExtLemmas

section MiscTheorems
variable [Semiring R] [Semiring S] [MulOneClass M] {s : Set M} {m : M}

/--
lemma `smul_of` / 引理 `smul_of`

English:
lemma smul_of
  given: (m : M) (r : R)
  statement: r • of R M m = single m r
  proof: by simp

中文:
引理 smul_of
  条件: (m : M) (r : R)
  结论: r • of R M m = single m r
  证明: by simp
-/
lemma smul_of (m : M) (r : R) : r • of R M m = single m r := by simp

/--
lemma `of_mem_span_of_iff` / 引理 `of_mem_span_of_iff`

English:
lemma of_mem_span_of_iff
  given: [Nontrivial R]
  statement: of R M m in Submodule.span R (of R M '' s) ↔ m in s
  proof: single_mem_span_single

中文:
引理 of_mem_span_of_iff
  条件: [Nontrivial R]
  结论: of R M m in Submodule.span R (of R M '' s) ↔ m in s
  证明: single_mem_span_single

Depends on / 依赖: single_mem_span_single
-/
lemma of_mem_span_of_iff [Nontrivial R] : of R M m in Submodule.span R (of R M '' s) ↔ m in s :=
  single_mem_span_single

/--
lemma `mem_closure_of_mem_span_closure` / 引理 `mem_closure_of_mem_span_closure`

English:
lemma mem_closure_of_mem_span_closure
  statement: [Nontrivial R]
  proof: by
  rw [← MonoidHom.map_mclosure] at h; simpa using of_mem_span_of_iff.1 h

中文:
引理 mem_closure_of_mem_span_closure
  结论: [Nontrivial R]
  证明: by
  rw [← MonoidHom.map_mclosure] at h; simpa using of_mem_span_of_iff.1 h

Depends on / 依赖: MonoidHom, MonoidHom.map_mclosure, map_mclosure, of_mem_span_of_iff
-/
lemma mem_closure_of_mem_span_closure [Nontrivial R]
    (h : of R M m in Submodule.span R (Submonoid.closure <| of R M '' s)) :
    m in Submonoid.closure s := by
  rw [← MonoidHom.map_mclosure] at h; simpa using of_mem_span_of_iff.1 h

/--
theorem `liftNC_smul` / 定理 `liftNC_smul`

English:
theorem liftNC_smul
  given: (f : S ->+* R) (g : M ->* R) (c : S) (φ : S[M])
  proof: by
  suffices (liftNC (↑f) g).comp (smulAddHom S S[M] c) =
      (AddMonoidHom.mulLeft (f c)).comp (liftNC (↑f) g) from
    DFunLike.congr_fun this φ
  ext
  simp [mul_assoc]

中文:
定理 liftNC_smul
  条件: (f : S ->+* R) (g : M ->* R) (c : S) (φ : S[M])
  证明: by
  suffices (liftNC (↑f) g).comp (smulAddHom S S[M] c) =
      (AddMonoidHom.mulLeft (f c)).comp (liftNC (↑f) g) from
    DFunLike.congr_fun this φ
  ext
  simp [mul_assoc]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mulLeft, DFunLike, DFunLike.congr_fun, congr_fun, liftNC, mulLeft, mul_assoc, smulAddHom
-/
theorem liftNC_smul (f : S ->+* R) (g : M ->* R) (c : S) (φ : S[M]) :
    liftNC (f : S ->+ R) g (c • φ) = f c * liftNC (f : S ->+ R) g φ := by
  suffices (liftNC (↑f) g).comp (smulAddHom S S[M] c) =
      (AddMonoidHom.mulLeft (f c)).comp (liftNC (↑f) g) from
    DFunLike.congr_fun this φ
  ext
  simp [mul_assoc]

end MiscTheorems

/-! #### Non-unital, non-associative algebra structure -/
section NonUnitalNonAssocAlgebra

variable (S) [Semiring S] [DistribSMul R S] [Mul M]

@[to_additive (dont_translate := R S) isScalarTower_self]
/--
Instance `isScalarTower_self` / 实例 `isScalarTower_self`

English:
instance isScalarTower_self
  signature: [IsScalarTower R S S]
  body: by
    classical ext; simp [coeff_mul, sum_smul_index', Finsupp.smul_sum, smul_mul_assoc]

中文:
实例 isScalarTower_self
  签名: [IsScalarTower R S S]
  定义体: by
    classical ext; simp [coeff_mul, sum_smul_index', Finsupp.smul_sum, smul_mul_assoc]

Depends on / 依赖: Finsupp, Finsupp.smul_sum, classical, coeff_mul, smul_mul_assoc, smul_sum, sum_smul_index
-/
instance isScalarTower_self [IsScalarTower R S S] : IsScalarTower R S[M] S[M] where
  smul_assoc t a b := by
    classical ext; simp [coeff_mul, sum_smul_index', Finsupp.smul_sum, smul_mul_assoc]

/-- Note that if `S` is a `CommSemiring` then we have `SMulCommClass S S S` and so we can take
`R = S` in the below. In other words, if the coefficients are commutative amongst themselves, they
also commute with the algebra multiplication. -/
@[to_additive (dont_translate := R S) smulCommClass_self]
/--
Instance `smulCommClass_self` / 实例 `smulCommClass_self`

English:
instance smulCommClass_self
  signature: [SMulCommClass R S S]
  body: by
    classical ext; simp [coeff_mul, sum_smul_index', Finsupp.smul_sum, mul_smul_comm]

@[to_additive (dont_translate := R S) smulCommClass_symm_self]

中文:
实例 smulCommClass_self
  签名: [SMulCommClass R S S]
  定义体: by
    classical ext; simp [coeff_mul, sum_smul_index', Finsupp.smul_sum, mul_smul_comm]

@[to_additive (dont_translate := R S) smulCommClass_symm_self]

Depends on / 依赖: Finsupp, Finsupp.smul_sum, classical, coeff_mul, mul_smul_comm, smul_sum, sum_smul_index
-/
instance smulCommClass_self [SMulCommClass R S S] : SMulCommClass R S[M] S[M] where
  smul_comm t a b := by
    classical ext; simp [coeff_mul, sum_smul_index', Finsupp.smul_sum, mul_smul_comm]

@[to_additive (dont_translate := R S) smulCommClass_symm_self]
/--
Instance `smulCommClass_symm_self` / 实例 `smulCommClass_symm_self`

English:
instance smulCommClass_symm_self
  signature: [SMulCommClass S R S]
  body: have := SMulCommClass.symm S R S; .symm ..

中文:
实例 smulCommClass_symm_self
  签名: [SMulCommClass S R S]
  定义体: have := SMulCommClass.symm S R S; .symm ..

Depends on / 依赖: SMulCommClass, SMulCommClass.symm
-/
instance smulCommClass_symm_self [SMulCommClass S R S] : SMulCommClass S[M] R S[M] :=
  have := SMulCommClass.symm S R S; .symm ..

end NonUnitalNonAssocAlgebra

section Submodule

variable [CommSemiring S] [Monoid M]
variable {V : Type*} [AddCommMonoid V]
variable [Module S V] [Module S[M] V] [IsScalarTower S S[M] V]

/--
Definition of `submoduleOfSMulMem` / `submoduleOfSMulMem` 的定义

English:
definition submoduleOfSMulMem
  signature: (W : Submodule S V) (h : forall (g : M) (v : V), v in W -> of S M g • v in W)
  body: W
  zero_mem' := W.zero_mem'
  add_mem' := W.add_mem'
  smul_mem' f v hv := by
    rw [← f.sum_coeff_single]; rw [Finsupp.sum]; rw [Finset.sum_smul]
    simp_rw [← smul_of, smul_assoc]
    exact Submodule.sum_smul_mem W _ fun g _ => h g v hv

中文:
定义 submoduleOfSMulMem
  签名: (W : Submodule S V) (h : 对任意 (g : M) (v : V), v in W -> of S M g • v in W)
  定义体: W
  zero_mem' := W.zero_mem'
  add_mem' := W.add_mem'
  smul_mem' f v hv := by
    rw [← f.sum_coeff_single]; rw [Finsupp.sum]; rw [Finset.sum_smul]
    simp_rw [← smul_of, smul_assoc]
    exact Submodule.sum_smul_mem W _ fun g _ => h g v hv
-/
def submoduleOfSMulMem (W : Submodule S V) (h : forall (g : M) (v : V), v in W -> of S M g • v in W) :
    Submodule S[M] V where
  carrier := W
  zero_mem' := W.zero_mem'
  add_mem' := W.add_mem'
  smul_mem' f v hv := by
    rw [← f.sum_coeff_single]; rw [Finsupp.sum]; rw [Finset.sum_smul]
    simp_rw [← smul_of, smul_assoc]
    exact Submodule.sum_smul_mem W _ fun g _ => h g v hv

end Submodule

end MonoidAlgebra

/-! ### Additive monoids -/

namespace AddMonoidAlgebra
section Semiring
variable [Semiring R] [Semiring S]

/--
lemma `of'_mem_span` / 引理 `of'_mem_span`

English:
lemma of'_mem_span
  given: [Nontrivial R] {m : M} {s : Set M}
  proof: single_mem_span_single

中文:
引理 of'_mem_span
  条件: [Nontrivial R] {m : M} {s : Set M}
  证明: single_mem_span_single
-/
lemma of'_mem_span [Nontrivial R] {m : M} {s : Set M} :
    of' R M m in Submodule.span R (of' R M '' s) ↔ m in s := single_mem_span_single

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mem_closure_of_mem_span_closure` / 引理 `mem_closure_of_mem_span_closure`

English:
lemma mem_closure_of_mem_span_closure
  statement: [AddMonoid M] [Nontrivial R] {m : M} {s : Set M}
  proof: by
  suffices Multiplicative.ofAdd m in Submonoid.closure (Multiplicative.toAdd ⁻¹' s) by
    simpa [← AddSubmonoid.toSubmonoid_closure]
  let s' := @Submonoid.closure (Multiplicative M) Multiplicative.mulOneClass s
  have h' : Submonoid.map (of R M) s' = Submonoid.closure (of R M '' s) :=
    Monoi

中文:
引理 mem_closure_of_mem_span_closure
  结论: [AddMonoid M] [Nontrivial R] {m : M} {s : Set M}
  证明: by
  suffices Multiplicative.ofAdd m in Submonoid.closure (Multiplicative.toAdd ⁻¹' s) by
    simpa [← AddSubmonoid.toSubmonoid_closure]
  let s' := @Submonoid.closure (Multiplicative M) Multiplicative.mulOneClass s
  have h' : Submonoid.map (of R M) s' = Submonoid.closure (of R M '' s) :=
    Monoi

Depends on / 依赖: AddSubmonoid, AddSubmonoid.toSubmonoid_closure, MonoidHom, MonoidHom.map_mclosure, Multiplicative, Multiplicative.mulOneClass, Multiplicative.ofAdd, Multiplicative.toAdd, Set.image_congr, Submonoid, Submonoid.closure, Submonoid.map, _eq_of, _mem_span, closure, image_congr, map_mclosure, mulOneClass, toSubmonoid_closure
-/
lemma mem_closure_of_mem_span_closure [AddMonoid M] [Nontrivial R] {m : M} {s : Set M}
    (h : of' R M m in Submodule.span R (Submonoid.closure <| of' R M '' s)) :
    m in AddSubmonoid.closure s := by
  suffices Multiplicative.ofAdd m in Submonoid.closure (Multiplicative.toAdd ⁻¹' s) by
    simpa [← AddSubmonoid.toSubmonoid_closure]
  let s' := @Submonoid.closure (Multiplicative M) Multiplicative.mulOneClass s
  have h' : Submonoid.map (of R M) s' = Submonoid.closure (of R M '' s) :=
    MonoidHom.map_mclosure _ _
  rw [Set.image_congr' (show forall x]; rw [of' R M x = of R M x from fun x => of'_eq_of x)]; rw [← h'] at h
  simpa using! of'_mem_span.1 h

/--
lemma `liftNC_smul` / 引理 `liftNC_smul`

English:
lemma liftNC_smul
  given: [AddZeroClass M] (f : S ->+* R) (g : Multiplicative M ->* R) (c : S) (φ : S[M])
  proof: by
  suffices (liftNC (↑f) g).comp (smulAddHom S S[M] c) =
      (AddMonoidHom.mulLeft (f c)).comp (liftNC f g) from DFunLike.congr_fun this φ
  ext
  simp [mul_assoc]

中文:
引理 liftNC_smul
  条件: [AddZeroClass M] (f : S ->+* R) (g : Multiplicative M ->* R) (c : S) (φ : S[M])
  证明: by
  suffices (liftNC (↑f) g).comp (smulAddHom S S[M] c) =
      (AddMonoidHom.mulLeft (f c)).comp (liftNC f g) from DFunLike.congr_fun this φ
  ext
  simp [mul_assoc]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mulLeft, DFunLike, DFunLike.congr_fun, congr_fun, liftNC, mulLeft, mul_assoc, smulAddHom
-/
lemma liftNC_smul [AddZeroClass M] (f : S ->+* R) (g : Multiplicative M ->* R) (c : S) (φ : S[M]) :
    liftNC (f : S ->+ R) g (c • φ) = f c * liftNC (f : S ->+ R) g φ := by
  suffices (liftNC (↑f) g).comp (smulAddHom S S[M] c) =
      (AddMonoidHom.mulLeft (f c)).comp (liftNC f g) from DFunLike.congr_fun this φ
  ext
  simp [mul_assoc]

end Semiring
end AddMonoidAlgebra
