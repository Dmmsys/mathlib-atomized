/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.Finsupp.SMul

/-!
# Properties of the module `α →₀ M`

Given an `R`-module `M`, the `R`-module structure on `α →₀ M` is defined in
`Mathlib/Data/Finsupp/SMul.lean`.

In this file we define `LinearMap` versions of various maps:

* `Finsupp.lsingle a : M →ₗ[R] ι →₀ M`: `Finsupp.single a` as a linear map;
* `Finsupp.lapply a : (ι →₀ M) →ₗ[R] M`: the map `fun f ↦ f a` as a linear map;
* `Finsupp.lsubtypeDomain (s : Set α) : (α →₀ M) →ₗ[R] (s →₀ M)`: restriction to a subtype as a
  linear map;
* `Finsupp.restrictDom`: `Finsupp.filter` as a linear map to `Finsupp.supported s`;
* `Finsupp.lmapDomain`: a linear map version of `Finsupp.mapDomain`;

## Tags

function with finite support, module, linear algebra
-/

@[expose] public section

assert_not_exists Submodule

noncomputable section

open Set LinearMap

namespace Finsupp

variable {α : Type*} {M : Type*} {N : Type*} {P : Type*} {R R₂ R₃ : Type*} {S : Type*}
variable [Semiring R] [Semiring R₂] [Semiring R₃] [Semiring S]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R₂ N]
variable [AddCommMonoid P] [Module R₃ P]
variable {σ₁₂ : R ->+* R₂} {σ₂₁ : R₂ ->+* R}
variable {σ₂₃ : R₂ ->+* R₃} {σ₃₂ : R₃ ->+* R₂}
variable {σ₁₃ : R ->+* R₃} {σ₃₁ : R₃ ->+* R}
variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]

section LinearEquivFunOnFinite

variable (R : Type*) {S : Type*} (M : Type*) (α : Type*)
variable [Finite α] [AddCommMonoid M] [Semiring R] [Module R M]

/-- Given `Finite α`, `linearEquivFunOnFinite R` is the natural `R`-linear equivalence between
`α →₀ β` and `α → β`. -/
@[simps apply]
/--
Definition of `linearEquivFunOnFinite` / `linearEquivFunOnFinite` 的定义

English:
definition linearEquivFunOnFinite
  signature: : (α ->₀ M) ≃ₗ[R] α -> M
  body: { equivFunOnFinite with
    toFun := (⇑)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

@[simp]

中文:
定义 linearEquivFunOnFinite
  签名: : (α ->₀ M) ≃ₗ[R] α -> M
  定义体: { equivFunOnFinite with
    toFun := (⇑)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

@[simp]

Depends on / 依赖: equivFunOnFinite, map_add, map_smul
-/
noncomputable def linearEquivFunOnFinite : (α ->₀ M) ≃ₗ[R] α -> M :=
  { equivFunOnFinite with
    toFun := (⇑)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

@[simp]
/--
theorem `linearEquivFunOnFinite_single` / 定理 `linearEquivFunOnFinite_single`

English:
theorem linearEquivFunOnFinite_single
  given: [DecidableEq α] (x : α) (m : M)
  proof: equivFunOnFinite_single x m

@[simp]

中文:
定理 linearEquivFunOnFinite_single
  条件: [DecidableEq α] (x : α) (m : M)
  证明: equivFunOnFinite_single x m

@[simp]

Depends on / 依赖: equivFunOnFinite_single
-/
theorem linearEquivFunOnFinite_single [DecidableEq α] (x : α) (m : M) :
    (linearEquivFunOnFinite R M α) (single x m) = Pi.single x m :=
  equivFunOnFinite_single x m

@[simp]
/--
theorem `linearEquivFunOnFinite_symm_single` / 定理 `linearEquivFunOnFinite_symm_single`

English:
theorem linearEquivFunOnFinite_symm_single
  given: [DecidableEq α] (x : α) (m : M)
  proof: equivFunOnFinite_symm_single x m

@[simp]

中文:
定理 linearEquivFunOnFinite_symm_single
  条件: [DecidableEq α] (x : α) (m : M)
  证明: equivFunOnFinite_symm_single x m

@[simp]

Depends on / 依赖: equivFunOnFinite_symm_single
-/
theorem linearEquivFunOnFinite_symm_single [DecidableEq α] (x : α) (m : M) :
    (linearEquivFunOnFinite R M α).symm (Pi.single x m) = single x m :=
  equivFunOnFinite_symm_single x m

@[simp]
/--
theorem `linearEquivFunOnFinite_symm_coe` / 定理 `linearEquivFunOnFinite_symm_coe`

English:
theorem linearEquivFunOnFinite_symm_coe
  given: (f : α ->₀ M)
  statement: (linearEquivFunOnFinite R M α).symm f = f
  proof: (linearEquivFunOnFinite R M α).symm_apply_apply f

@[simp]

中文:
定理 linearEquivFunOnFinite_symm_coe
  条件: (f : α ->₀ M)
  结论: (linearEquivFunOnFinite R M α).symm f = f
  证明: (linearEquivFunOnFinite R M α).symm_apply_apply f

@[simp]

Depends on / 依赖: linearEquivFunOnFinite, symm_apply_apply
-/
theorem linearEquivFunOnFinite_symm_coe (f : α ->₀ M) : (linearEquivFunOnFinite R M α).symm f = f :=
  (linearEquivFunOnFinite R M α).symm_apply_apply f

@[simp]
/--
theorem `linearEquivFunOnFinite_symm_apply` / 定理 `linearEquivFunOnFinite_symm_apply`

English:
theorem linearEquivFunOnFinite_symm_apply
  given: (f : α -> M)
  statement: (linearEquivFunOnFinite R M α).symm f = f
  proof: rfl

中文:
定理 linearEquivFunOnFinite_symm_apply
  条件: (f : α -> M)
  结论: (linearEquivFunOnFinite R M α).symm f = f
  证明: rfl
-/
theorem linearEquivFunOnFinite_symm_apply (f : α -> M) : (linearEquivFunOnFinite R M α).symm f = f :=
  rfl

end LinearEquivFunOnFinite

/--
Definition of `lsingle` / `lsingle` 的定义

English:
definition lsingle
  signature: (a : α)
  body: { Finsupp.singleAddHom a with map_smul' := fun _ _ => (smul_single _ _ _).symm }

中文:
定义 lsingle
  签名: (a : α)
  定义体: { Finsupp.singleAddHom a with map_smul' := fun _ _ => (smul_single _ _ _).symm }

Depends on / 依赖: Finsupp, Finsupp.singleAddHom, map_smul, singleAddHom, smul_single
-/
def lsingle (a : α) : M ->ₗ[R] α ->₀ M :=
  { Finsupp.singleAddHom a with map_smul' := fun _ _ => (smul_single _ _ _).symm }

/--
theorem `lhom_ext` / 定理 `lhom_ext`

English:
theorem lhom_ext
  given: ⦃φ ψ
  statement: (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a b, φ (single a b) = ψ (single a b)) : φ = ψ
  proof: LinearMap.toAddMonoidHom_injective addHom_ext h

中文:
定理 lhom_ext
  条件: ⦃φ ψ
  结论: (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : 对任意 a b, φ (single a b) = ψ (single a b)) : φ = ψ
  证明: LinearMap.toAddMonoidHom_injective addHom_ext h

Depends on / 依赖: LinearMap, LinearMap.toAddMonoidHom_injective, addHom_ext, toAddMonoidHom_injective
-/
theorem lhom_ext ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a b, φ (single a b) = ψ (single a b)) : φ = ψ :=
LinearMap.toAddMonoidHom_injective addHom_ext h

/-- Two `R`-linear maps from `Finsupp X M` which agree on each `single x y` agree everywhere.

We formulate this fact using equality of linear maps `φ.comp (lsingle a)` and `ψ.comp (lsingle a)`
so that the `ext` tactic can apply a type-specific extensionality lemma to prove equality of these
maps. E.g., if `M = R`, then it suffices to verify `φ (single a 1) = ψ (single a 1)`. -/
-- The priority should be higher than `LinearMap.ext`.
@[ext high]
/--
theorem `lhom_ext'` / 定理 `lhom_ext'`

English:
theorem lhom_ext'
  given: ⦃φ ψ
  statement: (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a, φ.comp (lsingle a) = ψ.comp (lsingle a)) :
  proof: lhom_ext fun a => LinearMap.congr_fun (h a)

中文:
定理 lhom_ext'
  条件: ⦃φ ψ
  结论: (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : 对任意 a, φ.comp (lsingle a) = ψ.comp (lsingle a)) :
  证明: lhom_ext fun a => LinearMap.congr_fun (h a)

Depends on / 依赖: LinearMap, LinearMap.congr_fun, congr_fun, lhom_ext
-/
theorem lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a, φ.comp (lsingle a) = ψ.comp (lsingle a)) :
    φ = ψ :=
  lhom_ext fun a => LinearMap.congr_fun (h a)

/--
Definition of `lapply` / `lapply` 的定义

English:
definition lapply
  signature: (a : α)
  body: { Finsupp.applyAddHom a with map_smul' := fun _ _ => rfl }

中文:
定义 lapply
  签名: (a : α)
  定义体: { Finsupp.applyAddHom a with map_smul' := fun _ _ => rfl }

Depends on / 依赖: Finsupp, Finsupp.applyAddHom, applyAddHom, map_smul, toMeasurableMul
-/
def lapply (a : α) : (α ->₀ M) ->ₗ[R] M :=
  { Finsupp.applyAddHom a with map_smul' := fun _ _ => rfl }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: α] [FaithfulSMul R M] : FaithfulSMul R (α ->₀ M)
  body: .of_injective (Finsupp.lsingle <| Classical.arbitrary _) (Finsupp.single_injective _)

中文:
实例 [Nonempty
  签名: α] [FaithfulSMul R M] : FaithfulSMul R (α ->₀ M)
  定义体: .of_injective (Finsupp.lsingle <| Classical.arbitrary _) (Finsupp.single_injective _)

Depends on / 依赖: Classical, Classical.arbitrary, Finsupp, Finsupp.lsingle, Finsupp.single_injective, arbitrary, lsingle, of_injective, single_injective
-/
instance [Nonempty α] [FaithfulSMul R M] : FaithfulSMul R (α ->₀ M) :=
  .of_injective (Finsupp.lsingle <| Classical.arbitrary _) (Finsupp.single_injective _)

section LSubtypeDomain

variable (s : Set α)

/--
Definition of `lsubtypeDomain` / `lsubtypeDomain` 的定义

English:
definition lsubtypeDomain
  signature: : (α ->₀ M) ->ₗ[R] s ->₀ M where
  body: subtypeDomain fun x => x in s
  map_add' _ _ := subtypeDomain_add
  map_smul' _ _ := ext fun _ => rfl

中文:
定义 lsubtypeDomain
  签名: : (α ->₀ M) ->ₗ[R] s ->₀ M where
  定义体: subtypeDomain fun x => x in s
  map_add' _ _ := subtypeDomain_add
  map_smul' _ _ := ext fun _ => rfl

Depends on / 依赖: subtypeDomain
-/
def lsubtypeDomain : (α ->₀ M) ->ₗ[R] s ->₀ M where
  toFun := subtypeDomain fun x => x in s
  map_add' _ _ := subtypeDomain_add
  map_smul' _ _ := ext fun _ => rfl

/--
theorem `lsubtypeDomain_apply` / 定理 `lsubtypeDomain_apply`

English:
theorem lsubtypeDomain_apply
  given: (f : α ->₀ M)
  proof: rfl

中文:
定理 lsubtypeDomain_apply
  条件: (f : α ->₀ M)
  证明: rfl
-/
theorem lsubtypeDomain_apply (f : α ->₀ M) :
    (lsubtypeDomain s : (α ->₀ M) ->ₗ[R] s ->₀ M) f = subtypeDomain (fun x => x in s) f :=
  rfl

end LSubtypeDomain

@[simp]
/--
theorem `lsingle_apply` / 定理 `lsingle_apply`

English:
theorem lsingle_apply
  given: (a : α) (b : M)
  statement: (lsingle a : M ->ₗ[R] α ->₀ M) b = single a b
  proof: rfl

@[simp]

中文:
定理 lsingle_apply
  条件: (a : α) (b : M)
  结论: (lsingle a : M ->ₗ[R] α ->₀ M) b = single a b
  证明: rfl

@[simp]
-/
theorem lsingle_apply (a : α) (b : M) : (lsingle a : M ->ₗ[R] α ->₀ M) b = single a b :=
  rfl

@[simp]
/--
theorem `lapply_apply` / 定理 `lapply_apply`

English:
theorem lapply_apply
  given: (a : α) (f : α ->₀ M)
  statement: (lapply a : (α ->₀ M) ->ₗ[R] M) f = f a
  proof: rfl

@[simp]

中文:
定理 lapply_apply
  条件: (a : α) (f : α ->₀ M)
  结论: (lapply a : (α ->₀ M) ->ₗ[R] M) f = f a
  证明: rfl

@[simp]
-/
theorem lapply_apply (a : α) (f : α ->₀ M) : (lapply a : (α ->₀ M) ->ₗ[R] M) f = f a :=
  rfl

@[simp]
/--
theorem `lapply_comp_lsingle_same` / 定理 `lapply_comp_lsingle_same`

English:
theorem lapply_comp_lsingle_same
  given: (a : α)
  statement: lapply a ∘ₗ lsingle a = (.id : M ->ₗ[R] M)
  proof: by ext; simp

@[simp]

中文:
定理 lapply_comp_lsingle_same
  条件: (a : α)
  结论: lapply a ∘ₗ lsingle a = (.id : M ->ₗ[R] M)
  证明: by ext; simp

@[simp]
-/
theorem lapply_comp_lsingle_same (a : α) : lapply a ∘ₗ lsingle a = (.id : M ->ₗ[R] M) := by ext; simp

@[simp]
/--
theorem `lapply_comp_lsingle_of_ne` / 定理 `lapply_comp_lsingle_of_ne`

English:
theorem lapply_comp_lsingle_of_ne
  given: (a a' : α) (h : a != a')
  proof: by ext; simp [h.symm]

中文:
定理 lapply_comp_lsingle_of_ne
  条件: (a a' : α) (h : a != a')
  证明: by ext; simp [h.symm]

Depends on / 依赖: h.symm
-/
theorem lapply_comp_lsingle_of_ne (a a' : α) (h : a != a') :
    lapply a ∘ₗ lsingle a' = (0 : M ->ₗ[R] M) := by ext; simp [h.symm]

section LMapDomain

variable {α' : Type*} {α'' : Type*} (M R)

/--
Definition of `lmapDomain` / `lmapDomain` 的定义

English:
definition lmapDomain
  signature: (f : α -> α')
  body: mapDomain f
  map_add' _ _ := mapDomain_add
  map_smul' := mapDomain_smul

@[simp]

中文:
定义 lmapDomain
  签名: (f : α -> α')
  定义体: mapDomain f
  map_add' _ _ := mapDomain_add
  map_smul' := mapDomain_smul

@[simp]

Depends on / 依赖: mapDomain
-/
def lmapDomain (f : α -> α') : (α ->₀ M) ->ₗ[R] α' ->₀ M where
  toFun := mapDomain f
  map_add' _ _ := mapDomain_add
  map_smul' := mapDomain_smul

@[simp]
/--
theorem `lmapDomain_apply` / 定理 `lmapDomain_apply`

English:
theorem lmapDomain_apply
  given: (f : α -> α') (l : α ->₀ M)
  proof: rfl

中文:
定理 lmapDomain_apply
  条件: (f : α -> α') (l : α ->₀ M)
  证明: rfl
-/
theorem lmapDomain_apply (f : α -> α') (l : α ->₀ M) :
    (lmapDomain M R f : (α ->₀ M) ->ₗ[R] α' ->₀ M) l = mapDomain f l :=
  rfl

/--
lemma `coe_lmapDomain` / 引理 `coe_lmapDomain`

English:
lemma coe_lmapDomain
  given: (f : α -> α')
  statement: ⇑(lmapDomain M R f) = Finsupp.mapDomain f
  proof: rfl

@[simp]

中文:
引理 coe_lmapDomain
  条件: (f : α -> α')
  结论: ⇑(lmapDomain M R f) = Finsupp.mapDomain f
  证明: rfl

@[simp]
-/
lemma coe_lmapDomain (f : α -> α') : ⇑(lmapDomain M R f) = Finsupp.mapDomain f :=
  rfl

@[simp]
/--
theorem `lmapDomain_id` / 定理 `lmapDomain_id`

English:
theorem lmapDomain_id
  statement: (lmapDomain M R _root_.id : (α ->₀ M) ->ₗ[R] α ->₀ M) = LinearMap.id
  proof: LinearMap.ext fun _ => mapDomain_id

中文:
定理 lmapDomain_id
  结论: (lmapDomain M R _root_.id : (α ->₀ M) ->ₗ[R] α ->₀ M) = LinearMap.id
  证明: LinearMap.ext fun _ => mapDomain_id

Depends on / 依赖: LinearMap, LinearMap.ext, mapDomain_id
-/
theorem lmapDomain_id : (lmapDomain M R _root_.id : (α ->₀ M) ->ₗ[R] α ->₀ M) = LinearMap.id :=
  LinearMap.ext fun _ => mapDomain_id

/--
theorem `lmapDomain_comp` / 定理 `lmapDomain_comp`

English:
theorem lmapDomain_comp
  given: (f : α -> α') (g : α' -> α'')
  proof: LinearMap.ext fun _ => mapDomain_comp

中文:
定理 lmapDomain_comp
  条件: (f : α -> α') (g : α' -> α'')
  证明: LinearMap.ext fun _ => mapDomain_comp

Depends on / 依赖: LinearMap, LinearMap.ext, mapDomain_comp
-/
theorem lmapDomain_comp (f : α -> α') (g : α' -> α'') :
    lmapDomain M R (g ∘ f) = (lmapDomain M R g).comp (lmapDomain M R f) :=
  LinearMap.ext fun _ => mapDomain_comp

/--
Definition of `mapDomain.linearEquiv` / `mapDomain.linearEquiv` 的定义

English:
definition mapDomain.linearEquiv
  signature: (f : α ≃ α')
  body: lmapDomain M R f.toFun
  invFun := mapDomain f.symm
  left_inv _ := by
    simp [← mapDomain_comp]
  right_inv _ := by
    simp [← mapDomain_comp]

中文:
定义 mapDomain.linearEquiv
  签名: (f : α ≃ α')
  定义体: lmapDomain M R f.toFun
  invFun := mapDomain f.symm
  left_inv _ := by
    simp [← mapDomain_comp]
  right_inv _ := by
    simp [← mapDomain_comp]

Depends on / 依赖: f.toFun, lmapDomain
-/
def mapDomain.linearEquiv (f : α ≃ α') : (α ->₀ M) ≃ₗ[R] (α' ->₀ M) where
  __ := lmapDomain M R f.toFun
  invFun := mapDomain f.symm
  left_inv _ := by
    simp [← mapDomain_comp]
  right_inv _ := by
    simp [← mapDomain_comp]

/--
theorem `mapDomain.coe_linearEquiv` / 定理 `mapDomain.coe_linearEquiv`

English:
theorem mapDomain.coe_linearEquiv
  given: (f : α ≃ α')
  proof: rfl

中文:
定理 mapDomain.coe_linearEquiv
  条件: (f : α ≃ α')
  证明: rfl
-/
@[simp] theorem mapDomain.coe_linearEquiv (f : α ≃ α') :
    ⇑(linearEquiv M R f) = mapDomain f := rfl

/--
theorem `mapDomain.toLinearMap_linearEquiv` / 定理 `mapDomain.toLinearMap_linearEquiv`

English:
theorem mapDomain.toLinearMap_linearEquiv
  given: (f : α ≃ α')
  proof: rfl

中文:
定理 mapDomain.toLinearMap_linearEquiv
  条件: (f : α ≃ α')
  证明: rfl
-/
@[simp] theorem mapDomain.toLinearMap_linearEquiv (f : α ≃ α') :
    (linearEquiv M R f : _ ->ₗ[R] _) = lmapDomain M R f := rfl

/--
theorem `mapDomain.linearEquiv_symm` / 定理 `mapDomain.linearEquiv_symm`

English:
theorem mapDomain.linearEquiv_symm
  given: (f : α ≃ α')
  proof: rfl

中文:
定理 mapDomain.linearEquiv_symm
  条件: (f : α ≃ α')
  证明: rfl
-/
@[simp] theorem mapDomain.linearEquiv_symm (f : α ≃ α') :
    (linearEquiv M R f).symm = linearEquiv M R f.symm := rfl

end LMapDomain

section LComapDomain

variable {β : Type*}

/-- Given `f : α → β` and a proof `hf` that `f` is injective, `lcomapDomain f hf` is the linear map
sending `l : β →₀ M` to the finitely supported function from `α` to `M` given by composing
`l` with `f`.

This is the linear version of `Finsupp.comapDomain`. -/
@[simps]
/--
Definition of `lcomapDomain` / `lcomapDomain` 的定义

English:
definition lcomapDomain
  signature: (f : α -> β) (hf : Function.Injective f)
  body: Finsupp.comapDomain f l hf.injOn
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

中文:
定义 lcomapDomain
  签名: (f : α -> β) (hf : Function.Injective f)
  定义体: Finsupp.comapDomain f l hf.injOn
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

Depends on / 依赖: Finsupp, Finsupp.comapDomain, comapDomain, hf.injOn
-/
def lcomapDomain (f : α -> β) (hf : Function.Injective f) : (β ->₀ M) ->ₗ[R] α ->₀ M where
  toFun l := Finsupp.comapDomain f l hf.injOn
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

/--
theorem `leftInverse_lcomapDomain_mapDomain` / 定理 `leftInverse_lcomapDomain_mapDomain`

English:
theorem leftInverse_lcomapDomain_mapDomain
  given: (f : α -> β) (hf : Function.Injective f)
  proof: comapDomain_mapDomain f hf

中文:
定理 leftInverse_lcomapDomain_mapDomain
  条件: (f : α -> β) (hf : Function.Injective f)
  证明: comapDomain_mapDomain f hf

Depends on / 依赖: mapDomain
-/
theorem leftInverse_lcomapDomain_mapDomain (f : α -> β) (hf : Function.Injective f) :
    Function.LeftInverse (lcomapDomain (R := R) (M := M) f hf) (mapDomain f) :=
  comapDomain_mapDomain f hf

end LComapDomain

/-- `Finsupp.mapRange` as a `LinearMap`. -/
@[simps apply]
/--
Definition of `mapRange.linearMap` / `mapRange.linearMap` 的定义

English:
definition mapRange.linearMap
  signature: (f : M ->ₛₗ[σ₁₂] N)
  body: { mapRange.addMonoidHom f.toAddMonoidHom with
    toFun := (mapRange f f.map_zero : (α ->₀ M) -> α ->₀ N)
    map_smul' := fun c v => mapRange_smul' c (σ₁₂ c) v (f.map_smulₛₗ c) }

@[simp]

中文:
定义 mapRange.linearMap
  签名: (f : M ->ₛₗ[σ₁₂] N)
  定义体: { mapRange.addMonoidHom f.toAddMonoidHom with
    toFun := (mapRange f f.map_zero : (α ->₀ M) -> α ->₀ N)
    map_smul' := fun c v => mapRange_smul' c (σ₁₂ c) v (f.map_smulₛₗ c) }

@[simp]
-/
def mapRange.linearMap (f : M ->ₛₗ[σ₁₂] N) : (α ->₀ M) ->ₛₗ[σ₁₂] α ->₀ N :=
  { mapRange.addMonoidHom f.toAddMonoidHom with
    toFun := (mapRange f f.map_zero : (α ->₀ M) -> α ->₀ N)
    map_smul' := fun c v => mapRange_smul' c (σ₁₂ c) v (f.map_smulₛₗ c) }

@[simp]
/--
theorem `mapRange.linearMap_id` / 定理 `mapRange.linearMap_id`

English:
theorem mapRange.linearMap_id
  proof: LinearMap.ext mapRange_id

中文:
定理 mapRange.linearMap_id
  证明: LinearMap.ext mapRange_id

Depends on / 依赖: toMeasurableDiv
-/
theorem mapRange.linearMap_id :
    mapRange.linearMap LinearMap.id = (LinearMap.id : (α ->₀ M) ->ₗ[R] _) :=
  LinearMap.ext mapRange_id

/--
theorem `mapRange.linearMap_comp` / 定理 `mapRange.linearMap_comp`

English:
theorem mapRange.linearMap_comp
  given: (f : N ->ₛₗ[σ₂₃] P) (f₂ : M ->ₛₗ[σ₁₂] N)
  proof: LinearMap.ext mapRange_comp f f.map_zero f₂ f₂.map_zero (comp f f₂).map_zero

@[simp]

中文:
定理 mapRange.linearMap_comp
  条件: (f : N ->ₛₗ[σ₂₃] P) (f₂ : M ->ₛₗ[σ₁₂] N)
  证明: LinearMap.ext mapRange_comp f f.map_zero f₂ f₂.map_zero (comp f f₂).map_zero

@[simp]
-/
theorem mapRange.linearMap_comp (f : N ->ₛₗ[σ₂₃] P) (f₂ : M ->ₛₗ[σ₁₂] N) :
    (mapRange.linearMap (f.comp f₂) : (α ->₀ _) ->ₛₗ[σ₁₃] _) =
      (mapRange.linearMap f).comp (mapRange.linearMap f₂) :=
LinearMap.ext mapRange_comp f f.map_zero f₂ f₂.map_zero (comp f f₂).map_zero

@[simp]
/--
theorem `mapRange.linearMap_toAddMonoidHom` / 定理 `mapRange.linearMap_toAddMonoidHom`

English:
theorem mapRange.linearMap_toAddMonoidHom
  given: (f : M ->ₛₗ[σ₁₂] N)
  proof: AddMonoidHom.ext fun _ => rfl

中文:
定理 mapRange.linearMap_toAddMonoidHom
  条件: (f : M ->ₛₗ[σ₁₂] N)
  证明: AddMonoidHom.ext fun _ => rfl

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ext
-/
theorem mapRange.linearMap_toAddMonoidHom (f : M ->ₛₗ[σ₁₂] N) :
    (mapRange.linearMap f).toAddMonoidHom =
      (mapRange.addMonoidHom f.toAddMonoidHom : (α ->₀ M) ->+ _) :=
  AddMonoidHom.ext fun _ => rfl

section Equiv

variable [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
variable [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
variable [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃]

/-- `Finsupp.mapRange` as a `LinearEquiv`. -/
@[simps apply]
/--
Definition of `mapRange.linearEquiv` / `mapRange.linearEquiv` 的定义

English:
definition mapRange.linearEquiv
  signature: (e : M ≃ₛₗ[σ₁₂] N)
  body: { mapRange.linearMap e.toLinearMap,
    mapRange.addEquiv e.toAddEquiv with
    toFun := mapRange e e.map_zero
    invFun := mapRange e.symm e.symm.map_zero }

@[simp]

中文:
定义 mapRange.linearEquiv
  签名: (e : M ≃ₛₗ[σ₁₂] N)
  定义体: { mapRange.linearMap e.toLinearMap,
    mapRange.addEquiv e.toAddEquiv with
    toFun := mapRange e e.map_zero
    invFun := mapRange e.symm e.symm.map_zero }

@[simp]

Depends on / 依赖: Set.diagonal, diagonal, measurability, simp_rw, singlePass, sub_eq_zero
-/
def mapRange.linearEquiv (e : M ≃ₛₗ[σ₁₂] N) : (α ->₀ M) ≃ₛₗ[σ₁₂] α ->₀ N :=
  { mapRange.linearMap e.toLinearMap,
    mapRange.addEquiv e.toAddEquiv with
    toFun := mapRange e e.map_zero
    invFun := mapRange e.symm e.symm.map_zero }

@[simp]
/--
theorem `mapRange.linearEquiv_refl` / 定理 `mapRange.linearEquiv_refl`

English:
theorem mapRange.linearEquiv_refl
  proof: LinearEquiv.ext mapRange_id

中文:
定理 mapRange.linearEquiv_refl
  证明: LinearEquiv.ext mapRange_id

Depends on / 依赖: Set.diagonal, diagonal, le_antisymm_iff, measurability, simp_rw, tsub_eq_zero_iff_le
-/
theorem mapRange.linearEquiv_refl :
    mapRange.linearEquiv (LinearEquiv.refl R M) = LinearEquiv.refl R (α ->₀ M) :=
  LinearEquiv.ext mapRange_id

/--
theorem `mapRange.linearEquiv_trans` / 定理 `mapRange.linearEquiv_trans`

English:
theorem mapRange.linearEquiv_trans
  given: (f : M ≃ₛₗ[σ₁₂] N) (f₂ : N ≃ₛₗ[σ₂₃] P)
  proof: LinearEquiv.ext mapRange_comp f₂ f₂.map_zero f f.map_zero (f.trans f₂).map_zero

@[simp]

中文:
定理 mapRange.linearEquiv_trans
  条件: (f : M ≃ₛₗ[σ₁₂] N) (f₂ : N ≃ₛₗ[σ₂₃] P)
  证明: LinearEquiv.ext mapRange_comp f₂ f₂.map_zero f f.map_zero (f.trans f₂).map_zero

@[simp]

Depends on / 依赖: MeasurableSpace, measurableDiv_of_mul_inv
-/
theorem mapRange.linearEquiv_trans (f : M ≃ₛₗ[σ₁₂] N) (f₂ : N ≃ₛₗ[σ₂₃] P) :
    (mapRange.linearEquiv (f.trans f₂) : (α ->₀ _) ≃ₛₗ[σ₁₃] _) =
      (mapRange.linearEquiv f).trans (mapRange.linearEquiv f₂) :=
LinearEquiv.ext mapRange_comp f₂ f₂.map_zero f f.map_zero (f.trans f₂).map_zero

@[simp]
/--
theorem `mapRange.linearEquiv_symm` / 定理 `mapRange.linearEquiv_symm`

English:
theorem mapRange.linearEquiv_symm
  given: (f : M ≃ₛₗ[σ₁₂] N)
  proof: LinearEquiv.ext fun _x => rfl

@[simp]

中文:
定理 mapRange.linearEquiv_symm
  条件: (f : M ≃ₛₗ[σ₁₂] N)
  证明: LinearEquiv.ext fun _x => rfl

@[simp]
-/
theorem mapRange.linearEquiv_symm (f : M ≃ₛₗ[σ₁₂] N) :
    ((mapRange.linearEquiv f).symm : (α ->₀ _) ≃ₛₗ[σ₂₁] _) = mapRange.linearEquiv f.symm :=
  LinearEquiv.ext fun _x => rfl

@[simp]
/--
theorem `mapRange.linearEquiv_toAddEquiv` / 定理 `mapRange.linearEquiv_toAddEquiv`

English:
theorem mapRange.linearEquiv_toAddEquiv
  given: (f : M ≃ₛₗ[σ₁₂] N)
  proof: AddEquiv.ext fun _ => rfl

@[simp]

中文:
定理 mapRange.linearEquiv_toAddEquiv
  条件: (f : M ≃ₛₗ[σ₁₂] N)
  证明: AddEquiv.ext fun _ => rfl

@[simp]

Depends on / 依赖: AddEquiv, AddEquiv.ext
-/
theorem mapRange.linearEquiv_toAddEquiv (f : M ≃ₛₗ[σ₁₂] N) :
    (mapRange.linearEquiv f).toAddEquiv = (mapRange.addEquiv f.toAddEquiv : (α ->₀ M) ≃+ _) :=
  AddEquiv.ext fun _ => rfl

@[simp]
/--
theorem `mapRange.linearEquiv_toLinearMap` / 定理 `mapRange.linearEquiv_toLinearMap`

English:
theorem mapRange.linearEquiv_toLinearMap
  given: (f : M ≃ₛₗ[σ₁₂] N)
  proof: LinearMap.ext fun _ => rfl

中文:
定理 mapRange.linearEquiv_toLinearMap
  条件: (f : M ≃ₛₗ[σ₁₂] N)
  证明: LinearMap.ext fun _ => rfl

Depends on / 依赖: LinearMap, LinearMap.ext
-/
theorem mapRange.linearEquiv_toLinearMap (f : M ≃ₛₗ[σ₁₂] N) :
    (mapRange.linearEquiv f).toLinearMap =
    (mapRange.linearMap f.toLinearMap : (α ->₀ M) ->ₛₗ[σ₁₂] _) :=
  LinearMap.ext fun _ => rfl

end Equiv

section Prod

variable {α β R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

variable (R) in
/-- The linear equivalence between `α × β →₀ M` and `α →₀ β →₀ M`.

This is the `LinearEquiv` version of `Finsupp.curryEquiv`. -/
@[simps +simpRhs]
/--
Definition of `curryLinearEquiv` / `curryLinearEquiv` 的定义

English:
definition curryLinearEquiv
  signature: : (α × β ->₀ M) ≃ₗ[R] α ->₀ β ->₀ M where
  body: curryAddEquiv
  map_smul' c f := by ext; simp

@[deprecated (since := "2026-01-03")] alias finsuppProdLEquiv := curryLinearEquiv

中文:
定义 curryLinearEquiv
  签名: : (α × β ->₀ M) ≃ₗ[R] α ->₀ β ->₀ M where
  定义体: curryAddEquiv
  map_smul' c f := by ext; simp

@[deprecated (since := "2026-01-03")] alias finsuppProdLEquiv := curryLinearEquiv

Depends on / 依赖: curryAddEquiv
-/
noncomputable def curryLinearEquiv : (α × β ->₀ M) ≃ₗ[R] α ->₀ β ->₀ M where
  toAddEquiv := curryAddEquiv
  map_smul' c f := by ext; simp

@[deprecated (since := "2026-01-03")] alias finsuppProdLEquiv := curryLinearEquiv

/--
theorem `curryLinearEquiv_symm_apply_apply` / 定理 `curryLinearEquiv_symm_apply_apply`

English:
theorem curryLinearEquiv_symm_apply_apply
  given: (f : α ->₀ β ->₀ M) (xy)
  proof: rfl

@[deprecated (since := "2026-01-03")]
alias finsuppProdLEquiv_symm_apply_apply := curryLinearEquiv_symm_apply_apply

中文:
定理 curryLinearEquiv_symm_apply_apply
  条件: (f : α ->₀ β ->₀ M) (xy)
  证明: rfl

@[deprecated (since := "2026-01-03")]
alias finsuppProdLEquiv_symm_apply_apply := curryLinearEquiv_symm_apply_apply
-/
theorem curryLinearEquiv_symm_apply_apply (f : α ->₀ β ->₀ M) (xy) :
    (curryLinearEquiv R).symm f xy = f xy.1 xy.2 :=
  rfl

@[deprecated (since := "2026-01-03")]
alias finsuppProdLEquiv_symm_apply_apply := curryLinearEquiv_symm_apply_apply

end Prod

end Finsupp

variable {R : Type*} {M : Type*} {N : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

open Finsupp

section

variable (R)

/-- If `Subsingleton R`, then `M ≃ₗ[R] ι →₀ R` for any type `ι`. -/
@[simps]
/--
Definition of `Module.subsingletonEquiv` / `Module.subsingletonEquiv` 的定义

English:
definition Module.subsingletonEquiv
  signature: (R M ι : Type*) [Semiring R] [Subsingleton R] [AddCommMonoid M]
  body: 0
  invFun _ := 0
  left_inv m :=
    have := Module.subsingleton R M
    Subsingleton.elim _ _
  right_inv f := by simp only [eq_iff_true_of_subsingleton]
  map_add' _ _ := (add_zero 0).symm
  map_smul' r _ := (smul_zero r).symm

中文:
定义 Module.subsingletonEquiv
  签名: (R M ι : 类型) [Semiring R] [Subsingleton R] [AddCommMonoid M]
  定义体: 0
  invFun _ := 0
  left_inv m :=
    have := Module.subsingleton R M
    Subsingleton.elim _ _
  right_inv f := by simp only [eq_iff_true_of_subsingleton]
  map_add' _ _ := (add_zero 0).symm
  map_smul' r _ := (smul_zero r).symm
-/
def Module.subsingletonEquiv (R M ι : Type*) [Semiring R] [Subsingleton R] [AddCommMonoid M]
    [Module R M] : M ≃ₗ[R] ι ->₀ R where
  toFun _ := 0
  invFun _ := 0
  left_inv m :=
    have := Module.subsingleton R M
    Subsingleton.elim _ _
  right_inv f := by simp only [eq_iff_true_of_subsingleton]
  map_add' _ _ := (add_zero 0).symm
  map_smul' r _ := (smul_zero r).symm

end

namespace Module.End

variable (ι : Type*) {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/--
Definition of `ringHomEndFinsupp` / `ringHomEndFinsupp` 的定义

English:
definition ringHomEndFinsupp
  signature: :
  body: { toFun := Finsupp.mapRange.addMonoidHom f
    map_add' := map_add _
    map_smul' g x := x.induction_linear (by simp)
      (fun _ _ h h' => by rw [smul_add, map_add, h, h', map_add, smul_add]) fun i m => by
        ext j
        change f (Finsupp.lapply j ∘ₗ g ∘ₗ Finsupp.lsingle i • m) = _
       

中文:
定义 ringHomEndFinsupp
  签名: :
  定义体: { toFun := Finsupp.mapRange.addMonoidHom f
    map_add' := map_add _
    map_smul' g x := x.induction_linear (by simp)
      (fun _ _ h h' => by rw [smul_add, map_add, h, h', map_add, smul_add]) fun i m => by
        ext j
        change f (Finsupp.lapply j ∘ₗ g ∘ₗ Finsupp.lsingle i • m) = _
       
-/
@[simps] noncomputable def ringHomEndFinsupp :
    End (End R M) M ->+* End (End R (ι ->₀ M)) (ι ->₀ M) where
  toFun f :=
  { toFun := Finsupp.mapRange.addMonoidHom f
    map_add' := map_add _
    map_smul' g x := x.induction_linear (by simp)
      (fun _ _ h h' => by rw [smul_add, map_add, h, h', map_add, smul_add]) fun i m => by
        ext j
        change f (Finsupp.lapply j ∘ₗ g ∘ₗ Finsupp.lsingle i • m) = _
        rw [map_smul]
        simp }
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

variable {ι}

/--
Definition of `ringEquivEndFinsupp` / `ringEquivEndFinsupp` 的定义

English:
definition ringEquivEndFinsupp
  signature: (i : ι)
  body: ringHomEndFinsupp ι
  invFun f :=
  { toFun m := f (Finsupp.single i m) i
    map_add' _ _ := by simp
    map_smul' g m := let g := Finsupp.mapRange.linearMap g
      show _ = g _ i by rw [← End.smul_def g, ← map_smul]; simp [g] }
  left_inv _ := by ext; simp
  right_inv f := by
    ext x j
    chan

中文:
定义 ringEquivEndFinsupp
  签名: (i : ι)
  定义体: ringHomEndFinsupp ι
  invFun f :=
  { toFun m := f (Finsupp.single i m) i
    map_add' _ _ := by simp
    map_smul' g m := let g := Finsupp.mapRange.linearMap g
      show _ = g _ i by rw [← End.smul_def g, ← map_smul]; simp [g] }
  left_inv _ := by ext; simp
  right_inv f := by
    ext x j
    chan
-/
@[simps!] noncomputable def ringEquivEndFinsupp (i : ι) :
    End (End R M) M ≃+* End (End R (ι ->₀ M)) (ι ->₀ M) where
  __ := ringHomEndFinsupp ι
  invFun f :=
  { toFun m := f (Finsupp.single i m) i
    map_add' _ _ := by simp
    map_smul' g m := let g := Finsupp.mapRange.linearMap g
      show _ = g _ i by rw [← End.smul_def g, ← map_smul]; simp [g] }
  left_inv _ := by ext; simp
  right_inv f := by
    ext x j
    change f (Finsupp.lsingle (R := R) (M := M) i ∘ₗ Finsupp.lapply j • x) i = _
    rw [map_smul]
    simp

variable (R M ι)

/--
theorem `ringHomEndFinsupp_surjective` / 定理 `ringHomEndFinsupp_surjective`

English:
theorem ringHomEndFinsupp_surjective
  proof: by
  intro f
  obtain _ | ⟨⟨i⟩⟩ := isEmpty_or_nonempty ι
  · exact ⟨0, Subsingleton.elim ..⟩
  · exact ⟨_, (ringEquivEndFinsupp i).right_inv f⟩

中文:
定理 ringHomEndFinsupp_surjective
  证明: by
  intro f
  obtain _ | ⟨⟨i⟩⟩ := isEmpty_or_nonempty ι
  · exact ⟨0, Subsingleton.elim ..⟩
  · exact ⟨_, (ringEquivEndFinsupp i).right_inv f⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, isEmpty_or_nonempty, right_inv, ringEquivEndFinsupp
-/
theorem ringHomEndFinsupp_surjective :
    Function.Surjective (ringHomEndFinsupp (R := R) (M := M) ι) := by
  intro f
  obtain _ | ⟨⟨i⟩⟩ := isEmpty_or_nonempty ι
  · exact ⟨0, Subsingleton.elim ..⟩
  · exact ⟨_, (ringEquivEndFinsupp i).right_inv f⟩

end Module.End
