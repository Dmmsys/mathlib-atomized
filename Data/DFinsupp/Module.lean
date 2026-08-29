/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.DFinsupp.Defs

/-!
# Group actions on `DFinsupp`

## Main results

* `DFinsupp.module`: pointwise scalar multiplication on `DFinsupp` gives a module structure
-/

@[expose] public section

universe u u₁ u₂ v v₁ v₂ v₃ w x y l

variable {ι : Type u} {γ : Type w} {β : ι -> Type v} {β₁ : ι -> Type v₁} {β₂ : ι -> Type v₂}

namespace DFinsupp

section Algebra

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, Zero (β i)] [forall i, SMulZeroClass γ (β i)] : SMulZeroClass γ (Π₀ i, β i) where
  body: v.mapRange (fun _ => (c • ·)) fun _ => smul_zero _
  smul_zero _ := mapRange_zero _ _

中文:
实例 [forall
  签名: i, Zero (β i)] [对任意 i, SMulZeroClass γ (β i)] : SMulZeroClass γ (Π₀ i, β i) where
  定义体: v.mapRange (fun _ => (c • ·)) fun _ => smul_zero _
  smul_zero _ := mapRange_zero _ _

Depends on / 依赖: mapRange, smul_zero, v.mapRange
-/
instance [forall i, Zero (β i)] [forall i, SMulZeroClass γ (β i)] : SMulZeroClass γ (Π₀ i, β i) where
  smul c v := v.mapRange (fun _ => (c • ·)) fun _ => smul_zero _
  smul_zero _ := mapRange_zero _ _

/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  statement: [forall i, Zero (β i)] [forall i, SMulZeroClass γ (β i)] (b : γ)
  proof: rfl

@[simp, norm_cast]

中文:
定理 smul_apply
  结论: [对任意 i, Zero (β i)] [对任意 i, SMulZeroClass γ (β i)] (b : γ)
  证明: rfl

@[simp, norm_cast]
-/
theorem smul_apply [forall i, Zero (β i)] [forall i, SMulZeroClass γ (β i)] (b : γ)
    (v : Π₀ i, β i) (i : ι) : (b • v) i = b • v i :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  statement: [forall i, Zero (β i)] [forall i, SMulZeroClass γ (β i)] (b : γ)
  proof: rfl

中文:
定理 coe_smul
  结论: [对任意 i, Zero (β i)] [对任意 i, SMulZeroClass γ (β i)] (b : γ)
  证明: rfl
-/
theorem coe_smul [forall i, Zero (β i)] [forall i, SMulZeroClass γ (β i)] (b : γ)
    (v : Π₀ i, β i) : ⇑(b • v) = b • ⇑v :=
  rfl

/--
Instance `smulCommClass` / 实例 `smulCommClass`

English:
instance smulCommClass
  signature: {δ : Type*} [forall i, Zero (β i)]
  body: ext fun i => by simp only [smul_apply, smul_comm r s (m i)]

中文:
实例 smulCommClass
  签名: {δ : 类型} [对任意 i, Zero (β i)]
  定义体: ext fun i => by simp only [smul_apply, smul_comm r s (m i)]

Depends on / 依赖: smul_apply, smul_comm
-/
instance smulCommClass {δ : Type*} [forall i, Zero (β i)]
    [forall i, SMulZeroClass γ (β i)] [forall i, SMulZeroClass δ (β i)] [forall i, SMulCommClass γ δ (β i)] :
    SMulCommClass γ δ (Π₀ i, β i) where
  smul_comm r s m := ext fun i => by simp only [smul_apply, smul_comm r s (m i)]

/--
Instance `isScalarTower` / 实例 `isScalarTower`

English:
instance isScalarTower
  signature: {δ : Type*} [forall i, Zero (β i)]
  body: ext fun i => by simp only [smul_apply, smul_assoc r s (m i)]

中文:
实例 isScalarTower
  签名: {δ : 类型} [对任意 i, Zero (β i)]
  定义体: ext fun i => by simp only [smul_apply, smul_assoc r s (m i)]

Depends on / 依赖: smul_apply, smul_assoc
-/
instance isScalarTower {δ : Type*} [forall i, Zero (β i)]
    [forall i, SMulZeroClass γ (β i)] [forall i, SMulZeroClass δ (β i)] [SMul γ δ]
    [forall i, IsScalarTower γ δ (β i)] : IsScalarTower γ δ (Π₀ i, β i) where
  smul_assoc r s m := ext fun i => by simp only [smul_apply, smul_assoc r s (m i)]

/--
Instance `isCentralScalar` / 实例 `isCentralScalar`

English:
instance isCentralScalar
  signature: [forall i, Zero (β i)] [forall i, SMulZeroClass γ (β i)]
  body: ext fun i => by simp only [smul_apply, op_smul_eq_smul r (m i)]

中文:
实例 isCentralScalar
  签名: [对任意 i, Zero (β i)] [对任意 i, SMulZeroClass γ (β i)]
  定义体: ext fun i => by simp only [smul_apply, op_smul_eq_smul r (m i)]

Depends on / 依赖: op_smul_eq_smul, smul_apply
-/
instance isCentralScalar [forall i, Zero (β i)] [forall i, SMulZeroClass γ (β i)]
    [forall i, SMulZeroClass γᵐᵒᵖ (β i)] [forall i, IsCentralScalar γ (β i)] :
    IsCentralScalar γ (Π₀ i, β i) where
  op_smul_eq_smul r m := ext fun i => by simp only [smul_apply, op_smul_eq_smul r (m i)]

/--
Instance `distribMulAction` / 实例 `distribMulAction`

English:
instance distribMulAction
  signature: [Monoid γ] [forall i, AddMonoid (β i)] [forall i, DistribMulAction γ (β i)]
  body: Function.Injective.distribMulAction coeFnAddMonoidHom DFunLike.coe_injective coe_smul

中文:
实例 distribMulAction
  签名: [Monoid γ] [对任意 i, AddMonoid (β i)] [对任意 i, DistribMulAction γ (β i)]
  定义体: Function.Injective.distribMulAction coeFnAddMonoidHom DFunLike.coe_injective coe_smul

Depends on / 依赖: DFunLike, DFunLike.coe_injective, Function, Function.Injective.distribMulAction, Injective, coeFnAddMonoidHom, coe_injective, coe_smul, distribMulAction
-/
instance distribMulAction [Monoid γ] [forall i, AddMonoid (β i)] [forall i, DistribMulAction γ (β i)] :
    DistribMulAction γ (Π₀ i, β i) :=
  Function.Injective.distribMulAction coeFnAddMonoidHom DFunLike.coe_injective coe_smul

/--
Instance `module` / 实例 `module`

English:
instance module
  signature: [Semiring γ] [forall i, AddCommMonoid (β i)] [forall i, Module γ (β i)]
  body: { (inferInstance : DistribMulAction γ (Π₀ i, β i)) with
    zero_smul := fun c => ext fun i => by simp only [smul_apply, zero_smul, zero_apply]
    add_smul := fun c x y => ext fun i => by simp only [add_apply, smul_apply, add_smul] }

中文:
实例 module
  签名: [Semiring γ] [对任意 i, AddCommMonoid (β i)] [对任意 i, Module γ (β i)]
  定义体: { (inferInstance : DistribMulAction γ (Π₀ i, β i)) with
    zero_smul := fun c => ext fun i => by simp only [smul_apply, zero_smul, zero_apply]
    add_smul := fun c x y => ext fun i => by simp only [add_apply, smul_apply, add_smul] }

Depends on / 依赖: DistribMulAction, add_apply, add_smul, smul_apply, zero_apply, zero_smul
-/
instance module [Semiring γ] [forall i, AddCommMonoid (β i)] [forall i, Module γ (β i)] :
    Module γ (Π₀ i, β i) :=
  { (inferInstance : DistribMulAction γ (Π₀ i, β i)) with
    zero_smul := fun c => ext fun i => by simp only [smul_apply, zero_smul, zero_apply]
    add_smul := fun c x y => ext fun i => by simp only [add_apply, smul_apply, add_smul] }

end Algebra

variable (γ) in
/--
Definition of `coeFnLinearMap` / `coeFnLinearMap` 的定义

English:
definition coeFnLinearMap
  signature: [Semiring γ] [forall i, AddCommMonoid (β i)] [forall i, Module γ (β i)]
  body: (⇑)
  map_add' := coe_add
  map_smul' := coe_smul

@[simp]

中文:
定义 coeFnLinearMap
  签名: [Semiring γ] [对任意 i, AddCommMonoid (β i)] [对任意 i, Module γ (β i)]
  定义体: (⇑)
  map_add' := coe_add
  map_smul' := coe_smul

@[simp]
-/
def coeFnLinearMap [Semiring γ] [forall i, AddCommMonoid (β i)] [forall i, Module γ (β i)] :
    (Π₀ i, β i) ->ₗ[γ] forall i, β i where
  toFun := (⇑)
  map_add' := coe_add
  map_smul' := coe_smul

@[simp]
/--
lemma `coeFnLinearMap_apply` / 引理 `coeFnLinearMap_apply`

English:
lemma coeFnLinearMap_apply
  statement: [Semiring γ] [forall i, AddCommMonoid (β i)] [forall i, Module γ (β i)]
  proof: rfl

中文:
引理 coeFnLinearMap_apply
  结论: [Semiring γ] [对任意 i, AddCommMonoid (β i)] [对任意 i, Module γ (β i)]
  证明: rfl
-/
lemma coeFnLinearMap_apply [Semiring γ] [forall i, AddCommMonoid (β i)] [forall i, Module γ (β i)]
    (v : Π₀ i, β i) : coeFnLinearMap γ v = v :=
  rfl

section FilterAndSubtypeDomain

@[simp]
/--
theorem `filter_smul` / 定理 `filter_smul`

English:
theorem filter_smul
  statement: [forall i, Zero (β i)] [forall i, SMulZeroClass γ (β i)] (p : ι -> Prop)
  proof: by
  ext
  simp [smul_apply, smul_ite]

中文:
定理 filter_smul
  结论: [对任意 i, Zero (β i)] [对任意 i, SMulZeroClass γ (β i)] (p : ι -> 命题)
  证明: by
  ext
  simp [smul_apply, smul_ite]

Depends on / 依赖: smul_apply, smul_ite
-/
theorem filter_smul [forall i, Zero (β i)] [forall i, SMulZeroClass γ (β i)] (p : ι -> Prop)
    [DecidablePred p] (r : γ) (f : Π₀ i, β i) : (r • f).filter p = r • f.filter p := by
  ext
  simp [smul_apply, smul_ite]

variable (γ β)

/-- `DFinsupp.filter` as a `LinearMap`. -/
@[simps]
/--
Definition of `filterLinearMap` / `filterLinearMap` 的定义

English:
definition filterLinearMap
  signature: [Semiring γ] [forall i, AddCommMonoid (β i)] [forall i, Module γ (β i)] (p : ι -> Prop)
  body: filter p
  map_add' := filter_add p
  map_smul' := filter_smul p

中文:
定义 filterLinearMap
  签名: [Semiring γ] [对任意 i, AddCommMonoid (β i)] [对任意 i, Module γ (β i)] (p : ι -> 命题)
  定义体: filter p
  map_add' := filter_add p
  map_smul' := filter_smul p

Depends on / 依赖: filter
-/
def filterLinearMap [Semiring γ] [forall i, AddCommMonoid (β i)] [forall i, Module γ (β i)] (p : ι -> Prop)
    [DecidablePred p] : (Π₀ i, β i) ->ₗ[γ] Π₀ i, β i where
  toFun := filter p
  map_add' := filter_add p
  map_smul' := filter_smul p

variable {γ β}

@[simp]
/--
theorem `subtypeDomain_smul` / 定理 `subtypeDomain_smul`

English:
theorem subtypeDomain_smul
  statement: [forall i, Zero (β i)] [forall i, SMulZeroClass γ (β i)]
  proof: DFunLike.coe_injective rfl

中文:
定理 subtypeDomain_smul
  结论: [对任意 i, Zero (β i)] [对任意 i, SMulZeroClass γ (β i)]
  证明: DFunLike.coe_injective rfl

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem subtypeDomain_smul [forall i, Zero (β i)] [forall i, SMulZeroClass γ (β i)]
    {p : ι -> Prop} [DecidablePred p] (r : γ) (f : Π₀ i, β i) :
    (r • f).subtypeDomain p = r • f.subtypeDomain p :=
  DFunLike.coe_injective rfl

variable (γ β)

/-- `DFinsupp.subtypeDomain` as a `LinearMap`. -/
@[simps]
/--
Definition of `subtypeDomainLinearMap` / `subtypeDomainLinearMap` 的定义

English:
definition subtypeDomainLinearMap
  signature: [Semiring γ] [forall i, AddCommMonoid (β i)] [forall i, Module γ (β i)]
  body: subtypeDomain p
  map_add' := subtypeDomain_add
  map_smul' := subtypeDomain_smul

中文:
定义 subtypeDomainLinearMap
  签名: [Semiring γ] [对任意 i, AddCommMonoid (β i)] [对任意 i, Module γ (β i)]
  定义体: subtypeDomain p
  map_add' := subtypeDomain_add
  map_smul' := subtypeDomain_smul

Depends on / 依赖: subtypeDomain
-/
def subtypeDomainLinearMap [Semiring γ] [forall i, AddCommMonoid (β i)] [forall i, Module γ (β i)]
    (p : ι -> Prop) [DecidablePred p] : (Π₀ i, β i) ->ₗ[γ] Π₀ i : Subtype p, β i where
  toFun := subtypeDomain p
  map_add' := subtypeDomain_add
  map_smul' := subtypeDomain_smul

end FilterAndSubtypeDomain

section DecidableEq
variable [DecidableEq ι]

section

variable [forall i, Zero (β i)] [forall i, SMulZeroClass γ (β i)]

@[simp]
/--
theorem `mk_smul` / 定理 `mk_smul`

English:
theorem mk_smul
  given: {s : Finset ι} (c : γ) (x : forall i : (↑s : Set ι), β (i : ι))
  proof: ext fun i => by simp only [smul_apply, mk_apply]; split_ifs <;> [rfl; rw [smul_zero]]

@[simp]

中文:
定理 mk_smul
  条件: {s : Finset ι} (c : γ) (x : 对任意 i : (↑s : Set ι), β (i : ι))
  证明: ext fun i => by simp only [smul_apply, mk_apply]; split_ifs <;> [rfl; rw [smul_zero]]

@[simp]

Depends on / 依赖: mk_apply, smul_apply, smul_zero, split_ifs
-/
theorem mk_smul {s : Finset ι} (c : γ) (x : forall i : (↑s : Set ι), β (i : ι)) :
    mk s (c • x) = c • mk s x :=
  ext fun i => by simp only [smul_apply, mk_apply]; split_ifs <;> [rfl; rw [smul_zero]]

@[simp]
/--
theorem `single_smul` / 定理 `single_smul`

English:
theorem single_smul
  given: {i : ι} (c : γ) (x : β i)
  statement: single i (c • x) = c • single i x
  proof: ext fun i => by
    simp only [smul_apply, single_apply]
    split_ifs with h
    · cases h; rfl
    · rw [smul_zero]

中文:
定理 single_smul
  条件: {i : ι} (c : γ) (x : β i)
  结论: single i (c • x) = c • single i x
  证明: ext fun i => by
    simp only [smul_apply, single_apply]
    split_ifs with h
    · cases h; rfl
    · rw [smul_zero]

Depends on / 依赖: single_apply, smul_apply, smul_zero, split_ifs
-/
theorem single_smul {i : ι} (c : γ) (x : β i) : single i (c • x) = c • single i x :=
  ext fun i => by
    simp only [smul_apply, single_apply]
    split_ifs with h
    · cases h; rfl
    · rw [smul_zero]

end

/--
theorem `support_smul` / 定理 `support_smul`

English:
theorem support_smul
  statement: {γ : Type w} [forall i, Zero (β i)] [forall i, SMulZeroClass γ (β i)]
  proof: support_mapRange

中文:
定理 support_smul
  结论: {γ : Type w} [对任意 i, Zero (β i)] [对任意 i, SMulZeroClass γ (β i)]
  证明: support_mapRange

Depends on / 依赖: support_mapRange
-/
theorem support_smul {γ : Type w} [forall i, Zero (β i)] [forall i, SMulZeroClass γ (β i)]
    [forall (i : ι) (x : β i), Decidable (x != 0)] (b : γ) (v : Π₀ i, β i) :
    (b • v).support subseteq v.support :=
  support_mapRange

end DecidableEq

section Equiv

open Finset

variable {κ : Type*}

@[simp]
/--
theorem `comapDomain_smul` / 定理 `comapDomain_smul`

English:
theorem comapDomain_smul
  statement: [forall i, Zero (β i)] [forall i, SMulZeroClass γ (β i)]
  proof: by
  ext
  rw [smul_apply]; rw [comapDomain_apply]; rw [smul_apply]; rw [comapDomain_apply]

@[simp]

中文:
定理 comapDomain_smul
  结论: [对任意 i, Zero (β i)] [对任意 i, SMulZeroClass γ (β i)]
  证明: by
  ext
  rw [smul_apply]; rw [comapDomain_apply]; rw [smul_apply]; rw [comapDomain_apply]

@[simp]

Depends on / 依赖: comapDomain_apply, smul_apply
-/
theorem comapDomain_smul [forall i, Zero (β i)] [forall i, SMulZeroClass γ (β i)]
    (h : κ -> ι) (hh : Function.Injective h) (r : γ) (f : Π₀ i, β i) :
    comapDomain h hh (r • f) = r • comapDomain h hh f := by
  ext
  rw [smul_apply]; rw [comapDomain_apply]; rw [smul_apply]; rw [comapDomain_apply]

@[simp]
/--
theorem `comapDomain'_smul` / 定理 `comapDomain'_smul`

English:
theorem comapDomain'_smul
  statement: [forall i, Zero (β i)] [forall i, SMulZeroClass γ (β i)]
  proof: by
  ext
  rw [smul_apply]; rw [comapDomain'_apply]; rw [smul_apply]; rw [comapDomain'_apply]

中文:
定理 comapDomain'_smul
  结论: [对任意 i, Zero (β i)] [对任意 i, SMulZeroClass γ (β i)]
  证明: by
  ext
  rw [smul_apply]; rw [comapDomain'_apply]; rw [smul_apply]; rw [comapDomain'_apply]
-/
theorem comapDomain'_smul [forall i, Zero (β i)] [forall i, SMulZeroClass γ (β i)]
    (h : κ -> ι) {h' : ι -> κ} (hh' : Function.LeftInverse h' h) (r : γ) (f : Π₀ i, β i) :
    comapDomain' h hh' (r • f) = r • comapDomain' h hh' f := by
  ext
  rw [smul_apply]; rw [comapDomain'_apply]; rw [smul_apply]; rw [comapDomain'_apply]

section SigmaCurry

variable {α : ι -> Type*} {δ : forall i, α i -> Type v}

/--
Instance `distribMulAction₂` / 实例 `distribMulAction₂`

English:
instance distribMulAction₂
  signature: [Monoid γ] [forall i j, AddMonoid (δ i j)]
  body: @DFinsupp.distribMulAction ι _ (fun i => Π₀ j, δ i j) _ _ _

中文:
实例 distribMulAction₂
  签名: [Monoid γ] [对任意 i j, AddMonoid (δ i j)]
  定义体: @DFinsupp.distribMulAction ι _ (fun i => Π₀ j, δ i j) _ _ _

Depends on / 依赖: DFinsupp, DFinsupp.distribMulAction, distribMulAction
-/
instance distribMulAction₂ [Monoid γ] [forall i j, AddMonoid (δ i j)]
    [forall i j, DistribMulAction γ (δ i j)] : DistribMulAction γ (Π₀ (i : ι) (j : α i), δ i j) :=
  @DFinsupp.distribMulAction ι _ (fun i => Π₀ j, δ i j) _ _ _

end SigmaCurry

variable {α : Option ι -> Type v}

/--
theorem `equivProdDFinsupp_smul` / 定理 `equivProdDFinsupp_smul`

English:
theorem equivProdDFinsupp_smul
  statement: [forall i, Zero (α i)] [forall i, SMulZeroClass γ (α i)]
  proof: Prod.ext (smul_apply _ _ _) (comapDomain_smul _ (Option.some_injective _) _ _)

中文:
定理 equivProdDFinsupp_smul
  结论: [对任意 i, Zero (α i)] [对任意 i, SMulZeroClass γ (α i)]
  证明: Prod.ext (smul_apply _ _ _) (comapDomain_smul _ (Option.some_injective _) _ _)

Depends on / 依赖: Option.some_injective, Prod.ext, comapDomain_smul, smul_apply, some_injective
-/
theorem equivProdDFinsupp_smul [forall i, Zero (α i)] [forall i, SMulZeroClass γ (α i)]
    (r : γ) (f : Π₀ i, α i) : equivProdDFinsupp (r • f) = r • equivProdDFinsupp f :=
  Prod.ext (smul_apply _ _ _) (comapDomain_smul _ (Option.some_injective _) _ _)

end Equiv

end DFinsupp
