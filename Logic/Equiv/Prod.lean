/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Tactic.Contrapose

/-!
# Equivalence between product types

In this file we continue the work on equivalences begun in `Mathlib/Logic/Equiv/Defs.lean`,
focusing on product types.

## Main definitions

  - `Equiv.prodCongr ea eb : α₁ × β₁ ≃ α₂ × β₂`: combine two equivalences `ea : α₁ ≃ α₂` and
    `eb : β₁ ≃ β₂` using `Prod.map`.

## Tags

equivalence, congruence, bijective map
-/

@[expose] public section

open Function

universe u

-- Unless required to be `Type*`, all variables in this file are `Sort*`
variable {α α₁ α₂ β β₁ β₂ γ δ : Sort*}

namespace Equiv

/-- `PProd α β` is equivalent to `α × β` -/
@[simps (attr := grind =) apply symm_apply]
/--
Definition of `pprodEquivProd` / `pprodEquivProd` 的定义

English:
definition pprodEquivProd
  signature: {α β}
  body: (x.1, x.2)
  invFun x := ⟨x.1, x.2⟩

中文:
定义 pprodEquivProd
  签名: {α β}
  定义体: (x.1, x.2)
  invFun x := ⟨x.1, x.2⟩
-/
def pprodEquivProd {α β} : PProd α β ≃ α × β where
  toFun x := (x.1, x.2)
  invFun x := ⟨x.1, x.2⟩

/-- Product of two equivalences, in terms of `PProd`. If `α ≃ β` and `γ ≃ δ`, then
`PProd α γ ≃ PProd β δ`. -/
@[simps (attr := grind =) apply symm_apply]
/--
Definition of `pprodCongr` / `pprodCongr` 的定义

English:
definition pprodCongr
  signature: (e₁ : α ≃ β) (e₂ : γ ≃ δ)
  body: ⟨e₁ x.1, e₂ x.2⟩
  invFun x := ⟨e₁.symm x.1, e₂.symm x.2⟩
  left_inv := by grind
  right_inv := by grind

中文:
定义 pprodCongr
  签名: (e₁ : α ≃ β) (e₂ : γ ≃ δ)
  定义体: ⟨e₁ x.1, e₂ x.2⟩
  invFun x := ⟨e₁.symm x.1, e₂.symm x.2⟩
  left_inv := by grind
  right_inv := by grind
-/
def pprodCongr (e₁ : α ≃ β) (e₂ : γ ≃ δ) : PProd α γ ≃ PProd β δ where
  toFun x := ⟨e₁ x.1, e₂ x.2⟩
  invFun x := ⟨e₁.symm x.1, e₂.symm x.2⟩
  left_inv := by grind
  right_inv := by grind

/-- Combine two equivalences using `PProd` in the domain and `Prod` in the codomain. -/
@[simps! (attr := grind =) apply symm_apply]
/--
Definition of `pprodProd` / `pprodProd` 的定义

English:
definition pprodProd
  signature: {α₂ β₂} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂)
  body: (ea.pprodCongr eb).trans pprodEquivProd

中文:
定义 pprodProd
  签名: {α₂ β₂} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂)
  定义体: (ea.pprodCongr eb).trans pprodEquivProd

Depends on / 依赖: ea.pprodCongr, pprodCongr, pprodEquivProd
-/
def pprodProd {α₂ β₂} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) :
    PProd α₁ β₁ ≃ α₂ × β₂ :=
  (ea.pprodCongr eb).trans pprodEquivProd

/-- Combine two equivalences using `PProd` in the codomain and `Prod` in the domain. -/
@[simps! (attr := grind =) apply symm_apply]
/--
Definition of `prodPProd` / `prodPProd` 的定义

English:
definition prodPProd
  signature: {α₁ β₁} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂)
  body: (ea.symm.pprodProd eb.symm).symm

中文:
定义 prodPProd
  签名: {α₁ β₁} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂)
  定义体: (ea.symm.pprodProd eb.symm).symm

Depends on / 依赖: ea.symm.pprodProd, eb.symm, pprodProd
-/
def prodPProd {α₁ β₁} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) :
    α₁ × β₁ ≃ PProd α₂ β₂ :=
  (ea.symm.pprodProd eb.symm).symm

/-- `PProd α β` is equivalent to `PLift α × PLift β` -/
@[simps! (attr := grind =) apply symm_apply]
/--
Definition of `pprodEquivProdPLift` / `pprodEquivProdPLift` 的定义

English:
definition pprodEquivProdPLift
  signature: : PProd α β ≃ PLift α × PLift β
  body: Equiv.plift.symm.pprodProd Equiv.plift.symm

中文:
定义 pprodEquivProdPLift
  签名: : 命题积类型 α β ≃ 命题层提升 α × 命题层提升 β
  定义体: Equiv.plift.symm.pprodProd Equiv.plift.symm

Depends on / 依赖: Equiv.plift.symm, Equiv.plift.symm.pprodProd, pprodProd
-/
def pprodEquivProdPLift : PProd α β ≃ PLift α × PLift β :=
  Equiv.plift.symm.pprodProd Equiv.plift.symm

/-- Product of two equivalences. If `α₁ ≃ α₂` and `β₁ ≃ β₂`, then `α₁ × β₁ ≃ α₂ × β₂`. This is
`Prod.map` as an equivalence. -/
@[simps (attr := grind =) -fullyApplied apply]
/--
Definition of `prodCongr` / `prodCongr` 的定义

English:
definition prodCongr
  signature: {α₁ α₂ β₁ β₂} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂)
  body: ⟨Prod.map e₁ e₂, Prod.map e₁.symm e₂.symm, fun ⟨a, b⟩ => by simp, fun ⟨a, b⟩ => by simp⟩

@[simp, grind =]

中文:
定义 prodCongr
  签名: {α₁ α₂ β₁ β₂} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂)
  定义体: ⟨Prod.map e₁ e₂, Prod.map e₁.symm e₂.symm, fun ⟨a, b⟩ => by simp, fun ⟨a, b⟩ => by simp⟩

@[simp, grind =]

Depends on / 依赖: Prod.map
-/
def prodCongr {α₁ α₂ β₁ β₂} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) : α₁ × β₁ ≃ α₂ × β₂ :=
  ⟨Prod.map e₁ e₂, Prod.map e₁.symm e₂.symm, fun ⟨a, b⟩ => by simp, fun ⟨a, b⟩ => by simp⟩

@[simp, grind =]
/--
theorem `prodCongr_symm` / 定理 `prodCongr_symm`

English:
theorem prodCongr_symm
  given: {α₁ α₂ β₁ β₂} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂)
  proof: rfl

中文:
定理 prodCongr_symm
  条件: {α₁ α₂ β₁ β₂} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂)
  证明: rfl
-/
theorem prodCongr_symm {α₁ α₂ β₁ β₂} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
    (prodCongr e₁ e₂).symm = prodCongr e₁.symm e₂.symm :=
  rfl

/--
Definition of `prodComm` / `prodComm` 的定义

English:
definition prodComm
  signature: (α β)
  body: Prod.swap
  invFun := Prod.swap

@[simp]

中文:
定义 prodComm
  签名: (α β)
  定义体: Prod.swap
  invFun := Prod.swap

@[simp]

Depends on / 依赖: Prod.swap
-/
def prodComm (α β) : α × β ≃ β × α where
  toFun := Prod.swap
  invFun := Prod.swap

@[simp]
/--
theorem `coe_prodComm` / 定理 `coe_prodComm`

English:
theorem coe_prodComm
  given: (α β)
  statement: (⇑(prodComm α β) : α × β -> β × α) = Prod.swap
  proof: rfl

@[simp, grind =]

中文:
定理 coe_prodComm
  条件: (α β)
  结论: (⇑(prodComm α β) : α × β -> β × α) = 积类型.swap
  证明: rfl

@[simp, grind =]
-/
theorem coe_prodComm (α β) : (⇑(prodComm α β) : α × β -> β × α) = Prod.swap :=
  rfl

@[simp, grind =]
/--
theorem `prodComm_apply` / 定理 `prodComm_apply`

English:
theorem prodComm_apply
  given: {α β} (x : α × β)
  statement: prodComm α β x = x.swap
  proof: rfl

@[simp, grind =]

中文:
定理 prodComm_apply
  条件: {α β} (x : α × β)
  结论: prodComm α β x = x.swap
  证明: rfl

@[simp, grind =]
-/
theorem prodComm_apply {α β} (x : α × β) : prodComm α β x = x.swap :=
  rfl

@[simp, grind =]
/--
theorem `prodComm_symm` / 定理 `prodComm_symm`

English:
theorem prodComm_symm
  given: (α β)
  statement: (prodComm α β).symm = prodComm β α
  proof: rfl

中文:
定理 prodComm_symm
  条件: (α β)
  结论: (prodComm α β).symm = prodComm β α
  证明: rfl
-/
theorem prodComm_symm (α β) : (prodComm α β).symm = prodComm β α :=
  rfl

/-- Type product is associative up to an equivalence. -/
@[simps (attr := grind =)]
/--
Definition of `prodAssoc` / `prodAssoc` 的定义

English:
definition prodAssoc
  signature: (α β γ)
  body: ⟨fun p => (p.1.1, p.1.2, p.2), fun p => ((p.1, p.2.1), p.2.2), fun ⟨⟨_, _⟩, _⟩ => rfl,
    fun ⟨_, ⟨_, _⟩⟩ => rfl⟩

中文:
定义 prodAssoc
  签名: (α β γ)
  定义体: ⟨fun p => (p.1.1, p.1.2, p.2), fun p => ((p.1, p.2.1), p.2.2), fun ⟨⟨_, _⟩, _⟩ => rfl,
    fun ⟨_, ⟨_, _⟩⟩ => rfl⟩
-/
def prodAssoc (α β γ) : (α × β) × γ ≃ α × β × γ :=
  ⟨fun p => (p.1.1, p.1.2, p.2), fun p => ((p.1, p.2.1), p.2.2), fun ⟨⟨_, _⟩, _⟩ => rfl,
    fun ⟨_, ⟨_, _⟩⟩ => rfl⟩

/-- Four-way commutativity of `prod`. The name matches `mul_mul_mul_comm`. -/
@[simps (attr := grind =) apply]
/--
Definition of `prodProdProdComm` / `prodProdProdComm` 的定义

English:
definition prodProdProdComm
  signature: (α β γ δ)
  body: ((abcd.1.1, abcd.2.1), (abcd.1.2, abcd.2.2))
  invFun acbd := ((acbd.1.1, acbd.2.1), (acbd.1.2, acbd.2.2))

@[simp, grind =]

中文:
定义 prodProdProdComm
  签名: (α β γ δ)
  定义体: ((abcd.1.1, abcd.2.1), (abcd.1.2, abcd.2.2))
  invFun acbd := ((acbd.1.1, acbd.2.1), (acbd.1.2, acbd.2.2))

@[simp, grind =]
-/
def prodProdProdComm (α β γ δ) : (α × β) × γ × δ ≃ (α × γ) × β × δ where
  toFun abcd := ((abcd.1.1, abcd.2.1), (abcd.1.2, abcd.2.2))
  invFun acbd := ((acbd.1.1, acbd.2.1), (acbd.1.2, acbd.2.2))

@[simp, grind =]
/--
theorem `prodProdProdComm_symm` / 定理 `prodProdProdComm_symm`

English:
theorem prodProdProdComm_symm
  given: (α β γ δ)
  proof: rfl

中文:
定理 prodProdProdComm_symm
  条件: (α β γ δ)
  证明: rfl
-/
theorem prodProdProdComm_symm (α β γ δ) :
    (prodProdProdComm α β γ δ).symm = prodProdProdComm α γ β δ :=
  rfl

/-- `γ`-valued functions on `α × β` are equivalent to functions `α → β → γ`. -/
@[simps (attr := grind =) -fullyApplied]
/--
Definition of `curry` / `curry` 的定义

English:
definition curry
  signature: (α β γ)
  body: Function.curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

中文:
定义 curry
  签名: (α β γ)
  定义体: Function.curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

Depends on / 依赖: Function, Function.curry
-/
def curry (α β γ) : (α × β -> γ) ≃ (α -> β -> γ) where
  toFun := Function.curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

section

/-- `PUnit` is a right identity for type product up to an equivalence. -/
@[simps (attr := grind =)]
/--
Definition of `prodPUnit` / `prodPUnit` 的定义

English:
definition prodPUnit
  signature: (α)
  body: fun p => p.1
  invFun := fun a => (a, PUnit.unit)

中文:
定义 prodPUnit
  签名: (α)
  定义体: fun p => p.1
  invFun := fun a => (a, PUnit.unit)
-/
def prodPUnit (α) : α × PUnit ≃ α where
  toFun := fun p => p.1
  invFun := fun a => (a, PUnit.unit)

/-- `PUnit` is a left identity for type product up to an equivalence. -/
@[simps! (attr := grind =)]
/--
Definition of `punitProd` / `punitProd` 的定义

English:
definition punitProd
  signature: (α)
  body: calc
    PUnit × α ≃ α × PUnit := prodComm _ _
    _ ≃ α := prodPUnit _

中文:
定义 punitProd
  签名: (α)
  定义体: calc
    PUnit × α ≃ α × PUnit := prodComm _ _
    _ ≃ α := prodPUnit _

Depends on / 依赖: prodComm, prodPUnit
-/
def punitProd (α) : PUnit × α ≃ α :=
  calc
    PUnit × α ≃ α × PUnit := prodComm _ _
    _ ≃ α := prodPUnit _

/-- `PUnit` is a right identity for dependent type product up to an equivalence. -/
@[simps (attr := grind =)]
/--
Definition of `sigmaPUnit` / `sigmaPUnit` 的定义

English:
definition sigmaPUnit
  signature: (α)
  body: fun p => p.1
  invFun := fun a => ⟨a, PUnit.unit⟩

中文:
定义 sigmaPUnit
  签名: (α)
  定义体: fun p => p.1
  invFun := fun a => ⟨a, PUnit.unit⟩
-/
def sigmaPUnit (α) : (_ : α) × PUnit ≃ α where
  toFun := fun p => p.1
  invFun := fun a => ⟨a, PUnit.unit⟩

/--
Definition of `prodUnique` / `prodUnique` 的定义

English:
definition prodUnique
  signature: (α β) [Unique β]
  body: ((Equiv.refl α).prodCongr <| equivPUnit.{_, 1} β).trans prodPUnit α

@[simp]

中文:
定义 prodUnique
  签名: (α β) [唯一 β]
  定义体: ((Equiv.refl α).prodCongr <| equivPUnit.{_, 1} β).trans prodPUnit α

@[simp]

Depends on / 依赖: Equiv.refl, equivPUnit, prodCongr, prodPUnit
-/
def prodUnique (α β) [Unique β] : α × β ≃ α :=
((Equiv.refl α).prodCongr <| equivPUnit.{_, 1} β).trans prodPUnit α

@[simp]
/--
theorem `coe_prodUnique` / 定理 `coe_prodUnique`

English:
theorem coe_prodUnique
  given: {α β} [Unique β]
  statement: (⇑(prodUnique α β) : α × β -> α) = Prod.fst
  proof: rfl

中文:
定理 coe_prodUnique
  条件: {α β} [唯一 β]
  结论: (⇑(prodUnique α β) : α × β -> α) = 积类型.fst
  证明: rfl
-/
theorem coe_prodUnique {α β} [Unique β] : (⇑(prodUnique α β) : α × β -> α) = Prod.fst :=
  rfl

/--
theorem `prodUnique_apply` / 定理 `prodUnique_apply`

English:
theorem prodUnique_apply
  given: {α β} [Unique β] (x : α × β)
  statement: prodUnique α β x = x.1
  proof: rfl

@[simp]

中文:
定理 prodUnique_apply
  条件: {α β} [唯一 β] (x : α × β)
  结论: prodUnique α β x = x.1
  证明: rfl

@[simp]
-/
theorem prodUnique_apply {α β} [Unique β] (x : α × β) : prodUnique α β x = x.1 :=
  rfl

@[simp]
/--
theorem `prodUnique_symm_apply` / 定理 `prodUnique_symm_apply`

English:
theorem prodUnique_symm_apply
  given: {α β} [Unique β] (x : α)
  statement: (prodUnique α β).symm x = (x, default)
  proof: rfl

中文:
定理 prodUnique_symm_apply
  条件: {α β} [唯一 β] (x : α)
  结论: (prodUnique α β).symm x = (x, default)
  证明: rfl
-/
theorem prodUnique_symm_apply {α β} [Unique β] (x : α) : (prodUnique α β).symm x = (x, default) :=
  rfl

/--
Definition of `uniqueProd` / `uniqueProd` 的定义

English:
definition uniqueProd
  signature: (α β) [Unique β]
  body: ((equivPUnit.{_, 1} β).prodCongr <| Equiv.refl α).trans punitProd α

@[simp]

中文:
定义 uniqueProd
  签名: (α β) [唯一 β]
  定义体: ((equivPUnit.{_, 1} β).prodCongr <| Equiv.refl α).trans punitProd α

@[simp]

Depends on / 依赖: Equiv.refl, equivPUnit, prodCongr, punitProd
-/
def uniqueProd (α β) [Unique β] : β × α ≃ α :=
((equivPUnit.{_, 1} β).prodCongr <| Equiv.refl α).trans punitProd α

@[simp]
/--
theorem `coe_uniqueProd` / 定理 `coe_uniqueProd`

English:
theorem coe_uniqueProd
  given: {α β} [Unique β]
  statement: (⇑(uniqueProd α β) : β × α -> α) = Prod.snd
  proof: rfl

中文:
定理 coe_uniqueProd
  条件: {α β} [唯一 β]
  结论: (⇑(uniqueProd α β) : β × α -> α) = 积类型.snd
  证明: rfl
-/
theorem coe_uniqueProd {α β} [Unique β] : (⇑(uniqueProd α β) : β × α -> α) = Prod.snd :=
  rfl

/--
theorem `uniqueProd_apply` / 定理 `uniqueProd_apply`

English:
theorem uniqueProd_apply
  given: {α β} [Unique β] (x : β × α)
  statement: uniqueProd α β x = x.2
  proof: rfl

@[simp]

中文:
定理 uniqueProd_apply
  条件: {α β} [唯一 β] (x : β × α)
  结论: uniqueProd α β x = x.2
  证明: rfl

@[simp]
-/
theorem uniqueProd_apply {α β} [Unique β] (x : β × α) : uniqueProd α β x = x.2 :=
  rfl

@[simp]
/--
theorem `uniqueProd_symm_apply` / 定理 `uniqueProd_symm_apply`

English:
theorem uniqueProd_symm_apply
  given: {α β} [Unique β] (x : α)
  proof: rfl

中文:
定理 uniqueProd_symm_apply
  条件: {α β} [唯一 β] (x : α)
  证明: rfl
-/
theorem uniqueProd_symm_apply {α β} [Unique β] (x : α) :
    (uniqueProd α β).symm x = (default, x) :=
  rfl

/--
Definition of `sigmaUnique` / `sigmaUnique` 的定义

English:
definition sigmaUnique
  signature: (α) (β : α -> Type*) [forall a, Unique (β a)]
  body: (Equiv.sigmaCongrRight fun a => equivPUnit.{_, 1} (β a)).trans sigmaPUnit α

@[simp]

中文:
定义 sigmaUnique
  签名: (α) (β : α -> 类型) [对任意 a, 唯一 (β a)]
  定义体: (Equiv.sigmaCongrRight fun a => equivPUnit.{_, 1} (β a)).trans sigmaPUnit α

@[simp]

Depends on / 依赖: Equiv.sigmaCongrRight, equivPUnit, sigmaCongrRight, sigmaPUnit
-/
def sigmaUnique (α) (β : α -> Type*) [forall a, Unique (β a)] : (a : α) × (β a) ≃ α :=
(Equiv.sigmaCongrRight fun a => equivPUnit.{_, 1} (β a)).trans sigmaPUnit α

@[simp]
/--
theorem `coe_sigmaUnique` / 定理 `coe_sigmaUnique`

English:
theorem coe_sigmaUnique
  given: {α} {β : α -> Type*} [forall a, Unique (β a)]
  proof: rfl

中文:
定理 coe_sigmaUnique
  条件: {α} {β : α -> 类型} [对任意 a, 唯一 (β a)]
  证明: rfl
-/
theorem coe_sigmaUnique {α} {β : α -> Type*} [forall a, Unique (β a)] :
    (⇑(sigmaUnique α β) : (a : α) × (β a) -> α) = Sigma.fst :=
  rfl

/--
theorem `sigmaUnique_apply` / 定理 `sigmaUnique_apply`

English:
theorem sigmaUnique_apply
  given: {α} {β : α -> Type*} [forall a, Unique (β a)] (x : (a : α) × β a)
  proof: rfl

@[simp]

中文:
定理 sigmaUnique_apply
  条件: {α} {β : α -> 类型} [对任意 a, 唯一 (β a)] (x : (a : α) × β a)
  证明: rfl

@[simp]
-/
theorem sigmaUnique_apply {α} {β : α -> Type*} [forall a, Unique (β a)] (x : (a : α) × β a) :
    sigmaUnique α β x = x.1 :=
  rfl

@[simp]
/--
theorem `sigmaUnique_symm_apply` / 定理 `sigmaUnique_symm_apply`

English:
theorem sigmaUnique_symm_apply
  given: {α} {β : α -> Type*} [forall a, Unique (β a)] (x : α)
  proof: rfl

中文:
定理 sigmaUnique_symm_apply
  条件: {α} {β : α -> 类型} [对任意 a, 唯一 (β a)] (x : α)
  证明: rfl
-/
theorem sigmaUnique_symm_apply {α} {β : α -> Type*} [forall a, Unique (β a)] (x : α) :
    (sigmaUnique α β).symm x = ⟨x, default⟩ :=
  rfl

/--
Definition of `uniqueSigma` / `uniqueSigma` 的定义

English:
definition uniqueSigma
  signature: {α} (β : α -> Type*) [Unique α]
  body: fun p => (Unique.eq_default _).rec p.2
  invFun := fun b => ⟨default, b⟩
  left_inv := fun _ => Sigma.ext (Unique.default_eq _) (eqRec_heq _ _)

中文:
定义 uniqueSigma
  签名: {α} (β : α -> 类型) [唯一 α]
  定义体: fun p => (Unique.eq_default _).rec p.2
  invFun := fun b => ⟨default, b⟩
  left_inv := fun _ => Sigma.ext (Unique.default_eq _) (eqRec_heq _ _)

Depends on / 依赖: Unique, Unique.eq_default, eq_default
-/
def uniqueSigma {α} (β : α -> Type*) [Unique α] : (i : α) × β i ≃ β default where
  toFun := fun p => (Unique.eq_default _).rec p.2
  invFun := fun b => ⟨default, b⟩
  left_inv := fun _ => Sigma.ext (Unique.default_eq _) (eqRec_heq _ _)

/--
theorem `uniqueSigma_apply` / 定理 `uniqueSigma_apply`

English:
theorem uniqueSigma_apply
  given: {α} {β : α -> Type*} [Unique α] (x : (a : α) × β a)
  proof: rfl

@[simp]

中文:
定理 uniqueSigma_apply
  条件: {α} {β : α -> 类型} [唯一 α] (x : (a : α) × β a)
  证明: rfl

@[simp]
-/
theorem uniqueSigma_apply {α} {β : α -> Type*} [Unique α] (x : (a : α) × β a) :
    uniqueSigma β x = (Unique.eq_default _).rec x.2 :=
  rfl

@[simp]
/--
theorem `uniqueSigma_symm_apply` / 定理 `uniqueSigma_symm_apply`

English:
theorem uniqueSigma_symm_apply
  given: {α} {β : α -> Type*} [Unique α] (y : β default)
  proof: rfl

中文:
定理 uniqueSigma_symm_apply
  条件: {α} {β : α -> 类型} [唯一 α] (y : β default)
  证明: rfl
-/
theorem uniqueSigma_symm_apply {α} {β : α -> Type*} [Unique α] (y : β default) :
    (uniqueSigma β).symm y = ⟨default, y⟩ :=
  rfl

/--
Definition of `prodEmpty` / `prodEmpty` 的定义

English:
definition prodEmpty
  signature: (α)
  body: equivEmpty _

中文:
定义 prodEmpty
  签名: (α)
  定义体: equivEmpty _

Depends on / 依赖: equivEmpty
-/
def prodEmpty (α) : α × Empty ≃ Empty :=
  equivEmpty _

/--
Definition of `emptyProd` / `emptyProd` 的定义

English:
definition emptyProd
  signature: (α)
  body: equivEmpty _

中文:
定义 emptyProd
  签名: (α)
  定义体: equivEmpty _

Depends on / 依赖: equivEmpty
-/
def emptyProd (α) : Empty × α ≃ Empty :=
  equivEmpty _

/--
Definition of `prodPEmpty` / `prodPEmpty` 的定义

English:
definition prodPEmpty
  signature: (α)
  body: equivPEmpty _

中文:
定义 prodPEmpty
  签名: (α)
  定义体: equivPEmpty _

Depends on / 依赖: equivPEmpty
-/
def prodPEmpty (α) : α × PEmpty ≃ PEmpty :=
  equivPEmpty _

/--
Definition of `pemptyProd` / `pemptyProd` 的定义

English:
definition pemptyProd
  signature: (α)
  body: equivPEmpty _

中文:
定义 pemptyProd
  签名: (α)
  定义体: equivPEmpty _

Depends on / 依赖: equivPEmpty
-/
def pemptyProd (α) : PEmpty × α ≃ PEmpty :=
  equivPEmpty _

end

section prodCongr

variable {α₁ α₂ β₁ β₂ : Type*} (e : α₁ -> β₁ ≃ β₂)

/-- A family of equivalences `∀ (a : α₁), β₁ ≃ β₂` generates an equivalence
between `β₁ × α₁` and `β₂ × α₁`. -/
@[simps apply_fst apply_snd]
/--
Definition of `prodCongrLeft` / `prodCongrLeft` 的定义

English:
definition prodCongrLeft
  signature: : β₁ × α₁ ≃ β₂ × α₁ where
  body: ⟨e ab.2 ab.1, ab.2⟩
  invFun ab := ⟨(e ab.2).symm ab.1, ab.2⟩
  left_inv := by grind
  right_inv := by grind

@[simp]

中文:
定义 prodCongrLeft
  签名: : β₁ × α₁ ≃ β₂ × α₁ where
  定义体: ⟨e ab.2 ab.1, ab.2⟩
  invFun ab := ⟨(e ab.2).symm ab.1, ab.2⟩
  left_inv := by grind
  right_inv := by grind

@[simp]
-/
def prodCongrLeft : β₁ × α₁ ≃ β₂ × α₁ where
  toFun ab := ⟨e ab.2 ab.1, ab.2⟩
  invFun ab := ⟨(e ab.2).symm ab.1, ab.2⟩
  left_inv := by grind
  right_inv := by grind

@[simp]
/--
theorem `prodCongrLeft_apply` / 定理 `prodCongrLeft_apply`

English:
theorem prodCongrLeft_apply
  given: (b : β₁) (a : α₁)
  statement: prodCongrLeft e (b, a) = (e a b, a)
  proof: rfl

中文:
定理 prodCongrLeft_apply
  条件: (b : β₁) (a : α₁)
  结论: prodCongrLeft e (b, a) = (e a b, a)
  证明: rfl
-/
theorem prodCongrLeft_apply (b : β₁) (a : α₁) : prodCongrLeft e (b, a) = (e a b, a) :=
  rfl

/--
theorem `prodCongr_refl_right` / 定理 `prodCongr_refl_right`

English:
theorem prodCongr_refl_right
  given: (e : β₁ ≃ β₂)
  proof: rfl

中文:
定理 prodCongr_refl_right
  条件: (e : β₁ ≃ β₂)
  证明: rfl
-/
theorem prodCongr_refl_right (e : β₁ ≃ β₂) :
    prodCongr e (Equiv.refl α₁) = prodCongrLeft fun _ => e := rfl

/--
lemma `prodCongrLeft_symm` / 引理 `prodCongrLeft_symm`

English:
lemma prodCongrLeft_symm
  statement: (prodCongrLeft e).symm = prodCongrLeft (.symm ∘ e)
  proof: rfl

中文:
引理 prodCongrLeft_symm
  结论: (prodCongrLeft e).symm = prodCongrLeft (.symm ∘ e)
  证明: rfl
-/
@[simp] lemma prodCongrLeft_symm : (prodCongrLeft e).symm = prodCongrLeft (.symm ∘ e) := rfl

/-- A family of equivalences `∀ (a : α₁), β₁ ≃ β₂` generates an equivalence
between `α₁ × β₁` and `α₁ × β₂`. -/
@[simps apply_fst apply_snd]
/--
Definition of `prodCongrRight` / `prodCongrRight` 的定义

English:
definition prodCongrRight
  signature: : α₁ × β₁ ≃ α₁ × β₂ where
  body: ⟨ab.1, e ab.1 ab.2⟩
  invFun ab := ⟨ab.1, (e ab.1).symm ab.2⟩
  left_inv := by grind
  right_inv := by grind

@[simp]

中文:
定义 prodCongrRight
  签名: : α₁ × β₁ ≃ α₁ × β₂ where
  定义体: ⟨ab.1, e ab.1 ab.2⟩
  invFun ab := ⟨ab.1, (e ab.1).symm ab.2⟩
  left_inv := by grind
  right_inv := by grind

@[simp]
-/
def prodCongrRight : α₁ × β₁ ≃ α₁ × β₂ where
  toFun ab := ⟨ab.1, e ab.1 ab.2⟩
  invFun ab := ⟨ab.1, (e ab.1).symm ab.2⟩
  left_inv := by grind
  right_inv := by grind

@[simp]
/--
theorem `prodCongrRight_apply` / 定理 `prodCongrRight_apply`

English:
theorem prodCongrRight_apply
  given: (a : α₁) (b : β₁)
  statement: prodCongrRight e (a, b) = (a, e a b)
  proof: rfl

中文:
定理 prodCongrRight_apply
  条件: (a : α₁) (b : β₁)
  结论: prodCongrRight e (a, b) = (a, e a b)
  证明: rfl
-/
theorem prodCongrRight_apply (a : α₁) (b : β₁) : prodCongrRight e (a, b) = (a, e a b) :=
  rfl

/--
theorem `prodCongr_refl_left` / 定理 `prodCongr_refl_left`

English:
theorem prodCongr_refl_left
  given: (e : β₁ ≃ β₂)
  proof: rfl

中文:
定理 prodCongr_refl_left
  条件: (e : β₁ ≃ β₂)
  证明: rfl
-/
theorem prodCongr_refl_left (e : β₁ ≃ β₂) :
    prodCongr (Equiv.refl α₁) e = prodCongrRight fun _ => e := rfl

/--
lemma `prodCongrRight_symm` / 引理 `prodCongrRight_symm`

English:
lemma prodCongrRight_symm
  statement: (prodCongrRight e).symm = prodCongrRight (.symm ∘ e)
  proof: rfl

@[simp]

中文:
引理 prodCongrRight_symm
  结论: (prodCongrRight e).symm = prodCongrRight (.symm ∘ e)
  证明: rfl

@[simp]
-/
@[simp] lemma prodCongrRight_symm : (prodCongrRight e).symm = prodCongrRight (.symm ∘ e) := rfl

@[simp]
/--
theorem `prodCongrLeft_trans_prodComm` / 定理 `prodCongrLeft_trans_prodComm`

English:
theorem prodCongrLeft_trans_prodComm
  proof: by
  ext ⟨a, b⟩ : 1
  simp

@[simp]

中文:
定理 prodCongrLeft_trans_prodComm
  证明: by
  ext ⟨a, b⟩ : 1
  simp

@[simp]
-/
theorem prodCongrLeft_trans_prodComm :
    (prodCongrLeft e).trans (prodComm _ _) = (prodComm _ _).trans (prodCongrRight e) := by
  ext ⟨a, b⟩ : 1
  simp

@[simp]
/--
theorem `prodCongrRight_trans_prodComm` / 定理 `prodCongrRight_trans_prodComm`

English:
theorem prodCongrRight_trans_prodComm
  proof: by
  ext ⟨a, b⟩ : 1
  simp

中文:
定理 prodCongrRight_trans_prodComm
  证明: by
  ext ⟨a, b⟩ : 1
  simp
-/
theorem prodCongrRight_trans_prodComm :
    (prodCongrRight e).trans (prodComm _ _) = (prodComm _ _).trans (prodCongrLeft e) := by
  ext ⟨a, b⟩ : 1
  simp

/--
theorem `sigmaCongrRight_sigmaEquivProd` / 定理 `sigmaCongrRight_sigmaEquivProd`

English:
theorem sigmaCongrRight_sigmaEquivProd
  proof: by
  ext ⟨a, b⟩ : 1
  simp

中文:
定理 sigmaCongrRight_sigmaEquivProd
  证明: by
  ext ⟨a, b⟩ : 1
  simp
-/
theorem sigmaCongrRight_sigmaEquivProd :
    (sigmaCongrRight e).trans (sigmaEquivProd α₁ β₂)
    = (sigmaEquivProd α₁ β₁).trans (prodCongrRight e) := by
  ext ⟨a, b⟩ : 1
  simp

/--
theorem `sigmaEquivProd_sigmaCongrRight` / 定理 `sigmaEquivProd_sigmaCongrRight`

English:
theorem sigmaEquivProd_sigmaCongrRight
  proof: by
  ext ⟨a, b⟩ : 1
  simp only [trans_apply, sigmaCongrRight_apply, prodCongrRight_apply]
  rfl

中文:
定理 sigmaEquivProd_sigmaCongrRight
  证明: by
  ext ⟨a, b⟩ : 1
  simp only [trans_apply, sigmaCongrRight_apply, prodCongrRight_apply]
  rfl

Depends on / 依赖: prodCongrRight_apply, sigmaCongrRight_apply, trans_apply
-/
theorem sigmaEquivProd_sigmaCongrRight :
    (sigmaEquivProd α₁ β₁).symm.trans (sigmaCongrRight e)
    = (prodCongrRight e).trans (sigmaEquivProd α₁ β₂).symm := by
  ext ⟨a, b⟩ : 1
  simp only [trans_apply, sigmaCongrRight_apply, prodCongrRight_apply]
  rfl

/-- A variation on `Equiv.prodCongr` where the equivalence in the second component can depend
  on the first component. A typical example is a shear mapping, explaining the name of this
  declaration. -/
@[simps -fullyApplied]
/--
Definition of `prodShear` / `prodShear` 的定义

English:
definition prodShear
  signature: (e₁ : α₁ ≃ α₂) (e₂ : α₁ -> β₁ ≃ β₂)
  body: fun x : α₁ × β₁ => (e₁ x.1, e₂ x.1 x.2)
  invFun := fun y : α₂ × β₂ => (e₁.symm y.1, (e₂ <| e₁.symm y.1).symm y.2)
  left_inv := by grind
  right_inv := by grind

中文:
定义 prodShear
  签名: (e₁ : α₁ ≃ α₂) (e₂ : α₁ -> β₁ ≃ β₂)
  定义体: fun x : α₁ × β₁ => (e₁ x.1, e₂ x.1 x.2)
  invFun := fun y : α₂ × β₂ => (e₁.symm y.1, (e₂ <| e₁.symm y.1).symm y.2)
  left_inv := by grind
  right_inv := by grind
-/
def prodShear (e₁ : α₁ ≃ α₂) (e₂ : α₁ -> β₁ ≃ β₂) : α₁ × β₁ ≃ α₂ × β₂ where
  toFun := fun x : α₁ × β₁ => (e₁ x.1, e₂ x.1 x.2)
  invFun := fun y : α₂ × β₂ => (e₁.symm y.1, (e₂ <| e₁.symm y.1).symm y.2)
  left_inv := by grind
  right_inv := by grind

end prodCongr

namespace Perm

variable {α₁ β₁ : Type*} [DecidableEq α₁] (a : α₁) (e : Perm β₁)

/--
Definition of `prodExtendRight` / `prodExtendRight` 的定义

English:
definition prodExtendRight
  signature: : Perm (α₁ × β₁) where
  body: if ab.fst = a then (a, e ab.snd) else ab
  invFun ab := if ab.fst = a then (a, e.symm ab.snd) else ab
  left_inv := by grind
  right_inv := by grind

@[simp]

中文:
定义 prodExtendRight
  签名: : 置换 (α₁ × β₁) where
  定义体: if ab.fst = a then (a, e ab.snd) else ab
  invFun ab := if ab.fst = a then (a, e.symm ab.snd) else ab
  left_inv := by grind
  right_inv := by grind

@[simp]

Depends on / 依赖: ab.fst, ab.snd
-/
def prodExtendRight : Perm (α₁ × β₁) where
  toFun ab := if ab.fst = a then (a, e ab.snd) else ab
  invFun ab := if ab.fst = a then (a, e.symm ab.snd) else ab
  left_inv := by grind
  right_inv := by grind

@[simp]
/--
theorem `prodExtendRight_apply_eq` / 定理 `prodExtendRight_apply_eq`

English:
theorem prodExtendRight_apply_eq
  given: (b : β₁)
  statement: prodExtendRight a e (a, b) = (a, e b)
  proof: if_pos rfl

中文:
定理 prodExtendRight_apply_eq
  条件: (b : β₁)
  结论: prodExtendRight a e (a, b) = (a, e b)
  证明: if_pos rfl

Depends on / 依赖: if_pos
-/
theorem prodExtendRight_apply_eq (b : β₁) : prodExtendRight a e (a, b) = (a, e b) :=
  if_pos rfl

/--
theorem `prodExtendRight_apply_ne` / 定理 `prodExtendRight_apply_ne`

English:
theorem prodExtendRight_apply_ne
  given: {a a' : α₁} (h : a' != a) (b : β₁)
  proof: if_neg h

中文:
定理 prodExtendRight_apply_ne
  条件: {a a' : α₁} (h : a' != a) (b : β₁)
  证明: if_neg h

Depends on / 依赖: if_neg
-/
theorem prodExtendRight_apply_ne {a a' : α₁} (h : a' != a) (b : β₁) :
    prodExtendRight a e (a', b) = (a', b) :=
  if_neg h

/--
theorem `eq_of_prodExtendRight_ne` / 定理 `eq_of_prodExtendRight_ne`

English:
theorem eq_of_prodExtendRight_ne
  statement: {e : Perm β₁} {a a' : α₁} {b : β₁}
  proof: by
  contrapose! h
  exact prodExtendRight_apply_ne _ h _

@[simp]

中文:
定理 eq_of_prodExtendRight_ne
  结论: {e : 置换 β₁} {a a' : α₁} {b : β₁}
  证明: by
  contrapose! h
  exact prodExtendRight_apply_ne _ h _

@[simp]

Depends on / 依赖: contrapose, prodExtendRight_apply_ne
-/
theorem eq_of_prodExtendRight_ne {e : Perm β₁} {a a' : α₁} {b : β₁}
    (h : prodExtendRight a e (a', b) != (a', b)) : a' = a := by
  contrapose! h
  exact prodExtendRight_apply_ne _ h _

@[simp]
/--
theorem `fst_prodExtendRight` / 定理 `fst_prodExtendRight`

English:
theorem fst_prodExtendRight
  given: (ab : α₁ × β₁)
  statement: (prodExtendRight a e ab).fst = ab.fst
  proof: by
  grind [prodExtendRight]

中文:
定理 fst_prodExtendRight
  条件: (ab : α₁ × β₁)
  结论: (prodExtendRight a e ab).fst = ab.fst
  证明: by
  grind [prodExtendRight]

Depends on / 依赖: prodExtendRight
-/
theorem fst_prodExtendRight (ab : α₁ × β₁) : (prodExtendRight a e ab).fst = ab.fst := by
  grind [prodExtendRight]

end Perm

section

/-- The type of functions to a product `β × γ` is equivalent to the type of pairs of functions
`α → β` and `β → γ`. -/
@[simps]
/--
Definition of `arrowProdEquivProdArrow` / `arrowProdEquivProdArrow` 的定义

English:
definition arrowProdEquivProdArrow
  signature: (α : Type*) (β γ : α -> Type*)
  body: fun f => (fun c => (f c).1, fun c => (f c).2)
  invFun := fun p c => (p.1 c, p.2 c)

中文:
定义 arrowProdEquivProdArrow
  签名: (α : 类型) (β γ : α -> 类型)
  定义体: fun f => (fun c => (f c).1, fun c => (f c).2)
  invFun := fun p c => (p.1 c, p.2 c)
-/
def arrowProdEquivProdArrow (α : Type*) (β γ : α -> Type*) :
    ((i : α) -> β i × γ i) ≃ ((i : α) -> β i) × ((i : α) -> γ i) where
  toFun := fun f => (fun c => (f c).1, fun c => (f c).2)
  invFun := fun p c => (p.1 c, p.2 c)

open Sum

/-- The type of dependent functions on a sum type `ι ⊕ ι'` is equivalent to the type of pairs of
functions on `ι` and on `ι'`. This is a dependent version of `Equiv.sumArrowEquivProdArrow`. -/
@[simps (attr := grind =)]
/--
Definition of `sumPiEquivProdPi` / `sumPiEquivProdPi` 的定义

English:
definition sumPiEquivProdPi
  signature: {ι ι'} (π : ι oplus ι' -> Type*)
  body: ⟨fun i => f (inl i), fun i' => f (inr i')⟩
  invFun g := Sum.rec g.1 g.2
  left_inv f := by ext (i | i) <;> rfl

中文:
定义 sumPiEquivProdPi
  签名: {ι ι'} (π : ι oplus ι' -> 类型)
  定义体: ⟨fun i => f (inl i), fun i' => f (inr i')⟩
  invFun g := Sum.rec g.1 g.2
  left_inv f := by ext (i | i) <;> rfl
-/
def sumPiEquivProdPi {ι ι'} (π : ι oplus ι' -> Type*) :
    (forall i, π i) ≃ (forall i, π (inl i)) × forall i', π (inr i') where
  toFun f := ⟨fun i => f (inl i), fun i' => f (inr i')⟩
  invFun g := Sum.rec g.1 g.2
  left_inv f := by ext (i | i) <;> rfl

/-- The equivalence between a product of two dependent functions types and a single dependent
function type. Basically a symmetric version of `Equiv.sumPiEquivProdPi`. -/
@[simps! (attr := grind =)]
/--
Definition of `prodPiEquivSumPi` / `prodPiEquivSumPi` 的定义

English:
definition prodPiEquivSumPi
  signature: {ι ι'} (π : ι -> Type u) (π' : ι' -> Type u)
  body: .symm sumPiEquivProdPi (Sum.elim π π')

中文:
定义 prodPiEquivSumPi
  签名: {ι ι'} (π : ι -> 类型u) (π' : ι' -> 类型u)
  定义体: .symm sumPiEquivProdPi (Sum.elim π π')

Depends on / 依赖: Sum.elim, sumPiEquivProdPi
-/
def prodPiEquivSumPi {ι ι'} (π : ι -> Type u) (π' : ι' -> Type u) :
    ((forall i, π i) × forall i', π' i') ≃ forall i, Sum.elim π π' i :=
.symm sumPiEquivProdPi (Sum.elim π π')

/--
Definition of `sumArrowEquivProdArrow` / `sumArrowEquivProdArrow` 的定义

English:
definition sumArrowEquivProdArrow
  signature: (α β γ : Type*)
  body: ⟨fun f => (f ∘ inl, f ∘ inr), fun p => Sum.elim p.1 p.2, fun f => by ext ⟨⟩ <;> rfl, fun p => by
    cases p
    rfl⟩

@[simp, grind =]

中文:
定义 sumArrowEquivProdArrow
  签名: (α β γ : 类型)
  定义体: ⟨fun f => (f ∘ inl, f ∘ inr), fun p => Sum.elim p.1 p.2, fun f => by ext ⟨⟩ <;> rfl, fun p => by
    cases p
    rfl⟩

@[simp, grind =]

Depends on / 依赖: Sum.elim
-/
def sumArrowEquivProdArrow (α β γ : Type*) : (α oplus β -> γ) ≃ (α -> γ) × (β -> γ) :=
  ⟨fun f => (f ∘ inl, f ∘ inr), fun p => Sum.elim p.1 p.2, fun f => by ext ⟨⟩ <;> rfl, fun p => by
    cases p
    rfl⟩

@[simp, grind =]
/--
theorem `sumArrowEquivProdArrow_apply_fst` / 定理 `sumArrowEquivProdArrow_apply_fst`

English:
theorem sumArrowEquivProdArrow_apply_fst
  given: {α β γ} (f : α oplus β -> γ) (a : α)
  proof: rfl

@[simp, grind =]

中文:
定理 sumArrowEquivProdArrow_apply_fst
  条件: {α β γ} (f : α oplus β -> γ) (a : α)
  证明: rfl

@[simp, grind =]
-/
theorem sumArrowEquivProdArrow_apply_fst {α β γ} (f : α oplus β -> γ) (a : α) :
    (sumArrowEquivProdArrow α β γ f).1 a = f (inl a) :=
  rfl

@[simp, grind =]
/--
theorem `sumArrowEquivProdArrow_apply_snd` / 定理 `sumArrowEquivProdArrow_apply_snd`

English:
theorem sumArrowEquivProdArrow_apply_snd
  given: {α β γ} (f : α oplus β -> γ) (b : β)
  proof: rfl

@[simp, grind =]

中文:
定理 sumArrowEquivProdArrow_apply_snd
  条件: {α β γ} (f : α oplus β -> γ) (b : β)
  证明: rfl

@[simp, grind =]
-/
theorem sumArrowEquivProdArrow_apply_snd {α β γ} (f : α oplus β -> γ) (b : β) :
    (sumArrowEquivProdArrow α β γ f).2 b = f (inr b) :=
  rfl

@[simp, grind =]
/--
theorem `sumArrowEquivProdArrow_symm_apply_inl` / 定理 `sumArrowEquivProdArrow_symm_apply_inl`

English:
theorem sumArrowEquivProdArrow_symm_apply_inl
  given: {α β γ} (f : α -> γ) (g : β -> γ) (a : α)
  proof: rfl

@[simp, grind =]

中文:
定理 sumArrowEquivProdArrow_symm_apply_inl
  条件: {α β γ} (f : α -> γ) (g : β -> γ) (a : α)
  证明: rfl

@[simp, grind =]
-/
theorem sumArrowEquivProdArrow_symm_apply_inl {α β γ} (f : α -> γ) (g : β -> γ) (a : α) :
    ((sumArrowEquivProdArrow α β γ).symm (f, g)) (inl a) = f a :=
  rfl

@[simp, grind =]
/--
theorem `sumArrowEquivProdArrow_symm_apply_inr` / 定理 `sumArrowEquivProdArrow_symm_apply_inr`

English:
theorem sumArrowEquivProdArrow_symm_apply_inr
  given: {α β γ} (f : α -> γ) (g : β -> γ) (b : β)
  proof: rfl

中文:
定理 sumArrowEquivProdArrow_symm_apply_inr
  条件: {α β γ} (f : α -> γ) (g : β -> γ) (b : β)
  证明: rfl
-/
theorem sumArrowEquivProdArrow_symm_apply_inr {α β γ} (f : α -> γ) (g : β -> γ) (b : β) :
    ((sumArrowEquivProdArrow α β γ).symm (f, g)) (inr b) = g b :=
  rfl

/--
Definition of `sumProdDistrib` / `sumProdDistrib` 的定义

English:
definition sumProdDistrib
  signature: (α β γ)
  body: ⟨fun p => p.1.map (fun x => (x, p.2)) fun x => (x, p.2),
    fun s => s.elim (Prod.map inl id) (Prod.map inr id), by
      rintro ⟨_ | _, _⟩ <;> rfl, by rintro (⟨_, _⟩ | ⟨_, _⟩) <;> rfl⟩

@[simp, grind =]

中文:
定义 sumProdDistrib
  签名: (α β γ)
  定义体: ⟨fun p => p.1.map (fun x => (x, p.2)) fun x => (x, p.2),
    fun s => s.elim (Prod.map inl id) (Prod.map inr id), by
      rintro ⟨_ | _, _⟩ <;> rfl, by rintro (⟨_, _⟩ | ⟨_, _⟩) <;> rfl⟩

@[simp, grind =]

Depends on / 依赖: Prod.map, s.elim
-/
def sumProdDistrib (α β γ) : (α oplus β) × γ ≃ α × γ oplus β × γ :=
  ⟨fun p => p.1.map (fun x => (x, p.2)) fun x => (x, p.2),
    fun s => s.elim (Prod.map inl id) (Prod.map inr id), by
      rintro ⟨_ | _, _⟩ <;> rfl, by rintro (⟨_, _⟩ | ⟨_, _⟩) <;> rfl⟩

@[simp, grind =]
/--
theorem `sumProdDistrib_apply_left` / 定理 `sumProdDistrib_apply_left`

English:
theorem sumProdDistrib_apply_left
  given: {α β γ} (a : α) (c : γ)
  proof: rfl

@[simp, grind =]

中文:
定理 sumProdDistrib_apply_left
  条件: {α β γ} (a : α) (c : γ)
  证明: rfl

@[simp, grind =]
-/
theorem sumProdDistrib_apply_left {α β γ} (a : α) (c : γ) :
    sumProdDistrib α β γ (Sum.inl a, c) = Sum.inl (a, c) :=
  rfl

@[simp, grind =]
/--
theorem `sumProdDistrib_apply_right` / 定理 `sumProdDistrib_apply_right`

English:
theorem sumProdDistrib_apply_right
  given: {α β γ} (b : β) (c : γ)
  proof: rfl

@[simp, grind =]

中文:
定理 sumProdDistrib_apply_right
  条件: {α β γ} (b : β) (c : γ)
  证明: rfl

@[simp, grind =]
-/
theorem sumProdDistrib_apply_right {α β γ} (b : β) (c : γ) :
    sumProdDistrib α β γ (Sum.inr b, c) = Sum.inr (b, c) :=
  rfl

@[simp, grind =]
/--
theorem `sumProdDistrib_symm_apply_left` / 定理 `sumProdDistrib_symm_apply_left`

English:
theorem sumProdDistrib_symm_apply_left
  given: {α β γ} (a : α × γ)
  proof: rfl

@[simp, grind =]

中文:
定理 sumProdDistrib_symm_apply_left
  条件: {α β γ} (a : α × γ)
  证明: rfl

@[simp, grind =]
-/
theorem sumProdDistrib_symm_apply_left {α β γ} (a : α × γ) :
    (sumProdDistrib α β γ).symm (inl a) = (inl a.1, a.2) :=
  rfl

@[simp, grind =]
/--
theorem `sumProdDistrib_symm_apply_right` / 定理 `sumProdDistrib_symm_apply_right`

English:
theorem sumProdDistrib_symm_apply_right
  given: {α β γ} (b : β × γ)
  proof: rfl

中文:
定理 sumProdDistrib_symm_apply_right
  条件: {α β γ} (b : β × γ)
  证明: rfl
-/
theorem sumProdDistrib_symm_apply_right {α β γ} (b : β × γ) :
    (sumProdDistrib α β γ).symm (inr b) = (inr b.1, b.2) :=
  rfl

/-- The product of an indexed sum of types (formally, a `Sigma`-type `Σ i, α i`) by a type `β` is
equivalent to the sum of products `Σ i, (α i × β)`. -/
@[simps (attr := grind =) apply symm_apply]
/--
Definition of `sigmaProdDistrib` / `sigmaProdDistrib` 的定义

English:
definition sigmaProdDistrib
  signature: {ι : Type*} (α : ι -> Type*) (β : Type*)
  body: ⟨fun p => ⟨p.1.1, (p.1.2, p.2)⟩, fun p => (⟨p.1, p.2.1⟩, p.2.2), by grind, by grind⟩

中文:
定义 sigmaProdDistrib
  签名: {ι : 类型} (α : ι -> 类型) (β : 类型)
  定义体: ⟨fun p => ⟨p.1.1, (p.1.2, p.2)⟩, fun p => (⟨p.1, p.2.1⟩, p.2.2), by grind, by grind⟩
-/
def sigmaProdDistrib {ι : Type*} (α : ι -> Type*) (β : Type*) : (Σ i, α i) × β ≃ Σ i, α i × β :=
  ⟨fun p => ⟨p.1.1, (p.1.2, p.2)⟩, fun p => (⟨p.1, p.2.1⟩, p.2.2), by grind, by grind⟩

/-- The product `Bool × α` is equivalent to `α ⊕ α`. -/
@[simps (attr := grind =)]
/--
Definition of `boolProdEquivSum` / `boolProdEquivSum` 的定义

English:
definition boolProdEquivSum
  signature: (α)
  body: if p.1 then (inr p.2) else (inl p.2)
  invFun := Sum.elim (Prod.mk false) (Prod.mk true)
  left_inv := by rintro ⟨_ | _, _⟩ <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

中文:
定义 boolProdEquivSum
  签名: (α)
  定义体: if p.1 then (inr p.2) else (inl p.2)
  invFun := Sum.elim (Prod.mk false) (Prod.mk true)
  left_inv := by rintro ⟨_ | _, _⟩ <;> rfl
  right_inv := by rintro (_ | _) <;> rfl
-/
def boolProdEquivSum (α) : Bool × α ≃ α oplus α where
  toFun p := if p.1 then (inr p.2) else (inl p.2)
  invFun := Sum.elim (Prod.mk false) (Prod.mk true)
  left_inv := by rintro ⟨_ | _, _⟩ <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

/-- The function type `Bool → α` is equivalent to `α × α`. -/
@[simps (attr := grind =)]
/--
Definition of `boolArrowEquivProd` / `boolArrowEquivProd` 的定义

English:
definition boolArrowEquivProd
  signature: (α : Type*)
  body: (f false, f true)
  invFun p b := if b then p.2 else p.1
  left_inv _ := by grind

中文:
定义 boolArrowEquivProd
  签名: (α : 类型)
  定义体: (f false, f true)
  invFun p b := if b then p.2 else p.1
  left_inv _ := by grind
-/
def boolArrowEquivProd (α : Type*) : (Bool -> α) ≃ α × α where
  toFun f := (f false, f true)
  invFun p b := if b then p.2 else p.1
  left_inv _ := by grind

end

section

open Subtype

/--
Definition of `subtypeProdEquivProd` / `subtypeProdEquivProd` 的定义

English:
definition subtypeProdEquivProd
  signature: {α β} {p : α -> Prop} {q : β -> Prop}
  body: fun x => ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩
  invFun := fun x => ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩

中文:
定义 subtypeProdEquivProd
  签名: {α β} {p : α -> 命题} {q : β -> 命题}
  定义体: fun x => ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩
  invFun := fun x => ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩
-/
def subtypeProdEquivProd {α β} {p : α -> Prop} {q : β -> Prop} :
    { c : α × β // p c.1 ∧ q c.2 } ≃ { a // p a } × { b // q b } where
  toFun := fun x => ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩
  invFun := fun x => ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩

/--
Definition of `prodSubtypeFstEquivSubtypeProd` / `prodSubtypeFstEquivSubtypeProd` 的定义

English:
definition prodSubtypeFstEquivSubtypeProd
  signature: {α β} {p : α -> Prop}
  body: ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩

中文:
定义 prodSubtypeFstEquivSubtypeProd
  签名: {α β} {p : α -> 命题}
  定义体: ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
-/
def prodSubtypeFstEquivSubtypeProd {α β} {p : α -> Prop} :
    {s : α × β // p s.1} ≃ {a // p a} × β where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩

/--
Definition of `subtypeProdEquivSigmaSubtype` / `subtypeProdEquivSigmaSubtype` 的定义

English:
definition subtypeProdEquivSigmaSubtype
  signature: {α β} (p : α -> β -> Prop)
  body: ⟨x.1.1, x.1.2, x.property⟩
  invFun x := ⟨⟨x.1, x.2⟩, x.2.property⟩

中文:
定义 subtypeProdEquivSigmaSubtype
  签名: {α β} (p : α -> β -> 命题)
  定义体: ⟨x.1.1, x.1.2, x.property⟩
  invFun x := ⟨⟨x.1, x.2⟩, x.2.property⟩

Depends on / 依赖: property, x.property
-/
def subtypeProdEquivSigmaSubtype {α β} (p : α -> β -> Prop) :
    { x : α × β // p x.1 x.2 } ≃ Σ a, { b : β // p a b } where
  toFun x := ⟨x.1.1, x.1.2, x.property⟩
  invFun x := ⟨⟨x.1, x.2⟩, x.2.property⟩

/-- The type `∀ (i : α), β i` can be split as a product by separating the indices in `α`
depending on whether they satisfy a predicate `p` or not. -/
@[simps]
/--
Definition of `piEquivPiSubtypeProd` / `piEquivPiSubtypeProd` 的定义

English:
definition piEquivPiSubtypeProd
  signature: {α : Type*} (p : α -> Prop) (β : α -> Type*) [DecidablePred p]
  body: (fun x => f x, fun x => f x)
  invFun f x := if h : p x then f.1 ⟨x, h⟩ else f.2 ⟨x, h⟩
  right_inv := by
    rintro ⟨f, g⟩
    ext1 <;> grind
  left_inv f := by grind

中文:
定义 piEquivPiSubtypeProd
  签名: {α : 类型} (p : α -> 命题) (β : α -> 类型) [DecidablePred p]
  定义体: (fun x => f x, fun x => f x)
  invFun f x := if h : p x then f.1 ⟨x, h⟩ else f.2 ⟨x, h⟩
  right_inv := by
    rintro ⟨f, g⟩
    ext1 <;> grind
  left_inv f := by grind
-/
def piEquivPiSubtypeProd {α : Type*} (p : α -> Prop) (β : α -> Type*) [DecidablePred p] :
    (forall i : α, β i) ≃ (forall i : { x // p x }, β i) × forall i : { x // ¬p x }, β i where
  toFun f := (fun x => f x, fun x => f x)
  invFun f x := if h : p x then f.1 ⟨x, h⟩ else f.2 ⟨x, h⟩
  right_inv := by
    rintro ⟨f, g⟩
    ext1 <;> grind
  left_inv f := by grind

/-- A product of types can be split as the binary product of one of the types and the product
  of all the remaining types. -/
@[simps]
/--
Definition of `piSplitAt` / `piSplitAt` 的定义

English:
definition piSplitAt
  signature: {α : Type*} [DecidableEq α] (i : α) (β : α -> Type*)
  body: ⟨f i, fun j => f j⟩
  invFun f j := if h : j = i then h.symm.rec f.1 else f.2 ⟨j, h⟩
  right_inv f := by ext x <;> grind
  left_inv f := by grind

中文:
定义 piSplitAt
  签名: {α : 类型} [DecidableEq α] (i : α) (β : α -> 类型)
  定义体: ⟨f i, fun j => f j⟩
  invFun f j := if h : j = i then h.symm.rec f.1 else f.2 ⟨j, h⟩
  right_inv f := by ext x <;> grind
  left_inv f := by grind
-/
def piSplitAt {α : Type*} [DecidableEq α] (i : α) (β : α -> Type*) :
    (forall j, β j) ≃ β i × forall j : { j // j != i }, β j where
  toFun f := ⟨f i, fun j => f j⟩
  invFun f j := if h : j = i then h.symm.rec f.1 else f.2 ⟨j, h⟩
  right_inv f := by ext x <;> grind
  left_inv f := by grind

/-- A product of copies of a type can be split as the binary product of one copy and the product
  of all the remaining copies. -/
@[simps!]
/--
Definition of `funSplitAt` / `funSplitAt` 的定义

English:
definition funSplitAt
  signature: {α : Type*} [DecidableEq α] (i : α) (β : Type*)
  body: piSplitAt i _

中文:
定义 funSplitAt
  签名: {α : 类型} [DecidableEq α] (i : α) (β : 类型)
  定义体: piSplitAt i _

Depends on / 依赖: piSplitAt
-/
def funSplitAt {α : Type*} [DecidableEq α] (i : α) (β : Type*) :
    (α -> β) ≃ β × ({ j // j != i } -> β) :=
  piSplitAt i _

end

end Equiv

/--
Definition of `subsingletonProdSelfEquiv` / `subsingletonProdSelfEquiv` 的定义

English:
definition subsingletonProdSelfEquiv
  signature: {α} [Subsingleton α]
  body: p.1
  invFun a := (a, a)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

中文:
定义 subsingletonProdSelfEquiv
  签名: {α} [子单例 α]
  定义体: p.1
  invFun a := (a, a)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
-/
def subsingletonProdSelfEquiv {α} [Subsingleton α] : α × α ≃ α where
  toFun p := p.1
  invFun a := (a, a)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

section

variable {α β : Type*} (a : α) (b : β)

/--
Definition of `optionProdEquiv` / `optionProdEquiv` 的定义

English:
definition optionProdEquiv
  signature: : Option α × β ≃ β oplus α × β where
  body: x.1.casesOn (.inl x.2) (fun a => .inr (a, x.2))
  invFun x := x.casesOn (.mk none) (.map some id)
  left_inv
  | (none, _) => rfl
  | (some _, _) => rfl
  right_inv
  | .inl _ => rfl
  | .inr (_, _) => rfl

中文:
定义 optionProdEquiv
  签名: : 选项类型 α × β ≃ β oplus α × β where
  定义体: x.1.casesOn (.inl x.2) (fun a => .inr (a, x.2))
  invFun x := x.casesOn (.mk none) (.map some id)
  left_inv
  | (none, _) => rfl
  | (some _, _) => rfl
  right_inv
  | .inl _ => rfl
  | .inr (_, _) => rfl

Depends on / 依赖: casesOn
-/
def optionProdEquiv : Option α × β ≃ β oplus α × β where
  toFun x := x.1.casesOn (.inl x.2) (fun a => .inr (a, x.2))
  invFun x := x.casesOn (.mk none) (.map some id)
  left_inv
  | (none, _) => rfl
  | (some _, _) => rfl
  right_inv
  | .inl _ => rfl
  | .inr (_, _) => rfl

/--
lemma `optionProdEquiv_mk_none` / 引理 `optionProdEquiv_mk_none`

English:
lemma optionProdEquiv_mk_none
  statement: optionProdEquiv (α := α) (.none, b) = .inl b
  proof: rfl

中文:
引理 optionProdEquiv_mk_none
  结论: optionProdEquiv (α := α) (.none, b) = .inl b
  证明: rfl
-/
@[simp] lemma optionProdEquiv_mk_none : optionProdEquiv (α := α) (.none, b) = .inl b := rfl

/--
lemma `optionProdEquiv_mk_some` / 引理 `optionProdEquiv_mk_some`

English:
lemma optionProdEquiv_mk_some
  statement: optionProdEquiv (.some a, b) = .inr (a, b)
  proof: rfl

中文:
引理 optionProdEquiv_mk_some
  结论: optionProdEquiv (.some a, b) = .inr (a, b)
  证明: rfl
-/
@[simp] lemma optionProdEquiv_mk_some : optionProdEquiv (.some a, b) = .inr (a, b) := rfl

/--
lemma `optionProdEquiv_symm_inl` / 引理 `optionProdEquiv_symm_inl`

English:
lemma optionProdEquiv_symm_inl
  statement: optionProdEquiv (α := α).symm (.inl b) = (.none, b)
  proof: rfl

中文:
引理 optionProdEquiv_symm_inl
  结论: optionProdEquiv (α := α).symm (.inl b) = (.none, b)
  证明: rfl
-/
@[simp] lemma optionProdEquiv_symm_inl : optionProdEquiv (α := α).symm (.inl b) = (.none, b) := rfl

/--
lemma `optionProdEquiv_symm_inr` / 引理 `optionProdEquiv_symm_inr`

English:
lemma optionProdEquiv_symm_inr
  given: (p : α × β)
  proof: rfl

中文:
引理 optionProdEquiv_symm_inr
  条件: (p : α × β)
  证明: rfl
-/
@[simp] lemma optionProdEquiv_symm_inr (p : α × β) :
  optionProdEquiv.symm (.inr p) = p.map some id := rfl

end
