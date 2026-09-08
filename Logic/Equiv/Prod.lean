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
/-
**Equiv.pprodEquivProd** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：pprodEquivProd {α β} : PProd α β ≃ α × β where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PProd α β` is equivalent to `α × β`
-/
def pprodEquivProd {α β} : PProd α β ≃ α × β where
  toFun x := (x.1, x.2)
  invFun x := ⟨x.1, x.2⟩

/-- Product of two equivalences, in terms of `PProd`. If `α ≃ β` and `γ ≃ δ`, then
`PProd α γ ≃ PProd β δ`. -/
@[simps (attr := grind =) apply symm_apply]
/-
**Equiv.pprodCongr** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：pprodCongr (e₁ : α ≃ β) (e₂ : γ ≃ δ) : PProd α γ ≃ PProd β δ where toFun x
参数：e₁ : α ≃ β；e₂ : γ ≃ δ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Product of two equivalences, in terms of `PProd`. If `α ≃ β` and `γ ≃ δ`, then
`PProd α γ ≃ PProd β δ`.
-/
def pprodCongr (e₁ : α ≃ β) (e₂ : γ ≃ δ) : PProd α γ ≃ PProd β δ where
  toFun x := ⟨e₁ x.1, e₂ x.2⟩
  invFun x := ⟨e₁.symm x.1, e₂.symm x.2⟩
  left_inv := by grind
  right_inv := by grind

/-- Combine two equivalences using `PProd` in the domain and `Prod` in the codomain. -/
@[simps! (attr := grind =) apply symm_apply]
/-
**Equiv.pprodProd** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：pprodProd {α₂ β₂} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) : PProd α₁ β₁ ≃ α₂ × β₂
参数：ea : α₁ ≃ α₂；eb : β₁ ≃ β₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Combine two equivalences using `PProd` in the domain and `Prod` in the codomain.
-/
def pprodProd {α₂ β₂} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) :
    PProd α₁ β₁ ≃ α₂ × β₂ :=
  (ea.pprodCongr eb).trans pprodEquivProd

/-- Combine two equivalences using `PProd` in the codomain and `Prod` in the domain. -/
@[simps! (attr := grind =) apply symm_apply]
/-
**Equiv.prodPProd** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：prodPProd {α₁ β₁} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) : α₁ × β₁ ≃ PProd α₂ β₂
参数：ea : α₁ ≃ α₂；eb : β₁ ≃ β₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Combine two equivalences using `PProd` in the codomain and `Prod` in the domain.
-/
def prodPProd {α₁ β₁} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) :
    α₁ × β₁ ≃ PProd α₂ β₂ :=
  (ea.symm.pprodProd eb.symm).symm

/-- `PProd α β` is equivalent to `PLift α × PLift β` -/
@[simps! (attr := grind =) apply symm_apply]
/-
**Equiv.pprodEquivProdPLift** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：pprodEquivProdPLift : PProd α β ≃ PLift α × PLift β
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`PProd α β` is equivalent to `PLift α × PLift β`
-/
def pprodEquivProdPLift : PProd α β ≃ PLift α × PLift β :=
  Equiv.plift.symm.pprodProd Equiv.plift.symm

/-- Product of two equivalences. If `α₁ ≃ α₂` and `β₁ ≃ β₂`, then `α₁ × β₁ ≃ α₂ × β₂`. This is
`Prod.map` as an equivalence. -/
@[simps (attr := grind =) -fullyApplied apply]
/-
**Equiv.prodCongr** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：prodCongr {α₁ α₂ β₁ β₂} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) : α₁ × β₁ ≃ α₂ × β₂
参数：e₁ : α₁ ≃ α₂；e₂ : β₁ ≃ β₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Product of two equivalences. If `α₁ ≃ α₂` and `β₁ ≃ β₂`, then `α₁ × β₁ ≃ α₂ × β₂
`. This is
`Prod.map` as an equivalence.
-/
def prodCongr {α₁ α₂ β₁ β₂} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) : α₁ × β₁ ≃ α₂ × β₂ :=
  ⟨Prod.map e₁ e₂, Prod.map e₁.symm e₂.symm, fun ⟨a, b⟩ => by simp, fun ⟨a, b⟩ => by simp⟩

@[simp, grind =]
/-
**Equiv.prodCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：prodCongr_symm {α₁ α₂ β₁ β₂} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) : (prodCongr e₁
 e₂).symm = prodCongr e₁.symm e₂.symm
参数：e₁ : α₁ ≃ α₂；e₂ : β₁ ≃ β₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem prodCongr_symm {α₁ α₂ β₁ β₂} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
    (prodCongr e₁ e₂).symm = prodCongr e₁.symm e₂.symm :=
  rfl

/-- Type product is commutative up to an equivalence: `α × β ≃ β × α`. This is `Prod.swap` as an
equivalence. -/
/-
**Equiv.prodComm** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：prodComm (α β) : α × β ≃ β × α where toFun
参数：α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type product is commutative up to an equivalence: `α × β ≃ β × α`. This is `Prod
.swap` as an
equivalence.
-/
def prodComm (α β) : α × β ≃ β × α where
  toFun := Prod.swap
  invFun := Prod.swap

@[simp]
/-
**Equiv.coe_prodComm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：coe_prodComm (α β) : (⇑(prodComm α β) : α × β -> β × α) = Prod.swap
参数：α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodComm (α β) : (⇑(prodComm α β) : α × β → β × α) = Prod.swap :=
  rfl

@[simp, grind =]
/-
**Equiv.prodComm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：prodComm_apply {α β} (x : α × β) : prodComm α β x = x.swap
参数：x : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodComm_apply {α β} (x : α × β) : prodComm α β x = x.swap :=
  rfl

@[simp, grind =]
/-
**Equiv.prodComm_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：prodComm_symm (α β) : (prodComm α β).symm = prodComm β α
参数：α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem prodComm_symm (α β) : (prodComm α β).symm = prodComm β α :=
  rfl

/-- Type product is associative up to an equivalence. -/
@[simps (attr := grind =)]
/-
**Equiv.prodAssoc** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：prodAssoc (α β γ) : (α × β) × γ ≃ α × β × γ
参数：α β γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type product is associative up to an equivalence.
-/
def prodAssoc (α β γ) : (α × β) × γ ≃ α × β × γ :=
  ⟨fun p => (p.1.1, p.1.2, p.2), fun p => ((p.1, p.2.1), p.2.2), fun ⟨⟨_, _⟩, _⟩ => rfl,
    fun ⟨_, ⟨_, _⟩⟩ => rfl⟩

/-- Four-way commutativity of `prod`. The name matches `mul_mul_mul_comm`. -/
@[simps (attr := grind =) apply]
/-
**Equiv.prodProdProdComm** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：prodProdProdComm (α β γ δ) : (α × β) × γ × δ ≃ (α × γ) × β × δ where toFun
 abcd
参数：α β γ δ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Four-way commutativity of `prod`. The name matches `mul_mul_mul_comm`.
-/
def prodProdProdComm (α β γ δ) : (α × β) × γ × δ ≃ (α × γ) × β × δ where
  toFun abcd := ((abcd.1.1, abcd.2.1), (abcd.1.2, abcd.2.2))
  invFun acbd := ((acbd.1.1, acbd.2.1), (acbd.1.2, acbd.2.2))

@[simp, grind =]
/-
**Equiv.prodProdProdComm_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：prodProdProdComm_symm (α β γ δ) : (prodProdProdComm α β γ δ).symm = prodPr
odProdComm α γ β δ
参数：α β γ δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem prodProdProdComm_symm (α β γ δ) :
    (prodProdProdComm α β γ δ).symm = prodProdProdComm α γ β δ :=
  rfl

/-- `γ`-valued functions on `α × β` are equivalent to functions `α → β → γ`. -/
@[simps (attr := grind =) -fullyApplied]
/-
**Equiv.curry** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：curry (α β γ) : (α × β -> γ) ≃ (α -> β -> γ) where toFun
参数：α β γ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.uncurry_curry`：∀ {α : Type u_1} {β : Type u_2} {φ : Sort u_3} (
f : α × β → φ), Function.uncurry (Function.curry f) = f
· 使用定理 `Function.curry_uncurry`：∀ {α : Type u_1} {β : Type u_2} {φ : Sort u_3} (
f : α → β → φ), Function.curry (Function.uncurry f) = f

--- 原说明 ---
`γ`-valued functions on `α × β` are equivalent to functions `α → β → γ`.
-/
def curry (α β γ) : (α × β → γ) ≃ (α → β → γ) where
  toFun := Function.curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

section

/-- `PUnit` is a right identity for type product up to an equivalence. -/
@[simps (attr := grind =)]
/-
**Equiv.prodPUnit** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：prodPUnit (α) : α × PUnit ≃ α where toFun
参数：α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PUnit` is a right identity for type product up to an equivalence.
-/
def prodPUnit (α) : α × PUnit ≃ α where
  toFun := fun p => p.1
  invFun := fun a => (a, PUnit.unit)

/-- `PUnit` is a left identity for type product up to an equivalence. -/
@[simps! (attr := grind =)]
/-
**Equiv.punitProd** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：punitProd (α) : PUnit × α ≃ α
参数：α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PUnit` is a left identity for type product up to an equivalence.
-/
def punitProd (α) : PUnit × α ≃ α :=
  calc
    PUnit × α ≃ α × PUnit := prodComm _ _
    _ ≃ α := prodPUnit _

/-- `PUnit` is a right identity for dependent type product up to an equivalence. -/
@[simps (attr := grind =)]
/-
**Equiv.sigmaPUnit** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：sigmaPUnit (α) : (_ : α) × PUnit ≃ α where toFun
参数：α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PUnit` is a right identity for dependent type product up to an equivalence.
-/
def sigmaPUnit (α) : (_ : α) × PUnit ≃ α where
  toFun := fun p => p.1
  invFun := fun a => ⟨a, PUnit.unit⟩

/-- Any `Unique` type is a right identity for type product up to equivalence. -/
/-
**Equiv.prodUnique** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：prodUnique (α β) [Unique β] : α × β ≃ α
参数：α β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
Any `Unique` type is a right identity for type product up to equivalence.
-/
def prodUnique (α β) [Unique β] : α × β ≃ α :=
  ((Equiv.refl α).prodCongr <| equivPUnit.{_, 1} β).trans <| prodPUnit α

@[simp]
/-
**Equiv.coe_prodUnique** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：coe_prodUnique {α β} [Unique β] : (⇑(prodUnique α β) : α × β -> α) = Prod.
fst
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodUnique {α β} [Unique β] : (⇑(prodUnique α β) : α × β → α) = Prod.fst :=
  rfl
/-
**Equiv.prodUnique_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：prodUnique_apply {α β} [Unique β] (x : α × β) : prodUnique α β x = x.1
参数：x : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodUnique_apply {α β} [Unique β] (x : α × β) : prodUnique α β x = x.1 :=
  rfl

@[simp]
/-
**Equiv.prodUnique_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：prodUnique_symm_apply {α β} [Unique β] (x : α) : (prodUnique α β).symm x =
 (x, default)
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem prodUnique_symm_apply {α β} [Unique β] (x : α) : (prodUnique α β).symm x = (x, default) :=
  rfl

/-- Any `Unique` type is a left identity for type product up to equivalence. -/
/-
**Equiv.uniqueProd** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：uniqueProd (α β) [Unique β] : β × α ≃ α
参数：α β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
Any `Unique` type is a left identity for type product up to equivalence.
-/
def uniqueProd (α β) [Unique β] : β × α ≃ α :=
  ((equivPUnit.{_, 1} β).prodCongr <| Equiv.refl α).trans <| punitProd α

@[simp]
/-
**Equiv.coe_uniqueProd** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：coe_uniqueProd {α β} [Unique β] : (⇑(uniqueProd α β) : β × α -> α) = Prod.
snd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_uniqueProd {α β} [Unique β] : (⇑(uniqueProd α β) : β × α → α) = Prod.snd :=
  rfl
/-
**Equiv.uniqueProd_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：uniqueProd_apply {α β} [Unique β] (x : β × α) : uniqueProd α β x = x.2
参数：x : β × α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniqueProd_apply {α β} [Unique β] (x : β × α) : uniqueProd α β x = x.2 :=
  rfl

@[simp]
/-
**Equiv.uniqueProd_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：uniqueProd_symm_apply {α β} [Unique β] (x : α) : (uniqueProd α β).symm x =
 (default, x)
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem uniqueProd_symm_apply {α β} [Unique β] (x : α) :
    (uniqueProd α β).symm x = (default, x) :=
  rfl

/-- Any family of `Unique` types is a right identity for dependent type product up to
equivalence. -/
/-
**Equiv.sigmaUnique** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：sigmaUnique (α) (β : α -> Type*) [forall a, Unique (β a)] : (a : α) × (β a
) ≃ α
参数：α；β : α -> Type*；β a。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Any family of `Unique` types is a right identity for dependent type product up t
o
equivalence.
-/
def sigmaUnique (α) (β : α → Type*) [∀ a, Unique (β a)] : (a : α) × (β a) ≃ α :=
  (Equiv.sigmaCongrRight fun a ↦ equivPUnit.{_, 1} (β a)).trans <| sigmaPUnit α

@[simp]
/-
**Equiv.coe_sigmaUnique** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：coe_sigmaUnique {α} {β : α -> Type*} [forall a, Unique (β a)] : (⇑(sigmaUn
ique α β) : (a : α) × (β a) -> α) = Sigma.fst
参数：β a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sigmaUnique {α} {β : α → Type*} [∀ a, Unique (β a)] :
    (⇑(sigmaUnique α β) : (a : α) × (β a) → α) = Sigma.fst :=
  rfl
/-
**Equiv.sigmaUnique_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：sigmaUnique_apply {α} {β : α -> Type*} [forall a, Unique (β a)] (x : (a : 
α) × β a) : sigmaUnique α β x = x.1
参数：β a；x : (a : α) × β a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sigmaUnique_apply {α} {β : α → Type*} [∀ a, Unique (β a)] (x : (a : α) × β a) :
    sigmaUnique α β x = x.1 :=
  rfl

@[simp]
/-
**Equiv.sigmaUnique_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：sigmaUnique_symm_apply {α} {β : α -> Type*} [forall a, Unique (β a)] (x : 
α) : (sigmaUnique α β).symm x = ⟨x, default⟩
参数：β a；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem sigmaUnique_symm_apply {α} {β : α → Type*} [∀ a, Unique (β a)] (x : α) :
    (sigmaUnique α β).symm x = ⟨x, default⟩ :=
  rfl

/-- Any `Unique` type is a left identity for type sigma up to equivalence. Compare with `uniqueProd`
which is non-dependent. -/
/-
**Equiv.uniqueSigma** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：uniqueSigma {α} (β : α -> Type*) [Unique α] : (i : α) × β i ≃ β default wh
ere toFun
参数：β : α -> Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any `Unique` type is a left identity for type sigma up to equivalence. Compare w
ith `uniqueProd`
which is non-dependent.
-/
def uniqueSigma {α} (β : α → Type*) [Unique α] : (i : α) × β i ≃ β default where
  toFun := fun p ↦ (Unique.eq_default _).rec p.2
  invFun := fun b ↦ ⟨default, b⟩
  left_inv := fun _ ↦ Sigma.ext (Unique.default_eq _) (eqRec_heq _ _)
/-
**Equiv.uniqueSigma_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：uniqueSigma_apply {α} {β : α -> Type*} [Unique α] (x : (a : α) × β a) : un
iqueSigma β x = (Unique.eq_default _).rec x.2
参数：x : (a : α) × β a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniqueSigma_apply {α} {β : α → Type*} [Unique α] (x : (a : α) × β a) :
    uniqueSigma β x = (Unique.eq_default _).rec x.2 :=
  rfl

@[simp]
/-
**Equiv.uniqueSigma_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：uniqueSigma_symm_apply {α} {β : α -> Type*} [Unique α] (y : β default) : (
uniqueSigma β).symm y = ⟨default, y⟩
参数：y : β default。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem uniqueSigma_symm_apply {α} {β : α → Type*} [Unique α] (y : β default) :
    (uniqueSigma β).symm y = ⟨default, y⟩ :=
  rfl

/-- `Empty` type is a right absorbing element for type product up to an equivalence. -/
/-
**Equiv.prodEmpty** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：prodEmpty (α) : α × Empty ≃ Empty
参数：α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Empty` type is a right absorbing element for type product up to an equivalence.
-/
def prodEmpty (α) : α × Empty ≃ Empty :=
  equivEmpty _

/-- `Empty` type is a left absorbing element for type product up to an equivalence. -/
/-
**Equiv.emptyProd** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：emptyProd (α) : Empty × α ≃ Empty
参数：α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Empty` type is a left absorbing element for type product up to an equivalence.
-/
def emptyProd (α) : Empty × α ≃ Empty :=
  equivEmpty _

/-- `PEmpty` type is a right absorbing element for type product up to an equivalence. -/
/-
**Equiv.prodPEmpty** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：prodPEmpty (α) : α × PEmpty ≃ PEmpty
参数：α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PEmpty` type is a right absorbing element for type product up to an equivalence
.
-/
def prodPEmpty (α) : α × PEmpty ≃ PEmpty :=
  equivPEmpty _

/-- `PEmpty` type is a left absorbing element for type product up to an equivalence. -/
/-
**Equiv.pemptyProd** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：pemptyProd (α) : PEmpty × α ≃ PEmpty
参数：α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PEmpty` type is a left absorbing element for type product up to an equivalence.
-/
def pemptyProd (α) : PEmpty × α ≃ PEmpty :=
  equivPEmpty _

end

section prodCongr

variable {α₁ α₂ β₁ β₂ : Type*} (e : α₁ → β₁ ≃ β₂)

/-- A family of equivalences `∀ (a : α₁), β₁ ≃ β₂` generates an equivalence
between `β₁ × α₁` and `β₂ × α₁`. -/
@[simps apply_fst apply_snd]
/-
**Equiv.prodCongrLeft** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：prodCongrLeft : β₁ × α₁ ≃ β₂ × α₁ where toFun ab
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A family of equivalences `∀ (a : α₁), β₁ ≃ β₂` generates an equivalence
between `β₁ × α₁` and `β₂ × α₁`.
-/
def prodCongrLeft : β₁ × α₁ ≃ β₂ × α₁ where
  toFun ab := ⟨e ab.2 ab.1, ab.2⟩
  invFun ab := ⟨(e ab.2).symm ab.1, ab.2⟩
  left_inv := by grind
  right_inv := by grind

@[simp]
/-
**Equiv.prodCongrLeft_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：prodCongrLeft_apply (b : β₁) (a : α₁) : prodCongrLeft e (b, a) = (e a b, a
)
参数：b : β₁；a : α₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodCongrLeft_apply (b : β₁) (a : α₁) : prodCongrLeft e (b, a) = (e a b, a) :=
  rfl
/-
**Equiv.prodCongr_refl_right** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：prodCongr_refl_right (e : β₁ ≃ β₂) : prodCongr e (Equiv.refl α₁) = prodCon
grLeft fun _ => e
参数：e : β₁ ≃ β₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem prodCongr_refl_right (e : β₁ ≃ β₂) :
    prodCongr e (Equiv.refl α₁) = prodCongrLeft fun _ ↦ e := rfl
/-
**Equiv.prodCongrLeft_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α₁ : Type u_9} {β₁ : Type u_11} {β₂ : Type u_12} (e : α₁ → β₁ ≃ β₂),   
(Equiv.prodCongrLeft e).symm = Equiv.prodCongrLeft (Equiv.symm ∘ e)
参数：e : α₁ → β₁ ≃ β₂；Equiv.prodCongrLeft e；Equiv.symm ∘ e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma prodCongrLeft_symm : (prodCongrLeft e).symm = prodCongrLeft (.symm ∘ e) := rfl

/-- A family of equivalences `∀ (a : α₁), β₁ ≃ β₂` generates an equivalence
between `α₁ × β₁` and `α₁ × β₂`. -/
@[simps apply_fst apply_snd]
/-
**Equiv.prodCongrRight** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：prodCongrRight : α₁ × β₁ ≃ α₁ × β₂ where toFun ab
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A family of equivalences `∀ (a : α₁), β₁ ≃ β₂` generates an equivalence
between `α₁ × β₁` and `α₁ × β₂`.
-/
def prodCongrRight : α₁ × β₁ ≃ α₁ × β₂ where
  toFun ab := ⟨ab.1, e ab.1 ab.2⟩
  invFun ab := ⟨ab.1, (e ab.1).symm ab.2⟩
  left_inv := by grind
  right_inv := by grind

@[simp]
/-
**Equiv.prodCongrRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：prodCongrRight_apply (a : α₁) (b : β₁) : prodCongrRight e (a, b) = (a, e a
 b)
参数：a : α₁；b : β₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodCongrRight_apply (a : α₁) (b : β₁) : prodCongrRight e (a, b) = (a, e a b) :=
  rfl
/-
**Equiv.prodCongr_refl_left** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：prodCongr_refl_left (e : β₁ ≃ β₂) : prodCongr (Equiv.refl α₁) e = prodCong
rRight fun _ => e
参数：e : β₁ ≃ β₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem prodCongr_refl_left (e : β₁ ≃ β₂) :
    prodCongr (Equiv.refl α₁) e = prodCongrRight fun _ ↦ e := rfl
/-
**Equiv.prodCongrRight_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α₁ : Type u_9} {β₁ : Type u_11} {β₂ : Type u_12} (e : α₁ → β₁ ≃ β₂),   
(Equiv.prodCongrRight e).symm = Equiv.prodCongrRight (Equiv.symm ∘ e)
参数：e : α₁ → β₁ ≃ β₂；Equiv.prodCongrRight e；Equiv.symm ∘ e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma prodCongrRight_symm : (prodCongrRight e).symm = prodCongrRight (.symm ∘ e) := rfl

@[simp]
/-
**Equiv.prodCongrLeft_trans_prodComm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：prodCongrLeft_trans_prodComm : (prodCongrLeft e).trans (prodComm _ _) = (p
rodComm _ _).trans (prodCongrRight e)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prodCongrLeft_trans_prodComm :
    (prodCongrLeft e).trans (prodComm _ _) = (prodComm _ _).trans (prodCongrRight e) := by
  ext ⟨a, b⟩ : 1
  simp

@[simp]
/-
**Equiv.prodCongrRight_trans_prodComm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：prodCongrRight_trans_prodComm : (prodCongrRight e).trans (prodComm _ _) = 
(prodComm _ _).trans (prodCongrLeft e)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prodCongrRight_trans_prodComm :
    (prodCongrRight e).trans (prodComm _ _) = (prodComm _ _).trans (prodCongrLeft e) := by
  ext ⟨a, b⟩ : 1
  simp
/-
**Equiv.sigmaCongrRight_sigmaEquivProd** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：sigmaCongrRight_sigmaEquivProd : (sigmaCongrRight e).trans (sigmaEquivProd
 α₁ β₂) = (sigmaEquivProd α₁ β₁).trans (prodCongrRight e)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.sigmaCongrRight_apply`：∀ {α : Type u_3} {β₁ : α → Type u_1} {β₂ : 
α → Type u_2} (F : (a : α) → β₁ a ≃ β₂ a) (a : (a : α) × β₁ a),   (Equiv.sigmaCo
ngrRight F) a = ⟨…
· 使用定理 `Equiv.sigmaEquivProd_apply`：∀ (α : Type u_1) (β : Type u_2) (a : (_ : α)
 × β), (Equiv.sigmaEquivProd α β) a = (a.fst, a.snd)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sigmaCongrRight_sigmaEquivProd :
    (sigmaCongrRight e).trans (sigmaEquivProd α₁ β₂)
    = (sigmaEquivProd α₁ β₁).trans (prodCongrRight e) := by
  ext ⟨a, b⟩ : 1
  simp
/-
**Equiv.sigmaEquivProd_sigmaCongrRight** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：sigmaEquivProd_sigmaCongrRight : (sigmaEquivProd α₁ β₁).symm.trans (sigmaC
ongrRight e) = (prodCongrRight e).trans (sigmaEquivProd α₁ β₂).symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.sigmaCongrRight_apply`：∀ {α : Type u_3} {β₁ : α → Type u_1} {β₂ : 
α → Type u_2} (F : (a : α) → β₁ a ≃ β₂ a) (a : (a : α) × β₁ a),   (Equiv.sigmaCo
ngrRight F) a = ⟨…
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
/-
**Equiv.prodShear** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：prodShear (e₁ : α₁ ≃ α₂) (e₂ : α₁ -> β₁ ≃ β₂) : α₁ × β₁ ≃ α₂ × β₂ where to
Fun
参数：e₁ : α₁ ≃ α₂；e₂ : α₁ -> β₁ ≃ β₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A variation on `Equiv.prodCongr` where the equivalence in the second component c
an depend
  on the first component. A typical example is a shear mapping, explaining the n
ame of this
  declaration.
-/
def prodShear (e₁ : α₁ ≃ α₂) (e₂ : α₁ → β₁ ≃ β₂) : α₁ × β₁ ≃ α₂ × β₂ where
  toFun := fun x : α₁ × β₁ => (e₁ x.1, e₂ x.1 x.2)
  invFun := fun y : α₂ × β₂ => (e₁.symm y.1, (e₂ <| e₁.symm y.1).symm y.2)
  left_inv := by grind
  right_inv := by grind

end prodCongr

namespace Perm

variable {α₁ β₁ : Type*} [DecidableEq α₁] (a : α₁) (e : Perm β₁)

/-- `prodExtendRight a e` extends `e : Perm β` to `Perm (α × β)` by sending `(a, b)` to
`(a, e b)` and keeping the other `(a', b)` fixed. -/
/-
**Equiv.Perm.prodExtendRight** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：prodExtendRight : Perm (α₁ × β₁) where toFun ab
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`prodExtendRight a e` extends `e : Perm β` to `Perm (α × β)` by sending `(a, b)`
 to
`(a, e b)` and keeping the other `(a', b)` fixed.
-/
def prodExtendRight : Perm (α₁ × β₁) where
  toFun ab := if ab.fst = a then (a, e ab.snd) else ab
  invFun ab := if ab.fst = a then (a, e.symm ab.snd) else ab
  left_inv := by grind
  right_inv := by grind

@[simp]
/-
**Equiv.Perm.prodExtendRight_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：prodExtendRight_apply_eq (b : β₁) : prodExtendRight a e (a, b) = (a, e b)
参数：b : β₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem prodExtendRight_apply_eq (b : β₁) : prodExtendRight a e (a, b) = (a, e b) :=
  if_pos rfl
/-
**Equiv.Perm.prodExtendRight_apply_ne** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：prodExtendRight_apply_ne {a a' : α₁} (h : a' != a) (b : β₁) : prodExtendRi
ght a e (a', b) = (a', b)
参数：h : a' != a；b : β₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem prodExtendRight_apply_ne {a a' : α₁} (h : a' ≠ a) (b : β₁) :
    prodExtendRight a e (a', b) = (a', b) :=
  if_neg h
/-
**Equiv.Perm.eq_of_prodExtendRight_ne** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：eq_of_prodExtendRight_ne {e : Perm β₁} {a a' : α₁} {b : β₁} (h : prodExten
dRight a e (a', b) != (a', b)) : a' = a
参数：h : prodExtendRight a e (a', b) != (a', b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Equiv.Perm.prodExtendRight_apply_ne`：prodExtendRight_apply_ne {a a' : α₁
} (h : a' != a) (b : β₁) : prodExtendRight a e (a', b) = (a', b)
-/
theorem eq_of_prodExtendRight_ne {e : Perm β₁} {a a' : α₁} {b : β₁}
    (h : prodExtendRight a e (a', b) ≠ (a', b)) : a' = a := by
  contrapose! h
  exact prodExtendRight_apply_ne _ h _

@[simp]
/-
**Equiv.Perm.fst_prodExtendRight** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：fst_prodExtendRight (ab : α₁ × β₁) : (prodExtendRight a e ab).fst = ab.fst
参数：ab : α₁ × β₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_prodExtendRight (ab : α₁ × β₁) : (prodExtendRight a e ab).fst = ab.fst := by
  grind [prodExtendRight]

end Perm

section

/-- The type of functions to a product `β × γ` is equivalent to the type of pairs of functions
`α → β` and `β → γ`. -/
@[simps]
/-
**Equiv.arrowProdEquivProdArrow** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：arrowProdEquivProdArrow (α : Type*) (β γ : α -> Type*) : ((i : α) -> β i ×
 γ i) ≃ ((i : α) -> β i) × ((i : α) -> γ i) where toFun
参数：α : Type*；β γ : α -> Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of functions to a product `β × γ` is equivalent to the type of pairs of
 functions
`α → β` and `β → γ`.
-/
def arrowProdEquivProdArrow (α : Type*) (β γ : α → Type*) :
    ((i : α) → β i × γ i) ≃ ((i : α) → β i) × ((i : α) → γ i) where
  toFun := fun f => (fun c => (f c).1, fun c => (f c).2)
  invFun := fun p c => (p.1 c, p.2 c)

open Sum

/-- The type of dependent functions on a sum type `ι ⊕ ι'` is equivalent to the type of pairs of
functions on `ι` and on `ι'`. This is a dependent version of `Equiv.sumArrowEquivProdArrow`. -/
@[simps (attr := grind =)]
/-
**Equiv.sumPiEquivProdPi** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：sumPiEquivProdPi {ι ι'} (π : ι oplus ι' -> Type*) : (forall i, π i) ≃ (for
all i, π (inl i)) × forall i', π (inr i') where toFun f
参数：π : ι oplus ι' -> Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of dependent functions on a sum type `ι ⊕ ι'` is equivalent to the type
 of pairs of
functions on `ι` and on `ι'`. This is a dependent version of `Equiv.sumArrowEqui
vProdArrow`.
-/
def sumPiEquivProdPi {ι ι'} (π : ι ⊕ ι' → Type*) :
    (∀ i, π i) ≃ (∀ i, π (inl i)) × ∀ i', π (inr i') where
  toFun f := ⟨fun i => f (inl i), fun i' => f (inr i')⟩
  invFun g := Sum.rec g.1 g.2
  left_inv f := by ext (i | i) <;> rfl

/-- The equivalence between a product of two dependent functions types and a single dependent
function type. Basically a symmetric version of `Equiv.sumPiEquivProdPi`. -/
@[simps! (attr := grind =)]
/-
**Equiv.prodPiEquivSumPi** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：prodPiEquivSumPi {ι ι'} (π : ι -> Type u) (π' : ι' -> Type u) : ((forall i
, π i) × forall i', π' i') ≃ forall i, Sum.elim π π' i
参数：π : ι -> Type u；π' : ι' -> Type u。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The equivalence between a product of two dependent functions types and a single 
dependent
function type. Basically a symmetric version of `Equiv.sumPiEquivProdPi`.
-/
def prodPiEquivSumPi {ι ι'} (π : ι → Type u) (π' : ι' → Type u) :
    ((∀ i, π i) × ∀ i', π' i') ≃ ∀ i, Sum.elim π π' i :=
  sumPiEquivProdPi (Sum.elim π π') |>.symm

/-- The type of functions on a sum type `α ⊕ β` is equivalent to the type of pairs of functions
on `α` and on `β`. -/
/-
**Equiv.sumArrowEquivProdArrow** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：sumArrowEquivProdArrow (α β γ : Type*) : (α oplus β -> γ) ≃ (α -> γ) × (β 
-> γ)
参数：α β γ : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of functions on a sum type `α ⊕ β` is equivalent to the type of pairs o
f functions
on `α` and on `β`.
-/
def sumArrowEquivProdArrow (α β γ : Type*) : (α ⊕ β → γ) ≃ (α → γ) × (β → γ) :=
  ⟨fun f => (f ∘ inl, f ∘ inr), fun p => Sum.elim p.1 p.2, fun f => by ext ⟨⟩ <;> rfl, fun p => by
    cases p
    rfl⟩

@[simp, grind =]
/-
**Equiv.sumArrowEquivProdArrow_apply_fst** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：sumArrowEquivProdArrow_apply_fst {α β γ} (f : α oplus β -> γ) (a : α) : (s
umArrowEquivProdArrow α β γ f).1 a = f (inl a)
参数：f : α oplus β -> γ；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumArrowEquivProdArrow_apply_fst {α β γ} (f : α ⊕ β → γ) (a : α) :
    (sumArrowEquivProdArrow α β γ f).1 a = f (inl a) :=
  rfl

@[simp, grind =]
/-
**Equiv.sumArrowEquivProdArrow_apply_snd** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：sumArrowEquivProdArrow_apply_snd {α β γ} (f : α oplus β -> γ) (b : β) : (s
umArrowEquivProdArrow α β γ f).2 b = f (inr b)
参数：f : α oplus β -> γ；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumArrowEquivProdArrow_apply_snd {α β γ} (f : α ⊕ β → γ) (b : β) :
    (sumArrowEquivProdArrow α β γ f).2 b = f (inr b) :=
  rfl

@[simp, grind =]
/-
**Equiv.sumArrowEquivProdArrow_symm_apply_inl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：sumArrowEquivProdArrow_symm_apply_inl {α β γ} (f : α -> γ) (g : β -> γ) (a
 : α) : ((sumArrowEquivProdArrow α β γ).symm (f, g)) (inl a) = f a
参数：f : α -> γ；g : β -> γ；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem sumArrowEquivProdArrow_symm_apply_inl {α β γ} (f : α → γ) (g : β → γ) (a : α) :
    ((sumArrowEquivProdArrow α β γ).symm (f, g)) (inl a) = f a :=
  rfl

@[simp, grind =]
/-
**Equiv.sumArrowEquivProdArrow_symm_apply_inr** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：sumArrowEquivProdArrow_symm_apply_inr {α β γ} (f : α -> γ) (g : β -> γ) (b
 : β) : ((sumArrowEquivProdArrow α β γ).symm (f, g)) (inr b) = g b
参数：f : α -> γ；g : β -> γ；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem sumArrowEquivProdArrow_symm_apply_inr {α β γ} (f : α → γ) (g : β → γ) (b : β) :
    ((sumArrowEquivProdArrow α β γ).symm (f, g)) (inr b) = g b :=
  rfl

/-- Type product is right distributive with respect to type sum up to an equivalence. -/
/-
**Equiv.sumProdDistrib** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：sumProdDistrib (α β γ) : (α oplus β) × γ ≃ α × γ oplus β × γ
参数：α β γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type product is right distributive with respect to type sum up to an equivalence
.
-/
def sumProdDistrib (α β γ) : (α ⊕ β) × γ ≃ α × γ ⊕ β × γ :=
  ⟨fun p => p.1.map (fun x => (x, p.2)) fun x => (x, p.2),
    fun s => s.elim (Prod.map inl id) (Prod.map inr id), by
      rintro ⟨_ | _, _⟩ <;> rfl, by rintro (⟨_, _⟩ | ⟨_, _⟩) <;> rfl⟩

@[simp, grind =]
/-
**Equiv.sumProdDistrib_apply_left** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：sumProdDistrib_apply_left {α β γ} (a : α) (c : γ) : sumProdDistrib α β γ (
Sum.inl a, c) = Sum.inl (a, c)
参数：a : α；c : γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumProdDistrib_apply_left {α β γ} (a : α) (c : γ) :
    sumProdDistrib α β γ (Sum.inl a, c) = Sum.inl (a, c) :=
  rfl

@[simp, grind =]
/-
**Equiv.sumProdDistrib_apply_right** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：sumProdDistrib_apply_right {α β γ} (b : β) (c : γ) : sumProdDistrib α β γ 
(Sum.inr b, c) = Sum.inr (b, c)
参数：b : β；c : γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumProdDistrib_apply_right {α β γ} (b : β) (c : γ) :
    sumProdDistrib α β γ (Sum.inr b, c) = Sum.inr (b, c) :=
  rfl

@[simp, grind =]
/-
**Equiv.sumProdDistrib_symm_apply_left** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：sumProdDistrib_symm_apply_left {α β γ} (a : α × γ) : (sumProdDistrib α β γ
).symm (inl a) = (inl a.1, a.2)
参数：a : α × γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem sumProdDistrib_symm_apply_left {α β γ} (a : α × γ) :
    (sumProdDistrib α β γ).symm (inl a) = (inl a.1, a.2) :=
  rfl

@[simp, grind =]
/-
**Equiv.sumProdDistrib_symm_apply_right** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：sumProdDistrib_symm_apply_right {α β γ} (b : β × γ) : (sumProdDistrib α β 
γ).symm (inr b) = (inr b.1, b.2)
参数：b : β × γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem sumProdDistrib_symm_apply_right {α β γ} (b : β × γ) :
    (sumProdDistrib α β γ).symm (inr b) = (inr b.1, b.2) :=
  rfl

/-- The product of an indexed sum of types (formally, a `Sigma`-type `Σ i, α i`) by a type `β` is
equivalent to the sum of products `Σ i, (α i × β)`. -/
@[simps (attr := grind =) apply symm_apply]
/-
**Equiv.sigmaProdDistrib** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：sigmaProdDistrib {ι : Type*} (α : ι -> Type*) (β : Type*) : (Σ i, α i) × β
 ≃ Σ i, α i × β
参数：α : ι -> Type*；β : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of an indexed sum of types (formally, a `Sigma`-type `Σ i, α i`) by 
a type `β` is
equivalent to the sum of products `Σ i, (α i × β)`.
-/
def sigmaProdDistrib {ι : Type*} (α : ι → Type*) (β : Type*) : (Σ i, α i) × β ≃ Σ i, α i × β :=
  ⟨fun p => ⟨p.1.1, (p.1.2, p.2)⟩, fun p => (⟨p.1, p.2.1⟩, p.2.2), by grind, by grind⟩

/-- The product `Bool × α` is equivalent to `α ⊕ α`. -/
@[simps (attr := grind =)]
/-
**Equiv.boolProdEquivSum** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：boolProdEquivSum (α) : Bool × α ≃ α oplus α where toFun p
参数：α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product `Bool × α` is equivalent to `α ⊕ α`.
-/
def boolProdEquivSum (α) : Bool × α ≃ α ⊕ α where
  toFun p := if p.1 then (inr p.2) else (inl p.2)
  invFun := Sum.elim (Prod.mk false) (Prod.mk true)
  left_inv := by rintro ⟨_ | _, _⟩ <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

/-- The function type `Bool → α` is equivalent to `α × α`. -/
@[simps (attr := grind =)]
/-
**Equiv.boolArrowEquivProd** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：boolArrowEquivProd (α : Type*) : (Bool -> α) ≃ α × α where toFun f
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function type `Bool → α` is equivalent to `α × α`.
-/
def boolArrowEquivProd (α : Type*) : (Bool → α) ≃ α × α where
  toFun f := (f false, f true)
  invFun p b := if b then p.2 else p.1
  left_inv _ := by grind

end

section

open Subtype

/-- A subtype of a product defined by componentwise conditions
is equivalent to a product of subtypes. -/
/-
**Equiv.subtypeProdEquivProd** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：subtypeProdEquivProd {α β} {p : α -> Prop} {q : β -> Prop} : { c : α × β /
/ p c.1 ∧ q c.2 } ≃ { a // p a } × { b // q b } where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subtype of a product defined by componentwise conditions
is equivalent to a product of subtypes.
-/
def subtypeProdEquivProd {α β} {p : α → Prop} {q : β → Prop} :
    { c : α × β // p c.1 ∧ q c.2 } ≃ { a // p a } × { b // q b } where
  toFun := fun x => ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩
  invFun := fun x => ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩

/-- A subtype of a `Prod` that depends only on the first component is equivalent to the
corresponding subtype of the first type times the second type. -/
/-
**Equiv.prodSubtypeFstEquivSubtypeProd** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：prodSubtypeFstEquivSubtypeProd {α β} {p : α -> Prop} : {s : α × β // p s.1
} ≃ {a // p a} × β where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subtype of a `Prod` that depends only on the first component is equivalent to 
the
corresponding subtype of the first type times the second type.
-/
def prodSubtypeFstEquivSubtypeProd {α β} {p : α → Prop} :
    {s : α × β // p s.1} ≃ {a // p a} × β where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩

/-- A subtype of a `Prod` is equivalent to a sigma type whose fibers are subtypes. -/
/-
**Equiv.subtypeProdEquivSigmaSubtype** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：subtypeProdEquivSigmaSubtype {α β} (p : α -> β -> Prop) : { x : α × β // p
 x.1 x.2 } ≃ Σ a, { b : β // p a b } where toFun x
参数：p : α -> β -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subtype of a `Prod` is equivalent to a sigma type whose fibers are subtypes.
-/
def subtypeProdEquivSigmaSubtype {α β} (p : α → β → Prop) :
    { x : α × β // p x.1 x.2 } ≃ Σ a, { b : β // p a b } where
  toFun x := ⟨x.1.1, x.1.2, x.property⟩
  invFun x := ⟨⟨x.1, x.2⟩, x.2.property⟩

/-- The type `∀ (i : α), β i` can be split as a product by separating the indices in `α`
depending on whether they satisfy a predicate `p` or not. -/
@[simps]
/-
**Equiv.piEquivPiSubtypeProd** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：piEquivPiSubtypeProd {α : Type*} (p : α -> Prop) (β : α -> Type*) [Decidab
lePred p] : (forall i : α, β i) ≃ (forall i : { x // p x }, β i) × forall i : { 
x // ¬p x }, β i where toFun f
参数：p : α -> Prop；β : α -> Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type `∀ (i : α), β i` can be split as a product by separating the indices in
 `α`
depending on whether they satisfy a predicate `p` or not.
-/
def piEquivPiSubtypeProd {α : Type*} (p : α → Prop) (β : α → Type*) [DecidablePred p] :
    (∀ i : α, β i) ≃ (∀ i : { x // p x }, β i) × ∀ i : { x // ¬p x }, β i where
  toFun f := (fun x => f x, fun x => f x)
  invFun f x := if h : p x then f.1 ⟨x, h⟩ else f.2 ⟨x, h⟩
  right_inv := by
    rintro ⟨f, g⟩
    ext1 <;> grind
  left_inv f := by grind

/-- A product of types can be split as the binary product of one of the types and the product
  of all the remaining types. -/
@[simps]
/-
**Equiv.piSplitAt** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：piSplitAt {α : Type*} [DecidableEq α] (i : α) (β : α -> Type*) : (forall j
, β j) ≃ β i × forall j : { j // j != i }, β j where toFun f
参数：i : α；β : α -> Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A product of types can be split as the binary product of one of the types and th
e product
  of all the remaining types.
-/
def piSplitAt {α : Type*} [DecidableEq α] (i : α) (β : α → Type*) :
    (∀ j, β j) ≃ β i × ∀ j : { j // j ≠ i }, β j where
  toFun f := ⟨f i, fun j => f j⟩
  invFun f j := if h : j = i then h.symm.rec f.1 else f.2 ⟨j, h⟩
  right_inv f := by ext x <;> grind
  left_inv f := by grind

/-- A product of copies of a type can be split as the binary product of one copy and the product
  of all the remaining copies. -/
@[simps!]
/-
**Equiv.funSplitAt** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：funSplitAt {α : Type*} [DecidableEq α] (i : α) (β : Type*) : (α -> β) ≃ β 
× ({ j // j != i } -> β)
参数：i : α；β : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A product of copies of a type can be split as the binary product of one copy and
 the product
  of all the remaining copies.
-/
def funSplitAt {α : Type*} [DecidableEq α] (i : α) (β : Type*) :
    (α → β) ≃ β × ({ j // j ≠ i } → β) :=
  piSplitAt i _

end

end Equiv

/-- If `α` is a subsingleton, then it is equivalent to `α × α`. -/
/-
**subsingletonProdSelfEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：subsingletonProdSelfEquiv {α} [Subsingleton α] : α × α ≃ α where toFun p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is a subsingleton, then it is equivalent to `α × α`.
-/
def subsingletonProdSelfEquiv {α} [Subsingleton α] : α × α ≃ α where
  toFun p := p.1
  invFun a := (a, a)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

section

variable {α β : Type*} (a : α) (b : β)

/-- `(1 + α) × β = β + α × β` -/
/-
**optionProdEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：optionProdEquiv : Option α × β ≃ β oplus α × β where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`(1 + α) × β = β + α × β`
-/
def optionProdEquiv : Option α × β ≃ β ⊕ α × β where
  toFun x := x.1.casesOn (.inl x.2) (fun a ↦ .inr (a, x.2))
  invFun x := x.casesOn (.mk none) (.map some id)
  left_inv
  | (none, _) => rfl
  | (some _, _) => rfl
  right_inv
  | .inl _ => rfl
  | .inr (_, _) => rfl
/-
**optionProdEquiv_mk_none** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_9} {β : Type u_10} (b : β), optionProdEquiv (none, b) = Sum.
inl b
参数：b : β；none, b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma optionProdEquiv_mk_none : optionProdEquiv (α := α) (.none, b) = .inl b := rfl
/-
**optionProdEquiv_mk_some** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_9} {β : Type u_10} (a : α) (b : β), optionProdEquiv (some a,
 b) = Sum.inr (a, b)
参数：a : α；b : β；some a, b；a, b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma optionProdEquiv_mk_some : optionProdEquiv (.some a, b) = .inr (a, b) := rfl
/-
**optionProdEquiv_symm_inl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_9} {β : Type u_10} (b : β), optionProdEquiv.symm (Sum.inl b)
 = (none, b)
参数：b : β；Sum.inl b；none, b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma optionProdEquiv_symm_inl : optionProdEquiv (α := α).symm (.inl b) = (.none, b) := rfl
/-
**optionProdEquiv_symm_inr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_9} {β : Type u_10} (p : α × β), optionProdEquiv.symm (Sum.in
r p) = Prod.map some id p
参数：p : α × β；Sum.inr p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma optionProdEquiv_symm_inr (p : α × β) :
  optionProdEquiv.symm (.inr p) = p.map some id := rfl

end

