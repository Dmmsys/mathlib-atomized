/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.GaloisConnection.Basic

/-!
# Heyting regular elements

This file defines Heyting regular elements, elements of a Heyting algebra that are their own double
complement, and proves that they form a Boolean algebra.

From a logic standpoint, this means that we can perform classical logic within intuitionistic logic
by simply double-negating all propositions. This is practical for synthetic computability theory.

## Main declarations

* `IsRegular`: `a` is Heyting-regular if `aᶜᶜ = a`.
* `Regular`: The subtype of Heyting-regular elements.
* `Regular.BooleanAlgebra`: Heyting-regular elements form a Boolean algebra.

## References

* [Francis Borceux, *Handbook of Categorical Algebra III*][borceux-vol3]
-/

@[expose] public section

-- We want the theorems in this file to be intuitionistic.
set_option linter.unusedDecidableInType false

open Function

variable {α : Type*}

namespace Heyting

section Compl

variable [Compl α] {a : α}

/--
Definition of `IsRegular` / `IsRegular` 的定义

English:
definition IsRegular
  signature: (a : α)
  body: aᶜᶜ = a

中文:
定义 是正则
  签名: (a : α)
  定义体: aᶜᶜ = a
-/
def IsRegular (a : α) : Prop :=
  aᶜᶜ = a

/--
theorem `IsRegular.eq` / 定理 `IsRegular.eq`

English:
theorem IsRegular.eq
  statement: IsRegular a -> aᶜᶜ = a
  proof: id

中文:
定理 是正则.eq
  结论: 是正则 a -> aᶜᶜ = a
  证明: id
-/
protected theorem IsRegular.eq : IsRegular a -> aᶜᶜ = a :=
  id

/--
Instance `IsRegular.decidablePred` / 实例 `IsRegular.decidablePred`

English:
instance IsRegular.decidablePred
  signature: [DecidableEq α]
  body: fun _ =>
  ‹DecidableEq α› _ _

中文:
实例 是正则.decidablePred
  签名: [DecidableEq α]
  定义体: fun _ =>
  ‹DecidableEq α› _ _
-/
instance IsRegular.decidablePred [DecidableEq α] : @DecidablePred α IsRegular := fun _ =>
  ‹DecidableEq α› _ _

end Compl

section HeytingAlgebra

variable [HeytingAlgebra α] {a b : α}

/--
theorem `isRegular_bot` / 定理 `isRegular_bot`

English:
theorem isRegular_bot
  statement: IsRegular (⊥ : α)
  proof: by rw [IsRegular, compl_bot, compl_top]

中文:
定理 isRegular_bot
  结论: 是正则 (⊥ : α)
  证明: by rw [IsRegular, compl_bot, compl_top]

Depends on / 依赖: IsRegular, compl_bot, compl_top
-/
theorem isRegular_bot : IsRegular (⊥ : α) := by rw [IsRegular, compl_bot, compl_top]

/--
theorem `isRegular_top` / 定理 `isRegular_top`

English:
theorem isRegular_top
  statement: IsRegular (⊤ : α)
  proof: by rw [IsRegular, compl_top, compl_bot]

中文:
定理 isRegular_top
  结论: 是正则 (⊤ : α)
  证明: by rw [IsRegular, compl_top, compl_bot]

Depends on / 依赖: IsRegular, compl_bot, compl_top
-/
theorem isRegular_top : IsRegular (⊤ : α) := by rw [IsRegular, compl_top, compl_bot]

/--
theorem `IsRegular.inf` / 定理 `IsRegular.inf`

English:
theorem IsRegular.inf
  given: (ha : IsRegular a) (hb : IsRegular b)
  statement: IsRegular (a ⊓ b)
  proof: by
  rw [IsRegular]; rw [compl_compl_inf_distrib]; rw [ha.eq]; rw [hb.eq]

中文:
定理 是正则.下确界
  条件: (ha : 是正则 a) (hb : 是正则 b)
  结论: 是正则 (a ⊓ b)
  证明: by
  rw [IsRegular]; rw [compl_compl_inf_distrib]; rw [ha.eq]; rw [hb.eq]
-/
theorem IsRegular.inf (ha : IsRegular a) (hb : IsRegular b) : IsRegular (a ⊓ b) := by
  rw [IsRegular]; rw [compl_compl_inf_distrib]; rw [ha.eq]; rw [hb.eq]

/--
theorem `IsRegular.himp` / 定理 `IsRegular.himp`

English:
theorem IsRegular.himp
  given: (ha : IsRegular a) (hb : IsRegular b)
  statement: IsRegular (a ⇨ b)
  proof: by
  rw [IsRegular]; rw [compl_compl_himp_distrib]; rw [ha.eq]; rw [hb.eq]

中文:
定理 是正则.himp
  条件: (ha : 是正则 a) (hb : 是正则 b)
  结论: 是正则 (a ⇨ b)
  证明: by
  rw [IsRegular]; rw [compl_compl_himp_distrib]; rw [ha.eq]; rw [hb.eq]

Depends on / 依赖: IsRegular, compl_compl_himp_distrib, ha.eq, hb.eq
-/
theorem IsRegular.himp (ha : IsRegular a) (hb : IsRegular b) : IsRegular (a ⇨ b) := by
  rw [IsRegular]; rw [compl_compl_himp_distrib]; rw [ha.eq]; rw [hb.eq]

/--
theorem `isRegular_compl` / 定理 `isRegular_compl`

English:
theorem isRegular_compl
  given: (a : α)
  statement: IsRegular aᶜ
  proof: compl_compl_compl _

中文:
定理 isRegular_compl
  条件: (a : α)
  结论: 是正则 aᶜ
  证明: compl_compl_compl _

Depends on / 依赖: compl_compl_compl
-/
theorem isRegular_compl (a : α) : IsRegular aᶜ :=
  compl_compl_compl _

/--
theorem `IsRegular.disjoint_compl_left_iff` / 定理 `IsRegular.disjoint_compl_left_iff`

English:
theorem IsRegular.disjoint_compl_left_iff
  given: (ha : IsRegular a)
  proof: by rw [← le_compl_iff_disjoint_left, ha.eq]

中文:
定理 是正则.disjoint_compl_left_iff
  条件: (ha : 是正则 a)
  证明: by rw [← le_compl_iff_disjoint_left, ha.eq]
-/
protected theorem IsRegular.disjoint_compl_left_iff (ha : IsRegular a) :
    Disjoint aᶜ b ↔ b <= a := by rw [← le_compl_iff_disjoint_left, ha.eq]

/--
theorem `IsRegular.disjoint_compl_right_iff` / 定理 `IsRegular.disjoint_compl_right_iff`

English:
theorem IsRegular.disjoint_compl_right_iff
  given: (hb : IsRegular b)
  proof: by rw [← le_compl_iff_disjoint_right, hb.eq]

中文:
定理 是正则.disjoint_compl_right_iff
  条件: (hb : 是正则 b)
  证明: by rw [← le_compl_iff_disjoint_right, hb.eq]
-/
protected theorem IsRegular.disjoint_compl_right_iff (hb : IsRegular b) :
    Disjoint a bᶜ ↔ a <= b := by rw [← le_compl_iff_disjoint_right, hb.eq]

-- See note [reducible non-instances]
/--
Definition of `_root_.BooleanAlgebra.ofRegular` / `_root_.BooleanAlgebra.ofRegular` 的定义

English:
abbreviation _root_.BooleanAlgebra.ofRegular
  signature: (h : forall a : α, IsRegular (a ⊔ aᶜ))
  body: have : forall a : α, IsCompl a aᶜ := fun a =>
    ⟨disjoint_compl_right,
codisjoint_iff.2 by rw [← (h a), compl_sup, inf_compl_eq_bot, compl_bot]⟩
  { ‹HeytingAlgebra α›,
    GeneralizedHeytingAlgebra.toDistribLattice with
    himp_eq := fun _ _ =>
      eq_of_forall_le_iff fun _ => le_himp_iff.trans (this _).le_sup_right_iff_inf_left_le.symm
    inf_compl_le_bot := fun _ => (this _).1.le_bot
    top_le_sup_compl := fun _ => (this _).2.top_le }

中文:
缩写 _root_.布尔代数.ofRegular
  签名: (h : 对任意 a : α, 是正则 (a ⊔ aᶜ))
  定义体: have : forall a : α, IsCompl a aᶜ := fun a =>
    ⟨disjoint_compl_right,
codisjoint_iff.2 by rw [← (h a), compl_sup, inf_compl_eq_bot, compl_bot]⟩
  { ‹HeytingAlgebra α›,
    GeneralizedHeytingAlgebra.toDistribLattice with
    himp_eq := fun _ _ =>
      eq_of_forall_le_iff fun _ => le_himp_iff.trans (this _).le_sup_right_iff_inf_left_le.symm
    inf_compl_le_bot := fun _ => (this _).1.le_bot
    top_le_sup_compl := fun _ => (this _).2.top_le }

Depends on / 依赖: GeneralizedHeytingAlgebra, GeneralizedHeytingAlgebra.toDistribLattice, HeytingAlgebra, IsCompl, codisjoint_iff, compl_bot, compl_sup, disjoint_compl_right, eq_of_forall_le_iff, himp_eq, inf_compl_eq_bot, inf_compl_le_bot, le_bot, le_himp_iff, le_himp_iff.trans, le_sup_right_iff_inf_left_le, le_sup_right_iff_inf_left_le.symm, toDistribLattice, top_le, top_le_sup_compl
-/
abbrev _root_.BooleanAlgebra.ofRegular (h : forall a : α, IsRegular (a ⊔ aᶜ)) : BooleanAlgebra α :=
  have : forall a : α, IsCompl a aᶜ := fun a =>
    ⟨disjoint_compl_right,
codisjoint_iff.2 by rw [← (h a), compl_sup, inf_compl_eq_bot, compl_bot]⟩
  { ‹HeytingAlgebra α›,
    GeneralizedHeytingAlgebra.toDistribLattice with
    himp_eq := fun _ _ =>
      eq_of_forall_le_iff fun _ => le_himp_iff.trans (this _).le_sup_right_iff_inf_left_le.symm
    inf_compl_le_bot := fun _ => (this _).1.le_bot
    top_le_sup_compl := fun _ => (this _).2.top_le }

variable (α)

/--
Definition of `Regular` / `Regular` 的定义

English:
definition Regular
  signature: : Type _
  body: { a : α // IsRegular a }

中文:
定义 正则
  签名: : 类型 _
  定义体: { a : α // IsRegular a }

Depends on / 依赖: IsRegular
-/
def Regular : Type _ :=
  { a : α // IsRegular a }

variable {α}

namespace Regular

/--
Definition of `val` / `val` 的定义

English:
definition val
  signature: : Regular α -> α
  body: Subtype.val

中文:
定义 val
  签名: : 正则 α -> α
  定义体: Subtype.val
-/
@[coe] def val : Regular α -> α :=
  Subtype.val

/--
theorem `prop` / 定理 `prop`

English:
theorem prop
  statement: forall a : Regular α, IsRegular a.val
  proof: Subtype.prop

中文:
定理 prop
  结论: 对任意 a : 正则 α, 是正则 a.val
  证明: Subtype.prop

Depends on / 依赖: Subtype, Subtype.prop
-/
theorem prop : forall a : Regular α, IsRegular a.val := Subtype.prop

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeOut (Regular α) α
  body: ⟨Regular.val⟩

中文:
实例 :
  签名: CoeOut (正则 α) α
  定义体: ⟨Regular.val⟩

Depends on / 依赖: Regular, Regular.val
-/
instance : CoeOut (Regular α) α := ⟨Regular.val⟩

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Injective ((↑) : Regular α -> α)
  proof: Subtype.coe_injective

@[simp]

中文:
定理 coe_injective
  结论: 单射 ((↑) : 正则 α -> α)
  证明: Subtype.coe_injective

@[simp]

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
theorem coe_injective : Injective ((↑) : Regular α -> α) :=
  Subtype.coe_injective

@[simp]
/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: {a b : Regular α}
  statement: (a : α) = b ↔ a = b
  proof: Subtype.coe_inj

中文:
定理 coe_inj
  条件: {a b : 正则 α}
  结论: (a : α) = b ↔ a = b
  证明: Subtype.coe_inj

Depends on / 依赖: Subtype, Subtype.coe_inj, coe_inj
-/
theorem coe_inj {a b : Regular α} : (a : α) = b ↔ a = b :=
  Subtype.coe_inj

/--
Instance `top` / 实例 `top`

English:
instance top
  signature: : Top (Regular α)
  body: ⟨⟨⊤, isRegular_top⟩⟩

中文:
实例 top
  签名: : 顶元素 (正则 α)
  定义体: ⟨⟨⊤, isRegular_top⟩⟩

Depends on / 依赖: isRegular_top
-/
instance top : Top (Regular α) :=
  ⟨⟨⊤, isRegular_top⟩⟩

/--
Instance `bot` / 实例 `bot`

English:
instance bot
  signature: : Bot (Regular α)
  body: ⟨⟨⊥, isRegular_bot⟩⟩

中文:
实例 bot
  签名: : 底元素 (正则 α)
  定义体: ⟨⟨⊥, isRegular_bot⟩⟩

Depends on / 依赖: isRegular_bot
-/
instance bot : Bot (Regular α) :=
  ⟨⟨⊥, isRegular_bot⟩⟩

/--
Instance `inf` / 实例 `inf`

English:
instance inf
  signature: : Min (Regular α)
  body: ⟨fun a b => ⟨a ⊓ b, a.2.inf b.2⟩⟩

中文:
实例 下确界
  签名: : 最小值 (正则 α)
  定义体: ⟨fun a b => ⟨a ⊓ b, a.2.inf b.2⟩⟩
-/
instance inf : Min (Regular α) :=
  ⟨fun a b => ⟨a ⊓ b, a.2.inf b.2⟩⟩

/--
Instance `himp` / 实例 `himp`

English:
instance himp
  signature: : HImp (Regular α)
  body: ⟨fun a b => ⟨a ⇨ b, a.2.himp b.2⟩⟩

中文:
实例 himp
  签名: : HImp (正则 α)
  定义体: ⟨fun a b => ⟨a ⇨ b, a.2.himp b.2⟩⟩
-/
instance himp : HImp (Regular α) :=
  ⟨fun a b => ⟨a ⇨ b, a.2.himp b.2⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Compl (Regular α)
  body: ⟨fun a => ⟨aᶜ, isRegular_compl _⟩⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 补集 (正则 α)
  定义体: ⟨fun a => ⟨aᶜ, isRegular_compl _⟩⟩

@[simp, norm_cast]

Depends on / 依赖: isRegular_compl
-/
instance : Compl (Regular α) :=
  ⟨fun a => ⟨aᶜ, isRegular_compl _⟩⟩

@[simp, norm_cast]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  statement: ((⊤ : Regular α) : α) = ⊤
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_top
  结论: ((⊤ : 正则 α) : α) = ⊤
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_top : ((⊤ : Regular α) : α) = ⊤ :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  statement: ((⊥ : Regular α) : α) = ⊥
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_bot
  结论: ((⊥ : 正则 α) : α) = ⊥
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_bot : ((⊥ : Regular α) : α) = ⊥ :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: (a b : Regular α)
  statement: (↑(a ⊓ b) : α) = (a : α) ⊓ b
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_inf
  条件: (a b : 正则 α)
  结论: (↑(a ⊓ b) : α) = (a : α) ⊓ b
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_inf (a b : Regular α) : (↑(a ⊓ b) : α) = (a : α) ⊓ b :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_himp` / 定理 `coe_himp`

English:
theorem coe_himp
  given: (a b : Regular α)
  statement: (↑(a ⇨ b) : α) = (a : α) ⇨ b
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_himp
  条件: (a b : 正则 α)
  结论: (↑(a ⇨ b) : α) = (a : α) ⇨ b
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_himp (a b : Regular α) : (↑(a ⇨ b) : α) = (a : α) ⇨ b :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_compl` / 定理 `coe_compl`

English:
theorem coe_compl
  given: (a : Regular α)
  statement: (↑aᶜ : α) = (a : α)ᶜ
  proof: rfl

中文:
定理 coe_compl
  条件: (a : 正则 α)
  结论: (↑aᶜ : α) = (a : α)ᶜ
  证明: rfl
-/
theorem coe_compl (a : Regular α) : (↑aᶜ : α) = (a : α)ᶜ :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Regular α)
  body: ⟨⊥⟩

中文:
实例 :
  签名: 可居 (正则 α)
  定义体: ⟨⊥⟩
-/
instance : Inhabited (Regular α) :=
  ⟨⊥⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Regular α)
  body: PartialOrder.lift _ coe_injective

中文:
实例 :
  签名: 偏序 (正则 α)
  定义体: PartialOrder.lift _ coe_injective

Depends on / 依赖: PartialOrder, PartialOrder.lift, coe_injective
-/
instance : PartialOrder (Regular α) :=
  PartialOrder.lift _ coe_injective

/--
Instance `boundedOrder` / 实例 `boundedOrder`

English:
instance boundedOrder
  signature: : BoundedOrder (Regular α)
  body: BoundedOrder.lift ((↑) : Regular α -> α) (fun _ _ => id) coe_top coe_bot

@[simp, norm_cast]

中文:
实例 boundedOrder
  签名: : 有界序 (正则 α)
  定义体: BoundedOrder.lift ((↑) : Regular α -> α) (fun _ _ => id) coe_top coe_bot

@[simp, norm_cast]

Depends on / 依赖: BoundedOrder, BoundedOrder.lift, Regular, coe_bot, coe_top
-/
instance boundedOrder : BoundedOrder (Regular α) :=
  BoundedOrder.lift ((↑) : Regular α -> α) (fun _ _ => id) coe_top coe_bot

@[simp, norm_cast]
/--
theorem `coe_le_coe` / 定理 `coe_le_coe`

English:
theorem coe_le_coe
  given: {a b : Regular α}
  statement: (a : α) <= b ↔ a <= b
  proof: Iff.rfl

@[simp, norm_cast]

中文:
定理 coe_le_coe
  条件: {a b : 正则 α}
  结论: (a : α) <= b ↔ a <= b
  证明: Iff.rfl

@[simp, norm_cast]

Depends on / 依赖: Iff.rfl
-/
theorem coe_le_coe {a b : Regular α} : (a : α) <= b ↔ a <= b :=
  Iff.rfl

@[simp, norm_cast]
/--
theorem `coe_lt_coe` / 定理 `coe_lt_coe`

English:
theorem coe_lt_coe
  given: {a b : Regular α}
  statement: (a : α) < b ↔ a < b
  proof: Iff.rfl

中文:
定理 coe_lt_coe
  条件: {a b : 正则 α}
  结论: (a : α) < b ↔ a < b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem coe_lt_coe {a b : Regular α} : (a : α) < b ↔ a < b :=
  Iff.rfl

/--
Definition of `toRegular` / `toRegular` 的定义

English:
definition toRegular
  signature: : α ->o Regular α
  body: ⟨fun a => ⟨aᶜᶜ, isRegular_compl _⟩, fun _ _ h =>
coe_le_coe.1 compl_le_compl compl_le_compl h⟩

@[simp, norm_cast]

中文:
定义 toRegular
  签名: : α ->o 正则 α
  定义体: ⟨fun a => ⟨aᶜᶜ, isRegular_compl _⟩, fun _ _ h =>
coe_le_coe.1 compl_le_compl compl_le_compl h⟩

@[simp, norm_cast]

Depends on / 依赖: coe_le_coe, compl_le_compl, isRegular_compl
-/
def toRegular : α ->o Regular α :=
  ⟨fun a => ⟨aᶜᶜ, isRegular_compl _⟩, fun _ _ h =>
coe_le_coe.1 compl_le_compl compl_le_compl h⟩

@[simp, norm_cast]
/--
theorem `coe_toRegular` / 定理 `coe_toRegular`

English:
theorem coe_toRegular
  given: (a : α)
  statement: (toRegular a : α) = aᶜᶜ
  proof: rfl

@[simp]

中文:
定理 coe_toRegular
  条件: (a : α)
  结论: (toRegular a : α) = aᶜᶜ
  证明: rfl

@[simp]
-/
theorem coe_toRegular (a : α) : (toRegular a : α) = aᶜᶜ :=
  rfl

@[simp]
/--
theorem `toRegular_coe` / 定理 `toRegular_coe`

English:
theorem toRegular_coe
  given: (a : Regular α)
  statement: toRegular (a : α) = a
  proof: coe_injective a.2

中文:
定理 toRegular_coe
  条件: (a : 正则 α)
  结论: toRegular (a : α) = a
  证明: coe_injective a.2

Depends on / 依赖: coe_injective
-/
theorem toRegular_coe (a : Regular α) : toRegular (a : α) = a :=
  coe_injective a.2

/--
Definition of `gi` / `gi` 的定义

English:
definition gi
  signature: : GaloisInsertion toRegular ((↑) : Regular α -> α) where
  body: ⟨a, ha.antisymm le_compl_compl⟩
  gc _ b :=
coe_le_coe.symm.trans
      ⟨le_compl_compl.trans, fun h => (compl_anti <| compl_anti h).trans_eq b.2⟩
  le_l_u _ := le_compl_compl
choice_eq _ ha := coe_injective le_compl_compl.antisymm ha

中文:
定义 gi
  签名: : Galois嵌入 toRegular ((↑) : 正则 α -> α) where
  定义体: ⟨a, ha.antisymm le_compl_compl⟩
  gc _ b :=
coe_le_coe.symm.trans
      ⟨le_compl_compl.trans, fun h => (compl_anti <| compl_anti h).trans_eq b.2⟩
  le_l_u _ := le_compl_compl
choice_eq _ ha := coe_injective le_compl_compl.antisymm ha

Depends on / 依赖: antisymm, ha.antisymm, le_compl_compl
-/
def gi : GaloisInsertion toRegular ((↑) : Regular α -> α) where
  choice a ha := ⟨a, ha.antisymm le_compl_compl⟩
  gc _ b :=
coe_le_coe.symm.trans
      ⟨le_compl_compl.trans, fun h => (compl_anti <| compl_anti h).trans_eq b.2⟩
  le_l_u _ := le_compl_compl
choice_eq _ ha := coe_injective le_compl_compl.antisymm ha

/--
Instance `lattice` / 实例 `lattice`

English:
instance lattice
  signature: : Lattice (Regular α)
  body: gi.liftLattice

@[simp, norm_cast]

中文:
实例 lattice
  签名: : 格 (正则 α)
  定义体: gi.liftLattice

@[simp, norm_cast]

Depends on / 依赖: gi.liftLattice, liftLattice
-/
instance lattice : Lattice (Regular α) :=
  gi.liftLattice

@[simp, norm_cast]
/--
theorem `coe_sup` / 定理 `coe_sup`

English:
theorem coe_sup
  given: (a b : Regular α)
  statement: (↑(a ⊔ b) : α) = ((a : α) ⊔ b)ᶜᶜ
  proof: rfl

中文:
定理 coe_sup
  条件: (a b : 正则 α)
  结论: (↑(a ⊔ b) : α) = ((a : α) ⊔ b)ᶜᶜ
  证明: rfl
-/
theorem coe_sup (a b : Regular α) : (↑(a ⊔ b) : α) = ((a : α) ⊔ b)ᶜᶜ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BooleanAlgebra (Regular α)
  body: { Regular.lattice, Regular.boundedOrder, Regular.himp,
    Regular.instCompl with
    le_sup_inf := fun a b c =>
coe_le_coe.1 by
        dsimp
        rw [sup_inf_left]; rw [compl_compl_inf_distrib]
inf_compl_le_bot := fun _ => coe_le_coe.1 disjoint_iff_inf_le.1 disjoint_compl_right
    top_le_sup_compl := fun a =>
coe_le_coe.1 by
        dsimp
        rw [compl_sup]; rw [inf_compl_eq_bot]; rw [compl_bot]
    himp_eq := fun a b =>
      coe_injective
        (by
          dsimp
          rw [compl_sup]; rw [a.prop.eq]
          refine eq_of_forall_le_iff fun c => le_himp_iff.trans ?_
          rw [le_compl_iff_disjoint_right]; rw [disjoint_left_comm]
          rw [b.prop.disjoint_compl_left_iff]) }

@[simp, norm_cast]

中文:
实例 :
  签名: 布尔代数 (正则 α)
  定义体: { Regular.lattice, Regular.boundedOrder, Regular.himp,
    Regular.instCompl with
    le_sup_inf := fun a b c =>
coe_le_coe.1 by
        dsimp
        rw [sup_inf_left]; rw [compl_compl_inf_distrib]
inf_compl_le_bot := fun _ => coe_le_coe.1 disjoint_iff_inf_le.1 disjoint_compl_right
    top_le_sup_compl := fun a =>
coe_le_coe.1 by
        dsimp
        rw [compl_sup]; rw [inf_compl_eq_bot]; rw [compl_bot]
    himp_eq := fun a b =>
      coe_injective
        (by
          dsimp
          rw [compl_sup]; rw [a.prop.eq]
          refine eq_of_forall_le_iff fun c => le_himp_iff.trans ?_
          rw [le_compl_iff_disjoint_right]; rw [disjoint_left_comm]
          rw [b.prop.disjoint_compl_left_iff]) }

@[simp, norm_cast]

Depends on / 依赖: Regular, Regular.boundedOrder, Regular.himp, Regular.instCompl, Regular.lattice, a.prop.eq, boundedOrder, coe_injective, coe_le_coe, compl_bot, compl_compl_inf_distrib, compl_sup, disjoint_compl_right, disjoint_iff_inf_le, eq_of_forall_le_iff, himp_eq, inf_compl_eq_bot, inf_compl_le_bot, instCompl, lattice
-/
instance : BooleanAlgebra (Regular α) :=
  { Regular.lattice, Regular.boundedOrder, Regular.himp,
    Regular.instCompl with
    le_sup_inf := fun a b c =>
coe_le_coe.1 by
        dsimp
        rw [sup_inf_left]; rw [compl_compl_inf_distrib]
inf_compl_le_bot := fun _ => coe_le_coe.1 disjoint_iff_inf_le.1 disjoint_compl_right
    top_le_sup_compl := fun a =>
coe_le_coe.1 by
        dsimp
        rw [compl_sup]; rw [inf_compl_eq_bot]; rw [compl_bot]
    himp_eq := fun a b =>
      coe_injective
        (by
          dsimp
          rw [compl_sup]; rw [a.prop.eq]
          refine eq_of_forall_le_iff fun c => le_himp_iff.trans ?_
          rw [le_compl_iff_disjoint_right]; rw [disjoint_left_comm]
          rw [b.prop.disjoint_compl_left_iff]) }

@[simp, norm_cast]
/--
theorem `coe_sdiff` / 定理 `coe_sdiff`

English:
theorem coe_sdiff
  given: (a b : Regular α)
  statement: (↑(a \ b) : α) = (a : α) ⊓ bᶜ
  proof: rfl

中文:
定理 coe_sdiff
  条件: (a b : 正则 α)
  结论: (↑(a \ b) : α) = (a : α) ⊓ bᶜ
  证明: rfl
-/
theorem coe_sdiff (a b : Regular α) : (↑(a \ b) : α) = (a : α) ⊓ bᶜ :=
  rfl

end Regular

end HeytingAlgebra

variable [BooleanAlgebra α]

/--
theorem `isRegular_of_boolean` / 定理 `isRegular_of_boolean`

English:
theorem isRegular_of_boolean
  statement: forall a : α, IsRegular a
  proof: compl_compl

中文:
定理 isRegular_of_boolean
  结论: 对任意 a : α, 是正则 a
  证明: compl_compl

Depends on / 依赖: compl_compl
-/
theorem isRegular_of_boolean : forall a : α, IsRegular a :=
  compl_compl

/--
theorem `isRegular_of_decidable` / 定理 `isRegular_of_decidable`

English:
theorem isRegular_of_decidable
  given: (p : Prop) [Decidable p]
  statement: IsRegular p
  proof: propext Decidable.not_not

中文:
定理 isRegular_of_decidable
  条件: (p : 命题) [可判定 p]
  结论: 是正则 p
  证明: propext Decidable.not_not

Depends on / 依赖: Decidable, Decidable.not_not, not_not, propext
-/
theorem isRegular_of_decidable (p : Prop) [Decidable p] : IsRegular p :=
propext Decidable.not_not

end Heyting
