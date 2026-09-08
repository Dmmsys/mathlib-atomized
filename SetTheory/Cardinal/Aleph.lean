/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Order.Monoid.Basic
public import Mathlib.SetTheory.Cardinal.Cofinality.Enum
public import Mathlib.SetTheory.Cardinal.ToNat
public import Mathlib.SetTheory.Cardinal.ENat
public import Mathlib.SetTheory.Ordinal.Enum
public import Mathlib.SetTheory.Ordinal.Univ

import Mathlib.SetTheory.Ordinal.Principal

/-!
# Omega, aleph, and beth functions

This file defines the `ω`, `ℵ`, and `ℶ` functions which enumerate certain kinds of ordinals and
cardinals. Each is provided in two variants: the standard versions which only take infinite values,
and "preliminary" versions which include finite values and are sometimes more convenient.

* The function `Ordinal.preOmega` enumerates the initial ordinals, i.e. the smallest ordinals with
  any given cardinality. Thus `preOmega n = n`, `preOmega ω = ω`, `preOmega (ω + 1) = ω₁`, etc.
  `Ordinal.omega` is the more standard function which skips over finite ordinals.
* The function `Cardinal.preAleph` is an order isomorphism between ordinals and cardinals. Thus
  `preAleph n = n`, `preAleph ω = ℵ₀`, `preAleph (ω + 1) = ℵ₁`, etc. `Cardinal.aleph` is the more
  standard function which skips over finite cardinals.
* The function `Cardinal.preBeth` is the unique normal function with `beth 0 = 0` and
  `beth (succ o) = 2 ^ beth o`. `Cardinal.beth` is the more standard function which skips over
  finite cardinals.

## Notation

The following notations are scoped to the `Ordinal` namespace.

- `ω_ o` is notation for `Ordinal.omega o`. `ω₁` is notation for `ω_ 1`.

The following notations are scoped to the `Cardinal` namespace.

- `ℵ_ o` is notation for `aleph o`. `ℵ₁` is notation for `ℵ_ 1`.
- `ℶ_ o` is notation for `beth o`. The value `ℶ_ 1` equals the continuum `𝔠`, which is defined in
  `Mathlib/SetTheory/Cardinal/Continuum.lean`.
-/

@[expose] public section

assert_not_exists Field Finsupp Module Cardinal.mul_eq_self

noncomputable section

open Function Set Cardinal Equiv Order Ordinal

universe u v w

/-! ### Omega ordinals -/

namespace Ordinal

/-- An ordinal is initial when it is the first ordinal with a given cardinality.

This is written as `o.card.ord = o`, i.e. `o` is the smallest ordinal with cardinality `o.card`. -/
/-
**Ordinal.IsInitial** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：IsInitial (o : Ordinal) : Prop
参数：o : Ordinal。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ordinal is initial when it is the first ordinal with a given cardinality.

This is written as `o.card.ord = o`, i.e. `o` is the smallest ordinal with cardi
nality `o.card`.
-/
def IsInitial (o : Ordinal) : Prop :=
  o.card.ord = o
/-
**Ordinal.IsInitial.ord_card** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsInitial`。
形式化陈述：∀ {o : Ordinal.{u_1}}, o.IsInitial → o.card.ord = o
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsInitial.ord_card {o : Ordinal} (h : IsInitial o) : o.card.ord = o := h
/-
**Ordinal.IsInitial.le_ord_iff_card_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsInit
ial`。
形式化陈述：∀ {o : Ordinal.{u_1}}, o.IsInitial → ∀ (c : Cardinal.{u_1}), o ≤ c.ord ↔ o
.card ≤ c
参数：c : Cardinal.{u_1}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.ord_le_ord`：ord_le_ord {c₁ c₂} : ord c₁ <= ord c₂ ↔ c₁ <= c₂
· 使用定理 `Ordinal.IsInitial.ord_card`：∀ {o : Ordinal.{u_1}}, o.IsInitial → o.card.
ord = o
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem IsInitial.le_ord_iff_card_le {o : Ordinal} (ho : o.IsInitial) (c : Cardinal) :
    o ≤ c.ord ↔ o.card ≤ c := by
  grw [← ord_le_ord, ho.ord_card]
/-
**Ordinal.IsInitial.card_le_card** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsInitial`。
形式化陈述：∀ {a b : Ordinal.{u_1}}, a.IsInitial → (a.card ≤ b.card ↔ a ≤ b)
参数：a.card ≤ b.card ↔ a ≤ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.IsInitial.le_ord_iff_card_le`：∀ {o : Ordinal.{u_1}}, o.IsInitial
 → ∀ (c : Cardinal.{u_1}), o ≤ c.ord ↔ o.card ≤ c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Cardinal.ord_card_le`：ord_card_le (o : Ordinal) : o.card.ord <= o
· 使用定理 `Ordinal.card_le_card`：card_le_card {o₁ o₂ : Ordinal} : o₁ <= o₂ -> card 
o₁ <= card o₂
-/
theorem IsInitial.card_le_card {a b : Ordinal} (ha : IsInitial a) : a.card ≤ b.card ↔ a ≤ b := by
  refine ⟨fun h ↦ ?_, Ordinal.card_le_card⟩
  rw [← ha.le_ord_iff_card_le] at h
  grw [h, ord_card_le]
/-
**Ordinal.IsInitial.card_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsInitial`。
形式化陈述：∀ {a b : Ordinal.{u_1}}, b.IsInitial → (a.card < b.card ↔ a < b)
参数：a.card < b.card ↔ a < b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `Ordinal.IsInitial.card_le_card`：∀ {a b : Ordinal.{u_1}}, a.IsInitial → (
a.card ≤ b.card ↔ a ≤ b)
-/
theorem IsInitial.card_lt_card {a b : Ordinal} (hb : IsInitial b) : a.card < b.card ↔ a < b :=
  lt_iff_lt_of_le_iff_le hb.card_le_card
/-
**Ordinal.isInitial_ord** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isInitial_ord (c : Cardinal) : IsInitial c.ord
参数：c : Cardinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.IsInitial.eq_1`：∀ (o : Ordinal.{u_1}), o.IsInitial = (o.card.ord
 = o)
· 使用定理 `Cardinal.card_ord`：card_ord (c) : (ord c).card = c
-/
theorem isInitial_ord (c : Cardinal) : IsInitial c.ord := by
  rw [IsInitial, card_ord]

@[simp]
/-
**Ordinal.isInitial_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isInitial_natCast (n : Nat) : IsInitial n
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.IsInitial.eq_1`：∀ (o : Ordinal.{u_1}), o.IsInitial = (o.card.ord
 = o)
· 使用定理 `Ordinal.card_nat`：card_nat (n : Nat) : card.{u} n = n
· 使用定理 `Cardinal.ord_natCast`：ord_natCast (n : Nat) : ord n = n
-/
theorem isInitial_natCast (n : ℕ) : IsInitial n := by
  rw [IsInitial, card_nat, ord_natCast]
/-
**Ordinal.isInitial_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isInitial_zero : IsInitial 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.isInitial_natCast`：isInitial_natCast (n : Nat) : IsInitial n
-/
theorem isInitial_zero : IsInitial 0 := by
  exact_mod_cast isInitial_natCast 0
/-
**Ordinal.isInitial_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isInitial_one : IsInitial 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.isInitial_natCast`：isInitial_natCast (n : Nat) : IsInitial n
-/
theorem isInitial_one : IsInitial 1 := by
  exact_mod_cast isInitial_natCast 1
/-
**Ordinal.isInitial_omega0** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isInitial_omega0 : IsInitial ω
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.IsInitial.eq_1`：∀ (o : Ordinal.{u_1}), o.IsInitial = (o.card.ord
 = o)
· 使用定理 `Ordinal.card_omega0`：card_omega0 : card ω = ℵ₀
· 使用定理 `Cardinal.ord_aleph0`：ord_aleph0 : ord.{u} ℵ₀ = ω
-/
theorem isInitial_omega0 : IsInitial ω := by
  rw [IsInitial, card_omega0, ord_aleph0]
/-
**Ordinal.isInitial_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isInitial_succ {o : Ordinal} : IsInitial (succ o) ↔ o < ω
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.mtr`：∀ {a b : Prop}, (¬a → ¬b) → b → a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Ordinal.card_add`：card_add (o₁ o₂ : Ordinal) : card (o₁ + o₂) = card o₁ 
+ card o₂
· 使用定理 `Ordinal.card_one`：card_one : card 1 = 1
· 使用定理 `Cardinal.add_one_of_aleph0_le`：add_one_of_aleph0_le {c} (h : ℵ₀ <= c) : 
c + 1 = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Ordinal.isInitial_natCast`：isInitial_natCast (n : Nat) : IsInitial n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.lt_omega0`：lt_omega0 {o : Ordinal} : o < ω ↔ exists n : Nat, o =
 n
-/
theorem isInitial_succ {o : Ordinal} : IsInitial (succ o) ↔ o < ω :=
  ⟨Function.mtr fun hwo ↦ ne_of_lt <| by simp_all [ord_card_le],
  fun how ↦ (Ordinal.lt_omega0.1 how).rec fun n h ↦ h ▸ isInitial_natCast (n + 1)⟩
/-
**Ordinal.not_bddAbove_isInitial** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：not_bddAbove_isInitial : ¬ BddAbove {x | IsInitial x}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.isInitial_ord`：isInitial_ord (c : Cardinal) : IsInitial c.ord
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `Cardinal.instNoMaxOrder`：NoMaxOrder Cardinal.{u}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.ord_le`：ord_le {c o} : ord c <= o ↔ c <= o.card
-/
theorem not_bddAbove_isInitial : ¬ BddAbove {x | IsInitial x} := by
  rintro ⟨a, ha⟩
  have := ha (isInitial_ord (succ a.card))
  rw [ord_le] at this
  exact (lt_succ _).not_ge this

/-- Initial ordinals are order-isomorphic to the cardinals. -/
@[simps!]
/-
**Ordinal.isInitialIso** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：isInitialIso : {x // IsInitial x} ≃o Cardinal where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.isInitial_ord`：isInitial_ord (c : Cardinal) : IsInitial c.ord
· 使用定理 `Cardinal.card_ord`：card_ord (c) : (ord c).card = c

--- 原说明 ---
Initial ordinals are order-isomorphic to the cardinals.
-/
def isInitialIso : {x // IsInitial x} ≃o Cardinal where
  toFun x := x.1.card
  invFun x := ⟨x.ord, isInitial_ord _⟩
  left_inv x := Subtype.ext x.2.ord_card
  right_inv x := card_ord x
  map_rel_iff' {a _} := a.2.card_le_card

/-- The "pre-omega" function gives the initial ordinals listed by their ordinal index.
`preOmega n = n`, `preOmega ω = ω`, `preOmega (ω + 1) = ω₁`, etc.

For the more common omega function skipping over finite ordinals, see `Ordinal.omega`. -/
/-
**Ordinal.preOmega** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：preOmega : Ordinal.{u} ↪o Ordinal.{u} where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "pre-omega" function gives the initial ordinals listed by their ordinal inde
x.
`preOmega n = n`, `preOmega ω = ω`, `preOmega (ω + 1) = ω₁`, etc.

For the more common omega function skipping over finite ordinals, see `Ordinal.o
mega`.
-/
def preOmega : Ordinal.{u} ↪o Ordinal.{u} where
  toFun := enumOrd {x | IsInitial x}
  inj' _ _ h := enumOrd_injective not_bddAbove_isInitial h
  map_rel_iff' := enumOrd_le_enumOrd not_bddAbove_isInitial
/-
**Ordinal.coe_preOmega** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：coe_preOmega : preOmega = enumOrd {x | IsInitial x}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_preOmega : preOmega = enumOrd {x | IsInitial x} :=
  rfl
/-
**Ordinal.preOmega_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：preOmega_strictMono : StrictMono preOmega
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preor
der α] [inst_1 : Preorder β] (f : α ↪o β), StrictMono ⇑f
-/
theorem preOmega_strictMono : StrictMono preOmega :=
  preOmega.strictMono
/-
**Ordinal.preOmega_lt_preOmega** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：preOmega_lt_preOmega {o₁ o₂ : Ordinal} : preOmega o₁ < preOmega o₂ ↔ o₁ < 
o₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.lt_iff_lt`：lt_iff_lt {a b} : f a < f b ↔ a < b
-/
theorem preOmega_lt_preOmega {o₁ o₂ : Ordinal} : preOmega o₁ < preOmega o₂ ↔ o₁ < o₂ :=
  preOmega.lt_iff_lt
/-
**Ordinal.preOmega_le_preOmega** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：preOmega_le_preOmega {o₁ o₂ : Ordinal} : preOmega o₁ <= preOmega o₂ ↔ o₁ <
= o₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.le_iff_le`：le_iff_le {a b} : f a <= f b ↔ a <= b
-/
theorem preOmega_le_preOmega {o₁ o₂ : Ordinal} : preOmega o₁ ≤ preOmega o₂ ↔ o₁ ≤ o₂ :=
  preOmega.le_iff_le
/-
**Ordinal.preOmega_max** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：preOmega_max (o₁ o₂ : Ordinal) : preOmega (max o₁ o₂) = max (preOmega o₁) 
(preOmega o₂)
参数：o₁ o₂ : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `OrderEmbedding.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorde
r α] [inst_1 : Preorder β] (f : α ↪o β), Monotone ⇑f
-/
theorem preOmega_max (o₁ o₂ : Ordinal) : preOmega (max o₁ o₂) = max (preOmega o₁) (preOmega o₂) :=
  preOmega.monotone.map_max
/-
**Ordinal.isInitial_preOmega** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isInitial_preOmega (o : Ordinal) : IsInitial (preOmega o)
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.enumOrd_mem`：enumOrd_mem (hs : ¬ BddAbove s) (o : Ordinal) : enu
mOrd s o in s
· 使用定理 `Ordinal.not_bddAbove_isInitial`：not_bddAbove_isInitial : ¬ BddAbove {x |
 IsInitial x}
-/
theorem isInitial_preOmega (o : Ordinal) : IsInitial (preOmega o) :=
  enumOrd_mem not_bddAbove_isInitial o
/-
**Ordinal.le_preOmega_self** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：le_preOmega_self (o : Ordinal) : o <= preOmega o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_apply`：StrictMono.le_apply [WellFoundedLT β] {f : β -> β} 
(hf : StrictMono f) {x} : x <= f x
· 使用定理 `Ordinal.preOmega_strictMono`：preOmega_strictMono : StrictMono preOmega
-/
theorem le_preOmega_self (o : Ordinal) : o ≤ preOmega o :=
  preOmega_strictMono.le_apply

@[simp]
/-
**Ordinal.preOmega_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：preOmega_zero : preOmega 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.coe_preOmega`：coe_preOmega : preOmega = enumOrd {x | IsInitial x
}
· 使用定理 `Ordinal.enumOrd_zero`：∀ {s : Set Ordinal.{u}}, Ordinal.enumOrd s 0 = sIn
f s
· 使用定理 `csInf_eq_bot_of_bot_mem`：∀ {α : Type u_1} [inst : ConditionallyCompleteL
inearOrder α] [inst_1 : OrderBot α] {s : Set α}, ⊥ ∈ s → sInf s = ⊥
· 使用定理 `Ordinal.isInitial_zero`：isInitial_zero : IsInitial 0
-/
theorem preOmega_zero : preOmega 0 = 0 := by
  rw [coe_preOmega, enumOrd_zero]
  exact csInf_eq_bot_of_bot_mem isInitial_zero

@[simp]
/-
**Ordinal.preOmega_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：preOmega_natCast (n : Nat) : preOmega n = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.preOmega_zero`：preOmega_zero : preOmega 0 = 0
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `Ordinal.le_preOmega_self`：le_preOmega_self (o : Ordinal) : o <= preOmega
 o
· 使用定理 `Ordinal.enumOrd_succ_le`：enumOrd_succ_le (hs : ¬ BddAbove s) (ha : a in 
s) (hb : enumOrd s b < a) : enumOrd s (succ b) <= a
· 使用定理 `Ordinal.not_bddAbove_isInitial`：not_bddAbove_isInitial : ¬ BddAbove {x |
 IsInitial x}
· 使用定理 `Ordinal.isInitial_natCast`：isInitial_natCast (n : Nat) : IsInitial n
· 使用定理 `Eq.trans_lt`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a = b → b < c →
 a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
-/
theorem preOmega_natCast (n : ℕ) : preOmega n = n := by
  induction n with
  | zero => exact preOmega_zero
  | succ n IH =>
    apply (le_preOmega_self _).antisymm'
    apply enumOrd_succ_le not_bddAbove_isInitial (isInitial_natCast _) (IH.trans_lt _)
    rw [Nat.cast_lt]
    exact lt_succ n

@[simp]
/-
**Ordinal.preOmega_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：preOmega_ofNat (n : Nat) [n.AtLeastTwo] : preOmega ofNat(n) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.preOmega_natCast`：preOmega_natCast (n : Nat) : preOmega n = n
-/
theorem preOmega_ofNat (n : ℕ) [n.AtLeastTwo] : preOmega ofNat(n) = n :=
  preOmega_natCast n
/-
**Ordinal.preOmega_le_of_forall_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：preOmega_le_of_forall_lt {o a : Ordinal} (ha : IsInitial a) (H : forall b 
< o, preOmega b < a) : preOmega o <= a
参数：ha : IsInitial a；H : forall b < o, preOmega b < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.enumOrd_le_of_forall_lt`：enumOrd_le_of_forall_lt (ha : a in s) (
H : forall b < o, enumOrd s b < a) : enumOrd s o <= a
-/
theorem preOmega_le_of_forall_lt {o a : Ordinal} (ha : IsInitial a) (H : ∀ b < o, preOmega b < a) :
    preOmega o ≤ a :=
  enumOrd_le_of_forall_lt ha H
/-
**Ordinal.isNormal_preOmega** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isNormal_preOmega : IsNormal preOmega
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.isNormal_iff`：isNormal_iff [LinearOrder α] [LinearOrder β] {f : α 
-> β} : IsNormal f ↔ StrictMono f ∧ forall o, IsSuccLimit o -> forall a, (forall
 b < o, …
· 使用定理 `Ordinal.preOmega_strictMono`：preOmega_strictMono : StrictMono preOmega
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ordinal.preOmega_le_of_forall_lt`：preOmega_le_of_forall_lt {o a : Ordina
l} (ha : IsInitial a) (H : forall b < o, preOmega b < a) : preOmega o <= a
· 使用定理 `Ordinal.isInitial_ord`：isInitial_ord (c : Cardinal) : IsInitial c.ord
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.IsInitial.card_lt_card`：∀ {a b : Ordinal.{u_1}}, b.IsInitial → (
a.card < b.card ↔ a < b)
· 使用定理 `Cardinal.card_ord`：card_ord (c) : (ord c).card = c
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Ordinal.isInitial_preOmega`：isInitial_preOmega (o : Ordinal) : IsInitial
 (preOmega o)
· 使用定理 `Ordinal.preOmega_lt_preOmega`：preOmega_lt_preOmega {o₁ o₂ : Ordinal} : p
reOmega o₁ < preOmega o₂ ↔ o₁ < o₂
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Ordinal.card_le_card`：card_le_card {o₁ o₂ : Ordinal} : o₁ <= o₂ -> card 
o₁ <= card o₂
· 使用定理 `Order.IsSuccLimit.succ_lt`：∀ {α : Type u_1} {a b : α} [inst : PartialOrd
er α] [inst_1 : SuccOrder α],   Order.IsSuccLimit b → a < b → Order.succ a < b
· 使用定理 `Cardinal.ord_card_le`：ord_card_le (o : Ordinal) : o.card.ord <= o
-/
theorem isNormal_preOmega : IsNormal preOmega := by
  rw [isNormal_iff]
  refine ⟨preOmega_strictMono, fun o ho a ha ↦
    (preOmega_le_of_forall_lt (isInitial_ord _) fun b hb ↦ ?_).trans (ord_card_le a)⟩
  rw [← (isInitial_ord _).card_lt_card, card_ord]
  apply lt_of_lt_of_le _ (card_le_card <| ha _ (ho.succ_lt hb))
  rw [(isInitial_preOmega _).card_lt_card, preOmega_lt_preOmega]
  exact lt_succ b

@[simp]
/-
**Ordinal.range_preOmega** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：range_preOmega : range preOmega = {x | IsInitial x}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.range_enumOrd`：range_enumOrd (hs : ¬ BddAbove s) : range (enumOr
d s) = s
· 使用定理 `Ordinal.not_bddAbove_isInitial`：not_bddAbove_isInitial : ¬ BddAbove {x |
 IsInitial x}
-/
theorem range_preOmega : range preOmega = {x | IsInitial x} :=
  range_enumOrd not_bddAbove_isInitial
/-
**Ordinal.mem_range_preOmega_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mem_range_preOmega_iff {x : Ordinal} : x in range preOmega ↔ IsInitial x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.range_preOmega`：range_preOmega : range preOmega = {x | IsInitial
 x}
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_range_preOmega_iff {x : Ordinal} : x ∈ range preOmega ↔ IsInitial x := by
  rw [range_preOmega, mem_ofPred]

alias ⟨_, IsInitial.mem_range_preOmega⟩ := mem_range_preOmega_iff

@[simp]
/-
**Ordinal.preOmega_omega0** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：preOmega_omega0 : preOmega ω = ω
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.apply_omega0_of_isNormal`：apply_omega0_of_isNormal {f : Ordinal.
{u} -> Ordinal.{v}} (hf : IsNormal f) : ⨆ n : Nat, f n = f ω
· 使用定理 `Ordinal.isNormal_preOmega`：isNormal_preOmega : IsNormal preOmega
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ordinal.preOmega_natCast`：preOmega_natCast (n : Nat) : preOmega n = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ordinal.iSup_natCast`：iSup_natCast : iSup Nat.cast = ω
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preOmega_omega0 : preOmega ω = ω := by
  simp_rw [← apply_omega0_of_isNormal isNormal_preOmega, preOmega_natCast, iSup_natCast]

@[simp]
/-
**Ordinal.omega0_le_preOmega_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：omega0_le_preOmega_iff {x : Ordinal} : ω <= preOmega x ↔ ω <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.preOmega_omega0`：preOmega_omega0 : preOmega ω = ω
· 使用定理 `Ordinal.preOmega_le_preOmega`：preOmega_le_preOmega {o₁ o₂ : Ordinal} : p
reOmega o₁ <= preOmega o₂ ↔ o₁ <= o₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem omega0_le_preOmega_iff {x : Ordinal} : ω ≤ preOmega x ↔ ω ≤ x := by
  conv_lhs => rw [← preOmega_omega0, preOmega_le_preOmega]

@[simp]
/-
**Ordinal.omega0_lt_preOmega_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：omega0_lt_preOmega_iff {x : Ordinal} : ω < preOmega x ↔ ω < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.preOmega_omega0`：preOmega_omega0 : preOmega ω = ω
· 使用定理 `Ordinal.preOmega_lt_preOmega`：preOmega_lt_preOmega {o₁ o₂ : Ordinal} : p
reOmega o₁ < preOmega o₂ ↔ o₁ < o₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem omega0_lt_preOmega_iff {x : Ordinal} : ω < preOmega x ↔ ω < x := by
  conv_lhs => rw [← preOmega_omega0, preOmega_lt_preOmega]

/-- The `omega` function gives the infinite initial ordinals listed by their ordinal index.
`omega 0 = ω`, `omega 1 = ω₁` is the first uncountable ordinal, and so on.

This is not to be confused with the first infinite ordinal `Ordinal.omega0`.

For a version including finite ordinals, see `Ordinal.preOmega`. -/
/-
**Ordinal.omega** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：omega : Ordinal ↪o Ordinal
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `omega` function gives the infinite initial ordinals listed by their ordinal
 index.
`omega 0 = ω`, `omega 1 = ω₁` is the first uncountable ordinal, and so on.

This is not to be confused with the first infinite ordinal `Ordinal.omega0`.

For a version including finite ordinals, see `Ordinal.preOmega`.
-/
def omega : Ordinal ↪o Ordinal :=
  (OrderEmbedding.addLeft ω).trans preOmega

@[inherit_doc] scoped notation "ω_ " => omega
recommended_spelling "omega" for "ω_" in [omega, «termω_»]

/-- `ω₁` is the first uncountable ordinal. -/
scoped notation "ω₁" => ω_ 1
recommended_spelling "omega_one" for "ω₁" in [«termω₁»]

/-
**Ordinal.omega_eq_preOmega** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：omega_eq_preOmega (o : Ordinal) : ω_ o = preOmega (ω + o)
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem omega_eq_preOmega (o : Ordinal) : ω_ o = preOmega (ω + o) :=
  rfl
/-
**Ordinal.omega_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：omega_strictMono : StrictMono omega
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preor
der α] [inst_1 : Preorder β] (f : α ↪o β), StrictMono ⇑f
-/
theorem omega_strictMono : StrictMono omega :=
  omega.strictMono
/-
**Ordinal.omega_lt_omega** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：omega_lt_omega {o₁ o₂ : Ordinal} : ω_ o₁ < ω_ o₂ ↔ o₁ < o₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.lt_iff_lt`：lt_iff_lt {a b} : f a < f b ↔ a < b
-/
theorem omega_lt_omega {o₁ o₂ : Ordinal} : ω_ o₁ < ω_ o₂ ↔ o₁ < o₂ :=
  omega.lt_iff_lt
/-
**Ordinal.omega_le_omega** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：omega_le_omega {o₁ o₂ : Ordinal} : ω_ o₁ <= ω_ o₂ ↔ o₁ <= o₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.le_iff_le`：le_iff_le {a b} : f a <= f b ↔ a <= b
-/
theorem omega_le_omega {o₁ o₂ : Ordinal} : ω_ o₁ ≤ ω_ o₂ ↔ o₁ ≤ o₂ :=
  omega.le_iff_le
/-
**Ordinal.omega_max** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：omega_max (o₁ o₂ : Ordinal) : ω_ (max o₁ o₂) = max (ω_ o₁) (ω_ o₂)
参数：o₁ o₂ : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `OrderEmbedding.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorde
r α] [inst_1 : Preorder β] (f : α ↪o β), Monotone ⇑f
-/
theorem omega_max (o₁ o₂ : Ordinal) : ω_ (max o₁ o₂) = max (ω_ o₁) (ω_ o₂) :=
  omega.monotone.map_max
/-
**Ordinal.preOmega_le_omega** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：preOmega_le_omega (o : Ordinal) : preOmega o <= ω_ o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.preOmega_le_preOmega`：preOmega_le_preOmega {o₁ o₂ : Ordinal} : p
reOmega o₁ <= preOmega o₂ ↔ o₁ <= o₂
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
-/
theorem preOmega_le_omega (o : Ordinal) : preOmega o ≤ ω_ o :=
  preOmega_le_preOmega.2 le_add_self
/-
**Ordinal.isInitial_omega** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isInitial_omega (o : Ordinal) : IsInitial (omega o)
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.isInitial_preOmega`：isInitial_preOmega (o : Ordinal) : IsInitial
 (preOmega o)
-/
theorem isInitial_omega (o : Ordinal) : IsInitial (omega o) :=
  isInitial_preOmega _
/-
**Ordinal.le_omega_self** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：le_omega_self (o : Ordinal) : o <= omega o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_apply`：StrictMono.le_apply [WellFoundedLT β] {f : β -> β} 
(hf : StrictMono f) {x} : x <= f x
· 使用定理 `Ordinal.omega_strictMono`：omega_strictMono : StrictMono omega
-/
theorem le_omega_self (o : Ordinal) : o ≤ omega o :=
  omega_strictMono.le_apply

@[simp]
/-
**Ordinal.omega_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：omega_zero : ω_ 0 = ω
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.omega_eq_preOmega`：omega_eq_preOmega (o : Ordinal) : ω_ o = preO
mega (ω + o)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Ordinal.preOmega_omega0`：preOmega_omega0 : preOmega ω = ω
-/
theorem omega_zero : ω_ 0 = ω := by
  rw [omega_eq_preOmega, add_zero, preOmega_omega0]
/-
**Ordinal.omega0_le_omega** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：omega0_le_omega (o : Ordinal) : ω <= ω_ o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.omega_zero`：omega_zero : ω_ 0 = ω
· 使用定理 `Ordinal.omega_le_omega`：omega_le_omega {o₁ o₂ : Ordinal} : ω_ o₁ <= ω_ o
₂ ↔ o₁ <= o₂
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem omega0_le_omega (o : Ordinal) : ω ≤ ω_ o := by
  rw [← omega_zero, omega_le_omega]
  exact zero_le

/-- For the theorem `0 < ω`, see `omega0_pos`. -/
/-
**Ordinal.omega_pos** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：omega_pos (o : Ordinal) : 0 < ω_ o
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Ordinal.omega0_pos`：omega0_pos : 0 < ω
· 使用定理 `Ordinal.omega0_le_omega`：omega0_le_omega (o : Ordinal) : ω <= ω_ o

--- 原说明 ---
For the theorem `0 < ω`, see `omega0_pos`.
-/
theorem omega_pos (o : Ordinal) : 0 < ω_ o :=
  omega0_pos.trans_le (omega0_le_omega o)

@[simp]
/-
**Ordinal.omega0_lt_omega_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：omega0_lt_omega_one : ω < ω₁
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.omega_zero`：omega_zero : ω_ 0 = ω
· 使用定理 `Ordinal.omega_lt_omega`：omega_lt_omega {o₁ o₂ : Ordinal} : ω_ o₁ < ω_ o₂
 ↔ o₁ < o₂
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem omega0_lt_omega_one : ω < ω₁ := by
  rw [← omega_zero, omega_lt_omega]
  exact zero_lt_one
/-
**Ordinal.isNormal_omega** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isNormal_omega : IsNormal omega
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsNormal.comp`：comp (hg : IsNormal g) (hf : IsNormal f) : IsNormal
 (g ∘ f)
· 使用定理 `Ordinal.isNormal_preOmega`：isNormal_preOmega : IsNormal preOmega
· 使用定理 `Ordinal.isNormal_add_right`：isNormal_add_right (a : Ordinal) : IsNormal 
(a + ·)
-/
theorem isNormal_omega : IsNormal omega :=
  isNormal_preOmega.comp (isNormal_add_right _)

@[simp]
/-
**Ordinal.range_omega** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：range_omega : range omega = {x | ω <= x ∧ IsInitial x}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Ordinal.omega0_le_omega`：omega0_le_omega (o : Ordinal) : ω <= ω_ o
· 使用定理 `Ordinal.isInitial_omega`：isInitial_omega (o : Ordinal) : IsInitial (omeg
a o)
· 使用定理 `Ordinal.IsInitial.mem_range_preOmega`：∀ {x : Ordinal.{u_1}}, x.IsInitial
 → x ∈ Set.range ⇑Ordinal.preOmega
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.omega_eq_preOmega`：omega_eq_preOmega (o : Ordinal) : ω_ o = preO
mega (ω + o)
· 使用定理 `Ordinal.add_sub_cancel_of_le`：∀ {a b : Ordinal.{u_4}}, b ≤ a → b + (a - 
b) = a
· 使用定理 `Ordinal.omega0_le_preOmega_iff`：omega0_le_preOmega_iff {x : Ordinal} : ω
 <= preOmega x ↔ ω <= x
-/
theorem range_omega : range omega = {x | ω ≤ x ∧ IsInitial x} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨omega0_le_omega a, isInitial_omega a⟩
  · rintro ⟨ha', ha⟩
    obtain ⟨a, rfl⟩ := ha.mem_range_preOmega
    use a - ω
    rw [omega0_le_preOmega_iff] at ha'
    rw [omega_eq_preOmega, Ordinal.add_sub_cancel_of_le ha']
/-
**Ordinal.mem_range_omega_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mem_range_omega_iff {x : Ordinal} : x in range omega ↔ ω <= x ∧ IsInitial 
x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.range_omega`：range_omega : range omega = {x | ω <= x ∧ IsInitial
 x}
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_range_omega_iff {x : Ordinal} : x ∈ range omega ↔ ω ≤ x ∧ IsInitial x := by
  rw [range_omega, mem_ofPred]
/-
**Ordinal.preOmega_of_omega0_sq_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：preOmega_of_omega0_sq_le {o : Ordinal} (ho : ω ^ 2 <= o) : preOmega o = ω_
 o
参数：ho : ω ^ 2 <= o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.omega_eq_preOmega`：omega_eq_preOmega (o : Ordinal) : ω_ o = preO
mega (ω + o)
· 使用定理 `Ordinal.add_of_omega0_opow_le`：add_of_omega0_opow_le (h₁ : a < ω ^ b) (h
₂ : ω ^ b <= c) : a + c = c
· 使用定理 `Ordinal.left_lt_opow`：left_lt_opow {a b : Ordinal} (ha : 1 < a) (hb : 1 
< b) : a < a ^ b
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.opow_natCast`：opow_natCast (a : Ordinal) (n : Nat) : a ^ (n : Or
dinal) = a ^ n
-/
theorem preOmega_of_omega0_sq_le {o : Ordinal} (ho : ω ^ 2 ≤ o) : preOmega o = ω_ o := by
  rw [← opow_natCast] at ho
  rw [omega_eq_preOmega, add_of_omega0_opow_le _ ho]
  apply left_lt_opow one_lt_omega0
  simp

end Ordinal

/-! ### Aleph cardinals -/

namespace Cardinal

/-- The "pre-aleph" function gives the cardinals listed by their ordinal index. `preAleph n = n`,
`preAleph ω = ℵ₀`, `preAleph (ω + 1) = succ ℵ₀`, etc.

For the more common aleph function skipping over finite cardinals, see `Cardinal.aleph`. -/
/-
**Cardinal.preAleph** 是 Mathlib 中的一个定义，位于命名空间 `Cardinal`。
形式化陈述：preAleph : Ordinal.{u} ≃o Cardinal.{u}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.not_bddAbove_isInitial`：not_bddAbove_isInitial : ¬ BddAbove {x |
 IsInitial x}

--- 原说明 ---
The "pre-aleph" function gives the cardinals listed by their ordinal index. `pre
Aleph n = n`,
`preAleph ω = ℵ₀`, `preAleph (ω + 1) = succ ℵ₀`, etc.

For the more common aleph function skipping over finite cardinals, see `Cardinal
.aleph`.
-/
def preAleph : Ordinal.{u} ≃o Cardinal.{u} :=
  (enumOrdOrderIso _ not_bddAbove_isInitial).trans isInitialIso

@[simp]
/-
**Cardinal._root_.Ordinal.card_preOmega** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Ordinal.card_preOmega (o : Ordinal) : (preOmega o).card = preAleph o :=
  rfl

@[simp]
/-
**Cardinal.ord_preAleph** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ord_preAleph (o : Ordinal) : (preAleph o).ord = preOmega o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.card_preOmega`：∀ (o : Ordinal.{u_1}), (Ordinal.preOmega o).card 
= Cardinal.preAleph o
· 使用定理 `Ordinal.IsInitial.ord_card`：∀ {o : Ordinal.{u_1}}, o.IsInitial → o.card.
ord = o
· 使用定理 `Ordinal.isInitial_preOmega`：isInitial_preOmega (o : Ordinal) : IsInitial
 (preOmega o)
-/
theorem ord_preAleph (o : Ordinal) : (preAleph o).ord = preOmega o := by
  rw [← o.card_preOmega, (isInitial_preOmega o).ord_card]

@[simp]
/-
**Cardinal._root_.Ordinal.type_lt_cardinal** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Ordinal.type_lt_cardinal : typeLT Cardinal = Ordinal.univ.{u, u + 1} := by
  simpa using preAleph.symm.ordinalType_congr

@[deprecated (since := "2026-03-20")] alias type_cardinal := type_lt_cardinal

@[simp]
/-
**Cardinal.mk_cardinal** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_cardinal : #Cardinal = univ.{u, u + 1}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Cardinal.instWellFoundedLT`：WellFoundedLT Cardinal.{u}
· 使用定理 `Ordinal.type_lt_cardinal`：(Ordinal.type fun x1 x2 => x1 < x2) = Ordinal.
univ.{u, u + 1}
-/
theorem mk_cardinal : #Cardinal = univ.{u, u + 1} := by
  simpa only [card_type, card_univ] using congr_arg card type_lt_cardinal
/-
**Cardinal._root_.Order.cof_cardinal** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Order.cof_cardinal : Order.cof Cardinal.{u} = Cardinal.univ.{u, u + 1} := by
  simpa using preAleph.cof_congr.symm
/-
**Cardinal.** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsRegularCardinalOrder Cardinal := ⟨by simp [Order.cof_cardinal]⟩
/-
**Cardinal.preAleph_lt_preAleph** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preAleph_lt_preAleph {o₁ o₂ : Ordinal} : preAleph o₁ < preAleph o₂ ↔ o₁ < 
o₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.lt_iff_lt`：lt_iff_lt (e : α ≃o β) {x y : α} : e x < e y ↔ x < y
-/
theorem preAleph_lt_preAleph {o₁ o₂ : Ordinal} : preAleph o₁ < preAleph o₂ ↔ o₁ < o₂ :=
  preAleph.lt_iff_lt
/-
**Cardinal.preAleph_le_preAleph** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preAleph_le_preAleph {o₁ o₂ : Ordinal} : preAleph o₁ <= preAleph o₂ ↔ o₁ <
= o₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.le_iff_le`：le_iff_le (e : α ≃o β) {x y : α} : e x <= e y ↔ x <=
 y
-/
theorem preAleph_le_preAleph {o₁ o₂ : Ordinal} : preAleph o₁ ≤ preAleph o₂ ↔ o₁ ≤ o₂ :=
  preAleph.le_iff_le
/-
**Cardinal.preAleph_max** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preAleph_max (o₁ o₂ : Ordinal) : preAleph (max o₁ o₂) = max (preAleph o₁) 
(preAleph o₂)
参数：o₁ o₂ : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `OrderIso.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (e : α ≃o β), Monotone ⇑e
-/
theorem preAleph_max (o₁ o₂ : Ordinal) : preAleph (max o₁ o₂) = max (preAleph o₁) (preAleph o₂) :=
  preAleph.monotone.map_max

@[simp]
/-
**Cardinal.preAleph_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preAleph_zero : preAleph 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_bot`：OrderIso.map_bot [LE α] [PartialOrder β] [OrderBot α] 
[OrderBot β] (f : α ≃o β) : f ⊥ = ⊥
-/
theorem preAleph_zero : preAleph 0 = 0 :=
  preAleph.map_bot

@[simp]
/-
**Cardinal.succ_preAleph** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：succ_preAleph (o : Ordinal) : succ (preAleph o) = preAleph (o + 1)
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.map_succ`：∀ {α : Type u_1} {β : Type u_2} [inst : PartialOrder 
α] [inst_1 : SuccOrder α] [inst_2 : PartialOrder β]   [inst_3 : SuccOrder β] (f 
: α ≃o …
-/
theorem succ_preAleph (o : Ordinal) : succ (preAleph o) = preAleph (o + 1) :=
  (preAleph.map_succ o).symm

@[deprecated succ_preAleph (since := "2026-03-24")]
/-
**Cardinal.preAleph_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preAleph_add_one (o : Ordinal) : preAleph (o + 1) = succ (preAleph o)
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_succ`：∀ {α : Type u_1} {β : Type u_2} [inst : PartialOrder 
α] [inst_1 : SuccOrder α] [inst_2 : PartialOrder β]   [inst_3 : SuccOrder β] (f 
: α ≃o …
-/
theorem preAleph_add_one (o : Ordinal) : preAleph (o + 1) = succ (preAleph o) :=
  preAleph.map_succ o

@[deprecated succ_preAleph (since := "2026-03-24")]
/-
**Cardinal.preAleph_succ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preAleph_succ (o : Ordinal) : preAleph (succ o) = succ (preAleph o)
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_succ`：∀ {α : Type u_1} {β : Type u_2} [inst : PartialOrder 
α] [inst_1 : SuccOrder α] [inst_2 : PartialOrder β]   [inst_3 : SuccOrder β] (f 
: α ≃o …
-/
theorem preAleph_succ (o : Ordinal) : preAleph (succ o) = succ (preAleph o) :=
  preAleph.map_succ o

@[simp]
/-
**Cardinal.preAleph_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preAleph_natCast (n : Nat) : preAleph n = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.card_preOmega`：∀ (o : Ordinal.{u_1}), (Ordinal.preOmega o).card 
= Cardinal.preAleph o
· 使用定理 `Ordinal.preOmega_natCast`：preOmega_natCast (n : Nat) : preOmega n = n
· 使用定理 `Ordinal.card_nat`：card_nat (n : Nat) : card.{u} n = n
-/
theorem preAleph_natCast (n : ℕ) : preAleph n = n := by
  rw [← card_preOmega, preOmega_natCast, card_nat]

@[simp]
/-
**Cardinal.preAleph_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preAleph_ofNat (n : Nat) [n.AtLeastTwo] : preAleph ofNat(n) = ofNat(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.preAleph_natCast`：preAleph_natCast (n : Nat) : preAleph n = n
-/
theorem preAleph_ofNat (n : ℕ) [n.AtLeastTwo] : preAleph ofNat(n) = ofNat(n) :=
  preAleph_natCast n

@[simp]
/-
**Cardinal.preAleph_symm_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preAleph_symm_natCast (n : Nat) : preAleph.symm n = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.preAleph_natCast`：preAleph_natCast (n : Nat) : preAleph n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preAleph_symm_natCast (n : ℕ) : preAleph.symm n = n := by
  simp [OrderIso.symm_apply_eq]

@[simp]
/-
**Cardinal.preAleph_symm_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preAleph_symm_ofNat (n : Nat) [n.AtLeastTwo] : preAleph.symm ofNat(n) = of
Nat(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.preAleph_symm_natCast`：preAleph_symm_natCast (n : Nat) : preAle
ph.symm n = n
-/
theorem preAleph_symm_ofNat (n : ℕ) [n.AtLeastTwo] : preAleph.symm ofNat(n) = ofNat(n) :=
  preAleph_symm_natCast n

@[deprecated (since := "2026-05-22")] alias preAleph_nat := preAleph_natCast

@[simp]
/-
**Cardinal.preAleph_omega0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preAleph_omega0 : preAleph ω = ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.card_preOmega`：∀ (o : Ordinal.{u_1}), (Ordinal.preOmega o).card 
= Cardinal.preAleph o
· 使用定理 `Ordinal.preOmega_omega0`：preOmega_omega0 : preOmega ω = ω
· 使用定理 `Ordinal.card_omega0`：card_omega0 : card ω = ℵ₀
-/
theorem preAleph_omega0 : preAleph ω = ℵ₀ := by
  rw [← card_preOmega, preOmega_omega0, card_omega0]

@[simp]
/-
**Cardinal.preAleph_symm_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preAleph_symm_aleph0 : preAleph.symm ℵ₀ = ω
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.preAleph_omega0`：preAleph_omega0 : preAleph ω = ℵ₀
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preAleph_symm_aleph0 : preAleph.symm ℵ₀ = ω := by
  simp [OrderIso.symm_apply_eq]

@[simp]
/-
**Cardinal.preAleph_pos** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preAleph_pos {o : Ordinal} : 0 < preAleph o ↔ 0 < o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.preAleph_zero`：preAleph_zero : preAleph 0 = 0
· 使用定理 `Cardinal.preAleph_lt_preAleph`：preAleph_lt_preAleph {o₁ o₂ : Ordinal} : 
preAleph o₁ < preAleph o₂ ↔ o₁ < o₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem preAleph_pos {o : Ordinal} : 0 < preAleph o ↔ 0 < o := by
  rw [← preAleph_zero, preAleph_lt_preAleph]

@[simp]
/-
**Cardinal.aleph0_le_preAleph** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_le_preAleph {o : Ordinal} : ℵ₀ <= preAleph o ↔ ω <= o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.preAleph_omega0`：preAleph_omega0 : preAleph ω = ℵ₀
· 使用定理 `Cardinal.preAleph_le_preAleph`：preAleph_le_preAleph {o₁ o₂ : Ordinal} : 
preAleph o₁ <= preAleph o₂ ↔ o₁ <= o₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem aleph0_le_preAleph {o : Ordinal} : ℵ₀ ≤ preAleph o ↔ ω ≤ o := by
  rw [← preAleph_omega0, preAleph_le_preAleph]
/-
**Cardinal._root_.Ordinal.card_le_preAleph** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Ordinal.card_le_preAleph (o : Ordinal) : o.card ≤ preAleph o :=
  o.card_preOmega.trans_ge <| card_le_card <| o.le_preOmega_self
/-
**Cardinal.le_preAleph_ord** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：le_preAleph_ord (c : Cardinal) : c <= preAleph c.ord
参数：c : Cardinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.card_ord`：card_ord (c) : (ord c).card = c
· 使用定理 `Ordinal.card_le_preAleph`：∀ (o : Ordinal.{u_1}), o.card ≤ Cardinal.preAl
eph o
-/
theorem le_preAleph_ord (c : Cardinal) : c ≤ preAleph c.ord := by
  simpa using c.ord.card_le_preAleph

@[simp]
/-
**Cardinal.lift_preAleph** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_preAleph (o : Ordinal.{u}) : lift.{v} (preAleph o) = preAleph (Ordina
l.lift.{v} o)
参数：o : Ordinal.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.eq`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β
 → β → Prop} [IsWellOrder β s] (f g : InitialSeg r s) (a : α),   f a = g a
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Cardinal.instWellFoundedLT`：WellFoundedLT Cardinal.{u}
-/
theorem lift_preAleph (o : Ordinal.{u}) : lift.{v} (preAleph o) = preAleph (Ordinal.lift.{v} o) :=
  (preAleph.toInitialSeg.trans liftInitialSeg).eq
    (Ordinal.liftInitialSeg.trans preAleph.toInitialSeg) o

@[simp]
/-
**Cardinal._root_.Ordinal.lift_preOmega** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Ordinal.lift_preOmega (o : Ordinal.{u}) :
    Ordinal.lift.{v} (preOmega o) = preOmega (Ordinal.lift.{v} o) := by
  rw [← ord_preAleph, lift_ord, lift_preAleph, ord_preAleph]
/-
**Cardinal.isNormal_preAleph** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：isNormal_preAleph : Order.IsNormal preAleph
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.isNormal`：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α
] [inst_1 : LinearOrder β] (f : α ≃o β), Order.IsNormal ⇑f
-/
theorem isNormal_preAleph : Order.IsNormal preAleph :=
  OrderIso.isNormal _
/-
**Cardinal.preAleph_le_of_isSuccPrelimit** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preAleph_le_of_isSuccPrelimit {o : Ordinal} (l : IsSuccPrelimit o) {c} : p
reAleph o <= c ↔ forall o' < o, preAleph o' <= c
参数：l : IsSuccPrelimit o。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.preAleph_zero`：preAleph_zero : preAleph 0 = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.IsNormal.le_iff_forall_le`：le_iff_forall_le (hf : IsNormal f) (ha 
: IsSuccLimit a) {b : β} : f a <= b ↔ forall a' < a, f a' <= b
· 使用定理 `Cardinal.isNormal_preAleph`：isNormal_preAleph : Order.IsNormal preAleph
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
-/
theorem preAleph_le_of_isSuccPrelimit {o : Ordinal} (l : IsSuccPrelimit o) {c} :
    preAleph o ≤ c ↔ ∀ o' < o, preAleph o' ≤ c := by
  obtain rfl | ho := eq_or_ne o 0
  · simp
  · exact isNormal_preAleph.le_iff_forall_le ⟨by simpa, l⟩
/-
**Cardinal.preAleph_limit** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preAleph_limit {o : Ordinal} (ho : IsSuccPrelimit o) : preAleph o = ⨆ a : 
Iio o, preAleph a
参数：ho : IsSuccPrelimit o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.preAleph_zero`：preAleph_zero : preAleph 0 = 0
· 使用定理 `ciSup_of_empty`：ciSup_of_empty [IsEmpty ι] (f : ι -> α) : ⨆ i, f i = ⊥
· 使用定理 `Set.isEmpty_Iio_zero`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Zer
o α] [IsBotZeroClass α], IsEmpty ↑(Set.Iio 0)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.IsNormal.apply_of_isSuccLimit`：apply_of_isSuccLimit (hf : IsNormal
 f) (ha : IsSuccLimit a) : f a = ⨆ b : Iio a, f b
· 使用定理 `Cardinal.isNormal_preAleph`：isNormal_preAleph : Order.IsNormal preAleph
-/
theorem preAleph_limit {o : Ordinal} (ho : IsSuccPrelimit o) :
    preAleph o = ⨆ a : Iio o, preAleph a := by
  obtain rfl | h := eq_or_ne o 0
  · simp
  · exact isNormal_preAleph.apply_of_isSuccLimit ⟨by simpa, ho⟩
/-
**Cardinal.preAleph_le_of_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preAleph_le_of_strictMono {f : Ordinal -> Cardinal} (hf : StrictMono f) (o
 : Ordinal) : preAleph o <= f o
参数：hf : StrictMono f；o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
· 使用定理 `StrictMono.id_le`：StrictMono.id_le [WellFoundedLT β] {f : β -> β} (hf : 
StrictMono f) : id <= f
· 使用定理 `Cardinal.instWellFoundedLT`：WellFoundedLT Cardinal.{u}
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
· 使用定理 `OrderIso.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α]
 [inst_1 : Preorder β] (e : α ≃o β), StrictMono ⇑e
-/
theorem preAleph_le_of_strictMono {f : Ordinal → Cardinal} (hf : StrictMono f) (o : Ordinal) :
    preAleph o ≤ f o := by
  simpa using (hf.comp preAleph.symm.strictMono).id_le (preAleph o)

/-- The `aleph` function gives the infinite cardinals listed by their ordinal index. `aleph 0 = ℵ₀`,
`aleph 1 = succ ℵ₀` is the first uncountable cardinal, and so on.

For a version including finite cardinals, see `Cardinal.preAleph`. -/
/-
**Cardinal.aleph** 是 Mathlib 中的一个定义，位于命名空间 `Cardinal`。
形式化陈述：aleph : Ordinal ↪o Cardinal
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `aleph` function gives the infinite cardinals listed by their ordinal index.
 `aleph 0 = ℵ₀`,
`aleph 1 = succ ℵ₀` is the first uncountable cardinal, and so on.

For a version including finite cardinals, see `Cardinal.preAleph`.
-/
def aleph : Ordinal ↪o Cardinal :=
  (OrderEmbedding.addLeft ω).trans preAleph

@[inherit_doc] scoped notation "ℵ_ " => aleph
recommended_spelling "aleph" for "ℵ_" in [aleph, «termℵ_»]

/-- `ℵ₁` is the first uncountable cardinal. -/
scoped notation "ℵ₁" => ℵ_ 1
recommended_spelling "aleph_one" for "ℵ₁" in [«termℵ₁»]

/-
**Cardinal.aleph_eq_preAleph** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph_eq_preAleph (o : Ordinal) : ℵ_ o = preAleph (ω + o)
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem aleph_eq_preAleph (o : Ordinal) : ℵ_ o = preAleph (ω + o) :=
  rfl

@[simp]
/-
**Cardinal._root_.Ordinal.card_omega** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Ordinal.card_omega (o : Ordinal) : (ω_ o).card = ℵ_ o :=
  rfl

@[simp]
/-
**Cardinal.preAleph_symm_aleph** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preAleph_symm_aleph (o : Ordinal) : preAleph.symm (ℵ_ o) = ω + o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
-/
theorem preAleph_symm_aleph (o : Ordinal) : preAleph.symm (ℵ_ o) = ω + o :=
  preAleph.symm_apply_apply _

@[simp]
/-
**Cardinal.ord_aleph** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ord_aleph (o : Ordinal) : (ℵ_ o).ord = ω_ o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.ord_preAleph`：ord_preAleph (o : Ordinal) : (preAleph o).ord = p
reOmega o
-/
theorem ord_aleph (o : Ordinal) : (ℵ_ o).ord = ω_ o :=
  ord_preAleph _
/-
**Cardinal.aleph_lt_aleph** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph_lt_aleph {o₁ o₂ : Ordinal} : ℵ_ o₁ < ℵ_ o₂ ↔ o₁ < o₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.lt_iff_lt`：lt_iff_lt {a b} : f a < f b ↔ a < b
-/
theorem aleph_lt_aleph {o₁ o₂ : Ordinal} : ℵ_ o₁ < ℵ_ o₂ ↔ o₁ < o₂ :=
  aleph.lt_iff_lt
/-
**Cardinal.aleph_le_aleph** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph_le_aleph {o₁ o₂ : Ordinal} : ℵ_ o₁ <= ℵ_ o₂ ↔ o₁ <= o₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.le_iff_le`：le_iff_le {a b} : f a <= f b ↔ a <= b
-/
theorem aleph_le_aleph {o₁ o₂ : Ordinal} : ℵ_ o₁ ≤ ℵ_ o₂ ↔ o₁ ≤ o₂ :=
  aleph.le_iff_le
/-
**Cardinal.aleph_max** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph_max (o₁ o₂ : Ordinal) : ℵ_ (max o₁ o₂) = max (ℵ_ o₁) (ℵ_ o₂)
参数：o₁ o₂ : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `OrderEmbedding.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorde
r α] [inst_1 : Preorder β] (f : α ↪o β), Monotone ⇑f
-/
theorem aleph_max (o₁ o₂ : Ordinal) : ℵ_ (max o₁ o₂) = max (ℵ_ o₁) (ℵ_ o₂) :=
  aleph.monotone.map_max
/-
**Cardinal.preAleph_le_aleph** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preAleph_le_aleph (o : Ordinal) : preAleph o <= ℵ_ o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.preAleph_le_preAleph`：preAleph_le_preAleph {o₁ o₂ : Ordinal} : 
preAleph o₁ <= preAleph o₂ ↔ o₁ <= o₂
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
-/
theorem preAleph_le_aleph (o : Ordinal) : preAleph o ≤ ℵ_ o :=
  preAleph_le_preAleph.2 le_add_self

@[simp]
/-
**Cardinal.succ_aleph** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：succ_aleph (o : Ordinal) : succ (ℵ_ o) = ℵ_ (o + 1)
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.aleph_eq_preAleph`：aleph_eq_preAleph (o : Ordinal) : ℵ_ o = pre
Aleph (ω + o)
· 使用定理 `Cardinal.succ_preAleph`：succ_preAleph (o : Ordinal) : succ (preAleph o) 
= preAleph (o + 1)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
-/
theorem succ_aleph (o : Ordinal) : succ (ℵ_ o) = ℵ_ (o + 1) := by
  rw [aleph_eq_preAleph, succ_preAleph, add_assoc, aleph_eq_preAleph]

@[deprecated succ_aleph (since := "2026-03-24")]
/-
**Cardinal.aleph_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph_add_one (o : Ordinal) : ℵ_ (o + 1) = succ (ℵ_ o)
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.succ_aleph`：succ_aleph (o : Ordinal) : succ (ℵ_ o) = ℵ_ (o + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem aleph_add_one (o : Ordinal) : ℵ_ (o + 1) = succ (ℵ_ o) := by
  simp

@[deprecated succ_aleph (since := "2026-03-24")]
/-
**Cardinal.aleph_succ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph_succ (o : Ordinal) : ℵ_ (succ o) = succ (ℵ_ o)
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.succ_aleph`：succ_aleph (o : Ordinal) : succ (ℵ_ o) = ℵ_ (o + 1)
-/
theorem aleph_succ (o : Ordinal) : ℵ_ (succ o) = succ (ℵ_ o) :=
  (succ_aleph o).symm

@[simp]
/-
**Cardinal.aleph_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph_zero : ℵ_ 0 = ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.aleph_eq_preAleph`：aleph_eq_preAleph (o : Ordinal) : ℵ_ o = pre
Aleph (ω + o)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Cardinal.preAleph_omega0`：preAleph_omega0 : preAleph ω = ℵ₀
-/
theorem aleph_zero : ℵ_ 0 = ℵ₀ := by rw [aleph_eq_preAleph, add_zero, preAleph_omega0]

@[simp]
/-
**Cardinal.lift_aleph** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_aleph (o : Ordinal.{u}) : lift.{v} (aleph o) = aleph (Ordinal.lift.{v
} o)
参数：o : Ordinal.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_preAleph`：lift_preAleph (o : Ordinal.{u}) : lift.{v} (preA
leph o) = preAleph (Ordinal.lift.{v} o)
· 使用定理 `Ordinal.lift_add`：lift_add (a b : Ordinal.{v}) : lift.{u} (a + b) = lift
.{u} a + lift.{u} b
· 使用定理 `Ordinal.lift_omega0`：lift_omega0 : lift ω = ω
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_aleph (o : Ordinal.{u}) : lift.{v} (aleph o) = aleph (Ordinal.lift.{v} o) := by
  simp [aleph_eq_preAleph]

/-- For the theorem `lift ω = ω`, see `lift_omega0`. -/
@[simp]
/-
**Cardinal._root_.Ordinal.lift_omega** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For the theorem `lift ω = ω`, see `lift_omega0`.
-/
theorem _root_.Ordinal.lift_omega (o : Ordinal.{u}) :
    Ordinal.lift.{v} (ω_ o) = ω_ (Ordinal.lift.{v} o) := by
  simp [omega_eq_preOmega]
/-
**Cardinal.isNormal_aleph** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：isNormal_aleph : Order.IsNormal aleph
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsNormal.comp`：comp (hg : IsNormal g) (hf : IsNormal f) : IsNormal
 (g ∘ f)
· 使用定理 `Cardinal.isNormal_preAleph`：isNormal_preAleph : Order.IsNormal preAleph
· 使用定理 `Ordinal.isNormal_add_right`：isNormal_add_right (a : Ordinal) : IsNormal 
(a + ·)
-/
theorem isNormal_aleph : Order.IsNormal aleph :=
  isNormal_preAleph.comp (isNormal_add_right _)
/-
**Cardinal.aleph_limit** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph_limit {o : Ordinal} (ho : IsSuccLimit o) : ℵ_ o = ⨆ a : Iio o, ℵ_ a
参数：ho : IsSuccLimit o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsNormal.apply_of_isSuccLimit`：apply_of_isSuccLimit (hf : IsNormal
 f) (ha : IsSuccLimit a) : f a = ⨆ b : Iio a, f b
· 使用定理 `Cardinal.isNormal_aleph`：isNormal_aleph : Order.IsNormal aleph
-/
theorem aleph_limit {o : Ordinal} (ho : IsSuccLimit o) : ℵ_ o = ⨆ a : Iio o, ℵ_ a :=
  isNormal_aleph.apply_of_isSuccLimit ho

@[simp]
/-
**Cardinal.aleph0_le_aleph** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_le_aleph (o : Ordinal) : ℵ₀ <= ℵ_ o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.aleph_eq_preAleph`：aleph_eq_preAleph (o : Ordinal) : ℵ_ o = pre
Aleph (ω + o)
· 使用定理 `Cardinal.aleph0_le_preAleph`：aleph0_le_preAleph {o : Ordinal} : ℵ₀ <= pr
eAleph o ↔ ω <= o
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
-/
theorem aleph0_le_aleph (o : Ordinal) : ℵ₀ ≤ ℵ_ o := by
  rw [aleph_eq_preAleph, aleph0_le_preAleph]
  exact le_self_add

@[simp]
/-
**Cardinal.aleph0_lt_aleph** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_lt_aleph {o : Ordinal} : ℵ₀ < ℵ_ o ↔ 0 < o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.aleph_zero`：aleph_zero : ℵ_ 0 = ℵ₀
· 使用定理 `Cardinal.aleph_lt_aleph`：aleph_lt_aleph {o₁ o₂ : Ordinal} : ℵ_ o₁ < ℵ_ o
₂ ↔ o₁ < o₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem aleph0_lt_aleph {o : Ordinal} : ℵ₀ < ℵ_ o ↔ 0 < o := by
  rw [← aleph_zero, aleph_lt_aleph]
/-
**Cardinal.aleph_pos** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph_pos (o : Ordinal) : 0 < ℵ_ o
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Cardinal.aleph0_pos`：aleph0_pos : 0 < ℵ₀
· 使用定理 `Cardinal.aleph0_le_aleph`：aleph0_le_aleph (o : Ordinal) : ℵ₀ <= ℵ_ o
-/
theorem aleph_pos (o : Ordinal) : 0 < ℵ_ o :=
  aleph0_pos.trans_le (aleph0_le_aleph o)
/-
**Cardinal._root_.Ordinal.card_le_aleph** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Ordinal.card_le_aleph (o : Ordinal) : o.card ≤ ℵ_ o :=
  o.card_le_preAleph.trans (preAleph_le_aleph o)
/-
**Cardinal.le_aleph_ord** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：le_aleph_ord (c : Cardinal) : c <= ℵ_ c.ord
参数：c : Cardinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.card_ord`：card_ord (c) : (ord c).card = c
· 使用定理 `Ordinal.card_le_aleph`：∀ (o : Ordinal.{u_1}), o.card ≤ Cardinal.aleph o
-/
theorem le_aleph_ord (c : Cardinal) : c ≤ ℵ_ c.ord := by
  simpa using c.ord.card_le_aleph

@[simp]
/-
**Cardinal.aleph_toNat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph_toNat (o : Ordinal) : toNat (ℵ_ o) = 0
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.toNat_apply_of_aleph0_le`：toNat_apply_of_aleph0_le {c : Cardina
l} (h : ℵ₀ <= c) : toNat c = 0
· 使用定理 `Cardinal.aleph0_le_aleph`：aleph0_le_aleph (o : Ordinal) : ℵ₀ <= ℵ_ o
-/
theorem aleph_toNat (o : Ordinal) : toNat (ℵ_ o) = 0 :=
  toNat_apply_of_aleph0_le <| aleph0_le_aleph o

@[simp]
/-
**Cardinal.aleph_toENat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph_toENat (o : Ordinal) : toENat (ℵ_ o) = ⊤
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.toENat_eq_top`：∀ {c : Cardinal.{u}}, Cardinal.toENat c = ⊤ ↔ Ca
rdinal.aleph0 ≤ c
· 使用定理 `Cardinal.aleph0_le_aleph`：aleph0_le_aleph (o : Ordinal) : ℵ₀ <= ℵ_ o
-/
theorem aleph_toENat (o : Ordinal) : toENat (ℵ_ o) = ⊤ :=
  (toENat_eq_top.2 (aleph0_le_aleph o))
/-
**Cardinal.isSuccLimit_omega** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：isSuccLimit_omega (o : Ordinal) : IsSuccLimit (ω_ o)
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.ord_aleph`：ord_aleph (o : Ordinal) : (ℵ_ o).ord = ω_ o
· 使用定理 `Cardinal.isSuccLimit_ord`：isSuccLimit_ord {c} (hc : ℵ₀ <= c) : IsSuccLim
it (ord c)
· 使用定理 `Cardinal.aleph0_le_aleph`：aleph0_le_aleph (o : Ordinal) : ℵ₀ <= ℵ_ o
-/
theorem isSuccLimit_omega (o : Ordinal) : IsSuccLimit (ω_ o) := by
  rw [← ord_aleph]
  exact isSuccLimit_ord (aleph0_le_aleph _)

@[simp]
/-
**Cardinal.range_aleph** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：range_aleph : range aleph = Set.Ici ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Cardinal.aleph0_le_aleph`：aleph0_le_aleph (o : Ordinal) : ℵ₀ <= ℵ_ o
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.aleph_eq_preAleph`：aleph_eq_preAleph (o : Ordinal) : ℵ_ o = pre
Aleph (ω + o)
· 使用定理 `Ordinal.add_sub_cancel_of_le`：∀ {a b : Ordinal.{u_4}}, b ≤ a → b + (a - 
b) = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.aleph0_le_preAleph`：aleph0_le_preAleph {o : Ordinal} : ℵ₀ <= pr
eAleph o ↔ ω <= o
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
-/
theorem range_aleph : range aleph = Set.Ici ℵ₀ := by
  ext c
  refine ⟨fun ⟨o, e⟩ => e ▸ aleph0_le_aleph _, fun hc ↦ ⟨preAleph.symm c - ω, ?_⟩⟩
  rw [aleph_eq_preAleph, Ordinal.add_sub_cancel_of_le, preAleph.apply_symm_apply]
  rwa [← aleph0_le_preAleph, preAleph.apply_symm_apply]
/-
**Cardinal.mem_range_aleph_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mem_range_aleph_iff {c : Cardinal} : c in range aleph ↔ ℵ₀ <= c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.range_aleph`：range_aleph : range aleph = Set.Ici ℵ₀
· 使用定理 `Set.mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ici
 b ↔ b ≤ x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_range_aleph_iff {c : Cardinal} : c ∈ range aleph ↔ ℵ₀ ≤ c := by
  rw [range_aleph, mem_Ici]
/-
**Cardinal.lt_omega_iff_card_lt** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lt_omega_iff_card_lt {x o : Ordinal} : x < ω_ o ↔ x.card < ℵ_ o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.IsInitial.card_lt_card`：∀ {a b : Ordinal.{u_1}}, b.IsInitial → (
a.card < b.card ↔ a < b)
· 使用定理 `Ordinal.isInitial_omega`：isInitial_omega (o : Ordinal) : IsInitial (omeg
a o)
· 使用定理 `Ordinal.card_omega`：∀ (o : Ordinal.{u_1}), (Ordinal.omega o).card = Card
inal.aleph o
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_omega_iff_card_lt {x o : Ordinal} : x < ω_ o ↔ x.card < ℵ_ o := by
  rw [← (isInitial_omega o).card_lt_card, card_omega]

@[simp]
/-
**Cardinal.succ_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：succ_aleph0 : succ ℵ₀ = ℵ₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.aleph_zero`：aleph_zero : ℵ_ 0 = ℵ₀
· 使用定理 `Cardinal.succ_aleph`：succ_aleph (o : Ordinal) : succ (ℵ_ o) = ℵ_ (o + 1)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem succ_aleph0 : succ ℵ₀ = ℵ₁ := by
  rw [← aleph_zero, succ_aleph, zero_add]

@[simp]
/-
**Cardinal.aleph_one_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph_one_le_iff {c : Cardinal} : ℵ₁ <= c ↔ ℵ₀ < c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.succ_aleph0`：succ_aleph0 : succ ℵ₀ = ℵ₁
· 使用定理 `Order.succ_le_iff`：succ_le_iff : succ a <= b ↔ a < b
· 使用定理 `Cardinal.instNoMaxOrder`：NoMaxOrder Cardinal.{u}
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem aleph_one_le_iff {c : Cardinal} : ℵ₁ ≤ c ↔ ℵ₀ < c := by
  rw [← succ_aleph0, succ_le_iff]

@[simp]
/-
**Cardinal.lt_aleph_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lt_aleph_one_iff {c : Cardinal} : c < ℵ₁ ↔ c <= ℵ₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.succ_aleph0`：succ_aleph0 : succ ℵ₀ = ℵ₁
· 使用定理 `Order.lt_succ_iff`：lt_succ_iff : a < succ b ↔ a <= b
· 使用定理 `Cardinal.instNoMaxOrder`：NoMaxOrder Cardinal.{u}
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_aleph_one_iff {c : Cardinal} : c < ℵ₁ ↔ c ≤ ℵ₀ := by
  rw [← succ_aleph0, lt_succ_iff]
/-
**Cardinal.aleph0_lt_aleph_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_lt_aleph_one : ℵ₀ < ℵ₁
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem aleph0_lt_aleph_one : ℵ₀ < ℵ₁ := by simp

@[deprecated aleph_one_le_iff (since := "2026-03-23")]
/-
**Cardinal.aleph0_lt_iff_aleph_one_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_lt_iff_aleph_one_le {c} : ℵ₀ < c ↔ ℵ₁ <= c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Cardinal.aleph_one_le_iff`：aleph_one_le_iff {c : Cardinal} : ℵ₁ <= c ↔ ℵ
₀ < c
-/
theorem aleph0_lt_iff_aleph_one_le {c} : ℵ₀ < c ↔ ℵ₁ ≤ c :=
  aleph_one_le_iff.symm

@[deprecated aleph0_lt_mk_iff (since := "2026-03-23")]
/-
**Cardinal.aleph1_le_mk_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph1_le_mk_iff {α : Type*} : ℵ₁ <= #α ↔ Uncountable α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.aleph_one_le_iff`：aleph_one_le_iff {c : Cardinal} : ℵ₁ <= c ↔ ℵ
₀ < c
· 使用定理 `Cardinal.aleph0_lt_mk_iff`：aleph0_lt_mk_iff : ℵ₀ < #α ↔ Uncountable α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem aleph1_le_mk_iff {α : Type*} : ℵ₁ ≤ #α ↔ Uncountable α := by
  rw [aleph_one_le_iff, aleph0_lt_mk_iff]

@[deprecated aleph0_lt_mk (since := "2026-03-23")]
/-
**Cardinal.aleph1_le_mk** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph1_le_mk (α : Type*) [Uncountable α] : ℵ₁ <= #α
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem aleph1_le_mk (α : Type*) [Uncountable α] : ℵ₁ ≤ #α := by
  simp

@[deprecated le_aleph0_iff_set_countable (since := "2026-03-23")]
/-
**Cardinal.countable_iff_lt_aleph_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：countable_iff_lt_aleph_one {α : Type*} (s : Set α) : s.Countable ↔ #s < ℵ₁
参数：s : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lt_aleph_one_iff`：lt_aleph_one_iff {c : Cardinal} : c < ℵ₁ ↔ c 
<= ℵ₀
· 使用定理 `Cardinal.le_aleph0_iff_set_countable`：le_aleph0_iff_set_countable {s : S
et α} : #s <= ℵ₀ ↔ s.Countable
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem countable_iff_lt_aleph_one {α : Type*} (s : Set α) : s.Countable ↔ #s < ℵ₁ := by
  rw [lt_aleph_one_iff, le_aleph0_iff_set_countable]
/-
**Cardinal.preAleph_of_omega0_sq_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preAleph_of_omega0_sq_le {o : Ordinal} (ho : ω ^ 2 <= o) : preAleph o = ℵ_
 o
参数：ho : ω ^ 2 <= o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.ord_preAleph`：ord_preAleph (o : Ordinal) : (preAleph o).ord = p
reOmega o
· 使用定理 `Cardinal.ord_aleph`：ord_aleph (o : Ordinal) : (ℵ_ o).ord = ω_ o
· 使用定理 `Ordinal.preOmega_of_omega0_sq_le`：preOmega_of_omega0_sq_le {o : Ordinal}
 (ho : ω ^ 2 <= o) : preOmega o = ω_ o
-/
theorem preAleph_of_omega0_sq_le {o : Ordinal} (ho : ω ^ 2 ≤ o) : preAleph o = ℵ_ o := by
  simpa [← ord_inj] using preOmega_of_omega0_sq_le ho

end Cardinal

/-! ### Beth cardinals -/

namespace Cardinal

/-- The "pre-beth" function is defined so that `preBeth o` is the supremum of `2 ^ preBeth a` for
`a < o`. This implies `beth 0 = 0`, `beth (succ o) = 2 ^ beth o`, and that for a limit ordinal `o`,
`beth o` is the supremum of `beth a` for `a < o`.

For the usual function starting at `ℵ₀`, see `Cardinal.beth`. -/
/-
**Cardinal.preBeth** 是 Mathlib 中的一个定义，位于命名空间 `Cardinal`。
形式化陈述：preBeth (o : Ordinal.{u}) : Cardinal.{u}
参数：o : Ordinal.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "pre-beth" function is defined so that `preBeth o` is the supremum of `2 ^ p
reBeth a` for
`a < o`. This implies `beth 0 = 0`, `beth (succ o) = 2 ^ beth o`, and that for a
 limit ordinal `o`,
`beth o` is the supremum of `beth a` for `a < o`.

For the usual function starting at `ℵ₀`, see `Cardinal.beth`.
-/
def preBeth (o : Ordinal.{u}) : Cardinal.{u} :=
  ⨆ a : Iio o, 2 ^ preBeth a
termination_by o
decreasing_by exact a.2
/-
**Cardinal.preBeth_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preBeth_strictMono : StrictMono preBeth
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.preBeth.eq_1`：∀ (o : Ordinal.{u}), Cardinal.preBeth o = ⨆ a, 2 
^ Cardinal.preBeth ↑a
· 使用定理 `lt_ciSup_iff'`：lt_ciSup_iff' {f : ι -> α} (h : BddAbove (range f)) : a <
 iSup f ↔ exists i, a < f i
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `Cardinal.cantor`：cantor (a : Cardinal.{u}) : a < 2 ^ a
-/
theorem preBeth_strictMono : StrictMono preBeth := by
  intro a b h
  conv_rhs => rw [preBeth]
  rw [lt_ciSup_iff' bddAbove_of_small]
  exact ⟨⟨a, h⟩, cantor _⟩
/-
**Cardinal.preBeth_mono** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preBeth_mono : Monotone preBeth
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Cardinal.preBeth_strictMono`：preBeth_strictMono : StrictMono preBeth
-/
theorem preBeth_mono : Monotone preBeth :=
  preBeth_strictMono.monotone
/-
**Cardinal.preAleph_le_preBeth** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preAleph_le_preBeth (o : Ordinal) : preAleph o <= preBeth o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.preAleph_le_of_strictMono`：preAleph_le_of_strictMono {f : Ordin
al -> Cardinal} (hf : StrictMono f) (o : Ordinal) : preAleph o <= f o
· 使用定理 `Cardinal.preBeth_strictMono`：preBeth_strictMono : StrictMono preBeth
-/
theorem preAleph_le_preBeth (o : Ordinal) : preAleph o ≤ preBeth o :=
  preAleph_le_of_strictMono preBeth_strictMono o

@[simp]
/-
**Cardinal.preBeth_lt_preBeth** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preBeth_lt_preBeth {o₁ o₂ : Ordinal} : preBeth o₁ < preBeth o₂ ↔ o₁ < o₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `Cardinal.preBeth_strictMono`：preBeth_strictMono : StrictMono preBeth
-/
theorem preBeth_lt_preBeth {o₁ o₂ : Ordinal} : preBeth o₁ < preBeth o₂ ↔ o₁ < o₂ :=
  preBeth_strictMono.lt_iff_lt

@[simp]
/-
**Cardinal.preBeth_le_preBeth** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preBeth_le_preBeth {o₁ o₂ : Ordinal} : preBeth o₁ <= preBeth o₂ ↔ o₁ <= o₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `Cardinal.preBeth_strictMono`：preBeth_strictMono : StrictMono preBeth
-/
theorem preBeth_le_preBeth {o₁ o₂ : Ordinal} : preBeth o₁ ≤ preBeth o₂ ↔ o₁ ≤ o₂ :=
  preBeth_strictMono.le_iff_le

@[simp]
/-
**Cardinal.preBeth_inj** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preBeth_inj {o₁ o₂ : Ordinal} : preBeth o₁ = preBeth o₂ ↔ o₁ = o₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `Cardinal.preBeth_strictMono`：preBeth_strictMono : StrictMono preBeth
-/
theorem preBeth_inj {o₁ o₂ : Ordinal} : preBeth o₁ = preBeth o₂ ↔ o₁ = o₂ :=
  preBeth_strictMono.injective.eq_iff

@[simp]
/-
**Cardinal.preBeth_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preBeth_zero : preBeth 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.preBeth.eq_1`：∀ (o : Ordinal.{u}), Cardinal.preBeth o = ⨆ a, 2 
^ Cardinal.preBeth ↑a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ciSup_of_empty`：ciSup_of_empty [IsEmpty ι] (f : ι -> α) : ⨆ i, f i = ⊥
· 使用定理 `Set.isEmpty_Iio_zero`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Zer
o α] [IsBotZeroClass α], IsEmpty ↑(Set.Iio 0)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preBeth_zero : preBeth 0 = 0 := by
  rw [preBeth]
  simp

@[simp]
/-
**Cardinal.preBeth_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preBeth_add_one (o : Ordinal) : preBeth (o + 1) = 2 ^ preBeth o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.preBeth.eq_1`：∀ (o : Ordinal.{u}), Cardinal.preBeth o = ⨆ a, 2 
^ Cardinal.preBeth ↑a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Order.Iio_succ`：Iio_succ (a : α) : Iio (succ a) = Iic a
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `ciSup_Iic`：ciSup_Iic [Preorder β] {f : β -> α} (a : β) (hf : Monotone f)
 : ⨆ x : Iic a, f x = f a
· 使用定理 `Cardinal.power_le_power_left`：power_le_power_left : forall {a b c : Card
inal}, a != 0 -> b <= c -> a ^ b <= a ^ c
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Cardinal.preBeth_mono`：preBeth_mono : Monotone preBeth
-/
theorem preBeth_add_one (o : Ordinal) : preBeth (o + 1) = 2 ^ preBeth o := by
  rw [preBeth, ← succ_eq_add_one, Iio_succ]
  exact ciSup_Iic o fun x y h ↦ power_le_power_left two_ne_zero (preBeth_mono h)

@[deprecated preBeth_add_one (since := "2026-05-26")]
/-
**Cardinal.preBeth_succ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preBeth_succ (o : Ordinal) : preBeth (succ o) = 2 ^ preBeth o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.preBeth_add_one`：preBeth_add_one (o : Ordinal) : preBeth (o + 1
) = 2 ^ preBeth o
-/
theorem preBeth_succ (o : Ordinal) : preBeth (succ o) = 2 ^ preBeth o :=
  preBeth_add_one o
/-
**Cardinal.preBeth_limit** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preBeth_limit {o : Ordinal} (ho : IsSuccPrelimit o) : preBeth o = ⨆ a : Ii
o o, preBeth a
参数：ho : IsSuccPrelimit o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.preBeth.eq_1`：∀ (o : Ordinal.{u}), Cardinal.preBeth o = ⨆ a, 2 
^ Cardinal.preBeth ↑a
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ciSup_mono`：ciSup_mono {f g : ι -> α} (B : BddAbove (range g)) (H : fora
ll x, f x <= g x) : iSup f <= iSup g
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Cardinal.cantor`：cantor (a : Cardinal.{u}) : a < 2 ^ a
· 使用定理 `ciSup_le_iff'`：ciSup_le_iff' {f : ι -> α} (h : BddAbove (range f)) {a : 
α} : ⨆ i, f i <= a ↔ forall i, f i <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.preBeth_add_one`：preBeth_add_one (o : Ordinal) : preBeth (o + 1
) = 2 ^ preBeth o
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用定理 `Order.IsSuccPrelimit.succ_lt`：∀ {α : Type u_1} {a b : α} [inst : Partial
Order α] [inst_1 : SuccOrder α],   Order.IsSuccPrelimit b → a < b → Order.succ a
 < b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem preBeth_limit {o : Ordinal} (ho : IsSuccPrelimit o) :
    preBeth o = ⨆ a : Iio o, preBeth a := by
  rw [preBeth]
  apply (ciSup_mono bddAbove_of_small fun _ ↦ (cantor _).le).antisymm'
  rw [ciSup_le_iff' bddAbove_of_small]
  intro a
  rw [← preBeth_add_one]
  exact le_ciSup bddAbove_of_small (⟨_, ho.succ_lt a.2⟩ : Iio o)
/-
**Cardinal.isNormal_preBeth** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：isNormal_preBeth : Order.IsNormal preBeth
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.isNormal_iff`：isNormal_iff [LinearOrder α] [LinearOrder β] {f : α 
-> β} : IsNormal f ↔ StrictMono f ∧ forall o, IsSuccLimit o -> forall a, (forall
 b < o, …
· 使用定理 `Cardinal.preBeth_strictMono`：preBeth_strictMono : StrictMono preBeth
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.preBeth_limit`：preBeth_limit {o : Ordinal} (ho : IsSuccPrelimit
 o) : preBeth o = ⨆ a : Iio o, preBeth a
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
· 使用定理 `ciSup_le_iff'`：ciSup_le_iff' {f : ι -> α} (h : BddAbove (range f)) {a : 
α} : ⨆ i, f i <= a ↔ forall i, f i <= a
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem isNormal_preBeth : Order.IsNormal preBeth := by
  rw [isNormal_iff]
  refine ⟨preBeth_strictMono, fun o ho ↦ ?_⟩
  simp [preBeth_limit ho.isSuccPrelimit, ciSup_le_iff' bddAbove_of_small]
/-
**Cardinal.preBeth_nat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ (n : ℕ), Cardinal.preBeth ↑n = ↑((fun x => 2 ^ x)^[n] 0)
参数：n : ℕ；(fun x => 2 ^ x)^[n] 0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preBeth_nat : ∀ n : ℕ, preBeth n = (2 ^ ·)^[n] (0 : ℕ)
  | 0 => by simp
  | n + 1 => by simp [Function.iterate_succ_apply', preBeth_nat]

@[simp]
/-
**Cardinal.preBeth_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preBeth_one : preBeth 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_one`：iterate_one : f^[1] = f
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Cardinal.preBeth_nat`：∀ (n : ℕ), Cardinal.preBeth ↑n = ↑((fun x => 2 ^ x
)^[n] 0)
-/
theorem preBeth_one : preBeth 1 = 1 := by
  simpa using preBeth_nat 1

@[simp]
/-
**Cardinal.preBeth_omega** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preBeth_omega : preBeth ω = ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.preBeth_limit`：preBeth_limit {o : Ordinal} (ho : IsSuccPrelimit
 o) : preBeth o = ⨆ a : Iio o, preBeth a
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
· 使用定理 `Ordinal.isSuccLimit_omega0`：isSuccLimit_omega0 : IsSuccLimit ω
· 使用定理 `ciSup_le_iff'`：ciSup_le_iff' {f : ι -> α} (h : BddAbove (range f)) {a : 
α} : ⨆ i, f i <= a ↔ forall i, f i <= a
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.lt_omega0`：lt_omega0 {o : Ordinal} : o < ω ↔ exists n : Nat, o =
 n
· 使用定理 `Cardinal.preBeth_nat`：∀ (n : ℕ), Cardinal.preBeth ↑n = ↑((fun x => 2 ^ x
)^[n] 0)
· 使用定理 `Cardinal.natCast_le_aleph0`：∀ {n : ℕ}, ↑n ≤ Cardinal.aleph0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.preAleph_omega0`：preAleph_omega0 : preAleph ω = ℵ₀
· 使用定理 `Cardinal.preAleph_le_preBeth`：preAleph_le_preBeth (o : Ordinal) : preAle
ph o <= preBeth o
-/
theorem preBeth_omega : preBeth ω = ℵ₀ := by
  apply le_antisymm
  · rw [preBeth_limit isSuccLimit_omega0.isSuccPrelimit, ciSup_le_iff' bddAbove_of_small]
    rintro ⟨a, ha⟩
    obtain ⟨n, rfl⟩ := lt_omega0.1 ha
    rw [preBeth_nat]
    exact natCast_le_aleph0
  · simpa using preAleph_le_preBeth ω

@[simp]
/-
**Cardinal.preBeth_pos** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preBeth_pos {o : Ordinal} : 0 < preBeth o ↔ 0 < o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.preBeth_zero`：preBeth_zero : preBeth 0 = 0
· 使用定理 `Cardinal.preBeth_lt_preBeth`：preBeth_lt_preBeth {o₁ o₂ : Ordinal} : preB
eth o₁ < preBeth o₂ ↔ o₁ < o₂
-/
theorem preBeth_pos {o : Ordinal} : 0 < preBeth o ↔ 0 < o := by
  simpa using preBeth_lt_preBeth (o₁ := 0)
/-
**Cardinal._root_.Ordinal.card_le_preBeth** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Ordinal.card_le_preBeth (o : Ordinal) : o.card ≤ preBeth o :=
  o.card_le_preAleph.trans (preAleph_le_preBeth o)
/-
**Cardinal.le_preBeth_ord** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：le_preBeth_ord (c : Cardinal) : c <= preBeth c.ord
参数：c : Cardinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.card_ord`：card_ord (c) : (ord c).card = c
· 使用定理 `Ordinal.card_le_preBeth`：∀ (o : Ordinal.{u_1}), o.card ≤ Cardinal.preBet
h o
-/
theorem le_preBeth_ord (c : Cardinal) : c ≤ preBeth c.ord := by
  simpa using c.ord.card_le_preBeth

@[simp]
/-
**Cardinal.preBeth_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preBeth_eq_zero {o : Ordinal} : preBeth o = 0 ↔ o = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.preBeth_zero`：preBeth_zero : preBeth 0 = 0
· 使用定理 `Cardinal.preBeth_inj`：preBeth_inj {o₁ o₂ : Ordinal} : preBeth o₁ = preBe
th o₂ ↔ o₁ = o₂
-/
theorem preBeth_eq_zero {o : Ordinal} : preBeth o = 0 ↔ o = 0 := by
  simpa using preBeth_inj (o₂ := 0)

@[simp]
/-
**Cardinal.isStrongPrelimit_preBeth** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：isStrongPrelimit_preBeth {o : Ordinal} : IsStrongPrelimit (preBeth o) ↔ Is
SuccPrelimit o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.not_isSuccPrelimit_iff_mem_range_succ`：not_isSuccPrelimit_iff_mem_
range_succ : ¬ IsSuccPrelimit a ↔ a in range (succ : α -> α)
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Cardinal.not_isStrongPrelimit_iff`：not_isStrongPrelimit_iff {c} : ¬ IsSt
rongPrelimit c ↔ exists x < c, c <= 2 ^ x
· 使用定理 `Cardinal.preBeth_lt_preBeth`：preBeth_lt_preBeth {o₁ o₂ : Ordinal} : preB
eth o₁ < preBeth o₂ ↔ o₁ < o₂
· 使用定理 `Order.lt_succ_iff`：lt_succ_iff : a < succ b ↔ a <= b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Cardinal.preBeth_add_one`：preBeth_add_one (o : Ordinal) : preBeth (o + 1
) = 2 ^ preBeth o
· 使用定理 `exists_lt_of_lt_ciSup'`：exists_lt_of_lt_ciSup' {f : ι -> α} {a : α} (h :
 a < ⨆ i, f i) : exists i, a < f i
· 使用定理 `Cardinal.preBeth_limit`：preBeth_limit {o : Ordinal} (ho : IsSuccPrelimit
 o) : preBeth o = ⨆ a : Iio o, preBeth a
· 使用定理 `LT.lt.trans_le'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b < a
 → c ≤ b → c < a
· 使用定理 `Cardinal.preBeth_strictMono`：preBeth_strictMono : StrictMono preBeth
· 使用定理 `Order.IsSuccPrelimit.add_one_lt`：∀ {α : Type u_1} {x y : α} [inst : Part
ialOrder α] [inst_1 : Add α] [inst_2 : One α] [SuccAddOrder α],   Order.IsSuccPr
elimit x → y < x → y …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Cardinal.power_le_power_left`：power_le_power_left : forall {a b c : Card
inal}, a != 0 -> b <= c -> a ^ b <= a ^ c
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem isStrongPrelimit_preBeth {o : Ordinal} :
    IsStrongPrelimit (preBeth o) ↔ IsSuccPrelimit o := by
  refine ⟨?_, fun ho x hx ↦ ?_⟩
  · contrapose!
    rw [not_isSuccPrelimit_iff_mem_range_succ, not_isStrongPrelimit_iff]
    rintro ⟨a, rfl⟩
    refine ⟨preBeth a, ?_, ?_⟩
    · rw [preBeth_lt_preBeth, lt_succ_iff]
    · simp
  · rw [preBeth_limit ho] at hx
    obtain ⟨a, ha⟩ := exists_lt_of_lt_ciSup' hx
    apply (preBeth_strictMono (ho.add_one_lt a.2)).trans_le'
    simpa using power_le_power_left two_ne_zero ha.le

@[simp]
/-
**Cardinal.isStrongLimit_preBeth** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：isStrongLimit_preBeth {o : Ordinal} : IsStrongLimit (preBeth o) ↔ IsSuccLi
mit o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.isStrongLimit_iff`：∀ (c : Cardinal.{u_1}), c.IsStrongLimit ↔ c 
≠ 0 ∧ c.IsStrongPrelimit
· 使用定理 `Ordinal.isSuccLimit_iff`：isSuccLimit_iff {o : Ordinal} : IsSuccLimit o ↔
 o != 0 ∧ IsSuccPrelimit o
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用定理 `Cardinal.preBeth_eq_zero`：preBeth_eq_zero {o : Ordinal} : preBeth o = 0 
↔ o = 0
· 使用定理 `Cardinal.isStrongPrelimit_preBeth`：isStrongPrelimit_preBeth {o : Ordinal
} : IsStrongPrelimit (preBeth o) ↔ IsSuccPrelimit o
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isStrongLimit_preBeth {o : Ordinal} : IsStrongLimit (preBeth o) ↔ IsSuccLimit o := by
  rw [isStrongLimit_iff, isSuccLimit_iff, preBeth_eq_zero.ne, isStrongPrelimit_preBeth]

@[simp]
/-
**Cardinal.lift_preBeth** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_preBeth (o : Ordinal) : lift.{v} (preBeth o) = preBeth (Ordinal.lift.
{v} o)
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Cardinal.preBeth_add_one`：preBeth_add_one (o : Ordinal) : preBeth (o + 1
) = 2 ^ preBeth o
· 使用定理 `Cardinal.lift_power`：lift_power (a b : Cardinal.{u}) : lift.{v} (a ^ b) 
= lift.{v} a ^ lift.{v} b
· 使用定理 `Cardinal.lift_ofNat`：lift_ofNat (n : Nat) [n.AtLeastTwo] : lift.{u} (ofN
at(n) : Cardinal.{v}) = OfNat.ofNat n
· 使用定理 `Ordinal.lift_add`：lift_add (a b : Ordinal.{v}) : lift.{u} (a + b) = lift
.{u} a + lift.{u} b
· 使用定理 `Ordinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Cardinal.preBeth_limit`：preBeth_limit {o : Ordinal} (ho : IsSuccPrelimit
 o) : preBeth o = ⨆ a : Iio o, preBeth a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.isSuccPrelimit_lift`：isSuccPrelimit_lift {o : Ordinal} : IsSuccP
relimit (lift.{u, v} o) ↔ IsSuccPrelimit o
· 使用定理 `Cardinal.lift_iSup`：lift_iSup {ι : Type v} {f : ι -> Cardinal.{w}} (hf :
 BddAbove (range f)) : lift.{u} (iSup f) = ⨆ i, lift.{u} (f i)
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.mem_range_lift_of_le`：mem_range_lift_of_le {a : Ordinal.{u}} {b 
: Ordinal.{max u v}} (h : b <= lift.{v} a) : b in Set.range lift.{v}
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Ordinal.lift_lt`：lift_lt {a b : Ordinal} : lift.{u, v} a < lift.{u, v} b
 ↔ a < b
· 使用定理 `Set.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iio
 b ↔ x < b
-/
theorem lift_preBeth (o : Ordinal) : lift.{v} (preBeth o) = preBeth (Ordinal.lift.{v} o) := by
  induction o using SuccOrder.prelimitRecOn with
  | succ o _ IH => simp [IH]
  | isSuccPrelimit o ho IH =>
    rw [preBeth_limit ho, preBeth_limit (isSuccPrelimit_lift.2 ho), lift_iSup bddAbove_of_small]
    apply congrArg sSup
    ext x
    constructor <;> rintro ⟨⟨i, hi⟩, rfl⟩
    · refine ⟨⟨i.lift, ?_⟩, (IH _ hi).symm⟩
      simpa
    · obtain ⟨i, rfl⟩ := Ordinal.mem_range_lift_of_le hi.le
      rw [mem_Iio, Ordinal.lift_lt] at hi
      exact ⟨⟨i, hi⟩, IH _ hi⟩

/-- The Beth function is defined so that `beth 0 = ℵ₀`, `beth (succ o) = 2 ^ beth o`, and that for a
limit ordinal `o`, `beth o` is the supremum of `beth a` for `a < o`.

Assuming the generalized continuum hypothesis, which is undecidable in ZFC, we have `ℶ_ o = ℵ_ o`
for all ordinals.

For a version which starts at zero, see `Cardinal.preBeth`. -/
/-
**Cardinal.beth** 是 Mathlib 中的一个定义，位于命名空间 `Cardinal`。
形式化陈述：beth (o : Ordinal.{u}) : Cardinal.{u}
参数：o : Ordinal.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Beth function is defined so that `beth 0 = ℵ₀`, `beth (succ o) = 2 ^ beth o`
, and that for a
limit ordinal `o`, `beth o` is the supremum of `beth a` for `a < o`.

Assuming the generalized continuum hypothesis, which is undecidable in ZFC, we h
ave `ℶ_ o = ℵ_ o`
for all ordinals.

For a version which starts at zero, see `Cardinal.preBeth`.
-/
def beth (o : Ordinal.{u}) : Cardinal.{u} :=
  preBeth (ω + o)

@[inherit_doc] scoped notation "ℶ_ " => beth
recommended_spelling "beth" for "ℶ_" in [«termℶ_»]
/-
**Cardinal.beth_eq_preBeth** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：beth_eq_preBeth (o : Ordinal) : beth o = preBeth (ω + o)
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem beth_eq_preBeth (o : Ordinal) : beth o = preBeth (ω + o) :=
  rfl
/-
**Cardinal.preBeth_le_beth** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preBeth_le_beth (o : Ordinal) : preBeth o <= ℶ_ o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.preBeth_le_preBeth`：preBeth_le_preBeth {o₁ o₂ : Ordinal} : preB
eth o₁ <= preBeth o₂ ↔ o₁ <= o₂
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
-/
theorem preBeth_le_beth (o : Ordinal) : preBeth o ≤ ℶ_ o :=
  preBeth_le_preBeth.2 le_add_self
/-
**Cardinal.beth_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：beth_strictMono : StrictMono beth
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
· 使用定理 `Cardinal.preBeth_strictMono`：preBeth_strictMono : StrictMono preBeth
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
-/
theorem beth_strictMono : StrictMono beth :=
  preBeth_strictMono.comp fun _ _ h ↦ by gcongr
/-
**Cardinal.beth_mono** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：beth_mono : Monotone beth
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Cardinal.beth_strictMono`：beth_strictMono : StrictMono beth
-/
theorem beth_mono : Monotone beth :=
  beth_strictMono.monotone

@[simp]
/-
**Cardinal.beth_lt_beth** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：beth_lt_beth {o₁ o₂ : Ordinal} : ℶ_ o₁ < ℶ_ o₂ ↔ o₁ < o₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `Cardinal.beth_strictMono`：beth_strictMono : StrictMono beth
-/
theorem beth_lt_beth {o₁ o₂ : Ordinal} : ℶ_ o₁ < ℶ_ o₂ ↔ o₁ < o₂ :=
  beth_strictMono.lt_iff_lt

@[simp]
/-
**Cardinal.beth_le_beth** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：beth_le_beth {o₁ o₂ : Ordinal} : ℶ_ o₁ <= ℶ_ o₂ ↔ o₁ <= o₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `Cardinal.beth_strictMono`：beth_strictMono : StrictMono beth
-/
theorem beth_le_beth {o₁ o₂ : Ordinal} : ℶ_ o₁ ≤ ℶ_ o₂ ↔ o₁ ≤ o₂ :=
  beth_strictMono.le_iff_le

@[simp]
/-
**Cardinal.beth_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：beth_zero : ℶ_ 0 = ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Cardinal.preBeth_omega`：preBeth_omega : preBeth ω = ℵ₀
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem beth_zero : ℶ_ 0 = ℵ₀ := by
  simp [beth]

@[simp]
/-
**Cardinal.beth_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：beth_add_one (o : Ordinal) : ℶ_ (o + 1) = 2 ^ ℶ_ o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.preBeth_add_one`：preBeth_add_one (o : Ordinal) : preBeth (o + 1
) = 2 ^ preBeth o
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem beth_add_one (o : Ordinal) : ℶ_ (o + 1) = 2 ^ ℶ_ o := by
  simp [beth, ← add_assoc]

-- TODO; deprecate
/-
**Cardinal.beth_succ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：beth_succ (o : Ordinal) : ℶ_ (succ o) = 2 ^ ℶ_ o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.beth_add_one`：beth_add_one (o : Ordinal) : ℶ_ (o + 1) = 2 ^ ℶ_ 
o
-/
theorem beth_succ (o : Ordinal) : ℶ_ (succ o) = 2 ^ ℶ_ o :=
  beth_add_one o
/-
**Cardinal.isNormal_beth** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：isNormal_beth : Order.IsNormal beth
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsNormal.comp`：comp (hg : IsNormal g) (hf : IsNormal f) : IsNormal
 (g ∘ f)
· 使用定理 `Cardinal.isNormal_preBeth`：isNormal_preBeth : Order.IsNormal preBeth
· 使用定理 `Ordinal.isNormal_add_right`：isNormal_add_right (a : Ordinal) : IsNormal 
(a + ·)
-/
theorem isNormal_beth : Order.IsNormal beth :=
  isNormal_preBeth.comp (isNormal_add_right _)
/-
**Cardinal.beth_limit** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：beth_limit {o : Ordinal} (ho : IsSuccLimit o) : ℶ_ o = ⨆ a : Iio o, ℶ_ a
参数：ho : IsSuccLimit o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsNormal.apply_of_isSuccLimit`：apply_of_isSuccLimit (hf : IsNormal
 f) (ha : IsSuccLimit a) : f a = ⨆ b : Iio a, f b
· 使用定理 `Cardinal.isNormal_beth`：isNormal_beth : Order.IsNormal beth
-/
theorem beth_limit {o : Ordinal} (ho : IsSuccLimit o) : ℶ_ o = ⨆ a : Iio o, ℶ_ a :=
  isNormal_beth.apply_of_isSuccLimit ho
/-
**Cardinal.aleph_le_beth** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph_le_beth (o : Ordinal) : ℵ_ o <= ℶ_ o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.preAleph_le_preBeth`：preAleph_le_preBeth (o : Ordinal) : preAle
ph o <= preBeth o
-/
theorem aleph_le_beth (o : Ordinal) : ℵ_ o ≤ ℶ_ o :=
  preAleph_le_preBeth _
/-
**Cardinal.aleph0_le_beth** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_le_beth (o : Ordinal) : ℵ₀ <= ℶ_ o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.aleph0_le_aleph`：aleph0_le_aleph (o : Ordinal) : ℵ₀ <= ℵ_ o
· 使用定理 `Cardinal.aleph_le_beth`：aleph_le_beth (o : Ordinal) : ℵ_ o <= ℶ_ o
-/
theorem aleph0_le_beth (o : Ordinal) : ℵ₀ ≤ ℶ_ o :=
  (aleph0_le_aleph o).trans <| aleph_le_beth o
/-
**Cardinal.beth_pos** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：beth_pos (o : Ordinal) : 0 < ℶ_ o
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Cardinal.aleph0_pos`：aleph0_pos : 0 < ℵ₀
· 使用定理 `Cardinal.aleph0_le_beth`：aleph0_le_beth (o : Ordinal) : ℵ₀ <= ℶ_ o
-/
theorem beth_pos (o : Ordinal) : 0 < ℶ_ o :=
  aleph0_pos.trans_le <| aleph0_le_beth o
/-
**Cardinal.beth_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：beth_ne_zero (o : Ordinal) : ℶ_ o != 0
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Cardinal.beth_pos`：beth_pos (o : Ordinal) : 0 < ℶ_ o
-/
theorem beth_ne_zero (o : Ordinal) : ℶ_ o ≠ 0 :=
  (beth_pos o).ne'
/-
**Cardinal._root_.Ordinal.card_le_beth** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Ordinal.card_le_beth (o : Ordinal) : o.card ≤ ℶ_ o :=
  o.card_le_aleph.trans (aleph_le_beth o)
/-
**Cardinal.le_beth_ord** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：le_beth_ord (c : Cardinal) : c <= ℶ_ c.ord
参数：c : Cardinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.card_ord`：card_ord (c) : (ord c).card = c
· 使用定理 `Ordinal.card_le_beth`：∀ (o : Ordinal.{u_1}), o.card ≤ Cardinal.beth o
-/
theorem le_beth_ord (c : Cardinal) : c ≤ ℶ_ c.ord := by
  simpa using c.ord.card_le_beth

@[simp]
/-
**Cardinal.isStrongLimit_beth** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：isStrongLimit_beth {o : Ordinal} : IsStrongLimit (ℶ_ o) ↔ IsSuccPrelimit o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.beth_eq_preBeth`：beth_eq_preBeth (o : Ordinal) : beth o = preBe
th (ω + o)
· 使用定理 `Cardinal.isStrongLimit_preBeth`：isStrongLimit_preBeth {o : Ordinal} : Is
StrongLimit (preBeth o) ↔ IsSuccLimit o
· 使用定理 `Ordinal.isSuccLimit_add_iff_of_isSuccLimit`：isSuccLimit_add_iff_of_isSuc
cLimit {a b : Ordinal} (h : IsSuccLimit a) : IsSuccLimit (a + b) ↔ IsSuccPrelimi
t b
· 使用定理 `Ordinal.isSuccLimit_omega0`：isSuccLimit_omega0 : IsSuccLimit ω
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isStrongLimit_beth {o : Ordinal} : IsStrongLimit (ℶ_ o) ↔ IsSuccPrelimit o := by
  rw [beth_eq_preBeth, isStrongLimit_preBeth, isSuccLimit_add_iff_of_isSuccLimit isSuccLimit_omega0]

@[simp]
/-
**Cardinal.lift_beth** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_beth (o : Ordinal) : lift.{v} (ℶ_ o) = ℶ_ (Ordinal.lift.{v} o)
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.beth_eq_preBeth`：beth_eq_preBeth (o : Ordinal) : beth o = preBe
th (ω + o)
· 使用定理 `Cardinal.lift_preBeth`：lift_preBeth (o : Ordinal) : lift.{v} (preBeth o)
 = preBeth (Ordinal.lift.{v} o)
· 使用定理 `Ordinal.lift_add`：lift_add (a b : Ordinal.{v}) : lift.{u} (a + b) = lift
.{u} a + lift.{u} b
· 使用定理 `Ordinal.lift_omega0`：lift_omega0 : lift ω = ω
-/
theorem lift_beth (o : Ordinal) : lift.{v} (ℶ_ o) = ℶ_ (Ordinal.lift.{v} o) := by
  rw [beth_eq_preBeth, beth_eq_preBeth, lift_preBeth, Ordinal.lift_add, lift_omega0]
/-
**Cardinal.preBeth_of_omega0_sq_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preBeth_of_omega0_sq_le {o : Ordinal} (ho : ω ^ 2 <= o) : preBeth o = ℶ_ o
参数：ho : ω ^ 2 <= o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.beth.eq_1`：∀ (o : Ordinal.{u}), Cardinal.beth o = Cardinal.preB
eth (Ordinal.omega0 + o)
· 使用定理 `Ordinal.add_of_omega0_opow_le`：add_of_omega0_opow_le (h₁ : a < ω ^ b) (h
₂ : ω ^ b <= c) : a + c = c
· 使用定理 `Ordinal.left_lt_opow`：left_lt_opow {a b : Ordinal} (ha : 1 < a) (hb : 1 
< b) : a < a ^ b
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.opow_natCast`：opow_natCast (a : Ordinal) (n : Nat) : a ^ (n : Or
dinal) = a ^ n
-/
theorem preBeth_of_omega0_sq_le {o : Ordinal} (ho : ω ^ 2 ≤ o) : preBeth o = ℶ_ o := by
  rw [← opow_natCast] at ho
  rw [beth, add_of_omega0_opow_le _ ho]
  apply left_lt_opow one_lt_omega0
  simp

/-! ### Simp lemmas with `lift` -/

section lift
variable {c : Cardinal.{u}} {n : ℕ}

@[deprecated aleph0_lt_lift (since := "2026-03-23")]
/-
**Cardinal.aleph_one_le_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph_one_le_lift : ℵ₁ <= lift.{v} c ↔ ℵ₁ <= c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem aleph_one_le_lift : ℵ₁ ≤ lift.{v} c ↔ ℵ₁ ≤ c := by
  simp

@[simp]
/-
**Cardinal.lift_le_aleph_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_le_aleph_one : lift.{v} c <= ℵ₁ ↔ c <= ℵ₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.lift_aleph`：lift_aleph (o : Ordinal.{u}) : lift.{v} (aleph o) =
 aleph (Ordinal.lift.{v} o)
· 使用定理 `Ordinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
-/
theorem lift_le_aleph_one : lift.{v} c ≤ ℵ₁ ↔ c ≤ ℵ₁ := by
  simpa using lift_le (b := ℵ₁)

@[simp]
/-
**Cardinal.aleph_one_lt_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph_one_lt_lift : ℵ₁ < lift.{v} c ↔ ℵ₁ < c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.lift_aleph`：lift_aleph (o : Ordinal.{u}) : lift.{v} (aleph o) =
 aleph (Ordinal.lift.{v} o)
· 使用定理 `Ordinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
-/
theorem aleph_one_lt_lift : ℵ₁ < lift.{v} c ↔ ℵ₁ < c := by
  simpa using lift_lt (a := ℵ₁)

@[deprecated lift_le_aleph0 (since := "2026-03-23")]
/-
**Cardinal.lift_lt_aleph_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_lt_aleph_one : lift.{v} c < ℵ₁ ↔ c < ℵ₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lift_lt_aleph_one : lift.{v} c < ℵ₁ ↔ c < ℵ₁ := by
  simp

@[simp]
/-
**Cardinal.aleph_one_eq_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph_one_eq_lift : ℵ₁ = lift.{v} c ↔ ℵ₁ = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.lift_aleph`：lift_aleph (o : Ordinal.{u}) : lift.{v} (aleph o) =
 aleph (Ordinal.lift.{v} o)
· 使用定理 `Ordinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
-/
theorem aleph_one_eq_lift : ℵ₁ = lift.{v} c ↔ ℵ₁ = c := by
  simpa using lift_inj (a := ℵ₁)

@[simp]
/-
**Cardinal.lift_eq_aleph_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_eq_aleph_one : lift.{v} c = ℵ₁ ↔ c = ℵ₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm_eq`：eq_comm_eq {α : Sort*} (a b : α) : (a = b) = (b = a)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lift_eq_aleph_one : lift.{v} c = ℵ₁ ↔ c = ℵ₁ := by
  simp [eqComm]

@[simp]
/-
**Cardinal.aleph_natCast_le_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph_natCast_le_lift : ℵ_ n <= lift.{v} c ↔ ℵ_ n <= c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.lift_aleph`：lift_aleph (o : Ordinal.{u}) : lift.{v} (aleph o) =
 aleph (Ordinal.lift.{v} o)
· 使用定理 `Ordinal.lift_natCast`：∀ (n : ℕ), Ordinal.lift.{u, v} ↑n = ↑n
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
-/
theorem aleph_natCast_le_lift : ℵ_ n ≤ lift.{v} c ↔ ℵ_ n ≤ c := by
  simpa using lift_le (a := ℵ_ n)

@[simp]
/-
**Cardinal.lift_le_aleph_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_le_aleph_natCast : lift.{v} c <= ℵ_ n ↔ c <= ℵ_ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.lift_aleph`：lift_aleph (o : Ordinal.{u}) : lift.{v} (aleph o) =
 aleph (Ordinal.lift.{v} o)
· 使用定理 `Ordinal.lift_natCast`：∀ (n : ℕ), Ordinal.lift.{u, v} ↑n = ↑n
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
-/
theorem lift_le_aleph_natCast : lift.{v} c ≤ ℵ_ n ↔ c ≤ ℵ_ n := by
  simpa using lift_le (b := ℵ_ n)

@[simp]
/-
**Cardinal.aleph_natCast_lt_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph_natCast_lt_lift : ℵ_ n < lift.{v} c ↔ ℵ_ n < c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.lift_aleph`：lift_aleph (o : Ordinal.{u}) : lift.{v} (aleph o) =
 aleph (Ordinal.lift.{v} o)
· 使用定理 `Ordinal.lift_natCast`：∀ (n : ℕ), Ordinal.lift.{u, v} ↑n = ↑n
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
-/
theorem aleph_natCast_lt_lift : ℵ_ n < lift.{v} c ↔ ℵ_ n < c := by
  simpa using lift_lt (a := ℵ_ n)

@[simp]
/-
**Cardinal.lift_lt_aleph_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_lt_aleph_natCast : lift.{v} c < ℵ_ n ↔ c < ℵ_ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.lift_aleph`：lift_aleph (o : Ordinal.{u}) : lift.{v} (aleph o) =
 aleph (Ordinal.lift.{v} o)
· 使用定理 `Ordinal.lift_natCast`：∀ (n : ℕ), Ordinal.lift.{u, v} ↑n = ↑n
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
-/
theorem lift_lt_aleph_natCast : lift.{v} c < ℵ_ n ↔ c < ℵ_ n := by
  simpa using lift_lt (b := ℵ_ n)

@[simp]
/-
**Cardinal.aleph_natCast_eq_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph_natCast_eq_lift : ℵ_ n = lift.{v} c ↔ ℵ_ n = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.lift_aleph`：lift_aleph (o : Ordinal.{u}) : lift.{v} (aleph o) =
 aleph (Ordinal.lift.{v} o)
· 使用定理 `Ordinal.lift_natCast`：∀ (n : ℕ), Ordinal.lift.{u, v} ↑n = ↑n
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
-/
theorem aleph_natCast_eq_lift : ℵ_ n = lift.{v} c ↔ ℵ_ n = c := by
  simpa using lift_inj (a := ℵ_ n)

@[simp]
/-
**Cardinal.lift_eq_aleph_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_eq_aleph_natCast : lift.{v} c = ℵ_ n ↔ c = ℵ_ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm_eq`：eq_comm_eq {α : Sort*} (a b : α) : (a = b) = (b = a)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lift_eq_aleph_natCast : lift.{v} c = ℵ_ n ↔ c = ℵ_ n := by
  simp [eqComm]

@[simp]
/-
**Cardinal.aleph_ofNat_le_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph_ofNat_le_lift [n.AtLeastTwo] : ℵ_ ofNat(n) <= lift.{v} c ↔ ℵ_ ofNat(
n) <= c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.aleph_natCast_le_lift`：aleph_natCast_le_lift : ℵ_ n <= lift.{v}
 c ↔ ℵ_ n <= c
-/
theorem aleph_ofNat_le_lift [n.AtLeastTwo] : ℵ_ ofNat(n) ≤ lift.{v} c ↔ ℵ_ ofNat(n) ≤ c :=
  aleph_natCast_le_lift

@[simp]
/-
**Cardinal.lift_le_aleph_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_le_aleph_ofNat [n.AtLeastTwo] : lift.{v} c <= ℵ_ ofNat(n) ↔ c <= ℵ_ o
fNat(n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.lift_le_aleph_natCast`：lift_le_aleph_natCast : lift.{v} c <= ℵ_
 n ↔ c <= ℵ_ n
-/
theorem lift_le_aleph_ofNat [n.AtLeastTwo] : lift.{v} c ≤ ℵ_ ofNat(n) ↔ c ≤ ℵ_ ofNat(n) :=
  lift_le_aleph_natCast

@[simp]
/-
**Cardinal.aleph_ofNat_lt_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph_ofNat_lt_lift [n.AtLeastTwo] : ℵ_ ofNat(n) < lift.{v} c ↔ ℵ_ ofNat(n
) < c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.aleph_natCast_lt_lift`：aleph_natCast_lt_lift : ℵ_ n < lift.{v} 
c ↔ ℵ_ n < c
-/
theorem aleph_ofNat_lt_lift [n.AtLeastTwo] : ℵ_ ofNat(n) < lift.{v} c ↔ ℵ_ ofNat(n) < c :=
  aleph_natCast_lt_lift

@[simp]
/-
**Cardinal.lift_lt_aleph_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_lt_aleph_ofNat [n.AtLeastTwo] : lift.{v} c < ℵ_ ofNat(n) ↔ c < ℵ_ ofN
at(n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.lift_lt_aleph_natCast`：lift_lt_aleph_natCast : lift.{v} c < ℵ_ 
n ↔ c < ℵ_ n
-/
theorem lift_lt_aleph_ofNat [n.AtLeastTwo] : lift.{v} c < ℵ_ ofNat(n) ↔ c < ℵ_ ofNat(n) :=
  lift_lt_aleph_natCast

@[simp]
/-
**Cardinal.aleph_ofNat_eq_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph_ofNat_eq_lift [n.AtLeastTwo] : ℵ_ ofNat(n) = lift.{v} c ↔ ℵ_ ofNat(n
) = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.aleph_natCast_eq_lift`：aleph_natCast_eq_lift : ℵ_ n = lift.{v} 
c ↔ ℵ_ n = c
-/
theorem aleph_ofNat_eq_lift [n.AtLeastTwo] : ℵ_ ofNat(n) = lift.{v} c ↔ ℵ_ ofNat(n) = c :=
  aleph_natCast_eq_lift

@[simp]
/-
**Cardinal.lift_eq_aleph_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_eq_aleph_ofNat [n.AtLeastTwo] : lift.{v} c = ℵ_ ofNat(n) ↔ c = ℵ_ ofN
at(n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.lift_eq_aleph_natCast`：lift_eq_aleph_natCast : lift.{v} c = ℵ_ 
n ↔ c = ℵ_ n
-/
theorem lift_eq_aleph_ofNat [n.AtLeastTwo] : lift.{v} c = ℵ_ ofNat(n) ↔ c = ℵ_ ofNat(n) :=
  lift_eq_aleph_natCast

@[simp]
/-
**Cardinal.beth_natCast_le_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：beth_natCast_le_lift : ℶ_ n <= lift.{v} c ↔ ℶ_ n <= c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.lift_beth`：lift_beth (o : Ordinal) : lift.{v} (ℶ_ o) = ℶ_ (Ordi
nal.lift.{v} o)
· 使用定理 `Ordinal.lift_natCast`：∀ (n : ℕ), Ordinal.lift.{u, v} ↑n = ↑n
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
-/
theorem beth_natCast_le_lift : ℶ_ n ≤ lift.{v} c ↔ ℶ_ n ≤ c := by
  simpa using lift_le (a := ℶ_ n)

@[simp]
/-
**Cardinal.lift_le_beth_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_le_beth_natCast : lift.{v} c <= ℶ_ n ↔ c <= ℶ_ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.lift_beth`：lift_beth (o : Ordinal) : lift.{v} (ℶ_ o) = ℶ_ (Ordi
nal.lift.{v} o)
· 使用定理 `Ordinal.lift_natCast`：∀ (n : ℕ), Ordinal.lift.{u, v} ↑n = ↑n
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
-/
theorem lift_le_beth_natCast : lift.{v} c ≤ ℶ_ n ↔ c ≤ ℶ_ n := by
  simpa using lift_le (b := ℶ_ n)

@[simp]
/-
**Cardinal.beth_natCast_lt_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：beth_natCast_lt_lift : ℶ_ n < lift.{v} c ↔ ℶ_ n < c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.lift_beth`：lift_beth (o : Ordinal) : lift.{v} (ℶ_ o) = ℶ_ (Ordi
nal.lift.{v} o)
· 使用定理 `Ordinal.lift_natCast`：∀ (n : ℕ), Ordinal.lift.{u, v} ↑n = ↑n
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
-/
theorem beth_natCast_lt_lift : ℶ_ n < lift.{v} c ↔ ℶ_ n < c := by
  simpa using lift_lt (a := ℶ_ n)

@[simp]
/-
**Cardinal.lift_lt_beth_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_lt_beth_natCast : lift.{v} c < ℶ_ n ↔ c < ℶ_ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.lift_beth`：lift_beth (o : Ordinal) : lift.{v} (ℶ_ o) = ℶ_ (Ordi
nal.lift.{v} o)
· 使用定理 `Ordinal.lift_natCast`：∀ (n : ℕ), Ordinal.lift.{u, v} ↑n = ↑n
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
-/
theorem lift_lt_beth_natCast : lift.{v} c < ℶ_ n ↔ c < ℶ_ n := by
  simpa using lift_lt (b := ℶ_ n)

@[simp]
/-
**Cardinal.beth_natCast_eq_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：beth_natCast_eq_lift : ℶ_ n = lift.{v} c ↔ ℶ_ n = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.lift_beth`：lift_beth (o : Ordinal) : lift.{v} (ℶ_ o) = ℶ_ (Ordi
nal.lift.{v} o)
· 使用定理 `Ordinal.lift_natCast`：∀ (n : ℕ), Ordinal.lift.{u, v} ↑n = ↑n
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
-/
theorem beth_natCast_eq_lift : ℶ_ n = lift.{v} c ↔ ℶ_ n = c := by
  simpa using lift_inj (a := ℶ_ n)

@[simp]
/-
**Cardinal.lift_eq_beth_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_eq_beth_natCast : lift.{v} c = ℶ_ n ↔ c = ℶ_ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm_eq`：eq_comm_eq {α : Sort*} (a b : α) : (a = b) = (b = a)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lift_eq_beth_natCast : lift.{v} c = ℶ_ n ↔ c = ℶ_ n := by
  simp [eqComm]

@[simp]
/-
**Cardinal.beth_ofNat_le_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：beth_ofNat_le_lift [n.AtLeastTwo] : ℶ_ ofNat(n) <= lift.{v} c ↔ ℶ_ ofNat(n
) <= c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.beth_natCast_le_lift`：beth_natCast_le_lift : ℶ_ n <= lift.{v} c
 ↔ ℶ_ n <= c
-/
theorem beth_ofNat_le_lift [n.AtLeastTwo] : ℶ_ ofNat(n) ≤ lift.{v} c ↔ ℶ_ ofNat(n) ≤ c :=
  beth_natCast_le_lift

@[simp]
/-
**Cardinal.lift_le_beth_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_le_beth_ofNat [n.AtLeastTwo] : lift.{v} c <= ℶ_ ofNat(n) ↔ c <= ℶ_ of
Nat(n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.lift_le_beth_natCast`：lift_le_beth_natCast : lift.{v} c <= ℶ_ n
 ↔ c <= ℶ_ n
-/
theorem lift_le_beth_ofNat [n.AtLeastTwo] : lift.{v} c ≤ ℶ_ ofNat(n) ↔ c ≤ ℶ_ ofNat(n) :=
  lift_le_beth_natCast

@[simp]
/-
**Cardinal.beth_ofNat_lt_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：beth_ofNat_lt_lift [n.AtLeastTwo] : ℶ_ ofNat(n) < lift.{v} c ↔ ℶ_ ofNat(n)
 < c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.beth_natCast_lt_lift`：beth_natCast_lt_lift : ℶ_ n < lift.{v} c 
↔ ℶ_ n < c
-/
theorem beth_ofNat_lt_lift [n.AtLeastTwo] : ℶ_ ofNat(n) < lift.{v} c ↔ ℶ_ ofNat(n) < c :=
  beth_natCast_lt_lift

@[simp]
/-
**Cardinal.lift_lt_beth_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_lt_beth_ofNat [n.AtLeastTwo] : lift.{v} c < ℶ_ ofNat(n) ↔ c < ℶ_ ofNa
t(n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.lift_lt_beth_natCast`：lift_lt_beth_natCast : lift.{v} c < ℶ_ n 
↔ c < ℶ_ n
-/
theorem lift_lt_beth_ofNat [n.AtLeastTwo] : lift.{v} c < ℶ_ ofNat(n) ↔ c < ℶ_ ofNat(n) :=
  lift_lt_beth_natCast

@[simp]
/-
**Cardinal.beth_ofNat_eq_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：beth_ofNat_eq_lift [n.AtLeastTwo] : ℶ_ ofNat(n) = lift.{v} c ↔ ℶ_ ofNat(n)
 = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.beth_natCast_eq_lift`：beth_natCast_eq_lift : ℶ_ n = lift.{v} c 
↔ ℶ_ n = c
-/
theorem beth_ofNat_eq_lift [n.AtLeastTwo] : ℶ_ ofNat(n) = lift.{v} c ↔ ℶ_ ofNat(n) = c :=
  beth_natCast_eq_lift

@[simp]
/-
**Cardinal.lift_eq_beth_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_eq_beth_ofNat [n.AtLeastTwo] : lift.{v} c = ℶ_ ofNat(n) ↔ c = ℶ_ ofNa
t(n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.lift_eq_beth_natCast`：lift_eq_beth_natCast : lift.{v} c = ℶ_ n 
↔ c = ℶ_ n
-/
theorem lift_eq_beth_ofNat [n.AtLeastTwo] : lift.{v} c = ℶ_ ofNat(n) ↔ c = ℶ_ ofNat(n) :=
  lift_eq_beth_natCast

end lift
end Cardinal

namespace Ordinal
section lift
variable {o : Ordinal.{u}} {n : ℕ}

@[simp]
/-
**Ordinal.omega_one_le_lift** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：omega_one_le_lift : ω₁ <= lift.{v} o ↔ ω₁ <= o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ordinal.lift_omega`：∀ (o : Ordinal.{u}), Ordinal.lift.{v, u} (Ordinal.om
ega o) = Ordinal.omega (Ordinal.lift.{v, u} o)
· 使用定理 `Ordinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `Ordinal.lift_le`：lift_le {a b : Ordinal} : lift.{u, v} a <= lift.{u, v} 
b ↔ a <= b
-/
theorem omega_one_le_lift : ω₁ ≤ lift.{v} o ↔ ω₁ ≤ o := by
  simpa using lift_le (a := ω₁)

@[simp]
/-
**Ordinal.lift_le_omega_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_le_omega_one : lift.{v} o <= ω₁ ↔ o <= ω₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ordinal.lift_omega`：∀ (o : Ordinal.{u}), Ordinal.lift.{v, u} (Ordinal.om
ega o) = Ordinal.omega (Ordinal.lift.{v, u} o)
· 使用定理 `Ordinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `Ordinal.lift_le`：lift_le {a b : Ordinal} : lift.{u, v} a <= lift.{u, v} 
b ↔ a <= b
-/
theorem lift_le_omega_one : lift.{v} o ≤ ω₁ ↔ o ≤ ω₁ := by
  simpa using lift_le (b := ω₁)

@[simp]
/-
**Ordinal.omega_one_lt_lift** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：omega_one_lt_lift : ω₁ < lift.{v} o ↔ ω₁ < o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ordinal.lift_omega`：∀ (o : Ordinal.{u}), Ordinal.lift.{v, u} (Ordinal.om
ega o) = Ordinal.omega (Ordinal.lift.{v, u} o)
· 使用定理 `Ordinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `Ordinal.lift_lt`：lift_lt {a b : Ordinal} : lift.{u, v} a < lift.{u, v} b
 ↔ a < b
-/
theorem omega_one_lt_lift : ω₁ < lift.{v} o ↔ ω₁ < o := by
  simpa using lift_lt (a := ω₁)

@[simp]
/-
**Ordinal.lift_lt_omega_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_lt_omega_one : lift.{v} o < ω₁ ↔ o < ω₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ordinal.lift_omega`：∀ (o : Ordinal.{u}), Ordinal.lift.{v, u} (Ordinal.om
ega o) = Ordinal.omega (Ordinal.lift.{v, u} o)
· 使用定理 `Ordinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `Ordinal.lift_lt`：lift_lt {a b : Ordinal} : lift.{u, v} a < lift.{u, v} b
 ↔ a < b
-/
theorem lift_lt_omega_one : lift.{v} o < ω₁ ↔ o < ω₁ := by
  simpa using lift_lt (b := ω₁)

@[simp]
/-
**Ordinal.omega_one_eq_lift** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：omega_one_eq_lift : ω₁ = lift.{v} o ↔ ω₁ = o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ordinal.lift_omega`：∀ (o : Ordinal.{u}), Ordinal.lift.{v, u} (Ordinal.om
ega o) = Ordinal.omega (Ordinal.lift.{v, u} o)
· 使用定理 `Ordinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `Ordinal.lift_inj`：lift_inj {a b : Ordinal} : lift.{u, v} a = lift.{u, v}
 b ↔ a = b
-/
theorem omega_one_eq_lift : ω₁ = lift.{v} o ↔ ω₁ = o := by
  simpa using lift_inj (a := ω₁)

@[simp]
/-
**Ordinal.lift_eq_omega_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_eq_omega_one : lift.{v} o = ω₁ ↔ o = ω₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm_eq`：eq_comm_eq {α : Sort*} (a b : α) : (a = b) = (b = a)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lift_eq_omega_one : lift.{v} o = ω₁ ↔ o = ω₁ := by
  simp [eqComm]

@[simp]
/-
**Ordinal.omega_natCast_le_lift** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：omega_natCast_le_lift : ω_ n <= lift.{v} o ↔ ω_ n <= o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ordinal.lift_omega`：∀ (o : Ordinal.{u}), Ordinal.lift.{v, u} (Ordinal.om
ega o) = Ordinal.omega (Ordinal.lift.{v, u} o)
· 使用定理 `Ordinal.lift_natCast`：∀ (n : ℕ), Ordinal.lift.{u, v} ↑n = ↑n
· 使用定理 `Ordinal.lift_le`：lift_le {a b : Ordinal} : lift.{u, v} a <= lift.{u, v} 
b ↔ a <= b
-/
theorem omega_natCast_le_lift : ω_ n ≤ lift.{v} o ↔ ω_ n ≤ o := by
  simpa using lift_le (a := ω_ n)

@[simp]
/-
**Ordinal.lift_le_omega_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_le_omega_natCast : lift.{v} o <= ω_ n ↔ o <= ω_ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ordinal.lift_omega`：∀ (o : Ordinal.{u}), Ordinal.lift.{v, u} (Ordinal.om
ega o) = Ordinal.omega (Ordinal.lift.{v, u} o)
· 使用定理 `Ordinal.lift_natCast`：∀ (n : ℕ), Ordinal.lift.{u, v} ↑n = ↑n
· 使用定理 `Ordinal.lift_le`：lift_le {a b : Ordinal} : lift.{u, v} a <= lift.{u, v} 
b ↔ a <= b
-/
theorem lift_le_omega_natCast : lift.{v} o ≤ ω_ n ↔ o ≤ ω_ n := by
  simpa using lift_le (b := ω_ n)

@[simp]
/-
**Ordinal.omega_natCast_lt_lift** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：omega_natCast_lt_lift : ω_ n < lift.{v} o ↔ ω_ n < o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ordinal.lift_omega`：∀ (o : Ordinal.{u}), Ordinal.lift.{v, u} (Ordinal.om
ega o) = Ordinal.omega (Ordinal.lift.{v, u} o)
· 使用定理 `Ordinal.lift_natCast`：∀ (n : ℕ), Ordinal.lift.{u, v} ↑n = ↑n
· 使用定理 `Ordinal.lift_lt`：lift_lt {a b : Ordinal} : lift.{u, v} a < lift.{u, v} b
 ↔ a < b
-/
theorem omega_natCast_lt_lift : ω_ n < lift.{v} o ↔ ω_ n < o := by
  simpa using lift_lt (a := ω_ n)

@[simp]
/-
**Ordinal.lift_lt_omega_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_lt_omega_natCast : lift.{v} o < ω_ n ↔ o < ω_ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ordinal.lift_omega`：∀ (o : Ordinal.{u}), Ordinal.lift.{v, u} (Ordinal.om
ega o) = Ordinal.omega (Ordinal.lift.{v, u} o)
· 使用定理 `Ordinal.lift_natCast`：∀ (n : ℕ), Ordinal.lift.{u, v} ↑n = ↑n
· 使用定理 `Ordinal.lift_lt`：lift_lt {a b : Ordinal} : lift.{u, v} a < lift.{u, v} b
 ↔ a < b
-/
theorem lift_lt_omega_natCast : lift.{v} o < ω_ n ↔ o < ω_ n := by
  simpa using lift_lt (b := ω_ n)

@[simp]
/-
**Ordinal.omega_natCast_eq_lift** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：omega_natCast_eq_lift : ω_ n = lift.{v} o ↔ ω_ n = o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ordinal.lift_omega`：∀ (o : Ordinal.{u}), Ordinal.lift.{v, u} (Ordinal.om
ega o) = Ordinal.omega (Ordinal.lift.{v, u} o)
· 使用定理 `Ordinal.lift_natCast`：∀ (n : ℕ), Ordinal.lift.{u, v} ↑n = ↑n
· 使用定理 `Ordinal.lift_inj`：lift_inj {a b : Ordinal} : lift.{u, v} a = lift.{u, v}
 b ↔ a = b
-/
theorem omega_natCast_eq_lift : ω_ n = lift.{v} o ↔ ω_ n = o := by
  simpa using lift_inj (a := ω_ n)

@[simp]
/-
**Ordinal.lift_eq_omega_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_eq_omega_natCast : lift.{v} o = ω_ n ↔ o = ω_ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm_eq`：eq_comm_eq {α : Sort*} (a b : α) : (a = b) = (b = a)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lift_eq_omega_natCast : lift.{v} o = ω_ n ↔ o = ω_ n := by
  simp [eqComm]

@[simp]
/-
**Ordinal.omega_ofNat_le_lift** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：omega_ofNat_le_lift [n.AtLeastTwo] : ω_ ofNat(n) <= lift.{v} o ↔ ω_ ofNat(
n) <= o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.omega_natCast_le_lift`：omega_natCast_le_lift : ω_ n <= lift.{v} 
o ↔ ω_ n <= o
-/
theorem omega_ofNat_le_lift [n.AtLeastTwo] : ω_ ofNat(n) ≤ lift.{v} o ↔ ω_ ofNat(n) ≤ o :=
  omega_natCast_le_lift

@[simp]
/-
**Ordinal.lift_le_omega_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_le_omega_ofNat [n.AtLeastTwo] : lift.{v} o <= ω_ ofNat(n) ↔ o <= ω_ o
fNat(n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.lift_le_omega_natCast`：lift_le_omega_natCast : lift.{v} o <= ω_ 
n ↔ o <= ω_ n
-/
theorem lift_le_omega_ofNat [n.AtLeastTwo] : lift.{v} o ≤ ω_ ofNat(n) ↔ o ≤ ω_ ofNat(n) :=
  lift_le_omega_natCast

@[simp]
/-
**Ordinal.omega_ofNat_lt_lift** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：omega_ofNat_lt_lift [n.AtLeastTwo] : ω_ ofNat(n) < lift.{v} o ↔ ω_ ofNat(n
) < o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.omega_natCast_lt_lift`：omega_natCast_lt_lift : ω_ n < lift.{v} o
 ↔ ω_ n < o
-/
theorem omega_ofNat_lt_lift [n.AtLeastTwo] : ω_ ofNat(n) < lift.{v} o ↔ ω_ ofNat(n) < o :=
  omega_natCast_lt_lift

@[simp]
/-
**Ordinal.lift_lt_omega_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_lt_omega_ofNat [n.AtLeastTwo] : lift.{v} o < ω_ ofNat(n) ↔ o < ω_ ofN
at(n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.lift_lt_omega_natCast`：lift_lt_omega_natCast : lift.{v} o < ω_ n
 ↔ o < ω_ n
-/
theorem lift_lt_omega_ofNat [n.AtLeastTwo] : lift.{v} o < ω_ ofNat(n) ↔ o < ω_ ofNat(n) :=
  lift_lt_omega_natCast

@[simp]
/-
**Ordinal.omega_ofNat_eq_lift** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：omega_ofNat_eq_lift [n.AtLeastTwo] : ω_ ofNat(n) = lift.{v} o ↔ ω_ ofNat(n
) = o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.omega_natCast_eq_lift`：omega_natCast_eq_lift : ω_ n = lift.{v} o
 ↔ ω_ n = o
-/
theorem omega_ofNat_eq_lift [n.AtLeastTwo] : ω_ ofNat(n) = lift.{v} o ↔ ω_ ofNat(n) = o :=
  omega_natCast_eq_lift

@[simp]
/-
**Ordinal.lift_eq_omega_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_eq_omega_ofNat [n.AtLeastTwo] : lift.{v} o = ω_ ofNat(n) ↔ o = ω_ ofN
at(n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.lift_eq_omega_natCast`：lift_eq_omega_natCast : lift.{v} o = ω_ n
 ↔ o = ω_ n
-/
theorem lift_eq_omega_ofNat [n.AtLeastTwo] : lift.{v} o = ω_ ofNat(n) ↔ o = ω_ ofNat(n) :=
  lift_eq_omega_natCast

end lift
end Ordinal

