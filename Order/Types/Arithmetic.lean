/-
Copyright (c) 2025 Yan Yablonovskiy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yan Yablonovskiy
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Types.Defs
public import Mathlib.SetTheory.Cardinal.Order

/-!

## Main definitions

* `OrderType.card o`: the cardinality of an OrderType `o`.
* `o₁ + o₂`: the lexicographic sum of order types, which forms an `AddMonoid`.
* `o₁ * o₂`: the lexicographic product of order types, which forms a `MonoidWithZero`.

## Notation

The following are notations in the `OrderType` namespace:

* `η` is a notation for the order type of `ℚ` with its natural order.
* `θ` is a notation for the order type of `ℝ` with its natural order.

## References

* <https://en.wikipedia.org/wiki/Order_type>
* [Dauben, J. W., Georg Cantor: His Mathematics and Philosophy of the Infinite. Princeton,
  NJ: Princeton University Press, 1990.][dauben_1990]
* [Enderton, Herbert B., Elements of Set Theory. United Kingdom: Academic Press,
  1977.][enderton_1977]

## Tags

order type, order isomorphism, linear order
-/

public noncomputable section

namespace OrderType

universe u v

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ZeroLEOneClass OrderType
  body: ⟨OrderType.zero_le _⟩

中文:
实例 :
  签名: ZeroLEOne类 序型
  定义体: ⟨OrderType.zero_le _⟩

Depends on / 依赖: OrderType, OrderType.zero_le, zero_le
-/
instance : ZeroLEOneClass OrderType :=
  ⟨OrderType.zero_le _⟩

instance (priority := low) : HAdd OrderType.{u} OrderType.{v} OrderType.{max u v} where
  hAdd o₁ o₂ := OrderType.liftOn₂ o₁ o₂ (fun r _ s _ => type (r oplusₗ s))
    fun _ _ _ _ _ _ _ _ ha hb => OrderIso.sumLexCongr (Classical.choice <| type_eq_type.mp ha)
type_congr (Classical.choice <| type_eq_type.mp hb)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add OrderType.{u}
  body: o₁ + o₂

@[simp]

中文:
实例 :
  签名: 加法 序型.{u}
  定义体: o₁ + o₂

@[simp]
-/
instance : Add OrderType.{u} where
  add o₁ o₂ := o₁ + o₂

@[simp]
/--
lemma `type_lex_sum` / 引理 `type_lex_sum`

English:
lemma type_lex_sum
  given: (α : Type u) (β : Type v) [LinearOrder α] [LinearOrder β]
  proof: by simp [HAdd.hAdd]

中文:
引理 type_lex_sum
  条件: (α : 类型u) (β : 类型v) [线性序 α] [线性序 β]
  证明: by simp [HAdd.hAdd]

Depends on / 依赖: HAdd.hAdd
-/
lemma type_lex_sum (α : Type u) (β : Type v) [LinearOrder α] [LinearOrder β] :
    type (α oplusₗ β) = type α + type β := by simp [HAdd.hAdd]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddMonoid OrderType.{u}
  body: inductionOn₃ o₁ o₂ o₃ fun α _ β _ γ _ => by
      simp only [← type_lex_sum, (OrderIso.sumLexAssoc α β γ).type_congr]
  zero_add o :=
    inductionOn o (fun α _ => by
      simp only [show 0 = type PEmpty by rfl, ← type_lex_sum]
      exact (OrderIso.emptySumLex (β := PEmpty) (α := α)).type_congr)
 

中文:
实例 :
  签名: 加法幺半群 序型.{u}
  定义体: inductionOn₃ o₁ o₂ o₃ fun α _ β _ γ _ => by
      simp only [← type_lex_sum, (OrderIso.sumLexAssoc α β γ).type_congr]
  zero_add o :=
    inductionOn o (fun α _ => by
      simp only [show 0 = type PEmpty by rfl, ← type_lex_sum]
      exact (OrderIso.emptySumLex (β := PEmpty) (α := α)).type_congr)
 

Depends on / 依赖: OrderIso, OrderIso.emptySumLex, OrderIso.sumLexAssoc, OrderIso.sumLexEmpty, PEmpty, add_zero, emptySumLex, inductionOn, nsmulRec, sumLexAssoc, sumLexEmpty, type_congr, type_lex_sum, zero_add
-/
instance : AddMonoid OrderType.{u} where
  add_assoc o₁ o₂ o₃ :=
    inductionOn₃ o₁ o₂ o₃ fun α _ β _ γ _ => by
      simp only [← type_lex_sum, (OrderIso.sumLexAssoc α β γ).type_congr]
  zero_add o :=
    inductionOn o (fun α _ => by
      simp only [show 0 = type PEmpty by rfl, ← type_lex_sum]
      exact (OrderIso.emptySumLex (β := PEmpty) (α := α)).type_congr)
  add_zero o :=
    inductionOn o (fun α _ => by
      simp only [show 0 = type PEmpty by rfl, ← type_lex_sum]
      exact (OrderIso.sumLexEmpty (β := PEmpty) (α := α)).type_congr)
  nsmul := nsmulRec

instance (priority := low) : HMul OrderType.{u} OrderType.{v} OrderType.{max u v} where
  hMul o₁ o₂ := OrderType.liftOn₂ o₁ o₂ (fun r _ s _ => type (s ×ₗ r))
    fun _ _ _ _ _ _ _ _ ha hb => Prod.Lex.prodLexCongr (Classical.choice <| type_eq_type.mp hb)
type_congr (Classical.choice <| type_eq_type.mp ha)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul OrderType.{u}
  body: o₁ * o₂

@[simp]

中文:
实例 :
  签名: 乘法 序型.{u}
  定义体: o₁ * o₂

@[simp]
-/
instance : Mul OrderType.{u} where
  mul o₁ o₂ := o₁ * o₂

@[simp]
/--
lemma `type_lex_prod` / 引理 `type_lex_prod`

English:
lemma type_lex_prod
  given: (α : Type u) (β : Type v) [LinearOrder α] [LinearOrder β]
  proof: by simp [HMul.hMul]

中文:
引理 type_lex_prod
  条件: (α : 类型u) (β : 类型v) [线性序 α] [线性序 β]
  证明: by simp [HMul.hMul]

Depends on / 依赖: HMul.hMul
-/
lemma type_lex_prod (α : Type u) (β : Type v) [LinearOrder α] [LinearOrder β] :
    type (α ×ₗ β) = type β * type α := by simp [HMul.hMul]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monoid OrderType.{u}
  body: inductionOn₃ o₁ o₂ o₃ fun α _ β _ γ _ => by
      simp only [← type_lex_prod]
      exact (Prod.Lex.prodLexAssoc γ β α).symm.type_congr
  one_mul o :=
    inductionOn o (fun α _ => by
      simp only [show 1 = type PUnit by rfl, ← type_lex_prod]
      exact (Prod.Lex.prodUnique α PUnit).type_congr)


中文:
实例 :
  签名: 幺半群 序型.{u}
  定义体: inductionOn₃ o₁ o₂ o₃ fun α _ β _ γ _ => by
      simp only [← type_lex_prod]
      exact (Prod.Lex.prodLexAssoc γ β α).symm.type_congr
  one_mul o :=
    inductionOn o (fun α _ => by
      simp only [show 1 = type PUnit by rfl, ← type_lex_prod]
      exact (Prod.Lex.prodUnique α PUnit).type_congr)


Depends on / 依赖: Prod.Lex.prodLexAssoc, Prod.Lex.prodUnique, Prod.Lex.uniqueProd, inductionOn, mul_one, one_mul, prodLexAssoc, prodUnique, symm.type_congr, type_congr, type_lex_prod, uniqueProd
-/
instance : Monoid OrderType.{u} where
  mul_assoc o₁ o₂ o₃ :=
    inductionOn₃ o₁ o₂ o₃ fun α _ β _ γ _ => by
      simp only [← type_lex_prod]
      exact (Prod.Lex.prodLexAssoc γ β α).symm.type_congr
  one_mul o :=
    inductionOn o (fun α _ => by
      simp only [show 1 = type PUnit by rfl, ← type_lex_prod]
      exact (Prod.Lex.prodUnique α PUnit).type_congr)
  mul_one o :=
    inductionOn o (fun α _ => by
      simp only [show 1 = type PUnit by rfl, ← type_lex_prod]
      exact (Prod.Lex.uniqueProd PUnit α).type_congr)

section Cardinal

open Cardinal

/--
Definition of `card` / `card` 的定义

English:
definition card
  signature: (o : OrderType)
  body: o.liftOn (fun α _ => #α)
    fun _ _ _ _ hab => mk_congr (type_eq_type.mp hab).some.toEquiv

@[simp]

中文:
定义 card
  签名: (o : 序型)
  定义体: o.liftOn (fun α _ => #α)
    fun _ _ _ _ hab => mk_congr (type_eq_type.mp hab).some.toEquiv

@[simp]

Depends on / 依赖: liftOn, mk_congr, o.liftOn, some.toEquiv, toEquiv, type_eq_type, type_eq_type.mp
-/
def card (o : OrderType) : Cardinal :=
  o.liftOn (fun α _ => #α)
    fun _ _ _ _ hab => mk_congr (type_eq_type.mp hab).some.toEquiv

@[simp]
/--
theorem `card_type` / 定理 `card_type`

English:
theorem card_type
  given: {α : Type u} [LinearOrder α]
  statement: card (type α) = #α
  proof: by
  rw [card]; rw [liftOn_type]

@[gcongr]

中文:
定理 card_type
  条件: {α : 类型u} [线性序 α]
  结论: card (type α) = #α
  证明: by
  rw [card]; rw [liftOn_type]

@[gcongr]

Depends on / 依赖: liftOn_type
-/
theorem card_type {α : Type u} [LinearOrder α] : card (type α) = #α := by
  rw [card]; rw [liftOn_type]

@[gcongr]
/--
theorem `card_mono` / 定理 `card_mono`

English:
theorem card_mono
  given: {o₁ o₂ : OrderType}
  statement: o₁ <= o₂ -> card o₁ <= card o₂
  proof: inductionOn₂ o₁ o₂ fun _ _ _ _ hle => by
    simp [card, (type_le_type_iff.mp hle).some.cardinal_le]

中文:
定理 card_mono
  条件: {o₁ o₂ : 序型}
  结论: o₁ <= o₂ -> card o₁ <= card o₂
  证明: inductionOn₂ o₁ o₂ fun _ _ _ _ hle => by
    simp [card, (type_le_type_iff.mp hle).some.cardinal_le]

Depends on / 依赖: cardinal_le, some.cardinal_le, type_le_type_iff, type_le_type_iff.mp
-/
theorem card_mono {o₁ o₂ : OrderType} : o₁ <= o₂ -> card o₁ <= card o₂ :=
  inductionOn₂ o₁ o₂ fun _ _ _ _ hle => by
    simp [card, (type_le_type_iff.mp hle).some.cardinal_le]

/--
theorem `card_monotone` / 定理 `card_monotone`

English:
theorem card_monotone
  statement: Monotone card
  proof: @card_mono

中文:
定理 card_monotone
  结论: 递增 card
  证明: @card_mono

Depends on / 依赖: card_mono
-/
theorem card_monotone : Monotone card := @card_mono

/--
theorem `card_zero` / 定理 `card_zero`

English:
theorem card_zero
  statement: card 0 = 0
  proof: by simpa using card_type (α := PEmpty)

中文:
定理 card_zero
  结论: card 0 = 0
  证明: by simpa using card_type (α := PEmpty)
-/
@[simp] theorem card_zero : card 0 = 0 := by simpa using card_type (α := PEmpty)

/--
theorem `card_one` / 定理 `card_one`

English:
theorem card_one
  statement: card 1 = 1
  proof: by simpa using card_type (α := PUnit)

中文:
定理 card_one
  结论: card 1 = 1
  证明: by simpa using card_type (α := PUnit)
-/
@[simp] theorem card_one : card 1 = 1 := by simpa using card_type (α := PUnit)

end Cardinal

instance (n : Nat) : OfNat OrderType n where
type ofNat := Fin n

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LeftDistribClass OrderType
  body: by
    refine inductionOn₃ a b c (fun _ _ _ _ _ _ => ?_)
    simp only [← type_lex_prod, ← type_lex_sum]
    exact (Prod.Lex.sumLexProdLexDistrib _ _ _).type_congr

中文:
实例 :
  签名: LeftDistrib类 序型
  定义体: by
    refine inductionOn₃ a b c (fun _ _ _ _ _ _ => ?_)
    simp only [← type_lex_prod, ← type_lex_sum]
    exact (Prod.Lex.sumLexProdLexDistrib _ _ _).type_congr

Depends on / 依赖: Prod.Lex.sumLexProdLexDistrib, sumLexProdLexDistrib, type_congr, type_lex_prod, type_lex_sum
-/
instance : LeftDistribClass OrderType where
  left_distrib a b c := by
    refine inductionOn₃ a b c (fun _ _ _ _ _ _ => ?_)
    simp only [← type_lex_prod, ← type_lex_sum]
    exact (Prod.Lex.sumLexProdLexDistrib _ _ _).type_congr

/--
Definition of `eta` / `eta` 的定义

English:
definition eta
  signature: : OrderType
  body: type Rat

中文:
定义 eta
  签名: : 序型
  定义体: type Rat
-/
def eta : OrderType := type Rat

/--
Definition of `theta` / `theta` 的定义

English:
definition theta
  signature: : OrderType
  body: type Real

@[inherit_doc]
scoped notation "η" => OrderType.eta
recommended_spelling "eta" for "η" in [eta, «termη»]

@[inherit_doc]
scoped notation "θ" => OrderType.theta
recommended_spelling "theta" for "θ" in [theta, «termθ»]

中文:
定义 theta
  签名: : 序型
  定义体: type Real

@[inherit_doc]
scoped notation "η" => OrderType.eta
recommended_spelling "eta" for "η" in [eta, «termη»]

@[inherit_doc]
scoped notation "θ" => OrderType.theta
recommended_spelling "theta" for "θ" in [theta, «termθ»]
-/
def theta : OrderType := type Real

@[inherit_doc]
scoped notation "η" => OrderType.eta
recommended_spelling "eta" for "η" in [eta, «termη»]

@[inherit_doc]
scoped notation "θ" => OrderType.theta
recommended_spelling "theta" for "θ" in [theta, «termθ»]

end OrderType
