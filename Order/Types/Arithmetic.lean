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

/-
**OrderType.** 是 Mathlib 中的一个实例，位于命名空间 `OrderType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ZeroLEOneClass OrderType :=
  ⟨OrderType.zero_le _⟩
/-
**OrderType.** 是 Mathlib 中的一个实例，位于命名空间 `OrderType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) : HAdd OrderType.{u} OrderType.{v} OrderType.{max u v} where
  hAdd o₁ o₂ := OrderType.liftOn₂ o₁ o₂ (fun r _ s _ ↦ type (r ⊕ₗ s))
    fun _ _ _ _ _ _ _ _ ha hb ↦ OrderIso.sumLexCongr (Classical.choice <| type_eq_type.mp ha)
      (Classical.choice <| type_eq_type.mp hb) |> type_congr
/-
**OrderType.** 是 Mathlib 中的一个实例，位于命名空间 `OrderType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add OrderType.{u} where
  add o₁ o₂ := o₁ + o₂

@[simp]
/-
**OrderType.type_lex_sum** 是 Mathlib 中的一个引理，位于命名空间 `OrderType`。
形式化陈述：type_lex_sum (α : Type u) (β : Type v) [LinearOrder α] [LinearOrder β] : t
ype (α oplusₗ β) = type α + type β
参数：α : Type u；β : Type v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderType.liftOn₂_type`：liftOn₂_type {α : Type u} {β : Type v} {δ : Type
*} [LinearOrder α] [LinearOrder β] (f : forall (α) [LinearOrder α] (β) [LinearOr
der β], δ) (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma type_lex_sum (α : Type u) (β : Type v) [LinearOrder α] [LinearOrder β] :
    type (α ⊕ₗ β) = type α + type β := by simp [HAdd.hAdd]
/-
**OrderType.** 是 Mathlib 中的一个实例，位于命名空间 `OrderType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddMonoid OrderType.{u} where
  add_assoc o₁ o₂ o₃ :=
    inductionOn₃ o₁ o₂ o₃ fun α _ β _ γ _ ↦ by
      simp only [← type_lex_sum, (OrderIso.sumLexAssoc α β γ).type_congr]
  zero_add o :=
    inductionOn o (fun α _ ↦ by
      simp only [show 0 = type PEmpty by rfl, ← type_lex_sum]
      exact (OrderIso.emptySumLex (β := PEmpty) (α := α)).type_congr)
  add_zero o :=
    inductionOn o (fun α _ ↦ by
      simp only [show 0 = type PEmpty by rfl, ← type_lex_sum]
      exact (OrderIso.sumLexEmpty (β := PEmpty) (α := α)).type_congr)
  nsmul := nsmulRec
/-
**OrderType.** 是 Mathlib 中的一个实例，位于命名空间 `OrderType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) : HMul OrderType.{u} OrderType.{v} OrderType.{max u v} where
  hMul o₁ o₂ := OrderType.liftOn₂ o₁ o₂ (fun r _ s _ ↦ type (s ×ₗ r))
    fun _ _ _ _ _ _ _ _ ha hb ↦ Prod.Lex.prodLexCongr (Classical.choice <| type_eq_type.mp hb)
      (Classical.choice <| type_eq_type.mp ha) |> type_congr
/-
**OrderType.** 是 Mathlib 中的一个实例，位于命名空间 `OrderType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul OrderType.{u} where
  mul o₁ o₂ := o₁ * o₂

@[simp]
/-
**OrderType.type_lex_prod** 是 Mathlib 中的一个引理，位于命名空间 `OrderType`。
形式化陈述：type_lex_prod (α : Type u) (β : Type v) [LinearOrder α] [LinearOrder β] : 
type (α ×ₗ β) = type β * type α
参数：α : Type u；β : Type v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderType.liftOn₂_type`：liftOn₂_type {α : Type u} {β : Type v} {δ : Type
*} [LinearOrder α] [LinearOrder β] (f : forall (α) [LinearOrder α] (β) [LinearOr
der β], δ) (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma type_lex_prod (α : Type u) (β : Type v) [LinearOrder α] [LinearOrder β] :
    type (α ×ₗ β) = type β * type α := by simp [HMul.hMul]
/-
**OrderType.** 是 Mathlib 中的一个实例，位于命名空间 `OrderType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monoid OrderType.{u} where
  mul_assoc o₁ o₂ o₃ :=
    inductionOn₃ o₁ o₂ o₃ fun α _ β _ γ _ ↦ by
      simp only [← type_lex_prod]
      exact (Prod.Lex.prodLexAssoc γ β α).symm.type_congr
  one_mul o :=
    inductionOn o (fun α _ ↦ by
      simp only [show 1 = type PUnit by rfl, ← type_lex_prod]
      exact (Prod.Lex.prodUnique α PUnit).type_congr)
  mul_one o :=
    inductionOn o (fun α _ ↦ by
      simp only [show 1 = type PUnit by rfl, ← type_lex_prod]
      exact (Prod.Lex.uniqueProd PUnit α).type_congr)

section Cardinal

open Cardinal

/-- The cardinal of an `OrderType` is the cardinality of any type on which a relation
with that order type is defined. -/
/-
**OrderType.card** 是 Mathlib 中的一个定义，位于命名空间 `OrderType`。
形式化陈述：card (o : OrderType) : Cardinal
参数：o : OrderType。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cardinal of an `OrderType` is the cardinality of any type on which a relatio
n
with that order type is defined.
-/
def card (o : OrderType) : Cardinal :=
  o.liftOn (fun α _ ↦ #α)
    fun _ _ _ _ hab ↦ mk_congr (type_eq_type.mp hab).some.toEquiv

@[simp]
/-
**OrderType.card_type** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：card_type {α : Type u} [LinearOrder α] : card (type α) = #α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Order.Types.Arithmetic.0.OrderType.card.eq_1`：∀ (o : Or
derType.{u_1}), o.card = o.liftOn (fun α x => Cardinal.mk α) OrderType.card._pro
of_1✝
· 使用定理 `OrderType.liftOn_type`：liftOn_type (f : forall (α) [LinearOrder α], δ) (
c : forall (α) [LinearOrder α] (β) [LinearOrder β], type α = type β -> f α = f β
) {γ} [Line…
-/
theorem card_type {α : Type u} [LinearOrder α] : card (type α) = #α := by
  rw [card, liftOn_type]

@[gcongr]
/-
**OrderType.card_mono** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：card_mono {o₁ o₂ : OrderType} : o₁ <= o₂ -> card o₁ <= card o₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderType.inductionOn₂`：inductionOn₂ {C : OrderType -> OrderType -> Prop
} (o₁ o₂ : OrderType) (H : forall α [LinearOrder α] β [LinearOrder β], C (type α
) (type β)) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderType.liftOn_type`：liftOn_type (f : forall (α) [LinearOrder α], δ) (
c : forall (α) [LinearOrder α] (β) [LinearOrder β], type α = type β -> f α = f β
) {γ} [Line…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Function.Embedding.cardinal_le`：∀ {α β : Type u} (f : α ↪ β), Cardinal.m
k α ≤ Cardinal.mk β
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `OrderType.type_le_type_iff`：type_le_type_iff : type α <= type β ↔ Nonemp
ty (α ↪o β)
-/
theorem card_mono {o₁ o₂ : OrderType} : o₁ ≤ o₂ → card o₁ ≤ card o₂ :=
  inductionOn₂ o₁ o₂ fun _ _ _ _ hle ↦ by
    simp [card, (type_le_type_iff.mp hle).some.cardinal_le]
/-
**OrderType.card_monotone** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：card_monotone : Monotone card
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderType.card_mono`：card_mono {o₁ o₂ : OrderType} : o₁ <= o₂ -> card o₁
 <= card o₂
-/
theorem card_monotone : Monotone card := @card_mono
/-
**OrderType.card_zero** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：OrderType.card 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderType.type_of_isEmpty`：type_of_isEmpty [IsEmpty α] : type α = 0
· 使用定理 `Cardinal.mk_eq_zero`：mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0
· 使用定理 `OrderType.card_type`：card_type {α : Type u} [LinearOrder α] : card (type
 α) = #α
-/
@[simp] theorem card_zero : card 0 = 0 := by simpa using card_type (α := PEmpty)
/-
**OrderType.card_one** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：OrderType.card 1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderType.type_of_unique`：type_of_unique [Nonempty α] [Subsingleton α] :
 type α = 1
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `OrderType.card_type`：card_type {α : Type u} [LinearOrder α] : card (type
 α) = #α
-/
@[simp] theorem card_one : card 1 = 1 := by simpa using card_type (α := PUnit)

end Cardinal

/-
**OrderType.** 是 Mathlib 中的一个实例，位于命名空间 `OrderType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : Nat) : OfNat OrderType n where
  ofNat := Fin n |> type
/-
**OrderType.** 是 Mathlib 中的一个实例，位于命名空间 `OrderType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LeftDistribClass OrderType where
  left_distrib a b c := by
    refine inductionOn₃ a b c (fun _ _ _ _ _ _ ↦ ?_)
    simp only [← type_lex_prod, ← type_lex_sum]
    exact (Prod.Lex.sumLexProdLexDistrib _ _ _).type_congr

/-- The order type of the rational numbers. -/
/-
**OrderType.eta** 是 Mathlib 中的一个定义，位于命名空间 `OrderType`。
形式化陈述：eta : OrderType
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order type of the rational numbers.
-/
def eta : OrderType := type ℚ

/-- The order type of the real numbers. -/
/-
**OrderType.theta** 是 Mathlib 中的一个定义，位于命名空间 `OrderType`。
形式化陈述：theta : OrderType
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order type of the real numbers.
-/
def theta : OrderType := type ℝ

@[inherit_doc]
scoped notation "η" => OrderType.eta
recommended_spelling "eta" for "η" in [eta, «termη»]

@[inherit_doc]
scoped notation "θ" => OrderType.theta
recommended_spelling "theta" for "θ" in [theta, «termθ»]

end OrderType

