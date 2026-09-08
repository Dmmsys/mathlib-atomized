/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Order.Hom.Lattice

/-!
# Adding complements to a generalized Boolean algebra

This file embeds any generalized Boolean algebra into a Boolean algebra.

This concretely proves that any equation holding true in the theory of Boolean algebras that does
not reference `ᶜ` also holds true in the theory of generalized Boolean algebras. Put another way,
one does not need the existence of complements to prove something which does not talk about
complements.

## Main declarations

* `Booleanisation`: Boolean algebra containing a given generalised Boolean algebra as a sublattice.
* `Booleanisation.liftLatticeHom`: Boolean algebra containing a given generalised Boolean algebra as
  a sublattice.

## Future work

If mathlib ever acquires `GenBoolAlg`, the category of generalised Boolean algebras, then one could
show that `Booleanisation` is the free functor from `GenBoolAlg` to `BoolAlg`.
-/

@[expose] public section

open Function

variable {α : Type*}

/-- Boolean algebra containing a given generalised Boolean algebra `α` as a sublattice.

This should be thought of as made of a copy of `α` (representing elements of `α`) living under
another copy of `α` (representing complements of elements of `α`). -/
/-
**Booleanisation** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Booleanisation (α : Type*)
参数：α : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Boolean algebra containing a given generalised Boolean algebra `α` as a sublatti
ce.

This should be thought of as made of a copy of `α` (representing elements of `α`
) living under
another copy of `α` (representing complements of elements of `α`).
-/
def Booleanisation (α : Type*) := α ⊕ α

namespace Booleanisation

/-
**Booleanisation.instDecidableEq** 是 Mathlib 中的一个实例，位于命名空间 `Booleanisation`。
形式化陈述：instDecidableEq [DecidableEq α] : DecidableEq (Booleanisation α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDecidableEq [DecidableEq α] : DecidableEq (Booleanisation α) :=
  inferInstanceAs <| DecidableEq (α ⊕ α)

/-- The natural inclusion `a ↦ a` from a generalized Boolean algebra to its generated Boolean
algebra. -/
/-
**Booleanisation.lift** 是 Mathlib 中的一个定义，位于命名空间 `Booleanisation`。
形式化陈述：{α : Type u_1} → α → Booleanisation α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural inclusion `a ↦ a` from a generalized Boolean algebra to its generate
d Boolean
algebra.
-/
@[match_pattern] def lift : α → Booleanisation α := Sum.inl

/-- The inclusion `a ↦ aᶜ` from a generalized Boolean algebra to its generated Boolean algebra. -/
/-
**Booleanisation.comp** 是 Mathlib 中的一个定义，位于命名空间 `Booleanisation`。
形式化陈述：{α : Type u_1} → α → Booleanisation α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `a ↦ aᶜ` from a generalized Boolean algebra to its generated Boole
an algebra.
-/
@[match_pattern] def comp : α → Booleanisation α := Sum.inr

/-- The complement operator on `Booleanisation α` sends `a` to `aᶜ` and `aᶜ` to `a`, for `a : α`. -/
/-
**Booleanisation.instCompl** 是 Mathlib 中的一个定义，位于命名空间 `Booleanisation`。
形式化陈述：{α : Type u_1} → Compl (Booleanisation α)
参数：Booleanisation α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The complement operator on `Booleanisation α` sends `a` to `aᶜ` and `aᶜ` to `a`,
 for `a : α`.
-/
instance instCompl : Compl (Booleanisation α) where
  compl
    | lift a => comp a
    | comp a => lift a
/-
**Booleanisation.compl_lift** 是 Mathlib 中的一个定理，位于命名空间 `Booleanisation`。
形式化陈述：∀ {α : Type u_1} (a : α), (Booleanisation.lift a)ᶜ = Booleanisation.comp a
参数：a : α；Booleanisation.lift a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma compl_lift (a : α) : (lift a)ᶜ = comp a := rfl
/-
**Booleanisation.compl_comp** 是 Mathlib 中的一个定理，位于命名空间 `Booleanisation`。
形式化陈述：∀ {α : Type u_1} (a : α), (Booleanisation.comp a)ᶜ = Booleanisation.lift a
参数：a : α；Booleanisation.comp a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma compl_comp (a : α) : (comp a)ᶜ = lift a := rfl

variable [GeneralizedBooleanAlgebra α]

/-- The order on `Booleanisation α` is as follows: For `a b : α`,
* `a ≤ b` iff `a ≤ b` in `α`
* `a ≤ bᶜ` iff `a` and `b` are disjoint in `α`
* `aᶜ ≤ bᶜ` iff `b ≤ a` in `α`
* `¬ aᶜ ≤ b` -/
/-
**Booleanisation.LE** 是 Mathlib 中的一个归纳类型，位于命名空间 `Booleanisation`。
形式化陈述：{α : Type u_1} → [GeneralizedBooleanAlgebra α] → Booleanisation α → Boolea
nisation α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order on `Booleanisation α` is as follows: For `a b : α`,
* `a ≤ b` iff `a ≤ b` in `α`
* `a ≤ bᶜ` iff `a` and `b` are disjoint in `α`
* `aᶜ ≤ bᶜ` iff `b ≤ a` in `α`
* `¬ aᶜ ≤ b`
-/
protected inductive LE : Booleanisation α → Booleanisation α → Prop
  | protected lift {a b} : a ≤ b → Booleanisation.LE (lift a) (lift b)
  | protected comp {a b} : a ≤ b → Booleanisation.LE (comp b) (comp a)
  | protected sep {a b} : Disjoint a b → Booleanisation.LE (lift a) (comp b)

/-- The order on `Booleanisation α` is as follows: For `a b : α`,
* `a < b` iff `a < b` in `α`
* `a < bᶜ` iff `a` and `b` are disjoint in `α`
* `aᶜ < bᶜ` iff `b < a` in `α`
* `¬ aᶜ < b` -/
/-
**Booleanisation.LT** 是 Mathlib 中的一个归纳类型，位于命名空间 `Booleanisation`。
形式化陈述：{α : Type u_1} → [GeneralizedBooleanAlgebra α] → Booleanisation α → Boolea
nisation α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order on `Booleanisation α` is as follows: For `a b : α`,
* `a < b` iff `a < b` in `α`
* `a < bᶜ` iff `a` and `b` are disjoint in `α`
* `aᶜ < bᶜ` iff `b < a` in `α`
* `¬ aᶜ < b`
-/
protected inductive LT : Booleanisation α → Booleanisation α → Prop
  | protected lift {a b} : a < b → Booleanisation.LT (lift a) (lift b)
  | protected comp {a b} : a < b → Booleanisation.LT (comp b) (comp a)
  | protected sep {a b} : Disjoint a b → Booleanisation.LT (lift a) (comp b)

@[inherit_doc Booleanisation.LE]
/-
**Booleanisation.instLE** 是 Mathlib 中的一个实例，位于命名空间 `Booleanisation`。
形式化陈述：instLE : LE (Booleanisation α) where le
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLE : LE (Booleanisation α) where
  le := Booleanisation.LE

@[inherit_doc Booleanisation.LT]
/-
**Booleanisation.instLT** 是 Mathlib 中的一个实例，位于命名空间 `Booleanisation`。
形式化陈述：instLT : LT (Booleanisation α) where lt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLT : LT (Booleanisation α) where
  lt := Booleanisation.LT

/-- The supremum on `Booleanisation α` is as follows: For `a b : α`,
* `a ⊔ b` is `a ⊔ b`
* `a ⊔ bᶜ` is `(b \ a)ᶜ`
* `aᶜ ⊔ b` is `(a \ b)ᶜ`
* `aᶜ ⊔ bᶜ` is `(a ⊓ b)ᶜ` -/
/-
**Booleanisation.instSup** 是 Mathlib 中的一个定义，位于命名空间 `Booleanisation`。
形式化陈述：{α : Type u_1} → [GeneralizedBooleanAlgebra α] → Max (Booleanisation α)
参数：Booleanisation α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The supremum on `Booleanisation α` is as follows: For `a b : α`,
* `a ⊔ b` is `a ⊔ b`
* `a ⊔ bᶜ` is `(b \ a)ᶜ`
* `aᶜ ⊔ b` is `(a \ b)ᶜ`
* `aᶜ ⊔ bᶜ` is `(a ⊓ b)ᶜ`
-/
instance instSup : Max (Booleanisation α) where
  max
    | lift a, lift b => lift (a ⊔ b)
    | lift a, comp b => comp (b \ a)
    | comp a, lift b => comp (a \ b)
    | comp a, comp b => comp (a ⊓ b)

/-- The infimum on `Booleanisation α` is as follows: For `a b : α`,
* `a ⊓ b` is `a ⊓ b`
* `a ⊓ bᶜ` is `a \ b`
* `aᶜ ⊓ b` is `b \ a`
* `aᶜ ⊓ bᶜ` is `(a ⊔ b)ᶜ` -/
/-
**Booleanisation.instInf** 是 Mathlib 中的一个定义，位于命名空间 `Booleanisation`。
形式化陈述：{α : Type u_1} → [GeneralizedBooleanAlgebra α] → Min (Booleanisation α)
参数：Booleanisation α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The infimum on `Booleanisation α` is as follows: For `a b : α`,
* `a ⊓ b` is `a ⊓ b`
* `a ⊓ bᶜ` is `a \ b`
* `aᶜ ⊓ b` is `b \ a`
* `aᶜ ⊓ bᶜ` is `(a ⊔ b)ᶜ`
-/
instance instInf : Min (Booleanisation α) where
  min
    | lift a, lift b => lift (a ⊓ b)
    | lift a, comp b => lift (a \ b)
    | comp a, lift b => lift (b \ a)
    | comp a, comp b => comp (a ⊔ b)

/-- The bottom element of `Booleanisation α` is the bottom element of `α`. -/
/-
**Booleanisation.instBot** 是 Mathlib 中的一个实例，位于命名空间 `Booleanisation`。
形式化陈述：instBot : Bot (Booleanisation α) where bot
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bottom element of `Booleanisation α` is the bottom element of `α`.
-/
instance instBot : Bot (Booleanisation α) where
  bot := lift ⊥

/-- The top element of `Booleanisation α` is the complement of the bottom element of `α`. -/
/-
**Booleanisation.instTop** 是 Mathlib 中的一个实例，位于命名空间 `Booleanisation`。
形式化陈述：instTop : Top (Booleanisation α) where top
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The top element of `Booleanisation α` is the complement of the bottom element of
 `α`.
-/
instance instTop : Top (Booleanisation α) where
  top := comp ⊥

/-- The difference operator on `Booleanisation α` is as follows: For `a b : α`,
* `a \ b` is `a \ b`
* `a \ bᶜ` is `a ⊓ b`
* `aᶜ \ b` is `(a ⊔ b)ᶜ`
* `aᶜ \ bᶜ` is `b \ a` -/
/-
**Booleanisation.instSDiff** 是 Mathlib 中的一个定义，位于命名空间 `Booleanisation`。
形式化陈述：{α : Type u_1} → [GeneralizedBooleanAlgebra α] → SDiff (Booleanisation α)
参数：Booleanisation α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The difference operator on `Booleanisation α` is as follows: For `a b : α`,
* `a \ b` is `a \ b`
* `a \ bᶜ` is `a ⊓ b`
* `aᶜ \ b` is `(a ⊔ b)ᶜ`
* `aᶜ \ bᶜ` is `b \ a`
-/
instance instSDiff : SDiff (Booleanisation α) where
  sdiff
    | lift a, lift b => lift (a \ b)
    | lift a, comp b => lift (a ⊓ b)
    | comp a, lift b => comp (a ⊔ b)
    | comp a, comp b => lift (b \ a)

variable {a b : α}
/-
**Booleanisation.lift_le_lift** 是 Mathlib 中的一个定理，位于命名空间 `Booleanisation`。
形式化陈述：∀ {α : Type u_1} [inst : GeneralizedBooleanAlgebra α] {a b : α}, Booleanis
ation.lift a ≤ Booleanisation.lift b ↔ a ≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
@[simp] lemma lift_le_lift : lift a ≤ lift b ↔ a ≤ b := ⟨by rintro ⟨_⟩; assumption, LE.lift⟩
/-
**Booleanisation.comp_le_comp** 是 Mathlib 中的一个定理，位于命名空间 `Booleanisation`。
形式化陈述：∀ {α : Type u_1} [inst : GeneralizedBooleanAlgebra α] {a b : α}, Booleanis
ation.comp a ≤ Booleanisation.comp b ↔ b ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
@[simp] lemma comp_le_comp : comp a ≤ comp b ↔ b ≤ a := ⟨by rintro ⟨_⟩; assumption, LE.comp⟩
/-
**Booleanisation.lift_le_comp** 是 Mathlib 中的一个定理，位于命名空间 `Booleanisation`。
形式化陈述：∀ {α : Type u_1} [inst : GeneralizedBooleanAlgebra α] {a b : α},   Boolean
isation.lift a ≤ Booleanisation.comp b ↔ Disjoint a b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
@[simp] lemma lift_le_comp : lift a ≤ comp b ↔ Disjoint a b := ⟨by rintro ⟨_⟩; assumption, LE.sep⟩
/-
**Booleanisation.not_comp_le_lift** 是 Mathlib 中的一个定理，位于命名空间 `Booleanisation`。
形式化陈述：∀ {α : Type u_1} [inst : GeneralizedBooleanAlgebra α] {a b : α}, ¬Booleani
sation.comp a ≤ Booleanisation.lift b
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma not_comp_le_lift : ¬ comp a ≤ lift b := fun h ↦ nomatch h
/-
**Booleanisation.lift_lt_lift** 是 Mathlib 中的一个定理，位于命名空间 `Booleanisation`。
形式化陈述：∀ {α : Type u_1} [inst : GeneralizedBooleanAlgebra α] {a b : α}, Booleanis
ation.lift a < Booleanisation.lift b ↔ a < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
@[simp] lemma lift_lt_lift : lift a < lift b ↔ a < b := ⟨by rintro ⟨_⟩; assumption, LT.lift⟩
/-
**Booleanisation.comp_lt_comp** 是 Mathlib 中的一个定理，位于命名空间 `Booleanisation`。
形式化陈述：∀ {α : Type u_1} [inst : GeneralizedBooleanAlgebra α] {a b : α}, Booleanis
ation.comp a < Booleanisation.comp b ↔ b < a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
@[simp] lemma comp_lt_comp : comp a < comp b ↔ b < a := ⟨by rintro ⟨_⟩; assumption, LT.comp⟩
/-
**Booleanisation.lift_lt_comp** 是 Mathlib 中的一个定理，位于命名空间 `Booleanisation`。
形式化陈述：∀ {α : Type u_1} [inst : GeneralizedBooleanAlgebra α] {a b : α},   Boolean
isation.lift a < Booleanisation.comp b ↔ Disjoint a b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
@[simp] lemma lift_lt_comp : lift a < comp b ↔ Disjoint a b := ⟨by rintro ⟨_⟩; assumption, LT.sep⟩
/-
**Booleanisation.not_comp_lt_lift** 是 Mathlib 中的一个定理，位于命名空间 `Booleanisation`。
形式化陈述：∀ {α : Type u_1} [inst : GeneralizedBooleanAlgebra α] {a b : α}, ¬Booleani
sation.comp a < Booleanisation.lift b
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma not_comp_lt_lift : ¬ comp a < lift b := fun h ↦ nomatch h
/-
**Booleanisation.lift_sup_lift** 是 Mathlib 中的一个定理，位于命名空间 `Booleanisation`。
形式化陈述：∀ {α : Type u_1} [inst : GeneralizedBooleanAlgebra α] (a b : α),   Boolean
isation.lift a ⊔ Booleanisation.lift b = Booleanisation.lift (a ⊔ b)
参数：a b : α；a ⊔ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma lift_sup_lift (a b : α) : lift a ⊔ lift b = lift (a ⊔ b) := rfl
/-
**Booleanisation.lift_sup_comp** 是 Mathlib 中的一个定理，位于命名空间 `Booleanisation`。
形式化陈述：∀ {α : Type u_1} [inst : GeneralizedBooleanAlgebra α] (a b : α),   Boolean
isation.lift a ⊔ Booleanisation.comp b = Booleanisation.comp (b \ a)
参数：a b : α；b \ a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma lift_sup_comp (a b : α) : lift a ⊔ comp b = comp (b \ a) := rfl
/-
**Booleanisation.comp_sup_lift** 是 Mathlib 中的一个定理，位于命名空间 `Booleanisation`。
形式化陈述：∀ {α : Type u_1} [inst : GeneralizedBooleanAlgebra α] (a b : α),   Boolean
isation.comp a ⊔ Booleanisation.lift b = Booleanisation.comp (a \ b)
参数：a b : α；a \ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma comp_sup_lift (a b : α) : comp a ⊔ lift b = comp (a \ b) := rfl
/-
**Booleanisation.comp_sup_comp** 是 Mathlib 中的一个定理，位于命名空间 `Booleanisation`。
形式化陈述：∀ {α : Type u_1} [inst : GeneralizedBooleanAlgebra α] (a b : α),   Boolean
isation.comp a ⊔ Booleanisation.comp b = Booleanisation.comp (a ⊓ b)
参数：a b : α；a ⊓ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma comp_sup_comp (a b : α) : comp a ⊔ comp b = comp (a ⊓ b) := rfl
/-
**Booleanisation.lift_inf_lift** 是 Mathlib 中的一个定理，位于命名空间 `Booleanisation`。
形式化陈述：∀ {α : Type u_1} [inst : GeneralizedBooleanAlgebra α] (a b : α),   Boolean
isation.lift a ⊓ Booleanisation.lift b = Booleanisation.lift (a ⊓ b)
参数：a b : α；a ⊓ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma lift_inf_lift (a b : α) : lift a ⊓ lift b = lift (a ⊓ b) := rfl
/-
**Booleanisation.lift_inf_comp** 是 Mathlib 中的一个定理，位于命名空间 `Booleanisation`。
形式化陈述：∀ {α : Type u_1} [inst : GeneralizedBooleanAlgebra α] (a b : α),   Boolean
isation.lift a ⊓ Booleanisation.comp b = Booleanisation.lift (a \ b)
参数：a b : α；a \ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma lift_inf_comp (a b : α) : lift a ⊓ comp b = lift (a \ b) := rfl
/-
**Booleanisation.comp_inf_lift** 是 Mathlib 中的一个定理，位于命名空间 `Booleanisation`。
形式化陈述：∀ {α : Type u_1} [inst : GeneralizedBooleanAlgebra α] (a b : α),   Boolean
isation.comp a ⊓ Booleanisation.lift b = Booleanisation.lift (b \ a)
参数：a b : α；b \ a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma comp_inf_lift (a b : α) : comp a ⊓ lift b = lift (b \ a) := rfl
/-
**Booleanisation.comp_inf_comp** 是 Mathlib 中的一个定理，位于命名空间 `Booleanisation`。
形式化陈述：∀ {α : Type u_1} [inst : GeneralizedBooleanAlgebra α] (a b : α),   Boolean
isation.comp a ⊓ Booleanisation.comp b = Booleanisation.comp (a ⊔ b)
参数：a b : α；a ⊔ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma comp_inf_comp (a b : α) : comp a ⊓ comp b = comp (a ⊔ b) := rfl
/-
**Booleanisation.lift_bot** 是 Mathlib 中的一个定理，位于命名空间 `Booleanisation`。
形式化陈述：∀ {α : Type u_1} [inst : GeneralizedBooleanAlgebra α], Booleanisation.lift
 ⊥ = ⊥
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma lift_bot : lift (⊥ : α) = ⊥ := rfl
/-
**Booleanisation.comp_bot** 是 Mathlib 中的一个定理，位于命名空间 `Booleanisation`。
形式化陈述：∀ {α : Type u_1} [inst : GeneralizedBooleanAlgebra α], Booleanisation.comp
 ⊥ = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma comp_bot : comp (⊥ : α) = ⊤ := rfl
/-
**Booleanisation.lift_sdiff_lift** 是 Mathlib 中的一个定理，位于命名空间 `Booleanisation`。
形式化陈述：∀ {α : Type u_1} [inst : GeneralizedBooleanAlgebra α] (a b : α),   Boolean
isation.lift a \ Booleanisation.lift b = Booleanisation.lift (a \ b)
参数：a b : α；a \ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma lift_sdiff_lift (a b : α) : lift a \ lift b = lift (a \ b) := rfl
/-
**Booleanisation.lift_sdiff_comp** 是 Mathlib 中的一个定理，位于命名空间 `Booleanisation`。
形式化陈述：∀ {α : Type u_1} [inst : GeneralizedBooleanAlgebra α] (a b : α),   Boolean
isation.lift a \ Booleanisation.comp b = Booleanisation.lift (a ⊓ b)
参数：a b : α；a ⊓ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma lift_sdiff_comp (a b : α) : lift a \ comp b = lift (a ⊓ b) := rfl
/-
**Booleanisation.comp_sdiff_lift** 是 Mathlib 中的一个定理，位于命名空间 `Booleanisation`。
形式化陈述：∀ {α : Type u_1} [inst : GeneralizedBooleanAlgebra α] (a b : α),   Boolean
isation.comp a \ Booleanisation.lift b = Booleanisation.comp (a ⊔ b)
参数：a b : α；a ⊔ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma comp_sdiff_lift (a b : α) : comp a \ lift b = comp (a ⊔ b) := rfl
/-
**Booleanisation.comp_sdiff_comp** 是 Mathlib 中的一个定理，位于命名空间 `Booleanisation`。
形式化陈述：∀ {α : Type u_1} [inst : GeneralizedBooleanAlgebra α] (a b : α),   Boolean
isation.comp a \ Booleanisation.comp b = Booleanisation.lift (b \ a)
参数：a b : α；b \ a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma comp_sdiff_comp (a b : α) : comp a \ comp b = lift (b \ a) := rfl
/-
**Booleanisation.instPreorder** 是 Mathlib 中的一个实例，位于命名空间 `Booleanisation`。
形式化陈述：instPreorder : Preorder (Booleanisation α) where lt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPreorder : Preorder (Booleanisation α) where
  lt := (· < ·)
  lt_iff_le_not_ge
    | lift a, lift b => by simp [lt_iff_le_not_ge]
    | lift a, comp b => by simp
    | comp a, lift b => by simp
    | comp a, comp b => by simp [lt_iff_le_not_ge]
  le_refl
    | lift _ => LE.lift le_rfl
    | comp _ => LE.comp le_rfl
  le_trans
    | lift _, lift _, lift _, LE.lift hab, LE.lift hbc => LE.lift <| hab.trans hbc
    | lift _, lift _, comp _, LE.lift hab, LE.sep hbc => LE.sep <| hbc.mono_left hab
    | lift _, comp _, comp _, LE.sep hab, LE.comp hcb => LE.sep <| hab.mono_right hcb
    | comp _, comp _, comp _, LE.comp hba, LE.comp hcb => LE.comp <| hcb.trans hba
/-
**Booleanisation.instPartialOrder** 是 Mathlib 中的一个定义，位于命名空间 `Booleanisation`。
形式化陈述：{α : Type u_1} → [GeneralizedBooleanAlgebra α] → PartialOrder (Booleanisat
ion α)
参数：Booleanisation α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPartialOrder : PartialOrder (Booleanisation α) where
  le_antisymm
    | lift a, lift b, LE.lift hab, LE.lift hba => by rw [hab.antisymm hba]
    | comp a, comp b, LE.comp hab, LE.comp hba => by rw [hab.antisymm hba]

-- The linter significantly hinders readability here.
set_option linter.unusedVariables false in
/-
**Booleanisation.instSemilatticeSup** 是 Mathlib 中的一个实例，位于命名空间 `Booleanisation`。
形式化陈述：instSemilatticeSup : SemilatticeSup (Booleanisation α) where sup x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemilatticeSup : SemilatticeSup (Booleanisation α) where
  sup x y := max x y
  le_sup_left
    | lift a, lift b => LE.lift le_sup_left
    | lift a, comp b => LE.sep disjoint_sdiff_self_right
    | comp a, lift b => LE.comp sdiff_le
    | comp a, comp b => LE.comp inf_le_left
  le_sup_right
    | lift a, lift b => LE.lift le_sup_right
    | lift a, comp b => LE.comp sdiff_le
    | comp a, lift b => LE.sep disjoint_sdiff_self_right
    | comp a, comp b => LE.comp inf_le_right
  sup_le
    | lift a, lift b, lift c, LE.lift hac, LE.lift hbc => LE.lift <| sup_le hac hbc
    | lift a, lift b, comp c, LE.sep hac, LE.sep hbc => LE.sep <| hac.sup_left hbc
    | lift a, comp b, comp c, LE.sep hac, LE.comp hcb => LE.comp <| le_sdiff.2 ⟨hcb, hac.symm⟩
    | comp a, lift b, comp c, LE.comp hca, LE.sep hbc => LE.comp <| le_sdiff.2 ⟨hca, hbc.symm⟩
    | comp a, comp b, comp c, LE.comp hca, LE.comp hcb => LE.comp <| le_inf hca hcb

-- The linter significantly hinders readability here.
set_option linter.unusedVariables false in
/-
**Booleanisation.instSemilatticeInf** 是 Mathlib 中的一个实例，位于命名空间 `Booleanisation`。
形式化陈述：instSemilatticeInf : SemilatticeInf (Booleanisation α) where inf x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemilatticeInf : SemilatticeInf (Booleanisation α) where
  inf x y := min x y
  inf_le_left
    | lift a, lift b => LE.lift inf_le_left
    | lift a, comp b => LE.lift sdiff_le
    | comp a, lift b => LE.sep disjoint_sdiff_self_left
    | comp a, comp b => LE.comp le_sup_left
  inf_le_right
    | lift a, lift b => LE.lift inf_le_right
    | lift a, comp b => LE.sep disjoint_sdiff_self_left
    | comp a, lift b => LE.lift sdiff_le
    | comp a, comp b => LE.comp le_sup_right
  le_inf
    | lift a, lift b, lift c, LE.lift hab, LE.lift hac => LE.lift <| le_inf hab hac
    | lift a, lift b, comp c, LE.lift hab, LE.sep hac => LE.lift <| le_sdiff.2 ⟨hab, hac⟩
    | lift a, comp b, lift c, LE.sep hab, LE.lift hac => LE.lift <| le_sdiff.2 ⟨hac, hab⟩
    | lift a, comp b, comp c, LE.sep hab, LE.sep hac => LE.sep <| hab.sup_right hac
    | comp a, comp b, comp c, LE.comp hba, LE.comp hca => LE.comp <| sup_le hba hca
/-
**Booleanisation.instDistribLattice** 是 Mathlib 中的一个实例，位于命名空间 `Booleanisation`。
形式化陈述：instDistribLattice : DistribLattice (Booleanisation α) where inf x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribLattice : DistribLattice (Booleanisation α) where
  inf x y := x ⊓ y
  inf_le_left _ _ := inf_le_left
  inf_le_right _ _ := inf_le_right
  le_inf _ _ _ := le_inf
  le_sup_inf
    | lift _, lift _, lift _ => LE.lift le_sup_inf
    | lift a, lift b, comp c => LE.lift <| by simp [sup_comm, sup_assoc]
    | lift a, comp b, lift c => LE.lift <| by
      simp [sup_left_comm (a := b \ a), sup_comm (a := b \ a)]
    | lift a, comp b, comp c => LE.comp <| by rw [sup_sdiff]
    | comp a, lift b, lift c => LE.comp <| by rw [sdiff_inf]
    | comp a, lift b, comp c => LE.comp <| by rw [sdiff_sdiff_right']
    | comp a, comp b, lift c => LE.comp <| by rw [sdiff_sdiff_right', sup_comm]
    | comp _, comp _, comp _ => LE.comp (inf_sup_left _ _ _).le

-- The linter significantly hinders readability here.
set_option linter.unusedVariables false in
/-
**Booleanisation.instBoundedOrder** 是 Mathlib 中的一个定义，位于命名空间 `Booleanisation`。
形式化陈述：{α : Type u_1} → [inst : GeneralizedBooleanAlgebra α] → BoundedOrder (Bool
eanisation α)
参数：Booleanisation α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instBoundedOrder : BoundedOrder (Booleanisation α) where
  le_top
    | lift a => LE.sep disjoint_bot_right
    | comp a => LE.comp bot_le
  bot_le
    | lift a => LE.lift bot_le
    | comp a => LE.sep disjoint_bot_left
/-
**Booleanisation.instBooleanAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `Booleanisation`。
形式化陈述：instBooleanAlgebra : BooleanAlgebra (Booleanisation α) where le_top _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instBooleanAlgebra : BooleanAlgebra (Booleanisation α) where
  le_top _ := le_top
  bot_le _ := bot_le
  inf_compl_le_bot
    | lift a => by simp
    | comp a => by simp
  top_le_sup_compl
    | lift a => by simp
    | comp a => by simp
  sdiff_eq
    | lift a, lift b => by simp
    | lift a, comp b => by simp
    | comp a, lift b => by simp
    | comp a, comp b => by simp

/-- The embedding from a generalised Boolean algebra to its generated Boolean algebra. -/
/-
**Booleanisation.liftLatticeHom** 是 Mathlib 中的一个定义，位于命名空间 `Booleanisation`。
形式化陈述：liftLatticeHom : LatticeHom α (Booleanisation α) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding from a generalised Boolean algebra to its generated Boolean algebr
a.
-/
def liftLatticeHom : LatticeHom α (Booleanisation α) where
  toFun := lift
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl
/-
**Booleanisation.liftLatticeHom_injective** 是 Mathlib 中的一个引理，位于命名空间 `Booleanisat
ion`。
形式化陈述：liftLatticeHom_injective : Injective (liftLatticeHom (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
-/
lemma liftLatticeHom_injective : Injective (liftLatticeHom (α := α)) := Sum.inl_injective

end Booleanisation

