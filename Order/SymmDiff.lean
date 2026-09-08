/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Bryan Gin-ge Chen, Yaël Dillies
-/
module

public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Logic.Equiv.Basic

/-!
# Symmetric difference and bi-implication

This file defines the symmetric difference and bi-implication operators in (co-)Heyting algebras.

## Examples

Some examples are
* The symmetric difference of two sets is the set of elements that are in either but not both.
* The symmetric difference on propositions is `Xor`.
* The symmetric difference on `Bool` is `Bool.xor`.
* The equivalence of propositions. Two propositions are equivalent if they imply each other.
* The symmetric difference translates to addition when considering a Boolean algebra as a Boolean
  ring.

## Main declarations

* `symmDiff`: The symmetric difference operator, defined as `(a \ b) ⊔ (b \ a)`
* `bihimp`: The bi-implication operator, defined as `(b ⇨ a) ⊓ (a ⇨ b)`

In generalized Boolean algebras, the symmetric difference operator is:

* `symmDiff_comm`: commutative, and
* `symmDiff_assoc`: associative.

## Notation

* `a ∆ b`: `symmDiff a b`
* `a ⇔ b`: `bihimp a b`

## References

The proof of associativity follows the note "Associativity of the Symmetric Difference of Sets: A
Proof from the Book" by John McCuan:

* <https://people.math.gatech.edu/~mccuan/courses/4317/symmetricdifference.pdf>

## Tags

boolean ring, generalized boolean algebra, boolean algebra, symmetric difference, bi-implication,
Heyting
-/

@[expose] public section

assert_not_exists RelIso

open Function OrderDual

variable {ι α β : Type*} {π : ι → Type*}

to_dual_name_hint Compl HNot, SDiff HImp

/-- The symmetric difference operator on a type with `⊔` and `\` is `(A \ B) ⊔ (B \ A)`. -/
@[to_dual
/-- The Heyting bi-implication is `(b ⇨ a) ⊓ (a ⇨ b)`. This generalizes equivalence of
propositions. -/]
/-
**symmDiff** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：symmDiff [Max α] [SDiff α] (a b : α) : α
参数：a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def symmDiff [Max α] [SDiff α] (a b : α) : α :=
  a \ b ⊔ b \ a

/-- Notation for symmDiff -/
scoped[symmDiff] infixl:100 " ∆ " => symmDiff

/-- Notation for bihimp -/
scoped[symmDiff] infixl:100 " ⇔ " => bihimp

open scoped symmDiff

@[to_dual]
/-
**symmDiff_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_def [Max α] [SDiff α] (a b : α) : a ∆ b = a \ b ⊔ b \ a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symmDiff_def [Max α] [SDiff α] (a b : α) : a ∆ b = a \ b ⊔ b \ a :=
  rfl
/-
**symmDiff_eq_xor** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_eq_xor (p q : Prop) : p ∆ q = Xor p q
参数：p q : Prop。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symmDiff_eq_xor (p q : Prop) : p ∆ q = Xor p q :=
  rfl

@[deprecated (since := "2026-04-27")] alias symmDiff_eq_Xor' := symmDiff_eq_xor

@[simp]
/-
**bihimp_iff_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bihimp_iff_iff {p q : Prop} : p ⇔ q ↔ (p ↔ q)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `iff_iff_implies_and_implies`：∀ {a b : Prop}, (a ↔ b) ↔ (a → b) ∧ (b → a)
· 使用定理 `Iff.comm`：∀ {a b : Prop}, (a ↔ b) ↔ (b ↔ a)
-/
theorem bihimp_iff_iff {p q : Prop} : p ⇔ q ↔ (p ↔ q) :=
  iff_iff_implies_and_implies.symm.trans Iff.comm

@[simp]
/-
**Bool.symmDiff_eq_xor** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Bool.symmDiff_eq_xor : forall p q : Bool, p ∆ q = xor p q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem Bool.symmDiff_eq_xor : ∀ p q : Bool, p ∆ q = xor p q := by decide

section GeneralizedCoheytingAlgebra

variable [GeneralizedCoheytingAlgebra α] (a b c : α)

@[to_dual (attr := simp)]
/-
**toDual_symmDiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toDual_symmDiff : toDual (a ∆ b) = toDual a ⇔ toDual b
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toDual_symmDiff : toDual (a ∆ b) = toDual a ⇔ toDual b :=
  rfl

@[to_dual (attr := simp)]
/-
**ofDual_bihimp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofDual_bihimp (a b : αᵒᵈ) : ofDual (a ⇔ b) = ofDual a ∆ ofDual b
参数：a b : αᵒᵈ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofDual_bihimp (a b : αᵒᵈ) : ofDual (a ⇔ b) = ofDual a ∆ ofDual b :=
  rfl

@[to_dual]
/-
**symmDiff_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_comm : a ∆ b = b ∆ a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem symmDiff_comm : a ∆ b = b ∆ a := by simp only [symmDiff, sup_comm]

@[to_dual]
/-
**symmDiff_isCommutative** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：symmDiff_isCommutative : Std.Commutative (α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `symmDiff_comm`：symmDiff_comm : a ∆ b = b ∆ a
-/
instance symmDiff_isCommutative : Std.Commutative (α := α) (· ∆ ·) :=
  ⟨symmDiff_comm⟩

@[to_dual (attr := simp)]
/-
**symmDiff_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_self : a ∆ a = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff.eq_1`：∀ {α : Type u_2} [inst : Max α] [inst_1 : SDiff α] (a b :
 α), symmDiff a b = a \ b ⊔ b \ a
· 使用定理 `sup_idem`：sup_idem (a : α) : a ⊔ a = a
· 使用定理 `sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a :
 α}, a \ a = ⊥
-/
theorem symmDiff_self : a ∆ a = ⊥ := by rw [symmDiff, sup_idem, sdiff_self]

@[to_dual (attr := simp)]
/-
**symmDiff_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_bot : a ∆ ⊥ = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff.eq_1`：∀ {α : Type u_2} [inst : Max α] [inst_1 : SDiff α] (a b :
 α), symmDiff a b = a \ b ⊔ b \ a
· 使用定理 `sdiff_bot`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a : 
α}, a \ ⊥ = a
· 使用定理 `bot_sdiff`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a : 
α}, ⊥ \ a = ⊥
· 使用定理 `sup_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), a ⊔ ⊥ = a
-/
theorem symmDiff_bot : a ∆ ⊥ = a := by rw [symmDiff, sdiff_bot, bot_sdiff, sup_bot_eq]

@[to_dual (attr := simp)]
/-
**bot_symmDiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bot_symmDiff : ⊥ ∆ a = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_comm`：symmDiff_comm : a ∆ b = b ∆ a
· 使用定理 `symmDiff_bot`：symmDiff_bot : a ∆ ⊥ = a
-/
theorem bot_symmDiff : ⊥ ∆ a = a := by rw [symmDiff_comm, symmDiff_bot]

@[to_dual (attr := simp)]
/-
**symmDiff_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_eq_bot {a b : α} : a ∆ b = ⊥ ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem symmDiff_eq_bot {a b : α} : a ∆ b = ⊥ ↔ a = b := by
  simp_rw [symmDiff, sup_eq_bot_iff, sdiff_eq_bot_iff, le_antisymm_iff]

@[to_dual]
/-
**symmDiff_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_of_le {a b : α} (h : a <= b) : a ∆ b = b \ a
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff.eq_1`：∀ {α : Type u_2} [inst : Max α] [inst_1 : SDiff α] (a b :
 α), symmDiff a b = a \ b ⊔ b \ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sdiff_eq_bot_iff`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α
] {a b : α}, b \ a = ⊥ ↔ b ≤ a
· 使用定理 `bot_sup_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊔ a = a
-/
theorem symmDiff_of_le {a b : α} (h : a ≤ b) : a ∆ b = b \ a := by
  rw [symmDiff, sdiff_eq_bot_iff.2 h, bot_sup_eq]

@[to_dual]
/-
**symmDiff_of_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_of_ge {a b : α} (h : b <= a) : a ∆ b = a \ b
参数：h : b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff.eq_1`：∀ {α : Type u_2} [inst : Max α] [inst_1 : SDiff α] (a b :
 α), symmDiff a b = a \ b ⊔ b \ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sdiff_eq_bot_iff`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α
] {a b : α}, b \ a = ⊥ ↔ b ≤ a
· 使用定理 `sup_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), a ⊔ ⊥ = a
-/
theorem symmDiff_of_ge {a b : α} (h : b ≤ a) : a ∆ b = a \ b := by
  rw [symmDiff, sdiff_eq_bot_iff.2 h, sup_bot_eq]

@[to_dual le_bihimp]
/-
**symmDiff_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_le {a b c : α} (ha : a <= b ⊔ c) (hb : b <= a ⊔ c) : a ∆ b <= c
参数：ha : a <= b ⊔ c；hb : b <= a ⊔ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sdiff_le_iff`：sdiff_le_iff [GeneralizedCoheytingAlgebra α] {a b c : α} :
 a \ b <= c ↔ a <= b ⊔ c
-/
theorem symmDiff_le {a b c : α} (ha : a ≤ b ⊔ c) (hb : b ≤ a ⊔ c) : a ∆ b ≤ c :=
  sup_le (sdiff_le_iff.2 ha) <| sdiff_le_iff.2 hb

@[to_dual le_bihimp_iff]
/-
**symmDiff_le_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_le_iff {a b c : α} : a ∆ b <= c ↔ a <= b ⊔ c ∧ b <= a ⊔ c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem symmDiff_le_iff {a b c : α} : a ∆ b ≤ c ↔ a ≤ b ⊔ c ∧ b ≤ a ⊔ c := by
  simp_rw [symmDiff, sup_le_iff, sdiff_le_iff]

@[to_dual (attr := simp) inf_le_bihimp]
/-
**symmDiff_le_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_le_sup {a b : α} : a ∆ b <= a ⊔ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
-/
theorem symmDiff_le_sup {a b : α} : a ∆ b ≤ a ⊔ b :=
  sup_le_sup sdiff_le sdiff_le

@[to_dual bihimp_eq_sup_himp_inf]
/-
**symmDiff_eq_sup_sdiff_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_eq_sup_sdiff_inf : a ∆ b = (a ⊔ b) \ (a ⊓ b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_sdiff`：sup_sdiff : (a ⊔ b) \ c = a \ c ⊔ b \ c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sdiff_inf_self_left`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebr
a α] (a b : α), a \ (a ⊓ b) = a \ b
· 使用定理 `sdiff_inf_self_right`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgeb
ra α] (a b : α), b \ (a ⊓ b) = b \ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem symmDiff_eq_sup_sdiff_inf : a ∆ b = (a ⊔ b) \ (a ⊓ b) := by simp [sup_sdiff, symmDiff]

@[to_dual]
/-
**Disjoint.symmDiff_eq_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.symmDiff_eq_sup {a b : α} (h : Disjoint a b) : a ∆ b = a ⊔ b
参数：h : Disjoint a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff.eq_1`：∀ {α : Type u_2} [inst : Max α] [inst_1 : SDiff α] (a b :
 α), symmDiff a b = a \ b ⊔ b \ a
· 使用定理 `Disjoint.sdiff_eq_left`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlg
ebra α] {a b : α}, Disjoint a b → a \ b = a
· 使用定理 `Disjoint.sdiff_eq_right`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAl
gebra α] {a b : α}, Disjoint a b → b \ a = b
-/
theorem Disjoint.symmDiff_eq_sup {a b : α} (h : Disjoint a b) : a ∆ b = a ⊔ b := by
  rw [symmDiff, h.sdiff_eq_left, h.sdiff_eq_right]

@[to_dual himp_bihimp]
/-
**symmDiff_sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_sdiff : a ∆ b \ c = a \ (b ⊔ c) ⊔ b \ (a ⊔ c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff.eq_1`：∀ {α : Type u_2} [inst : Max α] [inst_1 : SDiff α] (a b :
 α), symmDiff a b = a \ b ⊔ b \ a
· 使用定理 `sup_sdiff_distrib`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra 
α] (b c a : α), (b ⊔ c) \ a = b \ a ⊔ c \ a
· 使用定理 `sdiff_sdiff_left`：sdiff_sdiff_left : (a \ b) \ c = a \ (b ⊔ c)
-/
theorem symmDiff_sdiff : a ∆ b \ c = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) := by
  rw [symmDiff, sup_sdiff_distrib, sdiff_sdiff_left, sdiff_sdiff_left]

@[to_dual (attr := simp) sup_himp_bihimp]
/-
**symmDiff_sdiff_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_sdiff_inf : a ∆ b \ (a ⊓ b) = a ∆ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_sdiff`：symmDiff_sdiff : a ∆ b \ c = a \ (b ⊔ c) ⊔ b \ (a ⊔ c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem symmDiff_sdiff_inf : a ∆ b \ (a ⊓ b) = a ∆ b := by
  rw [symmDiff_sdiff]
  simp [symmDiff]

@[to_dual (attr := simp)]
/-
**symmDiff_sdiff_eq_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_sdiff_eq_sup : a ∆ (b \ a) = a ⊔ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff.eq_1`：∀ {α : Type u_2} [inst : Max α] [inst_1 : SDiff α] (a b :
 α), symmDiff a b = a \ b ⊔ b \ a
· 使用定理 `sdiff_idem`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b
 : α}, (a \ b) \ b = a \ b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `le_sdiff_sup`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a
 b : α}, b ≤ b \ a ⊔ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem symmDiff_sdiff_eq_sup : a ∆ (b \ a) = a ⊔ b := by
  rw [symmDiff, sdiff_idem]
  exact
    le_antisymm (sup_le_sup sdiff_le sdiff_le)
      (sup_le le_sdiff_sup <| le_sdiff_sup.trans <| sup_le le_sup_right le_sdiff_sup)

@[to_dual (attr := simp)]
/-
**sdiff_symmDiff_eq_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_symmDiff_eq_sup : (a \ b) ∆ b = a ⊔ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_comm`：symmDiff_comm : a ∆ b = b ∆ a
· 使用定理 `symmDiff_sdiff_eq_sup`：symmDiff_sdiff_eq_sup : a ∆ (b \ a) = a ⊔ b
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
-/
theorem sdiff_symmDiff_eq_sup : (a \ b) ∆ b = a ⊔ b := by
  rw [symmDiff_comm, symmDiff_sdiff_eq_sup, sup_comm]

@[to_dual (attr := simp)]
/-
**symmDiff_sup_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_sup_inf : a ∆ b ⊔ a ⊓ b = a ⊔ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `symmDiff_le_sup`：symmDiff_le_sup {a b : α} : a ∆ b <= a ⊔ b
· 使用定理 `inf_le_sup`：inf_le_sup : a ⊓ b <= a ⊔ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_inf_left`：sup_inf_left (a b c : α) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)
· 使用定理 `symmDiff.eq_1`：∀ {α : Type u_2} [inst : Max α] [inst_1 : SDiff α] (a b :
 α), symmDiff a b = a \ b ⊔ b \ a
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `sup_right_comm`：sup_right_comm (a b c : α) : a ⊔ b ⊔ c = a ⊔ c ⊔ b
· 使用定理 `le_sup_of_le_left`：le_sup_of_le_left (h : c <= a) : c <= a ⊔ b
· 使用定理 `le_sdiff_sup`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a
 b : α}, b ≤ b \ a ⊔ a
· 使用定理 `sup_assoc`：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
· 使用定理 `le_sup_of_le_right`：le_sup_of_le_right (h : c <= b) : c <= a ⊔ b
-/
theorem symmDiff_sup_inf : a ∆ b ⊔ a ⊓ b = a ⊔ b := by
  refine le_antisymm (sup_le symmDiff_le_sup inf_le_sup) ?_
  rw [sup_inf_left, symmDiff]
  refine sup_le (le_inf le_sup_right ?_) (le_inf ?_ le_sup_right)
  · rw [sup_right_comm]
    exact le_sup_of_le_left le_sdiff_sup
  · rw [sup_assoc]
    exact le_sup_of_le_right le_sdiff_sup

@[to_dual (attr := simp)]
/-
**inf_sup_symmDiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_sup_symmDiff : a ⊓ b ⊔ a ∆ b = a ⊔ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `symmDiff_sup_inf`：symmDiff_sup_inf : a ∆ b ⊔ a ⊓ b = a ⊔ b
-/
theorem inf_sup_symmDiff : a ⊓ b ⊔ a ∆ b = a ⊔ b := by rw [sup_comm, symmDiff_sup_inf]

@[to_dual (attr := simp)]
/-
**symmDiff_symmDiff_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_symmDiff_inf : a ∆ b ∆ (a ⊓ b) = a ⊔ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `symmDiff_sdiff_inf`：symmDiff_sdiff_inf : a ∆ b \ (a ⊓ b) = a ∆ b
· 使用定理 `sdiff_symmDiff_eq_sup`：sdiff_symmDiff_eq_sup : (a \ b) ∆ b = a ⊔ b
· 使用定理 `symmDiff_sup_inf`：symmDiff_sup_inf : a ∆ b ⊔ a ⊓ b = a ⊔ b
-/
theorem symmDiff_symmDiff_inf : a ∆ b ∆ (a ⊓ b) = a ⊔ b := by
  rw [← symmDiff_sdiff_inf a, sdiff_symmDiff_eq_sup, symmDiff_sup_inf]

@[to_dual (attr := simp)]
/-
**inf_symmDiff_symmDiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_symmDiff_symmDiff : (a ⊓ b) ∆ (a ∆ b) = a ⊔ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_comm`：symmDiff_comm : a ∆ b = b ∆ a
· 使用定理 `symmDiff_symmDiff_inf`：symmDiff_symmDiff_inf : a ∆ b ∆ (a ⊓ b) = a ⊔ b
-/
theorem inf_symmDiff_symmDiff : (a ⊓ b) ∆ (a ∆ b) = a ⊔ b := by
  rw [symmDiff_comm, symmDiff_symmDiff_inf]

@[to_dual]
/-
**symmDiff_triangle** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_triangle : a ∆ c <= a ∆ b ⊔ b ∆ c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
· 使用定理 `sdiff_triangle`：sdiff_triangle (a b c : α) : a \ c <= a \ b ⊔ b \ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `sup_sup_sup_comm`：sup_sup_sup_comm (a b c d : α) : a ⊔ b ⊔ (c ⊔ d) = a ⊔
 c ⊔ (b ⊔ d)
· 使用定理 `symmDiff.eq_1`：∀ {α : Type u_2} [inst : Max α] [inst_1 : SDiff α] (a b :
 α), symmDiff a b = a \ b ⊔ b \ a
-/
theorem symmDiff_triangle : a ∆ c ≤ a ∆ b ⊔ b ∆ c := by
  refine (sup_le_sup (sdiff_triangle a b c) <| sdiff_triangle _ b _).trans_eq ?_
  rw [sup_comm (c \ b), sup_sup_sup_comm, symmDiff, symmDiff]

@[to_dual]
/-
**le_symmDiff_sup_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_symmDiff_sup_right (a b : α) : a <= (a ∆ b) ⊔ b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_bot`：symmDiff_bot : a ∆ ⊥ = a
· 使用定理 `symmDiff_triangle`：symmDiff_triangle : a ∆ c <= a ∆ b ⊔ b ∆ c
-/
theorem le_symmDiff_sup_right (a b : α) : a ≤ (a ∆ b) ⊔ b := by
  convert! symmDiff_triangle a b ⊥ <;> rw [symmDiff_bot]

@[to_dual]
/-
**le_symmDiff_sup_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_symmDiff_sup_left (a b : α) : b <= (a ∆ b) ⊔ a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_symmDiff_sup_right`：le_symmDiff_sup_right (a b : α) : a <= (a ∆ b) ⊔ 
b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `symmDiff_comm`：symmDiff_comm : a ∆ b = b ∆ a
-/
theorem le_symmDiff_sup_left (a b : α) : b ≤ (a ∆ b) ⊔ a :=
  symmDiff_comm a b ▸ le_symmDiff_sup_right ..

end GeneralizedCoheytingAlgebra

section CoheytingAlgebra

variable [CoheytingAlgebra α] (a : α)

@[to_dual (attr := simp)]
/-
**symmDiff_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_top : a ∆ ⊤ = ￢a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sdiff_top`：∀ {α : Type u_2} [inst : CoheytingAlgebra α] (a : α), a \ ⊤ =
 ⊥
· 使用定理 `top_sdiff'`：∀ {α : Type u_2} [inst : CoheytingAlgebra α] (a : α), ⊤ \ a 
= ￢a
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem symmDiff_top : a ∆ ⊤ = ￢a := by simp [symmDiff]

@[to_dual (attr := simp)]
/-
**top_symmDiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：top_symmDiff : ⊤ ∆ a = ￢a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `top_sdiff'`：∀ {α : Type u_2} [inst : CoheytingAlgebra α] (a : α), ⊤ \ a 
= ￢a
· 使用定理 `sdiff_top`：∀ {α : Type u_2} [inst : CoheytingAlgebra α] (a : α), a \ ⊤ =
 ⊥
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem top_symmDiff : ⊤ ∆ a = ￢a := by simp [symmDiff]

@[deprecated (since := "2026-08-04")] alias symmDiff_top' := symmDiff_top
@[deprecated (since := "2026-08-04")] alias top_symmDiff' := top_symmDiff

@[to_dual (attr := simp)]
/-
**hnot_symmDiff_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hnot_symmDiff_self : (￢a) ∆ a = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `symmDiff.eq_1`：∀ {α : Type u_2} [inst : Max α] [inst_1 : SDiff α] (a b :
 α), symmDiff a b = a \ b ⊔ b \ a
· 使用定理 `hnot_sdiff`：∀ {α : Type u_2} [inst : CoheytingAlgebra α] (a : α), ￢a \ a
 = ￢a
· 使用定理 `sup_sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] 
(a b : α), a ⊔ b \ a = a ⊔ b
· 使用定理 `Codisjoint.top_le`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : 
OrderTop α] {a b : α}, Codisjoint a b → ⊤ ≤ a ⊔ b
· 使用定理 `codisjoint_hnot_left`：∀ {α : Type u_2} [inst : CoheytingAlgebra α] {a : 
α}, Codisjoint (￢a) a
-/
theorem hnot_symmDiff_self : (￢a) ∆ a = ⊤ := by
  rw [eq_top_iff, symmDiff, hnot_sdiff, sup_sdiff_self]
  exact Codisjoint.top_le codisjoint_hnot_left

@[to_dual (attr := simp)]
/-
**symmDiff_hnot_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_hnot_self : a ∆ (￢a) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_comm`：symmDiff_comm : a ∆ b = b ∆ a
· 使用定理 `hnot_symmDiff_self`：hnot_symmDiff_self : (￢a) ∆ a = ⊤
-/
theorem symmDiff_hnot_self : a ∆ (￢a) = ⊤ := by rw [symmDiff_comm, hnot_symmDiff_self]

@[deprecated (since := "2026-07-15")] alias bihimp_hnot_self := bihimp_compl_self

@[to_dual]
/-
**IsCompl.symmDiff_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompl.symmDiff_eq_top {a b : α} (h : IsCompl a b) : a ∆ b = ⊤
参数：h : IsCompl a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCompl.eq_hnot`：∀ {α : Type u_2} [inst : CoheytingAlgebra α] {a b : α},
 IsCompl a b → a = ￢b
· 使用定理 `hnot_symmDiff_self`：hnot_symmDiff_self : (￢a) ∆ a = ⊤
-/
theorem IsCompl.symmDiff_eq_top {a b : α} (h : IsCompl a b) : a ∆ b = ⊤ := by
  rw [h.eq_hnot, hnot_symmDiff_self]

end CoheytingAlgebra

section GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra α] (a b c d : α)

@[simp]
/-
**sup_sdiff_symmDiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_sdiff_symmDiff : (a ⊔ b) \ a ∆ b = a ⊓ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_eq_symm`：sdiff_eq_symm (hy : y <= x) (h : x \ y = z) : x \ z = y
· 使用定理 `inf_le_sup`：inf_le_sup : a ⊓ b <= a ⊔ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_eq_sup_sdiff_inf`：symmDiff_eq_sup_sdiff_inf : a ∆ b = (a ⊔ b) \
 (a ⊓ b)
-/
theorem sup_sdiff_symmDiff : (a ⊔ b) \ a ∆ b = a ⊓ b :=
  sdiff_eq_symm inf_le_sup (by rw [symmDiff_eq_sup_sdiff_inf])
/-
**disjoint_symmDiff_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_symmDiff_inf : Disjoint (a ∆ b) (a ⊓ b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_eq_sup_sdiff_inf`：symmDiff_eq_sup_sdiff_inf : a ∆ b = (a ⊔ b) \
 (a ⊓ b)
· 使用定理 `disjoint_sdiff_self_left`：disjoint_sdiff_self_left : Disjoint (y \ x) x
-/
theorem disjoint_symmDiff_inf : Disjoint (a ∆ b) (a ⊓ b) := by
  rw [symmDiff_eq_sup_sdiff_inf]
  exact disjoint_sdiff_self_left
/-
**inf_symmDiff_distrib_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_symmDiff_distrib_left : a ⊓ b ∆ c = (a ⊓ b) ∆ (a ⊓ c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_eq_sup_sdiff_inf`：symmDiff_eq_sup_sdiff_inf : a ∆ b = (a ⊔ b) \
 (a ⊓ b)
· 使用定理 `inf_sdiff_distrib_left`：inf_sdiff_distrib_left (a b c : α) : a ⊓ b \ c =
 (a ⊓ b) \ (a ⊓ c)
· 使用定理 `inf_sup_left`：inf_sup_left (a b c : α) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c
· 使用定理 `inf_inf_distrib_left`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : 
α), a ⊓ (b ⊓ c) = a ⊓ b ⊓ (a ⊓ c)
-/
theorem inf_symmDiff_distrib_left : a ⊓ b ∆ c = (a ⊓ b) ∆ (a ⊓ c) := by
  rw [symmDiff_eq_sup_sdiff_inf, inf_sdiff_distrib_left, inf_sup_left, inf_inf_distrib_left,
    symmDiff_eq_sup_sdiff_inf]
/-
**inf_symmDiff_distrib_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_symmDiff_distrib_right : a ∆ b ⊓ c = (a ⊓ c) ∆ (b ⊓ c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_symmDiff_distrib_left`：inf_symmDiff_distrib_left : a ⊓ b ∆ c = (a ⊓ 
b) ∆ (a ⊓ c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inf_symmDiff_distrib_right : a ∆ b ⊓ c = (a ⊓ c) ∆ (b ⊓ c) := by
  simp_rw [inf_comm _ c, inf_symmDiff_distrib_left]
/-
**sdiff_symmDiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_symmDiff : c \ a ∆ b = c ⊓ a ⊓ b ⊔ c \ a ⊓ c \ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_sdiff_sup_sdiff'`：sdiff_sdiff_sup_sdiff' : z \ (x \ y ⊔ y \ x) = z
 ⊓ x ⊓ y ⊔ z \ x ⊓ z \ y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sdiff_symmDiff : c \ a ∆ b = c ⊓ a ⊓ b ⊔ c \ a ⊓ c \ b := by
  simp only [(· ∆ ·), sdiff_sdiff_sup_sdiff']
/-
**sdiff_symmDiff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_symmDiff' : c \ a ∆ b = c ⊓ a ⊓ b ⊔ c \ (a ⊔ b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_symmDiff`：sdiff_symmDiff : c \ a ∆ b = c ⊓ a ⊓ b ⊔ c \ a ⊓ c \ b
· 使用定理 `sdiff_sup`：sdiff_sup : y \ (x ⊔ z) = y \ x ⊓ y \ z
-/
theorem sdiff_symmDiff' : c \ a ∆ b = c ⊓ a ⊓ b ⊔ c \ (a ⊔ b) := by
  rw [sdiff_symmDiff, sdiff_sup]

@[simp]
/-
**symmDiff_sdiff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_sdiff_left : a ∆ b \ a = b \ a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_def`：symmDiff_def [Max α] [SDiff α] (a b : α) : a ∆ b = a \ b ⊔
 b \ a
· 使用定理 `sup_sdiff`：sup_sdiff : (a ⊔ b) \ c = a \ c ⊔ b \ c
· 使用定理 `sdiff_idem`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b
 : α}, (a \ b) \ b = a \ b
· 使用定理 `sdiff_sdiff_self`：sdiff_sdiff_self : (a \ b) \ a = ⊥
· 使用定理 `bot_sup_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊔ a = a
-/
theorem symmDiff_sdiff_left : a ∆ b \ a = b \ a := by
  rw [symmDiff_def, sup_sdiff, sdiff_idem, sdiff_sdiff_self, bot_sup_eq]

@[simp]
/-
**symmDiff_sdiff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_sdiff_right : a ∆ b \ b = a \ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_comm`：symmDiff_comm : a ∆ b = b ∆ a
· 使用定理 `symmDiff_sdiff_left`：symmDiff_sdiff_left : a ∆ b \ a = b \ a
-/
theorem symmDiff_sdiff_right : a ∆ b \ b = a \ b := by rw [symmDiff_comm, symmDiff_sdiff_left]

@[simp]
/-
**sdiff_symmDiff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_symmDiff_left : a \ a ∆ b = a ⊓ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_symmDiff`：sdiff_symmDiff : c \ a ∆ b = c ⊓ a ⊓ b ⊔ c \ a ⊓ c \ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a :
 α}, a \ a = ⊥
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sdiff_symmDiff_left : a \ a ∆ b = a ⊓ b := by simp [sdiff_symmDiff]

@[simp]
/-
**sdiff_symmDiff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_symmDiff_right : b \ a ∆ b = a ⊓ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_comm`：symmDiff_comm : a ∆ b = b ∆ a
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `sdiff_symmDiff_left`：sdiff_symmDiff_left : a \ a ∆ b = a ⊓ b
-/
theorem sdiff_symmDiff_right : b \ a ∆ b = a ⊓ b := by
  rw [symmDiff_comm, inf_comm, sdiff_symmDiff_left]
/-
**symmDiff_eq_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_eq_sup : a ∆ b = a ⊔ b ↔ Disjoint a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.of_disjoint_inf_of_le`：Disjoint.of_disjoint_inf_of_le (h : Disj
oint (a ⊓ b) c) (hle : a <= c) : Disjoint a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_eq_self_iff_disjoint`：sdiff_eq_self_iff_disjoint : x \ y = x ↔ Dis
joint y x
· 使用定理 `symmDiff_eq_sup_sdiff_inf`：symmDiff_eq_sup_sdiff_inf : a ∆ b = (a ⊔ b) \
 (a ⊓ b)
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `Disjoint.symmDiff_eq_sup`：Disjoint.symmDiff_eq_sup {a b : α} (h : Disjoi
nt a b) : a ∆ b = a ⊔ b
-/
theorem symmDiff_eq_sup : a ∆ b = a ⊔ b ↔ Disjoint a b := by
  refine ⟨fun h => ?_, Disjoint.symmDiff_eq_sup⟩
  rw [symmDiff_eq_sup_sdiff_inf, sdiff_eq_self_iff_disjoint] at h
  exact h.of_disjoint_inf_of_le le_sup_left

@[simp]
/-
**le_symmDiff_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_symmDiff_iff_left : a <= a ∆ b ↔ Disjoint a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_sdiff_right`：le_sdiff_right : x <= y \ x ↔ x = ⊥
· 使用定理 `inf_le_of_left_le`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c : α},
 a ≤ c → a ⊓ b ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_eq_sup_sdiff_inf`：symmDiff_eq_sup_sdiff_inf : a ∆ b = (a ⊔ b) \
 (a ⊓ b)
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Disjoint.symmDiff_eq_sup`：Disjoint.symmDiff_eq_sup {a b : α} (h : Disjoi
nt a b) : a ∆ b = a ⊔ b
-/
theorem le_symmDiff_iff_left : a ≤ a ∆ b ↔ Disjoint a b := by
  refine ⟨fun h => ?_, fun h => h.symmDiff_eq_sup.symm ▸ le_sup_left⟩
  rw [symmDiff_eq_sup_sdiff_inf] at h
  exact disjoint_iff_inf_le.mpr (le_sdiff_right.1 <| inf_le_of_left_le h).le

@[simp]
/-
**le_symmDiff_iff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_symmDiff_iff_right : b <= a ∆ b ↔ Disjoint a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_comm`：symmDiff_comm : a ∆ b = b ∆ a
· 使用定理 `le_symmDiff_iff_left`：le_symmDiff_iff_left : a <= a ∆ b ↔ Disjoint a b
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_symmDiff_iff_right : b ≤ a ∆ b ↔ Disjoint a b := by
  rw [symmDiff_comm, le_symmDiff_iff_left, disjoint_comm]
/-
**symmDiff_symmDiff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_symmDiff_left : a ∆ b ∆ c = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ c \ (a ⊔ 
b) ⊔ a ⊓ b ⊓ c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symmDiff_def`：symmDiff_def [Max α] [SDiff α] (a b : α) : a ∆ b = a \ b ⊔
 b \ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_symmDiff'`：sdiff_symmDiff' : c \ a ∆ b = c ⊓ a ⊓ b ⊔ c \ (a ⊔ b)
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `symmDiff_sdiff`：symmDiff_sdiff : a ∆ b \ c = a \ (b ⊔ c) ⊔ b \ (a ⊔ c)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Lean.Data.AC.Context.eq_of_norm`：∀ {α : Sort u_1} (ctx : Data.AC.Context
 α) (a b : Data.AC.Expr),   (Data.AC.norm ctx a == Data.AC.norm ctx b) = true → 
Data.AC.eval α ctx a …
· 使用定理 `instAssociativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Associative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instCommutativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Commutative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instIdempotentOpMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], S
td.IdempotentOp fun x1 x2 => x1 ⊔ x2
· 使用定理 `instAssociativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Associative fun x1 x2 => x1 ⊓ x2
· 使用定理 `instCommutativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Commutative fun x1 x2 => x1 ⊓ x2
· 使用定理 `instIdempotentOpMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], S
td.IdempotentOp fun x1 x2 => x1 ⊓ x2
-/
theorem symmDiff_symmDiff_left :
    a ∆ b ∆ c = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ c \ (a ⊔ b) ⊔ a ⊓ b ⊓ c :=
  calc
    a ∆ b ∆ c = a ∆ b \ c ⊔ c \ a ∆ b := symmDiff_def _ _
    _ = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ (c \ (a ⊔ b) ⊔ c ⊓ a ⊓ b) := by
        { rw [sdiff_symmDiff', sup_comm (c ⊓ a ⊓ b), symmDiff_sdiff] }
    _ = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ c \ (a ⊔ b) ⊔ a ⊓ b ⊓ c := by ac_rfl
/-
**symmDiff_symmDiff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_symmDiff_right : a ∆ (b ∆ c) = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ c \ (a
 ⊔ b) ⊔ a ⊓ b ⊓ c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symmDiff_def`：symmDiff_def [Max α] [SDiff α] (a b : α) : a ∆ b = a \ b ⊔
 b \ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_symmDiff'`：sdiff_symmDiff' : c \ a ∆ b = c ⊓ a ⊓ b ⊔ c \ (a ⊔ b)
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `symmDiff_sdiff`：symmDiff_sdiff : a ∆ b \ c = a \ (b ⊔ c) ⊔ b \ (a ⊔ c)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Lean.Data.AC.Context.eq_of_norm`：∀ {α : Sort u_1} (ctx : Data.AC.Context
 α) (a b : Data.AC.Expr),   (Data.AC.norm ctx a == Data.AC.norm ctx b) = true → 
Data.AC.eval α ctx a …
· 使用定理 `instAssociativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Associative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instCommutativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Commutative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instIdempotentOpMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], S
td.IdempotentOp fun x1 x2 => x1 ⊔ x2
· 使用定理 `instAssociativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Associative fun x1 x2 => x1 ⊓ x2
· 使用定理 `instCommutativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Commutative fun x1 x2 => x1 ⊓ x2
· 使用定理 `instIdempotentOpMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], S
td.IdempotentOp fun x1 x2 => x1 ⊓ x2
-/
theorem symmDiff_symmDiff_right :
    a ∆ (b ∆ c) = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ c \ (a ⊔ b) ⊔ a ⊓ b ⊓ c :=
  calc
    a ∆ (b ∆ c) = a \ b ∆ c ⊔ b ∆ c \ a := symmDiff_def _ _
    _ = a \ (b ⊔ c) ⊔ a ⊓ b ⊓ c ⊔ (b \ (c ⊔ a) ⊔ c \ (b ⊔ a)) := by
        { rw [sdiff_symmDiff', sup_comm (a ⊓ b ⊓ c), symmDiff_sdiff] }
    _ = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ c \ (a ⊔ b) ⊔ a ⊓ b ⊓ c := by ac_rfl
/-
**symmDiff_assoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_assoc : a ∆ b ∆ c = a ∆ (b ∆ c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_symmDiff_left`：symmDiff_symmDiff_left : a ∆ b ∆ c = a \ (b ⊔ c)
 ⊔ b \ (a ⊔ c) ⊔ c \ (a ⊔ b) ⊔ a ⊓ b ⊓ c
· 使用定理 `symmDiff_symmDiff_right`：symmDiff_symmDiff_right : a ∆ (b ∆ c) = a \ (b 
⊔ c) ⊔ b \ (a ⊔ c) ⊔ c \ (a ⊔ b) ⊔ a ⊓ b ⊓ c
-/
theorem symmDiff_assoc : a ∆ b ∆ c = a ∆ (b ∆ c) := by
  rw [symmDiff_symmDiff_left, symmDiff_symmDiff_right]
/-
**symmDiff_isAssociative** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：symmDiff_isAssociative : Std.Associative (α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `symmDiff_assoc`：symmDiff_assoc : a ∆ b ∆ c = a ∆ (b ∆ c)
-/
instance symmDiff_isAssociative : Std.Associative (α := α) (· ∆ ·) :=
  ⟨symmDiff_assoc⟩
/-
**symmDiff_left_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_left_comm : a ∆ (b ∆ c) = b ∆ (a ∆ c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `symmDiff_comm`：symmDiff_comm : a ∆ b = b ∆ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem symmDiff_left_comm : a ∆ (b ∆ c) = b ∆ (a ∆ c) := by
  simp_rw [← symmDiff_assoc, symmDiff_comm]
/-
**symmDiff_right_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_right_comm : a ∆ b ∆ c = a ∆ c ∆ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_assoc`：symmDiff_assoc : a ∆ b ∆ c = a ∆ (b ∆ c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `symmDiff_comm`：symmDiff_comm : a ∆ b = b ∆ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem symmDiff_right_comm : a ∆ b ∆ c = a ∆ c ∆ b := by simp_rw [symmDiff_assoc, symmDiff_comm]
/-
**symmDiff_symmDiff_symmDiff_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_symmDiff_symmDiff_comm : a ∆ b ∆ (c ∆ d) = a ∆ c ∆ (b ∆ d)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_assoc`：symmDiff_assoc : a ∆ b ∆ c = a ∆ (b ∆ c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `symmDiff_left_comm`：symmDiff_left_comm : a ∆ (b ∆ c) = b ∆ (a ∆ c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem symmDiff_symmDiff_symmDiff_comm : a ∆ b ∆ (c ∆ d) = a ∆ c ∆ (b ∆ d) := by
  simp_rw [symmDiff_assoc, symmDiff_left_comm]

@[simp]
/-
**symmDiff_symmDiff_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_symmDiff_cancel_left : a ∆ (a ∆ b) = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_self`：symmDiff_self : a ∆ a = ⊥
· 使用定理 `bot_symmDiff`：bot_symmDiff : ⊥ ∆ a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem symmDiff_symmDiff_cancel_left : a ∆ (a ∆ b) = b := by simp [← symmDiff_assoc]

@[simp]
/-
**symmDiff_symmDiff_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_symmDiff_cancel_right : b ∆ a ∆ a = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_assoc`：symmDiff_assoc : a ∆ b ∆ c = a ∆ (b ∆ c)
· 使用定理 `symmDiff_self`：symmDiff_self : a ∆ a = ⊥
· 使用定理 `symmDiff_bot`：symmDiff_bot : a ∆ ⊥ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem symmDiff_symmDiff_cancel_right : b ∆ a ∆ a = b := by simp [symmDiff_assoc]

@[simp]
/-
**symmDiff_symmDiff_self'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_symmDiff_self' : a ∆ b ∆ a = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_comm`：symmDiff_comm : a ∆ b = b ∆ a
· 使用定理 `symmDiff_symmDiff_cancel_left`：symmDiff_symmDiff_cancel_left : a ∆ (a ∆ 
b) = b
-/
theorem symmDiff_symmDiff_self' : a ∆ b ∆ a = b := by
  rw [symmDiff_comm, symmDiff_symmDiff_cancel_left]
/-
**symmDiff_left_involutive** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_left_involutive (a : α) : Involutive (· ∆ a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symmDiff_symmDiff_cancel_right`：symmDiff_symmDiff_cancel_right : b ∆ a ∆
 a = b
-/
theorem symmDiff_left_involutive (a : α) : Involutive (· ∆ a) :=
  symmDiff_symmDiff_cancel_right _
/-
**symmDiff_right_involutive** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_right_involutive (a : α) : Involutive (a ∆ ·)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symmDiff_symmDiff_cancel_left`：symmDiff_symmDiff_cancel_left : a ∆ (a ∆ 
b) = b
-/
theorem symmDiff_right_involutive (a : α) : Involutive (a ∆ ·) :=
  symmDiff_symmDiff_cancel_left _
/-
**symmDiff_left_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_left_injective (a : α) : Injective (· ∆ a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.injective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Injective f
· 使用定理 `symmDiff_left_involutive`：symmDiff_left_involutive (a : α) : Involutive 
(· ∆ a)
-/
theorem symmDiff_left_injective (a : α) : Injective (· ∆ a) :=
  Function.Involutive.injective (symmDiff_left_involutive a)
/-
**symmDiff_right_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_right_injective (a : α) : Injective (a ∆ ·)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.injective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Injective f
· 使用定理 `symmDiff_right_involutive`：symmDiff_right_involutive (a : α) : Involutiv
e (a ∆ ·)
-/
theorem symmDiff_right_injective (a : α) : Injective (a ∆ ·) :=
  Function.Involutive.injective (symmDiff_right_involutive _)
/-
**symmDiff_left_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_left_surjective (a : α) : Surjective (· ∆ a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.surjective`：∀ {α : Sort u} {f : α → α}, Function.Inv
olutive f → Function.Surjective f
· 使用定理 `symmDiff_left_involutive`：symmDiff_left_involutive (a : α) : Involutive 
(· ∆ a)
-/
theorem symmDiff_left_surjective (a : α) : Surjective (· ∆ a) :=
  Function.Involutive.surjective (symmDiff_left_involutive _)
/-
**symmDiff_right_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_right_surjective (a : α) : Surjective (a ∆ ·)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.surjective`：∀ {α : Sort u} {f : α → α}, Function.Inv
olutive f → Function.Surjective f
· 使用定理 `symmDiff_right_involutive`：symmDiff_right_involutive (a : α) : Involutiv
e (a ∆ ·)
-/
theorem symmDiff_right_surjective (a : α) : Surjective (a ∆ ·) :=
  Function.Involutive.surjective (symmDiff_right_involutive _)

variable {a b c}

@[simp]
/-
**symmDiff_left_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_left_inj : a ∆ b = c ∆ b ↔ a = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `symmDiff_left_injective`：symmDiff_left_injective (a : α) : Injective (· 
∆ a)
-/
theorem symmDiff_left_inj : a ∆ b = c ∆ b ↔ a = c :=
  (symmDiff_left_injective _).eq_iff

@[simp]
/-
**symmDiff_right_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_right_inj : a ∆ b = a ∆ c ↔ b = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `symmDiff_right_injective`：symmDiff_right_injective (a : α) : Injective (
a ∆ ·)
-/
theorem symmDiff_right_inj : a ∆ b = a ∆ c ↔ b = c :=
  (symmDiff_right_injective _).eq_iff

@[simp]
/-
**symmDiff_eq_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_eq_left : a ∆ b = a ↔ b = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_bot`：symmDiff_bot : a ∆ ⊥ = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `symmDiff_right_inj`：symmDiff_right_inj : a ∆ b = a ∆ c ↔ b = c
-/
theorem symmDiff_eq_left : a ∆ b = a ↔ b = ⊥ :=
  calc
    a ∆ b = a ↔ a ∆ b = a ∆ ⊥ := by rw [symmDiff_bot]
    _ ↔ b = ⊥ := by rw [symmDiff_right_inj]

@[simp]
/-
**symmDiff_eq_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_eq_right : a ∆ b = b ↔ a = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_comm`：symmDiff_comm : a ∆ b = b ∆ a
· 使用定理 `symmDiff_eq_left`：symmDiff_eq_left : a ∆ b = a ↔ b = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem symmDiff_eq_right : a ∆ b = b ↔ a = ⊥ := by rw [symmDiff_comm, symmDiff_eq_left]
/-
**Disjoint.symmDiff_left** 是 Mathlib 中的一个定理，位于命名空间 `Disjoint`。
形式化陈述：∀ {α : Type u_2} [inst : GeneralizedBooleanAlgebra α] {a b c : α},   Disjo
int a c → Disjoint b c → Disjoint (symmDiff a b) c
参数：symmDiff a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_eq_sup_sdiff_inf`：symmDiff_eq_sup_sdiff_inf : a ∆ b = (a ⊔ b) \
 (a ⊓ b)
· 使用定理 `Disjoint.disjoint_sdiff_left`：Disjoint.disjoint_sdiff_left (h : Disjoint
 a b) : Disjoint (a \ c) b
· 使用定理 `Disjoint.sup_left`：Disjoint.sup_left (ha : Disjoint a c) (hb : Disjoint 
b c) : Disjoint (a ⊔ b) c
-/
protected theorem Disjoint.symmDiff_left (ha : Disjoint a c) (hb : Disjoint b c) :
    Disjoint (a ∆ b) c := by
  rw [symmDiff_eq_sup_sdiff_inf]
  exact (ha.sup_left hb).disjoint_sdiff_left
/-
**Disjoint.symmDiff_right** 是 Mathlib 中的一个定理，位于命名空间 `Disjoint`。
形式化陈述：∀ {α : Type u_2} [inst : GeneralizedBooleanAlgebra α] {a b c : α},   Disjo
int a b → Disjoint a c → Disjoint a (symmDiff b c)
参数：symmDiff b c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Disjoint.symmDiff_left`：∀ {α : Type u_2} [inst : GeneralizedBooleanAlgeb
ra α] {a b c : α},   Disjoint a c → Disjoint b c → Disjoint (symmDiff a b) c
-/
protected theorem Disjoint.symmDiff_right (ha : Disjoint a b) (hb : Disjoint a c) :
    Disjoint a (b ∆ c) :=
  (ha.symm.symmDiff_left hb.symm).symm
/-
**symmDiff_eq_iff_sdiff_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_eq_iff_sdiff_eq (ha : a <= c) : a ∆ b = c ↔ c \ a = b
参数：ha : a <= c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `symmDiff_of_le`：symmDiff_of_le {a b : α} (h : a <= b) : a ∆ b = b \ a
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `symmDiff_right_involutive`：symmDiff_right_involutive (a : α) : Involutiv
e (a ∆ ·)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
theorem symmDiff_eq_iff_sdiff_eq (ha : a ≤ c) : a ∆ b = c ↔ c \ a = b := by
  rw [← symmDiff_of_le ha]
  exact ((symmDiff_right_involutive a).toPerm _).eq_symm_apply.symm.trans eq_comm

end GeneralizedBooleanAlgebra

section BooleanAlgebra

variable [BooleanAlgebra α] (a b c d : α)

/-! `CogeneralizedBooleanAlgebra` isn't actually a typeclass, but the lemmas in here are dual to
the `GeneralizedBooleanAlgebra` ones -/
section CogeneralizedBooleanAlgebra

@[simp]
/-
**inf_himp_bihimp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_himp_bihimp : a ⇔ b ⇨ a ⊓ b = a ⊔ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_sdiff_symmDiff`：sup_sdiff_symmDiff : (a ⊔ b) \ a ∆ b = a ⊓ b
-/
theorem inf_himp_bihimp : a ⇔ b ⇨ a ⊓ b = a ⊔ b :=
  @sup_sdiff_symmDiff αᵒᵈ _ _ _
/-
**codisjoint_bihimp_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：codisjoint_bihimp_sup : Codisjoint (a ⇔ b) (a ⊔ b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_symmDiff_inf`：disjoint_symmDiff_inf : Disjoint (a ∆ b) (a ⊓ b)
-/
theorem codisjoint_bihimp_sup : Codisjoint (a ⇔ b) (a ⊔ b) :=
  @disjoint_symmDiff_inf αᵒᵈ _ _ _

@[simp]
/-
**himp_bihimp_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：himp_bihimp_left : a ⇨ a ⇔ b = a ⇨ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symmDiff_sdiff_left`：symmDiff_sdiff_left : a ∆ b \ a = b \ a
-/
theorem himp_bihimp_left : a ⇨ a ⇔ b = a ⇨ b :=
  @symmDiff_sdiff_left αᵒᵈ _ _ _

@[simp]
/-
**himp_bihimp_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：himp_bihimp_right : b ⇨ a ⇔ b = b ⇨ a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symmDiff_sdiff_right`：symmDiff_sdiff_right : a ∆ b \ b = a \ b
-/
theorem himp_bihimp_right : b ⇨ a ⇔ b = b ⇨ a :=
  @symmDiff_sdiff_right αᵒᵈ _ _ _

@[simp]
/-
**bihimp_himp_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bihimp_himp_left : a ⇔ b ⇨ a = a ⊔ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_symmDiff_left`：sdiff_symmDiff_left : a \ a ∆ b = a ⊓ b
-/
theorem bihimp_himp_left : a ⇔ b ⇨ a = a ⊔ b :=
  @sdiff_symmDiff_left αᵒᵈ _ _ _

@[simp]
/-
**bihimp_himp_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bihimp_himp_right : a ⇔ b ⇨ b = a ⊔ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_symmDiff_right`：sdiff_symmDiff_right : b \ a ∆ b = a ⊓ b
-/
theorem bihimp_himp_right : a ⇔ b ⇨ b = a ⊔ b :=
  @sdiff_symmDiff_right αᵒᵈ _ _ _

@[simp]
/-
**bihimp_eq_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bihimp_eq_inf : a ⇔ b = a ⊓ b ↔ Codisjoint a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symmDiff_eq_sup`：symmDiff_eq_sup : a ∆ b = a ⊔ b ↔ Disjoint a b
-/
theorem bihimp_eq_inf : a ⇔ b = a ⊓ b ↔ Codisjoint a b :=
  @symmDiff_eq_sup αᵒᵈ _ _ _

@[simp]
/-
**bihimp_le_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bihimp_le_iff_left : a ⇔ b <= a ↔ Codisjoint a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_symmDiff_iff_left`：le_symmDiff_iff_left : a <= a ∆ b ↔ Disjoint a b
-/
theorem bihimp_le_iff_left : a ⇔ b ≤ a ↔ Codisjoint a b :=
  @le_symmDiff_iff_left αᵒᵈ _ _ _

@[simp]
/-
**bihimp_le_iff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bihimp_le_iff_right : a ⇔ b <= b ↔ Codisjoint a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_symmDiff_iff_right`：le_symmDiff_iff_right : b <= a ∆ b ↔ Disjoint a b
-/
theorem bihimp_le_iff_right : a ⇔ b ≤ b ↔ Codisjoint a b :=
  @le_symmDiff_iff_right αᵒᵈ _ _ _
/-
**bihimp_assoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bihimp_assoc : a ⇔ b ⇔ c = a ⇔ (b ⇔ c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symmDiff_assoc`：symmDiff_assoc : a ∆ b ∆ c = a ∆ (b ∆ c)
-/
theorem bihimp_assoc : a ⇔ b ⇔ c = a ⇔ (b ⇔ c) :=
  @symmDiff_assoc αᵒᵈ _ _ _ _
/-
**bihimp_isAssociative** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：bihimp_isAssociative : Std.Associative (α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `bihimp_assoc`：bihimp_assoc : a ⇔ b ⇔ c = a ⇔ (b ⇔ c)
-/
instance bihimp_isAssociative : Std.Associative (α := α) (· ⇔ ·) :=
  ⟨bihimp_assoc⟩
/-
**bihimp_left_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bihimp_left_comm : a ⇔ (b ⇔ c) = b ⇔ (a ⇔ c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `bihimp_comm`：∀ {α : Type u_2} [inst : GeneralizedHeytingAlgebra α] (a b 
: α), bihimp a b = bihimp b a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bihimp_left_comm : a ⇔ (b ⇔ c) = b ⇔ (a ⇔ c) := by simp_rw [← bihimp_assoc, bihimp_comm]
/-
**bihimp_right_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bihimp_right_comm : a ⇔ b ⇔ c = a ⇔ c ⇔ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bihimp_assoc`：bihimp_assoc : a ⇔ b ⇔ c = a ⇔ (b ⇔ c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `bihimp_comm`：∀ {α : Type u_2} [inst : GeneralizedHeytingAlgebra α] (a b 
: α), bihimp a b = bihimp b a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bihimp_right_comm : a ⇔ b ⇔ c = a ⇔ c ⇔ b := by simp_rw [bihimp_assoc, bihimp_comm]
/-
**bihimp_bihimp_bihimp_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bihimp_bihimp_bihimp_comm : a ⇔ b ⇔ (c ⇔ d) = a ⇔ c ⇔ (b ⇔ d)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bihimp_assoc`：bihimp_assoc : a ⇔ b ⇔ c = a ⇔ (b ⇔ c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `bihimp_left_comm`：bihimp_left_comm : a ⇔ (b ⇔ c) = b ⇔ (a ⇔ c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bihimp_bihimp_bihimp_comm : a ⇔ b ⇔ (c ⇔ d) = a ⇔ c ⇔ (b ⇔ d) := by
  simp_rw [bihimp_assoc, bihimp_left_comm]

@[simp]
/-
**bihimp_bihimp_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bihimp_bihimp_cancel_left : a ⇔ (a ⇔ b) = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bihimp_self`：∀ {α : Type u_2} [inst : GeneralizedHeytingAlgebra α] (a : 
α), bihimp a a = ⊤
· 使用定理 `top_bihimp`：∀ {α : Type u_2} [inst : GeneralizedHeytingAlgebra α] (a : α
), bihimp ⊤ a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bihimp_bihimp_cancel_left : a ⇔ (a ⇔ b) = b := by simp [← bihimp_assoc]

@[simp]
/-
**bihimp_bihimp_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bihimp_bihimp_cancel_right : b ⇔ a ⇔ a = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bihimp_assoc`：bihimp_assoc : a ⇔ b ⇔ c = a ⇔ (b ⇔ c)
· 使用定理 `bihimp_self`：∀ {α : Type u_2} [inst : GeneralizedHeytingAlgebra α] (a : 
α), bihimp a a = ⊤
· 使用定理 `bihimp_top`：∀ {α : Type u_2} [inst : GeneralizedHeytingAlgebra α] (a : α
), bihimp a ⊤ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bihimp_bihimp_cancel_right : b ⇔ a ⇔ a = b := by simp [bihimp_assoc]

@[simp]
/-
**bihimp_bihimp_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bihimp_bihimp_self : a ⇔ b ⇔ a = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bihimp_comm`：∀ {α : Type u_2} [inst : GeneralizedHeytingAlgebra α] (a b 
: α), bihimp a b = bihimp b a
· 使用定理 `bihimp_bihimp_cancel_left`：bihimp_bihimp_cancel_left : a ⇔ (a ⇔ b) = b
-/
theorem bihimp_bihimp_self : a ⇔ b ⇔ a = b := by rw [bihimp_comm, bihimp_bihimp_cancel_left]
/-
**bihimp_left_involutive** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bihimp_left_involutive (a : α) : Involutive (· ⇔ a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bihimp_bihimp_cancel_right`：bihimp_bihimp_cancel_right : b ⇔ a ⇔ a = b
-/
theorem bihimp_left_involutive (a : α) : Involutive (· ⇔ a) :=
  bihimp_bihimp_cancel_right _
/-
**bihimp_right_involutive** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bihimp_right_involutive (a : α) : Involutive (a ⇔ ·)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bihimp_bihimp_cancel_left`：bihimp_bihimp_cancel_left : a ⇔ (a ⇔ b) = b
-/
theorem bihimp_right_involutive (a : α) : Involutive (a ⇔ ·) :=
  bihimp_bihimp_cancel_left _
/-
**bihimp_left_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bihimp_left_injective (a : α) : Injective (· ⇔ a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symmDiff_left_injective`：symmDiff_left_injective (a : α) : Injective (· 
∆ a)
-/
theorem bihimp_left_injective (a : α) : Injective (· ⇔ a) :=
  @symmDiff_left_injective αᵒᵈ _ _
/-
**bihimp_right_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bihimp_right_injective (a : α) : Injective (a ⇔ ·)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symmDiff_right_injective`：symmDiff_right_injective (a : α) : Injective (
a ∆ ·)
-/
theorem bihimp_right_injective (a : α) : Injective (a ⇔ ·) :=
  @symmDiff_right_injective αᵒᵈ _ _
/-
**bihimp_left_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bihimp_left_surjective (a : α) : Surjective (· ⇔ a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symmDiff_left_surjective`：symmDiff_left_surjective (a : α) : Surjective 
(· ∆ a)
-/
theorem bihimp_left_surjective (a : α) : Surjective (· ⇔ a) :=
  @symmDiff_left_surjective αᵒᵈ _ _
/-
**bihimp_right_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bihimp_right_surjective (a : α) : Surjective (a ⇔ ·)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symmDiff_right_surjective`：symmDiff_right_surjective (a : α) : Surjectiv
e (a ∆ ·)
-/
theorem bihimp_right_surjective (a : α) : Surjective (a ⇔ ·) :=
  @symmDiff_right_surjective αᵒᵈ _ _

variable {a b c}

@[simp]
/-
**bihimp_left_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bihimp_left_inj : a ⇔ b = c ⇔ b ↔ a = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `bihimp_left_injective`：bihimp_left_injective (a : α) : Injective (· ⇔ a)
-/
theorem bihimp_left_inj : a ⇔ b = c ⇔ b ↔ a = c :=
  (bihimp_left_injective _).eq_iff

@[simp]
/-
**bihimp_right_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bihimp_right_inj : a ⇔ b = a ⇔ c ↔ b = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `bihimp_right_injective`：bihimp_right_injective (a : α) : Injective (a ⇔ 
·)
-/
theorem bihimp_right_inj : a ⇔ b = a ⇔ c ↔ b = c :=
  (bihimp_right_injective _).eq_iff

@[simp]
/-
**bihimp_eq_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bihimp_eq_left : a ⇔ b = a ↔ b = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symmDiff_eq_left`：symmDiff_eq_left : a ∆ b = a ↔ b = ⊥
-/
theorem bihimp_eq_left : a ⇔ b = a ↔ b = ⊤ :=
  @symmDiff_eq_left αᵒᵈ _ _ _

@[simp]
/-
**bihimp_eq_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bihimp_eq_right : a ⇔ b = b ↔ a = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symmDiff_eq_right`：symmDiff_eq_right : a ∆ b = b ↔ a = ⊥
-/
theorem bihimp_eq_right : a ⇔ b = b ↔ a = ⊤ :=
  @symmDiff_eq_right αᵒᵈ _ _ _
/-
**Codisjoint.bihimp_left** 是 Mathlib 中的一个定理，位于命名空间 `Codisjoint`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {a b c : α}, Codisjoint a c → C
odisjoint b c → Codisjoint (bihimp a b) c
参数：bihimp a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Codisjoint.mono_left`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 :
 OrderTop α] {a b c : α}, b ≤ a → Codisjoint b c → Codisjoint a c
· 使用定理 `inf_le_bihimp`：∀ {α : Type u_2} [inst : GeneralizedHeytingAlgebra α] {a 
b : α}, a ⊓ b ≤ bihimp a b
· 使用定理 `Codisjoint.inf_left`：Codisjoint.inf_left (ha : Codisjoint a c) (hb : Cod
isjoint b c) : Codisjoint (a ⊓ b) c
-/
protected theorem Codisjoint.bihimp_left (ha : Codisjoint a c) (hb : Codisjoint b c) :
    Codisjoint (a ⇔ b) c :=
  (ha.inf_left hb).mono_left inf_le_bihimp
/-
**Codisjoint.bihimp_right** 是 Mathlib 中的一个定理，位于命名空间 `Codisjoint`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {a b c : α}, Codisjoint a b → C
odisjoint a c → Codisjoint a (bihimp b c)
参数：bihimp b c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Codisjoint.mono_right`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 
: OrderTop α] {a b c : α}, c ≤ b → Codisjoint a c → Codisjoint a b
· 使用定理 `inf_le_bihimp`：∀ {α : Type u_2} [inst : GeneralizedHeytingAlgebra α] {a 
b : α}, a ⊓ b ≤ bihimp a b
· 使用定理 `Codisjoint.inf_right`：Codisjoint.inf_right (hb : Codisjoint a b) (hc : C
odisjoint a c) : Codisjoint a (b ⊓ c)
-/
protected theorem Codisjoint.bihimp_right (ha : Codisjoint a b) (hb : Codisjoint a c) :
    Codisjoint a (b ⇔ c) :=
  (ha.inf_right hb).mono_right inf_le_bihimp

end CogeneralizedBooleanAlgebra

/-
**symmDiff_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_eq : a ∆ b = a ⊓ bᶜ ⊔ b ⊓ aᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sdiff_eq`：sdiff_eq : x \ y = x ⊓ yᶜ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem symmDiff_eq : a ∆ b = a ⊓ bᶜ ⊔ b ⊓ aᶜ := by simp only [(· ∆ ·), sdiff_eq]
/-
**bihimp_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bihimp_eq : a ⇔ b = (a ⊔ bᶜ) ⊓ (b ⊔ aᶜ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `himp_eq`：himp_eq : x ⇨ y = y ⊔ xᶜ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bihimp_eq : a ⇔ b = (a ⊔ bᶜ) ⊓ (b ⊔ aᶜ) := by simp only [(· ⇔ ·), himp_eq]
/-
**symmDiff_eq'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_eq' : a ∆ b = (a ⊔ b) ⊓ (aᶜ ⊔ bᶜ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_eq_sup_sdiff_inf`：symmDiff_eq_sup_sdiff_inf : a ∆ b = (a ⊔ b) \
 (a ⊓ b)
· 使用定理 `sdiff_eq`：sdiff_eq : x \ y = x ⊓ yᶜ
· 使用定理 `compl_inf`：compl_inf : (x ⊓ y)ᶜ = xᶜ ⊔ yᶜ
-/
theorem symmDiff_eq' : a ∆ b = (a ⊔ b) ⊓ (aᶜ ⊔ bᶜ) := by
  rw [symmDiff_eq_sup_sdiff_inf, sdiff_eq, compl_inf]
/-
**bihimp_eq'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bihimp_eq' : a ⇔ b = a ⊓ b ⊔ aᶜ ⊓ bᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symmDiff_eq'`：symmDiff_eq' : a ∆ b = (a ⊔ b) ⊓ (aᶜ ⊔ bᶜ)
-/
theorem bihimp_eq' : a ⇔ b = a ⊓ b ⊔ aᶜ ⊓ bᶜ :=
  @symmDiff_eq' αᵒᵈ _ _ _

@[simp]
/-
**compl_symmDiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_symmDiff : (a ∆ b)ᶜ = a ⇔ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_sup_distrib`：compl_sup_distrib (a b : α) : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `compl_sdiff`：compl_sdiff : (x \ y)ᶜ = x ⇨ y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem compl_symmDiff : (a ∆ b)ᶜ = a ⇔ b := by
  simp_rw [symmDiff, compl_sup_distrib, compl_sdiff, bihimp, inf_comm]

@[simp]
/-
**compl_bihimp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_bihimp : (a ⇔ b)ᶜ = a ∆ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_symmDiff`：compl_symmDiff : (a ∆ b)ᶜ = a ⇔ b
-/
theorem compl_bihimp : (a ⇔ b)ᶜ = a ∆ b :=
  @compl_symmDiff αᵒᵈ _ _ _

@[simp]
/-
**compl_symmDiff_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_symmDiff_compl : aᶜ ∆ bᶜ = a ∆ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `compl_sdiff_compl`：compl_sdiff_compl : xᶜ \ yᶜ = y \ x
· 使用定理 `sdiff_eq`：sdiff_eq : x \ y = x ⊓ yᶜ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `symmDiff_eq`：symmDiff_eq : a ∆ b = a ⊓ bᶜ ⊔ b ⊓ aᶜ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem compl_symmDiff_compl : aᶜ ∆ bᶜ = a ∆ b :=
  (sup_comm _ _).trans <| by simp_rw [compl_sdiff_compl, sdiff_eq, symmDiff_eq]

@[simp]
/-
**compl_bihimp_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_bihimp_compl : aᶜ ⇔ bᶜ = a ⇔ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_symmDiff_compl`：compl_symmDiff_compl : aᶜ ∆ bᶜ = a ∆ b
-/
theorem compl_bihimp_compl : aᶜ ⇔ bᶜ = a ⇔ b :=
  @compl_symmDiff_compl αᵒᵈ _ _ _

@[simp]
/-
**symmDiff_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_eq_top : a ∆ b = ⊤ ↔ IsCompl a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_eq'`：symmDiff_eq' : a ∆ b = (a ⊔ b) ⊓ (aᶜ ⊔ bᶜ)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compl_inf`：compl_inf : (x ⊓ y)ᶜ = xᶜ ⊔ yᶜ
· 使用定理 `inf_eq_top_iff`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : Ord
erTop α] {a b : α}, a ⊓ b = ⊤ ↔ a = ⊤ ∧ b = ⊤
· 使用定理 `compl_eq_top`：compl_eq_top : xᶜ = ⊤ ↔ x = ⊥
· 使用定理 `isCompl_iff`：isCompl_iff [PartialOrder α] [BoundedOrder α] {a b : α} : I
sCompl a b ↔ Disjoint a b ∧ Codisjoint a b
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `codisjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : Ord
erTop α] {a b : α}, Codisjoint a b ↔ a ⊔ b = ⊤
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem symmDiff_eq_top : a ∆ b = ⊤ ↔ IsCompl a b := by
  rw [symmDiff_eq', ← compl_inf, inf_eq_top_iff, compl_eq_top, isCompl_iff, disjoint_iff,
    codisjoint_iff, and_comm]

@[simp]
/-
**bihimp_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bihimp_eq_bot : a ⇔ b = ⊥ ↔ IsCompl a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bihimp_eq'`：bihimp_eq' : a ⇔ b = a ⊓ b ⊔ aᶜ ⊓ bᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compl_sup`：compl_sup : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ
· 使用定理 `sup_eq_bot_iff`：sup_eq_bot_iff : a ⊔ b = ⊥ ↔ a = ⊥ ∧ b = ⊥
· 使用定理 `compl_eq_bot`：compl_eq_bot : xᶜ = ⊥ ↔ x = ⊤
· 使用定理 `isCompl_iff`：isCompl_iff [PartialOrder α] [BoundedOrder α] {a b : α} : I
sCompl a b ↔ Disjoint a b ∧ Codisjoint a b
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `codisjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : Ord
erTop α] {a b : α}, Codisjoint a b ↔ a ⊔ b = ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem bihimp_eq_bot : a ⇔ b = ⊥ ↔ IsCompl a b := by
  rw [bihimp_eq', ← compl_sup, sup_eq_bot_iff, compl_eq_bot, isCompl_iff, disjoint_iff,
    codisjoint_iff]

@[simp]
/-
**compl_symmDiff_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_symmDiff_self : aᶜ ∆ a = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hnot_symmDiff_self`：hnot_symmDiff_self : (￢a) ∆ a = ⊤
-/
theorem compl_symmDiff_self : aᶜ ∆ a = ⊤ :=
  hnot_symmDiff_self _

@[simp]
/-
**symmDiff_compl_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_compl_self : a ∆ aᶜ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symmDiff_hnot_self`：symmDiff_hnot_self : a ∆ (￢a) = ⊤
-/
theorem symmDiff_compl_self : a ∆ aᶜ = ⊤ :=
  symmDiff_hnot_self _
/-
**symmDiff_symmDiff_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_symmDiff_right' : a ∆ (b ∆ c) = a ⊓ b ⊓ c ⊔ a ⊓ bᶜ ⊓ cᶜ ⊔ aᶜ ⊓ b 
⊓ cᶜ ⊔ aᶜ ⊓ bᶜ ⊓ c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_eq`：symmDiff_eq : a ∆ b = a ⊓ bᶜ ⊔ b ⊓ aᶜ
· 使用定理 `compl_symmDiff`：compl_symmDiff : (a ∆ b)ᶜ = a ⇔ b
· 使用定理 `bihimp_eq'`：bihimp_eq' : a ⇔ b = a ⊓ b ⊔ aᶜ ⊓ bᶜ
· 使用定理 `inf_sup_left`：inf_sup_left (a b c : α) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c
· 使用定理 `inf_sup_right`：inf_sup_right (a b c : α) : (a ⊔ b) ⊓ c = a ⊓ c ⊔ b ⊓ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_assoc`：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `inf_left_right_swap`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α
), a ⊓ b ⊓ c = c ⊓ b ⊓ a
-/
theorem symmDiff_symmDiff_right' :
    a ∆ (b ∆ c) = a ⊓ b ⊓ c ⊔ a ⊓ bᶜ ⊓ cᶜ ⊔ aᶜ ⊓ b ⊓ cᶜ ⊔ aᶜ ⊓ bᶜ ⊓ c :=
  calc
    a ∆ (b ∆ c) = a ⊓ (b ⊓ c ⊔ bᶜ ⊓ cᶜ) ⊔ (b ⊓ cᶜ ⊔ c ⊓ bᶜ) ⊓ aᶜ := by
        { rw [symmDiff_eq, compl_symmDiff, bihimp_eq', symmDiff_eq] }
    _ = a ⊓ b ⊓ c ⊔ a ⊓ bᶜ ⊓ cᶜ ⊔ b ⊓ cᶜ ⊓ aᶜ ⊔ c ⊓ bᶜ ⊓ aᶜ := by
        { rw [inf_sup_left, inf_sup_right, ← sup_assoc, ← inf_assoc, ← inf_assoc] }
    _ = a ⊓ b ⊓ c ⊔ a ⊓ bᶜ ⊓ cᶜ ⊔ aᶜ ⊓ b ⊓ cᶜ ⊔ aᶜ ⊓ bᶜ ⊓ c := (by
      congr 1
      · congr 1
        rw [inf_comm, inf_assoc]
      · apply inf_left_right_swap)

variable {a b c}
/-
**Disjoint.le_symmDiff_sup_symmDiff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.le_symmDiff_sup_symmDiff_left (h : Disjoint a b) : c <= a ∆ c ⊔ b
 ∆ c
参数：h : Disjoint a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `sdiff_bot`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a : 
α}, a \ ⊥ = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `sdiff_inf`：sdiff_inf : a \ (b ⊓ c) = a \ b ⊔ a \ c
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem Disjoint.le_symmDiff_sup_symmDiff_left (h : Disjoint a b) : c ≤ a ∆ c ⊔ b ∆ c := by
  trans c \ (a ⊓ b)
  · rw [h.eq_bot, sdiff_bot]
  · rw [sdiff_inf]
    exact sup_le_sup le_sup_right le_sup_right
/-
**Disjoint.le_symmDiff_sup_symmDiff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.le_symmDiff_sup_symmDiff_right (h : Disjoint b c) : a <= a ∆ b ⊔ 
a ∆ c
参数：h : Disjoint b c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `symmDiff_comm`：symmDiff_comm : a ∆ b = b ∆ a
· 使用定理 `Disjoint.le_symmDiff_sup_symmDiff_left`：Disjoint.le_symmDiff_sup_symmDif
f_left (h : Disjoint a b) : c <= a ∆ c ⊔ b ∆ c
-/
theorem Disjoint.le_symmDiff_sup_symmDiff_right (h : Disjoint b c) : a ≤ a ∆ b ⊔ a ∆ c := by
  simp_rw [symmDiff_comm a]
  exact h.le_symmDiff_sup_symmDiff_left
/-
**Codisjoint.bihimp_inf_bihimp_le_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Codisjoint.bihimp_inf_bihimp_le_left (h : Codisjoint a b) : a ⇔ c ⊓ b ⇔ c 
<= c
参数：h : Codisjoint a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.le_symmDiff_sup_symmDiff_left`：Disjoint.le_symmDiff_sup_symmDif
f_left (h : Disjoint a b) : c <= a ∆ c ⊔ b ∆ c
· 使用定理 `Codisjoint.dual`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Orde
rTop α] {a b : α},   Codisjoint a b → Disjoint (OrderDual.toDual a) (OrderDual.t
oDual…
-/
theorem Codisjoint.bihimp_inf_bihimp_le_left (h : Codisjoint a b) : a ⇔ c ⊓ b ⇔ c ≤ c :=
  h.dual.le_symmDiff_sup_symmDiff_left
/-
**Codisjoint.bihimp_inf_bihimp_le_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Codisjoint.bihimp_inf_bihimp_le_right (h : Codisjoint b c) : a ⇔ b ⊓ a ⇔ c
 <= a
参数：h : Codisjoint b c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.le_symmDiff_sup_symmDiff_right`：Disjoint.le_symmDiff_sup_symmDi
ff_right (h : Disjoint b c) : a <= a ∆ b ⊔ a ∆ c
· 使用定理 `Codisjoint.dual`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Orde
rTop α] {a b : α},   Codisjoint a b → Disjoint (OrderDual.toDual a) (OrderDual.t
oDual…
-/
theorem Codisjoint.bihimp_inf_bihimp_le_right (h : Codisjoint b c) : a ⇔ b ⊓ a ⇔ c ≤ a :=
  h.dual.le_symmDiff_sup_symmDiff_right

end BooleanAlgebra

/-! ### Prod -/


section Prod

@[to_dual (attr := simp)]
/-
**symmDiff_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_fst [GeneralizedCoheytingAlgebra α] [GeneralizedCoheytingAlgebra 
β] (a b : α × β) : (a ∆ b).1 = a.1 ∆ b.1
参数：a b : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symmDiff_fst [GeneralizedCoheytingAlgebra α] [GeneralizedCoheytingAlgebra β]
    (a b : α × β) : (a ∆ b).1 = a.1 ∆ b.1 :=
  rfl

@[to_dual (attr := simp)]
/-
**symmDiff_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmDiff_snd [GeneralizedCoheytingAlgebra α] [GeneralizedCoheytingAlgebra 
β] (a b : α × β) : (a ∆ b).2 = a.2 ∆ b.2
参数：a b : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symmDiff_snd [GeneralizedCoheytingAlgebra α] [GeneralizedCoheytingAlgebra β]
    (a b : α × β) : (a ∆ b).2 = a.2 ∆ b.2 :=
  rfl

end Prod

/-! ### Pi -/


namespace Pi

@[to_dual (attr := push ←)]
/-
**Pi.symmDiff_def** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：symmDiff_def [forall i, GeneralizedCoheytingAlgebra (π i)] (a b : forall i
, π i) : a ∆ b = fun i => a i ∆ b i
参数：π i；a b : forall i, π i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symmDiff_def [∀ i, GeneralizedCoheytingAlgebra (π i)] (a b : ∀ i, π i) :
    a ∆ b = fun i => a i ∆ b i :=
  rfl

@[to_dual (attr := simp)]
/-
**Pi.symmDiff_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：symmDiff_apply [forall i, GeneralizedCoheytingAlgebra (π i)] (a b : forall
 i, π i) (i : ι) : (a ∆ b) i = a i ∆ b i
参数：π i；a b : forall i, π i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symmDiff_apply [∀ i, GeneralizedCoheytingAlgebra (π i)] (a b : ∀ i, π i) (i : ι) :
    (a ∆ b) i = a i ∆ b i :=
  rfl

end Pi

