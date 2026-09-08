/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.SetTheory.Cardinal.Finite

/-!

# Cardinality of finite types

The cardinality of a finite type `α` is given by `Nat.card α`. This function has
the "junk value" of `0` for infinite types, but to ensure the function has valid
output, one just needs to know that it's possible to produce a `Finite` instance
for the type. (Note: we could have defined a `Finite.card` that required you to
supply a `Finite` instance, but (a) the function would be `noncomputable` anyway
so there is no need to supply the instance and (b) the function would have a more
complicated dependent type that easily leads to "motive not type correct" errors.)

## Implementation notes

Theorems about `Nat.card` are sometimes incidentally true for both finite and infinite
types. If removing a finiteness constraint results in no loss in legibility, we remove
it. We generally put such theorems into the `SetTheory.Cardinal.Finite` module.

-/

@[expose] public section

assert_not_exists Field

noncomputable section

variable {α β γ : Type*}

/-- There is (noncomputably) an equivalence between a finite type `α` and `Fin (Nat.card α)`. -/
/-
**Finite.equivFin** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Finite.equivFin (α : Type*) [Finite α] : α ≃ Fin (Nat.card α)
参数：α : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.exists_equiv_fin`：Finite.exists_equiv_fin (α : Sort*) [h : Finite
 α] : exists n : Nat, Nonempty (α ≃ Fin n)

--- 原说明 ---
There is (noncomputably) an equivalence between a finite type `α` and `Fin (Nat.
card α)`.
-/
def Finite.equivFin (α : Type*) [Finite α] : α ≃ Fin (Nat.card α) := by
  have := (Finite.exists_equiv_fin α).choose_spec.some
  rwa [Nat.card_eq_of_equiv_fin this]

/-- Similar to `Finite.equivFin` but with control over the term used for the cardinality. -/
/-
**Finite.equivFinOfCardEq** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Finite.equivFinOfCardEq [Finite α] {n : Nat} (h : Nat.card α = n) : α ≃ Fi
n n
参数：h : Nat.card α = n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Similar to `Finite.equivFin` but with control over the term used for the cardina
lity.
-/
def Finite.equivFinOfCardEq [Finite α] {n : ℕ} (h : Nat.card α = n) : α ≃ Fin n := by
  subst h
  apply Finite.equivFin

open scoped Classical in
/-
**Nat.card_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.card_eq (α : Type*) : Nat.card α = if _ : Finite α then @Fintype.card 
α (Fintype.ofFinite α) else 0
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_finite_iff_infinite`：not_finite_iff_infinite : ¬Finite α ↔ Infinite 
α
-/
theorem Nat.card_eq (α : Type*) :
    Nat.card α = if _ : Finite α then @Fintype.card α (Fintype.ofFinite α) else 0 := by
  cases finite_or_infinite α
  · let := Fintype.ofFinite α
    simp only [this, *, Nat.card_eq_fintype_card, dif_pos]
  · simp only [*, card_eq_zero_of_infinite, not_finite_iff_infinite.mpr, dite_false]
/-
**Finite.card_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finite.card_pos_iff [Finite α] : 0 < Nat.card α ↔ Nonempty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_pos_iff`：card_pos_iff : 0 < card α ↔ Nonempty α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Finite.card_pos_iff [Finite α] : 0 < Nat.card α ↔ Nonempty α := by
  have := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Fintype.card_pos_iff]
/-
**Finite.card_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finite.card_pos [Finite α] [h : Nonempty α] : 0 < Nat.card α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finite.card_pos_iff`：Finite.card_pos_iff [Finite α] : 0 < Nat.card α ↔ N
onempty α
-/
theorem Finite.card_pos [Finite α] [h : Nonempty α] : 0 < Nat.card α :=
  Finite.card_pos_iff.mpr h

namespace Finite

/-
**Finite.card_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finite`。
形式化陈述：card_eq [Finite α] [Finite β] : Nat.card α = Nat.card β ↔ Nonempty (α ≃ β)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem card_eq [Finite α] [Finite β] : Nat.card α = Nat.card β ↔ Nonempty (α ≃ β) := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  simp only [Nat.card_eq_fintype_card, Fintype.card_eq]
/-
**Finite.card_le_one_iff_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Finite`。
形式化陈述：card_le_one_iff_subsingleton [Finite α] : Nat.card α <= 1 ↔ Subsingleton α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem card_le_one_iff_subsingleton [Finite α] : Nat.card α ≤ 1 ↔ Subsingleton α := by
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.card_le_one_iff_subsingleton]
/-
**Finite.one_lt_card_iff_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Finite`。
形式化陈述：one_lt_card_iff_nontrivial [Finite α] : 1 < Nat.card α ↔ Nontrivial α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem one_lt_card_iff_nontrivial [Finite α] : 1 < Nat.card α ↔ Nontrivial α := by
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.one_lt_card_iff_nontrivial]
/-
**Finite.one_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `Finite`。
形式化陈述：one_lt_card [Finite α] [h : Nontrivial α] : 1 < Nat.card α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finite.one_lt_card_iff_nontrivial`：one_lt_card_iff_nontrivial [Finite α]
 : 1 < Nat.card α ↔ Nontrivial α
-/
theorem one_lt_card [Finite α] [h : Nontrivial α] : 1 < Nat.card α :=
  one_lt_card_iff_nontrivial.mpr h

@[simp]
/-
**Finite.card_option** 是 Mathlib 中的一个定理，位于命名空间 `Finite`。
形式化陈述：card_option [Finite α] : Nat.card (Option α) = Nat.card α + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_option`：Fintype.card_option {α : Type*} [Fintype α] : Finty
pe.card (Option α) = Fintype.card α + 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_option [Finite α] : Nat.card (Option α) = Nat.card α + 1 := by
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.card_option]
/-
**Finite.card_le_of_embedding** 是 Mathlib 中的一个定理，位于命名空间 `Finite`。
形式化陈述：card_le_of_embedding [Finite β] (f : α ↪ β) : Nat.card α <= Nat.card β
参数：f : α ↪ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.card_le_card_of_injective`：card_le_card_of_injective {α : Type u} {β
 : Type v} [Finite β] (f : α -> β) (hf : Injective f) : Nat.card α <= Nat.card β
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
-/
theorem card_le_of_embedding [Finite β] (f : α ↪ β) : Nat.card α ≤ Nat.card β :=
  Nat.card_le_card_of_injective _ f.injective
/-
**Finite.card_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finite`。
形式化陈述：card_eq_zero_iff [Finite α] : Nat.card α = 0 ↔ IsEmpty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem card_eq_zero_iff [Finite α] : Nat.card α = 0 ↔ IsEmpty α := by
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]

/-- If `f` is injective, then `Nat.card α ≤ Nat.card β`. We must also assume
  `Nat.card β = 0 → Nat.card α = 0` since `Nat.card` is defined to be `0` for infinite types. -/
/-
**Finite.card_le_of_injective'** 是 Mathlib 中的一个定理，位于命名空间 `Finite`。
形式化陈述：card_le_of_injective' {f : α -> β} (hf : Function.Injective f) (h : Nat.ca
rd β = 0 -> Nat.card α = 0) : Nat.card α <= Nat.card β
参数：hf : Function.Injective f；h : Nat.card β = 0 -> Nat.card α = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `or_not_of_imp`：or_not_of_imp : (a -> b) -> b ∨ ¬a
· 使用定理 `le_of_eq_of_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ 
c → a ≤ c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用引理 `Nat.card_le_card_of_injective`：card_le_card_of_injective {α : Type u} {β
 : Type v} [Finite β] (f : α -> β) (hf : Injective f) : Nat.card α <= Nat.card β
· 使用定理 `Nat.finite_of_card_ne_zero`：finite_of_card_ne_zero (h : Nat.card α != 0)
 : Finite α

--- 原说明 ---
If `f` is injective, then `Nat.card α ≤ Nat.card β`. We must also assume
  `Nat.card β = 0 → Nat.card α = 0` since `Nat.card` is defined to be `0` for in
finite types.
-/
theorem card_le_of_injective' {f : α → β} (hf : Function.Injective f)
    (h : Nat.card β = 0 → Nat.card α = 0) : Nat.card α ≤ Nat.card β :=
  (or_not_of_imp h).casesOn (fun h => le_of_eq_of_le h (Nat.zero_le _)) fun h =>
    @Nat.card_le_card_of_injective α β (Nat.finite_of_card_ne_zero h) f hf

/-- If `f` is an embedding, then `Nat.card α ≤ Nat.card β`. We must also assume
  `Nat.card β = 0 → Nat.card α = 0` since `Nat.card` is defined to be `0` for infinite types. -/
/-
**Finite.card_le_of_embedding'** 是 Mathlib 中的一个定理，位于命名空间 `Finite`。
形式化陈述：card_le_of_embedding' (f : α ↪ β) (h : Nat.card β = 0 -> Nat.card α = 0) :
 Nat.card α <= Nat.card β
参数：f : α ↪ β；h : Nat.card β = 0 -> Nat.card α = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.card_le_of_injective'`：card_le_of_injective' {f : α -> β} (hf : F
unction.Injective f) (h : Nat.card β = 0 -> Nat.card α = 0) : Nat.card α <= Nat.
card β
· 使用定理 `Function.Embedding.inj'`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ↪ β),
 Function.Injective self.toFun

--- 原说明 ---
If `f` is an embedding, then `Nat.card α ≤ Nat.card β`. We must also assume
  `Nat.card β = 0 → Nat.card α = 0` since `Nat.card` is defined to be `0` for in
finite types.
-/
theorem card_le_of_embedding' (f : α ↪ β) (h : Nat.card β = 0 → Nat.card α = 0) :
    Nat.card α ≤ Nat.card β :=
  card_le_of_injective' f.2 h

/-- If `f` is surjective, then `Nat.card β ≤ Nat.card α`. We must also assume
  `Nat.card α = 0 → Nat.card β = 0` since `Nat.card` is defined to be `0` for infinite types. -/
/-
**Finite.card_le_of_surjective'** 是 Mathlib 中的一个定理，位于命名空间 `Finite`。
形式化陈述：card_le_of_surjective' {f : α -> β} (hf : Function.Surjective f) (h : Nat.
card α = 0 -> Nat.card β = 0) : Nat.card β <= Nat.card α
参数：hf : Function.Surjective f；h : Nat.card α = 0 -> Nat.card β = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `or_not_of_imp`：or_not_of_imp : (a -> b) -> b ∨ ¬a
· 使用定理 `le_of_eq_of_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ 
c → a ≤ c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用引理 `Nat.card_le_card_of_surjective`：card_le_card_of_surjective {α : Type u} 
{β : Type v} [Finite α] (f : α -> β) (hf : Surjective f) : Nat.card β <= Nat.car
d α
· 使用定理 `Nat.finite_of_card_ne_zero`：finite_of_card_ne_zero (h : Nat.card α != 0)
 : Finite α

--- 原说明 ---
If `f` is surjective, then `Nat.card β ≤ Nat.card α`. We must also assume
  `Nat.card α = 0 → Nat.card β = 0` since `Nat.card` is defined to be `0` for in
finite types.
-/
theorem card_le_of_surjective' {f : α → β} (hf : Function.Surjective f)
    (h : Nat.card α = 0 → Nat.card β = 0) : Nat.card β ≤ Nat.card α :=
  (or_not_of_imp h).casesOn (fun h => le_of_eq_of_le h (Nat.zero_le _)) fun h =>
    @Nat.card_le_card_of_surjective α β (Nat.finite_of_card_ne_zero h) f hf

/-- NB: `Nat.card` is defined to be `0` for infinite types. -/
/-
**Finite.card_eq_zero_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Finite`。
形式化陈述：card_eq_zero_of_surjective {f : α -> β} (hf : Function.Surjective f) (h : 
Nat.card β = 0) : Nat.card α = 0
参数：hf : Function.Surjective f；h : Nat.card β = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finite.card_eq_zero_iff`：card_eq_zero_iff [Finite α] : Nat.card α = 0 ↔ 
IsEmpty α
· 使用定理 `Function.isEmpty`：∀ {α : Sort u} {β : Sort v} [IsEmpty β] (f : α → β), I
sEmpty α
· 使用定理 `Nat.card_of_isEmpty`：∀ {α : Type u_1} [IsEmpty α], Nat.card α = 0
· 使用定理 `Infinite.of_surjective`：of_surjective {α β} [Infinite β] (f : α -> β) (h
f : Surjective f) : Infinite α
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0

--- 原说明 ---
NB: `Nat.card` is defined to be `0` for infinite types.
-/
theorem card_eq_zero_of_surjective {f : α → β} (hf : Function.Surjective f) (h : Nat.card β = 0) :
    Nat.card α = 0 := by
  cases finite_or_infinite β
  · have := card_eq_zero_iff.mp h
    have := Function.isEmpty f
    exact Nat.card_of_isEmpty
  · have := Infinite.of_surjective f hf
    exact Nat.card_eq_zero_of_infinite

/-- NB: `Nat.card` is defined to be `0` for infinite types. -/
/-
**Finite.card_eq_zero_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Finite`。
形式化陈述：card_eq_zero_of_injective [Nonempty α] {f : α -> β} (hf : Function.Injecti
ve f) (h : Nat.card α = 0) : Nat.card β = 0
参数：hf : Function.Injective f；h : Nat.card α = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.card_eq_zero_of_surjective`：card_eq_zero_of_surjective {f : α -> 
β} (hf : Function.Surjective f) (h : Nat.card β = 0) : Nat.card α = 0
· 使用定理 `Function.invFun_surjective`：invFun_surjective (hf : Injective f) : Surje
ctive (invFun f)

--- 原说明 ---
NB: `Nat.card` is defined to be `0` for infinite types.
-/
theorem card_eq_zero_of_injective [Nonempty α] {f : α → β} (hf : Function.Injective f)
    (h : Nat.card α = 0) : Nat.card β = 0 :=
  card_eq_zero_of_surjective (Function.invFun_surjective hf) h

/-- NB: `Nat.card` is defined to be `0` for infinite types. -/
/-
**Finite.card_eq_zero_of_embedding** 是 Mathlib 中的一个定理，位于命名空间 `Finite`。
形式化陈述：card_eq_zero_of_embedding [Nonempty α] (f : α ↪ β) (h : Nat.card α = 0) : 
Nat.card β = 0
参数：f : α ↪ β；h : Nat.card α = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.card_eq_zero_of_injective`：card_eq_zero_of_injective [Nonempty α]
 {f : α -> β} (hf : Function.Injective f) (h : Nat.card α = 0) : Nat.card β = 0
· 使用定理 `Function.Embedding.inj'`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ↪ β),
 Function.Injective self.toFun

--- 原说明 ---
NB: `Nat.card` is defined to be `0` for infinite types.
-/
theorem card_eq_zero_of_embedding [Nonempty α] (f : α ↪ β) (h : Nat.card α = 0) : Nat.card β = 0 :=
  card_eq_zero_of_injective f.2 h
/-
**Finite.card_image_le** 是 Mathlib 中的一个定理，位于命名空间 `Finite`。
形式化陈述：card_image_le {s : Set α} [Finite s] (f : α -> β) : Nat.card (f '' s) <= N
at.card s
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.card_le_card_of_surjective`：card_le_card_of_surjective {α : Type u} 
{β : Type v} [Finite α] (f : α -> β) (hf : Surjective f) : Nat.card β <= Nat.car
d α
· 使用定理 `Set.imageFactorization_surjective`：imageFactorization_surjective {f : α 
-> β} {s : Set α} : Surjective (imageFactorization f s)
-/
theorem card_image_le {s : Set α} [Finite s] (f : α → β) : Nat.card (f '' s) ≤ Nat.card s :=
  Nat.card_le_card_of_surjective _ Set.imageFactorization_surjective
/-
**Finite.card_range_le** 是 Mathlib 中的一个定理，位于命名空间 `Finite`。
形式化陈述：card_range_le [Finite α] (f : α -> β) : Nat.card (Set.range f) <= Nat.card
 α
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.card_le_card_of_surjective`：card_le_card_of_surjective {α : Type u} 
{β : Type v} [Finite α] (f : α -> β) (hf : Surjective f) : Nat.card β <= Nat.car
d α
· 使用定理 `Set.rangeFactorization_surjective`：∀ {α : Type u} {ι : Sort u_1} {f : ι 
→ α}, Function.Surjective (Set.rangeFactorization f)
-/
theorem card_range_le [Finite α] (f : α → β) : Nat.card (Set.range f) ≤ Nat.card α :=
  Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective
/-
**Finite.card_subtype_le** 是 Mathlib 中的一个定理，位于命名空间 `Finite`。
形式化陈述：card_subtype_le [Finite α] (p : α -> Prop) : Nat.card { x // p x } <= Nat.
card α
参数：p : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_subtype_le`：Fintype.card_subtype_le [Fintype α] (p : α -> P
rop) [Fintype {a // p a}] : Fintype.card { x // p x } <= Fintype.card α
-/
theorem card_subtype_le [Finite α] (p : α → Prop) : Nat.card { x // p x } ≤ Nat.card α := by
  classical
  have := Fintype.ofFinite α
  simpa only [Nat.card_eq_fintype_card] using Fintype.card_subtype_le p
/-
**Finite.card_subtype_lt** 是 Mathlib 中的一个定理，位于命名空间 `Finite`。
形式化陈述：card_subtype_lt [Finite α] {p : α -> Prop} {x : α} (hx : ¬p x) : Nat.card 
{ x // p x } < Nat.card α
参数：hx : ¬p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用引理 `Fintype.card_subtype_lt`：Fintype.card_subtype_lt [Fintype α] {p : α -> P
rop} [Fintype {a // p a}] {x : α} (hx : ¬p x) : Fintype.card { x // p x } < Fint
ype.card α
-/
theorem card_subtype_lt [Finite α] {p : α → Prop} {x : α} (hx : ¬p x) :
    Nat.card { x // p x } < Nat.card α := by
  classical
  have := Fintype.ofFinite α
  simpa only [Nat.card_eq_fintype_card, gt_iff_lt] using Fintype.card_subtype_lt hx

/-- A custom induction principle for finite types, by strong induction on `Nat.card`:
the base case is a subsingleton type, and the induction step is for nontrivial types,
where one can assume the hypothesis for all types of smaller cardinality. -/
@[elab_as_elim]
/-
**Finite.induction_subsingleton_or_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Finite`
。
形式化陈述：induction_subsingleton_or_nontrivial {P : Type* -> Prop} (α) [Finite α] (h
base : forall (α) [Finite α] [Subsingleton α], P α) (hstep : forall (α) [Finite 
α] [Nontrivial α], (forall (β) [Finite β], Nat.card β < Nat.card α -> P β) -> P 
α) : P α
参数：α；hbase : forall (α) [Finite α] [Subsingleton α], P α；hstep : forall (α) [Fin
ite α] [Nontrivial α], (forall (β) [Finite β], Nat.card β < Nat.card α -> P β) -
> P α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
A custom induction principle for finite types, by strong induction on `Nat.card`
:
the base case is a subsingleton type, and the induction step is for nontrivial t
ypes,
where one can assume the hypothesis for all types of smaller cardinality.
-/
theorem induction_subsingleton_or_nontrivial {P : Type* → Prop} (α) [Finite α]
    (hbase : ∀ (α) [Finite α] [Subsingleton α], P α)
    (hstep : ∀ (α) [Finite α] [Nontrivial α],
      (∀ (β) [Finite β], Nat.card β < Nat.card α → P β) → P α) :
    P α := by
  obtain ⟨n, hn⟩ : ∃ n, Nat.card α = n := ⟨Nat.card α, rfl⟩
  induction n using Nat.strong_induction_on generalizing α with | _ n ih
  rcases subsingleton_or_nontrivial α with hsing | hnontriv
  · apply hbase
  · apply hstep
    intro β _ hlt
    rw [hn] at hlt
    exact ih (Nat.card β) hlt _ rfl

end Finite

namespace ENat

/-
**ENat.card_eq_coe_natCard** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：card_eq_coe_natCard (α : Type*) [Finite α] : card α = Nat.card α
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
· 使用定理 `IsEquiv.toSymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEquiv α r]
, Std.Symm r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.natCast_eq_toENat`：∀ {c : Cardinal.{u}} {n : ℕ}, ↑n = Cardinal.
toENat c ↔ ↑n = c
· 使用引理 `Nat.cast_card`：cast_card [Finite α] : (Nat.card α : Cardinal) = Cardinal
.mk α
-/
theorem card_eq_coe_natCard (α : Type*) [Finite α] : card α = Nat.card α := by
  unfold ENat.card
  apply symm
  rw [Cardinal.natCast_eq_toENat]
  exact Nat.cast_card

end ENat

namespace Set

/-
**Set.card_union_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：card_union_le (s t : Set α) : Nat.card (↥(s union t)) <= Nat.card s + Nat.
card t
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.finite_coe_iff`：finite_coe_iff {s : Set α} : Finite s ↔ s.Finite
· 使用定理 `Set.finite_union`：finite_union {s t : Set α} : (s union t).Finite ↔ s.Fi
nite ∧ t.Finite
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用引理 `Nat.cast_card`：cast_card [Finite α] : (Nat.card α : Cardinal) = Cardinal
.mk α
· 使用定理 `Cardinal.mk_union_le`：mk_union_le {α : Type u} (S T : Set α) : #(S union
 T : Set α) <= #S + #T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem card_union_le (s t : Set α) : Nat.card (↥(s ∪ t)) ≤ Nat.card s + Nat.card t := by
  rcases _root_.finite_or_infinite (↥(s ∪ t)) with h | h
  · rw [finite_coe_iff, finite_union, ← finite_coe_iff, ← finite_coe_iff] at h
    cases h
    rw [← @Nat.cast_le Cardinal, Nat.cast_add, Nat.cast_card, Nat.cast_card, Nat.cast_card]
    exact Cardinal.mk_union_le s t
  · simp

namespace Finite

variable {s t : Set α}

/-
**Set.Finite.card_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：card_lt_card (ht : t.Finite) (hsub : s ⊂ t) : Nat.card s < Nat.card t
参数：ht : t.Finite；hsub : s ⊂ t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `subset_of_ssubset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : 
Preorder α] {a b : α}, a ⊂ b → a ⊆ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Set.card_lt_card`：card_lt_card {s t : Set α} [Fintype s] [Fintype t] (h 
: s ⊂ t) : Fintype.card s < Fintype.card t
-/
theorem card_lt_card (ht : t.Finite) (hsub : s ⊂ t) : Nat.card s < Nat.card t := by
  have : Fintype t := Finite.fintype ht
  have : Fintype s := Finite.fintype (subset ht (subset_of_ssubset hsub))
  simp only [Nat.card_eq_fintype_card]
  exact Set.card_lt_card hsub
/-
**Set.Finite._root_.Set.ecard_le_ecard** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.ecard_le_ecard (hsub : s ⊆ t) : ENat.card s ≤ ENat.card t :=
  ENat.card_le_card_of_injective <| inclusion_injective hsub
/-
**Set.Finite.ecard_lt_ecard** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：ecard_lt_ecard (hs : s.Finite) (hsub : s ⊂ t) : ENat.card s < ENat.card t
参数：hs : s.Finite；hsub : s ⊂ t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_add_of_le_right`：∀ {α : Type u} [inst : Add α] [inst_1 : Preorder α] 
[CanonicallyOrderedAdd α] {a b c : α}, a ≤ c → a ≤ b + c
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.card_sum`：card_sum (α β : Type*) : card (α oplus β) = card α + card
 β
· 使用定理 `ENat.card_congr`：card_congr {α β : Type*} (f : α ≃ β) : card α = card β
· 使用引理 `Set.disjoint_sdiff_left`：disjoint_sdiff_left : Disjoint (t \ s) s
· 使用定理 `Set.sdiff_union_of_subset`：sdiff_union_of_subset {s t : Set α} (h : t su
bseteq s) : s \ t union t = s
· 使用定理 `LT.lt.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b : α}, a ⊂ b → a ⊆ b
· 使用定理 `WithTop.le_of_add_le_add_right`：∀ {α : Type u} [inst : Add α] {x y z : W
ithTop α} [inst_1 : LE α] [AddRightReflectLE α], z ≠ ⊤ → x + z ≤ y + z → x ≤ y
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENat.card_lt_top`：∀ {α : Type u_1}, ENat.card α < ⊤ ↔ Finite α
· 使用定理 `Set.sdiff_eq_empty`：sdiff_eq_empty {s t : Set α} : s \ t = ∅ ↔ s subsete
q t
· 使用定理 `Set.isEmpty_coe_sort`：isEmpty_coe_sort {s : Set α} : IsEmpty (↥s) ↔ s = 
∅
· 使用定理 `ENat.card_eq_zero_iff_empty`：card_eq_zero_iff_empty (α : Type*) : card α
 = 0 ↔ IsEmpty α
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用引理 `lt_of_le_not_ge`：lt_of_le_not_ge (hab : a <= b) (hba : ¬ b <= a) : a < b
· 使用定理 `Set.ecard_le_ecard`：∀ {α : Type u_1} {s t : Set α}, s ⊆ t → ENat.card ↑s
 ≤ ENat.card ↑t
· 使用定理 `not_subset_of_ssubset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [ins
t : Preorder α] {a b : α}, a ⊂ b → ¬b ⊆ a
-/
theorem ecard_lt_ecard (hs : s.Finite) (hsub : s ⊂ t) : ENat.card s < ENat.card t := by
  classical
  suffices ENat.card t ≤ ENat.card s → t ⊆ s from
    lt_of_le_not_ge (ecard_le_ecard hsub.subset) fun hle ↦ not_subset_of_ssubset hsub <| this hle
  intro hle
  suffices ENat.card ↑(t \ s) ≤ 0 by
    rwa [← sdiff_eq_empty, ← Set.isEmpty_coe_sort, ← ENat.card_eq_zero_iff_empty,
      ← nonpos_iff_eq_zero]
  suffices ENat.card ↑(t \ s) + ENat.card ↑s ≤ 0 + ENat.card ↑s from
    WithTop.le_of_add_le_add_right (ENat.card_lt_top.mpr hs).ne this
  suffices ENat.card ↑t ≤ 0 + ENat.card ↑s by
    rwa [← ENat.card_sum, ← ENat.card_congr <| Equiv.Set.union disjoint_sdiff_left,
      sdiff_union_of_subset hsub.subset]
  exact le_add_of_le_right hle
/-
**Set.Finite.card_strictMonoOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：card_strictMonoOn : StrictMonoOn (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.card_lt_card`：card_lt_card (ht : t.Finite) (hsub : s ⊂ t) : N
at.card s < Nat.card t
-/
theorem card_strictMonoOn : StrictMonoOn (α := Set α) (Nat.card ∘ (↑)) (Set.ofPred Set.Finite) :=
  fun _ _ _ ↦ card_lt_card
/-
**Set.Finite.ecard_strictMonoOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：ecard_strictMonoOn : StrictMonoOn (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.ecard_lt_ecard`：ecard_lt_ecard (hs : s.Finite) (hsub : s ⊂ t)
 : ENat.card s < ENat.card t
-/
theorem ecard_strictMonoOn : StrictMonoOn (α := Set α) (ENat.card ∘ (↑)) (Set.ofPred Set.Finite) :=
  fun _ hs _ _ ↦ hs.ecard_lt_ecard
/-
**Set.Finite.eq_of_subset_of_card_le** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：eq_of_subset_of_card_le (ht : t.Finite) (hsub : s subseteq t) (hcard : Nat
.card t <= Nat.card s) : s = t
参数：ht : t.Finite；hsub : s subseteq t；hcard : Nat.card t <= Nat.card s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `eq_or_ssubset_of_subset`：∀ {α : Type u_2} [UsesSetNotationForOrder α] [i
nst : PartialOrder α] {a b : α}, a ⊆ b → a = b ∨ a ⊂ b
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Set.Finite.card_lt_card`：card_lt_card (ht : t.Finite) (hsub : s ⊂ t) : N
at.card s < Nat.card t
-/
theorem eq_of_subset_of_card_le (ht : t.Finite) (hsub : s ⊆ t) (hcard : Nat.card t ≤ Nat.card s) :
    s = t :=
  (eq_or_ssubset_of_subset hsub).elim id fun h ↦ absurd hcard <| not_le_of_gt <| ht.card_lt_card h
/-
**Set.Finite.equiv_image_eq_iff_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：equiv_image_eq_iff_subset (e : α ≃ α) (hs : s.Finite) : e '' s = s ↔ e '' 
s subseteq s
参数：e : α ≃ α；hs : s.Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Set.Finite.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (ht : t.Fini
te) (hsub : s subseteq t) (hcard : Nat.card t <= Nat.card s) : s = t
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem equiv_image_eq_iff_subset (e : α ≃ α) (hs : s.Finite) : e '' s = s ↔ e '' s ⊆ s :=
  ⟨fun h ↦ by rw [h], fun h ↦ hs.eq_of_subset_of_card_le h <|
    ge_of_eq (Nat.card_congr (e.image s).symm)⟩

end Finite

/-
**Set.card_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：card_strictMono [Finite α] : StrictMono (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.card_lt_card`：card_lt_card (ht : t.Finite) (hsub : s ⊂ t) : N
at.card s < Nat.card t
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
-/
theorem card_strictMono [Finite α] : StrictMono (α := Set α) (Nat.card ∘ (↑)) :=
  fun _ t ↦ t.toFinite.card_lt_card
/-
**Set.ecard_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ecard_strictMono [Finite α] : StrictMono (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.ecard_lt_ecard`：ecard_lt_ecard (hs : s.Finite) (hsub : s ⊂ t)
 : ENat.card s < ENat.card t
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
-/
theorem ecard_strictMono [Finite α] : StrictMono (α := Set α) (ENat.card ∘ (↑)) :=
  fun s _ ↦ s.toFinite.ecard_lt_ecard
/-
**Set.eq_top_of_card_le_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_top_of_card_le_of_finite [Finite α] {s : Set α} (h : Nat.card α <= Nat.
card s) : s = ⊤
参数：h : Nat.card α <= Nat.card s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (ht : t.Fini
te) (hsub : s subseteq t) (hcard : Nat.card t <= Nat.card s) : s = t
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
-/
theorem eq_top_of_card_le_of_finite [Finite α] {s : Set α} (h : Nat.card α ≤ Nat.card s) : s = ⊤ :=
  Set.Finite.eq_of_subset_of_card_le univ.toFinite (subset_univ s) <|
    Nat.card_congr (Equiv.Set.univ α) ▸ h

end Set

namespace List.Nodup

variable {l : List α} (h : l.Nodup)
include h

/-
**List.Nodup.length_le_natCard** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：length_le_natCard [Finite α] : l.length <= Nat.card α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `List.Nodup.length_le_card`：List.Nodup.length_le_card {α : Type*} [Fintyp
e α] {l : List α} (h : l.Nodup) : l.length <= Fintype.card α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_eq_nat_card`：∀ {α : Type u_1} {x : Fintype α}, Fintype.card
 α = Nat.card α
-/
theorem length_le_natCard [Finite α] : l.length ≤ Nat.card α := by
  have := Fintype.ofFinite α
  grw [h.length_le_card, Fintype.card_eq_nat_card]
/-
**List.Nodup.length_le_enatCard** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：length_le_enatCard : l.length <= ENat.card α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `List.Nodup.length_le_natCard`：length_le_natCard [Finite α] : l.length <=
 Nat.card α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.card_eq_coe_natCard`：card_eq_coe_natCard (α : Type*) [Finite α] : c
ard α = Nat.card α
· 使用定理 `ENat.card_eq_top_of_infinite`：card_eq_top_of_infinite [Infinite α] : car
d α = ⊤
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem length_le_enatCard : l.length ≤ ENat.card α := by
  cases finite_or_infinite α
  · grw [h.length_le_natCard, ENat.card_eq_coe_natCard]
  · grw [ENat.card_eq_top_of_infinite]
    exact le_top

end List.Nodup

