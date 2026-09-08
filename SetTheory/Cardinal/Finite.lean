/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Data.ENat.Pow
public import Mathlib.Data.ULift
public import Mathlib.Data.ZMod.Defs
public import Mathlib.SetTheory.Cardinal.ToNat
public import Mathlib.SetTheory.Cardinal.ENat

/-!
# Finite Cardinality Functions

## Main Definitions

* `Nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `Nat.card α = 0`.
* `ENat.card α` is the cardinality of `α` as an extended natural number.
  If `α` is infinite, `ENat.card α = ⊤`.
-/

@[expose] public section

assert_not_exists Field

open Cardinal Function

noncomputable section

variable {α β : Type*}

universe u v

namespace Nat

/-- `Nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `Nat.card α = 0`. -/
/-
**Nat.card** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：Type u_3 → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `Nat.card α = 0`.
-/
protected def card (α : Type*) : ℕ :=
  toNat (mk α)

@[simp]
/-
**Nat.card_eq_fintype_card** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：card_eq_fintype_card [Fintype α] : Nat.card α = Fintype.card α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_toNat_eq_card`：mk_toNat_eq_card [Fintype α] : toNat #α = Fin
type.card α
-/
theorem card_eq_fintype_card [Fintype α] : Nat.card α = Fintype.card α :=
  mk_toNat_eq_card

/-- Because this theorem takes `Fintype α` as a non-instance argument, it can be used in particular
when `Fintype.card` ends up with different instance than the one found by inference -/
/-
**Nat._root_.Fintype.card_eq_nat_card** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Because this theorem takes `Fintype α` as a non-instance argument, it can be use
d in particular
when `Fintype.card` ends up with different instance than the one found by infere
nce
-/
theorem _root_.Fintype.card_eq_nat_card {_ : Fintype α} : Fintype.card α = Nat.card α :=
  mk_toNat_eq_card.symm
/-
**Nat.card_eq_finsetCard** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：card_eq_finsetCard (s : Finset α) : Nat.card s = s.card
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma card_eq_finsetCard (s : Finset α) : Nat.card s = s.card := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe]
/-
**Nat.card_eq_card_toFinset** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：card_eq_card_toFinset (s : Set α) [Fintype s] : Nat.card s = s.toFinset.ca
rd
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma card_eq_card_toFinset (s : Set α) [Fintype s] : Nat.card s = s.toFinset.card := by
  simp only [← Nat.card_eq_finsetCard, s.mem_toFinset]
/-
**Nat.card_eq_card_finite_toFinset** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：card_eq_card_finite_toFinset {s : Set α} (hs : s.Finite) : Nat.card s = hs
.toFinset.card
参数：hs : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma card_eq_card_finite_toFinset {s : Set α} (hs : s.Finite) : Nat.card s = hs.toFinset.card := by
  simp only [← Nat.card_eq_finsetCard, hs.mem_toFinset]
/-
**Nat.subtype_card** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：subtype_card {p : α -> Prop} (s : Finset α) (H : forall x : α, x in s ↔ p 
x) : Nat.card { x // p x } = Finset.card s
参数：s : Finset α；H : forall x : α, x in s ↔ p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.subtype_card`：subtype_card {p : α -> Prop} (s : Finset α) (H : f
orall x : α, x in s ↔ p x) : @card { x // p x } (Fintype.subtype s H) = #s
· 使用定理 `Fintype.card_eq_nat_card`：∀ {α : Type u_1} {x : Fintype α}, Fintype.card
 α = Nat.card α
-/
theorem subtype_card {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x) :
    Nat.card { x // p x } = Finset.card s := by
  rw [← Fintype.subtype_card s H, Fintype.card_eq_nat_card]
/-
**Nat.card_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {α : Type u_1} [IsEmpty α], Nat.card α = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_eq_zero`：mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0
· 使用定理 `Cardinal.zero_toNat`：zero_toNat : toNat 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem card_of_isEmpty [IsEmpty α] : Nat.card α = 0 := by simp [Nat.card]
/-
**Nat.card_eq_zero_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {α : Type u_1} [Infinite α], Nat.card α = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_toNat_of_infinite`：mk_toNat_of_infinite [h : Infinite α] : t
oNat #α = 0
-/
@[simp] lemma card_eq_zero_of_infinite [Infinite α] : Nat.card α = 0 := mk_toNat_of_infinite
/-
**Nat.cast_card** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：cast_card [Finite α] : (Nat.card α : Cardinal) = Cardinal.mk α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card.eq_1`：∀ (α : Type u_3), Nat.card α = Cardinal.toNat (Cardinal.m
k α)
· 使用定理 `Cardinal.cast_toNat_of_lt_aleph0`：cast_toNat_of_lt_aleph0 {c : Cardinal}
 (h : c < ℵ₀) : ↑(toNat c) = c
· 使用定理 `Cardinal.lt_aleph0_of_finite`：lt_aleph0_of_finite (α : Type u) [Finite α
] : #α < ℵ₀
-/
lemma cast_card [Finite α] : (Nat.card α : Cardinal) = Cardinal.mk α := by
  rw [Nat.card, Cardinal.cast_toNat_of_lt_aleph0]
  exact Cardinal.lt_aleph0_of_finite _
/-
**Nat._root_.Set.Infinite.card_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Set.Infinite.card_eq_zero {s : Set α} (hs : s.Infinite) : Nat.card s = 0 :=
  @card_eq_zero_of_infinite _ hs.to_subtype
/-
**Nat.card_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：card_eq_zero : Nat.card α = 0 ↔ IsEmpty α ∨ Infinite α
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma card_eq_zero : Nat.card α = 0 ↔ IsEmpty α ∨ Infinite α := by
  simp [Nat.card, mk_eq_zero_iff, aleph0_le_mk_iff]
/-
**Nat.card_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：card_ne_zero : Nat.card α != 0 ↔ Nonempty α ∧ Finite α
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma card_ne_zero : Nat.card α ≠ 0 ↔ Nonempty α ∧ Finite α := by simp [card_eq_zero, not_or]
/-
**Nat.card_pos_iff** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：card_pos_iff : 0 < Nat.card α ↔ Nonempty α ∧ Finite α
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma card_pos_iff : 0 < Nat.card α ↔ Nonempty α ∧ Finite α := by
  simp [Nat.card, mk_eq_zero_iff, mk_lt_aleph0_iff]
/-
**Nat.card_pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {α : Type u_1} [Nonempty α] [Finite α], 0 < Nat.card α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.card_pos_iff`：card_pos_iff : 0 < Nat.card α ↔ Nonempty α ∧ Finite α
-/
@[simp] lemma card_pos [Nonempty α] [Finite α] : 0 < Nat.card α := card_pos_iff.2 ⟨‹_›, ‹_›⟩
/-
**Nat.** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty α] [Finite α] : NeZero (Nat.card α) := ⟨card_pos.ne'⟩
/-
**Nat.finite_of_card_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：finite_of_card_ne_zero (h : Nat.card α != 0) : Finite α
参数：h : Nat.card α != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Nat.card_ne_zero`：card_ne_zero : Nat.card α != 0 ↔ Nonempty α ∧ Finite α
-/
theorem finite_of_card_ne_zero (h : Nat.card α ≠ 0) : Finite α := (card_ne_zero.1 h).2
/-
**Nat.card_congr** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
参数：f : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.toNat_congr`：toNat_congr {β : Type v} (e : α ≃ β) : toNat #α = 
toNat #β
-/
theorem card_congr (f : α ≃ β) : Nat.card α = Nat.card β :=
  Cardinal.toNat_congr f
/-
**Nat.card_le_card_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：card_le_card_of_injective {α : Type u} {β : Type v} [Finite β] (f : α -> β
) (hf : Injective f) : Nat.card α <= Nat.card β
参数：f : α -> β；hf : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `Cardinal.toNat_le_toNat`：toNat_le_toNat (hcd : c <= d) (hd : d < ℵ₀) : t
oNat c <= toNat d
· 使用引理 `Cardinal.lift_mk_le_lift_mk_of_injective`：lift_mk_le_lift_mk_of_injectiv
e {α : Type u} {β : Type v} {f : α -> β} (hf : Injective f) : Cardinal.lift.{v} 
(#α) <= Cardinal.lift.{u} (#β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma card_le_card_of_injective {α : Type u} {β : Type v} [Finite β] (f : α → β)
    (hf : Injective f) : Nat.card α ≤ Nat.card β := by
  simpa using! toNat_le_toNat (lift_mk_le_lift_mk_of_injective hf) (by simp)
/-
**Nat.card_le_card_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：card_le_card_of_surjective {α : Type u} {β : Type v} [Finite α] (f : α -> 
β) (hf : Surjective f) : Nat.card β <= Nat.card α
参数：f : α -> β；hf : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_le_of_surjective`：mk_le_of_surjective {α β : Type u} {f : α 
-> β} (hf : Surjective f) : #β <= #α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ULift.map_surjective`：∀ {α : Type u} {β : Type v} {f : α → β}, Function.
Surjective (ULift.map f) ↔ Function.Surjective f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `Cardinal.toNat_le_toNat`：toNat_le_toNat (hcd : c <= d) (hd : d < ℵ₀) : t
oNat c <= toNat d
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma card_le_card_of_surjective {α : Type u} {β : Type v} [Finite α] (f : α → β)
    (hf : Surjective f) : Nat.card β ≤ Nat.card α := by
  have : lift.{u} #β ≤ lift.{v} #α := mk_le_of_surjective (ULift.map_surjective.2 hf)
  simpa using! toNat_le_toNat this (by simp)
/-
**Nat.card_eq_of_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：card_eq_of_bijective (f : α -> β) (hf : Function.Bijective f) : Nat.card α
 = Nat.card β
参数：f : α -> β；hf : Function.Bijective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
-/
theorem card_eq_of_bijective (f : α → β) (hf : Function.Bijective f) : Nat.card α = Nat.card β :=
  card_congr (Equiv.ofBijective f hf)
/-
**Nat.bijective_iff_injective_and_card** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [Finite β] (f : α → β),   Function.Bijecti
ve f ↔ Function.Injective f ∧ Nat.card α = Nat.card β
参数：f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Bijective.eq_1`：∀ {α : Sort u₁} {β : Sort u₂} (f : α → β), Func
tion.Bijective f = (Function.Injective f ∧ Function.Surjective f)
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.bijective_iff_injective_and_card`：bijective_iff_injective_and_ca
rd (f : α -> β) : Bijective f ↔ Injective f ∧ card α = card β
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem bijective_iff_injective_and_card [Finite β] (f : α → β) :
    Bijective f ↔ Injective f ∧ Nat.card α = Nat.card β := by
  rw [Bijective, and_congr_right_iff]
  intro h
  have := Fintype.ofFinite β
  have := Fintype.ofInjective f h
  revert h
  rw [← and_congr_right_iff, ← Bijective,
    card_eq_fintype_card, card_eq_fintype_card, Fintype.bijective_iff_injective_and_card]
/-
**Nat.bijective_iff_surjective_and_card** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [Finite α] (f : α → β),   Function.Bijecti
ve f ↔ Function.Surjective f ∧ Nat.card α = Nat.card β
参数：f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Function.Bijective.eq_1`：∀ {α : Sort u₁} {β : Sort u₂} (f : α → β), Func
tion.Bijective f = (Function.Injective f ∧ Function.Surjective f)
· 使用定理 `and_congr_left_iff`：∀ {a c b : Prop}, (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.bijective_iff_surjective_and_card`：bijective_iff_surjective_and_
card (f : α -> β) : Bijective f ↔ Surjective f ∧ card α = card β
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem bijective_iff_surjective_and_card [Finite α] (f : α → β) :
    Bijective f ↔ Surjective f ∧ Nat.card α = Nat.card β := by
  classical
  rw [_root_.and_comm, Bijective, and_congr_left_iff]
  intro h
  have := Fintype.ofFinite α
  have := Fintype.ofSurjective f h
  revert h
  rw [← and_congr_left_iff, ← Bijective, ← and_comm,
    card_eq_fintype_card, card_eq_fintype_card, Fintype.bijective_iff_surjective_and_card]
/-
**Nat._root_.Function.Injective.bijective_of_nat_card_le** 是 Mathlib 中的一个定理，位于命名
空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Injective.bijective_of_nat_card_le [Finite β] {f : α → β}
    (inj : Injective f) (hc : Nat.card β ≤ Nat.card α) : Bijective f :=
  (Nat.bijective_iff_injective_and_card f).mpr
    ⟨inj, hc.antisymm (card_le_card_of_injective f inj) |>.symm⟩
/-
**Nat._root_.Function.Surjective.bijective_of_nat_card_le** 是 Mathlib 中的一个定理，位于命
名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Surjective.bijective_of_nat_card_le [Finite α] {f : α → β}
    (surj : Surjective f) (hc : Nat.card α ≤ Nat.card β) : Bijective f :=
  (Nat.bijective_iff_surjective_and_card f).mpr
    ⟨surj, hc.antisymm (card_le_card_of_surjective f surj)⟩
/-
**Nat.card_eq_of_equiv_fin** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：card_eq_of_equiv_fin {α : Type*} {n : Nat} (f : α ≃ Fin n) : Nat.card α = 
n
参数：f : α ≃ Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
-/
theorem card_eq_of_equiv_fin {α : Type*} {n : ℕ} (f : α ≃ Fin n) : Nat.card α = n := by
  simpa only [card_eq_fintype_card, Fintype.card_fin] using card_congr f
/-
**Nat.card_fin** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：card_fin (n : Nat) : Nat.card (Fin n) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
-/
lemma card_fin (n : ℕ) : Nat.card (Fin n) = n := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fin]

section Set
open Set
variable {s t : Set α}

/-
**Nat.card_mono** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：card_mono (ht : t.Finite) (h : s subseteq t) : Nat.card s <= Nat.card t
参数：ht : t.Finite；h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.toNat_le_toNat`：toNat_le_toNat (hcd : c <= d) (hd : d < ℵ₀) : t
oNat c <= toNat d
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
· 使用定理 `Set.Finite.lt_aleph0`：∀ {α : Type u} {S : Set α}, S.Finite → Cardinal.mk
 ↑S < Cardinal.aleph0
-/
lemma card_mono (ht : t.Finite) (h : s ⊆ t) : Nat.card s ≤ Nat.card t :=
  toNat_le_toNat (mk_le_mk_of_subset h) ht.lt_aleph0
/-
**Nat.card_image_le** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：card_image_le {f : α -> β} (hs : s.Finite) : Nat.card (f '' s) <= Nat.card
 s
参数：hs : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用引理 `Nat.card_le_card_of_surjective`：card_le_card_of_surjective {α : Type u} 
{β : Type v} [Finite α] (f : α -> β) (hf : Surjective f) : Nat.card β <= Nat.car
d α
· 使用定理 `Set.imageFactorization_surjective`：imageFactorization_surjective {f : α 
-> β} {s : Set α} : Surjective (imageFactorization f s)
-/
lemma card_image_le {f : α → β} (hs : s.Finite) : Nat.card (f '' s) ≤ Nat.card s :=
  have := hs.to_subtype
  card_le_card_of_surjective (imageFactorization f s) imageFactorization_surjective
/-
**Nat.card_image_of_injOn** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：card_image_of_injOn {f : α -> β} (hf : s.InjOn f) : Nat.card (f '' s) = Na
t.card s
参数：hf : s.InjOn f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_or_infinite`：∀ {α : Type u} (s : Set α), s.Finite ∨ s.Infinit
e
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.card_image_of_inj_on`：card_image_of_inj_on {s : Set α} [Fintype s] {
f : α -> β} [Fintype (f '' s)] (H : forall x in s, forall y in s, f x = f y -> x
 = y) : Fintyp…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.Infinite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Infinite → Infini
te ↑s
· 使用定理 `Set.Infinite.image`：∀ {α : Type u} {β : Type v} {s : Set α} {f : α → β},
 Set.InjOn f s → s.Infinite → (f '' s).Infinite
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0
-/
lemma card_image_of_injOn {f : α → β} (hf : s.InjOn f) : Nat.card (f '' s) = Nat.card s := by
  classical
  obtain hs | hs := s.finite_or_infinite
  · have := hs.fintype
    simp_rw [Nat.card_eq_fintype_card, Set.card_image_of_inj_on hf]
  · have := hs.to_subtype
    have := (hs.image hf).to_subtype
    simp [Nat.card_eq_zero_of_infinite]
/-
**Nat.card_image_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：card_image_of_injective {f : α -> β} (hf : Injective f) (s : Set α) : Nat.
card (f '' s) = Nat.card s
参数：hf : Injective f；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.card_image_of_injOn`：card_image_of_injOn {f : α -> β} (hf : s.InjOn 
f) : Nat.card (f '' s) = Nat.card s
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
-/
lemma card_image_of_injective {f : α → β} (hf : Injective f) (s : Set α) :
    Nat.card (f '' s) = Nat.card s := card_image_of_injOn hf.injOn
/-
**Nat.card_image_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：card_image_equiv (e : α ≃ β) : Nat.card (e '' s) = Nat.card s
参数：e : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma card_image_equiv (e : α ≃ β) : Nat.card (e '' s) = Nat.card s :=
    Nat.card_congr (e.image s).symm
/-
**Nat.card_preimage_of_injOn** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：card_preimage_of_injOn {f : α -> β} {s : Set β} (hf : (f ⁻¹' s).InjOn f) (
hsf : s subseteq range f) : Nat.card (f ⁻¹' s) = Nat.card s
参数：hf : (f ⁻¹' s).InjOn f；hsf : s subseteq range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.card_image_of_injOn`：card_image_of_injOn {f : α -> β} (hf : s.InjOn 
f) : Nat.card (f '' s) = Nat.card s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_preimage_eq_iff`：image_preimage_eq_iff {f : α -> β} {s : Set β
} : f '' f ⁻¹' s = s ↔ s subseteq range f
-/
lemma card_preimage_of_injOn {f : α → β} {s : Set β} (hf : (f ⁻¹' s).InjOn f) (hsf : s ⊆ range f) :
    Nat.card (f ⁻¹' s) = Nat.card s := by
  rw [← Nat.card_image_of_injOn hf, image_preimage_eq_iff.2 hsf]
/-
**Nat.card_preimage_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：card_preimage_of_injective {f : α -> β} {s : Set β} (hf : Injective f) (hs
f : s subseteq range f) : Nat.card (f ⁻¹' s) = Nat.card s
参数：hf : Injective f；hsf : s subseteq range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.card_preimage_of_injOn`：card_preimage_of_injOn {f : α -> β} {s : Set
 β} (hf : (f ⁻¹' s).InjOn f) (hsf : s subseteq range f) : Nat.card (f ⁻¹' s) = N
at.card s
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
-/
lemma card_preimage_of_injective {f : α → β} {s : Set β} (hf : Injective f) (hsf : s ⊆ range f) :
    Nat.card (f ⁻¹' s) = Nat.card s := card_preimage_of_injOn hf.injOn hsf
/-
**Nat.card_univ** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：card_univ : Nat.card (univ : Set α) = Nat.card α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
-/
lemma card_univ : Nat.card (univ : Set α) = Nat.card α :=
  card_congr (Equiv.Set.univ α)
/-
**Nat.card_range_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：card_range_of_injective {f : α -> β} (hf : Injective f) : Nat.card (range 
f) = Nat.card α
参数：hf : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.card_preimage_of_injective`：card_preimage_of_injective {f : α -> β} 
{s : Set β} (hf : Injective f) (hsf : s subseteq range f) : Nat.card (f ⁻¹' s) =
 Nat.card s
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.preimage_range`：preimage_range (f : α -> β) : f ⁻¹' range f = univ
· 使用引理 `Nat.card_univ`：card_univ : Nat.card (univ : Set α) = Nat.card α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma card_range_of_injective {f : α → β} (hf : Injective f) :
    Nat.card (range f) = Nat.card α := by
  rw [← Nat.card_preimage_of_injective hf le_rfl]
  simp [Nat.card_univ]

end Set

/-- If the cardinality is positive, that means it is a finite type, so there is
an equivalence between `α` and `Fin (Nat.card α)`. See also `Finite.equivFin`. -/
/-
**Nat.equivFinOfCardPos** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：equivFinOfCardPos {α : Type*} (h : Nat.card α != 0) : α ≃ Fin (Nat.card α)
参数：h : Nat.card α != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the cardinality is positive, that means it is a finite type, so there is
an equivalence between `α` and `Fin (Nat.card α)`. See also `Finite.equivFin`.
-/
def equivFinOfCardPos {α : Type*} (h : Nat.card α ≠ 0) : α ≃ Fin (Nat.card α) := by
  cases fintypeOrInfinite α
  · simpa only [card_eq_fintype_card] using Fintype.equivFin α
  · simp only [card_eq_zero_of_infinite, ne_eq, not_true_eq_false] at h
/-
**Nat.card_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：card_of_subsingleton (a : α) [Subsingleton α] : Nat.card α = 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_ofSubsingleton`：card_ofSubsingleton (a : α) [Subsingleton α
] : @Fintype.card _ (ofSubsingleton a) = 1
-/
theorem card_of_subsingleton (a : α) [Subsingleton α] : Nat.card α = 1 := by
  let := Fintype.ofSubsingleton a
  rw [card_eq_fintype_card, Fintype.card_ofSubsingleton a]
/-
**Nat.card_eq_one_iff_unique** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：card_eq_one_iff_unique : Nat.card α = 1 ↔ Subsingleton α ∧ Nonempty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.toNat_eq_one_iff_unique`：toNat_eq_one_iff_unique : toNat #α = 1
 ↔ Subsingleton α ∧ Nonempty α
-/
theorem card_eq_one_iff_unique : Nat.card α = 1 ↔ Subsingleton α ∧ Nonempty α :=
  Cardinal.toNat_eq_one_iff_unique

@[simp]
/-
**Nat.card_unique** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：card_unique [Nonempty α] [Subsingleton α] : Nat.card α = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem card_unique [Nonempty α] [Subsingleton α] : Nat.card α = 1 := by
  simp [card_eq_one_iff_unique, *]
/-
**Nat.card_eq_one_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：card_eq_one_iff_exists : Nat.card α = 1 ↔ exists x : α, forall y : α, y = 
x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_one_iff_unique`：card_eq_one_iff_unique : Nat.card α = 1 ↔ Su
bsingleton α ∧ Nonempty α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `subsingleton_of_forall_eq`：∀ {α : Sort u_1} (x : α), (∀ (y : α), y = x) 
→ Subsingleton α
-/
theorem card_eq_one_iff_exists : Nat.card α = 1 ↔ ∃ x : α, ∀ y : α, y = x := by
  rw [card_eq_one_iff_unique]
  exact ⟨fun ⟨s, ⟨a⟩⟩ ↦ ⟨a, fun x ↦ s.elim x a⟩, fun ⟨x, h⟩ ↦ ⟨subsingleton_of_forall_eq x h, ⟨x⟩⟩⟩
/-
**Nat.card_eq_two_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：card_eq_two_iff : Nat.card α = 2 ↔ exists x y : α, x != y ∧ {x, y} = @Set.
univ α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Cardinal.toNat_eq_ofNat`：toNat_eq_ofNat {n : Nat} [Nat.AtLeastTwo n] : t
oNat c = OfNat.ofNat n ↔ c = OfNat.ofNat n
· 使用定理 `Cardinal.mk_eq_two_iff`：mk_eq_two_iff : #α = 2 ↔ exists x y : α, x != y 
∧ ({x, y} : Set α) = univ
-/
theorem card_eq_two_iff : Nat.card α = 2 ↔ ∃ x y : α, x ≠ y ∧ {x, y} = @Set.univ α :=
  toNat_eq_ofNat.trans mk_eq_two_iff
/-
**Nat.card_eq_two_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：card_eq_two_iff' (x : α) : Nat.card α = 2 ↔ exists! y, y != x
参数：x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Cardinal.toNat_eq_ofNat`：toNat_eq_ofNat {n : Nat} [Nat.AtLeastTwo n] : t
oNat c = OfNat.ofNat n ↔ c = OfNat.ofNat n
· 使用定理 `Cardinal.mk_eq_two_iff'`：mk_eq_two_iff' (x : α) : #α = 2 ↔ exists! y, y 
!= x
-/
theorem card_eq_two_iff' (x : α) : Nat.card α = 2 ↔ ∃! y, y ≠ x :=
  toNat_eq_ofNat.trans (mk_eq_two_iff' x)

@[simp]
/-
**Nat.card_subtype_true** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：card_subtype_true : Nat.card {_a : α // True} = Nat.card α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `trivial`：True
-/
theorem card_subtype_true : Nat.card {_a : α // True} = Nat.card α :=
  card_congr <| Equiv.subtypeUnivEquiv fun _ => trivial

@[simp]
/-
**Nat.card_sum** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：card_sum [Finite α] [Finite β] : Nat.card (α oplus β) = Nat.card α + Nat.c
ard β
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_sum`：Fintype.card_sum [Fintype α] [Fintype β] : Fintype.car
d (α oplus β) = Fintype.card α + Fintype.card β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_sum [Finite α] [Finite β] : Nat.card (α ⊕ β) = Nat.card α + Nat.card β := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_sum]

@[simp]
/-
**Nat.card_prod** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：card_prod (α β : Type*) : Nat.card (α × β) = Nat.card α * Nat.card β
参数：α β : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_prod`：mk_prod (α : Type u) (β : Type v) : #(α × β) = lift.{v
, u} #α * lift.{u, v} #β
· 使用定理 `Cardinal.toNat_mul`：toNat_mul (x y : Cardinal) : toNat (x * y) = toNat x
 * toNat y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_prod (α β : Type*) : Nat.card (α × β) = Nat.card α * Nat.card β := by
  simp only [Nat.card, mk_prod, toNat_mul, toNat_lift]

@[simp]
/-
**Nat.card_ulift** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：card_ulift (α : Type*) : Nat.card (ULift α) = Nat.card α
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
-/
theorem card_ulift (α : Type*) : Nat.card (ULift α) = Nat.card α :=
  card_congr Equiv.ulift

@[simp]
/-
**Nat.card_plift** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：card_plift (α : Type*) : Nat.card (PLift α) = Nat.card α
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
-/
theorem card_plift (α : Type*) : Nat.card (PLift α) = Nat.card α :=
  card_congr Equiv.plift
/-
**Nat.card_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：card_sigma {β : α -> Type*} [Fintype α] [forall a, Finite (β a)] : Nat.car
d (Sigma β) = ∑ a, Nat.card (β a)
参数：β a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_sigma`：∀ {ι : Type u_8} {α : ι → Type u_7} [inst : Fintype 
ι] [inst_1 : (i : ι) → Fintype (α i)],   Fintype.card (Sigma α) = ∑ i, Fintype.c
ard (α i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_sigma {β : α → Type*} [Fintype α] [∀ a, Finite (β a)] :
    Nat.card (Sigma β) = ∑ a, Nat.card (β a) := by
  let _ (a : α) : Fintype (β a) := Fintype.ofFinite (β a)
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
/-
**Nat.card_pi** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：card_pi {β : α -> Type*} [Fintype α] : Nat.card (forall a, β a) = ∏ a, Nat
.card (β a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_pi`：mk_pi {ι : Type u} (α : ι -> Type v) : #(Π i, α i) = pro
d fun i => #(α i)
· 使用定理 `Cardinal.prod_eq_of_fintype`：prod_eq_of_fintype {α : Type u} [h : Fintyp
e α] (f : α -> Cardinal.{v}) : prod f = Cardinal.lift.{u} (∏ i, f i)
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_pi {β : α → Type*} [Fintype α] : Nat.card (∀ a, β a) = ∏ a, Nat.card (β a) := by
  simp_rw [Nat.card, mk_pi, prod_eq_of_fintype, toNat_lift, _root_.map_prod]
/-
**Nat.card_fun** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：card_fun [Finite α] : Nat.card (α -> β) = Nat.card β ^ Nat.card α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_pi`：card_pi {β : α -> Type*} [Fintype α] : Nat.card (forall a, 
β a) = ∏ a, Nat.card (β a)
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
-/
theorem card_fun [Finite α] : Nat.card (α → β) = Nat.card β ^ Nat.card α := by
  have := Fintype.ofFinite α
  rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card]

@[simp]
/-
**Nat.card_zmod** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：card_zmod (n : Nat) : Nat.card (ZMod n) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `ZMod.card`：card (n : Nat) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n
-/
theorem card_zmod (n : ℕ) : Nat.card (ZMod n) = n := by
  cases n
  · exact @Nat.card_eq_zero_of_infinite _ Int.infinite
  · rw [Nat.card_eq_fintype_card, ZMod.card]

end Nat

namespace Set
variable {s : Set α}

/-
**Set.card_singleton_prod** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：card_singleton_prod (a : α) (t : Set β) : Nat.card ({a} ×ˢ t) = Nat.card t
参数：a : α；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.singleton_prod`：singleton_prod : ({a} : Set α) ×ˢ t = Prod.mk a '' t
· 使用引理 `Nat.card_image_of_injective`：card_image_of_injective {f : α -> β} (hf : 
Injective f) (s : Set α) : Nat.card (f '' s) = Nat.card s
· 使用定理 `Prod.mk_right_injective`：mk_right_injective {α β : Type*} (a : α) : (mk 
a : β -> α × β).Injective
-/
lemma card_singleton_prod (a : α) (t : Set β) : Nat.card ({a} ×ˢ t) = Nat.card t := by
  rw [singleton_prod, Nat.card_image_of_injective (Prod.mk_right_injective a)]
/-
**Set.card_prod_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：card_prod_singleton (s : Set α) (b : β) : Nat.card (s ×ˢ {b}) = Nat.card s
参数：s : Set α；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.prod_singleton`：prod_singleton : s ×ˢ ({b} : Set β) = (fun a => (a, 
b)) '' s
· 使用引理 `Nat.card_image_of_injective`：card_image_of_injective {f : α -> β} (hf : 
Injective f) (s : Set α) : Nat.card (f '' s) = Nat.card s
· 使用定理 `Prod.mk_left_injective`：mk_left_injective {α β : Type*} (b : β) : (fun a
 => mk a b : α -> α × β).Injective
-/
lemma card_prod_singleton (s : Set α) (b : β) : Nat.card (s ×ˢ {b}) = Nat.card s := by
  rw [prod_singleton, Nat.card_image_of_injective (Prod.mk_left_injective b)]
/-
**Set.natCard_pos** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：natCard_pos (hs : s.Finite) : 0 < Nat.card s ↔ s.Nonempty
参数：hs : s.Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem natCard_pos (hs : s.Finite) : 0 < Nat.card s ↔ s.Nonempty := by
  simp [pos_iff_ne_zero, Nat.card_eq_zero, hs.to_subtype, nonempty_iff_ne_empty]

protected alias ⟨_, Nonempty.natCard_pos⟩ := natCard_pos
/-
**Set.natCard_graphOn** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：natCard_graphOn (s : Set α) (f : α -> β) : Nat.card (s.graphOn f) = Nat.ca
rd s
参数：s : Set α；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.card_image_of_injOn`：card_image_of_injOn {f : α -> β} (hf : s.InjOn 
f) : Nat.card (f '' s) = Nat.card s
· 使用引理 `Set.fst_injOn_graph`：fst_injOn_graph : (s.graphOn f).InjOn Prod.fst
· 使用引理 `Set.image_fst_graphOn`：image_fst_graphOn (f : α -> β) (s : Set α) : Prod
.fst '' graphOn f s = s
-/
lemma natCard_graphOn (s : Set α) (f : α → β) : Nat.card (s.graphOn f) = Nat.card s := by
  rw [← Nat.card_image_of_injOn fst_injOn_graph, image_fst_graphOn]

end Set


namespace ENat

/-- `ENat.card α` is the cardinality of `α` as an extended natural number.
  If `α` is infinite, `ENat.card α = ⊤`. -/
/-
**ENat.card** 是 Mathlib 中的一个定义，位于命名空间 `ENat`。
形式化陈述：card (α : Type*) : Nat∞
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ENat.card α` is the cardinality of `α` as an extended natural number.
  If `α` is infinite, `ENat.card α = ⊤`.
-/
def card (α : Type*) : ℕ∞ :=
  toENat (mk α)

@[simp]
/-
**ENat.card_eq_coe_fintype_card** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：card_eq_coe_fintype_card [Fintype α] : card α = Fintype.card α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_eq_coe_fintype_card [Fintype α] : card α = Fintype.card α := by
  simp [card]

@[simp high]
/-
**ENat.card_eq_top_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：card_eq_top_of_infinite [Infinite α] : card α = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem card_eq_top_of_infinite [Infinite α] : card α = ⊤ := by
  simp only [card, toENat_eq_top, aleph0_le_mk]
/-
**ENat.card_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {α : Type u_1}, ENat.card α = ⊤ ↔ Infinite α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma card_eq_top : card α = ⊤ ↔ Infinite α := by simp [card, aleph0_le_mk_iff]
/-
**ENat.card_lt_top_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {α : Type u_1} [Finite α], ENat.card α < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
@[simp high] theorem card_lt_top_of_finite [Finite α] : card α < ⊤ := by simp [card]
/-
**ENat.card_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {α : Type u_1}, ENat.card α < ⊤ ↔ Finite α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem card_lt_top : card α < ⊤ ↔ Finite α := by simp [card, lt_aleph0_iff_finite]

@[simp]
/-
**ENat.card_sum** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：card_sum (α β : Type*) : card (α oplus β) = card α + card β
参数：α β : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_sum`：mk_sum (α : Type u) (β : Type v) : #(α oplus β) = lift.
{v, u} #α + lift.{u, v} #β
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.toENat_lift`：toENat_lift : toENat (lift.{v} c) = toENat c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_sum (α β : Type*) :
    card (α ⊕ β) = card α + card β := by
  simp only [card, mk_sum, map_add, toENat_lift]
/-
**ENat.card_congr** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：card_congr {α β : Type*} (f : α ≃ β) : card α = card β
参数：f : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.toENat_congr`：toENat_congr {α : Type u} {β : Type v} (e : α ≃ β
) : toENat #α = toENat #β
-/
theorem card_congr {α β : Type*} (f : α ≃ β) : card α = card β :=
  Cardinal.toENat_congr f
/-
**ENat.card_ulift** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (α : Type u_3), ENat.card (ULift.{u_4, u_3} α) = ENat.card α
参数：α : Type u_3；ULift.{u_4, u_3} α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.card_congr`：card_congr {α β : Type*} (f : α ≃ β) : card α = card β
-/
@[simp] lemma card_ulift (α : Type*) : card (ULift α) = card α := card_congr Equiv.ulift
/-
**ENat.card_plift** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (α : Type u_3), ENat.card (PLift α) = ENat.card α
参数：α : Type u_3；PLift α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.card_congr`：card_congr {α β : Type*} (f : α ≃ β) : card α = card β
-/
@[simp] lemma card_plift (α : Type*) : card (PLift α) = card α := card_congr Equiv.plift
/-
**ENat.card_image_of_injOn** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：card_image_of_injOn {α β : Type*} {f : α -> β} {s : Set α} (h : Set.InjOn 
f s) : card (f '' s) = card s
参数：h : Set.InjOn f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.card_congr`：card_congr {α β : Type*} (f : α ≃ β) : card α = card β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem card_image_of_injOn {α β : Type*} {f : α → β} {s : Set α} (h : Set.InjOn f s) :
    card (f '' s) = card s :=
  card_congr (Equiv.Set.imageOfInjOn f s h).symm
/-
**ENat.card_image_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：card_image_of_injective {α β : Type*} (f : α -> β) (s : Set α) (h : Functi
on.Injective f) : card (f '' s) = card s
参数：f : α -> β；s : Set α；h : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.card_image_of_injOn`：card_image_of_injOn {α β : Type*} {f : α -> β}
 {s : Set α} (h : Set.InjOn f s) : card (f '' s) = card s
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
-/
theorem card_image_of_injective {α β : Type*} (f : α → β) (s : Set α)
    (h : Function.Injective f) : card (f '' s) = card s := card_image_of_injOn h.injOn
/-
**ENat.card_le_card_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：card_le_card_of_injective {α β : Type*} {f : α -> β} (hf : Injective f) : 
card α <= card β
参数：hf : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.card_ulift`：∀ (α : Type u_3), ENat.card (ULift.{u_4, u_3} α) = ENat
.card α
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
· 使用定理 `GaloisCoinsertion.gc`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [i
nst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisCoinsertion l u), Ga
loisConnec…
· 使用引理 `Cardinal.lift_mk_le_lift_mk_of_injective`：lift_mk_le_lift_mk_of_injectiv
e {α : Type u} {β : Type v} {f : α -> β} (hf : Injective f) : Cardinal.lift.{v} 
(#α) <= Cardinal.lift.{u} (#β)
-/
lemma card_le_card_of_injective {α β : Type*} {f : α → β} (hf : Injective f) : card α ≤ card β := by
  rw [← card_ulift α, ← card_ulift β]
  exact Cardinal.gciENat.gc.monotone_u <| Cardinal.lift_mk_le_lift_mk_of_injective hf

@[deprecated natCast_le_toENat (since := "2026-02-17")]
/-
**ENat._root_.Cardinal.natCast_le_toENat_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Cardinal.natCast_le_toENat_iff {n : ℕ} {c : Cardinal} :
    ↑n ≤ toENat c ↔ ↑n ≤ c := by
  rw [← toENat_nat n, toENat_le_iff_of_le_aleph0 natCast_le_aleph0]

@[deprecated toENat_le_natCast (since := "2026-02-17")]
/-
**ENat._root_.Cardinal.toENat_le_natCast_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Cardinal.toENat_le_natCast_iff {c : Cardinal} {n : ℕ} :
    toENat c ≤ n ↔ c ≤ n := by simp

@[deprecated natCast_eq_toENat (since := "2026-02-17")]
/-
**ENat._root_.Cardinal.natCast_eq_toENat_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Cardinal.natCast_eq_toENat_iff {n : ℕ} {c : Cardinal} :
    ↑n = toENat c ↔ ↑n = c := by
  rw [le_antisymm_iff, le_antisymm_iff, Cardinal.toENat_le_natCast, Cardinal.natCast_le_toENat]

@[deprecated toENat_eq_natCast (since := "2026-02-17")]
/-
**ENat._root_.Cardinal.toENat_eq_natCast_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Cardinal.toENat_eq_natCast_iff {c : Cardinal} {n : ℕ} :
    Cardinal.toENat c = n ↔ c = n := by simp

@[deprecated natCast_lt_toENat (since := "2026-02-17")]
/-
**ENat._root_.Cardinal.natCast_lt_toENat_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Cardinal.natCast_lt_toENat_iff {n : ℕ} {c : Cardinal} :
    ↑n < toENat c ↔ ↑n < c := by
  simp only [← not_le, Cardinal.toENat_le_natCast]

@[deprecated toENat_lt_natCast (since := "2026-02-17")]
/-
**ENat._root_.Cardinal.toENat_lt_natCast_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Cardinal.toENat_lt_natCast_iff {n : ℕ} {c : Cardinal} :
    toENat c < ↑n ↔ c < ↑n := by
  simp only [← not_le, Cardinal.natCast_le_toENat]
/-
**ENat.card_eq_zero_iff_empty** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：card_eq_zero_iff_empty (α : Type*) : card α = 0 ↔ IsEmpty α
参数：α : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_eq_zero_iff`：mk_eq_zero_iff {α : Type u} : #α = 0 ↔ IsEmpty 
α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem card_eq_zero_iff_empty (α : Type*) : card α = 0 ↔ IsEmpty α := by
  rw [← Cardinal.mk_eq_zero_iff]
  simp [card]
/-
**ENat.card_ne_zero_iff_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：card_ne_zero_iff_nonempty (α : Type*) : card α != 0 ↔ Nonempty α
参数：α : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem card_ne_zero_iff_nonempty (α : Type*) : card α ≠ 0 ↔ Nonempty α := by
  simp [card_eq_zero_iff_empty]
/-
**ENat.card_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {α : Type u_1} [Nonempty α], ENat.card α ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENat.card_ne_zero_iff_nonempty`：card_ne_zero_iff_nonempty (α : Type*) : 
card α != 0 ↔ Nonempty α
-/
@[simp] lemma card_ne_zero [Nonempty α] : card α ≠ 0 := (card_ne_zero_iff_nonempty _).2 ‹_›
/-
**ENat.card_pos_iff_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：card_pos_iff_nonempty (α : Type*) : 0 < card α ↔ Nonempty α
参数：α : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `ENat.card_ne_zero_iff_nonempty`：card_ne_zero_iff_nonempty (α : Type*) : 
card α != 0 ↔ Nonempty α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem card_pos_iff_nonempty (α : Type*) : 0 < card α ↔ Nonempty α := by
  rw [pos_iff_ne_zero, card_ne_zero_iff_nonempty]
/-
**ENat.one_le_card_iff_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：one_le_card_iff_nonempty (α : Type*) : 1 <= card α ↔ Nonempty α
参数：α : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem one_le_card_iff_nonempty (α : Type*) : 1 ≤ card α ↔ Nonempty α := by
  simp [Order.one_le_iff_ne_zero, card_eq_zero_iff_empty]
/-
**ENat.card_pos** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {α : Type u_1} [Nonempty α], 0 < ENat.card α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] lemma card_pos [Nonempty α] : 0 < card α := by simp [pos_iff_ne_zero]
/-
**ENat.card_le_one_iff_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：card_le_one_iff_subsingleton (α : Type*) : card α <= 1 ↔ Subsingleton α
参数：α : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.le_one_iff_subsingleton`：le_one_iff_subsingleton {α : Type u} :
 #α <= 1 ↔ Subsingleton α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem card_le_one_iff_subsingleton (α : Type*) : card α ≤ 1 ↔ Subsingleton α := by
  rw [← le_one_iff_subsingleton]
  simp [card]
/-
**ENat.card_le_one** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {α : Type u_1} [Subsingleton α], ENat.card α ≤ 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma card_le_one [Subsingleton α] : card α ≤ 1 := by simpa [card_le_one_iff_subsingleton]
/-
**ENat.card_eq_one_iff_unique** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：card_eq_one_iff_unique {α : Type*} : card α = 1 ↔ Nonempty (Unique α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `unique_iff_subsingleton_and_nonempty`：unique_iff_subsingleton_and_nonemp
ty (α : Sort u) : Nonempty (Unique α) ↔ Subsingleton α ∧ Nonempty α
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `ENat.card_le_one_iff_subsingleton`：card_le_one_iff_subsingleton (α : Typ
e*) : card α <= 1 ↔ Subsingleton α
· 使用定理 `ENat.one_le_card_iff_nonempty`：one_le_card_iff_nonempty (α : Type*) : 1 
<= card α ↔ Nonempty α
-/
lemma card_eq_one_iff_unique {α : Type*} : card α = 1 ↔ Nonempty (Unique α) := by
  rw [unique_iff_subsingleton_and_nonempty α, le_antisymm_iff]
  exact and_congr (card_le_one_iff_subsingleton α) (one_le_card_iff_nonempty α)
/-
**ENat.one_lt_card_iff_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：one_lt_card_iff_nontrivial (α : Type*) : 1 < card α ↔ Nontrivial α
参数：α : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.one_lt_iff_nontrivial`：one_lt_iff_nontrivial {α : Type u} : 1 <
 #α ↔ Nontrivial α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Cardinal.natCast_lt_toENat`：∀ {c : Cardinal.{u}} {n : ℕ}, ↑n < Cardinal.
toENat c ↔ ↑n < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem one_lt_card_iff_nontrivial (α : Type*) : 1 < card α ↔ Nontrivial α := by
  rw [← Cardinal.one_lt_iff_nontrivial]
  conv_rhs => rw [← Nat.cast_one]
  rw [← natCast_lt_toENat]
  simp only [ENat.card, Nat.cast_one]
/-
**ENat.one_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {α : Type u_1} [Nontrivial α], 1 < ENat.card α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma one_lt_card [Nontrivial α] : 1 < card α := by simpa [one_lt_card_iff_nontrivial]
/-
**ENat.exists_ne_ne_of_three_le** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：exists_ne_ne_of_three_le (h : 3 <= ENat.card α) (x y : α) : exists z, z !=
 x ∧ z != y
参数：h : 3 <= ENat.card α；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Cardinal.exists_ne_ne_of_three_le`：exists_ne_ne_of_three_le {α : Type*} 
(h : 3 <= #α) (x y : α) : exists z : α, z != x ∧ z != y
-/
lemma exists_ne_ne_of_three_le (h : 3 ≤ ENat.card α) (x y : α) : ∃ z, z ≠ x ∧ z ≠ y :=
  Cardinal.exists_ne_ne_of_three_le (by simpa [ENat.card] using h) x y

@[simp]
/-
**ENat.card_prod** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：card_prod (α β : Type*) : card (α × β) = card α * card β
参数：α β : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_prod`：mk_prod (α : Type u) (β : Type v) : #(α × β) = lift.{v
, u} #α * lift.{u, v} #β
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.toENat_lift`：toENat_lift : toENat (lift.{v} c) = toENat c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_prod (α β : Type*) : card (α × β) = card α * card β := by
  simp [ENat.card]

@[simp]
/-
**ENat.card_fun** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：card_fun {α β : Type*} : card (α -> β) = card β ^ card α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.card_eq_coe_fintype_card`：card_eq_coe_fintype_card [Fintype α] : ca
rd α = Fintype.card α
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENat.card_eq_zero_iff_empty`：card_eq_zero_iff_empty (α : Type*) : card α
 = 0 ↔ IsEmpty α
· 使用引理 `ENat.epow_zero`：epow_zero : x ^ (0 : Nat∞) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `Fintype.card_pi`：∀ {ι : Type u_4} {α : ι → Type u_6} [inst : DecidableEq
 ι] [inst_1 : Fintype ι] [inst_2 : (i : ι) → Fintype (α i)],   Fintype.card ((i 
: ι) …
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `ENat.card_eq_top_of_infinite`：card_eq_top_of_infinite [Infinite α] : car
d α = ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ENat.top_epow`：top_epow (h : y != 0) : (⊤ : Nat∞) ^ y = ⊤
· 使用定理 `ENat.card_ne_zero_iff_nonempty`：card_ne_zero_iff_nonempty (α : Type*) : 
card α != 0 ↔ Nonempty α
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `Order.lt_one_iff`：lt_one_iff : x < 1 ↔ x = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用引理 `ENat.zero_epow_top`：zero_epow_top : (0 : Nat∞) ^ (⊤ : Nat∞) = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `ENat.one_epow`：one_epow : (1 : Nat∞) ^ y = 1
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
（共 40 条，此处仅展示前 30 条）
-/
lemma card_fun {α β : Type*} : card (α → β) = card β ^ card α := by
  classical
  rcases isEmpty_or_nonempty α with α_emp | α_emp
  · simp [(card_eq_zero_iff_empty α).2 α_emp]
  rcases finite_or_infinite α
  · rcases finite_or_infinite β
    · let := Fintype.ofFinite α
      let := Fintype.ofFinite β
      simp
    · simp only [card_eq_top_of_infinite]
      rw [top_epow]
      rwa [card_ne_zero_iff_nonempty]
  · rw [card_eq_top_of_infinite (α := α)]
    rcases lt_trichotomy (card β) 1 with b_0 | b_1 | b_2
    · rw [Order.lt_one_iff, card_eq_zero_iff_empty] at b_0
      rw [(card_eq_zero_iff_empty β).2 b_0, zero_epow_top, card_eq_zero_iff_empty]
      simp [b_0]
    · rw [b_1, one_epow]
      apply le_antisymm
      · let := (card_le_one_iff_subsingleton β).1 b_1.le
        exact (card_le_one_iff_subsingleton (α → β)).2 Pi.instSubsingleton
      · let := (one_le_card_iff_nonempty β).1 b_1.ge
        exact (one_le_card_iff_nonempty (α → β)).2 Pi.instNonempty
    · rw [epow_top b_2, card_eq_top]
      rw [one_lt_card_iff_nontrivial β] at b_2
      exact Pi.infinite_of_left

end ENat

