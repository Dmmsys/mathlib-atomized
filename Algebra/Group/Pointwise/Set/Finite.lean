/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Data.Finite.Prod
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-! # Finiteness lemmas for pointwise operations on sets -/

public section

assert_not_exists MulAction MonoidWithZero

open scoped Pointwise

variable {F α β γ : Type*}

namespace Set

section One

variable [One α]

@[to_additive (attr := simp)]
/-
**Set.finite_one** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：finite_one : (1 : Set α).Finite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
-/
theorem finite_one : (1 : Set α).Finite :=
  finite_singleton _

end One

section Mul

variable [Mul α] {s t : Set α}

@[to_additive]
/-
**Set.Finite.mul** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_2} [inst : Mul α] {s t : Set α}, s.Finite → t.Finite → (s * 
t).Finite
参数：s * t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.image2`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : S
et α} {t : Set β} (f : α → β → γ),   s.Finite → t.Finite → (Set.image2 f s t).Fi
nite
-/
theorem Finite.mul : s.Finite → t.Finite → (s * t).Finite :=
  Finite.image2 _

/-- Multiplication preserves finiteness. -/
@[to_additive /-- Addition preserves finiteness. -/]
/-
**Set.fintypeMul** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：fintypeMul [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t] : Fintype
 (s * t)
参数：s t : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication preserves finiteness.
-/
instance fintypeMul [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t] : Fintype (s * t) :=
  Set.fintypeImage2 _ _ _

end Mul

section Monoid

variable [Monoid α] {s t : Set α}

@[to_additive]
/-
**Set.decidableMemMul** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：decidableMemMul [Fintype α] [DecidableEq α] [DecidablePred (· in s)] [Deci
dablePred (· in t)] : DecidablePred (· in s * t)
参数：· in s；· in t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableMemMul [Fintype α] [DecidableEq α] [DecidablePred (· ∈ s)]
    [DecidablePred (· ∈ t)] : DecidablePred (· ∈ s * t) := fun _ ↦ decidable_of_iff _ mem_mul.symm

@[to_additive]
/-
**Set.decidableMemPow** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：decidableMemPow [Fintype α] [DecidableEq α] [DecidablePred (· in s)] (n : 
Nat) : DecidablePred (· in s ^ n)
参数：· in s；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableMemPow [Fintype α] [DecidableEq α] [DecidablePred (· ∈ s)] (n : ℕ) :
    DecidablePred (· ∈ s ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero, mem_one]
    infer_instance
  | succ n ih =>
    rw [pow_succ]
    infer_instance

end Monoid

section SMul

variable [SMul α β] {s : Set α} {t : Set β}

@[to_additive]
/-
**Set.Finite.smul** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s : Set α} {t : Set β},
 s.Finite → t.Finite → (s • t).Finite
参数：s • t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.image2`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : S
et α} {t : Set β} (f : α → β → γ),   s.Finite → t.Finite → (Set.image2 f s t).Fi
nite
-/
theorem Finite.smul : s.Finite → t.Finite → (s • t).Finite :=
  Finite.image2 _

end SMul

section HasSMulSet

variable [SMul α β] {s : Set β} {a : α}

@[to_additive]
/-
**Set.Finite.smul_set** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s : Set β} {a : α}, s.F
inite → (a • s).Finite
参数：a • s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
-/
theorem Finite.smul_set : s.Finite → (a • s).Finite :=
  Finite.image _

@[to_additive]
/-
**Set.Infinite.of_smul_set** 是 Mathlib 中的一个定理，位于命名空间 `Set.Infinite`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s : Set β} {a : α}, (a 
• s).Infinite → s.Infinite
参数：a • s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Infinite.of_image`：∀ {α : Type u} {β : Type v} (f : α → β) {s : Set 
α}, (f '' s).Infinite → s.Infinite
-/
theorem Infinite.of_smul_set : (a • s).Infinite → s.Infinite :=
  Infinite.of_image _

end HasSMulSet

section Vsub

variable [VSub α β] {s t : Set β}

/-
**Set.Finite.vsub** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : VSub α β] {s t : Set β}, s.Finite 
→ t.Finite → (s -ᵥ t).Finite
参数：s -ᵥ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.image2`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : S
et α} {t : Set β} (f : α → β → γ),   s.Finite → t.Finite → (Set.image2 f s t).Fi
nite
-/
theorem Finite.vsub (hs : s.Finite) (ht : t.Finite) : Set.Finite (s -ᵥ t) :=
  hs.image2 _ ht

end Vsub

section Cancel

variable [Mul α] [IsLeftCancelMul α] [IsRightCancelMul α] {s t : Set α}

@[to_additive]
/-
**Set.finite_mul** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：finite_mul : (s * t).Finite ↔ s.Finite ∧ t.Finite ∨ s = ∅ ∨ t = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.finite_image2`：finite_image2 (hfs : forall b in t, InjOn (f · b) s) 
(hft : forall a in s, InjOn (f a) t) : (image2 f s t).Finite ↔ s.Finite ∧ t.Fini
te ∨ s …
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `mul_left_injective`：mul_left_injective (a : G) : Function.Injective (· *
 a)
· 使用定理 `mul_right_injective`：mul_right_injective (a : G) : Injective (a * ·)
-/
lemma finite_mul : (s * t).Finite ↔ s.Finite ∧ t.Finite ∨ s = ∅ ∨ t = ∅ :=
  finite_image2 (fun _ _ ↦ (mul_left_injective _).injOn) fun _ _ ↦ (mul_right_injective _).injOn

@[to_additive]
/-
**Set.infinite_mul** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：infinite_mul : (s * t).Infinite ↔ s.Infinite ∧ t.Nonempty ∨ t.Infinite ∧ s
.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.infinite_image2`：infinite_image2 (hfs : forall b in t, InjOn (fun a 
=> f a b) s) (hft : forall a in s, InjOn (f a) t) : (image2 f s t).Infinite ↔ s.
Infinite …
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `mul_left_injective`：mul_left_injective (a : G) : Function.Injective (· *
 a)
· 使用定理 `mul_right_injective`：mul_right_injective (a : G) : Injective (a * ·)
-/
lemma infinite_mul : (s * t).Infinite ↔ s.Infinite ∧ t.Nonempty ∨ t.Infinite ∧ s.Nonempty :=
  infinite_image2 (fun _ _ => (mul_left_injective _).injOn) fun _ _ => (mul_right_injective _).injOn

end Cancel

section InvolutiveInv
variable [InvolutiveInv α] {s : Set α}

/-
**Set.finite_inv** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} [inst : InvolutiveInv α] {s : Set α}, s⁻¹.Finite ↔ s.Fini
te
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
· 使用定理 `Set.finite_image_iff`：finite_image_iff {s : Set α} {f : α -> β} (hi : In
jOn f s) : (f '' s).Finite ↔ s.Finite
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `inv_injective`：inv_injective : Function.Injective (Inv.inv : G -> G)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_additive (attr := simp)] lemma finite_inv : s⁻¹.Finite ↔ s.Finite := by
  rw [← image_inv_eq_inv, finite_image_iff inv_injective.injOn]
/-
**Set.infinite_inv** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} [inst : InvolutiveInv α] {s : Set α}, s⁻¹.Infinite ↔ s.In
finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Set.finite_inv`：∀ {α : Type u_2} [inst : InvolutiveInv α] {s : Set α}, s
⁻¹.Finite ↔ s.Finite
-/
@[to_additive (attr := simp)] lemma infinite_inv : s⁻¹.Infinite ↔ s.Infinite := finite_inv.not

@[to_additive] alias ⟨Finite.of_inv, Finite.inv⟩ := finite_inv

end InvolutiveInv

section Div
variable [Div α] {s t : Set α}

/-
**Set.Finite.div** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_2} [inst : Div α] {s t : Set α}, s.Finite → t.Finite → (s / 
t).Finite
参数：s / t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.image2`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : S
et α} {t : Set β} (f : α → β → γ),   s.Finite → t.Finite → (Set.image2 f s t).Fi
nite
-/
@[to_additive] lemma Finite.div : s.Finite → t.Finite → (s / t).Finite := .image2 _

/-- Division preserves finiteness. -/
@[to_additive /-- Subtraction preserves finiteness. -/]
/-
**Set.fintypeDiv** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：fintypeDiv [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t] : Fintype
 (s / t)
参数：s t : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Division preserves finiteness.
-/
instance fintypeDiv [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t] : Fintype (s / t) :=
  Set.fintypeImage2 _ _ _

end Div

section Group

variable [Group α] {s t : Set α}

@[to_additive]
/-
**Set.finite_div** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：finite_div : (s / t).Finite ↔ s.Finite ∧ t.Finite ∨ s = ∅ ∨ t = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.finite_image2`：finite_image2 (hfs : forall b in t, InjOn (f · b) s) 
(hft : forall a in s, InjOn (f a) t) : (image2 f s t).Finite ↔ s.Finite ∧ t.Fini
te ∨ s …
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `div_left_injective`：div_left_injective : Function.Injective fun a => a /
 b
· 使用定理 `div_right_injective`：div_right_injective : Function.Injective fun a => b
 / a
-/
lemma finite_div : (s / t).Finite ↔ s.Finite ∧ t.Finite ∨ s = ∅ ∨ t = ∅ :=
  finite_image2 (fun _ _ ↦ div_left_injective.injOn) fun _ _ ↦ div_right_injective.injOn

@[to_additive]
/-
**Set.infinite_div** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：infinite_div : (s / t).Infinite ↔ s.Infinite ∧ t.Nonempty ∨ t.Infinite ∧ s
.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.infinite_image2`：infinite_image2 (hfs : forall b in t, InjOn (fun a 
=> f a b) s) (hft : forall a in s, InjOn (f a) t) : (image2 f s t).Infinite ↔ s.
Infinite …
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `div_left_injective`：div_left_injective : Function.Injective fun a => a /
 b
· 使用定理 `div_right_injective`：div_right_injective : Function.Injective fun a => b
 / a
-/
lemma infinite_div : (s / t).Infinite ↔ s.Infinite ∧ t.Nonempty ∨ t.Infinite ∧ s.Nonempty :=
  infinite_image2 (fun _ _ ↦ div_left_injective.injOn) fun _ _ ↦ div_right_injective.injOn

end Group

end Set

open Set

namespace Group

variable {G : Type*} [Group G] [Fintype G] (S : Set G)

@[to_additive]
/-
**Group.card_pow_eq_card_pow_card_univ** 是 Mathlib 中的一个定理，位于命名空间 `Group`。
形式化陈述：card_pow_eq_card_pow_card_univ [forall k : Nat, DecidablePred (· in S ^ k)
] : forall k, Fintype.card G <= k -> Fintype.card (↥(S ^ k)) = Fintype.card (↥(S
 ^ Fintype.card G))
参数：· in S ^ k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_pos`：card_pos [h : Nonempty α] : 0 < card α
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.empty_pow`：empty_pow (hn : n != 0) : (∅ : Set α) ^ n = ∅
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_le_of_injective`：card_le_of_injective (f : α -> β) (hf : Fu
nction.Injective f) : card α <= card β
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `mul_right_cancel`：mul_right_cancel : a * b = c * b -> a = c
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `monotone_nat_of_le_succ`：monotone_nat_of_le_succ {f : Nat -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
· 使用定理 `Set.mul_mem_mul`：mul_mem_mul : a in s -> b in t -> a * b in s * t
· 使用引理 `Nat.stabilises_of_monotone`：Nat.stabilises_of_monotone {f : Nat -> Nat} 
{b n : Nat} (hfmono : Monotone f) (hfb : forall m, f m <= b) (hfstab : forall m,
 f m = f (m + 1)…
· 使用定理 `set_fintype_card_le_univ`：set_fintype_card_le_univ [Fintype α] (s : Set 
α) [Fintype s] : Fintype.card s <= Fintype.card α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `Set.eq_of_subset_of_card_le`：eq_of_subset_of_card_le {s t : Set α} [Fint
ype s] [Fintype t] (hsub : s subseteq t) (hcard : Fintype.card t <= Fintype.card
 s) : s = t
· 使用定理 `Set.mul_subset_mul`：mul_subset_mul : s₁ subseteq t₁ -> s₂ subseteq t₂ ->
 s₁ * s₂ subseteq t₁ * t₂
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
（共 36 条，此处仅展示前 30 条）
-/
theorem card_pow_eq_card_pow_card_univ [∀ k : ℕ, DecidablePred (· ∈ S ^ k)] :
    ∀ k, Fintype.card G ≤ k → Fintype.card (↥(S ^ k)) = Fintype.card (↥(S ^ Fintype.card G)) := by
  have hG : 0 < Fintype.card G := Fintype.card_pos
  rcases S.eq_empty_or_nonempty with (rfl | ⟨a, ha⟩)
  · refine fun k hk ↦ Fintype.card_congr ?_
    rw [empty_pow (hG.trans_le hk).ne', empty_pow (ne_of_gt hG)]
  have key : ∀ (a) (s t : Set G) [Fintype s] [Fintype t],
      (∀ b : G, b ∈ s → b * a ∈ t) → Fintype.card s ≤ Fintype.card t := by
    refine fun a s t _ _ h ↦ Fintype.card_le_of_injective (fun ⟨b, hb⟩ ↦ ⟨b * a, h b hb⟩) ?_
    rintro ⟨b, hb⟩ ⟨c, hc⟩ hbc
    exact Subtype.ext (mul_right_cancel (Subtype.ext_iff.mp hbc))
  have mono : Monotone (fun n ↦ Fintype.card (↥(S ^ n)) : ℕ → ℕ) :=
    monotone_nat_of_le_succ fun n ↦ key a _ _ fun b hb ↦ Set.mul_mem_mul hb ha
  refine fun _ ↦ Nat.stabilises_of_monotone mono (fun n ↦ set_fintype_card_le_univ (S ^ n))
    fun n h ↦ le_antisymm (mono (n + 1).le_succ) (key a⁻¹ (S ^ (n + 2)) (S ^ (n + 1)) ?_)
  replace h₂ : S ^ n * {a} = S ^ (n + 1) := by
    have : Fintype (S ^ n * Set.singleton a) := by
      classical
      apply fintypeMul
    refine Set.eq_of_subset_of_card_le ?_ (le_trans (ge_of_eq h) ?_)
    · exact mul_subset_mul Set.Subset.rfl (Set.singleton_subset_iff.mpr ha)
    · convert! key a (S ^ n) (S ^ n * { a }) fun b hb ↦ Set.mul_mem_mul hb (Set.mem_singleton a)
  rw [pow_succ', ← h₂, ← mul_assoc, ← pow_succ', h₂, mul_singleton, forall_mem_image]
  intro x hx
  rwa [mul_inv_cancel_right]

end Group

