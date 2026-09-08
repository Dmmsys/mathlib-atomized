/-
Copyright (c) 2025 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# `Finset.lcm` lemmas

## Tags

finset, lcm, prod, coprime, Rat.den
-/

public section

namespace Finset

variable {ι α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

/-
**Finset.lcm_dvd_prod** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：lcm_dvd_prod (s : Finset ι) (f : ι -> α) : s.lcm f ∣ s.prod f
参数：s : Finset ι；f : ι -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.lcm_dvd`：lcm_dvd {a : α} : (forall b in s, f b ∣ a) -> s.lcm f ∣ 
a
· 使用定理 `Finset.dvd_prod_of_mem`：dvd_prod_of_mem (f : ι -> M) {a : ι} {s : Finset
 ι} (ha : a in s) : f a ∣ ∏ i in s, f i
-/
theorem lcm_dvd_prod (s : Finset ι) (f : ι → α) : s.lcm f ∣ s.prod f :=
  lcm_dvd fun _ ↦ dvd_prod_of_mem _
/-
**Finset.associated_lcm_prod** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：associated_lcm_prod {s : Finset ι} {f : ι -> α} (h : Set.Pairwise s <| IsR
elPrime.onFun f) : Associated (s.lcm f) (s.prod f)
参数：h : Set.Pairwise s <| IsRelPrime.onFun f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `associated_of_dvd_dvd`：associated_of_dvd_dvd [MonoidWithZero M] [IsLeftC
ancelMulZero M] {a b : M} (hab : a ∣ b) (hba : b ∣ a) : a ~ᵤ b
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `GCDMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : CommMonoidWithZero
 α} [self : GCDMonoid α], IsCancelMulZero α
· 使用定理 `Finset.lcm_dvd_prod`：lcm_dvd_prod (s : Finset ι) (f : ι -> α) : s.lcm f 
∣ s.prod f
· 使用定理 `Finset.prod_dvd_of_isRelPrime`：Finset.prod_dvd_of_isRelPrime : (t : Set 
I).Pairwise (IsRelPrime on s) -> (forall i in t, s i ∣ z) -> (∏ x in t, s x) ∣ z
· 使用定理 `instDecompositionMonoidOfIsGCDMonoid`：∀ {α : Type u_1} [inst : CommMonoi
dWithZero α] [h : IsGCDMonoid α], DecompositionMonoid α
· 使用定理 `instIsGCDMonoidOfGCDMonoid`：∀ {α : Type u_1} [inst : CommMonoidWithZero 
α] [GCDMonoid α], IsGCDMonoid α
· 使用定理 `Finset.dvd_lcm`：dvd_lcm {b : β} (hb : b in s) : f b ∣ s.lcm f
-/
theorem associated_lcm_prod {s : Finset ι} {f : ι → α} (h : Set.Pairwise s <| IsRelPrime.onFun f) :
    Associated (s.lcm f) (s.prod f) :=
  associated_of_dvd_dvd (s.lcm_dvd_prod f) (s.prod_dvd_of_isRelPrime h fun _ ↦ dvd_lcm)
/-
**Finset.lcm_eq_prod** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：lcm_eq_prod {s : Finset ι} {f : ι -> Nat} (h : Set.Pairwise s <| Nat.Copri
me.onFun f) : s.lcm f = s.prod f
参数：h : Set.Pairwise s <| Nat.Coprime.onFun f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Associated.eq_of_normalized`：Associated.eq_of_normalized {a b : α} (h : 
Associated a b) (ha : normalize a = a) (hb : normalize b = b) : a = b
· 使用定理 `Finset.associated_lcm_prod`：associated_lcm_prod {s : Finset ι} {f : ι ->
 α} (h : Set.Pairwise s <| IsRelPrime.onFun f) : Associated (s.lcm f) (s.prod f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.coprime_iff_isRelPrime`：coprime_iff_isRelPrime {m n : Nat} : m.Copri
me n ↔ IsRelPrime m n
· 使用定理 `normalize_eq`：normalize_eq (x : α) : normalize x = x
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem lcm_eq_prod {s : Finset ι} {f : ι → ℕ} (h : Set.Pairwise s <| Nat.Coprime.onFun f) :
    s.lcm f = s.prod f := by
  rw [show Nat.Coprime = IsRelPrime by ext; exact Nat.coprime_iff_isRelPrime] at h
  exact associated_lcm_prod h |>.eq_of_normalized (normalize_eq _) (normalize_eq _)

/-- An analogue of `Nat.factorization_lcm` for `Finset.lcm`. -/
/-
**Finset.factorization_lcm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：factorization_lcm {f : ι -> Nat} {s : Finset ι} (hf : forall k in s, f k !
= 0) (p : Nat) : (s.lcm f).factorization p = s.sup fun a => (f a).factorization 
p
参数：hf : forall k in s, f k != 0；p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.factorization_one`：factorization_one : factorization 1 = 0
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.lcm_insert`：lcm_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).lcm f = GCDMonoid.lcm (f b) (s.lcm f)
· 使用定理 `Nat.factorization_lcm`：factorization_lcm {a b : Nat} (ha : a != 0) (hb :
 b != 0) : (a.lcm b).factorization = a.factorization ⊔ b.factorization
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Finset.sup_insert`：sup_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).sup f = f b ⊔ s.sup f

--- 原说明 ---
An analogue of `Nat.factorization_lcm` for `Finset.lcm`.
-/
theorem factorization_lcm {f : ι → ℕ} {s : Finset ι} (hf : ∀ k ∈ s, f k ≠ 0) (p : ℕ) :
    (s.lcm f).factorization p = s.sup fun a ↦ (f a).factorization p := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert _ _ _ _ => simp_all [lcm_eq_nat_lcm, Nat.factorization_lcm]

namespace Rat

/-
**Finset.Rat.den_sum_dvd_lcm_den** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Rat`。
形式化陈述：den_sum_dvd_lcm_den {ι : Type*} (s : Finset ι) (f : ι -> Rat) : (∑ i in s,
 f i).den ∣ s.lcm (fun i => (f i).den)
参数：s : Finset ι；f : ι -> Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Finset.lcm_insert`：lcm_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).lcm f = GCDMonoid.lcm (f b) (s.lcm f)
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Rat.add_den_dvd_lcm`：add_den_dvd_lcm (q₁ q₂ : Rat) : (q₁ + q₂).den ∣ q₁.
den.lcm q₂.den
· 使用定理 `lcm_dvd_lcm`：lcm_dvd_lcm [GCDMonoid α] {a b c d : α} (hab : a ∣ b) (hcd 
: c ∣ d) : lcm a c ∣ lcm b d
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
-/
theorem den_sum_dvd_lcm_den {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    (∑ i ∈ s, f i).den ∣ s.lcm (fun i ↦ (f i).den) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert _ _ has ih =>
    rw [Finset.sum_insert has, Finset.lcm_insert]
    exact (Rat.add_den_dvd_lcm _ _).trans (lcm_dvd_lcm dvd_rfl ih)
/-
**Finset.Rat.den_sum_dvd_prod_den** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Rat`。
形式化陈述：den_sum_dvd_prod_den {ι : Type*} (s : Finset ι) (f : ι -> Rat) : (∑ i in s
, f i).den ∣ ∏ i in s, (f i).den
参数：s : Finset ι；f : ι -> Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Finset.Rat.den_sum_dvd_lcm_den`：den_sum_dvd_lcm_den {ι : Type*} (s : Fin
set ι) (f : ι -> Rat) : (∑ i in s, f i).den ∣ s.lcm (fun i => (f i).den)
· 使用定理 `Finset.lcm_dvd_prod`：lcm_dvd_prod (s : Finset ι) (f : ι -> α) : s.lcm f 
∣ s.prod f
-/
theorem den_sum_dvd_prod_den {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    (∑ i ∈ s, f i).den ∣ ∏ i ∈ s, (f i).den :=
  (den_sum_dvd_lcm_den s f).trans <| s.lcm_dvd_prod _
/-
**Finset.Rat.den_prod_dvd_prod_den** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Rat`。
形式化陈述：den_prod_dvd_prod_den {ι : Type*} (s : Finset ι) (f : ι -> Rat) : (∏ i in 
s, f i).den ∣ ∏ i in s, (f i).den
参数：s : Finset ι；f : ι -> Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Rat.mul_den_dvd`：mul_den_dvd (q₁ q₂ : Rat) : (q₁ * q₂).den ∣ q₁.den * q₂
.den
· 使用定理 `mul_dvd_mul_left`：mul_dvd_mul_left (a : α) (h : b ∣ c) : a * b ∣ a * c
-/
theorem den_prod_dvd_prod_den {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    (∏ i ∈ s, f i).den ∣ ∏ i ∈ s, (f i).den := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert _ _ has ih =>
    simp_rw [Finset.prod_insert has]
    exact (Rat.mul_den_dvd ..).trans <| mul_dvd_mul_left _ ih

end Rat

end Finset

