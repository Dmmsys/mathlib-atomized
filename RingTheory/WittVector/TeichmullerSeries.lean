/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.RingTheory.WittVector.Complete
public import Mathlib.RingTheory.WittVector.Teichmuller

/-!
# Teichmuller Series

Let `R` be a characteristic `p` perfect ring. In this file, we show that
every element `x` of the Witt vectors `𝕎 R` can be written as the
(`p`-adic) summation of Teichmuller series, namely
`∑ i, (teichmuller p
        (((frobeniusEquiv R p).symm ^ i) (x.coeff i)) * p ^ i)`

## Main theorems

* `WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff` : `p ^ (n + 1)` divides
  `x` minus the summation of the first `n + 1` terms of the Teichmuller series.
* `WittVector.eq_of_apply_teichmuller_eq` : Given a ring `S` such that `p` is nilpotent in `S`
  and two ring maps `f g : 𝕎 R →+* S`, if they coincide on the teichmuller representatives,
  then they are equal.

## TODO
Show that the Teichmuller series is unique.
-/

public section

open Ideal Quotient
namespace WittVector

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

local notation "𝕎" => WittVector p

variable {R : Type*} [CommRing R]

/-
**WittVector.sum_coeff_eq_coeff_sum** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：sum_coeff_eq_coeff_sum {α : Type*} {S : Finset α} (x : α -> 𝕎 R) (h : fora
ll (n : Nat), Subsingleton {r | r in S ∧ (x r).coeff n != 0}) (n : Nat) : (∑ s i
n S, x s).coeff n = ∑ (s in S), (x s).coeff n
参数：x : α -> 𝕎 R；h : forall (n : Nat), Subsingleton {r | r in S ∧ (x r).coeff n !
= 0}；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.zero_coeff`：zero_coeff (n : Nat) : (0 : 𝕎 R).coeff n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Finset.subset_insert`：∀ {α : Type u_1} [inst : DecidableEq α] (a : α) (s
 : Finset α), s ⊆ insert a s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subsingleton.allEq`：∀ {α : Sort u} [self : Subsingleton α] (a b : α), a 
= b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `WittVector.coeff_add_of_disjoint`：coeff_add_of_disjoint (x y : 𝕎 R) (h :
 forall n, x.coeff n = 0 ∨ y.coeff n = 0) : (x + y).coeff n = x.coeff n + y.coef
f n
-/
theorem sum_coeff_eq_coeff_sum {α : Type*} {S : Finset α} (x : α → 𝕎 R)
    (h : ∀ (n : ℕ), Subsingleton {r | r ∈ S ∧ (x r).coeff n ≠ 0}) (n : ℕ) :
    (∑ s ∈ S, x s).coeff n = ∑ (s ∈ S), (x s).coeff n := by
  classical
  induction S using Finset.induction generalizing n with
  | empty =>
    simp
  | insert a S' ha hind =>
    have : (∀ (n : ℕ), Subsingleton {r | r ∈ S' ∧ (x r).coeff n ≠ 0}) := by
      refine fun n ↦ ⟨fun b c ↦ ?_⟩
      ext
      exact congrArg (fun x ↦ x.1) <|
          (h n).allEq ⟨b.1, S'.subset_insert a b.2.1, b.2.2⟩ ⟨c.1, S'.subset_insert a c.2.1, c.2.2⟩
    replace hind := hind this
    simp only [ha, not_false_eq_true, Finset.sum_insert]
    have : ∀ (n : ℕ), (x a).coeff n = 0 ∨ (∑ s ∈ S', x s).coeff n = 0 := by
      simp only [hind]
      by_contra! ⟨m, hma, hmS'⟩
      have := Finset.sum_eq_zero.mt hmS'
      push Not at this
      choose b hb hb' using this
      have : a = b :=
        congrArg (fun x ↦ x.1) <|
          (h m).allEq ⟨a, S'.mem_insert_self a, hma⟩ ⟨b, S'.mem_insert_of_mem hb, hb'⟩
      exact ha (this ▸ hb)
    rw [coeff_add_of_disjoint n _ _ this, hind n]

variable [CharP R p]

@[simp]
/-
**WittVector.teichmuller_mul_pow_coeff** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：teichmuller_mul_pow_coeff (n : Nat) (x : R) : (teichmuller p x * p ^ n).co
eff n = x ^ p ^ n
参数：n : Nat；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `WittVector.mul_pow_charP_coeff_succ`：mul_pow_charP_coeff_succ [CharP R p
] (x : 𝕎 R) {m n : Nat} : (x * p ^ n).coeff (m + n) = x.coeff m ^ (p ^ n)
-/
theorem teichmuller_mul_pow_coeff (n : ℕ) (x : R) :
    (teichmuller p x * p ^ n).coeff n = x ^ p ^ n := by
  simpa using WittVector.mul_pow_charP_coeff_succ (teichmuller p x) (m := 0)
/-
**WittVector.teichmuller_mul_pow_coeff_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `WittVect
or`。
形式化陈述：teichmuller_mul_pow_coeff_of_ne (x : R) {m n : Nat} (h : m != n) : (teichm
uller p x * p ^ n).coeff m = 0
参数：x : R；h : m != n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_or_lt_of_ne`：∀ {a b : ℕ}, a ≠ b → a < b ∨ b < a
· 使用定理 `WittVector.mul_pow_charP_coeff_zero`：mul_pow_charP_coeff_zero [CharP R p
] (x : 𝕎 R) {m n : Nat} (h : m < n) : (x * p ^ n).coeff m = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `WittVector.mul_pow_charP_coeff_succ`：mul_pow_charP_coeff_succ [CharP R p
] (x : 𝕎 R) {m n : Nat} : (x * p ^ n).coeff (m + n) = x.coeff m ^ (p ^ n)
· 使用定理 `WittVector.teichmuller_coeff_pos`：∀ (p : ℕ) {R : Type u_1} [hp : Fact (N
at.Prime p)] [inst : CommRing R] (r : R) (n : ℕ),   0 < n → ((WittVector.teichmu
ller p) r).coeff n = 0
· 使用定理 `Nat.zero_lt_sub_of_lt`：∀ {i a : ℕ}, i < a → 0 < a - i
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem teichmuller_mul_pow_coeff_of_ne (x : R)
    {m n : ℕ} (h : m ≠ n) : (teichmuller p x * p ^ n).coeff m = 0 := by
  cases Nat.lt_or_lt_of_ne h with
  | inl h =>
    exact WittVector.mul_pow_charP_coeff_zero (teichmuller p x) h
  | inr h =>
    rw [← Nat.sub_add_cancel h.le, WittVector.mul_pow_charP_coeff_succ (teichmuller p x),
      WittVector.teichmuller_coeff_pos p x (m - n) (Nat.zero_lt_sub_of_lt h), zero_pow]
    simp [Nat.Prime.ne_zero Fact.out]

variable [PerfectRing R p]

/--
`p ^ (n + 1)` divides
`x` minus the summation of the first `n + 1` terms of the Teichmuller series.
-/
/-
**WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff** 是 Mathlib 中的一
个定理，位于命名空间 `WittVector`。
形式化陈述：dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff (x : 𝕎 R) (n : Nat) : 
(p : 𝕎 R) ^ (n + 1) ∣ x - ∑ (i <= n), (teichmuller p (((_root_.frobeniusEquiv R 
p).symm ^ i) (x.coeff i)) * p ^ i)
参数：x : 𝕎 R；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `WittVector.mem_span_p_pow_iff_le_coeff_eq_zero`：mem_span_p_pow_iff_le_co
eff_eq_zero (x : 𝕎 k) (n : Nat) : x in (Ideal.span {(p ^ n : 𝕎 k)}) ↔ forall m, 
m < n -> x.coeff m = 0
· 使用定理 `WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero`：le_coeff_eq_iff_le_sub_
coeff_eq_zero {x y : 𝕎 k} {n : Nat} : (forall i < n, x.coeff i = y.coeff i) ↔ fo
rall i < n, (x - y).coeff i = 0
· 使用定理 `WittVector.sum_coeff_eq_coeff_sum`：sum_coeff_eq_coeff_sum {α : Type*} {S
 : Finset α} (x : α -> 𝕎 R) (h : forall (n : Nat), Subsingleton {r | r in S ∧ (x
 r).coeff n != 0}) (n :…
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Not.imp_symm`：Not.imp_symm : (¬a -> b) -> ¬b -> a
· 使用定理 `WittVector.teichmuller_mul_pow_coeff_of_ne`：teichmuller_mul_pow_coeff_of
_ne (x : R) {m n : Nat} (h : m != n) : (teichmuller p x * p ^ n).coeff m = 0
· 使用定理 `Finset.sum_eq_add_sum_sdiff_singleton_of_mem`：∀ {ι : Type u_1} {M : Type
 u_3} [inst : AddCommMonoid M] [inst_1 : DecidableEq ι] {s : Finset ι} {i : ι}, 
  i ∈ s → ∀ (f : ι → M), ∑ x ∈ s, …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iic a ↔ x ≤ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Ne.intro`：∀ {α : Sort u} {a b : α}, (a = b → False) → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `RingAut.coe_pow`：coe_pow (f : R ≃+* R) (n : Nat) : ⇑(f ^ n) = f^[n]
· 使用定理 `WittVector.teichmuller_mul_pow_coeff`：teichmuller_mul_pow_coeff (n : Nat
) (x : R) : (teichmuller p x * p ^ n).coeff n = x ^ p ^ n
· 使用定理 `iterate_frobeniusEquiv_symm_pow_p_pow`：iterate_frobeniusEquiv_symm_pow_p
_pow (x : R) (n : Nat) : ((frobeniusEquiv R p).symm^[n]) x ^ (p ^ n) = x
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`p ^ (n + 1)` divides
`x` minus the summation of the first `n + 1` terms of the Teichmuller series.
-/
theorem dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff (x : 𝕎 R) (n : ℕ) :
    (p : 𝕎 R) ^ (n + 1) ∣ x - ∑ (i ≤ n), (teichmuller p
        (((_root_.frobeniusEquiv R p).symm ^ i) (x.coeff i)) * p ^ i) := by
  rw [← Ideal.mem_span_singleton, mem_span_p_pow_iff_le_coeff_eq_zero,
      ← le_coeff_eq_iff_le_sub_coeff_eq_zero]
  intro i hi
  rw [WittVector.sum_coeff_eq_coeff_sum]
  · rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp hi))]
    let g := fun x : ℕ ↦ (0 : R)
    rw [Finset.sum_congr rfl (g := g)]
    · simp [g]
    · intro b hb
      simp only [Finset.mem_sdiff, Finset.mem_Iic, Finset.mem_singleton] at hb
      exact teichmuller_mul_pow_coeff_of_ne _ (Ne.intro hb.2).symm
  · refine fun n ↦ ⟨fun ⟨a, _, ha⟩ ⟨b, _, hb⟩ ↦ ?_⟩
    ext
    dsimp only [ne_eq, Set.mem_ofPred_eq]
    rw [← Not.imp_symm (teichmuller_mul_pow_coeff_of_ne _) ha]
    exact Not.imp_symm (teichmuller_mul_pow_coeff_of_ne _) hb

/--
Given a ring `S` such that `p` is nilpotent in `S`
and two ring maps `f g : 𝕎 R →+* S`, if they coincide on the teichmuller representatives,
then they are equal.
-/
/-
**WittVector.eq_of_apply_teichmuller_eq** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：eq_of_apply_teichmuller_eq {S : Type*} [CommRing S] (f g : 𝕎 R ->+* S) (hp
 : IsNilpotent (p : S)) (h : forall (x : R), f (teichmuller p x) = g (teichmulle
r p x)) : f = g
参数：f g : 𝕎 R ->+* S；hp : IsNilpotent (p : S)；h : forall (x : R), f (teichmuller 
p x) = g (teichmuller p x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff`：dvd_sub_
sum_teichmuller_iterateFrobeniusEquiv_coeff (x : 𝕎 R) (n : Nat) : (p : 𝕎 R) ^ (n
 + 1) ∣ x - ∑ (i <= n), (teichmuller p (((_root_.fro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `RingAut.coe_pow`：coe_pow (f : R ≃+* R) (n : Nat) : ⇑(f ^ n) = f^[n]
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a

--- 原说明 ---
Given a ring `S` such that `p` is nilpotent in `S`
and two ring maps `f g : 𝕎 R →+* S`, if they coincide on the teichmuller represe
ntatives,
then they are equal.
-/
theorem eq_of_apply_teichmuller_eq
    {S : Type*} [CommRing S] (f g : 𝕎 R →+* S) (hp : IsNilpotent (p : S))
    (h : ∀ (x : R), f (teichmuller p x) = g (teichmuller p x)) : f = g := by
  obtain ⟨n, hn⟩ := hp
  ext x
  obtain ⟨c, hc⟩ := (dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff x n)
  calc
    f x = f (x - ∑ (i ≤ n), teichmuller p (((_root_.frobeniusEquiv R p).symm ^ i)
        (x.coeff i)) * p ^ i) + f (∑ (i ≤ n), teichmuller p
        (((_root_.frobeniusEquiv R p).symm ^ i) (x.coeff i)) * p ^ i) := by simp
    _ = ∑ (i ≤ n), f (teichmuller p (((_root_.frobeniusEquiv R p).symm ^ i)
        (x.coeff i))) * p ^ i := by rw [hc]; simp [pow_succ, hn]
    _ = ∑ (i ≤ n), g (teichmuller p
        (((_root_.frobeniusEquiv R p).symm ^ i) (x.coeff i))) * p ^ i := by simp [h]
    _ = g (x - ∑ (i ≤ n), teichmuller p (((_root_.frobeniusEquiv R p).symm ^ i)
        (x.coeff i)) * p ^ i) + g (∑ (i ≤ n), teichmuller p (((_root_.frobeniusEquiv R p).symm ^ i)
        (x.coeff i)) * p ^ i) := by rw [hc]; simp [pow_succ, hn]
    _ = g x := by simp

end WittVector

