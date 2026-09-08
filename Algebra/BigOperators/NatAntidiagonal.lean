/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Big operators for `NatAntidiagonal`

This file contains theorems relevant to big operators over `Finset.NatAntidiagonal`.
-/

public section

variable {M N : Type*} [CommMonoid M] [AddCommMonoid N]

namespace Finset

open HasAntidiagonal

namespace Nat

/-
**Finset.Nat.prod_antidiagonal_succ** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nat`。
形式化陈述：prod_antidiagonal_succ {n : Nat} {f : Nat × Nat -> M} : (∏ p in antidiagon
al (n + 1), f p) = f (0, n + 1) * ∏ p in antidiagonal n, f (p.1 + 1, p.2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.succ_injective`：succ_injective : Injective Nat.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Nat.antidiagonal_succ`：antidiagonal_succ (n : Nat) : antidiagonal
 (n + 1) = cons (0, n + 1) ((antidiagonal n).map (Embedding.prodMap ⟨Nat.succ, N
at.succ_injective⟩…
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
-/
theorem prod_antidiagonal_succ {n : ℕ} {f : ℕ × ℕ → M} :
    (∏ p ∈ antidiagonal (n + 1), f p)
      = f (0, n + 1) * ∏ p ∈ antidiagonal n, f (p.1 + 1, p.2) := by
  rw [antidiagonal_succ, prod_cons, prod_map]; rfl
/-
**Finset.Nat.sum_antidiagonal_succ** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nat`。
形式化陈述：sum_antidiagonal_succ {n : Nat} {f : Nat × Nat -> N} : (∑ p in antidiagona
l (n + 1), f p) = f (0, n + 1) + ∑ p in antidiagonal n, f (p.1 + 1, p.2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nat.prod_antidiagonal_succ`：prod_antidiagonal_succ {n : Nat} {f :
 Nat × Nat -> M} : (∏ p in antidiagonal (n + 1), f p) = f (0, n + 1) * ∏ p in an
tidiagonal n, f (p.1 + …
-/
theorem sum_antidiagonal_succ {n : ℕ} {f : ℕ × ℕ → N} :
    (∑ p ∈ antidiagonal (n + 1), f p) = f (0, n + 1) + ∑ p ∈ antidiagonal n, f (p.1 + 1, p.2) :=
  @prod_antidiagonal_succ (Multiplicative N) _ _ _

@[to_additive]
/-
**Finset.Nat.prod_antidiagonal_swap** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nat`。
形式化陈述：prod_antidiagonal_swap {n : Nat} {f : Nat × Nat -> M} : ∏ p in antidiagona
l n, f p.swap = ∏ p in antidiagonal n, f p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.swap_injective`：swap_injective : Function.Injective (@swap α β)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.HasAntidiagonal.map_swap_antidiagonal`：∀ {A : Type u_1} [inst : A
ddCommMonoid A] [inst_1 : Finset.HasAntidiagonal A] {n : A},   Finset.map { toFu
n := Prod.swap, inj' := ⋯ } (Finse…
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
-/
theorem prod_antidiagonal_swap {n : ℕ} {f : ℕ × ℕ → M} :
    ∏ p ∈ antidiagonal n, f p.swap = ∏ p ∈ antidiagonal n, f p := by
  conv_lhs => rw [← map_swap_antidiagonal, Finset.prod_map]
  rfl
/-
**Finset.Nat.prod_antidiagonal_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nat`。
形式化陈述：prod_antidiagonal_succ' {n : Nat} {f : Nat × Nat -> M} : (∏ p in antidiago
nal (n + 1), f p) = f (n + 1, 0) * ∏ p in antidiagonal n, f (p.1, p.2 + 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.Nat.prod_antidiagonal_swap`：prod_antidiagonal_swap {n : Nat} {f :
 Nat × Nat -> M} : ∏ p in antidiagonal n, f p.swap = ∏ p in antidiagonal n, f p
· 使用定理 `Finset.Nat.prod_antidiagonal_succ`：prod_antidiagonal_succ {n : Nat} {f :
 Nat × Nat -> M} : (∏ p in antidiagonal (n + 1), f p) = f (0, n + 1) * ∏ p in an
tidiagonal n, f (p.1 + …
-/
theorem prod_antidiagonal_succ' {n : ℕ} {f : ℕ × ℕ → M} : (∏ p ∈ antidiagonal (n + 1), f p) =
    f (n + 1, 0) * ∏ p ∈ antidiagonal n, f (p.1, p.2 + 1) := by
  rw [← prod_antidiagonal_swap, prod_antidiagonal_succ, ← prod_antidiagonal_swap]
  rfl
/-
**Finset.Nat.sum_antidiagonal_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nat`。
形式化陈述：sum_antidiagonal_succ' {n : Nat} {f : Nat × Nat -> N} : (∑ p in antidiagon
al (n + 1), f p) = f (n + 1, 0) + ∑ p in antidiagonal n, f (p.1, p.2 + 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nat.prod_antidiagonal_succ'`：prod_antidiagonal_succ' {n : Nat} {f
 : Nat × Nat -> M} : (∏ p in antidiagonal (n + 1), f p) = f (n + 1, 0) * ∏ p in 
antidiagonal n, f (p.1, …
-/
theorem sum_antidiagonal_succ' {n : ℕ} {f : ℕ × ℕ → N} :
    (∑ p ∈ antidiagonal (n + 1), f p) = f (n + 1, 0) + ∑ p ∈ antidiagonal n, f (p.1, p.2 + 1) :=
  @prod_antidiagonal_succ' (Multiplicative N) _ _ _

@[to_additive]
/-
**Finset.Nat.prod_antidiagonal_subst** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nat`。
形式化陈述：prod_antidiagonal_subst {n : Nat} {f : Nat × Nat -> Nat -> M} : ∏ p in ant
idiagonal n, f p n = ∏ p in antidiagonal n, f p (p.1 + p.2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…
-/
theorem prod_antidiagonal_subst {n : ℕ} {f : ℕ × ℕ → ℕ → M} :
    ∏ p ∈ antidiagonal n, f p n = ∏ p ∈ antidiagonal n, f p (p.1 + p.2) :=
  prod_congr rfl fun p hp ↦ by rw [mem_antidiagonal.mp hp]

@[to_additive]
/-
**Finset.Nat.prod_antidiagonal_eq_prod_range_succ_mk** 是 Mathlib 中的一个定理，位于命名空间 `
Finset.Nat`。
形式化陈述：prod_antidiagonal_eq_prod_range_succ_mk {M : Type*} [CommMonoid M] (f : Na
t × Nat -> M) (n : Nat) : ∏ ij in antidiagonal n, f ij = ∏ k in range n.succ, f 
(k, n - k)
参数：f : Nat × Nat -> M；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Prod.mk.inj`：∀ {α : Type u} {β : Type v} {fst : α} {snd : β} {fst_1 : α}
 {snd_1 : β},   (fst, snd) = (fst_1, snd_1) → fst = fst_1 ∧ snd = snd_1
-/
theorem prod_antidiagonal_eq_prod_range_succ_mk {M : Type*} [CommMonoid M] (f : ℕ × ℕ → M)
    (n : ℕ) : ∏ ij ∈ antidiagonal n, f ij = ∏ k ∈ range n.succ, f (k, n - k) :=
  Finset.prod_map (range n.succ) ⟨fun i ↦ (i, n - i), fun _ _ h ↦ (Prod.mk.inj h).1⟩ f

/-- This lemma matches more generally than `Finset.Nat.prod_antidiagonal_eq_prod_range_succ_mk` when
using `rw ← `. -/
@[to_additive /-- This lemma matches more generally than
`Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk` when using `rw ← `. -/]
/-
**Finset.Nat.prod_antidiagonal_eq_prod_range_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin
set.Nat`。
形式化陈述：prod_antidiagonal_eq_prod_range_succ {M : Type*} [CommMonoid M] (f : Nat -
> Nat -> M) (n : Nat) : ∏ ij in antidiagonal n, f ij.1 ij.2 = ∏ k in range n.suc
c, f k (n - k)
参数：f : Nat -> Nat -> M；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nat.prod_antidiagonal_eq_prod_range_succ_mk`：prod_antidiagonal_eq
_prod_range_succ_mk {M : Type*} [CommMonoid M] (f : Nat × Nat -> M) (n : Nat) : 
∏ ij in antidiagonal n, f ij = ∏ k in ra…
-/
theorem prod_antidiagonal_eq_prod_range_succ {M : Type*} [CommMonoid M] (f : ℕ → ℕ → M) (n : ℕ) :
    ∏ ij ∈ antidiagonal n, f ij.1 ij.2 = ∏ k ∈ range n.succ, f k (n - k) :=
  prod_antidiagonal_eq_prod_range_succ_mk _ _
end Nat

end Finset

