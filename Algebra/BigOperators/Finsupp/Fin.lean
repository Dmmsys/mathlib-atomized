/-
Copyright (c) 2023 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Finsupp.Fin

/-!
# `Finsupp.sum` and `Finsupp.prod` over `Fin`

This file contains theorems relevant to big operators on finitely supported functions over `Fin`.
-/

@[expose] public section

variable {M N : Type*}

namespace Finsupp

/-
**Finsupp.sum_cons** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：sum_cons [AddCommMonoid M] (n : Nat) (σ : Fin n ->₀ M) (i : M) : (sum (con
s i σ) fun _ e => e) = i + sum σ (fun _ e => e)
参数：n : Nat；σ : Fin n ->₀ M；i : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_fintype`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [in
st : Zero M] [inst_1 : AddCommMonoid N] [inst_2 : Fintype α]   (f : α →₀ M) (g :
 α → M → …
· 使用定理 `Fin.sum_cons`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (x : M) 
(f : Fin n → M), ∑ i, Fin.cons x f i = x + ∑ i, f i
-/
lemma sum_cons [AddCommMonoid M] (n : ℕ) (σ : Fin n →₀ M) (i : M) :
    (sum (cons i σ) fun _ e ↦ e) = i + sum σ (fun _ e ↦ e) := by
  rw [sum_fintype _ _ (fun _ => rfl), sum_fintype _ _ (fun _ => rfl)]
  exact Fin.sum_cons i σ
/-
**Finsupp.sum_cons'** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：sum_cons' [Zero M] [AddCommMonoid N] (n : Nat) (σ : Fin n ->₀ M) (i : M) (
f : Fin (n + 1) -> M -> N) (h : forall x, f x 0 = 0) : (sum (Finsupp.cons i σ) f
) = f 0 i + sum σ (Fin.tail f)
参数：n : Nat；σ : Fin n ->₀ M；i : M；f : Fin (n + 1) -> M -> N；h : forall x, f x 0 =
 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_fintype`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [in
st : Zero M] [inst_1 : AddCommMonoid N] [inst_2 : Fintype α]   (f : α →₀ M) (g :
 α → M → …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.sum_univ_succ`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f 
: Fin (n + 1) → M), ∑ i, f i = f 0 + ∑ i, f i.succ
-/
lemma sum_cons' [Zero M] [AddCommMonoid N] (n : ℕ) (σ : Fin n →₀ M) (i : M)
    (f : Fin (n + 1) → M → N) (h : ∀ x, f x 0 = 0) :
    (sum (Finsupp.cons i σ) f) = f 0 i + sum σ (Fin.tail f) := by
  rw [sum_fintype _ _ (fun _ => by apply h), sum_fintype _ _ (fun _ => by apply h)]
  simp_rw [Fin.sum_univ_succ, cons_zero, cons_succ]
  congr
/-
**Finsupp.ofSupportFinite_fin_two_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：ofSupportFinite_fin_two_eq (n : Fin 2 ->₀ Nat) : ofSupportFinite ![n 0, n 
1] (Set.toFinite _) = n
参数：n : Fin 2 ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.ext_iff`：∀ {α : Type u_1} {M : Type u_4} [inst : Zero M] {f g : 
α →₀ M}, f = g ↔ ∀ (a : α), f a = g a
· 使用定理 `Fin.forall_fin_two`：∀ {p : Fin 2 → Prop}, (∀ (i : Fin 2), p i) ↔ p 0 ∧ p
 1
-/
theorem ofSupportFinite_fin_two_eq (n : Fin 2 →₀ ℕ) :
    ofSupportFinite ![n 0, n 1] (Set.toFinite _) = n := by
  rw [Finsupp.ext_iff, Fin.forall_fin_two]
  exact ⟨rfl, rfl⟩

end Finsupp

section Fin2

variable (M) in
/-- The space of finitely supported functions `Fin 2 →₀ α` is equivalent to `α × α`.
See also `finTwoArrowEquiv`. -/
@[simps! apply symm_apply]
/-
**finTwoArrowEquiv'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finTwoArrowEquiv' [Zero M] : (Fin 2 ->₀ M) ≃ M × M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The space of finitely supported functions `Fin 2 →₀ α` is equivalent to `α × α`.
See also `finTwoArrowEquiv`.
-/
noncomputable def finTwoArrowEquiv' [Zero M] : (Fin 2 →₀ M) ≃ M × M :=
  Finsupp.equivFunOnFinite.trans (finTwoArrowEquiv M)
/-
**finTwoArrowEquiv'_sum_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_1} {d : M × M} [inst : AddCommMonoid M], (((finTwoArrowEquiv
' M).symm d).sum fun x n => n) = d.1 + d.2
参数：((finTwoArrowEquiv' M).symm d).sum fun x n => n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finsupp.equivFunOnFinite_symm_sum`：equivFunOnFinite_symm_sum [Fintype α]
 [AddCommMonoid M] (f : α -> M) : ((equivFunOnFinite.symm f).sum fun _ n => n) =
 ∑ a, f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `finTwoArrowEquiv_symm_apply`：∀ (α : Type u_1), ⇑(finTwoArrowEquiv α).sym
m = fun x => ![x.1, x.2]
· 使用定理 `Fin.sum_univ_two`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 2 →
 M), ∑ i, f i = f 0 + f 1
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finTwoArrowEquiv'_sum_eq {d : M × M} [AddCommMonoid M] :
    (((finTwoArrowEquiv' M).symm d).sum fun _ n ↦ n) = d.1 + d.2 := by
  apply (Finsupp.equivFunOnFinite_symm_sum _).trans
  simp

end Fin2

