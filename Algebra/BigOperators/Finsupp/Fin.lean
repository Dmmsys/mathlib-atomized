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

/--
lemma `sum_cons` / 引理 `sum_cons`

English:
lemma sum_cons
  given: [AddCommMonoid M] (n : Nat) (σ : Fin n ->₀ M) (i : M)
  proof: by
  rw [sum_fintype _ _ (fun _ => rfl)]; rw [sum_fintype _ _ (fun _ => rfl)]
  exact Fin.sum_cons i σ

中文:
引理 sum_cons
  条件: [AddCommMonoid M] (n : 自然数) (σ : Fin n ->₀ M) (i : M)
  证明: by
  rw [sum_fintype _ _ (fun _ => rfl)]; rw [sum_fintype _ _ (fun _ => rfl)]
  exact Fin.sum_cons i σ

Depends on / 依赖: Fin.sum_cons, sum_cons, sum_fintype
-/
lemma sum_cons [AddCommMonoid M] (n : Nat) (σ : Fin n ->₀ M) (i : M) :
    (sum (cons i σ) fun _ e => e) = i + sum σ (fun _ e => e) := by
  rw [sum_fintype _ _ (fun _ => rfl)]; rw [sum_fintype _ _ (fun _ => rfl)]
  exact Fin.sum_cons i σ

/--
lemma `sum_cons'` / 引理 `sum_cons'`

English:
lemma sum_cons'
  statement: [Zero M] [AddCommMonoid N] (n : Nat) (σ : Fin n ->₀ M) (i : M)
  proof: by
  rw [sum_fintype _ _ (fun _ => by apply h)]; rw [sum_fintype _ _ (fun _ => by apply h)]
  simp_rw [Fin.sum_univ_succ, cons_zero, cons_succ]
  congr

中文:
引理 sum_cons'
  结论: [Zero M] [AddCommMonoid N] (n : 自然数) (σ : Fin n ->₀ M) (i : M)
  证明: by
  rw [sum_fintype _ _ (fun _ => by apply h)]; rw [sum_fintype _ _ (fun _ => by apply h)]
  simp_rw [Fin.sum_univ_succ, cons_zero, cons_succ]
  congr

Depends on / 依赖: Fin.sum_univ_succ, cons_succ, cons_zero, simp_rw, sum_fintype, sum_univ_succ
-/
lemma sum_cons' [Zero M] [AddCommMonoid N] (n : Nat) (σ : Fin n ->₀ M) (i : M)
    (f : Fin (n + 1) -> M -> N) (h : forall x, f x 0 = 0) :
    (sum (Finsupp.cons i σ) f) = f 0 i + sum σ (Fin.tail f) := by
  rw [sum_fintype _ _ (fun _ => by apply h)]; rw [sum_fintype _ _ (fun _ => by apply h)]
  simp_rw [Fin.sum_univ_succ, cons_zero, cons_succ]
  congr

/--
theorem `ofSupportFinite_fin_two_eq` / 定理 `ofSupportFinite_fin_two_eq`

English:
theorem ofSupportFinite_fin_two_eq
  given: (n : Fin 2 ->₀ Nat)
  proof: by
  rw [Finsupp.ext_iff]; rw [Fin.forall_fin_two]
  exact ⟨rfl, rfl⟩

中文:
定理 ofSupportFinite_fin_two_eq
  条件: (n : Fin 2 ->₀ 自然数)
  证明: by
  rw [Finsupp.ext_iff]; rw [Fin.forall_fin_two]
  exact ⟨rfl, rfl⟩

Depends on / 依赖: Fin.forall_fin_two, Finsupp, Finsupp.ext_iff, ext_iff, forall_fin_two
-/
theorem ofSupportFinite_fin_two_eq (n : Fin 2 ->₀ Nat) :
    ofSupportFinite ![n 0, n 1] (Set.toFinite _) = n := by
  rw [Finsupp.ext_iff]; rw [Fin.forall_fin_two]
  exact ⟨rfl, rfl⟩

end Finsupp

section Fin2

variable (M) in
/-- The space of finitely supported functions `Fin 2 →₀ α` is equivalent to `α × α`.
See also `finTwoArrowEquiv`. -/
@[simps! apply symm_apply]
/--
Definition of `finTwoArrowEquiv'` / `finTwoArrowEquiv'` 的定义

English:
definition finTwoArrowEquiv'
  signature: [Zero M]
  body: Finsupp.equivFunOnFinite.trans (finTwoArrowEquiv M)

中文:
定义 finTwoArrowEquiv'
  签名: [Zero M]
  定义体: Finsupp.equivFunOnFinite.trans (finTwoArrowEquiv M)

Depends on / 依赖: Finsupp, Finsupp.equivFunOnFinite.trans, equivFunOnFinite, finTwoArrowEquiv
-/
noncomputable def finTwoArrowEquiv' [Zero M] : (Fin 2 ->₀ M) ≃ M × M :=
  Finsupp.equivFunOnFinite.trans (finTwoArrowEquiv M)

/--
theorem `finTwoArrowEquiv'_sum_eq` / 定理 `finTwoArrowEquiv'_sum_eq`

English:
theorem finTwoArrowEquiv'_sum_eq
  given: {d : M × M} [AddCommMonoid M]
  proof: by
  apply (Finsupp.equivFunOnFinite_symm_sum _).trans
  simp

中文:
定理 finTwoArrowEquiv'_sum_eq
  条件: {d : M × M} [AddCommMonoid M]
  证明: by
  apply (Finsupp.equivFunOnFinite_symm_sum _).trans
  simp
-/
theorem finTwoArrowEquiv'_sum_eq {d : M × M} [AddCommMonoid M] :
    (((finTwoArrowEquiv' M).symm d).sum fun _ n => n) = d.1 + d.2 := by
  apply (Finsupp.equivFunOnFinite_symm_sum _).trans
  simp

end Fin2
