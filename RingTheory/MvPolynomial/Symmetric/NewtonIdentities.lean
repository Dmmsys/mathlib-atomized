/-
Copyright (c) 2023 Michael Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Lee
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Data.Fintype.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Newton's Identities

This file defines `MvPolynomial` power sums as a means of implementing Newton's identities. The
combinatorial proof, due to Zeilberger, defines for `k : ℕ` a subset `pairs` of
`(range k).powerset × range k` and a map `pairMap` such that `pairMap` is an involution on `pairs`,
and a map `weight` which identifies elements of `pairs` with the terms of the summation in Newton's
identities and which satisfies `weight ∘ pairMap = -weight`. The result therefore follows neatly
from an identity implemented in mathlib as `Finset.sum_involution`. Namely, we use
`Finset.sum_involution` to show that `∑ t ∈ pairs σ k, weight σ R k t = 0`. We then identify
`(-1) ^ k * k * esymm σ R k` with the terms of the weight sum for which `t.fst` has
cardinality `k`, and `(-1) ^ i * esymm σ R i * psum σ R (k - i)` with the terms of the weight sum
for which `t.fst` has cardinality `i` for `i < k`, and we thereby derive the main result
`(-1) ^ k * k * esymm σ R k + ∑ i ∈ range k, (-1) ^ i * esymm σ R i * psum σ R (k - i) = 0` (or
rather, two equivalent forms which provide direct definitions for `esymm` and `psum` in lower-degree
terms).

## Main declarations

* `MvPolynomial.mul_esymm_eq_sum`: a recurrence relation for the `k`th elementary
  symmetric polynomial in terms of lower-degree elementary symmetric polynomials and power sums.

* `MvPolynomial.psum_eq_mul_esymm_sub_sum`: a recurrence relation for the degree-`k` power sum
  in terms of lower-degree elementary symmetric polynomials and power sums.

## References

See [zeilberger1984] for the combinatorial proof of Newton's identities.
-/

public section

open Equiv (Perm)

open MvPolynomial

noncomputable section

namespace MvPolynomial

open Finset Nat

namespace NewtonIdentities

variable (σ : Type*) (R : Type*) [CommRing R]

section DecidableEq

variable [DecidableEq σ]

/-
**MvPolynomial.NewtonIdentities.pairMap** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial.
NewtonIdentities`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def pairMap (t : Finset σ × σ) : Finset σ × σ :=
  if h : t.snd ∈ t.fst then (t.fst.erase t.snd, t.snd) else (t.fst.cons t.snd h, t.snd)
/-
**MvPolynomial.NewtonIdentities.pairMap_ne_self** 是 Mathlib 中的一个引理，位于命名空间 `MvPol
ynomial.NewtonIdentities`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma pairMap_ne_self (t : Finset σ × σ) : pairMap σ t ≠ t := by
  rw [pairMap]
  split_ifs with h1
  all_goals by_contra ht; rw [← ht] at h1; simp_all
/-
**MvPolynomial.NewtonIdentities.pairMap_of_snd_mem_fst** 是 Mathlib 中的一个引理，位于命名空间
 `MvPolynomial.NewtonIdentities`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma pairMap_of_snd_mem_fst {t : Finset σ × σ} (h : t.snd ∈ t.fst) :
    pairMap σ t = (t.fst.erase t.snd, t.snd) := by
  simp [pairMap, h]
/-
**MvPolynomial.NewtonIdentities.pairMap_of_snd_notMem_fst** 是 Mathlib 中的一个引理，位于命
名空间 `MvPolynomial.NewtonIdentities`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma pairMap_of_snd_notMem_fst {t : Finset σ × σ} (h : t.snd ∉ t.fst) :
    pairMap σ t = (t.fst.cons t.snd h, t.snd) := by
  simp [pairMap, h]

@[simp]
/-
**MvPolynomial.NewtonIdentities.pairMap_involutive** 是 Mathlib 中的一个定理，位于命名空间 `Mv
Polynomial.NewtonIdentities`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem pairMap_involutive : (pairMap σ).Involutive := by
  intro t
  rw [pairMap, pairMap]
  split_ifs with h1 h2 h3
  · simp at h2
  · simp [insert_erase h1]
  · simp_all
  · simp at h3

variable [Fintype σ]
/-
**MvPolynomial.NewtonIdentities.pairs** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial.Ne
wtonIdentities`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def pairs (k : ℕ) : Finset (Finset σ × σ) :=
  {t | #t.1 ≤ k ∧ (#t.1 = k → t.snd ∈ t.fst)}

@[simp]
/-
**MvPolynomial.NewtonIdentities.mem_pairs** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomia
l.NewtonIdentities`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma mem_pairs (k : ℕ) (t : Finset σ × σ) :
    t ∈ pairs σ k ↔ #t.1 ≤ k ∧ (#t.1 = k → t.snd ∈ t.fst) := by
  simp [pairs]
/-
**MvPolynomial.NewtonIdentities.weight** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial.N
ewtonIdentities`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def weight (k : ℕ) (t : Finset σ × σ) : MvPolynomial σ R :=
  (-1) ^ #t.1 * ((∏ a ∈ t.fst, X a) * X t.snd ^ (k - #t.1))
/-
**MvPolynomial.NewtonIdentities.pairMap_mem_pairs** 是 Mathlib 中的一个定理，位于命名空间 `MvP
olynomial.NewtonIdentities`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem pairMap_mem_pairs {k : ℕ} (t : Finset σ × σ) (h : t ∈ pairs σ k) :
    pairMap σ t ∈ pairs σ k := by
  rw [mem_pairs] at h ⊢
  rcases (em (t.snd ∈ t.fst)) with h1 | h1
  · rw [pairMap_of_snd_mem_fst σ h1]
    simp only [h1, implies_true, and_true] at h
    simp only [card_erase_of_mem h1, tsub_le_iff_right, mem_erase, ne_eq, h1]
    refine ⟨le_succ_of_le h, ?_⟩
    by_contra h2
    simp only [not_true_eq_false, and_true, not_forall, not_false_eq_true, exists_prop] at h2
    rw [← h2] at h
    exact not_le_of_gt (sub_lt (card_pos.mpr ⟨t.snd, h1⟩) zero_lt_one) h
  · rw [pairMap_of_snd_notMem_fst σ h1]
    simp only [h1] at h
    simp only [card_cons, mem_cons, true_or, implies_true, and_true]
    exact (le_iff_eq_or_lt.mp h.left).resolve_left h.right
/-
**MvPolynomial.NewtonIdentities.weight_add_weight_pairMap** 是 Mathlib 中的一个定理，位于命
名空间 `MvPolynomial.NewtonIdentities`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem weight_add_weight_pairMap {k : ℕ} (t : Finset σ × σ) (h : t ∈ pairs σ k) :
    weight σ R k t + weight σ R k (pairMap σ t) = 0 := by
  rw [weight, weight]
  rw [mem_pairs] at h
  have h2 (n : ℕ) : -(-1 : MvPolynomial σ R) ^ n = (-1) ^ (n + 1) := by
    rw [← neg_one_mul ((-1 : MvPolynomial σ R) ^ n), pow_add, pow_one, mul_comm]
  rcases (em (t.snd ∈ t.fst)) with h1 | h1
  · rw [pairMap_of_snd_mem_fst σ h1]
    simp only [← prod_erase_mul t.fst (fun j ↦ (X j : MvPolynomial σ R)) h1,
      mul_assoc (∏ a ∈ erase t.fst t.snd, X a), card_erase_of_mem h1]
    nth_rewrite 1 [← pow_one (X t.snd)]
    simp only [← pow_add, add_comm]
    have h3 : 1 ≤ #t.1 := lt_iff_add_one_le.mp (card_pos.mpr ⟨t.snd, h1⟩)
    rw [← tsub_tsub_assoc h.left h3, ← neg_neg ((-1 : MvPolynomial σ R) ^ (#t.1 - 1)),
      h2 (#t.1 - 1), Nat.sub_add_cancel h3]
    simp
  · rw [pairMap_of_snd_notMem_fst σ h1]
    simp only [mul_comm, mul_assoc (∏ a ∈ t.fst, X a), card_cons, prod_cons]
    nth_rewrite 2 [← pow_one (X t.snd)]
    simp only [← pow_add, ← Nat.add_sub_assoc (Nat.lt_of_le_of_ne h.left (mt h.right h1)), add_comm,
      Nat.succ_eq_add_one, Nat.add_sub_add_right]
    rw [← neg_neg ((-1 : MvPolynomial σ R) ^ #t.1), h2]
    simp
/-
**MvPolynomial.NewtonIdentities.weight_sum** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomi
al.NewtonIdentities`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem weight_sum (k : ℕ) : ∑ t ∈ pairs σ k, weight σ R k t = 0 :=
  sum_involution (fun t _ ↦ pairMap σ t) (weight_add_weight_pairMap σ R)
    (fun t _ ↦ (fun _ ↦ pairMap_ne_self σ t)) (pairMap_mem_pairs σ)
    (fun t _ ↦ pairMap_involutive σ t)
/-
**MvPolynomial.NewtonIdentities.sum_filter_pairs_eq_sum_powersetCard_sum** 是 Mat
hlib 中的一个定理，位于命名空间 `MvPolynomial.NewtonIdentities`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem sum_filter_pairs_eq_sum_powersetCard_sum (k : ℕ)
    (f : Finset σ × σ → MvPolynomial σ R) :
    ∑ t ∈ pairs σ k with #t.1 = k, f t = ∑ A ∈ powersetCard k univ, ∑ j ∈ A, f (A, j) := by
  apply sum_finset_product
  aesop
/-
**MvPolynomial.NewtonIdentities.sum_filter_pairs_eq_sum_powersetCard_mem_filter_
antidiagonal_sum** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial.NewtonIdentities`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem sum_filter_pairs_eq_sum_powersetCard_mem_filter_antidiagonal_sum (k : ℕ) (a : ℕ × ℕ)
    (ha : a ∈ {a ∈ antidiagonal k | a.fst < k}) (f : Finset σ × σ → MvPolynomial σ R) :
    ∑ t ∈ pairs σ k with #t.1 = a.1, f t = ∑ A ∈ powersetCard a.1 univ, ∑ j, f (A, j) := by
  apply sum_finset_product
  simp only [mem_filter, mem_powersetCard_univ, mem_univ, and_true, and_iff_right_iff_imp]
  rintro p hp
  have : #p.fst ≤ k := by apply le_of_lt; simp_all
  aesop

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.NewtonIdentities.filter_pairs_lt** 是 Mathlib 中的一个引理，位于命名空间 `MvPol
ynomial.NewtonIdentities`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma filter_pairs_lt (k : ℕ) :
    (pairs σ k).filter (fun (s, _) ↦ #s < k) =
      (range k).disjiUnion (powersetCard · univ) ((pairwise_disjoint_powersetCard _).set_pairwise _)
        ×ˢ univ := by ext; aesop (add unsafe le_of_lt)

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.NewtonIdentities.sum_filter_pairs_eq_sum_filter_antidiagonal_powe
rsetCard_sum** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial.NewtonIdentities`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem sum_filter_pairs_eq_sum_filter_antidiagonal_powersetCard_sum (k : ℕ)
    (f : Finset σ × σ → MvPolynomial σ R) :
    ∑ t ∈ pairs σ k with #t.1 < k, f t =
      ∑ a ∈ antidiagonal k with a.fst < k, ∑ A ∈ powersetCard a.fst univ, ∑ j, f (A, j) := by
  rw [filter_pairs_lt, sum_product, sum_disjiUnion]
  refine sum_nbij' (fun n ↦ (n, k - n)) Prod.fst ?_ ?_ ?_ ?_ ?_ <;>
    simp +contextual [@eq_comm _ _ k, le_of_lt]
/-
**MvPolynomial.NewtonIdentities.disjoint_filter_pairs_lt_filter_pairs_eq** 是 Mat
hlib 中的一个定理，位于命名空间 `MvPolynomial.NewtonIdentities`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem disjoint_filter_pairs_lt_filter_pairs_eq (k : ℕ) :
    Disjoint {t ∈ pairs σ k | #t.1 < k} {t ∈ pairs σ k | #t.1 = k} := by
  rw [disjoint_filter]
  exact fun _ _ h1 h2 ↦ lt_irrefl _ (h2.symm.subst h1)
/-
**MvPolynomial.NewtonIdentities.disjUnion_filter_pairs_eq_pairs** 是 Mathlib 中的一个
定理，位于命名空间 `MvPolynomial.NewtonIdentities`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem disjUnion_filter_pairs_eq_pairs (k : ℕ) :
    disjUnion {t ∈ pairs σ k | #t.1 < k} {t ∈ pairs σ k | #t.1 = k}
      (disjoint_filter_pairs_lt_filter_pairs_eq σ k) = pairs σ k := by
  grind [MvPolynomial.NewtonIdentities.pairs]

end DecidableEq

variable [Fintype σ]

/-
**MvPolynomial.NewtonIdentities.esymm_summand_to_weight** 是 Mathlib 中的一个定理，位于命名空
间 `MvPolynomial.NewtonIdentities`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem esymm_summand_to_weight (k : ℕ) (A : Finset σ) (h : A ∈ powersetCard k univ) :
    ∑ j ∈ A, weight σ R k (A, j) = k * (-1) ^ k * (∏ i ∈ A, X i : MvPolynomial σ R) := by
  simp [weight, mem_powersetCard_univ.mp h, mul_assoc]
/-
**MvPolynomial.NewtonIdentities.esymm_to_weight** 是 Mathlib 中的一个定理，位于命名空间 `MvPol
ynomial.NewtonIdentities`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem esymm_to_weight [DecidableEq σ] (k : ℕ) : k * esymm σ R k =
    (-1) ^ k * ∑ t ∈ pairs σ k with #t.1 = k, weight σ R k t := by
  rw [esymm, sum_filter_pairs_eq_sum_powersetCard_sum σ R k (fun t ↦ weight σ R k t),
    sum_congr rfl (esymm_summand_to_weight σ R k), mul_comm (k : MvPolynomial σ R) ((-1) ^ k),
    ← mul_sum, ← mul_assoc, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨k, rfl⟩, one_mul]
/-
**MvPolynomial.NewtonIdentities.esymm_mul_psum_summand_to_weight** 是 Mathlib 中的一
个定理，位于命名空间 `MvPolynomial.NewtonIdentities`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem esymm_mul_psum_summand_to_weight (k : ℕ) (a : ℕ × ℕ) (ha : a ∈ antidiagonal k) :
    ∑ A ∈ powersetCard a.fst univ, ∑ j, weight σ R k (A, j) =
    (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd := by
  simp only [esymm, psum, weight, ← mul_assoc, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [sum_mul]
  refine sum_congr rfl fun s hs ↦ ?_
  rw [mem_powersetCard_univ.mp hs, ← mem_antidiagonal.mp ha, add_sub_self_left]
/-
**MvPolynomial.NewtonIdentities.esymm_mul_psum_to_weight** 是 Mathlib 中的一个定理，位于命名
空间 `MvPolynomial.NewtonIdentities`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem esymm_mul_psum_to_weight [DecidableEq σ] (k : ℕ) :
    ∑ a ∈ antidiagonal k with a.fst < k, (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd =
      ∑ t ∈ pairs σ k with #t.1 < k, weight σ R k t := by
  rw [← sum_congr rfl (fun a ha ↦ esymm_mul_psum_summand_to_weight σ R k a (mem_filter.mp ha).left),
    sum_filter_pairs_eq_sum_filter_antidiagonal_powersetCard_sum σ R k]

end NewtonIdentities

variable (σ : Type*) [Fintype σ] (R : Type*) [CommRing R]

/-- **Newton's identities** give a recurrence relation for the kth elementary symmetric polynomial
in terms of lower degree elementary symmetric polynomials and power sums. -/
/-
**MvPolynomial.mul_esymm_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：mul_esymm_eq_sum (k : Nat) : k * esymm σ R k = (-1) ^ (k + 1) * ∑ a in ant
idiagonal k with a.1 < k, (-1) ^ a.1 * esymm σ R a.1 * psum σ R a.2
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities.0.Mv
Polynomial.NewtonIdentities.esymm_to_weight`：∀ (σ : Type u_1) (R : Type u_2) [in
st : CommRing R] [inst_1 : Fintype σ] [inst_2 : DecidableEq σ] (k : ℕ),   ↑k * M
vPolynomial.esymm σ R k =…
· 使用定理 `_private.Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities.0.Mv
Polynomial.NewtonIdentities.esymm_mul_psum_to_weight`：∀ (σ : Type u_1) (R : Type
 u_2) [inst : CommRing R] [inst_1 : Fintype σ] [inst_2 : DecidableEq σ] (k : ℕ),
   ∑ a ∈ Finset.HasAntidiagonal.an…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `neg_mul_eq_neg_mul`：neg_mul_eq_neg_mul (a b : α) : -(a * b) = -a * b
· 使用定理 `neg_eq_neg_one_mul`：neg_eq_neg_one_mul (a : α) : -a = -1 * a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `left_distrib`：left_distrib [Mul R] [Add R] [LeftDistribClass R] (a b c :
 R) : a * (b + c) = a * b + a * c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `_private.Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities.0.Mv
Polynomial.NewtonIdentities.disjoint_filter_pairs_lt_filter_pairs_eq`：∀ (σ : Typ
e u_1) [inst : DecidableEq σ] [inst_1 : Fintype σ] (k : ℕ),   Disjoint ({t ∈ MvP
olynomial.NewtonIdentities.pairs✝ σ k | t.1.card <…
· 使用定理 `Finset.sum_disjUnion`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι}
 [inst : AddCommMonoid M] {f : ι → M} (h : Disjoint s₁ s₂),   ∑ x ∈ s₁.disjUnion
 s₂ h, f x…
· 使用定理 `_private.Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities.0.Mv
Polynomial.NewtonIdentities.disjUnion_filter_pairs_eq_pairs`：∀ (σ : Type u_1) [i
nst : DecidableEq σ] [inst_1 : Fintype σ] (k : ℕ),   {t ∈ MvPolynomial.NewtonIde
ntities.pairs✝ σ k | t.1.card < k}.disjUn…
· 使用定理 `_private.Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities.0.Mv
Polynomial.NewtonIdentities.weight_sum`：∀ (σ : Type u_1) (R : Type u_2) [inst : 
CommRing R] [inst_1 : DecidableEq σ] [inst_2 : Fintype σ] (k : ℕ),   ∑ t ∈ MvPol
ynomial.NewtonIdenti…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_one_pow_mul_eq_zero_iff`：∀ {R : Type u} [inst : Ring R] {a : R} {n :
 ℕ}, (-1) ^ n * a = 0 ↔ a = 0

--- 原说明 ---
**Newton's identities** give a recurrence relation for the kth elementary symmet
ric polynomial
in terms of lower degree elementary symmetric polynomials and power sums.
-/
theorem mul_esymm_eq_sum (k : ℕ) :
    k * esymm σ R k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k, (-1) ^ a.1 * esymm σ R a.1 * psum σ R a.2 := by
  classical
  rw [NewtonIdentities.esymm_to_weight σ R k, NewtonIdentities.esymm_mul_psum_to_weight σ R k,
    eq_comm, ← sub_eq_zero, sub_eq_add_neg, neg_mul_eq_neg_mul,
    neg_eq_neg_one_mul ((-1 : MvPolynomial σ R) ^ k)]
  nth_rw 2 [← pow_one (-1 : MvPolynomial σ R)]
  rw [← pow_add, add_comm 1 k, ← left_distrib,
    ← sum_disjUnion (NewtonIdentities.disjoint_filter_pairs_lt_filter_pairs_eq σ k),
    NewtonIdentities.disjUnion_filter_pairs_eq_pairs σ k, NewtonIdentities.weight_sum σ R k,
    neg_one_pow_mul_eq_zero_iff.mpr rfl]
/-
**MvPolynomial.sum_antidiagonal_card_esymm_psum_eq_zero** 是 Mathlib 中的一个定理，位于命名空
间 `MvPolynomial`。
形式化陈述：sum_antidiagonal_card_esymm_psum_eq_zero : ∑ a in antidiagonal (Fintype.ca
rd σ), (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_filter_add_sum_filter_not`：∀ {ι : Type u_1} {M : Type u_4} [i
nst : AddCommMonoid M] (s : Finset ι) (p : ι → Prop) [inst_1 : DecidablePred p] 
  [inst_2 : (x : ι) → Deci…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `add_left_injective`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G]
 (a : G), Function.Injective fun x => x + a
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
· 使用定理 `Finset.Nat.antidiagonal_filter_le_fst_of_le`：∀ {n k : ℕ},   k ≤ n →     
{a ∈ Finset.HasAntidiagonal.antidiagonal n | k ≤ a.1} =       Finset.map ({ toFu
n := fun x => x + k, inj' := ⋯ }.…
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `Finset.HasAntidiagonal.antidiagonal_zero`：∀ {A : Type u_1} [inst : AddCo
mmMonoid A] [inst_1 : PartialOrder A] [CanonicallyOrderedAdd A]   [inst_3 : Fins
et.HasAntidiagonal A], Finset.…
· 使用定理 `Finset.map_singleton`：map_singleton (f : α ↪ β) (a : α) : map f {a} = {f
 a}
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Function.Embedding.refl_apply`：∀ (α : Sort u_1) (a : α), (Function.Embed
ding.refl α) a = a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `MvPolynomial.psum_zero`：psum_zero : psum σ R 0 = Fintype.card σ
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Odd.neg_one_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistrib
Neg α] {n : ℕ}, Odd n → (-1) ^ n = -1
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
（共 32 条，此处仅展示前 30 条）
-/
theorem sum_antidiagonal_card_esymm_psum_eq_zero :
    ∑ a ∈ antidiagonal (Fintype.card σ), (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd = 0 := by
  let k := Fintype.card σ
  suffices (-1 : MvPolynomial σ R) ^ (k + 1) *
      ∑ a ∈ antidiagonal k, (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd = 0 by
    simpa using this
  simp [k, ← sum_filter_add_sum_filter_not (antidiagonal k) (fun a ↦ a.fst < k),
    ← mul_esymm_eq_sum, mul_add, ← mul_assoc, ← pow_add, mul_comm ↑k (esymm σ R k)]

/-- A version of Newton's identities which may be more useful in the case that we know the values of
the elementary symmetric polynomials and would like to calculate the values of the power sums. -/
/-
**MvPolynomial.psum_eq_mul_esymm_sub_sum** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial
`。
形式化陈述：psum_eq_mul_esymm_sub_sum (k : Nat) (h : 0 < k) : psum σ R k = (-1) ^ (k +
 1) * k * esymm σ R k - ∑ a in antidiagonal k with a.1 in Set.Ioo 0 k, (-1) ^ a.
fst * esymm σ R a.1 * psum σ R a.2
参数：k : Nat；h : 0 < k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.mul_esymm_eq_sum`：mul_esymm_eq_sum (k : Nat) : k * esymm σ 
R k = (-1) ^ (k + 1) * ∑ a in antidiagonal k with a.1 < k, (-1) ^ a.1 * esymm σ 
R a.1 * psum σ R a.…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_filter_add_sum_filter_not`：∀ {ι : Type u_1} {M : Type u_4} [i
nst : AddCommMonoid M] (s : Finset ι) (p : ι → Prop) [inst_1 : DecidablePred p] 
  [inst_2 : (x : ι) → Deci…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `left_distrib`：left_distrib [Mul R] [Add R] [LeftDistribClass R] (a b c :
 R) : a * (b + c) = a * b + a * c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Nat.eq_zero_of_not_pos`：∀ {n : ℕ}, ¬0 < n → n = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.filter_filter`：∀ {α : Type u_1} (p q : α → Prop) [inst : Decidabl
ePred p] [inst_1 : DecidablePred q] (s : Finset α),   Finset.filter q (Finset.fi
lter p s) …
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `MvPolynomial.esymm_zero`：esymm_zero : esymm σ R 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `mul_sub_left_distrib`：mul_sub_left_distrib (a b c : α) : a * (b - c) = a
 * b - a * c
· 使用引理 `Even.neg_one_pow`：Even.neg_one_pow (h : Even n) : (-1 : α) ^ n = 1

--- 原说明 ---
A version of Newton's identities which may be more useful in the case that we kn
ow the values of
the elementary symmetric polynomials and would like to calculate the values of t
he power sums.
-/
theorem psum_eq_mul_esymm_sub_sum (k : ℕ) (h : 0 < k) :
    psum σ R k = (-1) ^ (k + 1) * k * esymm σ R k -
    ∑ a ∈ antidiagonal k with a.1 ∈ Set.Ioo 0 k, (-1) ^ a.fst * esymm σ R a.1 * psum σ R a.2 := by
  simp only [Set.Ioo, Set.mem_ofPred_eq, and_comm]
  have hesymm := mul_esymm_eq_sum σ R k
  rw [← (sum_filter_add_sum_filter_not {a ∈ antidiagonal k | a.fst < k}
    (fun a ↦ 0 < a.fst) (fun a ↦ (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd))] at hesymm
  have sub_both_sides := congrArg (· - (-1 : MvPolynomial σ R) ^ (k + 1) *
    ∑ a ∈ {a ∈ antidiagonal k | a.fst < k} with 0 < a.fst,
    (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd) hesymm
  simp only [left_distrib, add_sub_cancel_left] at sub_both_sides
  have sub_both_sides := congrArg ((-1 : MvPolynomial σ R) ^ (k + 1) * ·) sub_both_sides
  simp only [mul_sub_left_distrib, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨k + 1, rfl⟩, one_mul,
    filter_filter (fun a : ℕ × ℕ ↦ a.fst < k) (fun a ↦ ¬0 < a.fst)]
    at sub_both_sides
  have : {a ∈ antidiagonal k | a.fst < k ∧ ¬0 < a.fst} = {(0, k)} := by
    ext a
    rw [mem_filter, mem_antidiagonal, mem_singleton]
    refine ⟨?_, by rintro rfl; lia⟩
    rintro ⟨ha, ⟨_, ha0⟩⟩
    rw [← ha, Nat.eq_zero_of_not_pos ha0, zero_add, ← Nat.eq_zero_of_not_pos ha0]
  rw [this, sum_singleton] at sub_both_sides
  simp only [_root_.pow_zero, esymm_zero, mul_one, one_mul, filter_filter] at sub_both_sides
  exact sub_both_sides.symm

end MvPolynomial

