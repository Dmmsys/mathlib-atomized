/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.GroupWithZero.Regular
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Degree.Defs

/-!
# Lemmas for calculating the degree of univariate polynomials

## Main results
- `degree_mul` : The degree of the product is the sum of degrees
- `leadingCoeff_add_of_degree_eq` and `leadingCoeff_add_of_degree_lt` :
    The leading coefficient of a sum is determined by the leading coefficients and degrees
-/

@[expose] public section

noncomputable section

open Finsupp Finset

open Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b c d : R} {n m : Nat}

section Semiring

variable [Semiring R] [Semiring S] {p q r : R[X]}

/--
theorem `supDegree_eq_degree` / 定理 `supDegree_eq_degree`

English:
theorem supDegree_eq_degree
  given: (p : R[X])
  statement: p.toFinsupp.supDegree WithBot.some = p.degree
  proof: max_eq_sup_coe

中文:
定理 supDegree_eq_degree
  条件: (p : R[X])
  结论: p.toFinsupp.supDegree WithBot.some = p.degree
  证明: max_eq_sup_coe

Depends on / 依赖: max_eq_sup_coe
-/
theorem supDegree_eq_degree (p : R[X]) : p.toFinsupp.supDegree WithBot.some = p.degree :=
  max_eq_sup_coe

/--
theorem `degree_lt_wf` / 定理 `degree_lt_wf`

English:
theorem degree_lt_wf
  statement: WellFounded fun p q : R[X] => degree p < degree q
  proof: InvImage.wf degree wellFounded_lt

中文:
定理 degree_lt_wf
  结论: WellFounded fun p q : R[X] => degree p < degree q
  证明: InvImage.wf degree wellFounded_lt

Depends on / 依赖: InvImage, InvImage.wf, degree, wellFounded_lt
-/
theorem degree_lt_wf : WellFounded fun p q : R[X] => degree p < degree q :=
  InvImage.wf degree wellFounded_lt

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: WellFoundedRelation R[X]
  body: ⟨_, degree_lt_wf⟩

@[nontriviality]

中文:
实例 :
  签名: WellFoundedRelation R[X]
  定义体: ⟨_, degree_lt_wf⟩

@[nontriviality]

Depends on / 依赖: degree_lt_wf
-/
instance : WellFoundedRelation R[X] :=
  ⟨_, degree_lt_wf⟩

@[nontriviality]
/--
theorem `monic_of_subsingleton` / 定理 `monic_of_subsingleton`

English:
theorem monic_of_subsingleton
  given: [Subsingleton R] (p : R[X])
  statement: Monic p
  proof: Subsingleton.elim _ _

@[nontriviality]

中文:
定理 monic_of_subsingleton
  条件: [Subsingleton R] (p : R[X])
  结论: Monic p
  证明: Subsingleton.elim _ _

@[nontriviality]

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem monic_of_subsingleton [Subsingleton R] (p : R[X]) : Monic p :=
  Subsingleton.elim _ _

@[nontriviality]
/--
theorem `degree_of_subsingleton` / 定理 `degree_of_subsingleton`

English:
theorem degree_of_subsingleton
  given: [Subsingleton R]
  statement: degree p = ⊥
  proof: by
  rw [Subsingleton.elim p 0]; rw [degree_zero]

@[nontriviality]

中文:
定理 degree_of_subsingleton
  条件: [Subsingleton R]
  结论: degree p = ⊥
  证明: by
  rw [Subsingleton.elim p 0]; rw [degree_zero]

@[nontriviality]

Depends on / 依赖: Subsingleton, Subsingleton.elim, degree_zero
-/
theorem degree_of_subsingleton [Subsingleton R] : degree p = ⊥ := by
  rw [Subsingleton.elim p 0]; rw [degree_zero]

@[nontriviality]
/--
theorem `natDegree_of_subsingleton` / 定理 `natDegree_of_subsingleton`

English:
theorem natDegree_of_subsingleton
  given: [Subsingleton R]
  statement: natDegree p = 0
  proof: by
  rw [Subsingleton.elim p 0]; rw [natDegree_zero]

中文:
定理 natDegree_of_subsingleton
  条件: [Subsingleton R]
  结论: natDegree p = 0
  证明: by
  rw [Subsingleton.elim p 0]; rw [natDegree_zero]

Depends on / 依赖: Subsingleton, Subsingleton.elim, natDegree_zero
-/
theorem natDegree_of_subsingleton [Subsingleton R] : natDegree p = 0 := by
  rw [Subsingleton.elim p 0]; rw [natDegree_zero]

/--
theorem `le_natDegree_of_ne_zero` / 定理 `le_natDegree_of_ne_zero`

English:
theorem le_natDegree_of_ne_zero
  given: (h : coeff p n != 0)
  statement: n <= natDegree p
  proof: by
  rw [← Nat.cast_le (α := WithBot Nat)]; rw [← degree_eq_natDegree]
  · exact le_degree_of_ne_zero h
  · rintro rfl
    exact h rfl

中文:
定理 le_natDegree_of_ne_zero
  条件: (h : coeff p n != 0)
  结论: n <= natDegree p
  证明: by
  rw [← Nat.cast_le (α := WithBot Nat)]; rw [← degree_eq_natDegree]
  · exact le_degree_of_ne_zero h
  · rintro rfl
    exact h rfl

Depends on / 依赖: Nat.cast_le, WithBot, cast_le, degree_eq_natDegree, le_degree_of_ne_zero
-/
theorem le_natDegree_of_ne_zero (h : coeff p n != 0) : n <= natDegree p := by
  rw [← Nat.cast_le (α := WithBot Nat)]; rw [← degree_eq_natDegree]
  · exact le_degree_of_ne_zero h
  · rintro rfl
    exact h rfl

/--
theorem `degree_eq_of_le_of_coeff_ne_zero` / 定理 `degree_eq_of_le_of_coeff_ne_zero`

English:
theorem degree_eq_of_le_of_coeff_ne_zero
  given: (pn : p.degree <= n) (p1 : p.coeff n != 0)
  statement: p.degree = n
  proof: pn.antisymm (le_degree_of_ne_zero p1)

中文:
定理 degree_eq_of_le_of_coeff_ne_zero
  条件: (pn : p.degree <= n) (p1 : p.coeff n != 0)
  结论: p.degree = n
  证明: pn.antisymm (le_degree_of_ne_zero p1)

Depends on / 依赖: antisymm, le_degree_of_ne_zero, pn.antisymm
-/
theorem degree_eq_of_le_of_coeff_ne_zero (pn : p.degree <= n) (p1 : p.coeff n != 0) : p.degree = n :=
  pn.antisymm (le_degree_of_ne_zero p1)

/--
theorem `natDegree_eq_of_le_of_coeff_ne_zero` / 定理 `natDegree_eq_of_le_of_coeff_ne_zero`

English:
theorem natDegree_eq_of_le_of_coeff_ne_zero
  given: (pn : p.natDegree <= n) (p1 : p.coeff n != 0)
  proof: pn.antisymm (le_natDegree_of_ne_zero p1)

中文:
定理 natDegree_eq_of_le_of_coeff_ne_zero
  条件: (pn : p.natDegree <= n) (p1 : p.coeff n != 0)
  证明: pn.antisymm (le_natDegree_of_ne_zero p1)

Depends on / 依赖: antisymm, le_natDegree_of_ne_zero, pn.antisymm
-/
theorem natDegree_eq_of_le_of_coeff_ne_zero (pn : p.natDegree <= n) (p1 : p.coeff n != 0) :
    p.natDegree = n :=
  pn.antisymm (le_natDegree_of_ne_zero p1)

/--
theorem `natDegree_lt_natDegree` / 定理 `natDegree_lt_natDegree`

English:
theorem natDegree_lt_natDegree
  given: {q : S[X]} (hp : p != 0) (hpq : p.degree < q.degree)
  proof: by
  by_cases hq : q = 0
  · exact (not_lt_bot <| hq ▸ hpq).elim
  rwa [degree_eq_natDegree hp, degree_eq_natDegree hq, Nat.cast_lt] at hpq

中文:
定理 natDegree_lt_natDegree
  条件: {q : S[X]} (hp : p != 0) (hpq : p.degree < q.degree)
  证明: by
  by_cases hq : q = 0
  · exact (not_lt_bot <| hq ▸ hpq).elim
  rwa [degree_eq_natDegree hp, degree_eq_natDegree hq, Nat.cast_lt] at hpq

Depends on / 依赖: Nat.cast_lt, cast_lt, degree_eq_natDegree, not_lt_bot
-/
theorem natDegree_lt_natDegree {q : S[X]} (hp : p != 0) (hpq : p.degree < q.degree) :
    p.natDegree < q.natDegree := by
  by_cases hq : q = 0
  · exact (not_lt_bot <| hq ▸ hpq).elim
  rwa [degree_eq_natDegree hp, degree_eq_natDegree hq, Nat.cast_lt] at hpq

/--
lemma `natDegree_eq_natDegree` / 引理 `natDegree_eq_natDegree`

English:
lemma natDegree_eq_natDegree
  given: {q : S[X]} (hpq : p.degree = q.degree)
  proof: by simp [natDegree, hpq]

中文:
引理 natDegree_eq_natDegree
  条件: {q : S[X]} (hpq : p.degree = q.degree)
  证明: by simp [natDegree, hpq]

Depends on / 依赖: natDegree
-/
lemma natDegree_eq_natDegree {q : S[X]} (hpq : p.degree = q.degree) :
    p.natDegree = q.natDegree := by simp [natDegree, hpq]

/--
theorem `coeff_eq_zero_of_degree_lt` / 定理 `coeff_eq_zero_of_degree_lt`

English:
theorem coeff_eq_zero_of_degree_lt
  given: (h : degree p < n)
  statement: coeff p n = 0
  proof: Classical.not_not.1 (mt le_degree_of_ne_zero (not_le_of_gt h))

中文:
定理 coeff_eq_zero_of_degree_lt
  条件: (h : degree p < n)
  结论: coeff p n = 0
  证明: Classical.not_not.1 (mt le_degree_of_ne_zero (not_le_of_gt h))

Depends on / 依赖: Classical, Classical.not_not, le_degree_of_ne_zero, not_le_of_gt, not_not
-/
theorem coeff_eq_zero_of_degree_lt (h : degree p < n) : coeff p n = 0 :=
  Classical.not_not.1 (mt le_degree_of_ne_zero (not_le_of_gt h))

/--
theorem `coeff_eq_zero_of_natDegree_lt` / 定理 `coeff_eq_zero_of_natDegree_lt`

English:
theorem coeff_eq_zero_of_natDegree_lt
  given: {p : R[X]} {n : Nat} (h : p.natDegree < n)
  proof: by
  apply coeff_eq_zero_of_degree_lt
  by_cases hp : p = 0
  · subst hp
    exact WithBot.bot_lt_coe n
  · rwa [degree_eq_natDegree hp, Nat.cast_lt]

中文:
定理 coeff_eq_zero_of_natDegree_lt
  条件: {p : R[X]} {n : 自然数} (h : p.natDegree < n)
  证明: by
  apply coeff_eq_zero_of_degree_lt
  by_cases hp : p = 0
  · subst hp
    exact WithBot.bot_lt_coe n
  · rwa [degree_eq_natDegree hp, Nat.cast_lt]

Depends on / 依赖: Nat.cast_lt, WithBot, WithBot.bot_lt_coe, bot_lt_coe, cast_lt, coeff_eq_zero_of_degree_lt, degree_eq_natDegree
-/
theorem coeff_eq_zero_of_natDegree_lt {p : R[X]} {n : Nat} (h : p.natDegree < n) :
    p.coeff n = 0 := by
  apply coeff_eq_zero_of_degree_lt
  by_cases hp : p = 0
  · subst hp
    exact WithBot.bot_lt_coe n
  · rwa [degree_eq_natDegree hp, Nat.cast_lt]

/--
theorem `ext_iff_natDegree_le` / 定理 `ext_iff_natDegree_le`

English:
theorem ext_iff_natDegree_le
  given: {p q : R[X]} {n : Nat} (hp : p.natDegree <= n) (hq : q.natDegree <= n)
  proof: by
  refine Iff.trans Polynomial.ext_iff ?_
  refine forall_congr' fun i => ⟨fun h _ => h, fun h => ?_⟩
  refine (le_or_gt i n).elim h fun k => ?_
  exact
    (coeff_eq_zero_of_natDegree_lt (hp.trans_lt k)).trans
      (coeff_eq_zero_of_natDegree_lt (hq.trans_lt k)).symm

中文:
定理 ext_iff_natDegree_le
  条件: {p q : R[X]} {n : 自然数} (hp : p.natDegree <= n) (hq : q.natDegree <= n)
  证明: by
  refine Iff.trans Polynomial.ext_iff ?_
  refine forall_congr' fun i => ⟨fun h _ => h, fun h => ?_⟩
  refine (le_or_gt i n).elim h fun k => ?_
  exact
    (coeff_eq_zero_of_natDegree_lt (hp.trans_lt k)).trans
      (coeff_eq_zero_of_natDegree_lt (hq.trans_lt k)).symm

Depends on / 依赖: Iff.trans, Polynomial, Polynomial.ext_iff, coeff_eq_zero_of_natDegree_lt, ext_iff, forall_congr, hp.trans_lt, hq.trans_lt, le_or_gt, trans_lt
-/
theorem ext_iff_natDegree_le {p q : R[X]} {n : Nat} (hp : p.natDegree <= n) (hq : q.natDegree <= n) :
    p = q ↔ forall i <= n, p.coeff i = q.coeff i := by
  refine Iff.trans Polynomial.ext_iff ?_
  refine forall_congr' fun i => ⟨fun h _ => h, fun h => ?_⟩
  refine (le_or_gt i n).elim h fun k => ?_
  exact
    (coeff_eq_zero_of_natDegree_lt (hp.trans_lt k)).trans
      (coeff_eq_zero_of_natDegree_lt (hq.trans_lt k)).symm

/--
theorem `ext_iff_degree_le` / 定理 `ext_iff_degree_le`

English:
theorem ext_iff_degree_le
  given: {p q : R[X]} {n : Nat} (hp : p.degree <= n) (hq : q.degree <= n)
  proof: ext_iff_natDegree_le (natDegree_le_of_degree_le hp) (natDegree_le_of_degree_le hq)

@[simp]

中文:
定理 ext_iff_degree_le
  条件: {p q : R[X]} {n : 自然数} (hp : p.degree <= n) (hq : q.degree <= n)
  证明: ext_iff_natDegree_le (natDegree_le_of_degree_le hp) (natDegree_le_of_degree_le hq)

@[simp]

Depends on / 依赖: ext_iff_natDegree_le, natDegree_le_of_degree_le
-/
theorem ext_iff_degree_le {p q : R[X]} {n : Nat} (hp : p.degree <= n) (hq : q.degree <= n) :
    p = q ↔ forall i <= n, p.coeff i = q.coeff i :=
  ext_iff_natDegree_le (natDegree_le_of_degree_le hp) (natDegree_le_of_degree_le hq)

@[simp]
/--
theorem `coeff_natDegree_succ_eq_zero` / 定理 `coeff_natDegree_succ_eq_zero`

English:
theorem coeff_natDegree_succ_eq_zero
  given: {p : R[X]}
  statement: p.coeff (p.natDegree + 1) = 0
  proof: coeff_eq_zero_of_natDegree_lt (lt_add_one _)

中文:
定理 coeff_natDegree_succ_eq_zero
  条件: {p : R[X]}
  结论: p.coeff (p.natDegree + 1) = 0
  证明: coeff_eq_zero_of_natDegree_lt (lt_add_one _)

Depends on / 依赖: coeff_eq_zero_of_natDegree_lt, lt_add_one
-/
theorem coeff_natDegree_succ_eq_zero {p : R[X]} : p.coeff (p.natDegree + 1) = 0 :=
  coeff_eq_zero_of_natDegree_lt (lt_add_one _)

-- We need the explicit `Decidable` argument here because an exotic one shows up in a moment!
/--
theorem `ite_le_natDegree_coeff` / 定理 `ite_le_natDegree_coeff`

English:
theorem ite_le_natDegree_coeff
  given: (p : R[X]) (n : Nat) (I : Decidable (n < 1 + natDegree p))
  proof: by
  split_ifs with h
  · rfl
  · exact (coeff_eq_zero_of_natDegree_lt (not_le.1 fun w => h (Nat.lt_one_add_iff.2 w))).symm

中文:
定理 ite_le_natDegree_coeff
  条件: (p : R[X]) (n : 自然数) (I : Decidable (n < 1 + natDegree p))
  证明: by
  split_ifs with h
  · rfl
  · exact (coeff_eq_zero_of_natDegree_lt (not_le.1 fun w => h (Nat.lt_one_add_iff.2 w))).symm

Depends on / 依赖: Nat.lt_one_add_iff, coeff_eq_zero_of_natDegree_lt, lt_one_add_iff, not_le, split_ifs
-/
theorem ite_le_natDegree_coeff (p : R[X]) (n : Nat) (I : Decidable (n < 1 + natDegree p)) :
    @ite _ (n < 1 + natDegree p) I (coeff p n) 0 = coeff p n := by
  split_ifs with h
  · rfl
  · exact (coeff_eq_zero_of_natDegree_lt (not_le.1 fun w => h (Nat.lt_one_add_iff.2 w))).symm

end Semiring

section Ring

variable [Ring R]

/--
theorem `coeff_mul_X_sub_C` / 定理 `coeff_mul_X_sub_C`

English:
theorem coeff_mul_X_sub_C
  given: {p : R[X]} {r : R} {a : Nat}
  proof: by simp [mul_sub]

中文:
定理 coeff_mul_X_sub_C
  条件: {p : R[X]} {r : R} {a : 自然数}
  证明: by simp [mul_sub]

Depends on / 依赖: mul_sub
-/
theorem coeff_mul_X_sub_C {p : R[X]} {r : R} {a : Nat} :
    coeff (p * (X - C r)) (a + 1) = coeff p a - coeff p (a + 1) * r := by simp [mul_sub]

/--
theorem `coeff_X_sub_C_mul` / 定理 `coeff_X_sub_C_mul`

English:
theorem coeff_X_sub_C_mul
  given: {p : R[X]} {r : R} {a : Nat}
  proof: by simp [sub_mul]

中文:
定理 coeff_X_sub_C_mul
  条件: {p : R[X]} {r : R} {a : 自然数}
  证明: by simp [sub_mul]

Depends on / 依赖: sub_mul
-/
theorem coeff_X_sub_C_mul {p : R[X]} {r : R} {a : Nat} :
    coeff ((X - C r) * p) (a + 1) = coeff p a - r * coeff p (a + 1) := by simp [sub_mul]

end Ring

section Semiring

variable [Semiring R] {p q : R[X]} {ι : Type*}

/--
theorem `coeff_natDegree_eq_zero_of_degree_lt` / 定理 `coeff_natDegree_eq_zero_of_degree_lt`

English:
theorem coeff_natDegree_eq_zero_of_degree_lt
  given: (h : degree p < degree q)
  proof: coeff_eq_zero_of_degree_lt (lt_of_lt_of_le h degree_le_natDegree)

中文:
定理 coeff_natDegree_eq_zero_of_degree_lt
  条件: (h : degree p < degree q)
  证明: coeff_eq_zero_of_degree_lt (lt_of_lt_of_le h degree_le_natDegree)

Depends on / 依赖: coeff_eq_zero_of_degree_lt, degree_le_natDegree, lt_of_lt_of_le
-/
theorem coeff_natDegree_eq_zero_of_degree_lt (h : degree p < degree q) :
    coeff p (natDegree q) = 0 :=
  coeff_eq_zero_of_degree_lt (lt_of_lt_of_le h degree_le_natDegree)

/--
theorem `ne_zero_of_degree_gt` / 定理 `ne_zero_of_degree_gt`

English:
theorem ne_zero_of_degree_gt
  given: {n : WithBot Nat} (h : n < degree p)
  statement: p != 0
  proof: mt degree_eq_bot.2 h.ne_bot

中文:
定理 ne_zero_of_degree_gt
  条件: {n : WithBot 自然数} (h : n < degree p)
  结论: p != 0
  证明: mt degree_eq_bot.2 h.ne_bot

Depends on / 依赖: degree_eq_bot, h.ne_bot, ne_bot
-/
theorem ne_zero_of_degree_gt {n : WithBot Nat} (h : n < degree p) : p != 0 :=
  mt degree_eq_bot.2 h.ne_bot

/--
theorem `ne_zero_of_degree_ge_degree` / 定理 `ne_zero_of_degree_ge_degree`

English:
theorem ne_zero_of_degree_ge_degree
  given: (hpq : p.degree <= q.degree) (hp : p != 0)
  statement: q != 0
  proof: Polynomial.ne_zero_of_degree_gt
    (lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr (by rwa [Ne, Polynomial.degree_eq_bot])) hpq :
      q.degree > ⊥)

中文:
定理 ne_zero_of_degree_ge_degree
  条件: (hpq : p.degree <= q.degree) (hp : p != 0)
  结论: q != 0
  证明: Polynomial.ne_zero_of_degree_gt
    (lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr (by rwa [Ne, Polynomial.degree_eq_bot])) hpq :
      q.degree > ⊥)

Depends on / 依赖: Polynomial, Polynomial.degree_eq_bot, Polynomial.ne_zero_of_degree_gt, bot_lt_iff_ne_bot, bot_lt_iff_ne_bot.mpr, degree, degree_eq_bot, lt_of_lt_of_le, ne_zero_of_degree_gt, q.degree
-/
theorem ne_zero_of_degree_ge_degree (hpq : p.degree <= q.degree) (hp : p != 0) : q != 0 :=
  Polynomial.ne_zero_of_degree_gt
    (lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr (by rwa [Ne, Polynomial.degree_eq_bot])) hpq :
      q.degree > ⊥)

/--
theorem `ne_zero_of_natDegree_gt` / 定理 `ne_zero_of_natDegree_gt`

English:
theorem ne_zero_of_natDegree_gt
  given: {n : Nat} (h : n < natDegree p)
  statement: p != 0
  proof: fun H => by
  simp [H] at h

中文:
定理 ne_zero_of_natDegree_gt
  条件: {n : 自然数} (h : n < natDegree p)
  结论: p != 0
  证明: fun H => by
  simp [H] at h
-/
theorem ne_zero_of_natDegree_gt {n : Nat} (h : n < natDegree p) : p != 0 := fun H => by
  simp [H] at h

/--
theorem `degree_lt_degree` / 定理 `degree_lt_degree`

English:
theorem degree_lt_degree
  given: (h : natDegree p < natDegree q)
  statement: degree p < degree q
  proof: by
  by_cases hp : p = 0
  · simp only [hp, degree_zero]
    rw [bot_lt_iff_ne_bot]
    intro hq
    simp [hp, degree_eq_bot.mp hq] at h
  · rwa [degree_eq_natDegree hp, degree_eq_natDegree <| ne_zero_of_natDegree_gt h, Nat.cast_lt]

中文:
定理 degree_lt_degree
  条件: (h : natDegree p < natDegree q)
  结论: degree p < degree q
  证明: by
  by_cases hp : p = 0
  · simp only [hp, degree_zero]
    rw [bot_lt_iff_ne_bot]
    intro hq
    simp [hp, degree_eq_bot.mp hq] at h
  · rwa [degree_eq_natDegree hp, degree_eq_natDegree <| ne_zero_of_natDegree_gt h, Nat.cast_lt]

Depends on / 依赖: Nat.cast_lt, bot_lt_iff_ne_bot, cast_lt, degree_eq_bot, degree_eq_bot.mp, degree_eq_natDegree, degree_zero, ne_zero_of_natDegree_gt
-/
theorem degree_lt_degree (h : natDegree p < natDegree q) : degree p < degree q := by
  by_cases hp : p = 0
  · simp only [hp, degree_zero]
    rw [bot_lt_iff_ne_bot]
    intro hq
    simp [hp, degree_eq_bot.mp hq] at h
  · rwa [degree_eq_natDegree hp, degree_eq_natDegree <| ne_zero_of_natDegree_gt h, Nat.cast_lt]

/--
theorem `natDegree_lt_natDegree_iff` / 定理 `natDegree_lt_natDegree_iff`

English:
theorem natDegree_lt_natDegree_iff
  given: (hp : p != 0)
  statement: natDegree p < natDegree q ↔ degree p < degree q
  proof: ⟨degree_lt_degree, fun h => by
    have hq : q != 0 := ne_zero_of_degree_gt h
    rwa [degree_eq_natDegree hp, degree_eq_natDegree hq, Nat.cast_lt] at h⟩

中文:
定理 natDegree_lt_natDegree_iff
  条件: (hp : p != 0)
  结论: natDegree p < natDegree q ↔ degree p < degree q
  证明: ⟨degree_lt_degree, fun h => by
    have hq : q != 0 := ne_zero_of_degree_gt h
    rwa [degree_eq_natDegree hp, degree_eq_natDegree hq, Nat.cast_lt] at h⟩

Depends on / 依赖: Nat.cast_lt, cast_lt, degree_eq_natDegree, degree_lt_degree, ne_zero_of_degree_gt
-/
theorem natDegree_lt_natDegree_iff (hp : p != 0) : natDegree p < natDegree q ↔ degree p < degree q :=
  ⟨degree_lt_degree, fun h => by
    have hq : q != 0 := ne_zero_of_degree_gt h
    rwa [degree_eq_natDegree hp, degree_eq_natDegree hq, Nat.cast_lt] at h⟩

/--
theorem `eq_C_of_degree_le_zero` / 定理 `eq_C_of_degree_le_zero`

English:
theorem eq_C_of_degree_le_zero
  given: (h : degree p <= 0)
  statement: p = C (coeff p 0)
  proof: by
  ext (_ | n)
  · simp
  rw [coeff_C]; rw [if_neg (Nat.succ_ne_zero _)]; rw [coeff_eq_zero_of_degree_lt]
  exact h.trans_lt (WithBot.coe_lt_coe.2 n.succ_pos)

中文:
定理 eq_C_of_degree_le_zero
  条件: (h : degree p <= 0)
  结论: p = C (coeff p 0)
  证明: by
  ext (_ | n)
  · simp
  rw [coeff_C]; rw [if_neg (Nat.succ_ne_zero _)]; rw [coeff_eq_zero_of_degree_lt]
  exact h.trans_lt (WithBot.coe_lt_coe.2 n.succ_pos)

Depends on / 依赖: Nat.succ_ne_zero, WithBot, WithBot.coe_lt_coe, coe_lt_coe, coeff_C, coeff_eq_zero_of_degree_lt, h.trans_lt, if_neg, n.succ_pos, succ_ne_zero, succ_pos, trans_lt
-/
theorem eq_C_of_degree_le_zero (h : degree p <= 0) : p = C (coeff p 0) := by
  ext (_ | n)
  · simp
  rw [coeff_C]; rw [if_neg (Nat.succ_ne_zero _)]; rw [coeff_eq_zero_of_degree_lt]
  exact h.trans_lt (WithBot.coe_lt_coe.2 n.succ_pos)

/--
theorem `eq_C_of_degree_eq_zero` / 定理 `eq_C_of_degree_eq_zero`

English:
theorem eq_C_of_degree_eq_zero
  given: (h : degree p = 0)
  statement: p = C (coeff p 0)
  proof: eq_C_of_degree_le_zero h.le

中文:
定理 eq_C_of_degree_eq_zero
  条件: (h : degree p = 0)
  结论: p = C (coeff p 0)
  证明: eq_C_of_degree_le_zero h.le

Depends on / 依赖: eq_C_of_degree_le_zero, h.le
-/
theorem eq_C_of_degree_eq_zero (h : degree p = 0) : p = C (coeff p 0) :=
  eq_C_of_degree_le_zero h.le

/--
theorem `degree_le_zero_iff` / 定理 `degree_le_zero_iff`

English:
theorem degree_le_zero_iff
  statement: degree p <= 0 ↔ p = C (coeff p 0)
  proof: ⟨eq_C_of_degree_le_zero, fun h => h.symm ▸ degree_C_le⟩

中文:
定理 degree_le_zero_iff
  结论: degree p <= 0 ↔ p = C (coeff p 0)
  证明: ⟨eq_C_of_degree_le_zero, fun h => h.symm ▸ degree_C_le⟩

Depends on / 依赖: degree_C_le, eq_C_of_degree_le_zero, h.symm
-/
theorem degree_le_zero_iff : degree p <= 0 ↔ p = C (coeff p 0) :=
  ⟨eq_C_of_degree_le_zero, fun h => h.symm ▸ degree_C_le⟩

/--
theorem `degree_add_eq_left_of_degree_lt` / 定理 `degree_add_eq_left_of_degree_lt`

English:
theorem degree_add_eq_left_of_degree_lt
  given: (h : degree q < degree p)
  statement: degree (p + q) = degree p
  proof: le_antisymm (max_eq_left_of_lt h ▸ degree_add_le _ _)
degree_le_degree by
      rw [coeff_add]; rw [coeff_natDegree_eq_zero_of_degree_lt h]; rw [add_zero]
      exact mt leadingCoeff_eq_zero.1 (ne_zero_of_degree_gt h)

中文:
定理 degree_add_eq_left_of_degree_lt
  条件: (h : degree q < degree p)
  结论: degree (p + q) = degree p
  证明: le_antisymm (max_eq_left_of_lt h ▸ degree_add_le _ _)
degree_le_degree by
      rw [coeff_add]; rw [coeff_natDegree_eq_zero_of_degree_lt h]; rw [add_zero]
      exact mt leadingCoeff_eq_zero.1 (ne_zero_of_degree_gt h)

Depends on / 依赖: add_zero, coeff_add, coeff_natDegree_eq_zero_of_degree_lt, degree_add_le, degree_le_degree, le_antisymm, leadingCoeff_eq_zero, max_eq_left_of_lt, ne_zero_of_degree_gt
-/
theorem degree_add_eq_left_of_degree_lt (h : degree q < degree p) : degree (p + q) = degree p :=
le_antisymm (max_eq_left_of_lt h ▸ degree_add_le _ _)
degree_le_degree by
      rw [coeff_add]; rw [coeff_natDegree_eq_zero_of_degree_lt h]; rw [add_zero]
      exact mt leadingCoeff_eq_zero.1 (ne_zero_of_degree_gt h)

/--
theorem `degree_add_eq_right_of_degree_lt` / 定理 `degree_add_eq_right_of_degree_lt`

English:
theorem degree_add_eq_right_of_degree_lt
  given: (h : degree p < degree q)
  statement: degree (p + q) = degree q
  proof: by
  rw [add_comm]; rw [degree_add_eq_left_of_degree_lt h]

中文:
定理 degree_add_eq_right_of_degree_lt
  条件: (h : degree p < degree q)
  结论: degree (p + q) = degree q
  证明: by
  rw [add_comm]; rw [degree_add_eq_left_of_degree_lt h]

Depends on / 依赖: add_comm, degree_add_eq_left_of_degree_lt
-/
theorem degree_add_eq_right_of_degree_lt (h : degree p < degree q) : degree (p + q) = degree q := by
  rw [add_comm]; rw [degree_add_eq_left_of_degree_lt h]

/--
theorem `natDegree_add_eq_left_of_degree_lt` / 定理 `natDegree_add_eq_left_of_degree_lt`

English:
theorem natDegree_add_eq_left_of_degree_lt
  given: (h : degree q < degree p)
  proof: natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt h)

中文:
定理 natDegree_add_eq_left_of_degree_lt
  条件: (h : degree q < degree p)
  证明: natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt h)

Depends on / 依赖: degree_add_eq_left_of_degree_lt, natDegree_eq_of_degree_eq
-/
theorem natDegree_add_eq_left_of_degree_lt (h : degree q < degree p) :
    natDegree (p + q) = natDegree p :=
  natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt h)

/--
theorem `natDegree_add_eq_left_of_natDegree_lt` / 定理 `natDegree_add_eq_left_of_natDegree_lt`

English:
theorem natDegree_add_eq_left_of_natDegree_lt
  given: (h : natDegree q < natDegree p)
  proof: natDegree_add_eq_left_of_degree_lt (degree_lt_degree h)

中文:
定理 natDegree_add_eq_left_of_natDegree_lt
  条件: (h : natDegree q < natDegree p)
  证明: natDegree_add_eq_left_of_degree_lt (degree_lt_degree h)

Depends on / 依赖: degree_lt_degree, natDegree_add_eq_left_of_degree_lt
-/
theorem natDegree_add_eq_left_of_natDegree_lt (h : natDegree q < natDegree p) :
    natDegree (p + q) = natDegree p :=
  natDegree_add_eq_left_of_degree_lt (degree_lt_degree h)

/--
theorem `natDegree_add_eq_right_of_degree_lt` / 定理 `natDegree_add_eq_right_of_degree_lt`

English:
theorem natDegree_add_eq_right_of_degree_lt
  given: (h : degree p < degree q)
  proof: natDegree_eq_of_degree_eq (degree_add_eq_right_of_degree_lt h)

中文:
定理 natDegree_add_eq_right_of_degree_lt
  条件: (h : degree p < degree q)
  证明: natDegree_eq_of_degree_eq (degree_add_eq_right_of_degree_lt h)

Depends on / 依赖: degree_add_eq_right_of_degree_lt, natDegree_eq_of_degree_eq
-/
theorem natDegree_add_eq_right_of_degree_lt (h : degree p < degree q) :
    natDegree (p + q) = natDegree q :=
  natDegree_eq_of_degree_eq (degree_add_eq_right_of_degree_lt h)

/--
theorem `natDegree_add_eq_right_of_natDegree_lt` / 定理 `natDegree_add_eq_right_of_natDegree_lt`

English:
theorem natDegree_add_eq_right_of_natDegree_lt
  given: (h : natDegree p < natDegree q)
  proof: natDegree_add_eq_right_of_degree_lt (degree_lt_degree h)

中文:
定理 natDegree_add_eq_right_of_natDegree_lt
  条件: (h : natDegree p < natDegree q)
  证明: natDegree_add_eq_right_of_degree_lt (degree_lt_degree h)

Depends on / 依赖: degree_lt_degree, natDegree_add_eq_right_of_degree_lt
-/
theorem natDegree_add_eq_right_of_natDegree_lt (h : natDegree p < natDegree q) :
    natDegree (p + q) = natDegree q :=
  natDegree_add_eq_right_of_degree_lt (degree_lt_degree h)

/--
theorem `degree_add_C` / 定理 `degree_add_C`

English:
theorem degree_add_C
  given: (hp : 0 < degree p)
  statement: degree (p + C a) = degree p
  proof: add_comm (C a) p ▸ degree_add_eq_right_of_degree_lt lt_of_le_of_lt degree_C_le hp

中文:
定理 degree_add_C
  条件: (hp : 0 < degree p)
  结论: degree (p + C a) = degree p
  证明: add_comm (C a) p ▸ degree_add_eq_right_of_degree_lt lt_of_le_of_lt degree_C_le hp

Depends on / 依赖: add_comm, degree_C_le, degree_add_eq_right_of_degree_lt, lt_of_le_of_lt
-/
theorem degree_add_C (hp : 0 < degree p) : degree (p + C a) = degree p :=
add_comm (C a) p ▸ degree_add_eq_right_of_degree_lt lt_of_le_of_lt degree_C_le hp

/--
theorem `natDegree_add_C` / 定理 `natDegree_add_C`

English:
theorem natDegree_add_C
  given: {a : R}
  statement: (p + C a).natDegree = p.natDegree
  proof: by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  by_cases! hpd : p.degree <= 0
  · rw [eq_C_of_degree_le_zero hpd, ← C_add, natDegree_C, natDegree_C]
  · rw [degree_eq_natDegree hp, Nat.cast_pos, ← natDegree_C a] at hpd
    exact natDegree_add_eq_left_of_natDegree_lt hpd

中文:
定理 natDegree_add_C
  条件: {a : R}
  结论: (p + C a).natDegree = p.natDegree
  证明: by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  by_cases! hpd : p.degree <= 0
  · rw [eq_C_of_degree_le_zero hpd, ← C_add, natDegree_C, natDegree_C]
  · rw [degree_eq_natDegree hp, Nat.cast_pos, ← natDegree_C a] at hpd
    exact natDegree_add_eq_left_of_natDegree_lt hpd
-/
@[simp, grind =] theorem natDegree_add_C {a : R} : (p + C a).natDegree = p.natDegree := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  by_cases! hpd : p.degree <= 0
  · rw [eq_C_of_degree_le_zero hpd, ← C_add, natDegree_C, natDegree_C]
  · rw [degree_eq_natDegree hp, Nat.cast_pos, ← natDegree_C a] at hpd
    exact natDegree_add_eq_left_of_natDegree_lt hpd

/--
theorem `natDegree_C_add` / 定理 `natDegree_C_add`

English:
theorem natDegree_C_add
  given: {a : R}
  statement: (C a + p).natDegree = p.natDegree
  proof: by
  simp [add_comm _ p]

中文:
定理 natDegree_C_add
  条件: {a : R}
  结论: (C a + p).natDegree = p.natDegree
  证明: by
  simp [add_comm _ p]
-/
@[simp] theorem natDegree_C_add {a : R} : (C a + p).natDegree = p.natDegree := by
  simp [add_comm _ p]

/--
theorem `degree_add_eq_of_leadingCoeff_add_ne_zero` / 定理 `degree_add_eq_of_leadingCoeff_add_ne_zero`

English:
theorem degree_add_eq_of_leadingCoeff_add_ne_zero
  given: (h : leadingCoeff p + leadingCoeff q != 0)
  proof: le_antisymm (degree_add_le _ _)
    match lt_trichotomy (degree p) (degree q) with
    | Or.inl hlt => by
      rw [degree_add_eq_right_of_degree_lt hlt]; rw [max_eq_right_of_lt hlt]
    | Or.inr (Or.inl HEq) =>
      le_of_not_gt fun hlt : max (degree p) (degree q) > degree (p + q) =>
h
          s

中文:
定理 degree_add_eq_of_leadingCoeff_add_ne_zero
  条件: (h : leadingCoeff p + leadingCoeff q != 0)
  证明: le_antisymm (degree_add_le _ _)
    match lt_trichotomy (degree p) (degree q) with
    | Or.inl hlt => by
      rw [degree_add_eq_right_of_degree_lt hlt]; rw [max_eq_right_of_lt hlt]
    | Or.inr (Or.inl HEq) =>
      le_of_not_gt fun hlt : max (degree p) (degree q) > degree (p + q) =>
h
          s

Depends on / 依赖: Or.inl, Or.inr, coeff_add, coeff_natDegree_eq_zero_of_degree_lt, degree, degree_add_eq_right_of_degree_lt, degree_add_le, le_antisymm, le_of_not_gt, leadingCoeff, lt_trichotomy, max_eq_right_of_lt, max_self, natDegree_eq_of_degree_eq
-/
theorem degree_add_eq_of_leadingCoeff_add_ne_zero (h : leadingCoeff p + leadingCoeff q != 0) :
    degree (p + q) = max p.degree q.degree :=
le_antisymm (degree_add_le _ _)
    match lt_trichotomy (degree p) (degree q) with
    | Or.inl hlt => by
      rw [degree_add_eq_right_of_degree_lt hlt]; rw [max_eq_right_of_lt hlt]
    | Or.inr (Or.inl HEq) =>
      le_of_not_gt fun hlt : max (degree p) (degree q) > degree (p + q) =>
h
          show leadingCoeff p + leadingCoeff q = 0 by
            rw [HEq]; rw [max_self] at hlt
            rw [leadingCoeff]; rw [leadingCoeff]; rw [natDegree_eq_of_degree_eq HEq]; rw [← coeff_add]
            exact coeff_natDegree_eq_zero_of_degree_lt hlt
    | Or.inr (Or.inr hlt) => by
      rw [degree_add_eq_left_of_degree_lt hlt]; rw [max_eq_left_of_lt hlt]

/--
lemma `natDegree_eq_of_natDegree_add_lt_left` / 引理 `natDegree_eq_of_natDegree_add_lt_left`

English:
lemma natDegree_eq_of_natDegree_add_lt_left
  statement: (p q : R[X])
  proof: by
  by_contra h
  cases Nat.lt_or_lt_of_ne h with
  | inl h => exact lt_asymm h (by rwa [natDegree_add_eq_right_of_natDegree_lt h] at H)
  | inr h =>
    rw [natDegree_add_eq_left_of_natDegree_lt h] at H
    exact LT.lt.false H

中文:
引理 natDegree_eq_of_natDegree_add_lt_left
  结论: (p q : R[X])
  证明: by
  by_contra h
  cases Nat.lt_or_lt_of_ne h with
  | inl h => exact lt_asymm h (by rwa [natDegree_add_eq_right_of_natDegree_lt h] at H)
  | inr h =>
    rw [natDegree_add_eq_left_of_natDegree_lt h] at H
    exact LT.lt.false H

Depends on / 依赖: LT.lt.false, Nat.lt_or_lt_of_ne, lt_asymm, lt_or_lt_of_ne, natDegree_add_eq_left_of_natDegree_lt, natDegree_add_eq_right_of_natDegree_lt
-/
lemma natDegree_eq_of_natDegree_add_lt_left (p q : R[X])
    (H : natDegree (p + q) < natDegree p) : natDegree p = natDegree q := by
  by_contra h
  cases Nat.lt_or_lt_of_ne h with
  | inl h => exact lt_asymm h (by rwa [natDegree_add_eq_right_of_natDegree_lt h] at H)
  | inr h =>
    rw [natDegree_add_eq_left_of_natDegree_lt h] at H
    exact LT.lt.false H

/--
lemma `natDegree_eq_of_natDegree_add_lt_right` / 引理 `natDegree_eq_of_natDegree_add_lt_right`

English:
lemma natDegree_eq_of_natDegree_add_lt_right
  statement: (p q : R[X])
  proof: (natDegree_eq_of_natDegree_add_lt_left q p (add_comm p q ▸ H)).symm

中文:
引理 natDegree_eq_of_natDegree_add_lt_right
  结论: (p q : R[X])
  证明: (natDegree_eq_of_natDegree_add_lt_left q p (add_comm p q ▸ H)).symm

Depends on / 依赖: add_comm, natDegree_eq_of_natDegree_add_lt_left
-/
lemma natDegree_eq_of_natDegree_add_lt_right (p q : R[X])
    (H : natDegree (p + q) < natDegree q) : natDegree p = natDegree q :=
  (natDegree_eq_of_natDegree_add_lt_left q p (add_comm p q ▸ H)).symm

/--
lemma `natDegree_eq_of_natDegree_add_eq_zero` / 引理 `natDegree_eq_of_natDegree_add_eq_zero`

English:
lemma natDegree_eq_of_natDegree_add_eq_zero
  statement: (p q : R[X])
  proof: by
  by_cases h₁ : natDegree p = 0; on_goal 1 => by_cases h₂ : natDegree q = 0
  · exact h₁.trans h₂.symm
  · apply natDegree_eq_of_natDegree_add_lt_right; rwa [H, Nat.pos_iff_ne_zero]
  · apply natDegree_eq_of_natDegree_add_lt_left; rwa [H, Nat.pos_iff_ne_zero]

中文:
引理 natDegree_eq_of_natDegree_add_eq_zero
  结论: (p q : R[X])
  证明: by
  by_cases h₁ : natDegree p = 0; on_goal 1 => by_cases h₂ : natDegree q = 0
  · exact h₁.trans h₂.symm
  · apply natDegree_eq_of_natDegree_add_lt_right; rwa [H, Nat.pos_iff_ne_zero]
  · apply natDegree_eq_of_natDegree_add_lt_left; rwa [H, Nat.pos_iff_ne_zero]

Depends on / 依赖: Nat.pos_iff_ne_zero, natDegree, natDegree_eq_of_natDegree_add_lt_left, natDegree_eq_of_natDegree_add_lt_right, on_goal, pos_iff_ne_zero
-/
lemma natDegree_eq_of_natDegree_add_eq_zero (p q : R[X])
    (H : natDegree (p + q) = 0) : natDegree p = natDegree q := by
  by_cases h₁ : natDegree p = 0; on_goal 1 => by_cases h₂ : natDegree q = 0
  · exact h₁.trans h₂.symm
  · apply natDegree_eq_of_natDegree_add_lt_right; rwa [H, Nat.pos_iff_ne_zero]
  · apply natDegree_eq_of_natDegree_add_lt_left; rwa [H, Nat.pos_iff_ne_zero]

/--
theorem `monic_of_natDegree_le_of_coeff_eq_one` / 定理 `monic_of_natDegree_le_of_coeff_eq_one`

English:
theorem monic_of_natDegree_le_of_coeff_eq_one
  given: (n : Nat) (pn : p.natDegree <= n) (p1 : p.coeff n = 1)
  proof: by
  unfold Monic
  nontriviality
  refine (congr_arg _ <| natDegree_eq_of_le_of_coeff_ne_zero pn ?_).trans p1
  exact ne_of_eq_of_ne p1 one_ne_zero

中文:
定理 monic_of_natDegree_le_of_coeff_eq_one
  条件: (n : 自然数) (pn : p.natDegree <= n) (p1 : p.coeff n = 1)
  证明: by
  unfold Monic
  nontriviality
  refine (congr_arg _ <| natDegree_eq_of_le_of_coeff_ne_zero pn ?_).trans p1
  exact ne_of_eq_of_ne p1 one_ne_zero

Depends on / 依赖: congr_arg, natDegree_eq_of_le_of_coeff_ne_zero, ne_of_eq_of_ne, nontriviality, one_ne_zero
-/
theorem monic_of_natDegree_le_of_coeff_eq_one (n : Nat) (pn : p.natDegree <= n) (p1 : p.coeff n = 1) :
    Monic p := by
  unfold Monic
  nontriviality
  refine (congr_arg _ <| natDegree_eq_of_le_of_coeff_ne_zero pn ?_).trans p1
  exact ne_of_eq_of_ne p1 one_ne_zero

/--
theorem `monic_of_degree_le` / 定理 `monic_of_degree_le`

English:
theorem monic_of_degree_le
  given: (n : Nat) (pn : p.degree <= n) (p1 : p.coeff n = 1)
  statement: Monic p
  proof: monic_of_natDegree_le_of_coeff_eq_one n (natDegree_le_of_degree_le pn) p1

中文:
定理 monic_of_degree_le
  条件: (n : 自然数) (pn : p.degree <= n) (p1 : p.coeff n = 1)
  结论: Monic p
  证明: monic_of_natDegree_le_of_coeff_eq_one n (natDegree_le_of_degree_le pn) p1

Depends on / 依赖: monic_of_natDegree_le_of_coeff_eq_one, natDegree_le_of_degree_le
-/
theorem monic_of_degree_le (n : Nat) (pn : p.degree <= n) (p1 : p.coeff n = 1) : Monic p :=
  monic_of_natDegree_le_of_coeff_eq_one n (natDegree_le_of_degree_le pn) p1

/--
theorem `leadingCoeff_add_of_degree_lt` / 定理 `leadingCoeff_add_of_degree_lt`

English:
theorem leadingCoeff_add_of_degree_lt
  given: (h : degree p < degree q)
  proof: by
  have : coeff p (natDegree q) = 0 := coeff_natDegree_eq_zero_of_degree_lt h
  simp only [leadingCoeff, natDegree_eq_of_degree_eq (degree_add_eq_right_of_degree_lt h), this,
    coeff_add, zero_add]

中文:
定理 leadingCoeff_add_of_degree_lt
  条件: (h : degree p < degree q)
  证明: by
  have : coeff p (natDegree q) = 0 := coeff_natDegree_eq_zero_of_degree_lt h
  simp only [leadingCoeff, natDegree_eq_of_degree_eq (degree_add_eq_right_of_degree_lt h), this,
    coeff_add, zero_add]

Depends on / 依赖: coeff_add, coeff_natDegree_eq_zero_of_degree_lt, degree_add_eq_right_of_degree_lt, leadingCoeff, natDegree, natDegree_eq_of_degree_eq, zero_add
-/
theorem leadingCoeff_add_of_degree_lt (h : degree p < degree q) :
    leadingCoeff (p + q) = leadingCoeff q := by
  have : coeff p (natDegree q) = 0 := coeff_natDegree_eq_zero_of_degree_lt h
  simp only [leadingCoeff, natDegree_eq_of_degree_eq (degree_add_eq_right_of_degree_lt h), this,
    coeff_add, zero_add]

/--
theorem `leadingCoeff_add_of_degree_lt'` / 定理 `leadingCoeff_add_of_degree_lt'`

English:
theorem leadingCoeff_add_of_degree_lt'
  given: (h : degree q < degree p)
  proof: by
  rw [add_comm]
  exact leadingCoeff_add_of_degree_lt h

中文:
定理 leadingCoeff_add_of_degree_lt'
  条件: (h : degree q < degree p)
  证明: by
  rw [add_comm]
  exact leadingCoeff_add_of_degree_lt h

Depends on / 依赖: add_comm, leadingCoeff_add_of_degree_lt
-/
theorem leadingCoeff_add_of_degree_lt' (h : degree q < degree p) :
    leadingCoeff (p + q) = leadingCoeff p := by
  rw [add_comm]
  exact leadingCoeff_add_of_degree_lt h

/--
theorem `leadingCoeff_add_of_degree_eq` / 定理 `leadingCoeff_add_of_degree_eq`

English:
theorem leadingCoeff_add_of_degree_eq
  statement: (h : degree p = degree q)
  proof: by
  have : natDegree (p + q) = natDegree p := by
    apply natDegree_eq_of_degree_eq
    rw [degree_add_eq_of_leadingCoeff_add_ne_zero hlc]; rw [h]; rw [max_self]
  simp only [leadingCoeff, this, natDegree_eq_of_degree_eq h, coeff_add]

@[simp]

中文:
定理 leadingCoeff_add_of_degree_eq
  结论: (h : degree p = degree q)
  证明: by
  have : natDegree (p + q) = natDegree p := by
    apply natDegree_eq_of_degree_eq
    rw [degree_add_eq_of_leadingCoeff_add_ne_zero hlc]; rw [h]; rw [max_self]
  simp only [leadingCoeff, this, natDegree_eq_of_degree_eq h, coeff_add]

@[simp]

Depends on / 依赖: coeff_add, degree_add_eq_of_leadingCoeff_add_ne_zero, leadingCoeff, max_self, natDegree, natDegree_eq_of_degree_eq
-/
theorem leadingCoeff_add_of_degree_eq (h : degree p = degree q)
    (hlc : leadingCoeff p + leadingCoeff q != 0) :
    leadingCoeff (p + q) = leadingCoeff p + leadingCoeff q := by
  have : natDegree (p + q) = natDegree p := by
    apply natDegree_eq_of_degree_eq
    rw [degree_add_eq_of_leadingCoeff_add_ne_zero hlc]; rw [h]; rw [max_self]
  simp only [leadingCoeff, this, natDegree_eq_of_degree_eq h, coeff_add]

@[simp]
/--
theorem `coeff_mul_degree_add_degree` / 定理 `coeff_mul_degree_add_degree`

English:
theorem coeff_mul_degree_add_degree
  given: (p q : R[X])
  proof: calc
    coeff (p * q) (natDegree p + natDegree q) =
        ∑ x in antidiagonal (natDegree p + natDegree q), coeff p x.1 * coeff q x.2 :=
      coeff_mul _ _ _
    _ = coeff p (natDegree p) * coeff q (natDegree q) := by
      refine Finset.sum_eq_single (natDegree p, natDegree q) ?_ ?_
      · rint

中文:
定理 coeff_mul_degree_add_degree
  条件: (p q : R[X])
  证明: calc
    coeff (p * q) (natDegree p + natDegree q) =
        ∑ x in antidiagonal (natDegree p + natDegree q), coeff p x.1 * coeff q x.2 :=
      coeff_mul _ _ _
    _ = coeff p (natDegree p) * coeff q (natDegree q) := by
      refine Finset.sum_eq_single (natDegree p, natDegree q) ?_ ?_
      · rint

Depends on / 依赖: Finset, Finset.sum_eq_single, WithBot, WithBot.coe_lt_coe, antidiagonal, coe_lt_coe, coeff_eq_zero_of_degree_lt, coeff_mul, degree_le_natDegree, lt_of_le_of_lt, mem_antidiagonal, natDegree, not_lt_iff_eq_or_lt, sum_eq_single, zero_mul
-/
theorem coeff_mul_degree_add_degree (p q : R[X]) :
    coeff (p * q) (natDegree p + natDegree q) = leadingCoeff p * leadingCoeff q :=
  calc
    coeff (p * q) (natDegree p + natDegree q) =
        ∑ x in antidiagonal (natDegree p + natDegree q), coeff p x.1 * coeff q x.2 :=
      coeff_mul _ _ _
    _ = coeff p (natDegree p) * coeff q (natDegree q) := by
      refine Finset.sum_eq_single (natDegree p, natDegree q) ?_ ?_
      · rintro ⟨i, j⟩ h₁ h₂
        rw [mem_antidiagonal] at h₁
        by_cases H : natDegree p < i
        · rw [coeff_eq_zero_of_degree_lt
              (lt_of_le_of_lt degree_le_natDegree (WithBot.coe_lt_coe.2 H)),
            zero_mul]
        · rw [not_lt_iff_eq_or_lt] at H
          rcases H with H | H
          · simp_all
          · suffices natDegree q < j by
              rw [coeff_eq_zero_of_degree_lt
                  (lt_of_le_of_lt degree_le_natDegree (WithBot.coe_lt_coe.2 this))]; rw [mul_zero]
            by_contra! H'
            exact
              ne_of_lt (Nat.lt_of_lt_of_le (Nat.add_lt_add_right H j) (Nat.add_le_add_left H' _))
                h₁
      · intro H
        exfalso
        apply H
        rw [mem_antidiagonal]

/--
theorem `degree_mul'` / 定理 `degree_mul'`

English:
theorem degree_mul'
  given: (h : leadingCoeff p * leadingCoeff q != 0)
  proof: have hp : p != 0 := by refine mt ?_ h; exact fun hp => by rw [hp, leadingCoeff_zero, zero_mul]
  have hq : q != 0 := by refine mt ?_ h; exact fun hq => by rw [hq, leadingCoeff_zero, mul_zero]
  le_antisymm (degree_mul_le _ _)
    (by
      rw [degree_eq_natDegree hp]; rw [degree_eq_natDegree hq]
   

中文:
定理 degree_mul'
  条件: (h : leadingCoeff p * leadingCoeff q != 0)
  证明: have hp : p != 0 := by refine mt ?_ h; exact fun hp => by rw [hp, leadingCoeff_zero, zero_mul]
  have hq : q != 0 := by refine mt ?_ h; exact fun hq => by rw [hq, leadingCoeff_zero, mul_zero]
  le_antisymm (degree_mul_le _ _)
    (by
      rw [degree_eq_natDegree hp]; rw [degree_eq_natDegree hq]
   

Depends on / 依赖: coeff_mul_degree_add_degree, degree_eq_natDegree, degree_mul_le, le_antisymm, le_degree_of_ne_zero, leadingCoeff_zero, mul_zero, natDegree, zero_mul
-/
theorem degree_mul' (h : leadingCoeff p * leadingCoeff q != 0) :
    degree (p * q) = degree p + degree q :=
  have hp : p != 0 := by refine mt ?_ h; exact fun hp => by rw [hp, leadingCoeff_zero, zero_mul]
  have hq : q != 0 := by refine mt ?_ h; exact fun hq => by rw [hq, leadingCoeff_zero, mul_zero]
  le_antisymm (degree_mul_le _ _)
    (by
      rw [degree_eq_natDegree hp]; rw [degree_eq_natDegree hq]
      refine le_degree_of_ne_zero (n := natDegree p + natDegree q) ?_
      rwa [coeff_mul_degree_add_degree])

/--
theorem `Monic.degree_mul` / 定理 `Monic.degree_mul`

English:
theorem Monic.degree_mul
  given: (hq : Monic q)
  statement: degree (p * q) = degree p + degree q
  proof: letI := Classical.decEq R
  if hp : p = 0 then by simp [hp]
else degree_mul' by rwa [hq.leadingCoeff, mul_one, Ne, leadingCoeff_eq_zero]

中文:
定理 Monic.degree_mul
  条件: (hq : Monic q)
  结论: degree (p * q) = degree p + degree q
  证明: letI := Classical.decEq R
  if hp : p = 0 then by simp [hp]
else degree_mul' by rwa [hq.leadingCoeff, mul_one, Ne, leadingCoeff_eq_zero]

Depends on / 依赖: Classical, Classical.decEq, degree_mul, hq.leadingCoeff, leadingCoeff, leadingCoeff_eq_zero, mul_one
-/
theorem Monic.degree_mul (hq : Monic q) : degree (p * q) = degree p + degree q :=
  letI := Classical.decEq R
  if hp : p = 0 then by simp [hp]
else degree_mul' by rwa [hq.leadingCoeff, mul_one, Ne, leadingCoeff_eq_zero]

/--
theorem `natDegree_mul'` / 定理 `natDegree_mul'`

English:
theorem natDegree_mul'
  given: (h : leadingCoeff p * leadingCoeff q != 0)
  proof: have hp : p != 0 := mt leadingCoeff_eq_zero.2 fun h₁ => h by rw [h₁, zero_mul]
have hq : q != 0 := mt leadingCoeff_eq_zero.2 fun h₁ => h by rw [h₁, mul_zero]
natDegree_eq_of_degree_eq_some by
    rw [degree_mul' h]; rw [Nat.cast_add]; rw [degree_eq_natDegree hp]; rw [degree_eq_natDegree hq]

中文:
定理 natDegree_mul'
  条件: (h : leadingCoeff p * leadingCoeff q != 0)
  证明: have hp : p != 0 := mt leadingCoeff_eq_zero.2 fun h₁ => h by rw [h₁, zero_mul]
have hq : q != 0 := mt leadingCoeff_eq_zero.2 fun h₁ => h by rw [h₁, mul_zero]
natDegree_eq_of_degree_eq_some by
    rw [degree_mul' h]; rw [Nat.cast_add]; rw [degree_eq_natDegree hp]; rw [degree_eq_natDegree hq]

Depends on / 依赖: Nat.cast_add, cast_add, degree_eq_natDegree, degree_mul, leadingCoeff_eq_zero, mul_zero, natDegree_eq_of_degree_eq_some, zero_mul
-/
theorem natDegree_mul' (h : leadingCoeff p * leadingCoeff q != 0) :
    natDegree (p * q) = natDegree p + natDegree q :=
have hp : p != 0 := mt leadingCoeff_eq_zero.2 fun h₁ => h by rw [h₁, zero_mul]
have hq : q != 0 := mt leadingCoeff_eq_zero.2 fun h₁ => h by rw [h₁, mul_zero]
natDegree_eq_of_degree_eq_some by
    rw [degree_mul' h]; rw [Nat.cast_add]; rw [degree_eq_natDegree hp]; rw [degree_eq_natDegree hq]

/--
theorem `leadingCoeff_mul'` / 定理 `leadingCoeff_mul'`

English:
theorem leadingCoeff_mul'
  given: (h : leadingCoeff p * leadingCoeff q != 0)
  proof: by
  simp [← coeff_natDegree, natDegree_mul' h, coeff_mul_degree_add_degree]

中文:
定理 leadingCoeff_mul'
  条件: (h : leadingCoeff p * leadingCoeff q != 0)
  证明: by
  simp [← coeff_natDegree, natDegree_mul' h, coeff_mul_degree_add_degree]

Depends on / 依赖: coeff_mul_degree_add_degree, coeff_natDegree, natDegree_mul
-/
theorem leadingCoeff_mul' (h : leadingCoeff p * leadingCoeff q != 0) :
    leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q := by
  simp [← coeff_natDegree, natDegree_mul' h, coeff_mul_degree_add_degree]

/--
lemma `Monic.leadingCoeff_C_mul` / 引理 `Monic.leadingCoeff_C_mul`

English:
lemma Monic.leadingCoeff_C_mul
  given: (hp : p.Monic) (r : R)
  statement: (C r * p).leadingCoeff = r
  proof: by
  by_cases hr : r = 0 <;> simp_all [leadingCoeff_mul']

中文:
引理 Monic.leadingCoeff_C_mul
  条件: (hp : p.Monic) (r : R)
  结论: (C r * p).leadingCoeff = r
  证明: by
  by_cases hr : r = 0 <;> simp_all [leadingCoeff_mul']

Depends on / 依赖: leadingCoeff_mul
-/
lemma Monic.leadingCoeff_C_mul (hp : p.Monic) (r : R) : (C r * p).leadingCoeff = r := by
  by_cases hr : r = 0 <;> simp_all [leadingCoeff_mul']

/--
theorem `leadingCoeff_pow'` / 定理 `leadingCoeff_pow'`

English:
theorem leadingCoeff_pow'
  statement: leadingCoeff p ^ n != 0 -> leadingCoeff (p ^ n) = leadingCoeff p ^ n
  proof: Nat.recOn n (by simp) fun n ih h => by
have h₁ : leadingCoeff p ^ n != 0 := fun h₁ => h by rw [pow_succ, h₁, zero_mul]
    have h₂ : leadingCoeff p * leadingCoeff (p ^ n) != 0 := by rwa [pow_succ', ← ih h₁] at h
    rw [pow_succ']; rw [pow_succ']; rw [leadingCoeff_mul' h₂]; rw [ih h₁]

中文:
定理 leadingCoeff_pow'
  结论: leadingCoeff p ^ n != 0 -> leadingCoeff (p ^ n) = leadingCoeff p ^ n
  证明: Nat.recOn n (by simp) fun n ih h => by
have h₁ : leadingCoeff p ^ n != 0 := fun h₁ => h by rw [pow_succ, h₁, zero_mul]
    have h₂ : leadingCoeff p * leadingCoeff (p ^ n) != 0 := by rwa [pow_succ', ← ih h₁] at h
    rw [pow_succ']; rw [pow_succ']; rw [leadingCoeff_mul' h₂]; rw [ih h₁]

Depends on / 依赖: Nat.recOn, leadingCoeff, leadingCoeff_mul, pow_succ, zero_mul
-/
theorem leadingCoeff_pow' : leadingCoeff p ^ n != 0 -> leadingCoeff (p ^ n) = leadingCoeff p ^ n :=
  Nat.recOn n (by simp) fun n ih h => by
have h₁ : leadingCoeff p ^ n != 0 := fun h₁ => h by rw [pow_succ, h₁, zero_mul]
    have h₂ : leadingCoeff p * leadingCoeff (p ^ n) != 0 := by rwa [pow_succ', ← ih h₁] at h
    rw [pow_succ']; rw [pow_succ']; rw [leadingCoeff_mul' h₂]; rw [ih h₁]

/--
theorem `degree_pow'` / 定理 `degree_pow'`

English:
theorem degree_pow'
  statement: forall {n : Nat}, leadingCoeff p ^ n != 0 -> degree (p ^ n) = n • degree p
  proof: fun h₁ => h by rw [pow_succ, h₁, zero_mul]
    have h₂ : leadingCoeff (p ^ n) * leadingCoeff p != 0 := by
      rwa [pow_succ, ← leadingCoeff_pow' h₁] at h
    rw [pow_succ]; rw [degree_mul' h₂]; rw [succ_nsmul]; rw [degree_pow' h₁]

中文:
定理 degree_pow'
  结论: 对任意 {n : 自然数}, leadingCoeff p ^ n != 0 -> degree (p ^ n) = n • degree p
  证明: fun h₁ => h by rw [pow_succ, h₁, zero_mul]
    have h₂ : leadingCoeff (p ^ n) * leadingCoeff p != 0 := by
      rwa [pow_succ, ← leadingCoeff_pow' h₁] at h
    rw [pow_succ]; rw [degree_mul' h₂]; rw [succ_nsmul]; rw [degree_pow' h₁]

Depends on / 依赖: pow_succ, zero_mul
-/
theorem degree_pow' : forall {n : Nat}, leadingCoeff p ^ n != 0 -> degree (p ^ n) = n • degree p
  | 0 => fun h => by rw [pow_zero, ← C_1] at *; rw [degree_C h, zero_nsmul]
  | n + 1 => fun h => by
have h₁ : leadingCoeff p ^ n != 0 := fun h₁ => h by rw [pow_succ, h₁, zero_mul]
    have h₂ : leadingCoeff (p ^ n) * leadingCoeff p != 0 := by
      rwa [pow_succ, ← leadingCoeff_pow' h₁] at h
    rw [pow_succ]; rw [degree_mul' h₂]; rw [succ_nsmul]; rw [degree_pow' h₁]

/--
theorem `natDegree_pow'` / 定理 `natDegree_pow'`

English:
theorem natDegree_pow'
  given: {n : Nat} (h : leadingCoeff p ^ n != 0)
  statement: natDegree (p ^ n) = n * natDegree p
  proof: letI := Classical.decEq R
  if hp0 : p = 0 then
    if hn0 : n = 0 then by simp [*] else by rw [hp0, zero_pow hn0]; simp
  else
    have hpn : p ^ n != 0 := fun hpn0 => by
      have h1 := h
      rw [← leadingCoeff_pow' h1]; rw [hpn0]; rw [leadingCoeff_zero] at h; exact h rfl
Option.some_inj.1
    

中文:
定理 natDegree_pow'
  条件: {n : 自然数} (h : leadingCoeff p ^ n != 0)
  结论: natDegree (p ^ n) = n * natDegree p
  证明: letI := Classical.decEq R
  if hp0 : p = 0 then
    if hn0 : n = 0 then by simp [*] else by rw [hp0, zero_pow hn0]; simp
  else
    have hpn : p ^ n != 0 := fun hpn0 => by
      have h1 := h
      rw [← leadingCoeff_pow' h1]; rw [hpn0]; rw [leadingCoeff_zero] at h; exact h rfl
Option.some_inj.1
    

Depends on / 依赖: Classical, Classical.decEq, Option.some_inj, WithBot, degree_eq_natDegree, degree_pow, leadingCoeff_pow, leadingCoeff_zero, natDegree, some_inj, zero_pow
-/
theorem natDegree_pow' {n : Nat} (h : leadingCoeff p ^ n != 0) : natDegree (p ^ n) = n * natDegree p :=
  letI := Classical.decEq R
  if hp0 : p = 0 then
    if hn0 : n = 0 then by simp [*] else by rw [hp0, zero_pow hn0]; simp
  else
    have hpn : p ^ n != 0 := fun hpn0 => by
      have h1 := h
      rw [← leadingCoeff_pow' h1]; rw [hpn0]; rw [leadingCoeff_zero] at h; exact h rfl
Option.some_inj.1
      show (natDegree (p ^ n) : WithBot Nat) = (n * natDegree p : Nat) by
        rw [← degree_eq_natDegree hpn]; rw [degree_pow' h]; rw [degree_eq_natDegree hp0]; simp

/--
theorem `leadingCoeff_monic_mul` / 定理 `leadingCoeff_monic_mul`

English:
theorem leadingCoeff_monic_mul
  given: {p q : R[X]} (hp : Monic p)
  proof: by
  rcases eq_or_ne q 0 with (rfl | H)
  · simp
  · rw [leadingCoeff_mul', hp.leadingCoeff, one_mul]
    rwa [hp.leadingCoeff, one_mul, Ne, leadingCoeff_eq_zero]

中文:
定理 leadingCoeff_monic_mul
  条件: {p q : R[X]} (hp : Monic p)
  证明: by
  rcases eq_or_ne q 0 with (rfl | H)
  · simp
  · rw [leadingCoeff_mul', hp.leadingCoeff, one_mul]
    rwa [hp.leadingCoeff, one_mul, Ne, leadingCoeff_eq_zero]

Depends on / 依赖: eq_or_ne, hp.leadingCoeff, leadingCoeff, leadingCoeff_eq_zero, leadingCoeff_mul, one_mul
-/
theorem leadingCoeff_monic_mul {p q : R[X]} (hp : Monic p) :
    leadingCoeff (p * q) = leadingCoeff q := by
  rcases eq_or_ne q 0 with (rfl | H)
  · simp
  · rw [leadingCoeff_mul', hp.leadingCoeff, one_mul]
    rwa [hp.leadingCoeff, one_mul, Ne, leadingCoeff_eq_zero]

/--
theorem `leadingCoeff_mul_monic` / 定理 `leadingCoeff_mul_monic`

English:
theorem leadingCoeff_mul_monic
  given: {p q : R[X]} (hq : Monic q)
  proof: letI := Classical.decEq R
  Decidable.byCases
    (fun H : leadingCoeff p = 0 => by
      rw [H]; rw [leadingCoeff_eq_zero.1 H]; rw [zero_mul]; rw [leadingCoeff_zero])
    fun H : leadingCoeff p != 0 => by
      rw [leadingCoeff_mul']; rw [hq.leadingCoeff]; rw [mul_one]
      rwa [hq.leadingCoeff, m

中文:
定理 leadingCoeff_mul_monic
  条件: {p q : R[X]} (hq : Monic q)
  证明: letI := Classical.decEq R
  Decidable.byCases
    (fun H : leadingCoeff p = 0 => by
      rw [H]; rw [leadingCoeff_eq_zero.1 H]; rw [zero_mul]; rw [leadingCoeff_zero])
    fun H : leadingCoeff p != 0 => by
      rw [leadingCoeff_mul']; rw [hq.leadingCoeff]; rw [mul_one]
      rwa [hq.leadingCoeff, m

Depends on / 依赖: Classical, Classical.decEq, Decidable, Decidable.byCases, byCases, hq.leadingCoeff, leadingCoeff, leadingCoeff_eq_zero, leadingCoeff_mul, leadingCoeff_zero, mul_one, zero_mul
-/
theorem leadingCoeff_mul_monic {p q : R[X]} (hq : Monic q) :
    leadingCoeff (p * q) = leadingCoeff p :=
  letI := Classical.decEq R
  Decidable.byCases
    (fun H : leadingCoeff p = 0 => by
      rw [H]; rw [leadingCoeff_eq_zero.1 H]; rw [zero_mul]; rw [leadingCoeff_zero])
    fun H : leadingCoeff p != 0 => by
      rw [leadingCoeff_mul']; rw [hq.leadingCoeff]; rw [mul_one]
      rwa [hq.leadingCoeff, mul_one]

/--
lemma `degree_C_mul_of_isUnit` / 引理 `degree_C_mul_of_isUnit`

English:
lemma degree_C_mul_of_isUnit
  given: (ha : IsUnit a) (p : R[X])
  statement: (C a * p).degree = p.degree
  proof: by
  obtain rfl | hp := eq_or_ne p 0
  · simp
  nontriviality R
  rw [degree_mul']; rw [degree_C ha.ne_zero]
  · simp
  · simpa [ha.mul_right_eq_zero]

中文:
引理 degree_C_mul_of_isUnit
  条件: (ha : IsUnit a) (p : R[X])
  结论: (C a * p).degree = p.degree
  证明: by
  obtain rfl | hp := eq_or_ne p 0
  · simp
  nontriviality R
  rw [degree_mul']; rw [degree_C ha.ne_zero]
  · simp
  · simpa [ha.mul_right_eq_zero]

Depends on / 依赖: degree_C, degree_mul, eq_or_ne, ha.mul_right_eq_zero, ha.ne_zero, mul_right_eq_zero, ne_zero, nontriviality
-/
lemma degree_C_mul_of_isUnit (ha : IsUnit a) (p : R[X]) : (C a * p).degree = p.degree := by
  obtain rfl | hp := eq_or_ne p 0
  · simp
  nontriviality R
  rw [degree_mul']; rw [degree_C ha.ne_zero]
  · simp
  · simpa [ha.mul_right_eq_zero]

/--
lemma `degree_mul_C_of_isUnit` / 引理 `degree_mul_C_of_isUnit`

English:
lemma degree_mul_C_of_isUnit
  given: (ha : IsUnit a) (p : R[X])
  statement: (p * C a).degree = p.degree
  proof: by
  obtain rfl | hp := eq_or_ne p 0
  · simp
  nontriviality R
  rw [degree_mul']; rw [degree_C ha.ne_zero]
  · simp
  · simpa [ha.mul_left_eq_zero]

中文:
引理 degree_mul_C_of_isUnit
  条件: (ha : IsUnit a) (p : R[X])
  结论: (p * C a).degree = p.degree
  证明: by
  obtain rfl | hp := eq_or_ne p 0
  · simp
  nontriviality R
  rw [degree_mul']; rw [degree_C ha.ne_zero]
  · simp
  · simpa [ha.mul_left_eq_zero]

Depends on / 依赖: degree_C, degree_mul, eq_or_ne, ha.mul_left_eq_zero, ha.ne_zero, mul_left_eq_zero, ne_zero, nontriviality
-/
lemma degree_mul_C_of_isUnit (ha : IsUnit a) (p : R[X]) : (p * C a).degree = p.degree := by
  obtain rfl | hp := eq_or_ne p 0
  · simp
  nontriviality R
  rw [degree_mul']; rw [degree_C ha.ne_zero]
  · simp
  · simpa [ha.mul_left_eq_zero]

/--
lemma `natDegree_C_mul_of_isUnit` / 引理 `natDegree_C_mul_of_isUnit`

English:
lemma natDegree_C_mul_of_isUnit
  given: (ha : IsUnit a) (p : R[X])
  statement: (C a * p).natDegree = p.natDegree
  proof: by
  simp [natDegree, degree_C_mul_of_isUnit ha]

中文:
引理 natDegree_C_mul_of_isUnit
  条件: (ha : IsUnit a) (p : R[X])
  结论: (C a * p).natDegree = p.natDegree
  证明: by
  simp [natDegree, degree_C_mul_of_isUnit ha]

Depends on / 依赖: degree_C_mul_of_isUnit, natDegree
-/
lemma natDegree_C_mul_of_isUnit (ha : IsUnit a) (p : R[X]) : (C a * p).natDegree = p.natDegree := by
  simp [natDegree, degree_C_mul_of_isUnit ha]

/--
lemma `natDegree_mul_C_of_isUnit` / 引理 `natDegree_mul_C_of_isUnit`

English:
lemma natDegree_mul_C_of_isUnit
  given: (ha : IsUnit a) (p : R[X])
  statement: (p * C a).natDegree = p.natDegree
  proof: by
  simp [natDegree, degree_mul_C_of_isUnit ha]

中文:
引理 natDegree_mul_C_of_isUnit
  条件: (ha : IsUnit a) (p : R[X])
  结论: (p * C a).natDegree = p.natDegree
  证明: by
  simp [natDegree, degree_mul_C_of_isUnit ha]

Depends on / 依赖: degree_mul_C_of_isUnit, natDegree
-/
lemma natDegree_mul_C_of_isUnit (ha : IsUnit a) (p : R[X]) : (p * C a).natDegree = p.natDegree := by
  simp [natDegree, degree_mul_C_of_isUnit ha]

/--
lemma `leadingCoeff_C_mul_of_isUnit` / 引理 `leadingCoeff_C_mul_of_isUnit`

English:
lemma leadingCoeff_C_mul_of_isUnit
  given: (ha : IsUnit a) (p : R[X])
  proof: by
  rwa [leadingCoeff, coeff_C_mul, natDegree_C_mul_of_isUnit, leadingCoeff]

中文:
引理 leadingCoeff_C_mul_of_isUnit
  条件: (ha : IsUnit a) (p : R[X])
  证明: by
  rwa [leadingCoeff, coeff_C_mul, natDegree_C_mul_of_isUnit, leadingCoeff]

Depends on / 依赖: coeff_C_mul, leadingCoeff, natDegree_C_mul_of_isUnit
-/
lemma leadingCoeff_C_mul_of_isUnit (ha : IsUnit a) (p : R[X]) :
    (C a * p).leadingCoeff = a * p.leadingCoeff := by
  rwa [leadingCoeff, coeff_C_mul, natDegree_C_mul_of_isUnit, leadingCoeff]

/--
lemma `leadingCoeff_mul_C_of_isUnit` / 引理 `leadingCoeff_mul_C_of_isUnit`

English:
lemma leadingCoeff_mul_C_of_isUnit
  given: (ha : IsUnit a) (p : R[X])
  proof: by
  rwa [leadingCoeff, coeff_mul_C, natDegree_mul_C_of_isUnit, leadingCoeff]

@[simp]

中文:
引理 leadingCoeff_mul_C_of_isUnit
  条件: (ha : IsUnit a) (p : R[X])
  证明: by
  rwa [leadingCoeff, coeff_mul_C, natDegree_mul_C_of_isUnit, leadingCoeff]

@[simp]

Depends on / 依赖: coeff_mul_C, leadingCoeff, natDegree_mul_C_of_isUnit
-/
lemma leadingCoeff_mul_C_of_isUnit (ha : IsUnit a) (p : R[X]) :
    (p * C a).leadingCoeff = p.leadingCoeff * a := by
  rwa [leadingCoeff, coeff_mul_C, natDegree_mul_C_of_isUnit, leadingCoeff]

@[simp]
/--
theorem `leadingCoeff_mul_X_pow` / 定理 `leadingCoeff_mul_X_pow`

English:
theorem leadingCoeff_mul_X_pow
  given: {p : R[X]} {n : Nat}
  statement: leadingCoeff (p * X ^ n) = leadingCoeff p
  proof: leadingCoeff_mul_monic (monic_X_pow n)

@[simp]

中文:
定理 leadingCoeff_mul_X_pow
  条件: {p : R[X]} {n : 自然数}
  结论: leadingCoeff (p * X ^ n) = leadingCoeff p
  证明: leadingCoeff_mul_monic (monic_X_pow n)

@[simp]

Depends on / 依赖: leadingCoeff_mul_monic, monic_X_pow
-/
theorem leadingCoeff_mul_X_pow {p : R[X]} {n : Nat} : leadingCoeff (p * X ^ n) = leadingCoeff p :=
  leadingCoeff_mul_monic (monic_X_pow n)

@[simp]
/--
theorem `leadingCoeff_mul_X` / 定理 `leadingCoeff_mul_X`

English:
theorem leadingCoeff_mul_X
  given: {p : R[X]}
  statement: leadingCoeff (p * X) = leadingCoeff p
  proof: leadingCoeff_mul_monic monic_X

@[simp]

中文:
定理 leadingCoeff_mul_X
  条件: {p : R[X]}
  结论: leadingCoeff (p * X) = leadingCoeff p
  证明: leadingCoeff_mul_monic monic_X

@[simp]

Depends on / 依赖: leadingCoeff_mul_monic, monic_X
-/
theorem leadingCoeff_mul_X {p : R[X]} : leadingCoeff (p * X) = leadingCoeff p :=
  leadingCoeff_mul_monic monic_X

@[simp]
/--
theorem `coeff_pow_mul_natDegree` / 定理 `coeff_pow_mul_natDegree`

English:
theorem coeff_pow_mul_natDegree
  given: (p : R[X]) (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ i hi =>
    rw [pow_succ]; rw [pow_succ]; rw [Nat.succ_mul]
    by_cases hp1 : p.leadingCoeff ^ i = 0
    · rw [hp1, zero_mul]
      by_cases hp2 : p ^ i = 0
      · rw [hp2, zero_mul, coeff_zero]
      · apply coeff_eq_zero_of_natDegree_lt
        hav

中文:
定理 coeff_pow_mul_natDegree
  条件: (p : R[X]) (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ i hi =>
    rw [pow_succ]; rw [pow_succ]; rw [Nat.succ_mul]
    by_cases hp1 : p.leadingCoeff ^ i = 0
    · rw [hp1, zero_mul]
      by_cases hp2 : p ^ i = 0
      · rw [hp2, zero_mul, coeff_zero]
      · apply coeff_eq_zero_of_natDegree_lt
        hav

Depends on / 依赖: Nat.succ_mul, coeff_eq_zero_of_natDegree_lt, coeff_zero, leadingCoeff, leadingCoeff_eq_zero, leadingCoeff_eq_zero.mp, lt_of_le_of_ne, natDegree, natDegree_mul_le, natDegree_pow_le, p.leadingCoeff, p.natDegree, pow_succ, succ_mul, zero_mul
-/
theorem coeff_pow_mul_natDegree (p : R[X]) (n : Nat) :
    (p ^ n).coeff (n * p.natDegree) = p.leadingCoeff ^ n := by
  induction n with
  | zero => simp
  | succ i hi =>
    rw [pow_succ]; rw [pow_succ]; rw [Nat.succ_mul]
    by_cases hp1 : p.leadingCoeff ^ i = 0
    · rw [hp1, zero_mul]
      by_cases hp2 : p ^ i = 0
      · rw [hp2, zero_mul, coeff_zero]
      · apply coeff_eq_zero_of_natDegree_lt
        have h1 : (p ^ i).natDegree < i * p.natDegree := by
          refine lt_of_le_of_ne natDegree_pow_le fun h => hp2 ?_
          rw [← h]; rw [hp1] at hi
          exact leadingCoeff_eq_zero.mp hi
        calc
          (p ^ i * p).natDegree <= (p ^ i).natDegree + p.natDegree := natDegree_mul_le
          _ < i * p.natDegree + p.natDegree := by gcongr
    · rw [← natDegree_pow' hp1, ← leadingCoeff_pow' hp1]
      exact coeff_mul_degree_add_degree _ _

/--
theorem `coeff_mul_add_eq_of_natDegree_le` / 定理 `coeff_mul_add_eq_of_natDegree_le`

English:
theorem coeff_mul_add_eq_of_natDegree_le
  statement: {df dg : Nat} {f g : R[X]}
  proof: by
  rw [coeff_mul]; rw [Finset.sum_eq_single_of_mem (df]; rw [dg)]
  · rw [mem_antidiagonal]
  rintro ⟨df', dg'⟩ hmem hne
  obtain h | hdf' := lt_or_ge df df'
  · rw [coeff_eq_zero_of_natDegree_lt (hdf.trans_lt h), zero_mul]
  obtain h | hdg' := lt_or_ge dg dg'
  · rw [coeff_eq_zero_of_natDegree_lt

中文:
定理 coeff_mul_add_eq_of_natDegree_le
  结论: {df dg : 自然数} {f g : R[X]}
  证明: by
  rw [coeff_mul]; rw [Finset.sum_eq_single_of_mem (df]; rw [dg)]
  · rw [mem_antidiagonal]
  rintro ⟨df', dg'⟩ hmem hne
  obtain h | hdf' := lt_or_ge df df'
  · rw [coeff_eq_zero_of_natDegree_lt (hdf.trans_lt h), zero_mul]
  obtain h | hdg' := lt_or_ge dg dg'
  · rw [coeff_eq_zero_of_natDegree_lt

Depends on / 依赖: Finset, Finset.sum_eq_single_of_mem, add_eq_add_iff_eq_and_eq, coeff_eq_zero_of_natDegree_lt, coeff_mul, hdf.trans_lt, hdg.trans_lt, lt_or_ge, mem_antidiagonal, mul_zero, sum_eq_single_of_mem, trans_lt, zero_mul
-/
theorem coeff_mul_add_eq_of_natDegree_le {df dg : Nat} {f g : R[X]}
    (hdf : natDegree f <= df) (hdg : natDegree g <= dg) :
    (f * g).coeff (df + dg) = f.coeff df * g.coeff dg := by
  rw [coeff_mul]; rw [Finset.sum_eq_single_of_mem (df]; rw [dg)]
  · rw [mem_antidiagonal]
  rintro ⟨df', dg'⟩ hmem hne
  obtain h | hdf' := lt_or_ge df df'
  · rw [coeff_eq_zero_of_natDegree_lt (hdf.trans_lt h), zero_mul]
  obtain h | hdg' := lt_or_ge dg dg'
  · rw [coeff_eq_zero_of_natDegree_lt (hdg.trans_lt h), mul_zero]
  obtain ⟨rfl, rfl⟩ :=
    (add_eq_add_iff_eq_and_eq hdf' hdg').mp (mem_antidiagonal.1 hmem)
  exact (hne rfl).elim

/--
theorem `degree_smul_le` / 定理 `degree_smul_le`

English:
theorem degree_smul_le
  given: {S : Type*} [SMulZeroClass S R] (a : S) (p : R[X])
  proof: by
  refine (degree_le_iff_coeff_zero _ _).2 fun m hm => ?_
  rw [degree_lt_iff_coeff_zero] at hm
  simp [hm m le_rfl]

中文:
定理 degree_smul_le
  条件: {S : 类型} [SMulZeroClass S R] (a : S) (p : R[X])
  证明: by
  refine (degree_le_iff_coeff_zero _ _).2 fun m hm => ?_
  rw [degree_lt_iff_coeff_zero] at hm
  simp [hm m le_rfl]

Depends on / 依赖: degree_le_iff_coeff_zero, degree_lt_iff_coeff_zero, le_rfl
-/
theorem degree_smul_le {S : Type*} [SMulZeroClass S R] (a : S) (p : R[X]) :
    degree (a • p) <= degree p := by
  refine (degree_le_iff_coeff_zero _ _).2 fun m hm => ?_
  rw [degree_lt_iff_coeff_zero] at hm
  simp [hm m le_rfl]

/--
theorem `natDegree_smul_le` / 定理 `natDegree_smul_le`

English:
theorem natDegree_smul_le
  given: {S : Type*} [SMulZeroClass S R] (a : S) (p : R[X])
  proof: natDegree_le_natDegree (degree_smul_le a p)

中文:
定理 natDegree_smul_le
  条件: {S : 类型} [SMulZeroClass S R] (a : S) (p : R[X])
  证明: natDegree_le_natDegree (degree_smul_le a p)

Depends on / 依赖: degree_smul_le, natDegree_le_natDegree
-/
theorem natDegree_smul_le {S : Type*} [SMulZeroClass S R] (a : S) (p : R[X]) :
    natDegree (a • p) <= natDegree p :=
  natDegree_le_natDegree (degree_smul_le a p)

/--
theorem `degree_smul_of_isRightRegular_leadingCoeff` / 定理 `degree_smul_of_isRightRegular_leadingCoeff`

English:
theorem degree_smul_of_isRightRegular_leadingCoeff
  statement: (ha : a != 0)
  proof: by
refine le_antisymm (degree_smul_le a p) degree_le_degree ?_
  rw [coeff_smul]; rw [coeff_natDegree]; rw [smul_eq_mul]; rw [ne_eq]
  exact hp.mul_right_eq_zero_iff.ne.mpr ha

中文:
定理 degree_smul_of_isRightRegular_leadingCoeff
  结论: (ha : a != 0)
  证明: by
refine le_antisymm (degree_smul_le a p) degree_le_degree ?_
  rw [coeff_smul]; rw [coeff_natDegree]; rw [smul_eq_mul]; rw [ne_eq]
  exact hp.mul_right_eq_zero_iff.ne.mpr ha

Depends on / 依赖: coeff_natDegree, coeff_smul, degree_le_degree, degree_smul_le, hp.mul_right_eq_zero_iff.ne.mpr, le_antisymm, mul_right_eq_zero_iff, ne_eq, smul_eq_mul
-/
theorem degree_smul_of_isRightRegular_leadingCoeff (ha : a != 0)
    (hp : IsRightRegular p.leadingCoeff) : (a • p).degree = p.degree := by
refine le_antisymm (degree_smul_le a p) degree_le_degree ?_
  rw [coeff_smul]; rw [coeff_natDegree]; rw [smul_eq_mul]; rw [ne_eq]
  exact hp.mul_right_eq_zero_iff.ne.mpr ha

/--
theorem `degree_lt_degree_mul_X` / 定理 `degree_lt_degree_mul_X`

English:
theorem degree_lt_degree_mul_X
  given: (hp : p != 0)
  statement: p.degree < (p * X).degree
  proof: by
  have := Nontrivial.of_polynomial_ne hp
  have : leadingCoeff p * leadingCoeff X != 0 := by simpa
  rw [degree_mul' this]; rw [degree_eq_natDegree hp]; rw [degree_X]; rw [← Nat.cast_one]; rw [← Nat.cast_add]
  norm_cast
  exact Nat.lt_succ_self _

中文:
定理 degree_lt_degree_mul_X
  条件: (hp : p != 0)
  结论: p.degree < (p * X).degree
  证明: by
  have := Nontrivial.of_polynomial_ne hp
  have : leadingCoeff p * leadingCoeff X != 0 := by simpa
  rw [degree_mul' this]; rw [degree_eq_natDegree hp]; rw [degree_X]; rw [← Nat.cast_one]; rw [← Nat.cast_add]
  norm_cast
  exact Nat.lt_succ_self _

Depends on / 依赖: Nat.cast_add, Nat.cast_one, Nat.lt_succ_self, Nontrivial, Nontrivial.of_polynomial_ne, cast_add, cast_one, degree_X, degree_eq_natDegree, degree_mul, leadingCoeff, lt_succ_self, of_polynomial_ne
-/
theorem degree_lt_degree_mul_X (hp : p != 0) : p.degree < (p * X).degree := by
  have := Nontrivial.of_polynomial_ne hp
  have : leadingCoeff p * leadingCoeff X != 0 := by simpa
  rw [degree_mul' this]; rw [degree_eq_natDegree hp]; rw [degree_X]; rw [← Nat.cast_one]; rw [← Nat.cast_add]
  norm_cast
  exact Nat.lt_succ_self _

/--
theorem `eq_C_of_natDegree_le_zero` / 定理 `eq_C_of_natDegree_le_zero`

English:
theorem eq_C_of_natDegree_le_zero
  given: (h : natDegree p <= 0)
  statement: p = C (coeff p 0)
  proof: eq_C_of_degree_le_zero degree_le_of_natDegree_le h

中文:
定理 eq_C_of_natDegree_le_zero
  条件: (h : natDegree p <= 0)
  结论: p = C (coeff p 0)
  证明: eq_C_of_degree_le_zero degree_le_of_natDegree_le h

Depends on / 依赖: degree_le_of_natDegree_le, eq_C_of_degree_le_zero
-/
theorem eq_C_of_natDegree_le_zero (h : natDegree p <= 0) : p = C (coeff p 0) :=
eq_C_of_degree_le_zero degree_le_of_natDegree_le h

/--
theorem `eq_C_of_natDegree_eq_zero` / 定理 `eq_C_of_natDegree_eq_zero`

English:
theorem eq_C_of_natDegree_eq_zero
  given: (h : natDegree p = 0)
  statement: p = C (coeff p 0)
  proof: eq_C_of_natDegree_le_zero h.le

中文:
定理 eq_C_of_natDegree_eq_zero
  条件: (h : natDegree p = 0)
  结论: p = C (coeff p 0)
  证明: eq_C_of_natDegree_le_zero h.le

Depends on / 依赖: eq_C_of_natDegree_le_zero, h.le
-/
theorem eq_C_of_natDegree_eq_zero (h : natDegree p = 0) : p = C (coeff p 0) :=
  eq_C_of_natDegree_le_zero h.le

/--
lemma `natDegree_eq_zero` / 引理 `natDegree_eq_zero`

English:
lemma natDegree_eq_zero
  given: {p : R[X]}
  statement: p.natDegree = 0 ↔ exists x, C x = p
  proof: ⟨fun h => ⟨_, (eq_C_of_natDegree_eq_zero h).symm⟩, by aesop⟩

中文:
引理 natDegree_eq_zero
  条件: {p : R[X]}
  结论: p.natDegree = 0 ↔ 存在 x, C x = p
  证明: ⟨fun h => ⟨_, (eq_C_of_natDegree_eq_zero h).symm⟩, by aesop⟩

Depends on / 依赖: eq_C_of_natDegree_eq_zero
-/
lemma natDegree_eq_zero {p : R[X]} : p.natDegree = 0 ↔ exists x, C x = p :=
  ⟨fun h => ⟨_, (eq_C_of_natDegree_eq_zero h).symm⟩, by aesop⟩

/--
theorem `eq_C_coeff_zero_iff_natDegree_eq_zero` / 定理 `eq_C_coeff_zero_iff_natDegree_eq_zero`

English:
theorem eq_C_coeff_zero_iff_natDegree_eq_zero
  statement: p = C (p.coeff 0) ↔ p.natDegree = 0
  proof: ⟨fun h => by rw [h, natDegree_C], eq_C_of_natDegree_eq_zero⟩

中文:
定理 eq_C_coeff_zero_iff_natDegree_eq_zero
  结论: p = C (p.coeff 0) ↔ p.natDegree = 0
  证明: ⟨fun h => by rw [h, natDegree_C], eq_C_of_natDegree_eq_zero⟩

Depends on / 依赖: eq_C_of_natDegree_eq_zero, natDegree_C
-/
theorem eq_C_coeff_zero_iff_natDegree_eq_zero : p = C (p.coeff 0) ↔ p.natDegree = 0 :=
  ⟨fun h => by rw [h, natDegree_C], eq_C_of_natDegree_eq_zero⟩

/--
theorem `eq_one_of_monic_natDegree_zero` / 定理 `eq_one_of_monic_natDegree_zero`

English:
theorem eq_one_of_monic_natDegree_zero
  given: (hf : p.Monic) (hfd : p.natDegree = 0)
  statement: p = 1
  proof: by
  rw [Monic.def]; rw [leadingCoeff]; rw [hfd] at hf
  rw [eq_C_of_natDegree_eq_zero hfd]; rw [hf]; rw [map_one]

@[simp]

中文:
定理 eq_one_of_monic_natDegree_zero
  条件: (hf : p.Monic) (hfd : p.natDegree = 0)
  结论: p = 1
  证明: by
  rw [Monic.def]; rw [leadingCoeff]; rw [hfd] at hf
  rw [eq_C_of_natDegree_eq_zero hfd]; rw [hf]; rw [map_one]

@[simp]

Depends on / 依赖: Monic.def, eq_C_of_natDegree_eq_zero, leadingCoeff, map_one
-/
theorem eq_one_of_monic_natDegree_zero (hf : p.Monic) (hfd : p.natDegree = 0) : p = 1 := by
  rw [Monic.def]; rw [leadingCoeff]; rw [hfd] at hf
  rw [eq_C_of_natDegree_eq_zero hfd]; rw [hf]; rw [map_one]

@[simp]
/--
theorem `Monic.natDegree_eq_zero` / 定理 `Monic.natDegree_eq_zero`

English:
theorem Monic.natDegree_eq_zero
  given: (hf : p.Monic)
  statement: p.natDegree = 0 ↔ p = 1
  proof: ⟨eq_one_of_monic_natDegree_zero hf, by rintro rfl; simp⟩

中文:
定理 Monic.natDegree_eq_zero
  条件: (hf : p.Monic)
  结论: p.natDegree = 0 ↔ p = 1
  证明: ⟨eq_one_of_monic_natDegree_zero hf, by rintro rfl; simp⟩

Depends on / 依赖: eq_one_of_monic_natDegree_zero
-/
theorem Monic.natDegree_eq_zero (hf : p.Monic) : p.natDegree = 0 ↔ p = 1 :=
  ⟨eq_one_of_monic_natDegree_zero hf, by rintro rfl; simp⟩

/--
theorem `degree_sum_fin_lt` / 定理 `degree_sum_fin_lt`

English:
theorem degree_sum_fin_lt
  given: {n : Nat} (f : Fin n -> R)
  proof: (degree_sum_le _ _).trans_lt
    (Finset.sup_lt_iff <| WithBot.bot_lt_coe n).2 fun k _hk =>
(degree_C_mul_X_pow_le _ _).trans_lt WithBot.coe_lt_coe.2 k.is_lt

中文:
定理 degree_sum_fin_lt
  条件: {n : 自然数} (f : Fin n -> R)
  证明: (degree_sum_le _ _).trans_lt
    (Finset.sup_lt_iff <| WithBot.bot_lt_coe n).2 fun k _hk =>
(degree_C_mul_X_pow_le _ _).trans_lt WithBot.coe_lt_coe.2 k.is_lt

Depends on / 依赖: Finset, Finset.sup_lt_iff, WithBot, WithBot.bot_lt_coe, WithBot.coe_lt_coe, bot_lt_coe, coe_lt_coe, degree_C_mul_X_pow_le, degree_sum_le, is_lt, k.is_lt, sup_lt_iff, trans_lt
-/
theorem degree_sum_fin_lt {n : Nat} (f : Fin n -> R) :
    degree (∑ i : Fin n, C (f i) * X ^ (i : Nat)) < n :=
(degree_sum_le _ _).trans_lt
    (Finset.sup_lt_iff <| WithBot.bot_lt_coe n).2 fun k _hk =>
(degree_C_mul_X_pow_le _ _).trans_lt WithBot.coe_lt_coe.2 k.is_lt

/--
theorem `degree_C_lt_degree_C_mul_X` / 定理 `degree_C_lt_degree_C_mul_X`

English:
theorem degree_C_lt_degree_C_mul_X
  given: (ha : a != 0)
  statement: degree (C b) < degree (C a * X)
  proof: by
  simpa only [degree_C_mul_X ha] using degree_C_lt

中文:
定理 degree_C_lt_degree_C_mul_X
  条件: (ha : a != 0)
  结论: degree (C b) < degree (C a * X)
  证明: by
  simpa only [degree_C_mul_X ha] using degree_C_lt

Depends on / 依赖: degree_C_lt, degree_C_mul_X
-/
theorem degree_C_lt_degree_C_mul_X (ha : a != 0) : degree (C b) < degree (C a * X) := by
  simpa only [degree_C_mul_X ha] using degree_C_lt

end Semiring

section NontrivialSemiring

variable [Semiring R] [Nontrivial R] {p q : R[X]} (n : Nat)

/--
lemma `natDegree_mul_X` / 引理 `natDegree_mul_X`

English:
lemma natDegree_mul_X
  given: (hp : p != 0)
  statement: natDegree (p * X) = natDegree p + 1
  proof: by
  rw [natDegree_mul' (by simpa)]; rw [natDegree_X]

中文:
引理 natDegree_mul_X
  条件: (hp : p != 0)
  结论: natDegree (p * X) = natDegree p + 1
  证明: by
  rw [natDegree_mul' (by simpa)]; rw [natDegree_X]
-/
@[simp] lemma natDegree_mul_X (hp : p != 0) : natDegree (p * X) = natDegree p + 1 := by
  rw [natDegree_mul' (by simpa)]; rw [natDegree_X]

/--
lemma `natDegree_X_mul` / 引理 `natDegree_X_mul`

English:
lemma natDegree_X_mul
  given: (hp : p != 0)
  statement: natDegree (X * p) = natDegree p + 1
  proof: by
  rw [commute_X p]; rw [natDegree_mul_X hp]

中文:
引理 natDegree_X_mul
  条件: (hp : p != 0)
  结论: natDegree (X * p) = natDegree p + 1
  证明: by
  rw [commute_X p]; rw [natDegree_mul_X hp]
-/
@[simp] lemma natDegree_X_mul (hp : p != 0) : natDegree (X * p) = natDegree p + 1 := by
  rw [commute_X p]; rw [natDegree_mul_X hp]

/--
lemma `natDegree_mul_X_pow` / 引理 `natDegree_mul_X_pow`

English:
lemma natDegree_mul_X_pow
  given: (hp : p != 0)
  statement: natDegree (p * X ^ n) = natDegree p + n
  proof: by
  rw [natDegree_mul' (by simpa)]; rw [natDegree_X_pow]

中文:
引理 natDegree_mul_X_pow
  条件: (hp : p != 0)
  结论: natDegree (p * X ^ n) = natDegree p + n
  证明: by
  rw [natDegree_mul' (by simpa)]; rw [natDegree_X_pow]
-/
@[simp] lemma natDegree_mul_X_pow (hp : p != 0) : natDegree (p * X ^ n) = natDegree p + n := by
  rw [natDegree_mul' (by simpa)]; rw [natDegree_X_pow]

/--
lemma `natDegree_X_pow_mul` / 引理 `natDegree_X_pow_mul`

English:
lemma natDegree_X_pow_mul
  given: (hp : p != 0)
  statement: natDegree (X ^ n * p) = natDegree p + n
  proof: by
  rw [commute_X_pow]; rw [natDegree_mul_X_pow n hp]

中文:
引理 natDegree_X_pow_mul
  条件: (hp : p != 0)
  结论: natDegree (X ^ n * p) = natDegree p + n
  证明: by
  rw [commute_X_pow]; rw [natDegree_mul_X_pow n hp]
-/
@[simp] lemma natDegree_X_pow_mul (hp : p != 0) : natDegree (X ^ n * p) = natDegree p + n := by
  rw [commute_X_pow]; rw [natDegree_mul_X_pow n hp]

-- This lemma explicitly does not require the `Nontrivial R` assumption.
/--
theorem `natDegree_X_pow_le` / 定理 `natDegree_X_pow_le`

English:
theorem natDegree_X_pow_le
  given: {R : Type*} [Semiring R] (n : Nat)
  statement: (X ^ n : R[X]).natDegree <= n
  proof: by
  nontriviality R
  rw [Polynomial.natDegree_X_pow]

中文:
定理 natDegree_X_pow_le
  条件: {R : 类型} [Semiring R] (n : 自然数)
  结论: (X ^ n : R[X]).natDegree <= n
  证明: by
  nontriviality R
  rw [Polynomial.natDegree_X_pow]

Depends on / 依赖: Polynomial, Polynomial.natDegree_X_pow, natDegree_X_pow, nontriviality
-/
theorem natDegree_X_pow_le {R : Type*} [Semiring R] (n : Nat) : (X ^ n : R[X]).natDegree <= n := by
  nontriviality R
  rw [Polynomial.natDegree_X_pow]

/--
theorem `not_isUnit_X` / 定理 `not_isUnit_X`

English:
theorem not_isUnit_X
  statement: ¬IsUnit (X : R[X])
  proof: fun ⟨⟨_, g, _hfg, hgf⟩, rfl⟩ =>
zero_ne_one' R by
    rw [← coeff_one_zero]; rw [← hgf]
    simp

@[simp]

中文:
定理 not_isUnit_X
  结论: ¬IsUnit (X : R[X])
  证明: fun ⟨⟨_, g, _hfg, hgf⟩, rfl⟩ =>
zero_ne_one' R by
    rw [← coeff_one_zero]; rw [← hgf]
    simp

@[simp]

Depends on / 依赖: _hfg
-/
theorem not_isUnit_X : ¬IsUnit (X : R[X]) := fun ⟨⟨_, g, _hfg, hgf⟩, rfl⟩ =>
zero_ne_one' R by
    rw [← coeff_one_zero]; rw [← hgf]
    simp

@[simp]
/--
theorem `degree_mul_X` / 定理 `degree_mul_X`

English:
theorem degree_mul_X
  statement: degree (p * X) = degree p + 1
  proof: by simp [monic_X.degree_mul]

@[simp]

中文:
定理 degree_mul_X
  结论: degree (p * X) = degree p + 1
  证明: by simp [monic_X.degree_mul]

@[simp]

Depends on / 依赖: degree_mul, monic_X, monic_X.degree_mul
-/
theorem degree_mul_X : degree (p * X) = degree p + 1 := by simp [monic_X.degree_mul]

@[simp]
/--
theorem `degree_mul_X_pow` / 定理 `degree_mul_X_pow`

English:
theorem degree_mul_X_pow
  statement: degree (p * X ^ n) = degree p + n
  proof: by simp [(monic_X_pow n).degree_mul]

中文:
定理 degree_mul_X_pow
  结论: degree (p * X ^ n) = degree p + n
  证明: by simp [(monic_X_pow n).degree_mul]

Depends on / 依赖: degree_mul, monic_X_pow
-/
theorem degree_mul_X_pow : degree (p * X ^ n) = degree p + n := by simp [(monic_X_pow n).degree_mul]

end NontrivialSemiring

section Ring

variable [Ring R] {p q : R[X]}

/--
theorem `degree_sub_C` / 定理 `degree_sub_C`

English:
theorem degree_sub_C
  given: (hp : 0 < degree p)
  statement: degree (p - C a) = degree p
  proof: by
  rw [sub_eq_add_neg]; rw [← C_neg]; rw [degree_add_C hp]

@[simp]

中文:
定理 degree_sub_C
  条件: (hp : 0 < degree p)
  结论: degree (p - C a) = degree p
  证明: by
  rw [sub_eq_add_neg]; rw [← C_neg]; rw [degree_add_C hp]

@[simp]

Depends on / 依赖: C_neg, degree_add_C, sub_eq_add_neg
-/
theorem degree_sub_C (hp : 0 < degree p) : degree (p - C a) = degree p := by
  rw [sub_eq_add_neg]; rw [← C_neg]; rw [degree_add_C hp]

@[simp]
/--
theorem `natDegree_sub_C` / 定理 `natDegree_sub_C`

English:
theorem natDegree_sub_C
  given: {a : R}
  statement: natDegree (p - C a) = natDegree p
  proof: by
  rw [sub_eq_add_neg]; rw [← C_neg]; rw [natDegree_add_C]

中文:
定理 natDegree_sub_C
  条件: {a : R}
  结论: natDegree (p - C a) = natDegree p
  证明: by
  rw [sub_eq_add_neg]; rw [← C_neg]; rw [natDegree_add_C]

Depends on / 依赖: C_neg, natDegree_add_C, sub_eq_add_neg
-/
theorem natDegree_sub_C {a : R} : natDegree (p - C a) = natDegree p := by
  rw [sub_eq_add_neg]; rw [← C_neg]; rw [natDegree_add_C]

/--
theorem `leadingCoeff_sub_of_degree_lt` / 定理 `leadingCoeff_sub_of_degree_lt`

English:
theorem leadingCoeff_sub_of_degree_lt
  given: (h : Polynomial.degree q < Polynomial.degree p)
  proof: by
  rw [← q.degree_neg] at h
  rw [sub_eq_add_neg]; rw [leadingCoeff_add_of_degree_lt' h]

中文:
定理 leadingCoeff_sub_of_degree_lt
  条件: (h : Polynomial.degree q < Polynomial.degree p)
  证明: by
  rw [← q.degree_neg] at h
  rw [sub_eq_add_neg]; rw [leadingCoeff_add_of_degree_lt' h]

Depends on / 依赖: degree_neg, leadingCoeff_add_of_degree_lt, q.degree_neg, sub_eq_add_neg
-/
theorem leadingCoeff_sub_of_degree_lt (h : Polynomial.degree q < Polynomial.degree p) :
    (p - q).leadingCoeff = p.leadingCoeff := by
  rw [← q.degree_neg] at h
  rw [sub_eq_add_neg]; rw [leadingCoeff_add_of_degree_lt' h]

/--
theorem `leadingCoeff_sub_of_degree_lt'` / 定理 `leadingCoeff_sub_of_degree_lt'`

English:
theorem leadingCoeff_sub_of_degree_lt'
  given: (h : Polynomial.degree p < Polynomial.degree q)
  proof: by
  rw [← q.degree_neg] at h
  rw [sub_eq_add_neg]; rw [leadingCoeff_add_of_degree_lt h]; rw [leadingCoeff_neg]

中文:
定理 leadingCoeff_sub_of_degree_lt'
  条件: (h : Polynomial.degree p < Polynomial.degree q)
  证明: by
  rw [← q.degree_neg] at h
  rw [sub_eq_add_neg]; rw [leadingCoeff_add_of_degree_lt h]; rw [leadingCoeff_neg]

Depends on / 依赖: degree_neg, leadingCoeff_add_of_degree_lt, leadingCoeff_neg, q.degree_neg, sub_eq_add_neg
-/
theorem leadingCoeff_sub_of_degree_lt' (h : Polynomial.degree p < Polynomial.degree q) :
    (p - q).leadingCoeff = -q.leadingCoeff := by
  rw [← q.degree_neg] at h
  rw [sub_eq_add_neg]; rw [leadingCoeff_add_of_degree_lt h]; rw [leadingCoeff_neg]

/--
theorem `leadingCoeff_sub_of_degree_eq` / 定理 `leadingCoeff_sub_of_degree_eq`

English:
theorem leadingCoeff_sub_of_degree_eq
  statement: (h : degree p = degree q)
  proof: by
  replace h : degree p = degree (-q) := by rwa [q.degree_neg]
  replace hlc : leadingCoeff p + leadingCoeff (-q) != 0 := by
    rwa [← sub_ne_zero, sub_eq_add_neg, ← q.leadingCoeff_neg] at hlc
  rw [sub_eq_add_neg]; rw [leadingCoeff_add_of_degree_eq h hlc]; rw [leadingCoeff_neg]; rw [sub_eq_add_n

中文:
定理 leadingCoeff_sub_of_degree_eq
  结论: (h : degree p = degree q)
  证明: by
  replace h : degree p = degree (-q) := by rwa [q.degree_neg]
  replace hlc : leadingCoeff p + leadingCoeff (-q) != 0 := by
    rwa [← sub_ne_zero, sub_eq_add_neg, ← q.leadingCoeff_neg] at hlc
  rw [sub_eq_add_neg]; rw [leadingCoeff_add_of_degree_eq h hlc]; rw [leadingCoeff_neg]; rw [sub_eq_add_n

Depends on / 依赖: classical, degree, degree_neg, leadingCoeff, leadingCoeff_add_of_degree_eq, leadingCoeff_neg, q.degree_neg, q.leadingCoeff_neg, replace, sub_eq_add_neg, sub_ne_zero
-/
theorem leadingCoeff_sub_of_degree_eq (h : degree p = degree q)
    (hlc : leadingCoeff p != leadingCoeff q) :
    leadingCoeff (p - q) = leadingCoeff p - leadingCoeff q := by
  replace h : degree p = degree (-q) := by rwa [q.degree_neg]
  replace hlc : leadingCoeff p + leadingCoeff (-q) != 0 := by
    rwa [← sub_ne_zero, sub_eq_add_neg, ← q.leadingCoeff_neg] at hlc
  rw [sub_eq_add_neg]; rw [leadingCoeff_add_of_degree_eq h hlc]; rw [leadingCoeff_neg]; rw [sub_eq_add_neg]

/--
theorem `degree_sub_eq_left_of_degree_lt` / 定理 `degree_sub_eq_left_of_degree_lt`

English:
theorem degree_sub_eq_left_of_degree_lt
  given: (h : degree q < degree p)
  statement: degree (p - q) = degree p
  proof: by
  rw [← degree_neg q] at h
  rw [sub_eq_add_neg]; rw [degree_add_eq_left_of_degree_lt h]

中文:
定理 degree_sub_eq_left_of_degree_lt
  条件: (h : degree q < degree p)
  结论: degree (p - q) = degree p
  证明: by
  rw [← degree_neg q] at h
  rw [sub_eq_add_neg]; rw [degree_add_eq_left_of_degree_lt h]

Depends on / 依赖: degree_add_eq_left_of_degree_lt, degree_neg, sub_eq_add_neg
-/
theorem degree_sub_eq_left_of_degree_lt (h : degree q < degree p) : degree (p - q) = degree p := by
  rw [← degree_neg q] at h
  rw [sub_eq_add_neg]; rw [degree_add_eq_left_of_degree_lt h]

/--
theorem `degree_sub_eq_right_of_degree_lt` / 定理 `degree_sub_eq_right_of_degree_lt`

English:
theorem degree_sub_eq_right_of_degree_lt
  given: (h : degree p < degree q)
  statement: degree (p - q) = degree q
  proof: by
  rw [← degree_neg q] at h
  rw [sub_eq_add_neg]; rw [degree_add_eq_right_of_degree_lt h]; rw [degree_neg]

中文:
定理 degree_sub_eq_right_of_degree_lt
  条件: (h : degree p < degree q)
  结论: degree (p - q) = degree q
  证明: by
  rw [← degree_neg q] at h
  rw [sub_eq_add_neg]; rw [degree_add_eq_right_of_degree_lt h]; rw [degree_neg]

Depends on / 依赖: degree_add_eq_right_of_degree_lt, degree_neg, sub_eq_add_neg
-/
theorem degree_sub_eq_right_of_degree_lt (h : degree p < degree q) : degree (p - q) = degree q := by
  rw [← degree_neg q] at h
  rw [sub_eq_add_neg]; rw [degree_add_eq_right_of_degree_lt h]; rw [degree_neg]

/--
theorem `natDegree_sub_eq_left_of_natDegree_lt` / 定理 `natDegree_sub_eq_left_of_natDegree_lt`

English:
theorem natDegree_sub_eq_left_of_natDegree_lt
  given: (h : natDegree q < natDegree p)
  proof: natDegree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt (degree_lt_degree h))

中文:
定理 natDegree_sub_eq_left_of_natDegree_lt
  条件: (h : natDegree q < natDegree p)
  证明: natDegree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt (degree_lt_degree h))

Depends on / 依赖: degree_lt_degree, degree_sub_eq_left_of_degree_lt, natDegree_eq_of_degree_eq
-/
theorem natDegree_sub_eq_left_of_natDegree_lt (h : natDegree q < natDegree p) :
    natDegree (p - q) = natDegree p :=
  natDegree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt (degree_lt_degree h))

/--
theorem `natDegree_sub_eq_right_of_natDegree_lt` / 定理 `natDegree_sub_eq_right_of_natDegree_lt`

English:
theorem natDegree_sub_eq_right_of_natDegree_lt
  given: (h : natDegree p < natDegree q)
  proof: natDegree_eq_of_degree_eq (degree_sub_eq_right_of_degree_lt (degree_lt_degree h))

中文:
定理 natDegree_sub_eq_right_of_natDegree_lt
  条件: (h : natDegree p < natDegree q)
  证明: natDegree_eq_of_degree_eq (degree_sub_eq_right_of_degree_lt (degree_lt_degree h))

Depends on / 依赖: degree_lt_degree, degree_sub_eq_right_of_degree_lt, natDegree_eq_of_degree_eq
-/
theorem natDegree_sub_eq_right_of_natDegree_lt (h : natDegree p < natDegree q) :
    natDegree (p - q) = natDegree q :=
  natDegree_eq_of_degree_eq (degree_sub_eq_right_of_degree_lt (degree_lt_degree h))

end Ring

section NonzeroRing

variable [Nontrivial R]

section Semiring

variable [Semiring R]

@[simp]
/--
theorem `degree_X_add_C` / 定理 `degree_X_add_C`

English:
theorem degree_X_add_C
  given: (a : R)
  statement: degree (X + C a) = 1
  proof: by
  have : degree (C a) < degree (X : R[X]) :=
    calc
      degree (C a) <= 0 := degree_C_le
      _ < 1 := WithBot.coe_lt_coe.mpr zero_lt_one
      _ = degree X := degree_X.symm
  rw [degree_add_eq_left_of_degree_lt this]; rw [degree_X]

中文:
定理 degree_X_add_C
  条件: (a : R)
  结论: degree (X + C a) = 1
  证明: by
  have : degree (C a) < degree (X : R[X]) :=
    calc
      degree (C a) <= 0 := degree_C_le
      _ < 1 := WithBot.coe_lt_coe.mpr zero_lt_one
      _ = degree X := degree_X.symm
  rw [degree_add_eq_left_of_degree_lt this]; rw [degree_X]

Depends on / 依赖: WithBot, WithBot.coe_lt_coe.mpr, coe_lt_coe, degree, degree_C_le, degree_X, degree_X.symm, degree_add_eq_left_of_degree_lt, zero_lt_one
-/
theorem degree_X_add_C (a : R) : degree (X + C a) = 1 := by
  have : degree (C a) < degree (X : R[X]) :=
    calc
      degree (C a) <= 0 := degree_C_le
      _ < 1 := WithBot.coe_lt_coe.mpr zero_lt_one
      _ = degree X := degree_X.symm
  rw [degree_add_eq_left_of_degree_lt this]; rw [degree_X]

/--
theorem `natDegree_X_add_C` / 定理 `natDegree_X_add_C`

English:
theorem natDegree_X_add_C
  given: (x : R)
  statement: (X + C x).natDegree = 1
  proof: natDegree_eq_of_degree_eq_some degree_X_add_C x

@[simp]

中文:
定理 natDegree_X_add_C
  条件: (x : R)
  结论: (X + C x).natDegree = 1
  证明: natDegree_eq_of_degree_eq_some degree_X_add_C x

@[simp]

Depends on / 依赖: degree_X_add_C, natDegree_eq_of_degree_eq_some
-/
theorem natDegree_X_add_C (x : R) : (X + C x).natDegree = 1 :=
natDegree_eq_of_degree_eq_some degree_X_add_C x

@[simp]
/--
theorem `nextCoeff_X_add_C` / 定理 `nextCoeff_X_add_C`

English:
theorem nextCoeff_X_add_C
  given: [Semiring S] (c : S)
  statement: nextCoeff (X + C c) = c
  proof: by
  nontriviality S
  simp [nextCoeff_of_natDegree_pos]

中文:
定理 nextCoeff_X_add_C
  条件: [Semiring S] (c : S)
  结论: nextCoeff (X + C c) = c
  证明: by
  nontriviality S
  simp [nextCoeff_of_natDegree_pos]

Depends on / 依赖: nextCoeff_of_natDegree_pos, nontriviality
-/
theorem nextCoeff_X_add_C [Semiring S] (c : S) : nextCoeff (X + C c) = c := by
  nontriviality S
  simp [nextCoeff_of_natDegree_pos]

/--
theorem `degree_X_pow_add_C` / 定理 `degree_X_pow_add_C`

English:
theorem degree_X_pow_add_C
  given: {n : Nat} (hn : 0 < n) (a : R)
  statement: degree ((X : R[X]) ^ n + C a) = n
  proof: by
have : degree (C a) < degree ((X : R[X]) ^ n) := degree_C_le.trans_lt by
    rwa [degree_X_pow, Nat.cast_pos]
  rw [degree_add_eq_left_of_degree_lt this]; rw [degree_X_pow]

中文:
定理 degree_X_pow_add_C
  条件: {n : 自然数} (hn : 0 < n) (a : R)
  结论: degree ((X : R[X]) ^ n + C a) = n
  证明: by
have : degree (C a) < degree ((X : R[X]) ^ n) := degree_C_le.trans_lt by
    rwa [degree_X_pow, Nat.cast_pos]
  rw [degree_add_eq_left_of_degree_lt this]; rw [degree_X_pow]

Depends on / 依赖: Nat.cast_pos, cast_pos, degree, degree_C_le, degree_C_le.trans_lt, degree_X_pow, degree_add_eq_left_of_degree_lt, trans_lt
-/
theorem degree_X_pow_add_C {n : Nat} (hn : 0 < n) (a : R) : degree ((X : R[X]) ^ n + C a) = n := by
have : degree (C a) < degree ((X : R[X]) ^ n) := degree_C_le.trans_lt by
    rwa [degree_X_pow, Nat.cast_pos]
  rw [degree_add_eq_left_of_degree_lt this]; rw [degree_X_pow]

/--
theorem `X_pow_add_C_ne_zero` / 定理 `X_pow_add_C_ne_zero`

English:
theorem X_pow_add_C_ne_zero
  given: {n : Nat} (hn : 0 < n) (a : R)
  statement: (X : R[X]) ^ n + C a != 0
  proof: mt degree_eq_bot.2
    (show degree ((X : R[X]) ^ n + C a) != ⊥ by
      rw [degree_X_pow_add_C hn a]; exact WithBot.coe_ne_bot)

中文:
定理 X_pow_add_C_ne_zero
  条件: {n : 自然数} (hn : 0 < n) (a : R)
  结论: (X : R[X]) ^ n + C a != 0
  证明: mt degree_eq_bot.2
    (show degree ((X : R[X]) ^ n + C a) != ⊥ by
      rw [degree_X_pow_add_C hn a]; exact WithBot.coe_ne_bot)

Depends on / 依赖: WithBot, WithBot.coe_ne_bot, coe_ne_bot, degree, degree_X_pow_add_C, degree_eq_bot
-/
theorem X_pow_add_C_ne_zero {n : Nat} (hn : 0 < n) (a : R) : (X : R[X]) ^ n + C a != 0 :=
  mt degree_eq_bot.2
    (show degree ((X : R[X]) ^ n + C a) != ⊥ by
      rw [degree_X_pow_add_C hn a]; exact WithBot.coe_ne_bot)

/--
theorem `X_add_C_ne_zero` / 定理 `X_add_C_ne_zero`

English:
theorem X_add_C_ne_zero
  given: (r : R)
  statement: X + C r != 0
  proof: pow_one (X : R[X]) ▸ X_pow_add_C_ne_zero zero_lt_one r

中文:
定理 X_add_C_ne_zero
  条件: (r : R)
  结论: X + C r != 0
  证明: pow_one (X : R[X]) ▸ X_pow_add_C_ne_zero zero_lt_one r

Depends on / 依赖: X_pow_add_C_ne_zero, pow_one, zero_lt_one
-/
theorem X_add_C_ne_zero (r : R) : X + C r != 0 :=
  pow_one (X : R[X]) ▸ X_pow_add_C_ne_zero zero_lt_one r

/--
theorem `zero_notMem_multiset_map_X_add_C` / 定理 `zero_notMem_multiset_map_X_add_C`

English:
theorem zero_notMem_multiset_map_X_add_C
  given: {α : Type*} (m : Multiset α) (f : α -> R)
  proof: fun mem =>
  let ⟨_a, _, ha⟩ := Multiset.mem_map.mp mem
  X_add_C_ne_zero _ ha

中文:
定理 zero_notMem_multiset_map_X_add_C
  条件: {α : 类型} (m : Multiset α) (f : α -> R)
  证明: fun mem =>
  let ⟨_a, _, ha⟩ := Multiset.mem_map.mp mem
  X_add_C_ne_zero _ ha
-/
theorem zero_notMem_multiset_map_X_add_C {α : Type*} (m : Multiset α) (f : α -> R) :
    (0 : R[X]) ∉ m.map fun a => X + C (f a) := fun mem =>
  let ⟨_a, _, ha⟩ := Multiset.mem_map.mp mem
  X_add_C_ne_zero _ ha

/--
theorem `natDegree_X_pow_add_C` / 定理 `natDegree_X_pow_add_C`

English:
theorem natDegree_X_pow_add_C
  given: {n : Nat} {r : R}
  statement: (X ^ n + C r).natDegree = n
  proof: by
  simp

中文:
定理 natDegree_X_pow_add_C
  条件: {n : 自然数} {r : R}
  结论: (X ^ n + C r).natDegree = n
  证明: by
  simp
-/
theorem natDegree_X_pow_add_C {n : Nat} {r : R} : (X ^ n + C r).natDegree = n := by
  simp

/--
theorem `X_pow_add_C_ne_one` / 定理 `X_pow_add_C_ne_one`

English:
theorem X_pow_add_C_ne_one
  given: {n : Nat} (hn : 0 < n) (a : R)
  statement: (X : R[X]) ^ n + C a != 1
  proof: fun h =>
hn.ne' by simpa only [natDegree_X_pow_add_C, natDegree_one] using congr_arg natDegree h

中文:
定理 X_pow_add_C_ne_one
  条件: {n : 自然数} (hn : 0 < n) (a : R)
  结论: (X : R[X]) ^ n + C a != 1
  证明: fun h =>
hn.ne' by simpa only [natDegree_X_pow_add_C, natDegree_one] using congr_arg natDegree h
-/
theorem X_pow_add_C_ne_one {n : Nat} (hn : 0 < n) (a : R) : (X : R[X]) ^ n + C a != 1 := fun h =>
hn.ne' by simpa only [natDegree_X_pow_add_C, natDegree_one] using congr_arg natDegree h

/--
theorem `X_add_C_ne_one` / 定理 `X_add_C_ne_one`

English:
theorem X_add_C_ne_one
  given: (r : R)
  statement: X + C r != 1
  proof: pow_one (X : R[X]) ▸ X_pow_add_C_ne_one zero_lt_one r

中文:
定理 X_add_C_ne_one
  条件: (r : R)
  结论: X + C r != 1
  证明: pow_one (X : R[X]) ▸ X_pow_add_C_ne_one zero_lt_one r

Depends on / 依赖: X_pow_add_C_ne_one, pow_one, zero_lt_one
-/
theorem X_add_C_ne_one (r : R) : X + C r != 1 :=
  pow_one (X : R[X]) ▸ X_pow_add_C_ne_one zero_lt_one r

end Semiring

end NonzeroRing

section Semiring

variable [Semiring R]

@[simp]
/--
theorem `leadingCoeff_X_pow_add_C` / 定理 `leadingCoeff_X_pow_add_C`

English:
theorem leadingCoeff_X_pow_add_C
  given: {n : Nat} (hn : 0 < n) {r : R}
  proof: by
  nontriviality R
  rw [leadingCoeff]; rw [natDegree_X_pow_add_C]; rw [coeff_add]; rw [coeff_X_pow_self]; rw [coeff_C]; rw [if_neg (pos_iff_ne_zero.mp hn)]; rw [add_zero]

@[simp]

中文:
定理 leadingCoeff_X_pow_add_C
  条件: {n : 自然数} (hn : 0 < n) {r : R}
  证明: by
  nontriviality R
  rw [leadingCoeff]; rw [natDegree_X_pow_add_C]; rw [coeff_add]; rw [coeff_X_pow_self]; rw [coeff_C]; rw [if_neg (pos_iff_ne_zero.mp hn)]; rw [add_zero]

@[simp]

Depends on / 依赖: add_zero, coeff_C, coeff_X_pow_self, coeff_add, if_neg, leadingCoeff, natDegree_X_pow_add_C, nontriviality, pos_iff_ne_zero, pos_iff_ne_zero.mp
-/
theorem leadingCoeff_X_pow_add_C {n : Nat} (hn : 0 < n) {r : R} :
    (X ^ n + C r).leadingCoeff = 1 := by
  nontriviality R
  rw [leadingCoeff]; rw [natDegree_X_pow_add_C]; rw [coeff_add]; rw [coeff_X_pow_self]; rw [coeff_C]; rw [if_neg (pos_iff_ne_zero.mp hn)]; rw [add_zero]

@[simp]
/--
theorem `leadingCoeff_X_add_C` / 定理 `leadingCoeff_X_add_C`

English:
theorem leadingCoeff_X_add_C
  given: [Semiring S] (r : S)
  statement: (X + C r).leadingCoeff = 1
  proof: by
  rw [← pow_one (X : S[X]), leadingCoeff_X_pow_add_C zero_lt_one]

@[simp]

中文:
定理 leadingCoeff_X_add_C
  条件: [Semiring S] (r : S)
  结论: (X + C r).leadingCoeff = 1
  证明: by
  rw [← pow_one (X : S[X]), leadingCoeff_X_pow_add_C zero_lt_one]

@[simp]

Depends on / 依赖: leadingCoeff_X_pow_add_C, pow_one, zero_lt_one
-/
theorem leadingCoeff_X_add_C [Semiring S] (r : S) : (X + C r).leadingCoeff = 1 := by
  rw [← pow_one (X : S[X]), leadingCoeff_X_pow_add_C zero_lt_one]

@[simp]
/--
theorem `leadingCoeff_X_pow_add_one` / 定理 `leadingCoeff_X_pow_add_one`

English:
theorem leadingCoeff_X_pow_add_one
  given: {n : Nat} (hn : 0 < n)
  statement: (X ^ n + 1 : R[X]).leadingCoeff = 1
  proof: leadingCoeff_X_pow_add_C hn

@[simp]

中文:
定理 leadingCoeff_X_pow_add_one
  条件: {n : 自然数} (hn : 0 < n)
  结论: (X ^ n + 1 : R[X]).leadingCoeff = 1
  证明: leadingCoeff_X_pow_add_C hn

@[simp]

Depends on / 依赖: leadingCoeff_X_pow_add_C
-/
theorem leadingCoeff_X_pow_add_one {n : Nat} (hn : 0 < n) : (X ^ n + 1 : R[X]).leadingCoeff = 1 :=
  leadingCoeff_X_pow_add_C hn

@[simp]
/--
theorem `leadingCoeff_pow_X_add_C` / 定理 `leadingCoeff_pow_X_add_C`

English:
theorem leadingCoeff_pow_X_add_C
  given: (r : R) (i : Nat)
  statement: leadingCoeff ((X + C r) ^ i) = 1
  proof: by
  nontriviality
  rw [leadingCoeff_pow'] <;> simp

中文:
定理 leadingCoeff_pow_X_add_C
  条件: (r : R) (i : 自然数)
  结论: leadingCoeff ((X + C r) ^ i) = 1
  证明: by
  nontriviality
  rw [leadingCoeff_pow'] <;> simp

Depends on / 依赖: leadingCoeff_pow, nontriviality
-/
theorem leadingCoeff_pow_X_add_C (r : R) (i : Nat) : leadingCoeff ((X + C r) ^ i) = 1 := by
  nontriviality
  rw [leadingCoeff_pow'] <;> simp

variable [NoZeroDivisors R] {p q : R[X]}

@[simp]
/--
lemma `degree_mul` / 引理 `degree_mul`

English:
lemma degree_mul
  statement: degree (p * q) = degree p + degree q
  proof: letI := Classical.decEq R
  if hp0 : p = 0 then by simp only [hp0, degree_zero, zero_mul, WithBot.bot_add]
  else
    if hq0 : q = 0 then by simp only [hq0, degree_zero, mul_zero, WithBot.add_bot]
else degree_mul' mul_ne_zero (mt leadingCoeff_eq_zero.1 hp0) (mt leadingCoeff_eq_zero.1 hq0)

中文:
引理 degree_mul
  结论: degree (p * q) = degree p + degree q
  证明: letI := Classical.decEq R
  if hp0 : p = 0 then by simp only [hp0, degree_zero, zero_mul, WithBot.bot_add]
  else
    if hq0 : q = 0 then by simp only [hq0, degree_zero, mul_zero, WithBot.add_bot]
else degree_mul' mul_ne_zero (mt leadingCoeff_eq_zero.1 hp0) (mt leadingCoeff_eq_zero.1 hq0)

Depends on / 依赖: Classical, Classical.decEq, WithBot, WithBot.add_bot, WithBot.bot_add, add_bot, bot_add, degree_mul, degree_zero, leadingCoeff_eq_zero, mul_ne_zero, mul_zero, zero_mul
-/
lemma degree_mul : degree (p * q) = degree p + degree q :=
  letI := Classical.decEq R
  if hp0 : p = 0 then by simp only [hp0, degree_zero, zero_mul, WithBot.bot_add]
  else
    if hq0 : q = 0 then by simp only [hq0, degree_zero, mul_zero, WithBot.add_bot]
else degree_mul' mul_ne_zero (mt leadingCoeff_eq_zero.1 hp0) (mt leadingCoeff_eq_zero.1 hq0)

/--
Definition of `degreeMonoidHom` / `degreeMonoidHom` 的定义

English:
definition degreeMonoidHom
  signature: [Nontrivial R]
  body: degree
  map_one' := degree_one
  map_mul' _ _ := degree_mul

@[simp]

中文:
定义 degreeMonoidHom
  签名: [Nontrivial R]
  定义体: degree
  map_one' := degree_one
  map_mul' _ _ := degree_mul

@[simp]

Depends on / 依赖: degree
-/
def degreeMonoidHom [Nontrivial R] : R[X] ->* Multiplicative (WithBot Nat) where
  toFun := degree
  map_one' := degree_one
  map_mul' _ _ := degree_mul

@[simp]
/--
lemma `degree_pow` / 引理 `degree_pow`

English:
lemma degree_pow
  given: [Nontrivial R] (p : R[X]) (n : Nat)
  statement: degree (p ^ n) = n • degree p
  proof: map_pow (@degreeMonoidHom R _ _ _) _ _

@[simp]

中文:
引理 degree_pow
  条件: [Nontrivial R] (p : R[X]) (n : 自然数)
  结论: degree (p ^ n) = n • degree p
  证明: map_pow (@degreeMonoidHom R _ _ _) _ _

@[simp]

Depends on / 依赖: degreeMonoidHom, map_pow
-/
lemma degree_pow [Nontrivial R] (p : R[X]) (n : Nat) : degree (p ^ n) = n • degree p :=
  map_pow (@degreeMonoidHom R _ _ _) _ _

@[simp]
/--
lemma `leadingCoeff_mul` / 引理 `leadingCoeff_mul`

English:
lemma leadingCoeff_mul
  given: (p q : R[X])
  statement: leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q
  proof: by
  by_cases hp : p = 0
  · simp only [hp, zero_mul, leadingCoeff_zero]
  · by_cases hq : q = 0
    · simp only [hq, mul_zero, leadingCoeff_zero]
    · rw [leadingCoeff_mul']
      exact mul_ne_zero (mt leadingCoeff_eq_zero.1 hp) (mt leadingCoeff_eq_zero.1 hq)

中文:
引理 leadingCoeff_mul
  条件: (p q : R[X])
  结论: leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q
  证明: by
  by_cases hp : p = 0
  · simp only [hp, zero_mul, leadingCoeff_zero]
  · by_cases hq : q = 0
    · simp only [hq, mul_zero, leadingCoeff_zero]
    · rw [leadingCoeff_mul']
      exact mul_ne_zero (mt leadingCoeff_eq_zero.1 hp) (mt leadingCoeff_eq_zero.1 hq)

Depends on / 依赖: leadingCoeff_eq_zero, leadingCoeff_mul, leadingCoeff_zero, mul_ne_zero, mul_zero, zero_mul
-/
lemma leadingCoeff_mul (p q : R[X]) : leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q := by
  by_cases hp : p = 0
  · simp only [hp, zero_mul, leadingCoeff_zero]
  · by_cases hq : q = 0
    · simp only [hq, mul_zero, leadingCoeff_zero]
    · rw [leadingCoeff_mul']
      exact mul_ne_zero (mt leadingCoeff_eq_zero.1 hp) (mt leadingCoeff_eq_zero.1 hq)

/--
Definition of `leadingCoeffHom` / `leadingCoeffHom` 的定义

English:
definition leadingCoeffHom
  signature: : R[X] ->* R where
  body: leadingCoeff
  map_one' := by simp
  map_mul' := leadingCoeff_mul

@[simp]

中文:
定义 leadingCoeffHom
  签名: : R[X] ->* R where
  定义体: leadingCoeff
  map_one' := by simp
  map_mul' := leadingCoeff_mul

@[simp]

Depends on / 依赖: leadingCoeff
-/
def leadingCoeffHom : R[X] ->* R where
  toFun := leadingCoeff
  map_one' := by simp
  map_mul' := leadingCoeff_mul

@[simp]
/--
lemma `leadingCoeffHom_apply` / 引理 `leadingCoeffHom_apply`

English:
lemma leadingCoeffHom_apply
  given: (p : R[X])
  statement: leadingCoeffHom p = leadingCoeff p
  proof: rfl

@[simp]

中文:
引理 leadingCoeffHom_apply
  条件: (p : R[X])
  结论: leadingCoeffHom p = leadingCoeff p
  证明: rfl

@[simp]
-/
lemma leadingCoeffHom_apply (p : R[X]) : leadingCoeffHom p = leadingCoeff p :=
  rfl

@[simp]
/--
lemma `leadingCoeff_pow` / 引理 `leadingCoeff_pow`

English:
lemma leadingCoeff_pow
  given: (p : R[X]) (n : Nat)
  statement: leadingCoeff (p ^ n) = leadingCoeff p ^ n
  proof: (leadingCoeffHom : R[X] ->* R).map_pow p n

中文:
引理 leadingCoeff_pow
  条件: (p : R[X]) (n : 自然数)
  结论: leadingCoeff (p ^ n) = leadingCoeff p ^ n
  证明: (leadingCoeffHom : R[X] ->* R).map_pow p n

Depends on / 依赖: leadingCoeffHom, map_pow
-/
lemma leadingCoeff_pow (p : R[X]) (n : Nat) : leadingCoeff (p ^ n) = leadingCoeff p ^ n :=
  (leadingCoeffHom : R[X] ->* R).map_pow p n

/--
lemma `leadingCoeff_dvd_leadingCoeff` / 引理 `leadingCoeff_dvd_leadingCoeff`

English:
lemma leadingCoeff_dvd_leadingCoeff
  given: {a p : R[X]} (hap : a ∣ p)
  proof: map_dvd leadingCoeffHom hap

中文:
引理 leadingCoeff_dvd_leadingCoeff
  条件: {a p : R[X]} (hap : a ∣ p)
  证明: map_dvd leadingCoeffHom hap

Depends on / 依赖: leadingCoeffHom, map_dvd
-/
lemma leadingCoeff_dvd_leadingCoeff {a p : R[X]} (hap : a ∣ p) :
    a.leadingCoeff ∣ p.leadingCoeff :=
  map_dvd leadingCoeffHom hap

/--
lemma `degree_le_mul_left` / 引理 `degree_le_mul_left`

English:
lemma degree_le_mul_left
  given: (p : R[X]) (hq : q != 0)
  statement: degree p <= degree (p * q)
  proof: by
  obtain rfl | hp := eq_or_ne p 0
  · simp
  · rw [degree_mul, degree_eq_natDegree hp, degree_eq_natDegree hq]
    exact WithBot.coe_le_coe.2 (Nat.le_add_right _ _)

中文:
引理 degree_le_mul_left
  条件: (p : R[X]) (hq : q != 0)
  结论: degree p <= degree (p * q)
  证明: by
  obtain rfl | hp := eq_or_ne p 0
  · simp
  · rw [degree_mul, degree_eq_natDegree hp, degree_eq_natDegree hq]
    exact WithBot.coe_le_coe.2 (Nat.le_add_right _ _)

Depends on / 依赖: Nat.le_add_right, WithBot, WithBot.coe_le_coe, coe_le_coe, degree_eq_natDegree, degree_mul, eq_or_ne, le_add_right
-/
lemma degree_le_mul_left (p : R[X]) (hq : q != 0) : degree p <= degree (p * q) := by
  obtain rfl | hp := eq_or_ne p 0
  · simp
  · rw [degree_mul, degree_eq_natDegree hp, degree_eq_natDegree hq]
    exact WithBot.coe_le_coe.2 (Nat.le_add_right _ _)

end Semiring

section CommSemiring
variable [CommSemiring R] {a p : R[X]} (hp : p.Monic)
include hp

/--
lemma `Monic.natDegree_pos` / 引理 `Monic.natDegree_pos`

English:
lemma Monic.natDegree_pos
  statement: 0 < natDegree p ↔ p != 1
  proof: Nat.pos_iff_ne_zero.trans hp.natDegree_eq_zero.not

中文:
引理 Monic.natDegree_pos
  结论: 0 < natDegree p ↔ p != 1
  证明: Nat.pos_iff_ne_zero.trans hp.natDegree_eq_zero.not

Depends on / 依赖: Nat.pos_iff_ne_zero.trans, hp.natDegree_eq_zero.not, natDegree_eq_zero, pos_iff_ne_zero
-/
lemma Monic.natDegree_pos : 0 < natDegree p ↔ p != 1 :=
  Nat.pos_iff_ne_zero.trans hp.natDegree_eq_zero.not

/--
lemma `Monic.degree_pos` / 引理 `Monic.degree_pos`

English:
lemma Monic.degree_pos
  statement: 0 < degree p ↔ p != 1
  proof: natDegree_pos_iff_degree_pos.symm.trans hp.natDegree_pos

中文:
引理 Monic.degree_pos
  结论: 0 < degree p ↔ p != 1
  证明: natDegree_pos_iff_degree_pos.symm.trans hp.natDegree_pos

Depends on / 依赖: hp.natDegree_pos, natDegree_pos, natDegree_pos_iff_degree_pos, natDegree_pos_iff_degree_pos.symm.trans
-/
lemma Monic.degree_pos : 0 < degree p ↔ p != 1 :=
  natDegree_pos_iff_degree_pos.symm.trans hp.natDegree_pos

end CommSemiring

section Ring

variable [Ring R]

@[simp]
/--
theorem `leadingCoeff_X_pow_sub_C` / 定理 `leadingCoeff_X_pow_sub_C`

English:
theorem leadingCoeff_X_pow_sub_C
  given: {n : Nat} (hn : 0 < n) {r : R}
  proof: by
  rw [sub_eq_add_neg]; rw [← map_neg C r]; rw [leadingCoeff_X_pow_add_C hn]

@[simp]

中文:
定理 leadingCoeff_X_pow_sub_C
  条件: {n : 自然数} (hn : 0 < n) {r : R}
  证明: by
  rw [sub_eq_add_neg]; rw [← map_neg C r]; rw [leadingCoeff_X_pow_add_C hn]

@[simp]

Depends on / 依赖: leadingCoeff_X_pow_add_C, map_neg, sub_eq_add_neg
-/
theorem leadingCoeff_X_pow_sub_C {n : Nat} (hn : 0 < n) {r : R} :
    (X ^ n - C r).leadingCoeff = 1 := by
  rw [sub_eq_add_neg]; rw [← map_neg C r]; rw [leadingCoeff_X_pow_add_C hn]

@[simp]
/--
theorem `leadingCoeff_X_pow_sub_one` / 定理 `leadingCoeff_X_pow_sub_one`

English:
theorem leadingCoeff_X_pow_sub_one
  given: {n : Nat} (hn : 0 < n)
  statement: (X ^ n - 1 : R[X]).leadingCoeff = 1
  proof: leadingCoeff_X_pow_sub_C hn

中文:
定理 leadingCoeff_X_pow_sub_one
  条件: {n : 自然数} (hn : 0 < n)
  结论: (X ^ n - 1 : R[X]).leadingCoeff = 1
  证明: leadingCoeff_X_pow_sub_C hn

Depends on / 依赖: leadingCoeff_X_pow_sub_C
-/
theorem leadingCoeff_X_pow_sub_one {n : Nat} (hn : 0 < n) : (X ^ n - 1 : R[X]).leadingCoeff = 1 :=
  leadingCoeff_X_pow_sub_C hn

variable [Nontrivial R]

@[simp]
/--
theorem `degree_X_sub_C` / 定理 `degree_X_sub_C`

English:
theorem degree_X_sub_C
  given: (a : R)
  statement: degree (X - C a) = 1
  proof: by
  rw [sub_eq_add_neg]; rw [← map_neg C a]; rw [degree_X_add_C]

中文:
定理 degree_X_sub_C
  条件: (a : R)
  结论: degree (X - C a) = 1
  证明: by
  rw [sub_eq_add_neg]; rw [← map_neg C a]; rw [degree_X_add_C]

Depends on / 依赖: degree_X_add_C, map_neg, sub_eq_add_neg
-/
theorem degree_X_sub_C (a : R) : degree (X - C a) = 1 := by
  rw [sub_eq_add_neg]; rw [← map_neg C a]; rw [degree_X_add_C]

/--
theorem `natDegree_X_sub_C` / 定理 `natDegree_X_sub_C`

English:
theorem natDegree_X_sub_C
  given: (x : R)
  statement: (X - C x).natDegree = 1
  proof: by
  rw [natDegree_sub_C]; rw [natDegree_X]

@[simp]

中文:
定理 natDegree_X_sub_C
  条件: (x : R)
  结论: (X - C x).natDegree = 1
  证明: by
  rw [natDegree_sub_C]; rw [natDegree_X]

@[simp]

Depends on / 依赖: natDegree_X, natDegree_sub_C
-/
theorem natDegree_X_sub_C (x : R) : (X - C x).natDegree = 1 := by
  rw [natDegree_sub_C]; rw [natDegree_X]

@[simp]
/--
theorem `nextCoeff_X_sub_C` / 定理 `nextCoeff_X_sub_C`

English:
theorem nextCoeff_X_sub_C
  given: [Ring S] (c : S)
  statement: nextCoeff (X - C c) = -c
  proof: by
  rw [sub_eq_add_neg]; rw [← map_neg C c]; rw [nextCoeff_X_add_C]

中文:
定理 nextCoeff_X_sub_C
  条件: [Ring S] (c : S)
  结论: nextCoeff (X - C c) = -c
  证明: by
  rw [sub_eq_add_neg]; rw [← map_neg C c]; rw [nextCoeff_X_add_C]

Depends on / 依赖: map_neg, nextCoeff_X_add_C, sub_eq_add_neg
-/
theorem nextCoeff_X_sub_C [Ring S] (c : S) : nextCoeff (X - C c) = -c := by
  rw [sub_eq_add_neg]; rw [← map_neg C c]; rw [nextCoeff_X_add_C]

/--
theorem `degree_X_pow_sub_C` / 定理 `degree_X_pow_sub_C`

English:
theorem degree_X_pow_sub_C
  given: {n : Nat} (hn : 0 < n) (a : R)
  statement: degree ((X : R[X]) ^ n - C a) = n
  proof: by
  rw [sub_eq_add_neg]; rw [← map_neg C a]; rw [degree_X_pow_add_C hn]

中文:
定理 degree_X_pow_sub_C
  条件: {n : 自然数} (hn : 0 < n) (a : R)
  结论: degree ((X : R[X]) ^ n - C a) = n
  证明: by
  rw [sub_eq_add_neg]; rw [← map_neg C a]; rw [degree_X_pow_add_C hn]

Depends on / 依赖: degree_X_pow_add_C, map_neg, sub_eq_add_neg
-/
theorem degree_X_pow_sub_C {n : Nat} (hn : 0 < n) (a : R) : degree ((X : R[X]) ^ n - C a) = n := by
  rw [sub_eq_add_neg]; rw [← map_neg C a]; rw [degree_X_pow_add_C hn]

/--
theorem `X_pow_sub_C_ne_zero` / 定理 `X_pow_sub_C_ne_zero`

English:
theorem X_pow_sub_C_ne_zero
  given: {n : Nat} (hn : 0 < n) (a : R)
  statement: (X : R[X]) ^ n - C a != 0
  proof: by
  rw [sub_eq_add_neg]; rw [← map_neg C a]
  exact X_pow_add_C_ne_zero hn _

中文:
定理 X_pow_sub_C_ne_zero
  条件: {n : 自然数} (hn : 0 < n) (a : R)
  结论: (X : R[X]) ^ n - C a != 0
  证明: by
  rw [sub_eq_add_neg]; rw [← map_neg C a]
  exact X_pow_add_C_ne_zero hn _

Depends on / 依赖: X_pow_add_C_ne_zero, map_neg, sub_eq_add_neg
-/
theorem X_pow_sub_C_ne_zero {n : Nat} (hn : 0 < n) (a : R) : (X : R[X]) ^ n - C a != 0 := by
  rw [sub_eq_add_neg]; rw [← map_neg C a]
  exact X_pow_add_C_ne_zero hn _

/--
theorem `X_sub_C_ne_zero` / 定理 `X_sub_C_ne_zero`

English:
theorem X_sub_C_ne_zero
  given: (r : R)
  statement: X - C r != 0
  proof: pow_one (X : R[X]) ▸ X_pow_sub_C_ne_zero zero_lt_one r

中文:
定理 X_sub_C_ne_zero
  条件: (r : R)
  结论: X - C r != 0
  证明: pow_one (X : R[X]) ▸ X_pow_sub_C_ne_zero zero_lt_one r

Depends on / 依赖: X_pow_sub_C_ne_zero, pow_one, zero_lt_one
-/
theorem X_sub_C_ne_zero (r : R) : X - C r != 0 :=
  pow_one (X : R[X]) ▸ X_pow_sub_C_ne_zero zero_lt_one r

/--
theorem `zero_notMem_multiset_map_X_sub_C` / 定理 `zero_notMem_multiset_map_X_sub_C`

English:
theorem zero_notMem_multiset_map_X_sub_C
  given: {α : Type*} (m : Multiset α) (f : α -> R)
  proof: fun mem =>
  let ⟨_a, _, ha⟩ := Multiset.mem_map.mp mem
  X_sub_C_ne_zero _ ha

中文:
定理 zero_notMem_multiset_map_X_sub_C
  条件: {α : 类型} (m : Multiset α) (f : α -> R)
  证明: fun mem =>
  let ⟨_a, _, ha⟩ := Multiset.mem_map.mp mem
  X_sub_C_ne_zero _ ha
-/
theorem zero_notMem_multiset_map_X_sub_C {α : Type*} (m : Multiset α) (f : α -> R) :
    (0 : R[X]) ∉ m.map fun a => X - C (f a) := fun mem =>
  let ⟨_a, _, ha⟩ := Multiset.mem_map.mp mem
  X_sub_C_ne_zero _ ha

/--
theorem `natDegree_X_pow_sub_C` / 定理 `natDegree_X_pow_sub_C`

English:
theorem natDegree_X_pow_sub_C
  given: {n : Nat} {r : R}
  statement: (X ^ n - C r).natDegree = n
  proof: by
  rw [sub_eq_add_neg]; rw [← map_neg C r]; rw [natDegree_X_pow_add_C]

@[simp]

中文:
定理 natDegree_X_pow_sub_C
  条件: {n : 自然数} {r : R}
  结论: (X ^ n - C r).natDegree = n
  证明: by
  rw [sub_eq_add_neg]; rw [← map_neg C r]; rw [natDegree_X_pow_add_C]

@[simp]

Depends on / 依赖: map_neg, natDegree_X_pow_add_C, sub_eq_add_neg
-/
theorem natDegree_X_pow_sub_C {n : Nat} {r : R} : (X ^ n - C r).natDegree = n := by
  rw [sub_eq_add_neg]; rw [← map_neg C r]; rw [natDegree_X_pow_add_C]

@[simp]
/--
theorem `leadingCoeff_X_sub_C` / 定理 `leadingCoeff_X_sub_C`

English:
theorem leadingCoeff_X_sub_C
  given: [Ring S] (r : S)
  statement: (X - C r).leadingCoeff = 1
  proof: by
  rw [sub_eq_add_neg]; rw [← map_neg C r]; rw [leadingCoeff_X_add_C]

中文:
定理 leadingCoeff_X_sub_C
  条件: [Ring S] (r : S)
  结论: (X - C r).leadingCoeff = 1
  证明: by
  rw [sub_eq_add_neg]; rw [← map_neg C r]; rw [leadingCoeff_X_add_C]

Depends on / 依赖: leadingCoeff_X_add_C, map_neg, sub_eq_add_neg
-/
theorem leadingCoeff_X_sub_C [Ring S] (r : S) : (X - C r).leadingCoeff = 1 := by
  rw [sub_eq_add_neg]; rw [← map_neg C r]; rw [leadingCoeff_X_add_C]

end Ring
end Polynomial
