/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Degree
public import Mathlib.Algebra.Order.Ring.WithTop
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.Nat.Cast.WithTop
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Order.SuccPred.WithBot

/-!
# Degree of univariate polynomials

## Main definitions

* `Polynomial.degree`: the degree of a polynomial, where `0` has degree `⊥`
* `Polynomial.natDegree`: the degree of a polynomial, where `0` has degree `0`
* `Polynomial.leadingCoeff`: the leading coefficient of a polynomial
* `Polynomial.Monic`: a polynomial is monic if its leading coefficient is 1
* `Polynomial.nextCoeff`: the next coefficient after the leading coefficient

## Main results

* `Polynomial.degree_eq_natDegree`: the degree and natDegree coincide for nonzero polynomials
-/

@[expose] public section

open Finset

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b c d : R} {n m : Nat}

section Semiring

variable [Semiring R] {p q r : R[X]}

/--
Definition of `degree` / `degree` 的定义

English:
definition degree
  signature: (p : R[X])
  body: p.support.max

中文:
定义 degree
  签名: (p : R[X])
  定义体: p.support.max

Depends on / 依赖: p.support.max, support
-/
def degree (p : R[X]) : WithBot Nat :=
  p.support.max

/--
Definition of `natDegree` / `natDegree` 的定义

English:
definition natDegree
  signature: (p : R[X])
  body: (degree p).unbotD 0

中文:
定义 natDegree
  签名: (p : R[X])
  定义体: (degree p).unbotD 0

Depends on / 依赖: degree, unbotD
-/
def natDegree (p : R[X]) : Nat :=
  (degree p).unbotD 0

/--
Definition of `leadingCoeff` / `leadingCoeff` 的定义

English:
definition leadingCoeff
  signature: (p : R[X])
  body: coeff p (natDegree p)

中文:
定义 leadingCoeff
  签名: (p : R[X])
  定义体: coeff p (natDegree p)

Depends on / 依赖: natDegree
-/
def leadingCoeff (p : R[X]) : R :=
  coeff p (natDegree p)

/--
Definition of `Monic` / `Monic` 的定义

English:
definition Monic
  signature: (p : R[X])
  body: leadingCoeff p = (1 : R)

中文:
定义 Monic
  签名: (p : R[X])
  定义体: leadingCoeff p = (1 : R)

Depends on / 依赖: leadingCoeff
-/
def Monic (p : R[X]) :=
  leadingCoeff p = (1 : R)

/--
theorem `Monic.def` / 定理 `Monic.def`

English:
theorem Monic.def
  statement: Monic p ↔ leadingCoeff p = 1
  proof: Iff.rfl

中文:
定理 Monic.def
  结论: Monic p ↔ leadingCoeff p = 1
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem Monic.def : Monic p ↔ leadingCoeff p = 1 :=
  Iff.rfl

/--
Instance `Monic.decidable` / 实例 `Monic.decidable`

English:
instance Monic.decidable
  signature: [DecidableEq R]
  body: inferInstanceAs Decidable (p.leadingCoeff = 1)

@[simp]

中文:
实例 Monic.decidable
  签名: [DecidableEq R]
  定义体: inferInstanceAs Decidable (p.leadingCoeff = 1)

@[simp]

Depends on / 依赖: Decidable, leadingCoeff, p.leadingCoeff
-/
instance Monic.decidable [DecidableEq R] : Decidable (Monic p) :=
inferInstanceAs Decidable (p.leadingCoeff = 1)

@[simp]
/--
theorem `Monic.leadingCoeff` / 定理 `Monic.leadingCoeff`

English:
theorem Monic.leadingCoeff
  given: {p : R[X]} (hp : p.Monic)
  statement: leadingCoeff p = 1
  proof: hp

中文:
定理 Monic.leadingCoeff
  条件: {p : R[X]} (hp : p.Monic)
  结论: leadingCoeff p = 1
  证明: hp
-/
theorem Monic.leadingCoeff {p : R[X]} (hp : p.Monic) : leadingCoeff p = 1 :=
  hp

/--
theorem `Monic.coeff_natDegree` / 定理 `Monic.coeff_natDegree`

English:
theorem Monic.coeff_natDegree
  given: {p : R[X]} (hp : p.Monic)
  statement: p.coeff p.natDegree = 1
  proof: hp

@[simp, grind =]

中文:
定理 Monic.coeff_natDegree
  条件: {p : R[X]} (hp : p.Monic)
  结论: p.coeff p.natDegree = 1
  证明: hp

@[simp, grind =]
-/
theorem Monic.coeff_natDegree {p : R[X]} (hp : p.Monic) : p.coeff p.natDegree = 1 :=
  hp

@[simp, grind =]
/--
theorem `degree_zero` / 定理 `degree_zero`

English:
theorem degree_zero
  statement: degree (0 : R[X]) = ⊥
  proof: rfl

@[simp, grind =]

中文:
定理 degree_zero
  结论: degree (0 : R[X]) = ⊥
  证明: rfl

@[simp, grind =]
-/
theorem degree_zero : degree (0 : R[X]) = ⊥ :=
  rfl

@[simp, grind =]
/--
theorem `natDegree_zero` / 定理 `natDegree_zero`

English:
theorem natDegree_zero
  statement: natDegree (0 : R[X]) = 0
  proof: rfl

@[simp]

中文:
定理 natDegree_zero
  结论: natDegree (0 : R[X]) = 0
  证明: rfl

@[simp]
-/
theorem natDegree_zero : natDegree (0 : R[X]) = 0 :=
  rfl

@[simp]
/--
theorem `coeff_natDegree` / 定理 `coeff_natDegree`

English:
theorem coeff_natDegree
  statement: coeff p (natDegree p) = leadingCoeff p
  proof: rfl

@[simp]

中文:
定理 coeff_natDegree
  结论: coeff p (natDegree p) = leadingCoeff p
  证明: rfl

@[simp]
-/
theorem coeff_natDegree : coeff p (natDegree p) = leadingCoeff p :=
  rfl

@[simp]
/--
theorem `degree_eq_bot` / 定理 `degree_eq_bot`

English:
theorem degree_eq_bot
  statement: degree p = ⊥ ↔ p = 0
  proof: ⟨fun h => support_eq_empty.1 (Finset.max_eq_bot.1 h), fun h => h.symm ▸ rfl⟩

中文:
定理 degree_eq_bot
  结论: degree p = ⊥ ↔ p = 0
  证明: ⟨fun h => support_eq_empty.1 (Finset.max_eq_bot.1 h), fun h => h.symm ▸ rfl⟩

Depends on / 依赖: Finset, Finset.max_eq_bot, h.symm, max_eq_bot, support_eq_empty
-/
theorem degree_eq_bot : degree p = ⊥ ↔ p = 0 :=
  ⟨fun h => support_eq_empty.1 (Finset.max_eq_bot.1 h), fun h => h.symm ▸ rfl⟩

/--
theorem `degree_ne_bot` / 定理 `degree_ne_bot`

English:
theorem degree_ne_bot
  statement: degree p != ⊥ ↔ p != 0
  proof: degree_eq_bot.not

中文:
定理 degree_ne_bot
  结论: degree p != ⊥ ↔ p != 0
  证明: degree_eq_bot.not

Depends on / 依赖: degree_eq_bot, degree_eq_bot.not
-/
theorem degree_ne_bot : degree p != ⊥ ↔ p != 0 := degree_eq_bot.not

/--
theorem `degree_eq_natDegree` / 定理 `degree_eq_natDegree`

English:
theorem degree_eq_natDegree
  given: (hp : p != 0)
  statement: degree p = (natDegree p : WithBot Nat)
  proof: by
  let ⟨n, hn⟩ := not_forall.1 (mt Option.eq_none_iff_forall_not_mem.2 (mt degree_eq_bot.1 hp))
  have hn : degree p = some n := Classical.not_not.1 hn
  rw [natDegree]; rw [hn]; rfl

中文:
定理 degree_eq_natDegree
  条件: (hp : p != 0)
  结论: degree p = (natDegree p : WithBot 自然数)
  证明: by
  let ⟨n, hn⟩ := not_forall.1 (mt Option.eq_none_iff_forall_not_mem.2 (mt degree_eq_bot.1 hp))
  have hn : degree p = some n := Classical.not_not.1 hn
  rw [natDegree]; rw [hn]; rfl

Depends on / 依赖: Classical, Classical.not_not, Option.eq_none_iff_forall_not_mem, degree, degree_eq_bot, eq_none_iff_forall_not_mem, natDegree, not_forall, not_not
-/
theorem degree_eq_natDegree (hp : p != 0) : degree p = (natDegree p : WithBot Nat) := by
  let ⟨n, hn⟩ := not_forall.1 (mt Option.eq_none_iff_forall_not_mem.2 (mt degree_eq_bot.1 hp))
  have hn : degree p = some n := Classical.not_not.1 hn
  rw [natDegree]; rw [hn]; rfl

/--
theorem `degree_eq_iff_natDegree_eq` / 定理 `degree_eq_iff_natDegree_eq`

English:
theorem degree_eq_iff_natDegree_eq
  given: {p : R[X]} {n : Nat} (hp : p != 0)
  proof: by rw [degree_eq_natDegree hp]; exact WithBot.coe_eq_coe

中文:
定理 degree_eq_iff_natDegree_eq
  条件: {p : R[X]} {n : 自然数} (hp : p != 0)
  证明: by rw [degree_eq_natDegree hp]; exact WithBot.coe_eq_coe

Depends on / 依赖: WithBot, WithBot.coe_eq_coe, coe_eq_coe, degree_eq_natDegree
-/
theorem degree_eq_iff_natDegree_eq {p : R[X]} {n : Nat} (hp : p != 0) :
    p.degree = n ↔ p.natDegree = n := by rw [degree_eq_natDegree hp]; exact WithBot.coe_eq_coe

/--
theorem `degree_eq_iff_natDegree_eq_of_pos` / 定理 `degree_eq_iff_natDegree_eq_of_pos`

English:
theorem degree_eq_iff_natDegree_eq_of_pos
  given: {p : R[X]} {n : Nat} (hn : 0 < n)
  proof: by
  obtain rfl | h := eq_or_ne p 0
  · simp [hn.ne]
  · exact degree_eq_iff_natDegree_eq h

中文:
定理 degree_eq_iff_natDegree_eq_of_pos
  条件: {p : R[X]} {n : 自然数} (hn : 0 < n)
  证明: by
  obtain rfl | h := eq_or_ne p 0
  · simp [hn.ne]
  · exact degree_eq_iff_natDegree_eq h

Depends on / 依赖: degree_eq_iff_natDegree_eq, eq_or_ne, hn.ne
-/
theorem degree_eq_iff_natDegree_eq_of_pos {p : R[X]} {n : Nat} (hn : 0 < n) :
    p.degree = n ↔ p.natDegree = n := by
  obtain rfl | h := eq_or_ne p 0
  · simp [hn.ne]
  · exact degree_eq_iff_natDegree_eq h

/--
theorem `natDegree_eq_of_degree_eq_some` / 定理 `natDegree_eq_of_degree_eq_some`

English:
theorem natDegree_eq_of_degree_eq_some
  given: {p : R[X]} {n : Nat} (h : degree p = n)
  statement: natDegree p = n
  proof: by
  rw [natDegree]; rw [h]; rw [Nat.cast_withBot]; rw [WithBot.unbotD_coe]

中文:
定理 natDegree_eq_of_degree_eq_some
  条件: {p : R[X]} {n : 自然数} (h : degree p = n)
  结论: natDegree p = n
  证明: by
  rw [natDegree]; rw [h]; rw [Nat.cast_withBot]; rw [WithBot.unbotD_coe]

Depends on / 依赖: Nat.cast_withBot, WithBot, WithBot.unbotD_coe, cast_withBot, natDegree, unbotD_coe
-/
theorem natDegree_eq_of_degree_eq_some {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n := by
  rw [natDegree]; rw [h]; rw [Nat.cast_withBot]; rw [WithBot.unbotD_coe]

/--
theorem `degree_ne_of_natDegree_ne` / 定理 `degree_ne_of_natDegree_ne`

English:
theorem degree_ne_of_natDegree_ne
  given: {n : Nat}
  statement: p.natDegree != n -> degree p != n
  proof: mt natDegree_eq_of_degree_eq_some

@[simp]

中文:
定理 degree_ne_of_natDegree_ne
  条件: {n : 自然数}
  结论: p.natDegree != n -> degree p != n
  证明: mt natDegree_eq_of_degree_eq_some

@[simp]

Depends on / 依赖: natDegree_eq_of_degree_eq_some
-/
theorem degree_ne_of_natDegree_ne {n : Nat} : p.natDegree != n -> degree p != n :=
  mt natDegree_eq_of_degree_eq_some

@[simp]
/--
theorem `degree_le_natDegree` / 定理 `degree_le_natDegree`

English:
theorem degree_le_natDegree
  statement: degree p <= natDegree p
  proof: WithBot.giUnbotDBot.gc.le_u_l _

中文:
定理 degree_le_natDegree
  结论: degree p <= natDegree p
  证明: WithBot.giUnbotDBot.gc.le_u_l _

Depends on / 依赖: WithBot, WithBot.giUnbotDBot.gc.le_u_l, giUnbotDBot, le_u_l
-/
theorem degree_le_natDegree : degree p <= natDegree p :=
  WithBot.giUnbotDBot.gc.le_u_l _

/--
theorem `natDegree_eq_of_degree_eq` / 定理 `natDegree_eq_of_degree_eq`

English:
theorem natDegree_eq_of_degree_eq
  given: [Semiring S] {q : S[X]} (h : degree p = degree q)
  proof: by unfold natDegree; rw [h]

中文:
定理 natDegree_eq_of_degree_eq
  条件: [半环 S] {q : S[X]} (h : degree p = degree q)
  证明: by unfold natDegree; rw [h]

Depends on / 依赖: natDegree
-/
theorem natDegree_eq_of_degree_eq [Semiring S] {q : S[X]} (h : degree p = degree q) :
    natDegree p = natDegree q := by unfold natDegree; rw [h]

/--
theorem `le_degree_of_ne_zero` / 定理 `le_degree_of_ne_zero`

English:
theorem le_degree_of_ne_zero
  given: (h : coeff p n != 0)
  statement: (n : WithBot Nat) <= degree p
  proof: by
  rw [Nat.cast_withBot]
  exact Finset.le_sup (mem_support_iff.2 h)

中文:
定理 le_degree_of_ne_zero
  条件: (h : coeff p n != 0)
  结论: (n : WithBot 自然数) <= degree p
  证明: by
  rw [Nat.cast_withBot]
  exact Finset.le_sup (mem_support_iff.2 h)

Depends on / 依赖: Finset, Finset.le_sup, Nat.cast_withBot, cast_withBot, le_sup, mem_support_iff
-/
theorem le_degree_of_ne_zero (h : coeff p n != 0) : (n : WithBot Nat) <= degree p := by
  rw [Nat.cast_withBot]
  exact Finset.le_sup (mem_support_iff.2 h)

/--
theorem `degree_mono` / 定理 `degree_mono`

English:
theorem degree_mono
  given: [Semiring S] {f : R[X]} {g : S[X]} (h : f.support subseteq g.support)
  proof: Finset.sup_mono h

中文:
定理 degree_mono
  条件: [半环 S] {f : R[X]} {g : S[X]} (h : f.support subseteq g.support)
  证明: Finset.sup_mono h

Depends on / 依赖: Finset, Finset.sup_mono, sup_mono
-/
theorem degree_mono [Semiring S] {f : R[X]} {g : S[X]} (h : f.support subseteq g.support) :
    f.degree <= g.degree :=
  Finset.sup_mono h

/--
theorem `degree_le_degree` / 定理 `degree_le_degree`

English:
theorem degree_le_degree
  given: (h : coeff q (natDegree p) != 0)
  statement: degree p <= degree q
  proof: by
  by_cases hp : p = 0
  · rw [hp, degree_zero]
    exact bot_le
  · rw [degree_eq_natDegree hp]
    exact le_degree_of_ne_zero h

中文:
定理 degree_le_degree
  条件: (h : coeff q (natDegree p) != 0)
  结论: degree p <= degree q
  证明: by
  by_cases hp : p = 0
  · rw [hp, degree_zero]
    exact bot_le
  · rw [degree_eq_natDegree hp]
    exact le_degree_of_ne_zero h

Depends on / 依赖: bot_le, degree_eq_natDegree, degree_zero, le_degree_of_ne_zero
-/
theorem degree_le_degree (h : coeff q (natDegree p) != 0) : degree p <= degree q := by
  by_cases hp : p = 0
  · rw [hp, degree_zero]
    exact bot_le
  · rw [degree_eq_natDegree hp]
    exact le_degree_of_ne_zero h

/--
theorem `natDegree_le_iff_degree_le` / 定理 `natDegree_le_iff_degree_le`

English:
theorem natDegree_le_iff_degree_le
  given: {n : Nat}
  statement: natDegree p <= n ↔ degree p <= n
  proof: WithBot.unbotD_le_iff (fun _ => bot_le)

中文:
定理 natDegree_le_iff_degree_le
  条件: {n : 自然数}
  结论: natDegree p <= n ↔ degree p <= n
  证明: WithBot.unbotD_le_iff (fun _ => bot_le)

Depends on / 依赖: WithBot, WithBot.unbotD_le_iff, bot_le, unbotD_le_iff
-/
theorem natDegree_le_iff_degree_le {n : Nat} : natDegree p <= n ↔ degree p <= n :=
  WithBot.unbotD_le_iff (fun _ => bot_le)

/--
theorem `natDegree_lt_iff_degree_lt` / 定理 `natDegree_lt_iff_degree_lt`

English:
theorem natDegree_lt_iff_degree_lt
  given: (hp : p != 0)
  statement: p.natDegree < n ↔ p.degree < ↑n
  proof: WithBot.unbotD_lt_iff (absurd · (degree_eq_bot.not.mpr hp))

alias ⟨degree_le_of_natDegree_le, natDegree_le_of_degree_le⟩ := natDegree_le_iff_degree_le

中文:
定理 natDegree_lt_iff_degree_lt
  条件: (hp : p != 0)
  结论: p.natDegree < n ↔ p.degree < ↑n
  证明: WithBot.unbotD_lt_iff (absurd · (degree_eq_bot.not.mpr hp))

alias ⟨degree_le_of_natDegree_le, natDegree_le_of_degree_le⟩ := natDegree_le_iff_degree_le

Depends on / 依赖: WithBot, WithBot.unbotD_lt_iff, absurd, degree_eq_bot, degree_eq_bot.not.mpr, unbotD_lt_iff
-/
theorem natDegree_lt_iff_degree_lt (hp : p != 0) : p.natDegree < n ↔ p.degree < ↑n :=
  WithBot.unbotD_lt_iff (absurd · (degree_eq_bot.not.mpr hp))

alias ⟨degree_le_of_natDegree_le, natDegree_le_of_degree_le⟩ := natDegree_le_iff_degree_le

/--
theorem `natDegree_le_natDegree` / 定理 `natDegree_le_natDegree`

English:
theorem natDegree_le_natDegree
  given: [Semiring S] {q : S[X]} (hpq : p.degree <= q.degree)
  proof: WithBot.giUnbotDBot.gc.monotone_l hpq

@[simp]

中文:
定理 natDegree_le_natDegree
  条件: [半环 S] {q : S[X]} (hpq : p.degree <= q.degree)
  证明: WithBot.giUnbotDBot.gc.monotone_l hpq

@[simp]

Depends on / 依赖: WithBot, WithBot.giUnbotDBot.gc.monotone_l, giUnbotDBot, monotone_l
-/
theorem natDegree_le_natDegree [Semiring S] {q : S[X]} (hpq : p.degree <= q.degree) :
    p.natDegree <= q.natDegree :=
  WithBot.giUnbotDBot.gc.monotone_l hpq

@[simp]
/--
theorem `degree_C` / 定理 `degree_C`

English:
theorem degree_C
  given: (ha : a != 0)
  statement: degree (C a) = (0 : WithBot Nat)
  proof: by
  rw [degree]; rw [← monomial_zero_left]; rw [support_monomial 0 ha]; rw [max_eq_sup_coe]; rw [sup_singleton]; rw [WithBot.coe_zero]

中文:
定理 degree_C
  条件: (ha : a != 0)
  结论: degree (C a) = (0 : WithBot 自然数)
  证明: by
  rw [degree]; rw [← monomial_zero_left]; rw [support_monomial 0 ha]; rw [max_eq_sup_coe]; rw [sup_singleton]; rw [WithBot.coe_zero]

Depends on / 依赖: WithBot, WithBot.coe_zero, coe_zero, degree, max_eq_sup_coe, monomial_zero_left, sup_singleton, support_monomial
-/
theorem degree_C (ha : a != 0) : degree (C a) = (0 : WithBot Nat) := by
  rw [degree]; rw [← monomial_zero_left]; rw [support_monomial 0 ha]; rw [max_eq_sup_coe]; rw [sup_singleton]; rw [WithBot.coe_zero]

/--
theorem `degree_C_le` / 定理 `degree_C_le`

English:
theorem degree_C_le
  statement: degree (C a) <= 0
  proof: by
  by_cases h : a = 0
  · rw [h, C_0]
    exact bot_le
  · rw [degree_C h]

中文:
定理 degree_C_le
  结论: degree (C a) <= 0
  证明: by
  by_cases h : a = 0
  · rw [h, C_0]
    exact bot_le
  · rw [degree_C h]

Depends on / 依赖: bot_le, degree_C
-/
theorem degree_C_le : degree (C a) <= 0 := by
  by_cases h : a = 0
  · rw [h, C_0]
    exact bot_le
  · rw [degree_C h]

/--
theorem `degree_C_lt` / 定理 `degree_C_lt`

English:
theorem degree_C_lt
  statement: degree (C a) < 1
  proof: degree_C_le.trans_lt WithBot.coe_lt_coe.mpr zero_lt_one

中文:
定理 degree_C_lt
  结论: degree (C a) < 1
  证明: degree_C_le.trans_lt WithBot.coe_lt_coe.mpr zero_lt_one

Depends on / 依赖: WithBot, WithBot.coe_lt_coe.mpr, coe_lt_coe, degree_C_le, degree_C_le.trans_lt, trans_lt, zero_lt_one
-/
theorem degree_C_lt : degree (C a) < 1 :=
degree_C_le.trans_lt WithBot.coe_lt_coe.mpr zero_lt_one

/--
theorem `degree_one_le` / 定理 `degree_one_le`

English:
theorem degree_one_le
  statement: degree (1 : R[X]) <= (0 : WithBot Nat)
  proof: by rw [← C_1]; exact degree_C_le

@[simp, grind =]

中文:
定理 degree_one_le
  结论: degree (1 : R[X]) <= (0 : WithBot 自然数)
  证明: by rw [← C_1]; exact degree_C_le

@[simp, grind =]

Depends on / 依赖: degree_C_le
-/
theorem degree_one_le : degree (1 : R[X]) <= (0 : WithBot Nat) := by rw [← C_1]; exact degree_C_le

@[simp, grind =]
/--
theorem `natDegree_C` / 定理 `natDegree_C`

English:
theorem natDegree_C
  given: (a : R)
  statement: natDegree (C a) = 0
  proof: by
  by_cases ha : a = 0
  · have : C a = 0 := by rw [ha, C_0]
    rw [natDegree]; rw [degree_eq_bot.2 this]; rw [WithBot.unbotD_bot]
  · rw [natDegree, degree_C ha, WithBot.unbotD_zero]

@[simp, grind =]

中文:
定理 natDegree_C
  条件: (a : R)
  结论: natDegree (C a) = 0
  证明: by
  by_cases ha : a = 0
  · have : C a = 0 := by rw [ha, C_0]
    rw [natDegree]; rw [degree_eq_bot.2 this]; rw [WithBot.unbotD_bot]
  · rw [natDegree, degree_C ha, WithBot.unbotD_zero]

@[simp, grind =]

Depends on / 依赖: WithBot, WithBot.unbotD_bot, WithBot.unbotD_zero, degree_C, degree_eq_bot, natDegree, unbotD_bot, unbotD_zero
-/
theorem natDegree_C (a : R) : natDegree (C a) = 0 := by
  by_cases ha : a = 0
  · have : C a = 0 := by rw [ha, C_0]
    rw [natDegree]; rw [degree_eq_bot.2 this]; rw [WithBot.unbotD_bot]
  · rw [natDegree, degree_C ha, WithBot.unbotD_zero]

@[simp, grind =]
/--
theorem `natDegree_one` / 定理 `natDegree_one`

English:
theorem natDegree_one
  statement: natDegree (1 : R[X]) = 0
  proof: natDegree_C 1

@[simp, grind =]

中文:
定理 natDegree_one
  结论: natDegree (1 : R[X]) = 0
  证明: natDegree_C 1

@[simp, grind =]

Depends on / 依赖: natDegree_C
-/
theorem natDegree_one : natDegree (1 : R[X]) = 0 :=
  natDegree_C 1

@[simp, grind =]
/--
theorem `natDegree_natCast` / 定理 `natDegree_natCast`

English:
theorem natDegree_natCast
  given: (n : Nat)
  statement: natDegree (n : R[X]) = 0
  proof: by
  simp only [← C_eq_natCast, natDegree_C]

@[simp]

中文:
定理 natDegree_natCast
  条件: (n : 自然数)
  结论: natDegree (n : R[X]) = 0
  证明: by
  simp only [← C_eq_natCast, natDegree_C]

@[simp]

Depends on / 依赖: C_eq_natCast, natDegree_C
-/
theorem natDegree_natCast (n : Nat) : natDegree (n : R[X]) = 0 := by
  simp only [← C_eq_natCast, natDegree_C]

@[simp]
/--
theorem `natDegree_ofNat` / 定理 `natDegree_ofNat`

English:
theorem natDegree_ofNat
  given: (n : Nat) [Nat.AtLeastTwo n]
  proof: natDegree_natCast _

中文:
定理 natDegree_of自然数
  条件: (n : 自然数) [自然数.AtLeastTwo n]
  证明: natDegree_natCast _

Depends on / 依赖: natDegree_natCast
-/
theorem natDegree_ofNat (n : Nat) [Nat.AtLeastTwo n] :
    natDegree (ofNat(n) : R[X]) = 0 :=
  natDegree_natCast _

/--
theorem `degree_natCast_le` / 定理 `degree_natCast_le`

English:
theorem degree_natCast_le
  given: (n : Nat)
  statement: degree (n : R[X]) <= 0
  proof: degree_le_of_natDegree_le (by simp)

@[simp]

中文:
定理 degree_natCast_le
  条件: (n : 自然数)
  结论: degree (n : R[X]) <= 0
  证明: degree_le_of_natDegree_le (by simp)

@[simp]

Depends on / 依赖: degree_le_of_natDegree_le
-/
theorem degree_natCast_le (n : Nat) : degree (n : R[X]) <= 0 := degree_le_of_natDegree_le (by simp)

@[simp]
/--
theorem `degree_monomial` / 定理 `degree_monomial`

English:
theorem degree_monomial
  given: (n : Nat) (ha : a != 0)
  statement: degree (monomial n a) = n
  proof: by
  rw [degree]; rw [support_monomial n ha]; rw [max_singleton]; rw [Nat.cast_withBot]

@[simp]

中文:
定理 degree_monomial
  条件: (n : 自然数) (ha : a != 0)
  结论: degree (monomial n a) = n
  证明: by
  rw [degree]; rw [support_monomial n ha]; rw [max_singleton]; rw [Nat.cast_withBot]

@[simp]

Depends on / 依赖: Nat.cast_withBot, cast_withBot, degree, max_singleton, support_monomial
-/
theorem degree_monomial (n : Nat) (ha : a != 0) : degree (monomial n a) = n := by
  rw [degree]; rw [support_monomial n ha]; rw [max_singleton]; rw [Nat.cast_withBot]

@[simp]
/--
theorem `degree_C_mul_X_pow` / 定理 `degree_C_mul_X_pow`

English:
theorem degree_C_mul_X_pow
  given: (n : Nat) (ha : a != 0)
  statement: degree (C a * X ^ n) = n
  proof: by
  rw [C_mul_X_pow_eq_monomial]; rw [degree_monomial n ha]

中文:
定理 degree_C_mul_X_pow
  条件: (n : 自然数) (ha : a != 0)
  结论: degree (C a * X ^ n) = n
  证明: by
  rw [C_mul_X_pow_eq_monomial]; rw [degree_monomial n ha]

Depends on / 依赖: C_mul_X_pow_eq_monomial, degree_monomial
-/
theorem degree_C_mul_X_pow (n : Nat) (ha : a != 0) : degree (C a * X ^ n) = n := by
  rw [C_mul_X_pow_eq_monomial]; rw [degree_monomial n ha]

/--
theorem `degree_C_mul_X` / 定理 `degree_C_mul_X`

English:
theorem degree_C_mul_X
  given: (ha : a != 0)
  statement: degree (C a * X) = 1
  proof: by
  simpa only [pow_one] using! degree_C_mul_X_pow 1 ha

中文:
定理 degree_C_mul_X
  条件: (ha : a != 0)
  结论: degree (C a * X) = 1
  证明: by
  simpa only [pow_one] using! degree_C_mul_X_pow 1 ha

Depends on / 依赖: degree_C_mul_X_pow, pow_one
-/
theorem degree_C_mul_X (ha : a != 0) : degree (C a * X) = 1 := by
  simpa only [pow_one] using! degree_C_mul_X_pow 1 ha

/--
theorem `degree_monomial_le` / 定理 `degree_monomial_le`

English:
theorem degree_monomial_le
  given: (n : Nat) (a : R)
  statement: degree (monomial n a) <= n
  proof: letI := Classical.decEq R
  if h : a = 0 then by rw [h, (monomial n).map_zero, degree_zero]; exact bot_le
  else le_of_eq (degree_monomial n h)

中文:
定理 degree_monomial_le
  条件: (n : 自然数) (a : R)
  结论: degree (monomial n a) <= n
  证明: letI := Classical.decEq R
  if h : a = 0 then by rw [h, (monomial n).map_zero, degree_zero]; exact bot_le
  else le_of_eq (degree_monomial n h)

Depends on / 依赖: Classical, Classical.decEq, bot_le, degree_monomial, degree_zero, le_of_eq, map_zero, monomial
-/
theorem degree_monomial_le (n : Nat) (a : R) : degree (monomial n a) <= n :=
  letI := Classical.decEq R
  if h : a = 0 then by rw [h, (monomial n).map_zero, degree_zero]; exact bot_le
  else le_of_eq (degree_monomial n h)

/--
theorem `degree_C_mul_X_pow_le` / 定理 `degree_C_mul_X_pow_le`

English:
theorem degree_C_mul_X_pow_le
  given: (n : Nat) (a : R)
  statement: degree (C a * X ^ n) <= n
  proof: by
  rw [C_mul_X_pow_eq_monomial]
  apply degree_monomial_le

中文:
定理 degree_C_mul_X_pow_le
  条件: (n : 自然数) (a : R)
  结论: degree (C a * X ^ n) <= n
  证明: by
  rw [C_mul_X_pow_eq_monomial]
  apply degree_monomial_le

Depends on / 依赖: C_mul_X_pow_eq_monomial, degree_monomial_le
-/
theorem degree_C_mul_X_pow_le (n : Nat) (a : R) : degree (C a * X ^ n) <= n := by
  rw [C_mul_X_pow_eq_monomial]
  apply degree_monomial_le

/--
theorem `degree_C_mul_X_le` / 定理 `degree_C_mul_X_le`

English:
theorem degree_C_mul_X_le
  given: (a : R)
  statement: degree (C a * X) <= 1
  proof: by
  simpa only [pow_one] using! degree_C_mul_X_pow_le 1 a

@[simp, grind =]

中文:
定理 degree_C_mul_X_le
  条件: (a : R)
  结论: degree (C a * X) <= 1
  证明: by
  simpa only [pow_one] using! degree_C_mul_X_pow_le 1 a

@[simp, grind =]

Depends on / 依赖: degree_C_mul_X_pow_le, pow_one
-/
theorem degree_C_mul_X_le (a : R) : degree (C a * X) <= 1 := by
  simpa only [pow_one] using! degree_C_mul_X_pow_le 1 a

@[simp, grind =]
/--
theorem `natDegree_C_mul_X_pow` / 定理 `natDegree_C_mul_X_pow`

English:
theorem natDegree_C_mul_X_pow
  given: (n : Nat) (a : R) (ha : a != 0)
  statement: natDegree (C a * X ^ n) = n
  proof: natDegree_eq_of_degree_eq_some (degree_C_mul_X_pow n ha)

@[simp, grind =]

中文:
定理 natDegree_C_mul_X_pow
  条件: (n : 自然数) (a : R) (ha : a != 0)
  结论: natDegree (C a * X ^ n) = n
  证明: natDegree_eq_of_degree_eq_some (degree_C_mul_X_pow n ha)

@[simp, grind =]

Depends on / 依赖: degree_C_mul_X_pow, natDegree_eq_of_degree_eq_some
-/
theorem natDegree_C_mul_X_pow (n : Nat) (a : R) (ha : a != 0) : natDegree (C a * X ^ n) = n :=
  natDegree_eq_of_degree_eq_some (degree_C_mul_X_pow n ha)

@[simp, grind =]
/--
theorem `natDegree_C_mul_X` / 定理 `natDegree_C_mul_X`

English:
theorem natDegree_C_mul_X
  given: (a : R) (ha : a != 0)
  statement: natDegree (C a * X) = 1
  proof: by
  simpa only [pow_one] using natDegree_C_mul_X_pow 1 a ha

@[simp]

中文:
定理 natDegree_C_mul_X
  条件: (a : R) (ha : a != 0)
  结论: natDegree (C a * X) = 1
  证明: by
  simpa only [pow_one] using natDegree_C_mul_X_pow 1 a ha

@[simp]

Depends on / 依赖: natDegree_C_mul_X_pow, pow_one
-/
theorem natDegree_C_mul_X (a : R) (ha : a != 0) : natDegree (C a * X) = 1 := by
  simpa only [pow_one] using natDegree_C_mul_X_pow 1 a ha

@[simp]
/--
theorem `natDegree_monomial` / 定理 `natDegree_monomial`

English:
theorem natDegree_monomial
  given: [DecidableEq R] (i : Nat) (r : R)
  proof: by
  split_ifs with hr
  · simp [hr]
  · rw [← C_mul_X_pow_eq_monomial, natDegree_C_mul_X_pow i r hr]

中文:
定理 natDegree_monomial
  条件: [DecidableEq R] (i : 自然数) (r : R)
  证明: by
  split_ifs with hr
  · simp [hr]
  · rw [← C_mul_X_pow_eq_monomial, natDegree_C_mul_X_pow i r hr]

Depends on / 依赖: C_mul_X_pow_eq_monomial, natDegree_C_mul_X_pow, split_ifs
-/
theorem natDegree_monomial [DecidableEq R] (i : Nat) (r : R) :
    natDegree (monomial i r) = if r = 0 then 0 else i := by
  split_ifs with hr
  · simp [hr]
  · rw [← C_mul_X_pow_eq_monomial, natDegree_C_mul_X_pow i r hr]

/--
theorem `natDegree_monomial_le` / 定理 `natDegree_monomial_le`

English:
theorem natDegree_monomial_le
  given: (a : R) {m : Nat}
  statement: (monomial m a).natDegree <= m
  proof: by
  classical
  rw [Polynomial.natDegree_monomial]
  split_ifs
  exacts [Nat.zero_le _, le_rfl]

中文:
定理 natDegree_monomial_le
  条件: (a : R) {m : 自然数}
  结论: (monomial m a).natDegree <= m
  证明: by
  classical
  rw [Polynomial.natDegree_monomial]
  split_ifs
  exacts [Nat.zero_le _, le_rfl]

Depends on / 依赖: Nat.zero_le, Polynomial, Polynomial.natDegree_monomial, classical, exacts, le_rfl, natDegree_monomial, split_ifs, zero_le
-/
theorem natDegree_monomial_le (a : R) {m : Nat} : (monomial m a).natDegree <= m := by
  classical
  rw [Polynomial.natDegree_monomial]
  split_ifs
  exacts [Nat.zero_le _, le_rfl]

/--
theorem `natDegree_monomial_eq` / 定理 `natDegree_monomial_eq`

English:
theorem natDegree_monomial_eq
  given: (i : Nat) {r : R} (r0 : r != 0)
  statement: (monomial i r).natDegree = i
  proof: letI := Classical.decEq R
  Eq.trans (natDegree_monomial _ _) (if_neg r0)

中文:
定理 natDegree_monomial_eq
  条件: (i : 自然数) {r : R} (r0 : r != 0)
  结论: (monomial i r).natDegree = i
  证明: letI := Classical.decEq R
  Eq.trans (natDegree_monomial _ _) (if_neg r0)

Depends on / 依赖: Classical, Classical.decEq, Eq.trans, if_neg, natDegree_monomial
-/
theorem natDegree_monomial_eq (i : Nat) {r : R} (r0 : r != 0) : (monomial i r).natDegree = i :=
  letI := Classical.decEq R
  Eq.trans (natDegree_monomial _ _) (if_neg r0)

/--
theorem `coeff_ne_zero_of_eq_degree` / 定理 `coeff_ne_zero_of_eq_degree`

English:
theorem coeff_ne_zero_of_eq_degree
  given: (hn : degree p = n)
  statement: coeff p n != 0
  proof: fun h =>
  mem_support_iff.mp (mem_of_max hn) h

中文:
定理 coeff_ne_zero_of_eq_degree
  条件: (hn : degree p = n)
  结论: coeff p n != 0
  证明: fun h =>
  mem_support_iff.mp (mem_of_max hn) h
-/
theorem coeff_ne_zero_of_eq_degree (hn : degree p = n) : coeff p n != 0 := fun h =>
  mem_support_iff.mp (mem_of_max hn) h

/--
theorem `degree_X_pow_le` / 定理 `degree_X_pow_le`

English:
theorem degree_X_pow_le
  given: (n : Nat)
  statement: degree (X ^ n : R[X]) <= n
  proof: by
  simpa only [C_1, one_mul] using degree_C_mul_X_pow_le n (1 : R)

中文:
定理 degree_X_pow_le
  条件: (n : 自然数)
  结论: degree (X ^ n : R[X]) <= n
  证明: by
  simpa only [C_1, one_mul] using degree_C_mul_X_pow_le n (1 : R)

Depends on / 依赖: degree_C_mul_X_pow_le, one_mul
-/
theorem degree_X_pow_le (n : Nat) : degree (X ^ n : R[X]) <= n := by
  simpa only [C_1, one_mul] using degree_C_mul_X_pow_le n (1 : R)

/--
theorem `degree_X_le` / 定理 `degree_X_le`

English:
theorem degree_X_le
  statement: degree (X : R[X]) <= 1
  proof: degree_monomial_le _ _

中文:
定理 degree_X_le
  结论: degree (X : R[X]) <= 1
  证明: degree_monomial_le _ _

Depends on / 依赖: degree_monomial_le
-/
theorem degree_X_le : degree (X : R[X]) <= 1 :=
  degree_monomial_le _ _

/--
theorem `natDegree_X_le` / 定理 `natDegree_X_le`

English:
theorem natDegree_X_le
  statement: (X : R[X]).natDegree <= 1
  proof: natDegree_le_of_degree_le degree_X_le

中文:
定理 natDegree_X_le
  结论: (X : R[X]).natDegree <= 1
  证明: natDegree_le_of_degree_le degree_X_le

Depends on / 依赖: degree_X_le, natDegree_le_of_degree_le
-/
theorem natDegree_X_le : (X : R[X]).natDegree <= 1 :=
  natDegree_le_of_degree_le degree_X_le

/--
theorem `withBotSucc_degree_eq_natDegree_add_one` / 定理 `withBotSucc_degree_eq_natDegree_add_one`

English:
theorem withBotSucc_degree_eq_natDegree_add_one
  given: (h : p != 0)
  statement: p.degree.succ = p.natDegree + 1
  proof: by
  rw [degree_eq_natDegree h]
  exact WithBot.succ_coe p.natDegree

中文:
定理 withBotSucc_degree_eq_natDegree_add_one
  条件: (h : p != 0)
  结论: p.degree.succ = p.natDegree + 1
  证明: by
  rw [degree_eq_natDegree h]
  exact WithBot.succ_coe p.natDegree

Depends on / 依赖: WithBot, WithBot.succ_coe, degree_eq_natDegree, natDegree, p.natDegree, succ_coe
-/
theorem withBotSucc_degree_eq_natDegree_add_one (h : p != 0) : p.degree.succ = p.natDegree + 1 := by
  rw [degree_eq_natDegree h]
  exact WithBot.succ_coe p.natDegree

end Semiring

section NonzeroSemiring

variable [Semiring R] [Nontrivial R] {p q : R[X]}

@[simp]
/--
theorem `degree_one` / 定理 `degree_one`

English:
theorem degree_one
  statement: degree (1 : R[X]) = (0 : WithBot Nat)
  proof: degree_C one_ne_zero

@[simp]

中文:
定理 degree_one
  结论: degree (1 : R[X]) = (0 : WithBot 自然数)
  证明: degree_C one_ne_zero

@[simp]

Depends on / 依赖: degree_C, one_ne_zero
-/
theorem degree_one : degree (1 : R[X]) = (0 : WithBot Nat) :=
  degree_C one_ne_zero

@[simp]
/--
theorem `degree_X` / 定理 `degree_X`

English:
theorem degree_X
  statement: degree (X : R[X]) = 1
  proof: degree_monomial _ one_ne_zero

@[simp]

中文:
定理 degree_X
  结论: degree (X : R[X]) = 1
  证明: degree_monomial _ one_ne_zero

@[simp]

Depends on / 依赖: degree_monomial, one_ne_zero
-/
theorem degree_X : degree (X : R[X]) = 1 :=
  degree_monomial _ one_ne_zero

@[simp]
/--
theorem `natDegree_X` / 定理 `natDegree_X`

English:
theorem natDegree_X
  statement: (X : R[X]).natDegree = 1
  proof: natDegree_eq_of_degree_eq_some degree_X

中文:
定理 natDegree_X
  结论: (X : R[X]).natDegree = 1
  证明: natDegree_eq_of_degree_eq_some degree_X

Depends on / 依赖: degree_X, natDegree_eq_of_degree_eq_some
-/
theorem natDegree_X : (X : R[X]).natDegree = 1 :=
  natDegree_eq_of_degree_eq_some degree_X

end NonzeroSemiring

section Ring

variable [Ring R]

@[simp]
/--
theorem `degree_neg` / 定理 `degree_neg`

English:
theorem degree_neg
  given: (p : R[X])
  statement: degree (-p) = degree p
  proof: by unfold degree; rw [support_neg]

中文:
定理 degree_neg
  条件: (p : R[X])
  结论: degree (-p) = degree p
  证明: by unfold degree; rw [support_neg]

Depends on / 依赖: degree, support_neg
-/
theorem degree_neg (p : R[X]) : degree (-p) = degree p := by unfold degree; rw [support_neg]

/--
theorem `degree_neg_le_of_le` / 定理 `degree_neg_le_of_le`

English:
theorem degree_neg_le_of_le
  given: {a : WithBot Nat} {p : R[X]} (hp : degree p <= a)
  statement: degree (-p) <= a
  proof: p.degree_neg.le.trans hp

@[simp]

中文:
定理 degree_neg_le_of_le
  条件: {a : WithBot 自然数} {p : R[X]} (hp : degree p <= a)
  结论: degree (-p) <= a
  证明: p.degree_neg.le.trans hp

@[simp]

Depends on / 依赖: degree_neg, p.degree_neg.le.trans
-/
theorem degree_neg_le_of_le {a : WithBot Nat} {p : R[X]} (hp : degree p <= a) : degree (-p) <= a :=
  p.degree_neg.le.trans hp

@[simp]
/--
theorem `natDegree_neg` / 定理 `natDegree_neg`

English:
theorem natDegree_neg
  given: (p : R[X])
  statement: natDegree (-p) = natDegree p
  proof: by simp [natDegree]

中文:
定理 natDegree_neg
  条件: (p : R[X])
  结论: natDegree (-p) = natDegree p
  证明: by simp [natDegree]

Depends on / 依赖: natDegree
-/
theorem natDegree_neg (p : R[X]) : natDegree (-p) = natDegree p := by simp [natDegree]

/--
theorem `natDegree_neg_le_of_le` / 定理 `natDegree_neg_le_of_le`

English:
theorem natDegree_neg_le_of_le
  given: {p : R[X]} (hp : natDegree p <= m)
  statement: natDegree (-p) <= m
  proof: (natDegree_neg p).le.trans hp

@[simp]

中文:
定理 natDegree_neg_le_of_le
  条件: {p : R[X]} (hp : natDegree p <= m)
  结论: natDegree (-p) <= m
  证明: (natDegree_neg p).le.trans hp

@[simp]

Depends on / 依赖: le.trans, natDegree_neg
-/
theorem natDegree_neg_le_of_le {p : R[X]} (hp : natDegree p <= m) : natDegree (-p) <= m :=
  (natDegree_neg p).le.trans hp

@[simp]
/--
theorem `natDegree_intCast` / 定理 `natDegree_intCast`

English:
theorem natDegree_intCast
  given: (n : Int)
  statement: natDegree (n : R[X]) = 0
  proof: by
  rw [← C_eq_intCast]; rw [natDegree_C]

中文:
定理 natDegree_intCast
  条件: (n : 整数)
  结论: natDegree (n : R[X]) = 0
  证明: by
  rw [← C_eq_intCast]; rw [natDegree_C]

Depends on / 依赖: C_eq_intCast, natDegree_C
-/
theorem natDegree_intCast (n : Int) : natDegree (n : R[X]) = 0 := by
  rw [← C_eq_intCast]; rw [natDegree_C]

/--
theorem `degree_intCast_le` / 定理 `degree_intCast_le`

English:
theorem degree_intCast_le
  given: (n : Int)
  statement: degree (n : R[X]) <= 0
  proof: degree_le_of_natDegree_le (by simp)

@[simp]

中文:
定理 degree_intCast_le
  条件: (n : 整数)
  结论: degree (n : R[X]) <= 0
  证明: degree_le_of_natDegree_le (by simp)

@[simp]

Depends on / 依赖: degree_le_of_natDegree_le
-/
theorem degree_intCast_le (n : Int) : degree (n : R[X]) <= 0 := degree_le_of_natDegree_le (by simp)

@[simp]
/--
theorem `leadingCoeff_neg` / 定理 `leadingCoeff_neg`

English:
theorem leadingCoeff_neg
  given: (p : R[X])
  statement: (-p).leadingCoeff = -p.leadingCoeff
  proof: by
  rw [leadingCoeff]; rw [leadingCoeff]; rw [natDegree_neg]; rw [coeff_neg]

中文:
定理 leadingCoeff_neg
  条件: (p : R[X])
  结论: (-p).leadingCoeff = -p.leadingCoeff
  证明: by
  rw [leadingCoeff]; rw [leadingCoeff]; rw [natDegree_neg]; rw [coeff_neg]

Depends on / 依赖: coeff_neg, leadingCoeff, natDegree_neg
-/
theorem leadingCoeff_neg (p : R[X]) : (-p).leadingCoeff = -p.leadingCoeff := by
  rw [leadingCoeff]; rw [leadingCoeff]; rw [natDegree_neg]; rw [coeff_neg]

end Ring

section Semiring

variable [Semiring R] {p : R[X]}

/--
Definition of `nextCoeff` / `nextCoeff` 的定义

English:
definition nextCoeff
  signature: (p : R[X])
  body: if p.natDegree = 0 then 0 else p.coeff (p.natDegree - 1)

中文:
定义 nextCoeff
  签名: (p : R[X])
  定义体: if p.natDegree = 0 then 0 else p.coeff (p.natDegree - 1)

Depends on / 依赖: natDegree, p.coeff, p.natDegree
-/
def nextCoeff (p : R[X]) : R :=
  if p.natDegree = 0 then 0 else p.coeff (p.natDegree - 1)

/--
lemma `nextCoeff_eq_zero` / 引理 `nextCoeff_eq_zero`

English:
lemma nextCoeff_eq_zero
  proof: by
  simp [nextCoeff, or_iff_not_imp_left, pos_iff_ne_zero]; simp_all

中文:
引理 nextCoeff_eq_zero
  证明: by
  simp [nextCoeff, or_iff_not_imp_left, pos_iff_ne_zero]; simp_all

Depends on / 依赖: nextCoeff, or_iff_not_imp_left, pos_iff_ne_zero
-/
lemma nextCoeff_eq_zero :
    p.nextCoeff = 0 ↔ p.natDegree = 0 ∨ 0 < p.natDegree ∧ p.coeff (p.natDegree - 1) = 0 := by
  simp [nextCoeff, or_iff_not_imp_left, pos_iff_ne_zero]; simp_all

/--
lemma `nextCoeff_ne_zero` / 引理 `nextCoeff_ne_zero`

English:
lemma nextCoeff_ne_zero
  statement: p.nextCoeff != 0 ↔ p.natDegree != 0 ∧ p.coeff (p.natDegree - 1) != 0
  proof: by
  simp [nextCoeff]

@[simp]

中文:
引理 nextCoeff_ne_zero
  结论: p.nextCoeff != 0 ↔ p.natDegree != 0 ∧ p.coeff (p.natDegree - 1) != 0
  证明: by
  simp [nextCoeff]

@[simp]

Depends on / 依赖: nextCoeff
-/
lemma nextCoeff_ne_zero : p.nextCoeff != 0 ↔ p.natDegree != 0 ∧ p.coeff (p.natDegree - 1) != 0 := by
  simp [nextCoeff]

@[simp]
/--
theorem `nextCoeff_C_eq_zero` / 定理 `nextCoeff_C_eq_zero`

English:
theorem nextCoeff_C_eq_zero
  given: (c : R)
  statement: nextCoeff (C c) = 0
  proof: by
  rw [nextCoeff]
  simp

中文:
定理 nextCoeff_C_eq_zero
  条件: (c : R)
  结论: nextCoeff (C c) = 0
  证明: by
  rw [nextCoeff]
  simp

Depends on / 依赖: nextCoeff
-/
theorem nextCoeff_C_eq_zero (c : R) : nextCoeff (C c) = 0 := by
  rw [nextCoeff]
  simp

/--
theorem `nextCoeff_of_natDegree_pos` / 定理 `nextCoeff_of_natDegree_pos`

English:
theorem nextCoeff_of_natDegree_pos
  given: (hp : 0 < p.natDegree)
  proof: by
  rw [nextCoeff]; rw [if_neg]
  contrapose! hp
  simpa

中文:
定理 nextCoeff_of_natDegree_pos
  条件: (hp : 0 < p.natDegree)
  证明: by
  rw [nextCoeff]; rw [if_neg]
  contrapose! hp
  simpa

Depends on / 依赖: contrapose, if_neg, nextCoeff
-/
theorem nextCoeff_of_natDegree_pos (hp : 0 < p.natDegree) :
    nextCoeff p = p.coeff (p.natDegree - 1) := by
  rw [nextCoeff]; rw [if_neg]
  contrapose! hp
  simpa

variable {p q : R[X]} {ι : Type*}

/--
theorem `degree_add_le` / 定理 `degree_add_le`

English:
theorem degree_add_le
  given: (p q : R[X])
  statement: degree (p + q) <= max (degree p) (degree q)
  proof: by
  simpa only [degree, ← support_toFinsupp, toFinsupp_add]
    using! AddMonoidAlgebra.sup_support_coeff_add_le _ _ _

中文:
定理 degree_add_le
  条件: (p q : R[X])
  结论: degree (p + q) <= 最大值 (degree p) (degree q)
  证明: by
  simpa only [degree, ← support_toFinsupp, toFinsupp_add]
    using! AddMonoidAlgebra.sup_support_coeff_add_le _ _ _

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.sup_support_coeff_add_le, degree, sup_support_coeff_add_le, support_toFinsupp, toFinsupp_add
-/
theorem degree_add_le (p q : R[X]) : degree (p + q) <= max (degree p) (degree q) := by
  simpa only [degree, ← support_toFinsupp, toFinsupp_add]
    using! AddMonoidAlgebra.sup_support_coeff_add_le _ _ _

/--
theorem `degree_add_le_of_degree_le` / 定理 `degree_add_le_of_degree_le`

English:
theorem degree_add_le_of_degree_le
  given: {p q : R[X]} {n : Nat} (hp : degree p <= n) (hq : degree q <= n)
  proof: (degree_add_le p q).trans max_le hp hq

中文:
定理 degree_add_le_of_degree_le
  条件: {p q : R[X]} {n : 自然数} (hp : degree p <= n) (hq : degree q <= n)
  证明: (degree_add_le p q).trans max_le hp hq

Depends on / 依赖: degree_add_le, max_le
-/
theorem degree_add_le_of_degree_le {p q : R[X]} {n : Nat} (hp : degree p <= n) (hq : degree q <= n) :
    degree (p + q) <= n :=
(degree_add_le p q).trans max_le hp hq

/--
theorem `degree_add_le_of_le` / 定理 `degree_add_le_of_le`

English:
theorem degree_add_le_of_le
  given: {a b : WithBot Nat} (hp : degree p <= a) (hq : degree q <= b)
  proof: (p.degree_add_le q).trans max_le_max ‹_› ‹_›

中文:
定理 degree_add_le_of_le
  条件: {a b : WithBot 自然数} (hp : degree p <= a) (hq : degree q <= b)
  证明: (p.degree_add_le q).trans max_le_max ‹_› ‹_›

Depends on / 依赖: degree_add_le, max_le_max, p.degree_add_le
-/
theorem degree_add_le_of_le {a b : WithBot Nat} (hp : degree p <= a) (hq : degree q <= b) :
    degree (p + q) <= max a b :=
(p.degree_add_le q).trans max_le_max ‹_› ‹_›

/--
theorem `natDegree_add_le` / 定理 `natDegree_add_le`

English:
theorem natDegree_add_le
  given: (p q : R[X])
  statement: natDegree (p + q) <= max (natDegree p) (natDegree q)
  proof: by
  rcases le_max_iff.1 (degree_add_le p q) with h | h <;> simp [natDegree_le_natDegree h]

中文:
定理 natDegree_add_le
  条件: (p q : R[X])
  结论: natDegree (p + q) <= 最大值 (natDegree p) (natDegree q)
  证明: by
  rcases le_max_iff.1 (degree_add_le p q) with h | h <;> simp [natDegree_le_natDegree h]

Depends on / 依赖: degree_add_le, le_max_iff, natDegree_le_natDegree
-/
theorem natDegree_add_le (p q : R[X]) : natDegree (p + q) <= max (natDegree p) (natDegree q) := by
  rcases le_max_iff.1 (degree_add_le p q) with h | h <;> simp [natDegree_le_natDegree h]

/--
theorem `natDegree_add_le_of_degree_le` / 定理 `natDegree_add_le_of_degree_le`

English:
theorem natDegree_add_le_of_degree_le
  statement: {p q : R[X]} {n : Nat} (hp : natDegree p <= n)
  proof: (natDegree_add_le p q).trans max_le hp hq

中文:
定理 natDegree_add_le_of_degree_le
  结论: {p q : R[X]} {n : 自然数} (hp : natDegree p <= n)
  证明: (natDegree_add_le p q).trans max_le hp hq

Depends on / 依赖: max_le, natDegree_add_le
-/
theorem natDegree_add_le_of_degree_le {p q : R[X]} {n : Nat} (hp : natDegree p <= n)
    (hq : natDegree q <= n) : natDegree (p + q) <= n :=
(natDegree_add_le p q).trans max_le hp hq

/--
theorem `natDegree_add_le_of_le` / 定理 `natDegree_add_le_of_le`

English:
theorem natDegree_add_le_of_le
  given: (hp : natDegree p <= m) (hq : natDegree q <= n)
  proof: (p.natDegree_add_le q).trans max_le_max ‹_› ‹_›

@[simp]

中文:
定理 natDegree_add_le_of_le
  条件: (hp : natDegree p <= m) (hq : natDegree q <= n)
  证明: (p.natDegree_add_le q).trans max_le_max ‹_› ‹_›

@[simp]

Depends on / 依赖: max_le_max, natDegree_add_le, p.natDegree_add_le
-/
theorem natDegree_add_le_of_le (hp : natDegree p <= m) (hq : natDegree q <= n) :
    natDegree (p + q) <= max m n :=
(p.natDegree_add_le q).trans max_le_max ‹_› ‹_›

@[simp]
/--
theorem `leadingCoeff_zero` / 定理 `leadingCoeff_zero`

English:
theorem leadingCoeff_zero
  statement: leadingCoeff (0 : R[X]) = 0
  proof: rfl

@[simp]

中文:
定理 leadingCoeff_zero
  结论: leadingCoeff (0 : R[X]) = 0
  证明: rfl

@[simp]
-/
theorem leadingCoeff_zero : leadingCoeff (0 : R[X]) = 0 :=
  rfl

@[simp]
/--
theorem `leadingCoeff_eq_zero` / 定理 `leadingCoeff_eq_zero`

English:
theorem leadingCoeff_eq_zero
  statement: leadingCoeff p = 0 ↔ p = 0
  proof: ⟨fun h =>
    Classical.by_contradiction fun hp =>
      mt mem_support_iff.1 (Classical.not_not.2 h) (mem_of_max (degree_eq_natDegree hp)),
    fun h => h.symm ▸ leadingCoeff_zero⟩

中文:
定理 leadingCoeff_eq_zero
  结论: leadingCoeff p = 0 ↔ p = 0
  证明: ⟨fun h =>
    Classical.by_contradiction fun hp =>
      mt mem_support_iff.1 (Classical.not_not.2 h) (mem_of_max (degree_eq_natDegree hp)),
    fun h => h.symm ▸ leadingCoeff_zero⟩

Depends on / 依赖: Classical, Classical.by_contradiction, Classical.not_not, by_contradiction, degree_eq_natDegree, h.symm, leadingCoeff_zero, mem_of_max, mem_support_iff, not_not
-/
theorem leadingCoeff_eq_zero : leadingCoeff p = 0 ↔ p = 0 :=
  ⟨fun h =>
    Classical.by_contradiction fun hp =>
      mt mem_support_iff.1 (Classical.not_not.2 h) (mem_of_max (degree_eq_natDegree hp)),
    fun h => h.symm ▸ leadingCoeff_zero⟩

/--
theorem `leadingCoeff_ne_zero` / 定理 `leadingCoeff_ne_zero`

English:
theorem leadingCoeff_ne_zero
  statement: leadingCoeff p != 0 ↔ p != 0
  proof: by rw [Ne, leadingCoeff_eq_zero]

中文:
定理 leadingCoeff_ne_zero
  结论: leadingCoeff p != 0 ↔ p != 0
  证明: by rw [Ne, leadingCoeff_eq_zero]

Depends on / 依赖: leadingCoeff_eq_zero
-/
theorem leadingCoeff_ne_zero : leadingCoeff p != 0 ↔ p != 0 := by rw [Ne, leadingCoeff_eq_zero]

/--
theorem `leadingCoeff_eq_zero_iff_deg_eq_bot` / 定理 `leadingCoeff_eq_zero_iff_deg_eq_bot`

English:
theorem leadingCoeff_eq_zero_iff_deg_eq_bot
  statement: leadingCoeff p = 0 ↔ degree p = ⊥
  proof: by
  rw [leadingCoeff_eq_zero]; rw [degree_eq_bot]

中文:
定理 leadingCoeff_eq_zero_iff_deg_eq_bot
  结论: leadingCoeff p = 0 ↔ degree p = ⊥
  证明: by
  rw [leadingCoeff_eq_zero]; rw [degree_eq_bot]

Depends on / 依赖: degree_eq_bot, leadingCoeff_eq_zero
-/
theorem leadingCoeff_eq_zero_iff_deg_eq_bot : leadingCoeff p = 0 ↔ degree p = ⊥ := by
  rw [leadingCoeff_eq_zero]; rw [degree_eq_bot]

/--
theorem `natDegree_C_mul_X_pow_le` / 定理 `natDegree_C_mul_X_pow_le`

English:
theorem natDegree_C_mul_X_pow_le
  given: (a : R) (n : Nat)
  statement: natDegree (C a * X ^ n) <= n
  proof: natDegree_le_iff_degree_le.2 degree_C_mul_X_pow_le _ _

中文:
定理 natDegree_C_mul_X_pow_le
  条件: (a : R) (n : 自然数)
  结论: natDegree (C a * X ^ n) <= n
  证明: natDegree_le_iff_degree_le.2 degree_C_mul_X_pow_le _ _

Depends on / 依赖: degree_C_mul_X_pow_le, natDegree_le_iff_degree_le
-/
theorem natDegree_C_mul_X_pow_le (a : R) (n : Nat) : natDegree (C a * X ^ n) <= n :=
natDegree_le_iff_degree_le.2 degree_C_mul_X_pow_le _ _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `degree_erase_le` / 定理 `degree_erase_le`

English:
theorem degree_erase_le
  given: (p : R[X]) (n : Nat)
  statement: degree (p.erase n) <= degree p
  proof: by
  apply sup_mono
  simpa using Finset.erase_subset ..

中文:
定理 degree_erase_le
  条件: (p : R[X]) (n : 自然数)
  结论: degree (p.erase n) <= degree p
  证明: by
  apply sup_mono
  simpa using Finset.erase_subset ..

Depends on / 依赖: Finset, Finset.erase_subset, erase_subset, sup_mono
-/
theorem degree_erase_le (p : R[X]) (n : Nat) : degree (p.erase n) <= degree p := by
  apply sup_mono
  simpa using Finset.erase_subset ..

/--
theorem `degree_erase_lt` / 定理 `degree_erase_lt`

English:
theorem degree_erase_lt
  given: (hp : p != 0)
  statement: degree (p.erase (natDegree p)) < degree p
  proof: by
  apply lt_of_le_of_ne (degree_erase_le _ _)
  rw [degree_eq_natDegree hp]; rw [degree]; rw [support_erase]
  exact fun h => notMem_erase _ _ (mem_of_max h)

中文:
定理 degree_erase_lt
  条件: (hp : p != 0)
  结论: degree (p.erase (natDegree p)) < degree p
  证明: by
  apply lt_of_le_of_ne (degree_erase_le _ _)
  rw [degree_eq_natDegree hp]; rw [degree]; rw [support_erase]
  exact fun h => notMem_erase _ _ (mem_of_max h)

Depends on / 依赖: degree, degree_eq_natDegree, degree_erase_le, lt_of_le_of_ne, mem_of_max, notMem_erase, support_erase
-/
theorem degree_erase_lt (hp : p != 0) : degree (p.erase (natDegree p)) < degree p := by
  apply lt_of_le_of_ne (degree_erase_le _ _)
  rw [degree_eq_natDegree hp]; rw [degree]; rw [support_erase]
  exact fun h => notMem_erase _ _ (mem_of_max h)

/--
theorem `degree_update_le` / 定理 `degree_update_le`

English:
theorem degree_update_le
  given: (p : R[X]) (n : Nat) (a : R)
  statement: degree (p.update n a) <= max (degree p) n
  proof: by
  classical
  rw [degree]; rw [support_update]
  split_ifs
  · exact (Finset.max_mono (erase_subset _ _)).trans (le_max_left _ _)
  · rw [max_insert, max_comm]
    exact le_rfl

中文:
定理 degree_update_le
  条件: (p : R[X]) (n : 自然数) (a : R)
  结论: degree (p.update n a) <= 最大值 (degree p) n
  证明: by
  classical
  rw [degree]; rw [support_update]
  split_ifs
  · exact (Finset.max_mono (erase_subset _ _)).trans (le_max_left _ _)
  · rw [max_insert, max_comm]
    exact le_rfl

Depends on / 依赖: Finset, Finset.max_mono, classical, degree, erase_subset, le_max_left, le_rfl, max_comm, max_insert, max_mono, split_ifs, support_update
-/
theorem degree_update_le (p : R[X]) (n : Nat) (a : R) : degree (p.update n a) <= max (degree p) n := by
  classical
  rw [degree]; rw [support_update]
  split_ifs
  · exact (Finset.max_mono (erase_subset _ _)).trans (le_max_left _ _)
  · rw [max_insert, max_comm]
    exact le_rfl

/--
theorem `degree_sum_le` / 定理 `degree_sum_le`

English:
theorem degree_sum_le
  given: (s : Finset ι) (f : ι -> R[X])
  proof: Finset.cons_induction_on s (by simp)
    fun a s has ih =>
    calc
      degree (∑ i in cons a s has, f i) <= max (degree (f a)) (degree (∑ i in s, f i)) := by
        rw [Finset.sum_cons]; exact degree_add_le _ _
      _ <= _ := by rw [sup_cons]; exact max_le_max le_rfl ih

中文:
定理 degree_sum_le
  条件: (s : 有限集 ι) (f : ι -> R[X])
  证明: Finset.cons_induction_on s (by simp)
    fun a s has ih =>
    calc
      degree (∑ i in cons a s has, f i) <= max (degree (f a)) (degree (∑ i in s, f i)) := by
        rw [Finset.sum_cons]; exact degree_add_le _ _
      _ <= _ := by rw [sup_cons]; exact max_le_max le_rfl ih

Depends on / 依赖: Finset, Finset.cons_induction_on, Finset.sum_cons, cons_induction_on, degree, degree_add_le, le_rfl, max_le_max, sum_cons, sup_cons
-/
theorem degree_sum_le (s : Finset ι) (f : ι -> R[X]) :
    degree (∑ i in s, f i) <= s.sup fun b => degree (f b) :=
  Finset.cons_induction_on s (by simp)
    fun a s has ih =>
    calc
      degree (∑ i in cons a s has, f i) <= max (degree (f a)) (degree (∑ i in s, f i)) := by
        rw [Finset.sum_cons]; exact degree_add_le _ _
      _ <= _ := by rw [sup_cons]; exact max_le_max le_rfl ih

/--
theorem `degree_mul_le` / 定理 `degree_mul_le`

English:
theorem degree_mul_le
  given: (p q : R[X])
  statement: degree (p * q) <= degree p + degree q
  proof: by
  simpa [degree, ← support_toFinsupp] using! AddMonoidAlgebra.sup_support_coeff_mul_le (by simp) ..

中文:
定理 degree_mul_le
  条件: (p q : R[X])
  结论: degree (p * q) <= degree p + degree q
  证明: by
  simpa [degree, ← support_toFinsupp] using! AddMonoidAlgebra.sup_support_coeff_mul_le (by simp) ..

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.sup_support_coeff_mul_le, degree, sup_support_coeff_mul_le, support_toFinsupp
-/
theorem degree_mul_le (p q : R[X]) : degree (p * q) <= degree p + degree q := by
  simpa [degree, ← support_toFinsupp] using! AddMonoidAlgebra.sup_support_coeff_mul_le (by simp) ..

/--
theorem `degree_mul_le_of_le` / 定理 `degree_mul_le_of_le`

English:
theorem degree_mul_le_of_le
  given: {a b : WithBot Nat} (hp : degree p <= a) (hq : degree q <= b)
  proof: by grw [degree_mul_le, hp, hq]

中文:
定理 degree_mul_le_of_le
  条件: {a b : WithBot 自然数} (hp : degree p <= a) (hq : degree q <= b)
  证明: by grw [degree_mul_le, hp, hq]

Depends on / 依赖: degree_mul_le
-/
theorem degree_mul_le_of_le {a b : WithBot Nat} (hp : degree p <= a) (hq : degree q <= b) :
    degree (p * q) <= a + b := by grw [degree_mul_le, hp, hq]

/--
theorem `degree_pow_le` / 定理 `degree_pow_le`

English:
theorem degree_pow_le
  given: (p : R[X])
  statement: forall n : Nat, degree (p ^ n) <= n • degree p

中文:
定理 degree_pow_le
  条件: (p : R[X])
  结论: 对任意 n : 自然数, degree (p ^ n) <= n • degree p
-/
theorem degree_pow_le (p : R[X]) : forall n : Nat, degree (p ^ n) <= n • degree p
  | 0 => by rw [pow_zero, zero_nsmul]; exact degree_one_le
  | n + 1 => by grw [pow_succ, succ_nsmul, degree_mul_le, degree_pow_le]

/--
theorem `degree_pow_le_of_le` / 定理 `degree_pow_le_of_le`

English:
theorem degree_pow_le_of_le
  given: {a : WithBot Nat} (b : Nat) (hp : degree p <= a)
  proof: by
  induction b with
  | zero => simp [degree_one_le]
  | succ n hn =>
      rw [Nat.cast_succ]; rw [add_mul]; rw [one_mul]; rw [pow_succ]
      exact degree_mul_le_of_le hn hp

@[simp]

中文:
定理 degree_pow_le_of_le
  条件: {a : WithBot 自然数} (b : 自然数) (hp : degree p <= a)
  证明: by
  induction b with
  | zero => simp [degree_one_le]
  | succ n hn =>
      rw [Nat.cast_succ]; rw [add_mul]; rw [one_mul]; rw [pow_succ]
      exact degree_mul_le_of_le hn hp

@[simp]

Depends on / 依赖: Nat.cast_succ, add_mul, cast_succ, degree_mul_le_of_le, degree_one_le, one_mul, pow_succ
-/
theorem degree_pow_le_of_le {a : WithBot Nat} (b : Nat) (hp : degree p <= a) :
    degree (p ^ b) <= b * a := by
  induction b with
  | zero => simp [degree_one_le]
  | succ n hn =>
      rw [Nat.cast_succ]; rw [add_mul]; rw [one_mul]; rw [pow_succ]
      exact degree_mul_le_of_le hn hp

@[simp]
/--
theorem `leadingCoeff_monomial` / 定理 `leadingCoeff_monomial`

English:
theorem leadingCoeff_monomial
  given: (a : R) (n : Nat)
  statement: leadingCoeff (monomial n a) = a
  proof: by
  classical
  by_cases ha : a = 0
  · simp only [ha, (monomial n).map_zero, leadingCoeff_zero]
  · rw [leadingCoeff, natDegree_monomial, if_neg ha, coeff_monomial]
    simp

中文:
定理 leadingCoeff_monomial
  条件: (a : R) (n : 自然数)
  结论: leadingCoeff (monomial n a) = a
  证明: by
  classical
  by_cases ha : a = 0
  · simp only [ha, (monomial n).map_zero, leadingCoeff_zero]
  · rw [leadingCoeff, natDegree_monomial, if_neg ha, coeff_monomial]
    simp

Depends on / 依赖: classical, coeff_monomial, if_neg, leadingCoeff, leadingCoeff_zero, map_zero, monomial, natDegree_monomial
-/
theorem leadingCoeff_monomial (a : R) (n : Nat) : leadingCoeff (monomial n a) = a := by
  classical
  by_cases ha : a = 0
  · simp only [ha, (monomial n).map_zero, leadingCoeff_zero]
  · rw [leadingCoeff, natDegree_monomial, if_neg ha, coeff_monomial]
    simp

/--
theorem `leadingCoeff_C_mul_X_pow` / 定理 `leadingCoeff_C_mul_X_pow`

English:
theorem leadingCoeff_C_mul_X_pow
  given: (a : R) (n : Nat)
  statement: leadingCoeff (C a * X ^ n) = a
  proof: by
  rw [C_mul_X_pow_eq_monomial]; rw [leadingCoeff_monomial]

中文:
定理 leadingCoeff_C_mul_X_pow
  条件: (a : R) (n : 自然数)
  结论: leadingCoeff (C a * X ^ n) = a
  证明: by
  rw [C_mul_X_pow_eq_monomial]; rw [leadingCoeff_monomial]

Depends on / 依赖: C_mul_X_pow_eq_monomial, leadingCoeff_monomial
-/
theorem leadingCoeff_C_mul_X_pow (a : R) (n : Nat) : leadingCoeff (C a * X ^ n) = a := by
  rw [C_mul_X_pow_eq_monomial]; rw [leadingCoeff_monomial]

/--
theorem `leadingCoeff_C_mul_X` / 定理 `leadingCoeff_C_mul_X`

English:
theorem leadingCoeff_C_mul_X
  given: (a : R)
  statement: leadingCoeff (C a * X) = a
  proof: by
  simpa only [pow_one] using leadingCoeff_C_mul_X_pow a 1

@[simp]

中文:
定理 leadingCoeff_C_mul_X
  条件: (a : R)
  结论: leadingCoeff (C a * X) = a
  证明: by
  simpa only [pow_one] using leadingCoeff_C_mul_X_pow a 1

@[simp]

Depends on / 依赖: leadingCoeff_C_mul_X_pow, pow_one
-/
theorem leadingCoeff_C_mul_X (a : R) : leadingCoeff (C a * X) = a := by
  simpa only [pow_one] using leadingCoeff_C_mul_X_pow a 1

@[simp]
/--
theorem `leadingCoeff_C` / 定理 `leadingCoeff_C`

English:
theorem leadingCoeff_C
  given: (a : R)
  statement: leadingCoeff (C a) = a
  proof: leadingCoeff_monomial a 0

中文:
定理 leadingCoeff_C
  条件: (a : R)
  结论: leadingCoeff (C a) = a
  证明: leadingCoeff_monomial a 0

Depends on / 依赖: leadingCoeff_monomial
-/
theorem leadingCoeff_C (a : R) : leadingCoeff (C a) = a :=
  leadingCoeff_monomial a 0

/--
theorem `leadingCoeff_X_pow` / 定理 `leadingCoeff_X_pow`

English:
theorem leadingCoeff_X_pow
  given: (n : Nat)
  statement: leadingCoeff ((X : R[X]) ^ n) = 1
  proof: by
  simpa only [C_1, one_mul] using leadingCoeff_C_mul_X_pow (1 : R) n

中文:
定理 leadingCoeff_X_pow
  条件: (n : 自然数)
  结论: leadingCoeff ((X : R[X]) ^ n) = 1
  证明: by
  simpa only [C_1, one_mul] using leadingCoeff_C_mul_X_pow (1 : R) n

Depends on / 依赖: leadingCoeff_C_mul_X_pow, one_mul
-/
theorem leadingCoeff_X_pow (n : Nat) : leadingCoeff ((X : R[X]) ^ n) = 1 := by
  simpa only [C_1, one_mul] using leadingCoeff_C_mul_X_pow (1 : R) n

/--
theorem `leadingCoeff_X` / 定理 `leadingCoeff_X`

English:
theorem leadingCoeff_X
  statement: leadingCoeff (X : R[X]) = 1
  proof: by
  simpa only [pow_one] using @leadingCoeff_X_pow R _ 1

@[simp]

中文:
定理 leadingCoeff_X
  结论: leadingCoeff (X : R[X]) = 1
  证明: by
  simpa only [pow_one] using @leadingCoeff_X_pow R _ 1

@[simp]

Depends on / 依赖: leadingCoeff_X_pow, pow_one
-/
theorem leadingCoeff_X : leadingCoeff (X : R[X]) = 1 := by
  simpa only [pow_one] using @leadingCoeff_X_pow R _ 1

@[simp]
/--
theorem `monic_X_pow` / 定理 `monic_X_pow`

English:
theorem monic_X_pow
  given: (n : Nat)
  statement: Monic (X ^ n : R[X])
  proof: leadingCoeff_X_pow n

@[simp]

中文:
定理 monic_X_pow
  条件: (n : 自然数)
  结论: Monic (X ^ n : R[X])
  证明: leadingCoeff_X_pow n

@[simp]

Depends on / 依赖: leadingCoeff_X_pow
-/
theorem monic_X_pow (n : Nat) : Monic (X ^ n : R[X]) :=
  leadingCoeff_X_pow n

@[simp]
/--
theorem `monic_X` / 定理 `monic_X`

English:
theorem monic_X
  statement: Monic (X : R[X])
  proof: leadingCoeff_X

中文:
定理 monic_X
  结论: Monic (X : R[X])
  证明: leadingCoeff_X

Depends on / 依赖: leadingCoeff_X
-/
theorem monic_X : Monic (X : R[X]) :=
  leadingCoeff_X

/--
theorem `leadingCoeff_one` / 定理 `leadingCoeff_one`

English:
theorem leadingCoeff_one
  statement: leadingCoeff (1 : R[X]) = 1
  proof: leadingCoeff_C 1

@[simp]

中文:
定理 leadingCoeff_one
  结论: leadingCoeff (1 : R[X]) = 1
  证明: leadingCoeff_C 1

@[simp]

Depends on / 依赖: leadingCoeff_C
-/
theorem leadingCoeff_one : leadingCoeff (1 : R[X]) = 1 :=
  leadingCoeff_C 1

@[simp]
/--
theorem `monic_one` / 定理 `monic_one`

English:
theorem monic_one
  statement: Monic (1 : R[X])
  proof: leadingCoeff_C _

中文:
定理 monic_one
  结论: Monic (1 : R[X])
  证明: leadingCoeff_C _

Depends on / 依赖: leadingCoeff_C
-/
theorem monic_one : Monic (1 : R[X]) :=
  leadingCoeff_C _

/--
theorem `Monic.ne_zero` / 定理 `Monic.ne_zero`

English:
theorem Monic.ne_zero
  given: [Nontrivial R] {p : R[X]} (hp : p.Monic)
  proof: by
  rintro rfl
  simp [Monic] at hp

中文:
定理 Monic.ne_zero
  条件: [非平凡 R] {p : R[X]} (hp : p.Monic)
  证明: by
  rintro rfl
  simp [Monic] at hp
-/
theorem Monic.ne_zero [Nontrivial R] {p : R[X]} (hp : p.Monic) :
    p != 0 := by
  rintro rfl
  simp [Monic] at hp

/--
theorem `Monic.ne_zero_of_ne` / 定理 `Monic.ne_zero_of_ne`

English:
theorem Monic.ne_zero_of_ne
  given: (h : (0 : R) != 1) {p : R[X]} (hp : p.Monic)
  statement: p != 0
  proof: by
  nontriviality R
  exact hp.ne_zero

中文:
定理 Monic.ne_zero_of_ne
  条件: (h : (0 : R) != 1) {p : R[X]} (hp : p.Monic)
  结论: p != 0
  证明: by
  nontriviality R
  exact hp.ne_zero

Depends on / 依赖: hp.ne_zero, ne_zero, nontriviality
-/
theorem Monic.ne_zero_of_ne (h : (0 : R) != 1) {p : R[X]} (hp : p.Monic) : p != 0 := by
  nontriviality R
  exact hp.ne_zero

/--
lemma `Monic.ne_zero_of_C` / 引理 `Monic.ne_zero_of_C`

English:
lemma Monic.ne_zero_of_C
  given: [Nontrivial R] {c : R} (hc : Monic (C c))
  statement: c != 0
  proof: by
  rintro rfl
  simp [Monic] at hc

中文:
引理 Monic.ne_zero_of_C
  条件: [非平凡 R] {c : R} (hc : Monic (C c))
  结论: c != 0
  证明: by
  rintro rfl
  simp [Monic] at hc
-/
lemma Monic.ne_zero_of_C [Nontrivial R] {c : R} (hc : Monic (C c)) : c != 0 := by
  rintro rfl
  simp [Monic] at hc

/--
theorem `Monic.ne_zero_of_polynomial_ne` / 定理 `Monic.ne_zero_of_polynomial_ne`

English:
theorem Monic.ne_zero_of_polynomial_ne
  given: {r} (hp : Monic p) (hne : q != r)
  statement: p != 0
  proof: haveI := Nontrivial.of_polynomial_ne hne
  hp.ne_zero

中文:
定理 Monic.ne_zero_of_polynomial_ne
  条件: {r} (hp : Monic p) (hne : q != r)
  结论: p != 0
  证明: haveI := Nontrivial.of_polynomial_ne hne
  hp.ne_zero

Depends on / 依赖: Nontrivial, Nontrivial.of_polynomial_ne, hp.ne_zero, ne_zero, of_polynomial_ne
-/
theorem Monic.ne_zero_of_polynomial_ne {r} (hp : Monic p) (hne : q != r) : p != 0 :=
  haveI := Nontrivial.of_polynomial_ne hne
  hp.ne_zero

/--
theorem `natDegree_mul_le` / 定理 `natDegree_mul_le`

English:
theorem natDegree_mul_le
  given: {p q : R[X]}
  statement: natDegree (p * q) <= natDegree p + natDegree q
  proof: by
  apply natDegree_le_of_degree_le
  apply le_trans (degree_mul_le p q)
  rw [Nat.cast_add]
  apply add_le_add <;> apply degree_le_natDegree

中文:
定理 natDegree_mul_le
  条件: {p q : R[X]}
  结论: natDegree (p * q) <= natDegree p + natDegree q
  证明: by
  apply natDegree_le_of_degree_le
  apply le_trans (degree_mul_le p q)
  rw [Nat.cast_add]
  apply add_le_add <;> apply degree_le_natDegree

Depends on / 依赖: Nat.cast_add, add_le_add, cast_add, degree_le_natDegree, degree_mul_le, le_trans, natDegree_le_of_degree_le
-/
theorem natDegree_mul_le {p q : R[X]} : natDegree (p * q) <= natDegree p + natDegree q := by
  apply natDegree_le_of_degree_le
  apply le_trans (degree_mul_le p q)
  rw [Nat.cast_add]
  apply add_le_add <;> apply degree_le_natDegree

/--
theorem `natDegree_mul_le_of_le` / 定理 `natDegree_mul_le_of_le`

English:
theorem natDegree_mul_le_of_le
  given: (hp : natDegree p <= m) (hg : natDegree q <= n)
  proof: natDegree_mul_le.trans add_le_add ‹_› ‹_›

中文:
定理 natDegree_mul_le_of_le
  条件: (hp : natDegree p <= m) (hg : natDegree q <= n)
  证明: natDegree_mul_le.trans add_le_add ‹_› ‹_›

Depends on / 依赖: add_le_add, natDegree_mul_le, natDegree_mul_le.trans
-/
theorem natDegree_mul_le_of_le (hp : natDegree p <= m) (hg : natDegree q <= n) :
    natDegree (p * q) <= m + n :=
natDegree_mul_le.trans add_le_add ‹_› ‹_›

/--
theorem `natDegree_pow_le` / 定理 `natDegree_pow_le`

English:
theorem natDegree_pow_le
  given: {p : R[X]} {n : Nat}
  statement: (p ^ n).natDegree <= n * p.natDegree
  proof: by
  induction n with
  | zero => simp
  | succ n ih => grw [pow_succ, Nat.succ_mul, natDegree_mul_le, ih]

中文:
定理 natDegree_pow_le
  条件: {p : R[X]} {n : 自然数}
  结论: (p ^ n).natDegree <= n * p.natDegree
  证明: by
  induction n with
  | zero => simp
  | succ n ih => grw [pow_succ, Nat.succ_mul, natDegree_mul_le, ih]

Depends on / 依赖: Nat.succ_mul, natDegree_mul_le, pow_succ, succ_mul
-/
theorem natDegree_pow_le {p : R[X]} {n : Nat} : (p ^ n).natDegree <= n * p.natDegree := by
  induction n with
  | zero => simp
  | succ n ih => grw [pow_succ, Nat.succ_mul, natDegree_mul_le, ih]

/--
theorem `natDegree_pow_le_of_le` / 定理 `natDegree_pow_le_of_le`

English:
theorem natDegree_pow_le_of_le
  given: (n : Nat) (hp : natDegree p <= m)
  proof: natDegree_pow_le.trans (Nat.mul_le_mul le_rfl ‹_›)

中文:
定理 natDegree_pow_le_of_le
  条件: (n : 自然数) (hp : natDegree p <= m)
  证明: natDegree_pow_le.trans (Nat.mul_le_mul le_rfl ‹_›)

Depends on / 依赖: Nat.mul_le_mul, le_rfl, mul_le_mul, natDegree_pow_le, natDegree_pow_le.trans
-/
theorem natDegree_pow_le_of_le (n : Nat) (hp : natDegree p <= m) :
    natDegree (p ^ n) <= n * m :=
  natDegree_pow_le.trans (Nat.mul_le_mul le_rfl ‹_›)

/--
theorem `natDegree_eq_zero_iff_degree_le_zero` / 定理 `natDegree_eq_zero_iff_degree_le_zero`

English:
theorem natDegree_eq_zero_iff_degree_le_zero
  statement: p.natDegree = 0 ↔ p.degree <= 0
  proof: by
  rw [← nonpos_iff_eq_zero]; rw [natDegree_le_iff_degree_le]; rw [Nat.cast_zero]

中文:
定理 natDegree_eq_zero_iff_degree_le_zero
  结论: p.natDegree = 0 ↔ p.degree <= 0
  证明: by
  rw [← nonpos_iff_eq_zero]; rw [natDegree_le_iff_degree_le]; rw [Nat.cast_zero]

Depends on / 依赖: Nat.cast_zero, cast_zero, natDegree_le_iff_degree_le, nonpos_iff_eq_zero
-/
theorem natDegree_eq_zero_iff_degree_le_zero : p.natDegree = 0 ↔ p.degree <= 0 := by
  rw [← nonpos_iff_eq_zero]; rw [natDegree_le_iff_degree_le]; rw [Nat.cast_zero]

/--
theorem `degree_zero_le` / 定理 `degree_zero_le`

English:
theorem degree_zero_le
  statement: degree (0 : R[X]) <= 0
  proof: natDegree_eq_zero_iff_degree_le_zero.mp rfl

中文:
定理 degree_zero_le
  结论: degree (0 : R[X]) <= 0
  证明: natDegree_eq_zero_iff_degree_le_zero.mp rfl

Depends on / 依赖: natDegree_eq_zero_iff_degree_le_zero, natDegree_eq_zero_iff_degree_le_zero.mp
-/
theorem degree_zero_le : degree (0 : R[X]) <= 0 := natDegree_eq_zero_iff_degree_le_zero.mp rfl

/--
theorem `degree_le_iff_coeff_zero` / 定理 `degree_le_iff_coeff_zero`

English:
theorem degree_le_iff_coeff_zero
  given: (f : R[X]) (n : WithBot Nat)
  proof: by
  simp only [degree, Finset.max, Finset.sup_le_iff, mem_support_iff, Ne, ← not_le,
    not_imp_comm, Nat.cast_withBot]

中文:
定理 degree_le_iff_coeff_zero
  条件: (f : R[X]) (n : WithBot 自然数)
  证明: by
  simp only [degree, Finset.max, Finset.sup_le_iff, mem_support_iff, Ne, ← not_le,
    not_imp_comm, Nat.cast_withBot]

Depends on / 依赖: Finset, Finset.max, Finset.sup_le_iff, Nat.cast_withBot, cast_withBot, degree, mem_support_iff, not_imp_comm, not_le, sup_le_iff
-/
theorem degree_le_iff_coeff_zero (f : R[X]) (n : WithBot Nat) :
    degree f <= n ↔ forall m : Nat, n < m -> coeff f m = 0 := by
  simp only [degree, Finset.max, Finset.sup_le_iff, mem_support_iff, Ne, ← not_le,
    not_imp_comm, Nat.cast_withBot]

/--
theorem `degree_lt_iff_coeff_zero` / 定理 `degree_lt_iff_coeff_zero`

English:
theorem degree_lt_iff_coeff_zero
  given: (f : R[X]) (n : Nat)
  proof: by
  simp only [degree, Finset.sup_lt_iff (WithBot.bot_lt_coe n), mem_support_iff,
    WithBot.coe_lt_coe, ← @not_le Nat, max_eq_sup_coe, Nat.cast_withBot, Ne, not_imp_not]

中文:
定理 degree_lt_iff_coeff_zero
  条件: (f : R[X]) (n : 自然数)
  证明: by
  simp only [degree, Finset.sup_lt_iff (WithBot.bot_lt_coe n), mem_support_iff,
    WithBot.coe_lt_coe, ← @not_le Nat, max_eq_sup_coe, Nat.cast_withBot, Ne, not_imp_not]

Depends on / 依赖: Finset, Finset.sup_lt_iff, Nat.cast_withBot, WithBot, WithBot.bot_lt_coe, WithBot.coe_lt_coe, bot_lt_coe, cast_withBot, coe_lt_coe, degree, max_eq_sup_coe, mem_support_iff, not_imp_not, not_le, sup_lt_iff
-/
theorem degree_lt_iff_coeff_zero (f : R[X]) (n : Nat) :
    degree f < n ↔ forall m : Nat, n <= m -> coeff f m = 0 := by
  simp only [degree, Finset.sup_lt_iff (WithBot.bot_lt_coe n), mem_support_iff,
    WithBot.coe_lt_coe, ← @not_le Nat, max_eq_sup_coe, Nat.cast_withBot, Ne, not_imp_not]

/--
theorem `natDegree_pos_iff_degree_pos` / 定理 `natDegree_pos_iff_degree_pos`

English:
theorem natDegree_pos_iff_degree_pos
  statement: 0 < natDegree p ↔ 0 < degree p
  proof: lt_iff_lt_of_le_iff_le natDegree_le_iff_degree_le

中文:
定理 natDegree_pos_iff_degree_pos
  结论: 0 < natDegree p ↔ 0 < degree p
  证明: lt_iff_lt_of_le_iff_le natDegree_le_iff_degree_le

Depends on / 依赖: lt_iff_lt_of_le_iff_le, natDegree_le_iff_degree_le
-/
theorem natDegree_pos_iff_degree_pos : 0 < natDegree p ↔ 0 < degree p :=
  lt_iff_lt_of_le_iff_le natDegree_le_iff_degree_le

end Semiring

section NontrivialSemiring

variable [Semiring R] [Nontrivial R] {p q : R[X]} (n : Nat)

@[simp]
/--
theorem `degree_X_pow` / 定理 `degree_X_pow`

English:
theorem degree_X_pow
  statement: degree ((X : R[X]) ^ n) = n
  proof: by
  rw [X_pow_eq_monomial]; rw [degree_monomial _ (one_ne_zero' R)]

@[simp]

中文:
定理 degree_X_pow
  结论: degree ((X : R[X]) ^ n) = n
  证明: by
  rw [X_pow_eq_monomial]; rw [degree_monomial _ (one_ne_zero' R)]

@[simp]

Depends on / 依赖: X_pow_eq_monomial, degree_monomial, one_ne_zero
-/
theorem degree_X_pow : degree ((X : R[X]) ^ n) = n := by
  rw [X_pow_eq_monomial]; rw [degree_monomial _ (one_ne_zero' R)]

@[simp]
/--
theorem `natDegree_X_pow` / 定理 `natDegree_X_pow`

English:
theorem natDegree_X_pow
  statement: natDegree ((X : R[X]) ^ n) = n
  proof: natDegree_eq_of_degree_eq_some (degree_X_pow n)

中文:
定理 natDegree_X_pow
  结论: natDegree ((X : R[X]) ^ n) = n
  证明: natDegree_eq_of_degree_eq_some (degree_X_pow n)

Depends on / 依赖: degree_X_pow, natDegree_eq_of_degree_eq_some
-/
theorem natDegree_X_pow : natDegree ((X : R[X]) ^ n) = n :=
  natDegree_eq_of_degree_eq_some (degree_X_pow n)

end NontrivialSemiring

section Ring

variable [Ring R] {p q : R[X]}

/--
theorem `degree_sub_le` / 定理 `degree_sub_le`

English:
theorem degree_sub_le
  given: (p q : R[X])
  statement: degree (p - q) <= max (degree p) (degree q)
  proof: by
  simpa only [degree_neg q] using! degree_add_le p (-q)

中文:
定理 degree_sub_le
  条件: (p q : R[X])
  结论: degree (p - q) <= 最大值 (degree p) (degree q)
  证明: by
  simpa only [degree_neg q] using! degree_add_le p (-q)

Depends on / 依赖: degree_add_le, degree_neg
-/
theorem degree_sub_le (p q : R[X]) : degree (p - q) <= max (degree p) (degree q) := by
  simpa only [degree_neg q] using! degree_add_le p (-q)

/--
theorem `degree_sub_le_of_le` / 定理 `degree_sub_le_of_le`

English:
theorem degree_sub_le_of_le
  given: {a b : WithBot Nat} (hp : degree p <= a) (hq : degree q <= b)
  proof: (p.degree_sub_le q).trans max_le_max ‹_› ‹_›

中文:
定理 degree_sub_le_of_le
  条件: {a b : WithBot 自然数} (hp : degree p <= a) (hq : degree q <= b)
  证明: (p.degree_sub_le q).trans max_le_max ‹_› ‹_›

Depends on / 依赖: degree_sub_le, max_le_max, p.degree_sub_le
-/
theorem degree_sub_le_of_le {a b : WithBot Nat} (hp : degree p <= a) (hq : degree q <= b) :
    degree (p - q) <= max a b :=
(p.degree_sub_le q).trans max_le_max ‹_› ‹_›

/--
theorem `natDegree_sub_le` / 定理 `natDegree_sub_le`

English:
theorem natDegree_sub_le
  given: (p q : R[X])
  statement: natDegree (p - q) <= max (natDegree p) (natDegree q)
  proof: by
  simpa only [← natDegree_neg q] using! natDegree_add_le p (-q)

中文:
定理 natDegree_sub_le
  条件: (p q : R[X])
  结论: natDegree (p - q) <= 最大值 (natDegree p) (natDegree q)
  证明: by
  simpa only [← natDegree_neg q] using! natDegree_add_le p (-q)

Depends on / 依赖: natDegree_add_le, natDegree_neg
-/
theorem natDegree_sub_le (p q : R[X]) : natDegree (p - q) <= max (natDegree p) (natDegree q) := by
  simpa only [← natDegree_neg q] using! natDegree_add_le p (-q)

/--
theorem `natDegree_sub_le_of_le` / 定理 `natDegree_sub_le_of_le`

English:
theorem natDegree_sub_le_of_le
  given: (hp : natDegree p <= m) (hq : natDegree q <= n)
  proof: (p.natDegree_sub_le q).trans max_le_max ‹_› ‹_›

中文:
定理 natDegree_sub_le_of_le
  条件: (hp : natDegree p <= m) (hq : natDegree q <= n)
  证明: (p.natDegree_sub_le q).trans max_le_max ‹_› ‹_›

Depends on / 依赖: max_le_max, natDegree_sub_le, p.natDegree_sub_le
-/
theorem natDegree_sub_le_of_le (hp : natDegree p <= m) (hq : natDegree q <= n) :
    natDegree (p - q) <= max m n :=
(p.natDegree_sub_le q).trans max_le_max ‹_› ‹_›

/--
theorem `degree_sub_lt_left` / 定理 `degree_sub_lt_left`

English:
theorem degree_sub_lt_left
  statement: (hd : degree p = degree q) (hp0 : p != 0)
  proof: have hp : monomial (natDegree p) (leadingCoeff p) + p.erase (natDegree p) = p :=
    monomial_add_erase _ _
  have hq : monomial (natDegree q) (leadingCoeff q) + q.erase (natDegree q) = q :=
    monomial_add_erase _ _
  have hd' : natDegree p = natDegree q := by unfold natDegree; rw [hd]
  have hq0 : q != 0 := mt degree_eq_bot.2 (hd ▸ mt degree_eq_bot.1 hp0)
  calc
    degree (p - q) = degree (erase (natDegree q) p + -erase (natDegree q) q) := by
      conv =>
        lhs
        rw [← hp]; rw [← hq]; rw [hlc]; rw [hd']; rw [add_sub_add_left_eq_sub]; rw [sub_eq_add_neg]
    _ <= max (degree (erase (natDegree q) p)) (degree (erase (natDegree q) q)) :=
      (degree_neg (erase (natDegree q) q) ▸ degree_add_le _ _)
    _ < degree p := max_lt_iff.2 ⟨hd' ▸ degree_erase_lt hp0, hd.symm ▸ degree_erase_lt hq0⟩

@[deprecated (since := "2026-06-30")] alias degree_sub_lt := degree_sub_lt_left

中文:
定理 degree_sub_lt_left
  结论: (hd : degree p = degree q) (hp0 : p != 0)
  证明: have hp : monomial (natDegree p) (leadingCoeff p) + p.erase (natDegree p) = p :=
    monomial_add_erase _ _
  have hq : monomial (natDegree q) (leadingCoeff q) + q.erase (natDegree q) = q :=
    monomial_add_erase _ _
  have hd' : natDegree p = natDegree q := by unfold natDegree; rw [hd]
  have hq0 : q != 0 := mt degree_eq_bot.2 (hd ▸ mt degree_eq_bot.1 hp0)
  calc
    degree (p - q) = degree (erase (natDegree q) p + -erase (natDegree q) q) := by
      conv =>
        lhs
        rw [← hp]; rw [← hq]; rw [hlc]; rw [hd']; rw [add_sub_add_left_eq_sub]; rw [sub_eq_add_neg]
    _ <= max (degree (erase (natDegree q) p)) (degree (erase (natDegree q) q)) :=
      (degree_neg (erase (natDegree q) q) ▸ degree_add_le _ _)
    _ < degree p := max_lt_iff.2 ⟨hd' ▸ degree_erase_lt hp0, hd.symm ▸ degree_erase_lt hq0⟩

@[deprecated (since := "2026-06-30")] alias degree_sub_lt := degree_sub_lt_left

Depends on / 依赖: add_sub_add, degree, degree_eq_bot, leadingCoeff, monomial, monomial_add_erase, natDegree, p.erase, q.erase
-/
theorem degree_sub_lt_left (hd : degree p = degree q) (hp0 : p != 0)
    (hlc : leadingCoeff p = leadingCoeff q) : degree (p - q) < degree p :=
  have hp : monomial (natDegree p) (leadingCoeff p) + p.erase (natDegree p) = p :=
    monomial_add_erase _ _
  have hq : monomial (natDegree q) (leadingCoeff q) + q.erase (natDegree q) = q :=
    monomial_add_erase _ _
  have hd' : natDegree p = natDegree q := by unfold natDegree; rw [hd]
  have hq0 : q != 0 := mt degree_eq_bot.2 (hd ▸ mt degree_eq_bot.1 hp0)
  calc
    degree (p - q) = degree (erase (natDegree q) p + -erase (natDegree q) q) := by
      conv =>
        lhs
        rw [← hp]; rw [← hq]; rw [hlc]; rw [hd']; rw [add_sub_add_left_eq_sub]; rw [sub_eq_add_neg]
    _ <= max (degree (erase (natDegree q) p)) (degree (erase (natDegree q) q)) :=
      (degree_neg (erase (natDegree q) q) ▸ degree_add_le _ _)
    _ < degree p := max_lt_iff.2 ⟨hd' ▸ degree_erase_lt hp0, hd.symm ▸ degree_erase_lt hq0⟩

@[deprecated (since := "2026-06-30")] alias degree_sub_lt := degree_sub_lt_left

/--
theorem `degree_sub_lt_right` / 定理 `degree_sub_lt_right`

English:
theorem degree_sub_lt_right
  statement: (hd : degree p = degree q) (hq0 : q != 0)
  proof: by
  rw [← degree_neg]; rw [neg_sub]
  exact degree_sub_lt_left hd.symm hq0 hlc.symm

中文:
定理 degree_sub_lt_right
  结论: (hd : degree p = degree q) (hq0 : q != 0)
  证明: by
  rw [← degree_neg]; rw [neg_sub]
  exact degree_sub_lt_left hd.symm hq0 hlc.symm

Depends on / 依赖: degree_neg, degree_sub_lt_left, hd.symm, hlc.symm, neg_sub
-/
theorem degree_sub_lt_right (hd : degree p = degree q) (hq0 : q != 0)
    (hlc : p.leadingCoeff = q.leadingCoeff) : degree (p - q) < degree q := by
  rw [← degree_neg]; rw [neg_sub]
  exact degree_sub_lt_left hd.symm hq0 hlc.symm

/--
theorem `degree_X_sub_C_le` / 定理 `degree_X_sub_C_le`

English:
theorem degree_X_sub_C_le
  given: (r : R)
  statement: (X - C r).degree <= 1
  proof: (degree_sub_le _ _).trans (max_le degree_X_le (degree_C_le.trans zero_le_one))

中文:
定理 degree_X_sub_C_le
  条件: (r : R)
  结论: (X - C r).degree <= 1
  证明: (degree_sub_le _ _).trans (max_le degree_X_le (degree_C_le.trans zero_le_one))

Depends on / 依赖: degree_C_le, degree_C_le.trans, degree_X_le, degree_sub_le, max_le, zero_le_one
-/
theorem degree_X_sub_C_le (r : R) : (X - C r).degree <= 1 :=
  (degree_sub_le _ _).trans (max_le degree_X_le (degree_C_le.trans zero_le_one))

/--
theorem `natDegree_X_sub_C_le` / 定理 `natDegree_X_sub_C_le`

English:
theorem natDegree_X_sub_C_le
  given: (r : R)
  statement: (X - C r).natDegree <= 1
  proof: natDegree_le_iff_degree_le.2 degree_X_sub_C_le r

中文:
定理 natDegree_X_sub_C_le
  条件: (r : R)
  结论: (X - C r).natDegree <= 1
  证明: natDegree_le_iff_degree_le.2 degree_X_sub_C_le r

Depends on / 依赖: degree_X_sub_C_le, natDegree_le_iff_degree_le
-/
theorem natDegree_X_sub_C_le (r : R) : (X - C r).natDegree <= 1 :=
natDegree_le_iff_degree_le.2 degree_X_sub_C_le r

end Ring

end Polynomial
