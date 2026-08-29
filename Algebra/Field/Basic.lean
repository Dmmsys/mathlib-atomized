/-
Copyright (c) 2014 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.GrindInstances
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Algebra.Ring.Invertible
public import Mathlib.Order.OrderDual
public import Mathlib.Order.Lex
public import Mathlib.Algebra.Order.Ring.Synonym
public import Mathlib.Algebra.Order.GroupWithZero.Synonym

import Mathlib.Tactic.Tauto

/-!
# Lemmas about division (semi)rings and (semi)fields

-/

@[expose] public section

open Function OrderDual Set

universe u

variable {K L : Type*}

section DivisionSemiring

variable [DivisionSemiring K] {a b c d : K}

/--
theorem `add_div` / 定理 `add_div`

English:
theorem add_div
  given: (a b c : K)
  statement: (a + b) / c = a / c + b / c
  proof: by simp_rw [div_eq_mul_inv, add_mul]

中文:
定理 add_div
  条件: (a b c : K)
  结论: (a + b) / c = a / c + b / c
  证明: by simp_rw [div_eq_mul_inv, add_mul]

Depends on / 依赖: add_mul, div_eq_mul_inv, simp_rw
-/
theorem add_div (a b c : K) : (a + b) / c = a / c + b / c := by simp_rw [div_eq_mul_inv, add_mul]

/--
theorem `same_add_div` / 定理 `same_add_div`

English:
theorem same_add_div
  given: (h : b != 0)
  statement: (b + a) / b = 1 + a / b
  proof: by rw [← div_self h, add_div]

中文:
定理 same_add_div
  条件: (h : b != 0)
  结论: (b + a) / b = 1 + a / b
  证明: by rw [← div_self h, add_div]

Depends on / 依赖: add_div, div_self
-/
theorem same_add_div (h : b != 0) : (b + a) / b = 1 + a / b := by rw [← div_self h, add_div]

/--
theorem `div_add_same` / 定理 `div_add_same`

English:
theorem div_add_same
  given: (h : b != 0)
  statement: (a + b) / b = a / b + 1
  proof: by rw [← div_self h, add_div]

中文:
定理 div_add_same
  条件: (h : b != 0)
  结论: (a + b) / b = a / b + 1
  证明: by rw [← div_self h, add_div]

Depends on / 依赖: add_div, div_self
-/
theorem div_add_same (h : b != 0) : (a + b) / b = a / b + 1 := by rw [← div_self h, add_div]

/--
theorem `one_add_div` / 定理 `one_add_div`

English:
theorem one_add_div
  given: (h : b != 0)
  statement: 1 + a / b = (b + a) / b
  proof: (same_add_div h).symm

中文:
定理 one_add_div
  条件: (h : b != 0)
  结论: 1 + a / b = (b + a) / b
  证明: (same_add_div h).symm

Depends on / 依赖: same_add_div
-/
theorem one_add_div (h : b != 0) : 1 + a / b = (b + a) / b :=
  (same_add_div h).symm

/--
theorem `div_add_one` / 定理 `div_add_one`

English:
theorem div_add_one
  given: (h : b != 0)
  statement: a / b + 1 = (a + b) / b
  proof: (div_add_same h).symm

中文:
定理 div_add_one
  条件: (h : b != 0)
  结论: a / b + 1 = (a + b) / b
  证明: (div_add_same h).symm

Depends on / 依赖: div_add_same
-/
theorem div_add_one (h : b != 0) : a / b + 1 = (a + b) / b :=
  (div_add_same h).symm

/--
theorem `inv_add_inv'` / 定理 `inv_add_inv'`

English:
theorem inv_add_inv'
  given: (ha : a != 0) (hb : b != 0)
  proof: let _ := invertibleOfNonzero ha; let _ := invertibleOfNonzero hb; invOf_add_invOf a b

中文:
定理 inv_add_inv'
  条件: (ha : a != 0) (hb : b != 0)
  证明: let _ := invertibleOfNonzero ha; let _ := invertibleOfNonzero hb; invOf_add_invOf a b

Depends on / 依赖: invOf_add_invOf, invertibleOfNonzero
-/
theorem inv_add_inv' (ha : a != 0) (hb : b != 0) :
    a⁻¹ + b⁻¹ = a⁻¹ * (a + b) * b⁻¹ :=
  let _ := invertibleOfNonzero ha; let _ := invertibleOfNonzero hb; invOf_add_invOf a b

/--
theorem `one_div_mul_add_mul_one_div_eq_one_div_add_one_div` / 定理 `one_div_mul_add_mul_one_div_eq_one_div_add_one_div`

English:
theorem one_div_mul_add_mul_one_div_eq_one_div_add_one_div
  given: (ha : a != 0) (hb : b != 0)
  proof: by
  simpa only [one_div] using (inv_add_inv' ha hb).symm

中文:
定理 one_div_mul_add_mul_one_div_eq_one_div_add_one_div
  条件: (ha : a != 0) (hb : b != 0)
  证明: by
  simpa only [one_div] using (inv_add_inv' ha hb).symm

Depends on / 依赖: inv_add_inv, one_div
-/
theorem one_div_mul_add_mul_one_div_eq_one_div_add_one_div (ha : a != 0) (hb : b != 0) :
    1 / a * (a + b) * (1 / b) = 1 / a + 1 / b := by
  simpa only [one_div] using (inv_add_inv' ha hb).symm

/--
theorem `add_div_eq_mul_add_div` / 定理 `add_div_eq_mul_add_div`

English:
theorem add_div_eq_mul_add_div
  given: (a b : K) (hc : c != 0)
  statement: a + b / c = (a * c + b) / c
  proof: (eq_div_iff_mul_eq hc).2 by rw [right_distrib, div_mul_cancel₀ _ hc]

中文:
定理 add_div_eq_mul_add_div
  条件: (a b : K) (hc : c != 0)
  结论: a + b / c = (a * c + b) / c
  证明: (eq_div_iff_mul_eq hc).2 by rw [right_distrib, div_mul_cancel₀ _ hc]

Depends on / 依赖: eq_div_iff_mul_eq, right_distrib
-/
theorem add_div_eq_mul_add_div (a b : K) (hc : c != 0) : a + b / c = (a * c + b) / c :=
(eq_div_iff_mul_eq hc).2 by rw [right_distrib, div_mul_cancel₀ _ hc]

/--
theorem `add_div'` / 定理 `add_div'`

English:
theorem add_div'
  given: (a b c : K) (hc : c != 0)
  statement: b + a / c = (b * c + a) / c
  proof: by
  rw [add_div]; rw [mul_div_cancel_right₀ _ hc]

中文:
定理 add_div'
  条件: (a b c : K) (hc : c != 0)
  结论: b + a / c = (b * c + a) / c
  证明: by
  rw [add_div]; rw [mul_div_cancel_right₀ _ hc]

Depends on / 依赖: add_div
-/
theorem add_div' (a b c : K) (hc : c != 0) : b + a / c = (b * c + a) / c := by
  rw [add_div]; rw [mul_div_cancel_right₀ _ hc]

/--
theorem `div_add'` / 定理 `div_add'`

English:
theorem div_add'
  given: (a b c : K) (hc : c != 0)
  statement: a / c + b = (a + b * c) / c
  proof: by
  rwa [add_comm, add_div', add_comm]

中文:
定理 div_add'
  条件: (a b c : K) (hc : c != 0)
  结论: a / c + b = (a + b * c) / c
  证明: by
  rwa [add_comm, add_div', add_comm]

Depends on / 依赖: add_comm, add_div
-/
theorem div_add' (a b c : K) (hc : c != 0) : a / c + b = (a + b * c) / c := by
  rwa [add_comm, add_div', add_comm]

/--
theorem `Commute.div_add_div` / 定理 `Commute.div_add_div`

English:
theorem Commute.div_add_div
  statement: (hbc : Commute b c) (hbd : Commute b d) (hb : b != 0)
  proof: by
  rw [add_div]; rw [mul_div_mul_right _ b hd]; rw [hbc.eq]; rw [hbd.eq]; rw [mul_div_mul_right c d hb]

中文:
定理 Commute.div_add_div
  结论: (hbc : Commute b c) (hbd : Commute b d) (hb : b != 0)
  证明: by
  rw [add_div]; rw [mul_div_mul_right _ b hd]; rw [hbc.eq]; rw [hbd.eq]; rw [mul_div_mul_right c d hb]
-/
protected theorem Commute.div_add_div (hbc : Commute b c) (hbd : Commute b d) (hb : b != 0)
    (hd : d != 0) : a / b + c / d = (a * d + b * c) / (b * d) := by
  rw [add_div]; rw [mul_div_mul_right _ b hd]; rw [hbc.eq]; rw [hbd.eq]; rw [mul_div_mul_right c d hb]

/--
theorem `Commute.one_div_add_one_div` / 定理 `Commute.one_div_add_one_div`

English:
theorem Commute.one_div_add_one_div
  given: (hab : Commute a b) (ha : a != 0) (hb : b != 0)
  proof: by
  rw [(Commute.one_right a).div_add_div hab ha hb]; rw [one_mul]; rw [mul_one]; rw [add_comm]

中文:
定理 Commute.one_div_add_one_div
  条件: (hab : Commute a b) (ha : a != 0) (hb : b != 0)
  证明: by
  rw [(Commute.one_right a).div_add_div hab ha hb]; rw [one_mul]; rw [mul_one]; rw [add_comm]
-/
protected theorem Commute.one_div_add_one_div (hab : Commute a b) (ha : a != 0) (hb : b != 0) :
    1 / a + 1 / b = (a + b) / (a * b) := by
  rw [(Commute.one_right a).div_add_div hab ha hb]; rw [one_mul]; rw [mul_one]; rw [add_comm]

/--
theorem `Commute.inv_add_inv` / 定理 `Commute.inv_add_inv`

English:
theorem Commute.inv_add_inv
  given: (hab : Commute a b) (ha : a != 0) (hb : b != 0)
  proof: by
  rw [inv_eq_one_div]; rw [inv_eq_one_div]; rw [hab.one_div_add_one_div ha hb]

中文:
定理 Commute.inv_add_inv
  条件: (hab : Commute a b) (ha : a != 0) (hb : b != 0)
  证明: by
  rw [inv_eq_one_div]; rw [inv_eq_one_div]; rw [hab.one_div_add_one_div ha hb]
-/
protected theorem Commute.inv_add_inv (hab : Commute a b) (ha : a != 0) (hb : b != 0) :
    a⁻¹ + b⁻¹ = (a + b) / (a * b) := by
  rw [inv_eq_one_div]; rw [inv_eq_one_div]; rw [hab.one_div_add_one_div ha hb]

variable [NeZero (2 : K)]

/--
lemma `add_self_div_two` / 引理 `add_self_div_two`

English:
lemma add_self_div_two
  given: (a : K)
  statement: (a + a) / 2 = a
  proof: by
  rw [← mul_two]; rw [mul_div_cancel_right₀ a two_ne_zero]

中文:
引理 add_self_div_two
  条件: (a : K)
  结论: (a + a) / 2 = a
  证明: by
  rw [← mul_two]; rw [mul_div_cancel_right₀ a two_ne_zero]
-/
@[simp] lemma add_self_div_two (a : K) : (a + a) / 2 = a := by
  rw [← mul_two]; rw [mul_div_cancel_right₀ a two_ne_zero]

/--
lemma `add_halves` / 引理 `add_halves`

English:
lemma add_halves
  given: (a : K)
  statement: a / 2 + a / 2 = a
  proof: by rw [← add_div, add_self_div_two]

中文:
引理 add_halves
  条件: (a : K)
  结论: a / 2 + a / 2 = a
  证明: by rw [← add_div, add_self_div_two]
-/
@[simp] lemma add_halves (a : K) : a / 2 + a / 2 = a := by rw [← add_div, add_self_div_two]

end DivisionSemiring

section DivisionRing

variable [DivisionRing K] {a b c d : K}

@[simp]
/--
theorem `div_neg_self` / 定理 `div_neg_self`

English:
theorem div_neg_self
  given: {a : K} (h : a != 0)
  statement: a / -a = -1
  proof: by rw [div_neg_eq_neg_div, div_self h]

@[simp]

中文:
定理 div_neg_self
  条件: {a : K} (h : a != 0)
  结论: a / -a = -1
  证明: by rw [div_neg_eq_neg_div, div_self h]

@[simp]

Depends on / 依赖: div_neg_eq_neg_div, div_self
-/
theorem div_neg_self {a : K} (h : a != 0) : a / -a = -1 := by rw [div_neg_eq_neg_div, div_self h]

@[simp]
/--
theorem `neg_div_self` / 定理 `neg_div_self`

English:
theorem neg_div_self
  given: {a : K} (h : a != 0)
  statement: -a / a = -1
  proof: by rw [neg_div, div_self h]

中文:
定理 neg_div_self
  条件: {a : K} (h : a != 0)
  结论: -a / a = -1
  证明: by rw [neg_div, div_self h]

Depends on / 依赖: div_self, neg_div
-/
theorem neg_div_self {a : K} (h : a != 0) : -a / a = -1 := by rw [neg_div, div_self h]

/--
theorem `div_sub_div_same` / 定理 `div_sub_div_same`

English:
theorem div_sub_div_same
  given: (a b c : K)
  statement: a / c - b / c = (a - b) / c
  proof: by
  rw [sub_eq_add_neg]; rw [← neg_div]; rw [← add_div]; rw [sub_eq_add_neg]

中文:
定理 div_sub_div_same
  条件: (a b c : K)
  结论: a / c - b / c = (a - b) / c
  证明: by
  rw [sub_eq_add_neg]; rw [← neg_div]; rw [← add_div]; rw [sub_eq_add_neg]

Depends on / 依赖: add_div, neg_div, sub_eq_add_neg
-/
theorem div_sub_div_same (a b c : K) : a / c - b / c = (a - b) / c := by
  rw [sub_eq_add_neg]; rw [← neg_div]; rw [← add_div]; rw [sub_eq_add_neg]

/--
theorem `same_sub_div` / 定理 `same_sub_div`

English:
theorem same_sub_div
  given: {a b : K} (h : b != 0)
  statement: (b - a) / b = 1 - a / b
  proof: by
  simpa only [← @div_self _ _ b h] using (div_sub_div_same b a b).symm

中文:
定理 same_sub_div
  条件: {a b : K} (h : b != 0)
  结论: (b - a) / b = 1 - a / b
  证明: by
  simpa only [← @div_self _ _ b h] using (div_sub_div_same b a b).symm

Depends on / 依赖: div_self, div_sub_div_same
-/
theorem same_sub_div {a b : K} (h : b != 0) : (b - a) / b = 1 - a / b := by
  simpa only [← @div_self _ _ b h] using (div_sub_div_same b a b).symm

/--
theorem `one_sub_div` / 定理 `one_sub_div`

English:
theorem one_sub_div
  given: {a b : K} (h : b != 0)
  statement: 1 - a / b = (b - a) / b
  proof: (same_sub_div h).symm

中文:
定理 one_sub_div
  条件: {a b : K} (h : b != 0)
  结论: 1 - a / b = (b - a) / b
  证明: (same_sub_div h).symm

Depends on / 依赖: same_sub_div
-/
theorem one_sub_div {a b : K} (h : b != 0) : 1 - a / b = (b - a) / b :=
  (same_sub_div h).symm

/--
theorem `div_sub_same` / 定理 `div_sub_same`

English:
theorem div_sub_same
  given: {a b : K} (h : b != 0)
  statement: (a - b) / b = a / b - 1
  proof: by
  simpa only [← @div_self _ _ b h] using (div_sub_div_same a b b).symm

中文:
定理 div_sub_same
  条件: {a b : K} (h : b != 0)
  结论: (a - b) / b = a / b - 1
  证明: by
  simpa only [← @div_self _ _ b h] using (div_sub_div_same a b b).symm

Depends on / 依赖: div_self, div_sub_div_same
-/
theorem div_sub_same {a b : K} (h : b != 0) : (a - b) / b = a / b - 1 := by
  simpa only [← @div_self _ _ b h] using (div_sub_div_same a b b).symm

/--
theorem `div_sub_one` / 定理 `div_sub_one`

English:
theorem div_sub_one
  given: {a b : K} (h : b != 0)
  statement: a / b - 1 = (a - b) / b
  proof: (div_sub_same h).symm

中文:
定理 div_sub_one
  条件: {a b : K} (h : b != 0)
  结论: a / b - 1 = (a - b) / b
  证明: (div_sub_same h).symm

Depends on / 依赖: div_sub_same
-/
theorem div_sub_one {a b : K} (h : b != 0) : a / b - 1 = (a - b) / b :=
  (div_sub_same h).symm

/--
theorem `sub_div` / 定理 `sub_div`

English:
theorem sub_div
  given: (a b c : K)
  statement: (a - b) / c = a / c - b / c
  proof: (div_sub_div_same _ _ _).symm

中文:
定理 sub_div
  条件: (a b c : K)
  结论: (a - b) / c = a / c - b / c
  证明: (div_sub_div_same _ _ _).symm

Depends on / 依赖: div_sub_div_same
-/
theorem sub_div (a b c : K) : (a - b) / c = a / c - b / c :=
  (div_sub_div_same _ _ _).symm

/--
theorem `inv_sub_inv'` / 定理 `inv_sub_inv'`

English:
theorem inv_sub_inv'
  given: {a b : K} (ha : a != 0) (hb : b != 0)
  statement: a⁻¹ - b⁻¹ = a⁻¹ * (b - a) * b⁻¹
  proof: let _ := invertibleOfNonzero ha; let _ := invertibleOfNonzero hb; invOf_sub_invOf a b

中文:
定理 inv_sub_inv'
  条件: {a b : K} (ha : a != 0) (hb : b != 0)
  结论: a⁻¹ - b⁻¹ = a⁻¹ * (b - a) * b⁻¹
  证明: let _ := invertibleOfNonzero ha; let _ := invertibleOfNonzero hb; invOf_sub_invOf a b

Depends on / 依赖: invOf_sub_invOf, invertibleOfNonzero
-/
theorem inv_sub_inv' {a b : K} (ha : a != 0) (hb : b != 0) : a⁻¹ - b⁻¹ = a⁻¹ * (b - a) * b⁻¹ :=
  let _ := invertibleOfNonzero ha; let _ := invertibleOfNonzero hb; invOf_sub_invOf a b

/--
theorem `one_div_mul_sub_mul_one_div_eq_one_div_add_one_div` / 定理 `one_div_mul_sub_mul_one_div_eq_one_div_add_one_div`

English:
theorem one_div_mul_sub_mul_one_div_eq_one_div_add_one_div
  given: (ha : a != 0) (hb : b != 0)
  proof: by
  simpa only [one_div] using (inv_sub_inv' ha hb).symm

中文:
定理 one_div_mul_sub_mul_one_div_eq_one_div_add_one_div
  条件: (ha : a != 0) (hb : b != 0)
  证明: by
  simpa only [one_div] using (inv_sub_inv' ha hb).symm

Depends on / 依赖: inv_sub_inv, one_div
-/
theorem one_div_mul_sub_mul_one_div_eq_one_div_add_one_div (ha : a != 0) (hb : b != 0) :
    1 / a * (b - a) * (1 / b) = 1 / a - 1 / b := by
  simpa only [one_div] using (inv_sub_inv' ha hb).symm

/--
theorem `inv_eq_self₀` / 定理 `inv_eq_self₀`

English:
theorem inv_eq_self₀
  given: {a : K}
  statement: a⁻¹ = a ↔ a = -1 ∨ a = 0 ∨ a = 1
  proof: by
  obtain rfl | ha := eq_or_ne a 0; · simp
  rw [← mul_eq_one_iff_inv_eq₀ ha]; rw [← pow_two]; rw [sq_eq_one_iff]
  tauto

中文:
定理 inv_eq_self₀
  条件: {a : K}
  结论: a⁻¹ = a ↔ a = -1 ∨ a = 0 ∨ a = 1
  证明: by
  obtain rfl | ha := eq_or_ne a 0; · simp
  rw [← mul_eq_one_iff_inv_eq₀ ha]; rw [← pow_two]; rw [sq_eq_one_iff]
  tauto

Depends on / 依赖: eq_or_ne, pow_two, sq_eq_one_iff
-/
theorem inv_eq_self₀ {a : K} : a⁻¹ = a ↔ a = -1 ∨ a = 0 ∨ a = 1 := by
  obtain rfl | ha := eq_or_ne a 0; · simp
  rw [← mul_eq_one_iff_inv_eq₀ ha]; rw [← pow_two]; rw [sq_eq_one_iff]
  tauto

/--
theorem `self_eq_inv₀` / 定理 `self_eq_inv₀`

English:
theorem self_eq_inv₀
  given: {a : K}
  statement: a = a⁻¹ ↔ a = -1 ∨ a = 0 ∨ a = 1
  proof: by
  rw [eq_comm]; rw [inv_eq_self₀]

中文:
定理 self_eq_inv₀
  条件: {a : K}
  结论: a = a⁻¹ ↔ a = -1 ∨ a = 0 ∨ a = 1
  证明: by
  rw [eq_comm]; rw [inv_eq_self₀]

Depends on / 依赖: eq_comm
-/
theorem self_eq_inv₀ {a : K} : a = a⁻¹ ↔ a = -1 ∨ a = 0 ∨ a = 1 := by
  rw [eq_comm]; rw [inv_eq_self₀]

-- see Note [lower instance priority]
instance (priority := 100) DivisionRing.isDomain : IsDomain K :=
  NoZeroDivisors.to_isDomain _

/--
theorem `Commute.div_sub_div` / 定理 `Commute.div_sub_div`

English:
theorem Commute.div_sub_div
  statement: (hbc : Commute b c) (hbd : Commute b d) (hb : b != 0)
  proof: by
  simpa only [mul_neg, neg_div, ← sub_eq_add_neg] using hbc.neg_right.div_add_div hbd hb hd

中文:
定理 Commute.div_sub_div
  结论: (hbc : Commute b c) (hbd : Commute b d) (hb : b != 0)
  证明: by
  simpa only [mul_neg, neg_div, ← sub_eq_add_neg] using hbc.neg_right.div_add_div hbd hb hd
-/
protected theorem Commute.div_sub_div (hbc : Commute b c) (hbd : Commute b d) (hb : b != 0)
    (hd : d != 0) : a / b - c / d = (a * d - b * c) / (b * d) := by
  simpa only [mul_neg, neg_div, ← sub_eq_add_neg] using hbc.neg_right.div_add_div hbd hb hd

/--
theorem `Commute.inv_sub_inv` / 定理 `Commute.inv_sub_inv`

English:
theorem Commute.inv_sub_inv
  given: (hab : Commute a b) (ha : a != 0) (hb : b != 0)
  proof: by
  simp only [inv_eq_one_div, (Commute.one_right a).div_sub_div hab ha hb, one_mul, mul_one]

中文:
定理 Commute.inv_sub_inv
  条件: (hab : Commute a b) (ha : a != 0) (hb : b != 0)
  证明: by
  simp only [inv_eq_one_div, (Commute.one_right a).div_sub_div hab ha hb, one_mul, mul_one]
-/
protected theorem Commute.inv_sub_inv (hab : Commute a b) (ha : a != 0) (hb : b != 0) :
    a⁻¹ - b⁻¹ = (b - a) / (a * b) := by
  simp only [inv_eq_one_div, (Commute.one_right a).div_sub_div hab ha hb, one_mul, mul_one]

variable [NeZero (2 : K)]

/--
lemma `sub_half` / 引理 `sub_half`

English:
lemma sub_half
  given: (a : K)
  statement: a - a / 2 = a / 2
  proof: by rw [sub_eq_iff_eq_add, add_halves]

中文:
引理 sub_half
  条件: (a : K)
  结论: a - a / 2 = a / 2
  证明: by rw [sub_eq_iff_eq_add, add_halves]

Depends on / 依赖: add_halves, sub_eq_iff_eq_add
-/
lemma sub_half (a : K) : a - a / 2 = a / 2 := by rw [sub_eq_iff_eq_add, add_halves]
/--
lemma `half_sub` / 引理 `half_sub`

English:
lemma half_sub
  given: (a : K)
  statement: a / 2 - a = -(a / 2)
  proof: by rw [← neg_sub, sub_half]

中文:
引理 half_sub
  条件: (a : K)
  结论: a / 2 - a = -(a / 2)
  证明: by rw [← neg_sub, sub_half]

Depends on / 依赖: neg_sub, sub_half
-/
lemma half_sub (a : K) : a / 2 - a = -(a / 2) := by rw [← neg_sub, sub_half]

end DivisionRing

section Semifield

variable [Semifield K] {a b d : K}

/--
theorem `div_add_div` / 定理 `div_add_div`

English:
theorem div_add_div
  given: (a : K) (c : K) (hb : b != 0) (hd : d != 0)
  proof: (Commute.all b _).div_add_div (Commute.all _ _) hb hd

中文:
定理 div_add_div
  条件: (a : K) (c : K) (hb : b != 0) (hd : d != 0)
  证明: (Commute.all b _).div_add_div (Commute.all _ _) hb hd

Depends on / 依赖: Commute, Commute.all, div_add_div
-/
theorem div_add_div (a : K) (c : K) (hb : b != 0) (hd : d != 0) :
    a / b + c / d = (a * d + b * c) / (b * d) :=
  (Commute.all b _).div_add_div (Commute.all _ _) hb hd

/--
theorem `one_div_add_one_div` / 定理 `one_div_add_one_div`

English:
theorem one_div_add_one_div
  given: (ha : a != 0) (hb : b != 0)
  statement: 1 / a + 1 / b = (a + b) / (a * b)
  proof: (Commute.all a _).one_div_add_one_div ha hb

中文:
定理 one_div_add_one_div
  条件: (ha : a != 0) (hb : b != 0)
  结论: 1 / a + 1 / b = (a + b) / (a * b)
  证明: (Commute.all a _).one_div_add_one_div ha hb

Depends on / 依赖: Commute, Commute.all, one_div_add_one_div
-/
theorem one_div_add_one_div (ha : a != 0) (hb : b != 0) : 1 / a + 1 / b = (a + b) / (a * b) :=
  (Commute.all a _).one_div_add_one_div ha hb

/--
theorem `inv_add_inv` / 定理 `inv_add_inv`

English:
theorem inv_add_inv
  given: (ha : a != 0) (hb : b != 0)
  statement: a⁻¹ + b⁻¹ = (a + b) / (a * b)
  proof: (Commute.all a _).inv_add_inv ha hb

中文:
定理 inv_add_inv
  条件: (ha : a != 0) (hb : b != 0)
  结论: a⁻¹ + b⁻¹ = (a + b) / (a * b)
  证明: (Commute.all a _).inv_add_inv ha hb

Depends on / 依赖: Commute, Commute.all, inv_add_inv
-/
theorem inv_add_inv (ha : a != 0) (hb : b != 0) : a⁻¹ + b⁻¹ = (a + b) / (a * b) :=
  (Commute.all a _).inv_add_inv ha hb

end Semifield

section Field

variable [Field K]

instance (priority := 100) Field.toGrindField : Lean.Grind.Field K :=
  { CommRing.toGrindCommRing K, ‹Field K› with
    zpow := ⟨fun a n => a^n⟩
    zpow_zero a := by simp
    zpow_succ a n := by
      by_cases h : a = 0
      · rw [← Int.natCast_add_one, zpow_natCast, zpow_natCast, pow_succ]
      · rw [zpow_add_one₀ h]
    zpow_neg a n := by simp
    zero_ne_one := zero_ne_one }

attribute [local simp] mul_assoc mul_comm mul_left_comm

/--
theorem `div_sub_div` / 定理 `div_sub_div`

English:
theorem div_sub_div
  given: (a : K) {b : K} (c : K) {d : K} (hb : b != 0) (hd : d != 0)
  proof: (Commute.all b _).div_sub_div (Commute.all _ _) hb hd

中文:
定理 div_sub_div
  条件: (a : K) {b : K} (c : K) {d : K} (hb : b != 0) (hd : d != 0)
  证明: (Commute.all b _).div_sub_div (Commute.all _ _) hb hd

Depends on / 依赖: Commute, Commute.all, div_sub_div
-/
theorem div_sub_div (a : K) {b : K} (c : K) {d : K} (hb : b != 0) (hd : d != 0) :
    a / b - c / d = (a * d - b * c) / (b * d) :=
  (Commute.all b _).div_sub_div (Commute.all _ _) hb hd

/--
theorem `inv_sub_inv` / 定理 `inv_sub_inv`

English:
theorem inv_sub_inv
  given: {a b : K} (ha : a != 0) (hb : b != 0)
  statement: a⁻¹ - b⁻¹ = (b - a) / (a * b)
  proof: by
  rw [inv_eq_one_div]; rw [inv_eq_one_div]; rw [div_sub_div _ _ ha hb]; rw [one_mul]; rw [mul_one]

中文:
定理 inv_sub_inv
  条件: {a b : K} (ha : a != 0) (hb : b != 0)
  结论: a⁻¹ - b⁻¹ = (b - a) / (a * b)
  证明: by
  rw [inv_eq_one_div]; rw [inv_eq_one_div]; rw [div_sub_div _ _ ha hb]; rw [one_mul]; rw [mul_one]

Depends on / 依赖: div_sub_div, inv_eq_one_div, mul_one, one_mul
-/
theorem inv_sub_inv {a b : K} (ha : a != 0) (hb : b != 0) : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by
  rw [inv_eq_one_div]; rw [inv_eq_one_div]; rw [div_sub_div _ _ ha hb]; rw [one_mul]; rw [mul_one]

/--
theorem `sub_div'` / 定理 `sub_div'`

English:
theorem sub_div'
  given: {a b c : K} (hc : c != 0)
  statement: b - a / c = (b * c - a) / c
  proof: by
  simpa using div_sub_div b a one_ne_zero hc

中文:
定理 sub_div'
  条件: {a b c : K} (hc : c != 0)
  结论: b - a / c = (b * c - a) / c
  证明: by
  simpa using div_sub_div b a one_ne_zero hc

Depends on / 依赖: MulDivCancelClass, div_sub_div, one_ne_zero, toMulDivCancelClass
-/
theorem sub_div' {a b c : K} (hc : c != 0) : b - a / c = (b * c - a) / c := by
  simpa using div_sub_div b a one_ne_zero hc

/--
theorem `div_sub'` / 定理 `div_sub'`

English:
theorem div_sub'
  given: {a b c : K} (hc : c != 0)
  statement: a / c - b = (a - c * b) / c
  proof: by
  simpa using div_sub_div a b hc one_ne_zero

中文:
定理 div_sub'
  条件: {a b c : K} (hc : c != 0)
  结论: a / c - b = (a - c * b) / c
  证明: by
  simpa using div_sub_div a b hc one_ne_zero

Depends on / 依赖: div_sub_div, one_ne_zero
-/
theorem div_sub' {a b c : K} (hc : c != 0) : a / c - b = (a - c * b) / c := by
  simpa using div_sub_div a b hc one_ne_zero

-- see Note [lower instance priority]
instance (priority := 100) Field.isDomain : IsDomain K :=
  { DivisionRing.isDomain with }

end Field

section NoncomputableDefs

variable {R : Type*} [Nontrivial R]

-- See note [reducible non-instances]
/--
Definition of `DivisionRing.ofIsUnitOrEqZero` / `DivisionRing.ofIsUnitOrEqZero` 的定义

English:
abbreviation DivisionRing.ofIsUnitOrEqZero
  signature: [Ring R] (h : forall a : R, IsUnit a ∨ a = 0)
  body: ‹Ring R›
  __ := groupWithZeroOfIsUnitOrEqZero h
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

中文:
缩写 DivisionRing.ofIsUnitOrEqZero
  签名: [Ring R] (h : 对任意 a : R, IsUnit a ∨ a = 0)
  定义体: ‹Ring R›
  __ := groupWithZeroOfIsUnitOrEqZero h
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl
-/
noncomputable abbrev DivisionRing.ofIsUnitOrEqZero [Ring R] (h : forall a : R, IsUnit a ∨ a = 0) :
    DivisionRing R where
  toRing := ‹Ring R›
  __ := groupWithZeroOfIsUnitOrEqZero h
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

-- See note [reducible non-instances]
/--
Definition of `Field.ofIsUnitOrEqZero` / `Field.ofIsUnitOrEqZero` 的定义

English:
abbreviation Field.ofIsUnitOrEqZero
  signature: [CommRing R] (h : forall a : R, IsUnit a ∨ a = 0)
  body: ‹CommRing R›
  __ := DivisionRing.ofIsUnitOrEqZero h

中文:
缩写 Field.ofIsUnitOrEqZero
  签名: [CommRing R] (h : 对任意 a : R, IsUnit a ∨ a = 0)
  定义体: ‹CommRing R›
  __ := DivisionRing.ofIsUnitOrEqZero h

Depends on / 依赖: CommRing
-/
noncomputable abbrev Field.ofIsUnitOrEqZero [CommRing R] (h : forall a : R, IsUnit a ∨ a = 0) :
    Field R where
  toCommRing := ‹CommRing R›
  __ := DivisionRing.ofIsUnitOrEqZero h

end NoncomputableDefs

namespace Function.Injective
variable [Zero K] [Add K] [Neg K] [Sub K] [One K] [Mul K] [Inv K] [Div K] [SMul Nat K] [SMul Int K]
  [SMul Rat>=0 K] [SMul Rat K] [Pow K Nat] [Pow K Int] [NatCast K] [IntCast K] [NNRatCast K] [RatCast K]
  (f : K -> L) (hf : Injective f)

-- See note [reducible non-instances]
/--
Definition of `divisionSemiring` / `divisionSemiring` 的定义

English:
abbreviation divisionSemiring
  signature: [DivisionSemiring L] (zero : f 0 = 0) (one : f 1 = 1)
  body: hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.groupWithZero f zero one mul inv div npow zpow
nnratCast_def q := hf by rw [nnratCast, NNRat.cast_def, div, natCast, natCast]
  nnqsmul := (· • ·)
nnqsmul_def q a := hf by rw [nnqsmul, NNRat.smul_def, mul, nnratCast]

中文:
缩写 divisionSemiring
  签名: [DivisionSemiring L] (zero : f 0 = 0) (one : f 1 = 1)
  定义体: hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.groupWithZero f zero one mul inv div npow zpow
nnratCast_def q := hf by rw [nnratCast, NNRat.cast_def, div, natCast, natCast]
  nnqsmul := (· • ·)
nnqsmul_def q a := hf by rw [nnqsmul, NNRat.smul_def, mul, nnratCast]
-/
protected abbrev divisionSemiring [DivisionSemiring L] (zero : f 0 = 0) (one : f 1 = 1)
    (add : forall x y, f (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y)
    (inv : forall x, f x⁻¹ = (f x)⁻¹) (div : forall x y, f (x / y) = f x / f y)
    (nsmul : forall (n : Nat) (x), f (n • x) = n • f x) (nnqsmul : forall (q : Rat>=0) (x), f (q • x) = q • f x)
    (npow : forall (x) (n : Nat), f (x ^ n) = f x ^ n) (zpow : forall (x) (n : Int), f (x ^ n) = f x ^ n)
    (natCast : forall n : Nat, f n = n) (nnratCast : forall q : Rat>=0, f q = q) : DivisionSemiring K where
  toSemiring := hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.groupWithZero f zero one mul inv div npow zpow
nnratCast_def q := hf by rw [nnratCast, NNRat.cast_def, div, natCast, natCast]
  nnqsmul := (· • ·)
nnqsmul_def q a := hf by rw [nnqsmul, NNRat.smul_def, mul, nnratCast]

-- See note [reducible non-instances]
/--
Definition of `divisionRing` / `divisionRing` 的定义

English:
abbreviation divisionRing
  signature: [DivisionRing L] (zero : f 0 = 0) (one : f 1 = 1)
  body: hf.ring f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.groupWithZero f zero one mul inv div npow zpow
  __ := hf.divisionSemiring f zero one add mul inv div nsmul nnqsmul npow zpow natCast nnratCast
ratCast_def q := hf by rw [ratCast, div, intCast, natCast, Rat.cast_def]
  qs

中文:
缩写 divisionRing
  签名: [DivisionRing L] (zero : f 0 = 0) (one : f 1 = 1)
  定义体: hf.ring f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.groupWithZero f zero one mul inv div npow zpow
  __ := hf.divisionSemiring f zero one add mul inv div nsmul nnqsmul npow zpow natCast nnratCast
ratCast_def q := hf by rw [ratCast, div, intCast, natCast, Rat.cast_def]
  qs
-/
protected abbrev divisionRing [DivisionRing L] (zero : f 0 = 0) (one : f 1 = 1)
    (add : forall x y, f (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y)
    (neg : forall x, f (-x) = -f x) (sub : forall x y, f (x - y) = f x - f y) (inv : forall x, f x⁻¹ = (f x)⁻¹)
    (div : forall x y, f (x / y) = f x / f y)
    (nsmul : forall (n : Nat) (x), f (n • x) = n • f x) (zsmul : forall (n : Int) (x), f (n • x) = n • f x)
    (nnqsmul : forall (q : Rat>=0) (x), f (q • x) = q • f x) (qsmul : forall (q : Rat) (x), f (q • x) = q • f x)
    (npow : forall (x) (n : Nat), f (x ^ n) = f x ^ n) (zpow : forall (x) (n : Int), f (x ^ n) = f x ^ n)
    (natCast : forall n : Nat, f n = n) (intCast : forall n : Int, f n = n) (nnratCast : forall q : Rat>=0, f q = q)
    (ratCast : forall q : Rat, f q = q) : DivisionRing K where
  toRing := hf.ring f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.groupWithZero f zero one mul inv div npow zpow
  __ := hf.divisionSemiring f zero one add mul inv div nsmul nnqsmul npow zpow natCast nnratCast
ratCast_def q := hf by rw [ratCast, div, intCast, natCast, Rat.cast_def]
  qsmul := (· • ·)
qsmul_def q a := hf by rw [qsmul, mul, Rat.smul_def, ratCast]

-- See note [reducible non-instances]
/--
Definition of `semifield` / `semifield` 的定义

English:
abbreviation semifield
  signature: [Semifield L] (zero : f 0 = 0) (one : f 1 = 1)
  body: hf.commSemiring f zero one add mul nsmul npow natCast
  __ := hf.commGroupWithZero f zero one mul inv div npow zpow
  __ := hf.divisionSemiring f zero one add mul inv div nsmul nnqsmul npow zpow natCast nnratCast

中文:
缩写 semifield
  签名: [Semifield L] (zero : f 0 = 0) (one : f 1 = 1)
  定义体: hf.commSemiring f zero one add mul nsmul npow natCast
  __ := hf.commGroupWithZero f zero one mul inv div npow zpow
  __ := hf.divisionSemiring f zero one add mul inv div nsmul nnqsmul npow zpow natCast nnratCast
-/
protected abbrev semifield [Semifield L] (zero : f 0 = 0) (one : f 1 = 1)
    (add : forall x y, f (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y)
    (inv : forall x, f x⁻¹ = (f x)⁻¹) (div : forall x y, f (x / y) = f x / f y)
    (nsmul : forall (n : Nat) (x), f (n • x) = n • f x) (nnqsmul : forall (q : Rat>=0) (x), f (q • x) = q • f x)
    (npow : forall (x) (n : Nat), f (x ^ n) = f x ^ n) (zpow : forall (x) (n : Int), f (x ^ n) = f x ^ n)
    (natCast : forall n : Nat, f n = n) (nnratCast : forall q : Rat>=0, f q = q) : Semifield K where
  toCommSemiring := hf.commSemiring f zero one add mul nsmul npow natCast
  __ := hf.commGroupWithZero f zero one mul inv div npow zpow
  __ := hf.divisionSemiring f zero one add mul inv div nsmul nnqsmul npow zpow natCast nnratCast

-- See note [reducible non-instances]
/--
Definition of `field` / `field` 的定义

English:
abbreviation field
  signature: [Field L] (zero : f 0 = 0) (one : f 1 = 1)
  body: hf.commRing f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.divisionRing f zero one add mul neg sub inv div nsmul zsmul nnqsmul qsmul npow zpow
    natCast intCast nnratCast ratCast

中文:
缩写 field
  签名: [Field L] (zero : f 0 = 0) (one : f 1 = 1)
  定义体: hf.commRing f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.divisionRing f zero one add mul neg sub inv div nsmul zsmul nnqsmul qsmul npow zpow
    natCast intCast nnratCast ratCast
-/
protected abbrev field [Field L] (zero : f 0 = 0) (one : f 1 = 1)
    (add : forall x y, f (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y)
    (neg : forall x, f (-x) = -f x) (sub : forall x y, f (x - y) = f x - f y) (inv : forall x, f x⁻¹ = (f x)⁻¹)
    (div : forall x y, f (x / y) = f x / f y)
    (nsmul : forall (n : Nat) (x), f (n • x) = n • f x) (zsmul : forall (n : Int) (x), f (n • x) = n • f x)
    (nnqsmul : forall (q : Rat>=0) (x), f (q • x) = q • f x) (qsmul : forall (q : Rat) (x), f (q • x) = q • f x)
    (npow : forall (x) (n : Nat), f (x ^ n) = f x ^ n) (zpow : forall (x) (n : Int), f (x ^ n) = f x ^ n)
    (natCast : forall n : Nat, f n = n) (intCast : forall n : Int, f n = n) (nnratCast : forall q : Rat>=0, f q = q)
    (ratCast : forall q : Rat, f q = q) :
    Field K where
  toCommRing := hf.commRing f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.divisionRing f zero one add mul neg sub inv div nsmul zsmul nnqsmul qsmul npow zpow
    natCast intCast nnratCast ratCast

end Function.Injective

/-! ### Order dual -/

namespace OrderDual

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [RatCast
  signature: K] : RatCast Kᵒᵈ
  body: inferInstanceAs RatCast K

中文:
实例 [RatCast
  签名: K] : RatCast Kᵒᵈ
  定义体: inferInstanceAs RatCast K

Depends on / 依赖: RatCast
-/
instance [RatCast K] : RatCast Kᵒᵈ := inferInstanceAs RatCast K
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NNRatCast
  signature: K] : NNRatCast Kᵒᵈ
  body: inferInstanceAs NNRatCast K

中文:
实例 [NNRatCast
  签名: K] : NNRatCast Kᵒᵈ
  定义体: inferInstanceAs NNRatCast K

Depends on / 依赖: NNRatCast
-/
instance [NNRatCast K] : NNRatCast Kᵒᵈ := inferInstanceAs NNRatCast K
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DivisionSemiring
  signature: K] : DivisionSemiring Kᵒᵈ
  body: inferInstanceAs DivisionSemiring K

中文:
实例 [DivisionSemiring
  签名: K] : DivisionSemiring Kᵒᵈ
  定义体: inferInstanceAs DivisionSemiring K

Depends on / 依赖: DivisionSemiring
-/
instance [DivisionSemiring K] : DivisionSemiring Kᵒᵈ := inferInstanceAs DivisionSemiring K
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DivisionRing
  signature: K] : DivisionRing Kᵒᵈ
  body: inferInstanceAs DivisionRing K

中文:
实例 [DivisionRing
  签名: K] : DivisionRing Kᵒᵈ
  定义体: inferInstanceAs DivisionRing K

Depends on / 依赖: DivisionRing
-/
instance [DivisionRing K] : DivisionRing Kᵒᵈ := inferInstanceAs DivisionRing K
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semifield
  signature: K] : Semifield Kᵒᵈ
  body: inferInstanceAs Semifield K

中文:
实例 [Semifield
  签名: K] : Semifield Kᵒᵈ
  定义体: inferInstanceAs Semifield K

Depends on / 依赖: Semifield
-/
instance [Semifield K] : Semifield Kᵒᵈ := inferInstanceAs Semifield K
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Field
  signature: K] : Field Kᵒᵈ
  body: inferInstanceAs Field K

中文:
实例 [Field
  签名: K] : Field Kᵒᵈ
  定义体: inferInstanceAs Field K
-/
instance [Field K] : Field Kᵒᵈ := inferInstanceAs Field K

end OrderDual

/--
lemma `toDual_ratCast` / 引理 `toDual_ratCast`

English:
lemma toDual_ratCast
  given: [RatCast K] (n : Rat)
  statement: toDual (n : K) = n
  proof: rfl

中文:
引理 toDual_ratCast
  条件: [RatCast K] (n : Rat)
  结论: toDual (n : K) = n
  证明: rfl
-/
@[simp] lemma toDual_ratCast [RatCast K] (n : Rat) : toDual (n : K) = n := rfl

/--
lemma `ofDual_ratCast` / 引理 `ofDual_ratCast`

English:
lemma ofDual_ratCast
  given: [RatCast K] (n : Rat)
  statement: (ofDual n : K) = n
  proof: rfl

中文:
引理 ofDual_ratCast
  条件: [RatCast K] (n : Rat)
  结论: (ofDual n : K) = n
  证明: rfl
-/
@[simp] lemma ofDual_ratCast [RatCast K] (n : Rat) : (ofDual n : K) = n := rfl

/-! ### Lexicographic order -/

namespace Lex

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [RatCast
  signature: K] : RatCast (Lex K)
  body: inferInstanceAs RatCast K

中文:
实例 [RatCast
  签名: K] : RatCast (Lex K)
  定义体: inferInstanceAs RatCast K

Depends on / 依赖: RatCast
-/
instance [RatCast K] : RatCast (Lex K) := inferInstanceAs RatCast K
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DivisionSemiring
  signature: K] : DivisionSemiring (Lex K)
  body: inferInstanceAs DivisionSemiring K

中文:
实例 [DivisionSemiring
  签名: K] : DivisionSemiring (Lex K)
  定义体: inferInstanceAs DivisionSemiring K

Depends on / 依赖: DivisionSemiring
-/
instance [DivisionSemiring K] : DivisionSemiring (Lex K) := inferInstanceAs DivisionSemiring K
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DivisionRing
  signature: K] : DivisionRing (Lex K)
  body: inferInstanceAs DivisionRing K

中文:
实例 [DivisionRing
  签名: K] : DivisionRing (Lex K)
  定义体: inferInstanceAs DivisionRing K

Depends on / 依赖: DivisionRing
-/
instance [DivisionRing K] : DivisionRing (Lex K) := inferInstanceAs DivisionRing K
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semifield
  signature: K] : Semifield (Lex K)
  body: inferInstanceAs Semifield K

中文:
实例 [Semifield
  签名: K] : Semifield (Lex K)
  定义体: inferInstanceAs Semifield K

Depends on / 依赖: Semifield
-/
instance [Semifield K] : Semifield (Lex K) := inferInstanceAs Semifield K
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Field
  signature: K] : Field (Lex K)
  body: inferInstanceAs Field K

中文:
实例 [Field
  签名: K] : Field (Lex K)
  定义体: inferInstanceAs Field K
-/
instance [Field K] : Field (Lex K) := inferInstanceAs Field K

end Lex

/--
lemma `toLex_ratCast` / 引理 `toLex_ratCast`

English:
lemma toLex_ratCast
  given: [RatCast K] (n : Rat)
  statement: toLex (n : K) = n
  proof: rfl

中文:
引理 toLex_ratCast
  条件: [RatCast K] (n : Rat)
  结论: toLex (n : K) = n
  证明: rfl
-/
@[simp] lemma toLex_ratCast [RatCast K] (n : Rat) : toLex (n : K) = n := rfl

/--
lemma `ofLex_ratCast` / 引理 `ofLex_ratCast`

English:
lemma ofLex_ratCast
  given: [RatCast K] (n : Rat)
  statement: (ofLex n : K) = n
  proof: rfl

中文:
引理 ofLex_ratCast
  条件: [RatCast K] (n : Rat)
  结论: (ofLex n : K) = n
  证明: rfl
-/
@[simp] lemma ofLex_ratCast [RatCast K] (n : Rat) : (ofLex n : K) = n := rfl
