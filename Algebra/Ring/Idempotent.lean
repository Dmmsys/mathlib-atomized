/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Algebra.GroupWithZero.Idempotent
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Order.Notation
public import Mathlib.Tactic.Convert
public import Mathlib.Algebra.Group.Torsion

/-!
# Idempotent elements of a ring

This file proves result about idempotent elements of a ring, like:
* `IsIdempotentElem.one_sub_iff`: In a (non-associative) ring, `a` is an idempotent if and only if
  `1 - a` is an idempotent.
-/

public section

variable {R : Type*}

namespace IsIdempotentElem
section NonAssocRing
variable [NonAssocRing R] {a : R}

/--
lemma `one_sub` / 引理 `one_sub`

English:
lemma one_sub
  given: (h : IsIdempotentElem a)
  statement: IsIdempotentElem (1 - a)
  proof: by
  rw [IsIdempotentElem]; rw [mul_sub]; rw [mul_one]; rw [sub_mul]; rw [one_mul]; rw [h.eq]; rw [sub_self]; rw [sub_zero]

@[simp]

中文:
引理 one_sub
  条件: (h : IsIdempotentElem a)
  结论: IsIdempotentElem (1 - a)
  证明: by
  rw [IsIdempotentElem]; rw [mul_sub]; rw [mul_one]; rw [sub_mul]; rw [one_mul]; rw [h.eq]; rw [sub_self]; rw [sub_zero]

@[simp]

Depends on / 依赖: IsIdempotentElem, Subsingleton, Subsingleton.elim, h.eq, infer_instance, mul_one, mul_sub, one_mul, sub_mul, sub_self, sub_zero
-/
lemma one_sub (h : IsIdempotentElem a) : IsIdempotentElem (1 - a) := by
  rw [IsIdempotentElem]; rw [mul_sub]; rw [mul_one]; rw [sub_mul]; rw [one_mul]; rw [h.eq]; rw [sub_self]; rw [sub_zero]

@[simp]
/--
lemma `one_sub_iff` / 引理 `one_sub_iff`

English:
lemma one_sub_iff
  statement: IsIdempotentElem (1 - a) ↔ IsIdempotentElem a
  proof: ⟨fun h => sub_sub_cancel 1 a ▸ h.one_sub, IsIdempotentElem.one_sub⟩

@[simp]

中文:
引理 one_sub_iff
  结论: IsIdempotentElem (1 - a) ↔ IsIdempotentElem a
  证明: ⟨fun h => sub_sub_cancel 1 a ▸ h.one_sub, IsIdempotentElem.one_sub⟩

@[simp]

Depends on / 依赖: IsAffine, IsIdempotentElem, IsIdempotentElem.one_sub, Scheme, Scheme.topIso, Subsingleton, Subsingleton.elim, X.isBasis_affineOpens.exists_subset_of_mem_open, exists_subset_of_mem_open, h.one_sub, infer_instance, isBasis_affineOpens, isEmpty_or_nonempty, isOpen_univ, of_isIso, one_sub, sub_sub_cancel, topIso
-/
lemma one_sub_iff : IsIdempotentElem (1 - a) ↔ IsIdempotentElem a :=
  ⟨fun h => sub_sub_cancel 1 a ▸ h.one_sub, IsIdempotentElem.one_sub⟩

@[simp]
/--
lemma `mul_one_sub_self` / 引理 `mul_one_sub_self`

English:
lemma mul_one_sub_self
  given: (h : IsIdempotentElem a)
  statement: a * (1 - a) = 0
  proof: by
  rw [mul_sub]; rw [mul_one]; rw [h.eq]; rw [sub_self]

@[simp]

中文:
引理 mul_one_sub_self
  条件: (h : IsIdempotentElem a)
  结论: a * (1 - a) = 0
  证明: by
  rw [mul_sub]; rw [mul_one]; rw [h.eq]; rw [sub_self]

@[simp]

Depends on / 依赖: h.eq, mul_one, mul_sub, sub_self
-/
lemma mul_one_sub_self (h : IsIdempotentElem a) : a * (1 - a) = 0 := by
  rw [mul_sub]; rw [mul_one]; rw [h.eq]; rw [sub_self]

@[simp]
/--
lemma `one_sub_mul_self` / 引理 `one_sub_mul_self`

English:
lemma one_sub_mul_self
  given: (h : IsIdempotentElem a)
  statement: (1 - a) * a = 0
  proof: by
  rw [sub_mul]; rw [one_mul]; rw [h.eq]; rw [sub_self]

中文:
引理 one_sub_mul_self
  条件: (h : IsIdempotentElem a)
  结论: (1 - a) * a = 0
  证明: by
  rw [sub_mul]; rw [one_mul]; rw [h.eq]; rw [sub_self]

Depends on / 依赖: h.eq, one_mul, sub_mul, sub_self
-/
lemma one_sub_mul_self (h : IsIdempotentElem a) : (1 - a) * a = 0 := by
  rw [sub_mul]; rw [one_mul]; rw [h.eq]; rw [sub_self]

/--
lemma `_root_.isIdempotentElem_iff_mul_one_sub_self` / 引理 `_root_.isIdempotentElem_iff_mul_one_sub_self`

English:
lemma _root_.isIdempotentElem_iff_mul_one_sub_self
  proof: by
  rw [mul_sub]; rw [mul_one]; rw [sub_eq_zero]; rw [eq_comm]; rw [IsIdempotentElem]

中文:
引理 _root_.isIdempotentElem_iff_mul_one_sub_self
  证明: by
  rw [mul_sub]; rw [mul_one]; rw [sub_eq_zero]; rw [eq_comm]; rw [IsIdempotentElem]

Depends on / 依赖: IsIdempotentElem, eq_comm, mul_one, mul_sub, sub_eq_zero
-/
lemma _root_.isIdempotentElem_iff_mul_one_sub_self :
    IsIdempotentElem a ↔ a * (1 - a) = 0 := by
  rw [mul_sub]; rw [mul_one]; rw [sub_eq_zero]; rw [eq_comm]; rw [IsIdempotentElem]

/--
lemma `_root_.isIdempotentElem_iff_one_sub_mul_self` / 引理 `_root_.isIdempotentElem_iff_one_sub_mul_self`

English:
lemma _root_.isIdempotentElem_iff_one_sub_mul_self
  proof: by
  rw [sub_mul]; rw [one_mul]; rw [sub_eq_zero]; rw [eq_comm]; rw [IsIdempotentElem]

中文:
引理 _root_.isIdempotentElem_iff_one_sub_mul_self
  证明: by
  rw [sub_mul]; rw [one_mul]; rw [sub_eq_zero]; rw [eq_comm]; rw [IsIdempotentElem]

Depends on / 依赖: IsIdempotentElem, eq_comm, one_mul, sub_eq_zero, sub_mul
-/
lemma _root_.isIdempotentElem_iff_one_sub_mul_self :
    IsIdempotentElem a ↔ (1 - a) * a = 0 := by
  rw [sub_mul]; rw [one_mul]; rw [sub_eq_zero]; rw [eq_comm]; rw [IsIdempotentElem]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Compl {a : R // IsIdempotentElem a}
  body: ⟨1 - a, a.prop.one_sub⟩

中文:
实例 :
  签名: Compl {a : R // IsIdempotentElem a}
  定义体: ⟨1 - a, a.prop.one_sub⟩

Depends on / 依赖: a.prop.one_sub, one_sub
-/
instance : Compl {a : R // IsIdempotentElem a} where compl a := ⟨1 - a, a.prop.one_sub⟩

/--
lemma `coe_compl` / 引理 `coe_compl`

English:
lemma coe_compl
  given: (a : {a : R // IsIdempotentElem a})
  statement: ↑aᶜ = (1 : R) - ↑a
  proof: rfl

中文:
引理 coe_compl
  条件: (a : {a : R // IsIdempotentElem a})
  结论: ↑aᶜ = (1 : R) - ↑a
  证明: rfl
-/
@[simp] lemma coe_compl (a : {a : R // IsIdempotentElem a}) : ↑aᶜ = (1 : R) - ↑a := rfl

/--
lemma `compl_compl` / 引理 `compl_compl`

English:
lemma compl_compl
  given: (a : {a : R // IsIdempotentElem a})
  statement: aᶜᶜ = a
  proof: by ext; simp

中文:
引理 compl_compl
  条件: (a : {a : R // IsIdempotentElem a})
  结论: aᶜᶜ = a
  证明: by ext; simp
-/
@[simp] lemma compl_compl (a : {a : R // IsIdempotentElem a}) : aᶜᶜ = a := by ext; simp
/--
lemma `zero_compl` / 引理 `zero_compl`

English:
lemma zero_compl
  statement: (0 : {a : R // IsIdempotentElem a})ᶜ = 1
  proof: by ext; simp

中文:
引理 zero_compl
  结论: (0 : {a : R // IsIdempotentElem a})ᶜ = 1
  证明: by ext; simp
-/
@[simp] lemma zero_compl : (0 : {a : R // IsIdempotentElem a})ᶜ = 1 := by ext; simp
/--
lemma `one_compl` / 引理 `one_compl`

English:
lemma one_compl
  statement: (1 : {a : R // IsIdempotentElem a})ᶜ = 0
  proof: by ext; simp

中文:
引理 one_compl
  结论: (1 : {a : R // IsIdempotentElem a})ᶜ = 0
  证明: by ext; simp
-/
@[simp] lemma one_compl : (1 : {a : R // IsIdempotentElem a})ᶜ = 0 := by ext; simp

end NonAssocRing

section Semiring
variable [Semiring R] {a b : R}

/--
lemma `of_mul_add` / 引理 `of_mul_add`

English:
lemma of_mul_add
  given: (mul : a * b = 0) (add : a + b = 1)
  statement: IsIdempotentElem a ∧ IsIdempotentElem b
  proof: by
  simp_rw [IsIdempotentElem]; constructor
  · conv_rhs => rw [← mul_one a, ← add, mul_add, mul, add_zero]
  · conv_rhs => rw [← one_mul b, ← add, add_mul, mul, zero_add]

中文:
引理 of_mul_add
  条件: (mul : a * b = 0) (add : a + b = 1)
  结论: IsIdempotentElem a ∧ IsIdempotentElem b
  证明: by
  simp_rw [IsIdempotentElem]; constructor
  · conv_rhs => rw [← mul_one a, ← add, mul_add, mul, add_zero]
  · conv_rhs => rw [← one_mul b, ← add, add_mul, mul, zero_add]

Depends on / 依赖: IsIdempotentElem, add_mul, add_zero, conv_rhs, mul_add, mul_one, one_mul, simp_rw, zero_add
-/
lemma of_mul_add (mul : a * b = 0) (add : a + b = 1) : IsIdempotentElem a ∧ IsIdempotentElem b := by
  simp_rw [IsIdempotentElem]; constructor
  · conv_rhs => rw [← mul_one a, ← add, mul_add, mul, add_zero]
  · conv_rhs => rw [← one_mul b, ← add, add_mul, mul, zero_add]

end Semiring

section NonUnitalRing
variable [NonUnitalRing R] {a b : R}

/--
lemma `add_sub_mul_of_commute` / 引理 `add_sub_mul_of_commute`

English:
lemma add_sub_mul_of_commute
  given: (h : Commute a b) (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
  proof: by
  simp only [IsIdempotentElem, h.eq, mul_sub, mul_add, sub_mul, add_mul, ha.eq,
    mul_assoc, add_sub_cancel_right, hb.eq, hb.mul_self_mul, add_sub_cancel_left, sub_right_inj]
  rw [← h.eq]; rw [ha.mul_self_mul]; rw [h.eq]; rw [hb.mul_self_mul]; rw [add_sub_cancel_right]

中文:
引理 add_sub_mul_of_commute
  条件: (h : Commute a b) (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
  证明: by
  simp only [IsIdempotentElem, h.eq, mul_sub, mul_add, sub_mul, add_mul, ha.eq,
    mul_assoc, add_sub_cancel_right, hb.eq, hb.mul_self_mul, add_sub_cancel_left, sub_right_inj]
  rw [← h.eq]; rw [ha.mul_self_mul]; rw [h.eq]; rw [hb.mul_self_mul]; rw [add_sub_cancel_right]

Depends on / 依赖: IsIdempotentElem, add_mul, add_sub_cancel_left, add_sub_cancel_right, h.eq, ha.eq, ha.mul_self_mul, hb.eq, hb.mul_self_mul, mul_add, mul_assoc, mul_self_mul, mul_sub, sub_mul, sub_right_inj
-/
lemma add_sub_mul_of_commute (h : Commute a b) (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) :
    IsIdempotentElem (a + b - a * b) := by
  simp only [IsIdempotentElem, h.eq, mul_sub, mul_add, sub_mul, add_mul, ha.eq,
    mul_assoc, add_sub_cancel_right, hb.eq, hb.mul_self_mul, add_sub_cancel_left, sub_right_inj]
  rw [← h.eq]; rw [ha.mul_self_mul]; rw [h.eq]; rw [hb.mul_self_mul]; rw [add_sub_cancel_right]

end NonUnitalRing

section CommRing
variable [CommRing R] {a b : R}

/--
lemma `add_sub_mul` / 引理 `add_sub_mul`

English:
lemma add_sub_mul
  given: (hp : IsIdempotentElem a) (hq : IsIdempotentElem b)
  proof: add_sub_mul_of_commute (.all ..) hp hq

中文:
引理 add_sub_mul
  条件: (hp : IsIdempotentElem a) (hq : IsIdempotentElem b)
  证明: add_sub_mul_of_commute (.all ..) hp hq

Depends on / 依赖: add_sub_mul_of_commute
-/
lemma add_sub_mul (hp : IsIdempotentElem a) (hq : IsIdempotentElem b) :
    IsIdempotentElem (a + b - a * b) := add_sub_mul_of_commute (.all ..) hp hq

end CommRing

/--
theorem `add` / 定理 `add`

English:
theorem add
  statement: [NonUnitalNonAssocSemiring R]
  proof: by
  simp_rw [IsIdempotentElem, mul_add, add_mul, ha.eq, hb.eq, add_add_add_comm, ← add_assoc,
    add_assoc a, hab, zero_add]

中文:
定理 add
  结论: [NonUnitalNonAssocSemiring R]
  证明: by
  simp_rw [IsIdempotentElem, mul_add, add_mul, ha.eq, hb.eq, add_add_add_comm, ← add_assoc,
    add_assoc a, hab, zero_add]

Depends on / 依赖: IsIdempotentElem, add_add_add_comm, add_assoc, add_mul, ha.eq, hb.eq, mul_add, simp_rw, zero_add
-/
theorem add [NonUnitalNonAssocSemiring R]
    {a b : R} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (hab : a * b + b * a = 0) : IsIdempotentElem (a + b) := by
  simp_rw [IsIdempotentElem, mul_add, add_mul, ha.eq, hb.eq, add_add_add_comm, ← add_assoc,
    add_assoc a, hab, zero_add]

/--
theorem `add_iff` / 定理 `add_iff`

English:
theorem add_iff
  statement: [NonUnitalNonAssocSemiring R] [IsCancelAdd R]
  proof: by
  refine ⟨fun h => ?_, ha.add hb⟩
  rw [← add_right_cancel_iff (a := b)]; rw [add_assoc]; rw [← add_left_cancel_iff (a := a)]; rw [← add_assoc]; rw [add_add_add_comm]
  simpa [add_mul, mul_add, ha.eq, hb.eq] using h.eq

中文:
定理 add_iff
  结论: [NonUnitalNonAssocSemiring R] [IsCancelAdd R]
  证明: by
  refine ⟨fun h => ?_, ha.add hb⟩
  rw [← add_right_cancel_iff (a := b)]; rw [add_assoc]; rw [← add_left_cancel_iff (a := a)]; rw [← add_assoc]; rw [add_add_add_comm]
  simpa [add_mul, mul_add, ha.eq, hb.eq] using h.eq

Depends on / 依赖: add_add_add_comm, add_assoc, add_left_cancel_iff, add_mul, add_right_cancel_iff, h.eq, ha.add, ha.eq, hb.eq, mul_add
-/
theorem add_iff [NonUnitalNonAssocSemiring R] [IsCancelAdd R]
    {a b : R} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) :
    IsIdempotentElem (a + b) ↔ a * b + b * a = 0 := by
  refine ⟨fun h => ?_, ha.add hb⟩
  rw [← add_right_cancel_iff (a := b)]; rw [add_assoc]; rw [← add_left_cancel_iff (a := a)]; rw [← add_assoc]; rw [add_add_add_comm]
  simpa [add_mul, mul_add, ha.eq, hb.eq] using h.eq

/--
lemma `sub` / 引理 `sub`

English:
lemma sub
  statement: [NonUnitalNonAssocRing R] {a b : R} (ha : IsIdempotentElem a)
  proof: by
  simp_rw [IsIdempotentElem, sub_mul, mul_sub, hab, hba, ha.eq, hb.eq, sub_self, sub_zero]

中文:
引理 sub
  结论: [NonUnitalNonAssocRing R] {a b : R} (ha : IsIdempotentElem a)
  证明: by
  simp_rw [IsIdempotentElem, sub_mul, mul_sub, hab, hba, ha.eq, hb.eq, sub_self, sub_zero]

Depends on / 依赖: IsIdempotentElem, ha.eq, hb.eq, mul_sub, simp_rw, sub_mul, sub_self, sub_zero
-/
lemma sub [NonUnitalNonAssocRing R] {a b : R} (ha : IsIdempotentElem a)
    (hb : IsIdempotentElem b) (hab : a * b = a) (hba : b * a = a) : IsIdempotentElem (b - a) := by
  simp_rw [IsIdempotentElem, sub_mul, mul_sub, hab, hba, ha.eq, hb.eq, sub_self, sub_zero]

/--
theorem `mul_eq_zero_of_anticommute` / 定理 `mul_eq_zero_of_anticommute`

English:
theorem mul_eq_zero_of_anticommute
  statement: {a b : R} [NonUnitalSemiring R] [IsAddTorsionFree R]
  proof: by
  have h : a * b * a = 0 := by
    rw [← nsmul_right_inj ((Nat.zero_ne_add_one 1).symm)]; rw [nsmul_zero]
    have : a * (a * b + b * a) * a = 0 := by rw [hab, mul_zero, zero_mul]
    simp_rw [mul_add, add_mul, mul_assoc, ha.eq, ← mul_assoc, ha.eq, ← two_nsmul] at this
    exact this
  suffices a

中文:
定理 mul_eq_zero_of_anticommute
  结论: {a b : R} [NonUnitalSemiring R] [IsAddTorsionFree R]
  证明: by
  have h : a * b * a = 0 := by
    rw [← nsmul_right_inj ((Nat.zero_ne_add_one 1).symm)]; rw [nsmul_zero]
    have : a * (a * b + b * a) * a = 0 := by rw [hab, mul_zero, zero_mul]
    simp_rw [mul_add, add_mul, mul_assoc, ha.eq, ← mul_assoc, ha.eq, ← two_nsmul] at this
    exact this
  suffices a

Depends on / 依赖: Nat.zero_ne_add_one, add_mul, add_zero, ha.eq, mul_add, mul_assoc, mul_zero, nsmul_right_inj, nsmul_zero, simp_rw, two_nsmul, zero_mul, zero_ne_add_one
-/
theorem mul_eq_zero_of_anticommute {a b : R} [NonUnitalSemiring R] [IsAddTorsionFree R]
    (ha : IsIdempotentElem a) (hab : a * b + b * a = 0) : a * b = 0 := by
  have h : a * b * a = 0 := by
    rw [← nsmul_right_inj ((Nat.zero_ne_add_one 1).symm)]; rw [nsmul_zero]
    have : a * (a * b + b * a) * a = 0 := by rw [hab, mul_zero, zero_mul]
    simp_rw [mul_add, add_mul, mul_assoc, ha.eq, ← mul_assoc, ha.eq, ← two_nsmul] at this
    exact this
  suffices a * a * b + a * b * a = 0 by rwa [h, add_zero, ha.eq] at this
  rw [mul_assoc]; rw [mul_assoc]; rw [← mul_add]; rw [hab]; rw [mul_zero]

/--
lemma `commute_of_anticommute` / 引理 `commute_of_anticommute`

English:
lemma commute_of_anticommute
  statement: {a b : R} [NonUnitalSemiring R] [IsAddTorsionFree R]
  proof: by
  have := mul_eq_zero_of_anticommute ha hab
  rw [this]; rw [zero_add] at hab
  rw [Commute]; rw [SemiconjBy]; rw [hab]; rw [this]

中文:
引理 commute_of_anticommute
  结论: {a b : R} [NonUnitalSemiring R] [IsAddTorsionFree R]
  证明: by
  have := mul_eq_zero_of_anticommute ha hab
  rw [this]; rw [zero_add] at hab
  rw [Commute]; rw [SemiconjBy]; rw [hab]; rw [this]

Depends on / 依赖: Commute, SemiconjBy, mul_eq_zero_of_anticommute, zero_add
-/
lemma commute_of_anticommute {a b : R} [NonUnitalSemiring R] [IsAddTorsionFree R]
    (ha : IsIdempotentElem a) (hab : a * b + b * a = 0) : Commute a b := by
  have := mul_eq_zero_of_anticommute ha hab
  rw [this]; rw [zero_add] at hab
  rw [Commute]; rw [SemiconjBy]; rw [hab]; rw [this]

/--
theorem `sub_iff` / 定理 `sub_iff`

English:
theorem sub_iff
  statement: [NonUnitalRing R] [IsAddTorsionFree R] {p q : R}
  proof: by
  refine ⟨fun hqp => ?_, fun ⟨h1, h2⟩ => hp.sub hq h1 h2⟩
.mp ((add_sub_cancel p q).symm ▸ hq) have h : p * (q - p) + (q - p) * p = 0 := hp.add_iff hqp
  have hpq : Commute p q := by
    simp_rw [IsIdempotentElem, mul_sub, sub_mul,
    hp.eq, hq.eq, ← sub_add_eq_sub_sub, sub_right_inj, add_sub] a

中文:
定理 sub_iff
  结论: [NonUnitalRing R] [IsAddTorsionFree R] {p q : R}
  证明: by
  refine ⟨fun hqp => ?_, fun ⟨h1, h2⟩ => hp.sub hq h1 h2⟩
.mp ((add_sub_cancel p q).symm ▸ hq) have h : p * (q - p) + (q - p) * p = 0 := hp.add_iff hqp
  have hpq : Commute p q := by
    simp_rw [IsIdempotentElem, mul_sub, sub_mul,
    hp.eq, hq.eq, ← sub_add_eq_sub_sub, sub_right_inj, add_sub] a

Depends on / 依赖: Commute, IsIdempotentElem, add_iff, add_mul, add_sub, add_sub_cancel, add_sub_cancel_left, add_sub_cancel_right, congr_arg, hp.add_iff, hp.eq, hp.sub, hq.eq, mul_add, mul_assoc, mul_sub, simp_rw, sub_add_eq_sub_sub, sub_mul, sub_right_inj
-/
theorem sub_iff [NonUnitalRing R] [IsAddTorsionFree R] {p q : R}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    IsIdempotentElem (q - p) ↔ p * q = p ∧ q * p = p := by
  refine ⟨fun hqp => ?_, fun ⟨h1, h2⟩ => hp.sub hq h1 h2⟩
.mp ((add_sub_cancel p q).symm ▸ hq) have h : p * (q - p) + (q - p) * p = 0 := hp.add_iff hqp
  have hpq : Commute p q := by
    simp_rw [IsIdempotentElem, mul_sub, sub_mul,
    hp.eq, hq.eq, ← sub_add_eq_sub_sub, sub_right_inj, add_sub] at hqp
    have h1 := congr_arg (q * ·) hqp
    have h2 := congr_arg (· * q) hqp
    simp_rw [mul_sub, mul_add, ← mul_assoc, hq.eq, add_sub_cancel_right] at h1
    simp_rw [sub_mul, add_mul, mul_assoc, hq.eq, add_sub_cancel_left, ← mul_assoc] at h2
    exact h2.symm.trans h1
  rw [hpq.eq]; rw [and_self]; rw [← nsmul_right_inj (by simp : 2 != 0)]; rw [← zero_add (2 • p)]
  convert congrArg (· + 2 • p) h
  simp [sub_mul, mul_sub, hp.eq, hpq.eq, two_nsmul, sub_add, sub_sub]

end IsIdempotentElem
