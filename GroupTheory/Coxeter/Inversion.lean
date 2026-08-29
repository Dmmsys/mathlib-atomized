/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee, Óscar Álvarez
-/
module

public import Mathlib.GroupTheory.Coxeter.Length
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.Group

/-!
# Reflections, inversions, and inversion sequences

Throughout this file, `B` is a type and `M : CoxeterMatrix B` is a Coxeter matrix.
`cs : CoxeterSystem M W` is a Coxeter system; that is, `W` is a group, and `cs` holds the data
of a group isomorphism `W ≃* M.group`, where `M.group` refers to the quotient of the free group on
`B` by the Coxeter relations given by the matrix `M`. See `Mathlib/GroupTheory/Coxeter/Basic.lean`
for more details.

We define a *reflection* (`CoxeterSystem.IsReflection`) to be an element of the form
$t = u s_i u^{-1}$, where $u \in W$ and $s_i$ is a simple reflection. We say that a reflection $t$
is a *left inversion* (`CoxeterSystem.IsLeftInversion`) of an element $w \in W$ if
$\ell(t w) < \ell(w)$, and we say it is a *right inversion* (`CoxeterSystem.IsRightInversion`) of
$w$ if $\ell(w t) > \ell(w)$. Here $\ell$ is the length function
(see `Mathlib/GroupTheory/Coxeter/Length.lean`).

Given a word, we define its *left inversion sequence* (`CoxeterSystem.leftInvSeq`) and its
*right inversion sequence* (`CoxeterSystem.rightInvSeq`). We prove that if a word is reduced, then
both of its inversion sequences contain no duplicates. In fact, the right (respectively, left)
inversion sequence of a reduced word for $w$ consists of all of the right (respectively, left)
inversions of $w$ in some order, but we do not prove that in this file.

## Main definitions

* `CoxeterSystem.IsReflection`
* `CoxeterSystem.IsLeftInversion`
* `CoxeterSystem.IsRightInversion`
* `CoxeterSystem.leftInvSeq`
* `CoxeterSystem.rightInvSeq`

## References

* [A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*](bjorner2005)

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

namespace CoxeterSystem

open List Matrix Function

variable {B : Type*}
variable {W : Type*} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s " => cs.simple
local prefix:100 "π " => cs.wordProd
local prefix:100 "ℓ " => cs.length

/--
Definition of `IsReflection` / `IsReflection` 的定义

English:
definition IsReflection
  signature: (t : W)
  body: exists w i, t = w * s i * w⁻¹

中文:
定义 IsReflection
  签名: (t : W)
  定义体: exists w i, t = w * s i * w⁻¹
-/
def IsReflection (t : W) : Prop := exists w i, t = w * s i * w⁻¹

/--
theorem `isReflection_simple` / 定理 `isReflection_simple`

English:
theorem isReflection_simple
  given: (i : B)
  statement: cs.IsReflection (s i)
  proof: by use 1, i; simp

中文:
定理 isReflection_simple
  条件: (i : B)
  结论: cs.IsReflection (s i)
  证明: by use 1, i; simp
-/
theorem isReflection_simple (i : B) : cs.IsReflection (s i) := by use 1, i; simp

namespace IsReflection

variable {cs}
variable {t : W} (ht : cs.IsReflection t)
include ht

/--
theorem `pow_two` / 定理 `pow_two`

English:
theorem pow_two
  statement: t ^ 2 = 1
  proof: by
  rcases ht with ⟨w, i, rfl⟩
  simp

中文:
定理 pow_two
  结论: t ^ 2 = 1
  证明: by
  rcases ht with ⟨w, i, rfl⟩
  simp
-/
theorem pow_two : t ^ 2 = 1 := by
  rcases ht with ⟨w, i, rfl⟩
  simp

/--
theorem `mul_self` / 定理 `mul_self`

English:
theorem mul_self
  statement: t * t = 1
  proof: by
  rcases ht with ⟨w, i, rfl⟩
  simp

中文:
定理 mul_self
  结论: t * t = 1
  证明: by
  rcases ht with ⟨w, i, rfl⟩
  simp
-/
theorem mul_self : t * t = 1 := by
  rcases ht with ⟨w, i, rfl⟩
  simp

/--
theorem `inv` / 定理 `inv`

English:
theorem inv
  statement: t⁻¹ = t
  proof: by
  rcases ht with ⟨w, i, rfl⟩
  simp [mul_assoc]

中文:
定理 inv
  结论: t⁻¹ = t
  证明: by
  rcases ht with ⟨w, i, rfl⟩
  simp [mul_assoc]

Depends on / 依赖: mul_assoc
-/
theorem inv : t⁻¹ = t := by
  rcases ht with ⟨w, i, rfl⟩
  simp [mul_assoc]

/--
theorem `isReflection_inv` / 定理 `isReflection_inv`

English:
theorem isReflection_inv
  statement: cs.IsReflection t⁻¹
  proof: by rwa [ht.inv]

中文:
定理 isReflection_inv
  结论: cs.IsReflection t⁻¹
  证明: by rwa [ht.inv]

Depends on / 依赖: ht.inv
-/
theorem isReflection_inv : cs.IsReflection t⁻¹ := by rwa [ht.inv]

/--
theorem `odd_length` / 定理 `odd_length`

English:
theorem odd_length
  statement: Odd (ℓ t)
  proof: by
  suffices cs.lengthParity t = Multiplicative.ofAdd 1 by
    simpa [lengthParity_eq_ofAdd_length, ZMod.natCast_eq_one_iff_odd]
  rcases ht with ⟨w, i, rfl⟩
  simp [lengthParity_simple]

中文:
定理 odd_length
  结论: Odd (ℓ t)
  证明: by
  suffices cs.lengthParity t = Multiplicative.ofAdd 1 by
    simpa [lengthParity_eq_ofAdd_length, ZMod.natCast_eq_one_iff_odd]
  rcases ht with ⟨w, i, rfl⟩
  simp [lengthParity_simple]

Depends on / 依赖: Multiplicative, Multiplicative.ofAdd, ZMod.natCast_eq_one_iff_odd, cs.lengthParity, lengthParity, lengthParity_eq_ofAdd_length, lengthParity_simple, natCast_eq_one_iff_odd
-/
theorem odd_length : Odd (ℓ t) := by
  suffices cs.lengthParity t = Multiplicative.ofAdd 1 by
    simpa [lengthParity_eq_ofAdd_length, ZMod.natCast_eq_one_iff_odd]
  rcases ht with ⟨w, i, rfl⟩
  simp [lengthParity_simple]

/--
theorem `length_mul_left_ne` / 定理 `length_mul_left_ne`

English:
theorem length_mul_left_ne
  given: (w : W)
  statement: ℓ (w * t) != ℓ w
  proof: by
  suffices cs.lengthParity (w * t) != cs.lengthParity w by
    contrapose this
    simp only [lengthParity_eq_ofAdd_length, this]
  rcases ht with ⟨w, i, rfl⟩
  simp [lengthParity_simple]

中文:
定理 length_mul_left_ne
  条件: (w : W)
  结论: ℓ (w * t) != ℓ w
  证明: by
  suffices cs.lengthParity (w * t) != cs.lengthParity w by
    contrapose this
    simp only [lengthParity_eq_ofAdd_length, this]
  rcases ht with ⟨w, i, rfl⟩
  simp [lengthParity_simple]

Depends on / 依赖: contrapose, cs.lengthParity, lengthParity, lengthParity_eq_ofAdd_length, lengthParity_simple
-/
theorem length_mul_left_ne (w : W) : ℓ (w * t) != ℓ w := by
  suffices cs.lengthParity (w * t) != cs.lengthParity w by
    contrapose this
    simp only [lengthParity_eq_ofAdd_length, this]
  rcases ht with ⟨w, i, rfl⟩
  simp [lengthParity_simple]

/--
theorem `length_mul_right_ne` / 定理 `length_mul_right_ne`

English:
theorem length_mul_right_ne
  given: (w : W)
  statement: ℓ (t * w) != ℓ w
  proof: by
  suffices cs.lengthParity (t * w) != cs.lengthParity w by
    contrapose this
    simp only [lengthParity_eq_ofAdd_length, this]
  rcases ht with ⟨w, i, rfl⟩
  simp [lengthParity_simple]

中文:
定理 length_mul_right_ne
  条件: (w : W)
  结论: ℓ (t * w) != ℓ w
  证明: by
  suffices cs.lengthParity (t * w) != cs.lengthParity w by
    contrapose this
    simp only [lengthParity_eq_ofAdd_length, this]
  rcases ht with ⟨w, i, rfl⟩
  simp [lengthParity_simple]

Depends on / 依赖: contrapose, cs.lengthParity, lengthParity, lengthParity_eq_ofAdd_length, lengthParity_simple
-/
theorem length_mul_right_ne (w : W) : ℓ (t * w) != ℓ w := by
  suffices cs.lengthParity (t * w) != cs.lengthParity w by
    contrapose this
    simp only [lengthParity_eq_ofAdd_length, this]
  rcases ht with ⟨w, i, rfl⟩
  simp [lengthParity_simple]

/--
theorem `conj` / 定理 `conj`

English:
theorem conj
  given: (w : W)
  statement: cs.IsReflection (w * t * w⁻¹)
  proof: by
  obtain ⟨u, i, rfl⟩ := ht
  use w * u, i
  group

中文:
定理 conj
  条件: (w : W)
  结论: cs.IsReflection (w * t * w⁻¹)
  证明: by
  obtain ⟨u, i, rfl⟩ := ht
  use w * u, i
  group
-/
theorem conj (w : W) : cs.IsReflection (w * t * w⁻¹) := by
  obtain ⟨u, i, rfl⟩ := ht
  use w * u, i
  group

end IsReflection

@[simp]
/--
theorem `isReflection_conj_iff` / 定理 `isReflection_conj_iff`

English:
theorem isReflection_conj_iff
  given: (w t : W)
  proof: by
  constructor
  · intro h
    simpa [← mul_assoc] using h.conj w⁻¹
  · exact IsReflection.conj (w := w)

中文:
定理 isReflection_conj_iff
  条件: (w t : W)
  证明: by
  constructor
  · intro h
    simpa [← mul_assoc] using h.conj w⁻¹
  · exact IsReflection.conj (w := w)

Depends on / 依赖: IsReflection, IsReflection.conj, h.conj, mul_assoc
-/
theorem isReflection_conj_iff (w t : W) :
    cs.IsReflection (w * t * w⁻¹) ↔ cs.IsReflection t := by
  constructor
  · intro h
    simpa [← mul_assoc] using h.conj w⁻¹
  · exact IsReflection.conj (w := w)

/--
Definition of `IsRightInversion` / `IsRightInversion` 的定义

English:
definition IsRightInversion
  signature: (w t : W)
  body: cs.IsReflection t ∧ ℓ (w * t) < ℓ w

中文:
定义 IsRightInversion
  签名: (w t : W)
  定义体: cs.IsReflection t ∧ ℓ (w * t) < ℓ w

Depends on / 依赖: IsReflection, cs.IsReflection
-/
def IsRightInversion (w t : W) : Prop := cs.IsReflection t ∧ ℓ (w * t) < ℓ w

/--
Definition of `IsLeftInversion` / `IsLeftInversion` 的定义

English:
definition IsLeftInversion
  signature: (w t : W)
  body: cs.IsReflection t ∧ ℓ (t * w) < ℓ w

中文:
定义 IsLeftInversion
  签名: (w t : W)
  定义体: cs.IsReflection t ∧ ℓ (t * w) < ℓ w

Depends on / 依赖: IsReflection, cs.IsReflection
-/
def IsLeftInversion (w t : W) : Prop := cs.IsReflection t ∧ ℓ (t * w) < ℓ w

/--
theorem `isRightInversion_inv_iff` / 定理 `isRightInversion_inv_iff`

English:
theorem isRightInversion_inv_iff
  given: {w t : W}
  proof: by
  apply and_congr_right
  intro ht
  rw [← length_inv]; rw [mul_inv_rev]; rw [inv_inv]; rw [ht.inv]; rw [cs.length_inv w]

中文:
定理 isRightInversion_inv_iff
  条件: {w t : W}
  证明: by
  apply and_congr_right
  intro ht
  rw [← length_inv]; rw [mul_inv_rev]; rw [inv_inv]; rw [ht.inv]; rw [cs.length_inv w]

Depends on / 依赖: and_congr_right, cs.length_inv, ht.inv, inv_inv, length_inv, mul_inv_rev
-/
theorem isRightInversion_inv_iff {w t : W} :
    cs.IsRightInversion w⁻¹ t ↔ cs.IsLeftInversion w t := by
  apply and_congr_right
  intro ht
  rw [← length_inv]; rw [mul_inv_rev]; rw [inv_inv]; rw [ht.inv]; rw [cs.length_inv w]

/--
theorem `isLeftInversion_inv_iff` / 定理 `isLeftInversion_inv_iff`

English:
theorem isLeftInversion_inv_iff
  given: {w t : W}
  proof: by
  convert! cs.isRightInversion_inv_iff.symm
  simp

中文:
定理 isLeftInversion_inv_iff
  条件: {w t : W}
  证明: by
  convert! cs.isRightInversion_inv_iff.symm
  simp

Depends on / 依赖: convert, cs.isRightInversion_inv_iff.symm, isRightInversion_inv_iff
-/
theorem isLeftInversion_inv_iff {w t : W} :
    cs.IsLeftInversion w⁻¹ t ↔ cs.IsRightInversion w t := by
  convert! cs.isRightInversion_inv_iff.symm
  simp

namespace IsReflection

variable {cs}
variable {t : W} (ht : cs.IsReflection t)
include ht

/--
theorem `isRightInversion_mul_left_iff` / 定理 `isRightInversion_mul_left_iff`

English:
theorem isRightInversion_mul_left_iff
  given: {w : W}
  proof: by
  unfold IsRightInversion
  simp only [mul_assoc, ht.mul_self, mul_one, ht, true_and, not_lt]
  constructor
  · exact le_of_lt
  · exact (lt_of_le_of_ne' · (ht.length_mul_left_ne w))

中文:
定理 isRightInversion_mul_left_iff
  条件: {w : W}
  证明: by
  unfold IsRightInversion
  simp only [mul_assoc, ht.mul_self, mul_one, ht, true_and, not_lt]
  constructor
  · exact le_of_lt
  · exact (lt_of_le_of_ne' · (ht.length_mul_left_ne w))

Depends on / 依赖: IsRightInversion, ht.length_mul_left_ne, ht.mul_self, le_of_lt, length_mul_left_ne, lt_of_le_of_ne, mul_assoc, mul_one, mul_self, not_lt, true_and
-/
theorem isRightInversion_mul_left_iff {w : W} :
    cs.IsRightInversion (w * t) t ↔ ¬cs.IsRightInversion w t := by
  unfold IsRightInversion
  simp only [mul_assoc, ht.mul_self, mul_one, ht, true_and, not_lt]
  constructor
  · exact le_of_lt
  · exact (lt_of_le_of_ne' · (ht.length_mul_left_ne w))

/--
theorem `not_isRightInversion_mul_left_iff` / 定理 `not_isRightInversion_mul_left_iff`

English:
theorem not_isRightInversion_mul_left_iff
  given: {w : W}
  proof: ht.isRightInversion_mul_left_iff.not_left

中文:
定理 not_isRightInversion_mul_left_iff
  条件: {w : W}
  证明: ht.isRightInversion_mul_left_iff.not_left

Depends on / 依赖: ht.isRightInversion_mul_left_iff.not_left, isRightInversion_mul_left_iff, not_left
-/
theorem not_isRightInversion_mul_left_iff {w : W} :
    ¬cs.IsRightInversion (w * t) t ↔ cs.IsRightInversion w t :=
  ht.isRightInversion_mul_left_iff.not_left

/--
theorem `isLeftInversion_mul_right_iff` / 定理 `isLeftInversion_mul_right_iff`

English:
theorem isLeftInversion_mul_right_iff
  given: {w : W}
  proof: by
  rw [← isRightInversion_inv_iff]; rw [← isRightInversion_inv_iff]; rw [mul_inv_rev]; rw [ht.inv]; rw [ht.isRightInversion_mul_left_iff]

中文:
定理 isLeftInversion_mul_right_iff
  条件: {w : W}
  证明: by
  rw [← isRightInversion_inv_iff]; rw [← isRightInversion_inv_iff]; rw [mul_inv_rev]; rw [ht.inv]; rw [ht.isRightInversion_mul_left_iff]

Depends on / 依赖: ht.inv, ht.isRightInversion_mul_left_iff, isRightInversion_inv_iff, isRightInversion_mul_left_iff, mul_inv_rev
-/
theorem isLeftInversion_mul_right_iff {w : W} :
    cs.IsLeftInversion (t * w) t ↔ ¬cs.IsLeftInversion w t := by
  rw [← isRightInversion_inv_iff]; rw [← isRightInversion_inv_iff]; rw [mul_inv_rev]; rw [ht.inv]; rw [ht.isRightInversion_mul_left_iff]

/--
theorem `not_isLeftInversion_mul_right_iff` / 定理 `not_isLeftInversion_mul_right_iff`

English:
theorem not_isLeftInversion_mul_right_iff
  given: {w : W}
  proof: ht.isLeftInversion_mul_right_iff.not_left

中文:
定理 not_isLeftInversion_mul_right_iff
  条件: {w : W}
  证明: ht.isLeftInversion_mul_right_iff.not_left

Depends on / 依赖: ht.isLeftInversion_mul_right_iff.not_left, isLeftInversion_mul_right_iff, not_left
-/
theorem not_isLeftInversion_mul_right_iff {w : W} :
    ¬cs.IsLeftInversion (t * w) t ↔ cs.IsLeftInversion w t :=
  ht.isLeftInversion_mul_right_iff.not_left

end IsReflection

@[simp]
/--
theorem `isRightInversion_simple_iff_isRightDescent` / 定理 `isRightInversion_simple_iff_isRightDescent`

English:
theorem isRightInversion_simple_iff_isRightDescent
  given: (w : W) (i : B)
  proof: by
  simp [IsRightInversion, IsRightDescent, cs.isReflection_simple i]

@[simp]

中文:
定理 isRightInversion_simple_iff_isRightDescent
  条件: (w : W) (i : B)
  证明: by
  simp [IsRightInversion, IsRightDescent, cs.isReflection_simple i]

@[simp]

Depends on / 依赖: IsRightDescent, IsRightInversion, cs.isReflection_simple, isReflection_simple
-/
theorem isRightInversion_simple_iff_isRightDescent (w : W) (i : B) :
    cs.IsRightInversion w (s i) ↔ cs.IsRightDescent w i := by
  simp [IsRightInversion, IsRightDescent, cs.isReflection_simple i]

@[simp]
/--
theorem `isLeftInversion_simple_iff_isLeftDescent` / 定理 `isLeftInversion_simple_iff_isLeftDescent`

English:
theorem isLeftInversion_simple_iff_isLeftDescent
  given: (w : W) (i : B)
  proof: by
  simp [IsLeftInversion, IsLeftDescent, cs.isReflection_simple i]

中文:
定理 isLeftInversion_simple_iff_isLeftDescent
  条件: (w : W) (i : B)
  证明: by
  simp [IsLeftInversion, IsLeftDescent, cs.isReflection_simple i]

Depends on / 依赖: IsLeftDescent, IsLeftInversion, cs.isReflection_simple, isReflection_simple
-/
theorem isLeftInversion_simple_iff_isLeftDescent (w : W) (i : B) :
    cs.IsLeftInversion w (s i) ↔ cs.IsLeftDescent w i := by
  simp [IsLeftInversion, IsLeftDescent, cs.isReflection_simple i]

/--
Definition of `rightInvSeq` / `rightInvSeq` 的定义

English:
definition rightInvSeq
  signature: (ω : List B)
  body: match ω with
  | [] => []
  | i :: ω => (π ω)⁻¹ * (s i) * (π ω) :: rightInvSeq ω

中文:
定义 rightInvSeq
  签名: (ω : 列表 B)
  定义体: match ω with
  | [] => []
  | i :: ω => (π ω)⁻¹ * (s i) * (π ω) :: rightInvSeq ω

Depends on / 依赖: rightInvSeq
-/
def rightInvSeq (ω : List B) : List W :=
  match ω with
  | [] => []
  | i :: ω => (π ω)⁻¹ * (s i) * (π ω) :: rightInvSeq ω

/--
Definition of `leftInvSeq` / `leftInvSeq` 的定义

English:
definition leftInvSeq
  signature: (ω : List B)
  body: match ω with
  | [] => []
  | i :: ω => s i :: List.map (MulAut.conj (s i)) (leftInvSeq ω)

local prefix:100 "ris " => cs.rightInvSeq
local prefix:100 "lis " => cs.leftInvSeq

中文:
定义 leftInvSeq
  签名: (ω : 列表 B)
  定义体: match ω with
  | [] => []
  | i :: ω => s i :: List.map (MulAut.conj (s i)) (leftInvSeq ω)

local prefix:100 "ris " => cs.rightInvSeq
local prefix:100 "lis " => cs.leftInvSeq

Depends on / 依赖: List.map, MulAut, MulAut.conj, leftInvSeq
-/
def leftInvSeq (ω : List B) : List W :=
  match ω with
  | [] => []
  | i :: ω => s i :: List.map (MulAut.conj (s i)) (leftInvSeq ω)

local prefix:100 "ris " => cs.rightInvSeq
local prefix:100 "lis " => cs.leftInvSeq

/--
theorem `rightInvSeq_nil` / 定理 `rightInvSeq_nil`

English:
theorem rightInvSeq_nil
  statement: ris [] = []
  proof: rfl

中文:
定理 rightInvSeq_nil
  结论: ris [] = []
  证明: rfl
-/
@[simp] theorem rightInvSeq_nil : ris [] = [] := rfl

/--
theorem `leftInvSeq_nil` / 定理 `leftInvSeq_nil`

English:
theorem leftInvSeq_nil
  statement: lis [] = []
  proof: rfl

中文:
定理 leftInvSeq_nil
  结论: lis [] = []
  证明: rfl
-/
@[simp] theorem leftInvSeq_nil : lis [] = [] := rfl

/--
theorem `rightInvSeq_singleton` / 定理 `rightInvSeq_singleton`

English:
theorem rightInvSeq_singleton
  given: (i : B)
  statement: ris [i] = [s i]
  proof: by simp [rightInvSeq]

中文:
定理 rightInvSeq_singleton
  条件: (i : B)
  结论: ris [i] = [s i]
  证明: by simp [rightInvSeq]
-/
@[simp] theorem rightInvSeq_singleton (i : B) : ris [i] = [s i] := by simp [rightInvSeq]

/--
theorem `leftInvSeq_singleton` / 定理 `leftInvSeq_singleton`

English:
theorem leftInvSeq_singleton
  given: (i : B)
  statement: lis [i] = [s i]
  proof: rfl

中文:
定理 leftInvSeq_singleton
  条件: (i : B)
  结论: lis [i] = [s i]
  证明: rfl
-/
@[simp] theorem leftInvSeq_singleton (i : B) : lis [i] = [s i] := rfl

/--
theorem `rightInvSeq_concat` / 定理 `rightInvSeq_concat`

English:
theorem rightInvSeq_concat
  given: (ω : List B) (i : B)
  proof: by
  induction ω with
  | nil => simp
  | cons j ω ih =>
    dsimp [rightInvSeq, concat]
    rw [ih]
    simp only [concat_eq_append, wordProd_append, wordProd_cons, wordProd_nil, mul_one, mul_inv_rev,
      inv_simple, map_cons, MulAut.conj_apply, cons_append, cons.injEq, and_true]
    group

中文:
定理 rightInvSeq_concat
  条件: (ω : 列表 B) (i : B)
  证明: by
  induction ω with
  | nil => simp
  | cons j ω ih =>
    dsimp [rightInvSeq, concat]
    rw [ih]
    simp only [concat_eq_append, wordProd_append, wordProd_cons, wordProd_nil, mul_one, mul_inv_rev,
      inv_simple, map_cons, MulAut.conj_apply, cons_append, cons.injEq, and_true]
    group

Depends on / 依赖: MulAut, MulAut.conj_apply, and_true, concat, concat_eq_append, conj_apply, cons.injEq, cons_append, inv_simple, map_cons, mul_inv_rev, mul_one, rightInvSeq, wordProd_append, wordProd_cons, wordProd_nil
-/
theorem rightInvSeq_concat (ω : List B) (i : B) :
    ris (ω.concat i) = (List.map (MulAut.conj (s i)) (ris ω)).concat (s i) := by
  induction ω with
  | nil => simp
  | cons j ω ih =>
    dsimp [rightInvSeq, concat]
    rw [ih]
    simp only [concat_eq_append, wordProd_append, wordProd_cons, wordProd_nil, mul_one, mul_inv_rev,
      inv_simple, map_cons, MulAut.conj_apply, cons_append, cons.injEq, and_true]
    group

/--
theorem `leftInvSeq_eq_reverse_rightInvSeq_reverse` / 定理 `leftInvSeq_eq_reverse_rightInvSeq_reverse`

English:
theorem leftInvSeq_eq_reverse_rightInvSeq_reverse
  given: (ω : List B)
  proof: by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [leftInvSeq]; rw [reverse_cons]; rw [← concat_eq_append]; rw [rightInvSeq_concat]; rw [ih]
    simp [map_reverse]

中文:
定理 leftInvSeq_eq_reverse_rightInvSeq_reverse
  条件: (ω : 列表 B)
  证明: by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [leftInvSeq]; rw [reverse_cons]; rw [← concat_eq_append]; rw [rightInvSeq_concat]; rw [ih]
    simp [map_reverse]
-/
private theorem leftInvSeq_eq_reverse_rightInvSeq_reverse (ω : List B) :
    lis ω = (ris ω.reverse).reverse := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [leftInvSeq]; rw [reverse_cons]; rw [← concat_eq_append]; rw [rightInvSeq_concat]; rw [ih]
    simp [map_reverse]

/--
theorem `leftInvSeq_concat` / 定理 `leftInvSeq_concat`

English:
theorem leftInvSeq_concat
  given: (ω : List B) (i : B)
  proof: by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse, rightInvSeq]

中文:
定理 leftInvSeq_concat
  条件: (ω : 列表 B) (i : B)
  证明: by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse, rightInvSeq]

Depends on / 依赖: leftInvSeq_eq_reverse_rightInvSeq_reverse, rightInvSeq
-/
theorem leftInvSeq_concat (ω : List B) (i : B) :
    lis (ω.concat i) = (lis ω).concat ((π ω) * (s i) * (π ω)⁻¹) := by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse, rightInvSeq]

/--
theorem `rightInvSeq_reverse` / 定理 `rightInvSeq_reverse`

English:
theorem rightInvSeq_reverse
  given: (ω : List B)
  proof: by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse]

中文:
定理 rightInvSeq_reverse
  条件: (ω : 列表 B)
  证明: by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse]

Depends on / 依赖: leftInvSeq_eq_reverse_rightInvSeq_reverse
-/
theorem rightInvSeq_reverse (ω : List B) :
    ris (ω.reverse) = (lis ω).reverse := by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse]

/--
theorem `leftInvSeq_reverse` / 定理 `leftInvSeq_reverse`

English:
theorem leftInvSeq_reverse
  given: (ω : List B)
  proof: by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse]

中文:
定理 leftInvSeq_reverse
  条件: (ω : 列表 B)
  证明: by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse]

Depends on / 依赖: leftInvSeq_eq_reverse_rightInvSeq_reverse
-/
theorem leftInvSeq_reverse (ω : List B) :
    lis (ω.reverse) = (ris ω).reverse := by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse]

/--
theorem `length_rightInvSeq` / 定理 `length_rightInvSeq`

English:
theorem length_rightInvSeq
  given: (ω : List B)
  statement: (ris ω).length = ω.length
  proof: by
  induction ω with
  | nil => simp
  | cons i ω ih => simpa [rightInvSeq]

中文:
定理 length_rightInvSeq
  条件: (ω : 列表 B)
  结论: (ris ω).length = ω.length
  证明: by
  induction ω with
  | nil => simp
  | cons i ω ih => simpa [rightInvSeq]
-/
@[simp] theorem length_rightInvSeq (ω : List B) : (ris ω).length = ω.length := by
  induction ω with
  | nil => simp
  | cons i ω ih => simpa [rightInvSeq]

/--
theorem `length_leftInvSeq` / 定理 `length_leftInvSeq`

English:
theorem length_leftInvSeq
  given: (ω : List B)
  statement: (lis ω).length = ω.length
  proof: by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse]

中文:
定理 length_leftInvSeq
  条件: (ω : 列表 B)
  结论: (lis ω).length = ω.length
  证明: by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse]
-/
@[simp] theorem length_leftInvSeq (ω : List B) : (lis ω).length = ω.length := by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse]

/--
theorem `getD_rightInvSeq` / 定理 `getD_rightInvSeq`

English:
theorem getD_rightInvSeq
  given: (ω : List B) (j : Nat)
  proof: by
  induction ω generalizing j with
  | nil => simp
  | cons i ω ih =>
    dsimp only [rightInvSeq]
    rcases j with _ | j'
    · simp
    · simp only [getD_eq_getElem?_getD] at ih
      simp [ih j']

中文:
定理 getD_rightInvSeq
  条件: (ω : 列表 B) (j : 自然数)
  证明: by
  induction ω generalizing j with
  | nil => simp
  | cons i ω ih =>
    dsimp only [rightInvSeq]
    rcases j with _ | j'
    · simp
    · simp only [getD_eq_getElem?_getD] at ih
      simp [ih j']

Depends on / 依赖: _getD, generalizing, getD_eq_getElem, rightInvSeq
-/
theorem getD_rightInvSeq (ω : List B) (j : Nat) :
    (ris ω).getD j 1 =
      (π (ω.drop (j + 1)))⁻¹
        * (Option.map (cs.simple) ω[j]?).getD 1
        * π (ω.drop (j + 1)) := by
  induction ω generalizing j with
  | nil => simp
  | cons i ω ih =>
    dsimp only [rightInvSeq]
    rcases j with _ | j'
    · simp
    · simp only [getD_eq_getElem?_getD] at ih
      simp [ih j']

/--
lemma `getElem_rightInvSeq` / 引理 `getElem_rightInvSeq`

English:
lemma getElem_rightInvSeq
  given: (ω : List B) (j : Nat) (h : j < ω.length)
  proof: by
  rw [← List.getD_eq_getElem (ris ω) 1]; rw [getD_rightInvSeq]

中文:
引理 getElem_rightInvSeq
  条件: (ω : 列表 B) (j : 自然数) (h : j < ω.length)
  证明: by
  rw [← List.getD_eq_getElem (ris ω) 1]; rw [getD_rightInvSeq]

Depends on / 依赖: List.getD_eq_getElem, getD_eq_getElem, getD_rightInvSeq
-/
lemma getElem_rightInvSeq (ω : List B) (j : Nat) (h : j < ω.length) :
    (ris ω)[j]'(by simp [h]) =
    (π (ω.drop (j + 1)))⁻¹
      * (Option.map (cs.simple) ω[j]?).getD 1
      * π (ω.drop (j + 1)) := by
  rw [← List.getD_eq_getElem (ris ω) 1]; rw [getD_rightInvSeq]

/--
theorem `getD_leftInvSeq` / 定理 `getD_leftInvSeq`

English:
theorem getD_leftInvSeq
  given: (ω : List B) (j : Nat)
  proof: by
  induction ω generalizing j with
  | nil => simp
  | cons i ω ih =>
    dsimp [leftInvSeq]
    rcases j with _ | j'
    · simp
    · rw [getD_cons_succ]
      rw [(by simp : 1 = ⇑(MulAut.conj (s i)) 1)]
      rw [getD_map]
      rw [ih j']
      simp [← mul_assoc, wordProd_cons]

中文:
定理 getD_leftInvSeq
  条件: (ω : 列表 B) (j : 自然数)
  证明: by
  induction ω generalizing j with
  | nil => simp
  | cons i ω ih =>
    dsimp [leftInvSeq]
    rcases j with _ | j'
    · simp
    · rw [getD_cons_succ]
      rw [(by simp : 1 = ⇑(MulAut.conj (s i)) 1)]
      rw [getD_map]
      rw [ih j']
      simp [← mul_assoc, wordProd_cons]

Depends on / 依赖: MulAut, MulAut.conj, generalizing, getD_cons_succ, getD_map, leftInvSeq, mul_assoc, wordProd_cons
-/
theorem getD_leftInvSeq (ω : List B) (j : Nat) :
    (lis ω).getD j 1 =
      π (ω.take j)
        * (Option.map (cs.simple) ω[j]?).getD 1
        * (π (ω.take j))⁻¹ := by
  induction ω generalizing j with
  | nil => simp
  | cons i ω ih =>
    dsimp [leftInvSeq]
    rcases j with _ | j'
    · simp
    · rw [getD_cons_succ]
      rw [(by simp : 1 = ⇑(MulAut.conj (s i)) 1)]
      rw [getD_map]
      rw [ih j']
      simp [← mul_assoc, wordProd_cons]

/--
lemma `getElem_leftInvSeq` / 引理 `getElem_leftInvSeq`

English:
lemma getElem_leftInvSeq
  given: (ω : List B) (j : Nat) (h : j < ω.length)
  proof: by
  rw [← List.getD_eq_getElem (lis ω) 1]; rw [getD_leftInvSeq]
  simp [h]

中文:
引理 getElem_leftInvSeq
  条件: (ω : 列表 B) (j : 自然数) (h : j < ω.length)
  证明: by
  rw [← List.getD_eq_getElem (lis ω) 1]; rw [getD_leftInvSeq]
  simp [h]

Depends on / 依赖: List.getD_eq_getElem, getD_eq_getElem, getD_leftInvSeq
-/
lemma getElem_leftInvSeq (ω : List B) (j : Nat) (h : j < ω.length) :
    (lis ω)[j]'(by simp [h]) =
    cs.wordProd (List.take j ω) * s ω[j] * (cs.wordProd (List.take j ω))⁻¹ := by
  rw [← List.getD_eq_getElem (lis ω) 1]; rw [getD_leftInvSeq]
  simp [h]

/--
theorem `getD_rightInvSeq_mul_self` / 定理 `getD_rightInvSeq_mul_self`

English:
theorem getD_rightInvSeq_mul_self
  given: (ω : List B) (j : Nat)
  proof: by
  simp_rw [getD_rightInvSeq, mul_assoc]
  rcases em (j < ω.length) with hj | nhj
  · rw [getElem?_eq_getElem hj]
    simp [← mul_assoc]
  · rw [getElem?_eq_none_iff.mpr (by lia)]
    simp

中文:
定理 getD_rightInvSeq_mul_self
  条件: (ω : 列表 B) (j : 自然数)
  证明: by
  simp_rw [getD_rightInvSeq, mul_assoc]
  rcases em (j < ω.length) with hj | nhj
  · rw [getElem?_eq_getElem hj]
    simp [← mul_assoc]
  · rw [getElem?_eq_none_iff.mpr (by lia)]
    simp

Depends on / 依赖: _eq_getElem, _eq_none_iff, _eq_none_iff.mpr, getD_rightInvSeq, getElem, length, mul_assoc, simp_rw
-/
theorem getD_rightInvSeq_mul_self (ω : List B) (j : Nat) :
    ((ris ω).getD j 1) * ((ris ω).getD j 1) = 1 := by
  simp_rw [getD_rightInvSeq, mul_assoc]
  rcases em (j < ω.length) with hj | nhj
  · rw [getElem?_eq_getElem hj]
    simp [← mul_assoc]
  · rw [getElem?_eq_none_iff.mpr (by lia)]
    simp

/--
theorem `getD_leftInvSeq_mul_self` / 定理 `getD_leftInvSeq_mul_self`

English:
theorem getD_leftInvSeq_mul_self
  given: (ω : List B) (j : Nat)
  proof: by
  simp_rw [getD_leftInvSeq, mul_assoc]
  rcases em (j < ω.length) with hj | nhj
  · rw [getElem?_eq_getElem hj]
    simp [← mul_assoc]
  · rw [getElem?_eq_none_iff.mpr (by lia)]
    simp

中文:
定理 getD_leftInvSeq_mul_self
  条件: (ω : 列表 B) (j : 自然数)
  证明: by
  simp_rw [getD_leftInvSeq, mul_assoc]
  rcases em (j < ω.length) with hj | nhj
  · rw [getElem?_eq_getElem hj]
    simp [← mul_assoc]
  · rw [getElem?_eq_none_iff.mpr (by lia)]
    simp

Depends on / 依赖: _eq_getElem, _eq_none_iff, _eq_none_iff.mpr, getD_leftInvSeq, getElem, length, mul_assoc, simp_rw
-/
theorem getD_leftInvSeq_mul_self (ω : List B) (j : Nat) :
    ((lis ω).getD j 1) * ((lis ω).getD j 1) = 1 := by
  simp_rw [getD_leftInvSeq, mul_assoc]
  rcases em (j < ω.length) with hj | nhj
  · rw [getElem?_eq_getElem hj]
    simp [← mul_assoc]
  · rw [getElem?_eq_none_iff.mpr (by lia)]
    simp

/--
theorem `rightInvSeq_drop` / 定理 `rightInvSeq_drop`

English:
theorem rightInvSeq_drop
  given: (ω : List B) (j : Nat)
  proof: by
  induction j generalizing ω with
  | zero => simp
  | succ j ih₁ =>
    induction ω with
    | nil => simp
    | cons k ω _ => rw [drop_succ_cons, ih₁ ω, rightInvSeq, drop_succ_cons]

中文:
定理 rightInvSeq_drop
  条件: (ω : 列表 B) (j : 自然数)
  证明: by
  induction j generalizing ω with
  | zero => simp
  | succ j ih₁ =>
    induction ω with
    | nil => simp
    | cons k ω _ => rw [drop_succ_cons, ih₁ ω, rightInvSeq, drop_succ_cons]

Depends on / 依赖: drop_succ_cons, generalizing, rightInvSeq
-/
theorem rightInvSeq_drop (ω : List B) (j : Nat) :
    ris (ω.drop j) = (ris ω).drop j := by
  induction j generalizing ω with
  | zero => simp
  | succ j ih₁ =>
    induction ω with
    | nil => simp
    | cons k ω _ => rw [drop_succ_cons, ih₁ ω, rightInvSeq, drop_succ_cons]

/--
theorem `leftInvSeq_take` / 定理 `leftInvSeq_take`

English:
theorem leftInvSeq_take
  given: (ω : List B) (j : Nat)
  proof: by
  simp only [leftInvSeq_eq_reverse_rightInvSeq_reverse]
  rw [List.take_reverse]
  nth_rw 1 [← List.reverse_reverse ω]
  rw [List.take_reverse]
  simp [rightInvSeq_drop]

中文:
定理 leftInvSeq_take
  条件: (ω : 列表 B) (j : 自然数)
  证明: by
  simp only [leftInvSeq_eq_reverse_rightInvSeq_reverse]
  rw [List.take_reverse]
  nth_rw 1 [← List.reverse_reverse ω]
  rw [List.take_reverse]
  simp [rightInvSeq_drop]

Depends on / 依赖: List.reverse_reverse, List.take_reverse, leftInvSeq_eq_reverse_rightInvSeq_reverse, nth_rw, reverse_reverse, rightInvSeq_drop, take_reverse
-/
theorem leftInvSeq_take (ω : List B) (j : Nat) :
    lis (ω.take j) = (lis ω).take j := by
  simp only [leftInvSeq_eq_reverse_rightInvSeq_reverse]
  rw [List.take_reverse]
  nth_rw 1 [← List.reverse_reverse ω]
  rw [List.take_reverse]
  simp [rightInvSeq_drop]

/--
theorem `isReflection_of_mem_rightInvSeq` / 定理 `isReflection_of_mem_rightInvSeq`

English:
theorem isReflection_of_mem_rightInvSeq
  given: (ω : List B) {t : W} (ht : t in ris ω)
  proof: by
  induction ω with
  | nil => simp at ht
  | cons i ω ih =>
    dsimp [rightInvSeq] at ht
    rcases ht with _ | ⟨_, mem⟩
    · use (π ω)⁻¹, i
      group
    · exact ih mem

中文:
定理 isReflection_of_mem_rightInvSeq
  条件: (ω : 列表 B) {t : W} (ht : t in ris ω)
  证明: by
  induction ω with
  | nil => simp at ht
  | cons i ω ih =>
    dsimp [rightInvSeq] at ht
    rcases ht with _ | ⟨_, mem⟩
    · use (π ω)⁻¹, i
      group
    · exact ih mem

Depends on / 依赖: rightInvSeq
-/
theorem isReflection_of_mem_rightInvSeq (ω : List B) {t : W} (ht : t in ris ω) :
    cs.IsReflection t := by
  induction ω with
  | nil => simp at ht
  | cons i ω ih =>
    dsimp [rightInvSeq] at ht
    rcases ht with _ | ⟨_, mem⟩
    · use (π ω)⁻¹, i
      group
    · exact ih mem

/--
theorem `isReflection_of_mem_leftInvSeq` / 定理 `isReflection_of_mem_leftInvSeq`

English:
theorem isReflection_of_mem_leftInvSeq
  given: (ω : List B) {t : W} (ht : t in lis ω)
  proof: by
  simp only [leftInvSeq_eq_reverse_rightInvSeq_reverse, mem_reverse] at ht
  exact cs.isReflection_of_mem_rightInvSeq ω.reverse ht

中文:
定理 isReflection_of_mem_leftInvSeq
  条件: (ω : 列表 B) {t : W} (ht : t in lis ω)
  证明: by
  simp only [leftInvSeq_eq_reverse_rightInvSeq_reverse, mem_reverse] at ht
  exact cs.isReflection_of_mem_rightInvSeq ω.reverse ht

Depends on / 依赖: Fintype, Fintype.ofFinite, MulOpposite, MulOpposite.isStablyFiniteRing_iff, RingEquiv, RingEquiv.isStablyFiniteRing_iff, classical, cs.isReflection_of_mem_rightInvSeq, infer_instance, isReflection_of_mem_rightInvSeq, isStablyFiniteRing_iff, leftInvSeq_eq_reverse_rightInvSeq_reverse, matrixRingEquivEndVecMulOpposite, mem_reverse, ofFinite, reverse
-/
theorem isReflection_of_mem_leftInvSeq (ω : List B) {t : W} (ht : t in lis ω) :
    cs.IsReflection t := by
  simp only [leftInvSeq_eq_reverse_rightInvSeq_reverse, mem_reverse] at ht
  exact cs.isReflection_of_mem_rightInvSeq ω.reverse ht

/--
theorem `wordProd_mul_getD_rightInvSeq` / 定理 `wordProd_mul_getD_rightInvSeq`

English:
theorem wordProd_mul_getD_rightInvSeq
  given: (ω : List B) (j : Nat)
  proof: by
  rw [getD_rightInvSeq]; rw [eraseIdx_eq_take_drop_succ]
  nth_rw 1 [← take_append_drop (j + 1) ω]
  rw [take_add_one]
  obtain lt | le := lt_or_ge j ω.length
  · simp only [getElem?_eq_getElem lt, wordProd_append, mul_assoc]
    simp
  · simp only [getElem?_eq_none le]
    simp

中文:
定理 wordProd_mul_getD_rightInvSeq
  条件: (ω : 列表 B) (j : 自然数)
  证明: by
  rw [getD_rightInvSeq]; rw [eraseIdx_eq_take_drop_succ]
  nth_rw 1 [← take_append_drop (j + 1) ω]
  rw [take_add_one]
  obtain lt | le := lt_or_ge j ω.length
  · simp only [getElem?_eq_getElem lt, wordProd_append, mul_assoc]
    simp
  · simp only [getElem?_eq_none le]
    simp

Depends on / 依赖: _eq_getElem, _eq_none, eraseIdx_eq_take_drop_succ, getD_rightInvSeq, getElem, length, lt_or_ge, mul_assoc, nth_rw, take_add_one, take_append_drop, wordProd_append
-/
theorem wordProd_mul_getD_rightInvSeq (ω : List B) (j : Nat) :
    π ω * ((ris ω).getD j 1) = π (ω.eraseIdx j) := by
  rw [getD_rightInvSeq]; rw [eraseIdx_eq_take_drop_succ]
  nth_rw 1 [← take_append_drop (j + 1) ω]
  rw [take_add_one]
  obtain lt | le := lt_or_ge j ω.length
  · simp only [getElem?_eq_getElem lt, wordProd_append, mul_assoc]
    simp
  · simp only [getElem?_eq_none le]
    simp

/--
theorem `getD_leftInvSeq_mul_wordProd` / 定理 `getD_leftInvSeq_mul_wordProd`

English:
theorem getD_leftInvSeq_mul_wordProd
  given: (ω : List B) (j : Nat)
  proof: by
  rw [getD_leftInvSeq]; rw [eraseIdx_eq_take_drop_succ]
  nth_rw 4 [← take_append_drop (j + 1) ω]
  rw [take_add_one]
  obtain lt | le := lt_or_ge j ω.length
  · simp only [getElem?_eq_getElem lt, wordProd_append, mul_assoc]
    simp
  · simp only [getElem?_eq_none le]
    simp

中文:
定理 getD_leftInvSeq_mul_wordProd
  条件: (ω : 列表 B) (j : 自然数)
  证明: by
  rw [getD_leftInvSeq]; rw [eraseIdx_eq_take_drop_succ]
  nth_rw 4 [← take_append_drop (j + 1) ω]
  rw [take_add_one]
  obtain lt | le := lt_or_ge j ω.length
  · simp only [getElem?_eq_getElem lt, wordProd_append, mul_assoc]
    simp
  · simp only [getElem?_eq_none le]
    simp

Depends on / 依赖: _eq_getElem, _eq_none, eraseIdx_eq_take_drop_succ, getD_leftInvSeq, getElem, length, lt_or_ge, mul_assoc, nth_rw, take_add_one, take_append_drop, wordProd_append
-/
theorem getD_leftInvSeq_mul_wordProd (ω : List B) (j : Nat) :
    ((lis ω).getD j 1) * π ω = π (ω.eraseIdx j) := by
  rw [getD_leftInvSeq]; rw [eraseIdx_eq_take_drop_succ]
  nth_rw 4 [← take_append_drop (j + 1) ω]
  rw [take_add_one]
  obtain lt | le := lt_or_ge j ω.length
  · simp only [getElem?_eq_getElem lt, wordProd_append, mul_assoc]
    simp
  · simp only [getElem?_eq_none le]
    simp

/--
theorem `isRightInversion_of_mem_rightInvSeq` / 定理 `isRightInversion_of_mem_rightInvSeq`

English:
theorem isRightInversion_of_mem_rightInvSeq
  statement: {ω : List B} (hω : cs.IsReduced ω) {t : W}
  proof: by
  constructor
  · exact cs.isReflection_of_mem_rightInvSeq ω ht
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ht
    rw [← List.getD_eq_getElem _ 1 hj]; rw [wordProd_mul_getD_rightInvSeq]
    rw [cs.length_rightInvSeq] at hj
    calc
      ℓ (π (ω.eraseIdx j))
      _ <= (ω.eraseIdx j).length := cs.length_wordProd_le _
      _ < ω.length := by rw [← List.length_eraseIdx_add_one hj]; exact lt_add_one _
      _ = ℓ (π ω) := hω.symm

中文:
定理 isRightInversion_of_mem_rightInvSeq
  结论: {ω : 列表 B} (hω : cs.是既约 ω) {t : W}
  证明: by
  constructor
  · exact cs.isReflection_of_mem_rightInvSeq ω ht
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ht
    rw [← List.getD_eq_getElem _ 1 hj]; rw [wordProd_mul_getD_rightInvSeq]
    rw [cs.length_rightInvSeq] at hj
    calc
      ℓ (π (ω.eraseIdx j))
      _ <= (ω.eraseIdx j).length := cs.length_wordProd_le _
      _ < ω.length := by rw [← List.length_eraseIdx_add_one hj]; exact lt_add_one _
      _ = ℓ (π ω) := hω.symm

Depends on / 依赖: List.getD_eq_getElem, List.length_eraseIdx_add_one, List.mem_iff_getElem.mp, cs.isReflection_of_mem_rightInvSeq, cs.length_rightInvSeq, cs.length_wordProd_le, eraseIdx, getD_eq_getElem, isReflection_of_mem_rightInvSeq, length, length_eraseIdx_add_one, length_rightInvSeq, length_wordProd_le, lt_add_one, mem_iff_getElem, wordProd_mul_getD_rightInvSeq
-/
theorem isRightInversion_of_mem_rightInvSeq {ω : List B} (hω : cs.IsReduced ω) {t : W}
    (ht : t in ris ω) : cs.IsRightInversion (π ω) t := by
  constructor
  · exact cs.isReflection_of_mem_rightInvSeq ω ht
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ht
    rw [← List.getD_eq_getElem _ 1 hj]; rw [wordProd_mul_getD_rightInvSeq]
    rw [cs.length_rightInvSeq] at hj
    calc
      ℓ (π (ω.eraseIdx j))
      _ <= (ω.eraseIdx j).length := cs.length_wordProd_le _
      _ < ω.length := by rw [← List.length_eraseIdx_add_one hj]; exact lt_add_one _
      _ = ℓ (π ω) := hω.symm

/--
theorem `isLeftInversion_of_mem_leftInvSeq` / 定理 `isLeftInversion_of_mem_leftInvSeq`

English:
theorem isLeftInversion_of_mem_leftInvSeq
  statement: {ω : List B} (hω : cs.IsReduced ω) {t : W}
  proof: by
  constructor
  · exact cs.isReflection_of_mem_leftInvSeq ω ht
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ht
    rw [← List.getD_eq_getElem _ 1 hj]; rw [getD_leftInvSeq_mul_wordProd]
    rw [cs.length_leftInvSeq] at hj
    calc
      ℓ (π (ω.eraseIdx j))
      _ <= (ω.eraseIdx j).length := cs.length_wordProd_le _
      _ < ω.length := by rw [← List.length_eraseIdx_add_one hj]; exact lt_add_one _
      _ = ℓ (π ω) := hω.symm

中文:
定理 isLeftInversion_of_mem_leftInvSeq
  结论: {ω : 列表 B} (hω : cs.是既约 ω) {t : W}
  证明: by
  constructor
  · exact cs.isReflection_of_mem_leftInvSeq ω ht
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ht
    rw [← List.getD_eq_getElem _ 1 hj]; rw [getD_leftInvSeq_mul_wordProd]
    rw [cs.length_leftInvSeq] at hj
    calc
      ℓ (π (ω.eraseIdx j))
      _ <= (ω.eraseIdx j).length := cs.length_wordProd_le _
      _ < ω.length := by rw [← List.length_eraseIdx_add_one hj]; exact lt_add_one _
      _ = ℓ (π ω) := hω.symm

Depends on / 依赖: List.getD_eq_getElem, List.length_eraseIdx_add_one, List.mem_iff_getElem.mp, cs.isReflection_of_mem_leftInvSeq, cs.length_leftInvSeq, cs.length_wordProd_le, eraseIdx, getD_eq_getElem, getD_leftInvSeq_mul_wordProd, isReflection_of_mem_leftInvSeq, length, length_eraseIdx_add_one, length_leftInvSeq, length_wordProd_le, lt_add_one, mem_iff_getElem
-/
theorem isLeftInversion_of_mem_leftInvSeq {ω : List B} (hω : cs.IsReduced ω) {t : W}
    (ht : t in lis ω) : cs.IsLeftInversion (π ω) t := by
  constructor
  · exact cs.isReflection_of_mem_leftInvSeq ω ht
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ht
    rw [← List.getD_eq_getElem _ 1 hj]; rw [getD_leftInvSeq_mul_wordProd]
    rw [cs.length_leftInvSeq] at hj
    calc
      ℓ (π (ω.eraseIdx j))
      _ <= (ω.eraseIdx j).length := cs.length_wordProd_le _
      _ < ω.length := by rw [← List.length_eraseIdx_add_one hj]; exact lt_add_one _
      _ = ℓ (π ω) := hω.symm

/--
theorem `prod_rightInvSeq` / 定理 `prod_rightInvSeq`

English:
theorem prod_rightInvSeq
  given: (ω : List B)
  statement: prod (ris ω) = (π ω)⁻¹
  proof: by
  induction ω with
  | nil => simp
  | cons i ω ih => simp [rightInvSeq, ih, wordProd_cons]

中文:
定理 prod_rightInvSeq
  条件: (ω : 列表 B)
  结论: 乘积 (ris ω) = (π ω)⁻¹
  证明: by
  induction ω with
  | nil => simp
  | cons i ω ih => simp [rightInvSeq, ih, wordProd_cons]

Depends on / 依赖: rightInvSeq, wordProd_cons
-/
theorem prod_rightInvSeq (ω : List B) : prod (ris ω) = (π ω)⁻¹ := by
  induction ω with
  | nil => simp
  | cons i ω ih => simp [rightInvSeq, ih, wordProd_cons]

/--
theorem `prod_leftInvSeq` / 定理 `prod_leftInvSeq`

English:
theorem prod_leftInvSeq
  given: (ω : List B)
  statement: prod (lis ω) = (π ω)⁻¹
  proof: by
  simp only [leftInvSeq_eq_reverse_rightInvSeq_reverse, prod_reverse_noncomm, inv_inj]
  have : List.map (fun x => x⁻¹) (ris ω.reverse) = ris ω.reverse := calc
    List.map (fun x => x⁻¹) (ris ω.reverse)
    _ = List.map id (ris ω.reverse) := by
        apply List.map_congr_left
        intro t ht
        exact (cs.isReflection_of_mem_rightInvSeq _ ht).inv
    _ = ris ω.reverse := map_id _
  rw [this]
  nth_rw 2 [← reverse_reverse ω]
  rw [wordProd_reverse]
  exact cs.prod_rightInvSeq _

中文:
定理 prod_leftInvSeq
  条件: (ω : 列表 B)
  结论: 乘积 (lis ω) = (π ω)⁻¹
  证明: by
  simp only [leftInvSeq_eq_reverse_rightInvSeq_reverse, prod_reverse_noncomm, inv_inj]
  have : List.map (fun x => x⁻¹) (ris ω.reverse) = ris ω.reverse := calc
    List.map (fun x => x⁻¹) (ris ω.reverse)
    _ = List.map id (ris ω.reverse) := by
        apply List.map_congr_left
        intro t ht
        exact (cs.isReflection_of_mem_rightInvSeq _ ht).inv
    _ = ris ω.reverse := map_id _
  rw [this]
  nth_rw 2 [← reverse_reverse ω]
  rw [wordProd_reverse]
  exact cs.prod_rightInvSeq _

Depends on / 依赖: List.map, List.map_congr_left, cs.isReflection_of_mem_rightInvSeq, cs.prod_rightInvSeq, inv_inj, isReflection_of_mem_rightInvSeq, leftInvSeq_eq_reverse_rightInvSeq_reverse, map_congr_left, map_id, nth_rw, prod_reverse_noncomm, prod_rightInvSeq, reverse, reverse_reverse, wordProd_reverse
-/
theorem prod_leftInvSeq (ω : List B) : prod (lis ω) = (π ω)⁻¹ := by
  simp only [leftInvSeq_eq_reverse_rightInvSeq_reverse, prod_reverse_noncomm, inv_inj]
  have : List.map (fun x => x⁻¹) (ris ω.reverse) = ris ω.reverse := calc
    List.map (fun x => x⁻¹) (ris ω.reverse)
    _ = List.map id (ris ω.reverse) := by
        apply List.map_congr_left
        intro t ht
        exact (cs.isReflection_of_mem_rightInvSeq _ ht).inv
    _ = ris ω.reverse := map_id _
  rw [this]
  nth_rw 2 [← reverse_reverse ω]
  rw [wordProd_reverse]
  exact cs.prod_rightInvSeq _

/--
theorem `IsReduced.nodup_rightInvSeq` / 定理 `IsReduced.nodup_rightInvSeq`

English:
theorem IsReduced.nodup_rightInvSeq
  given: {ω : List B} (rω : cs.IsReduced ω)
  statement: List.Nodup (ris ω)
  proof: by
  apply List.nodup_iff_getElem?_ne_getElem?.mpr
  intro j j' j_lt_j' j'_lt_length (dup : (rightInvSeq cs ω)[j]? = (rightInvSeq cs ω)[j']?)
  show False
  replace j'_lt_length : j' < List.length ω := by simpa using j'_lt_length
  rw [getElem?_eq_getElem (by simp; lia)]; rw [getElem?_eq_getElem (by simp; lia)] at dup
  apply Option.some_injective at dup
  rw [← getD_eq_getElem _ 1]; rw [← getD_eq_getElem _ 1] at dup
  set! t := (ris ω).getD j 1 with h₁
  set! t' := (ris (ω.eraseIdx j)).getD (j' - 1) 1 with h₂
  have h₃ : t' = (ris ω).getD j' 1 := by
    grind only [cs.getD_rightInvSeq, = eraseIdx_eq_take_drop_succ, = getElem?_eraseIdx,
      = drop_append, drop_of_length_le, drop_drop, = length_append, = length_take, = length_drop,
      = min_def]
  have h₄ : t * t' = 1 := by
    rw [h₁]; rw [h₃]; rw [dup]
    exact cs.getD_rightInvSeq_mul_self _ _
  have h₅ := calc
    π ω = π ω * t * t' := by rw [mul_assoc, h₄]; group
    _ = (π (ω.eraseIdx j)) * t' :=
        congrArg (· * t') (cs.wordProd_mul_getD_rightInvSeq _ _)
    _ = π ((ω.eraseIdx j).eraseIdx (j' - 1)) :=
        cs.wordProd_mul_getD_rightInvSeq _ _
  have h₆ := calc
    ω.length = ℓ (π ω) := rω.symm
    _ = ℓ (π ((ω.eraseIdx j).eraseIdx (j' - 1))) := congrArg cs.length h₅
    _ <= ((ω.eraseIdx j).eraseIdx (j' - 1)).length := cs.length_wordProd_le _
  grind

中文:
定理 是既约.nodup_rightInvSeq
  条件: {ω : 列表 B} (rω : cs.是既约 ω)
  结论: 列表.Nodup (ris ω)
  证明: by
  apply List.nodup_iff_getElem?_ne_getElem?.mpr
  intro j j' j_lt_j' j'_lt_length (dup : (rightInvSeq cs ω)[j]? = (rightInvSeq cs ω)[j']?)
  show False
  replace j'_lt_length : j' < List.length ω := by simpa using j'_lt_length
  rw [getElem?_eq_getElem (by simp; lia)]; rw [getElem?_eq_getElem (by simp; lia)] at dup
  apply Option.some_injective at dup
  rw [← getD_eq_getElem _ 1]; rw [← getD_eq_getElem _ 1] at dup
  set! t := (ris ω).getD j 1 with h₁
  set! t' := (ris (ω.eraseIdx j)).getD (j' - 1) 1 with h₂
  have h₃ : t' = (ris ω).getD j' 1 := by
    grind only [cs.getD_rightInvSeq, = eraseIdx_eq_take_drop_succ, = getElem?_eraseIdx,
      = drop_append, drop_of_length_le, drop_drop, = length_append, = length_take, = length_drop,
      = min_def]
  have h₄ : t * t' = 1 := by
    rw [h₁]; rw [h₃]; rw [dup]
    exact cs.getD_rightInvSeq_mul_self _ _
  have h₅ := calc
    π ω = π ω * t * t' := by rw [mul_assoc, h₄]; group
    _ = (π (ω.eraseIdx j)) * t' :=
        congrArg (· * t') (cs.wordProd_mul_getD_rightInvSeq _ _)
    _ = π ((ω.eraseIdx j).eraseIdx (j' - 1)) :=
        cs.wordProd_mul_getD_rightInvSeq _ _
  have h₆ := calc
    ω.length = ℓ (π ω) := rω.symm
    _ = ℓ (π ((ω.eraseIdx j).eraseIdx (j' - 1))) := congrArg cs.length h₅
    _ <= ((ω.eraseIdx j).eraseIdx (j' - 1)).length := cs.length_wordProd_le _
  grind

Depends on / 依赖: List.length, List.nodup_iff_getElem, Option.some_injective, _eq_getElem, _lt_length, _ne_getElem, eraseIdx, getD_eq_getElem, getElem, j_lt_j, length, nodup_iff_getElem, replace, rightInvSeq, some_injective
-/
theorem IsReduced.nodup_rightInvSeq {ω : List B} (rω : cs.IsReduced ω) : List.Nodup (ris ω) := by
  apply List.nodup_iff_getElem?_ne_getElem?.mpr
  intro j j' j_lt_j' j'_lt_length (dup : (rightInvSeq cs ω)[j]? = (rightInvSeq cs ω)[j']?)
  show False
  replace j'_lt_length : j' < List.length ω := by simpa using j'_lt_length
  rw [getElem?_eq_getElem (by simp; lia)]; rw [getElem?_eq_getElem (by simp; lia)] at dup
  apply Option.some_injective at dup
  rw [← getD_eq_getElem _ 1]; rw [← getD_eq_getElem _ 1] at dup
  set! t := (ris ω).getD j 1 with h₁
  set! t' := (ris (ω.eraseIdx j)).getD (j' - 1) 1 with h₂
  have h₃ : t' = (ris ω).getD j' 1 := by
    grind only [cs.getD_rightInvSeq, = eraseIdx_eq_take_drop_succ, = getElem?_eraseIdx,
      = drop_append, drop_of_length_le, drop_drop, = length_append, = length_take, = length_drop,
      = min_def]
  have h₄ : t * t' = 1 := by
    rw [h₁]; rw [h₃]; rw [dup]
    exact cs.getD_rightInvSeq_mul_self _ _
  have h₅ := calc
    π ω = π ω * t * t' := by rw [mul_assoc, h₄]; group
    _ = (π (ω.eraseIdx j)) * t' :=
        congrArg (· * t') (cs.wordProd_mul_getD_rightInvSeq _ _)
    _ = π ((ω.eraseIdx j).eraseIdx (j' - 1)) :=
        cs.wordProd_mul_getD_rightInvSeq _ _
  have h₆ := calc
    ω.length = ℓ (π ω) := rω.symm
    _ = ℓ (π ((ω.eraseIdx j).eraseIdx (j' - 1))) := congrArg cs.length h₅
    _ <= ((ω.eraseIdx j).eraseIdx (j' - 1)).length := cs.length_wordProd_le _
  grind

/--
theorem `IsReduced.nodup_leftInvSeq` / 定理 `IsReduced.nodup_leftInvSeq`

English:
theorem IsReduced.nodup_leftInvSeq
  given: {ω : List B} (rω : cs.IsReduced ω)
  statement: List.Nodup (lis ω)
  proof: by
  simp only [leftInvSeq_eq_reverse_rightInvSeq_reverse, nodup_reverse]
  apply nodup_rightInvSeq
  rwa [isReduced_reverse_iff]

中文:
定理 是既约.nodup_leftInvSeq
  条件: {ω : 列表 B} (rω : cs.是既约 ω)
  结论: 列表.Nodup (lis ω)
  证明: by
  simp only [leftInvSeq_eq_reverse_rightInvSeq_reverse, nodup_reverse]
  apply nodup_rightInvSeq
  rwa [isReduced_reverse_iff]

Depends on / 依赖: isReduced_reverse_iff, leftInvSeq_eq_reverse_rightInvSeq_reverse, nodup_reverse, nodup_rightInvSeq
-/
theorem IsReduced.nodup_leftInvSeq {ω : List B} (rω : cs.IsReduced ω) : List.Nodup (lis ω) := by
  simp only [leftInvSeq_eq_reverse_rightInvSeq_reverse, nodup_reverse]
  apply nodup_rightInvSeq
  rwa [isReduced_reverse_iff]

/--
lemma `getElem_succ_leftInvSeq_alternatingWord` / 引理 `getElem_succ_leftInvSeq_alternatingWord`

English:
lemma getElem_succ_leftInvSeq_alternatingWord
  proof: by
  rw [cs.getElem_leftInvSeq (alternatingWord i j (2 * p)) (k + 1) (by simp [h]),
    cs.getElem_leftInvSeq (alternatingWord j i (2 * p)) k (by simp; lia)]
  simp only [MulAut.conj, listTake_succ_alternatingWord i j p k h, cs.wordProd_cons, mul_assoc,
    mul_inv_rev, inv_simple, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.coe_mk, Equiv.coe_fn_mk,
    mul_right_inj, mul_left_inj]
  rw [getElem_alternatingWord_swapIndices i j (2 * p) k]
  lia

中文:
引理 getElem_succ_leftInvSeq_alternatingWord
  证明: by
  rw [cs.getElem_leftInvSeq (alternatingWord i j (2 * p)) (k + 1) (by simp [h]),
    cs.getElem_leftInvSeq (alternatingWord j i (2 * p)) k (by simp; lia)]
  simp only [MulAut.conj, listTake_succ_alternatingWord i j p k h, cs.wordProd_cons, mul_assoc,
    mul_inv_rev, inv_simple, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.coe_mk, Equiv.coe_fn_mk,
    mul_right_inj, mul_left_inj]
  rw [getElem_alternatingWord_swapIndices i j (2 * p) k]
  lia

Depends on / 依赖: Equiv.coe_fn_mk, MonoidHom, MonoidHom.coe_mk, MulAut, MulAut.conj, MulEquiv, MulEquiv.coe_mk, OneHom, OneHom.coe_mk, alternatingWord, coe_fn_mk, coe_mk, cs.getElem_leftInvSeq, cs.wordProd_cons, getElem_alternatingWord_swapIndices, getElem_leftInvSeq, inv_simple, listTake_succ_alternatingWord, mul_assoc, mul_inv_rev
-/
lemma getElem_succ_leftInvSeq_alternatingWord
    (i j : B) (p k : Nat) (h : k + 1 < 2 * p) :
    (lis (alternatingWord i j (2 * p)))[k + 1]'(by simpa using h) =
    MulAut.conj (s i) ((lis (alternatingWord j i (2 * p)))[k]'(by simp; lia)) := by
  rw [cs.getElem_leftInvSeq (alternatingWord i j (2 * p)) (k + 1) (by simp [h]),
    cs.getElem_leftInvSeq (alternatingWord j i (2 * p)) k (by simp; lia)]
  simp only [MulAut.conj, listTake_succ_alternatingWord i j p k h, cs.wordProd_cons, mul_assoc,
    mul_inv_rev, inv_simple, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.coe_mk, Equiv.coe_fn_mk,
    mul_right_inj, mul_left_inj]
  rw [getElem_alternatingWord_swapIndices i j (2 * p) k]
  lia

/--
theorem `getElem_leftInvSeq_alternatingWord` / 定理 `getElem_leftInvSeq_alternatingWord`

English:
theorem getElem_leftInvSeq_alternatingWord
  proof: by
  induction k generalizing i j with
  | zero =>
    simp only [CoxeterSystem.getElem_leftInvSeq cs (alternatingWord i j (2 * p)) 0 (by simp [h]),
      take_zero, wordProd_nil, one_mul, inv_one, mul_one, alternatingWord, concat_eq_append,
      nil_append, wordProd_singleton]
    simp only [getElem_alternatingWord i j (2 * p) 0 (by simp [h]), add_zero, even_two,
      Even.mul_right, ↓reduceIte]
  | succ k hk =>
    simp only [getElem_succ_leftInvSeq_alternatingWord cs i j p k h, hk _ _ (by lia),
      MulAut.conj_apply, inv_simple, alternatingWord_succ' j i, even_two, Even.mul_right,
      ↓reduceIte, wordProd_cons]
    rw [(by ring : 2 * (k + 1) = 2 * k + 1 + 1)]; rw [alternatingWord_succ j i]; rw [wordProd_concat]
    simp [mul_assoc]

中文:
定理 getElem_leftInvSeq_alternatingWord
  证明: by
  induction k generalizing i j with
  | zero =>
    simp only [CoxeterSystem.getElem_leftInvSeq cs (alternatingWord i j (2 * p)) 0 (by simp [h]),
      take_zero, wordProd_nil, one_mul, inv_one, mul_one, alternatingWord, concat_eq_append,
      nil_append, wordProd_singleton]
    simp only [getElem_alternatingWord i j (2 * p) 0 (by simp [h]), add_zero, even_two,
      Even.mul_right, ↓reduceIte]
  | succ k hk =>
    simp only [getElem_succ_leftInvSeq_alternatingWord cs i j p k h, hk _ _ (by lia),
      MulAut.conj_apply, inv_simple, alternatingWord_succ' j i, even_two, Even.mul_right,
      ↓reduceIte, wordProd_cons]
    rw [(by ring : 2 * (k + 1) = 2 * k + 1 + 1)]; rw [alternatingWord_succ j i]; rw [wordProd_concat]
    simp [mul_assoc]

Depends on / 依赖: CoxeterSystem, CoxeterSystem.getElem_leftInvSeq, Even.mul_right, MulAut, MulAut.conj_apply, add_zero, alternatingWord, concat_eq_append, conj_apply, even_two, generalizing, getElem_alternatingWord, getElem_leftInvSeq, getElem_succ_leftInvSeq_alternatingWord, inv_one, inv_simple, mul_one, mul_right, nil_append, one_mul
-/
theorem getElem_leftInvSeq_alternatingWord
    (i j : B) (p k : Nat) (h : k < 2 * p) :
    (lis (alternatingWord i j (2 * p)))[k]'(by simp; lia) =
    π alternatingWord j i (2 * k + 1) := by
  induction k generalizing i j with
  | zero =>
    simp only [CoxeterSystem.getElem_leftInvSeq cs (alternatingWord i j (2 * p)) 0 (by simp [h]),
      take_zero, wordProd_nil, one_mul, inv_one, mul_one, alternatingWord, concat_eq_append,
      nil_append, wordProd_singleton]
    simp only [getElem_alternatingWord i j (2 * p) 0 (by simp [h]), add_zero, even_two,
      Even.mul_right, ↓reduceIte]
  | succ k hk =>
    simp only [getElem_succ_leftInvSeq_alternatingWord cs i j p k h, hk _ _ (by lia),
      MulAut.conj_apply, inv_simple, alternatingWord_succ' j i, even_two, Even.mul_right,
      ↓reduceIte, wordProd_cons]
    rw [(by ring : 2 * (k + 1) = 2 * k + 1 + 1)]; rw [alternatingWord_succ j i]; rw [wordProd_concat]
    simp [mul_assoc]

end CoxeterSystem
