/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Data.ENat.Basic

/-!
# Trailing degree of univariate polynomials

## Main definitions

* `trailingDegree p`: the multiplicity of `X` in the polynomial `p`
* `natTrailingDegree`: a variant of `trailingDegree` that takes values in the natural numbers
* `trailingCoeff`: the coefficient at index `natTrailingDegree p`

Converts most results about `degree`, `natDegree` and `leadingCoeff` to results about the bottom
end of a polynomial
-/

@[expose] public section


noncomputable section

open Function Polynomial Finsupp Finset

open scoped Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b : R} {n m : Nat}

section Semiring

variable [Semiring R] {p q r : R[X]}

/--
Definition of `trailingDegree` / `trailingDegree` 的定义

English:
definition trailingDegree
  signature: (p : R[X])
  body: p.support.min

中文:
定义 trailingDegree
  签名: (p : R[X])
  定义体: p.support.min

Depends on / 依赖: p.support.min, support
-/
def trailingDegree (p : R[X]) : Nat∞ :=
  p.support.min

/--
theorem `trailingDegree_lt_wf` / 定理 `trailingDegree_lt_wf`

English:
theorem trailingDegree_lt_wf
  statement: WellFounded fun p q : R[X] => trailingDegree p < trailingDegree q
  proof: InvImage.wf trailingDegree wellFounded_lt

中文:
定理 trailingDegree_lt_wf
  结论: 良基 fun p q : R[X] => trailingDegree p < trailingDegree q
  证明: InvImage.wf trailingDegree wellFounded_lt

Depends on / 依赖: InvImage, InvImage.wf, trailingDegree, wellFounded_lt
-/
theorem trailingDegree_lt_wf : WellFounded fun p q : R[X] => trailingDegree p < trailingDegree q :=
  InvImage.wf trailingDegree wellFounded_lt

/--
Definition of `natTrailingDegree` / `natTrailingDegree` 的定义

English:
definition natTrailingDegree
  signature: (p : R[X])
  body: ENat.toNat (trailingDegree p)

中文:
定义 natTrailingDegree
  签名: (p : R[X])
  定义体: ENat.toNat (trailingDegree p)

Depends on / 依赖: ENat.toNat, trailingDegree
-/
def natTrailingDegree (p : R[X]) : Nat :=
  ENat.toNat (trailingDegree p)

/--
Definition of `trailingCoeff` / `trailingCoeff` 的定义

English:
definition trailingCoeff
  signature: (p : R[X])
  body: coeff p (natTrailingDegree p)

中文:
定义 trailingCoeff
  签名: (p : R[X])
  定义体: coeff p (natTrailingDegree p)

Depends on / 依赖: natTrailingDegree
-/
def trailingCoeff (p : R[X]) : R :=
  coeff p (natTrailingDegree p)

/--
Definition of `TrailingMonic` / `TrailingMonic` 的定义

English:
definition TrailingMonic
  signature: (p : R[X])
  body: trailingCoeff p = (1 : R)

中文:
定义 TrailingMonic
  签名: (p : R[X])
  定义体: trailingCoeff p = (1 : R)

Depends on / 依赖: trailingCoeff
-/
def TrailingMonic (p : R[X]) :=
  trailingCoeff p = (1 : R)

/--
theorem `TrailingMonic.def` / 定理 `TrailingMonic.def`

English:
theorem TrailingMonic.def
  statement: TrailingMonic p ↔ trailingCoeff p = 1
  proof: Iff.rfl

中文:
定理 TrailingMonic.def
  结论: TrailingMonic p ↔ trailingCoeff p = 1
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem TrailingMonic.def : TrailingMonic p ↔ trailingCoeff p = 1 :=
  Iff.rfl

/--
Instance `TrailingMonic.decidable` / 实例 `TrailingMonic.decidable`

English:
instance TrailingMonic.decidable
  signature: [DecidableEq R]
  body: inferInstanceAs Decidable (trailingCoeff p = (1 : R))

@[simp]

中文:
实例 TrailingMonic.decidable
  签名: [DecidableEq R]
  定义体: inferInstanceAs Decidable (trailingCoeff p = (1 : R))

@[simp]

Depends on / 依赖: Decidable, trailingCoeff
-/
instance TrailingMonic.decidable [DecidableEq R] : Decidable (TrailingMonic p) :=
inferInstanceAs Decidable (trailingCoeff p = (1 : R))

@[simp]
/--
theorem `TrailingMonic.trailingCoeff` / 定理 `TrailingMonic.trailingCoeff`

English:
theorem TrailingMonic.trailingCoeff
  given: {p : R[X]} (hp : p.TrailingMonic)
  statement: trailingCoeff p = 1
  proof: hp

@[simp]

中文:
定理 TrailingMonic.trailingCoeff
  条件: {p : R[X]} (hp : p.TrailingMonic)
  结论: trailingCoeff p = 1
  证明: hp

@[simp]
-/
theorem TrailingMonic.trailingCoeff {p : R[X]} (hp : p.TrailingMonic) : trailingCoeff p = 1 :=
  hp

@[simp]
/--
theorem `trailingDegree_zero` / 定理 `trailingDegree_zero`

English:
theorem trailingDegree_zero
  statement: trailingDegree (0 : R[X]) = ⊤
  proof: rfl

@[simp]

中文:
定理 trailingDegree_zero
  结论: trailingDegree (0 : R[X]) = ⊤
  证明: rfl

@[simp]
-/
theorem trailingDegree_zero : trailingDegree (0 : R[X]) = ⊤ :=
  rfl

@[simp]
/--
theorem `trailingCoeff_zero` / 定理 `trailingCoeff_zero`

English:
theorem trailingCoeff_zero
  statement: trailingCoeff (0 : R[X]) = 0
  proof: rfl

@[simp]

中文:
定理 trailingCoeff_zero
  结论: trailingCoeff (0 : R[X]) = 0
  证明: rfl

@[simp]
-/
theorem trailingCoeff_zero : trailingCoeff (0 : R[X]) = 0 :=
  rfl

@[simp]
/--
theorem `natTrailingDegree_zero` / 定理 `natTrailingDegree_zero`

English:
theorem natTrailingDegree_zero
  statement: natTrailingDegree (0 : R[X]) = 0
  proof: rfl

@[simp]

中文:
定理 natTrailingDegree_zero
  结论: natTrailingDegree (0 : R[X]) = 0
  证明: rfl

@[simp]
-/
theorem natTrailingDegree_zero : natTrailingDegree (0 : R[X]) = 0 :=
  rfl

@[simp]
/--
theorem `trailingDegree_eq_top` / 定理 `trailingDegree_eq_top`

English:
theorem trailingDegree_eq_top
  statement: trailingDegree p = ⊤ ↔ p = 0
  proof: ⟨fun h => support_eq_empty.1 (Finset.min_eq_top.1 h), fun h => by simp [h]⟩

中文:
定理 trailingDegree_eq_top
  结论: trailingDegree p = ⊤ ↔ p = 0
  证明: ⟨fun h => support_eq_empty.1 (Finset.min_eq_top.1 h), fun h => by simp [h]⟩

Depends on / 依赖: Finset, Finset.min_eq_top, min_eq_top, support_eq_empty
-/
theorem trailingDegree_eq_top : trailingDegree p = ⊤ ↔ p = 0 :=
  ⟨fun h => support_eq_empty.1 (Finset.min_eq_top.1 h), fun h => by simp [h]⟩

/--
theorem `trailingDegree_eq_natTrailingDegree` / 定理 `trailingDegree_eq_natTrailingDegree`

English:
theorem trailingDegree_eq_natTrailingDegree
  given: (hp : p != 0)
  proof: .symm ENat.natCast_toNat mt trailingDegree_eq_top.1 hp

中文:
定理 trailingDegree_eq_natTrailingDegree
  条件: (hp : p != 0)
  证明: .symm ENat.natCast_toNat mt trailingDegree_eq_top.1 hp

Depends on / 依赖: ENat.natCast_toNat, natCast_toNat, trailingDegree_eq_top
-/
theorem trailingDegree_eq_natTrailingDegree (hp : p != 0) :
    trailingDegree p = (natTrailingDegree p : Nat∞) :=
.symm ENat.natCast_toNat mt trailingDegree_eq_top.1 hp

/--
theorem `trailingDegree_eq_iff_natTrailingDegree_eq` / 定理 `trailingDegree_eq_iff_natTrailingDegree_eq`

English:
theorem trailingDegree_eq_iff_natTrailingDegree_eq
  given: {p : R[X]} {n : Nat} (hp : p != 0)
  proof: by
  rw [trailingDegree_eq_natTrailingDegree hp]; rw [Nat.cast_inj]

中文:
定理 trailingDegree_eq_iff_natTrailingDegree_eq
  条件: {p : R[X]} {n : 自然数} (hp : p != 0)
  证明: by
  rw [trailingDegree_eq_natTrailingDegree hp]; rw [Nat.cast_inj]

Depends on / 依赖: Nat.cast_inj, cast_inj, trailingDegree_eq_natTrailingDegree
-/
theorem trailingDegree_eq_iff_natTrailingDegree_eq {p : R[X]} {n : Nat} (hp : p != 0) :
    p.trailingDegree = n ↔ p.natTrailingDegree = n := by
  rw [trailingDegree_eq_natTrailingDegree hp]; rw [Nat.cast_inj]

/--
theorem `trailingDegree_eq_iff_natTrailingDegree_eq_of_pos` / 定理 `trailingDegree_eq_iff_natTrailingDegree_eq_of_pos`

English:
theorem trailingDegree_eq_iff_natTrailingDegree_eq_of_pos
  given: {p : R[X]} {n : Nat} (hn : n != 0)
  proof: by
  rw [natTrailingDegree]; rw [ENat.toNat_eq_iff hn]

中文:
定理 trailingDegree_eq_iff_natTrailingDegree_eq_of_pos
  条件: {p : R[X]} {n : 自然数} (hn : n != 0)
  证明: by
  rw [natTrailingDegree]; rw [ENat.toNat_eq_iff hn]

Depends on / 依赖: ENat.toNat_eq_iff, natTrailingDegree, toNat_eq_iff
-/
theorem trailingDegree_eq_iff_natTrailingDegree_eq_of_pos {p : R[X]} {n : Nat} (hn : n != 0) :
    p.trailingDegree = n ↔ p.natTrailingDegree = n := by
  rw [natTrailingDegree]; rw [ENat.toNat_eq_iff hn]

/--
theorem `natTrailingDegree_eq_of_trailingDegree_eq_some` / 定理 `natTrailingDegree_eq_of_trailingDegree_eq_some`

English:
theorem natTrailingDegree_eq_of_trailingDegree_eq_some
  statement: {p : R[X]} {n : Nat}
  proof: by
  simp [natTrailingDegree, h]

@[simp]

中文:
定理 natTrailingDegree_eq_of_trailingDegree_eq_some
  结论: {p : R[X]} {n : 自然数}
  证明: by
  simp [natTrailingDegree, h]

@[simp]

Depends on / 依赖: natTrailingDegree
-/
theorem natTrailingDegree_eq_of_trailingDegree_eq_some {p : R[X]} {n : Nat}
    (h : trailingDegree p = n) : natTrailingDegree p = n := by
  simp [natTrailingDegree, h]

@[simp]
/--
theorem `natTrailingDegree_le_trailingDegree` / 定理 `natTrailingDegree_le_trailingDegree`

English:
theorem natTrailingDegree_le_trailingDegree
  statement: ↑(natTrailingDegree p) <= trailingDegree p
  proof: ENat.natCast_toNat_le_self _

中文:
定理 natTrailingDegree_le_trailingDegree
  结论: ↑(natTrailingDegree p) <= trailingDegree p
  证明: ENat.natCast_toNat_le_self _

Depends on / 依赖: ENat.natCast_toNat_le_self, natCast_toNat_le_self
-/
theorem natTrailingDegree_le_trailingDegree : ↑(natTrailingDegree p) <= trailingDegree p :=
  ENat.natCast_toNat_le_self _

/--
theorem `natTrailingDegree_eq_of_trailingDegree_eq` / 定理 `natTrailingDegree_eq_of_trailingDegree_eq`

English:
theorem natTrailingDegree_eq_of_trailingDegree_eq
  statement: [Semiring S] {q : S[X]}
  proof: by
  unfold natTrailingDegree
  rw [h]

中文:
定理 natTrailingDegree_eq_of_trailingDegree_eq
  结论: [半环 S] {q : S[X]}
  证明: by
  unfold natTrailingDegree
  rw [h]

Depends on / 依赖: natTrailingDegree
-/
theorem natTrailingDegree_eq_of_trailingDegree_eq [Semiring S] {q : S[X]}
    (h : trailingDegree p = trailingDegree q) : natTrailingDegree p = natTrailingDegree q := by
  unfold natTrailingDegree
  rw [h]

/--
theorem `trailingDegree_le_of_ne_zero` / 定理 `trailingDegree_le_of_ne_zero`

English:
theorem trailingDegree_le_of_ne_zero
  given: (h : coeff p n != 0)
  statement: trailingDegree p <= n
  proof: min_le (mem_support_iff.2 h)

中文:
定理 trailingDegree_le_of_ne_zero
  条件: (h : coeff p n != 0)
  结论: trailingDegree p <= n
  证明: min_le (mem_support_iff.2 h)

Depends on / 依赖: mem_support_iff, min_le
-/
theorem trailingDegree_le_of_ne_zero (h : coeff p n != 0) : trailingDegree p <= n :=
  min_le (mem_support_iff.2 h)

/--
theorem `natTrailingDegree_le_of_ne_zero` / 定理 `natTrailingDegree_le_of_ne_zero`

English:
theorem natTrailingDegree_le_of_ne_zero
  given: (h : coeff p n != 0)
  statement: natTrailingDegree p <= n
  proof: ENat.toNat_le_of_le_natCast trailingDegree_le_of_ne_zero h

中文:
定理 natTrailingDegree_le_of_ne_zero
  条件: (h : coeff p n != 0)
  结论: natTrailingDegree p <= n
  证明: ENat.toNat_le_of_le_natCast trailingDegree_le_of_ne_zero h

Depends on / 依赖: ENat.toNat_le_of_le_natCast, toNat_le_of_le_natCast, trailingDegree_le_of_ne_zero
-/
theorem natTrailingDegree_le_of_ne_zero (h : coeff p n != 0) : natTrailingDegree p <= n :=
ENat.toNat_le_of_le_natCast trailingDegree_le_of_ne_zero h

/--
lemma `coeff_natTrailingDegree_eq_zero` / 引理 `coeff_natTrailingDegree_eq_zero`

English:
lemma coeff_natTrailingDegree_eq_zero
  statement: coeff p p.natTrailingDegree = 0 ↔ p = 0
  proof: by
  constructor
  · rintro h
    by_contra hp
obtain ⟨n, hpn, hn⟩ := by simpa using min_mem_image_coe support_nonempty.2 hp
    obtain rfl := (trailingDegree_eq_iff_natTrailingDegree_eq hp).1 hn.symm
    exact hpn h
  · rintro rfl
    simp

中文:
引理 coeff_natTrailingDegree_eq_zero
  结论: coeff p p.natTrailingDegree = 0 ↔ p = 0
  证明: by
  constructor
  · rintro h
    by_contra hp
obtain ⟨n, hpn, hn⟩ := by simpa using min_mem_image_coe support_nonempty.2 hp
    obtain rfl := (trailingDegree_eq_iff_natTrailingDegree_eq hp).1 hn.symm
    exact hpn h
  · rintro rfl
    simp
-/
@[simp] lemma coeff_natTrailingDegree_eq_zero : coeff p p.natTrailingDegree = 0 ↔ p = 0 := by
  constructor
  · rintro h
    by_contra hp
obtain ⟨n, hpn, hn⟩ := by simpa using min_mem_image_coe support_nonempty.2 hp
    obtain rfl := (trailingDegree_eq_iff_natTrailingDegree_eq hp).1 hn.symm
    exact hpn h
  · rintro rfl
    simp

/--
lemma `coeff_natTrailingDegree_ne_zero` / 引理 `coeff_natTrailingDegree_ne_zero`

English:
lemma coeff_natTrailingDegree_ne_zero
  statement: coeff p p.natTrailingDegree != 0 ↔ p != 0
  proof: coeff_natTrailingDegree_eq_zero.not

@[simp]

中文:
引理 coeff_natTrailingDegree_ne_zero
  结论: coeff p p.natTrailingDegree != 0 ↔ p != 0
  证明: coeff_natTrailingDegree_eq_zero.not

@[simp]

Depends on / 依赖: coeff_natTrailingDegree_eq_zero, coeff_natTrailingDegree_eq_zero.not
-/
lemma coeff_natTrailingDegree_ne_zero : coeff p p.natTrailingDegree != 0 ↔ p != 0 :=
  coeff_natTrailingDegree_eq_zero.not

@[simp]
/--
lemma `trailingDegree_eq_zero` / 引理 `trailingDegree_eq_zero`

English:
lemma trailingDegree_eq_zero
  statement: trailingDegree p = 0 ↔ coeff p 0 != 0
  proof: Finset.min_eq_bot.trans mem_support_iff

中文:
引理 trailingDegree_eq_zero
  结论: trailingDegree p = 0 ↔ coeff p 0 != 0
  证明: Finset.min_eq_bot.trans mem_support_iff

Depends on / 依赖: Finset, Finset.min_eq_bot.trans, mem_support_iff, min_eq_bot
-/
lemma trailingDegree_eq_zero : trailingDegree p = 0 ↔ coeff p 0 != 0 :=
  Finset.min_eq_bot.trans mem_support_iff

/--
lemma `natTrailingDegree_eq_zero` / 引理 `natTrailingDegree_eq_zero`

English:
lemma natTrailingDegree_eq_zero
  statement: natTrailingDegree p = 0 ↔ p = 0 ∨ coeff p 0 != 0
  proof: by
  simp [natTrailingDegree, or_comm]

中文:
引理 natTrailingDegree_eq_zero
  结论: natTrailingDegree p = 0 ↔ p = 0 ∨ coeff p 0 != 0
  证明: by
  simp [natTrailingDegree, or_comm]
-/
@[simp] lemma natTrailingDegree_eq_zero : natTrailingDegree p = 0 ↔ p = 0 ∨ coeff p 0 != 0 := by
  simp [natTrailingDegree, or_comm]

/--
lemma `natTrailingDegree_ne_zero` / 引理 `natTrailingDegree_ne_zero`

English:
lemma natTrailingDegree_ne_zero
  statement: natTrailingDegree p != 0 ↔ p != 0 ∧ coeff p 0 = 0
  proof: natTrailingDegree_eq_zero.not.trans by rw [not_or, not_ne_iff]

中文:
引理 natTrailingDegree_ne_zero
  结论: natTrailingDegree p != 0 ↔ p != 0 ∧ coeff p 0 = 0
  证明: natTrailingDegree_eq_zero.not.trans by rw [not_or, not_ne_iff]

Depends on / 依赖: natTrailingDegree_eq_zero, natTrailingDegree_eq_zero.not.trans, not_ne_iff, not_or
-/
lemma natTrailingDegree_ne_zero : natTrailingDegree p != 0 ↔ p != 0 ∧ coeff p 0 = 0 :=
natTrailingDegree_eq_zero.not.trans by rw [not_or, not_ne_iff]

/--
lemma `trailingDegree_ne_zero` / 引理 `trailingDegree_ne_zero`

English:
lemma trailingDegree_ne_zero
  statement: trailingDegree p != 0 ↔ coeff p 0 = 0
  proof: trailingDegree_eq_zero.not_left

中文:
引理 trailingDegree_ne_zero
  结论: trailingDegree p != 0 ↔ coeff p 0 = 0
  证明: trailingDegree_eq_zero.not_left

Depends on / 依赖: not_left, trailingDegree_eq_zero, trailingDegree_eq_zero.not_left
-/
lemma trailingDegree_ne_zero : trailingDegree p != 0 ↔ coeff p 0 = 0 :=
  trailingDegree_eq_zero.not_left

/--
theorem `trailingDegree_le_trailingDegree` / 定理 `trailingDegree_le_trailingDegree`

English:
theorem trailingDegree_le_trailingDegree
  given: (h : coeff q (natTrailingDegree p) != 0)
  proof: (trailingDegree_le_of_ne_zero h).trans natTrailingDegree_le_trailingDegree

中文:
定理 trailingDegree_le_trailingDegree
  条件: (h : coeff q (natTrailingDegree p) != 0)
  证明: (trailingDegree_le_of_ne_zero h).trans natTrailingDegree_le_trailingDegree
-/
@[simp] theorem trailingDegree_le_trailingDegree (h : coeff q (natTrailingDegree p) != 0) :
    trailingDegree q <= trailingDegree p :=
  (trailingDegree_le_of_ne_zero h).trans natTrailingDegree_le_trailingDegree

/--
theorem `trailingCoeff_eq_coeff_zero` / 定理 `trailingCoeff_eq_coeff_zero`

English:
theorem trailingCoeff_eq_coeff_zero
  given: (h : coeff p 0 != 0)
  statement: trailingCoeff p = coeff p 0
  proof: by
  rw [trailingCoeff]; rw [(natTrailingDegree_eq_zero.mpr <| .inr h)]

中文:
定理 trailingCoeff_eq_coeff_zero
  条件: (h : coeff p 0 != 0)
  结论: trailingCoeff p = coeff p 0
  证明: by
  rw [trailingCoeff]; rw [(natTrailingDegree_eq_zero.mpr <| .inr h)]

Depends on / 依赖: natTrailingDegree_eq_zero, natTrailingDegree_eq_zero.mpr, trailingCoeff
-/
theorem trailingCoeff_eq_coeff_zero (h : coeff p 0 != 0) : trailingCoeff p = coeff p 0 := by
  rw [trailingCoeff]; rw [(natTrailingDegree_eq_zero.mpr <| .inr h)]

/--
theorem `trailingDegree_ne_of_natTrailingDegree_ne` / 定理 `trailingDegree_ne_of_natTrailingDegree_ne`

English:
theorem trailingDegree_ne_of_natTrailingDegree_ne
  given: {n : Nat}
  proof: mt fun h => by rw [natTrailingDegree, h, ENat.toNat_natCast]

中文:
定理 trailingDegree_ne_of_natTrailingDegree_ne
  条件: {n : 自然数}
  证明: mt fun h => by rw [natTrailingDegree, h, ENat.toNat_natCast]

Depends on / 依赖: ENat.toNat_natCast, natTrailingDegree, toNat_natCast
-/
theorem trailingDegree_ne_of_natTrailingDegree_ne {n : Nat} :
    p.natTrailingDegree != n -> trailingDegree p != n :=
  mt fun h => by rw [natTrailingDegree, h, ENat.toNat_natCast]

/--
theorem `natTrailingDegree_le_of_trailingDegree_le` / 定理 `natTrailingDegree_le_of_trailingDegree_le`

English:
theorem natTrailingDegree_le_of_trailingDegree_le
  statement: {n : Nat} {hp : p != 0}
  proof: by
  rwa [trailingDegree_eq_natTrailingDegree hp, Nat.cast_le] at H

中文:
定理 natTrailingDegree_le_of_trailingDegree_le
  结论: {n : 自然数} {hp : p != 0}
  证明: by
  rwa [trailingDegree_eq_natTrailingDegree hp, Nat.cast_le] at H

Depends on / 依赖: Nat.cast_le, cast_le, trailingDegree_eq_natTrailingDegree
-/
theorem natTrailingDegree_le_of_trailingDegree_le {n : Nat} {hp : p != 0}
    (H : (n : Nat∞) <= trailingDegree p) : n <= natTrailingDegree p := by
  rwa [trailingDegree_eq_natTrailingDegree hp, Nat.cast_le] at H

/--
theorem `natTrailingDegree_le_natTrailingDegree` / 定理 `natTrailingDegree_le_natTrailingDegree`

English:
theorem natTrailingDegree_le_natTrailingDegree
  statement: (hq : q != 0)
  proof: ENat.toNat_le_toNat hpq by simpa

@[simp]

中文:
定理 natTrailingDegree_le_natTrailingDegree
  结论: (hq : q != 0)
  证明: ENat.toNat_le_toNat hpq by simpa

@[simp]

Depends on / 依赖: ENat.toNat_le_toNat, toNat_le_toNat
-/
theorem natTrailingDegree_le_natTrailingDegree (hq : q != 0)
    (hpq : p.trailingDegree <= q.trailingDegree) : p.natTrailingDegree <= q.natTrailingDegree :=
ENat.toNat_le_toNat hpq by simpa

@[simp]
/--
theorem `trailingDegree_monomial` / 定理 `trailingDegree_monomial`

English:
theorem trailingDegree_monomial
  given: (ha : a != 0)
  statement: trailingDegree (monomial n a) = n
  proof: by
  rw [trailingDegree]; rw [support_monomial n ha]; rw [min_singleton]
  rfl

中文:
定理 trailingDegree_monomial
  条件: (ha : a != 0)
  结论: trailingDegree (monomial n a) = n
  证明: by
  rw [trailingDegree]; rw [support_monomial n ha]; rw [min_singleton]
  rfl

Depends on / 依赖: min_singleton, support_monomial, trailingDegree
-/
theorem trailingDegree_monomial (ha : a != 0) : trailingDegree (monomial n a) = n := by
  rw [trailingDegree]; rw [support_monomial n ha]; rw [min_singleton]
  rfl

/--
theorem `natTrailingDegree_monomial` / 定理 `natTrailingDegree_monomial`

English:
theorem natTrailingDegree_monomial
  given: (ha : a != 0)
  statement: natTrailingDegree (monomial n a) = n
  proof: by
  rw [natTrailingDegree]; rw [trailingDegree_monomial ha]
  rfl

中文:
定理 natTrailingDegree_monomial
  条件: (ha : a != 0)
  结论: natTrailingDegree (monomial n a) = n
  证明: by
  rw [natTrailingDegree]; rw [trailingDegree_monomial ha]
  rfl

Depends on / 依赖: natTrailingDegree, trailingDegree_monomial
-/
theorem natTrailingDegree_monomial (ha : a != 0) : natTrailingDegree (monomial n a) = n := by
  rw [natTrailingDegree]; rw [trailingDegree_monomial ha]
  rfl

/--
theorem `natTrailingDegree_monomial_le` / 定理 `natTrailingDegree_monomial_le`

English:
theorem natTrailingDegree_monomial_le
  statement: natTrailingDegree (monomial n a) <= n
  proof: letI := Classical.decEq R
  if ha : a = 0 then by simp [ha] else (natTrailingDegree_monomial ha).le

中文:
定理 natTrailingDegree_monomial_le
  结论: natTrailingDegree (monomial n a) <= n
  证明: letI := Classical.decEq R
  if ha : a = 0 then by simp [ha] else (natTrailingDegree_monomial ha).le

Depends on / 依赖: Classical, Classical.decEq, natTrailingDegree_monomial
-/
theorem natTrailingDegree_monomial_le : natTrailingDegree (monomial n a) <= n :=
  letI := Classical.decEq R
  if ha : a = 0 then by simp [ha] else (natTrailingDegree_monomial ha).le

/--
theorem `le_trailingDegree_monomial` / 定理 `le_trailingDegree_monomial`

English:
theorem le_trailingDegree_monomial
  statement: ↑n <= trailingDegree (monomial n a)
  proof: letI := Classical.decEq R
  if ha : a = 0 then by simp [ha] else (trailingDegree_monomial ha).ge

@[simp]

中文:
定理 le_trailingDegree_monomial
  结论: ↑n <= trailingDegree (monomial n a)
  证明: letI := Classical.decEq R
  if ha : a = 0 then by simp [ha] else (trailingDegree_monomial ha).ge

@[simp]

Depends on / 依赖: Classical, Classical.decEq, trailingDegree_monomial
-/
theorem le_trailingDegree_monomial : ↑n <= trailingDegree (monomial n a) :=
  letI := Classical.decEq R
  if ha : a = 0 then by simp [ha] else (trailingDegree_monomial ha).ge

@[simp]
/--
theorem `trailingDegree_C` / 定理 `trailingDegree_C`

English:
theorem trailingDegree_C
  given: (ha : a != 0)
  statement: trailingDegree (C a) = (0 : Nat∞)
  proof: trailingDegree_monomial ha

中文:
定理 trailingDegree_C
  条件: (ha : a != 0)
  结论: trailingDegree (C a) = (0 : 自然数∞)
  证明: trailingDegree_monomial ha

Depends on / 依赖: trailingDegree_monomial
-/
theorem trailingDegree_C (ha : a != 0) : trailingDegree (C a) = (0 : Nat∞) :=
  trailingDegree_monomial ha

/--
theorem `le_trailingDegree_C` / 定理 `le_trailingDegree_C`

English:
theorem le_trailingDegree_C
  statement: (0 : Nat∞) <= trailingDegree (C a)
  proof: le_trailingDegree_monomial

中文:
定理 le_trailingDegree_C
  结论: (0 : 自然数∞) <= trailingDegree (C a)
  证明: le_trailingDegree_monomial

Depends on / 依赖: le_trailingDegree_monomial
-/
theorem le_trailingDegree_C : (0 : Nat∞) <= trailingDegree (C a) :=
  le_trailingDegree_monomial

/--
theorem `trailingDegree_one_le` / 定理 `trailingDegree_one_le`

English:
theorem trailingDegree_one_le
  statement: (0 : Nat∞) <= trailingDegree (1 : R[X])
  proof: by
  rw [← C_1]
  exact le_trailingDegree_C

@[simp]

中文:
定理 trailingDegree_one_le
  结论: (0 : 自然数∞) <= trailingDegree (1 : R[X])
  证明: by
  rw [← C_1]
  exact le_trailingDegree_C

@[simp]

Depends on / 依赖: le_trailingDegree_C
-/
theorem trailingDegree_one_le : (0 : Nat∞) <= trailingDegree (1 : R[X]) := by
  rw [← C_1]
  exact le_trailingDegree_C

@[simp]
/--
theorem `natTrailingDegree_C` / 定理 `natTrailingDegree_C`

English:
theorem natTrailingDegree_C
  given: (a : R)
  statement: natTrailingDegree (C a) = 0
  proof: nonpos_iff_eq_zero.1 natTrailingDegree_monomial_le

@[simp]

中文:
定理 natTrailingDegree_C
  条件: (a : R)
  结论: natTrailingDegree (C a) = 0
  证明: nonpos_iff_eq_zero.1 natTrailingDegree_monomial_le

@[simp]

Depends on / 依赖: natTrailingDegree_monomial_le, nonpos_iff_eq_zero
-/
theorem natTrailingDegree_C (a : R) : natTrailingDegree (C a) = 0 :=
  nonpos_iff_eq_zero.1 natTrailingDegree_monomial_le

@[simp]
/--
theorem `natTrailingDegree_one` / 定理 `natTrailingDegree_one`

English:
theorem natTrailingDegree_one
  statement: natTrailingDegree (1 : R[X]) = 0
  proof: natTrailingDegree_C 1

@[simp]

中文:
定理 natTrailingDegree_one
  结论: natTrailingDegree (1 : R[X]) = 0
  证明: natTrailingDegree_C 1

@[simp]

Depends on / 依赖: natTrailingDegree_C
-/
theorem natTrailingDegree_one : natTrailingDegree (1 : R[X]) = 0 :=
  natTrailingDegree_C 1

@[simp]
/--
theorem `natTrailingDegree_natCast` / 定理 `natTrailingDegree_natCast`

English:
theorem natTrailingDegree_natCast
  given: (n : Nat)
  statement: natTrailingDegree (n : R[X]) = 0
  proof: by
  simp only [← C_eq_natCast, natTrailingDegree_C]

@[simp]

中文:
定理 natTrailingDegree_natCast
  条件: (n : 自然数)
  结论: natTrailingDegree (n : R[X]) = 0
  证明: by
  simp only [← C_eq_natCast, natTrailingDegree_C]

@[simp]

Depends on / 依赖: C_eq_natCast, natTrailingDegree_C
-/
theorem natTrailingDegree_natCast (n : Nat) : natTrailingDegree (n : R[X]) = 0 := by
  simp only [← C_eq_natCast, natTrailingDegree_C]

@[simp]
/--
theorem `trailingDegree_C_mul_X_pow` / 定理 `trailingDegree_C_mul_X_pow`

English:
theorem trailingDegree_C_mul_X_pow
  given: (n : Nat) (ha : a != 0)
  statement: trailingDegree (C a * X ^ n) = n
  proof: by
  rw [C_mul_X_pow_eq_monomial]; rw [trailingDegree_monomial ha]

中文:
定理 trailingDegree_C_mul_X_pow
  条件: (n : 自然数) (ha : a != 0)
  结论: trailingDegree (C a * X ^ n) = n
  证明: by
  rw [C_mul_X_pow_eq_monomial]; rw [trailingDegree_monomial ha]

Depends on / 依赖: C_mul_X_pow_eq_monomial, trailingDegree_monomial
-/
theorem trailingDegree_C_mul_X_pow (n : Nat) (ha : a != 0) : trailingDegree (C a * X ^ n) = n := by
  rw [C_mul_X_pow_eq_monomial]; rw [trailingDegree_monomial ha]

/--
theorem `le_trailingDegree_C_mul_X_pow` / 定理 `le_trailingDegree_C_mul_X_pow`

English:
theorem le_trailingDegree_C_mul_X_pow
  given: (n : Nat) (a : R)
  proof: by
  rw [C_mul_X_pow_eq_monomial]
  exact le_trailingDegree_monomial

中文:
定理 le_trailingDegree_C_mul_X_pow
  条件: (n : 自然数) (a : R)
  证明: by
  rw [C_mul_X_pow_eq_monomial]
  exact le_trailingDegree_monomial

Depends on / 依赖: C_mul_X_pow_eq_monomial, le_trailingDegree_monomial
-/
theorem le_trailingDegree_C_mul_X_pow (n : Nat) (a : R) :
    (n : Nat∞) <= trailingDegree (C a * X ^ n) := by
  rw [C_mul_X_pow_eq_monomial]
  exact le_trailingDegree_monomial

/--
theorem `coeff_eq_zero_of_lt_trailingDegree` / 定理 `coeff_eq_zero_of_lt_trailingDegree`

English:
theorem coeff_eq_zero_of_lt_trailingDegree
  given: (h : (n : Nat∞) < trailingDegree p)
  statement: coeff p n = 0
  proof: Classical.not_not.1 (mt trailingDegree_le_of_ne_zero (not_le_of_gt h))

中文:
定理 coeff_eq_zero_of_lt_trailingDegree
  条件: (h : (n : 自然数∞) < trailingDegree p)
  结论: coeff p n = 0
  证明: Classical.not_not.1 (mt trailingDegree_le_of_ne_zero (not_le_of_gt h))

Depends on / 依赖: Classical, Classical.not_not, not_le_of_gt, not_not, trailingDegree_le_of_ne_zero
-/
theorem coeff_eq_zero_of_lt_trailingDegree (h : (n : Nat∞) < trailingDegree p) : coeff p n = 0 :=
  Classical.not_not.1 (mt trailingDegree_le_of_ne_zero (not_le_of_gt h))

/--
theorem `coeff_eq_zero_of_lt_natTrailingDegree` / 定理 `coeff_eq_zero_of_lt_natTrailingDegree`

English:
theorem coeff_eq_zero_of_lt_natTrailingDegree
  given: {p : R[X]} {n : Nat} (h : n < p.natTrailingDegree)
  proof: by
  apply coeff_eq_zero_of_lt_trailingDegree
  by_cases hp : p = 0
  · rw [hp, trailingDegree_zero]
    exact WithTop.coe_lt_top n
  · rw [trailingDegree_eq_natTrailingDegree hp]
    exact WithTop.coe_lt_coe.2 h

@[simp]

中文:
定理 coeff_eq_zero_of_lt_natTrailingDegree
  条件: {p : R[X]} {n : 自然数} (h : n < p.natTrailingDegree)
  证明: by
  apply coeff_eq_zero_of_lt_trailingDegree
  by_cases hp : p = 0
  · rw [hp, trailingDegree_zero]
    exact WithTop.coe_lt_top n
  · rw [trailingDegree_eq_natTrailingDegree hp]
    exact WithTop.coe_lt_coe.2 h

@[simp]

Depends on / 依赖: WithTop, WithTop.coe_lt_coe, WithTop.coe_lt_top, coe_lt_coe, coe_lt_top, coeff_eq_zero_of_lt_trailingDegree, trailingDegree_eq_natTrailingDegree, trailingDegree_zero
-/
theorem coeff_eq_zero_of_lt_natTrailingDegree {p : R[X]} {n : Nat} (h : n < p.natTrailingDegree) :
    p.coeff n = 0 := by
  apply coeff_eq_zero_of_lt_trailingDegree
  by_cases hp : p = 0
  · rw [hp, trailingDegree_zero]
    exact WithTop.coe_lt_top n
  · rw [trailingDegree_eq_natTrailingDegree hp]
    exact WithTop.coe_lt_coe.2 h

@[simp]
/--
theorem `coeff_natTrailingDegree_pred_eq_zero` / 定理 `coeff_natTrailingDegree_pred_eq_zero`

English:
theorem coeff_natTrailingDegree_pred_eq_zero
  given: {p : R[X]} {hp : (0 : Nat∞) < natTrailingDegree p}
  proof: coeff_eq_zero_of_lt_natTrailingDegree
    Nat.sub_lt (WithTop.coe_pos.mp hp) Nat.one_pos

中文:
定理 coeff_natTrailingDegree_pred_eq_zero
  条件: {p : R[X]} {hp : (0 : 自然数∞) < natTrailingDegree p}
  证明: coeff_eq_zero_of_lt_natTrailingDegree
    Nat.sub_lt (WithTop.coe_pos.mp hp) Nat.one_pos

Depends on / 依赖: Nat.one_pos, Nat.sub_lt, WithTop, WithTop.coe_pos.mp, coe_pos, coeff_eq_zero_of_lt_natTrailingDegree, one_pos, sub_lt
-/
theorem coeff_natTrailingDegree_pred_eq_zero {p : R[X]} {hp : (0 : Nat∞) < natTrailingDegree p} :
    p.coeff (p.natTrailingDegree - 1) = 0 :=
coeff_eq_zero_of_lt_natTrailingDegree
    Nat.sub_lt (WithTop.coe_pos.mp hp) Nat.one_pos

/--
theorem `le_trailingDegree_X_pow` / 定理 `le_trailingDegree_X_pow`

English:
theorem le_trailingDegree_X_pow
  given: (n : Nat)
  statement: (n : Nat∞) <= trailingDegree (X ^ n : R[X])
  proof: by
  simpa only [C_1, one_mul] using le_trailingDegree_C_mul_X_pow n (1 : R)

中文:
定理 le_trailingDegree_X_pow
  条件: (n : 自然数)
  结论: (n : 自然数∞) <= trailingDegree (X ^ n : R[X])
  证明: by
  simpa only [C_1, one_mul] using le_trailingDegree_C_mul_X_pow n (1 : R)

Depends on / 依赖: le_trailingDegree_C_mul_X_pow, one_mul
-/
theorem le_trailingDegree_X_pow (n : Nat) : (n : Nat∞) <= trailingDegree (X ^ n : R[X]) := by
  simpa only [C_1, one_mul] using le_trailingDegree_C_mul_X_pow n (1 : R)

/--
theorem `le_trailingDegree_X` / 定理 `le_trailingDegree_X`

English:
theorem le_trailingDegree_X
  statement: (1 : Nat∞) <= trailingDegree (X : R[X])
  proof: le_trailingDegree_monomial

中文:
定理 le_trailingDegree_X
  结论: (1 : 自然数∞) <= trailingDegree (X : R[X])
  证明: le_trailingDegree_monomial

Depends on / 依赖: le_trailingDegree_monomial
-/
theorem le_trailingDegree_X : (1 : Nat∞) <= trailingDegree (X : R[X]) :=
  le_trailingDegree_monomial

/--
theorem `natTrailingDegree_X_le` / 定理 `natTrailingDegree_X_le`

English:
theorem natTrailingDegree_X_le
  statement: (X : R[X]).natTrailingDegree <= 1
  proof: natTrailingDegree_monomial_le

@[simp]

中文:
定理 natTrailingDegree_X_le
  结论: (X : R[X]).natTrailingDegree <= 1
  证明: natTrailingDegree_monomial_le

@[simp]

Depends on / 依赖: natTrailingDegree_monomial_le
-/
theorem natTrailingDegree_X_le : (X : R[X]).natTrailingDegree <= 1 :=
  natTrailingDegree_monomial_le

@[simp]
/--
theorem `trailingCoeff_eq_zero` / 定理 `trailingCoeff_eq_zero`

English:
theorem trailingCoeff_eq_zero
  statement: trailingCoeff p = 0 ↔ p = 0
  proof: ⟨fun h =>
    _root_.by_contradiction fun hp =>
      mt mem_support_iff.1 (Classical.not_not.2 h)
        (mem_of_min (trailingDegree_eq_natTrailingDegree hp)),
    fun h => h.symm ▸ leadingCoeff_zero⟩

中文:
定理 trailingCoeff_eq_zero
  结论: trailingCoeff p = 0 ↔ p = 0
  证明: ⟨fun h =>
    _root_.by_contradiction fun hp =>
      mt mem_support_iff.1 (Classical.not_not.2 h)
        (mem_of_min (trailingDegree_eq_natTrailingDegree hp)),
    fun h => h.symm ▸ leadingCoeff_zero⟩

Depends on / 依赖: Classical, Classical.not_not, _root_, _root_.by_contradiction, by_contradiction, h.symm, leadingCoeff_zero, mem_of_min, mem_support_iff, not_not, trailingDegree_eq_natTrailingDegree
-/
theorem trailingCoeff_eq_zero : trailingCoeff p = 0 ↔ p = 0 :=
  ⟨fun h =>
    _root_.by_contradiction fun hp =>
      mt mem_support_iff.1 (Classical.not_not.2 h)
        (mem_of_min (trailingDegree_eq_natTrailingDegree hp)),
    fun h => h.symm ▸ leadingCoeff_zero⟩

/--
theorem `trailingCoeff_nonzero_iff_nonzero` / 定理 `trailingCoeff_nonzero_iff_nonzero`

English:
theorem trailingCoeff_nonzero_iff_nonzero
  statement: trailingCoeff p != 0 ↔ p != 0
  proof: not_congr trailingCoeff_eq_zero

中文:
定理 trailingCoeff_nonzero_iff_nonzero
  结论: trailingCoeff p != 0 ↔ p != 0
  证明: not_congr trailingCoeff_eq_zero

Depends on / 依赖: not_congr, trailingCoeff_eq_zero
-/
theorem trailingCoeff_nonzero_iff_nonzero : trailingCoeff p != 0 ↔ p != 0 :=
  not_congr trailingCoeff_eq_zero

/--
theorem `natTrailingDegree_mem_support_of_nonzero` / 定理 `natTrailingDegree_mem_support_of_nonzero`

English:
theorem natTrailingDegree_mem_support_of_nonzero
  statement: p != 0 -> natTrailingDegree p in p.support
  proof: mem_support_iff.mpr ∘ trailingCoeff_nonzero_iff_nonzero.mpr

中文:
定理 natTrailingDegree_mem_support_of_nonzero
  结论: p != 0 -> natTrailingDegree p in p.support
  证明: mem_support_iff.mpr ∘ trailingCoeff_nonzero_iff_nonzero.mpr

Depends on / 依赖: mem_support_iff, mem_support_iff.mpr, trailingCoeff_nonzero_iff_nonzero, trailingCoeff_nonzero_iff_nonzero.mpr
-/
theorem natTrailingDegree_mem_support_of_nonzero : p != 0 -> natTrailingDegree p in p.support :=
  mem_support_iff.mpr ∘ trailingCoeff_nonzero_iff_nonzero.mpr

/--
theorem `natTrailingDegree_le_of_mem_supp` / 定理 `natTrailingDegree_le_of_mem_supp`

English:
theorem natTrailingDegree_le_of_mem_supp
  given: (a : Nat)
  statement: a in p.support -> natTrailingDegree p <= a
  proof: natTrailingDegree_le_of_ne_zero ∘ mem_support_iff.mp

中文:
定理 natTrailingDegree_le_of_mem_supp
  条件: (a : 自然数)
  结论: a in p.support -> natTrailingDegree p <= a
  证明: natTrailingDegree_le_of_ne_zero ∘ mem_support_iff.mp

Depends on / 依赖: mem_support_iff, mem_support_iff.mp, natTrailingDegree_le_of_ne_zero
-/
theorem natTrailingDegree_le_of_mem_supp (a : Nat) : a in p.support -> natTrailingDegree p <= a :=
  natTrailingDegree_le_of_ne_zero ∘ mem_support_iff.mp

/--
theorem `natTrailingDegree_eq_support_min'` / 定理 `natTrailingDegree_eq_support_min'`

English:
theorem natTrailingDegree_eq_support_min'
  given: (h : p != 0)
  proof: by
  rw [natTrailingDegree]; rw [trailingDegree]; rw [← Finset.coe_min' (support_nonempty.mpr h)]
  norm_cast

中文:
定理 natTrailingDegree_eq_support_min'
  条件: (h : p != 0)
  证明: by
  rw [natTrailingDegree]; rw [trailingDegree]; rw [← Finset.coe_min' (support_nonempty.mpr h)]
  norm_cast

Depends on / 依赖: Finset, Finset.coe_min, coe_min, natTrailingDegree, support_nonempty, support_nonempty.mpr, trailingDegree
-/
theorem natTrailingDegree_eq_support_min' (h : p != 0) :
    natTrailingDegree p = p.support.min' (nonempty_support_iff.mpr h) := by
  rw [natTrailingDegree]; rw [trailingDegree]; rw [← Finset.coe_min' (support_nonempty.mpr h)]
  norm_cast

/--
theorem `le_natTrailingDegree` / 定理 `le_natTrailingDegree`

English:
theorem le_natTrailingDegree
  given: (hp : p != 0) (hn : forall m < n, p.coeff m = 0)
  proof: by
  rw [natTrailingDegree_eq_support_min' hp]
exact Finset.le_min' _ _ _ fun m hm => not_lt.1 fun hmn => mem_support_iff.1 hm hn _ hmn

中文:
定理 le_natTrailingDegree
  条件: (hp : p != 0) (hn : 对任意 m < n, p.coeff m = 0)
  证明: by
  rw [natTrailingDegree_eq_support_min' hp]
exact Finset.le_min' _ _ _ fun m hm => not_lt.1 fun hmn => mem_support_iff.1 hm hn _ hmn

Depends on / 依赖: Finset, Finset.le_min, le_min, mem_support_iff, natTrailingDegree_eq_support_min, not_lt
-/
theorem le_natTrailingDegree (hp : p != 0) (hn : forall m < n, p.coeff m = 0) :
    n <= p.natTrailingDegree := by
  rw [natTrailingDegree_eq_support_min' hp]
exact Finset.le_min' _ _ _ fun m hm => not_lt.1 fun hmn => mem_support_iff.1 hm hn _ hmn

/--
theorem `natTrailingDegree_le_natDegree` / 定理 `natTrailingDegree_le_natDegree`

English:
theorem natTrailingDegree_le_natDegree
  given: (p : R[X])
  statement: p.natTrailingDegree <= p.natDegree
  proof: by
  by_cases hp : p = 0
  · rw [hp, natDegree_zero, natTrailingDegree_zero]
  · exact le_natDegree_of_ne_zero (mt trailingCoeff_eq_zero.mp hp)

中文:
定理 natTrailingDegree_le_natDegree
  条件: (p : R[X])
  结论: p.natTrailingDegree <= p.natDegree
  证明: by
  by_cases hp : p = 0
  · rw [hp, natDegree_zero, natTrailingDegree_zero]
  · exact le_natDegree_of_ne_zero (mt trailingCoeff_eq_zero.mp hp)

Depends on / 依赖: le_natDegree_of_ne_zero, natDegree_zero, natTrailingDegree_zero, trailingCoeff_eq_zero, trailingCoeff_eq_zero.mp
-/
theorem natTrailingDegree_le_natDegree (p : R[X]) : p.natTrailingDegree <= p.natDegree := by
  by_cases hp : p = 0
  · rw [hp, natDegree_zero, natTrailingDegree_zero]
  · exact le_natDegree_of_ne_zero (mt trailingCoeff_eq_zero.mp hp)

/--
theorem `natTrailingDegree_mul_X_pow` / 定理 `natTrailingDegree_mul_X_pow`

English:
theorem natTrailingDegree_mul_X_pow
  given: {p : R[X]} (hp : p != 0) (n : Nat)
  proof: by
  apply le_antisymm
  · refine natTrailingDegree_le_of_ne_zero fun h => mt trailingCoeff_eq_zero.mp hp ?_
    rwa [trailingCoeff, ← coeff_mul_X_pow]
  · rw [natTrailingDegree_eq_support_min' fun h => hp (mul_X_pow_eq_zero h), Finset.le_min'_iff]
    intro y hy
    have key : n <= y := by
      rw [mem_support_iff]; rw [coeff_mul_X_pow'] at hy
      exact by_contra fun h => hy (if_neg h)
    rw [mem_support_iff]; rw [coeff_mul_X_pow']; rw [if_pos key] at hy
    exact (le_tsub_iff_right key).mp (natTrailingDegree_le_of_ne_zero hy)

中文:
定理 natTrailingDegree_mul_X_pow
  条件: {p : R[X]} (hp : p != 0) (n : 自然数)
  证明: by
  apply le_antisymm
  · refine natTrailingDegree_le_of_ne_zero fun h => mt trailingCoeff_eq_zero.mp hp ?_
    rwa [trailingCoeff, ← coeff_mul_X_pow]
  · rw [natTrailingDegree_eq_support_min' fun h => hp (mul_X_pow_eq_zero h), Finset.le_min'_iff]
    intro y hy
    have key : n <= y := by
      rw [mem_support_iff]; rw [coeff_mul_X_pow'] at hy
      exact by_contra fun h => hy (if_neg h)
    rw [mem_support_iff]; rw [coeff_mul_X_pow']; rw [if_pos key] at hy
    exact (le_tsub_iff_right key).mp (natTrailingDegree_le_of_ne_zero hy)

Depends on / 依赖: Finset, Finset.le_min, _iff, coeff_mul_X_pow, if_neg, if_pos, le_antisymm, le_min, le_tsub_iff_right, mem_support_iff, mul_X_pow_eq_zero, natTrailingDegree_eq_support_min, natTrailingDegree_le_of_ne_zero, trailingCoeff, trailingCoeff_eq_zero, trailingCoeff_eq_zero.mp
-/
theorem natTrailingDegree_mul_X_pow {p : R[X]} (hp : p != 0) (n : Nat) :
    (p * X ^ n).natTrailingDegree = p.natTrailingDegree + n := by
  apply le_antisymm
  · refine natTrailingDegree_le_of_ne_zero fun h => mt trailingCoeff_eq_zero.mp hp ?_
    rwa [trailingCoeff, ← coeff_mul_X_pow]
  · rw [natTrailingDegree_eq_support_min' fun h => hp (mul_X_pow_eq_zero h), Finset.le_min'_iff]
    intro y hy
    have key : n <= y := by
      rw [mem_support_iff]; rw [coeff_mul_X_pow'] at hy
      exact by_contra fun h => hy (if_neg h)
    rw [mem_support_iff]; rw [coeff_mul_X_pow']; rw [if_pos key] at hy
    exact (le_tsub_iff_right key).mp (natTrailingDegree_le_of_ne_zero hy)

/--
theorem `le_trailingDegree_mul` / 定理 `le_trailingDegree_mul`

English:
theorem le_trailingDegree_mul
  statement: p.trailingDegree + q.trailingDegree <= (p * q).trailingDegree
  proof: by
  refine Finset.le_min fun n hn => ?_
  rw [mem_support_iff]; rw [coeff_mul] at hn
  obtain ⟨⟨i, j⟩, hij, hpq⟩ := exists_ne_zero_of_sum_ne_zero hn
  refine
    (add_le_add (min_le (mem_support_iff.mpr (left_ne_zero_of_mul hpq)))
          (min_le (mem_support_iff.mpr (right_ne_zero_of_mul hpq)))).trans_eq ?_
  rwa [← WithTop.coe_add, WithTop.coe_eq_coe, ← mem_antidiagonal]

中文:
定理 le_trailingDegree_mul
  结论: p.trailingDegree + q.trailingDegree <= (p * q).trailingDegree
  证明: by
  refine Finset.le_min fun n hn => ?_
  rw [mem_support_iff]; rw [coeff_mul] at hn
  obtain ⟨⟨i, j⟩, hij, hpq⟩ := exists_ne_zero_of_sum_ne_zero hn
  refine
    (add_le_add (min_le (mem_support_iff.mpr (left_ne_zero_of_mul hpq)))
          (min_le (mem_support_iff.mpr (right_ne_zero_of_mul hpq)))).trans_eq ?_
  rwa [← WithTop.coe_add, WithTop.coe_eq_coe, ← mem_antidiagonal]

Depends on / 依赖: Finset, Finset.le_min, WithTop, WithTop.coe_add, WithTop.coe_eq_coe, add_le_add, coe_add, coe_eq_coe, coeff_mul, exists_ne_zero_of_sum_ne_zero, le_min, left_ne_zero_of_mul, mem_antidiagonal, mem_support_iff, mem_support_iff.mpr, min_le, right_ne_zero_of_mul, trans_eq
-/
theorem le_trailingDegree_mul : p.trailingDegree + q.trailingDegree <= (p * q).trailingDegree := by
  refine Finset.le_min fun n hn => ?_
  rw [mem_support_iff]; rw [coeff_mul] at hn
  obtain ⟨⟨i, j⟩, hij, hpq⟩ := exists_ne_zero_of_sum_ne_zero hn
  refine
    (add_le_add (min_le (mem_support_iff.mpr (left_ne_zero_of_mul hpq)))
          (min_le (mem_support_iff.mpr (right_ne_zero_of_mul hpq)))).trans_eq ?_
  rwa [← WithTop.coe_add, WithTop.coe_eq_coe, ← mem_antidiagonal]

/--
theorem `le_natTrailingDegree_mul` / 定理 `le_natTrailingDegree_mul`

English:
theorem le_natTrailingDegree_mul
  given: (h : p * q != 0)
  proof: by
  have hp : p != 0 := fun hp => h (by rw [hp, zero_mul])
  have hq : q != 0 := fun hq => h (by rw [hq, mul_zero])
  rw [← ENat.natCast_le_natCast]; rw [ENat.natCast_add]; rw [← trailingDegree_eq_natTrailingDegree hp]; rw [← trailingDegree_eq_natTrailingDegree hq]; rw [← trailingDegree_eq_natTrailingDegree h]
  exact le_trailingDegree_mul

中文:
定理 le_natTrailingDegree_mul
  条件: (h : p * q != 0)
  证明: by
  have hp : p != 0 := fun hp => h (by rw [hp, zero_mul])
  have hq : q != 0 := fun hq => h (by rw [hq, mul_zero])
  rw [← ENat.natCast_le_natCast]; rw [ENat.natCast_add]; rw [← trailingDegree_eq_natTrailingDegree hp]; rw [← trailingDegree_eq_natTrailingDegree hq]; rw [← trailingDegree_eq_natTrailingDegree h]
  exact le_trailingDegree_mul

Depends on / 依赖: ENat.natCast_add, ENat.natCast_le_natCast, le_trailingDegree_mul, mul_zero, natCast_add, natCast_le_natCast, trailingDegree_eq_natTrailingDegree, zero_mul
-/
theorem le_natTrailingDegree_mul (h : p * q != 0) :
    p.natTrailingDegree + q.natTrailingDegree <= (p * q).natTrailingDegree := by
  have hp : p != 0 := fun hp => h (by rw [hp, zero_mul])
  have hq : q != 0 := fun hq => h (by rw [hq, mul_zero])
  rw [← ENat.natCast_le_natCast]; rw [ENat.natCast_add]; rw [← trailingDegree_eq_natTrailingDegree hp]; rw [← trailingDegree_eq_natTrailingDegree hq]; rw [← trailingDegree_eq_natTrailingDegree h]
  exact le_trailingDegree_mul

/--
theorem `coeff_mul_natTrailingDegree_add_natTrailingDegree` / 定理 `coeff_mul_natTrailingDegree_add_natTrailingDegree`

English:
theorem coeff_mul_natTrailingDegree_add_natTrailingDegree
  statement: (p * q).coeff
  proof: by
  rw [coeff_mul]
  refine
    Finset.sum_eq_single (p.natTrailingDegree, q.natTrailingDegree) ?_ fun h =>
      (h (mem_antidiagonal.mpr rfl)).elim
  rintro ⟨i, j⟩ h₁ h₂
  rw [mem_antidiagonal] at h₁
  by_cases! hi : i < p.natTrailingDegree
  · rw [coeff_eq_zero_of_lt_natTrailingDegree hi, zero_mul]
  by_cases! hj : j < q.natTrailingDegree
  · rw [coeff_eq_zero_of_lt_natTrailingDegree hj, mul_zero]
  refine (h₂ (Prod.ext_iff.mpr ?_).symm).elim
  exact (add_eq_add_iff_eq_and_eq hi hj).mp h₁.symm

中文:
定理 coeff_mul_natTrailingDegree_add_natTrailingDegree
  结论: (p * q).coeff
  证明: by
  rw [coeff_mul]
  refine
    Finset.sum_eq_single (p.natTrailingDegree, q.natTrailingDegree) ?_ fun h =>
      (h (mem_antidiagonal.mpr rfl)).elim
  rintro ⟨i, j⟩ h₁ h₂
  rw [mem_antidiagonal] at h₁
  by_cases! hi : i < p.natTrailingDegree
  · rw [coeff_eq_zero_of_lt_natTrailingDegree hi, zero_mul]
  by_cases! hj : j < q.natTrailingDegree
  · rw [coeff_eq_zero_of_lt_natTrailingDegree hj, mul_zero]
  refine (h₂ (Prod.ext_iff.mpr ?_).symm).elim
  exact (add_eq_add_iff_eq_and_eq hi hj).mp h₁.symm

Depends on / 依赖: Finset, Finset.sum_eq_single, Prod.ext_iff.mpr, add_eq_add_iff_eq_and_eq, coeff_eq_zero_of_lt_natTrailingDegree, coeff_mul, ext_iff, mem_antidiagonal, mem_antidiagonal.mpr, mul_zero, natTrailingDegree, p.natTrailingDegree, q.natTrailingDegree, sum_eq_single, zero_mul
-/
theorem coeff_mul_natTrailingDegree_add_natTrailingDegree : (p * q).coeff
    (p.natTrailingDegree + q.natTrailingDegree) = p.trailingCoeff * q.trailingCoeff := by
  rw [coeff_mul]
  refine
    Finset.sum_eq_single (p.natTrailingDegree, q.natTrailingDegree) ?_ fun h =>
      (h (mem_antidiagonal.mpr rfl)).elim
  rintro ⟨i, j⟩ h₁ h₂
  rw [mem_antidiagonal] at h₁
  by_cases! hi : i < p.natTrailingDegree
  · rw [coeff_eq_zero_of_lt_natTrailingDegree hi, zero_mul]
  by_cases! hj : j < q.natTrailingDegree
  · rw [coeff_eq_zero_of_lt_natTrailingDegree hj, mul_zero]
  refine (h₂ (Prod.ext_iff.mpr ?_).symm).elim
  exact (add_eq_add_iff_eq_and_eq hi hj).mp h₁.symm

/--
theorem `trailingDegree_mul'` / 定理 `trailingDegree_mul'`

English:
theorem trailingDegree_mul'
  given: (h : p.trailingCoeff * q.trailingCoeff != 0)
  proof: by
  have hp : p != 0 := fun hp => h (by rw [hp, trailingCoeff_zero, zero_mul])
  have hq : q != 0 := fun hq => h (by rw [hq, trailingCoeff_zero, mul_zero])
  refine le_antisymm ?_ le_trailingDegree_mul
  rw [trailingDegree_eq_natTrailingDegree hp]; rw [trailingDegree_eq_natTrailingDegree hq]; rw [←
    ENat.natCast_add]
  apply trailingDegree_le_of_ne_zero
  rwa [coeff_mul_natTrailingDegree_add_natTrailingDegree]

中文:
定理 trailingDegree_mul'
  条件: (h : p.trailingCoeff * q.trailingCoeff != 0)
  证明: by
  have hp : p != 0 := fun hp => h (by rw [hp, trailingCoeff_zero, zero_mul])
  have hq : q != 0 := fun hq => h (by rw [hq, trailingCoeff_zero, mul_zero])
  refine le_antisymm ?_ le_trailingDegree_mul
  rw [trailingDegree_eq_natTrailingDegree hp]; rw [trailingDegree_eq_natTrailingDegree hq]; rw [←
    ENat.natCast_add]
  apply trailingDegree_le_of_ne_zero
  rwa [coeff_mul_natTrailingDegree_add_natTrailingDegree]

Depends on / 依赖: ENat.natCast_add, coeff_mul_natTrailingDegree_add_natTrailingDegree, le_antisymm, le_trailingDegree_mul, mul_zero, natCast_add, trailingCoeff_zero, trailingDegree_eq_natTrailingDegree, trailingDegree_le_of_ne_zero, zero_mul
-/
theorem trailingDegree_mul' (h : p.trailingCoeff * q.trailingCoeff != 0) :
    (p * q).trailingDegree = p.trailingDegree + q.trailingDegree := by
  have hp : p != 0 := fun hp => h (by rw [hp, trailingCoeff_zero, zero_mul])
  have hq : q != 0 := fun hq => h (by rw [hq, trailingCoeff_zero, mul_zero])
  refine le_antisymm ?_ le_trailingDegree_mul
  rw [trailingDegree_eq_natTrailingDegree hp]; rw [trailingDegree_eq_natTrailingDegree hq]; rw [←
    ENat.natCast_add]
  apply trailingDegree_le_of_ne_zero
  rwa [coeff_mul_natTrailingDegree_add_natTrailingDegree]

/--
theorem `natTrailingDegree_mul'` / 定理 `natTrailingDegree_mul'`

English:
theorem natTrailingDegree_mul'
  given: (h : p.trailingCoeff * q.trailingCoeff != 0)
  proof: by
  have hp : p != 0 := fun hp => h (by rw [hp, trailingCoeff_zero, zero_mul])
  have hq : q != 0 := fun hq => h (by rw [hq, trailingCoeff_zero, mul_zero])
  apply natTrailingDegree_eq_of_trailingDegree_eq_some
  rw [trailingDegree_mul' h]; rw [ENat.natCast_add]; rw [← trailingDegree_eq_natTrailingDegree hp]; rw [← trailingDegree_eq_natTrailingDegree hq]

中文:
定理 natTrailingDegree_mul'
  条件: (h : p.trailingCoeff * q.trailingCoeff != 0)
  证明: by
  have hp : p != 0 := fun hp => h (by rw [hp, trailingCoeff_zero, zero_mul])
  have hq : q != 0 := fun hq => h (by rw [hq, trailingCoeff_zero, mul_zero])
  apply natTrailingDegree_eq_of_trailingDegree_eq_some
  rw [trailingDegree_mul' h]; rw [ENat.natCast_add]; rw [← trailingDegree_eq_natTrailingDegree hp]; rw [← trailingDegree_eq_natTrailingDegree hq]

Depends on / 依赖: ENat.natCast_add, mul_zero, natCast_add, natTrailingDegree_eq_of_trailingDegree_eq_some, trailingCoeff_zero, trailingDegree_eq_natTrailingDegree, trailingDegree_mul, zero_mul
-/
theorem natTrailingDegree_mul' (h : p.trailingCoeff * q.trailingCoeff != 0) :
    (p * q).natTrailingDegree = p.natTrailingDegree + q.natTrailingDegree := by
  have hp : p != 0 := fun hp => h (by rw [hp, trailingCoeff_zero, zero_mul])
  have hq : q != 0 := fun hq => h (by rw [hq, trailingCoeff_zero, mul_zero])
  apply natTrailingDegree_eq_of_trailingDegree_eq_some
  rw [trailingDegree_mul' h]; rw [ENat.natCast_add]; rw [← trailingDegree_eq_natTrailingDegree hp]; rw [← trailingDegree_eq_natTrailingDegree hq]

/--
theorem `natTrailingDegree_mul` / 定理 `natTrailingDegree_mul`

English:
theorem natTrailingDegree_mul
  given: [NoZeroDivisors R] (hp : p != 0) (hq : q != 0)
  proof: natTrailingDegree_mul'
    (mul_ne_zero (mt trailingCoeff_eq_zero.mp hp) (mt trailingCoeff_eq_zero.mp hq))

中文:
定理 natTrailingDegree_mul
  条件: [无零因子 R] (hp : p != 0) (hq : q != 0)
  证明: natTrailingDegree_mul'
    (mul_ne_zero (mt trailingCoeff_eq_zero.mp hp) (mt trailingCoeff_eq_zero.mp hq))

Depends on / 依赖: mul_ne_zero, natTrailingDegree_mul, trailingCoeff_eq_zero, trailingCoeff_eq_zero.mp
-/
theorem natTrailingDegree_mul [NoZeroDivisors R] (hp : p != 0) (hq : q != 0) :
    (p * q).natTrailingDegree = p.natTrailingDegree + q.natTrailingDegree :=
  natTrailingDegree_mul'
    (mul_ne_zero (mt trailingCoeff_eq_zero.mp hp) (mt trailingCoeff_eq_zero.mp hq))

end Semiring

section NonzeroSemiring

variable [Semiring R] [Nontrivial R] {p q : R[X]}

@[simp]
/--
theorem `trailingDegree_one` / 定理 `trailingDegree_one`

English:
theorem trailingDegree_one
  statement: trailingDegree (1 : R[X]) = (0 : Nat∞)
  proof: trailingDegree_C one_ne_zero

@[simp]

中文:
定理 trailingDegree_one
  结论: trailingDegree (1 : R[X]) = (0 : 自然数∞)
  证明: trailingDegree_C one_ne_zero

@[simp]

Depends on / 依赖: one_ne_zero, trailingDegree_C
-/
theorem trailingDegree_one : trailingDegree (1 : R[X]) = (0 : Nat∞) :=
  trailingDegree_C one_ne_zero

@[simp]
/--
theorem `trailingDegree_X` / 定理 `trailingDegree_X`

English:
theorem trailingDegree_X
  statement: trailingDegree (X : R[X]) = 1
  proof: trailingDegree_monomial one_ne_zero

@[simp]

中文:
定理 trailingDegree_X
  结论: trailingDegree (X : R[X]) = 1
  证明: trailingDegree_monomial one_ne_zero

@[simp]

Depends on / 依赖: one_ne_zero, trailingDegree_monomial
-/
theorem trailingDegree_X : trailingDegree (X : R[X]) = 1 :=
  trailingDegree_monomial one_ne_zero

@[simp]
/--
theorem `natTrailingDegree_X` / 定理 `natTrailingDegree_X`

English:
theorem natTrailingDegree_X
  statement: (X : R[X]).natTrailingDegree = 1
  proof: natTrailingDegree_monomial one_ne_zero

@[simp]

中文:
定理 natTrailingDegree_X
  结论: (X : R[X]).natTrailingDegree = 1
  证明: natTrailingDegree_monomial one_ne_zero

@[simp]

Depends on / 依赖: natTrailingDegree_monomial, one_ne_zero
-/
theorem natTrailingDegree_X : (X : R[X]).natTrailingDegree = 1 :=
  natTrailingDegree_monomial one_ne_zero

@[simp]
/--
lemma `trailingDegree_X_pow` / 引理 `trailingDegree_X_pow`

English:
lemma trailingDegree_X_pow
  given: (n : Nat)
  proof: by
  rw [X_pow_eq_monomial]; rw [trailingDegree_monomial one_ne_zero]

@[simp]

中文:
引理 trailingDegree_X_pow
  条件: (n : 自然数)
  证明: by
  rw [X_pow_eq_monomial]; rw [trailingDegree_monomial one_ne_zero]

@[simp]

Depends on / 依赖: X_pow_eq_monomial, one_ne_zero, trailingDegree_monomial
-/
lemma trailingDegree_X_pow (n : Nat) :
    (X ^ n : R[X]).trailingDegree = n := by
  rw [X_pow_eq_monomial]; rw [trailingDegree_monomial one_ne_zero]

@[simp]
/--
lemma `natTrailingDegree_X_pow` / 引理 `natTrailingDegree_X_pow`

English:
lemma natTrailingDegree_X_pow
  given: (n : Nat)
  proof: by
  rw [X_pow_eq_monomial]; rw [natTrailingDegree_monomial one_ne_zero]

中文:
引理 natTrailingDegree_X_pow
  条件: (n : 自然数)
  证明: by
  rw [X_pow_eq_monomial]; rw [natTrailingDegree_monomial one_ne_zero]

Depends on / 依赖: X_pow_eq_monomial, natTrailingDegree_monomial, one_ne_zero
-/
lemma natTrailingDegree_X_pow (n : Nat) :
    (X ^ n : R[X]).natTrailingDegree = n := by
  rw [X_pow_eq_monomial]; rw [natTrailingDegree_monomial one_ne_zero]

end NonzeroSemiring

section Ring

variable [Ring R]

@[simp]
/--
theorem `trailingDegree_neg` / 定理 `trailingDegree_neg`

English:
theorem trailingDegree_neg
  given: (p : R[X])
  statement: trailingDegree (-p) = trailingDegree p
  proof: by
  unfold trailingDegree
  rw [support_neg]

@[simp]

中文:
定理 trailingDegree_neg
  条件: (p : R[X])
  结论: trailingDegree (-p) = trailingDegree p
  证明: by
  unfold trailingDegree
  rw [support_neg]

@[simp]

Depends on / 依赖: support_neg, trailingDegree
-/
theorem trailingDegree_neg (p : R[X]) : trailingDegree (-p) = trailingDegree p := by
  unfold trailingDegree
  rw [support_neg]

@[simp]
/--
theorem `natTrailingDegree_neg` / 定理 `natTrailingDegree_neg`

English:
theorem natTrailingDegree_neg
  given: (p : R[X])
  statement: natTrailingDegree (-p) = natTrailingDegree p
  proof: by
  simp [natTrailingDegree]

@[simp]

中文:
定理 natTrailingDegree_neg
  条件: (p : R[X])
  结论: natTrailingDegree (-p) = natTrailingDegree p
  证明: by
  simp [natTrailingDegree]

@[simp]

Depends on / 依赖: natTrailingDegree
-/
theorem natTrailingDegree_neg (p : R[X]) : natTrailingDegree (-p) = natTrailingDegree p := by
  simp [natTrailingDegree]

@[simp]
/--
theorem `natTrailingDegree_intCast` / 定理 `natTrailingDegree_intCast`

English:
theorem natTrailingDegree_intCast
  given: (n : Int)
  statement: natTrailingDegree (n : R[X]) = 0
  proof: by
  simp only [← C_eq_intCast, natTrailingDegree_C]

中文:
定理 natTrailingDegree_intCast
  条件: (n : 整数)
  结论: natTrailingDegree (n : R[X]) = 0
  证明: by
  simp only [← C_eq_intCast, natTrailingDegree_C]

Depends on / 依赖: C_eq_intCast, MulSemiringAction, MulSemiringAction.toMulDistribMulAction, natTrailingDegree_C, toMulDistribMulAction
-/
theorem natTrailingDegree_intCast (n : Int) : natTrailingDegree (n : R[X]) = 0 := by
  simp only [← C_eq_intCast, natTrailingDegree_C]

end Ring

section Semiring

variable [Semiring R]

/--
Definition of `nextCoeffUp` / `nextCoeffUp` 的定义

English:
definition nextCoeffUp
  signature: (p : R[X])
  body: if p.natTrailingDegree = 0 then 0 else p.coeff (p.natTrailingDegree + 1)

中文:
定义 nextCoeffUp
  签名: (p : R[X])
  定义体: if p.natTrailingDegree = 0 then 0 else p.coeff (p.natTrailingDegree + 1)

Depends on / 依赖: natTrailingDegree, p.coeff, p.natTrailingDegree
-/
def nextCoeffUp (p : R[X]) : R :=
  if p.natTrailingDegree = 0 then 0 else p.coeff (p.natTrailingDegree + 1)

/--
lemma `nextCoeffUp_zero` / 引理 `nextCoeffUp_zero`

English:
lemma nextCoeffUp_zero
  statement: nextCoeffUp (0 : R[X]) = 0
  proof: by simp [nextCoeffUp]

@[simp]

中文:
引理 nextCoeffUp_zero
  结论: nextCoeffUp (0 : R[X]) = 0
  证明: by simp [nextCoeffUp]

@[simp]
-/
@[simp] lemma nextCoeffUp_zero : nextCoeffUp (0 : R[X]) = 0 := by simp [nextCoeffUp]

@[simp]
/--
theorem `nextCoeffUp_C_eq_zero` / 定理 `nextCoeffUp_C_eq_zero`

English:
theorem nextCoeffUp_C_eq_zero
  given: (c : R)
  statement: nextCoeffUp (C c) = 0
  proof: by
  rw [nextCoeffUp]
  simp

中文:
定理 nextCoeffUp_C_eq_zero
  条件: (c : R)
  结论: nextCoeffUp (C c) = 0
  证明: by
  rw [nextCoeffUp]
  simp

Depends on / 依赖: nextCoeffUp
-/
theorem nextCoeffUp_C_eq_zero (c : R) : nextCoeffUp (C c) = 0 := by
  rw [nextCoeffUp]
  simp

/--
theorem `nextCoeffUp_of_constantCoeff_eq_zero` / 定理 `nextCoeffUp_of_constantCoeff_eq_zero`

English:
theorem nextCoeffUp_of_constantCoeff_eq_zero
  given: (p : R[X]) (hp : coeff p 0 = 0)
  proof: by
  obtain rfl | hp₀ := eq_or_ne p 0
  · simp
  · rw [nextCoeffUp, if_neg (natTrailingDegree_ne_zero.2 ⟨hp₀, hp⟩)]

中文:
定理 nextCoeffUp_of_constantCoeff_eq_zero
  条件: (p : R[X]) (hp : coeff p 0 = 0)
  证明: by
  obtain rfl | hp₀ := eq_or_ne p 0
  · simp
  · rw [nextCoeffUp, if_neg (natTrailingDegree_ne_zero.2 ⟨hp₀, hp⟩)]

Depends on / 依赖: eq_or_ne, if_neg, natTrailingDegree_ne_zero, nextCoeffUp
-/
theorem nextCoeffUp_of_constantCoeff_eq_zero (p : R[X]) (hp : coeff p 0 = 0) :
    nextCoeffUp p = p.coeff (p.natTrailingDegree + 1) := by
  obtain rfl | hp₀ := eq_or_ne p 0
  · simp
  · rw [nextCoeffUp, if_neg (natTrailingDegree_ne_zero.2 ⟨hp₀, hp⟩)]

end Semiring

section Semiring

variable [Semiring R] {p q : R[X]}

/--
theorem `coeff_natTrailingDegree_eq_zero_of_trailingDegree_lt` / 定理 `coeff_natTrailingDegree_eq_zero_of_trailingDegree_lt`

English:
theorem coeff_natTrailingDegree_eq_zero_of_trailingDegree_lt
  proof: coeff_eq_zero_of_lt_trailingDegree natTrailingDegree_le_trailingDegree.trans_lt h

中文:
定理 coeff_natTrailingDegree_eq_zero_of_trailingDegree_lt
  证明: coeff_eq_zero_of_lt_trailingDegree natTrailingDegree_le_trailingDegree.trans_lt h

Depends on / 依赖: coeff_eq_zero_of_lt_trailingDegree, natTrailingDegree_le_trailingDegree, natTrailingDegree_le_trailingDegree.trans_lt, trans_lt
-/
theorem coeff_natTrailingDegree_eq_zero_of_trailingDegree_lt
    (h : trailingDegree p < trailingDegree q) : coeff q (natTrailingDegree p) = 0 :=
coeff_eq_zero_of_lt_trailingDegree natTrailingDegree_le_trailingDegree.trans_lt h

/--
theorem `ne_zero_of_trailingDegree_lt` / 定理 `ne_zero_of_trailingDegree_lt`

English:
theorem ne_zero_of_trailingDegree_lt
  given: {n : Nat∞} (h : trailingDegree p < n)
  statement: p != 0
  proof: fun h₀ =>
  h.not_ge (by simp [h₀])

中文:
定理 ne_zero_of_trailingDegree_lt
  条件: {n : 自然数∞} (h : trailingDegree p < n)
  结论: p != 0
  证明: fun h₀ =>
  h.not_ge (by simp [h₀])
-/
theorem ne_zero_of_trailingDegree_lt {n : Nat∞} (h : trailingDegree p < n) : p != 0 := fun h₀ =>
  h.not_ge (by simp [h₀])

/--
lemma `natTrailingDegree_eq_zero_of_constantCoeff_ne_zero` / 引理 `natTrailingDegree_eq_zero_of_constantCoeff_ne_zero`

English:
lemma natTrailingDegree_eq_zero_of_constantCoeff_ne_zero
  given: (h : constantCoeff p != 0)
  proof: eq_zero_of_nonpos (natTrailingDegree_le_of_ne_zero h)

中文:
引理 natTrailingDegree_eq_zero_of_constantCoeff_ne_zero
  条件: (h : constantCoeff p != 0)
  证明: eq_zero_of_nonpos (natTrailingDegree_le_of_ne_zero h)

Depends on / 依赖: eq_zero_of_nonpos, natTrailingDegree_le_of_ne_zero
-/
lemma natTrailingDegree_eq_zero_of_constantCoeff_ne_zero (h : constantCoeff p != 0) :
    p.natTrailingDegree = 0 :=
  eq_zero_of_nonpos (natTrailingDegree_le_of_ne_zero h)

namespace Monic

/--
lemma `eq_X_pow_iff_natDegree_le_natTrailingDegree` / 引理 `eq_X_pow_iff_natDegree_le_natTrailingDegree`

English:
lemma eq_X_pow_iff_natDegree_le_natTrailingDegree
  given: (h₁ : p.Monic)
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · nontriviality R
    rw [h]; rw [natTrailingDegree_X_pow]; rw [← h]
  · ext n
    rw [coeff_X_pow]
    obtain hn | rfl | hn := lt_trichotomy n p.natDegree
    · rw [if_neg hn.ne, coeff_eq_zero_of_lt_natTrailingDegree (hn.trans_le h)]
    · simpa only [if_pos rfl] using! h₁.leadingCoeff
    · rw [if_neg hn.ne', coeff_eq_zero_of_natDegree_lt hn]

中文:
引理 eq_X_pow_iff_natDegree_le_natTrailingDegree
  条件: (h₁ : p.Monic)
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · nontriviality R
    rw [h]; rw [natTrailingDegree_X_pow]; rw [← h]
  · ext n
    rw [coeff_X_pow]
    obtain hn | rfl | hn := lt_trichotomy n p.natDegree
    · rw [if_neg hn.ne, coeff_eq_zero_of_lt_natTrailingDegree (hn.trans_le h)]
    · simpa only [if_pos rfl] using! h₁.leadingCoeff
    · rw [if_neg hn.ne', coeff_eq_zero_of_natDegree_lt hn]

Depends on / 依赖: coeff_X_pow, coeff_eq_zero_of_lt_natTrailingDegree, coeff_eq_zero_of_natDegree_lt, hn.ne, hn.trans_le, if_neg, if_pos, leadingCoeff, lt_trichotomy, natDegree, natTrailingDegree_X_pow, nontriviality, p.natDegree, trans_le
-/
lemma eq_X_pow_iff_natDegree_le_natTrailingDegree (h₁ : p.Monic) :
    p = X ^ p.natDegree ↔ p.natDegree <= p.natTrailingDegree := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · nontriviality R
    rw [h]; rw [natTrailingDegree_X_pow]; rw [← h]
  · ext n
    rw [coeff_X_pow]
    obtain hn | rfl | hn := lt_trichotomy n p.natDegree
    · rw [if_neg hn.ne, coeff_eq_zero_of_lt_natTrailingDegree (hn.trans_le h)]
    · simpa only [if_pos rfl] using! h₁.leadingCoeff
    · rw [if_neg hn.ne', coeff_eq_zero_of_natDegree_lt hn]

/--
lemma `eq_X_pow_iff_natTrailingDegree_eq_natDegree` / 引理 `eq_X_pow_iff_natTrailingDegree_eq_natDegree`

English:
lemma eq_X_pow_iff_natTrailingDegree_eq_natDegree
  given: (h₁ : p.Monic)
  proof: h₁.eq_X_pow_iff_natDegree_le_natTrailingDegree.trans (natTrailingDegree_le_natDegree p).ge_iff_eq

中文:
引理 eq_X_pow_iff_natTrailingDegree_eq_natDegree
  条件: (h₁ : p.Monic)
  证明: h₁.eq_X_pow_iff_natDegree_le_natTrailingDegree.trans (natTrailingDegree_le_natDegree p).ge_iff_eq

Depends on / 依赖: eq_X_pow_iff_natDegree_le_natTrailingDegree, eq_X_pow_iff_natDegree_le_natTrailingDegree.trans, ge_iff_eq, natTrailingDegree_le_natDegree
-/
lemma eq_X_pow_iff_natTrailingDegree_eq_natDegree (h₁ : p.Monic) :
    p = X ^ p.natDegree ↔ p.natTrailingDegree = p.natDegree :=
  h₁.eq_X_pow_iff_natDegree_le_natTrailingDegree.trans (natTrailingDegree_le_natDegree p).ge_iff_eq

end Monic

end Semiring

end Polynomial
