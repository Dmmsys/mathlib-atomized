/-
Copyright (c) 2022 Eric Wieser, Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Yaël Dillies, Andrew Yang
-/
module

public import Mathlib.Algebra.Order.Ring.Canonical
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# `Finset.sup` and ring operations
-/

public section

open Finset

namespace Nat
variable {ι R : Type*}

section LinearOrderedSemiring
variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] {s : Finset ι}

set_option linter.docPrime false in
@[simp, norm_cast]
/--
lemma `cast_finsetSup'` / 引理 `cast_finsetSup'`

English:
lemma cast_finsetSup'
  given: (f : ι -> Nat) (hs)
  statement: ((s.sup' hs f : Nat) : R) = s.sup' hs fun i => (f i : R)
  proof: apply_sup'_eq_sup'_comp _ _ cast_max

中文:
引理 cast_finsetSup'
  条件: (f : ι -> 自然数) (hs)
  结论: ((s.sup' hs f : 自然数) : R) = s.sup' hs fun i => (f i : R)
  证明: apply_sup'_eq_sup'_comp _ _ cast_max

Depends on / 依赖: _comp, _eq_sup, apply_sup, cast_max
-/
lemma cast_finsetSup' (f : ι -> Nat) (hs) : ((s.sup' hs f : Nat) : R) = s.sup' hs fun i => (f i : R) :=
  apply_sup'_eq_sup'_comp _ _ cast_max

set_option linter.docPrime false in
@[simp, norm_cast]
/--
lemma `cast_finsetInf'` / 引理 `cast_finsetInf'`

English:
lemma cast_finsetInf'
  given: (f : ι -> Nat) (hs)
  statement: (↑(s.inf' hs f) : R) = s.inf' hs fun i => (f i : R)
  proof: apply_inf'_eq_inf'_comp _ _ cast_min

@[simp, norm_cast]

中文:
引理 cast_finsetInf'
  条件: (f : ι -> 自然数) (hs)
  结论: (↑(s.inf' hs f) : R) = s.inf' hs fun i => (f i : R)
  证明: apply_inf'_eq_inf'_comp _ _ cast_min

@[simp, norm_cast]

Depends on / 依赖: _comp, _eq_inf, apply_inf, cast_min
-/
lemma cast_finsetInf' (f : ι -> Nat) (hs) : (↑(s.inf' hs f) : R) = s.inf' hs fun i => (f i : R) :=
  apply_inf'_eq_inf'_comp _ _ cast_min

@[simp, norm_cast]
/--
lemma `cast_finsetSup` / 引理 `cast_finsetSup`

English:
lemma cast_finsetSup
  given: [OrderBot R] [CanonicallyOrderedAdd R] (s : Finset ι) (f : ι -> Nat)
  proof: apply_sup_eq_sup_comp _ cast_max (by simp)

中文:
引理 cast_finsetSup
  条件: [OrderBot R] [CanonicallyOrderedAdd R] (s : Finset ι) (f : ι -> 自然数)
  证明: apply_sup_eq_sup_comp _ cast_max (by simp)

Depends on / 依赖: apply_sup_eq_sup_comp, cast_max
-/
lemma cast_finsetSup [OrderBot R] [CanonicallyOrderedAdd R] (s : Finset ι) (f : ι -> Nat) :
    (↑(s.sup f) : R) = s.sup fun i => (f i : R) :=
  apply_sup_eq_sup_comp _ cast_max (by simp)

end LinearOrderedSemiring

end Nat

section

variable {R ι : Type*} [LinearOrder R] [NonUnitalNonAssocSemiring R]
  [CanonicallyOrderedAdd R] [OrderBot R]

/--
lemma `Finset.mul_sup₀` / 引理 `Finset.mul_sup₀`

English:
lemma Finset.mul_sup₀
  given: (s : Finset ι) (f : ι -> R) (a : R)
  proof: by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert _ _ _ IH => simp only [sup_insert, mul_max, ← IH]

中文:
引理 Finset.mul_sup₀
  条件: (s : Finset ι) (f : ι -> R) (a : R)
  证明: by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert _ _ _ IH => simp only [sup_insert, mul_max, ← IH]

Depends on / 依赖: Finset, Finset.induction, classical, insert, mul_max, sup_insert
-/
lemma Finset.mul_sup₀ (s : Finset ι) (f : ι -> R) (a : R) :
    a * s.sup f = s.sup (a * f ·) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert _ _ _ IH => simp only [sup_insert, mul_max, ← IH]

/--
lemma `Finset.sup_mul₀` / 引理 `Finset.sup_mul₀`

English:
lemma Finset.sup_mul₀
  given: (s : Finset ι) (f : ι -> R) (a : R)
  proof: by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert _ _ _ IH => simp only [sup_insert, max_mul, ← IH]

中文:
引理 Finset.sup_mul₀
  条件: (s : Finset ι) (f : ι -> R) (a : R)
  证明: by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert _ _ _ IH => simp only [sup_insert, max_mul, ← IH]

Depends on / 依赖: Finset, Finset.induction, classical, insert, max_mul, sup_insert
-/
lemma Finset.sup_mul₀ (s : Finset ι) (f : ι -> R) (a : R) :
    s.sup f * a = s.sup (f · * a) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert _ _ _ IH => simp only [sup_insert, max_mul, ← IH]

end
