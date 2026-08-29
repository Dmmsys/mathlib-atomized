/-
Copyright (c) 2024 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Data.Nat.DvdSequence
public import Mathlib.Data.Nat.EvenOddRec
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Data.Int.ModEq

/-!
# Elliptic divisibility sequences

This file defines the predicates for a sequence to be an elliptic net or an elliptic divisibility
sequence, as well as the canonical example of a normalised elliptic divisibility sequence.

## Mathematical background

Let `R` be a commutative ring, and let `W` be a sequence of elements in `R` indexed by `ℤ`. The
*elliptic relator* `ER(p, q, r, s) ∈ R` associated to `W` is given for all `p, q, r, s ∈ ℤ` by
`ER(p, q, r, s) := W(p+q+s)W(p-q)W(r+s)W(r) - W(p+r+s)W(p-r)W(q+s)W(q) + W(q+r+s)W(q-r)W(p+s)W(p)`.
Call `W` an *elliptic net* if it satisfies the *elliptic relation* `ER(p, q, r, s) = 0` for all
`p, q, r, s ∈ ℤ`. By a change of variables, `ER` is related to the symmetric relation `ERₐ` (see
`IsEllipticNet.rel_eq` and `IsEllipticNet.atomRel_eq`), where `ERₐ(a, b, c, d) ∈ R` is given for all
`a, b, c, d ∈ ℤ` by `ERₐ(a, b, c, d) := Wₐ(a, b)Wₐ(c, d) - Wₐ(a, c)Wₐ(b, d) + Wₐ(a, d)Wₐ(b, c)`
defined in terms of *elliptic atoms* `Wₐ(a, b) := W((a + b) / 2)W((a - b) / 2)`.

As a special case, `W` is an *elliptic sequence* if it satisfies `ER(p, q, r, 0) = 0` for all
`p, q, r ∈ ℤ`. It is a *divisibility sequence* if it satisfies `W(k) ∣ W(n * k)` for all `k, n ∈ ℤ`,
and an *elliptic divisibility sequence* (EDS) if it is a divisibility sequence that is elliptic. If
`W` is an EDS, then `x • W` is also an EDS for any `x ∈ R`. It turns out that any EDS `W` can be
normalised such that `W(1) = 1`, in which case it can be characterised completely by

* the *even relations* `ER(m + 1, m - 1, 1, 0) = 0` for all `m ∈ ℤ`, or in other words that
  `W(2m)W(2) = W(m - 1)²W(m)W(m + 2) - W(m - 2)W(m)W(m + 1)²` for all `m ∈ ℤ`, and
* the *odd relations* `ER(m + 1, m, 1, 0) = 0` for all `m ∈ ℤ`, or in other words that
  `W(2m + 1) = W(m + 2)W(m)³ - W(m - 1)W(m + 1)³` for all `m ∈ ℤ`,

with initial values `W(0) = 0`, `W(1) = 1`, `W(2) = b`, `W(3) = c`, and `W(4) = d * b` for some
`b, c, d ∈ R`. This will be called the *canonical example of a normalised EDS* in this file.

Some examples of EDSs include
* the identity sequence,
* certain terms of Lucas sequences, and
* division polynomials of elliptic curves.

## Main definitions

* `IsEllipticNet.atom`: the elliptic atom `Wₐ(a, b)` indexed by `ℤ`.
* `IsEllipticNet.atomRel`: the elliptic relator `ERₐ(a, b, c, d)` indexed by `ℤ`.
* `IsEllipticNet.rel`: the elliptic relator `ER(p, q, r, s)` indexed by `ℤ`.
* `IsEllipticNet`: a sequence indexed by `ℤ` is an elliptic net.
* `IsEllipticSequence`: a sequence indexed by `ℤ` is an elliptic sequence.
* `IsEllipticDvdSequence`: a sequence indexed by `ℤ` is an EDS.
* `preNormEDS'`: the auxiliary sequence for a normalised EDS indexed by `ℕ`.
* `preNormEDS`: the auxiliary sequence for a normalised EDS indexed by `ℤ`.
* `complEDS₂`: the 2-complement sequence for a normalised EDS indexed by `ℕ`.
* `normEDS`: the canonical example of a normalised EDS indexed by `ℤ`.
* `complEDS'`: the complement sequence for a normalised EDS indexed by `ℕ`.
* `complEDS`: the complement sequence for a normalised EDS indexed by `ℤ`.

## Main statements

* TODO: prove that `normEDS` satisfies `IsEllipticDvdSequence`.
* TODO: prove that a sequence satisfying `IsEllipticDvdSequence` can be normalised to a `normEDS`.

## Implementation notes

The elliptic relator is identical to the elliptic net recurrence defined by Stange, except that the
final term in the latter is negated. This unifies the definitions of Stange's elliptic nets and
Ward's elliptic sequences without requiring the sequence to be an odd function.

The normalised EDS `normEDS b c d n` is defined in terms of the auxiliary sequence
`preNormEDS (b ^ 4) c d n`, which are equal when `n` is odd, and which differ by a factor of `b`
when `n` is even. This coincides with the definition in the references since both agree for
`normEDS b c d 2` and for `normEDS b c d 4`, and the correct factors of `b` are removed in
`normEDS b c d (2 * (m + 2) + 1)` and in `normEDS b c d (2 * (m + 3))`.

One reason is to avoid the necessity for ring division by `b` in the inductive definition of
`normEDS b c d (2 * (m + 3))`. The idea is that it can be shown that `normEDS b c d (2 * (m + 3))`
always contains a factor of `b`, so it is possible to remove a factor of `b` *a posteriori*, but
stating this lemma requires first defining `normEDS b c d (2 * (m + 3))`, which requires having this
factor of `b` *a priori*. Another reason is to allow the definition of univariate `n`-division
polynomials of elliptic curves, omitting a factor of the bivariate `2`-division polynomial.

## References

* K Stange, *Elliptic Nets and Elliptic Curves*
* M Ward, *Memoir on Elliptic Divisibility Sequences*

## Tags

elliptic net, elliptic divisibility sequence
-/

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S] (W : Int -> R) {F : Type*} [FunLike F R S]
  [RingHomClass F R S] (f : F)

namespace IsEllipticNet

/--
Definition of `atom` / `atom` 的定义

English:
definition atom
  signature: (a b : Int)
  body: W ((a + b).tdiv 2) * W ((a - b).tdiv 2)

@[simp]

中文:
定义 atom
  签名: (a b : 整数)
  定义体: W ((a + b).tdiv 2) * W ((a - b).tdiv 2)

@[simp]
-/
def atom (a b : Int) : R :=
  W ((a + b).tdiv 2) * W ((a - b).tdiv 2)

@[simp]
/--
lemma `atom_same` / 引理 `atom_same`

English:
lemma atom_same
  given: (a : Int)
  statement: atom W a a = W a * W 0
  proof: by
  rw [atom]; rw [← two_mul]; rw [Int.mul_tdiv_cancel_left _ two_ne_zero]; rw [sub_self]; rw [Int.zero_tdiv]

中文:
引理 atom_same
  条件: (a : 整数)
  结论: atom W a a = W a * W 0
  证明: by
  rw [atom]; rw [← two_mul]; rw [Int.mul_tdiv_cancel_left _ two_ne_zero]; rw [sub_self]; rw [Int.zero_tdiv]

Depends on / 依赖: Int.mul_tdiv_cancel_left, Int.zero_tdiv, mul_tdiv_cancel_left, sub_self, two_mul, two_ne_zero, zero_tdiv
-/
lemma atom_same (a : Int) : atom W a a = W a * W 0 := by
  rw [atom]; rw [← two_mul]; rw [Int.mul_tdiv_cancel_left _ two_ne_zero]; rw [sub_self]; rw [Int.zero_tdiv]

variable {W} in
@[simp]
/--
lemma `neg_atom` / 引理 `neg_atom`

English:
lemma neg_atom
  given: (odd : W.Odd) (a b : Int)
  statement: -atom W a b = atom W b a
  proof: by
  rw [atom]; rw [atom]; rw [add_comm]; rw [← neg_sub a]; rw [Int.neg_tdiv]; rw [odd]; rw [mul_neg]

中文:
引理 neg_atom
  条件: (odd : W.Odd) (a b : 整数)
  结论: -atom W a b = atom W b a
  证明: by
  rw [atom]; rw [atom]; rw [add_comm]; rw [← neg_sub a]; rw [Int.neg_tdiv]; rw [odd]; rw [mul_neg]

Depends on / 依赖: Int.neg_tdiv, add_comm, mul_neg, neg_sub, neg_tdiv
-/
lemma neg_atom (odd : W.Odd) (a b : Int) : -atom W a b = atom W b a := by
  rw [atom]; rw [atom]; rw [add_comm]; rw [← neg_sub a]; rw [Int.neg_tdiv]; rw [odd]; rw [mul_neg]

variable {W} in
/--
lemma `atom_mul_atom` / 引理 `atom_mul_atom`

English:
lemma atom_mul_atom
  given: (odd : W.Odd) (a b c d : Int)
  proof: by
  rw [← neg_atom odd a b]; rw [← neg_atom odd c d]; rw [neg_mul_neg]

中文:
引理 atom_mul_atom
  条件: (odd : W.Odd) (a b c d : 整数)
  证明: by
  rw [← neg_atom odd a b]; rw [← neg_atom odd c d]; rw [neg_mul_neg]

Depends on / 依赖: neg_atom, neg_mul_neg
-/
lemma atom_mul_atom (odd : W.Odd) (a b c d : Int) :
    atom W a b * atom W c d = atom W b a * atom W d c := by
  rw [← neg_atom odd a b]; rw [← neg_atom odd c d]; rw [neg_mul_neg]

variable {W} in
@[simp]
/--
lemma `atom_neg_left` / 引理 `atom_neg_left`

English:
lemma atom_neg_left
  given: (odd : W.Odd) (a b : Int)
  statement: atom W (-a) b = atom W a b
  proof: by
  rw [atom]; rw [atom]; rw [neg_add_eq_sub]; rw [← neg_sub a]; rw [← neg_add']; rw [Int.neg_tdiv]; rw [odd]; rw [Int.neg_tdiv]; rw [odd]; rw [neg_mul_neg]; rw [mul_comm]

@[simp]

中文:
引理 atom_neg_left
  条件: (odd : W.Odd) (a b : 整数)
  结论: atom W (-a) b = atom W a b
  证明: by
  rw [atom]; rw [atom]; rw [neg_add_eq_sub]; rw [← neg_sub a]; rw [← neg_add']; rw [Int.neg_tdiv]; rw [odd]; rw [Int.neg_tdiv]; rw [odd]; rw [neg_mul_neg]; rw [mul_comm]

@[simp]

Depends on / 依赖: Int.neg_tdiv, mul_comm, neg_add, neg_add_eq_sub, neg_mul_neg, neg_sub, neg_tdiv
-/
lemma atom_neg_left (odd : W.Odd) (a b : Int) : atom W (-a) b = atom W a b := by
  rw [atom]; rw [atom]; rw [neg_add_eq_sub]; rw [← neg_sub a]; rw [← neg_add']; rw [Int.neg_tdiv]; rw [odd]; rw [Int.neg_tdiv]; rw [odd]; rw [neg_mul_neg]; rw [mul_comm]

@[simp]
/--
lemma `atom_neg_right` / 引理 `atom_neg_right`

English:
lemma atom_neg_right
  given: (a b : Int)
  statement: atom W a (-b) = atom W a b
  proof: by
  simp_rw [atom, ← sub_eq_add_neg, sub_neg_eq_add, mul_comm]

中文:
引理 atom_neg_right
  条件: (a b : 整数)
  结论: atom W a (-b) = atom W a b
  证明: by
  simp_rw [atom, ← sub_eq_add_neg, sub_neg_eq_add, mul_comm]

Depends on / 依赖: mul_comm, simp_rw, sub_eq_add_neg, sub_neg_eq_add
-/
lemma atom_neg_right (a b : Int) : atom W a (-b) = atom W a b := by
  simp_rw [atom, ← sub_eq_add_neg, sub_neg_eq_add, mul_comm]

variable {W} in
@[simp]
/--
lemma `atom_abs_left` / 引理 `atom_abs_left`

English:
lemma atom_abs_left
  given: (odd : W.Odd) (a b : Int)
  statement: atom W |a| b = atom W a b
  proof: by
  rcases abs_choice a with h | h <;> simp only [h, atom_neg_left odd]

@[simp]

中文:
引理 atom_abs_left
  条件: (odd : W.Odd) (a b : 整数)
  结论: atom W |a| b = atom W a b
  证明: by
  rcases abs_choice a with h | h <;> simp only [h, atom_neg_left odd]

@[simp]

Depends on / 依赖: abs_choice, atom_neg_left
-/
lemma atom_abs_left (odd : W.Odd) (a b : Int) : atom W |a| b = atom W a b := by
  rcases abs_choice a with h | h <;> simp only [h, atom_neg_left odd]

@[simp]
/--
lemma `atom_abs_right` / 引理 `atom_abs_right`

English:
lemma atom_abs_right
  given: (a b : Int)
  statement: atom W a |b| = atom W a b
  proof: by
  rcases abs_choice b with h | h <;> simp only [h, atom_neg_right]

中文:
引理 atom_abs_right
  条件: (a b : 整数)
  结论: atom W a |b| = atom W a b
  证明: by
  rcases abs_choice b with h | h <;> simp only [h, atom_neg_right]

Depends on / 依赖: abs_choice, atom_neg_right
-/
lemma atom_abs_right (a b : Int) : atom W a |b| = atom W a b := by
  rcases abs_choice b with h | h <;> simp only [h, atom_neg_right]

/--
lemma `atom_even` / 引理 `atom_even`

English:
lemma atom_even
  given: (a b : Int)
  statement: atom W (2 * a) (2 * b) = W (a + b) * W (a - b)
  proof: by
  simp_rw [atom, ← mul_add, ← mul_sub, Int.mul_tdiv_cancel_left _ two_ne_zero]

中文:
引理 atom_even
  条件: (a b : 整数)
  结论: atom W (2 * a) (2 * b) = W (a + b) * W (a - b)
  证明: by
  simp_rw [atom, ← mul_add, ← mul_sub, Int.mul_tdiv_cancel_left _ two_ne_zero]

Depends on / 依赖: Int.mul_tdiv_cancel_left, mul_add, mul_sub, mul_tdiv_cancel_left, simp_rw, two_ne_zero
-/
lemma atom_even (a b : Int) : atom W (2 * a) (2 * b) = W (a + b) * W (a - b) := by
  simp_rw [atom, ← mul_add, ← mul_sub, Int.mul_tdiv_cancel_left _ two_ne_zero]

/--
lemma `atom_odd` / 引理 `atom_odd`

English:
lemma atom_odd
  given: (a b : Int)
  statement: atom W (2 * a + 1) (2 * b + 1) = W (a + b + 1) * W (a - b)
  proof: by
  simp_rw [atom, add_add_add_comm _ (1 : Int), ← two_mul, ← mul_add, add_sub_add_comm, sub_self,
    add_zero, ← mul_sub, Int.mul_tdiv_cancel_left _ two_ne_zero]

中文:
引理 atom_odd
  条件: (a b : 整数)
  结论: atom W (2 * a + 1) (2 * b + 1) = W (a + b + 1) * W (a - b)
  证明: by
  simp_rw [atom, add_add_add_comm _ (1 : Int), ← two_mul, ← mul_add, add_sub_add_comm, sub_self,
    add_zero, ← mul_sub, Int.mul_tdiv_cancel_left _ two_ne_zero]

Depends on / 依赖: Int.mul_tdiv_cancel_left, add_add_add_comm, add_sub_add_comm, add_zero, mul_add, mul_sub, mul_tdiv_cancel_left, simp_rw, sub_self, two_mul, two_ne_zero
-/
lemma atom_odd (a b : Int) : atom W (2 * a + 1) (2 * b + 1) = W (a + b + 1) * W (a - b) := by
  simp_rw [atom, add_add_add_comm _ (1 : Int), ← two_mul, ← mul_add, add_sub_add_comm, sub_self,
    add_zero, ← mul_sub, Int.mul_tdiv_cancel_left _ two_ne_zero]

/--
lemma `map_atom` / 引理 `map_atom`

English:
lemma map_atom
  given: (a b : Int)
  statement: f (atom W a b) = atom (f ∘ W) a b
  proof: by
  simp_rw [atom, map_mul, Function.comp]

中文:
引理 map_atom
  条件: (a b : 整数)
  结论: f (atom W a b) = atom (f ∘ W) a b
  证明: by
  simp_rw [atom, map_mul, Function.comp]

Depends on / 依赖: Function, Function.comp, map_mul, simp_rw
-/
lemma map_atom (a b : Int) : f (atom W a b) = atom (f ∘ W) a b := by
  simp_rw [atom, map_mul, Function.comp]

/--
Definition of `atomRel` / `atomRel` 的定义

English:
definition atomRel
  signature: (a b c d : Int)
  body: atom W a b * atom W c d - atom W a c * atom W b d + atom W a d * atom W b c

@[simp]

中文:
定义 atomRel
  签名: (a b c d : 整数)
  定义体: atom W a b * atom W c d - atom W a c * atom W b d + atom W a d * atom W b c

@[simp]
-/
def atomRel (a b c d : Int) : R :=
  atom W a b * atom W c d - atom W a c * atom W b d + atom W a d * atom W b c

@[simp]
/--
lemma `atomRel_same₁₂` / 引理 `atomRel_same₁₂`

English:
lemma atomRel_same₁₂
  given: (a b c : Int)
  statement: atomRel W a a b c = W a * W 0 * atom W b c
  proof: by
  simp_rw [atomRel, atom_same, mul_comm <| atom W a b, sub_add_cancel]

中文:
引理 atomRel_same₁₂
  条件: (a b c : 整数)
  结论: atomRel W a a b c = W a * W 0 * atom W b c
  证明: by
  simp_rw [atomRel, atom_same, mul_comm <| atom W a b, sub_add_cancel]

Depends on / 依赖: atomRel, atom_same, mul_comm, simp_rw, sub_add_cancel
-/
lemma atomRel_same₁₂ (a b c : Int) : atomRel W a a b c = W a * W 0 * atom W b c := by
  simp_rw [atomRel, atom_same, mul_comm <| atom W a b, sub_add_cancel]

variable {W} in
@[simp]
/--
lemma `atomRel_same₁₃` / 引理 `atomRel_same₁₃`

English:
lemma atomRel_same₁₃
  given: (odd : W.Odd) (a b c : Int)
  statement: atomRel W a b a c = W a * W 0 * atom W c b
  proof: by
  linear_combination (norm := (simp_rw [atomRel, atom_same]; ring1))
    W a * W 0 * neg_atom odd c b - atom W a c * neg_atom odd a b

中文:
引理 atomRel_same₁₃
  条件: (odd : W.Odd) (a b c : 整数)
  结论: atomRel W a b a c = W a * W 0 * atom W c b
  证明: by
  linear_combination (norm := (simp_rw [atomRel, atom_same]; ring1))
    W a * W 0 * neg_atom odd c b - atom W a c * neg_atom odd a b

Depends on / 依赖: atomRel, atom_same, linear_combination, neg_atom, simp_rw
-/
lemma atomRel_same₁₃ (odd : W.Odd) (a b c : Int) : atomRel W a b a c = W a * W 0 * atom W c b := by
  linear_combination (norm := (simp_rw [atomRel, atom_same]; ring1))
    W a * W 0 * neg_atom odd c b - atom W a c * neg_atom odd a b

variable {W} in
@[simp]
/--
lemma `atomRel_same₁₄` / 引理 `atomRel_same₁₄`

English:
lemma atomRel_same₁₄
  given: (odd : W.Odd) (a b c : Int)
  statement: atomRel W a b c a = W a * W 0 * atom W b c
  proof: by
  simp_rw [atomRel, atom_mul_atom odd a b, mul_comm <| atom W b a, sub_self, zero_add, atom_same]

@[simp]

中文:
引理 atomRel_same₁₄
  条件: (odd : W.Odd) (a b c : 整数)
  结论: atomRel W a b c a = W a * W 0 * atom W b c
  证明: by
  simp_rw [atomRel, atom_mul_atom odd a b, mul_comm <| atom W b a, sub_self, zero_add, atom_same]

@[simp]

Depends on / 依赖: atomRel, atom_mul_atom, atom_same, mul_comm, simp_rw, sub_self, zero_add
-/
lemma atomRel_same₁₄ (odd : W.Odd) (a b c : Int) : atomRel W a b c a = W a * W 0 * atom W b c := by
  simp_rw [atomRel, atom_mul_atom odd a b, mul_comm <| atom W b a, sub_self, zero_add, atom_same]

@[simp]
/--
lemma `atomRel_same₂₃` / 引理 `atomRel_same₂₃`

English:
lemma atomRel_same₂₃
  given: (a b c : Int)
  statement: atomRel W a b b c = W b * W 0 * atom W a c
  proof: by
  simp_rw [atomRel, atom_same, sub_self, zero_add, mul_comm]

中文:
引理 atomRel_same₂₃
  条件: (a b c : 整数)
  结论: atomRel W a b b c = W b * W 0 * atom W a c
  证明: by
  simp_rw [atomRel, atom_same, sub_self, zero_add, mul_comm]

Depends on / 依赖: atomRel, atom_same, mul_comm, simp_rw, sub_self, zero_add
-/
lemma atomRel_same₂₃ (a b c : Int) : atomRel W a b b c = W b * W 0 * atom W a c := by
  simp_rw [atomRel, atom_same, sub_self, zero_add, mul_comm]

variable {W} in
@[simp]
/--
lemma `atomRel_same₂₄` / 引理 `atomRel_same₂₄`

English:
lemma atomRel_same₂₄
  given: (odd : W.Odd) (a b c : Int)
  statement: atomRel W a b c b = W b * W 0 * atom W c a
  proof: by
  linear_combination (norm := (simp_rw [atomRel, atom_same]; ring1))
    W b * W 0 * neg_atom odd a c - atom W a b * neg_atom odd b c

@[simp]

中文:
引理 atomRel_same₂₄
  条件: (odd : W.Odd) (a b c : 整数)
  结论: atomRel W a b c b = W b * W 0 * atom W c a
  证明: by
  linear_combination (norm := (simp_rw [atomRel, atom_same]; ring1))
    W b * W 0 * neg_atom odd a c - atom W a b * neg_atom odd b c

@[simp]

Depends on / 依赖: atomRel, atom_same, linear_combination, neg_atom, simp_rw
-/
lemma atomRel_same₂₄ (odd : W.Odd) (a b c : Int) : atomRel W a b c b = W b * W 0 * atom W c a := by
  linear_combination (norm := (simp_rw [atomRel, atom_same]; ring1))
    W b * W 0 * neg_atom odd a c - atom W a b * neg_atom odd b c

@[simp]
/--
lemma `atomRel_same₃₄` / 引理 `atomRel_same₃₄`

English:
lemma atomRel_same₃₄
  given: (a b c : Int)
  statement: atomRel W a b c c = W c * W 0 * atom W a b
  proof: by
  simp_rw [atomRel, atom_same, mul_comm, sub_add_cancel]

中文:
引理 atomRel_same₃₄
  条件: (a b c : 整数)
  结论: atomRel W a b c c = W c * W 0 * atom W a b
  证明: by
  simp_rw [atomRel, atom_same, mul_comm, sub_add_cancel]

Depends on / 依赖: atomRel, atom_same, mul_comm, simp_rw, sub_add_cancel
-/
lemma atomRel_same₃₄ (a b c : Int) : atomRel W a b c c = W c * W 0 * atom W a b := by
  simp_rw [atomRel, atom_same, mul_comm, sub_add_cancel]

variable {W} in
@[simp]
/--
lemma `atomRel_neg₁` / 引理 `atomRel_neg₁`

English:
lemma atomRel_neg₁
  given: (odd : W.Odd) (a b c d : Int)
  statement: atomRel W (-a) b c d = atomRel W a b c d
  proof: by
  simp_rw [atomRel, atom_neg_left odd]

中文:
引理 atomRel_neg₁
  条件: (odd : W.Odd) (a b c d : 整数)
  结论: atomRel W (-a) b c d = atomRel W a b c d
  证明: by
  simp_rw [atomRel, atom_neg_left odd]

Depends on / 依赖: atomRel, atom_neg_left, simp_rw
-/
lemma atomRel_neg₁ (odd : W.Odd) (a b c d : Int) : atomRel W (-a) b c d = atomRel W a b c d := by
  simp_rw [atomRel, atom_neg_left odd]

variable {W} in
@[simp]
/--
lemma `atomRel_neg₂` / 引理 `atomRel_neg₂`

English:
lemma atomRel_neg₂
  given: (odd : W.Odd) (a b c d : Int)
  statement: atomRel W a (-b) c d = atomRel W a b c d
  proof: by
  simp_rw [atomRel, atom_neg_left odd, atom_neg_right]

中文:
引理 atomRel_neg₂
  条件: (odd : W.Odd) (a b c d : 整数)
  结论: atomRel W a (-b) c d = atomRel W a b c d
  证明: by
  simp_rw [atomRel, atom_neg_left odd, atom_neg_right]

Depends on / 依赖: atomRel, atom_neg_left, atom_neg_right, simp_rw
-/
lemma atomRel_neg₂ (odd : W.Odd) (a b c d : Int) : atomRel W a (-b) c d = atomRel W a b c d := by
  simp_rw [atomRel, atom_neg_left odd, atom_neg_right]

variable {W} in
@[simp]
/--
lemma `atomRel_neg₃` / 引理 `atomRel_neg₃`

English:
lemma atomRel_neg₃
  given: (odd : W.Odd) (a b c d : Int)
  statement: atomRel W a b (-c) d = atomRel W a b c d
  proof: by
  simp_rw [atomRel, atom_neg_left odd, atom_neg_right]

@[simp]

中文:
引理 atomRel_neg₃
  条件: (odd : W.Odd) (a b c d : 整数)
  结论: atomRel W a b (-c) d = atomRel W a b c d
  证明: by
  simp_rw [atomRel, atom_neg_left odd, atom_neg_right]

@[simp]

Depends on / 依赖: atomRel, atom_neg_left, atom_neg_right, simp_rw
-/
lemma atomRel_neg₃ (odd : W.Odd) (a b c d : Int) : atomRel W a b (-c) d = atomRel W a b c d := by
  simp_rw [atomRel, atom_neg_left odd, atom_neg_right]

@[simp]
/--
lemma `atomRel_neg₄` / 引理 `atomRel_neg₄`

English:
lemma atomRel_neg₄
  given: (a b c d : Int)
  statement: atomRel W a b c (-d) = atomRel W a b c d
  proof: by
  simp_rw [atomRel, atom_neg_right]

中文:
引理 atomRel_neg₄
  条件: (a b c d : 整数)
  结论: atomRel W a b c (-d) = atomRel W a b c d
  证明: by
  simp_rw [atomRel, atom_neg_right]

Depends on / 依赖: atomRel, atom_neg_right, simp_rw
-/
lemma atomRel_neg₄ (a b c d : Int) : atomRel W a b c (-d) = atomRel W a b c d := by
  simp_rw [atomRel, atom_neg_right]

variable {W} in
@[simp]
/--
lemma `atomRel_abs₁` / 引理 `atomRel_abs₁`

English:
lemma atomRel_abs₁
  given: (odd : W.Odd) (a b c d : Int)
  statement: atomRel W |a| b c d = atomRel W a b c d
  proof: by
  simp_rw [atomRel, atom_abs_left odd]

中文:
引理 atomRel_abs₁
  条件: (odd : W.Odd) (a b c d : 整数)
  结论: atomRel W |a| b c d = atomRel W a b c d
  证明: by
  simp_rw [atomRel, atom_abs_left odd]

Depends on / 依赖: CompleteLattice, atomRel, atom_abs_left, sSupHomClass, sSupHomClass.toSupBotHomClass, simp_rw, toSupBotHomClass
-/
lemma atomRel_abs₁ (odd : W.Odd) (a b c d : Int) : atomRel W |a| b c d = atomRel W a b c d := by
  simp_rw [atomRel, atom_abs_left odd]

variable {W} in
@[simp]
/--
lemma `atomRel_abs₂` / 引理 `atomRel_abs₂`

English:
lemma atomRel_abs₂
  given: (odd : W.Odd) (a b c d : Int)
  statement: atomRel W a |b| c d = atomRel W a b c d
  proof: by
  simp_rw [atomRel, atom_abs_left odd, atom_abs_right]

中文:
引理 atomRel_abs₂
  条件: (odd : W.Odd) (a b c d : 整数)
  结论: atomRel W a |b| c d = atomRel W a b c d
  证明: by
  simp_rw [atomRel, atom_abs_left odd, atom_abs_right]

Depends on / 依赖: CompleteLattice, FrameHomClass, FrameHomClass.tosSupHomClass, atomRel, atom_abs_left, atom_abs_right, simp_rw, tosSupHomClass
-/
lemma atomRel_abs₂ (odd : W.Odd) (a b c d : Int) : atomRel W a |b| c d = atomRel W a b c d := by
  simp_rw [atomRel, atom_abs_left odd, atom_abs_right]

variable {W} in
@[simp]
/--
lemma `atomRel_abs₃` / 引理 `atomRel_abs₃`

English:
lemma atomRel_abs₃
  given: (odd : W.Odd) (a b c d : Int)
  statement: atomRel W a b |c| d = atomRel W a b c d
  proof: by
  simp_rw [atomRel, atom_abs_left odd, atom_abs_right]

@[simp]

中文:
引理 atomRel_abs₃
  条件: (odd : W.Odd) (a b c d : 整数)
  结论: atomRel W a b |c| d = atomRel W a b c d
  证明: by
  simp_rw [atomRel, atom_abs_left odd, atom_abs_right]

@[simp]

Depends on / 依赖: CompleteLattice, FrameHomClass, FrameHomClass.toBoundedLatticeHomClass, atomRel, atom_abs_left, atom_abs_right, simp_rw, toBoundedLatticeHomClass
-/
lemma atomRel_abs₃ (odd : W.Odd) (a b c d : Int) : atomRel W a b |c| d = atomRel W a b c d := by
  simp_rw [atomRel, atom_abs_left odd, atom_abs_right]

@[simp]
/--
lemma `atomRel_abs₄` / 引理 `atomRel_abs₄`

English:
lemma atomRel_abs₄
  given: (a b c d : Int)
  statement: atomRel W a b c |d| = atomRel W a b c d
  proof: by
  simp_rw [atomRel, atom_abs_right]

中文:
引理 atomRel_abs₄
  条件: (a b c d : 整数)
  结论: atomRel W a b c |d| = atomRel W a b c d
  证明: by
  simp_rw [atomRel, atom_abs_right]

Depends on / 依赖: CompleteLattice, CompleteLatticeHomClass, CompleteLatticeHomClass.toFrameHomClass, atomRel, atom_abs_right, simp_rw, toFrameHomClass
-/
lemma atomRel_abs₄ (a b c d : Int) : atomRel W a b c |d| = atomRel W a b c d := by
  simp_rw [atomRel, atom_abs_right]

/--
lemma `atomRel_avg_sub` / 引理 `atomRel_avg_sub`

English:
lemma atomRel_avg_sub
  given: {a b c d : Int} (parity : d % 2 = a % 2 ∧ d % 2 = b % 2 ∧ d % 2 = c % 2)
  proof: by
  simp_rw [add_assoc <| a + b, atomRel, atom, sub_add_sub_comm, ← two_mul]
  repeat rw [Int.mul_ediv_cancel'] <;> grind

中文:
引理 atomRel_avg_sub
  条件: {a b c d : 整数} (parity : d % 2 = a % 2 ∧ d % 2 = b % 2 ∧ d % 2 = c % 2)
  证明: by
  simp_rw [add_assoc <| a + b, atomRel, atom, sub_add_sub_comm, ← two_mul]
  repeat rw [Int.mul_ediv_cancel'] <;> grind

Depends on / 依赖: CompleteLattice, CompleteLatticeHomClass, CompleteLatticeHomClass.toBoundedLatticeHomClass, Int.mul_ediv_cancel, add_assoc, atomRel, mul_ediv_cancel, repeat, simp_rw, sub_add_sub_comm, toBoundedLatticeHomClass, two_mul
-/
lemma atomRel_avg_sub {a b c d : Int} (parity : d % 2 = a % 2 ∧ d % 2 = b % 2 ∧ d % 2 = c % 2) :
    atomRel W ((a + b + c + d) / 2 - d) ((a + b + c + d) / 2 - c) ((a + b + c + d) / 2 - b)
      ((a + b + c + d) / 2 - a) = atomRel W a b c d := by
  simp_rw [add_assoc <| a + b, atomRel, atom, sub_add_sub_comm, ← two_mul]
  repeat rw [Int.mul_ediv_cancel'] <;> grind

/--
lemma `map_atomRel` / 引理 `map_atomRel`

English:
lemma map_atomRel
  given: (a b c d : Int)
  statement: f (atomRel W a b c d) = atomRel (f ∘ W) a b c d
  proof: by
  simp_rw [atomRel, map_add, map_sub, map_mul, map_atom]

中文:
引理 map_atomRel
  条件: (a b c d : 整数)
  结论: f (atomRel W a b c d) = atomRel (f ∘ W) a b c d
  证明: by
  simp_rw [atomRel, map_add, map_sub, map_mul, map_atom]

Depends on / 依赖: CompleteLattice, OrderIsoClass, OrderIsoClass.tosSupHomClass, atomRel, map_add, map_atom, map_mul, map_sub, simp_rw, tosSupHomClass
-/
lemma map_atomRel (a b c d : Int) : f (atomRel W a b c d) = atomRel (f ∘ W) a b c d := by
  simp_rw [atomRel, map_add, map_sub, map_mul, map_atom]

/--
Definition of `rel` / `rel` 的定义

English:
definition rel
  signature: (p q r s : Int)
  body: W (p + q + s) * W (p - q) * W (r + s) * W r - W (p + r + s) * W (p - r) * W (q + s) * W q +
    W (q + r + s) * W (q - r) * W (p + s) * W p

中文:
定义 rel
  签名: (p q r s : 整数)
  定义体: W (p + q + s) * W (p - q) * W (r + s) * W r - W (p + r + s) * W (p - r) * W (q + s) * W q +
    W (q + r + s) * W (q - r) * W (p + s) * W p

Depends on / 依赖: CompleteLattice, OrderIsoClass, OrderIsoClass.toCompleteLatticeHomClass, toCompleteLatticeHomClass
-/
def rel (p q r s : Int) : R :=
  W (p + q + s) * W (p - q) * W (r + s) * W r - W (p + r + s) * W (p - r) * W (q + s) * W q +
    W (q + r + s) * W (q - r) * W (p + s) * W p

/--
lemma `rel_eq` / 引理 `rel_eq`

English:
lemma rel_eq
  given: (p q r s : Int)
  statement: rel W p q r s = atomRel W (2 * p + s) (2 * q + s) (2 * r + s) s
  proof: by
  simp_rw [rel, atomRel, atom, add_add_add_comm _ s, add_assoc _ s, ← two_mul, ← mul_add,
    add_sub_add_comm, add_sub_assoc, sub_self, add_zero, ← mul_sub,
Int.mul_tdiv_cancel_left _ two_ne_zero, mul_comm _ * W p, mul_assoc]

中文:
引理 rel_eq
  条件: (p q r s : 整数)
  结论: rel W p q r s = atomRel W (2 * p + s) (2 * q + s) (2 * r + s) s
  证明: by
  simp_rw [rel, atomRel, atom, add_add_add_comm _ s, add_assoc _ s, ← two_mul, ← mul_add,
    add_sub_add_comm, add_sub_assoc, sub_self, add_zero, ← mul_sub,
Int.mul_tdiv_cancel_left _ two_ne_zero, mul_comm _ * W p, mul_assoc]

Depends on / 依赖: Int.mul_tdiv_cancel_left, add_add_add_comm, add_assoc, add_sub_add_comm, add_sub_assoc, add_zero, atomRel, mul_add, mul_assoc, mul_comm, mul_sub, mul_tdiv_cancel_left, simp_rw, sub_self, two_mul, two_ne_zero
-/
lemma rel_eq (p q r s : Int) : rel W p q r s = atomRel W (2 * p + s) (2 * q + s) (2 * r + s) s := by
  simp_rw [rel, atomRel, atom, add_add_add_comm _ s, add_assoc _ s, ← two_mul, ← mul_add,
    add_sub_add_comm, add_sub_assoc, sub_self, add_zero, ← mul_sub,
Int.mul_tdiv_cancel_left _ two_ne_zero, mul_comm _ * W p, mul_assoc]

/--
lemma `atomRel_two_mul` / 引理 `atomRel_two_mul`

English:
lemma atomRel_two_mul
  given: (a b c d : Int)
  proof: by
  simp_rw [rel_eq, mul_sub, sub_add_cancel]

中文:
引理 atomRel_two_mul
  条件: (a b c d : 整数)
  证明: by
  simp_rw [rel_eq, mul_sub, sub_add_cancel]

Depends on / 依赖: mul_sub, rel_eq, simp_rw, sub_add_cancel
-/
lemma atomRel_two_mul (a b c d : Int) :
    atomRel W (2 * a) (2 * b) (2 * c) (2 * d) = rel W (a - d) (b - d) (c - d) (2 * d) := by
  simp_rw [rel_eq, mul_sub, sub_add_cancel]

/--
lemma `atomRel_eq` / 引理 `atomRel_eq`

English:
lemma atomRel_eq
  given: {a b c d : Int} (parity : d % 2 = a % 2 ∧ d % 2 = b % 2 ∧ d % 2 = c % 2)
  proof: by
  simp only [rel_eq, Int.mul_ediv_cancel', Int.ModEq.dvd parity.1, Int.ModEq.dvd parity.2.1,
    Int.ModEq.dvd parity.2.2, sub_add_cancel]

中文:
引理 atomRel_eq
  条件: {a b c d : 整数} (parity : d % 2 = a % 2 ∧ d % 2 = b % 2 ∧ d % 2 = c % 2)
  证明: by
  simp only [rel_eq, Int.mul_ediv_cancel', Int.ModEq.dvd parity.1, Int.ModEq.dvd parity.2.1,
    Int.ModEq.dvd parity.2.2, sub_add_cancel]

Depends on / 依赖: Int.ModEq.dvd, Int.mul_ediv_cancel, mul_ediv_cancel, parity, rel_eq, sub_add_cancel
-/
lemma atomRel_eq {a b c d : Int} (parity : d % 2 = a % 2 ∧ d % 2 = b % 2 ∧ d % 2 = c % 2) :
    atomRel W a b c d = rel W ((a - d) / 2) ((b - d) / 2) ((c - d) / 2) d := by
  simp only [rel_eq, Int.mul_ediv_cancel', Int.ModEq.dvd parity.1, Int.ModEq.dvd parity.2.1,
    Int.ModEq.dvd parity.2.2, sub_add_cancel]

variable {W} in
@[simp]
/--
lemma `rel_neg` / 引理 `rel_neg`

English:
lemma rel_neg
  given: (odd : W.Odd) (p q r s : Int)
  statement: rel W (-p) (-q) (-r) (-s) = rel W p q r s
  proof: by
  simp_rw [rel_eq, mul_neg, ← neg_add, atomRel_neg₁ odd, atomRel_neg₂ odd, atomRel_neg₃ odd,
    atomRel_neg₄]

中文:
引理 rel_neg
  条件: (odd : W.Odd) (p q r s : 整数)
  结论: rel W (-p) (-q) (-r) (-s) = rel W p q r s
  证明: by
  simp_rw [rel_eq, mul_neg, ← neg_add, atomRel_neg₁ odd, atomRel_neg₂ odd, atomRel_neg₃ odd,
    atomRel_neg₄]

Depends on / 依赖: mul_neg, neg_add, rel_eq, simp_rw
-/
lemma rel_neg (odd : W.Odd) (p q r s : Int) : rel W (-p) (-q) (-r) (-s) = rel W p q r s := by
  simp_rw [rel_eq, mul_neg, ← neg_add, atomRel_neg₁ odd, atomRel_neg₂ odd, atomRel_neg₃ odd,
    atomRel_neg₄]

/--
lemma `rel_even` / 引理 `rel_even`

English:
lemma rel_even
  given: (m : Int)
  statement: rel W (m + 1) (m - 1) 1 0 = W (2 * m) * W 2 * W 1 ^ 2 -
  proof: by
  rw [rel]
  ring_nf

中文:
引理 rel_even
  条件: (m : 整数)
  结论: rel W (m + 1) (m - 1) 1 0 = W (2 * m) * W 2 * W 1 ^ 2 -
  证明: by
  rw [rel]
  ring_nf

Depends on / 依赖: ring_nf
-/
lemma rel_even (m : Int) : rel W (m + 1) (m - 1) 1 0 = W (2 * m) * W 2 * W 1 ^ 2 -
    W (m - 1) ^ 2 * W m * W (m + 2) + W (m - 2) * W m * W (m + 1) ^ 2 := by
  rw [rel]
  ring_nf

/--
lemma `rel_odd` / 引理 `rel_odd`

English:
lemma rel_odd
  given: (m : Int)
  statement: rel W (m + 1) m 1 0 =
  proof: by
  rw [rel]
  ring_nf

中文:
引理 rel_odd
  条件: (m : 整数)
  结论: rel W (m + 1) m 1 0 =
  证明: by
  rw [rel]
  ring_nf

Depends on / 依赖: ring_nf
-/
lemma rel_odd (m : Int) : rel W (m + 1) m 1 0 =
    W (2 * m + 1) * W 1 ^ 3 - W (m + 2) * W m ^ 3 + W (m - 1) * W (m + 1) ^ 3 := by
  rw [rel]
  ring_nf

/--
lemma `map_rel` / 引理 `map_rel`

English:
lemma map_rel
  given: (p q r s : Int)
  statement: f (rel W p q r s) = rel (f ∘ W) p q r s
  proof: by
  simp_rw [rel, map_add, map_sub, map_mul, Function.comp]

中文:
引理 map_rel
  条件: (p q r s : 整数)
  结论: f (rel W p q r s) = rel (f ∘ W) p q r s
  证明: by
  simp_rw [rel, map_add, map_sub, map_mul, Function.comp]

Depends on / 依赖: Function, Function.comp, map_add, map_mul, map_sub, simp_rw
-/
lemma map_rel (p q r s : Int) : f (rel W p q r s) = rel (f ∘ W) p q r s := by
  simp_rw [rel, map_add, map_sub, map_mul, Function.comp]

end IsEllipticNet

/--
Definition of `IsEllipticNet` / `IsEllipticNet` 的定义

English:
definition IsEllipticNet
  signature: : Prop
  body: forall p q r s : Int, IsEllipticNet.rel W p q r s = 0

中文:
定义 IsEllipticNet
  签名: : 命题
  定义体: forall p q r s : Int, IsEllipticNet.rel W p q r s = 0

Depends on / 依赖: IsEllipticNet, IsEllipticNet.rel
-/
def IsEllipticNet : Prop :=
  forall p q r s : Int, IsEllipticNet.rel W p q r s = 0

/--
Definition of `IsEllipticSequence` / `IsEllipticSequence` 的定义

English:
definition IsEllipticSequence
  signature: : Prop
  body: forall p q r : Int, IsEllipticNet.rel W p q r 0 = 0

@[deprecated (since := "2026-07-01")] alias IsEllSequence := IsEllipticSequence

中文:
定义 IsEllipticSequence
  签名: : 命题
  定义体: forall p q r : Int, IsEllipticNet.rel W p q r 0 = 0

@[deprecated (since := "2026-07-01")] alias IsEllSequence := IsEllipticSequence

Depends on / 依赖: IsEllipticNet, IsEllipticNet.rel
-/
def IsEllipticSequence : Prop :=
  forall p q r : Int, IsEllipticNet.rel W p q r 0 = 0

@[deprecated (since := "2026-07-01")] alias IsEllSequence := IsEllipticSequence

/--
Definition of `IsEllipticDvdSequence` / `IsEllipticDvdSequence` 的定义

English:
definition IsEllipticDvdSequence
  signature: : Prop
  body: IsEllipticSequence W ∧ IsDvdSequence W

@[deprecated (since := "2026-06-30")] alias IsEllDivSequence := IsEllipticDvdSequence

中文:
定义 IsEllipticDvdSequence
  签名: : 命题
  定义体: IsEllipticSequence W ∧ IsDvdSequence W

@[deprecated (since := "2026-06-30")] alias IsEllDivSequence := IsEllipticDvdSequence

Depends on / 依赖: IsDvdSequence, IsEllipticSequence
-/
def IsEllipticDvdSequence : Prop :=
  IsEllipticSequence W ∧ IsDvdSequence W

@[deprecated (since := "2026-06-30")] alias IsEllDivSequence := IsEllipticDvdSequence

namespace IsEllipticNet

variable {W}

/--
lemma `isEllipticSequence` / 引理 `isEllipticSequence`

English:
lemma isEllipticSequence
  given: (h : IsEllipticNet W)
  statement: IsEllipticSequence W
  proof: (h · · · 0)

中文:
引理 isEllipticSequence
  条件: (h : IsEllipticNet W)
  结论: IsEllipticSequence W
  证明: (h · · · 0)
-/
lemma isEllipticSequence (h : IsEllipticNet W) : IsEllipticSequence W :=
  (h · · · 0)

/--
lemma `id` / 引理 `id`

English:
lemma id
  statement: IsEllipticNet (id : Int -> Int)
  proof: fun _ _ _ _ => by simp_rw [rel, id_eq]; ring1

中文:
引理 id
  结论: IsEllipticNet (id : 整数 -> 整数)
  证明: fun _ _ _ _ => by simp_rw [rel, id_eq]; ring1
-/
protected lemma id : IsEllipticNet (id : Int -> Int) :=
  fun _ _ _ _ => by simp_rw [rel, id_eq]; ring1

/--
lemma `smul` / 引理 `smul`

English:
lemma smul
  given: (h : IsEllipticNet W) (x : R)
  statement: IsEllipticNet x • W
  proof: fun p q r s => by
  linear_combination (norm := (simp_rw [rel, Pi.smul_apply, smul_eq_mul]; ring1)) x ^ 4 * h p q r s

中文:
引理 smul
  条件: (h : IsEllipticNet W) (x : R)
  结论: IsEllipticNet x • W
  证明: fun p q r s => by
  linear_combination (norm := (simp_rw [rel, Pi.smul_apply, smul_eq_mul]; ring1)) x ^ 4 * h p q r s
-/
protected lemma smul (h : IsEllipticNet W) (x : R) : IsEllipticNet x • W := fun p q r s => by
  linear_combination (norm := (simp_rw [rel, Pi.smul_apply, smul_eq_mul]; ring1)) x ^ 4 * h p q r s

end IsEllipticNet

namespace IsEllipticSequence

variable {W}

/--
lemma `id` / 引理 `id`

English:
lemma id
  statement: IsEllipticSequence (id : Int -> Int)
  proof: IsEllipticNet.id.isEllipticSequence

中文:
引理 id
  结论: IsEllipticSequence (id : 整数 -> 整数)
  证明: IsEllipticNet.id.isEllipticSequence
-/
protected lemma id : IsEllipticSequence (id : Int -> Int) :=
  IsEllipticNet.id.isEllipticSequence

/--
lemma `smul` / 引理 `smul`

English:
lemma smul
  given: (h : IsEllipticSequence W) (x : R)
  statement: IsEllipticSequence x • W
  proof: fun p q r => by linear_combination (norm := (simp [IsEllipticNet.rel]; ring1)) x ^ 4 * h p q r

中文:
引理 smul
  条件: (h : IsEllipticSequence W) (x : R)
  结论: IsEllipticSequence x • W
  证明: fun p q r => by linear_combination (norm := (simp [IsEllipticNet.rel]; ring1)) x ^ 4 * h p q r
-/
protected lemma smul (h : IsEllipticSequence W) (x : R) : IsEllipticSequence x • W :=
  fun p q r => by linear_combination (norm := (simp [IsEllipticNet.rel]; ring1)) x ^ 4 * h p q r

end IsEllipticSequence

@[deprecated (since := "2026-07-01")] alias isEllSequence_id := IsEllipticSequence.id
@[deprecated (since := "2026-07-01")] alias IsEllSequence.smul := IsEllipticSequence.smul

namespace IsEllipticDvdSequence

variable {W}

/--
theorem `id` / 定理 `id`

English:
theorem id
  statement: IsEllipticDvdSequence (id : Int -> Int)
  proof: ⟨IsEllipticSequence.id, .id Int⟩

中文:
定理 id
  结论: IsEllipticDvdSequence (id : 整数 -> 整数)
  证明: ⟨IsEllipticSequence.id, .id Int⟩
-/
protected theorem id : IsEllipticDvdSequence (id : Int -> Int) :=
  ⟨IsEllipticSequence.id, .id Int⟩

/--
lemma `smul` / 引理 `smul`

English:
lemma smul
  given: (h : IsEllipticDvdSequence W) (x : R)
  statement: IsEllipticDvdSequence x • W
  proof: ⟨h.left.smul x, h.right.smul x⟩

中文:
引理 smul
  条件: (h : IsEllipticDvdSequence W) (x : R)
  结论: IsEllipticDvdSequence x • W
  证明: ⟨h.left.smul x, h.right.smul x⟩
-/
protected lemma smul (h : IsEllipticDvdSequence W) (x : R) : IsEllipticDvdSequence x • W :=
  ⟨h.left.smul x, h.right.smul x⟩

end IsEllipticDvdSequence

@[deprecated (since := "2026-06-30")] alias isEllDivSequence_id := IsEllipticDvdSequence.id
@[deprecated (since := "2026-06-30")] alias IsEllDivSequence.smul := IsEllipticDvdSequence.smul

variable (b c d : R)

section PreNormEDS

/--
Definition of `preNormEDS'` / `preNormEDS'` 的定义

English:
definition preNormEDS'
  signature: : Nat -> R
  body: n / 2
    if hn : Even n then
      preNormEDS' (m + 4) * preNormEDS' (m + 2) ^ 3 * (if Even m then b else 1) -
        preNormEDS' (m + 1) * preNormEDS' (m + 3) ^ 3 * (if Even m then 1 else b)
    else
      have : m + 5 < n + 5 := by
        gcongr; exact Nat.div_lt_self (Nat.not_even_iff_odd.mp h

中文:
定义 preNormEDS'
  签名: : 自然数 -> R
  定义体: n / 2
    if hn : Even n then
      preNormEDS' (m + 4) * preNormEDS' (m + 2) ^ 3 * (if Even m then b else 1) -
        preNormEDS' (m + 1) * preNormEDS' (m + 3) ^ 3 * (if Even m then 1 else b)
    else
      have : m + 5 < n + 5 := by
        gcongr; exact Nat.div_lt_self (Nat.not_even_iff_odd.mp h
-/
def preNormEDS' : Nat -> R
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => c
  | 4 => d
  | (n + 5) => let m := n / 2
    if hn : Even n then
      preNormEDS' (m + 4) * preNormEDS' (m + 2) ^ 3 * (if Even m then b else 1) -
        preNormEDS' (m + 1) * preNormEDS' (m + 3) ^ 3 * (if Even m then 1 else b)
    else
      have : m + 5 < n + 5 := by
        gcongr; exact Nat.div_lt_self (Nat.not_even_iff_odd.mp hn).pos one_lt_two
      preNormEDS' (m + 2) ^ 2 * preNormEDS' (m + 3) * preNormEDS' (m + 5) -
        preNormEDS' (m + 1) * preNormEDS' (m + 3) * preNormEDS' (m + 4) ^ 2

@[simp]
/--
lemma `preNormEDS'_zero` / 引理 `preNormEDS'_zero`

English:
lemma preNormEDS'_zero
  statement: preNormEDS' b c d 0 = 0
  proof: by
  rw [preNormEDS']

@[simp]

中文:
引理 preNormEDS'_zero
  结论: preNormEDS' b c d 0 = 0
  证明: by
  rw [preNormEDS']

@[simp]
-/
lemma preNormEDS'_zero : preNormEDS' b c d 0 = 0 := by
  rw [preNormEDS']

@[simp]
/--
lemma `preNormEDS'_one` / 引理 `preNormEDS'_one`

English:
lemma preNormEDS'_one
  statement: preNormEDS' b c d 1 = 1
  proof: by
  rw [preNormEDS']

@[simp]

中文:
引理 preNormEDS'_one
  结论: preNormEDS' b c d 1 = 1
  证明: by
  rw [preNormEDS']

@[simp]
-/
lemma preNormEDS'_one : preNormEDS' b c d 1 = 1 := by
  rw [preNormEDS']

@[simp]
/--
lemma `preNormEDS'_two` / 引理 `preNormEDS'_two`

English:
lemma preNormEDS'_two
  statement: preNormEDS' b c d 2 = 1
  proof: by
  rw [preNormEDS']

@[simp]

中文:
引理 preNormEDS'_two
  结论: preNormEDS' b c d 2 = 1
  证明: by
  rw [preNormEDS']

@[simp]
-/
lemma preNormEDS'_two : preNormEDS' b c d 2 = 1 := by
  rw [preNormEDS']

@[simp]
/--
lemma `preNormEDS'_three` / 引理 `preNormEDS'_three`

English:
lemma preNormEDS'_three
  statement: preNormEDS' b c d 3 = c
  proof: by
  rw [preNormEDS']

@[simp]

中文:
引理 preNormEDS'_three
  结论: preNormEDS' b c d 3 = c
  证明: by
  rw [preNormEDS']

@[simp]
-/
lemma preNormEDS'_three : preNormEDS' b c d 3 = c := by
  rw [preNormEDS']

@[simp]
/--
lemma `preNormEDS'_four` / 引理 `preNormEDS'_four`

English:
lemma preNormEDS'_four
  statement: preNormEDS' b c d 4 = d
  proof: by
  rw [preNormEDS']

中文:
引理 preNormEDS'_four
  结论: preNormEDS' b c d 4 = d
  证明: by
  rw [preNormEDS']
-/
lemma preNormEDS'_four : preNormEDS' b c d 4 = d := by
  rw [preNormEDS']

/--
lemma `preNormEDS'_even` / 引理 `preNormEDS'_even`

English:
lemma preNormEDS'_even
  given: (m : Nat)
  statement: preNormEDS' b c d (2 * (m + 3)) =
  proof: by
  rw [show 2 * (m + 3) = 2 * m + 1 + 5 by rfl]; rw [preNormEDS']; rw [dif_neg m.not_even_two_mul_add_one]
  simp [Nat.mul_add_div two_pos]

中文:
引理 preNormEDS'_even
  条件: (m : 自然数)
  结论: preNormEDS' b c d (2 * (m + 3)) =
  证明: by
  rw [show 2 * (m + 3) = 2 * m + 1 + 5 by rfl]; rw [preNormEDS']; rw [dif_neg m.not_even_two_mul_add_one]
  simp [Nat.mul_add_div two_pos]
-/
lemma preNormEDS'_even (m : Nat) : preNormEDS' b c d (2 * (m + 3)) =
    preNormEDS' b c d (m + 2) ^ 2 * preNormEDS' b c d (m + 3) * preNormEDS' b c d (m + 5) -
      preNormEDS' b c d (m + 1) * preNormEDS' b c d (m + 3) * preNormEDS' b c d (m + 4) ^ 2 := by
  rw [show 2 * (m + 3) = 2 * m + 1 + 5 by rfl]; rw [preNormEDS']; rw [dif_neg m.not_even_two_mul_add_one]
  simp [Nat.mul_add_div two_pos]

/--
lemma `preNormEDS'_odd` / 引理 `preNormEDS'_odd`

English:
lemma preNormEDS'_odd
  given: (m : Nat)
  statement: preNormEDS' b c d (2 * (m + 2) + 1) =
  proof: by
  rw [show 2 * (m + 2) + 1 = 2 * m + 5 by rfl]; rw [preNormEDS']; rw [dif_pos <| even_two_mul m]; rw [m.mul_div_cancel_left two_pos]

中文:
引理 preNormEDS'_odd
  条件: (m : 自然数)
  结论: preNormEDS' b c d (2 * (m + 2) + 1) =
  证明: by
  rw [show 2 * (m + 2) + 1 = 2 * m + 5 by rfl]; rw [preNormEDS']; rw [dif_pos <| even_two_mul m]; rw [m.mul_div_cancel_left two_pos]
-/
lemma preNormEDS'_odd (m : Nat) : preNormEDS' b c d (2 * (m + 2) + 1) =
    preNormEDS' b c d (m + 4) * preNormEDS' b c d (m + 2) ^ 3 * (if Even m then b else 1) -
      preNormEDS' b c d (m + 1) * preNormEDS' b c d (m + 3) ^ 3 * (if Even m then 1 else b) := by
  rw [show 2 * (m + 2) + 1 = 2 * m + 5 by rfl]; rw [preNormEDS']; rw [dif_pos <| even_two_mul m]; rw [m.mul_div_cancel_left two_pos]

/--
Definition of `preNormEDS` / `preNormEDS` 的定义

English:
definition preNormEDS
  signature: (n : Int)
  body: n.sign * preNormEDS' b c d n.natAbs

@[simp]

中文:
定义 preNormEDS
  签名: (n : 整数)
  定义体: n.sign * preNormEDS' b c d n.natAbs

@[simp]

Depends on / 依赖: n.natAbs, n.sign, natAbs, preNormEDS
-/
def preNormEDS (n : Int) : R :=
  n.sign * preNormEDS' b c d n.natAbs

@[simp]
/--
lemma `preNormEDS_ofNat` / 引理 `preNormEDS_ofNat`

English:
lemma preNormEDS_ofNat
  given: (n : Nat)
  statement: preNormEDS b c d n = preNormEDS' b c d n
  proof: by
  by_cases hn : n = 0
  · simp [hn, preNormEDS]
  · simp [preNormEDS, Int.sign_natCast_of_ne_zero hn]

@[simp]

中文:
引理 preNormEDS_ofNat
  条件: (n : 自然数)
  结论: preNormEDS b c d n = preNormEDS' b c d n
  证明: by
  by_cases hn : n = 0
  · simp [hn, preNormEDS]
  · simp [preNormEDS, Int.sign_natCast_of_ne_zero hn]

@[simp]

Depends on / 依赖: Int.sign_natCast_of_ne_zero, preNormEDS, sign_natCast_of_ne_zero
-/
lemma preNormEDS_ofNat (n : Nat) : preNormEDS b c d n = preNormEDS' b c d n := by
  by_cases hn : n = 0
  · simp [hn, preNormEDS]
  · simp [preNormEDS, Int.sign_natCast_of_ne_zero hn]

@[simp]
/--
lemma `preNormEDS_zero` / 引理 `preNormEDS_zero`

English:
lemma preNormEDS_zero
  statement: preNormEDS b c d 0 = 0
  proof: by
  simp [preNormEDS]

@[simp]

中文:
引理 preNormEDS_zero
  结论: preNormEDS b c d 0 = 0
  证明: by
  simp [preNormEDS]

@[simp]

Depends on / 依赖: preNormEDS
-/
lemma preNormEDS_zero : preNormEDS b c d 0 = 0 := by
  simp [preNormEDS]

@[simp]
/--
lemma `preNormEDS_one` / 引理 `preNormEDS_one`

English:
lemma preNormEDS_one
  statement: preNormEDS b c d 1 = 1
  proof: by
  simp [preNormEDS]

@[simp]

中文:
引理 preNormEDS_one
  结论: preNormEDS b c d 1 = 1
  证明: by
  simp [preNormEDS]

@[simp]

Depends on / 依赖: preNormEDS
-/
lemma preNormEDS_one : preNormEDS b c d 1 = 1 := by
  simp [preNormEDS]

@[simp]
/--
lemma `preNormEDS_two` / 引理 `preNormEDS_two`

English:
lemma preNormEDS_two
  statement: preNormEDS b c d 2 = 1
  proof: by
  simp [preNormEDS, Int.sign_eq_one_of_pos]

@[simp]

中文:
引理 preNormEDS_two
  结论: preNormEDS b c d 2 = 1
  证明: by
  simp [preNormEDS, Int.sign_eq_one_of_pos]

@[simp]

Depends on / 依赖: Int.sign_eq_one_of_pos, preNormEDS, sign_eq_one_of_pos
-/
lemma preNormEDS_two : preNormEDS b c d 2 = 1 := by
  simp [preNormEDS, Int.sign_eq_one_of_pos]

@[simp]
/--
lemma `preNormEDS_three` / 引理 `preNormEDS_three`

English:
lemma preNormEDS_three
  statement: preNormEDS b c d 3 = c
  proof: by
  simp [preNormEDS, Int.sign_eq_one_of_pos]

@[simp]

中文:
引理 preNormEDS_three
  结论: preNormEDS b c d 3 = c
  证明: by
  simp [preNormEDS, Int.sign_eq_one_of_pos]

@[simp]

Depends on / 依赖: Int.sign_eq_one_of_pos, preNormEDS, sign_eq_one_of_pos
-/
lemma preNormEDS_three : preNormEDS b c d 3 = c := by
  simp [preNormEDS, Int.sign_eq_one_of_pos]

@[simp]
/--
lemma `preNormEDS_four` / 引理 `preNormEDS_four`

English:
lemma preNormEDS_four
  statement: preNormEDS b c d 4 = d
  proof: by
  simp [preNormEDS, Int.sign_eq_one_of_pos]

@[simp]

中文:
引理 preNormEDS_four
  结论: preNormEDS b c d 4 = d
  证明: by
  simp [preNormEDS, Int.sign_eq_one_of_pos]

@[simp]

Depends on / 依赖: Int.sign_eq_one_of_pos, preNormEDS, sign_eq_one_of_pos
-/
lemma preNormEDS_four : preNormEDS b c d 4 = d := by
  simp [preNormEDS, Int.sign_eq_one_of_pos]

@[simp]
/--
lemma `preNormEDS_neg` / 引理 `preNormEDS_neg`

English:
lemma preNormEDS_neg
  given: (n : Int)
  statement: preNormEDS b c d (-n) = -preNormEDS b c d n
  proof: by
  simp [preNormEDS]

中文:
引理 preNormEDS_neg
  条件: (n : 整数)
  结论: preNormEDS b c d (-n) = -preNormEDS b c d n
  证明: by
  simp [preNormEDS]

Depends on / 依赖: preNormEDS
-/
lemma preNormEDS_neg (n : Int) : preNormEDS b c d (-n) = -preNormEDS b c d n := by
  simp [preNormEDS]

/--
lemma `preNormEDS_even` / 引理 `preNormEDS_even`

English:
lemma preNormEDS_even
  given: (m : Int)
  statement: preNormEDS b c d (2 * m) =
  proof: by
  induction m using Int.negInduction with
  | nat m =>
    rcases m with _ | _ | _ | m
    iterate 3 simp
    simp_rw [Nat.cast_succ, Int.add_sub_cancel, show (m : Int) + 1 + 1 + 1 = m + 1 + 2 by rfl,
      Int.add_sub_cancel]
    norm_cast
    simpa only [preNormEDS_ofNat] using preNormEDS'_even

中文:
引理 preNormEDS_even
  条件: (m : 整数)
  结论: preNormEDS b c d (2 * m) =
  证明: by
  induction m using Int.negInduction with
  | nat m =>
    rcases m with _ | _ | _ | m
    iterate 3 simp
    simp_rw [Nat.cast_succ, Int.add_sub_cancel, show (m : Int) + 1 + 1 + 1 = m + 1 + 2 by rfl,
      Int.add_sub_cancel]
    norm_cast
    simpa only [preNormEDS_ofNat] using preNormEDS'_even

Depends on / 依赖: Int.add_sub_cancel, Int.negInduction, Nat.cast_succ, _even, add_sub_cancel, cast_succ, iterate, mul_neg, negInduction, neg_add, neg_sub, preNormEDS, preNormEDS_neg, preNormEDS_ofNat, simp_rw, sub_neg_eq_add
-/
lemma preNormEDS_even (m : Int) : preNormEDS b c d (2 * m) =
    preNormEDS b c d (m - 1) ^ 2 * preNormEDS b c d m * preNormEDS b c d (m + 2) -
      preNormEDS b c d (m - 2) * preNormEDS b c d m * preNormEDS b c d (m + 1) ^ 2 := by
  induction m using Int.negInduction with
  | nat m =>
    rcases m with _ | _ | _ | m
    iterate 3 simp
    simp_rw [Nat.cast_succ, Int.add_sub_cancel, show (m : Int) + 1 + 1 + 1 = m + 1 + 2 by rfl,
      Int.add_sub_cancel]
    norm_cast
    simpa only [preNormEDS_ofNat] using preNormEDS'_even ..
  | neg ih m =>
    simp_rw [mul_neg, ← sub_neg_eq_add, ← neg_sub', ← neg_add', preNormEDS_neg, ih]
    ring1

/--
lemma `preNormEDS_odd` / 引理 `preNormEDS_odd`

English:
lemma preNormEDS_odd
  given: (m : Int)
  statement: preNormEDS b c d (2 * m + 1) =
  proof: by
  induction m using Int.negInduction with
  | nat m =>
    rcases m with _ | _ | _
    iterate 2 simp
    simp_rw [Nat.cast_succ, Int.add_sub_cancel, Int.even_add_one, not_not, Int.even_coe_nat]
    norm_cast
    simpa only [preNormEDS_ofNat] using preNormEDS'_odd ..
  | neg ih m =>
    rcases m 

中文:
引理 preNormEDS_odd
  条件: (m : 整数)
  结论: preNormEDS b c d (2 * m + 1) =
  证明: by
  induction m using Int.negInduction with
  | nat m =>
    rcases m with _ | _ | _
    iterate 2 simp
    simp_rw [Nat.cast_succ, Int.add_sub_cancel, Int.even_add_one, not_not, Int.even_coe_nat]
    norm_cast
    simpa only [preNormEDS_ofNat] using preNormEDS'_odd ..
  | neg ih m =>
    rcases m 

Depends on / 依赖: Int.add_sub_cancel, Int.even_add_one, Int.even_coe_nat, Int.negInduction, Nat.cast_succ, _odd, add_sub_cancel, cast_succ, even_add_one, even_coe_nat, iterate, negInduction, not_not, preNormEDS, preNormEDS_ofNat, simp_rw
-/
lemma preNormEDS_odd (m : Int) : preNormEDS b c d (2 * m + 1) =
    preNormEDS b c d (m + 2) * preNormEDS b c d m ^ 3 * (if Even m then b else 1) -
      preNormEDS b c d (m - 1) * preNormEDS b c d (m + 1) ^ 3 * (if Even m then 1 else b) := by
  induction m using Int.negInduction with
  | nat m =>
    rcases m with _ | _ | _
    iterate 2 simp
    simp_rw [Nat.cast_succ, Int.add_sub_cancel, Int.even_add_one, not_not, Int.even_coe_nat]
    norm_cast
    simpa only [preNormEDS_ofNat] using preNormEDS'_odd ..
  | neg ih m =>
    rcases m with _ | m
    · simp
    simp_rw [Nat.cast_succ, show 2 * -(m + 1 : Int) + 1 = -(2 * m + 1) by rfl,
      show -(m + 1 : Int) + 2 = -(m - 1) by ring1, show -(m + 1 : Int) - 1 = -(m + 2) by rfl,
      show -(m + 1 : Int) + 1 = -m by ring1, preNormEDS_neg, even_neg, Int.even_add_one, ite_not, ih]
    ring1

/--
Definition of `complEDS₂` / `complEDS₂` 的定义

English:
definition complEDS₂
  signature: (k : Int)
  body: (preNormEDS (b ^ 4) c d (k - 1) ^ 2 * preNormEDS (b ^ 4) c d (k + 2) -
    preNormEDS (b ^ 4) c d (k - 2) * preNormEDS (b ^ 4) c d (k + 1) ^ 2) * if Even k then 1 else b

@[simp]

中文:
定义 complEDS₂
  签名: (k : 整数)
  定义体: (preNormEDS (b ^ 4) c d (k - 1) ^ 2 * preNormEDS (b ^ 4) c d (k + 2) -
    preNormEDS (b ^ 4) c d (k - 2) * preNormEDS (b ^ 4) c d (k + 1) ^ 2) * if Even k then 1 else b

@[simp]

Depends on / 依赖: preNormEDS
-/
def complEDS₂ (k : Int) : R :=
  (preNormEDS (b ^ 4) c d (k - 1) ^ 2 * preNormEDS (b ^ 4) c d (k + 2) -
    preNormEDS (b ^ 4) c d (k - 2) * preNormEDS (b ^ 4) c d (k + 1) ^ 2) * if Even k then 1 else b

@[simp]
/--
lemma `complEDS₂_zero` / 引理 `complEDS₂_zero`

English:
lemma complEDS₂_zero
  statement: complEDS₂ b c d 0 = 2
  proof: by
  simp [complEDS₂, one_add_one_eq_two]

@[simp]

中文:
引理 complEDS₂_zero
  结论: complEDS₂ b c d 0 = 2
  证明: by
  simp [complEDS₂, one_add_one_eq_two]

@[simp]

Depends on / 依赖: one_add_one_eq_two
-/
lemma complEDS₂_zero : complEDS₂ b c d 0 = 2 := by
  simp [complEDS₂, one_add_one_eq_two]

@[simp]
/--
lemma `complEDS₂_one` / 引理 `complEDS₂_one`

English:
lemma complEDS₂_one
  statement: complEDS₂ b c d 1 = b
  proof: by
  simp [complEDS₂]

@[simp]

中文:
引理 complEDS₂_one
  结论: complEDS₂ b c d 1 = b
  证明: by
  simp [complEDS₂]

@[simp]
-/
lemma complEDS₂_one : complEDS₂ b c d 1 = b := by
  simp [complEDS₂]

@[simp]
/--
lemma `complEDS₂_two` / 引理 `complEDS₂_two`

English:
lemma complEDS₂_two
  statement: complEDS₂ b c d 2 = d
  proof: by
  simp [complEDS₂]

@[simp]

中文:
引理 complEDS₂_two
  结论: complEDS₂ b c d 2 = d
  证明: by
  simp [complEDS₂]

@[simp]
-/
lemma complEDS₂_two : complEDS₂ b c d 2 = d := by
  simp [complEDS₂]

@[simp]
/--
lemma `complEDS₂_three` / 引理 `complEDS₂_three`

English:
lemma complEDS₂_three
  statement: complEDS₂ b c d 3 = preNormEDS (b ^ 4) c d 5 * b - d ^ 2 * b
  proof: by
  simp [complEDS₂, if_neg (by decide : ¬Even (3 : Int)), sub_mul]

@[simp]

中文:
引理 complEDS₂_three
  结论: complEDS₂ b c d 3 = preNormEDS (b ^ 4) c d 5 * b - d ^ 2 * b
  证明: by
  simp [complEDS₂, if_neg (by decide : ¬Even (3 : Int)), sub_mul]

@[simp]

Depends on / 依赖: if_neg, sub_mul
-/
lemma complEDS₂_three : complEDS₂ b c d 3 = preNormEDS (b ^ 4) c d 5 * b - d ^ 2 * b := by
  simp [complEDS₂, if_neg (by decide : ¬Even (3 : Int)), sub_mul]

@[simp]
/--
lemma `complEDS₂_four` / 引理 `complEDS₂_four`

English:
lemma complEDS₂_four
  statement: complEDS₂ b c d 4 =
  proof: by
  simp [complEDS₂, if_pos (by decide : Even (4 : Int))]

@[simp]

中文:
引理 complEDS₂_four
  结论: complEDS₂ b c d 4 =
  证明: by
  simp [complEDS₂, if_pos (by decide : Even (4 : Int))]

@[simp]

Depends on / 依赖: if_pos
-/
lemma complEDS₂_four : complEDS₂ b c d 4 =
    c ^ 2 * preNormEDS (b ^ 4) c d 6 - preNormEDS (b ^ 4) c d 5 ^ 2 := by
  simp [complEDS₂, if_pos (by decide : Even (4 : Int))]

@[simp]
/--
lemma `complEDS₂_neg` / 引理 `complEDS₂_neg`

English:
lemma complEDS₂_neg
  given: (k : Int)
  statement: complEDS₂ b c d (-k) = complEDS₂ b c d k
  proof: by
  simp_rw [complEDS₂, ← neg_add', ← sub_neg_eq_add, ← neg_sub', preNormEDS_neg, even_neg]
  ring1

中文:
引理 complEDS₂_neg
  条件: (k : 整数)
  结论: complEDS₂ b c d (-k) = complEDS₂ b c d k
  证明: by
  simp_rw [complEDS₂, ← neg_add', ← sub_neg_eq_add, ← neg_sub', preNormEDS_neg, even_neg]
  ring1

Depends on / 依赖: even_neg, neg_add, neg_sub, preNormEDS_neg, simp_rw, sub_neg_eq_add
-/
lemma complEDS₂_neg (k : Int) : complEDS₂ b c d (-k) = complEDS₂ b c d k := by
  simp_rw [complEDS₂, ← neg_add', ← sub_neg_eq_add, ← neg_sub', preNormEDS_neg, even_neg]
  ring1

/--
lemma `preNormEDS_mul_complEDS₂` / 引理 `preNormEDS_mul_complEDS₂`

English:
lemma preNormEDS_mul_complEDS₂
  given: (k : Int)
  statement: preNormEDS (b ^ 4) c d k * complEDS₂ b c d k =
  proof: by
  rw [complEDS₂]; rw [preNormEDS_even]
  ring1

中文:
引理 preNormEDS_mul_complEDS₂
  条件: (k : 整数)
  结论: preNormEDS (b ^ 4) c d k * complEDS₂ b c d k =
  证明: by
  rw [complEDS₂]; rw [preNormEDS_even]
  ring1

Depends on / 依赖: preNormEDS_even
-/
lemma preNormEDS_mul_complEDS₂ (k : Int) : preNormEDS (b ^ 4) c d k * complEDS₂ b c d k =
    preNormEDS (b ^ 4) c d (2 * k) * if Even k then 1 else b := by
  rw [complEDS₂]; rw [preNormEDS_even]
  ring1

end PreNormEDS

section NormEDS

/--
Definition of `normEDS` / `normEDS` 的定义

English:
definition normEDS
  signature: (n : Int)
  body: preNormEDS (b ^ 4) c d n * if Even n then b else 1

@[simp]

中文:
定义 normEDS
  签名: (n : 整数)
  定义体: preNormEDS (b ^ 4) c d n * if Even n then b else 1

@[simp]

Depends on / 依赖: preNormEDS
-/
def normEDS (n : Int) : R :=
  preNormEDS (b ^ 4) c d n * if Even n then b else 1

@[simp]
/--
lemma `normEDS_ofNat` / 引理 `normEDS_ofNat`

English:
lemma normEDS_ofNat
  given: (n : Nat)
  proof: by
  simp [normEDS]

@[simp]

中文:
引理 normEDS_ofNat
  条件: (n : 自然数)
  证明: by
  simp [normEDS]

@[simp]

Depends on / 依赖: normEDS
-/
lemma normEDS_ofNat (n : Nat) :
    normEDS b c d n = preNormEDS' (b ^ 4) c d n * if Even n then b else 1 := by
  simp [normEDS]

@[simp]
/--
lemma `normEDS_zero` / 引理 `normEDS_zero`

English:
lemma normEDS_zero
  statement: normEDS b c d 0 = 0
  proof: by
  simp [normEDS]

@[simp]

中文:
引理 normEDS_zero
  结论: normEDS b c d 0 = 0
  证明: by
  simp [normEDS]

@[simp]

Depends on / 依赖: normEDS
-/
lemma normEDS_zero : normEDS b c d 0 = 0 := by
  simp [normEDS]

@[simp]
/--
lemma `normEDS_one` / 引理 `normEDS_one`

English:
lemma normEDS_one
  statement: normEDS b c d 1 = 1
  proof: by
  simp [normEDS]

@[simp]

中文:
引理 normEDS_one
  结论: normEDS b c d 1 = 1
  证明: by
  simp [normEDS]

@[simp]

Depends on / 依赖: normEDS
-/
lemma normEDS_one : normEDS b c d 1 = 1 := by
  simp [normEDS]

@[simp]
/--
lemma `normEDS_two` / 引理 `normEDS_two`

English:
lemma normEDS_two
  statement: normEDS b c d 2 = b
  proof: by
  simp [normEDS]

@[simp]

中文:
引理 normEDS_two
  结论: normEDS b c d 2 = b
  证明: by
  simp [normEDS]

@[simp]

Depends on / 依赖: normEDS
-/
lemma normEDS_two : normEDS b c d 2 = b := by
  simp [normEDS]

@[simp]
/--
lemma `normEDS_three` / 引理 `normEDS_three`

English:
lemma normEDS_three
  statement: normEDS b c d 3 = c
  proof: by
  simp [normEDS, show ¬Even (3 : Int) by decide]

@[simp]

中文:
引理 normEDS_three
  结论: normEDS b c d 3 = c
  证明: by
  simp [normEDS, show ¬Even (3 : Int) by decide]

@[simp]

Depends on / 依赖: normEDS
-/
lemma normEDS_three : normEDS b c d 3 = c := by
  simp [normEDS, show ¬Even (3 : Int) by decide]

@[simp]
/--
lemma `normEDS_four` / 引理 `normEDS_four`

English:
lemma normEDS_four
  statement: normEDS b c d 4 = d * b
  proof: by
  simp [normEDS, show ¬Odd (4 : Int) by decide]

@[simp]

中文:
引理 normEDS_four
  结论: normEDS b c d 4 = d * b
  证明: by
  simp [normEDS, show ¬Odd (4 : Int) by decide]

@[simp]

Depends on / 依赖: normEDS
-/
lemma normEDS_four : normEDS b c d 4 = d * b := by
  simp [normEDS, show ¬Odd (4 : Int) by decide]

@[simp]
/--
lemma `normEDS_neg` / 引理 `normEDS_neg`

English:
lemma normEDS_neg
  given: (n : Int)
  statement: normEDS b c d (-n) = -normEDS b c d n
  proof: by
  simp_rw [normEDS, preNormEDS_neg, even_neg, neg_mul]

中文:
引理 normEDS_neg
  条件: (n : 整数)
  结论: normEDS b c d (-n) = -normEDS b c d n
  证明: by
  simp_rw [normEDS, preNormEDS_neg, even_neg, neg_mul]

Depends on / 依赖: even_neg, neg_mul, normEDS, preNormEDS_neg, simp_rw
-/
lemma normEDS_neg (n : Int) : normEDS b c d (-n) = -normEDS b c d n := by
  simp_rw [normEDS, preNormEDS_neg, even_neg, neg_mul]

/--
lemma `normEDS_mul_complEDS₂` / 引理 `normEDS_mul_complEDS₂`

English:
lemma normEDS_mul_complEDS₂
  given: (k : Int)
  proof: by
  simp_rw [normEDS, mul_right_comm, preNormEDS_mul_complEDS₂, mul_assoc, apply_ite₂, one_mul,
mul_one, ite_self, if_pos even_two_mul k]

中文:
引理 normEDS_mul_complEDS₂
  条件: (k : 整数)
  证明: by
  simp_rw [normEDS, mul_right_comm, preNormEDS_mul_complEDS₂, mul_assoc, apply_ite₂, one_mul,
mul_one, ite_self, if_pos even_two_mul k]

Depends on / 依赖: even_two_mul, if_pos, ite_self, mul_assoc, mul_one, mul_right_comm, normEDS, one_mul, simp_rw
-/
lemma normEDS_mul_complEDS₂ (k : Int) :
    normEDS b c d k * complEDS₂ b c d k = normEDS b c d (2 * k) := by
  simp_rw [normEDS, mul_right_comm, preNormEDS_mul_complEDS₂, mul_assoc, apply_ite₂, one_mul,
mul_one, ite_self, if_pos even_two_mul k]

/--
lemma `normEDS_dvd_normEDS_two_mul` / 引理 `normEDS_dvd_normEDS_two_mul`

English:
lemma normEDS_dvd_normEDS_two_mul
  given: (k : Int)
  statement: normEDS b c d k ∣ normEDS b c d (2 * k)
  proof: ⟨complEDS₂ .., (normEDS_mul_complEDS₂ ..).symm⟩

中文:
引理 normEDS_dvd_normEDS_two_mul
  条件: (k : 整数)
  结论: normEDS b c d k ∣ normEDS b c d (2 * k)
  证明: ⟨complEDS₂ .., (normEDS_mul_complEDS₂ ..).symm⟩
-/
lemma normEDS_dvd_normEDS_two_mul (k : Int) : normEDS b c d k ∣ normEDS b c d (2 * k) :=
  ⟨complEDS₂ .., (normEDS_mul_complEDS₂ ..).symm⟩

/--
lemma `complEDS₂_mul_b` / 引理 `complEDS₂_mul_b`

English:
lemma complEDS₂_mul_b
  given: (k : Int)
  statement: complEDS₂ b c d k * b =
  proof: by
  simp_rw [complEDS₂, normEDS, Int.even_add, Int.even_sub, even_two, iff_true, Int.not_even_one,
    iff_false]
  split_ifs <;> ring1

中文:
引理 complEDS₂_mul_b
  条件: (k : 整数)
  结论: complEDS₂ b c d k * b =
  证明: by
  simp_rw [complEDS₂, normEDS, Int.even_add, Int.even_sub, even_two, iff_true, Int.not_even_one,
    iff_false]
  split_ifs <;> ring1

Depends on / 依赖: Int.even_add, Int.even_sub, Int.not_even_one, even_add, even_sub, even_two, iff_false, iff_true, normEDS, not_even_one, simp_rw, split_ifs
-/
lemma complEDS₂_mul_b (k : Int) : complEDS₂ b c d k * b =
    normEDS b c d (k - 1) ^ 2 * normEDS b c d (k + 2) -
      normEDS b c d (k - 2) * normEDS b c d (k + 1) ^ 2 := by
  simp_rw [complEDS₂, normEDS, Int.even_add, Int.even_sub, even_two, iff_true, Int.not_even_one,
    iff_false]
  split_ifs <;> ring1

/--
lemma `normEDS_even` / 引理 `normEDS_even`

English:
lemma normEDS_even
  given: (m : Int)
  statement: normEDS b c d (2 * m) * b =
  proof: by
  rw [← normEDS_mul_complEDS₂]; rw [mul_assoc]; rw [complEDS₂_mul_b]
  ring1

中文:
引理 normEDS_even
  条件: (m : 整数)
  结论: normEDS b c d (2 * m) * b =
  证明: by
  rw [← normEDS_mul_complEDS₂]; rw [mul_assoc]; rw [complEDS₂_mul_b]
  ring1

Depends on / 依赖: mul_assoc
-/
lemma normEDS_even (m : Int) : normEDS b c d (2 * m) * b =
    normEDS b c d (m - 1) ^ 2 * normEDS b c d m * normEDS b c d (m + 2) -
      normEDS b c d (m - 2) * normEDS b c d m * normEDS b c d (m + 1) ^ 2 := by
  rw [← normEDS_mul_complEDS₂]; rw [mul_assoc]; rw [complEDS₂_mul_b]
  ring1

/--
lemma `normEDS_odd` / 引理 `normEDS_odd`

English:
lemma normEDS_odd
  given: (m : Int)
  statement: normEDS b c d (2 * m + 1) =
  proof: by
  simp_rw [normEDS, preNormEDS_odd, if_neg m.not_even_two_mul_add_one, Int.even_add, Int.even_sub,
    even_two, iff_true, Int.not_even_one, iff_false]
  split_ifs <;> ring1

中文:
引理 normEDS_odd
  条件: (m : 整数)
  结论: normEDS b c d (2 * m + 1) =
  证明: by
  simp_rw [normEDS, preNormEDS_odd, if_neg m.not_even_two_mul_add_one, Int.even_add, Int.even_sub,
    even_two, iff_true, Int.not_even_one, iff_false]
  split_ifs <;> ring1

Depends on / 依赖: Int.even_add, Int.even_sub, Int.not_even_one, even_add, even_sub, even_two, if_neg, iff_false, iff_true, m.not_even_two_mul_add_one, normEDS, not_even_one, not_even_two_mul_add_one, preNormEDS_odd, simp_rw, split_ifs
-/
lemma normEDS_odd (m : Int) : normEDS b c d (2 * m + 1) =
    normEDS b c d (m + 2) * normEDS b c d m ^ 3 -
      normEDS b c d (m - 1) * normEDS b c d (m + 1) ^ 3 := by
  simp_rw [normEDS, preNormEDS_odd, if_neg m.not_even_two_mul_add_one, Int.even_add, Int.even_sub,
    even_two, iff_true, Int.not_even_one, iff_false]
  split_ifs <;> ring1

/--
Strong recursion principle for a normalised EDS: if we have
* `P 0`, `P 1`, `P 2`, `P 3`, and `P 4`,
* for all `m : ℕ` we can prove `P (2 * (m + 3))` from `P k` for all `k < 2 * (m + 3)`, and
* for all `m : ℕ` we can prove `P (2 * (m + 2) + 1)` from `P k` for all `k < 2 * (m + 2) + 1`,

then we have `P n` for all `n : ℕ`.
-/
@[elab_as_elim]
/--
Definition of `normEDSRec'` / `normEDSRec'` 的定义

English:
definition normEDSRec'
  signature: {P : Nat -> Sort*}
  body: n.evenOddStrongRec (by rintro (_ | _ | _ | _) h; exacts [zero, two, four, even _ h])
    (by rintro (_ | _ | _) h; exacts [one, three, odd _ h])

中文:
定义 normEDSRec'
  签名: {P : 自然数 -> Sort*}
  定义体: n.evenOddStrongRec (by rintro (_ | _ | _ | _) h; exacts [zero, two, four, even _ h])
    (by rintro (_ | _ | _) h; exacts [one, three, odd _ h])

Depends on / 依赖: evenOddStrongRec, exacts, n.evenOddStrongRec
-/
noncomputable def normEDSRec' {P : Nat -> Sort*}
    (zero : P 0) (one : P 1) (two : P 2) (three : P 3) (four : P 4)
    (even : forall m : Nat, (forall k < 2 * (m + 3), P k) -> P (2 * (m + 3)))
    (odd : forall m : Nat, (forall k < 2 * (m + 2) + 1, P k) -> P (2 * (m + 2) + 1)) (n : Nat) : P n :=
  n.evenOddStrongRec (by rintro (_ | _ | _ | _) h; exacts [zero, two, four, even _ h])
    (by rintro (_ | _ | _) h; exacts [one, three, odd _ h])

/-- Recursion principle for a normalised EDS: if we have
* `P 0`, `P 1`, `P 2`, `P 3`, and `P 4`,
* for all `m : ℕ` we can prove `P (2 * (m + 3))` from `P (m + 1)`, `P (m + 2)`, `P (m + 3)`,
  `P (m + 4)`, and `P (m + 5)`, and
* for all `m : ℕ` we can prove `P (2 * (m + 2) + 1)` from `P (m + 1)`, `P (m + 2)`, `P (m + 3)`,
  and `P (m + 4)`,

then we have `P n` for all `n : ℕ`. -/
@[elab_as_elim]
/--
Definition of `normEDSRec` / `normEDSRec` 的定义

English:
definition normEDSRec
  signature: {P : Nat -> Sort*}
  body: normEDSRec' zero one two three four (fun _ ih => by apply even <;> exact ih _ <| by linarith only)
    (fun _ ih => by apply odd <;> exact ih _ <| by linarith only) n

中文:
定义 normEDSRec
  签名: {P : 自然数 -> Sort*}
  定义体: normEDSRec' zero one two three four (fun _ ih => by apply even <;> exact ih _ <| by linarith only)
    (fun _ ih => by apply odd <;> exact ih _ <| by linarith only) n

Depends on / 依赖: normEDSRec
-/
noncomputable def normEDSRec {P : Nat -> Sort*}
    (zero : P 0) (one : P 1) (two : P 2) (three : P 3) (four : P 4)
    (even : forall m : Nat, P (m + 1) -> P (m + 2) -> P (m + 3) -> P (m + 4) -> P (m + 5) -> P (2 * (m + 3)))
    (odd : forall m : Nat, P (m + 1) -> P (m + 2) -> P (m + 3) -> P (m + 4) -> P (2 * (m + 2) + 1)) (n : Nat) :
    P n :=
  normEDSRec' zero one two three four (fun _ ih => by apply even <;> exact ih _ <| by linarith only)
    (fun _ ih => by apply odd <;> exact ih _ <| by linarith only) n

end NormEDS

section ComplEDS

variable (k : Int)

/--
Definition of `complEDS'` / `complEDS'` 的定义

English:
definition complEDS'
  signature: : Nat -> R
  body: n / 2 + 1
    if hn : Even n then complEDS' m * complEDS₂ b c d (m * k) else
      have : m + 1 < n + 2 :=
        add_lt_add_left (Nat.div_lt_self (Nat.not_even_iff_odd.mp hn).pos one_lt_two) 2
      complEDS' m ^ 2 * normEDS b c d ((m + 1) * k + 1) * normEDS b c d ((m + 1) * k - 1) -
        compl

中文:
定义 complEDS'
  签名: : 自然数 -> R
  定义体: n / 2 + 1
    if hn : Even n then complEDS' m * complEDS₂ b c d (m * k) else
      have : m + 1 < n + 2 :=
        add_lt_add_left (Nat.div_lt_self (Nat.not_even_iff_odd.mp hn).pos one_lt_two) 2
      complEDS' m ^ 2 * normEDS b c d ((m + 1) * k + 1) * normEDS b c d ((m + 1) * k - 1) -
        compl
-/
def complEDS' : Nat -> R
  | 0 => 0
  | 1 => 1
  | (n + 2) => let m := n / 2 + 1
    if hn : Even n then complEDS' m * complEDS₂ b c d (m * k) else
      have : m + 1 < n + 2 :=
        add_lt_add_left (Nat.div_lt_self (Nat.not_even_iff_odd.mp hn).pos one_lt_two) 2
      complEDS' m ^ 2 * normEDS b c d ((m + 1) * k + 1) * normEDS b c d ((m + 1) * k - 1) -
        complEDS' (m + 1) ^ 2 * normEDS b c d (m * k + 1) * normEDS b c d (m * k - 1)

@[simp]
/--
lemma `complEDS'_zero` / 引理 `complEDS'_zero`

English:
lemma complEDS'_zero
  statement: complEDS' b c d k 0 = 0
  proof: by
  rw [complEDS']

@[simp]

中文:
引理 complEDS'_zero
  结论: complEDS' b c d k 0 = 0
  证明: by
  rw [complEDS']

@[simp]
-/
lemma complEDS'_zero : complEDS' b c d k 0 = 0 := by
  rw [complEDS']

@[simp]
/--
lemma `complEDS'_one` / 引理 `complEDS'_one`

English:
lemma complEDS'_one
  statement: complEDS' b c d k 1 = 1
  proof: by
  rw [complEDS']

中文:
引理 complEDS'_one
  结论: complEDS' b c d k 1 = 1
  证明: by
  rw [complEDS']
-/
lemma complEDS'_one : complEDS' b c d k 1 = 1 := by
  rw [complEDS']

/--
lemma `complEDS'_even` / 引理 `complEDS'_even`

English:
lemma complEDS'_even
  given: (m : Nat)
  statement: complEDS' b c d k (2 * (m + 1)) =
  proof: by
  rw [show 2 * (m + 1) = 2 * m + 2 by rfl]; rw [complEDS']; rw [dif_pos <| even_two_mul m]; rw [m.mul_div_cancel_left two_pos]; rw [Nat.cast_succ]

中文:
引理 complEDS'_even
  条件: (m : 自然数)
  结论: complEDS' b c d k (2 * (m + 1)) =
  证明: by
  rw [show 2 * (m + 1) = 2 * m + 2 by rfl]; rw [complEDS']; rw [dif_pos <| even_two_mul m]; rw [m.mul_div_cancel_left two_pos]; rw [Nat.cast_succ]
-/
lemma complEDS'_even (m : Nat) : complEDS' b c d k (2 * (m + 1)) =
    complEDS' b c d k (m + 1) * complEDS₂ b c d ((m + 1) * k) := by
  rw [show 2 * (m + 1) = 2 * m + 2 by rfl]; rw [complEDS']; rw [dif_pos <| even_two_mul m]; rw [m.mul_div_cancel_left two_pos]; rw [Nat.cast_succ]

/--
lemma `complEDS'_odd` / 引理 `complEDS'_odd`

English:
lemma complEDS'_odd
  given: (m : Nat)
  statement: complEDS' b c d k (2 * (m + 1) + 1) =
  proof: by
  rw [show 2 * (m + 1) + 1 = 2 * m + 3 by rfl]; rw [complEDS']; rw [dif_neg m.not_even_two_mul_add_one]
  simp [Nat.mul_add_div two_pos, add_assoc]

中文:
引理 complEDS'_odd
  条件: (m : 自然数)
  结论: complEDS' b c d k (2 * (m + 1) + 1) =
  证明: by
  rw [show 2 * (m + 1) + 1 = 2 * m + 3 by rfl]; rw [complEDS']; rw [dif_neg m.not_even_two_mul_add_one]
  simp [Nat.mul_add_div two_pos, add_assoc]
-/
lemma complEDS'_odd (m : Nat) : complEDS' b c d k (2 * (m + 1) + 1) =
    complEDS' b c d k (m + 1) ^ 2
        * normEDS b c d ((m + 2) * k + 1) * normEDS b c d ((m + 2) * k - 1) -
      complEDS' b c d k (m + 2) ^ 2
          * normEDS b c d ((m + 1) * k + 1) * normEDS b c d ((m + 1) * k - 1) := by
  rw [show 2 * (m + 1) + 1 = 2 * m + 3 by rfl]; rw [complEDS']; rw [dif_neg m.not_even_two_mul_add_one]
  simp [Nat.mul_add_div two_pos, add_assoc]

/--
Definition of `complEDS` / `complEDS` 的定义

English:
definition complEDS
  signature: (n : Int)
  body: n.sign * complEDS' b c d k n.natAbs

@[simp]

中文:
定义 complEDS
  签名: (n : 整数)
  定义体: n.sign * complEDS' b c d k n.natAbs

@[simp]

Depends on / 依赖: complEDS, n.natAbs, n.sign, natAbs
-/
def complEDS (n : Int) : R :=
  n.sign * complEDS' b c d k n.natAbs

@[simp]
/--
lemma `complEDS_ofNat` / 引理 `complEDS_ofNat`

English:
lemma complEDS_ofNat
  given: (n : Nat)
  statement: complEDS b c d k n = complEDS' b c d k n
  proof: by
  by_cases hn : n = 0
  · simp [hn, complEDS]
  · simp [complEDS, Int.sign_natCast_of_ne_zero hn]

@[simp]

中文:
引理 complEDS_ofNat
  条件: (n : 自然数)
  结论: complEDS b c d k n = complEDS' b c d k n
  证明: by
  by_cases hn : n = 0
  · simp [hn, complEDS]
  · simp [complEDS, Int.sign_natCast_of_ne_zero hn]

@[simp]

Depends on / 依赖: Int.sign_natCast_of_ne_zero, complEDS, sign_natCast_of_ne_zero
-/
lemma complEDS_ofNat (n : Nat) : complEDS b c d k n = complEDS' b c d k n := by
  by_cases hn : n = 0
  · simp [hn, complEDS]
  · simp [complEDS, Int.sign_natCast_of_ne_zero hn]

@[simp]
/--
lemma `complEDS_zero` / 引理 `complEDS_zero`

English:
lemma complEDS_zero
  statement: complEDS b c d k 0 = 0
  proof: by
  simp [complEDS]

@[simp]

中文:
引理 complEDS_zero
  结论: complEDS b c d k 0 = 0
  证明: by
  simp [complEDS]

@[simp]

Depends on / 依赖: complEDS
-/
lemma complEDS_zero : complEDS b c d k 0 = 0 := by
  simp [complEDS]

@[simp]
/--
lemma `complEDS_one` / 引理 `complEDS_one`

English:
lemma complEDS_one
  statement: complEDS b c d k 1 = 1
  proof: by
  simp [complEDS]

@[simp]

中文:
引理 complEDS_one
  结论: complEDS b c d k 1 = 1
  证明: by
  simp [complEDS]

@[simp]

Depends on / 依赖: complEDS
-/
lemma complEDS_one : complEDS b c d k 1 = 1 := by
  simp [complEDS]

@[simp]
/--
lemma `complEDS_neg` / 引理 `complEDS_neg`

English:
lemma complEDS_neg
  given: (n : Int)
  statement: complEDS b c d k (-n) = -complEDS b c d k n
  proof: by
  simp [complEDS]

中文:
引理 complEDS_neg
  条件: (n : 整数)
  结论: complEDS b c d k (-n) = -complEDS b c d k n
  证明: by
  simp [complEDS]

Depends on / 依赖: complEDS
-/
lemma complEDS_neg (n : Int) : complEDS b c d k (-n) = -complEDS b c d k n := by
  simp [complEDS]

/--
lemma `complEDS_even` / 引理 `complEDS_even`

English:
lemma complEDS_even
  given: (m : Int)
  proof: by
  induction m using Int.negInduction with
  | nat m =>
    rcases m with _ | _
    · simp
    norm_cast
    simpa only [complEDS_ofNat] using! complEDS'_even ..
  | neg ih => simp_rw [mul_neg, complEDS_neg, ih, neg_mul, complEDS₂_neg]

中文:
引理 complEDS_even
  条件: (m : 整数)
  证明: by
  induction m using Int.negInduction with
  | nat m =>
    rcases m with _ | _
    · simp
    norm_cast
    simpa only [complEDS_ofNat] using! complEDS'_even ..
  | neg ih => simp_rw [mul_neg, complEDS_neg, ih, neg_mul, complEDS₂_neg]

Depends on / 依赖: Int.negInduction, _even, complEDS, complEDS_neg, complEDS_ofNat, mul_neg, negInduction, neg_mul, simp_rw
-/
lemma complEDS_even (m : Int) :
    complEDS b c d k (2 * m) = complEDS b c d k m * complEDS₂ b c d (m * k) := by
  induction m using Int.negInduction with
  | nat m =>
    rcases m with _ | _
    · simp
    norm_cast
    simpa only [complEDS_ofNat] using! complEDS'_even ..
  | neg ih => simp_rw [mul_neg, complEDS_neg, ih, neg_mul, complEDS₂_neg]

/--
lemma `complEDS_odd` / 引理 `complEDS_odd`

English:
lemma complEDS_odd
  given: (m : Int)
  statement: complEDS b c d k (2 * m + 1) =
  proof: by
  induction m using Int.negInduction with
  | nat m =>
    rcases m with _ | _
    · simp
    norm_cast
    simpa only [complEDS_ofNat] using! complEDS'_odd ..
  | neg ih m =>
    rcases m with _ | m
    · simp
    simp_rw [Nat.cast_succ, show 2 * -(m + 1 : Int) + 1 = -(2 * m + 1) by rfl,
      s

中文:
引理 complEDS_odd
  条件: (m : 整数)
  结论: complEDS b c d k (2 * m + 1) =
  证明: by
  induction m using Int.negInduction with
  | nat m =>
    rcases m with _ | _
    · simp
    norm_cast
    simpa only [complEDS_ofNat] using! complEDS'_odd ..
  | neg ih m =>
    rcases m with _ | m
    · simp
    simp_rw [Nat.cast_succ, show 2 * -(m + 1 : Int) + 1 = -(2 * m + 1) by rfl,
      s

Depends on / 依赖: Int.negInduction, Nat.cast_succ, _odd, cast_succ, complEDS, complEDS_neg, complEDS_ofNat, negInduction, neg_add, neg_mul, neg_sub, normEDS_neg, simp_rw, sub_neg_eq_add
-/
lemma complEDS_odd (m : Int) : complEDS b c d k (2 * m + 1) =
    complEDS b c d k m ^ 2 * normEDS b c d ((m + 1) * k + 1) * normEDS b c d ((m + 1) * k - 1) -
      complEDS b c d k (m + 1) ^ 2 * normEDS b c d (m * k + 1) * normEDS b c d (m * k - 1) := by
  induction m using Int.negInduction with
  | nat m =>
    rcases m with _ | _
    · simp
    norm_cast
    simpa only [complEDS_ofNat] using! complEDS'_odd ..
  | neg ih m =>
    rcases m with _ | m
    · simp
    simp_rw [Nat.cast_succ, show 2 * -(m + 1 : Int) + 1 = -(2 * m + 1) by rfl,
      show (-(m + 1 : Int) + 1) = -m by ring1, neg_mul, ← sub_neg_eq_add, ← neg_sub', sub_neg_eq_add,
      ← neg_add', complEDS_neg, normEDS_neg, ih]
    ring1

/-- Strong recursion principle for the complement sequence for a normalised EDS: if we have
* `P 0`, `P 1`,
* for all `m : ℕ` we can prove `P (2 * (m + 3))` from `P k` for all `k < 2 * (m + 3)`, and
* for all `m : ℕ` we can prove `P (2 * (m + 2) + 1)` from `P k` for all `k < 2 * (m + 2) + 1`,

then we have `P n` for all `n : ℕ`. -/
@[elab_as_elim]
/--
Definition of `complEDSRec'` / `complEDSRec'` 的定义

English:
definition complEDSRec'
  signature: {P : Nat -> Sort*} (zero : P 0) (one : P 1)
  body: n.evenOddStrongRec (by rintro (_ | _) h; exacts [zero, even _ h])
    (by rintro (_ | _) h; exacts [one, odd _ h])

中文:
定义 complEDSRec'
  签名: {P : 自然数 -> Sort*} (zero : P 0) (one : P 1)
  定义体: n.evenOddStrongRec (by rintro (_ | _) h; exacts [zero, even _ h])
    (by rintro (_ | _) h; exacts [one, odd _ h])

Depends on / 依赖: evenOddStrongRec, exacts, n.evenOddStrongRec
-/
noncomputable def complEDSRec' {P : Nat -> Sort*} (zero : P 0) (one : P 1)
    (even : forall m : Nat, (forall k < 2 * (m + 1), P k) -> P (2 * (m + 1)))
    (odd : forall m : Nat, (forall k < 2 * (m + 1) + 1, P k) -> P (2 * (m + 1) + 1)) (n : Nat) : P n :=
  n.evenOddStrongRec (by rintro (_ | _) h; exacts [zero, even _ h])
    (by rintro (_ | _) h; exacts [one, odd _ h])

/-- Recursion principle for the complement sequence for a normalised EDS: if we have
* `P 0`, `P 1`,
* for all `m : ℕ` we can prove `P (2 * (m + 3))` from `P (m + 1)`, `P (m + 2)`, `P (m + 3)`,
  `P (m + 4)`, and `P (m + 5)`, and
* for all `m : ℕ` we can prove `P (2 * (m + 2) + 1)` from `P (m + 1)`, `P (m + 2)`, `P (m + 3)`,
  and `P (m + 4)`,

then we have `P n` for all `n : ℕ`. -/
@[elab_as_elim]
/--
Definition of `complEDSRec` / `complEDSRec` 的定义

English:
definition complEDSRec
  signature: {P : Nat -> Sort*} (zero : P 0) (one : P 1)
  body: complEDSRec' zero one (fun _ ih => even _ <| ih _ <| by linarith only)
    (fun _ ih => odd _ (ih _ <| by linarith only) <| ih _ <| by linarith only) n

中文:
定义 complEDSRec
  签名: {P : 自然数 -> Sort*} (zero : P 0) (one : P 1)
  定义体: complEDSRec' zero one (fun _ ih => even _ <| ih _ <| by linarith only)
    (fun _ ih => odd _ (ih _ <| by linarith only) <| ih _ <| by linarith only) n

Depends on / 依赖: complEDSRec
-/
noncomputable def complEDSRec {P : Nat -> Sort*} (zero : P 0) (one : P 1)
    (even : forall m : Nat, P (m + 1) -> P (2 * (m + 1)))
    (odd : forall m : Nat, P (m + 1) -> P (m + 2) -> P (2 * (m + 1) + 1)) (n : Nat) : P n :=
  complEDSRec' zero one (fun _ ih => even _ <| ih _ <| by linarith only)
    (fun _ ih => odd _ (ih _ <| by linarith only) <| ih _ <| by linarith only) n

end ComplEDS

section Map

@[simp]
/--
lemma `map_preNormEDS'` / 引理 `map_preNormEDS'`

English:
lemma map_preNormEDS'
  given: (n : Nat)
  statement: f (preNormEDS' b c d n) = preNormEDS' (f b) (f c) (f d) n
  proof: by
  induction n using normEDSRec' with
  | zero => simp
  | one => simp
  | two => simp
  | three => simp
  | four => simp
  | _ _ ih =>
    simp only [preNormEDS'_even, preNormEDS'_odd, apply_ite f, map_pow, map_mul, map_sub, map_one]
    repeat rw [ih _ <| by linarith only]

@[simp]

中文:
引理 map_preNormEDS'
  条件: (n : 自然数)
  结论: f (preNormEDS' b c d n) = preNormEDS' (f b) (f c) (f d) n
  证明: by
  induction n using normEDSRec' with
  | zero => simp
  | one => simp
  | two => simp
  | three => simp
  | four => simp
  | _ _ ih =>
    simp only [preNormEDS'_even, preNormEDS'_odd, apply_ite f, map_pow, map_mul, map_sub, map_one]
    repeat rw [ih _ <| by linarith only]

@[simp]

Depends on / 依赖: _even, _odd, apply_ite, map_mul, map_one, map_pow, map_sub, normEDSRec, preNormEDS, repeat
-/
lemma map_preNormEDS' (n : Nat) : f (preNormEDS' b c d n) = preNormEDS' (f b) (f c) (f d) n := by
  induction n using normEDSRec' with
  | zero => simp
  | one => simp
  | two => simp
  | three => simp
  | four => simp
  | _ _ ih =>
    simp only [preNormEDS'_even, preNormEDS'_odd, apply_ite f, map_pow, map_mul, map_sub, map_one]
    repeat rw [ih _ <| by linarith only]

@[simp]
/--
lemma `map_preNormEDS` / 引理 `map_preNormEDS`

English:
lemma map_preNormEDS
  given: (n : Int)
  statement: f (preNormEDS b c d n) = preNormEDS (f b) (f c) (f d) n
  proof: by
  simp [preNormEDS]

@[simp]

中文:
引理 map_preNormEDS
  条件: (n : 整数)
  结论: f (preNormEDS b c d n) = preNormEDS (f b) (f c) (f d) n
  证明: by
  simp [preNormEDS]

@[simp]

Depends on / 依赖: preNormEDS
-/
lemma map_preNormEDS (n : Int) : f (preNormEDS b c d n) = preNormEDS (f b) (f c) (f d) n := by
  simp [preNormEDS]

@[simp]
/--
lemma `map_complEDS₂` / 引理 `map_complEDS₂`

English:
lemma map_complEDS₂
  given: (n : Int)
  statement: f (complEDS₂ b c d n) = complEDS₂ (f b) (f c) (f d) n
  proof: by
  simp [complEDS₂, apply_ite f]

@[simp]

中文:
引理 map_complEDS₂
  条件: (n : 整数)
  结论: f (complEDS₂ b c d n) = complEDS₂ (f b) (f c) (f d) n
  证明: by
  simp [complEDS₂, apply_ite f]

@[simp]

Depends on / 依赖: apply_ite
-/
lemma map_complEDS₂ (n : Int) : f (complEDS₂ b c d n) = complEDS₂ (f b) (f c) (f d) n := by
  simp [complEDS₂, apply_ite f]

@[simp]
/--
lemma `map_normEDS` / 引理 `map_normEDS`

English:
lemma map_normEDS
  given: (n : Int)
  statement: f (normEDS b c d n) = normEDS (f b) (f c) (f d) n
  proof: by
  simp [normEDS, apply_ite f]

@[simp]

中文:
引理 map_normEDS
  条件: (n : 整数)
  结论: f (normEDS b c d n) = normEDS (f b) (f c) (f d) n
  证明: by
  simp [normEDS, apply_ite f]

@[simp]

Depends on / 依赖: apply_ite, normEDS
-/
lemma map_normEDS (n : Int) : f (normEDS b c d n) = normEDS (f b) (f c) (f d) n := by
  simp [normEDS, apply_ite f]

@[simp]
/--
lemma `map_complEDS'` / 引理 `map_complEDS'`

English:
lemma map_complEDS'
  given: (k : Int) (n : Nat)
  proof: by
  induction n using complEDSRec' with
  | zero => simp
  | one => simp
  | _ _ ih =>
    simp only [complEDS'_even, complEDS'_odd, map_normEDS, map_complEDS₂, map_pow, map_mul, map_sub]
    repeat rw [ih _ <| by linarith only]

@[simp]

中文:
引理 map_complEDS'
  条件: (k : 整数) (n : 自然数)
  证明: by
  induction n using complEDSRec' with
  | zero => simp
  | one => simp
  | _ _ ih =>
    simp only [complEDS'_even, complEDS'_odd, map_normEDS, map_complEDS₂, map_pow, map_mul, map_sub]
    repeat rw [ih _ <| by linarith only]

@[simp]

Depends on / 依赖: _even, _odd, complEDS, complEDSRec, map_mul, map_normEDS, map_pow, map_sub, repeat
-/
lemma map_complEDS' (k : Int) (n : Nat) :
    f (complEDS' b c d k n) = complEDS' (f b) (f c) (f d) k n := by
  induction n using complEDSRec' with
  | zero => simp
  | one => simp
  | _ _ ih =>
    simp only [complEDS'_even, complEDS'_odd, map_normEDS, map_complEDS₂, map_pow, map_mul, map_sub]
    repeat rw [ih _ <| by linarith only]

@[simp]
/--
lemma `map_complEDS` / 引理 `map_complEDS`

English:
lemma map_complEDS
  given: (k n : Int)
  statement: f (complEDS b c d k n) = complEDS (f b) (f c) (f d) k n
  proof: by
  simp [complEDS]

中文:
引理 map_complEDS
  条件: (k n : 整数)
  结论: f (complEDS b c d k n) = complEDS (f b) (f c) (f d) k n
  证明: by
  simp [complEDS]

Depends on / 依赖: complEDS
-/
lemma map_complEDS (k n : Int) : f (complEDS b c d k n) = complEDS (f b) (f c) (f d) k n := by
  simp [complEDS]

end Map
