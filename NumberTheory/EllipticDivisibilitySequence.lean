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

variable {R S : Type*} [CommRing R] [CommRing S] (W : ℤ → R) {F : Type*} [FunLike F R S]
  [RingHomClass F R S] (f : F)

namespace IsEllipticNet

/-- The elliptic atom `Wₐ(a, b)` that defines an elliptic net. Note that this is defined in terms of
truncated integer division, and hence should only be used when `a` and `b` have the same parity. -/
/-
**IsEllipticNet.atom** 是 Mathlib 中的一个定义，位于命名空间 `IsEllipticNet`。
形式化陈述：atom (a b : Int) : R
参数：a b : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The elliptic atom `Wₐ(a, b)` that defines an elliptic net. Note that this is def
ined in terms of
truncated integer division, and hence should only be used when `a` and `b` have 
the same parity.
-/
def atom (a b : ℤ) : R :=
  W ((a + b).tdiv 2) * W ((a - b).tdiv 2)

@[simp]
/-
**IsEllipticNet.atom_same** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
形式化陈述：atom_same (a : Int) : atom W a a = W a * W 0
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsEllipticNet.atom.eq_1`：∀ {R : Type u_1} [inst : CommRing R] (W : ℤ → R
) (a b : ℤ),   IsEllipticNet.atom W a b = W ((a + b).tdiv 2) * W ((a - b).tdiv 2
)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Int.mul_tdiv_cancel_left`：∀ {a : ℤ} (b : ℤ), a ≠ 0 → (a * b).tdiv a = b
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Int.zero_tdiv`：∀ (b : ℤ), Int.tdiv 0 b = 0
-/
lemma atom_same (a : ℤ) : atom W a a = W a * W 0 := by
  rw [atom, ← two_mul, Int.mul_tdiv_cancel_left _ two_ne_zero, sub_self, Int.zero_tdiv]

variable {W} in
@[simp]
/-
**IsEllipticNet.neg_atom** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
形式化陈述：neg_atom (odd : W.Odd) (a b : Int) : -atom W a b = atom W b a
参数：odd : W.Odd；a b : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsEllipticNet.atom.eq_1`：∀ {R : Type u_1} [inst : CommRing R] (W : ℤ → R
) (a b : ℤ),   IsEllipticNet.atom W a b = W ((a + b).tdiv 2) * W ((a - b).tdiv 2
)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `Int.neg_tdiv`：∀ (a b : ℤ), (-a).tdiv b = -a.tdiv b
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
-/
lemma neg_atom (odd : W.Odd) (a b : ℤ) : -atom W a b = atom W b a := by
  rw [atom, atom, add_comm, ← neg_sub a, Int.neg_tdiv, odd, mul_neg]

variable {W} in
/-
**IsEllipticNet.atom_mul_atom** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
形式化陈述：atom_mul_atom (odd : W.Odd) (a b c d : Int) : atom W a b * atom W c d = at
om W b a * atom W d c
参数：odd : W.Odd；a b c d : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsEllipticNet.neg_atom`：neg_atom (odd : W.Odd) (a b : Int) : -atom W a b
 = atom W b a
· 使用定理 `neg_mul_neg`：neg_mul_neg (a b : α) : -a * -b = a * b
-/
lemma atom_mul_atom (odd : W.Odd) (a b c d : ℤ) :
    atom W a b * atom W c d = atom W b a * atom W d c := by
  rw [← neg_atom odd a b, ← neg_atom odd c d, neg_mul_neg]

variable {W} in
@[simp]
/-
**IsEllipticNet.atom_neg_left** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
形式化陈述：atom_neg_left (odd : W.Odd) (a b : Int) : atom W (-a) b = atom W a b
参数：odd : W.Odd；a b : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsEllipticNet.atom.eq_1`：∀ {R : Type u_1} [inst : CommRing R] (W : ℤ → R
) (a b : ℤ),   IsEllipticNet.atom W a b = W ((a + b).tdiv 2) * W ((a - b).tdiv 2
)
· 使用定理 `neg_add_eq_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), -a + b = b - a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `neg_add'`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α), -
(a + b) = -a - b
· 使用定理 `Int.neg_tdiv`：∀ (a b : ℤ), (-a).tdiv b = -a.tdiv b
· 使用定理 `neg_mul_neg`：neg_mul_neg (a b : α) : -a * -b = a * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma atom_neg_left (odd : W.Odd) (a b : ℤ) : atom W (-a) b = atom W a b := by
  rw [atom, atom, neg_add_eq_sub, ← neg_sub a, ← neg_add', Int.neg_tdiv, odd, Int.neg_tdiv, odd,
    neg_mul_neg, mul_comm]

@[simp]
/-
**IsEllipticNet.atom_neg_right** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
形式化陈述：atom_neg_right (a b : Int) : atom W a (-b) = atom W a b
参数：a b : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma atom_neg_right (a b : ℤ) : atom W a (-b) = atom W a b := by
  simp_rw [atom, ← sub_eq_add_neg, sub_neg_eq_add, mul_comm]

variable {W} in
@[simp]
/-
**IsEllipticNet.atom_abs_left** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
形式化陈述：atom_abs_left (odd : W.Odd) (a b : Int) : atom W |a| b = atom W a b
参数：odd : W.Odd；a b : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_choice`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α
] (x : α), |x| = x ∨ |x| = -x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `IsEllipticNet.atom_neg_left`：atom_neg_left (odd : W.Odd) (a b : Int) : a
tom W (-a) b = atom W a b
-/
lemma atom_abs_left (odd : W.Odd) (a b : ℤ) : atom W |a| b = atom W a b := by
  rcases abs_choice a with h | h <;> simp only [h, atom_neg_left odd]

@[simp]
/-
**IsEllipticNet.atom_abs_right** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
形式化陈述：atom_abs_right (a b : Int) : atom W a |b| = atom W a b
参数：a b : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_choice`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α
] (x : α), |x| = x ∨ |x| = -x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `IsEllipticNet.atom_neg_right`：atom_neg_right (a b : Int) : atom W a (-b)
 = atom W a b
-/
lemma atom_abs_right (a b : ℤ) : atom W a |b| = atom W a b := by
  rcases abs_choice b with h | h <;> simp only [h, atom_neg_right]
/-
**IsEllipticNet.atom_even** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
形式化陈述：atom_even (a b : Int) : atom W (2 * a) (2 * b) = W (a + b) * W (a - b)
参数：a b : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.mul_tdiv_cancel_left`：∀ {a : ℤ} (b : ℤ), a ≠ 0 → (a * b).tdiv a = b
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma atom_even (a b : ℤ) : atom W (2 * a) (2 * b) = W (a + b) * W (a - b) := by
  simp_rw [atom, ← mul_add, ← mul_sub, Int.mul_tdiv_cancel_left _ two_ne_zero]
/-
**IsEllipticNet.atom_odd** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
形式化陈述：atom_odd (a b : Int) : atom W (2 * a + 1) (2 * b + 1) = W (a + b + 1) * W 
(a - b)
参数：a b : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_sub_add_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b
 c d : α), a + b - (c + d) = a - c + (b - d)
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.mul_tdiv_cancel_left`：∀ {a : ℤ} (b : ℤ), a ≠ 0 → (a * b).tdiv a = b
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma atom_odd (a b : ℤ) : atom W (2 * a + 1) (2 * b + 1) = W (a + b + 1) * W (a - b) := by
  simp_rw [atom, add_add_add_comm _ (1 : ℤ), ← two_mul, ← mul_add, add_sub_add_comm, sub_self,
    add_zero, ← mul_sub, Int.mul_tdiv_cancel_left _ two_ne_zero]
/-
**IsEllipticNet.map_atom** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
形式化陈述：map_atom (a b : Int) : f (atom W a b) = atom (f ∘ W) a b
参数：a b : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_atom (a b : ℤ) : f (atom W a b) = atom (f ∘ W) a b := by
  simp_rw [atom, map_mul, Function.comp]

/-- The elliptic relator `ERₐ(a, b, c, d)` obtained by a change of variables in `ER(p, q, r, s)`
(see `IsEllipticNet.rel_eq` and `IsEllipticNet.atomRel_eq`). Note that this is defined in terms of
elliptic atoms, and hence should only be used when `a`, `b`, `c`, and `d` have the same parity. -/
/-
**IsEllipticNet.atomRel** 是 Mathlib 中的一个定义，位于命名空间 `IsEllipticNet`。
形式化陈述：atomRel (a b c d : Int) : R
参数：a b c d : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The elliptic relator `ERₐ(a, b, c, d)` obtained by a change of variables in `ER(
p, q, r, s)`
(see `IsEllipticNet.rel_eq` and `IsEllipticNet.atomRel_eq`). Note that this is d
efined in terms of
elliptic atoms, and hence should only be used when `a`, `b`, `c`, and `d` have t
he same parity.
-/
def atomRel (a b c d : ℤ) : R :=
  atom W a b * atom W c d - atom W a c * atom W b d + atom W a d * atom W b c

@[simp]
/-
**IsEllipticNet.atomRel_same** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma atomRel_same₁₂ (a b c : ℤ) : atomRel W a a b c = W a * W 0 * atom W b c := by
  simp_rw [atomRel, atom_same, mul_comm <| atom W a b, sub_add_cancel]

variable {W} in
@[simp]
/-
**IsEllipticNet.atomRel_same** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma atomRel_same₁₃ (odd : W.Odd) (a b c : ℤ) : atomRel W a b a c = W a * W 0 * atom W c b := by
  linear_combination (norm := (simp_rw [atomRel, atom_same]; ring1))
    W a * W 0 * neg_atom odd c b - atom W a c * neg_atom odd a b

variable {W} in
@[simp]
/-
**IsEllipticNet.atomRel_same** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma atomRel_same₁₄ (odd : W.Odd) (a b c : ℤ) : atomRel W a b c a = W a * W 0 * atom W b c := by
  simp_rw [atomRel, atom_mul_atom odd a b, mul_comm <| atom W b a, sub_self, zero_add, atom_same]

@[simp]
/-
**IsEllipticNet.atomRel_same** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma atomRel_same₂₃ (a b c : ℤ) : atomRel W a b b c = W b * W 0 * atom W a c := by
  simp_rw [atomRel, atom_same, sub_self, zero_add, mul_comm]

variable {W} in
@[simp]
/-
**IsEllipticNet.atomRel_same** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma atomRel_same₂₄ (odd : W.Odd) (a b c : ℤ) : atomRel W a b c b = W b * W 0 * atom W c a := by
  linear_combination (norm := (simp_rw [atomRel, atom_same]; ring1))
    W b * W 0 * neg_atom odd a c - atom W a b * neg_atom odd b c

@[simp]
/-
**IsEllipticNet.atomRel_same** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma atomRel_same₃₄ (a b c : ℤ) : atomRel W a b c c = W c * W 0 * atom W a b := by
  simp_rw [atomRel, atom_same, mul_comm, sub_add_cancel]

variable {W} in
@[simp]
/-
**IsEllipticNet.atomRel_neg** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma atomRel_neg₁ (odd : W.Odd) (a b c d : ℤ) : atomRel W (-a) b c d = atomRel W a b c d := by
  simp_rw [atomRel, atom_neg_left odd]

variable {W} in
@[simp]
/-
**IsEllipticNet.atomRel_neg** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma atomRel_neg₂ (odd : W.Odd) (a b c d : ℤ) : atomRel W a (-b) c d = atomRel W a b c d := by
  simp_rw [atomRel, atom_neg_left odd, atom_neg_right]

variable {W} in
@[simp]
/-
**IsEllipticNet.atomRel_neg** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma atomRel_neg₃ (odd : W.Odd) (a b c d : ℤ) : atomRel W a b (-c) d = atomRel W a b c d := by
  simp_rw [atomRel, atom_neg_left odd, atom_neg_right]

@[simp]
/-
**IsEllipticNet.atomRel_neg** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma atomRel_neg₄ (a b c d : ℤ) : atomRel W a b c (-d) = atomRel W a b c d := by
  simp_rw [atomRel, atom_neg_right]

variable {W} in
@[simp]
/-
**IsEllipticNet.atomRel_abs** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma atomRel_abs₁ (odd : W.Odd) (a b c d : ℤ) : atomRel W |a| b c d = atomRel W a b c d := by
  simp_rw [atomRel, atom_abs_left odd]

variable {W} in
@[simp]
/-
**IsEllipticNet.atomRel_abs** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma atomRel_abs₂ (odd : W.Odd) (a b c d : ℤ) : atomRel W a |b| c d = atomRel W a b c d := by
  simp_rw [atomRel, atom_abs_left odd, atom_abs_right]

variable {W} in
@[simp]
/-
**IsEllipticNet.atomRel_abs** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma atomRel_abs₃ (odd : W.Odd) (a b c d : ℤ) : atomRel W a b |c| d = atomRel W a b c d := by
  simp_rw [atomRel, atom_abs_left odd, atom_abs_right]

@[simp]
/-
**IsEllipticNet.atomRel_abs** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma atomRel_abs₄ (a b c d : ℤ) : atomRel W a b c |d| = atomRel W a b c d := by
  simp_rw [atomRel, atom_abs_right]
/-
**IsEllipticNet.atomRel_avg_sub** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
形式化陈述：atomRel_avg_sub {a b c d : Int} (parity : d % 2 = a % 2 ∧ d % 2 = b % 2 ∧ 
d % 2 = c % 2) : atomRel W ((a + b + c + d) / 2 - d) ((a + b + c + d) / 2 - c) (
(a + b + c + d) / 2 - b) ((a + b + c + d) / 2 - a) = atomRel W a b c d
参数：parity : d % 2 = a % 2 ∧ d % 2 = b % 2 ∧ d % 2 = c % 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `sub_add_sub_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b
 c d : α), a - b + (c - d) = a + c - (b + d)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Int.mul_ediv_cancel'`：∀ {a b : ℤ}, a ∣ b → a * (b / a) = b
-/
lemma atomRel_avg_sub {a b c d : ℤ} (parity : d % 2 = a % 2 ∧ d % 2 = b % 2 ∧ d % 2 = c % 2) :
    atomRel W ((a + b + c + d) / 2 - d) ((a + b + c + d) / 2 - c) ((a + b + c + d) / 2 - b)
      ((a + b + c + d) / 2 - a) = atomRel W a b c d := by
  simp_rw [add_assoc <| a + b, atomRel, atom, sub_add_sub_comm, ← two_mul]
  repeat rw [Int.mul_ediv_cancel'] <;> grind
/-
**IsEllipticNet.map_atomRel** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
形式化陈述：map_atomRel (a b c d : Int) : f (atomRel W a b c d) = atomRel (f ∘ W) a b 
c d
参数：a b c d : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `IsEllipticNet.map_atom`：map_atom (a b : Int) : f (atom W a b) = atom (f 
∘ W) a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_atomRel (a b c d : ℤ) : f (atomRel W a b c d) = atomRel (f ∘ W) a b c d := by
  simp_rw [atomRel, map_add, map_sub, map_mul, map_atom]

/-- The elliptic relator `ER(p, q, r, s)` that defines an elliptic net. -/
/-
**IsEllipticNet.rel** 是 Mathlib 中的一个定义，位于命名空间 `IsEllipticNet`。
形式化陈述：rel (p q r s : Int) : R
参数：p q r s : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The elliptic relator `ER(p, q, r, s)` that defines an elliptic net.
-/
def rel (p q r s : ℤ) : R :=
  W (p + q + s) * W (p - q) * W (r + s) * W r - W (p + r + s) * W (p - r) * W (q + s) * W q +
    W (q + r + s) * W (q - r) * W (p + s) * W p
/-
**IsEllipticNet.rel_eq** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
形式化陈述：rel_eq (p q r s : Int) : rel W p q r s = atomRel W (2 * p + s) (2 * q + s)
 (2 * r + s) s
参数：p q r s : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_sub_add_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b
 c d : α), a + b - (c + d) = a - c + (b - d)
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Int.mul_tdiv_cancel_left`：∀ {a : ℤ} (b : ℤ), a ≠ 0 → (a * b).tdiv a = b
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rel_eq (p q r s : ℤ) : rel W p q r s = atomRel W (2 * p + s) (2 * q + s) (2 * r + s) s := by
  simp_rw [rel, atomRel, atom, add_add_add_comm _ s, add_assoc _ s, ← two_mul, ← mul_add,
    add_sub_add_comm, add_sub_assoc, sub_self, add_zero, ← mul_sub,
    Int.mul_tdiv_cancel_left _ two_ne_zero, mul_comm <| _ * W p, mul_assoc]
/-
**IsEllipticNet.atomRel_two_mul** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
形式化陈述：atomRel_two_mul (a b c d : Int) : atomRel W (2 * a) (2 * b) (2 * c) (2 * d
) = rel W (a - d) (b - d) (c - d) (2 * d)
参数：a b c d : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsEllipticNet.rel_eq`：rel_eq (p q r s : Int) : rel W p q r s = atomRel W
 (2 * p + s) (2 * q + s) (2 * r + s) s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma atomRel_two_mul (a b c d : ℤ) :
    atomRel W (2 * a) (2 * b) (2 * c) (2 * d) = rel W (a - d) (b - d) (c - d) (2 * d) := by
  simp_rw [rel_eq, mul_sub, sub_add_cancel]
/-
**IsEllipticNet.atomRel_eq** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
形式化陈述：atomRel_eq {a b c d : Int} (parity : d % 2 = a % 2 ∧ d % 2 = b % 2 ∧ d % 2
 = c % 2) : atomRel W a b c d = rel W ((a - d) / 2) ((b - d) / 2) ((c - d) / 2) 
d
参数：parity : d % 2 = a % 2 ∧ d % 2 = b % 2 ∧ d % 2 = c % 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsEllipticNet.rel_eq`：rel_eq (p q r s : Int) : rel W p q r s = atomRel W
 (2 * p + s) (2 * q + s) (2 * r + s) s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.mul_ediv_cancel'`：∀ {a b : ℤ}, a ∣ b → a * (b / a) = b
· 使用定理 `Int.ModEq.dvd`：∀ {n a b : ℤ}, a ≡ b [ZMOD n] → n ∣ b - a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma atomRel_eq {a b c d : ℤ} (parity : d % 2 = a % 2 ∧ d % 2 = b % 2 ∧ d % 2 = c % 2) :
    atomRel W a b c d = rel W ((a - d) / 2) ((b - d) / 2) ((c - d) / 2) d := by
  simp only [rel_eq, Int.mul_ediv_cancel', Int.ModEq.dvd parity.1, Int.ModEq.dvd parity.2.1,
    Int.ModEq.dvd parity.2.2, sub_add_cancel]

variable {W} in
@[simp]
/-
**IsEllipticNet.rel_neg** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
形式化陈述：rel_neg (odd : W.Odd) (p q r s : Int) : rel W (-p) (-q) (-r) (-s) = rel W 
p q r s
参数：odd : W.Odd；p q r s : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsEllipticNet.rel_eq`：rel_eq (p q r s : Int) : rel W p q r s = atomRel W
 (2 * p + s) (2 * q + s) (2 * r + s) s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用引理 `IsEllipticNet.atomRel_neg₁`：atomRel_neg₁ (odd : W.Odd) (a b c d : Int) :
 atomRel W (-a) b c d = atomRel W a b c d
· 使用引理 `IsEllipticNet.atomRel_neg₂`：atomRel_neg₂ (odd : W.Odd) (a b c d : Int) :
 atomRel W a (-b) c d = atomRel W a b c d
· 使用引理 `IsEllipticNet.atomRel_neg₃`：atomRel_neg₃ (odd : W.Odd) (a b c d : Int) :
 atomRel W a b (-c) d = atomRel W a b c d
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `IsEllipticNet.atomRel_neg₄`：atomRel_neg₄ (a b c d : Int) : atomRel W a b
 c (-d) = atomRel W a b c d
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rel_neg (odd : W.Odd) (p q r s : ℤ) : rel W (-p) (-q) (-r) (-s) = rel W p q r s := by
  simp_rw [rel_eq, mul_neg, ← neg_add, atomRel_neg₁ odd, atomRel_neg₂ odd, atomRel_neg₃ odd,
    atomRel_neg₄]

/-- The even elliptic relator `ER(m + 1, m - 1, 1, 0)` for `m ∈ ℤ`. -/
/-
**IsEllipticNet.rel_even** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
形式化陈述：rel_even (m : Int) : rel W (m + 1) (m - 1) 1 0 = W (2 * m) * W 2 * W 1 ^ 2
 - W (m - 1) ^ 2 * W m * W (m + 2) + W (m - 2) * W m * W (m + 1) ^ 2
参数：m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsEllipticNet.rel.eq_1`：∀ {R : Type u_1} [inst : CommRing R] (W : ℤ → R)
 (p q r s : ℤ),   IsEllipticNet.rel W p q r s =     W (p + q + s) * W (p - q) * 
W (r + s) * …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf'`：∀ {R : Type u_1} [inst : CommSemiri
ng R] {a a' b : R},   a = a' → ∀ {e : ℕ}, Nat.rawCast 1 = e → a' ^ e * Nat.rawCa
st 1 = b → a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf`：∀ {R : Type u_1} [inst : Comm
Semiring R] {a b c : R} (x : R) (e : ℕ), a + b = c → x ^ e * a + x ^ e * b = x ^
 e * c
（共 62 条，此处仅展示前 30 条）

--- 原说明 ---
The even elliptic relator `ER(m + 1, m - 1, 1, 0)` for `m ∈ ℤ`.
-/
lemma rel_even (m : ℤ) : rel W (m + 1) (m - 1) 1 0 = W (2 * m) * W 2 * W 1 ^ 2 -
    W (m - 1) ^ 2 * W m * W (m + 2) + W (m - 2) * W m * W (m + 1) ^ 2 := by
  rw [rel]
  ring_nf

/-- The odd elliptic relator `ER(m + 1, m, 1, 0)` for `m ∈ ℤ`. -/
/-
**IsEllipticNet.rel_odd** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
形式化陈述：rel_odd (m : Int) : rel W (m + 1) m 1 0 = W (2 * m + 1) * W 1 ^ 3 - W (m +
 2) * W m ^ 3 + W (m - 1) * W (m + 1) ^ 3
参数：m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsEllipticNet.rel.eq_1`：∀ {R : Type u_1} [inst : CommRing R] (W : ℤ → R)
 (p q r s : ℤ),   IsEllipticNet.rel W p q r s =     W (p + q + s) * W (p - q) * 
W (r + s) * …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf'`：∀ {R : Type u_1} [inst : CommSemiri
ng R] {a a' b : R},   a = a' → ∀ {e : ℕ}, Nat.rawCast 1 = e → a' ^ e * Nat.rawCa
st 1 = b → a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf`：∀ {R : Type u_1} [inst : Comm
Semiring R] {a b c : R} (x : R) (e : ℕ), a + b = c → x ^ e * a + x ^ e * b = x ^
 e * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Tactic.RingNF.add_assoc_rev`：add_assoc_rev (a b c : R) : a + (b 
+ c) = a + b + c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Tactic.RingNF.nat_rawCast_1`：nat_rawCast_1 : (Nat.rawCast 1 : R)
 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
（共 62 条，此处仅展示前 30 条）

--- 原说明 ---
The odd elliptic relator `ER(m + 1, m, 1, 0)` for `m ∈ ℤ`.
-/
lemma rel_odd (m : ℤ) : rel W (m + 1) m 1 0 =
    W (2 * m + 1) * W 1 ^ 3 - W (m + 2) * W m ^ 3 + W (m - 1) * W (m + 1) ^ 3 := by
  rw [rel]
  ring_nf
/-
**IsEllipticNet.map_rel** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
形式化陈述：map_rel (p q r s : Int) : f (rel W p q r s) = rel (f ∘ W) p q r s
参数：p q r s : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_rel (p q r s : ℤ) : f (rel W p q r s) = rel (f ∘ W) p q r s := by
  simp_rw [rel, map_add, map_sub, map_mul, Function.comp]

end IsEllipticNet

/-- The proposition that a sequence indexed by `ℤ` is an elliptic net. -/
/-
**IsEllipticNet** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsEllipticNet : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposition that a sequence indexed by `ℤ` is an elliptic net.
-/
def IsEllipticNet : Prop :=
  ∀ p q r s : ℤ, IsEllipticNet.rel W p q r s = 0

/-- The proposition that a sequence indexed by `ℤ` is an elliptic sequence. -/
/-
**IsEllipticSequence** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsEllipticSequence : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposition that a sequence indexed by `ℤ` is an elliptic sequence.
-/
def IsEllipticSequence : Prop :=
  ∀ p q r : ℤ, IsEllipticNet.rel W p q r 0 = 0

@[deprecated (since := "2026-07-01")] alias IsEllSequence := IsEllipticSequence

/-- The proposition that a sequence indexed by `ℤ` is an EDS. -/
/-
**IsEllipticDvdSequence** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsEllipticDvdSequence : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposition that a sequence indexed by `ℤ` is an EDS.
-/
def IsEllipticDvdSequence : Prop :=
  IsEllipticSequence W ∧ IsDvdSequence W

@[deprecated (since := "2026-06-30")] alias IsEllDivSequence := IsEllipticDvdSequence

namespace IsEllipticNet

variable {W}

/-
**IsEllipticNet.isEllipticSequence** 是 Mathlib 中的一个引理，位于命名空间 `IsEllipticNet`。
形式化陈述：isEllipticSequence (h : IsEllipticNet W) : IsEllipticSequence W
参数：h : IsEllipticNet W。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isEllipticSequence (h : IsEllipticNet W) : IsEllipticSequence W :=
  (h · · · 0)
/-
**IsEllipticNet.id** 是 Mathlib 中的一个定理，位于命名空间 `IsEllipticNet`。
形式化陈述：IsEllipticNet id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
（共 37 条，此处仅展示前 30 条）
-/
protected lemma id : IsEllipticNet (id : ℤ → ℤ) :=
  fun _ _ _ _ ↦ by simp_rw [rel, id_eq]; ring1
/-
**IsEllipticNet.smul** 是 Mathlib 中的一个定理，位于命名空间 `IsEllipticNet`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {W : ℤ → R}, IsEllipticNet W → ∀ (x :
 R), IsEllipticNet (x • W)
参数：x : R；x • W。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.LinearCombination.mul_const_eq`：mul_const_eq [Mul α] (p :
 b = c) (a : α) : a * b = a * c
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
（共 48 条，此处仅展示前 30 条）
-/
protected lemma smul (h : IsEllipticNet W) (x : R) : IsEllipticNet <| x • W := fun p q r s ↦ by
  linear_combination (norm := (simp_rw [rel, Pi.smul_apply, smul_eq_mul]; ring1)) x ^ 4 * h p q r s

end IsEllipticNet

namespace IsEllipticSequence

variable {W}

/-
**IsEllipticSequence.id** 是 Mathlib 中的一个定理，位于命名空间 `IsEllipticSequence`。
形式化陈述：IsEllipticSequence id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsEllipticNet.isEllipticSequence`：isEllipticSequence (h : IsEllipticNet 
W) : IsEllipticSequence W
· 使用定理 `IsEllipticNet.id`：IsEllipticNet id
-/
protected lemma id : IsEllipticSequence (id : ℤ → ℤ) :=
  IsEllipticNet.id.isEllipticSequence
/-
**IsEllipticSequence.smul** 是 Mathlib 中的一个定理，位于命名空间 `IsEllipticSequence`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {W : ℤ → R}, IsEllipticSequence W → ∀
 (x : R), IsEllipticSequence (x • W)
参数：x : R；x • W。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.LinearCombination.mul_const_eq`：mul_const_eq [Mul α] (p :
 b = c) (a : α) : a * b = a * c
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
（共 54 条，此处仅展示前 30 条）
-/
protected lemma smul (h : IsEllipticSequence W) (x : R) : IsEllipticSequence <| x • W :=
  fun p q r ↦ by linear_combination (norm := (simp [IsEllipticNet.rel]; ring1)) x ^ 4 * h p q r

end IsEllipticSequence

@[deprecated (since := "2026-07-01")] alias isEllSequence_id := IsEllipticSequence.id
@[deprecated (since := "2026-07-01")] alias IsEllSequence.smul := IsEllipticSequence.smul

namespace IsEllipticDvdSequence

variable {W}

/-- The identity sequence is an EDS. -/
/-
**IsEllipticDvdSequence.id** 是 Mathlib 中的一个定理，位于命名空间 `IsEllipticDvdSequence`。
形式化陈述：IsEllipticDvdSequence id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsEllipticSequence.id`：IsEllipticSequence id
· 使用定理 `IsDvdSequence.id`：∀ (α : Type u_1) [inst : Dvd α], IsDvdSequence id

--- 原说明 ---
The identity sequence is an EDS.
-/
protected theorem id : IsEllipticDvdSequence (id : ℤ → ℤ) :=
  ⟨IsEllipticSequence.id, .id ℤ⟩
/-
**IsEllipticDvdSequence.smul** 是 Mathlib 中的一个定理，位于命名空间 `IsEllipticDvdSequence`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {W : ℤ → R}, IsEllipticDvdSequence W 
→ ∀ (x : R), IsEllipticDvdSequence (x • W)
参数：x : R；x • W。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsEllipticSequence.smul`：∀ {R : Type u_1} [inst : CommRing R] {W : ℤ → R
}, IsEllipticSequence W → ∀ (x : R), IsEllipticSequence (x • W)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsDvdSequence.smul`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst
 : Dvd α] [inst_1 : Monoid β] [inst_2 : Monoid γ] {f : α → γ}   [inst_3 : SMul β
 γ] [IsS…
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected lemma smul (h : IsEllipticDvdSequence W) (x : R) : IsEllipticDvdSequence <| x • W :=
  ⟨h.left.smul x, h.right.smul x⟩

end IsEllipticDvdSequence

@[deprecated (since := "2026-06-30")] alias isEllDivSequence_id := IsEllipticDvdSequence.id
@[deprecated (since := "2026-06-30")] alias IsEllDivSequence.smul := IsEllipticDvdSequence.smul

variable (b c d : R)

section PreNormEDS

/-- The auxiliary sequence for a normalised EDS `W : ℕ → R`, with initial values
`W(0) = 0`, `W(1) = 1`, `W(2) = 1`, `W(3) = c`, and `W(4) = d` and extra parameter `b`. -/
/-
**preNormEDS'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：preNormEDS' : Nat -> R | 0 => 0 | 1 => 1 | 2 => 1 | 3 => c | 4 => d | (n +
 5) => let m
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The auxiliary sequence for a normalised EDS `W : ℕ → R`, with initial values
`W(0) = 0`, `W(1) = 1`, `W(2) = 1`, `W(3) = c`, and `W(4) = d` and extra paramet
er `b`.
-/
def preNormEDS' : ℕ → R
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
/-
**preNormEDS'_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (b c d : R), preNormEDS' b c d 0 = 0
参数：b c d : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `preNormEDS'.eq_1`：∀ {R : Type u_1} [inst : CommRing R] (b c d : R), preN
ormEDS' b c d 0 = 0
-/
lemma preNormEDS'_zero : preNormEDS' b c d 0 = 0 := by
  rw [preNormEDS']

@[simp]
/-
**preNormEDS'_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (b c d : R), preNormEDS' b c d 1 = 1
参数：b c d : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `preNormEDS'.eq_2`：∀ {R : Type u_1} [inst : CommRing R] (b c d : R), preN
ormEDS' b c d 1 = 1
-/
lemma preNormEDS'_one : preNormEDS' b c d 1 = 1 := by
  rw [preNormEDS']

@[simp]
/-
**preNormEDS'_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (b c d : R), preNormEDS' b c d 2 = 1
参数：b c d : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `preNormEDS'.eq_3`：∀ {R : Type u_1} [inst : CommRing R] (b c d : R), preN
ormEDS' b c d 2 = 1
-/
lemma preNormEDS'_two : preNormEDS' b c d 2 = 1 := by
  rw [preNormEDS']

@[simp]
/-
**preNormEDS'_three** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (b c d : R), preNormEDS' b c d 3 = c
参数：b c d : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `preNormEDS'.eq_4`：∀ {R : Type u_1} [inst : CommRing R] (b c d : R), preN
ormEDS' b c d 3 = c
-/
lemma preNormEDS'_three : preNormEDS' b c d 3 = c := by
  rw [preNormEDS']

@[simp]
/-
**preNormEDS'_four** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (b c d : R), preNormEDS' b c d 4 = d
参数：b c d : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `preNormEDS'.eq_5`：∀ {R : Type u_1} [inst : CommRing R] (b c d : R), preN
ormEDS' b c d 4 = d
-/
lemma preNormEDS'_four : preNormEDS' b c d 4 = d := by
  rw [preNormEDS']
/-
**preNormEDS'_even** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (m : ℕ),   preNormEDS' b 
c d (2 * (m + 3)) =     preNormEDS' b c d (m + 2) ^ 2 * preNormEDS' b c d (m + 3
) * preNormEDS' b c d (m + 5) -       preNormEDS' b c d (m + 1) * preNormEDS' b 
c d (m + 3) * preNormEDS' b c d (m + 4) ^ 2
参数：b c d : R；m : ℕ；2 * (m + 3)；m + 2；m + 3；m + 5；m + 1；m + 3；m + 4。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `preNormEDS'.eq_6`：∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (n : 
ℕ),   preNormEDS' b c d n.succ.succ.succ.succ.succ =     if hn : Even n then    
   (pr…
· 使用引理 `Nat.not_even_two_mul_add_one`：not_even_two_mul_add_one (n : Nat) : ¬ Eve
n (2 * n + 1)
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.mul_add_div`：∀ {m : ℕ}, m > 0 → ∀ (x y : ℕ), (m * x + y) / m = x + y
 / m
· 使用定理 `two_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preNormEDS'_even (m : ℕ) : preNormEDS' b c d (2 * (m + 3)) =
    preNormEDS' b c d (m + 2) ^ 2 * preNormEDS' b c d (m + 3) * preNormEDS' b c d (m + 5) -
      preNormEDS' b c d (m + 1) * preNormEDS' b c d (m + 3) * preNormEDS' b c d (m + 4) ^ 2 := by
  rw [show 2 * (m + 3) = 2 * m + 1 + 5 by rfl, preNormEDS', dif_neg m.not_even_two_mul_add_one]
  simp [Nat.mul_add_div two_pos]
/-
**preNormEDS'_odd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (m : ℕ),   preNormEDS' b 
c d (2 * (m + 2) + 1) =     (preNormEDS' b c d (m + 4) * preNormEDS' b c d (m + 
2) ^ 3 * if Even m then b else 1) -       preNormEDS' b c d (m + 1) * preNormEDS
' b c d (m + 3) ^ 3 * if Even m then 1 else b
参数：b c d : R；m : ℕ；2 * (m + 2) + 1；preNormEDS' b c d (m + 4) * preNormEDS' b c d
 (m + 2) ^ 3 * if Even m then b else 1；m + 1；m + 3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `preNormEDS'.eq_6`：∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (n : 
ℕ),   preNormEDS' b c d n.succ.succ.succ.succ.succ =     if hn : Even n then    
   (pr…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用定理 `Nat.mul_div_cancel_left`：∀ (m : ℕ) {n : ℕ}, 0 < n → n * m / n = m
· 使用定理 `two_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma preNormEDS'_odd (m : ℕ) : preNormEDS' b c d (2 * (m + 2) + 1) =
    preNormEDS' b c d (m + 4) * preNormEDS' b c d (m + 2) ^ 3 * (if Even m then b else 1) -
      preNormEDS' b c d (m + 1) * preNormEDS' b c d (m + 3) ^ 3 * (if Even m then 1 else b) := by
  rw [show 2 * (m + 2) + 1 = 2 * m + 5 by rfl, preNormEDS', dif_pos <| even_two_mul m,
    m.mul_div_cancel_left two_pos]

/-- The auxiliary sequence for a normalised EDS `W : ℤ → R`, with initial values
`W(0) = 0`, `W(1) = 1`, `W(2) = 1`, `W(3) = c`, and `W(4) = d` and extra parameter `b`.

This extends `preNormEDS'` by defining its values at negative integers. -/
/-
**preNormEDS** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：preNormEDS (n : Int) : R
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The auxiliary sequence for a normalised EDS `W : ℤ → R`, with initial values
`W(0) = 0`, `W(1) = 1`, `W(2) = 1`, `W(3) = c`, and `W(4) = d` and extra paramet
er `b`.

This extends `preNormEDS'` by defining its values at negative integers.
-/
def preNormEDS (n : ℤ) : R :=
  n.sign * preNormEDS' b c d n.natAbs

@[simp]
/-
**preNormEDS_ofNat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：preNormEDS_ofNat (n : Nat) : preNormEDS b c d n = preNormEDS' b c d n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `preNormEDS'_zero`：∀ {R : Type u_1} [inst : CommRing R] (b c d : R), preN
ormEDS' b c d 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.sign_natCast_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → (↑n).sign = 1
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma preNormEDS_ofNat (n : ℕ) : preNormEDS b c d n = preNormEDS' b c d n := by
  by_cases hn : n = 0
  · simp [hn, preNormEDS]
  · simp [preNormEDS, Int.sign_natCast_of_ne_zero hn]

@[simp]
/-
**preNormEDS_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：preNormEDS_zero : preNormEDS b c d 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `preNormEDS'_zero`：∀ {R : Type u_1} [inst : CommRing R] (b c d : R), preN
ormEDS' b c d 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preNormEDS_zero : preNormEDS b c d 0 = 0 := by
  simp [preNormEDS]

@[simp]
/-
**preNormEDS_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：preNormEDS_one : preNormEDS b c d 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Int.natAbs_of_isUnit`：∀ {u : ℤ}, IsUnit u → u.natAbs = 1
· 使用定理 `preNormEDS'_one`：∀ {R : Type u_1} [inst : CommRing R] (b c d : R), preNo
rmEDS' b c d 1 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preNormEDS_one : preNormEDS b c d 1 = 1 := by
  simp [preNormEDS]

@[simp]
/-
**preNormEDS_two** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：preNormEDS_two : preNormEDS b c d 2 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.sign_eq_one_of_pos`：∀ {a : ℤ}, 0 < a → a.sign = 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `preNormEDS'_two`：∀ {R : Type u_1} [inst : CommRing R] (b c d : R), preNo
rmEDS' b c d 2 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preNormEDS_two : preNormEDS b c d 2 = 1 := by
  simp [preNormEDS, Int.sign_eq_one_of_pos]

@[simp]
/-
**preNormEDS_three** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：preNormEDS_three : preNormEDS b c d 3 = c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.sign_eq_one_of_pos`：∀ {a : ℤ}, 0 < a → a.sign = 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `preNormEDS'_three`：∀ {R : Type u_1} [inst : CommRing R] (b c d : R), pre
NormEDS' b c d 3 = c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preNormEDS_three : preNormEDS b c d 3 = c := by
  simp [preNormEDS, Int.sign_eq_one_of_pos]

@[simp]
/-
**preNormEDS_four** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：preNormEDS_four : preNormEDS b c d 4 = d
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.sign_eq_one_of_pos`：∀ {a : ℤ}, 0 < a → a.sign = 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `preNormEDS'_four`：∀ {R : Type u_1} [inst : CommRing R] (b c d : R), preN
ormEDS' b c d 4 = d
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preNormEDS_four : preNormEDS b c d 4 = d := by
  simp [preNormEDS, Int.sign_eq_one_of_pos]

@[simp]
/-
**preNormEDS_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：preNormEDS_neg (n : Int) : preNormEDS b c d (-n) = -preNormEDS b c d n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.sign_neg`：∀ (z : ℤ), (-z).sign = -z.sign
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.natAbs_neg`：∀ (a : ℤ), (-a).natAbs = a.natAbs
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preNormEDS_neg (n : ℤ) : preNormEDS b c d (-n) = -preNormEDS b c d n := by
  simp [preNormEDS]
/-
**preNormEDS_even** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：preNormEDS_even (m : Int) : preNormEDS b c d (2 * m) = preNormEDS b c d (m
 - 1) ^ 2 * preNormEDS b c d m * preNormEDS b c d (m + 2) - preNormEDS b c d (m 
- 2) * preNormEDS b c d m * preNormEDS b c d (m + 1) ^ 2
参数：m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `preNormEDS_zero`：preNormEDS_zero : preNormEDS b c d 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用引理 `preNormEDS_neg`：preNormEDS_neg (n : Int) : preNormEDS b c d (-n) = -preN
ormEDS b c d n
· 使用引理 `preNormEDS_one`：preNormEDS_one : preNormEDS b c d 1 = 1
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `preNormEDS_two`：preNormEDS_two : preNormEDS b c d 2 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `preNormEDS_three`：preNormEDS_three : preNormEDS b c d 3 = c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用引理 `preNormEDS_four`：preNormEDS_four : preNormEDS b c d 4 = d
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
（共 75 条，此处仅展示前 30 条）
-/
lemma preNormEDS_even (m : ℤ) : preNormEDS b c d (2 * m) =
    preNormEDS b c d (m - 1) ^ 2 * preNormEDS b c d m * preNormEDS b c d (m + 2) -
      preNormEDS b c d (m - 2) * preNormEDS b c d m * preNormEDS b c d (m + 1) ^ 2 := by
  induction m using Int.negInduction with
  | nat m =>
    rcases m with _ | _ | _ | m
    iterate 3 simp
    simp_rw [Nat.cast_succ, Int.add_sub_cancel, show (m : ℤ) + 1 + 1 + 1 = m + 1 + 2 by rfl,
      Int.add_sub_cancel]
    norm_cast
    simpa only [preNormEDS_ofNat] using preNormEDS'_even ..
  | neg ih m =>
    simp_rw [mul_neg, ← sub_neg_eq_add, ← neg_sub', ← neg_add', preNormEDS_neg, ih]
    ring1
/-
**preNormEDS_odd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：preNormEDS_odd (m : Int) : preNormEDS b c d (2 * m + 1) = preNormEDS b c d
 (m + 2) * preNormEDS b c d m ^ 3 * (if Even m then b else 1) - preNormEDS b c d
 (m - 1) * preNormEDS b c d (m + 1) ^ 3 * (if Even m then 1 else b)
参数：m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `preNormEDS_one`：preNormEDS_one : preNormEDS b c d 1 = 1
· 使用引理 `preNormEDS_two`：preNormEDS_two : preNormEDS b c d 2 = 1
· 使用引理 `preNormEDS_zero`：preNormEDS_zero : preNormEDS b c d 0 = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用引理 `preNormEDS_neg`：preNormEDS_neg (n : Int) : preNormEDS b c d (-n) = -preN
ormEDS b c d n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `preNormEDS_three`：preNormEDS_three : preNormEDS b c d 3 = c
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
（共 80 条，此处仅展示前 30 条）
-/
lemma preNormEDS_odd (m : ℤ) : preNormEDS b c d (2 * m + 1) =
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
    simp_rw [Nat.cast_succ, show 2 * -(m + 1 : ℤ) + 1 = -(2 * m + 1) by rfl,
      show -(m + 1 : ℤ) + 2 = -(m - 1) by ring1, show -(m + 1 : ℤ) - 1 = -(m + 2) by rfl,
      show -(m + 1 : ℤ) + 1 = -m by ring1, preNormEDS_neg, even_neg, Int.even_add_one, ite_not, ih]
    ring1

/-- The 2-complement sequence `Wᶜ₂ : ℤ → R` for a normalised EDS `W : ℤ → R` that witnesses
`W(k) ∣ W(2 * k)`. In other words, `W(k) * Wᶜ₂(k) = W(2 * k)` for all `k ∈ ℤ`.

This is defined in terms of `preNormEDS`. -/
/-
**complEDS** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：complEDS (n : Int) : R
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The 2-complement sequence `Wᶜ₂ : ℤ → R` for a normalised EDS `W : ℤ → R` that wi
tnesses
`W(k) ∣ W(2 * k)`. In other words, `W(k) * Wᶜ₂(k) = W(2 * k)` for all `k ∈ ℤ`.

This is defined in terms of `preNormEDS`.
-/
def complEDS₂ (k : ℤ) : R :=
  (preNormEDS (b ^ 4) c d (k - 1) ^ 2 * preNormEDS (b ^ 4) c d (k + 2) -
    preNormEDS (b ^ 4) c d (k - 2) * preNormEDS (b ^ 4) c d (k + 1) ^ 2) * if Even k then 1 else b

@[simp]
/-
**complEDS** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：complEDS (n : Int) : R
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma complEDS₂_zero : complEDS₂ b c d 0 = 2 := by
  simp [complEDS₂, one_add_one_eq_two]

@[simp]
/-
**complEDS** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：complEDS (n : Int) : R
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma complEDS₂_one : complEDS₂ b c d 1 = b := by
  simp [complEDS₂]

@[simp]
/-
**complEDS** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：complEDS (n : Int) : R
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma complEDS₂_two : complEDS₂ b c d 2 = d := by
  simp [complEDS₂]

@[simp]
/-
**complEDS** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：complEDS (n : Int) : R
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma complEDS₂_three : complEDS₂ b c d 3 = preNormEDS (b ^ 4) c d 5 * b - d ^ 2 * b := by
  simp [complEDS₂, if_neg (by decide : ¬Even (3 : ℤ)), sub_mul]

@[simp]
/-
**complEDS** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：complEDS (n : Int) : R
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma complEDS₂_four : complEDS₂ b c d 4 =
    c ^ 2 * preNormEDS (b ^ 4) c d 6 - preNormEDS (b ^ 4) c d 5 ^ 2 := by
  simp [complEDS₂, if_pos (by decide : Even (4 : ℤ))]

@[simp]
/-
**complEDS** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：complEDS (n : Int) : R
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma complEDS₂_neg (k : ℤ) : complEDS₂ b c d (-k) = complEDS₂ b c d k := by
  simp_rw [complEDS₂, ← neg_add', ← sub_neg_eq_add, ← neg_sub', preNormEDS_neg, even_neg]
  ring1
/-
**preNormEDS_mul_complEDS** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma preNormEDS_mul_complEDS₂ (k : ℤ) : preNormEDS (b ^ 4) c d k * complEDS₂ b c d k =
    preNormEDS (b ^ 4) c d (2 * k) * if Even k then 1 else b := by
  rw [complEDS₂, preNormEDS_even]
  ring1

end PreNormEDS

section NormEDS

/-- The canonical example of a normalised EDS `W : ℤ → R`, with initial values
`W(0) = 0`, `W(1) = 1`, `W(2) = b`, `W(3) = c`, and `W(4) = d * b`.

This is defined in terms of `preNormEDS` whose even terms differ by a factor of `b`. -/
/-
**normEDS** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：normEDS (n : Int) : R
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical example of a normalised EDS `W : ℤ → R`, with initial values
`W(0) = 0`, `W(1) = 1`, `W(2) = b`, `W(3) = c`, and `W(4) = d * b`.

This is defined in terms of `preNormEDS` whose even terms differ by a factor of 
`b`.
-/
def normEDS (n : ℤ) : R :=
  preNormEDS (b ^ 4) c d n * if Even n then b else 1

@[simp]
/-
**normEDS_ofNat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：normEDS_ofNat (n : Nat) : normEDS b c d n = preNormEDS' (b ^ 4) c d n * if
 Even n then b else 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `preNormEDS_ofNat`：preNormEDS_ofNat (n : Nat) : preNormEDS b c d n = preN
ormEDS' b c d n
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma normEDS_ofNat (n : ℕ) :
    normEDS b c d n = preNormEDS' (b ^ 4) c d n * if Even n then b else 1 := by
  simp [normEDS]

@[simp]
/-
**normEDS_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：normEDS_zero : normEDS b c d 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `preNormEDS_zero`：preNormEDS_zero : preNormEDS b c d 0 = 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma normEDS_zero : normEDS b c d 0 = 0 := by
  simp [normEDS]

@[simp]
/-
**normEDS_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：normEDS_one : normEDS b c d 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `preNormEDS_one`：preNormEDS_one : preNormEDS b c d 1 = 1
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma normEDS_one : normEDS b c d 1 = 1 := by
  simp [normEDS]

@[simp]
/-
**normEDS_two** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：normEDS_two : normEDS b c d 2 = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `preNormEDS_two`：preNormEDS_two : preNormEDS b c d 2 = 1
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma normEDS_two : normEDS b c d 2 = b := by
  simp [normEDS]

@[simp]
/-
**normEDS_three** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：normEDS_three : normEDS b c d 3 = c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `preNormEDS_three`：preNormEDS_three : preNormEDS b c d 3 = c
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma normEDS_three : normEDS b c d 3 = c := by
  simp [normEDS, show ¬Even (3 : ℤ) by decide]

@[simp]
/-
**normEDS_four** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：normEDS_four : normEDS b c d 4 = d * b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `preNormEDS_four`：preNormEDS_four : preNormEDS b c d 4 = d
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
lemma normEDS_four : normEDS b c d 4 = d * b := by
  simp [normEDS, show ¬Odd (4 : ℤ) by decide]

@[simp]
/-
**normEDS_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：normEDS_neg (n : Int) : normEDS b c d (-n) = -normEDS b c d n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `preNormEDS_neg`：preNormEDS_neg (n : Int) : preNormEDS b c d (-n) = -preN
ormEDS b c d n
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma normEDS_neg (n : ℤ) : normEDS b c d (-n) = -normEDS b c d n := by
  simp_rw [normEDS, preNormEDS_neg, even_neg, neg_mul]
/-
**normEDS_mul_complEDS** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma normEDS_mul_complEDS₂ (k : ℤ) :
    normEDS b c d k * complEDS₂ b c d k = normEDS b c d (2 * k) := by
  simp_rw [normEDS, mul_right_comm, preNormEDS_mul_complEDS₂, mul_assoc, apply_ite₂, one_mul,
    mul_one, ite_self, if_pos <| even_two_mul k]
/-
**normEDS_dvd_normEDS_two_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：normEDS_dvd_normEDS_two_mul (k : Int) : normEDS b c d k ∣ normEDS b c d (2
 * k)
参数：k : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `normEDS_mul_complEDS₂`：normEDS_mul_complEDS₂ (k : Int) : normEDS b c d k
 * complEDS₂ b c d k = normEDS b c d (2 * k)
-/
lemma normEDS_dvd_normEDS_two_mul (k : ℤ) : normEDS b c d k ∣ normEDS b c d (2 * k) :=
  ⟨complEDS₂ .., (normEDS_mul_complEDS₂ ..).symm⟩
/-
**complEDS** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：complEDS (n : Int) : R
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma complEDS₂_mul_b (k : ℤ) : complEDS₂ b c d k * b =
    normEDS b c d (k - 1) ^ 2 * normEDS b c d (k + 2) -
      normEDS b c d (k - 2) * normEDS b c d (k + 1) ^ 2 := by
  simp_rw [complEDS₂, normEDS, Int.even_add, Int.even_sub, even_two, iff_true, Int.not_even_one,
    iff_false]
  split_ifs <;> ring1
/-
**normEDS_even** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：normEDS_even (m : Int) : normEDS b c d (2 * m) * b = normEDS b c d (m - 1)
 ^ 2 * normEDS b c d m * normEDS b c d (m + 2) - normEDS b c d (m - 2) * normEDS
 b c d m * normEDS b c d (m + 1) ^ 2
参数：m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `normEDS_mul_complEDS₂`：normEDS_mul_complEDS₂ (k : Int) : normEDS b c d k
 * complEDS₂ b c d k = normEDS b c d (2 * k)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `complEDS₂_mul_b`：complEDS₂_mul_b (k : Int) : complEDS₂ b c d k * b = nor
mEDS b c d (k - 1) ^ 2 * normEDS b c d (k + 2) - normEDS b c d (k - 2) * normEDS
 b c …
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
（共 38 条，此处仅展示前 30 条）
-/
lemma normEDS_even (m : ℤ) : normEDS b c d (2 * m) * b =
    normEDS b c d (m - 1) ^ 2 * normEDS b c d m * normEDS b c d (m + 2) -
      normEDS b c d (m - 2) * normEDS b c d m * normEDS b c d (m + 1) ^ 2 := by
  rw [← normEDS_mul_complEDS₂, mul_assoc, complEDS₂_mul_b]
  ring1
/-
**normEDS_odd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：normEDS_odd (m : Int) : normEDS b c d (2 * m + 1) = normEDS b c d (m + 2) 
* normEDS b c d m ^ 3 - normEDS b c d (m - 1) * normEDS b c d (m + 1) ^ 3
参数：m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `preNormEDS_odd`：preNormEDS_odd (m : Int) : preNormEDS b c d (2 * m + 1) 
= preNormEDS b c d (m + 2) * preNormEDS b c d m ^ 3 * (if Even m then b else 1) 
- pr…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `Int.not_even_two_mul_add_one`：not_even_two_mul_add_one (n : Int) : ¬ Eve
n (2 * n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `not_not_intro`：∀ {p : Prop}, p → ¬¬p
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
（共 48 条，此处仅展示前 30 条）
-/
lemma normEDS_odd (m : ℤ) : normEDS b c d (2 * m + 1) =
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
/-
**normEDSRec'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：normEDSRec' {P : Nat -> Sort*} (zero : P 0) (one : P 1) (two : P 2) (three
 : P 3) (four : P 4) (even : forall m : Nat, (forall k < 2 * (m + 3), P k) -> P 
(2 * (m + 3))) (odd : forall m : Nat, (forall k < 2 * (m + 2) + 1, P k) -> P (2 
* (m + 2) + 1)) (n : Nat) : P n
参数：zero : P 0；one : P 1；two : P 2；three : P 3；four : P 4；even : forall m : Nat, 
(forall k < 2 * (m + 3), P k) -> P (2 * (m + 3))；odd : forall m : Nat, (forall k
 < 2 * (m + 2) + 1, P k) -> P (2 * (m + 2) + 1)；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Strong recursion principle for a normalised EDS: if we have
* `P 0`, `P 1`, `P 2`, `P 3`, and `P 4`,
* for all `m : ℕ` we can prove `P (2 * (m + 3))` from `P k` for all `k < 2 * (m 
+ 3)`, and
* for all `m : ℕ` we can prove `P (2 * (m + 2) + 1)` from `P k` for all `k < 2 *
 (m + 2) + 1`,

then we have `P n` for all `n : ℕ`.
-/
noncomputable def normEDSRec' {P : ℕ → Sort*}
    (zero : P 0) (one : P 1) (two : P 2) (three : P 3) (four : P 4)
    (even : ∀ m : ℕ, (∀ k < 2 * (m + 3), P k) → P (2 * (m + 3)))
    (odd : ∀ m : ℕ, (∀ k < 2 * (m + 2) + 1, P k) → P (2 * (m + 2) + 1)) (n : ℕ) : P n :=
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
/-
**normEDSRec** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：normEDSRec {P : Nat -> Sort*} (zero : P 0) (one : P 1) (two : P 2) (three 
: P 3) (four : P 4) (even : forall m : Nat, P (m + 1) -> P (m + 2) -> P (m + 3) 
-> P (m + 4) -> P (m + 5) -> P (2 * (m + 3))) (odd : forall m : Nat, P (m + 1) -
> P (m + 2) -> P (m + 3) -> P (m + 4) -> P (2 * (m + 2) + 1)) (n : Nat) : P n
参数：zero : P 0；one : P 1；two : P 2；three : P 3；four : P 4；even : forall m : Nat, 
P (m + 1) -> P (m + 2) -> P (m + 3) -> P (m + 4) -> P (m + 5) -> P (2 * (m + 3))
；odd : forall m : Nat, P (m + 1) -> P (m + 2) -> P (m + 3) -> P (m + 4) -> P (2 
* (m + 2) + 1)；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recursion principle for a normalised EDS: if we have
* `P 0`, `P 1`, `P 2`, `P 3`, and `P 4`,
* for all `m : ℕ` we can prove `P (2 * (m + 3))` from `P (m + 1)`, `P (m + 2)`, 
`P (m + 3)`,
  `P (m + 4)`, and `P (m + 5)`, and
* for all `m : ℕ` we can prove `P (2 * (m + 2) + 1)` from `P (m + 1)`, `P (m + 2
)`, `P (m + 3)`,
  and `P (m + 4)`,

then we have `P n` for all `n : ℕ`.
-/
noncomputable def normEDSRec {P : ℕ → Sort*}
    (zero : P 0) (one : P 1) (two : P 2) (three : P 3) (four : P 4)
    (even : ∀ m : ℕ, P (m + 1) → P (m + 2) → P (m + 3) → P (m + 4) → P (m + 5) → P (2 * (m + 3)))
    (odd : ∀ m : ℕ, P (m + 1) → P (m + 2) → P (m + 3) → P (m + 4) → P (2 * (m + 2) + 1)) (n : ℕ) :
    P n :=
  normEDSRec' zero one two three four (fun _ ih ↦ by apply even <;> exact ih _ <| by linarith only)
    (fun _ ih ↦ by apply odd <;> exact ih _ <| by linarith only) n

end NormEDS

section ComplEDS

variable (k : ℤ)

/-- The complement sequence `Wᶜ : ℤ × ℕ → R` for a normalised EDS `W : ℤ → R` that witnesses
`W(k) ∣ W(n * k)`. In other words, `W(k) * Wᶜ(k, n) = W(n * k)` for all `k, n ∈ ℤ`.

This is defined in terms of `normEDS` and agrees with `complEDS₂` when `n = 2`. -/
/-
**complEDS'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：complEDS' : Nat -> R | 0 => 0 | 1 => 1 | (n + 2) => let m
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The complement sequence `Wᶜ : ℤ × ℕ → R` for a normalised EDS `W : ℤ → R` that w
itnesses
`W(k) ∣ W(n * k)`. In other words, `W(k) * Wᶜ(k, n) = W(n * k)` for all `k, n ∈ 
ℤ`.

This is defined in terms of `normEDS` and agrees with `complEDS₂` when `n = 2`.
-/
def complEDS' : ℕ → R
  | 0 => 0
  | 1 => 1
  | (n + 2) => let m := n / 2 + 1
    if hn : Even n then complEDS' m * complEDS₂ b c d (m * k) else
      have : m + 1 < n + 2 :=
        add_lt_add_left (Nat.div_lt_self (Nat.not_even_iff_odd.mp hn).pos one_lt_two) 2
      complEDS' m ^ 2 * normEDS b c d ((m + 1) * k + 1) * normEDS b c d ((m + 1) * k - 1) -
        complEDS' (m + 1) ^ 2 * normEDS b c d (m * k + 1) * normEDS b c d (m * k - 1)

@[simp]
/-
**complEDS'_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (k : ℤ), complEDS' b c d 
k 0 = 0
参数：b c d : R；k : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `complEDS'.eq_1`：∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (k : ℤ)
, complEDS' b c d k 0 = 0
-/
lemma complEDS'_zero : complEDS' b c d k 0 = 0 := by
  rw [complEDS']

@[simp]
/-
**complEDS'_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (k : ℤ), complEDS' b c d 
k 1 = 1
参数：b c d : R；k : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `complEDS'.eq_2`：∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (k : ℤ)
, complEDS' b c d k 1 = 1
-/
lemma complEDS'_one : complEDS' b c d k 1 = 1 := by
  rw [complEDS']
/-
**complEDS'_even** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (k : ℤ) (m : ℕ),   complE
DS' b c d k (2 * (m + 1)) = complEDS' b c d k (m + 1) * complEDS₂ b c d ((↑m + 1
) * k)
参数：b c d : R；k : ℤ；m : ℕ；2 * (m + 1)；m + 1；(↑m + 1) * k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `complEDS'.eq_3`：∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (k : ℤ)
 (n : ℕ),   complEDS' b c d k n.succ.succ =     if hn : Even n then complEDS' b 
c d …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用定理 `Nat.mul_div_cancel_left`：∀ (m : ℕ) {n : ℕ}, 0 < n → n * m / n = m
· 使用定理 `two_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
-/
lemma complEDS'_even (m : ℕ) : complEDS' b c d k (2 * (m + 1)) =
    complEDS' b c d k (m + 1) * complEDS₂ b c d ((m + 1) * k) := by
  rw [show 2 * (m + 1) = 2 * m + 2 by rfl, complEDS', dif_pos <| even_two_mul m,
    m.mul_div_cancel_left two_pos, Nat.cast_succ]
/-
**complEDS'_odd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (k : ℤ) (m : ℕ),   complE
DS' b c d k (2 * (m + 1) + 1) =     complEDS' b c d k (m + 1) ^ 2 * normEDS b c 
d ((↑m + 2) * k + 1) * normEDS b c d ((↑m + 2) * k - 1) -       complEDS' b c d 
k (m + 2) ^ 2 * normEDS b c d ((↑m + 1) * k + 1) * normEDS b c d ((↑m + 1) * k -
 1)
参数：b c d : R；k : ℤ；m : ℕ；2 * (m + 1) + 1；m + 1；(↑m + 2) * k + 1；(↑m + 2) * k - 1
；m + 2；(↑m + 1) * k + 1；(↑m + 1) * k - 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `complEDS'.eq_3`：∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (k : ℤ)
 (n : ℕ),   complEDS' b c d k n.succ.succ =     if hn : Even n then complEDS' b 
c d …
· 使用引理 `Nat.not_even_two_mul_add_one`：not_even_two_mul_add_one (n : Nat) : ¬ Eve
n (2 * n + 1)
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.mul_add_div`：∀ {m : ℕ}, m > 0 → ∀ (x y : ℕ), (m * x + y) / m = x + y
 / m
· 使用定理 `two_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma complEDS'_odd (m : ℕ) : complEDS' b c d k (2 * (m + 1) + 1) =
    complEDS' b c d k (m + 1) ^ 2
        * normEDS b c d ((m + 2) * k + 1) * normEDS b c d ((m + 2) * k - 1) -
      complEDS' b c d k (m + 2) ^ 2
          * normEDS b c d ((m + 1) * k + 1) * normEDS b c d ((m + 1) * k - 1) := by
  rw [show 2 * (m + 1) + 1 = 2 * m + 3 by rfl, complEDS', dif_neg m.not_even_two_mul_add_one]
  simp [Nat.mul_add_div two_pos, add_assoc]

/-- The complement sequence `Wᶜ : ℤ × ℤ → R` for a normalised EDS `W : ℤ → R` that witnesses
`W(k) ∣ W(n * k)`. In other words, `W(k) * Wᶜ(k, n) = W(n * k)` for all `k, n ∈ ℤ`.

This extends `complEDS'` by defining its values at negative integers. -/
/-
**complEDS** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：complEDS (n : Int) : R
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The complement sequence `Wᶜ : ℤ × ℤ → R` for a normalised EDS `W : ℤ → R` that w
itnesses
`W(k) ∣ W(n * k)`. In other words, `W(k) * Wᶜ(k, n) = W(n * k)` for all `k, n ∈ 
ℤ`.

This extends `complEDS'` by defining its values at negative integers.
-/
def complEDS (n : ℤ) : R :=
  n.sign * complEDS' b c d k n.natAbs

@[simp]
/-
**complEDS_ofNat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：complEDS_ofNat (n : Nat) : complEDS b c d k n = complEDS' b c d k n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `complEDS'_zero`：∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (k : ℤ)
, complEDS' b c d k 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.sign_natCast_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → (↑n).sign = 1
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma complEDS_ofNat (n : ℕ) : complEDS b c d k n = complEDS' b c d k n := by
  by_cases hn : n = 0
  · simp [hn, complEDS]
  · simp [complEDS, Int.sign_natCast_of_ne_zero hn]

@[simp]
/-
**complEDS_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：complEDS_zero : complEDS b c d k 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `complEDS'_zero`：∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (k : ℤ)
, complEDS' b c d k 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma complEDS_zero : complEDS b c d k 0 = 0 := by
  simp [complEDS]

@[simp]
/-
**complEDS_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：complEDS_one : complEDS b c d k 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Int.natAbs_of_isUnit`：∀ {u : ℤ}, IsUnit u → u.natAbs = 1
· 使用定理 `complEDS'_one`：∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (k : ℤ),
 complEDS' b c d k 1 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma complEDS_one : complEDS b c d k 1 = 1 := by
  simp [complEDS]

@[simp]
/-
**complEDS_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：complEDS_neg (n : Int) : complEDS b c d k (-n) = -complEDS b c d k n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.sign_neg`：∀ (z : ℤ), (-z).sign = -z.sign
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.natAbs_neg`：∀ (a : ℤ), (-a).natAbs = a.natAbs
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma complEDS_neg (n : ℤ) : complEDS b c d k (-n) = -complEDS b c d k n := by
  simp [complEDS]
/-
**complEDS_even** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：complEDS_even (m : Int) : complEDS b c d k (2 * m) = complEDS b c d k m * 
complEDS₂ b c d (m * k)
参数：m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `complEDS_zero`：complEDS_zero : complEDS b c d k 0 = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `complEDS₂_zero`：complEDS₂_zero : complEDS₂ b c d 0 = 2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `complEDS_ofNat`：complEDS_ofNat (n : Nat) : complEDS b c d k n = complEDS
' b c d k n
· 使用定理 `complEDS'_even`：∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (k : ℤ)
 (m : ℕ),   complEDS' b c d k (2 * (m + 1)) = complEDS' b c d k (m + 1) * complE
DS₂ …
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用引理 `complEDS_neg`：complEDS_neg (n : Int) : complEDS b c d k (-n) = -complEDS
 b c d k n
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用引理 `complEDS₂_neg`：complEDS₂_neg (k : Int) : complEDS₂ b c d (-k) = complEDS
₂ b c d k
-/
lemma complEDS_even (m : ℤ) :
    complEDS b c d k (2 * m) = complEDS b c d k m * complEDS₂ b c d (m * k) := by
  induction m using Int.negInduction with
  | nat m =>
    rcases m with _ | _
    · simp
    norm_cast
    simpa only [complEDS_ofNat] using! complEDS'_even ..
  | neg ih => simp_rw [mul_neg, complEDS_neg, ih, neg_mul, complEDS₂_neg]
/-
**complEDS_odd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：complEDS_odd (m : Int) : complEDS b c d k (2 * m + 1) = complEDS b c d k m
 ^ 2 * normEDS b c d ((m + 1) * k + 1) * normEDS b c d ((m + 1) * k - 1) - compl
EDS b c d k (m + 1) ^ 2 * normEDS b c d (m * k + 1) * normEDS b c d (m * k - 1)
参数：m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `complEDS_one`：complEDS_one : complEDS b c d k 1 = 1
· 使用引理 `complEDS_zero`：complEDS_zero : complEDS b c d k 0 = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用引理 `normEDS_one`：normEDS_one : normEDS b c d 1 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用引理 `normEDS_neg`：normEDS_neg (n : Int) : normEDS b c d (-n) = -normEDS b c d
 n
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `complEDS_ofNat`：complEDS_ofNat (n : Nat) : complEDS b c d k n = complEDS
' b c d k n
· 使用定理 `complEDS'_odd`：∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (k : ℤ) 
(m : ℕ),   complEDS' b c d k (2 * (m + 1) + 1) =     complEDS' b c d k (m + 1) ^
 2 …
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
（共 75 条，此处仅展示前 30 条）
-/
lemma complEDS_odd (m : ℤ) : complEDS b c d k (2 * m + 1) =
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
    simp_rw [Nat.cast_succ, show 2 * -(m + 1 : ℤ) + 1 = -(2 * m + 1) by rfl,
      show (-(m + 1 : ℤ) + 1) = -m by ring1, neg_mul, ← sub_neg_eq_add, ← neg_sub', sub_neg_eq_add,
      ← neg_add', complEDS_neg, normEDS_neg, ih]
    ring1

/-- Strong recursion principle for the complement sequence for a normalised EDS: if we have
* `P 0`, `P 1`,
* for all `m : ℕ` we can prove `P (2 * (m + 3))` from `P k` for all `k < 2 * (m + 3)`, and
* for all `m : ℕ` we can prove `P (2 * (m + 2) + 1)` from `P k` for all `k < 2 * (m + 2) + 1`,

then we have `P n` for all `n : ℕ`. -/
@[elab_as_elim]
/-
**complEDSRec'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：complEDSRec' {P : Nat -> Sort*} (zero : P 0) (one : P 1) (even : forall m 
: Nat, (forall k < 2 * (m + 1), P k) -> P (2 * (m + 1))) (odd : forall m : Nat, 
(forall k < 2 * (m + 1) + 1, P k) -> P (2 * (m + 1) + 1)) (n : Nat) : P n
参数：zero : P 0；one : P 1；even : forall m : Nat, (forall k < 2 * (m + 1), P k) -> 
P (2 * (m + 1))；odd : forall m : Nat, (forall k < 2 * (m + 1) + 1, P k) -> P (2 
* (m + 1) + 1)；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Strong recursion principle for the complement sequence for a normalised EDS: if 
we have
* `P 0`, `P 1`,
* for all `m : ℕ` we can prove `P (2 * (m + 3))` from `P k` for all `k < 2 * (m 
+ 3)`, and
* for all `m : ℕ` we can prove `P (2 * (m + 2) + 1)` from `P k` for all `k < 2 *
 (m + 2) + 1`,

then we have `P n` for all `n : ℕ`.
-/
noncomputable def complEDSRec' {P : ℕ → Sort*} (zero : P 0) (one : P 1)
    (even : ∀ m : ℕ, (∀ k < 2 * (m + 1), P k) → P (2 * (m + 1)))
    (odd : ∀ m : ℕ, (∀ k < 2 * (m + 1) + 1, P k) → P (2 * (m + 1) + 1)) (n : ℕ) : P n :=
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
/-
**complEDSRec** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：complEDSRec {P : Nat -> Sort*} (zero : P 0) (one : P 1) (even : forall m :
 Nat, P (m + 1) -> P (2 * (m + 1))) (odd : forall m : Nat, P (m + 1) -> P (m + 2
) -> P (2 * (m + 1) + 1)) (n : Nat) : P n
参数：zero : P 0；one : P 1；even : forall m : Nat, P (m + 1) -> P (2 * (m + 1))；odd 
: forall m : Nat, P (m + 1) -> P (m + 2) -> P (2 * (m + 1) + 1)；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recursion principle for the complement sequence for a normalised EDS: if we have
* `P 0`, `P 1`,
* for all `m : ℕ` we can prove `P (2 * (m + 3))` from `P (m + 1)`, `P (m + 2)`, 
`P (m + 3)`,
  `P (m + 4)`, and `P (m + 5)`, and
* for all `m : ℕ` we can prove `P (2 * (m + 2) + 1)` from `P (m + 1)`, `P (m + 2
)`, `P (m + 3)`,
  and `P (m + 4)`,

then we have `P n` for all `n : ℕ`.
-/
noncomputable def complEDSRec {P : ℕ → Sort*} (zero : P 0) (one : P 1)
    (even : ∀ m : ℕ, P (m + 1) → P (2 * (m + 1)))
    (odd : ∀ m : ℕ, P (m + 1) → P (m + 2) → P (2 * (m + 1) + 1)) (n : ℕ) : P n :=
  complEDSRec' zero one (fun _ ih ↦ even _ <| ih _ <| by linarith only)
    (fun _ ih ↦ odd _ (ih _ <| by linarith only) <| ih _ <| by linarith only) n

end ComplEDS

section Map

@[simp]
/-
**map_preNormEDS'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：map_preNormEDS' (n : Nat) : f (preNormEDS' b c d n) = preNormEDS' (f b) (f
 c) (f d) n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `preNormEDS'_zero`：∀ {R : Type u_1} [inst : CommRing R] (b c d : R), preN
ormEDS' b c d 0 = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `preNormEDS'_one`：∀ {R : Type u_1} [inst : CommRing R] (b c d : R), preNo
rmEDS' b c d 1 = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `preNormEDS'_two`：∀ {R : Type u_1} [inst : CommRing R] (b c d : R), preNo
rmEDS' b c d 2 = 1
· 使用定理 `preNormEDS'_three`：∀ {R : Type u_1} [inst : CommRing R] (b c d : R), pre
NormEDS' b c d 3 = c
· 使用定理 `preNormEDS'_four`：∀ {R : Type u_1} [inst : CommRing R] (b c d : R), preN
ormEDS' b c d 4 = d
· 使用定理 `preNormEDS'_even`：∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (m : 
ℕ),   preNormEDS' b c d (2 * (m + 3)) =     preNormEDS' b c d (m + 2) ^ 2 * preN
ormEDS…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
（共 81 条，此处仅展示前 30 条）
-/
lemma map_preNormEDS' (n : ℕ) : f (preNormEDS' b c d n) = preNormEDS' (f b) (f c) (f d) n := by
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
/-
**map_preNormEDS** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：map_preNormEDS (n : Int) : f (preNormEDS b c d n) = preNormEDS (f b) (f c)
 (f d) n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
· 使用引理 `map_preNormEDS'`：map_preNormEDS' (n : Nat) : f (preNormEDS' b c d n) = p
reNormEDS' (f b) (f c) (f d) n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_preNormEDS (n : ℤ) : f (preNormEDS b c d n) = preNormEDS (f b) (f c) (f d) n := by
  simp [preNormEDS]

@[simp]
/-
**map_complEDS** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：map_complEDS (k n : Int) : f (complEDS b c d k n) = complEDS (f b) (f c) (
f d) k n
参数：k n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
· 使用引理 `map_complEDS'`：map_complEDS' (k : Int) (n : Nat) : f (complEDS' b c d k 
n) = complEDS' (f b) (f c) (f d) k n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_complEDS₂ (n : ℤ) : f (complEDS₂ b c d n) = complEDS₂ (f b) (f c) (f d) n := by
  simp [complEDS₂, apply_ite f]

@[simp]
/-
**map_normEDS** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：map_normEDS (n : Int) : f (normEDS b c d n) = normEDS (f b) (f c) (f d) n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `map_preNormEDS`：map_preNormEDS (n : Int) : f (preNormEDS b c d n) = preN
ormEDS (f b) (f c) (f d) n
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_normEDS (n : ℤ) : f (normEDS b c d n) = normEDS (f b) (f c) (f d) n := by
  simp [normEDS, apply_ite f]

@[simp]
/-
**map_complEDS'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：map_complEDS' (k : Int) (n : Nat) : f (complEDS' b c d k n) = complEDS' (f
 b) (f c) (f d) k n
参数：k : Int；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `complEDS'_zero`：∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (k : ℤ)
, complEDS' b c d k 0 = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `complEDS'_one`：∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (k : ℤ),
 complEDS' b c d k 1 = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `complEDS'_even`：∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (k : ℤ)
 (m : ℕ),   complEDS' b c d k (2 * (m + 1)) = complEDS' b c d k (m + 1) * complE
DS₂ …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用引理 `map_complEDS₂`：map_complEDS₂ (n : Int) : f (complEDS₂ b c d n) = complED
S₂ (f b) (f c) (f d) n
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
（共 77 条，此处仅展示前 30 条）
-/
lemma map_complEDS' (k : ℤ) (n : ℕ) :
    f (complEDS' b c d k n) = complEDS' (f b) (f c) (f d) k n := by
  induction n using complEDSRec' with
  | zero => simp
  | one => simp
  | _ _ ih =>
    simp only [complEDS'_even, complEDS'_odd, map_normEDS, map_complEDS₂, map_pow, map_mul, map_sub]
    repeat rw [ih _ <| by linarith only]

@[simp]
/-
**map_complEDS** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：map_complEDS (k n : Int) : f (complEDS b c d k n) = complEDS (f b) (f c) (
f d) k n
参数：k n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
· 使用引理 `map_complEDS'`：map_complEDS' (k : Int) (n : Nat) : f (complEDS' b c d k 
n) = complEDS' (f b) (f c) (f d) k n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_complEDS (k n : ℤ) : f (complEDS b c d k n) = complEDS (f b) (f c) (f d) k n := by
  simp [complEDS]

end Map

