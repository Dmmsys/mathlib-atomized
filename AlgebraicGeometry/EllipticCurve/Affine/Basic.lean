/-
Copyright (c) 2025 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# Weierstrass equations and the nonsingular condition in affine coordinates

Let `W` be a Weierstrass curve over a commutative ring `R` with coefficients `aᵢ`. An *affine point*
on `W` is a tuple `(x, y)` of elements in `R` satisfying the *Weierstrass equation* `W(X, Y) = 0` in
*affine coordinates*, where `W(X, Y) := Y² + a₁XY + a₃Y - (X³ + a₂X² + a₄X + a₆)`. It is
*nonsingular* if its partial derivatives `W_X(x, y)` and `W_Y(x, y)` do not vanish simultaneously.

This file defines polynomials associated to Weierstrass equations and the nonsingular condition in
affine coordinates. The group law on the actual type of nonsingular points in affine coordinates
will be defined in `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`, based on the
formulae for group operations in `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean`.

## Main definitions

* `WeierstrassCurve.Affine.Equation`: the Weierstrass equation in affine coordinates.
* `WeierstrassCurve.Affine.Nonsingular`: the nonsingular condition in affine coordinates.

## Main statements

* `WeierstrassCurve.Affine.equation_iff_nonsingular`: an elliptic curve in affine coordinates is
  nonsingular at every point.

## Implementation notes

All definitions and lemmas for Weierstrass curves in affine coordinates live in the namespace
`WeierstrassCurve.Affine` to distinguish them from those in other coordinates. This is simply an
abbreviation for `WeierstrassCurve` that can be converted using `WeierstrassCurve.toAffine`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, affine, Weierstrass equation, nonsingular
-/

@[expose] public section

open Polynomial

open scoped Polynomial.Bivariate

local macro "eval_simp" : tactic =>
  `(tactic| simp only [eval_C, eval_X, eval_neg, eval_add, eval_sub, eval_mul, eval_pow, evalEval])

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow, map_div₀,
    Polynomial.map_ofNat, map_C, map_X, Polynomial.map_neg, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_div, coe_mapRingHom,
    WeierstrassCurve.map])

universe r s u v

variable {R : Type r}

namespace WeierstrassCurve

/-! ## Affine coordinates -/

variable (R) in
/-- An abbreviation for a Weierstrass curve in affine coordinates. -/
/-
**WeierstrassCurve.Affine** 是 Mathlib 中的一个缩写定义，位于命名空间 `WeierstrassCurve`。
形式化陈述：Affine : Type r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abbreviation for a Weierstrass curve in affine coordinates.
-/
abbrev Affine : Type r :=
  WeierstrassCurve R

/-- The conversion from a Weierstrass curve to affine coordinates. -/
/-
**WeierstrassCurve.toAffine** 是 Mathlib 中的一个缩写定义，位于命名空间 `WeierstrassCurve`。
形式化陈述：toAffine (W : WeierstrassCurve R) : Affine R
参数：W : WeierstrassCurve R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The conversion from a Weierstrass curve to affine coordinates.
-/
abbrev toAffine (W : WeierstrassCurve R) : Affine R :=
  W

variable [CommRing R] {W : Affine R}
  {S : Type s} [CommRing S] {A : Type u} [CommRing A] {B : Type v} [CommRing B]

namespace Affine

/-! ## Weierstrass equations in affine coordinates -/

variable (W) in
/-- The polynomial `W(X, Y) := Y² + a₁XY + a₃Y - (X³ + a₂X² + a₄X + a₆)` associated to a Weierstrass
curve `W` over a ring `R` in affine coordinates.

For ease of polynomial manipulation, this is represented as a term of type `R[X][X]`, where the
inner variable represents `X` and the outer variable represents `Y`. For clarity, the alternative
notations `Y` and `R[X][Y]` are provided in the `Polynomial.Bivariate` scope to represent the outer
variable and the bivariate polynomial ring `R[X][X]` respectively. -/
/-
**WeierstrassCurve.Affine.polynomial** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve
.Affine`。
形式化陈述：polynomial : R[X][Y]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The polynomial `W(X, Y) := Y² + a₁XY + a₃Y - (X³ + a₂X² + a₄X + a₆)` associated 
to a Weierstrass
curve `W` over a ring `R` in affine coordinates.

For ease of polynomial manipulation, this is represented as a term of type `R[X]
[X]`, where the
inner variable represents `X` and the outer variable represents `Y`. For clarity
, the alternative
notations `Y` and `R[X][Y]` are provided in the `Polynomial.Bivariate` scope to 
represent the outer
variable and the bivariate polynomial ring `R[X][X]` respectively.
-/
noncomputable def polynomial : R[X][Y] :=
  Y ^ 2 + C (C W.a₁ * X + C W.a₃) * Y - C (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)
/-
**WeierstrassCurve.Affine.polynomial_eq** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCu
rve.Affine`。
形式化陈述：polynomial_eq : W.polynomial = Cubic.toPoly ⟨0, 1, Cubic.toPoly ⟨0, 0, W.a
₁, W.a₃⟩, Cubic.toPoly ⟨-1, -W.a₂, -W.a₄, -W.a₆⟩⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
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
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
（共 55 条，此处仅展示前 30 条）
-/
lemma polynomial_eq : W.polynomial = Cubic.toPoly
    ⟨0, 1, Cubic.toPoly ⟨0, 0, W.a₁, W.a₃⟩, Cubic.toPoly ⟨-1, -W.a₂, -W.a₄, -W.a₆⟩⟩ := by
  simp_rw [polynomial, Cubic.toPoly]
  map_simp
  simp only [C_0, C_1]
  ring1
/-
**WeierstrassCurve.Affine.polynomial_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Weierstr
assCurve.Affine`。
形式化陈述：polynomial_ne_zero [Nontrivial R] : W.polynomial != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Affine.polynomial_eq`：polynomial_eq : W.polynomial = Cu
bic.toPoly ⟨0, 1, Cubic.toPoly ⟨0, 0, W.a₁, W.a₃⟩, Cubic.toPoly ⟨-1, -W.a₂, -W.a
₄, -W.a₆⟩⟩
· 使用定理 `Cubic.ne_zero_of_b_ne_zero`：ne_zero_of_b_ne_zero (hb : P.b != 0) : P.toP
oly != 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
lemma polynomial_ne_zero [Nontrivial R] : W.polynomial ≠ 0 := by
  rw [polynomial_eq]
  exact Cubic.ne_zero_of_b_ne_zero one_ne_zero

@[simp]
/-
**WeierstrassCurve.Affine.degree_polynomial** 是 Mathlib 中的一个引理，位于命名空间 `Weierstra
ssCurve.Affine`。
形式化陈述：degree_polynomial [Nontrivial R] : W.polynomial.degree = 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Affine.polynomial_eq`：polynomial_eq : W.polynomial = Cu
bic.toPoly ⟨0, 1, Cubic.toPoly ⟨0, 0, W.a₁, W.a₃⟩, Cubic.toPoly ⟨-1, -W.a₂, -W.a
₄, -W.a₆⟩⟩
· 使用定理 `Cubic.degree_of_b_ne_zero'`：degree_of_b_ne_zero' (hb : b != 0) : (toPoly
 ⟨0, b, c, d⟩).degree = 2
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
lemma degree_polynomial [Nontrivial R] : W.polynomial.degree = 2 := by
  rw [polynomial_eq]
  exact Cubic.degree_of_b_ne_zero' one_ne_zero

@[simp]
/-
**WeierstrassCurve.Affine.natDegree_polynomial** 是 Mathlib 中的一个引理，位于命名空间 `Weiers
trassCurve.Affine`。
形式化陈述：natDegree_polynomial [Nontrivial R] : W.polynomial.natDegree = 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Affine.polynomial_eq`：polynomial_eq : W.polynomial = Cu
bic.toPoly ⟨0, 1, Cubic.toPoly ⟨0, 0, W.a₁, W.a₃⟩, Cubic.toPoly ⟨-1, -W.a₂, -W.a
₄, -W.a₆⟩⟩
· 使用定理 `Cubic.natDegree_of_b_ne_zero'`：natDegree_of_b_ne_zero' (hb : b != 0) : (
toPoly ⟨0, b, c, d⟩).natDegree = 2
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
lemma natDegree_polynomial [Nontrivial R] : W.polynomial.natDegree = 2 := by
  rw [polynomial_eq]
  exact Cubic.natDegree_of_b_ne_zero' one_ne_zero
/-
**WeierstrassCurve.Affine.monic_polynomial** 是 Mathlib 中的一个引理，位于命名空间 `Weierstras
sCurve.Affine`。
形式化陈述：monic_polynomial : W.polynomial.Monic
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Affine.polynomial_eq`：polynomial_eq : W.polynomial = Cu
bic.toPoly ⟨0, 1, Cubic.toPoly ⟨0, 0, W.a₁, W.a₃⟩, Cubic.toPoly ⟨-1, -W.a₂, -W.a
₄, -W.a₆⟩⟩
· 使用定理 `Cubic.monic_of_b_eq_one'`：monic_of_b_eq_one' : (toPoly ⟨0, 1, c, d⟩).Mon
ic
-/
lemma monic_polynomial : W.polynomial.Monic := by
  simpa only [polynomial_eq] using Cubic.monic_of_b_eq_one'
/-
**WeierstrassCurve.Affine.irreducible_polynomial** 是 Mathlib 中的一个引理，位于命名空间 `Weie
rstrassCurve.Affine`。
形式化陈述：irreducible_polynomial [IsDomain R] : Irreducible W.polynomial
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.Monic.not_irreducible_iff_exists_add_mul_eq_coeff`：∀ {R : Typ
e u} [inst : CommSemiring R] [NoZeroDivisors R] {p : Polynomial R},   p.Monic → 
p.natDegree = 2 → (¬Irreducible p ↔ ∃ c₁ c₂, p.coe…
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用引理 `WeierstrassCurve.Affine.monic_polynomial`：monic_polynomial : W.polynomia
l.Monic
· 使用引理 `WeierstrassCurve.Affine.natDegree_polynomial`：natDegree_polynomial [Nont
rivial R] : W.polynomial.natDegree = 2
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `WeierstrassCurve.Affine.polynomial_eq`：polynomial_eq : W.polynomial = Cu
bic.toPoly ⟨0, 1, Cubic.toPoly ⟨0, 0, W.a₁, W.a₃⟩, Cubic.toPoly ⟨-1, -W.a₂, -W.a
₄, -W.a₆⟩⟩
· 使用定理 `Cubic.coeff_eq_c`：coeff_eq_c : P.toPoly.coeff 1 = P.c
· 使用定理 `Cubic.degree_of_b_eq_zero'`：degree_of_b_eq_zero' : (toPoly ⟨0, 0, c, d⟩)
.degree <= 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.WithBot.add_eq_three_iff`：add_eq_three_iff {n m : WithBot Nat} : n +
 m = 3 ↔ n = 0 ∧ m = 3 ∨ n = 1 ∧ m = 2 ∨ n = 2 ∧ m = 1 ∨ n = 3 ∧ m = 0
· 使用引理 `Polynomial.degree_mul`：degree_mul : degree (p * q) = degree p + degree q
· 使用定理 `Cubic.degree_of_a_ne_zero'`：degree_of_a_ne_zero' (ha : a != 0) : (toPoly
 ⟨a, b, c, d⟩).degree = 3
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用引理 `one_ne_zero'`：one_ne_zero' [One α] [NeZero (1 : α)] : (1 : α) != 0
· 使用定理 `Cubic.coeff_eq_d`：coeff_eq_d : P.toPoly.coeff 0 = P.d
· 使用定理 `Polynomial.degree_add_eq_right_of_degree_lt`：degree_add_eq_right_of_degr
ee_lt (h : degree p < degree q) : degree (p + q) = degree q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 32 条，此处仅展示前 30 条）
-/
lemma irreducible_polynomial [IsDomain R] : Irreducible W.polynomial := by
  by_contra h
  rcases (monic_polynomial.not_irreducible_iff_exists_add_mul_eq_coeff natDegree_polynomial).mp h
    with ⟨f, g, h0, h1⟩
  simp only [polynomial_eq, Cubic.coeff_eq_c, Cubic.coeff_eq_d] at h0 h1
  apply_fun degree at h0 h1
  rw [Cubic.degree_of_a_ne_zero' <| neg_ne_zero.mpr <| one_ne_zero' R, degree_mul] at h0
  apply (h1.symm.le.trans Cubic.degree_of_b_eq_zero').not_gt
  rcases Nat.WithBot.add_eq_three_iff.mp h0.symm with h | h | h | h
  iterate 2 rw [degree_add_eq_right_of_degree_lt] <;> simp only [h] <;> decide
  iterate 2 rw [degree_add_eq_left_of_degree_lt] <;> simp only [h] <;> decide
/-
**WeierstrassCurve.Affine.evalEval_polynomial** 是 Mathlib 中的一个引理，位于命名空间 `Weierst
rassCurve.Affine`。
形式化陈述：evalEval_polynomial (x y : R) : W.polynomial.evalEval x y = y ^ 2 + W.a₁ *
 x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
-/
lemma evalEval_polynomial (x y : R) : W.polynomial.evalEval x y =
    y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) := by
  simp only [polynomial]
  eval_simp
  rw [add_mul, ← add_assoc]

@[simp]
/-
**WeierstrassCurve.Affine.evalEval_polynomial_zero** 是 Mathlib 中的一个引理，位于命名空间 `We
ierstrassCurve.Affine`。
形式化陈述：evalEval_polynomial_zero : W.polynomial.evalEval 0 0 = -W.a₆
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Affine.evalEval_polynomial`：evalEval_polynomial (x y : 
R) : W.polynomial.evalEval x y = y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂
 * x ^ 2 + W.a₄ * x + W.a₆)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma evalEval_polynomial_zero : W.polynomial.evalEval 0 0 = -W.a₆ := by
  simp only [evalEval_polynomial, zero_add, zero_sub, mul_zero, zero_pow <| Nat.succ_ne_zero _]

variable (W) in
/-- The proposition that an affine point `(x, y)` lies in a Weierstrass curve `W`.

In other words, it satisfies the Weierstrass equation `W(X, Y) = 0`. -/
/-
**WeierstrassCurve.Affine.Equation** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve.A
ffine`。
形式化陈述：Equation (x y : R) : Prop
参数：x y : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposition that an affine point `(x, y)` lies in a Weierstrass curve `W`.

In other words, it satisfies the Weierstrass equation `W(X, Y) = 0`.
-/
def Equation (x y : R) : Prop :=
  W.polynomial.evalEval x y = 0
/-
**WeierstrassCurve.Affine.equation_iff'** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCu
rve.Affine`。
形式化陈述：equation_iff' (x y : R) : W.Equation x y ↔ y ^ 2 + W.a₁ * x * y + W.a₃ * y
 - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0
参数：x y : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.Affine.Equation.eq_1`：∀ {R : Type r} [inst : CommRing R
] (W : WeierstrassCurve.Affine R) (x y : R),   W.Equation x y = (Polynomial.eval
Eval x y W.polynomial = 0)
· 使用引理 `WeierstrassCurve.Affine.evalEval_polynomial`：evalEval_polynomial (x y : 
R) : W.polynomial.evalEval x y = y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂
 * x ^ 2 + W.a₄ * x + W.a₆)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma equation_iff' (x y : R) : W.Equation x y ↔
    y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 := by
  rw [Equation, evalEval_polynomial]
/-
**WeierstrassCurve.Affine.equation_iff** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCur
ve.Affine`。
形式化陈述：equation_iff (x y : R) : W.Equation x y ↔ y ^ 2 + W.a₁ * x * y + W.a₃ * y 
= x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆
参数：x y : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Affine.equation_iff'`：equation_iff' (x y : R) : W.Equat
ion x y ↔ y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W
.a₆) = 0
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma equation_iff (x y : R) : W.Equation x y ↔
    y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
  rw [equation_iff', sub_eq_zero]

@[simp]
/-
**WeierstrassCurve.Affine.equation_zero** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCu
rve.Affine`。
形式化陈述：equation_zero : W.Equation 0 0 ↔ W.a₆ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.Affine.Equation.eq_1`：∀ {R : Type r} [inst : CommRing R
] (W : WeierstrassCurve.Affine R) (x y : R),   W.Equation x y = (Polynomial.eval
Eval x y W.polynomial = 0)
· 使用引理 `WeierstrassCurve.Affine.evalEval_polynomial_zero`：evalEval_polynomial_ze
ro : W.polynomial.evalEval 0 0 = -W.a₆
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma equation_zero : W.Equation 0 0 ↔ W.a₆ = 0 := by
  rw [Equation, evalEval_polynomial_zero, neg_eq_zero]
/-
**WeierstrassCurve.Affine.equation_iff_variableChange** 是 Mathlib 中的一个引理，位于命名空间 
`WeierstrassCurve.Affine`。
形式化陈述：equation_iff_variableChange (x y : R) : W.Equation x y ↔ (VariableChange.m
k 1 x 0 y • W).toAffine.Equation 0 0
参数：x y : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Affine.equation_iff'`：equation_iff' (x y : R) : W.Equat
ion x y ↔ y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W
.a₆) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用引理 `WeierstrassCurve.Affine.equation_zero`：equation_zero : W.Equation 0 0 ↔ 
W.a₆ = 0
· 使用引理 `WeierstrassCurve.variableChange_a₆`：variableChange_a₆ : (C • W).a₆ = C.u
⁻¹ ^ 6 * (W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃ - C.t ^ 2 - 
C.r * C.t * W.a₁)
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
（共 48 条，此处仅展示前 30 条）
-/
lemma equation_iff_variableChange (x y : R) :
    W.Equation x y ↔ (VariableChange.mk 1 x 0 y • W).toAffine.Equation 0 0 := by
  rw [equation_iff', ← neg_eq_zero, equation_zero, variableChange_a₆, inv_one, Units.val_one]
  congr! 1
  ring1

/-! ## The nonsingular condition in affine coordinates -/

variable (W) in
/-- The partial derivative `W_X(X, Y)` with respect to `X` of the polynomial `W(X, Y)` associated to
a Weierstrass curve `W` in affine coordinates. -/
-- TODO: define this in terms of `Polynomial.derivative`.
/-
**WeierstrassCurve.Affine.polynomialX** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurv
e.Affine`。
形式化陈述：polynomialX : R[X][Y]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def polynomialX : R[X][Y] :=
  C (C W.a₁) * Y - C (C 3 * X ^ 2 + C (2 * W.a₂) * X + C W.a₄)
/-
**WeierstrassCurve.Affine.evalEval_polynomialX** 是 Mathlib 中的一个引理，位于命名空间 `Weiers
trassCurve.Affine`。
形式化陈述：evalEval_polynomialX (x y : R) : W.polynomialX.evalEval x y = W.a₁ * y - (
3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma evalEval_polynomialX (x y : R) :
    W.polynomialX.evalEval x y = W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) := by
  simp only [polynomialX]
  eval_simp

@[simp]
/-
**WeierstrassCurve.Affine.evalEval_polynomialX_zero** 是 Mathlib 中的一个引理，位于命名空间 `W
eierstrassCurve.Affine`。
形式化陈述：evalEval_polynomialX_zero : W.polynomialX.evalEval 0 0 = -W.a₄
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `WeierstrassCurve.Affine.evalEval_polynomialX`：evalEval_polynomialX (x y 
: R) : W.polynomialX.evalEval x y = W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma evalEval_polynomialX_zero : W.polynomialX.evalEval 0 0 = -W.a₄ := by
  simp only [evalEval_polynomialX, zero_add, zero_sub, mul_zero, zero_pow <| Nat.succ_ne_zero _]

variable (W) in
/-- The partial derivative `W_Y(X, Y)` with respect to `Y` of the polynomial `W(X, Y)` associated to
a Weierstrass curve `W` in affine coordinates. -/
-- TODO: define this in terms of `Polynomial.derivative`.
/-
**WeierstrassCurve.Affine.polynomialY** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurv
e.Affine`。
形式化陈述：polynomialY : R[X][Y]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def polynomialY : R[X][Y] :=
  C (C 2) * Y + C (C W.a₁ * X + C W.a₃)
/-
**WeierstrassCurve.Affine.evalEval_polynomialY** 是 Mathlib 中的一个引理，位于命名空间 `Weiers
trassCurve.Affine`。
形式化陈述：evalEval_polynomialY (x y : R) : W.polynomialY.evalEval x y = 2 * y + W.a₁
 * x + W.a₃
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
-/
lemma evalEval_polynomialY (x y : R) : W.polynomialY.evalEval x y = 2 * y + W.a₁ * x + W.a₃ := by
  simp only [polynomialY]
  eval_simp
  rw [← add_assoc]

@[simp]
/-
**WeierstrassCurve.Affine.evalEval_polynomialY_zero** 是 Mathlib 中的一个引理，位于命名空间 `W
eierstrassCurve.Affine`。
形式化陈述：evalEval_polynomialY_zero : W.polynomialY.evalEval 0 0 = W.a₃
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `WeierstrassCurve.Affine.evalEval_polynomialY`：evalEval_polynomialY (x y 
: R) : W.polynomialY.evalEval x y = 2 * y + W.a₁ * x + W.a₃
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma evalEval_polynomialY_zero : W.polynomialY.evalEval 0 0 = W.a₃ := by
  simp only [evalEval_polynomialY, zero_add, mul_zero]

variable (W) in
/-- The proposition that an affine point `(x, y)` on a Weierstrass curve `W` is nonsingular.

In other words, either `W_X(x, y) ≠ 0` or `W_Y(x, y) ≠ 0`.

Note that this definition is only mathematically accurate for fields. -/
-- TODO: generalise this definition to be mathematically accurate for a larger class of rings.
/-
**WeierstrassCurve.Affine.Nonsingular** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurv
e.Affine`。
形式化陈述：Nonsingular (x y : R) : Prop
参数：x y : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Nonsingular (x y : R) : Prop :=
  W.Equation x y ∧ (W.polynomialX.evalEval x y ≠ 0 ∨ W.polynomialY.evalEval x y ≠ 0)
/-
**WeierstrassCurve.Affine.nonsingular_iff'** 是 Mathlib 中的一个引理，位于命名空间 `Weierstras
sCurve.Affine`。
形式化陈述：nonsingular_iff' (x y : R) : W.Nonsingular x y ↔ W.Equation x y ∧ (W.a₁ * 
y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) != 0 ∨ 2 * y + W.a₁ * x + W.a₃ != 0)
参数：x y : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.Affine.Nonsingular.eq_1`：∀ {R : Type r} [inst : CommRin
g R] (W : WeierstrassCurve.Affine R) (x y : R),   W.Nonsingular x y =     (W.Equ
ation x y ∧ (Polynomial.evalEv…
· 使用引理 `WeierstrassCurve.Affine.equation_iff'`：equation_iff' (x y : R) : W.Equat
ion x y ↔ y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W
.a₆) = 0
· 使用引理 `WeierstrassCurve.Affine.evalEval_polynomialX`：evalEval_polynomialX (x y 
: R) : W.polynomialX.evalEval x y = W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)
· 使用引理 `WeierstrassCurve.Affine.evalEval_polynomialY`：evalEval_polynomialY (x y 
: R) : W.polynomialY.evalEval x y = 2 * y + W.a₁ * x + W.a₃
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma nonsingular_iff' (x y : R) : W.Nonsingular x y ↔ W.Equation x y ∧
    (W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ≠ 0 ∨ 2 * y + W.a₁ * x + W.a₃ ≠ 0) := by
  rw [Nonsingular, equation_iff', evalEval_polynomialX, evalEval_polynomialY]
/-
**WeierstrassCurve.Affine.nonsingular_iff** 是 Mathlib 中的一个引理，位于命名空间 `Weierstrass
Curve.Affine`。
形式化陈述：nonsingular_iff (x y : R) : W.Nonsingular x y ↔ W.Equation x y ∧ (W.a₁ * y
 != 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ∨ y != -y - W.a₁ * x - W.a₃)
参数：x y : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Affine.nonsingular_iff'`：nonsingular_iff' (x y : R) : W
.Nonsingular x y ↔ W.Equation x y ∧ (W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄
) != 0 ∨ 2 * y + W.a₁ * x + W.…
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
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
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
（共 41 条，此处仅展示前 30 条）
-/
lemma nonsingular_iff (x y : R) : W.Nonsingular x y ↔ W.Equation x y ∧
    (W.a₁ * y ≠ 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ∨ y ≠ -y - W.a₁ * x - W.a₃) := by
  rw [nonsingular_iff', sub_ne_zero, ← sub_ne_zero (a := y)]
  congr! 3
  ring1

@[simp]
/-
**WeierstrassCurve.Affine.nonsingular_zero** 是 Mathlib 中的一个引理，位于命名空间 `Weierstras
sCurve.Affine`。
形式化陈述：nonsingular_zero : W.Nonsingular 0 0 ↔ W.a₆ = 0 ∧ (W.a₃ != 0 ∨ W.a₄ != 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.Affine.Nonsingular.eq_1`：∀ {R : Type r} [inst : CommRin
g R] (W : WeierstrassCurve.Affine R) (x y : R),   W.Nonsingular x y =     (W.Equ
ation x y ∧ (Polynomial.evalEv…
· 使用引理 `WeierstrassCurve.Affine.equation_zero`：equation_zero : W.Equation 0 0 ↔ 
W.a₆ = 0
· 使用引理 `WeierstrassCurve.Affine.evalEval_polynomialX_zero`：evalEval_polynomialX_
zero : W.polynomialX.evalEval 0 0 = -W.a₄
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用引理 `WeierstrassCurve.Affine.evalEval_polynomialY_zero`：evalEval_polynomialY_
zero : W.polynomialY.evalEval 0 0 = W.a₃
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma nonsingular_zero : W.Nonsingular 0 0 ↔ W.a₆ = 0 ∧ (W.a₃ ≠ 0 ∨ W.a₄ ≠ 0) := by
  rw [Nonsingular, equation_zero, evalEval_polynomialX_zero, neg_ne_zero, evalEval_polynomialY_zero,
    or_comm]
/-
**WeierstrassCurve.Affine.nonsingular_iff_variableChange** 是 Mathlib 中的一个引理，位于命名
空间 `WeierstrassCurve.Affine`。
形式化陈述：nonsingular_iff_variableChange (x y : R) : W.Nonsingular x y ↔ (VariableCh
ange.mk 1 x 0 y • W).toAffine.Nonsingular 0 0
参数：x y : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Affine.nonsingular_iff'`：nonsingular_iff' (x y : R) : W
.Nonsingular x y ↔ W.Equation x y ∧ (W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄
) != 0 ∨ 2 * y + W.a₁ * x + W.…
· 使用引理 `WeierstrassCurve.Affine.equation_iff_variableChange`：equation_iff_variab
leChange (x y : R) : W.Equation x y ↔ (VariableChange.mk 1 x 0 y • W).toAffine.E
quation 0 0
· 使用引理 `WeierstrassCurve.Affine.equation_zero`：equation_zero : W.Equation 0 0 ↔ 
W.a₆ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用引理 `WeierstrassCurve.Affine.nonsingular_zero`：nonsingular_zero : W.Nonsingul
ar 0 0 ↔ W.a₆ = 0 ∧ (W.a₃ != 0 ∨ W.a₄ != 0)
· 使用引理 `WeierstrassCurve.variableChange_a₃`：variableChange_a₃ : (C • W).a₃ = C.u
⁻¹ ^ 3 * (W.a₃ + C.r * W.a₁ + 2 * C.t)
· 使用引理 `WeierstrassCurve.variableChange_a₄`：variableChange_a₄ : (C • W).a₄ = C.u
⁻¹ ^ 4 * (W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁ + 3 * C.
r ^ 2 - 2 * C.s * C.t)
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
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
（共 57 条，此处仅展示前 30 条）
-/
lemma nonsingular_iff_variableChange (x y : R) :
    W.Nonsingular x y ↔ (VariableChange.mk 1 x 0 y • W).toAffine.Nonsingular 0 0 := by
  rw [nonsingular_iff', equation_iff_variableChange, equation_zero, ← neg_ne_zero, or_comm,
    nonsingular_zero, variableChange_a₃, variableChange_a₄, inv_one, Units.val_one]
  simp only [variableChange_def]
  congr! 3 <;> ring1
/-
**WeierstrassCurve.Affine.equation_zero_iff_nonsingular_zero_of_** 是 Mathlib 中的一
个引理，位于命名空间 `WeierstrassCurve.Affine`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma equation_zero_iff_nonsingular_zero_of_Δ_ne_zero (hΔ : W.Δ ≠ 0) :
    W.Equation 0 0 ↔ W.Nonsingular 0 0 := by
  simp only [equation_zero, nonsingular_zero, iff_self_and]
  contrapose! hΔ
  simp only [b₂, b₄, b₆, b₈, Δ, hΔ]
  ring1
/-
**WeierstrassCurve.Affine.equation_iff_nonsingular_of_** 是 Mathlib 中的一个引理，位于命名空间
 `WeierstrassCurve.Affine`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equation_iff_nonsingular_of_Δ_ne_zero {x y : R} (hΔ : W.Δ ≠ 0) :
    W.Equation x y ↔ W.Nonsingular x y := by
  rw [equation_iff_variableChange, nonsingular_iff_variableChange,
    equation_zero_iff_nonsingular_zero_of_Δ_ne_zero <| by
      rwa [variableChange_Δ, inv_one, Units.val_one, one_pow, one_mul]]
/-
**WeierstrassCurve.Affine.equation_iff_nonsingular** 是 Mathlib 中的一个引理，位于命名空间 `We
ierstrassCurve.Affine`。
形式化陈述：equation_iff_nonsingular [Nontrivial R] [W.IsElliptic] {x y : R} : W.Equat
ion x y ↔ W.Nonsingular x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero`：equation_
iff_nonsingular_of_Δ_ne_zero {x y : R} (hΔ : W.Δ != 0) : W.Equation x y ↔ W.Nons
ingular x y
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用引理 `WeierstrassCurve.coe_Δ'`：coe_Δ' : W.Δ' = W.Δ
-/
lemma equation_iff_nonsingular [Nontrivial R] [W.IsElliptic] {x y : R} :
    W.Equation x y ↔ W.Nonsingular x y :=
  W.equation_iff_nonsingular_of_Δ_ne_zero <| W.coe_Δ' ▸ W.Δ'.ne_zero

/-! ### Maps and base changes -/

variable (W) (f : R →+* S)

/-- The Weierstrass curve in affine coordinates mapped over a ring homomorphism `f : R →+* S`. -/
/-
**WeierstrassCurve.Affine.map** 是 Mathlib 中的一个缩写定义，位于命名空间 `WeierstrassCurve.Affi
ne`。
形式化陈述：map : Affine S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Weierstrass curve in affine coordinates mapped over a ring homomorphism `f :
 R →+* S`.
-/
abbrev map : Affine S :=
  WeierstrassCurve.map W f

variable (S) in
/-- The Weierstrass curve in affine coordinates base changed to an algebra `S` over `R`. -/
@[simps!]
/-
**WeierstrassCurve.Affine.baseChange** 是 Mathlib 中的一个缩写定义，位于命名空间 `WeierstrassCur
ve.Affine`。
形式化陈述：baseChange [Algebra R S] : Affine S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Weierstrass curve in affine coordinates base changed to an algebra `S` over 
`R`.
-/
abbrev baseChange [Algebra R S] : Affine S :=
  WeierstrassCurve.baseChange W S

/-- The notation `\textf` for `WeierstrassCurve.Affine.baseChange W S`. -/
scoped notation:max W:max "⁄" S:max => baseChange W S

/-
**WeierstrassCurve.Affine.map_polynomial** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassC
urve.Affine`。
形式化陈述：map_polynomial : (W.map f).polynomial = W.polynomial.map (mapRingHom f)
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
· 使用定理 `WeierstrassCurve.map.eq_1`：∀ {R : Type u} [inst : CommRing R] (W : Weier
strassCurve R) {A : Type v} [inst_1 : CommRing A] (f : R →+* A),   W.map f = { a
₁ := f W.a₁, a₂…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
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
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Polynomial.map_sub`：∀ {R : Type u} [inst : Ring R] {p q : Polynomial R} 
{S : Type u_1} [inst_1 : Ring S] (f : R →+* S),   Polynomial.map f (p - q) = Pol
ynomial.…
· 使用定理 `Polynomial.map_add`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p + q)
 = Polyn…
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_polynomial : (W.map f).polynomial = W.polynomial.map (mapRingHom f) := by
  simp only [polynomial]
  map_simp

variable {W} in
/-
**WeierstrassCurve.Affine.Equation.map** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCur
ve.Affine.Equation`。
形式化陈述：∀ {R : Type r} [inst : CommRing R] {W : WeierstrassCurve.Affine R} {S : Ty
pe s} [inst_1 : CommRing S] (f : R →+* S)   {x y : R}, W.Equation x y → (W.map f
).Equation (f x) (f y)
参数：f : R →+* S；W.map f；f x；f y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.Affine.Equation.eq_1`：∀ {R : Type r} [inst : CommRing R
] (W : WeierstrassCurve.Affine R) (x y : R),   W.Equation x y = (Polynomial.eval
Eval x y W.polynomial = 0)
· 使用引理 `WeierstrassCurve.Affine.map_polynomial`：map_polynomial : (W.map f).polyn
omial = W.polynomial.map (mapRingHom f)
· 使用引理 `Polynomial.map_mapRingHom_evalEval`：map_mapRingHom_evalEval (x y : R) : 
(p.map <| mapRingHom f).evalEval (f x) (f y) = f (p.evalEval x y)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
lemma Equation.map {x y : R} (h : W.Equation x y) : (W.map f).Equation (f x) (f y) := by
  rw [Equation, map_polynomial, map_mapRingHom_evalEval, h, map_zero]

variable {f} in
/-
**WeierstrassCurve.Affine.map_equation** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCur
ve.Affine`。
形式化陈述：map_equation (hf : Function.Injective f) (x y : R) : (W.map f).Equation (f
 x) (f y) ↔ W.Equation x y
参数：hf : Function.Injective f；x y : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Affine.map_polynomial`：map_polynomial : (W.map f).polyn
omial = W.polynomial.map (mapRingHom f)
· 使用引理 `Polynomial.map_mapRingHom_evalEval`：map_mapRingHom_evalEval (x y : R) : 
(p.map <| mapRingHom f).evalEval (f x) (f y) = f (p.evalEval x y)
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma map_equation (hf : Function.Injective f) (x y : R) :
    (W.map f).Equation (f x) (f y) ↔ W.Equation x y := by
  simp only [Equation, map_polynomial, map_mapRingHom_evalEval, map_eq_zero_iff f hf]
/-
**WeierstrassCurve.Affine.map_polynomialX** 是 Mathlib 中的一个引理，位于命名空间 `Weierstrass
Curve.Affine`。
形式化陈述：map_polynomialX : (W.map f).polynomialX = W.polynomialX.map (mapRingHom f)
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
· 使用定理 `WeierstrassCurve.map.eq_1`：∀ {R : Type u} [inst : CommRing R] (W : Weier
strassCurve R) {A : Type v} [inst_1 : CommRing A] (f : R →+* A),   W.map f = { a
₁ := f W.a₁, a₂…
· 使用定理 `map_ofNat`：map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : N
at) [Nat.AtLeastTwo n] : (f ofNat(n) : S) = OfNat.ofNat n
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Polynomial.map_sub`：∀ {R : Type u} [inst : Ring R] {p q : Polynomial R} 
{S : Type u_1} [inst_1 : Ring S] (f : R →+* S),   Polynomial.map f (p - q) = Pol
ynomial.…
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.map_add`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p + q)
 = Polyn…
· 使用定理 `Polynomial.map_ofNat`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [i
nst_1 : Semiring S] (f : R →+* S) (n : ℕ) [inst_2 : n.AtLeastTwo],   Polynomial.
map f (OfN…
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_polynomialX : (W.map f).polynomialX = W.polynomialX.map (mapRingHom f) := by
  simp only [polynomialX]
  map_simp
/-
**WeierstrassCurve.Affine.map_polynomialY** 是 Mathlib 中的一个引理，位于命名空间 `Weierstrass
Curve.Affine`。
形式化陈述：map_polynomialY : (W.map f).polynomialY = W.polynomialY.map (mapRingHom f)
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
· 使用定理 `map_ofNat`：map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : N
at) [Nat.AtLeastTwo n] : (f ofNat(n) : S) = OfNat.ofNat n
· 使用定理 `WeierstrassCurve.map.eq_1`：∀ {R : Type u} [inst : CommRing R] (W : Weier
strassCurve R) {A : Type v} [inst_1 : CommRing A] (f : R →+* A),   W.map f = { a
₁ := f W.a₁, a₂…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
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
· 使用定理 `Polynomial.map_add`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p + q)
 = Polyn…
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.map_ofNat`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [i
nst_1 : Semiring S] (f : R →+* S) (n : ℕ) [inst_2 : n.AtLeastTwo],   Polynomial.
map f (OfN…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_polynomialY : (W.map f).polynomialY = W.polynomialY.map (mapRingHom f) := by
  simp only [polynomialY]
  map_simp

variable {f} in
/-
**WeierstrassCurve.Affine.map_nonsingular** 是 Mathlib 中的一个引理，位于命名空间 `Weierstrass
Curve.Affine`。
形式化陈述：map_nonsingular (hf : Function.Injective f) (x y : R) : (W.map f).Nonsingu
lar (f x) (f y) ↔ W.Nonsingular x y
参数：hf : Function.Injective f；x y : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `WeierstrassCurve.Affine.map_equation`：map_equation (hf : Function.Inject
ive f) (x y : R) : (W.map f).Equation (f x) (f y) ↔ W.Equation x y
· 使用引理 `WeierstrassCurve.Affine.map_polynomialX`：map_polynomialX : (W.map f).pol
ynomialX = W.polynomialX.map (mapRingHom f)
· 使用引理 `Polynomial.map_mapRingHom_evalEval`：map_mapRingHom_evalEval (x y : R) : 
(p.map <| mapRingHom f).evalEval (f x) (f y) = f (p.evalEval x y)
· 使用定理 `map_ne_zero_iff`：∀ {R : Type u_10} {S : Type u_11} {F : Type u_12} [inst
 : Zero R] [inst_1 : Zero S] [inst_2 : FunLike F R S]   [ZeroHomClass F R S] (f 
: F),…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `WeierstrassCurve.Affine.map_polynomialY`：map_polynomialY : (W.map f).pol
ynomialY = W.polynomialY.map (mapRingHom f)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma map_nonsingular (hf : Function.Injective f) (x y : R) :
    (W.map f).Nonsingular (f x) (f y) ↔ W.Nonsingular x y := by
  simp only [Nonsingular, evalEval, W.map_equation hf, map_polynomialX, map_polynomialY,
    map_mapRingHom_evalEval, map_ne_zero_iff f hf]

variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Algebra R B] [Algebra S B]
  [IsScalarTower R S B] (f : A →ₐ[S] B)
/-
**WeierstrassCurve.Affine.map_baseChange** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassC
urve.Affine`。
形式化陈述：map_baseChange : (W⁄A).map f = W⁄B
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.map_baseChange`：map_baseChange {S : Type s} [CommRing S
] [Algebra R S] {A : Type v} [CommRing A] [Algebra R A] [Algebra S A] [IsScalarT
ower R S A] {B : Type…
-/
lemma map_baseChange : (W⁄A).map f = W⁄B :=
  WeierstrassCurve.map_baseChange W f
/-
**WeierstrassCurve.Affine.baseChange_polynomial** 是 Mathlib 中的一个引理，位于命名空间 `Weier
strassCurve.Affine`。
形式化陈述：baseChange_polynomial : (W⁄B).polynomial = (W⁄A).polynomial.map (mapRingHo
m f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WeierstrassCurve.Affine.map_polynomial`：map_polynomial : (W.map f).polyn
omial = W.polynomial.map (mapRingHom f)
· 使用引理 `WeierstrassCurve.Affine.map_baseChange`：map_baseChange : (W⁄A).map f = W
⁄B
-/
lemma baseChange_polynomial : (W⁄B).polynomial = (W⁄A).polynomial.map (mapRingHom f) := by
  rw [← map_polynomial, map_baseChange]

variable {W} in
/-
**WeierstrassCurve.Affine.Equation.baseChange** 是 Mathlib 中的一个定理，位于命名空间 `Weierst
rassCurve.Affine.Equation`。
形式化陈述：∀ {R : Type r} [inst : CommRing R] {W : WeierstrassCurve.Affine R} {S : Ty
pe s} [inst_1 : CommRing S] {A : Type u}   [inst_2 : CommRing A] {B : Type v} [i
nst_3 : CommRing B] [inst_4 : Algebra R S] [inst_5 : Algebra R A]   [inst_6 : Al
gebra S A] [IsScalarTower R S A] [inst_8 : Algebra R B] [inst_9 : Algebra S B] [
IsScalarTower R S B]   (f : A →ₐ[S] B) {x y : A}, (W.baseChange A).Equation x y 
→ (W.baseChange B).Equation (f x) (f y)
参数：f : A →ₐ[S] B；W.baseChange A；W.baseChange B；f x；f y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.toRingHom_eq_coe`：toRingHom_eq_coe (f : A ->ₐ[R] B) : f.toRingHom
 = f
· 使用引理 `WeierstrassCurve.Affine.map_baseChange`：map_baseChange : (W⁄A).map f = W
⁄B
· 使用定理 `WeierstrassCurve.Affine.Equation.map`：∀ {R : Type r} [inst : CommRing R]
 {W : WeierstrassCurve.Affine R} {S : Type s} [inst_1 : CommRing S] (f : R →+* S
)   {x y : R}, W.Equation …
-/
lemma Equation.baseChange {x y : A} (h : (W⁄A).Equation x y) : (W⁄B).Equation (f x) (f y) := by
  convert! Equation.map f.toRingHom h using 1
  rw [AlgHom.toRingHom_eq_coe, map_baseChange]

variable {f} in
/-
**WeierstrassCurve.Affine.baseChange_equation** 是 Mathlib 中的一个引理，位于命名空间 `Weierst
rassCurve.Affine`。
形式化陈述：baseChange_equation (hf : Function.Injective f) (x y : A) : (W⁄B).Equation
 (f x) (f y) ↔ (W⁄A).Equation x y
参数：hf : Function.Injective f；x y : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WeierstrassCurve.Affine.map_equation`：map_equation (hf : Function.Inject
ive f) (x y : R) : (W.map f).Equation (f x) (f y) ↔ W.Equation x y
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.toRingHom_eq_coe`：toRingHom_eq_coe (f : A ->ₐ[R] B) : f.toRingHom
 = f
· 使用引理 `WeierstrassCurve.Affine.map_baseChange`：map_baseChange : (W⁄A).map f = W
⁄B
· 使用定理 `RingHom.coe_coe`：coe_coe {F : Type*} [FunLike F α β] [RingHomClass F α β
] (f : F) : ((f : α ->+* β) : α -> β) = f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma baseChange_equation (hf : Function.Injective f) (x y : A) :
    (W⁄B).Equation (f x) (f y) ↔ (W⁄A).Equation x y := by
  rw [← map_equation _ hf, AlgHom.toRingHom_eq_coe, map_baseChange, RingHom.coe_coe]
/-
**WeierstrassCurve.Affine.baseChange_polynomialX** 是 Mathlib 中的一个引理，位于命名空间 `Weie
rstrassCurve.Affine`。
形式化陈述：baseChange_polynomialX : (W⁄B).polynomialX = (W⁄A).polynomialX.map (mapRin
gHom f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WeierstrassCurve.Affine.map_polynomialX`：map_polynomialX : (W.map f).pol
ynomialX = W.polynomialX.map (mapRingHom f)
· 使用引理 `WeierstrassCurve.Affine.map_baseChange`：map_baseChange : (W⁄A).map f = W
⁄B
-/
lemma baseChange_polynomialX : (W⁄B).polynomialX = (W⁄A).polynomialX.map (mapRingHom f) := by
  rw [← map_polynomialX, map_baseChange]
/-
**WeierstrassCurve.Affine.baseChange_polynomialY** 是 Mathlib 中的一个引理，位于命名空间 `Weie
rstrassCurve.Affine`。
形式化陈述：baseChange_polynomialY : (W⁄B).polynomialY = (W⁄A).polynomialY.map (mapRin
gHom f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WeierstrassCurve.Affine.map_polynomialY`：map_polynomialY : (W.map f).pol
ynomialY = W.polynomialY.map (mapRingHom f)
· 使用引理 `WeierstrassCurve.Affine.map_baseChange`：map_baseChange : (W⁄A).map f = W
⁄B
-/
lemma baseChange_polynomialY : (W⁄B).polynomialY = (W⁄A).polynomialY.map (mapRingHom f) := by
  rw [← map_polynomialY, map_baseChange]

variable {f} in
/-
**WeierstrassCurve.Affine.baseChange_nonsingular** 是 Mathlib 中的一个引理，位于命名空间 `Weie
rstrassCurve.Affine`。
形式化陈述：baseChange_nonsingular (hf : Function.Injective f) (x y : A) : (W⁄B).Nonsi
ngular (f x) (f y) ↔ (W⁄A).Nonsingular x y
参数：hf : Function.Injective f；x y : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WeierstrassCurve.Affine.map_nonsingular`：map_nonsingular (hf : Function.
Injective f) (x y : R) : (W.map f).Nonsingular (f x) (f y) ↔ W.Nonsingular x y
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.toRingHom_eq_coe`：toRingHom_eq_coe (f : A ->ₐ[R] B) : f.toRingHom
 = f
· 使用引理 `WeierstrassCurve.Affine.map_baseChange`：map_baseChange : (W⁄A).map f = W
⁄B
· 使用定理 `RingHom.coe_coe`：coe_coe {F : Type*} [FunLike F α β] [RingHomClass F α β
] (f : F) : ((f : α ->+* β) : α -> β) = f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma baseChange_nonsingular (hf : Function.Injective f) (x y : A) :
    (W⁄B).Nonsingular (f x) (f y) ↔ (W⁄A).Nonsingular x y := by
  rw [← map_nonsingular _ hf, AlgHom.toRingHom_eq_coe, map_baseChange, RingHom.coe_coe]

end Affine

end WeierstrassCurve

