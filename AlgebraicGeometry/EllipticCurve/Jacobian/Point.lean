/-
Copyright (c) 2025 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Formula

/-!
# Nonsingular points and the group law in Jacobian coordinates

Let `W` be a Weierstrass curve over a field `F`. The nonsingular Jacobian points of `W` can be
endowed with a group law, which is uniquely determined by the formulae in
`Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Formula.lean` and follows from an equivalence with
the nonsingular points in affine coordinates.

This file defines the group law on nonsingular Jacobian points.

## Main definitions

* `WeierstrassCurve.Jacobian.neg`: the negation of a point representative.
* `WeierstrassCurve.Jacobian.negMap`: the negation of a point class.
* `WeierstrassCurve.Jacobian.add`: the addition of two point representatives.
* `WeierstrassCurve.Jacobian.addMap`: the addition of two point classes.
* `WeierstrassCurve.Jacobian.Point`: a nonsingular Jacobian point.
* `WeierstrassCurve.Jacobian.Point.neg`: the negation of a nonsingular Jacobian point.
* `WeierstrassCurve.Jacobian.Point.add`: the addition of two nonsingular Jacobian points.
* `WeierstrassCurve.Jacobian.Point.toAffineAddEquiv`: the equivalence between the type of
  nonsingular Jacobian points with the type of nonsingular points in affine coordinates.

## Main statements

* `WeierstrassCurve.Jacobian.nonsingular_neg`: negation preserves the nonsingular condition.
* `WeierstrassCurve.Jacobian.nonsingular_add`: addition preserves the nonsingular condition.
* `WeierstrassCurve.Jacobian.Point.instAddCommGroup`: the type of nonsingular Jacobian points forms
  an abelian group under addition.

## Implementation notes

Note that `W(X, Y, Z)` and its partial derivatives are independent of the point representative, and
the nonsingularity condition already implies `(x, y, z) ≠ (0, 0, 0)`, so a nonsingular Jacobian
point on `W` can be given by `[x : y : z]` and the nonsingular condition on any representative.

A nonsingular Jacobian point representative can be converted to a nonsingular point in affine
coordinates using `WeierstrassCurve.Jacobian.Point.toAffine`, which lifts to a map on nonsingular
Jacobian points using `WeierstrassCurve.Jacobian.Point.toAffineLift`. Conversely, a nonsingular
point in affine coordinates can be converted to a nonsingular Jacobian point using
`WeierstrassCurve.Jacobian.Point.fromAffine` or `WeierstrassCurve.Affine.Point.toJacobian`.

Whenever possible, all changes to documentation and naming of definitions and theorems should be
mirrored in `Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Point.lean`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, Jacobian, point, group law
-/

@[expose] public section

local notation3 "x" => (0 : Fin 3)

local notation3 "y" => (1 : Fin 3)

local notation3 "z" => (2 : Fin 3)

open MvPolynomial

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_C, map_X, map_neg, map_add, map_sub, map_mul, map_pow,
    map_div₀, WeierstrassCurve.map, Function.comp_apply])

universe r s u v

namespace WeierstrassCurve

variable {R : Type r} {S : Type s} {A F : Type u} {B K : Type v} [CommRing R] [CommRing S]
  [CommRing A] [CommRing B] [Field F] [Field K] {W' : Jacobian R} {W : Jacobian F}

namespace Jacobian

/-! ## Negation on Jacobian point representatives -/

variable (W') in
/-- The negation of a Jacobian point representative on a Weierstrass curve. -/
/-
**WeierstrassCurve.Jacobian.neg** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve.Jaco
bian`。
形式化陈述：neg (P : Fin 3 -> R) : Fin 3 -> R
参数：P : Fin 3 -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The negation of a Jacobian point representative on a Weierstrass curve.
-/
def neg (P : Fin 3 → R) : Fin 3 → R :=
  ![P x, W'.negY P, P z]
/-
**WeierstrassCurve.Jacobian.neg_X** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve.Ja
cobian`。
形式化陈述：neg_X (P : Fin 3 -> R) : W'.neg P x = P x
参数：P : Fin 3 -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma neg_X (P : Fin 3 → R) : W'.neg P x = P x :=
  rfl
/-
**WeierstrassCurve.Jacobian.neg_Y** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve.Ja
cobian`。
形式化陈述：neg_Y (P : Fin 3 -> R) : W'.neg P y = W'.negY P
参数：P : Fin 3 -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma neg_Y (P : Fin 3 → R) : W'.neg P y = W'.negY P :=
  rfl
/-
**WeierstrassCurve.Jacobian.neg_Z** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve.Ja
cobian`。
形式化陈述：neg_Z (P : Fin 3 -> R) : W'.neg P z = P z
参数：P : Fin 3 -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma neg_Z (P : Fin 3 → R) : W'.neg P z = P z :=
  rfl
/-
**WeierstrassCurve.Jacobian.neg_smul** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve
.Jacobian`。
形式化陈述：∀ {R : Type r} [inst : CommRing R] {W' : WeierstrassCurve.Jacobian R} (P :
 Fin 3 → R) (u : R),   W'.neg (u • P) = u • W'.neg P
参数：P : Fin 3 → R；u : R；u • P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.Jacobian.neg.eq_1`：∀ {R : Type r} [inst : CommRing R] (
W' : WeierstrassCurve.Jacobian R) (P : Fin 3 → R), W'.neg P = ![P 0, W'.negY P, 
P 2]
· 使用引理 `WeierstrassCurve.Jacobian.negY_smul`：negY_smul (P : Fin 3 -> R) (u : R) 
: W'.negY (u • P) = u ^ 3 * W'.negY P
-/
protected lemma neg_smul (P : Fin 3 → R) (u : R) : W'.neg (u • P) = u • W'.neg P := by
  rw [neg, negY_smul]
  rfl
/-
**WeierstrassCurve.Jacobian.neg_smul_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Weierstras
sCurve.Jacobian`。
形式化陈述：neg_smul_equiv (P : Fin 3 -> R) {u : R} (hu : IsUnit u) : W'.neg (u • P) ≈
 W'.neg P
参数：P : Fin 3 -> R；hu : IsUnit u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WeierstrassCurve.Jacobian.neg_smul`：∀ {R : Type r} [inst : CommRing R] {
W' : WeierstrassCurve.Jacobian R} (P : Fin 3 → R) (u : R),   W'.neg (u • P) = u 
• W'.neg P
-/
lemma neg_smul_equiv (P : Fin 3 → R) {u : R} (hu : IsUnit u) : W'.neg (u • P) ≈ W'.neg P :=
  ⟨hu.unit, (W'.neg_smul ..).symm⟩
/-
**WeierstrassCurve.Jacobian.neg_equiv** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurv
e.Jacobian`。
形式化陈述：neg_equiv {P Q : Fin 3 -> R} (h : P ≈ Q) : W'.neg P ≈ W'.neg Q
参数：h : P ≈ Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Jacobian.neg_smul_equiv`：neg_smul_equiv (P : Fin 3 -> R
) {u : R} (hu : IsUnit u) : W'.neg (u • P) ≈ W'.neg P
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
lemma neg_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : W'.neg P ≈ W'.neg Q := by
  rcases h with ⟨u, rfl⟩
  exact neg_smul_equiv Q u.isUnit
/-
**WeierstrassCurve.Jacobian.neg_of_Z_eq_zero'** 是 Mathlib 中的一个引理，位于命名空间 `Weierst
rassCurve.Jacobian`。
形式化陈述：neg_of_Z_eq_zero' {P : Fin 3 -> R} (hPz : P z = 0) : W'.neg P = ![P x, -P 
y, 0]
参数：hPz : P z = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.Jacobian.neg.eq_1`：∀ {R : Type r} [inst : CommRing R] (
W' : WeierstrassCurve.Jacobian R) (P : Fin 3 → R), W'.neg P = ![P 0, W'.negY P, 
P 2]
· 使用引理 `WeierstrassCurve.Jacobian.negY_of_Z_eq_zero`：negY_of_Z_eq_zero {P : Fin 
3 -> R} (hPz : P z = 0) : W'.negY P = -P y
-/
lemma neg_of_Z_eq_zero' {P : Fin 3 → R} (hPz : P z = 0) : W'.neg P = ![P x, -P y, 0] := by
  rw [neg, negY_of_Z_eq_zero hPz, hPz]
/-
**WeierstrassCurve.Jacobian.neg_of_Z_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Weierstr
assCurve.Jacobian`。
形式化陈述：neg_of_Z_eq_zero {P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z = 0) :
 W.neg P = -(P y / P x) • ![1, 1, 0]
参数：hP : W.Nonsingular P；hPz : P z = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsUnit.pow`：∀ {M : Type u_1} [inst : Monoid M] {a : M} (n : ℕ), IsUnit a
 → IsUnit (a ^ n)
· 使用引理 `WeierstrassCurve.Jacobian.isUnit_X_of_Z_eq_zero`：isUnit_X_of_Z_eq_zero {
P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z = 0) : IsUnit (P x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.neg_of_Z_eq_zero'`：neg_of_Z_eq_zero' {P : Fin 
3 -> R} (hPz : P z = 0) : W'.neg P = ![P x, -P y, 0]
· 使用引理 `WeierstrassCurve.Jacobian.smul_fin3`：smul_fin3 (P : Fin 3 -> R) (u : R) 
: u • P = ![u ^ 2 * P x, u ^ 3 * P y, u * P z]
· 使用引理 `neg_sq`：neg_sq (a : R) : (-a) ^ 2 = a ^ 2
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WeierstrassCurve.Jacobian.equation_of_Z_eq_zero`：equation_of_Z_eq_zero {
P : Fin 3 -> R} (hPz : P z = 0) : W'.Equation P ↔ P y ^ 2 = P x ^ 3
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `IsUnit.mul_div_cancel_left`：∀ {α : Type u} [inst : DivisionCommMonoid α]
 {a : α}, IsUnit a → ∀ (b : α), a * b / a = b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `Odd.neg_pow`：Odd.neg_pow : Odd n -> forall a : α, (-a) ^ n = -a ^ n
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
lemma neg_of_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z = 0) :
    W.neg P = -(P y / P x) • ![1, 1, 0] := by
  have hX {n : ℕ} : IsUnit <| P x ^ n := (isUnit_X_of_Z_eq_zero hP hPz).pow n
  erw [neg_of_Z_eq_zero' hPz, smul_fin3, neg_sq, div_pow, (equation_of_Z_eq_zero hPz).mp hP.left,
    pow_succ, hX.mul_div_cancel_left, mul_one, Odd.neg_pow <| by decide, div_pow, pow_succ,
    (equation_of_Z_eq_zero hPz).mp hP.left, hX.mul_div_cancel_left, mul_one, mul_zero]
/-
**WeierstrassCurve.Jacobian.neg_of_Z_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Weierstr
assCurve.Jacobian`。
形式化陈述：neg_of_Z_ne_zero {P : Fin 3 -> F} (hPz : P z != 0) : W.neg P = P z • ![P x
 / P z ^ 2, W.toAffine.negY (P x / P z ^ 2) (P y / P z ^ 3), 1]
参数：hPz : P z != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.Jacobian.neg.eq_1`：∀ {R : Type r} [inst : CommRing R] (
W' : WeierstrassCurve.Jacobian R) (P : Fin 3 → R), W'.neg P = ![P 0, W'.negY P, 
P 2]
· 使用引理 `WeierstrassCurve.Jacobian.smul_fin3`：smul_fin3 (P : Fin 3 -> R) (u : R) 
: u • P = ![u ^ 2 * P x, u ^ 3 * P y, u * P z]
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WeierstrassCurve.Jacobian.negY_of_Z_ne_zero`：negY_of_Z_ne_zero {P : Fin 
3 -> F} (hPz : P z != 0) : W.negY P / P z ^ 3 = W.toAffine.negY (P x / P z ^ 2) 
(P y / P z ^ 3)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma neg_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.neg P = P z • ![P x / P z ^ 2, W.toAffine.negY (P x / P z ^ 2) (P y / P z ^ 3), 1] := by
  rw [neg, smul_fin3]
  simp only [fin3_def_ext]
  rw [mul_div_cancel₀ _ <| pow_ne_zero 2 hPz, ← negY_of_Z_ne_zero hPz,
    mul_div_cancel₀ _ <| pow_ne_zero 3 hPz, mul_one]
/-
**WeierstrassCurve.Jacobian.nonsingular_neg_of_Z_ne_zero** 是 Mathlib 中的一个引理，位于命名
空间 `WeierstrassCurve.Jacobian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma nonsingular_neg_of_Z_ne_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z ≠ 0) :
    W.Nonsingular ![P x / P z ^ 2, W.toAffine.negY (P x / P z ^ 2) (P y / P z ^ 3), 1] :=
  (nonsingular_some ..).mpr <| (Affine.nonsingular_neg ..).mpr <|
    (nonsingular_of_Z_ne_zero hPz).mp hP
/-
**WeierstrassCurve.Jacobian.nonsingular_neg** 是 Mathlib 中的一个引理，位于命名空间 `Weierstra
ssCurve.Jacobian`。
形式化陈述：nonsingular_neg {P : Fin 3 -> F} (hP : W.Nonsingular P) : W.Nonsingular W.
neg P
参数：hP : W.Nonsingular P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.neg_of_Z_eq_zero`：neg_of_Z_eq_zero {P : Fin 3 
-> F} (hP : W.Nonsingular P) (hPz : P z = 0) : W.neg P = -(P y / P x) • ![1, 1, 
0]
· 使用引理 `WeierstrassCurve.Jacobian.nonsingular_smul`：nonsingular_smul (P : Fin 3 
-> R) {u : R} (hu : IsUnit u) : W'.Nonsingular (u • P) ↔ W'.Nonsingular P
· 使用定理 `IsUnit.neg`：∀ {α : Type u} [inst : Monoid α] [inst_1 : HasDistribNeg α] 
{a : α}, IsUnit a → IsUnit (-a)
· 使用引理 `IsUnit.div`：div (ha : IsUnit a) (hb : IsUnit b) : IsUnit (a / b)
· 使用引理 `WeierstrassCurve.Jacobian.isUnit_Y_of_Z_eq_zero`：isUnit_Y_of_Z_eq_zero {
P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z = 0) : IsUnit (P y)
· 使用引理 `WeierstrassCurve.Jacobian.isUnit_X_of_Z_eq_zero`：isUnit_X_of_Z_eq_zero {
P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z = 0) : IsUnit (P x)
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用引理 `WeierstrassCurve.Jacobian.neg_of_Z_ne_zero`：neg_of_Z_ne_zero {P : Fin 3 
-> F} (hPz : P z != 0) : W.neg P = P z • ![P x / P z ^ 2, W.toAffine.negY (P x /
 P z ^ 2) (P y / P z ^ 3), 1]
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `_private.Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point.0.Weiers
trassCurve.Jacobian.nonsingular_neg_of_Z_ne_zero`：∀ {F : Type u} [inst : Field F
] {W : WeierstrassCurve.Jacobian F} {P : Fin 3 → F},   W.Nonsingular P → P 2 ≠ 0
 → W.Nonsingular ![P 0 / P 2 ^…
-/
lemma nonsingular_neg {P : Fin 3 → F} (hP : W.Nonsingular P) : W.Nonsingular <| W.neg P := by
  by_cases hPz : P z = 0
  · simp only [neg_of_Z_eq_zero hP hPz, nonsingular_smul _
        ((isUnit_Y_of_Z_eq_zero hP hPz).div <| isUnit_X_of_Z_eq_zero hP hPz).neg, nonsingular_zero]
  · simp only [neg_of_Z_ne_zero hPz, nonsingular_smul _ <| Ne.isUnit hPz,
      nonsingular_neg_of_Z_ne_zero hP hPz]
/-
**WeierstrassCurve.Jacobian.addZ_neg** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve
.Jacobian`。
形式化陈述：addZ_neg (P : Fin 3 -> R) : addZ P (W'.neg P) = 0
参数：P : Fin 3 -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Jacobian.addZ_of_X_eq`：addZ_of_X_eq {P Q : Fin 3 -> R} 
(hx : P x * Q z ^ 2 = Q x * P z ^ 2) : addZ P Q = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma addZ_neg (P : Fin 3 → R) : addZ P (W'.neg P) = 0 :=
  addZ_of_X_eq rfl
/-
**WeierstrassCurve.Jacobian.addX_neg** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve
.Jacobian`。
形式化陈述：addX_neg {P : Fin 3 -> R} (hP : W'.Equation P) : W'.addX P (W'.neg P) = W'
.dblZ P ^ 2
参数：hP : W'.Equation P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.LinearCombination.mul_const_eq`：mul_const_eq [Mul α] (p :
 b = c) (a : α) : a * b = a * c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WeierstrassCurve.Jacobian.equation_iff`：equation_iff (P : Fin 3 -> R) : 
W'.Equation P ↔ P y ^ 2 + W'.a₁ * P x * P y * P z + W'.a₃ * P y * P z ^ 3 - (P x
 ^ 3 + W'.a₂ * P x ^ 2 * P z…
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.Jacobian.addX.eq_1`：∀ {R : Type r} [inst : CommRing R] 
(W' : WeierstrassCurve.Jacobian R) (P Q : Fin 3 → R),   W'.addX P Q =     P 0 * 
Q 0 ^ 2 * P 2 ^ 2 - 2 * P…
· 使用引理 `WeierstrassCurve.Jacobian.neg_X`：neg_X (P : Fin 3 -> R) : W'.neg P x = P
 x
· 使用引理 `WeierstrassCurve.Jacobian.neg_Y`：neg_Y (P : Fin 3 -> R) : W'.neg P y = W
'.negY P
· 使用引理 `WeierstrassCurve.Jacobian.neg_Z`：neg_Z (P : Fin 3 -> R) : W'.neg P z = P
 z
· 使用定理 `WeierstrassCurve.Jacobian.dblZ.eq_1`：∀ {R : Type r} [inst : CommRing R] 
(W' : WeierstrassCurve.Jacobian R) (P : Fin 3 → R),   W'.dblZ P = P 2 * (P 1 - W
'.negY P)
· 使用定理 `WeierstrassCurve.Jacobian.negY.eq_1`：∀ {R : Type r} [inst : CommRing R] 
(W' : WeierstrassCurve.Jacobian R) (P : Fin 3 → R),   W'.negY P = -P 1 - W'.a₁ *
 P 0 * P 2 - W'.a₃ * P 2 …
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
（共 68 条，此处仅展示前 30 条）
-/
lemma addX_neg {P : Fin 3 → R} (hP : W'.Equation P) : W'.addX P (W'.neg P) = W'.dblZ P ^ 2 := by
  linear_combination (norm := (rw [addX, neg_X, neg_Y, neg_Z, dblZ, negY]; ring1))
    -2 * P z ^ 2 * (equation_iff _).mp hP
/-
**WeierstrassCurve.Jacobian.negAddY_neg** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCu
rve.Jacobian`。
形式化陈述：negAddY_neg {P : Fin 3 -> R} (hP : W'.Equation P) : W'.negAddY P (W'.neg P
) = W'.dblZ P ^ 3
参数：hP : W'.Equation P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.LinearCombination.mul_const_eq`：mul_const_eq [Mul α] (p :
 b = c) (a : α) : a * b = a * c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WeierstrassCurve.Jacobian.equation_iff`：equation_iff (P : Fin 3 -> R) : 
W'.Equation P ↔ P y ^ 2 + W'.a₁ * P x * P y * P z + W'.a₃ * P y * P z ^ 3 - (P x
 ^ 3 + W'.a₂ * P x ^ 2 * P z…
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.Jacobian.negAddY.eq_1`：∀ {R : Type r} [inst : CommRing 
R] (W' : WeierstrassCurve.Jacobian R) (P Q : Fin 3 → R),   W'.negAddY P Q =     
-P 1 * Q 0 ^ 3 * P 2 ^ 3 + 2…
· 使用引理 `WeierstrassCurve.Jacobian.neg_X`：neg_X (P : Fin 3 -> R) : W'.neg P x = P
 x
· 使用引理 `WeierstrassCurve.Jacobian.neg_Y`：neg_Y (P : Fin 3 -> R) : W'.neg P y = W
'.negY P
· 使用引理 `WeierstrassCurve.Jacobian.neg_Z`：neg_Z (P : Fin 3 -> R) : W'.neg P z = P
 z
· 使用定理 `WeierstrassCurve.Jacobian.dblZ.eq_1`：∀ {R : Type r} [inst : CommRing R] 
(W' : WeierstrassCurve.Jacobian R) (P : Fin 3 → R),   W'.dblZ P = P 2 * (P 1 - W
'.negY P)
· 使用定理 `WeierstrassCurve.Jacobian.negY.eq_1`：∀ {R : Type r} [inst : CommRing R] 
(W' : WeierstrassCurve.Jacobian R) (P : Fin 3 → R),   W'.negY P = -P 1 - W'.a₁ *
 P 0 * P 2 - W'.a₃ * P 2 …
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
（共 69 条，此处仅展示前 30 条）
-/
lemma negAddY_neg {P : Fin 3 → R} (hP : W'.Equation P) :
    W'.negAddY P (W'.neg P) = W'.dblZ P ^ 3 := by
  linear_combination (norm := (rw [negAddY, neg_X, neg_Y, neg_Z, dblZ, negY]; ring1))
    -2 * P z ^ 3 * (P y - W'.negY P) * (equation_iff _).mp hP
/-
**WeierstrassCurve.Jacobian.addY_neg** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve
.Jacobian`。
形式化陈述：addY_neg {P : Fin 3 -> R} (hP : W'.Equation P) : W'.addY P (W'.neg P) = -W
'.dblZ P ^ 3
参数：hP : W'.Equation P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.Jacobian.addY.eq_1`：∀ {R : Type r} [inst : CommRing R] 
(W' : WeierstrassCurve.Jacobian R) (P Q : Fin 3 → R),   W'.addY P Q = W'.negY ![
W'.addX P Q, W'.negAddY P…
· 使用引理 `WeierstrassCurve.Jacobian.addX_neg`：addX_neg {P : Fin 3 -> R} (hP : W'.E
quation P) : W'.addX P (W'.neg P) = W'.dblZ P ^ 2
· 使用引理 `WeierstrassCurve.Jacobian.negAddY_neg`：negAddY_neg {P : Fin 3 -> R} (hP 
: W'.Equation P) : W'.negAddY P (W'.neg P) = W'.dblZ P ^ 3
· 使用引理 `WeierstrassCurve.Jacobian.addZ_neg`：addZ_neg (P : Fin 3 -> R) : addZ P (
W'.neg P) = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `WeierstrassCurve.Jacobian.negY_of_Z_eq_zero`：negY_of_Z_eq_zero {P : Fin 
3 -> R} (hPz : P z = 0) : W'.negY P = -P y
-/
lemma addY_neg {P : Fin 3 → R} (hP : W'.Equation P) : W'.addY P (W'.neg P) = -W'.dblZ P ^ 3 := by
  rw [addY, addX_neg hP, negAddY_neg hP, addZ_neg, negY_of_Z_eq_zero rfl]
  rfl
/-
**WeierstrassCurve.Jacobian.addXYZ_neg** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCur
ve.Jacobian`。
形式化陈述：addXYZ_neg {P : Fin 3 -> R} (hP : W'.Equation P) : W'.addXYZ P (W'.neg P) 
= -W'.dblZ P • ![1, 1, 0]
参数：hP : W'.Equation P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.Jacobian.addXYZ.eq_1`：∀ {R : Type r} [inst : CommRing R
] (W' : WeierstrassCurve.Jacobian R) (P Q : Fin 3 → R),   W'.addXYZ P Q = ![W'.a
ddX P Q, W'.addY P Q, Weier…
· 使用引理 `WeierstrassCurve.Jacobian.addX_neg`：addX_neg {P : Fin 3 -> R} (hP : W'.E
quation P) : W'.addX P (W'.neg P) = W'.dblZ P ^ 2
· 使用引理 `WeierstrassCurve.Jacobian.addY_neg`：addY_neg {P : Fin 3 -> R} (hP : W'.E
quation P) : W'.addY P (W'.neg P) = -W'.dblZ P ^ 3
· 使用引理 `WeierstrassCurve.Jacobian.addZ_neg`：addZ_neg (P : Fin 3 -> R) : addZ P (
W'.neg P) = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `WeierstrassCurve.Jacobian.smul_fin3`：smul_fin3 (P : Fin 3 -> R) (u : R) 
: u • P = ![u ^ 2 * P x, u ^ 3 * P y, u * P z]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `Odd.neg_pow`：Odd.neg_pow : Odd n -> forall a : α, (-a) ^ n = -a ^ n
· 使用定理 `eq_true_of_decide`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma addXYZ_neg {P : Fin 3 → R} (hP : W'.Equation P) :
    W'.addXYZ P (W'.neg P) = -W'.dblZ P • ![1, 1, 0] := by
  rw [addXYZ, addX_neg hP, addY_neg hP, addZ_neg, smul_fin3]
  simp +decide [fin3_def_ext, Odd.neg_pow]

variable (W') in
/-- The negation of a Jacobian point class on a Weierstrass curve `W`.

If `P` is a Jacobian point representative on `W`, then `W.negMap ⟦P⟧` is definitionally equivalent
to `W.neg P`. -/
/-
**WeierstrassCurve.Jacobian.negMap** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve.J
acobian`。
形式化陈述：negMap (P : PointClass R) : PointClass R
参数：P : PointClass R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Jacobian.neg_equiv`：neg_equiv {P Q : Fin 3 -> R} (h : P
 ≈ Q) : W'.neg P ≈ W'.neg Q

--- 原说明 ---
The negation of a Jacobian point class on a Weierstrass curve `W`.

If `P` is a Jacobian point representative on `W`, then `W.negMap ⟦P⟧` is definit
ionally equivalent
to `W.neg P`.
-/
def negMap (P : PointClass R) : PointClass R :=
  P.map W'.neg fun _ _ => neg_equiv
/-
**WeierstrassCurve.Jacobian.negMap_eq** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurv
e.Jacobian`。
形式化陈述：negMap_eq (P : Fin 3 -> R) : W'.negMap ⟦P⟧ = ⟦W'.neg P⟧
参数：P : Fin 3 -> R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma negMap_eq (P : Fin 3 → R) : W'.negMap ⟦P⟧ = ⟦W'.neg P⟧ :=
  rfl
/-
**WeierstrassCurve.Jacobian.negMap_of_Z_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Weier
strassCurve.Jacobian`。
形式化陈述：negMap_of_Z_eq_zero {P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z = 0
) : W.negMap ⟦P⟧ = ⟦![1, 1, 0]⟧
参数：hP : W.Nonsingular P；hPz : P z = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.negMap_eq`：negMap_eq (P : Fin 3 -> R) : W'.neg
Map ⟦P⟧ = ⟦W'.neg P⟧
· 使用引理 `WeierstrassCurve.Jacobian.neg_of_Z_eq_zero`：neg_of_Z_eq_zero {P : Fin 3 
-> F} (hP : W.Nonsingular P) (hPz : P z = 0) : W.neg P = -(P y / P x) • ![1, 1, 
0]
· 使用引理 `WeierstrassCurve.Jacobian.smul_eq`：smul_eq (P : Fin 3 -> R) {u : R} (hu 
: IsUnit u) : (⟦u • P⟧ : PointClass R) = ⟦P⟧
· 使用定理 `IsUnit.neg`：∀ {α : Type u} [inst : Monoid α] [inst_1 : HasDistribNeg α] 
{a : α}, IsUnit a → IsUnit (-a)
· 使用引理 `IsUnit.div`：div (ha : IsUnit a) (hb : IsUnit b) : IsUnit (a / b)
· 使用引理 `WeierstrassCurve.Jacobian.isUnit_Y_of_Z_eq_zero`：isUnit_Y_of_Z_eq_zero {
P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z = 0) : IsUnit (P y)
· 使用引理 `WeierstrassCurve.Jacobian.isUnit_X_of_Z_eq_zero`：isUnit_X_of_Z_eq_zero {
P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z = 0) : IsUnit (P x)
-/
lemma negMap_of_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z = 0) :
    W.negMap ⟦P⟧ = ⟦![1, 1, 0]⟧ := by
  rw [negMap_eq, neg_of_Z_eq_zero hP hPz,
    smul_eq _ ((isUnit_Y_of_Z_eq_zero hP hPz).div <| isUnit_X_of_Z_eq_zero hP hPz).neg]
/-
**WeierstrassCurve.Jacobian.negMap_of_Z_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Weier
strassCurve.Jacobian`。
形式化陈述：negMap_of_Z_ne_zero {P : Fin 3 -> F} (hPz : P z != 0) : W.negMap ⟦P⟧ = ⟦![
P x / P z ^ 2, W.toAffine.negY (P x / P z ^ 2) (P y / P z ^ 3), 1]⟧
参数：hPz : P z != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.negMap_eq`：negMap_eq (P : Fin 3 -> R) : W'.neg
Map ⟦P⟧ = ⟦W'.neg P⟧
· 使用引理 `WeierstrassCurve.Jacobian.neg_of_Z_ne_zero`：neg_of_Z_ne_zero {P : Fin 3 
-> F} (hPz : P z != 0) : W.neg P = P z • ![P x / P z ^ 2, W.toAffine.negY (P x /
 P z ^ 2) (P y / P z ^ 3), 1]
· 使用引理 `WeierstrassCurve.Jacobian.smul_eq`：smul_eq (P : Fin 3 -> R) {u : R} (hu 
: IsUnit u) : (⟦u • P⟧ : PointClass R) = ⟦P⟧
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
-/
lemma negMap_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.negMap ⟦P⟧ = ⟦![P x / P z ^ 2, W.toAffine.negY (P x / P z ^ 2) (P y / P z ^ 3), 1]⟧ := by
  rw [negMap_eq, neg_of_Z_ne_zero hPz, smul_eq _ <| Ne.isUnit hPz]
/-
**WeierstrassCurve.Jacobian.nonsingularLift_negMap** 是 Mathlib 中的一个引理，位于命名空间 `We
ierstrassCurve.Jacobian`。
形式化陈述：nonsingularLift_negMap {P : PointClass F} (hP : W.NonsingularLift P) : W.N
onsingularLift W.negMap P
参数：hP : W.NonsingularLift P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Jacobian.nonsingular_neg`：nonsingular_neg {P : Fin 3 ->
 F} (hP : W.Nonsingular P) : W.Nonsingular W.neg P
-/
lemma nonsingularLift_negMap {P : PointClass F} (hP : W.NonsingularLift P) :
    W.NonsingularLift <| W.negMap P := by
  rcases P with ⟨_⟩
  exact nonsingular_neg hP

/-! ## Addition on Jacobian point representatives -/

open scoped Classical in
variable (W') in
/-- The addition of two Jacobian point representatives on a Weierstrass curve. -/
/-
**WeierstrassCurve.Jacobian.add** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve.Jaco
bian`。
形式化陈述：add (P Q : Fin 3 -> R) : Fin 3 -> R
参数：P Q : Fin 3 -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The addition of two Jacobian point representatives on a Weierstrass curve.
-/
noncomputable def add (P Q : Fin 3 → R) : Fin 3 → R :=
  if P ≈ Q then W'.dblXYZ P else W'.addXYZ P Q
/-
**WeierstrassCurve.Jacobian.add_of_equiv** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassC
urve.Jacobian`。
形式化陈述：add_of_equiv {P Q : Fin 3 -> R} (h : P ≈ Q) : W'.add P Q = W'.dblXYZ P
参数：h : P ≈ Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma add_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : W'.add P Q = W'.dblXYZ P :=
  if_pos h
/-
**WeierstrassCurve.Jacobian.add_smul_of_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Weierst
rassCurve.Jacobian`。
形式化陈述：add_smul_of_equiv {P Q : Fin 3 -> R} (h : P ≈ Q) {u v : R} (hu : IsUnit u)
 (hv : IsUnit v) : W'.add (u • P) (v • Q) = u ^ 4 • W'.add P Q
参数：h : P ≈ Q；hu : IsUnit u；hv : IsUnit v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.add_of_equiv`：add_of_equiv {P Q : Fin 3 -> R} 
(h : P ≈ Q) : W'.add P Q = W'.dblXYZ P
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WeierstrassCurve.Jacobian.smul_equiv_smul`：smul_equiv_smul (P Q : Fin 3 
-> R) {u v : R} (hu : IsUnit u) (hv : IsUnit v) : u • P ≈ v • Q ↔ P ≈ Q
· 使用引理 `WeierstrassCurve.Jacobian.dblXYZ_smul`：dblXYZ_smul (P : Fin 3 -> R) (u :
 R) : W'.dblXYZ (u • P) = u ^ 4 • W'.dblXYZ P
-/
lemma add_smul_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) {u v : R} (hu : IsUnit u) (hv : IsUnit v) :
    W'.add (u • P) (v • Q) = u ^ 4 • W'.add P Q := by
  rw [add_of_equiv <| (smul_equiv_smul P Q hu hv).mpr h, dblXYZ_smul, add_of_equiv h]
/-
**WeierstrassCurve.Jacobian.add_self** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve
.Jacobian`。
形式化陈述：add_self (P : Fin 3 -> R) : W'.add P P = W'.dblXYZ P
参数：P : Fin 3 -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Jacobian.add_of_equiv`：add_of_equiv {P Q : Fin 3 -> R} 
(h : P ≈ Q) : W'.add P Q = W'.dblXYZ P
· 使用定理 `Setoid.refl`：∀ {α : Sort u} [inst : Setoid α] (a : α), a ≈ a
-/
lemma add_self (P : Fin 3 → R) : W'.add P P = W'.dblXYZ P :=
  add_of_equiv <| Setoid.refl _
/-
**WeierstrassCurve.Jacobian.add_of_eq** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurv
e.Jacobian`。
形式化陈述：add_of_eq {P Q : Fin 3 -> R} (h : P = Q) : W'.add P Q = W'.dblXYZ P
参数：h : P = Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Jacobian.add_self`：add_self (P : Fin 3 -> R) : W'.add P
 P = W'.dblXYZ P
-/
lemma add_of_eq {P Q : Fin 3 → R} (h : P = Q) : W'.add P Q = W'.dblXYZ P :=
  h ▸ add_self P
/-
**WeierstrassCurve.Jacobian.add_of_not_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Weierstr
assCurve.Jacobian`。
形式化陈述：add_of_not_equiv {P Q : Fin 3 -> R} (h : ¬P ≈ Q) : W'.add P Q = W'.addXYZ 
P Q
参数：h : ¬P ≈ Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma add_of_not_equiv {P Q : Fin 3 → R} (h : ¬P ≈ Q) : W'.add P Q = W'.addXYZ P Q :=
  if_neg h
/-
**WeierstrassCurve.Jacobian.add_smul_of_not_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Wei
erstrassCurve.Jacobian`。
形式化陈述：add_smul_of_not_equiv {P Q : Fin 3 -> R} (h : ¬P ≈ Q) {u v : R} (hu : IsUn
it u) (hv : IsUnit v) : W'.add (u • P) (v • Q) = (u * v) ^ 2 • W'.add P Q
参数：h : ¬P ≈ Q；hu : IsUnit u；hv : IsUnit v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.add_of_not_equiv`：add_of_not_equiv {P Q : Fin 
3 -> R} (h : ¬P ≈ Q) : W'.add P Q = W'.addXYZ P Q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WeierstrassCurve.Jacobian.smul_equiv_smul`：smul_equiv_smul (P Q : Fin 3 
-> R) {u v : R} (hu : IsUnit u) (hv : IsUnit v) : u • P ≈ v • Q ↔ P ≈ Q
· 使用引理 `WeierstrassCurve.Jacobian.addXYZ_smul`：addXYZ_smul (P Q : Fin 3 -> R) (u
 v : R) : W'.addXYZ (u • P) (v • Q) = (u * v) ^ 2 • W'.addXYZ P Q
-/
lemma add_smul_of_not_equiv {P Q : Fin 3 → R} (h : ¬P ≈ Q) {u v : R} (hu : IsUnit u)
    (hv : IsUnit v) : W'.add (u • P) (v • Q) = (u * v) ^ 2 • W'.add P Q := by
  rw [add_of_not_equiv <| h.comp (smul_equiv_smul P Q hu hv).mp, addXYZ_smul, add_of_not_equiv h]
/-
**WeierstrassCurve.Jacobian.add_smul_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Weierstras
sCurve.Jacobian`。
形式化陈述：add_smul_equiv (P Q : Fin 3 -> R) {u v : R} (hu : IsUnit u) (hv : IsUnit v
) : W'.add (u • P) (v • Q) ≈ W'.add P Q
参数：P Q : Fin 3 -> R；hu : IsUnit u；hv : IsUnit v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WeierstrassCurve.Jacobian.add_smul_of_equiv`：add_smul_of_equiv {P Q : Fi
n 3 -> R} (h : P ≈ Q) {u v : R} (hu : IsUnit u) (hv : IsUnit v) : W'.add (u • P)
 (v • Q) = u ^ 4 • W'.add P Q
· 使用引理 `WeierstrassCurve.Jacobian.add_smul_of_not_equiv`：add_smul_of_not_equiv {
P Q : Fin 3 -> R} (h : ¬P ≈ Q) {u v : R} (hu : IsUnit u) (hv : IsUnit v) : W'.ad
d (u • P) (v • Q) = (u * v) ^ 2 • W'.…
-/
lemma add_smul_equiv (P Q : Fin 3 → R) {u v : R} (hu : IsUnit u) (hv : IsUnit v) :
    W'.add (u • P) (v • Q) ≈ W'.add P Q := by
  by_cases h : P ≈ Q
  · exact ⟨hu.unit ^ 4, by convert! (add_smul_of_equiv h hu hv).symm⟩
  · exact ⟨(hu.unit * hv.unit) ^ 2, by convert! (add_smul_of_not_equiv h hu hv).symm⟩
/-
**WeierstrassCurve.Jacobian.add_equiv** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurv
e.Jacobian`。
形式化陈述：add_equiv {P P' Q Q' : Fin 3 -> R} (hP : P ≈ P') (hQ : Q ≈ Q') : W'.add P 
Q ≈ W'.add P' Q'
参数：hP : P ≈ P'；hQ : Q ≈ Q'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Jacobian.add_smul_equiv`：add_smul_equiv (P Q : Fin 3 ->
 R) {u v : R} (hu : IsUnit u) (hv : IsUnit v) : W'.add (u • P) (v • Q) ≈ W'.add 
P Q
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
lemma add_equiv {P P' Q Q' : Fin 3 → R} (hP : P ≈ P') (hQ : Q ≈ Q') :
    W'.add P Q ≈ W'.add P' Q' := by
  rcases hP, hQ with ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
  exact add_smul_equiv P' Q' u.isUnit v.isUnit
/-
**WeierstrassCurve.Jacobian.add_of_Z_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Weierstr
assCurve.Jacobian`。
形式化陈述：add_of_Z_eq_zero {P Q : Fin 3 -> F} (hP : W.Nonsingular P) (hQ : W.Nonsing
ular Q) (hPz : P z = 0) (hQz : Q z = 0) : W.add P Q = P x ^ 2 • ![1, 1, 0]
参数：hP : W.Nonsingular P；hQ : W.Nonsingular Q；hPz : P z = 0；hQz : Q z = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.add_of_equiv`：add_of_equiv {P Q : Fin 3 -> R} 
(h : P ≈ Q) : W'.add P Q = W'.dblXYZ P
· 使用引理 `WeierstrassCurve.Jacobian.equiv_of_Z_eq_zero`：equiv_of_Z_eq_zero {P Q : 
Fin 3 -> F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) (hPz : P z = 0) (hQz :
 Q z = 0) : P ≈ Q
· 使用引理 `WeierstrassCurve.Jacobian.dblXYZ_of_Z_eq_zero`：dblXYZ_of_Z_eq_zero {P : 
Fin 3 -> R} (hP : W'.Equation P) (hPz : P z = 0) : W'.dblXYZ P = P x ^ 2 • ![1, 
1, 0]
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma add_of_Z_eq_zero {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (hPz : P z = 0) (hQz : Q z = 0) : W.add P Q = P x ^ 2 • ![1, 1, 0] := by
  rw [add_of_equiv <| equiv_of_Z_eq_zero hP hQ hPz hQz, dblXYZ_of_Z_eq_zero hP.left hPz]
/-
**WeierstrassCurve.Jacobian.add_of_Z_eq_zero_left** 是 Mathlib 中的一个引理，位于命名空间 `Wei
erstrassCurve.Jacobian`。
形式化陈述：add_of_Z_eq_zero_left {P Q : Fin 3 -> R} (hP : W'.Equation P) (hPz : P z =
 0) (hQz : Q z != 0) : W'.add P Q = (P x * Q z) • Q
参数：hP : W'.Equation P；hPz : P z = 0；hQz : Q z != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.add_of_not_equiv`：add_of_not_equiv {P Q : Fin 
3 -> R} (h : ¬P ≈ Q) : W'.add P Q = W'.addXYZ P Q
· 使用引理 `WeierstrassCurve.Jacobian.not_equiv_of_Z_eq_zero_left`：not_equiv_of_Z_eq
_zero_left {P Q : Fin 3 -> R} (hPz : P z = 0) (hQz : Q z != 0) : ¬P ≈ Q
· 使用引理 `WeierstrassCurve.Jacobian.addXYZ_of_Z_eq_zero_left`：addXYZ_of_Z_eq_zero_
left {P Q : Fin 3 -> R} (hP : W'.Equation P) (hPz : P z = 0) : W'.addXYZ P Q = (
P x * Q z) • Q
-/
lemma add_of_Z_eq_zero_left {P Q : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) (hQz : Q z ≠ 0) :
    W'.add P Q = (P x * Q z) • Q := by
  rw [add_of_not_equiv <| not_equiv_of_Z_eq_zero_left hPz hQz, addXYZ_of_Z_eq_zero_left hP hPz]
/-
**WeierstrassCurve.Jacobian.add_of_Z_eq_zero_right** 是 Mathlib 中的一个引理，位于命名空间 `We
ierstrassCurve.Jacobian`。
形式化陈述：add_of_Z_eq_zero_right {P Q : Fin 3 -> R} (hQ : W'.Equation Q) (hPz : P z 
!= 0) (hQz : Q z = 0) : W'.add P Q = -(Q x * P z) • P
参数：hQ : W'.Equation Q；hPz : P z != 0；hQz : Q z = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.add_of_not_equiv`：add_of_not_equiv {P Q : Fin 
3 -> R} (h : ¬P ≈ Q) : W'.add P Q = W'.addXYZ P Q
· 使用引理 `WeierstrassCurve.Jacobian.not_equiv_of_Z_eq_zero_right`：not_equiv_of_Z_e
q_zero_right {P Q : Fin 3 -> R} (hPz : P z != 0) (hQz : Q z = 0) : ¬P ≈ Q
· 使用引理 `WeierstrassCurve.Jacobian.addXYZ_of_Z_eq_zero_right`：addXYZ_of_Z_eq_zero
_right {P Q : Fin 3 -> R} (hQ : W'.Equation Q) (hQz : Q z = 0) : W'.addXYZ P Q =
 -(Q x * P z) • P
-/
lemma add_of_Z_eq_zero_right {P Q : Fin 3 → R} (hQ : W'.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z = 0) : W'.add P Q = -(Q x * P z) • P := by
  rw [add_of_not_equiv <| not_equiv_of_Z_eq_zero_right hPz hQz, addXYZ_of_Z_eq_zero_right hQ hQz]
/-
**WeierstrassCurve.Jacobian.add_of_Y_eq** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCu
rve.Jacobian`。
形式化陈述：add_of_Y_eq {P Q : Fin 3 -> F} (hPz : P z != 0) (hQz : Q z != 0) (hx : P x
 * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = Q y * P z ^ 3) (hy' : P y * Q 
z ^ 3 = W.negY Q * P z ^ 3) : W.add P Q = W.dblU P • ![1, 1, 0]
参数：hPz : P z != 0；hQz : Q z != 0；hx : P x * Q z ^ 2 = Q x * P z ^ 2；hy : P y * Q
 z ^ 3 = Q y * P z ^ 3；hy' : P y * Q z ^ 3 = W.negY Q * P z ^ 3。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.add_of_equiv`：add_of_equiv {P Q : Fin 3 -> R} 
(h : P ≈ Q) : W'.add P Q = W'.dblXYZ P
· 使用引理 `WeierstrassCurve.Jacobian.equiv_of_X_eq_of_Y_eq`：equiv_of_X_eq_of_Y_eq {
P Q : Fin 3 -> F} (hPz : P z != 0) (hQz : Q z != 0) (hx : P x * Q z ^ 2 = Q x * 
P z ^ 2) (hy : P y * Q z ^ 3 = Q y * …
· 使用引理 `WeierstrassCurve.Jacobian.dblXYZ_of_Y_eq`：dblXYZ_of_Y_eq {P Q : Fin 3 ->
 F} (hQz : Q z != 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = 
Q y * P z ^ 3) (hy' : P y * Q …
-/
lemma add_of_Y_eq {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = Q y * P z ^ 3)
    (hy' : P y * Q z ^ 3 = W.negY Q * P z ^ 3) : W.add P Q = W.dblU P • ![1, 1, 0] := by
  rw [add_of_equiv <| equiv_of_X_eq_of_Y_eq hPz hQz hx hy, dblXYZ_of_Y_eq hQz hx hy hy']
/-
**WeierstrassCurve.Jacobian.add_of_Y_ne** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCu
rve.Jacobian`。
形式化陈述：add_of_Y_ne {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q) (hP
z : P z != 0) (hQz : Q z != 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * 
Q z ^ 3 != Q y * P z ^ 3) : W.add P Q = addU P Q • ![1, 1, 0]
参数：hP : W.Equation P；hQ : W.Equation Q；hPz : P z != 0；hQz : Q z != 0；hx : P x * 
Q z ^ 2 = Q x * P z ^ 2；hy : P y * Q z ^ 3 != Q y * P z ^ 3。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.add_of_not_equiv`：add_of_not_equiv {P Q : Fin 
3 -> R} (h : ¬P ≈ Q) : W'.add P Q = W'.addXYZ P Q
· 使用引理 `WeierstrassCurve.Jacobian.not_equiv_of_Y_ne`：not_equiv_of_Y_ne {P Q : Fi
n 3 -> R} (hy : P y * Q z ^ 3 != Q y * P z ^ 3) : ¬P ≈ Q
· 使用引理 `WeierstrassCurve.Jacobian.addXYZ_of_X_eq`：addXYZ_of_X_eq {P Q : Fin 3 ->
 F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z != 0) (hQz : Q z != 0) (h
x : P x * Q z ^ 2 = Q x * P z …
-/
lemma add_of_Y_ne {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 ≠ Q y * P z ^ 3) :
    W.add P Q = addU P Q • ![1, 1, 0] := by
  rw [add_of_not_equiv <| not_equiv_of_Y_ne hy, addXYZ_of_X_eq hP hQ hPz hQz hx]
/-
**WeierstrassCurve.Jacobian.add_of_Y_ne'** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassC
urve.Jacobian`。
形式化陈述：add_of_Y_ne' [DecidableEq F] {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : 
W.Equation Q) (hPz : P z != 0) (hQz : Q z != 0) (hx : P x * Q z ^ 2 = Q x * P z 
^ 2) (hy : P y * Q z ^ 3 != W.negY Q * P z ^ 3) : W.add P Q = W.dblZ P • ![W.toA
ffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2) (W.toAffine.slope (P x / P z ^ 2) (Q 
x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)), W.toAffine.addY (P x / P z ^ 2) (
Q x / Q z ^ 2) (P y / P z ^ 3) (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2)
 (P y / P z ^ 3) (Q y / Q 
参数：hP : W.Equation P；hQ : W.Equation Q；hPz : P z != 0；hQz : Q z != 0；hx : P x * 
Q z ^ 2 = Q x * P z ^ 2；hy : P y * Q z ^ 3 != W.negY Q * P z ^ 3。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.add_of_equiv`：add_of_equiv {P Q : Fin 3 -> R} 
(h : P ≈ Q) : W'.add P Q = W'.dblXYZ P
· 使用引理 `WeierstrassCurve.Jacobian.equiv_of_X_eq_of_Y_eq`：equiv_of_X_eq_of_Y_eq {
P Q : Fin 3 -> F} (hPz : P z != 0) (hQz : Q z != 0) (hx : P x * Q z ^ 2 = Q x * 
P z ^ 2) (hy : P y * Q z ^ 3 = Q y * …
· 使用引理 `WeierstrassCurve.Jacobian.Y_eq_of_Y_ne'`：Y_eq_of_Y_ne' [NoZeroDivisors R
] {P Q : Fin 3 -> R} (hP : W'.Equation P) (hQ : W'.Equation Q) (hx : P x * Q z ^
 2 = Q x * P z ^ 2) (hy : P y…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `WeierstrassCurve.Jacobian.dblXYZ_of_Z_ne_zero`：dblXYZ_of_Z_ne_zero [Deci
dableEq F] {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z
 != 0) (hQz : Q z != 0) (hx : P x *…
-/
lemma add_of_Y_ne' [DecidableEq F] {P Q : Fin 3 → F}
    (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 ≠ W.negY Q * P z ^ 3) :
    W.add P Q = W.dblZ P •
      ![W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        1] := by
  rw [add_of_equiv <| equiv_of_X_eq_of_Y_eq hPz hQz hx <| Y_eq_of_Y_ne' hP hQ hx hy,
    dblXYZ_of_Z_ne_zero hP hQ hPz hQz hx hy]
/-
**WeierstrassCurve.Jacobian.add_of_X_ne** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCu
rve.Jacobian`。
形式化陈述：add_of_X_ne [DecidableEq F] {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W
.Equation Q) (hPz : P z != 0) (hQz : Q z != 0) (hx : P x * Q z ^ 2 != Q x * P z 
^ 2) : W.add P Q = addZ P Q • ![W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2) 
(W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3
)), W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (W.toAffine.
slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)), 1]
参数：hP : W.Equation P；hQ : W.Equation Q；hPz : P z != 0；hQz : Q z != 0；hx : P x * 
Q z ^ 2 != Q x * P z ^ 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.add_of_not_equiv`：add_of_not_equiv {P Q : Fin 
3 -> R} (h : ¬P ≈ Q) : W'.add P Q = W'.addXYZ P Q
· 使用引理 `WeierstrassCurve.Jacobian.not_equiv_of_X_ne`：not_equiv_of_X_ne {P Q : Fi
n 3 -> R} (hx : P x * Q z ^ 2 != Q x * P z ^ 2) : ¬P ≈ Q
· 使用引理 `WeierstrassCurve.Jacobian.addXYZ_of_Z_ne_zero`：addXYZ_of_Z_ne_zero [Deci
dableEq F] {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z
 != 0) (hQz : Q z != 0) (hx : P x *…
-/
lemma add_of_X_ne [DecidableEq F] {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 ≠ Q x * P z ^ 2) : W.add P Q = addZ P Q •
      ![W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        1] := by
  rw [add_of_not_equiv <| not_equiv_of_X_ne hx, addXYZ_of_Z_ne_zero hP hQ hPz hQz hx]
/-
**WeierstrassCurve.Jacobian.nonsingular_add_of_Z_ne_zero** 是 Mathlib 中的一个引理，位于命名
空间 `WeierstrassCurve.Jacobian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma nonsingular_add_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 → F} (hP : W.Nonsingular P)
    (hQ : W.Nonsingular Q) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hxy : ¬(P x * Q z ^ 2 = Q x * P z ^ 2 ∧ P y * Q z ^ 3 = W.negY Q * P z ^ 3)) : W.Nonsingular
      ![W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)), 1] :=
  (nonsingular_some ..).mpr <| Affine.nonsingular_add ((nonsingular_of_Z_ne_zero hPz).mp hP)
    ((nonsingular_of_Z_ne_zero hQz).mp hQ) <| by rwa [← X_eq_iff hPz hQz, ← Y_eq_iff' hPz hQz]
/-
**WeierstrassCurve.Jacobian.nonsingular_add** 是 Mathlib 中的一个引理，位于命名空间 `Weierstra
ssCurve.Jacobian`。
形式化陈述：nonsingular_add {P Q : Fin 3 -> F} (hP : W.Nonsingular P) (hQ : W.Nonsingu
lar Q) : W.Nonsingular W.add P Q
参数：hP : W.Nonsingular P；hQ : W.Nonsingular Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.add_of_Z_eq_zero`：add_of_Z_eq_zero {P Q : Fin 
3 -> F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) (hPz : P z = 0) (hQz : Q z
 = 0) : W.add P Q = P x ^ 2 • ![…
· 使用引理 `WeierstrassCurve.Jacobian.nonsingular_smul`：nonsingular_smul (P : Fin 3 
-> R) {u : R} (hu : IsUnit u) : W'.Nonsingular (u • P) ↔ W'.Nonsingular P
· 使用定理 `IsUnit.pow`：∀ {M : Type u_1} [inst : Monoid M] {a : M} (n : ℕ), IsUnit a
 → IsUnit (a ^ n)
· 使用引理 `WeierstrassCurve.Jacobian.isUnit_X_of_Z_eq_zero`：isUnit_X_of_Z_eq_zero {
P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z = 0) : IsUnit (P x)
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用引理 `WeierstrassCurve.Jacobian.add_of_Z_eq_zero_left`：add_of_Z_eq_zero_left {
P Q : Fin 3 -> R} (hP : W'.Equation P) (hPz : P z = 0) (hQz : Q z != 0) : W'.add
 P Q = (P x * Q z) • Q
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsUnit.mul`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, IsUnit a → IsU
nit b → IsUnit (a * b)
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
· 使用引理 `WeierstrassCurve.Jacobian.add_of_Z_eq_zero_right`：add_of_Z_eq_zero_right
 {P Q : Fin 3 -> R} (hQ : W'.Equation Q) (hPz : P z != 0) (hQz : Q z = 0) : W'.a
dd P Q = -(Q x * P z) • P
· 使用定理 `IsUnit.neg`：∀ {α : Type u} [inst : Monoid α] [inst_1 : HasDistribNeg α] 
{a : α}, IsUnit a → IsUnit (-a)
· 使用引理 `WeierstrassCurve.Jacobian.add_of_Y_eq`：add_of_Y_eq {P Q : Fin 3 -> F} (h
Pz : P z != 0) (hQz : Q z != 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y *
 Q z ^ 3 = Q y * P z ^ 3) (…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `WeierstrassCurve.Jacobian.isUnit_dblU_of_Y_eq`：isUnit_dblU_of_Y_eq {P Q 
: Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z != 0) (hQz : Q z != 0) (hx : P x
 * Q z ^ 2 = Q x * P z ^ 2) (hy : P…
· 使用引理 `WeierstrassCurve.Jacobian.add_of_Y_ne`：add_of_Y_ne {P Q : Fin 3 -> F} (h
P : W.Equation P) (hQ : W.Equation Q) (hPz : P z != 0) (hQz : Q z != 0) (hx : P 
x * Q z ^ 2 = Q x * P z ^ 2…
· 使用引理 `WeierstrassCurve.Jacobian.isUnit_addU_of_Y_ne`：isUnit_addU_of_Y_ne {P Q 
: Fin 3 -> F} (hPz : P z != 0) (hQz : Q z != 0) (hy : P y * Q z ^ 3 != Q y * P z
 ^ 3) : IsUnit (addU P Q)
· 使用定理 `_private.Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point.0.Weiers
trassCurve.Jacobian.nonsingular_add_of_Z_ne_zero`：∀ {F : Type u} [inst : Field F
] {W : WeierstrassCurve.Jacobian F} [inst_1 : DecidableEq F] {P Q : Fin 3 → F}, 
  W.Nonsingular P →     W.Nons…
· 使用引理 `WeierstrassCurve.Jacobian.add_of_Y_ne'`：add_of_Y_ne' [DecidableEq F] {P 
Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z != 0) (hQz : 
Q z != 0) (hx : P x * Q z ^ …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_and`：∀ {a b : Prop}, ¬(a ∧ b) ↔ a → ¬b
· 使用引理 `WeierstrassCurve.Jacobian.isUnit_dblZ_of_Y_ne'`：isUnit_dblZ_of_Y_ne' {P 
Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z != 0) (hx : P
 x * Q z ^ 2 = Q x * P z ^ 2) (hy : …
· 使用引理 `WeierstrassCurve.Jacobian.add_of_X_ne`：add_of_X_ne [DecidableEq F] {P Q 
: Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z != 0) (hQz : Q 
z != 0) (hx : P x * Q z ^ 2…
· 使用引理 `WeierstrassCurve.Jacobian.isUnit_addZ_of_X_ne`：isUnit_addZ_of_X_ne {P Q 
: Fin 3 -> F} (hx : P x * Q z ^ 2 != Q x * P z ^ 2) : IsUnit addZ P Q
-/
lemma nonsingular_add {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    W.Nonsingular <| W.add P Q := by
  by_cases hPz : P z = 0
  · by_cases hQz : Q z = 0
    · simp only [add_of_Z_eq_zero hP hQ hPz hQz,
        nonsingular_smul _ <| (isUnit_X_of_Z_eq_zero hP hPz).pow 2, nonsingular_zero]
    · simpa only [add_of_Z_eq_zero_left hP.left hPz hQz,
        nonsingular_smul _ <| (isUnit_X_of_Z_eq_zero hP hPz).mul <| Ne.isUnit hQz]
  · by_cases hQz : Q z = 0
    · simpa only [add_of_Z_eq_zero_right hQ.left hPz hQz,
        nonsingular_smul _ ((isUnit_X_of_Z_eq_zero hQ hQz).mul <| Ne.isUnit hPz).neg]
    · by_cases hxy : P x * Q z ^ 2 = Q x * P z ^ 2 ∧ P y * Q z ^ 3 = W.negY Q * P z ^ 3
      · by_cases hy : P y * Q z ^ 3 = Q y * P z ^ 3
        · simp only [add_of_Y_eq hPz hQz hxy.left hy hxy.right, nonsingular_smul _ <|
              isUnit_dblU_of_Y_eq hP hPz hQz hxy.left hy hxy.right, nonsingular_zero]
        · simp only [add_of_Y_ne hP.left hQ.left hPz hQz hxy.left hy,
            nonsingular_smul _ <| isUnit_addU_of_Y_ne hPz hQz hy, nonsingular_zero]
      · classical
        have := nonsingular_add_of_Z_ne_zero hP hQ hPz hQz hxy
        by_cases hx : P x * Q z ^ 2 = Q x * P z ^ 2
        · simpa only [add_of_Y_ne' hP.left hQ.left hPz hQz hx <| not_and.mp hxy hx,
            nonsingular_smul _ <| isUnit_dblZ_of_Y_ne' hP.left hQ.left hPz hx <| not_and.mp hxy hx]
        · simpa only [add_of_X_ne hP.left hQ.left hPz hQz hx,
            nonsingular_smul _ <| isUnit_addZ_of_X_ne hx]

variable (W') in
/-- The addition of two Jacobian point classes on a Weierstrass curve `W`.

If `P` and `Q` are two Jacobian point representatives on `W`, then `W.addMap ⟦P⟧ ⟦Q⟧` is
definitionally equivalent to `W.add P Q`. -/
/-
**WeierstrassCurve.Jacobian.addMap** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve.J
acobian`。
形式化陈述：addMap (P Q : PointClass R) : PointClass R
参数：P Q : PointClass R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Jacobian.add_equiv`：add_equiv {P P' Q Q' : Fin 3 -> R} 
(hP : P ≈ P') (hQ : Q ≈ Q') : W'.add P Q ≈ W'.add P' Q'

--- 原说明 ---
The addition of two Jacobian point classes on a Weierstrass curve `W`.

If `P` and `Q` are two Jacobian point representatives on `W`, then `W.addMap ⟦P⟧
 ⟦Q⟧` is
definitionally equivalent to `W.add P Q`.
-/
noncomputable def addMap (P Q : PointClass R) : PointClass R :=
  Quotient.map₂ W'.add (fun _ _ hP _ _ hQ => add_equiv hP hQ) P Q
/-
**WeierstrassCurve.Jacobian.addMap_eq** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurv
e.Jacobian`。
形式化陈述：addMap_eq (P Q : Fin 3 -> R) : W'.addMap ⟦P⟧ ⟦Q⟧ = ⟦W'.add P Q⟧
参数：P Q : Fin 3 -> R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma addMap_eq (P Q : Fin 3 → R) : W'.addMap ⟦P⟧ ⟦Q⟧ = ⟦W'.add P Q⟧ :=
  rfl
/-
**WeierstrassCurve.Jacobian.addMap_of_Z_eq_zero_left** 是 Mathlib 中的一个引理，位于命名空间 `
WeierstrassCurve.Jacobian`。
形式化陈述：addMap_of_Z_eq_zero_left {P : Fin 3 -> F} {Q : PointClass F} (hP : W.Nonsi
ngular P) (hQ : W.NonsingularLift Q) (hPz : P z = 0) : W.addMap ⟦P⟧ Q = Q
参数：hP : W.Nonsingular P；hQ : W.NonsingularLift Q；hPz : P z = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.addMap_eq`：addMap_eq (P Q : Fin 3 -> R) : W'.a
ddMap ⟦P⟧ ⟦Q⟧ = ⟦W'.add P Q⟧
· 使用引理 `WeierstrassCurve.Jacobian.add_of_Z_eq_zero`：add_of_Z_eq_zero {P Q : Fin 
3 -> F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) (hPz : P z = 0) (hQz : Q z
 = 0) : W.add P Q = P x ^ 2 • ![…
· 使用引理 `WeierstrassCurve.Jacobian.smul_eq`：smul_eq (P : Fin 3 -> R) {u : R} (hu 
: IsUnit u) : (⟦u • P⟧ : PointClass R) = ⟦P⟧
· 使用定理 `IsUnit.pow`：∀ {M : Type u_1} [inst : Monoid M] {a : M} (n : ℕ), IsUnit a
 → IsUnit (a ^ n)
· 使用引理 `WeierstrassCurve.Jacobian.isUnit_X_of_Z_eq_zero`：isUnit_X_of_Z_eq_zero {
P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z = 0) : IsUnit (P x)
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a
· 使用引理 `WeierstrassCurve.Jacobian.equiv_zero_of_Z_eq_zero`：equiv_zero_of_Z_eq_ze
ro {P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z = 0) : P ≈ ![1, 1, 0]
· 使用引理 `WeierstrassCurve.Jacobian.add_of_Z_eq_zero_left`：add_of_Z_eq_zero_left {
P Q : Fin 3 -> R} (hP : W'.Equation P) (hPz : P z = 0) (hQz : Q z != 0) : W'.add
 P Q = (P x * Q z) • Q
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsUnit.mul`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, IsUnit a → IsU
nit b → IsUnit (a * b)
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
-/
lemma addMap_of_Z_eq_zero_left {P : Fin 3 → F} {Q : PointClass F} (hP : W.Nonsingular P)
    (hQ : W.NonsingularLift Q) (hPz : P z = 0) : W.addMap ⟦P⟧ Q = Q := by
  revert hQ
  refine Q.inductionOn (motive := fun Q => _ → W.addMap _ Q = Q) fun Q hQ => ?_
  by_cases hQz : Q z = 0
  · rw [addMap_eq, add_of_Z_eq_zero hP hQ hPz hQz,
      smul_eq _ <| (isUnit_X_of_Z_eq_zero hP hPz).pow 2, Quotient.eq]
    exact Setoid.symm <| equiv_zero_of_Z_eq_zero hQ hQz
  · rw [addMap_eq, add_of_Z_eq_zero_left hP.left hPz hQz,
      smul_eq _ <| (isUnit_X_of_Z_eq_zero hP hPz).mul <| Ne.isUnit hQz]
/-
**WeierstrassCurve.Jacobian.addMap_of_Z_eq_zero_right** 是 Mathlib 中的一个引理，位于命名空间 
`WeierstrassCurve.Jacobian`。
形式化陈述：addMap_of_Z_eq_zero_right {P : PointClass F} {Q : Fin 3 -> F} (hP : W.Nons
ingularLift P) (hQ : W.Nonsingular Q) (hQz : Q z = 0) : W.addMap P ⟦Q⟧ = P
参数：hP : W.NonsingularLift P；hQ : W.Nonsingular Q；hQz : Q z = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.addMap_eq`：addMap_eq (P Q : Fin 3 -> R) : W'.a
ddMap ⟦P⟧ ⟦Q⟧ = ⟦W'.add P Q⟧
· 使用引理 `WeierstrassCurve.Jacobian.add_of_Z_eq_zero`：add_of_Z_eq_zero {P Q : Fin 
3 -> F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) (hPz : P z = 0) (hQz : Q z
 = 0) : W.add P Q = P x ^ 2 • ![…
· 使用引理 `WeierstrassCurve.Jacobian.smul_eq`：smul_eq (P : Fin 3 -> R) {u : R} (hu 
: IsUnit u) : (⟦u • P⟧ : PointClass R) = ⟦P⟧
· 使用定理 `IsUnit.pow`：∀ {M : Type u_1} [inst : Monoid M] {a : M} (n : ℕ), IsUnit a
 → IsUnit (a ^ n)
· 使用引理 `WeierstrassCurve.Jacobian.isUnit_X_of_Z_eq_zero`：isUnit_X_of_Z_eq_zero {
P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z = 0) : IsUnit (P x)
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a
· 使用引理 `WeierstrassCurve.Jacobian.equiv_zero_of_Z_eq_zero`：equiv_zero_of_Z_eq_ze
ro {P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z = 0) : P ≈ ![1, 1, 0]
· 使用引理 `WeierstrassCurve.Jacobian.add_of_Z_eq_zero_right`：add_of_Z_eq_zero_right
 {P Q : Fin 3 -> R} (hQ : W'.Equation Q) (hPz : P z != 0) (hQz : Q z = 0) : W'.a
dd P Q = -(Q x * P z) • P
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsUnit.neg`：∀ {α : Type u} [inst : Monoid α] [inst_1 : HasDistribNeg α] 
{a : α}, IsUnit a → IsUnit (-a)
· 使用定理 `IsUnit.mul`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, IsUnit a → IsU
nit b → IsUnit (a * b)
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
-/
lemma addMap_of_Z_eq_zero_right {P : PointClass F} {Q : Fin 3 → F} (hP : W.NonsingularLift P)
    (hQ : W.Nonsingular Q) (hQz : Q z = 0) : W.addMap P ⟦Q⟧ = P := by
  revert hP
  refine P.inductionOn (motive := fun P => _ → W.addMap P _ = P) fun P hP => ?_
  by_cases hPz : P z = 0
  · rw [addMap_eq, add_of_Z_eq_zero hP hQ hPz hQz,
      smul_eq _ <| (isUnit_X_of_Z_eq_zero hP hPz).pow 2, Quotient.eq]
    exact Setoid.symm <| equiv_zero_of_Z_eq_zero hP hPz
  · rw [addMap_eq, add_of_Z_eq_zero_right hQ.left hPz hQz,
      smul_eq _ ((isUnit_X_of_Z_eq_zero hQ hQz).mul <| Ne.isUnit hPz).neg]
/-
**WeierstrassCurve.Jacobian.addMap_of_Y_eq** 是 Mathlib 中的一个引理，位于命名空间 `Weierstras
sCurve.Jacobian`。
形式化陈述：addMap_of_Y_eq {P Q : Fin 3 -> F} (hP : W.Nonsingular P) (hQ : W.Equation 
Q) (hPz : P z != 0) (hQz : Q z != 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy' :
 P y * Q z ^ 3 = W.negY Q * P z ^ 3) : W.addMap ⟦P⟧ ⟦Q⟧ = ⟦![1, 1, 0]⟧
参数：hP : W.Nonsingular P；hQ : W.Equation Q；hPz : P z != 0；hQz : Q z != 0；hx : P x
 * Q z ^ 2 = Q x * P z ^ 2；hy' : P y * Q z ^ 3 = W.negY Q * P z ^ 3。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.addMap_eq`：addMap_eq (P Q : Fin 3 -> R) : W'.a
ddMap ⟦P⟧ ⟦Q⟧ = ⟦W'.add P Q⟧
· 使用引理 `WeierstrassCurve.Jacobian.add_of_Y_eq`：add_of_Y_eq {P Q : Fin 3 -> F} (h
Pz : P z != 0) (hQz : Q z != 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y *
 Q z ^ 3 = Q y * P z ^ 3) (…
· 使用引理 `WeierstrassCurve.Jacobian.smul_eq`：smul_eq (P : Fin 3 -> R) {u : R} (hu 
: IsUnit u) : (⟦u • P⟧ : PointClass R) = ⟦P⟧
· 使用引理 `WeierstrassCurve.Jacobian.isUnit_dblU_of_Y_eq`：isUnit_dblU_of_Y_eq {P Q 
: Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z != 0) (hQz : Q z != 0) (hx : P x
 * Q z ^ 2 = Q x * P z ^ 2) (hy : P…
· 使用引理 `WeierstrassCurve.Jacobian.add_of_Y_ne`：add_of_Y_ne {P Q : Fin 3 -> F} (h
P : W.Equation P) (hQ : W.Equation Q) (hPz : P z != 0) (hQz : Q z != 0) (hx : P 
x * Q z ^ 2 = Q x * P z ^ 2…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `WeierstrassCurve.Jacobian.isUnit_addU_of_Y_ne`：isUnit_addU_of_Y_ne {P Q 
: Fin 3 -> F} (hPz : P z != 0) (hQz : Q z != 0) (hy : P y * Q z ^ 3 != Q y * P z
 ^ 3) : IsUnit (addU P Q)
-/
lemma addMap_of_Y_eq {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2)
    (hy' : P y * Q z ^ 3 = W.negY Q * P z ^ 3) : W.addMap ⟦P⟧ ⟦Q⟧ = ⟦![1, 1, 0]⟧ := by
  by_cases hy : P y * Q z ^ 3 = Q y * P z ^ 3
  · rw [addMap_eq, add_of_Y_eq hPz hQz hx hy hy',
      smul_eq _ <| isUnit_dblU_of_Y_eq hP hPz hQz hx hy hy']
  · rw [addMap_eq, add_of_Y_ne hP.left hQ hPz hQz hx hy,
      smul_eq _ <| isUnit_addU_of_Y_ne hPz hQz hy]
/-
**WeierstrassCurve.Jacobian.addMap_of_Z_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Weier
strassCurve.Jacobian`。
形式化陈述：addMap_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 -> F} (hP : W.Equation P)
 (hQ : W.Equation Q) (hPz : P z != 0) (hQz : Q z != 0) (hxy : ¬(P x * Q z ^ 2 = 
Q x * P z ^ 2 ∧ P y * Q z ^ 3 = W.negY Q * P z ^ 3)) : W.addMap ⟦P⟧ ⟦Q⟧ = ⟦![W.t
oAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2) (W.toAffine.slope (P x / P z ^ 2) (
Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)), W.toAffine.addY (P x / P z ^ 2)
 (Q x / Q z ^ 2) (P y / P z ^ 3) (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 
2) (P y / P z ^ 3) (Q y / 
参数：hP : W.Equation P；hQ : W.Equation Q；hPz : P z != 0；hQz : Q z != 0；hxy : ¬(P x
 * Q z ^ 2 = Q x * P z ^ 2 ∧ P y * Q z ^ 3 = W.negY Q * P z ^ 3)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.addMap_eq`：addMap_eq (P Q : Fin 3 -> R) : W'.a
ddMap ⟦P⟧ ⟦Q⟧ = ⟦W'.add P Q⟧
· 使用引理 `WeierstrassCurve.Jacobian.add_of_Y_ne'`：add_of_Y_ne' [DecidableEq F] {P 
Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z != 0) (hQz : 
Q z != 0) (hx : P x * Q z ^ …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_and`：∀ {a b : Prop}, ¬(a ∧ b) ↔ a → ¬b
· 使用引理 `WeierstrassCurve.Jacobian.smul_eq`：smul_eq (P : Fin 3 -> R) {u : R} (hu 
: IsUnit u) : (⟦u • P⟧ : PointClass R) = ⟦P⟧
· 使用引理 `WeierstrassCurve.Jacobian.isUnit_dblZ_of_Y_ne'`：isUnit_dblZ_of_Y_ne' {P 
Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z != 0) (hx : P
 x * Q z ^ 2 = Q x * P z ^ 2) (hy : …
· 使用引理 `WeierstrassCurve.Jacobian.add_of_X_ne`：add_of_X_ne [DecidableEq F] {P Q 
: Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z != 0) (hQz : Q 
z != 0) (hx : P x * Q z ^ 2…
· 使用引理 `WeierstrassCurve.Jacobian.isUnit_addZ_of_X_ne`：isUnit_addZ_of_X_ne {P Q 
: Fin 3 -> F} (hx : P x * Q z ^ 2 != Q x * P z ^ 2) : IsUnit addZ P Q
-/
lemma addMap_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 → F}
    (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hxy : ¬(P x * Q z ^ 2 = Q x * P z ^ 2 ∧ P y * Q z ^ 3 = W.negY Q * P z ^ 3)) :
    W.addMap ⟦P⟧ ⟦Q⟧ =
      ⟦![W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        1]⟧ := by
  by_cases hx : P x * Q z ^ 2 = Q x * P z ^ 2
  · rw [addMap_eq, add_of_Y_ne' hP hQ hPz hQz hx <| not_and.mp hxy hx,
      smul_eq _ <| isUnit_dblZ_of_Y_ne' hP hQ hPz hx <| not_and.mp hxy hx]
  · rw [addMap_eq, add_of_X_ne hP hQ hPz hQz hx, smul_eq _ <| isUnit_addZ_of_X_ne hx]
/-
**WeierstrassCurve.Jacobian.nonsingularLift_addMap** 是 Mathlib 中的一个引理，位于命名空间 `We
ierstrassCurve.Jacobian`。
形式化陈述：nonsingularLift_addMap {P Q : PointClass F} (hP : W.NonsingularLift P) (hQ
 : W.NonsingularLift Q) : W.NonsingularLift W.addMap P Q
参数：hP : W.NonsingularLift P；hQ : W.NonsingularLift Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Jacobian.nonsingular_add`：nonsingular_add {P Q : Fin 3 
-> F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) : W.Nonsingular W.add P Q
-/
lemma nonsingularLift_addMap {P Q : PointClass F} (hP : W.NonsingularLift P)
    (hQ : W.NonsingularLift Q) : W.NonsingularLift <| W.addMap P Q := by
  rcases P; rcases Q
  exact nonsingular_add hP hQ

/-! ## Nonsingular Jacobian points -/

variable (W') in
/-- A nonsingular Jacobian point on a Weierstrass curve `W`. -/
@[ext]
/-
**WeierstrassCurve.Jacobian.Point** 是 Mathlib 中的一个归纳类型，位于命名空间 `WeierstrassCurve.
Jacobian`。
形式化陈述：{R : Type r} → [CommRing R] → WeierstrassCurve.Jacobian R → Type r
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A nonsingular Jacobian point on a Weierstrass curve `W`.
-/
structure Point where
  /-- The Jacobian point class underlying a nonsingular Jacobian point on `W`. -/
  {point : PointClass R}
  /-- The nonsingular condition underlying a nonsingular Jacobian point on `W`. -/
  (nonsingular : W'.NonsingularLift point)

namespace Point

/-
**WeierstrassCurve.Jacobian.Point.mk_point** 是 Mathlib 中的一个引理，位于命名空间 `Weierstras
sCurve.Jacobian.Point`。
形式化陈述：mk_point {P : PointClass R} (h : W'.NonsingularLift P) : (mk h).point = P
参数：h : W'.NonsingularLift P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_point {P : PointClass R} (h : W'.NonsingularLift P) : (mk h).point = P :=
  rfl
/-
**WeierstrassCurve.Jacobian.Point.** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurve.J
acobian.Point`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial R] : Zero W'.Point :=
  ⟨⟨nonsingularLift_zero⟩⟩
/-
**WeierstrassCurve.Jacobian.Point.zero_def** 是 Mathlib 中的一个引理，位于命名空间 `Weierstras
sCurve.Jacobian.Point`。
形式化陈述：zero_def [Nontrivial R] : (0 : W'.Point) = ⟨nonsingularLift_zero⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zero_def [Nontrivial R] : (0 : W'.Point) = ⟨nonsingularLift_zero⟩ :=
  rfl
/-
**WeierstrassCurve.Jacobian.Point.zero_point** 是 Mathlib 中的一个引理，位于命名空间 `Weierstr
assCurve.Jacobian.Point`。
形式化陈述：zero_point [Nontrivial R] : (0 : W'.Point).point = ⟦![1, 1, 0]⟧
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zero_point [Nontrivial R] : (0 : W'.Point).point = ⟦![1, 1, 0]⟧ :=
  rfl
/-
**WeierstrassCurve.Jacobian.Point.mk_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Weierstr
assCurve.Jacobian.Point`。
形式化陈述：mk_ne_zero [Nontrivial R] {X Y : R} (h : W'.NonsingularLift ⟦![X, Y, 1]⟧) 
: mk h != 0
参数：h : W'.NonsingularLift ⟦![X, Y, 1]⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Jacobian.not_equiv_of_Z_eq_zero_right`：not_equiv_of_Z_e
q_zero_right {P Q : Fin 3 -> R} (hPz : P z != 0) (hQz : Q z = 0) : ¬P ≈ Q
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
· 使用定理 `WeierstrassCurve.Jacobian.Point.ext_iff`：∀ {R : Type r} {inst : CommRing
 R} {W' : WeierstrassCurve.Jacobian R} {x y : W'.Point}, x = y ↔ x.point = y.poi
nt
-/
lemma mk_ne_zero [Nontrivial R] {X Y : R} (h : W'.NonsingularLift ⟦![X, Y, 1]⟧) : mk h ≠ 0 :=
  (not_equiv_of_Z_eq_zero_right one_ne_zero rfl).comp <| Quotient.eq.mp.comp Point.ext_iff.mp

/-- The natural map from a nonsingular point on a Weierstrass curve in affine coordinates to its
corresponding nonsingular Jacobian point. -/
/-
**WeierstrassCurve.Jacobian.Point.fromAffine** 是 Mathlib 中的一个定义，位于命名空间 `Weierstr
assCurve.Jacobian.Point`。
形式化陈述：{R : Type r} → [inst : CommRing R] → {W' : WeierstrassCurve.Jacobian R} → 
[Nontrivial R] → W'.toAffine.Point → W'.Point
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural map from a nonsingular point on a Weierstrass curve in affine coordi
nates to its
corresponding nonsingular Jacobian point.
-/
def fromAffine [Nontrivial R] : W'.toAffine.Point → W'.Point
  | 0 => 0
  | .some _ _ h => ⟨(nonsingularLift_some ..).mpr h⟩
/-
**WeierstrassCurve.Jacobian.Point.fromAffine_zero** 是 Mathlib 中的一个引理，位于命名空间 `Wei
erstrassCurve.Jacobian.Point`。
形式化陈述：fromAffine_zero [Nontrivial R] : fromAffine 0 = (0 : W'.Point)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fromAffine_zero [Nontrivial R] : fromAffine 0 = (0 : W'.Point) :=
  rfl
/-
**WeierstrassCurve.Jacobian.Point.fromAffine_some** 是 Mathlib 中的一个引理，位于命名空间 `Wei
erstrassCurve.Jacobian.Point`。
形式化陈述：fromAffine_some [Nontrivial R] {X Y : R} (h : W'.toAffine.Nonsingular X Y)
 : fromAffine (.some _ _ h) = ⟨(nonsingularLift_some ..).mpr h⟩
参数：h : W'.toAffine.Nonsingular X Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fromAffine_some [Nontrivial R] {X Y : R} (h : W'.toAffine.Nonsingular X Y) :
    fromAffine (.some _ _ h) = ⟨(nonsingularLift_some ..).mpr h⟩ :=
  rfl
/-
**WeierstrassCurve.Jacobian.Point.fromAffine_some_ne_zero** 是 Mathlib 中的一个引理，位于命
名空间 `WeierstrassCurve.Jacobian.Point`。
形式化陈述：fromAffine_some_ne_zero [Nontrivial R] {X Y : R} (h : W'.toAffine.Nonsingu
lar X Y) : fromAffine (.some _ _ h) != 0
参数：h : W'.toAffine.Nonsingular X Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Jacobian.Point.mk_ne_zero`：mk_ne_zero [Nontrivial R] {X
 Y : R} (h : W'.NonsingularLift ⟦![X, Y, 1]⟧) : mk h != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WeierstrassCurve.Jacobian.nonsingularLift_some`：nonsingularLift_some (a 
b : R) : W'.NonsingularLift ⟦![a, b, 1]⟧ ↔ W'.toAffine.Nonsingular a b
-/
lemma fromAffine_some_ne_zero [Nontrivial R] {X Y : R} (h : W'.toAffine.Nonsingular X Y) :
    fromAffine (.some _ _ h) ≠ 0 :=
  mk_ne_zero <| (nonsingularLift_some ..).mpr h

/-- The negation of a nonsingular Jacobian point on a Weierstrass curve `W`.

Given a nonsingular Jacobian point `P` on `W`, use `-P` instead of `neg P`. -/
/-
**WeierstrassCurve.Jacobian.Point.neg** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurv
e.Jacobian.Point`。
形式化陈述：neg (P : W.Point) : W.Point
参数：P : W.Point。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The negation of a nonsingular Jacobian point on a Weierstrass curve `W`.

Given a nonsingular Jacobian point `P` on `W`, use `-P` instead of `neg P`.
-/
def neg (P : W.Point) : W.Point :=
  ⟨nonsingularLift_negMap P.nonsingular⟩
/-
**WeierstrassCurve.Jacobian.Point.** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurve.J
acobian.Point`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg W.Point :=
  ⟨neg⟩
/-
**WeierstrassCurve.Jacobian.Point.neg_def** 是 Mathlib 中的一个引理，位于命名空间 `Weierstrass
Curve.Jacobian.Point`。
形式化陈述：neg_def (P : W.Point) : -P = P.neg
参数：P : W.Point。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma neg_def (P : W.Point) : -P = P.neg :=
  rfl
/-
**WeierstrassCurve.Jacobian.Point.neg_point** 是 Mathlib 中的一个引理，位于命名空间 `Weierstra
ssCurve.Jacobian.Point`。
形式化陈述：neg_point (P : W.Point) : (-P).point = W.negMap P.point
参数：P : W.Point。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma neg_point (P : W.Point) : (-P).point = W.negMap P.point :=
  rfl

/-- The addition of two nonsingular Jacobian points on a Weierstrass curve `W`.

Given two nonsingular Jacobian points `P` and `Q` on `W`, use `P + Q` instead of `add P Q`. -/
/-
**WeierstrassCurve.Jacobian.Point.add** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurv
e.Jacobian.Point`。
形式化陈述：add (P Q : W.Point) : W.Point
参数：P Q : W.Point。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The addition of two nonsingular Jacobian points on a Weierstrass curve `W`.

Given two nonsingular Jacobian points `P` and `Q` on `W`, use `P + Q` instead of
 `add P Q`.
-/
noncomputable def add (P Q : W.Point) : W.Point :=
  ⟨nonsingularLift_addMap P.nonsingular Q.nonsingular⟩
/-
**WeierstrassCurve.Jacobian.Point.** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurve.J
acobian.Point`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Add W.Point :=
  ⟨add⟩
/-
**WeierstrassCurve.Jacobian.Point.add_def** 是 Mathlib 中的一个引理，位于命名空间 `Weierstrass
Curve.Jacobian.Point`。
形式化陈述：add_def (P Q : W.Point) : P + Q = P.add Q
参数：P Q : W.Point。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma add_def (P Q : W.Point) : P + Q = P.add Q :=
  rfl
/-
**WeierstrassCurve.Jacobian.Point.add_point** 是 Mathlib 中的一个引理，位于命名空间 `Weierstra
ssCurve.Jacobian.Point`。
形式化陈述：add_point (P Q : W.Point) : (P + Q).point = W.addMap P.point Q.point
参数：P Q : W.Point。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma add_point (P Q : W.Point) : (P + Q).point = W.addMap P.point Q.point :=
  rfl

/-! ## Equivalence between Jacobian and affine coordinates -/

open scoped Classical in
variable (W) in
/-- The natural map from a nonsingular Jacobian point representative on a Weierstrass curve to its
corresponding nonsingular point in affine coordinates. -/
/-
**WeierstrassCurve.Jacobian.Point.toAffine** 是 Mathlib 中的一个定义，位于命名空间 `Weierstras
sCurve.Jacobian.Point`。
形式化陈述：toAffine (P : Fin 3 -> F) : W.toAffine.Point
参数：P : Fin 3 -> F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural map from a nonsingular Jacobian point representative on a Weierstras
s curve to its
corresponding nonsingular point in affine coordinates.
-/
noncomputable def toAffine (P : Fin 3 → F) : W.toAffine.Point :=
  if hP : W.Nonsingular P ∧ P z ≠ 0 then .some _ _ <| (nonsingular_of_Z_ne_zero hP.2).mp hP.1 else 0
/-
**WeierstrassCurve.Jacobian.Point.toAffine_of_singular** 是 Mathlib 中的一个引理，位于命名空间
 `WeierstrassCurve.Jacobian.Point`。
形式化陈述：toAffine_of_singular {P : Fin 3 -> F} (hP : ¬W.Nonsingular P) : toAffine W
 P = 0
参数：hP : ¬W.Nonsingular P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.Jacobian.Point.toAffine.eq_1`：∀ {F : Type u} [inst : Fi
eld F] (W : WeierstrassCurve.Jacobian F) (P : Fin 3 → F),   WeierstrassCurve.Jac
obian.Point.toAffine W P =     if h…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `not_and_of_not_left`：∀ {a : Prop} (b : Prop), ¬a → ¬(a ∧ b)
-/
lemma toAffine_of_singular {P : Fin 3 → F} (hP : ¬W.Nonsingular P) : toAffine W P = 0 := by
  rw [toAffine, dif_neg <| not_and_of_not_left _ hP]
/-
**WeierstrassCurve.Jacobian.Point.toAffine_of_Z_eq_zero** 是 Mathlib 中的一个引理，位于命名空
间 `WeierstrassCurve.Jacobian.Point`。
形式化陈述：toAffine_of_Z_eq_zero {P : Fin 3 -> F} (hPz : P z = 0) : toAffine W P = 0
参数：hPz : P z = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.Jacobian.Point.toAffine.eq_1`：∀ {F : Type u} [inst : Fi
eld F] (W : WeierstrassCurve.Jacobian F) (P : Fin 3 → F),   WeierstrassCurve.Jac
obian.Point.toAffine W P =     if h…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_and_not_right`：not_and_not_right : ¬(a ∧ ¬b) ↔ a -> b
-/
lemma toAffine_of_Z_eq_zero {P : Fin 3 → F} (hPz : P z = 0) : toAffine W P = 0 := by
  rw [toAffine, dif_neg <| not_and_not_right.mpr fun _ => hPz]
/-
**WeierstrassCurve.Jacobian.Point.toAffine_zero** 是 Mathlib 中的一个引理，位于命名空间 `Weier
strassCurve.Jacobian.Point`。
形式化陈述：toAffine_zero : toAffine W ![1, 1, 0] = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Jacobian.Point.toAffine_of_Z_eq_zero`：toAffine_of_Z_eq_
zero {P : Fin 3 -> F} (hPz : P z = 0) : toAffine W P = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma toAffine_zero : toAffine W ![1, 1, 0] = 0 :=
  toAffine_of_Z_eq_zero rfl
/-
**WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero** 是 Mathlib 中的一个引理，位于命名空
间 `WeierstrassCurve.Jacobian.Point`。
形式化陈述：toAffine_of_Z_ne_zero {P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z !
= 0) : toAffine W P = .some _ _ ((nonsingular_of_Z_ne_zero hPz).mp hP)
参数：hP : W.Nonsingular P；hPz : P z != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WeierstrassCurve.Jacobian.nonsingular_of_Z_ne_zero`：nonsingular_of_Z_ne_
zero {P : Fin 3 -> F} (hPz : P z != 0) : W.Nonsingular P ↔ W.toAffine.Nonsingula
r (P x / P z ^ 2) (P y / P z ^ 3)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.Jacobian.Point.toAffine.eq_1`：∀ {F : Type u} [inst : Fi
eld F] (W : WeierstrassCurve.Jacobian F) (P : Fin 3 → F),   WeierstrassCurve.Jac
obian.Point.toAffine W P =     if h…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
lemma toAffine_of_Z_ne_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z ≠ 0) :
    toAffine W P = .some _ _ ((nonsingular_of_Z_ne_zero hPz).mp hP) := by
  rw [toAffine, dif_pos ⟨hP, hPz⟩]
/-
**WeierstrassCurve.Jacobian.Point.toAffine_some** 是 Mathlib 中的一个引理，位于命名空间 `Weier
strassCurve.Jacobian.Point`。
形式化陈述：toAffine_some {X Y : F} (h : W.Nonsingular ![X, Y, 1]) : toAffine W ![X, Y
, 1] = .some _ _ ((nonsingular_some ..).mp h)
参数：h : W.Nonsingular ![X, Y, 1]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WeierstrassCurve.Jacobian.nonsingular_some`：nonsingular_some (a b : R) :
 W'.Nonsingular ![a, b, 1] ↔ W'.toAffine.Nonsingular a b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `WeierstrassCurve.Jacobian.nonsingular_of_Z_ne_zero`：nonsingular_of_Z_ne_
zero {P : Fin 3 -> F} (hPz : P z != 0) : W.Nonsingular P ↔ W.toAffine.Nonsingula
r (P x / P z ^ 2) (P y / P z ^ 3)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用引理 `WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero`：toAffine_of_Z_ne_
zero {P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z != 0) : toAffine W P = .
some _ _ ((nonsingular_of_Z_ne_zero hPz).mp…
· 使用定理 `WeierstrassCurve.Affine.Point.some.congr_simp`：∀ {R : Type r} [inst : Co
mmRing R] {W' : WeierstrassCurve.Affine R} (x x_1 : R) (e_x : x = x_1) (y y_1 : 
R)   (e_y : y = y_1) (h : W'.Nonsin…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toAffine_some {X Y : F} (h : W.Nonsingular ![X, Y, 1]) :
    toAffine W ![X, Y, 1] = .some _ _ ((nonsingular_some ..).mp h) := by
  simp only [toAffine_of_Z_ne_zero h one_ne_zero, fin3_def_ext, one_pow, div_one]
/-
**WeierstrassCurve.Jacobian.Point.toAffine_smul** 是 Mathlib 中的一个引理，位于命名空间 `Weier
strassCurve.Jacobian.Point`。
形式化陈述：toAffine_smul (P : Fin 3 -> F) {u : F} (hu : IsUnit u) : toAffine W (u • P
) = toAffine W P
参数：P : Fin 3 -> F；hu : IsUnit u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.Point.toAffine_of_Z_eq_zero`：toAffine_of_Z_eq_
zero {P : Fin 3 -> F} (hPz : P z = 0) : toAffine W P = 0
· 使用定理 `mul_eq_zero_of_right`：mul_eq_zero_of_right (a : M₀) {b : M₀} (h : b = 0)
 : a * b = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WeierstrassCurve.Jacobian.nonsingular_of_Z_ne_zero`：nonsingular_of_Z_ne_
zero {P : Fin 3 -> F} (hPz : P z != 0) : W.Nonsingular P ↔ W.toAffine.Nonsingula
r (P x / P z ^ 2) (P y / P z ^ 3)
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsUnit.ne_zero`：ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a != 
0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WeierstrassCurve.Jacobian.nonsingular_smul`：nonsingular_smul (P : Fin 3 
-> R) {u : R} (hu : IsUnit u) : W'.Nonsingular (u • P) ↔ W'.Nonsingular P
· 使用引理 `WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero`：toAffine_of_Z_ne_
zero {P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z != 0) : toAffine W P = .
some _ _ ((nonsingular_of_Z_ne_zero hPz).mp…
· 使用定理 `WeierstrassCurve.Affine.Point.some.injEq`：∀ {R : Type r} [inst : CommRin
g R] {W' : WeierstrassCurve.Affine R} (x y : R) (h : W'.Nonsingular x y) (x_1 y_
1 : R)   (h_1 : W'.Nonsingular…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用引理 `mul_div_mul_left`：mul_div_mul_left (a b : G₀) (hc : c != 0) : c * a / (c
 * b) = a / b
· 使用定理 `IsUnit.pow`：∀ {M : Type u_1} [inst : Monoid M] {a : M} (n : ℕ), IsUnit a
 → IsUnit (a ^ n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `WeierstrassCurve.Jacobian.Point.toAffine_of_singular`：toAffine_of_singul
ar {P : Fin 3 -> F} (hP : ¬W.Nonsingular P) : toAffine W P = 0
-/
lemma toAffine_smul (P : Fin 3 → F) {u : F} (hu : IsUnit u) :
    toAffine W (u • P) = toAffine W P := by
  by_cases hP : W.Nonsingular P
  · by_cases hPz : P z = 0
    · rw [toAffine_of_Z_eq_zero <| mul_eq_zero_of_right u hPz, toAffine_of_Z_eq_zero hPz]
    · rw [toAffine_of_Z_ne_zero ((nonsingular_smul P hu).mpr hP) <| mul_ne_zero hu.ne_zero hPz,
        toAffine_of_Z_ne_zero hP hPz, Affine.Point.some.injEq]
      simp only [smul_fin3_ext, mul_pow, mul_div_mul_left _ _ (hu.pow _).ne_zero, and_self]
  · rw [toAffine_of_singular <| hP.comp (nonsingular_smul P hu).mp, toAffine_of_singular hP]
/-
**WeierstrassCurve.Jacobian.Point.toAffine_of_equiv** 是 Mathlib 中的一个引理，位于命名空间 `W
eierstrassCurve.Jacobian.Point`。
形式化陈述：toAffine_of_equiv {P Q : Fin 3 -> F} (h : P ≈ Q) : toAffine W P = toAffine
 W Q
参数：h : P ≈ Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Jacobian.Point.toAffine_smul`：toAffine_smul (P : Fin 3 
-> F) {u : F} (hu : IsUnit u) : toAffine W (u • P) = toAffine W P
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
lemma toAffine_of_equiv {P Q : Fin 3 → F} (h : P ≈ Q) : toAffine W P = toAffine W Q := by
  rcases h with ⟨u, rfl⟩
  exact toAffine_smul Q u.isUnit
/-
**WeierstrassCurve.Jacobian.Point.toAffine_neg** 是 Mathlib 中的一个引理，位于命名空间 `Weiers
trassCurve.Jacobian.Point`。
形式化陈述：toAffine_neg {P : Fin 3 -> F} (hP : W.Nonsingular P) : toAffine W (W.neg P
) = -toAffine W P
参数：hP : W.Nonsingular P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.neg_of_Z_eq_zero`：neg_of_Z_eq_zero {P : Fin 3 
-> F} (hP : W.Nonsingular P) (hPz : P z = 0) : W.neg P = -(P y / P x) • ![1, 1, 
0]
· 使用引理 `WeierstrassCurve.Jacobian.Point.toAffine_smul`：toAffine_smul (P : Fin 3 
-> F) {u : F} (hu : IsUnit u) : toAffine W (u • P) = toAffine W P
· 使用定理 `IsUnit.neg`：∀ {α : Type u} [inst : Monoid α] [inst_1 : HasDistribNeg α] 
{a : α}, IsUnit a → IsUnit (-a)
· 使用引理 `IsUnit.div`：div (ha : IsUnit a) (hb : IsUnit b) : IsUnit (a / b)
· 使用引理 `WeierstrassCurve.Jacobian.isUnit_Y_of_Z_eq_zero`：isUnit_Y_of_Z_eq_zero {
P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z = 0) : IsUnit (P y)
· 使用引理 `WeierstrassCurve.Jacobian.isUnit_X_of_Z_eq_zero`：isUnit_X_of_Z_eq_zero {
P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z = 0) : IsUnit (P x)
· 使用引理 `WeierstrassCurve.Jacobian.Point.toAffine_zero`：toAffine_zero : toAffine 
W ![1, 1, 0] = 0
· 使用引理 `WeierstrassCurve.Jacobian.Point.toAffine_of_Z_eq_zero`：toAffine_of_Z_eq_
zero {P : Fin 3 -> F} (hPz : P z = 0) : toAffine W P = 0
· 使用引理 `WeierstrassCurve.Affine.Point.neg_zero`：neg_zero : (-0 : W'.Point) = 0
· 使用引理 `WeierstrassCurve.Jacobian.neg_of_Z_ne_zero`：neg_of_Z_ne_zero {P : Fin 3 
-> F} (hPz : P z != 0) : W.neg P = P z • ![P x / P z ^ 2, W.toAffine.negY (P x /
 P z ^ 2) (P y / P z ^ 3), 1]
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WeierstrassCurve.Jacobian.nonsingular_some`：nonsingular_some (a b : R) :
 W'.Nonsingular ![a, b, 1] ↔ W'.toAffine.Nonsingular a b
· 使用引理 `WeierstrassCurve.Jacobian.nonsingular_smul`：nonsingular_smul (P : Fin 3 
-> R) {u : R} (hu : IsUnit u) : W'.Nonsingular (u • P) ↔ W'.Nonsingular P
· 使用引理 `WeierstrassCurve.Jacobian.nonsingular_neg`：nonsingular_neg {P : Fin 3 ->
 F} (hP : W.Nonsingular P) : W.Nonsingular W.neg P
· 使用引理 `WeierstrassCurve.Jacobian.Point.toAffine_some`：toAffine_some {X Y : F} (
h : W.Nonsingular ![X, Y, 1]) : toAffine W ![X, Y, 1] = .some _ _ ((nonsingular_
some ..).mp h)
· 使用引理 `WeierstrassCurve.Jacobian.nonsingular_of_Z_ne_zero`：nonsingular_of_Z_ne_
zero {P : Fin 3 -> F} (hPz : P z != 0) : W.Nonsingular P ↔ W.toAffine.Nonsingula
r (P x / P z ^ 2) (P y / P z ^ 3)
· 使用引理 `WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero`：toAffine_of_Z_ne_
zero {P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z != 0) : toAffine W P = .
some _ _ ((nonsingular_of_Z_ne_zero hPz).mp…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WeierstrassCurve.Affine.nonsingular_neg`：nonsingular_neg (x y : R) : W'.
Nonsingular x (W'.negY x y) ↔ W'.Nonsingular x y
· 使用引理 `WeierstrassCurve.Affine.Point.neg_some`：neg_some {x y : R} (h : W'.Nonsi
ngular x y) : -some _ _ h = some _ _ ((nonsingular_neg ..).mpr h)
-/
lemma toAffine_neg {P : Fin 3 → F} (hP : W.Nonsingular P) :
    toAffine W (W.neg P) = -toAffine W P := by
  by_cases hPz : P z = 0
  · rw [neg_of_Z_eq_zero hP hPz,
      toAffine_smul _ ((isUnit_Y_of_Z_eq_zero hP hPz).div <| isUnit_X_of_Z_eq_zero hP hPz).neg,
      toAffine_zero, toAffine_of_Z_eq_zero hPz, Affine.Point.neg_zero]
  · rw [neg_of_Z_ne_zero hPz, toAffine_smul _ <| Ne.isUnit hPz, toAffine_some <|
        (nonsingular_smul _ <| Ne.isUnit hPz).mp <| neg_of_Z_ne_zero hPz ▸ nonsingular_neg hP,
      toAffine_of_Z_ne_zero hP hPz, Affine.Point.neg_some]
/-
**WeierstrassCurve.Jacobian.Point.toAffine_add_of_Z_ne_zero** 是 Mathlib 中的一个引理，位
于命名空间 `WeierstrassCurve.Jacobian.Point`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma toAffine_add_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 → F}
    (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hxy : ¬(P x * Q z ^ 2 = Q x * P z ^ 2 ∧ P y * Q z ^ 3 = W.negY Q * P z ^ 3)) : toAffine W
      ![W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        1] = toAffine W P + toAffine W Q := by
  rw [toAffine_some <| nonsingular_add_of_Z_ne_zero hP hQ hPz hQz hxy, toAffine_of_Z_ne_zero hP hPz,
    toAffine_of_Z_ne_zero hQ hQz,
    Affine.Point.add_some <| by rwa [← X_eq_iff hPz hQz, ← Y_eq_iff' hPz hQz]]
/-
**WeierstrassCurve.Jacobian.Point.toAffine_add** 是 Mathlib 中的一个引理，位于命名空间 `Weiers
trassCurve.Jacobian.Point`。
形式化陈述：toAffine_add [DecidableEq F] {P Q : Fin 3 -> F} (hP : W.Nonsingular P) (hQ
 : W.Nonsingular Q) : toAffine W (W.add P Q) = toAffine W P + toAffine W Q
参数：hP : W.Nonsingular P；hQ : W.Nonsingular Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.Point.toAffine_of_Z_eq_zero`：toAffine_of_Z_eq_
zero {P : Fin 3 -> F} (hPz : P z = 0) : toAffine W P = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `WeierstrassCurve.Jacobian.add_of_Z_eq_zero`：add_of_Z_eq_zero {P Q : Fin 
3 -> F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) (hPz : P z = 0) (hQz : Q z
 = 0) : W.add P Q = P x ^ 2 • ![…
· 使用引理 `WeierstrassCurve.Jacobian.Point.toAffine_smul`：toAffine_smul (P : Fin 3 
-> F) {u : F} (hu : IsUnit u) : toAffine W (u • P) = toAffine W P
· 使用定理 `IsUnit.pow`：∀ {M : Type u_1} [inst : Monoid M] {a : M} (n : ℕ), IsUnit a
 → IsUnit (a ^ n)
· 使用引理 `WeierstrassCurve.Jacobian.isUnit_X_of_Z_eq_zero`：isUnit_X_of_Z_eq_zero {
P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z = 0) : IsUnit (P x)
· 使用引理 `WeierstrassCurve.Jacobian.Point.toAffine_zero`：toAffine_zero : toAffine 
W ![1, 1, 0] = 0
· 使用引理 `WeierstrassCurve.Jacobian.add_of_Z_eq_zero_left`：add_of_Z_eq_zero_left {
P Q : Fin 3 -> R} (hP : W'.Equation P) (hPz : P z = 0) (hQz : Q z != 0) : W'.add
 P Q = (P x * Q z) • Q
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsUnit.mul`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, IsUnit a → IsU
nit b → IsUnit (a * b)
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
· 使用引理 `WeierstrassCurve.Jacobian.add_of_Z_eq_zero_right`：add_of_Z_eq_zero_right
 {P Q : Fin 3 -> R} (hQ : W'.Equation Q) (hPz : P z != 0) (hQz : Q z = 0) : W'.a
dd P Q = -(Q x * P z) • P
· 使用定理 `IsUnit.neg`：∀ {α : Type u} [inst : Monoid α] [inst_1 : HasDistribNeg α] 
{a : α}, IsUnit a → IsUnit (-a)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WeierstrassCurve.Jacobian.nonsingular_of_Z_ne_zero`：nonsingular_of_Z_ne_
zero {P : Fin 3 -> F} (hPz : P z != 0) : W.Nonsingular P ↔ W.toAffine.Nonsingula
r (P x / P z ^ 2) (P y / P z ^ 3)
· 使用引理 `WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero`：toAffine_of_Z_ne_
zero {P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z != 0) : toAffine W P = .
some _ _ ((nonsingular_of_Z_ne_zero hPz).mp…
· 使用引理 `WeierstrassCurve.Affine.Point.add_of_Y_eq`：add_of_Y_eq {x₁ x₂ y₁ y₂ : F}
 {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂} (hx : x₁ = x₂) (hy : y₁ =
 W.negY x₂ y₂) : some _ _ h₁ + …
· 使用引理 `WeierstrassCurve.Jacobian.X_eq_iff`：X_eq_iff {P Q : Fin 3 -> F} (hPz : P
 z != 0) (hQz : Q z != 0) : P x * Q z ^ 2 = Q x * P z ^ 2 ↔ P x / P z ^ 2 = Q x 
/ Q z ^ 2
· 使用引理 `WeierstrassCurve.Jacobian.Y_eq_iff'`：Y_eq_iff' {P Q : Fin 3 -> F} (hPz :
 P z != 0) (hQz : Q z != 0) : P y * Q z ^ 3 = W.negY Q * P z ^ 3 ↔ P y / P z ^ 3
 = W.toAffine.negY (Q x /…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `WeierstrassCurve.Jacobian.add_of_Y_eq`：add_of_Y_eq {P Q : Fin 3 -> F} (h
Pz : P z != 0) (hQz : Q z != 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y *
 Q z ^ 3 = Q y * P z ^ 3) (…
· 使用引理 `WeierstrassCurve.Jacobian.isUnit_dblU_of_Y_eq`：isUnit_dblU_of_Y_eq {P Q 
: Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z != 0) (hQz : Q z != 0) (hx : P x
 * Q z ^ 2 = Q x * P z ^ 2) (hy : P…
· 使用引理 `WeierstrassCurve.Jacobian.add_of_Y_ne`：add_of_Y_ne {P Q : Fin 3 -> F} (h
P : W.Equation P) (hQ : W.Equation Q) (hPz : P z != 0) (hQz : Q z != 0) (hx : P 
x * Q z ^ 2 = Q x * P z ^ 2…
· 使用引理 `WeierstrassCurve.Jacobian.isUnit_addU_of_Y_ne`：isUnit_addU_of_Y_ne {P Q 
: Fin 3 -> F} (hPz : P z != 0) (hQz : Q z != 0) (hy : P y * Q z ^ 3 != Q y * P z
 ^ 3) : IsUnit (addU P Q)
· 使用定理 `_private.Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point.0.Weiers
trassCurve.Jacobian.Point.toAffine_add_of_Z_ne_zero`：∀ {F : Type u} [inst : Fiel
d F] {W : WeierstrassCurve.Jacobian F} [inst_1 : DecidableEq F] {P Q : Fin 3 → F
},   W.Nonsingular P →     W.Nons…
· 使用引理 `WeierstrassCurve.Jacobian.add_of_Y_ne'`：add_of_Y_ne' [DecidableEq F] {P 
Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z != 0) (hQz : 
Q z != 0) (hx : P x * Q z ^ …
· 使用定理 `not_and`：∀ {a b : Prop}, ¬(a ∧ b) ↔ a → ¬b
（共 33 条，此处仅展示前 30 条）
-/
lemma toAffine_add [DecidableEq F] {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    toAffine W (W.add P Q) = toAffine W P + toAffine W Q := by
  by_cases hPz : P z = 0
  · rw [toAffine_of_Z_eq_zero hPz, zero_add]
    by_cases hQz : Q z = 0
    · rw [add_of_Z_eq_zero hP hQ hPz hQz, toAffine_smul _ <| (isUnit_X_of_Z_eq_zero hP hPz).pow 2,
        toAffine_zero, toAffine_of_Z_eq_zero hQz]
    · rw [add_of_Z_eq_zero_left hP.left hPz hQz,
        toAffine_smul _ <| (isUnit_X_of_Z_eq_zero hP hPz).mul <| Ne.isUnit hQz]
  · by_cases hQz : Q z = 0
    · rw [add_of_Z_eq_zero_right hQ.left hPz hQz,
        toAffine_smul _ ((isUnit_X_of_Z_eq_zero hQ hQz).mul <| Ne.isUnit hPz).neg,
        toAffine_of_Z_eq_zero hQz, add_zero]
    · by_cases hxy : P x * Q z ^ 2 = Q x * P z ^ 2 ∧ P y * Q z ^ 3 = W.negY Q * P z ^ 3
      · rw [toAffine_of_Z_ne_zero hP hPz, toAffine_of_Z_ne_zero hQ hQz, Affine.Point.add_of_Y_eq
            ((X_eq_iff hPz hQz).mp hxy.left) ((Y_eq_iff' hPz hQz).mp hxy.right)]
        by_cases hy : P y * Q z ^ 3 = Q y * P z ^ 3
        · rw [add_of_Y_eq hPz hQz hxy.left hy hxy.right,
            toAffine_smul _ <| isUnit_dblU_of_Y_eq hP hPz hQz hxy.left hy hxy.right, toAffine_zero]
        · rw [add_of_Y_ne hP.left hQ.left hPz hQz hxy.left hy,
            toAffine_smul _ <| isUnit_addU_of_Y_ne hPz hQz hy, toAffine_zero]
      · have := toAffine_add_of_Z_ne_zero hP hQ hPz hQz hxy
        by_cases hx : P x * Q z ^ 2 = Q x * P z ^ 2
        · rwa [add_of_Y_ne' hP.left hQ.left hPz hQz hx <| not_and.mp hxy hx,
            toAffine_smul _ <| isUnit_dblZ_of_Y_ne' hP.left hQ.left hPz hx <| not_and.mp hxy hx]
        · rwa [add_of_X_ne hP.left hQ.left hPz hQz hx, toAffine_smul _ <| isUnit_addZ_of_X_ne hx]

/-- The natural map from a nonsingular Jacobian point on a Weierstrass curve `W` to its
corresponding nonsingular point in affine coordinates.

If `hP` is the nonsingular condition underlying a nonsingular Jacobian point `P` on `W`, then
`toAffineLift ⟨hP⟩` is definitionally equivalent to `toAffine W P`. -/
/-
**WeierstrassCurve.Jacobian.Point.toAffineLift** 是 Mathlib 中的一个定义，位于命名空间 `Weiers
trassCurve.Jacobian.Point`。
形式化陈述：toAffineLift (P : W.Point) : W.toAffine.Point
参数：P : W.Point。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Jacobian.Point.toAffine_of_equiv`：toAffine_of_equiv {P 
Q : Fin 3 -> F} (h : P ≈ Q) : toAffine W P = toAffine W Q

--- 原说明 ---
The natural map from a nonsingular Jacobian point on a Weierstrass curve `W` to 
its
corresponding nonsingular point in affine coordinates.

If `hP` is the nonsingular condition underlying a nonsingular Jacobian point `P`
 on `W`, then
`toAffineLift ⟨hP⟩` is definitionally equivalent to `toAffine W P`.
-/
noncomputable def toAffineLift (P : W.Point) : W.toAffine.Point :=
  P.point.lift _ fun _ _ => toAffine_of_equiv
/-
**WeierstrassCurve.Jacobian.Point.toAffineLift_eq** 是 Mathlib 中的一个引理，位于命名空间 `Wei
erstrassCurve.Jacobian.Point`。
形式化陈述：toAffineLift_eq {P : Fin 3 -> F} (hP : W.NonsingularLift ⟦P⟧) : toAffineLi
ft ⟨hP⟩ = toAffine W P
参数：hP : W.NonsingularLift ⟦P⟧。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toAffineLift_eq {P : Fin 3 → F} (hP : W.NonsingularLift ⟦P⟧) :
    toAffineLift ⟨hP⟩ = toAffine W P :=
  rfl
/-
**WeierstrassCurve.Jacobian.Point.toAffineLift_of_Z_eq_zero** 是 Mathlib 中的一个引理，位
于命名空间 `WeierstrassCurve.Jacobian.Point`。
形式化陈述：toAffineLift_of_Z_eq_zero {P : Fin 3 -> F} (hP : W.NonsingularLift ⟦P⟧) (h
Pz : P z = 0) : toAffineLift ⟨hP⟩ = 0
参数：hP : W.NonsingularLift ⟦P⟧；hPz : P z = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `WeierstrassCurve.Jacobian.Point.toAffine_of_Z_eq_zero`：toAffine_of_Z_eq_
zero {P : Fin 3 -> F} (hPz : P z = 0) : toAffine W P = 0
-/
lemma toAffineLift_of_Z_eq_zero {P : Fin 3 → F} (hP : W.NonsingularLift ⟦P⟧) (hPz : P z = 0) :
    toAffineLift ⟨hP⟩ = 0 :=
  toAffine_of_Z_eq_zero hPz
/-
**WeierstrassCurve.Jacobian.Point.toAffineLift_zero** 是 Mathlib 中的一个引理，位于命名空间 `W
eierstrassCurve.Jacobian.Point`。
形式化陈述：toAffineLift_zero : toAffineLift (0 : W.Point) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Jacobian.Point.toAffine_zero`：toAffine_zero : toAffine 
W ![1, 1, 0] = 0
-/
lemma toAffineLift_zero : toAffineLift (0 : W.Point) = 0 :=
  toAffine_zero
/-
**WeierstrassCurve.Jacobian.Point.toAffineLift_of_Z_ne_zero** 是 Mathlib 中的一个引理，位
于命名空间 `WeierstrassCurve.Jacobian.Point`。
形式化陈述：toAffineLift_of_Z_ne_zero {P : Fin 3 -> F} {hP : W.NonsingularLift ⟦P⟧} (h
Pz : P z != 0) : toAffineLift ⟨hP⟩ = .some _ _ ((nonsingular_of_Z_ne_zero hPz).m
p hP)
参数：hPz : P z != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero`：toAffine_of_Z_ne_
zero {P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z != 0) : toAffine W P = .
some _ _ ((nonsingular_of_Z_ne_zero hPz).mp…
-/
lemma toAffineLift_of_Z_ne_zero {P : Fin 3 → F} {hP : W.NonsingularLift ⟦P⟧} (hPz : P z ≠ 0) :
    toAffineLift ⟨hP⟩ = .some _ _ ((nonsingular_of_Z_ne_zero hPz).mp hP) :=
  toAffine_of_Z_ne_zero hP hPz
/-
**WeierstrassCurve.Jacobian.Point.toAffineLift_some** 是 Mathlib 中的一个引理，位于命名空间 `W
eierstrassCurve.Jacobian.Point`。
形式化陈述：toAffineLift_some {X Y : F} (h : W.NonsingularLift ⟦![X, Y, 1]⟧) : toAffin
eLift ⟨h⟩ = .some _ _ ((nonsingular_some ..).mp h)
参数：h : W.NonsingularLift ⟦![X, Y, 1]⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Jacobian.Point.toAffine_some`：toAffine_some {X Y : F} (
h : W.Nonsingular ![X, Y, 1]) : toAffine W ![X, Y, 1] = .some _ _ ((nonsingular_
some ..).mp h)
-/
lemma toAffineLift_some {X Y : F} (h : W.NonsingularLift ⟦![X, Y, 1]⟧) :
    toAffineLift ⟨h⟩ = .some _ _ ((nonsingular_some ..).mp h) :=
  toAffine_some h
/-
**WeierstrassCurve.Jacobian.Point.toAffineLift_neg** 是 Mathlib 中的一个引理，位于命名空间 `We
ierstrassCurve.Jacobian.Point`。
形式化陈述：toAffineLift_neg (P : W.Point) : (-P).toAffineLift = -P.toAffineLift
参数：P : W.Point。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Jacobian.Point.toAffine_neg`：toAffine_neg {P : Fin 3 ->
 F} (hP : W.Nonsingular P) : toAffine W (W.neg P) = -toAffine W P
-/
lemma toAffineLift_neg (P : W.Point) : (-P).toAffineLift = -P.toAffineLift := by
  rcases P with @⟨⟨_⟩, hP⟩
  exact toAffine_neg hP
/-
**WeierstrassCurve.Jacobian.Point.toAffineLift_add** 是 Mathlib 中的一个引理，位于命名空间 `We
ierstrassCurve.Jacobian.Point`。
形式化陈述：toAffineLift_add [DecidableEq F] (P Q : W.Point) : (P + Q).toAffineLift = 
P.toAffineLift + Q.toAffineLift
参数：P Q : W.Point。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Jacobian.Point.toAffine_add`：toAffine_add [DecidableEq 
F] {P Q : Fin 3 -> F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) : toAffine W
 (W.add P Q) = toAffine W P + toAf…
-/
lemma toAffineLift_add [DecidableEq F] (P Q : W.Point) :
    (P + Q).toAffineLift = P.toAffineLift + Q.toAffineLift := by
  rcases P, Q with ⟨@⟨⟨_⟩, hP⟩, @⟨⟨_⟩, hQ⟩⟩
  exact toAffine_add hP hQ

set_option backward.isDefEq.respectTransparency false in
variable (W) in
/-- The addition-preserving equivalence between the type of nonsingular Jacobian points on a
Weierstrass curve `W` and the type of nonsingular points in affine coordinates. -/
@[simps]
/-
**WeierstrassCurve.Jacobian.Point.toAffineAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `We
ierstrassCurve.Jacobian.Point`。
形式化陈述：toAffineAddEquiv [DecidableEq F] : W.Point ≃+ W.toAffine.Point where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Jacobian.Point.toAffineLift_add`：toAffineLift_add [Deci
dableEq F] (P Q : W.Point) : (P + Q).toAffineLift = P.toAffineLift + Q.toAffineL
ift

--- 原说明 ---
The addition-preserving equivalence between the type of nonsingular Jacobian poi
nts on a
Weierstrass curve `W` and the type of nonsingular points in affine coordinates.
-/
noncomputable def toAffineAddEquiv [DecidableEq F] : W.Point ≃+ W.toAffine.Point where
  toFun := toAffineLift
  invFun := fromAffine
  left_inv := by
    rintro @⟨⟨P⟩, hP⟩
    by_cases hPz : P z = 0
    · rw [Point.ext_iff, toAffineLift_eq, toAffine_of_Z_eq_zero hPz]
      exact Quotient.eq.mpr <| Setoid.symm <| equiv_zero_of_Z_eq_zero hP hPz
    · rw [Point.ext_iff, toAffineLift_eq, toAffine_of_Z_ne_zero hP hPz]
      exact Quotient.eq.mpr <| Setoid.symm <| equiv_some_of_Z_ne_zero hPz
  right_inv := by
    rintro (_ | _)
    · rw [← Affine.Point.zero_def, fromAffine_zero, toAffineLift_zero]
    · rw [fromAffine_some, toAffineLift_some]
  map_add' := toAffineLift_add
/-
**WeierstrassCurve.Jacobian.Point.** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurve.J
acobian.Point`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : AddCommGroup W.Point where
  nsmul := nsmulRec
  zsmul := zsmulRec
  zero_add _ := by
    classical
    apply (toAffineAddEquiv W).injective
    simp only [map_add, toAffineAddEquiv_apply, toAffineLift_zero, zero_add]
  add_zero _ := by
    classical
    apply (toAffineAddEquiv W).injective
    simp only [map_add, toAffineAddEquiv_apply, toAffineLift_zero, add_zero]
  neg_add_cancel P := by
    classical
    apply (toAffineAddEquiv W).injective
    simp only [map_add, toAffineAddEquiv_apply, toAffineLift_neg, neg_add_cancel, toAffineLift_zero]
  add_comm _ _ := by
    classical
    apply (toAffineAddEquiv W).injective
    simp only [map_add, add_comm]
  add_assoc _ _ _ := by
    classical
    apply (toAffineAddEquiv W).injective
    simp only [map_add, add_assoc]

end Point

/-! ## Maps and base changes -/

@[simp]
/-
**WeierstrassCurve.Jacobian.map_neg** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve.
Jacobian`。
形式化陈述：∀ {R : Type r} {S : Type s} [inst : CommRing R] [inst_1 : CommRing S] {W' 
: WeierstrassCurve.Jacobian R} (f : R →+* S)   (P : Fin 3 → R), (W'.map f).neg (
⇑f ∘ P) = ⇑f ∘ W'.neg P
参数：f : R →+* S；P : Fin 3 → R；W'.map f；⇑f ∘ P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `WeierstrassCurve.Jacobian.map_negY`：map_negY : (W'.map f).negY (f ∘ P) =
 f (W'.negY P)
· 使用引理 `WeierstrassCurve.Jacobian.comp_fin3`：comp_fin3 {S : Type s} (f : R -> S)
 (a b c : R) : f ∘ ![a, b, c] = ![f a, f b, f c]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
## Maps and base changes
-/
protected lemma map_neg (f : R →+* S) (P : Fin 3 → R) : (W'.map f).neg (f ∘ P) = f ∘ W'.neg P := by
  simp only [neg, map_negY, comp_fin3]
  map_simp

@[simp]
/-
**WeierstrassCurve.Jacobian.map_add** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve.
Jacobian`。
形式化陈述：∀ {F : Type u} {K : Type v} [inst : Field F] [inst_1 : Field K] {W : Weier
strassCurve.Jacobian F} (f : F →+* K)   {P Q : Fin 3 → F}, W.Nonsingular P → W.N
onsingular Q → (W.map f).add (⇑f ∘ P) (⇑f ∘ Q) = ⇑f ∘ W.add P Q
参数：f : F →+* K；W.map f；⇑f ∘ P；⇑f ∘ Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.add_of_equiv`：add_of_equiv {P Q : Fin 3 -> R} 
(h : P ≈ Q) : W'.add P Q = W'.dblXYZ P
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WeierstrassCurve.Jacobian.comp_equiv_comp`：comp_equiv_comp (f : F ->+* K
) {P Q : Fin 3 -> F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) : f ∘ P ≈ f ∘
 Q ↔ P ≈ Q
· 使用引理 `WeierstrassCurve.Jacobian.map_dblXYZ`：map_dblXYZ : (W'.map f).dblXYZ (f 
∘ P) = f ∘ dblXYZ W' P
· 使用引理 `WeierstrassCurve.Jacobian.add_of_not_equiv`：add_of_not_equiv {P Q : Fin 
3 -> R} (h : ¬P ≈ Q) : W'.add P Q = W'.addXYZ P Q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WeierstrassCurve.Jacobian.map_addXYZ`：map_addXYZ : (W'.map f).addXYZ (f 
∘ P) (f ∘ Q) = f ∘ addXYZ W' P Q
-/
protected lemma map_add (f : F →+* K) {P Q : Fin 3 → F} (hP : W.Nonsingular P)
    (hQ : W.Nonsingular Q) : (W.map f).add (f ∘ P) (f ∘ Q) = f ∘ W.add P Q := by
  by_cases h : P ≈ Q
  · rw [add_of_equiv <| (comp_equiv_comp f hP hQ).mpr h, add_of_equiv h, map_dblXYZ]
  · rw [add_of_not_equiv <| h.comp (comp_equiv_comp f hP hQ).mp, add_of_not_equiv h, map_addXYZ]
/-
**WeierstrassCurve.Jacobian.baseChange_neg** 是 Mathlib 中的一个引理，位于命名空间 `Weierstras
sCurve.Jacobian`。
形式化陈述：baseChange_neg [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R 
S A] [Algebra R B] [Algebra S B] [IsScalarTower R S B] (f : A ->ₐ[S] B) (P : Fin
 3 -> A) : (W'⁄B).neg (f ∘ P) = f ∘ (W'⁄A).neg P
参数：f : A ->ₐ[S] B；P : Fin 3 -> A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.coe_coe`：coe_coe {F : Type*} [FunLike F α β] [RingHomClass F α β
] (f : F) : ((f : α ->+* β) : α -> β) = f
· 使用定理 `WeierstrassCurve.Jacobian.map_neg`：∀ {R : Type r} {S : Type s} [inst : C
ommRing R] [inst_1 : CommRing S] {W' : WeierstrassCurve.Jacobian R} (f : R →+* S
)   (P : Fin 3 → R), (W…
· 使用引理 `WeierstrassCurve.Jacobian.map_baseChange`：map_baseChange : (W'⁄A).map f 
= W'⁄B
-/
lemma baseChange_neg [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Algebra R B]
    [Algebra S B] [IsScalarTower R S B] (f : A →ₐ[S] B) (P : Fin 3 → A) :
    (W'⁄B).neg (f ∘ P) = f ∘ (W'⁄A).neg P := by
  rw [← RingHom.coe_coe, ← WeierstrassCurve.Jacobian.map_neg, map_baseChange]
/-
**WeierstrassCurve.Jacobian.baseChange_add** 是 Mathlib 中的一个引理，位于命名空间 `Weierstras
sCurve.Jacobian`。
形式化陈述：baseChange_add [Algebra R S] [Algebra R F] [Algebra S F] [IsScalarTower R 
S F] [Algebra R K] [Algebra S K] [IsScalarTower R S K] (f : F ->ₐ[S] K) {P Q : F
in 3 -> F} (hP : (W'⁄F).Nonsingular P) (hQ : (W'⁄F).Nonsingular Q) : (W'⁄K).add 
(f ∘ P) (f ∘ Q) = f ∘ (W'⁄F).add P Q
参数：f : F ->ₐ[S] K；hP : (W'⁄F).Nonsingular P；hQ : (W'⁄F).Nonsingular Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.coe_coe`：coe_coe {F : Type*} [FunLike F α β] [RingHomClass F α β
] (f : F) : ((f : α ->+* β) : α -> β) = f
· 使用定理 `WeierstrassCurve.Jacobian.map_add`：∀ {F : Type u} {K : Type v} [inst : F
ield F] [inst_1 : Field K] {W : WeierstrassCurve.Jacobian F} (f : F →+* K)   {P 
Q : Fin 3 → F}, W.Nonsi…
· 使用引理 `WeierstrassCurve.Jacobian.map_baseChange`：map_baseChange : (W'⁄A).map f 
= W'⁄B
-/
lemma baseChange_add [Algebra R S] [Algebra R F] [Algebra S F] [IsScalarTower R S F] [Algebra R K]
    [Algebra S K] [IsScalarTower R S K] (f : F →ₐ[S] K) {P Q : Fin 3 → F}
    (hP : (W'⁄F).Nonsingular P) (hQ : (W'⁄F).Nonsingular Q) :
    (W'⁄K).add (f ∘ P) (f ∘ Q) = f ∘ (W'⁄F).add P Q := by
  rw [← RingHom.coe_coe, ← WeierstrassCurve.Jacobian.map_add _ hP hQ, map_baseChange]

end Jacobian

/-- An abbreviation for `WeierstrassCurve.Jacobian.Point.fromAffine` for dot notation. -/
/-
**WeierstrassCurve.Affine.Point.toJacobian** 是 Mathlib 中的一个定义，位于命名空间 `Weierstras
sCurve.Affine.Point`。
形式化陈述：{R : Type r} →   [inst : CommRing R] →     [Nontrivial R] → {W : Weierstra
ssCurve.Affine R} → W.Point → (WeierstrassCurve.toJacobian W).Point
参数：WeierstrassCurve.toJacobian W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abbreviation for `WeierstrassCurve.Jacobian.Point.fromAffine` for dot notatio
n.
-/
abbrev Affine.Point.toJacobian [Nontrivial R] {W : Affine R} (P : W.Point) : W.toJacobian.Point :=
  Jacobian.Point.fromAffine P

end WeierstrassCurve

