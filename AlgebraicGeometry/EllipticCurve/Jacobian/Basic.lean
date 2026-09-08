/-
Copyright (c) 2025 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.Data.Fin.Tuple.Reflection
public import Mathlib.Tactic.Ring.NamePolyVars

/-!
# Weierstrass equations and the nonsingular condition in Jacobian coordinates

A point on the projective plane over a commutative ring `R` with weights `(2, 3, 1)` is an
equivalence class `[x : y : z]` of triples `(x, y, z) ≠ (0, 0, 0)` of elements in `R` such that
`(x, y, z) ∼ (x', y', z')` if there is some unit `u` in `Rˣ` with `(x, y, z) = (u²x', u³y', uz')`.

Let `W` be a Weierstrass curve over a commutative ring `R` with coefficients `aᵢ`. A
*Jacobian point* is a point on the projective plane over `R` with weights `(2, 3, 1)` satisfying the
*`(2, 3, 1)`-homogeneous Weierstrass equation* `W(X, Y, Z) = 0` in *Jacobian coordinates*, where
`W(X, Y, Z) := Y² + a₁XYZ + a₃YZ³ - (X³ + a₂X²Z² + a₄XZ⁴ + a₆Z⁶)`. It is *nonsingular* if its
partial derivatives `W_X(x, y, z)`, `W_Y(x, y, z)`, and `W_Z(x, y, z)` do not vanish simultaneously.

This file gives an explicit implementation of equivalence classes of triples up to scaling by
weights, and defines polynomials associated to Weierstrass equations and the nonsingular condition
in Jacobian coordinates. The group law on the actual type of nonsingular Jacobian points will be
defined in `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Point.lean`, based on the formulae for
group operations in `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Formula.lean`.

## Main definitions

* `WeierstrassCurve.Jacobian.PointClass`: the equivalence class of a point representative.
* `WeierstrassCurve.Jacobian.Nonsingular`: the nonsingular condition on a point representative.
* `WeierstrassCurve.Jacobian.NonsingularLift`: the nonsingular condition on a point class.

## Main statements

* `WeierstrassCurve.Jacobian.polynomial_relation`: Euler's homogeneous function theorem.

## Implementation notes

All definitions and lemmas for Weierstrass curves in Jacobian coordinates live in the namespace
`WeierstrassCurve.Jacobian` to distinguish them from those in other coordinates. This is simply an
abbreviation for `WeierstrassCurve` that can be converted using `WeierstrassCurve.toJacobian`. This
can be converted into `WeierstrassCurve.Affine` using `WeierstrassCurve.Jacobian.toAffine`.

A point representative is implemented as a term `P` of type `Fin 3 → R`, which allows for the vector
notation `![x, y, z]`. However, `P` is not syntactically equivalent to the expanded vector
`![P x, P y, P z]`, so the lemmas `fin3_def` and `fin3_def_ext` can be used to convert between the
two forms. The equivalence of two point representatives `P` and `Q` is implemented as an equivalence
of orbits of the action of `Rˣ`, or equivalently that there is some unit `u` of `R` such that
`P = u • Q`. However, `u • Q` is not syntactically equal to `![u² * Q x, u³ * Q y, u * Q z]`, so the
lemmas `smul_fin3` and `smul_fin3_ext` can be used to convert between the two forms. Files in
`Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian` make extensive use of `erw` to get around this.
While `erw` is often an indication of a problem, in this case it is self-contained and should not
cause any issues. It would alternatively be possible to add some automation to assist here.

Whenever possible, all changes to documentation and naming of definitions and theorems should be
mirrored in `Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Basic.lean`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, Jacobian, Weierstrass equation, nonsingular
-/

@[expose] public section

local notation3 "x" => (0 : Fin 3)

local notation3 "y" => (1 : Fin 3)

local notation3 "z" => (2 : Fin 3)

open MvPolynomial

local macro "eval_simp" : tactic =>
  `(tactic| simp only [eval_C, eval_X, eval_add, eval_sub, eval_mul, eval_pow])

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_C, map_X, map_neg, map_add, map_sub, map_mul, map_pow,
    map_div₀, WeierstrassCurve.map, Function.comp_apply])

local macro "matrix_simp" : tactic =>
  `(tactic| simp only [Matrix.head_cons, Matrix.tail_cons, Matrix.smul_empty, Matrix.smul_cons,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two])

local macro "pderiv_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, pderiv_mul, pderiv_pow,
    pderiv_C, pderiv_X_self, pderiv_X_of_ne one_ne_zero, pderiv_X_of_ne one_ne_zero.symm,
    pderiv_X_of_ne (by decide : z ≠ x), pderiv_X_of_ne (by decide : x ≠ z),
    pderiv_X_of_ne (by decide : z ≠ y), pderiv_X_of_ne (by decide : y ≠ z)])

universe r s u v

variable {R : Type r} {F : Type u}

name_poly_vars X, Y, Z over R

namespace WeierstrassCurve

/-! ## Jacobian coordinates -/

variable (R) in
/-- An abbreviation for a Weierstrass curve in Jacobian coordinates. -/
/-
**WeierstrassCurve.Jacobian** 是 Mathlib 中的一个缩写定义，位于命名空间 `WeierstrassCurve`。
形式化陈述：Jacobian : Type r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abbreviation for a Weierstrass curve in Jacobian coordinates.
-/
abbrev Jacobian : Type r :=
  WeierstrassCurve R

/-- The conversion from a Weierstrass curve to Jacobian coordinates. -/
/-
**WeierstrassCurve.toJacobian** 是 Mathlib 中的一个缩写定义，位于命名空间 `WeierstrassCurve`。
形式化陈述：toJacobian (W : WeierstrassCurve R) : Jacobian R
参数：W : WeierstrassCurve R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The conversion from a Weierstrass curve to Jacobian coordinates.
-/
abbrev toJacobian (W : WeierstrassCurve R) : Jacobian R :=
  W

namespace Jacobian

/-- The conversion from a Weierstrass curve in Jacobian coordinates to affine coordinates. -/
/-
**WeierstrassCurve.Jacobian.toAffine** 是 Mathlib 中的一个缩写定义，位于命名空间 `WeierstrassCur
ve.Jacobian`。
形式化陈述：toAffine (W' : Jacobian R) : Affine R
参数：W' : Jacobian R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The conversion from a Weierstrass curve in Jacobian coordinates to affine coordi
nates.
-/
abbrev toAffine (W' : Jacobian R) : Affine R :=
  W'
/-
**WeierstrassCurve.Jacobian.fin3_def** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve
.Jacobian`。
形式化陈述：fin3_def (P : Fin 3 -> R) : ![P x, P y, P z] = P
参数：P : Fin 3 -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
lemma fin3_def (P : Fin 3 → R) : ![P x, P y, P z] = P := by
  ext n; fin_cases n <;> rfl
/-
**WeierstrassCurve.Jacobian.fin3_def_ext** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassC
urve.Jacobian`。
形式化陈述：fin3_def_ext (a b c : R) : ![a, b, c] x = a ∧ ![a, b, c] y = b ∧ ![a, b, c
] z = c
参数：a b c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma fin3_def_ext (a b c : R) : ![a, b, c] x = a ∧ ![a, b, c] y = b ∧ ![a, b, c] z = c :=
  ⟨rfl, rfl, rfl⟩
/-
**WeierstrassCurve.Jacobian.comp_fin3** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurv
e.Jacobian`。
形式化陈述：comp_fin3 {S : Type s} (f : R -> S) (a b c : R) : f ∘ ![a, b, c] = ![f a, 
f b, f c]
参数：f : R -> S；a b c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FinVec.map_eq`：map_eq (f : α -> β) {m} (v : Fin m -> α) : map f v = f ∘ 
v
-/
lemma comp_fin3 {S : Type s} (f : R → S) (a b c : R) : f ∘ ![a, b, c] = ![f a, f b, f c] :=
  (FinVec.map_eq ..).symm

variable [CommRing R] [Field F] {W' : Jacobian R} {W : Jacobian F} {S : Type s} [CommRing S]
  {A : Type u} [CommRing A] {B : Type v} [CommRing B] {K : Type v} [Field K]

/-- The scalar multiplication for a Jacobian point representative on a Weierstrass curve. -/
/-
**WeierstrassCurve.Jacobian.** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurve.Jacobia
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The scalar multiplication for a Jacobian point representative on a Weierstrass c
urve.
-/
scoped instance : SMul R <| Fin 3 → R :=
  ⟨fun u P => ![u ^ 2 * P x, u ^ 3 * P y, u * P z]⟩
/-
**WeierstrassCurve.Jacobian.smul_fin3** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurv
e.Jacobian`。
形式化陈述：smul_fin3 (P : Fin 3 -> R) (u : R) : u • P = ![u ^ 2 * P x, u ^ 3 * P y, u
 * P z]
参数：P : Fin 3 -> R；u : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_fin3 (P : Fin 3 → R) (u : R) : u • P = ![u ^ 2 * P x, u ^ 3 * P y, u * P z] :=
  rfl
/-
**WeierstrassCurve.Jacobian.smul_fin3_ext** 是 Mathlib 中的一个引理，位于命名空间 `Weierstrass
Curve.Jacobian`。
形式化陈述：smul_fin3_ext (P : Fin 3 -> R) (u : R) : (u • P) x = u ^ 2 * P x ∧ (u • P)
 y = u ^ 3 * P y ∧ (u • P) z = u * P z
参数：P : Fin 3 -> R；u : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma smul_fin3_ext (P : Fin 3 → R) (u : R) :
    (u • P) x = u ^ 2 * P x ∧ (u • P) y = u ^ 3 * P y ∧ (u • P) z = u * P z :=
  ⟨rfl, rfl, rfl⟩
/-
**WeierstrassCurve.Jacobian.comp_smul** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurv
e.Jacobian`。
形式化陈述：comp_smul (f : R ->+* S) (P : Fin 3 -> R) (u : R) : f ∘ (u • P) = f u • f 
∘ P
参数：f : R ->+* S；P : Fin 3 -> R；u : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `WeierstrassCurve.Jacobian.comp_fin3`：comp_fin3 {S : Type s} (f : R -> S)
 (a b c : R) : f ∘ ![a, b, c] = ![f a, f b, f c]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
lemma comp_smul (f : R →+* S) (P : Fin 3 → R) (u : R) : f ∘ (u • P) = f u • f ∘ P := by
  ext n; fin_cases n <;> simp only [smul_fin3, comp_fin3] <;> map_simp

/-- The multiplicative action for a Jacobian point representative on a Weierstrass curve. -/
/-
**WeierstrassCurve.Jacobian.** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurve.Jacobia
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplicative action for a Jacobian point representative on a Weierstrass c
urve.
-/
scoped instance : MulAction R <| Fin 3 → R where
  one_smul _ := by simp only [smul_fin3, one_pow, one_mul, fin3_def]
  mul_smul _ _ _ := by simp only [smul_fin3, mul_pow, mul_assoc, fin3_def_ext]

/-- The equivalence setoid for a Jacobian point representative on a Weierstrass curve. -/
@[reducible]
/-
**WeierstrassCurve.Jacobian.** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurve.Jacobia
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence setoid for a Jacobian point representative on a Weierstrass curv
e.
-/
scoped instance : Setoid <| Fin 3 → R :=
  MulAction.orbitRel Rˣ <| Fin 3 → R

variable (R) in
/-- The equivalence class of a Jacobian point representative on a Weierstrass curve. -/
/-
**WeierstrassCurve.Jacobian.PointClass** 是 Mathlib 中的一个缩写定义，位于命名空间 `WeierstrassC
urve.Jacobian`。
形式化陈述：PointClass : Type r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence class of a Jacobian point representative on a Weierstrass curve.
-/
abbrev PointClass : Type r :=
  MulAction.orbitRel.Quotient Rˣ <| Fin 3 → R
/-
**WeierstrassCurve.Jacobian.smul_equiv** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCur
ve.Jacobian`。
形式化陈述：smul_equiv (P : Fin 3 -> R) {u : R} (hu : IsUnit u) : u • P ≈ P
参数：P : Fin 3 -> R；hu : IsUnit u。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_equiv (P : Fin 3 → R) {u : R} (hu : IsUnit u) : u • P ≈ P :=
  ⟨hu.unit, rfl⟩

@[simp]
/-
**WeierstrassCurve.Jacobian.smul_eq** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve.
Jacobian`。
形式化陈述：smul_eq (P : Fin 3 -> R) {u : R} (hu : IsUnit u) : (⟦u • P⟧ : PointClass R
) = ⟦P⟧
参数：P : Fin 3 -> R；hu : IsUnit u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
· 使用引理 `WeierstrassCurve.Jacobian.smul_equiv`：smul_equiv (P : Fin 3 -> R) {u : R
} (hu : IsUnit u) : u • P ≈ P
-/
lemma smul_eq (P : Fin 3 → R) {u : R} (hu : IsUnit u) : (⟦u • P⟧ : PointClass R) = ⟦P⟧ :=
  Quotient.eq.mpr <| smul_equiv P hu
/-
**WeierstrassCurve.Jacobian.smul_equiv_smul** 是 Mathlib 中的一个引理，位于命名空间 `Weierstra
ssCurve.Jacobian`。
形式化陈述：smul_equiv_smul (P Q : Fin 3 -> R) {u v : R} (hu : IsUnit u) (hv : IsUnit 
v) : u • P ≈ v • Q ↔ P ≈ Q
参数：P Q : Fin 3 -> R；hu : IsUnit u；hv : IsUnit v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quotient.eq_iff_equiv`：Quotient.eq_iff_equiv {r : Setoid α} {x y : α} : 
Quotient.mk r x = ⟦y⟧ ↔ x ≈ y
· 使用引理 `WeierstrassCurve.Jacobian.smul_eq`：smul_eq (P : Fin 3 -> R) {u : R} (hu 
: IsUnit u) : (⟦u • P⟧ : PointClass R) = ⟦P⟧
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma smul_equiv_smul (P Q : Fin 3 → R) {u v : R} (hu : IsUnit u) (hv : IsUnit v) :
    u • P ≈ v • Q ↔ P ≈ Q := by
  rw [← Quotient.eq_iff_equiv, ← Quotient.eq_iff_equiv, smul_eq P hu, smul_eq Q hv]
/-
**WeierstrassCurve.Jacobian.equiv_iff_eq_of_Z_eq'** 是 Mathlib 中的一个引理，位于命名空间 `Wei
erstrassCurve.Jacobian`。
形式化陈述：equiv_iff_eq_of_Z_eq' {P Q : Fin 3 -> R} (hz : P z = Q z) (hQz : Q z in no
nZeroDivisors R) : P ≈ Q ↔ P = Q
参数：hz : P z = Q z；hQz : Q z in nonZeroDivisors R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `mul_cancel_right_mem_nonZeroDivisors`：mul_cancel_right_mem_nonZeroDiviso
rs (hr : r in R⁰) : x * r = y * r ↔ x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Quotient.exact`：∀ {α : Sort u} {s : Setoid α} {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈
 b
-/
lemma equiv_iff_eq_of_Z_eq' {P Q : Fin 3 → R} (hz : P z = Q z) (hQz : Q z ∈ nonZeroDivisors R) :
    P ≈ Q ↔ P = Q := by
  refine ⟨?_, Quotient.exact.comp <| congrArg _⟩
  rintro ⟨u, rfl⟩
  simp only [Units.smul_def, (mul_cancel_right_mem_nonZeroDivisors hQz).mp <| one_mul (Q z) ▸ hz]
  rw [one_smul]
/-
**WeierstrassCurve.Jacobian.equiv_iff_eq_of_Z_eq** 是 Mathlib 中的一个引理，位于命名空间 `Weie
rstrassCurve.Jacobian`。
形式化陈述：equiv_iff_eq_of_Z_eq [NoZeroDivisors R] {P Q : Fin 3 -> R} (hz : P z = Q z
) (hQz : Q z != 0) : P ≈ Q ↔ P = Q
参数：hz : P z = Q z；hQz : Q z != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `WeierstrassCurve.Jacobian.equiv_iff_eq_of_Z_eq'`：equiv_iff_eq_of_Z_eq' {
P Q : Fin 3 -> R} (hz : P z = Q z) (hQz : Q z in nonZeroDivisors R) : P ≈ Q ↔ P 
= Q
· 使用定理 `mem_nonZeroDivisors_of_ne_zero`：mem_nonZeroDivisors_of_ne_zero (hx : x !
= 0) : x in M₀⁰
-/
lemma equiv_iff_eq_of_Z_eq [NoZeroDivisors R] {P Q : Fin 3 → R} (hz : P z = Q z) (hQz : Q z ≠ 0) :
    P ≈ Q ↔ P = Q :=
  equiv_iff_eq_of_Z_eq' hz <| mem_nonZeroDivisors_of_ne_zero hQz
/-
**WeierstrassCurve.Jacobian.Z_eq_zero_of_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Weiers
trassCurve.Jacobian`。
形式化陈述：Z_eq_zero_of_equiv {P Q : Fin 3 -> R} (h : P ≈ Q) : P z = 0 ↔ Q z = 0
参数：h : P ≈ Q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Z_eq_zero_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : P z = 0 ↔ Q z = 0 := by
  rcases h with ⟨_, rfl⟩
  simp only [Units.smul_def, smul_fin3_ext, Units.mul_right_eq_zero]
/-
**WeierstrassCurve.Jacobian.X_eq_of_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Weierstrass
Curve.Jacobian`。
形式化陈述：X_eq_of_equiv {P Q : Fin 3 -> R} (h : P ≈ Q) : P x * Q z ^ 2 = Q x * P z ^
 2
参数：h : P ≈ Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
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
-/
lemma X_eq_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : P x * Q z ^ 2 = Q x * P z ^ 2 := by
  rcases h with ⟨u, rfl⟩
  simp only [Units.smul_def, smul_fin3_ext]
  ring1
/-
**WeierstrassCurve.Jacobian.Y_eq_of_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Weierstrass
Curve.Jacobian`。
形式化陈述：Y_eq_of_equiv {P Q : Fin 3 -> R} (h : P ≈ Q) : P y * Q z ^ 3 = Q y * P z ^
 3
参数：h : P ≈ Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
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
-/
lemma Y_eq_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : P y * Q z ^ 3 = Q y * P z ^ 3 := by
  rcases h with ⟨u, rfl⟩
  simp only [Units.smul_def, smul_fin3_ext]
  ring1
/-
**WeierstrassCurve.Jacobian.not_equiv_of_Z_eq_zero_left** 是 Mathlib 中的一个引理，位于命名空
间 `WeierstrassCurve.Jacobian`。
形式化陈述：not_equiv_of_Z_eq_zero_left {P Q : Fin 3 -> R} (hPz : P z = 0) (hQz : Q z 
!= 0) : ¬P ≈ Q
参数：hPz : P z = 0；hQz : Q z != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WeierstrassCurve.Jacobian.Z_eq_zero_of_equiv`：Z_eq_zero_of_equiv {P Q : 
Fin 3 -> R} (h : P ≈ Q) : P z = 0 ↔ Q z = 0
-/
lemma not_equiv_of_Z_eq_zero_left {P Q : Fin 3 → R} (hPz : P z = 0) (hQz : Q z ≠ 0) : ¬P ≈ Q :=
  fun h => hQz <| (Z_eq_zero_of_equiv h).mp hPz
/-
**WeierstrassCurve.Jacobian.not_equiv_of_Z_eq_zero_right** 是 Mathlib 中的一个引理，位于命名
空间 `WeierstrassCurve.Jacobian`。
形式化陈述：not_equiv_of_Z_eq_zero_right {P Q : Fin 3 -> R} (hPz : P z != 0) (hQz : Q 
z = 0) : ¬P ≈ Q
参数：hPz : P z != 0；hQz : Q z = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WeierstrassCurve.Jacobian.Z_eq_zero_of_equiv`：Z_eq_zero_of_equiv {P Q : 
Fin 3 -> R} (h : P ≈ Q) : P z = 0 ↔ Q z = 0
-/
lemma not_equiv_of_Z_eq_zero_right {P Q : Fin 3 → R} (hPz : P z ≠ 0) (hQz : Q z = 0) : ¬P ≈ Q :=
  fun h => hPz <| (Z_eq_zero_of_equiv h).mpr hQz
/-
**WeierstrassCurve.Jacobian.not_equiv_of_X_ne** 是 Mathlib 中的一个引理，位于命名空间 `Weierst
rassCurve.Jacobian`。
形式化陈述：not_equiv_of_X_ne {P Q : Fin 3 -> R} (hx : P x * Q z ^ 2 != Q x * P z ^ 2)
 : ¬P ≈ Q
参数：hx : P x * Q z ^ 2 != Q x * P z ^ 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `WeierstrassCurve.Jacobian.X_eq_of_equiv`：X_eq_of_equiv {P Q : Fin 3 -> R
} (h : P ≈ Q) : P x * Q z ^ 2 = Q x * P z ^ 2
-/
lemma not_equiv_of_X_ne {P Q : Fin 3 → R} (hx : P x * Q z ^ 2 ≠ Q x * P z ^ 2) : ¬P ≈ Q :=
  hx.comp X_eq_of_equiv
/-
**WeierstrassCurve.Jacobian.not_equiv_of_Y_ne** 是 Mathlib 中的一个引理，位于命名空间 `Weierst
rassCurve.Jacobian`。
形式化陈述：not_equiv_of_Y_ne {P Q : Fin 3 -> R} (hy : P y * Q z ^ 3 != Q y * P z ^ 3)
 : ¬P ≈ Q
参数：hy : P y * Q z ^ 3 != Q y * P z ^ 3。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `WeierstrassCurve.Jacobian.Y_eq_of_equiv`：Y_eq_of_equiv {P Q : Fin 3 -> R
} (h : P ≈ Q) : P y * Q z ^ 3 = Q y * P z ^ 3
-/
lemma not_equiv_of_Y_ne {P Q : Fin 3 → R} (hy : P y * Q z ^ 3 ≠ Q y * P z ^ 3) : ¬P ≈ Q :=
  hy.comp Y_eq_of_equiv
/-
**WeierstrassCurve.Jacobian.equiv_of_X_eq_of_Y_eq** 是 Mathlib 中的一个引理，位于命名空间 `Wei
erstrassCurve.Jacobian`。
形式化陈述：equiv_of_X_eq_of_Y_eq {P Q : Fin 3 -> F} (hPz : P z != 0) (hQz : Q z != 0)
 (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = Q y * P z ^ 3) : P ≈
 Q
参数：hPz : P z != 0；hQz : Q z != 0；hx : P x * Q z ^ 2 = Q x * P z ^ 2；hy : P y * Q
 z ^ 3 = Q y * P z ^ 3。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Units.val_div_eq_div_val`：val_div_eq_div_val : forall u₁ u₂ : αˣ, ↑(u₁ /
 u₂) = (u₁ / u₂ : α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_div`：mul_div (a b c : G) : a * (b / c) = a * b / c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_div_cancel_right₀`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [ins
t_1 : Div M₀] [MulDivCancelClass M₀] (a : M₀) {b : M₀},   b ≠ 0 → a * b / b = a
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `WeierstrassCurve.Jacobian.fin3_def`：fin3_def (P : Fin 3 -> R) : ![P x, P
 y, P z] = P
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equiv_of_X_eq_of_Y_eq {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = Q y * P z ^ 3) : P ≈ Q := by
  use Units.mk0 _ hPz / Units.mk0 _ hQz
  simp only [Units.smul_def, smul_fin3, Units.val_div_eq_div_val, Units.val_mk0, div_pow, mul_comm,
    mul_div, ← hx, ← hy, mul_div_cancel_right₀ _ <| pow_ne_zero _ hQz, mul_div_cancel_right₀ _ hQz,
    fin3_def]
/-
**WeierstrassCurve.Jacobian.equiv_some_of_Z_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `W
eierstrassCurve.Jacobian`。
形式化陈述：equiv_some_of_Z_ne_zero {P : Fin 3 -> F} (hPz : P z != 0) : P ≈ ![P x / P 
z ^ 2, P y / P z ^ 3, 1]
参数：hPz : P z != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `WeierstrassCurve.Jacobian.equiv_of_X_eq_of_Y_eq`：equiv_of_X_eq_of_Y_eq {
P Q : Fin 3 -> F} (hPz : P z != 0) (hQz : Q z != 0) (hx : P x * Q z ^ 2 = Q x * 
P z ^ 2) (hy : P y * Q z ^ 3 = Q y * …
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.LinearCombination.mul_const_eq`：mul_const_eq [Mul α] (p :
 b = c) (a : α) : a * b = a * c
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.tail_cons`：tail_cons (x : α) (u : Fin m -> α) : vecTail (vecCons 
x u) = u
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
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
（共 64 条，此处仅展示前 30 条）
-/
lemma equiv_some_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    P ≈ ![P x / P z ^ 2, P y / P z ^ 3, 1] :=
  equiv_of_X_eq_of_Y_eq hPz one_ne_zero
    (by linear_combination (norm := (matrix_simp; ring1)) -P x * div_self (pow_ne_zero 2 hPz))
    (by linear_combination (norm := (matrix_simp; ring1)) -P y * div_self (pow_ne_zero 3 hPz))
/-
**WeierstrassCurve.Jacobian.X_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve
.Jacobian`。
形式化陈述：X_eq_iff {P Q : Fin 3 -> F} (hPz : P z != 0) (hQz : Q z != 0) : P x * Q z 
^ 2 = Q x * P z ^ 2 ↔ P x / P z ^ 2 = Q x / Q z ^ 2
参数：hPz : P z != 0；hQz : Q z != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `div_eq_div_iff`：div_eq_div_iff (hb : b != 0) (hd : d != 0) : a / b = c /
 d ↔ a * d = c * b
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
-/
lemma X_eq_iff {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) :
    P x * Q z ^ 2 = Q x * P z ^ 2 ↔ P x / P z ^ 2 = Q x / Q z ^ 2 :=
  (div_eq_div_iff (pow_ne_zero 2 hPz) (pow_ne_zero 2 hQz)).symm
/-
**WeierstrassCurve.Jacobian.Y_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve
.Jacobian`。
形式化陈述：Y_eq_iff {P Q : Fin 3 -> F} (hPz : P z != 0) (hQz : Q z != 0) : P y * Q z 
^ 3 = Q y * P z ^ 3 ↔ P y / P z ^ 3 = Q y / Q z ^ 3
参数：hPz : P z != 0；hQz : Q z != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `div_eq_div_iff`：div_eq_div_iff (hb : b != 0) (hd : d != 0) : a / b = c /
 d ↔ a * d = c * b
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
-/
lemma Y_eq_iff {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) :
    P y * Q z ^ 3 = Q y * P z ^ 3 ↔ P y / P z ^ 3 = Q y / Q z ^ 3 :=
  (div_eq_div_iff (pow_ne_zero 3 hPz) (pow_ne_zero 3 hQz)).symm

/-! ## Weierstrass equations in Jacobian coordinates -/

variable (W') in
/-- The polynomial `W(X, Y, Z) := Y² + a₁XYZ + a₃YZ³ - (X³ + a₂X²Z² + a₄XZ⁴ + a₆Z⁶)` associated to a
Weierstrass curve `W` over a ring `R` in Jacobian coordinates.

This is represented as a term of type `MvPolynomial (Fin 3) R`, where `X`, `Y`, and `Z`
represent `X`, `Y`, and `Z` respectively. -/
/-
**WeierstrassCurve.Jacobian.polynomial** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCur
ve.Jacobian`。
形式化陈述：polynomial : MvPolynomial (Fin 3) R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The polynomial `W(X, Y, Z) := Y² + a₁XYZ + a₃YZ³ - (X³ + a₂X²Z² + a₄XZ⁴ + a₆Z⁶)`
 associated to a
Weierstrass curve `W` over a ring `R` in Jacobian coordinates.

This is represented as a term of type `MvPolynomial (Fin 3) R`, where `X`, `Y`, 
and `Z`
represent `X`, `Y`, and `Z` respectively.
-/
noncomputable def polynomial : MvPolynomial (Fin 3) R :=
  Y ^ 2 + C W'.a₁ * X * Y * Z + C W'.a₃ * Y * Z ^ 3
    - (X ^ 3 + C W'.a₂ * X ^ 2 * Z ^ 2 + C W'.a₄ * X * Z ^ 4 + C W'.a₆ * Z ^ 6)
/-
**WeierstrassCurve.Jacobian.eval_polynomial** 是 Mathlib 中的一个引理，位于命名空间 `Weierstra
ssCurve.Jacobian`。
形式化陈述：eval_polynomial (P : Fin 3 -> R) : eval P W'.polynomial = P y ^ 2 + W'.a₁ 
* P x * P y * P z + W'.a₃ * P y * P z ^ 3 - (P x ^ 3 + W'.a₂ * P x ^ 2 * P z ^ 2
 + W'.a₄ * P x * P z ^ 4 + W'.a₆ * P z ^ 6)
参数：P : Fin 3 -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.Jacobian.polynomial.eq_1`：∀ {R : Type r} [inst : CommRi
ng R] (W' : WeierstrassCurve.Jacobian R),   W'.polynomial =     MvPolynomial.X 1
 ^ 2 + MvPolynomial.C W'.a₁ * M…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MvPolynomial.eval_X`：eval_X : forall n, eval f (X n) = f n
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `MvPolynomial.eval_C`：eval_C : forall a, eval f (C a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eval_polynomial (P : Fin 3 → R) : eval P W'.polynomial =
    P y ^ 2 + W'.a₁ * P x * P y * P z + W'.a₃ * P y * P z ^ 3
      - (P x ^ 3 + W'.a₂ * P x ^ 2 * P z ^ 2 + W'.a₄ * P x * P z ^ 4 + W'.a₆ * P z ^ 6) := by
  rw [polynomial]
  simp
/-
**WeierstrassCurve.Jacobian.eval_polynomial_of_Z_ne_zero** 是 Mathlib 中的一个引理，位于命名
空间 `WeierstrassCurve.Jacobian`。
形式化陈述：eval_polynomial_of_Z_ne_zero {P : Fin 3 -> F} (hPz : P z != 0) : eval P W.
polynomial / P z ^ 6 = W.toAffine.polynomial.evalEval (P x / P z ^ 2) (P y / P z
 ^ 3)
参数：hPz : P z != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.LinearCombination.add_eq_eq`：add_eq_eq [Add α] (p₁ : (a₁ 
: α) = b₁) (p₂ : a₂ = b₂) : a₁ + a₂ = b₁ + b₂
· 使用定理 `Mathlib.Tactic.LinearCombination.mul_const_eq`：mul_const_eq [Mul α] (p :
 b = c) (a : α) : a * b = a * c
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.eval_polynomial`：eval_polynomial (P : Fin 3 ->
 R) : eval P W'.polynomial = P y ^ 2 + W'.a₁ * P x * P y * P z + W'.a₃ * P y * P
 z ^ 3 - (P x ^ 3 + W'.a₂ * P x…
· 使用引理 `WeierstrassCurve.Affine.evalEval_polynomial`：evalEval_polynomial (x y : 
R) : W.polynomial.evalEval x y = y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂
 * x ^ 2 + W.a₄ * x + W.a₆)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
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
（共 64 条，此处仅展示前 30 条）
-/
lemma eval_polynomial_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) : eval P W.polynomial / P z ^ 6 =
    W.toAffine.polynomial.evalEval (P x / P z ^ 2) (P y / P z ^ 3) := by
  linear_combination (norm := (rw [eval_polynomial, Affine.evalEval_polynomial]; ring1))
    W.a₁ * P x * P y / P z ^ 5 * div_self hPz + W.a₃ * P y / P z ^ 3 * div_self (pow_ne_zero 3 hPz)
      - W.a₂ * P x ^ 2 / P z ^ 4 * div_self (pow_ne_zero 2 hPz)
      - W.a₄ * P x / P z ^ 2 * div_self (pow_ne_zero 4 hPz) - W.a₆ * div_self (pow_ne_zero 6 hPz)

variable (W') in
/-- The proposition that a Jacobian point representative `(x, y, z)` lies in a Weierstrass curve
`W`.

In other words, it satisfies the `(2, 3, 1)`-homogeneous Weierstrass equation `W(X, Y, Z) = 0`. -/
/-
**WeierstrassCurve.Jacobian.Equation** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve
.Jacobian`。
形式化陈述：Equation (P : Fin 3 -> R) : Prop
参数：P : Fin 3 -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposition that a Jacobian point representative `(x, y, z)` lies in a Weier
strass curve
`W`.

In other words, it satisfies the `(2, 3, 1)`-homogeneous Weierstrass equation `W
(X, Y, Z) = 0`.
-/
def Equation (P : Fin 3 → R) : Prop :=
  eval P W'.polynomial = 0
/-
**WeierstrassCurve.Jacobian.equation_iff** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassC
urve.Jacobian`。
形式化陈述：equation_iff (P : Fin 3 -> R) : W'.Equation P ↔ P y ^ 2 + W'.a₁ * P x * P 
y * P z + W'.a₃ * P y * P z ^ 3 - (P x ^ 3 + W'.a₂ * P x ^ 2 * P z ^ 2 + W'.a₄ *
 P x * P z ^ 4 + W'.a₆ * P z ^ 6) = 0
参数：P : Fin 3 -> R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.Jacobian.Equation.eq_1`：∀ {R : Type r} [inst : CommRing
 R] (W' : WeierstrassCurve.Jacobian R) (P : Fin 3 → R),   W'.Equation P = ((MvPo
lynomial.eval P) W'.polynomia…
· 使用引理 `WeierstrassCurve.Jacobian.eval_polynomial`：eval_polynomial (P : Fin 3 ->
 R) : eval P W'.polynomial = P y ^ 2 + W'.a₁ * P x * P y * P z + W'.a₃ * P y * P
 z ^ 3 - (P x ^ 3 + W'.a₂ * P x…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma equation_iff (P : Fin 3 → R) : W'.Equation P ↔
    P y ^ 2 + W'.a₁ * P x * P y * P z + W'.a₃ * P y * P z ^ 3
      - (P x ^ 3 + W'.a₂ * P x ^ 2 * P z ^ 2 + W'.a₄ * P x * P z ^ 4 + W'.a₆ * P z ^ 6) = 0 := by
  rw [Equation, eval_polynomial]
/-
**WeierstrassCurve.Jacobian.equation_smul** 是 Mathlib 中的一个引理，位于命名空间 `Weierstrass
Curve.Jacobian`。
形式化陈述：equation_smul (P : Fin 3 -> R) {u : R} (hu : IsUnit u) : W'.Equation (u • 
P) ↔ W'.Equation P
参数：P : Fin 3 -> R；hu : IsUnit u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.equation_iff`：equation_iff (P : Fin 3 -> R) : 
W'.Equation P ↔ P y ^ 2 + W'.a₁ * P x * P y * P z + W'.a₃ * P y * P z ^ 3 - (P x
 ^ 3 + W'.a₂ * P x ^ 2 * P z…
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
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
（共 57 条，此处仅展示前 30 条）
-/
lemma equation_smul (P : Fin 3 → R) {u : R} (hu : IsUnit u) : W'.Equation (u • P) ↔ W'.Equation P :=
  have hP (u : R) {P : Fin 3 → R} (hP : W'.Equation P) : W'.Equation <| u • P := by
    rw [equation_iff] at hP ⊢
    linear_combination (norm := (simp only [smul_fin3_ext]; ring1)) u ^ 6 * hP
  ⟨fun h => by convert! hP (↑hu.unit⁻¹) h; rw [smul_smul, hu.val_inv_mul, one_smul], hP u⟩
/-
**WeierstrassCurve.Jacobian.equation_of_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Weierst
rassCurve.Jacobian`。
形式化陈述：equation_of_equiv {P Q : Fin 3 -> R} (h : P ≈ Q) : W'.Equation P ↔ W'.Equa
tion Q
参数：h : P ≈ Q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Jacobian.equation_smul`：equation_smul (P : Fin 3 -> R) 
{u : R} (hu : IsUnit u) : W'.Equation (u • P) ↔ W'.Equation P
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
lemma equation_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : W'.Equation P ↔ W'.Equation Q := by
  rcases h with ⟨u, rfl⟩
  exact equation_smul Q u.isUnit
/-
**WeierstrassCurve.Jacobian.equation_of_Z_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Wei
erstrassCurve.Jacobian`。
形式化陈述：equation_of_Z_eq_zero {P : Fin 3 -> R} (hPz : P z = 0) : W'.Equation P ↔ P
 y ^ 2 = P x ^ 3
参数：hPz : P z = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `OfNat.ofNat_ne_zero`：∀ {R : Type u_1} [inst : AddMonoidWithOne R] [CharZ
ero R] (n : ℕ) [inst_2 : n.AtLeastTwo], OfNat.ofNat n ≠ 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma equation_of_Z_eq_zero {P : Fin 3 → R} (hPz : P z = 0) :
    W'.Equation P ↔ P y ^ 2 = P x ^ 3 := by
  simp only [equation_iff, hPz, add_zero, mul_zero, zero_pow <| OfNat.ofNat_ne_zero _, sub_eq_zero]
/-
**WeierstrassCurve.Jacobian.equation_zero** 是 Mathlib 中的一个引理，位于命名空间 `Weierstrass
Curve.Jacobian`。
形式化陈述：equation_zero : W'.Equation ![1, 1, 0]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
lemma equation_zero : W'.Equation ![1, 1, 0] := by
  simp only [equation_of_Z_eq_zero, fin3_def_ext, one_pow]
/-
**WeierstrassCurve.Jacobian.equation_some** 是 Mathlib 中的一个引理，位于命名空间 `Weierstrass
Curve.Jacobian`。
形式化陈述：equation_some (a b : R) : W'.Equation ![a, b, 1] ↔ W'.toAffine.Equation a 
b
参数：a b : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma equation_some (a b : R) : W'.Equation ![a, b, 1] ↔ W'.toAffine.Equation a b := by
  simp only [equation_iff, Affine.equation_iff', fin3_def_ext, one_pow, mul_one]
/-
**WeierstrassCurve.Jacobian.equation_of_Z_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Wei
erstrassCurve.Jacobian`。
形式化陈述：equation_of_Z_ne_zero {P : Fin 3 -> F} (hPz : P z != 0) : W.Equation P ↔ W
.toAffine.Equation (P x / P z ^ 2) (P y / P z ^ 3)
参数：hPz : P z != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `WeierstrassCurve.Jacobian.equation_of_equiv`：equation_of_equiv {P Q : Fi
n 3 -> R} (h : P ≈ Q) : W'.Equation P ↔ W'.Equation Q
· 使用引理 `WeierstrassCurve.Jacobian.equiv_some_of_Z_ne_zero`：equiv_some_of_Z_ne_ze
ro {P : Fin 3 -> F} (hPz : P z != 0) : P ≈ ![P x / P z ^ 2, P y / P z ^ 3, 1]
· 使用引理 `WeierstrassCurve.Jacobian.equation_some`：equation_some (a b : R) : W'.Eq
uation ![a, b, 1] ↔ W'.toAffine.Equation a b
-/
lemma equation_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.Equation P ↔ W.toAffine.Equation (P x / P z ^ 2) (P y / P z ^ 3) :=
  (equation_of_equiv <| equiv_some_of_Z_ne_zero hPz).trans <| equation_some ..

/-! ## The nonsingular condition in Jacobian coordinates -/

variable (W') in
/-- The partial derivative `W_X(X, Y, Z)` with respect to `X` of the polynomial `W(X, Y, Z)`
associated to a Weierstrass curve `W` in Jacobian coordinates. -/
/-
**WeierstrassCurve.Jacobian.polynomialX** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCu
rve.Jacobian`。
形式化陈述：polynomialX : MvPolynomial (Fin 3) R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The partial derivative `W_X(X, Y, Z)` with respect to `X` of the polynomial `W(X
, Y, Z)`
associated to a Weierstrass curve `W` in Jacobian coordinates.
-/
noncomputable def polynomialX : MvPolynomial (Fin 3) R :=
  pderiv x W'.polynomial
/-
**WeierstrassCurve.Jacobian.polynomialX_eq** 是 Mathlib 中的一个引理，位于命名空间 `Weierstras
sCurve.Jacobian`。
形式化陈述：polynomialX_eq : W'.polynomialX = C W'.a₁ * Y * Z - (C 3 * X ^ 2 + C (2 * 
W'.a₂) * X * Z ^ 2 + C W'.a₄ * Z ^ 4)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.Jacobian.polynomialX.eq_1`：∀ {R : Type r} [inst : CommR
ing R] (W' : WeierstrassCurve.Jacobian R),   W'.polynomialX = (MvPolynomial.pder
iv 0) W'.polynomial
· 使用定理 `WeierstrassCurve.Jacobian.polynomial.eq_1`：∀ {R : Type r} [inst : CommRi
ng R] (W' : WeierstrassCurve.Jacobian R),   W'.polynomial =     MvPolynomial.X 1
 ^ 2 + MvPolynomial.C W'.a₁ * M…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `Derivation.instAddMonoidHomClass`：∀ {R : Type u_1} {A : Type u_2} {M : T
ype u_4} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddCommMo
noid M] [inst_3 : Alge…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `MvPolynomial.pderiv_pow`：pderiv_pow {i : σ} {f : MvPolynomial σ R} {n : 
Nat} : pderiv i (f ^ n) = n * f ^ (n - 1) * pderiv i f
· 使用定理 `MvPolynomial.pderiv_X_of_ne`：pderiv_X_of_ne {i j : σ} (h : j != i) : pde
riv i (X j : MvPolynomial σ R) = 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `MvPolynomial.pderiv_mul`：pderiv_mul {i : σ} {f g : MvPolynomial σ R} : p
deriv i (f * g) = pderiv i f * g + f * pderiv i g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.pderiv_C`：pderiv_C {i : σ} : pderiv i (C a) = 0
· 使用定理 `MvPolynomial.pderiv_X_self`：pderiv_X_self (i : σ) : pderiv i (X i : MvPo
lynomial σ R) = 1
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
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
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_natCast`：isNat_natCast {R} [AddMonoidWithOne 
R] (n m : Nat) : IsNat n m -> IsNat (n : R) m
（共 65 条，此处仅展示前 30 条）
-/
lemma polynomialX_eq : W'.polynomialX =
    C W'.a₁ * Y * Z - (C 3 * X ^ 2 + C (2 * W'.a₂) * X * Z ^ 2 + C W'.a₄ * Z ^ 4) := by
  rw [polynomialX, polynomial]
  pderiv_simp
  ring1
/-
**WeierstrassCurve.Jacobian.eval_polynomialX** 是 Mathlib 中的一个引理，位于命名空间 `Weierstr
assCurve.Jacobian`。
形式化陈述：eval_polynomialX (P : Fin 3 -> R) : eval P W'.polynomialX = W'.a₁ * P y * 
P z - (3 * P x ^ 2 + 2 * W'.a₂ * P x * P z ^ 2 + W'.a₄ * P z ^ 4)
参数：P : Fin 3 -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.polynomialX_eq`：polynomialX_eq : W'.polynomial
X = C W'.a₁ * Y * Z - (C 3 * X ^ 2 + C (2 * W'.a₂) * X * Z ^ 2 + C W'.a₄ * Z ^ 4
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.C_mul`：C_mul : (C (a * a') : MvPolynomial σ R) = C a * C a'
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
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
· 使用定理 `MvPolynomial.eval_C`：eval_C : forall a, eval f (C a) = a
· 使用定理 `MvPolynomial.eval_X`：eval_X : forall n, eval f (X n) = f n
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
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
lemma eval_polynomialX (P : Fin 3 → R) : eval P W'.polynomialX =
    W'.a₁ * P y * P z - (3 * P x ^ 2 + 2 * W'.a₂ * P x * P z ^ 2 + W'.a₄ * P z ^ 4) := by
  rw [polynomialX_eq]
  simp
/-
**WeierstrassCurve.Jacobian.eval_polynomialX_of_Z_ne_zero** 是 Mathlib 中的一个引理，位于命
名空间 `WeierstrassCurve.Jacobian`。
形式化陈述：eval_polynomialX_of_Z_ne_zero {P : Fin 3 -> F} (hPz : P z != 0) : eval P W
.polynomialX / P z ^ 4 = W.toAffine.polynomialX.evalEval (P x / P z ^ 2) (P y / 
P z ^ 3)
参数：hPz : P z != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.LinearCombination.add_eq_eq`：add_eq_eq [Add α] (p₁ : (a₁ 
: α) = b₁) (p₂ : a₂ = b₂) : a₁ + a₂ = b₁ + b₂
· 使用定理 `Mathlib.Tactic.LinearCombination.mul_const_eq`：mul_const_eq [Mul α] (p :
 b = c) (a : α) : a * b = a * c
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.eval_polynomialX`：eval_polynomialX (P : Fin 3 
-> R) : eval P W'.polynomialX = W'.a₁ * P y * P z - (3 * P x ^ 2 + 2 * W'.a₂ * P
 x * P z ^ 2 + W'.a₄ * P z ^ 4)
· 使用引理 `WeierstrassCurve.Affine.evalEval_polynomialX`：evalEval_polynomialX (x y 
: R) : W.polynomialX.evalEval x y = W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
（共 66 条，此处仅展示前 30 条）
-/
lemma eval_polynomialX_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    eval P W.polynomialX / P z ^ 4 =
      W.toAffine.polynomialX.evalEval (P x / P z ^ 2) (P y / P z ^ 3) := by
  linear_combination (norm := (rw [eval_polynomialX, Affine.evalEval_polynomialX]; ring1))
    W.a₁ * P y / P z ^ 3 * div_self hPz - 2 * W.a₂ * P x / P z ^ 2 * div_self (pow_ne_zero 2 hPz)
      - W.a₄ * div_self (pow_ne_zero 4 hPz)

variable (W') in
/-- The partial derivative `W_Y(X, Y, Z)` with respect to `Y` of the polynomial `W(X, Y, Z)`
associated to a Weierstrass curve `W` in Jacobian coordinates. -/
/-
**WeierstrassCurve.Jacobian.polynomialY** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCu
rve.Jacobian`。
形式化陈述：polynomialY : MvPolynomial (Fin 3) R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The partial derivative `W_Y(X, Y, Z)` with respect to `Y` of the polynomial `W(X
, Y, Z)`
associated to a Weierstrass curve `W` in Jacobian coordinates.
-/
noncomputable def polynomialY : MvPolynomial (Fin 3) R :=
  pderiv y W'.polynomial
/-
**WeierstrassCurve.Jacobian.polynomialY_eq** 是 Mathlib 中的一个引理，位于命名空间 `Weierstras
sCurve.Jacobian`。
形式化陈述：polynomialY_eq : W'.polynomialY = C 2 * Y + C W'.a₁ * X * Z + C W'.a₃ * Z 
^ 3
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.Jacobian.polynomialY.eq_1`：∀ {R : Type r} [inst : CommR
ing R] (W' : WeierstrassCurve.Jacobian R),   W'.polynomialY = (MvPolynomial.pder
iv 1) W'.polynomial
· 使用定理 `WeierstrassCurve.Jacobian.polynomial.eq_1`：∀ {R : Type r} [inst : CommRi
ng R] (W' : WeierstrassCurve.Jacobian R),   W'.polynomial =     MvPolynomial.X 1
 ^ 2 + MvPolynomial.C W'.a₁ * M…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `Derivation.instAddMonoidHomClass`：∀ {R : Type u_1} {A : Type u_2} {M : T
ype u_4} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddCommMo
noid M] [inst_3 : Alge…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `MvPolynomial.pderiv_pow`：pderiv_pow {i : σ} {f : MvPolynomial σ R} {n : 
Nat} : pderiv i (f ^ n) = n * f ^ (n - 1) * pderiv i f
· 使用定理 `MvPolynomial.pderiv_X_self`：pderiv_X_self (i : σ) : pderiv i (X i : MvPo
lynomial σ R) = 1
· 使用定理 `MvPolynomial.pderiv_mul`：pderiv_mul {i : σ} {f g : MvPolynomial σ R} : p
deriv i (f * g) = pderiv i f * g + f * pderiv i g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.pderiv_C`：pderiv_C {i : σ} : pderiv i (C a) = 0
· 使用定理 `MvPolynomial.pderiv_X_of_ne`：pderiv_X_of_ne {i j : σ} (h : j != i) : pde
riv i (X j : MvPolynomial σ R) = 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `map_ofNat`：map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : N
at) [Nat.AtLeastTwo n] : (f ofNat(n) : S) = OfNat.ofNat n
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_natCast`：isNat_natCast {R} [AddMonoidWithOne 
R] (n m : Nat) : IsNat n m -> IsNat (n : R) m
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
（共 57 条，此处仅展示前 30 条）
-/
lemma polynomialY_eq : W'.polynomialY = C 2 * Y + C W'.a₁ * X * Z + C W'.a₃ * Z ^ 3 := by
  rw [polynomialY, polynomial]
  pderiv_simp
  ring1
/-
**WeierstrassCurve.Jacobian.eval_polynomialY** 是 Mathlib 中的一个引理，位于命名空间 `Weierstr
assCurve.Jacobian`。
形式化陈述：eval_polynomialY (P : Fin 3 -> R) : eval P W'.polynomialY = 2 * P y + W'.a
₁ * P x * P z + W'.a₃ * P z ^ 3
参数：P : Fin 3 -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.polynomialY_eq`：polynomialY_eq : W'.polynomial
Y = C 2 * Y + C W'.a₁ * X * Z + C W'.a₃ * Z ^ 3
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
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
· 使用定理 `MvPolynomial.eval_C`：eval_C : forall a, eval f (C a) = a
· 使用定理 `MvPolynomial.eval_X`：eval_X : forall n, eval f (X n) = f n
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
lemma eval_polynomialY (P : Fin 3 → R) :
    eval P W'.polynomialY = 2 * P y + W'.a₁ * P x * P z + W'.a₃ * P z ^ 3 := by
  rw [polynomialY_eq]
  simp
/-
**WeierstrassCurve.Jacobian.eval_polynomialY_of_Z_ne_zero** 是 Mathlib 中的一个引理，位于命
名空间 `WeierstrassCurve.Jacobian`。
形式化陈述：eval_polynomialY_of_Z_ne_zero {P : Fin 3 -> F} (hPz : P z != 0) : eval P W
.polynomialY / P z ^ 3 = W.toAffine.polynomialY.evalEval (P x / P z ^ 2) (P y / 
P z ^ 3)
参数：hPz : P z != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.LinearCombination.add_eq_eq`：add_eq_eq [Add α] (p₁ : (a₁ 
: α) = b₁) (p₂ : a₂ = b₂) : a₁ + a₂ = b₁ + b₂
· 使用定理 `Mathlib.Tactic.LinearCombination.mul_const_eq`：mul_const_eq [Mul α] (p :
 b = c) (a : α) : a * b = a * c
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.eval_polynomialY`：eval_polynomialY (P : Fin 3 
-> R) : eval P W'.polynomialY = 2 * P y + W'.a₁ * P x * P z + W'.a₃ * P z ^ 3
· 使用引理 `WeierstrassCurve.Affine.evalEval_polynomialY`：evalEval_polynomialY (x y 
: R) : W.polynomialY.evalEval x y = 2 * y + W.a₁ * x + W.a₃
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
（共 65 条，此处仅展示前 30 条）
-/
lemma eval_polynomialY_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    eval P W.polynomialY / P z ^ 3 =
      W.toAffine.polynomialY.evalEval (P x / P z ^ 2) (P y / P z ^ 3) := by
  linear_combination (norm := (rw [eval_polynomialY, Affine.evalEval_polynomialY]; ring1))
    W.a₁ * P x / P z ^ 2 * div_self hPz + W.a₃ * div_self (pow_ne_zero 3 hPz)

variable (W') in
/-- The partial derivative `W_Z(X, Y, Z)` with respect to `Z` of the polynomial `W(X, Y, Z)`
associated to a Weierstrass curve `W` in Jacobian coordinates. -/
/-
**WeierstrassCurve.Jacobian.polynomialZ** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCu
rve.Jacobian`。
形式化陈述：polynomialZ : MvPolynomial (Fin 3) R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The partial derivative `W_Z(X, Y, Z)` with respect to `Z` of the polynomial `W(X
, Y, Z)`
associated to a Weierstrass curve `W` in Jacobian coordinates.
-/
noncomputable def polynomialZ : MvPolynomial (Fin 3) R :=
  pderiv z W'.polynomial
/-
**WeierstrassCurve.Jacobian.polynomialZ_eq** 是 Mathlib 中的一个引理，位于命名空间 `Weierstras
sCurve.Jacobian`。
形式化陈述：polynomialZ_eq : W'.polynomialZ = C W'.a₁ * X * Y + C (3 * W'.a₃) * Y * Z 
^ 2 - (C (2 * W'.a₂) * X ^ 2 * Z + C (4 * W'.a₄) * X * Z ^ 3 + C (6 * W'.a₆) * Z
 ^ 5)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.Jacobian.polynomialZ.eq_1`：∀ {R : Type r} [inst : CommR
ing R] (W' : WeierstrassCurve.Jacobian R),   W'.polynomialZ = (MvPolynomial.pder
iv 2) W'.polynomial
· 使用定理 `WeierstrassCurve.Jacobian.polynomial.eq_1`：∀ {R : Type r} [inst : CommRi
ng R] (W' : WeierstrassCurve.Jacobian R),   W'.polynomial =     MvPolynomial.X 1
 ^ 2 + MvPolynomial.C W'.a₁ * M…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `Derivation.instAddMonoidHomClass`：∀ {R : Type u_1} {A : Type u_2} {M : T
ype u_4} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddCommMo
noid M] [inst_3 : Alge…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `MvPolynomial.pderiv_pow`：pderiv_pow {i : σ} {f : MvPolynomial σ R} {n : 
Nat} : pderiv i (f ^ n) = n * f ^ (n - 1) * pderiv i f
· 使用定理 `MvPolynomial.pderiv_X_of_ne`：pderiv_X_of_ne {i j : σ} (h : j != i) : pde
riv i (X j : MvPolynomial σ R) = 0
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `MvPolynomial.pderiv_mul`：pderiv_mul {i : σ} {f g : MvPolynomial σ R} : p
deriv i (f * g) = pderiv i f * g + f * pderiv i g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.pderiv_C`：pderiv_C {i : σ} : pderiv i (C a) = 0
· 使用定理 `MvPolynomial.pderiv_X_self`：pderiv_X_self (i : σ) : pderiv i (X i : MvPo
lynomial σ R) = 1
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_ofNat`：map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : N
at) [Nat.AtLeastTwo n] : (f ofNat(n) : S) = OfNat.ofNat n
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_natCast`：isNat_natCast {R} [AddMonoidWithOne 
R] (n m : Nat) : IsNat n m -> IsNat (n : R) m
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
（共 63 条，此处仅展示前 30 条）
-/
lemma polynomialZ_eq : W'.polynomialZ = C W'.a₁ * X * Y + C (3 * W'.a₃) * Y * Z ^ 2 -
    (C (2 * W'.a₂) * X ^ 2 * Z + C (4 * W'.a₄) * X * Z ^ 3 + C (6 * W'.a₆) * Z ^ 5) := by
  rw [polynomialZ, polynomial]
  pderiv_simp
  ring1
/-
**WeierstrassCurve.Jacobian.eval_polynomialZ** 是 Mathlib 中的一个引理，位于命名空间 `Weierstr
assCurve.Jacobian`。
形式化陈述：eval_polynomialZ (P : Fin 3 -> R) : eval P W'.polynomialZ = W'.a₁ * P x * 
P y + 3 * W'.a₃ * P y * P z ^ 2 - (2 * W'.a₂ * P x ^ 2 * P z + 4 * W'.a₄ * P x *
 P z ^ 3 + 6 * W'.a₆ * P z ^ 5)
参数：P : Fin 3 -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.polynomialZ_eq`：polynomialZ_eq : W'.polynomial
Z = C W'.a₁ * X * Y + C (3 * W'.a₃) * Y * Z ^ 2 - (C (2 * W'.a₂) * X ^ 2 * Z + C
 (4 * W'.a₄) * X * Z ^ 3 + C (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPolynomial.C_mul`：C_mul : (C (a * a') : MvPolynomial σ R) = C a * C a'
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `MvPolynomial.eval_C`：eval_C : forall a, eval f (C a) = a
· 使用定理 `MvPolynomial.eval_X`：eval_X : forall n, eval f (X n) = f n
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
lemma eval_polynomialZ (P : Fin 3 → R) : eval P W'.polynomialZ =
    W'.a₁ * P x * P y + 3 * W'.a₃ * P y * P z ^ 2 -
      (2 * W'.a₂ * P x ^ 2 * P z + 4 * W'.a₄ * P x * P z ^ 3 + 6 * W'.a₆ * P z ^ 5) := by
  rw [polynomialZ_eq]
  simp

/-- Euler's homogeneous function theorem in Jacobian coordinates. -/
/-
**WeierstrassCurve.Jacobian.polynomial_relation** 是 Mathlib 中的一个定理，位于命名空间 `Weier
strassCurve.Jacobian`。
形式化陈述：polynomial_relation (P : Fin 3 -> R) : 6 * eval P W'.polynomial = 2 * P x 
* eval P W'.polynomialX + 3 * P y * eval P W'.polynomialY + P z * eval P W'.poly
nomialZ
参数：P : Fin 3 -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.eval_polynomial`：eval_polynomial (P : Fin 3 ->
 R) : eval P W'.polynomial = P y ^ 2 + W'.a₁ * P x * P y * P z + W'.a₃ * P y * P
 z ^ 3 - (P x ^ 3 + W'.a₂ * P x…
· 使用引理 `WeierstrassCurve.Jacobian.eval_polynomialX`：eval_polynomialX (P : Fin 3 
-> R) : eval P W'.polynomialX = W'.a₁ * P y * P z - (3 * P x ^ 2 + 2 * W'.a₂ * P
 x * P z ^ 2 + W'.a₄ * P z ^ 4)
· 使用引理 `WeierstrassCurve.Jacobian.eval_polynomialY`：eval_polynomialY (P : Fin 3 
-> R) : eval P W'.polynomialY = 2 * P y + W'.a₁ * P x * P z + W'.a₃ * P z ^ 3
· 使用引理 `WeierstrassCurve.Jacobian.eval_polynomialZ`：eval_polynomialZ (P : Fin 3 
-> R) : eval P W'.polynomialZ = W'.a₁ * P x * P y + 3 * W'.a₃ * P y * P z ^ 2 - 
(2 * W'.a₂ * P x ^ 2 * P z + 4 *…
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
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
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
Euler's homogeneous function theorem in Jacobian coordinates.
-/
theorem polynomial_relation (P : Fin 3 → R) : 6 * eval P W'.polynomial =
    2 * P x * eval P W'.polynomialX + 3 * P y * eval P W'.polynomialY +
      P z * eval P W'.polynomialZ := by
  rw [eval_polynomial, eval_polynomialX, eval_polynomialY, eval_polynomialZ]
  ring1

variable (W') in
/-- The proposition that a Jacobian point representative `(x, y, z)` on a Weierstrass curve `W` is
nonsingular.

In other words, either `W_X(x, y, z) ≠ 0`, `W_Y(x, y, z) ≠ 0`, or `W_Z(x, y, z) ≠ 0`.

Note that this definition is only mathematically accurate for fields. -/
-- TODO: generalise this definition to be mathematically accurate for a larger class of rings.
/-
**WeierstrassCurve.Jacobian.Nonsingular** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCu
rve.Jacobian`。
形式化陈述：Nonsingular (P : Fin 3 -> R) : Prop
参数：P : Fin 3 -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Nonsingular (P : Fin 3 → R) : Prop :=
  W'.Equation P ∧
    (eval P W'.polynomialX ≠ 0 ∨ eval P W'.polynomialY ≠ 0 ∨ eval P W'.polynomialZ ≠ 0)
/-
**WeierstrassCurve.Jacobian.nonsingular_iff** 是 Mathlib 中的一个引理，位于命名空间 `Weierstra
ssCurve.Jacobian`。
形式化陈述：nonsingular_iff (P : Fin 3 -> R) : W'.Nonsingular P ↔ W'.Equation P ∧ (W'.
a₁ * P y * P z - (3 * P x ^ 2 + 2 * W'.a₂ * P x * P z ^ 2 + W'.a₄ * P z ^ 4) != 
0 ∨ 2 * P y + W'.a₁ * P x * P z + W'.a₃ * P z ^ 3 != 0 ∨ W'.a₁ * P x * P y + 3 *
 W'.a₃ * P y * P z ^ 2 - (2 * W'.a₂ * P x ^ 2 * P z + 4 * W'.a₄ * P x * P z ^ 3 
+ 6 * W'.a₆ * P z ^ 5) != 0)
参数：P : Fin 3 -> R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.Jacobian.Nonsingular.eq_1`：∀ {R : Type r} [inst : CommR
ing R] (W' : WeierstrassCurve.Jacobian R) (P : Fin 3 → R),   W'.Nonsingular P = 
    (W'.Equation P ∧       ((MvP…
· 使用引理 `WeierstrassCurve.Jacobian.eval_polynomialX`：eval_polynomialX (P : Fin 3 
-> R) : eval P W'.polynomialX = W'.a₁ * P y * P z - (3 * P x ^ 2 + 2 * W'.a₂ * P
 x * P z ^ 2 + W'.a₄ * P z ^ 4)
· 使用引理 `WeierstrassCurve.Jacobian.eval_polynomialY`：eval_polynomialY (P : Fin 3 
-> R) : eval P W'.polynomialY = 2 * P y + W'.a₁ * P x * P z + W'.a₃ * P z ^ 3
· 使用引理 `WeierstrassCurve.Jacobian.eval_polynomialZ`：eval_polynomialZ (P : Fin 3 
-> R) : eval P W'.polynomialZ = W'.a₁ * P x * P y + 3 * W'.a₃ * P y * P z ^ 2 - 
(2 * W'.a₂ * P x ^ 2 * P z + 4 *…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma nonsingular_iff (P : Fin 3 → R) : W'.Nonsingular P ↔ W'.Equation P ∧
    (W'.a₁ * P y * P z - (3 * P x ^ 2 + 2 * W'.a₂ * P x * P z ^ 2 + W'.a₄ * P z ^ 4) ≠ 0 ∨
      2 * P y + W'.a₁ * P x * P z + W'.a₃ * P z ^ 3 ≠ 0 ∨
      W'.a₁ * P x * P y + 3 * W'.a₃ * P y * P z ^ 2
        - (2 * W'.a₂ * P x ^ 2 * P z + 4 * W'.a₄ * P x * P z ^ 3 + 6 * W'.a₆ * P z ^ 5) ≠ 0) := by
  rw [Nonsingular, eval_polynomialX, eval_polynomialY, eval_polynomialZ]
/-
**WeierstrassCurve.Jacobian.nonsingular_smul** 是 Mathlib 中的一个引理，位于命名空间 `Weierstr
assCurve.Jacobian`。
形式化陈述：nonsingular_smul (P : Fin 3 -> R) {u : R} (hu : IsUnit u) : W'.Nonsingular
 (u • P) ↔ W'.Nonsingular P
参数：P : Fin 3 -> R；hu : IsUnit u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WeierstrassCurve.Jacobian.nonsingular_iff`：nonsingular_iff (P : Fin 3 ->
 R) : W'.Nonsingular P ↔ W'.Equation P ∧ (W'.a₁ * P y * P z - (3 * P x ^ 2 + 2 *
 W'.a₂ * P x * P z ^ 2 + W'.a₄ …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WeierstrassCurve.Jacobian.equation_smul`：equation_smul (P : Fin 3 -> R) 
{u : R} (hu : IsUnit u) : W'.Equation (u • P) ↔ W'.Equation P
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.LinearCombination.mul_const_eq`：mul_const_eq [Mul α] (p :
 b = c) (a : α) : a * b = a * c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
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
（共 67 条，此处仅展示前 30 条）
-/
lemma nonsingular_smul (P : Fin 3 → R) {u : R} (hu : IsUnit u) :
    W'.Nonsingular (u • P) ↔ W'.Nonsingular P :=
  have hP {u : R} (hu : IsUnit u) {P : Fin 3 → R} (hP : W'.Nonsingular <| u • P) :
      W'.Nonsingular P := by
    rcases (nonsingular_iff _).mp hP with ⟨hP, hP'⟩
    refine (nonsingular_iff P).mpr ⟨(equation_smul P hu).mp hP, ?_⟩
    contrapose! hP'
    simp only [smul_fin3_ext]
    exact ⟨by linear_combination (norm := ring1) u ^ 4 * hP'.left,
      by linear_combination (norm := ring1) u ^ 3 * hP'.right.left,
      by linear_combination (norm := ring1) u ^ 5 * hP'.right.right⟩
  ⟨hP hu, fun h => hP hu.unit⁻¹.isUnit <| by rwa [smul_smul, hu.val_inv_mul, one_smul]⟩
/-
**WeierstrassCurve.Jacobian.nonsingular_of_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Weie
rstrassCurve.Jacobian`。
形式化陈述：nonsingular_of_equiv {P Q : Fin 3 -> R} (h : P ≈ Q) : W'.Nonsingular P ↔ W
'.Nonsingular Q
参数：h : P ≈ Q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Jacobian.nonsingular_smul`：nonsingular_smul (P : Fin 3 
-> R) {u : R} (hu : IsUnit u) : W'.Nonsingular (u • P) ↔ W'.Nonsingular P
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
lemma nonsingular_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : W'.Nonsingular P ↔ W'.Nonsingular Q := by
  rcases h with ⟨u, rfl⟩
  exact nonsingular_smul Q u.isUnit
/-
**WeierstrassCurve.Jacobian.nonsingular_of_Z_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `
WeierstrassCurve.Jacobian`。
形式化陈述：nonsingular_of_Z_eq_zero {P : Fin 3 -> R} (hPz : P z = 0) : W'.Nonsingular
 P ↔ W'.Equation P ∧ (3 * P x ^ 2 != 0 ∨ 2 * P y != 0 ∨ W'.a₁ * P x * P y != 0)
参数：hPz : P z = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `OfNat.ofNat_ne_zero`：∀ {R : Type u_1} [inst : AddMonoidWithOne R] [CharZ
ero R] (n : ℕ) [inst_2 : n.AtLeastTwo], OfNat.ofNat n ≠ 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma nonsingular_of_Z_eq_zero {P : Fin 3 → R} (hPz : P z = 0) :
    W'.Nonsingular P ↔ W'.Equation P ∧ (3 * P x ^ 2 ≠ 0 ∨ 2 * P y ≠ 0 ∨ W'.a₁ * P x * P y ≠ 0) := by
  simp only [nonsingular_iff, hPz, add_zero, sub_zero, zero_sub, mul_zero,
    zero_pow <| OfNat.ofNat_ne_zero _, neg_ne_zero]
/-
**WeierstrassCurve.Jacobian.nonsingular_zero** 是 Mathlib 中的一个引理，位于命名空间 `Weierstr
assCurve.Jacobian`。
形式化陈述：nonsingular_zero [Nontrivial R] : W'.Nonsingular ![1, 1, 0]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.LinearCombination.add_eq_eq`：add_eq_eq [Add α] (p₁ : (a₁ 
: α) = b₁) (p₂ : a₂ = b₂) : a₁ + a₂ = b₁ + b₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
（共 53 条，此处仅展示前 30 条）
-/
lemma nonsingular_zero [Nontrivial R] : W'.Nonsingular ![1, 1, 0] := by
  simp only [nonsingular_of_Z_eq_zero, equation_zero, true_and, fin3_def_ext, ← not_and_or]
  exact fun h => one_ne_zero <| by linear_combination (norm := ring1) h.1 - h.2.1
/-
**WeierstrassCurve.Jacobian.nonsingular_some** 是 Mathlib 中的一个引理，位于命名空间 `Weierstr
assCurve.Jacobian`。
形式化陈述：nonsingular_some (a b : R) : W'.Nonsingular ![a, b, 1] ↔ W'.toAffine.Nonsi
ngular a b
参数：a b : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.LinearCombination.add_eq_eq`：add_eq_eq [Add α] (p₁ : (a₁ 
: α) = b₁) (p₂ : a₂ = b₂) : a₁ + a₂ = b₁ + b₂
· 使用定理 `Mathlib.Tactic.LinearCombination.mul_const_eq`：mul_const_eq [Mul α] (p :
 b = c) (a : α) : a * b = a * c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
（共 61 条，此处仅展示前 30 条）
-/
lemma nonsingular_some (a b : R) : W'.Nonsingular ![a, b, 1] ↔ W'.toAffine.Nonsingular a b := by
  simp_rw [nonsingular_iff, equation_some, fin3_def_ext, Affine.nonsingular_iff',
    Affine.equation_iff', and_congr_right_iff, ← not_and_or, not_iff_not, one_pow, mul_one,
    and_congr_right_iff, Iff.comm, iff_self_and]
  intro h ha hb
  linear_combination (norm := ring1) 6 * h - 2 * a * ha - 3 * b * hb
/-
**WeierstrassCurve.Jacobian.nonsingular_of_Z_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `
WeierstrassCurve.Jacobian`。
形式化陈述：nonsingular_of_Z_ne_zero {P : Fin 3 -> F} (hPz : P z != 0) : W.Nonsingular
 P ↔ W.toAffine.Nonsingular (P x / P z ^ 2) (P y / P z ^ 3)
参数：hPz : P z != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `WeierstrassCurve.Jacobian.nonsingular_of_equiv`：nonsingular_of_equiv {P 
Q : Fin 3 -> R} (h : P ≈ Q) : W'.Nonsingular P ↔ W'.Nonsingular Q
· 使用引理 `WeierstrassCurve.Jacobian.equiv_some_of_Z_ne_zero`：equiv_some_of_Z_ne_ze
ro {P : Fin 3 -> F} (hPz : P z != 0) : P ≈ ![P x / P z ^ 2, P y / P z ^ 3, 1]
· 使用引理 `WeierstrassCurve.Jacobian.nonsingular_some`：nonsingular_some (a b : R) :
 W'.Nonsingular ![a, b, 1] ↔ W'.toAffine.Nonsingular a b
-/
lemma nonsingular_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.Nonsingular P ↔ W.toAffine.Nonsingular (P x / P z ^ 2) (P y / P z ^ 3) :=
  (nonsingular_of_equiv <| equiv_some_of_Z_ne_zero hPz).trans <| nonsingular_some ..
/-
**WeierstrassCurve.Jacobian.nonsingular_iff_of_Z_ne_zero** 是 Mathlib 中的一个引理，位于命名
空间 `WeierstrassCurve.Jacobian`。
形式化陈述：nonsingular_iff_of_Z_ne_zero {P : Fin 3 -> F} (hPz : P z != 0) : W.Nonsing
ular P ↔ W.Equation P ∧ (eval P W.polynomialX != 0 ∨ eval P W.polynomialY != 0)
参数：hPz : P z != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.nonsingular_of_Z_ne_zero`：nonsingular_of_Z_ne_
zero {P : Fin 3 -> F} (hPz : P z != 0) : W.Nonsingular P ↔ W.toAffine.Nonsingula
r (P x / P z ^ 2) (P y / P z ^ 3)
· 使用定理 `WeierstrassCurve.Affine.Nonsingular.eq_1`：∀ {R : Type r} [inst : CommRin
g R] (W : WeierstrassCurve.Affine R) (x y : R),   W.Nonsingular x y =     (W.Equ
ation x y ∧ (Polynomial.evalEv…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WeierstrassCurve.Jacobian.equation_of_Z_ne_zero`：equation_of_Z_ne_zero {
P : Fin 3 -> F} (hPz : P z != 0) : W.Equation P ↔ W.toAffine.Equation (P x / P z
 ^ 2) (P y / P z ^ 3)
· 使用引理 `WeierstrassCurve.Jacobian.eval_polynomialX_of_Z_ne_zero`：eval_polynomial
X_of_Z_ne_zero {P : Fin 3 -> F} (hPz : P z != 0) : eval P W.polynomialX / P z ^ 
4 = W.toAffine.polynomialX.evalEval (P x / P …
· 使用定理 `div_ne_zero_iff`：div_ne_zero_iff : a / b != 0 ↔ a != 0 ∧ b != 0
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `WeierstrassCurve.Jacobian.eval_polynomialY_of_Z_ne_zero`：eval_polynomial
Y_of_Z_ne_zero {P : Fin 3 -> F} (hPz : P z != 0) : eval P W.polynomialY / P z ^ 
3 = W.toAffine.polynomialY.evalEval (P x / P …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma nonsingular_iff_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.Nonsingular P ↔ W.Equation P ∧ (eval P W.polynomialX ≠ 0 ∨ eval P W.polynomialY ≠ 0) := by
  rw [nonsingular_of_Z_ne_zero hPz, Affine.Nonsingular, ← equation_of_Z_ne_zero hPz,
    ← eval_polynomialX_of_Z_ne_zero hPz, div_ne_zero_iff, and_iff_left <| pow_ne_zero 4 hPz,
    ← eval_polynomialY_of_Z_ne_zero hPz, div_ne_zero_iff, and_iff_left <| pow_ne_zero 3 hPz]
/-
**WeierstrassCurve.Jacobian.X_ne_zero_of_Z_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `We
ierstrassCurve.Jacobian`。
形式化陈述：X_ne_zero_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 -> R} (hP : W'.Nonsin
gular P) (hPz : P z = 0) : P x != 0
参数：hP : W'.Nonsingular P；hPz : P z = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_self_iff_false`：∀ {α : Sort u_1} (a : α), a ≠ a ↔ False
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `pow_eq_zero_iff`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀} {
n : ℕ} [IsReduced M₀], n ≠ 0 → (a ^ n = 0 ↔ a = 0)
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `WeierstrassCurve.Jacobian.nonsingular_of_Z_eq_zero`：nonsingular_of_Z_eq_
zero {P : Fin 3 -> R} (hPz : P z = 0) : W'.Nonsingular P ↔ W'.Equation P ∧ (3 * 
P x ^ 2 != 0 ∨ 2 * P y != 0 ∨ W'.a₁ * P …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `WeierstrassCurve.Jacobian.equation_of_Z_eq_zero`：equation_of_Z_eq_zero {
P : Fin 3 -> R} (hPz : P z = 0) : W'.Equation P ↔ P y ^ 2 = P x ^ 3
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `OfNat.ofNat_ne_zero`：∀ {R : Type u_1} [inst : AddMonoidWithOne R] [CharZ
ero R] (n : ℕ) [inst_2 : n.AtLeastTwo], OfNat.ofNat n ≠ 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
lemma X_ne_zero_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 → R} (hP : W'.Nonsingular P)
    (hPz : P z = 0) : P x ≠ 0 := by
  intro hPx
  simp only [nonsingular_of_Z_eq_zero hPz, equation_of_Z_eq_zero hPz, hPx, mul_zero, zero_mul,
    zero_pow <| OfNat.ofNat_ne_zero _, ne_self_iff_false, or_false, false_or] at hP
  rwa [pow_eq_zero_iff two_ne_zero, hP.left, eq_self, true_and, mul_zero, ne_self_iff_false] at hP
/-
**WeierstrassCurve.Jacobian.isUnit_X_of_Z_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Wei
erstrassCurve.Jacobian`。
形式化陈述：isUnit_X_of_Z_eq_zero {P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z =
 0) : IsUnit (P x)
参数：hP : W.Nonsingular P；hPz : P z = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
· 使用引理 `WeierstrassCurve.Jacobian.X_ne_zero_of_Z_eq_zero`：X_ne_zero_of_Z_eq_zero
 [NoZeroDivisors R] {P : Fin 3 -> R} (hP : W'.Nonsingular P) (hPz : P z = 0) : P
 x != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
-/
lemma isUnit_X_of_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z = 0) : IsUnit (P x) :=
  (X_ne_zero_of_Z_eq_zero hP hPz).isUnit
/-
**WeierstrassCurve.Jacobian.Y_ne_zero_of_Z_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `We
ierstrassCurve.Jacobian`。
形式化陈述：Y_ne_zero_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 -> R} (hP : W'.Nonsin
gular P) (hPz : P z = 0) : P y != 0
参数：hP : W'.Nonsingular P；hPz : P z = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `WeierstrassCurve.Jacobian.X_ne_zero_of_Z_eq_zero`：X_ne_zero_of_Z_eq_zero
 [NoZeroDivisors R] {P : Fin 3 -> R} (hP : W'.Nonsingular P) (hPz : P z = 0) : P
 x != 0
· 使用定理 `eq_zero_of_pow_eq_zero`：eq_zero_of_pow_eq_zero [Zero R] [Pow R Nat] [IsR
educed R] {n : Nat} (h : x ^ n = 0) : x = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用引理 `WeierstrassCurve.Jacobian.equation_of_Z_eq_zero`：equation_of_Z_eq_zero {
P : Fin 3 -> R} (hPz : P z = 0) : W'.Equation P ↔ P y ^ 2 = P x ^ 3
· 使用引理 `WeierstrassCurve.Jacobian.nonsingular_of_Z_eq_zero`：nonsingular_of_Z_eq_
zero {P : Fin 3 -> R} (hPz : P z = 0) : W'.Nonsingular P ↔ W'.Equation P ∧ (3 * 
P x ^ 2 != 0 ∨ 2 * P y != 0 ∨ W'.a₁ * P …
-/
lemma Y_ne_zero_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 → R} (hP : W'.Nonsingular P)
    (hPz : P z = 0) : P y ≠ 0 := by
  have hPx : P x ≠ 0 := X_ne_zero_of_Z_eq_zero hP hPz
  intro hPy
  rw [nonsingular_of_Z_eq_zero hPz, equation_of_Z_eq_zero hPz, hPy, zero_pow two_ne_zero] at hP
  exact hPx <| eq_zero_of_pow_eq_zero hP.left.symm
/-
**WeierstrassCurve.Jacobian.isUnit_Y_of_Z_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Wei
erstrassCurve.Jacobian`。
形式化陈述：isUnit_Y_of_Z_eq_zero {P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z =
 0) : IsUnit (P y)
参数：hP : W.Nonsingular P；hPz : P z = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
· 使用引理 `WeierstrassCurve.Jacobian.Y_ne_zero_of_Z_eq_zero`：Y_ne_zero_of_Z_eq_zero
 [NoZeroDivisors R] {P : Fin 3 -> R} (hP : W'.Nonsingular P) (hPz : P z = 0) : P
 y != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
-/
lemma isUnit_Y_of_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z = 0) : IsUnit (P y) :=
  (Y_ne_zero_of_Z_eq_zero hP hPz).isUnit
/-
**WeierstrassCurve.Jacobian.equiv_of_Z_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Weiers
trassCurve.Jacobian`。
形式化陈述：equiv_of_Z_eq_zero {P Q : Fin 3 -> F} (hP : W.Nonsingular P) (hQ : W.Nonsi
ngular Q) (hPz : P z = 0) (hQz : Q z = 0) : P ≈ Q
参数：hP : W.Nonsingular P；hQ : W.Nonsingular Q；hPz : P z = 0；hQz : Q z = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `WeierstrassCurve.Jacobian.isUnit_X_of_Z_eq_zero`：isUnit_X_of_Z_eq_zero {
P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z = 0) : IsUnit (P x)
· 使用引理 `WeierstrassCurve.Jacobian.isUnit_Y_of_Z_eq_zero`：isUnit_Y_of_Z_eq_zero {
P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z = 0) : IsUnit (P y)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Units.val_div_eq_div_val`：val_div_eq_div_val : forall u₁ u₂ : αˣ, ↑(u₁ /
 u₂) = (u₁ / u₂ : α)
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WeierstrassCurve.Jacobian.fin3_def`：fin3_def (P : Fin 3 -> R) : ![P x, P
 y, P z] = P
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `IsUnit.mul_div_cancel_left`：∀ {α : Type u} [inst : DivisionCommMonoid α]
 {a : α}, IsUnit a → ∀ (b : α), a * b / a = b
· 使用定理 `IsUnit.pow`：∀ {M : Type u_1} [inst : Monoid M] {a : M} (n : ℕ), IsUnit a
 → IsUnit (a ^ n)
· 使用定理 `IsUnit.div_mul_cancel_left`：∀ {α : Type u} [inst : DivisionCommMonoid α]
 {a : α}, IsUnit a → ∀ (b : α), a / (a * b) = b⁻¹
· 使用定理 `IsUnit.inv_mul_cancel_right`：∀ {α : Type u} [inst : DivisionMonoid α] {b
 : α}, IsUnit b → ∀ (a : α), a * b⁻¹ * b = a
-/
lemma equiv_of_Z_eq_zero {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (hPz : P z = 0) (hQz : Q z = 0) : P ≈ Q := by
  have hPx : IsUnit <| P x := isUnit_X_of_Z_eq_zero hP hPz
  have hPy : IsUnit <| P y := isUnit_Y_of_Z_eq_zero hP hPz
  have hQx : IsUnit <| Q x := isUnit_X_of_Z_eq_zero hQ hQz
  have hQy : IsUnit <| Q y := isUnit_Y_of_Z_eq_zero hQ hQz
  simp only [nonsingular_of_Z_eq_zero, equation_of_Z_eq_zero, hPz, hQz] at hP hQ
  use (hPy.unit / hPx.unit) * (hQx.unit / hQy.unit)
  simp only [Units.smul_def, smul_fin3, Units.val_mul, Units.val_div_eq_div_val, IsUnit.unit_spec,
    mul_pow, div_pow, hQz, mul_zero]
  conv_rhs => rw [← fin3_def P, hPz]
  congr! 2
  · rw [hP.left, pow_succ, (hPx.pow 2).mul_div_cancel_left, hQ.left, pow_succ _ 2,
      (hQx.pow 2).div_mul_cancel_left, hQx.inv_mul_cancel_right]
  · rw [← hP.left, pow_succ, (hPy.pow 2).mul_div_cancel_left, ← hQ.left, pow_succ _ 2,
      (hQy.pow 2).div_mul_cancel_left, hQy.inv_mul_cancel_right]
/-
**WeierstrassCurve.Jacobian.equiv_zero_of_Z_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `W
eierstrassCurve.Jacobian`。
形式化陈述：equiv_zero_of_Z_eq_zero {P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z
 = 0) : P ≈ ![1, 1, 0]
参数：hP : W.Nonsingular P；hPz : P z = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `WeierstrassCurve.Jacobian.equiv_of_Z_eq_zero`：equiv_of_Z_eq_zero {P Q : 
Fin 3 -> F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) (hPz : P z = 0) (hQz :
 Q z = 0) : P ≈ Q
· 使用引理 `WeierstrassCurve.Jacobian.nonsingular_zero`：nonsingular_zero [Nontrivial
 R] : W'.Nonsingular ![1, 1, 0]
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
lemma equiv_zero_of_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z = 0) :
    P ≈ ![1, 1, 0] :=
  equiv_of_Z_eq_zero hP nonsingular_zero hPz rfl
/-
**WeierstrassCurve.Jacobian.comp_equiv_comp** 是 Mathlib 中的一个引理，位于命名空间 `Weierstra
ssCurve.Jacobian`。
形式化陈述：comp_equiv_comp (f : F ->+* K) {P Q : Fin 3 -> F} (hP : W.Nonsingular P) (
hQ : W.Nonsingular Q) : f ∘ P ≈ f ∘ Q ↔ P ≈ Q
参数：f : F ->+* K；hP : W.Nonsingular P；hQ : W.Nonsingular Q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `WeierstrassCurve.Jacobian.equiv_of_Z_eq_zero`：equiv_of_Z_eq_zero {P Q : 
Fin 3 -> F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) (hPz : P z = 0) (hQz :
 Q z = 0) : P ≈ Q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用引理 `WeierstrassCurve.Jacobian.Z_eq_zero_of_equiv`：Z_eq_zero_of_equiv {P Q : 
Fin 3 -> R} (h : P ≈ Q) : P z = 0 ↔ Q z = 0
· 使用引理 `WeierstrassCurve.Jacobian.equiv_of_X_eq_of_Y_eq`：equiv_of_X_eq_of_Y_eq {
P Q : Fin 3 -> F} (hPz : P z != 0) (hQz : Q z != 0) (hx : P x * Q z ^ 2 = Q x * 
P z ^ 2) (hy : P y * Q z ^ 3 = Q y * …
· 使用定理 `map_ne_zero_iff`：∀ {R : Type u_10} {S : Type u_11} {F : Type u_12} [inst
 : Zero R] [inst_1 : Zero S] [inst_2 : FunLike F R S]   [ZeroHomClass F R S] (f 
: F),…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用引理 `WeierstrassCurve.Jacobian.X_eq_of_equiv`：X_eq_of_equiv {P Q : Fin 3 -> R
} (h : P ≈ Q) : P x * Q z ^ 2 = Q x * P z ^ 2
· 使用引理 `WeierstrassCurve.Jacobian.Y_eq_of_equiv`：Y_eq_of_equiv {P Q : Fin 3 -> R
} (h : P ≈ Q) : P y * Q z ^ 3 = Q y * P z ^ 3
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WeierstrassCurve.Jacobian.comp_smul`：comp_smul (f : R ->+* S) (P : Fin 3
 -> R) (u : R) : f ∘ (u • P) = f u • f ∘ P
-/
lemma comp_equiv_comp (f : F →+* K) {P Q : Fin 3 → F} (hP : W.Nonsingular P)
    (hQ : W.Nonsingular Q) : f ∘ P ≈ f ∘ Q ↔ P ≈ Q := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_cases hz : f (P z) = 0
    · exact equiv_of_Z_eq_zero hP hQ ((map_eq_zero_iff f f.injective).mp hz) <|
        (map_eq_zero_iff f f.injective).mp <| (Z_eq_zero_of_equiv h).mp hz
    · refine equiv_of_X_eq_of_Y_eq ((map_ne_zero_iff f f.injective).mp hz)
        ((map_ne_zero_iff f f.injective).mp <| hz.comp (Z_eq_zero_of_equiv h).mpr) ?_ ?_
      all_goals apply f.injective; map_simp
      exacts [X_eq_of_equiv h, Y_eq_of_equiv h]
  · rcases h with ⟨u, rfl⟩
    exact ⟨Units.map f u, (comp_smul ..).symm⟩

variable (W') in
/-- The proposition that a Jacobian point class on a Weierstrass curve `W` is nonsingular.

If `P` is a Jacobian point representative on `W`, then `W.NonsingularLift ⟦P⟧` is definitionally
equivalent to `W.Nonsingular P`.

Note that this definition is only mathematically accurate for fields. -/
/-
**WeierstrassCurve.Jacobian.NonsingularLift** 是 Mathlib 中的一个定义，位于命名空间 `Weierstra
ssCurve.Jacobian`。
形式化陈述：NonsingularLift (P : PointClass R) : Prop
参数：P : PointClass R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposition that a Jacobian point class on a Weierstrass curve `W` is nonsin
gular.

If `P` is a Jacobian point representative on `W`, then `W.NonsingularLift ⟦P⟧` i
s definitionally
equivalent to `W.Nonsingular P`.

Note that this definition is only mathematically accurate for fields.
-/
def NonsingularLift (P : PointClass R) : Prop :=
  P.lift W'.Nonsingular fun _ _ => propext ∘ nonsingular_of_equiv
/-
**WeierstrassCurve.Jacobian.nonsingularLift_iff** 是 Mathlib 中的一个引理，位于命名空间 `Weier
strassCurve.Jacobian`。
形式化陈述：nonsingularLift_iff (P : Fin 3 -> R) : W'.NonsingularLift ⟦P⟧ ↔ W'.Nonsing
ular P
参数：P : Fin 3 -> R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma nonsingularLift_iff (P : Fin 3 → R) : W'.NonsingularLift ⟦P⟧ ↔ W'.Nonsingular P :=
  Iff.rfl
/-
**WeierstrassCurve.Jacobian.nonsingularLift_zero** 是 Mathlib 中的一个引理，位于命名空间 `Weie
rstrassCurve.Jacobian`。
形式化陈述：nonsingularLift_zero [Nontrivial R] : W'.NonsingularLift ⟦![1, 1, 0]⟧
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Jacobian.nonsingular_zero`：nonsingular_zero [Nontrivial
 R] : W'.Nonsingular ![1, 1, 0]
-/
lemma nonsingularLift_zero [Nontrivial R] : W'.NonsingularLift ⟦![1, 1, 0]⟧ :=
  nonsingular_zero
/-
**WeierstrassCurve.Jacobian.nonsingularLift_some** 是 Mathlib 中的一个引理，位于命名空间 `Weie
rstrassCurve.Jacobian`。
形式化陈述：nonsingularLift_some (a b : R) : W'.NonsingularLift ⟦![a, b, 1]⟧ ↔ W'.toAf
fine.Nonsingular a b
参数：a b : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Jacobian.nonsingular_some`：nonsingular_some (a b : R) :
 W'.Nonsingular ![a, b, 1] ↔ W'.toAffine.Nonsingular a b
-/
lemma nonsingularLift_some (a b : R) :
    W'.NonsingularLift ⟦![a, b, 1]⟧ ↔ W'.toAffine.Nonsingular a b :=
  nonsingular_some a b

/-! ## Maps and base changes -/

variable (W') (f : R →+* S)

/-- The Weierstrass curve in Jacobian coordinates mapped over a ring homomorphism `f : R →+* S`. -/
/-
**WeierstrassCurve.Jacobian.map** 是 Mathlib 中的一个缩写定义，位于命名空间 `WeierstrassCurve.Ja
cobian`。
形式化陈述：map : Jacobian S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Weierstrass curve in Jacobian coordinates mapped over a ring homomorphism `f
 : R →+* S`.
-/
abbrev map : Jacobian S :=
  WeierstrassCurve.map W' f

variable (S) in
/-- The Weierstrass curve in Jacobian coordinates base changed to an algebra `S` over `R`. -/
/-
**WeierstrassCurve.Jacobian.baseChange** 是 Mathlib 中的一个缩写定义，位于命名空间 `WeierstrassC
urve.Jacobian`。
形式化陈述：baseChange [Algebra R S] : Jacobian S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Weierstrass curve in Jacobian coordinates base changed to an algebra `S` ove
r `R`.
-/
abbrev baseChange [Algebra R S] : Jacobian S :=
  WeierstrassCurve.baseChange W' S

/-- The notation `\textf` for `WeierstrassCurve.Jacobian.baseChange W S`. -/
scoped notation:max W:max "⁄" S:max => baseChange W S

@[simp]
/-
**WeierstrassCurve.Jacobian.map_polynomial** 是 Mathlib 中的一个引理，位于命名空间 `Weierstras
sCurve.Jacobian`。
形式化陈述：map_polynomial : (W'.map f).polynomial = .map f W'.polynomial
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
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MvPolynomial.map_X`：map_X (n : σ) : map f (X n : MvPolynomial σ R) = X n
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `MvPolynomial.map_C`：map_C : forall a : R, map f (C a : MvPolynomial σ R)
 = C (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_polynomial : (W'.map f).polynomial = .map f W'.polynomial := by
  simp only [polynomial]
  map_simp

variable {W'} in
/-
**WeierstrassCurve.Jacobian.Equation.map** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassC
urve.Jacobian.Equation`。
形式化陈述：∀ {R : Type r} [inst : CommRing R] {W' : WeierstrassCurve.Jacobian R} {S :
 Type s} [inst_1 : CommRing S] (f : R →+* S)   {P : Fin 3 → R}, W'.Equation P → 
(W'.map f).Equation (⇑f ∘ P)
参数：f : R →+* S；W'.map f；⇑f ∘ P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.Jacobian.Equation.eq_1`：∀ {R : Type r} [inst : CommRing
 R] (W' : WeierstrassCurve.Jacobian R) (P : Fin 3 → R),   W'.Equation P = ((MvPo
lynomial.eval P) W'.polynomia…
· 使用引理 `WeierstrassCurve.Jacobian.map_polynomial`：map_polynomial : (W'.map f).po
lynomial = .map f W'.polynomial
· 使用定理 `MvPolynomial.eval_map`：eval_map (f : R ->+* S₁) (g : σ -> S₁) (p : MvPol
ynomial σ R) : eval g (map f p) = eval₂ f g p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.eval₂_comp`：eval₂_comp (f : R ->+* S₁) (g : σ -> R) (p : Mv
Polynomial σ R) : f (eval g p) = eval₂ f (f ∘ g) p
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
lemma Equation.map {P : Fin 3 → R} (h : W'.Equation P) : (W'.map f).Equation (f ∘ P) := by
  rw [Equation, map_polynomial, eval_map, ← eval₂_comp, h, map_zero]

variable {f} in
@[simp]
/-
**WeierstrassCurve.Jacobian.map_equation** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassC
urve.Jacobian`。
形式化陈述：map_equation (hf : Function.Injective f) (P : Fin 3 -> R) : (W'.map f).Equ
ation (f ∘ P) ↔ W'.Equation P
参数：hf : Function.Injective f；P : Fin 3 -> R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.map_polynomial`：map_polynomial : (W'.map f).po
lynomial = .map f W'.polynomial
· 使用定理 `MvPolynomial.eval_map`：eval_map (f : R ->+* S₁) (g : σ -> S₁) (p : MvPol
ynomial σ R) : eval g (map f p) = eval₂ f g p
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
lemma map_equation (hf : Function.Injective f) (P : Fin 3 → R) :
    (W'.map f).Equation (f ∘ P) ↔ W'.Equation P := by
  simp only [Equation, map_polynomial, eval_map, ← eval₂_comp, map_eq_zero_iff f hf]

@[simp]
/-
**WeierstrassCurve.Jacobian.map_polynomialX** 是 Mathlib 中的一个引理，位于命名空间 `Weierstra
ssCurve.Jacobian`。
形式化陈述：map_polynomialX : (W'.map f).polynomialX = .map f W'.polynomialX
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.map_polynomial`：map_polynomial : (W'.map f).po
lynomial = .map f W'.polynomial
· 使用定理 `MvPolynomial.pderiv_map`：pderiv_map {S} [CommSemiring S] {φ : R ->+* S} 
{f : MvPolynomial σ R} {i : σ} : pderiv i (map φ f) = map φ (pderiv i f)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_polynomialX : (W'.map f).polynomialX = .map f W'.polynomialX := by
  simp only [polynomialX, map_polynomial, pderiv_map]

@[simp]
/-
**WeierstrassCurve.Jacobian.map_polynomialY** 是 Mathlib 中的一个引理，位于命名空间 `Weierstra
ssCurve.Jacobian`。
形式化陈述：map_polynomialY : (W'.map f).polynomialY = .map f W'.polynomialY
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.map_polynomial`：map_polynomial : (W'.map f).po
lynomial = .map f W'.polynomial
· 使用定理 `MvPolynomial.pderiv_map`：pderiv_map {S} [CommSemiring S] {φ : R ->+* S} 
{f : MvPolynomial σ R} {i : σ} : pderiv i (map φ f) = map φ (pderiv i f)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_polynomialY : (W'.map f).polynomialY = .map f W'.polynomialY := by
  simp only [polynomialY, map_polynomial, pderiv_map]

@[simp]
/-
**WeierstrassCurve.Jacobian.map_polynomialZ** 是 Mathlib 中的一个引理，位于命名空间 `Weierstra
ssCurve.Jacobian`。
形式化陈述：map_polynomialZ : (W'.map f).polynomialZ = .map f W'.polynomialZ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Jacobian.map_polynomial`：map_polynomial : (W'.map f).po
lynomial = .map f W'.polynomial
· 使用定理 `MvPolynomial.pderiv_map`：pderiv_map {S} [CommSemiring S] {φ : R ->+* S} 
{f : MvPolynomial σ R} {i : σ} : pderiv i (map φ f) = map φ (pderiv i f)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_polynomialZ : (W'.map f).polynomialZ = .map f W'.polynomialZ := by
  simp only [polynomialZ, map_polynomial, pderiv_map]

variable {f} in
@[simp]
/-
**WeierstrassCurve.Jacobian.map_nonsingular** 是 Mathlib 中的一个引理，位于命名空间 `Weierstra
ssCurve.Jacobian`。
形式化陈述：map_nonsingular (hf : Function.Injective f) (P : Fin 3 -> R) : (W'.map f).
Nonsingular (f ∘ P) ↔ W'.Nonsingular P
参数：hf : Function.Injective f；P : Fin 3 -> R。
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
· 使用引理 `WeierstrassCurve.Jacobian.map_equation`：map_equation (hf : Function.Inje
ctive f) (P : Fin 3 -> R) : (W'.map f).Equation (f ∘ P) ↔ W'.Equation P
· 使用引理 `WeierstrassCurve.Jacobian.map_polynomialX`：map_polynomialX : (W'.map f).
polynomialX = .map f W'.polynomialX
· 使用定理 `MvPolynomial.eval_map`：eval_map (f : R ->+* S₁) (g : σ -> S₁) (p : MvPol
ynomial σ R) : eval g (map f p) = eval₂ f g p
· 使用定理 `map_ne_zero_iff`：∀ {R : Type u_10} {S : Type u_11} {F : Type u_12} [inst
 : Zero R] [inst_1 : Zero S] [inst_2 : FunLike F R S]   [ZeroHomClass F R S] (f 
: F),…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `WeierstrassCurve.Jacobian.map_polynomialY`：map_polynomialY : (W'.map f).
polynomialY = .map f W'.polynomialY
· 使用引理 `WeierstrassCurve.Jacobian.map_polynomialZ`：map_polynomialZ : (W'.map f).
polynomialZ = .map f W'.polynomialZ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma map_nonsingular (hf : Function.Injective f) (P : Fin 3 → R) :
    (W'.map f).Nonsingular (f ∘ P) ↔ W'.Nonsingular P := by
  simp only [Nonsingular, W'.map_equation hf, map_polynomialX, map_polynomialY, map_polynomialZ,
    eval_map, ← eval₂_comp, map_ne_zero_iff f hf]

variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Algebra R B] [Algebra S B]
  [IsScalarTower R S B] (f : A →ₐ[S] B)
/-
**WeierstrassCurve.Jacobian.map_baseChange** 是 Mathlib 中的一个引理，位于命名空间 `Weierstras
sCurve.Jacobian`。
形式化陈述：map_baseChange : (W'⁄A).map f = W'⁄B
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.map_baseChange`：map_baseChange {S : Type s} [CommRing S
] [Algebra R S] {A : Type v} [CommRing A] [Algebra R A] [Algebra S A] [IsScalarT
ower R S A] {B : Type…
-/
lemma map_baseChange : (W'⁄A).map f = W'⁄B :=
  WeierstrassCurve.map_baseChange W' f
/-
**WeierstrassCurve.Jacobian.baseChange_polynomial** 是 Mathlib 中的一个引理，位于命名空间 `Wei
erstrassCurve.Jacobian`。
形式化陈述：baseChange_polynomial : (W'⁄B).polynomial = .map f (W'⁄A).polynomial
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WeierstrassCurve.Jacobian.map_polynomial`：map_polynomial : (W'.map f).po
lynomial = .map f W'.polynomial
· 使用引理 `WeierstrassCurve.Jacobian.map_baseChange`：map_baseChange : (W'⁄A).map f 
= W'⁄B
-/
lemma baseChange_polynomial : (W'⁄B).polynomial = .map f (W'⁄A).polynomial := by
  rw [← map_polynomial, map_baseChange]

variable {W'} in
/-
**WeierstrassCurve.Jacobian.Equation.baseChange** 是 Mathlib 中的一个定理，位于命名空间 `Weier
strassCurve.Jacobian.Equation`。
形式化陈述：∀ {R : Type r} [inst : CommRing R] {W' : WeierstrassCurve.Jacobian R} {S :
 Type s} [inst_1 : CommRing S] {A : Type u}   [inst_2 : CommRing A] {B : Type v}
 [inst_3 : CommRing B] [inst_4 : Algebra R S] [inst_5 : Algebra R A]   [inst_6 :
 Algebra S A] [IsScalarTower R S A] [inst_8 : Algebra R B] [inst_9 : Algebra S B
] [IsScalarTower R S B]   (f : A →ₐ[S] B) {P : Fin 3 → A}, (W'.baseChange A).Equ
ation P → (W'.baseChange B).Equation (⇑f ∘ P)
参数：f : A →ₐ[S] B；W'.baseChange A；W'.baseChange B；⇑f ∘ P。
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
· 使用引理 `WeierstrassCurve.Jacobian.map_baseChange`：map_baseChange : (W'⁄A).map f 
= W'⁄B
· 使用定理 `WeierstrassCurve.Jacobian.Equation.map`：∀ {R : Type r} [inst : CommRing 
R] {W' : WeierstrassCurve.Jacobian R} {S : Type s} [inst_1 : CommRing S] (f : R 
→+* S)   {P : Fin 3 → R}, W'…
-/
lemma Equation.baseChange {P : Fin 3 → A} (h : (W'⁄A).Equation P) : (W'⁄B).Equation (f ∘ P) := by
  convert! Equation.map f.toRingHom h using 1
  rw [AlgHom.toRingHom_eq_coe, map_baseChange]

variable {f} in
/-
**WeierstrassCurve.Jacobian.baseChange_equation** 是 Mathlib 中的一个引理，位于命名空间 `Weier
strassCurve.Jacobian`。
形式化陈述：baseChange_equation (hf : Function.Injective f) (P : Fin 3 -> A) : (W'⁄B).
Equation (f ∘ P) ↔ (W'⁄A).Equation P
参数：hf : Function.Injective f；P : Fin 3 -> A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.coe_coe`：coe_coe {F : Type*} [FunLike F α β] [RingHomClass F α β
] (f : F) : ((f : α ->+* β) : α -> β) = f
· 使用引理 `WeierstrassCurve.Jacobian.map_equation`：map_equation (hf : Function.Inje
ctive f) (P : Fin 3 -> R) : (W'.map f).Equation (f ∘ P) ↔ W'.Equation P
· 使用定理 `AlgHom.toRingHom_eq_coe`：toRingHom_eq_coe (f : A ->ₐ[R] B) : f.toRingHom
 = f
· 使用引理 `WeierstrassCurve.Jacobian.map_baseChange`：map_baseChange : (W'⁄A).map f 
= W'⁄B
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma baseChange_equation (hf : Function.Injective f) (P : Fin 3 → A) :
    (W'⁄B).Equation (f ∘ P) ↔ (W'⁄A).Equation P := by
  rw [← RingHom.coe_coe, ← map_equation _ hf, AlgHom.toRingHom_eq_coe, map_baseChange]
/-
**WeierstrassCurve.Jacobian.baseChange_polynomialX** 是 Mathlib 中的一个引理，位于命名空间 `We
ierstrassCurve.Jacobian`。
形式化陈述：baseChange_polynomialX : (W'⁄B).polynomialX = .map f (W'⁄A).polynomialX
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WeierstrassCurve.Jacobian.map_polynomialX`：map_polynomialX : (W'.map f).
polynomialX = .map f W'.polynomialX
· 使用引理 `WeierstrassCurve.Jacobian.map_baseChange`：map_baseChange : (W'⁄A).map f 
= W'⁄B
-/
lemma baseChange_polynomialX : (W'⁄B).polynomialX = .map f (W'⁄A).polynomialX := by
  rw [← map_polynomialX, map_baseChange]
/-
**WeierstrassCurve.Jacobian.baseChange_polynomialY** 是 Mathlib 中的一个引理，位于命名空间 `We
ierstrassCurve.Jacobian`。
形式化陈述：baseChange_polynomialY : (W'⁄B).polynomialY = .map f (W'⁄A).polynomialY
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WeierstrassCurve.Jacobian.map_polynomialY`：map_polynomialY : (W'.map f).
polynomialY = .map f W'.polynomialY
· 使用引理 `WeierstrassCurve.Jacobian.map_baseChange`：map_baseChange : (W'⁄A).map f 
= W'⁄B
-/
lemma baseChange_polynomialY : (W'⁄B).polynomialY = .map f (W'⁄A).polynomialY := by
  rw [← map_polynomialY, map_baseChange]
/-
**WeierstrassCurve.Jacobian.baseChange_polynomialZ** 是 Mathlib 中的一个引理，位于命名空间 `We
ierstrassCurve.Jacobian`。
形式化陈述：baseChange_polynomialZ : (W'⁄B).polynomialZ = .map f (W'⁄A).polynomialZ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WeierstrassCurve.Jacobian.map_polynomialZ`：map_polynomialZ : (W'.map f).
polynomialZ = .map f W'.polynomialZ
· 使用引理 `WeierstrassCurve.Jacobian.map_baseChange`：map_baseChange : (W'⁄A).map f 
= W'⁄B
-/
lemma baseChange_polynomialZ : (W'⁄B).polynomialZ = .map f (W'⁄A).polynomialZ := by
  rw [← map_polynomialZ, map_baseChange]

variable {f} in
/-
**WeierstrassCurve.Jacobian.baseChange_nonsingular** 是 Mathlib 中的一个引理，位于命名空间 `We
ierstrassCurve.Jacobian`。
形式化陈述：baseChange_nonsingular (hf : Function.Injective f) (P : Fin 3 -> A) : (W'⁄
B).Nonsingular (f ∘ P) ↔ (W'⁄A).Nonsingular P
参数：hf : Function.Injective f；P : Fin 3 -> A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.coe_coe`：coe_coe {F : Type*} [FunLike F α β] [RingHomClass F α β
] (f : F) : ((f : α ->+* β) : α -> β) = f
· 使用引理 `WeierstrassCurve.Jacobian.map_nonsingular`：map_nonsingular (hf : Functio
n.Injective f) (P : Fin 3 -> R) : (W'.map f).Nonsingular (f ∘ P) ↔ W'.Nonsingula
r P
· 使用定理 `AlgHom.toRingHom_eq_coe`：toRingHom_eq_coe (f : A ->ₐ[R] B) : f.toRingHom
 = f
· 使用引理 `WeierstrassCurve.Jacobian.map_baseChange`：map_baseChange : (W'⁄A).map f 
= W'⁄B
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma baseChange_nonsingular (hf : Function.Injective f) (P : Fin 3 → A) :
    (W'⁄B).Nonsingular (f ∘ P) ↔ (W'⁄A).Nonsingular P := by
  rw [← RingHom.coe_coe, ← map_nonsingular _ hf, AlgHom.toRingHom_eq_coe, map_baseChange]

end Jacobian

end WeierstrassCurve

