/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Tactic.Ring.NamePolyVars

/-!
# The addition-and-subtraction map on x-coordinates

We set up the endomorphism of `ℙ²` that on affine points with affine sum is equal to

`(x(P) * x(Q) : x(P) + x(Q) : 1) ↦ (x(P+Q) * x(P-Q) : x(P+Q) + x(P-Q) : 1);`

see `WeierstrassCurve.addSubMap` (this is on coordinate vectors).

TODO: Show that the map really does what it is claimed to do.

This will be used to eventually show the approximate parallelogram law for `K`-points
on an elliptic curve `E`:
`∃ C, ∀ P Q : E(K), |h(P+Q) + h(P-Q) - 2*h(P) - 2*h(Q)| ≤ C`,
where `K` is a field with a height and `h` denotes the (logarithmic) naïve height on `E(K)`.
-/

public section

namespace WeierstrassCurve

/-!
### The addition-and-subtraction map on x-coordinates
-/

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

open MvPolynomial

name_poly_vars s, t, u over R

/-- The polynomial map on coordinate vectors giving
`(x(P) * x(Q) : x(P) + x(Q) : 1) ↦ (x(P+Q) * x(P-Q) : x(P+Q) + x(P-Q) : 1)`
for points `P`, `Q` on the Weierstrass curve `W`. -/
/-
**WeierstrassCurve.addSubMap** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve`。
形式化陈述：{R : Type u_1} → [inst : CommRing R] → WeierstrassCurve R → Fin 3 → MvPoly
nomial (Fin 3) R
参数：Fin 3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The polynomial map on coordinate vectors giving
`(x(P) * x(Q) : x(P) + x(Q) : 1) ↦ (x(P+Q) * x(P-Q) : x(P+Q) + x(P-Q) : 1)`
for points `P`, `Q` on the Weierstrass curve `W`.
-/
@[expose] noncomputable def addSubMap : Fin 3 → MvPolynomial (Fin 3) R :=
  ![s ^ 2 - C W.b₄ * s * u - C W.b₆ * t * u - C W.b₈ * u ^ 2,
    C 2 * t * s + C W.b₂ * s * u + C W.b₄ * t * u + C W.b₆ * u ^ 2,
    t ^ 2 - C 4 * s * u]

/-- The coefficient polynomials in linear combinations of the polynomials in `addSubMap`
that result in the fourth powers of the variables, multiplied by `W.Δ`. -/
/-
**WeierstrassCurve.addSubMapCoeff** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve`。
形式化陈述：addSubMapCoeff : Fin 3 × Fin 3 -> MvPolynomial (Fin 3) R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coefficient polynomials in linear combinations of the polynomials in `addSub
Map`
that result in the fourth powers of the variables, multiplied by `W.Δ`.
-/
noncomputable def addSubMapCoeff : Fin 3 × Fin 3 → MvPolynomial (Fin 3) R :=
  ![![C (-W.b₂ ^ 2 * W.b₈ + 9 * W.b₂ * W.b₄ * W.b₆ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2) * s ^ 2 +
        C (2 * W.b₂ * W.b₄ * W.b₈ - 2 * W.b₄ ^ 2 * W.b₆ - 10 * W.b₆ * W.b₈) * s * t +
        C (-W.b₂ * W.b₆ * W.b₈ + W.b₄ * W.b₆ ^ 2) * s * u +
        C (3 * W.b₄ ^ 2 * W.b₈ - 3 * W.b₄ * W.b₆ ^ 2) * t ^ 2 +
        C (3 * W.b₄ * W.b₆ * W.b₈ - 3 * W.b₆ ^ 3) * t * u,
      C (-W.b₂ * W.b₄ * W.b₈ + W.b₄ ^ 2 * W.b₆ + 5 * W.b₆ * W.b₈) * s ^ 2 +
        C (2 * W.b₂ * W.b₆ * W.b₈ - 2 * W.b₄ * W.b₆ ^ 2 - 10 * W.b₈ ^ 2) * s * t +
        C (-W.b₂ * W.b₈ ^ 2 + W.b₄ * W.b₆ * W.b₈) * s * u +
        C (3 * W.b₄ * W.b₆ * W.b₈ - 3 * W.b₆ ^ 3) * t ^ 2 +
        C (3 * W.b₄ * W.b₈ ^ 2 - 3 * W.b₆ ^ 2 * W.b₈) * t * u,
      C (W.b₂ * W.b₆ * W.b₈ - 8 * W.b₄ ^ 2 * W.b₈ + 7 * W.b₄ * W.b₆ ^ 2) * s ^ 2 +
        C (-6 * W.b₄ * W.b₆ * W.b₈ + 6 * W.b₆ ^ 3) * s * t +
        C (-8 * W.b₄ * W.b₈ ^ 2 + 8 * W.b₆ ^ 2 * W.b₈) * s * u],
    ![C (96 * W.b₆) * s * t + C (12 * W.b₂ * W.b₆ - 64 * W.b₈) * t ^ 2 +
        C (16 * W.b₄ * W.b₆) * t * u,
      C (-48 * W.b₆) * s ^ 2 + C (32 * W.b₈) * s * t +
        C (-4 * W.b₂ * W.b₈ + 16 * W.b₄ * W.b₆) * t ^ 2 + C (16 * W.b₄ * W.b₈) * t * u,
      C (-12 * W.b₂ * W.b₆) * s ^ 2 + C (8 * W.b₂ * W.b₈ - 32 * W.b₄ * W.b₆) * s * t +
        C (-12 * W.b₆ ^ 2) * s * u +
        C (-W.b₂ ^ 2 * W.b₈ + 9 * W.b₂ * W.b₄ * W.b₆ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2) * t ^ 2 +
        C (4 * W.b₂ * W.b₄ * W.b₈ - 4 * W.b₂ * W.b₆ ^ 2) * t * u],
    ![C (-12) * t ^ 2 + C (-4 * W.b₂) * t * u + C (W.b₂ ^ 2 - 32 * W.b₄) * u ^ 2,
      C 6 * s * t + C (-W.b₂) * s * u + C (-5 * W.b₄) * t * u + C (W.b₂ * W.b₄ - 27 * W.b₆) * u ^ 2,
      C (-8 * W.b₄) * s * u + C (-12 * W.b₆) * t * u + C (W.b₄ ^ 2 - 28 * W.b₈) * u ^ 2]].uncurry
/-
**WeierstrassCurve.CXX** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma CXX {i : Fin 3} {a : R} : (C a * X (R := R) i ^ 2).IsHomogeneous 2 :=
  isHomogeneous_C_mul_X_pow ..
/-
**WeierstrassCurve.CXY** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma CXY {i j : Fin 3} {a : R} : (C a * X (R := R) i * X j).IsHomogeneous 2 :=
  .mul (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
/-
**WeierstrassCurve.isHomogeneous_addSubMap** 是 Mathlib 中的一个引理，位于命名空间 `Weierstras
sCurve`。
形式化陈述：isHomogeneous_addSubMap (i : Fin 3) : (addSubMap W i).IsHomogeneous 2
参数：i : Fin 3。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `MvPolynomial.IsHomogeneous.sub`：sub (hφ : IsHomogeneous φ n) (hψ : IsHom
ogeneous ψ n) : IsHomogeneous (φ - ψ) n
· 使用定理 `MvPolynomial.isHomogeneous_X_pow`：∀ {σ : Type u_1} {R : Type u_3} [inst 
: CommSemiring R] (i : σ) (n : ℕ), (MvPolynomial.X i ^ n).IsHomogeneous n
· 使用定理 `_private.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap.0.Weie
rstrassCurve.CXY`：∀ {R : Type u_1} [inst : CommRing R] {i j : Fin 3} {a : R},   
(MvPolynomial.C a * MvPolynomial.X i * MvPolynomial.X j).IsHomogeneous 2
· 使用定理 `_private.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap.0.Weie
rstrassCurve.CXX`：∀ {R : Type u_1} [inst : CommRing R] {i : Fin 3} {a : R}, (MvP
olynomial.C a * MvPolynomial.X i ^ 2).IsHomogeneous 2
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `MvPolynomial.IsHomogeneous.add`：add (hφ : IsHomogeneous φ n) (hψ : IsHom
ogeneous ψ n) : IsHomogeneous (φ + ψ) n
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
lemma isHomogeneous_addSubMap (i : Fin 3) : (addSubMap W i).IsHomogeneous 2 := by
  simp only [addSubMap]
  fin_cases i <;>
    simp only [Fin.isValue, Fin.mk_one, Fin.zero_eta, Fin.reduceFinMk, Matrix.cons_val,
      Matrix.cons_val_one, Matrix.cons_val_zero]
  · exact isHomogeneous_X_pow .. |>.sub CXY |>.sub CXY |>.sub CXX
  · exact CXY.add CXY |>.add CXY |>.add CXX
  · exact isHomogeneous_X_pow .. |>.sub CXY
/-
**WeierstrassCurve.isHomogeneous_addSubMapCoeff** 是 Mathlib 中的一个引理，位于命名空间 `Weier
strassCurve`。
形式化陈述：isHomogeneous_addSubMapCoeff (ij : Fin 3 × Fin 3) : (addSubMapCoeff W ij).
IsHomogeneous 2
参数：ij : Fin 3 × Fin 3。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `MvPolynomial.IsHomogeneous.add`：add (hφ : IsHomogeneous φ n) (hψ : IsHom
ogeneous ψ n) : IsHomogeneous (φ + ψ) n
· 使用定理 `_private.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap.0.Weie
rstrassCurve.CXX`：∀ {R : Type u_1} [inst : CommRing R] {i : Fin 3} {a : R}, (MvP
olynomial.C a * MvPolynomial.X i ^ 2).IsHomogeneous 2
· 使用定理 `_private.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap.0.Weie
rstrassCurve.CXY`：∀ {R : Type u_1} [inst : CommRing R] {i j : Fin 3} {a : R},   
(MvPolynomial.C a * MvPolynomial.X i * MvPolynomial.X j).IsHomogeneous 2
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
lemma isHomogeneous_addSubMapCoeff (ij : Fin 3 × Fin 3) :
    (addSubMapCoeff W ij).IsHomogeneous 2 := by
  simp only [addSubMapCoeff]
  fin_cases ij <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Function.uncurry_apply_pair,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, neg_mul, Fin.mk_one,
      Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val, Fin.zero_eta]
    -- The following works, but is slow (44894 vs. 11717 heartbeats):
    -- <;> repeat first | refine .add ?_ CXY | refine .add ?_ CXX | exact CXX | exact CXY
  · exact CXX.add CXY |>.add CXY |>.add CXX |>.add CXY
  · exact CXX.add CXY |>.add CXY |>.add CXX |>.add CXY
  · exact CXX.add CXY |>.add CXY
  · exact CXY.add CXX |>.add CXY
  · exact CXX.add CXY |>.add CXX |>.add CXY
  · exact CXX.add CXY |>.add CXY |>.add CXX |>.add CXY
  · exact CXX.add CXY |>.add CXX
  · exact CXY.add CXY |>.add CXY |>.add CXX
  · exact CXY.add CXY |>.add CXX

variable [W.IsElliptic]
/-
**WeierstrassCurve.addSubMapCoeff_condition** 是 Mathlib 中的一个引理，位于命名空间 `Weierstra
ssCurve`。
形式化陈述：addSubMapCoeff_condition (x : Fin 3 -> R) (i : Fin 3) : ∑ j : Fin 3, (C (↑
W.Δ'⁻¹ : R) * addSubMapCoeff W (i, j)).eval x * (addSubMap W j).eval x = x i ^ 4
参数：x : Fin 3 -> R；i : Fin 3。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.eval_mul`：eval_mul : eval f (p * q) = eval f p * eval f q
· 使用定理 `MvPolynomial.eval_C`：eval_C : forall a, eval f (C a) = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Units.inv_mul_eq_iff_eq_mul`：inv_mul_eq_iff_eq_mul {b c : α} : ↑a⁻¹ * b 
= c ↔ b = a * c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.sum_univ_three`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 3
 → M), ∑ i, f i = f 0 + f 1 + f 2
· 使用定理 `WeierstrassCurve.addSubMap.eq_1`：∀ {R : Type u_1} [inst : CommRing R] (W
 : WeierstrassCurve R),   W.addSubMap =     ![MvPolynomial.X 0 ^ 2 - MvPolynomia
l.C W.b₄ * MvPolynomi…
· 使用定理 `_private.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap.0.Weie
rstrassCurve.addSubMapCoeff.eq_1`：∀ {R : Type u_1} [inst : CommRing R] (W : Weie
rstrassCurve R),   W.addSubMapCoeff =     Function.uncurry       ![![MvPolynomia
l.C (-W.b₂ ^ 2…
· 使用定理 `Function.uncurry_apply_pair`：∀ {α : Type u_1} {β : Type u_2} {γ : Sort u
_3} (f : α → β → γ) (x : α) (y : β), Function.uncurry f (x, y) = f x y
· 使用引理 `WeierstrassCurve.coe_Δ'`：coe_Δ' : W.Δ' = W.Δ
· 使用定理 `WeierstrassCurve.Δ.eq_1`：∀ {R : Type u} [inst : CommRing R] (W : Weierst
rassCurve R),   W.Δ = -W.b₂ ^ 2 * W.b₈ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2 + 9 * W.b₂
 * W.b₄ * W.b…
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `MvPolynomial.C_sub`：C_sub : (C (a - a') : MvPolynomial σ R) = C a - C a'
· 使用定理 `MvPolynomial.C_add`：C_add : (C (a + a') : MvPolynomial σ R) = C a + C a'
· 使用定理 `MvPolynomial.C_neg`：C_neg : (C (-a) : MvPolynomial σ R) = -C a
· 使用定理 `MvPolynomial.C_mul`：C_mul : (C (a * a') : MvPolynomial σ R) = C a * C a'
· 使用定理 `MvPolynomial.C_pow`：C_pow (a : R) (n : Nat) : (C (a ^ n) : MvPolynomial 
σ R) = C a ^ n
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
（共 45 条，此处仅展示前 30 条）
-/
lemma addSubMapCoeff_condition (x : Fin 3 → R) (i : Fin 3) :
    ∑ j : Fin 3, (C (↑W.Δ'⁻¹ : R) * addSubMapCoeff W (i, j)).eval x *
      (addSubMap W j).eval x = x i ^ 4 := by
  simp only [eval_mul, eval_C, mul_assoc]
  rw [← Finset.mul_sum, Units.inv_mul_eq_iff_eq_mul, Fin.sum_univ_three, addSubMap, addSubMapCoeff,
    Function.uncurry_apply_pair, coe_Δ', Δ]
  fin_cases i <;> simp <;> grind only [b_relation]
/-
**WeierstrassCurve.addSubMap_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve
`。
形式化陈述：addSubMap_ne_zero [IsReduced R] {x : Fin 3 -> R} (hx : x != 0) : (fun i =>
 (addSubMap W i).eval x) != 0
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.eval_C`：eval_C : forall a, eval f (C a) = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WeierstrassCurve.addSubMapCoeff_condition`：addSubMapCoeff_condition (x :
 Fin 3 -> R) (i : Fin 3) : ∑ j : Fin 3, (C (↑W.Δ'⁻¹ : R) * addSubMapCoeff W (i, 
j)).eval x * (addSubMap W j).ev…
-/
lemma addSubMap_ne_zero [IsReduced R] {x : Fin 3 → R} (hx : x ≠ 0) :
    (fun i ↦ (addSubMap W i).eval x) ≠ 0 := by
  contrapose! hx
  ext i
  simpa [congrFun hx] using (addSubMapCoeff_condition W x i).symm

end WeierstrassCurve

/-!
### The symmetric square of the x-coordinate map

We define `Weierstrass.Affine.Point.sym2x`, which sends a pair `P`, `Q` of nonsingular points in
affine coordinates on a Weierstrass curve to a triple projectively equal to
`(x(P)*x(Q), x(P)+x(Q), 1)`, and provide some API.
-/

namespace WeierstrassCurve.Affine.Point

variable {R : Type*} [CommRing R] {W' : Affine R}

/-- This map sends a pair `P`, `Q` of nonsingular points in affine coordinates on `W`
to a triple projectively equivalent to `![x(P) * x(Q), x(P) + x(Q), 1]`.

In more geometric terms, this is the map `Sym² W → Sym² ℙ¹ ≃ ℙ²` induced by `x : W → ℙ¹`. -/
/-
**WeierstrassCurve.Affine.Point.sym2x** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurv
e.Affine.Point`。
形式化陈述：sym2x (P Q : W'.Point) : Fin 3 -> R
参数：P Q : W'.Point。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This map sends a pair `P`, `Q` of nonsingular points in affine coordinates on `W
`
to a triple projectively equivalent to `![x(P) * x(Q), x(P) + x(Q), 1]`.

In more geometric terms, this is the map `Sym² W → Sym² ℙ¹ ≃ ℙ²` induced by `x :
 W → ℙ¹`.
-/
noncomputable def sym2x (P Q : W'.Point) : Fin 3 → R :=
  letI Px := P.xRep
  letI Qx := Q.xRep
  ![Px 0 * Qx 0, Px 0 * Qx 1 + Px 1 * Qx 0, Px 1 * Qx 1]

@[simp]
/-
**WeierstrassCurve.Affine.Point.sym2x_zero_zero** 是 Mathlib 中的一个引理，位于命名空间 `Weier
strassCurve.Affine.Point`。
形式化陈述：sym2x_zero_zero : (0 : W'.Point).sym2x 0 = ![1, 0, 0]
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
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sym2x_zero_zero : (0 : W'.Point).sym2x 0 = ![1, 0, 0] := by
  simp [sym2x]

@[simp]
/-
**WeierstrassCurve.Affine.Point.sym2x_zero_some** 是 Mathlib 中的一个引理，位于命名空间 `Weier
strassCurve.Affine.Point`。
形式化陈述：sym2x_zero_some {x y : R} (h : W'.Nonsingular x y) : (0 : W'.Point).sym2x 
(some x y h) = ![x, 1, 0]
参数：h : W'.Nonsingular x y。
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
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sym2x_zero_some {x y : R} (h : W'.Nonsingular x y) :
    (0 : W'.Point).sym2x (some x y h) = ![x, 1, 0] := by
  simp [sym2x]

@[simp]
/-
**WeierstrassCurve.Affine.Point.sym2x_some_zero** 是 Mathlib 中的一个引理，位于命名空间 `Weier
strassCurve.Affine.Point`。
形式化陈述：sym2x_some_zero {x y : R} (h : W'.Nonsingular x y) : (some x y h).sym2x 0 
= ![x, 1, 0]
参数：h : W'.Nonsingular x y。
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
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sym2x_some_zero {x y : R} (h : W'.Nonsingular x y) :
    (some x y h).sym2x 0 = ![x, 1, 0] := by
  simp [sym2x]

@[simp]
/-
**WeierstrassCurve.Affine.Point.sym2x_some_some** 是 Mathlib 中的一个引理，位于命名空间 `Weier
strassCurve.Affine.Point`。
形式化陈述：sym2x_some_some {x y x' y' : R} (h : W'.Nonsingular x y) (h' : W'.Nonsingu
lar x' y') : (some x y h).sym2x (some x' y' h') = ![x * x', x + x', 1]
参数：h : W'.Nonsingular x y；h' : W'.Nonsingular x' y'。
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
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sym2x_some_some {x y x' y' : R} (h : W'.Nonsingular x y) (h' : W'.Nonsingular x' y') :
    (some x y h).sym2x (some x' y' h') = ![x * x', x + x', 1] := by
  simp [sym2x]
/-
**WeierstrassCurve.Affine.Point.sym2x_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Weierst
rassCurve.Affine.Point`。
形式化陈述：sym2x_ne_zero [Nontrivial R] (P Q : W'.Point) : P.sym2x Q != 0
参数：P Q : W'.Point。
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
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.zero_empty`：∀ {α : Type u_1} [inst : Zero α], 0 = ![]
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
lemma sym2x_ne_zero [Nontrivial R] (P Q : W'.Point) : P.sym2x Q ≠ 0 := by
  cases P <;> cases Q <;> simp [sym2x, xRep]
/-
**WeierstrassCurve.Affine.Point.sym2x_comm** 是 Mathlib 中的一个引理，位于命名空间 `Weierstras
sCurve.Affine.Point`。
形式化陈述：sym2x_comm (P Q : W'.Point) : P.sym2x Q = Q.sym2x P
参数：P Q : W'.Point。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Affine.Point.sym2x_zero_zero`：sym2x_zero_zero : (0 : W'
.Point).sym2x 0 = ![1, 0, 0]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WeierstrassCurve.Affine.Point.sym2x_zero_some`：sym2x_zero_some {x y : R}
 (h : W'.Nonsingular x y) : (0 : W'.Point).sym2x (some x y h) = ![x, 1, 0]
· 使用引理 `WeierstrassCurve.Affine.Point.sym2x_some_zero`：sym2x_some_zero {x y : R}
 (h : W'.Nonsingular x y) : (some x y h).sym2x 0 = ![x, 1, 0]
· 使用引理 `WeierstrassCurve.Affine.Point.sym2x_some_some`：sym2x_some_some {x y x' y
' : R} (h : W'.Nonsingular x y) (h' : W'.Nonsingular x' y') : (some x y h).sym2x
 (some x' y' h') = ![x * x', x + x'…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
lemma sym2x_comm (P Q : W'.Point) : P.sym2x Q = Q.sym2x P := by
  cases P <;> cases Q <;> simp [← zero_def, mul_comm, add_comm]
/-
**WeierstrassCurve.Affine.Point.sym2x_neg_left** 是 Mathlib 中的一个引理，位于命名空间 `Weiers
trassCurve.Affine.Point`。
形式化陈述：sym2x_neg_left (P Q : W'.Point) : (-P).sym2x Q = P.sym2x Q
参数：P Q : W'.Point。
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
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `WeierstrassCurve.Affine.Point.xRep_neg`：xRep_neg (P : W'.Point) : (-P).x
Rep = P.xRep
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sym2x_neg_left (P Q : W'.Point) : (-P).sym2x Q = P.sym2x Q := by
  simp [sym2x]
/-
**WeierstrassCurve.Affine.Point.sym2x_neg_right** 是 Mathlib 中的一个引理，位于命名空间 `Weier
strassCurve.Affine.Point`。
形式化陈述：sym2x_neg_right (P Q : W'.Point) : P.sym2x (-Q) = P.sym2x Q
参数：P Q : W'.Point。
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
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `WeierstrassCurve.Affine.Point.xRep_neg`：xRep_neg (P : W'.Point) : (-P).x
Rep = P.xRep
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sym2x_neg_right (P Q : W'.Point) : P.sym2x (-Q) = P.sym2x Q := by
  simp [sym2x]

end WeierstrassCurve.Affine.Point

end

