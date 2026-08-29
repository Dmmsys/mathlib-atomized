/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.RatFunc.Defs
public import Mathlib.RingTheory.Algebraic.Integral

/-!
# The field structure of rational functions

## Main definitions
Working with rational functions as polynomials:
- `RatFunc.instField` provides a field structure

You can use `IsFractionRing` API to treat `RatFunc` as the field of fractions of polynomials:
* `algebraMap K[X] K⟮X⟯` maps polynomials to rational functions
* `IsFractionRing.algEquiv` maps other fields of fractions of `K[X]` to `K⟮X⟯`.

In particular:
* `FractionRing.algEquiv K[X] K⟮X⟯` maps the generic field of
  fraction construction to `K⟮X⟯`. Combine this with `AlgEquiv.restrictScalars` to change
  the `FractionRing K[X] ≃ₐ[K[X]] K⟮X⟯` to `FractionRing K[X] ≃ₐ[K] K⟮X⟯`.

Working with rational functions as fractions:
- `RatFunc.num` and `RatFunc.denom` give the numerator and denominator.
  These values are chosen to be coprime and such that `RatFunc.denom` is monic.

Lifting homomorphisms of polynomials to other types, by mapping and dividing, as long
as the homomorphism retains the non-zero-divisor property:
- `RatFunc.liftMonoidWithZeroHom` lifts a `K[X] →*₀ G₀` to
  a `K⟮X⟯ →*₀ G₀`, where `[CommRing K] [CommGroupWithZero G₀]`
- `RatFunc.liftRingHom` lifts a `K[X] →+* L` to a `K⟮X⟯ →+* L`,
  where `[CommRing K] [Field L]`
- `RatFunc.liftAlgHom` lifts a `K[X] →ₐ[S] L` to a `K⟮X⟯ →ₐ[S] L`,
  where `[CommRing K] [Field L] [CommSemiring S] [Algebra S K[X]] [Algebra S L]`

This is satisfied by injective homs.

We also have lifting homomorphisms of polynomials to other polynomials,
with the same condition on retaining the non-zero-divisor property across the map:
- `RatFunc.map` lifts `K[X] →* R[X]` when `[CommRing K] [CommRing R]`
- `RatFunc.mapRingHom` lifts `K[X] →+* R[X]` when `[CommRing K] [CommRing R]`
- `RatFunc.mapAlgHom` lifts `K[X] →ₐ[S] R[X]` when
  `[CommRing K] [IsDomain K] [CommRing R] [IsDomain R]`
-/

@[expose] public section

universe u v

noncomputable section

open scoped nonZeroDivisors Polynomial

variable {K : Type u}

namespace RatFunc

section Field

variable [CommRing K]

/-- The zero rational function. -/
protected irreducible_def zero : K⟮X⟯ :=
  ⟨0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero K⟮X⟯
  body: ⟨RatFunc.zero⟩

中文:
实例 :
  签名: 零 K⟮X⟯
  定义体: ⟨RatFunc.zero⟩

Depends on / 依赖: RatFunc, RatFunc.zero
-/
instance : Zero K⟮X⟯ :=
  ⟨RatFunc.zero⟩

/--
theorem `ofFractionRing_zero` / 定理 `ofFractionRing_zero`

English:
theorem ofFractionRing_zero
  statement: (ofFractionRing 0 : K⟮X⟯) = 0
  proof: zero_def.symm

中文:
定理 ofFractionRing_zero
  结论: (ofFractionRing 0 : K⟮X⟯) = 0
  证明: zero_def.symm

Depends on / 依赖: zero_def, zero_def.symm
-/
theorem ofFractionRing_zero : (ofFractionRing 0 : K⟮X⟯) = 0 :=
  zero_def.symm

/-- Addition of rational functions. -/
protected irreducible_def add : K⟮X⟯ -> K⟮X⟯ -> K⟮X⟯
  | ⟨p⟩, ⟨q⟩ => ⟨p + q⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add K⟮X⟯
  body: ⟨RatFunc.add⟩

中文:
实例 :
  签名: 加法 K⟮X⟯
  定义体: ⟨RatFunc.add⟩

Depends on / 依赖: RatFunc, RatFunc.add
-/
instance : Add K⟮X⟯ :=
  ⟨RatFunc.add⟩

/--
theorem `ofFractionRing_add` / 定理 `ofFractionRing_add`

English:
theorem ofFractionRing_add
  given: (p q : FractionRing K[X])
  proof: (add_def _ _).symm

中文:
定理 ofFractionRing_add
  条件: (p q : FractionRing K[X])
  证明: (add_def _ _).symm

Depends on / 依赖: add_def
-/
theorem ofFractionRing_add (p q : FractionRing K[X]) :
    ofFractionRing (p + q) = ofFractionRing p + ofFractionRing q :=
  (add_def _ _).symm

/-- Subtraction of rational functions. -/
protected irreducible_def sub : K⟮X⟯ -> K⟮X⟯ -> K⟮X⟯
  | ⟨p⟩, ⟨q⟩ => ⟨p - q⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub K⟮X⟯
  body: ⟨RatFunc.sub⟩

中文:
实例 :
  签名: 减法 K⟮X⟯
  定义体: ⟨RatFunc.sub⟩

Depends on / 依赖: RatFunc, RatFunc.sub
-/
instance : Sub K⟮X⟯ :=
  ⟨RatFunc.sub⟩

/--
theorem `ofFractionRing_sub` / 定理 `ofFractionRing_sub`

English:
theorem ofFractionRing_sub
  given: (p q : FractionRing K[X])
  proof: (sub_def _ _).symm

中文:
定理 ofFractionRing_sub
  条件: (p q : FractionRing K[X])
  证明: (sub_def _ _).symm

Depends on / 依赖: sub_def
-/
theorem ofFractionRing_sub (p q : FractionRing K[X]) :
    ofFractionRing (p - q) = ofFractionRing p - ofFractionRing q :=
  (sub_def _ _).symm

/-- Additive inverse of a rational function. -/
protected irreducible_def neg : K⟮X⟯ -> K⟮X⟯
  | ⟨p⟩ => ⟨-p⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg K⟮X⟯
  body: ⟨RatFunc.neg⟩

中文:
实例 :
  签名: 取负 K⟮X⟯
  定义体: ⟨RatFunc.neg⟩

Depends on / 依赖: RatFunc, RatFunc.neg
-/
instance : Neg K⟮X⟯ :=
  ⟨RatFunc.neg⟩

/--
theorem `ofFractionRing_neg` / 定理 `ofFractionRing_neg`

English:
theorem ofFractionRing_neg
  given: (p : FractionRing K[X])
  proof: (neg_def _).symm

中文:
定理 ofFractionRing_neg
  条件: (p : FractionRing K[X])
  证明: (neg_def _).symm

Depends on / 依赖: neg_def
-/
theorem ofFractionRing_neg (p : FractionRing K[X]) :
    ofFractionRing (-p) = -ofFractionRing p :=
  (neg_def _).symm

/-- The multiplicative unit of rational functions. -/
protected irreducible_def one : K⟮X⟯ :=
  ⟨1⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One K⟮X⟯
  body: ⟨RatFunc.one⟩

中文:
实例 :
  签名: 幺 K⟮X⟯
  定义体: ⟨RatFunc.one⟩

Depends on / 依赖: RatFunc, RatFunc.one
-/
instance : One K⟮X⟯ :=
  ⟨RatFunc.one⟩

/--
theorem `ofFractionRing_one` / 定理 `ofFractionRing_one`

English:
theorem ofFractionRing_one
  statement: (ofFractionRing 1 : K⟮X⟯) = 1
  proof: one_def.symm

中文:
定理 ofFractionRing_one
  结论: (ofFractionRing 1 : K⟮X⟯) = 1
  证明: one_def.symm

Depends on / 依赖: one_def, one_def.symm
-/
theorem ofFractionRing_one : (ofFractionRing 1 : K⟮X⟯) = 1 :=
  one_def.symm

/-- Multiplication of rational functions. -/
protected irreducible_def mul : K⟮X⟯ -> K⟮X⟯ -> K⟮X⟯
  | ⟨p⟩, ⟨q⟩ => ⟨p * q⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul K⟮X⟯
  body: ⟨RatFunc.mul⟩

中文:
实例 :
  签名: 乘法 K⟮X⟯
  定义体: ⟨RatFunc.mul⟩

Depends on / 依赖: RatFunc, RatFunc.mul
-/
instance : Mul K⟮X⟯ :=
  ⟨RatFunc.mul⟩

/--
theorem `ofFractionRing_mul` / 定理 `ofFractionRing_mul`

English:
theorem ofFractionRing_mul
  given: (p q : FractionRing K[X])
  proof: (mul_def _ _).symm

中文:
定理 ofFractionRing_mul
  条件: (p q : FractionRing K[X])
  证明: (mul_def _ _).symm

Depends on / 依赖: mul_def
-/
theorem ofFractionRing_mul (p q : FractionRing K[X]) :
    ofFractionRing (p * q) = ofFractionRing p * ofFractionRing q :=
  (mul_def _ _).symm

section IsDomain

variable [IsDomain K]

/-- Division of rational functions. -/
protected irreducible_def div : K⟮X⟯ -> K⟮X⟯ -> K⟮X⟯
  | ⟨p⟩, ⟨q⟩ => ⟨p / q⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Div K⟮X⟯
  body: ⟨RatFunc.div⟩

中文:
实例 :
  签名: 除法 K⟮X⟯
  定义体: ⟨RatFunc.div⟩

Depends on / 依赖: RatFunc, RatFunc.div
-/
instance : Div K⟮X⟯ :=
  ⟨RatFunc.div⟩

/--
theorem `ofFractionRing_div` / 定理 `ofFractionRing_div`

English:
theorem ofFractionRing_div
  given: (p q : FractionRing K[X])
  proof: (div_def _ _).symm

中文:
定理 ofFractionRing_div
  条件: (p q : FractionRing K[X])
  证明: (div_def _ _).symm

Depends on / 依赖: div_def
-/
theorem ofFractionRing_div (p q : FractionRing K[X]) :
    ofFractionRing (p / q) = ofFractionRing p / ofFractionRing q :=
  (div_def _ _).symm

/-- Multiplicative inverse of a rational function. -/
protected irreducible_def inv : K⟮X⟯ -> K⟮X⟯
  | ⟨p⟩ => ⟨p⁻¹⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inv K⟮X⟯
  body: ⟨RatFunc.inv⟩

中文:
实例 :
  签名: 取逆 K⟮X⟯
  定义体: ⟨RatFunc.inv⟩

Depends on / 依赖: RatFunc, RatFunc.inv
-/
instance : Inv K⟮X⟯ :=
  ⟨RatFunc.inv⟩

/--
theorem `ofFractionRing_inv` / 定理 `ofFractionRing_inv`

English:
theorem ofFractionRing_inv
  given: (p : FractionRing K[X])
  proof: (inv_def _).symm

中文:
定理 ofFractionRing_inv
  条件: (p : FractionRing K[X])
  证明: (inv_def _).symm

Depends on / 依赖: inv_def
-/
theorem ofFractionRing_inv (p : FractionRing K[X]) :
    ofFractionRing p⁻¹ = (ofFractionRing p)⁻¹ :=
  (inv_def _).symm

-- Auxiliary lemma for the `Field` instance
/--
theorem `mul_inv_cancel` / 定理 `mul_inv_cancel`

English:
theorem mul_inv_cancel
  statement: forall {p : K⟮X⟯}, p != 0 -> p * p⁻¹ = 1
  proof: fun hp => h by rw [hp, ofFractionRing_zero]
    simpa only [← ofFractionRing_inv, ← ofFractionRing_mul, ← ofFractionRing_one,
        ofFractionRing.injEq] using
      mul_inv_cancel₀ this

中文:
定理 mul_inv_cancel
  结论: 对任意 {p : K⟮X⟯}, p != 0 -> p * p⁻¹ = 1
  证明: fun hp => h by rw [hp, ofFractionRing_zero]
    simpa only [← ofFractionRing_inv, ← ofFractionRing_mul, ← ofFractionRing_one,
        ofFractionRing.injEq] using
      mul_inv_cancel₀ this

Depends on / 依赖: ofFractionRing_zero
-/
theorem mul_inv_cancel : forall {p : K⟮X⟯}, p != 0 -> p * p⁻¹ = 1
  | ⟨p⟩, h => by
have : p != 0 := fun hp => h by rw [hp, ofFractionRing_zero]
    simpa only [← ofFractionRing_inv, ← ofFractionRing_mul, ← ofFractionRing_one,
        ofFractionRing.injEq] using
      mul_inv_cancel₀ this

end IsDomain

section SMul

variable {R : Type*}

/-- Scalar multiplication of rational functions. -/
protected irreducible_def smul [SMul R (FractionRing K[X])] : R -> K⟮X⟯ -> K⟮X⟯
  | r, ⟨p⟩ => ⟨r • p⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: R (FractionRing K[X])] : SMul R K⟮X⟯
  body: ⟨RatFunc.smul⟩

中文:
实例 [标量乘法
  签名: R (FractionRing K[X])] : 标量乘法 R K⟮X⟯
  定义体: ⟨RatFunc.smul⟩

Depends on / 依赖: RatFunc, RatFunc.smul
-/
instance [SMul R (FractionRing K[X])] : SMul R K⟮X⟯ :=
  ⟨RatFunc.smul⟩

/--
theorem `ofFractionRing_smul` / 定理 `ofFractionRing_smul`

English:
theorem ofFractionRing_smul
  given: [SMul R (FractionRing K[X])] (c : R) (p : FractionRing K[X])
  proof: (smul_def _ _).symm

中文:
定理 ofFractionRing_smul
  条件: [标量乘法 R (FractionRing K[X])] (c : R) (p : FractionRing K[X])
  证明: (smul_def _ _).symm

Depends on / 依赖: smul_def
-/
theorem ofFractionRing_smul [SMul R (FractionRing K[X])] (c : R) (p : FractionRing K[X]) :
    ofFractionRing (c • p) = c • ofFractionRing p :=
  (smul_def _ _).symm

/--
theorem `toFractionRing_smul` / 定理 `toFractionRing_smul`

English:
theorem toFractionRing_smul
  given: [SMul R (FractionRing K[X])] (c : R) (p : K⟮X⟯)
  proof: by
  cases p
  rw [← ofFractionRing_smul]

中文:
定理 toFractionRing_smul
  条件: [标量乘法 R (FractionRing K[X])] (c : R) (p : K⟮X⟯)
  证明: by
  cases p
  rw [← ofFractionRing_smul]

Depends on / 依赖: ofFractionRing_smul
-/
theorem toFractionRing_smul [SMul R (FractionRing K[X])] (c : R) (p : K⟮X⟯) :
    toFractionRing (c • p) = c • toFractionRing p := by
  cases p
  rw [← ofFractionRing_smul]

/--
theorem `smul_eq_C_smul` / 定理 `smul_eq_C_smul`

English:
theorem smul_eq_C_smul
  given: (x : K⟮X⟯) (r : K)
  statement: r • x = Polynomial.C r • x
  proof: by
  obtain ⟨x⟩ := x
  induction x using Localization.induction_on
  rw [← ofFractionRing_smul]; rw [← ofFractionRing_smul]; rw [Localization.smul_mk]; rw [Localization.smul_mk]; rw [smul_eq_mul]; rw [Polynomial.smul_eq_C_mul]

中文:
定理 smul_eq_C_smul
  条件: (x : K⟮X⟯) (r : K)
  结论: r • x = 多项式.C r • x
  证明: by
  obtain ⟨x⟩ := x
  induction x using Localization.induction_on
  rw [← ofFractionRing_smul]; rw [← ofFractionRing_smul]; rw [Localization.smul_mk]; rw [Localization.smul_mk]; rw [smul_eq_mul]; rw [Polynomial.smul_eq_C_mul]

Depends on / 依赖: Localization, Localization.induction_on, Localization.smul_mk, Polynomial, Polynomial.smul_eq_C_mul, induction_on, ofFractionRing_smul, smul_eq_C_mul, smul_eq_mul, smul_mk
-/
theorem smul_eq_C_smul (x : K⟮X⟯) (r : K) : r • x = Polynomial.C r • x := by
  obtain ⟨x⟩ := x
  induction x using Localization.induction_on
  rw [← ofFractionRing_smul]; rw [← ofFractionRing_smul]; rw [Localization.smul_mk]; rw [Localization.smul_mk]; rw [smul_eq_mul]; rw [Polynomial.smul_eq_C_mul]

section IsDomain

variable [IsDomain K]
variable [Monoid R] [DistribMulAction R K[X]]
variable [IsScalarTower R K[X] K[X]]

/--
theorem `mk_smul` / 定理 `mk_smul`

English:
theorem mk_smul
  given: (c : R) (p q : K[X])
  statement: RatFunc.mk (c • p) q = c • RatFunc.mk p q
  proof: by
  let : SMulZeroClass R (FractionRing K[X]) := inferInstance
  by_cases hq : q = 0
  · rw [hq, mk_zero, mk_zero, ← ofFractionRing_smul, smul_zero]
  · rw [mk_eq_localization_mk _ hq, mk_eq_localization_mk _ hq, ← Localization.smul_mk, ←
      ofFractionRing_smul]

中文:
定理 mk_smul
  条件: (c : R) (p q : K[X])
  结论: 有理函数.mk (c • p) q = c • 有理函数.mk p q
  证明: by
  let : SMulZeroClass R (FractionRing K[X]) := inferInstance
  by_cases hq : q = 0
  · rw [hq, mk_zero, mk_zero, ← ofFractionRing_smul, smul_zero]
  · rw [mk_eq_localization_mk _ hq, mk_eq_localization_mk _ hq, ← Localization.smul_mk, ←
      ofFractionRing_smul]

Depends on / 依赖: FractionRing, Localization, Localization.smul_mk, SMulZeroClass, mk_eq_localization_mk, mk_zero, ofFractionRing_smul, smul_mk, smul_zero
-/
theorem mk_smul (c : R) (p q : K[X]) : RatFunc.mk (c • p) q = c • RatFunc.mk p q := by
  let : SMulZeroClass R (FractionRing K[X]) := inferInstance
  by_cases hq : q = 0
  · rw [hq, mk_zero, mk_zero, ← ofFractionRing_smul, smul_zero]
  · rw [mk_eq_localization_mk _ hq, mk_eq_localization_mk _ hq, ← Localization.smul_mk, ←
      ofFractionRing_smul]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower R K[X] K⟮X⟯
  body: ⟨fun c p q => q.induction_on' fun q r _ => by rw [← mk_smul, smul_assoc, mk_smul, mk_smul]⟩

中文:
实例 :
  签名: 标量塔 R K[X] K⟮X⟯
  定义体: ⟨fun c p q => q.induction_on' fun q r _ => by rw [← mk_smul, smul_assoc, mk_smul, mk_smul]⟩

Depends on / 依赖: induction_on, mk_smul, q.induction_on, smul_assoc
-/
instance : IsScalarTower R K[X] K⟮X⟯ :=
  ⟨fun c p q => q.induction_on' fun q r _ => by rw [← mk_smul, smul_assoc, mk_smul, mk_smul]⟩

end IsDomain

end SMul

variable (K)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: K] : Subsingleton K⟮X⟯
  body: toFractionRing_injective.subsingleton

中文:
实例 [子单例
  签名: K] : 子单例 K⟮X⟯
  定义体: toFractionRing_injective.subsingleton

Depends on / 依赖: subsingleton, toFractionRing_injective, toFractionRing_injective.subsingleton
-/
instance [Subsingleton K] : Subsingleton K⟮X⟯ :=
  toFractionRing_injective.subsingleton

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited K⟮X⟯
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 K⟮X⟯
  定义体: ⟨0⟩
-/
instance : Inhabited K⟮X⟯ :=
  ⟨0⟩

/--
Instance `instNontrivial` / 实例 `instNontrivial`

English:
instance instNontrivial
  signature: [Nontrivial K]
  body: ofFractionRing_injective.nontrivial

中文:
实例 instNontrivial
  签名: [非平凡 K]
  定义体: ofFractionRing_injective.nontrivial

Depends on / 依赖: nontrivial, ofFractionRing_injective, ofFractionRing_injective.nontrivial
-/
instance instNontrivial [Nontrivial K] : Nontrivial K⟮X⟯ :=
  ofFractionRing_injective.nontrivial

/-- `K⟮X⟯` is isomorphic to the field of fractions of `K[X]`, as rings.

This is an auxiliary definition; `simp`-normal form is `IsLocalization.algEquiv`.
-/
@[simps apply]
/--
Definition of `toFractionRingRingEquiv` / `toFractionRingRingEquiv` 的定义

English:
definition toFractionRingRingEquiv
  signature: : K⟮X⟯ ≃+* FractionRing K[X] where
  body: toFractionRing
  invFun := ofFractionRing
  map_add' := fun ⟨_⟩ ⟨_⟩ => by simp [← ofFractionRing_add]
  map_mul' := fun ⟨_⟩ ⟨_⟩ => by simp [← ofFractionRing_mul]

中文:
定义 toFractionRingRingEquiv
  签名: : K⟮X⟯ ≃+* FractionRing K[X] where
  定义体: toFractionRing
  invFun := ofFractionRing
  map_add' := fun ⟨_⟩ ⟨_⟩ => by simp [← ofFractionRing_add]
  map_mul' := fun ⟨_⟩ ⟨_⟩ => by simp [← ofFractionRing_mul]

Depends on / 依赖: toFractionRing
-/
def toFractionRingRingEquiv : K⟮X⟯ ≃+* FractionRing K[X] where
  toFun := toFractionRing
  invFun := ofFractionRing
  map_add' := fun ⟨_⟩ ⟨_⟩ => by simp [← ofFractionRing_add]
  map_mul' := fun ⟨_⟩ ⟨_⟩ => by simp [← ofFractionRing_mul]

end Field

section TacticInterlude

/-- Solve equations for `K⟮X⟯` by working in `FractionRing K[X]`. -/
macro "frac_tac" : tactic => `(tactic|
  · repeat (rintro (⟨⟩ : _⟮X⟯))
    try simp only [← ofFractionRing_zero, ← ofFractionRing_add, ← ofFractionRing_sub,
      ← ofFractionRing_neg, ← ofFractionRing_one, ← ofFractionRing_mul, ← ofFractionRing_div,
      ← ofFractionRing_inv,
      add_assoc, zero_add, add_zero, mul_assoc, mul_zero, mul_one, mul_add, inv_zero,
      add_comm, add_left_comm, mul_comm, mul_left_comm, sub_eq_add_neg, div_eq_mul_inv,
      add_mul, zero_mul, one_mul, neg_mul, mul_neg, add_neg_cancel])

/-- Solve equations for `K⟮X⟯` by applying `RatFunc.induction_on`. -/
macro "smul_tac" : tactic => `(tactic|
    repeat
      (first
        | rintro (⟨⟩ : _⟮X⟯)
        | intro) <;>
    simp_rw [← ofFractionRing_smul] <;>
    simp only [add_comm, mul_comm, zero_smul, succ_nsmul, zsmul_eq_mul, mul_add, mul_one, mul_zero,
      neg_add, mul_neg,
      Int.cast_zero, Int.cast_add, Int.cast_one,
      Int.cast_negSucc, Int.cast_natCast, Nat.cast_succ,
      Localization.mk_zero, Localization.add_mk_self, Localization.neg_mk,
      ofFractionRing_zero, ← ofFractionRing_add, ← ofFractionRing_neg])

end TacticInterlude

section CommRing

variable (K) [CommRing K]
/-- `K⟮X⟯` is a commutative monoid.

This is an intermediate step on the way to the full instance `RatFunc.instCommRing`.
-/
@[instance_reducible]
/--
Definition of `instCommMonoid` / `instCommMonoid` 的定义

English:
definition instCommMonoid
  signature: : CommMonoid K⟮X⟯ where
  body: by frac_tac
  mul_comm := by frac_tac
  one_mul := by frac_tac
  mul_one := by frac_tac
  npow := npowRec

中文:
定义 instCommMonoid
  签名: : 交换幺半群 K⟮X⟯ where
  定义体: by frac_tac
  mul_comm := by frac_tac
  one_mul := by frac_tac
  mul_one := by frac_tac
  npow := npowRec

Depends on / 依赖: frac_tac, mul_comm, mul_one, npowRec, one_mul
-/
def instCommMonoid : CommMonoid K⟮X⟯ where
  mul_assoc := by frac_tac
  mul_comm := by frac_tac
  one_mul := by frac_tac
  mul_one := by frac_tac
  npow := npowRec

/-- `K⟮X⟯` is an additive commutative group.

This is an intermediate step on the way to the full instance `RatFunc.instCommRing`.
-/
@[instance_reducible]
/--
Definition of `instAddCommGroup` / `instAddCommGroup` 的定义

English:
definition instAddCommGroup
  signature: : AddCommGroup K⟮X⟯ where
  body: by frac_tac
  add_comm := by frac_tac
  zero_add := by frac_tac
  add_zero := by frac_tac
  neg_add_cancel := by frac_tac
  sub_eq_add_neg := by frac_tac
  nsmul_zero := by smul_tac
  nsmul_succ _ := by smul_tac
  zsmul_zero' := by smul_tac
  zsmul_succ' _ := by smul_tac
  zsmul_neg' _ := by smul_ta

中文:
定义 instAddCommGroup
  签名: : 加法交换群 K⟮X⟯ where
  定义体: by frac_tac
  add_comm := by frac_tac
  zero_add := by frac_tac
  add_zero := by frac_tac
  neg_add_cancel := by frac_tac
  sub_eq_add_neg := by frac_tac
  nsmul_zero := by smul_tac
  nsmul_succ _ := by smul_tac
  zsmul_zero' := by smul_tac
  zsmul_succ' _ := by smul_tac
  zsmul_neg' _ := by smul_ta

Depends on / 依赖: add_comm, add_zero, frac_tac, neg_add_cancel, nsmul_succ, nsmul_zero, smul_tac, sub_eq_add_neg, zero_add, zsmul_neg, zsmul_succ, zsmul_zero
-/
def instAddCommGroup : AddCommGroup K⟮X⟯ where
  add_assoc := by frac_tac
  add_comm := by frac_tac
  zero_add := by frac_tac
  add_zero := by frac_tac
  neg_add_cancel := by frac_tac
  sub_eq_add_neg := by frac_tac
  nsmul_zero := by smul_tac
  nsmul_succ _ := by smul_tac
  zsmul_zero' := by smul_tac
  zsmul_succ' _ := by smul_tac
  zsmul_neg' _ := by smul_tac

/--
Instance `instCommRing` / 实例 `instCommRing`

English:
instance instCommRing
  signature: : CommRing K⟮X⟯
  body: { instCommMonoid K, instAddCommGroup K with
    zero_mul := by frac_tac
    mul_zero := by frac_tac
    left_distrib := by frac_tac
    right_distrib := by frac_tac
    npow := npowRec }

中文:
实例 instCommRing
  签名: : 交换环 K⟮X⟯
  定义体: { instCommMonoid K, instAddCommGroup K with
    zero_mul := by frac_tac
    mul_zero := by frac_tac
    left_distrib := by frac_tac
    right_distrib := by frac_tac
    npow := npowRec }

Depends on / 依赖: frac_tac, instAddCommGroup, instCommMonoid, left_distrib, mul_zero, npowRec, right_distrib, zero_mul
-/
instance instCommRing : CommRing K⟮X⟯ :=
  { instCommMonoid K, instAddCommGroup K with
    zero_mul := by frac_tac
    mul_zero := by frac_tac
    left_distrib := by frac_tac
    right_distrib := by frac_tac
    npow := npowRec }

variable {K}

section LiftHom

open RatFunc

variable {G₀ L R S F : Type*} [CommGroupWithZero G₀] [Field L] [CommRing R] [CommRing S]
variable [FunLike F R[X] S[X]]

open scoped Classical in
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: [MonoidHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ <= S[X]⁰.comap φ)
  body: RatFunc.liftOn f
      (fun n d => if h : φ d in S[X]⁰ then ofFractionRing (Localization.mk (φ n) ⟨φ d, h⟩) else 0)
      fun {p q p' q'} hq hq' h => by
      simp only [Submonoid.mem_comap.mp (hφ hq), Submonoid.mem_comap.mp (hφ hq'),
        dif_pos, ofFractionRing.injEq, Localization.mk_eq_mk_iff]

中文:
定义 map
  签名: [幺半群态射类 F R[X] S[X]] (φ : F) (hφ : R[X]⁰ <= S[X]⁰.comap φ)
  定义体: RatFunc.liftOn f
      (fun n d => if h : φ d in S[X]⁰ then ofFractionRing (Localization.mk (φ n) ⟨φ d, h⟩) else 0)
      fun {p q p' q'} hq hq' h => by
      simp only [Submonoid.mem_comap.mp (hφ hq), Submonoid.mem_comap.mp (hφ hq'),
        dif_pos, ofFractionRing.injEq, Localization.mk_eq_mk_iff]

Depends on / 依赖: Localization, Localization.mk, Localization.mk_eq_mk_iff, Localization.mk_one, Localization.r_of_eq, OneMemClass, OneMemClass.coe_one, OneMemClass.one_mem, RatFunc, RatFunc.liftOn, Submonoid, Submonoid.mem_comap.mp, coe_one, congr_arg, dif_pos, dite_tr, liftOn, liftOn_ofFractionRing_mk, map_mul, map_one
-/
def map [MonoidHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ <= S[X]⁰.comap φ) :
    R⟮X⟯ ->* S⟮X⟯ where
  toFun f :=
    RatFunc.liftOn f
      (fun n d => if h : φ d in S[X]⁰ then ofFractionRing (Localization.mk (φ n) ⟨φ d, h⟩) else 0)
      fun {p q p' q'} hq hq' h => by
      simp only [Submonoid.mem_comap.mp (hφ hq), Submonoid.mem_comap.mp (hφ hq'),
        dif_pos, ofFractionRing.injEq, Localization.mk_eq_mk_iff]
      refine Localization.r_of_eq ?_
      simpa only [map_mul] using congr_arg φ h
  map_one' := by
    simp_rw [← ofFractionRing_one, ← Localization.mk_one, liftOn_ofFractionRing_mk,
      OneMemClass.coe_one, map_one, OneMemClass.one_mem, dite_true, ofFractionRing.injEq,
      Localization.mk_one, Localization.mk_eq_monoidOf_mk', Submonoid.LocalizationMap.mk'_self]
  map_mul' x y := by
    obtain ⟨x⟩ := x; obtain ⟨y⟩ := y
    cases x using Localization.induction_on with | _ pq
    cases y using Localization.induction_on with | _ p'q'
    obtain ⟨p, q⟩ := pq
    obtain ⟨p', q'⟩ := p'q'
    have hq : φ q in S[X]⁰ := hφ q.prop
    have hq' : φ q' in S[X]⁰ := hφ q'.prop
    have hqq' : φ ↑(q * q') in S[X]⁰ := by simpa using Submonoid.mul_mem _ hq hq'
    simp_rw [← ofFractionRing_mul, Localization.mk_mul, liftOn_ofFractionRing_mk, dif_pos hq,
      dif_pos hq', dif_pos hqq', ← ofFractionRing_mul, Submonoid.coe_mul, map_mul,
      Localization.mk_mul, Submonoid.mk_mul_mk]

/--
theorem `map_apply_ofFractionRing_mk` / 定理 `map_apply_ofFractionRing_mk`

English:
theorem map_apply_ofFractionRing_mk
  statement: [MonoidHomClass F R[X] S[X]] (φ : F)
  proof: by
  simp only [map, MonoidHom.coe_mk, OneHom.coe_mk, liftOn_ofFractionRing_mk,
    Submonoid.mem_comap.mp (hφ d.2), ↓reduceDIte]

中文:
定理 map_apply_ofFractionRing_mk
  结论: [幺半群态射类 F R[X] S[X]] (φ : F)
  证明: by
  simp only [map, MonoidHom.coe_mk, OneHom.coe_mk, liftOn_ofFractionRing_mk,
    Submonoid.mem_comap.mp (hφ d.2), ↓reduceDIte]

Depends on / 依赖: MonoidHom, MonoidHom.coe_mk, OneHom, OneHom.coe_mk, Submonoid, Submonoid.mem_comap.mp, coe_mk, liftOn_ofFractionRing_mk, mem_comap, reduceDIte
-/
theorem map_apply_ofFractionRing_mk [MonoidHomClass F R[X] S[X]] (φ : F)
    (hφ : R[X]⁰ <= S[X]⁰.comap φ) (n : R[X]) (d : R[X]⁰) :
    map φ hφ (ofFractionRing (Localization.mk n d)) =
      ofFractionRing (Localization.mk (φ n) ⟨φ d, hφ d.prop⟩) := by
  simp only [map, MonoidHom.coe_mk, OneHom.coe_mk, liftOn_ofFractionRing_mk,
    Submonoid.mem_comap.mp (hφ d.2), ↓reduceDIte]

/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  statement: [MonoidHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ <= S[X]⁰.comap φ)
  proof: by
  rintro ⟨x⟩ ⟨y⟩ h
  induction x using Localization.induction_on
  induction y using Localization.induction_on
  simpa only [map_apply_ofFractionRing_mk, ofFractionRing_injective.eq_iff,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists, mul_cancel_left_coe_nonZeroDivisors,
    exists_cons

中文:
定理 map_injective
  结论: [幺半群态射类 F R[X] S[X]] (φ : F) (hφ : R[X]⁰ <= S[X]⁰.comap φ)
  证明: by
  rintro ⟨x⟩ ⟨y⟩ h
  induction x using Localization.induction_on
  induction y using Localization.induction_on
  simpa only [map_apply_ofFractionRing_mk, ofFractionRing_injective.eq_iff,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists, mul_cancel_left_coe_nonZeroDivisors,
    exists_cons

Depends on / 依赖: Localization, Localization.induction_on, Localization.mk_eq_mk_iff, Localization.r_iff_exists, eq_iff, exists_const, hf.eq_iff, induction_on, map_apply_ofFractionRing_mk, map_mul, mk_eq_mk_iff, mul_cancel_left_coe_nonZeroDivisors, ofFractionRing_injective, ofFractionRing_injective.eq_iff, r_iff_exists
-/
theorem map_injective [MonoidHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ <= S[X]⁰.comap φ)
    (hf : Function.Injective φ) : Function.Injective (map φ hφ) := by
  rintro ⟨x⟩ ⟨y⟩ h
  induction x using Localization.induction_on
  induction y using Localization.induction_on
  simpa only [map_apply_ofFractionRing_mk, ofFractionRing_injective.eq_iff,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists, mul_cancel_left_coe_nonZeroDivisors,
    exists_const, ← map_mul, hf.eq_iff] using h

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `mapRingHom` / `mapRingHom` 的定义

English:
definition mapRingHom
  signature: [RingHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ <= S[X]⁰.comap φ)
  body: { map φ hφ with
    map_zero' := by
      simp_rw [MonoidHom.toFun_eq_coe, ← ofFractionRing_zero, ← Localization.mk_zero (1 : R[X]⁰),
        ← Localization.mk_zero (1 : S[X]⁰), map_apply_ofFractionRing_mk, map_zero,
        Localization.mk_eq_mk', IsLocalization.mk'_zero]
    map_add' := by
      r

中文:
定义 mapRingHom
  签名: [环态射类 F R[X] S[X]] (φ : F) (hφ : R[X]⁰ <= S[X]⁰.comap φ)
  定义体: { map φ hφ with
    map_zero' := by
      simp_rw [MonoidHom.toFun_eq_coe, ← ofFractionRing_zero, ← Localization.mk_zero (1 : R[X]⁰),
        ← Localization.mk_zero (1 : S[X]⁰), map_apply_ofFractionRing_mk, map_zero,
        Localization.mk_eq_mk', IsLocalization.mk'_zero]
    map_add' := by
      r

Depends on / 依赖: IsLocalization, IsLocalization.mk, Localization, Localization.add_mk, Localization.induction_on, Localization.mk_eq_mk, Localization.mk_zero, MonoidHom, MonoidHom.toFun_eq_coe, Submono, _zero, add_mk, induction_on, map_add, map_apply_ofFractionRing_mk, map_mul, map_zero, mk_eq_mk, mk_zero, ofFractionRing_add
-/
def mapRingHom [RingHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ <= S[X]⁰.comap φ) :
    R⟮X⟯ ->+* S⟮X⟯ :=
  { map φ hφ with
    map_zero' := by
      simp_rw [MonoidHom.toFun_eq_coe, ← ofFractionRing_zero, ← Localization.mk_zero (1 : R[X]⁰),
        ← Localization.mk_zero (1 : S[X]⁰), map_apply_ofFractionRing_mk, map_zero,
        Localization.mk_eq_mk', IsLocalization.mk'_zero]
    map_add' := by
      rintro ⟨x⟩ ⟨y⟩
      induction x using Localization.induction_on
      induction y using Localization.induction_on
      · simp only [← ofFractionRing_add, Localization.add_mk, map_add, map_mul,
          MonoidHom.toFun_eq_coe, map_apply_ofFractionRing_mk, Submonoid.coe_mul,
          -- We have to specify `S[X]⁰` to `mk_mul_mk`, otherwise it will try to rewrite
          -- the wrong occurrence.
          Submonoid.mk_mul_mk S[X]⁰] }

/--
theorem `coe_mapRingHom_eq_coe_map` / 定理 `coe_mapRingHom_eq_coe_map`

English:
theorem coe_mapRingHom_eq_coe_map
  given: [RingHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ <= S[X]⁰.comap φ)
  proof: rfl

中文:
定理 coe_mapRingHom_eq_coe_map
  条件: [环态射类 F R[X] S[X]] (φ : F) (hφ : R[X]⁰ <= S[X]⁰.comap φ)
  证明: rfl
-/
theorem coe_mapRingHom_eq_coe_map [RingHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ <= S[X]⁰.comap φ) :
    (mapRingHom φ hφ : R⟮X⟯ -> S⟮X⟯) = map φ hφ :=
  rfl

-- TODO: Generalize to `FunLike` classes,
/--
Definition of `liftMonoidWithZeroHom` / `liftMonoidWithZeroHom` 的定义

English:
definition liftMonoidWithZeroHom
  signature: (φ : R[X] ->*₀ G₀) (hφ : R[X]⁰ <= G₀⁰.comap φ)
  body: RatFunc.liftOn f (fun p q => φ p / φ q) fun {p q p' q'} hq hq' h => by
      cases subsingleton_or_nontrivial R
      · rw [Subsingleton.elim p q, Subsingleton.elim p' q, Subsingleton.elim q' q]
      rw [div_eq_div_iff]; rw [← map_mul]; rw [mul_comm p]; rw [h]; rw [map_mul]; rw [mul_comm] <;>
     

中文:
定义 liftMonoidWithZeroHom
  签名: (φ : R[X] ->*₀ G₀) (hφ : R[X]⁰ <= G₀⁰.comap φ)
  定义体: RatFunc.liftOn f (fun p q => φ p / φ q) fun {p q p' q'} hq hq' h => by
      cases subsingleton_or_nontrivial R
      · rw [Subsingleton.elim p q, Subsingleton.elim p' q, Subsingleton.elim q' q]
      rw [div_eq_div_iff]; rw [← map_mul]; rw [mul_comm p]; rw [h]; rw [map_mul]; rw [mul_comm] <;>
     

Depends on / 依赖: Localization, Localization.mk_one, OneMemClass, OneMemClass.coe_one, RatFunc, RatFunc.liftOn, Subsingleton, Subsingleton.elim, coe_one, div_eq_div_iff, div_one, liftOn, liftOn_ofFractionRing_mk, map_mul, map_one, mk_one, mul_comm, ne_zero, nonZeroDivisors, nonZeroDivisors.ne_zero
-/
def liftMonoidWithZeroHom (φ : R[X] ->*₀ G₀) (hφ : R[X]⁰ <= G₀⁰.comap φ) : R⟮X⟯ ->*₀ G₀ where
  toFun f :=
    RatFunc.liftOn f (fun p q => φ p / φ q) fun {p q p' q'} hq hq' h => by
      cases subsingleton_or_nontrivial R
      · rw [Subsingleton.elim p q, Subsingleton.elim p' q, Subsingleton.elim q' q]
      rw [div_eq_div_iff]; rw [← map_mul]; rw [mul_comm p]; rw [h]; rw [map_mul]; rw [mul_comm] <;>
        exact nonZeroDivisors.ne_zero (hφ ‹_›)
  map_one' := by
    simp_rw [← ofFractionRing_one, ← Localization.mk_one, liftOn_ofFractionRing_mk,
      OneMemClass.coe_one, map_one, div_one]
  map_mul' x y := by
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    cases x using Localization.induction_on
    cases y using Localization.induction_on
    rw [← ofFractionRing_mul]; rw [Localization.mk_mul]
    simp only [liftOn_ofFractionRing_mk, div_mul_div_comm, map_mul, Submonoid.coe_mul]
  map_zero' := by
    simp_rw [← ofFractionRing_zero, ← Localization.mk_zero (1 : R[X]⁰), liftOn_ofFractionRing_mk,
      map_zero, zero_div]

/--
theorem `liftMonoidWithZeroHom_apply_ofFractionRing_mk` / 定理 `liftMonoidWithZeroHom_apply_ofFractionRing_mk`

English:
theorem liftMonoidWithZeroHom_apply_ofFractionRing_mk
  statement: (φ : R[X] ->*₀ G₀) (hφ : R[X]⁰ <= G₀⁰.comap φ)
  proof: liftOn_ofFractionRing_mk _ _ _ _

中文:
定理 liftMonoidWithZeroHom_apply_ofFractionRing_mk
  结论: (φ : R[X] ->*₀ G₀) (hφ : R[X]⁰ <= G₀⁰.comap φ)
  证明: liftOn_ofFractionRing_mk _ _ _ _

Depends on / 依赖: liftOn_ofFractionRing_mk
-/
theorem liftMonoidWithZeroHom_apply_ofFractionRing_mk (φ : R[X] ->*₀ G₀) (hφ : R[X]⁰ <= G₀⁰.comap φ)
    (n : R[X]) (d : R[X]⁰) :
    liftMonoidWithZeroHom φ hφ (ofFractionRing (Localization.mk n d)) = φ n / φ d :=
  liftOn_ofFractionRing_mk _ _ _ _

/--
theorem `liftMonoidWithZeroHom_injective` / 定理 `liftMonoidWithZeroHom_injective`

English:
theorem liftMonoidWithZeroHom_injective
  statement: [Nontrivial R] (φ : R[X] ->*₀ G₀) (hφ : Function.Injective φ)
  proof: by
  rintro ⟨x⟩ ⟨y⟩
  cases x using Localization.induction_on
  cases y using Localization.induction_on with | _ a'
  simp_rw [liftMonoidWithZeroHom_apply_ofFractionRing_mk]
  intro h
  congr 1
  refine Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (M := R[X]) ?_)
  have := mul_eq_mul_of_div_e

中文:
定理 liftMonoidWithZeroHom_injective
  结论: [非平凡 R] (φ : R[X] ->*₀ G₀) (hφ : 函数.单射 φ)
  证明: by
  rintro ⟨x⟩ ⟨y⟩
  cases x using Localization.induction_on
  cases y using Localization.induction_on with | _ a'
  simp_rw [liftMonoidWithZeroHom_apply_ofFractionRing_mk]
  intro h
  congr 1
  refine Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (M := R[X]) ?_)
  have := mul_eq_mul_of_div_e

Depends on / 依赖: nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
-/
theorem liftMonoidWithZeroHom_injective [Nontrivial R] (φ : R[X] ->*₀ G₀) (hφ : Function.Injective φ)
    (hφ' : R[X]⁰ <= G₀⁰.comap φ := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hφ) :
    Function.Injective (liftMonoidWithZeroHom φ hφ') := by
  rintro ⟨x⟩ ⟨y⟩
  cases x using Localization.induction_on
  cases y using Localization.induction_on with | _ a'
  simp_rw [liftMonoidWithZeroHom_apply_ofFractionRing_mk]
  intro h
  congr 1
  refine Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (M := R[X]) ?_)
  have := mul_eq_mul_of_div_eq_div _ _ ?_ ?_ h
  · rwa [← map_mul, ← map_mul, hφ.eq_iff, mul_comm, mul_comm a'.fst] at this
  all_goals exact map_ne_zero_of_mem_nonZeroDivisors _ hφ (SetLike.coe_mem _)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `liftRingHom` / `liftRingHom` 的定义

English:
definition liftRingHom
  signature: (φ : R[X] ->+* L) (hφ : R[X]⁰ <= L⁰.comap φ)
  body: { liftMonoidWithZeroHom φ.toMonoidWithZeroHom hφ with
    map_add' := fun x y => by
      simp only [ZeroHom.toFun_eq_coe, MonoidWithZeroHom.toZeroHom_coe]
      cases subsingleton_or_nontrivial R
      · rw [Subsingleton.elim (x + y) y, Subsingleton.elim x 0, map_zero, zero_add]
      obtain ⟨x⟩ :=

中文:
定义 liftRingHom
  签名: (φ : R[X] ->+* L) (hφ : R[X]⁰ <= L⁰.comap φ)
  定义体: { liftMonoidWithZeroHom φ.toMonoidWithZeroHom hφ with
    map_add' := fun x y => by
      simp only [ZeroHom.toFun_eq_coe, MonoidWithZeroHom.toZeroHom_coe]
      cases subsingleton_or_nontrivial R
      · rw [Subsingleton.elim (x + y) y, Subsingleton.elim x 0, map_zero, zero_add]
      obtain ⟨x⟩ :=

Depends on / 依赖: Localization, Localization.add_mk, Localization.induction_on, MonoidWithZeroHom, MonoidWithZeroHom.toZeroHom_coe, Subsingleton, Subsingleton.elim, ZeroHom, ZeroHom.toFun_eq_coe, add_mk, induction_on, liftMonoidWithZeroHom, map_add, map_zero, ofFractionRing_add, subsingleton_or_nontrivial, toFun_eq_coe, toMonoidWithZeroHom, toZeroHom_coe, zero_add
-/
def liftRingHom (φ : R[X] ->+* L) (hφ : R[X]⁰ <= L⁰.comap φ) : R⟮X⟯ ->+* L :=
  { liftMonoidWithZeroHom φ.toMonoidWithZeroHom hφ with
    map_add' := fun x y => by
      simp only [ZeroHom.toFun_eq_coe, MonoidWithZeroHom.toZeroHom_coe]
      cases subsingleton_or_nontrivial R
      · rw [Subsingleton.elim (x + y) y, Subsingleton.elim x 0, map_zero, zero_add]
      obtain ⟨x⟩ := x
      obtain ⟨y⟩ := y
      cases x using Localization.induction_on with | _ pq
      cases y using Localization.induction_on with | _ p'q'
      obtain ⟨p, q⟩ := pq
      obtain ⟨p', q'⟩ := p'q'
      rw [← ofFractionRing_add]; rw [Localization.add_mk]
      simp only [RingHom.toMonoidWithZeroHom_eq_coe,
        liftMonoidWithZeroHom_apply_ofFractionRing_mk]
      rw [div_add_div]; rw [div_eq_div_iff]
      · rw [mul_comm _ p, mul_comm _ p', mul_comm _ (φ p'), add_comm]
        simp only [map_add, map_mul, Submonoid.coe_mul]
      all_goals
        try simp only [← map_mul, ← Submonoid.coe_mul]
        exact nonZeroDivisors.ne_zero (hφ (SetLike.coe_mem _)) }

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `liftRingHom_apply_ofFractionRing_mk` / 定理 `liftRingHom_apply_ofFractionRing_mk`

English:
theorem liftRingHom_apply_ofFractionRing_mk
  statement: (φ : R[X] ->+* L) (hφ : R[X]⁰ <= L⁰.comap φ) (n : R[X])
  proof: liftMonoidWithZeroHom_apply_ofFractionRing_mk _ hφ _ _

中文:
定理 liftRingHom_apply_ofFractionRing_mk
  结论: (φ : R[X] ->+* L) (hφ : R[X]⁰ <= L⁰.comap φ) (n : R[X])
  证明: liftMonoidWithZeroHom_apply_ofFractionRing_mk _ hφ _ _

Depends on / 依赖: liftMonoidWithZeroHom_apply_ofFractionRing_mk
-/
theorem liftRingHom_apply_ofFractionRing_mk (φ : R[X] ->+* L) (hφ : R[X]⁰ <= L⁰.comap φ) (n : R[X])
    (d : R[X]⁰) : liftRingHom φ hφ (ofFractionRing (Localization.mk n d)) = φ n / φ d :=
  liftMonoidWithZeroHom_apply_ofFractionRing_mk _ hφ _ _

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `liftRingHom_ofFractionRing_algebraMap` / 引理 `liftRingHom_ofFractionRing_algebraMap`

English:
lemma liftRingHom_ofFractionRing_algebraMap
  proof: by
  rw [← Localization.mk_one_eq_algebraMap]; rw [liftRingHom_apply_ofFractionRing_mk]
  simp

中文:
引理 liftRingHom_ofFractionRing_algebraMap
  证明: by
  rw [← Localization.mk_one_eq_algebraMap]; rw [liftRingHom_apply_ofFractionRing_mk]
  simp

Depends on / 依赖: Localization, Localization.mk_one_eq_algebraMap, liftRingHom_apply_ofFractionRing_mk, mk_one_eq_algebraMap
-/
lemma liftRingHom_ofFractionRing_algebraMap
    (φ : R[X] ->+* L) (hφ : R[X]⁰ <= L⁰.comap φ) (x : R[X]) :
    RatFunc.liftRingHom φ hφ (ofFractionRing <| algebraMap R[X] _ x) = φ x := by
  rw [← Localization.mk_one_eq_algebraMap]; rw [liftRingHom_apply_ofFractionRing_mk]
  simp

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `liftRingHom_injective` / 定理 `liftRingHom_injective`

English:
theorem liftRingHom_injective
  statement: [Nontrivial R] (φ : R[X] ->+* L) (hφ : Function.Injective φ)
  proof: liftMonoidWithZeroHom_injective _ hφ

中文:
定理 liftRingHom_injective
  结论: [非平凡 R] (φ : R[X] ->+* L) (hφ : 函数.单射 φ)
  证明: liftMonoidWithZeroHom_injective _ hφ

Depends on / 依赖: nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
-/
theorem liftRingHom_injective [Nontrivial R] (φ : R[X] ->+* L) (hφ : Function.Injective φ)
    (hφ' : R[X]⁰ <= L⁰.comap φ := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hφ) :
    Function.Injective (liftRingHom φ hφ') :=
  liftMonoidWithZeroHom_injective _ hφ

end LiftHom

variable (K)

@[stacks 09FK]
/--
Instance `instField` / 实例 `instField`

English:
instance instField
  signature: [IsDomain K]
  body: by frac_tac
  div_eq_mul_inv := by frac_tac
  mul_inv_cancel _ := mul_inv_cancel
  zpow := zpowRec
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

中文:
实例 instField
  签名: [是整环 K]
  定义体: by frac_tac
  div_eq_mul_inv := by frac_tac
  mul_inv_cancel _ := mul_inv_cancel
  zpow := zpowRec
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

Depends on / 依赖: div_eq_mul_inv, frac_tac, mul_inv_cancel, nnqsmul, nnqsmul_def, qsmul_def, zpowRec
-/
instance instField [IsDomain K] : Field K⟮X⟯ where
  inv_zero := by frac_tac
  div_eq_mul_inv := by frac_tac
  mul_inv_cancel _ := mul_inv_cancel
  zpow := zpowRec
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

section IsFractionRing

/-! ### `RatFunc` as field of fractions of `Polynomial` -/

section IsDomain

variable [IsDomain K]

instance (R : Type*) [CommSemiring R] [Algebra R K[X]] : Algebra R K⟮X⟯ where
  algebraMap :=
  { toFun x := RatFunc.mk (algebraMap _ _ x) 1
    map_add' x y := by simp only [mk_one', map_add, ofFractionRing_add]
    map_mul' x y := by simp only [mk_one', map_mul, ofFractionRing_mul]
    map_one' := by simp only [mk_one', map_one, ofFractionRing_one]
    map_zero' := by simp only [mk_one', map_zero, ofFractionRing_zero] }
  smul_def' c x := by
    induction x using RatFunc.induction_on' with | _ p q hq
    rw [RingHom.coe_mk]; rw [MonoidHom.coe_mk]; rw [OneHom.coe_mk]; rw [mk_one']; rw [← mk_smul]; rw [mk_def_of_ne (c • p) hq]; rw [mk_def_of_ne p hq]; rw [← ofFractionRing_mul]; rw [IsLocalization.mul_mk'_eq_mk'_of_mul]; rw [Algebra.smul_def]
  commutes' _ _ := mul_comm _ _

variable {K}

/-- The coercion from polynomials to rational functions, implemented as the algebra map from a
domain to its field of fractions -/
@[coe]
/--
Definition of `coePolynomial` / `coePolynomial` 的定义

English:
definition coePolynomial
  signature: (P : Polynomial K)
  body: algebraMap _ _ P

中文:
定义 coePolynomial
  签名: (P : 多项式 K)
  定义体: algebraMap _ _ P

Depends on / 依赖: algebraMap
-/
def coePolynomial (P : Polynomial K) : K⟮X⟯ := algebraMap _ _ P

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (Polynomial K) K⟮X⟯
  body: ⟨coePolynomial⟩

中文:
实例 :
  签名: Coe (多项式 K) K⟮X⟯
  定义体: ⟨coePolynomial⟩

Depends on / 依赖: coePolynomial
-/
instance : Coe (Polynomial K) K⟮X⟯ := ⟨coePolynomial⟩

/--
theorem `mk_one` / 定理 `mk_one`

English:
theorem mk_one
  given: (x : K[X])
  statement: RatFunc.mk x 1 = algebraMap _ _ x
  proof: rfl

中文:
定理 mk_one
  条件: (x : K[X])
  结论: 有理函数.mk x 1 = algebraMap _ _ x
  证明: rfl
-/
theorem mk_one (x : K[X]) : RatFunc.mk x 1 = algebraMap _ _ x :=
  rfl

/--
theorem `ofFractionRing_algebraMap` / 定理 `ofFractionRing_algebraMap`

English:
theorem ofFractionRing_algebraMap
  given: (x : K[X])
  proof: by
  rw [← mk_one]; rw [mk_one']

中文:
定理 ofFractionRing_algebraMap
  条件: (x : K[X])
  证明: by
  rw [← mk_one]; rw [mk_one']

Depends on / 依赖: mk_one
-/
theorem ofFractionRing_algebraMap (x : K[X]) :
    ofFractionRing (algebraMap _ (FractionRing K[X]) x) = algebraMap _ _ x := by
  rw [← mk_one]; rw [mk_one']

variable (K) in
/--
The equivalence between `K⟮X⟯` and the field of fractions of `K[X]`
-/
@[simps! apply]
/--
Definition of `toFractionRingAlgEquiv` / `toFractionRingAlgEquiv` 的定义

English:
definition toFractionRingAlgEquiv
  signature: (R : Type*) [CommSemiring R] [Algebra R K[X]]
  body: RatFunc.toFractionRingRingEquiv K
  commutes' r := by
    change (RatFunc.mk (algebraMap R K[X] r) 1).toFractionRing = _
    rw [mk_one']; rfl

@[simp]

中文:
定义 toFractionRingAlgEquiv
  签名: (R : 类型) [交换半环 R] [代数 R K[X]]
  定义体: RatFunc.toFractionRingRingEquiv K
  commutes' r := by
    change (RatFunc.mk (algebraMap R K[X] r) 1).toFractionRing = _
    rw [mk_one']; rfl

@[simp]

Depends on / 依赖: RatFunc, RatFunc.toFractionRingRingEquiv, toFractionRingRingEquiv
-/
def toFractionRingAlgEquiv (R : Type*) [CommSemiring R] [Algebra R K[X]] :
    K⟮X⟯ ≃ₐ[R] FractionRing K[X] where
  __ := RatFunc.toFractionRingRingEquiv K
  commutes' r := by
    change (RatFunc.mk (algebraMap R K[X] r) 1).toFractionRing = _
    rw [mk_one']; rfl

@[simp]
/--
theorem `mk_eq_div` / 定理 `mk_eq_div`

English:
theorem mk_eq_div
  given: (p q : K[X])
  statement: RatFunc.mk p q = algebraMap _ _ p / algebraMap _ _ q
  proof: by
  simp only [mk_eq_div', ofFractionRing_div, ofFractionRing_algebraMap]

@[simp]

中文:
定理 mk_eq_div
  条件: (p q : K[X])
  结论: 有理函数.mk p q = algebraMap _ _ p / algebraMap _ _ q
  证明: by
  simp only [mk_eq_div', ofFractionRing_div, ofFractionRing_algebraMap]

@[simp]

Depends on / 依赖: mk_eq_div, ofFractionRing_algebraMap, ofFractionRing_div
-/
theorem mk_eq_div (p q : K[X]) : RatFunc.mk p q = algebraMap _ _ p / algebraMap _ _ q := by
  simp only [mk_eq_div', ofFractionRing_div, ofFractionRing_algebraMap]

@[simp]
/--
theorem `div_smul` / 定理 `div_smul`

English:
theorem div_smul
  statement: {R} [Monoid R] [DistribMulAction R K[X]] [IsScalarTower R K[X] K[X]] (c : R)
  proof: by
  rw [← mk_eq_div]; rw [mk_smul]; rw [mk_eq_div]

中文:
定理 div_smul
  结论: {R} [幺半群 R] [分配乘法作用 R K[X]] [标量塔 R K[X] K[X]] (c : R)
  证明: by
  rw [← mk_eq_div]; rw [mk_smul]; rw [mk_eq_div]

Depends on / 依赖: H.symm_of_commute, mk_eq_div, mk_smul, mul_comm, symm_of_commute
-/
theorem div_smul {R} [Monoid R] [DistribMulAction R K[X]] [IsScalarTower R K[X] K[X]] (c : R)
    (p q : K[X]) :
    algebraMap _ K⟮X⟯ (c • p) / algebraMap _ _ q =
      c • (algebraMap _ _ p / algebraMap _ _ q) := by
  rw [← mk_eq_div]; rw [mk_smul]; rw [mk_eq_div]

/--
theorem `algebraMap_apply` / 定理 `algebraMap_apply`

English:
theorem algebraMap_apply
  given: {R : Type*} [CommSemiring R] [Algebra R K[X]] (x : R)
  proof: by
  rw [← mk_eq_div]
  rfl

中文:
定理 algebraMap_apply
  条件: {R : 类型} [交换半环 R] [代数 R K[X]] (x : R)
  证明: by
  rw [← mk_eq_div]
  rfl

Depends on / 依赖: mk_eq_div
-/
theorem algebraMap_apply {R : Type*} [CommSemiring R] [Algebra R K[X]] (x : R) :
    algebraMap R K⟮X⟯ x = algebraMap _ _ (algebraMap R K[X] x) / algebraMap K[X] _ 1 := by
  rw [← mk_eq_div]
  rfl

/--
theorem `map_apply_div_ne_zero` / 定理 `map_apply_div_ne_zero`

English:
theorem map_apply_div_ne_zero
  statement: {R F : Type*} [CommRing R] [IsDomain R]
  proof: by
  have hq' : φ q != 0 := nonZeroDivisors.ne_zero (hφ (mem_nonZeroDivisors_iff_ne_zero.mpr hq))
  simp only [← mk_eq_div, mk_eq_localization_mk _ hq, map_apply_ofFractionRing_mk,
    mk_eq_localization_mk _ hq']

@[simp]

中文:
定理 map_apply_div_ne_zero
  结论: {R F : 类型} [交换环 R] [是整环 R]
  证明: by
  have hq' : φ q != 0 := nonZeroDivisors.ne_zero (hφ (mem_nonZeroDivisors_iff_ne_zero.mpr hq))
  simp only [← mk_eq_div, mk_eq_localization_mk _ hq, map_apply_ofFractionRing_mk,
    mk_eq_localization_mk _ hq']

@[simp]

Depends on / 依赖: map_apply_ofFractionRing_mk, mem_nonZeroDivisors_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero.mpr, mk_eq_div, mk_eq_localization_mk, ne_zero, nonZeroDivisors, nonZeroDivisors.ne_zero
-/
theorem map_apply_div_ne_zero {R F : Type*} [CommRing R] [IsDomain R]
    [FunLike F K[X] R[X]] [MonoidHomClass F K[X] R[X]]
    (φ : F) (hφ : K[X]⁰ <= R[X]⁰.comap φ) (p q : K[X]) (hq : q != 0) :
    map φ hφ (algebraMap _ _ p / algebraMap _ _ q) =
      algebraMap _ _ (φ p) / algebraMap _ _ (φ q) := by
  have hq' : φ q != 0 := nonZeroDivisors.ne_zero (hφ (mem_nonZeroDivisors_iff_ne_zero.mpr hq))
  simp only [← mk_eq_div, mk_eq_localization_mk _ hq, map_apply_ofFractionRing_mk,
    mk_eq_localization_mk _ hq']

@[simp]
/--
theorem `map_apply_div` / 定理 `map_apply_div`

English:
theorem map_apply_div
  statement: {R F : Type*} [CommRing R] [IsDomain R]
  proof: by
  rcases eq_or_ne q 0 with (rfl | hq)
  · have : (0 : K⟮X⟯) = algebraMap K[X] _ 0 / algebraMap K[X] _ 1 := by simp
    rw [map_zero]; rw [map_zero]; rw [map_zero]; rw [div_zero]; rw [div_zero]; rw [this]; rw [map_apply_div_ne_zero]; rw [map_one]; rw [map_one]; rw [div_one]; rw [map_zero]; rw [map

中文:
定理 map_apply_div
  结论: {R F : 类型} [交换环 R] [是整环 R]
  证明: by
  rcases eq_or_ne q 0 with (rfl | hq)
  · have : (0 : K⟮X⟯) = algebraMap K[X] _ 0 / algebraMap K[X] _ 1 := by simp
    rw [map_zero]; rw [map_zero]; rw [map_zero]; rw [div_zero]; rw [div_zero]; rw [this]; rw [map_apply_div_ne_zero]; rw [map_one]; rw [map_one]; rw [div_one]; rw [map_zero]; rw [map

Depends on / 依赖: algebraMap, div_one, div_zero, eq_or_ne, map_apply_div_ne_zero, map_one, map_zero, one_ne_zero
-/
theorem map_apply_div {R F : Type*} [CommRing R] [IsDomain R]
    [FunLike F K[X] R[X]] [MonoidWithZeroHomClass F K[X] R[X]]
    (φ : F) (hφ : K[X]⁰ <= R[X]⁰.comap φ) (p q : K[X]) :
    map φ hφ (algebraMap _ _ p / algebraMap _ _ q) =
      algebraMap _ _ (φ p) / algebraMap _ _ (φ q) := by
  rcases eq_or_ne q 0 with (rfl | hq)
  · have : (0 : K⟮X⟯) = algebraMap K[X] _ 0 / algebraMap K[X] _ 1 := by simp
    rw [map_zero]; rw [map_zero]; rw [map_zero]; rw [div_zero]; rw [div_zero]; rw [this]; rw [map_apply_div_ne_zero]; rw [map_one]; rw [map_one]; rw [div_one]; rw [map_zero]; rw [map_zero]
    exact one_ne_zero
  exact map_apply_div_ne_zero _ _ _ _ hq

/--
theorem `liftMonoidWithZeroHom_apply_div` / 定理 `liftMonoidWithZeroHom_apply_div`

English:
theorem liftMonoidWithZeroHom_apply_div
  statement: {L : Type*} [CommGroupWithZero L]
  proof: by
  rcases eq_or_ne q 0 with (rfl | hq)
  · simp only [div_zero, map_zero]
  simp only [← mk_eq_div, mk_eq_localization_mk _ hq,
    liftMonoidWithZeroHom_apply_ofFractionRing_mk]

@[simp]

中文:
定理 liftMonoidWithZeroHom_apply_div
  结论: {L : 类型} [带零交换群 L]
  证明: by
  rcases eq_or_ne q 0 with (rfl | hq)
  · simp only [div_zero, map_zero]
  simp only [← mk_eq_div, mk_eq_localization_mk _ hq,
    liftMonoidWithZeroHom_apply_ofFractionRing_mk]

@[simp]

Depends on / 依赖: div_zero, eq_or_ne, liftMonoidWithZeroHom_apply_ofFractionRing_mk, map_zero, mk_eq_div, mk_eq_localization_mk
-/
theorem liftMonoidWithZeroHom_apply_div {L : Type*} [CommGroupWithZero L]
    (φ : MonoidWithZeroHom K[X] L) (hφ : K[X]⁰ <= L⁰.comap φ) (p q : K[X]) :
    liftMonoidWithZeroHom φ hφ (algebraMap _ _ p / algebraMap _ _ q) = φ p / φ q := by
  rcases eq_or_ne q 0 with (rfl | hq)
  · simp only [div_zero, map_zero]
  simp only [← mk_eq_div, mk_eq_localization_mk _ hq,
    liftMonoidWithZeroHom_apply_ofFractionRing_mk]

@[simp]
/--
theorem `liftMonoidWithZeroHom_apply_div'` / 定理 `liftMonoidWithZeroHom_apply_div'`

English:
theorem liftMonoidWithZeroHom_apply_div'
  statement: {L : Type*} [CommGroupWithZero L]
  proof: by
  rw [← map_div₀]; rw [liftMonoidWithZeroHom_apply_div]

中文:
定理 liftMonoidWithZeroHom_apply_div'
  结论: {L : 类型} [带零交换群 L]
  证明: by
  rw [← map_div₀]; rw [liftMonoidWithZeroHom_apply_div]

Depends on / 依赖: liftMonoidWithZeroHom_apply_div
-/
theorem liftMonoidWithZeroHom_apply_div' {L : Type*} [CommGroupWithZero L]
    (φ : MonoidWithZeroHom K[X] L) (hφ : K[X]⁰ <= L⁰.comap φ) (p q : K[X]) :
    liftMonoidWithZeroHom φ hφ (algebraMap _ _ p) / liftMonoidWithZeroHom φ hφ (algebraMap _ _ q) =
      φ p / φ q := by
  rw [← map_div₀]; rw [liftMonoidWithZeroHom_apply_div]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `liftRingHom_apply_div` / 定理 `liftRingHom_apply_div`

English:
theorem liftRingHom_apply_div
  statement: {L : Type*} [Field L] (φ : K[X] ->+* L) (hφ : K[X]⁰ <= L⁰.comap φ)
  proof: liftMonoidWithZeroHom_apply_div _ hφ _ _

中文:
定理 liftRingHom_apply_div
  结论: {L : 类型} [域 L] (φ : K[X] ->+* L) (hφ : K[X]⁰ <= L⁰.comap φ)
  证明: liftMonoidWithZeroHom_apply_div _ hφ _ _

Depends on / 依赖: liftMonoidWithZeroHom_apply_div
-/
theorem liftRingHom_apply_div {L : Type*} [Field L] (φ : K[X] ->+* L) (hφ : K[X]⁰ <= L⁰.comap φ)
    (p q : K[X]) : liftRingHom φ hφ (algebraMap _ _ p / algebraMap _ _ q) = φ p / φ q :=
  liftMonoidWithZeroHom_apply_div _ hφ _ _

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `liftRingHom_apply_div'` / 定理 `liftRingHom_apply_div'`

English:
theorem liftRingHom_apply_div'
  statement: {L : Type*} [Field L] (φ : K[X] ->+* L) (hφ : K[X]⁰ <= L⁰.comap φ)
  proof: liftMonoidWithZeroHom_apply_div' _ hφ _ _

中文:
定理 liftRingHom_apply_div'
  结论: {L : 类型} [域 L] (φ : K[X] ->+* L) (hφ : K[X]⁰ <= L⁰.comap φ)
  证明: liftMonoidWithZeroHom_apply_div' _ hφ _ _

Depends on / 依赖: liftMonoidWithZeroHom_apply_div
-/
theorem liftRingHom_apply_div' {L : Type*} [Field L] (φ : K[X] ->+* L) (hφ : K[X]⁰ <= L⁰.comap φ)
    (p q : K[X]) : liftRingHom φ hφ (algebraMap _ _ p) / liftRingHom φ hφ (algebraMap _ _ q) =
      φ p / φ q :=
  liftMonoidWithZeroHom_apply_div' _ hφ _ _

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `liftRingHom_algebraMap` / 引理 `liftRingHom_algebraMap`

English:
lemma liftRingHom_algebraMap
  statement: {L : Type*} [Field L] (φ : K[X] ->+* L) (hφ : K[X]⁰ <= L⁰.comap φ)
  proof: by
  simpa using liftRingHom_apply_div' φ hφ x 1

中文:
引理 liftRingHom_algebraMap
  结论: {L : 类型} [域 L] (φ : K[X] ->+* L) (hφ : K[X]⁰ <= L⁰.comap φ)
  证明: by
  simpa using liftRingHom_apply_div' φ hφ x 1

Depends on / 依赖: liftRingHom_apply_div
-/
lemma liftRingHom_algebraMap {L : Type*} [Field L] (φ : K[X] ->+* L) (hφ : K[X]⁰ <= L⁰.comap φ)
    (x : K[X]) : liftRingHom φ hφ (algebraMap K[X] _ x) = φ x := by
  simpa using liftRingHom_apply_div' φ hφ x 1

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `liftRingHom_comp_algebraMap` / 引理 `liftRingHom_comp_algebraMap`

English:
lemma liftRingHom_comp_algebraMap
  given: {L : Type*} [Field L] (φ : K[X] ->+* L) (hφ : K[X]⁰ <= L⁰.comap φ)
  proof: RingHom.ext fun _ => liftRingHom_algebraMap _ hφ _

中文:
引理 liftRingHom_comp_algebraMap
  条件: {L : 类型} [域 L] (φ : K[X] ->+* L) (hφ : K[X]⁰ <= L⁰.comap φ)
  证明: RingHom.ext fun _ => liftRingHom_algebraMap _ hφ _

Depends on / 依赖: RingHom, RingHom.ext, liftRingHom_algebraMap
-/
lemma liftRingHom_comp_algebraMap {L : Type*} [Field L] (φ : K[X] ->+* L) (hφ : K[X]⁰ <= L⁰.comap φ) :
    (liftRingHom φ hφ).comp (algebraMap K[X] _) = φ :=
  RingHom.ext fun _ => liftRingHom_algebraMap _ hφ _

variable (K)

/--
theorem `ofFractionRing_comp_algebraMap` / 定理 `ofFractionRing_comp_algebraMap`

English:
theorem ofFractionRing_comp_algebraMap
  proof: funext ofFractionRing_algebraMap

中文:
定理 ofFractionRing_comp_algebraMap
  证明: funext ofFractionRing_algebraMap

Depends on / 依赖: ofFractionRing_algebraMap
-/
theorem ofFractionRing_comp_algebraMap :
    ofFractionRing ∘ algebraMap K[X] (FractionRing K[X]) = algebraMap _ _ :=
  funext ofFractionRing_algebraMap

/--
theorem `algebraMap_injective` / 定理 `algebraMap_injective`

English:
theorem algebraMap_injective
  statement: Function.Injective (algebraMap K[X] K⟮X⟯)
  proof: by
  rw [← ofFractionRing_comp_algebraMap]
  exact ofFractionRing_injective.comp (IsFractionRing.injective _ _)

中文:
定理 algebraMap_injective
  结论: 函数.单射 (algebraMap K[X] K⟮X⟯)
  证明: by
  rw [← ofFractionRing_comp_algebraMap]
  exact ofFractionRing_injective.comp (IsFractionRing.injective _ _)

Depends on / 依赖: IsFractionRing, IsFractionRing.injective, injective, ofFractionRing_comp_algebraMap, ofFractionRing_injective, ofFractionRing_injective.comp
-/
theorem algebraMap_injective : Function.Injective (algebraMap K[X] K⟮X⟯) := by
  rw [← ofFractionRing_comp_algebraMap]
  exact ofFractionRing_injective.comp (IsFractionRing.injective _ _)

variable {K}

section LiftAlgHom

variable {L R S : Type*} [Field L] [CommRing R] [IsDomain R] [CommSemiring S] [Algebra S K[X]]
  [Algebra S L] [Algebra S R[X]] (φ : K[X] ->ₐ[S] L) (hφ : K[X]⁰ <= L⁰.comap φ)

/--
Definition of `mapAlgHom` / `mapAlgHom` 的定义

English:
definition mapAlgHom
  signature: (φ : K[X] ->ₐ[S] R[X]) (hφ : K[X]⁰ <= R[X]⁰.comap φ)
  body: { mapRingHom φ hφ with
    commutes' := fun r => by
      simp_rw [RingHom.toFun_eq_coe, coe_mapRingHom_eq_coe_map, algebraMap_apply r, map_apply_div,
        map_one, AlgHom.commutes] }

中文:
定义 mapAlgHom
  签名: (φ : K[X] ->ₐ[S] R[X]) (hφ : K[X]⁰ <= R[X]⁰.comap φ)
  定义体: { mapRingHom φ hφ with
    commutes' := fun r => by
      simp_rw [RingHom.toFun_eq_coe, coe_mapRingHom_eq_coe_map, algebraMap_apply r, map_apply_div,
        map_one, AlgHom.commutes] }

Depends on / 依赖: AlgHom, AlgHom.commutes, RingHom, RingHom.toFun_eq_coe, algebraMap_apply, coe_mapRingHom_eq_coe_map, commutes, mapRingHom, map_apply_div, map_one, simp_rw, toFun_eq_coe
-/
def mapAlgHom (φ : K[X] ->ₐ[S] R[X]) (hφ : K[X]⁰ <= R[X]⁰.comap φ) : K⟮X⟯ ->ₐ[S] R⟮X⟯ :=
  { mapRingHom φ hφ with
    commutes' := fun r => by
      simp_rw [RingHom.toFun_eq_coe, coe_mapRingHom_eq_coe_map, algebraMap_apply r, map_apply_div,
        map_one, AlgHom.commutes] }

/--
theorem `coe_mapAlgHom_eq_coe_map` / 定理 `coe_mapAlgHom_eq_coe_map`

English:
theorem coe_mapAlgHom_eq_coe_map
  given: (φ : K[X] ->ₐ[S] R[X]) (hφ : K[X]⁰ <= R[X]⁰.comap φ)
  proof: rfl

中文:
定理 coe_mapAlgHom_eq_coe_map
  条件: (φ : K[X] ->ₐ[S] R[X]) (hφ : K[X]⁰ <= R[X]⁰.comap φ)
  证明: rfl
-/
theorem coe_mapAlgHom_eq_coe_map (φ : K[X] ->ₐ[S] R[X]) (hφ : K[X]⁰ <= R[X]⁰.comap φ) :
    (mapAlgHom φ hφ : K⟮X⟯ -> R⟮X⟯) = map φ hφ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `liftAlgHom` / `liftAlgHom` 的定义

English:
definition liftAlgHom
  signature: : K⟮X⟯ ->ₐ[S] L
  body: { liftRingHom φ.toRingHom hφ with
    commutes' := fun r => by
      simp_rw [RingHom.toFun_eq_coe, AlgHom.toRingHom_eq_coe, algebraMap_apply r,
        liftRingHom_apply_div, AlgHom.coe_toRingHom, map_one, div_one, AlgHom.commutes] }

中文:
定义 liftAlgHom
  签名: : K⟮X⟯ ->ₐ[S] L
  定义体: { liftRingHom φ.toRingHom hφ with
    commutes' := fun r => by
      simp_rw [RingHom.toFun_eq_coe, AlgHom.toRingHom_eq_coe, algebraMap_apply r,
        liftRingHom_apply_div, AlgHom.coe_toRingHom, map_one, div_one, AlgHom.commutes] }

Depends on / 依赖: AlgHom, AlgHom.coe_toRingHom, AlgHom.commutes, AlgHom.toRingHom_eq_coe, RingHom, RingHom.toFun_eq_coe, algebraMap_apply, coe_toRingHom, commutes, div_one, liftRingHom, liftRingHom_apply_div, map_one, simp_rw, toFun_eq_coe, toRingHom, toRingHom_eq_coe
-/
def liftAlgHom : K⟮X⟯ ->ₐ[S] L :=
  { liftRingHom φ.toRingHom hφ with
    commutes' := fun r => by
      simp_rw [RingHom.toFun_eq_coe, AlgHom.toRingHom_eq_coe, algebraMap_apply r,
        liftRingHom_apply_div, AlgHom.coe_toRingHom, map_one, div_one, AlgHom.commutes] }

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `liftAlgHom_apply_ofFractionRing_mk` / 定理 `liftAlgHom_apply_ofFractionRing_mk`

English:
theorem liftAlgHom_apply_ofFractionRing_mk
  given: (n : K[X]) (d : K[X]⁰)
  proof: liftMonoidWithZeroHom_apply_ofFractionRing_mk _ hφ _ _

中文:
定理 liftAlgHom_apply_ofFractionRing_mk
  条件: (n : K[X]) (d : K[X]⁰)
  证明: liftMonoidWithZeroHom_apply_ofFractionRing_mk _ hφ _ _

Depends on / 依赖: liftMonoidWithZeroHom_apply_ofFractionRing_mk
-/
theorem liftAlgHom_apply_ofFractionRing_mk (n : K[X]) (d : K[X]⁰) :
    liftAlgHom φ hφ (ofFractionRing (Localization.mk n d)) = φ n / φ d :=
  liftMonoidWithZeroHom_apply_ofFractionRing_mk _ hφ _ _

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `liftAlgHom_injective` / 定理 `liftAlgHom_injective`

English:
theorem liftAlgHom_injective
  statement: (φ : K[X] ->ₐ[S] L) (hφ : Function.Injective φ)
  proof: liftMonoidWithZeroHom_injective _ hφ

中文:
定理 liftAlgHom_injective
  结论: (φ : K[X] ->ₐ[S] L) (hφ : 函数.单射 φ)
  证明: liftMonoidWithZeroHom_injective _ hφ

Depends on / 依赖: nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
-/
theorem liftAlgHom_injective (φ : K[X] ->ₐ[S] L) (hφ : Function.Injective φ)
    (hφ' : K[X]⁰ <= L⁰.comap φ := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hφ) :
    Function.Injective (liftAlgHom φ hφ') :=
  liftMonoidWithZeroHom_injective _ hφ

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `liftAlgHom_apply_div'` / 定理 `liftAlgHom_apply_div'`

English:
theorem liftAlgHom_apply_div'
  given: (p q : K[X])
  proof: liftMonoidWithZeroHom_apply_div' _ hφ _ _

中文:
定理 liftAlgHom_apply_div'
  条件: (p q : K[X])
  证明: liftMonoidWithZeroHom_apply_div' _ hφ _ _

Depends on / 依赖: liftMonoidWithZeroHom_apply_div
-/
theorem liftAlgHom_apply_div' (p q : K[X]) :
    liftAlgHom φ hφ (algebraMap _ _ p) / liftAlgHom φ hφ (algebraMap _ _ q) = φ p / φ q :=
  liftMonoidWithZeroHom_apply_div' _ hφ _ _

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `liftAlgHom_apply_div` / 定理 `liftAlgHom_apply_div`

English:
theorem liftAlgHom_apply_div
  given: (p q : K[X])
  proof: liftMonoidWithZeroHom_apply_div _ hφ _ _

中文:
定理 liftAlgHom_apply_div
  条件: (p q : K[X])
  证明: liftMonoidWithZeroHom_apply_div _ hφ _ _

Depends on / 依赖: liftMonoidWithZeroHom_apply_div
-/
theorem liftAlgHom_apply_div (p q : K[X]) :
    liftAlgHom φ hφ (algebraMap _ _ p / algebraMap _ _ q) = φ p / φ q :=
  liftMonoidWithZeroHom_apply_div _ hφ _ _

end LiftAlgHom

variable (K)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsFractionRing K[X] K⟮X⟯
  body: by
    rw [← ofFractionRing_algebraMap]
    exact (toFractionRingRingEquiv K).symm.toRingHom.isUnit_map (IsLocalization.map_units _ y)
  exists_of_eq {x y} := by
    rw [← ofFractionRing_algebraMap]; rw [← ofFractionRing_algebraMap]
    exact fun h => IsLocalization.exists_of_eq ((toFractionRingRing

中文:
实例 :
  签名: IsFractionRing K[X] K⟮X⟯
  定义体: by
    rw [← ofFractionRing_algebraMap]
    exact (toFractionRingRingEquiv K).symm.toRingHom.isUnit_map (IsLocalization.map_units _ y)
  exists_of_eq {x y} := by
    rw [← ofFractionRing_algebraMap]; rw [← ofFractionRing_algebraMap]
    exact fun h => IsLocalization.exists_of_eq ((toFractionRingRing

Depends on / 依赖: IsLocalization, IsLocalization.exists_of_eq, IsLocalization.map_units, IsLocalization.surj, convert, exists_of_eq, injective, isUnit_map, map_units, ofFractionRing, ofFractionRing.injEq, ofFractionRing_algebraMap, ofFractionRing_mul, symm.injective, symm.toRingHom.isUnit_map, toFractionRingRingEquiv, toRingHom
-/
instance : IsFractionRing K[X] K⟮X⟯ where
  map_units y := by
    rw [← ofFractionRing_algebraMap]
    exact (toFractionRingRingEquiv K).symm.toRingHom.isUnit_map (IsLocalization.map_units _ y)
  exists_of_eq {x y} := by
    rw [← ofFractionRing_algebraMap]; rw [← ofFractionRing_algebraMap]
    exact fun h => IsLocalization.exists_of_eq ((toFractionRingRingEquiv K).symm.injective h)
  surj := by
    rintro ⟨z⟩
    convert! IsLocalization.surj K[X]⁰ z
    simp only [← ofFractionRing_algebraMap, ← ofFractionRing_mul,
      ofFractionRing.injEq]

variable {K}

/--
theorem `algebraMap_ne_zero` / 定理 `algebraMap_ne_zero`

English:
theorem algebraMap_ne_zero
  given: {x : K[X]} (hx : x != 0)
  statement: algebraMap K[X] K⟮X⟯ x != 0
  proof: by
  simpa

@[simp]

中文:
定理 algebraMap_ne_zero
  条件: {x : K[X]} (hx : x != 0)
  结论: algebraMap K[X] K⟮X⟯ x != 0
  证明: by
  simpa

@[simp]
-/
theorem algebraMap_ne_zero {x : K[X]} (hx : x != 0) : algebraMap K[X] K⟮X⟯ x != 0 := by
  simpa

@[simp]
/--
theorem `liftOn_div` / 定理 `liftOn_div`

English:
theorem liftOn_div
  statement: {P : Sort v} (p q : K[X]) (f : K[X] -> K[X] -> P) (f0 : forall p, f p 0 = f 0 1)
  proof: by
  rw [← mk_eq_div]; rw [liftOn_mk _ _ f f0 @H']

@[simp]

中文:
定理 liftOn_div
  结论: {P : 类型层 v} (p q : K[X]) (f : K[X] -> K[X] -> P) (f0 : 对任意 p, f p 0 = f 0 1)
  证明: by
  rw [← mk_eq_div]; rw [liftOn_mk _ _ f f0 @H']

@[simp]

Depends on / 依赖: RatFunc, RatFunc.liftOn, algebraMap, liftOn, liftOn_mk, mk_eq_div, ne_zero, nonZeroDivisors, nonZeroDivisors.ne_zero
-/
theorem liftOn_div {P : Sort v} (p q : K[X]) (f : K[X] -> K[X] -> P) (f0 : forall p, f p 0 = f 0 1)
    (H' : forall {p q p' q'} (_hq : q != 0) (_hq' : q' != 0), q' * p = q * p' -> f p q = f p' q')
    (H : forall {p q p' q'} (_hq : q in K[X]⁰) (_hq' : q' in K[X]⁰), q' * p = q * p' -> f p q = f p' q' :=
      fun {_ _ _ _} hq hq' h => H' (nonZeroDivisors.ne_zero hq) (nonZeroDivisors.ne_zero hq') h) :
    (RatFunc.liftOn (algebraMap _ K⟮X⟯ p / algebraMap _ _ q)) f @H = f p q := by
  rw [← mk_eq_div]; rw [liftOn_mk _ _ f f0 @H']

@[simp]
/--
theorem `liftOn'_div` / 定理 `liftOn'_div`

English:
theorem liftOn'_div
  statement: {P : Sort v} (p q : K[X]) (f : K[X] -> K[X] -> P) (f0 : forall p, f p 0 = f 0 1)
  proof: by
  rw [RatFunc.liftOn']; rw [liftOn_div _ _ _ f0]
  apply liftOn_condition_of_liftOn'_condition H

中文:
定理 liftOn'_div
  结论: {P : 类型层 v} (p q : K[X]) (f : K[X] -> K[X] -> P) (f0 : 对任意 p, f p 0 = f 0 1)
  证明: by
  rw [RatFunc.liftOn']; rw [liftOn_div _ _ _ f0]
  apply liftOn_condition_of_liftOn'_condition H

Depends on / 依赖: RatFunc, RatFunc.liftOn, _condition, liftOn, liftOn_condition_of_liftOn, liftOn_div
-/
theorem liftOn'_div {P : Sort v} (p q : K[X]) (f : K[X] -> K[X] -> P) (f0 : forall p, f p 0 = f 0 1)
    (H) :
    (RatFunc.liftOn' (algebraMap _ K⟮X⟯ p / algebraMap _ _ q)) f @H = f p q := by
  rw [RatFunc.liftOn']; rw [liftOn_div _ _ _ f0]
  apply liftOn_condition_of_liftOn'_condition H

/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  statement: {P : K⟮X⟯ -> Prop} (x : K⟮X⟯)
  proof: x.induction_on' fun p q hq => by simpa using f p q hq

中文:
定理 induction_on
  结论: {P : K⟮X⟯ -> 命题} (x : K⟮X⟯)
  证明: x.induction_on' fun p q hq => by simpa using f p q hq
-/
protected theorem induction_on {P : K⟮X⟯ -> Prop} (x : K⟮X⟯)
    (f : forall (p q : K[X]) (_ : q != 0), P (algebraMap _ K⟮X⟯ p / algebraMap _ _ q)) : P x :=
  x.induction_on' fun p q hq => by simpa using f p q hq

/--
theorem `ofFractionRing_mk'` / 定理 `ofFractionRing_mk'`

English:
theorem ofFractionRing_mk'
  given: (x : K[X]) (y : K[X]⁰)
  proof: by
  rw [IsFractionRing.mk'_eq_div]; rw [IsFractionRing.mk'_eq_div]; rw [← mk_eq_div']; rw [← mk_eq_div]

中文:
定理 ofFractionRing_mk'
  条件: (x : K[X]) (y : K[X]⁰)
  证明: by
  rw [IsFractionRing.mk'_eq_div]; rw [IsFractionRing.mk'_eq_div]; rw [← mk_eq_div']; rw [← mk_eq_div]

Depends on / 依赖: IsFractionRing, IsFractionRing.mk, _eq_div, mk_eq_div
-/
theorem ofFractionRing_mk' (x : K[X]) (y : K[X]⁰) :
    ofFractionRing (IsLocalization.mk' _ x y) =
      IsLocalization.mk' K⟮X⟯ x y := by
  rw [IsFractionRing.mk'_eq_div]; rw [IsFractionRing.mk'_eq_div]; rw [← mk_eq_div']; rw [← mk_eq_div]

/--
theorem `mk_eq_mk'` / 定理 `mk_eq_mk'`

English:
theorem mk_eq_mk'
  given: (f : Polynomial K) {g : Polynomial K} (hg : g != 0)
  proof: by
  simp only [mk_eq_div, IsFractionRing.mk'_eq_div]

中文:
定理 mk_eq_mk'
  条件: (f : 多项式 K) {g : 多项式 K} (hg : g != 0)
  证明: by
  simp only [mk_eq_div, IsFractionRing.mk'_eq_div]

Depends on / 依赖: IsFractionRing, IsFractionRing.mk, _eq_div, mk_eq_div
-/
theorem mk_eq_mk' (f : Polynomial K) {g : Polynomial K} (hg : g != 0) :
    RatFunc.mk f g = IsLocalization.mk' K⟮X⟯ f
      ⟨g, mem_nonZeroDivisors_iff_ne_zero.2 hg⟩ := by
  simp only [mk_eq_div, IsFractionRing.mk'_eq_div]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `ofFractionRing_eq` / 定理 `ofFractionRing_eq`

English:
theorem ofFractionRing_eq
  proof: funext fun x =>
    Localization.induction_on x fun x => by
      simp only [Localization.mk_eq_mk'_apply, ofFractionRing_mk', IsLocalization.algEquiv_apply,
        IsLocalization.map_mk', RingHom.id_apply]

中文:
定理 ofFractionRing_eq
  证明: funext fun x =>
    Localization.induction_on x fun x => by
      simp only [Localization.mk_eq_mk'_apply, ofFractionRing_mk', IsLocalization.algEquiv_apply,
        IsLocalization.map_mk', RingHom.id_apply]

Depends on / 依赖: IsLocalization, IsLocalization.algEquiv_apply, IsLocalization.map_mk, Localization, Localization.induction_on, Localization.mk_eq_mk, RingHom, RingHom.id_apply, _apply, algEquiv_apply, id_apply, induction_on, map_mk, mk_eq_mk, ofFractionRing_mk
-/
theorem ofFractionRing_eq :
    (ofFractionRing : FractionRing K[X] -> K⟮X⟯) = IsLocalization.algEquiv K[X]⁰ _ _ :=
  funext fun x =>
    Localization.induction_on x fun x => by
      simp only [Localization.mk_eq_mk'_apply, ofFractionRing_mk', IsLocalization.algEquiv_apply,
        IsLocalization.map_mk', RingHom.id_apply]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `toFractionRing_eq` / 定理 `toFractionRing_eq`

English:
theorem toFractionRing_eq
  proof: funext fun ⟨x⟩ =>
    Localization.induction_on x fun x => by
      simp only [Localization.mk_eq_mk'_apply, ofFractionRing_mk', IsLocalization.algEquiv_apply,
        IsLocalization.map_mk', RingHom.id_apply]

中文:
定理 toFractionRing_eq
  证明: funext fun ⟨x⟩ =>
    Localization.induction_on x fun x => by
      simp only [Localization.mk_eq_mk'_apply, ofFractionRing_mk', IsLocalization.algEquiv_apply,
        IsLocalization.map_mk', RingHom.id_apply]

Depends on / 依赖: IsLocalization, IsLocalization.algEquiv_apply, IsLocalization.map_mk, Localization, Localization.induction_on, Localization.mk_eq_mk, RingHom, RingHom.id_apply, _apply, algEquiv_apply, id_apply, induction_on, map_mk, mk_eq_mk, ofFractionRing_mk
-/
theorem toFractionRing_eq :
    (toFractionRing : K⟮X⟯ -> FractionRing K[X]) = IsLocalization.algEquiv K[X]⁰ _ _ :=
  funext fun ⟨x⟩ =>
    Localization.induction_on x fun x => by
      simp only [Localization.mk_eq_mk'_apply, ofFractionRing_mk', IsLocalization.algEquiv_apply,
        IsLocalization.map_mk', RingHom.id_apply]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `toFractionRingRingEquiv_symm_eq` / 定理 `toFractionRingRingEquiv_symm_eq`

English:
theorem toFractionRingRingEquiv_symm_eq
  proof: by
  ext x
  simp [toFractionRingRingEquiv, ofFractionRing_eq]

中文:
定理 toFractionRingRingEquiv_symm_eq
  证明: by
  ext x
  simp [toFractionRingRingEquiv, ofFractionRing_eq]

Depends on / 依赖: ofFractionRing_eq, toFractionRingRingEquiv
-/
theorem toFractionRingRingEquiv_symm_eq :
    (toFractionRingRingEquiv K).symm = (IsLocalization.algEquiv K[X]⁰ _ _).toRingEquiv := by
  ext x
  simp [toFractionRingRingEquiv, ofFractionRing_eq]

section lift

/-
As `R⟮X⟯` is a one-field-struct, we need to specialize the following instances of
`FractionRing`.
-/

variable (R L : Type*) [CommRing R] [Field L] [IsDomain R] [Algebra R[X] L] [FaithfulSMul R[X] L]

/-- `FractionRing.liftAlgebra` specialized to `R⟮X⟯`.

This is a scoped instance because it creates a diamond when `L = R⟮X⟯`. -/
scoped instance liftAlgebra : Algebra R⟮X⟯ L :=
  RingHom.toAlgebra (IsFractionRing.lift (FaithfulSMul.algebraMap_injective R[X] _))

/--
Instance `isScalarTower_liftAlgebra` / 实例 `isScalarTower_liftAlgebra`

English:
instance isScalarTower_liftAlgebra
  signature: :
  body: IsScalarTower.of_algebraMap_eq fun x =>
    (IsFractionRing.lift_algebraMap (FaithfulSMul.algebraMap_injective R[X] L) x).symm

中文:
实例 isScalarTower_liftAlgebra
  签名: :
  定义体: IsScalarTower.of_algebraMap_eq fun x =>
    (IsFractionRing.lift_algebraMap (FaithfulSMul.algebraMap_injective R[X] L) x).symm

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, IsFractionRing, IsFractionRing.lift_algebraMap, IsScalarTower, IsScalarTower.of_algebraMap_eq, algebraMap_injective, lift_algebraMap, of_algebraMap_eq
-/
instance isScalarTower_liftAlgebra :
    IsScalarTower R[X] R⟮X⟯ L :=
  IsScalarTower.of_algebraMap_eq fun x =>
    (IsFractionRing.lift_algebraMap (FaithfulSMul.algebraMap_injective R[X] L) x).symm

attribute [local instance] Polynomial.algebra

/--
Instance `faithfulSMul` / 实例 `faithfulSMul`

English:
instance faithfulSMul
  signature: (K E : Type*) [Field K] [Field E] [Algebra K E]
  body: (faithfulSMul_iff_algebraMap_injective ..).mpr
    (IsFractionRing.injective E[X] _).comp
      (Polynomial.map_injective _ <| FaithfulSMul.algebraMap_injective K E)

中文:
实例 faithfulSMul
  签名: (K E : 类型) [域 K] [域 E] [代数 K E]
  定义体: (faithfulSMul_iff_algebraMap_injective ..).mpr
    (IsFractionRing.injective E[X] _).comp
      (Polynomial.map_injective _ <| FaithfulSMul.algebraMap_injective K E)

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, IsFractionRing, IsFractionRing.injective, Polynomial, Polynomial.map_injective, algebraMap_injective, faithfulSMul_iff_algebraMap_injective, injective, map_injective
-/
instance faithfulSMul (K E : Type*) [Field K] [Field E] [Algebra K E]
    [FaithfulSMul K E] : FaithfulSMul K[X] E⟮X⟯ :=
(faithfulSMul_iff_algebraMap_injective ..).mpr
    (IsFractionRing.injective E[X] _).comp
      (Polynomial.map_injective _ <| FaithfulSMul.algebraMap_injective K E)

section rank

attribute [local instance] Polynomial.algebra

variable (k K : Type*) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]

/--
theorem `rank_ratFunc_ratFunc` / 定理 `rank_ratFunc_ratFunc`

English:
theorem rank_ratFunc_ratFunc
  statement: Module.rank k⟮X⟯ K⟮X⟯ = Module.rank k K
  proof: by
  rw [Algebra.IsAlgebraic.rank_of_isFractionRing k[X] k⟮X⟯ K[X] K⟮X⟯,
    rank_polynomial_polynomial]

中文:
定理 rank_ratFunc_ratFunc
  结论: 模.rank k⟮X⟯ K⟮X⟯ = 模.rank k K
  证明: by
  rw [Algebra.IsAlgebraic.rank_of_isFractionRing k[X] k⟮X⟯ K[X] K⟮X⟯,
    rank_polynomial_polynomial]

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.rank_of_isFractionRing, IsAlgebraic, rank_of_isFractionRing, rank_polynomial_polynomial
-/
theorem rank_ratFunc_ratFunc : Module.rank k⟮X⟯ K⟮X⟯ = Module.rank k K := by
  rw [Algebra.IsAlgebraic.rank_of_isFractionRing k[X] k⟮X⟯ K[X] K⟮X⟯,
    rank_polynomial_polynomial]

/--
theorem `finrank_ratFunc_ratFunc` / 定理 `finrank_ratFunc_ratFunc`

English:
theorem finrank_ratFunc_ratFunc
  statement: Module.finrank k⟮X⟯ K⟮X⟯ = Module.finrank k K
  proof: by
  by_cases hf : Module.Finite k⟮X⟯ K⟮X⟯
  · have hrank := rank_ratFunc_ratFunc k K
    rw [← Module.finrank_eq_rank] at hrank
    exact (Module.finrank_eq_of_rank_eq hrank.symm).symm
  · have hf' : ¬ Module.Finite k K := by
      rwa [← Module.rank_lt_aleph0_iff, ← rank_ratFunc_ratFunc, Module.ra

中文:
定理 finrank_ratFunc_ratFunc
  结论: 模.finrank k⟮X⟯ K⟮X⟯ = 模.finrank k K
  证明: by
  by_cases hf : Module.Finite k⟮X⟯ K⟮X⟯
  · have hrank := rank_ratFunc_ratFunc k K
    rw [← Module.finrank_eq_rank] at hrank
    exact (Module.finrank_eq_of_rank_eq hrank.symm).symm
  · have hf' : ¬ Module.Finite k K := by
      rwa [← Module.rank_lt_aleph0_iff, ← rank_ratFunc_ratFunc, Module.ra

Depends on / 依赖: Finite, Module, Module.Finite, Module.finrank_eq_of_rank_eq, Module.finrank_eq_rank, Module.finrank_of_not_finite, Module.rank_lt_aleph0_iff, finrank_eq_of_rank_eq, finrank_eq_rank, finrank_of_not_finite, hrank.symm, rank_lt_aleph0_iff, rank_ratFunc_ratFunc
-/
theorem finrank_ratFunc_ratFunc : Module.finrank k⟮X⟯ K⟮X⟯ = Module.finrank k K := by
  by_cases hf : Module.Finite k⟮X⟯ K⟮X⟯
  · have hrank := rank_ratFunc_ratFunc k K
    rw [← Module.finrank_eq_rank] at hrank
    exact (Module.finrank_eq_of_rank_eq hrank.symm).symm
  · have hf' : ¬ Module.Finite k K := by
      rwa [← Module.rank_lt_aleph0_iff, ← rank_ratFunc_ratFunc, Module.rank_lt_aleph0_iff]
    rw [Module.finrank_of_not_finite hf]; rw [Module.finrank_of_not_finite hf']

end rank

end lift

section IsScalarTower

/-- Let `A⟮X⟯ / A[X] / R / R₀` be a tower. If `A[X] / R / R₀` is a scalar tower
then so is `A⟮X⟯ / R / R₀`. -/
instance (R₀ R A : Type*) [CommSemiring R₀] [CommSemiring R] [CommRing A] [IsDomain A]
    [Algebra R₀ A[X]] [SMul R₀ R] [Algebra R A[X]] [IsScalarTower R₀ R A[X]] :
    IsScalarTower R₀ R A⟮X⟯ := IsScalarTower.to₁₂₄ _ _ A[X] _

/-- Let `K / A⟮X⟯ / A[X] / R` be a tower. If `K / A[X] / R` is a scalar tower
then so is `K / A⟮X⟯ / R`. -/
instance (R A K : Type*) [CommRing A] [IsDomain A] [Field K] [Algebra A[X] K]
    [FaithfulSMul A[X] K] [CommSemiring R] [Algebra R A[X]] [SMul R K] [IsScalarTower R A[X] K] :
    IsScalarTower R A⟮X⟯ K :=
  IsScalarTower.to₁₃₄ _ A[X] _ _

/-- Let `K / k / A⟮X⟯ / A[X]` be a tower. If `K / k / A[X]` is a scalar tower
then so is `K / k / A⟮X⟯`. -/
instance (A k K : Type*) [CommRing A] [IsDomain A] [Field k] [Field K] [Algebra A[X] k]
    [Algebra A[X] K] [SMul k K] [FaithfulSMul A[X] k] [FaithfulSMul A[X] K]
    [IsScalarTower A[X] k K] : IsScalarTower A⟮X⟯ k K where
  smul_assoc a b c := by
    induction a using RatFunc.induction_on with | f p q hq =>
    rw [← smul_right_inj hq]
    simp_rw [← smul_assoc, Algebra.smul_def q]
    field_simp [hq]
    simp

end IsScalarTower

end IsDomain

end IsFractionRing

end CommRing

section NumDenom

/-! ### Numerator and denominator -/

open GCDMonoid Polynomial

variable [Field K]

open scoped Classical in
/--
Definition of `numDenom` / `numDenom` 的定义

English:
definition numDenom
  signature: (x : K⟮X⟯)
  body: x.liftOn'
    (fun p q =>
      if q = 0 then ⟨0, 1⟩
      else
        let r := gcd p q
        ⟨Polynomial.C (q / r).leadingCoeff⁻¹ * (p / r),
          Polynomial.C (q / r).leadingCoeff⁻¹ * (q / r)⟩)
  (by
      intro p q a hq ha
      dsimp
      rw [if_neg hq]; rw [if_neg (mul_ne_zero ha hq)]
 

中文:
定义 numDenom
  签名: (x : K⟮X⟯)
  定义体: x.liftOn'
    (fun p q =>
      if q = 0 then ⟨0, 1⟩
      else
        let r := gcd p q
        ⟨Polynomial.C (q / r).leadingCoeff⁻¹ * (p / r),
          Polynomial.C (q / r).leadingCoeff⁻¹ * (q / r)⟩)
  (by
      intro p q a hq ha
      dsimp
      rw [if_neg hq]; rw [if_neg (mul_ne_zero ha hq)]
 

Depends on / 依赖: CommGroupWithZero, CommGroupWithZero.coe_normUnit, Polynomial, Polynomial.C, Polynomial.coe_normUnit, Polynomial.leadingCoeff_ne_zero.mpr, Prod.ext_iff, a.leadingCoeff, coe_normUnit, ext_iff, gcd_mul_left, if_neg, inv_ne_zero, leadingCoeff, leadingCoeff_ne_zero, liftOn, mul_assoc, mul_ne_zero, normalize_apply, x.liftOn
-/
def numDenom (x : K⟮X⟯) : K[X] × K[X] :=
  x.liftOn'
    (fun p q =>
      if q = 0 then ⟨0, 1⟩
      else
        let r := gcd p q
        ⟨Polynomial.C (q / r).leadingCoeff⁻¹ * (p / r),
          Polynomial.C (q / r).leadingCoeff⁻¹ * (q / r)⟩)
  (by
      intro p q a hq ha
      dsimp
      rw [if_neg hq]; rw [if_neg (mul_ne_zero ha hq)]
      have ha' : a.leadingCoeff != 0 := Polynomial.leadingCoeff_ne_zero.mpr ha
      have hainv : a.leadingCoeff⁻¹ != 0 := inv_ne_zero ha'
      simp only [Prod.ext_iff, gcd_mul_left, normalize_apply a, Polynomial.coe_normUnit, mul_assoc,
        CommGroupWithZero.coe_normUnit _ ha']
      have hdeg : (gcd p q).degree <= q.degree := degree_gcd_le_right _ hq
      have hdeg' : (Polynomial.C a.leadingCoeff⁻¹ * gcd p q).degree <= q.degree := by
        rw [Polynomial.degree_mul]; rw [Polynomial.degree_C hainv]; rw [zero_add]
        exact hdeg
      have hdivp : Polynomial.C a.leadingCoeff⁻¹ * gcd p q ∣ p :=
        (C_mul_dvd hainv).mpr (gcd_dvd_left p q)
      have hdivq : Polynomial.C a.leadingCoeff⁻¹ * gcd p q ∣ q :=
        (C_mul_dvd hainv).mpr (gcd_dvd_right p q)
      rw [EuclideanDomain.mul_div_mul_cancel ha hdivp]; rw [EuclideanDomain.mul_div_mul_cancel ha hdivq]; rw [leadingCoeff_div hdeg]; rw [leadingCoeff_div hdeg']; rw [Polynomial.leadingCoeff_mul]; rw [Polynomial.leadingCoeff_C]; rw [div_C_mul]; rw [div_C_mul]; rw [← mul_assoc]; rw [← Polynomial.C_mul]; rw [←
        mul_assoc]; rw [← Polynomial.C_mul]
      constructor <;> congr <;>
        rw [inv_div]; rw [mul_comm]; rw [mul_div_assoc]; rw [← mul_assoc]; rw [inv_inv]; rw [mul_inv_cancel₀ ha']; rw [one_mul]; rw [inv_div])

open scoped Classical in
@[simp]
/--
theorem `numDenom_div` / 定理 `numDenom_div`

English:
theorem numDenom_div
  given: (p : K[X]) {q : K[X]} (hq : q != 0)
  proof: by
  rw [numDenom]; rw [liftOn'_div]; rw [if_neg hq]
  intro p
  rw [if_pos rfl]; rw [if_neg (one_ne_zero' K[X])]
  simp

中文:
定理 numDenom_div
  条件: (p : K[X]) {q : K[X]} (hq : q != 0)
  证明: by
  rw [numDenom]; rw [liftOn'_div]; rw [if_neg hq]
  intro p
  rw [if_pos rfl]; rw [if_neg (one_ne_zero' K[X])]
  simp

Depends on / 依赖: _div, if_neg, if_pos, liftOn, numDenom, one_ne_zero
-/
theorem numDenom_div (p : K[X]) {q : K[X]} (hq : q != 0) :
    numDenom (algebraMap _ _ p / algebraMap _ _ q) =
      (Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (p / gcd p q),
        Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (q / gcd p q)) := by
  rw [numDenom]; rw [liftOn'_div]; rw [if_neg hq]
  intro p
  rw [if_pos rfl]; rw [if_neg (one_ne_zero' K[X])]
  simp

/--
Definition of `num` / `num` 的定义

English:
definition num
  signature: (x : K⟮X⟯)
  body: x.numDenom.1

中文:
定义 num
  签名: (x : K⟮X⟯)
  定义体: x.numDenom.1

Depends on / 依赖: numDenom, x.numDenom
-/
def num (x : K⟮X⟯) : K[X] :=
  x.numDenom.1

open scoped Classical in
/--
theorem `num_div'` / 定理 `num_div'`

English:
theorem num_div'
  given: (p : K[X]) {q : K[X]} (hq : q != 0)
  proof: by
  rw [num]; rw [numDenom_div _ hq]

@[simp]

中文:
定理 num_div'
  条件: (p : K[X]) {q : K[X]} (hq : q != 0)
  证明: by
  rw [num]; rw [numDenom_div _ hq]

@[simp]
-/
private theorem num_div' (p : K[X]) {q : K[X]} (hq : q != 0) :
    num (algebraMap _ _ p / algebraMap _ _ q) =
      Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (p / gcd p q) := by
  rw [num]; rw [numDenom_div _ hq]

@[simp]
/--
theorem `num_zero` / 定理 `num_zero`

English:
theorem num_zero
  statement: num (0 : K⟮X⟯) = 0
  proof: by convert! num_div' (0 : K[X]) one_ne_zero <;> simp

中文:
定理 num_zero
  结论: num (0 : K⟮X⟯) = 0
  证明: by convert! num_div' (0 : K[X]) one_ne_zero <;> simp

Depends on / 依赖: convert, num_div, one_ne_zero
-/
theorem num_zero : num (0 : K⟮X⟯) = 0 := by convert! num_div' (0 : K[X]) one_ne_zero <;> simp

open scoped Classical in
@[simp]
/--
theorem `num_div` / 定理 `num_div`

English:
theorem num_div
  given: (p q : K[X])
  proof: by
  by_cases hq : q = 0
  · simp [hq]
  · exact num_div' p hq

@[simp]

中文:
定理 num_div
  条件: (p q : K[X])
  证明: by
  by_cases hq : q = 0
  · simp [hq]
  · exact num_div' p hq

@[simp]

Depends on / 依赖: num_div
-/
theorem num_div (p q : K[X]) :
    num (algebraMap _ _ p / algebraMap _ _ q) =
      Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (p / gcd p q) := by
  by_cases hq : q = 0
  · simp [hq]
  · exact num_div' p hq

@[simp]
/--
theorem `num_one` / 定理 `num_one`

English:
theorem num_one
  statement: num (1 : K⟮X⟯) = 1
  proof: by convert! num_div (1 : K[X]) 1 <;> simp

@[simp]

中文:
定理 num_one
  结论: num (1 : K⟮X⟯) = 1
  证明: by convert! num_div (1 : K[X]) 1 <;> simp

@[simp]

Depends on / 依赖: convert, num_div
-/
theorem num_one : num (1 : K⟮X⟯) = 1 := by convert! num_div (1 : K[X]) 1 <;> simp

@[simp]
/--
theorem `num_algebraMap` / 定理 `num_algebraMap`

English:
theorem num_algebraMap
  given: (p : K[X])
  statement: num (algebraMap _ _ p) = p
  proof: by convert! num_div p 1 <;> simp

中文:
定理 num_algebraMap
  条件: (p : K[X])
  结论: num (algebraMap _ _ p) = p
  证明: by convert! num_div p 1 <;> simp

Depends on / 依赖: convert, num_div
-/
theorem num_algebraMap (p : K[X]) : num (algebraMap _ _ p) = p := by convert! num_div p 1 <;> simp

/--
theorem `num_div_dvd` / 定理 `num_div_dvd`

English:
theorem num_div_dvd
  given: (p : K[X]) {q : K[X]} (hq : q != 0)
  proof: by
  classical
  rw [num_div _ q]; rw [C_mul_dvd]
  · exact EuclideanDomain.div_dvd_of_dvd (gcd_dvd_left p q)
  · simpa only [Ne, inv_eq_zero, Polynomial.leadingCoeff_eq_zero] using right_div_gcd_ne_zero hq

中文:
定理 num_div_dvd
  条件: (p : K[X]) {q : K[X]} (hq : q != 0)
  证明: by
  classical
  rw [num_div _ q]; rw [C_mul_dvd]
  · exact EuclideanDomain.div_dvd_of_dvd (gcd_dvd_left p q)
  · simpa only [Ne, inv_eq_zero, Polynomial.leadingCoeff_eq_zero] using right_div_gcd_ne_zero hq

Depends on / 依赖: C_mul_dvd, EuclideanDomain, EuclideanDomain.div_dvd_of_dvd, Polynomial, Polynomial.leadingCoeff_eq_zero, classical, div_dvd_of_dvd, gcd_dvd_left, inv_eq_zero, leadingCoeff_eq_zero, num_div, right_div_gcd_ne_zero
-/
theorem num_div_dvd (p : K[X]) {q : K[X]} (hq : q != 0) :
    num (algebraMap _ _ p / algebraMap _ _ q) ∣ p := by
  classical
  rw [num_div _ q]; rw [C_mul_dvd]
  · exact EuclideanDomain.div_dvd_of_dvd (gcd_dvd_left p q)
  · simpa only [Ne, inv_eq_zero, Polynomial.leadingCoeff_eq_zero] using right_div_gcd_ne_zero hq

open scoped Classical in
/-- A version of `num_div_dvd` with the LHS in simp normal form -/
@[simp]
/--
theorem `num_div_dvd'` / 定理 `num_div_dvd'`

English:
theorem num_div_dvd'
  given: (p : K[X]) {q : K[X]} (hq : q != 0)
  proof: by simpa using num_div_dvd p hq

中文:
定理 num_div_dvd'
  条件: (p : K[X]) {q : K[X]} (hq : q != 0)
  证明: by simpa using num_div_dvd p hq

Depends on / 依赖: num_div_dvd
-/
theorem num_div_dvd' (p : K[X]) {q : K[X]} (hq : q != 0) :
    C (q / gcd p q).leadingCoeff⁻¹ * (p / gcd p q) ∣ p := by simpa using num_div_dvd p hq

/--
Definition of `denom` / `denom` 的定义

English:
definition denom
  signature: (x : K⟮X⟯)
  body: x.numDenom.2

中文:
定义 denom
  签名: (x : K⟮X⟯)
  定义体: x.numDenom.2

Depends on / 依赖: numDenom, x.numDenom
-/
def denom (x : K⟮X⟯) : K[X] :=
  x.numDenom.2

open scoped Classical in
@[simp]
/--
theorem `denom_div` / 定理 `denom_div`

English:
theorem denom_div
  given: (p : K[X]) {q : K[X]} (hq : q != 0)
  proof: by
  rw [denom]; rw [numDenom_div _ hq]

中文:
定理 denom_div
  条件: (p : K[X]) {q : K[X]} (hq : q != 0)
  证明: by
  rw [denom]; rw [numDenom_div _ hq]

Depends on / 依赖: numDenom_div
-/
theorem denom_div (p : K[X]) {q : K[X]} (hq : q != 0) :
    denom (algebraMap _ _ p / algebraMap _ _ q) =
      Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (q / gcd p q) := by
  rw [denom]; rw [numDenom_div _ hq]

/--
theorem `monic_denom` / 定理 `monic_denom`

English:
theorem monic_denom
  given: (x : K⟮X⟯)
  statement: (denom x).Monic
  proof: by
  classical
  induction x using RatFunc.induction_on with
  | f p q hq =>
    rw [denom_div p hq]; rw [mul_comm]
    exact Polynomial.monic_mul_leadingCoeff_inv (right_div_gcd_ne_zero hq)

中文:
定理 monic_denom
  条件: (x : K⟮X⟯)
  结论: (denom x).Monic
  证明: by
  classical
  induction x using RatFunc.induction_on with
  | f p q hq =>
    rw [denom_div p hq]; rw [mul_comm]
    exact Polynomial.monic_mul_leadingCoeff_inv (right_div_gcd_ne_zero hq)

Depends on / 依赖: Polynomial, Polynomial.monic_mul_leadingCoeff_inv, RatFunc, RatFunc.induction_on, classical, denom_div, induction_on, monic_mul_leadingCoeff_inv, mul_comm, right_div_gcd_ne_zero
-/
theorem monic_denom (x : K⟮X⟯) : (denom x).Monic := by
  classical
  induction x using RatFunc.induction_on with
  | f p q hq =>
    rw [denom_div p hq]; rw [mul_comm]
    exact Polynomial.monic_mul_leadingCoeff_inv (right_div_gcd_ne_zero hq)

/--
theorem `denom_ne_zero` / 定理 `denom_ne_zero`

English:
theorem denom_ne_zero
  given: (x : K⟮X⟯)
  statement: denom x != 0
  proof: (monic_denom x).ne_zero

@[simp]

中文:
定理 denom_ne_zero
  条件: (x : K⟮X⟯)
  结论: denom x != 0
  证明: (monic_denom x).ne_zero

@[simp]

Depends on / 依赖: monic_denom, ne_zero
-/
theorem denom_ne_zero (x : K⟮X⟯) : denom x != 0 :=
  (monic_denom x).ne_zero

@[simp]
/--
theorem `denom_zero` / 定理 `denom_zero`

English:
theorem denom_zero
  statement: denom (0 : K⟮X⟯) = 1
  proof: by
  convert! denom_div (0 : K[X]) one_ne_zero <;> simp

@[simp]

中文:
定理 denom_zero
  结论: denom (0 : K⟮X⟯) = 1
  证明: by
  convert! denom_div (0 : K[X]) one_ne_zero <;> simp

@[simp]

Depends on / 依赖: Classical, Classical.choose_spec, RingHom, RingHom.map_sub, choose_spec, convert, denom_div, map_sub, mem_span_singleton, mkSpanSingleton, one_ne_zero, sub_eq_zero, sub_smul
-/
theorem denom_zero : denom (0 : K⟮X⟯) = 1 := by
  convert! denom_div (0 : K[X]) one_ne_zero <;> simp

@[simp]
/--
theorem `denom_one` / 定理 `denom_one`

English:
theorem denom_one
  statement: denom (1 : K⟮X⟯) = 1
  proof: by
  convert! denom_div (1 : K[X]) one_ne_zero <;> simp

@[simp]

中文:
定理 denom_one
  结论: denom (1 : K⟮X⟯) = 1
  证明: by
  convert! denom_div (1 : K[X]) one_ne_zero <;> simp

@[simp]

Depends on / 依赖: RingHom, RingHom.map_one, _apply, conv_rhs, convert, denom_div, map_one, mkSpanSingleton, one_ne_zero, one_smul
-/
theorem denom_one : denom (1 : K⟮X⟯) = 1 := by
  convert! denom_div (1 : K[X]) one_ne_zero <;> simp

@[simp]
/--
theorem `denom_algebraMap` / 定理 `denom_algebraMap`

English:
theorem denom_algebraMap
  given: (p : K[X])
  statement: denom (algebraMap _ K⟮X⟯ p) = 1
  proof: by
  convert! denom_div p one_ne_zero <;> simp

@[simp]

中文:
定理 denom_algebraMap
  条件: (p : K[X])
  结论: denom (algebraMap _ K⟮X⟯ p) = 1
  证明: by
  convert! denom_div p one_ne_zero <;> simp

@[simp]

Depends on / 依赖: convert, denom_div, one_ne_zero
-/
theorem denom_algebraMap (p : K[X]) : denom (algebraMap _ K⟮X⟯ p) = 1 := by
  convert! denom_div p one_ne_zero <;> simp

@[simp]
/--
theorem `denom_div_dvd` / 定理 `denom_div_dvd`

English:
theorem denom_div_dvd
  given: (p q : K[X])
  statement: denom (algebraMap _ _ p / algebraMap _ _ q) ∣ q
  proof: by
  classical
  by_cases hq : q = 0
  · simp [hq]
  rw [denom_div _ hq]; rw [C_mul_dvd]
  · exact EuclideanDomain.div_dvd_of_dvd (gcd_dvd_right p q)
  · simpa only [Ne, inv_eq_zero, Polynomial.leadingCoeff_eq_zero] using right_div_gcd_ne_zero hq

@[simp]

中文:
定理 denom_div_dvd
  条件: (p q : K[X])
  结论: denom (algebraMap _ _ p / algebraMap _ _ q) ∣ q
  证明: by
  classical
  by_cases hq : q = 0
  · simp [hq]
  rw [denom_div _ hq]; rw [C_mul_dvd]
  · exact EuclideanDomain.div_dvd_of_dvd (gcd_dvd_right p q)
  · simpa only [Ne, inv_eq_zero, Polynomial.leadingCoeff_eq_zero] using right_div_gcd_ne_zero hq

@[simp]

Depends on / 依赖: C_mul_dvd, EuclideanDomain, EuclideanDomain.div_dvd_of_dvd, Polynomial, Polynomial.leadingCoeff_eq_zero, classical, denom_div, div_dvd_of_dvd, gcd_dvd_right, inv_eq_zero, leadingCoeff_eq_zero, right_div_gcd_ne_zero
-/
theorem denom_div_dvd (p q : K[X]) : denom (algebraMap _ _ p / algebraMap _ _ q) ∣ q := by
  classical
  by_cases hq : q = 0
  · simp [hq]
  rw [denom_div _ hq]; rw [C_mul_dvd]
  · exact EuclideanDomain.div_dvd_of_dvd (gcd_dvd_right p q)
  · simpa only [Ne, inv_eq_zero, Polynomial.leadingCoeff_eq_zero] using right_div_gcd_ne_zero hq

@[simp]
/--
theorem `num_div_denom` / 定理 `num_div_denom`

English:
theorem num_div_denom
  given: (x : K⟮X⟯)
  statement: algebraMap _ _ (num x) / algebraMap _ _ (denom x) = x
  proof: by
  classical
  induction x using RatFunc.induction_on with | _ p q hq
  have q_div_ne_zero : q / gcd p q != 0 := right_div_gcd_ne_zero hq
  rw [num_div p q]; rw [denom_div p hq]; rw [map_mul]; rw [map_mul]; rw [mul_div_mul_left]; rw [div_eq_div_iff]; rw [← map_mul]; rw [← map_mul]; rw [mul_comm _ 

中文:
定理 num_div_denom
  条件: (x : K⟮X⟯)
  结论: algebraMap _ _ (num x) / algebraMap _ _ (denom x) = x
  证明: by
  classical
  induction x using RatFunc.induction_on with | _ p q hq
  have q_div_ne_zero : q / gcd p q != 0 := right_div_gcd_ne_zero hq
  rw [num_div p q]; rw [denom_div p hq]; rw [map_mul]; rw [map_mul]; rw [mul_div_mul_left]; rw [div_eq_div_iff]; rw [← map_mul]; rw [← map_mul]; rw [mul_comm _ 

Depends on / 依赖: EuclideanDomain, EuclideanDomain.mul_div_assoc, RatFunc, RatFunc.induction_on, algebraMap_ne_zero, classical, denom_div, div_eq_div_iff, gcd_dvd_left, gcd_dvd_right, induction_on, map_mul, mul_comm, mul_div_assoc, mul_div_mul_left, num_div, q_div_ne_zero, right_div_gcd_ne_zero
-/
theorem num_div_denom (x : K⟮X⟯) : algebraMap _ _ (num x) / algebraMap _ _ (denom x) = x := by
  classical
  induction x using RatFunc.induction_on with | _ p q hq
  have q_div_ne_zero : q / gcd p q != 0 := right_div_gcd_ne_zero hq
  rw [num_div p q]; rw [denom_div p hq]; rw [map_mul]; rw [map_mul]; rw [mul_div_mul_left]; rw [div_eq_div_iff]; rw [← map_mul]; rw [← map_mul]; rw [mul_comm _ q]; rw [←
    EuclideanDomain.mul_div_assoc]; rw [← EuclideanDomain.mul_div_assoc]; rw [mul_comm]
  · apply gcd_dvd_right
  · apply gcd_dvd_left
  · exact algebraMap_ne_zero q_div_ne_zero
  · exact algebraMap_ne_zero hq
  · refine algebraMap_ne_zero (mt Polynomial.C_eq_zero.mp ?_)
    exact inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr q_div_ne_zero)

/--
theorem `isCoprime_num_denom` / 定理 `isCoprime_num_denom`

English:
theorem isCoprime_num_denom
  given: (x : K⟮X⟯)
  statement: IsCoprime x.num x.denom
  proof: by
  classical
  induction x using RatFunc.induction_on with | _ p q hq
  rw [num_div]; rw [denom_div _ hq]
  exact (isCoprime_mul_unit_left
    ((leadingCoeff_ne_zero.2 <| right_div_gcd_ne_zero hq).isUnit.inv.map C) _ _).2
      (isCoprime_div_gcd_div_gcd hq)

@[simp]

中文:
定理 isCoprime_num_denom
  条件: (x : K⟮X⟯)
  结论: IsCoprime x.num x.denom
  证明: by
  classical
  induction x using RatFunc.induction_on with | _ p q hq
  rw [num_div]; rw [denom_div _ hq]
  exact (isCoprime_mul_unit_left
    ((leadingCoeff_ne_zero.2 <| right_div_gcd_ne_zero hq).isUnit.inv.map C) _ _).2
      (isCoprime_div_gcd_div_gcd hq)

@[simp]

Depends on / 依赖: RatFunc, RatFunc.induction_on, classical, denom_div, induction_on, isCoprime_div_gcd_div_gcd, isCoprime_mul_unit_left, isUnit, isUnit.inv.map, leadingCoeff_ne_zero, num_div, right_div_gcd_ne_zero
-/
theorem isCoprime_num_denom (x : K⟮X⟯) : IsCoprime x.num x.denom := by
  classical
  induction x using RatFunc.induction_on with | _ p q hq
  rw [num_div]; rw [denom_div _ hq]
  exact (isCoprime_mul_unit_left
    ((leadingCoeff_ne_zero.2 <| right_div_gcd_ne_zero hq).isUnit.inv.map C) _ _).2
      (isCoprime_div_gcd_div_gcd hq)

@[simp]
/--
theorem `num_eq_zero_iff` / 定理 `num_eq_zero_iff`

English:
theorem num_eq_zero_iff
  given: {x : K⟮X⟯}
  statement: num x = 0 ↔ x = 0
  proof: ⟨fun h => by rw [← num_div_denom x, h, map_zero, zero_div], fun h => h.symm ▸ num_zero⟩

中文:
定理 num_eq_zero_iff
  条件: {x : K⟮X⟯}
  结论: num x = 0 ↔ x = 0
  证明: ⟨fun h => by rw [← num_div_denom x, h, map_zero, zero_div], fun h => h.symm ▸ num_zero⟩

Depends on / 依赖: h.symm, map_zero, num_div_denom, num_zero, zero_div
-/
theorem num_eq_zero_iff {x : K⟮X⟯} : num x = 0 ↔ x = 0 :=
  ⟨fun h => by rw [← num_div_denom x, h, map_zero, zero_div], fun h => h.symm ▸ num_zero⟩

/--
theorem `num_ne_zero` / 定理 `num_ne_zero`

English:
theorem num_ne_zero
  given: {x : K⟮X⟯} (hx : x != 0)
  statement: num x != 0
  proof: mt num_eq_zero_iff.mp hx

中文:
定理 num_ne_zero
  条件: {x : K⟮X⟯} (hx : x != 0)
  结论: num x != 0
  证明: mt num_eq_zero_iff.mp hx

Depends on / 依赖: num_eq_zero_iff, num_eq_zero_iff.mp
-/
theorem num_ne_zero {x : K⟮X⟯} (hx : x != 0) : num x != 0 :=
  mt num_eq_zero_iff.mp hx

/--
theorem `num_mul_eq_mul_denom_iff` / 定理 `num_mul_eq_mul_denom_iff`

English:
theorem num_mul_eq_mul_denom_iff
  given: {x : K⟮X⟯} {p q : K[X]} (hq : q != 0)
  proof: by
  rw [← (algebraMap_injective K).eq_iff]; rw [eq_div_iff (algebraMap_ne_zero hq)]
  conv_rhs => rw [← num_div_denom x]
  rw [map_mul]; rw [map_mul]; rw [div_eq_mul_inv]; rw [mul_assoc]; rw [mul_comm (Inv.inv _)]; rw [←
    mul_assoc]; rw [← div_eq_mul_inv]; rw [div_eq_iff]
  exact algebraMap_ne_z

中文:
定理 num_mul_eq_mul_denom_iff
  条件: {x : K⟮X⟯} {p q : K[X]} (hq : q != 0)
  证明: by
  rw [← (algebraMap_injective K).eq_iff]; rw [eq_div_iff (algebraMap_ne_zero hq)]
  conv_rhs => rw [← num_div_denom x]
  rw [map_mul]; rw [map_mul]; rw [div_eq_mul_inv]; rw [mul_assoc]; rw [mul_comm (Inv.inv _)]; rw [←
    mul_assoc]; rw [← div_eq_mul_inv]; rw [div_eq_iff]
  exact algebraMap_ne_z

Depends on / 依赖: Inv.inv, algebraMap_injective, algebraMap_ne_zero, conv_rhs, denom_ne_zero, div_eq_iff, div_eq_mul_inv, eq_div_iff, eq_iff, map_mul, mul_assoc, mul_comm, num_div_denom
-/
theorem num_mul_eq_mul_denom_iff {x : K⟮X⟯} {p q : K[X]} (hq : q != 0) :
    x.num * q = p * x.denom ↔ x = algebraMap _ _ p / algebraMap _ _ q := by
  rw [← (algebraMap_injective K).eq_iff]; rw [eq_div_iff (algebraMap_ne_zero hq)]
  conv_rhs => rw [← num_div_denom x]
  rw [map_mul]; rw [map_mul]; rw [div_eq_mul_inv]; rw [mul_assoc]; rw [mul_comm (Inv.inv _)]; rw [←
    mul_assoc]; rw [← div_eq_mul_inv]; rw [div_eq_iff]
  exact algebraMap_ne_zero (denom_ne_zero x)

/--
theorem `num_denom_add` / 定理 `num_denom_add`

English:
theorem num_denom_add
  given: (x y : K⟮X⟯)
  proof: (num_mul_eq_mul_denom_iff (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))).mpr by
    conv_lhs => rw [← num_div_denom x, ← num_div_denom y]
    rw [div_add_div]; rw [map_mul]; rw [map_add]; rw [map_mul]; rw [map_mul]
    · exact algebraMap_ne_zero (denom_ne_zero x)
    · exact algebraMap_ne_zero (

中文:
定理 num_denom_add
  条件: (x y : K⟮X⟯)
  证明: (num_mul_eq_mul_denom_iff (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))).mpr by
    conv_lhs => rw [← num_div_denom x, ← num_div_denom y]
    rw [div_add_div]; rw [map_mul]; rw [map_add]; rw [map_mul]; rw [map_mul]
    · exact algebraMap_ne_zero (denom_ne_zero x)
    · exact algebraMap_ne_zero (

Depends on / 依赖: algebraMap_ne_zero, conv_lhs, denom_ne_zero, div_add_div, map_add, map_mul, mul_ne_zero, num_div_denom, num_mul_eq_mul_denom_iff
-/
theorem num_denom_add (x y : K⟮X⟯) :
    (x + y).num * (x.denom * y.denom) = (x.num * y.denom + x.denom * y.num) * (x + y).denom :=
(num_mul_eq_mul_denom_iff (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))).mpr by
    conv_lhs => rw [← num_div_denom x, ← num_div_denom y]
    rw [div_add_div]; rw [map_mul]; rw [map_add]; rw [map_mul]; rw [map_mul]
    · exact algebraMap_ne_zero (denom_ne_zero x)
    · exact algebraMap_ne_zero (denom_ne_zero y)

/--
theorem `num_denom_neg` / 定理 `num_denom_neg`

English:
theorem num_denom_neg
  given: (x : K⟮X⟯)
  statement: (-x).num * x.denom = -x.num * (-x).denom
  proof: by
  rw [num_mul_eq_mul_denom_iff (denom_ne_zero x)]; rw [map_neg]; rw [neg_div]; rw [num_div_denom]

中文:
定理 num_denom_neg
  条件: (x : K⟮X⟯)
  结论: (-x).num * x.denom = -x.num * (-x).denom
  证明: by
  rw [num_mul_eq_mul_denom_iff (denom_ne_zero x)]; rw [map_neg]; rw [neg_div]; rw [num_div_denom]

Depends on / 依赖: denom_ne_zero, map_neg, neg_div, num_div_denom, num_mul_eq_mul_denom_iff
-/
theorem num_denom_neg (x : K⟮X⟯) : (-x).num * x.denom = -x.num * (-x).denom := by
  rw [num_mul_eq_mul_denom_iff (denom_ne_zero x)]; rw [map_neg]; rw [neg_div]; rw [num_div_denom]

/--
theorem `num_denom_mul` / 定理 `num_denom_mul`

English:
theorem num_denom_mul
  given: (x y : K⟮X⟯)
  proof: (num_mul_eq_mul_denom_iff (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))).mpr by
    conv_lhs =>
      rw [← num_div_denom x]; rw [← num_div_denom y]; rw [div_mul_div_comm]; rw [← map_mul]; rw [← map_mul]

中文:
定理 num_denom_mul
  条件: (x y : K⟮X⟯)
  证明: (num_mul_eq_mul_denom_iff (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))).mpr by
    conv_lhs =>
      rw [← num_div_denom x]; rw [← num_div_denom y]; rw [div_mul_div_comm]; rw [← map_mul]; rw [← map_mul]

Depends on / 依赖: conv_lhs, denom_ne_zero, div_mul_div_comm, map_mul, mul_ne_zero, num_div_denom, num_mul_eq_mul_denom_iff
-/
theorem num_denom_mul (x y : K⟮X⟯) :
    (x * y).num * (x.denom * y.denom) = x.num * y.num * (x * y).denom :=
(num_mul_eq_mul_denom_iff (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))).mpr by
    conv_lhs =>
      rw [← num_div_denom x]; rw [← num_div_denom y]; rw [div_mul_div_comm]; rw [← map_mul]; rw [← map_mul]

/--
theorem `num_dvd` / 定理 `num_dvd`

English:
theorem num_dvd
  given: {x : K⟮X⟯} {p : K[X]} (hp : p != 0)
  proof: by
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨_hx, hq⟩ := mul_ne_zero_iff.mp hp
    use denom x * q
    rw [map_mul]; rw [map_mul]; rw [← div_mul_div_comm]; rw [div_self]; rw [mul_one]; rw [num_div_denom]
    · exact ⟨mul_ne_zero (denom_ne_zero x) hq, rfl⟩
    · exact algebraMap_ne_zero hq
  · ri

中文:
定理 num_dvd
  条件: {x : K⟮X⟯} {p : K[X]} (hp : p != 0)
  证明: by
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨_hx, hq⟩ := mul_ne_zero_iff.mp hp
    use denom x * q
    rw [map_mul]; rw [map_mul]; rw [← div_mul_div_comm]; rw [div_self]; rw [mul_one]; rw [num_div_denom]
    · exact ⟨mul_ne_zero (denom_ne_zero x) hq, rfl⟩
    · exact algebraMap_ne_zero hq
  · ri

Depends on / 依赖: algebraMap_ne_zero, denom_ne_zero, div_mul_div_comm, div_self, map_mul, mul_ne_zero, mul_ne_zero_iff, mul_ne_zero_iff.mp, mul_one, num_div_denom, num_div_dvd
-/
theorem num_dvd {x : K⟮X⟯} {p : K[X]} (hp : p != 0) :
    num x ∣ p ↔ exists q : K[X], q != 0 ∧ x = algebraMap _ _ p / algebraMap _ _ q := by
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨_hx, hq⟩ := mul_ne_zero_iff.mp hp
    use denom x * q
    rw [map_mul]; rw [map_mul]; rw [← div_mul_div_comm]; rw [div_self]; rw [mul_one]; rw [num_div_denom]
    · exact ⟨mul_ne_zero (denom_ne_zero x) hq, rfl⟩
    · exact algebraMap_ne_zero hq
  · rintro ⟨q, hq, rfl⟩
    exact num_div_dvd p hq

/--
theorem `denom_dvd` / 定理 `denom_dvd`

English:
theorem denom_dvd
  given: {x : K⟮X⟯} {q : K[X]} (hq : q != 0)
  proof: by
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨_hx, hp⟩ := mul_ne_zero_iff.mp hq
    use num x * p
    rw [map_mul]; rw [map_mul]; rw [← div_mul_div_comm]; rw [div_self]; rw [mul_one]; rw [num_div_denom]
    exact algebraMap_ne_zero hp
  · rintro ⟨p, rfl⟩
    exact denom_div_dvd p q

中文:
定理 denom_dvd
  条件: {x : K⟮X⟯} {q : K[X]} (hq : q != 0)
  证明: by
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨_hx, hp⟩ := mul_ne_zero_iff.mp hq
    use num x * p
    rw [map_mul]; rw [map_mul]; rw [← div_mul_div_comm]; rw [div_self]; rw [mul_one]; rw [num_div_denom]
    exact algebraMap_ne_zero hp
  · rintro ⟨p, rfl⟩
    exact denom_div_dvd p q

Depends on / 依赖: algebraMap_ne_zero, denom_div_dvd, div_mul_div_comm, div_self, map_mul, mul_ne_zero_iff, mul_ne_zero_iff.mp, mul_one, num_div_denom
-/
theorem denom_dvd {x : K⟮X⟯} {q : K[X]} (hq : q != 0) :
    denom x ∣ q ↔ exists p : K[X], x = algebraMap _ _ p / algebraMap _ _ q := by
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨_hx, hp⟩ := mul_ne_zero_iff.mp hq
    use num x * p
    rw [map_mul]; rw [map_mul]; rw [← div_mul_div_comm]; rw [div_self]; rw [mul_one]; rw [num_div_denom]
    exact algebraMap_ne_zero hp
  · rintro ⟨p, rfl⟩
    exact denom_div_dvd p q

/--
theorem `num_mul_dvd` / 定理 `num_mul_dvd`

English:
theorem num_mul_dvd
  given: (x y : K⟮X⟯)
  statement: num (x * y) ∣ num x * num y
  proof: by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [num_dvd (mul_ne_zero (num_ne_zero hx) (num_ne_zero hy))]
  refine ⟨x.denom * y.denom, mul_ne_zero (denom_ne_zero x) (denom_ne_zero y), ?_⟩
  rw [map_mul]; rw [map_mul]; rw [← div_mul_div_comm]; rw [num_div_denom]; rw [n

中文:
定理 num_mul_dvd
  条件: (x y : K⟮X⟯)
  结论: num (x * y) ∣ num x * num y
  证明: by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [num_dvd (mul_ne_zero (num_ne_zero hx) (num_ne_zero hy))]
  refine ⟨x.denom * y.denom, mul_ne_zero (denom_ne_zero x) (denom_ne_zero y), ?_⟩
  rw [map_mul]; rw [map_mul]; rw [← div_mul_div_comm]; rw [num_div_denom]; rw [n

Depends on / 依赖: denom_ne_zero, div_mul_div_comm, map_mul, mul_ne_zero, num_div_denom, num_dvd, num_ne_zero, x.denom, y.denom
-/
theorem num_mul_dvd (x y : K⟮X⟯) : num (x * y) ∣ num x * num y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [num_dvd (mul_ne_zero (num_ne_zero hx) (num_ne_zero hy))]
  refine ⟨x.denom * y.denom, mul_ne_zero (denom_ne_zero x) (denom_ne_zero y), ?_⟩
  rw [map_mul]; rw [map_mul]; rw [← div_mul_div_comm]; rw [num_div_denom]; rw [num_div_denom]

/--
theorem `denom_mul_dvd` / 定理 `denom_mul_dvd`

English:
theorem denom_mul_dvd
  given: (x y : K⟮X⟯)
  statement: denom (x * y) ∣ denom x * denom y
  proof: by
  rw [denom_dvd (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))]
  refine ⟨x.num * y.num, ?_⟩
  rw [map_mul]; rw [map_mul]; rw [← div_mul_div_comm]; rw [num_div_denom]; rw [num_div_denom]

中文:
定理 denom_mul_dvd
  条件: (x y : K⟮X⟯)
  结论: denom (x * y) ∣ denom x * denom y
  证明: by
  rw [denom_dvd (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))]
  refine ⟨x.num * y.num, ?_⟩
  rw [map_mul]; rw [map_mul]; rw [← div_mul_div_comm]; rw [num_div_denom]; rw [num_div_denom]

Depends on / 依赖: denom_dvd, denom_ne_zero, div_mul_div_comm, map_mul, mul_ne_zero, num_div_denom, x.num, y.num
-/
theorem denom_mul_dvd (x y : K⟮X⟯) : denom (x * y) ∣ denom x * denom y := by
  rw [denom_dvd (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))]
  refine ⟨x.num * y.num, ?_⟩
  rw [map_mul]; rw [map_mul]; rw [← div_mul_div_comm]; rw [num_div_denom]; rw [num_div_denom]

/--
theorem `denom_add_dvd` / 定理 `denom_add_dvd`

English:
theorem denom_add_dvd
  given: (x y : K⟮X⟯)
  statement: denom (x + y) ∣ denom x * denom y
  proof: by
  rw [denom_dvd (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))]
  refine ⟨x.num * y.denom + x.denom * y.num, ?_⟩
  rw [map_mul]; rw [map_add]; rw [map_mul]; rw [map_mul]; rw [← div_add_div]; rw [num_div_denom]; rw [num_div_denom]
  · exact algebraMap_ne_zero (denom_ne_zero x)
  · exact algebra

中文:
定理 denom_add_dvd
  条件: (x y : K⟮X⟯)
  结论: denom (x + y) ∣ denom x * denom y
  证明: by
  rw [denom_dvd (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))]
  refine ⟨x.num * y.denom + x.denom * y.num, ?_⟩
  rw [map_mul]; rw [map_add]; rw [map_mul]; rw [map_mul]; rw [← div_add_div]; rw [num_div_denom]; rw [num_div_denom]
  · exact algebraMap_ne_zero (denom_ne_zero x)
  · exact algebra

Depends on / 依赖: algebraMap_ne_zero, denom_dvd, denom_ne_zero, div_add_div, map_add, map_mul, mul_ne_zero, num_div_denom, x.denom, x.num, y.denom, y.num
-/
theorem denom_add_dvd (x y : K⟮X⟯) : denom (x + y) ∣ denom x * denom y := by
  rw [denom_dvd (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))]
  refine ⟨x.num * y.denom + x.denom * y.num, ?_⟩
  rw [map_mul]; rw [map_add]; rw [map_mul]; rw [map_mul]; rw [← div_add_div]; rw [num_div_denom]; rw [num_div_denom]
  · exact algebraMap_ne_zero (denom_ne_zero x)
  · exact algebraMap_ne_zero (denom_ne_zero y)

/--
theorem `num_inv_dvd` / 定理 `num_inv_dvd`

English:
theorem num_inv_dvd
  given: {x : K⟮X⟯} (hx : x != 0)
  statement: num x⁻¹ ∣ denom x
  proof: by
  rw [num_dvd x.denom_ne_zero]
  refine ⟨x.num, num_ne_zero hx, ?_⟩
  nth_rw 1 [← x.num_div_denom]
  rw [inv_div]

中文:
定理 num_inv_dvd
  条件: {x : K⟮X⟯} (hx : x != 0)
  结论: num x⁻¹ ∣ denom x
  证明: by
  rw [num_dvd x.denom_ne_zero]
  refine ⟨x.num, num_ne_zero hx, ?_⟩
  nth_rw 1 [← x.num_div_denom]
  rw [inv_div]

Depends on / 依赖: denom_ne_zero, inv_div, nth_rw, num_div_denom, num_dvd, num_ne_zero, x.denom_ne_zero, x.num, x.num_div_denom
-/
theorem num_inv_dvd {x : K⟮X⟯} (hx : x != 0) : num x⁻¹ ∣ denom x := by
  rw [num_dvd x.denom_ne_zero]
  refine ⟨x.num, num_ne_zero hx, ?_⟩
  nth_rw 1 [← x.num_div_denom]
  rw [inv_div]

/--
theorem `denom_inv_dvd` / 定理 `denom_inv_dvd`

English:
theorem denom_inv_dvd
  given: {x : K⟮X⟯} (hx : x != 0)
  statement: denom x⁻¹ ∣ num x
  proof: by
  rw [denom_dvd (num_ne_zero hx)]
  refine ⟨x.denom, ?_⟩
  nth_rw 1 [← x.num_div_denom]
  rw [inv_div]

中文:
定理 denom_inv_dvd
  条件: {x : K⟮X⟯} (hx : x != 0)
  结论: denom x⁻¹ ∣ num x
  证明: by
  rw [denom_dvd (num_ne_zero hx)]
  refine ⟨x.denom, ?_⟩
  nth_rw 1 [← x.num_div_denom]
  rw [inv_div]

Depends on / 依赖: denom_dvd, inv_div, nth_rw, num_div_denom, num_ne_zero, x.denom, x.num_div_denom
-/
theorem denom_inv_dvd {x : K⟮X⟯} (hx : x != 0) : denom x⁻¹ ∣ num x := by
  rw [denom_dvd (num_ne_zero hx)]
  refine ⟨x.denom, ?_⟩
  nth_rw 1 [← x.num_div_denom]
  rw [inv_div]

/--
theorem `associated_num_inv` / 定理 `associated_num_inv`

English:
theorem associated_num_inv
  given: {x : K⟮X⟯} (hx : x != 0)
  statement: Associated (num x⁻¹) (denom x)
  proof: by
  apply associated_of_dvd_dvd (num_inv_dvd hx)
  convert! denom_inv_dvd (inv_ne_zero hx)
  rw [inv_inv]

中文:
定理 associated_num_inv
  条件: {x : K⟮X⟯} (hx : x != 0)
  结论: Associated (num x⁻¹) (denom x)
  证明: by
  apply associated_of_dvd_dvd (num_inv_dvd hx)
  convert! denom_inv_dvd (inv_ne_zero hx)
  rw [inv_inv]

Depends on / 依赖: associated_of_dvd_dvd, convert, denom_inv_dvd, inv_inv, inv_ne_zero, num_inv_dvd
-/
theorem associated_num_inv {x : K⟮X⟯} (hx : x != 0) : Associated (num x⁻¹) (denom x) := by
  apply associated_of_dvd_dvd (num_inv_dvd hx)
  convert! denom_inv_dvd (inv_ne_zero hx)
  rw [inv_inv]

/--
theorem `associated_denom_inv` / 定理 `associated_denom_inv`

English:
theorem associated_denom_inv
  given: {x : K⟮X⟯} (hx : x != 0)
  statement: Associated (denom x⁻¹) (num x)
  proof: by
  apply Associated.symm
  convert! associated_num_inv (inv_ne_zero hx)
  rw [inv_inv]

中文:
定理 associated_denom_inv
  条件: {x : K⟮X⟯} (hx : x != 0)
  结论: Associated (denom x⁻¹) (num x)
  证明: by
  apply Associated.symm
  convert! associated_num_inv (inv_ne_zero hx)
  rw [inv_inv]

Depends on / 依赖: Associated, Associated.symm, associated_num_inv, convert, inv_inv, inv_ne_zero
-/
theorem associated_denom_inv {x : K⟮X⟯} (hx : x != 0) : Associated (denom x⁻¹) (num x) := by
  apply Associated.symm
  convert! associated_num_inv (inv_ne_zero hx)
  rw [inv_inv]

/--
theorem `map_denom_ne_zero` / 定理 `map_denom_ne_zero`

English:
theorem map_denom_ne_zero
  statement: {L F : Type*} [Zero L] [FunLike F K[X] L] [ZeroHomClass F K[X] L]
  proof: fun H =>
  (denom_ne_zero f) ((map_eq_zero_iff φ hφ).mp H)

中文:
定理 map_denom_ne_zero
  结论: {L F : 类型} [零 L] [函数状 F K[X] L] [保零态射类 F K[X] L]
  证明: fun H =>
  (denom_ne_zero f) ((map_eq_zero_iff φ hφ).mp H)
-/
theorem map_denom_ne_zero {L F : Type*} [Zero L] [FunLike F K[X] L] [ZeroHomClass F K[X] L]
    (φ : F) (hφ : Function.Injective φ) (f : K⟮X⟯) : φ f.denom != 0 := fun H =>
  (denom_ne_zero f) ((map_eq_zero_iff φ hφ).mp H)

/--
theorem `map_apply` / 定理 `map_apply`

English:
theorem map_apply
  statement: {R F : Type*} [CommRing R] [IsDomain R]
  proof: by
  rw [← num_div_denom f]; rw [map_apply_div_ne_zero]; rw [num_div_denom f]
  exact denom_ne_zero _

中文:
定理 map_apply
  结论: {R F : 类型} [交换环 R] [是整环 R]
  证明: by
  rw [← num_div_denom f]; rw [map_apply_div_ne_zero]; rw [num_div_denom f]
  exact denom_ne_zero _

Depends on / 依赖: denom_ne_zero, map_apply_div_ne_zero, num_div_denom
-/
theorem map_apply {R F : Type*} [CommRing R] [IsDomain R]
    [FunLike F K[X] R[X]] [MonoidHomClass F K[X] R[X]] (φ : F)
    (hφ : K[X]⁰ <= R[X]⁰.comap φ) (f : K⟮X⟯) :
    map φ hφ f = algebraMap _ _ (φ f.num) / algebraMap _ _ (φ f.denom) := by
  rw [← num_div_denom f]; rw [map_apply_div_ne_zero]; rw [num_div_denom f]
  exact denom_ne_zero _

/--
theorem `liftMonoidWithZeroHom_apply` / 定理 `liftMonoidWithZeroHom_apply`

English:
theorem liftMonoidWithZeroHom_apply
  statement: {L : Type*} [CommGroupWithZero L] (φ : K[X] ->*₀ L)
  proof: by
  rw [← num_div_denom f]; rw [liftMonoidWithZeroHom_apply_div]; rw [num_div_denom]

中文:
定理 liftMonoidWithZeroHom_apply
  结论: {L : 类型} [带零交换群 L] (φ : K[X] ->*₀ L)
  证明: by
  rw [← num_div_denom f]; rw [liftMonoidWithZeroHom_apply_div]; rw [num_div_denom]

Depends on / 依赖: liftMonoidWithZeroHom_apply_div, num_div_denom
-/
theorem liftMonoidWithZeroHom_apply {L : Type*} [CommGroupWithZero L] (φ : K[X] ->*₀ L)
    (hφ : K[X]⁰ <= L⁰.comap φ) (f : K⟮X⟯) :
    liftMonoidWithZeroHom φ hφ f = φ f.num / φ f.denom := by
  rw [← num_div_denom f]; rw [liftMonoidWithZeroHom_apply_div]; rw [num_div_denom]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `liftRingHom_apply` / 定理 `liftRingHom_apply`

English:
theorem liftRingHom_apply
  statement: {L : Type*} [Field L] (φ : K[X] ->+* L) (hφ : K[X]⁰ <= L⁰.comap φ)
  proof: liftMonoidWithZeroHom_apply _ hφ _

中文:
定理 liftRingHom_apply
  结论: {L : 类型} [域 L] (φ : K[X] ->+* L) (hφ : K[X]⁰ <= L⁰.comap φ)
  证明: liftMonoidWithZeroHom_apply _ hφ _

Depends on / 依赖: liftMonoidWithZeroHom_apply
-/
theorem liftRingHom_apply {L : Type*} [Field L] (φ : K[X] ->+* L) (hφ : K[X]⁰ <= L⁰.comap φ)
    (f : K⟮X⟯) : liftRingHom φ hφ f = φ f.num / φ f.denom :=
  liftMonoidWithZeroHom_apply _ hφ _

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `liftAlgHom_apply` / 定理 `liftAlgHom_apply`

English:
theorem liftAlgHom_apply
  statement: {L S : Type*} [Field L] [CommSemiring S] [Algebra S K[X]] [Algebra S L]
  proof: liftMonoidWithZeroHom_apply _ hφ _

中文:
定理 liftAlgHom_apply
  结论: {L S : 类型} [域 L] [交换半环 S] [代数 S K[X]] [代数 S L]
  证明: liftMonoidWithZeroHom_apply _ hφ _

Depends on / 依赖: liftMonoidWithZeroHom_apply
-/
theorem liftAlgHom_apply {L S : Type*} [Field L] [CommSemiring S] [Algebra S K[X]] [Algebra S L]
    (φ : K[X] ->ₐ[S] L) (hφ : K[X]⁰ <= L⁰.comap φ) (f : K⟮X⟯) :
    liftAlgHom φ hφ f = φ f.num / φ f.denom :=
  liftMonoidWithZeroHom_apply _ hφ _

/--
theorem `num_mul_denom_add_denom_mul_num_ne_zero` / 定理 `num_mul_denom_add_denom_mul_num_ne_zero`

English:
theorem num_mul_denom_add_denom_mul_num_ne_zero
  given: {x y : K⟮X⟯} (hxy : x + y != 0)
  proof: by
  intro h_zero
  have h := num_denom_add x y
  rw [h_zero]; rw [zero_mul] at h
  exact (mul_ne_zero (num_ne_zero hxy) (mul_ne_zero x.denom_ne_zero y.denom_ne_zero)) h

中文:
定理 num_mul_denom_add_denom_mul_num_ne_zero
  条件: {x y : K⟮X⟯} (hxy : x + y != 0)
  证明: by
  intro h_zero
  have h := num_denom_add x y
  rw [h_zero]; rw [zero_mul] at h
  exact (mul_ne_zero (num_ne_zero hxy) (mul_ne_zero x.denom_ne_zero y.denom_ne_zero)) h

Depends on / 依赖: denom_ne_zero, h_zero, mul_ne_zero, num_denom_add, num_ne_zero, x.denom_ne_zero, y.denom_ne_zero, zero_mul
-/
theorem num_mul_denom_add_denom_mul_num_ne_zero {x y : K⟮X⟯} (hxy : x + y != 0) :
    x.num * y.denom + x.denom * y.num != 0 := by
  intro h_zero
  have h := num_denom_add x y
  rw [h_zero]; rw [zero_mul] at h
  exact (mul_ne_zero (num_ne_zero hxy) (mul_ne_zero x.denom_ne_zero y.denom_ne_zero)) h

end NumDenom

section Char

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Field
  signature: K] {p
  body: charP_of_injective_algebraMap' K p

中文:
实例 [域
  签名: K] {p
  定义体: charP_of_injective_algebraMap' K p

Depends on / 依赖: charP_of_injective_algebraMap
-/
instance [Field K] {p : Nat} [CharP K p] : CharP K⟮X⟯ p :=
  charP_of_injective_algebraMap' K p

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Field
  signature: K] {p
  body: ExpChar.of_injective_algebraMap' K p

中文:
实例 [域
  签名: K] {p
  定义体: ExpChar.of_injective_algebraMap' K p

Depends on / 依赖: ExpChar, ExpChar.of_injective_algebraMap, of_injective_algebraMap
-/
instance [Field K] {p : Nat} [ExpChar K p] : ExpChar K⟮X⟯ p :=
  ExpChar.of_injective_algebraMap' K p

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Field
  signature: K] [CharZero K] : CharZero K⟮X⟯
  body: Algebra.charZero_of_charZero K _

中文:
实例 [域
  签名: K] [特征零 K] : 特征零 K⟮X⟯
  定义体: Algebra.charZero_of_charZero K _

Depends on / 依赖: Algebra, Algebra.charZero_of_charZero, charZero_of_charZero
-/
instance [Field K] [CharZero K] : CharZero K⟮X⟯ :=
  Algebra.charZero_of_charZero K _

end Char

end RatFunc
