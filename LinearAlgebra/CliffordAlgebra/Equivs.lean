/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.QuaternionBasis
public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.CliffordAlgebra.Star
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Other constructions isomorphic to Clifford Algebras

This file contains isomorphisms showing that other types are equivalent to some `CliffordAlgebra`.

## Rings

* `CliffordAlgebraRing.equiv`: any ring is equivalent to a `CliffordAlgebra` over a
  zero-dimensional vector space.

## Complex numbers

* `CliffordAlgebraComplex.equiv`: the `Complex` numbers are equivalent as an `ℝ`-algebra to a
  `CliffordAlgebra` over a one-dimensional vector space with a quadratic form that satisfies
  `Q (ι Q 1) = -1`.
* `CliffordAlgebraComplex.toComplex`: the forward direction of this equiv
* `CliffordAlgebraComplex.ofComplex`: the reverse direction of this equiv

We show additionally that this equivalence sends `Complex.conj` to `CliffordAlgebra.involute` and
vice-versa:

* `CliffordAlgebraComplex.toComplex_involute`
* `CliffordAlgebraComplex.ofComplex_conj`

Note that in this algebra `CliffordAlgebra.reverse` is the identity and so the clifford conjugate
is the same as `CliffordAlgebra.involute`.

## Quaternion algebras

* `CliffordAlgebraQuaternion.equiv`: a `QuaternionAlgebra` over `R` is equivalent as an
  `R`-algebra to a clifford algebra over `R × R`, sending `i` to `(0, 1)` and `j` to `(1, 0)`.
* `CliffordAlgebraQuaternion.toQuaternion`: the forward direction of this equiv
* `CliffordAlgebraQuaternion.ofQuaternion`: the reverse direction of this equiv

We show additionally that this equivalence sends `QuaternionAlgebra.conj` to the clifford conjugate
and vice-versa:

* `CliffordAlgebraQuaternion.toQuaternion_star`
* `CliffordAlgebraQuaternion.ofQuaternion_star`

## Dual numbers

* `CliffordAlgebraDualNumber.equiv`: `R[ε]` is equivalent as an `R`-algebra to a clifford
  algebra over `R` where `Q = 0`.

-/

@[expose] public section


open CliffordAlgebra

/-! ### The clifford algebra isomorphic to a ring -/


namespace CliffordAlgebraRing

open scoped ComplexConjugate

variable {R : Type*} [CommRing R]

@[simp]
/--
theorem `ι_eq_zero` / 定理 `ι_eq_zero`

English:
theorem ι_eq_zero
  statement: ι (0 : QuadraticForm R Unit) = 0
  proof: Subsingleton.elim _ _

中文:
定理 ι_eq_zero
  结论: ι (0 : QuadraticForm R 单元) = 0
  证明: Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem ι_eq_zero : ι (0 : QuadraticForm R Unit) = 0 :=
  Subsingleton.elim _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommRing (CliffordAlgebra (0 : QuadraticForm R Unit))
  body: fun x y => by
    induction x using CliffordAlgebra.induction with
    | algebraMap r => apply Algebra.commutes
    | ι x => simp
    | add x₁ x₂ hx₁ hx₂ => rw [mul_add, add_mul, hx₁, hx₂]
    | mul x₁ x₂ hx₁ hx₂ => rw [mul_assoc, hx₂, ← mul_assoc, hx₁, ← mul_assoc]

中文:
实例 :
  签名: 交换环 (CliffordAlgebra (0 : QuadraticForm R 单元))
  定义体: fun x y => by
    induction x using CliffordAlgebra.induction with
    | algebraMap r => apply Algebra.commutes
    | ι x => simp
    | add x₁ x₂ hx₁ hx₂ => rw [mul_add, add_mul, hx₁, hx₂]
    | mul x₁ x₂ hx₁ hx₂ => rw [mul_assoc, hx₂, ← mul_assoc, hx₁, ← mul_assoc]

Depends on / 依赖: Algebra, Algebra.commutes, CliffordAlgebra, CliffordAlgebra.induction, add_mul, algebraMap, commutes, mul_add, mul_assoc
-/
instance : CommRing (CliffordAlgebra (0 : QuadraticForm R Unit)) where
  mul_comm := fun x y => by
    induction x using CliffordAlgebra.induction with
    | algebraMap r => apply Algebra.commutes
    | ι x => simp
    | add x₁ x₂ hx₁ hx₂ => rw [mul_add, add_mul, hx₁, hx₂]
    | mul x₁ x₂ hx₁ hx₂ => rw [mul_assoc, hx₂, ← mul_assoc, hx₁, ← mul_assoc]

/--
theorem `reverse_apply` / 定理 `reverse_apply`

English:
theorem reverse_apply
  given: (x : CliffordAlgebra (0 : QuadraticForm R Unit))
  proof: by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => exact reverse.commutes _
  | ι x => rw [ι_eq_zero, LinearMap.zero_apply, reverse.map_zero]
  | mul x₁ x₂ hx₁ hx₂ => rw [reverse.map_mul, mul_comm, hx₁, hx₂]
  | add x₁ x₂ hx₁ hx₂ => rw [reverse.map_add, hx₁, hx₂]

@[simp]

中文:
定理 reverse_apply
  条件: (x : CliffordAlgebra (0 : QuadraticForm R 单元))
  证明: by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => exact reverse.commutes _
  | ι x => rw [ι_eq_zero, LinearMap.zero_apply, reverse.map_zero]
  | mul x₁ x₂ hx₁ hx₂ => rw [reverse.map_mul, mul_comm, hx₁, hx₂]
  | add x₁ x₂ hx₁ hx₂ => rw [reverse.map_add, hx₁, hx₂]

@[simp]

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.induction, LinearMap, LinearMap.zero_apply, algebraMap, commutes, map_add, map_mul, map_zero, mul_comm, reverse, reverse.commutes, reverse.map_add, reverse.map_mul, reverse.map_zero, zero_apply
-/
theorem reverse_apply (x : CliffordAlgebra (0 : QuadraticForm R Unit)) :
    x.reverse = x := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => exact reverse.commutes _
  | ι x => rw [ι_eq_zero, LinearMap.zero_apply, reverse.map_zero]
  | mul x₁ x₂ hx₁ hx₂ => rw [reverse.map_mul, mul_comm, hx₁, hx₂]
  | add x₁ x₂ hx₁ hx₂ => rw [reverse.map_add, hx₁, hx₂]

@[simp]
/--
theorem `reverse_eq_id` / 定理 `reverse_eq_id`

English:
theorem reverse_eq_id
  proof: LinearMap.ext reverse_apply

@[simp]

中文:
定理 reverse_eq_id
  证明: LinearMap.ext reverse_apply

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext, reverse_apply
-/
theorem reverse_eq_id :
    (reverse : CliffordAlgebra (0 : QuadraticForm R Unit) ->ₗ[R] _) = LinearMap.id :=
  LinearMap.ext reverse_apply

@[simp]
/--
theorem `involute_eq_id` / 定理 `involute_eq_id`

English:
theorem involute_eq_id
  proof: by ext; simp

中文:
定理 involute_eq_id
  证明: by ext; simp
-/
theorem involute_eq_id :
    (involute : CliffordAlgebra (0 : QuadraticForm R Unit) ->ₐ[R] _) = AlgHom.id R _ := by ext; simp

/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : CliffordAlgebra (0 : QuadraticForm R Unit) ≃ₐ[R] R
  body: AlgEquiv.ofAlgHom
    (CliffordAlgebra.lift (0 : QuadraticForm R Unit) <|
      ⟨0, fun _ : Unit => (zero_mul (0 : R)).trans (algebraMap R _).map_zero.symm⟩)
    (Algebra.ofId R _) (by ext)
    (by ext : 1; rw [ι_eq_zero, LinearMap.comp_zero, LinearMap.comp_zero])

中文:
定义 equiv
  签名: : CliffordAlgebra (0 : QuadraticForm R 单元) ≃ₐ[R] R
  定义体: AlgEquiv.ofAlgHom
    (CliffordAlgebra.lift (0 : QuadraticForm R Unit) <|
      ⟨0, fun _ : Unit => (zero_mul (0 : R)).trans (algebraMap R _).map_zero.symm⟩)
    (Algebra.ofId R _) (by ext)
    (by ext : 1; rw [ι_eq_zero, LinearMap.comp_zero, LinearMap.comp_zero])
-/
protected def equiv : CliffordAlgebra (0 : QuadraticForm R Unit) ≃ₐ[R] R :=
  AlgEquiv.ofAlgHom
    (CliffordAlgebra.lift (0 : QuadraticForm R Unit) <|
      ⟨0, fun _ : Unit => (zero_mul (0 : R)).trans (algebraMap R _).map_zero.symm⟩)
    (Algebra.ofId R _) (by ext)
    (by ext : 1; rw [ι_eq_zero, LinearMap.comp_zero, LinearMap.comp_zero])

end CliffordAlgebraRing

/-! ### The clifford algebra isomorphic to the complex numbers -/


namespace CliffordAlgebraComplex

open scoped ComplexConjugate

/--
Definition of `Q` / `Q` 的定义

English:
definition Q
  signature: : QuadraticForm Real Real
  body: -QuadraticMap.sq

@[simp]

中文:
定义 Q
  签名: : QuadraticForm 实数 实数
  定义体: -QuadraticMap.sq

@[simp]

Depends on / 依赖: QuadraticMap, QuadraticMap.sq
-/
def Q : QuadraticForm Real Real :=
  -QuadraticMap.sq

@[simp]
/--
theorem `Q_apply` / 定理 `Q_apply`

English:
theorem Q_apply
  given: (r : Real)
  statement: Q r = -(r * r)
  proof: rfl

中文:
定理 Q_apply
  条件: (r : 实数)
  结论: Q r = -(r * r)
  证明: rfl
-/
theorem Q_apply (r : Real) : Q r = -(r * r) :=
  rfl

/--
Definition of `toComplex` / `toComplex` 的定义

English:
definition toComplex
  signature: : CliffordAlgebra Q ->ₐ[Real] Complex
  body: CliffordAlgebra.lift Q
    ⟨LinearMap.toSpanSingleton _ _ Complex.I, fun r => by
      dsimp [LinearMap.toSpanSingleton, LinearMap.id]
      rw [mul_mul_mul_comm]
      simp⟩

@[simp]

中文:
定义 toComplex
  签名: : CliffordAlgebra Q ->ₐ[实数] 复形
  定义体: CliffordAlgebra.lift Q
    ⟨LinearMap.toSpanSingleton _ _ Complex.I, fun r => by
      dsimp [LinearMap.toSpanSingleton, LinearMap.id]
      rw [mul_mul_mul_comm]
      simp⟩

@[simp]

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.lift, Complex.I, LinearMap, LinearMap.id, LinearMap.toSpanSingleton, mul_mul_mul_comm, toSpanSingleton
-/
def toComplex : CliffordAlgebra Q ->ₐ[Real] Complex :=
  CliffordAlgebra.lift Q
    ⟨LinearMap.toSpanSingleton _ _ Complex.I, fun r => by
      dsimp [LinearMap.toSpanSingleton, LinearMap.id]
      rw [mul_mul_mul_comm]
      simp⟩

@[simp]
/--
theorem `toComplex_ι` / 定理 `toComplex_ι`

English:
theorem toComplex_ι
  given: (r : Real)
  statement: toComplex (ι Q r) = r • Complex.I
  proof: CliffordAlgebra.lift_ι_apply _ _ r

中文:
定理 toComplex_ι
  条件: (r : 实数)
  结论: toComplex (ι Q r) = r • 复形.I
  证明: CliffordAlgebra.lift_ι_apply _ _ r

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.lift_
-/
theorem toComplex_ι (r : Real) : toComplex (ι Q r) = r • Complex.I :=
  CliffordAlgebra.lift_ι_apply _ _ r

/-- `CliffordAlgebra.involute` is analogous to `Complex.conj`. -/
@[simp]
/--
theorem `toComplex_involute` / 定理 `toComplex_involute`

English:
theorem toComplex_involute
  given: (c : CliffordAlgebra Q)
  proof: by
  have : toComplex (involute (ι Q 1)) = conj (toComplex (ι Q 1)) := by
    simp only [involute_ι, toComplex_ι, map_neg, one_smul, Complex.conj_I]
  suffices toComplex.comp involute = Complex.conjAe.toAlgHom.comp toComplex by
    exact AlgHom.congr_fun this c
  ext : 2
  exact this

中文:
定理 toComplex_involute
  条件: (c : CliffordAlgebra Q)
  证明: by
  have : toComplex (involute (ι Q 1)) = conj (toComplex (ι Q 1)) := by
    simp only [involute_ι, toComplex_ι, map_neg, one_smul, Complex.conj_I]
  suffices toComplex.comp involute = Complex.conjAe.toAlgHom.comp toComplex by
    exact AlgHom.congr_fun this c
  ext : 2
  exact this

Depends on / 依赖: AlgHom, AlgHom.congr_fun, Complex.conjAe.toAlgHom.comp, Complex.conj_I, congr_fun, conjAe, conj_I, involute, map_neg, one_smul, toAlgHom, toComplex, toComplex.comp
-/
theorem toComplex_involute (c : CliffordAlgebra Q) :
    toComplex (involute c) = conj (toComplex c) := by
  have : toComplex (involute (ι Q 1)) = conj (toComplex (ι Q 1)) := by
    simp only [involute_ι, toComplex_ι, map_neg, one_smul, Complex.conj_I]
  suffices toComplex.comp involute = Complex.conjAe.toAlgHom.comp toComplex by
    exact AlgHom.congr_fun this c
  ext : 2
  exact this

/--
Definition of `ofComplex` / `ofComplex` 的定义

English:
definition ofComplex
  signature: : Complex ->ₐ[Real] CliffordAlgebra Q
  body: Complex.lift
    ⟨CliffordAlgebra.ι Q 1, by
      rw [CliffordAlgebra.ι_sq_scalar]; rw [Q_apply]; rw [one_mul]; rw [map_neg]; rw [map_one]⟩

@[simp]

中文:
定义 ofComplex
  签名: : 复形 ->ₐ[实数] CliffordAlgebra Q
  定义体: Complex.lift
    ⟨CliffordAlgebra.ι Q 1, by
      rw [CliffordAlgebra.ι_sq_scalar]; rw [Q_apply]; rw [one_mul]; rw [map_neg]; rw [map_one]⟩

@[simp]

Depends on / 依赖: CliffordAlgebra, Complex.lift, Q_apply, map_neg, map_one, one_mul
-/
def ofComplex : Complex ->ₐ[Real] CliffordAlgebra Q :=
  Complex.lift
    ⟨CliffordAlgebra.ι Q 1, by
      rw [CliffordAlgebra.ι_sq_scalar]; rw [Q_apply]; rw [one_mul]; rw [map_neg]; rw [map_one]⟩

@[simp]
/--
theorem `ofComplex_I` / 定理 `ofComplex_I`

English:
theorem ofComplex_I
  statement: ofComplex Complex.I = ι Q 1
  proof: Complex.liftAux_apply_I _ (by simp)

@[simp]

中文:
定理 ofComplex_I
  结论: ofComplex 复形.I = ι Q 1
  证明: Complex.liftAux_apply_I _ (by simp)

@[simp]

Depends on / 依赖: Complex.liftAux_apply_I, liftAux_apply_I
-/
theorem ofComplex_I : ofComplex Complex.I = ι Q 1 :=
  Complex.liftAux_apply_I _ (by simp)

@[simp]
/--
theorem `toComplex_comp_ofComplex` / 定理 `toComplex_comp_ofComplex`

English:
theorem toComplex_comp_ofComplex
  statement: toComplex.comp ofComplex = AlgHom.id Real Complex
  proof: by
  ext1
  dsimp only [AlgHom.comp_apply, Subtype.coe_mk, AlgHom.id_apply]
  rw [ofComplex_I]; rw [toComplex_ι]; rw [one_smul]

@[simp]

中文:
定理 toComplex_comp_ofComplex
  结论: toComplex.comp ofComplex = 代数态射.id 实数 复形
  证明: by
  ext1
  dsimp only [AlgHom.comp_apply, Subtype.coe_mk, AlgHom.id_apply]
  rw [ofComplex_I]; rw [toComplex_ι]; rw [one_smul]

@[simp]

Depends on / 依赖: AlgHom, AlgHom.comp_apply, AlgHom.id_apply, Subtype, Subtype.coe_mk, coe_mk, comp_apply, id_apply, ofComplex_I, one_smul
-/
theorem toComplex_comp_ofComplex : toComplex.comp ofComplex = AlgHom.id Real Complex := by
  ext1
  dsimp only [AlgHom.comp_apply, Subtype.coe_mk, AlgHom.id_apply]
  rw [ofComplex_I]; rw [toComplex_ι]; rw [one_smul]

@[simp]
/--
theorem `toComplex_ofComplex` / 定理 `toComplex_ofComplex`

English:
theorem toComplex_ofComplex
  given: (c : Complex)
  statement: toComplex (ofComplex c) = c
  proof: AlgHom.congr_fun toComplex_comp_ofComplex c

@[simp]

中文:
定理 toComplex_ofComplex
  条件: (c : 复形)
  结论: toComplex (ofComplex c) = c
  证明: AlgHom.congr_fun toComplex_comp_ofComplex c

@[simp]

Depends on / 依赖: AlgHom, AlgHom.congr_fun, congr_fun, toComplex_comp_ofComplex
-/
theorem toComplex_ofComplex (c : Complex) : toComplex (ofComplex c) = c :=
  AlgHom.congr_fun toComplex_comp_ofComplex c

@[simp]
/--
theorem `ofComplex_comp_toComplex` / 定理 `ofComplex_comp_toComplex`

English:
theorem ofComplex_comp_toComplex
  statement: ofComplex.comp toComplex = AlgHom.id Real (CliffordAlgebra Q)
  proof: by
  ext
  dsimp only [LinearMap.comp_apply, Subtype.coe_mk, AlgHom.id_apply, AlgHom.toLinearMap_apply,
    AlgHom.comp_apply]
  rw [toComplex_ι]; rw [one_smul]; rw [ofComplex_I]

@[simp]

中文:
定理 ofComplex_comp_toComplex
  结论: ofComplex.comp toComplex = 代数态射.id 实数 (CliffordAlgebra Q)
  证明: by
  ext
  dsimp only [LinearMap.comp_apply, Subtype.coe_mk, AlgHom.id_apply, AlgHom.toLinearMap_apply,
    AlgHom.comp_apply]
  rw [toComplex_ι]; rw [one_smul]; rw [ofComplex_I]

@[simp]

Depends on / 依赖: AlgHom, AlgHom.comp_apply, AlgHom.id_apply, AlgHom.toLinearMap_apply, LinearMap, LinearMap.comp_apply, Subtype, Subtype.coe_mk, coe_mk, comp_apply, id_apply, ofComplex_I, one_smul, toLinearMap_apply
-/
theorem ofComplex_comp_toComplex : ofComplex.comp toComplex = AlgHom.id Real (CliffordAlgebra Q) := by
  ext
  dsimp only [LinearMap.comp_apply, Subtype.coe_mk, AlgHom.id_apply, AlgHom.toLinearMap_apply,
    AlgHom.comp_apply]
  rw [toComplex_ι]; rw [one_smul]; rw [ofComplex_I]

@[simp]
/--
theorem `ofComplex_toComplex` / 定理 `ofComplex_toComplex`

English:
theorem ofComplex_toComplex
  given: (c : CliffordAlgebra Q)
  statement: ofComplex (toComplex c) = c
  proof: AlgHom.congr_fun ofComplex_comp_toComplex c

中文:
定理 ofComplex_toComplex
  条件: (c : CliffordAlgebra Q)
  结论: ofComplex (toComplex c) = c
  证明: AlgHom.congr_fun ofComplex_comp_toComplex c

Depends on / 依赖: AlgHom, AlgHom.congr_fun, congr_fun, ofComplex_comp_toComplex
-/
theorem ofComplex_toComplex (c : CliffordAlgebra Q) : ofComplex (toComplex c) = c :=
  AlgHom.congr_fun ofComplex_comp_toComplex c

/-- The clifford algebras over `CliffordAlgebraComplex.Q` is isomorphic as an `ℝ`-algebra to `ℂ`. -/
@[simps!]
/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : CliffordAlgebra Q ≃ₐ[Real] Complex
  body: AlgEquiv.ofAlgHom toComplex ofComplex toComplex_comp_ofComplex ofComplex_comp_toComplex

中文:
定义 equiv
  签名: : CliffordAlgebra Q ≃ₐ[实数] 复形
  定义体: AlgEquiv.ofAlgHom toComplex ofComplex toComplex_comp_ofComplex ofComplex_comp_toComplex
-/
protected def equiv : CliffordAlgebra Q ≃ₐ[Real] Complex :=
  AlgEquiv.ofAlgHom toComplex ofComplex toComplex_comp_ofComplex ofComplex_comp_toComplex

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommRing (CliffordAlgebra Q)
  body: fun x y =>
CliffordAlgebraComplex.equiv.injective by
      rw [map_mul]; rw [mul_comm]; rw [map_mul]

中文:
实例 :
  签名: 交换环 (CliffordAlgebra Q)
  定义体: fun x y =>
CliffordAlgebraComplex.equiv.injective by
      rw [map_mul]; rw [mul_comm]; rw [map_mul]
-/
instance : CommRing (CliffordAlgebra Q) where
  mul_comm := fun x y =>
CliffordAlgebraComplex.equiv.injective by
      rw [map_mul]; rw [mul_comm]; rw [map_mul]

/--
theorem `reverse_apply` / 定理 `reverse_apply`

English:
theorem reverse_apply
  given: (x : CliffordAlgebra Q)
  statement: x.reverse = x
  proof: by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => exact reverse.commutes _
  | ι x => rw [reverse_ι]
  | mul x₁ x₂ hx₁ hx₂ => rw [reverse.map_mul, mul_comm, hx₁, hx₂]
  | add x₁ x₂ hx₁ hx₂ => rw [reverse.map_add, hx₁, hx₂]

@[simp]

中文:
定理 reverse_apply
  条件: (x : CliffordAlgebra Q)
  结论: x.reverse = x
  证明: by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => exact reverse.commutes _
  | ι x => rw [reverse_ι]
  | mul x₁ x₂ hx₁ hx₂ => rw [reverse.map_mul, mul_comm, hx₁, hx₂]
  | add x₁ x₂ hx₁ hx₂ => rw [reverse.map_add, hx₁, hx₂]

@[simp]

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.induction, algebraMap, commutes, map_add, map_mul, mul_comm, reverse, reverse.commutes, reverse.map_add, reverse.map_mul
-/
theorem reverse_apply (x : CliffordAlgebra Q) : x.reverse = x := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => exact reverse.commutes _
  | ι x => rw [reverse_ι]
  | mul x₁ x₂ hx₁ hx₂ => rw [reverse.map_mul, mul_comm, hx₁, hx₂]
  | add x₁ x₂ hx₁ hx₂ => rw [reverse.map_add, hx₁, hx₂]

@[simp]
/--
theorem `reverse_eq_id` / 定理 `reverse_eq_id`

English:
theorem reverse_eq_id
  statement: (reverse : CliffordAlgebra Q ->ₗ[Real] _) = LinearMap.id
  proof: LinearMap.ext reverse_apply

中文:
定理 reverse_eq_id
  结论: (reverse : CliffordAlgebra Q ->ₗ[实数] _) = 线性映射.id
  证明: LinearMap.ext reverse_apply

Depends on / 依赖: LinearMap, LinearMap.ext, reverse_apply
-/
theorem reverse_eq_id : (reverse : CliffordAlgebra Q ->ₗ[Real] _) = LinearMap.id :=
  LinearMap.ext reverse_apply

/-- `Complex.conj` is analogous to `CliffordAlgebra.involute`. -/
@[simp]
/--
theorem `ofComplex_conj` / 定理 `ofComplex_conj`

English:
theorem ofComplex_conj
  given: (c : Complex)
  statement: ofComplex (conj c) = involute (ofComplex c)
  proof: CliffordAlgebraComplex.equiv.injective by
    rw [equiv_apply]; rw [equiv_apply]; rw [toComplex_involute]; rw [toComplex_ofComplex]; rw [toComplex_ofComplex]

中文:
定理 ofComplex_conj
  条件: (c : 复形)
  结论: ofComplex (conj c) = involute (ofComplex c)
  证明: CliffordAlgebraComplex.equiv.injective by
    rw [equiv_apply]; rw [equiv_apply]; rw [toComplex_involute]; rw [toComplex_ofComplex]; rw [toComplex_ofComplex]

Depends on / 依赖: CliffordAlgebraComplex, CliffordAlgebraComplex.equiv.injective, equiv_apply, injective, toComplex_involute, toComplex_ofComplex
-/
theorem ofComplex_conj (c : Complex) : ofComplex (conj c) = involute (ofComplex c) :=
CliffordAlgebraComplex.equiv.injective by
    rw [equiv_apply]; rw [equiv_apply]; rw [toComplex_involute]; rw [toComplex_ofComplex]; rw [toComplex_ofComplex]

end CliffordAlgebraComplex

/-! ### The clifford algebra isomorphic to the quaternions -/


namespace CliffordAlgebraQuaternion

open scoped Quaternion

open QuaternionAlgebra

variable {R : Type*} [CommRing R] (c₁ c₂ : R)

/--
Definition of `Q` / `Q` 的定义

English:
definition Q
  signature: : QuadraticForm R (R × R)
  body: (c₁ • QuadraticMap.sq).prod (c₂ • QuadraticMap.sq)

@[simp]

中文:
定义 Q
  签名: : QuadraticForm R (R × R)
  定义体: (c₁ • QuadraticMap.sq).prod (c₂ • QuadraticMap.sq)

@[simp]

Depends on / 依赖: QuadraticMap, QuadraticMap.sq
-/
def Q : QuadraticForm R (R × R) :=
  (c₁ • QuadraticMap.sq).prod (c₂ • QuadraticMap.sq)

@[simp]
/--
theorem `Q_apply` / 定理 `Q_apply`

English:
theorem Q_apply
  given: (v : R × R)
  statement: Q c₁ c₂ v = c₁ * (v.1 * v.1) + c₂ * (v.2 * v.2)
  proof: rfl

中文:
定理 Q_apply
  条件: (v : R × R)
  结论: Q c₁ c₂ v = c₁ * (v.1 * v.1) + c₂ * (v.2 * v.2)
  证明: rfl
-/
theorem Q_apply (v : R × R) : Q c₁ c₂ v = c₁ * (v.1 * v.1) + c₂ * (v.2 * v.2) :=
  rfl

/-- The quaternion basis vectors within the algebra. -/
@[simps i j k]
/--
Definition of `quaternionBasis` / `quaternionBasis` 的定义

English:
definition quaternionBasis
  signature: : QuaternionAlgebra.Basis (CliffordAlgebra (Q c₁ c₂)) c₁ 0 c₂ where
  body: ι (Q c₁ c₂) (1, 0)
  j := ι (Q c₁ c₂) (0, 1)
  k := ι (Q c₁ c₂) (1, 0) * ι (Q c₁ c₂) (0, 1)
  i_mul_i := by
    rw [ι_sq_scalar]; rw [Q_apply]; rw [← Algebra.algebraMap_eq_smul_one]
    simp
  j_mul_j := by
    rw [ι_sq_scalar]; rw [Q_apply]; rw [← Algebra.algebraMap_eq_smul_one]
    simp
  i_mul_j := rfl
  j_mul_i := by
    rw [zero_smul]; rw [zero_sub]; rw [eq_neg_iff_add_eq_zero]; rw [ι_mul_ι_add_swap]; rw [QuadraticMap.polar]
    simp

中文:
定义 quaternionBasis
  签名: : Quaternion代数.基 (CliffordAlgebra (Q c₁ c₂)) c₁ 0 c₂ where
  定义体: ι (Q c₁ c₂) (1, 0)
  j := ι (Q c₁ c₂) (0, 1)
  k := ι (Q c₁ c₂) (1, 0) * ι (Q c₁ c₂) (0, 1)
  i_mul_i := by
    rw [ι_sq_scalar]; rw [Q_apply]; rw [← Algebra.algebraMap_eq_smul_one]
    simp
  j_mul_j := by
    rw [ι_sq_scalar]; rw [Q_apply]; rw [← Algebra.algebraMap_eq_smul_one]
    simp
  i_mul_j := rfl
  j_mul_i := by
    rw [zero_smul]; rw [zero_sub]; rw [eq_neg_iff_add_eq_zero]; rw [ι_mul_ι_add_swap]; rw [QuadraticMap.polar]
    simp
-/
def quaternionBasis : QuaternionAlgebra.Basis (CliffordAlgebra (Q c₁ c₂)) c₁ 0 c₂ where
  i := ι (Q c₁ c₂) (1, 0)
  j := ι (Q c₁ c₂) (0, 1)
  k := ι (Q c₁ c₂) (1, 0) * ι (Q c₁ c₂) (0, 1)
  i_mul_i := by
    rw [ι_sq_scalar]; rw [Q_apply]; rw [← Algebra.algebraMap_eq_smul_one]
    simp
  j_mul_j := by
    rw [ι_sq_scalar]; rw [Q_apply]; rw [← Algebra.algebraMap_eq_smul_one]
    simp
  i_mul_j := rfl
  j_mul_i := by
    rw [zero_smul]; rw [zero_sub]; rw [eq_neg_iff_add_eq_zero]; rw [ι_mul_ι_add_swap]; rw [QuadraticMap.polar]
    simp

variable {c₁ c₂}

/--
Definition of `toQuaternion` / `toQuaternion` 的定义

English:
definition toQuaternion
  signature: : CliffordAlgebra (Q c₁ c₂) ->ₐ[R] ℍ[R,c₁,0,c₂]
  body: CliffordAlgebra.lift (Q c₁ c₂)
    ⟨{ toFun := fun v => (⟨0, v.1, v.2, 0⟩ : ℍ[R,c₁,0,c₂])
        map_add' := fun v₁ v₂ => by simp
        map_smul' := fun r v => by dsimp; rw [mul_zero] }, fun v => by
      dsimp
      ext
      all_goals dsimp; ring⟩

@[simp]

中文:
定义 toQuaternion
  签名: : CliffordAlgebra (Q c₁ c₂) ->ₐ[R] ℍ[R,c₁,0,c₂]
  定义体: CliffordAlgebra.lift (Q c₁ c₂)
    ⟨{ toFun := fun v => (⟨0, v.1, v.2, 0⟩ : ℍ[R,c₁,0,c₂])
        map_add' := fun v₁ v₂ => by simp
        map_smul' := fun r v => by dsimp; rw [mul_zero] }, fun v => by
      dsimp
      ext
      all_goals dsimp; ring⟩

@[simp]

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.lift, all_goals, map_add, map_smul, mul_zero
-/
def toQuaternion : CliffordAlgebra (Q c₁ c₂) ->ₐ[R] ℍ[R,c₁,0,c₂] :=
  CliffordAlgebra.lift (Q c₁ c₂)
    ⟨{ toFun := fun v => (⟨0, v.1, v.2, 0⟩ : ℍ[R,c₁,0,c₂])
        map_add' := fun v₁ v₂ => by simp
        map_smul' := fun r v => by dsimp; rw [mul_zero] }, fun v => by
      dsimp
      ext
      all_goals dsimp; ring⟩

@[simp]
/--
theorem `toQuaternion_ι` / 定理 `toQuaternion_ι`

English:
theorem toQuaternion_ι
  given: (v : R × R)
  proof: CliffordAlgebra.lift_ι_apply _ _ v

中文:
定理 toQuaternion_ι
  条件: (v : R × R)
  证明: CliffordAlgebra.lift_ι_apply _ _ v

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.lift_
-/
theorem toQuaternion_ι (v : R × R) :
    toQuaternion (ι (Q c₁ c₂) v) = (⟨0, v.1, v.2, 0⟩ : ℍ[R,c₁,0,c₂]) :=
  CliffordAlgebra.lift_ι_apply _ _ v

/--
theorem `toQuaternion_star` / 定理 `toQuaternion_star`

English:
theorem toQuaternion_star
  given: (c : CliffordAlgebra (Q c₁ c₂))
  proof: by
  simp only [CliffordAlgebra.star_def']
  induction c using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι x => simp
  | mul x₁ x₂ hx₁ hx₂ => simp [hx₁, hx₂]
  | add x₁ x₂ hx₁ hx₂ => simp [hx₁, hx₂]

中文:
定理 toQuaternion_star
  条件: (c : CliffordAlgebra (Q c₁ c₂))
  证明: by
  simp only [CliffordAlgebra.star_def']
  induction c using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι x => simp
  | mul x₁ x₂ hx₁ hx₂ => simp [hx₁, hx₂]
  | add x₁ x₂ hx₁ hx₂ => simp [hx₁, hx₂]

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.induction, CliffordAlgebra.star_def, algebraMap, star_def
-/
theorem toQuaternion_star (c : CliffordAlgebra (Q c₁ c₂)) :
    toQuaternion (star c) = star (toQuaternion c) := by
  simp only [CliffordAlgebra.star_def']
  induction c using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι x => simp
  | mul x₁ x₂ hx₁ hx₂ => simp [hx₁, hx₂]
  | add x₁ x₂ hx₁ hx₂ => simp [hx₁, hx₂]

/--
Definition of `ofQuaternion` / `ofQuaternion` 的定义

English:
definition ofQuaternion
  signature: : ℍ[R,c₁,0,c₂] ->ₐ[R] CliffordAlgebra (Q c₁ c₂)
  body: (quaternionBasis c₁ c₂).liftHom

@[simp]

中文:
定义 ofQuaternion
  签名: : ℍ[R,c₁,0,c₂] ->ₐ[R] CliffordAlgebra (Q c₁ c₂)
  定义体: (quaternionBasis c₁ c₂).liftHom

@[simp]

Depends on / 依赖: liftHom, quaternionBasis
-/
def ofQuaternion : ℍ[R,c₁,0,c₂] ->ₐ[R] CliffordAlgebra (Q c₁ c₂) :=
  (quaternionBasis c₁ c₂).liftHom

@[simp]
/--
theorem `ofQuaternion_mk` / 定理 `ofQuaternion_mk`

English:
theorem ofQuaternion_mk
  given: (a₁ a₂ a₃ a₄ : R)
  proof: rfl

@[simp]

中文:
定理 ofQuaternion_mk
  条件: (a₁ a₂ a₃ a₄ : R)
  证明: rfl

@[simp]
-/
theorem ofQuaternion_mk (a₁ a₂ a₃ a₄ : R) :
    ofQuaternion (⟨a₁, a₂, a₃, a₄⟩ : ℍ[R,c₁,0,c₂]) =
      algebraMap R _ a₁ + a₂ • ι (Q c₁ c₂) (1, 0) + a₃ • ι (Q c₁ c₂) (0, 1) +
        a₄ • (ι (Q c₁ c₂) (1, 0) * ι (Q c₁ c₂) (0, 1)) :=
  rfl

@[simp]
/--
theorem `ofQuaternion_comp_toQuaternion` / 定理 `ofQuaternion_comp_toQuaternion`

English:
theorem ofQuaternion_comp_toQuaternion
  proof: by
  ext : 2 <;> (ext; simp)

@[simp]

中文:
定理 ofQuaternion_comp_toQuaternion
  证明: by
  ext : 2 <;> (ext; simp)

@[simp]
-/
theorem ofQuaternion_comp_toQuaternion :
    ofQuaternion.comp toQuaternion = AlgHom.id R (CliffordAlgebra (Q c₁ c₂)) := by
  ext : 2 <;> (ext; simp)

@[simp]
/--
theorem `ofQuaternion_toQuaternion` / 定理 `ofQuaternion_toQuaternion`

English:
theorem ofQuaternion_toQuaternion
  given: (c : CliffordAlgebra (Q c₁ c₂))
  proof: AlgHom.congr_fun ofQuaternion_comp_toQuaternion c

@[simp]

中文:
定理 ofQuaternion_toQuaternion
  条件: (c : CliffordAlgebra (Q c₁ c₂))
  证明: AlgHom.congr_fun ofQuaternion_comp_toQuaternion c

@[simp]

Depends on / 依赖: AlgHom, AlgHom.congr_fun, congr_fun, ofQuaternion_comp_toQuaternion
-/
theorem ofQuaternion_toQuaternion (c : CliffordAlgebra (Q c₁ c₂)) :
    ofQuaternion (toQuaternion c) = c :=
  AlgHom.congr_fun ofQuaternion_comp_toQuaternion c

@[simp]
/--
theorem `toQuaternion_comp_ofQuaternion` / 定理 `toQuaternion_comp_ofQuaternion`

English:
theorem toQuaternion_comp_ofQuaternion
  proof: by
  ext : 1 <;> simp

@[simp]

中文:
定理 toQuaternion_comp_ofQuaternion
  证明: by
  ext : 1 <;> simp

@[simp]
-/
theorem toQuaternion_comp_ofQuaternion :
    toQuaternion.comp ofQuaternion = AlgHom.id R ℍ[R,c₁,0,c₂] := by
  ext : 1 <;> simp

@[simp]
/--
theorem `toQuaternion_ofQuaternion` / 定理 `toQuaternion_ofQuaternion`

English:
theorem toQuaternion_ofQuaternion
  given: (q : ℍ[R,c₁,0,c₂])
  statement: toQuaternion (ofQuaternion q) = q
  proof: AlgHom.congr_fun toQuaternion_comp_ofQuaternion q

中文:
定理 toQuaternion_ofQuaternion
  条件: (q : ℍ[R,c₁,0,c₂])
  结论: toQuaternion (ofQuaternion q) = q
  证明: AlgHom.congr_fun toQuaternion_comp_ofQuaternion q

Depends on / 依赖: AlgHom, AlgHom.congr_fun, congr_fun, toQuaternion_comp_ofQuaternion
-/
theorem toQuaternion_ofQuaternion (q : ℍ[R,c₁,0,c₂]) : toQuaternion (ofQuaternion q) = q :=
  AlgHom.congr_fun toQuaternion_comp_ofQuaternion q

/-- The clifford algebra over `CliffordAlgebraQuaternion.Q c₁ c₂` is isomorphic as an `R`-algebra
to `ℍ[R,c₁,c₂]`. -/
@[simps!]
/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : CliffordAlgebra (Q c₁ c₂) ≃ₐ[R] ℍ[R,c₁,0,c₂]
  body: AlgEquiv.ofAlgHom toQuaternion ofQuaternion toQuaternion_comp_ofQuaternion
    ofQuaternion_comp_toQuaternion

中文:
定义 equiv
  签名: : CliffordAlgebra (Q c₁ c₂) ≃ₐ[R] ℍ[R,c₁,0,c₂]
  定义体: AlgEquiv.ofAlgHom toQuaternion ofQuaternion toQuaternion_comp_ofQuaternion
    ofQuaternion_comp_toQuaternion
-/
protected def equiv : CliffordAlgebra (Q c₁ c₂) ≃ₐ[R] ℍ[R,c₁,0,c₂] :=
  AlgEquiv.ofAlgHom toQuaternion ofQuaternion toQuaternion_comp_ofQuaternion
    ofQuaternion_comp_toQuaternion

/-- The quaternion conjugate maps to the "clifford conjugate" (aka `star`). -/
@[simp]
/--
theorem `ofQuaternion_star` / 定理 `ofQuaternion_star`

English:
theorem ofQuaternion_star
  given: (q : ℍ[R,c₁,0,c₂])
  statement: ofQuaternion (star q) = star (ofQuaternion q)
  proof: CliffordAlgebraQuaternion.equiv.injective by
    rw [equiv_apply]; rw [equiv_apply]; rw [toQuaternion_star]; rw [toQuaternion_ofQuaternion]; rw [toQuaternion_ofQuaternion]

中文:
定理 ofQuaternion_star
  条件: (q : ℍ[R,c₁,0,c₂])
  结论: ofQuaternion (star q) = star (ofQuaternion q)
  证明: CliffordAlgebraQuaternion.equiv.injective by
    rw [equiv_apply]; rw [equiv_apply]; rw [toQuaternion_star]; rw [toQuaternion_ofQuaternion]; rw [toQuaternion_ofQuaternion]

Depends on / 依赖: CliffordAlgebraQuaternion, CliffordAlgebraQuaternion.equiv.injective, equiv_apply, injective, toQuaternion_ofQuaternion, toQuaternion_star
-/
theorem ofQuaternion_star (q : ℍ[R,c₁,0,c₂]) : ofQuaternion (star q) = star (ofQuaternion q) :=
CliffordAlgebraQuaternion.equiv.injective by
    rw [equiv_apply]; rw [equiv_apply]; rw [toQuaternion_star]; rw [toQuaternion_ofQuaternion]; rw [toQuaternion_ofQuaternion]

end CliffordAlgebraQuaternion

/-! ### The clifford algebra isomorphic to the dual numbers -/


namespace CliffordAlgebraDualNumber

open scoped DualNumber

open DualNumber TrivSqZeroExt

variable {R : Type*} [CommRing R]

/--
theorem `ι_mul_ι` / 定理 `ι_mul_ι`

English:
theorem ι_mul_ι
  given: (r₁ r₂)
  statement: ι (0 : QuadraticForm R R) r₁ * ι (0 : QuadraticForm R R) r₂ = 0
  proof: by
  rw [← mul_one r₁]; rw [← mul_one r₂]; rw [← smul_eq_mul r₁]; rw [← smul_eq_mul r₂]; rw [map_smul]; rw [map_smul]; rw [smul_mul_smul_comm]; rw [ι_sq_scalar]; rw [zero_apply]; rw [map_zero]; rw [smul_zero]

中文:
定理 ι_mul_ι
  条件: (r₁ r₂)
  结论: ι (0 : QuadraticForm R R) r₁ * ι (0 : QuadraticForm R R) r₂ = 0
  证明: by
  rw [← mul_one r₁]; rw [← mul_one r₂]; rw [← smul_eq_mul r₁]; rw [← smul_eq_mul r₂]; rw [map_smul]; rw [map_smul]; rw [smul_mul_smul_comm]; rw [ι_sq_scalar]; rw [zero_apply]; rw [map_zero]; rw [smul_zero]

Depends on / 依赖: map_smul, map_zero, mul_one, smul_eq_mul, smul_mul_smul_comm, smul_zero, zero_apply
-/
theorem ι_mul_ι (r₁ r₂) : ι (0 : QuadraticForm R R) r₁ * ι (0 : QuadraticForm R R) r₂ = 0 := by
  rw [← mul_one r₁]; rw [← mul_one r₂]; rw [← smul_eq_mul r₁]; rw [← smul_eq_mul r₂]; rw [map_smul]; rw [map_smul]; rw [smul_mul_smul_comm]; rw [ι_sq_scalar]; rw [zero_apply]; rw [map_zero]; rw [smul_zero]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : CliffordAlgebra (0 : QuadraticForm R R) ≃ₐ[R] R[ε]
  body: AlgEquiv.ofAlgHom
    (CliffordAlgebra.lift (0 : QuadraticForm R R) ⟨inrHom R _, fun m => inr_mul_inr _ m m⟩)
    (DualNumber.lift ⟨
      (Algebra.ofId _ _, ι (R := R) _ 1),
      ι_mul_ι (1 : R) 1,
      fun _ => (Algebra.commutes _ _).symm⟩)
    (by ext : 1; simp) (by ext : 2; simp)

中文:
定义 equiv
  签名: : CliffordAlgebra (0 : QuadraticForm R R) ≃ₐ[R] R[ε]
  定义体: AlgEquiv.ofAlgHom
    (CliffordAlgebra.lift (0 : QuadraticForm R R) ⟨inrHom R _, fun m => inr_mul_inr _ m m⟩)
    (DualNumber.lift ⟨
      (Algebra.ofId _ _, ι (R := R) _ 1),
      ι_mul_ι (1 : R) 1,
      fun _ => (Algebra.commutes _ _).symm⟩)
    (by ext : 1; simp) (by ext : 2; simp)
-/
protected def equiv : CliffordAlgebra (0 : QuadraticForm R R) ≃ₐ[R] R[ε] :=
  AlgEquiv.ofAlgHom
    (CliffordAlgebra.lift (0 : QuadraticForm R R) ⟨inrHom R _, fun m => inr_mul_inr _ m m⟩)
    (DualNumber.lift ⟨
      (Algebra.ofId _ _, ι (R := R) _ 1),
      ι_mul_ι (1 : R) 1,
      fun _ => (Algebra.commutes _ _).symm⟩)
    (by ext : 1; simp) (by ext : 2; simp)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `equiv_ι` / 定理 `equiv_ι`

English:
theorem equiv_ι
  given: (r : R)
  statement: CliffordAlgebraDualNumber.equiv (ι (R := R) _ r) = r • ε
  proof: by
  dsimp [CliffordAlgebraDualNumber.equiv, AlgEquiv.ofAlgHom]
  exact (lift_ι_apply _ _ r).trans (inr_eq_smul_eps _)

中文:
定理 equiv_ι
  条件: (r : R)
  结论: CliffordAlgebraDualNumber.equiv (ι (R := R) _ r) = r • ε
  证明: by
  dsimp [CliffordAlgebraDualNumber.equiv, AlgEquiv.ofAlgHom]
  exact (lift_ι_apply _ _ r).trans (inr_eq_smul_eps _)

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, CliffordAlgebraDualNumber, CliffordAlgebraDualNumber.equiv, inr_eq_smul_eps, ofAlgHom
-/
theorem equiv_ι (r : R) : CliffordAlgebraDualNumber.equiv (ι (R := R) _ r) = r • ε := by
  dsimp [CliffordAlgebraDualNumber.equiv, AlgEquiv.ofAlgHom]
  exact (lift_ι_apply _ _ r).trans (inr_eq_smul_eps _)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `equiv_symm_eps` / 定理 `equiv_symm_eps`

English:
theorem equiv_symm_eps
  proof: by
  dsimp [CliffordAlgebraDualNumber.equiv, AlgEquiv.ofAlgHom]
  exact DualNumber.lift_apply_eps _

中文:
定理 equiv_symm_eps
  证明: by
  dsimp [CliffordAlgebraDualNumber.equiv, AlgEquiv.ofAlgHom]
  exact DualNumber.lift_apply_eps _

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, CliffordAlgebraDualNumber, CliffordAlgebraDualNumber.equiv, DualNumber, DualNumber.lift_apply_eps, lift_apply_eps, ofAlgHom
-/
theorem equiv_symm_eps :
    CliffordAlgebraDualNumber.equiv.symm (eps : R[ε]) = ι (0 : QuadraticForm R R) 1 := by
  dsimp [CliffordAlgebraDualNumber.equiv, AlgEquiv.ofAlgHom]
  exact DualNumber.lift_apply_eps _

end CliffordAlgebraDualNumber
