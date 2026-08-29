/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.Algebra.Ring.Subring.Units

/-!
# The General Linear group $GL(n, R)$

This file defines the elements of the General Linear group `Matrix.GeneralLinearGroup n R`,
consisting of all invertible `n` by `n` `R`-matrices.

## Main definitions

* `Matrix.GeneralLinearGroup` is the type of matrices over R which are units in the matrix ring.
* `Matrix.GLPos` gives the subgroup of matrices with
  positive determinant (over a linear ordered ring).

## Tags

matrix group, group, matrix inverse
-/

@[expose] public section


namespace Matrix

universe u v

open Matrix

open LinearMap

/--
Definition of `GeneralLinearGroup` / `GeneralLinearGroup` 的定义

English:
abbreviation GeneralLinearGroup
  signature: (n : Type u) (R : Type v) [DecidableEq n] [Fintype n] [Semiring R]
  body: (Matrix n n R)ˣ

@[inherit_doc] notation "GL" => GeneralLinearGroup

中文:
缩写 GeneralLinearGroup
  签名: (n : 类型u) (R : 类型v) [DecidableEq n] [有限类型 n] [半环 R]
  定义体: (Matrix n n R)ˣ

@[inherit_doc] notation "GL" => GeneralLinearGroup

Depends on / 依赖: Matrix
-/
abbrev GeneralLinearGroup (n : Type u) (R : Type v) [DecidableEq n] [Fintype n] [Semiring R] :
    Type _ :=
  (Matrix n n R)ˣ

@[inherit_doc] notation "GL" => GeneralLinearGroup

namespace GeneralLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v}

variable (n) in
/--
Definition of `scalar` / `scalar` 的定义

English:
definition scalar
  signature: [Semiring R]
  body: Units.map (Matrix.scalar n).toMonoidHom

中文:
定义 scalar
  签名: [半环 R]
  定义体: Units.map (Matrix.scalar n).toMonoidHom

Depends on / 依赖: Matrix, Matrix.scalar, Units.map, scalar, toMonoidHom
-/
def scalar [Semiring R] : Rˣ ->* GL n R :=
  Units.map (Matrix.scalar n).toMonoidHom

section CoeFnInstance

/--
Instance `instCoeFun` / 实例 `instCoeFun`

English:
instance instCoeFun
  signature: [Semiring R]
  body: (A : Matrix n n R)

@[simp]

中文:
实例 instCoeFun
  签名: [半环 R]
  定义体: (A : Matrix n n R)

@[simp]

Depends on / 依赖: Matrix
-/
instance instCoeFun [Semiring R] : CoeFun (GL n R) fun _ => n -> n -> R where
  coe A := (A : Matrix n n R)

@[simp]
/--
lemma `coe_scalar` / 引理 `coe_scalar`

English:
lemma coe_scalar
  given: [Semiring R] (u : Rˣ)
  statement: ↑(scalar n u) = Matrix.scalar n u.1
  proof: rfl

中文:
引理 coe_scalar
  条件: [半环 R] (u : Rˣ)
  结论: ↑(scalar n u) = 矩阵.scalar n u.1
  证明: rfl
-/
lemma coe_scalar [Semiring R] (u : Rˣ) : ↑(scalar n u) = Matrix.scalar n u.1 := rfl

end CoeFnInstance

variable [CommRing R]

/--
lemma `scalar_commute` / 引理 `scalar_commute`

English:
lemma scalar_commute
  given: (u : Rˣ) (A : GL n R)
  statement: scalar n u * A = A * scalar n u
  proof: by
  ext : 1
  rw [Units.val_mul]; rw [Units.val_mul]; rw [coe_scalar]; rw [Matrix.scalar_comm _ (Commute.all _)]

中文:
引理 scalar_commute
  条件: (u : Rˣ) (A : GL n R)
  结论: scalar n u * A = A * scalar n u
  证明: by
  ext : 1
  rw [Units.val_mul]; rw [Units.val_mul]; rw [coe_scalar]; rw [Matrix.scalar_comm _ (Commute.all _)]

Depends on / 依赖: Commute, Commute.all, Matrix, Matrix.scalar_comm, Units.val_mul, coe_scalar, scalar_comm, val_mul
-/
lemma scalar_commute (u : Rˣ) (A : GL n R) : scalar n u * A = A * scalar n u := by
  ext : 1
  rw [Units.val_mul]; rw [Units.val_mul]; rw [coe_scalar]; rw [Matrix.scalar_comm _ (Commute.all _)]

/-- The determinant of a unit matrix is itself a unit. -/
@[simps]
/--
Definition of `det` / `det` 的定义

English:
definition det
  signature: : GL n R ->* Rˣ where
  body: { val := (↑A : Matrix n n R).det
      inv := (↑A⁻¹ : Matrix n n R).det
      val_inv := by rw [← det_mul, A.mul_inv, det_one]
      inv_val := by rw [← det_mul, A.inv_mul, det_one] }
  map_one' := Units.ext det_one
map_mul' _ _ := Units.ext det_mul _ _

中文:
定义 det
  签名: : GL n R ->* Rˣ where
  定义体: { val := (↑A : Matrix n n R).det
      inv := (↑A⁻¹ : Matrix n n R).det
      val_inv := by rw [← det_mul, A.mul_inv, det_one]
      inv_val := by rw [← det_mul, A.inv_mul, det_one] }
  map_one' := Units.ext det_one
map_mul' _ _ := Units.ext det_mul _ _

Depends on / 依赖: A.inv_mul, A.mul_inv, Matrix, Units.ext, det_mul, det_one, inv_mul, inv_val, map_mul, map_one, mul_inv, val_inv
-/
def det : GL n R ->* Rˣ where
  toFun A :=
    { val := (↑A : Matrix n n R).det
      inv := (↑A⁻¹ : Matrix n n R).det
      val_inv := by rw [← det_mul, A.mul_inv, det_one]
      inv_val := by rw [← det_mul, A.inv_mul, det_one] }
  map_one' := Units.ext det_one
map_mul' _ _ := Units.ext det_mul _ _

/--
lemma `det_ne_zero` / 引理 `det_ne_zero`

English:
lemma det_ne_zero
  given: [Nontrivial R] (g : GL n R)
  statement: g.val.det != 0
  proof: g.det.ne_zero

@[simp]

中文:
引理 det_ne_zero
  条件: [非平凡 R] (g : GL n R)
  结论: g.val.det != 0
  证明: g.det.ne_zero

@[simp]

Depends on / 依赖: g.det.ne_zero, ne_zero
-/
lemma det_ne_zero [Nontrivial R] (g : GL n R) : g.val.det != 0 :=
  g.det.ne_zero

@[simp]
/--
theorem `det_scalar` / 定理 `det_scalar`

English:
theorem det_scalar
  given: (u : Rˣ)
  statement: det (scalar n u) = u ^ Fintype.card n
  proof: by
  ext
  simp

中文:
定理 det_scalar
  条件: (u : Rˣ)
  结论: det (scalar n u) = u ^ 有限类型.card n
  证明: by
  ext
  simp
-/
theorem det_scalar (u : Rˣ) : det (scalar n u) = u ^ Fintype.card n := by
  ext
  simp

/--
lemma `det_surjective` / 引理 `det_surjective`

English:
lemma det_surjective
  given: [Nonempty n]
  statement: Function.Surjective (det : GL n R -> Rˣ)
  proof: fun r => by
  obtain ⟨i⟩ := ‹Nonempty n›
  refine ⟨⟨diagonal fun j => if j = i then r else 1, diagonal fun j => if j = i then r⁻¹.1 else 1,
    ?_, ?_⟩, by simp [det]⟩
  <;> simp only [diagonal_mul_diagonal, mul_ite, ite_mul, Units.mul_inv, one_mul, mul_one,
      diagonal_eq_one]
  <;> funext j <;>

中文:
引理 det_surjective
  条件: [非空 n]
  结论: 函数.满射 (det : GL n R -> Rˣ)
  证明: fun r => by
  obtain ⟨i⟩ := ‹Nonempty n›
  refine ⟨⟨diagonal fun j => if j = i then r else 1, diagonal fun j => if j = i then r⁻¹.1 else 1,
    ?_, ?_⟩, by simp [det]⟩
  <;> simp only [diagonal_mul_diagonal, mul_ite, ite_mul, Units.mul_inv, one_mul, mul_one,
      diagonal_eq_one]
  <;> funext j <;>

Depends on / 依赖: Nonempty, Units.mul_inv, diagonal, diagonal_eq_one, diagonal_mul_diagonal, ite_mul, mul_inv, mul_ite, mul_one, one_mul, split_ifs
-/
lemma det_surjective [Nonempty n] : Function.Surjective (det : GL n R -> Rˣ) := fun r => by
  obtain ⟨i⟩ := ‹Nonempty n›
  refine ⟨⟨diagonal fun j => if j = i then r else 1, diagonal fun j => if j = i then r⁻¹.1 else 1,
    ?_, ?_⟩, by simp [det]⟩
  <;> simp only [diagonal_mul_diagonal, mul_ite, ite_mul, Units.mul_inv, one_mul, mul_one,
      diagonal_eq_one]
  <;> funext j <;> split_ifs <;> simp

/--
Definition of `toLin` / `toLin` 的定义

English:
definition toLin
  signature: : GL n R ≃* LinearMap.GeneralLinearGroup R (n -> R)
  body: Units.mapEquiv toLinAlgEquiv'.toMulEquiv

中文:
定义 toLin
  签名: : GL n R ≃* 线性映射.GeneralLinearGroup R (n -> R)
  定义体: Units.mapEquiv toLinAlgEquiv'.toMulEquiv

Depends on / 依赖: Units.mapEquiv, mapEquiv, toLinAlgEquiv, toMulEquiv
-/
def toLin : GL n R ≃* LinearMap.GeneralLinearGroup R (n -> R) :=
  Units.mapEquiv toLinAlgEquiv'.toMulEquiv

/--
Definition of `toLin'` / `toLin'` 的定义

English:
definition toLin'
  body: toLin.trans LinearMap.GeneralLinearGroup.congrLinearEquiv b.equivFun.symm

中文:
定义 toLin'
  定义体: toLin.trans LinearMap.GeneralLinearGroup.congrLinearEquiv b.equivFun.symm

Depends on / 依赖: GeneralLinearGroup, LinearMap, LinearMap.GeneralLinearGroup.congrLinearEquiv, b.equivFun.symm, congrLinearEquiv, equivFun, toLin.trans
-/
noncomputable def toLin'
    {V : Type*} [AddCommGroup V] [Module R V] (b : Module.Basis n R V) :
    GL n R ≃* LinearMap.GeneralLinearGroup R V :=
toLin.trans LinearMap.GeneralLinearGroup.congrLinearEquiv b.equivFun.symm

/--
lemma `toLin'_apply` / 引理 `toLin'_apply`

English:
lemma toLin'_apply
  statement: {V : Type*} [AddCommGroup V] [Module R V]
  proof: by
  simp [toLin', toLin, Fintype.linearCombination_apply, MulEquiv.trans_apply]

中文:
引理 toLin'_apply
  结论: {V : 类型} [加法交换群 V] [模 R V]
  证明: by
  simp [toLin', toLin, Fintype.linearCombination_apply, MulEquiv.trans_apply]
-/
lemma toLin'_apply {V : Type*} [AddCommGroup V] [Module R V]
    (b : Module.Basis n R V) (M : GL n R) (v : V) :
    (toLin' b M).toLinearEquiv v = Fintype.linearCombination R ⇑b (↑M *ᵥ (b.repr v)) := by
  simp [toLin', toLin, Fintype.linearCombination_apply, MulEquiv.trans_apply]

/-- Given a matrix with invertible determinant, we get an element of `GL n R`. -/
@[simps! val]
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (A : Matrix n n R) (_ : Invertible (Matrix.det A))
  body: unitOfDetInvertible A

中文:
定义 mk'
  签名: (A : 矩阵 n n R) (_ : 可逆 (矩阵.det A))
  定义体: unitOfDetInvertible A

Depends on / 依赖: unitOfDetInvertible
-/
def mk' (A : Matrix n n R) (_ : Invertible (Matrix.det A)) : GL n R :=
  unitOfDetInvertible A

/-- Given a matrix with unit determinant, we get an element of `GL n R`. -/
@[simps! val]
/--
Definition of `mk''` / `mk''` 的定义

English:
definition mk''
  signature: (A : Matrix n n R) (h : IsUnit (Matrix.det A))
  body: nonsingInvUnit A h

中文:
定义 mk''
  签名: (A : 矩阵 n n R) (h : 是单位 (矩阵.det A))
  定义体: nonsingInvUnit A h

Depends on / 依赖: nonsingInvUnit
-/
noncomputable def mk'' (A : Matrix n n R) (h : IsUnit (Matrix.det A)) : GL n R :=
  nonsingInvUnit A h

/-- Given a matrix with non-zero determinant over a field, we get an element of `GL n K`. -/
@[simps! val]
/--
Definition of `mkOfDetNeZero` / `mkOfDetNeZero` 的定义

English:
definition mkOfDetNeZero
  signature: {K : Type*} [Field K] (A : Matrix n n K) (h : Matrix.det A != 0)
  body: mk' A (invertibleOfNonzero h)

中文:
定义 mkOfDetNeZero
  签名: {K : 类型} [域 K] (A : 矩阵 n n K) (h : 矩阵.det A != 0)
  定义体: mk' A (invertibleOfNonzero h)

Depends on / 依赖: invertibleOfNonzero
-/
def mkOfDetNeZero {K : Type*} [Field K] (A : Matrix n n K) (h : Matrix.det A != 0) : GL n K :=
  mk' A (invertibleOfNonzero h)

/--
theorem `ext_iff` / 定理 `ext_iff`

English:
theorem ext_iff
  given: (A B : GL n R)
  statement: A = B ↔ forall i j, (A : Matrix n n R) i j = (B : Matrix n n R) i j
  proof: Units.ext_iff.trans Matrix.ext_iff.symm

中文:
定理 ext_iff
  条件: (A B : GL n R)
  结论: A = B ↔ 对任意 i j, (A : 矩阵 n n R) i j = (B : 矩阵 n n R) i j
  证明: Units.ext_iff.trans Matrix.ext_iff.symm

Depends on / 依赖: Matrix, Matrix.ext_iff.symm, Units.ext_iff.trans, ext_iff
-/
theorem ext_iff (A B : GL n R) : A = B ↔ forall i j, (A : Matrix n n R) i j = (B : Matrix n n R) i j :=
  Units.ext_iff.trans Matrix.ext_iff.symm

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃A B
  statement: GL n R⦄ (h : forall i j, (A : Matrix n n R) i j = (B : Matrix n n R) i j) : A = B
  proof: Units.ext Matrix.ext h

中文:
定理 ext
  条件: ⦃A B
  结论: GL n R⦄ (h : 对任意 i j, (A : 矩阵 n n R) i j = (B : 矩阵 n n R) i j) : A = B
  证明: Units.ext Matrix.ext h

Depends on / 依赖: Matrix, Matrix.ext, Units.ext
-/
theorem ext ⦃A B : GL n R⦄ (h : forall i j, (A : Matrix n n R) i j = (B : Matrix n n R) i j) : A = B :=
Units.ext Matrix.ext h

section CoeLemmas

variable (A B : GL n R)

@[simp]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  statement: ↑(A * B) = (↑A : Matrix n n R) * (↑B : Matrix n n R)
  proof: rfl

@[simp]

中文:
定理 coe_mul
  结论: ↑(A * B) = (↑A : 矩阵 n n R) * (↑B : 矩阵 n n R)
  证明: rfl

@[simp]
-/
theorem coe_mul : ↑(A * B) = (↑A : Matrix n n R) * (↑B : Matrix n n R) :=
  rfl

@[simp]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ↑(1 : GL n R) = (1 : Matrix n n R)
  proof: rfl

中文:
定理 coe_one
  结论: ↑(1 : GL n R) = (1 : 矩阵 n n R)
  证明: rfl
-/
theorem coe_one : ↑(1 : GL n R) = (1 : Matrix n n R) :=
  rfl

/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  statement: ↑A⁻¹ = (↑A : Matrix n n R)⁻¹
  proof: letI := A.invertible
  invOf_eq_nonsing_inv (↑A : Matrix n n R)

@[simp]

中文:
定理 coe_inv
  结论: ↑A⁻¹ = (↑A : 矩阵 n n R)⁻¹
  证明: letI := A.invertible
  invOf_eq_nonsing_inv (↑A : Matrix n n R)

@[simp]

Depends on / 依赖: A.invertible, Matrix, invOf_eq_nonsing_inv, invertible
-/
theorem coe_inv : ↑A⁻¹ = (↑A : Matrix n n R)⁻¹ :=
  letI := A.invertible
  invOf_eq_nonsing_inv (↑A : Matrix n n R)

@[simp]
/--
theorem `coe_toLin` / 定理 `coe_toLin`

English:
theorem coe_toLin
  statement: (toLin A : (n -> R) ->ₗ[R] n -> R) = Matrix.mulVecLin A
  proof: rfl

@[simp]

中文:
定理 coe_toLin
  结论: (toLin A : (n -> R) ->ₗ[R] n -> R) = 矩阵.mulVecLin A
  证明: rfl

@[simp]
-/
theorem coe_toLin : (toLin A : (n -> R) ->ₗ[R] n -> R) = Matrix.mulVecLin A :=
  rfl

@[simp]
/--
theorem `toLin_apply` / 定理 `toLin_apply`

English:
theorem toLin_apply
  given: (v : n -> R)
  statement: (toLin A : _ -> n -> R) v = Matrix.mulVecLin A v
  proof: rfl

中文:
定理 toLin_apply
  条件: (v : n -> R)
  结论: (toLin A : _ -> n -> R) v = 矩阵.mulVecLin A v
  证明: rfl
-/
theorem toLin_apply (v : n -> R) : (toLin A : _ -> n -> R) v = Matrix.mulVecLin A v :=
  rfl

end CoeLemmas

variable {S T : Type*} [CommRing S] [CommRing T]

/-- A ring homomorphism ``f : R →+* S`` induces a homomorphism ``GLₙ(f) : GLₙ(R) →* GLₙ(S)``. -/
@[simps! apply_val]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : R ->+* S)
  body: Units.map (RingHom.mapMatrix f).toMonoidHom

@[simp]

中文:
定义 map
  签名: (f : R ->+* S)
  定义体: Units.map (RingHom.mapMatrix f).toMonoidHom

@[simp]

Depends on / 依赖: RingHom, RingHom.mapMatrix, Units.map, mapMatrix, toMonoidHom
-/
def map (f : R ->+* S) : GL n R ->* GL n S := Units.map (RingHom.mapMatrix f).toMonoidHom

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: map (RingHom.id R) = MonoidHom.id (GL n R)
  proof: rfl

@[simp]

中文:
定理 map_id
  结论: map (环态射.id R) = 幺半群态射.id (GL n R)
  证明: rfl

@[simp]
-/
theorem map_id : map (RingHom.id R) = MonoidHom.id (GL n R) :=
  rfl

@[simp]
/--
lemma `map_apply` / 引理 `map_apply`

English:
lemma map_apply
  given: (f : R ->+* S) (i j : n) (g : GL n R)
  statement: map f g i j = f (g i j)
  proof: by
  rfl

@[simp]

中文:
引理 map_apply
  条件: (f : R ->+* S) (i j : n) (g : GL n R)
  结论: map f g i j = f (g i j)
  证明: by
  rfl

@[simp]
-/
protected lemma map_apply (f : R ->+* S) (i j : n) (g : GL n R) : map f g i j = f (g i j) := by
  rfl

@[simp]
/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: (f : T ->+* R) (g : R ->+* S)
  proof: rfl

@[simp]

中文:
定理 map_comp
  条件: (f : T ->+* R) (g : R ->+* S)
  证明: rfl

@[simp]
-/
theorem map_comp (f : T ->+* R) (g : R ->+* S) :
    map (g.comp f) = (map g).comp (map (n := n) f) :=
  rfl

@[simp]
/--
theorem `map_comp_apply` / 定理 `map_comp_apply`

English:
theorem map_comp_apply
  given: (f : T ->+* R) (g : R ->+* S) (x : GL n T)
  proof: rfl

中文:
定理 map_comp_apply
  条件: (f : T ->+* R) (g : R ->+* S) (x : GL n T)
  证明: rfl
-/
theorem map_comp_apply (f : T ->+* R) (g : R ->+* S) (x : GL n T) :
    (map g).comp (map f) x = map g (map f x) :=
  rfl

variable (f : R ->+* S)

@[simp]
/--
lemma `map_one` / 引理 `map_one`

English:
lemma map_one
  statement: map f (1 : GL n R) = 1
  proof: by
  simp only [map_one]

中文:
引理 map_one
  结论: map f (1 : GL n R) = 1
  证明: by
  simp only [map_one]
-/
protected lemma map_one : map f (1 : GL n R) = 1 := by
  simp only [map_one]

/--
lemma `map_mul` / 引理 `map_mul`

English:
lemma map_mul
  given: (g h : GL n R)
  statement: map f (g * h) = map f g * map f h
  proof: by
  simp only [map_mul]

中文:
引理 map_mul
  条件: (g h : GL n R)
  结论: map f (g * h) = map f g * map f h
  证明: by
  simp only [map_mul]
-/
protected lemma map_mul (g h : GL n R) : map f (g * h) = map f g * map f h := by
  simp only [map_mul]

/--
lemma `map_inv` / 引理 `map_inv`

English:
lemma map_inv
  given: (g : GL n R)
  statement: map f g⁻¹ = (map f g)⁻¹
  proof: by
  simp only [map_inv]

中文:
引理 map_inv
  条件: (g : GL n R)
  结论: map f g⁻¹ = (map f g)⁻¹
  证明: by
  simp only [map_inv]
-/
protected lemma map_inv (g : GL n R) : map f g⁻¹ = (map f g)⁻¹ := by
  simp only [map_inv]

/--
lemma `map_det` / 引理 `map_det`

English:
lemma map_det
  given: (g : GL n R)
  statement: Matrix.GeneralLinearGroup.det (map f g) =
  proof: by
  ext
  simp only [map,
    Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, MonoidHom.coe_coe]
  exact Eq.symm (RingHom.map_det f g.1)

中文:
引理 map_det
  条件: (g : GL n R)
  结论: 矩阵.GeneralLinearGroup.det (map f g) =
  证明: by
  ext
  simp only [map,
    Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, MonoidHom.coe_coe]
  exact Eq.symm (RingHom.map_det f g.1)
-/
protected lemma map_det (g : GL n R) : Matrix.GeneralLinearGroup.det (map f g) =
    Units.map f (Matrix.GeneralLinearGroup.det g) := by
  ext
  simp only [map,
    Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, MonoidHom.coe_coe]
  exact Eq.symm (RingHom.map_det f g.1)

/--
lemma `map_mul_map_inv` / 引理 `map_mul_map_inv`

English:
lemma map_mul_map_inv
  given: (g : GL n R)
  statement: map f g * map f g⁻¹ = 1
  proof: by
  simp only [map_inv, mul_inv_cancel]

中文:
引理 map_mul_map_inv
  条件: (g : GL n R)
  结论: map f g * map f g⁻¹ = 1
  证明: by
  simp only [map_inv, mul_inv_cancel]

Depends on / 依赖: map_inv, mul_inv_cancel
-/
lemma map_mul_map_inv (g : GL n R) : map f g * map f g⁻¹ = 1 := by
  simp only [map_inv, mul_inv_cancel]

/--
lemma `map_inv_mul_map` / 引理 `map_inv_mul_map`

English:
lemma map_inv_mul_map
  given: (g : GL n R)
  statement: map f g⁻¹ * map f g = 1
  proof: by
  simp only [map_inv, inv_mul_cancel]

@[simp]

中文:
引理 map_inv_mul_map
  条件: (g : GL n R)
  结论: map f g⁻¹ * map f g = 1
  证明: by
  simp only [map_inv, inv_mul_cancel]

@[simp]

Depends on / 依赖: inv_mul_cancel, map_inv
-/
lemma map_inv_mul_map (g : GL n R) : map f g⁻¹ * map f g = 1 := by
  simp only [map_inv, inv_mul_cancel]

@[simp]
/--
lemma `coe_map_mul_map_inv` / 引理 `coe_map_mul_map_inv`

English:
lemma coe_map_mul_map_inv
  given: (g : GL n R)
  statement: g.val.map f * g.val⁻¹.map f = 1
  proof: by
  rw [← Matrix.map_mul]
  simp only [isUnits_det_units, mul_nonsing_inv, map_zero, map_one, Matrix.map_one]

@[simp]

中文:
引理 coe_map_mul_map_inv
  条件: (g : GL n R)
  结论: g.val.map f * g.val⁻¹.map f = 1
  证明: by
  rw [← Matrix.map_mul]
  simp only [isUnits_det_units, mul_nonsing_inv, map_zero, map_one, Matrix.map_one]

@[simp]

Depends on / 依赖: Matrix, Matrix.map_mul, Matrix.map_one, isUnits_det_units, map_mul, map_one, map_zero, mul_nonsing_inv
-/
lemma coe_map_mul_map_inv (g : GL n R) : g.val.map f * g.val⁻¹.map f = 1 := by
  rw [← Matrix.map_mul]
  simp only [isUnits_det_units, mul_nonsing_inv, map_zero, map_one, Matrix.map_one]

@[simp]
/--
lemma `coe_map_inv_mul_map` / 引理 `coe_map_inv_mul_map`

English:
lemma coe_map_inv_mul_map
  given: (g : GL n R)
  statement: g.val⁻¹.map f * g.val.map f = 1
  proof: by
  rw [← Matrix.map_mul]
  simp only [isUnits_det_units, nonsing_inv_mul, map_zero, map_one, Matrix.map_one]

中文:
引理 coe_map_inv_mul_map
  条件: (g : GL n R)
  结论: g.val⁻¹.map f * g.val.map f = 1
  证明: by
  rw [← Matrix.map_mul]
  simp only [isUnits_det_units, nonsing_inv_mul, map_zero, map_one, Matrix.map_one]

Depends on / 依赖: Matrix, Matrix.map_mul, Matrix.map_one, isUnits_det_units, map_mul, map_one, map_zero, nonsing_inv_mul
-/
lemma coe_map_inv_mul_map (g : GL n R) : g.val⁻¹.map f * g.val.map f = 1 := by
  rw [← Matrix.map_mul]
  simp only [isUnits_det_units, nonsing_inv_mul, map_zero, map_one, Matrix.map_one]

/--
lemma `map_scalar` / 引理 `map_scalar`

English:
lemma map_scalar
  given: (u : Rˣ)
  statement: map f (scalar n u) = scalar n (Units.map f u)
  proof: by
  ext
  simp [Matrix.diagonal_apply]
  split <;> simp

中文:
引理 map_scalar
  条件: (u : Rˣ)
  结论: map f (scalar n u) = scalar n (单位群.map f u)
  证明: by
  ext
  simp [Matrix.diagonal_apply]
  split <;> simp

Depends on / 依赖: Matrix, Matrix.diagonal_apply, diagonal_apply
-/
lemma map_scalar (u : Rˣ) : map f (scalar n u) = scalar n (Units.map f u) := by
  ext
  simp [Matrix.diagonal_apply]
  split <;> simp

section kronecker
variable {R m : Type*} [CommSemiring R] [Fintype m] [DecidableEq m]

open scoped Kronecker

/--
Definition of `kronecker` / `kronecker` 的定义

English:
definition kronecker
  signature: (x : GL n R) (y : GL m R)
  body: x otimesₖ y
  inv := ↑x⁻¹ otimesₖ ↑y⁻¹
  val_inv := by simp only [← mul_kronecker_mul, Units.mul_inv, one_kronecker_one]
  inv_val := by simp only [← mul_kronecker_mul, Units.inv_mul, one_kronecker_one]

中文:
定义 kronecker
  签名: (x : GL n R) (y : GL m R)
  定义体: x otimesₖ y
  inv := ↑x⁻¹ otimesₖ ↑y⁻¹
  val_inv := by simp only [← mul_kronecker_mul, Units.mul_inv, one_kronecker_one]
  inv_val := by simp only [← mul_kronecker_mul, Units.inv_mul, one_kronecker_one]
-/
protected def kronecker (x : GL n R) (y : GL m R) : GL (n × m) R where
  val := x otimesₖ y
  inv := ↑x⁻¹ otimesₖ ↑y⁻¹
  val_inv := by simp only [← mul_kronecker_mul, Units.mul_inv, one_kronecker_one]
  inv_val := by simp only [← mul_kronecker_mul, Units.inv_mul, one_kronecker_one]

/--
theorem `_root_.Matrix.IsUnit.kronecker` / 定理 `_root_.Matrix.IsUnit.kronecker`

English:
theorem _root_.Matrix.IsUnit.kronecker
  statement: {x : Matrix n n R} {y : Matrix m m R}
  proof: .isUnit GeneralLinearGroup.kronecker hx.unit hy.unit

中文:
定理 _root_.矩阵.是单位.kronecker
  结论: {x : 矩阵 n n R} {y : 矩阵 m m R}
  证明: .isUnit GeneralLinearGroup.kronecker hx.unit hy.unit

Depends on / 依赖: GeneralLinearGroup, GeneralLinearGroup.kronecker, hx.unit, hy.unit, isUnit, kronecker
-/
theorem _root_.Matrix.IsUnit.kronecker {x : Matrix n n R} {y : Matrix m m R}
    (hx : IsUnit x) (hy : IsUnit y) : IsUnit (x otimesₖ y) :=
.isUnit GeneralLinearGroup.kronecker hx.unit hy.unit

end kronecker

end GeneralLinearGroup

namespace SpecialLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]
  {S : Type*} [CommRing S] [Algebra R S]

/--
Definition of `toGL` / `toGL` 的定义

English:
definition toGL
  signature: : Matrix.SpecialLinearGroup n R ->* Matrix.GeneralLinearGroup n R where
  body: ⟨↑A, ↑A⁻¹, congr_arg (·.1) (mul_inv_cancel A), congr_arg (·.1) (inv_mul_cancel A)⟩
  map_one' := Units.ext rfl
  map_mul' _ _ := Units.ext rfl

中文:
定义 toGL
  签名: : 矩阵.SpecialLinearGroup n R ->* 矩阵.GeneralLinearGroup n R where
  定义体: ⟨↑A, ↑A⁻¹, congr_arg (·.1) (mul_inv_cancel A), congr_arg (·.1) (inv_mul_cancel A)⟩
  map_one' := Units.ext rfl
  map_mul' _ _ := Units.ext rfl

Depends on / 依赖: congr_arg, inv_mul_cancel, mul_inv_cancel
-/
def toGL : Matrix.SpecialLinearGroup n R ->* Matrix.GeneralLinearGroup n R where
  toFun A := ⟨↑A, ↑A⁻¹, congr_arg (·.1) (mul_inv_cancel A), congr_arg (·.1) (inv_mul_cancel A)⟩
  map_one' := Units.ext rfl
  map_mul' _ _ := Units.ext rfl

/--
Instance `hasCoeToGeneralLinearGroup` / 实例 `hasCoeToGeneralLinearGroup`

English:
instance hasCoeToGeneralLinearGroup
  signature: : Coe (SpecialLinearGroup n R) (GL n R)
  body: ⟨toGL⟩

中文:
实例 hasCoeToGeneralLinearGroup
  签名: : Coe (SpecialLinearGroup n R) (GL n R)
  定义体: ⟨toGL⟩
-/
instance hasCoeToGeneralLinearGroup : Coe (SpecialLinearGroup n R) (GL n R) :=
  ⟨toGL⟩

/--
lemma `toGL_injective` / 引理 `toGL_injective`

English:
lemma toGL_injective
  proof: fun g g' => by
  simpa [toGL] using! fun h _ => Subtype.ext h

@[simp]

中文:
引理 toGL_injective
  证明: fun g g' => by
  simpa [toGL] using! fun h _ => Subtype.ext h

@[simp]

Depends on / 依赖: Subtype, Subtype.ext
-/
lemma toGL_injective :
    Function.Injective (toGL : SpecialLinearGroup n R -> GL n R) := fun g g' => by
  simpa [toGL] using! fun h _ => Subtype.ext h

@[simp]
/--
lemma `toGL_inj` / 引理 `toGL_inj`

English:
lemma toGL_inj
  given: (g g' : SpecialLinearGroup n R)
  proof: toGL_injective.eq_iff

@[simp]

中文:
引理 toGL_inj
  条件: (g g' : SpecialLinearGroup n R)
  证明: toGL_injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, toGL_injective, toGL_injective.eq_iff
-/
lemma toGL_inj (g g' : SpecialLinearGroup n R) :
    (g : GeneralLinearGroup n R) = g' ↔ g = g' :=
  toGL_injective.eq_iff

@[simp]
/--
theorem `coeToGL_det` / 定理 `coeToGL_det`

English:
theorem coeToGL_det
  given: (g : SpecialLinearGroup n R)
  proof: Units.ext g.prop

@[simp]

中文:
定理 coeToGL_det
  条件: (g : SpecialLinearGroup n R)
  证明: Units.ext g.prop

@[simp]

Depends on / 依赖: Units.ext, g.prop
-/
theorem coeToGL_det (g : SpecialLinearGroup n R) :
    Matrix.GeneralLinearGroup.det (g : GL n R) = 1 :=
  Units.ext g.prop

@[simp]
/--
lemma `coe_GL_coe_matrix` / 引理 `coe_GL_coe_matrix`

English:
lemma coe_GL_coe_matrix
  given: (g : SpecialLinearGroup n R)
  statement: ((toGL g) : Matrix n n R) = g
  proof: rfl

中文:
引理 coe_GL_coe_matrix
  条件: (g : SpecialLinearGroup n R)
  结论: ((toGL g) : 矩阵 n n R) = g
  证明: rfl
-/
lemma coe_GL_coe_matrix (g : SpecialLinearGroup n R) : ((toGL g) : Matrix n n R) = g := rfl

variable (S) in
/--
Definition of `mapGL` / `mapGL` 的定义

English:
definition mapGL
  signature: : Matrix.SpecialLinearGroup n R ->* Matrix.GeneralLinearGroup n S
  body: toGL.comp (map (algebraMap R S))

@[simp]

中文:
定义 mapGL
  签名: : 矩阵.SpecialLinearGroup n R ->* 矩阵.GeneralLinearGroup n S
  定义体: toGL.comp (map (algebraMap R S))

@[simp]

Depends on / 依赖: algebraMap, toGL.comp
-/
def mapGL : Matrix.SpecialLinearGroup n R ->* Matrix.GeneralLinearGroup n S :=
  toGL.comp (map (algebraMap R S))

@[simp]
/--
lemma `mapGL_inj` / 引理 `mapGL_inj`

English:
lemma mapGL_inj
  given: [FaithfulSMul R S] (g g' : SpecialLinearGroup n R)
  proof: by
  simp [mapGL, ext_iff]

中文:
引理 mapGL_inj
  条件: [忠实标量乘法 R S] (g g' : SpecialLinearGroup n R)
  证明: by
  simp [mapGL, ext_iff]

Depends on / 依赖: ext_iff
-/
lemma mapGL_inj [FaithfulSMul R S] (g g' : SpecialLinearGroup n R) :
    mapGL S g = mapGL S g' ↔ g = g' := by
  simp [mapGL, ext_iff]

/--
lemma `mapGL_injective` / 引理 `mapGL_injective`

English:
lemma mapGL_injective
  given: [FaithfulSMul R S]
  proof: fun a b => by simp

@[simp]

中文:
引理 mapGL_injective
  条件: [忠实标量乘法 R S]
  证明: fun a b => by simp

@[simp]
-/
lemma mapGL_injective [FaithfulSMul R S] :
    Function.Injective (mapGL (R := R) (n := n) S) :=
  fun a b => by simp

@[simp]
/--
lemma `mapGL_coe_matrix` / 引理 `mapGL_coe_matrix`

English:
lemma mapGL_coe_matrix
  given: (g : SpecialLinearGroup n R)
  proof: rfl

@[simp]

中文:
引理 mapGL_coe_matrix
  条件: (g : SpecialLinearGroup n R)
  证明: rfl

@[simp]
-/
lemma mapGL_coe_matrix (g : SpecialLinearGroup n R) :
    ((mapGL S g) : Matrix n n S) = g.map (algebraMap R S) :=
  rfl

@[simp]
/--
lemma `map_mapGL` / 引理 `map_mapGL`

English:
lemma map_mapGL
  statement: {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  proof: by
  ext
  simp [IsScalarTower.algebraMap_apply R S T]

@[simp]

中文:
引理 map_mapGL
  结论: {T : 类型} [交换环 T] [代数 R T] [代数 S T] [标量塔 R S T]
  证明: by
  ext
  simp [IsScalarTower.algebraMap_apply R S T]

@[simp]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_apply, algebraMap_apply
-/
lemma map_mapGL {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (g : SpecialLinearGroup n R) :
    (mapGL S g).map (algebraMap S T) = mapGL T g := by
  ext
  simp [IsScalarTower.algebraMap_apply R S T]

@[simp]
/--
lemma `det_mapGL` / 引理 `det_mapGL`

English:
lemma det_mapGL
  given: (g : SpecialLinearGroup n R)
  statement: (mapGL S g).det = 1
  proof: by
  simp [mapGL]

中文:
引理 det_mapGL
  条件: (g : SpecialLinearGroup n R)
  结论: (mapGL S g).det = 1
  证明: by
  simp [mapGL]
-/
lemma det_mapGL (g : SpecialLinearGroup n R) : (mapGL S g).det = 1 := by
  simp [mapGL]

end SpecialLinearGroup

section

variable {n : Type u} {R : Type v} [DecidableEq n] [Fintype n]
  [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

section

variable (n R)

/--
Definition of `GLPos` / `GLPos` 的定义

English:
definition GLPos
  signature: : Subgroup (GL n R)
  body: (Units.posSubgroup R).comap GeneralLinearGroup.det

@[inherit_doc] scoped[MatrixGroups] notation "GL(" n ", " R ")" "⁺" => GLPos (Fin n) R

中文:
定义 GLPos
  签名: : 子群 (GL n R)
  定义体: (Units.posSubgroup R).comap GeneralLinearGroup.det

@[inherit_doc] scoped[MatrixGroups] notation "GL(" n ", " R ")" "⁺" => GLPos (Fin n) R

Depends on / 依赖: GeneralLinearGroup, GeneralLinearGroup.det, Units.posSubgroup, posSubgroup
-/
def GLPos : Subgroup (GL n R) :=
  (Units.posSubgroup R).comap GeneralLinearGroup.det

@[inherit_doc] scoped[MatrixGroups] notation "GL(" n ", " R ")" "⁺" => GLPos (Fin n) R

end

@[simp]
/--
theorem `mem_glpos` / 定理 `mem_glpos`

English:
theorem mem_glpos
  given: (A : GL n R)
  statement: A in GLPos n R ↔ 0 < (Matrix.GeneralLinearGroup.det A : R)
  proof: Iff.rfl

中文:
定理 mem_glpos
  条件: (A : GL n R)
  结论: A in GLPos n R ↔ 0 < (矩阵.GeneralLinearGroup.det A : R)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_glpos (A : GL n R) : A in GLPos n R ↔ 0 < (Matrix.GeneralLinearGroup.det A : R) :=
  Iff.rfl

/--
theorem `GLPos.det_ne_zero` / 定理 `GLPos.det_ne_zero`

English:
theorem GLPos.det_ne_zero
  given: (A : GLPos n R)
  statement: ((A : GL n R) : Matrix n n R).det != 0
  proof: ne_of_gt A.prop

中文:
定理 GLPos.det_ne_zero
  条件: (A : GLPos n R)
  结论: ((A : GL n R) : 矩阵 n n R).det != 0
  证明: ne_of_gt A.prop

Depends on / 依赖: A.prop, ne_of_gt
-/
theorem GLPos.det_ne_zero (A : GLPos n R) : ((A : GL n R) : Matrix n n R).det != 0 :=
  ne_of_gt A.prop

end

section Neg

variable {n : Type u} {R : Type v} [DecidableEq n] [Fintype n]
  [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [Fact (Even (Fintype.card n))]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (GLPos n R)
  body: ⟨fun g =>
    ⟨-g, by
      rw [mem_glpos]; rw [GeneralLinearGroup.val_det_apply]; rw [Units.val_neg]; rw [det_neg]; rw [(Fact.out (p := Even <| Fintype.card n)).neg_one_pow]; rw [one_mul]
      exact g.prop⟩⟩

@[simp]

中文:
实例 :
  签名: 取负 (GLPos n R)
  定义体: ⟨fun g =>
    ⟨-g, by
      rw [mem_glpos]; rw [GeneralLinearGroup.val_det_apply]; rw [Units.val_neg]; rw [det_neg]; rw [(Fact.out (p := Even <| Fintype.card n)).neg_one_pow]; rw [one_mul]
      exact g.prop⟩⟩

@[simp]

Depends on / 依赖: Fact.out, Fintype, Fintype.card, GeneralLinearGroup, GeneralLinearGroup.val_det_apply, Units.val_neg, det_neg, g.prop, mem_glpos, neg_one_pow, one_mul, val_det_apply, val_neg
-/
instance : Neg (GLPos n R) :=
  ⟨fun g =>
    ⟨-g, by
      rw [mem_glpos]; rw [GeneralLinearGroup.val_det_apply]; rw [Units.val_neg]; rw [det_neg]; rw [(Fact.out (p := Even <| Fintype.card n)).neg_one_pow]; rw [one_mul]
      exact g.prop⟩⟩

@[simp]
/--
theorem `GLPos.coe_neg_GL` / 定理 `GLPos.coe_neg_GL`

English:
theorem GLPos.coe_neg_GL
  given: (g : GLPos n R)
  statement: ↑(-g) = -(g : GL n R)
  proof: rfl

@[simp]

中文:
定理 GLPos.coe_neg_GL
  条件: (g : GLPos n R)
  结论: ↑(-g) = -(g : GL n R)
  证明: rfl

@[simp]
-/
theorem GLPos.coe_neg_GL (g : GLPos n R) : ↑(-g) = -(g : GL n R) :=
  rfl

@[simp]
/--
theorem `GLPos.coe_neg` / 定理 `GLPos.coe_neg`

English:
theorem GLPos.coe_neg
  given: (g : GLPos n R)
  statement: (↑(-g) : GL n R) = -((g : GL n R) : Matrix n n R)
  proof: rfl

@[simp]

中文:
定理 GLPos.coe_neg
  条件: (g : GLPos n R)
  结论: (↑(-g) : GL n R) = -((g : GL n R) : 矩阵 n n R)
  证明: rfl

@[simp]
-/
theorem GLPos.coe_neg (g : GLPos n R) : (↑(-g) : GL n R) = -((g : GL n R) : Matrix n n R) :=
  rfl

@[simp]
/--
theorem `GLPos.coe_neg_apply` / 定理 `GLPos.coe_neg_apply`

English:
theorem GLPos.coe_neg_apply
  given: (g : GLPos n R) (i j : n)
  proof: rfl

中文:
定理 GLPos.coe_neg_apply
  条件: (g : GLPos n R) (i j : n)
  证明: rfl
-/
theorem GLPos.coe_neg_apply (g : GLPos n R) (i j : n) :
    ((↑(-g) : GL n R) : Matrix n n R) i j = -((g : GL n R) : Matrix n n R) i j :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasDistribNeg (GLPos n R)
  body: Subtype.coe_injective.hasDistribNeg _ GLPos.coe_neg_GL (GLPos n R).coe_mul

中文:
实例 :
  签名: 有DistribNeg (GLPos n R)
  定义体: Subtype.coe_injective.hasDistribNeg _ GLPos.coe_neg_GL (GLPos n R).coe_mul

Depends on / 依赖: GLPos.coe_neg_GL, Subtype, Subtype.coe_injective.hasDistribNeg, coe_injective, coe_mul, coe_neg_GL, hasDistribNeg
-/
instance : HasDistribNeg (GLPos n R) :=
  Subtype.coe_injective.hasDistribNeg _ GLPos.coe_neg_GL (GLPos n R).coe_mul

end Neg

namespace SpecialLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n]
  {R : Type v} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/--
Definition of `toGLPos` / `toGLPos` 的定义

English:
definition toGLPos
  signature: : SpecialLinearGroup n R ->* GLPos n R where
  body: ⟨(A : GL n R), show 0 < (↑A : Matrix n n R).det from A.prop.symm ▸ zero_lt_one⟩
map_one' := Subtype.ext Units.ext rfl
map_mul' _ _ := Subtype.ext Units.ext rfl

中文:
定义 toGLPos
  签名: : SpecialLinearGroup n R ->* GLPos n R where
  定义体: ⟨(A : GL n R), show 0 < (↑A : Matrix n n R).det from A.prop.symm ▸ zero_lt_one⟩
map_one' := Subtype.ext Units.ext rfl
map_mul' _ _ := Subtype.ext Units.ext rfl

Depends on / 依赖: A.prop.symm, Matrix, zero_lt_one
-/
def toGLPos : SpecialLinearGroup n R ->* GLPos n R where
  toFun A := ⟨(A : GL n R), show 0 < (↑A : Matrix n n R).det from A.prop.symm ▸ zero_lt_one⟩
map_one' := Subtype.ext Units.ext rfl
map_mul' _ _ := Subtype.ext Units.ext rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (SpecialLinearGroup n R) (GLPos n R)
  body: ⟨toGLPos⟩

中文:
实例 :
  签名: Coe (SpecialLinearGroup n R) (GLPos n R)
  定义体: ⟨toGLPos⟩

Depends on / 依赖: toGLPos
-/
instance : Coe (SpecialLinearGroup n R) (GLPos n R) :=
  ⟨toGLPos⟩

/--
theorem `toGLPos_injective` / 定理 `toGLPos_injective`

English:
theorem toGLPos_injective
  statement: Function.Injective (toGLPos : SpecialLinearGroup n R -> GLPos n R)
  proof: -- Porting note: had to rewrite this to hint the correct types to Lean
  -- (It can't find the coercion GLPos n R → Matrix n n R)
  Function.Injective.of_comp
    (f := fun (A : GLPos n R) => ((A : GL n R) : Matrix n n R))
    Subtype.coe_injective

中文:
定理 toGLPos_injective
  结论: 函数.单射 (toGLPos : SpecialLinearGroup n R -> GLPos n R)
  证明: -- Porting note: had to rewrite this to hint the correct types to Lean
  -- (It can't find the coercion GLPos n R → Matrix n n R)
  Function.Injective.of_comp
    (f := fun (A : GLPos n R) => ((A : GL n R) : Matrix n n R))
    Subtype.coe_injective
-/
theorem toGLPos_injective : Function.Injective (toGLPos : SpecialLinearGroup n R -> GLPos n R) :=
  -- Porting note: had to rewrite this to hint the correct types to Lean
  -- (It can't find the coercion GLPos n R → Matrix n n R)
  Function.Injective.of_comp
    (f := fun (A : GLPos n R) => ((A : GL n R) : Matrix n n R))
    Subtype.coe_injective

/-- Coercing a `Matrix.SpecialLinearGroup` via `GL_pos` and `GL` is the same as coercing straight to
a matrix. -/
@[simp]
/--
theorem `coe_GLPos_coe_GL_coe_matrix` / 定理 `coe_GLPos_coe_GL_coe_matrix`

English:
theorem coe_GLPos_coe_GL_coe_matrix
  given: (g : SpecialLinearGroup n R)
  proof: rfl

@[simp]

中文:
定理 coe_GLPos_coe_GL_coe_matrix
  条件: (g : SpecialLinearGroup n R)
  证明: rfl

@[simp]
-/
theorem coe_GLPos_coe_GL_coe_matrix (g : SpecialLinearGroup n R) :
    (↑(↑(↑g : GLPos n R) : GL n R) : Matrix n n R) = ↑g :=
  rfl

@[simp]
/--
theorem `coe_to_GLPos_to_GL_det` / 定理 `coe_to_GLPos_to_GL_det`

English:
theorem coe_to_GLPos_to_GL_det
  given: (g : SpecialLinearGroup n R)
  proof: Units.ext g.prop

中文:
定理 coe_to_GLPos_to_GL_det
  条件: (g : SpecialLinearGroup n R)
  证明: Units.ext g.prop

Depends on / 依赖: Units.ext, g.prop
-/
theorem coe_to_GLPos_to_GL_det (g : SpecialLinearGroup n R) :
    Matrix.GeneralLinearGroup.det ((g : GLPos n R) : GL n R) = 1 :=
  Units.ext g.prop

variable [Fact (Even (Fintype.card n))]

@[norm_cast]
/--
theorem `coe_GLPos_neg` / 定理 `coe_GLPos_neg`

English:
theorem coe_GLPos_neg
  given: (g : SpecialLinearGroup n R)
  statement: ↑(-g) = -(↑g : GLPos n R)
  proof: Subtype.ext Units.ext rfl

中文:
定理 coe_GLPos_neg
  条件: (g : SpecialLinearGroup n R)
  结论: ↑(-g) = -(↑g : GLPos n R)
  证明: Subtype.ext Units.ext rfl

Depends on / 依赖: Subtype, Subtype.ext, Units.ext
-/
theorem coe_GLPos_neg (g : SpecialLinearGroup n R) : ↑(-g) = -(↑g : GLPos n R) :=
Subtype.ext Units.ext rfl

end SpecialLinearGroup

end Matrix
