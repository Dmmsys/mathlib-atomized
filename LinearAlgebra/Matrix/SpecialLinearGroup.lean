/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Wen Yang
-/
module

public import Mathlib.Data.Fintype.Parity
public import Mathlib.LinearAlgebra.Matrix.Action
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# The Special Linear group $SL(n, R)$

This file defines the elements of the Special Linear group `SpecialLinearGroup n R`, consisting
of all square `R`-matrices with determinant `1` on the fintype `n` by `n`. In addition, we define
the group structure on `SpecialLinearGroup n R` and the embedding into the general linear group
`GeneralLinearGroup R (n → R)`.

## Main definitions

* `Matrix.SpecialLinearGroup` is the type of matrices with determinant 1
* `Matrix.SpecialLinearGroup.group` gives the group structure (under multiplication)
* `Matrix.SpecialLinearGroup.toGL` is the embedding `SLₙ(R) → GLₙ(R)`

## Notation

For `m : ℕ`, we introduce the notation `SL(m,R)` for the special linear group on the fintype
`n = Fin m`, in the scope `MatrixGroups`.

## Implementation notes
The inverse operation in the `SpecialLinearGroup` is defined to be the adjugate
matrix, so that `SpecialLinearGroup n R` has a group structure for all `CommRing R`.

We define the elements of `SpecialLinearGroup` to be matrices, since we need to
compute their determinant. This is in contrast with `GeneralLinearGroup R M`,
which consists of invertible `R`-linear maps on `M`.

We provide `Matrix.SpecialLinearGroup.hasCoeToFun` for convenience, but do not state any
lemmas about it, and use `Matrix.SpecialLinearGroup.coeFn_eq_coe` to eliminate it `⇑` in favor
of a regular `↑` coercion.

## References

* https://en.wikipedia.org/wiki/Special_linear_group

## Tags

matrix group, group, matrix inverse
-/

@[expose] public section


namespace Matrix

universe u v

open LinearMap

section

variable (n : Type u) [DecidableEq n] [Fintype n] (R : Type v) [CommRing R]

/--
Definition of `SpecialLinearGroup` / `SpecialLinearGroup` 的定义

English:
definition SpecialLinearGroup
  body: { A : Matrix n n R // A.det = 1 }

中文:
定义 SpecialLinearGroup
  定义体: { A : Matrix n n R // A.det = 1 }

Depends on / 依赖: A.det, Matrix
-/
def SpecialLinearGroup :=
  { A : Matrix n n R // A.det = 1 }

end

@[inherit_doc]
scoped[MatrixGroups] notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

namespace SpecialLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: R] : DecidableEq (SpecialLinearGroup n R)
  body: Subtype.instDecidableEq

中文:
实例 [DecidableEq
  签名: R] : DecidableEq (SpecialLinearGroup n R)
  定义体: Subtype.instDecidableEq

Depends on / 依赖: Subtype, Subtype.instDecidableEq, instDecidableEq
-/
instance [DecidableEq R] : DecidableEq (SpecialLinearGroup n R) := Subtype.instDecidableEq

/--
Instance `hasCoeToMatrix` / 实例 `hasCoeToMatrix`

English:
instance hasCoeToMatrix
  signature: : Coe (SpecialLinearGroup n R) (Matrix n n R)
  body: ⟨fun A => A.val⟩

中文:
实例 hasCoeToMatrix
  签名: : Coe (SpecialLinearGroup n R) (矩阵 n n R)
  定义体: ⟨fun A => A.val⟩

Depends on / 依赖: A.val
-/
instance hasCoeToMatrix : Coe (SpecialLinearGroup n R) (Matrix n n R) :=
  ⟨fun A => A.val⟩

/-- In this file, Lean often has a hard time working out the values of `n` and `R` for an expression
like `det ↑A`. Rather than writing `(A : Matrix n n R)` everywhere in this file which is annoyingly
verbose, or `A.val` which is not the simp-normal form for subtypes, we create a local notation
`↑ₘA`. This notation references the local `n` and `R` variables, so is not valid as a global
notation. -/
local notation:1024 "↑ₘ" A:1024 => ((A : SpecialLinearGroup n R) : Matrix n n R)

section CoeFnInstance

/--
Instance `instCoeFun` / 实例 `instCoeFun`

English:
instance instCoeFun
  signature: : CoeFun (SpecialLinearGroup n R) fun _ => n -> n -> R where coe A
  body: ↑ₘA

中文:
实例 instCoeFun
  签名: : CoeFun (SpecialLinearGroup n R) fun _ => n -> n -> R where coe A
  定义体: ↑ₘA
-/
instance instCoeFun : CoeFun (SpecialLinearGroup n R) fun _ => n -> n -> R where coe A := ↑ₘA

end CoeFnInstance

/--
theorem `ext_iff` / 定理 `ext_iff`

English:
theorem ext_iff
  given: (A B : SpecialLinearGroup n R)
  statement: A = B ↔ forall i j, A i j = B i j
  proof: Subtype.ext_iff.trans Matrix.ext_iff.symm

@[ext]

中文:
定理 ext_iff
  条件: (A B : SpecialLinearGroup n R)
  结论: A = B ↔ 对任意 i j, A i j = B i j
  证明: Subtype.ext_iff.trans Matrix.ext_iff.symm

@[ext]

Depends on / 依赖: Matrix, Matrix.ext_iff.symm, Subtype, Subtype.ext_iff.trans, ext_iff
-/
theorem ext_iff (A B : SpecialLinearGroup n R) : A = B ↔ forall i j, A i j = B i j :=
  Subtype.ext_iff.trans Matrix.ext_iff.symm

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (A B : SpecialLinearGroup n R)
  statement: (forall i j, A i j = B i j) -> A = B
  proof: (SpecialLinearGroup.ext_iff A B).mpr

中文:
定理 ext
  条件: (A B : SpecialLinearGroup n R)
  结论: (对任意 i j, A i j = B i j) -> A = B
  证明: (SpecialLinearGroup.ext_iff A B).mpr

Depends on / 依赖: SpecialLinearGroup, SpecialLinearGroup.ext_iff, ext_iff
-/
theorem ext (A B : SpecialLinearGroup n R) : (forall i j, A i j = B i j) -> A = B :=
  (SpecialLinearGroup.ext_iff A B).mpr

/--
Instance `subsingleton_of_subsingleton` / 实例 `subsingleton_of_subsingleton`

English:
instance subsingleton_of_subsingleton
  signature: [Subsingleton n]
  body: by
  refine ⟨fun ⟨A, hA⟩ ⟨B, hB⟩ => ?_⟩
  ext i j
  rcases isEmpty_or_nonempty n with hn | hn; · exfalso; exact IsEmpty.false i
  rw [det_eq_elem_of_subsingleton _ i] at hA hB
  simp only [Subsingleton.elim j i, hA, hB]

中文:
实例 subsingleton_of_subsingleton
  签名: [子单例 n]
  定义体: by
  refine ⟨fun ⟨A, hA⟩ ⟨B, hB⟩ => ?_⟩
  ext i j
  rcases isEmpty_or_nonempty n with hn | hn; · exfalso; exact IsEmpty.false i
  rw [det_eq_elem_of_subsingleton _ i] at hA hB
  simp only [Subsingleton.elim j i, hA, hB]

Depends on / 依赖: IsEmpty, IsEmpty.false, Subsingleton, Subsingleton.elim, det_eq_elem_of_subsingleton, isEmpty_or_nonempty
-/
instance subsingleton_of_subsingleton [Subsingleton n] : Subsingleton (SpecialLinearGroup n R) := by
  refine ⟨fun ⟨A, hA⟩ ⟨B, hB⟩ => ?_⟩
  ext i j
  rcases isEmpty_or_nonempty n with hn | hn; · exfalso; exact IsEmpty.false i
  rw [det_eq_elem_of_subsingleton _ i] at hA hB
  simp only [Subsingleton.elim j i, hA, hB]

/--
Instance `hasInv` / 实例 `hasInv`

English:
instance hasInv
  signature: : Inv (SpecialLinearGroup n R)
  body: ⟨fun A => ⟨adjugate A, by rw [det_adjugate, A.prop, one_pow]⟩⟩

中文:
实例 hasInv
  签名: : 取逆 (SpecialLinearGroup n R)
  定义体: ⟨fun A => ⟨adjugate A, by rw [det_adjugate, A.prop, one_pow]⟩⟩

Depends on / 依赖: A.prop, adjugate, det_adjugate, one_pow
-/
instance hasInv : Inv (SpecialLinearGroup n R) :=
  ⟨fun A => ⟨adjugate A, by rw [det_adjugate, A.prop, one_pow]⟩⟩

/--
Instance `hasMul` / 实例 `hasMul`

English:
instance hasMul
  signature: : Mul (SpecialLinearGroup n R)
  body: ⟨fun A B => ⟨A * B, by rw [det_mul, A.prop, B.prop, one_mul]⟩⟩

中文:
实例 hasMul
  签名: : 乘法 (SpecialLinearGroup n R)
  定义体: ⟨fun A B => ⟨A * B, by rw [det_mul, A.prop, B.prop, one_mul]⟩⟩

Depends on / 依赖: A.prop, B.prop, det_mul, one_mul
-/
instance hasMul : Mul (SpecialLinearGroup n R) :=
  ⟨fun A B => ⟨A * B, by rw [det_mul, A.prop, B.prop, one_mul]⟩⟩

/--
Instance `hasOne` / 实例 `hasOne`

English:
instance hasOne
  signature: : One (SpecialLinearGroup n R)
  body: ⟨⟨1, det_one⟩⟩

中文:
实例 hasOne
  签名: : 幺 (SpecialLinearGroup n R)
  定义体: ⟨⟨1, det_one⟩⟩

Depends on / 依赖: det_one
-/
instance hasOne : One (SpecialLinearGroup n R) :=
  ⟨⟨1, det_one⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow (SpecialLinearGroup n R) Nat
  body: ⟨x ^ n, (det_pow _ _).trans x.prop.symm ▸ one_pow _⟩

中文:
实例 :
  签名: 幂 (SpecialLinearGroup n R) 自然数
  定义体: ⟨x ^ n, (det_pow _ _).trans x.prop.symm ▸ one_pow _⟩

Depends on / 依赖: det_pow, one_pow, x.prop.symm
-/
instance : Pow (SpecialLinearGroup n R) Nat where
pow x n := ⟨x ^ n, (det_pow _ _).trans x.prop.symm ▸ one_pow _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (SpecialLinearGroup n R)
  body: ⟨1⟩

中文:
实例 :
  签名: 可居 (SpecialLinearGroup n R)
  定义体: ⟨1⟩
-/
instance : Inhabited (SpecialLinearGroup n R) :=
  ⟨1⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fintype
  signature: R] [DecidableEq R] : Fintype (SpecialLinearGroup n R)
  body: Subtype.fintype _

中文:
实例 [有限类型
  签名: R] [DecidableEq R] : 有限类型 (SpecialLinearGroup n R)
  定义体: Subtype.fintype _

Depends on / 依赖: Subtype, Subtype.fintype, fintype
-/
instance [Fintype R] [DecidableEq R] : Fintype (SpecialLinearGroup n R) := Subtype.fintype _
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: R] : Finite (SpecialLinearGroup n R)
  body: Subtype.finite

中文:
实例 [有限
  签名: R] : 有限 (SpecialLinearGroup n R)
  定义体: Subtype.finite

Depends on / 依赖: Subtype, Subtype.finite, finite
-/
instance [Finite R] : Finite (SpecialLinearGroup n R) := Subtype.finite

/--
Definition of `transpose` / `transpose` 的定义

English:
definition transpose
  signature: (A : SpecialLinearGroup n R)
  body: ⟨A.1.transpose, A.1.det_transpose ▸ A.2⟩

@[inherit_doc]
scoped postfix:1024 "ᵀ" => SpecialLinearGroup.transpose

中文:
定义 transpose
  签名: (A : SpecialLinearGroup n R)
  定义体: ⟨A.1.transpose, A.1.det_transpose ▸ A.2⟩

@[inherit_doc]
scoped postfix:1024 "ᵀ" => SpecialLinearGroup.transpose

Depends on / 依赖: det_transpose, transpose
-/
def transpose (A : SpecialLinearGroup n R) : SpecialLinearGroup n R :=
  ⟨A.1.transpose, A.1.det_transpose ▸ A.2⟩

@[inherit_doc]
scoped postfix:1024 "ᵀ" => SpecialLinearGroup.transpose

section CoeLemmas

variable (A B : SpecialLinearGroup n R)

/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (A : Matrix n n R) (h : det A = 1)
  statement: ↑(⟨A, h⟩ : SpecialLinearGroup n R) = A
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: (A : 矩阵 n n R) (h : det A = 1)
  结论: ↑(⟨A, h⟩ : SpecialLinearGroup n R) = A
  证明: rfl

@[simp]
-/
theorem coe_mk (A : Matrix n n R) (h : det A = 1) : ↑(⟨A, h⟩ : SpecialLinearGroup n R) = A :=
  rfl

@[simp]
/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  statement: ↑ₘ(A⁻¹) = adjugate A
  proof: rfl

@[simp]

中文:
定理 coe_inv
  结论: ↑ₘ(A⁻¹) = adjugate A
  证明: rfl

@[simp]
-/
theorem coe_inv : ↑ₘ(A⁻¹) = adjugate A :=
  rfl

@[simp]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  statement: ↑ₘ(A * B) = ↑ₘA * ↑ₘB
  proof: rfl

@[simp]

中文:
定理 coe_mul
  结论: ↑ₘ(A * B) = ↑ₘA * ↑ₘB
  证明: rfl

@[simp]
-/
theorem coe_mul : ↑ₘ(A * B) = ↑ₘA * ↑ₘB :=
  rfl

@[simp]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: (1 : SpecialLinearGroup n R) = (1 : Matrix n n R)
  proof: rfl

@[simp]

中文:
定理 coe_one
  结论: (1 : SpecialLinearGroup n R) = (1 : 矩阵 n n R)
  证明: rfl

@[simp]
-/
theorem coe_one : (1 : SpecialLinearGroup n R) = (1 : Matrix n n R) :=
  rfl

@[simp]
/--
theorem `det_coe` / 定理 `det_coe`

English:
theorem det_coe
  statement: det ↑ₘA = 1
  proof: A.2

@[simp]

中文:
定理 det_coe
  结论: det ↑ₘA = 1
  证明: A.2

@[simp]
-/
theorem det_coe : det ↑ₘA = 1 :=
  A.2

@[simp]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (m : Nat)
  statement: ↑ₘ(A ^ m) = ↑ₘA ^ m
  proof: rfl

@[simp]

中文:
定理 coe_pow
  条件: (m : 自然数)
  结论: ↑ₘ(A ^ m) = ↑ₘA ^ m
  证明: rfl

@[simp]
-/
theorem coe_pow (m : Nat) : ↑ₘ(A ^ m) = ↑ₘA ^ m :=
  rfl

@[simp]
/--
lemma `coe_transpose` / 引理 `coe_transpose`

English:
lemma coe_transpose
  given: (A : SpecialLinearGroup n R)
  statement: ↑ₘAᵀ = (↑ₘA)ᵀ
  proof: rfl

中文:
引理 coe_transpose
  条件: (A : SpecialLinearGroup n R)
  结论: ↑ₘAᵀ = (↑ₘA)ᵀ
  证明: rfl
-/
lemma coe_transpose (A : SpecialLinearGroup n R) : ↑ₘAᵀ = (↑ₘA)ᵀ :=
  rfl

/--
theorem `det_ne_zero` / 定理 `det_ne_zero`

English:
theorem det_ne_zero
  given: [Nontrivial R] (g : SpecialLinearGroup n R)
  statement: det ↑ₘg != 0
  proof: by
  rw [g.det_coe]
  norm_num

中文:
定理 det_ne_zero
  条件: [非平凡 R] (g : SpecialLinearGroup n R)
  结论: det ↑ₘg != 0
  证明: by
  rw [g.det_coe]
  norm_num

Depends on / 依赖: det_coe, g.det_coe
-/
theorem det_ne_zero [Nontrivial R] (g : SpecialLinearGroup n R) : det ↑ₘg != 0 := by
  rw [g.det_coe]
  norm_num

/--
theorem `row_ne_zero` / 定理 `row_ne_zero`

English:
theorem row_ne_zero
  given: [Nontrivial R] (g : SpecialLinearGroup n R) (i : n)
  statement: g i != 0
  proof: fun h =>
g.det_ne_zero det_eq_zero_of_row_eq_zero i by simp [h]

中文:
定理 row_ne_zero
  条件: [非平凡 R] (g : SpecialLinearGroup n R) (i : n)
  结论: g i != 0
  证明: fun h =>
g.det_ne_zero det_eq_zero_of_row_eq_zero i by simp [h]
-/
theorem row_ne_zero [Nontrivial R] (g : SpecialLinearGroup n R) (i : n) : g i != 0 := fun h =>
g.det_ne_zero det_eq_zero_of_row_eq_zero i by simp [h]

end CoeLemmas

/--
Instance `monoid` / 实例 `monoid`

English:
instance monoid
  signature: : Monoid (SpecialLinearGroup n R)
  body: Function.Injective.monoid _ Subtype.coe_injective coe_one coe_mul coe_pow

中文:
实例 monoid
  签名: : 幺半群 (SpecialLinearGroup n R)
  定义体: Function.Injective.monoid _ Subtype.coe_injective coe_one coe_mul coe_pow

Depends on / 依赖: Function, Function.Injective.monoid, Injective, Subtype, Subtype.coe_injective, coe_injective, coe_mul, coe_one, coe_pow, monoid
-/
instance monoid : Monoid (SpecialLinearGroup n R) :=
  Function.Injective.monoid _ Subtype.coe_injective coe_one coe_mul coe_pow

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group (SpecialLinearGroup n R)
  body: { SpecialLinearGroup.monoid, SpecialLinearGroup.hasInv with
    inv_mul_cancel := fun A => by
      ext1
      simp [adjugate_mul] }

中文:
实例 :
  签名: 群 (SpecialLinearGroup n R)
  定义体: { SpecialLinearGroup.monoid, SpecialLinearGroup.hasInv with
    inv_mul_cancel := fun A => by
      ext1
      simp [adjugate_mul] }

Depends on / 依赖: SpecialLinearGroup, SpecialLinearGroup.hasInv, SpecialLinearGroup.monoid, adjugate_mul, hasInv, inv_mul_cancel, monoid
-/
instance : Group (SpecialLinearGroup n R) :=
  { SpecialLinearGroup.monoid, SpecialLinearGroup.hasInv with
    inv_mul_cancel := fun A => by
      ext1
      simp [adjugate_mul] }

/--
Definition of `toLin'` / `toLin'` 的定义

English:
definition toLin'
  signature: : SpecialLinearGroup n R ->* (n -> R) ≃ₗ[R] n -> R where
  body: LinearEquiv.ofLinearMap (Matrix.toLin' ↑ₘA) (Matrix.toLin' ↑ₘA⁻¹)
      (by rw [← toLin'_mul, ← coe_mul, mul_inv_cancel, coe_one, toLin'_one])
      (by rw [← toLin'_mul, ← coe_mul, inv_mul_cancel, coe_one, toLin'_one])
  map_one' := LinearEquiv.toLinearMap_injective Matrix.toLin'_one
map_mul' A B :

中文:
定义 toLin'
  签名: : SpecialLinearGroup n R ->* (n -> R) ≃ₗ[R] n -> R where
  定义体: LinearEquiv.ofLinearMap (Matrix.toLin' ↑ₘA) (Matrix.toLin' ↑ₘA⁻¹)
      (by rw [← toLin'_mul, ← coe_mul, mul_inv_cancel, coe_one, toLin'_one])
      (by rw [← toLin'_mul, ← coe_mul, inv_mul_cancel, coe_one, toLin'_one])
  map_one' := LinearEquiv.toLinearMap_injective Matrix.toLin'_one
map_mul' A B :
-/
def toLin' : SpecialLinearGroup n R ->* (n -> R) ≃ₗ[R] n -> R where
  toFun A :=
    LinearEquiv.ofLinearMap (Matrix.toLin' ↑ₘA) (Matrix.toLin' ↑ₘA⁻¹)
      (by rw [← toLin'_mul, ← coe_mul, mul_inv_cancel, coe_one, toLin'_one])
      (by rw [← toLin'_mul, ← coe_mul, inv_mul_cancel, coe_one, toLin'_one])
  map_one' := LinearEquiv.toLinearMap_injective Matrix.toLin'_one
map_mul' A B := LinearEquiv.toLinearMap_injective Matrix.toLin'_mul ↑ₘA ↑ₘB

/--
theorem `toLin'_apply` / 定理 `toLin'_apply`

English:
theorem toLin'_apply
  given: (A : SpecialLinearGroup n R) (v : n -> R)
  proof: rfl

中文:
定理 toLin'_apply
  条件: (A : SpecialLinearGroup n R) (v : n -> R)
  证明: rfl
-/
theorem toLin'_apply (A : SpecialLinearGroup n R) (v : n -> R) :
    SpecialLinearGroup.toLin' A v = Matrix.toLin' (↑ₘA) v :=
  rfl

/--
theorem `toLin'_to_linearMap` / 定理 `toLin'_to_linearMap`

English:
theorem toLin'_to_linearMap
  given: (A : SpecialLinearGroup n R)
  proof: rfl

中文:
定理 toLin'_to_linearMap
  条件: (A : SpecialLinearGroup n R)
  证明: rfl
-/
theorem toLin'_to_linearMap (A : SpecialLinearGroup n R) :
    ↑(SpecialLinearGroup.toLin' A) = Matrix.toLin' ↑ₘA :=
  rfl

/--
theorem `toLin'_symm_apply` / 定理 `toLin'_symm_apply`

English:
theorem toLin'_symm_apply
  given: (A : SpecialLinearGroup n R) (v : n -> R)
  proof: rfl

中文:
定理 toLin'_symm_apply
  条件: (A : SpecialLinearGroup n R) (v : n -> R)
  证明: rfl
-/
theorem toLin'_symm_apply (A : SpecialLinearGroup n R) (v : n -> R) :
    A.toLin'.symm v = Matrix.toLin' (↑ₘA⁻¹) v :=
  rfl

/--
theorem `toLin'_symm_to_linearMap` / 定理 `toLin'_symm_to_linearMap`

English:
theorem toLin'_symm_to_linearMap
  given: (A : SpecialLinearGroup n R)
  proof: rfl

中文:
定理 toLin'_symm_to_linearMap
  条件: (A : SpecialLinearGroup n R)
  证明: rfl
-/
theorem toLin'_symm_to_linearMap (A : SpecialLinearGroup n R) :
    ↑A.toLin'.symm = Matrix.toLin' ↑ₘA⁻¹ :=
  rfl

/--
theorem `toLin'_injective` / 定理 `toLin'_injective`

English:
theorem toLin'_injective
  proof: fun _ _ h =>
Subtype.coe_injective Matrix.toLin'.injective LinearEquiv.toLinearMap_injective.eq_iff.mpr h

中文:
定理 toLin'_injective
  证明: fun _ _ h =>
Subtype.coe_injective Matrix.toLin'.injective LinearEquiv.toLinearMap_injective.eq_iff.mpr h
-/
theorem toLin'_injective :
    Function.Injective ↑(toLin' : SpecialLinearGroup n R ->* (n -> R) ≃ₗ[R] n -> R) := fun _ _ h =>
Subtype.coe_injective Matrix.toLin'.injective LinearEquiv.toLinearMap_injective.eq_iff.mpr h

variable {S : Type*} [CommRing S]

/-- A ring homomorphism from `R` to `S` induces a group homomorphism from
`SpecialLinearGroup n R` to `SpecialLinearGroup n S`. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : R ->+* S)
  body: ⟨f.mapMatrix ↑ₘg, by
      rw [← f.map_det]
      simp [g.prop]⟩
map_one' := Subtype.ext f.mapMatrix.map_one
map_mul' x y := Subtype.ext f.mapMatrix.map_mul ↑ₘx ↑ₘy

中文:
定义 map
  签名: (f : R ->+* S)
  定义体: ⟨f.mapMatrix ↑ₘg, by
      rw [← f.map_det]
      simp [g.prop]⟩
map_one' := Subtype.ext f.mapMatrix.map_one
map_mul' x y := Subtype.ext f.mapMatrix.map_mul ↑ₘx ↑ₘy

Depends on / 依赖: Subtype, Subtype.ext, f.mapMatrix, f.mapMatrix.map_mul, f.mapMatrix.map_one, f.map_det, g.prop, mapMatrix, map_det, map_mul, map_one
-/
def map (f : R ->+* S) : SpecialLinearGroup n R ->* SpecialLinearGroup n S where
  toFun g :=
    ⟨f.mapMatrix ↑ₘg, by
      rw [← f.map_det]
      simp [g.prop]⟩
map_one' := Subtype.ext f.mapMatrix.map_one
map_mul' x y := Subtype.ext f.mapMatrix.map_mul ↑ₘx ↑ₘy

section center

open Subgroup

@[simp]
/--
theorem `center_eq_bot_of_subsingleton` / 定理 `center_eq_bot_of_subsingleton`

English:
theorem center_eq_bot_of_subsingleton
  given: [Subsingleton n]
  proof: eq_bot_iff.mpr fun x _ => by rw [mem_bot, Subsingleton.elim x 1]

中文:
定理 center_eq_bot_of_subsingleton
  条件: [子单例 n]
  证明: eq_bot_iff.mpr fun x _ => by rw [mem_bot, Subsingleton.elim x 1]

Depends on / 依赖: Subsingleton, Subsingleton.elim, eq_bot_iff, eq_bot_iff.mpr, mem_bot
-/
theorem center_eq_bot_of_subsingleton [Subsingleton n] :
    center (SpecialLinearGroup n R) = ⊥ :=
  eq_bot_iff.mpr fun x _ => by rw [mem_bot, Subsingleton.elim x 1]

/--
theorem `scalar_eq_self_of_mem_center` / 定理 `scalar_eq_self_of_mem_center`

English:
theorem scalar_eq_self_of_mem_center
  proof: by
  obtain ⟨r : R, hr : scalar n r = A⟩ := mem_range_scalar_of_commute_transvectionStruct fun t =>
Subtype.ext_iff.mp Subgroup.mem_center_iff.mp hA ⟨t.toMatrix, by simp⟩
  simp [← congr_fun₂ hr i i, ← hr]

中文:
定理 scalar_eq_self_of_mem_center
  证明: by
  obtain ⟨r : R, hr : scalar n r = A⟩ := mem_range_scalar_of_commute_transvectionStruct fun t =>
Subtype.ext_iff.mp Subgroup.mem_center_iff.mp hA ⟨t.toMatrix, by simp⟩
  simp [← congr_fun₂ hr i i, ← hr]

Depends on / 依赖: Subgroup, Subgroup.mem_center_iff.mp, Subtype, Subtype.ext_iff.mp, ext_iff, mem_center_iff, mem_range_scalar_of_commute_transvectionStruct, scalar, t.toMatrix, toMatrix
-/
theorem scalar_eq_self_of_mem_center
    {A : SpecialLinearGroup n R} (hA : A in center (SpecialLinearGroup n R)) (i : n) :
    scalar n (A i i) = A := by
  obtain ⟨r : R, hr : scalar n r = A⟩ := mem_range_scalar_of_commute_transvectionStruct fun t =>
Subtype.ext_iff.mp Subgroup.mem_center_iff.mp hA ⟨t.toMatrix, by simp⟩
  simp [← congr_fun₂ hr i i, ← hr]

/--
theorem `scalar_eq_coe_self_center` / 定理 `scalar_eq_coe_self_center`

English:
theorem scalar_eq_coe_self_center
  proof: scalar_eq_self_of_mem_center A.property i

中文:
定理 scalar_eq_coe_self_center
  证明: scalar_eq_self_of_mem_center A.property i

Depends on / 依赖: A.property, property, scalar_eq_self_of_mem_center
-/
theorem scalar_eq_coe_self_center
    (A : center (SpecialLinearGroup n R)) (i : n) :
    scalar n ((A : Matrix n n R) i i) = A :=
  scalar_eq_self_of_mem_center A.property i

/--
theorem `mem_center_iff` / 定理 `mem_center_iff`

English:
theorem mem_center_iff
  given: {A : SpecialLinearGroup n R}
  proof: by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i⟩⟩; · exact ⟨by aesop, by simp [Subsingleton.elim A 1]⟩
  refine ⟨fun h => ⟨A i i, ?_, ?_⟩, fun ⟨r, _, hr⟩ => Subgroup.mem_center_iff.mpr fun B => ?_⟩
  · have : det ((scalar n) (A i i)) = 1 := (scalar_eq_self_of_mem_center h i).symm ▸ A.property
    si

中文:
定理 mem_center_iff
  条件: {A : SpecialLinearGroup n R}
  证明: by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i⟩⟩; · exact ⟨by aesop, by simp [Subsingleton.elim A 1]⟩
  refine ⟨fun h => ⟨A i i, ?_, ?_⟩, fun ⟨r, _, hr⟩ => Subgroup.mem_center_iff.mpr fun B => ?_⟩
  · have : det ((scalar n) (A i i)) = 1 := (scalar_eq_self_of_mem_center h i).symm ▸ A.property
    si

Depends on / 依赖: A.property, Commute, Commute.all, Subgroup, Subgroup.mem_center_iff.mpr, Subsingleton, Subsingleton.elim, Subtype, Subtype.val_injective, coe_mul, isEmpty_or_nonempty, mem_center_iff, property, scalar, scalar_commute, scalar_eq_self_of_mem_center, val_injective
-/
theorem mem_center_iff {A : SpecialLinearGroup n R} :
    A in center (SpecialLinearGroup n R) ↔ exists (r : R), r ^ (Fintype.card n) = 1 ∧ scalar n r = A := by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i⟩⟩; · exact ⟨by aesop, by simp [Subsingleton.elim A 1]⟩
  refine ⟨fun h => ⟨A i i, ?_, ?_⟩, fun ⟨r, _, hr⟩ => Subgroup.mem_center_iff.mpr fun B => ?_⟩
  · have : det ((scalar n) (A i i)) = 1 := (scalar_eq_self_of_mem_center h i).symm ▸ A.property
    simpa using! this
  · exact scalar_eq_self_of_mem_center h i
  · suffices ↑ₘ(B * A) = ↑ₘ(A * B) from Subtype.val_injective this
    simpa only [coe_mul, ← hr] using! (scalar_commute (n := n) r (Commute.all r) B).symm

set_option backward.isDefEq.respectTransparency false in
/-- An equivalence of groups, from the center of the special linear group to the roots of unity. -/
@[simps]
/--
Definition of `center_equiv_rootsOfUnity'` / `center_equiv_rootsOfUnity'` 的定义

English:
definition center_equiv_rootsOfUnity'
  signature: (i : n)
  body: haveI : Nonempty n := ⟨i⟩
rootsOfUnity.mkOfPowEq (↑ₘA i i) by
      obtain ⟨r, hr, hr'⟩ := mem_center_iff.mp A.property
      replace hr' : A.val i i = r := by simp only [← hr', scalar_apply, diagonal_apply_eq]
      simp only [hr', hr]
  invFun a := ⟨⟨a • (1 : Matrix n n R), by aesop⟩,
Subgroup.mem

中文:
定义 center_equiv_rootsOfUnity'
  签名: (i : n)
  定义体: haveI : Nonempty n := ⟨i⟩
rootsOfUnity.mkOfPowEq (↑ₘA i i) by
      obtain ⟨r, hr, hr'⟩ := mem_center_iff.mp A.property
      replace hr' : A.val i i = r := by simp only [← hr', scalar_apply, diagonal_apply_eq]
      simp only [hr', hr]
  invFun a := ⟨⟨a • (1 : Matrix n n R), by aesop⟩,
Subgroup.mem

Depends on / 依赖: A.property, A.val, Matrix, Nonempty, SetCoe, SetCoe.ext, Subgroup, Subgroup.mem_center_iff.mpr, Submonoid, Submonoid.smul_def, Subtype, Subtype.val_injective, Units.smul_def, coe_mul, diagonal_apply_eq, invFun, left_inv, mem_center_iff, mem_center_iff.mp, mkOfPowEq
-/
def center_equiv_rootsOfUnity' (i : n) :
    center (SpecialLinearGroup n R) ≃* rootsOfUnity (Fintype.card n) R where
  toFun A :=
    haveI : Nonempty n := ⟨i⟩
rootsOfUnity.mkOfPowEq (↑ₘA i i) by
      obtain ⟨r, hr, hr'⟩ := mem_center_iff.mp A.property
      replace hr' : A.val i i = r := by simp only [← hr', scalar_apply, diagonal_apply_eq]
      simp only [hr', hr]
  invFun a := ⟨⟨a • (1 : Matrix n n R), by aesop⟩,
Subgroup.mem_center_iff.mpr fun B => Subtype.val_injective by simp [coe_mul]⟩
  left_inv A := by
refine SetCoe.ext SetCoe.ext ?_
    obtain ⟨r, _, hr⟩ := mem_center_iff.mp A.property
    simpa [← hr, Submonoid.smul_def, Units.smul_def] using! smul_one_eq_diagonal r
  right_inv a := by
    obtain ⟨⟨a, _⟩, ha⟩ := a
exact SetCoe.ext Units.ext by simp
  map_mul' A B := by
    dsimp
    ext
    simp only [rootsOfUnity.val_mkOfPowEq_coe, Subgroup.coe_mul, Units.val_mul]
    rw [← scalar_eq_coe_self_center A i]; rw [← scalar_eq_coe_self_center B i]
    simp

open scoped Classical in
/--
Definition of `center_equiv_rootsOfUnity` / `center_equiv_rootsOfUnity` 的定义

English:
definition center_equiv_rootsOfUnity
  signature: :
  body: (isEmpty_or_nonempty n).by_cases
  (fun hn => by
    rw [center_eq_bot_of_subsingleton]; rw [Fintype.card_eq_zero]; rw [max_eq_right_of_lt zero_lt_one]; rw [rootsOfUnity_one]
    exact MulEquiv.ofUnique)
  (fun _ =>
    (max_eq_left (NeZero.one_le : 1 <= Fintype.card n)).symm ▸
      center_equiv_ro

中文:
定义 center_equiv_rootsOfUnity
  签名: :
  定义体: (isEmpty_or_nonempty n).by_cases
  (fun hn => by
    rw [center_eq_bot_of_subsingleton]; rw [Fintype.card_eq_zero]; rw [max_eq_right_of_lt zero_lt_one]; rw [rootsOfUnity_one]
    exact MulEquiv.ofUnique)
  (fun _ =>
    (max_eq_left (NeZero.one_le : 1 <= Fintype.card n)).symm ▸
      center_equiv_ro

Depends on / 依赖: Classical, Classical.arbitrary, Fintype, Fintype.card, Fintype.card_eq_zero, MulEquiv, MulEquiv.ofUnique, NeZero, NeZero.one_le, arbitrary, card_eq_zero, center_eq_bot_of_subsingleton, center_equiv_rootsOfUnity, isEmpty_or_nonempty, max_eq_left, max_eq_right_of_lt, ofUnique, one_le, rootsOfUnity_one, zero_lt_one
-/
noncomputable def center_equiv_rootsOfUnity :
    center (SpecialLinearGroup n R) ≃* rootsOfUnity (max (Fintype.card n) 1) R :=
  (isEmpty_or_nonempty n).by_cases
  (fun hn => by
    rw [center_eq_bot_of_subsingleton]; rw [Fintype.card_eq_zero]; rw [max_eq_right_of_lt zero_lt_one]; rw [rootsOfUnity_one]
    exact MulEquiv.ofUnique)
  (fun _ =>
    (max_eq_left (NeZero.one_le : 1 <= Fintype.card n)).symm ▸
      center_equiv_rootsOfUnity' (Classical.arbitrary n))

/--
theorem `eq_scalar_center_equiv_rootsOfUnity` / 定理 `eq_scalar_center_equiv_rootsOfUnity`

English:
theorem eq_scalar_center_equiv_rootsOfUnity
  proof: by
  unfold center_equiv_rootsOfUnity Or.by_cases
  split_ifs with h
  · subsingleton
  dsimp only
  generalize_proofs _ eq
  generalize max (Fintype.card n) 1 = c at eq
  subst eq
  rw [center_equiv_rootsOfUnity'_apply]; rw [rootsOfUnity.val_mkOfPowEq_coe]; rw [scalar_eq_coe_self_center]

中文:
定理 eq_scalar_center_equiv_rootsOfUnity
  证明: by
  unfold center_equiv_rootsOfUnity Or.by_cases
  split_ifs with h
  · subsingleton
  dsimp only
  generalize_proofs _ eq
  generalize max (Fintype.card n) 1 = c at eq
  subst eq
  rw [center_equiv_rootsOfUnity'_apply]; rw [rootsOfUnity.val_mkOfPowEq_coe]; rw [scalar_eq_coe_self_center]

Depends on / 依赖: Fintype, Fintype.card, Or.by_cases, _apply, center_equiv_rootsOfUnity, generalize, generalize_proofs, rootsOfUnity, rootsOfUnity.val_mkOfPowEq_coe, scalar_eq_coe_self_center, split_ifs, subsingleton, val_mkOfPowEq_coe
-/
theorem eq_scalar_center_equiv_rootsOfUnity
    (A : center (SpecialLinearGroup n R)) :
    A = scalar n ((Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity A : Rˣ) : R) := by
  unfold center_equiv_rootsOfUnity Or.by_cases
  split_ifs with h
  · subsingleton
  dsimp only
  generalize_proofs _ eq
  generalize max (Fintype.card n) 1 = c at eq
  subst eq
  rw [center_equiv_rootsOfUnity'_apply]; rw [rootsOfUnity.val_mkOfPowEq_coe]; rw [scalar_eq_coe_self_center]

end center

section cast

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (SpecialLinearGroup n Int) (SpecialLinearGroup n R)
  body: ⟨fun x => map (Int.castRingHom R) x⟩

中文:
实例 :
  签名: Coe (SpecialLinearGroup n 整数) (SpecialLinearGroup n R)
  定义体: ⟨fun x => map (Int.castRingHom R) x⟩

Depends on / 依赖: Int.castRingHom, castRingHom
-/
instance : Coe (SpecialLinearGroup n Int) (SpecialLinearGroup n R) :=
  ⟨fun x => map (Int.castRingHom R) x⟩

/--
theorem `coe_matrix_coe` / 定理 `coe_matrix_coe`

English:
theorem coe_matrix_coe
  given: (g : SpecialLinearGroup n Int)
  proof: map_apply_coe (Int.castRingHom R) g

中文:
定理 coe_matrix_coe
  条件: (g : SpecialLinearGroup n 整数)
  证明: map_apply_coe (Int.castRingHom R) g

Depends on / 依赖: Int.castRingHom, castRingHom, map_apply_coe
-/
theorem coe_matrix_coe (g : SpecialLinearGroup n Int) :
    ↑(g : SpecialLinearGroup n R) = (↑g : Matrix n n Int).map (Int.castRingHom R) :=
  map_apply_coe (Int.castRingHom R) g

/--
lemma `map_intCast_injective` / 引理 `map_intCast_injective`

English:
lemma map_intCast_injective
  given: [CharZero R]
  proof: fun g h => by
  simp_rw [ext_iff, map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom,
    Matrix.map_apply, Int.cast_inj]
  tauto

@[simp]

中文:
引理 map_intCast_injective
  条件: [特征零 R]
  证明: fun g h => by
  simp_rw [ext_iff, map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom,
    Matrix.map_apply, Int.cast_inj]
  tauto

@[simp]

Depends on / 依赖: Int.cast_inj, Int.coe_castRingHom, Matrix, Matrix.map_apply, RingHom, RingHom.mapMatrix_apply, cast_inj, coe_castRingHom, ext_iff, mapMatrix_apply, map_apply, map_apply_coe, simp_rw
-/
lemma map_intCast_injective [CharZero R] :
    Function.Injective ((↑) : SpecialLinearGroup n Int -> SpecialLinearGroup n R) := fun g h => by
  simp_rw [ext_iff, map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom,
    Matrix.map_apply, Int.cast_inj]
  tauto

@[simp]
/--
lemma `map_intCast_inj` / 引理 `map_intCast_inj`

English:
lemma map_intCast_inj
  given: [CharZero R] {x y : SpecialLinearGroup n Int}
  proof: map_intCast_injective.eq_iff

中文:
引理 map_intCast_inj
  条件: [特征零 R] {x y : SpecialLinearGroup n 整数}
  证明: map_intCast_injective.eq_iff

Depends on / 依赖: eq_iff, map_intCast_injective, map_intCast_injective.eq_iff
-/
lemma map_intCast_inj [CharZero R] {x y : SpecialLinearGroup n Int} :
    (x : SpecialLinearGroup n R) = y ↔ x = y :=
  map_intCast_injective.eq_iff

end cast

section Neg

variable [Fact (Even (Fintype.card n))]

/--
Instance `instNeg` / 实例 `instNeg`

English:
instance instNeg
  signature: : Neg (SpecialLinearGroup n R)
  body: ⟨fun g => ⟨-g, by
    simpa [(@Fact.out <| Even <| Fintype.card n).neg_one_pow, g.det_coe]
      using det_smul (↑ₘg) (-1)⟩⟩

@[simp]

中文:
实例 instNeg
  签名: : 取负 (SpecialLinearGroup n R)
  定义体: ⟨fun g => ⟨-g, by
    simpa [(@Fact.out <| Even <| Fintype.card n).neg_one_pow, g.det_coe]
      using det_smul (↑ₘg) (-1)⟩⟩

@[simp]

Depends on / 依赖: Fact.out, Fintype, Fintype.card, det_coe, det_smul, g.det_coe, neg_one_pow
-/
instance instNeg : Neg (SpecialLinearGroup n R) :=
  ⟨fun g => ⟨-g, by
    simpa [(@Fact.out <| Even <| Fintype.card n).neg_one_pow, g.det_coe]
      using det_smul (↑ₘg) (-1)⟩⟩

@[simp]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  given: (g : SpecialLinearGroup n R)
  statement: ↑(-g) = -(g : Matrix n n R)
  proof: rfl

中文:
定理 coe_neg
  条件: (g : SpecialLinearGroup n R)
  结论: ↑(-g) = -(g : 矩阵 n n R)
  证明: rfl
-/
theorem coe_neg (g : SpecialLinearGroup n R) : ↑(-g) = -(g : Matrix n n R) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasDistribNeg (SpecialLinearGroup n R)
  body: Function.Injective.hasDistribNeg _ Subtype.coe_injective coe_neg coe_mul

@[simp]

中文:
实例 :
  签名: 有DistribNeg (SpecialLinearGroup n R)
  定义体: Function.Injective.hasDistribNeg _ Subtype.coe_injective coe_neg coe_mul

@[simp]

Depends on / 依赖: Function, Function.Injective.hasDistribNeg, Injective, Subtype, Subtype.coe_injective, coe_injective, coe_mul, coe_neg, hasDistribNeg
-/
instance : HasDistribNeg (SpecialLinearGroup n R) :=
  Function.Injective.hasDistribNeg _ Subtype.coe_injective coe_neg coe_mul

@[simp]
/--
theorem `coe_int_neg` / 定理 `coe_int_neg`

English:
theorem coe_int_neg
  given: (g : SpecialLinearGroup n Int)
  statement: ↑(-g) = (-↑g : SpecialLinearGroup n R)
  proof: Subtype.ext (@RingHom.mapMatrix n _ _ _ _ _ _ (Int.castRingHom R)).map_neg ↑g

中文:
定理 coe_int_neg
  条件: (g : SpecialLinearGroup n 整数)
  结论: ↑(-g) = (-↑g : SpecialLinearGroup n R)
  证明: Subtype.ext (@RingHom.mapMatrix n _ _ _ _ _ _ (Int.castRingHom R)).map_neg ↑g

Depends on / 依赖: Int.castRingHom, RingHom, RingHom.mapMatrix, Subtype, Subtype.ext, castRingHom, mapMatrix, map_neg
-/
theorem coe_int_neg (g : SpecialLinearGroup n Int) : ↑(-g) = (-↑g : SpecialLinearGroup n R) :=
Subtype.ext (@RingHom.mapMatrix n _ _ _ _ _ _ (Int.castRingHom R)).map_neg ↑g

end Neg

section SpecialCases

open scoped MatrixGroups

set_option backward.isDefEq.respectTransparency false in
/--
theorem `SL2_inv_expl_det` / 定理 `SL2_inv_expl_det`

English:
theorem SL2_inv_expl_det
  given: (A : SL(2, R))
  proof: by
  simpa [-det_coe, Matrix.det_fin_two, mul_comm] using A.2

中文:
定理 SL2_inv_expl_det
  条件: (A : SL(2, R))
  证明: by
  simpa [-det_coe, Matrix.det_fin_two, mul_comm] using A.2

Depends on / 依赖: Matrix, Matrix.det_fin_two, det_coe, det_fin_two, mul_comm
-/
theorem SL2_inv_expl_det (A : SL(2, R)) :
    det ![![A.1 1 1, -A.1 0 1], ![-A.1 1 0, A.1 0 0]] = 1 := by
  simpa [-det_coe, Matrix.det_fin_two, mul_comm] using A.2

/--
theorem `SL2_inv_expl` / 定理 `SL2_inv_expl`

English:
theorem SL2_inv_expl
  given: (A : SL(2, R))
  proof: by
  ext
  have := Matrix.adjugate_fin_two A.1
  rw [coe_inv]; rw [this]
  simp

中文:
定理 SL2_inv_expl
  条件: (A : SL(2, R))
  证明: by
  ext
  have := Matrix.adjugate_fin_two A.1
  rw [coe_inv]; rw [this]
  simp

Depends on / 依赖: Matrix, Matrix.adjugate_fin_two, adjugate_fin_two, coe_inv
-/
theorem SL2_inv_expl (A : SL(2, R)) :
    A⁻¹ = ⟨![![A.1 1 1, -A.1 0 1], ![-A.1 1 0, A.1 0 0]], SL2_inv_expl_det A⟩ := by
  ext
  have := Matrix.adjugate_fin_two A.1
  rw [coe_inv]; rw [this]
  simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `fin_two_induction` / 定理 `fin_two_induction`

English:
theorem fin_two_induction
  statement: (P : SL(2, R) -> Prop)
  proof: by
  obtain ⟨m, hm⟩ := g
  convert! h (m 0 0) (m 0 1) (m 1 0) (m 1 1) (by rwa [det_fin_two] at hm)
  ext i j; fin_cases i <;> fin_cases j <;> rfl

中文:
定理 fin_two_induction
  结论: (P : SL(2, R) -> 命题)
  证明: by
  obtain ⟨m, hm⟩ := g
  convert! h (m 0 0) (m 0 1) (m 1 0) (m 1 1) (by rwa [det_fin_two] at hm)
  ext i j; fin_cases i <;> fin_cases j <;> rfl

Depends on / 依赖: convert, det_fin_two, fin_cases
-/
theorem fin_two_induction (P : SL(2, R) -> Prop)
    (h : forall (a b c d : R) (hdet : a * d - b * c = 1), P ⟨!![a, b; c, d], by rwa [det_fin_two_of]⟩)
    (g : SL(2, R)) : P g := by
  obtain ⟨m, hm⟩ := g
  convert! h (m 0 0) (m 0 1) (m 1 0) (m 1 1) (by rwa [det_fin_two] at hm)
  ext i j; fin_cases i <;> fin_cases j <;> rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `fin_two_exists_eq_mk_of_apply_zero_one_eq_zero` / 定理 `fin_two_exists_eq_mk_of_apply_zero_one_eq_zero`

English:
theorem fin_two_exists_eq_mk_of_apply_zero_one_eq_zero
  statement: {R : Type*} [Field R] (g : SL(2, R))
  proof: by
  induction g using Matrix.SpecialLinearGroup.fin_two_induction with | h a b c d h_det =>
  replace hg : c = 0 := by simpa using hg
  have had : a * d = 1 := by rwa [hg, mul_zero, sub_zero] at h_det
  refine ⟨a, b, left_ne_zero_of_mul_eq_one had, ?_⟩
  simp_rw [eq_inv_of_mul_eq_one_right had, hg]

中文:
定理 fin_two_存在_eq_mk_of_apply_zero_one_eq_zero
  结论: {R : 类型} [域 R] (g : SL(2, R))
  证明: by
  induction g using Matrix.SpecialLinearGroup.fin_two_induction with | h a b c d h_det =>
  replace hg : c = 0 := by simpa using hg
  have had : a * d = 1 := by rwa [hg, mul_zero, sub_zero] at h_det
  refine ⟨a, b, left_ne_zero_of_mul_eq_one had, ?_⟩
  simp_rw [eq_inv_of_mul_eq_one_right had, hg]

Depends on / 依赖: Matrix, Matrix.SpecialLinearGroup.fin_two_induction, SpecialLinearGroup, eq_inv_of_mul_eq_one_right, fin_two_induction, h_det, left_ne_zero_of_mul_eq_one, mul_zero, replace, simp_rw, sub_zero
-/
theorem fin_two_exists_eq_mk_of_apply_zero_one_eq_zero {R : Type*} [Field R] (g : SL(2, R))
    (hg : g 1 0 = 0) :
    exists (a b : R) (h : a != 0), g = (⟨!![a, b; 0, a⁻¹], by simp [h]⟩ : SL(2, R)) := by
  induction g using Matrix.SpecialLinearGroup.fin_two_induction with | h a b c d h_det =>
  replace hg : c = 0 := by simpa using hg
  have had : a * d = 1 := by rwa [hg, mul_zero, sub_zero] at h_det
  refine ⟨a, b, left_ne_zero_of_mul_eq_one had, ?_⟩
  simp_rw [eq_inv_of_mul_eq_one_right had, hg]

/--
lemma `isCoprime_row` / 引理 `isCoprime_row`

English:
lemma isCoprime_row
  given: (A : SL(2, R)) (i : Fin 2)
  statement: IsCoprime (A i 0) (A i 1)
  proof: by
  refine match i with
  | 0 => ⟨A 1 1, -(A 1 0), ?_⟩
  | 1 => ⟨-(A 0 1), A 0 0, ?_⟩ <;>
  · simp_rw [det_coe A ▸ det_fin_two A.1]
    ring

中文:
引理 isCoprime_row
  条件: (A : SL(2, R)) (i : 有限集 2)
  结论: IsCoprime (A i 0) (A i 1)
  证明: by
  refine match i with
  | 0 => ⟨A 1 1, -(A 1 0), ?_⟩
  | 1 => ⟨-(A 0 1), A 0 0, ?_⟩ <;>
  · simp_rw [det_coe A ▸ det_fin_two A.1]
    ring

Depends on / 依赖: det_coe, det_fin_two, simp_rw
-/
lemma isCoprime_row (A : SL(2, R)) (i : Fin 2) : IsCoprime (A i 0) (A i 1) := by
  refine match i with
  | 0 => ⟨A 1 1, -(A 1 0), ?_⟩
  | 1 => ⟨-(A 0 1), A 0 0, ?_⟩ <;>
  · simp_rw [det_coe A ▸ det_fin_two A.1]
    ring

/--
lemma `isCoprime_col` / 引理 `isCoprime_col`

English:
lemma isCoprime_col
  given: (A : SL(2, R)) (j : Fin 2)
  statement: IsCoprime (A 0 j) (A 1 j)
  proof: by
  refine match j with
  | 0 => ⟨A 1 1, -(A 0 1), ?_⟩
  | 1 => ⟨-(A 1 0), A 0 0, ?_⟩ <;>
  · simp_rw [det_coe A ▸ det_fin_two A.1]
    ring

中文:
引理 isCoprime_col
  条件: (A : SL(2, R)) (j : 有限集 2)
  结论: IsCoprime (A 0 j) (A 1 j)
  证明: by
  refine match j with
  | 0 => ⟨A 1 1, -(A 0 1), ?_⟩
  | 1 => ⟨-(A 1 0), A 0 0, ?_⟩ <;>
  · simp_rw [det_coe A ▸ det_fin_two A.1]
    ring

Depends on / 依赖: det_coe, det_fin_two, simp_rw
-/
lemma isCoprime_col (A : SL(2, R)) (j : Fin 2) : IsCoprime (A 0 j) (A 1 j) := by
  refine match j with
  | 0 => ⟨A 1 1, -(A 0 1), ?_⟩
  | 1 => ⟨-(A 1 0), A 0 0, ?_⟩ <;>
  · simp_rw [det_coe A ▸ det_fin_two A.1]
    ring

end SpecialCases

end SpecialLinearGroup

end Matrix

namespace IsCoprime

open Matrix MatrixGroups SpecialLinearGroup

variable {R : Type*} [CommRing R]

/--
lemma `exists_SL2_col` / 引理 `exists_SL2_col`

English:
lemma exists_SL2_col
  given: {a b : R} (hab : IsCoprime a b) (j : Fin 2)
  proof: by
  obtain ⟨u, v, h⟩ := hab
  refine match j with
  | 0 => ⟨⟨!![a, -v; b, u], ?_⟩, rfl, rfl⟩
  | 1 => ⟨⟨!![v, a; -u, b], ?_⟩, rfl, rfl⟩ <;>
  · rw [Matrix.det_fin_two_of, ← h]
    ring

中文:
引理 存在_SL2_col
  条件: {a b : R} (hab : IsCoprime a b) (j : 有限集 2)
  证明: by
  obtain ⟨u, v, h⟩ := hab
  refine match j with
  | 0 => ⟨⟨!![a, -v; b, u], ?_⟩, rfl, rfl⟩
  | 1 => ⟨⟨!![v, a; -u, b], ?_⟩, rfl, rfl⟩ <;>
  · rw [Matrix.det_fin_two_of, ← h]
    ring

Depends on / 依赖: Matrix, Matrix.det_fin_two_of, det_fin_two_of
-/
lemma exists_SL2_col {a b : R} (hab : IsCoprime a b) (j : Fin 2) :
    exists g : SL(2, R), g 0 j = a ∧ g 1 j = b := by
  obtain ⟨u, v, h⟩ := hab
  refine match j with
  | 0 => ⟨⟨!![a, -v; b, u], ?_⟩, rfl, rfl⟩
  | 1 => ⟨⟨!![v, a; -u, b], ?_⟩, rfl, rfl⟩ <;>
  · rw [Matrix.det_fin_two_of, ← h]
    ring

/--
lemma `exists_SL2_row` / 引理 `exists_SL2_row`

English:
lemma exists_SL2_row
  given: {a b : R} (hab : IsCoprime a b) (i : Fin 2)
  proof: by
  obtain ⟨u, v, h⟩ := hab
  refine match i with
  | 0 => ⟨⟨!![a, b; -v, u], ?_⟩, rfl, rfl⟩
  | 1 => ⟨⟨!![v, -u; a, b], ?_⟩, rfl, rfl⟩ <;>
  · rw [Matrix.det_fin_two_of, ← h]
    ring

中文:
引理 存在_SL2_row
  条件: {a b : R} (hab : IsCoprime a b) (i : 有限集 2)
  证明: by
  obtain ⟨u, v, h⟩ := hab
  refine match i with
  | 0 => ⟨⟨!![a, b; -v, u], ?_⟩, rfl, rfl⟩
  | 1 => ⟨⟨!![v, -u; a, b], ?_⟩, rfl, rfl⟩ <;>
  · rw [Matrix.det_fin_two_of, ← h]
    ring

Depends on / 依赖: Matrix, Matrix.det_fin_two_of, det_fin_two_of
-/
lemma exists_SL2_row {a b : R} (hab : IsCoprime a b) (i : Fin 2) :
    exists g : SL(2, R), g i 0 = a ∧ g i 1 = b := by
  obtain ⟨u, v, h⟩ := hab
  refine match i with
  | 0 => ⟨⟨!![a, b; -v, u], ?_⟩, rfl, rfl⟩
  | 1 => ⟨⟨!![v, -u; a, b], ?_⟩, rfl, rfl⟩ <;>
  · rw [Matrix.det_fin_two_of, ← h]
    ring

/--
lemma `vecMulSL` / 引理 `vecMulSL`

English:
lemma vecMulSL
  given: {v : Fin 2 -> R} (hab : IsCoprime (v 0) (v 1)) (A : SL(2, R))
  proof: by
  obtain ⟨g, hg⟩ := hab.exists_SL2_row 0
  have : v = g 0 := funext fun t => by { fin_cases t <;> tauto }
  simpa only [this] using! isCoprime_row (g * A) 0

中文:
引理 vecMulSL
  条件: {v : 有限集 2 -> R} (hab : IsCoprime (v 0) (v 1)) (A : SL(2, R))
  证明: by
  obtain ⟨g, hg⟩ := hab.exists_SL2_row 0
  have : v = g 0 := funext fun t => by { fin_cases t <;> tauto }
  simpa only [this] using! isCoprime_row (g * A) 0

Depends on / 依赖: exists_SL2_row, fin_cases, hab.exists_SL2_row, isCoprime_row
-/
lemma vecMulSL {v : Fin 2 -> R} (hab : IsCoprime (v 0) (v 1)) (A : SL(2, R)) :
    IsCoprime ((v ᵥ* A.1) 0) ((v ᵥ* A.1) 1) := by
  obtain ⟨g, hg⟩ := hab.exists_SL2_row 0
  have : v = g 0 := funext fun t => by { fin_cases t <;> tauto }
  simpa only [this] using! isCoprime_row (g * A) 0

/--
lemma `mulVecSL` / 引理 `mulVecSL`

English:
lemma mulVecSL
  given: {v : Fin 2 -> R} (hab : IsCoprime (v 0) (v 1)) (A : SL(2, R))
  proof: by
  simpa only [← vecMul_transpose] using! hab.vecMulSL A.transpose

中文:
引理 mulVecSL
  条件: {v : 有限集 2 -> R} (hab : IsCoprime (v 0) (v 1)) (A : SL(2, R))
  证明: by
  simpa only [← vecMul_transpose] using! hab.vecMulSL A.transpose

Depends on / 依赖: A.transpose, hab.vecMulSL, transpose, vecMulSL, vecMul_transpose
-/
lemma mulVecSL {v : Fin 2 -> R} (hab : IsCoprime (v 0) (v 1)) (A : SL(2, R)) :
    IsCoprime ((A.1 *ᵥ v) 0) ((A.1 *ᵥ v) 1) := by
  simpa only [← vecMul_transpose] using! hab.vecMulSL A.transpose

end IsCoprime

namespace Matrix

section Action

variable {F : Type*} [CommRing F] {ι : Type*} [DecidableEq ι] [Fintype ι]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DistribMulAction (Matrix.SpecialLinearGroup ι F) (ι -> F)
  body: m.1 • v
  smul_zero _ := smul_zero (M := Matrix ι ι F) _
  smul_add _ := smul_add (M := Matrix ι ι F) _
  one_smul _ := one_smul (M := Matrix ι ι F) _
  mul_smul _ _ _ := SemigroupAction.mul_smul (α := Matrix ι ι F) _ _ _

中文:
实例 :
  签名: 分配乘法作用 (矩阵.SpecialLinearGroup ι F) (ι -> F)
  定义体: m.1 • v
  smul_zero _ := smul_zero (M := Matrix ι ι F) _
  smul_add _ := smul_add (M := Matrix ι ι F) _
  one_smul _ := one_smul (M := Matrix ι ι F) _
  mul_smul _ _ _ := SemigroupAction.mul_smul (α := Matrix ι ι F) _ _ _
-/
instance : DistribMulAction (Matrix.SpecialLinearGroup ι F) (ι -> F) where
  smul m v := m.1 • v
  smul_zero _ := smul_zero (M := Matrix ι ι F) _
  smul_add _ := smul_add (M := Matrix ι ι F) _
  one_smul _ := one_smul (M := Matrix ι ι F) _
  mul_smul _ _ _ := SemigroupAction.mul_smul (α := Matrix ι ι F) _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulCommClass (Matrix.SpecialLinearGroup ι F) F (ι -> F)
  body: show m.1 • k • v = k • m.1 • v from smul_comm _ _ _

中文:
实例 :
  签名: 标量交换类 (矩阵.SpecialLinearGroup ι F) F (ι -> F)
  定义体: show m.1 • k • v = k • m.1 • v from smul_comm _ _ _

Depends on / 依赖: smul_comm
-/
instance : SMulCommClass (Matrix.SpecialLinearGroup ι F) F (ι -> F) where
  smul_comm m k v := show m.1 • k • v = k • m.1 • v from smul_comm _ _ _

/--
lemma `SpecialLinearGroup.smul_def` / 引理 `SpecialLinearGroup.smul_def`

English:
lemma SpecialLinearGroup.smul_def
  proof: rfl

中文:
引理 SpecialLinearGroup.smul_def
  证明: rfl
-/
protected lemma SpecialLinearGroup.smul_def
    (m : Matrix.SpecialLinearGroup ι F) (v : ι -> F) :
    m • v = m.1 • v := rfl

end Action

section transvection

variable {ι F : Type*} [DecidableEq ι] [Fintype ι] [CommRing F]

/--
Definition of `SpecialLinearGroup.transvection` / `SpecialLinearGroup.transvection` 的定义

English:
definition SpecialLinearGroup.transvection
  signature: {i j : ι} (hij : i != j) (b : F)
  body: ⟨Matrix.transvection i j b, Matrix.det_transvection_of_ne i j hij b⟩

中文:
定义 SpecialLinearGroup.transvection
  签名: {i j : ι} (hij : i != j) (b : F)
  定义体: ⟨Matrix.transvection i j b, Matrix.det_transvection_of_ne i j hij b⟩

Depends on / 依赖: Matrix, Matrix.det_transvection_of_ne, Matrix.transvection, det_transvection_of_ne, transvection
-/
def SpecialLinearGroup.transvection {i j : ι} (hij : i != j) (b : F) :
    Matrix.SpecialLinearGroup ι F :=
  ⟨Matrix.transvection i j b, Matrix.det_transvection_of_ne i j hij b⟩

namespace SpecialLinearGroup

/--
lemma `transvection_coe` / 引理 `transvection_coe`

English:
lemma transvection_coe
  given: {i j : ι} (hij : i != j) (b : F)
  proof: rfl

@[simp]

中文:
引理 transvection_coe
  条件: {i j : ι} (hij : i != j) (b : F)
  证明: rfl

@[simp]
-/
lemma transvection_coe {i j : ι} (hij : i != j) (b : F) :
    (transvection hij b) = (1 : Matrix ι ι F) + single i j b := rfl

@[simp]
/--
lemma `transvection_coeff_zero` / 引理 `transvection_coeff_zero`

English:
lemma transvection_coeff_zero
  given: {i j : ι} (hij : i != j)
  proof: by ext; simp [transvection_coe]

中文:
引理 transvection_coeff_zero
  条件: {i j : ι} (hij : i != j)
  证明: by ext; simp [transvection_coe]

Depends on / 依赖: transvection_coe
-/
lemma transvection_coeff_zero {i j : ι} (hij : i != j) :
    transvection hij (0 : F) = 1 := by ext; simp [transvection_coe]

/--
lemma `transvection_smul_single_fst` / 引理 `transvection_smul_single_fst`

English:
lemma transvection_smul_single_fst
  given: {i j : ι} (hij : i != j) (b : F)
  proof: by
  simp [SpecialLinearGroup.smul_def, -mulVec_single, transvection_coe,
    add_mulVec, single_mulVec_eq, hij]

@[deprecated transvection_smul_single_fst (since := "2026-06-22")]

中文:
引理 transvection_smul_single_fst
  条件: {i j : ι} (hij : i != j) (b : F)
  证明: by
  simp [SpecialLinearGroup.smul_def, -mulVec_single, transvection_coe,
    add_mulVec, single_mulVec_eq, hij]

@[deprecated transvection_smul_single_fst (since := "2026-06-22")]

Depends on / 依赖: SpecialLinearGroup, SpecialLinearGroup.smul_def, add_mulVec, mulVec_single, single_mulVec_eq, smul_def, transvection_coe
-/
lemma transvection_smul_single_fst {i j : ι} (hij : i != j) (b : F) :
    (transvection hij b) • (Pi.single i 1 : ι -> F) = Pi.single i 1 := by
  simp [SpecialLinearGroup.smul_def, -mulVec_single, transvection_coe,
    add_mulVec, single_mulVec_eq, hij]

@[deprecated transvection_smul_single_fst (since := "2026-06-22")]
/--
lemma `transvection_mulVec_single_self` / 引理 `transvection_mulVec_single_self`

English:
lemma transvection_mulVec_single_self
  given: {i j : ι} (hij : i != j) (b : F)
  proof: by
  rw [transvection_coe]
  simp [-mulVec_single, add_mulVec, single_mulVec_eq, hij]

中文:
引理 transvection_mulVec_single_self
  条件: {i j : ι} (hij : i != j) (b : F)
  证明: by
  rw [transvection_coe]
  simp [-mulVec_single, add_mulVec, single_mulVec_eq, hij]

Depends on / 依赖: add_mulVec, mulVec_single, single_mulVec_eq, transvection_coe
-/
lemma transvection_mulVec_single_self {i j : ι} (hij : i != j) (b : F) :
    (transvection hij b).1 *ᵥ (Pi.single i (1 : F)) = Pi.single i 1 := by
  rw [transvection_coe]
  simp [-mulVec_single, add_mulVec, single_mulVec_eq, hij]

/--
lemma `transvection_smul_single_snd` / 引理 `transvection_smul_single_snd`

English:
lemma transvection_smul_single_snd
  given: {i j : ι} (hij : i != j) (b : F)
  proof: by
  simp [SpecialLinearGroup.smul_def, transvection_coe, -mulVec_single,
    add_mulVec, single_mulVec_eq]

@[deprecated transvection_smul_single_snd (since := "2026-06-22")]

中文:
引理 transvection_smul_single_snd
  条件: {i j : ι} (hij : i != j) (b : F)
  证明: by
  simp [SpecialLinearGroup.smul_def, transvection_coe, -mulVec_single,
    add_mulVec, single_mulVec_eq]

@[deprecated transvection_smul_single_snd (since := "2026-06-22")]

Depends on / 依赖: SpecialLinearGroup, SpecialLinearGroup.smul_def, add_mulVec, mulVec_single, single_mulVec_eq, smul_def, transvection_coe
-/
lemma transvection_smul_single_snd {i j : ι} (hij : i != j) (b : F) :
    (transvection hij b) • (Pi.single j 1 : ι -> F) = Pi.single j 1 + b • Pi.single i 1 := by
  simp [SpecialLinearGroup.smul_def, transvection_coe, -mulVec_single,
    add_mulVec, single_mulVec_eq]

@[deprecated transvection_smul_single_snd (since := "2026-06-22")]
/--
lemma `transvection_mulVec_single_other` / 引理 `transvection_mulVec_single_other`

English:
lemma transvection_mulVec_single_other
  given: {i j : ι} (hij : i != j) (b : F)
  proof: by
  rw [transvection_coe]
  simp [-mulVec_single, add_mulVec, single_mulVec_eq]

中文:
引理 transvection_mulVec_single_other
  条件: {i j : ι} (hij : i != j) (b : F)
  证明: by
  rw [transvection_coe]
  simp [-mulVec_single, add_mulVec, single_mulVec_eq]

Depends on / 依赖: add_mulVec, mulVec_single, single_mulVec_eq, transvection_coe
-/
lemma transvection_mulVec_single_other {i j : ι} (hij : i != j) (b : F) :
    (transvection hij b).1 *ᵥ (Pi.single j (1 : F)) = Pi.single j 1 + b • Pi.single i 1 := by
  rw [transvection_coe]
  simp [-mulVec_single, add_mulVec, single_mulVec_eq]

/--
lemma `transvection_mul_neg` / 引理 `transvection_mul_neg`

English:
lemma transvection_mul_neg
  given: {i j : ι} (hij : i != j) (b : F)
  proof: Subtype.ext by
  simp [transvection_coe, mul_add, add_mul,
    single_mul_single_of_ne _ _ _ _ hij.symm, ← single_neg]

中文:
引理 transvection_mul_neg
  条件: {i j : ι} (hij : i != j) (b : F)
  证明: Subtype.ext by
  simp [transvection_coe, mul_add, add_mul,
    single_mul_single_of_ne _ _ _ _ hij.symm, ← single_neg]

Depends on / 依赖: Subtype, Subtype.ext, add_mul, hij.symm, mul_add, single_mul_single_of_ne, single_neg, transvection_coe
-/
lemma transvection_mul_neg {i j : ι} (hij : i != j) (b : F) :
transvection hij b * transvection hij (-b) = 1 := Subtype.ext by
  simp [transvection_coe, mul_add, add_mul,
    single_mul_single_of_ne _ _ _ _ hij.symm, ← single_neg]

/--
lemma `transvection_inv` / 引理 `transvection_inv`

English:
lemma transvection_inv
  given: {i j : ι} (hij : i != j) (b : F)
  proof: inv_eq_of_mul_eq_one_left (by rw [← transvection_mul_neg hij (-b), neg_neg])

中文:
引理 transvection_inv
  条件: {i j : ι} (hij : i != j) (b : F)
  证明: inv_eq_of_mul_eq_one_left (by rw [← transvection_mul_neg hij (-b), neg_neg])

Depends on / 依赖: inv_eq_of_mul_eq_one_left, neg_neg, transvection_mul_neg
-/
lemma transvection_inv {i j : ι} (hij : i != j) (b : F) :
    (transvection hij b)⁻¹ = transvection hij (-b) :=
  inv_eq_of_mul_eq_one_left (by rw [← transvection_mul_neg hij (-b), neg_neg])

/--
lemma `transvection_add` / 引理 `transvection_add`

English:
lemma transvection_add
  given: {i j : ι} (hij : i != j) (b₁ b₂ : F)
  proof: Subtype.ext by simp [transvection_coe, mul_add, add_mul,
    single_mul_single_of_ne _ _ _ _ hij.symm, single_add, add_assoc]

中文:
引理 transvection_add
  条件: {i j : ι} (hij : i != j) (b₁ b₂ : F)
  证明: Subtype.ext by simp [transvection_coe, mul_add, add_mul,
    single_mul_single_of_ne _ _ _ _ hij.symm, single_add, add_assoc]

Depends on / 依赖: Subtype, Subtype.ext, add_assoc, add_mul, hij.symm, mul_add, single_add, single_mul_single_of_ne, transvection_coe
-/
lemma transvection_add {i j : ι} (hij : i != j) (b₁ b₂ : F) :
    transvection hij (b₁ + b₂) = transvection hij b₁ * transvection hij b₂ :=
Subtype.ext by simp [transvection_coe, mul_add, add_mul,
    single_mul_single_of_ne _ _ _ _ hij.symm, single_add, add_assoc]

/--
lemma `transvection_mem_center_iff` / 引理 `transvection_mem_center_iff`

English:
lemma transvection_mem_center_iff
  given: {i j : ι} (hij : i != j) (b : F)
  proof: by
  refine ⟨fun h => ?_, fun hb => ?_⟩
  · obtain ⟨r, _, hr⟩ := mem_center_iff.1 h
    simpa [transvection_coe, hij] using congr($hr i j).symm
  · simp only [hb, mem_center_iff, scalar_apply, transvection_coe, single_zero,
      add_zero, diagonal_eq_one]
    exact ⟨1, one_pow _, rfl⟩

中文:
引理 transvection_mem_center_iff
  条件: {i j : ι} (hij : i != j) (b : F)
  证明: by
  refine ⟨fun h => ?_, fun hb => ?_⟩
  · obtain ⟨r, _, hr⟩ := mem_center_iff.1 h
    simpa [transvection_coe, hij] using congr($hr i j).symm
  · simp only [hb, mem_center_iff, scalar_apply, transvection_coe, single_zero,
      add_zero, diagonal_eq_one]
    exact ⟨1, one_pow _, rfl⟩

Depends on / 依赖: add_zero, diagonal_eq_one, mem_center_iff, one_pow, scalar_apply, single_zero, transvection_coe
-/
lemma transvection_mem_center_iff {i j : ι} (hij : i != j) (b : F) :
    transvection hij b in Subgroup.center (SpecialLinearGroup ι F) ↔ b = 0 := by
  refine ⟨fun h => ?_, fun hb => ?_⟩
  · obtain ⟨r, _, hr⟩ := mem_center_iff.1 h
    simpa [transvection_coe, hij] using congr($hr i j).symm
  · simp only [hb, mem_center_iff, scalar_apply, transvection_coe, single_zero,
      add_zero, diagonal_eq_one]
    exact ⟨1, one_pow _, rfl⟩

end SpecialLinearGroup

namespace TransvectionStruct

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/--
Definition of `toSpecialLinearGroup` / `toSpecialLinearGroup` 的定义

English:
definition toSpecialLinearGroup
  signature: (t : TransvectionStruct ι F)
  body: SpecialLinearGroup.transvection t.hij t.c

中文:
定义 toSpecialLinearGroup
  签名: (t : 平换结构 ι F)
  定义体: SpecialLinearGroup.transvection t.hij t.c

Depends on / 依赖: SpecialLinearGroup, SpecialLinearGroup.transvection, t.hij, transvection
-/
def toSpecialLinearGroup (t : TransvectionStruct ι F) :
    SpecialLinearGroup ι F :=
  SpecialLinearGroup.transvection t.hij t.c

/--
lemma `toSpecialLinearGroup_def` / 引理 `toSpecialLinearGroup_def`

English:
lemma toSpecialLinearGroup_def
  given: (t : TransvectionStruct ι F)
  proof: rfl

@[simp]

中文:
引理 toSpecialLinearGroup_def
  条件: (t : 平换结构 ι F)
  证明: rfl

@[simp]
-/
lemma toSpecialLinearGroup_def (t : TransvectionStruct ι F) :
    t.toSpecialLinearGroup = SpecialLinearGroup.transvection t.hij t.c := rfl

@[simp]
/--
lemma `toSpecialLinearGroup_coe` / 引理 `toSpecialLinearGroup_coe`

English:
lemma toSpecialLinearGroup_coe
  given: (t : TransvectionStruct ι F)
  proof: rfl

@[simp]

中文:
引理 toSpecialLinearGroup_coe
  条件: (t : 平换结构 ι F)
  证明: rfl

@[simp]
-/
lemma toSpecialLinearGroup_coe (t : TransvectionStruct ι F) :
    (t.toSpecialLinearGroup : Matrix ι ι F) = t.toMatrix := rfl

@[simp]
/--
lemma `toSpecialLinearGroup_mk` / 引理 `toSpecialLinearGroup_mk`

English:
lemma toSpecialLinearGroup_mk
  given: {i j : ι} (hij : i != j) (c : F)
  proof: rfl

中文:
引理 toSpecialLinearGroup_mk
  条件: {i j : ι} (hij : i != j) (c : F)
  证明: rfl
-/
lemma toSpecialLinearGroup_mk {i j : ι} (hij : i != j) (c : F) :
    (TransvectionStruct.mk i j hij c).toSpecialLinearGroup =
      SpecialLinearGroup.transvection hij c := rfl

end TransvectionStruct

end transvection

section SL2

variable {F : Type*} [Field F]

open MatrixGroups

namespace SpecialLinearGroup

/--
Definition of `diag2n` / `diag2n` 的定义

English:
definition diag2n
  signature: {ι : Type*} [Fintype ι] [DecidableEq ι] {i j : ι} (hij : i != j) (a : F)
  body: ⟨diagonal (fun k => if k = i then a else if k = j then a⁻¹ else 1), by
    simp [Finset.prod_ite, hij.symm, Finset.card_eq_one (s := {x : ι | x = i}).2 ⟨i, by grind⟩,
      mul_inv_cancel₀ ha]⟩

中文:
定义 diag2n
  签名: {ι : 类型} [有限类型 ι] [DecidableEq ι] {i j : ι} (hij : i != j) (a : F)
  定义体: ⟨diagonal (fun k => if k = i then a else if k = j then a⁻¹ else 1), by
    simp [Finset.prod_ite, hij.symm, Finset.card_eq_one (s := {x : ι | x = i}).2 ⟨i, by grind⟩,
      mul_inv_cancel₀ ha]⟩

Depends on / 依赖: Finset, Finset.card_eq_one, Finset.prod_ite, card_eq_one, diagonal, hij.symm, prod_ite
-/
noncomputable def diag2n {ι : Type*} [Fintype ι] [DecidableEq ι] {i j : ι} (hij : i != j) (a : F)
    (ha : a != 0) : SpecialLinearGroup ι F :=
  ⟨diagonal (fun k => if k = i then a else if k = j then a⁻¹ else 1), by
    simp [Finset.prod_ite, hij.symm, Finset.card_eq_one (s := {x : ι | x = i}).2 ⟨i, by grind⟩,
      mul_inv_cancel₀ ha]⟩

/--
lemma `diag2n_coe` / 引理 `diag2n_coe`

English:
lemma diag2n_coe
  statement: {ι : Type*} [Fintype ι] [DecidableEq ι] {i j : ι} (hij : i != j) (a : F)
  proof: rfl

中文:
引理 diag2n_coe
  结论: {ι : 类型} [有限类型 ι] [DecidableEq ι] {i j : ι} (hij : i != j) (a : F)
  证明: rfl
-/
lemma diag2n_coe {ι : Type*} [Fintype ι] [DecidableEq ι] {i j : ι} (hij : i != j) (a : F)
    (ha : a != 0) : (diag2n hij a ha).1 = diagonal (fun k =>
      if k = i then a else if k = j then a⁻¹ else 1) := rfl

/--
Definition of `diag2` / `diag2` 的定义

English:
abbreviation diag2
  signature: (a : F) (ha : a != 0)
  body: diag2n zero_ne_one a ha

中文:
缩写 diag2
  签名: (a : F) (ha : a != 0)
  定义体: diag2n zero_ne_one a ha

Depends on / 依赖: diag2n, zero_ne_one
-/
noncomputable abbrev diag2 (a : F) (ha : a != 0) : SL(2, F) :=
  diag2n zero_ne_one a ha

/--
lemma `diag2_def` / 引理 `diag2_def`

English:
lemma diag2_def
  given: {a : F} (ha : a != 0)
  statement: diag2 a ha = diag2n zero_ne_one a ha
  proof: rfl

中文:
引理 diag2_def
  条件: {a : F} (ha : a != 0)
  结论: diag2 a ha = diag2n zero_ne_one a ha
  证明: rfl
-/
lemma diag2_def {a : F} (ha : a != 0) : diag2 a ha = diag2n zero_ne_one a ha := rfl

/--
lemma `diag2_coe` / 引理 `diag2_coe`

English:
lemma diag2_coe
  given: (a : F) (ha : a != 0)
  proof: by simp [diag2n_coe]

中文:
引理 diag2_coe
  条件: (a : F) (ha : a != 0)
  证明: by simp [diag2n_coe]

Depends on / 依赖: diag2n_coe
-/
lemma diag2_coe (a : F) (ha : a != 0) :
    (diag2 a ha).1 = diagonal (fun i => match i with | 0 => a|1 => a⁻¹) := by simp [diag2n_coe]

/--
lemma `diag2_coe'` / 引理 `diag2_coe'`

English:
lemma diag2_coe'
  given: {a : F} (ha : a != 0)
  proof: by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag2n_coe]

中文:
引理 diag2_coe'
  条件: {a : F} (ha : a != 0)
  证明: by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag2n_coe]

Depends on / 依赖: diag2n_coe, fin_cases
-/
lemma diag2_coe' {a : F} (ha : a != 0) :
    (diag2 a ha).1 = !![a, 0; 0, a⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag2n_coe]

/--
lemma `diag2_smul_single_i₁` / 引理 `diag2_smul_single_i₁`

English:
lemma diag2_smul_single_i₁
  given: {a : F} (ha : a != 0)
  proof: by
  ext k; fin_cases k <;> simp [Matrix.SpecialLinearGroup.smul_def, diag2_coe]

中文:
引理 diag2_smul_single_i₁
  条件: {a : F} (ha : a != 0)
  证明: by
  ext k; fin_cases k <;> simp [Matrix.SpecialLinearGroup.smul_def, diag2_coe]

Depends on / 依赖: Matrix, Matrix.SpecialLinearGroup.smul_def, SpecialLinearGroup, diag2_coe, fin_cases, smul_def
-/
lemma diag2_smul_single_i₁ {a : F} (ha : a != 0) :
    diag2 a ha • (Pi.single 0 1 : Fin 2 -> F) = a • Pi.single 0 (1 : F) := by
  ext k; fin_cases k <;> simp [Matrix.SpecialLinearGroup.smul_def, diag2_coe]

/--
lemma `diag2_smul_single_i₂` / 引理 `diag2_smul_single_i₂`

English:
lemma diag2_smul_single_i₂
  given: {a : F} (ha : a != 0)
  proof: by
  ext k; fin_cases k <;> simp [Matrix.SpecialLinearGroup.smul_def, diag2_coe]

中文:
引理 diag2_smul_single_i₂
  条件: {a : F} (ha : a != 0)
  证明: by
  ext k; fin_cases k <;> simp [Matrix.SpecialLinearGroup.smul_def, diag2_coe]

Depends on / 依赖: Matrix, Matrix.SpecialLinearGroup.smul_def, SpecialLinearGroup, diag2_coe, fin_cases, smul_def
-/
lemma diag2_smul_single_i₂ {a : F} (ha : a != 0) :
    diag2 a ha • (Pi.single 1 1 : Fin 2 -> F) = a⁻¹ • Pi.single 1 (1 : F) := by
  ext k; fin_cases k <;> simp [Matrix.SpecialLinearGroup.smul_def, diag2_coe]

/--
lemma `diag2_mul_inv` / 引理 `diag2_mul_inv`

English:
lemma diag2_mul_inv
  given: (a : F) (ha : a != 0)
  proof: Subtype.ext by
  simp [diag2_coe, funext_iff, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha]

中文:
引理 diag2_mul_inv
  条件: (a : F) (ha : a != 0)
  证明: Subtype.ext by
  simp [diag2_coe, funext_iff, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha]

Depends on / 依赖: Subtype, Subtype.ext, diag2_coe, funext_iff
-/
lemma diag2_mul_inv (a : F) (ha : a != 0) :
diag2 a ha * diag2 a⁻¹ (inv_ne_zero ha) = 1 := Subtype.ext by
  simp [diag2_coe, funext_iff, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha]

/--
lemma `diag2_inv` / 引理 `diag2_inv`

English:
lemma diag2_inv
  given: (a : F) (ha : a != 0)
  proof: by
  apply inv_eq_of_mul_eq_one_right
  exact diag2_mul_inv a ha

中文:
引理 diag2_inv
  条件: (a : F) (ha : a != 0)
  证明: by
  apply inv_eq_of_mul_eq_one_right
  exact diag2_mul_inv a ha

Depends on / 依赖: diag2_mul_inv, inv_eq_of_mul_eq_one_right
-/
lemma diag2_inv (a : F) (ha : a != 0) :
    (diag2 a ha)⁻¹ = diag2 a⁻¹ (inv_ne_zero ha) := by
  apply inv_eq_of_mul_eq_one_right
  exact diag2_mul_inv a ha

section induction

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/--
Definition of `coeMonoidHom` / `coeMonoidHom` 的定义

English:
definition coeMonoidHom
  signature: : SpecialLinearGroup ι R ->* Matrix ι ι R where
  body: Subtype.val
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]

中文:
定义 coeMonoidHom
  签名: : SpecialLinearGroup ι R ->* 矩阵 ι ι R where
  定义体: Subtype.val
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]

Depends on / 依赖: Subtype, Subtype.val
-/
def coeMonoidHom : SpecialLinearGroup ι R ->* Matrix ι ι R where
  toFun := Subtype.val
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
/--
lemma `coeMonoidHom_apply` / 引理 `coeMonoidHom_apply`

English:
lemma coeMonoidHom_apply
  given: (g : SpecialLinearGroup ι R)
  statement: coeMonoidHom g = (g : Matrix ι ι R)
  proof: rfl

中文:
引理 coeMonoidHom_apply
  条件: (g : SpecialLinearGroup ι R)
  结论: coeMonoidHom g = (g : 矩阵 ι ι R)
  证明: rfl
-/
lemma coeMonoidHom_apply (g : SpecialLinearGroup ι R) : coeMonoidHom g = (g : Matrix ι ι R) := rfl

/--
lemma `coeMonoidHom_injective` / 引理 `coeMonoidHom_injective`

English:
lemma coeMonoidHom_injective
  statement: Function.Injective (coeMonoidHom : SpecialLinearGroup ι R -> _)
  proof: Subtype.val_injective

中文:
引理 coeMonoidHom_injective
  结论: 函数.单射 (coeMonoidHom : SpecialLinearGroup ι R -> _)
  证明: Subtype.val_injective

Depends on / 依赖: Subtype, Subtype.val_injective, val_injective
-/
lemma coeMonoidHom_injective : Function.Injective (coeMonoidHom : SpecialLinearGroup ι R -> _) :=
  Subtype.val_injective

/--
lemma `diag_decompose` / 引理 `diag_decompose`

English:
lemma diag_decompose
  given: (i₀ : ι) (D : ι -> F) (hD : det (diagonal D) = 1)
  proof: by
  rw [det_diagonal]; rw [show Finset.univ = insert i₀ ({i | i != i₀} : Finset ι) by grind]; rw [Finset.prod_insert (by grind)]; rw [mul_eq_one_iff_eq_inv₀ (by grind)]; rw [← Finset.prod_inv_distrib] at hD
  ext x
  by_cases hx : x = i₀
  · simpa [hx, hD, -Finset.prod_inv_distrib] using Finset.pro

中文:
引理 diag_decompose
  条件: (i₀ : ι) (D : ι -> F) (hD : det (diagonal D) = 1)
  证明: by
  rw [det_diagonal]; rw [show Finset.univ = insert i₀ ({i | i != i₀} : Finset ι) by grind]; rw [Finset.prod_insert (by grind)]; rw [mul_eq_one_iff_eq_inv₀ (by grind)]; rw [← Finset.prod_inv_distrib] at hD
  ext x
  by_cases hx : x = i₀
  · simpa [hx, hD, -Finset.prod_inv_distrib] using Finset.pro
-/
private lemma diag_decompose (i₀ : ι) (D : ι -> F) (hD : det (diagonal D) = 1) :
    Finset.prod {i | i != i₀} (fun i k => if k = i then D i else
      if k = i₀ then (D i)⁻¹ else 1 : ι -> ι -> F) = D := by
  rw [det_diagonal]; rw [show Finset.univ = insert i₀ ({i | i != i₀} : Finset ι) by grind]; rw [Finset.prod_insert (by grind)]; rw [mul_eq_one_iff_eq_inv₀ (by grind)]; rw [← Finset.prod_inv_distrib] at hD
  ext x
  by_cases hx : x = i₀
  · simpa [hx, hD, -Finset.prod_inv_distrib] using Finset.prod_congr rfl (by grind)
  · simp [hx]

/--
lemma `diagonal_neZero` / 引理 `diagonal_neZero`

English:
lemma diagonal_neZero
  given: (D : ι -> F) (hD : det (diagonal D) = 1) (j : ι)
  proof: fun h => by
  rw [det_diagonal]; rw [show Finset.univ = insert j ({i | i != j} : Finset ι) by grind]; rw [Finset.prod_insert (by grind)]; rw [h]; rw [zero_mul] at hD
  exact zero_ne_one hD

中文:
引理 diagonal_neZero
  条件: (D : ι -> F) (hD : det (diagonal D) = 1) (j : ι)
  证明: fun h => by
  rw [det_diagonal]; rw [show Finset.univ = insert j ({i | i != j} : Finset ι) by grind]; rw [Finset.prod_insert (by grind)]; rw [h]; rw [zero_mul] at hD
  exact zero_ne_one hD

Depends on / 依赖: Finset, Finset.prod_insert, Finset.univ, det_diagonal, insert, prod_insert, zero_mul, zero_ne_one
-/
lemma diagonal_neZero (D : ι -> F) (hD : det (diagonal D) = 1) (j : ι) :
    D j != 0 := fun h => by
  rw [det_diagonal]; rw [show Finset.univ = insert j ({i | i != j} : Finset ι) by grind]; rw [Finset.prod_insert (by grind)]; rw [h]; rw [zero_mul] at hD
  exact zero_ne_one hD

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `diag_commute` / 引理 `diag_commute`

English:
lemma diag_commute
  given: (i₀ : ι) (D : ι -> F) (hD : det (diagonal D) = 1)
  proof: by
  intro i1 hi1 i2 hi2 hi12
  ext i j
  simp [apply_dite, diag2n_coe]
  split_ifs <;> simp [diagonal_apply]; grind

中文:
引理 diag_commute
  条件: (i₀ : ι) (D : ι -> F) (hD : det (diagonal D) = 1)
  证明: by
  intro i1 hi1 i2 hi2 hi12
  ext i j
  simp [apply_dite, diag2n_coe]
  split_ifs <;> simp [diagonal_apply]; grind

Depends on / 依赖: apply_dite, diag2n_coe, diagonal_apply, split_ifs
-/
lemma diag_commute (i₀ : ι) (D : ι -> F) (hD : det (diagonal D) = 1) :
    (({i | i != i₀} : Finset ι) : Set ι).Pairwise (Function.onFun Commute fun i =>
      if hi : i != i₀ then diag2n hi (D i) (diagonal_neZero D hD i) else 1) := by
  intro i1 hi1 i2 hi2 hi12
  ext i j
  simp [apply_dite, diag2n_coe]
  split_ifs <;> simp [diagonal_apply]; grind

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `diag_eq_diag2n_prod` / 引理 `diag_eq_diag2n_prod`

English:
lemma diag_eq_diag2n_prod
  given: (i₀ : ι) (D : ι -> F) (hD : det (diagonal D) = 1)
  proof: by
  set g : ι -> ι -> F := fun i k => if k = i then D i else if k = i₀ then (D i)⁻¹ else 1 with hg_def
  apply coeMonoidHom_injective
  rw [Finset.map_noncommProd]
  simp_rw [coeMonoidHom_apply, apply_dite, coe_one]
  rw [Finset.noncommProd_congr (s₂ := {i | i != i₀}) rfl (fun i hi =>
      (dif_po

中文:
引理 diag_eq_diag2n_prod
  条件: (i₀ : ι) (D : ι -> F) (hD : det (diagonal D) = 1)
  证明: by
  set g : ι -> ι -> F := fun i k => if k = i then D i else if k = i₀ then (D i)⁻¹ else 1 with hg_def
  apply coeMonoidHom_injective
  rw [Finset.map_noncommProd]
  simp_rw [coeMonoidHom_apply, apply_dite, coe_one]
  rw [Finset.noncommProd_congr (s₂ := {i | i != i₀}) rfl (fun i hi =>
      (dif_po

Depends on / 依赖: Finset, Finset.map_noncommP, Finset.map_noncommProd, Finset.mem_filter, Finset.noncommProd, Finset.noncommProd_congr, apply_dite, coeMonoidHom_apply, coeMonoidHom_injective, coe_one, convert_to, diag2n, diagonal, diagonalRingHom_apply, dif_pos, hg_def, map_noncommP, map_noncommProd, mem_filter, noncommProd
-/
lemma diag_eq_diag2n_prod (i₀ : ι) (D : ι -> F) (hD : det (diagonal D) = 1) :
    (⟨diagonal D, hD⟩ : SpecialLinearGroup ι F) =
      Finset.noncommProd {i : ι | i != i₀} (fun i => if hi : i != i₀ then
      diag2n hi (D i) (diagonal_neZero D hD i) else 1) (diag_commute i₀ D hD) := by
  set g : ι -> ι -> F := fun i k => if k = i then D i else if k = i₀ then (D i)⁻¹ else 1 with hg_def
  apply coeMonoidHom_injective
  rw [Finset.map_noncommProd]
  simp_rw [coeMonoidHom_apply, apply_dite, coe_one]
  rw [Finset.noncommProd_congr (s₂ := {i | i != i₀}) rfl (fun i hi =>
      (dif_pos (Finset.mem_filter.1 hi).2 : _ = (diag2n (Finset.mem_filter.1 hi).2 _ _).1))]
  convert_to! _ = Finset.noncommProd {i | i != i₀} (fun x => diagonal (g x)) _
  simp_rw [← diagonalRingHom_apply]
  rw [← Finset.map_noncommProd _ _ (fun _ _ _ _ _ => Commute.all _ _)]; rw [Finset.noncommProd_eq_prod]
  rw [diag_decompose i₀ D hD]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `exists_list_transvec_mul_diagonal_mul_list_transvec` / 定理 `exists_list_transvec_mul_diagonal_mul_list_transvec`

English:
theorem exists_list_transvec_mul_diagonal_mul_list_transvec
  given: (M : SpecialLinearGroup ι F)
  proof: by
  obtain ⟨L, L', D, hM⟩ := Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M.1
refine ⟨L, L', D, by simpa [hM] using M.2, Subtype.ext ?_⟩
  simp_rw [coe_mul, ← coeMonoidHom_apply, map_list_prod, List.map_map, Function.comp_def,
    coeMonoidHom_apply, TransvectionStruct.toSpecialLinearG

中文:
定理 存在_list_transvec_mul_diagonal_mul_list_transvec
  条件: (M : SpecialLinearGroup ι F)
  证明: by
  obtain ⟨L, L', D, hM⟩ := Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M.1
refine ⟨L, L', D, by simpa [hM] using M.2, Subtype.ext ?_⟩
  simp_rw [coe_mul, ← coeMonoidHom_apply, map_list_prod, List.map_map, Function.comp_def,
    coeMonoidHom_apply, TransvectionStruct.toSpecialLinearG

Depends on / 依赖: Function, Function.comp_def, List.map_map, Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec, Subtype, Subtype.ext, TransvectionStruct, TransvectionStruct.toSpecialLinearGroup_coe, coeMonoidHom_apply, coe_mul, comp_def, exists_list_transvec_mul_diagonal_mul_list_transvec, map_list_prod, map_map, simp_rw, toSpecialLinearGroup_coe
-/
theorem exists_list_transvec_mul_diagonal_mul_list_transvec (M : SpecialLinearGroup ι F) :
    exists (L L' : List (TransvectionStruct ι F)) (D : ι -> F) (hD : det (diagonal D) = 1),
      M = (L.map TransvectionStruct.toSpecialLinearGroup).prod * ⟨diagonal D, hD⟩ *
        (L'.map TransvectionStruct.toSpecialLinearGroup).prod := by
  obtain ⟨L, L', D, hM⟩ := Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M.1
refine ⟨L, L', D, by simpa [hM] using M.2, Subtype.ext ?_⟩
  simp_rw [coe_mul, ← coeMonoidHom_apply, map_list_prod, List.map_map, Function.comp_def,
    coeMonoidHom_apply, TransvectionStruct.toSpecialLinearGroup_coe, hM]

/--
theorem `diagonal_transvection_induction'` / 定理 `diagonal_transvection_induction'`

English:
theorem diagonal_transvection_induction'
  statement: [Nontrivial ι] (P : SpecialLinearGroup ι F -> Prop)
  proof: by
  obtain ⟨i₀, j₀, hij₀⟩ := exists_pair_ne ι
  have hP1 : P 1 := transvection_coeff_zero (F := F) hij₀ ▸ htransvec i₀ j₀ hij₀ 0
  have hdiagonal (D : ι -> F) (hD : det (diagonal D) = 1) : P ⟨diagonal D, hD⟩ := by
    rw [diag_eq_diag2n_prod i₀ D hD]
    refine Finset.noncommProd_induction _ _ _ P 

中文:
定理 diagonal_transvection_induction'
  结论: [非平凡 ι] (P : SpecialLinearGroup ι F -> 命题)
  证明: by
  obtain ⟨i₀, j₀, hij₀⟩ := exists_pair_ne ι
  have hP1 : P 1 := transvection_coeff_zero (F := F) hij₀ ▸ htransvec i₀ j₀ hij₀ 0
  have hdiagonal (D : ι -> F) (hD : det (diagonal D) = 1) : P ⟨diagonal D, hD⟩ := by
    rw [diag_eq_diag2n_prod i₀ D hD]
    refine Finset.noncommProd_induction _ _ _ P 

Depends on / 依赖: Finset, Finset.mem_filter, Finset.noncommProd_induction, L.map, TransvectionStruct, TransvectionStruct.toSpecialLinearGroup, diag_eq_diag2n_prod, diagonal, exists_pair_ne, hdiagonal, htransvec, mem_filter, noncommProd_induction, toSpecialLinearGroup, transvection_coeff_zero
-/
theorem diagonal_transvection_induction' [Nontrivial ι] (P : SpecialLinearGroup ι F -> Prop)
    (M : SpecialLinearGroup ι F)
    (hdiag : forall (i j : ι) (hij : i != j) {c : F} (hc : c != 0), P (diag2n hij c hc))
    (htransvec : forall (i j : ι) (hij : i != j) (a : F), P (transvection hij a))
    (hmul : forall A B, P A -> P B -> P (A * B)) : P M := by
  obtain ⟨i₀, j₀, hij₀⟩ := exists_pair_ne ι
  have hP1 : P 1 := transvection_coeff_zero (F := F) hij₀ ▸ htransvec i₀ j₀ hij₀ 0
  have hdiagonal (D : ι -> F) (hD : det (diagonal D) = 1) : P ⟨diagonal D, hD⟩ := by
    rw [diag_eq_diag2n_prod i₀ D hD]
    refine Finset.noncommProd_induction _ _ _ P hmul hP1 fun i hi => ?_
    simp [(Finset.mem_filter.1 hi).2, hdiag]
  have hlist (L : List (TransvectionStruct ι F)) :
      P (L.map TransvectionStruct.toSpecialLinearGroup).prod := by
    induction L with
    | nil => simpa using hP1
    | cons t L ih =>
      rw [List.map_cons]; rw [List.prod_cons]; rw [t.toSpecialLinearGroup_def]
      exact hmul _ _ (htransvec t.i t.j t.hij t.c) ih
  obtain ⟨L, L', D, hD, hM⟩ := exists_list_transvec_mul_diagonal_mul_list_transvec M
  exact hM ▸ hmul _ _ (hmul _ _ (hlist L) (hdiagonal D hD)) (hlist L')

end induction

end SpecialLinearGroup

open Matrix.SpecialLinearGroup
open scoped commutatorElement

/--
lemma `commutator_diag2_transvection` / 引理 `commutator_diag2_transvection`

English:
lemma commutator_diag2_transvection
  statement: (a : F) (ha : a != 0) (b c : F)
  proof: by
  rw [commutatorElement_def]; rw [diag2_inv a ha]; rw [SpecialLinearGroup.transvection_inv zero_ne_one b]
refine Subtype.ext Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j
  <;> simp [hc, SpecialLinearGroup.transvection_coe, diag2_coe, mul_add, add_mul,
    mul_inv_cancel₀ ha, inv_mul_can

中文:
引理 commutator_diag2_transvection
  结论: (a : F) (ha : a != 0) (b c : F)
  证明: by
  rw [commutatorElement_def]; rw [diag2_inv a ha]; rw [SpecialLinearGroup.transvection_inv zero_ne_one b]
refine Subtype.ext Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j
  <;> simp [hc, SpecialLinearGroup.transvection_coe, diag2_coe, mul_add, add_mul,
    mul_inv_cancel₀ ha, inv_mul_can

Depends on / 依赖: Matrix, Matrix.ext, SpecialLinearGroup, SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_inv, Subtype, Subtype.ext, add_mul, commutatorElement_def, diag2_coe, diag2_inv, fin_cases, mul_add, mul_assoc, mul_comm, mul_sub_one, pow_two, sub_eq_add_neg, transvection_coe, transvection_inv
-/
lemma commutator_diag2_transvection (a : F) (ha : a != 0) (b c : F)
    (hc : c = b * (a ^ 2 - 1)) : ⁅diag2 a ha, SpecialLinearGroup.transvection zero_ne_one b⁆ =
    (SpecialLinearGroup.transvection zero_ne_one c : SL(2, F)) := by
  rw [commutatorElement_def]; rw [diag2_inv a ha]; rw [SpecialLinearGroup.transvection_inv zero_ne_one b]
refine Subtype.ext Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j
  <;> simp [hc, SpecialLinearGroup.transvection_coe, diag2_coe, mul_add, add_mul,
    mul_inv_cancel₀ ha, inv_mul_cancel₀ ha, mul_comm a b, mul_assoc b a a, ← pow_two,
    mul_sub_one, ← sub_eq_add_neg]

/--
lemma `transvection_mem_commutator₀` / 引理 `transvection_mem_commutator₀`

English:
lemma transvection_mem_commutator₀
  given: {a : F} (ha : a != 0) (hasq : a ^ 2 != 1) (c : F)
  proof: by
  rw [← commutator_diag2_transvection a ha (c / (a ^ 2 - 1)) c
    (div_mul_cancel₀ c (sub_ne_zero_of_ne hasq)).symm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

中文:
引理 transvection_mem_commutator₀
  条件: {a : F} (ha : a != 0) (hasq : a ^ 2 != 1) (c : F)
  证明: by
  rw [← commutator_diag2_transvection a ha (c / (a ^ 2 - 1)) c
    (div_mul_cancel₀ c (sub_ne_zero_of_ne hasq)).symm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

Depends on / 依赖: Subgroup, Subgroup.commutator_mem_commutator, Subgroup.mem_top, commutator_diag2_transvection, commutator_mem_commutator, mem_top, sub_ne_zero_of_ne
-/
lemma transvection_mem_commutator₀ {a : F} (ha : a != 0) (hasq : a ^ 2 != 1) (c : F) :
    SpecialLinearGroup.transvection zero_ne_one c in commutator SL(2, F) := by
  rw [← commutator_diag2_transvection a ha (c / (a ^ 2 - 1)) c
    (div_mul_cancel₀ c (sub_ne_zero_of_ne hasq)).symm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/--
lemma `transvection_mem_commutator₁` / 引理 `transvection_mem_commutator₁`

English:
lemma transvection_mem_commutator₁
  given: {a : F} (ha : a != 0) (hasq : a ^ 2 != 1) (c : F)
  proof: by
  have (b c' : F) (hc : c' = b * (a ^ 2 - 1)) :
      ⁅diag2 a⁻¹ (inv_ne_zero ha), SpecialLinearGroup.transvection one_ne_zero b⁆ =
      (SpecialLinearGroup.transvection one_ne_zero c' : SL(2, F)) := by
    rw [commutatorElement_def]; rw [diag2_inv a⁻¹ (inv_ne_zero ha)]; rw [SpecialLinearGroup.t

中文:
引理 transvection_mem_commutator₁
  条件: {a : F} (ha : a != 0) (hasq : a ^ 2 != 1) (c : F)
  证明: by
  have (b c' : F) (hc : c' = b * (a ^ 2 - 1)) :
      ⁅diag2 a⁻¹ (inv_ne_zero ha), SpecialLinearGroup.transvection one_ne_zero b⁆ =
      (SpecialLinearGroup.transvection one_ne_zero c' : SL(2, F)) := by
    rw [commutatorElement_def]; rw [diag2_inv a⁻¹ (inv_ne_zero ha)]; rw [SpecialLinearGroup.t

Depends on / 依赖: Matrix, Matrix.ext, SpecialLinearGroup, SpecialLinearGroup.transvection, SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_inv, Subtype, Subtype.ext, add_mul, commutatorElement_def, diag2_coe, diag2_inv, fin_cases, inv_inv, inv_mu, inv_ne_zero, mul_add, one_ne_zero, transvection, transvection_coe
-/
lemma transvection_mem_commutator₁ {a : F} (ha : a != 0) (hasq : a ^ 2 != 1) (c : F) :
    SpecialLinearGroup.transvection one_ne_zero c in commutator SL(2, F) := by
  have (b c' : F) (hc : c' = b * (a ^ 2 - 1)) :
      ⁅diag2 a⁻¹ (inv_ne_zero ha), SpecialLinearGroup.transvection one_ne_zero b⁆ =
      (SpecialLinearGroup.transvection one_ne_zero c' : SL(2, F)) := by
    rw [commutatorElement_def]; rw [diag2_inv a⁻¹ (inv_ne_zero ha)]; rw [SpecialLinearGroup.transvection_inv one_ne_zero b]
refine Subtype.ext Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
    simp [hc, SpecialLinearGroup.transvection_coe, diag2_coe, inv_inv, mul_add, add_mul,
      mul_inv_cancel₀ ha, inv_mul_cancel₀ ha, mul_comm a b, mul_assoc b a a, ← pow_two,
      mul_sub_one, ← sub_eq_add_neg]
  rw [← this (c / (a ^ 2 - 1)) c (div_mul_cancel₀ c (sub_ne_zero_of_ne hasq)).symm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/--
lemma `transvection_mem_commutator` / 引理 `transvection_mem_commutator`

English:
lemma transvection_mem_commutator
  statement: {a : F} (ha : a != 0) (hasq : a ^ 2 != 1) {i j : Fin 2} (h : i != j)
  proof: by
  fin_cases i
  · obtain rfl : j = 1 := by fin_cases j <;> tauto
    exact transvection_mem_commutator₀ ha hasq c
  · obtain rfl : j = 0 := by fin_cases j <;> tauto
    exact transvection_mem_commutator₁ ha hasq c

中文:
引理 transvection_mem_commutator
  结论: {a : F} (ha : a != 0) (hasq : a ^ 2 != 1) {i j : 有限集 2} (h : i != j)
  证明: by
  fin_cases i
  · obtain rfl : j = 1 := by fin_cases j <;> tauto
    exact transvection_mem_commutator₀ ha hasq c
  · obtain rfl : j = 0 := by fin_cases j <;> tauto
    exact transvection_mem_commutator₁ ha hasq c

Depends on / 依赖: fin_cases
-/
lemma transvection_mem_commutator {a : F} (ha : a != 0) (hasq : a ^ 2 != 1) {i j : Fin 2} (h : i != j)
    (c : F) : SpecialLinearGroup.transvection h c in commutator SL(2, F) := by
  fin_cases i
  · obtain rfl : j = 1 := by fin_cases j <;> tauto
    exact transvection_mem_commutator₀ ha hasq c
  · obtain rfl : j = 0 := by fin_cases j <;> tauto
    exact transvection_mem_commutator₁ ha hasq c

/--
lemma `diag2_decompose` / 引理 `diag2_decompose`

English:
lemma diag2_decompose
  given: (a : F) (ha : a != 0)
  proof: by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [diag2_coe', transvection_coe, mul_add, add_mul, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha]

中文:
引理 diag2_decompose
  条件: (a : F) (ha : a != 0)
  证明: by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [diag2_coe', transvection_coe, mul_add, add_mul, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha]

Depends on / 依赖: add_mul, diag2_coe, fin_cases, mul_add, transvection_coe
-/
lemma diag2_decompose (a : F) (ha : a != 0) :
    diag2 a ha = SpecialLinearGroup.transvection zero_ne_one a *
      SpecialLinearGroup.transvection one_ne_zero (- a⁻¹) *
      SpecialLinearGroup.transvection zero_ne_one a *
      SpecialLinearGroup.transvection zero_ne_one (-1) *
      SpecialLinearGroup.transvection one_ne_zero 1 *
      SpecialLinearGroup.transvection zero_ne_one (-1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [diag2_coe', transvection_coe, mul_add, add_mul, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha]

/--
theorem `SL2.transvection_induction` / 定理 `SL2.transvection_induction`

English:
theorem SL2.transvection_induction
  statement: (P : SL(2, F) -> Prop)
  proof: by
  refine diagonal_transvection_induction' P _ (fun i j hij c hc => ?_) htransvec hmul
  fin_cases i
  · obtain rfl : j = 1 := by fin_cases j <;> tauto
    change P (diag2 c hc)
    rw [diag2_decompose c hc]
    refine hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ ?_ ?_) ?_) ?_) ?_) ?_
    all_

中文:
定理 SL2.transvection_induction
  结论: (P : SL(2, F) -> 命题)
  证明: by
  refine diagonal_transvection_induction' P _ (fun i j hij c hc => ?_) htransvec hmul
  fin_cases i
  · obtain rfl : j = 1 := by fin_cases j <;> tauto
    change P (diag2 c hc)
    rw [diag2_decompose c hc]
    refine hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ ?_ ?_) ?_) ?_) ?_) ?_
    all_

Depends on / 依赖: all_goals, diag2_decompose, diag2n, diag2n_coe, diagonal_apply, diagonal_transvection_induction, fin_cases, htransvec, inv_ne_zero
-/
theorem SL2.transvection_induction (P : SL(2, F) -> Prop)
    (htransvec : forall (i j : Fin 2) (h : i != j) c, P (SpecialLinearGroup.transvection h c))
    (hmul : forall A B, P A -> P B -> P (A * B)) (A : SL(2, F)) : P A := by
  refine diagonal_transvection_induction' P _ (fun i j hij c hc => ?_) htransvec hmul
  fin_cases i
  · obtain rfl : j = 1 := by fin_cases j <;> tauto
    change P (diag2 c hc)
    rw [diag2_decompose c hc]
    refine hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ ?_ ?_) ?_) ?_) ?_) ?_
    all_goals exact htransvec _ _ _ _
  · obtain rfl : j = 0 := by fin_cases j <;> tauto
    rw [show diag2n hij c hc = diag2 c⁻¹ (inv_ne_zero hc) by
      ext; simp [diag2n_coe]; rw [diagonal_apply]; grind, diag2_decompose c⁻¹ (inv_ne_zero hc)]
    refine hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ ?_ ?_) ?_) ?_) ?_) ?_
    all_goals exact htransvec _ _ _ _

/--
lemma `SL2.commutator_eq_top` / 引理 `SL2.commutator_eq_top`

English:
lemma SL2.commutator_eq_top
  given: {a : F} (ha : a != 0) (hasq : a ^ 2 != 1)
  proof: le_antisymm le_top (fun A _ => SL2.transvection_induction _
    (fun _ _ => transvection_mem_commutator ha hasq) (fun _ _ => mul_mem) A)

中文:
引理 SL2.commutator_eq_top
  条件: {a : F} (ha : a != 0) (hasq : a ^ 2 != 1)
  证明: le_antisymm le_top (fun A _ => SL2.transvection_induction _
    (fun _ _ => transvection_mem_commutator ha hasq) (fun _ _ => mul_mem) A)

Depends on / 依赖: SL2.transvection_induction, le_antisymm, le_top, mul_mem, transvection_induction, transvection_mem_commutator
-/
lemma SL2.commutator_eq_top {a : F} (ha : a != 0) (hasq : a ^ 2 != 1) :
    commutator SL(2, F) = ⊤ :=
  le_antisymm le_top (fun A _ => SL2.transvection_induction _
    (fun _ _ => transvection_mem_commutator ha hasq) (fun _ _ => mul_mem) A)

end SL2

end Matrix

namespace ModularGroup

open MatrixGroups

open Matrix Matrix.SpecialLinearGroup

/--
Definition of `S` / `S` 的定义

English:
definition S
  signature: : SL(2, Int)
  body: ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩

中文:
定义 S
  签名: : SL(2, 整数)
  定义体: ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩

Depends on / 依赖: Matrix, Matrix.det_fin_two_of, det_fin_two_of
-/
def S : SL(2, Int) :=
  ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩

/--
Definition of `T` / `T` 的定义

English:
definition T
  signature: : SL(2, Int)
  body: ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[simp]

中文:
定义 T
  签名: : SL(2, 整数)
  定义体: ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[simp]

Depends on / 依赖: Matrix, Matrix.det_fin_two_of, det_fin_two_of
-/
def T : SL(2, Int) :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[simp]
/--
theorem `coe_S` / 定理 `coe_S`

English:
theorem coe_S
  statement: ↑S = !![0, -1; 1, 0]
  proof: rfl

中文:
定理 coe_S
  结论: ↑S = !![0, -1; 1, 0]
  证明: rfl
-/
theorem coe_S : ↑S = !![0, -1; 1, 0] :=
  rfl

/--
lemma `S_inv` / 引理 `S_inv`

English:
lemma S_inv
  statement: S⁻¹ = -S
  proof: by decide

@[simp]

中文:
引理 S_inv
  结论: S⁻¹ = -S
  证明: by decide

@[simp]
-/
lemma S_inv : S⁻¹ = -S := by decide

@[simp]
/--
theorem `coe_T` / 定理 `coe_T`

English:
theorem coe_T
  statement: ↑T = (!![1, 1; 0, 1] : Matrix _ _ Int)
  proof: rfl

中文:
定理 coe_T
  结论: ↑T = (!![1, 1; 0, 1] : 矩阵 _ _ 整数)
  证明: rfl
-/
theorem coe_T : ↑T = (!![1, 1; 0, 1] : Matrix _ _ Int) :=
  rfl

/--
theorem `coe_T_inv` / 定理 `coe_T_inv`

English:
theorem coe_T_inv
  statement: ↑(T⁻¹) = !![1, -1; 0, 1]
  proof: by simp [coe_inv, coe_T, adjugate_fin_two]

中文:
定理 coe_T_inv
  结论: ↑(T⁻¹) = !![1, -1; 0, 1]
  证明: by simp [coe_inv, coe_T, adjugate_fin_two]

Depends on / 依赖: adjugate_fin_two, coe_T, coe_inv
-/
theorem coe_T_inv : ↑(T⁻¹) = !![1, -1; 0, 1] := by simp [coe_inv, coe_T, adjugate_fin_two]

/--
theorem `coe_T_zpow` / 定理 `coe_T_zpow`

English:
theorem coe_T_zpow
  given: (n : Int)
  statement: (T ^ n).1 = !![1, n; 0, 1]
  proof: by
  induction n with
  | zero => rw [zpow_zero, coe_one, Matrix.one_fin_two]
  | succ n h =>
    simp_rw [zpow_add, zpow_one, coe_mul, h, coe_T, Matrix.mul_fin_two]
    congrm !![_, ?_; _, _]
    rw [mul_one]; rw [mul_one]; rw [add_comm]
  | pred n h =>
    simp_rw [zpow_sub, zpow_one, coe_mul, h, 

中文:
定理 coe_T_zpow
  条件: (n : 整数)
  结论: (T ^ n).1 = !![1, n; 0, 1]
  证明: by
  induction n with
  | zero => rw [zpow_zero, coe_one, Matrix.one_fin_two]
  | succ n h =>
    simp_rw [zpow_add, zpow_one, coe_mul, h, coe_T, Matrix.mul_fin_two]
    congrm !![_, ?_; _, _]
    rw [mul_one]; rw [mul_one]; rw [add_comm]
  | pred n h =>
    simp_rw [zpow_sub, zpow_one, coe_mul, h, 

Depends on / 依赖: Matrix, Matrix.mul_fin_two, Matrix.one_fin_two, add_comm, coe_T, coe_T_inv, coe_mul, coe_one, congrm, mul_fin_two, mul_one, one_fin_two, simp_rw, zpow_add, zpow_one, zpow_sub, zpow_zero
-/
theorem coe_T_zpow (n : Int) : (T ^ n).1 = !![1, n; 0, 1] := by
  induction n with
  | zero => rw [zpow_zero, coe_one, Matrix.one_fin_two]
  | succ n h =>
    simp_rw [zpow_add, zpow_one, coe_mul, h, coe_T, Matrix.mul_fin_two]
    congrm !![_, ?_; _, _]
    rw [mul_one]; rw [mul_one]; rw [add_comm]
  | pred n h =>
    simp_rw [zpow_sub, zpow_one, coe_mul, h, coe_T_inv, Matrix.mul_fin_two]
    congrm !![?_, ?_; _, _] <;> ring

@[simp]
/--
theorem `T_pow_mul_apply_one` / 定理 `T_pow_mul_apply_one`

English:
theorem T_pow_mul_apply_one
  given: (n : Int) (g : SL(2, Int))
  statement: (T ^ n * g) 1 = g 1
  proof: by
  ext j
  simp [coe_T_zpow, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

@[simp]

中文:
定理 T_pow_mul_apply_one
  条件: (n : 整数) (g : SL(2, 整数))
  结论: (T ^ n * g) 1 = g 1
  证明: by
  ext j
  simp [coe_T_zpow, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

@[simp]

Depends on / 依赖: Fin.sum_univ_succ, Matrix, Matrix.vecMul, coe_T_zpow, dotProduct, sum_univ_succ, vecMul
-/
theorem T_pow_mul_apply_one (n : Int) (g : SL(2, Int)) : (T ^ n * g) 1 = g 1 := by
  ext j
  simp [coe_T_zpow, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

@[simp]
/--
theorem `T_mul_apply_one` / 定理 `T_mul_apply_one`

English:
theorem T_mul_apply_one
  given: (g : SL(2, Int))
  statement: (T * g) 1 = g 1
  proof: by
  simpa using T_pow_mul_apply_one 1 g

@[simp]

中文:
定理 T_mul_apply_one
  条件: (g : SL(2, 整数))
  结论: (T * g) 1 = g 1
  证明: by
  simpa using T_pow_mul_apply_one 1 g

@[simp]

Depends on / 依赖: T_pow_mul_apply_one
-/
theorem T_mul_apply_one (g : SL(2, Int)) : (T * g) 1 = g 1 := by
  simpa using T_pow_mul_apply_one 1 g

@[simp]
/--
theorem `T_inv_mul_apply_one` / 定理 `T_inv_mul_apply_one`

English:
theorem T_inv_mul_apply_one
  given: (g : SL(2, Int))
  statement: (T⁻¹ * g) 1 = g 1
  proof: by
  simpa using T_pow_mul_apply_one (-1) g

中文:
定理 T_inv_mul_apply_one
  条件: (g : SL(2, 整数))
  结论: (T⁻¹ * g) 1 = g 1
  证明: by
  simpa using T_pow_mul_apply_one (-1) g

Depends on / 依赖: T_pow_mul_apply_one
-/
theorem T_inv_mul_apply_one (g : SL(2, Int)) : (T⁻¹ * g) 1 = g 1 := by
  simpa using T_pow_mul_apply_one (-1) g

/--
lemma `S_mul_S_eq` / 引理 `S_mul_S_eq`

English:
lemma S_mul_S_eq
  statement: (S : Matrix (Fin 2) (Fin 2) Int) * S = -1
  proof: by
  simp only [S, Int.reduceNeg, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd,
    vecMul_cons, head_cons, zero_smul, tail_cons, neg_smul, one_smul, neg_cons, neg_zero, neg_empty,
    empty_vecMul, add_zero, zero_add, empty_mul, Equiv.symm_apply_apply]
  exact Eq.symm (eta_fin_two (-1))

中文:
引理 S_mul_S_eq
  结论: (S : 矩阵 (有限集 2) (有限集 2) 整数) * S = -1
  证明: by
  simp only [S, Int.reduceNeg, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd,
    vecMul_cons, head_cons, zero_smul, tail_cons, neg_smul, one_smul, neg_cons, neg_zero, neg_empty,
    empty_vecMul, add_zero, zero_add, empty_mul, Equiv.symm_apply_apply]
  exact Eq.symm (eta_fin_two (-1))

Depends on / 依赖: Eq.symm, Equiv.symm_apply_apply, Int.reduceNeg, Nat.reduceAdd, Nat.succ_eq_add_one, add_zero, cons_mul, empty_mul, empty_vecMul, eta_fin_two, head_cons, neg_cons, neg_empty, neg_smul, neg_zero, one_smul, reduceAdd, reduceNeg, succ_eq_add_one, symm_apply_apply
-/
lemma S_mul_S_eq : (S : Matrix (Fin 2) (Fin 2) Int) * S = -1 := by
  simp only [S, Int.reduceNeg, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd,
    vecMul_cons, head_cons, zero_smul, tail_cons, neg_smul, one_smul, neg_cons, neg_zero, neg_empty,
    empty_vecMul, add_zero, zero_add, empty_mul, Equiv.symm_apply_apply]
  exact Eq.symm (eta_fin_two (-1))

/--
lemma `T_S_rel` / 引理 `T_S_rel`

English:
lemma T_S_rel
  statement: S • S • S • T • S • T • S = T⁻¹
  proof: by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

中文:
引理 T_S_rel
  结论: S • S • S • T • S • T • S = T⁻¹
  证明: by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

Depends on / 依赖: fin_cases
-/
lemma T_S_rel : S • S • S • T • S • T • S = T⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end ModularGroup
