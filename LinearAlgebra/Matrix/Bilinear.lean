/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Algebra.Algebra.Bilinear

/-!
# Bundled versions of multiplication for matrices

This file provides versions of `LinearMap.mulLeft` and `LinearMap.mulRight` which work for the
heterogeneous multiplication of matrices.
-/

@[expose] public section

variable {l m n o : Type*} {R A : Type*}

section NonUnitalNonAssocSemiring
variable (R) [Fintype m]

section one_side
variable [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]

section left
variable (n) [SMulCommClass R A A]

/-- A version of `LinearMap.mulLeft` for matrix multiplication. -/
@[simps]
/--
Definition of `mulLeftLinearMap` / `mulLeftLinearMap` 的定义

English:
definition mulLeftLinearMap
  signature: (X : Matrix l m A)
  body: (X * ·)
  map_smul' := Matrix.mul_smul _
  map_add' := Matrix.mul_add _

中文:
定义 mulLeftLinearMap
  签名: (X : Matrix l m A)
  定义体: (X * ·)
  map_smul' := Matrix.mul_smul _
  map_add' := Matrix.mul_add _
-/
def mulLeftLinearMap (X : Matrix l m A) :
    Matrix m n A ->ₗ[R] Matrix l n A where
  toFun := (X * ·)
  map_smul' := Matrix.mul_smul _
  map_add' := Matrix.mul_add _

/--
theorem `mulLeftLinearMap_eq_mulLeft` / 定理 `mulLeftLinearMap_eq_mulLeft`

English:
theorem mulLeftLinearMap_eq_mulLeft
  proof: rfl

中文:
定理 mulLeftLinearMap_eq_mulLeft
  证明: rfl

Depends on / 依赖: Matrix
-/
theorem mulLeftLinearMap_eq_mulLeft :
    mulLeftLinearMap m R = LinearMap.mulLeft R (A := Matrix m m A) := rfl

/-- A version of `LinearMap.mulLeft_zero_eq_zero` for matrix multiplication. -/
@[simp]
/--
theorem `mulLeftLinearMap_zero_eq_zero` / 定理 `mulLeftLinearMap_zero_eq_zero`

English:
theorem mulLeftLinearMap_zero_eq_zero
  statement: mulLeftLinearMap n R (0 : Matrix l m A) = 0
  proof: LinearMap.ext fun _ => Matrix.zero_mul _

中文:
定理 mulLeftLinearMap_zero_eq_zero
  结论: mulLeftLinearMap n R (0 : Matrix l m A) = 0
  证明: LinearMap.ext fun _ => Matrix.zero_mul _

Depends on / 依赖: LinearMap, LinearMap.ext, Matrix, Matrix.zero_mul, zero_mul
-/
theorem mulLeftLinearMap_zero_eq_zero : mulLeftLinearMap n R (0 : Matrix l m A) = 0 :=
  LinearMap.ext fun _ => Matrix.zero_mul _

end left

section right
variable (l) [IsScalarTower R A A]

/-- A version of `LinearMap.mulRight` for matrix multiplication. -/
@[simps]
/--
Definition of `mulRightLinearMap` / `mulRightLinearMap` 的定义

English:
definition mulRightLinearMap
  signature: (Y : Matrix m n A)
  body: (· * Y)
  map_smul' _ _ := Matrix.smul_mul _ _ _
  map_add' _ _ := Matrix.add_mul _ _ _

中文:
定义 mulRightLinearMap
  签名: (Y : Matrix m n A)
  定义体: (· * Y)
  map_smul' _ _ := Matrix.smul_mul _ _ _
  map_add' _ _ := Matrix.add_mul _ _ _
-/
def mulRightLinearMap (Y : Matrix m n A) :
    Matrix l m A ->ₗ[R] Matrix l n A where
  toFun := (· * Y)
  map_smul' _ _ := Matrix.smul_mul _ _ _
  map_add' _ _ := Matrix.add_mul _ _ _

/--
theorem `mulRightLinearMap_eq_mulRight` / 定理 `mulRightLinearMap_eq_mulRight`

English:
theorem mulRightLinearMap_eq_mulRight
  proof: rfl

中文:
定理 mulRightLinearMap_eq_mulRight
  证明: rfl

Depends on / 依赖: Matrix
-/
theorem mulRightLinearMap_eq_mulRight :
    mulRightLinearMap m R = LinearMap.mulRight R (A := Matrix m m A) := rfl

/-- A version of `LinearMap.mulLeft_zero_eq_zero` for matrix multiplication. -/
@[simp]
/--
theorem `mulRightLinearMap_zero_eq_zero` / 定理 `mulRightLinearMap_zero_eq_zero`

English:
theorem mulRightLinearMap_zero_eq_zero
  statement: mulRightLinearMap l R (0 : Matrix m n A) = 0
  proof: LinearMap.ext fun _ => Matrix.mul_zero _

中文:
定理 mulRightLinearMap_zero_eq_zero
  结论: mulRightLinearMap l R (0 : Matrix m n A) = 0
  证明: LinearMap.ext fun _ => Matrix.mul_zero _

Depends on / 依赖: LinearMap, LinearMap.ext, Matrix, Matrix.mul_zero, mul_zero
-/
theorem mulRightLinearMap_zero_eq_zero : mulRightLinearMap l R (0 : Matrix m n A) = 0 :=
  LinearMap.ext fun _ => Matrix.mul_zero _

end right

end one_side

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
variable [SMulCommClass R A A] [IsScalarTower R A A]

/-- A version of `LinearMap.mul` for matrix multiplication. -/
@[simps!]
/--
Definition of `mulLinearMap` / `mulLinearMap` 的定义

English:
definition mulLinearMap
  signature: : Matrix l m A ->ₗ[R] Matrix m n A ->ₗ[R] Matrix l n A where
  body: mulLeftLinearMap n R
  map_add' _ _ := LinearMap.ext fun _ => Matrix.add_mul _ _ _
  map_smul' _ _ := LinearMap.ext fun _ => Matrix.smul_mul _ _ _

中文:
定义 mulLinearMap
  签名: : Matrix l m A ->ₗ[R] Matrix m n A ->ₗ[R] Matrix l n A where
  定义体: mulLeftLinearMap n R
  map_add' _ _ := LinearMap.ext fun _ => Matrix.add_mul _ _ _
  map_smul' _ _ := LinearMap.ext fun _ => Matrix.smul_mul _ _ _

Depends on / 依赖: mulLeftLinearMap
-/
def mulLinearMap : Matrix l m A ->ₗ[R] Matrix m n A ->ₗ[R] Matrix l n A where
  toFun := mulLeftLinearMap n R
  map_add' _ _ := LinearMap.ext fun _ => Matrix.add_mul _ _ _
  map_smul' _ _ := LinearMap.ext fun _ => Matrix.smul_mul _ _ _

/--
theorem `mulLinearMap_eq_mul` / 定理 `mulLinearMap_eq_mul`

English:
theorem mulLinearMap_eq_mul
  proof: rfl

中文:
定理 mulLinearMap_eq_mul
  证明: rfl

Depends on / 依赖: Matrix
-/
theorem mulLinearMap_eq_mul :
    mulLinearMap R = LinearMap.mul R (A := Matrix m m A) := rfl

end NonUnitalNonAssocSemiring

section NonUnital

section one_side
variable [Fintype m] [Fintype n] [Semiring R] [NonUnitalSemiring A] [Module R A]

/-- A version of `LinearMap.mulLeft_mul` for matrix multiplication. -/
@[simp]
/--
theorem `mulLeftLinearMap_mul` / 定理 `mulLeftLinearMap_mul`

English:
theorem mulLeftLinearMap_mul
  given: [SMulCommClass R A A] (a : Matrix l m A) (b : Matrix m n A)
  proof: by
  ext
  simp only [mulLeftLinearMap_apply, LinearMap.comp_apply, Matrix.mul_assoc]

中文:
定理 mulLeftLinearMap_mul
  条件: [SMulCommClass R A A] (a : Matrix l m A) (b : Matrix m n A)
  证明: by
  ext
  simp only [mulLeftLinearMap_apply, LinearMap.comp_apply, Matrix.mul_assoc]

Depends on / 依赖: LinearMap, LinearMap.comp_apply, Matrix, Matrix.mul_assoc, comp_apply, mulLeftLinearMap_apply, mul_assoc
-/
theorem mulLeftLinearMap_mul [SMulCommClass R A A] (a : Matrix l m A) (b : Matrix m n A) :
    mulLeftLinearMap o R (a * b) = (mulLeftLinearMap o R a).comp (mulLeftLinearMap o R b) := by
  ext
  simp only [mulLeftLinearMap_apply, LinearMap.comp_apply, Matrix.mul_assoc]

/-- A version of `LinearMap.mulRight_mul` for matrix multiplication. -/
@[simp]
/--
theorem `mulRightLinearMap_mul` / 定理 `mulRightLinearMap_mul`

English:
theorem mulRightLinearMap_mul
  given: [IsScalarTower R A A] (a : Matrix m n A) (b : Matrix n o A)
  proof: by
  ext
  simp only [mulRightLinearMap_apply, LinearMap.comp_apply, Matrix.mul_assoc]

中文:
定理 mulRightLinearMap_mul
  条件: [IsScalarTower R A A] (a : Matrix m n A) (b : Matrix n o A)
  证明: by
  ext
  simp only [mulRightLinearMap_apply, LinearMap.comp_apply, Matrix.mul_assoc]

Depends on / 依赖: LinearMap, LinearMap.comp_apply, Matrix, Matrix.mul_assoc, comp_apply, mulRightLinearMap_apply, mul_assoc
-/
theorem mulRightLinearMap_mul [IsScalarTower R A A] (a : Matrix m n A) (b : Matrix n o A) :
    mulRightLinearMap l R (a * b) = (mulRightLinearMap l R b).comp (mulRightLinearMap l R a) := by
  ext
  simp only [mulRightLinearMap_apply, LinearMap.comp_apply, Matrix.mul_assoc]

end one_side

variable [Fintype m] [Fintype n] [CommSemiring R] [NonUnitalSemiring A] [Module R A]
variable [SMulCommClass R A A] [IsScalarTower R A A]

/--
theorem `commute_mulLeftLinearMap_mulRightLinearMap` / 定理 `commute_mulLeftLinearMap_mulRightLinearMap`

English:
theorem commute_mulLeftLinearMap_mulRightLinearMap
  given: (a : Matrix l m A) (b : Matrix n o A)
  proof: by
  ext c : 1
  exact (Matrix.mul_assoc a c b).symm

中文:
定理 commute_mulLeftLinearMap_mulRightLinearMap
  条件: (a : Matrix l m A) (b : Matrix n o A)
  证明: by
  ext c : 1
  exact (Matrix.mul_assoc a c b).symm

Depends on / 依赖: Matrix, Matrix.mul_assoc, mul_assoc
-/
theorem commute_mulLeftLinearMap_mulRightLinearMap (a : Matrix l m A) (b : Matrix n o A) :
    mulLeftLinearMap o R a ∘ₗ mulRightLinearMap m R b =
      mulRightLinearMap l R b ∘ₗ mulLeftLinearMap n R a := by
  ext c : 1
  exact (Matrix.mul_assoc a c b).symm

end NonUnital

section Semiring

section one_side
variable [Fintype m] [DecidableEq m] [Semiring R] [Semiring A]

section left
variable [Module R A] [SMulCommClass R A A]

/-- A version of `LinearMap.mulLeft_one` for matrix multiplication. -/
@[simp]
/--
theorem `mulLeftLinearMap_one` / 定理 `mulLeftLinearMap_one`

English:
theorem mulLeftLinearMap_one
  statement: mulLeftLinearMap n R (1 : Matrix m m A) = LinearMap.id
  proof: LinearMap.ext fun _ => Matrix.one_mul _

omit [DecidableEq m] in

中文:
定理 mulLeftLinearMap_one
  结论: mulLeftLinearMap n R (1 : Matrix m m A) = LinearMap.id
  证明: LinearMap.ext fun _ => Matrix.one_mul _

omit [DecidableEq m] in

Depends on / 依赖: LinearMap, LinearMap.ext, Matrix, Matrix.one_mul, one_mul
-/
theorem mulLeftLinearMap_one : mulLeftLinearMap n R (1 : Matrix m m A) = LinearMap.id :=
  LinearMap.ext fun _ => Matrix.one_mul _

omit [DecidableEq m] in
/-- A version of `LinearMap.mulLeft_eq_zero_iff` for matrix multiplication. -/
@[simp]
/--
theorem `mulLeftLinearMap_eq_zero_iff` / 定理 `mulLeftLinearMap_eq_zero_iff`

English:
theorem mulLeftLinearMap_eq_zero_iff
  given: [Nonempty n] (a : Matrix l m A)
  proof: by
  constructor <;> intro h
  · inhabit n
    ext i j
    classical
    replace h := DFunLike.congr_fun h (Matrix.single j (default : n) 1)
    simpa using Matrix.ext_iff.2 h i default
  · rw [h]
    exact mulLeftLinearMap_zero_eq_zero _ _

中文:
定理 mulLeftLinearMap_eq_zero_iff
  条件: [Nonempty n] (a : Matrix l m A)
  证明: by
  constructor <;> intro h
  · inhabit n
    ext i j
    classical
    replace h := DFunLike.congr_fun h (Matrix.single j (default : n) 1)
    simpa using Matrix.ext_iff.2 h i default
  · rw [h]
    exact mulLeftLinearMap_zero_eq_zero _ _

Depends on / 依赖: DFunLike, DFunLike.congr_fun, Matrix, Matrix.ext_iff, Matrix.single, classical, congr_fun, ext_iff, inhabit, mulLeftLinearMap_zero_eq_zero, replace, single
-/
theorem mulLeftLinearMap_eq_zero_iff [Nonempty n] (a : Matrix l m A) :
    mulLeftLinearMap n R a = 0 ↔ a = 0 := by
  constructor <;> intro h
  · inhabit n
    ext i j
    classical
    replace h := DFunLike.congr_fun h (Matrix.single j (default : n) 1)
    simpa using Matrix.ext_iff.2 h i default
  · rw [h]
    exact mulLeftLinearMap_zero_eq_zero _ _

/-- A version of `LinearMap.pow_mulLeft` for matrix multiplication. -/
@[simp]
/--
theorem `pow_mulLeftLinearMap` / 定理 `pow_mulLeftLinearMap`

English:
theorem pow_mulLeftLinearMap
  given: (a : Matrix m m A) (k : Nat)
  proof: match k with
  | 0 => by rw [pow_zero, pow_zero, mulLeftLinearMap_one, Module.End.one_eq_id]
  | (n + 1) => by
    rw [pow_succ]; rw [pow_succ]; rw [mulLeftLinearMap_mul]; rw [Module.End.mul_eq_comp]; rw [pow_mulLeftLinearMap]

中文:
定理 pow_mulLeftLinearMap
  条件: (a : Matrix m m A) (k : 自然数)
  证明: match k with
  | 0 => by rw [pow_zero, pow_zero, mulLeftLinearMap_one, Module.End.one_eq_id]
  | (n + 1) => by
    rw [pow_succ]; rw [pow_succ]; rw [mulLeftLinearMap_mul]; rw [Module.End.mul_eq_comp]; rw [pow_mulLeftLinearMap]

Depends on / 依赖: Module, Module.End.mul_eq_comp, Module.End.one_eq_id, mulLeftLinearMap_mul, mulLeftLinearMap_one, mul_eq_comp, one_eq_id, pow_mulLeftLinearMap, pow_succ, pow_zero
-/
theorem pow_mulLeftLinearMap (a : Matrix m m A) (k : Nat) :
    mulLeftLinearMap n R a ^ k = mulLeftLinearMap n R (a ^ k) :=
  match k with
  | 0 => by rw [pow_zero, pow_zero, mulLeftLinearMap_one, Module.End.one_eq_id]
  | (n + 1) => by
    rw [pow_succ]; rw [pow_succ]; rw [mulLeftLinearMap_mul]; rw [Module.End.mul_eq_comp]; rw [pow_mulLeftLinearMap]

end left

section right
variable [Module R A] [IsScalarTower R A A]

/-- A version of `LinearMap.mulRight_one` for matrix multiplication. -/
@[simp]
/--
theorem `mulRightLinearMap_one` / 定理 `mulRightLinearMap_one`

English:
theorem mulRightLinearMap_one
  statement: mulRightLinearMap l R (1 : Matrix m m A) = LinearMap.id
  proof: LinearMap.ext fun _ => Matrix.mul_one _

omit [DecidableEq m] in

中文:
定理 mulRightLinearMap_one
  结论: mulRightLinearMap l R (1 : Matrix m m A) = LinearMap.id
  证明: LinearMap.ext fun _ => Matrix.mul_one _

omit [DecidableEq m] in

Depends on / 依赖: LinearMap, LinearMap.ext, Matrix, Matrix.mul_one, mul_one
-/
theorem mulRightLinearMap_one : mulRightLinearMap l R (1 : Matrix m m A) = LinearMap.id :=
  LinearMap.ext fun _ => Matrix.mul_one _

omit [DecidableEq m] in
/-- A version of `LinearMap.mulRight_eq_zero_iff` for matrix multiplication. -/
@[simp]
/--
theorem `mulRightLinearMap_eq_zero_iff` / 定理 `mulRightLinearMap_eq_zero_iff`

English:
theorem mulRightLinearMap_eq_zero_iff
  given: (a : Matrix m n A) [Nonempty l]
  proof: by
  constructor <;> intro h
  · inhabit l
    ext i j
    classical
    replace h := DFunLike.congr_fun h (Matrix.single (default : l) i 1)
    simpa using Matrix.ext_iff.2 h default j
  · rw [h]
    exact mulRightLinearMap_zero_eq_zero _ _

中文:
定理 mulRightLinearMap_eq_zero_iff
  条件: (a : Matrix m n A) [Nonempty l]
  证明: by
  constructor <;> intro h
  · inhabit l
    ext i j
    classical
    replace h := DFunLike.congr_fun h (Matrix.single (default : l) i 1)
    simpa using Matrix.ext_iff.2 h default j
  · rw [h]
    exact mulRightLinearMap_zero_eq_zero _ _

Depends on / 依赖: DFunLike, DFunLike.congr_fun, Matrix, Matrix.ext_iff, Matrix.single, classical, congr_fun, ext_iff, inhabit, mulRightLinearMap_zero_eq_zero, replace, single
-/
theorem mulRightLinearMap_eq_zero_iff (a : Matrix m n A) [Nonempty l] :
    mulRightLinearMap l R a = 0 ↔ a = 0 := by
  constructor <;> intro h
  · inhabit l
    ext i j
    classical
    replace h := DFunLike.congr_fun h (Matrix.single (default : l) i 1)
    simpa using Matrix.ext_iff.2 h default j
  · rw [h]
    exact mulRightLinearMap_zero_eq_zero _ _

/-- A version of `LinearMap.pow_mulRight` for matrix multiplication. -/
@[simp]
/--
theorem `pow_mulRightLinearMap` / 定理 `pow_mulRightLinearMap`

English:
theorem pow_mulRightLinearMap
  given: (a : Matrix m m A) (k : Nat)
  proof: match k with
  | 0 => by rw [pow_zero, pow_zero, mulRightLinearMap_one, Module.End.one_eq_id]
  | (n + 1) => by
    rw [pow_succ]; rw [pow_succ']; rw [mulRightLinearMap_mul]; rw [Module.End.mul_eq_comp]; rw [pow_mulRightLinearMap]

中文:
定理 pow_mulRightLinearMap
  条件: (a : Matrix m m A) (k : 自然数)
  证明: match k with
  | 0 => by rw [pow_zero, pow_zero, mulRightLinearMap_one, Module.End.one_eq_id]
  | (n + 1) => by
    rw [pow_succ]; rw [pow_succ']; rw [mulRightLinearMap_mul]; rw [Module.End.mul_eq_comp]; rw [pow_mulRightLinearMap]

Depends on / 依赖: Module, Module.End.mul_eq_comp, Module.End.one_eq_id, mulRightLinearMap_mul, mulRightLinearMap_one, mul_eq_comp, one_eq_id, pow_mulRightLinearMap, pow_succ, pow_zero
-/
theorem pow_mulRightLinearMap (a : Matrix m m A) (k : Nat) :
    mulRightLinearMap l R a ^ k = mulRightLinearMap l R (a ^ k) :=
  match k with
  | 0 => by rw [pow_zero, pow_zero, mulRightLinearMap_one, Module.End.one_eq_id]
  | (n + 1) => by
    rw [pow_succ]; rw [pow_succ']; rw [mulRightLinearMap_mul]; rw [Module.End.mul_eq_comp]; rw [pow_mulRightLinearMap]

end right

end one_side

end Semiring
