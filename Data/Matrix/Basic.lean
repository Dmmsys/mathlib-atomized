/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin, Lu-Ming Zhang
-/
module

public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.BigOperators.RingEquiv
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.GroupTheory.DedekindFinite

/-!
# Matrices

This file contains basic results on matrices including bundled versions of matrix operators.

## Implementation notes

For convenience, `Matrix m n α` is defined as `m → n → α`, as this allows elements of the matrix
to be accessed with `A i j`. However, it is not advisable to _construct_ matrices using terms of the
form `fun i j ↦ _` or even `(fun i j ↦ _ : Matrix m n α)`, as these are not recognized by Lean
as having the right type. Instead, `Matrix.of` should be used.

## TODO

Under various conditions, multiplication of infinite matrices makes sense.
These have not yet been implemented.
-/

@[expose] public section

assert_not_exists TrivialStar

universe u u' v w

variable {l m n o : Type*} {m' : o -> Type*} {n' : o -> Type*}
variable {R S T A α β γ : Type*}

namespace Matrix

/--
Instance `decidableEq` / 实例 `decidableEq`

English:
instance decidableEq
  signature: [DecidableEq α] [Fintype m] [Fintype n]
  body: Fintype.decidablePiFintype

中文:
实例 decidableEq
  签名: [DecidableEq α] [有限类型 m] [有限类型 n]
  定义体: Fintype.decidablePiFintype

Depends on / 依赖: Fintype, Fintype.decidablePiFintype, decidablePiFintype
-/
instance decidableEq [DecidableEq α] [Fintype m] [Fintype n] : DecidableEq (Matrix m n α) :=
  Fintype.decidablePiFintype

instance {n m} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (α) [Fintype α] :
    Fintype (Matrix m n α) := inferInstanceAs (Fintype (m -> n -> α))

instance {n m} [Finite m] [Finite n] (α) [Finite α] :
    Finite (Matrix m n α) := inferInstanceAs (Finite (m -> n -> α))

instance (priority := low) [Semiring α] [Finite α] : IsStablyFiniteRing α := ⟨inferInstance⟩

section
variable (R)

/--
Definition of `ofLinearEquiv` / `ofLinearEquiv` 的定义

English:
definition ofLinearEquiv
  signature: [Semiring R] [AddCommMonoid α] [Module R α]
  body: ofAddEquiv
  map_smul' _ _ := rfl

中文:
定义 ofLinearEquiv
  签名: [半环 R] [加法交换幺半群 α] [模 R α]
  定义体: ofAddEquiv
  map_smul' _ _ := rfl

Depends on / 依赖: ofAddEquiv
-/
def ofLinearEquiv [Semiring R] [AddCommMonoid α] [Module R α] : (m -> n -> α) ≃ₗ[R] Matrix m n α where
  __ := ofAddEquiv
  map_smul' _ _ := rfl

/--
lemma `coe_ofLinearEquiv` / 引理 `coe_ofLinearEquiv`

English:
lemma coe_ofLinearEquiv
  given: [Semiring R] [AddCommMonoid α] [Module R α]
  proof: rfl

中文:
引理 coe_ofLinearEquiv
  条件: [半环 R] [加法交换幺半群 α] [模 R α]
  证明: rfl
-/
@[simp] lemma coe_ofLinearEquiv [Semiring R] [AddCommMonoid α] [Module R α] :
    ⇑(ofLinearEquiv _ : (m -> n -> α) ≃ₗ[R] Matrix m n α) = of := rfl
/--
lemma `coe_ofLinearEquiv_symm` / 引理 `coe_ofLinearEquiv_symm`

English:
lemma coe_ofLinearEquiv_symm
  given: [Semiring R] [AddCommMonoid α] [Module R α]
  proof: rfl

中文:
引理 coe_ofLinearEquiv_symm
  条件: [半环 R] [加法交换幺半群 α] [模 R α]
  证明: rfl
-/
@[simp] lemma coe_ofLinearEquiv_symm [Semiring R] [AddCommMonoid α] [Module R α] :
    ⇑((ofLinearEquiv _).symm : Matrix m n α ≃ₗ[R] (m -> n -> α)) = of.symm := rfl

end

/--
theorem `sum_apply` / 定理 `sum_apply`

English:
theorem sum_apply
  given: [AddCommMonoid α] (i : m) (j : n) (s : Finset β) (g : β -> Matrix m n α)
  proof: (congr_fun (s.sum_apply i g) j).trans (s.sum_apply j _)

中文:
定理 sum_apply
  条件: [加法交换幺半群 α] (i : m) (j : n) (s : 有限集 β) (g : β -> 矩阵 m n α)
  证明: (congr_fun (s.sum_apply i g) j).trans (s.sum_apply j _)

Depends on / 依赖: congr_fun, s.sum_apply, sum_apply
-/
theorem sum_apply [AddCommMonoid α] (i : m) (j : n) (s : Finset β) (g : β -> Matrix m n α) :
    (∑ c in s, g c) i j = ∑ c in s, g c i j :=
  (congr_fun (s.sum_apply i g) j).trans (s.sum_apply j _)

end Matrix

open Matrix

namespace Matrix

section Diagonal

variable [DecidableEq n]

variable (n α)

/-- `Matrix.diagonal` as an `AddMonoidHom`. -/
@[simps]
/--
Definition of `diagonalAddMonoidHom` / `diagonalAddMonoidHom` 的定义

English:
definition diagonalAddMonoidHom
  signature: [AddZeroClass α]
  body: diagonal
  map_zero' := diagonal_zero
  map_add' x y := (diagonal_add x y).symm

中文:
定义 diagonalAddMonoidHom
  签名: [加法零类 α]
  定义体: diagonal
  map_zero' := diagonal_zero
  map_add' x y := (diagonal_add x y).symm

Depends on / 依赖: diagonal
-/
def diagonalAddMonoidHom [AddZeroClass α] : (n -> α) ->+ Matrix n n α where
  toFun := diagonal
  map_zero' := diagonal_zero
  map_add' x y := (diagonal_add x y).symm

variable (R)

/-- `Matrix.diagonal` as a `LinearMap`. -/
@[simps]
/--
Definition of `diagonalLinearMap` / `diagonalLinearMap` 的定义

English:
definition diagonalLinearMap
  signature: [Semiring R] [AddCommMonoid α] [Module R α]
  body: { diagonalAddMonoidHom n α with map_smul' := diagonal_smul }

中文:
定义 diagonalLinearMap
  签名: [半环 R] [加法交换幺半群 α] [模 R α]
  定义体: { diagonalAddMonoidHom n α with map_smul' := diagonal_smul }

Depends on / 依赖: diagonalAddMonoidHom, diagonal_smul, map_smul
-/
def diagonalLinearMap [Semiring R] [AddCommMonoid α] [Module R α] : (n -> α) ->ₗ[R] Matrix n n α :=
  { diagonalAddMonoidHom n α with map_smul' := diagonal_smul }

variable {n α R}

section One

variable [Zero α] [One α]

/--
lemma `zero_le_one_elem` / 引理 `zero_le_one_elem`

English:
lemma zero_le_one_elem
  given: [Preorder α] [ZeroLEOneClass α] (i j : n)
  proof: by
  by_cases hi : i = j
  · subst hi
    simp
  · simp [hi]

中文:
引理 zero_le_one_elem
  条件: [预序 α] [ZeroLEOne类 α] (i j : n)
  证明: by
  by_cases hi : i = j
  · subst hi
    simp
  · simp [hi]
-/
lemma zero_le_one_elem [Preorder α] [ZeroLEOneClass α] (i j : n) :
    0 <= (1 : Matrix n n α) i j := by
  by_cases hi : i = j
  · subst hi
    simp
  · simp [hi]

/--
lemma `zero_le_one_row` / 引理 `zero_le_one_row`

English:
lemma zero_le_one_row
  given: [Preorder α] [ZeroLEOneClass α] (i : n)
  proof: zero_le_one_elem i

中文:
引理 zero_le_one_row
  条件: [预序 α] [ZeroLEOne类 α] (i : n)
  证明: zero_le_one_elem i

Depends on / 依赖: zero_le_one_elem
-/
lemma zero_le_one_row [Preorder α] [ZeroLEOneClass α] (i : n) :
    0 <= (1 : Matrix n n α) i :=
  zero_le_one_elem i

end One

end Diagonal

section Diag

variable (n α)

/-- `Matrix.diag` as an `AddMonoidHom`. -/
@[simps]
/--
Definition of `diagAddMonoidHom` / `diagAddMonoidHom` 的定义

English:
definition diagAddMonoidHom
  signature: [AddZeroClass α]
  body: diag
  map_zero' := diag_zero
  map_add' := diag_add

中文:
定义 diagAddMonoidHom
  签名: [加法零类 α]
  定义体: diag
  map_zero' := diag_zero
  map_add' := diag_add
-/
def diagAddMonoidHom [AddZeroClass α] : Matrix n n α ->+ n -> α where
  toFun := diag
  map_zero' := diag_zero
  map_add' := diag_add

variable (R)

/-- `Matrix.diag` as a `LinearMap`. -/
@[simps]
/--
Definition of `diagLinearMap` / `diagLinearMap` 的定义

English:
definition diagLinearMap
  signature: [Semiring R] [AddCommMonoid α] [Module R α]
  body: { diagAddMonoidHom n α with map_smul' := diag_smul }

中文:
定义 diagLinearMap
  签名: [半环 R] [加法交换幺半群 α] [模 R α]
  定义体: { diagAddMonoidHom n α with map_smul' := diag_smul }

Depends on / 依赖: diagAddMonoidHom, diag_smul, map_smul
-/
def diagLinearMap [Semiring R] [AddCommMonoid α] [Module R α] : Matrix n n α ->ₗ[R] n -> α :=
  { diagAddMonoidHom n α with map_smul' := diag_smul }

variable {n α R}

@[simp]
/--
theorem `diag_list_sum` / 定理 `diag_list_sum`

English:
theorem diag_list_sum
  given: [AddMonoid α] (l : List (Matrix n n α))
  statement: diag l.sum = (l.map diag).sum
  proof: map_list_sum (diagAddMonoidHom n α) l

@[simp]

中文:
定理 diag_list_sum
  条件: [加法幺半群 α] (l : 列表 (矩阵 n n α))
  结论: diag l.求和 = (l.map diag).求和
  证明: map_list_sum (diagAddMonoidHom n α) l

@[simp]

Depends on / 依赖: diagAddMonoidHom, map_list_sum
-/
theorem diag_list_sum [AddMonoid α] (l : List (Matrix n n α)) : diag l.sum = (l.map diag).sum :=
  map_list_sum (diagAddMonoidHom n α) l

@[simp]
/--
theorem `diag_multiset_sum` / 定理 `diag_multiset_sum`

English:
theorem diag_multiset_sum
  given: [AddCommMonoid α] (s : Multiset (Matrix n n α))
  proof: map_multiset_sum (diagAddMonoidHom n α) s

@[simp]

中文:
定理 diag_multiset_sum
  条件: [加法交换幺半群 α] (s : Multiset (矩阵 n n α))
  证明: map_multiset_sum (diagAddMonoidHom n α) s

@[simp]

Depends on / 依赖: diagAddMonoidHom, map_multiset_sum
-/
theorem diag_multiset_sum [AddCommMonoid α] (s : Multiset (Matrix n n α)) :
    diag s.sum = (s.map diag).sum :=
  map_multiset_sum (diagAddMonoidHom n α) s

@[simp]
/--
theorem `diag_sum` / 定理 `diag_sum`

English:
theorem diag_sum
  given: {ι} [AddCommMonoid α] (s : Finset ι) (f : ι -> Matrix n n α)
  proof: map_sum (diagAddMonoidHom n α) f s

中文:
定理 diag_sum
  条件: {ι} [加法交换幺半群 α] (s : 有限集 ι) (f : ι -> 矩阵 n n α)
  证明: map_sum (diagAddMonoidHom n α) f s

Depends on / 依赖: diagAddMonoidHom, map_sum
-/
theorem diag_sum {ι} [AddCommMonoid α] (s : Finset ι) (f : ι -> Matrix n n α) :
    diag (∑ i in s, f i) = ∑ i in s, diag (f i) :=
  map_sum (diagAddMonoidHom n α) f s

end Diag

open Matrix

section NonAssocSemiring

variable [NonAssocSemiring α]

variable (α n)

/-- `Matrix.diagonal` as a `RingHom`. -/
@[simps]
/--
Definition of `diagonalRingHom` / `diagonalRingHom` 的定义

English:
definition diagonalRingHom
  signature: [Fintype n] [DecidableEq n]
  body: { diagonalAddMonoidHom n α with
    toFun := diagonal
    map_one' := diagonal_one
    map_mul' := fun _ _ => (diagonal_mul_diagonal' _ _).symm }

中文:
定义 diagonalRingHom
  签名: [有限类型 n] [DecidableEq n]
  定义体: { diagonalAddMonoidHom n α with
    toFun := diagonal
    map_one' := diagonal_one
    map_mul' := fun _ _ => (diagonal_mul_diagonal' _ _).symm }

Depends on / 依赖: diagonal, diagonalAddMonoidHom, diagonal_mul_diagonal, diagonal_one, map_mul, map_one
-/
def diagonalRingHom [Fintype n] [DecidableEq n] : (n -> α) ->+* Matrix n n α :=
  { diagonalAddMonoidHom n α with
    toFun := diagonal
    map_one' := diagonal_one
    map_mul' := fun _ _ => (diagonal_mul_diagonal' _ _).symm }

end NonAssocSemiring

section Semiring

variable [Semiring α]

/--
theorem `diagonal_pow` / 定理 `diagonal_pow`

English:
theorem diagonal_pow
  given: [Fintype n] [DecidableEq n] (v : n -> α) (k : Nat)
  proof: (map_pow (diagonalRingHom n α) v k).symm

中文:
定理 diagonal_pow
  条件: [有限类型 n] [DecidableEq n] (v : n -> α) (k : 自然数)
  证明: (map_pow (diagonalRingHom n α) v k).symm

Depends on / 依赖: diagonalRingHom, map_pow
-/
theorem diagonal_pow [Fintype n] [DecidableEq n] (v : n -> α) (k : Nat) :
    diagonal v ^ k = diagonal (v ^ k) :=
  (map_pow (diagonalRingHom n α) v k).symm

/--
Definition of `scalar` / `scalar` 的定义

English:
definition scalar
  signature: (n : Type u) [DecidableEq n] [Fintype n]
  body: (diagonalRingHom n α).comp Pi.constRingHom n α

中文:
定义 scalar
  签名: (n : 类型u) [DecidableEq n] [有限类型 n]
  定义体: (diagonalRingHom n α).comp Pi.constRingHom n α

Depends on / 依赖: Pi.constRingHom, constRingHom, diagonalRingHom
-/
def scalar (n : Type u) [DecidableEq n] [Fintype n] : α ->+* Matrix n n α :=
(diagonalRingHom n α).comp Pi.constRingHom n α

section Scalar

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

@[simp]
/--
theorem `scalar_apply` / 定理 `scalar_apply`

English:
theorem scalar_apply
  given: (a : α)
  statement: scalar n a = diagonal fun _ => a
  proof: rfl

中文:
定理 scalar_apply
  条件: (a : α)
  结论: scalar n a = diagonal fun _ => a
  证明: rfl
-/
theorem scalar_apply (a : α) : scalar n a = diagonal fun _ => a :=
  rfl

/--
theorem `scalar_inj` / 定理 `scalar_inj`

English:
theorem scalar_inj
  given: [Nonempty n] {r s : α}
  statement: scalar n r = scalar n s ↔ r = s
  proof: (diagonal_injective.comp Function.const_injective).eq_iff

中文:
定理 scalar_inj
  条件: [非空 n] {r s : α}
  结论: scalar n r = scalar n s ↔ r = s
  证明: (diagonal_injective.comp Function.const_injective).eq_iff

Depends on / 依赖: Function, Function.const_injective, const_injective, diagonal_injective, diagonal_injective.comp, eq_iff
-/
theorem scalar_inj [Nonempty n] {r s : α} : scalar n r = scalar n s ↔ r = s :=
  (diagonal_injective.comp Function.const_injective).eq_iff

/--
theorem `scalar_comm_iff` / 定理 `scalar_comm_iff`

English:
theorem scalar_comm_iff
  given: {r : α} {M : Matrix m n α}
  proof: by
  simp_rw [scalar_apply, ← smul_eq_diagonal_mul, ← op_smul_eq_mul_diagonal]

中文:
定理 scalar_comm_iff
  条件: {r : α} {M : 矩阵 m n α}
  证明: by
  simp_rw [scalar_apply, ← smul_eq_diagonal_mul, ← op_smul_eq_mul_diagonal]

Depends on / 依赖: op_smul_eq_mul_diagonal, scalar_apply, simp_rw, smul_eq_diagonal_mul
-/
theorem scalar_comm_iff {r : α} {M : Matrix m n α} :
    scalar m r * M = M * scalar n r ↔ r • M = MulOpposite.op r • M := by
  simp_rw [scalar_apply, ← smul_eq_diagonal_mul, ← op_smul_eq_mul_diagonal]

/--
theorem `scalar_commute_iff` / 定理 `scalar_commute_iff`

English:
theorem scalar_commute_iff
  given: {r : α} {M : Matrix n n α}
  proof: scalar_comm_iff

中文:
定理 scalar_commute_iff
  条件: {r : α} {M : 矩阵 n n α}
  证明: scalar_comm_iff

Depends on / 依赖: scalar_comm_iff
-/
theorem scalar_commute_iff {r : α} {M : Matrix n n α} :
    Commute (scalar n r) M ↔ r • M = MulOpposite.op r • M :=
  scalar_comm_iff

/--
theorem `scalar_comm` / 定理 `scalar_comm`

English:
theorem scalar_comm
  given: (r : α) (hr : forall r', Commute r r') (M : Matrix m n α)
  proof: scalar_comm_iff.2 ext fun _ _ => hr _

中文:
定理 scalar_comm
  条件: (r : α) (hr : 对任意 r', Commute r r') (M : 矩阵 m n α)
  证明: scalar_comm_iff.2 ext fun _ _ => hr _

Depends on / 依赖: scalar_comm_iff
-/
theorem scalar_comm (r : α) (hr : forall r', Commute r r') (M : Matrix m n α) :
    scalar m r * M = M * scalar n r :=
scalar_comm_iff.2 ext fun _ _ => hr _

/--
theorem `scalar_commute` / 定理 `scalar_commute`

English:
theorem scalar_commute
  given: (r : α) (hr : forall r', Commute r r') (M : Matrix n n α)
  proof: scalar_comm r hr M

中文:
定理 scalar_commute
  条件: (r : α) (hr : 对任意 r', Commute r r') (M : 矩阵 n n α)
  证明: scalar_comm r hr M

Depends on / 依赖: scalar_comm
-/
theorem scalar_commute (r : α) (hr : forall r', Commute r r') (M : Matrix n n α) :
    Commute (scalar n r) M := scalar_comm r hr M

end Scalar

end Semiring

section Algebra

variable [Fintype n] [DecidableEq n]
variable [CommSemiring R] [Semiring α] [Semiring β] [Algebra R α] [Algebra R β]

/--
Instance `instAlgebra` / 实例 `instAlgebra`

English:
instance instAlgebra
  signature: : Algebra R (Matrix n n α) where
  body: (Matrix.scalar n).comp (algebraMap R α)
  commutes' _ _ := scalar_commute _ (fun _ => Algebra.commutes _ _) _
  smul_def' r x := by ext; simp [Matrix.scalar, Algebra.smul_def r]

中文:
实例 instAlgebra
  签名: : 代数 R (矩阵 n n α) where
  定义体: (Matrix.scalar n).comp (algebraMap R α)
  commutes' _ _ := scalar_commute _ (fun _ => Algebra.commutes _ _) _
  smul_def' r x := by ext; simp [Matrix.scalar, Algebra.smul_def r]

Depends on / 依赖: Matrix, Matrix.scalar, algebraMap, scalar
-/
instance instAlgebra : Algebra R (Matrix n n α) where
  algebraMap := (Matrix.scalar n).comp (algebraMap R α)
  commutes' _ _ := scalar_commute _ (fun _ => Algebra.commutes _ _) _
  smul_def' r x := by ext; simp [Matrix.scalar, Algebra.smul_def r]

/--
theorem `algebraMap_matrix_apply` / 定理 `algebraMap_matrix_apply`

English:
theorem algebraMap_matrix_apply
  given: {r : R} {i j : n}
  proof: rfl

中文:
定理 algebraMap_matrix_apply
  条件: {r : R} {i j : n}
  证明: rfl
-/
theorem algebraMap_matrix_apply {r : R} {i j : n} :
    algebraMap R (Matrix n n α) r i j = if i = j then algebraMap R α r else 0 := rfl

/--
theorem `algebraMap_eq_diagonal` / 定理 `algebraMap_eq_diagonal`

English:
theorem algebraMap_eq_diagonal
  given: (r : R)
  proof: rfl

中文:
定理 algebraMap_eq_diagonal
  条件: (r : R)
  证明: rfl
-/
theorem algebraMap_eq_diagonal (r : R) :
    algebraMap R (Matrix n n α) r = diagonal (algebraMap R (n -> α) r) := rfl

/--
theorem `algebraMap_eq_diagonalRingHom` / 定理 `algebraMap_eq_diagonalRingHom`

English:
theorem algebraMap_eq_diagonalRingHom
  proof: rfl

@[simp]

中文:
定理 algebraMap_eq_diagonalRingHom
  证明: rfl

@[simp]
-/
theorem algebraMap_eq_diagonalRingHom :
    algebraMap R (Matrix n n α) = (diagonalRingHom n α).comp (algebraMap R _) := rfl

@[simp]
/--
theorem `map_algebraMap` / 定理 `map_algebraMap`

English:
theorem map_algebraMap
  statement: (r : R) (f : α -> β) (hf : f 0 = 0)
  proof: by
  rw [algebraMap_eq_diagonal]; rw [algebraMap_eq_diagonal]; rw [diagonal_map hf]
  simp [hf₂]

中文:
定理 map_algebraMap
  结论: (r : R) (f : α -> β) (hf : f 0 = 0)
  证明: by
  rw [algebraMap_eq_diagonal]; rw [algebraMap_eq_diagonal]; rw [diagonal_map hf]
  simp [hf₂]

Depends on / 依赖: algebraMap_eq_diagonal, diagonal_map
-/
theorem map_algebraMap (r : R) (f : α -> β) (hf : f 0 = 0)
    (hf₂ : f (algebraMap R α r) = algebraMap R β r) :
    (algebraMap R (Matrix n n α) r).map f = algebraMap R (Matrix n n β) r := by
  rw [algebraMap_eq_diagonal]; rw [algebraMap_eq_diagonal]; rw [diagonal_map hf]
  simp [hf₂]

variable (R)

/-- `Matrix.diagonal` as an `AlgHom`. -/
@[simps]
/--
Definition of `diagonalAlgHom` / `diagonalAlgHom` 的定义

English:
definition diagonalAlgHom
  signature: : (n -> α) ->ₐ[R] Matrix n n α
  body: { diagonalRingHom n α with
    toFun := diagonal
    commutes' := fun r => (algebraMap_eq_diagonal r).symm }

中文:
定义 diagonalAlgHom
  签名: : (n -> α) ->ₐ[R] 矩阵 n n α
  定义体: { diagonalRingHom n α with
    toFun := diagonal
    commutes' := fun r => (algebraMap_eq_diagonal r).symm }

Depends on / 依赖: algebraMap_eq_diagonal, commutes, diagonal, diagonalRingHom
-/
def diagonalAlgHom : (n -> α) ->ₐ[R] Matrix n n α :=
  { diagonalRingHom n α with
    toFun := diagonal
    commutes' := fun r => (algebraMap_eq_diagonal r).symm }

variable (n)

/--
Definition of `scalarAlgHom` / `scalarAlgHom` 的定义

English:
definition scalarAlgHom
  signature: : α ->ₐ[R] Matrix n n α where
  body: scalar n
  commutes' _ := rfl

中文:
定义 scalarAlgHom
  签名: : α ->ₐ[R] 矩阵 n n α where
  定义体: scalar n
  commutes' _ := rfl

Depends on / 依赖: scalar
-/
def scalarAlgHom : α ->ₐ[R] Matrix n n α where
  toRingHom := scalar n
  commutes' _ := rfl

/--
theorem `scalarAlgHom_apply` / 定理 `scalarAlgHom_apply`

English:
theorem scalarAlgHom_apply
  given: (a : α)
  statement: scalarAlgHom n R a = scalar n a
  proof: rfl

中文:
定理 scalarAlgHom_apply
  条件: (a : α)
  结论: scalarAlgHom n R a = scalar n a
  证明: rfl
-/
@[simp] theorem scalarAlgHom_apply (a : α) : scalarAlgHom n R a = scalar n a := rfl

end Algebra

section AddHom

variable [Add α]

variable (R α) in
/-- Extracting entries from a matrix as an additive homomorphism. -/
@[simps]
/--
Definition of `entryAddHom` / `entryAddHom` 的定义

English:
definition entryAddHom
  signature: (i : m) (j : n)
  body: M i j
  map_add' _ _ := rfl

中文:
定义 entryAddHom
  签名: (i : m) (j : n)
  定义体: M i j
  map_add' _ _ := rfl
-/
def entryAddHom (i : m) (j : n) : AddHom (Matrix m n α) α where
  toFun M := M i j
  map_add' _ _ := rfl

-- It is necessary to spell out the name of the coercion explicitly on the RHS
-- for unification to succeed
/--
lemma `entryAddHom_eq_comp` / 引理 `entryAddHom_eq_comp`

English:
lemma entryAddHom_eq_comp
  given: {i : m} {j : n}
  proof: rfl

中文:
引理 entryAddHom_eq_comp
  条件: {i : m} {j : n}
  证明: rfl
-/
lemma entryAddHom_eq_comp {i : m} {j : n} :
    entryAddHom α i j =
      ((Pi.evalAddHom (fun _ => α) j).comp (Pi.evalAddHom _ i)).comp
        (AddHomClass.toAddHom ofAddEquiv.symm) :=
  rfl

end AddHom

section AddMonoidHom

variable [AddZeroClass α]

variable (R α) in
/--
Extracting entries from a matrix as an additive monoid homomorphism. Note this cannot be upgraded to
a ring homomorphism, as it does not respect multiplication.
-/
@[simps]
/--
Definition of `entryAddMonoidHom` / `entryAddMonoidHom` 的定义

English:
definition entryAddMonoidHom
  signature: (i : m) (j : n)
  body: M i j
  map_add' _ _ := rfl
  map_zero' := rfl

中文:
定义 entryAddMonoidHom
  签名: (i : m) (j : n)
  定义体: M i j
  map_add' _ _ := rfl
  map_zero' := rfl
-/
def entryAddMonoidHom (i : m) (j : n) : Matrix m n α ->+ α where
  toFun M := M i j
  map_add' _ _ := rfl
  map_zero' := rfl

-- It is necessary to spell out the name of the coercion explicitly on the RHS
-- for unification to succeed
/--
lemma `entryAddMonoidHom_eq_comp` / 引理 `entryAddMonoidHom_eq_comp`

English:
lemma entryAddMonoidHom_eq_comp
  given: {i : m} {j : n}
  proof: by
  rfl

中文:
引理 entryAddMonoidHom_eq_comp
  条件: {i : m} {j : n}
  证明: by
  rfl
-/
lemma entryAddMonoidHom_eq_comp {i : m} {j : n} :
    entryAddMonoidHom α i j =
      ((Pi.evalAddMonoidHom (fun _ => α) j).comp (Pi.evalAddMonoidHom _ i)).comp
        (AddMonoidHomClass.toAddMonoidHom ofAddEquiv.symm) := by
  rfl

/--
lemma `evalAddMonoidHom_comp_diagAddMonoidHom` / 引理 `evalAddMonoidHom_comp_diagAddMonoidHom`

English:
lemma evalAddMonoidHom_comp_diagAddMonoidHom
  given: (i : m)
  proof: by
  simp [AddMonoidHom.ext_iff]

中文:
引理 evalAddMonoidHom_comp_diagAddMonoidHom
  条件: (i : m)
  证明: by
  simp [AddMonoidHom.ext_iff]
-/
@[simp] lemma evalAddMonoidHom_comp_diagAddMonoidHom (i : m) :
    (Pi.evalAddMonoidHom _ i).comp (diagAddMonoidHom m α) = entryAddMonoidHom α i i := by
  simp [AddMonoidHom.ext_iff]

/--
lemma `entryAddMonoidHom_toAddHom` / 引理 `entryAddMonoidHom_toAddHom`

English:
lemma entryAddMonoidHom_toAddHom
  given: {i : m} {j : n}
  proof: rfl

中文:
引理 entryAddMonoidHom_toAddHom
  条件: {i : m} {j : n}
  证明: rfl
-/
@[simp] lemma entryAddMonoidHom_toAddHom {i : m} {j : n} :
    (entryAddMonoidHom α i j : AddHom _ _) = entryAddHom α i j := rfl

end AddMonoidHom

section LinearMap

variable [Semiring R] [AddCommMonoid α] [Module R α]

variable (R α) in
/--
Extracting entries from a matrix as a linear map. Note this cannot be upgraded to an algebra
homomorphism, as it does not respect multiplication.
-/
@[simps]
/--
Definition of `entryLinearMap` / `entryLinearMap` 的定义

English:
definition entryLinearMap
  signature: (i : m) (j : n)
  body: M i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 entryLinearMap
  签名: (i : m) (j : n)
  定义体: M i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
-/
def entryLinearMap (i : m) (j : n) :
    Matrix m n α ->ₗ[R] α where
  toFun M := M i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

-- It is necessary to spell out the name of the coercion explicitly on the RHS
-- for unification to succeed
/--
lemma `entryLinearMap_eq_comp` / 引理 `entryLinearMap_eq_comp`

English:
lemma entryLinearMap_eq_comp
  given: {i : m} {j : n}
  proof: by
  rfl

中文:
引理 entryLinearMap_eq_comp
  条件: {i : m} {j : n}
  证明: by
  rfl
-/
lemma entryLinearMap_eq_comp {i : m} {j : n} :
    entryLinearMap R α i j =
      LinearMap.proj j ∘ₗ LinearMap.proj i ∘ₗ (ofLinearEquiv R).symm.toLinearMap := by
  rfl

/--
lemma `proj_comp_diagLinearMap` / 引理 `proj_comp_diagLinearMap`

English:
lemma proj_comp_diagLinearMap
  given: (i : m)
  proof: by
  simp [LinearMap.ext_iff]

中文:
引理 proj_comp_diagLinearMap
  条件: (i : m)
  证明: by
  simp [LinearMap.ext_iff]
-/
@[simp] lemma proj_comp_diagLinearMap (i : m) :
    LinearMap.proj i ∘ₗ diagLinearMap m R α = entryLinearMap R α i i := by
  simp [LinearMap.ext_iff]

/--
lemma `entryLinearMap_toAddMonoidHom` / 引理 `entryLinearMap_toAddMonoidHom`

English:
lemma entryLinearMap_toAddMonoidHom
  given: {i : m} {j : n}
  proof: rfl

中文:
引理 entryLinearMap_toAddMonoidHom
  条件: {i : m} {j : n}
  证明: rfl
-/
@[simp] lemma entryLinearMap_toAddMonoidHom {i : m} {j : n} :
    (entryLinearMap R α i j : _ ->+ _) = entryAddMonoidHom α i j := rfl

/--
lemma `entryLinearMap_toAddHom` / 引理 `entryLinearMap_toAddHom`

English:
lemma entryLinearMap_toAddHom
  given: {i : m} {j : n}
  proof: rfl

中文:
引理 entryLinearMap_toAddHom
  条件: {i : m} {j : n}
  证明: rfl
-/
@[simp] lemma entryLinearMap_toAddHom {i : m} {j : n} :
    (entryLinearMap R α i j : AddHom _ _) = entryAddHom α i j := rfl

end LinearMap

end Matrix

/-!
### Bundled versions of `Matrix.map`
-/


namespace Equiv

/-- The `Equiv` between spaces of matrices induced by an `Equiv` between their
coefficients. This is `Matrix.map` as an `Equiv`. -/
@[simps apply]
/--
Definition of `mapMatrix` / `mapMatrix` 的定义

English:
definition mapMatrix
  signature: (f : α ≃ β)
  body: M.map f
  invFun M := M.map f.symm
  left_inv _ := Matrix.ext fun _ _ => f.symm_apply_apply _
  right_inv _ := Matrix.ext fun _ _ => f.apply_symm_apply _

@[simp]

中文:
定义 mapMatrix
  签名: (f : α ≃ β)
  定义体: M.map f
  invFun M := M.map f.symm
  left_inv _ := Matrix.ext fun _ _ => f.symm_apply_apply _
  right_inv _ := Matrix.ext fun _ _ => f.apply_symm_apply _

@[simp]

Depends on / 依赖: M.map
-/
def mapMatrix (f : α ≃ β) : Matrix m n α ≃ Matrix m n β where
  toFun M := M.map f
  invFun M := M.map f.symm
  left_inv _ := Matrix.ext fun _ _ => f.symm_apply_apply _
  right_inv _ := Matrix.ext fun _ _ => f.apply_symm_apply _

@[simp]
/--
theorem `mapMatrix_refl` / 定理 `mapMatrix_refl`

English:
theorem mapMatrix_refl
  statement: (Equiv.refl α).mapMatrix = Equiv.refl (Matrix m n α)
  proof: rfl

@[simp]

中文:
定理 mapMatrix_refl
  结论: (等价.refl α).mapMatrix = 等价.refl (矩阵 m n α)
  证明: rfl

@[simp]
-/
theorem mapMatrix_refl : (Equiv.refl α).mapMatrix = Equiv.refl (Matrix m n α) :=
  rfl

@[simp]
/--
theorem `mapMatrix_symm` / 定理 `mapMatrix_symm`

English:
theorem mapMatrix_symm
  given: (f : α ≃ β)
  statement: f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m n β ≃ _)
  proof: rfl

@[simp]

中文:
定理 mapMatrix_symm
  条件: (f : α ≃ β)
  结论: f.mapMatrix.symm = (f.symm.mapMatrix : 矩阵 m n β ≃ _)
  证明: rfl

@[simp]
-/
theorem mapMatrix_symm (f : α ≃ β) : f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m n β ≃ _) :=
  rfl

@[simp]
/--
theorem `mapMatrix_trans` / 定理 `mapMatrix_trans`

English:
theorem mapMatrix_trans
  given: (f : α ≃ β) (g : β ≃ γ)
  proof: rfl

中文:
定理 mapMatrix_trans
  条件: (f : α ≃ β) (g : β ≃ γ)
  证明: rfl
-/
theorem mapMatrix_trans (f : α ≃ β) (g : β ≃ γ) :
    f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m n α ≃ _) :=
  rfl

end Equiv

namespace AddMonoidHom

section AddZeroClass
variable [AddZeroClass α] [AddZeroClass β] [AddZeroClass γ]

/-- The `AddMonoidHom` between spaces of matrices induced by an `AddMonoidHom` between their
coefficients. This is `Matrix.map` as an `AddMonoidHom`. -/
@[simps]
/--
Definition of `mapMatrix` / `mapMatrix` 的定义

English:
definition mapMatrix
  signature: (f : α ->+ β)
  body: M.map f
  map_zero' := Matrix.map_zero f f.map_zero
  map_add' := Matrix.map_add f f.map_add

@[simp]

中文:
定义 mapMatrix
  签名: (f : α ->+ β)
  定义体: M.map f
  map_zero' := Matrix.map_zero f f.map_zero
  map_add' := Matrix.map_add f f.map_add

@[simp]

Depends on / 依赖: M.map
-/
def mapMatrix (f : α ->+ β) : Matrix m n α ->+ Matrix m n β where
  toFun M := M.map f
  map_zero' := Matrix.map_zero f f.map_zero
  map_add' := Matrix.map_add f f.map_add

@[simp]
/--
theorem `mapMatrix_id` / 定理 `mapMatrix_id`

English:
theorem mapMatrix_id
  statement: (AddMonoidHom.id α).mapMatrix = AddMonoidHom.id (Matrix m n α)
  proof: rfl

@[simp]

中文:
定理 mapMatrix_id
  结论: (加法幺半群态射.id α).mapMatrix = 加法幺半群态射.id (矩阵 m n α)
  证明: rfl

@[simp]
-/
theorem mapMatrix_id : (AddMonoidHom.id α).mapMatrix = AddMonoidHom.id (Matrix m n α) :=
  rfl

@[simp]
/--
theorem `mapMatrix_comp` / 定理 `mapMatrix_comp`

English:
theorem mapMatrix_comp
  given: (f : β ->+ γ) (g : α ->+ β)
  proof: rfl

中文:
定理 mapMatrix_comp
  条件: (f : β ->+ γ) (g : α ->+ β)
  证明: rfl
-/
theorem mapMatrix_comp (f : β ->+ γ) (g : α ->+ β) :
    f.mapMatrix.comp g.mapMatrix = ((f.comp g).mapMatrix : Matrix m n α ->+ _) :=
  rfl

/--
lemma `entryAddMonoidHom_comp_mapMatrix` / 引理 `entryAddMonoidHom_comp_mapMatrix`

English:
lemma entryAddMonoidHom_comp_mapMatrix
  given: (f : α ->+ β) (i : m) (j : n)
  proof: rfl

@[simp]

中文:
引理 entryAddMonoidHom_comp_mapMatrix
  条件: (f : α ->+ β) (i : m) (j : n)
  证明: rfl

@[simp]
-/
@[simp] lemma entryAddMonoidHom_comp_mapMatrix (f : α ->+ β) (i : m) (j : n) :
    (entryAddMonoidHom β i j).comp f.mapMatrix = f.comp (entryAddMonoidHom α i j) := rfl

@[simp]
/--
theorem `mapMatrix_zero` / 定理 `mapMatrix_zero`

English:
theorem mapMatrix_zero
  statement: (0 : α ->+ β).mapMatrix = (0 : Matrix m n α ->+ _)
  proof: rfl

中文:
定理 mapMatrix_zero
  结论: (0 : α ->+ β).mapMatrix = (0 : 矩阵 m n α ->+ _)
  证明: rfl
-/
theorem mapMatrix_zero : (0 : α ->+ β).mapMatrix = (0 : Matrix m n α ->+ _) := rfl

end AddZeroClass

@[simp]
/--
theorem `mapMatrix_add` / 定理 `mapMatrix_add`

English:
theorem mapMatrix_add
  given: [AddZeroClass α] [AddCommMonoid β] (f g : α ->+ β)
  proof: rfl

@[simp]

中文:
定理 mapMatrix_add
  条件: [加法零类 α] [加法交换幺半群 β] (f g : α ->+ β)
  证明: rfl

@[simp]
-/
theorem mapMatrix_add [AddZeroClass α] [AddCommMonoid β] (f g : α ->+ β) :
    (f + g).mapMatrix = (f.mapMatrix + g.mapMatrix : Matrix m n α ->+ _) := rfl

@[simp]
/--
theorem `mapMatrix_sub` / 定理 `mapMatrix_sub`

English:
theorem mapMatrix_sub
  given: [AddZeroClass α] [AddCommGroup β] (f g : α ->+ β)
  proof: rfl

@[simp]

中文:
定理 mapMatrix_sub
  条件: [加法零类 α] [加法交换群 β] (f g : α ->+ β)
  证明: rfl

@[simp]
-/
theorem mapMatrix_sub [AddZeroClass α] [AddCommGroup β] (f g : α ->+ β) :
    (f - g).mapMatrix = (f.mapMatrix - g.mapMatrix : Matrix m n α ->+ _) := rfl

@[simp]
/--
theorem `mapMatrix_neg` / 定理 `mapMatrix_neg`

English:
theorem mapMatrix_neg
  given: [AddZeroClass α] [AddCommGroup β] (f : α ->+ β)
  proof: rfl

@[simp]

中文:
定理 mapMatrix_neg
  条件: [加法零类 α] [加法交换群 β] (f : α ->+ β)
  证明: rfl

@[simp]
-/
theorem mapMatrix_neg [AddZeroClass α] [AddCommGroup β] (f : α ->+ β) :
    (-f).mapMatrix = (-f.mapMatrix : Matrix m n α ->+ _) := rfl

@[simp]
/--
theorem `mapMatrix_smul` / 定理 `mapMatrix_smul`

English:
theorem mapMatrix_smul
  statement: [Monoid A] [AddZeroClass α] [AddMonoid β] [DistribMulAction A β]
  proof: rfl

中文:
定理 mapMatrix_smul
  结论: [幺半群 A] [加法零类 α] [加法幺半群 β] [分配乘法作用 A β]
  证明: rfl
-/
theorem mapMatrix_smul [Monoid A] [AddZeroClass α] [AddMonoid β] [DistribMulAction A β]
    (a : A) (f : α ->+ β) :
    (a • f).mapMatrix = (a • f.mapMatrix : Matrix m n α ->+ _) := rfl

end AddMonoidHom

namespace AddEquiv

variable [Add α] [Add β] [Add γ]

/-- The `AddEquiv` between spaces of matrices induced by an `AddEquiv` between their
coefficients. This is `Matrix.map` as an `AddEquiv`. -/
@[simps apply]
/--
Definition of `mapMatrix` / `mapMatrix` 的定义

English:
definition mapMatrix
  signature: (f : α ≃+ β)
  body: { f.toEquiv.mapMatrix with
    toFun := fun M => M.map f
    invFun := fun M => M.map f.symm
    map_add' := Matrix.map_add f (map_add f) }

@[simp]

中文:
定义 mapMatrix
  签名: (f : α ≃+ β)
  定义体: { f.toEquiv.mapMatrix with
    toFun := fun M => M.map f
    invFun := fun M => M.map f.symm
    map_add' := Matrix.map_add f (map_add f) }

@[simp]

Depends on / 依赖: M.map, Matrix, Matrix.map_add, f.symm, f.toEquiv.mapMatrix, invFun, mapMatrix, map_add, toEquiv
-/
def mapMatrix (f : α ≃+ β) : Matrix m n α ≃+ Matrix m n β :=
  { f.toEquiv.mapMatrix with
    toFun := fun M => M.map f
    invFun := fun M => M.map f.symm
    map_add' := Matrix.map_add f (map_add f) }

@[simp]
/--
theorem `mapMatrix_refl` / 定理 `mapMatrix_refl`

English:
theorem mapMatrix_refl
  statement: (AddEquiv.refl α).mapMatrix = AddEquiv.refl (Matrix m n α)
  proof: rfl

@[simp]

中文:
定理 mapMatrix_refl
  结论: (加法等价.refl α).mapMatrix = 加法等价.refl (矩阵 m n α)
  证明: rfl

@[simp]
-/
theorem mapMatrix_refl : (AddEquiv.refl α).mapMatrix = AddEquiv.refl (Matrix m n α) :=
  rfl

@[simp]
/--
theorem `mapMatrix_symm` / 定理 `mapMatrix_symm`

English:
theorem mapMatrix_symm
  given: (f : α ≃+ β)
  statement: f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m n β ≃+ _)
  proof: rfl

@[simp]

中文:
定理 mapMatrix_symm
  条件: (f : α ≃+ β)
  结论: f.mapMatrix.symm = (f.symm.mapMatrix : 矩阵 m n β ≃+ _)
  证明: rfl

@[simp]
-/
theorem mapMatrix_symm (f : α ≃+ β) : f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m n β ≃+ _) :=
  rfl

@[simp]
/--
theorem `mapMatrix_trans` / 定理 `mapMatrix_trans`

English:
theorem mapMatrix_trans
  given: (f : α ≃+ β) (g : β ≃+ γ)
  proof: rfl

中文:
定理 mapMatrix_trans
  条件: (f : α ≃+ β) (g : β ≃+ γ)
  证明: rfl
-/
theorem mapMatrix_trans (f : α ≃+ β) (g : β ≃+ γ) :
    f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m n α ≃+ _) :=
  rfl

/--
lemma `entryAddHom_comp_mapMatrix` / 引理 `entryAddHom_comp_mapMatrix`

English:
lemma entryAddHom_comp_mapMatrix
  given: (f : α ≃+ β) (i : m) (j : n)
  proof: rfl

中文:
引理 entryAddHom_comp_mapMatrix
  条件: (f : α ≃+ β) (i : m) (j : n)
  证明: rfl
-/
@[simp] lemma entryAddHom_comp_mapMatrix (f : α ≃+ β) (i : m) (j : n) :
    (entryAddHom β i j).comp (AddHomClass.toAddHom f.mapMatrix) =
      (f : AddHom α β).comp (entryAddHom _ i j) := rfl

end AddEquiv

namespace LinearMap

variable [Semiring R] [Semiring S] [Semiring T]
variable {σᵣₛ : R ->+* S} {σₛₜ : S ->+* T} {σᵣₜ : R ->+* T} [RingHomCompTriple σᵣₛ σₛₜ σᵣₜ]

section AddCommMonoid
variable [AddCommMonoid α] [AddCommMonoid β] [AddCommMonoid γ]
variable [Module R α] [Module S β] [Module T γ]

/-- The `LinearMap` between spaces of matrices induced by a `LinearMap` between their
coefficients. This is `Matrix.map` as a `LinearMap`. -/
@[simps]
/--
Definition of `mapMatrix` / `mapMatrix` 的定义

English:
definition mapMatrix
  signature: (f : α ->ₛₗ[σᵣₛ] β)
  body: M.map f
  map_add' := Matrix.map_add f f.map_add
  map_smul' r := Matrix.map_smulₛₗ f _ r (f.map_smulₛₗ r)

@[simp]

中文:
定义 mapMatrix
  签名: (f : α ->ₛₗ[σᵣₛ] β)
  定义体: M.map f
  map_add' := Matrix.map_add f f.map_add
  map_smul' r := Matrix.map_smulₛₗ f _ r (f.map_smulₛₗ r)

@[simp]

Depends on / 依赖: M.map
-/
def mapMatrix (f : α ->ₛₗ[σᵣₛ] β) : Matrix m n α ->ₛₗ[σᵣₛ] Matrix m n β where
  toFun M := M.map f
  map_add' := Matrix.map_add f f.map_add
  map_smul' r := Matrix.map_smulₛₗ f _ r (f.map_smulₛₗ r)

@[simp]
/--
theorem `mapMatrix_id` / 定理 `mapMatrix_id`

English:
theorem mapMatrix_id
  statement: LinearMap.id.mapMatrix = (LinearMap.id : Matrix m n α ->ₗ[R] _)
  proof: rfl

@[simp]

中文:
定理 mapMatrix_id
  结论: 线性映射.id.mapMatrix = (线性映射.id : 矩阵 m n α ->ₗ[R] _)
  证明: rfl

@[simp]
-/
theorem mapMatrix_id : LinearMap.id.mapMatrix = (LinearMap.id : Matrix m n α ->ₗ[R] _) :=
  rfl

@[simp]
/--
theorem `mapMatrix_comp` / 定理 `mapMatrix_comp`

English:
theorem mapMatrix_comp
  given: (f : β ->ₛₗ[σₛₜ] γ) (g : α ->ₛₗ[σᵣₛ] β)
  proof: rfl

中文:
定理 mapMatrix_comp
  条件: (f : β ->ₛₗ[σₛₜ] γ) (g : α ->ₛₗ[σᵣₛ] β)
  证明: rfl
-/
theorem mapMatrix_comp (f : β ->ₛₗ[σₛₜ] γ) (g : α ->ₛₗ[σᵣₛ] β) :
    f.mapMatrix.comp g.mapMatrix = ((f.comp g).mapMatrix : Matrix m n α ->ₛₗ[_] _) :=
  rfl

/--
lemma `entryLinearMap_comp_mapMatrix` / 引理 `entryLinearMap_comp_mapMatrix`

English:
lemma entryLinearMap_comp_mapMatrix
  given: (f : α ->ₛₗ[σᵣₛ] β) (i : m) (j : n)
  proof: rfl

@[simp]

中文:
引理 entryLinearMap_comp_mapMatrix
  条件: (f : α ->ₛₗ[σᵣₛ] β) (i : m) (j : n)
  证明: rfl

@[simp]
-/
@[simp] lemma entryLinearMap_comp_mapMatrix (f : α ->ₛₗ[σᵣₛ] β) (i : m) (j : n) :
    (entryLinearMap S _ i j).comp f.mapMatrix = f.comp (entryLinearMap R _ i j) := rfl

@[simp]
/--
theorem `mapMatrix_zero` / 定理 `mapMatrix_zero`

English:
theorem mapMatrix_zero
  statement: (0 : α ->ₛₗ[σᵣₛ] β).mapMatrix = (0 : Matrix m n α ->ₛₗ[_] _)
  proof: rfl

@[simp]

中文:
定理 mapMatrix_zero
  结论: (0 : α ->ₛₗ[σᵣₛ] β).mapMatrix = (0 : 矩阵 m n α ->ₛₗ[_] _)
  证明: rfl

@[simp]
-/
theorem mapMatrix_zero : (0 : α ->ₛₗ[σᵣₛ] β).mapMatrix = (0 : Matrix m n α ->ₛₗ[_] _) := rfl

@[simp]
/--
theorem `mapMatrix_add` / 定理 `mapMatrix_add`

English:
theorem mapMatrix_add
  given: (f g : α ->ₛₗ[σᵣₛ] β)
  proof: rfl

@[simp]

中文:
定理 mapMatrix_add
  条件: (f g : α ->ₛₗ[σᵣₛ] β)
  证明: rfl

@[simp]
-/
theorem mapMatrix_add (f g : α ->ₛₗ[σᵣₛ] β) :
    (f + g).mapMatrix = (f.mapMatrix + g.mapMatrix : Matrix m n α ->ₛₗ[_] _) := rfl

@[simp]
/--
theorem `mapMatrix_smul` / 定理 `mapMatrix_smul`

English:
theorem mapMatrix_smul
  statement: [Monoid A] [DistribMulAction A β] [SMulCommClass S A β]
  proof: rfl

中文:
定理 mapMatrix_smul
  结论: [幺半群 A] [分配乘法作用 A β] [标量交换类 S A β]
  证明: rfl
-/
theorem mapMatrix_smul [Monoid A] [DistribMulAction A β] [SMulCommClass S A β]
    (a : A) (f : α ->ₛₗ[σᵣₛ] β) :
    (a • f).mapMatrix = (a • f.mapMatrix : Matrix m n α ->ₛₗ[_] _) := rfl

variable (A) in
/-- `LinearMap.mapMatrix` is itself linear in the map being applied.

Alternative, this is `Matrix.map` as a bilinear map. -/
@[simps]
/--
Definition of `mapMatrixLinear` / `mapMatrixLinear` 的定义

English:
definition mapMatrixLinear
  signature: [Semiring A] [Module A β] [SMulCommClass S A β]
  body: mapMatrix
  map_add' := mapMatrix_add
  map_smul' := mapMatrix_smul

中文:
定义 mapMatrixLinear
  签名: [半环 A] [模 A β] [标量交换类 S A β]
  定义体: mapMatrix
  map_add' := mapMatrix_add
  map_smul' := mapMatrix_smul

Depends on / 依赖: mapMatrix
-/
def mapMatrixLinear [Semiring A] [Module A β] [SMulCommClass S A β] :
    (α ->ₛₗ[σᵣₛ] β) ->ₗ[A] (Matrix m n α ->ₛₗ[σᵣₛ] Matrix m n β) where
  toFun := mapMatrix
  map_add' := mapMatrix_add
  map_smul' := mapMatrix_smul

end AddCommMonoid

section
variable [AddCommMonoid α] [AddCommGroup β]
variable [Module R α] [Module S β]

@[simp]
/--
theorem `mapMatrix_sub` / 定理 `mapMatrix_sub`

English:
theorem mapMatrix_sub
  given: (f g : α ->ₛₗ[σᵣₛ] β)
  proof: rfl

@[simp]

中文:
定理 mapMatrix_sub
  条件: (f g : α ->ₛₗ[σᵣₛ] β)
  证明: rfl

@[simp]
-/
theorem mapMatrix_sub (f g : α ->ₛₗ[σᵣₛ] β) :
    (f - g).mapMatrix = (f.mapMatrix - g.mapMatrix : Matrix m n α ->ₛₗ[σᵣₛ] _) := rfl

@[simp]
/--
theorem `mapMatrix_neg` / 定理 `mapMatrix_neg`

English:
theorem mapMatrix_neg
  given: (f : α ->ₛₗ[σᵣₛ] β)
  proof: rfl

中文:
定理 mapMatrix_neg
  条件: (f : α ->ₛₗ[σᵣₛ] β)
  证明: rfl
-/
theorem mapMatrix_neg (f : α ->ₛₗ[σᵣₛ] β) :
    (-f).mapMatrix = (-f.mapMatrix : Matrix m n α ->ₛₗ[σᵣₛ] _) := rfl

end

end LinearMap

namespace LinearEquiv

variable [Semiring R] [Semiring S] [Semiring T]
variable [AddCommMonoid α] [AddCommMonoid β] [AddCommMonoid γ]
variable [Module R α] [Module S β] [Module T γ]
variable {σᵣₛ : R ->+* S} {σₛₜ : S ->+* T} {σᵣₜ : R ->+* T} [RingHomCompTriple σᵣₛ σₛₜ σᵣₜ]
variable {σₛᵣ : S ->+* R} {σₜₛ : T ->+* S} {σₜᵣ : T ->+* R} [RingHomCompTriple σₜₛ σₛᵣ σₜᵣ]
variable [RingHomInvPair σᵣₛ σₛᵣ] [RingHomInvPair σₛᵣ σᵣₛ]
variable [RingHomInvPair σₛₜ σₜₛ] [RingHomInvPair σₜₛ σₛₜ]
variable [RingHomInvPair σᵣₜ σₜᵣ] [RingHomInvPair σₜᵣ σᵣₜ]

/-- The `LinearEquiv` between spaces of matrices induced by a `LinearEquiv` between their
coefficients. This is `Matrix.map` as a `LinearEquiv`. -/
@[simps apply]
/--
Definition of `mapMatrix` / `mapMatrix` 的定义

English:
definition mapMatrix
  signature: (f : α ≃ₛₗ[σᵣₛ] β)
  body: { f.toEquiv.mapMatrix,
    f.toLinearMap.mapMatrix with
    toFun := fun M => M.map f
    invFun := fun M => M.map f.symm }

@[simp]

中文:
定义 mapMatrix
  签名: (f : α ≃ₛₗ[σᵣₛ] β)
  定义体: { f.toEquiv.mapMatrix,
    f.toLinearMap.mapMatrix with
    toFun := fun M => M.map f
    invFun := fun M => M.map f.symm }

@[simp]

Depends on / 依赖: M.map, f.symm, f.toEquiv.mapMatrix, f.toLinearMap.mapMatrix, invFun, mapMatrix, toEquiv, toLinearMap
-/
def mapMatrix (f : α ≃ₛₗ[σᵣₛ] β) : Matrix m n α ≃ₛₗ[σᵣₛ] Matrix m n β :=
  { f.toEquiv.mapMatrix,
    f.toLinearMap.mapMatrix with
    toFun := fun M => M.map f
    invFun := fun M => M.map f.symm }

@[simp]
/--
theorem `mapMatrix_refl` / 定理 `mapMatrix_refl`

English:
theorem mapMatrix_refl
  statement: (LinearEquiv.refl R α).mapMatrix = LinearEquiv.refl R (Matrix m n α)
  proof: rfl

@[simp]

中文:
定理 mapMatrix_refl
  结论: (线性等价.refl R α).mapMatrix = 线性等价.refl R (矩阵 m n α)
  证明: rfl

@[simp]
-/
theorem mapMatrix_refl : (LinearEquiv.refl R α).mapMatrix = LinearEquiv.refl R (Matrix m n α) :=
  rfl

@[simp]
/--
theorem `mapMatrix_symm` / 定理 `mapMatrix_symm`

English:
theorem mapMatrix_symm
  given: (f : α ≃ₛₗ[σᵣₛ] β)
  proof: rfl

@[simp]

中文:
定理 mapMatrix_symm
  条件: (f : α ≃ₛₗ[σᵣₛ] β)
  证明: rfl

@[simp]
-/
theorem mapMatrix_symm (f : α ≃ₛₗ[σᵣₛ] β) :
    f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m n β ≃ₛₗ[_] _) :=
  rfl

@[simp]
/--
theorem `mapMatrix_trans` / 定理 `mapMatrix_trans`

English:
theorem mapMatrix_trans
  given: (f : α ≃ₛₗ[σᵣₛ] β) (g : β ≃ₛₗ[σₛₜ] γ)
  proof: rfl

中文:
定理 mapMatrix_trans
  条件: (f : α ≃ₛₗ[σᵣₛ] β) (g : β ≃ₛₗ[σₛₜ] γ)
  证明: rfl
-/
theorem mapMatrix_trans (f : α ≃ₛₗ[σᵣₛ] β) (g : β ≃ₛₗ[σₛₜ] γ) :
    f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m n α ≃ₛₗ[_] _) :=
  rfl

/--
lemma `mapMatrix_toLinearMap` / 引理 `mapMatrix_toLinearMap`

English:
lemma mapMatrix_toLinearMap
  given: (f : α ≃ₛₗ[σᵣₛ] β)
  proof: by
  rfl

中文:
引理 mapMatrix_toLinearMap
  条件: (f : α ≃ₛₗ[σᵣₛ] β)
  证明: by
  rfl
-/
@[simp] lemma mapMatrix_toLinearMap (f : α ≃ₛₗ[σᵣₛ] β) :
    (f.mapMatrix : _ ≃ₛₗ[_] Matrix m n β).toLinearMap = f.toLinearMap.mapMatrix := by
  rfl

/--
lemma `entryLinearMap_comp_mapMatrix` / 引理 `entryLinearMap_comp_mapMatrix`

English:
lemma entryLinearMap_comp_mapMatrix
  given: (f : α ≃ₛₗ[σᵣₛ] β) (i : m) (j : n)
  proof: by
  simp only [mapMatrix_toLinearMap, LinearMap.entryLinearMap_comp_mapMatrix]

中文:
引理 entryLinearMap_comp_mapMatrix
  条件: (f : α ≃ₛₗ[σᵣₛ] β) (i : m) (j : n)
  证明: by
  simp only [mapMatrix_toLinearMap, LinearMap.entryLinearMap_comp_mapMatrix]

Depends on / 依赖: LinearMap, LinearMap.entryLinearMap_comp_mapMatrix, entryLinearMap_comp_mapMatrix, mapMatrix_toLinearMap
-/
lemma entryLinearMap_comp_mapMatrix (f : α ≃ₛₗ[σᵣₛ] β) (i : m) (j : n) :
    (entryLinearMap S _ i j).comp f.mapMatrix.toLinearMap =
      f.toLinearMap.comp (entryLinearMap R _ i j) := by
  simp only [mapMatrix_toLinearMap, LinearMap.entryLinearMap_comp_mapMatrix]

end LinearEquiv

namespace RingHom

variable [Fintype m] [DecidableEq m]
variable [NonAssocSemiring α] [NonAssocSemiring β] [NonAssocSemiring γ]

/-- The `RingHom` between spaces of square matrices induced by a `RingHom` between their
coefficients. This is `Matrix.map` as a `RingHom`. -/
@[simps]
/--
Definition of `mapMatrix` / `mapMatrix` 的定义

English:
definition mapMatrix
  signature: (f : α ->+* β)
  body: { f.toAddMonoidHom.mapMatrix with
    toFun := fun M => M.map f
    map_one' := by simp
    map_mul' := fun _ _ => Matrix.map_mul }

@[simp]

中文:
定义 mapMatrix
  签名: (f : α ->+* β)
  定义体: { f.toAddMonoidHom.mapMatrix with
    toFun := fun M => M.map f
    map_one' := by simp
    map_mul' := fun _ _ => Matrix.map_mul }

@[simp]

Depends on / 依赖: M.map, Matrix, Matrix.map_mul, f.toAddMonoidHom.mapMatrix, mapMatrix, map_mul, map_one, toAddMonoidHom
-/
def mapMatrix (f : α ->+* β) : Matrix m m α ->+* Matrix m m β :=
  { f.toAddMonoidHom.mapMatrix with
    toFun := fun M => M.map f
    map_one' := by simp
    map_mul' := fun _ _ => Matrix.map_mul }

@[simp]
/--
theorem `mapMatrix_id` / 定理 `mapMatrix_id`

English:
theorem mapMatrix_id
  statement: (RingHom.id α).mapMatrix = RingHom.id (Matrix m m α)
  proof: rfl

@[simp]

中文:
定理 mapMatrix_id
  结论: (环态射.id α).mapMatrix = 环态射.id (矩阵 m m α)
  证明: rfl

@[simp]
-/
theorem mapMatrix_id : (RingHom.id α).mapMatrix = RingHom.id (Matrix m m α) :=
  rfl

@[simp]
/--
theorem `mapMatrix_comp` / 定理 `mapMatrix_comp`

English:
theorem mapMatrix_comp
  given: (f : β ->+* γ) (g : α ->+* β)
  proof: rfl

中文:
定理 mapMatrix_comp
  条件: (f : β ->+* γ) (g : α ->+* β)
  证明: rfl
-/
theorem mapMatrix_comp (f : β ->+* γ) (g : α ->+* β) :
    f.mapMatrix.comp g.mapMatrix = ((f.comp g).mapMatrix : Matrix m m α ->+* _) :=
  rfl

/--
lemma `_root_.Matrix.map_pow` / 引理 `_root_.Matrix.map_pow`

English:
lemma _root_.Matrix.map_pow
  statement: {α β : Type*} [Semiring α] [Semiring β]
  proof: f.mapMatrix.map_pow M a

中文:
引理 _root_.矩阵.map_pow
  结论: {α β : 类型} [半环 α] [半环 β]
  证明: f.mapMatrix.map_pow M a
-/
protected lemma _root_.Matrix.map_pow {α β : Type*} [Semiring α] [Semiring β]
    (M : Matrix m m α) (f : α ->+* β) (a : Nat) : (M ^ a).map f = (M.map f) ^ a :=
  f.mapMatrix.map_pow M a

end RingHom

namespace RingEquiv

variable [Fintype m] [DecidableEq m]
variable [NonAssocSemiring α] [NonAssocSemiring β] [NonAssocSemiring γ]

/-- The `RingEquiv` between spaces of square matrices induced by a `RingEquiv` between their
coefficients. This is `Matrix.map` as a `RingEquiv`. -/
@[simps apply]
/--
Definition of `mapMatrix` / `mapMatrix` 的定义

English:
definition mapMatrix
  signature: (f : α ≃+* β)
  body: { f.toRingHom.mapMatrix,
    f.toAddEquiv.mapMatrix with
    toFun := fun M => M.map f
    invFun := fun M => M.map f.symm }

@[simp]

中文:
定义 mapMatrix
  签名: (f : α ≃+* β)
  定义体: { f.toRingHom.mapMatrix,
    f.toAddEquiv.mapMatrix with
    toFun := fun M => M.map f
    invFun := fun M => M.map f.symm }

@[simp]

Depends on / 依赖: M.map, f.symm, f.toAddEquiv.mapMatrix, f.toRingHom.mapMatrix, invFun, mapMatrix, toAddEquiv, toRingHom
-/
def mapMatrix (f : α ≃+* β) : Matrix m m α ≃+* Matrix m m β :=
  { f.toRingHom.mapMatrix,
    f.toAddEquiv.mapMatrix with
    toFun := fun M => M.map f
    invFun := fun M => M.map f.symm }

@[simp]
/--
theorem `mapMatrix_refl` / 定理 `mapMatrix_refl`

English:
theorem mapMatrix_refl
  statement: (RingEquiv.refl α).mapMatrix = RingEquiv.refl (Matrix m m α)
  proof: rfl

@[simp]

中文:
定理 mapMatrix_refl
  结论: (环等价.refl α).mapMatrix = 环等价.refl (矩阵 m m α)
  证明: rfl

@[simp]
-/
theorem mapMatrix_refl : (RingEquiv.refl α).mapMatrix = RingEquiv.refl (Matrix m m α) :=
  rfl

@[simp]
/--
theorem `mapMatrix_symm` / 定理 `mapMatrix_symm`

English:
theorem mapMatrix_symm
  given: (f : α ≃+* β)
  statement: f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m m β ≃+* _)
  proof: rfl

@[simp]

中文:
定理 mapMatrix_symm
  条件: (f : α ≃+* β)
  结论: f.mapMatrix.symm = (f.symm.mapMatrix : 矩阵 m m β ≃+* _)
  证明: rfl

@[simp]
-/
theorem mapMatrix_symm (f : α ≃+* β) : f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m m β ≃+* _) :=
  rfl

@[simp]
/--
theorem `mapMatrix_trans` / 定理 `mapMatrix_trans`

English:
theorem mapMatrix_trans
  given: (f : α ≃+* β) (g : β ≃+* γ)
  proof: rfl

中文:
定理 mapMatrix_trans
  条件: (f : α ≃+* β) (g : β ≃+* γ)
  证明: rfl
-/
theorem mapMatrix_trans (f : α ≃+* β) (g : β ≃+* γ) :
    f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m m α ≃+* _) :=
  rfl

open MulOpposite in
/-- For any ring `α`, we have ring isomorphism `Matₙₓₙ(αᵒᵖ) ≅ (Matₙₓₙ(α))ᵒᵖ` given by transpose.

See also `Matrix.transposeRingEquiv` for a version that doesn't take the opposite of `α`,
given that its multiplication is commutative. -/
@[simps apply symm_apply]
/--
Definition of `mopMatrix` / `mopMatrix` 的定义

English:
definition mopMatrix
  signature: {α} [Mul α] [AddCommMonoid α]
  body: op (M.transpose.map unop)
  invFun M := M.unop.transpose.map op
map_mul' _ _ := unop_injective by ext; simp [mul_apply]
  map_add' _ _ := rfl

中文:
定义 mopMatrix
  签名: {α} [乘法 α] [加法交换幺半群 α]
  定义体: op (M.transpose.map unop)
  invFun M := M.unop.transpose.map op
map_mul' _ _ := unop_injective by ext; simp [mul_apply]
  map_add' _ _ := rfl

Depends on / 依赖: M.transpose.map, transpose
-/
def mopMatrix {α} [Mul α] [AddCommMonoid α] : Matrix m m αᵐᵒᵖ ≃+* (Matrix m m α)ᵐᵒᵖ where
  toFun M := op (M.transpose.map unop)
  invFun M := M.unop.transpose.map op
map_mul' _ _ := unop_injective by ext; simp [mul_apply]
  map_add' _ _ := rfl

end RingEquiv

set_option backward.isDefEq.respectTransparency false in
instance (α) [MulOne α] [AddCommMonoid α] [IsStablyFiniteRing α] : IsStablyFiniteRing αᵐᵒᵖ where
  isDedekindFiniteMonoid n := .of_injective (MonoidHom.mk
    ⟨RingEquiv.mopMatrix, by simp⟩ RingEquiv.mopMatrix.map_mul) (RingEquiv.injective _)

open MulOpposite in
/--
theorem `MulOpposite.isStablyFiniteRing_iff` / 定理 `MulOpposite.isStablyFiniteRing_iff`

English:
theorem MulOpposite.isStablyFiniteRing_iff
  given: (α) [MulOne α] [AddCommMonoid α]
  proof: ⟨fun n => let f := MonoidHom.mk ⟨fun M : Matrix (Fin n) (Fin n) α => M.map (op ∘ op), by aesop⟩
               fun _ _ => by ext; simp [mul_apply]
  .of_injective f (map_injective (op_injective.comp op_injective))⟩
  mpr _ := inferInstance

中文:
定理 MulOpposite.isStablyFiniteRing_iff
  条件: (α) [MulOne α] [加法交换幺半群 α]
  证明: ⟨fun n => let f := MonoidHom.mk ⟨fun M : Matrix (Fin n) (Fin n) α => M.map (op ∘ op), by aesop⟩
               fun _ _ => by ext; simp [mul_apply]
  .of_injective f (map_injective (op_injective.comp op_injective))⟩
  mpr _ := inferInstance

Depends on / 依赖: M.map, Matrix, MonoidHom, MonoidHom.mk, map_injective, mul_apply, of_injective, op_injective, op_injective.comp
-/
theorem MulOpposite.isStablyFiniteRing_iff (α) [MulOne α] [AddCommMonoid α] :
    IsStablyFiniteRing αᵐᵒᵖ ↔ IsStablyFiniteRing α where
  mp _ :=
  ⟨fun n => let f := MonoidHom.mk ⟨fun M : Matrix (Fin n) (Fin n) α => M.map (op ∘ op), by aesop⟩
               fun _ _ => by ext; simp [mul_apply]
  .of_injective f (map_injective (op_injective.comp op_injective))⟩
  mpr _ := inferInstance

namespace AlgHom

variable [Fintype m] [DecidableEq m]
variable [CommSemiring R] [Semiring α] [Semiring β] [Semiring γ]
variable [Algebra R α] [Algebra R β] [Algebra R γ]

/-- The `AlgHom` between spaces of square matrices induced by an `AlgHom` between their
coefficients. This is `Matrix.map` as an `AlgHom`. -/
@[simps]
/--
Definition of `mapMatrix` / `mapMatrix` 的定义

English:
definition mapMatrix
  signature: (f : α ->ₐ[R] β)
  body: { f.toRingHom.mapMatrix with
    toFun := fun M => M.map f
    commutes' := fun r => Matrix.map_algebraMap r f (map_zero _) (f.commutes r) }

@[simp]

中文:
定义 mapMatrix
  签名: (f : α ->ₐ[R] β)
  定义体: { f.toRingHom.mapMatrix with
    toFun := fun M => M.map f
    commutes' := fun r => Matrix.map_algebraMap r f (map_zero _) (f.commutes r) }

@[simp]

Depends on / 依赖: M.map, Matrix, Matrix.map_algebraMap, commutes, f.commutes, f.toRingHom.mapMatrix, mapMatrix, map_algebraMap, map_zero, toRingHom
-/
def mapMatrix (f : α ->ₐ[R] β) : Matrix m m α ->ₐ[R] Matrix m m β :=
  { f.toRingHom.mapMatrix with
    toFun := fun M => M.map f
    commutes' := fun r => Matrix.map_algebraMap r f (map_zero _) (f.commutes r) }

@[simp]
/--
theorem `mapMatrix_id` / 定理 `mapMatrix_id`

English:
theorem mapMatrix_id
  statement: (AlgHom.id R α).mapMatrix = AlgHom.id R (Matrix m m α)
  proof: rfl

@[simp]

中文:
定理 mapMatrix_id
  结论: (代数态射.id R α).mapMatrix = 代数态射.id R (矩阵 m m α)
  证明: rfl

@[simp]
-/
theorem mapMatrix_id : (AlgHom.id R α).mapMatrix = AlgHom.id R (Matrix m m α) :=
  rfl

@[simp]
/--
theorem `mapMatrix_comp` / 定理 `mapMatrix_comp`

English:
theorem mapMatrix_comp
  given: (f : β ->ₐ[R] γ) (g : α ->ₐ[R] β)
  proof: rfl

中文:
定理 mapMatrix_comp
  条件: (f : β ->ₐ[R] γ) (g : α ->ₐ[R] β)
  证明: rfl
-/
theorem mapMatrix_comp (f : β ->ₐ[R] γ) (g : α ->ₐ[R] β) :
    f.mapMatrix.comp g.mapMatrix = ((f.comp g).mapMatrix : Matrix m m α ->ₐ[R] _) :=
  rfl

end AlgHom

namespace AlgEquiv

variable [Fintype m] [DecidableEq m]
variable [CommSemiring R] [Semiring α] [Semiring β] [Semiring γ]
variable [Algebra R α] [Algebra R β] [Algebra R γ]

/-- The `AlgEquiv` between spaces of square matrices induced by an `AlgEquiv` between their
coefficients. This is `Matrix.map` as an `AlgEquiv`. -/
@[simps apply]
/--
Definition of `mapMatrix` / `mapMatrix` 的定义

English:
definition mapMatrix
  signature: (f : α ≃ₐ[R] β)
  body: { f.toAlgHom.mapMatrix,
    f.toRingEquiv.mapMatrix with
    toFun := fun M => M.map f
    invFun := fun M => M.map f.symm }

@[simp]

中文:
定义 mapMatrix
  签名: (f : α ≃ₐ[R] β)
  定义体: { f.toAlgHom.mapMatrix,
    f.toRingEquiv.mapMatrix with
    toFun := fun M => M.map f
    invFun := fun M => M.map f.symm }

@[simp]

Depends on / 依赖: M.map, f.symm, f.toAlgHom.mapMatrix, f.toRingEquiv.mapMatrix, invFun, mapMatrix, toAlgHom, toRingEquiv
-/
def mapMatrix (f : α ≃ₐ[R] β) : Matrix m m α ≃ₐ[R] Matrix m m β :=
  { f.toAlgHom.mapMatrix,
    f.toRingEquiv.mapMatrix with
    toFun := fun M => M.map f
    invFun := fun M => M.map f.symm }

@[simp]
/--
theorem `mapMatrix_refl` / 定理 `mapMatrix_refl`

English:
theorem mapMatrix_refl
  statement: AlgEquiv.refl.mapMatrix = (AlgEquiv.refl : Matrix m m α ≃ₐ[R] _)
  proof: rfl

@[simp]

中文:
定理 mapMatrix_refl
  结论: 代数等价.refl.mapMatrix = (代数等价.refl : 矩阵 m m α ≃ₐ[R] _)
  证明: rfl

@[simp]
-/
theorem mapMatrix_refl : AlgEquiv.refl.mapMatrix = (AlgEquiv.refl : Matrix m m α ≃ₐ[R] _) :=
  rfl

@[simp]
/--
theorem `mapMatrix_symm` / 定理 `mapMatrix_symm`

English:
theorem mapMatrix_symm
  given: (f : α ≃ₐ[R] β)
  proof: rfl

@[simp]

中文:
定理 mapMatrix_symm
  条件: (f : α ≃ₐ[R] β)
  证明: rfl

@[simp]
-/
theorem mapMatrix_symm (f : α ≃ₐ[R] β) :
    f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m m β ≃ₐ[R] _) :=
  rfl

@[simp]
/--
theorem `mapMatrix_trans` / 定理 `mapMatrix_trans`

English:
theorem mapMatrix_trans
  given: (f : α ≃ₐ[R] β) (g : β ≃ₐ[R] γ)
  proof: rfl

中文:
定理 mapMatrix_trans
  条件: (f : α ≃ₐ[R] β) (g : β ≃ₐ[R] γ)
  证明: rfl
-/
theorem mapMatrix_trans (f : α ≃ₐ[R] β) (g : β ≃ₐ[R] γ) :
    f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m m α ≃ₐ[R] _) :=
  rfl

/--
Definition of `mopMatrix` / `mopMatrix` 的定义

English:
definition mopMatrix
  signature: : Matrix m m αᵐᵒᵖ ≃ₐ[R] (Matrix m m α)ᵐᵒᵖ where
  body: RingEquiv.mopMatrix
commutes' _ := MulOpposite.unop_injective by
    ext; simp [algebraMap_matrix_apply, eq_comm, apply_ite MulOpposite.unop]

中文:
定义 mopMatrix
  签名: : 矩阵 m m αᵐᵒᵖ ≃ₐ[R] (矩阵 m m α)ᵐᵒᵖ where
  定义体: RingEquiv.mopMatrix
commutes' _ := MulOpposite.unop_injective by
    ext; simp [algebraMap_matrix_apply, eq_comm, apply_ite MulOpposite.unop]
-/
@[simps!] def mopMatrix : Matrix m m αᵐᵒᵖ ≃ₐ[R] (Matrix m m α)ᵐᵒᵖ where
  __ := RingEquiv.mopMatrix
commutes' _ := MulOpposite.unop_injective by
    ext; simp [algebraMap_matrix_apply, eq_comm, apply_ite MulOpposite.unop]

end AlgEquiv

namespace AddSubmonoid

variable {A : Type*} [AddMonoid A]

/-- A version of `Set.matrix` for `AddSubmonoid`s.
Given an `AddSubmonoid` `S`, `S.matrix` is the `AddSubmonoid` of matrices `m`
all of whose entries `m i j` belong to `S`. -/
@[simps]
/--
Definition of `matrix` / `matrix` 的定义

English:
definition matrix
  signature: (S : AddSubmonoid A)
  body: Set.matrix S
  add_mem' hm hn i j := add_mem (hm i j) (hn i j)
  zero_mem' _ _ := zero_mem _

中文:
定义 matrix
  签名: (S : 加法子幺半群 A)
  定义体: Set.matrix S
  add_mem' hm hn i j := add_mem (hm i j) (hn i j)
  zero_mem' _ _ := zero_mem _

Depends on / 依赖: Set.matrix, matrix
-/
def matrix (S : AddSubmonoid A) : AddSubmonoid (Matrix m n A) where
  carrier := Set.matrix S
  add_mem' hm hn i j := add_mem (hm i j) (hn i j)
  zero_mem' _ _ := zero_mem _

end AddSubmonoid

namespace AddSubgroup

variable {A : Type*} [AddGroup A]

/-- A version of `Set.matrix` for `AddSubgroup`s.
Given an `AddSubgroup` `S`, `S.matrix` is the `AddSubgroup` of matrices `m`
all of whose entries `m i j` belong to `S`. -/
@[simps!]
/--
Definition of `matrix` / `matrix` 的定义

English:
definition matrix
  signature: (S : AddSubgroup A)
  body: S.toAddSubmonoid.matrix
  neg_mem' hm i j := AddSubgroup.neg_mem _ (hm i j)

中文:
定义 matrix
  签名: (S : 加法子群 A)
  定义体: S.toAddSubmonoid.matrix
  neg_mem' hm i j := AddSubgroup.neg_mem _ (hm i j)

Depends on / 依赖: S.toAddSubmonoid.matrix, matrix, toAddSubmonoid
-/
def matrix (S : AddSubgroup A) : AddSubgroup (Matrix m n A) where
  __ := S.toAddSubmonoid.matrix
  neg_mem' hm i j := AddSubgroup.neg_mem _ (hm i j)

end AddSubgroup

namespace Subsemiring

variable {R : Type*} [NonAssocSemiring R]
variable [Fintype n] [DecidableEq n]

/-- A version of `Set.matrix` for `Subsemiring`s.
Given a `Subsemiring` `S`, `S.matrix` is the `Subsemiring` of square matrices `m`
all of whose entries `m i j` belong to `S`. -/
@[simps!]
/--
Definition of `matrix` / `matrix` 的定义

English:
definition matrix
  signature: (S : Subsemiring R)
  body: S.toAddSubmonoid.matrix
  mul_mem' ha hb i j := Subsemiring.sum_mem _ (fun k _ => Subsemiring.mul_mem _ (ha i k) (hb k j))
  one_mem' := (diagonal_mem_matrix_iff (Subsemiring.zero_mem _)).mpr fun _ => Subsemiring.one_mem _

中文:
定义 matrix
  签名: (S : 子半环 R)
  定义体: S.toAddSubmonoid.matrix
  mul_mem' ha hb i j := Subsemiring.sum_mem _ (fun k _ => Subsemiring.mul_mem _ (ha i k) (hb k j))
  one_mem' := (diagonal_mem_matrix_iff (Subsemiring.zero_mem _)).mpr fun _ => Subsemiring.one_mem _

Depends on / 依赖: S.toAddSubmonoid.matrix, matrix, toAddSubmonoid
-/
def matrix (S : Subsemiring R) : Subsemiring (Matrix n n R) where
  __ := S.toAddSubmonoid.matrix
  mul_mem' ha hb i j := Subsemiring.sum_mem _ (fun k _ => Subsemiring.mul_mem _ (ha i k) (hb k j))
  one_mem' := (diagonal_mem_matrix_iff (Subsemiring.zero_mem _)).mpr fun _ => Subsemiring.one_mem _

end Subsemiring

namespace Subring

variable {R : Type*} [NonAssocRing R]
variable [Fintype n] [DecidableEq n]

/-- A version of `Set.matrix` for `Subring`s.
Given a `Subring` `S`, `S.matrix` is the `Subring` of square matrices `m`
all of whose entries `m i j` belong to `S`. -/
@[simps!]
/--
Definition of `matrix` / `matrix` 的定义

English:
definition matrix
  signature: (S : Subring R)
  body: S.toSubsemiring.matrix
  neg_mem' hm i j := Subring.neg_mem _ (hm i j)

中文:
定义 matrix
  签名: (S : 子环 R)
  定义体: S.toSubsemiring.matrix
  neg_mem' hm i j := Subring.neg_mem _ (hm i j)

Depends on / 依赖: S.toSubsemiring.matrix, matrix, toSubsemiring
-/
def matrix (S : Subring R) : Subring (Matrix n n R) where
  __ := S.toSubsemiring.matrix
  neg_mem' hm i j := Subring.neg_mem _ (hm i j)

end Subring

namespace Submodule

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- A version of `Set.matrix` for `Submodule`s.
Given a `Submodule` `S`, `S.matrix` is the `Submodule` of matrices `m`
all of whose entries `m i j` belong to `S`. -/
@[simps!]
/--
Definition of `matrix` / `matrix` 的定义

English:
definition matrix
  signature: (S : Submodule R M)
  body: S.toAddSubmonoid.matrix
  smul_mem' _ _ hm i j := Submodule.smul_mem _ _ (hm i j)

中文:
定义 matrix
  签名: (S : 子模 R M)
  定义体: S.toAddSubmonoid.matrix
  smul_mem' _ _ hm i j := Submodule.smul_mem _ _ (hm i j)

Depends on / 依赖: S.toAddSubmonoid.matrix, matrix, toAddSubmonoid
-/
def matrix (S : Submodule R M) : Submodule R (Matrix m n M) where
  __ := S.toAddSubmonoid.matrix
  smul_mem' _ _ hm i j := Submodule.smul_mem _ _ (hm i j)

end Submodule

open Matrix

namespace Matrix

section Pi

variable {ι : Type*} {β : ι -> Type*}

/--
Definition of `piEquiv` / `piEquiv` 的定义

English:
definition piEquiv
  signature: : Matrix m n (Π i, β i) ≃ Π i, Matrix m n (β i) where
  body: f.map (· i)
  invFun f := .of fun j k i => f i j k
  left_inv _ := rfl
  right_inv _ := rfl

中文:
定义 piEquiv
  签名: : 矩阵 m n (Π i, β i) ≃ Π i, 矩阵 m n (β i) where
  定义体: f.map (· i)
  invFun f := .of fun j k i => f i j k
  left_inv _ := rfl
  right_inv _ := rfl
-/
@[simps] def piEquiv : Matrix m n (Π i, β i) ≃ Π i, Matrix m n (β i) where
  toFun f i := f.map (· i)
  invFun f := .of fun j k i => f i j k
  left_inv _ := rfl
  right_inv _ := rfl

/--
Definition of `piAddEquiv` / `piAddEquiv` 的定义

English:
definition piAddEquiv
  signature: [forall i, Add (β i)]
  body: piEquiv
  map_add' _ _ := rfl

中文:
定义 piAddEquiv
  签名: [对任意 i, 加法 (β i)]
  定义体: piEquiv
  map_add' _ _ := rfl
-/
@[simps!] def piAddEquiv [forall i, Add (β i)] : Matrix m n (Π i, β i) ≃+ Π i, Matrix m n (β i) where
  __ := piEquiv
  map_add' _ _ := rfl

/--
Definition of `piLinearEquiv` / `piLinearEquiv` 的定义

English:
definition piLinearEquiv
  signature: (R) [Semiring R] [forall i, AddCommMonoid (β i)] [forall i, Module R (β i)]
  body: piAddEquiv
  map_smul' _ _ := rfl

中文:
定义 piLinearEquiv
  签名: (R) [半环 R] [对任意 i, 加法交换幺半群 (β i)] [对任意 i, 模 R (β i)]
  定义体: piAddEquiv
  map_smul' _ _ := rfl
-/
@[simps] def piLinearEquiv (R) [Semiring R] [forall i, AddCommMonoid (β i)] [forall i, Module R (β i)] :
    Matrix m n (Π i, β i) ≃ₗ[R] Π i, Matrix m n (β i) where
  __ := piAddEquiv
  map_smul' _ _ := rfl

/--
Definition of `piRingEquiv` / `piRingEquiv` 的定义

English:
definition piRingEquiv
  signature: [forall i, AddCommMonoid (β i)] [forall i, Mul (β i)] [Fintype n]
  body: piAddEquiv
  map_mul' _ _ := by ext; simp [Matrix.mul_apply]

中文:
定义 piRingEquiv
  签名: [对任意 i, 加法交换幺半群 (β i)] [对任意 i, 乘法 (β i)] [有限类型 n]
  定义体: piAddEquiv
  map_mul' _ _ := by ext; simp [Matrix.mul_apply]
-/
@[simps!] def piRingEquiv [forall i, AddCommMonoid (β i)] [forall i, Mul (β i)] [Fintype n] :
    Matrix n n (Π i, β i) ≃+* Π i, Matrix n n (β i) where
  __ := piAddEquiv
  map_mul' _ _ := by ext; simp [Matrix.mul_apply]

/--
Definition of `piAlgEquiv` / `piAlgEquiv` 的定义

English:
definition piAlgEquiv
  signature: (R) [CommSemiring R] [forall i, Semiring (β i)] [forall i, Algebra R (β i)]
  body: piRingEquiv
  commutes' := (AlgHom.mk' (piRingEquiv (β := β) (n := n)).toRingHom fun _ _ => rfl).commutes

中文:
定义 piAlgEquiv
  签名: (R) [交换半环 R] [对任意 i, 半环 (β i)] [对任意 i, 代数 R (β i)]
  定义体: piRingEquiv
  commutes' := (AlgHom.mk' (piRingEquiv (β := β) (n := n)).toRingHom fun _ _ => rfl).commutes
-/
@[simps!] def piAlgEquiv (R) [CommSemiring R] [forall i, Semiring (β i)] [forall i, Algebra R (β i)]
    [Fintype n] [DecidableEq n] : Matrix n n (Π i, β i) ≃ₐ[R] Π i, Matrix n n (β i) where
  __ := piRingEquiv
  commutes' := (AlgHom.mk' (piRingEquiv (β := β) (n := n)).toRingHom fun _ _ => rfl).commutes

end Pi

section Transpose

open Matrix

variable (m n α)

/-- `Matrix.transpose` as an `AddEquiv` -/
@[simps apply]
/--
Definition of `transposeAddEquiv` / `transposeAddEquiv` 的定义

English:
definition transposeAddEquiv
  signature: [Add α]
  body: transpose
  invFun := transpose
  left_inv := transpose_transpose
  right_inv := transpose_transpose
  map_add' := transpose_add

@[simp]

中文:
定义 transposeAddEquiv
  签名: [加法 α]
  定义体: transpose
  invFun := transpose
  left_inv := transpose_transpose
  right_inv := transpose_transpose
  map_add' := transpose_add

@[simp]

Depends on / 依赖: transpose
-/
def transposeAddEquiv [Add α] : Matrix m n α ≃+ Matrix n m α where
  toFun := transpose
  invFun := transpose
  left_inv := transpose_transpose
  right_inv := transpose_transpose
  map_add' := transpose_add

@[simp]
/--
theorem `transposeAddEquiv_symm` / 定理 `transposeAddEquiv_symm`

English:
theorem transposeAddEquiv_symm
  given: [Add α]
  statement: (transposeAddEquiv m n α).symm = transposeAddEquiv n m α
  proof: rfl

中文:
定理 transposeAddEquiv_symm
  条件: [加法 α]
  结论: (transposeAddEquiv m n α).symm = transposeAddEquiv n m α
  证明: rfl
-/
theorem transposeAddEquiv_symm [Add α] : (transposeAddEquiv m n α).symm = transposeAddEquiv n m α :=
  rfl

variable {m n α}

/--
theorem `transpose_list_sum` / 定理 `transpose_list_sum`

English:
theorem transpose_list_sum
  given: [AddMonoid α] (l : List (Matrix m n α))
  proof: map_list_sum (transposeAddEquiv m n α) l

中文:
定理 transpose_list_sum
  条件: [加法幺半群 α] (l : 列表 (矩阵 m n α))
  证明: map_list_sum (transposeAddEquiv m n α) l

Depends on / 依赖: map_list_sum, transposeAddEquiv
-/
theorem transpose_list_sum [AddMonoid α] (l : List (Matrix m n α)) :
    l.sumᵀ = (l.map transpose).sum :=
  map_list_sum (transposeAddEquiv m n α) l

/--
theorem `transpose_multiset_sum` / 定理 `transpose_multiset_sum`

English:
theorem transpose_multiset_sum
  given: [AddCommMonoid α] (s : Multiset (Matrix m n α))
  proof: (transposeAddEquiv m n α).toAddMonoidHom.map_multiset_sum s

中文:
定理 transpose_multiset_sum
  条件: [加法交换幺半群 α] (s : Multiset (矩阵 m n α))
  证明: (transposeAddEquiv m n α).toAddMonoidHom.map_multiset_sum s

Depends on / 依赖: map_multiset_sum, toAddMonoidHom, toAddMonoidHom.map_multiset_sum, transposeAddEquiv
-/
theorem transpose_multiset_sum [AddCommMonoid α] (s : Multiset (Matrix m n α)) :
    s.sumᵀ = (s.map transpose).sum :=
  (transposeAddEquiv m n α).toAddMonoidHom.map_multiset_sum s

/--
theorem `transpose_sum` / 定理 `transpose_sum`

English:
theorem transpose_sum
  given: [AddCommMonoid α] {ι : Type*} (s : Finset ι) (M : ι -> Matrix m n α)
  proof: map_sum (transposeAddEquiv m n α) _ s

中文:
定理 transpose_sum
  条件: [加法交换幺半群 α] {ι : 类型} (s : 有限集 ι) (M : ι -> 矩阵 m n α)
  证明: map_sum (transposeAddEquiv m n α) _ s

Depends on / 依赖: map_sum, transposeAddEquiv
-/
theorem transpose_sum [AddCommMonoid α] {ι : Type*} (s : Finset ι) (M : ι -> Matrix m n α) :
    (∑ i in s, M i)ᵀ = ∑ i in s, (M i)ᵀ :=
  map_sum (transposeAddEquiv m n α) _ s

variable (m n R α)

/-- `Matrix.transpose` as a `LinearMap` -/
@[simps apply]
/--
Definition of `transposeLinearEquiv` / `transposeLinearEquiv` 的定义

English:
definition transposeLinearEquiv
  signature: [Semiring R] [AddCommMonoid α] [Module R α]
  body: transposeAddEquiv m n α
  map_smul' := transpose_smul

@[simp]

中文:
定义 transposeLinearEquiv
  签名: [半环 R] [加法交换幺半群 α] [模 R α]
  定义体: transposeAddEquiv m n α
  map_smul' := transpose_smul

@[simp]

Depends on / 依赖: transposeAddEquiv
-/
def transposeLinearEquiv [Semiring R] [AddCommMonoid α] [Module R α] :
    Matrix m n α ≃ₗ[R] Matrix n m α where
  __ := transposeAddEquiv m n α
  map_smul' := transpose_smul

@[simp]
/--
theorem `transposeLinearEquiv_symm` / 定理 `transposeLinearEquiv_symm`

English:
theorem transposeLinearEquiv_symm
  given: [Semiring R] [AddCommMonoid α] [Module R α]
  proof: rfl

中文:
定理 transposeLinearEquiv_symm
  条件: [半环 R] [加法交换幺半群 α] [模 R α]
  证明: rfl
-/
theorem transposeLinearEquiv_symm [Semiring R] [AddCommMonoid α] [Module R α] :
    (transposeLinearEquiv m n R α).symm = transposeLinearEquiv n m R α :=
  rfl

variable {m n R α}
variable (m α)

/-- `Matrix.transpose` as a `RingEquiv` to the opposite ring.

See also `RingEquiv.mopMatrix` for a version that doesn't require `α` to have commutative
multiplication, by taking its opposite. -/
@[simps!]
/--
Definition of `transposeRingEquiv` / `transposeRingEquiv` 的定义

English:
definition transposeRingEquiv
  signature: [AddCommMonoid α] [CommMagma α] [Fintype m]
  body: transposeAddEquiv m m α
map_mul' M N := (congrArg MulOpposite.op <| transpose_mul M N).trans MulOpposite.op_mul ..

中文:
定义 transposeRingEquiv
  签名: [加法交换幺半群 α] [交换原群 α] [有限类型 m]
  定义体: transposeAddEquiv m m α
map_mul' M N := (congrArg MulOpposite.op <| transpose_mul M N).trans MulOpposite.op_mul ..

Depends on / 依赖: transposeAddEquiv
-/
def transposeRingEquiv [AddCommMonoid α] [CommMagma α] [Fintype m] :
    Matrix m m α ≃+* (Matrix m m α)ᵐᵒᵖ where
.trans MulOpposite.opAddEquiv __ := transposeAddEquiv m m α
map_mul' M N := (congrArg MulOpposite.op <| transpose_mul M N).trans MulOpposite.op_mul ..

variable {m α}

@[simp]
/--
theorem `transpose_pow` / 定理 `transpose_pow`

English:
theorem transpose_pow
  given: [CommSemiring α] [Fintype m] [DecidableEq m] (M : Matrix m m α) (k : Nat)
  proof: MulOpposite.op_injective map_pow (transposeRingEquiv m α) M k

中文:
定理 transpose_pow
  条件: [交换半环 α] [有限类型 m] [DecidableEq m] (M : 矩阵 m m α) (k : 自然数)
  证明: MulOpposite.op_injective map_pow (transposeRingEquiv m α) M k

Depends on / 依赖: MulOpposite, MulOpposite.op_injective, map_pow, op_injective, transposeRingEquiv
-/
theorem transpose_pow [CommSemiring α] [Fintype m] [DecidableEq m] (M : Matrix m m α) (k : Nat) :
    (M ^ k)ᵀ = Mᵀ ^ k :=
MulOpposite.op_injective map_pow (transposeRingEquiv m α) M k

/--
theorem `transpose_list_prod` / 定理 `transpose_list_prod`

English:
theorem transpose_list_prod
  given: [CommSemiring α] [Fintype m] [DecidableEq m] (l : List (Matrix m m α))
  proof: (transposeRingEquiv m α).unop_map_list_prod l

中文:
定理 transpose_list_prod
  条件: [交换半环 α] [有限类型 m] [DecidableEq m] (l : 列表 (矩阵 m m α))
  证明: (transposeRingEquiv m α).unop_map_list_prod l

Depends on / 依赖: transposeRingEquiv, unop_map_list_prod
-/
theorem transpose_list_prod [CommSemiring α] [Fintype m] [DecidableEq m] (l : List (Matrix m m α)) :
    l.prodᵀ = (l.map transpose).reverse.prod :=
  (transposeRingEquiv m α).unop_map_list_prod l

variable (R m α)

/-- `Matrix.transpose` as an `AlgEquiv` to the opposite ring.

See also `AlgEquiv.mopMatrix` for a version that doesn't require `α` to have commutative
multiplication, by taking its opposite. -/
@[simps!]
/--
Definition of `transposeAlgEquiv` / `transposeAlgEquiv` 的定义

English:
definition transposeAlgEquiv
  signature: [CommSemiring R] [CommSemiring α] [Fintype m] [DecidableEq m] [Algebra R α]
  body: transposeRingEquiv m α
  commutes' r := by simp [algebraMap_eq_diagonal]

中文:
定义 transposeAlgEquiv
  签名: [交换半环 R] [交换半环 α] [有限类型 m] [DecidableEq m] [代数 R α]
  定义体: transposeRingEquiv m α
  commutes' r := by simp [algebraMap_eq_diagonal]

Depends on / 依赖: transposeRingEquiv
-/
def transposeAlgEquiv [CommSemiring R] [CommSemiring α] [Fintype m] [DecidableEq m] [Algebra R α] :
    Matrix m m α ≃ₐ[R] (Matrix m m α)ᵐᵒᵖ where
  __ := transposeRingEquiv m α
  commutes' r := by simp [algebraMap_eq_diagonal]

end Transpose

section NonUnitalNonAssocSemiring
variable {ι : Type*} [NonUnitalNonAssocSemiring α] [Fintype n]

/--
theorem `sum_mulVec` / 定理 `sum_mulVec`

English:
theorem sum_mulVec
  given: (s : Finset ι) (x : ι -> Matrix m n α) (y : n -> α)
  proof: by
  ext
  simp only [mulVec, dotProduct, sum_apply, Finset.sum_mul, Finset.sum_apply]
  rw [Finset.sum_comm]

中文:
定理 sum_mulVec
  条件: (s : 有限集 ι) (x : ι -> 矩阵 m n α) (y : n -> α)
  证明: by
  ext
  simp only [mulVec, dotProduct, sum_apply, Finset.sum_mul, Finset.sum_apply]
  rw [Finset.sum_comm]

Depends on / 依赖: Finset, Finset.sum_apply, Finset.sum_comm, Finset.sum_mul, dotProduct, mulVec, sum_apply, sum_comm, sum_mul
-/
theorem sum_mulVec (s : Finset ι) (x : ι -> Matrix m n α) (y : n -> α) :
    (∑ i in s, x i) *ᵥ y = ∑ i in s, x i *ᵥ y := by
  ext
  simp only [mulVec, dotProduct, sum_apply, Finset.sum_mul, Finset.sum_apply]
  rw [Finset.sum_comm]

/--
theorem `mulVec_sum` / 定理 `mulVec_sum`

English:
theorem mulVec_sum
  given: (x : Matrix m n α) (s : Finset ι) (y : ι -> (n -> α))
  proof: by
  ext
  simp only [mulVec, dotProduct_sum, Finset.sum_apply]

中文:
定理 mulVec_sum
  条件: (x : 矩阵 m n α) (s : 有限集 ι) (y : ι -> (n -> α))
  证明: by
  ext
  simp only [mulVec, dotProduct_sum, Finset.sum_apply]

Depends on / 依赖: Finset, Finset.sum_apply, dotProduct_sum, mulVec, sum_apply
-/
theorem mulVec_sum (x : Matrix m n α) (s : Finset ι) (y : ι -> (n -> α)) :
    x *ᵥ ∑ i in s, y i = ∑ i in s, x *ᵥ y i := by
  ext
  simp only [mulVec, dotProduct_sum, Finset.sum_apply]

/--
theorem `sum_vecMul` / 定理 `sum_vecMul`

English:
theorem sum_vecMul
  given: (s : Finset ι) (x : ι -> (n -> α)) (y : Matrix n m α)
  proof: by
  ext
  simp only [vecMul, sum_dotProduct, Finset.sum_apply]

中文:
定理 sum_vecMul
  条件: (s : 有限集 ι) (x : ι -> (n -> α)) (y : 矩阵 n m α)
  证明: by
  ext
  simp only [vecMul, sum_dotProduct, Finset.sum_apply]

Depends on / 依赖: Finset, Finset.sum_apply, sum_apply, sum_dotProduct, vecMul
-/
theorem sum_vecMul (s : Finset ι) (x : ι -> (n -> α)) (y : Matrix n m α) :
    (∑ i in s, x i) ᵥ* y = ∑ i in s, x i ᵥ* y := by
  ext
  simp only [vecMul, sum_dotProduct, Finset.sum_apply]

/--
theorem `vecMul_sum` / 定理 `vecMul_sum`

English:
theorem vecMul_sum
  given: (x : n -> α) (s : Finset ι) (y : ι -> Matrix n m α)
  proof: by
  ext
  simp only [vecMul, dotProduct, sum_apply, Finset.mul_sum, Finset.sum_apply]
  rw [Finset.sum_comm]

中文:
定理 vecMul_sum
  条件: (x : n -> α) (s : 有限集 ι) (y : ι -> 矩阵 n m α)
  证明: by
  ext
  simp only [vecMul, dotProduct, sum_apply, Finset.mul_sum, Finset.sum_apply]
  rw [Finset.sum_comm]

Depends on / 依赖: Finset, Finset.mul_sum, Finset.sum_apply, Finset.sum_comm, dotProduct, mul_sum, sum_apply, sum_comm, vecMul
-/
theorem vecMul_sum (x : n -> α) (s : Finset ι) (y : ι -> Matrix n m α) :
    x ᵥ* (∑ i in s, y i) = ∑ i in s, x ᵥ* y i := by
  ext
  simp only [vecMul, dotProduct, sum_apply, Finset.mul_sum, Finset.sum_apply]
  rw [Finset.sum_comm]

end NonUnitalNonAssocSemiring

end Matrix
