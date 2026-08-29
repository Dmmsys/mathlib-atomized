/-
Copyright (c) 2019 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Row and column matrices

This file provides results about row and column matrices.

## Main definitions

* `Matrix.replicateRow ι r : Matrix ι n α`: the matrix where every row is the vector `r : n → α`
* `Matrix.replicateCol ι c : Matrix m ι α`: the matrix where every column is the vector `c : m → α`
* `Matrix.updateRow M i r`: update the `i`th row of `M` to `r`
* `Matrix.updateCol M j c`: update the `j`th column of `M` to `c`

-/

@[expose] public section

variable {l m n o : Type*}

universe u v w
variable {R : Type*} {α : Type v} {β : Type w}

namespace Matrix

/--
Definition of `replicateCol` / `replicateCol` 的定义

English:
definition replicateCol
  signature: (ι : Type*) (w : m -> α)
  body: of fun x _ => w x

中文:
定义 replicateCol
  签名: (ι : 类型) (w : m -> α)
  定义体: of fun x _ => w x
-/
def replicateCol (ι : Type*) (w : m -> α) : Matrix m ι α :=
  of fun x _ => w x

-- TODO: set as an equation lemma for `replicateCol`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
/--
theorem `replicateCol_apply` / 定理 `replicateCol_apply`

English:
theorem replicateCol_apply
  given: {ι : Type*} (w : m -> α) (i) (j : ι)
  statement: replicateCol ι w i j = w i
  proof: rfl

中文:
定理 replicateCol_apply
  条件: {ι : 类型} (w : m -> α) (i) (j : ι)
  结论: replicateCol ι w i j = w i
  证明: rfl
-/
theorem replicateCol_apply {ι : Type*} (w : m -> α) (i) (j : ι) : replicateCol ι w i j = w i :=
  rfl

/--
Definition of `replicateRow` / `replicateRow` 的定义

English:
definition replicateRow
  signature: (ι : Type*) (v : n -> α)
  body: of fun _ y => v y

中文:
定义 replicateRow
  签名: (ι : 类型) (v : n -> α)
  定义体: of fun _ y => v y
-/
def replicateRow (ι : Type*) (v : n -> α) : Matrix ι n α :=
  of fun _ y => v y

variable {ι : Type*}

-- TODO: set as an equation lemma for `replicateRow`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
/--
theorem `replicateRow_apply` / 定理 `replicateRow_apply`

English:
theorem replicateRow_apply
  given: (v : n -> α) (i : ι) (j)
  statement: replicateRow ι v i j = v j
  proof: rfl

@[simp]

中文:
定理 replicateRow_apply
  条件: (v : n -> α) (i : ι) (j)
  结论: replicateRow ι v i j = v j
  证明: rfl

@[simp]
-/
theorem replicateRow_apply (v : n -> α) (i : ι) (j) : replicateRow ι v i j = v j :=
  rfl

@[simp]
/--
theorem `vecMulVec_one` / 定理 `vecMulVec_one`

English:
theorem vecMulVec_one
  given: [MulOneClass R] (x : n -> R)
  proof: by
  ext; simp [vecMulVec_apply]

@[simp]

中文:
定理 vecMulVec_one
  条件: [MulOne类 R] (x : n -> R)
  证明: by
  ext; simp [vecMulVec_apply]

@[simp]

Depends on / 依赖: vecMulVec_apply
-/
theorem vecMulVec_one [MulOneClass R] (x : n -> R) :
    vecMulVec x 1 = replicateCol m x := by
  ext; simp [vecMulVec_apply]

@[simp]
/--
theorem `one_vecMulVec` / 定理 `one_vecMulVec`

English:
theorem one_vecMulVec
  given: [MulOneClass R] (x : n -> R)
  proof: by
  ext; simp [vecMulVec_apply]

中文:
定理 one_vecMulVec
  条件: [MulOne类 R] (x : n -> R)
  证明: by
  ext; simp [vecMulVec_apply]

Depends on / 依赖: vecMulVec_apply
-/
theorem one_vecMulVec [MulOneClass R] (x : n -> R) :
    vecMulVec 1 x = replicateRow m x := by
  ext; simp [vecMulVec_apply]

/--
theorem `replicateCol_injective` / 定理 `replicateCol_injective`

English:
theorem replicateCol_injective
  given: [Nonempty ι]
  proof: by
  inhabit ι
  exact fun _x _y h => funext fun i => congr_fun₂ h i default

中文:
定理 replicateCol_injective
  条件: [非空 ι]
  证明: by
  inhabit ι
  exact fun _x _y h => funext fun i => congr_fun₂ h i default

Depends on / 依赖: inhabit
-/
theorem replicateCol_injective [Nonempty ι] :
    Function.Injective (replicateCol ι : (m -> α) -> Matrix m ι α) := by
  inhabit ι
  exact fun _x _y h => funext fun i => congr_fun₂ h i default

/--
theorem `replicateCol_inj` / 定理 `replicateCol_inj`

English:
theorem replicateCol_inj
  given: [Nonempty ι] {v w : m -> α}
  proof: replicateCol_injective.eq_iff

中文:
定理 replicateCol_inj
  条件: [非空 ι] {v w : m -> α}
  证明: replicateCol_injective.eq_iff
-/
@[simp] theorem replicateCol_inj [Nonempty ι] {v w : m -> α} :
    replicateCol ι v = replicateCol ι w ↔ v = w :=
  replicateCol_injective.eq_iff

/--
theorem `replicateCol_zero` / 定理 `replicateCol_zero`

English:
theorem replicateCol_zero
  given: [Zero α]
  statement: replicateCol ι (0 : m -> α) = 0
  proof: rfl

中文:
定理 replicateCol_zero
  条件: [零 α]
  结论: replicateCol ι (0 : m -> α) = 0
  证明: rfl
-/
@[simp] theorem replicateCol_zero [Zero α] : replicateCol ι (0 : m -> α) = 0 := rfl

/--
theorem `replicateCol_eq_zero` / 定理 `replicateCol_eq_zero`

English:
theorem replicateCol_eq_zero
  given: [Zero α] [Nonempty ι] (v : m -> α)
  proof: replicateCol_inj

@[simp]

中文:
定理 replicateCol_eq_zero
  条件: [零 α] [非空 ι] (v : m -> α)
  证明: replicateCol_inj

@[simp]
-/
@[simp] theorem replicateCol_eq_zero [Zero α] [Nonempty ι] (v : m -> α) :
    replicateCol ι v = 0 ↔ v = 0 :=
  replicateCol_inj

@[simp]
/--
theorem `replicateCol_add` / 定理 `replicateCol_add`

English:
theorem replicateCol_add
  given: [Add α] (v w : m -> α)
  proof: by
  ext
  rfl

@[simp]

中文:
定理 replicateCol_add
  条件: [加法 α] (v w : m -> α)
  证明: by
  ext
  rfl

@[simp]
-/
theorem replicateCol_add [Add α] (v w : m -> α) :
    replicateCol ι (v + w) = replicateCol ι v + replicateCol ι w := by
  ext
  rfl

@[simp]
/--
theorem `replicateCol_smul` / 定理 `replicateCol_smul`

English:
theorem replicateCol_smul
  given: [SMul R α] (x : R) (v : m -> α)
  proof: by
  ext
  rfl

中文:
定理 replicateCol_smul
  条件: [标量乘法 R α] (x : R) (v : m -> α)
  证明: by
  ext
  rfl
-/
theorem replicateCol_smul [SMul R α] (x : R) (v : m -> α) :
    replicateCol ι (x • v) = x • replicateCol ι v := by
  ext
  rfl

/--
theorem `replicateRow_injective` / 定理 `replicateRow_injective`

English:
theorem replicateRow_injective
  given: [Nonempty ι]
  proof: by
  inhabit ι
  exact fun _x _y h => funext fun j => congr_fun₂ h default j

中文:
定理 replicateRow_injective
  条件: [非空 ι]
  证明: by
  inhabit ι
  exact fun _x _y h => funext fun j => congr_fun₂ h default j

Depends on / 依赖: inhabit
-/
theorem replicateRow_injective [Nonempty ι] :
    Function.Injective (replicateRow ι : (n -> α) -> Matrix ι n α) := by
  inhabit ι
  exact fun _x _y h => funext fun j => congr_fun₂ h default j

/--
theorem `replicateRow_inj` / 定理 `replicateRow_inj`

English:
theorem replicateRow_inj
  given: [Nonempty ι] {v w : n -> α}
  proof: replicateRow_injective.eq_iff

中文:
定理 replicateRow_inj
  条件: [非空 ι] {v w : n -> α}
  证明: replicateRow_injective.eq_iff
-/
@[simp] theorem replicateRow_inj [Nonempty ι] {v w : n -> α} :
    replicateRow ι v = replicateRow ι w ↔ v = w :=
  replicateRow_injective.eq_iff

/--
theorem `replicateRow_zero` / 定理 `replicateRow_zero`

English:
theorem replicateRow_zero
  given: [Zero α]
  statement: replicateRow ι (0 : n -> α) = 0
  proof: rfl

中文:
定理 replicateRow_zero
  条件: [零 α]
  结论: replicateRow ι (0 : n -> α) = 0
  证明: rfl
-/
@[simp] theorem replicateRow_zero [Zero α] : replicateRow ι (0 : n -> α) = 0 := rfl

/--
theorem `replicateRow_eq_zero` / 定理 `replicateRow_eq_zero`

English:
theorem replicateRow_eq_zero
  given: [Zero α] [Nonempty ι] (v : n -> α)
  proof: replicateRow_inj

@[simp]

中文:
定理 replicateRow_eq_zero
  条件: [零 α] [非空 ι] (v : n -> α)
  证明: replicateRow_inj

@[simp]
-/
@[simp] theorem replicateRow_eq_zero [Zero α] [Nonempty ι] (v : n -> α) :
    replicateRow ι v = 0 ↔ v = 0 :=
  replicateRow_inj

@[simp]
/--
theorem `replicateRow_add` / 定理 `replicateRow_add`

English:
theorem replicateRow_add
  given: [Add α] (v w : m -> α)
  proof: by
  ext
  rfl

@[simp]

中文:
定理 replicateRow_add
  条件: [加法 α] (v w : m -> α)
  证明: by
  ext
  rfl

@[simp]
-/
theorem replicateRow_add [Add α] (v w : m -> α) :
    replicateRow ι (v + w) = replicateRow ι v + replicateRow ι w := by
  ext
  rfl

@[simp]
/--
theorem `replicateRow_smul` / 定理 `replicateRow_smul`

English:
theorem replicateRow_smul
  given: [SMul R α] (x : R) (v : m -> α)
  proof: by
  ext
  rfl

@[simp]

中文:
定理 replicateRow_smul
  条件: [标量乘法 R α] (x : R) (v : m -> α)
  证明: by
  ext
  rfl

@[simp]
-/
theorem replicateRow_smul [SMul R α] (x : R) (v : m -> α) :
    replicateRow ι (x • v) = x • replicateRow ι v := by
  ext
  rfl

@[simp]
/--
theorem `transpose_replicateCol` / 定理 `transpose_replicateCol`

English:
theorem transpose_replicateCol
  given: (v : m -> α)
  statement: (replicateCol ι v)ᵀ = replicateRow ι v
  proof: by
  ext
  rfl

@[simp]

中文:
定理 transpose_replicateCol
  条件: (v : m -> α)
  结论: (replicateCol ι v)ᵀ = replicateRow ι v
  证明: by
  ext
  rfl

@[simp]
-/
theorem transpose_replicateCol (v : m -> α) : (replicateCol ι v)ᵀ = replicateRow ι v := by
  ext
  rfl

@[simp]
/--
theorem `transpose_replicateRow` / 定理 `transpose_replicateRow`

English:
theorem transpose_replicateRow
  given: (v : m -> α)
  statement: (replicateRow ι v)ᵀ = replicateCol ι v
  proof: by
  ext
  rfl

@[simp]

中文:
定理 transpose_replicateRow
  条件: (v : m -> α)
  结论: (replicateRow ι v)ᵀ = replicateCol ι v
  证明: by
  ext
  rfl

@[simp]
-/
theorem transpose_replicateRow (v : m -> α) : (replicateRow ι v)ᵀ = replicateCol ι v := by
  ext
  rfl

@[simp]
/--
theorem `conjTranspose_replicateCol` / 定理 `conjTranspose_replicateCol`

English:
theorem conjTranspose_replicateCol
  given: [Star α] (v : m -> α)
  proof: by
  ext
  rfl

@[simp]

中文:
定理 conjTranspose_replicateCol
  条件: [对合 α] (v : m -> α)
  证明: by
  ext
  rfl

@[simp]
-/
theorem conjTranspose_replicateCol [Star α] (v : m -> α) :
    (replicateCol ι v)ᴴ = replicateRow ι (star v) := by
  ext
  rfl

@[simp]
/--
theorem `conjTranspose_replicateRow` / 定理 `conjTranspose_replicateRow`

English:
theorem conjTranspose_replicateRow
  given: [Star α] (v : m -> α)
  proof: by
  ext
  rfl

中文:
定理 conjTranspose_replicateRow
  条件: [对合 α] (v : m -> α)
  证明: by
  ext
  rfl
-/
theorem conjTranspose_replicateRow [Star α] (v : m -> α) :
    (replicateRow ι v)ᴴ = replicateCol ι (star v) := by
  ext
  rfl

/--
theorem `replicateRow_vecMul` / 定理 `replicateRow_vecMul`

English:
theorem replicateRow_vecMul
  statement: [Fintype m] [NonUnitalNonAssocSemiring α] (M : Matrix m n α)
  proof: by
  ext
  rfl

中文:
定理 replicateRow_vecMul
  结论: [有限类型 m] [非幺非结合半环 α] (M : 矩阵 m n α)
  证明: by
  ext
  rfl
-/
theorem replicateRow_vecMul [Fintype m] [NonUnitalNonAssocSemiring α] (M : Matrix m n α)
    (v : m -> α) : replicateRow ι (v ᵥ* M) = replicateRow ι v * M := by
  ext
  rfl

/--
theorem `replicateCol_vecMul` / 定理 `replicateCol_vecMul`

English:
theorem replicateCol_vecMul
  statement: [Fintype m] [NonUnitalNonAssocSemiring α] (M : Matrix m n α)
  proof: by
  ext
  rfl

中文:
定理 replicateCol_vecMul
  结论: [有限类型 m] [非幺非结合半环 α] (M : 矩阵 m n α)
  证明: by
  ext
  rfl
-/
theorem replicateCol_vecMul [Fintype m] [NonUnitalNonAssocSemiring α] (M : Matrix m n α)
    (v : m -> α) : replicateCol ι (v ᵥ* M) = (replicateRow ι v * M)ᵀ := by
  ext
  rfl

/--
theorem `replicateCol_mulVec` / 定理 `replicateCol_mulVec`

English:
theorem replicateCol_mulVec
  statement: [Fintype n] [NonUnitalNonAssocSemiring α] (M : Matrix m n α)
  proof: by
  ext
  rfl

中文:
定理 replicateCol_mulVec
  结论: [有限类型 n] [非幺非结合半环 α] (M : 矩阵 m n α)
  证明: by
  ext
  rfl
-/
theorem replicateCol_mulVec [Fintype n] [NonUnitalNonAssocSemiring α] (M : Matrix m n α)
    (v : n -> α) : replicateCol ι (M *ᵥ v) = M * replicateCol ι v := by
  ext
  rfl

/--
theorem `replicateRow_mulVec` / 定理 `replicateRow_mulVec`

English:
theorem replicateRow_mulVec
  statement: [Fintype n] [NonUnitalNonAssocSemiring α] (M : Matrix m n α)
  proof: by
  ext
  rfl

中文:
定理 replicateRow_mulVec
  结论: [有限类型 n] [非幺非结合半环 α] (M : 矩阵 m n α)
  证明: by
  ext
  rfl
-/
theorem replicateRow_mulVec [Fintype n] [NonUnitalNonAssocSemiring α] (M : Matrix m n α)
    (v : n -> α) : replicateRow ι (M *ᵥ v) = (M * replicateCol ι v)ᵀ := by
  ext
  rfl

/--
theorem `replicateRow_mulVec_eq_const` / 定理 `replicateRow_mulVec_eq_const`

English:
theorem replicateRow_mulVec_eq_const
  given: [Fintype m] [NonUnitalNonAssocSemiring α] (v w : m -> α)
  proof: rfl

中文:
定理 replicateRow_mulVec_eq_const
  条件: [有限类型 m] [非幺非结合半环 α] (v w : m -> α)
  证明: rfl
-/
theorem replicateRow_mulVec_eq_const [Fintype m] [NonUnitalNonAssocSemiring α] (v w : m -> α) :
    replicateRow ι v *ᵥ w = Function.const _ (v ⬝ᵥ w) := rfl

/--
theorem `mulVec_replicateCol_eq_const` / 定理 `mulVec_replicateCol_eq_const`

English:
theorem mulVec_replicateCol_eq_const
  given: [Fintype m] [NonUnitalNonAssocSemiring α] (v w : m -> α)
  proof: rfl

中文:
定理 mulVec_replicateCol_eq_const
  条件: [有限类型 m] [非幺非结合半环 α] (v w : m -> α)
  证明: rfl
-/
theorem mulVec_replicateCol_eq_const [Fintype m] [NonUnitalNonAssocSemiring α] (v w : m -> α) :
    v ᵥ* replicateCol ι w = Function.const _ (v ⬝ᵥ w) := rfl

/--
theorem `replicateRow_mul_replicateCol` / 定理 `replicateRow_mul_replicateCol`

English:
theorem replicateRow_mul_replicateCol
  given: [Fintype m] [Mul α] [AddCommMonoid α] (v w : m -> α)
  proof: rfl

@[simp]

中文:
定理 replicateRow_mul_replicateCol
  条件: [有限类型 m] [乘法 α] [加法交换幺半群 α] (v w : m -> α)
  证明: rfl

@[simp]
-/
theorem replicateRow_mul_replicateCol [Fintype m] [Mul α] [AddCommMonoid α] (v w : m -> α) :
    replicateRow ι v * replicateCol ι w = of fun _ _ => v ⬝ᵥ w :=
  rfl

@[simp]
/--
theorem `replicateRow_mul_replicateCol_apply` / 定理 `replicateRow_mul_replicateCol_apply`

English:
theorem replicateRow_mul_replicateCol_apply
  statement: [Fintype m] [Mul α] [AddCommMonoid α] (v w : m -> α)
  proof: rfl

@[simp]

中文:
定理 replicateRow_mul_replicateCol_apply
  结论: [有限类型 m] [乘法 α] [加法交换幺半群 α] (v w : m -> α)
  证明: rfl

@[simp]
-/
theorem replicateRow_mul_replicateCol_apply [Fintype m] [Mul α] [AddCommMonoid α] (v w : m -> α)
    (i j) : (replicateRow ι v * replicateCol ι w) i j = v ⬝ᵥ w :=
  rfl

@[simp]
/--
theorem `diag_replicateCol_mul_replicateRow` / 定理 `diag_replicateCol_mul_replicateRow`

English:
theorem diag_replicateCol_mul_replicateRow
  given: [Mul α] [AddCommMonoid α] [Unique ι] (a b : n -> α)
  proof: by
  ext
  simp [Matrix.mul_apply, replicateCol, replicateRow]

中文:
定理 diag_replicateCol_mul_replicateRow
  条件: [乘法 α] [加法交换幺半群 α] [唯一 ι] (a b : n -> α)
  证明: by
  ext
  simp [Matrix.mul_apply, replicateCol, replicateRow]

Depends on / 依赖: Matrix, Matrix.mul_apply, mul_apply, replicateCol, replicateRow
-/
theorem diag_replicateCol_mul_replicateRow [Mul α] [AddCommMonoid α] [Unique ι] (a b : n -> α) :
    diag (replicateCol ι a * replicateRow ι b) = a * b := by
  ext
  simp [Matrix.mul_apply, replicateCol, replicateRow]

variable (ι)

/--
theorem `vecMulVec_eq` / 定理 `vecMulVec_eq`

English:
theorem vecMulVec_eq
  given: [Mul α] [AddCommMonoid α] [Unique ι] (w : m -> α) (v : n -> α)
  proof: by
  ext
  simp [vecMulVec, mul_apply]

中文:
定理 vecMulVec_eq
  条件: [乘法 α] [加法交换幺半群 α] [唯一 ι] (w : m -> α) (v : n -> α)
  证明: by
  ext
  simp [vecMulVec, mul_apply]

Depends on / 依赖: mul_apply, vecMulVec
-/
theorem vecMulVec_eq [Mul α] [AddCommMonoid α] [Unique ι] (w : m -> α) (v : n -> α) :
    vecMulVec w v = replicateCol ι w * replicateRow ι v := by
  ext
  simp [vecMulVec, mul_apply]

/-! ### Updating rows and columns -/

/--
Definition of `updateRow` / `updateRow` 的定义

English:
definition updateRow
  signature: [DecidableEq m] (M : Matrix m n α) (i : m) (b : n -> α)
  body: of Function.update M i b

中文:
定义 updateRow
  签名: [DecidableEq m] (M : 矩阵 m n α) (i : m) (b : n -> α)
  定义体: of Function.update M i b

Depends on / 依赖: Function, Function.update, update
-/
def updateRow [DecidableEq m] (M : Matrix m n α) (i : m) (b : n -> α) : Matrix m n α :=
of Function.update M i b

/--
Definition of `updateCol` / `updateCol` 的定义

English:
definition updateCol
  signature: [DecidableEq n] (M : Matrix m n α) (j : n) (b : m -> α)
  body: of fun i => Function.update (M i) j (b i)

中文:
定义 updateCol
  签名: [DecidableEq n] (M : 矩阵 m n α) (j : n) (b : m -> α)
  定义体: of fun i => Function.update (M i) j (b i)

Depends on / 依赖: Function, Function.update, update
-/
def updateCol [DecidableEq n] (M : Matrix m n α) (j : n) (b : m -> α) : Matrix m n α :=
  of fun i => Function.update (M i) j (b i)

variable {M : Matrix m n α} {i : m} {j : n} {b : n -> α} {c : m -> α}

@[simp]
/--
theorem `updateRow_self` / 定理 `updateRow_self`

English:
theorem updateRow_self
  given: [DecidableEq m]
  statement: updateRow M i b i = b
  proof: Function.update_self (β := fun _ => (n -> α)) i b M

@[simp]

中文:
定理 updateRow_self
  条件: [DecidableEq m]
  结论: updateRow M i b i = b
  证明: Function.update_self (β := fun _ => (n -> α)) i b M

@[simp]

Depends on / 依赖: Function, Function.update_self, update_self
-/
theorem updateRow_self [DecidableEq m] : updateRow M i b i = b :=
  Function.update_self (β := fun _ => (n -> α)) i b M

@[simp]
/--
theorem `updateCol_self` / 定理 `updateCol_self`

English:
theorem updateCol_self
  given: [DecidableEq n]
  statement: updateCol M j c i j = c i
  proof: Function.update_self (β := fun _ => α) j (c i) (M i)

@[simp]

中文:
定理 updateCol_self
  条件: [DecidableEq n]
  结论: updateCol M j c i j = c i
  证明: Function.update_self (β := fun _ => α) j (c i) (M i)

@[simp]

Depends on / 依赖: Function, Function.update_self, update_self
-/
theorem updateCol_self [DecidableEq n] : updateCol M j c i j = c i :=
  Function.update_self (β := fun _ => α) j (c i) (M i)

@[simp]
/--
theorem `updateRow_ne` / 定理 `updateRow_ne`

English:
theorem updateRow_ne
  given: [DecidableEq m] {i' : m} (i_ne : i' != i)
  statement: updateRow M i b i' = M i'
  proof: Function.update_of_ne (β := fun _ => (n -> α)) i_ne b M

@[simp]

中文:
定理 updateRow_ne
  条件: [DecidableEq m] {i' : m} (i_ne : i' != i)
  结论: updateRow M i b i' = M i'
  证明: Function.update_of_ne (β := fun _ => (n -> α)) i_ne b M

@[simp]

Depends on / 依赖: Function, Function.update_of_ne, i_ne, update_of_ne
-/
theorem updateRow_ne [DecidableEq m] {i' : m} (i_ne : i' != i) : updateRow M i b i' = M i' :=
  Function.update_of_ne (β := fun _ => (n -> α)) i_ne b M

@[simp]
/--
theorem `updateCol_ne` / 定理 `updateCol_ne`

English:
theorem updateCol_ne
  given: [DecidableEq n] {j' : n} (j_ne : j' != j)
  proof: Function.update_of_ne (β := fun _ => α) j_ne (c i) (M i)

中文:
定理 updateCol_ne
  条件: [DecidableEq n] {j' : n} (j_ne : j' != j)
  证明: Function.update_of_ne (β := fun _ => α) j_ne (c i) (M i)

Depends on / 依赖: Function, Function.update_of_ne, j_ne, update_of_ne
-/
theorem updateCol_ne [DecidableEq n] {j' : n} (j_ne : j' != j) :
    updateCol M j c i j' = M i j' :=
  Function.update_of_ne (β := fun _ => α) j_ne (c i) (M i)

/--
theorem `updateRow_apply` / 定理 `updateRow_apply`

English:
theorem updateRow_apply
  given: [DecidableEq m] {i' : m}
  proof: by
  by_cases h : i' = i
  · rw [h, updateRow_self, if_pos rfl]
  · rw [updateRow_ne h, if_neg h]

中文:
定理 updateRow_apply
  条件: [DecidableEq m] {i' : m}
  证明: by
  by_cases h : i' = i
  · rw [h, updateRow_self, if_pos rfl]
  · rw [updateRow_ne h, if_neg h]

Depends on / 依赖: if_neg, if_pos, updateRow_ne, updateRow_self
-/
theorem updateRow_apply [DecidableEq m] {i' : m} :
    updateRow M i b i' j = if i' = i then b j else M i' j := by
  by_cases h : i' = i
  · rw [h, updateRow_self, if_pos rfl]
  · rw [updateRow_ne h, if_neg h]

/--
theorem `updateCol_apply` / 定理 `updateCol_apply`

English:
theorem updateCol_apply
  given: [DecidableEq n] {j' : n}
  proof: by
  by_cases h : j' = j
  · rw [h, updateCol_self, if_pos rfl]
  · rw [updateCol_ne h, if_neg h]

@[simp]

中文:
定理 updateCol_apply
  条件: [DecidableEq n] {j' : n}
  证明: by
  by_cases h : j' = j
  · rw [h, updateCol_self, if_pos rfl]
  · rw [updateCol_ne h, if_neg h]

@[simp]

Depends on / 依赖: if_neg, if_pos, updateCol_ne, updateCol_self
-/
theorem updateCol_apply [DecidableEq n] {j' : n} :
    updateCol M j c i j' = if j' = j then c i else M i j' := by
  by_cases h : j' = j
  · rw [h, updateCol_self, if_pos rfl]
  · rw [updateCol_ne h, if_neg h]

@[simp]
/--
theorem `updateCol_subsingleton` / 定理 `updateCol_subsingleton`

English:
theorem updateCol_subsingleton
  given: [Subsingleton n] (A : Matrix m n R) (i : n) (b : m -> R)
  proof: by
  ext x y
  simp [Subsingleton.elim i y]

@[simp]

中文:
定理 updateCol_subsingleton
  条件: [子单例 n] (A : 矩阵 m n R) (i : n) (b : m -> R)
  证明: by
  ext x y
  simp [Subsingleton.elim i y]

@[simp]

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem updateCol_subsingleton [Subsingleton n] (A : Matrix m n R) (i : n) (b : m -> R) :
    A.updateCol i b = (replicateCol (Fin 1) b).submatrix id (Function.const n 0) := by
  ext x y
  simp [Subsingleton.elim i y]

@[simp]
/--
theorem `updateRow_subsingleton` / 定理 `updateRow_subsingleton`

English:
theorem updateRow_subsingleton
  given: [Subsingleton m] (A : Matrix m n R) (i : m) (b : n -> R)
  proof: by
  ext x y
  simp [Subsingleton.elim i x]

中文:
定理 updateRow_subsingleton
  条件: [子单例 m] (A : 矩阵 m n R) (i : m) (b : n -> R)
  证明: by
  ext x y
  simp [Subsingleton.elim i x]

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem updateRow_subsingleton [Subsingleton m] (A : Matrix m n R) (i : m) (b : n -> R) :
    A.updateRow i b = (replicateRow (Fin 1) b).submatrix (Function.const m 0) id := by
  ext x y
  simp [Subsingleton.elim i x]

/--
theorem `map_updateRow` / 定理 `map_updateRow`

English:
theorem map_updateRow
  given: [DecidableEq m] (f : α -> β)
  proof: by
  ext
  rw [updateRow_apply]; rw [map_apply]; rw [map_apply]; rw [updateRow_apply]
  exact apply_ite f _ _ _

中文:
定理 map_updateRow
  条件: [DecidableEq m] (f : α -> β)
  证明: by
  ext
  rw [updateRow_apply]; rw [map_apply]; rw [map_apply]; rw [updateRow_apply]
  exact apply_ite f _ _ _

Depends on / 依赖: apply_ite, map_apply, updateRow_apply
-/
theorem map_updateRow [DecidableEq m] (f : α -> β) :
    map (updateRow M i b) f = updateRow (M.map f) i (f ∘ b) := by
  ext
  rw [updateRow_apply]; rw [map_apply]; rw [map_apply]; rw [updateRow_apply]
  exact apply_ite f _ _ _

/--
theorem `map_updateCol` / 定理 `map_updateCol`

English:
theorem map_updateCol
  given: [DecidableEq n] (f : α -> β)
  proof: by
  ext
  rw [updateCol_apply]; rw [map_apply]; rw [map_apply]; rw [updateCol_apply]
  exact apply_ite f _ _ _

中文:
定理 map_updateCol
  条件: [DecidableEq n] (f : α -> β)
  证明: by
  ext
  rw [updateCol_apply]; rw [map_apply]; rw [map_apply]; rw [updateCol_apply]
  exact apply_ite f _ _ _

Depends on / 依赖: apply_ite, map_apply, updateCol_apply
-/
theorem map_updateCol [DecidableEq n] (f : α -> β) :
    map (updateCol M j c) f = updateCol (M.map f) j (f ∘ c) := by
  ext
  rw [updateCol_apply]; rw [map_apply]; rw [map_apply]; rw [updateCol_apply]
  exact apply_ite f _ _ _

/--
theorem `updateRow_transpose` / 定理 `updateRow_transpose`

English:
theorem updateRow_transpose
  given: [DecidableEq n]
  statement: updateRow Mᵀ j c = (updateCol M j c)ᵀ
  proof: by
  ext
  rw [transpose_apply]; rw [updateRow_apply]; rw [updateCol_apply]
  rfl

中文:
定理 updateRow_transpose
  条件: [DecidableEq n]
  结论: updateRow Mᵀ j c = (updateCol M j c)ᵀ
  证明: by
  ext
  rw [transpose_apply]; rw [updateRow_apply]; rw [updateCol_apply]
  rfl

Depends on / 依赖: Subsingleton, Subsingleton.measurableSingletonClass, measurableSingletonClass, transpose_apply, updateCol_apply, updateRow_apply
-/
theorem updateRow_transpose [DecidableEq n] : updateRow Mᵀ j c = (updateCol M j c)ᵀ := by
  ext
  rw [transpose_apply]; rw [updateRow_apply]; rw [updateCol_apply]
  rfl

/--
theorem `updateCol_transpose` / 定理 `updateCol_transpose`

English:
theorem updateCol_transpose
  given: [DecidableEq m]
  statement: updateCol Mᵀ i b = (updateRow M i b)ᵀ
  proof: by
  ext
  rw [transpose_apply]; rw [updateRow_apply]; rw [updateCol_apply]
  rfl

中文:
定理 updateCol_transpose
  条件: [DecidableEq m]
  结论: updateCol Mᵀ i b = (updateRow M i b)ᵀ
  证明: by
  ext
  rw [transpose_apply]; rw [updateRow_apply]; rw [updateCol_apply]
  rfl

Depends on / 依赖: transpose_apply, updateCol_apply, updateRow_apply
-/
theorem updateCol_transpose [DecidableEq m] : updateCol Mᵀ i b = (updateRow M i b)ᵀ := by
  ext
  rw [transpose_apply]; rw [updateRow_apply]; rw [updateCol_apply]
  rfl

/--
theorem `updateRow_conjTranspose` / 定理 `updateRow_conjTranspose`

English:
theorem updateRow_conjTranspose
  given: [DecidableEq n] [Star α]
  proof: by
  rw [conjTranspose]; rw [conjTranspose]; rw [transpose_map]; rw [transpose_map]; rw [updateRow_transpose]; rw [map_updateCol]
  rfl

中文:
定理 updateRow_conjTranspose
  条件: [DecidableEq n] [对合 α]
  证明: by
  rw [conjTranspose]; rw [conjTranspose]; rw [transpose_map]; rw [transpose_map]; rw [updateRow_transpose]; rw [map_updateCol]
  rfl

Depends on / 依赖: conjTranspose, map_updateCol, transpose_map, updateRow_transpose
-/
theorem updateRow_conjTranspose [DecidableEq n] [Star α] :
    updateRow Mᴴ j (star c) = (updateCol M j c)ᴴ := by
  rw [conjTranspose]; rw [conjTranspose]; rw [transpose_map]; rw [transpose_map]; rw [updateRow_transpose]; rw [map_updateCol]
  rfl

/--
theorem `updateCol_conjTranspose` / 定理 `updateCol_conjTranspose`

English:
theorem updateCol_conjTranspose
  given: [DecidableEq m] [Star α]
  proof: by
  rw [conjTranspose]; rw [conjTranspose]; rw [transpose_map]; rw [transpose_map]; rw [updateCol_transpose]; rw [map_updateRow]
  rfl

@[simp]

中文:
定理 updateCol_conjTranspose
  条件: [DecidableEq m] [对合 α]
  证明: by
  rw [conjTranspose]; rw [conjTranspose]; rw [transpose_map]; rw [transpose_map]; rw [updateCol_transpose]; rw [map_updateRow]
  rfl

@[simp]

Depends on / 依赖: conjTranspose, map_updateRow, transpose_map, updateCol_transpose
-/
theorem updateCol_conjTranspose [DecidableEq m] [Star α] :
    updateCol Mᴴ i (star b) = (updateRow M i b)ᴴ := by
  rw [conjTranspose]; rw [conjTranspose]; rw [transpose_map]; rw [transpose_map]; rw [updateCol_transpose]; rw [map_updateRow]
  rfl

@[simp]
/--
theorem `updateRow_eq_self` / 定理 `updateRow_eq_self`

English:
theorem updateRow_eq_self
  given: [DecidableEq m] (A : Matrix m n α) (i : m)
  statement: A.updateRow i (A i) = A
  proof: Function.update_eq_self i A

@[simp]

中文:
定理 updateRow_eq_self
  条件: [DecidableEq m] (A : 矩阵 m n α) (i : m)
  结论: A.updateRow i (A i) = A
  证明: Function.update_eq_self i A

@[simp]

Depends on / 依赖: Function, Function.update_eq_self, update_eq_self
-/
theorem updateRow_eq_self [DecidableEq m] (A : Matrix m n α) (i : m) : A.updateRow i (A i) = A :=
  Function.update_eq_self i A

@[simp]
/--
theorem `updateCol_eq_self` / 定理 `updateCol_eq_self`

English:
theorem updateCol_eq_self
  given: [DecidableEq n] (A : Matrix m n α) (i : n)
  proof: funext fun j => Function.update_eq_self i (A j)

@[simp]

中文:
定理 updateCol_eq_self
  条件: [DecidableEq n] (A : 矩阵 m n α) (i : n)
  证明: funext fun j => Function.update_eq_self i (A j)

@[simp]

Depends on / 依赖: Function, Function.update_eq_self, update_eq_self
-/
theorem updateCol_eq_self [DecidableEq n] (A : Matrix m n α) (i : n) :
    (A.updateCol i fun j => A j i) = A :=
  funext fun j => Function.update_eq_self i (A j)

@[simp]
/--
theorem `updateRow_zero_zero` / 定理 `updateRow_zero_zero`

English:
theorem updateRow_zero_zero
  given: [DecidableEq m] [Zero α] (i : m)
  proof: updateRow_eq_self _ i

@[simp]

中文:
定理 updateRow_zero_zero
  条件: [DecidableEq m] [零 α] (i : m)
  证明: updateRow_eq_self _ i

@[simp]

Depends on / 依赖: updateRow_eq_self
-/
theorem updateRow_zero_zero [DecidableEq m] [Zero α] (i : m) :
    (0 : Matrix m n α).updateRow i 0 = 0 :=
  updateRow_eq_self _ i

@[simp]
/--
theorem `updateCol_zero_zero` / 定理 `updateCol_zero_zero`

English:
theorem updateCol_zero_zero
  given: [DecidableEq n] [Zero α] (i : n)
  proof: updateCol_eq_self _ i

中文:
定理 updateCol_zero_zero
  条件: [DecidableEq n] [零 α] (i : n)
  证明: updateCol_eq_self _ i

Depends on / 依赖: updateCol_eq_self
-/
theorem updateCol_zero_zero [DecidableEq n] [Zero α] (i : n) :
    (0 : Matrix m n α).updateCol i 0 = 0 :=
  updateCol_eq_self _ i

/--
theorem `diagonal_updateCol_single` / 定理 `diagonal_updateCol_single`

English:
theorem diagonal_updateCol_single
  given: [DecidableEq n] [Zero α] (v : n -> α) (i : n) (x : α)
  proof: by
  ext j k
  obtain rfl | hjk := eq_or_ne j k
  · rw [diagonal_apply_eq]
    obtain rfl | hji := eq_or_ne j i
    · rw [updateCol_self, Pi.single_eq_same, Function.update_self]
    · rw [updateCol_ne hji, diagonal_apply_eq, Function.update_of_ne hji]
  · rw [diagonal_apply_ne _ hjk]
    obtain rfl

中文:
定理 diagonal_updateCol_single
  条件: [DecidableEq n] [零 α] (v : n -> α) (i : n) (x : α)
  证明: by
  ext j k
  obtain rfl | hjk := eq_or_ne j k
  · rw [diagonal_apply_eq]
    obtain rfl | hji := eq_or_ne j i
    · rw [updateCol_self, Pi.single_eq_same, Function.update_self]
    · rw [updateCol_ne hji, diagonal_apply_eq, Function.update_of_ne hji]
  · rw [diagonal_apply_ne _ hjk]
    obtain rfl

Depends on / 依赖: Function, Function.update_of_ne, Function.update_self, Pi.single_eq_of_ne, Pi.single_eq_same, diagonal_apply_eq, diagonal_apply_ne, eq_or_ne, single_eq_of_ne, single_eq_same, updateCol_ne, updateCol_self, update_of_ne, update_self
-/
theorem diagonal_updateCol_single [DecidableEq n] [Zero α] (v : n -> α) (i : n) (x : α) :
    (diagonal v).updateCol i (Pi.single i x) = diagonal (Function.update v i x) := by
  ext j k
  obtain rfl | hjk := eq_or_ne j k
  · rw [diagonal_apply_eq]
    obtain rfl | hji := eq_or_ne j i
    · rw [updateCol_self, Pi.single_eq_same, Function.update_self]
    · rw [updateCol_ne hji, diagonal_apply_eq, Function.update_of_ne hji]
  · rw [diagonal_apply_ne _ hjk]
    obtain rfl | hki := eq_or_ne k i
    · rw [updateCol_self, Pi.single_eq_of_ne hjk]
    · rw [updateCol_ne hki, diagonal_apply_ne _ hjk]

/--
theorem `diagonal_updateRow_single` / 定理 `diagonal_updateRow_single`

English:
theorem diagonal_updateRow_single
  given: [DecidableEq n] [Zero α] (v : n -> α) (i : n) (x : α)
  proof: by
  rw [← diagonal_transpose]; rw [updateRow_transpose]; rw [diagonal_updateCol_single]; rw [diagonal_transpose]

@[simp]

中文:
定理 diagonal_updateRow_single
  条件: [DecidableEq n] [零 α] (v : n -> α) (i : n) (x : α)
  证明: by
  rw [← diagonal_transpose]; rw [updateRow_transpose]; rw [diagonal_updateCol_single]; rw [diagonal_transpose]

@[simp]

Depends on / 依赖: diagonal_transpose, diagonal_updateCol_single, updateRow_transpose
-/
theorem diagonal_updateRow_single [DecidableEq n] [Zero α] (v : n -> α) (i : n) (x : α) :
    (diagonal v).updateRow i (Pi.single i x) = diagonal (Function.update v i x) := by
  rw [← diagonal_transpose]; rw [updateRow_transpose]; rw [diagonal_updateCol_single]; rw [diagonal_transpose]

@[simp]
/--
theorem `updateRow_idem` / 定理 `updateRow_idem`

English:
theorem updateRow_idem
  given: [DecidableEq m] (A : Matrix m n α) (i : m) (x y : n -> α)
  proof: Function.update_idem _ _ _

中文:
定理 updateRow_idem
  条件: [DecidableEq m] (A : 矩阵 m n α) (i : m) (x y : n -> α)
  证明: Function.update_idem _ _ _

Depends on / 依赖: Function, Function.update_idem, update_idem
-/
theorem updateRow_idem [DecidableEq m] (A : Matrix m n α) (i : m) (x y : n -> α) :
    (A.updateRow i x).updateRow i y = A.updateRow i y := Function.update_idem _ _ _

/--
theorem `updateRow_comm` / 定理 `updateRow_comm`

English:
theorem updateRow_comm
  given: [DecidableEq m] (A : Matrix m n α) {i i' : m} (h : i != i') (x y : n -> α)
  proof: Function.update_comm h _ _ _

@[simp]

中文:
定理 updateRow_comm
  条件: [DecidableEq m] (A : 矩阵 m n α) {i i' : m} (h : i != i') (x y : n -> α)
  证明: Function.update_comm h _ _ _

@[simp]

Depends on / 依赖: Function, Function.update_comm, update_comm
-/
theorem updateRow_comm [DecidableEq m] (A : Matrix m n α) {i i' : m} (h : i != i') (x y : n -> α) :
    (A.updateRow i x).updateRow i' y = (A.updateRow i' y).updateRow i x :=
  Function.update_comm h _ _ _

@[simp]
/--
theorem `updateCol_idem` / 定理 `updateCol_idem`

English:
theorem updateCol_idem
  given: [DecidableEq n] (A : Matrix m n α) (j : n) (x y : m -> α)
  proof: by
simpa only [updateRow_transpose] using! congr_arg transpose updateRow_idem Aᵀ j x y

中文:
定理 updateCol_idem
  条件: [DecidableEq n] (A : 矩阵 m n α) (j : n) (x y : m -> α)
  证明: by
simpa only [updateRow_transpose] using! congr_arg transpose updateRow_idem Aᵀ j x y

Depends on / 依赖: congr_arg, transpose, updateRow_idem, updateRow_transpose
-/
theorem updateCol_idem [DecidableEq n] (A : Matrix m n α) (j : n) (x y : m -> α) :
    (A.updateCol j x).updateCol j y = A.updateCol j y := by
simpa only [updateRow_transpose] using! congr_arg transpose updateRow_idem Aᵀ j x y

/--
theorem `updateCol_comm` / 定理 `updateCol_comm`

English:
theorem updateCol_comm
  given: [DecidableEq n] (A : Matrix m n α) {j j' : n} (h : j != j') (x y : m -> α)
  proof: by
simpa only [updateRow_transpose] using! congr_arg transpose updateRow_comm Aᵀ h x y

中文:
定理 updateCol_comm
  条件: [DecidableEq n] (A : 矩阵 m n α) {j j' : n} (h : j != j') (x y : m -> α)
  证明: by
simpa only [updateRow_transpose] using! congr_arg transpose updateRow_comm Aᵀ h x y

Depends on / 依赖: congr_arg, transpose, updateRow_comm, updateRow_transpose
-/
theorem updateCol_comm [DecidableEq n] (A : Matrix m n α) {j j' : n} (h : j != j') (x y : m -> α) :
    (A.updateCol j x).updateCol j' y = (A.updateCol j' y).updateCol j x := by
simpa only [updateRow_transpose] using! congr_arg transpose updateRow_comm Aᵀ h x y



/--
theorem `updateRow_submatrix_equiv` / 定理 `updateRow_submatrix_equiv`

English:
theorem updateRow_submatrix_equiv
  statement: [DecidableEq l] [DecidableEq m] (A : Matrix m n α) (i : l)
  proof: by
  ext i' j
  simp only [submatrix_apply, updateRow_apply, Equiv.apply_eq_iff_eq, Equiv.symm_apply_apply]

中文:
定理 updateRow_submatrix_equiv
  结论: [DecidableEq l] [DecidableEq m] (A : 矩阵 m n α) (i : l)
  证明: by
  ext i' j
  simp only [submatrix_apply, updateRow_apply, Equiv.apply_eq_iff_eq, Equiv.symm_apply_apply]

Depends on / 依赖: Equiv.apply_eq_iff_eq, Equiv.symm_apply_apply, apply_eq_iff_eq, submatrix_apply, symm_apply_apply, updateRow_apply
-/
theorem updateRow_submatrix_equiv [DecidableEq l] [DecidableEq m] (A : Matrix m n α) (i : l)
    (r : o -> α) (e : l ≃ m) (f : o ≃ n) :
    updateRow (A.submatrix e f) i r = (A.updateRow (e i) fun j => r (f.symm j)).submatrix e f := by
  ext i' j
  simp only [submatrix_apply, updateRow_apply, Equiv.apply_eq_iff_eq, Equiv.symm_apply_apply]

/--
theorem `submatrix_updateRow_equiv` / 定理 `submatrix_updateRow_equiv`

English:
theorem submatrix_updateRow_equiv
  statement: [DecidableEq l] [DecidableEq m] (A : Matrix m n α) (i : m)
  proof: Eq.trans (by simp_rw [Equiv.apply_symm_apply]) (updateRow_submatrix_equiv A _ _ e f).symm

中文:
定理 submatrix_updateRow_equiv
  结论: [DecidableEq l] [DecidableEq m] (A : 矩阵 m n α) (i : m)
  证明: Eq.trans (by simp_rw [Equiv.apply_symm_apply]) (updateRow_submatrix_equiv A _ _ e f).symm

Depends on / 依赖: Eq.trans, Equiv.apply_symm_apply, apply_symm_apply, simp_rw, updateRow_submatrix_equiv
-/
theorem submatrix_updateRow_equiv [DecidableEq l] [DecidableEq m] (A : Matrix m n α) (i : m)
    (r : n -> α) (e : l ≃ m) (f : o ≃ n) :
    (A.updateRow i r).submatrix e f = updateRow (A.submatrix e f) (e.symm i) fun i => r (f i) :=
  Eq.trans (by simp_rw [Equiv.apply_symm_apply]) (updateRow_submatrix_equiv A _ _ e f).symm

/--
theorem `updateCol_submatrix_equiv` / 定理 `updateCol_submatrix_equiv`

English:
theorem updateCol_submatrix_equiv
  statement: [DecidableEq o] [DecidableEq n] (A : Matrix m n α) (j : o)
  proof: by
  simpa only [← transpose_submatrix, updateRow_transpose] using!
    congr_arg transpose (updateRow_submatrix_equiv Aᵀ j c f e)

中文:
定理 updateCol_submatrix_equiv
  结论: [DecidableEq o] [DecidableEq n] (A : 矩阵 m n α) (j : o)
  证明: by
  simpa only [← transpose_submatrix, updateRow_transpose] using!
    congr_arg transpose (updateRow_submatrix_equiv Aᵀ j c f e)

Depends on / 依赖: congr_arg, transpose, transpose_submatrix, updateRow_submatrix_equiv, updateRow_transpose
-/
theorem updateCol_submatrix_equiv [DecidableEq o] [DecidableEq n] (A : Matrix m n α) (j : o)
    (c : l -> α) (e : l ≃ m) (f : o ≃ n) : updateCol (A.submatrix e f) j c =
    (A.updateCol (f j) fun i => c (e.symm i)).submatrix e f := by
  simpa only [← transpose_submatrix, updateRow_transpose] using!
    congr_arg transpose (updateRow_submatrix_equiv Aᵀ j c f e)

/--
theorem `submatrix_updateCol_equiv` / 定理 `submatrix_updateCol_equiv`

English:
theorem submatrix_updateCol_equiv
  statement: [DecidableEq o] [DecidableEq n] (A : Matrix m n α) (j : n)
  proof: Eq.trans (by simp_rw [Equiv.apply_symm_apply]) (updateCol_submatrix_equiv A _ _ e f).symm

中文:
定理 submatrix_updateCol_equiv
  结论: [DecidableEq o] [DecidableEq n] (A : 矩阵 m n α) (j : n)
  证明: Eq.trans (by simp_rw [Equiv.apply_symm_apply]) (updateCol_submatrix_equiv A _ _ e f).symm

Depends on / 依赖: Eq.trans, Equiv.apply_symm_apply, apply_symm_apply, simp_rw, updateCol_submatrix_equiv
-/
theorem submatrix_updateCol_equiv [DecidableEq o] [DecidableEq n] (A : Matrix m n α) (j : n)
    (c : m -> α) (e : l ≃ m) (f : o ≃ n) : (A.updateCol j c).submatrix e f =
    updateCol (A.submatrix e f) (f.symm j) fun i => c (e i) :=
  Eq.trans (by simp_rw [Equiv.apply_symm_apply]) (updateCol_submatrix_equiv A _ _ e f).symm



/--
theorem `updateRow_reindex` / 定理 `updateRow_reindex`

English:
theorem updateRow_reindex
  statement: [DecidableEq l] [DecidableEq m] (A : Matrix m n α) (i : l) (r : o -> α)
  proof: updateRow_submatrix_equiv _ _ _ _ _

中文:
定理 updateRow_reindex
  结论: [DecidableEq l] [DecidableEq m] (A : 矩阵 m n α) (i : l) (r : o -> α)
  证明: updateRow_submatrix_equiv _ _ _ _ _

Depends on / 依赖: updateRow_submatrix_equiv
-/
theorem updateRow_reindex [DecidableEq l] [DecidableEq m] (A : Matrix m n α) (i : l) (r : o -> α)
    (e : m ≃ l) (f : n ≃ o) :
    updateRow (reindex e f A) i r = reindex e f (A.updateRow (e.symm i) fun j => r (f j)) :=
  updateRow_submatrix_equiv _ _ _ _ _

/--
theorem `reindex_updateRow` / 定理 `reindex_updateRow`

English:
theorem reindex_updateRow
  statement: [DecidableEq l] [DecidableEq m] (A : Matrix m n α) (i : m) (r : n -> α)
  proof: submatrix_updateRow_equiv _ _ _ _ _

中文:
定理 reindex_updateRow
  结论: [DecidableEq l] [DecidableEq m] (A : 矩阵 m n α) (i : m) (r : n -> α)
  证明: submatrix_updateRow_equiv _ _ _ _ _

Depends on / 依赖: submatrix_updateRow_equiv
-/
theorem reindex_updateRow [DecidableEq l] [DecidableEq m] (A : Matrix m n α) (i : m) (r : n -> α)
    (e : m ≃ l) (f : n ≃ o) :
    reindex e f (A.updateRow i r) = updateRow (reindex e f A) (e i) fun i => r (f.symm i) :=
  submatrix_updateRow_equiv _ _ _ _ _

/--
theorem `updateCol_reindex` / 定理 `updateCol_reindex`

English:
theorem updateCol_reindex
  statement: [DecidableEq o] [DecidableEq n] (A : Matrix m n α) (j : o) (c : l -> α)
  proof: updateCol_submatrix_equiv _ _ _ _ _

中文:
定理 updateCol_reindex
  结论: [DecidableEq o] [DecidableEq n] (A : 矩阵 m n α) (j : o) (c : l -> α)
  证明: updateCol_submatrix_equiv _ _ _ _ _

Depends on / 依赖: updateCol_submatrix_equiv
-/
theorem updateCol_reindex [DecidableEq o] [DecidableEq n] (A : Matrix m n α) (j : o) (c : l -> α)
    (e : m ≃ l) (f : n ≃ o) :
    updateCol (reindex e f A) j c = reindex e f (A.updateCol (f.symm j) fun i => c (e i)) :=
  updateCol_submatrix_equiv _ _ _ _ _

/--
theorem `reindex_updateCol` / 定理 `reindex_updateCol`

English:
theorem reindex_updateCol
  statement: [DecidableEq o] [DecidableEq n] (A : Matrix m n α) (j : n) (c : m -> α)
  proof: submatrix_updateCol_equiv _ _ _ _ _

中文:
定理 reindex_updateCol
  结论: [DecidableEq o] [DecidableEq n] (A : 矩阵 m n α) (j : n) (c : m -> α)
  证明: submatrix_updateCol_equiv _ _ _ _ _

Depends on / 依赖: submatrix_updateCol_equiv
-/
theorem reindex_updateCol [DecidableEq o] [DecidableEq n] (A : Matrix m n α) (j : n) (c : m -> α)
    (e : m ≃ l) (f : n ≃ o) :
    reindex e f (A.updateCol j c) = updateCol (reindex e f A) (f j) fun i => c (e.symm i) :=
  submatrix_updateCol_equiv _ _ _ _ _

/--
theorem `single_eq_updateRow_zero` / 定理 `single_eq_updateRow_zero`

English:
theorem single_eq_updateRow_zero
  given: [DecidableEq m] [DecidableEq n] [Zero α] (i : m) (j : n) (r : α)
  proof: single_eq_of_single_single _ _ _

中文:
定理 single_eq_updateRow_zero
  条件: [DecidableEq m] [DecidableEq n] [零 α] (i : m) (j : n) (r : α)
  证明: single_eq_of_single_single _ _ _

Depends on / 依赖: single_eq_of_single_single
-/
theorem single_eq_updateRow_zero [DecidableEq m] [DecidableEq n] [Zero α] (i : m) (j : n) (r : α) :
    single i j r = updateRow 0 i (Pi.single j r) :=
  single_eq_of_single_single _ _ _

/--
theorem `single_eq_updateCol_zero` / 定理 `single_eq_updateCol_zero`

English:
theorem single_eq_updateCol_zero
  given: [DecidableEq m] [DecidableEq n] [Zero α] (i : m) (j : n) (r : α)
  proof: by
  simpa [← updateCol_transpose] using congr($(single_eq_updateRow_zero j i r)ᵀ)

中文:
定理 single_eq_updateCol_zero
  条件: [DecidableEq m] [DecidableEq n] [零 α] (i : m) (j : n) (r : α)
  证明: by
  simpa [← updateCol_transpose] using congr($(single_eq_updateRow_zero j i r)ᵀ)

Depends on / 依赖: single_eq_updateRow_zero, updateCol_transpose
-/
theorem single_eq_updateCol_zero [DecidableEq m] [DecidableEq n] [Zero α] (i : m) (j : n) (r : α) :
    single i j r = updateCol 0 j (Pi.single i r) := by
  simpa [← updateCol_transpose] using congr($(single_eq_updateRow_zero j i r)ᵀ)

section mul

/--
theorem `updateRow_mulVec` / 定理 `updateRow_mulVec`

English:
theorem updateRow_mulVec
  statement: [DecidableEq l] [Fintype m] [NonUnitalNonAssocSemiring α]
  proof: by
  ext i'
  obtain rfl | hi := eq_or_ne i' i
  · simp [mulVec]
  · simp [mulVec, hi]

中文:
定理 updateRow_mulVec
  结论: [DecidableEq l] [有限类型 m] [非幺非结合半环 α]
  证明: by
  ext i'
  obtain rfl | hi := eq_or_ne i' i
  · simp [mulVec]
  · simp [mulVec, hi]

Depends on / 依赖: eq_or_ne, mulVec
-/
theorem updateRow_mulVec [DecidableEq l] [Fintype m] [NonUnitalNonAssocSemiring α]
    (A : Matrix l m α) (i : l) (c : m -> α) (v : m -> α) :
    A.updateRow i c *ᵥ v = Function.update (A *ᵥ v) i (c ⬝ᵥ v) := by
  ext i'
  obtain rfl | hi := eq_or_ne i' i
  · simp [mulVec]
  · simp [mulVec, hi]

/--
theorem `vecMul_updateCol` / 定理 `vecMul_updateCol`

English:
theorem vecMul_updateCol
  statement: [DecidableEq n] [Fintype m] [NonUnitalNonAssocSemiring α]
  proof: by
  ext j'
  obtain rfl | hj := eq_or_ne j' j
  · simp [vecMul]
  · simp [vecMul, hj]

中文:
定理 vecMul_updateCol
  结论: [DecidableEq n] [有限类型 m] [非幺非结合半环 α]
  证明: by
  ext j'
  obtain rfl | hj := eq_or_ne j' j
  · simp [vecMul]
  · simp [vecMul, hj]

Depends on / 依赖: eq_or_ne, vecMul
-/
theorem vecMul_updateCol [DecidableEq n] [Fintype m] [NonUnitalNonAssocSemiring α]
    (v : m -> α) (B : Matrix m n α) (j : n) (r : m -> α) :
    v ᵥ* B.updateCol j r = Function.update (v ᵥ* B) j (v ⬝ᵥ r) := by
  ext j'
  obtain rfl | hj := eq_or_ne j' j
  · simp [vecMul]
  · simp [vecMul, hj]

/--
theorem `update_vecMulVec` / 定理 `update_vecMulVec`

English:
theorem update_vecMulVec
  given: [DecidableEq m] [Mul α] (u : m -> α) (v : n -> α) (i : m) (a : α)
  proof: by
  ext i' j
  obtain rfl | hi := eq_or_ne i' i
  · simp [vecMulVec_apply]
  · simp [vecMulVec_apply, hi]

中文:
定理 update_vecMulVec
  条件: [DecidableEq m] [乘法 α] (u : m -> α) (v : n -> α) (i : m) (a : α)
  证明: by
  ext i' j
  obtain rfl | hi := eq_or_ne i' i
  · simp [vecMulVec_apply]
  · simp [vecMulVec_apply, hi]

Depends on / 依赖: eq_or_ne, vecMulVec_apply
-/
theorem update_vecMulVec [DecidableEq m] [Mul α] (u : m -> α) (v : n -> α) (i : m) (a : α) :
    vecMulVec (Function.update u i a) v = (vecMulVec u v).updateRow i (a • v) := by
  ext i' j
  obtain rfl | hi := eq_or_ne i' i
  · simp [vecMulVec_apply]
  · simp [vecMulVec_apply, hi]

/--
theorem `vecMulVec_update` / 定理 `vecMulVec_update`

English:
theorem vecMulVec_update
  given: [DecidableEq n] [Mul α] (u : m -> α) (v : n -> α) (j : n) (a : α)
  proof: by
  ext i j'
  obtain rfl | hi := eq_or_ne j' j
  · simp [vecMulVec_apply]
  · simp [vecMulVec_apply, hi]

中文:
定理 vecMulVec_update
  条件: [DecidableEq n] [乘法 α] (u : m -> α) (v : n -> α) (j : n) (a : α)
  证明: by
  ext i j'
  obtain rfl | hi := eq_or_ne j' j
  · simp [vecMulVec_apply]
  · simp [vecMulVec_apply, hi]

Depends on / 依赖: eq_or_ne, vecMulVec_apply
-/
theorem vecMulVec_update [DecidableEq n] [Mul α] (u : m -> α) (v : n -> α) (j : n) (a : α) :
    vecMulVec u (Function.update v j a) = (vecMulVec u v).updateCol j (MulOpposite.op a • u) := by
  ext i j'
  obtain rfl | hi := eq_or_ne j' j
  · simp [vecMulVec_apply]
  · simp [vecMulVec_apply, hi]

/--
theorem `updateRow_mul` / 定理 `updateRow_mul`

English:
theorem updateRow_mul
  statement: [DecidableEq l] [Fintype m] [NonUnitalNonAssocSemiring α]
  proof: by
  ext i' j'
  obtain rfl | hi := eq_or_ne i' i
  · simp [mul_apply, vecMul, dotProduct]
  · simp [mul_apply, hi]

中文:
定理 updateRow_mul
  结论: [DecidableEq l] [有限类型 m] [非幺非结合半环 α]
  证明: by
  ext i' j'
  obtain rfl | hi := eq_or_ne i' i
  · simp [mul_apply, vecMul, dotProduct]
  · simp [mul_apply, hi]

Depends on / 依赖: dotProduct, eq_or_ne, mul_apply, vecMul
-/
theorem updateRow_mul [DecidableEq l] [Fintype m] [NonUnitalNonAssocSemiring α]
    (A : Matrix l m α) (i : l) (r : m -> α) (B : Matrix m n α) :
    A.updateRow i r * B = (A * B).updateRow i (r ᵥ* B) := by
  ext i' j'
  obtain rfl | hi := eq_or_ne i' i
  · simp [mul_apply, vecMul, dotProduct]
  · simp [mul_apply, hi]

/--
theorem `mul_updateCol` / 定理 `mul_updateCol`

English:
theorem mul_updateCol
  statement: [DecidableEq n] [Fintype m] [NonUnitalNonAssocSemiring α]
  proof: by
  ext i' j'
  obtain rfl | hj := eq_or_ne j' j
  · simp [mul_apply, mulVec, dotProduct]
  · simp [mul_apply, hj]

中文:
定理 mul_updateCol
  结论: [DecidableEq n] [有限类型 m] [非幺非结合半环 α]
  证明: by
  ext i' j'
  obtain rfl | hj := eq_or_ne j' j
  · simp [mul_apply, mulVec, dotProduct]
  · simp [mul_apply, hj]

Depends on / 依赖: dotProduct, eq_or_ne, mulVec, mul_apply
-/
theorem mul_updateCol [DecidableEq n] [Fintype m] [NonUnitalNonAssocSemiring α]
    (A : Matrix l m α) (B : Matrix m n α) (j : n) (c : m -> α) :
    A * B.updateCol j c = (A * B).updateCol j (A *ᵥ c) := by
  ext i' j'
  obtain rfl | hj := eq_or_ne j' j
  · simp [mul_apply, mulVec, dotProduct]
  · simp [mul_apply, hj]

open RightActions in
/--
theorem `mul_single_eq_updateCol_zero` / 定理 `mul_single_eq_updateCol_zero`

English:
theorem mul_single_eq_updateCol_zero
  proof: by
  rw [single_eq_updateCol_zero]; rw [mul_updateCol]; rw [Matrix.mul_zero]; rw [mulVec_single]

中文:
定理 mul_single_eq_updateCol_zero
  证明: by
  rw [single_eq_updateCol_zero]; rw [mul_updateCol]; rw [Matrix.mul_zero]; rw [mulVec_single]

Depends on / 依赖: Matrix, Matrix.mul_zero, mulVec_single, mul_updateCol, mul_zero, single_eq_updateCol_zero
-/
theorem mul_single_eq_updateCol_zero
    [DecidableEq m] [DecidableEq n] [Fintype m] [NonUnitalNonAssocSemiring α]
    (A : Matrix l m α) (i : m) (j : n) (r : α) :
    A * single i j r = updateCol 0 j (A.col i <• r) := by
  rw [single_eq_updateCol_zero]; rw [mul_updateCol]; rw [Matrix.mul_zero]; rw [mulVec_single]

/--
theorem `single_mul_eq_updateRow_zero` / 定理 `single_mul_eq_updateRow_zero`

English:
theorem single_mul_eq_updateRow_zero
  proof: by
  rw [single_eq_updateRow_zero]; rw [updateRow_mul]; rw [Matrix.zero_mul]; rw [single_vecMul]

中文:
定理 single_mul_eq_updateRow_zero
  证明: by
  rw [single_eq_updateRow_zero]; rw [updateRow_mul]; rw [Matrix.zero_mul]; rw [single_vecMul]

Depends on / 依赖: Matrix, Matrix.zero_mul, single_eq_updateRow_zero, single_vecMul, updateRow_mul, zero_mul
-/
theorem single_mul_eq_updateRow_zero
    [DecidableEq l] [DecidableEq m] [Fintype m] [NonUnitalNonAssocSemiring α]
    (i : l) (j : m) (r : α) (B : Matrix m n α) :
    single i j r * B = updateRow 0 i (r • B.row j) := by
  rw [single_eq_updateRow_zero]; rw [updateRow_mul]; rw [Matrix.zero_mul]; rw [single_vecMul]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `updateRow_zero_mul_updateCol_zero` / 定理 `updateRow_zero_mul_updateCol_zero`

English:
theorem updateRow_zero_mul_updateCol_zero
  proof: by
  rw [updateRow_mul]; rw [vecMul_updateCol]; rw [mul_updateCol]; rw [single_eq_of_single_single]; rw [Matrix.zero_mul]; rw [vecMul_zero]; rw [zero_mulVec]; rw [updateCol_zero_zero]; rw [updateRow]; rw [← Pi.single]; rw [← Pi.single]

中文:
定理 updateRow_zero_mul_updateCol_zero
  证明: by
  rw [updateRow_mul]; rw [vecMul_updateCol]; rw [mul_updateCol]; rw [single_eq_of_single_single]; rw [Matrix.zero_mul]; rw [vecMul_zero]; rw [zero_mulVec]; rw [updateCol_zero_zero]; rw [updateRow]; rw [← Pi.single]; rw [← Pi.single]

Depends on / 依赖: Matrix, Matrix.zero_mul, Pi.single, mul_updateCol, single, single_eq_of_single_single, updateCol_zero_zero, updateRow, updateRow_mul, vecMul_updateCol, vecMul_zero, zero_mul, zero_mulVec
-/
theorem updateRow_zero_mul_updateCol_zero
    [DecidableEq l] [DecidableEq n] [Fintype m] [NonUnitalNonAssocSemiring α]
    (i : l) (r : m -> α) (j : n) (c : m -> α) :
    (0 : Matrix l m α).updateRow i r * (0 : Matrix m n α).updateCol j c = single i j (r ⬝ᵥ c) := by
  rw [updateRow_mul]; rw [vecMul_updateCol]; rw [mul_updateCol]; rw [single_eq_of_single_single]; rw [Matrix.zero_mul]; rw [vecMul_zero]; rw [zero_mulVec]; rw [updateCol_zero_zero]; rw [updateRow]; rw [← Pi.single]; rw [← Pi.single]

end mul

end Matrix
