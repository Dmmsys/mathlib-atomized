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
`Matrix.replicateCol ι u` is the matrix with all columns equal to the vector `u`.

To get a column matrix with exactly one column,
`Matrix.replicateCol (Fin 1) u` is the canonical choice.
-/
/-
**Matrix.replicateCol** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：replicateCol (ι : Type*) (w : m -> α) : Matrix m ι α
参数：ι : Type*；w : m -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.replicateCol ι u` is the matrix with all columns equal to the vector `u`
.

To get a column matrix with exactly one column,
`Matrix.replicateCol (Fin 1) u` is the canonical choice.
-/
def replicateCol (ι : Type*) (w : m → α) : Matrix m ι α :=
  of fun x _ => w x

-- TODO: set as an equation lemma for `replicateCol`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
/-
**Matrix.replicateCol_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：replicateCol_apply {ι : Type*} (w : m -> α) (i) (j : ι) : replicateCol ι w
 i j = w i
参数：w : m -> α；i；j : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem replicateCol_apply {ι : Type*} (w : m → α) (i) (j : ι) : replicateCol ι w i j = w i :=
  rfl

/--
`Matrix.replicateRow ι u` is the matrix with all rows equal to the vector `u`.

To get a row matrix with exactly one row, `Matrix.replicateRow (Fin 1) u` is the canonical choice.
-/
/-
**Matrix.replicateRow** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：replicateRow (ι : Type*) (v : n -> α) : Matrix ι n α
参数：ι : Type*；v : n -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.replicateRow ι u` is the matrix with all rows equal to the vector `u`.

To get a row matrix with exactly one row, `Matrix.replicateRow (Fin 1) u` is the
 canonical choice.
-/
def replicateRow (ι : Type*) (v : n → α) : Matrix ι n α :=
  of fun _ y => v y

variable {ι : Type*}

-- TODO: set as an equation lemma for `replicateRow`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
/-
**Matrix.replicateRow_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：replicateRow_apply (v : n -> α) (i : ι) (j) : replicateRow ι v i j = v j
参数：v : n -> α；i : ι；j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem replicateRow_apply (v : n → α) (i : ι) (j) : replicateRow ι v i j = v j :=
  rfl

@[simp]
/-
**Matrix.vecMulVec_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMulVec_one [MulOneClass R] (x : n -> R) : vecMulVec x 1 = replicateCol 
m x
参数：x : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vecMulVec_one [MulOneClass R] (x : n → R) :
    vecMulVec x 1 = replicateCol m x := by
  ext; simp [vecMulVec_apply]

@[simp]
/-
**Matrix.one_vecMulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：one_vecMulVec [MulOneClass R] (x : n -> R) : vecMulVec 1 x = replicateRow 
m x
参数：x : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem one_vecMulVec [MulOneClass R] (x : n → R) :
    vecMulVec 1 x = replicateRow m x := by
  ext; simp [vecMulVec_apply]
/-
**Matrix.replicateCol_injective** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：replicateCol_injective [Nonempty ι] : Function.Injective (replicateCol ι :
 (m -> α) -> Matrix m ι α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr_fun₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sor
t u_3} {f g : (a : α) → (b : β a) → γ a b},   f = g → ∀ (a : α) (b : β a), f a b
…
-/
theorem replicateCol_injective [Nonempty ι] :
    Function.Injective (replicateCol ι : (m → α) → Matrix m ι α) := by
  inhabit ι
  exact fun _x _y h => funext fun i => congr_fun₂ h i default
/-
**Matrix.replicateCol_inj** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {α : Type v} {ι : Type u_6} [Nonempty ι] {v w : m → α},  
 Matrix.replicateCol ι v = Matrix.replicateCol ι w ↔ v = w
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Matrix.replicateCol_injective`：replicateCol_injective [Nonempty ι] : Fun
ction.Injective (replicateCol ι : (m -> α) -> Matrix m ι α)
-/
@[simp] theorem replicateCol_inj [Nonempty ι] {v w : m → α} :
    replicateCol ι v = replicateCol ι w ↔ v = w :=
  replicateCol_injective.eq_iff
/-
**Matrix.replicateCol_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {α : Type v} {ι : Type u_6} [inst : Zero α], Matrix.repli
cateCol ι 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem replicateCol_zero [Zero α] : replicateCol ι (0 : m → α) = 0 := rfl
/-
**Matrix.replicateCol_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {α : Type v} {ι : Type u_6} [inst : Zero α] [Nonempty ι] 
(v : m → α),   Matrix.replicateCol ι v = 0 ↔ v = 0
参数：v : m → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.replicateCol_inj`：∀ {m : Type u_2} {α : Type v} {ι : Type u_6} [N
onempty ι] {v w : m → α},   Matrix.replicateCol ι v = Matrix.replicateCol ι w ↔ 
v = w
-/
@[simp] theorem replicateCol_eq_zero [Zero α] [Nonempty ι] (v : m → α) :
    replicateCol ι v = 0 ↔ v = 0 :=
  replicateCol_inj

@[simp]
/-
**Matrix.replicateCol_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：replicateCol_add [Add α] (v w : m -> α) : replicateCol ι (v + w) = replica
teCol ι v + replicateCol ι w
参数：v w : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem replicateCol_add [Add α] (v w : m → α) :
    replicateCol ι (v + w) = replicateCol ι v + replicateCol ι w := by
  ext
  rfl

@[simp]
/-
**Matrix.replicateCol_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：replicateCol_smul [SMul R α] (x : R) (v : m -> α) : replicateCol ι (x • v)
 = x • replicateCol ι v
参数：x : R；v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem replicateCol_smul [SMul R α] (x : R) (v : m → α) :
    replicateCol ι (x • v) = x • replicateCol ι v := by
  ext
  rfl
/-
**Matrix.replicateRow_injective** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：replicateRow_injective [Nonempty ι] : Function.Injective (replicateRow ι :
 (n -> α) -> Matrix ι n α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr_fun₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sor
t u_3} {f g : (a : α) → (b : β a) → γ a b},   f = g → ∀ (a : α) (b : β a), f a b
…
-/
theorem replicateRow_injective [Nonempty ι] :
    Function.Injective (replicateRow ι : (n → α) → Matrix ι n α) := by
  inhabit ι
  exact fun _x _y h => funext fun j => congr_fun₂ h default j
/-
**Matrix.replicateRow_inj** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_3} {α : Type v} {ι : Type u_6} [Nonempty ι] {v w : n → α},  
 Matrix.replicateRow ι v = Matrix.replicateRow ι w ↔ v = w
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Matrix.replicateRow_injective`：replicateRow_injective [Nonempty ι] : Fun
ction.Injective (replicateRow ι : (n -> α) -> Matrix ι n α)
-/
@[simp] theorem replicateRow_inj [Nonempty ι] {v w : n → α} :
    replicateRow ι v = replicateRow ι w ↔ v = w :=
  replicateRow_injective.eq_iff
/-
**Matrix.replicateRow_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_3} {α : Type v} {ι : Type u_6} [inst : Zero α], Matrix.repli
cateRow ι 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem replicateRow_zero [Zero α] : replicateRow ι (0 : n → α) = 0 := rfl
/-
**Matrix.replicateRow_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_3} {α : Type v} {ι : Type u_6} [inst : Zero α] [Nonempty ι] 
(v : n → α),   Matrix.replicateRow ι v = 0 ↔ v = 0
参数：v : n → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.replicateRow_inj`：∀ {n : Type u_3} {α : Type v} {ι : Type u_6} [N
onempty ι] {v w : n → α},   Matrix.replicateRow ι v = Matrix.replicateRow ι w ↔ 
v = w
-/
@[simp] theorem replicateRow_eq_zero [Zero α] [Nonempty ι] (v : n → α) :
    replicateRow ι v = 0 ↔ v = 0 :=
  replicateRow_inj

@[simp]
/-
**Matrix.replicateRow_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：replicateRow_add [Add α] (v w : m -> α) : replicateRow ι (v + w) = replica
teRow ι v + replicateRow ι w
参数：v w : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem replicateRow_add [Add α] (v w : m → α) :
    replicateRow ι (v + w) = replicateRow ι v + replicateRow ι w := by
  ext
  rfl

@[simp]
/-
**Matrix.replicateRow_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：replicateRow_smul [SMul R α] (x : R) (v : m -> α) : replicateRow ι (x • v)
 = x • replicateRow ι v
参数：x : R；v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem replicateRow_smul [SMul R α] (x : R) (v : m → α) :
    replicateRow ι (x • v) = x • replicateRow ι v := by
  ext
  rfl

@[simp]
/-
**Matrix.transpose_replicateCol** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_replicateCol (v : m -> α) : (replicateCol ι v)ᵀ = replicateRow ι
 v
参数：v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem transpose_replicateCol (v : m → α) : (replicateCol ι v)ᵀ = replicateRow ι v := by
  ext
  rfl

@[simp]
/-
**Matrix.transpose_replicateRow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_replicateRow (v : m -> α) : (replicateRow ι v)ᵀ = replicateCol ι
 v
参数：v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem transpose_replicateRow (v : m → α) : (replicateRow ι v)ᵀ = replicateCol ι v := by
  ext
  rfl

@[simp]
/-
**Matrix.conjTranspose_replicateCol** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_replicateCol [Star α] (v : m -> α) : (replicateCol ι v)ᴴ = r
eplicateRow ι (star v)
参数：v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem conjTranspose_replicateCol [Star α] (v : m → α) :
    (replicateCol ι v)ᴴ = replicateRow ι (star v) := by
  ext
  rfl

@[simp]
/-
**Matrix.conjTranspose_replicateRow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_replicateRow [Star α] (v : m -> α) : (replicateRow ι v)ᴴ = r
eplicateCol ι (star v)
参数：v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem conjTranspose_replicateRow [Star α] (v : m → α) :
    (replicateRow ι v)ᴴ = replicateCol ι (star v) := by
  ext
  rfl

/-- `v ᵥ* M` is the vector whose entries are those of `replicateRow ι v * M`. -/
/-
**Matrix.replicateRow_vecMul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：replicateRow_vecMul [Fintype m] [NonUnitalNonAssocSemiring α] (M : Matrix 
m n α) (v : m -> α) : replicateRow ι (v ᵥ* M) = replicateRow ι v * M
参数：M : Matrix m n α；v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N

--- 原说明 ---
`v ᵥ* M` is the vector whose entries are those of `replicateRow ι v * M`.
-/
theorem replicateRow_vecMul [Fintype m] [NonUnitalNonAssocSemiring α] (M : Matrix m n α)
    (v : m → α) : replicateRow ι (v ᵥ* M) = replicateRow ι v * M := by
  ext
  rfl
/-
**Matrix.replicateCol_vecMul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：replicateCol_vecMul [Fintype m] [NonUnitalNonAssocSemiring α] (M : Matrix 
m n α) (v : m -> α) : replicateCol ι (v ᵥ* M) = (replicateRow ι v * M)ᵀ
参数：M : Matrix m n α；v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem replicateCol_vecMul [Fintype m] [NonUnitalNonAssocSemiring α] (M : Matrix m n α)
    (v : m → α) : replicateCol ι (v ᵥ* M) = (replicateRow ι v * M)ᵀ := by
  ext
  rfl

/-- `M *ᵥ v` is the vector whose entries are those of `M * replicateCol ι v`. -/
/-
**Matrix.replicateCol_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：replicateCol_mulVec [Fintype n] [NonUnitalNonAssocSemiring α] (M : Matrix 
m n α) (v : n -> α) : replicateCol ι (M *ᵥ v) = M * replicateCol ι v
参数：M : Matrix m n α；v : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N

--- 原说明 ---
`M *ᵥ v` is the vector whose entries are those of `M * replicateCol ι v`.
-/
theorem replicateCol_mulVec [Fintype n] [NonUnitalNonAssocSemiring α] (M : Matrix m n α)
    (v : n → α) : replicateCol ι (M *ᵥ v) = M * replicateCol ι v := by
  ext
  rfl
/-
**Matrix.replicateRow_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：replicateRow_mulVec [Fintype n] [NonUnitalNonAssocSemiring α] (M : Matrix 
m n α) (v : n -> α) : replicateRow ι (M *ᵥ v) = (M * replicateCol ι v)ᵀ
参数：M : Matrix m n α；v : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem replicateRow_mulVec [Fintype n] [NonUnitalNonAssocSemiring α] (M : Matrix m n α)
    (v : n → α) : replicateRow ι (M *ᵥ v) = (M * replicateCol ι v)ᵀ := by
  ext
  rfl
/-
**Matrix.replicateRow_mulVec_eq_const** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：replicateRow_mulVec_eq_const [Fintype m] [NonUnitalNonAssocSemiring α] (v 
w : m -> α) : replicateRow ι v *ᵥ w = Function.const _ (v ⬝ᵥ w)
参数：v w : m -> α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem replicateRow_mulVec_eq_const [Fintype m] [NonUnitalNonAssocSemiring α] (v w : m → α) :
    replicateRow ι v *ᵥ w = Function.const _ (v ⬝ᵥ w) := rfl
/-
**Matrix.mulVec_replicateCol_eq_const** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mulVec_replicateCol_eq_const [Fintype m] [NonUnitalNonAssocSemiring α] (v 
w : m -> α) : v ᵥ* replicateCol ι w = Function.const _ (v ⬝ᵥ w)
参数：v w : m -> α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulVec_replicateCol_eq_const [Fintype m] [NonUnitalNonAssocSemiring α] (v w : m → α) :
    v ᵥ* replicateCol ι w = Function.const _ (v ⬝ᵥ w) := rfl
/-
**Matrix.replicateRow_mul_replicateCol** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：replicateRow_mul_replicateCol [Fintype m] [Mul α] [AddCommMonoid α] (v w :
 m -> α) : replicateRow ι v * replicateCol ι w = of fun _ _ => v ⬝ᵥ w
参数：v w : m -> α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem replicateRow_mul_replicateCol [Fintype m] [Mul α] [AddCommMonoid α] (v w : m → α) :
    replicateRow ι v * replicateCol ι w = of fun _ _ => v ⬝ᵥ w :=
  rfl

@[simp]
/-
**Matrix.replicateRow_mul_replicateCol_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：replicateRow_mul_replicateCol_apply [Fintype m] [Mul α] [AddCommMonoid α] 
(v w : m -> α) (i j) : (replicateRow ι v * replicateCol ι w) i j = v ⬝ᵥ w
参数：v w : m -> α；i j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem replicateRow_mul_replicateCol_apply [Fintype m] [Mul α] [AddCommMonoid α] (v w : m → α)
    (i j) : (replicateRow ι v * replicateCol ι w) i j = v ⬝ᵥ w :=
  rfl

@[simp]
/-
**Matrix.diag_replicateCol_mul_replicateRow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diag_replicateCol_mul_replicateRow [Mul α] [AddCommMonoid α] [Unique ι] (a
 b : n -> α) : diag (replicateCol ι a * replicateRow ι b) = a * b
参数：a b : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diag_replicateCol_mul_replicateRow [Mul α] [AddCommMonoid α] [Unique ι] (a b : n → α) :
    diag (replicateCol ι a * replicateRow ι b) = a * b := by
  ext
  simp [Matrix.mul_apply, replicateCol, replicateRow]

variable (ι)
/-
**Matrix.vecMulVec_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMulVec_eq [Mul α] [AddCommMonoid α] [Unique ι] (w : m -> α) (v : n -> α
) : vecMulVec w v = replicateCol ι w * replicateRow ι v
参数：w : m -> α；v : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vecMulVec_eq [Mul α] [AddCommMonoid α] [Unique ι] (w : m → α) (v : n → α) :
    vecMulVec w v = replicateCol ι w * replicateRow ι v := by
  ext
  simp [vecMulVec, mul_apply]

/-! ### Updating rows and columns -/

/-- Update, i.e. replace the `i`th row of matrix `A` with the values in `b`. -/
/-
**Matrix.updateRow** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：updateRow [DecidableEq m] (M : Matrix m n α) (i : m) (b : n -> α) : Matrix
 m n α
参数：M : Matrix m n α；i : m；b : n -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Update, i.e. replace the `i`th row of matrix `A` with the values in `b`.
-/
def updateRow [DecidableEq m] (M : Matrix m n α) (i : m) (b : n → α) : Matrix m n α :=
  of <| Function.update M i b

/-- Update, i.e. replace the `j`th column of matrix `A` with the values in `b`. -/
/-
**Matrix.updateCol** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：updateCol [DecidableEq n] (M : Matrix m n α) (j : n) (b : m -> α) : Matrix
 m n α
参数：M : Matrix m n α；j : n；b : m -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Update, i.e. replace the `j`th column of matrix `A` with the values in `b`.
-/
def updateCol [DecidableEq n] (M : Matrix m n α) (j : n) (b : m → α) : Matrix m n α :=
  of fun i => Function.update (M i) j (b i)

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

@[simp]
/-
**Matrix.updateRow_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：updateRow_self [DecidableEq m] : updateRow M i b i = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
-/
theorem updateRow_self [DecidableEq m] : updateRow M i b i = b :=
  Function.update_self (β := fun _ => (n → α)) i b M

@[simp]
/-
**Matrix.updateCol_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：updateCol_self [DecidableEq n] : updateCol M j c i j = c i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
-/
theorem updateCol_self [DecidableEq n] : updateCol M j c i j = c i :=
  Function.update_self (β := fun _ => α) j (c i) (M i)

@[simp]
/-
**Matrix.updateRow_ne** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：updateRow_ne [DecidableEq m] {i' : m} (i_ne : i' != i) : updateRow M i b i
' = M i'
参数：i_ne : i' != i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
-/
theorem updateRow_ne [DecidableEq m] {i' : m} (i_ne : i' ≠ i) : updateRow M i b i' = M i' :=
  Function.update_of_ne (β := fun _ => (n → α)) i_ne b M

@[simp]
/-
**Matrix.updateCol_ne** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：updateCol_ne [DecidableEq n] {j' : n} (j_ne : j' != j) : updateCol M j c i
 j' = M i j'
参数：j_ne : j' != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
-/
theorem updateCol_ne [DecidableEq n] {j' : n} (j_ne : j' ≠ j) :
    updateCol M j c i j' = M i j' :=
  Function.update_of_ne (β := fun _ => α) j_ne (c i) (M i)
/-
**Matrix.updateRow_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：updateRow_apply [DecidableEq m] {i' : m} : updateRow M i b i' j = if i' = 
i then b j else M i' j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.updateRow_self`：updateRow_self [DecidableEq m] : updateRow M i b 
i = b
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Matrix.updateRow_ne`：updateRow_ne [DecidableEq m] {i' : m} (i_ne : i' !=
 i) : updateRow M i b i' = M i'
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem updateRow_apply [DecidableEq m] {i' : m} :
    updateRow M i b i' j = if i' = i then b j else M i' j := by
  by_cases h : i' = i
  · rw [h, updateRow_self, if_pos rfl]
  · rw [updateRow_ne h, if_neg h]
/-
**Matrix.updateCol_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：updateCol_apply [DecidableEq n] {j' : n} : updateCol M j c i j' = if j' = 
j then c i else M i j'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.updateCol_self`：updateCol_self [DecidableEq n] : updateCol M j c 
i j = c i
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Matrix.updateCol_ne`：updateCol_ne [DecidableEq n] {j' : n} (j_ne : j' !=
 j) : updateCol M j c i j' = M i j'
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem updateCol_apply [DecidableEq n] {j' : n} :
    updateCol M j c i j' = if j' = j then c i else M i j' := by
  by_cases h : j' = j
  · rw [h, updateCol_self, if_pos rfl]
  · rw [updateCol_ne h, if_neg h]

@[simp]
/-
**Matrix.updateCol_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：updateCol_subsingleton [Subsingleton n] (A : Matrix m n R) (i : n) (b : m 
-> R) : A.updateCol i b = (replicateCol (Fin 1) b).submatrix id (Function.const 
n 0)
参数：A : Matrix m n R；i : n；b : m -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.updateCol.congr_simp`：∀ {m : Type u_2} {n : Type u_3} {α : Type v
} {inst : DecidableEq n} [inst_1 : DecidableEq n] (M M_1 : Matrix m n α),   M = 
M_1 →     ∀ (j j_…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Matrix.updateCol_self`：updateCol_self [DecidableEq n] : updateCol M j c 
i j = c i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem updateCol_subsingleton [Subsingleton n] (A : Matrix m n R) (i : n) (b : m → R) :
    A.updateCol i b = (replicateCol (Fin 1) b).submatrix id (Function.const n 0) := by
  ext x y
  simp [Subsingleton.elim i y]

@[simp]
/-
**Matrix.updateRow_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：updateRow_subsingleton [Subsingleton m] (A : Matrix m n R) (i : m) (b : n 
-> R) : A.updateRow i b = (replicateRow (Fin 1) b).submatrix (Function.const m 0
) id
参数：A : Matrix m n R；i : m；b : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.updateRow.congr_simp`：∀ {m : Type u_2} {n : Type u_3} {α : Type v
} {inst : DecidableEq m} [inst_1 : DecidableEq m] (M M_1 : Matrix m n α),   M = 
M_1 →     ∀ (i i_…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.updateRow_self`：updateRow_self [DecidableEq m] : updateRow M i b 
i = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem updateRow_subsingleton [Subsingleton m] (A : Matrix m n R) (i : m) (b : n → R) :
    A.updateRow i b = (replicateRow (Fin 1) b).submatrix (Function.const m 0) id := by
  ext x y
  simp [Subsingleton.elim i x]
/-
**Matrix.map_updateRow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：map_updateRow [DecidableEq m] (f : α -> β) : map (updateRow M i b) f = upd
ateRow (M.map f) i (f ∘ b)
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.updateRow_apply`：updateRow_apply [DecidableEq m] {i' : m} : updat
eRow M i b i' j = if i' = i then b j else M i' j
· 使用定理 `Matrix.map_apply`：map_apply {M : Matrix m n α} {f : α -> β} {i : m} {j :
 n} : M.map f i j = f (M i j)
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
-/
theorem map_updateRow [DecidableEq m] (f : α → β) :
    map (updateRow M i b) f = updateRow (M.map f) i (f ∘ b) := by
  ext
  rw [updateRow_apply, map_apply, map_apply, updateRow_apply]
  exact apply_ite f _ _ _
/-
**Matrix.map_updateCol** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：map_updateCol [DecidableEq n] (f : α -> β) : map (updateCol M j c) f = upd
ateCol (M.map f) j (f ∘ c)
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.updateCol_apply`：updateCol_apply [DecidableEq n] {j' : n} : updat
eCol M j c i j' = if j' = j then c i else M i j'
· 使用定理 `Matrix.map_apply`：map_apply {M : Matrix m n α} {f : α -> β} {i : m} {j :
 n} : M.map f i j = f (M i j)
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
-/
theorem map_updateCol [DecidableEq n] (f : α → β) :
    map (updateCol M j c) f = updateCol (M.map f) j (f ∘ c) := by
  ext
  rw [updateCol_apply, map_apply, map_apply, updateCol_apply]
  exact apply_ite f _ _ _
/-
**Matrix.updateRow_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：updateRow_transpose [DecidableEq n] : updateRow Mᵀ j c = (updateCol M j c)
ᵀ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.transpose_apply`：transpose_apply (M : Matrix m n α) (i j) : trans
pose M i j = M j i
· 使用定理 `Matrix.updateRow_apply`：updateRow_apply [DecidableEq m] {i' : m} : updat
eRow M i b i' j = if i' = i then b j else M i' j
· 使用定理 `Matrix.updateCol_apply`：updateCol_apply [DecidableEq n] {j' : n} : updat
eCol M j c i j' = if j' = j then c i else M i j'
-/
theorem updateRow_transpose [DecidableEq n] : updateRow Mᵀ j c = (updateCol M j c)ᵀ := by
  ext
  rw [transpose_apply, updateRow_apply, updateCol_apply]
  rfl
/-
**Matrix.updateCol_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：updateCol_transpose [DecidableEq m] : updateCol Mᵀ i b = (updateRow M i b)
ᵀ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.transpose_apply`：transpose_apply (M : Matrix m n α) (i j) : trans
pose M i j = M j i
· 使用定理 `Matrix.updateRow_apply`：updateRow_apply [DecidableEq m] {i' : m} : updat
eRow M i b i' j = if i' = i then b j else M i' j
· 使用定理 `Matrix.updateCol_apply`：updateCol_apply [DecidableEq n] {j' : n} : updat
eCol M j c i j' = if j' = j then c i else M i j'
-/
theorem updateCol_transpose [DecidableEq m] : updateCol Mᵀ i b = (updateRow M i b)ᵀ := by
  ext
  rw [transpose_apply, updateRow_apply, updateCol_apply]
  rfl
/-
**Matrix.updateRow_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：updateRow_conjTranspose [DecidableEq n] [Star α] : updateRow Mᴴ j (star c)
 = (updateCol M j c)ᴴ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.conjTranspose.eq_1`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} 
[inst : Star α] (M : Matrix m n α), M.conjTranspose = M.transpose.map star
· 使用定理 `Matrix.transpose_map`：transpose_map {f : α -> β} {M : Matrix m n α} : Mᵀ
.map f = (M.map f)ᵀ
· 使用定理 `Matrix.updateRow_transpose`：updateRow_transpose [DecidableEq n] : update
Row Mᵀ j c = (updateCol M j c)ᵀ
· 使用定理 `Matrix.map_updateCol`：map_updateCol [DecidableEq n] (f : α -> β) : map (
updateCol M j c) f = updateCol (M.map f) j (f ∘ c)
-/
theorem updateRow_conjTranspose [DecidableEq n] [Star α] :
    updateRow Mᴴ j (star c) = (updateCol M j c)ᴴ := by
  rw [conjTranspose, conjTranspose, transpose_map, transpose_map, updateRow_transpose,
    map_updateCol]
  rfl
/-
**Matrix.updateCol_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：updateCol_conjTranspose [DecidableEq m] [Star α] : updateCol Mᴴ i (star b)
 = (updateRow M i b)ᴴ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.conjTranspose.eq_1`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} 
[inst : Star α] (M : Matrix m n α), M.conjTranspose = M.transpose.map star
· 使用定理 `Matrix.transpose_map`：transpose_map {f : α -> β} {M : Matrix m n α} : Mᵀ
.map f = (M.map f)ᵀ
· 使用定理 `Matrix.updateCol_transpose`：updateCol_transpose [DecidableEq m] : update
Col Mᵀ i b = (updateRow M i b)ᵀ
· 使用定理 `Matrix.map_updateRow`：map_updateRow [DecidableEq m] (f : α -> β) : map (
updateRow M i b) f = updateRow (M.map f) i (f ∘ b)
-/
theorem updateCol_conjTranspose [DecidableEq m] [Star α] :
    updateCol Mᴴ i (star b) = (updateRow M i b)ᴴ := by
  rw [conjTranspose, conjTranspose, transpose_map, transpose_map, updateCol_transpose,
    map_updateRow]
  rfl

@[simp]
/-
**Matrix.updateRow_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：updateRow_eq_self [DecidableEq m] (A : Matrix m n α) (i : m) : A.updateRow
 i (A i) = A
参数：A : Matrix m n α；i : m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
-/
theorem updateRow_eq_self [DecidableEq m] (A : Matrix m n α) (i : m) : A.updateRow i (A i) = A :=
  Function.update_eq_self i A

@[simp]
/-
**Matrix.updateCol_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：updateCol_eq_self [DecidableEq n] (A : Matrix m n α) (i : n) : (A.updateCo
l i fun j => A j i) = A
参数：A : Matrix m n α；i : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
-/
theorem updateCol_eq_self [DecidableEq n] (A : Matrix m n α) (i : n) :
    (A.updateCol i fun j => A j i) = A :=
  funext fun j => Function.update_eq_self i (A j)

@[simp]
/-
**Matrix.updateRow_zero_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：updateRow_zero_zero [DecidableEq m] [Zero α] (i : m) : (0 : Matrix m n α).
updateRow i 0 = 0
参数：i : m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.updateRow_eq_self`：updateRow_eq_self [DecidableEq m] (A : Matrix 
m n α) (i : m) : A.updateRow i (A i) = A
-/
theorem updateRow_zero_zero [DecidableEq m] [Zero α] (i : m) :
    (0 : Matrix m n α).updateRow i 0 = 0 :=
  updateRow_eq_self _ i

@[simp]
/-
**Matrix.updateCol_zero_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：updateCol_zero_zero [DecidableEq n] [Zero α] (i : n) : (0 : Matrix m n α).
updateCol i 0 = 0
参数：i : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.updateCol_eq_self`：updateCol_eq_self [DecidableEq n] (A : Matrix 
m n α) (i : n) : (A.updateCol i fun j => A j i) = A
-/
theorem updateCol_zero_zero [DecidableEq n] [Zero α] (i : n) :
    (0 : Matrix m n α).updateCol i 0 = 0 :=
  updateCol_eq_self _ i
/-
**Matrix.diagonal_updateCol_single** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_updateCol_single [DecidableEq n] [Zero α] (v : n -> α) (i : n) (x
 : α) : (diagonal v).updateCol i (Pi.single i x) = diagonal (Function.update v i
 x)
参数：v : n -> α；i : n；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `Matrix.updateCol_self`：updateCol_self [DecidableEq n] : updateCol M j c 
i j = c i
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Matrix.updateCol_ne`：updateCol_ne [DecidableEq n] {j' : n} (j_ne : j' !=
 j) : updateCol M j c i j' = M i j'
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
-/
theorem diagonal_updateCol_single [DecidableEq n] [Zero α] (v : n → α) (i : n) (x : α) :
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
/-
**Matrix.diagonal_updateRow_single** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_updateRow_single [DecidableEq n] [Zero α] (v : n -> α) (i : n) (x
 : α) : (diagonal v).updateRow i (Pi.single i x) = diagonal (Function.update v i
 x)
参数：v : n -> α；i : n；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.diagonal_transpose`：diagonal_transpose [Zero α] (v : n -> α) : (d
iagonal v)ᵀ = diagonal v
· 使用定理 `Matrix.updateRow_transpose`：updateRow_transpose [DecidableEq n] : update
Row Mᵀ j c = (updateCol M j c)ᵀ
· 使用定理 `Matrix.diagonal_updateCol_single`：diagonal_updateCol_single [DecidableEq
 n] [Zero α] (v : n -> α) (i : n) (x : α) : (diagonal v).updateCol i (Pi.single 
i x) = diagonal (Funct…
-/
theorem diagonal_updateRow_single [DecidableEq n] [Zero α] (v : n → α) (i : n) (x : α) :
    (diagonal v).updateRow i (Pi.single i x) = diagonal (Function.update v i x) := by
  rw [← diagonal_transpose, updateRow_transpose, diagonal_updateCol_single, diagonal_transpose]

@[simp]
/-
**Matrix.updateRow_idem** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：updateRow_idem [DecidableEq m] (A : Matrix m n α) (i : m) (x y : n -> α) :
 (A.updateRow i x).updateRow i y = A.updateRow i y
参数：A : Matrix m n α；i : m；x y : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_idem`：update_idem {α} [DecidableEq α] {β : α -> Sort*} {
a : α} (v w : β a) (f : forall a, β a) : update (update f a v) a w = update f a 
w
-/
theorem updateRow_idem [DecidableEq m] (A : Matrix m n α) (i : m) (x y : n → α) :
    (A.updateRow i x).updateRow i y = A.updateRow i y := Function.update_idem _ _ _
/-
**Matrix.updateRow_comm** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：updateRow_comm [DecidableEq m] (A : Matrix m n α) {i i' : m} (h : i != i')
 (x y : n -> α) : (A.updateRow i x).updateRow i' y = (A.updateRow i' y).updateRo
w i x
参数：A : Matrix m n α；h : i != i'；x y : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_comm`：update_comm {α} [DecidableEq α] {β : α -> Sort*} {
a b : α} (h : a != b) (v : β a) (w : β b) (f : forall a, β a) : update (update f
 a v) b w …
-/
theorem updateRow_comm [DecidableEq m] (A : Matrix m n α) {i i' : m} (h : i ≠ i') (x y : n → α) :
    (A.updateRow i x).updateRow i' y = (A.updateRow i' y).updateRow i x :=
  Function.update_comm h _ _ _

@[simp]
/-
**Matrix.updateCol_idem** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：updateCol_idem [DecidableEq n] (A : Matrix m n α) (j : n) (x y : m -> α) :
 (A.updateCol j x).updateCol j y = A.updateCol j y
参数：A : Matrix m n α；j : n；x y : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.updateRow_transpose`：updateRow_transpose [DecidableEq n] : update
Row Mᵀ j c = (updateCol M j c)ᵀ
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Matrix.updateRow_idem`：updateRow_idem [DecidableEq m] (A : Matrix m n α)
 (i : m) (x y : n -> α) : (A.updateRow i x).updateRow i y = A.updateRow i y
-/
theorem updateCol_idem [DecidableEq n] (A : Matrix m n α) (j : n) (x y : m → α) :
    (A.updateCol j x).updateCol j y = A.updateCol j y := by
  simpa only [updateRow_transpose] using! congr_arg transpose <| updateRow_idem Aᵀ j x y
/-
**Matrix.updateCol_comm** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：updateCol_comm [DecidableEq n] (A : Matrix m n α) {j j' : n} (h : j != j')
 (x y : m -> α) : (A.updateCol j x).updateCol j' y = (A.updateCol j' y).updateCo
l j x
参数：A : Matrix m n α；h : j != j'；x y : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.updateRow_transpose`：updateRow_transpose [DecidableEq n] : update
Row Mᵀ j c = (updateCol M j c)ᵀ
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Matrix.updateRow_comm`：updateRow_comm [DecidableEq m] (A : Matrix m n α)
 {i i' : m} (h : i != i') (x y : n -> α) : (A.updateRow i x).updateRow i' y = (A
.updateRow …
-/
theorem updateCol_comm [DecidableEq n] (A : Matrix m n α) {j j' : n} (h : j ≠ j') (x y : m → α) :
    (A.updateCol j x).updateCol j' y = (A.updateCol j' y).updateCol j x := by
  simpa only [updateRow_transpose] using! congr_arg transpose <| updateRow_comm Aᵀ h x y

/-! Updating rows and columns commutes in the obvious way with reindexing the matrix. -/


/-
**Matrix.updateRow_submatrix_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：updateRow_submatrix_equiv [DecidableEq l] [DecidableEq m] (A : Matrix m n 
α) (i : l) (r : o -> α) (e : l ≃ m) (f : o ≃ n) : updateRow (A.submatrix e f) i 
r = (A.updateRow (e i) fun j => r (f.symm j)).submatrix e f
参数：A : Matrix m n α；i : l；r : o -> α；e : l ≃ m；f : o ≃ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.updateRow_apply`：updateRow_apply [DecidableEq m] {i' : m} : updat
eRow M i b i' j = if i' = i then b j else M i' j
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Updating rows and columns commutes in the obvious way with reindexing the matrix
.
-/
theorem updateRow_submatrix_equiv [DecidableEq l] [DecidableEq m] (A : Matrix m n α) (i : l)
    (r : o → α) (e : l ≃ m) (f : o ≃ n) :
    updateRow (A.submatrix e f) i r = (A.updateRow (e i) fun j => r (f.symm j)).submatrix e f := by
  ext i' j
  simp only [submatrix_apply, updateRow_apply, Equiv.apply_eq_iff_eq, Equiv.symm_apply_apply]
/-
**Matrix.submatrix_updateRow_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_updateRow_equiv [DecidableEq l] [DecidableEq m] (A : Matrix m n 
α) (i : m) (r : n -> α) (e : l ≃ m) (f : o ≃ n) : (A.updateRow i r).submatrix e 
f = updateRow (A.submatrix e f) (e.symm i) fun i => r (f i)
参数：A : Matrix m n α；i : m；r : n -> α；e : l ≃ m；f : o ≃ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.updateRow_submatrix_equiv`：updateRow_submatrix_equiv [DecidableEq
 l] [DecidableEq m] (A : Matrix m n α) (i : l) (r : o -> α) (e : l ≃ m) (f : o ≃
 n) : updateRow (A.sub…
-/
theorem submatrix_updateRow_equiv [DecidableEq l] [DecidableEq m] (A : Matrix m n α) (i : m)
    (r : n → α) (e : l ≃ m) (f : o ≃ n) :
    (A.updateRow i r).submatrix e f = updateRow (A.submatrix e f) (e.symm i) fun i => r (f i) :=
  Eq.trans (by simp_rw [Equiv.apply_symm_apply]) (updateRow_submatrix_equiv A _ _ e f).symm
/-
**Matrix.updateCol_submatrix_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：updateCol_submatrix_equiv [DecidableEq o] [DecidableEq n] (A : Matrix m n 
α) (j : o) (c : l -> α) (e : l ≃ m) (f : o ≃ n) : updateCol (A.submatrix e f) j 
c = (A.updateCol (f j) fun i => c (e.symm i)).submatrix e f
参数：A : Matrix m n α；j : o；c : l -> α；e : l ≃ m；f : o ≃ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.updateRow_transpose`：updateRow_transpose [DecidableEq n] : update
Row Mᵀ j c = (updateCol M j c)ᵀ
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Matrix.updateRow_submatrix_equiv`：updateRow_submatrix_equiv [DecidableEq
 l] [DecidableEq m] (A : Matrix m n α) (i : l) (r : o -> α) (e : l ≃ m) (f : o ≃
 n) : updateRow (A.sub…
-/
theorem updateCol_submatrix_equiv [DecidableEq o] [DecidableEq n] (A : Matrix m n α) (j : o)
    (c : l → α) (e : l ≃ m) (f : o ≃ n) : updateCol (A.submatrix e f) j c =
    (A.updateCol (f j) fun i => c (e.symm i)).submatrix e f := by
  simpa only [← transpose_submatrix, updateRow_transpose] using!
    congr_arg transpose (updateRow_submatrix_equiv Aᵀ j c f e)
/-
**Matrix.submatrix_updateCol_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_updateCol_equiv [DecidableEq o] [DecidableEq n] (A : Matrix m n 
α) (j : n) (c : m -> α) (e : l ≃ m) (f : o ≃ n) : (A.updateCol j c).submatrix e 
f = updateCol (A.submatrix e f) (f.symm j) fun i => c (e i)
参数：A : Matrix m n α；j : n；c : m -> α；e : l ≃ m；f : o ≃ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.updateCol_submatrix_equiv`：updateCol_submatrix_equiv [DecidableEq
 o] [DecidableEq n] (A : Matrix m n α) (j : o) (c : l -> α) (e : l ≃ m) (f : o ≃
 n) : updateCol (A.sub…
-/
theorem submatrix_updateCol_equiv [DecidableEq o] [DecidableEq n] (A : Matrix m n α) (j : n)
    (c : m → α) (e : l ≃ m) (f : o ≃ n) : (A.updateCol j c).submatrix e f =
    updateCol (A.submatrix e f) (f.symm j) fun i => c (e i) :=
  Eq.trans (by simp_rw [Equiv.apply_symm_apply]) (updateCol_submatrix_equiv A _ _ e f).symm

/-! `reindex` versions of the above `submatrix` lemmas for convenience. -/


/-
**Matrix.updateRow_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：updateRow_reindex [DecidableEq l] [DecidableEq m] (A : Matrix m n α) (i : 
l) (r : o -> α) (e : m ≃ l) (f : n ≃ o) : updateRow (reindex e f A) i r = reinde
x e f (A.updateRow (e.symm i) fun j => r (f j))
参数：A : Matrix m n α；i : l；r : o -> α；e : m ≃ l；f : n ≃ o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.updateRow_submatrix_equiv`：updateRow_submatrix_equiv [DecidableEq
 l] [DecidableEq m] (A : Matrix m n α) (i : l) (r : o -> α) (e : l ≃ m) (f : o ≃
 n) : updateRow (A.sub…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`reindex` versions of the above `submatrix` lemmas for convenience.
-/
theorem updateRow_reindex [DecidableEq l] [DecidableEq m] (A : Matrix m n α) (i : l) (r : o → α)
    (e : m ≃ l) (f : n ≃ o) :
    updateRow (reindex e f A) i r = reindex e f (A.updateRow (e.symm i) fun j => r (f j)) :=
  updateRow_submatrix_equiv _ _ _ _ _
/-
**Matrix.reindex_updateRow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：reindex_updateRow [DecidableEq l] [DecidableEq m] (A : Matrix m n α) (i : 
m) (r : n -> α) (e : m ≃ l) (f : n ≃ o) : reindex e f (A.updateRow i r) = update
Row (reindex e f A) (e i) fun i => r (f.symm i)
参数：A : Matrix m n α；i : m；r : n -> α；e : m ≃ l；f : n ≃ o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.submatrix_updateRow_equiv`：submatrix_updateRow_equiv [DecidableEq
 l] [DecidableEq m] (A : Matrix m n α) (i : m) (r : n -> α) (e : l ≃ m) (f : o ≃
 n) : (A.updateRow i r…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem reindex_updateRow [DecidableEq l] [DecidableEq m] (A : Matrix m n α) (i : m) (r : n → α)
    (e : m ≃ l) (f : n ≃ o) :
    reindex e f (A.updateRow i r) = updateRow (reindex e f A) (e i) fun i => r (f.symm i) :=
  submatrix_updateRow_equiv _ _ _ _ _
/-
**Matrix.updateCol_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：updateCol_reindex [DecidableEq o] [DecidableEq n] (A : Matrix m n α) (j : 
o) (c : l -> α) (e : m ≃ l) (f : n ≃ o) : updateCol (reindex e f A) j c = reinde
x e f (A.updateCol (f.symm j) fun i => c (e i))
参数：A : Matrix m n α；j : o；c : l -> α；e : m ≃ l；f : n ≃ o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.updateCol_submatrix_equiv`：updateCol_submatrix_equiv [DecidableEq
 o] [DecidableEq n] (A : Matrix m n α) (j : o) (c : l -> α) (e : l ≃ m) (f : o ≃
 n) : updateCol (A.sub…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem updateCol_reindex [DecidableEq o] [DecidableEq n] (A : Matrix m n α) (j : o) (c : l → α)
    (e : m ≃ l) (f : n ≃ o) :
    updateCol (reindex e f A) j c = reindex e f (A.updateCol (f.symm j) fun i => c (e i)) :=
  updateCol_submatrix_equiv _ _ _ _ _
/-
**Matrix.reindex_updateCol** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：reindex_updateCol [DecidableEq o] [DecidableEq n] (A : Matrix m n α) (j : 
n) (c : m -> α) (e : m ≃ l) (f : n ≃ o) : reindex e f (A.updateCol j c) = update
Col (reindex e f A) (f j) fun i => c (e.symm i)
参数：A : Matrix m n α；j : n；c : m -> α；e : m ≃ l；f : n ≃ o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.submatrix_updateCol_equiv`：submatrix_updateCol_equiv [DecidableEq
 o] [DecidableEq n] (A : Matrix m n α) (j : n) (c : m -> α) (e : l ≃ m) (f : o ≃
 n) : (A.updateCol j c…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem reindex_updateCol [DecidableEq o] [DecidableEq n] (A : Matrix m n α) (j : n) (c : m → α)
    (e : m ≃ l) (f : n ≃ o) :
    reindex e f (A.updateCol j c) = updateCol (reindex e f A) (f j) fun i => c (e.symm i) :=
  submatrix_updateCol_equiv _ _ _ _ _
/-
**Matrix.single_eq_updateRow_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：single_eq_updateRow_zero [DecidableEq m] [DecidableEq n] [Zero α] (i : m) 
(j : n) (r : α) : single i j r = updateRow 0 i (Pi.single j r)
参数：i : m；j : n；r : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.single_eq_of_single_single`：single_eq_of_single_single (i : m) (j
 : n) (a : α) : single i j a = Matrix.of (Pi.single i (Pi.single j a))
-/
theorem single_eq_updateRow_zero [DecidableEq m] [DecidableEq n] [Zero α] (i : m) (j : n) (r : α) :
    single i j r = updateRow 0 i (Pi.single j r) :=
  single_eq_of_single_single _ _ _
/-
**Matrix.single_eq_updateCol_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：single_eq_updateCol_zero [DecidableEq m] [DecidableEq n] [Zero α] (i : m) 
(j : n) (r : α) : single i j r = updateCol 0 j (Pi.single i r)
参数：i : m；j : n；r : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.transpose_single`：transpose_single (i : m) (j : n) (a : α) : (sin
gle i j a)ᵀ = single j i a
· 使用定理 `Matrix.single_eq_updateRow_zero`：single_eq_updateRow_zero [DecidableEq m
] [DecidableEq n] [Zero α] (i : m) (j : n) (r : α) : single i j r = updateRow 0 
i (Pi.single j r)
-/
theorem single_eq_updateCol_zero [DecidableEq m] [DecidableEq n] [Zero α] (i : m) (j : n) (r : α) :
    single i j r = updateCol 0 j (Pi.single i r) := by
  simpa [← updateCol_transpose] using congr($(single_eq_updateRow_zero j i r)ᵀ)

section mul

/-
**Matrix.updateRow_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：updateRow_mulVec [DecidableEq l] [Fintype m] [NonUnitalNonAssocSemiring α]
 (A : Matrix l m α) (i : l) (c : m -> α) (v : m -> α) : A.updateRow i c *ᵥ v = F
unction.update (A *ᵥ v) i (c ⬝ᵥ v)
参数：A : Matrix l m α；i : l；c : m -> α；v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.updateRow_self`：updateRow_self [DecidableEq m] : updateRow M i b 
i = b
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.updateRow_ne`：updateRow_ne [DecidableEq m] {i' : m} (i_ne : i' !=
 i) : updateRow M i b i' = M i'
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
-/
theorem updateRow_mulVec [DecidableEq l] [Fintype m] [NonUnitalNonAssocSemiring α]
    (A : Matrix l m α) (i : l) (c : m → α) (v : m → α) :
    A.updateRow i c *ᵥ v = Function.update (A *ᵥ v) i (c ⬝ᵥ v) := by
  ext i'
  obtain rfl | hi := eq_or_ne i' i
  · simp [mulVec]
  · simp [mulVec, hi]
/-
**Matrix.vecMul_updateCol** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMul_updateCol [DecidableEq n] [Fintype m] [NonUnitalNonAssocSemiring α]
 (v : m -> α) (B : Matrix m n α) (j : n) (r : m -> α) : v ᵥ* B.updateCol j r = F
unction.update (v ᵥ* B) j (v ⬝ᵥ r)
参数：v : m -> α；B : Matrix m n α；j : n；r : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.updateCol_self`：updateCol_self [DecidableEq n] : updateCol M j c 
i j = c i
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.updateCol_ne`：updateCol_ne [DecidableEq n] {j' : n} (j_ne : j' !=
 j) : updateCol M j c i j' = M i j'
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
-/
theorem vecMul_updateCol [DecidableEq n] [Fintype m] [NonUnitalNonAssocSemiring α]
    (v : m → α) (B : Matrix m n α) (j : n) (r : m → α) :
    v ᵥ* B.updateCol j r = Function.update (v ᵥ* B) j (v ⬝ᵥ r) := by
  ext j'
  obtain rfl | hj := eq_or_ne j' j
  · simp [vecMul]
  · simp [vecMul, hj]
/-
**Matrix.update_vecMulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：update_vecMulVec [DecidableEq m] [Mul α] (u : m -> α) (v : n -> α) (i : m)
 (a : α) : vecMulVec (Function.update u i a) v = (vecMulVec u v).updateRow i (a 
• v)
参数：u : m -> α；v : n -> α；i : m；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.updateRow_self`：updateRow_self [DecidableEq m] : updateRow M i b 
i = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Matrix.updateRow_ne`：updateRow_ne [DecidableEq m] {i' : m} (i_ne : i' !=
 i) : updateRow M i b i' = M i'
-/
theorem update_vecMulVec [DecidableEq m] [Mul α] (u : m → α) (v : n → α) (i : m) (a : α) :
    vecMulVec (Function.update u i a) v = (vecMulVec u v).updateRow i (a • v) := by
  ext i' j
  obtain rfl | hi := eq_or_ne i' i
  · simp [vecMulVec_apply]
  · simp [vecMulVec_apply, hi]
/-
**Matrix.vecMulVec_update** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMulVec_update [DecidableEq n] [Mul α] (u : m -> α) (v : n -> α) (j : n)
 (a : α) : vecMulVec u (Function.update v j a) = (vecMulVec u v).updateCol j (Mu
lOpposite.op a • u)
参数：u : m -> α；v : n -> α；j : n；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Matrix.updateCol_self`：updateCol_self [DecidableEq n] : updateCol M j c 
i j = c i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Matrix.updateCol_ne`：updateCol_ne [DecidableEq n] {j' : n} (j_ne : j' !=
 j) : updateCol M j c i j' = M i j'
-/
theorem vecMulVec_update [DecidableEq n] [Mul α] (u : m → α) (v : n → α) (j : n) (a : α) :
    vecMulVec u (Function.update v j a) = (vecMulVec u v).updateCol j (MulOpposite.op a • u) := by
  ext i j'
  obtain rfl | hi := eq_or_ne j' j
  · simp [vecMulVec_apply]
  · simp [vecMulVec_apply, hi]
/-
**Matrix.updateRow_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：updateRow_mul [DecidableEq l] [Fintype m] [NonUnitalNonAssocSemiring α] (A
 : Matrix l m α) (i : l) (r : m -> α) (B : Matrix m n α) : A.updateRow i r * B =
 (A * B).updateRow i (r ᵥ* B)
参数：A : Matrix l m α；i : l；r : m -> α；B : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.updateRow_self`：updateRow_self [DecidableEq m] : updateRow M i b 
i = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.updateRow_ne`：updateRow_ne [DecidableEq m] {i' : m} (i_ne : i' !=
 i) : updateRow M i b i' = M i'
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem updateRow_mul [DecidableEq l] [Fintype m] [NonUnitalNonAssocSemiring α]
    (A : Matrix l m α) (i : l) (r : m → α) (B : Matrix m n α) :
    A.updateRow i r * B = (A * B).updateRow i (r ᵥ* B) := by
  ext i' j'
  obtain rfl | hi := eq_or_ne i' i
  · simp [mul_apply, vecMul, dotProduct]
  · simp [mul_apply, hi]
/-
**Matrix.mul_updateCol** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_updateCol [DecidableEq n] [Fintype m] [NonUnitalNonAssocSemiring α] (A
 : Matrix l m α) (B : Matrix m n α) (j : n) (c : m -> α) : A * B.updateCol j c =
 (A * B).updateCol j (A *ᵥ c)
参数：A : Matrix l m α；B : Matrix m n α；j : n；c : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Matrix.updateCol_self`：updateCol_self [DecidableEq n] : updateCol M j c 
i j = c i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.updateCol_ne`：updateCol_ne [DecidableEq n] {j' : n} (j_ne : j' !=
 j) : updateCol M j c i j' = M i j'
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem mul_updateCol [DecidableEq n] [Fintype m] [NonUnitalNonAssocSemiring α]
    (A : Matrix l m α) (B : Matrix m n α) (j : n) (c : m → α) :
    A * B.updateCol j c = (A * B).updateCol j (A *ᵥ c) := by
  ext i' j'
  obtain rfl | hj := eq_or_ne j' j
  · simp [mul_apply, mulVec, dotProduct]
  · simp [mul_apply, hj]

open RightActions in
/-
**Matrix.mul_single_eq_updateCol_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_single_eq_updateCol_zero [DecidableEq m] [DecidableEq n] [Fintype m] [
NonUnitalNonAssocSemiring α] (A : Matrix l m α) (i : m) (j : n) (r : α) : A * si
ngle i j r = updateCol 0 j (A.col i <• r)
参数：A : Matrix l m α；i : m；j : n；r : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.single_eq_updateCol_zero`：single_eq_updateCol_zero [DecidableEq m
] [DecidableEq n] [Zero α] (i : m) (j : n) (r : α) : single i j r = updateCol 0 
j (Pi.single i r)
· 使用定理 `Matrix.mul_updateCol`：mul_updateCol [DecidableEq n] [Fintype m] [NonUnit
alNonAssocSemiring α] (A : Matrix l m α) (B : Matrix m n α) (j : n) (c : m -> α)
 : A * B.u…
· 使用定理 `Matrix.mul_zero`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Typ
e v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   (M : Matrix m n
 α), …
· 使用定理 `Matrix.mulVec_single`：mulVec_single [Fintype n] [DecidableEq n] [NonUnit
alNonAssocSemiring R] (M : Matrix m n R) (j : n) (x : R) : M *ᵥ Pi.single j x = 
MulOpposit…
-/
theorem mul_single_eq_updateCol_zero
    [DecidableEq m] [DecidableEq n] [Fintype m] [NonUnitalNonAssocSemiring α]
    (A : Matrix l m α) (i : m) (j : n) (r : α) :
    A * single i j r = updateCol 0 j (A.col i <• r) := by
  rw [single_eq_updateCol_zero, mul_updateCol, Matrix.mul_zero, mulVec_single]
/-
**Matrix.single_mul_eq_updateRow_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：single_mul_eq_updateRow_zero [DecidableEq l] [DecidableEq m] [Fintype m] [
NonUnitalNonAssocSemiring α] (i : l) (j : m) (r : α) (B : Matrix m n α) : single
 i j r * B = updateRow 0 i (r • B.row j)
参数：i : l；j : m；r : α；B : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.single_eq_updateRow_zero`：single_eq_updateRow_zero [DecidableEq m
] [DecidableEq n] [Zero α] (i : m) (j : n) (r : α) : single i j r = updateRow 0 
i (Pi.single j r)
· 使用定理 `Matrix.updateRow_mul`：updateRow_mul [DecidableEq l] [Fintype m] [NonUnit
alNonAssocSemiring α] (A : Matrix l m α) (i : l) (r : m -> α) (B : Matrix m n α)
 : A.updat…
· 使用定理 `Matrix.zero_mul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Typ
e v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype m]   (M : Matrix m n
 α), …
· 使用定理 `Matrix.single_vecMul`：single_vecMul [Fintype m] [DecidableEq m] [NonUnit
alNonAssocSemiring R] (M : Matrix m n R) (i : m) (x : R) : Pi.single i x ᵥ* M = 
x • M.row …
-/
theorem single_mul_eq_updateRow_zero
    [DecidableEq l] [DecidableEq m] [Fintype m] [NonUnitalNonAssocSemiring α]
    (i : l) (j : m) (r : α) (B : Matrix m n α) :
    single i j r * B = updateRow 0 i (r • B.row j) := by
  rw [single_eq_updateRow_zero, updateRow_mul, Matrix.zero_mul, single_vecMul]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Matrix.updateRow_zero_mul_updateCol_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：updateRow_zero_mul_updateCol_zero [DecidableEq l] [DecidableEq n] [Fintype
 m] [NonUnitalNonAssocSemiring α] (i : l) (r : m -> α) (j : n) (c : m -> α) : (0
 : Matrix l m α).updateRow i r * (0 : Matrix m n α).updateCol j c = single i j (
r ⬝ᵥ c)
参数：i : l；r : m -> α；j : n；c : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.updateRow_mul`：updateRow_mul [DecidableEq l] [Fintype m] [NonUnit
alNonAssocSemiring α] (A : Matrix l m α) (i : l) (r : m -> α) (B : Matrix m n α)
 : A.updat…
· 使用定理 `Matrix.vecMul_updateCol`：vecMul_updateCol [DecidableEq n] [Fintype m] [N
onUnitalNonAssocSemiring α] (v : m -> α) (B : Matrix m n α) (j : n) (r : m -> α)
 : v ᵥ* B.upd…
· 使用定理 `Matrix.mul_updateCol`：mul_updateCol [DecidableEq n] [Fintype m] [NonUnit
alNonAssocSemiring α] (A : Matrix l m α) (B : Matrix m n α) (j : n) (c : m -> α)
 : A * B.u…
· 使用定理 `Matrix.single_eq_of_single_single`：single_eq_of_single_single (i : m) (j
 : n) (a : α) : single i j a = Matrix.of (Pi.single i (Pi.single j a))
· 使用定理 `Matrix.zero_mul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Typ
e v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype m]   (M : Matrix m n
 α), …
· 使用定理 `Matrix.vecMul_zero`：vecMul_zero [Fintype m] (v : m -> α) : v ᵥ* (0 : Mat
rix m n α) = 0
· 使用定理 `Matrix.zero_mulVec`：zero_mulVec [Fintype n] (v : n -> α) : (0 : Matrix m
 n α) *ᵥ v = 0
· 使用定理 `Matrix.updateCol_zero_zero`：updateCol_zero_zero [DecidableEq n] [Zero α]
 (i : n) : (0 : Matrix m n α).updateCol i 0 = 0
· 使用定理 `Matrix.updateRow.eq_1`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [ins
t : DecidableEq m] (M : Matrix m n α) (i : m) (b : n → α),   M.updateRow i b = M
atrix.of (F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Pi.single.eq_1`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) → Ze
ro (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x = Function
.upd…
-/
theorem updateRow_zero_mul_updateCol_zero
    [DecidableEq l] [DecidableEq n] [Fintype m] [NonUnitalNonAssocSemiring α]
    (i : l) (r : m → α) (j : n) (c : m → α) :
    (0 : Matrix l m α).updateRow i r * (0 : Matrix m n α).updateCol j c = single i j (r ⬝ᵥ c) := by
  rw [updateRow_mul, vecMul_updateCol, mul_updateCol, single_eq_of_single_single, Matrix.zero_mul,
    vecMul_zero, zero_mulVec, updateCol_zero_zero, updateRow, ← Pi.single, ← Pi.single]

end mul

end Matrix

