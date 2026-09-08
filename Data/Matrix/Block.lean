/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Composition
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Block Matrices

## Main definitions

* `Matrix.fromBlocks`: build a block matrix out of 4 blocks
* `Matrix.toBlocks₁₁`, `Matrix.toBlocks₁₂`, `Matrix.toBlocks₂₁`, `Matrix.toBlocks₂₂`:
  extract each of the four blocks from `Matrix.fromBlocks`.
* `Matrix.blockDiagonal`: block diagonal of equally sized blocks. On square blocks, this is a
  ring homomorphisms, `Matrix.blockDiagonalRingHom`.
* `Matrix.blockDiag`: extract the blocks from the diagonal of a block diagonal matrix.
* `Matrix.blockDiagonal'`: block diagonal of unequally sized blocks. On square blocks, this is a
  ring homomorphisms, `Matrix.blockDiagonal'RingHom`.
* `Matrix.blockDiag'`: extract the blocks from the diagonal of a block diagonal matrix.
-/

@[expose] public section

variable {l m n o p q : Type*} {m' n' p' : o → Type*}
variable {R : Type*} {S : Type*} {α : Type*} {β : Type*}

open Matrix

namespace Matrix

/-
**Matrix.dotProduct_block** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：dotProduct_block [Fintype m] [Fintype n] [Mul α] [AddCommMonoid α] (v w : 
m oplus n -> α) : v ⬝ᵥ w = v ∘ Sum.inl ⬝ᵥ w ∘ Sum.inl + v ∘ Sum.inr ⬝ᵥ w ∘ Sum.i
nr
参数：v w : m oplus n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.sum_sum_type`：∀ {α₁ : Type u_4} {α₂ : Type u_5} {M : Type u_6} [
inst : Fintype α₁] [inst_1 : Fintype α₂] [inst_2 : AddCommMonoid M]   (f : α₁ ⊕ 
α₂ → M), ∑…
-/
theorem dotProduct_block [Fintype m] [Fintype n] [Mul α] [AddCommMonoid α] (v w : m ⊕ n → α) :
    v ⬝ᵥ w = v ∘ Sum.inl ⬝ᵥ w ∘ Sum.inl + v ∘ Sum.inr ⬝ᵥ w ∘ Sum.inr :=
  Fintype.sum_sum_type _

section BlockMatrices

/-- We can form a single large matrix by flattening smaller 'block' matrices of compatible
dimensions. -/
@[pp_nodot]
/-
**Matrix.fromBlocks** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：fromBlocks (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : M
atrix o m α) : Matrix (n oplus o) (l oplus m) α
参数：A : Matrix n l α；B : Matrix n m α；C : Matrix o l α；D : Matrix o m α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can form a single large matrix by flattening smaller 'block' matrices of comp
atible
dimensions.
-/
def fromBlocks (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
    Matrix (n ⊕ o) (l ⊕ m) α :=
  of <| Sum.elim (fun i => Sum.elim (A i) (B i)) (fun j => Sum.elim (C j) (D j))

@[simp]
/-
**Matrix.fromBlocks_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fromBlocks_apply₁₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (i : n) (j : l) : fromBlocks A B C D (Sum.inl i) (Sum.inl j) = A i j :=
  rfl

@[simp]
/-
**Matrix.fromBlocks_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fromBlocks_apply₁₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (i : n) (j : m) : fromBlocks A B C D (Sum.inl i) (Sum.inr j) = B i j :=
  rfl

@[simp]
/-
**Matrix.fromBlocks_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fromBlocks_apply₂₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (i : o) (j : l) : fromBlocks A B C D (Sum.inr i) (Sum.inl j) = C i j :=
  rfl

@[simp]
/-
**Matrix.fromBlocks_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fromBlocks_apply₂₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (i : o) (j : m) : fromBlocks A B C D (Sum.inr i) (Sum.inr j) = D i j :=
  rfl

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"top left" submatrix. -/
/-
**Matrix.toBlocks** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a matrix whose row and column indexes are sum types, we can extract the co
rresponding
"top left" submatrix.
-/
def toBlocks₁₁ (M : Matrix (n ⊕ o) (l ⊕ m) α) : Matrix n l α :=
  of fun i j => M (Sum.inl i) (Sum.inl j)

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"top right" submatrix. -/
/-
**Matrix.toBlocks** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a matrix whose row and column indexes are sum types, we can extract the co
rresponding
"top right" submatrix.
-/
def toBlocks₁₂ (M : Matrix (n ⊕ o) (l ⊕ m) α) : Matrix n m α :=
  of fun i j => M (Sum.inl i) (Sum.inr j)

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"bottom left" submatrix. -/
/-
**Matrix.toBlocks** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a matrix whose row and column indexes are sum types, we can extract the co
rresponding
"bottom left" submatrix.
-/
def toBlocks₂₁ (M : Matrix (n ⊕ o) (l ⊕ m) α) : Matrix o l α :=
  of fun i j => M (Sum.inr i) (Sum.inl j)

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"bottom right" submatrix. -/
/-
**Matrix.toBlocks** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a matrix whose row and column indexes are sum types, we can extract the co
rresponding
"bottom right" submatrix.
-/
def toBlocks₂₂ (M : Matrix (n ⊕ o) (l ⊕ m) α) : Matrix o m α :=
  of fun i j => M (Sum.inr i) (Sum.inr j)
/-
**Matrix.fromBlocks_toBlocks** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：fromBlocks_toBlocks (M : Matrix (n oplus o) (l oplus m) α) : fromBlocks M.
toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ = M
参数：M : Matrix (n oplus o) (l oplus m) α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem fromBlocks_toBlocks (M : Matrix (n ⊕ o) (l ⊕ m) α) :
    fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ = M := by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> rfl

@[simp]
/-
**Matrix.toBlocks_fromBlocks** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toBlocks_fromBlocks₁₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D).toBlocks₁₁ = A :=
  rfl

@[simp]
/-
**Matrix.toBlocks_fromBlocks** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toBlocks_fromBlocks₁₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D).toBlocks₁₂ = B :=
  rfl

@[simp]
/-
**Matrix.toBlocks_fromBlocks** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toBlocks_fromBlocks₂₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D).toBlocks₂₁ = C :=
  rfl

@[simp]
/-
**Matrix.toBlocks_fromBlocks** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toBlocks_fromBlocks₂₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D).toBlocks₂₂ = D :=
  rfl

/-- Two block matrices are equal if their blocks are equal. -/
/-
**Matrix.ext_iff_blocks** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：ext_iff_blocks {A B : Matrix (n oplus o) (l oplus m) α} : A = B ↔ A.toBloc
ks₁₁ = B.toBlocks₁₁ ∧ A.toBlocks₁₂ = B.toBlocks₁₂ ∧ A.toBlocks₂₁ = B.toBlocks₂₁ 
∧ A.toBlocks₂₂ = B.toBlocks₂₂
参数：n oplus o；l oplus m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.fromBlocks_toBlocks`：fromBlocks_toBlocks (M : Matrix (n oplus o) 
(l oplus m) α) : fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ 
= M

--- 原说明 ---
Two block matrices are equal if their blocks are equal.
-/
theorem ext_iff_blocks {A B : Matrix (n ⊕ o) (l ⊕ m) α} :
    A = B ↔
      A.toBlocks₁₁ = B.toBlocks₁₁ ∧
        A.toBlocks₁₂ = B.toBlocks₁₂ ∧ A.toBlocks₂₁ = B.toBlocks₂₁ ∧ A.toBlocks₂₂ = B.toBlocks₂₂ :=
  ⟨fun h => h ▸ ⟨rfl, rfl, rfl, rfl⟩, fun ⟨h₁₁, h₁₂, h₂₁, h₂₂⟩ => by
    rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, h₁₁, h₁₂, h₂₁, h₂₂]⟩

@[simp]
/-
**Matrix.fromBlocks_inj** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：fromBlocks_inj {A : Matrix n l α} {B : Matrix n m α} {C : Matrix o l α} {D
 : Matrix o m α} {A' : Matrix n l α} {B' : Matrix n m α} {C' : Matrix o l α} {D'
 : Matrix o m α} : fromBlocks A B C D = fromBlocks A' B' C' D' ↔ A = A' ∧ B = B'
 ∧ C = C' ∧ D = D'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext_iff_blocks`：ext_iff_blocks {A B : Matrix (n oplus o) (l oplus
 m) α} : A = B ↔ A.toBlocks₁₁ = B.toBlocks₁₁ ∧ A.toBlocks₁₂ = B.toBlocks₁₂ ∧ A.t
oBlocks₂₁ =…
-/
theorem fromBlocks_inj {A : Matrix n l α} {B : Matrix n m α} {C : Matrix o l α} {D : Matrix o m α}
    {A' : Matrix n l α} {B' : Matrix n m α} {C' : Matrix o l α} {D' : Matrix o m α} :
    fromBlocks A B C D = fromBlocks A' B' C' D' ↔ A = A' ∧ B = B' ∧ C = C' ∧ D = D' :=
  ext_iff_blocks
/-
**Matrix.fromBlocks_map** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：fromBlocks_map (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D
 : Matrix o m α) (f : α -> β) : (fromBlocks A B C D).map f = fromBlocks (A.map f
) (B.map f) (C.map f) (D.map f)
参数：A : Matrix n l α；B : Matrix n m α；C : Matrix o l α；D : Matrix o m α；f : α -> 
β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fromBlocks_map (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α)
    (f : α → β) : (fromBlocks A B C D).map f =
      fromBlocks (A.map f) (B.map f) (C.map f) (D.map f) := by
  ext i j; rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [fromBlocks]
/-
**Matrix.fromBlocks_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：fromBlocks_transpose (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l
 α) (D : Matrix o m α) : (fromBlocks A B C D)ᵀ = fromBlocks Aᵀ Cᵀ Bᵀ Dᵀ
参数：A : Matrix n l α；B : Matrix n m α；C : Matrix o l α；D : Matrix o m α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fromBlocks_transpose (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D)ᵀ = fromBlocks Aᵀ Cᵀ Bᵀ Dᵀ := by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [fromBlocks]
/-
**Matrix.fromBlocks_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：fromBlocks_conjTranspose [Star α] (A : Matrix n l α) (B : Matrix n m α) (C
 : Matrix o l α) (D : Matrix o m α) : (fromBlocks A B C D)ᴴ = fromBlocks Aᴴ Cᴴ B
ᴴ Dᴴ
参数：A : Matrix n l α；B : Matrix n m α；C : Matrix o l α；D : Matrix o m α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.fromBlocks_transpose`：fromBlocks_transpose (A : Matrix n l α) (B 
: Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) : (fromBlocks A B C D)ᵀ = 
fromBlocks Aᵀ Cᵀ …
· 使用定理 `Matrix.fromBlocks_map`：fromBlocks_map (A : Matrix n l α) (B : Matrix n m
 α) (C : Matrix o l α) (D : Matrix o m α) (f : α -> β) : (fromBlocks A B C D).ma
p f = fromB…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fromBlocks_conjTranspose [Star α] (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D)ᴴ = fromBlocks Aᴴ Cᴴ Bᴴ Dᴴ := by
  simp only [conjTranspose, fromBlocks_transpose, fromBlocks_map]

@[simp]
/-
**Matrix.fromBlocks_submatrix_sum_swap_left** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：fromBlocks_submatrix_sum_swap_left (A : Matrix n l α) (B : Matrix n m α) (
C : Matrix o l α) (D : Matrix o m α) (f : p -> l oplus m) : (fromBlocks A B C D)
.submatrix Sum.swap f = (fromBlocks C D A B).submatrix id f
参数：A : Matrix n l α；B : Matrix n m α；C : Matrix o l α；D : Matrix o m α；f : p -> 
l oplus m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem fromBlocks_submatrix_sum_swap_left (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (f : p → l ⊕ m) :
    (fromBlocks A B C D).submatrix Sum.swap f = (fromBlocks C D A B).submatrix id f := by
  ext i j
  cases i <;> dsimp <;> cases f j <;> rfl

@[simp]
/-
**Matrix.fromBlocks_submatrix_sum_swap_right** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：fromBlocks_submatrix_sum_swap_right (A : Matrix n l α) (B : Matrix n m α) 
(C : Matrix o l α) (D : Matrix o m α) (f : p -> n oplus o) : (fromBlocks A B C D
).submatrix f Sum.swap = (fromBlocks B A D C).submatrix f id
参数：A : Matrix n l α；B : Matrix n m α；C : Matrix o l α；D : Matrix o m α；f : p -> 
n oplus o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem fromBlocks_submatrix_sum_swap_right (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (f : p → n ⊕ o) :
    (fromBlocks A B C D).submatrix f Sum.swap = (fromBlocks B A D C).submatrix f id := by
  ext i j
  cases j <;> dsimp <;> cases f i <;> rfl
/-
**Matrix.fromBlocks_submatrix_sum_swap_sum_swap** 是 Mathlib 中的一个定理，位于命名空间 `Matri
x`。
形式化陈述：fromBlocks_submatrix_sum_swap_sum_swap {l m n o α : Type*} (A : Matrix n l
 α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) : (fromBlocks A B C
 D).submatrix Sum.swap Sum.swap = fromBlocks D C B A
参数：A : Matrix n l α；B : Matrix n m α；C : Matrix o l α；D : Matrix o m α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.fromBlocks_submatrix_sum_swap_right`：fromBlocks_submatrix_sum_swa
p_right (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m
 α) (f : p -> n oplus o) : (from…
· 使用定理 `Matrix.fromBlocks_submatrix_sum_swap_left`：fromBlocks_submatrix_sum_swap
_left (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α
) (f : p -> l oplus m) : (fromB…
· 使用定理 `Matrix.submatrix_id_id`：submatrix_id_id (A : Matrix m n α) : A.submatrix
 id id = A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fromBlocks_submatrix_sum_swap_sum_swap {l m n o α : Type*} (A : Matrix n l α)
    (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
    (fromBlocks A B C D).submatrix Sum.swap Sum.swap = fromBlocks D C B A := by simp

/-- A 2x2 block matrix is block diagonal if the blocks outside of the diagonal vanish -/
/-
**Matrix.IsTwoBlockDiagonal** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：IsTwoBlockDiagonal [Zero α] (A : Matrix (n oplus o) (l oplus m) α) : Prop
参数：A : Matrix (n oplus o) (l oplus m) α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A 2x2 block matrix is block diagonal if the blocks outside of the diagonal vanis
h
-/
def IsTwoBlockDiagonal [Zero α] (A : Matrix (n ⊕ o) (l ⊕ m) α) : Prop :=
  toBlocks₁₂ A = 0 ∧ toBlocks₂₁ A = 0

/-- Let `p` pick out certain rows and `q` pick out certain columns of a matrix `M`. Then
  `toBlock M p q` is the corresponding block matrix. -/
/-
**Matrix.toBlock** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：toBlock (M : Matrix m n α) (p : m -> Prop) (q : n -> Prop) : Matrix { a //
 p a } { a // q a } α
参数：M : Matrix m n α；p : m -> Prop；q : n -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `p` pick out certain rows and `q` pick out certain columns of a matrix `M`. 
Then
  `toBlock M p q` is the corresponding block matrix.
-/
def toBlock (M : Matrix m n α) (p : m → Prop) (q : n → Prop) : Matrix { a // p a } { a // q a } α :=
  M.submatrix (↑) (↑)

@[simp]
/-
**Matrix.toBlock_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：toBlock_apply (M : Matrix m n α) (p : m -> Prop) (q : n -> Prop) (i : { a 
// p a }) (j : { a // q a }) : toBlock M p q i j = M ↑i ↑j
参数：M : Matrix m n α；p : m -> Prop；q : n -> Prop；i : { a // p a }；j : { a // q a 
}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toBlock_apply (M : Matrix m n α) (p : m → Prop) (q : n → Prop) (i : { a // p a })
    (j : { a // q a }) : toBlock M p q i j = M ↑i ↑j :=
  rfl

/-- Let `p` pick out certain rows and columns of a square matrix `M`. Then
  `toSquareBlockProp M p` is the corresponding block matrix. -/
/-
**Matrix.toSquareBlockProp** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：toSquareBlockProp (M : Matrix m m α) (p : m -> Prop) : Matrix { a // p a }
 { a // p a } α
参数：M : Matrix m m α；p : m -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `p` pick out certain rows and columns of a square matrix `M`. Then
  `toSquareBlockProp M p` is the corresponding block matrix.
-/
def toSquareBlockProp (M : Matrix m m α) (p : m → Prop) : Matrix { a // p a } { a // p a } α :=
  toBlock M _ _
/-
**Matrix.toSquareBlockProp_def** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：toSquareBlockProp_def (M : Matrix m m α) (p : m -> Prop) : toSquareBlockPr
op M p = of (fun i j : { a // p a } => M ↑i ↑j)
参数：M : Matrix m m α；p : m -> Prop。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSquareBlockProp_def (M : Matrix m m α) (p : m → Prop) :
    toSquareBlockProp M p = of (fun i j : { a // p a } => M ↑i ↑j) :=
  rfl

/-- Let `b` map rows and columns of a square matrix `M` to blocks. Then
  `toSquareBlock M b k` is the block `k` matrix. -/
/-
**Matrix.toSquareBlock** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：toSquareBlock (M : Matrix m m α) (b : m -> β) (k : β) : Matrix { a // b a 
= k } { a // b a = k } α
参数：M : Matrix m m α；b : m -> β；k : β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `b` map rows and columns of a square matrix `M` to blocks. Then
  `toSquareBlock M b k` is the block `k` matrix.
-/
def toSquareBlock (M : Matrix m m α) (b : m → β) (k : β) :
    Matrix { a // b a = k } { a // b a = k } α :=
  toSquareBlockProp M _
/-
**Matrix.toSquareBlock_def** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：toSquareBlock_def (M : Matrix m m α) (b : m -> β) (k : β) : toSquareBlock 
M b k = of (fun i j : { a // b a = k } => M ↑i ↑j)
参数：M : Matrix m m α；b : m -> β；k : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSquareBlock_def (M : Matrix m m α) (b : m → β) (k : β) :
    toSquareBlock M b k = of (fun i j : { a // b a = k } => M ↑i ↑j) :=
  rfl
/-
**Matrix.fromBlocks_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：fromBlocks_smul [SMul R α] (x : R) (A : Matrix n l α) (B : Matrix n m α) (
C : Matrix o l α) (D : Matrix o m α) : x • fromBlocks A B C D = fromBlocks (x • 
A) (x • B) (x • C) (x • D)
参数：x : R；A : Matrix n l α；B : Matrix n m α；C : Matrix o l α；D : Matrix o m α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fromBlocks_smul [SMul R α] (x : R) (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : x • fromBlocks A B C D = fromBlocks (x • A) (x • B) (x • C) (x • D) := by
  ext i j; rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [fromBlocks]
/-
**Matrix.fromBlocks_neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：fromBlocks_neg [Neg R] (A : Matrix n l R) (B : Matrix n m R) (C : Matrix o
 l R) (D : Matrix o m R) : -fromBlocks A B C D = fromBlocks (-A) (-B) (-C) (-D)
参数：A : Matrix n l R；B : Matrix n m R；C : Matrix o l R；D : Matrix o m R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem fromBlocks_neg [Neg R] (A : Matrix n l R) (B : Matrix n m R) (C : Matrix o l R)
    (D : Matrix o m R) : -fromBlocks A B C D = fromBlocks (-A) (-B) (-C) (-D) := by
  ext i j
  cases i <;> cases j <;> simp [fromBlocks]

@[simp]
/-
**Matrix.fromBlocks_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：fromBlocks_zero [Zero α] : fromBlocks (0 : Matrix n l α) 0 0 (0 : Matrix o
 m α) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem fromBlocks_zero [Zero α] : fromBlocks (0 : Matrix n l α) 0 0 (0 : Matrix o m α) = 0 := by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> rfl
/-
**Matrix.fromBlocks_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：fromBlocks_add [Add α] (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o
 l α) (D : Matrix o m α) (A' : Matrix n l α) (B' : Matrix n m α) (C' : Matrix o 
l α) (D' : Matrix o m α) : fromBlocks A B C D + fromBlocks A' B' C' D' = fromBlo
cks (A + A') (B + B') (C + C') (D + D')
参数：A : Matrix n l α；B : Matrix n m α；C : Matrix o l α；D : Matrix o m α；A' : Matr
ix n l α；B' : Matrix n m α；C' : Matrix o l α；D' : Matrix o m α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem fromBlocks_add [Add α] (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (A' : Matrix n l α) (B' : Matrix n m α) (C' : Matrix o l α)
    (D' : Matrix o m α) : fromBlocks A B C D + fromBlocks A' B' C' D' =
      fromBlocks (A + A') (B + B') (C + C') (D + D') := by
  ext i j; rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> rfl
/-
**Matrix.fromBlocks_multiply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：fromBlocks_multiply [Fintype l] [Fintype m] [NonUnitalNonAssocSemiring α] 
(A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (A' 
: Matrix l p α) (B' : Matrix l q α) (C' : Matrix m p α) (D' : Matrix m q α) : fr
omBlocks A B C D * fromBlocks A' B' C' D' = fromBlocks (A * A' + B * C') (A * B'
 + B * D') (C * A' + D * C') (C * B' + D * D')
参数：A : Matrix n l α；B : Matrix n m α；C : Matrix o l α；D : Matrix o m α；A' : Matr
ix l p α；B' : Matrix l q α；C' : Matrix m p α；D' : Matrix m q α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.sum_sum_type`：∀ {α₁ : Type u_4} {α₂ : Type u_5} {M : Type u_6} [
inst : Fintype α₁] [inst_1 : Fintype α₂] [inst_2 : AddCommMonoid M]   (f : α₁ ⊕ 
α₂ → M), ∑…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fromBlocks_multiply [Fintype l] [Fintype m] [NonUnitalNonAssocSemiring α] (A : Matrix n l α)
    (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (A' : Matrix l p α) (B' : Matrix l q α)
    (C' : Matrix m p α) (D' : Matrix m q α) :
    fromBlocks A B C D * fromBlocks A' B' C' D' =
      fromBlocks (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') := by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp only [fromBlocks, mul_apply, of_apply,
      Sum.elim_inr, Fintype.sum_sum_type, Sum.elim_inl, add_apply]
/-
**Matrix.fromBlocks_diagonal_pow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：fromBlocks_diagonal_pow [Semiring α] [Fintype n] [Fintype m] [DecidableEq 
n] [DecidableEq m] (A : Matrix n n α) (D : Matrix m m α) (k : Nat) : (fromBlocks
 A 0 0 D) ^ k = fromBlocks (A ^ k) 0 0 (D ^ k)
参数：A : Matrix n n α；D : Matrix m m α；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.one_apply_ne`：one_apply_ne {i j} : i != j -> (1 : Matrix n n α) i
 j = 0
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Matrix.fromBlocks_multiply`：fromBlocks_multiply [Fintype l] [Fintype m] 
[NonUnitalNonAssocSemiring α] (A : Matrix n l α) (B : Matrix n m α) (C : Matrix 
o l α) (D : Matr…
· 使用定理 `Matrix.mul_zero`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Typ
e v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   (M : Matrix m n
 α), …
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Matrix.zero_mul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Typ
e v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype m]   (M : Matrix m n
 α), …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem fromBlocks_diagonal_pow [Semiring α] [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (A : Matrix n n α) (D : Matrix m m α) (k : ℕ) :
    (fromBlocks A 0 0 D) ^ k = fromBlocks (A ^ k) 0 0 (D ^ k) := by
  induction k with
  | zero => ext (i | i) (j | j) <;> simp [one_apply]
  | succ n ih =>
    simp [ih, pow_succ, fromBlocks_multiply]
/-
**Matrix.fromBlocks_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：fromBlocks_mulVec [Fintype l] [Fintype m] [NonUnitalNonAssocSemiring α] (A
 : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (x : l
 oplus m -> α) : (fromBlocks A B C D) *ᵥ x = Sum.elim (A *ᵥ (x ∘ Sum.inl) + B *ᵥ
 (x ∘ Sum.inr)) (C *ᵥ (x ∘ Sum.inl) + D *ᵥ (x ∘ Sum.inr))
参数：A : Matrix n l α；B : Matrix n m α；C : Matrix o l α；D : Matrix o m α；x : l opl
us m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Fintype.sum_sum_type`：∀ {α₁ : Type u_4} {α₂ : Type u_5} {M : Type u_6} [
inst : Fintype α₁] [inst_1 : Fintype α₂] [inst_2 : AddCommMonoid M]   (f : α₁ ⊕ 
α₂ → M), ∑…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem fromBlocks_mulVec [Fintype l] [Fintype m] [NonUnitalNonAssocSemiring α] (A : Matrix n l α)
    (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (x : l ⊕ m → α) :
    (fromBlocks A B C D) *ᵥ x =
      Sum.elim (A *ᵥ (x ∘ Sum.inl) + B *ᵥ (x ∘ Sum.inr))
        (C *ᵥ (x ∘ Sum.inl) + D *ᵥ (x ∘ Sum.inr)) := by
  ext i
  cases i <;> simp [mulVec, dotProduct]
/-
**Matrix.vecMul_fromBlocks** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMul_fromBlocks [Fintype n] [Fintype o] [NonUnitalNonAssocSemiring α] (A
 : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (x : n
 oplus o -> α) : x ᵥ* fromBlocks A B C D = Sum.elim ((x ∘ Sum.inl) ᵥ* A + (x ∘ S
um.inr) ᵥ* C) ((x ∘ Sum.inl) ᵥ* B + (x ∘ Sum.inr) ᵥ* D)
参数：A : Matrix n l α；B : Matrix n m α；C : Matrix o l α；D : Matrix o m α；x : n opl
us o -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Fintype.sum_sum_type`：∀ {α₁ : Type u_4} {α₂ : Type u_5} {M : Type u_6} [
inst : Fintype α₁] [inst_1 : Fintype α₂] [inst_2 : AddCommMonoid M]   (f : α₁ ⊕ 
α₂ → M), ∑…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem vecMul_fromBlocks [Fintype n] [Fintype o] [NonUnitalNonAssocSemiring α] (A : Matrix n l α)
    (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (x : n ⊕ o → α) :
    x ᵥ* fromBlocks A B C D =
      Sum.elim ((x ∘ Sum.inl) ᵥ* A + (x ∘ Sum.inr) ᵥ* C)
        ((x ∘ Sum.inl) ᵥ* B + (x ∘ Sum.inr) ᵥ* D) := by
  ext i
  cases i <;> simp [vecMul, dotProduct]

variable [DecidableEq l] [DecidableEq m]

section Zero

variable [Zero α]

/-
**Matrix.toBlock_diagonal_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：toBlock_diagonal_self (d : m -> α) (p : m -> Prop) : Matrix.toBlock (diago
nal d) p p = diagonal fun i : Subtype p => d ↑i
参数：d : m -> α；p : m -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `Matrix.diagonal.congr_simp`：∀ {n : Type u_3} {α : Type v} {inst : Decida
bleEq n} [inst_1 : DecidableEq n] [inst_2 : Zero α] (d d_1 : n → α),   d = d_1 →
 ∀ (a a_1 : n), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem toBlock_diagonal_self (d : m → α) (p : m → Prop) :
    Matrix.toBlock (diagonal d) p p = diagonal fun i : Subtype p => d ↑i := by
  ext i j
  by_cases h : i = j
  · simp [h]
  · simp [h, Subtype.val_injective.ne h]
/-
**Matrix.toBlock_diagonal_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：toBlock_diagonal_disjoint (d : m -> α) {p q : m -> Prop} (hpq : Disjoint p
 q) : Matrix.toBlock (diagonal d) p q = 0
参数：d : m -> α；hpq : Disjoint p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toBlock_diagonal_disjoint (d : m → α) {p q : m → Prop} (hpq : Disjoint p q) :
    Matrix.toBlock (diagonal d) p q = 0 := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  have : i ≠ j := fun heq => hpq.le_bot i ⟨hi, heq.symm ▸ hj⟩
  simp [diagonal_apply_ne d this]

@[simp]
/-
**Matrix.fromBlocks_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：fromBlocks_diagonal (d₁ : l -> α) (d₂ : m -> α) : fromBlocks (diagonal d₁)
 0 0 (diagonal d₂) = diagonal (Sum.elim d₁ d₂)
参数：d₁ : l -> α；d₂ : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
-/
theorem fromBlocks_diagonal (d₁ : l → α) (d₂ : m → α) :
    fromBlocks (diagonal d₁) 0 0 (diagonal d₂) = diagonal (Sum.elim d₁ d₂) := by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [diagonal]

@[simp]
/-
**Matrix.toBlocks** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toBlocks₁₁_diagonal (v : l ⊕ m → α) :
    toBlocks₁₁ (diagonal v) = diagonal (fun i => v (Sum.inl i)) := by
  unfold toBlocks₁₁
  funext i j
  simp only [Sum.inl.injEq, of_apply, diagonal_apply]

@[simp]
/-
**Matrix.toBlocks** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toBlocks₂₂_diagonal (v : l ⊕ m → α) :
    toBlocks₂₂ (diagonal v) = diagonal (fun i => v (Sum.inr i)) := by
  unfold toBlocks₂₂
  funext i j
  simp only [Sum.inr.injEq, of_apply, diagonal_apply]

@[simp]
/-
**Matrix.toBlocks** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toBlocks₁₂_diagonal (v : l ⊕ m → α) : toBlocks₁₂ (diagonal v) = 0 := rfl

@[simp]
/-
**Matrix.toBlocks** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toBlocks₂₁_diagonal (v : l ⊕ m → α) : toBlocks₂₁ (diagonal v) = 0 := rfl

end Zero

section HasZeroHasOne

variable [Zero α] [One α]

@[simp]
/-
**Matrix.fromBlocks_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：fromBlocks_one : fromBlocks (1 : Matrix l l α) 0 0 (1 : Matrix m m α) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.one_apply_ne`：one_apply_ne {i j} : i != j -> (1 : Matrix n n α) i
 j = 0
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
-/
theorem fromBlocks_one : fromBlocks (1 : Matrix l l α) 0 0 (1 : Matrix m m α) = 1 := by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [one_apply]

@[simp]
/-
**Matrix.toBlock_one_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：toBlock_one_self (p : m -> Prop) : Matrix.toBlock (1 : Matrix m m α) p p =
 1
参数：p : m -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.toBlock_diagonal_self`：toBlock_diagonal_self (d : m -> α) (p : m 
-> Prop) : Matrix.toBlock (diagonal d) p p = diagonal fun i : Subtype p => d ↑i
-/
theorem toBlock_one_self (p : m → Prop) : Matrix.toBlock (1 : Matrix m m α) p p = 1 :=
  toBlock_diagonal_self _ p
/-
**Matrix.toBlock_one_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：toBlock_one_disjoint {p q : m -> Prop} (hpq : Disjoint p q) : Matrix.toBlo
ck (1 : Matrix m m α) p q = 0
参数：hpq : Disjoint p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.toBlock_diagonal_disjoint`：toBlock_diagonal_disjoint (d : m -> α)
 {p q : m -> Prop} (hpq : Disjoint p q) : Matrix.toBlock (diagonal d) p q = 0
-/
theorem toBlock_one_disjoint {p q : m → Prop} (hpq : Disjoint p q) :
    Matrix.toBlock (1 : Matrix m m α) p q = 0 :=
  toBlock_diagonal_disjoint _ hpq

end HasZeroHasOne

end BlockMatrices

section BlockDiagonal

variable [DecidableEq o]

section Zero

variable [Zero α] [Zero β]

/-- `Matrix.blockDiagonal M` turns a homogeneously-indexed collection of matrices
`M : o → Matrix m n α'` into an `m × o`-by-`n × o` block matrix which has the entries of `M` along
the diagonal and zero elsewhere.

See also `Matrix.blockDiagonal'` if the matrices may not have the same size everywhere.
-/
/-
**Matrix.blockDiagonal** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：blockDiagonal (M : o -> Matrix m n α) : Matrix (m × o) (n × o) α
参数：M : o -> Matrix m n α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.blockDiagonal M` turns a homogeneously-indexed collection of matrices
`M : o → Matrix m n α'` into an `m × o`-by-`n × o` block matrix which has the en
tries of `M` along
the diagonal and zero elsewhere.

See also `Matrix.blockDiagonal'` if the matrices may not have the same size ever
ywhere.
-/
def blockDiagonal (M : o → Matrix m n α) : Matrix (m × o) (n × o) α :=
  of <| (fun ⟨i, k⟩ ⟨j, k'⟩ => if k = k' then M k i j else 0 : m × o → n × o → α)

-- TODO: set as an equation lemma for `blockDiagonal`, see https://github.com/leanprover-community/mathlib4/pull/3024
/-
**Matrix.blockDiagonal_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockDiagonal_apply' (M : o -> Matrix m n α) (i k j k') : blockDiagonal M 
⟨i, k⟩ ⟨j, k'⟩ = if k = k' then M k i j else 0
参数：M : o -> Matrix m n α；i k j k'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem blockDiagonal_apply' (M : o → Matrix m n α) (i k j k') :
    blockDiagonal M ⟨i, k⟩ ⟨j, k'⟩ = if k = k' then M k i j else 0 :=
  rfl
/-
**Matrix.blockDiagonal_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockDiagonal_apply (M : o -> Matrix m n α) (ik jk) : blockDiagonal M ik j
k = if ik.2 = jk.2 then M ik.2 ik.1 jk.1 else 0
参数：M : o -> Matrix m n α；ik jk。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem blockDiagonal_apply (M : o → Matrix m n α) (ik jk) :
    blockDiagonal M ik jk = if ik.2 = jk.2 then M ik.2 ik.1 jk.1 else 0 := rfl

@[simp]
/-
**Matrix.blockDiagonal_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockDiagonal_apply_eq (M : o -> Matrix m n α) (i j k) : blockDiagonal M (
i, k) (j, k) = M k i j
参数：M : o -> Matrix m n α；i j k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem blockDiagonal_apply_eq (M : o → Matrix m n α) (i j k) :
    blockDiagonal M (i, k) (j, k) = M k i j :=
  if_pos rfl
/-
**Matrix.blockDiagonal_apply_ne** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockDiagonal_apply_ne (M : o -> Matrix m n α) (i j) {k k'} (h : k != k') 
: blockDiagonal M (i, k) (j, k') = 0
参数：M : o -> Matrix m n α；i j；h : k != k'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem blockDiagonal_apply_ne (M : o → Matrix m n α) (i j) {k k'} (h : k ≠ k') :
    blockDiagonal M (i, k) (j, k') = 0 :=
  if_neg h
/-
**Matrix.blockDiagonal_map** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockDiagonal_map (M : o -> Matrix m n α) (f : α -> β) (hf : f 0 = 0) : (b
lockDiagonal M).map f = blockDiagonal fun k => (M k).map f
参数：M : o -> Matrix m n α；f : α -> β；hf : f 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
-/
theorem blockDiagonal_map (M : o → Matrix m n α) (f : α → β) (hf : f 0 = 0) :
    (blockDiagonal M).map f = blockDiagonal fun k => (M k).map f := by
  ext
  simp only [map_apply, blockDiagonal_apply]
  rw [apply_ite f, hf]

@[simp]
/-
**Matrix.blockDiagonal_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockDiagonal_transpose (M : o -> Matrix m n α) : (blockDiagonal M)ᵀ = blo
ckDiagonal fun k => (M k)ᵀ
参数：M : o -> Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem blockDiagonal_transpose (M : o → Matrix m n α) :
    (blockDiagonal M)ᵀ = blockDiagonal fun k => (M k)ᵀ := by
  ext
  simp only [transpose_apply, blockDiagonal_apply, eq_comm]
  split_ifs with h
  · rw [h]
  · rfl

@[simp]
/-
**Matrix.blockDiagonal_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockDiagonal_conjTranspose {α : Type*} [AddMonoid α] [StarAddMonoid α] (M
 : o -> Matrix m n α) : (blockDiagonal M)ᴴ = blockDiagonal fun k => (M k)ᴴ
参数：M : o -> Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.blockDiagonal_transpose`：blockDiagonal_transpose (M : o -> Matrix
 m n α) : (blockDiagonal M)ᵀ = blockDiagonal fun k => (M k)ᵀ
· 使用定理 `Matrix.blockDiagonal_map`：blockDiagonal_map (M : o -> Matrix m n α) (f :
 α -> β) (hf : f 0 = 0) : (blockDiagonal M).map f = blockDiagonal fun k => (M k)
.map f
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
-/
theorem blockDiagonal_conjTranspose {α : Type*} [AddMonoid α] [StarAddMonoid α]
    (M : o → Matrix m n α) : (blockDiagonal M)ᴴ = blockDiagonal fun k => (M k)ᴴ := by
  simp only [conjTranspose, blockDiagonal_transpose]
  rw [blockDiagonal_map _ star (star_zero α)]

@[simp]
/-
**Matrix.blockDiagonal_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockDiagonal_zero : blockDiagonal (0 : o -> Matrix m n α) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem blockDiagonal_zero : blockDiagonal (0 : o → Matrix m n α) = 0 := by
  ext
  simp [blockDiagonal_apply]

@[simp]
/-
**Matrix.blockDiagonal_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockDiagonal_diagonal [DecidableEq m] (d : o -> m -> α) : (blockDiagonal 
fun k => diagonal (d k)) = diagonal fun ik => d ik.2 ik.1
参数：d : o -> m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
-/
theorem blockDiagonal_diagonal [DecidableEq m] (d : o → m → α) :
    (blockDiagonal fun k => diagonal (d k)) = diagonal fun ik => d ik.2 ik.1 := by
  ext ⟨i, k⟩ ⟨j, k'⟩
  simp only [blockDiagonal_apply, diagonal_apply, Prod.mk_inj, ← ite_and]
  congr 1
  rw [and_comm]

@[simp]
/-
**Matrix.blockDiagonal_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockDiagonal_one [DecidableEq m] [One α] : blockDiagonal (1 : o -> Matrix
 m m α) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.blockDiagonal_diagonal`：blockDiagonal_diagonal [DecidableEq m] (d
 : o -> m -> α) : (blockDiagonal fun k => diagonal (d k)) = diagonal fun ik => d
 ik.2 ik.1
-/
theorem blockDiagonal_one [DecidableEq m] [One α] : blockDiagonal (1 : o → Matrix m m α) = 1 :=
  show (blockDiagonal fun _ : o => diagonal fun _ : m => (1 : α)) = diagonal fun _ => 1 by
    rw [blockDiagonal_diagonal]

end Zero

@[simp]
/-
**Matrix.blockDiagonal_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockDiagonal_add [AddZeroClass α] (M N : o -> Matrix m n α) : blockDiagon
al (M + N) = blockDiagonal M + blockDiagonal N
参数：M N : o -> Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem blockDiagonal_add [AddZeroClass α] (M N : o → Matrix m n α) :
    blockDiagonal (M + N) = blockDiagonal M + blockDiagonal N := by
  ext
  simp only [blockDiagonal_apply, Pi.add_apply, add_apply]
  split_ifs <;> simp

section

variable (o m n α)

/-- `Matrix.blockDiagonal` as an `AddMonoidHom`. -/
@[simps]
/-
**Matrix.blockDiagonalAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：blockDiagonalAddMonoidHom [AddZeroClass α] : (o -> Matrix m n α) ->+ Matri
x (m × o) (n × o) α where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.blockDiagonal_add`：blockDiagonal_add [AddZeroClass α] (M N : o ->
 Matrix m n α) : blockDiagonal (M + N) = blockDiagonal M + blockDiagonal N

--- 原说明 ---
`Matrix.blockDiagonal` as an `AddMonoidHom`.
-/
def blockDiagonalAddMonoidHom [AddZeroClass α] :
    (o → Matrix m n α) →+ Matrix (m × o) (n × o) α where
  toFun := blockDiagonal
  map_zero' := blockDiagonal_zero
  map_add' := blockDiagonal_add

end

@[simp]
/-
**Matrix.blockDiagonal_neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockDiagonal_neg [AddGroup α] (M : o -> Matrix m n α) : blockDiagonal (-M
) = -blockDiagonal M
参数：M : o -> Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem blockDiagonal_neg [AddGroup α] (M : o → Matrix m n α) :
    blockDiagonal (-M) = -blockDiagonal M :=
  map_neg (blockDiagonalAddMonoidHom m n o α) M

@[simp]
/-
**Matrix.blockDiagonal_sub** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockDiagonal_sub [AddGroup α] (M N : o -> Matrix m n α) : blockDiagonal (
M - N) = blockDiagonal M - blockDiagonal N
参数：M N : o -> Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem blockDiagonal_sub [AddGroup α] (M N : o → Matrix m n α) :
    blockDiagonal (M - N) = blockDiagonal M - blockDiagonal N :=
  map_sub (blockDiagonalAddMonoidHom m n o α) M N

@[simp]
/-
**Matrix.blockDiagonal_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockDiagonal_mul [Fintype n] [Fintype o] [NonUnitalNonAssocSemiring α] (M
 : o -> Matrix m n α) (N : o -> Matrix n p α) : (blockDiagonal fun k => M k * N 
k) = blockDiagonal M * blockDiagonal N
参数：M : o -> Matrix m n α；N : o -> Matrix n p α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Finset.sum_product`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst
 : AddCommMonoid β] (s : Finset γ) (t : Finset α) (f : γ × α → β),   ∑ x ∈ s ×ˢ 
t, f x =…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
-/
theorem blockDiagonal_mul [Fintype n] [Fintype o] [NonUnitalNonAssocSemiring α]
    (M : o → Matrix m n α) (N : o → Matrix n p α) :
    (blockDiagonal fun k => M k * N k) = blockDiagonal M * blockDiagonal N := by
  ext ⟨i, k⟩ ⟨j, k'⟩
  simp only [blockDiagonal_apply, mul_apply, ← Finset.univ_product_univ, Finset.sum_product]
  split_ifs with h <;> simp [h]

section

variable (α m o)

/-- `Matrix.blockDiagonal` as a `RingHom`. -/
@[simps]
/-
**Matrix.blockDiagonalRingHom** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：blockDiagonalRingHom [DecidableEq m] [Fintype o] [Fintype m] [NonAssocSemi
ring α] : (o -> Matrix m m α) ->+* Matrix (m × o) (m × o) α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.blockDiagonal` as a `RingHom`.
-/
def blockDiagonalRingHom [DecidableEq m] [Fintype o] [Fintype m] [NonAssocSemiring α] :
    (o → Matrix m m α) →+* Matrix (m × o) (m × o) α :=
  { blockDiagonalAddMonoidHom m m o α with
    toFun := blockDiagonal
    map_one' := blockDiagonal_one
    map_mul' := blockDiagonal_mul }

end

@[simp]
/-
**Matrix.blockDiagonal_pow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockDiagonal_pow [DecidableEq m] [Fintype o] [Fintype m] [Semiring α] (M 
: o -> Matrix m m α) (n : Nat) : blockDiagonal (M ^ n) = blockDiagonal M ^ n
参数：M : o -> Matrix m m α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem blockDiagonal_pow [DecidableEq m] [Fintype o] [Fintype m] [Semiring α]
    (M : o → Matrix m m α) (n : ℕ) : blockDiagonal (M ^ n) = blockDiagonal M ^ n :=
  map_pow (blockDiagonalRingHom m o α) M n

@[simp]
/-
**Matrix.blockDiagonal_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockDiagonal_smul {R : Type*} [Zero α] [SMulZeroClass R α] (x : R) (M : o
 -> Matrix m n α) : blockDiagonal (x • M) = x • blockDiagonal M
参数：x : R；M : o -> Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem blockDiagonal_smul {R : Type*} [Zero α] [SMulZeroClass R α] (x : R)
    (M : o → Matrix m n α) : blockDiagonal (x • M) = x • blockDiagonal M := by
  ext
  simp only [blockDiagonal_apply, Pi.smul_apply, smul_apply]
  split_ifs <;> simp

end BlockDiagonal

section BlockDiag

/-- Extract a block from the diagonal of a block diagonal matrix.

This is the block form of `Matrix.diag`, and the left-inverse of `Matrix.blockDiagonal`. -/
/-
**Matrix.blockDiag** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：blockDiag (M : Matrix (m × o) (n × o) α) (k : o) : Matrix m n α
参数：M : Matrix (m × o) (n × o) α；k : o。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract a block from the diagonal of a block diagonal matrix.

This is the block form of `Matrix.diag`, and the left-inverse of `Matrix.blockDi
agonal`.
-/
def blockDiag (M : Matrix (m × o) (n × o) α) (k : o) : Matrix m n α :=
  of fun i j => M (i, k) (j, k)

-- TODO: set as an equation lemma for `blockDiag`, see https://github.com/leanprover-community/mathlib4/pull/3024
/-
**Matrix.blockDiag_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockDiag_apply (M : Matrix (m × o) (n × o) α) (k : o) (i j) : blockDiag M
 k i j = M (i, k) (j, k)
参数：M : Matrix (m × o) (n × o) α；k : o；i j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem blockDiag_apply (M : Matrix (m × o) (n × o) α) (k : o) (i j) :
    blockDiag M k i j = M (i, k) (j, k) :=
  rfl
/-
**Matrix.blockDiag_map** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockDiag_map (M : Matrix (m × o) (n × o) α) (f : α -> β) : blockDiag (M.m
ap f) = fun k => (blockDiag M k).map f
参数：M : Matrix (m × o) (n × o) α；f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem blockDiag_map (M : Matrix (m × o) (n × o) α) (f : α → β) :
    blockDiag (M.map f) = fun k => (blockDiag M k).map f :=
  rfl

@[simp]
/-
**Matrix.blockDiag_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockDiag_transpose (M : Matrix (m × o) (n × o) α) (k : o) : blockDiag Mᵀ 
k = (blockDiag M k)ᵀ
参数：M : Matrix (m × o) (n × o) α；k : o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem blockDiag_transpose (M : Matrix (m × o) (n × o) α) (k : o) :
    blockDiag Mᵀ k = (blockDiag M k)ᵀ :=
  ext fun _ _ => rfl

@[simp]
/-
**Matrix.blockDiag_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockDiag_conjTranspose {α : Type*} [Star α] (M : Matrix (m × o) (n × o) α
) (k : o) : blockDiag Mᴴ k = (blockDiag M k)ᴴ
参数：M : Matrix (m × o) (n × o) α；k : o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem blockDiag_conjTranspose {α : Type*} [Star α]
    (M : Matrix (m × o) (n × o) α) (k : o) : blockDiag Mᴴ k = (blockDiag M k)ᴴ :=
  ext fun _ _ => rfl

section Zero

variable [Zero α] [Zero β]

@[simp]
/-
**Matrix.blockDiag_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockDiag_zero : blockDiag (0 : Matrix (m × o) (n × o) α) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem blockDiag_zero : blockDiag (0 : Matrix (m × o) (n × o) α) = 0 :=
  rfl

@[simp]
/-
**Matrix.blockDiag_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockDiag_diagonal [DecidableEq o] [DecidableEq m] (d : m × o -> α) (k : o
) : blockDiag (diagonal d) k = diagonal fun i => d (i, k)
参数：d : m × o -> α；k : o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Decidable.eq_or_ne`：Decidable.eq_or_ne {α : Sort*} (x y : α) [Decidable 
(x = y)] : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.blockDiag_apply`：blockDiag_apply (M : Matrix (m × o) (n × o) α) (
k : o) (i j) : blockDiag M k i j = M (i, k) (j, k)
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Prod.fst_eq_iff`：∀ {α : Type u_1} {β : Type u_2} {p : α × β} {x : α}, p.
1 = x ↔ p = (x, p.2)
-/
theorem blockDiag_diagonal [DecidableEq o] [DecidableEq m] (d : m × o → α) (k : o) :
    blockDiag (diagonal d) k = diagonal fun i => d (i, k) :=
  ext fun i j => by
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [blockDiag_apply, diagonal_apply_eq, diagonal_apply_eq]
    · rw [blockDiag_apply, diagonal_apply_ne _ hij, diagonal_apply_ne _ (mt _ hij)]
      exact Prod.fst_eq_iff.mpr

@[simp]
/-
**Matrix.blockDiag_blockDiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockDiag_blockDiagonal [DecidableEq o] (M : o -> Matrix m n α) : blockDia
g (blockDiagonal M) = M
参数：M : o -> Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Matrix.blockDiagonal_apply_eq`：blockDiagonal_apply_eq (M : o -> Matrix m
 n α) (i j k) : blockDiagonal M (i, k) (j, k) = M k i j
-/
theorem blockDiag_blockDiagonal [DecidableEq o] (M : o → Matrix m n α) :
    blockDiag (blockDiagonal M) = M :=
  funext fun _ => ext fun i j => blockDiagonal_apply_eq M i j _
/-
**Matrix.blockDiagonal_injective** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockDiagonal_injective [DecidableEq o] : Function.Injective (blockDiagona
l : (o -> Matrix m n α) -> Matrix _ _ α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `Matrix.blockDiag_blockDiagonal`：blockDiag_blockDiagonal [DecidableEq o] 
(M : o -> Matrix m n α) : blockDiag (blockDiagonal M) = M
-/
theorem blockDiagonal_injective [DecidableEq o] :
    Function.Injective (blockDiagonal : (o → Matrix m n α) → Matrix _ _ α) :=
  Function.LeftInverse.injective blockDiag_blockDiagonal

@[simp]
/-
**Matrix.blockDiagonal_inj** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockDiagonal_inj [DecidableEq o] {M N : o -> Matrix m n α} : blockDiagona
l M = blockDiagonal N ↔ M = N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Matrix.blockDiagonal_injective`：blockDiagonal_injective [DecidableEq o] 
: Function.Injective (blockDiagonal : (o -> Matrix m n α) -> Matrix _ _ α)
-/
theorem blockDiagonal_inj [DecidableEq o] {M N : o → Matrix m n α} :
    blockDiagonal M = blockDiagonal N ↔ M = N :=
  blockDiagonal_injective.eq_iff

@[simp]
/-
**Matrix.blockDiag_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockDiag_one [DecidableEq o] [DecidableEq m] [One α] : blockDiag (1 : Mat
rix (m × o) (m × o) α) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.blockDiag_diagonal`：blockDiag_diagonal [DecidableEq o] [Decidable
Eq m] (d : m × o -> α) (k : o) : blockDiag (diagonal d) k = diagonal fun i => d 
(i, k)
-/
theorem blockDiag_one [DecidableEq o] [DecidableEq m] [One α] :
    blockDiag (1 : Matrix (m × o) (m × o) α) = 1 :=
  funext <| blockDiag_diagonal _

end Zero

@[simp]
/-
**Matrix.blockDiag_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockDiag_add [Add α] (M N : Matrix (m × o) (n × o) α) : blockDiag (M + N)
 = blockDiag M + blockDiag N
参数：M N : Matrix (m × o) (n × o) α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem blockDiag_add [Add α] (M N : Matrix (m × o) (n × o) α) :
    blockDiag (M + N) = blockDiag M + blockDiag N :=
  rfl

section

variable (o m n α)

/-- `Matrix.blockDiag` as an `AddMonoidHom`. -/
@[simps]
/-
**Matrix.blockDiagAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：blockDiagAddMonoidHom [AddZeroClass α] : Matrix (m × o) (n × o) α ->+ o ->
 Matrix m n α where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.blockDiag` as an `AddMonoidHom`.
-/
def blockDiagAddMonoidHom [AddZeroClass α] : Matrix (m × o) (n × o) α →+ o → Matrix m n α where
  toFun := blockDiag
  map_zero' := blockDiag_zero
  map_add' := blockDiag_add

end

@[simp]
/-
**Matrix.blockDiag_neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockDiag_neg [AddGroup α] (M : Matrix (m × o) (n × o) α) : blockDiag (-M)
 = -blockDiag M
参数：M : Matrix (m × o) (n × o) α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem blockDiag_neg [AddGroup α] (M : Matrix (m × o) (n × o) α) : blockDiag (-M) = -blockDiag M :=
  map_neg (blockDiagAddMonoidHom m n o α) M

@[simp]
/-
**Matrix.blockDiag_sub** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockDiag_sub [AddGroup α] (M N : Matrix (m × o) (n × o) α) : blockDiag (M
 - N) = blockDiag M - blockDiag N
参数：M N : Matrix (m × o) (n × o) α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem blockDiag_sub [AddGroup α] (M N : Matrix (m × o) (n × o) α) :
    blockDiag (M - N) = blockDiag M - blockDiag N :=
  map_sub (blockDiagAddMonoidHom m n o α) M N

@[simp]
/-
**Matrix.blockDiag_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockDiag_smul {R : Type*} [SMul R α] (x : R) (M : Matrix (m × o) (n × o) 
α) : blockDiag (x • M) = x • blockDiag M
参数：x : R；M : Matrix (m × o) (n × o) α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem blockDiag_smul {R : Type*} [SMul R α] (x : R)
    (M : Matrix (m × o) (n × o) α) : blockDiag (x • M) = x • blockDiag M :=
  rfl

end BlockDiag

section BlockDiagonal'

variable [DecidableEq o]

section Zero

variable [Zero α] [Zero β]

/-- `Matrix.blockDiagonal' M` turns `M : Π i, Matrix (m i) (n i) α` into a
`Σ i, m i`-by-`Σ i, n i` block matrix which has the entries of `M` along the diagonal
and zero elsewhere.

This is the dependently-typed version of `Matrix.blockDiagonal`. -/
/-
**Matrix.blockDiagonal'** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：blockDiagonal' (M : forall i, Matrix (m' i) (n' i) α) : Matrix (Σ i, m' i)
 (Σ i, n' i) α
参数：M : forall i, Matrix (m' i) (n' i) α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.blockDiagonal' M` turns `M : Π i, Matrix (m i) (n i) α` into a
`Σ i, m i`-by-`Σ i, n i` block matrix which has the entries of `M` along the dia
gonal
and zero elsewhere.

This is the dependently-typed version of `Matrix.blockDiagonal`.
-/
def blockDiagonal' (M : ∀ i, Matrix (m' i) (n' i) α) : Matrix (Σ i, m' i) (Σ i, n' i) α :=
  of <|
    (fun ⟨k, i⟩ ⟨k', j⟩ => if h : k = k' then M k i (cast (congr_arg n' h.symm) j) else 0 :
      (Σ i, m' i) → (Σ i, n' i) → α)

-- TODO: set as an equation lemma for `blockDiagonal'`, see https://github.com/leanprover-community/mathlib4/pull/3024
/-
**Matrix.blockDiagonal'_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {o : Type u_4} {m' : o → Type u_7} {n' : o → Type u_8} {α : Type u_12} [
inst : DecidableEq o] [inst_1 : Zero α]   (M : (i : o) → Matrix (m' i) (n' i) α)
 (k : o) (i : m' k) (k' : o) (j : n' k'),   Matrix.blockDiagonal' M ⟨k, i⟩ ⟨k', 
j⟩ = if h : k = k' then M k i (cast ⋯ j) else 0
参数：M : (i : o) → Matrix (m' i) (n' i) α；k : o；i : m' k；k' : o；j : n' k'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem blockDiagonal'_apply' (M : ∀ i, Matrix (m' i) (n' i) α) (k i k' j) :
    blockDiagonal' M ⟨k, i⟩ ⟨k', j⟩ =
      if h : k = k' then M k i (cast (congr_arg n' h.symm) j) else 0 :=
  rfl
/-
**Matrix.blockDiagonal'_eq_blockDiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type u_12} [inst : Dec
idableEq o] [inst_1 : Zero α]   (M : o → Matrix m n α) {k k' : o} (i : m) (j : n
),   Matrix.blockDiagonal M (i, k) (j, k') = Matrix.blockDiagonal' M ⟨k, i⟩ ⟨k',
 j⟩
参数：M : o → Matrix m n α；i : m；j : n；i, k；j, k'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem blockDiagonal'_eq_blockDiagonal (M : o → Matrix m n α) {k k'} (i j) :
    blockDiagonal M (i, k) (j, k') = blockDiagonal' M ⟨k, i⟩ ⟨k', j⟩ :=
  rfl
/-
**Matrix.blockDiagonal'_submatrix_eq_blockDiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Ma
trix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type u_12} [inst : Dec
idableEq o] [inst_1 : Zero α]   (M : o → Matrix m n α),   (Matrix.blockDiagonal'
 M).submatrix (Prod.toSigma ∘ Prod.swap) (Prod.toSigma ∘ Prod.swap) = Matrix.blo
ckDiagonal M
参数：M : o → Matrix m n α；Matrix.blockDiagonal' M；Prod.toSigma ∘ Prod.swap；Prod.to
Sigma ∘ Prod.swap。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem blockDiagonal'_submatrix_eq_blockDiagonal (M : o → Matrix m n α) :
    (blockDiagonal' M).submatrix (Prod.toSigma ∘ Prod.swap) (Prod.toSigma ∘ Prod.swap) =
      blockDiagonal M :=
  Matrix.ext fun ⟨_, _⟩ ⟨_, _⟩ => rfl
/-
**Matrix.blockDiagonal'_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {o : Type u_4} {m' : o → Type u_7} {n' : o → Type u_8} {α : Type u_12} [
inst : DecidableEq o] [inst_1 : Zero α]   (M : (i : o) → Matrix (m' i) (n' i) α)
 (ik : (i : o) × m' i) (jk : (i : o) × n' i),   Matrix.blockDiagonal' M ik jk = 
if h : ik.fst = jk.fst then M ik.fst ik.snd (cast ⋯ jk.snd) else 0
参数：M : (i : o) → Matrix (m' i) (n' i) α；ik : (i : o) × m' i；jk : (i : o) × n' i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem blockDiagonal'_apply (M : ∀ i, Matrix (m' i) (n' i) α) (ik jk) :
    blockDiagonal' M ik jk =
      if h : ik.1 = jk.1 then M ik.1 ik.2 (cast (congr_arg n' h.symm) jk.2) else 0 := rfl

@[simp]
/-
**Matrix.blockDiagonal'_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {o : Type u_4} {m' : o → Type u_7} {n' : o → Type u_8} {α : Type u_12} [
inst : DecidableEq o] [inst_1 : Zero α]   (M : (i : o) → Matrix (m' i) (n' i) α)
 (k : o) (i : m' k) (j : n' k), Matrix.blockDiagonal' M ⟨k, i⟩ ⟨k, j⟩ = M k i j
参数：M : (i : o) → Matrix (m' i) (n' i) α；k : o；i : m' k；j : n' k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem blockDiagonal'_apply_eq (M : ∀ i, Matrix (m' i) (n' i) α) (k i j) :
    blockDiagonal' M ⟨k, i⟩ ⟨k, j⟩ = M k i j :=
  dif_pos rfl
/-
**Matrix.blockDiagonal'_apply_ne** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {o : Type u_4} {m' : o → Type u_7} {n' : o → Type u_8} {α : Type u_12} [
inst : DecidableEq o] [inst_1 : Zero α]   (M : (i : o) → Matrix (m' i) (n' i) α)
 {k k' : o} (i : m' k) (j : n' k'),   k ≠ k' → Matrix.blockDiagonal' M ⟨k, i⟩ ⟨k
', j⟩ = 0
参数：M : (i : o) → Matrix (m' i) (n' i) α；i : m' k；j : n' k'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem blockDiagonal'_apply_ne (M : ∀ i, Matrix (m' i) (n' i) α) {k k'} (i j) (h : k ≠ k') :
    blockDiagonal' M ⟨k, i⟩ ⟨k', j⟩ = 0 :=
  dif_neg h
/-
**Matrix.blockDiagonal'_map** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {o : Type u_4} {m' : o → Type u_7} {n' : o → Type u_8} {α : Type u_12} {
β : Type u_13} [inst : DecidableEq o]   [inst_1 : Zero α] [inst_2 : Zero β] (M :
 (i : o) → Matrix (m' i) (n' i) α) (f : α → β),   f 0 = 0 → (Matrix.blockDiagona
l' M).map f = Matrix.blockDiagonal' fun k => (M k).map f
参数：M : (i : o) → Matrix (m' i) (n' i) α；f : α → β；Matrix.blockDiagonal' M；M k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `apply_dite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst
 : Decidable P] (x : P → α) (y : ¬P → α),   f (dite P x y) = if h : P then f (x 
…
-/
theorem blockDiagonal'_map (M : ∀ i, Matrix (m' i) (n' i) α) (f : α → β) (hf : f 0 = 0) :
    (blockDiagonal' M).map f = blockDiagonal' fun k => (M k).map f := by
  ext
  simp only [map_apply, blockDiagonal'_apply]
  rw [apply_dite f, hf]

@[simp]
/-
**Matrix.blockDiagonal'_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {o : Type u_4} {m' : o → Type u_7} {n' : o → Type u_8} {α : Type u_12} [
inst : DecidableEq o] [inst_1 : Zero α]   (M : (i : o) → Matrix (m' i) (n' i) α)
,   (Matrix.blockDiagonal' M).transpose = Matrix.blockDiagonal' fun k => (M k).t
ranspose
参数：M : (i : o) → Matrix (m' i) (n' i) α；Matrix.blockDiagonal' M；M k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem blockDiagonal'_transpose (M : ∀ i, Matrix (m' i) (n' i) α) :
    (blockDiagonal' M)ᵀ = blockDiagonal' fun k => (M k)ᵀ := by
  ext ⟨ii, ix⟩ ⟨ji, jx⟩
  simp only [transpose_apply, blockDiagonal'_apply]
  split_ifs <;> grind

@[simp]
/-
**Matrix.blockDiagonal'_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {o : Type u_4} {m' : o → Type u_7} {n' : o → Type u_8} [inst : Decidable
Eq o] {α : Type u_14} [inst_1 : AddMonoid α]   [inst_2 : StarAddMonoid α] (M : (
i : o) → Matrix (m' i) (n' i) α),   (Matrix.blockDiagonal' M).conjTranspose = Ma
trix.blockDiagonal' fun k => (M k).conjTranspose
参数：M : (i : o) → Matrix (m' i) (n' i) α；Matrix.blockDiagonal' M；M k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.blockDiagonal'_transpose`：∀ {o : Type u_4} {m' : o → Type u_7} {n
' : o → Type u_8} {α : Type u_12} [inst : DecidableEq o] [inst_1 : Zero α]   (M 
: (i : o) → Matrix (m…
· 使用定理 `Matrix.blockDiagonal'_map`：∀ {o : Type u_4} {m' : o → Type u_7} {n' : o 
→ Type u_8} {α : Type u_12} {β : Type u_13} [inst : DecidableEq o]   [inst_1 : Z
ero α] [inst_2 …
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
-/
theorem blockDiagonal'_conjTranspose {α} [AddMonoid α] [StarAddMonoid α]
    (M : ∀ i, Matrix (m' i) (n' i) α) : (blockDiagonal' M)ᴴ = blockDiagonal' fun k => (M k)ᴴ := by
  simp only [conjTranspose, blockDiagonal'_transpose]
  exact blockDiagonal'_map _ star (star_zero α)

@[simp]
/-
**Matrix.blockDiagonal'_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {o : Type u_4} {m' : o → Type u_7} {n' : o → Type u_8} {α : Type u_12} [
inst : DecidableEq o] [inst_1 : Zero α],   Matrix.blockDiagonal' 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem blockDiagonal'_zero : blockDiagonal' (0 : ∀ i, Matrix (m' i) (n' i) α) = 0 := by
  ext
  simp [blockDiagonal'_apply]

@[simp]
/-
**Matrix.blockDiagonal'_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {o : Type u_4} {m' : o → Type u_7} {α : Type u_12} [inst : DecidableEq o
] [inst_1 : Zero α]   [inst_2 : (i : o) → DecidableEq (m' i)] (d : (i : o) → m' 
i → α),   (Matrix.blockDiagonal' fun k => Matrix.diagonal (d k)) = Matrix.diagon
al fun ik => d ik.fst ik.snd
参数：i : o；m' i；d : (i : o) → m' i → α；Matrix.blockDiagonal' fun k => Matrix.diago
nal (d k)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Decidable.eq_or_ne`：Decidable.eq_or_ne {α : Sort*} (x y : α) [Decidable 
(x = y)] : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
-/
theorem blockDiagonal'_diagonal [∀ i, DecidableEq (m' i)] (d : ∀ i, m' i → α) :
    (blockDiagonal' fun k => diagonal (d k)) = diagonal fun ik => d ik.1 ik.2 := by
  ext ⟨i, k⟩ ⟨j, k'⟩
  simp only [blockDiagonal'_apply, diagonal]
  obtain rfl | hij := Decidable.eq_or_ne i j
  · simp
  · simp [hij]

@[simp]
/-
**Matrix.blockDiagonal'_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {o : Type u_4} {m' : o → Type u_7} {α : Type u_12} [inst : DecidableEq o
] [inst_1 : Zero α]   [inst_2 : (i : o) → DecidableEq (m' i)] [inst_3 : One α], 
Matrix.blockDiagonal' 1 = 1
参数：i : o；m' i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.blockDiagonal'_diagonal`：∀ {o : Type u_4} {m' : o → Type u_7} {α 
: Type u_12} [inst : DecidableEq o] [inst_1 : Zero α]   [inst_2 : (i : o) → Deci
dableEq (m' i)] (d :…
-/
theorem blockDiagonal'_one [∀ i, DecidableEq (m' i)] [One α] :
    blockDiagonal' (1 : ∀ i, Matrix (m' i) (m' i) α) = 1 :=
  show (blockDiagonal' fun i : o => diagonal fun _ : m' i => (1 : α)) = diagonal fun _ => 1 by
    rw [blockDiagonal'_diagonal]

end Zero

@[simp]
/-
**Matrix.blockDiagonal'_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {o : Type u_4} {m' : o → Type u_7} {n' : o → Type u_8} {α : Type u_12} [
inst : DecidableEq o]   [inst_1 : AddZeroClass α] (M N : (i : o) → Matrix (m' i)
 (n' i) α),   Matrix.blockDiagonal' (M + N) = Matrix.blockDiagonal' M + Matrix.b
lockDiagonal' N
参数：M N : (i : o) → Matrix (m' i) (n' i) α；M + N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem blockDiagonal'_add [AddZeroClass α] (M N : ∀ i, Matrix (m' i) (n' i) α) :
    blockDiagonal' (M + N) = blockDiagonal' M + blockDiagonal' N := by
  ext
  simp only [blockDiagonal'_apply, Pi.add_apply, add_apply]
  split_ifs <;> simp

section

variable (m' n' α)

/-- `Matrix.blockDiagonal'` as an `AddMonoidHom`. -/
@[simps]
/-
**Matrix.blockDiagonal'AddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{o : Type u_4} →   (m' : o → Type u_7) →     (n' : o → Type u_8) →       (
α : Type u_12) →         [DecidableEq o] →           [inst : AddZeroClass α] → (
(i : o) → Matrix (m' i) (n' i) α) →+ Matrix ((i : o) × m' i) ((i : o) × n' i) α
参数：m' : o → Type u_7；n' : o → Type u_8；α : Type u_12；(i : o) → Matrix (m' i) (n'
 i) α；(i : o) × m' i；(i : o) × n' i。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.blockDiagonal'_add`：∀ {o : Type u_4} {m' : o → Type u_7} {n' : o 
→ Type u_8} {α : Type u_12} [inst : DecidableEq o]   [inst_1 : AddZeroClass α] (
M N : (i : o) →…

--- 原说明 ---
`Matrix.blockDiagonal'` as an `AddMonoidHom`.
-/
def blockDiagonal'AddMonoidHom [AddZeroClass α] :
    (∀ i, Matrix (m' i) (n' i) α) →+ Matrix (Σ i, m' i) (Σ i, n' i) α where
  toFun := blockDiagonal'
  map_zero' := blockDiagonal'_zero
  map_add' := blockDiagonal'_add

end

@[simp]
/-
**Matrix.blockDiagonal'_neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {o : Type u_4} {m' : o → Type u_7} {n' : o → Type u_8} {α : Type u_12} [
inst : DecidableEq o] [inst_1 : AddGroup α]   (M : (i : o) → Matrix (m' i) (n' i
) α), Matrix.blockDiagonal' (-M) = -Matrix.blockDiagonal' M
参数：M : (i : o) → Matrix (m' i) (n' i) α；-M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem blockDiagonal'_neg [AddGroup α] (M : ∀ i, Matrix (m' i) (n' i) α) :
    blockDiagonal' (-M) = -blockDiagonal' M :=
  map_neg (blockDiagonal'AddMonoidHom m' n' α) M

@[simp]
/-
**Matrix.blockDiagonal'_sub** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {o : Type u_4} {m' : o → Type u_7} {n' : o → Type u_8} {α : Type u_12} [
inst : DecidableEq o] [inst_1 : AddGroup α]   (M N : (i : o) → Matrix (m' i) (n'
 i) α),   Matrix.blockDiagonal' (M - N) = Matrix.blockDiagonal' M - Matrix.block
Diagonal' N
参数：M N : (i : o) → Matrix (m' i) (n' i) α；M - N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem blockDiagonal'_sub [AddGroup α] (M N : ∀ i, Matrix (m' i) (n' i) α) :
    blockDiagonal' (M - N) = blockDiagonal' M - blockDiagonal' N :=
  map_sub (blockDiagonal'AddMonoidHom m' n' α) M N

@[simp]
/-
**Matrix.blockDiagonal'_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {o : Type u_4} {m' : o → Type u_7} {n' : o → Type u_8} {p' : o → Type u_
9} {α : Type u_12} [inst : DecidableEq o]   [inst_1 : NonUnitalNonAssocSemiring 
α] [inst_2 : (i : o) → Fintype (n' i)] [inst_3 : Fintype o]   (M : (i : o) → Mat
rix (m' i) (n' i) α) (N : (i : o) → Matrix (n' i) (p' i) α),   (Matrix.blockDiag
onal' fun k => M k * N k) = Matrix.blockDiagonal' M * Matrix.blockDiagonal' N
参数：i : o；n' i；M : (i : o) → Matrix (m' i) (n' i) α；N : (i : o) → Matrix (n' i) (
p' i) α；Matrix.blockDiagonal' fun k => M k * N k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Finset.sum_sigma`：∀ {α : Type u_3} {β : Type u_4} [inst : AddCommMonoid 
β] {σ : α → Type u_6} (s : Finset α) (t : (a : α) → Finset (σ a))   (f : Sigma σ
 → β),…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Fintype.sum_eq_single`：∀ {α : Type u_1} {M : Type u_4} [inst : Fintype α
] [inst_1 : AddCommMonoid M] {f : α → M} (a : α),   (∀ (x : α), x ≠ a → f x = 0)
 → ∑ x, f x…
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
-/
theorem blockDiagonal'_mul [NonUnitalNonAssocSemiring α] [∀ i, Fintype (n' i)] [Fintype o]
    (M : ∀ i, Matrix (m' i) (n' i) α) (N : ∀ i, Matrix (n' i) (p' i) α) :
    (blockDiagonal' fun k => M k * N k) = blockDiagonal' M * blockDiagonal' N := by
  ext ⟨k, i⟩ ⟨k', j⟩
  simp only [blockDiagonal'_apply, mul_apply, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Fintype.sum_eq_single k]
  · simp only [dif_pos]
    split_ifs <;> simp
  · intro j' hj'
    exact Finset.sum_eq_zero fun _ _ => by rw [dif_neg hj'.symm, zero_mul]

section

variable (α m')

/-- `Matrix.blockDiagonal'` as a `RingHom`. -/
@[simps]
/-
**Matrix.blockDiagonal'RingHom** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{o : Type u_4} →   (m' : o → Type u_7) →     (α : Type u_12) →       [inst
 : DecidableEq o] →         [inst_1 : (i : o) → DecidableEq (m' i)] →           
[inst_2 : Fintype o] →             [inst_3 : (i : o) → Fintype (m' i)] →        
       [inst_4 : NonAssocSemiring α] →                 ((i : o) → Matrix (m' i) 
(m' i) α) →+* Matrix ((i : o) × m' i) ((i : o) × m' i) α
参数：m' : o → Type u_7；α : Type u_12；i : o；m' i；i : o；m' i；(i : o) → Matrix (m' i)
 (m' i) α；(i : o) × m' i；(i : o) × m' i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.blockDiagonal'` as a `RingHom`.
-/
def blockDiagonal'RingHom [∀ i, DecidableEq (m' i)] [Fintype o] [∀ i, Fintype (m' i)]
    [NonAssocSemiring α] : (∀ i, Matrix (m' i) (m' i) α) →+* Matrix (Σ i, m' i) (Σ i, m' i) α :=
  { blockDiagonal'AddMonoidHom m' m' α with
    toFun := blockDiagonal'
    map_one' := blockDiagonal'_one
    map_mul' := blockDiagonal'_mul }

end

@[simp]
/-
**Matrix.blockDiagonal'_pow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {o : Type u_4} {m' : o → Type u_7} {α : Type u_12} [inst : DecidableEq o
] [inst_1 : (i : o) → DecidableEq (m' i)]   [inst_2 : Fintype o] [inst_3 : (i : 
o) → Fintype (m' i)] [inst_4 : Semiring α] (M : (i : o) → Matrix (m' i) (m' i) α
)   (n : ℕ), Matrix.blockDiagonal' (M ^ n) = Matrix.blockDiagonal' M ^ n
参数：i : o；m' i；i : o；m' i；M : (i : o) → Matrix (m' i) (m' i) α；n : ℕ；M ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem blockDiagonal'_pow [∀ i, DecidableEq (m' i)] [Fintype o] [∀ i, Fintype (m' i)] [Semiring α]
    (M : ∀ i, Matrix (m' i) (m' i) α) (n : ℕ) : blockDiagonal' (M ^ n) = blockDiagonal' M ^ n :=
  map_pow (blockDiagonal'RingHom m' α) M n

@[simp]
/-
**Matrix.blockDiagonal'_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {o : Type u_4} {m' : o → Type u_7} {n' : o → Type u_8} {α : Type u_12} [
inst : DecidableEq o] {R : Type u_14}   [inst_1 : Zero α] [inst_2 : SMulZeroClas
s R α] (x : R) (M : (i : o) → Matrix (m' i) (n' i) α),   Matrix.blockDiagonal' (
x • M) = x • Matrix.blockDiagonal' M
参数：x : R；M : (i : o) → Matrix (m' i) (n' i) α；x • M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem blockDiagonal'_smul {R : Type*} [Zero α] [SMulZeroClass R α] (x : R)
    (M : ∀ i, Matrix (m' i) (n' i) α) : blockDiagonal' (x • M) = x • blockDiagonal' M := by
  ext
  simp only [blockDiagonal'_apply, Pi.smul_apply, smul_apply]
  split_ifs <;> simp

end BlockDiagonal'

section BlockDiag'

/-- Extract a block from the diagonal of a block diagonal matrix.

This is the block form of `Matrix.diag`, and the left-inverse of `Matrix.blockDiagonal'`. -/
/-
**Matrix.blockDiag'** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：blockDiag' (M : Matrix (Σ i, m' i) (Σ i, n' i) α) (k : o) : Matrix (m' k) 
(n' k) α
参数：M : Matrix (Σ i, m' i) (Σ i, n' i) α；k : o。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract a block from the diagonal of a block diagonal matrix.

This is the block form of `Matrix.diag`, and the left-inverse of `Matrix.blockDi
agonal'`.
-/
def blockDiag' (M : Matrix (Σ i, m' i) (Σ i, n' i) α) (k : o) : Matrix (m' k) (n' k) α :=
  of fun i j => M ⟨k, i⟩ ⟨k, j⟩

-- TODO: set as an equation lemma for `blockDiag'`, see https://github.com/leanprover-community/mathlib4/pull/3024
/-
**Matrix.blockDiag'_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {o : Type u_4} {m' : o → Type u_7} {n' : o → Type u_8} {α : Type u_12}  
 (M : Matrix ((i : o) × m' i) ((i : o) × n' i) α) (k : o) (i : m' k) (j : n' k),
 M.blockDiag' k i j = M ⟨k, i⟩ ⟨k, j⟩
参数：M : Matrix ((i : o) × m' i) ((i : o) × n' i) α；k : o；i : m' k；j : n' k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem blockDiag'_apply (M : Matrix (Σ i, m' i) (Σ i, n' i) α) (k : o) (i j) :
    blockDiag' M k i j = M ⟨k, i⟩ ⟨k, j⟩ :=
  rfl
/-
**Matrix.blockDiag'_map** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {o : Type u_4} {m' : o → Type u_7} {n' : o → Type u_8} {α : Type u_12} {
β : Type u_13}   (M : Matrix ((i : o) × m' i) ((i : o) × n' i) α) (f : α → β), (
M.map f).blockDiag' = fun k => (M.blockDiag' k).map f
参数：M : Matrix ((i : o) × m' i) ((i : o) × n' i) α；f : α → β；M.map f；M.blockDiag'
 k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem blockDiag'_map (M : Matrix (Σ i, m' i) (Σ i, n' i) α) (f : α → β) :
    blockDiag' (M.map f) = fun k => (blockDiag' M k).map f :=
  rfl

@[simp]
/-
**Matrix.blockDiag'_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {o : Type u_4} {m' : o → Type u_7} {n' : o → Type u_8} {α : Type u_12}  
 (M : Matrix ((i : o) × m' i) ((i : o) × n' i) α) (k : o), M.transpose.blockDiag
' k = (M.blockDiag' k).transpose
参数：M : Matrix ((i : o) × m' i) ((i : o) × n' i) α；k : o；M.blockDiag' k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem blockDiag'_transpose (M : Matrix (Σ i, m' i) (Σ i, n' i) α) (k : o) :
    blockDiag' Mᵀ k = (blockDiag' M k)ᵀ :=
  ext fun _ _ => rfl

@[simp]
/-
**Matrix.blockDiag'_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {o : Type u_4} {m' : o → Type u_7} {n' : o → Type u_8} {α : Type u_14} [
inst : Star α]   (M : Matrix ((i : o) × m' i) ((i : o) × n' i) α) (k : o),   M.c
onjTranspose.blockDiag' k = (M.blockDiag' k).conjTranspose
参数：M : Matrix ((i : o) × m' i) ((i : o) × n' i) α；k : o；M.blockDiag' k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem blockDiag'_conjTranspose {α : Type*} [Star α]
    (M : Matrix (Σ i, m' i) (Σ i, n' i) α) (k : o) : blockDiag' Mᴴ k = (blockDiag' M k)ᴴ :=
  ext fun _ _ => rfl

section Zero

variable [Zero α] [Zero β]

@[simp]
/-
**Matrix.blockDiag'_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {o : Type u_4} {m' : o → Type u_7} {n' : o → Type u_8} {α : Type u_12} [
inst : Zero α], Matrix.blockDiag' 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem blockDiag'_zero : blockDiag' (0 : Matrix (Σ i, m' i) (Σ i, n' i) α) = 0 :=
  rfl

@[simp]
/-
**Matrix.blockDiag'_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {o : Type u_4} {m' : o → Type u_7} {α : Type u_12} [inst : Zero α] [inst
_1 : DecidableEq o]   [inst_2 : (i : o) → DecidableEq (m' i)] (d : (i : o) × m' 
i → α) (k : o),   (Matrix.diagonal d).blockDiag' k = Matrix.diagonal fun i => d 
⟨k, i⟩
参数：i : o；m' i；d : (i : o) × m' i → α；k : o；Matrix.diagonal d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Decidable.eq_or_ne`：Decidable.eq_or_ne {α : Sort*} (x y : α) [Decidable 
(x = y)] : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.blockDiag'_apply`：∀ {o : Type u_4} {m' : o → Type u_7} {n' : o → 
Type u_8} {α : Type u_12}   (M : Matrix ((i : o) × m' i) ((i : o) × n' i) α) (k 
: o) (i : m' …
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem blockDiag'_diagonal
    [DecidableEq o] [∀ i, DecidableEq (m' i)] (d : (Σ i, m' i) → α) (k : o) :
    blockDiag' (diagonal d) k = diagonal fun i => d ⟨k, i⟩ :=
  ext fun i j => by
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [blockDiag'_apply, diagonal_apply_eq, diagonal_apply_eq]
    · rw [blockDiag'_apply, diagonal_apply_ne _ hij, diagonal_apply_ne _ (mt (fun h => ?_) hij)]
      cases h
      rfl

@[simp]
/-
**Matrix.blockDiag'_blockDiagonal'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {o : Type u_4} {m' : o → Type u_7} {n' : o → Type u_8} {α : Type u_12} [
inst : Zero α] [inst_1 : DecidableEq o]   (M : (i : o) → Matrix (m' i) (n' i) α)
, (Matrix.blockDiagonal' M).blockDiag' = M
参数：M : (i : o) → Matrix (m' i) (n' i) α；Matrix.blockDiagonal' M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Matrix.blockDiagonal'_apply_eq`：∀ {o : Type u_4} {m' : o → Type u_7} {n'
 : o → Type u_8} {α : Type u_12} [inst : DecidableEq o] [inst_1 : Zero α]   (M :
 (i : o) → Matrix (m…
-/
theorem blockDiag'_blockDiagonal' [DecidableEq o] (M : ∀ i, Matrix (m' i) (n' i) α) :
    blockDiag' (blockDiagonal' M) = M :=
  funext fun _ => ext fun _ _ => blockDiagonal'_apply_eq M _ _ _
/-
**Matrix.blockDiagonal'_injective** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {o : Type u_4} {m' : o → Type u_7} {n' : o → Type u_8} {α : Type u_12} [
inst : Zero α] [inst_1 : DecidableEq o],   Function.Injective Matrix.blockDiagon
al'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `Matrix.blockDiag'_blockDiagonal'`：∀ {o : Type u_4} {m' : o → Type u_7} {
n' : o → Type u_8} {α : Type u_12} [inst : Zero α] [inst_1 : DecidableEq o]   (M
 : (i : o) → Matrix (m…
-/
theorem blockDiagonal'_injective [DecidableEq o] :
    Function.Injective (blockDiagonal' : (∀ i, Matrix (m' i) (n' i) α) → Matrix _ _ α) :=
  Function.LeftInverse.injective blockDiag'_blockDiagonal'

@[simp]
/-
**Matrix.blockDiagonal'_inj** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {o : Type u_4} {m' : o → Type u_7} {n' : o → Type u_8} {α : Type u_12} [
inst : Zero α] [inst_1 : DecidableEq o]   {M N : (i : o) → Matrix (m' i) (n' i) 
α}, Matrix.blockDiagonal' M = Matrix.blockDiagonal' N ↔ M = N
参数：i : o；m' i；n' i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Matrix.blockDiagonal'_injective`：∀ {o : Type u_4} {m' : o → Type u_7} {n
' : o → Type u_8} {α : Type u_12} [inst : Zero α] [inst_1 : DecidableEq o],   Fu
nction.Injective Matr…
-/
theorem blockDiagonal'_inj [DecidableEq o] {M N : ∀ i, Matrix (m' i) (n' i) α} :
    blockDiagonal' M = blockDiagonal' N ↔ M = N :=
  blockDiagonal'_injective.eq_iff

@[simp]
/-
**Matrix.blockDiag'_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {o : Type u_4} {m' : o → Type u_7} {α : Type u_12} [inst : Zero α] [inst
_1 : DecidableEq o]   [inst_2 : (i : o) → DecidableEq (m' i)] [inst_3 : One α], 
Matrix.blockDiag' 1 = 1
参数：i : o；m' i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.blockDiag'_diagonal`：∀ {o : Type u_4} {m' : o → Type u_7} {α : Ty
pe u_12} [inst : Zero α] [inst_1 : DecidableEq o]   [inst_2 : (i : o) → Decidabl
eEq (m' i)] (d :…
-/
theorem blockDiag'_one [DecidableEq o] [∀ i, DecidableEq (m' i)] [One α] :
    blockDiag' (1 : Matrix (Σ i, m' i) (Σ i, m' i) α) = 1 :=
  funext <| blockDiag'_diagonal _

end Zero

@[simp]
/-
**Matrix.blockDiag'_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {o : Type u_4} {m' : o → Type u_7} {n' : o → Type u_8} {α : Type u_12} [
inst : Add α]   (M N : Matrix ((i : o) × m' i) ((i : o) × n' i) α), (M + N).bloc
kDiag' = M.blockDiag' + N.blockDiag'
参数：M N : Matrix ((i : o) × m' i) ((i : o) × n' i) α；M + N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem blockDiag'_add [Add α] (M N : Matrix (Σ i, m' i) (Σ i, n' i) α) :
    blockDiag' (M + N) = blockDiag' M + blockDiag' N :=
  rfl

section

variable (m' n' α)

/-- `Matrix.blockDiag'` as an `AddMonoidHom`. -/
@[simps]
/-
**Matrix.blockDiag'AddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{o : Type u_4} →   (m' : o → Type u_7) →     (n' : o → Type u_8) →       (
α : Type u_12) →         [inst : AddZeroClass α] → Matrix ((i : o) × m' i) ((i :
 o) × n' i) α →+ (i : o) → Matrix (m' i) (n' i) α
参数：m' : o → Type u_7；n' : o → Type u_8；α : Type u_12；(i : o) × m' i；(i : o) × n'
 i；i : o；m' i；n' i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.blockDiag'` as an `AddMonoidHom`.
-/
def blockDiag'AddMonoidHom [AddZeroClass α] :
    Matrix (Σ i, m' i) (Σ i, n' i) α →+ ∀ i, Matrix (m' i) (n' i) α where
  toFun := blockDiag'
  map_zero' := blockDiag'_zero
  map_add' := blockDiag'_add

end

@[simp]
/-
**Matrix.blockDiag'_neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {o : Type u_4} {m' : o → Type u_7} {n' : o → Type u_8} {α : Type u_12} [
inst : AddGroup α]   (M : Matrix ((i : o) × m' i) ((i : o) × n' i) α), (-M).bloc
kDiag' = -M.blockDiag'
参数：M : Matrix ((i : o) × m' i) ((i : o) × n' i) α；-M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem blockDiag'_neg [AddGroup α] (M : Matrix (Σ i, m' i) (Σ i, n' i) α) :
    blockDiag' (-M) = -blockDiag' M :=
  map_neg (blockDiag'AddMonoidHom m' n' α) M

@[simp]
/-
**Matrix.blockDiag'_sub** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {o : Type u_4} {m' : o → Type u_7} {n' : o → Type u_8} {α : Type u_12} [
inst : AddGroup α]   (M N : Matrix ((i : o) × m' i) ((i : o) × n' i) α), (M - N)
.blockDiag' = M.blockDiag' - N.blockDiag'
参数：M N : Matrix ((i : o) × m' i) ((i : o) × n' i) α；M - N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem blockDiag'_sub [AddGroup α] (M N : Matrix (Σ i, m' i) (Σ i, n' i) α) :
    blockDiag' (M - N) = blockDiag' M - blockDiag' N :=
  map_sub (blockDiag'AddMonoidHom m' n' α) M N

@[simp]
/-
**Matrix.blockDiag'_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {o : Type u_4} {m' : o → Type u_7} {n' : o → Type u_8} {α : Type u_12} {
R : Type u_14} [inst : SMul R α] (x : R)   (M : Matrix ((i : o) × m' i) ((i : o)
 × n' i) α), (x • M).blockDiag' = x • M.blockDiag'
参数：x : R；M : Matrix ((i : o) × m' i) ((i : o) × n' i) α；x • M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem blockDiag'_smul {R : Type*} [SMul R α] (x : R)
    (M : Matrix (Σ i, m' i) (Σ i, n' i) α) : blockDiag' (x • M) = x • blockDiag' M :=
  rfl

end BlockDiag'

section

variable [CommRing R]

/-
**Matrix.toBlock_mul_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：toBlock_mul_eq_mul {m n k : Type*} [Fintype n] (p : m -> Prop) (q : k -> P
rop) (A : Matrix m n R) (B : Matrix n k R) : (A * B).toBlock p q = A.toBlock p ⊤
 * B.toBlock ⊤ q
参数：p : m -> Prop；q : k -> Prop；A : Matrix m n R；B : Matrix n k R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_subtype`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoi
d M] {p : ι → Prop} {F : Fintype (Subtype p)} (s : Finset ι),   (∀ (x : ι), x ∈ 
s ↔ p x)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem toBlock_mul_eq_mul {m n k : Type*} [Fintype n] (p : m → Prop) (q : k → Prop)
    (A : Matrix m n R) (B : Matrix n k R) :
    (A * B).toBlock p q = A.toBlock p ⊤ * B.toBlock ⊤ q := by
  ext i k
  simp only [toBlock_apply, mul_apply]
  rw [Finset.sum_subtype]
  simp [Pi.top_apply, Prop.top_eq_true]
/-
**Matrix.toBlock_mul_eq_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：toBlock_mul_eq_add {m n k : Type*} [Fintype n] (p : m -> Prop) (q : n -> P
rop) [DecidablePred q] (r : k -> Prop) (A : Matrix m n R) (B : Matrix n k R) : (
A * B).toBlock p r = A.toBlock p q * B.toBlock q r + (A.toBlock p fun i => ¬q i)
 * B.toBlock (fun i => ¬q i) r
参数：p : m -> Prop；q : n -> Prop；r : k -> Prop；A : Matrix m n R；B : Matrix n k R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.sum_subtype_add_sum_subtype`：∀ {M : Type u_4} {ι : Type u_7} [in
st : Fintype ι] [inst_1 : AddCommMonoid M] (p : ι → Prop) (f : ι → M)   [inst_2 
: DecidablePred p], ∑ i, …
-/
theorem toBlock_mul_eq_add {m n k : Type*} [Fintype n] (p : m → Prop) (q : n → Prop)
    [DecidablePred q] (r : k → Prop) (A : Matrix m n R) (B : Matrix n k R) : (A * B).toBlock p r =
    A.toBlock p q * B.toBlock q r + (A.toBlock p fun i => ¬q i) * B.toBlock (fun i => ¬q i) r := by
  ext i k
  simp only [toBlock_apply, mul_apply]
  exact (Fintype.sum_subtype_add_sum_subtype q fun x => A (↑i) x * B x ↑k).symm

end

end Matrix

section Maps

variable {R α β ι : Type*}

/-
**Matrix.map_toSquareBlock** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Matrix.map_toSquareBlock (f : α -> β) {M : Matrix m m α} {ι} {b : m -> ι} 
{i : ι} : (M.map f).toSquareBlock b i = (M.toSquareBlock b i).map f
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.submatrix_map`：submatrix_map (f : α -> β) (e₁ : l -> m) (e₂ : o -
> n) (A : Matrix m n α) : (A.map f).submatrix e₁ e₂ = (A.submatrix e₁ e₂).map f
-/
lemma Matrix.map_toSquareBlock
    (f : α → β) {M : Matrix m m α} {ι} {b : m → ι} {i : ι} :
    (M.map f).toSquareBlock b i = (M.toSquareBlock b i).map f :=
  submatrix_map _ _ _ _
/-
**Matrix.comp_toSquareBlock** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Matrix.comp_toSquareBlock {b : m -> α} (M : Matrix m m (Matrix n n R)) (a 
: α) : letI equiv
参数：M : Matrix m m (Matrix n n R)；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Matrix.comp_toSquareBlock {b : m → α}
    (M : Matrix m m (Matrix n n R)) (a : α) :
    letI equiv := Equiv.prodSubtypeFstEquivSubtypeProd.symm
    (M.comp m m n n R).toSquareBlock (fun i ↦ b i.1) a =
      ((M.toSquareBlock b a).comp _ _ n n R).reindex equiv equiv :=
  rfl

variable [Zero R] [DecidableEq m]

set_option backward.isDefEq.respectTransparency false in
/-
**Matrix.comp_diagonal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Matrix.comp_diagonal (d) : comp m m n n R (diagonal d) = (blockDiagonal d)
.reindex (.prodComm ..) (.prodComm ..)
参数：d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.comp_apply`：∀ (I : Type u_1) (J : Type u_2) (K : Type u_3) (L : T
ype u_4) (R : Type u_5) (m : Matrix I J (Matrix K L R))   (ik : I × K) (jl : J ×
 L), (M…
· 使用定理 `Matrix.ite_apply`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} (P : Prop
) [inst : Decidable P] (A B : Matrix m n α) (i : m) (j : n),   (if P then A else
 B) i …
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Matrix.comp_diagonal (d) :
    comp m m n n R (diagonal d) =
      (blockDiagonal d).reindex (.prodComm ..) (.prodComm ..) := by
  ext
  simp [diagonal, blockDiagonal, Matrix.ite_apply]

end Maps

