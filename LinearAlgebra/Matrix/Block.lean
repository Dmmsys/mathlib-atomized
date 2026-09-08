/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen, Wen Yang
-/
module

public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.FinCases

/-!
# Block matrices and their determinant

This file defines a predicate `Matrix.BlockTriangular` saying a matrix
is block triangular, and proves the value of the determinant for various
matrices built out of blocks.

## Main definitions

* `Matrix.BlockTriangular` expresses that an `o` by `o` matrix is block triangular,
  if the rows and columns are ordered according to some order `b : o → α`

## Main results

* `Matrix.det_of_blockTriangular`: the determinant of a block triangular matrix
  is equal to the product of the determinants of all the blocks
* `Matrix.det_of_isUpperTriangular` and `Matrix.det_of_isLowerTriangular`: the determinant of
  a triangular matrix is the product of the entries along the diagonal

## Tags

matrix, diagonal, det, block triangular

-/

@[expose] public section


open Finset Function OrderDual

open Matrix

universe v

variable {α β m n o : Type*} {m' n' : α → Type*}
variable {R : Type v} {A : Type*} {M N : Matrix m m R} {b : m → α}

namespace Matrix

section LT

variable [LT α]

section Zero

variable [Zero R]

/-- Let `b` map rows and columns of a square matrix `M` to blocks indexed by `α`s. Then
`BlockTriangular M n b` says the matrix is block triangular. -/
/-
**Matrix.BlockTriangular** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：BlockTriangular (M : Matrix m m R) (b : m -> α) : Prop
参数：M : Matrix m m R；b : m -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `b` map rows and columns of a square matrix `M` to blocks indexed by `α`s. T
hen
`BlockTriangular M n b` says the matrix is block triangular.
-/
def BlockTriangular (M : Matrix m m R) (b : m → α) : Prop :=
  ∀ ⦃i j⦄, b j < b i → M i j = 0

/-- `M` is upper triangular: entries below the diagonal vanish. -/
/-
**Matrix.IsUpperTriangular** 是 Mathlib 中的一个缩写定义，位于命名空间 `Matrix`。
形式化陈述：IsUpperTriangular [LT m] (M : Matrix m m R) : Prop
参数：M : Matrix m m R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M` is upper triangular: entries below the diagonal vanish.
-/
abbrev IsUpperTriangular [LT m] (M : Matrix m m R) : Prop :=
  M.BlockTriangular id

/-- `M` is lower triangular: entries above the diagonal vanish. -/
/-
**Matrix.IsLowerTriangular** 是 Mathlib 中的一个缩写定义，位于命名空间 `Matrix`。
形式化陈述：IsLowerTriangular [LT m] (M : Matrix m m R) : Prop
参数：M : Matrix m m R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M` is lower triangular: entries above the diagonal vanish.
-/
abbrev IsLowerTriangular [LT m] (M : Matrix m m R) : Prop :=
  M.BlockTriangular toDual

@[simp]
/-
**Matrix.BlockTriangular.submatrix** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.BlockTriang
ular`。
形式化陈述：∀ {α : Type u_1} {m : Type u_3} {n : Type u_4} {R : Type v} {M : Matrix m 
m R} {b : m → α} [inst : LT α]   [inst_1 : Zero R] {f : n → m}, M.BlockTriangula
r b → (M.submatrix f f).BlockTriangular (b ∘ f)
参数：M.submatrix f f；b ∘ f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem BlockTriangular.submatrix {f : n → m} (h : M.BlockTriangular b) :
    (M.submatrix f f).BlockTriangular (b ∘ f) := fun _ _ hij => h hij
/-
**Matrix.blockTriangular_reindex_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockTriangular_reindex_iff {b : n -> α} {e : m ≃ n} : (reindex e e M).Blo
ckTriangular b ↔ M.BlockTriangular (b ∘ e)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Matrix.submatrix_submatrix`：submatrix_submatrix {l₂ o₂ : Type*} (A : Mat
rix m n α) (r₁ : l -> m) (c₁ : o -> n) (r₂ : l₂ -> l) (c₂ : o₂ -> o) : (A.submat
rix r₁ c₁).subma…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.symm_comp_self`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e.symm ∘
 ⇑e = id
· 使用定理 `Matrix.submatrix_id_id`：submatrix_id_id (A : Matrix m n α) : A.submatrix
 id id = A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.BlockTriangular.submatrix`：∀ {α : Type u_1} {m : Type u_3} {n : T
ype u_4} {R : Type v} {M : Matrix m m R} {b : m → α} [inst : LT α]   [inst_1 : Z
ero R] {f : n → m}, M.…
· 使用定理 `Equiv.self_comp_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e ∘ ⇑e.s
ymm = id
-/
theorem blockTriangular_reindex_iff {b : n → α} {e : m ≃ n} :
    (reindex e e M).BlockTriangular b ↔ M.BlockTriangular (b ∘ e) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · convert! h.submatrix
    simp only [reindex_apply, submatrix_submatrix, submatrix_id_id, Equiv.symm_comp_self]
  · convert! h.submatrix
    simp only [comp_assoc b e e.symm, Equiv.self_comp_symm, comp_id]
/-
**Matrix.BlockTriangular.transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.BlockTriang
ular`。
形式化陈述：∀ {α : Type u_1} {m : Type u_3} {R : Type v} {M : Matrix m m R} {b : m → α
} [inst : LT α] [inst_1 : Zero R],   M.BlockTriangular b → M.transpose.BlockTria
ngular (⇑OrderDual.toDual ∘ b)
参数：⇑OrderDual.toDual ∘ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem BlockTriangular.transpose :
    M.BlockTriangular b → Mᵀ.BlockTriangular (toDual ∘ b) :=
  swap

@[simp]
/-
**Matrix.blockTriangular_transpose_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {α : Type u_1} {m : Type u_3} {R : Type v} {M : Matrix m m R} [inst : LT
 α] [inst_1 : Zero R] {b : m → αᵒᵈ},   M.transpose.BlockTriangular b ↔ M.BlockTr
iangular (⇑OrderDual.ofDual ∘ b)
参数：⇑OrderDual.ofDual ∘ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
protected theorem blockTriangular_transpose_iff {b : m → αᵒᵈ} :
    Mᵀ.BlockTriangular b ↔ M.BlockTriangular (ofDual ∘ b) :=
  forall_comm

@[simp]
/-
**Matrix.blockTriangular_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockTriangular_zero : BlockTriangular (0 : Matrix m m R) b
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem blockTriangular_zero : BlockTriangular (0 : Matrix m m R) b := fun _ _ _ => rfl
/-
**Matrix.decidableBlockTriangular** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：decidableBlockTriangular [DecidableEq R] [Fintype m] [DecidableLT α] : Dec
idable (M.BlockTriangular b)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableBlockTriangular [DecidableEq R] [Fintype m] [DecidableLT α] :
    Decidable (M.BlockTriangular b) :=
  decidable_of_iff (∀ ij : m × m, b ij.2 < b ij.1 → M ij.1 ij.2 = 0)
    ⟨fun h i j hij => h (i, j) hij, fun h _ hij => h hij⟩

end Zero

/-
**Matrix.BlockTriangular.neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.BlockTriangular`。
形式化陈述：∀ {α : Type u_1} {m : Type u_3} {R : Type v} {b : m → α} [inst : LT α] [in
st_1 : NegZeroClass R] {M : Matrix m m R},   M.BlockTriangular b → (-M).BlockTri
angular b
参数：-M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.neg_apply`：neg_apply [Neg α] (A : Matrix m n α) (i : m) (j : n) :
 (-A) i j = -(A i j)
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
protected theorem BlockTriangular.neg [NegZeroClass R] {M : Matrix m m R}
    (hM : BlockTriangular M b) : BlockTriangular (-M) b :=
  fun _ _ h => by rw [neg_apply, hM h, neg_zero]
/-
**Matrix.BlockTriangular.add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.BlockTriangular`。
形式化陈述：∀ {α : Type u_1} {m : Type u_3} {R : Type v} {M N : Matrix m m R} {b : m →
 α} [inst : LT α] [inst_1 : AddZeroClass R],   M.BlockTriangular b → N.BlockTria
ngular b → (M + N).BlockTriangular b
参数：M + N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem BlockTriangular.add [AddZeroClass R] (hM : BlockTriangular M b) (hN : BlockTriangular N b) :
    BlockTriangular (M + N) b := fun i j h => by simp_rw [Matrix.add_apply, hM h, hN h, zero_add]
/-
**Matrix.BlockTriangular.sub** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.BlockTriangular`。
形式化陈述：∀ {α : Type u_1} {m : Type u_3} {R : Type v} {M N : Matrix m m R} {b : m →
 α} [inst : LT α]   [inst_1 : SubNegZeroMonoid R], M.BlockTriangular b → N.Block
Triangular b → (M - N).BlockTriangular b
参数：M - N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem BlockTriangular.sub [SubNegZeroMonoid R]
    (hM : BlockTriangular M b) (hN : BlockTriangular N b) :
    BlockTriangular (M - N) b := fun i j h => by simp_rw [Matrix.sub_apply, hM h, hN h, sub_zero]
/-
**Matrix.BlockTriangular.add_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.BlockTr
iangular`。
形式化陈述：∀ {α : Type u_1} {m : Type u_3} {R : Type v} {M N : Matrix m m R} {b : m →
 α} [inst : LT α] [inst_1 : AddGroup R],   M.BlockTriangular b → ((M + N).BlockT
riangular b ↔ N.BlockTriangular b)
参数：(M + N).BlockTriangular b ↔ N.BlockTriangular b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_add_cancel_left`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), -a 
+ (a + b) = b
· 使用定理 `Matrix.BlockTriangular.add`：∀ {α : Type u_1} {m : Type u_3} {R : Type v}
 {M N : Matrix m m R} {b : m → α} [inst : LT α] [inst_1 : AddZeroClass R],   M.B
lockTriangular b…
· 使用定理 `Matrix.BlockTriangular.neg`：∀ {α : Type u_1} {m : Type u_3} {R : Type v}
 {b : m → α} [inst : LT α] [inst_1 : NegZeroClass R] {M : Matrix m m R},   M.Blo
ckTriangular b →…
-/
lemma BlockTriangular.add_iff_right [AddGroup R] (hM : BlockTriangular M b) :
    BlockTriangular (M + N) b ↔ BlockTriangular N b := ⟨(by simpa using hM.neg.add ·), hM.add⟩
/-
**Matrix.BlockTriangular.add_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.BlockTri
angular`。
形式化陈述：∀ {α : Type u_1} {m : Type u_3} {R : Type v} {M N : Matrix m m R} {b : m →
 α} [inst : LT α] [inst_1 : AddGroup R],   N.BlockTriangular b → ((M + N).BlockT
riangular b ↔ M.BlockTriangular b)
参数：(M + N).BlockTriangular b ↔ M.BlockTriangular b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `Matrix.BlockTriangular.sub`：∀ {α : Type u_1} {m : Type u_3} {R : Type v}
 {M N : Matrix m m R} {b : m → α} [inst : LT α]   [inst_1 : SubNegZeroMonoid R],
 M.BlockTriangul…
· 使用定理 `Matrix.BlockTriangular.add`：∀ {α : Type u_1} {m : Type u_3} {R : Type v}
 {M N : Matrix m m R} {b : m → α} [inst : LT α] [inst_1 : AddZeroClass R],   M.B
lockTriangular b…
-/
lemma BlockTriangular.add_iff_left [AddGroup R] (hN : BlockTriangular N b) :
    BlockTriangular (M + N) b ↔ BlockTriangular M b := ⟨(by simpa using ·.sub hN), (·.add hN)⟩
/-
**Matrix.BlockTriangular.sub_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.BlockTr
iangular`。
形式化陈述：∀ {α : Type u_1} {m : Type u_3} {R : Type v} {M N : Matrix m m R} {b : m →
 α} [inst : LT α] [inst_1 : AddGroup R],   M.BlockTriangular b → ((M - N).BlockT
riangular b ↔ N.BlockTriangular b)
参数：(M - N).BlockTriangular b ↔ N.BlockTriangular b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Matrix.BlockTriangular.add`：∀ {α : Type u_1} {m : Type u_3} {R : Type v}
 {M N : Matrix m m R} {b : m → α} [inst : LT α] [inst_1 : AddZeroClass R],   M.B
lockTriangular b…
· 使用定理 `Matrix.BlockTriangular.neg`：∀ {α : Type u_1} {m : Type u_3} {R : Type v}
 {b : m → α} [inst : LT α] [inst_1 : NegZeroClass R] {M : Matrix m m R},   M.Blo
ckTriangular b →…
· 使用定理 `Matrix.BlockTriangular.sub`：∀ {α : Type u_1} {m : Type u_3} {R : Type v}
 {M N : Matrix m m R} {b : m → α} [inst : LT α]   [inst_1 : SubNegZeroMonoid R],
 M.BlockTriangul…
-/
lemma BlockTriangular.sub_iff_right [AddGroup R] (hM : BlockTriangular M b) :
    BlockTriangular (M - N) b ↔ BlockTriangular N b := ⟨(by simpa using ·.neg.add hM), hM.sub⟩
/-
**Matrix.BlockTriangular.sub_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.BlockTri
angular`。
形式化陈述：∀ {α : Type u_1} {m : Type u_3} {R : Type v} {M N : Matrix m m R} {b : m →
 α} [inst : LT α] [inst_1 : AddGroup R],   N.BlockTriangular b → ((M - N).BlockT
riangular b ↔ M.BlockTriangular b)
参数：(M - N).BlockTriangular b ↔ M.BlockTriangular b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Matrix.BlockTriangular.add`：∀ {α : Type u_1} {m : Type u_3} {R : Type v}
 {M N : Matrix m m R} {b : m → α} [inst : LT α] [inst_1 : AddZeroClass R],   M.B
lockTriangular b…
· 使用定理 `Matrix.BlockTriangular.sub`：∀ {α : Type u_1} {m : Type u_3} {R : Type v}
 {M N : Matrix m m R} {b : m → α} [inst : LT α]   [inst_1 : SubNegZeroMonoid R],
 M.BlockTriangul…
-/
lemma BlockTriangular.sub_iff_left [AddGroup R] (hN : BlockTriangular N b) :
    BlockTriangular (M - N) b ↔ BlockTriangular M b := ⟨(by simpa using ·.add hN), (·.sub hN)⟩
/-
**Matrix.BlockTriangular.map** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.BlockTriangular`。
形式化陈述：∀ {α : Type u_1} {m : Type u_3} {R : Type v} {M : Matrix m m R} {b : m → α
} [inst : LT α] {S : Type u_9} {F : Type u_10}   [inst_1 : FunLike F R S] [inst_
2 : Zero R] [inst_3 : Zero S] [ZeroHomClass F R S] (f : F),   M.BlockTriangular 
b → (M.map ⇑f).BlockTriangular b
参数：f : F；M.map ⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma BlockTriangular.map {S F} [FunLike F R S] [Zero R] [Zero S] [ZeroHomClass F R S] (f : F)
    (h : BlockTriangular M b) : BlockTriangular (M.map f) b :=
  fun i j lt ↦ by simp [h lt]
/-
**Matrix.BlockTriangular.comp** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.BlockTriangular`
。
形式化陈述：∀ {α : Type u_1} {m : Type u_3} {n : Type u_4} {R : Type v} {b : m → α} [i
nst : LT α] [inst_1 : Zero R]   {M : Matrix m m (Matrix n n R)}, M.BlockTriangul
ar b → ((Matrix.comp m m n n R) M).BlockTriangular fun i => b i.1
参数：Matrix n n R；(Matrix.comp m m n n R) M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.comp_apply`：∀ (I : Type u_1) (J : Type u_2) (K : Type u_3) (L : T
ype u_4) (R : Type u_5) (m : Matrix I J (Matrix K L R))   (ik : I × K) (jl : J ×
 L), (M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma BlockTriangular.comp [Zero R] {M : Matrix m m (Matrix n n R)} (h : BlockTriangular M b) :
    BlockTriangular (M.comp m m n n R) fun i ↦ b i.1 :=
  fun i j lt ↦ by simp [h lt]

end LT

section Preorder

variable [Preorder α]

section Zero

variable [Zero R]

/-
**Matrix.blockTriangular_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockTriangular_diagonal [DecidableEq m] (d : m -> R) : BlockTriangular (d
iagonal d) b
参数：d : m -> R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.diagonal_apply_ne'`：diagonal_apply_ne' [Zero α] (d : n -> α) {i j
 : n} (h : j != i) : (diagonal d) i j = 0
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem blockTriangular_diagonal [DecidableEq m] (d : m → R) : BlockTriangular (diagonal d) b :=
  fun _ _ h => diagonal_apply_ne' d fun h' => ne_of_lt h (congr_arg _ h')
/-
**Matrix.blockTriangular_blockDiagonal'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockTriangular_blockDiagonal' [DecidableEq α] (d : forall i : α, Matrix (
m' i) (m' i) R) : BlockTriangular (blockDiagonal' d) Sigma.fst
参数：d : forall i : α, Matrix (m' i) (m' i) R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.blockDiagonal'_apply_ne`：∀ {o : Type u_4} {m' : o → Type u_7} {n'
 : o → Type u_8} {α : Type u_12} [inst : DecidableEq o] [inst_1 : Zero α]   (M :
 (i : o) → Matrix (m…
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem blockTriangular_blockDiagonal' [DecidableEq α] (d : ∀ i : α, Matrix (m' i) (m' i) R) :
    BlockTriangular (blockDiagonal' d) Sigma.fst := by
  rintro ⟨i, i'⟩ ⟨j, j'⟩ h
  apply blockDiagonal'_apply_ne d i' j' fun h' => ne_of_lt h h'.symm
/-
**Matrix.blockTriangular_blockDiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockTriangular_blockDiagonal [DecidableEq α] (d : α -> Matrix m m R) : Bl
ockTriangular (blockDiagonal d) Prod.snd
参数：d : α -> Matrix m m R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.blockDiagonal'_eq_blockDiagonal`：∀ {m : Type u_2} {n : Type u_3} 
{o : Type u_4} {α : Type u_12} [inst : DecidableEq o] [inst_1 : Zero α]   (M : o
 → Matrix m n α) {k k' : o} …
· 使用定理 `Matrix.blockTriangular_blockDiagonal'`：blockTriangular_blockDiagonal' [D
ecidableEq α] (d : forall i : α, Matrix (m' i) (m' i) R) : BlockTriangular (bloc
kDiagonal' d) Sigma.fst
-/
theorem blockTriangular_blockDiagonal [DecidableEq α] (d : α → Matrix m m R) :
    BlockTriangular (blockDiagonal d) Prod.snd := by
  rintro ⟨i, i'⟩ ⟨j, j'⟩ h
  rw [blockDiagonal'_eq_blockDiagonal, blockTriangular_blockDiagonal']
  exact h

variable [DecidableEq m]
/-
**Matrix.blockTriangular_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockTriangular_one [One R] : BlockTriangular (1 : Matrix m m R) b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.blockTriangular_diagonal`：blockTriangular_diagonal [DecidableEq m
] (d : m -> R) : BlockTriangular (diagonal d) b
-/
theorem blockTriangular_one [One R] : BlockTriangular (1 : Matrix m m R) b :=
  blockTriangular_diagonal _
/-
**Matrix.blockTriangular_single** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockTriangular_single {i j : m} (hij : b i <= b j) (c : R) : BlockTriangu
lar (single i j c) b
参数：hij : b i <= b j；c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.single_apply_of_ne`：single_apply_of_ne (h : ¬(i = i' ∧ j = j')) :
 single i j c i' j' = 0
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
-/
theorem blockTriangular_single {i j : m} (hij : b i ≤ b j) (c : R) :
    BlockTriangular (single i j c) b := by
  intro r s hrs
  apply single_apply_of_ne
  rintro ⟨rfl, rfl⟩
  exact (hij.trans_lt hrs).false
/-
**Matrix.blockTriangular_single'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockTriangular_single' {i j : m} (hij : b j <= b i) (c : R) : BlockTriang
ular (single i j c) (toDual ∘ b)
参数：hij : b j <= b i；c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.blockTriangular_single`：blockTriangular_single {i j : m} (hij : b
 i <= b j) (c : R) : BlockTriangular (single i j c) b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `OrderDual.toDual_le_toDual`：toDual_le_toDual [LE α] {a b : α} : toDual a
 <= toDual b ↔ b <= a
-/
theorem blockTriangular_single' {i j : m} (hij : b j ≤ b i) (c : R) :
    BlockTriangular (single i j c) (toDual ∘ b) :=
  blockTriangular_single (by exact toDual_le_toDual.mpr hij) _

end Zero

variable [CommRing R] [DecidableEq m]

/-
**Matrix.blockTriangular_transvection** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockTriangular_transvection {i j : m} (hij : b i <= b j) (c : R) : BlockT
riangular (transvection i j c) b
参数：hij : b i <= b j；c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.BlockTriangular.add`：∀ {α : Type u_1} {m : Type u_3} {R : Type v}
 {M N : Matrix m m R} {b : m → α} [inst : LT α] [inst_1 : AddZeroClass R],   M.B
lockTriangular b…
· 使用定理 `Matrix.blockTriangular_one`：blockTriangular_one [One R] : BlockTriangula
r (1 : Matrix m m R) b
· 使用定理 `Matrix.blockTriangular_single`：blockTriangular_single {i j : m} (hij : b
 i <= b j) (c : R) : BlockTriangular (single i j c) b
-/
theorem blockTriangular_transvection {i j : m} (hij : b i ≤ b j) (c : R) :
    BlockTriangular (transvection i j c) b :=
  blockTriangular_one.add (blockTriangular_single hij c)
/-
**Matrix.blockTriangular_transvection'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockTriangular_transvection' {i j : m} (hij : b j <= b i) (c : R) : Block
Triangular (transvection i j c) (OrderDual.toDual ∘ b)
参数：hij : b j <= b i；c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.BlockTriangular.add`：∀ {α : Type u_1} {m : Type u_3} {R : Type v}
 {M N : Matrix m m R} {b : m → α} [inst : LT α] [inst_1 : AddZeroClass R],   M.B
lockTriangular b…
· 使用定理 `Matrix.blockTriangular_one`：blockTriangular_one [One R] : BlockTriangula
r (1 : Matrix m m R) b
· 使用定理 `Matrix.blockTriangular_single'`：blockTriangular_single' {i j : m} (hij :
 b j <= b i) (c : R) : BlockTriangular (single i j c) (toDual ∘ b)
-/
theorem blockTriangular_transvection' {i j : m} (hij : b j ≤ b i) (c : R) :
    BlockTriangular (transvection i j c) (OrderDual.toDual ∘ b) :=
  blockTriangular_one.add (blockTriangular_single' hij c)

end Preorder

section LinearOrder

variable [LinearOrder α]

/-
**Matrix.BlockTriangular.mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.BlockTriangular`。
形式化陈述：∀ {α : Type u_1} {m : Type u_3} {R : Type v} {b : m → α} [inst : LinearOrd
er α] [inst_1 : Fintype m]   [inst_2 : NonUnitalNonAssocSemiring R] {M N : Matri
x m m R},   M.BlockTriangular b → N.BlockTriangular b → (M * N).BlockTriangular 
b
参数：M * N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem BlockTriangular.mul [Fintype m] [NonUnitalNonAssocSemiring R]
    {M N : Matrix m m R} (hM : BlockTriangular M b)
    (hN : BlockTriangular N b) : BlockTriangular (M * N) b := by
  intro i j hij
  apply Finset.sum_eq_zero
  intro k _
  by_cases! hki : b k < b i
  · simp_rw [hM hki, zero_mul]
  · simp_rw [hN (lt_of_lt_of_le hij hki), mul_zero]

variable (R b) in
/-- `BlockTriangular` matrices form a subsemiring. -/
@[simps]
/-
**Matrix.blockTriangularSubsemiring** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：blockTriangularSubsemiring [DecidableEq m] [Fintype m] [Semiring R] : Subs
emiring (Matrix m m R) where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`BlockTriangular` matrices form a subsemiring.
-/
def blockTriangularSubsemiring [DecidableEq m] [Fintype m] [Semiring R] :
    Subsemiring (Matrix m m R) where
  carrier := {M | BlockTriangular M b}
  zero_mem' := blockTriangular_zero
  one_mem' := blockTriangular_one
  mul_mem' := .mul
  add_mem' := .add

@[simp]
/-
**Matrix.mem_blockTriangularSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mem_blockTriangularSubsemiring [DecidableEq m] [Fintype m] [Semiring R] {M
 : Matrix m m R} : M in blockTriangularSubsemiring R b ↔ BlockTriangular M b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_blockTriangularSubsemiring [DecidableEq m] [Fintype m] [Semiring R]
    {M : Matrix m m R} :
    M ∈ blockTriangularSubsemiring R b ↔ BlockTriangular M b :=
  Iff.rfl
/-
**Matrix.BlockTriangular.pow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.BlockTriangular`。
形式化陈述：∀ {α : Type u_1} {m : Type u_3} {R : Type v} {M : Matrix m m R} {b : m → α
} [inst : LinearOrder α]   [inst_1 : DecidableEq m] [inst_2 : Fintype m] [inst_3
 : Semiring R],   M.BlockTriangular b → ∀ (n : ℕ), (M ^ n).BlockTriangular b
参数：n : ℕ；M ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : Monoid M] [inst_1 : Set
Like A M] [SubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), x ^ n ∈ …
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R
-/
theorem BlockTriangular.pow [DecidableEq m] [Fintype m] [Semiring R] (hM : BlockTriangular M b)
    (n : ℕ) : BlockTriangular (M ^ n) b :=
  pow_mem (S := blockTriangularSubsemiring R b) hM n
/-
**Matrix.blockTriangular_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：blockTriangular_algebraMap [CommSemiring R] [Semiring A] [Algebra R A] [De
cidableEq m] [Fintype m] (r : R) : (algebraMap R (Matrix m m A) r).BlockTriangul
ar b
参数：r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.blockTriangular_diagonal`：blockTriangular_diagonal [DecidableEq m
] (d : m -> R) : BlockTriangular (diagonal d) b
-/
theorem blockTriangular_algebraMap [CommSemiring R] [Semiring A] [Algebra R A]
    [DecidableEq m] [Fintype m] (r : R) : (algebraMap R (Matrix m m A) r).BlockTriangular b :=
  blockTriangular_diagonal _

variable (R A b) in
/-- `BlockTriangular` matrices form a subalgebra. -/
/-
**Matrix.blockTriangularSubalgebra** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：blockTriangularSubalgebra [CommSemiring R] [Semiring A] [Algebra R A] [Dec
idableEq m] [Fintype m] : Subalgebra R (Matrix m m A) where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.blockTriangular_algebraMap`：blockTriangular_algebraMap [CommSemir
ing R] [Semiring A] [Algebra R A] [DecidableEq m] [Fintype m] (r : R) : (algebra
Map R (Matrix m m A) r)…

--- 原说明 ---
`BlockTriangular` matrices form a subalgebra.
-/
def blockTriangularSubalgebra [CommSemiring R] [Semiring A] [Algebra R A]
    [DecidableEq m] [Fintype m] : Subalgebra R (Matrix m m A) where
  __ := blockTriangularSubsemiring A b
  algebraMap_mem' r := blockTriangular_algebraMap r

@[simp]
/-
**Matrix.mem_blockTriangularSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mem_blockTriangularSubalgebra [CommSemiring R] [Semiring A] [Algebra R A] 
[DecidableEq m] [Fintype m] {M : Matrix m m A} : M in blockTriangularSubalgebra 
R A b ↔ BlockTriangular M b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_blockTriangularSubalgebra [CommSemiring R] [Semiring A] [Algebra R A]
    [DecidableEq m] [Fintype m] {M : Matrix m m A} :
    M ∈ blockTriangularSubalgebra R A b ↔ BlockTriangular M b :=
  Iff.rfl

end LinearOrder

/-
**Matrix.upper_two_blockTriangular** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：upper_two_blockTriangular [Zero R] [Preorder α] (A : Matrix m m R) (B : Ma
trix m n R) (D : Matrix n n R) {a b : α} (hab : a < b) : BlockTriangular (fromBl
ocks A B 0 D) (Sum.elim (fun _ => a) fun _ => b)
参数：A : Matrix m m R；B : Matrix m n R；D : Matrix n n R；hab : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem upper_two_blockTriangular [Zero R] [Preorder α] (A : Matrix m m R) (B : Matrix m n R)
    (D : Matrix n n R) {a b : α} (hab : a < b) :
    BlockTriangular (fromBlocks A B 0 D) (Sum.elim (fun _ => a) fun _ => b) := by
  rintro (c | c) (d | d) hcd <;> first | simp [hab.not_gt] at hcd ⊢

/-! ### Determinant -/


variable [CommRing R] [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]

/-
**Matrix.equiv_block_det** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：equiv_block_det (M : Matrix m m R) {p q : m -> Prop} [DecidablePred p] [De
cidablePred q] (e : forall x, q x ↔ p x) : (toSquareBlockProp M p).det = (toSqua
reBlockProp M q).det
参数：M : Matrix m m R；e : forall x, q x ↔ p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_reindex_self`：det_reindex_self (e : m ≃ n) (A : Matrix m m R)
 : det (reindex e e A) = det A
-/
theorem equiv_block_det (M : Matrix m m R) {p q : m → Prop} [DecidablePred p] [DecidablePred q]
    (e : ∀ x, q x ↔ p x) : (toSquareBlockProp M p).det = (toSquareBlockProp M q).det := by
  convert!
    Matrix.det_reindex_self (Equiv.subtypeEquivRight e)
      (toSquareBlockProp M q)
        -- Removed `@[simp]` attribute,
        -- as the LHS simplifies already to `M.toSquareBlock id i ⟨i, ⋯⟩ ⟨i, ⋯⟩`


-- Removed `@[simp]` attribute,
-- as the LHS simplifies already to `M.toSquareBlock id i ⟨i, ⋯⟩ ⟨i, ⋯⟩`
/-
**Matrix.det_toSquareBlock_id** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_toSquareBlock_id (M : Matrix m m R) (i : m) : (M.toSquareBlock id i).d
et = M i i
参数：M : Matrix m m R；i : m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Matrix.det_unique`：det_unique {n : Type*} [Unique n] [DecidableEq n] [Fi
ntype n] (A : Matrix n n R) : det A = A default default
-/
theorem det_toSquareBlock_id (M : Matrix m m R) (i : m) : (M.toSquareBlock id i).det = M i i :=
  letI : Unique { a // id a = i } := ⟨⟨⟨i, rfl⟩⟩, fun j => Subtype.ext j.property⟩
  (det_unique _).trans rfl
/-
**Matrix.det_toBlock** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_toBlock (M : Matrix m m R) (p : m -> Prop) [DecidablePred p] : M.det =
 (fromBlocks (toBlock M p p) (toBlock M p fun j => ¬p j) (toBlock M (fun j => ¬p
 j) p) <| toBlock M (fun j => ¬p j) fun j => ¬p j).det
参数：M : Matrix m m R；p : m -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_reindex_self`：det_reindex_self (e : m ≃ n) (A : Matrix m m R)
 : det (reindex e e A) = det A
· 使用定理 `Matrix.det_apply'`：det_apply' (M : Matrix n n R) : M.det = ∑ σ : Perm n,
 ε σ * ∏ i, M (σ i) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem det_toBlock (M : Matrix m m R) (p : m → Prop) [DecidablePred p] :
    M.det =
      (fromBlocks (toBlock M p p) (toBlock M p fun j => ¬p j) (toBlock M (fun j => ¬p j) p) <|
          toBlock M (fun j => ¬p j) fun j => ¬p j).det := by
  rw [← Matrix.det_reindex_self (Equiv.sumCompl p).symm M]
  rw [det_apply', det_apply']
  congr; ext σ; congr; ext x
  generalize hy : σ x = y
  cases x <;> cases y <;>
    simp only [Matrix.reindex_apply, toBlock_apply, Equiv.symm_symm, Equiv.sumCompl_apply_inr,
      Equiv.sumCompl_apply_inl, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.submatrix_apply]
/-
**Matrix.twoBlockTriangular_det** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：twoBlockTriangular_det (M : Matrix m m R) (p : m -> Prop) [DecidablePred p
] (h : forall i, ¬p i -> forall j, p j -> M i j = 0) : M.det = (toSquareBlockPro
p M p).det * (toSquareBlockProp M fun i => ¬p i).det
参数：M : Matrix m m R；p : m -> Prop；h : forall i, ¬p i -> forall j, p j -> M i j =
 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_toBlock`：det_toBlock (M : Matrix m m R) (p : m -> Prop) [Deci
dablePred p] : M.det = (fromBlocks (toBlock M p p) (toBlock M p fun j => ¬p j) (
toBlock …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Matrix.det_fromBlocks_zero₂₁`：det_fromBlocks_zero₂₁ (A : Matrix m m R) (
B : Matrix m n R) (D : Matrix n n R) : (Matrix.fromBlocks A B 0 D).det = A.det *
 D.det
-/
theorem twoBlockTriangular_det (M : Matrix m m R) (p : m → Prop) [DecidablePred p]
    (h : ∀ i, ¬p i → ∀ j, p j → M i j = 0) :
    M.det = (toSquareBlockProp M p).det * (toSquareBlockProp M fun i => ¬p i).det := by
  rw [det_toBlock M p]
  convert!
    det_fromBlocks_zero₂₁ (toBlock M p p) (toBlock M p fun j => ¬p j)
      (toBlock M (fun j => ¬p j) fun j => ¬p j)
  ext i j
  exact h (↑i) i.2 (↑j) j.2
/-
**Matrix.twoBlockTriangular_det'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：twoBlockTriangular_det' (M : Matrix m m R) (p : m -> Prop) [DecidablePred 
p] (h : forall i, p i -> forall j, ¬p j -> M i j = 0) : M.det = (toSquareBlockPr
op M p).det * (toSquareBlockProp M fun i => ¬p i).det
参数：M : Matrix m m R；p : m -> Prop；h : forall i, p i -> forall j, ¬p j -> M i j =
 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.twoBlockTriangular_det`：twoBlockTriangular_det (M : Matrix m m R)
 (p : m -> Prop) [DecidablePred p] (h : forall i, ¬p i -> forall j, p j -> M i j
 = 0) : M.det = (to…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Matrix.equiv_block_det`：equiv_block_det (M : Matrix m m R) {p q : m -> P
rop} [DecidablePred p] [DecidablePred q] (e : forall x, q x ↔ p x) : (toSquareBl
ockProp M p)…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
-/
theorem twoBlockTriangular_det' (M : Matrix m m R) (p : m → Prop) [DecidablePred p]
    (h : ∀ i, p i → ∀ j, ¬p j → M i j = 0) :
    M.det = (toSquareBlockProp M p).det * (toSquareBlockProp M fun i => ¬p i).det := by
  rw [M.twoBlockTriangular_det fun i => ¬p i, mul_comm]
  · congr 1
    exact equiv_block_det _ fun _ => not_not.symm
  · simpa only [Classical.not_not] using h
/-
**Matrix.BlockTriangular.det** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.BlockTriangular`。
形式化陈述：∀ {α : Type u_1} {m : Type u_3} {R : Type v} {M : Matrix m m R} {b : m → α
} [inst : CommRing R] [inst_1 : DecidableEq m]   [inst_2 : Fintype m] [inst_3 : 
DecidableEq α] [inst_4 : LinearOrder α],   M.BlockTriangular b → M.det = ∏ a ∈ F
inset.image b Finset.univ, (M.toSquareBlock b a).det
参数：M.toSquareBlock b a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eraseInduction`：eraseInduction [DecidableEq α] {p : Finset α -> P
rop} (H : (S : Finset α) -> (forall s in S, p (S.erase s)) -> p S) (S : Finset α
) : p S
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.coe_det_isEmpty`：coe_det_isEmpty [IsEmpty n] : (det : Matrix n n 
R -> R) = Function.const _ 1
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsEmptySubtype`：∀ {α : Sort u} [IsEmpty α] (p : α → Prop), IsEmpty (
Subtype p)
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Finset.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} [inst : Decidable
Eq β] {s : Finset α},   s.Nonempty → ∀ (f : α → β), (Finset.image f s).Nonempty
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `Matrix.twoBlockTriangular_det'`：twoBlockTriangular_det' (M : Matrix m m 
R) (p : m -> Prop) [DecidablePred p] (h : forall i, p i -> forall j, ¬p j -> M i
 j = 0) : M.det = (t…
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Finset.le_max'`：le_max' (x) (H2 : x in s) : x <= s.max' ⟨x, H2⟩
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Finset.max'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.max' H ∈ s
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Matrix.BlockTriangular.submatrix`：∀ {α : Type u_1} {m : Type u_3} {n : T
ype u_4} {R : Type v} {M : Matrix m m R} {b : m → α} [inst : LT α]   [inst_1 : Z
ero R] {f : n → m}, M.…
· 使用定理 `image_subtype_ne_univ_eq_image_erase`：image_subtype_ne_univ_eq_image_era
se [Fintype α] [DecidableEq β] (k : β) (b : α -> β) : image (fun i : { a // b a 
!= k } => b ↑i) univ = (im…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用引理 `ne_of_eq_of_ne`：ne_of_eq_of_ne {α : Sort*} {a b c : α} (h₁ : a = b) (h₂ 
: b != c) : a != c
（共 35 条，此处仅展示前 30 条）
-/
protected theorem BlockTriangular.det [DecidableEq α] [LinearOrder α] (hM : BlockTriangular M b) :
    M.det = ∏ a ∈ univ.image b, (M.toSquareBlock b a).det := by
  suffices ∀ hs : Finset α, univ.image b = hs → M.det = ∏ a ∈ hs, (M.toSquareBlock b a).det by
    exact this _ rfl
  intro s hs
  induction s using Finset.eraseInduction generalizing m with | H s ih =>
  subst hs
  cases isEmpty_or_nonempty m
  · simp
  let k := (univ.image b).max' (univ_nonempty.image _)
  rw [twoBlockTriangular_det' M fun i => b i = k]
  · have : univ.image b = insert k ((univ.image b).erase k) := by
      rw [insert_erase]
      apply max'_mem
    rw [this, prod_insert (notMem_erase _ _)]
    refine congr_arg _ ?_
    let b' := fun i : { a // b a ≠ k } => b ↑i
    have h' : BlockTriangular (M.toSquareBlockProp fun i => b i ≠ k) b' := hM.submatrix
    have hb' : image b' univ = (image b univ).erase k := by
      convert! image_subtype_ne_univ_eq_image_erase k b
    rw [ih _ (max'_mem _ _) h' hb']
    refine Finset.prod_congr rfl fun l hl => ?_
    let he : { a // b' a = l } ≃ { a // b a = l } :=
      haveI hc : ∀ i, b i = l → b i ≠ k := fun i hi => ne_of_eq_of_ne hi (ne_of_mem_erase hl)
      Equiv.subtypeSubtypeEquivSubtype @hc
    rw [toSquareBlock_def, ← Matrix.det_reindex_self he.symm]
    rfl
  · intro i hi j hj
    apply hM
    rw [hi]
    apply lt_of_le_of_ne _ hj
    exact Finset.le_max' (univ.image b) _ (mem_image_of_mem _ (mem_univ _))
/-
**Matrix.BlockTriangular.det_fintype** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.BlockTria
ngular`。
形式化陈述：∀ {α : Type u_1} {m : Type u_3} {R : Type v} {M : Matrix m m R} {b : m → α
} [inst : CommRing R] [inst_1 : DecidableEq m]   [inst_2 : Fintype m] [inst_3 : 
DecidableEq α] [inst_4 : Fintype α] [inst_5 : LinearOrder α],   M.BlockTriangula
r b → M.det = ∏ k, (M.toSquareBlock b k).det
参数：M.toSquareBlock b k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.BlockTriangular.det`：∀ {α : Type u_1} {m : Type u_3} {R : Type v}
 {M : Matrix m m R} {b : m → α} [inst : CommRing R] [inst_1 : DecidableEq m]   [
inst_2 : Fintype…
· 使用定理 `Finset.prod_subset`：prod_subset (h : s₁ subseteq s₂) (hf : forall x in s
₂, x ∉ s₁ -> f x = 1) : ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Matrix.det_isEmpty`：det_isEmpty [IsEmpty n] {A : Matrix n n R} : det A =
 1
-/
theorem BlockTriangular.det_fintype [DecidableEq α] [Fintype α] [LinearOrder α]
    (h : BlockTriangular M b) : M.det = ∏ k : α, (M.toSquareBlock b k).det := by
  refine h.det.trans (prod_subset (subset_univ _) fun a _ ha => ?_)
  have : IsEmpty { i // b i = a } := ⟨fun i => ha <| mem_image.2 ⟨i, mem_univ _, i.2⟩⟩
  exact det_isEmpty
/-
**Matrix.det_of_isUpperTriangular** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_of_isUpperTriangular [LinearOrder m] (h : M.IsUpperTriangular) : M.det
 = ∏ i : m, M i i
参数：h : M.IsUpperTriangular。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.BlockTriangular.det`：∀ {α : Type u_1} {m : Type u_3} {R : Type v}
 {M : Matrix m m R} {b : m → α} [inst : CommRing R] [inst_1 : DecidableEq m]   [
inst_2 : Fintype…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.image_id`：image_id [DecidableEq α] : s.image id = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.det_toSquareBlock_id`：det_toSquareBlock_id (M : Matrix m m R) (i 
: m) : (M.toSquareBlock id i).det = M i i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem det_of_isUpperTriangular [LinearOrder m] (h : M.IsUpperTriangular) :
    M.det = ∏ i : m, M i i := by
  have : DecidableEq R := Classical.decEq _
  simp_rw [h.det, image_id, det_toSquareBlock_id]

@[deprecated (since := "2026-07-30")] alias det_of_upperTriangular := det_of_isUpperTriangular
/-
**Matrix.det_of_isLowerTriangular** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_of_isLowerTriangular [LinearOrder m] (M : Matrix m m R) (h : M.IsLower
Triangular) : M.det = ∏ i : m, M i i
参数：M : Matrix m m R；h : M.IsLowerTriangular。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `Matrix.det_of_isUpperTriangular`：det_of_isUpperTriangular [LinearOrder m
] (h : M.IsUpperTriangular) : M.det = ∏ i : m, M i i
· 使用定理 `Matrix.BlockTriangular.transpose`：∀ {α : Type u_1} {m : Type u_3} {R : T
ype v} {M : Matrix m m R} {b : m → α} [inst : LT α] [inst_1 : Zero R],   M.Block
Triangular b → M.trans…
-/
theorem det_of_isLowerTriangular [LinearOrder m] (M : Matrix m m R) (h : M.IsLowerTriangular) :
    M.det = ∏ i : m, M i i := by
  rw [← det_transpose]
  exact det_of_isUpperTriangular h.transpose

@[deprecated (since := "2026-07-30")] alias det_of_lowerTriangular := det_of_isLowerTriangular

open Polynomial
/-
**Matrix.matrixOfPolynomials_blockTriangular** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：matrixOfPolynomials_blockTriangular {R} [Semiring R] {n : Nat} (p : Fin n 
-> R[X]) (h_deg : forall i, (p i).natDegree <= i) : Matrix.BlockTriangular (Matr
ix.of (fun (i j : Fin n) => (p j).coeff i)) id
参数：p : Fin n -> R[X]；h_deg : forall i, (p i).natDegree <= i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用定理 `Nat.lt_of_le_of_lt`：∀ {n m k : ℕ}, n ≤ m → m < k → n < k
-/
theorem matrixOfPolynomials_blockTriangular {R} [Semiring R] {n : ℕ} (p : Fin n → R[X])
    (h_deg : ∀ i, (p i).natDegree ≤ i) :
    Matrix.BlockTriangular (Matrix.of (fun (i j : Fin n) => (p j).coeff i)) id :=
  fun _ j h => by
    exact coeff_eq_zero_of_natDegree_lt <| Nat.lt_of_le_of_lt (h_deg j) h
/-
**Matrix.det_matrixOfPolynomials** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_matrixOfPolynomials {n : Nat} (p : Fin n -> R[X]) (h_deg : forall i, (
p i).natDegree = i) (h_monic : forall i, Monic <| p i) : (Matrix.of (fun (i j : 
Fin n) => (p j).coeff i)).det = 1
参数：p : Fin n -> R[X]；h_deg : forall i, (p i).natDegree = i；h_monic : forall i, M
onic <| p i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_of_isUpperTriangular`：det_of_isUpperTriangular [LinearOrder m
] (h : M.IsUpperTriangular) : M.det = ∏ i : m, M i i
· 使用定理 `Matrix.matrixOfPolynomials_blockTriangular`：matrixOfPolynomials_blockTri
angular {R} [Semiring R] {n : Nat} (p : Fin n -> R[X]) (h_deg : forall i, (p i).
natDegree <= i) : Matrix.BlockTr…
· 使用定理 `Nat.le_of_eq`：∀ {n m : ℕ}, n = m → n ≤ m
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Matrix.of_apply`：of_apply (f : m -> n -> α) (i j) : of f i j = f i j
· 使用定理 `Polynomial.coeff_natDegree`：coeff_natDegree : coeff p (natDegree p) = le
adingCoeff p
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
-/
theorem det_matrixOfPolynomials {n : ℕ} (p : Fin n → R[X])
    (h_deg : ∀ i, (p i).natDegree = i) (h_monic : ∀ i, Monic <| p i) :
    (Matrix.of (fun (i j : Fin n) => (p j).coeff i)).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (Matrix.matrixOfPolynomials_blockTriangular p (fun i ↦
      Nat.le_of_eq (h_deg i)))]
  convert! prod_const_one with x _
  rw [Matrix.of_apply, ← h_deg, coeff_natDegree, (h_monic x).leadingCoeff]

/-! ### Invertible -/


/-
**Matrix.BlockTriangular.toBlock_inverse_mul_toBlock_eq_one** 是 Mathlib 中的一个定理，位
于命名空间 `Matrix.BlockTriangular`。
形式化陈述：∀ {α : Type u_1} {m : Type u_3} {R : Type v} {M : Matrix m m R} {b : m → α
} [inst : CommRing R] [inst_1 : DecidableEq m]   [inst_2 : Fintype m] [inst_3 : 
LinearOrder α] [Invertible M],   M.BlockTriangular b →     ∀ (k : α), ((M⁻¹.toBl
ock (fun i => b i < k) fun i => b i < k) * M.toBlock (fun i => b i < k) fun i =>
 b i < k) = 1
参数：k : α；(M⁻¹.toBlock (fun i => b i < k) fun i => b i < k) * M.toBlock (fun i =>
 b i < k) fun i => b i < k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.toBlock_mul_eq_add`：toBlock_mul_eq_add {m n k : Type*} [Fintype n
] (p : m -> Prop) (q : n -> Prop) [DecidablePred q] (r : k -> Prop) (A : Matrix 
m n R) (B : Mat…
· 使用定理 `Matrix.inv_mul_of_invertible`：inv_mul_of_invertible [Invertible A] : A⁻¹
 * A = 1
· 使用定理 `Matrix.toBlock_one_self`：toBlock_one_self (p : m -> Prop) : Matrix.toBlo
ck (1 : Matrix m m α) p p = 1
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.mul_zero`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Typ
e v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   (M : Matrix m n
 α), …
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a

--- 原说明 ---
### Invertible
-/
theorem BlockTriangular.toBlock_inverse_mul_toBlock_eq_one [LinearOrder α] [Invertible M]
    (hM : BlockTriangular M b) (k : α) :
    ((M⁻¹.toBlock (fun i => b i < k) fun i => b i < k) *
        M.toBlock (fun i => b i < k) fun i => b i < k) =
      1 := by
  let p i := b i < k
  have h_sum :
    M⁻¹.toBlock p p * M.toBlock p p +
        (M⁻¹.toBlock p fun i => ¬p i) * M.toBlock (fun i => ¬p i) p =
      1 := by
    rw [← toBlock_mul_eq_add, inv_mul_of_invertible M, toBlock_one_self]
  have h_zero : M.toBlock (fun i => ¬p i) p = 0 := by
    ext i j
    simpa using hM (lt_of_lt_of_le j.2 (le_of_not_gt i.2))
  simpa [h_zero] using h_sum

/-- The inverse of an upper-left subblock of a block-triangular matrix `M` is the upper-left
subblock of `M⁻¹`. -/
/-
**Matrix.BlockTriangular.inv_toBlock** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.BlockTria
ngular`。
形式化陈述：∀ {α : Type u_1} {m : Type u_3} {R : Type v} {M : Matrix m m R} {b : m → α
} [inst : CommRing R] [inst_1 : DecidableEq m]   [inst_2 : Fintype m] [inst_3 : 
LinearOrder α] [Invertible M],   M.BlockTriangular b →     ∀ (k : α), (M.toBlock
 (fun i => b i < k) fun i => b i < k)⁻¹ = M⁻¹.toBlock (fun i => b i < k) fun i =
> b i < k
参数：k : α；M.toBlock (fun i => b i < k) fun i => b i < k；fun i => b i < k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.inv_eq_left_inv`：inv_eq_left_inv (h : B * A = 1) : A⁻¹ = B
· 使用定理 `Matrix.BlockTriangular.toBlock_inverse_mul_toBlock_eq_one`：∀ {α : Type u
_1} {m : Type u_3} {R : Type v} {M : Matrix m m R} {b : m → α} [inst : CommRing 
R] [inst_1 : DecidableEq m]   [inst_2 : Fintype…

--- 原说明 ---
The inverse of an upper-left subblock of a block-triangular matrix `M` is the up
per-left
subblock of `M⁻¹`.
-/
theorem BlockTriangular.inv_toBlock [LinearOrder α] [Invertible M] (hM : BlockTriangular M b)
    (k : α) :
    (M.toBlock (fun i => b i < k) fun i => b i < k)⁻¹ =
      M⁻¹.toBlock (fun i => b i < k) fun i => b i < k :=
  inv_eq_left_inv <| hM.toBlock_inverse_mul_toBlock_eq_one k

/-- An upper-left subblock of an invertible block-triangular matrix is invertible. -/
@[instance_reducible]
/-
**Matrix.BlockTriangular.invertibleToBlock** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.Blo
ckTriangular`。
形式化陈述：{α : Type u_1} →   {m : Type u_3} →     {R : Type v} →       {M : Matrix m
 m R} →         {b : m → α} →           [inst : CommRing R] →             [inst_
1 : DecidableEq m] →               [inst_2 : Fintype m] →                 [inst_
3 : LinearOrder α] →                   [Invertible M] →                     M.Bl
ockTriangular b → (k : α) → Invertible (M.toBlock (fun i => b i < k) fun i => b 
i < k)
参数：k : α；M.toBlock (fun i => b i < k) fun i => b i < k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An upper-left subblock of an invertible block-triangular matrix is invertible.
-/
def BlockTriangular.invertibleToBlock [LinearOrder α] [Invertible M] (hM : BlockTriangular M b)
    (k : α) : Invertible (M.toBlock (fun i => b i < k) fun i => b i < k) :=
  invertibleOfLeftInverse _ ((⅟M).toBlock (fun i => b i < k) fun i => b i < k) <| by
    simpa only [invOf_eq_nonsing_inv] using hM.toBlock_inverse_mul_toBlock_eq_one k

/-- A lower-left subblock of the inverse of a block-triangular matrix is zero. This is a first step
towards `BlockTriangular.inv_toBlock` below. -/
/-
**Matrix.toBlock_inverse_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：toBlock_inverse_eq_zero [LinearOrder α] [Invertible M] (hM : BlockTriangul
ar M b) (k : α) : (M⁻¹.toBlock (fun i => k <= b i) fun i => b i < k) = 0
参数：hM : BlockTriangular M b；k : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.toBlock_mul_eq_add`：toBlock_mul_eq_add {m n k : Type*} [Fintype n
] (p : m -> Prop) (q : n -> Prop) [DecidablePred q] (r : k -> Prop) (A : Matrix 
m n R) (B : Mat…
· 使用定理 `Matrix.inv_mul_of_invertible`：inv_mul_of_invertible [Invertible A] : A⁻¹
 * A = 1
· 使用定理 `Matrix.toBlock_one_disjoint`：toBlock_one_disjoint {p q : m -> Prop} (hpq
 : Disjoint p q) : Matrix.toBlock (1 : Matrix m m α) p q = 0
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.mul_zero`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Typ
e v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   (M : Matrix m n
 α), …
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Matrix.zero_mul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Typ
e v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype m]   (M : Matrix m n
 α), …
· 使用定理 `Matrix.mul_inv_cancel_right_of_invertible`：mul_inv_cancel_right_of_inver
tible (B : Matrix m n α) [Invertible A] : B * A * A⁻¹ = B

--- 原说明 ---
A lower-left subblock of the inverse of a block-triangular matrix is zero. This 
is a first step
towards `BlockTriangular.inv_toBlock` below.
-/
theorem toBlock_inverse_eq_zero [LinearOrder α] [Invertible M] (hM : BlockTriangular M b) (k : α) :
    (M⁻¹.toBlock (fun i => k ≤ b i) fun i => b i < k) = 0 := by
  let p i := b i < k
  let q i := ¬b i < k
  have h_sum : M⁻¹.toBlock q p * M.toBlock p p + M⁻¹.toBlock q q * M.toBlock q p = 0 := by
    rw [← toBlock_mul_eq_add, inv_mul_of_invertible M, toBlock_one_disjoint]
    rw [disjoint_iff_inf_le]
    exact fun i h => h.1 h.2
  have h_zero : M.toBlock q p = 0 := by
    ext i j
    simpa using hM (lt_of_lt_of_le j.2 <| le_of_not_gt i.2)
  have h_mul_eq_zero : M⁻¹.toBlock q p * M.toBlock p p = 0 := by simpa [h_zero] using h_sum
  have : Invertible (M.toBlock p p) := hM.invertibleToBlock k
  have : (fun i => k ≤ b i) = q := by
    ext
    exact not_lt.symm
  rw [this, ← Matrix.zero_mul (M.toBlock p p)⁻¹, ← h_mul_eq_zero,
    mul_inv_cancel_right_of_invertible]

/-- The inverse of a block-triangular matrix is block-triangular. -/
/-
**Matrix.blockTriangular_inv_of_blockTriangular** 是 Mathlib 中的一个定理，位于命名空间 `Matri
x`。
形式化陈述：blockTriangular_inv_of_blockTriangular [LinearOrder α] [Invertible M] (hM 
: BlockTriangular M b) : BlockTriangular M⁻¹ b
参数：hM : BlockTriangular M b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Finset.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} [inst : Decidable
Eq β] {s : Finset α},   s.Nonempty → ∀ (f : α → β), (Finset.image f s).Nonempty
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Finset.le_max'`：le_max' (x) (H2 : x in s) : x <= s.max' ⟨x, H2⟩
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.toBlock_inverse_eq_zero`：toBlock_inverse_eq_zero [LinearOrder α] 
[Invertible M] (hM : BlockTriangular M b) (k : α) : (M⁻¹.toBlock (fun i => k <= 
b i) fun i => b i < …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.BlockTriangular.submatrix`：∀ {α : Type u_1} {m : Type u_3} {n : T
ype u_4} {R : Type v} {M : Matrix m m R} {b : m → α} [inst : LT α]   [inst_1 : Z
ero R] {f : n → m}, M.…
· 使用定理 `image_subtype_univ_ssubset_image_univ`：image_subtype_univ_ssubset_image_
univ [Fintype α] [DecidableEq β] (k : β) (b : α -> β) (hk : k in Finset.image b 
univ) (p : β -> Prop) [Deci…
· 使用定理 `Finset.max'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.max' H ∈ s
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Matrix.BlockTriangular.inv_toBlock`：∀ {α : Type u_1} {m : Type u_3} {R :
 Type v} {M : Matrix m m R} {b : m → α} [inst : CommRing R] [inst_1 : DecidableE
q m]   [inst_2 : Fintype…

--- 原说明 ---
The inverse of a block-triangular matrix is block-triangular.
-/
theorem blockTriangular_inv_of_blockTriangular [LinearOrder α] [Invertible M]
    (hM : BlockTriangular M b) : BlockTriangular M⁻¹ b := by
  suffices ∀ hs : Finset α, univ.image b = hs → BlockTriangular M⁻¹ b by exact this _ rfl
  intro s hs
  induction s using Finset.strongInduction generalizing m with | H s ih =>
  subst hs
  intro i j hij
  have : Inhabited m := ⟨i⟩
  let k := (univ.image b).max' (univ_nonempty.image _)
  let b' := fun i : { a // b a < k } => b ↑i
  let A := M.toBlock (fun i => b i < k) fun j => b j < k
  obtain hbi | hi : b i = k ∨ _ := (le_max' _ (b i) <| mem_image_of_mem _ <| mem_univ _).eq_or_lt
  · have : M⁻¹.toBlock (fun i => k ≤ b i) (fun i => b i < k) ⟨i, hbi.ge⟩ ⟨j, hbi ▸ hij⟩ = 0 := by
      simp only [toBlock_inverse_eq_zero hM k, Matrix.zero_apply]
    simp [this.symm]
  have : Invertible A := hM.invertibleToBlock _
  have hA : A.BlockTriangular b' := hM.submatrix
  have hb' : image b' univ ⊂ image b univ := by
    convert! image_subtype_univ_ssubset_image_univ k b _ (fun a => a < k) (lt_irrefl _)
    convert! max'_mem (α := α) _ _
  have hij' : b' ⟨j, hij.trans hi⟩ < b' ⟨i, hi⟩ := by simp_rw [b', hij]
  simp [A, hM.inv_toBlock k, (ih (image b' univ) hb' hA rfl hij').symm]

end Matrix

