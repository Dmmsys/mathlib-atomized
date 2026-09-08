/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller, Lu-Ming Zhang
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Hadamard

import Mathlib.Algebra.GroupWithZero.Idempotent
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Adjacency Matrices

This module defines the adjacency matrix of a graph, and provides theorems connecting graph
properties to computational properties of the matrix.

## Main definitions

* `Matrix.IsAdjMatrix`: `A : Matrix V V α` is qualified as an "adjacency matrix" if
  (1) every entry of `A` is `0` or `1`,
  (2) `A` is symmetric,
  (3) every diagonal entry of `A` is `0`.

* `Matrix.IsAdjMatrix.toGraph`: for `A : Matrix V V α` and `h : A.IsAdjMatrix`,
  `h.toGraph` is the simple graph induced by `A`.

* `Matrix.compl`: for `A : Matrix V V α`, `A.compl` is supposed to be
  the adjacency matrix of the complement graph of the graph induced by `A`.

* `SimpleGraph.adjMatrix`: the adjacency matrix of a `SimpleGraph`.

* `SimpleGraph.adjMatrix_pow_apply_eq_card_walk`: each entry of the `n`th power of
  a graph's adjacency matrix counts the number of length-`n` walks between the corresponding
  pair of vertices.

-/

@[expose] public section


open Matrix

open Finset SimpleGraph

variable {α V W : Type*}

namespace Matrix

/-- `A : Matrix V V α` is qualified as an "adjacency matrix" if
(1) every entry of `A` is `0` or `1`,
(2) `A` is symmetric,
(3) every diagonal entry of `A` is `0`. -/
/-
**Matrix.IsAdjMatrix** 是 Mathlib 中的一个结构，位于命名空间 `Matrix`。
形式化陈述：IsAdjMatrix [Zero α] [One α] (A : Matrix V V α) : Prop where zero_or_one :
 forall i j, A i j = 0 ∨ A i j = 1
参数：A : Matrix V V α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`A : Matrix V V α` is qualified as an "adjacency matrix" if
(1) every entry of `A` is `0` or `1`,
(2) `A` is symmetric,
(3) every diagonal entry of `A` is `0`.
-/
structure IsAdjMatrix [Zero α] [One α] (A : Matrix V V α) : Prop where
  zero_or_one : ∀ i j, A i j = 0 ∨ A i j = 1 := by aesop
  symm : A.IsSymm := by aesop
  apply_diag : ∀ i, A i i = 0 := by aesop

namespace IsAdjMatrix

variable {A : Matrix V V α}

/-
**Matrix.IsAdjMatrix.zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsAdjMatrix`。
形式化陈述：∀ {α : Type u_1} {V : Type u_2} [inst : Zero α] [inst_1 : One α], Matrix.I
sAdjMatrix 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
@[simp] protected theorem zero [Zero α] [One α] : (0 : Matrix V V α).IsAdjMatrix where

@[simp]
/-
**Matrix.IsAdjMatrix.apply_diag_ne** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsAdjMatrix
`。
形式化陈述：apply_diag_ne [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (i : 
V) : ¬A i i = 1
参数：h : IsAdjMatrix A；i : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.IsAdjMatrix.apply_diag`：∀ {α : Type u_1} {V : Type u_2} [inst : Z
ero α] [inst_1 : One α] {A : Matrix V V α},   A.IsAdjMatrix → ∀ (i : V), A i i =
 0
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem apply_diag_ne [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (i : V) :
    ¬A i i = 1 := by simp [h.apply_diag i]

@[simp]
/-
**Matrix.IsAdjMatrix.apply_ne_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsAdjMat
rix`。
形式化陈述：apply_ne_one_iff [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (i
 j : V) : ¬A i j = 1 ↔ A i j = 0
参数：h : IsAdjMatrix A；i j : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsAdjMatrix.zero_or_one`：∀ {α : Type u_1} {V : Type u_2} [inst : 
Zero α] [inst_1 : One α] {A : Matrix V V α},   A.IsAdjMatrix → ∀ (i j : V), A i 
j = 0 ∨ A i j = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem apply_ne_one_iff [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (i j : V) :
    ¬A i j = 1 ↔ A i j = 0 := by obtain h | h := h.zero_or_one i j <;> simp [h]

@[simp]
/-
**Matrix.IsAdjMatrix.apply_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsAdjMa
trix`。
形式化陈述：apply_ne_zero_iff [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (
i j : V) : ¬A i j = 0 ↔ A i j = 1
参数：h : IsAdjMatrix A；i j : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.IsAdjMatrix.apply_ne_one_iff`：apply_ne_one_iff [MulZeroOneClass α
] [Nontrivial α] (h : IsAdjMatrix A) (i j : V) : ¬A i j = 1 ↔ A i j = 0
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem apply_ne_zero_iff [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (i j : V) :
    ¬A i j = 0 ↔ A i j = 1 := by rw [← apply_ne_one_iff h, Classical.not_not]

@[simp]
/-
**Matrix.IsAdjMatrix.diag_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsAdjMatrix`
。
形式化陈述：diag_eq_zero [Zero α] [One α] (h : IsAdjMatrix A) : A.diag = 0
参数：h : IsAdjMatrix A。
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
· 使用定理 `Matrix.IsAdjMatrix.apply_diag`：∀ {α : Type u_1} {V : Type u_2} [inst : Z
ero α] [inst_1 : One α] {A : Matrix V V α},   A.IsAdjMatrix → ∀ (i : V), A i i =
 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diag_eq_zero [Zero α] [One α] (h : IsAdjMatrix A) : A.diag = 0 := by
  ext
  simp [h.apply_diag]
/-
**Matrix.IsAdjMatrix.submatrix** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsAdjMatrix`。
形式化陈述：∀ {α : Type u_1} {V : Type u_2} {W : Type u_3} {A : Matrix V V α} [inst : 
Zero α] [inst_1 : One α],   A.IsAdjMatrix → ∀ (f : W → V), (A.submatrix f f).IsA
djMatrix
参数：f : W → V；A.submatrix f f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Matrix.IsAdjMatrix.zero_or_one`：∀ {α : Type u_1} {V : Type u_2} [inst : 
Zero α] [inst_1 : One α] {A : Matrix V V α},   A.IsAdjMatrix → ∀ (i j : V), A i 
j = 0 ∨ A i j = 1
· 使用定理 `Matrix.IsSymm.submatrix`：∀ {α : Type u_1} {n : Type u_3} {m : Type u_4} 
{A : Matrix n n α}, A.IsSymm → ∀ (f : m → n), (A.submatrix f f).IsSymm
· 使用定理 `Matrix.IsAdjMatrix.symm`：∀ {α : Type u_1} {V : Type u_2} [inst : Zero α]
 [inst_1 : One α] {A : Matrix V V α}, A.IsAdjMatrix → A.IsSymm
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsAdjMatrix.apply_diag`：∀ {α : Type u_1} {V : Type u_2} [inst : Z
ero α] [inst_1 : One α] {A : Matrix V V α},   A.IsAdjMatrix → ∀ (i : V), A i i =
 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem submatrix [Zero α] [One α] (h : IsAdjMatrix A) (f : W → V) :
    A.submatrix f f |>.IsAdjMatrix where
  zero_or_one i j := by simp [h.zero_or_one]
  symm := h.symm.submatrix f
  apply_diag i := by simp [h.apply_diag]
/-
**Matrix.IsAdjMatrix._root_.Matrix.isAdjMatrix_submatrix_iff** 是 Mathlib 中的一个定理，
位于命名空间 `Matrix.IsAdjMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Matrix.isAdjMatrix_submatrix_iff [Zero α] [One α] {f : W → V} (hf : f.Surjective) :
    (A.submatrix f f).IsAdjMatrix ↔ A.IsAdjMatrix := by
  refine ⟨fun h ↦ ?_, (·.submatrix f)⟩
  rw [← A.submatrix_id_id, ← f.comp_surjInv hf]
  apply h.submatrix
/-
**Matrix.IsAdjMatrix.reindex** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsAdjMatrix`。
形式化陈述：∀ {α : Type u_1} {V : Type u_2} {W : Type u_3} {A : Matrix V V α} [inst : 
Zero α] [inst_1 : One α],   A.IsAdjMatrix → ∀ (f : V ≃ W), ((Matrix.reindex f f)
 A).IsAdjMatrix
参数：f : V ≃ W；(Matrix.reindex f f) A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsAdjMatrix.submatrix`：∀ {α : Type u_1} {V : Type u_2} {W : Type 
u_3} {A : Matrix V V α} [inst : Zero α] [inst_1 : One α],   A.IsAdjMatrix → ∀ (f
 : W → V), (A.subm…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem reindex [Zero α] [One α] (h : IsAdjMatrix A) (f : V ≃ W) : A.reindex f f |>.IsAdjMatrix :=
  h.submatrix f.symm
/-
**Matrix.IsAdjMatrix._root_.Matrix.isAdjMatrix_reindex_iff** 是 Mathlib 中的一个定理，位于
命名空间 `Matrix.IsAdjMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Matrix.isAdjMatrix_reindex_iff [Zero α] [One α] {f : V ≃ W} :
    (A.reindex f f).IsAdjMatrix ↔ A.IsAdjMatrix :=
  isAdjMatrix_submatrix_iff f.symm.surjective

/-- For `A : Matrix V V α` and `h : IsAdjMatrix A`,
`h.toGraph` is the simple graph whose adjacency matrix is `A`. -/
@[simps]
/-
**Matrix.IsAdjMatrix.toGraph** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.IsAdjMatrix`。
形式化陈述：toGraph [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) : SimpleGra
ph V where Adj i j
参数：h : IsAdjMatrix A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `A : Matrix V V α` and `h : IsAdjMatrix A`,
`h.toGraph` is the simple graph whose adjacency matrix is `A`.
-/
def toGraph [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) : SimpleGraph V where
  Adj i j := A i j = 1
  symm.symm i j hij := by rwa [h.symm.apply i j]

set_option backward.isDefEq.respectTransparency.types false in
/-
**Matrix.IsAdjMatrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix.IsAdjMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulZeroOneClass α] [Nontrivial α] [DecidableEq α] (h : IsAdjMatrix A) :
    DecidableRel h.toGraph.Adj := by
  simp only [toGraph]
  infer_instance

variable (A) in
/-- A homomorphism of the graph of a submatrix of an adjacency matrix to the graph of the
adjacency matrix itself -/
@[simps]
/-
**Matrix.IsAdjMatrix.toGraphSubmatrixHom** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.IsAdj
Matrix`。
形式化陈述：toGraphSubmatrixHom [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A)
 (f : W -> V) : (h.submatrix f).toGraph ->g h.toGraph where toFun
参数：h : IsAdjMatrix A；f : W -> V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homomorphism of the graph of a submatrix of an adjacency matrix to the graph o
f the
adjacency matrix itself
-/
def toGraphSubmatrixHom [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (f : W → V) :
    (h.submatrix f).toGraph →g h.toGraph where
  toFun := f
  map_rel' := by simp

variable (A) in
/-- An embedding of the graph of a submatrix of an adjacency matrix to the graph of the
adjacency matrix itself, when the submatrix is given by an embedding -/
/-
**Matrix.IsAdjMatrix.toGraphSubmatrixEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Matrix
.IsAdjMatrix`。
形式化陈述：toGraphSubmatrixEmbedding [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMat
rix A) (f : W ↪ V) : (h.submatrix f).toGraph ↪g h.toGraph where __
参数：h : IsAdjMatrix A；f : W ↪ V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An embedding of the graph of a submatrix of an adjacency matrix to the graph of 
the
adjacency matrix itself, when the submatrix is given by an embedding
-/
def toGraphSubmatrixEmbedding [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (f : W ↪ V) :
    (h.submatrix f).toGraph ↪g h.toGraph where
  __ := f
  map_rel_iff' := by simp

variable (A) in
@[simp]
/-
**Matrix.IsAdjMatrix.toGraphSubmatrixEmbedding_apply** 是 Mathlib 中的一个定理，位于命名空间 `
Matrix.IsAdjMatrix`。
形式化陈述：toGraphSubmatrixEmbedding_apply [MulZeroOneClass α] [Nontrivial α] (h : A.
IsAdjMatrix) (f : W -> V) (v : W) : (toGraphSubmatrixHom A h f) v = f v
参数：h : A.IsAdjMatrix；f : W -> V；v : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsAdjMatrix.submatrix`：∀ {α : Type u_1} {V : Type u_2} {W : Type 
u_3} {A : Matrix V V α} [inst : Zero α] [inst_1 : One α],   A.IsAdjMatrix → ∀ (f
 : W → V), (A.subm…
-/
theorem toGraphSubmatrixEmbedding_apply [MulZeroOneClass α] [Nontrivial α] (h : A.IsAdjMatrix)
    (f : W → V) (v : W) : (toGraphSubmatrixHom A h f) v = f v :=
  rfl

variable (A) in
/-- An isomorphism of the graph of a reindexing of an adjacency matrix to the graph of the
adjacency matrix itself -/
@[simps!]
/-
**Matrix.IsAdjMatrix.toGraphReindexIso** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.IsAdjMa
trix`。
形式化陈述：toGraphReindexIso [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (
f : V ≃ W) : (h.reindex f).toGraph ≃g h.toGraph where __
参数：h : IsAdjMatrix A；f : V ≃ W。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
An isomorphism of the graph of a reindexing of an adjacency matrix to the graph 
of the
adjacency matrix itself
-/
def toGraphReindexIso [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (f : V ≃ W) :
    (h.reindex f).toGraph ≃g h.toGraph where
  __ := f.symm
  map_rel_iff' := by simp
/-
**Matrix.IsAdjMatrix.hadamard_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsAdjMatrix
`。
形式化陈述：∀ {α : Type u_1} {V : Type u_2} [inst : MulZeroOneClass α] {A : Matrix V V
 α}, A.IsAdjMatrix → A.hadamard A = A
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Matrix.IsAdjMatrix.zero_or_one`：∀ {α : Type u_1} {V : Type u_2} [inst : 
Zero α] [inst_1 : One α] {A : Matrix V V α},   A.IsAdjMatrix → ∀ (i j : V), A i 
j = 0 ∨ A i j = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
@[simp] theorem hadamard_self [MulZeroOneClass α] {A : Matrix V V α} (hA : A.IsAdjMatrix) :
    A ⊙ A = A := by ext i j; have := hA.zero_or_one i j; aesop

end IsAdjMatrix

/-
**Matrix.isAdjMatrix_iff_hadamard** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isAdjMatrix_iff_hadamard [DecidableEq V] [MonoidWithZero α] [IsLeftCancelM
ulZero α] {A : Matrix V V α} : A.IsAdjMatrix ↔ (A ⊙ A = A ∧ A.IsSymm ∧ 1 ⊙ A = 0
)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem isAdjMatrix_iff_hadamard [DecidableEq V] [MonoidWithZero α]
    [IsLeftCancelMulZero α] {A : Matrix V V α} :
    A.IsAdjMatrix ↔ (A ⊙ A = A ∧ A.IsSymm ∧ 1 ⊙ A = 0) := by
  simp only [hadamard_self_eq_self_iff, IsIdempotentElem.iff_eq_zero_or_one,
    one_hadamard_eq_zero_iff, funext_iff, diag, Pi.zero_apply]
  grind [IsAdjMatrix]

/-- For `A : Matrix V V α`, `A.compl` is supposed to be the adjacency matrix of
the complement graph of the graph induced by `A.adjMatrix`. -/
/-
**Matrix.compl** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：compl [Zero α] [One α] [DecidableEq α] [DecidableEq V] (A : Matrix V V α) 
: Matrix V V α
参数：A : Matrix V V α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `A : Matrix V V α`, `A.compl` is supposed to be the adjacency matrix of
the complement graph of the graph induced by `A.adjMatrix`.
-/
def compl [Zero α] [One α] [DecidableEq α] [DecidableEq V] (A : Matrix V V α) : Matrix V V α :=
  of fun i j ↦ if i = j then 0 else if A i j = 0 then 1 else 0

section Compl

variable [DecidableEq α] [DecidableEq V] (A : Matrix V V α)

@[simp]
/-
**Matrix.compl_apply_diag** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：compl_apply_diag [Zero α] [One α] (i : V) : A.compl i i = 0
参数：i : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem compl_apply_diag [Zero α] [One α] (i : V) : A.compl i i = 0 := by simp [compl]

@[simp]
/-
**Matrix.compl_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：compl_apply [Zero α] [One α] (i j : V) : A.compl i j = 0 ∨ A.compl i j = 1
参数：i j : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem compl_apply [Zero α] [One α] (i j : V) : A.compl i j = 0 ∨ A.compl i j = 1 := by
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
  without the `simp`. This is probably a problem at Mathlib's end rather than `grind`'s,
  as we are relying on seeing through the definition of `Matrix`, and `of`. -/
  simp [compl]
  grind

@[simp]
/-
**Matrix.isSymm_compl** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isSymm_compl [Zero α] [One α] (h : A.IsSymm) : A.compl.IsSymm
参数：h : A.IsSymm。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Matrix.IsSymm.apply`：∀ {α : Type u_1} {n : Type u_3} {A : Matrix n n α},
 A.IsSymm → ∀ (i j : n), A j i = A i j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isSymm_compl [Zero α] [One α] (h : A.IsSymm) : A.compl.IsSymm := by
  ext
  simp [compl, h.apply, eq_comm]

@[simp]
/-
**Matrix.isAdjMatrix_compl** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isAdjMatrix_compl [Zero α] [One α] (h : A.IsSymm) : IsAdjMatrix A.compl
参数：h : A.IsSymm。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.compl_apply_diag`：compl_apply_diag [Zero α] [One α] (i : V) : A.c
ompl i i = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isAdjMatrix_compl [Zero α] [One α] (h : A.IsSymm) : IsAdjMatrix A.compl :=
  { symm := by simp [h] }
/-
**Matrix.IsAdjMatrix.compl_inj** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsAdjMatrix`。
形式化陈述：∀ {α : Type u_1} {V : Type u_2} [inst : DecidableEq α] [inst_1 : Decidable
Eq V] [inst_2 : Zero α] [inst_3 : One α]   {A B : Matrix V V α}, A.IsAdjMatrix →
 B.IsAdjMatrix → (A.compl = B.compl ↔ A = B)
参数：A.compl = B.compl ↔ A = B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
-/
theorem IsAdjMatrix.compl_inj [Zero α] [One α] {A B : Matrix V V α}
    (hA : A.IsAdjMatrix) (hB : B.IsAdjMatrix) : A.compl = B.compl ↔ A = B :=
  ⟨fun h ↦ ext fun i j ↦ by
    #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
    without the `simp`. This is probably a problem at Mathlib's end rather than `grind`'s,
    as we are relying on seeing through the definition of `Matrix`, and `of`.
    The original proof was: `grind [of, congr($h i j), compl, IsAdjMatrix]` -/
    simp [compl] at h; grind [congr($h i j), IsAdjMatrix], fun h ↦ h ▸ rfl⟩
/-
**Matrix.IsAdjMatrix.compl_compl** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsAdjMatrix`。
形式化陈述：∀ {α : Type u_1} {V : Type u_2} [inst : DecidableEq α] [inst_1 : Decidable
Eq V] [inst_2 : Zero α] [inst_3 : One α]   {A : Matrix V V α}, A.IsAdjMatrix → A
.compl.compl = A
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
@[simp] theorem IsAdjMatrix.compl_compl [Zero α] [One α] {A : Matrix V V α} (hA : A.IsAdjMatrix) :
    A.compl.compl = A := by
  ext
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
  without the `simp`. This is probably a problem at Mathlib's end rather than `grind`'s,
  as we are relying on seeing through the definition of `Matrix`, and `of`. The original proof was:
  `grind [of, compl, IsAdjMatrix]` -/
  simp [compl]; grind [compl, IsAdjMatrix]

namespace IsAdjMatrix

variable {A}

@[simp]
/-
**Matrix.IsAdjMatrix.compl** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsAdjMatrix`。
形式化陈述：compl [Zero α] [One α] (h : IsAdjMatrix A) : IsAdjMatrix A.compl
参数：h : IsAdjMatrix A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.isAdjMatrix_compl`：isAdjMatrix_compl [Zero α] [One α] (h : A.IsSy
mm) : IsAdjMatrix A.compl
· 使用定理 `Matrix.IsAdjMatrix.symm`：∀ {α : Type u_1} {V : Type u_2} [inst : Zero α]
 [inst_1 : One α] {A : Matrix V V α}, A.IsAdjMatrix → A.IsSymm
-/
theorem compl [Zero α] [One α] (h : IsAdjMatrix A) : IsAdjMatrix A.compl :=
  isAdjMatrix_compl A h.symm
/-
**Matrix.IsAdjMatrix.toGraph_compl_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsAdjMat
rix`。
形式化陈述：toGraph_compl_eq [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) : 
h.compl.toGraph = h.toGraphᶜ
参数：h : IsAdjMatrix A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `Matrix.IsAdjMatrix.compl`：compl [Zero α] [One α] (h : IsAdjMatrix A) : I
sAdjMatrix A.compl
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.IsAdjMatrix.zero_or_one`：∀ {α : Type u_1} {V : Type u_2} [inst : 
Zero α] [inst_1 : One α] {A : Matrix V V α},   A.IsAdjMatrix → ∀ (i j : V), A i 
j = 0 ∨ A i j = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Matrix.IsAdjMatrix.toGraph_adj`：∀ {α : Type u_1} {V : Type u_2} {A : Mat
rix V V α} [inst : MulZeroOneClass α] [inst_1 : Nontrivial α]   (h : A.IsAdjMatr
ix) (i j : V), h.toG…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
theorem toGraph_compl_eq [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) :
    h.compl.toGraph = h.toGraphᶜ := by
  ext v w
  rcases h.zero_or_one v w with h | h <;> by_cases hvw : v = w <;> simp [Matrix.compl, h, hvw]

end IsAdjMatrix

end Compl

end Matrix

namespace SimpleGraph

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable (α) in
/-- `adjMatrix G α` is the matrix `A` such that `A i j = (1 : α)` if `i` and `j` are
  adjacent in the simple graph `G`, and otherwise `A i j = 0`. -/
/-
**SimpleGraph.adjMatrix** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：adjMatrix [Zero α] [One α] : Matrix V V α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`adjMatrix G α` is the matrix `A` such that `A i j = (1 : α)` if `i` and `j` are
  adjacent in the simple graph `G`, and otherwise `A i j = 0`.
-/
def adjMatrix [Zero α] [One α] : Matrix V V α :=
  of fun i j => if G.Adj i j then (1 : α) else 0

-- TODO: set as an equation lemma for `adjMatrix`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
/-
**SimpleGraph.adjMatrix_apply** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：adjMatrix_apply (v w : V) [Zero α] [One α] : G.adjMatrix α v w = if G.Adj 
v w then 1 else 0
参数：v w : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem adjMatrix_apply (v w : V) [Zero α] [One α] :
    G.adjMatrix α v w = if G.Adj v w then 1 else 0 :=
  rfl

@[simp]
/-
**SimpleGraph.adjMatrix_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：adjMatrix_bot [Zero α] [One α] : (⊥ : SimpleGraph V).adjMatrix α = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem adjMatrix_bot [Zero α] [One α] :
    (⊥ : SimpleGraph V).adjMatrix α = 0 := by
  ext; simp

@[simp]
/-
**SimpleGraph.adjMatrix_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：adjMatrix_top [DecidableEq V] [Ring α] : (⊤ : SimpleGraph V).adjMatrix α =
 .of (fun i j => if i = j then 0 else 1)
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
· 使用定理 `SimpleGraph.adjMatrix.congr_simp`：∀ (α : Type u_1) {V : Type u_2} (G G_1
 : SimpleGraph V),   G = G_1 →     ∀ {inst : DecidableRel G.Adj} [inst_1 : Decid
ableRel G_1.Adj] [inst…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem adjMatrix_top [DecidableEq V] [Ring α] :
    (⊤ : SimpleGraph V).adjMatrix α = .of (fun i j ↦ if i = j then 0 else 1) := by
  ext i j
  cases eq_or_ne i j <;> simp [‹_›]

@[simp]
/-
**SimpleGraph.transpose_adjMatrix** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：transpose_adjMatrix [Zero α] [One α] : (G.adjMatrix α)ᵀ = G.adjMatrix α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem transpose_adjMatrix [Zero α] [One α] : (G.adjMatrix α)ᵀ = G.adjMatrix α := by
  ext
  simp [adj_comm]

@[simp]
/-
**SimpleGraph.isSymm_adjMatrix** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isSymm_adjMatrix [Zero α] [One α] : (G.adjMatrix α).IsSymm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.transpose_adjMatrix`：transpose_adjMatrix [Zero α] [One α] : 
(G.adjMatrix α)ᵀ = G.adjMatrix α
-/
theorem isSymm_adjMatrix [Zero α] [One α] : (G.adjMatrix α).IsSymm :=
  transpose_adjMatrix G

variable (α)

/-- The adjacency matrix of `G` is an adjacency matrix. -/
@[simp]
/-
**SimpleGraph.isAdjMatrix_adjMatrix** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isAdjMatrix_adjMatrix [Zero α] [One α] : (G.adjMatrix α).IsAdjMatrix where
 zero_or_one
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The adjacency matrix of `G` is an adjacency matrix.
-/
theorem isAdjMatrix_adjMatrix [Zero α] [One α] : (G.adjMatrix α).IsAdjMatrix where
  zero_or_one := by grind [adjMatrix_apply]
/-
**SimpleGraph.diag_adjMatrix** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：diag_adjMatrix [Zero α] [One α] : (G.adjMatrix α).diag = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsAdjMatrix.diag_eq_zero`：diag_eq_zero [Zero α] [One α] (h : IsAd
jMatrix A) : A.diag = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diag_adjMatrix [Zero α] [One α] : (G.adjMatrix α).diag = 0 := by
  simp

/-- The graph induced by the adjacency matrix of `G` is `G` itself. -/
@[simp]
/-
**SimpleGraph.toGraph_adjMatrix_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：toGraph_adjMatrix_eq [MulZeroOneClass α] [Nontrivial α] : (G.isAdjMatrix_a
djMatrix α).toGraph = G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `SimpleGraph.isAdjMatrix_adjMatrix`：isAdjMatrix_adjMatrix [Zero α] [One α
] : (G.adjMatrix α).IsAdjMatrix where zero_or_one
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.IsAdjMatrix.toGraph_adj`：∀ {α : Type u_1} {V : Type u_2} {A : Mat
rix V V α} [inst : MulZeroOneClass α] [inst_1 : Nontrivial α]   (h : A.IsAdjMatr
ix) (i j : V), h.toG…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a

--- 原说明 ---
The graph induced by the adjacency matrix of `G` is `G` itself.
-/
theorem toGraph_adjMatrix_eq [MulZeroOneClass α] [Nontrivial α] :
    (G.isAdjMatrix_adjMatrix α).toGraph = G := by
  ext
  simp only [IsAdjMatrix.toGraph_adj, adjMatrix_apply, ite_eq_left_iff, zero_ne_one]
  apply Classical.not_not
/-
**SimpleGraph.compl_adjMatrix_eq_adjMatrix_compl** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph`。
形式化陈述：compl_adjMatrix_eq_adjMatrix_compl [DecidableEq V] [DecidableEq α] [Zero α
] [One α] : (G.adjMatrix α).compl = Gᶜ.adjMatrix α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem compl_adjMatrix_eq_adjMatrix_compl [DecidableEq V] [DecidableEq α] [Zero α] [One α] :
    (G.adjMatrix α).compl = Gᶜ.adjMatrix α := by aesop (add simp [Matrix.compl])

variable {G} in
@[simp]
/-
**SimpleGraph.Embedding.submatrix_adjMatrix** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.Embedding`。
形式化陈述：∀ (α : Type u_1) {V : Type u_2} {W : Type u_3} {G : SimpleGraph V} [inst :
 DecidableRel G.Adj] [inst_1 : Zero α]   [inst_2 : One α] {H : SimpleGraph W} [i
nst_3 : DecidableRel H.Adj] (f : G ↪g H),   (SimpleGraph.adjMatrix α H).submatri
x ⇑f ⇑f = SimpleGraph.adjMatrix α G
参数：α : Type u_1；f : G ↪g H；SimpleGraph.adjMatrix α H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Embedding.submatrix_adjMatrix [Zero α] [One α] {H : SimpleGraph W} [DecidableRel H.Adj]
    (f : G ↪g H) : (H.adjMatrix α).submatrix f f = G.adjMatrix α := by
  ext
  simp

variable {G} in
/-
**SimpleGraph.Iso.reindex_adjMatrix** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：∀ (α : Type u_1) {V : Type u_2} {W : Type u_3} {G : SimpleGraph V} [inst :
 DecidableRel G.Adj] [inst_1 : Zero α]   [inst_2 : One α] {H : SimpleGraph W} [i
nst_3 : DecidableRel H.Adj] (f : G ≃g H),   (Matrix.reindex ↑f ↑f) (SimpleGraph.
adjMatrix α G) = SimpleGraph.adjMatrix α H
参数：α : Type u_1；f : G ≃g H；Matrix.reindex ↑f ↑f；SimpleGraph.adjMatrix α G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Embedding.submatrix_adjMatrix`：∀ (α : Type u_1) {V : Type u_
2} {W : Type u_3} {G : SimpleGraph V} [inst : DecidableRel G.Adj] [inst_1 : Zero
 α]   [inst_2 : One α] {H : Sim…
-/
theorem Iso.reindex_adjMatrix [Zero α] [One α] {H : SimpleGraph W} [DecidableRel H.Adj]
    (f : G ≃g H) : (G.adjMatrix α).reindex f f = H.adjMatrix α :=
  f.symm.toEmbedding.submatrix_adjMatrix α

variable {G} in
/-
**SimpleGraph.IsCompl.adjMatrix_add_adjMatrix_eq_adjMatrix_completeGraph** 是 Mat
hlib 中的一个定理，位于命名空间 `SimpleGraph.IsCompl`。
形式化陈述：∀ (α : Type u_1) {V : Type u_2} {G : SimpleGraph V} [inst : DecidableRel G
.Adj] [inst_1 : DecidableEq V]   [inst_2 : AddZeroClass α] [inst_3 : One α] {H :
 SimpleGraph V} [inst_4 : DecidableRel H.Adj],   IsCompl G H →     SimpleGraph.a
djMatrix α G + SimpleGraph.adjMatrix α H = SimpleGraph.adjMatrix α (SimpleGraph.
completeGraph V)
参数：α : Type u_1；SimpleGraph.completeGraph V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.compl_eq`：IsCompl.compl_eq (h : IsCompl a b) : aᶜ = b
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem IsCompl.adjMatrix_add_adjMatrix_eq_adjMatrix_completeGraph [DecidableEq V] [AddZeroClass α]
    [One α] {H : SimpleGraph V} [DecidableRel H.Adj] (h : IsCompl G H) :
    G.adjMatrix α + H.adjMatrix α = (completeGraph V).adjMatrix α := calc
  _ = G.adjMatrix α + Gᶜ.adjMatrix α := by have := h.compl_eq; subst this; congr
  _ = _ := by aesop (add simp Matrix.compl)
/-
**SimpleGraph.adjMatrix_add_compl_adjMatrix_eq_adjMatrix_completeGraph** 是 Mathl
ib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ (α : Type u_1) {V : Type u_2} (G : SimpleGraph V) [inst : DecidableRel G
.Adj] [inst_1 : DecidableEq V]   [inst_2 : DecidableEq α] [inst_3 : AddZeroClass
 α] [inst_4 : One α],   SimpleGraph.adjMatrix α G + (SimpleGraph.adjMatrix α G).
compl = SimpleGraph.adjMatrix α (SimpleGraph.completeGraph V)
参数：α : Type u_1；G : SimpleGraph V；SimpleGraph.adjMatrix α G；SimpleGraph.complete
Graph V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsCompl.adjMatrix_add_adjMatrix_eq_adjMatrix_completeGraph`：
∀ (α : Type u_1) {V : Type u_2} {G : SimpleGraph V} [inst : DecidableRel G.Adj] 
[inst_1 : DecidableEq V]   [inst_2 : AddZeroClass α] [inst_3…
· 使用定理 `isCompl_compl`：isCompl_compl : IsCompl x xᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.compl_adjMatrix_eq_adjMatrix_compl`：compl_adjMatrix_eq_adjMa
trix_compl [DecidableEq V] [DecidableEq α] [Zero α] [One α] : (G.adjMatrix α).co
mpl = Gᶜ.adjMatrix α
-/
@[simp] theorem adjMatrix_add_compl_adjMatrix_eq_adjMatrix_completeGraph [DecidableEq V]
    [DecidableEq α] [AddZeroClass α] [One α] :
    G.adjMatrix α + (G.adjMatrix α).compl = (completeGraph V).adjMatrix α :=
  G.compl_adjMatrix_eq_adjMatrix_compl α ▸
    isCompl_compl.adjMatrix_add_adjMatrix_eq_adjMatrix_completeGraph α

/-- The sum of the identity, the adjacency matrix, and its complement is the all-ones matrix. -/
/-
**SimpleGraph.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one** 是 Mathlib 中的一个定理
，位于命名空间 `SimpleGraph`。
形式化陈述：one_add_adjMatrix_add_compl_adjMatrix_eq_of_one [DecidableEq V] [Decidable
Eq α] [AddMonoid α] [One α] : 1 + G.adjMatrix α + (G.adjMatrix α).compl = of 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `SimpleGraph.adjMatrix_add_compl_adjMatrix_eq_adjMatrix_completeGraph`：∀ 
(α : Type u_1) {V : Type u_2} (G : SimpleGraph V) [inst : DecidableRel G.Adj] [i
nst_1 : DecidableEq V]   [inst_2 : DecidableEq α] [inst_3 …
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Matrix.one_apply_ne`：one_apply_ne {i j} : i != j -> (1 : Matrix n n α) i
 j = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Matrix.one_apply_eq`：one_apply_eq (i) : (1 : Matrix n n α) i i = 1
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a

--- 原说明 ---
The sum of the identity, the adjacency matrix, and its complement is the all-one
s matrix.
-/
theorem one_add_adjMatrix_add_compl_adjMatrix_eq_of_one [DecidableEq V] [DecidableEq α]
    [AddMonoid α] [One α] : 1 + G.adjMatrix α + (G.adjMatrix α).compl = of 1 := by
  aesop (add simp [add_assoc])

@[deprecated (since := "2026-01-30")] alias one_add_adjMatrix_add_compl_adjMatrix_eq_allOnes :=
  one_add_adjMatrix_add_compl_adjMatrix_eq_of_one

variable (V)
/-
**SimpleGraph.compl_adjMatrix_completeGraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph`。
形式化陈述：∀ (α : Type u_1) (V : Type u_2) [inst : Zero α] [inst_1 : One α] [inst_2 :
 DecidableEq α] [inst_3 : DecidableEq V],   (SimpleGraph.adjMatrix α (SimpleGrap
h.completeGraph V)).compl = 0
参数：α : Type u_1；V : Type u_2；SimpleGraph.adjMatrix α (SimpleGraph.completeGraph 
V)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
-/
@[simp] theorem compl_adjMatrix_completeGraph [Zero α] [One α] [DecidableEq α] [DecidableEq V] :
    ((completeGraph V).adjMatrix α).compl = 0 := by aesop (add simp Matrix.compl)
/-
**SimpleGraph._root_.Matrix.compl_zero** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem _root_.Matrix.compl_zero [Zero α] [One α] [DecidableEq α] [DecidableEq V] :
    (0 : Matrix V V α).compl = (completeGraph V).adjMatrix α := by simp [← IsAdjMatrix.compl_inj]
/-
**SimpleGraph.adjMatrix_completeGraph_eq_of_one_sub_one** 是 Mathlib 中的一个定理，位于命名空
间 `SimpleGraph`。
形式化陈述：adjMatrix_completeGraph_eq_of_one_sub_one [AddGroup α] [One α] [DecidableE
q V] : (completeGraph V).adjMatrix α = of 1 - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
· 使用定理 `Matrix.one_apply`：one_apply {i j} : (1 : Matrix n n α) i j = if i = j th
en 1 else 0
· 使用定理 `sub_ite`：∀ {α : Type u_2} (P : Prop) [inst : Decidable P] [inst_1 : Sub 
α] (a b c : α),   (a - if P then b else c) = if P then a - b else a - c
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem adjMatrix_completeGraph_eq_of_one_sub_one [AddGroup α] [One α] [DecidableEq V] :
    (completeGraph V).adjMatrix α = of 1 - 1 := by ext; simp [one_apply, sub_ite]
/-
**SimpleGraph._root_.Matrix.compl_zero_eq_of_one_sub_one** 是 Mathlib 中的一个定理，位于命名
空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Matrix.compl_zero_eq_of_one_sub_one [AddGroup α] [One α] [DecidableEq V]
    [DecidableEq α] : (0 : Matrix V V α).compl = of 1 - 1 := by
  simp [adjMatrix_completeGraph_eq_of_one_sub_one]
/-
**SimpleGraph._root_.Matrix.compl_of_one_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem _root_.Matrix.compl_of_one_sub_one [AddGroup α] [One α] [DecidableEq V]
    [DecidableEq α] : (of 1 - 1 : Matrix V V α).compl = 0 := by
  simp [← adjMatrix_completeGraph_eq_of_one_sub_one]

variable {V}
/-
**SimpleGraph.adjMatrix_hadamard_self** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：adjMatrix_hadamard_self [MulZeroOneClass α] : G.adjMatrix α ⊙ G.adjMatrix 
α = G.adjMatrix α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsAdjMatrix.hadamard_self`：∀ {α : Type u_1} {V : Type u_2} [inst 
: MulZeroOneClass α] {A : Matrix V V α}, A.IsAdjMatrix → A.hadamard A = A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem adjMatrix_hadamard_self [MulZeroOneClass α] :
    G.adjMatrix α ⊙ G.adjMatrix α = G.adjMatrix α := by simp

variable {α}

section fintype
variable [Fintype V]

@[simp]
/-
**SimpleGraph.adjMatrix_dotProduct** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：adjMatrix_dotProduct [NonAssocSemiring α] (v : V) (vec : V -> α) : G.adjMa
trix α v ⬝ᵥ vec = ∑ u in G.neighborFinset v, vec u
参数：v : V；vec : V -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `SimpleGraph.neighborFinset_eq_filter`：neighborFinset_eq_filter {v : V} [
DecidableRel G.Adj] : G.neighborFinset v = ({w | G.Adj v w} : Finset _)
· 使用定理 `Finset.sum_filter`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst 
: AddCommMonoid M] (p : ι → Prop) [inst_1 : DecidablePred p]   (f : ι → M), ∑ a 
∈ s wit…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem adjMatrix_dotProduct [NonAssocSemiring α] (v : V) (vec : V → α) :
    G.adjMatrix α v ⬝ᵥ vec = ∑ u ∈ G.neighborFinset v, vec u := by
  simp [neighborFinset_eq_filter, dotProduct, sum_filter]

@[simp]
/-
**SimpleGraph.dotProduct_adjMatrix** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：dotProduct_adjMatrix [NonAssocSemiring α] (v : V) (vec : V -> α) : vec ⬝ᵥ 
G.adjMatrix α v = ∑ u in G.neighborFinset v, vec u
参数：v : V；vec : V -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `SimpleGraph.neighborFinset_eq_filter`：neighborFinset_eq_filter {v : V} [
DecidableRel G.Adj] : G.neighborFinset v = ({w | G.Adj v w} : Finset _)
· 使用定理 `Finset.sum_filter`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst 
: AddCommMonoid M] (p : ι → Prop) [inst_1 : DecidablePred p]   (f : ι → M), ∑ a 
∈ s wit…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dotProduct_adjMatrix [NonAssocSemiring α] (v : V) (vec : V → α) :
    vec ⬝ᵥ G.adjMatrix α v = ∑ u ∈ G.neighborFinset v, vec u := by
  simp [neighborFinset_eq_filter, dotProduct, sum_filter]

@[simp]
/-
**SimpleGraph.adjMatrix_mulVec_apply** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：adjMatrix_mulVec_apply [NonAssocSemiring α] (v : V) (vec : V -> α) : (G.ad
jMatrix α *ᵥ vec) v = ∑ u in G.neighborFinset v, vec u
参数：v : V；vec : V -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mulVec.eq_1`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst :
 NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   (M : Matrix m n α) (v : n →
 α) (x :…
· 使用定理 `SimpleGraph.adjMatrix_dotProduct`：adjMatrix_dotProduct [NonAssocSemiring
 α] (v : V) (vec : V -> α) : G.adjMatrix α v ⬝ᵥ vec = ∑ u in G.neighborFinset v,
 vec u
-/
theorem adjMatrix_mulVec_apply [NonAssocSemiring α] (v : V) (vec : V → α) :
    (G.adjMatrix α *ᵥ vec) v = ∑ u ∈ G.neighborFinset v, vec u := by
  rw [mulVec, adjMatrix_dotProduct]

@[simp]
/-
**SimpleGraph.adjMatrix_vecMul_apply** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：adjMatrix_vecMul_apply [NonAssocSemiring α] (v : V) (vec : V -> α) : (vec 
ᵥ* G.adjMatrix α) v = ∑ u in G.neighborFinset v, vec u
参数：v : V；vec : V -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.transpose_apply`：transpose_apply (M : Matrix m n α) (i j) : trans
pose M i j = M j i
· 使用定理 `SimpleGraph.transpose_adjMatrix`：transpose_adjMatrix [Zero α] [One α] : 
(G.adjMatrix α)ᵀ = G.adjMatrix α
-/
theorem adjMatrix_vecMul_apply [NonAssocSemiring α] (v : V) (vec : V → α) :
    (vec ᵥ* G.adjMatrix α) v = ∑ u ∈ G.neighborFinset v, vec u := by
  simp only [← dotProduct_adjMatrix, vecMul]
  refine congr rfl ?_; ext x
  rw [← transpose_apply (adjMatrix α G) x v, transpose_adjMatrix]

@[simp]
/-
**SimpleGraph.adjMatrix_mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：adjMatrix_mul_apply [NonAssocSemiring α] (M : Matrix V V α) (v w : V) : (G
.adjMatrix α * M) v w = ∑ u in G.neighborFinset v, M u w
参数：M : Matrix V V α；v w : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mul_apply`：mul_apply [Fintype m] [Mul α] [AddCommMonoid α] {M : M
atrix l m α} {N : Matrix m n α} {i k} : (M * N) i k = ∑ j, M i j * N j k
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `SimpleGraph.neighborFinset_eq_filter`：neighborFinset_eq_filter {v : V} [
DecidableRel G.Adj] : G.neighborFinset v = ({w | G.Adj v w} : Finset _)
· 使用定理 `Finset.sum_filter`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst 
: AddCommMonoid M] (p : ι → Prop) [inst_1 : DecidablePred p]   (f : ι → M), ∑ a 
∈ s wit…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem adjMatrix_mul_apply [NonAssocSemiring α] (M : Matrix V V α) (v w : V) :
    (G.adjMatrix α * M) v w = ∑ u ∈ G.neighborFinset v, M u w := by
  simp [mul_apply, neighborFinset_eq_filter, sum_filter]

@[simp]
/-
**SimpleGraph.mul_adjMatrix_apply** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：mul_adjMatrix_apply [NonAssocSemiring α] (M : Matrix V V α) (v w : V) : (M
 * G.adjMatrix α) v w = ∑ u in G.neighborFinset w, M v u
参数：M : Matrix V V α；v w : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mul_apply`：mul_apply [Fintype m] [Mul α] [AddCommMonoid α] {M : M
atrix l m α} {N : Matrix m n α} {i k} : (M * N) i k = ∑ j, M i j * N j k
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `SimpleGraph.neighborFinset_eq_filter`：neighborFinset_eq_filter {v : V} [
DecidableRel G.Adj] : G.neighborFinset v = ({w | G.Adj v w} : Finset _)
· 使用定理 `Finset.sum_filter`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst 
: AddCommMonoid M] (p : ι → Prop) [inst_1 : DecidablePred p]   (f : ι → M), ∑ a 
∈ s wit…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_adjMatrix_apply [NonAssocSemiring α] (M : Matrix V V α) (v w : V) :
    (M * G.adjMatrix α) v w = ∑ u ∈ G.neighborFinset w, M v u := by
  simp [mul_apply, neighborFinset_eq_filter, sum_filter, adj_comm]

variable (α) in
@[simp]
/-
**SimpleGraph.trace_adjMatrix** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：trace_adjMatrix [AddCommMonoid α] [One α] : Matrix.trace (G.adjMatrix α) =
 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trace_adjMatrix [AddCommMonoid α] [One α] : Matrix.trace (G.adjMatrix α) = 0 := by
  simp [Matrix.trace]
/-
**SimpleGraph.adjMatrix_mul_self_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph`。
形式化陈述：adjMatrix_mul_self_apply_self [NonAssocSemiring α] (i : V) : (G.adjMatrix 
α * G.adjMatrix α) i i = degree G i
参数：i : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.mul_adjMatrix_apply`：mul_adjMatrix_apply [NonAssocSemiring α
] (M : Matrix V V α) (v w : V) : (M * G.adjMatrix α) v w = ∑ u in G.neighborFins
et w, M v u
· 使用定理 `Finset.sum_boole`：∀ {ι : Type u_1} {R : Type u_4} [inst : AddCommMonoidW
ithOne R] (p : ι → Prop) [inst_1 : DecidablePred p]   (s : Finset ι), (∑ x ∈ s, 
if p x…
· 使用定理 `Finset.filter_true_of_mem`：∀ {α : Type u_1} {p : α → Prop} [inst : Decid
ablePred p] {s : Finset α}, (∀ x ∈ s, p x) → Finset.filter p s = s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem adjMatrix_mul_self_apply_self [NonAssocSemiring α] (i : V) :
    (G.adjMatrix α * G.adjMatrix α) i i = degree G i := by simp [filter_true_of_mem]

variable (R) in
/-- The number of all darts in a simple finite graph is equal to the dot product of
`G.adjMatrix α *ᵥ 1` and `1`. -/
/-
**SimpleGraph.natCast_card_dart_eq_dotProduct** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph`。
形式化陈述：natCast_card_dart_eq_dotProduct [NonAssocSemiring α] : (Fintype.card G.Dar
t : α) = adjMatrix α G *ᵥ 1 ⬝ᵥ 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.dart_card_eq_sum_degrees`：dart_card_eq_sum_degrees : Fintype
.card G.Dart = ∑ v, G.degree v
· 使用引理 `Nat.cast_sum`：cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι ->
 Nat) : ↑(∑ x in s, f x : Nat) = ∑ x in s, (f x : R)
· 使用定理 `dotProduct_one`：dotProduct_one (v : n -> α) : v ⬝ᵥ 1 = ∑ i, v i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `SimpleGraph.adjMatrix_mulVec_apply`：adjMatrix_mulVec_apply [NonAssocSemi
ring α] (v : V) (vec : V -> α) : (G.adjMatrix α *ᵥ vec) v = ∑ u in G.neighborFin
set v, vec u
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The number of all darts in a simple finite graph is equal to the dot product of
`G.adjMatrix α *ᵥ 1` and `1`.
-/
theorem natCast_card_dart_eq_dotProduct [NonAssocSemiring α] :
    (Fintype.card G.Dart : α) = adjMatrix α G *ᵥ 1 ⬝ᵥ 1 := by
  simp [G.dart_card_eq_sum_degrees, dotProduct_one]

variable {G}
/-
**SimpleGraph.adjMatrix_mulVec_const_apply** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
形式化陈述：adjMatrix_mulVec_const_apply [NonAssocSemiring α] {a : α} {v : V} : (G.adj
Matrix α *ᵥ Function.const _ a) v = G.degree v * a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.adjMatrix_mulVec_apply`：adjMatrix_mulVec_apply [NonAssocSemi
ring α] (v : V) (vec : V -> α) : (G.adjMatrix α *ᵥ vec) v = ∑ u in G.neighborFin
set v, vec u
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem adjMatrix_mulVec_const_apply [NonAssocSemiring α] {a : α} {v : V} :
    (G.adjMatrix α *ᵥ Function.const _ a) v = G.degree v * a := by simp
/-
**SimpleGraph.adjMatrix_mulVec_const_apply_of_regular** 是 Mathlib 中的一个定理，位于命名空间 
`SimpleGraph`。
形式化陈述：adjMatrix_mulVec_const_apply_of_regular [NonAssocSemiring α] {d : Nat} {a 
: α} (hd : G.IsRegularOfDegree d) {v : V} : (G.adjMatrix α *ᵥ Function.const _ a
) v = d * a
参数：hd : G.IsRegularOfDegree d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.adjMatrix_mulVec_apply`：adjMatrix_mulVec_apply [NonAssocSemi
ring α] (v : V) (vec : V -> α) : (G.adjMatrix α *ᵥ vec) v = ∑ u in G.neighborFin
set v, vec u
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem adjMatrix_mulVec_const_apply_of_regular [NonAssocSemiring α] {d : ℕ} {a : α}
    (hd : G.IsRegularOfDegree d) {v : V} : (G.adjMatrix α *ᵥ Function.const _ a) v = d * a := by
  simp [hd v]
/-
**SimpleGraph.adjMatrix_pow_apply_eq_card_walk** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph`。
形式化陈述：adjMatrix_pow_apply_eq_card_walk [DecidableEq V] [Semiring α] (n : Nat) (u
 v : V) : (G.adjMatrix α ^ n) u v = Fintype.card { p : G.Walk u v | p.length = n
 }
参数：n : Nat；u v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.card_set_walk_length_eq`：card_set_walk_length_eq (u v : V) (
n : Nat) : Fintype.card {p : G.Walk u v | p.length = n} = #(G.finsetWalkLength n
 u v)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Matrix.one_apply_eq`：one_apply_eq (i) : (1 : Matrix n n α) i i = 1
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Matrix.one_apply_ne`：one_apply_ne {i j} : i != j -> (1 : Matrix n n α) i
 j = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `SimpleGraph.adjMatrix_mul_apply`：adjMatrix_mul_apply [NonAssocSemiring α
] (M : Matrix V V α) (v w : V) : (G.adjMatrix α * M) v w = ∑ u in G.neighborFins
et v, M u w
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.card_biUnion`：card_biUnion [DecidableEq M] {t : ι -> Finset M} (h
 : (s : Set ι).PairwiseDisjoint t) : #(s.biUnion t) = ∑ u in s, #(t u)
· 使用定理 `Function.onFun.eq_1`：∀ {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} (f : β 
→ β → φ) (g : α → β) (x y : α),   Function.onFun f g x y = f (g x) (g y)
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `Nat.cast_sum`：cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι ->
 Nat) : ↑(∑ x in s, f x : Nat) = ∑ x in s, (f x : R)
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
（共 31 条，此处仅展示前 30 条）
-/
theorem adjMatrix_pow_apply_eq_card_walk [DecidableEq V] [Semiring α] (n : ℕ) (u v : V) :
    (G.adjMatrix α ^ n) u v = Fintype.card { p : G.Walk u v | p.length = n } := by
  rw [card_set_walk_length_eq]
  induction n generalizing u v with
  | zero => obtain rfl | h := eq_or_ne u v <;> simp [finsetWalkLength, *]
  | succ n ih =>
    simp only [pow_succ', finsetWalkLength, ih, adjMatrix_mul_apply]
    rw [Finset.card_biUnion]
    · norm_cast
      simp only [Nat.cast_sum, card_map, neighborFinset_def]
      apply Finset.sum_toFinset_eq_subtype
    -- Disjointness for card_bUnion
    · rintro ⟨x, hx⟩ - ⟨y, hy⟩ - hxy
      rw [Function.onFun, disjoint_iff_inf_le]
      intro p hp
      simp only [inf_eq_inter, mem_inter, mem_map] at hp
      obtain ⟨⟨px, _, rfl⟩, ⟨py, hpy, hp⟩⟩ := hp
      cases hp
      simp at hxy
/-
**SimpleGraph.dotProduct_mulVec_adjMatrix** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
`。
形式化陈述：dotProduct_mulVec_adjMatrix [NonAssocSemiring α] (x y : V -> α) : x ⬝ᵥ G.a
djMatrix α *ᵥ y = ∑ i : V, ∑ j : V, if G.Adj i j then x i * y j else 0
参数：x y : V -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dotProduct_mulVec_adjMatrix [NonAssocSemiring α] (x y : V → α) :
    x ⬝ᵥ G.adjMatrix α *ᵥ y = ∑ i : V, ∑ j : V, if G.Adj i j then x i * y j else 0 := by
  simp [dotProduct, mulVec, mul_sum]

end fintype

section hadamard
variable (α) [DecidableEq V] [MulZeroOneClass α]

open Matrix

/-
**SimpleGraph.adjMatrix_hadamard_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
`。
形式化陈述：∀ (α : Type u_1) {V : Type u_2} (G : SimpleGraph V) [inst : DecidableRel G
.Adj] [inst_1 : DecidableEq V]   [inst_2 : MulZeroOneClass α] (d : V → α), (Simp
leGraph.adjMatrix α G).hadamard (Matrix.diagonal d) = 0
参数：α : Type u_1；G : SimpleGraph V；d : V → α；SimpleGraph.adjMatrix α G；Matrix.dia
gonal d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.hadamard_diagonal`：hadamard_diagonal (M) (w : n -> α) : M ⊙ diago
nal w = diagonal (M.diag * w)
· 使用定理 `Matrix.IsAdjMatrix.diag_eq_zero`：diag_eq_zero [Zero α] [One α] (h : IsAd
jMatrix A) : A.diag = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Matrix.diagonal_zero'`：diagonal_zero' [Zero α] : (diagonal 0 : Matrix n 
n α) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem adjMatrix_hadamard_diagonal (d : V → α) :
    G.adjMatrix α ⊙ diagonal d = 0 := by simp [hadamard_diagonal]
/-
**SimpleGraph.diagonal_hadamard_adjMatrix** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
`。
形式化陈述：∀ (α : Type u_1) {V : Type u_2} (G : SimpleGraph V) [inst : DecidableRel G
.Adj] [inst_1 : DecidableEq V]   [inst_2 : MulZeroOneClass α] (d : V → α), (Matr
ix.diagonal d).hadamard (SimpleGraph.adjMatrix α G) = 0
参数：α : Type u_1；G : SimpleGraph V；d : V → α；Matrix.diagonal d；SimpleGraph.adjMat
rix α G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.diagonal_hadamard`：diagonal_hadamard (M) (w : n -> α) : diagonal 
w ⊙ M = diagonal (w * M.diag)
· 使用定理 `Matrix.IsAdjMatrix.diag_eq_zero`：diag_eq_zero [Zero α] [One α] (h : IsAd
jMatrix A) : A.diag = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Matrix.diagonal_zero'`：diagonal_zero' [Zero α] : (diagonal 0 : Matrix n 
n α) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem diagonal_hadamard_adjMatrix (d : V → α) :
    diagonal d ⊙ G.adjMatrix α = 0 := by simp [diagonal_hadamard]
/-
**SimpleGraph.adjMatrix_hadamard_natCast** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`
。
形式化陈述：∀ (α : Type u_1) {V : Type u_2} (G : SimpleGraph V) [inst : DecidableRel G
.Adj] [inst_1 : DecidableEq V]   [inst_2 : MulZeroOneClass α] [inst_3 : NatCast 
α] (a : ℕ), (SimpleGraph.adjMatrix α G).hadamard ↑a = 0
参数：α : Type u_1；G : SimpleGraph V；a : ℕ；SimpleGraph.adjMatrix α G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.adjMatrix_hadamard_diagonal`：∀ (α : Type u_1) {V : Type u_2}
 (G : SimpleGraph V) [inst : DecidableRel G.Adj] [inst_1 : DecidableEq V]   [ins
t_2 : MulZeroOneClass α] (d :…
-/
@[simp] theorem adjMatrix_hadamard_natCast [NatCast α] (a : ℕ) :
    G.adjMatrix α ⊙ a.cast = 0 := adjMatrix_hadamard_diagonal _ _ _
/-
**SimpleGraph.natCast_hadamard_adjMatrix** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`
。
形式化陈述：∀ (α : Type u_1) {V : Type u_2} (G : SimpleGraph V) [inst : DecidableRel G
.Adj] [inst_1 : DecidableEq V]   [inst_2 : MulZeroOneClass α] [inst_3 : NatCast 
α] (a : ℕ), (↑a).hadamard (SimpleGraph.adjMatrix α G) = 0
参数：α : Type u_1；G : SimpleGraph V；a : ℕ；↑a；SimpleGraph.adjMatrix α G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.diagonal_hadamard_adjMatrix`：∀ (α : Type u_1) {V : Type u_2}
 (G : SimpleGraph V) [inst : DecidableRel G.Adj] [inst_1 : DecidableEq V]   [ins
t_2 : MulZeroOneClass α] (d :…
-/
@[simp] theorem natCast_hadamard_adjMatrix [NatCast α] (a : ℕ) :
    a.cast ⊙ G.adjMatrix α = 0 := diagonal_hadamard_adjMatrix _ _ _
/-
**SimpleGraph.adjMatrix_hadamard_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ (α : Type u_1) {V : Type u_2} (G : SimpleGraph V) [inst : DecidableRel G
.Adj] [inst_1 : DecidableEq V]   [inst_2 : MulZeroOneClass α] [inst_3 : NatCast 
α] (a : ℕ) [inst_4 : a.AtLeastTwo],   (SimpleGraph.adjMatrix α G).hadamard (OfNa
t.ofNat a) = 0
参数：α : Type u_1；G : SimpleGraph V；a : ℕ；SimpleGraph.adjMatrix α G；OfNat.ofNat a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.adjMatrix_hadamard_diagonal`：∀ (α : Type u_1) {V : Type u_2}
 (G : SimpleGraph V) [inst : DecidableRel G.Adj] [inst_1 : DecidableEq V]   [ins
t_2 : MulZeroOneClass α] (d :…
-/
@[simp] theorem adjMatrix_hadamard_ofNat [NatCast α] (a : ℕ) [a.AtLeastTwo] :
    G.adjMatrix α ⊙ ofNat(a) = 0 := adjMatrix_hadamard_diagonal _ _ _
/-
**SimpleGraph.ofNat_hadamard_adjMatrix** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ (α : Type u_1) {V : Type u_2} (G : SimpleGraph V) [inst : DecidableRel G
.Adj] [inst_1 : DecidableEq V]   [inst_2 : MulZeroOneClass α] [inst_3 : NatCast 
α] (a : ℕ) [inst_4 : a.AtLeastTwo],   (OfNat.ofNat a).hadamard (SimpleGraph.adjM
atrix α G) = 0
参数：α : Type u_1；G : SimpleGraph V；a : ℕ；OfNat.ofNat a；SimpleGraph.adjMatrix α G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.diagonal_hadamard_adjMatrix`：∀ (α : Type u_1) {V : Type u_2}
 (G : SimpleGraph V) [inst : DecidableRel G.Adj] [inst_1 : DecidableEq V]   [ins
t_2 : MulZeroOneClass α] (d :…
-/
@[simp] theorem ofNat_hadamard_adjMatrix [NatCast α] (a : ℕ) [a.AtLeastTwo] :
    ofNat(a) ⊙ G.adjMatrix α = 0 := diagonal_hadamard_adjMatrix _ _ _
/-
**SimpleGraph.adjMatrix_hadamard_intCast** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`
。
形式化陈述：∀ (α : Type u_1) {V : Type u_2} (G : SimpleGraph V) [inst : DecidableRel G
.Adj] [inst_1 : DecidableEq V]   [inst_2 : MulZeroOneClass α] [inst_3 : IntCast 
α] (a : ℤ), (SimpleGraph.adjMatrix α G).hadamard ↑a = 0
参数：α : Type u_1；G : SimpleGraph V；a : ℤ；SimpleGraph.adjMatrix α G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.adjMatrix_hadamard_diagonal`：∀ (α : Type u_1) {V : Type u_2}
 (G : SimpleGraph V) [inst : DecidableRel G.Adj] [inst_1 : DecidableEq V]   [ins
t_2 : MulZeroOneClass α] (d :…
-/
@[simp] theorem adjMatrix_hadamard_intCast [IntCast α] (a : ℤ) :
    G.adjMatrix α ⊙ a.cast = 0 := adjMatrix_hadamard_diagonal _ _ _
/-
**SimpleGraph.intCast_hadamard_adjMatrix** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`
。
形式化陈述：∀ (α : Type u_1) {V : Type u_2} (G : SimpleGraph V) [inst : DecidableRel G
.Adj] [inst_1 : DecidableEq V]   [inst_2 : MulZeroOneClass α] [inst_3 : IntCast 
α] (a : ℤ), (↑a).hadamard (SimpleGraph.adjMatrix α G) = 0
参数：α : Type u_1；G : SimpleGraph V；a : ℤ；↑a；SimpleGraph.adjMatrix α G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.diagonal_hadamard_adjMatrix`：∀ (α : Type u_1) {V : Type u_2}
 (G : SimpleGraph V) [inst : DecidableRel G.Adj] [inst_1 : DecidableEq V]   [ins
t_2 : MulZeroOneClass α] (d :…
-/
@[simp] theorem intCast_hadamard_adjMatrix [IntCast α] (a : ℤ) :
    a.cast ⊙ G.adjMatrix α = 0 := diagonal_hadamard_adjMatrix _ _ _
/-
**SimpleGraph.adjMatrix_hadamard_one** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ (α : Type u_1) {V : Type u_2} (G : SimpleGraph V) [inst : DecidableRel G
.Adj] [inst_1 : DecidableEq V]   [inst_2 : MulZeroOneClass α], (SimpleGraph.adjM
atrix α G).hadamard 1 = 0
参数：α : Type u_1；G : SimpleGraph V；SimpleGraph.adjMatrix α G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.adjMatrix_hadamard_diagonal`：∀ (α : Type u_1) {V : Type u_2}
 (G : SimpleGraph V) [inst : DecidableRel G.Adj] [inst_1 : DecidableEq V]   [ins
t_2 : MulZeroOneClass α] (d :…
-/
@[simp] theorem adjMatrix_hadamard_one :
    G.adjMatrix α ⊙ 1 = 0 := adjMatrix_hadamard_diagonal _ _ _
/-
**SimpleGraph.one_hadamard_adjMatrix** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ (α : Type u_1) {V : Type u_2} (G : SimpleGraph V) [inst : DecidableRel G
.Adj] [inst_1 : DecidableEq V]   [inst_2 : MulZeroOneClass α], Matrix.hadamard 1
 (SimpleGraph.adjMatrix α G) = 0
参数：α : Type u_1；G : SimpleGraph V；SimpleGraph.adjMatrix α G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.diagonal_hadamard_adjMatrix`：∀ (α : Type u_1) {V : Type u_2}
 (G : SimpleGraph V) [inst : DecidableRel G.Adj] [inst_1 : DecidableEq V]   [ins
t_2 : MulZeroOneClass α] (d :…
-/
@[simp] theorem one_hadamard_adjMatrix :
    1 ⊙ G.adjMatrix α = 0 := diagonal_hadamard_adjMatrix _ _ _

end hadamard

end SimpleGraph

namespace Matrix.IsAdjMatrix

variable [MulZeroOneClass α] [Nontrivial α]
variable {A : Matrix V V α} (h : IsAdjMatrix A)

/-- If `A` is qualified as an adjacency matrix,
then the adjacency matrix of the graph induced by `A` is itself. -/
/-
**Matrix.IsAdjMatrix.adjMatrix_toGraph_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsAd
jMatrix`。
形式化陈述：adjMatrix_toGraph_eq [DecidableEq α] : h.toGraph.adjMatrix α = A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Matrix.IsAdjMatrix.zero_or_one`：∀ {α : Type u_1} {V : Type u_2} [inst : 
Zero α] [inst_1 : One α] {A : Matrix V V α},   A.IsAdjMatrix → ∀ (i j : V), A i 
j = 0 ∨ A i j = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Matrix.IsAdjMatrix.toGraph_adj`：∀ {α : Type u_1} {V : Type u_2} {A : Mat
rix V V α} [inst : MulZeroOneClass α] [inst_1 : Nontrivial α]   (h : A.IsAdjMatr
ix) (i j : V), h.toG…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a

--- 原说明 ---
If `A` is qualified as an adjacency matrix,
then the adjacency matrix of the graph induced by `A` is itself.
-/
theorem adjMatrix_toGraph_eq [DecidableEq α] : h.toGraph.adjMatrix α = A := by
  ext i j
  obtain h' | h' := h.zero_or_one i j <;> simp [h']

end Matrix.IsAdjMatrix

