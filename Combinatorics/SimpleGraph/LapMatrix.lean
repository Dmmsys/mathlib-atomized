/-
Copyright (c) 2023 Adrian Wüthrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Wüthrich
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Laplacian Matrix

This module defines the Laplacian matrix of a graph, and proves some of its elementary properties.

## Main definitions & Results

* `SimpleGraph.degMatrix`: The degree matrix of a simple graph
* `SimpleGraph.lapMatrix`: The Laplacian matrix of a simple graph, defined as the difference
  between the degree matrix and the adjacency matrix.
* `posSemidef_lapMatrix`: The Laplacian matrix is positive semidefinite.
* `card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix`:
  The number of connected components in a graph
  is the dimension of the nullspace of its Laplacian matrix.

-/

@[expose] public section

open Finset Matrix Module

namespace Matrix.IsAdjMatrix

variable {α V : Type*} [NonAssocSemiring α] [StarRing α] {A : Matrix V V α} (h : A.IsAdjMatrix)
include h

@[simp]
/-
**Matrix.IsAdjMatrix.isHermitian** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsAdjMatrix`。
形式化陈述：∀ {α : Type u_1} {V : Type u_2} [inst : NonAssocSemiring α] [inst_1 : Star
Ring α] {A : Matrix V V α},   A.IsAdjMatrix → A.IsHermitian
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
· 使用定理 `Matrix.IsSymm.apply`：∀ {α : Type u_1} {n : Type u_3} {A : Matrix n n α},
 A.IsSymm → ∀ (i j : n), A j i = A i j
· 使用定理 `Matrix.IsAdjMatrix.symm`：∀ {α : Type u_1} {V : Type u_2} [inst : Zero α]
 [inst_1 : One α] {A : Matrix V V α}, A.IsAdjMatrix → A.IsSymm
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `star_one`：star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1
-/
protected theorem isHermitian : A.IsHermitian := by
  ext i j
  rcases h.zero_or_one i j with heq | heq
    <;> simp [heq, h.symm.apply]

end Matrix.IsAdjMatrix

namespace SimpleGraph

variable {V : Type*} (R : Type*)
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] in
/-
**SimpleGraph.isHermitian_adjMatrix** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isHermitian_adjMatrix [NonAssocSemiring R] [StarRing R] : (G.adjMatrix R).
IsHermitian
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsAdjMatrix.isHermitian`：∀ {α : Type u_1} {V : Type u_2} [inst : 
NonAssocSemiring α] [inst_1 : StarRing α] {A : Matrix V V α},   A.IsAdjMatrix → 
A.IsHermitian
· 使用定理 `SimpleGraph.isAdjMatrix_adjMatrix`：isAdjMatrix_adjMatrix [Zero α] [One α
] : (G.adjMatrix α).IsAdjMatrix where zero_or_one
-/
theorem isHermitian_adjMatrix [NonAssocSemiring R] [StarRing R] : (G.adjMatrix R).IsHermitian :=
  G.isAdjMatrix_adjMatrix R |>.isHermitian
/-
**SimpleGraph.degree_eq_sum_if_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：degree_eq_sum_if_adj {R : Type*} [AddCommMonoidWithOne R] (i : V) : (G.deg
ree i : R) = ∑ j : V, if G.Adj i j then 1 else 0
参数：i : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_boole`：∀ {ι : Type u_1} {R : Type u_4} [inst : AddCommMonoidW
ithOne R] (p : ι → Prop) [inst_1 : DecidablePred p]   (s : Finset ι), (∑ x ∈ s, 
if p x…
· 使用定理 `Set.toFinset_ofPred`：toFinset_ofPred [Fintype α] (p : α -> Prop) [Decida
blePred p] [Fintype { x | p x }] : Set.toFinset {x | p x} = Finset.univ.filter p
-/
theorem degree_eq_sum_if_adj {R : Type*} [AddCommMonoidWithOne R] (i : V) :
    (G.degree i : R) = ∑ j : V, if G.Adj i j then 1 else 0 := by
  unfold degree neighborFinset neighborSet
  rw [sum_boole, Set.toFinset_ofPred]

variable [DecidableEq V]

/-- The diagonal matrix consisting of the degrees of the vertices in the graph. -/
/-
**SimpleGraph.degMatrix** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：degMatrix [AddMonoidWithOne R] : Matrix V V R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagonal matrix consisting of the degrees of the vertices in the graph.
-/
def degMatrix [AddMonoidWithOne R] : Matrix V V R := Matrix.diagonal (G.degree ·)

/-- The *Laplacian matrix* `lapMatrix G R` of a graph `G`
is the matrix `L = D - A` where `D` is the degree and `A` the adjacency matrix of `G`. -/
/-
**SimpleGraph.lapMatrix** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：lapMatrix [AddGroupWithOne R] : Matrix V V R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The *Laplacian matrix* `lapMatrix G R` of a graph `G`
is the matrix `L = D - A` where `D` is the degree and `A` the adjacency matrix o
f `G`.
-/
def lapMatrix [AddGroupWithOne R] : Matrix V V R := G.degMatrix R - G.adjMatrix R
/-
**SimpleGraph.isSymm_degMatrix** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isSymm_degMatrix [AddMonoidWithOne R] : (G.degMatrix R).IsSymm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.isSymm_diagonal`：isSymm_diagonal [DecidableEq n] [Zero α] (v : n 
-> α) : (diagonal v).IsSymm
-/
theorem isSymm_degMatrix [AddMonoidWithOne R] : (G.degMatrix R).IsSymm :=
  isSymm_diagonal _
/-
**SimpleGraph.isHermitian_degMatrix** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isHermitian_degMatrix [NonAssocSemiring R] [StarRing R] : (G.degMatrix R).
IsHermitian
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Matrix.isHermitian_diagonal_iff`：isHermitian_diagonal_iff [DecidableEq n
] {d : n -> α} : IsHermitian (diagonal d) ↔ (forall i : n, IsSelfAdjoint (d i))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem isHermitian_degMatrix [NonAssocSemiring R] [StarRing R] : (G.degMatrix R).IsHermitian :=
  Matrix.isHermitian_diagonal_iff.mpr <| by simp
/-
**SimpleGraph.isSymm_lapMatrix** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isSymm_lapMatrix [AddGroupWithOne R] : (G.lapMatrix R).IsSymm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsSymm.sub`：∀ {α : Type u_1} {n : Type u_3} {A B : Matrix n n α} 
[inst : Sub α], A.IsSymm → B.IsSymm → (A - B).IsSymm
· 使用定理 `SimpleGraph.isSymm_degMatrix`：isSymm_degMatrix [AddMonoidWithOne R] : (G
.degMatrix R).IsSymm
· 使用定理 `SimpleGraph.isSymm_adjMatrix`：isSymm_adjMatrix [Zero α] [One α] : (G.adj
Matrix α).IsSymm
-/
theorem isSymm_lapMatrix [AddGroupWithOne R] : (G.lapMatrix R).IsSymm :=
  G.isSymm_degMatrix R |>.sub G.isSymm_adjMatrix
/-
**SimpleGraph.isHermitian_lapMatrix** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isHermitian_lapMatrix [NonAssocRing R] [StarRing R] : (G.lapMatrix R).IsHe
rmitian
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsHermitian.sub`：∀ {α : Type u_1} {n : Type u_4} [inst : AddGroup
 α] [inst_1 : StarAddMonoid α] {A B : Matrix n n α},   A.IsHermitian → B.IsHermi
tian → (A - …
· 使用定理 `SimpleGraph.isHermitian_degMatrix`：isHermitian_degMatrix [NonAssocSemiri
ng R] [StarRing R] : (G.degMatrix R).IsHermitian
· 使用定理 `SimpleGraph.isHermitian_adjMatrix`：isHermitian_adjMatrix [NonAssocSemiri
ng R] [StarRing R] : (G.adjMatrix R).IsHermitian
-/
theorem isHermitian_lapMatrix [NonAssocRing R] [StarRing R] : (G.lapMatrix R).IsHermitian :=
  G.isHermitian_degMatrix R |>.sub <| G.isHermitian_adjMatrix R

variable {R}
/-
**SimpleGraph.degMatrix_mulVec_apply** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：degMatrix_mulVec_apply [NonAssocSemiring R] (v : V) (vec : V -> R) : (G.de
gMatrix R *ᵥ vec) v = G.degree v * vec v
参数：v : V；vec : V -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.degMatrix.eq_1`：∀ {V : Type u_1} (R : Type u_2) [inst : Fint
ype V] (G : SimpleGraph V) [inst_1 : DecidableRel G.Adj]   [inst_2 : DecidableEq
 V] [inst_3 : Ad…
· 使用定理 `Matrix.mulVec_diagonal`：mulVec_diagonal [Fintype m] [DecidableEq m] (v w
 : m -> α) (x : m) : (diagonal v *ᵥ w) x = v x * w x
-/
theorem degMatrix_mulVec_apply [NonAssocSemiring R] (v : V) (vec : V → R) :
    (G.degMatrix R *ᵥ vec) v = G.degree v * vec v := by
  rw [degMatrix, mulVec_diagonal]
/-
**SimpleGraph.lapMatrix_mulVec_apply** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：lapMatrix_mulVec_apply [NonAssocRing R] (v : V) (vec : V -> R) : (G.lapMat
rix R *ᵥ vec) v = G.degree v * vec v - ∑ u in G.neighborFinset v, vec u
参数：v : V；vec : V -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.sub_mulVec`：sub_mulVec [Fintype n] (A B : Matrix m n α) (x : n ->
 α) : (A - B) *ᵥ x = A *ᵥ x - B *ᵥ x
· 使用定理 `SimpleGraph.degMatrix_mulVec_apply`：degMatrix_mulVec_apply [NonAssocSemi
ring R] (v : V) (vec : V -> R) : (G.degMatrix R *ᵥ vec) v = G.degree v * vec v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.adjMatrix_mulVec_apply`：adjMatrix_mulVec_apply [NonAssocSemi
ring α] (v : V) (vec : V -> α) : (G.adjMatrix α *ᵥ vec) v = ∑ u in G.neighborFin
set v, vec u
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lapMatrix_mulVec_apply [NonAssocRing R] (v : V) (vec : V → R) :
    (G.lapMatrix R *ᵥ vec) v = G.degree v * vec v - ∑ u ∈ G.neighborFinset v, vec u := by
  simp_rw [lapMatrix, sub_mulVec, Pi.sub_apply, degMatrix_mulVec_apply, adjMatrix_mulVec_apply]
/-
**SimpleGraph.lapMatrix_mulVec_const_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph`。
形式化陈述：lapMatrix_mulVec_const_eq_zero [NonAssocRing R] : mulVec (G.lapMatrix R) (
fun _ => 1) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.lapMatrix_mulVec_apply`：lapMatrix_mulVec_apply [NonAssocRing
 R] (v : V) (vec : V -> R) : (G.lapMatrix R *ᵥ vec) v = G.degree v * vec v - ∑ u
 in G.neighborFinset v, …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lapMatrix_mulVec_const_eq_zero [NonAssocRing R] :
    mulVec (G.lapMatrix R) (fun _ ↦ 1) = 0 := by
  ext1 i
  rw [lapMatrix_mulVec_apply]
  simp
/-
**SimpleGraph.dotProduct_mulVec_degMatrix** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
`。
形式化陈述：dotProduct_mulVec_degMatrix [CommSemiring R] (x : V -> R) : x ⬝ᵥ (G.degMat
rix R *ᵥ x) = ∑ i : V, G.degree i * x i * x i
参数：x : V -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Matrix.mulVec_diagonal`：mulVec_diagonal [Fintype m] [DecidableEq m] (v w
 : m -> α) (x : m) : (diagonal v *ᵥ w) x = v x * w x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dotProduct_mulVec_degMatrix [CommSemiring R] (x : V → R) :
    x ⬝ᵥ (G.degMatrix R *ᵥ x) = ∑ i : V, G.degree i * x i * x i := by
  simp only [dotProduct, degMatrix, mulVec_diagonal, ← mul_assoc, mul_comm]

variable (R)

/-- Let $L$ be the graph Laplacian and let $x \in \mathbb{R}$, then
$$x^{\top} L x = \sum_{i \sim j} (x_{i}-x_{j})^{2}$$,
where $\sim$ denotes the adjacency relation -/
/-
**SimpleGraph.lapMatrix_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let $L$ be the graph Laplacian and let $x \in \mathbb{R}$, then
$$x^{\top} L x = \sum_{i \sim j} (x_{i}-x_{j})^{2}$$,
where $\sim$ denotes the adjacency relation
-/
theorem lapMatrix_toLinearMap₂' [Field R] [CharZero R] (x : V → R) :
    toLinearMap₂' R (G.lapMatrix R) x x =
    (∑ i : V, ∑ j : V, if G.Adj i j then (x i - x j) ^ 2 else 0) / 2 := by
  simp_rw [toLinearMap₂'_apply', lapMatrix, sub_mulVec, dotProduct_sub, dotProduct_mulVec_degMatrix,
    dotProduct_mulVec_adjMatrix, ← sum_sub_distrib, degree_eq_sum_if_adj, sum_mul, ite_mul, one_mul,
    zero_mul, ← sum_sub_distrib, ite_sub_ite, sub_zero]
  rw [← add_self_div_two (∑ x_1 : V, ∑ x_2 : V, _)]
  conv_lhs => enter [1, 2, 2, i, 2, j]; rw [if_congr (adj_comm G i j) rfl rfl]
  conv_lhs => enter [1, 2]; rw [Finset.sum_comm]
  simp_rw [← sum_add_distrib, ite_add_ite]
  congr 2 with i
  congr 2 with j
  ring_nf

/-- The Laplacian matrix is positive semidefinite -/
/-
**SimpleGraph.posSemidef_lapMatrix** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：posSemidef_lapMatrix [Field R] [LinearOrder R] [IsStrictOrderedRing R] [St
arRing R] [TrivialStar R] : PosSemidef (G.lapMatrix R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg`：of_dotProduct_mulVec_nonn
eg {M : Matrix n n R} (hM1 : M.IsHermitian) (hM2 : forall x, 0 <= star x ⬝ᵥ (M *
ᵥ x)) : M.PosSemidef
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsHermitian.eq_1`：∀ {α : Type u_1} {n : Type u_4} [inst : Star α]
 (A : Matrix n n α), A.IsHermitian = (A.conjTranspose = A)
· 使用定理 `Matrix.conjTranspose_eq_transpose_of_trivial`：conjTranspose_eq_transpose
_of_trivial [Star α] [TrivialStar α] (A : Matrix m n α) : Aᴴ = Aᵀ
· 使用定理 `SimpleGraph.isSymm_lapMatrix`：isSymm_lapMatrix [AddGroupWithOne R] : (G.
lapMatrix R).IsSymm
· 使用定理 `TrivialStar.star_trivial`：∀ {R : Type u} {inst : Star R} [self : Trivial
Star R] (r : R), star r = r
· 使用定理 `Pi.instTrivialStarForall`：∀ {I : Type u} {f : I → Type v} [inst : (i : I
) → Star (f i)] [∀ (i : I), TrivialStar (f i)],   TrivialStar ((i : I) → f i)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.toLinearMap₂'_apply'`：∀ {n : Type u_11} {m : Type u_12} [inst : F
intype n] [inst_1 : Fintype m] [inst_2 : DecidableEq n]   [inst_3 : DecidableEq 
m] {T : Type u_16…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SimpleGraph.lapMatrix_toLinearMap₂'`：lapMatrix_toLinearMap₂' [Field R] [
CharZero R] (x : V -> R) : toLinearMap₂' R (G.lapMatrix R) x x = (∑ i : V, ∑ j :
 V, if G.Adj i j then (x …
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_nonneg_of_pos`：div_nonneg_of_nonne
g_of_pos [PosMulReflectLT α] (ha : 0 <= a) (hb : 0 < b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `Mathlib.Meta.Positivity.ite_nonneg`：ite_nonneg [LE α] (ha : 0 <= a) (hb 
: 0 <= b) : 0 <= ite p a b
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用引理 `Mathlib.Meta.Positivity.nonneg_of_isNat`：nonneg_of_isNat {n : Nat} [Semi
ring A] [PartialOrder A] [IsOrderedRing A] (h : NormNum.IsNat e n) : 0 <= (e : A
)
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The Laplacian matrix is positive semidefinite
-/
theorem posSemidef_lapMatrix [Field R] [LinearOrder R] [IsStrictOrderedRing R] [StarRing R]
    [TrivialStar R] : PosSemidef (G.lapMatrix R) := by
  refine .of_dotProduct_mulVec_nonneg ?_ (fun x ↦ ?_)
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, isSymm_lapMatrix]
  · rw [star_trivial, ← toLinearMap₂'_apply', lapMatrix_toLinearMap₂']
    positivity
/-
**SimpleGraph.lapMatrix_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_adj
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] (x : V → R) :
    Matrix.toLinearMap₂' R (G.lapMatrix R) x x = 0 ↔ ∀ i j : V, G.Adj i j → x i = x j := by
  simp (disch := intros; positivity)
    [lapMatrix_toLinearMap₂', sum_eq_zero_iff_of_nonneg, sub_eq_zero]
/-
**SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_adj** 是 Mathlib 中的一个定理，位于命名空间 
`SimpleGraph`。
形式化陈述：lapMatrix_mulVec_eq_zero_iff_forall_adj {x : V -> Real} : G.lapMatrix Real
 *ᵥ x = 0 ↔ forall i j : V, G.Adj i j -> x i = x j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.PosSemidef.toLinearMap₂'_zero_iff`：∀ {𝕜 : Type u_1} {n : Type u_2
} [inst : RCLike 𝕜] [inst_1 : Fintype n] [inst_2 : DecidableEq n] {A : Matrix n 
n 𝕜},   A.PosSemidef → ∀ (x : …
· 使用定理 `SimpleGraph.posSemidef_lapMatrix`：posSemidef_lapMatrix [Field R] [Linear
Order R] [IsStrictOrderedRing R] [StarRing R] [TrivialStar R] : PosSemidef (G.la
pMatrix R)
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `TrivialStar.star_trivial`：∀ {R : Type u} {inst : Star R} [self : Trivial
Star R] (r : R), star r = r
· 使用定理 `Pi.instTrivialStarForall`：∀ {I : Type u} {f : I → Type v} [inst : (i : I
) → Star (f i)] [∀ (i : I), TrivialStar (f i)],   TrivialStar ((i : I) → f i)
· 使用定理 `SimpleGraph.lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_adj`：∀ {V 
: Type u_1} (R : Type u_2) [inst : Fintype V] (G : SimpleGraph V) [inst_1 : Deci
dableRel G.Adj]   [inst_2 : DecidableEq V] [inst_3 : Fi…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lapMatrix_mulVec_eq_zero_iff_forall_adj {x : V → ℝ} :
    G.lapMatrix ℝ *ᵥ x = 0 ↔ ∀ i j : V, G.Adj i j → x i = x j := by
  rw [← (posSemidef_lapMatrix ℝ G).toLinearMap₂'_zero_iff, star_trivial,
      lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_adj]
/-
**SimpleGraph.lapMatrix_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_reachable (x : V → ℝ) :
    Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) x x = 0 ↔
      ∀ i j : V, G.Reachable i j → x i = x j := by
  rw [lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_adj]
  refine ⟨?_, fun h i j hA ↦ h i j hA.reachable⟩
  intro h i j ⟨w⟩
  induction w with
  | nil => rfl
  | cons hA _ h' => exact (h _ _ hA).trans h'
/-
**SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_reachable** 是 Mathlib 中的一个定理，位
于命名空间 `SimpleGraph`。
形式化陈述：lapMatrix_mulVec_eq_zero_iff_forall_reachable {x : V -> Real} : G.lapMatri
x Real *ᵥ x = 0 ↔ forall i j : V, G.Reachable i j -> x i = x j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.PosSemidef.toLinearMap₂'_zero_iff`：∀ {𝕜 : Type u_1} {n : Type u_2
} [inst : RCLike 𝕜] [inst_1 : Fintype n] [inst_2 : DecidableEq n] {A : Matrix n 
n 𝕜},   A.PosSemidef → ∀ (x : …
· 使用定理 `SimpleGraph.posSemidef_lapMatrix`：posSemidef_lapMatrix [Field R] [Linear
Order R] [IsStrictOrderedRing R] [StarRing R] [TrivialStar R] : PosSemidef (G.la
pMatrix R)
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `TrivialStar.star_trivial`：∀ {R : Type u} {inst : Star R} [self : Trivial
Star R] (r : R), star r = r
· 使用定理 `Pi.instTrivialStarForall`：∀ {I : Type u} {f : I → Type v} [inst : (i : I
) → Star (f i)] [∀ (i : I), TrivialStar (f i)],   TrivialStar ((i : I) → f i)
· 使用定理 `SimpleGraph.lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_reachable`
：∀ {V : Type u_1} [inst : Fintype V] (G : SimpleGraph V) [inst_1 : DecidableRel 
G.Adj] [inst_2 : DecidableEq V]   (x : V → ℝ),   (((Matrix.to…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lapMatrix_mulVec_eq_zero_iff_forall_reachable {x : V → ℝ} :
    G.lapMatrix ℝ *ᵥ x = 0 ↔ ∀ i j : V, G.Reachable i j → x i = x j := by
  rw [← (posSemidef_lapMatrix ℝ G).toLinearMap₂'_zero_iff, star_trivial,
      lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_reachable]

@[simp]
/-
**SimpleGraph.det_lapMatrix_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：det_lapMatrix_eq_zero [h : Nonempty V] : (G.lapMatrix Real).det = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.exists_mulVec_eq_zero_iff`：exists_mulVec_eq_zero_iff [DecidableEq
 n] : (exists v != 0, M *ᵥ v = 0) ↔ M.det = 0
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `Function.support_nonempty_iff`：∀ {ι : Type u_1} {M : Type u_3} [inst : Z
ero M] {f : ι → M}, (Function.support f).Nonempty ↔ f ≠ 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_adj`：lapMatrix_mulVec_eq
_zero_iff_forall_adj {x : V -> Real} : G.lapMatrix Real *ᵥ x = 0 ↔ forall i j : 
V, G.Adj i j -> x i = x j
-/
theorem det_lapMatrix_eq_zero [h : Nonempty V] : (G.lapMatrix ℝ).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  use fun _ ↦ 1
  refine ⟨?_, (lapMatrix_mulVec_eq_zero_iff_forall_adj G).mpr fun _ _ _ ↦ rfl⟩
  rw [← Function.support_nonempty_iff]
  use Classical.choice h
  simp

section

variable [DecidableEq G.ConnectedComponent]

/-
**SimpleGraph.mem_ker_toLin'_lapMatrix_of_connectedComponent** 是 Mathlib 中的一个定理，
位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] {G : SimpleGr
aph V} [inst_2 : DecidableRel G.Adj]   [inst_3 : DecidableEq G.ConnectedComponen
t] (c : G.ConnectedComponent),   (fun i => if G.connectedComponentMk i = c then 
1 else 0) ∈ (Matrix.toLin' (SimpleGraph.lapMatrix ℝ G)).ker
参数：c : G.ConnectedComponent；fun i => if G.connectedComponentMk i = c then 1 else
 0；Matrix.toLin' (SimpleGraph.lapMatrix ℝ G)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `Matrix.toLin'_apply`：∀ {R : Type u_1} [inst : CommSemiring R] {m : Type 
u_4} {n : Type u_5} [inst_1 : DecidableEq n] [inst_2 : Fintype n]   (M : Matrix 
m n R) (v…
· 使用定理 `SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_reachable`：lapMatrix_mul
Vec_eq_zero_iff_forall_reachable {x : V -> Real} : G.lapMatrix Real *ᵥ x = 0 ↔ f
orall i j : V, G.Reachable i j -> x i = x j
-/
lemma mem_ker_toLin'_lapMatrix_of_connectedComponent {G : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableEq G.ConnectedComponent] (c : G.ConnectedComponent) :
    (fun i ↦ if connectedComponentMk G i = c then 1 else 0) ∈
      LinearMap.ker (toLin' (lapMatrix ℝ G)) := by
  rw [LinearMap.mem_ker, toLin'_apply, lapMatrix_mulVec_eq_zero_iff_forall_reachable]
  grind [ConnectedComponent.eq]

/-- Given a connected component `c` of a graph `G`, `lapMatrix_ker_basis_aux c` is the map
`V → ℝ` which is `1` on the vertices in `c` and `0` elsewhere.
The family of these maps indexed by the connected components of `G` proves to be a basis
of the kernel of `lapMatrix G R` -/
/-
**SimpleGraph.lapMatrix_ker_basis_aux** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：lapMatrix_ker_basis_aux (c : G.ConnectedComponent) : LinearMap.ker (Matrix
.toLin' (G.lapMatrix Real))
参数：c : G.ConnectedComponent。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.mem_ker_toLin'_lapMatrix_of_connectedComponent`：∀ {V : Type 
u_1} [inst : Fintype V] [inst_1 : DecidableEq V] {G : SimpleGraph V} [inst_2 : D
ecidableRel G.Adj]   [inst_3 : DecidableEq G.Con…

--- 原说明 ---
Given a connected component `c` of a graph `G`, `lapMatrix_ker_basis_aux c` is t
he map
`V → ℝ` which is `1` on the vertices in `c` and `0` elsewhere.
The family of these maps indexed by the connected components of `G` proves to be
 a basis
of the kernel of `lapMatrix G R`
-/
def lapMatrix_ker_basis_aux (c : G.ConnectedComponent) :
    LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ)) :=
  ⟨fun i ↦ if G.connectedComponentMk i = c then (1 : ℝ) else 0,
    mem_ker_toLin'_lapMatrix_of_connectedComponent c⟩
/-
**SimpleGraph.linearIndependent_lapMatrix_ker_basis_aux** 是 Mathlib 中的一个引理，位于命名空
间 `SimpleGraph`。
形式化陈述：linearIndependent_lapMatrix_ker_basis_aux : LinearIndependent Real (lapMat
rix_ker_basis_aux G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.linearIndependent_iff`：Fintype.linearIndependent_iff [Fintype ι]
 : LinearIndependent R v ↔ forall g : ι -> R, ∑ i, g i • v i = 0 -> forall i, g 
i = 0
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `SimpleGraph.mem_ker_toLin'_lapMatrix_of_connectedComponent`：∀ {V : Type 
u_1} [inst : Fintype V] [inst_1 : DecidableEq V] {G : SimpleGraph V} [inst_2 : D
ecidableRel G.Adj]   [inst_3 : DecidableEq G.Con…
· 使用定理 `AddSubmonoid.coe_finsetSum`：∀ {ι : Type u_4} {M : Type u_5} [inst : AddC
ommMonoid M] (S : AddSubmonoid M) (f : ι → ↥S) (s : Finset ι),   ↑(∑ i ∈ s, f i)
 = ∑ i ∈ s, ↑(f …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Quot.exists_rep`：∀ {α : Sort u} {r : α → α → Prop} (q : Quot r), ∃ a, Qu
ot.mk r a = q
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
lemma linearIndependent_lapMatrix_ker_basis_aux :
    LinearIndependent ℝ (lapMatrix_ker_basis_aux G) := by
  rw [Fintype.linearIndependent_iff]
  intro g h0
  rw [Subtype.ext_iff] at h0
  have h : ∑ c, g c • lapMatrix_ker_basis_aux G c = fun i ↦ g (connectedComponentMk G i) := by
    simp only [lapMatrix_ker_basis_aux, SetLike.mk_smul_mk]
    repeat rw [AddSubmonoid.coe_finsetSum]
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, sum_ite_eq,
      mem_univ, ↓reduceIte]
  rw [h] at h0
  intro c
  obtain ⟨i, h'⟩ : ∃ i : V, G.connectedComponentMk i = c := Quot.exists_rep c
  exact h' ▸ congrFun h0 i

set_option backward.isDefEq.respectTransparency.types false in
/-
**SimpleGraph.top_le_span_range_lapMatrix_ker_basis_aux** 是 Mathlib 中的一个引理，位于命名空
间 `SimpleGraph`。
形式化陈述：top_le_span_range_lapMatrix_ker_basis_aux : ⊤ <= Submodule.span Real (Set.
range (lapMatrix_ker_basis_aux G))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_span_range_iff_exists_fun`：Submodule.mem_span_range_iff_ex
ists_fun : x in span R (range v) ↔ exists c : α -> R, ∑ i, c i • v i = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_reachable`：lapMatrix_mul
Vec_eq_zero_iff_forall_reachable {x : V -> Real} : G.lapMatrix Real *ᵥ x = 0 ↔ f
orall i j : V, G.Reachable i j -> x i = x j
· 使用定理 `Matrix.toLin'_apply`：∀ {R : Type u_1} [inst : CommSemiring R] {m : Type 
u_4} {n : Type u_5} [inst_1 : DecidableEq n] [inst_2 : Fintype n]   (M : Matrix 
m n R) (v…
· 使用定理 `LinearMap.map_coe_ker`：map_coe_ker (f : M ->ₛₗ[τ₁₂] M₂) (x : ker f) : f 
x = 0
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.mem_ker_toLin'_lapMatrix_of_connectedComponent`：∀ {V : Type 
u_1} [inst : Fintype V] [inst_1 : DecidableEq V] {G : SimpleGraph V} [inst_2 : D
ecidableRel G.Adj]   [inst_3 : DecidableEq G.Con…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `AddSubmonoid.coe_finsetSum`：∀ {ι : Type u_4} {M : Type u_5} [inst : AddC
ommMonoid M] (S : AddSubmonoid M) (f : ι → ↥S) (s : Finset ι),   ↑(∑ i ∈ s, f i)
 = ∑ i ∈ s, ↑(f …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
-/
lemma top_le_span_range_lapMatrix_ker_basis_aux :
    ⊤ ≤ Submodule.span ℝ (Set.range (lapMatrix_ker_basis_aux G)) := by
  intro x _
  rw [Submodule.mem_span_range_iff_exists_fun]
  use Quot.lift x.val (by rw [← lapMatrix_mulVec_eq_zero_iff_forall_reachable,
    ← toLin'_apply, LinearMap.map_coe_ker])
  ext j
  simp only [lapMatrix_ker_basis_aux]
  rw [AddSubmonoid.coe_finsetSum]
  simp only [SetLike.mk_smul_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, sum_ite_eq, mem_univ, ↓reduceIte]
  rfl

/-- `lapMatrix_ker_basis G` is a basis of the nullspace indexed by its connected components,
the basis is made up of the functions `V → ℝ` which are `1` on the vertices of the given
connected component and `0` elsewhere. -/
/-
**SimpleGraph.lapMatrix_ker_basis** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：lapMatrix_ker_basis
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.linearIndependent_lapMatrix_ker_basis_aux`：linearIndependent
_lapMatrix_ker_basis_aux : LinearIndependent Real (lapMatrix_ker_basis_aux G)
· 使用引理 `SimpleGraph.top_le_span_range_lapMatrix_ker_basis_aux`：top_le_span_range
_lapMatrix_ker_basis_aux : ⊤ <= Submodule.span Real (Set.range (lapMatrix_ker_ba
sis_aux G))

--- 原说明 ---
`lapMatrix_ker_basis G` is a basis of the nullspace indexed by its connected com
ponents,
the basis is made up of the functions `V → ℝ` which are `1` on the vertices of t
he given
connected component and `0` elsewhere.
-/
noncomputable def lapMatrix_ker_basis :=
  Basis.mk G.linearIndependent_lapMatrix_ker_basis_aux G.top_le_span_range_lapMatrix_ker_basis_aux

end

/-- The number of connected components in `G` is the dimension of the nullspace of its Laplacian. -/
/-
**SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix** 是 Mathli
b 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} [inst : Fintype V] (G : SimpleGraph V) [inst_1 : Decidabl
eRel G.Adj] [inst_2 : DecidableEq V],   Fintype.card G.ConnectedComponent = Modu
le.finrank ℝ ↥(Matrix.toLin' (SimpleGraph.lapMatrix ℝ G)).ker
参数：G : SimpleGraph V；Matrix.toLin' (SimpleGraph.lapMatrix ℝ G)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_eq_card_basis`：finrank_eq_card_basis {ι : Type w} [Fintyp
e ι] (h : Basis ι R M) : finrank R M = Fintype.card ι
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R

--- 原说明 ---
The number of connected components in `G` is the dimension of the nullspace of i
ts Laplacian.
-/
theorem card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix :
    Fintype.card G.ConnectedComponent = Module.finrank ℝ (G.lapMatrix ℝ).toLin'.ker := by
  classical
  rw [Module.finrank_eq_card_basis G.lapMatrix_ker_basis]

end SimpleGraph

