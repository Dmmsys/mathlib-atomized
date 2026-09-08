/-
Copyright (c) 2021 Gabriel Moise. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Moise, Yaël Dillies, Kyle Miller
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Matrix.Mul

/-!
# Incidence matrix of a simple graph

This file defines the unoriented incidence matrix of a simple graph.

## Main definitions

* `SimpleGraph.incMatrix`: `G.incMatrix R` is the incidence matrix of `G` over the ring `R`.

## Main results

* `SimpleGraph.incMatrix_mul_transpose_diag`: The diagonal entries of the product of
  `G.incMatrix R` and its transpose are the degrees of the vertices.
* `SimpleGraph.incMatrix_mul_transpose`: Gives a complete description of the product of
  `G.incMatrix R` and its transpose; the diagonal is the degrees of each vertex, and the
  off-diagonals are 1 or 0 depending on whether or not the vertices are adjacent.
* `SimpleGraph.incMatrix_transpose_mul_diag`: The diagonal entries of the product of the
  transpose of `G.incMatrix R` and `G.inc_matrix R` are `2` or `0` depending on whether or
  not the unordered pair is an edge of `G`.

## Implementation notes

The usual definition of an incidence matrix has one row per vertex and one column per edge.
However, this definition has columns indexed by all of `Sym2 α`, where `α` is the vertex type.
This appears not to change the theory, and for simple graphs it has the nice effect that every
incidence matrix for each `SimpleGraph α` has the same type.

## TODO

* Define the oriented incidence matrices for oriented graphs.
* Define the graph Laplacian of a simple graph using the oriented incidence matrix from an
  arbitrary orientation of a simple graph.
-/

@[expose] public section

assert_not_exists Field

open Finset Matrix SimpleGraph Sym2

namespace SimpleGraph

variable (R : Type*) {α : Type*} (G : SimpleGraph α)

/-- `G.incMatrix R` is the `α × Sym2 α` matrix whose `(a, e)`-entry is `1` if `e` is incident to
`a` and `0` otherwise. -/
/-
**SimpleGraph.incMatrix** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：incMatrix [Zero R] [One R] [DecidableEq α] [DecidableRel G.Adj] : Matrix α
 (Sym2 α) R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G.incMatrix R` is the `α × Sym2 α` matrix whose `(a, e)`-entry is `1` if `e` is
 incident to
`a` and `0` otherwise.
-/
def incMatrix [Zero R] [One R] [DecidableEq α] [DecidableRel G.Adj] : Matrix α (Sym2 α) R :=
  .of fun a e =>
    if e ∈ G.incidenceSet a then 1 else 0

variable {R}
/-
**SimpleGraph.incMatrix_apply** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：incMatrix_apply [Zero R] [One R] [DecidableEq α] [DecidableRel G.Adj] {a :
 α} {e : Sym2 α} : G.incMatrix R a e = (G.incidenceSet a).indicator 1 e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem incMatrix_apply [Zero R] [One R] [DecidableEq α] [DecidableRel G.Adj] {a : α} {e : Sym2 α} :
    G.incMatrix R a e = (G.incidenceSet a).indicator 1 e := by
  simp [incMatrix, Set.indicator]

/-- Entries of the incidence matrix can be computed given additional decidable instances. -/
/-
**SimpleGraph.incMatrix_apply'** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：incMatrix_apply' [Zero R] [One R] [DecidableEq α] [DecidableRel G.Adj] {a 
: α} {e : Sym2 α} : G.incMatrix R a e = if e in G.incidenceSet a then 1 else 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Entries of the incidence matrix can be computed given additional decidable insta
nces.
-/
theorem incMatrix_apply' [Zero R] [One R] [DecidableEq α] [DecidableRel G.Adj] {a : α}
    {e : Sym2 α} : G.incMatrix R a e = if e ∈ G.incidenceSet a then 1 else 0 := rfl

section MulZeroOneClass

variable [MulZeroOneClass R] [DecidableEq α] [DecidableRel G.Adj] {a b : α} {e : Sym2 α}

/-
**SimpleGraph.incMatrix_apply_mul_incMatrix_apply** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph`。
形式化陈述：incMatrix_apply_mul_incMatrix_apply : G.incMatrix R a e * G.incMatrix R b 
e = (G.incidenceSet a inter G.incidenceSet b).indicator 1 e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem incMatrix_apply_mul_incMatrix_apply : G.incMatrix R a e * G.incMatrix R b e =
    (G.incidenceSet a ∩ G.incidenceSet b).indicator 1 e := by
  simp [incMatrix_apply', Set.indicator_apply, ← ite_and, and_comm]
/-
**SimpleGraph.incMatrix_apply_mul_incMatrix_apply_of_not_adj** 是 Mathlib 中的一个定理，
位于命名空间 `SimpleGraph`。
形式化陈述：incMatrix_apply_mul_incMatrix_apply_of_not_adj (hab : a != b) (h : ¬G.Adj 
a b) : G.incMatrix R a e * G.incMatrix R b e = 0
参数：hab : a != b；h : ¬G.Adj a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.incMatrix_apply_mul_incMatrix_apply`：incMatrix_apply_mul_inc
Matrix_apply : G.incMatrix R a e * G.incMatrix R b e = (G.incidenceSet a inter G
.incidenceSet b).indicator 1 e
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `SimpleGraph.incidenceSet_inter_incidenceSet_of_not_adj`：incidenceSet_int
er_incidenceSet_of_not_adj (h : ¬G.Adj a b) (hn : a != b) : G.incidenceSet a int
er G.incidenceSet b = ∅
· 使用定理 `Set.notMem_empty`：notMem_empty (x : α) : x ∉ (∅ : Set α)
-/
theorem incMatrix_apply_mul_incMatrix_apply_of_not_adj (hab : a ≠ b) (h : ¬G.Adj a b) :
    G.incMatrix R a e * G.incMatrix R b e = 0 := by
  rw [incMatrix_apply_mul_incMatrix_apply, Set.indicator_of_notMem]
  rw [G.incidenceSet_inter_incidenceSet_of_not_adj h hab]
  exact Set.notMem_empty e
/-
**SimpleGraph.incMatrix_of_notMem_incidenceSet** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph`。
形式化陈述：incMatrix_of_notMem_incidenceSet (h : e ∉ G.incidenceSet a) : G.incMatrix 
R a e = 0
参数：h : e ∉ G.incidenceSet a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.incMatrix_apply`：incMatrix_apply [Zero R] [One R] [Decidable
Eq α] [DecidableRel G.Adj] {a : α} {e : Sym2 α} : G.incMatrix R a e = (G.inciden
ceSet a).indicato…
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
-/
theorem incMatrix_of_notMem_incidenceSet (h : e ∉ G.incidenceSet a) : G.incMatrix R a e = 0 := by
  rw [incMatrix_apply, Set.indicator_of_notMem h]
/-
**SimpleGraph.incMatrix_of_mem_incidenceSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph`。
形式化陈述：incMatrix_of_mem_incidenceSet (h : e in G.incidenceSet a) : G.incMatrix R 
a e = 1
参数：h : e in G.incidenceSet a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.incMatrix_apply`：incMatrix_apply [Zero R] [One R] [Decidable
Eq α] [DecidableRel G.Adj] {a : α} {e : Sym2 α} : G.incMatrix R a e = (G.inciden
ceSet a).indicato…
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用引理 `Pi.one_apply`：one_apply (i : ι) : (1 : forall i, M i) i = 1
-/
theorem incMatrix_of_mem_incidenceSet (h : e ∈ G.incidenceSet a) : G.incMatrix R a e = 1 := by
  rw [incMatrix_apply, Set.indicator_of_mem h, Pi.one_apply]

variable [Nontrivial R]
/-
**SimpleGraph.incMatrix_apply_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
`。
形式化陈述：incMatrix_apply_eq_zero_iff : G.incMatrix R a e = 0 ↔ e ∉ G.incidenceSet a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.incMatrix_apply`：incMatrix_apply [Zero R] [One R] [Decidable
Eq α] [DecidableRel G.Adj] {a : α} {e : Sym2 α} : G.incMatrix R a e = (G.inciden
ceSet a).indicato…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem incMatrix_apply_eq_zero_iff : G.incMatrix R a e = 0 ↔ e ∉ G.incidenceSet a := by
  simp only [incMatrix_apply, Set.indicator_apply_eq_zero, Pi.one_apply, one_ne_zero]
/-
**SimpleGraph.incMatrix_apply_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`
。
形式化陈述：incMatrix_apply_eq_one_iff : G.incMatrix R a e = 1 ↔ e in G.incidenceSet a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.ite_eq_left_iff`：∀ {α : Sort u_1} {P : Prop} [inst : Decidable P] {a 
b : α}, a ≠ b → ((if P then a else b) = a ↔ P)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
theorem incMatrix_apply_eq_one_iff : G.incMatrix R a e = 1 ↔ e ∈ G.incidenceSet a := by
  convert! one_ne_zero.ite_eq_left_iff
  infer_instance

end MulZeroOneClass

section NonAssocSemiring

variable [NonAssocSemiring R] [DecidableEq α] [DecidableRel G.Adj] {a : α} {e : Sym2 α}

/-
**SimpleGraph.sum_incMatrix_apply** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：sum_incMatrix_apply [Fintype (Sym2 α)] [Fintype (neighborSet G a)] : ∑ e, 
G.incMatrix R a e = G.degree a
参数：Sym2 α；neighborSet G a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_boole`：∀ {ι : Type u_1} {R : Type u_4} [inst : AddCommMonoidW
ithOne R] (p : ι → Prop) [inst_1 : DecidablePred p]   (s : Finset ι), (∑ x ∈ s, 
if p x…
· 使用定理 `Set.filter_mem_univ_eq_toFinset`：filter_mem_univ_eq_toFinset [Fintype α]
 (s : Set α) [Fintype s] [DecidablePred (· in s)] : Finset.univ.filter (· in s) 
= s.toFinset
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `SimpleGraph.card_incidenceSet_eq_degree`：card_incidenceSet_eq_degree [De
cidableEq V] : Fintype.card (G.incidenceSet v) = G.degree v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_incMatrix_apply [Fintype (Sym2 α)] [Fintype (neighborSet G a)] :
    ∑ e, G.incMatrix R a e = G.degree a := by
  simp [incMatrix_apply', sum_boole, Set.filter_mem_univ_eq_toFinset, card_incidenceSet_eq_degree]

set_option backward.isDefEq.respectTransparency false in
/-
**SimpleGraph.incMatrix_mul_transpose_diag** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
形式化陈述：incMatrix_mul_transpose_diag [Fintype (Sym2 α)] [Fintype (neighborSet G a)
] : (G.incMatrix R * (G.incMatrix R)ᵀ) a a = G.degree a
参数：Sym2 α；neighborSet G a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.sum_incMatrix_apply`：sum_incMatrix_apply [Fintype (Sym2 α)] 
[Fintype (neighborSet G a)] : ∑ e, G.incMatrix R a e = G.degree a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.mul_apply`：mul_apply [Fintype m] [Mul α] [AddCommMonoid α] {M : M
atrix l m α} {N : Matrix m n α} {i k} : (M * N) i k = ∑ j, M i j * N j k
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.sum_boole`：∀ {ι : Type u_1} {R : Type u_4} [inst : AddCommMonoidW
ithOne R] (p : ι → Prop) [inst_1 : DecidablePred p]   (s : Finset ι), (∑ x ∈ s, 
if p x…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem incMatrix_mul_transpose_diag [Fintype (Sym2 α)] [Fintype (neighborSet G a)] :
    (G.incMatrix R * (G.incMatrix R)ᵀ) a a = G.degree a := by
  rw [← sum_incMatrix_apply]
  simp only [mul_apply, incMatrix_apply', transpose_apply, mul_ite, mul_one, mul_zero]
  simp_all only [ite_true, sum_boole]
/-
**SimpleGraph.sum_incMatrix_apply_of_mem_edgeSet** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph`。
形式化陈述：sum_incMatrix_apply_of_mem_edgeSet [Fintype α] : e in G.edgeSet -> ∑ a, G.
incMatrix R a e = 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_two`：cast_two [NatCast R] : ((2 : Nat) : R) = (2 : R)
· 使用定理 `Finset.card_pair`：∀ {α : Type u_1} {a b : α} [inst : DecidableEq α], a ≠
 b → {a, b}.card = 2
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
· 使用定理 `SimpleGraph.mem_edgeSet`：mem_edgeSet : s(v, w) in G.edgeSet ↔ G.Adj v w
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.sum_boole`：∀ {ι : Type u_1} {R : Type u_4} [inst : AddCommMonoidW
ithOne R] (p : ι → Prop) [inst_1 : DecidablePred p]   (s : Finset ι), (∑ x ∈ s, 
if p x…
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sum_incMatrix_apply_of_mem_edgeSet [Fintype α] :
    e ∈ G.edgeSet → ∑ a, G.incMatrix R a e = 2 := by
  refine e.ind ?_
  intro a b h
  rw [mem_edgeSet] at h
  rw [← Nat.cast_two, ← card_pair h.ne]
  simp only [incMatrix_apply', sum_boole, mk'_mem_incidenceSet_iff, h]
  congr 2
  ext e
  simp
/-
**SimpleGraph.sum_incMatrix_apply_of_notMem_edgeSet** 是 Mathlib 中的一个定理，位于命名空间 `S
impleGraph`。
形式化陈述：sum_incMatrix_apply_of_notMem_edgeSet [Fintype α] (h : e ∉ G.edgeSet) : ∑ 
a, G.incMatrix R a e = 0
参数：h : e ∉ G.edgeSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `SimpleGraph.incMatrix_of_notMem_incidenceSet`：incMatrix_of_notMem_incide
nceSet (h : e ∉ G.incidenceSet a) : G.incMatrix R a e = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem sum_incMatrix_apply_of_notMem_edgeSet [Fintype α] (h : e ∉ G.edgeSet) :
    ∑ a, G.incMatrix R a e = 0 :=
  sum_eq_zero fun _ _ => G.incMatrix_of_notMem_incidenceSet fun he => h he.1
/-
**SimpleGraph.incMatrix_transpose_mul_diag** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
形式化陈述：incMatrix_transpose_mul_diag [Fintype α] [Decidable (e in G.edgeSet)] : ((
G.incMatrix R)ᵀ * G.incMatrix R) e e = if e in G.edgeSet then 2 else 0
参数：e in G.edgeSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ite_zero_mul_ite_zero`：ite_zero_mul_ite_zero : ite P a 0 * ite Q b 0 = i
te (P ∧ Q) (a * b) 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Finset.sum_boole`：∀ {ι : Type u_1} {R : Type u_4} [inst : AddCommMonoidW
ithOne R] (p : ι → Prop) [inst_1 : DecidablePred p]   (s : Finset ι), (∑ x ∈ s, 
if p x…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_two`：cast_two [NatCast R] : ((2 : Nat) : R) = (2 : R)
· 使用定理 `Finset.card_pair`：∀ {α : Type u_1} {a b : α} [inst : DecidableEq α], a ≠
 b → {a, b}.card = 2
· 使用定理 `SimpleGraph.ne_of_adj`：ne_of_adj (h : G.Adj a b) : a != b
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.mem_edgeSet`：mem_edgeSet : s(v, w) in G.edgeSet ↔ G.Adj v w
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
（共 33 条，此处仅展示前 30 条）
-/
theorem incMatrix_transpose_mul_diag [Fintype α] [Decidable (e ∈ G.edgeSet)] :
    ((G.incMatrix R)ᵀ * G.incMatrix R) e e = if e ∈ G.edgeSet then 2 else 0 := by
  simp only [Matrix.mul_apply, incMatrix_apply', transpose_apply, ite_zero_mul_ite_zero, one_mul,
    sum_boole, and_self_iff]
  split_ifs with h
  · revert h
    refine e.ind ?_
    intro v w h
    rw [← Nat.cast_two, ← card_pair (G.ne_of_adj h)]
    simp only [mk'_mem_incidenceSet_iff, G.mem_edgeSet.mp h, true_and]
    congr 2
    ext u
    simp
  · revert h
    refine e.ind ?_
    intro v w h
    simp [mk'_mem_incidenceSet_iff, G.mem_edgeSet.not.mp h]

end NonAssocSemiring

section Semiring

variable [Fintype (Sym2 α)] [DecidableEq α] [DecidableRel G.Adj] [Semiring R] {a b : α}

/-
**SimpleGraph.incMatrix_mul_transpose_apply_of_adj** 是 Mathlib 中的一个定理，位于命名空间 `Si
mpleGraph`。
形式化陈述：incMatrix_mul_transpose_apply_of_adj (h : G.Adj a b) : (G.incMatrix R * (G
.incMatrix R)ᵀ) a b = (1 : R)
参数：h : G.Adj a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `SimpleGraph.incMatrix_apply_mul_incMatrix_apply`：incMatrix_apply_mul_inc
Matrix_apply : G.incMatrix R a e * G.incMatrix R b e = (G.incidenceSet a inter G
.incidenceSet b).indicator 1 e
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Finset.sum_boole`：∀ {ι : Type u_1} {R : Type u_4} [inst : AddCommMonoidW
ithOne R] (p : ι → Prop) [inst_1 : DecidablePred p]   (s : Finset ι), (∑ x ∈ s, 
if p x…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_eq_singleton`：coe_eq_singleton {s : Finset α} {a : α} : (s : 
Set α) = {a} ↔ s = {a}
· 使用定理 `Finset.coe_filter_univ`：coe_filter_univ (p : α -> Prop) [DecidablePred p
] : (univ.filter p : Set α) = { x | p x }
· 使用定理 `SimpleGraph.incidenceSet_inter_incidenceSet_of_adj`：incidenceSet_inter_i
ncidenceSet_of_adj (h : G.Adj a b) : G.incidenceSet a inter G.incidenceSet b = {
s(a, b)}
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem incMatrix_mul_transpose_apply_of_adj (h : G.Adj a b) :
    (G.incMatrix R * (G.incMatrix R)ᵀ) a b = (1 : R) := by
  simp_rw [Matrix.mul_apply, Matrix.transpose_apply, incMatrix_apply_mul_incMatrix_apply,
    Set.indicator_apply, Pi.one_apply, sum_boole]
  convert! @Nat.cast_one R _
  convert! card_singleton s(a, b)
  rw [← coe_eq_singleton, coe_filter_univ]
  exact G.incidenceSet_inter_incidenceSet_of_adj h
/-
**SimpleGraph.incMatrix_mul_transpose** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：incMatrix_mul_transpose [G.LocallyFinite] : G.incMatrix R * (G.incMatrix R
)ᵀ = of fun a b => if a = b then (G.degree a : R) else if G.Adj a b then 1 else 
0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `SimpleGraph.incMatrix_mul_transpose_diag`：incMatrix_mul_transpose_diag [
Fintype (Sym2 α)] [Fintype (neighborSet G a)] : (G.incMatrix R * (G.incMatrix R)
ᵀ) a a = G.degree a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `SimpleGraph.incMatrix_mul_transpose_apply_of_adj`：incMatrix_mul_transpos
e_apply_of_adj (h : G.Adj a b) : (G.incMatrix R * (G.incMatrix R)ᵀ) a b = (1 : R
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.incMatrix_apply_mul_incMatrix_apply_of_not_adj`：incMatrix_ap
ply_mul_incMatrix_apply_of_not_adj (hab : a != b) (h : ¬G.Adj a b) : G.incMatrix
 R a e * G.incMatrix R b e = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem incMatrix_mul_transpose [G.LocallyFinite] :
    G.incMatrix R * (G.incMatrix R)ᵀ =
      of fun a b => if a = b then (G.degree a : R) else if G.Adj a b then 1 else 0 := by
  ext a b
  dsimp
  split_ifs with h h'
  · subst b
    exact incMatrix_mul_transpose_diag (R := R) G
  · exact G.incMatrix_mul_transpose_apply_of_adj h'
  · simp only [Matrix.mul_apply, Matrix.transpose_apply,
      G.incMatrix_apply_mul_incMatrix_apply_of_not_adj h h', sum_const_zero]

end Semiring

end SimpleGraph

