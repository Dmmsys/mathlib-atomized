/-
Copyright (c) 2026 Edward van de Meent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward van de Meent
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
### Definition of Cayley graphs

This file defines and proves several fact about Cayley graphs.
A Cayley graph over type `M` with generators `s : Set M` is a graph in which two vertices `u ≠ v`
are adjacent if and only if there is some `g ∈ s` such that `u * g = v` or `v * g = u`.
The elements of `s` are called generators.

## Main declarations

* `SimpleGraph.mulCayley s`: the Cayley graph over `M` induced by `[Mul M]` with generators `s`.
* `SimpleGraph.addCayley s`: the Cayley graph over `M` induced by `[Add M]` with generators `s`.

## TODOS
* Add API describing behaviour w/r/t `MulOpposite`.
* Add lemma showing this graph is the same as `SimpleGraph.circulantGraph` in appropriate settings.

-/

@[expose] public section

namespace SimpleGraph

/-- The Cayley graph induced by an operation `[Mul M]` with generators `s` -/
@[to_additive /-- The Cayley graph induced by an operation `[Add M]` with generators `s` -/]
/-
**SimpleGraph.mulCayley** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：mulCayley {M : Type*} (s : Set M) [Mul M] : SimpleGraph M
参数：s : Set M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Cayley graph induced by an operation `[Mul M]` with generators `s`
-/
def mulCayley {M : Type*} (s : Set M) [Mul M] : SimpleGraph M :=
  fromRel (∃ g ∈ s, · * g = ·)

variable {M : Type*} (s : Set M)

section Mul
variable [Mul M]

/-- See `mulCayley_adj` for the more convenient form in a `Group`. -/
@[to_additive /-- See `addCayley_adj` for the more convenient form in an `AddGroup`. -/]
/-
**SimpleGraph.mulCayley_adj'** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：mulCayley_adj' (u v : M) : (mulCayley s).Adj u v ↔ u != v ∧ exists g in s,
 u * g = v ∨ u = v * g
参数：u v : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
See `mulCayley_adj` for the more convenient form in a `Group`.
-/
lemma mulCayley_adj' (u v : M) :
    (mulCayley s).Adj u v ↔ u ≠ v ∧ ∃ g ∈ s, u * g = v ∨ u = v * g := by
  simp [mulCayley, ← exists_or, ← and_or_left, eq_comm]

@[to_additive]
/-
**SimpleGraph.mulCayley_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：mulCayley_le_iff (G : SimpleGraph M) : mulCayley s <= G ↔ forall g in s, f
orall a, a * g != a -> G.Adj (a * g) a
参数：G : SimpleGraph M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.le_iff_adj`：le_iff_adj {G H : SimpleGraph V} : G <= H ↔ fora
ll v w, G.Adj v w -> H.Adj v w
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma mulCayley_le_iff (G : SimpleGraph M) :
    mulCayley s ≤ G ↔ ∀ g ∈ s, ∀ a, a * g ≠ a → G.Adj (a * g) a := by
  rw [SimpleGraph.le_iff_adj]
  simp only [mulCayley_adj', ne_eq, and_imp, forall_exists_index]
  constructor
  · intro h g hg a ha
    exact h (a * g) a ha g hg (Or.inr rfl)
  · rintro h v w hvw g hg (rfl | rfl)
    · exact (h g hg v (hvw ·.symm)).symm
    · exact h g hg w hvw

@[to_additive]
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Fintype M] [DecidableEq M] [DecidablePred (· ∈ s)] :
    DecidableRel (mulCayley s).Adj := fun u v =>
  decidable_of_iff (u ≠ v ∧ ∃ g ∈ s, u * g = v ∨ u = v * g) (mulCayley_adj' s u v).symm

variable (M) in
/-- `mulCayley` is a left (order-)adjoint. -/
@[to_additive /-- `addCayley` is a left (order-)adjoint. -/]
/-
**SimpleGraph.mulCayley_gc** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：mulCayley_gc : GaloisConnection (mulCayley ·) ({g : M | forall a, a * g !=
 a -> ·.Adj (a * g) a})
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`mulCayley` is a left (order-)adjoint.
-/
lemma mulCayley_gc :
    GaloisConnection (mulCayley ·) ({g : M | ∀ a, a * g ≠ a → ·.Adj (a * g) a}) := by
  intro S G
  simp [mulCayley_le_iff, Set.subset_def]

@[to_additive]
/-
**SimpleGraph.mulCayley_monotone** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：mulCayley_monotone : Monotone (mulCayley (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用引理 `SimpleGraph.mulCayley_gc`：mulCayley_gc : GaloisConnection (mulCayley ·) 
({g : M | forall a, a * g != a -> ·.Adj (a * g) a})
-/
theorem mulCayley_monotone : Monotone (mulCayley (M := M) ·) :=
  (mulCayley_gc M).monotone_l

@[to_additive (attr := gcongr)]
/-
**SimpleGraph.mulCayley_mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：mulCayley_mono {U V : Set M} (hUV : U subseteq V) : mulCayley U <= mulCayl
ey V
参数：hUV : U subseteq V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.mulCayley_monotone`：mulCayley_monotone : Monotone (mulCayley
 (M
-/
theorem mulCayley_mono {U V : Set M} (hUV : U ⊆ V) : mulCayley U ≤ mulCayley V :=
  mulCayley_monotone hUV

@[to_additive (attr := simp)]
/-
**SimpleGraph.mulCayley_empty** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：mulCayley_empty : mulCayley (∅ : Set M) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用引理 `SimpleGraph.mulCayley_gc`：mulCayley_gc : GaloisConnection (mulCayley ·) 
({g : M | forall a, a * g != a -> ·.Adj (a * g) a})
-/
theorem mulCayley_empty : mulCayley (∅ : Set M) = ⊥ := (mulCayley_gc M).l_bot

@[to_additive (attr := simp)]
/-
**SimpleGraph.mulCayley_union** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：mulCayley_union (s₁ s₂ : Set M) : mulCayley (s₁ union s₂) = mulCayley s₁ ⊔
 mulCayley s₂
参数：s₁ s₂ : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用引理 `SimpleGraph.mulCayley_gc`：mulCayley_gc : GaloisConnection (mulCayley ·) 
({g : M | forall a, a * g != a -> ·.Adj (a * g) a})
-/
theorem mulCayley_union (s₁ s₂ : Set M) : mulCayley (s₁ ∪ s₂) = mulCayley s₁ ⊔ mulCayley s₂ :=
  (mulCayley_gc M).l_sup

end Mul

section Semigroup
variable [Semigroup M]

@[to_additive (attr := simp)]
/-
**SimpleGraph.mulCayley_adj_mul_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
`。
形式化陈述：mulCayley_adj_mul_iff_right [IsLeftCancelMul M] {s : Set M} {u v d : M} : 
(mulCayley s).Adj (d * u) (d * v) ↔ (mulCayley s).Adj u v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mulCayley_adj_mul_iff_right [IsLeftCancelMul M] {s : Set M} {u v d : M} :
    (mulCayley s).Adj (d * u) (d * v) ↔ (mulCayley s).Adj u v := by
  simp [mulCayley_adj', mul_assoc]

end Semigroup

section MulOneClass
variable [MulOneClass M]

@[to_additive (attr := simp)]
/-
**SimpleGraph.mulCayley_erase_one** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：mulCayley_erase_one : mulCayley (s \ {1}) = mulCayley s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sdiff_union_inter`：sdiff_union_inter (s t : Set α) : s \ t union s i
nter t = s
· 使用定理 `SimpleGraph.mulCayley_union`：mulCayley_union (s₁ s₂ : Set M) : mulCayley
 (s₁ union s₂) = mulCayley s₁ ⊔ mulCayley s₂
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem mulCayley_erase_one : mulCayley (s \ {1}) = mulCayley s := by
  nth_rw 2 [← Set.sdiff_union_inter s {1}]
  rw [mulCayley_union]
  ext u v
  simp +contextual [mulCayley_adj']

@[to_additive (attr := simp)]
/-
**SimpleGraph.mulCayley_insert_one** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：mulCayley_insert_one : mulCayley (insert 1 s) = mulCayley s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Set.union_sdiff_right`：union_sdiff_right {s t : Set α} : (s union t) \ t
 = s \ t
· 使用定理 `sdiff_idem`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b
 : α}, (a \ b) \ b = a \ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mulCayley_insert_one : mulCayley (insert 1 s) = mulCayley s := by
  simp [← Set.union_singleton, ← mulCayley_erase_one]

@[to_additive (attr := simp)]
/-
**SimpleGraph.mulCayley_singleton_one** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：mulCayley_singleton_one : mulCayley ({1} : Set M) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.mulCayley_erase_one`：mulCayley_erase_one : mulCayley (s \ {1
}) = mulCayley s
· 使用定理 `Set.sdiff_self`：sdiff_self {s : Set α} : s \ s = ∅
· 使用定理 `SimpleGraph.mulCayley_empty`：mulCayley_empty : mulCayley (∅ : Set M) = ⊥
-/
theorem mulCayley_singleton_one : mulCayley ({1} : Set M) = ⊥ := by
  rw [← mulCayley_erase_one, Set.sdiff_self, mulCayley_empty]

end MulOneClass
section Group
variable [Group M]

@[to_additive]
/-
**SimpleGraph.mulCayley_adj** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：mulCayley_adj (u v : M) : (mulCayley s).Adj u v ↔ u != v ∧ (u⁻¹ * v in s ∨
 v⁻¹ * u in s)
参数：u v : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_inv_mul_iff_mul_eq`：eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c
· 使用定理 `inv_mul_eq_iff_eq_mul`：inv_mul_eq_iff_eq_mul : a⁻¹ * b = c ↔ b = a * c
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mulCayley_adj (u v : M) :
    (mulCayley s).Adj u v ↔ u ≠ v ∧ (u⁻¹ * v ∈ s ∨ v⁻¹ * u ∈ s) := by
  simp [mulCayley_adj', ← eq_inv_mul_iff_mul_eq (b := u), ← inv_mul_eq_iff_eq_mul (a := v),
    and_or_left, exists_or]

@[to_additive (attr := simp)]
/-
**SimpleGraph.mulCayley_inv** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：mulCayley_inv : mulCayley s⁻¹ = mulCayley s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mulCayley_inv : mulCayley s⁻¹ = mulCayley s := by
  ext u v
  simp [mulCayley_adj, or_comm]

@[to_additive]
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq M] [DecidablePred (· ∈ s)] : DecidableRel (mulCayley s).Adj :=
  fun u v => decidable_of_iff (u ≠ v ∧ (u⁻¹ * v ∈ s ∨ v⁻¹ * u ∈ s)) (mulCayley_adj s u v).symm

@[to_additive (attr := simp)]
/-
**SimpleGraph.mulCayley_univ** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：mulCayley_univ : mulCayley (Set.univ : Set M) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mulCayley_univ : mulCayley (Set.univ : Set M) = ⊤ := by
  ext _ _
  simp [mulCayley_adj]

@[to_additive (attr := simp)]
/-
**SimpleGraph.mulCayley_compl_singleton_one** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph`。
形式化陈述：mulCayley_compl_singleton_one : mulCayley ({1}ᶜ : Set M) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
· 使用定理 `SimpleGraph.mulCayley_erase_one`：mulCayley_erase_one : mulCayley (s \ {1
}) = mulCayley s
· 使用定理 `SimpleGraph.mulCayley_univ`：mulCayley_univ : mulCayley (Set.univ : Set M
) = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mulCayley_compl_singleton_one : mulCayley ({1}ᶜ : Set M) = ⊤ := by
  simp [Set.compl_eq_univ_sdiff]

end Group

end SimpleGraph

