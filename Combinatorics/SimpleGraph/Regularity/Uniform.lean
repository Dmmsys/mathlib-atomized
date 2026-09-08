/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Combinatorics.SimpleGraph.Density
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Order.Partition.Equipartition
public import Mathlib.SetTheory.Cardinal.Order

/-!
# Graph uniformity and uniform partitions

In this file we define uniformity of a pair of vertices in a graph and uniformity of a partition of
vertices of a graph. Both are also known as ε-regularity.

Finsets of vertices `s` and `t` are `ε`-uniform in a graph `G` if their edge density is at most
`ε`-far from the density of any big enough `s'` and `t'` where `s' ⊆ s`, `t' ⊆ t`.
The definition is pretty technical, but it amounts to the edges between `s` and `t` being "random"
The literature contains several definitions which are equivalent up to scaling `ε` by some constant
when the partition is equitable.

A partition `P` of the vertices is `ε`-uniform if the proportion of `ε`-uniform pairs of parts is
greater than `(1 - ε)`.

## Main declarations

* `SimpleGraph.IsUniform`: Graph uniformity of a pair of finsets of vertices.
* `SimpleGraph.nonuniformWitness`: `G.nonuniformWitness ε s t` and `G.nonuniformWitness ε t s`
  together witness the non-uniformity of `s` and `t`.
* `Finpartition.nonUniforms`: Nonuniform pairs of parts of a partition.
* `Finpartition.IsUniform`: Uniformity of a partition.
* `Finpartition.nonuniformWitnesses`: For each non-uniform pair of parts of a partition, pick
  witnesses of non-uniformity and dump them all together.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/

@[expose] public section


open Finset

variable {α 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-! ### Graph uniformity -/


namespace SimpleGraph

variable (G : SimpleGraph α) [DecidableRel G.Adj] (ε : 𝕜) {s t : Finset α} {a b : α}

/-- A pair of finsets of vertices is `ε`-uniform (aka `ε`-regular) iff their edge density is close
to the density of any big enough pair of subsets. Intuitively, the edges between them are
random-like. -/
/-
**SimpleGraph.IsUniform** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：IsUniform (s t : Finset α) : Prop
参数：s t : Finset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pair of finsets of vertices is `ε`-uniform (aka `ε`-regular) iff their edge de
nsity is close
to the density of any big enough pair of subsets. Intuitively, the edges between
 them are
random-like.
-/
def IsUniform (s t : Finset α) : Prop :=
  ∀ ⦃s'⦄, s' ⊆ s → ∀ ⦃t'⦄, t' ⊆ t → (#s : 𝕜) * ε ≤ #s' →
    (#t : 𝕜) * ε ≤ #t' → |(G.edgeDensity s' t' : 𝕜) - (G.edgeDensity s t : 𝕜)| < ε
deriving Decidable

variable {G ε}
/-
**SimpleGraph.IsUniform.mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsUniform`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] 
[IsStrictOrderedRing 𝕜] {G : SimpleGraph α}   [inst_3 : DecidableRel G.Adj] {ε :
 𝕜} {s t : Finset α} {ε' : 𝕜}, ε ≤ ε' → G.IsUniform ε s t → G.IsUniform ε' s t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
-/
theorem IsUniform.mono {ε' : 𝕜} (h : ε ≤ ε') (hε : IsUniform G ε s t) : IsUniform G ε' s t :=
  fun s' hs' t' ht' hs ht => by
  refine (hε hs' ht' (le_trans ?_ hs) (le_trans ?_ ht)).trans_le h <;> gcongr

omit [IsStrictOrderedRing 𝕜] in
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.Symm (IsUniform G ε) where
  symm s t h t' ht' s' hs' ht hs := by
    rw [edgeDensity_comm _ t', edgeDensity_comm _ t]
    exact h hs' ht' hs ht

omit [IsStrictOrderedRing 𝕜] in
/-
**SimpleGraph.IsUniform.symm** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsUniform`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] 
{G : SimpleGraph α}   [inst_2 : DecidableRel G.Adj] {ε : 𝕜} {s t : Finset α}, G.
IsUniform ε s t → G.IsUniform ε t s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symm_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b : α} [Std.Symm r], r a
 b → r b a
· 使用定理 `SimpleGraph.instSymmFinsetIsUniform`：∀ {α : Type u_1} {𝕜 : Type u_2} [in
st : Field 𝕜] [inst_1 : LinearOrder 𝕜] {G : SimpleGraph α}   [inst_2 : Decidable
Rel G.Adj] {ε : 𝕜}, Std.S…
-/
theorem IsUniform.symm : IsUniform G ε s t → IsUniform G ε t s :=
  symm_of _

variable (G)

omit [IsStrictOrderedRing 𝕜] in
/-
**SimpleGraph.isUniform_comm** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isUniform_comm : IsUniform G ε s t ↔ IsUniform G ε t s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symm_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b : α} [Std.Symm r], r a
 b → r b a
· 使用定理 `SimpleGraph.instSymmFinsetIsUniform`：∀ {α : Type u_1} {𝕜 : Type u_2} [in
st : Field 𝕜] [inst_1 : LinearOrder 𝕜] {G : SimpleGraph α}   [inst_2 : Decidable
Rel G.Adj] {ε : 𝕜}, Std.S…
-/
theorem isUniform_comm : IsUniform G ε s t ↔ IsUniform G ε t s :=
  ⟨symm_of _, symm_of _⟩
/-
**SimpleGraph.isUniform_one** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：isUniform_one : G.IsUniform (1 : 𝕜) s t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (h : s subseteq 
t) (h₂ : #t <= #s) : s = t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
-/
lemma isUniform_one : G.IsUniform (1 : 𝕜) s t := by
  intro s' hs' t' ht' hs ht
  rw [mul_one] at hs ht
  rw [eq_of_subset_of_card_le hs' (Nat.cast_le.1 hs),
    eq_of_subset_of_card_le ht' (Nat.cast_le.1 ht), sub_self, abs_zero]
  exact zero_lt_one

variable {G}
/-
**SimpleGraph.IsUniform.pos** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsUniform`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] 
[IsStrictOrderedRing 𝕜] {G : SimpleGraph α}   [inst_3 : DecidableRel G.Adj] {ε :
 𝕜} {s t : Finset α}, G.IsUniform ε s t → 0 < ε
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Finset.empty_subset`：empty_subset (s : Finset α) : ∅ subseteq s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `mul_nonpos_of_nonneg_of_nonpos`：mul_nonpos_of_nonneg_of_nonpos [PosMulMo
no α] (ha : 0 <= a) (hb : b <= 0) : a * b <= 0
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
-/
lemma IsUniform.pos (hG : G.IsUniform ε s t) : 0 < ε :=
  not_le.1 fun hε ↦ (hε.trans <| abs_nonneg _).not_gt <| hG (empty_subset _) (empty_subset _)
    (by simpa using mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hε)
    (by simpa using mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hε)
/-
**SimpleGraph.isUniform_singleton** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] 
[IsStrictOrderedRing 𝕜] {G : SimpleGraph α}   [inst_3 : DecidableRel G.Adj] {ε :
 𝕜} {a b : α}, G.IsUniform ε {a} {b} ↔ 0 < ε
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsUniform.pos`：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : Field
 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {G : SimpleGraph α}   [inst
_3 : DecidableR…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.subset_singleton_iff`：subset_singleton_iff {s : Finset α} {a : α}
 : s subseteq {a} ↔ s = ∅ ∨ s = {a}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
@[simp] lemma isUniform_singleton : G.IsUniform ε {a} {b} ↔ 0 < ε := by
  refine ⟨IsUniform.pos, fun hε s' hs' t' ht' hs ht ↦ ?_⟩
  rw [card_singleton, Nat.cast_one, one_mul] at hs ht
  obtain rfl | rfl := Finset.subset_singleton_iff.1 hs'
  · replace hs : ε ≤ 0 := by simpa using hs
    exact (hε.not_ge hs).elim
  obtain rfl | rfl := Finset.subset_singleton_iff.1 ht'
  · replace ht : ε ≤ 0 := by simpa using ht
    exact (hε.not_ge ht).elim
  · rwa [sub_self, abs_zero]
/-
**SimpleGraph.not_isUniform_zero** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：not_isUniform_zero : ¬G.IsUniform (0 : 𝕜) s t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Finset.empty_subset`：empty_subset (s : Finset α) : ∅ subseteq s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
theorem not_isUniform_zero : ¬G.IsUniform (0 : 𝕜) s t := fun h =>
  (abs_nonneg _).not_gt <| h (empty_subset _) (empty_subset _) (by simp) (by simp)
/-
**SimpleGraph.not_isUniform_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：not_isUniform_iff : ¬G.IsUniform ε s t ↔ exists s', s' subseteq s ∧ exists
 t', t' subseteq t ∧ #s * ε <= #s' ∧ #t * ε <= #t' ∧ ε <= |G.edgeDensity s' t' -
 G.edgeDensity s t|
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
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Rat.cast_abs`：∀ {K : Type u_5} [inst : Field K] [inst_1 : LinearOrder K]
 [IsStrictOrderedRing K] (q : ℚ), ↑|q| = |↑q|
· 使用定理 `Rat.cast_sub`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p - q) = ↑p - ↑q
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem not_isUniform_iff :
    ¬G.IsUniform ε s t ↔ ∃ s', s' ⊆ s ∧ ∃ t', t' ⊆ t ∧ #s * ε ≤ #s' ∧
      #t * ε ≤ #t' ∧ ε ≤ |G.edgeDensity s' t' - G.edgeDensity s t| := by
  unfold IsUniform
  simp only [not_forall, not_lt, exists_prop, Rat.cast_abs, Rat.cast_sub]

variable (G)

/-- An arbitrary pair of subsets witnessing the non-uniformity of `(s, t)`. If `(s, t)` is uniform,
returns `(s, t)`. Witnesses for `(s, t)` and `(t, s)` don't necessarily match. See
`SimpleGraph.nonuniformWitness`. -/
/-
**SimpleGraph.nonuniformWitnesses** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：nonuniformWitnesses (ε : 𝕜) (s t : Finset α) : Finset α × Finset α
参数：ε : 𝕜；s t : Finset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An arbitrary pair of subsets witnessing the non-uniformity of `(s, t)`. If `(s, 
t)` is uniform,
returns `(s, t)`. Witnesses for `(s, t)` and `(t, s)` don't necessarily match. S
ee
`SimpleGraph.nonuniformWitness`.
-/
noncomputable def nonuniformWitnesses (ε : 𝕜) (s t : Finset α) : Finset α × Finset α :=
  if h : ¬G.IsUniform ε s t then
    ((not_isUniform_iff.1 h).choose, (not_isUniform_iff.1 h).choose_spec.2.choose)
  else (s, t)
/-
**SimpleGraph.left_nonuniformWitnesses_subset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph`。
形式化陈述：left_nonuniformWitnesses_subset (h : ¬G.IsUniform ε s t) : (G.nonuniformWi
tnesses ε s t).1 subseteq s
参数：h : ¬G.IsUniform ε s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.nonuniformWitnesses.eq_1`：∀ {α : Type u_1} {𝕜 : Type u_2} [i
nst : Field 𝕜] [inst_1 : LinearOrder 𝕜] [inst_2 : IsStrictOrderedRing 𝕜]   (G : 
SimpleGraph α) [inst_3 : D…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.not_isUniform_iff`：not_isUniform_iff : ¬G.IsUniform ε s t ↔ 
exists s', s' subseteq s ∧ exists t', t' subseteq t ∧ #s * ε <= #s' ∧ #t * ε <= 
#t' ∧ ε <= |G.edgeD…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem left_nonuniformWitnesses_subset (h : ¬G.IsUniform ε s t) :
    (G.nonuniformWitnesses ε s t).1 ⊆ s := by
  rw [nonuniformWitnesses, dif_pos h]
  exact (not_isUniform_iff.1 h).choose_spec.1
/-
**SimpleGraph.left_nonuniformWitnesses_card** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph`。
形式化陈述：left_nonuniformWitnesses_card (h : ¬G.IsUniform ε s t) : #s * ε <= #(G.non
uniformWitnesses ε s t).1
参数：h : ¬G.IsUniform ε s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.nonuniformWitnesses.eq_1`：∀ {α : Type u_1} {𝕜 : Type u_2} [i
nst : Field 𝕜] [inst_1 : LinearOrder 𝕜] [inst_2 : IsStrictOrderedRing 𝕜]   (G : 
SimpleGraph α) [inst_3 : D…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.not_isUniform_iff`：not_isUniform_iff : ¬G.IsUniform ε s t ↔ 
exists s', s' subseteq s ∧ exists t', t' subseteq t ∧ #s * ε <= #s' ∧ #t * ε <= 
#t' ∧ ε <= |G.edgeD…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem left_nonuniformWitnesses_card (h : ¬G.IsUniform ε s t) :
    #s * ε ≤ #(G.nonuniformWitnesses ε s t).1 := by
  rw [nonuniformWitnesses, dif_pos h]
  exact (not_isUniform_iff.1 h).choose_spec.2.choose_spec.2.1
/-
**SimpleGraph.right_nonuniformWitnesses_subset** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph`。
形式化陈述：right_nonuniformWitnesses_subset (h : ¬G.IsUniform ε s t) : (G.nonuniformW
itnesses ε s t).2 subseteq t
参数：h : ¬G.IsUniform ε s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.nonuniformWitnesses.eq_1`：∀ {α : Type u_1} {𝕜 : Type u_2} [i
nst : Field 𝕜] [inst_1 : LinearOrder 𝕜] [inst_2 : IsStrictOrderedRing 𝕜]   (G : 
SimpleGraph α) [inst_3 : D…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.not_isUniform_iff`：not_isUniform_iff : ¬G.IsUniform ε s t ↔ 
exists s', s' subseteq s ∧ exists t', t' subseteq t ∧ #s * ε <= #s' ∧ #t * ε <= 
#t' ∧ ε <= |G.edgeD…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem right_nonuniformWitnesses_subset (h : ¬G.IsUniform ε s t) :
    (G.nonuniformWitnesses ε s t).2 ⊆ t := by
  rw [nonuniformWitnesses, dif_pos h]
  exact (not_isUniform_iff.1 h).choose_spec.2.choose_spec.1
/-
**SimpleGraph.right_nonuniformWitnesses_card** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph`。
形式化陈述：right_nonuniformWitnesses_card (h : ¬G.IsUniform ε s t) : #t * ε <= #(G.no
nuniformWitnesses ε s t).2
参数：h : ¬G.IsUniform ε s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.nonuniformWitnesses.eq_1`：∀ {α : Type u_1} {𝕜 : Type u_2} [i
nst : Field 𝕜] [inst_1 : LinearOrder 𝕜] [inst_2 : IsStrictOrderedRing 𝕜]   (G : 
SimpleGraph α) [inst_3 : D…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.not_isUniform_iff`：not_isUniform_iff : ¬G.IsUniform ε s t ↔ 
exists s', s' subseteq s ∧ exists t', t' subseteq t ∧ #s * ε <= #s' ∧ #t * ε <= 
#t' ∧ ε <= |G.edgeD…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem right_nonuniformWitnesses_card (h : ¬G.IsUniform ε s t) :
    #t * ε ≤ #(G.nonuniformWitnesses ε s t).2 := by
  rw [nonuniformWitnesses, dif_pos h]
  exact (not_isUniform_iff.1 h).choose_spec.2.choose_spec.2.2.1
/-
**SimpleGraph.nonuniformWitnesses_spec** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：nonuniformWitnesses_spec (h : ¬G.IsUniform ε s t) : ε <= |G.edgeDensity (G
.nonuniformWitnesses ε s t).1 (G.nonuniformWitnesses ε s t).2 - G.edgeDensity s 
t|
参数：h : ¬G.IsUniform ε s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.nonuniformWitnesses.eq_1`：∀ {α : Type u_1} {𝕜 : Type u_2} [i
nst : Field 𝕜] [inst_1 : LinearOrder 𝕜] [inst_2 : IsStrictOrderedRing 𝕜]   (G : 
SimpleGraph α) [inst_3 : D…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.not_isUniform_iff`：not_isUniform_iff : ¬G.IsUniform ε s t ↔ 
exists s', s' subseteq s ∧ exists t', t' subseteq t ∧ #s * ε <= #s' ∧ #t * ε <= 
#t' ∧ ε <= |G.edgeD…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem nonuniformWitnesses_spec (h : ¬G.IsUniform ε s t) :
    ε ≤
      |G.edgeDensity (G.nonuniformWitnesses ε s t).1 (G.nonuniformWitnesses ε s t).2 -
          G.edgeDensity s t| := by
  rw [nonuniformWitnesses, dif_pos h]
  exact (not_isUniform_iff.1 h).choose_spec.2.choose_spec.2.2.2

open scoped Classical in
/-- Arbitrary witness of non-uniformity. `G.nonuniformWitness ε s t` and
`G.nonuniformWitness ε t s` form a pair of subsets witnessing the non-uniformity of `(s, t)`. If
`(s, t)` is uniform, returns `s`. -/
/-
**SimpleGraph.nonuniformWitness** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：nonuniformWitness (ε : 𝕜) (s t : Finset α) : Finset α
参数：ε : 𝕜；s t : Finset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Arbitrary witness of non-uniformity. `G.nonuniformWitness ε s t` and
`G.nonuniformWitness ε t s` form a pair of subsets witnessing the non-uniformity
 of `(s, t)`. If
`(s, t)` is uniform, returns `s`.
-/
noncomputable def nonuniformWitness (ε : 𝕜) (s t : Finset α) : Finset α :=
  if WellOrderingRel s t then (G.nonuniformWitnesses ε s t).1 else (G.nonuniformWitnesses ε t s).2
/-
**SimpleGraph.nonuniformWitness_subset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：nonuniformWitness_subset (h : ¬G.IsUniform ε s t) : G.nonuniformWitness ε 
s t subseteq s
参数：h : ¬G.IsUniform ε s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `SimpleGraph.left_nonuniformWitnesses_subset`：left_nonuniformWitnesses_su
bset (h : ¬G.IsUniform ε s t) : (G.nonuniformWitnesses ε s t).1 subseteq s
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `SimpleGraph.right_nonuniformWitnesses_subset`：right_nonuniformWitnesses_
subset (h : ¬G.IsUniform ε s t) : (G.nonuniformWitnesses ε s t).2 subseteq t
· 使用定理 `SimpleGraph.IsUniform.symm`：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : Fiel
d 𝕜] [inst_1 : LinearOrder 𝕜] {G : SimpleGraph α}   [inst_2 : DecidableRel G.Adj
] {ε : 𝕜} {s t :…
-/
theorem nonuniformWitness_subset (h : ¬G.IsUniform ε s t) : G.nonuniformWitness ε s t ⊆ s := by
  unfold nonuniformWitness
  split_ifs
  · exact G.left_nonuniformWitnesses_subset h
  · exact G.right_nonuniformWitnesses_subset fun i => h i.symm
/-
**SimpleGraph.le_card_nonuniformWitness** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：le_card_nonuniformWitness (h : ¬G.IsUniform ε s t) : #s * ε <= #(G.nonunif
ormWitness ε s t)
参数：h : ¬G.IsUniform ε s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `SimpleGraph.left_nonuniformWitnesses_card`：left_nonuniformWitnesses_card
 (h : ¬G.IsUniform ε s t) : #s * ε <= #(G.nonuniformWitnesses ε s t).1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `SimpleGraph.right_nonuniformWitnesses_card`：right_nonuniformWitnesses_ca
rd (h : ¬G.IsUniform ε s t) : #t * ε <= #(G.nonuniformWitnesses ε s t).2
· 使用定理 `SimpleGraph.IsUniform.symm`：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : Fiel
d 𝕜] [inst_1 : LinearOrder 𝕜] {G : SimpleGraph α}   [inst_2 : DecidableRel G.Adj
] {ε : 𝕜} {s t :…
-/
theorem le_card_nonuniformWitness (h : ¬G.IsUniform ε s t) :
    #s * ε ≤ #(G.nonuniformWitness ε s t) := by
  unfold nonuniformWitness
  split_ifs
  · exact G.left_nonuniformWitnesses_card h
  · exact G.right_nonuniformWitnesses_card fun i => h i.symm
/-
**SimpleGraph.nonuniformWitness_spec** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：nonuniformWitness_spec (h₁ : s != t) (h₂ : ¬G.IsUniform ε s t) : ε <= |G.e
dgeDensity (G.nonuniformWitness ε s t) (G.nonuniformWitness ε t s) - G.edgeDensi
ty s t|
参数：h₁ : s != t；h₂ : ¬G.IsUniform ε s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `trichotomous_of`：trichotomous_of [Std.Trichotomous r] : forall a b : α, 
a ≺ b ∨ a = b ∨ b ≺ a
· 使用定理 `IsWellOrder.toTrichotomous`：∀ {α : Type u} {r : α → α → Prop} [self : Is
WellOrder α r], Std.Trichotomous r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `asymm`：asymm [Std.Asymm r] : a ≺ b -> ¬b ≺ a
· 使用定理 `instAsymmOfIsWellFounded`：∀ {α : Type u} (r : α → α → Prop) [IsWellFound
ed α r], Std.Asymm r
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `SimpleGraph.nonuniformWitnesses_spec`：nonuniformWitnesses_spec (h : ¬G.I
sUniform ε s t) : ε <= |G.edgeDensity (G.nonuniformWitnesses ε s t).1 (G.nonunif
ormWitnesses ε s t).2 - G.…
· 使用定理 `SimpleGraph.edgeDensity_comm`：edgeDensity_comm (s t : Finset α) : G.edge
Density s t = G.edgeDensity t s
· 使用定理 `SimpleGraph.IsUniform.symm`：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : Fiel
d 𝕜] [inst_1 : LinearOrder 𝕜] {G : SimpleGraph α}   [inst_2 : DecidableRel G.Adj
] {ε : 𝕜} {s t :…
-/
theorem nonuniformWitness_spec (h₁ : s ≠ t) (h₂ : ¬G.IsUniform ε s t) : ε ≤ |G.edgeDensity
    (G.nonuniformWitness ε s t) (G.nonuniformWitness ε t s) - G.edgeDensity s t| := by
  unfold nonuniformWitness
  rcases trichotomous_of WellOrderingRel s t with (lt | rfl | gt)
  · rw [if_pos lt, if_neg (asymm lt)]
    exact G.nonuniformWitnesses_spec h₂
  · cases h₁ rfl
  · rw [if_neg (asymm gt), if_pos gt, edgeDensity_comm, edgeDensity_comm _ s]
    apply G.nonuniformWitnesses_spec fun i => h₂ i.symm

end SimpleGraph

/-! ### Uniform partitions -/


variable [DecidableEq α] {A : Finset α} (P : Finpartition A) (G : SimpleGraph α)
  [DecidableRel G.Adj] {ε δ : 𝕜} {u v : Finset α}

namespace Finpartition

/-- The pairs of parts of a partition `P` which are not `ε`-dense in a graph `G`. Note that we
dismiss the diagonal. We do not care whether `s` is `ε`-dense with itself. -/
/-
**Finpartition.sparsePairs** 是 Mathlib 中的一个定义，位于命名空间 `Finpartition`。
形式化陈述：sparsePairs (ε : 𝕜) : Finset (Finset α × Finset α)
参数：ε : 𝕜。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pairs of parts of a partition `P` which are not `ε`-dense in a graph `G`. No
te that we
dismiss the diagonal. We do not care whether `s` is `ε`-dense with itself.
-/
def sparsePairs (ε : 𝕜) : Finset (Finset α × Finset α) :=
  P.parts.offDiag.filter fun (u, v) ↦ G.edgeDensity u v < ε

omit [IsStrictOrderedRing 𝕜] in
@[simp]
/-
**Finpartition.mk_mem_sparsePairs** 是 Mathlib 中的一个引理，位于命名空间 `Finpartition`。
形式化陈述：mk_mem_sparsePairs (u v : Finset α) (ε : 𝕜) : (u, v) in P.sparsePairs G ε 
↔ u in P.parts ∧ v in P.parts ∧ u != v ∧ G.edgeDensity u v < ε
参数：u v : Finset α；ε : 𝕜。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finpartition.sparsePairs.eq_1`：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : F
ield 𝕜] [inst_1 : LinearOrder 𝕜] [inst_2 : DecidableEq α] {A : Finset α}   (P : 
Finpartition A) (G …
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Finset.mem_offDiag`：mem_offDiag : x in s.offDiag ↔ x.1 in s ∧ x.2 in s ∧
 x.1 != x.2
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mk_mem_sparsePairs (u v : Finset α) (ε : 𝕜) :
    (u, v) ∈ P.sparsePairs G ε ↔ u ∈ P.parts ∧ v ∈ P.parts ∧ u ≠ v ∧ G.edgeDensity u v < ε := by
  rw [sparsePairs, mem_filter, mem_offDiag, and_assoc, and_assoc]

omit [IsStrictOrderedRing 𝕜] in
/-
**Finpartition.sparsePairs_mono** 是 Mathlib 中的一个引理，位于命名空间 `Finpartition`。
形式化陈述：sparsePairs_mono {ε ε' : 𝕜} (h : ε <= ε') : P.sparsePairs G ε subseteq P.s
parsePairs G ε'
参数：h : ε <= ε'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.monotone_filter_right`：∀ {α : Type u_1} (s : Finset α) ⦃p q : α →
 Prop⦄ [inst : DecidablePred p] [inst_1 : DecidablePred q],   (∀ a ∈ s, p a → q 
a) → Finset.filter…
· 使用定理 `LE.le.trans_lt'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a
 → c < b → c < a
-/
lemma sparsePairs_mono {ε ε' : 𝕜} (h : ε ≤ ε') : P.sparsePairs G ε ⊆ P.sparsePairs G ε' :=
  monotone_filter_right _ fun _ _ ↦ h.trans_lt'

/-- The pairs of parts of a partition `P` which are not `ε`-uniform in a graph `G`. Note that we
dismiss the diagonal. We do not care whether `s` is `ε`-uniform with itself. -/
/-
**Finpartition.nonUniforms** 是 Mathlib 中的一个定义，位于命名空间 `Finpartition`。
形式化陈述：nonUniforms (ε : 𝕜) : Finset (Finset α × Finset α)
参数：ε : 𝕜。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pairs of parts of a partition `P` which are not `ε`-uniform in a graph `G`. 
Note that we
dismiss the diagonal. We do not care whether `s` is `ε`-uniform with itself.
-/
def nonUniforms (ε : 𝕜) : Finset (Finset α × Finset α) :=
  P.parts.offDiag.filter fun (u, v) ↦ ¬G.IsUniform ε u v

omit [IsStrictOrderedRing 𝕜] in
/-
**Finpartition.mk_mem_nonUniforms** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] 
[inst_2 : DecidableEq α] {A : Finset α}   (P : Finpartition A) (G : SimpleGraph 
α) [inst_3 : DecidableRel G.Adj] {ε : 𝕜} {u v : Finset α},   (u, v) ∈ P.nonUnifo
rms G ε ↔ u ∈ P.parts ∧ v ∈ P.parts ∧ u ≠ v ∧ ¬G.IsUniform ε u v
参数：P : Finpartition A；G : SimpleGraph α；u, v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finpartition.nonUniforms.eq_1`：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : F
ield 𝕜] [inst_1 : LinearOrder 𝕜] [inst_2 : DecidableEq α] {A : Finset α}   (P : 
Finpartition A) (G …
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Finset.mem_offDiag`：mem_offDiag : x in s.offDiag ↔ x.1 in s ∧ x.2 in s ∧
 x.1 != x.2
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mk_mem_nonUniforms :
    (u, v) ∈ P.nonUniforms G ε ↔ u ∈ P.parts ∧ v ∈ P.parts ∧ u ≠ v ∧ ¬G.IsUniform ε u v := by
  rw [nonUniforms, mem_filter, mem_offDiag, and_assoc, and_assoc]
/-
**Finpartition.nonUniforms_mono** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：nonUniforms_mono {ε ε' : 𝕜} (h : ε <= ε') : P.nonUniforms G ε' subseteq P.
nonUniforms G ε
参数：h : ε <= ε'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.monotone_filter_right`：∀ {α : Type u_1} (s : Finset α) ⦃p q : α →
 Prop⦄ [inst : DecidablePred p] [inst_1 : DecidablePred q],   (∀ a ∈ s, p a → q 
a) → Finset.filter…
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `SimpleGraph.IsUniform.mono`：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : Fiel
d 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {G : SimpleGraph α}   [ins
t_3 : DecidableR…
-/
theorem nonUniforms_mono {ε ε' : 𝕜} (h : ε ≤ ε') : P.nonUniforms G ε' ⊆ P.nonUniforms G ε :=
  monotone_filter_right _ fun _ _ => mt <| SimpleGraph.IsUniform.mono h
/-
**Finpartition.nonUniforms_bot** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：nonUniforms_bot (hε : 0 < ε) : (⊥ : Finpartition A).nonUniforms G ε = ∅
参数：hε : 0 < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Finse
t α} : s = ∅ ↔ forall x, x ∉ s
· 使用定理 `Finset.singleton_injective`：singleton_injective : Injective (singleton :
 α -> Finset α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `SimpleGraph.isUniform_singleton`：∀ {α : Type u_1} {𝕜 : Type u_2} [inst :
 Field 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {G : SimpleGraph α}  
 [inst_3 : DecidableR…
-/
theorem nonUniforms_bot (hε : 0 < ε) : (⊥ : Finpartition A).nonUniforms G ε = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  rintro ⟨u, v⟩
  simp only [mk_mem_nonUniforms, parts_bot, mem_map, not_and,
    Classical.not_not, exists_imp]; dsimp
  rintro x ⟨_, rfl⟩ y ⟨_, rfl⟩ _
  rwa [SimpleGraph.isUniform_singleton]

/-- A finpartition of a graph's vertex set is `ε`-uniform (aka `ε`-regular) iff the proportion of
its pairs of parts that are not `ε`-uniform is at most `ε`. -/
/-
**Finpartition.IsUniform** 是 Mathlib 中的一个定义，位于命名空间 `Finpartition`。
形式化陈述：IsUniform (ε : 𝕜) : Prop
参数：ε : 𝕜。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finpartition of a graph's vertex set is `ε`-uniform (aka `ε`-regular) iff the 
proportion of
its pairs of parts that are not `ε`-uniform is at most `ε`.
-/
def IsUniform (ε : 𝕜) : Prop :=
  (#(P.nonUniforms G ε) : 𝕜) ≤ (#P.parts * (#P.parts - 1) : ℕ) * ε
/-
**Finpartition.bot_isUniform** 是 Mathlib 中的一个引理，位于命名空间 `Finpartition`。
形式化陈述：bot_isUniform (hε : 0 < ε) : (⊥ : Finpartition A).IsUniform G ε
参数：hε : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finpartition.IsUniform.eq_1`：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : Fie
ld 𝕜] [inst_1 : LinearOrder 𝕜] [inst_2 : DecidableEq α] {A : Finset α}   (P : Fi
npartition A) (G …
· 使用定理 `Finpartition.card_bot`：card_bot (s : Finset α) : #(⊥ : Finpartition s).p
arts = #s
· 使用定理 `Finpartition.nonUniforms_bot`：nonUniforms_bot (hε : 0 < ε) : (⊥ : Finpar
tition A).nonUniforms G ε = ∅
· 使用定理 `Finset.card_empty`：card_empty : #(∅ : Finset α) = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma bot_isUniform (hε : 0 < ε) : (⊥ : Finpartition A).IsUniform G ε := by
  rw [Finpartition.IsUniform, Finpartition.card_bot, nonUniforms_bot _ hε, Finset.card_empty,
    Nat.cast_zero]
  positivity
/-
**Finpartition.isUniform_one** 是 Mathlib 中的一个引理，位于命名空间 `Finpartition`。
形式化陈述：isUniform_one : P.IsUniform G (1 : 𝕜)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finpartition.IsUniform.eq_1`：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : Fie
ld 𝕜] [inst_1 : LinearOrder 𝕜] [inst_2 : DecidableEq α] {A : Finset α}   (P : Fi
npartition A) (G …
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.card_filter_le`：card_filter_le (s : Finset α) (p : α -> Prop) [De
cidablePred p] : #(s.filter p) <= #s
· 使用定理 `Finset.offDiag_card`：offDiag_card : (offDiag s).card = s.card * s.card -
 s.card
· 使用定理 `Nat.mul_sub_left_distrib`：∀ (n m k : ℕ), n * (m - k) = n * m - n * k
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma isUniform_one : P.IsUniform G (1 : 𝕜) := by
  rw [IsUniform, mul_one, Nat.cast_le]
  refine (card_filter_le _
    (fun uv => ¬SimpleGraph.IsUniform G 1 (Prod.fst uv) (Prod.snd uv))).trans ?_
  rw [offDiag_card, Nat.mul_sub_left_distrib, mul_one]

variable {P G}
/-
**Finpartition.IsUniform.mono** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition.IsUniform`
。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] 
[IsStrictOrderedRing 𝕜]   [inst_3 : DecidableEq α] {A : Finset α} {P : Finpartit
ion A} {G : SimpleGraph α} [inst_4 : DecidableRel G.Adj]   {ε ε' : 𝕜}, P.IsUnifo
rm G ε → ε ≤ ε' → P.IsUniform G ε'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Finpartition.nonUniforms_mono`：nonUniforms_mono {ε ε' : 𝕜} (h : ε <= ε')
 : P.nonUniforms G ε' subseteq P.nonUniforms G ε
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
-/
theorem IsUniform.mono {ε ε' : 𝕜} (hP : P.IsUniform G ε) (h : ε ≤ ε') : P.IsUniform G ε' :=
  ((Nat.cast_le.2 <| card_le_card <| P.nonUniforms_mono G h).trans hP).trans <| by gcongr

omit [IsStrictOrderedRing 𝕜] in
/-
**Finpartition.isUniformOfEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：isUniformOfEmpty (hP : P.parts = ∅) : P.IsUniform G ε
参数：hP : P.parts = ∅。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.filter.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p_1
 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Finset α
),       s = s…
· 使用定理 `Finset.filter_empty`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePr
ed p], Finset.filter p ∅ = ∅
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem isUniformOfEmpty (hP : P.parts = ∅) : P.IsUniform G ε := by
  simp [IsUniform, hP, nonUniforms]

omit [IsStrictOrderedRing 𝕜] in
/-
**Finpartition.nonempty_of_not_uniform** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：nonempty_of_not_uniform (h : ¬P.IsUniform G ε) : P.parts.Nonempty
参数：h : ¬P.IsUniform G ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.nonempty_of_ne_empty`：nonempty_of_ne_empty {s : Finset α} (h : s 
!= ∅) : s.Nonempty
· 使用定理 `Finpartition.isUniformOfEmpty`：isUniformOfEmpty (hP : P.parts = ∅) : P.I
sUniform G ε
-/
theorem nonempty_of_not_uniform (h : ¬P.IsUniform G ε) : P.parts.Nonempty :=
  nonempty_of_ne_empty fun h₁ => h <| isUniformOfEmpty h₁

variable (P G ε) (s : Finset α)

/-- A choice of witnesses of non-uniformity among the parts of a finpartition. -/
/-
**Finpartition.nonuniformWitnesses** 是 Mathlib 中的一个定义，位于命名空间 `Finpartition`。
形式化陈述：nonuniformWitnesses : Finset (Finset α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A choice of witnesses of non-uniformity among the parts of a finpartition.
-/
noncomputable def nonuniformWitnesses : Finset (Finset α) :=
  {t ∈ P.parts | s ≠ t ∧ ¬G.IsUniform ε s t}.image (G.nonuniformWitness ε s)

variable {P G ε s} {t : Finset α}
/-
**Finpartition.card_nonuniformWitnesses_le** 是 Mathlib 中的一个引理，位于命名空间 `Finpartiti
on`。
形式化陈述：card_nonuniformWitnesses_le : #(P.nonuniformWitnesses G ε s) <= #{t in P.p
arts | s != t ∧ ¬G.IsUniform ε s t}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_image_le`：card_image_le [DecidableEq β] : #(s.image f) <= #s
-/
lemma card_nonuniformWitnesses_le :
    #(P.nonuniformWitnesses G ε s) ≤ #{t ∈ P.parts | s ≠ t ∧ ¬G.IsUniform ε s t} := card_image_le
/-
**Finpartition.nonuniformWitness_mem_nonuniformWitnesses** 是 Mathlib 中的一个定理，位于命名
空间 `Finpartition`。
形式化陈述：nonuniformWitness_mem_nonuniformWitnesses (h : ¬G.IsUniform ε s t) (ht : t
 in P.parts) (hst : s != t) : G.nonuniformWitness ε s t in P.nonuniformWitnesses
 G ε s
参数：h : ¬G.IsUniform ε s t；ht : t in P.parts；hst : s != t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
-/
theorem nonuniformWitness_mem_nonuniformWitnesses (h : ¬G.IsUniform ε s t) (ht : t ∈ P.parts)
    (hst : s ≠ t) : G.nonuniformWitness ε s t ∈ P.nonuniformWitnesses G ε s :=
  mem_image_of_mem _ <| mem_filter.2 ⟨ht, hst, h⟩

/-! ### Equipartitions -/

open SimpleGraph in
/-
**Finpartition.IsEquipartition.card_interedges_sparsePairs_le'** 是 Mathlib 中的一个定
理，位于命名空间 `Finpartition.IsEquipartition`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] 
[IsStrictOrderedRing 𝕜]   [inst_3 : DecidableEq α] {A : Finset α} {P : Finpartit
ion A} {G : SimpleGraph α} [inst_4 : DecidableRel G.Adj]   {ε : 𝕜},   P.IsEquipa
rtition →     0 ≤ ε →       ↑((P.sparsePairs G ε).biUnion fun x =>              
 match x with               | (U, V) => G.interedges U V).card ≤         ε * (↑A
.card + ↑P.parts.card) ^ 2
参数：(P.sparsePairs G ε).biUnion fun x =>               match x with              
 | (U, V) => G.interedges U V；↑A.card + ↑P.parts.card。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Finset.card_biUnion_le`：card_biUnion_le [DecidableEq M] {s : Finset ι} {
t : ι -> Finset M} : #(s.biUnion t) <= ∑ a in s, #(t a)
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `div_lt_iff₀`：div_lt_iff₀ (hc : 0 < c) : b / c < a ↔ b < a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `Finset.Nonempty.card_pos`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
0 < s.card
· 使用定理 `Finpartition.nonempty_of_mem_parts`：nonempty_of_mem_parts {a : Finset α}
 (ha : a in P.parts) : a.Nonempty
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Rat.cast_div`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p / q) = ↑p / ↑q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `Rat.cast_mul`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p * q) = ↑p * ↑q
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
（共 57 条，此处仅展示前 30 条）
-/
lemma IsEquipartition.card_interedges_sparsePairs_le' (hP : P.IsEquipartition)
    (hε : 0 ≤ ε) :
    #((P.sparsePairs G ε).biUnion fun (U, V) ↦ G.interedges U V) ≤ ε * (#A + #P.parts) ^ 2 := by
  calc
    _ ≤ ∑ UV ∈ P.sparsePairs G ε, (#(G.interedges UV.1 UV.2) : 𝕜) := mod_cast card_biUnion_le
    _ ≤ ∑ UV ∈ P.sparsePairs G ε, ε * (#UV.1 * #UV.2) := ?_
    _ ≤ ∑ UV ∈ P.parts.offDiag, ε * (#UV.1 * #UV.2) := by gcongr; apply filter_subset
    _ = ε * ∑ UV ∈ P.parts.offDiag, (#UV.1 * #UV.2 : 𝕜) := (mul_sum _ _ _).symm
    _ ≤ _ := ?_
  · gcongr with ⟨U, V⟩ hUV
    simp only [mk_mem_sparsePairs, ne_eq, ← card_interedges_div_card, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_mul] at hUV
    refine ((div_lt_iff₀ ?_).1 hUV.2.2.2).le
    exact mul_pos (Nat.cast_pos.2 (P.nonempty_of_mem_parts hUV.1).card_pos)
      (Nat.cast_pos.2 (P.nonempty_of_mem_parts hUV.2.1).card_pos)
  norm_cast
  gcongr
  calc
    (_ : ℕ) ≤ _ := sum_le_card_nsmul P.parts.offDiag (fun i ↦ #i.1 * #i.2)
            ((#A / #P.parts + 1) ^ 2 : ℕ) ?_
    _ ≤ (#P.parts * (#A / #P.parts) + #P.parts) ^ 2 := ?_
    _ ≤ _ := by gcongr; apply Nat.mul_div_le
  · simp only [Prod.forall, and_imp, mem_offDiag, sq]
    rintro U V hU hV -
    exact_mod_cast Nat.mul_le_mul (hP.card_part_le_average_add_one hU)
      (hP.card_part_le_average_add_one hV)
  · rw [smul_eq_mul, offDiag_card, Nat.mul_sub_right_distrib, ← sq, ← mul_pow, mul_add_one (α := ℕ)]
    exact Nat.sub_le _ _
/-
**Finpartition.IsEquipartition.card_interedges_sparsePairs_le** 是 Mathlib 中的一个定理
，位于命名空间 `Finpartition.IsEquipartition`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] 
[IsStrictOrderedRing 𝕜]   [inst_3 : DecidableEq α] {A : Finset α} {P : Finpartit
ion A} {G : SimpleGraph α} [inst_4 : DecidableRel G.Adj]   {ε : 𝕜},   P.IsEquipa
rtition →     0 ≤ ε →       ↑((P.sparsePairs G ε).biUnion fun x =>              
 match x with               | (U, V) => G.interedges U V).card ≤         4 * ε *
 ↑A.card ^ 2
参数：(P.sparsePairs G ε).biUnion fun x =>               match x with              
 | (U, V) => G.interedges U V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finpartition.IsEquipartition.card_interedges_sparsePairs_le'`：∀ {α : Typ
e u_1} {𝕜 : Type u_2} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrdered
Ring 𝕜]   [inst_3 : DecidableEq α] {A : Finset α} …
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `pow_le_pow_left₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 :
 Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀],   0 ≤ a → a ≤ b → ∀ (n
 : ℕ),…
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `Finpartition.card_parts_le_card`：card_parts_le_card : #P.parts <= #s
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf`：∀ {R : Type u_1} [inst : Comm
Semiring R] {a b c : R} (x : R) (e : ℕ), a + b = c → x ^ e * a + x ^ e * b = x ^
 e * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
（共 51 条，此处仅展示前 30 条）
-/
lemma IsEquipartition.card_interedges_sparsePairs_le (hP : P.IsEquipartition) (hε : 0 ≤ ε) :
    #((P.sparsePairs G ε).biUnion fun (U, V) ↦ G.interedges U V) ≤ 4 * ε * #A ^ 2 := by
  calc
    _ ≤ _ := hP.card_interedges_sparsePairs_le' hε
    _ ≤ ε * (#A + #A) ^ 2 := by gcongr; exact P.card_parts_le_card
    _ = _ := by ring
/-
**Finpartition.aux** 是 Mathlib 中的一个引理，位于命名空间 `Finpartition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma aux {i j : ℕ} (hj : 0 < j) : j * (j - 1) * (i / j + 1) ^ 2 < (i + j) ^ 2 := by
  have : j * (j - 1) < j ^ 2 := by
    rw [sq]; exact Nat.mul_lt_mul_of_pos_left (Nat.sub_lt hj zero_lt_one) hj
  apply (Nat.mul_lt_mul_of_pos_right this <| pow_pos Nat.succ_pos' _).trans_le
  rw [← mul_pow, Nat.mul_succ]
  gcongr
  apply Nat.mul_div_le
/-
**Finpartition.IsEquipartition.card_biUnion_offDiag_le'** 是 Mathlib 中的一个定理，位于命名空
间 `Finpartition.IsEquipartition`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] 
[IsStrictOrderedRing 𝕜]   [inst_3 : DecidableEq α] {A : Finset α} {P : Finpartit
ion A},   P.IsEquipartition → ↑(P.parts.biUnion Finset.offDiag).card ≤ ↑A.card *
 (↑A.card + ↑P.parts.card) / ↑P.parts.card
参数：P.parts.biUnion Finset.offDiag；↑A.card + ↑P.parts.card。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Finset.card_biUnion_le_card_mul`：card_biUnion_le_card_mul [DecidableEq β
] (s : Finset ι) (f : ι -> Finset β) (n : Nat) (h : forall a in s, #(f a) <= n) 
: #(s.biUnion f) <= #…
· 使用定理 `Finpartition.IsEquipartition.card_part_le_average_add_one`：∀ {α : Type u
_1} [inst : DecidableEq α] {s t : Finset α} {P : Finpartition s},   P.IsEquipart
ition → t ∈ P.parts → t.card ≤ s.card / P.parts…
· 使用定理 `Nat.mul_le_mul`：∀ {n₁ m₁ n₂ m₂ : ℕ}, n₁ ≤ n₂ → m₁ ≤ m₂ → n₁ * m₁ ≤ n₂ * 
m₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.sub_le_sub_right`：∀ {n m : ℕ}, n ≤ m → ∀ (k : ℕ), n - k ≤ m - k
· 使用定理 `Finset.offDiag_card`：offDiag_card : (offDiag s).card = s.card * s.card -
 s.card
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Nat.mul_sub_right_distrib`：∀ (n m k : ℕ), (n - m) * k = n * k - m * k
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Nat.mul_div_le`：∀ (m n : ℕ), n * (m / n) ≤ m
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
（共 48 条，此处仅展示前 30 条）
-/
lemma IsEquipartition.card_biUnion_offDiag_le' (hP : P.IsEquipartition) :
    (#(P.parts.biUnion offDiag) : 𝕜) ≤ #A * (#A + #P.parts) / #P.parts := by
  obtain h | h := P.parts.eq_empty_or_nonempty
  · simp [h]
  calc
    _ ≤ (#P.parts : 𝕜) * (↑(#A / #P.parts) * ↑(#A / #P.parts + 1)) :=
        mod_cast card_biUnion_le_card_mul _ _ _ fun U hU ↦ ?_
    _ = #P.parts * ↑(#A / #P.parts) * ↑(#A / #P.parts + 1) := by rw [mul_assoc]
    _ ≤ #A * (#A / #P.parts + 1) :=
        mul_le_mul (mod_cast Nat.mul_div_le _ _) ?_ (by positivity) (by positivity)
    _ = _ := by rw [← div_add_same (mod_cast h.card_pos.ne'), mul_div_assoc]
  · simpa using Nat.cast_div_le
  suffices (#U - 1) * #U ≤ #A / #P.parts * (#A / #P.parts + 1) by
    rwa [Nat.mul_sub_right_distrib, one_mul, ← offDiag_card] at this
  have := hP.card_part_le_average_add_one hU
  refine Nat.mul_le_mul ((Nat.sub_le_sub_right this 1).trans ?_) this
  simp only [Nat.add_succ_sub_one, add_zero, le_rfl]
/-
**Finpartition.IsEquipartition.card_biUnion_offDiag_le** 是 Mathlib 中的一个定理，位于命名空间
 `Finpartition.IsEquipartition`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] 
[IsStrictOrderedRing 𝕜]   [inst_3 : DecidableEq α] {A : Finset α} {P : Finpartit
ion A} {ε : 𝕜},   0 < ε → P.IsEquipartition → 4 / ε ≤ ↑P.parts.card → ↑(P.parts.
biUnion Finset.offDiag).card ≤ ε / 2 * ↑A.card ^ 2
参数：P.parts.biUnion Finset.offDiag。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finpartition.IsEquipartition.card_biUnion_offDiag_le'`：∀ {α : Type u_1} 
{𝕜 : Type u_2} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
   [inst_3 : DecidableEq α] {A : Finset α} …
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Finset.Nonempty.card_pos`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
0 < s.card
· 使用定理 `Finpartition.parts_nonempty`：parts_nonempty (P : Finpartition a) (ha : a
 != ⊥) : P.parts.Nonempty
· 使用定理 `Finset.Nonempty.ne_empty`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
s ≠ ∅
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
（共 88 条，此处仅展示前 30 条）
-/
lemma IsEquipartition.card_biUnion_offDiag_le (hε : 0 < ε) (hP : P.IsEquipartition)
    (hP' : 4 / ε ≤ #P.parts) : #(P.parts.biUnion offDiag) ≤ ε / 2 * #A ^ 2 := by
  obtain rfl | hA : A = ⊥ ∨ _ := A.eq_empty_or_nonempty
  · simp [Subsingleton.elim P ⊥]
  apply hP.card_biUnion_offDiag_le'.trans
  rw [div_le_iff₀ (Nat.cast_pos.2 (P.parts_nonempty hA.ne_empty).card_pos)]
  have : (#A : 𝕜) + #P.parts ≤ 2 * #A := by
    rw [two_mul]; gcongr; exact P.card_parts_le_card
  refine (mul_le_mul_of_nonneg_left this <| by positivity).trans ?_
  suffices 1 ≤ ε / 4 * #P.parts by
    rw [mul_left_comm, ← sq]
    convert! mul_le_mul_of_nonneg_left this (mul_nonneg zero_le_two <| sq_nonneg (#A : 𝕜)) using 1
      <;> ring
  rwa [← div_le_iff₀', one_div_div]
  positivity
/-
**Finpartition.IsEquipartition.sum_nonUniforms_lt'** 是 Mathlib 中的一个定理，位于命名空间 `Fi
npartition.IsEquipartition`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] 
[IsStrictOrderedRing 𝕜]   [inst_3 : DecidableEq α] {A : Finset α} {P : Finpartit
ion A} {G : SimpleGraph α} [inst_4 : DecidableRel G.Adj]   {ε : 𝕜},   A.Nonempty
 →     0 < ε →       P.IsEquipartition →         P.IsUniform G ε → ∑ i ∈ P.nonUn
iforms G ε, ↑i.1.card * ↑i.2.card < ε * (↑A.card + ↑P.parts.card) ^ 2
参数：↑A.card + ↑P.parts.card。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_le_card_nsmul`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCom
mMonoid N] [inst_1 : Preorder N] [AddLeftMono N] (s : Finset ι)   (f : ι → N) (n
 : N), (∀ x ∈ …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Nat.mul_le_mul`：∀ {n₁ m₁ n₂ m₂ : ℕ}, n₁ ≤ n₂ → m₁ ≤ m₂ → n₁ * m₁ ≤ n₂ * 
m₂
· 使用定理 `Finpartition.IsEquipartition.card_part_le_average_add_one`：∀ {α : Type u
_1} [inst : DecidableEq α] {s t : Finset α} {P : Finpartition s},   P.IsEquipart
ition → t ∈ P.parts → t.card ≤ s.card / P.parts…
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Right.add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α]
 [inst_1 : Preorder α] [AddRightMono α] {a b : α}, 0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 40 条，此处仅展示前 30 条）
-/
lemma IsEquipartition.sum_nonUniforms_lt' (hA : A.Nonempty) (hε : 0 < ε) (hP : P.IsEquipartition)
    (hG : P.IsUniform G ε) :
    ∑ i ∈ P.nonUniforms G ε, (#i.1 * #i.2 : 𝕜) < ε * (#A + #P.parts) ^ 2 := by
  calc
    _ ≤ #(P.nonUniforms G ε) • (↑(#A / #P.parts + 1) : 𝕜) ^ 2 :=
      sum_le_card_nsmul _ _ _ ?_
    _ = _ := nsmul_eq_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hG <| by positivity
    _ < _ := ?_
  · simp only [Prod.forall, Finpartition.mk_mem_nonUniforms, and_imp]
    rintro U V hU hV - -
    rw [sq, ← Nat.cast_mul, ← Nat.cast_mul, Nat.cast_le]
    exact Nat.mul_le_mul (hP.card_part_le_average_add_one hU)
      (hP.card_part_le_average_add_one hV)
  · rw [mul_right_comm _ ε, mul_comm ε]
    gcongr
    norm_cast
    exact aux (P.parts_nonempty hA.ne_empty).card_pos
/-
**Finpartition.IsEquipartition.sum_nonUniforms_lt** 是 Mathlib 中的一个定理，位于命名空间 `Fin
partition.IsEquipartition`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] 
[IsStrictOrderedRing 𝕜]   [inst_3 : DecidableEq α] {A : Finset α} {P : Finpartit
ion A} {G : SimpleGraph α} [inst_4 : DecidableRel G.Adj]   {ε : 𝕜},   A.Nonempty
 →     0 < ε →       P.IsEquipartition →         P.IsUniform G ε →           ↑((
P.nonUniforms G ε).biUnion fun x =>                   match x with              
     | (U, V) => U ×ˢ V).card <             4 * ε * ↑A.card ^ 2
参数：(P.nonUniforms G ε).biUnion fun x =>                   match x with          
         | (U, V) => U ×ˢ V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Finset.card_biUnion_le`：card_biUnion_le [DecidableEq M] {s : Finset ι} {
t : ι -> Finset M} : #(s.biUnion t) <= ∑ a in s, #(t a)
· 使用定理 `Finpartition.IsEquipartition.sum_nonUniforms_lt'`：∀ {α : Type u_1} {𝕜 : 
Type u_2} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]   [i
nst_3 : DecidableEq α] {A : Finset α} …
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `pow_le_pow_left₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 :
 Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀],   0 ≤ a → a ≤ b → ∀ (n
 : ℕ),…
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Finset.Nonempty.card_pos`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
0 < s.card
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `Finpartition.card_parts_le_card`：card_parts_le_card : #P.parts <= #s
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
（共 59 条，此处仅展示前 30 条）
-/
lemma IsEquipartition.sum_nonUniforms_lt (hA : A.Nonempty) (hε : 0 < ε) (hP : P.IsEquipartition)
    (hG : P.IsUniform G ε) :
    #((P.nonUniforms G ε).biUnion fun (U, V) ↦ U ×ˢ V) < 4 * ε * #A ^ 2 := by
  calc
    _ ≤ ∑ i ∈ P.nonUniforms G ε, (#i.1 * #i.2 : 𝕜) := by
        norm_cast; simp_rw [← card_product]; exact card_biUnion_le
    _ < _ := hP.sum_nonUniforms_lt' hA hε hG
    _ ≤ ε * (#A + #A) ^ 2 := by gcongr; exact P.card_parts_le_card
    _ = _ := by ring

end Finpartition

/-! ### Reduced graph -/

namespace SimpleGraph

/-- The reduction of the graph `G` along partition `P` has edges between `ε`-uniform pairs of parts
that have edge density at least `δ`. -/
/-
**SimpleGraph.regularityReduced** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：{α : Type u_1} →   {𝕜 : Type u_2} →     [Field 𝕜] →       [LinearOrder 𝕜] 
→         [inst : DecidableEq α] →           {A : Finset α} → Finpartition A → (
G : SimpleGraph α) → [DecidableRel G.Adj] → 𝕜 → 𝕜 → SimpleGraph α
参数：G : SimpleGraph α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The reduction of the graph `G` along partition `P` has edges between `ε`-uniform
 pairs of parts
that have edge density at least `δ`.
-/
@[simps] def regularityReduced (ε δ : 𝕜) : SimpleGraph α where
  Adj a b := G.Adj a b ∧
    ∃ U ∈ P.parts, ∃ V ∈ P.parts, a ∈ U ∧ b ∈ V ∧ U ≠ V ∧ G.IsUniform ε U V ∧ δ ≤ G.edgeDensity U V
  symm.symm a b := by
    rintro ⟨ab, U, UP, V, VP, xU, yV, UV, GUV, εUV⟩
    refine ⟨ab.symm, V, VP, U, UP, yV, xU, UV.symm, GUV.symm, ?_⟩
    rwa [edgeDensity_comm]
/-
**SimpleGraph.regularityReduced.instDecidableRel_adj** 是 Mathlib 中的一个定义，位于命名空间 `
SimpleGraph.regularityReduced`。
形式化陈述：{α : Type u_1} →   {𝕜 : Type u_2} →     [inst : Field 𝕜] →       [inst_1 :
 LinearOrder 𝕜] →         [inst_2 : DecidableEq α] →           {A : Finset α} → 
            (P : Finpartition A) →               (G : SimpleGraph α) →          
       [inst_3 : DecidableRel G.Adj] → {ε δ : 𝕜} → DecidableRel (SimpleGraph.reg
ularityReduced P G ε δ).Adj
参数：P : Finpartition A；G : SimpleGraph α；SimpleGraph.regularityReduced P G ε δ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance regularityReduced.instDecidableRel_adj : DecidableRel (G.regularityReduced P ε δ).Adj :=
  inferInstanceAs <| DecidableRel (mk _ _).Adj

variable {G P}

omit [IsStrictOrderedRing 𝕜] in
/-
**SimpleGraph.regularityReduced_le** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：regularityReduced_le : G.regularityReduced P ε δ <= G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma regularityReduced_le : G.regularityReduced P ε δ ≤ G := fun _ _ ↦ And.left
/-
**SimpleGraph.regularityReduced_mono** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：regularityReduced_mono {ε₁ ε₂ : 𝕜} (hε : ε₁ <= ε₂) : G.regularityReduced P
 ε₁ δ <= G.regularityReduced P ε₂ δ
参数：hε : ε₁ <= ε₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsUniform.mono`：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : Fiel
d 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {G : SimpleGraph α}   [ins
t_3 : DecidableR…
-/
lemma regularityReduced_mono {ε₁ ε₂ : 𝕜} (hε : ε₁ ≤ ε₂) :
    G.regularityReduced P ε₁ δ ≤ G.regularityReduced P ε₂ δ :=
  fun _a _b ⟨hab, U, hU, V, hV, ha, hb, hUV, hGε, hGδ⟩ ↦
    ⟨hab, U, hU, V, hV, ha, hb, hUV, hGε.mono hε, hGδ⟩

omit [IsStrictOrderedRing 𝕜] in
/-
**SimpleGraph.regularityReduced_anti** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：regularityReduced_anti {δ₁ δ₂ : 𝕜} (hδ : δ₁ <= δ₂) : G.regularityReduced P
 ε δ₂ <= G.regularityReduced P ε δ₁
参数：hδ : δ₁ <= δ₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma regularityReduced_anti {δ₁ δ₂ : 𝕜} (hδ : δ₁ ≤ δ₂) :
    G.regularityReduced P ε δ₂ ≤ G.regularityReduced P ε δ₁ :=
  fun _a _b ⟨hab, U, hU, V, hV, ha, hb, hUV, hUVε, hUVδ⟩ ↦
    ⟨hab, U, hU, V, hV, ha, hb, hUV, hUVε, hδ.trans hUVδ⟩

omit [IsStrictOrderedRing 𝕜] in
/-
**SimpleGraph.unreduced_edges_subset** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：unreduced_edges_subset : (A ×ˢ A).filter (fun (x, y) => G.Adj x y ∧ ¬ (G.r
egularityReduced P (ε / 8) (ε / 4)).Adj x y) subseteq (P.nonUniforms G (ε / 8)).
biUnion (fun (U, V) => U ×ˢ V) union P.parts.biUnion offDiag union (P.sparsePair
s G (ε / 4)).biUnion fun (U, V) => G.interedges U V
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `SimpleGraph.regularityReduced_adj`：∀ {α : Type u_1} {𝕜 : Type u_2} [inst
 : Field 𝕜] [inst_1 : LinearOrder 𝕜] [inst_2 : DecidableEq α] {A : Finset α}   (
P : Finpartition A) (G …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finpartition.mk_mem_nonUniforms`：∀ {α : Type u_1} {𝕜 : Type u_2} [inst :
 Field 𝕜] [inst_1 : LinearOrder 𝕜] [inst_2 : DecidableEq α] {A : Finset α}   (P 
: Finpartition A) (G …
· 使用定理 `Finpartition.exists_mem`：exists_mem (ha : a in s) : exists t in P.parts,
 a in t
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `SimpleGraph.ne_of_adj`：ne_of_adj (h : G.Adj a b) : a != b
-/
lemma unreduced_edges_subset :
    (A ×ˢ A).filter (fun (x, y) ↦ G.Adj x y ∧ ¬ (G.regularityReduced P (ε / 8) (ε / 4)).Adj x y) ⊆
      (P.nonUniforms G (ε / 8)).biUnion (fun (U, V) ↦ U ×ˢ V) ∪ P.parts.biUnion offDiag ∪
        (P.sparsePairs G (ε / 4)).biUnion fun (U, V) ↦ G.interedges U V := by
  rintro ⟨x, y⟩
  simp only [mem_filter, regularityReduced_adj, not_and, not_exists,
    not_le, mem_biUnion, mem_union, mem_product, Prod.exists, mem_offDiag, and_imp,
    or_assoc, and_assoc, P.mk_mem_nonUniforms, Finpartition.mk_mem_sparsePairs, mem_interedges_iff]
  intro hx hy h h'
  replace h' := h' h
  obtain ⟨U, hU, hx⟩ := P.exists_mem hx
  obtain ⟨V, hV, hy⟩ := P.exists_mem hy
  obtain rfl | hUV := eq_or_ne U V
  · exact Or.inr (Or.inl ⟨U, hU, hx, hy, G.ne_of_adj h⟩)
  by_cases h₂ : G.IsUniform (ε / 8) U V
  · exact Or.inr <| Or.inr ⟨U, V, hU, hV, hUV, h' _ hU _ hV hx hy hUV h₂, hx, hy, h⟩
  · exact Or.inl ⟨U, V, hU, hV, hUV, h₂, hx, hy⟩

end SimpleGraph

