/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Group.Indicator
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Ordered
public import Mathlib.Topology.Algebra.Affine
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.GDelta.Basic

/-!
# Urysohn's lemma

In this file we prove Urysohn's lemma `exists_continuous_zero_one_of_isClosed`: for any two disjoint
closed sets `s` and `t` in a normal topological space `X` there exists a continuous function
`f : X → ℝ` such that

* `f` equals zero on `s`;
* `f` equals one on `t`;
* `0 ≤ f x ≤ 1` for all `x`.

We also give versions in a regular locally compact space where one assumes that `s` is compact
and `t` is closed, in `exists_continuous_zero_one_of_isCompact`
and `exists_continuous_one_zero_of_isCompact` (the latter providing additionally a function with
compact support).

We write a generic proof so that it applies both to normal spaces and to regular locally
compact spaces.

## Implementation notes

Most paper sources prove Urysohn's lemma using a family of open sets indexed by dyadic rational
numbers on `[0, 1]`. There are many technical difficulties with formalizing this proof (e.g., one
needs to formalize the "dyadic induction", then prove that the resulting family of open sets is
monotone). So, we formalize a slightly different proof.

Let `Urysohns.CU` be the type of pairs `(C, U)` of a closed set `C` and an open set `U` such that
`C ⊆ U`. Since `X` is a normal topological space, for each `c : CU` there exists an open set `u`
such that `c.C ⊆ u ∧ closure u ⊆ c.U`. We define `c.left` and `c.right` to be `(c.C, u)` and
`(closure u, c.U)`, respectively. Then we define a family of functions
`Urysohns.CU.approx (c : Urysohns.CU) (n : ℕ) : X → ℝ` by recursion on `n`:

* `c.approx 0` is the indicator of `c.Uᶜ`;
* `c.approx (n + 1) x = (c.left.approx n x + c.right.approx n x) / 2`.

For each `x` this is a monotone family of functions that are equal to zero on `c.C` and are equal to
one outside of `c.U`. We also have `c.approx n x ∈ [0, 1]` for all `c`, `n`, and `x`.

Let `Urysohns.CU.lim c` be the supremum (or equivalently, the limit) of `c.approx n`. Then
properties of `Urysohns.CU.approx` immediately imply that

* `c.lim x ∈ [0, 1]` for all `x`;
* `c.lim` equals zero on `c.C` and equals one outside of `c.U`;
* `c.lim x = (c.left.lim x + c.right.lim x) / 2`.

In order to prove that `c.lim` is continuous at `x`, we prove by induction on `n : ℕ` that for `y`
in a small neighborhood of `x` we have `|c.lim y - c.lim x| ≤ (3 / 4) ^ n`. Induction base follows
from `c.lim x ∈ [0, 1]`, `c.lim y ∈ [0, 1]`. For the induction step, consider two cases:

* `x ∈ c.left.U`; then for `y` in a small neighborhood of `x` we have `y ∈ c.left.U ⊆ c.right.C`
  (hence `c.right.lim x = c.right.lim y = 0`) and `|c.left.lim y - c.left.lim x| ≤ (3 / 4) ^ n`.
  Then
  `|c.lim y - c.lim x| = |c.left.lim y - c.left.lim x| / 2 ≤ (3 / 4) ^ n / 2 < (3 / 4) ^ (n + 1)`.
* otherwise, `x ∉ c.left.right.C`; then for `y` in a small neighborhood of `x` we have
  `y ∉ c.left.right.C ⊇ c.left.left.U` (hence `c.left.left.lim x = c.left.left.lim y = 1`),
  `|c.left.right.lim y - c.left.right.lim x| ≤ (3 / 4) ^ n`, and
  `|c.right.lim y - c.right.lim x| ≤ (3 / 4) ^ n`. Combining these inequalities, the triangle
  inequality, and the recurrence formula for `c.lim`, we get
  `|c.lim x - c.lim y| ≤ (3 / 4) ^ (n + 1)`.

The actual formalization uses `midpoint ℝ x y` instead of `(x + y) / 2` because we have more API
lemmas about `midpoint`.

## Tags

Urysohn's lemma, normal topological space, locally compact topological space
-/

@[expose] public noncomputable section


variable {X : Type*} [TopologicalSpace X]

open Set Filter TopologicalSpace Topology Filter
open scoped Pointwise

namespace Urysohns


/--
An auxiliary type for the proof of Urysohn's lemma: a pair of a closed set `C` and its open
neighborhood `U`, together with the assumption that `C` and `U` satisfy the property `P C U`.
The latter assumption will make it possible to prove simultaneously both versions of Urysohn's
lemma, in normal spaces (with `P` always true) and in locally compact spaces
(with `P C U = IsCompact C`). We put also in the structure the assumption that, for any such pair,
one may find an intermediate pair in between satisfying `P`,
to avoid carrying it around in the argument.
-/
/-
**Urysohns.CU** 是 Mathlib 中的一个归纳类型，位于命名空间 `Urysohns`。
形式化陈述：{X : Type u_2} → [TopologicalSpace X] → (Set X → Set X → Prop) → Type u_2
参数：Set X → Set X → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary type for the proof of Urysohn's lemma: a pair of a closed set `C` a
nd its open
neighborhood `U`, together with the assumption that `C` and `U` satisfy the prop
erty `P C U`.
The latter assumption will make it possible to prove simultaneously both version
s of Urysohn's
lemma, in normal spaces (with `P` always true) and in locally compact spaces
(with `P C U = IsCompact C`). We put also in the structure the assumption that, 
for any such pair,
one may find an intermediate pair in between satisfying `P`,
to avoid carrying it around in the argument.
-/
structure CU {X : Type*} [TopologicalSpace X] (P : Set X → Set X → Prop) where
  /-- The inner set in the inductive construction towards Urysohn's lemma -/
  protected C : Set X
  /-- The outer set in the inductive construction towards Urysohn's lemma -/
  protected U : Set X
  /-- The proof that `C` and `U` satisfy the property `P C U` -/
  protected P_C_U : P C U
  protected closed_C : IsClosed C
  protected open_U : IsOpen U
  protected subset : C ⊆ U
  /-- The proof that we can divide `CU` pairs in half -/
  protected hP : ∀ {c u : Set X}, IsClosed c → P c u → IsOpen u → c ⊆ u →
    ∃ (v : Set X), IsOpen v ∧ c ⊆ v ∧ closure v ⊆ u ∧ P c v ∧ P (closure v) u

namespace CU

variable {P : Set X → Set X → Prop}

/-- By assumption, for each `c : CU P` there exists an open set `u`
such that `c.C ⊆ u` and `closure u ⊆ c.U`. `c.left` is the pair `(c.C, u)`. -/
@[simps C]
/-
**Urysohns.CU.left** 是 Mathlib 中的一个定义，位于命名空间 `Urysohns.CU`。
形式化陈述：left (c : CU P) : CU P where C
参数：c : CU P。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Urysohns.CU.closed_C`：∀ {X : Type u_2} [inst : TopologicalSpace X] {P : 
Set X → Set X → Prop} (self : Urysohns.CU P), IsClosed self.C
· 使用定理 `Urysohns.CU.hP`：∀ {X : Type u_2} [inst : TopologicalSpace X] {P : Set X 
→ Set X → Prop} (self : Urysohns.CU P) {c u : Set X},   IsClosed c → P c u → IsO
pen …

--- 原说明 ---
By assumption, for each `c : CU P` there exists an open set `u`
such that `c.C ⊆ u` and `closure u ⊆ c.U`. `c.left` is the pair `(c.C, u)`.
-/
def left (c : CU P) : CU P where
  C := c.C
  U := (c.hP c.closed_C c.P_C_U c.open_U c.subset).choose
  closed_C := c.closed_C
  P_C_U := (c.hP c.closed_C c.P_C_U c.open_U c.subset).choose_spec.2.2.2.1
  open_U := (c.hP c.closed_C c.P_C_U c.open_U c.subset).choose_spec.1
  subset := (c.hP c.closed_C c.P_C_U c.open_U c.subset).choose_spec.2.1
  hP := c.hP

/-- By assumption, for each `c : CU P` there exists an open set `u`
such that `c.C ⊆ u` and `closure u ⊆ c.U`. `c.right` is the pair `(closure u, c.U)`. -/
@[simps U]
/-
**Urysohns.CU.right** 是 Mathlib 中的一个定义，位于命名空间 `Urysohns.CU`。
形式化陈述：right (c : CU P) : CU P where C
参数：c : CU P。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Urysohns.CU.open_U`：∀ {X : Type u_2} [inst : TopologicalSpace X] {P : Se
t X → Set X → Prop} (self : Urysohns.CU P), IsOpen self.U
· 使用定理 `Urysohns.CU.hP`：∀ {X : Type u_2} [inst : TopologicalSpace X] {P : Set X 
→ Set X → Prop} (self : Urysohns.CU P) {c u : Set X},   IsClosed c → P c u → IsO
pen …

--- 原说明 ---
By assumption, for each `c : CU P` there exists an open set `u`
such that `c.C ⊆ u` and `closure u ⊆ c.U`. `c.right` is the pair `(closure u, c.
U)`.
-/
def right (c : CU P) : CU P where
  C := closure (c.hP c.closed_C c.P_C_U c.open_U c.subset).choose
  U := c.U
  closed_C := isClosed_closure
  P_C_U := (c.hP c.closed_C c.P_C_U c.open_U c.subset).choose_spec.2.2.2.2
  open_U := c.open_U
  subset := (c.hP c.closed_C c.P_C_U c.open_U c.subset).choose_spec.2.2.1
  hP := c.hP
/-
**Urysohns.CU.left_U_subset_right_C** 是 Mathlib 中的一个定理，位于命名空间 `Urysohns.CU`。
形式化陈述：left_U_subset_right_C (c : CU P) : c.left.U subseteq c.right.C
参数：c : CU P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem left_U_subset_right_C (c : CU P) : c.left.U ⊆ c.right.C :=
  subset_closure
/-
**Urysohns.CU.left_U_subset** 是 Mathlib 中的一个定理，位于命名空间 `Urysohns.CU`。
形式化陈述：left_U_subset (c : CU P) : c.left.U subseteq c.U
参数：c : CU P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Urysohns.CU.left_U_subset_right_C`：left_U_subset_right_C (c : CU P) : c.
left.U subseteq c.right.C
· 使用定理 `Urysohns.CU.subset`：∀ {X : Type u_2} [inst : TopologicalSpace X] {P : Se
t X → Set X → Prop} (self : Urysohns.CU P), self.C ⊆ self.U
-/
theorem left_U_subset (c : CU P) : c.left.U ⊆ c.U :=
  Subset.trans c.left_U_subset_right_C c.right.subset
/-
**Urysohns.CU.subset_right_C** 是 Mathlib 中的一个定理，位于命名空间 `Urysohns.CU`。
形式化陈述：subset_right_C (c : CU P) : c.C subseteq c.right.C
参数：c : CU P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Urysohns.CU.subset`：∀ {X : Type u_2} [inst : TopologicalSpace X] {P : Se
t X → Set X → Prop} (self : Urysohns.CU P), self.C ⊆ self.U
· 使用定理 `Urysohns.CU.left_U_subset_right_C`：left_U_subset_right_C (c : CU P) : c.
left.U subseteq c.right.C
-/
theorem subset_right_C (c : CU P) : c.C ⊆ c.right.C :=
  Subset.trans c.left.subset c.left_U_subset_right_C

/-- `n`-th approximation to a continuous function `f : X → ℝ` such that `f = 0` on `c.C` and `f = 1`
outside of `c.U`. -/
/-
**Urysohns.CU.approx** 是 Mathlib 中的一个定义，位于命名空间 `Urysohns.CU`。
形式化陈述：{X : Type u_1} → [inst : TopologicalSpace X] → {P : Set X → Set X → Prop} 
→ ℕ → Urysohns.CU P → X → ℝ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`n`-th approximation to a continuous function `f : X → ℝ` such that `f = 0` on `
c.C` and `f = 1`
outside of `c.U`.
-/
def approx : ℕ → CU P → X → ℝ
  | 0, c, x => indicator c.Uᶜ 1 x
  | n + 1, c, x => midpoint ℝ (approx n c.left x) (approx n c.right x)
/-
**Urysohns.CU.approx_of_mem_C** 是 Mathlib 中的一个定理，位于命名空间 `Urysohns.CU`。
形式化陈述：approx_of_mem_C (c : CU P) (n : Nat) {x : X} (hx : x in c.C) : c.approx n 
x = 0
参数：c : CU P；n : Nat；hx : x in c.C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `Urysohns.CU.subset`：∀ {X : Type u_2} [inst : TopologicalSpace X] {P : Se
t X → Set X → Prop} (self : Urysohns.CU P), self.C ⊆ self.U
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Urysohns.CU.subset_right_C`：subset_right_C (c : CU P) : c.C subseteq c.r
ight.C
· 使用定理 `midpoint_self`：midpoint_self (x : P) : midpoint R x x = x
-/
theorem approx_of_mem_C (c : CU P) (n : ℕ) {x : X} (hx : x ∈ c.C) : c.approx n x = 0 := by
  induction n generalizing c with
  | zero => exact indicator_of_notMem (fun (hU : x ∈ c.Uᶜ) => hU <| c.subset hx) _
  | succ n ihn =>
    simp only [approx]
    rw [ihn, ihn, midpoint_self]
    exacts [c.subset_right_C hx, hx]
/-
**Urysohns.CU.approx_of_notMem_U** 是 Mathlib 中的一个定理，位于命名空间 `Urysohns.CU`。
形式化陈述：approx_of_notMem_U (c : CU P) (n : Nat) {x : X} (hx : x ∉ c.U) : c.approx 
n x = 1
参数：c : CU P；n : Nat；hx : x ∉ c.U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `Urysohns.CU.left_U_subset`：left_U_subset (c : CU P) : c.left.U subseteq 
c.U
· 使用定理 `midpoint_self`：midpoint_self (x : P) : midpoint R x x = x
-/
theorem approx_of_notMem_U (c : CU P) (n : ℕ) {x : X} (hx : x ∉ c.U) : c.approx n x = 1 := by
  induction n generalizing c with
  | zero =>
    rw [← mem_compl_iff] at hx
    exact indicator_of_mem hx _
  | succ n ihn =>
    simp only [approx]
    rw [ihn, ihn, midpoint_self]
    exacts [hx, fun hU => hx <| c.left_U_subset hU]
/-
**Urysohns.CU.approx_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Urysohns.CU`。
形式化陈述：approx_nonneg (c : CU P) (n : Nat) (x : X) : 0 <= c.approx n x
参数：c : CU P；n : Nat；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.indicator_nonneg`：∀ {α : Type u_2} {M : Type u_3} [inst : Preorder M
] [inst_1 : Zero M] {s : Set α} {f : α → M},   (∀ a ∈ s, 0 ≤ f a) → ∀ (a : α), 0
 ≤ s.indic…
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `midpoint_eq_smul_add`：midpoint_eq_smul_add (x y : V) : midpoint R x y = 
(⅟2 : R) • (x + y)
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Partia
lOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a⁻¹ ↔ 0 ≤ a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `zero_le_two`：zero_le_two [Preorder α] [ZeroLEOneClass α] [AddLeftMono α]
 : (0 : α) <= 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
-/
theorem approx_nonneg (c : CU P) (n : ℕ) (x : X) : 0 ≤ c.approx n x := by
  induction n generalizing c with
  | zero => exact indicator_nonneg (fun _ _ => zero_le_one) _
  | succ n ihn =>
    simp only [approx, midpoint_eq_smul_add]
    refine mul_nonneg (inv_nonneg.2 zero_le_two) (add_nonneg ?_ ?_) <;> apply ihn
/-
**Urysohns.CU.approx_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Urysohns.CU`。
形式化陈述：approx_le_one (c : CU P) (n : Nat) (x : X) : c.approx n x <= 1
参数：c : CU P；n : Nat；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.indicator_apply_le'`：∀ {α : Type u_2} {M : Type u_3} [inst : LE M] [
inst_1 : Zero M] {s : Set α} {f : α → M} {a : α} {y : M},   (a ∈ s → f a ≤ y) → 
(a ∉ s → 0 ≤ …
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `midpoint_eq_smul_add`：midpoint_eq_smul_add (x y : V) : midpoint R x y = 
(⅟2 : R) • (x + y)
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `div_le_one`：div_le_one (hb : 0 < b) : a / b <= 1 ↔ a <= b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem approx_le_one (c : CU P) (n : ℕ) (x : X) : c.approx n x ≤ 1 := by
  induction n generalizing c with
  | zero => exact indicator_apply_le' (fun _ => le_rfl) fun _ => zero_le_one
  | succ n ihn =>
    simp only [approx, midpoint_eq_smul_add, invOf_eq_inv, smul_eq_mul, ← div_eq_inv_mul]
    have := add_le_add (ihn (left c)) (ihn (right c))
    norm_num at this
    exact Iff.mpr (div_le_one zero_lt_two) this
/-
**Urysohns.CU.bddAbove_range_approx** 是 Mathlib 中的一个定理，位于命名空间 `Urysohns.CU`。
形式化陈述：bddAbove_range_approx (c : CU P) (x : X) : BddAbove (range fun n => c.appr
ox n x)
参数：c : CU P；x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Urysohns.CU.approx_le_one`：approx_le_one (c : CU P) (n : Nat) (x : X) : 
c.approx n x <= 1
-/
theorem bddAbove_range_approx (c : CU P) (x : X) : BddAbove (range fun n => c.approx n x) :=
  ⟨1, fun _ ⟨n, hn⟩ => hn ▸ c.approx_le_one n x⟩
/-
**Urysohns.CU.approx_le_approx_of_U_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Urysohns.CU
`。
形式化陈述：approx_le_approx_of_U_sub_C {c₁ c₂ : CU P} (h : c₁.U subseteq c₂.C) (n₁ n₂
 : Nat) (x : X) : c₂.approx n₂ x <= c₁.approx n₁ x
参数：h : c₁.U subseteq c₂.C；n₁ n₂ : Nat；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Urysohns.CU.approx_of_mem_C`：approx_of_mem_C (c : CU P) (n : Nat) {x : X
} (hx : x in c.C) : c.approx n x = 0
· 使用定理 `Urysohns.CU.approx_nonneg`：approx_nonneg (c : CU P) (n : Nat) (x : X) : 
0 <= c.approx n x
· 使用定理 `Urysohns.CU.approx_le_one`：approx_le_one (c : CU P) (n : Nat) (x : X) : 
c.approx n x <= 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Urysohns.CU.approx_of_notMem_U`：approx_of_notMem_U (c : CU P) (n : Nat) 
{x : X} (hx : x ∉ c.U) : c.approx n x = 1
-/
theorem approx_le_approx_of_U_sub_C {c₁ c₂ : CU P} (h : c₁.U ⊆ c₂.C) (n₁ n₂ : ℕ) (x : X) :
    c₂.approx n₂ x ≤ c₁.approx n₁ x := by
  by_cases hx : x ∈ c₁.U
  · calc
      approx n₂ c₂ x = 0 := approx_of_mem_C _ _ (h hx)
      _ ≤ approx n₁ c₁ x := approx_nonneg _ _ _
  · calc
      approx n₂ c₂ x ≤ 1 := approx_le_one _ _ _
      _ = approx n₁ c₁ x := (approx_of_notMem_U _ _ hx).symm
/-
**Urysohns.CU.approx_mem_Icc_right_left** 是 Mathlib 中的一个定理，位于命名空间 `Urysohns.CU`。
形式化陈述：approx_mem_Icc_right_left (c : CU P) (n : Nat) (x : X) : c.approx n x in I
cc (c.right.approx n x) (c.left.approx n x)
参数：c : CU P；n : Nat；x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Set.indicator_le_indicator_apply_of_subset`：∀ {α : Type u_2} {M : Type u
_3} [inst : Preorder M] [inst_1 : Zero M] {s t : Set α} {f : α → M} {a : α},   s
 ⊆ t → 0 ≤ f a → s.indicator f a…
· 使用定理 `compl_le_compl`：compl_le_compl (h : a <= b) : bᶜ <= aᶜ
· 使用定理 `Urysohns.CU.left_U_subset`：left_U_subset (c : CU P) : c.left.U subseteq 
c.U
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.one_apply`：one_apply (i : ι) : (1 : forall i, M i) i = 1
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `midpoint_le_midpoint`：midpoint_le_midpoint [Invertible (2 : k)] (ha : a 
<= a') (hb : b <= b') : midpoint k a b <= midpoint k a' b'
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `Urysohns.CU.approx_le_approx_of_U_sub_C`：approx_le_approx_of_U_sub_C {c₁
 c₂ : CU P} (h : c₁.U subseteq c₂.C) (n₁ n₂ : Nat) (x : X) : c₂.approx n₂ x <= c
₁.approx n₁ x
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem approx_mem_Icc_right_left (c : CU P) (n : ℕ) (x : X) :
    c.approx n x ∈ Icc (c.right.approx n x) (c.left.approx n x) := by
  induction n generalizing c with
  | zero =>
    simp only [approx]
    refine ⟨le_rfl, ?_⟩
    grw [left_U_subset]
    rw [Pi.one_apply]; positivity -- TODO: `positivity` doesn't prove that `1 x` is nonnegative
  | succ n ihn =>
    simp only [approx, mem_Icc]
    refine ⟨midpoint_le_midpoint ?_ (ihn _).1, midpoint_le_midpoint (ihn _).2 ?_⟩ <;>
      apply approx_le_approx_of_U_sub_C
    exacts [subset_closure, subset_closure]
/-
**Urysohns.CU.approx_le_succ** 是 Mathlib 中的一个定理，位于命名空间 `Urysohns.CU`。
形式化陈述：approx_le_succ (c : CU P) (n : Nat) (x : X) : c.approx n x <= c.approx (n 
+ 1) x
参数：c : CU P；n : Nat；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Urysohns.CU.right_U`：∀ {X : Type u_1} [inst : TopologicalSpace X] {P : S
et X → Set X → Prop} (c : Urysohns.CU P), c.right.U = c.U
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Urysohns.CU.approx_mem_Icc_right_left`：approx_mem_Icc_right_left (c : CU
 P) (n : Nat) (x : X) : c.approx n x in Icc (c.right.approx n x) (c.left.approx 
n x)
· 使用定理 `Urysohns.CU.approx.eq_2`：∀ {X : Type u_1} [inst : TopologicalSpace X] {P
 : Set X → Set X → Prop} (x : Urysohns.CU P) (x_1 : X) (n : ℕ),   Urysohns.CU.ap
prox n.succ x…
· 使用定理 `midpoint_le_midpoint`：midpoint_le_midpoint [Invertible (2 : k)] (ha : a 
<= a') (hb : b <= b') : midpoint k a b <= midpoint k a' b'
-/
theorem approx_le_succ (c : CU P) (n : ℕ) (x : X) : c.approx n x ≤ c.approx (n + 1) x := by
  induction n generalizing c with
  | zero =>
    simp only [approx, right_U, right_le_midpoint]
    exact (approx_mem_Icc_right_left c 0 x).2
  | succ n ihn =>
    rw [approx, approx]
    exact midpoint_le_midpoint (ihn _) (ihn _)
/-
**Urysohns.CU.approx_mono** 是 Mathlib 中的一个定理，位于命名空间 `Urysohns.CU`。
形式化陈述：approx_mono (c : CU P) (x : X) : Monotone fun n => c.approx n x
参数：c : CU P；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `monotone_nat_of_le_succ`：monotone_nat_of_le_succ {f : Nat -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
· 使用定理 `Urysohns.CU.approx_le_succ`：approx_le_succ (c : CU P) (n : Nat) (x : X) 
: c.approx n x <= c.approx (n + 1) x
-/
theorem approx_mono (c : CU P) (x : X) : Monotone fun n => c.approx n x :=
  monotone_nat_of_le_succ fun n => c.approx_le_succ n x

/-- A continuous function `f : X → ℝ` such that

* `0 ≤ f x ≤ 1` for all `x`;
* `f` equals zero on `c.C` and equals one outside of `c.U`;
-/
/-
**Urysohns.CU.lim** 是 Mathlib 中的一个定义，位于命名空间 `Urysohns.CU`。
形式化陈述：{X : Type u_1} → [inst : TopologicalSpace X] → {P : Set X → Set X → Prop} 
→ Urysohns.CU P → X → ℝ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous function `f : X → ℝ` such that

* `0 ≤ f x ≤ 1` for all `x`;
* `f` equals zero on `c.C` and equals one outside of `c.U`;
-/
protected def lim (c : CU P) (x : X) : ℝ :=
  ⨆ n, c.approx n x
/-
**Urysohns.CU.tendsto_approx_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Urysohns.CU`。
形式化陈述：tendsto_approx_atTop (c : CU P) (x : X) : Tendsto (fun n => c.approx n x) 
atTop (𝓝 <| c.lim x)
参数：c : CU P；x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_atTop_ciSup`：tendsto_atTop_ciSup (h_mono : Monotone f) (hbdd : B
ddAbove <| range f) : Tendsto f atTop (𝓝 (⨆ i, f i))
· 使用定理 `LinearOrder.supConvergenceClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : LinearOrder α] [OrderTopology α], SupConvergenceClass α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Urysohns.CU.approx_mono`：approx_mono (c : CU P) (x : X) : Monotone fun n
 => c.approx n x
· 使用定理 `Urysohns.CU.approx_le_one`：approx_le_one (c : CU P) (n : Nat) (x : X) : 
c.approx n x <= 1
-/
theorem tendsto_approx_atTop (c : CU P) (x : X) :
    Tendsto (fun n => c.approx n x) atTop (𝓝 <| c.lim x) :=
  tendsto_atTop_ciSup (c.approx_mono x) ⟨1, fun _ ⟨_, hn⟩ => hn ▸ c.approx_le_one _ _⟩
/-
**Urysohns.CU.lim_of_mem_C** 是 Mathlib 中的一个定理，位于命名空间 `Urysohns.CU`。
形式化陈述：lim_of_mem_C (c : CU P) (x : X) (h : x in c.C) : c.lim x = 0
参数：c : CU P；x : X；h : x in c.C。
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
· 使用定理 `Urysohns.CU.approx_of_mem_C`：approx_of_mem_C (c : CU P) (n : Nat) {x : X
} (hx : x in c.C) : c.approx n x = 0
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lim_of_mem_C (c : CU P) (x : X) (h : x ∈ c.C) : c.lim x = 0 := by
  simp only [CU.lim, approx_of_mem_C, h, ciSup_const]
/-
**Urysohns.CU.disjoint_C_support_lim** 是 Mathlib 中的一个定理，位于命名空间 `Urysohns.CU`。
形式化陈述：disjoint_C_support_lim (c : CU P) : Disjoint c.C (Function.support c.lim)
参数：c : CU P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.disjoint_support_iff`：∀ {ι : Type u_1} {M : Type u_3} [inst : Z
ero M] {f : ι → M} {s : Set ι},   Disjoint s (Function.support f) ↔ Set.EqOn f 0
 s
· 使用定理 `Urysohns.CU.lim_of_mem_C`：lim_of_mem_C (c : CU P) (x : X) (h : x in c.C)
 : c.lim x = 0
-/
theorem disjoint_C_support_lim (c : CU P) : Disjoint c.C (Function.support c.lim) :=
  Function.disjoint_support_iff.mpr (fun x hx => lim_of_mem_C c x hx)
/-
**Urysohns.CU.lim_of_notMem_U** 是 Mathlib 中的一个定理，位于命名空间 `Urysohns.CU`。
形式化陈述：lim_of_notMem_U (c : CU P) (x : X) (h : x ∉ c.U) : c.lim x = 1
参数：c : CU P；x : X；h : x ∉ c.U。
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
· 使用定理 `Urysohns.CU.approx_of_notMem_U`：approx_of_notMem_U (c : CU P) (n : Nat) 
{x : X} (hx : x ∉ c.U) : c.approx n x = 1
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lim_of_notMem_U (c : CU P) (x : X) (h : x ∉ c.U) : c.lim x = 1 := by
  simp only [CU.lim, approx_of_notMem_U c _ h, ciSup_const]
/-
**Urysohns.CU.lim_eq_midpoint** 是 Mathlib 中的一个定理，位于命名空间 `Urysohns.CU`。
形式化陈述：lim_eq_midpoint (c : CU P) (x : X) : c.lim x = midpoint Real (c.left.lim x
) (c.right.lim x)
参数：c : CU P；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Urysohns.CU.tendsto_approx_atTop`：tendsto_approx_atTop (c : CU P) (x : X
) : Tendsto (fun n => c.approx n x) atTop (𝓝 <| c.lim x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.tendsto_add_atTop_iff_nat`：tendsto_add_atTop_iff_nat {f : Nat -> 
α} {l : Filter α} (k : Nat) : Tendsto (fun n => f (n + k)) atTop l ↔ Tendsto f a
tTop l
· 使用定理 `Filter.Tendsto.midpoint`：∀ {R : Type u_1} {V : Type u_2} {P : Type u_3} 
[inst : AddCommGroup V] [inst_1 : TopologicalSpace V]   [inst_2 : AddTorsor V P]
 [inst_3 : To…
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
-/
theorem lim_eq_midpoint (c : CU P) (x : X) :
    c.lim x = midpoint ℝ (c.left.lim x) (c.right.lim x) := by
  refine tendsto_nhds_unique (c.tendsto_approx_atTop x) ((tendsto_add_atTop_iff_nat 1).1 ?_)
  simp only [approx]
  exact (c.left.tendsto_approx_atTop x).midpoint (c.right.tendsto_approx_atTop x)
/-
**Urysohns.CU.approx_le_lim** 是 Mathlib 中的一个定理，位于命名空间 `Urysohns.CU`。
形式化陈述：approx_le_lim (c : CU P) (x : X) (n : Nat) : c.approx n x <= c.lim x
参数：c : CU P；x : X；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用定理 `Urysohns.CU.bddAbove_range_approx`：bddAbove_range_approx (c : CU P) (x :
 X) : BddAbove (range fun n => c.approx n x)
-/
theorem approx_le_lim (c : CU P) (x : X) (n : ℕ) : c.approx n x ≤ c.lim x :=
  le_ciSup (c.bddAbove_range_approx x) _
/-
**Urysohns.CU.lim_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Urysohns.CU`。
形式化陈述：lim_nonneg (c : CU P) (x : X) : 0 <= c.lim x
参数：c : CU P；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Urysohns.CU.approx_nonneg`：approx_nonneg (c : CU P) (n : Nat) (x : X) : 
0 <= c.approx n x
· 使用定理 `Urysohns.CU.approx_le_lim`：approx_le_lim (c : CU P) (x : X) (n : Nat) : 
c.approx n x <= c.lim x
-/
theorem lim_nonneg (c : CU P) (x : X) : 0 ≤ c.lim x :=
  (c.approx_nonneg 0 x).trans (c.approx_le_lim x 0)
/-
**Urysohns.CU.lim_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Urysohns.CU`。
形式化陈述：lim_le_one (c : CU P) (x : X) : c.lim x <= 1
参数：c : CU P；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Urysohns.CU.approx_le_one`：approx_le_one (c : CU P) (n : Nat) (x : X) : 
c.approx n x <= 1
-/
theorem lim_le_one (c : CU P) (x : X) : c.lim x ≤ 1 :=
  ciSup_le fun _ => c.approx_le_one _ _
/-
**Urysohns.CU.lim_mem_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Urysohns.CU`。
形式化陈述：lim_mem_Icc (c : CU P) (x : X) : c.lim x in Icc (0 : Real) 1
参数：c : CU P；x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Urysohns.CU.lim_nonneg`：lim_nonneg (c : CU P) (x : X) : 0 <= c.lim x
· 使用定理 `Urysohns.CU.lim_le_one`：lim_le_one (c : CU P) (x : X) : c.lim x <= 1
-/
theorem lim_mem_Icc (c : CU P) (x : X) : c.lim x ∈ Icc (0 : ℝ) 1 :=
  ⟨c.lim_nonneg x, c.lim_le_one x⟩

/-- Continuity of `Urysohns.CU.lim`. See module docstring for a sketch of the proofs. -/
/-
**Urysohns.CU.continuous_lim** 是 Mathlib 中的一个定理，位于命名空间 `Urysohns.CU`。
形式化陈述：continuous_lim (c : CU P) : Continuous c.lim
参数：c : CU P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `Metric.nhds_basis_closedBall_pow`：nhds_basis_closedBall_pow {r : Real} (
h0 : 0 < r) (h1 : r < 1) : (𝓝 x).HasBasis (fun _ => True) fun n : Nat => closedB
all x (r ^ n)
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `Real.dist_le_of_mem_Icc_01`：dist_le_of_mem_Icc_01 {x y : Real} (hx : x i
n Icc (0 : Real) 1) (hy : y in Icc (0 : Real) 1) : dist x y <= 1
· 使用定理 `Urysohns.CU.lim_mem_Icc`：lim_mem_Icc (c : CU P) (x : X) : c.lim x in Icc
 (0 : Real) 1
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
（共 97 条，此处仅展示前 30 条）

--- 原说明 ---
Continuity of `Urysohns.CU.lim`. See module docstring for a sketch of the proofs
.
-/
theorem continuous_lim (c : CU P) : Continuous c.lim := by
  obtain ⟨h0, h1234, h1⟩ : 0 < (2⁻¹ : ℝ) ∧ (2⁻¹ : ℝ) < 3 / 4 ∧ (3 / 4 : ℝ) < 1 := by norm_num
  refine
    continuous_iff_continuousAt.2 fun x =>
      (Metric.nhds_basis_closedBall_pow (h0.trans h1234) h1).tendsto_right_iff.2 fun n _ => ?_
  simp only [Metric.mem_closedBall]
  induction n generalizing c with
  | zero =>
    filter_upwards with y
    rw [pow_zero]
    exact Real.dist_le_of_mem_Icc_01 (c.lim_mem_Icc _) (c.lim_mem_Icc _)
  | succ n ihn =>
    by_cases hxl : x ∈ c.left.U
    · filter_upwards [IsOpen.mem_nhds c.left.open_U hxl, ihn c.left] with _ hyl hyd
      rw [pow_succ', c.lim_eq_midpoint, c.lim_eq_midpoint,
        c.right.lim_of_mem_C _ (c.left_U_subset_right_C hyl),
        c.right.lim_of_mem_C _ (c.left_U_subset_right_C hxl)]
      refine (dist_midpoint_midpoint_le _ _ _ _).trans ?_
      rw [dist_self, add_zero, div_eq_inv_mul]
      gcongr
    · replace hxl : x ∈ c.left.right.Cᶜ :=
        compl_subset_compl.2 c.left.right.subset hxl
      filter_upwards [IsOpen.mem_nhds (isOpen_compl_iff.2 c.left.right.closed_C) hxl,
        ihn c.left.right, ihn c.right] with y hyl hydl hydr
      replace hxl : x ∉ c.left.left.U :=
        compl_subset_compl.2 c.left.left_U_subset_right_C hxl
      replace hyl : y ∉ c.left.left.U :=
        compl_subset_compl.2 c.left.left_U_subset_right_C hyl
      simp only [pow_succ, c.lim_eq_midpoint, c.left.lim_eq_midpoint,
        c.left.left.lim_of_notMem_U _ hxl, c.left.left.lim_of_notMem_U _ hyl]
      grw [dist_midpoint_midpoint_le, dist_midpoint_midpoint_le, dist_self, zero_add]
      set r := (3 / 4 : ℝ) ^ n
      calc _ ≤ (r / 2 + r) / 2 := by gcongr
        _ = _ := by ring

end CU

end Urysohns

/-- Urysohn's lemma: if `s` and `t` are two disjoint closed sets in a normal topological space `X`,
then there exists a continuous function `f : X → ℝ` such that

* `f` equals zero on `s`;
* `f` equals one on `t`;
* `0 ≤ f x ≤ 1` for all `x`.
-/
@[wikidata Q1816967]
/-
**exists_continuous_zero_one_of_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_continuous_zero_one_of_isClosed [NormalSpace X] {s t : Set X} (hs :
 IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) : exists f : C(X, Real), EqOn
 f 0 s ∧ EqOn f 1 t ∧ forall x, f x in Icc (0 : Real) 1
参数：hs : IsClosed s；ht : IsClosed t；hd : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `normal_exists_closure_subset`：normal_exists_closure_subset [NormalSpace 
X] {s t : Set X} (hs : IsClosed s) (ht : IsOpen t) (hst : s subseteq t) : exists
 u, IsOpen u ∧ s s…
· 使用定理 `Urysohns.CU.continuous_lim`：continuous_lim (c : CU P) : Continuous c.lim
· 使用定理 `Urysohns.CU.lim_of_mem_C`：lim_of_mem_C (c : CU P) (x : X) (h : x in c.C)
 : c.lim x = 0
· 使用定理 `Urysohns.CU.lim_of_notMem_U`：lim_of_notMem_U (c : CU P) (x : X) (h : x ∉
 c.U) : c.lim x = 1
· 使用定理 `Urysohns.CU.lim_mem_Icc`：lim_mem_Icc (c : CU P) (x : X) : c.lim x in Icc
 (0 : Real) 1

--- 原说明 ---
Urysohn's lemma: if `s` and `t` are two disjoint closed sets in a normal topolog
ical space `X`,
then there exists a continuous function `f : X → ℝ` such that

* `f` equals zero on `s`;
* `f` equals one on `t`;
* `0 ≤ f x ≤ 1` for all `x`.
-/
theorem exists_continuous_zero_one_of_isClosed [NormalSpace X]
    {s t : Set X} (hs : IsClosed s) (ht : IsClosed t)
    (hd : Disjoint s t) : ∃ f : C(X, ℝ), EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  -- The actual proof is in the code above. Here we just repack it into the expected format.
  let P : Set X → Set X → Prop := fun _ _ ↦ True
  set c : Urysohns.CU P :=
  { C := s
    U := tᶜ
    P_C_U := trivial
    closed_C := hs
    open_U := ht.isOpen_compl
    subset := disjoint_left.1 hd
    hP := by
      rintro c u c_closed - u_open cu
      rcases normal_exists_closure_subset c_closed u_open cu with ⟨v, v_open, cv, hv⟩
      exact ⟨v, v_open, cv, hv, trivial, trivial⟩ }
  exact ⟨⟨c.lim, c.continuous_lim⟩, c.lim_of_mem_C, fun x hx => c.lim_of_notMem_U _ fun h => h hx,
    c.lim_mem_Icc⟩

/-- Urysohn's lemma: if `s` and `t` are two disjoint sets in a regular locally compact topological
space `X`, with `s` compact and `t` closed, then there exists a continuous
function `f : X → ℝ` such that

* `f` equals zero on `s`;
* `f` equals one on `t`;
* `0 ≤ f x ≤ 1` for all `x`.
-/
/-
**exists_continuous_zero_one_of_isCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_continuous_zero_one_of_isCompact [RegularSpace X] [LocallyCompactSp
ace X] {s t : Set X} (hs : IsCompact s) (ht : IsClosed t) (hd : Disjoint s t) : 
exists f : C(X, Real), EqOn f 0 s ∧ EqOn f 1 t ∧ forall x, f x in Icc (0 : Real)
 1
参数：hs : IsCompact s；ht : IsClosed t；hd : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_compact_closed_between`：exists_compact_closed_between [LocallyCom
pactSpace X] [RegularSpace X] {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (
h_KU : K subseteq U…
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `Disjoint.subset_compl_left`：∀ {α : Type u_1} {s t : Set α}, Disjoint t s
 → s ⊆ tᶜ
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Urysohns.CU.continuous_lim`：continuous_lim (c : CU P) : Continuous c.lim
· 使用定理 `Urysohns.CU.lim_of_mem_C`：lim_of_mem_C (c : CU P) (x : X) (h : x in c.C)
 : c.lim x = 0
· 使用定理 `Urysohns.CU.lim_of_notMem_U`：lim_of_notMem_U (c : CU P) (x : X) (h : x ∉
 c.U) : c.lim x = 1
· 使用定理 `Urysohns.CU.lim_mem_Icc`：lim_mem_Icc (c : CU P) (x : X) : c.lim x in Icc
 (0 : Real) 1

--- 原说明 ---
Urysohn's lemma: if `s` and `t` are two disjoint sets in a regular locally compa
ct topological
space `X`, with `s` compact and `t` closed, then there exists a continuous
function `f : X → ℝ` such that

* `f` equals zero on `s`;
* `f` equals one on `t`;
* `0 ≤ f x ≤ 1` for all `x`.
-/
theorem exists_continuous_zero_one_of_isCompact [RegularSpace X] [LocallyCompactSpace X]
    {s t : Set X} (hs : IsCompact s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : C(X, ℝ), EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨k, k_comp, k_closed, sk, kt⟩ : ∃ k, IsCompact k ∧ IsClosed k ∧ s ⊆ interior k ∧ k ⊆ tᶜ :=
    exists_compact_closed_between hs ht.isOpen_compl hd.symm.subset_compl_left
  let P : Set X → Set X → Prop := fun C _ => IsCompact C
  set c : Urysohns.CU P :=
  { C := k
    U := tᶜ
    P_C_U := k_comp
    closed_C := k_closed
    open_U := ht.isOpen_compl
    subset := kt
    hP := by
      rintro c u - c_comp u_open cu
      rcases exists_compact_closed_between c_comp u_open cu with ⟨k, k_comp, k_closed, ck, ku⟩
      have A : closure (interior k) ⊆ k :=
        (IsClosed.closure_subset_iff k_closed).2 interior_subset
      refine ⟨interior k, isOpen_interior, ck, A.trans ku, c_comp,
        k_comp.of_isClosed_subset isClosed_closure A⟩ }
  exact ⟨⟨c.lim, c.continuous_lim⟩, fun x hx ↦ c.lim_of_mem_C _ (sk.trans interior_subset hx),
    fun x hx => c.lim_of_notMem_U _ fun h => h hx, c.lim_mem_Icc⟩

/-- Urysohn's lemma: if `s` and `t` are two disjoint sets in a regular locally compact topological
space `X`, with `s` compact and `t` closed, then there exists a continuous
function `f : X → ℝ` such that

* `f` equals zero on `t`;
* `f` equals one on `s`;
* `0 ≤ f x ≤ 1` for all `x`.
-/
/-
**exists_continuous_zero_one_of_isCompact'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_continuous_zero_one_of_isCompact' [RegularSpace X] [LocallyCompactS
pace X] {s t : Set X} (hs : IsCompact s) (ht : IsClosed t) (hd : Disjoint s t) :
 exists f : C(X, Real), EqOn f 0 t ∧ EqOn f 1 s ∧ forall x, f x in Icc (0 : Real
) 1
参数：hs : IsCompact s；ht : IsClosed t；hd : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_continuous_zero_one_of_isCompact`：exists_continuous_zero_one_of_i
sCompact [RegularSpace X] [LocallyCompactSpace X] {s t : Set X} (hs : IsCompact 
s) (ht : IsClosed t) (hd : Di…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `sub_eq_zero_of_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a = b
 → a - b = 0
· 使用定理 `Set.EqOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → 
β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₁ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N

--- 原说明 ---
Urysohn's lemma: if `s` and `t` are two disjoint sets in a regular locally compa
ct topological
space `X`, with `s` compact and `t` closed, then there exists a continuous
function `f : X → ℝ` such that

* `f` equals zero on `t`;
* `f` equals one on `s`;
* `0 ≤ f x ≤ 1` for all `x`.
-/
theorem exists_continuous_zero_one_of_isCompact' [RegularSpace X] [LocallyCompactSpace X]
    {s t : Set X} (hs : IsCompact s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : C(X, ℝ), EqOn f 0 t ∧ EqOn f 1 s ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨g, hgs, hgt, (hicc : ∀ x, 0 ≤ g x ∧ g x ≤ 1)⟩ := exists_continuous_zero_one_of_isCompact
    hs ht hd
  use 1 - g
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [ContinuousMap.sub_apply, ContinuousMap.one_apply, Pi.zero_apply]
    exact sub_eq_zero_of_eq (hgt.symm hx)
  · intro x hx
    simp only [ContinuousMap.sub_apply, ContinuousMap.one_apply, Pi.one_apply, sub_eq_self]
    exact hgs hx
  · intro x
    simpa [and_comm] using hicc x

/-- Urysohn's lemma: if `s` and `t` are two disjoint sets in a regular locally compact topological
space `X`, with `s` compact and `t` closed, then there exists a continuous compactly supported
function `f : X → ℝ` such that

* `f` equals one on `s`;
* `f` equals zero on `t`;
* `0 ≤ f x ≤ 1` for all `x`.
-/
/-
**exists_continuous_one_zero_of_isCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_continuous_one_zero_of_isCompact [RegularSpace X] [LocallyCompactSp
ace X] {s t : Set X} (hs : IsCompact s) (ht : IsClosed t) (hd : Disjoint s t) : 
exists f : C(X, Real), EqOn f 1 s ∧ EqOn f 0 t ∧ HasCompactSupport f ∧ forall x,
 f x in Icc (0 : Real) 1
参数：hs : IsCompact s；ht : IsClosed t；hd : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_compact_closed_between`：exists_compact_closed_between [LocallyCom
pactSpace X] [RegularSpace X] {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (
h_KU : K subseteq U…
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `Disjoint.subset_compl_left`：∀ {α : Type u_1} {s t : Set α}, Disjoint t s
 → s ⊆ tᶜ
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `exists_continuous_zero_one_of_isCompact`：exists_continuous_zero_one_of_i
sCompact [RegularSpace X] [LocallyCompactSpace X] {s t : Set X} (hs : IsCompact 
s) (ht : IsClosed t) (hd : Di…
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.disjoint_compl_right_iff_subset`：disjoint_compl_right_iff_subset : D
isjoint s tᶜ ↔ s subseteq t
· 使用定理 `Set.subset_compl_comm`：subset_compl_comm : s subseteq tᶜ ↔ t subseteq sᶜ
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `Continuous.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g 
: X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasCompactSupport.intro'`：∀ {α : Type u_2} {β : Type u_4} [inst : Topolo
gicalSpace α] [inst_1 : Zero β] {f : α → β} {K : Set α},   IsCompact K → IsClose
d K → (∀ x ∉ K…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Urysohn's lemma: if `s` and `t` are two disjoint sets in a regular locally compa
ct topological
space `X`, with `s` compact and `t` closed, then there exists a continuous compa
ctly supported
function `f : X → ℝ` such that

* `f` equals one on `s`;
* `f` equals zero on `t`;
* `0 ≤ f x ≤ 1` for all `x`.
-/
theorem exists_continuous_one_zero_of_isCompact [RegularSpace X] [LocallyCompactSpace X]
    {s t : Set X} (hs : IsCompact s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : C(X, ℝ), EqOn f 1 s ∧ EqOn f 0 t ∧ HasCompactSupport f ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨k, k_comp, k_closed, sk, kt⟩ : ∃ k, IsCompact k ∧ IsClosed k ∧ s ⊆ interior k ∧ k ⊆ tᶜ :=
    exists_compact_closed_between hs ht.isOpen_compl hd.symm.subset_compl_left
  rcases exists_continuous_zero_one_of_isCompact hs isOpen_interior.isClosed_compl
    (disjoint_compl_right_iff_subset.mpr sk) with ⟨⟨f, hf⟩, hfs, hft, h'f⟩
  have A : t ⊆ (interior k)ᶜ := subset_compl_comm.mpr (interior_subset.trans kt)
  refine ⟨⟨fun x ↦ 1 - f x, by fun_prop⟩, fun x hx ↦ by simpa using hfs hx,
    fun x hx ↦ by simpa [sub_eq_zero] using (hft (A hx)).symm, ?_, fun x ↦ ?_⟩
  · apply HasCompactSupport.intro' k_comp k_closed (fun x hx ↦ ?_)
    simp only [ContinuousMap.coe_mk, sub_eq_zero]
    apply (hft _).symm
    contrapose hx
    simp only [mem_compl_iff, not_not] at hx
    exact interior_subset hx
  · have : 0 ≤ f x ∧ f x ≤ 1 := by simpa using h'f x
    simp [this]

/-- Urysohn's lemma: if `s` and `t` are two disjoint sets in a regular locally compact topological
space `X`, with `s` compact and `t` closed, then there exists a continuous compactly supported
function `f : X → ℝ` such that

* `f` equals one on `s`;
* `f` equals zero on `t`;
* `0 ≤ f x ≤ 1` for all `x`.

Moreover, if `s` is Gδ, one can ensure that `f ⁻¹ {1}` is exactly `s`.
-/
/-
**exists_continuous_one_zero_of_isCompact_of_isG** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Urysohn's lemma: if `s` and `t` are two disjoint sets in a regular locally compa
ct topological
space `X`, with `s` compact and `t` closed, then there exists a continuous compa
ctly supported
function `f : X → ℝ` such that

* `f` equals one on `s`;
* `f` equals zero on `t`;
* `0 ≤ f x ≤ 1` for all `x`.

Moreover, if `s` is Gδ, one can ensure that `f ⁻¹ {1}` is exactly `s`.
-/
theorem exists_continuous_one_zero_of_isCompact_of_isGδ [RegularSpace X] [LocallyCompactSpace X]
    {s t : Set X} (hs : IsCompact s) (h's : IsGδ s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : C(X, ℝ), s = f ⁻¹' {1} ∧ EqOn f 0 t ∧ HasCompactSupport f
      ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  rcases h's.eq_iInter_nat with ⟨U, U_open, hU⟩
  obtain ⟨m, m_comp, -, sm, mt⟩ : ∃ m, IsCompact m ∧ IsClosed m ∧ s ⊆ interior m ∧ m ⊆ tᶜ :=
    exists_compact_closed_between hs ht.isOpen_compl hd.symm.subset_compl_left
  have A n : ∃ f : C(X, ℝ), EqOn f 1 s ∧ EqOn f 0 (U n ∩ interior m)ᶜ ∧ HasCompactSupport f
      ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
    apply exists_continuous_one_zero_of_isCompact hs
      ((U_open n).inter isOpen_interior).isClosed_compl
    rw [disjoint_compl_right_iff_subset]
    exact subset_inter ((hU.subset.trans (iInter_subset U n))) sm
  choose f fs fm _hf f_range using A
  obtain ⟨u, u_pos, u_sum, hu⟩ : ∃ (u : ℕ → ℝ), (∀ i, 0 < u i) ∧ Summable u ∧ ∑' i, u i = 1 :=
    ⟨fun n ↦ 1/2/2^n, fun n ↦ by positivity, summable_geometric_two' 1, tsum_geometric_two' 1⟩
  let g : X → ℝ := fun x ↦ ∑' n, u n * f n x
  have hgmc : EqOn g 0 mᶜ := by
    intro x hx
    have B n : f n x = 0 := by
      have : mᶜ ⊆ (U n ∩ interior m)ᶜ := by
        simpa using inter_subset_right.trans interior_subset
      exact fm n (this hx)
    simp [g, B]
  have I n x : u n * f n x ≤ u n := mul_le_of_le_one_right (u_pos n).le (f_range n x).2
  have S x : Summable (fun n ↦ u n * f n x) := Summable.of_nonneg_of_le
      (fun n ↦ mul_nonneg (u_pos n).le (f_range n x).1) (fun n ↦ I n x) u_sum
  refine ⟨⟨g, ?_⟩, ?_, hgmc.mono (subset_compl_comm.mp mt), ?_, fun x ↦ ⟨?_, ?_⟩⟩
  · apply continuous_tsum (fun n ↦ by fun_prop) u_sum (fun n x ↦ ?_)
    simpa [abs_of_nonneg, (u_pos n).le, (f_range n x).1] using I n x
  · apply Subset.antisymm (fun x hx ↦ by simp [g, fs _ hx, hu]) ?_
    apply compl_subset_compl.1
    intro x hx
    obtain ⟨n, hn⟩ : ∃ n, x ∉ U n := by simpa [hU] using hx
    have fnx : f n x = 0 := fm _ (by simp [hn])
    have : g x < 1 := by
      apply lt_of_lt_of_le ?_ hu.le
      exact (S x).tsum_lt_tsum (i := n) (fun i ↦ I i x) (by simp [fnx, u_pos n]) u_sum
    simpa using this.ne
  · exact HasCompactSupport.of_support_subset_isCompact m_comp
      (Function.support_subset_iff'.mpr hgmc)
  · exact tsum_nonneg (fun n ↦ mul_nonneg (u_pos n).le (f_range n x).1)
  · apply le_trans _ hu.le
    exact (S x).tsum_le_tsum (fun n ↦ I n x) u_sum

/-- A variation of Urysohn's lemma. In a `R1Space X`, for a closed set `t` and a relatively
compact open set `s` such that `t ⊆ s`, there is a continuous function `f` supported in `s`,
`f x = 1` on `t` and `0 ≤ f x ≤ 1`. -/
/-
**exists_tsupport_one_of_isOpen_isClosed** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_tsupport_one_of_isOpen_isClosed [R1Space X] {s t : Set X} (hs : IsO
pen s) (hscp : IsCompact (closure s)) (ht : IsClosed t) (hst : t subseteq s) : e
xists f : C(X, Real), tsupport f subseteq s ∧ EqOn f 1 t ∧ forall x, f x in Icc 
(0 : Real) 1
参数：hs : IsOpen s；hscp : IsCompact (closure s)；ht : IsClosed t；hst : t subseteq s
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SeparatedNhds.of_isClosed_isCompact_closure_compl_isClosed`：SeparatedNhd
s.of_isClosed_isCompact_closure_compl_isClosed [R1Space X] {s : Set X} {t : Set 
X} (H1 : IsClosed s) (H2 : IsCompact (closure sᶜ…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isClosed_compl_iff`：isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpe
n s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `LE.le.disjoint_compl_left`：LE.le.disjoint_compl_left (h : b <= a) : Disj
oint aᶜ b
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用引理 `Set.subset_compl_iff_disjoint_right`：subset_compl_iff_disjoint_right : s
 subseteq tᶜ ↔ Disjoint s t
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_compl_comm`：subset_compl_comm : s subseteq tᶜ ↔ t subseteq sᶜ
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `LE.le.disjoint_compl_right`：LE.le.disjoint_compl_right (h : a <= b) : Di
sjoint a bᶜ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.compl_subset_comm`：compl_subset_comm : sᶜ subseteq t ↔ tᶜ subseteq s
· 使用定理 `Urysohns.CU.continuous_lim`：continuous_lim (c : CU P) : Continuous c.lim
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `Disjoint.subset_compl_right`：∀ {α : Type u_1} {s t : Set α}, Disjoint s 
t → s ⊆ tᶜ
· 使用引理 `Set.disjoint_of_subset_right`：disjoint_of_subset_right (h : t subseteq u
) (d : Disjoint s u) : Disjoint s t
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Urysohns.CU.disjoint_C_support_lim`：disjoint_C_support_lim (c : CU P) : 
Disjoint c.C (Function.support c.lim)
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
A variation of Urysohn's lemma. In a `R1Space X`, for a closed set `t` and a rel
atively
compact open set `s` such that `t ⊆ s`, there is a continuous function `f` suppo
rted in `s`,
`f x = 1` on `t` and `0 ≤ f x ≤ 1`.
-/
lemma exists_tsupport_one_of_isOpen_isClosed [R1Space X] {s t : Set X}
    (hs : IsOpen s) (hscp : IsCompact (closure s)) (ht : IsClosed t) (hst : t ⊆ s) :
    ∃ f : C(X, ℝ), tsupport f ⊆ s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
-- separate `sᶜ` and `t` by `u` and `v`.
  rw [← compl_compl s] at hscp
  obtain ⟨u, v, huIsOpen, hvIsOpen, hscompl_subset_u, ht_subset_v, hDisjointuv⟩ :=
    SeparatedNhds.of_isClosed_isCompact_closure_compl_isClosed (isClosed_compl_iff.mpr hs)
    hscp ht (LE.le.disjoint_compl_left hst)
  rw [← subset_compl_iff_disjoint_right] at hDisjointuv
  have huvc : closure u ⊆ vᶜ := closure_minimal hDisjointuv hvIsOpen.isClosed_compl
-- although `sᶜ` is not compact, `closure s` is compact and we can apply
-- `SeparatedNhds.of_isClosed_isCompact_closure_compl_isClosed`. To apply the condition
-- recursively, we need to make sure that `sᶜ ⊆ C`.
  let P : Set X → Set X → Prop := fun C _ => sᶜ ⊆ C
  set c : Urysohns.CU P :=
  { C := closure u
    U := tᶜ
    P_C_U := hscompl_subset_u.trans subset_closure
    closed_C := isClosed_closure
    open_U := ht.isOpen_compl
    subset := subset_compl_comm.mp
      (Subset.trans ht_subset_v (subset_compl_comm.mp huvc))
    hP := by
      intro c u0 cIsClosed Pc u0IsOpen csubu0
      obtain ⟨u1, hu1⟩ := SeparatedNhds.of_isClosed_isCompact_closure_compl_isClosed cIsClosed
        (IsCompact.of_isClosed_subset hscp isClosed_closure
        (closure_mono (compl_subset_compl.mpr Pc)))
        (isClosed_compl_iff.mpr u0IsOpen) (LE.le.disjoint_compl_right csubu0)
      simp_rw [← subset_compl_iff_disjoint_right, compl_subset_comm (s := u0)] at hu1
      obtain ⟨v1, hu1, hv1, hcu1, hv1u, hu1v1⟩ := hu1
      refine ⟨u1, hu1, hcu1, ?_, Pc, (Pc.trans hcu1).trans subset_closure⟩
      exact closure_minimal hu1v1 hv1.isClosed_compl |>.trans hv1u }
-- `c.lim = 0` on `closure u` and `c.lim = 1` on `t`, so that `tsupport c.lim ⊆ s`.
  use ⟨c.lim, c.continuous_lim⟩
  simp only [ContinuousMap.coe_mk]
  refine ⟨?_, ?_, Urysohns.CU.lim_mem_Icc c⟩
  · apply Subset.trans _ (compl_subset_comm.mp hscompl_subset_u)
    rw [← IsClosed.closure_eq (isClosed_compl_iff.mpr huIsOpen)]
    apply closure_mono
    exact Disjoint.subset_compl_right (disjoint_of_subset_right subset_closure
      (Disjoint.symm (Urysohns.CU.disjoint_C_support_lim c)))
  · intro x hx
    apply Urysohns.CU.lim_of_notMem_U
    exact notMem_compl_iff.mpr hx

/-- A variation of **Urysohn's lemma**. In a Hausdorff locally compact space, for a compact set `K`
contained in an open set `V`, there exists a compactly supported continuous function `f` such that
`0 ≤ f ≤ 1`, `f = 1` on K and the support of `f` is contained in `V`. -/
/-
**exists_continuousMap_one_of_isCompact_subset_isOpen** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：exists_continuousMap_one_of_isCompact_subset_isOpen [R1Space X] [LocallyCo
mpactSpace X] {K V : Set X} (hK : IsCompact K) (hV : IsOpen V) (hKV : K subseteq
 V) : exists f : C(X, Real), Set.EqOn f 1 K ∧ IsCompact (tsupport f) ∧ tsupport 
f subseteq V ∧ forall x, f x in Set.Icc 0 1
参数：hK : IsCompact K；hV : IsOpen V；hKV : K subseteq V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_open_between_and_isCompact_closure`：exists_open_between_and_isCom
pact_closure [LocallyCompactSpace X] [RegularSpace X] {K U : Set X} (hK : IsComp
act K) (hU : IsOpen U) (hKU : K…
· 使用定理 `instRegularSpaceOfWeaklyLocallyCompactSpaceOfR1Space`：∀ {X : Type u_1} [
inst : TopologicalSpace X] [WeaklyLocallyCompactSpace X] [R1Space X], RegularSpa
ce X
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用引理 `exists_tsupport_one_of_isOpen_isClosed`：exists_tsupport_one_of_isOpen_is
Closed [R1Space X] {s t : Set X} (hs : IsOpen s) (hscp : IsCompact (closure s)) 
(ht : IsClosed t) (hst : t s…
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `IsCompact.closure_subset_of_isOpen`：IsCompact.closure_subset_of_isOpen {
K : Set X} (hK : IsCompact K) {U : Set X} (hU : IsOpen U) (hKU : K subseteq U) :
 closure K subseteq U
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Set.EqOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f₁ f₂ : 
α → β}, s₁ ⊆ s₂ → Set.EqOn f₁ f₂ s₂ → Set.EqOn f₁ f₂ s₁
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t

--- 原说明 ---
A variation of **Urysohn's lemma**. In a Hausdorff locally compact space, for a 
compact set `K`
contained in an open set `V`, there exists a compactly supported continuous func
tion `f` such that
`0 ≤ f ≤ 1`, `f = 1` on K and the support of `f` is contained in `V`.
-/
lemma exists_continuousMap_one_of_isCompact_subset_isOpen [R1Space X] [LocallyCompactSpace X]
    {K V : Set X} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ f : C(X, ℝ), Set.EqOn f 1 K ∧ IsCompact (tsupport f) ∧
      tsupport f ⊆ V ∧ ∀ x, f x ∈ Set.Icc 0 1 := by
  obtain ⟨U, hU1, hU2, hU3, hU4⟩ := exists_open_between_and_isCompact_closure hK hV hKV
  obtain ⟨f, hf1, hf2, hf3⟩ := exists_tsupport_one_of_isOpen_isClosed hU1 hU4
    isClosed_closure (hK.closure_subset_of_isOpen hU1 hU2)
  have hfU : tsupport f ⊆ closure U := hf1.trans subset_closure
  exact ⟨f, hf2.mono subset_closure,
    .of_isClosed_subset hU4 isClosed_closure hfU, hfU.trans hU3, hf3⟩
/-
**exists_continuous_nonneg_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_continuous_nonneg_pos [RegularSpace X] [LocallyCompactSpace X] (x :
 X) : exists f : C(X, Real), HasCompactSupport f ∧ 0 <= (f : X -> Real) ∧ f x !=
 0
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WeaklyLocallyCompactSpace.exists_compact_mem_nhds`：∀ {X : Type u_3} {ins
t : TopologicalSpace X} [self : WeaklyLocallyCompactSpace X] (x : X), ∃ s, IsCom
pact s ∧ s ∈ nhds x
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `exists_continuous_one_zero_of_isCompact`：exists_continuous_one_zero_of_i
sCompact [RegularSpace X] [LocallyCompactSpace X] {s t : Set X} (hs : IsCompact 
s) (ht : IsClosed t) (hd : Di…
· 使用定理 `isClosed_empty`：isClosed_empty : IsClosed (∅ : Set X)
· 使用定理 `Set.disjoint_empty`：∀ {α : Type u} (s : Set α), Disjoint s ∅
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem exists_continuous_nonneg_pos [RegularSpace X] [LocallyCompactSpace X] (x : X) :
    ∃ f : C(X, ℝ), HasCompactSupport f ∧ 0 ≤ (f : X → ℝ) ∧ f x ≠ 0 := by
  rcases exists_compact_mem_nhds x with ⟨k, hk, k_mem⟩
  rcases exists_continuous_one_zero_of_isCompact hk isClosed_empty (disjoint_empty k)
    with ⟨f, fk, -, f_comp, hf⟩
  refine ⟨f, f_comp, fun x ↦ (hf x).1, ?_⟩
  have := fk (mem_of_mem_nhds k_mem)
  simp only [Pi.one_apply] at this
  simp [this]
