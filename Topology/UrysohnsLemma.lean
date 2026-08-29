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
Definition of `CU` / `CU` 的定义

English:
structure CU
  parameters: {X : Type*} [TopologicalSpace X] (P : Set X -> Set X -> Prop)
  axioms and operations (7):
    - C : Set X
    - U : Set X
    - P_C_U : P C U
    - closed_C : IsClosed C
    - open_U : IsOpen U
    - subset : C subseteq U
    - hP : forall {c u : Set X}, IsClosed c -> P c u -> IsOpen u -> c subseteq u -> exists (v : Set X), IsOpen v ∧ c subseteq v ∧ closure v subseteq u ∧ P c v ∧ P (closure v) u

中文:
结构 CU
  参数: {X : 类型} [拓扑空间 X] (P : 集合 X -> 集合 X -> 命题)
  公理与运算 (7 个):
    - C : 集合 X
    - U : 集合 X
    - P_C_U : P C U
    - closed_C : 是闭集 C
    - open_U : 是开集 U
    - subset : C subseteq U
    - hP : 对任意 {c u : 集合 X}, 是闭集 c -> P c u -> 是开集 u -> c subseteq u -> 存在 (v : 集合 X), 是开集 v ∧ c subseteq v ∧ closure v subseteq u ∧ P c v ∧ P (closure v) u
-/
structure CU {X : Type*} [TopologicalSpace X] (P : Set X -> Set X -> Prop) where
  /-- The inner set in the inductive construction towards Urysohn's lemma -/
  protected C : Set X
  /-- The outer set in the inductive construction towards Urysohn's lemma -/
  protected U : Set X
  /-- The proof that `C` and `U` satisfy the property `P C U` -/
  protected P_C_U : P C U
  protected closed_C : IsClosed C
  protected open_U : IsOpen U
  protected subset : C subseteq U
  /-- The proof that we can divide `CU` pairs in half -/
  protected hP : forall {c u : Set X}, IsClosed c -> P c u -> IsOpen u -> c subseteq u ->
    exists (v : Set X), IsOpen v ∧ c subseteq v ∧ closure v subseteq u ∧ P c v ∧ P (closure v) u

namespace CU

variable {P : Set X -> Set X -> Prop}

/-- By assumption, for each `c : CU P` there exists an open set `u`
such that `c.C ⊆ u` and `closure u ⊆ c.U`. `c.left` is the pair `(c.C, u)`. -/
@[simps C]
/--
Definition of `left` / `left` 的定义

English:
definition left
  signature: (c : CU P)
  body: c.C
  U := (c.hP c.closed_C c.P_C_U c.open_U c.subset).choose
  closed_C := c.closed_C
  P_C_U := (c.hP c.closed_C c.P_C_U c.open_U c.subset).choose_spec.2.2.2.1
  open_U := (c.hP c.closed_C c.P_C_U c.open_U c.subset).choose_spec.1
  subset := (c.hP c.closed_C c.P_C_U c.open_U c.subset).choose_spec.

中文:
定义 left
  签名: (c : CU P)
  定义体: c.C
  U := (c.hP c.closed_C c.P_C_U c.open_U c.subset).choose
  closed_C := c.closed_C
  P_C_U := (c.hP c.closed_C c.P_C_U c.open_U c.subset).choose_spec.2.2.2.1
  open_U := (c.hP c.closed_C c.P_C_U c.open_U c.subset).choose_spec.1
  subset := (c.hP c.closed_C c.P_C_U c.open_U c.subset).choose_spec.
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
/--
Definition of `right` / `right` 的定义

English:
definition right
  signature: (c : CU P)
  body: closure (c.hP c.closed_C c.P_C_U c.open_U c.subset).choose
  U := c.U
  closed_C := isClosed_closure
  P_C_U := (c.hP c.closed_C c.P_C_U c.open_U c.subset).choose_spec.2.2.2.2
  open_U := c.open_U
  subset := (c.hP c.closed_C c.P_C_U c.open_U c.subset).choose_spec.2.2.1
  hP := c.hP

中文:
定义 right
  签名: (c : CU P)
  定义体: closure (c.hP c.closed_C c.P_C_U c.open_U c.subset).choose
  U := c.U
  closed_C := isClosed_closure
  P_C_U := (c.hP c.closed_C c.P_C_U c.open_U c.subset).choose_spec.2.2.2.2
  open_U := c.open_U
  subset := (c.hP c.closed_C c.P_C_U c.open_U c.subset).choose_spec.2.2.1
  hP := c.hP

Depends on / 依赖: P_C_U, c.P_C_U, c.closed_C, c.hP, c.open_U, c.subset, closed_C, closure, open_U, subset
-/
def right (c : CU P) : CU P where
  C := closure (c.hP c.closed_C c.P_C_U c.open_U c.subset).choose
  U := c.U
  closed_C := isClosed_closure
  P_C_U := (c.hP c.closed_C c.P_C_U c.open_U c.subset).choose_spec.2.2.2.2
  open_U := c.open_U
  subset := (c.hP c.closed_C c.P_C_U c.open_U c.subset).choose_spec.2.2.1
  hP := c.hP

/--
theorem `left_U_subset_right_C` / 定理 `left_U_subset_right_C`

English:
theorem left_U_subset_right_C
  given: (c : CU P)
  statement: c.left.U subseteq c.right.C
  proof: subset_closure

中文:
定理 left_U_subset_right_C
  条件: (c : CU P)
  结论: c.left.U subseteq c.right.C
  证明: subset_closure

Depends on / 依赖: subset_closure
-/
theorem left_U_subset_right_C (c : CU P) : c.left.U subseteq c.right.C :=
  subset_closure

/--
theorem `left_U_subset` / 定理 `left_U_subset`

English:
theorem left_U_subset
  given: (c : CU P)
  statement: c.left.U subseteq c.U
  proof: Subset.trans c.left_U_subset_right_C c.right.subset

中文:
定理 left_U_subset
  条件: (c : CU P)
  结论: c.left.U subseteq c.U
  证明: Subset.trans c.left_U_subset_right_C c.right.subset

Depends on / 依赖: Subset, Subset.trans, c.left_U_subset_right_C, c.right.subset, left_U_subset_right_C, subset
-/
theorem left_U_subset (c : CU P) : c.left.U subseteq c.U :=
  Subset.trans c.left_U_subset_right_C c.right.subset

/--
theorem `subset_right_C` / 定理 `subset_right_C`

English:
theorem subset_right_C
  given: (c : CU P)
  statement: c.C subseteq c.right.C
  proof: Subset.trans c.left.subset c.left_U_subset_right_C

中文:
定理 subset_right_C
  条件: (c : CU P)
  结论: c.C subseteq c.right.C
  证明: Subset.trans c.left.subset c.left_U_subset_right_C

Depends on / 依赖: Subset, Subset.trans, c.left.subset, c.left_U_subset_right_C, left_U_subset_right_C, subset
-/
theorem subset_right_C (c : CU P) : c.C subseteq c.right.C :=
  Subset.trans c.left.subset c.left_U_subset_right_C

/--
Definition of `approx` / `approx` 的定义

English:
definition approx
  signature: : Nat -> CU P -> X -> Real

中文:
定义 approx
  签名: : 自然数 -> CU P -> X -> 实数
-/
def approx : Nat -> CU P -> X -> Real
  | 0, c, x => indicator c.Uᶜ 1 x
  | n + 1, c, x => midpoint Real (approx n c.left x) (approx n c.right x)

/--
theorem `approx_of_mem_C` / 定理 `approx_of_mem_C`

English:
theorem approx_of_mem_C
  given: (c : CU P) (n : Nat) {x : X} (hx : x in c.C)
  statement: c.approx n x = 0
  proof: by
  induction n generalizing c with
  | zero => exact indicator_of_notMem (fun (hU : x in c.Uᶜ) => hU <| c.subset hx) _
  | succ n ihn =>
    simp only [approx]
    rw [ihn]; rw [ihn]; rw [midpoint_self]
    exacts [c.subset_right_C hx, hx]

中文:
定理 approx_of_mem_C
  条件: (c : CU P) (n : 自然数) {x : X} (hx : x in c.C)
  结论: c.approx n x = 0
  证明: by
  induction n generalizing c with
  | zero => exact indicator_of_notMem (fun (hU : x in c.Uᶜ) => hU <| c.subset hx) _
  | succ n ihn =>
    simp only [approx]
    rw [ihn]; rw [ihn]; rw [midpoint_self]
    exacts [c.subset_right_C hx, hx]

Depends on / 依赖: approx, c.subset, c.subset_right_C, exacts, generalizing, indicator_of_notMem, midpoint_self, subset, subset_right_C
-/
theorem approx_of_mem_C (c : CU P) (n : Nat) {x : X} (hx : x in c.C) : c.approx n x = 0 := by
  induction n generalizing c with
  | zero => exact indicator_of_notMem (fun (hU : x in c.Uᶜ) => hU <| c.subset hx) _
  | succ n ihn =>
    simp only [approx]
    rw [ihn]; rw [ihn]; rw [midpoint_self]
    exacts [c.subset_right_C hx, hx]

/--
theorem `approx_of_notMem_U` / 定理 `approx_of_notMem_U`

English:
theorem approx_of_notMem_U
  given: (c : CU P) (n : Nat) {x : X} (hx : x ∉ c.U)
  statement: c.approx n x = 1
  proof: by
  induction n generalizing c with
  | zero =>
    rw [← mem_compl_iff] at hx
    exact indicator_of_mem hx _
  | succ n ihn =>
    simp only [approx]
    rw [ihn]; rw [ihn]; rw [midpoint_self]
    exacts [hx, fun hU => hx <| c.left_U_subset hU]

中文:
定理 approx_of_notMem_U
  条件: (c : CU P) (n : 自然数) {x : X} (hx : x ∉ c.U)
  结论: c.approx n x = 1
  证明: by
  induction n generalizing c with
  | zero =>
    rw [← mem_compl_iff] at hx
    exact indicator_of_mem hx _
  | succ n ihn =>
    simp only [approx]
    rw [ihn]; rw [ihn]; rw [midpoint_self]
    exacts [hx, fun hU => hx <| c.left_U_subset hU]

Depends on / 依赖: approx, c.left_U_subset, exacts, generalizing, indicator_of_mem, left_U_subset, mem_compl_iff, midpoint_self
-/
theorem approx_of_notMem_U (c : CU P) (n : Nat) {x : X} (hx : x ∉ c.U) : c.approx n x = 1 := by
  induction n generalizing c with
  | zero =>
    rw [← mem_compl_iff] at hx
    exact indicator_of_mem hx _
  | succ n ihn =>
    simp only [approx]
    rw [ihn]; rw [ihn]; rw [midpoint_self]
    exacts [hx, fun hU => hx <| c.left_U_subset hU]

/--
theorem `approx_nonneg` / 定理 `approx_nonneg`

English:
theorem approx_nonneg
  given: (c : CU P) (n : Nat) (x : X)
  statement: 0 <= c.approx n x
  proof: by
  induction n generalizing c with
  | zero => exact indicator_nonneg (fun _ _ => zero_le_one) _
  | succ n ihn =>
    simp only [approx, midpoint_eq_smul_add]
    refine mul_nonneg (inv_nonneg.2 zero_le_two) (add_nonneg ?_ ?_) <;> apply ihn

中文:
定理 approx_nonneg
  条件: (c : CU P) (n : 自然数) (x : X)
  结论: 0 <= c.approx n x
  证明: by
  induction n generalizing c with
  | zero => exact indicator_nonneg (fun _ _ => zero_le_one) _
  | succ n ihn =>
    simp only [approx, midpoint_eq_smul_add]
    refine mul_nonneg (inv_nonneg.2 zero_le_two) (add_nonneg ?_ ?_) <;> apply ihn

Depends on / 依赖: add_nonneg, approx, generalizing, indicator_nonneg, inv_nonneg, midpoint_eq_smul_add, mul_nonneg, zero_le_one, zero_le_two
-/
theorem approx_nonneg (c : CU P) (n : Nat) (x : X) : 0 <= c.approx n x := by
  induction n generalizing c with
  | zero => exact indicator_nonneg (fun _ _ => zero_le_one) _
  | succ n ihn =>
    simp only [approx, midpoint_eq_smul_add]
    refine mul_nonneg (inv_nonneg.2 zero_le_two) (add_nonneg ?_ ?_) <;> apply ihn

/--
theorem `approx_le_one` / 定理 `approx_le_one`

English:
theorem approx_le_one
  given: (c : CU P) (n : Nat) (x : X)
  statement: c.approx n x <= 1
  proof: by
  induction n generalizing c with
  | zero => exact indicator_apply_le' (fun _ => le_rfl) fun _ => zero_le_one
  | succ n ihn =>
    simp only [approx, midpoint_eq_smul_add, invOf_eq_inv, smul_eq_mul, ← div_eq_inv_mul]
    have := add_le_add (ihn (left c)) (ihn (right c))
    norm_num at this
   

中文:
定理 approx_le_one
  条件: (c : CU P) (n : 自然数) (x : X)
  结论: c.approx n x <= 1
  证明: by
  induction n generalizing c with
  | zero => exact indicator_apply_le' (fun _ => le_rfl) fun _ => zero_le_one
  | succ n ihn =>
    simp only [approx, midpoint_eq_smul_add, invOf_eq_inv, smul_eq_mul, ← div_eq_inv_mul]
    have := add_le_add (ihn (left c)) (ihn (right c))
    norm_num at this
   

Depends on / 依赖: Iff.mpr, add_le_add, approx, div_eq_inv_mul, div_le_one, generalizing, indicator_apply_le, invOf_eq_inv, le_rfl, midpoint_eq_smul_add, smul_eq_mul, zero_le_one, zero_lt_two
-/
theorem approx_le_one (c : CU P) (n : Nat) (x : X) : c.approx n x <= 1 := by
  induction n generalizing c with
  | zero => exact indicator_apply_le' (fun _ => le_rfl) fun _ => zero_le_one
  | succ n ihn =>
    simp only [approx, midpoint_eq_smul_add, invOf_eq_inv, smul_eq_mul, ← div_eq_inv_mul]
    have := add_le_add (ihn (left c)) (ihn (right c))
    norm_num at this
    exact Iff.mpr (div_le_one zero_lt_two) this

/--
theorem `bddAbove_range_approx` / 定理 `bddAbove_range_approx`

English:
theorem bddAbove_range_approx
  given: (c : CU P) (x : X)
  statement: BddAbove (range fun n => c.approx n x)
  proof: ⟨1, fun _ ⟨n, hn⟩ => hn ▸ c.approx_le_one n x⟩

中文:
定理 bddAbove_range_approx
  条件: (c : CU P) (x : X)
  结论: BddAbove (range fun n => c.approx n x)
  证明: ⟨1, fun _ ⟨n, hn⟩ => hn ▸ c.approx_le_one n x⟩

Depends on / 依赖: approx_le_one, c.approx_le_one
-/
theorem bddAbove_range_approx (c : CU P) (x : X) : BddAbove (range fun n => c.approx n x) :=
  ⟨1, fun _ ⟨n, hn⟩ => hn ▸ c.approx_le_one n x⟩

/--
theorem `approx_le_approx_of_U_sub_C` / 定理 `approx_le_approx_of_U_sub_C`

English:
theorem approx_le_approx_of_U_sub_C
  given: {c₁ c₂ : CU P} (h : c₁.U subseteq c₂.C) (n₁ n₂ : Nat) (x : X)
  proof: by
  by_cases hx : x in c₁.U
  · calc
      approx n₂ c₂ x = 0 := approx_of_mem_C _ _ (h hx)
      _ <= approx n₁ c₁ x := approx_nonneg _ _ _
  · calc
      approx n₂ c₂ x <= 1 := approx_le_one _ _ _
      _ = approx n₁ c₁ x := (approx_of_notMem_U _ _ hx).symm

中文:
定理 approx_le_approx_of_U_sub_C
  条件: {c₁ c₂ : CU P} (h : c₁.U subseteq c₂.C) (n₁ n₂ : 自然数) (x : X)
  证明: by
  by_cases hx : x in c₁.U
  · calc
      approx n₂ c₂ x = 0 := approx_of_mem_C _ _ (h hx)
      _ <= approx n₁ c₁ x := approx_nonneg _ _ _
  · calc
      approx n₂ c₂ x <= 1 := approx_le_one _ _ _
      _ = approx n₁ c₁ x := (approx_of_notMem_U _ _ hx).symm

Depends on / 依赖: approx, approx_le_one, approx_nonneg, approx_of_mem_C, approx_of_notMem_U
-/
theorem approx_le_approx_of_U_sub_C {c₁ c₂ : CU P} (h : c₁.U subseteq c₂.C) (n₁ n₂ : Nat) (x : X) :
    c₂.approx n₂ x <= c₁.approx n₁ x := by
  by_cases hx : x in c₁.U
  · calc
      approx n₂ c₂ x = 0 := approx_of_mem_C _ _ (h hx)
      _ <= approx n₁ c₁ x := approx_nonneg _ _ _
  · calc
      approx n₂ c₂ x <= 1 := approx_le_one _ _ _
      _ = approx n₁ c₁ x := (approx_of_notMem_U _ _ hx).symm

/--
theorem `approx_mem_Icc_right_left` / 定理 `approx_mem_Icc_right_left`

English:
theorem approx_mem_Icc_right_left
  given: (c : CU P) (n : Nat) (x : X)
  proof: by
  induction n generalizing c with
  | zero =>
    simp only [approx]
    refine ⟨le_rfl, ?_⟩
    grw [left_U_subset]
    rw [Pi.one_apply]; positivity -- TODO: `positivity` doesn't prove that `1 x` is nonnegative
  | succ n ihn =>
    simp only [approx, mem_Icc]
    refine ⟨midpoint_le_midpoint ?

中文:
定理 approx_mem_Icc_right_left
  条件: (c : CU P) (n : 自然数) (x : X)
  证明: by
  induction n generalizing c with
  | zero =>
    simp only [approx]
    refine ⟨le_rfl, ?_⟩
    grw [left_U_subset]
    rw [Pi.one_apply]; positivity -- TODO: `positivity` doesn't prove that `1 x` is nonnegative
  | succ n ihn =>
    simp only [approx, mem_Icc]
    refine ⟨midpoint_le_midpoint ?

Depends on / 依赖: Pi.one_apply, approx, approx_le_approx_of_U_sub_C, exacts, generalizing, le_rfl, left_U_subset, mem_Icc, midpoint_le_midpoint, nonnegative, one_apply, subset_closure
-/
theorem approx_mem_Icc_right_left (c : CU P) (n : Nat) (x : X) :
    c.approx n x in Icc (c.right.approx n x) (c.left.approx n x) := by
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

/--
theorem `approx_le_succ` / 定理 `approx_le_succ`

English:
theorem approx_le_succ
  given: (c : CU P) (n : Nat) (x : X)
  statement: c.approx n x <= c.approx (n + 1) x
  proof: by
  induction n generalizing c with
  | zero =>
    simp only [approx, right_U, right_le_midpoint]
    exact (approx_mem_Icc_right_left c 0 x).2
  | succ n ihn =>
    rw [approx]; rw [approx]
    exact midpoint_le_midpoint (ihn _) (ihn _)

中文:
定理 approx_le_succ
  条件: (c : CU P) (n : 自然数) (x : X)
  结论: c.approx n x <= c.approx (n + 1) x
  证明: by
  induction n generalizing c with
  | zero =>
    simp only [approx, right_U, right_le_midpoint]
    exact (approx_mem_Icc_right_left c 0 x).2
  | succ n ihn =>
    rw [approx]; rw [approx]
    exact midpoint_le_midpoint (ihn _) (ihn _)

Depends on / 依赖: approx, approx_mem_Icc_right_left, generalizing, midpoint_le_midpoint, right_U, right_le_midpoint
-/
theorem approx_le_succ (c : CU P) (n : Nat) (x : X) : c.approx n x <= c.approx (n + 1) x := by
  induction n generalizing c with
  | zero =>
    simp only [approx, right_U, right_le_midpoint]
    exact (approx_mem_Icc_right_left c 0 x).2
  | succ n ihn =>
    rw [approx]; rw [approx]
    exact midpoint_le_midpoint (ihn _) (ihn _)

/--
theorem `approx_mono` / 定理 `approx_mono`

English:
theorem approx_mono
  given: (c : CU P) (x : X)
  statement: Monotone fun n => c.approx n x
  proof: monotone_nat_of_le_succ fun n => c.approx_le_succ n x

中文:
定理 approx_mono
  条件: (c : CU P) (x : X)
  结论: 递增 fun n => c.approx n x
  证明: monotone_nat_of_le_succ fun n => c.approx_le_succ n x

Depends on / 依赖: approx_le_succ, c.approx_le_succ, monotone_nat_of_le_succ
-/
theorem approx_mono (c : CU P) (x : X) : Monotone fun n => c.approx n x :=
  monotone_nat_of_le_succ fun n => c.approx_le_succ n x

/--
Definition of `lim` / `lim` 的定义

English:
definition lim
  signature: (c : CU P) (x : X)
  body: ⨆ n, c.approx n x

中文:
定义 lim
  签名: (c : CU P) (x : X)
  定义体: ⨆ n, c.approx n x
-/
protected def lim (c : CU P) (x : X) : Real :=
  ⨆ n, c.approx n x

/--
theorem `tendsto_approx_atTop` / 定理 `tendsto_approx_atTop`

English:
theorem tendsto_approx_atTop
  given: (c : CU P) (x : X)
  proof: tendsto_atTop_ciSup (c.approx_mono x) ⟨1, fun _ ⟨_, hn⟩ => hn ▸ c.approx_le_one _ _⟩

中文:
定理 tendsto_approx_atTop
  条件: (c : CU P) (x : X)
  证明: tendsto_atTop_ciSup (c.approx_mono x) ⟨1, fun _ ⟨_, hn⟩ => hn ▸ c.approx_le_one _ _⟩

Depends on / 依赖: approx_le_one, approx_mono, c.approx_le_one, c.approx_mono, tendsto_atTop_ciSup
-/
theorem tendsto_approx_atTop (c : CU P) (x : X) :
    Tendsto (fun n => c.approx n x) atTop (𝓝 <| c.lim x) :=
  tendsto_atTop_ciSup (c.approx_mono x) ⟨1, fun _ ⟨_, hn⟩ => hn ▸ c.approx_le_one _ _⟩

/--
theorem `lim_of_mem_C` / 定理 `lim_of_mem_C`

English:
theorem lim_of_mem_C
  given: (c : CU P) (x : X) (h : x in c.C)
  statement: c.lim x = 0
  proof: by
  simp only [CU.lim, approx_of_mem_C, h, ciSup_const]

中文:
定理 lim_of_mem_C
  条件: (c : CU P) (x : X) (h : x in c.C)
  结论: c.lim x = 0
  证明: by
  simp only [CU.lim, approx_of_mem_C, h, ciSup_const]

Depends on / 依赖: CU.lim, approx_of_mem_C, ciSup_const
-/
theorem lim_of_mem_C (c : CU P) (x : X) (h : x in c.C) : c.lim x = 0 := by
  simp only [CU.lim, approx_of_mem_C, h, ciSup_const]

/--
theorem `disjoint_C_support_lim` / 定理 `disjoint_C_support_lim`

English:
theorem disjoint_C_support_lim
  given: (c : CU P)
  statement: Disjoint c.C (Function.support c.lim)
  proof: Function.disjoint_support_iff.mpr (fun x hx => lim_of_mem_C c x hx)

中文:
定理 disjoint_C_support_lim
  条件: (c : CU P)
  结论: Disjoint c.C (函数.support c.lim)
  证明: Function.disjoint_support_iff.mpr (fun x hx => lim_of_mem_C c x hx)

Depends on / 依赖: Function, Function.disjoint_support_iff.mpr, disjoint_support_iff, lim_of_mem_C
-/
theorem disjoint_C_support_lim (c : CU P) : Disjoint c.C (Function.support c.lim) :=
  Function.disjoint_support_iff.mpr (fun x hx => lim_of_mem_C c x hx)

/--
theorem `lim_of_notMem_U` / 定理 `lim_of_notMem_U`

English:
theorem lim_of_notMem_U
  given: (c : CU P) (x : X) (h : x ∉ c.U)
  statement: c.lim x = 1
  proof: by
  simp only [CU.lim, approx_of_notMem_U c _ h, ciSup_const]

中文:
定理 lim_of_notMem_U
  条件: (c : CU P) (x : X) (h : x ∉ c.U)
  结论: c.lim x = 1
  证明: by
  simp only [CU.lim, approx_of_notMem_U c _ h, ciSup_const]

Depends on / 依赖: CU.lim, approx_of_notMem_U, ciSup_const
-/
theorem lim_of_notMem_U (c : CU P) (x : X) (h : x ∉ c.U) : c.lim x = 1 := by
  simp only [CU.lim, approx_of_notMem_U c _ h, ciSup_const]

/--
theorem `lim_eq_midpoint` / 定理 `lim_eq_midpoint`

English:
theorem lim_eq_midpoint
  given: (c : CU P) (x : X)
  proof: by
  refine tendsto_nhds_unique (c.tendsto_approx_atTop x) ((tendsto_add_atTop_iff_nat 1).1 ?_)
  simp only [approx]
  exact (c.left.tendsto_approx_atTop x).midpoint (c.right.tendsto_approx_atTop x)

中文:
定理 lim_eq_midpoint
  条件: (c : CU P) (x : X)
  证明: by
  refine tendsto_nhds_unique (c.tendsto_approx_atTop x) ((tendsto_add_atTop_iff_nat 1).1 ?_)
  simp only [approx]
  exact (c.left.tendsto_approx_atTop x).midpoint (c.right.tendsto_approx_atTop x)

Depends on / 依赖: approx, c.left.tendsto_approx_atTop, c.right.tendsto_approx_atTop, c.tendsto_approx_atTop, midpoint, tendsto_add_atTop_iff_nat, tendsto_approx_atTop, tendsto_nhds_unique
-/
theorem lim_eq_midpoint (c : CU P) (x : X) :
    c.lim x = midpoint Real (c.left.lim x) (c.right.lim x) := by
  refine tendsto_nhds_unique (c.tendsto_approx_atTop x) ((tendsto_add_atTop_iff_nat 1).1 ?_)
  simp only [approx]
  exact (c.left.tendsto_approx_atTop x).midpoint (c.right.tendsto_approx_atTop x)

/--
theorem `approx_le_lim` / 定理 `approx_le_lim`

English:
theorem approx_le_lim
  given: (c : CU P) (x : X) (n : Nat)
  statement: c.approx n x <= c.lim x
  proof: le_ciSup (c.bddAbove_range_approx x) _

中文:
定理 approx_le_lim
  条件: (c : CU P) (x : X) (n : 自然数)
  结论: c.approx n x <= c.lim x
  证明: le_ciSup (c.bddAbove_range_approx x) _

Depends on / 依赖: bddAbove_range_approx, c.bddAbove_range_approx, le_ciSup
-/
theorem approx_le_lim (c : CU P) (x : X) (n : Nat) : c.approx n x <= c.lim x :=
  le_ciSup (c.bddAbove_range_approx x) _

/--
theorem `lim_nonneg` / 定理 `lim_nonneg`

English:
theorem lim_nonneg
  given: (c : CU P) (x : X)
  statement: 0 <= c.lim x
  proof: (c.approx_nonneg 0 x).trans (c.approx_le_lim x 0)

中文:
定理 lim_nonneg
  条件: (c : CU P) (x : X)
  结论: 0 <= c.lim x
  证明: (c.approx_nonneg 0 x).trans (c.approx_le_lim x 0)

Depends on / 依赖: approx_le_lim, approx_nonneg, c.approx_le_lim, c.approx_nonneg
-/
theorem lim_nonneg (c : CU P) (x : X) : 0 <= c.lim x :=
  (c.approx_nonneg 0 x).trans (c.approx_le_lim x 0)

/--
theorem `lim_le_one` / 定理 `lim_le_one`

English:
theorem lim_le_one
  given: (c : CU P) (x : X)
  statement: c.lim x <= 1
  proof: ciSup_le fun _ => c.approx_le_one _ _

中文:
定理 lim_le_one
  条件: (c : CU P) (x : X)
  结论: c.lim x <= 1
  证明: ciSup_le fun _ => c.approx_le_one _ _

Depends on / 依赖: approx_le_one, c.approx_le_one, ciSup_le
-/
theorem lim_le_one (c : CU P) (x : X) : c.lim x <= 1 :=
  ciSup_le fun _ => c.approx_le_one _ _

/--
theorem `lim_mem_Icc` / 定理 `lim_mem_Icc`

English:
theorem lim_mem_Icc
  given: (c : CU P) (x : X)
  statement: c.lim x in Icc (0 : Real) 1
  proof: ⟨c.lim_nonneg x, c.lim_le_one x⟩

中文:
定理 lim_mem_Icc
  条件: (c : CU P) (x : X)
  结论: c.lim x in 闭区间 (0 : 实数) 1
  证明: ⟨c.lim_nonneg x, c.lim_le_one x⟩

Depends on / 依赖: c.lim_le_one, c.lim_nonneg, lim_le_one, lim_nonneg
-/
theorem lim_mem_Icc (c : CU P) (x : X) : c.lim x in Icc (0 : Real) 1 :=
  ⟨c.lim_nonneg x, c.lim_le_one x⟩

/--
theorem `continuous_lim` / 定理 `continuous_lim`

English:
theorem continuous_lim
  given: (c : CU P)
  statement: Continuous c.lim
  proof: by
  obtain ⟨h0, h1234, h1⟩ : 0 < (2⁻¹ : Real) ∧ (2⁻¹ : Real) < 3 / 4 ∧ (3 / 4 : Real) < 1 := by norm_num
  refine
    continuous_iff_continuousAt.2 fun x =>
      (Metric.nhds_basis_closedBall_pow (h0.trans h1234) h1).tendsto_right_iff.2 fun n _ => ?_
  simp only [Metric.mem_closedBall]
  induction

中文:
定理 continuous_lim
  条件: (c : CU P)
  结论: 连续 c.lim
  证明: by
  obtain ⟨h0, h1234, h1⟩ : 0 < (2⁻¹ : Real) ∧ (2⁻¹ : Real) < 3 / 4 ∧ (3 / 4 : Real) < 1 := by norm_num
  refine
    continuous_iff_continuousAt.2 fun x =>
      (Metric.nhds_basis_closedBall_pow (h0.trans h1234) h1).tendsto_right_iff.2 fun n _ => ?_
  simp only [Metric.mem_closedBall]
  induction

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, Metric, Metric.mem_closedBall, Metric.nhds_basis_closedBall_pow, Real.dist_le_of_mem_Icc_01, c.left.U, c.lim_mem_Icc, continuous_iff_continuousAt, dist_le_of_mem_Icc_01, filter_upwards, generalizing, h0.trans, lim_mem_Icc, mem_closedBall, mem_nhds, nhds_basis_closedBall_pow, pow_zero, tendsto_right_iff
-/
theorem continuous_lim (c : CU P) : Continuous c.lim := by
  obtain ⟨h0, h1234, h1⟩ : 0 < (2⁻¹ : Real) ∧ (2⁻¹ : Real) < 3 / 4 ∧ (3 / 4 : Real) < 1 := by norm_num
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
    by_cases hxl : x in c.left.U
    · filter_upwards [IsOpen.mem_nhds c.left.open_U hxl, ihn c.left] with _ hyl hyd
      rw [pow_succ']; rw [c.lim_eq_midpoint]; rw [c.lim_eq_midpoint]; rw [c.right.lim_of_mem_C _ (c.left_U_subset_right_C hyl)]; rw [c.right.lim_of_mem_C _ (c.left_U_subset_right_C hxl)]
      refine (dist_midpoint_midpoint_le _ _ _ _).trans ?_
      rw [dist_self]; rw [add_zero]; rw [div_eq_inv_mul]
      gcongr
    · replace hxl : x in c.left.right.Cᶜ :=
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
      set r := (3 / 4 : Real) ^ n
      calc _ <= (r / 2 + r) / 2 := by gcongr
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
/--
theorem `exists_continuous_zero_one_of_isClosed` / 定理 `exists_continuous_zero_one_of_isClosed`

English:
theorem exists_continuous_zero_one_of_isClosed
  statement: [NormalSpace X]
  proof: by
  -- The actual proof is in the code above. Here we just repack it into the expected format.
  let P : Set X -> Set X -> Prop := fun _ _ => True
  set c : Urysohns.CU P :=
  { C := s
    U := tᶜ
    P_C_U := trivial
    closed_C := hs
    open_U := ht.isOpen_compl
    subset := disjoint_left.1 hd

中文:
定理 存在_continuous_zero_one_of_isClosed
  结论: [正规空间 X]
  证明: by
  -- The actual proof is in the code above. Here we just repack it into the expected format.
  let P : Set X -> Set X -> Prop := fun _ _ => True
  set c : Urysohns.CU P :=
  { C := s
    U := tᶜ
    P_C_U := trivial
    closed_C := hs
    open_U := ht.isOpen_compl
    subset := disjoint_left.1 hd
-/
theorem exists_continuous_zero_one_of_isClosed [NormalSpace X]
    {s t : Set X} (hs : IsClosed s) (ht : IsClosed t)
    (hd : Disjoint s t) : exists f : C(X, Real), EqOn f 0 s ∧ EqOn f 1 t ∧ forall x, f x in Icc (0 : Real) 1 := by
  -- The actual proof is in the code above. Here we just repack it into the expected format.
  let P : Set X -> Set X -> Prop := fun _ _ => True
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

/--
theorem `exists_continuous_zero_one_of_isCompact` / 定理 `exists_continuous_zero_one_of_isCompact`

English:
theorem exists_continuous_zero_one_of_isCompact
  statement: [RegularSpace X] [LocallyCompactSpace X]
  proof: by
  obtain ⟨k, k_comp, k_closed, sk, kt⟩ : exists k, IsCompact k ∧ IsClosed k ∧ s subseteq interior k ∧ k subseteq tᶜ :=
    exists_compact_closed_between hs ht.isOpen_compl hd.symm.subset_compl_left
  let P : Set X -> Set X -> Prop := fun C _ => IsCompact C
  set c : Urysohns.CU P :=
  { C := k
  

中文:
定理 存在_continuous_zero_one_of_isCompact
  结论: [正则空间 X] [局部紧空间 X]
  证明: by
  obtain ⟨k, k_comp, k_closed, sk, kt⟩ : exists k, IsCompact k ∧ IsClosed k ∧ s subseteq interior k ∧ k subseteq tᶜ :=
    exists_compact_closed_between hs ht.isOpen_compl hd.symm.subset_compl_left
  let P : Set X -> Set X -> Prop := fun C _ => IsCompact C
  set c : Urysohns.CU P :=
  { C := k
  

Depends on / 依赖: IsClosed, IsCompact, P_C_U, Urysohns, Urysohns.CU, c_comp, closed_C, exists_compact_closed_between, hd.symm.subset_compl_left, ht.isOpen_compl, interior, isOpen_compl, k_closed, k_comp, open_U, subset, subset_compl_left, subseteq, u_open
-/
theorem exists_continuous_zero_one_of_isCompact [RegularSpace X] [LocallyCompactSpace X]
    {s t : Set X} (hs : IsCompact s) (ht : IsClosed t) (hd : Disjoint s t) :
    exists f : C(X, Real), EqOn f 0 s ∧ EqOn f 1 t ∧ forall x, f x in Icc (0 : Real) 1 := by
  obtain ⟨k, k_comp, k_closed, sk, kt⟩ : exists k, IsCompact k ∧ IsClosed k ∧ s subseteq interior k ∧ k subseteq tᶜ :=
    exists_compact_closed_between hs ht.isOpen_compl hd.symm.subset_compl_left
  let P : Set X -> Set X -> Prop := fun C _ => IsCompact C
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
      have A : closure (interior k) subseteq k :=
        (IsClosed.closure_subset_iff k_closed).2 interior_subset
      refine ⟨interior k, isOpen_interior, ck, A.trans ku, c_comp,
        k_comp.of_isClosed_subset isClosed_closure A⟩ }
  exact ⟨⟨c.lim, c.continuous_lim⟩, fun x hx => c.lim_of_mem_C _ (sk.trans interior_subset hx),
    fun x hx => c.lim_of_notMem_U _ fun h => h hx, c.lim_mem_Icc⟩

/--
theorem `exists_continuous_zero_one_of_isCompact'` / 定理 `exists_continuous_zero_one_of_isCompact'`

English:
theorem exists_continuous_zero_one_of_isCompact'
  statement: [RegularSpace X] [LocallyCompactSpace X]
  proof: by
  obtain ⟨g, hgs, hgt, (hicc : forall x, 0 <= g x ∧ g x <= 1)⟩ := exists_continuous_zero_one_of_isCompact
    hs ht hd
  use 1 - g
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [ContinuousMap.sub_apply, ContinuousMap.one_apply, Pi.zero_apply]
    exact sub_eq_zero_of_eq (hgt.symm hx)
  · int

中文:
定理 存在_continuous_zero_one_of_isCompact'
  结论: [正则空间 X] [局部紧空间 X]
  证明: by
  obtain ⟨g, hgs, hgt, (hicc : forall x, 0 <= g x ∧ g x <= 1)⟩ := exists_continuous_zero_one_of_isCompact
    hs ht hd
  use 1 - g
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [ContinuousMap.sub_apply, ContinuousMap.one_apply, Pi.zero_apply]
    exact sub_eq_zero_of_eq (hgt.symm hx)
  · int

Depends on / 依赖: ContinuousMap, ContinuousMap.one_apply, ContinuousMap.sub_apply, Pi.one_apply, Pi.zero_apply, and_comm, exists_continuous_zero_one_of_isCompact, hgt.symm, one_apply, sub_apply, sub_eq_self, sub_eq_zero_of_eq, zero_apply
-/
theorem exists_continuous_zero_one_of_isCompact' [RegularSpace X] [LocallyCompactSpace X]
    {s t : Set X} (hs : IsCompact s) (ht : IsClosed t) (hd : Disjoint s t) :
    exists f : C(X, Real), EqOn f 0 t ∧ EqOn f 1 s ∧ forall x, f x in Icc (0 : Real) 1 := by
  obtain ⟨g, hgs, hgt, (hicc : forall x, 0 <= g x ∧ g x <= 1)⟩ := exists_continuous_zero_one_of_isCompact
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

/--
theorem `exists_continuous_one_zero_of_isCompact` / 定理 `exists_continuous_one_zero_of_isCompact`

English:
theorem exists_continuous_one_zero_of_isCompact
  statement: [RegularSpace X] [LocallyCompactSpace X]
  proof: by
  obtain ⟨k, k_comp, k_closed, sk, kt⟩ : exists k, IsCompact k ∧ IsClosed k ∧ s subseteq interior k ∧ k subseteq tᶜ :=
    exists_compact_closed_between hs ht.isOpen_compl hd.symm.subset_compl_left
  rcases exists_continuous_zero_one_of_isCompact hs isOpen_interior.isClosed_compl
    (disjoint_co

中文:
定理 存在_continuous_one_zero_of_isCompact
  结论: [正则空间 X] [局部紧空间 X]
  证明: by
  obtain ⟨k, k_comp, k_closed, sk, kt⟩ : exists k, IsCompact k ∧ IsClosed k ∧ s subseteq interior k ∧ k subseteq tᶜ :=
    exists_compact_closed_between hs ht.isOpen_compl hd.symm.subset_compl_left
  rcases exists_continuous_zero_one_of_isCompact hs isOpen_interior.isClosed_compl
    (disjoint_co

Depends on / 依赖: IsClosed, IsCompact, disjoint_compl_right_iff_subset, disjoint_compl_right_iff_subset.mpr, exists_compact_closed_between, exists_continuous_zero_one_of_isCompact, fun_prop, hd.symm.subset_compl_left, ht.isOpen_compl, interior, interior_subset, interior_subset.trans, isClosed_compl, isOpen_compl, isOpen_interior, isOpen_interior.isClosed_compl, k_closed, k_comp, subset_compl_comm, subset_compl_comm.mpr
-/
theorem exists_continuous_one_zero_of_isCompact [RegularSpace X] [LocallyCompactSpace X]
    {s t : Set X} (hs : IsCompact s) (ht : IsClosed t) (hd : Disjoint s t) :
    exists f : C(X, Real), EqOn f 1 s ∧ EqOn f 0 t ∧ HasCompactSupport f ∧ forall x, f x in Icc (0 : Real) 1 := by
  obtain ⟨k, k_comp, k_closed, sk, kt⟩ : exists k, IsCompact k ∧ IsClosed k ∧ s subseteq interior k ∧ k subseteq tᶜ :=
    exists_compact_closed_between hs ht.isOpen_compl hd.symm.subset_compl_left
  rcases exists_continuous_zero_one_of_isCompact hs isOpen_interior.isClosed_compl
    (disjoint_compl_right_iff_subset.mpr sk) with ⟨⟨f, hf⟩, hfs, hft, h'f⟩
  have A : t subseteq (interior k)ᶜ := subset_compl_comm.mpr (interior_subset.trans kt)
  refine ⟨⟨fun x => 1 - f x, by fun_prop⟩, fun x hx => by simpa using hfs hx,
    fun x hx => by simpa [sub_eq_zero] using (hft (A hx)).symm, ?_, fun x => ?_⟩
  · apply HasCompactSupport.intro' k_comp k_closed (fun x hx => ?_)
    simp only [ContinuousMap.coe_mk, sub_eq_zero]
    apply (hft _).symm
    contrapose hx
    simp only [mem_compl_iff, not_not] at hx
    exact interior_subset hx
  · have : 0 <= f x ∧ f x <= 1 := by simpa using h'f x
    simp [this]

/--
theorem `exists_continuous_one_zero_of_isCompact_of_isGδ` / 定理 `exists_continuous_one_zero_of_isCompact_of_isGδ`

English:
theorem exists_continuous_one_zero_of_isCompact_of_isGδ
  statement: [RegularSpace X] [LocallyCompactSpace X]
  proof: by
  rcases h's.eq_iInter_nat with ⟨U, U_open, hU⟩
  obtain ⟨m, m_comp, -, sm, mt⟩ : exists m, IsCompact m ∧ IsClosed m ∧ s subseteq interior m ∧ m subseteq tᶜ :=
    exists_compact_closed_between hs ht.isOpen_compl hd.symm.subset_compl_left
  have A n : exists f : C(X, Real), EqOn f 1 s ∧ EqOn f 0 

中文:
定理 存在_continuous_one_zero_of_isCompact_of_isGδ
  结论: [正则空间 X] [局部紧空间 X]
  证明: by
  rcases h's.eq_iInter_nat with ⟨U, U_open, hU⟩
  obtain ⟨m, m_comp, -, sm, mt⟩ : exists m, IsCompact m ∧ IsClosed m ∧ s subseteq interior m ∧ m subseteq tᶜ :=
    exists_compact_closed_between hs ht.isOpen_compl hd.symm.subset_compl_left
  have A n : exists f : C(X, Real), EqOn f 1 s ∧ EqOn f 0 

Depends on / 依赖: HasCompactSupport, IsClosed, IsCompact, U_open, disjoint_compl_righ, eq_iInter_nat, exists_compact_closed_between, exists_continuous_one_zero_of_isCompact, hd.symm.subset_compl_left, ht.isOpen_compl, interior, isClosed_compl, isOpen_compl, isOpen_interior, m_comp, s.eq_iInter_nat, subset_compl_left, subseteq
-/
theorem exists_continuous_one_zero_of_isCompact_of_isGδ [RegularSpace X] [LocallyCompactSpace X]
    {s t : Set X} (hs : IsCompact s) (h's : IsGδ s) (ht : IsClosed t) (hd : Disjoint s t) :
    exists f : C(X, Real), s = f ⁻¹' {1} ∧ EqOn f 0 t ∧ HasCompactSupport f
      ∧ forall x, f x in Icc (0 : Real) 1 := by
  rcases h's.eq_iInter_nat with ⟨U, U_open, hU⟩
  obtain ⟨m, m_comp, -, sm, mt⟩ : exists m, IsCompact m ∧ IsClosed m ∧ s subseteq interior m ∧ m subseteq tᶜ :=
    exists_compact_closed_between hs ht.isOpen_compl hd.symm.subset_compl_left
  have A n : exists f : C(X, Real), EqOn f 1 s ∧ EqOn f 0 (U n inter interior m)ᶜ ∧ HasCompactSupport f
      ∧ forall x, f x in Icc (0 : Real) 1 := by
    apply exists_continuous_one_zero_of_isCompact hs
      ((U_open n).inter isOpen_interior).isClosed_compl
    rw [disjoint_compl_right_iff_subset]
    exact subset_inter ((hU.subset.trans (iInter_subset U n))) sm
  choose f fs fm _hf f_range using A
  obtain ⟨u, u_pos, u_sum, hu⟩ : exists (u : Nat -> Real), (forall i, 0 < u i) ∧ Summable u ∧ ∑' i, u i = 1 :=
    ⟨fun n => 1/2/2^n, fun n => by positivity, summable_geometric_two' 1, tsum_geometric_two' 1⟩
  let g : X -> Real := fun x => ∑' n, u n * f n x
  have hgmc : EqOn g 0 mᶜ := by
    intro x hx
    have B n : f n x = 0 := by
      have : mᶜ subseteq (U n inter interior m)ᶜ := by
        simpa using inter_subset_right.trans interior_subset
      exact fm n (this hx)
    simp [g, B]
  have I n x : u n * f n x <= u n := mul_le_of_le_one_right (u_pos n).le (f_range n x).2
  have S x : Summable (fun n => u n * f n x) := Summable.of_nonneg_of_le
      (fun n => mul_nonneg (u_pos n).le (f_range n x).1) (fun n => I n x) u_sum
  refine ⟨⟨g, ?_⟩, ?_, hgmc.mono (subset_compl_comm.mp mt), ?_, fun x => ⟨?_, ?_⟩⟩
  · apply continuous_tsum (fun n => by fun_prop) u_sum (fun n x => ?_)
    simpa [abs_of_nonneg, (u_pos n).le, (f_range n x).1] using I n x
  · apply Subset.antisymm (fun x hx => by simp [g, fs _ hx, hu]) ?_
    apply compl_subset_compl.1
    intro x hx
    obtain ⟨n, hn⟩ : exists n, x ∉ U n := by simpa [hU] using hx
    have fnx : f n x = 0 := fm _ (by simp [hn])
    have : g x < 1 := by
      apply lt_of_lt_of_le ?_ hu.le
      exact (S x).tsum_lt_tsum (i := n) (fun i => I i x) (by simp [fnx, u_pos n]) u_sum
    simpa using this.ne
  · exact HasCompactSupport.of_support_subset_isCompact m_comp
      (Function.support_subset_iff'.mpr hgmc)
  · exact tsum_nonneg (fun n => mul_nonneg (u_pos n).le (f_range n x).1)
  · apply le_trans _ hu.le
    exact (S x).tsum_le_tsum (fun n => I n x) u_sum

/--
lemma `exists_tsupport_one_of_isOpen_isClosed` / 引理 `exists_tsupport_one_of_isOpen_isClosed`

English:
lemma exists_tsupport_one_of_isOpen_isClosed
  statement: [R1Space X] {s t : Set X}
  proof: by

中文:
引理 存在_tsupport_one_of_isOpen_isClosed
  结论: [R1空间 X] {s t : 集合 X}
  证明: by
-/
lemma exists_tsupport_one_of_isOpen_isClosed [R1Space X] {s t : Set X}
    (hs : IsOpen s) (hscp : IsCompact (closure s)) (ht : IsClosed t) (hst : t subseteq s) :
    exists f : C(X, Real), tsupport f subseteq s ∧ EqOn f 1 t ∧ forall x, f x in Icc (0 : Real) 1 := by
-- separate `sᶜ` and `t` by `u` and `v`.
  rw [← compl_compl s] at hscp
  obtain ⟨u, v, huIsOpen, hvIsOpen, hscompl_subset_u, ht_subset_v, hDisjointuv⟩ :=
    SeparatedNhds.of_isClosed_isCompact_closure_compl_isClosed (isClosed_compl_iff.mpr hs)
    hscp ht (LE.le.disjoint_compl_left hst)
  rw [← subset_compl_iff_disjoint_right] at hDisjointuv
  have huvc : closure u subseteq vᶜ := closure_minimal hDisjointuv hvIsOpen.isClosed_compl
-- although `sᶜ` is not compact, `closure s` is compact and we can apply
-- `SeparatedNhds.of_isClosed_isCompact_closure_compl_isClosed`. To apply the condition
-- recursively, we need to make sure that `sᶜ ⊆ C`.
  let P : Set X -> Set X -> Prop := fun C _ => sᶜ subseteq C
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
.trans hv1u } exact closure_minimal hu1v1 hv1.isClosed_compl
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

/--
lemma `exists_continuousMap_one_of_isCompact_subset_isOpen` / 引理 `exists_continuousMap_one_of_isCompact_subset_isOpen`

English:
lemma exists_continuousMap_one_of_isCompact_subset_isOpen
  statement: [R1Space X] [LocallyCompactSpace X]
  proof: by
  obtain ⟨U, hU1, hU2, hU3, hU4⟩ := exists_open_between_and_isCompact_closure hK hV hKV
  obtain ⟨f, hf1, hf2, hf3⟩ := exists_tsupport_one_of_isOpen_isClosed hU1 hU4
    isClosed_closure (hK.closure_subset_of_isOpen hU1 hU2)
  have hfU : tsupport f subseteq closure U := hf1.trans subset_closure
 

中文:
引理 存在_continuousMap_one_of_isCompact_subset_isOpen
  结论: [R1空间 X] [局部紧空间 X]
  证明: by
  obtain ⟨U, hU1, hU2, hU3, hU4⟩ := exists_open_between_and_isCompact_closure hK hV hKV
  obtain ⟨f, hf1, hf2, hf3⟩ := exists_tsupport_one_of_isOpen_isClosed hU1 hU4
    isClosed_closure (hK.closure_subset_of_isOpen hU1 hU2)
  have hfU : tsupport f subseteq closure U := hf1.trans subset_closure
 

Depends on / 依赖: closure, closure_subset_of_isOpen, exists_open_between_and_isCompact_closure, exists_tsupport_one_of_isOpen_isClosed, hK.closure_subset_of_isOpen, hf1.trans, hf2.mono, hfU.trans, isClosed_closure, of_isClosed_subset, subset_closure, subseteq, tsupport
-/
lemma exists_continuousMap_one_of_isCompact_subset_isOpen [R1Space X] [LocallyCompactSpace X]
    {K V : Set X} (hK : IsCompact K) (hV : IsOpen V) (hKV : K subseteq V) :
    exists f : C(X, Real), Set.EqOn f 1 K ∧ IsCompact (tsupport f) ∧
      tsupport f subseteq V ∧ forall x, f x in Set.Icc 0 1 := by
  obtain ⟨U, hU1, hU2, hU3, hU4⟩ := exists_open_between_and_isCompact_closure hK hV hKV
  obtain ⟨f, hf1, hf2, hf3⟩ := exists_tsupport_one_of_isOpen_isClosed hU1 hU4
    isClosed_closure (hK.closure_subset_of_isOpen hU1 hU2)
  have hfU : tsupport f subseteq closure U := hf1.trans subset_closure
  exact ⟨f, hf2.mono subset_closure,
    .of_isClosed_subset hU4 isClosed_closure hfU, hfU.trans hU3, hf3⟩

/--
theorem `exists_continuous_nonneg_pos` / 定理 `exists_continuous_nonneg_pos`

English:
theorem exists_continuous_nonneg_pos
  given: [RegularSpace X] [LocallyCompactSpace X] (x : X)
  proof: by
  rcases exists_compact_mem_nhds x with ⟨k, hk, k_mem⟩
  rcases exists_continuous_one_zero_of_isCompact hk isClosed_empty (disjoint_empty k)
    with ⟨f, fk, -, f_comp, hf⟩
  refine ⟨f, f_comp, fun x => (hf x).1, ?_⟩
  have := fk (mem_of_mem_nhds k_mem)
  simp only [Pi.one_apply] at this
  simp [

中文:
定理 存在_continuous_nonneg_pos
  条件: [正则空间 X] [局部紧空间 X] (x : X)
  证明: by
  rcases exists_compact_mem_nhds x with ⟨k, hk, k_mem⟩
  rcases exists_continuous_one_zero_of_isCompact hk isClosed_empty (disjoint_empty k)
    with ⟨f, fk, -, f_comp, hf⟩
  refine ⟨f, f_comp, fun x => (hf x).1, ?_⟩
  have := fk (mem_of_mem_nhds k_mem)
  simp only [Pi.one_apply] at this
  simp [

Depends on / 依赖: Pi.one_apply, disjoint_empty, exists_compact_mem_nhds, exists_continuous_one_zero_of_isCompact, f_comp, isClosed_empty, k_mem, mem_of_mem_nhds, one_apply
-/
theorem exists_continuous_nonneg_pos [RegularSpace X] [LocallyCompactSpace X] (x : X) :
    exists f : C(X, Real), HasCompactSupport f ∧ 0 <= (f : X -> Real) ∧ f x != 0 := by
  rcases exists_compact_mem_nhds x with ⟨k, hk, k_mem⟩
  rcases exists_continuous_one_zero_of_isCompact hk isClosed_empty (disjoint_empty k)
    with ⟨f, fk, -, f_comp, hf⟩
  refine ⟨f, f_comp, fun x => (hf x).1, ?_⟩
  have := fk (mem_of_mem_nhds k_mem)
  simp only [Pi.one_apply] at this
  simp [this]
