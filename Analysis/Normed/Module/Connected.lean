/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Connectedness of subsets of vector spaces

We show several results related to the (path)-connectedness of subsets of real vector spaces:
* `Set.Countable.isPathConnected_compl_of_one_lt_rank` asserts that the complement of a countable
  set is path-connected in a space of dimension `> 1`.
* `isPathConnected_compl_singleton_of_one_lt_rank` is the special case of the complement of a
  singleton.
* `isPathConnected_sphere` shows that any sphere is path-connected in dimension `> 1`.
* `isPathConnected_compl_of_one_lt_codim` shows that the complement of a subspace
  of codimension `> 1` is path-connected.

Statements with connectedness instead of path-connectedness are also given.
-/

public section

assert_not_exists Subgroup.index Nat.divisors
-- TODO assert_not_exists Cardinal

open Set Metric
open scoped Convex ENNReal

section TopologicalVectorSpace

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]

/-- In a real vector space of dimension `> 1`, the complement of any countable set is path
connected. -/
/-
**Set.Countable.isPathConnected_compl_of_one_lt_rank** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：Set.Countable.isPathConnected_compl_of_one_lt_rank (h : 1 < Module.rank Re
al E) {s : Set E} (hs : s.Countable) : IsPathConnected sᶜ
参数：h : 1 < Module.rank Real E；hs : s.Countable。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `rank_pos_iff_nontrivial`：rank_pos_iff_nontrivial : 0 < Module.rank R M ↔
 Nontrivial M
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Dense.nonempty`：Dense.nonempty [h : Nonempty X] (hs : Dense s) : s.Nonem
pty
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `Set.Countable.dense_compl`：Set.Countable.dense_compl {E : Type u} (𝕜 : T
ype*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [AddCommGroup E] [Module 𝕜 E
] [Nontrivial E…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `JoinedIn.refl`：JoinedIn.refl (h : x in F) : JoinedIn F x x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval`：sub_eq_eval {R₁ R₂ S₁ S₂ : Type*} 
[AddCommGroup M] [Ring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂]
 [Module R₂ M] [Semiring S…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₁`：add_eq_eval₁ [AddMonoid M] [SMul 
R M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval + (a₂ ::ᵣ l₂).eva
l = l.eval) : (a₁ ::ᵣ l₁).e…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval₃`：sub_eq_eval₃ [Ring R] [AddCommGro
up M] [Module R M] {a₁ : R × M} (a₂ : R × M) {l₁ l₂ l : NF R M} (h : (a₁ ::ᵣ l₁)
.eval - l₂.eval = l.eval) :…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval₂`：sub_eq_eval₂ [Ring R] [AddCommGro
up M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval - l₂.eval
 = l.eval) : ((r₁, x) ::ᵣ l…
· 使用定理 `Mathlib.Tactic.Module.NF.zero_sub_eq_eval`：zero_sub_eq_eval [AddCommGrou
p M] [Ring R] [Module R M] (l : NF R M) : 0 - l.eval = (-l).eval
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 137 条，此处仅展示前 30 条）

--- 原说明 ---
In a real vector space of dimension `> 1`, the complement of any countable set i
s path
connected.
-/
theorem Set.Countable.isPathConnected_compl_of_one_lt_rank
    (h : 1 < Module.rank ℝ E) {s : Set E} (hs : s.Countable) :
    IsPathConnected sᶜ := by
  have : Nontrivial E := (rank_pos_iff_nontrivial (R := ℝ)).1 (zero_lt_one.trans h)
  -- the set `sᶜ` is dense, therefore nonempty. Pick `a ∈ sᶜ`. We have to show that any
  -- `b ∈ sᶜ` can be joined to `a`.
  obtain ⟨a, ha⟩ : sᶜ.Nonempty := (hs.dense_compl ℝ).nonempty
  refine ⟨a, ha, ?_⟩
  intro b hb
  rcases eq_or_ne a b with rfl | hab
  · exact JoinedIn.refl ha
  /- Assume `b ≠ a`. Write `a = c - x` and `b = c + x` for some nonzero `x`. Choose `y` which
  is linearly independent from `x`. Then the segments joining `a = c - x` to `c + ty` are pairwise
  disjoint for varying `t` (except for the endpoint `a`) so only countably many of them can
  intersect `s`. In the same way, there are countably many `t`s for which the segment
  from `b = c + x` to `c + ty` intersects `s`. Choosing `t` outside of these countable exceptions,
  one gets a path in the complement of `s` from `a` to `z = c + ty` and then to `b`.
  -/
  let c := (2 : ℝ)⁻¹ • (a + b)
  let x := (2 : ℝ)⁻¹ • (b - a)
  have Ia : c - x = a := by
    simp only [c, x]
    module
  have Ib : c + x = b := by
    simp only [c, x]
    module
  have x_ne_zero : x ≠ 0 := by simpa [x] using sub_ne_zero.2 hab.symm
  obtain ⟨y, hy⟩ : ∃ y, LinearIndependent ℝ ![x, y] :=
    exists_linearIndependent_pair_of_one_lt_rank h x_ne_zero
  have A : Set.Countable {t : ℝ | ([c + x -[ℝ] c + t • y] ∩ s).Nonempty} := by
    apply countable_ofPred_nonempty_of_disjoint _ (fun t ↦ inter_subset_right) hs
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.2
    have N : {c + x} ∩ s = ∅ := by
      simpa only [singleton_inter_eq_empty, mem_compl_iff, Ib] using hb
    rw [inter_assoc, inter_comm s, inter_assoc, inter_self, ← inter_assoc, ← subset_empty_iff, ← N]
    apply inter_subset_inter_left
    apply Eq.subset
    apply segment_inter_eq_endpoint_of_linearIndependent_of_ne hy htt'.symm
  have B : Set.Countable {t : ℝ | ([c - x -[ℝ] c + t • y] ∩ s).Nonempty} := by
    apply countable_ofPred_nonempty_of_disjoint _ (fun t ↦ inter_subset_right) hs
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.2
    have N : {c - x} ∩ s = ∅ := by
      simpa only [singleton_inter_eq_empty, mem_compl_iff, Ia] using ha
    rw [inter_assoc, inter_comm s, inter_assoc, inter_self, ← inter_assoc, ← subset_empty_iff, ← N]
    apply inter_subset_inter_left
    rw [sub_eq_add_neg _ x]
    apply Eq.subset
    apply segment_inter_eq_endpoint_of_linearIndependent_of_ne _ htt'.symm
    convert! hy.units_smul ![-1, 1]
    simp [← List.ofFn_inj]
  obtain ⟨t, ht⟩ : Set.Nonempty ({t : ℝ | ([c + x -[ℝ] c + t • y] ∩ s).Nonempty}
      ∪ {t : ℝ | ([c - x -[ℝ] c + t • y] ∩ s).Nonempty})ᶜ := ((A.union B).dense_compl ℝ).nonempty
  let z := c + t • y
  simp only [compl_union, mem_inter_iff, mem_compl_iff, mem_ofPred_eq, not_nonempty_iff_eq_empty]
    at ht
  have JA : JoinedIn sᶜ a z := by
    apply JoinedIn.of_segment_subset
    rw [subset_compl_iff_disjoint_right, disjoint_iff_inter_eq_empty]
    convert! ht.2
    exact Ia.symm
  have JB : JoinedIn sᶜ b z := by
    apply JoinedIn.of_segment_subset
    rw [subset_compl_iff_disjoint_right, disjoint_iff_inter_eq_empty]
    convert! ht.1
    exact Ib.symm
  exact JA.trans JB.symm

/-- In a real vector space of dimension `> 1`, the complement of any countable set is
connected. -/
/-
**Set.Countable.isConnected_compl_of_one_lt_rank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Countable.isConnected_compl_of_one_lt_rank (h : 1 < Module.rank Real E
) {s : Set E} (hs : s.Countable) : IsConnected sᶜ
参数：h : 1 < Module.rank Real E；hs : s.Countable。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPathConnected.isConnected`：IsPathConnected.isConnected (hF : IsPathCon
nected F) : IsConnected F
· 使用定理 `Set.Countable.isPathConnected_compl_of_one_lt_rank`：Set.Countable.isPath
Connected_compl_of_one_lt_rank (h : 1 < Module.rank Real E) {s : Set E} (hs : s.
Countable) : IsPathConnected sᶜ

--- 原说明 ---
In a real vector space of dimension `> 1`, the complement of any countable set i
s
connected.
-/
theorem Set.Countable.isConnected_compl_of_one_lt_rank (h : 1 < Module.rank ℝ E) {s : Set E}
    (hs : s.Countable) : IsConnected sᶜ :=
  (hs.isPathConnected_compl_of_one_lt_rank h).isConnected

/-- In a real vector space of dimension `> 1`, the complement of any singleton is path-connected. -/
/-
**isPathConnected_compl_singleton_of_one_lt_rank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPathConnected_compl_singleton_of_one_lt_rank (h : 1 < Module.rank Real E
) (x : E) : IsPathConnected {x}ᶜ
参数：h : 1 < Module.rank Real E；x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.isPathConnected_compl_of_one_lt_rank`：Set.Countable.isPath
Connected_compl_of_one_lt_rank (h : 1 < Module.rank Real E) {s : Set E} (hs : s.
Countable) : IsPathConnected sᶜ
· 使用定理 `Set.countable_singleton`：∀ {α : Type u} (a : α), {a}.Countable

--- 原说明 ---
In a real vector space of dimension `> 1`, the complement of any singleton is pa
th-connected.
-/
theorem isPathConnected_compl_singleton_of_one_lt_rank (h : 1 < Module.rank ℝ E) (x : E) :
    IsPathConnected {x}ᶜ :=
  Set.Countable.isPathConnected_compl_of_one_lt_rank h (countable_singleton x)

/-- In a real vector space of dimension `> 1`, the complement of a singleton is connected. -/
/-
**isConnected_compl_singleton_of_one_lt_rank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConnected_compl_singleton_of_one_lt_rank (h : 1 < Module.rank Real E) (x
 : E) : IsConnected {x}ᶜ
参数：h : 1 < Module.rank Real E；x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPathConnected.isConnected`：IsPathConnected.isConnected (hF : IsPathCon
nected F) : IsConnected F
· 使用定理 `isPathConnected_compl_singleton_of_one_lt_rank`：isPathConnected_compl_si
ngleton_of_one_lt_rank (h : 1 < Module.rank Real E) (x : E) : IsPathConnected {x
}ᶜ

--- 原说明 ---
In a real vector space of dimension `> 1`, the complement of a singleton is conn
ected.
-/
theorem isConnected_compl_singleton_of_one_lt_rank (h : 1 < Module.rank ℝ E) (x : E) :
    IsConnected {x}ᶜ :=
  (isPathConnected_compl_singleton_of_one_lt_rank h x).isConnected

end TopologicalVectorSpace

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Ball

namespace Metric

/-
**Metric.contractibleSpace_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：contractibleSpace_ball {x : E} {r : Real} (hr : 0 < r) : ContractibleSpace
 (ball x r)
参数：hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.contractibleSpace`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : _root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousAdd E]   [Conti
nuousSMul ℝ E]…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `convex_ball`：convex_ball (a : E) (r : Real) : Convex Real (ball a r)
-/
theorem contractibleSpace_ball {x : E} {r : ℝ} (hr : 0 < r) :
    ContractibleSpace (ball x r) :=
  (convex_ball _ _).contractibleSpace (by simpa)

@[deprecated (since := "2026-02-02")]
alias ball_contractible := contractibleSpace_ball
/-
**Metric.contractibleSpace_eball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：contractibleSpace_eball {x : E} {r : Real>=0∞} (hr : 0 < r) : Contractible
Space (eball x r)
参数：hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.contractibleSpace`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : _root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousAdd E]   [Conti
nuousSMul ℝ E]…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `convex_eball`：convex_eball (a : E) (r : ENNReal) : Convex Real (eball a 
r)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
-/
theorem contractibleSpace_eball {x : E} {r : ℝ≥0∞} (hr : 0 < r) :
    ContractibleSpace (eball x r) :=
  (convex_eball _ _).contractibleSpace ⟨x, by simpa⟩

@[deprecated (since := "2026-02-02")]
alias eball_contractible := contractibleSpace_eball
/-
**Metric.contractibleSpace_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：contractibleSpace_closedBall {x : E} {r : Real} (hr : 0 <= r) : Contractib
leSpace (closedBall x r)
参数：hr : 0 <= r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.contractibleSpace`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : _root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousAdd E]   [Conti
nuousSMul ℝ E]…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `convex_closedBall`：convex_closedBall (a : E) (r : Real) : Convex Real (c
losedBall a r)
-/
theorem contractibleSpace_closedBall {x : E} {r : ℝ} (hr : 0 ≤ r) :
    ContractibleSpace (closedBall x r) :=
  (convex_closedBall _ _).contractibleSpace (by simpa)
/-
**Metric.contractibleSpace_closedEBall** 是 Mathlib 中的一个实例，位于命名空间 `Metric`。
形式化陈述：contractibleSpace_closedEBall {x : E} {r : Real>=0∞} : ContractibleSpace (
closedEBall x r)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.contractibleSpace`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : _root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousAdd E]   [Conti
nuousSMul ℝ E]…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `convex_closedEBall`：convex_closedEBall (a : E) (r : ENNReal) : Convex Re
al (closedEBall a r)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
instance contractibleSpace_closedEBall {x : E} {r : ℝ≥0∞} :
    ContractibleSpace (closedEBall x r) :=
  (convex_closedEBall _ _).contractibleSpace ⟨x, by simp⟩
/-
**Metric.isPathConnected_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isPathConnected_ball {x : E} {r : Real} (hr : 0 < r) : IsPathConnected (ba
ll x r)
参数：hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.isPathConnected`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1
 : _root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousAdd E]   [Continu
ousSMul ℝ E]…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `convex_ball`：convex_ball (a : E) (r : Real) : Convex Real (ball a r)
-/
theorem isPathConnected_ball {x : E} {r : ℝ} (hr : 0 < r) :
    IsPathConnected (ball x r) :=
  convex_ball _ _ |>.isPathConnected <| by simpa
/-
**Metric.isPathConnected_eball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isPathConnected_eball {x : E} {r : Real>=0∞} (hr : 0 < r) : IsPathConnecte
d (eball x r)
参数：hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.isPathConnected`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1
 : _root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousAdd E]   [Continu
ousSMul ℝ E]…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `convex_eball`：convex_eball (a : E) (r : ENNReal) : Convex Real (eball a 
r)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
-/
theorem isPathConnected_eball {x : E} {r : ℝ≥0∞} (hr : 0 < r) :
    IsPathConnected (eball x r) :=
  convex_eball _ _ |>.isPathConnected ⟨x, by simpa⟩
/-
**Metric.isPathConnected_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isPathConnected_closedBall {x : E} {r : Real} (hr : 0 <= r) : IsPathConnec
ted (closedBall x r)
参数：hr : 0 <= r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.isPathConnected`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1
 : _root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousAdd E]   [Continu
ousSMul ℝ E]…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `convex_closedBall`：convex_closedBall (a : E) (r : Real) : Convex Real (c
losedBall a r)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
-/
theorem isPathConnected_closedBall {x : E} {r : ℝ} (hr : 0 ≤ r) :
    IsPathConnected (closedBall x r) :=
  convex_closedBall _ _ |>.isPathConnected ⟨x, by simpa⟩
/-
**Metric.isPathConnected_closedEBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isPathConnected_closedEBall {x : E} {r : Real>=0∞} : IsPathConnected (clos
edEBall x r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isPathConnected_iff_pathConnectedSpace`：isPathConnected_iff_pathConnecte
dSpace : IsPathConnected F ↔ PathConnectedSpace F
· 使用定理 `ContractibleSpace.instPathConnectedSpace`：∀ {X : Type u_1} [inst : Topol
ogicalSpace X] [ContractibleSpace X], PathConnectedSpace X
-/
theorem isPathConnected_closedEBall {x : E} {r : ℝ≥0∞} :
    IsPathConnected (closedEBall x r) :=
  isPathConnected_iff_pathConnectedSpace.mpr inferInstance
/-
**Metric.isPreconnected_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isPreconnected_ball {x : E} {r : Real} : IsPreconnected (ball x r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.isPreconnected`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 
: _root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousAdd E]   [Continuo
usSMul ℝ E]…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `convex_ball`：convex_ball (a : E) (r : Real) : Convex Real (ball a r)
-/
theorem isPreconnected_ball {x : E} {r : ℝ} : IsPreconnected (ball x r) :=
  (convex_ball _ _).isPreconnected
/-
**Metric.isPreconnected_eball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isPreconnected_eball {x : E} {r : Real>=0∞} : IsPreconnected (eball x r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.isPreconnected`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 
: _root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousAdd E]   [Continuo
usSMul ℝ E]…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `convex_eball`：convex_eball (a : E) (r : ENNReal) : Convex Real (eball a 
r)
-/
theorem isPreconnected_eball {x : E} {r : ℝ≥0∞} : IsPreconnected (eball x r) :=
  (convex_eball _ _).isPreconnected
/-
**Metric.isPreconnected_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isPreconnected_closedBall {x : E} {r : Real} : IsPreconnected (closedBall 
x r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.isPreconnected`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 
: _root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousAdd E]   [Continuo
usSMul ℝ E]…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `convex_closedBall`：convex_closedBall (a : E) (r : Real) : Convex Real (c
losedBall a r)
-/
theorem isPreconnected_closedBall {x : E} {r : ℝ} : IsPreconnected (closedBall x r) :=
  (convex_closedBall _ _).isPreconnected
/-
**Metric.isPreconnected_closedEBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isPreconnected_closedEBall {x : E} {r : Real>=0∞} : IsPreconnected (closed
EBall x r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.isPreconnected`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 
: _root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousAdd E]   [Continuo
usSMul ℝ E]…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `convex_closedEBall`：convex_closedEBall (a : E) (r : ENNReal) : Convex Re
al (closedEBall a r)
-/
theorem isPreconnected_closedEBall {x : E} {r : ℝ≥0∞} : IsPreconnected (closedEBall x r) :=
  (convex_closedEBall _ _).isPreconnected
/-
**Metric.isConnected_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isConnected_ball {x : E} {r : Real} (hr : 0 < r) : IsConnected (ball x r)
参数：hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPathConnected.isConnected`：IsPathConnected.isConnected (hF : IsPathCon
nected F) : IsConnected F
· 使用定理 `Metric.isPathConnected_ball`：isPathConnected_ball {x : E} {r : Real} (hr
 : 0 < r) : IsPathConnected (ball x r)
-/
theorem isConnected_ball {x : E} {r : ℝ} (hr : 0 < r) :
    IsConnected (ball x r) :=
  (isPathConnected_ball hr).isConnected
/-
**Metric.isConnected_eball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isConnected_eball {x : E} {r : Real>=0∞} (hr : 0 < r) : IsConnected (eball
 x r)
参数：hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPathConnected.isConnected`：IsPathConnected.isConnected (hF : IsPathCon
nected F) : IsConnected F
· 使用定理 `Metric.isPathConnected_eball`：isPathConnected_eball {x : E} {r : Real>=0
∞} (hr : 0 < r) : IsPathConnected (eball x r)
-/
theorem isConnected_eball {x : E} {r : ℝ≥0∞} (hr : 0 < r) :
    IsConnected (eball x r) :=
  (isPathConnected_eball hr).isConnected
/-
**Metric.isConnected_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isConnected_closedBall {x : E} {r : Real} (hr : 0 <= r) : IsConnected (clo
sedBall x r)
参数：hr : 0 <= r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `Metric.isPreconnected_closedBall`：isPreconnected_closedBall {x : E} {r :
 Real} : IsPreconnected (closedBall x r)
-/
theorem isConnected_closedBall {x : E} {r : ℝ} (hr : 0 ≤ r) : IsConnected (closedBall x r) :=
  ⟨⟨x, by simpa⟩, isPreconnected_closedBall⟩
/-
**Metric.isConnected_closedEBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isConnected_closedEBall {x : E} {r : Real>=0∞} : IsConnected (closedEBall 
x r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.mem_closedEBall_self`：mem_closedEBall_self : x in closedEBall x ε
· 使用定理 `Metric.isPreconnected_closedEBall`：isPreconnected_closedEBall {x : E} {r
 : Real>=0∞} : IsPreconnected (closedEBall x r)
-/
theorem isConnected_closedEBall {x : E} {r : ℝ≥0∞} : IsConnected (closedEBall x r) :=
  ⟨⟨x, mem_closedEBall_self⟩, isPreconnected_closedEBall⟩

end Metric

end Ball

/-- In a real vector space of dimension `> 1`, any sphere of nonnegative radius is
path connected. -/
/-
**isPathConnected_sphere** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPathConnected_sphere (h : 1 < Module.rank Real E) (x : E) {r : Real} (hr
 : 0 <= r) : IsPathConnected (sphere x r)
参数：h : 1 < Module.rank Real E；x : E；hr : 0 <= r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.sphere_zero`：∀ {γ : Type w} [inst : MetricSpace γ] {x : γ}, Metri
c.sphere x 0 = {x}
· 使用定理 `isPathConnected_singleton`：isPathConnected_singleton (x : X) : IsPathCon
nected ({x} : Set X)
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `ContinuousAt.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 :
 Add M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : 
X → M}…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x
· 使用定理 `ContinuousAt.smul`：ContinuousAt.smul (hf : ContinuousAt f b) (hg : Conti
nuousAt g b) : ContinuousAt (f • g) b
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousAt.mul`：ContinuousAt.mul (hf : ContinuousAt f x) (hg : Continu
ousAt g x) : ContinuousAt (f * g) x
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `ContinuousAt.inv₀`：∀ {α : Type u_1} {G₀ : Type u_3} [inst : Zero G₀] [in
st_1 : Inv G₀] [inst_2 : TopologicalSpace G₀] [ContinuousInv₀ G₀]   {f : α → G₀}
 {a : α…
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `ContinuousAt.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAdd
Group E] [inst_1 : TopologicalSpace α] {f : α → E} {a : α},   ContinuousAt f a →
 Contin…
· 使用定理 `continuousAt_id`：continuousAt_id : ContinuousAt id x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `isPathConnected_compl_singleton_of_one_lt_rank`：isPathConnected_compl_si
ngleton_of_one_lt_rank (h : 1 < Module.rank Real E) (x : E) : IsPathConnected {x
}ᶜ
· 使用定理 `IsPathConnected.image'`：IsPathConnected.image' (hF : IsPathConnected F) 
{f : X -> Y} (hf : ContinuousOn f F) : IsPathConnected (f '' F)
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
In a real vector space of dimension `> 1`, any sphere of nonnegative radius is
path connected.
-/
theorem isPathConnected_sphere (h : 1 < Module.rank ℝ E) (x : E) {r : ℝ} (hr : 0 ≤ r) :
    IsPathConnected (sphere x r) := by
  /- when `r > 0`, we write the sphere as the image of `{0}ᶜ` under the map
  `y ↦ x + (r * ‖y‖⁻¹) • y`. Since the image under a continuous map of a path connected set
  is path connected, this concludes the proof. -/
  rcases hr.eq_or_lt with rfl | rpos
  · simpa using isPathConnected_singleton x
  let f : E → E := fun y ↦ x + (r * ‖y‖⁻¹) • y
  have A : ContinuousOn f {0}ᶜ := by
    intro y hy
    apply (continuousAt_const.add _).continuousWithinAt
    apply (continuousAt_const.mul (ContinuousAt.inv₀ continuousAt_id.norm ?_)).smul continuousAt_id
    simpa using hy
  have B : IsPathConnected ({0}ᶜ : Set E) := isPathConnected_compl_singleton_of_one_lt_rank h 0
  have C : IsPathConnected (f '' {0}ᶜ) := B.image' A
  have : f '' {0}ᶜ = sphere x r := by
    apply Subset.antisymm
    · rintro - ⟨y, hy, rfl⟩
      have : ‖y‖ ≠ 0 := by simpa using hy
      simp [f, norm_smul, abs_of_nonneg hr, mul_assoc, inv_mul_cancel₀ this]
    · intro y hy
      refine ⟨y - x, ?_, ?_⟩
      · intro H
        simp only [mem_singleton_iff, sub_eq_zero] at H
        simp only [H, mem_sphere_iff_norm, sub_self, norm_zero] at hy
        exact rpos.ne hy
      · simp [f, mem_sphere_iff_norm.1 hy, mul_inv_cancel₀ rpos.ne']
  rwa [this] at C

/-- In a real vector space of dimension `> 1`, any sphere of nonnegative radius is connected. -/
/-
**isConnected_sphere** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConnected_sphere (h : 1 < Module.rank Real E) (x : E) {r : Real} (hr : 0
 <= r) : IsConnected (sphere x r)
参数：h : 1 < Module.rank Real E；x : E；hr : 0 <= r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPathConnected.isConnected`：IsPathConnected.isConnected (hF : IsPathCon
nected F) : IsConnected F
· 使用定理 `isPathConnected_sphere`：isPathConnected_sphere (h : 1 < Module.rank Real
 E) (x : E) {r : Real} (hr : 0 <= r) : IsPathConnected (sphere x r)

--- 原说明 ---
In a real vector space of dimension `> 1`, any sphere of nonnegative radius is c
onnected.
-/
theorem isConnected_sphere (h : 1 < Module.rank ℝ E) (x : E) {r : ℝ} (hr : 0 ≤ r) :
    IsConnected (sphere x r) :=
  (isPathConnected_sphere h x hr).isConnected

/-- In a real vector space of dimension `> 1`, any sphere is preconnected. -/
/-
**isPreconnected_sphere** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPreconnected_sphere (h : 1 < Module.rank Real E) (x : E) (r : Real) : Is
Preconnected (sphere x r)
参数：h : 1 < Module.rank Real E；x : E；r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `IsConnected.isPreconnected`：IsConnected.isPreconnected {s : Set α} (h : 
IsConnected s) : IsPreconnected s
· 使用定理 `isConnected_sphere`：isConnected_sphere (h : 1 < Module.rank Real E) (x :
 E) {r : Real} (hr : 0 <= r) : IsConnected (sphere x r)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.sphere_eq_empty_of_neg`：sphere_eq_empty_of_neg (hε : ε < 0) : sph
ere x ε = ∅
· 使用定理 `isPreconnected_empty`：isPreconnected_empty : IsPreconnected (∅ : Set α)

--- 原说明 ---
In a real vector space of dimension `> 1`, any sphere is preconnected.
-/
theorem isPreconnected_sphere (h : 1 < Module.rank ℝ E) (x : E) (r : ℝ) :
    IsPreconnected (sphere x r) := by
  rcases le_or_gt 0 r with hr | hr
  · exact (isConnected_sphere h x hr).isPreconnected
  · simpa [hr] using isPreconnected_empty

end NormedSpace

section

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

/-- Let `E` be a linear subspace in a real vector space.
If `E` has codimension at least two, its complement is path-connected. -/
/-
**isPathConnected_compl_of_one_lt_codim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPathConnected_compl_of_one_lt_codim {E : Submodule Real F} (hcodim : 1 <
 Module.rank Real (F ⧸ E)) : IsPathConnected (Eᶜ : Set F)
参数：hcodim : 1 < Module.rank Real (F ⧸ E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.exists_isCompl`：Submodule.exists_isCompl (p : Submodule K V) :
 exists q : Submodule K V, IsCompl p q
· 使用定理 `isPathConnected_compl_of_isPathConnected_compl_zero`：isPathConnected_com
pl_of_isPathConnected_compl_zero {p q : Submodule Real E} (hpq : IsCompl p q) (h
pc : IsPathConnected ({0}ᶜ : Set p)) : Is…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `isPathConnected_compl_singleton_of_one_lt_rank`：isPathConnected_compl_si
ngleton_of_one_lt_rank (h : 1 < Module.rank Real E) (x : E) : IsPathConnected {x
}ᶜ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.rank_eq`：LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank 
R M = Module.rank R M₁

--- 原说明 ---
Let `E` be a linear subspace in a real vector space.
If `E` has codimension at least two, its complement is path-connected.
-/
theorem isPathConnected_compl_of_one_lt_codim {E : Submodule ℝ F}
    (hcodim : 1 < Module.rank ℝ (F ⧸ E)) : IsPathConnected (Eᶜ : Set F) := by
  rcases E.exists_isCompl with ⟨E', hE'⟩
  refine isPathConnected_compl_of_isPathConnected_compl_zero hE'.symm
    (isPathConnected_compl_singleton_of_one_lt_rank ?_ 0)
  rwa [← (E.quotientEquivOfIsCompl E' hE').rank_eq]

/-- Let `E` be a linear subspace in a real vector space.
If `E` has codimension at least two, its complement is connected. -/
/-
**isConnected_compl_of_one_lt_codim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConnected_compl_of_one_lt_codim {E : Submodule Real F} (hcodim : 1 < Mod
ule.rank Real (F ⧸ E)) : IsConnected (Eᶜ : Set F)
参数：hcodim : 1 < Module.rank Real (F ⧸ E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPathConnected.isConnected`：IsPathConnected.isConnected (hF : IsPathCon
nected F) : IsConnected F
· 使用定理 `isPathConnected_compl_of_one_lt_codim`：isPathConnected_compl_of_one_lt_c
odim {E : Submodule Real F} (hcodim : 1 < Module.rank Real (F ⧸ E)) : IsPathConn
ected (Eᶜ : Set F)

--- 原说明 ---
Let `E` be a linear subspace in a real vector space.
If `E` has codimension at least two, its complement is connected.
-/
theorem isConnected_compl_of_one_lt_codim {E : Submodule ℝ F} (hcodim : 1 < Module.rank ℝ (F ⧸ E)) :
    IsConnected (Eᶜ : Set F) :=
  (isPathConnected_compl_of_one_lt_codim hcodim).isConnected
/-
**Submodule.connectedComponentIn_eq_self_of_one_lt_codim** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：Submodule.connectedComponentIn_eq_self_of_one_lt_codim (E : Submodule Real
 F) (hcodim : 1 < Module.rank Real (F ⧸ E)) {x : F} (hx : x ∉ E) : connectedComp
onentIn ((E : Set F)ᶜ) x = (E : Set F)ᶜ
参数：E : Submodule Real F；hcodim : 1 < Module.rank Real (F ⧸ E)；hx : x ∉ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPreconnected.connectedComponentIn`：IsPreconnected.connectedComponentIn
 {x : α} {F : Set α} (h : IsPreconnected F) (hx : x in F) : connectedComponentIn
 F x = F
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `isConnected_compl_of_one_lt_codim`：isConnected_compl_of_one_lt_codim {E 
: Submodule Real F} (hcodim : 1 < Module.rank Real (F ⧸ E)) : IsConnected (Eᶜ : 
Set F)
-/
theorem Submodule.connectedComponentIn_eq_self_of_one_lt_codim (E : Submodule ℝ F)
    (hcodim : 1 < Module.rank ℝ (F ⧸ E)) {x : F} (hx : x ∉ E) :
    connectedComponentIn ((E : Set F)ᶜ) x = (E : Set F)ᶜ :=
  (isConnected_compl_of_one_lt_codim hcodim).2.connectedComponentIn hx

end

