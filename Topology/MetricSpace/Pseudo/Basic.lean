/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Data.ENNReal.Real
public import Mathlib.Tactic.Bound.Attribute
public import Mathlib.Topology.EMetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic

/-!
## Pseudo-metric spaces

Further results about pseudo-metric spaces.

-/

public section

open Set Filter TopologicalSpace Bornology
open scoped ENNReal NNReal Uniformity Topology

universe u v

variable {α : Type u} {β : Type v} {ι : Type*}

variable [PseudoMetricSpace α]

/-- The triangle (polygon) inequality for sequences of points; `Finset.Ico` version. -/
/-
**dist_le_Ico_sum_dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_le_Ico_sum_dist (f : Nat -> α) {m n} (h : m <= n) : dist (f m) (f n) 
<= ∑ i in Finset.Ico m n, dist (f i) (f (i + 1))
参数：f : Nat -> α；h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Ico_self`：Ico_self : Ico a a = ∅
· 使用定理 `Finset.sum_empty`：∀ {ι : Type u_1} {M : Type u_3} {f : ι → M} [inst : Ad
dCommMonoid M], ∑ x ∈ ∅, f x = 0
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `dist_triangle`：dist_triangle (x y z : α) : dist x z <= dist x y + dist y
 z
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.insert_Ico_right_eq_Ico_add_one`：insert_Ico_right_eq_Ico_add_one 
(h : a <= b) : insert b (Ico a b) = Ico a (b + 1)
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a

--- 原说明 ---
The triangle (polygon) inequality for sequences of points; `Finset.Ico` version.
-/
theorem dist_le_Ico_sum_dist (f : ℕ → α) {m n} (h : m ≤ n) :
    dist (f m) (f n) ≤ ∑ i ∈ Finset.Ico m n, dist (f i) (f (i + 1)) := by
  induction n, h using Nat.le_induction with
  | base => rw [Finset.Ico_self, Finset.sum_empty, dist_self]
  | succ n hle ihn =>
    calc
      dist (f m) (f (n + 1)) ≤ dist (f m) (f n) + dist (f n) (f (n + 1)) := dist_triangle _ _ _
      _ ≤ (∑ i ∈ Finset.Ico m n, _) + _ := add_le_add ihn le_rfl
      _ = ∑ i ∈ Finset.Ico m (n + 1), _ := by
        rw [← Finset.insert_Ico_right_eq_Ico_add_one hle, Finset.sum_insert, add_comm]; simp

/-- The triangle (polygon) inequality for sequences of points; `Finset.range` version. -/
/-
**dist_le_range_sum_dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_le_range_sum_dist (f : Nat -> α) (n : Nat) : dist (f 0) (f n) <= ∑ i 
in Finset.range n, dist (f i) (f (i + 1))
参数：f : Nat -> α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dist_le_Ico_sum_dist`：dist_le_Ico_sum_dist (f : Nat -> α) {m n} (h : m <
= n) : dist (f m) (f n) <= ∑ i in Finset.Ico m n, dist (f i) (f (i + 1))
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Nat.Ico_zero_eq_range`：Ico_zero_eq_range : Ico 0 a = range a

--- 原说明 ---
The triangle (polygon) inequality for sequences of points; `Finset.range` versio
n.
-/
theorem dist_le_range_sum_dist (f : ℕ → α) (n : ℕ) :
    dist (f 0) (f n) ≤ ∑ i ∈ Finset.range n, dist (f i) (f (i + 1)) :=
  Nat.Ico_zero_eq_range n ▸ dist_le_Ico_sum_dist f (Nat.zero_le n)

/-- A version of `dist_le_Ico_sum_dist` with each intermediate distance replaced
with an upper estimate. -/
/-
**dist_le_Ico_sum_of_dist_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_le_Ico_sum_of_dist_le {f : Nat -> α} {m n} (hmn : m <= n) {d : Nat ->
 Real} (hd : forall {k}, m <= k -> k < n -> dist (f k) (f (k + 1)) <= d k) : dis
t (f m) (f n) <= ∑ i in Finset.Ico m n, d i
参数：hmn : m <= n；hd : forall {k}, m <= k -> k < n -> dist (f k) (f (k + 1)) <= d 
k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `dist_le_Ico_sum_dist`：dist_le_Ico_sum_dist (f : Nat -> α) {m n} (h : m <
= n) : dist (f m) (f n) <= ∑ i in Finset.Ico m n, dist (f i) (f (i + 1))
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ico`：mem_Ico : x in Ico a b ↔ a <= x ∧ x < b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
A version of `dist_le_Ico_sum_dist` with each intermediate distance replaced
with an upper estimate.
-/
theorem dist_le_Ico_sum_of_dist_le {f : ℕ → α} {m n} (hmn : m ≤ n) {d : ℕ → ℝ}
    (hd : ∀ {k}, m ≤ k → k < n → dist (f k) (f (k + 1)) ≤ d k) :
    dist (f m) (f n) ≤ ∑ i ∈ Finset.Ico m n, d i :=
  le_trans (dist_le_Ico_sum_dist f hmn) <|
    Finset.sum_le_sum fun _k hk => hd (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2

/-- A version of `dist_le_range_sum_dist` with each intermediate distance replaced
with an upper estimate. -/
/-
**dist_le_range_sum_of_dist_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_le_range_sum_of_dist_le {f : Nat -> α} (n : Nat) {d : Nat -> Real} (h
d : forall {k}, k < n -> dist (f k) (f (k + 1)) <= d k) : dist (f 0) (f n) <= ∑ 
i in Finset.range n, d i
参数：n : Nat；hd : forall {k}, k < n -> dist (f k) (f (k + 1)) <= d k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dist_le_Ico_sum_of_dist_le`：dist_le_Ico_sum_of_dist_le {f : Nat -> α} {m
 n} (hmn : m <= n) {d : Nat -> Real} (hd : forall {k}, m <= k -> k < n -> dist (
f k) (f (k + 1))…
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Ico_zero_eq_range`：Ico_zero_eq_range : Ico 0 a = range a

--- 原说明 ---
A version of `dist_le_range_sum_dist` with each intermediate distance replaced
with an upper estimate.
-/
theorem dist_le_range_sum_of_dist_le {f : ℕ → α} (n : ℕ) {d : ℕ → ℝ}
    (hd : ∀ {k}, k < n → dist (f k) (f (k + 1)) ≤ d k) :
    dist (f 0) (f n) ≤ ∑ i ∈ Finset.range n, d i :=
  Nat.Ico_zero_eq_range n ▸ dist_le_Ico_sum_of_dist_le zero_le fun _ => hd

namespace Metric

-- instantiate pseudometric space as a topology

nonrec theorem isUniformInducing_iff [PseudoMetricSpace β] {f : α → β} :
    IsUniformInducing f ↔ UniformContinuous f ∧
      ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, dist (f a) (f b) < ε → dist a b < δ :=
  isUniformInducing_iff'.trans <| Iff.rfl.and <|
    ((uniformity_basis_dist.comap _).le_basis_iff uniformity_basis_dist).trans <| by
      simp only [subset_def, Prod.forall, gt_iff_lt, preimage_ofPred_eq, Prod.map_apply, mem_ofPred]

nonrec theorem isUniformEmbedding_iff [PseudoMetricSpace β] {f : α → β} :
    IsUniformEmbedding f ↔ Function.Injective f ∧ UniformContinuous f ∧
      ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, dist (f a) (f b) < ε → dist a b < δ := by
  rw [isUniformEmbedding_iff, and_comm, isUniformInducing_iff]

/-- If a map between pseudometric spaces is a uniform inducing map then the distance between `f x`
and `f y` is controlled in terms of the distance between `x` and `y`. -/
/-
**Metric.controlled_of_isUniformInducing** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：controlled_of_isUniformInducing [PseudoMetricSpace β] {f : α -> β} (h : Is
UniformInducing f) : (forall ε > 0, exists δ > 0, forall {a b : α}, dist a b < δ
 -> dist (f a) (f b) < ε) ∧ forall δ > 0, exists ε > 0, forall {a b : α}, dist (
f a) (f b) < ε -> dist a b < δ
参数：h : IsUniformInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.uniformContinuous_iff`：uniformContinuous_iff [PseudoMetricSpace β
] {f : α -> β} : UniformContinuous f ↔ forall ε > 0, exists δ > 0, forall ⦃a b :
 α⦄, dist a b < δ …
· 使用定理 `IsUniformInducing.uniformContinuous`：IsUniformInducing.uniformContinuous
 {f : α -> β} (hf : IsUniformInducing f) : UniformContinuous f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Metric.isUniformInducing_iff`：∀ {α : Type u} {β : Type v} [inst : Pseudo
MetricSpace α] [inst_1 : PseudoMetricSpace β] {f : α → β},   IsUniformInducing f
 ↔ UniformContinuo…

--- 原说明 ---
If a map between pseudometric spaces is a uniform inducing map then the distance
 between `f x`
and `f y` is controlled in terms of the distance between `x` and `y`.
-/
theorem controlled_of_isUniformInducing [PseudoMetricSpace β] {f : α → β}
    (h : IsUniformInducing f) :
    (∀ ε > 0, ∃ δ > 0, ∀ {a b : α}, dist a b < δ → dist (f a) (f b) < ε) ∧
      ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, dist (f a) (f b) < ε → dist a b < δ :=
  ⟨uniformContinuous_iff.1 h.uniformContinuous, (isUniformInducing_iff.1 h).2⟩

@[deprecated controlled_of_isUniformInducing (since := "2026-04-01")]
/-
**Metric.controlled_of_isUniformEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：controlled_of_isUniformEmbedding [PseudoMetricSpace β] {f : α -> β} (h : I
sUniformEmbedding f) : (forall ε > 0, exists δ > 0, forall {a b : α}, dist a b <
 δ -> dist (f a) (f b) < ε) ∧ forall δ > 0, exists ε > 0, forall {a b : α}, dist
 (f a) (f b) < ε -> dist a b < δ
参数：h : IsUniformEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.controlled_of_isUniformInducing`：controlled_of_isUniformInducing 
[PseudoMetricSpace β] {f : α -> β} (h : IsUniformInducing f) : (forall ε > 0, ex
ists δ > 0, forall {a b : α}…
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
-/
theorem controlled_of_isUniformEmbedding [PseudoMetricSpace β] {f : α → β}
    (h : IsUniformEmbedding f) :
    (∀ ε > 0, ∃ δ > 0, ∀ {a b : α}, dist a b < δ → dist (f a) (f b) < ε) ∧
      ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, dist (f a) (f b) < ε → dist a b < δ :=
  controlled_of_isUniformInducing h.toIsUniformInducing
/-
**Metric.totallyBounded_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：totallyBounded_iff {s : Set α} : TotallyBounded s ↔ forall ε > 0, exists t
 : Set α, t.Finite ∧ s subseteq ⋃ y in t, ball y ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.totallyBounded_iff`：Filter.HasBasis.totallyBounded_iff {
ι} {p : ι -> Prop} {U : ι -> SetRel α α} (H : (𝓤 α).HasBasis p U) {s : Set α} : 
TotallyBounded s ↔ foral…
· 使用定理 `Metric.uniformity_basis_dist`：uniformity_basis_dist : (𝓤 α).HasBasis (fu
n ε : Real => 0 < ε) fun ε => { p : α × α | dist p.1 p.2 < ε }
-/
theorem totallyBounded_iff {s : Set α} :
    TotallyBounded s ↔ ∀ ε > 0, ∃ t : Set α, t.Finite ∧ s ⊆ ⋃ y ∈ t, ball y ε :=
  uniformity_basis_dist.totallyBounded_iff

/-- A pseudometric space is totally bounded if one can reconstruct up to any ε>0 any element of the
space from finitely many data. -/
/-
**Metric.totallyBounded_of_finite_discretization** 是 Mathlib 中的一个定理，位于命名空间 `Metr
ic`。
形式化陈述：totallyBounded_of_finite_discretization {s : Set α} (H : forall ε > (0 : R
eal), exists (β : Type u) (_ : Fintype β) (F : s -> β), forall x y, F x = F y ->
 dist (x : α) y < ε) : TotallyBounded s
参数：H : forall ε > (0 : Real), exists (β : Type u) (_ : Fintype β) (F : s -> β), 
forall x y, F x = F y -> dist (x : α) y < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `totallyBounded_empty`：totallyBounded_empty : TotallyBounded (∅ : Set α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.totallyBounded_iff`：totallyBounded_iff {s : Set α} : TotallyBound
ed s ↔ forall ε > 0, exists t : Set α, t.Finite ∧ s subseteq ⋃ y in t, ball y ε
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Function.invFun_eq`：invFun_eq (h : exists a, f a = b) : f (invFun f b) =
 b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A pseudometric space is totally bounded if one can reconstruct up to any ε>0 any
 element of the
space from finitely many data.
-/
theorem totallyBounded_of_finite_discretization {s : Set α}
    (H : ∀ ε > (0 : ℝ),
        ∃ (β : Type u) (_ : Fintype β) (F : s → β), ∀ x y, F x = F y → dist (x : α) y < ε) :
    TotallyBounded s := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · rw [hs]
    exact totallyBounded_empty
  rcases hs with ⟨x0, hx0⟩
  have : Inhabited s := ⟨⟨x0, hx0⟩⟩
  refine totallyBounded_iff.2 fun ε ε0 => ?_
  rcases H ε ε0 with ⟨β, fβ, F, hF⟩
  let Finv := Function.invFun F
  refine ⟨range (Subtype.val ∘ Finv), finite_range _, fun x xs => ?_⟩
  let x' := Finv (F ⟨x, xs⟩)
  have : F x' = F ⟨x, xs⟩ := Function.invFun_eq ⟨⟨x, xs⟩, rfl⟩
  simp only [Set.mem_iUnion, Set.mem_range]
  exact ⟨_, ⟨F ⟨x, xs⟩, rfl⟩, hF _ _ this.symm⟩
/-
**Metric.finite_approx_of_totallyBounded** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：finite_approx_of_totallyBounded {s : Set α} (hs : TotallyBounded s) : fora
ll ε > 0, exists t, t subseteq s ∧ Set.Finite t ∧ s subseteq ⋃ y in t, ball y ε
参数：hs : TotallyBounded s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `totallyBounded_iff_subset`：totallyBounded_iff_subset {s : Set α} : Total
lyBounded s ↔ forall d in 𝓤 α, exists t, t subseteq s ∧ Set.Finite t ∧ s subsete
q ⋃ y in t, { x…
· 使用定理 `Metric.dist_mem_uniformity`：dist_mem_uniformity {ε : Real} (ε0 : 0 < ε) 
: { p : α × α | dist p.1 p.2 < ε } in 𝓤 α
-/
theorem finite_approx_of_totallyBounded {s : Set α} (hs : TotallyBounded s) :
    ∀ ε > 0, ∃ t, t ⊆ s ∧ Set.Finite t ∧ s ⊆ ⋃ y ∈ t, ball y ε := by
  intro ε ε_pos
  rw [totallyBounded_iff_subset] at hs
  exact hs _ (dist_mem_uniformity ε_pos)

/-- Expressing uniform convergence using `dist` -/
/-
**Metric.tendstoUniformlyOnFilter_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：tendstoUniformlyOnFilter_iff {F : ι -> β -> α} {f : β -> α} {p : Filter ι}
 {p' : Filter β} : TendstoUniformlyOnFilter F f p p' ↔ forall ε > 0, forallᶠ n :
 ι × β in p ×ˢ p', dist (f n.snd) (F n.fst n.snd) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.dist_mem_uniformity`：dist_mem_uniformity {ε : Real} (ε0 : 0 < ε) 
: { p : α × α | dist p.1 p.2 < ε } in 𝓤 α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_uniformity_dist`：mem_uniformity_dist {s : Set (α × α)} : s in
 𝓤 α ↔ exists ε > 0, forall ⦃a b : α⦄, dist a b < ε -> (a, b) in s
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x

--- 原说明 ---
Expressing uniform convergence using `dist`
-/
theorem tendstoUniformlyOnFilter_iff {F : ι → β → α} {f : β → α} {p : Filter ι} {p' : Filter β} :
    TendstoUniformlyOnFilter F f p p' ↔
      ∀ ε > 0, ∀ᶠ n : ι × β in p ×ˢ p', dist (f n.snd) (F n.fst n.snd) < ε := by
  refine ⟨fun H ε hε => H _ (dist_mem_uniformity hε), fun H u hu => ?_⟩
  rcases mem_uniformity_dist.1 hu with ⟨ε, εpos, hε⟩
  exact (H ε εpos).mono fun n hn => hε hn

/-- Expressing locally uniform convergence on a set using `dist`. -/
/-
**Metric.tendstoLocallyUniformlyOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：tendstoLocallyUniformlyOn_iff [TopologicalSpace β] {F : ι -> β -> α} {f : 
β -> α} {p : Filter ι} {s : Set β} : TendstoLocallyUniformlyOn F f p s ↔ forall 
ε > 0, forall x in s, exists t in 𝓝[s] x, forallᶠ n in p, forall y in t, dist (f
 y) (F n y) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.dist_mem_uniformity`：dist_mem_uniformity {ε : Real} (ε0 : 0 < ε) 
: { p : α × α | dist p.1 p.2 < ε } in 𝓤 α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_uniformity_dist`：mem_uniformity_dist {s : Set (α × α)} : s in
 𝓤 α ↔ exists ε > 0, forall ⦃a b : α⦄, dist a b < ε -> (a, b) in s
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x

--- 原说明 ---
Expressing locally uniform convergence on a set using `dist`.
-/
theorem tendstoLocallyUniformlyOn_iff [TopologicalSpace β] {F : ι → β → α} {f : β → α}
    {p : Filter ι} {s : Set β} :
    TendstoLocallyUniformlyOn F f p s ↔
      ∀ ε > 0, ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, ∀ᶠ n in p, ∀ y ∈ t, dist (f y) (F n y) < ε := by
  refine ⟨fun H ε hε => H _ (dist_mem_uniformity hε), fun H u hu x hx => ?_⟩
  rcases mem_uniformity_dist.1 hu with ⟨ε, εpos, hε⟩
  rcases H ε εpos x hx with ⟨t, ht, Ht⟩
  exact ⟨t, ht, Ht.mono fun n hs x hx => hε (hs x hx)⟩

/-- Expressing uniform convergence on a set using `dist`. -/
/-
**Metric.tendstoUniformlyOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：tendstoUniformlyOn_iff {F : ι -> β -> α} {f : β -> α} {p : Filter ι} {s : 
Set β} : TendstoUniformlyOn F f p s ↔ forall ε > 0, forallᶠ n in p, forall x in 
s, dist (f x) (F n x) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.dist_mem_uniformity`：dist_mem_uniformity {ε : Real} (ε0 : 0 < ε) 
: { p : α × α | dist p.1 p.2 < ε } in 𝓤 α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_uniformity_dist`：mem_uniformity_dist {s : Set (α × α)} : s in
 𝓤 α ↔ exists ε > 0, forall ⦃a b : α⦄, dist a b < ε -> (a, b) in s
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x

--- 原说明 ---
Expressing uniform convergence on a set using `dist`.
-/
theorem tendstoUniformlyOn_iff {F : ι → β → α} {f : β → α} {p : Filter ι} {s : Set β} :
    TendstoUniformlyOn F f p s ↔ ∀ ε > 0, ∀ᶠ n in p, ∀ x ∈ s, dist (f x) (F n x) < ε := by
  refine ⟨fun H ε hε => H _ (dist_mem_uniformity hε), fun H u hu => ?_⟩
  rcases mem_uniformity_dist.1 hu with ⟨ε, εpos, hε⟩
  exact (H ε εpos).mono fun n hs x hx => hε (hs x hx)

/-- Expressing locally uniform convergence using `dist`. -/
/-
**Metric.tendstoLocallyUniformly_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：tendstoLocallyUniformly_iff [TopologicalSpace β] {F : ι -> β -> α} {f : β 
-> α} {p : Filter ι} : TendstoLocallyUniformly F f p ↔ forall ε > 0, forall x : 
β, exists t in 𝓝 x, forallᶠ n in p, forall y in t, dist (f y) (F n y) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Expressing locally uniform convergence using `dist`.
-/
theorem tendstoLocallyUniformly_iff [TopologicalSpace β] {F : ι → β → α} {f : β → α}
    {p : Filter ι} :
    TendstoLocallyUniformly F f p ↔
      ∀ ε > 0, ∀ x : β, ∃ t ∈ 𝓝 x, ∀ᶠ n in p, ∀ y ∈ t, dist (f y) (F n y) < ε := by
  simp only [← tendstoLocallyUniformlyOn_univ, tendstoLocallyUniformlyOn_iff, nhdsWithin_univ,
    mem_univ, forall_const]

/-- Expressing uniform convergence using `dist`. -/
/-
**Metric.tendstoUniformly_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：tendstoUniformly_iff {F : ι -> β -> α} {f : β -> α} {p : Filter ι} : Tends
toUniformly F f p ↔ forall ε > 0, forallᶠ n in p, forall x, dist (f x) (F n x) <
 ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tendstoUniformlyOn_univ`：tendstoUniformlyOn_univ : TendstoUniformlyOn F 
f p univ ↔ TendstoUniformly F f p
· 使用定理 `Metric.tendstoUniformlyOn_iff`：tendstoUniformlyOn_iff {F : ι -> β -> α} 
{f : β -> α} {p : Filter ι} {s : Set β} : TendstoUniformlyOn F f p s ↔ forall ε 
> 0, forallᶠ n in p…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Expressing uniform convergence using `dist`.
-/
theorem tendstoUniformly_iff {F : ι → β → α} {f : β → α} {p : Filter ι} :
    TendstoUniformly F f p ↔ ∀ ε > 0, ∀ᶠ n in p, ∀ x, dist (f x) (F n x) < ε := by
  rw [← tendstoUniformlyOn_univ, tendstoUniformlyOn_iff]
  simp
/-
**Metric.cauchy_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α] {f : Filter α},   Cauchy f ↔ f
.NeBot ∧ ∀ ε > 0, ∃ t ∈ f, ∀ x ∈ t, ∀ y ∈ t, dist x y < ε
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.cauchy_iff`：Filter.HasBasis.cauchy_iff {ι} {p : ι -> Pro
p} {s : ι -> SetRel α α} (h : (𝓤 α).HasBasis p s) {f : Filter α} : Cauchy f ↔ Ne
Bot f ∧ forall i…
· 使用定理 `Metric.uniformity_basis_dist`：uniformity_basis_dist : (𝓤 α).HasBasis (fu
n ε : Real => 0 < ε) fun ε => { p : α × α | dist p.1 p.2 < ε }
-/
protected theorem cauchy_iff {f : Filter α} :
    Cauchy f ↔ NeBot f ∧ ∀ ε > 0, ∃ t ∈ f, ∀ x ∈ t, ∀ y ∈ t, dist x y < ε :=
  uniformity_basis_dist.cauchy_iff

variable {s : Set α}

/-- Given a point `x` in a discrete subset `s` of a pseudometric space, there is an open ball
centered at `x` and intersecting `s` only at `x`. -/
/-
**Metric.exists_ball_inter_eq_singleton_of_mem_discrete** 是 Mathlib 中的一个定理，位于命名空
间 `Metric`。
形式化陈述：exists_ball_inter_eq_singleton_of_mem_discrete (hs : IsDiscrete s) {x : α}
 (hx : x in s) : exists ε > 0, Metric.ball x ε inter s = {x}
参数：hs : IsDiscrete s；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.exists_inter_eq_singleton_of_mem_discrete`：Filter.HasBas
is.exists_inter_eq_singleton_of_mem_discrete {ι : Type*} {p : ι -> Prop} {t : ι 
-> Set X} {s : Set X} (hs : IsDiscrete s) {x : …
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)

--- 原说明 ---
Given a point `x` in a discrete subset `s` of a pseudometric space, there is an 
open ball
centered at `x` and intersecting `s` only at `x`.
-/
theorem exists_ball_inter_eq_singleton_of_mem_discrete (hs : IsDiscrete s) {x : α} (hx : x ∈ s) :
    ∃ ε > 0, Metric.ball x ε ∩ s = {x} :=
  nhds_basis_ball.exists_inter_eq_singleton_of_mem_discrete hs hx

/-- Given a point `x` in a discrete subset `s` of a pseudometric space, there is a closed ball
of positive radius centered at `x` and intersecting `s` only at `x`. -/
/-
**Metric.exists_closedBall_inter_eq_singleton_of_discrete** 是 Mathlib 中的一个定理，位于命
名空间 `Metric`。
形式化陈述：exists_closedBall_inter_eq_singleton_of_discrete (hs : IsDiscrete s) {x : 
α} (hx : x in s) : exists ε > 0, Metric.closedBall x ε inter s = {x}
参数：hs : IsDiscrete s；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.exists_inter_eq_singleton_of_mem_discrete`：Filter.HasBas
is.exists_inter_eq_singleton_of_mem_discrete {ι : Type*} {p : ι -> Prop} {t : ι 
-> Set X} {s : Set X} (hs : IsDiscrete s) {x : …
· 使用定理 `Metric.nhds_basis_closedBall`：nhds_basis_closedBall : (𝓝 x).HasBasis (fu
n ε : Real => 0 < ε) (closedBall x)

--- 原说明 ---
Given a point `x` in a discrete subset `s` of a pseudometric space, there is a c
losed ball
of positive radius centered at `x` and intersecting `s` only at `x`.
-/
theorem exists_closedBall_inter_eq_singleton_of_discrete (hs : IsDiscrete s) {x : α} (hx : x ∈ s) :
    ∃ ε > 0, Metric.closedBall x ε ∩ s = {x} :=
  nhds_basis_closedBall.exists_inter_eq_singleton_of_mem_discrete hs hx

end Metric

open Metric

/-
**Metric.inseparable_iff_nndist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Metric.inseparable_iff_nndist {x y : α} : Inseparable x y ↔ nndist x y = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EMetric.inseparable_iff`：inseparable_iff : Inseparable x y ↔ edist x y =
 0
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y
· 使用定理 `ENNReal.coe_eq_zero`：∀ {r : NNReal}, ↑r = 0 ↔ r = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Metric.inseparable_iff_nndist {x y : α} : Inseparable x y ↔ nndist x y = 0 := by
  rw [EMetric.inseparable_iff, edist_nndist, ENNReal.coe_eq_zero]

alias ⟨Inseparable.nndist_eq_zero, _⟩ := Metric.inseparable_iff_nndist
/-
**Metric.inseparable_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Metric.inseparable_iff {x y : α} : Inseparable x y ↔ dist x y = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.inseparable_iff_nndist`：Metric.inseparable_iff_nndist {x y : α} :
 Inseparable x y ↔ nndist x y = 0
· 使用定理 `dist_nndist`：dist_nndist (x y : α) : dist x y = nndist x y
· 使用定理 `NNReal.coe_eq_zero`：∀ {r : NNReal}, ↑r = 0 ↔ r = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Metric.inseparable_iff {x y : α} : Inseparable x y ↔ dist x y = 0 := by
  rw [Metric.inseparable_iff_nndist, dist_nndist, NNReal.coe_eq_zero]

alias ⟨Inseparable.dist_eq_zero, _⟩ := Metric.inseparable_iff

/-- A weaker version of `tendsto_nhds_unique` for `PseudoMetricSpace`. -/
/-
**tendsto_nhds_unique_dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_nhds_unique_dist {f : β -> α} {l : Filter β} {x y : α} [NeBot l] (
ha : Tendsto f l (𝓝 x)) (hb : Tendsto f l (𝓝 y)) : dist x y = 0
参数：ha : Tendsto f l (𝓝 x)；hb : Tendsto f l (𝓝 y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Inseparable.dist_eq_zero`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x
 y : α}, Inseparable x y → dist x y = 0
· 使用定理 `tendsto_nhds_unique_inseparable`：tendsto_nhds_unique_inseparable {f : Y 
-> X} {l : Filter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto 
f l (𝓝 b)) : Insepara…
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.regularSpace`：∀ {X : Type u_2} [i
nst : TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X], RegularSpa
ce X
· 使用定理 `UniformSpace.pseudoMetrizableSpace`：∀ {X : Type u_5} [u : UniformSpace X
] [hu : (uniformity X).IsCountablyGenerated],   TopologicalSpace.PseudoMetrizabl
eSpace X
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated

--- 原说明 ---
A weaker version of `tendsto_nhds_unique` for `PseudoMetricSpace`.
-/
theorem tendsto_nhds_unique_dist {f : β → α} {l : Filter β} {x y : α} [NeBot l]
    (ha : Tendsto f l (𝓝 x)) (hb : Tendsto f l (𝓝 y)) : dist x y = 0 :=
  (tendsto_nhds_unique_inseparable ha hb).dist_eq_zero

section Real

/-
**cauchySeq_iff_tendsto_dist_atTop_0** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchySeq_iff_tendsto_dist_atTop_0 [Nonempty β] [SemilatticeSup β] {u : β 
-> α} : CauchySeq u ↔ Tendsto (fun n : β × β => dist (u n.1) (u n.2)) atTop (𝓝 0
)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cauchySeq_iff_tendsto`：cauchySeq_iff_tendsto [Nonempty β] [SemilatticeSu
p β] {u : β -> α} : CauchySeq u ↔ Tendsto (Prod.map u u) atTop (𝓤 α)
· 使用定理 `Metric.uniformity_eq_comap_nhds_zero`：Metric.uniformity_eq_comap_nhds_ze
ro : 𝓤 α = comap (fun p : α × α => dist p.1 p.2) (𝓝 (0 : Real))
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cauchySeq_iff_tendsto_dist_atTop_0 [Nonempty β] [SemilatticeSup β] {u : β → α} :
    CauchySeq u ↔ Tendsto (fun n : β × β => dist (u n.1) (u n.2)) atTop (𝓝 0) := by
  rw [cauchySeq_iff_tendsto, Metric.uniformity_eq_comap_nhds_zero, tendsto_comap_iff,
    Function.comp_def]
  simp_rw [Prod.map_fst, Prod.map_snd]

end Real

namespace Topology

/-- The preimage of a separable set by an inducing map is separable. -/
/-
**Topology.IsInducing.isSeparable_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Topology.I
sInducing`。
形式化陈述：∀ {β : Type v} {α : Type u_2} [inst : TopologicalSpace α] [TopologicalSpac
e.PseudoMetrizableSpace α] {f : β → α}   [inst_2 : TopologicalSpace β],   Topolo
gy.IsInducing f → ∀ {s : Set α}, TopologicalSpace.IsSeparable s → TopologicalSpa
ce.IsSeparable (f ⁻¹' s)
参数：f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.pseudoMetrizableSpaceUniformity_countably_generated`：ps
eudoMetrizableSpaceUniformity_countably_generated (X : Type*) [TopologicalSpace 
X] [h : PseudoMetrizableSpace X] : 𝓤[pseudoMetrizableSpace…
· 使用定理 `TopologicalSpace.IsSeparable.separableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X] {s : Set X},   Topo
logicalSpace.IsSeparable s → Topo…
· 使用定理 `instIsCountablyGeneratedProdElemUniformity`：∀ {α : Type ua} [inst : Unif
ormSpace α] [(uniformity α).IsCountablyGenerated] (s : Set α),   (uniformity ↑s)
.IsCountablyGenerated
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
· 使用定理 `Topology.IsInducing.codRestrict`：Topology.IsInducing.codRestrict {e : X 
-> Y} (he : IsInducing e) {s : Set Y} (hs : forall x, e x in s) : IsInducing (co
dRestrict e s hs)
· 使用定理 `Topology.IsInducing.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3}
 {f : X → Y} {g : Y → Z} [inst : TopologicalSpace Y]   [inst_1 : TopologicalSpac
e X] [inst_2 :…
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
· 使用定理 `Topology.IsInducing.secondCountableTopology`：∀ {α : Type u_1} {β : Type 
u_2} [inst : TopologicalSpace α] {f : α → β} [inst_1 : TopologicalSpace β]   [Se
condCountableTopology β], Topolog…
· 使用定理 `TopologicalSpace.IsSeparable.of_subtype`：∀ {α : Type u} [t : Topological
Space α] (s : Set α) [TopologicalSpace.SeparableSpace ↑s], TopologicalSpace.IsSe
parable s
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α

--- 原说明 ---
The preimage of a separable set by an inducing map is separable.
-/
protected lemma IsInducing.isSeparable_preimage {α : Type*} [TopologicalSpace α]
    [PseudoMetrizableSpace α] {f : β → α} [TopologicalSpace β]
    (hf : IsInducing f) {s : Set α} (hs : IsSeparable s) : IsSeparable (f ⁻¹' s) := by
  let : UniformSpace α := TopologicalSpace.pseudoMetrizableSpaceUniformity α
  have := pseudoMetrizableSpaceUniformity_countably_generated
  have : SeparableSpace s := hs.separableSpace
  have : SecondCountableTopology s := UniformSpace.secondCountable_of_separable _
  have : IsInducing ((mapsTo_preimage f s).restrict _ _ _) :=
    (hf.comp IsInducing.subtypeVal).codRestrict _
  have := this.secondCountableTopology
  exact .of_subtype _
/-
**Topology.IsEmbedding.isSeparable_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Topology.
IsEmbedding`。
形式化陈述：∀ {β : Type v} {α : Type u_2} [inst : TopologicalSpace α] [TopologicalSpac
e.PseudoMetrizableSpace α] {f : β → α}   [inst_2 : TopologicalSpace β],   Topolo
gy.IsEmbedding f → ∀ {s : Set α}, TopologicalSpace.IsSeparable s → TopologicalSp
ace.IsSeparable (f ⁻¹' s)
参数：f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.isSeparable_preimage`：∀ {β : Type v} {α : Type u_2} 
[inst : TopologicalSpace α] [TopologicalSpace.PseudoMetrizableSpace α] {f : β → 
α}   [inst_2 : TopologicalSpac…
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
-/
protected theorem IsEmbedding.isSeparable_preimage {α : Type*} [TopologicalSpace α]
    [PseudoMetrizableSpace α] {f : β → α} [TopologicalSpace β]
    (hf : IsEmbedding f) {s : Set α} (hs : IsSeparable s) : IsSeparable (f ⁻¹' s) :=
  hf.isInducing.isSeparable_preimage hs

end Topology

/-- A compact set is separable. -/
/-
**IsCompact.isSeparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.isSeparable {α : Type*} [TopologicalSpace α] [PseudoMetrizableSp
ace α] {s : Set α} (hs : IsCompact s) : IsSeparable s
参数：hs : IsCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsSeparable.of_subtype`：∀ {α : Type u} [t : Topological
Space α] (s : Set α) [TopologicalSpace.SeparableSpace ↑s], TopologicalSpace.IsSe
parable s
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `instLindelofSpaceOfSigmaCompactSpace`：∀ {X : Type u} [inst : Topological
Space X] [SigmaCompactSpace X], LindelofSpace X
· 使用定理 `CompactSpace.sigmaCompact`：∀ {X : Type u_1} [inst : TopologicalSpace X] 
[CompactSpace X], SigmaCompactSpace X
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.subtype`：∀ {X : Type u_2} [inst :
 TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X] (s : Set X),   T
opologicalSpace.PseudoMetrizableSpac…

--- 原说明 ---
A compact set is separable.
-/
theorem IsCompact.isSeparable {α : Type*} [TopologicalSpace α] [PseudoMetrizableSpace α]
    {s : Set α} (hs : IsCompact s) : IsSeparable s :=
  haveI : CompactSpace s := isCompact_iff_compactSpace.mp hs
  .of_subtype s

namespace Metric

section SecondCountable

open TopologicalSpace

/-- A pseudometric space is second countable if, for every `ε > 0`, there is a countable set which
is `ε`-dense. -/
/-
**Metric.secondCountable_of_almost_dense_set** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：secondCountable_of_almost_dense_set (H : forall ε > (0 : Real), exists s :
 Set α, s.Countable ∧ forall x, exists y in s, dist x y <= ε) : SecondCountableT
opology α
参数：H : forall ε > (0 : Real), exists s : Set α, s.Countable ∧ forall x, exists y
 in s, dist x y <= ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EMetric.secondCountable_of_almost_dense_set`：secondCountable_of_almost_d
ense_set (hs : forall ε > 0, exists t : Set α, t.Countable ∧ ⋃ x in t, closedEBa
ll x ε = univ) : SecondCountableT…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.lt_iff_exists_nnreal_btwn`：lt_iff_exists_nnreal_btwn : a < b ↔ e
xists r : Real>=0, a < r ∧ (r : Real>=0∞) < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.iUnion₂_eq_univ_iff`：iUnion₂_eq_univ_iff {s : forall i, κ i -> Set α
} : ⋃ (i) (j), s i j = univ ↔ forall a, exists i j, a in s i j
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0

--- 原说明 ---
A pseudometric space is second countable if, for every `ε > 0`, there is a count
able set which
is `ε`-dense.
-/
theorem secondCountable_of_almost_dense_set
    (H : ∀ ε > (0 : ℝ), ∃ s : Set α, s.Countable ∧ ∀ x, ∃ y ∈ s, dist x y ≤ ε) :
    SecondCountableTopology α := by
  refine EMetric.secondCountable_of_almost_dense_set fun ε ε0 => ?_
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 ε0 with ⟨ε', ε'0, ε'ε⟩
  choose s hsc y hys hyx using H ε' (mod_cast ε'0)
  refine ⟨s, hsc, iUnion₂_eq_univ_iff.2 fun x => ⟨y x, hys _, le_trans ?_ ε'ε.le⟩⟩
  exact mod_cast hyx x

end SecondCountable

end Metric

section Compact
variable {X : Type*} [PseudoMetricSpace X] {s : Set X} {ε : ℝ}

/-- Any compact set in a pseudometric space can be covered by finitely many balls of a given
positive radius -/
/-
**finite_cover_balls_of_compact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finite_cover_balls_of_compact (hs : IsCompact s) {e : Real} (he : 0 < e) :
 exists t subseteq s, t.Finite ∧ s subseteq ⋃ x in t, ball x e
参数：hs : IsCompact s；he : 0 < e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.elim_nhds_subcover`：IsCompact.elim_nhds_subcover (hs : IsCompa
ct s) (U : X -> Set X) (hU : forall x in s, U x in 𝓝 x) : exists t : Finset X, (
forall x in t, x i…
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite

--- 原说明 ---
Any compact set in a pseudometric space can be covered by finitely many balls of
 a given
positive radius
-/
theorem finite_cover_balls_of_compact (hs : IsCompact s) {e : ℝ} (he : 0 < e) :
    ∃ t ⊆ s, t.Finite ∧ s ⊆ ⋃ x ∈ t, ball x e :=
  let ⟨t, hts, ht⟩ := hs.elim_nhds_subcover _ (fun x _ => ball_mem_nhds x he)
  ⟨t, hts, t.finite_toSet, ht⟩

alias IsCompact.finite_cover_balls := finite_cover_balls_of_compact

/-- Any relatively compact set in a pseudometric space can be covered by finitely many balls of a
given positive radius. -/
/-
**exists_finite_cover_balls_of_isCompact_closure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_finite_cover_balls_of_isCompact_closure (hs : IsCompact (closure s)
) (hε : 0 < ε) : exists t subseteq s, t.Finite ∧ s subseteq ⋃ x in t, ball x ε
参数：hs : IsCompact (closure s)；hε : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.elim_finite_subcover`：IsCompact.elim_finite_subcover {ι : Type
 v} (hs : IsCompact s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) (hsU : s 
subseteq ⋃ i, U i) :…
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_closure_iff`：mem_closure_iff {s : Set α} {a : α} : a in closu
re s ↔ forall ε > 0, exists b in s, dist a b < ε
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s

--- 原说明 ---
Any relatively compact set in a pseudometric space can be covered by finitely ma
ny balls of a
given positive radius.
-/
lemma exists_finite_cover_balls_of_isCompact_closure (hs : IsCompact (closure s)) (hε : 0 < ε) :
    ∃ t ⊆ s, t.Finite ∧ s ⊆ ⋃ x ∈ t, ball x ε := by
  obtain ⟨t, hst⟩ := hs.elim_finite_subcover (fun x : s ↦ ball x ε) (fun _ ↦ isOpen_ball) fun x hx ↦
    let ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx _ hε; mem_iUnion.2 ⟨⟨y, hy⟩, hxy⟩
  refine ⟨t.map ⟨Subtype.val, Subtype.val_injective⟩, by simp, Finset.finite_toSet _, ?_⟩
  simpa using subset_closure.trans hst

end Compact

/-- If a map is continuous on a separable set `s`, then the image of `s` is also separable. -/
/-
**ContinuousOn.isSeparable_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.isSeparable_image {α : Type*} [TopologicalSpace α] [PseudoMet
rizableSpace α] [TopologicalSpace β] {f : α -> β} {s : Set α} (hf : ContinuousOn
 f s) (hs : IsSeparable s) : IsSeparable (f '' s)
参数：hf : ContinuousOn f s；hs : IsSeparable s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `TopologicalSpace.IsSeparable.image`：∀ {α : Type u} [t : TopologicalSpace
 α] {β : Type u_2} [inst : TopologicalSpace β] {s : Set α},   TopologicalSpace.I
sSeparable s → ∀ {f : α …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `TopologicalSpace.isSeparable_univ_iff`：isSeparable_univ_iff : IsSeparabl
e (univ : Set α) ↔ SeparableSpace α
· 使用定理 `TopologicalSpace.IsSeparable.separableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X] {s : Set X},   Topo
logicalSpace.IsSeparable s → Topo…
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…

--- 原说明 ---
If a map is continuous on a separable set `s`, then the image of `s` is also sep
arable.
-/
theorem ContinuousOn.isSeparable_image {α : Type*} [TopologicalSpace α] [PseudoMetrizableSpace α]
    [TopologicalSpace β] {f : α → β} {s : Set α}
    (hf : ContinuousOn f s) (hs : IsSeparable s) : IsSeparable (f '' s) := by
  rw [image_eq_range, ← image_univ]
  exact (isSeparable_univ_iff.2 hs.separableSpace).image hf.domRestrict
