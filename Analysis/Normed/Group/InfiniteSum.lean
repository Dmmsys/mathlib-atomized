/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Heather Macbeth, Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Infinite sums in (semi)normed groups

In a complete (semi)normed group,

- `summable_iff_vanishing_norm`: a series `∑' i, f i` is summable if and only if for any `ε > 0`,
  there exists a finite set `s` such that the sum `∑ i ∈ t, f i` over any finite set `t` disjoint
  with `s` has norm less than `ε`;

- `Summable.of_norm_bounded`, `Summable.of_norm_bounded_eventually`: if `‖f i‖` is bounded above by
  a summable series `∑' i, g i`, then `∑' i, f i` is summable as well; the same is true if the
  inequality hold only off some finite set.

- `tsum_of_norm_bounded`, `HasSum.norm_le_of_bounded`: if `‖f i‖ ≤ g i`, where `∑' i, g i` is a
  summable series, then `‖∑' i, f i‖ ≤ ∑' i, g i`.

- versions of these lemmas for `nnnorm` and `enorm`.

## Tags

infinite series, absolute convergence, normed group
-/

public section

open Topology ENNReal NNReal

open Finset Filter Metric

variable {ι α E F ε : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [TopologicalSpace ε] [ESeminormedAddCommMonoid ε]

/-
**cauchySeq_finset_iff_vanishing_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchySeq_finset_iff_vanishing_norm {f : ι -> E} : (CauchySeq fun s : Fins
et ι => ∑ i in s, f i) ↔ forall ε > (0 : Real), exists s : Finset ι, forall t, D
isjoint t s -> ‖∑ i in t, f i‖ < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cauchySeq_finset_iff_sum_vanishing`：∀ {α : Type u_1} {β : Type u_2} [ins
t : UniformSpace α] [inst_1 : AddCommGroup α] [IsUniformAddGroup α] {f : β → α},
   (CauchySeq fun s => ∑…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `Filter.HasBasis.forall_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s →     ∀ {P : Set α → Prop}, 
(∀ ⦃s t : Set α⦄…
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ball_zero_eq`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (r : ℝ), Me
tric.ball 0 r = {x | ‖x‖ < r}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cauchySeq_finset_iff_vanishing_norm {f : ι → E} :
    (CauchySeq fun s : Finset ι => ∑ i ∈ s, f i) ↔
      ∀ ε > (0 : ℝ), ∃ s : Finset ι, ∀ t, Disjoint t s → ‖∑ i ∈ t, f i‖ < ε := by
  rw [cauchySeq_finset_iff_sum_vanishing, nhds_basis_ball.forall_iff]
  · simp only [ball_zero_eq, Set.mem_ofPred_eq]
  · rintro s t hst ⟨s', hs'⟩
    exact ⟨s', fun t' ht' => hst <| hs' _ ht'⟩
/-
**summable_iff_vanishing_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_iff_vanishing_norm [CompleteSpace E] {f : ι -> E} : Summable f ↔ 
forall ε > (0 : Real), exists s : Finset ι, forall t, Disjoint t s -> ‖∑ i in t,
 f i‖ < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `summable_iff_cauchySeq_finset`：∀ {α : Type u_1} {β : Type u_2} [inst : U
niformSpace α] [inst_1 : AddCommMonoid α] [CompleteSpace α] {f : β → α},   Summa
ble f ↔ CauchySeq f…
· 使用定理 `cauchySeq_finset_iff_vanishing_norm`：cauchySeq_finset_iff_vanishing_norm
 {f : ι -> E} : (CauchySeq fun s : Finset ι => ∑ i in s, f i) ↔ forall ε > (0 : 
Real), exists s : Finset …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem summable_iff_vanishing_norm [CompleteSpace E] {f : ι → E} :
    Summable f ↔ ∀ ε > (0 : ℝ), ∃ s : Finset ι, ∀ t, Disjoint t s → ‖∑ i ∈ t, f i‖ < ε := by
  rw [summable_iff_cauchySeq_finset, cauchySeq_finset_iff_vanishing_norm]
/-
**cauchySeq_finset_of_norm_bounded_eventually** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchySeq_finset_of_norm_bounded_eventually {f : ι -> E} {g : ι -> Real} (
hg : Summable g) (h : forallᶠ i in cofinite, ‖f i‖ <= g i) : CauchySeq fun s => 
∑ i in s, f i
参数：hg : Summable g；h : forallᶠ i in cofinite, ‖f i‖ <= g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `cauchySeq_finset_iff_vanishing_norm`：cauchySeq_finset_iff_vanishing_norm
 {f : ι -> E} : (CauchySeq fun s : Finset ι => ∑ i in s, f i) ↔ forall ε > (0 : 
Real), exists s : Finset …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `summable_iff_vanishing_norm`：summable_iff_vanishing_norm [CompleteSpace 
E] {f : ι -> E} : Summable f ↔ forall ε > (0 : Real), exists s : Finset ι, foral
l t, Disjoint t s…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
· 使用定理 `norm_sum_le_of_le`：∀ {ι : Type u_3} {E : Type u_5} [inst : SeminormedAdd
CommGroup E] (s : Finset ι) {f : ι → E} {n : ι → ℝ},   (∀ b ∈ s, ‖f b‖ ≤ n b) → 
‖∑ b ∈ …
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
theorem cauchySeq_finset_of_norm_bounded_eventually {f : ι → E} {g : ι → ℝ} (hg : Summable g)
    (h : ∀ᶠ i in cofinite, ‖f i‖ ≤ g i) : CauchySeq fun s => ∑ i ∈ s, f i := by
  refine cauchySeq_finset_iff_vanishing_norm.2 fun ε hε => ?_
  rcases summable_iff_vanishing_norm.1 hg ε hε with ⟨s, hs⟩
  classical
  refine ⟨s ∪ h.toFinset, fun t ht => ?_⟩
  have : ∀ i ∈ t, ‖f i‖ ≤ g i := by
    intro i hi
    simp only [disjoint_left, mem_union, not_or, h.mem_toFinset, Set.mem_compl_iff,
      Classical.not_not] at ht
    exact (ht hi).2
  calc
    ‖∑ i ∈ t, f i‖ ≤ ∑ i ∈ t, g i := norm_sum_le_of_le _ this
    _ ≤ ‖∑ i ∈ t, g i‖ := le_abs_self _
    _ < ε := hs _ (ht.mono_right le_sup_left)
/-
**cauchySeq_finset_of_norm_bounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchySeq_finset_of_norm_bounded {f : ι -> E} {g : ι -> Real} (hg : Summab
le g) (h : forall i, ‖f i‖ <= g i) : CauchySeq fun s : Finset ι => ∑ i in s, f i
参数：hg : Summable g；h : forall i, ‖f i‖ <= g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `cauchySeq_finset_of_norm_bounded_eventually`：cauchySeq_finset_of_norm_bo
unded_eventually {f : ι -> E} {g : ι -> Real} (hg : Summable g) (h : forallᶠ i i
n cofinite, ‖f i‖ <= g i) : Cauch…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem cauchySeq_finset_of_norm_bounded {f : ι → E} {g : ι → ℝ} (hg : Summable g)
    (h : ∀ i, ‖f i‖ ≤ g i) : CauchySeq fun s : Finset ι => ∑ i ∈ s, f i :=
  cauchySeq_finset_of_norm_bounded_eventually hg <| Eventually.of_forall h

/-- A version of the **direct comparison test** for conditionally convergent series.
See `cauchySeq_finset_of_norm_bounded` for the same statement about absolutely convergent ones. -/
/-
**cauchySeq_range_of_norm_bounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchySeq_range_of_norm_bounded {f : Nat -> E} {g : Nat -> Real} (hg : Cau
chySeq fun n => ∑ i in range n, g i) (hf : forall i, ‖f i‖ <= g i) : CauchySeq f
un n => ∑ i in range n, f i
参数：hg : CauchySeq fun n => ∑ i in range n, g i；hf : forall i, ‖f i‖ <= g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.cauchySeq_iff'`：Metric.cauchySeq_iff' {u : β -> α} : CauchySeq u 
↔ forall ε > 0, exists N, forall n >= N, dist (u n) (u N) < ε
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_Ico_eq_sub`：∀ {δ : Type u_4} [inst : AddCommGroup δ] (f : ℕ →
 δ) {m n : ℕ},   m ≤ n → ∑ k ∈ Finset.Ico m n, f k = ∑ k ∈ Finset.range n, f k -
 ∑ k ∈ Fins…
· 使用定理 `norm_sum_le`：norm_sum_le {E} [SeminormedAddCommGroup E] (s : Finset ι) (
f : ι -> E) : ‖∑ i in s, f i‖ <= ∑ i in s, ‖f i‖
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b

--- 原说明 ---
A version of the **direct comparison test** for conditionally convergent series.
See `cauchySeq_finset_of_norm_bounded` for the same statement about absolutely c
onvergent ones.
-/
theorem cauchySeq_range_of_norm_bounded {f : ℕ → E} {g : ℕ → ℝ}
    (hg : CauchySeq fun n => ∑ i ∈ range n, g i) (hf : ∀ i, ‖f i‖ ≤ g i) :
    CauchySeq fun n => ∑ i ∈ range n, f i := by
  refine Metric.cauchySeq_iff'.2 fun ε hε => ?_
  refine (Metric.cauchySeq_iff'.1 hg ε hε).imp fun N hg n hn => ?_
  specialize hg n hn
  rw [dist_eq_norm, ← sum_Ico_eq_sub _ hn] at hg ⊢
  calc
    ‖∑ k ∈ Ico N n, f k‖ ≤ ∑ k ∈ _, ‖f k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ _, g k := sum_le_sum fun x _ => hf x
    _ ≤ ‖∑ k ∈ _, g k‖ := le_abs_self _
    _ < ε := hg
/-
**cauchySeq_finset_of_summable_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchySeq_finset_of_summable_norm {f : ι -> E} (hf : Summable fun a => ‖f 
a‖) : CauchySeq fun s : Finset ι => ∑ a in s, f a
参数：hf : Summable fun a => ‖f a‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `cauchySeq_finset_of_norm_bounded`：cauchySeq_finset_of_norm_bounded {f : 
ι -> E} {g : ι -> Real} (hg : Summable g) (h : forall i, ‖f i‖ <= g i) : CauchyS
eq fun s : Finset ι =>…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem cauchySeq_finset_of_summable_norm {f : ι → E} (hf : Summable fun a => ‖f a‖) :
    CauchySeq fun s : Finset ι => ∑ a ∈ s, f a :=
  cauchySeq_finset_of_norm_bounded hf fun _i => le_rfl

/-- If a function `f` is summable in norm, and along some sequence of finsets exhausting the space
its sum is converging to a limit `a`, then this holds along all finsets, i.e., `f` is summable
with sum `a`. -/
/-
**hasSum_of_subseq_of_summable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasSum_of_subseq_of_summable {f : ι -> E} (hf : Summable fun a => ‖f a‖) {
s : α -> Finset ι} {p : Filter α} [NeBot p] (hs : Tendsto s p atTop) {a : E} (ha
 : Tendsto (fun b => ∑ i in s b, f i) p (𝓝 a)) : HasSum f a
参数：hf : Summable fun a => ‖f a‖；hs : Tendsto s p atTop；ha : Tendsto (fun b => ∑ 
i in s b, f i) p (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_of_cauchySeq_of_subseq`：tendsto_nhds_of_cauchySeq_of_subseq
 [Preorder β] {u : β -> α} (hu : CauchySeq u) {ι : Type*} {f : ι -> β} {p : Filt
er ι} [NeBot p] (hf : Ten…
· 使用定理 `cauchySeq_finset_of_summable_norm`：cauchySeq_finset_of_summable_norm {f 
: ι -> E} (hf : Summable fun a => ‖f a‖) : CauchySeq fun s : Finset ι => ∑ a in 
s, f a

--- 原说明 ---
If a function `f` is summable in norm, and along some sequence of finsets exhaus
ting the space
its sum is converging to a limit `a`, then this holds along all finsets, i.e., `
f` is summable
with sum `a`.
-/
theorem hasSum_of_subseq_of_summable {f : ι → E} (hf : Summable fun a => ‖f a‖) {s : α → Finset ι}
    {p : Filter α} [NeBot p] (hs : Tendsto s p atTop) {a : E}
    (ha : Tendsto (fun b => ∑ i ∈ s b, f i) p (𝓝 a)) : HasSum f a :=
  tendsto_nhds_of_cauchySeq_of_subseq (cauchySeq_finset_of_summable_norm hf) hs ha
/-
**hasSum_iff_tendsto_nat_of_summable_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasSum_iff_tendsto_nat_of_summable_norm {f : Nat -> E} {a : E} (hf : Summa
ble fun i => ‖f i‖) : HasSum f a ↔ Tendsto (fun n : Nat => ∑ i in range n, f i) 
atTop (𝓝 a)
参数：hf : Summable fun i => ‖f i‖。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.tendsto_sum_nat`：∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_
1 : TopologicalSpace M] {m : M} {f : ℕ → M},   HasSum f m → Filter.Tendsto (fun 
n => ∑ i ∈ F…
· 使用定理 `hasSum_of_subseq_of_summable`：hasSum_of_subseq_of_summable {f : ι -> E} 
(hf : Summable fun a => ‖f a‖) {s : α -> Finset ι} {p : Filter α} [NeBot p] (hs 
: Tendsto s p atTo…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.tendsto_finset_range`：tendsto_finset_range : Tendsto Finset.range
 atTop atTop
-/
theorem hasSum_iff_tendsto_nat_of_summable_norm {f : ℕ → E} {a : E} (hf : Summable fun i => ‖f i‖) :
    HasSum f a ↔ Tendsto (fun n : ℕ => ∑ i ∈ range n, f i) atTop (𝓝 a) :=
  ⟨fun h => h.tendsto_sum_nat, fun h => hasSum_of_subseq_of_summable hf tendsto_finset_range h⟩

/-- The direct comparison test for series:  if the norm of `f` is bounded by a real function `g`
which is summable, then `f` is summable. -/
/-
**Summable.of_norm_bounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.of_norm_bounded [CompleteSpace E] {f : ι -> E} {g : ι -> Real} (h
g : Summable g) (h : forall i, ‖f i‖ <= g i) : Summable f
参数：hg : Summable g；h : forall i, ‖f i‖ <= g i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `summable_iff_cauchySeq_finset`：∀ {α : Type u_1} {β : Type u_2} [inst : U
niformSpace α] [inst_1 : AddCommMonoid α] [CompleteSpace α] {f : β → α},   Summa
ble f ↔ CauchySeq f…
· 使用定理 `cauchySeq_finset_of_norm_bounded`：cauchySeq_finset_of_norm_bounded {f : 
ι -> E} {g : ι -> Real} (hg : Summable g) (h : forall i, ‖f i‖ <= g i) : CauchyS
eq fun s : Finset ι =>…

--- 原说明 ---
The direct comparison test for series:  if the norm of `f` is bounded by a real 
function `g`
which is summable, then `f` is summable.
-/
theorem Summable.of_norm_bounded [CompleteSpace E] {f : ι → E} {g : ι → ℝ} (hg : Summable g)
    (h : ∀ i, ‖f i‖ ≤ g i) : Summable f := by
  rw [summable_iff_cauchySeq_finset]
  exact cauchySeq_finset_of_norm_bounded hg h
/-
**HasSum.enorm_le_of_bounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasSum.enorm_le_of_bounded {f : ι -> ε} {g : ι -> Real>=0∞} {a : ε} {b : R
eal>=0∞} (hf : HasSum f a) (hg : HasSum g b) (h : forall i, ‖f i‖ₑ <= g i) : ‖a‖
ₑ <= b
参数：hf : HasSum f a；hg : HasSum g b；h : forall i, ‖f i‖ₑ <= g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_tendsto_of_tendsto'`：le_of_tendsto_of_tendsto' {f g : β -> α} {b :
 Filter β} {a₁ a₂ : α} [hb : NeBot b] (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g 
b (𝓝 a₂)) (h : …
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `Filter.Tendsto.enorm`：Filter.Tendsto.enorm (h : Tendsto f l (𝓝 a)) : Ten
dsto (‖f ·‖ₑ) l (𝓝 ‖a‖ₑ)
· 使用定理 `enorm_sum_le_of_le`：∀ {ι : Type u_3} {ε : Type u_8} [inst : TopologicalS
pace ε] [inst_1 : ESeminormedAddCommMonoid ε] (s : Finset ι)   {f : ι → ε} {n : 
ι → ENNR…
-/
theorem HasSum.enorm_le_of_bounded {f : ι → ε} {g : ι → ℝ≥0∞} {a : ε} {b : ℝ≥0∞} (hf : HasSum f a)
    (hg : HasSum g b) (h : ∀ i, ‖f i‖ₑ ≤ g i) : ‖a‖ₑ ≤ b := by
  exact le_of_tendsto_of_tendsto' hf.enorm hg fun _s ↦ enorm_sum_le_of_le _ fun i _hi ↦ h i
/-
**HasSum.norm_le_of_bounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasSum.norm_le_of_bounded {f : ι -> E} {g : ι -> Real} {a : E} {b : Real} 
(hf : HasSum f a) (hg : HasSum g b) (h : forall i, ‖f i‖ <= g i) : ‖a‖ <= b
参数：hf : HasSum f a；hg : HasSum g b；h : forall i, ‖f i‖ <= g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_tendsto_of_tendsto'`：le_of_tendsto_of_tendsto' {f g : β -> α} {b :
 Filter β} {a₁ a₂ : α} [hb : NeBot b] (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g 
b (𝓝 a₂)) (h : …
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `Filter.Tendsto.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedA
ddGroup E] {a : E} {l : Filter α} {f : α → E},   Filter.Tendsto f l (nhds a) → F
ilter.Ten…
· 使用定理 `norm_sum_le_of_le`：∀ {ι : Type u_3} {E : Type u_5} [inst : SeminormedAdd
CommGroup E] (s : Finset ι) {f : ι → E} {n : ι → ℝ},   (∀ b ∈ s, ‖f b‖ ≤ n b) → 
‖∑ b ∈ …
-/
theorem HasSum.norm_le_of_bounded {f : ι → E} {g : ι → ℝ} {a : E} {b : ℝ} (hf : HasSum f a)
    (hg : HasSum g b) (h : ∀ i, ‖f i‖ ≤ g i) : ‖a‖ ≤ b := by
  exact le_of_tendsto_of_tendsto' hf.norm hg fun _s ↦ norm_sum_le_of_le _ fun i _hi ↦ h i

/-- Quantitative result associated to the direct comparison test for series:  If, for all `i`,
`‖f i‖ₑ ≤ g i`, then `‖∑' i, f i‖ₑ ≤ ∑' i, g i`. Note that we do not assume that `∑' i, f i` is
summable, and it might not be the case if `α` is not a complete space. -/
/-
**tsum_of_enorm_bounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsum_of_enorm_bounded {f : ι -> ε} {g : ι -> Real>=0∞} {a : Real>=0∞} (hg 
: HasSum g a) (h : forall i, ‖f i‖ₑ <= g i) : ‖∑' i : ι, f i‖ₑ <= a
参数：hg : HasSum g a；h : forall i, ‖f i‖ₑ <= g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.enorm_le_of_bounded`：HasSum.enorm_le_of_bounded {f : ι -> ε} {g :
 ι -> Real>=0∞} {a : ε} {b : Real>=0∞} (hf : HasSum f a) (hg : HasSum g b) (h : 
forall i, ‖f i‖ₑ…
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsum_eq_zero_of_not_summable`：∀ {α : Type u_1} {β : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → 
α}, ¬Summable f L …
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal

--- 原说明 ---
Quantitative result associated to the direct comparison test for series:  If, fo
r all `i`,
`‖f i‖ₑ ≤ g i`, then `‖∑' i, f i‖ₑ ≤ ∑' i, g i`. Note that we do not assume that
 `∑' i, f i` is
summable, and it might not be the case if `α` is not a complete space.
-/
theorem tsum_of_enorm_bounded {f : ι → ε} {g : ι → ℝ≥0∞} {a : ℝ≥0∞} (hg : HasSum g a)
    (h : ∀ i, ‖f i‖ₑ ≤ g i) : ‖∑' i : ι, f i‖ₑ ≤ a := by
  by_cases hf : Summable f
  · exact hf.hasSum.enorm_le_of_bounded hg h
  · simp [tsum_eq_zero_of_not_summable hf]
/-
**enorm_tsum_le_tsum_enorm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：enorm_tsum_le_tsum_enorm {f : ι -> ε} : ‖∑' i, f i‖ₑ <= ∑' i, ‖f i‖ₑ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsum_of_enorm_bounded`：tsum_of_enorm_bounded {f : ι -> ε} {g : ι -> Real
>=0∞} {a : Real>=0∞} (hg : HasSum g a) (h : forall i, ‖f i‖ₑ <= g i) : ‖∑' i : ι
, f i‖ₑ <= …
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem enorm_tsum_le_tsum_enorm {f : ι → ε} :
    ‖∑' i, f i‖ₑ ≤ ∑' i, ‖f i‖ₑ :=
  tsum_of_enorm_bounded ENNReal.summable.hasSum fun _i => le_rfl

/-- Quantitative result associated to the direct comparison test for series:  If `∑' i, g i` is
summable, and for all `i`, `‖f i‖ ≤ g i`, then `‖∑' i, f i‖ ≤ ∑' i, g i`. Note that we do not
assume that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete space. -/
/-
**tsum_of_norm_bounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsum_of_norm_bounded {f : ι -> E} {g : ι -> Real} {a : Real} (hg : HasSum 
g a) (h : forall i, ‖f i‖ <= g i) : ‖∑' i : ι, f i‖ <= a
参数：hg : HasSum g a；h : forall i, ‖f i‖ <= g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.norm_le_of_bounded`：HasSum.norm_le_of_bounded {f : ι -> E} {g : ι
 -> Real} {a : E} {b : Real} (hf : HasSum f a) (hg : HasSum g b) (h : forall i, 
‖f i‖ <= g i) :…
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsum_eq_zero_of_not_summable`：∀ {α : Type u_1} {β : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → 
α}, ¬Summable f L …
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `ge_of_tendsto'`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] 
[inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter 
β} […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖

--- 原说明 ---
Quantitative result associated to the direct comparison test for series:  If `∑'
 i, g i` is
summable, and for all `i`, `‖f i‖ ≤ g i`, then `‖∑' i, f i‖ ≤ ∑' i, g i`. Note t
hat we do not
assume that `∑' i, f i` is summable, and it might not be the case if `α` is not 
a complete space.
-/
theorem tsum_of_norm_bounded {f : ι → E} {g : ι → ℝ} {a : ℝ} (hg : HasSum g a)
    (h : ∀ i, ‖f i‖ ≤ g i) : ‖∑' i : ι, f i‖ ≤ a := by
  by_cases hf : Summable f
  · exact hf.hasSum.norm_le_of_bounded hg h
  · rw [tsum_eq_zero_of_not_summable hf, norm_zero]
    exact ge_of_tendsto' hg fun s => sum_nonneg fun i _hi => (norm_nonneg _).trans (h i)

/-- If `∑' i, ‖f i‖` is summable, then `‖∑' i, f i‖ ≤ (∑' i, ‖f i‖)`. Note that we do not assume
that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete space. -/
/-
**norm_tsum_le_tsum_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_tsum_le_tsum_norm {f : ι -> E} (hf : Summable fun i => ‖f i‖) : ‖∑' i
, f i‖ <= ∑' i, ‖f i‖
参数：hf : Summable fun i => ‖f i‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsum_of_norm_bounded`：tsum_of_norm_bounded {f : ι -> E} {g : ι -> Real} 
{a : Real} (hg : HasSum g a) (h : forall i, ‖f i‖ <= g i) : ‖∑' i : ι, f i‖ <= a
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
If `∑' i, ‖f i‖` is summable, then `‖∑' i, f i‖ ≤ (∑' i, ‖f i‖)`. Note that we d
o not assume
that `∑' i, f i` is summable, and it might not be the case if `α` is not a compl
ete space.
-/
theorem norm_tsum_le_tsum_norm {f : ι → E} (hf : Summable fun i => ‖f i‖) :
    ‖∑' i, f i‖ ≤ ∑' i, ‖f i‖ :=
  tsum_of_norm_bounded hf.hasSum fun _i => le_rfl

/-- Quantitative result associated to the direct comparison test for series: If `∑' i, g i` is
summable, and for all `i`, `‖f i‖₊ ≤ g i`, then `‖∑' i, f i‖₊ ≤ ∑' i, g i`. Note that we
do not assume that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete
space. -/
/-
**tsum_of_nnnorm_bounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsum_of_nnnorm_bounded {f : ι -> E} {g : ι -> Real>=0} {a : Real>=0} (hg :
 HasSum g a) (h : forall i, ‖f i‖₊ <= g i) : ‖∑' i : ι, f i‖₊ <= a
参数：hg : HasSum g a；h : forall i, ‖f i‖₊ <= g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsum_of_norm_bounded`：tsum_of_norm_bounded {f : ι -> E} {g : ι -> Real} 
{a : Real} (hg : HasSum g a) (h : forall i, ‖f i‖ <= g i) : ‖∑' i : ι, f i‖ <= a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a

--- 原说明 ---
Quantitative result associated to the direct comparison test for series: If `∑' 
i, g i` is
summable, and for all `i`, `‖f i‖₊ ≤ g i`, then `‖∑' i, f i‖₊ ≤ ∑' i, g i`. Note
 that we
do not assume that `∑' i, f i` is summable, and it might not be the case if `α` 
is not a complete
space.
-/
theorem tsum_of_nnnorm_bounded {f : ι → E} {g : ι → ℝ≥0} {a : ℝ≥0} (hg : HasSum g a)
    (h : ∀ i, ‖f i‖₊ ≤ g i) : ‖∑' i : ι, f i‖₊ ≤ a := by
  simp only [← NNReal.coe_le_coe, ← NNReal.hasSum_coe, coe_nnnorm] at *
  exact tsum_of_norm_bounded hg h

/-- If `∑' i, ‖f i‖₊` is summable, then `‖∑' i, f i‖₊ ≤ ∑' i, ‖f i‖₊`. Note that
we do not assume that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete
space. -/
/-
**nnnorm_tsum_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_tsum_le {f : ι -> E} (hf : Summable fun i => ‖f i‖₊) : ‖∑' i, f i‖₊
 <= ∑' i, ‖f i‖₊
参数：hf : Summable fun i => ‖f i‖₊。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsum_of_nnnorm_bounded`：tsum_of_nnnorm_bounded {f : ι -> E} {g : ι -> Re
al>=0} {a : Real>=0} (hg : HasSum g a) (h : forall i, ‖f i‖₊ <= g i) : ‖∑' i : ι
, f i‖₊ <= a
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
If `∑' i, ‖f i‖₊` is summable, then `‖∑' i, f i‖₊ ≤ ∑' i, ‖f i‖₊`. Note that
we do not assume that `∑' i, f i` is summable, and it might not be the case if `
α` is not a complete
space.
-/
theorem nnnorm_tsum_le {f : ι → E} (hf : Summable fun i => ‖f i‖₊) : ‖∑' i, f i‖₊ ≤ ∑' i, ‖f i‖₊ :=
  tsum_of_nnnorm_bounded hf.hasSum fun _i => le_rfl
/-
**tsum_enorm_ne_top_iff_summable_nnnorm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsum_enorm_ne_top_iff_summable_nnnorm {ι : Type*} {f : ι -> E} : ∑' i, ‖f 
i‖ₑ != ∞ ↔ Summable fun i => ‖f i‖₊
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tsum_enorm_ne_top_iff_summable_nnnorm {ι : Type*} {f : ι → E} :
    ∑' i, ‖f i‖ₑ ≠ ∞ ↔ Summable fun i ↦ ‖f i‖₊ := by
  simp only [enorm_eq_nnnorm, ENNReal.tsum_coe_ne_top_iff_summable]
/-
**tsum_enorm_ne_top_iff_summable_norm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tsum_enorm_ne_top_iff_summable_norm {ι : Type*} {f : ι -> E} : ∑' i, ‖f i‖
ₑ != ∞ ↔ Summable fun i => ‖f i‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma tsum_enorm_ne_top_iff_summable_norm {ι : Type*} {f : ι → E} :
    ∑' i, ‖f i‖ₑ ≠ ∞ ↔ Summable fun i ↦ ‖f i‖ := by
  simp only [tsum_enorm_ne_top_iff_summable_nnnorm, ← coe_nnnorm, NNReal.summable_coe]

variable [CompleteSpace E]

/-- Variant of the direct comparison test for series:  if the norm of `f` is eventually bounded by a
real function `g` which is summable, then `f` is summable. -/
/-
**Summable.of_norm_bounded_eventually** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.of_norm_bounded_eventually {f : ι -> E} {g : ι -> Real} (hg : Sum
mable g) (h : forallᶠ i in cofinite, ‖f i‖ <= g i) : Summable f
参数：hg : Summable g；h : forallᶠ i in cofinite, ‖f i‖ <= g i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `summable_iff_cauchySeq_finset`：∀ {α : Type u_1} {β : Type u_2} [inst : U
niformSpace α] [inst_1 : AddCommMonoid α] [CompleteSpace α] {f : β → α},   Summa
ble f ↔ CauchySeq f…
· 使用定理 `cauchySeq_finset_of_norm_bounded_eventually`：cauchySeq_finset_of_norm_bo
unded_eventually {f : ι -> E} {g : ι -> Real} (hg : Summable g) (h : forallᶠ i i
n cofinite, ‖f i‖ <= g i) : Cauch…

--- 原说明 ---
Variant of the direct comparison test for series:  if the norm of `f` is eventua
lly bounded by a
real function `g` which is summable, then `f` is summable.
-/
theorem Summable.of_norm_bounded_eventually {f : ι → E} {g : ι → ℝ} (hg : Summable g)
    (h : ∀ᶠ i in cofinite, ‖f i‖ ≤ g i) : Summable f :=
  summable_iff_cauchySeq_finset.2 <| cauchySeq_finset_of_norm_bounded_eventually hg h

/-- Variant of the direct comparison test for series:  if the norm of `f` is eventually bounded by a
real function `g` which is summable, then `f` is summable. -/
/-
**Summable.of_norm_bounded_eventually_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.of_norm_bounded_eventually_nat {f : Nat -> E} {g : Nat -> Real} (
hg : Summable g) (h : forallᶠ i in atTop, ‖f i‖ <= g i) : Summable f
参数：hg : Summable g；h : forallᶠ i in atTop, ‖f i‖ <= g i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.of_norm_bounded_eventually`：Summable.of_norm_bounded_eventually
 {f : ι -> E} {g : ι -> Real} (hg : Summable g) (h : forallᶠ i in cofinite, ‖f i
‖ <= g i) : Summable f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cofinite_eq_atTop`：Nat.cofinite_eq_atTop : @cofinite Nat = atTop

--- 原说明 ---
Variant of the direct comparison test for series:  if the norm of `f` is eventua
lly bounded by a
real function `g` which is summable, then `f` is summable.
-/
theorem Summable.of_norm_bounded_eventually_nat {f : ℕ → E} {g : ℕ → ℝ} (hg : Summable g)
    (h : ∀ᶠ i in atTop, ‖f i‖ ≤ g i) : Summable f :=
  .of_norm_bounded_eventually hg <| Nat.cofinite_eq_atTop ▸ h
/-
**Summable.of_nnnorm_bounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.of_nnnorm_bounded {f : ι -> E} {g : ι -> Real>=0} (hg : Summable 
g) (h : forall i, ‖f i‖₊ <= g i) : Summable f
参数：hg : Summable g；h : forall i, ‖f i‖₊ <= g i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.of_norm_bounded`：Summable.of_norm_bounded [CompleteSpace E] {f 
: ι -> E} {g : ι -> Real} (hg : Summable g) (h : forall i, ‖f i‖ <= g i) : Summa
ble f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.summable_coe`：summable_coe {f : α -> Real>=0} : (Summable (fun a 
=> (f a : Real)) L) ↔ Summable f L
-/
theorem Summable.of_nnnorm_bounded {f : ι → E} {g : ι → ℝ≥0} (hg : Summable g)
    (h : ∀ i, ‖f i‖₊ ≤ g i) : Summable f :=
  .of_norm_bounded (NNReal.summable_coe.2 hg) h
/-
**Summable.of_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.of_norm {f : ι -> E} (hf : Summable fun a => ‖f a‖) : Summable f
参数：hf : Summable fun a => ‖f a‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.of_norm_bounded`：Summable.of_norm_bounded [CompleteSpace E] {f 
: ι -> E} {g : ι -> Real} (hg : Summable g) (h : forall i, ‖f i‖ <= g i) : Summa
ble f
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Summable.of_norm {f : ι → E} (hf : Summable fun a => ‖f a‖) : Summable f :=
  .of_norm_bounded hf fun _i => le_rfl
/-
**Summable.of_nnnorm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.of_nnnorm {f : ι -> E} (hf : Summable fun a => ‖f a‖₊) : Summable
 f
参数：hf : Summable fun a => ‖f a‖₊。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.of_nnnorm_bounded`：Summable.of_nnnorm_bounded {f : ι -> E} {g :
 ι -> Real>=0} (hg : Summable g) (h : forall i, ‖f i‖₊ <= g i) : Summable f
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Summable.of_nnnorm {f : ι → E} (hf : Summable fun a => ‖f a‖₊) : Summable f :=
  .of_nnnorm_bounded hf fun _i => le_rfl
/-
**Summable.of_enorm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.of_enorm {f : ι -> E} (hf : ∑' a, ‖f a‖ₑ != ∞) : Summable f
参数：hf : ∑' a, ‖f a‖ₑ != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.of_nnnorm_bounded`：Summable.of_nnnorm_bounded {f : ι -> E} {g :
 ι -> Real>=0} (hg : Summable g) (h : forall i, ‖f i‖₊ <= g i) : Summable f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.tsum_coe_ne_top_iff_summable`：tsum_coe_ne_top_iff_summable {f : 
β -> Real>=0} : (∑' b, (f b : Real>=0∞)) != ∞ ↔ Summable f
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Summable.of_enorm {f : ι → E} (hf : ∑' a, ‖f a‖ₑ ≠ ∞) : Summable f :=
  Summable.of_nnnorm_bounded (tsum_coe_ne_top_iff_summable.1 hf) fun _i => le_rfl
