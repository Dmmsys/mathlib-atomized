/-
Copyright (c) 2023 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Completeness of normed groups

This file includes a completeness criterion for normed additive groups in terms of convergent
series.

## Main results

* `NormedAddCommGroup.completeSpace_of_summable_imp_tendsto`: A normed additive group is
  complete if any absolutely convergent series converges in the space.

## References

* [bergh_lofstrom_1976] `NormedAddCommGroup.completeSpace_of_summable_imp_tendsto` and
  `NormedAddCommGroup.summable_imp_tendsto_of_complete` correspond to the two directions of
  Lemma 2.2.1.

## Tags

CompleteSpace, CauchySeq
-/

public section

open scoped Topology
open Filter Finset

section Metric

variable {α : Type*} [PseudoMetricSpace α]

/-
**Metric.exists_subseq_summable_dist_of_cauchySeq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Metric.exists_subseq_summable_dist_of_cauchySeq (u : Nat -> α) (hu : Cauch
ySeq u) : exists f : Nat -> Nat, StrictMono f ∧ Summable fun i => dist (u (f (i 
+ 1))) (u (f i))
参数：u : Nat -> α；hu : CauchySeq u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Metric.exists_subseq_bounded_of_cauchySeq`：Metric.exists_subseq_bounded_
of_cauchySeq (u : Nat -> α) (hu : CauchySeq u) (b : Nat -> Real) (hb : forall n,
 0 < b n) : exists f : Nat -> N…
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Summable.of_nonneg_of_le`：Summable.of_nonneg_of_le {f g : β -> Real} (hg
 : forall b, 0 <= g b) (hgf : forall b, g b <= f b) (hf : Summable f) : Summable
 g
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `summable_geometric_two`：summable_geometric_two : Summable fun n : Nat =>
 ((1 : Real) / 2) ^ n
-/
lemma Metric.exists_subseq_summable_dist_of_cauchySeq (u : ℕ → α) (hu : CauchySeq u) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ Summable fun i => dist (u (f (i + 1))) (u (f i)) := by
  obtain ⟨f, hf₁, hf₂⟩ := Metric.exists_subseq_bounded_of_cauchySeq u hu
    (fun n => (1 / (2 : ℝ)) ^ n) (fun n => by positivity)
  refine ⟨f, hf₁, ?_⟩
  refine Summable.of_nonneg_of_le (fun n => by positivity) ?_ summable_geometric_two
  exact fun n => le_of_lt <| hf₂ n (f (n + 1)) <| hf₁.monotone (Nat.le_add_right n 1)

end Metric

section Normed

variable {E : Type*} [NormedAddCommGroup E]

/-- A normed additive group is complete if any absolutely convergent series converges in the
space. -/
/-
**NormedAddCommGroup.completeSpace_of_summable_imp_tendsto** 是 Mathlib 中的一个引理，位于
命名空间 ``。
形式化陈述：NormedAddCommGroup.completeSpace_of_summable_imp_tendsto (h : forall u : N
at -> E, Summable (‖u ·‖) -> exists a, Tendsto (fun n => ∑ i in range n, u i) at
Top (𝓝 a)) : CompleteSpace E
参数：h : forall u : Nat -> E, Summable (‖u ·‖) -> exists a, Tendsto (fun n => ∑ i 
in range n, u i) atTop (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.complete_of_cauchySeq_tendsto`：Metric.complete_of_cauchySeq_tends
to : (forall u : Nat -> α, CauchySeq u -> exists a, Tendsto u atTop (𝓝 a)) -> Co
mpleteSpace α
· 使用引理 `Metric.exists_subseq_summable_dist_of_cauchySeq`：Metric.exists_subseq_su
mmable_dist_of_cauchySeq (u : Nat -> α) (hu : CauchySeq u) : exists f : Nat -> N
at, StrictMono f ∧ Summable fun i => …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_range_sub`：∀ {G : Type u_3} [inst : AddCommGroup G] (f : ℕ → 
G) (n : ℕ), ∑ i ∈ Finset.range n, (f (i + 1) - f i) = f n - f 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `tendsto_nhds_of_cauchySeq_of_subseq`：tendsto_nhds_of_cauchySeq_of_subseq
 [Preorder β] {u : β -> α} (hu : CauchySeq u) {ι : Type*} {f : ι -> β} {p : Filt
er ι} [NeBot p] (hf : Ten…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `StrictMono.tendsto_atTop`：∀ {φ : ℕ → ℕ}, StrictMono φ → Filter.Tendsto φ
 Filter.atTop Filter.atTop
· 使用定理 `Filter.Tendsto.add_const`：∀ {M : Type u_1} [inst : TopologicalSpace M] [
inst_1 : Add M] [SeparatelyContinuousAdd M] {α : Type u_2} {f : α → M}   {x : Fi
lter α} {a : M…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a

--- 原说明 ---
A normed additive group is complete if any absolutely convergent series converge
s in the
space.
-/
lemma NormedAddCommGroup.completeSpace_of_summable_imp_tendsto
    (h : ∀ u : ℕ → E,
      Summable (‖u ·‖) → ∃ a, Tendsto (fun n => ∑ i ∈ range n, u i) atTop (𝓝 a)) :
    CompleteSpace E := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨f, hf₁, hf₂⟩ := Metric.exists_subseq_summable_dist_of_cauchySeq u hu
  simp only [dist_eq_norm] at hf₂
  let v n := u (f (n + 1)) - u (f n)
  have hv_sum : (fun n => (∑ i ∈ range n, v i)) = fun n => u (f n) - u (f 0) := by
    ext n
    exact sum_range_sub (u ∘ f) n
  obtain ⟨a, ha⟩ := h v hf₂
  refine ⟨a + u (f 0), ?_⟩
  refine tendsto_nhds_of_cauchySeq_of_subseq hu hf₁.tendsto_atTop ?_
  rw [hv_sum] at ha
  have h₁ : Tendsto (fun n => u (f n) - u (f 0) + u (f 0)) atTop (𝓝 (a + u (f 0))) :=
    Tendsto.add_const _ ha
  simpa only [sub_add_cancel] using! h₁

/-- In a complete normed additive group, every absolutely convergent series converges in the
space. -/
/-
**NormedAddCommGroup.summable_imp_tendsto_of_complete** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：NormedAddCommGroup.summable_imp_tendsto_of_complete [CompleteSpace E] (u :
 Nat -> E) (hu : Summable (‖u ·‖)) : exists a, Tendsto (fun n => ∑ i in range n,
 u i) atTop (𝓝 a)
参数：u : Nat -> E；hu : Summable (‖u ·‖)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `cauchySeq_tendsto_of_complete`：cauchySeq_tendsto_of_complete [Preorder β
] [CompleteSpace α] {u : β -> α} (H : CauchySeq u) : exists x, Tendsto u atTop (
𝓝 x)
· 使用定理 `cauchySeq_of_summable_dist`：cauchySeq_of_summable_dist (h : Summable fun
 n => dist (f n) (f n.succ)) : CauchySeq f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `sub_add_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a - (a + b) = -b
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
In a complete normed additive group, every absolutely convergent series converge
s in the
space.
-/
lemma NormedAddCommGroup.summable_imp_tendsto_of_complete [CompleteSpace E] (u : ℕ → E)
    (hu : Summable (‖u ·‖)) : ∃ a, Tendsto (fun n => ∑ i ∈ range n, u i) atTop (𝓝 a) := by
  refine cauchySeq_tendsto_of_complete <| cauchySeq_of_summable_dist ?_
  simp [dist_eq_norm, sum_range_succ, hu]

/-- In a normed additive group, every absolutely convergent series converges in the
space iff the space is complete. -/
/-
**NormedAddCommGroup.summable_imp_tendsto_iff_completeSpace** 是 Mathlib 中的一个引理，位
于命名空间 ``。
形式化陈述：NormedAddCommGroup.summable_imp_tendsto_iff_completeSpace : (forall u : Na
t -> E, Summable (‖u ·‖) -> exists a, Tendsto (fun n => ∑ i in range n, u i) atT
op (𝓝 a)) ↔ CompleteSpace E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NormedAddCommGroup.completeSpace_of_summable_imp_tendsto`：NormedAddCommG
roup.completeSpace_of_summable_imp_tendsto (h : forall u : Nat -> E, Summable (‖
u ·‖) -> exists a, Tendsto (fun n => ∑ i in ra…
· 使用引理 `NormedAddCommGroup.summable_imp_tendsto_of_complete`：NormedAddCommGroup.
summable_imp_tendsto_of_complete [CompleteSpace E] (u : Nat -> E) (hu : Summable
 (‖u ·‖)) : exists a, Tendsto (fun n => ∑…

--- 原说明 ---
In a normed additive group, every absolutely convergent series converges in the
space iff the space is complete.
-/
lemma NormedAddCommGroup.summable_imp_tendsto_iff_completeSpace :
    (∀ u : ℕ → E, Summable (‖u ·‖) → ∃ a, Tendsto (fun n => ∑ i ∈ range n, u i) atTop (𝓝 a))
     ↔ CompleteSpace E :=
  ⟨completeSpace_of_summable_imp_tendsto, fun _ u hu => summable_imp_tendsto_of_complete u hu⟩

end Normed

