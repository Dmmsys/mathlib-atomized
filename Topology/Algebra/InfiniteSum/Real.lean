/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Infinite sum in the reals

This file provides lemmas about Cauchy sequences in terms of infinite sums and infinite sums valued
in the reals.
-/

public section

open Filter Finset NNReal Topology

variable {α β : Type*} [PseudoMetricSpace α] {f : ℕ → α} {a : α}

/-- If the distance between consecutive points of a sequence is estimated by a summable series,
then the original sequence is a Cauchy sequence. -/
/-
**cauchySeq_of_dist_le_of_summable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchySeq_of_dist_le_of_summable (d : Nat -> Real) (hf : forall n, dist (f
 n) (f n.succ) <= d n) (hd : Summable d) : CauchySeq f
参数：d : Nat -> Real；hf : forall n, dist (f n) (f n.succ) <= d n；hd : Summable d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `cauchySeq_of_edist_le_of_summable`：cauchySeq_of_edist_le_of_summable {f 
: Nat -> α} (d : Nat -> Real>=0) (hf : forall n, edist (f n) (f n.succ) <= d n) 
(hd : Summable d) : Cau…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a

--- 原说明 ---
If the distance between consecutive points of a sequence is estimated by a summa
ble series,
then the original sequence is a Cauchy sequence.
-/
theorem cauchySeq_of_dist_le_of_summable (d : ℕ → ℝ) (hf : ∀ n, dist (f n) (f n.succ) ≤ d n)
    (hd : Summable d) : CauchySeq f := by
  lift d to ℕ → ℝ≥0 using fun n ↦ dist_nonneg.trans (hf n)
  apply cauchySeq_of_edist_le_of_summable d (α := α) (f := f)
  · exact_mod_cast hf
  · exact_mod_cast hd
/-
**cauchySeq_of_summable_dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchySeq_of_summable_dist (h : Summable fun n => dist (f n) (f n.succ)) :
 CauchySeq f
参数：h : Summable fun n => dist (f n) (f n.succ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `cauchySeq_of_dist_le_of_summable`：cauchySeq_of_dist_le_of_summable (d : 
Nat -> Real) (hf : forall n, dist (f n) (f n.succ) <= d n) (hd : Summable d) : C
auchySeq f
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem cauchySeq_of_summable_dist (h : Summable fun n ↦ dist (f n) (f n.succ)) : CauchySeq f :=
  cauchySeq_of_dist_le_of_summable _ (fun _ ↦ le_rfl) h
/-
**dist_le_tsum_of_dist_le_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_le_tsum_of_dist_le_of_tendsto (d : Nat -> Real) (hf : forall n, dist 
(f n) (f n.succ) <= d n) (hd : Summable d) {a : α} (ha : Tendsto f atTop (𝓝 a)) 
(n : Nat) : dist (f n) a <= ∑' m, d (n + m)
参数：d : Nat -> Real；hf : forall n, dist (f n) (f n.succ) <= d n；hd : Summable d；h
a : Tendsto f atTop (𝓝 a)；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_tendsto`：le_of_tendsto {x : Filter β} [hx : NeBot x] (lim : Tendst
o f x (𝓝 a)) (h : forallᶠ c in x, f c <= b) : a <= b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Tendsto.dist`：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoMetri
cSpace α] {f g : β → α} {x : Filter β} {a b : α},   Filter.Tendsto f x (nhds a) 
→     Fil…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `dist_le_Ico_sum_of_dist_le`：dist_le_Ico_sum_of_dist_le {f : Nat -> α} {m
 n} (hmn : m <= n) {d : Nat -> Real} (hd : forall {k}, m <= k -> k < n -> dist (
f k) (f (k + 1))…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_Ico_eq_sum_range`：∀ {M : Type u_3} [inst : AddCommMonoid M] (
f : ℕ → M) (m n : ℕ),   ∑ k ∈ Finset.Ico m n, f k = ∑ k ∈ Finset.range (n - m), 
f (m + k)
· 使用定理 `Summable.sum_le_tsum`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilt
er ι} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [i
nst_3 : To…
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `Summable.comp_injective`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
[inst : UniformSpace α] [inst_1 : AddCommGroup α] [IsUniformAddGroup α]   {f : β
 → α} [Comple…
· 使用定理 `instIsUniformAddGroupReal`：IsUniformAddGroup ℝ
· 使用定理 `add_right_injective`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G]
 (a : G), Function.Injective fun x => a + x
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
-/
theorem dist_le_tsum_of_dist_le_of_tendsto (d : ℕ → ℝ) (hf : ∀ n, dist (f n) (f n.succ) ≤ d n)
    (hd : Summable d) {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : ℕ) :
    dist (f n) a ≤ ∑' m, d (n + m) := by
  refine le_of_tendsto (tendsto_const_nhds.dist ha) (eventually_atTop.2 ⟨n, fun m hnm ↦ ?_⟩)
  refine le_trans (dist_le_Ico_sum_of_dist_le hnm fun _ _ ↦ hf _) ?_
  rw [sum_Ico_eq_sum_range]
  refine Summable.sum_le_tsum (range _) (fun _ _ ↦ le_trans dist_nonneg (hf _)) ?_
  exact hd.comp_injective (add_right_injective n)
/-
**dist_le_tsum_of_dist_le_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_le_tsum_of_dist_le_of_tendsto (d : Nat -> Real) (hf : forall n, dist 
(f n) (f n.succ) <= d n) (hd : Summable d) {a : α} (ha : Tendsto f atTop (𝓝 a)) 
(n : Nat) : dist (f n) a <= ∑' m, d (n + m)
参数：d : Nat -> Real；hf : forall n, dist (f n) (f n.succ) <= d n；hd : Summable d；h
a : Tendsto f atTop (𝓝 a)；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_tendsto`：le_of_tendsto {x : Filter β} [hx : NeBot x] (lim : Tendst
o f x (𝓝 a)) (h : forallᶠ c in x, f c <= b) : a <= b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Tendsto.dist`：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoMetri
cSpace α] {f g : β → α} {x : Filter β} {a b : α},   Filter.Tendsto f x (nhds a) 
→     Fil…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `dist_le_Ico_sum_of_dist_le`：dist_le_Ico_sum_of_dist_le {f : Nat -> α} {m
 n} (hmn : m <= n) {d : Nat -> Real} (hd : forall {k}, m <= k -> k < n -> dist (
f k) (f (k + 1))…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_Ico_eq_sum_range`：∀ {M : Type u_3} [inst : AddCommMonoid M] (
f : ℕ → M) (m n : ℕ),   ∑ k ∈ Finset.Ico m n, f k = ∑ k ∈ Finset.range (n - m), 
f (m + k)
· 使用定理 `Summable.sum_le_tsum`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilt
er ι} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [i
nst_3 : To…
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `Summable.comp_injective`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
[inst : UniformSpace α] [inst_1 : AddCommGroup α] [IsUniformAddGroup α]   {f : β
 → α} [Comple…
· 使用定理 `instIsUniformAddGroupReal`：IsUniformAddGroup ℝ
· 使用定理 `add_right_injective`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G]
 (a : G), Function.Injective fun x => a + x
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
-/
theorem dist_le_tsum_of_dist_le_of_tendsto₀ (d : ℕ → ℝ) (hf : ∀ n, dist (f n) (f n.succ) ≤ d n)
    (hd : Summable d) (ha : Tendsto f atTop (𝓝 a)) : dist (f 0) a ≤ tsum d := by
  simpa only [zero_add] using dist_le_tsum_of_dist_le_of_tendsto d hf hd ha 0
/-
**dist_le_tsum_dist_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_le_tsum_dist_of_tendsto (h : Summable fun n => dist (f n) (f n.succ))
 (ha : Tendsto f atTop (𝓝 a)) (n) : dist (f n) a <= ∑' m, dist (f (n + m)) (f (n
 + m).succ)
参数：h : Summable fun n => dist (f n) (f n.succ)；ha : Tendsto f atTop (𝓝 a)；n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dist_le_tsum_of_dist_le_of_tendsto`：dist_le_tsum_of_dist_le_of_tendsto (
d : Nat -> Real) (hf : forall n, dist (f n) (f n.succ) <= d n) (hd : Summable d)
 {a : α} (ha : Tendsto f…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem dist_le_tsum_dist_of_tendsto (h : Summable fun n ↦ dist (f n) (f n.succ))
    (ha : Tendsto f atTop (𝓝 a)) (n) : dist (f n) a ≤ ∑' m, dist (f (n + m)) (f (n + m).succ) :=
  show dist (f n) a ≤ ∑' m, (fun x ↦ dist (f x) (f x.succ)) (n + m) from
    dist_le_tsum_of_dist_le_of_tendsto (fun n ↦ dist (f n) (f n.succ)) (fun _ ↦ le_rfl) h ha n
/-
**dist_le_tsum_dist_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_le_tsum_dist_of_tendsto (h : Summable fun n => dist (f n) (f n.succ))
 (ha : Tendsto f atTop (𝓝 a)) (n) : dist (f n) a <= ∑' m, dist (f (n + m)) (f (n
 + m).succ)
参数：h : Summable fun n => dist (f n) (f n.succ)；ha : Tendsto f atTop (𝓝 a)；n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dist_le_tsum_of_dist_le_of_tendsto`：dist_le_tsum_of_dist_le_of_tendsto (
d : Nat -> Real) (hf : forall n, dist (f n) (f n.succ) <= d n) (hd : Summable d)
 {a : α} (ha : Tendsto f…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem dist_le_tsum_dist_of_tendsto₀ (h : Summable fun n ↦ dist (f n) (f n.succ))
    (ha : Tendsto f atTop (𝓝 a)) : dist (f 0) a ≤ ∑' n, dist (f n) (f n.succ) := by
  simpa only [zero_add] using dist_le_tsum_dist_of_tendsto h ha 0

section summable

/-
**not_summable_iff_tendsto_nat_atTop_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_summable_iff_tendsto_nat_atTop_of_nonneg {f : Nat -> Real} (hf : foral
l n, 0 <= f n) : ¬Summable f ↔ Tendsto (fun n : Nat => ∑ i in Finset.range n, f 
i) atTop atTop
参数：hf : forall n, 0 <= f n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NNReal.not_summable_iff_tendsto_nat_atTop`：not_summable_iff_tendsto_nat_
atTop {f : Nat -> Real>=0} : ¬Summable f ↔ Tendsto (fun n : Nat => ∑ i in Finset
.range n, f i) atTop atTop
-/
theorem not_summable_iff_tendsto_nat_atTop_of_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) :
    ¬Summable f ↔ Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop atTop := by
  lift f to ℕ → ℝ≥0 using hf
  simpa using mod_cast NNReal.not_summable_iff_tendsto_nat_atTop
/-
**summable_iff_not_tendsto_nat_atTop_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_iff_not_tendsto_nat_atTop_of_nonneg {f : Nat -> Real} (hf : foral
l n, 0 <= f n) : Summable f ↔ ¬Tendsto (fun n : Nat => ∑ i in Finset.range n, f 
i) atTop atTop
参数：hf : forall n, 0 <= f n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `not_summable_iff_tendsto_nat_atTop_of_nonneg`：not_summable_iff_tendsto_n
at_atTop_of_nonneg {f : Nat -> Real} (hf : forall n, 0 <= f n) : ¬Summable f ↔ T
endsto (fun n : Nat => ∑ i in Fins…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem summable_iff_not_tendsto_nat_atTop_of_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) :
    Summable f ↔ ¬Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop atTop := by
  rw [← not_iff_not, Classical.not_not, not_summable_iff_tendsto_nat_atTop_of_nonneg hf]
/-
**summable_sigma_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_sigma_of_nonneg {α} {β : α -> Type*} {f : (Σ x, β x) -> Real} (hf
 : forall x, 0 <= f x) : Summable f ↔ (forall x, Summable fun y => f ⟨x, y⟩) ∧ S
ummable fun x => ∑' y, f ⟨x, y⟩
参数：Σ x, β x；hf : forall x, 0 <= f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NNReal.summable_sigma`：summable_sigma {β : α -> Type*} {f : (Σ x, β x) -
> Real>=0} : Summable f ↔ (forall x, Summable fun y => f ⟨x, y⟩) ∧ Summable fun 
x => ∑' y, …
-/
theorem summable_sigma_of_nonneg {α} {β : α → Type*} {f : (Σ x, β x) → ℝ} (hf : ∀ x, 0 ≤ f x) :
    Summable f ↔ (∀ x, Summable fun y => f ⟨x, y⟩) ∧ Summable fun x => ∑' y, f ⟨x, y⟩ := by
  lift f to (Σ x, β x) → ℝ≥0 using hf
  simpa using mod_cast NNReal.summable_sigma
/-
**summable_partition** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：summable_partition {α β : Type*} {f : β -> Real} (hf : 0 <= f) {s : α -> S
et β} (hs : forall i, exists! j, i in s j) : Summable f ↔ (forall j, Summable fu
n i : s j => f i) ∧ Summable fun j => ∑' i : s j, f i
参数：hf : 0 <= f；hs : forall i, exists! j, i in s j。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.summable_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst
 : AddCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   (e : γ ≃ β), Sum
mable (f…
· 使用定理 `summable_sigma_of_nonneg`：summable_sigma_of_nonneg {α} {β : α -> Type*} 
{f : (Σ x, β x) -> Real} (hf : forall x, 0 <= f x) : Summable f ↔ (forall x, Sum
mable fun y =>…
-/
lemma summable_partition {α β : Type*} {f : β → ℝ} (hf : 0 ≤ f) {s : α → Set β}
    (hs : ∀ i, ∃! j, i ∈ s j) : Summable f ↔
      (∀ j, Summable fun i : s j ↦ f i) ∧ Summable fun j ↦ ∑' i : s j, f i := by
  simpa only [← (Set.sigmaEquiv s hs).summable_iff] using! summable_sigma_of_nonneg (fun _ ↦ hf _)
/-
**summable_prod_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_prod_of_nonneg {α β} {f : (α × β) -> Real} (hf : 0 <= f) : Summab
le f ↔ (forall x, Summable fun y => f (x, y)) ∧ Summable fun x => ∑' y, f (x, y)
参数：α × β；hf : 0 <= f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.summable_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst
 : AddCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   (e : γ ≃ β), Sum
mable (f…
· 使用定理 `summable_sigma_of_nonneg`：summable_sigma_of_nonneg {α} {β : α -> Type*} 
{f : (Σ x, β x) -> Real} (hf : forall x, 0 <= f x) : Summable f ↔ (forall x, Sum
mable fun y =>…
-/
theorem summable_prod_of_nonneg {α β} {f : (α × β) → ℝ} (hf : 0 ≤ f) :
    Summable f ↔ (∀ x, Summable fun y ↦ f (x, y)) ∧ Summable fun x ↦ ∑' y, f (x, y) :=
  (Equiv.sigmaEquivProd _ _).summable_iff.symm.trans <| summable_sigma_of_nonneg fun _ ↦ hf _
/-
**summable_of_sum_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_of_sum_le {ι : Type*} {f : ι -> Real} {c : Real} (hf : 0 <= f) (h
 : forall u : Finset ι, ∑ x in u, f x <= c) : Summable f
参数：hf : 0 <= f；h : forall u : Finset ι, ∑ x in u, f x <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_atTop_ciSup`：tendsto_atTop_ciSup (h_mono : Monotone f) (hbdd : B
ddAbove <| range f) : Tendsto f atTop (𝓝 (⨆ i, f i))
· 使用定理 `LinearOrder.supConvergenceClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : LinearOrder α] [OrderTopology α], SupConvergenceClass α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Finset.sum_mono_set_of_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : A
ddCommMonoid N] [inst_1 : Preorder N] {f : ι → N} [AddLeftMono N],   (∀ (x : ι),
 0 ≤ f x) → Monoton…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem summable_of_sum_le {ι : Type*} {f : ι → ℝ} {c : ℝ} (hf : 0 ≤ f)
    (h : ∀ u : Finset ι, ∑ x ∈ u, f x ≤ c) : Summable f :=
  ⟨⨆ u : Finset ι, ∑ x ∈ u, f x,
    tendsto_atTop_ciSup (Finset.sum_mono_set_of_nonneg hf) ⟨c, fun _ ⟨u, hu⟩ => hu ▸ h u⟩⟩
/-
**summable_of_sum_range_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_of_sum_range_le {f : Nat -> Real} {c : Real} (hf : forall n, 0 <=
 f n) (h : forall n, ∑ i in Finset.range n, f i <= c) : Summable f
参数：hf : forall n, 0 <= f n；h : forall n, ∑ i in Finset.range n, f i <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `summable_iff_not_tendsto_nat_atTop_of_nonneg`：summable_iff_not_tendsto_n
at_atTop_of_nonneg {f : Nat -> Real} (hf : forall n, 0 <= f n) : Summable f ↔ ¬T
endsto (fun n : Nat => ∑ i in Fins…
· 使用定理 `Filter.exists_lt_of_tendsto_atTop`：exists_lt_of_tendsto_atTop [NoMaxOrde
r β] (h : Tendsto u atTop atTop) (a : α) (b : β) : exists a', a <= a' ∧ b < u a'
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
-/
theorem summable_of_sum_range_le {f : ℕ → ℝ} {c : ℝ} (hf : ∀ n, 0 ≤ f n)
    (h : ∀ n, ∑ i ∈ Finset.range n, f i ≤ c) : Summable f := by
  refine (summable_iff_not_tendsto_nat_atTop_of_nonneg hf).2 fun H => ?_
  rcases exists_lt_of_tendsto_atTop H 0 c with ⟨n, -, hn⟩
  exact lt_irrefl _ (hn.trans_le (h n))
/-
**Real.tsum_le_of_sum_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.tsum_le_of_sum_le {ι : Type*} {f : ι -> Real} {c : Real} (hf : 0 <= f
) (h : forall u : Finset ι, ∑ x in u, f x <= c) : ∑' x, f x <= c
参数：hf : 0 <= f；h : forall u : Finset ι, ∑ x in u, f x <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tsum_le_of_sum_le`：∀ {ι : Type u_1} {α : Type u_3} {L : Summati
onFilter ι} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [inst_2 : Topologic
alSpace α] [Orde…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `summable_of_sum_le`：summable_of_sum_le {ι : Type*} {f : ι -> Real} {c : 
Real} (hf : 0 <= f) (h : forall u : Finset ι, ∑ x in u, f x <= c) : Summable f
-/
theorem Real.tsum_le_of_sum_le {ι : Type*} {f : ι → ℝ} {c : ℝ} (hf : 0 ≤ f)
    (h : ∀ u : Finset ι, ∑ x ∈ u, f x ≤ c) : ∑' x, f x ≤ c :=
  (summable_of_sum_le hf h).tsum_le_of_sum_le h
/-
**Real.tsum_le_of_sum_range_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.tsum_le_of_sum_range_le {f : Nat -> Real} {c : Real} (hf : forall n, 
0 <= f n) (h : forall n, ∑ i in Finset.range n, f i <= c) : ∑' n, f n <= c
参数：hf : forall n, 0 <= f n；h : forall n, ∑ i in Finset.range n, f i <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tsum_le_of_sum_range_le`：∀ {α : Type u_3} [inst : Preorder α] [
inst_1 : AddCommMonoid α] [inst_2 : TopologicalSpace α] {c : α}   [ClosedIicTopo
logy α] {f : ℕ → α}, S…
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `summable_of_sum_range_le`：summable_of_sum_range_le {f : Nat -> Real} {c 
: Real} (hf : forall n, 0 <= f n) (h : forall n, ∑ i in Finset.range n, f i <= c
) : Summable f
-/
theorem Real.tsum_le_of_sum_range_le {f : ℕ → ℝ} {c : ℝ} (hf : ∀ n, 0 ≤ f n)
    (h : ∀ n, ∑ i ∈ Finset.range n, f i ≤ c) : ∑' n, f n ≤ c :=
  (summable_of_sum_range_le hf h).tsum_le_of_sum_range_le h

/-- If a sequence `f` with non-negative terms is dominated by a sequence `g` with summable
series and at least one term of `f` is strictly smaller than the corresponding term in `g`,
then the series of `f` is strictly smaller than the series of `g`. -/
/-
**Summable.tsum_lt_tsum_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Summable`。
形式化陈述：∀ {i : ℕ} {f g : ℕ → ℝ},   (∀ (b : ℕ), 0 ≤ f b) → (∀ (b : ℕ), f b ≤ g b) →
 f i < g i → Summable g → ∑' (n : ℕ), f n < ∑' (n : ℕ), g n
参数：∀ (b : ℕ), 0 ≤ f b；∀ (b : ℕ), f b ≤ g b；n : ℕ；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tsum_lt_tsum`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFil
ter ι} [inst : AddCommGroup α] [inst_1 : PartialOrder α]   [IsOrderedAddMonoid α
] [inst_3 :…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Summable.of_nonneg_of_le`：Summable.of_nonneg_of_le {f g : β -> Real} (hg
 : forall b, 0 <= g b) (hgf : forall b, g b <= f b) (hf : Summable f) : Summable
 g

--- 原说明 ---
If a sequence `f` with non-negative terms is dominated by a sequence `g` with su
mmable
series and at least one term of `f` is strictly smaller than the corresponding t
erm in `g`,
then the series of `f` is strictly smaller than the series of `g`.
-/
protected theorem Summable.tsum_lt_tsum_of_nonneg {i : ℕ} {f g : ℕ → ℝ} (h0 : ∀ b : ℕ, 0 ≤ f b)
    (h : ∀ b : ℕ, f b ≤ g b) (hi : f i < g i) (hg : Summable g) : ∑' n, f n < ∑' n, g n :=
  Summable.tsum_lt_tsum h hi (.of_nonneg_of_le h0 h hg) hg

end summable

