/-
Copyright (c) 2024 Edward van de Meent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Edward van de Meent
-/
module

public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Tactic.Bound

/-!
# Infinite sums in extended nonnegative reals

This file proves results on infinite sums in `ℝ≥0∞`.

In particular, we give lemmas relating sums of constants to the cardinality of the domain of
these sums.

## TODO

+ Once we have a topology on `ENat`, provide an `ENat`-valued version
+ Provide versions which sum over the whole type.
-/

public section

open Set Function

open Filter Function Metric Set Topology
open scoped Finset ENNReal NNReal

variable {α : Type*} {β : Type*} {γ : Type*}

namespace ENNReal

variable {a b : ℝ≥0∞} {r : ℝ≥0} {x : ℝ≥0∞} {ε : ℝ≥0∞}

section tsum

variable {f g : α → ℝ≥0∞}

@[norm_cast]
/-
**ENNReal.hasSum_coe** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} {f : α → NNReal} {r : NNReal}, HasSum (fun a => ↑(f a)) ↑
r ↔ HasSum f r
参数：fun a => ↑(f a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem hasSum_coe {f : α → ℝ≥0} {r : ℝ≥0} :
    HasSum (fun a => (f a : ℝ≥0∞)) ↑r ↔ HasSum f r := by
  simp only [HasSum, ← ofNNReal_finsetSum, tendsto_coe]
/-
**ENNReal.tsum_coe_eq** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} {r : NNReal} {f : α → NNReal}, HasSum f r → ∑' (a : α), ↑
(f a) = ↑r
参数：a : α；f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.hasSum_coe`：∀ {α : Type u_1} {f : α → NNReal} {r : NNReal}, HasS
um (fun a => ↑(f a)) ↑r ↔ HasSum f r
-/
protected theorem tsum_coe_eq {f : α → ℝ≥0} (h : HasSum f r) : (∑' a, (f a : ℝ≥0∞)) = r :=
  (ENNReal.hasSum_coe.2 h).tsum_eq
/-
**ENNReal.coe_tsum** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} {f : α → NNReal}, Summable f → ↑(tsum f) = ∑' (a : α), ↑(
f a)
参数：tsum f；a : α；f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `ENNReal.tsum_coe_eq`：∀ {α : Type u_1} {r : NNReal} {f : α → NNReal}, Has
Sum f r → ∑' (a : α), ↑(f a) = ↑r
-/
protected theorem coe_tsum {f : α → ℝ≥0} : Summable f → ↑(tsum f) = ∑' a, (f a : ℝ≥0∞)
  | ⟨r, hr⟩ => by rw [hr.tsum_eq, ENNReal.tsum_coe_eq hr]
/-
**ENNReal.hasSum** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} {f : α → ENNReal}, HasSum f (⨆ s, ∑ a ∈ s, f a)
参数：⨆ s, ∑ a ∈ s, f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_atTop_iSup`：tendsto_atTop_iSup (h_mono : Monotone f) : Tendsto f
 atTop (𝓝 (⨆ i, f i))
· 使用定理 `LinearOrder.supConvergenceClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : LinearOrder α] [OrderTopology α], SupConvergenceClass α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `Finset.sum_le_sum_of_subset`：∀ {ι : Type u_1} {M : Type u_4} [inst : Add
CommMonoid M] [inst_1 : Preorder M] [CanonicallyOrderedAdd M] {f : ι → M}   {s t
 : Finset ι}, s ⊆…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
protected theorem hasSum : HasSum f (⨆ s : Finset α, ∑ a ∈ s, f a) :=
  tendsto_atTop_iSup fun _ _ => Finset.sum_le_sum_of_subset

@[simp]
/-
**ENNReal.summable** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.hasSum`：∀ {α : Type u_1} {f : α → ENNReal}, HasSum f (⨆ s, ∑ a ∈
 s, f a)
-/
protected theorem summable : Summable f :=
  ⟨_, ENNReal.hasSum⟩

macro_rules | `(tactic| gcongr_discharger) => `(tactic| apply ENNReal.summable)
/-
**ENNReal.tsum_coe_ne_top_iff_summable** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tsum_coe_ne_top_iff_summable {f : β -> Real>=0} : (∑' b, (f b : Real>=0∞))
 != ∞ ↔ Summable f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.hasSum_coe`：∀ {α : Type u_1} {f : α → NNReal} {r : NNReal}, HasS
um (fun a => ↑(f a)) ↑r ↔ HasSum f r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `ENNReal.coe_tsum`：∀ {α : Type u_1} {f : α → NNReal}, Summable f → ↑(tsum
 f) = ∑' (a : α), ↑(f a)
-/
theorem tsum_coe_ne_top_iff_summable {f : β → ℝ≥0} : (∑' b, (f b : ℝ≥0∞)) ≠ ∞ ↔ Summable f := by
  refine ⟨fun h => ?_, fun h => ENNReal.coe_tsum h ▸ ENNReal.coe_ne_top⟩
  lift ∑' b, (f b : ℝ≥0∞) to ℝ≥0 using h with a ha
  refine ⟨a, ENNReal.hasSum_coe.1 ?_⟩
  rw [ha]
  exact ENNReal.summable.hasSum
/-
**ENNReal.tsum_eq_iSup_sum** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} {f : α → ENNReal}, ∑' (a : α), f a = ⨆ s, ∑ a ∈ s, f a
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `ENNReal.hasSum`：∀ {α : Type u_1} {f : α → ENNReal}, HasSum f (⨆ s, ∑ a ∈
 s, f a)
-/
protected theorem tsum_eq_iSup_sum : ∑' a, f a = ⨆ s : Finset α, ∑ a ∈ s, f a :=
  ENNReal.hasSum.tsum_eq
/-
**ENNReal.tsum_eq_iSup_sum'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} {f : α → ENNReal} {ι : Type u_4} (s : ι → Finset α),   (∀
 (t : Finset α), ∃ i, t ⊆ s i) → ∑' (a : α), f a = ⨆ i, ∑ a ∈ s i, f a
参数：s : ι → Finset α；∀ (t : Finset α), ∃ i, t ⊆ s i；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.tsum_eq_iSup_sum`：∀ {α : Type u_1} {f : α → ENNReal}, ∑' (a : α)
, f a = ⨆ s, ∑ a ∈ s, f a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.iSup_comp_eq`：Monotone.iSup_comp_eq [Preorder β] {f : β -> α} (
hf : Monotone f) {s : ι -> β} (hs : forall x, exists i, x <= s i) : ⨆ x, f (s x)
 = ⨆ y, f y
· 使用定理 `Finset.sum_mono_set`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMono
id M] [inst_1 : Preorder M] [CanonicallyOrderedAdd M] (f : ι → M),   Monotone fu
n s => ∑ …
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
protected theorem tsum_eq_iSup_sum' {ι : Type*} (s : ι → Finset α) (hs : ∀ t, ∃ i, t ⊆ s i) :
    ∑' a, f a = ⨆ i, ∑ a ∈ s i, f a := by
  rw [ENNReal.tsum_eq_iSup_sum]
  symm
  change ⨆ i : ι, (fun t : Finset α => ∑ a ∈ t, f a) (s i) = ⨆ s : Finset α, ∑ a ∈ s, f a
  exact (Finset.sum_mono_set f).iSup_comp_eq hs
/-
**ENNReal.tsum_sigma** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} {β : α → Type u_4} (f : (a : α) → β a → ENNReal),   ∑' (p
 : (a : α) × β a), f p.fst p.snd = ∑' (a : α) (b : β a), f a b
参数：f : (a : α) → β a → ENNReal；p : (a : α) × β a；a : α；b : β a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tsum_sigma'`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMon
oid α] [inst_1 : TopologicalSpace α] [ContinuousAdd α] [T3Space α]   {γ : β → Ty
pe u_4} {f…
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `ENNReal.instT4Space`：T4Space ENNReal
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
-/
protected theorem tsum_sigma {β : α → Type*} (f : ∀ a, β a → ℝ≥0∞) :
    ∑' p : Σ a, β a, f p.1 p.2 = ∑' (a) (b), f a b :=
  ENNReal.summable.tsum_sigma' fun _ => ENNReal.summable
/-
**ENNReal.tsum_sigma'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} {β : α → Type u_4} (f : (a : α) × β a → ENNReal),   ∑' (p
 : (a : α) × β a), f p = ∑' (a : α) (b : β a), f ⟨a, b⟩
参数：f : (a : α) × β a → ENNReal；p : (a : α) × β a；a : α；b : β a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tsum_sigma'`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMon
oid α] [inst_1 : TopologicalSpace α] [ContinuousAdd α] [T3Space α]   {γ : β → Ty
pe u_4} {f…
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `ENNReal.instT4Space`：T4Space ENNReal
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
-/
protected theorem tsum_sigma' {β : α → Type*} (f : (Σ a, β a) → ℝ≥0∞) :
    ∑' p : Σ a, β a, f p = ∑' (a) (b), f ⟨a, b⟩ :=
  ENNReal.summable.tsum_sigma' fun _ => ENNReal.summable
/-
**ENNReal.tsum_biUnion'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} {S : Set ι} {f : α → ENNReal} {t : ι → Set
 α},   S.PairwiseDisjoint t → ∑' (x : ↑(⋃ i ∈ S, t i)), f ↑x = ∑' (i : ↑S) (x : 
↑(t ↑i)), f ↑x
参数：x : ↑(⋃ i ∈ S, t i)；i : ↑S；x : ↑(t ↑i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] (e : γ ≃ β)   (f : β → α), ∑' (c : 
γ),…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Set.coe_snd_biUnionEqSigmaOfDisjoint`：coe_snd_biUnionEqSigmaOfDisjoint {
α ι : Type*} {s : Set ι} {f : ι -> Set α} (h : s.PairwiseDisjoint f) (x : ⋃ i in
 s, f i) : ((Set.biUnionEq…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem tsum_biUnion' {ι : Type*} {S : Set ι} {f : α → ENNReal} {t : ι → Set α}
    (h : S.PairwiseDisjoint t) : ∑' x : ⋃ i ∈ S, t i, f x = ∑' (i : S), ∑' (x : t i), f x := by
  simp [← ENNReal.tsum_sigma, ← (Set.biUnionEqSigmaOfDisjoint h).tsum_eq]
/-
**ENNReal.tsum_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} {f : α → ENNReal} {t : ι → Set α},   Set.u
niv.PairwiseDisjoint t → ∑' (x : ↑(⋃ i, t i)), f ↑x = ∑' (i : ι) (x : ↑(t i)), f
 ↑x
参数：x : ↑(⋃ i, t i)；i : ι；x : ↑(t i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsum_univ`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] (f : β → α),   ∑' (x : ↑Set.univ), f ↑x = ∑' (x : β),…
· 使用定理 `ENNReal.tsum_biUnion'`：∀ {α : Type u_1} {ι : Type u_4} {S : Set ι} {f : 
α → ENNReal} {t : ι → Set α},   S.PairwiseDisjoint t → ∑' (x : ↑(⋃ i ∈ S, t i)),
 f ↑x = ∑' …
· 使用定理 `Set.biUnion_univ`：biUnion_univ (s : α -> Set β) : ⋃ x in @univ α, s x = 
⋃ x, s x
-/
protected theorem tsum_biUnion {ι : Type*} {f : α → ENNReal} {t : ι → Set α}
    (h : Set.univ.PairwiseDisjoint t) : ∑' x : ⋃ i, t i, f x = ∑' (i) (x : t i), f x := by
  nth_rw 2 [← tsum_univ]
  rw [← ENNReal.tsum_biUnion' h, Set.biUnion_univ]
/-
**ENNReal.tsum_prod** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β → ENNReal}, ∑' (p : α × β), f p
.1 p.2 = ∑' (a : α) (b : β), f a b
参数：p : α × β；a : α；b : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tsum_prod'`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [ins
t : AddCommMonoid α] [inst_1 : TopologicalSpace α] [ContinuousAdd α]   [T3Space 
α] {f : β…
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `ENNReal.instT4Space`：T4Space ENNReal
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
-/
protected theorem tsum_prod {f : α → β → ℝ≥0∞} : ∑' p : α × β, f p.1 p.2 = ∑' (a) (b), f a b :=
  ENNReal.summable.tsum_prod' fun _ => ENNReal.summable
/-
**ENNReal.tsum_prod'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α × β → ENNReal}, ∑' (p : α × β), f p
 = ∑' (a : α) (b : β), f (a, b)
参数：p : α × β；a : α；b : β；a, b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tsum_prod'`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [ins
t : AddCommMonoid α] [inst_1 : TopologicalSpace α] [ContinuousAdd α]   [T3Space 
α] {f : β…
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `ENNReal.instT4Space`：T4Space ENNReal
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
-/
protected theorem tsum_prod' {f : α × β → ℝ≥0∞} : ∑' p : α × β, f p = ∑' (a) (b), f (a, b) :=
  ENNReal.summable.tsum_prod' fun _ => ENNReal.summable
/-
**ENNReal.tsum_comm** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β → ENNReal}, ∑' (a : α) (b : β),
 f a b = ∑' (b : β) (a : α), f a b
参数：a : α；b : β；b : β；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tsum_comm'`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [ins
t : AddCommMonoid α] [inst_1 : TopologicalSpace α] [ContinuousAdd α]   [T3Space 
α] {f : β…
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `ENNReal.instT4Space`：T4Space ENNReal
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
-/
protected theorem tsum_comm {f : α → β → ℝ≥0∞} : ∑' a, ∑' b, f a b = ∑' b, ∑' a, f a b :=
  ENNReal.summable.tsum_comm' (fun _ => ENNReal.summable) fun _ => ENNReal.summable
/-
**ENNReal.tsum_add** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} {f g : α → ENNReal}, ∑' (a : α), (f a + g a) = ∑' (a : α)
, f a + ∑' (a : α), g a
参数：a : α；f a + g a；a : α；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tsum_add`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid
 α] [inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β} [T2Spa
ce α] […
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
-/
protected theorem tsum_add : ∑' a, (f a + g a) = ∑' a, f a + ∑' a, g a :=
  ENNReal.summable.tsum_add ENNReal.summable
/-
**ENNReal.sum_add_tsum_compl** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {ι : Type u_4} (s : Finset ι) (f : ι → ENNReal), ∑ i ∈ s, f i + ∑' (i : 
↑(↑s)ᶜ), f ↑i = ∑' (i : ι), f i
参数：s : Finset ι；f : ι → ENNReal；i : ↑(↑s)ᶜ；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsum_subtype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] (s : Set β) (f : β → α),   ∑' (x : ↑s), f ↑x = ∑' (
x …
· 使用定理 `sum_eq_tsum_indicator`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMo
noid α] [inst_1 : TopologicalSpace α] (f : β → α) (s : Finset β)   (L : optParam
 (Summation…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.indicator_self_add_compl_apply`：∀ {α : Type u_1} {M : Type u_4} [ins
t : AddZeroClass M] (s : Set α) (f : α → M) (a : α),   s.indicator f a + sᶜ.indi
cator f a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma sum_add_tsum_compl {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    ∑ i ∈ s, f i + ∑' i : ↥(s : Set ι)ᶜ, f i = ∑' i, f i := by
  rw [tsum_subtype, sum_eq_tsum_indicator]
  simp [← ENNReal.tsum_add]
/-
**ENNReal.tsum_le_tsum** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} {f g : α → ENNReal}, (∀ (a : α), f a ≤ g a) → ∑' (a : α),
 f a ≤ ∑' (a : α), g a
参数：∀ (a : α), f a ≤ g a；a : α；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tsum_le_tsum`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFil
ter ι} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [
inst_3 : To…
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
-/
protected theorem tsum_le_tsum (h : ∀ a, f a ≤ g a) : ∑' a, f a ≤ ∑' a, g a :=
  ENNReal.summable.tsum_le_tsum h ENNReal.summable
/-
**ENNReal.sum_le_tsum** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} {f : α → ENNReal} (s : Finset α), ∑ x ∈ s, f x ≤ ∑' (x : 
α), f x
参数：s : Finset α；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.sum_le_tsum`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilt
er ι} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [i
nst_3 : To…
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
-/
protected theorem sum_le_tsum {f : α → ℝ≥0∞} (s : Finset α) : ∑ x ∈ s, f x ≤ ∑' x, f x :=
  ENNReal.summable.sum_le_tsum s (fun _ _ => zero_le)
/-
**ENNReal.le_tsum_of_forall_lt_exists_sum** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} {a : ENNReal} {f : α → ENNReal}, (∀ b < a, ∃ I, b < ∑ i ∈
 I, f i) → a ≤ ∑' (i : α), f i
参数：∀ b < a, ∃ I, b < ∑ i ∈ I, f i；i : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_forall_lt`：le_of_forall_lt (H : forall c, c < a -> c < b) : a <= b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `ENNReal.sum_le_tsum`：∀ {α : Type u_1} {f : α → ENNReal} (s : Finset α), 
∑ x ∈ s, f x ≤ ∑' (x : α), f x
-/
protected lemma le_tsum_of_forall_lt_exists_sum
    (h : ∀ b < a, ∃ I : Finset α, b < ∑ i ∈ I, f i) : a ≤ ∑' i, f i := by
  refine le_of_forall_lt fun b hb ↦ ?_
  obtain ⟨I, hI⟩ := h b hb
  exact lt_of_lt_of_le hI (ENNReal.sum_le_tsum I)
/-
**ENNReal.tsum_eq_iSup_nat'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {f : ℕ → ENNReal} {N : ℕ → ℕ},   Filter.Tendsto N Filter.atTop Filter.at
Top → ∑' (i : ℕ), f i = ⨆ i, ∑ a ∈ Finset.range (N i), f a
参数：i : ℕ；N i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.tsum_eq_iSup_sum'`：∀ {α : Type u_1} {f : α → ENNReal} {ι : Type 
u_4} (s : ι → Finset α),   (∀ (t : Finset α), ∃ i, t ⊆ s i) → ∑' (a : α), f a = 
⨆ i, ∑ a ∈ s i,…
· 使用定理 `Finset.exists_nat_subset_range`：exists_nat_subset_range (s : Finset Nat)
 : exists n : Nat, s subseteq range n
· 使用引理 `Filter.exists_le_of_tendsto_atTop`：exists_le_of_tendsto_atTop (h : Tends
to u atTop atTop) (a : α) (b : β) : exists a', a <= a' ∧ b <= u a'
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `Finset.Subset.trans`：∀ {α : Type u_1} {s₁ s₂ s₃ : Finset α}, s₁ ⊆ s₂ → s
₂ ⊆ s₃ → s₁ ⊆ s₃
· 使用定理 `Finset.range_mono`：range_mono : Monotone range
-/
protected theorem tsum_eq_iSup_nat' {f : ℕ → ℝ≥0∞} {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
    ∑' i : ℕ, f i = ⨆ i : ℕ, ∑ a ∈ Finset.range (N i), f a :=
  ENNReal.tsum_eq_iSup_sum' _ fun t =>
    let ⟨n, hn⟩ := t.exists_nat_subset_range
    let ⟨k, _, hk⟩ := exists_le_of_tendsto_atTop hN 0 n
    ⟨k, Finset.Subset.trans hn (Finset.range_mono hk)⟩
/-
**ENNReal.tsum_eq_iSup_nat** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {f : ℕ → ENNReal}, ∑' (i : ℕ), f i = ⨆ i, ∑ a ∈ Finset.range i, f a
参数：i : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.tsum_eq_iSup_sum'`：∀ {α : Type u_1} {f : α → ENNReal} {ι : Type 
u_4} (s : ι → Finset α),   (∀ (t : Finset α), ∃ i, t ⊆ s i) → ∑' (a : α), f a = 
⨆ i, ∑ a ∈ s i,…
· 使用定理 `Finset.exists_nat_subset_range`：exists_nat_subset_range (s : Finset Nat)
 : exists n : Nat, s subseteq range n
-/
protected theorem tsum_eq_iSup_nat {f : ℕ → ℝ≥0∞} :
    ∑' i : ℕ, f i = ⨆ i : ℕ, ∑ a ∈ Finset.range i, f a :=
  ENNReal.tsum_eq_iSup_sum' _ Finset.exists_nat_subset_range
/-
**ENNReal.tsum_eq_liminf_sum_nat** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {f : ℕ → ENNReal}, ∑' (i : ℕ), f i = Filter.liminf (fun n => ∑ i ∈ Finse
t.range n, f i) Filter.atTop
参数：i : ℕ；fun n => ∑ i ∈ Finset.range n, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.Tendsto.liminf_eq`：Filter.Tendsto.liminf_eq {f : Filter β} {u : β
 -> α} {a : α} [NeBot f] (h : Tendsto u f (𝓝 a)) : liminf u f = a
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `HasSum.tendsto_sum_nat`：∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_
1 : TopologicalSpace M] {m : M} {f : ℕ → M},   HasSum f m → Filter.Tendsto (fun 
n => ∑ i ∈ F…
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
-/
protected theorem tsum_eq_liminf_sum_nat {f : ℕ → ℝ≥0∞} :
    ∑' i, f i = liminf (fun n => ∑ i ∈ Finset.range n, f i) atTop :=
  ENNReal.summable.hasSum.tendsto_sum_nat.liminf_eq.symm
/-
**ENNReal.tsum_eq_limsup_sum_nat** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {f : ℕ → ENNReal}, ∑' (i : ℕ), f i = Filter.limsup (fun n => ∑ i ∈ Finse
t.range n, f i) Filter.atTop
参数：i : ℕ；fun n => ∑ i ∈ Finset.range n, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.Tendsto.limsup_eq`：Filter.Tendsto.limsup_eq {f : Filter β} {u : β
 -> α} {a : α} [NeBot f] (h : Tendsto u f (𝓝 a)) : limsup u f = a
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `HasSum.tendsto_sum_nat`：∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_
1 : TopologicalSpace M] {m : M} {f : ℕ → M},   HasSum f m → Filter.Tendsto (fun 
n => ∑ i ∈ F…
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
-/
protected theorem tsum_eq_limsup_sum_nat {f : ℕ → ℝ≥0∞} :
    ∑' i, f i = limsup (fun n => ∑ i ∈ Finset.range n, f i) atTop :=
  ENNReal.summable.hasSum.tendsto_sum_nat.limsup_eq.symm
/-
**ENNReal.le_tsum** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} {f : α → ENNReal} (a : α), f a ≤ ∑' (a : α), f a
参数：a : α；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.le_tsum'`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddCommMonoid
 α] [inst_1 : PartialOrder α] [IsOrderedAddMonoid α]   [CanonicallyOrderedAdd α]
 [inst_…
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
-/
protected theorem le_tsum (a : α) : f a ≤ ∑' a, f a :=
  ENNReal.summable.le_tsum' a

@[simp]
/-
**ENNReal.tsum_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} {f : α → ENNReal}, ∑' (i : α), f i = 0 ↔ ∀ (i : α), f i =
 0
参数：i : α；i : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tsum_eq_zero_iff`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddCo
mmMonoid α] [inst_1 : PartialOrder α] [IsOrderedAddMonoid α]   [CanonicallyOrder
edAdd α] [inst_…
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
-/
protected theorem tsum_eq_zero : ∑' i, f i = 0 ↔ ∀ i, f i = 0 :=
  ENNReal.summable.tsum_eq_zero_iff
/-
**ENNReal.tsum_eq_top_of_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} {f : α → ENNReal}, (∃ a, f a = ⊤) → ∑' (a : α), f a = ⊤
参数：∃ a, f a = ⊤；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `ENNReal.le_tsum`：∀ {α : Type u_1} {f : α → ENNReal} (a : α), f a ≤ ∑' (a
 : α), f a
-/
protected theorem tsum_eq_top_of_eq_top : (∃ a, f a = ∞) → ∑' a, f a = ∞
  | ⟨a, ha⟩ => top_unique <| ha ▸ ENNReal.le_tsum a
/-
**ENNReal.lt_top_of_tsum_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} {a : α → ENNReal}, ∑' (i : α), a i ≠ ⊤ → ∀ (j : α), a j <
 ⊤
参数：i : α；j : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ENNReal.tsum_eq_top_of_eq_top`：∀ {α : Type u_1} {f : α → ENNReal}, (∃ a,
 f a = ⊤) → ∑' (a : α), f a = ⊤
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
-/
protected theorem lt_top_of_tsum_ne_top {a : α → ℝ≥0∞} (tsum_ne_top : ∑' i, a i ≠ ∞) (j : α) :
    a j < ∞ := by
  contrapose! tsum_ne_top with h
  exact ENNReal.tsum_eq_top_of_eq_top ⟨j, top_unique h⟩

@[simp]
/-
**ENNReal.tsum_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} [Nonempty α], ∑' (x : α), ⊤ = ⊤
参数：x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.tsum_eq_top_of_eq_top`：∀ {α : Type u_1} {f : α → ENNReal}, (∃ a,
 f a = ⊤) → ∑' (a : α), f a = ⊤
-/
protected theorem tsum_top [Nonempty α] : ∑' _ : α, ∞ = ∞ :=
  let ⟨a⟩ := ‹Nonempty α›
  ENNReal.tsum_eq_top_of_eq_top ⟨a, rfl⟩
/-
**ENNReal.tsum_const_eq_top_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tsum_const_eq_top_of_ne_zero {α : Type*} [Infinite α] {c : Real>=0∞} (hc :
 c != 0) : ∑' _ : α, c = ∞
参数：hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.Tendsto.mul_const`：∀ {α : Type u_1} {f : Filter α} {m : α → ENNR
eal} {a b : ENNReal},   Filter.Tendsto m f (nhds a) → a ≠ 0 ∨ b ≠ ⊤ → Filter.Ten
dsto (fun x => …
· 使用定理 `ENNReal.tendsto_nat_nhds_top`：tendsto_nat_nhds_top : Tendsto (fun n : Na
t => ↑n) atTop (𝓝 ∞)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Infinite.exists_subset_card_eq`：exists_subset_card_eq (α : Type*) [Infin
ite α] (n : Nat) : exists s : Finset α, #s = n
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `ENNReal.sum_le_tsum`：∀ {α : Type u_1} {f : α → ENNReal} (s : Finset α), 
∑ x ∈ s, f x ≤ ∑' (x : α), f x
· 使用定理 `ENNReal.top_mul`：∀ {a : ENNReal}, a ≠ 0 → ⊤ * a = ⊤
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `le_of_tendsto'`：le_of_tendsto' {x : Filter β} [hx : NeBot x] (lim : Tend
sto f x (𝓝 a)) (h : forall c, f c <= b) : a <= b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem tsum_const_eq_top_of_ne_zero {α : Type*} [Infinite α] {c : ℝ≥0∞} (hc : c ≠ 0) :
    ∑' _ : α, c = ∞ := by
  have A : Tendsto (fun n : ℕ => (n : ℝ≥0∞) * c) atTop (𝓝 (∞ * c)) := by
    apply ENNReal.Tendsto.mul_const tendsto_nat_nhds_top
    simp only [true_or, top_ne_zero, Ne, not_false_iff]
  have B : ∀ n : ℕ, (n : ℝ≥0∞) * c ≤ ∑' _ : α, c := fun n => by
    rcases Infinite.exists_subset_card_eq α n with ⟨s, hs⟩
    simpa [hs] using @ENNReal.sum_le_tsum α (fun _ => c) s
  simpa [hc] using le_of_tendsto' A B
/-
**ENNReal.ne_top_of_tsum_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} {f : α → ENNReal}, ∑' (a : α), f a ≠ ⊤ → ∀ (a : α), f a ≠
 ⊤
参数：a : α；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.tsum_eq_top_of_eq_top`：∀ {α : Type u_1} {f : α → ENNReal}, (∃ a,
 f a = ⊤) → ∑' (a : α), f a = ⊤
-/
protected theorem ne_top_of_tsum_ne_top (h : ∑' a, f a ≠ ∞) (a : α) : f a ≠ ∞ := fun ha =>
  h <| ENNReal.tsum_eq_top_of_eq_top ⟨a, ha⟩
/-
**ENNReal.tsum_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} {a : ENNReal} {f : α → ENNReal}, ∑' (i : α), a * f i = a 
* ∑' (i : α), f i
参数：i : α；i : α。
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
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ENNReal.Tendsto.const_mul`：∀ {α : Type u_1} {f : Filter α} {m : α → ENNR
eal} {a b : ENNReal},   Filter.Tendsto m f (nhds b) → b ≠ 0 ∨ a ≠ ⊤ → Filter.Ten
dsto (fun b => …
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.tsum_eq_zero`：∀ {α : Type u_1} {f : α → ENNReal}, ∑' (i : α), f 
i = 0 ↔ ∀ (i : α), f i = 0
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
-/
protected theorem tsum_mul_left : ∑' i, a * f i = a * ∑' i, f i := by
  by_cases hf : ∀ i, f i = 0
  · simp [hf]
  · rw [← ENNReal.tsum_eq_zero] at hf
    have : Tendsto (fun s : Finset α => ∑ j ∈ s, a * f j) atTop (𝓝 (a * ∑' i, f i)) := by
      simp only [← Finset.mul_sum]
      exact ENNReal.Tendsto.const_mul ENNReal.summable.hasSum (Or.inl hf)
    exact HasSum.tsum_eq this
/-
**ENNReal.tsum_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} {a : ENNReal} {f : α → ENNReal}, ∑' (i : α), f i * a = (∑
' (i : α), f i) * a
参数：i : α；∑' (i : α), f i。
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
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ENNReal.tsum_mul_left`：∀ {α : Type u_1} {a : ENNReal} {f : α → ENNReal},
 ∑' (i : α), a * f i = a * ∑' (i : α), f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem tsum_mul_right : ∑' i, f i * a = (∑' i, f i) * a := by
  simp [mul_comm, ENNReal.tsum_mul_left]
/-
**ENNReal.tsum_const_smul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} {f : α → ENNReal} {R : Type u_4} [inst : SMul R ENNReal] 
[IsScalarTower R ENNReal ENNReal] (a : R),   ∑' (i : α), a • f i = a • ∑' (i : α
), f i
参数：a : R；i : α；i : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `smul_one_mul`：smul_one_mul {M N} [MulOneClass N] [SMul M N] [IsScalarTow
er M N N] (x : M) (y : N) : x • (1 : N) * y = x • y
· 使用定理 `ENNReal.tsum_mul_left`：∀ {α : Type u_1} {a : ENNReal} {f : α → ENNReal},
 ∑' (i : α), a * f i = a * ∑' (i : α), f i
-/
protected theorem tsum_const_smul {R} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (a : R) :
    ∑' i, a • f i = a • ∑' i, f i := by
  simpa only [smul_one_mul] using @ENNReal.tsum_mul_left _ (a • (1 : ℝ≥0∞)) _

@[simp]
/-
**ENNReal.tsum_iSup_eq** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tsum_iSup_eq {α : Type*} (a : α) {f : α -> Real>=0∞} : (∑' b : α, ⨆ _ : a 
= b, f b) = f a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `tsum_eq_single`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] {f : β → α}
 (b …
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
-/
theorem tsum_iSup_eq {α : Type*} (a : α) {f : α → ℝ≥0∞} : (∑' b : α, ⨆ _ : a = b, f b) = f a :=
  (tsum_eq_single a fun _ h => by simp [h.symm]).trans <| by simp
/-
**ENNReal.hasSum_iff_tendsto_nat** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：hasSum_iff_tendsto_nat {f : Nat -> Real>=0∞} (r : Real>=0∞) : HasSum f r ↔
 Tendsto (fun n : Nat => ∑ i in Finset.range n, f i) atTop (𝓝 r)
参数：r : Real>=0∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.tendsto_sum_nat`：∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_
1 : TopologicalSpace M] {m : M} {f : ℕ → M},   HasSum f m → Filter.Tendsto (fun 
n => ∑ i ∈ F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_eq_of_tendsto`：iSup_eq_of_tendsto {α β} [TopologicalSpace α] [Compl
eteLinearOrder α] [OrderTopology α] [Nonempty β] [SemilatticeSup β] {f : β -> α}
 {a : α}…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Finset.sum_le_sum_of_subset`：∀ {ι : Type u_1} {M : Type u_4} [inst : Add
CommMonoid M] [inst_1 : Preorder M] [CanonicallyOrderedAdd M] {f : ι → M}   {s t
 : Finset ι}, s ⊆…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.range_subset_range`：range_subset_range {n m} : range n subseteq r
ange m ↔ n <= m
· 使用定理 `ENNReal.tsum_eq_iSup_nat`：∀ {f : ℕ → ENNReal}, ∑' (i : ℕ), f i = ⨆ i, ∑ 
a ∈ Finset.range i, f a
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
-/
theorem hasSum_iff_tendsto_nat {f : ℕ → ℝ≥0∞} (r : ℝ≥0∞) :
    HasSum f r ↔ Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop (𝓝 r) := by
  refine ⟨HasSum.tendsto_sum_nat, fun h => ?_⟩
  rw [← iSup_eq_of_tendsto _ h, ← ENNReal.tsum_eq_iSup_nat]
  · exact ENNReal.summable.hasSum
  · exact fun s t hst => Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hst)
/-
**ENNReal.tendsto_nat_tsum** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tendsto_nat_tsum (f : Nat -> Real>=0∞) : Tendsto (fun n : Nat => ∑ i in Fi
nset.range n, f i) atTop (𝓝 (∑' n, f n))
参数：f : Nat -> Real>=0∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.hasSum_iff_tendsto_nat`：hasSum_iff_tendsto_nat {f : Nat -> Real>
=0∞} (r : Real>=0∞) : HasSum f r ↔ Tendsto (fun n : Nat => ∑ i in Finset.range n
, f i) atTop (𝓝 r)
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
-/
theorem tendsto_nat_tsum (f : ℕ → ℝ≥0∞) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop (𝓝 (∑' n, f n)) := by
  rw [← hasSum_iff_tendsto_nat]
  exact ENNReal.summable.hasSum
/-
**ENNReal.toNNReal_apply_of_tsum_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toNNReal_apply_of_tsum_ne_top {α : Type*} {f : α -> Real>=0∞} (hf : ∑' i, 
f i != ∞) (x : α) : (((ENNReal.toNNReal ∘ f) x : Real>=0) : Real>=0∞) = f x
参数：hf : ∑' i, f i != ∞；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `ENNReal.ne_top_of_tsum_ne_top`：∀ {α : Type u_1} {f : α → ENNReal}, ∑' (a
 : α), f a ≠ ⊤ → ∀ (a : α), f a ≠ ⊤
-/
theorem toNNReal_apply_of_tsum_ne_top {α : Type*} {f : α → ℝ≥0∞} (hf : ∑' i, f i ≠ ∞) (x : α) :
    (((ENNReal.toNNReal ∘ f) x : ℝ≥0) : ℝ≥0∞) = f x :=
  coe_toNNReal <| ENNReal.ne_top_of_tsum_ne_top hf _
/-
**ENNReal.summable_toNNReal_of_tsum_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：summable_toNNReal_of_tsum_ne_top {α : Type*} {f : α -> Real>=0∞} (hf : ∑' 
i, f i != ∞) : Summable (ENNReal.toNNReal ∘ f)
参数：hf : ∑' i, f i != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.toNNReal_apply_of_tsum_ne_top`：toNNReal_apply_of_tsum_ne_top {α 
: Type*} {f : α -> Real>=0∞} (hf : ∑' i, f i != ∞) (x : α) : (((ENNReal.toNNReal
 ∘ f) x : Real>=0) : Real>=…
-/
theorem summable_toNNReal_of_tsum_ne_top {α : Type*} {f : α → ℝ≥0∞} (hf : ∑' i, f i ≠ ∞) :
    Summable (ENNReal.toNNReal ∘ f) := by
  simpa only [← tsum_coe_ne_top_iff_summable, toNNReal_apply_of_tsum_ne_top hf] using hf
/-
**ENNReal.tendsto_cofinite_zero_of_tsum_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNRea
l`。
形式化陈述：tendsto_cofinite_zero_of_tsum_ne_top {α} {f : α -> Real>=0∞} (hf : ∑' x, f
 x != ∞) : Tendsto f cofinite (𝓝 0)
参数：hf : ∑' x, f x != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.ne_top_of_tsum_ne_top`：∀ {α : Type u_1} {f : α → ENNReal}, ∑' (a
 : α), f a ≠ ⊤ → ∀ (a : α), f a ≠ ⊤
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.coe_zero`：↑0 = 0
· 使用定理 `ENNReal.tendsto_coe`：tendsto_coe {f : Filter α} {m : α -> Real>=0} {a : 
Real>=0} : Tendsto (fun a => (m a : Real>=0∞)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a)
· 使用定理 `NNReal.tendsto_cofinite_zero_of_summable`：tendsto_cofinite_zero_of_summa
ble {α} {f : α -> Real>=0} (hf : Summable f) : Tendsto f cofinite (𝓝 0)
· 使用定理 `ENNReal.summable_toNNReal_of_tsum_ne_top`：summable_toNNReal_of_tsum_ne_t
op {α : Type*} {f : α -> Real>=0∞} (hf : ∑' i, f i != ∞) : Summable (ENNReal.toN
NReal ∘ f)
-/
theorem tendsto_cofinite_zero_of_tsum_ne_top {α} {f : α → ℝ≥0∞} (hf : ∑' x, f x ≠ ∞) :
    Tendsto f cofinite (𝓝 0) := by
  have f_ne_top : ∀ n, f n ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top hf
  have h_f_coe : f = fun n => ((f n).toNNReal : ENNReal) :=
    funext fun n => (coe_toNNReal (f_ne_top n)).symm
  rw [h_f_coe, ← @coe_zero, tendsto_coe]
  exact NNReal.tendsto_cofinite_zero_of_summable (summable_toNNReal_of_tsum_ne_top hf)
/-
**ENNReal.tendsto_atTop_zero_of_tsum_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tendsto_atTop_zero_of_tsum_ne_top {f : Nat -> Real>=0∞} (hf : ∑' x, f x !=
 ∞) : Tendsto f atTop (𝓝 0)
参数：hf : ∑' x, f x != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cofinite_eq_atTop`：Nat.cofinite_eq_atTop : @cofinite Nat = atTop
· 使用定理 `ENNReal.tendsto_cofinite_zero_of_tsum_ne_top`：tendsto_cofinite_zero_of_t
sum_ne_top {α} {f : α -> Real>=0∞} (hf : ∑' x, f x != ∞) : Tendsto f cofinite (𝓝
 0)
-/
theorem tendsto_atTop_zero_of_tsum_ne_top {f : ℕ → ℝ≥0∞} (hf : ∑' x, f x ≠ ∞) :
    Tendsto f atTop (𝓝 0) := by
  rw [← Nat.cofinite_eq_atTop]
  exact tendsto_cofinite_zero_of_tsum_ne_top hf

/-- The sum over the complement of a finset tends to `0` when the finset grows to cover the whole
space. This does not need a summability assumption, as otherwise all sums are zero. -/
/-
**ENNReal.tendsto_tsum_compl_atTop_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tendsto_tsum_compl_atTop_zero {α : Type*} {f : α -> Real>=0∞} (hf : ∑' x, 
f x != ∞) : Tendsto (fun s : Finset α => ∑' b : { x // x ∉ s }, f b) atTop (𝓝 0)
参数：hf : ∑' x, f x != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `ENNReal.ne_top_of_tsum_ne_top`：∀ {α : Type u_1} {f : α → ENNReal}, ∑' (a
 : α), f a ≠ ⊤ → ∀ (a : α), f a ≠ ⊤
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.coe_tsum`：∀ {α : Type u_1} {f : α → NNReal}, Summable f → ↑(tsum
 f) = ∑' (a : α), ↑(f a)
· 使用定理 `NNReal.summable_comp_injective`：summable_comp_injective {β : Type*} {f :
 α -> Real>=0} (hf : Summable f) {i : β -> α} (hi : Function.Injective i) : Summ
able (f ∘ i)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.tsum_coe_ne_top_iff_summable`：tsum_coe_ne_top_iff_summable {f : 
β -> Real>=0} : (∑' b, (f b : Real>=0∞)) != ∞ ↔ Summable f
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.tendsto_coe`：tendsto_coe {f : Filter α} {m : α -> Real>=0} {a : 
Real>=0} : Tendsto (fun a => (m a : Real>=0∞)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a)
· 使用定理 `NNReal.tendsto_tsum_compl_atTop_zero`：∀ {α : Type u_3} (f : α → NNReal),
 Filter.Tendsto (fun s => ∑' (b : { x // x ∉ s }), f ↑b) Filter.atTop (nhds 0)

--- 原说明 ---
The sum over the complement of a finset tends to `0` when the finset grows to co
ver the whole
space. This does not need a summability assumption, as otherwise all sums are ze
ro.
-/
theorem tendsto_tsum_compl_atTop_zero {α : Type*} {f : α → ℝ≥0∞} (hf : ∑' x, f x ≠ ∞) :
    Tendsto (fun s : Finset α => ∑' b : { x // x ∉ s }, f b) atTop (𝓝 0) := by
  lift f to α → ℝ≥0 using ENNReal.ne_top_of_tsum_ne_top hf
  convert! ENNReal.tendsto_coe.2 (NNReal.tendsto_tsum_compl_atTop_zero f)
  rw [ENNReal.coe_tsum]
  exact NNReal.summable_comp_injective (tsum_coe_ne_top_iff_summable.1 hf) Subtype.coe_injective
/-
**ENNReal.tsum_apply** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {ι : Type u_4} {α : Type u_5} {f : ι → α → ENNReal} {x : α}, (∑' (i : ι)
, f i) x = ∑' (i : ι), f i x
参数：∑' (i : ι), f i；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsum_apply`：∀ {α : Type u_1} {ι : Type u_4} {X : α → Type u_5} [inst : (
x : α) → AddCommMonoid (X x)]   [inst_1 : (x : α) → TopologicalSpace (X x)] {L :
…
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Pi.summable`：∀ {α : Type u_1} {ι : Type u_4} {X : α → Type u_5} [inst : 
(x : α) → AddCommMonoid (X x)]   [inst_1 : (x : α) → TopologicalSpace (X x)] {L 
:…
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
-/
protected theorem tsum_apply {ι α : Type*} {f : ι → α → ℝ≥0∞} {x : α} :
    (∑' i, f i) x = ∑' i, f i x :=
  tsum_apply <| Pi.summable.mpr fun _ => ENNReal.summable
/-
**ENNReal.tsum_sub** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tsum_sub {f : Nat -> Real>=0∞} {g : Nat -> Real>=0∞} (h₁ : ∑' i, g i != ∞)
 (h₂ : g <= f) : ∑' i, (f i - g i) = ∑' i, f i - ∑' i, g i
参数：h₁ : ∑' i, g i != ∞；h₂ : g <= f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `ENNReal.eq_sub_of_add_eq`：∀ {a b c : ENNReal}, c ≠ ⊤ → a + c = b → a = b
 - c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tsum_sub {f : ℕ → ℝ≥0∞} {g : ℕ → ℝ≥0∞} (h₁ : ∑' i, g i ≠ ∞) (h₂ : g ≤ f) :
    ∑' i, (f i - g i) = ∑' i, f i - ∑' i, g i :=
  have : ∀ i, f i - g i + g i = f i := fun i => tsub_add_cancel_of_le (h₂ i)
  ENNReal.eq_sub_of_add_eq h₁ <| by simp only [← ENNReal.tsum_add, this]
/-
**ENNReal.tsum_comp_le_tsum_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tsum_comp_le_tsum_of_injective {f : α -> β} (hf : Injective f) (g : β -> R
eal>=0∞) : ∑' x, g (f x) <= ∑' y, g y
参数：hf : Injective f；g : β -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tsum_le_tsum_of_inj`：∀ {ι : Type u_1} {κ : Type u_2} {α : Type 
u_3} [inst : AddCommMonoid α] [inst_1 : Preorder α] [IsOrderedAddMonoid α]   [in
st_3 : Topological…
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
-/
theorem tsum_comp_le_tsum_of_injective {f : α → β} (hf : Injective f) (g : β → ℝ≥0∞) :
    ∑' x, g (f x) ≤ ∑' y, g y :=
  ENNReal.summable.tsum_le_tsum_of_inj f hf (fun _ _ => zero_le) (fun _ => le_rfl)
    ENNReal.summable
/-
**ENNReal.tsum_le_tsum_comp_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tsum_le_tsum_comp_of_surjective {f : α -> β} (hf : Surjective f) (g : β ->
 Real>=0∞) : ∑' y, g y <= ∑' x, g (f x)
参数：hf : Surjective f；g : β -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.surjInv_eq`：surjInv_eq (h : Surjective f) (b) : f (surjInv h b)
 = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ENNReal.tsum_comp_le_tsum_of_injective`：tsum_comp_le_tsum_of_injective {
f : α -> β} (hf : Injective f) (g : β -> Real>=0∞) : ∑' x, g (f x) <= ∑' y, g y
· 使用定理 `Function.injective_surjInv`：injective_surjInv (h : Surjective f) : Injec
tive (surjInv h)
-/
theorem tsum_le_tsum_comp_of_surjective {f : α → β} (hf : Surjective f) (g : β → ℝ≥0∞) :
    ∑' y, g y ≤ ∑' x, g (f x) :=
  calc ∑' y, g y = ∑' y, g (f (surjInv hf y)) := by simp only [surjInv_eq hf]
  _ ≤ ∑' x, g (f x) := tsum_comp_le_tsum_of_injective (injective_surjInv hf) _
/-
**ENNReal.tsum_mono_subtype** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tsum_mono_subtype (f : α -> Real>=0∞) {s t : Set α} (h : s subseteq t) : ∑
' x : s, f x <= ∑' x : t, f x
参数：f : α -> Real>=0∞；h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.tsum_comp_le_tsum_of_injective`：tsum_comp_le_tsum_of_injective {
f : α -> β} (hf : Injective f) (g : β -> Real>=0∞) : ∑' x, g (f x) <= ∑' y, g y
· 使用定理 `Set.inclusion_injective`：inclusion_injective (h : s subseteq t) : (inclu
sion h).Injective
-/
theorem tsum_mono_subtype (f : α → ℝ≥0∞) {s t : Set α} (h : s ⊆ t) :
    ∑' x : s, f x ≤ ∑' x : t, f x :=
  tsum_comp_le_tsum_of_injective (inclusion_injective h) _
/-
**ENNReal.tsum_iUnion_le_tsum** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tsum_iUnion_le_tsum {ι : Type*} (f : α -> Real>=0∞) (t : ι -> Set α) : ∑' 
x : ⋃ i, t i, f x <= ∑' i, ∑' x : t i, f x
参数：f : α -> Real>=0∞；t : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.tsum_le_tsum_comp_of_surjective`：tsum_le_tsum_comp_of_surjective
 {f : α -> β} (hf : Surjective f) (g : β -> Real>=0∞) : ∑' y, g y <= ∑' x, g (f 
x)
· 使用定理 `Set.sigmaToiUnion_surjective`：sigmaToiUnion_surjective : Surjective (sig
maToiUnion t) | ⟨b, hb⟩ => have : exists a, b in t a
· 使用定理 `ENNReal.tsum_sigma'`：∀ {α : Type u_1} {β : α → Type u_4} (f : (a : α) × 
β a → ENNReal),   ∑' (p : (a : α) × β a), f p = ∑' (a : α) (b : β a), f ⟨a, b⟩
-/
theorem tsum_iUnion_le_tsum {ι : Type*} (f : α → ℝ≥0∞) (t : ι → Set α) :
    ∑' x : ⋃ i, t i, f x ≤ ∑' i, ∑' x : t i, f x :=
  calc ∑' x : ⋃ i, t i, f x ≤ ∑' x : Σ i, t i, f x.2 :=
    tsum_le_tsum_comp_of_surjective (sigmaToiUnion_surjective t) _
  _ = ∑' i, ∑' x : t i, f x := ENNReal.tsum_sigma' _
/-
**ENNReal.tsum_biUnion_le_tsum** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tsum_biUnion_le_tsum {ι : Type*} (f : α -> Real>=0∞) (s : Set ι) (t : ι ->
 Set α) : ∑' x : ⋃ i in s, t i, f x <= ∑' i : s, ∑' x : t i, f x
参数：f : α -> Real>=0∞；s : Set ι；t : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsum_congr_set_coe`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoi
d α] [inst_1 : TopologicalSpace α] (f : β → α) {s t : Set β},   s = t → ∑' (x : 
↑s), f ↑…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ENNReal.tsum_iUnion_le_tsum`：tsum_iUnion_le_tsum {ι : Type*} (f : α -> R
eal>=0∞) (t : ι -> Set α) : ∑' x : ⋃ i, t i, f x <= ∑' i, ∑' x : t i, f x
-/
theorem tsum_biUnion_le_tsum {ι : Type*} (f : α → ℝ≥0∞) (s : Set ι) (t : ι → Set α) :
    ∑' x : ⋃ i ∈ s, t i, f x ≤ ∑' i : s, ∑' x : t i, f x :=
  calc ∑' x : ⋃ i ∈ s, t i, f x = ∑' x : ⋃ i : s, t i, f x := tsum_congr_set_coe _ <| by simp
  _ ≤ ∑' i : s, ∑' x : t i, f x := tsum_iUnion_le_tsum _ _
/-
**ENNReal.tsum_biUnion_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tsum_biUnion_le {ι : Type*} (f : α -> Real>=0∞) (s : Finset ι) (t : ι -> S
et α) : ∑' x : ⋃ i in s, t i, f x <= ∑ i in s, ∑' x : t i, f x
参数：f : α -> Real>=0∞；s : Finset ι；t : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `ENNReal.tsum_biUnion_le_tsum`：tsum_biUnion_le_tsum {ι : Type*} (f : α ->
 Real>=0∞) (s : Set ι) (t : ι -> Set α) : ∑' x : ⋃ i in s, t i, f x <= ∑' i : s,
 ∑' x : t i, f x
· 使用定理 `Finset.tsum_subtype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMono
id α] [inst_1 : TopologicalSpace α] (s : Finset β) (f : β → α),   ∑' (x : ↥s), f
 ↑x = ∑ x…
-/
theorem tsum_biUnion_le {ι : Type*} (f : α → ℝ≥0∞) (s : Finset ι) (t : ι → Set α) :
    ∑' x : ⋃ i ∈ s, t i, f x ≤ ∑ i ∈ s, ∑' x : t i, f x :=
  (tsum_biUnion_le_tsum f s t).trans_eq (Finset.tsum_subtype s fun i => ∑' x : t i, f x)
/-
**ENNReal.tsum_iUnion_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tsum_iUnion_le {ι : Type*} [Fintype ι] (f : α -> Real>=0∞) (t : ι -> Set α
) : ∑' x : ⋃ i, t i, f x <= ∑ i, ∑' x : t i, f x
参数：f : α -> Real>=0∞；t : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] [inst_3 : Fin
ty…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `ENNReal.tsum_iUnion_le_tsum`：tsum_iUnion_le_tsum {ι : Type*} (f : α -> R
eal>=0∞) (t : ι -> Set α) : ∑' x : ⋃ i, t i, f x <= ∑' i, ∑' x : t i, f x
-/
theorem tsum_iUnion_le {ι : Type*} [Fintype ι] (f : α → ℝ≥0∞) (t : ι → Set α) :
    ∑' x : ⋃ i, t i, f x ≤ ∑ i, ∑' x : t i, f x := by
  rw [← tsum_fintype (L := SummationFilter.unconditional _)]
  exact tsum_iUnion_le_tsum f t
/-
**ENNReal.tsum_union_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tsum_union_le (f : α -> Real>=0∞) (s t : Set α) : ∑' x : ↑(s union t), f x
 <= ∑' x : s, f x + ∑' x : t, f x
参数：f : α -> Real>=0∞；s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsum_congr_set_coe`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoi
d α] [inst_1 : TopologicalSpace α] (f : β → α) {s t : Set β},   s = t → ∑' (x : 
↑s), f ↑…
· 使用定理 `Set.union_eq_iUnion`：union_eq_iUnion {s₁ s₂ : Set α} : s₁ union s₂ = ⋃ b
 : Bool, cond b s₁ s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Bool.true_eq_false`：(true = false) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `ENNReal.tsum_iUnion_le`：tsum_iUnion_le {ι : Type*} [Fintype ι] (f : α ->
 Real>=0∞) (t : ι -> Set α) : ∑' x : ⋃ i, t i, f x <= ∑ i, ∑' x : t i, f x
-/
theorem tsum_union_le (f : α → ℝ≥0∞) (s t : Set α) :
    ∑' x : ↑(s ∪ t), f x ≤ ∑' x : s, f x + ∑' x : t, f x :=
  calc ∑' x : ↑(s ∪ t), f x = ∑' x : ⋃ b, cond b s t, f x := tsum_congr_set_coe _ union_eq_iUnion
  _ ≤ _ := by simpa using tsum_iUnion_le f (cond · s t)

open scoped Classical in
/-
**ENNReal.tsum_eq_add_tsum_ite** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tsum_eq_add_tsum_ite {f : β -> Real>=0∞} (b : β) : ∑' x, f x = f b + ∑' x,
 ite (x = b) 0 (f x)
参数：b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tsum_eq_add_tsum_ite'`：∀ {α : Type u_1} {β : Type u_2} [inst : 
AddCommMonoid α] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   [T2Spac
e α] [ContinuousAdd …
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
-/
theorem tsum_eq_add_tsum_ite {f : β → ℝ≥0∞} (b : β) :
    ∑' x, f x = f b + ∑' x, ite (x = b) 0 (f x) :=
  ENNReal.summable.tsum_eq_add_tsum_ite' b
/-
**ENNReal.tsum_add_one_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tsum_add_one_eq_top {f : Nat -> Real>=0∞} (hf : ∑' n, f n = ∞) (hf0 : f 0 
!= ∞) : ∑' n, f (n + 1) = ∞
参数：hf : ∑' n, f n = ∞；hf0 : f 0 != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.add_eq_top`：∀ {a b : ENNReal}, a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤
· 使用定理 `tsum_eq_zero_add'`：∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_1 : T
opologicalSpace M] [T2Space M] [ContinuousAdd M] {f : ℕ → M},   (Summable fun n 
=> f (n…
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
-/
theorem tsum_add_one_eq_top {f : ℕ → ℝ≥0∞} (hf : ∑' n, f n = ∞) (hf0 : f 0 ≠ ∞) :
    ∑' n, f (n + 1) = ∞ := by
  rw [tsum_eq_zero_add' ENNReal.summable, add_eq_top] at hf
  exact hf.resolve_left hf0

/-- A sum of extended nonnegative reals which is finite can have only finitely many terms
above any positive threshold. -/
/-
**ENNReal.finite_const_le_of_tsum_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：finite_const_le_of_tsum_ne_top {ι : Type*} {a : ι -> Real>=0∞} (tsum_ne_to
p : ∑' i, a i != ∞) {ε : Real>=0∞} (ε_ne_zero : ε != 0) : { i : ι | ε <= a i }.F
inite
参数：tsum_ne_top : ∑' i, a i != ∞；ε_ne_zero : ε != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Set.Infinite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Infinite → Infini
te ↑s
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.tsum_const_eq_top_of_ne_zero`：tsum_const_eq_top_of_ne_zero {α : 
Type*} [Infinite α] {c : Real>=0∞} (hc : c != 0) : ∑' _ : α, c = ∞
· 使用定理 `Summable.tsum_le_tsum_of_inj`：∀ {ι : Type u_1} {κ : Type u_2} {α : Type 
u_3} [inst : AddCommMonoid α] [inst_1 : Preorder α] [IsOrderedAddMonoid α]   [in
st_3 : Topological…
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f

--- 原说明 ---
A sum of extended nonnegative reals which is finite can have only finitely many 
terms
above any positive threshold.
-/
theorem finite_const_le_of_tsum_ne_top {ι : Type*} {a : ι → ℝ≥0∞} (tsum_ne_top : ∑' i, a i ≠ ∞)
    {ε : ℝ≥0∞} (ε_ne_zero : ε ≠ 0) : { i : ι | ε ≤ a i }.Finite := by
  by_contra h
  have := Infinite.to_subtype h
  refine tsum_ne_top (top_unique ?_)
  calc ∞ = ∑' _ : { i | ε ≤ a i }, ε := (tsum_const_eq_top_of_ne_zero ε_ne_zero).symm
  _ ≤ ∑' i, a i := ENNReal.summable.tsum_le_tsum_of_inj (↑)
    Subtype.val_injective (fun _ _ => zero_le) (fun i => i.2) ENNReal.summable

/-- Markov's inequality for `Finset.card` and `tsum` in `ℝ≥0∞`. -/
/-
**ENNReal.finset_card_const_le_le_of_tsum_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`
。
形式化陈述：finset_card_const_le_le_of_tsum_le {ι : Type*} {a : ι -> Real>=0∞} {c : Re
al>=0∞} (c_ne_top : c != ∞) (tsum_le_c : ∑' i, a i <= c) {ε : Real>=0∞} (ε_ne_ze
ro : ε != 0) : exists hf : { i : ι | ε <= a i }.Finite, #hf.toFinset <= c / ε
参数：c_ne_top : c != ∞；tsum_le_c : ∑' i, a i <= c；ε_ne_zero : ε != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.finite_const_le_of_tsum_ne_top`：finite_const_le_of_tsum_ne_top {
ι : Type*} {a : ι -> Real>=0∞} (tsum_ne_top : ∑' i, a i != ∞) {ε : Real>=0∞} (ε_
ne_zero : ε != 0) : { i : ι …
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.le_div_iff_mul_le`：∀ {a b c : ENNReal}, b ≠ 0 ∨ c ≠ 0 → b ≠ ⊤ ∨ 
c ≠ ⊤ → (a ≤ c / b ↔ a * b ≤ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
· 使用定理 `ENNReal.sum_le_tsum`：∀ {α : Type u_1} {f : α → ENNReal} (s : Finset α), 
∑ x ∈ s, f x ≤ ∑' (x : α), f x

--- 原说明 ---
Markov's inequality for `Finset.card` and `tsum` in `ℝ≥0∞`.
-/
theorem finset_card_const_le_le_of_tsum_le {ι : Type*} {a : ι → ℝ≥0∞} {c : ℝ≥0∞} (c_ne_top : c ≠ ∞)
    (tsum_le_c : ∑' i, a i ≤ c) {ε : ℝ≥0∞} (ε_ne_zero : ε ≠ 0) :
    ∃ hf : { i : ι | ε ≤ a i }.Finite, #hf.toFinset ≤ c / ε := by
  have hf : { i : ι | ε ≤ a i }.Finite :=
    finite_const_le_of_tsum_ne_top (ne_top_of_le_ne_top c_ne_top tsum_le_c) ε_ne_zero
  refine ⟨hf, (ENNReal.le_div_iff_mul_le (.inl ε_ne_zero) (.inr c_ne_top)).2 ?_⟩
  calc #hf.toFinset * ε = ∑ _i ∈ hf.toFinset, ε := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ hf.toFinset, a i := Finset.sum_le_sum fun i => hf.mem_toFinset.1
    _ ≤ ∑' i, a i := ENNReal.sum_le_tsum _
    _ ≤ c := tsum_le_c
/-
**ENNReal.tsum_fiberwise** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tsum_fiberwise (f : β -> Real>=0∞) (g : β -> γ) : ∑' x, ∑' b : g ⁻¹' {x}, 
f b = ∑' i, f i
参数：f : β -> Real>=0∞；g : β -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasSum.sigma`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] [ContinuousAdd α]   [RegularSpace α] {γ : β → Type 
u_…
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `T3Space.toRegularSpace`：∀ {X : Type u} {inst : TopologicalSpace X} [self
 : T3Space X], RegularSpace X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `ENNReal.instT4Space`：T4Space ENNReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.hasSum_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst :
 AddCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} (e : γ ≃ β
), Has…
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
· 使用定理 `Summable.hasSum_iff`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMono
id α] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α
} [T2Spac…
-/
theorem tsum_fiberwise (f : β → ℝ≥0∞) (g : β → γ) :
    ∑' x, ∑' b : g ⁻¹' {x}, f b = ∑' i, f i := by
  apply HasSum.tsum_eq
  let equiv := Equiv.sigmaFiberEquiv g
  apply (equiv.hasSum_iff.mpr ENNReal.summable.hasSum).sigma
  exact fun _ ↦ ENNReal.summable.hasSum_iff.mpr rfl

end tsum

/-
**ENNReal.tsum_coe_ne_top_iff_summable_coe** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tsum_coe_ne_top_iff_summable_coe {f : α -> Real>=0} : (∑' a, (f a : Real>=
0∞)) != ∞ ↔ Summable fun a => (f a : Real)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.summable_coe`：summable_coe {f : α -> Real>=0} : (Summable (fun a 
=> (f a : Real)) L) ↔ Summable f L
· 使用定理 `ENNReal.tsum_coe_ne_top_iff_summable`：tsum_coe_ne_top_iff_summable {f : 
β -> Real>=0} : (∑' b, (f b : Real>=0∞)) != ∞ ↔ Summable f
-/
theorem tsum_coe_ne_top_iff_summable_coe {f : α → ℝ≥0} :
    (∑' a, (f a : ℝ≥0∞)) ≠ ∞ ↔ Summable fun a => (f a : ℝ) := by
  rw [NNReal.summable_coe]
  exact tsum_coe_ne_top_iff_summable
/-
**ENNReal.tsum_coe_eq_top_iff_not_summable_coe** 是 Mathlib 中的一个定理，位于命名空间 `ENNRea
l`。
形式化陈述：tsum_coe_eq_top_iff_not_summable_coe {f : α -> Real>=0} : (∑' a, (f a : Re
al>=0∞)) = ∞ ↔ ¬Summable fun a => (f a : Real)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not_right`：Iff.not_right (h : ¬a ↔ b) : a ↔ ¬b
· 使用定理 `ENNReal.tsum_coe_ne_top_iff_summable_coe`：tsum_coe_ne_top_iff_summable_c
oe {f : α -> Real>=0} : (∑' a, (f a : Real>=0∞)) != ∞ ↔ Summable fun a => (f a :
 Real)
-/
theorem tsum_coe_eq_top_iff_not_summable_coe {f : α → ℝ≥0} :
    (∑' a, (f a : ℝ≥0∞)) = ∞ ↔ ¬Summable fun a => (f a : ℝ) :=
  tsum_coe_ne_top_iff_summable_coe.not_right
/-
**ENNReal.hasSum_toReal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：hasSum_toReal {f : α -> Real>=0∞} (hsum : ∑' x, f x != ∞) : HasSum (fun x 
=> (f x).toReal) (∑' x, (f x).toReal)
参数：hsum : ∑' x, f x != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `ENNReal.ne_top_of_tsum_ne_top`：∀ {α : Type u_1} {f : α → ENNReal}, ∑' (a
 : α), f a ≠ ⊤ → ∀ (a : α), f a ≠ ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.tsum_coe_ne_top_iff_summable`：tsum_coe_ne_top_iff_summable {f : 
β -> Real>=0} : (∑' b, (f b : Real>=0∞)) != ∞ ↔ Summable f
-/
theorem hasSum_toReal {f : α → ℝ≥0∞} (hsum : ∑' x, f x ≠ ∞) :
    HasSum (fun x => (f x).toReal) (∑' x, (f x).toReal) := by
  lift f to α → ℝ≥0 using ENNReal.ne_top_of_tsum_ne_top hsum
  simp only [coe_toReal, ← NNReal.coe_tsum, NNReal.hasSum_coe]
  exact (tsum_coe_ne_top_iff_summable.1 hsum).hasSum
/-
**ENNReal.summable_toReal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：summable_toReal {f : α -> Real>=0∞} (hsum : ∑' x, f x != ∞) : Summable fun
 x => (f x).toReal
参数：hsum : ∑' x, f x != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `ENNReal.hasSum_toReal`：hasSum_toReal {f : α -> Real>=0∞} (hsum : ∑' x, f
 x != ∞) : HasSum (fun x => (f x).toReal) (∑' x, (f x).toReal)
-/
theorem summable_toReal {f : α → ℝ≥0∞} (hsum : ∑' x, f x ≠ ∞) : Summable fun x => (f x).toReal :=
  (hasSum_toReal hsum).summable

end ENNReal

namespace NNReal


/-
**NNReal.tsum_eq_toNNReal_tsum** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：tsum_eq_toNNReal_tsum {f : β -> Real>=0} : ∑' b, f b = (∑' b, (f b : Real>
=0∞)).toNNReal
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_tsum`：∀ {α : Type u_1} {f : α → NNReal}, Summable f → ↑(tsum
 f) = ∑' (a : α), ↑(f a)
· 使用定理 `ENNReal.toNNReal_coe`：∀ (r : NNReal), (↑r).toNNReal = r
· 使用定理 `tsum_eq_zero_of_not_summable`：∀ {α : Type u_1} {β : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → 
α}, ¬Summable f L …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tsum_eq_toNNReal_tsum {f : β → ℝ≥0} : ∑' b, f b = (∑' b, (f b : ℝ≥0∞)).toNNReal := by
  by_cases h : Summable f
  · rw [← ENNReal.coe_tsum h, ENNReal.toNNReal_coe]
  · have A := tsum_eq_zero_of_not_summable h
    simp only [← ENNReal.tsum_coe_ne_top_iff_summable, Classical.not_not] at h
    simp only [h, ENNReal.toNNReal_top, A]

/-- Comparison test of convergence of `ℝ≥0`-valued series. -/
/-
**NNReal.exists_le_hasSum_of_le** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：exists_le_hasSum_of_le {f g : β -> Real>=0} {r : Real>=0} (hgf : forall b,
 g b <= f b) (hfr : HasSum f r) : exists p <= r, HasSum g p
参数：hgf : forall b, g b <= f b；hfr : HasSum f r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasSum_le`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι} [inst
 : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [inst_3 : To…
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
· 使用定理 `ENNReal.hasSum_coe`：∀ {α : Type u_1} {f : α → NNReal} {r : NNReal}, HasS
um (fun a => ↑(f a)) ↑r ↔ HasSum f r
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.le_coe_iff`：le_coe_iff : a <= ↑r ↔ exists p : Real>=0, a = p ∧ p
 <= r

--- 原说明 ---
Comparison test of convergence of `ℝ≥0`-valued series.
-/
theorem exists_le_hasSum_of_le {f g : β → ℝ≥0} {r : ℝ≥0} (hgf : ∀ b, g b ≤ f b) (hfr : HasSum f r) :
    ∃ p ≤ r, HasSum g p :=
  have : (∑' b, (g b : ℝ≥0∞)) ≤ r := by
    refine hasSum_le (fun b => ?_) ENNReal.summable.hasSum (ENNReal.hasSum_coe.2 hfr)
    exact ENNReal.coe_le_coe.2 (hgf _)
  let ⟨p, Eq, hpr⟩ := ENNReal.le_coe_iff.1 this
  ⟨p, hpr, ENNReal.hasSum_coe.1 <| Eq ▸ ENNReal.summable.hasSum⟩

/-- Comparison test of convergence of `ℝ≥0`-valued series. -/
/-
**NNReal.summable_of_le** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：summable_of_le {f g : β -> Real>=0} (hgf : forall b, g b <= f b) : Summabl
e f -> Summable g | ⟨_r, hfr⟩ => let ⟨_p, _, hp⟩
参数：hgf : forall b, g b <= f b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.exists_le_hasSum_of_le`：exists_le_hasSum_of_le {f g : β -> Real>=
0} {r : Real>=0} (hgf : forall b, g b <= f b) (hfr : HasSum f r) : exists p <= r
, HasSum g p
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…

--- 原说明 ---
Comparison test of convergence of `ℝ≥0`-valued series.
-/
theorem summable_of_le {f g : β → ℝ≥0} (hgf : ∀ b, g b ≤ f b) : Summable f → Summable g
  | ⟨_r, hfr⟩ =>
    let ⟨_p, _, hp⟩ := exists_le_hasSum_of_le hgf hfr
    hp.summable

/-- Summable non-negative functions have countable support -/
/-
**NNReal._root_.Summable.countable_support_nnreal** 是 Mathlib 中的一个定理，位于命名空间 `NNR
eal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Summable non-negative functions have countable support
-/
theorem _root_.Summable.countable_support_nnreal (f : α → ℝ≥0) (h : Summable f) :
    f.support.Countable := by
  rw [← NNReal.summable_coe] at h
  simpa [support] using h.countable_support

/-- A series of non-negative real numbers converges to `r` in the sense of `HasSum` if and only if
the sequence of partial sum converges to `r`. -/
/-
**NNReal.hasSum_iff_tendsto_nat** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：hasSum_iff_tendsto_nat {f : Nat -> Real>=0} {r : Real>=0} : HasSum f r ↔ T
endsto (fun n : Nat => ∑ i in Finset.range n, f i) atTop (𝓝 r)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.hasSum_coe`：∀ {α : Type u_1} {f : α → NNReal} {r : NNReal}, HasS
um (fun a => ↑(f a)) ↑r ↔ HasSum f r
· 使用定理 `ENNReal.hasSum_iff_tendsto_nat`：hasSum_iff_tendsto_nat {f : Nat -> Real>
=0∞} (r : Real>=0∞) : HasSum f r ↔ Tendsto (fun n : Nat => ∑ i in Finset.range n
, f i) atTop (𝓝 r)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A series of non-negative real numbers converges to `r` in the sense of `HasSum` 
if and only if
the sequence of partial sum converges to `r`.
-/
theorem hasSum_iff_tendsto_nat {f : ℕ → ℝ≥0} {r : ℝ≥0} :
    HasSum f r ↔ Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop (𝓝 r) := by
  rw [← ENNReal.hasSum_coe, ENNReal.hasSum_iff_tendsto_nat]
  norm_cast
/-
**NNReal.not_summable_iff_tendsto_nat_atTop** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：not_summable_iff_tendsto_nat_atTop {f : Nat -> Real>=0} : ¬Summable f ↔ Te
ndsto (fun n : Nat => ∑ i in Finset.range n, f i) atTop atTop
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `tendsto_atTop_of_monotone`：tendsto_atTop_of_monotone {ι α : Type*} [Preo
rder ι] [TopologicalSpace α] [ConditionallyCompleteLinearOrder α] [OrderTopology
 α] {f : ι -> α…
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `Finset.sum_mono_set`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMono
id M] [inst_1 : Preorder M] [CanonicallyOrderedAdd M] (f : ι → M),   Monotone fu
n s => ∑ …
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `Filter.tendsto_finset_range`：tendsto_finset_range : Tendsto Finset.range
 atTop atTop
· 使用定理 `not_tendsto_nhds_of_tendsto_atTop`：∀ {α : Type u} {β : Type v} [inst : P
reorder α] [NoTopOrder α] [inst_2 : TopologicalSpace α] [ClosedIciTopology α]   
{l : Filter β} [l.NeBot…
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `IsStrictOrderedRing.toNoMaxOrder`：∀ {R : Type u} [inst : Semiring R] [in
st_1 : PartialOrder R] [IsStrictOrderedRing R], NoMaxOrder R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NNReal.hasSum_iff_tendsto_nat`：hasSum_iff_tendsto_nat {f : Nat -> Real>=
0} {r : Real>=0} : HasSum f r ↔ Tendsto (fun n : Nat => ∑ i in Finset.range n, f
 i) atTop (𝓝 r)
-/
theorem not_summable_iff_tendsto_nat_atTop {f : ℕ → ℝ≥0} :
    ¬Summable f ↔ Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop atTop := by
  constructor
  · intro h
    refine ((tendsto_atTop_of_monotone ?_).resolve_right h).comp ?_
    exacts [Finset.sum_mono_set _, tendsto_finset_range]
  · rintro hnat ⟨r, hr⟩
    exact not_tendsto_nhds_of_tendsto_atTop hnat _ (hasSum_iff_tendsto_nat.1 hr)
/-
**NNReal.summable_iff_not_tendsto_nat_atTop** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：summable_iff_not_tendsto_nat_atTop {f : Nat -> Real>=0} : Summable f ↔ ¬Te
ndsto (fun n : Nat => ∑ i in Finset.range n, f i) atTop atTop
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `NNReal.not_summable_iff_tendsto_nat_atTop`：not_summable_iff_tendsto_nat_
atTop {f : Nat -> Real>=0} : ¬Summable f ↔ Tendsto (fun n : Nat => ∑ i in Finset
.range n, f i) atTop atTop
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem summable_iff_not_tendsto_nat_atTop {f : ℕ → ℝ≥0} :
    Summable f ↔ ¬Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop atTop := by
  rw [← not_iff_not, Classical.not_not, not_summable_iff_tendsto_nat_atTop]
/-
**NNReal.summable_of_sum_range_le** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：summable_of_sum_range_le {f : Nat -> Real>=0} {c : Real>=0} (h : forall n,
 ∑ i in Finset.range n, f i <= c) : Summable f
参数：h : forall n, ∑ i in Finset.range n, f i <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.summable_iff_not_tendsto_nat_atTop`：summable_iff_not_tendsto_nat_
atTop {f : Nat -> Real>=0} : Summable f ↔ ¬Tendsto (fun n : Nat => ∑ i in Finset
.range n, f i) atTop atTop
· 使用定理 `Filter.exists_lt_of_tendsto_atTop`：exists_lt_of_tendsto_atTop [NoMaxOrde
r β] (h : Tendsto u atTop atTop) (a : α) (b : β) : exists a', a <= a' ∧ b < u a'
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `IsStrictOrderedRing.toNoMaxOrder`：∀ {R : Type u} [inst : Semiring R] [in
st_1 : PartialOrder R] [IsStrictOrderedRing R], NoMaxOrder R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
-/
theorem summable_of_sum_range_le {f : ℕ → ℝ≥0} {c : ℝ≥0}
    (h : ∀ n, ∑ i ∈ Finset.range n, f i ≤ c) : Summable f := by
  refine summable_iff_not_tendsto_nat_atTop.2 fun H => ?_
  rcases exists_lt_of_tendsto_atTop H 0 c with ⟨n, -, hn⟩
  exact lt_irrefl _ (hn.trans_le (h n))
/-
**NNReal.tsum_le_of_sum_range_le** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：tsum_le_of_sum_range_le {f : Nat -> Real>=0} {c : Real>=0} (h : forall n, 
∑ i in Finset.range n, f i <= c) : ∑' n, f n <= c
参数：h : forall n, ∑ i in Finset.range n, f i <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tsum_le_of_sum_range_le`：∀ {α : Type u_3} [inst : Preorder α] [
inst_1 : AddCommMonoid α] [inst_2 : TopologicalSpace α] {c : α}   [ClosedIicTopo
logy α] {f : ℕ → α}, S…
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `NNReal.summable_of_sum_range_le`：summable_of_sum_range_le {f : Nat -> Re
al>=0} {c : Real>=0} (h : forall n, ∑ i in Finset.range n, f i <= c) : Summable 
f
-/
theorem tsum_le_of_sum_range_le {f : ℕ → ℝ≥0} {c : ℝ≥0}
    (h : ∀ n, ∑ i ∈ Finset.range n, f i ≤ c) : ∑' n, f n ≤ c :=
  (summable_of_sum_range_le h).tsum_le_of_sum_range_le h
/-
**NNReal.tsum_comp_le_tsum_of_inj** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：tsum_comp_le_tsum_of_inj {β : Type*} {f : α -> Real>=0} (hf : Summable f) 
{i : β -> α} (hi : Function.Injective i) : (∑' x, f (i x)) <= ∑' x, f x
参数：hf : Summable f；hi : Function.Injective i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tsum_le_tsum_of_inj`：∀ {ι : Type u_1} {κ : Type u_2} {α : Type 
u_3} [inst : AddCommMonoid α] [inst_1 : Preorder α] [IsOrderedAddMonoid α]   [in
st_3 : Topological…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `NNReal.summable_comp_injective`：summable_comp_injective {β : Type*} {f :
 α -> Real>=0} (hf : Summable f) {i : β -> α} (hi : Function.Injective i) : Summ
able (f ∘ i)
-/
theorem tsum_comp_le_tsum_of_inj {β : Type*} {f : α → ℝ≥0} (hf : Summable f) {i : β → α}
    (hi : Function.Injective i) : (∑' x, f (i x)) ≤ ∑' x, f x :=
  (summable_comp_injective hf hi).tsum_le_tsum_of_inj i hi (fun _ _ => zero_le) (fun _ => le_rfl)
    hf
/-
**NNReal.summable_sigma** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：summable_sigma {β : α -> Type*} {f : (Σ x, β x) -> Real>=0} : Summable f ↔
 (forall x, Summable fun y => f ⟨x, y⟩) ∧ Summable fun x => ∑' y, f ⟨x, y⟩
参数：Σ x, β x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
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
· 使用定理 `NNReal.coe_tsum`：coe_tsum {f : α -> Real>=0} : ↑(∑'[L] a, f a) = ∑'[L] a
, (f a : Real)
· 使用定理 `Summable.sigma_factor`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommGr
oup α] [inst_1 : UniformSpace α] [IsUniformAddGroup α]   [CompleteSpace α] {γ : 
β → Type u_…
· 使用定理 `instIsUniformAddGroupReal`：IsUniformAddGroup ℝ
· 使用定理 `Summable.sigma`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommGroup α] 
[inst_1 : UniformSpace α] [IsUniformAddGroup α]   [CompleteSpace α] {γ : β → Typ
e u_…
· 使用定理 `ENNReal.tsum_sigma'`：∀ {α : Type u_1} {β : α → Type u_4} (f : (a : α) × 
β a → ENNReal),   ∑' (p : (a : α) × β a), f p = ∑' (a : α) (b : β a), f ⟨a, b⟩
· 使用定理 `ENNReal.coe_tsum`：∀ {α : Type u_1} {f : α → NNReal}, Summable f → ↑(tsum
 f) = ∑' (a : α), ↑(f a)
-/
theorem summable_sigma {β : α → Type*} {f : (Σ x, β x) → ℝ≥0} :
    Summable f ↔ (∀ x, Summable fun y => f ⟨x, y⟩) ∧ Summable fun x => ∑' y, f ⟨x, y⟩ := by
  constructor
  · simp only [← NNReal.summable_coe, NNReal.coe_tsum]
    exact fun h => ⟨h.sigma_factor, h.sigma⟩
  · rintro ⟨h₁, h₂⟩
    simpa only [← ENNReal.tsum_coe_ne_top_iff_summable, ENNReal.tsum_sigma',
      ENNReal.coe_tsum (h₁ _)] using h₂
/-
**NNReal.indicator_summable** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：indicator_summable {f : α -> Real>=0} (hf : Summable f) (s : Set α) : Summ
able (s.indicator f)
参数：hf : Summable f；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.summable_of_le`：summable_of_le {f g : β -> Real>=0} (hgf : forall
 b, g b <= f b) : Summable f -> Summable g | ⟨_r, hfr⟩ => let ⟨_p, _, hp⟩
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `NNReal.zero_le_coe`：zero_le_coe {q : Real>=0} : 0 <= (q : Real)
-/
theorem indicator_summable {f : α → ℝ≥0} (hf : Summable f) (s : Set α) :
    Summable (s.indicator f) := by
  classical
  refine NNReal.summable_of_le (fun a => le_trans (le_of_eq (s.indicator_apply f a)) ?_) hf
  split_ifs
  · exact le_refl (f a)
  · exact zero_le_coe
/-
**NNReal.tsum_indicator_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：tsum_indicator_ne_zero {f : α -> Real>=0} (hf : Summable f) {s : Set α} (h
 : exists a in s, f a != 0) : (∑' x, (s.indicator f) x) != 0
参数：hf : Summable f；h : exists a in s, f a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.indicator_apply_eq_self`：∀ {α : Type u_1} {M : Type u_3} [inst : Zer
o M] {s : Set α} {f : α → M} {a : α}, s.indicator f a = f a ↔ a ∉ s → f a = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Summable.tsum_eq_zero_iff`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddCo
mmMonoid α] [inst_1 : PartialOrder α] [IsOrderedAddMonoid α]   [CanonicallyOrder
edAdd α] [inst_…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `NNReal.indicator_summable`：indicator_summable {f : α -> Real>=0} (hf : S
ummable f) (s : Set α) : Summable (s.indicator f)
-/
theorem tsum_indicator_ne_zero {f : α → ℝ≥0} (hf : Summable f) {s : Set α} (h : ∃ a ∈ s, f a ≠ 0) :
    (∑' x, (s.indicator f) x) ≠ 0 := fun h' =>
  let ⟨a, ha, hap⟩ := h
  hap ((Set.indicator_apply_eq_self.mpr (absurd ha)).symm.trans
    ((indicator_summable hf s).tsum_eq_zero_iff.1 h' a))

open Finset

/-- For `f : ℕ → ℝ≥0`, then `∑' k, f (k + i)` tends to zero. This does not require a summability
assumption on `f`, as otherwise all sums are zero. -/
/-
**NNReal.tendsto_sum_nat_add** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：tendsto_sum_nat_add (f : Nat -> Real>=0) : Tendsto (fun i => ∑' k, f (k + 
i)) atTop (𝓝 0)
参数：f : Nat -> Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.tendsto_coe`：tendsto_coe {f : Filter α} {m : α -> Real>=0} {x : R
eal>=0} : Tendsto (fun a => (m a : Real)) f (𝓝 (x : Real)) ↔ Tendsto m f (𝓝 x)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `tendsto_sum_nat_add`：∀ {G : Type u_2} [inst : AddCommGroup G] [inst_1 : 
TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]   (f : ℕ → G), Filter.
Tendsto (…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α

--- 原说明 ---
For `f : ℕ → ℝ≥0`, then `∑' k, f (k + i)` tends to zero. This does not require a
 summability
assumption on `f`, as otherwise all sums are zero.
-/
theorem tendsto_sum_nat_add (f : ℕ → ℝ≥0) : Tendsto (fun i => ∑' k, f (k + i)) atTop (𝓝 0) := by
  rw [← tendsto_coe]
  convert! _root_.tendsto_sum_nat_add fun i => (f i : ℝ)
  norm_cast

nonrec theorem hasSum_lt {f g : α → ℝ≥0} {sf sg : ℝ≥0} {i : α} (h : ∀ a : α, f a ≤ g a)
    (hi : f i < g i) (hf : HasSum f sf) (hg : HasSum g sg) : sf < sg := by
  have A : ∀ a : α, (f a : ℝ) ≤ g a := fun a => NNReal.coe_le_coe.2 (h a)
  have : (sf : ℝ) < sg := hasSum_lt A (NNReal.coe_lt_coe.2 hi) (hasSum_coe.2 hf) (hasSum_coe.2 hg)
  exact NNReal.coe_lt_coe.1 this

@[mono]
/-
**NNReal.hasSum_strict_mono** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：hasSum_strict_mono {f g : α -> Real>=0} {sf sg : Real>=0} (hf : HasSum f s
f) (hg : HasSum g sg) (h : f < g) : sf < sg
参数：hf : HasSum f sf；hg : HasSum g sg；h : f < g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Pi.lt_def`：Pi.lt_def [forall i, Preorder (π i)] {x y : forall i, π i} : 
x < y ↔ x <= y ∧ exists i, x i < y i
· 使用定理 `NNReal.hasSum_lt`：∀ {α : Type u_1} {f g : α → NNReal} {sf sg : NNReal} {
i : α},   (∀ (a : α), f a ≤ g a) → f i < g i → HasSum f sf → HasSum g sg → sf < 
sg
-/
theorem hasSum_strict_mono {f g : α → ℝ≥0} {sf sg : ℝ≥0} (hf : HasSum f sf) (hg : HasSum g sg)
    (h : f < g) : sf < sg :=
  let ⟨hle, _i, hi⟩ := Pi.lt_def.mp h
  hasSum_lt hle hi hf hg
/-
**NNReal.tsum_lt_tsum** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：tsum_lt_tsum {f g : α -> Real>=0} {i : α} (h : forall a : α, f a <= g a) (
hi : f i < g i) (hg : Summable g) : ∑' n, f n < ∑' n, g n
参数：h : forall a : α, f a <= g a；hi : f i < g i；hg : Summable g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.hasSum_lt`：∀ {α : Type u_1} {f g : α → NNReal} {sf sg : NNReal} {
i : α},   (∀ (a : α), f a ≤ g a) → f i < g i → HasSum f sf → HasSum g sg → sf < 
sg
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `NNReal.summable_of_le`：summable_of_le {f g : β -> Real>=0} (hgf : forall
 b, g b <= f b) : Summable f -> Summable g | ⟨_r, hfr⟩ => let ⟨_p, _, hp⟩
-/
theorem tsum_lt_tsum {f g : α → ℝ≥0} {i : α} (h : ∀ a : α, f a ≤ g a) (hi : f i < g i)
    (hg : Summable g) : ∑' n, f n < ∑' n, g n :=
  hasSum_lt h hi (summable_of_le h hg).hasSum hg.hasSum

@[gcongr, mono]
/-
**NNReal.tsum_strict_mono** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：tsum_strict_mono {f g : α -> Real>=0} (hg : Summable g) (h : f < g) : ∑' n
, f n < ∑' n, g n
参数：hg : Summable g；h : f < g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Pi.lt_def`：Pi.lt_def [forall i, Preorder (π i)] {x y : forall i, π i} : 
x < y ↔ x <= y ∧ exists i, x i < y i
· 使用定理 `NNReal.tsum_lt_tsum`：tsum_lt_tsum {f g : α -> Real>=0} {i : α} (h : fora
ll a : α, f a <= g a) (hi : f i < g i) (hg : Summable g) : ∑' n, f n < ∑' n, g n
-/
theorem tsum_strict_mono {f g : α → ℝ≥0} (hg : Summable g) (h : f < g) : ∑' n, f n < ∑' n, g n :=
  let ⟨hle, _i, hi⟩ := Pi.lt_def.mp h
  tsum_lt_tsum hle hi hg
/-
**NNReal.tsum_pos** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：tsum_pos {g : α -> Real>=0} (hg : Summable g) (i : α) (hi : 0 < g i) : 0 <
 ∑' b, g b
参数：hg : Summable g；i : α；hi : 0 < g i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `NNReal.tsum_lt_tsum`：tsum_lt_tsum {f g : α -> Real>=0} {i : α} (h : fora
ll a : α, f a <= g a) (hi : f i < g i) (hg : Summable g) : ∑' n, f n < ∑' n, g n
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem tsum_pos {g : α → ℝ≥0} (hg : Summable g) (i : α) (hi : 0 < g i) : 0 < ∑' b, g b := by
  simpa using tsum_lt_tsum (fun a => zero_le) hi hg

open scoped Classical in
/-
**NNReal.tsum_eq_add_tsum_ite** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：tsum_eq_add_tsum_ite {f : α -> Real>=0} (hf : Summable f) (i : α) : ∑' x, 
f x = f i + ∑' x, ite (x = i) 0 (f x)
参数：hf : Summable f；i : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tsum_eq_add_tsum_ite'`：∀ {α : Type u_1} {β : Type u_2} [inst : 
AddCommMonoid α] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   [T2Spac
e α] [ContinuousAdd …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `NNReal.summable_of_le`：summable_of_le {f g : β -> Real>=0} (hgf : forall
 b, g b <= f b) : Summable f -> Summable g | ⟨_r, hfr⟩ => let ⟨_p, _, hp⟩
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_apply`：update_apply {β : Sort*} (f : α -> β) (a' : α) (b
 : β) (a : α) : update f a' b a = if a = a' then b else f a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem tsum_eq_add_tsum_ite {f : α → ℝ≥0} (hf : Summable f) (i : α) :
    ∑' x, f x = f i + ∑' x, ite (x = i) 0 (f x) := by
  refine (NNReal.summable_of_le (fun i' => ?_) hf).tsum_eq_add_tsum_ite' i
  rw [Function.update_apply]
  split_ifs <;> simp

end NNReal

namespace ENNReal

/-
**ENNReal.tsum_toNNReal_eq** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tsum_toNNReal_eq {f : α -> Real>=0∞} (hf : forall a, f a != ∞) : (∑' a, f 
a).toNNReal = ∑' a, (f a).toNNReal
参数：hf : forall a, f a != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `NNReal.tsum_eq_toNNReal_tsum`：tsum_eq_toNNReal_tsum {f : β -> Real>=0} :
 ∑' b, f b = (∑' b, (f b : Real>=0∞)).toNNReal
-/
theorem tsum_toNNReal_eq {f : α → ℝ≥0∞} (hf : ∀ a, f a ≠ ∞) :
    (∑' a, f a).toNNReal = ∑' a, (f a).toNNReal :=
  (congr_arg ENNReal.toNNReal (tsum_congr fun x => (coe_toNNReal (hf x)).symm)).trans
    NNReal.tsum_eq_toNNReal_tsum.symm
/-
**ENNReal.tsum_toReal_eq** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tsum_toReal_eq {f : α -> Real>=0∞} (hf : forall a, f a != ∞) : (∑' a, f a)
.toReal = ∑' a, (f a).toReal
参数：hf : forall a, f a != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.tsum_toNNReal_eq`：tsum_toNNReal_eq {f : α -> Real>=0∞} (hf : for
all a, f a != ∞) : (∑' a, f a).toNNReal = ∑' a, (f a).toNNReal
· 使用定理 `NNReal.coe_tsum`：coe_tsum {f : α -> Real>=0} : ↑(∑'[L] a, f a) = ∑'[L] a
, (f a : Real)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tsum_toReal_eq {f : α → ℝ≥0∞} (hf : ∀ a, f a ≠ ∞) :
    (∑' a, f a).toReal = ∑' a, (f a).toReal := by
  simp only [ENNReal.toReal, tsum_toNNReal_eq hf, NNReal.coe_tsum]
/-
**ENNReal.tendsto_sum_nat_add** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tendsto_sum_nat_add (f : Nat -> Real>=0∞) (hf : ∑' i, f i != ∞) : Tendsto 
(fun i => ∑' k, f (k + i)) atTop (𝓝 0)
参数：f : Nat -> Real>=0∞；hf : ∑' i, f i != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `ENNReal.ne_top_of_tsum_ne_top`：∀ {α : Type u_1} {f : α → ENNReal}, ∑' (a
 : α), f a ≠ ⊤ → ∀ (a : α), f a ≠ ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.tsum_coe_ne_top_iff_summable`：tsum_coe_ne_top_iff_summable {f : 
β -> Real>=0} : (∑' b, (f b : Real>=0∞)) != ∞ ↔ Summable f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `NNReal.summable_nat_add`：summable_nat_add (f : Nat -> Real>=0) (hf : Sum
mable f) (k : Nat) : Summable fun i => f (i + k)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `NNReal.tendsto_sum_nat_add`：tendsto_sum_nat_add (f : Nat -> Real>=0) : T
endsto (fun i => ∑' k, f (k + i)) atTop (𝓝 0)
-/
theorem tendsto_sum_nat_add (f : ℕ → ℝ≥0∞) (hf : ∑' i, f i ≠ ∞) :
    Tendsto (fun i => ∑' k, f (k + i)) atTop (𝓝 0) := by
  lift f to ℕ → ℝ≥0 using ENNReal.ne_top_of_tsum_ne_top hf
  replace hf : Summable f := tsum_coe_ne_top_iff_summable.1 hf
  simp only [← ENNReal.coe_tsum, NNReal.summable_nat_add _ hf, ← ENNReal.coe_zero]
  exact mod_cast NNReal.tendsto_sum_nat_add f
/-
**ENNReal.tsum_le_of_sum_range_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tsum_le_of_sum_range_le {f : Nat -> Real>=0∞} {c : Real>=0∞} (h : forall n
, ∑ i in Finset.range n, f i <= c) : ∑' n, f n <= c
参数：h : forall n, ∑ i in Finset.range n, f i <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tsum_le_of_sum_range_le`：∀ {α : Type u_3} [inst : Preorder α] [
inst_1 : AddCommMonoid α] [inst_2 : TopologicalSpace α] {c : α}   [ClosedIicTopo
logy α] {f : ℕ → α}, S…
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
-/
theorem tsum_le_of_sum_range_le {f : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ n, ∑ i ∈ Finset.range n, f i ≤ c) : ∑' n, f n ≤ c :=
  ENNReal.summable.tsum_le_of_sum_range_le h
/-
**ENNReal.hasSum_lt** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：hasSum_lt {f g : α -> Real>=0∞} {sf sg : Real>=0∞} {i : α} (h : forall a :
 α, f a <= g a) (hi : f i < g i) (hsf : sf != ∞) (hf : HasSum f sf) (hg : HasSum
 g sg) : sf < sg
参数：h : forall a : α, f a <= g a；hi : f i < g i；hsf : sf != ∞；hf : HasSum f sf；hg
 : HasSum g sg。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ne_top_of_tsum_ne_top`：∀ {α : Type u_1} {f : α → ENNReal}, ∑' (a
 : α), f a ≠ ⊤ → ∀ (a : α), f a ≠ ⊤
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `NNReal.hasSum_lt`：∀ {α : Type u_1} {f g : α → NNReal} {sf sg : NNReal} {
i : α},   (∀ (a : α), f a ≤ g a) → f i < g i → HasSum f sf → HasSum g sg → sf < 
sg
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.hasSum_coe`：∀ {α : Type u_1} {f : α → NNReal} {r : NNReal}, HasS
um (fun a => ↑(f a)) ↑r ↔ HasSum f r
-/
theorem hasSum_lt {f g : α → ℝ≥0∞} {sf sg : ℝ≥0∞} {i : α} (h : ∀ a : α, f a ≤ g a) (hi : f i < g i)
    (hsf : sf ≠ ∞) (hf : HasSum f sf) (hg : HasSum g sg) : sf < sg := by
  by_cases hsg : sg = ∞
  · exact hsg.symm ▸ lt_of_le_of_ne le_top hsf
  · have hg' : ∀ x, g x ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top (hg.tsum_eq.symm ▸ hsg)
    lift f to α → ℝ≥0 using fun x =>
      ne_of_lt (lt_of_le_of_lt (h x) <| lt_of_le_of_ne le_top (hg' x))
    lift g to α → ℝ≥0 using hg'
    lift sf to ℝ≥0 using hsf
    lift sg to ℝ≥0 using hsg
    simp only [coe_le_coe, coe_lt_coe] at h hi ⊢
    exact NNReal.hasSum_lt h hi (ENNReal.hasSum_coe.1 hf) (ENNReal.hasSum_coe.1 hg)
/-
**ENNReal.tsum_lt_tsum** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tsum_lt_tsum {f g : α -> Real>=0∞} {i : α} (hfi : tsum f != ∞) (h : forall
 a : α, f a <= g a) (hi : f i < g i) : ∑' x, f x < ∑' x, g x
参数：hfi : tsum f != ∞；h : forall a : α, f a <= g a；hi : f i < g i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.hasSum_lt`：hasSum_lt {f g : α -> Real>=0∞} {sf sg : Real>=0∞} {i
 : α} (h : forall a : α, f a <= g a) (hi : f i < g i) (hsf : sf != ∞) (hf : HasS
um f sf…
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
-/
theorem tsum_lt_tsum {f g : α → ℝ≥0∞} {i : α} (hfi : tsum f ≠ ∞) (h : ∀ a : α, f a ≤ g a)
    (hi : f i < g i) : ∑' x, f x < ∑' x, g x :=
  hasSum_lt h hi hfi ENNReal.summable.hasSum ENNReal.summable.hasSum

end ENNReal

/-
**tsum_comp_le_tsum_of_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsum_comp_le_tsum_of_inj {β : Type*} {f : α -> Real} (hf : Summable f) (hn
 : forall a, 0 <= f a) {i : β -> α} (hi : Function.Injective i) : tsum (f ∘ i) <
= tsum f
参数：hf : Summable f；hn : forall a, 0 <= f a；hi : Function.Injective i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.tsum_comp_le_tsum_of_inj`：tsum_comp_le_tsum_of_inj {β : Type*} {f
 : α -> Real>=0} (hf : Summable f) {i : β -> α} (hi : Function.Injective i) : (∑
' x, f (i x)) <= ∑' x…
· 使用定理 `NNReal.summable_coe`：summable_coe {f : α -> Real>=0} : (Summable (fun a 
=> (f a : Real)) L) ↔ Summable f L
-/
theorem tsum_comp_le_tsum_of_inj {β : Type*} {f : α → ℝ} (hf : Summable f) (hn : ∀ a, 0 ≤ f a)
    {i : β → α} (hi : Function.Injective i) : tsum (f ∘ i) ≤ tsum f := by
  lift f to α → ℝ≥0 using hn
  rw [NNReal.summable_coe] at hf
  simpa only [Function.comp_def, ← NNReal.coe_tsum] using! NNReal.tsum_comp_le_tsum_of_inj hf hi

/-- Comparison test of convergence of series of non-negative real numbers. -/
/-
**Summable.of_nonneg_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.of_nonneg_of_le {f g : β -> Real} (hg : forall b, 0 <= g b) (hgf 
: forall b, g b <= f b) (hf : Summable f) : Summable g
参数：hg : forall b, 0 <= g b；hgf : forall b, g b <= f b；hf : Summable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.summable_coe`：summable_coe {f : α -> Real>=0} : (Summable (fun a 
=> (f a : Real)) L) ↔ Summable f L
· 使用定理 `NNReal.summable_of_le`：summable_of_le {f g : β -> Real>=0} (hgf : forall
 b, g b <= f b) : Summable f -> Summable g | ⟨_r, hfr⟩ => let ⟨_p, _, hp⟩
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂

--- 原说明 ---
Comparison test of convergence of series of non-negative real numbers.
-/
theorem Summable.of_nonneg_of_le {f g : β → ℝ} (hg : ∀ b, 0 ≤ g b) (hgf : ∀ b, g b ≤ f b)
    (hf : Summable f) : Summable g := by
  lift f to β → ℝ≥0 using fun b => (hg b).trans (hgf b)
  lift g to β → ℝ≥0 using hg
  rw [NNReal.summable_coe] at hf ⊢
  exact NNReal.summable_of_le (fun b => NNReal.coe_le_coe.1 (hgf b)) hf
/-
**Summable.toNNReal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.toNNReal {f : α -> Real} (hf : Summable f) : Summable fun n => (f
 n).toNNReal
参数：hf : Summable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NNReal.summable_coe`：summable_coe {f : α -> Real>=0} : (Summable (fun a 
=> (f a : Real)) L) ↔ Summable f L
· 使用定理 `Summable.of_nonneg_of_le`：Summable.of_nonneg_of_le {f g : β -> Real} (hg
 : forall b, 0 <= g b) (hgf : forall b, g b <= f b) (hf : Summable f) : Summable
 g
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Summable.abs`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddCommGroup α] [i
nst_1 : LinearOrder α] [IsOrderedAddMonoid α]   [inst_3 : UniformSpace α] [IsUni
fo…
· 使用定理 `instIsUniformAddGroupReal`：IsUniformAddGroup ℝ
-/
theorem Summable.toNNReal {f : α → ℝ} (hf : Summable f) : Summable fun n => (f n).toNNReal := by
  apply NNReal.summable_coe.1
  refine .of_nonneg_of_le (fun n => NNReal.coe_nonneg _) (fun n => ?_) hf.abs
  simp only [le_abs_self, Real.coe_toNNReal', max_le_iff, abs_nonneg, and_self_iff]
/-
**Summable.tsum_ofReal_lt_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Summable.tsum_ofReal_lt_top {f : α -> Real} (hf : Summable f) : ∑' i, .ofR
eal (f i) < ∞
参数：hf : Summable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `ENNReal.tsum_coe_ne_top_iff_summable`：tsum_coe_ne_top_iff_summable {f : 
β -> Real>=0} : (∑' b, (f b : Real>=0∞)) != ∞ ↔ Summable f
· 使用定理 `Summable.toNNReal`：Summable.toNNReal {f : α -> Real} (hf : Summable f) :
 Summable fun n => (f n).toNNReal
-/
lemma Summable.tsum_ofReal_lt_top {f : α → ℝ} (hf : Summable f) : ∑' i, .ofReal (f i) < ∞ := by
  unfold ENNReal.ofReal
  rw [lt_top_iff_ne_top, ENNReal.tsum_coe_ne_top_iff_summable]
  exact hf.toNNReal
/-
**Summable.tsum_ofReal_ne_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Summable.tsum_ofReal_ne_top {f : α -> Real} (hf : Summable f) : ∑' i, .ofR
eal (f i) != ∞
参数：hf : Summable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `Summable.tsum_ofReal_lt_top`：Summable.tsum_ofReal_lt_top {f : α -> Real}
 (hf : Summable f) : ∑' i, .ofReal (f i) < ∞
-/
lemma Summable.tsum_ofReal_ne_top {f : α → ℝ} (hf : Summable f) : ∑' i, .ofReal (f i) ≠ ∞ :=
  hf.tsum_ofReal_lt_top.ne

/-- Finitely summable non-negative functions have countable support -/
/-
**_root_.Summable.countable_support_ennreal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：_root_.Summable.countable_support_ennreal {f : α -> Real>=0∞} (h : ∑' (i :
 α), f i != ∞) : f.support.Countable
参数：h : ∑' (i : α), f i != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Finitely summable non-negative functions have countable support
-/
theorem _root_.Summable.countable_support_ennreal {f : α → ℝ≥0∞} (h : ∑' (i : α), f i ≠ ∞) :
    f.support.Countable := by
  lift f to α → ℝ≥0 using ENNReal.ne_top_of_tsum_ne_top h
  simpa [support] using (ENNReal.tsum_coe_ne_top_iff_summable.1 h).countable_support_nnreal

/-- A series of non-negative real numbers converges to `r` in the sense of `HasSum` if and only if
the sequence of partial sum converges to `r`. -/
/-
**hasSum_iff_tendsto_nat_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasSum_iff_tendsto_nat_of_nonneg {f : Nat -> Real} (hf : forall i, 0 <= f 
i) (r : Real) : HasSum f r ↔ Tendsto (fun n : Nat => ∑ i in Finset.range n, f i)
 atTop (𝓝 r)
参数：hf : forall i, 0 <= f i；r : Real。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `NNReal.hasSum_iff_tendsto_nat`：hasSum_iff_tendsto_nat {f : Nat -> Real>=
0} {r : Real>=0} : HasSum f r ↔ Tendsto (fun n : Nat => ∑ i in Finset.range n, f
 i) atTop (𝓝 r)

--- 原说明 ---
A series of non-negative real numbers converges to `r` in the sense of `HasSum` 
if and only if
the sequence of partial sum converges to `r`.
-/
theorem hasSum_iff_tendsto_nat_of_nonneg {f : ℕ → ℝ} (hf : ∀ i, 0 ≤ f i) (r : ℝ) :
    HasSum f r ↔ Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop (𝓝 r) := by
  lift f to ℕ → ℝ≥0 using hf
  simp only [HasSum, ← NNReal.coe_sum, NNReal.tendsto_coe']
  exact exists_congr fun hr => NNReal.hasSum_iff_tendsto_nat
/-
**ENNReal.ofReal_tsum_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ENNReal.ofReal_tsum_of_nonneg {f : α -> Real} (hf_nonneg : forall n, 0 <= 
f n) (hf : Summable f) : ENNReal.ofReal (∑' n, f n) = ∑' n, ENNReal.ofReal (f n)
参数：hf_nonneg : forall n, 0 <= f n；hf : Summable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.tsum_coe_eq`：∀ {α : Type u_1} {r : NNReal} {f : α → NNReal}, Has
Sum f r → ∑' (a : α), ↑(f a) = ↑r
· 使用定理 `NNReal.hasSum_real_toNNReal_of_nonneg`：hasSum_real_toNNReal_of_nonneg {f
 : α -> Real} (hf_nonneg : forall n, 0 <= f n) (hf : Summable f L) : HasSum (fun
 n => Real.toNNReal (f n)) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ENNReal.ofReal_tsum_of_nonneg {f : α → ℝ} (hf_nonneg : ∀ n, 0 ≤ f n) (hf : Summable f) :
    ENNReal.ofReal (∑' n, f n) = ∑' n, ENNReal.ofReal (f n) := by
  simp_rw [ENNReal.ofReal, ENNReal.tsum_coe_eq (NNReal.hasSum_real_toNNReal_of_nonneg hf_nonneg hf)]

section tprod

/-
**ENNReal.multipliable_of_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ENNReal.multipliable_of_le_one {f : α -> Real>=0∞} (h₀ : forall i, f i <= 
1) : Multipliable f
参数：h₀ : forall i, f i <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasProd_of_isGLB_of_le_one`：hasProd_of_isGLB_of_le_one [CommMonoid α] [L
inearOrder α] [IsOrderedMonoid α] [TopologicalSpace α] [OrderTopology α] {f : ι 
-> α} (i : α) (h…
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `isGLB_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] (s : Set 
α), IsGLB s (sInf s)
-/
theorem ENNReal.multipliable_of_le_one {f : α → ℝ≥0∞} (h₀ : ∀ i, f i ≤ 1) :
    Multipliable f :=
  ⟨_, _root_.hasProd_of_isGLB_of_le_one _ h₀ (isGLB_sInf _)⟩
/-
**ENNReal.hasProd_iInf_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ENNReal.hasProd_iInf_prod {f : α -> Real>=0∞} (h₀ : forall i, f i <= 1) : 
HasProd f (⨅ s : Finset α, ∏ i in s, f i)
参数：h₀ : forall i, f i <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_atTop_iInf`：tendsto_atTop_iInf (h_anti : Antitone f) : Tendsto f
 atTop (𝓝 (⨅ i, f i))
· 使用定理 `LinearOrder.infConvergenceClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : LinearOrder α] [OrderTopology α], InfConvergenceClass α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `Finset.prod_anti_set_of_le_one'`：prod_anti_set_of_le_one' {ι : Type u_1}
 {N : Type u_5} [CommMonoid N] [Preorder N] {f : ι -> N} [MulLeftMono N] (hf : f
orall (x : ι), f x <=…
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
-/
theorem ENNReal.hasProd_iInf_prod {f : α → ℝ≥0∞} (h₀ : ∀ i, f i ≤ 1) :
    HasProd f (⨅ s : Finset α, ∏ i ∈ s, f i) :=
  tendsto_atTop_iInf (Finset.prod_anti_set_of_le_one' h₀)
/-
**ENNReal.tprod_eq_iInf_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ENNReal.tprod_eq_iInf_prod {f : α -> Real>=0∞} (h₀ : forall i, f i <= 1) :
 ∏' i, f i = ⨅ s : Finset α, ∏ i in s, f i
参数：h₀ : forall i, f i <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `ENNReal.hasProd_iInf_prod`：ENNReal.hasProd_iInf_prod {f : α -> Real>=0∞}
 (h₀ : forall i, f i <= 1) : HasProd f (⨅ s : Finset α, ∏ i in s, f i)
-/
theorem ENNReal.tprod_eq_iInf_prod {f : α → ℝ≥0∞} (h₀ : ∀ i, f i ≤ 1) :
    ∏' i, f i = ⨅ s : Finset α, ∏ i ∈ s, f i :=
  (hasProd_iInf_prod h₀).tprod_eq

end tprod

variable [PseudoEMetricSpace α]

/-- If the extended distance between consecutive points of a sequence is estimated
by a summable series of `NNReal`s, then the original sequence is a Cauchy sequence. -/
/-
**cauchySeq_of_edist_le_of_summable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchySeq_of_edist_le_of_summable {f : Nat -> α} (d : Nat -> Real>=0) (hf 
: forall n, edist (f n) (f n.succ) <= d n) (hd : Summable d) : CauchySeq f
参数：d : Nat -> Real>=0；hf : forall n, edist (f n) (f n.succ) <= d n；hd : Summable
 d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EMetric.cauchySeq_iff_NNReal`：cauchySeq_iff_NNReal [Nonempty β] [Semilat
ticeSup β] {u : β -> α} : CauchySeq u ↔ forall ε : Real>=0, 0 < ε -> exists N, f
orall n, N <= n ->…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Tendsto.cauchySeq`：Filter.Tendsto.cauchySeq [SemilatticeSup β] [N
onempty β] {f : β -> α} {x} (hx : Tendsto f atTop (𝓝 x)) : CauchySeq f
· 使用定理 `HasSum.tendsto_sum_nat`：∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_
1 : TopologicalSpace M] {m : M} {f : ℕ → M},   HasSum f m → Filter.Tendsto (fun 
n => ∑ i ∈ F…
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `edist_le_Ico_sum_of_edist_le`：edist_le_Ico_sum_of_edist_le {f : Nat -> α
} {m n} (hmn : m <= n) {d : Nat -> Real>=0∞} (hd : forall {k}, m <= k -> k < n -
> edist (f k) (f (…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `max_lt_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max b c <
 a ↔ b < a ∧ c < a
· 使用定理 `NNReal.coe_lt_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ < ↑r₂ ↔ r₁ < r₂
· 使用定理 `add_tsub_cancel_left`：add_tsub_cancel_left (a b : α) : a + b - a = b
· 使用定理 `NNReal.instOrderedSub`：OrderedSub NNReal
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Finset.sum_range_add_sum_Ico`：∀ {M : Type u_3} [inst : AddCommMonoid M] 
(f : ℕ → M) {m n : ℕ},   m ≤ n → ∑ k ∈ Finset.range m, f k + ∑ k ∈ Finset.Ico m 
n, f k = ∑ k ∈ Fin…
· 使用引理 `NNReal.nndist_eq`：NNReal.nndist_eq (a b : Real>=0) : nndist a b = max (a
 - b) (b - a)
· 使用定理 `dist_nndist`：dist_nndist (x y : α) : dist x y = nndist x y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.cauchySeq_iff'`：Metric.cauchySeq_iff' {u : β -> α} : CauchySeq u 
↔ forall ε > 0, exists N, forall n >= N, dist (u n) (u N) < ε
· 使用定理 `NNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r

--- 原说明 ---
If the extended distance between consecutive points of a sequence is estimated
by a summable series of `NNReal`s, then the original sequence is a Cauchy sequen
ce.
-/
theorem cauchySeq_of_edist_le_of_summable {f : ℕ → α} (d : ℕ → ℝ≥0)
    (hf : ∀ n, edist (f n) (f n.succ) ≤ d n) (hd : Summable d) : CauchySeq f := by
  refine EMetric.cauchySeq_iff_NNReal.2 fun ε εpos ↦ ?_
  -- Actually we need partial sums of `d` to be a Cauchy sequence.
  replace hd : CauchySeq fun n : ℕ ↦ ∑ x ∈ Finset.range n, d x :=
    let ⟨_, H⟩ := hd
    H.tendsto_sum_nat.cauchySeq
  -- Now we take the same `N` as in one of the definitions of a Cauchy sequence.
  refine (Metric.cauchySeq_iff'.1 hd ε (NNReal.coe_pos.2 εpos)).imp fun N hN n hn ↦ ?_
  specialize hN n hn
  -- We simplify the known inequality.
  rw [dist_nndist, NNReal.nndist_eq, ← Finset.sum_range_add_sum_Ico _ hn, add_tsub_cancel_left,
    NNReal.coe_lt_coe, max_lt_iff] at hN
  rw [edist_comm]
  -- Then use `hf` to simplify the goal to the same form.
  refine lt_of_le_of_lt (edist_le_Ico_sum_of_edist_le hn fun _ _ ↦ hf _) ?_
  exact mod_cast hN.1
/-
**cauchySeq_of_edist_le_of_tsum_ne_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchySeq_of_edist_le_of_tsum_ne_top {f : Nat -> α} (d : Nat -> Real>=0∞) 
(hf : forall n, edist (f n) (f n.succ) <= d n) (hd : tsum d != ∞) : CauchySeq f
参数：d : Nat -> Real>=0∞；hf : forall n, edist (f n) (f n.succ) <= d n；hd : tsum d 
!= ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `ENNReal.ne_top_of_tsum_ne_top`：∀ {α : Type u_1} {f : α → ENNReal}, ∑' (a
 : α), f a ≠ ⊤ → ∀ (a : α), f a ≠ ⊤
· 使用定理 `cauchySeq_of_edist_le_of_summable`：cauchySeq_of_edist_le_of_summable {f 
: Nat -> α} (d : Nat -> Real>=0) (hf : forall n, edist (f n) (f n.succ) <= d n) 
(hd : Summable d) : Cau…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.tsum_coe_ne_top_iff_summable`：tsum_coe_ne_top_iff_summable {f : 
β -> Real>=0} : (∑' b, (f b : Real>=0∞)) != ∞ ↔ Summable f
-/
theorem cauchySeq_of_edist_le_of_tsum_ne_top {f : ℕ → α} (d : ℕ → ℝ≥0∞)
    (hf : ∀ n, edist (f n) (f n.succ) ≤ d n) (hd : tsum d ≠ ∞) : CauchySeq f := by
  lift d to ℕ → NNReal using fun i => ENNReal.ne_top_of_tsum_ne_top hd i
  rw [ENNReal.tsum_coe_ne_top_iff_summable] at hd
  exact cauchySeq_of_edist_le_of_summable d hf hd

/-- If `edist (f n) (f (n+1))` is bounded above by a function `d : ℕ → ℝ≥0∞`,
then the distance from `f n` to the limit is bounded by `∑'_{k=n}^∞ d k`. -/
/-
**edist_le_tsum_of_edist_le_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_le_tsum_of_edist_le_of_tendsto {f : Nat -> α} (d : Nat -> Real>=0∞) 
(hf : forall n, edist (f n) (f n.succ) <= d n) {a : α} (ha : Tendsto f atTop (𝓝 
a)) (n : Nat) : edist (f n) a <= ∑' m, d (n + m)
参数：d : Nat -> Real>=0∞；hf : forall n, edist (f n) (f n.succ) <= d n；ha : Tendsto
 f atTop (𝓝 a)；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_tendsto`：le_of_tendsto {x : Filter β} [hx : NeBot x] (lim : Tendst
o f x (𝓝 a)) (h : forallᶠ c in x, f c <= b) : a <= b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Tendsto.edist`：Filter.Tendsto.edist {f g : β -> α} {x : Filter β}
 {a b : α} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (fun x =>
 edist (f …
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.mem_atTop_sets`：mem_atTop_sets {s : Set α} : s in (atTop : Filter
 α) ↔ exists a : α, forall b, a <= b -> b in s
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `edist_le_Ico_sum_of_edist_le`：edist_le_Ico_sum_of_edist_le {f : Nat -> α
} {m n} (hmn : m <= n) {d : Nat -> Real>=0∞} (hd : forall {k}, m <= k -> k < n -
> edist (f k) (f (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_Ico_eq_sum_range`：∀ {M : Type u_3} [inst : AddCommMonoid M] (
f : ℕ → M) (m n : ℕ),   ∑ k ∈ Finset.Ico m n, f k = ∑ k ∈ Finset.range (n - m), 
f (m + k)
· 使用定理 `Summable.sum_le_tsum`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilt
er ι} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [i
nst_3 : To…
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f

--- 原说明 ---
If `edist (f n) (f (n+1))` is bounded above by a function `d : ℕ → ℝ≥0∞`,
then the distance from `f n` to the limit is bounded by `∑'_{k=n}^∞ d k`.
-/
theorem edist_le_tsum_of_edist_le_of_tendsto {f : ℕ → α} (d : ℕ → ℝ≥0∞)
    (hf : ∀ n, edist (f n) (f n.succ) ≤ d n) {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : ℕ) :
    edist (f n) a ≤ ∑' m, d (n + m) := by
  refine le_of_tendsto (tendsto_const_nhds.edist ha) (mem_atTop_sets.2 ⟨n, fun m hnm => ?_⟩)
  change edist _ _ ≤ _
  refine le_trans (edist_le_Ico_sum_of_edist_le hnm fun _ _ => hf _) ?_
  rw [Finset.sum_Ico_eq_sum_range]
  exact ENNReal.summable.sum_le_tsum _ (fun _ _ => zero_le)

/-- If `edist (f n) (f (n+1))` is bounded above by a function `d : ℕ → ℝ≥0∞`,
then the distance from `f 0` to the limit is bounded by `∑'_{k=0}^∞ d k`. -/
/-
**edist_le_tsum_of_edist_le_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_le_tsum_of_edist_le_of_tendsto {f : Nat -> α} (d : Nat -> Real>=0∞) 
(hf : forall n, edist (f n) (f n.succ) <= d n) {a : α} (ha : Tendsto f atTop (𝓝 
a)) (n : Nat) : edist (f n) a <= ∑' m, d (n + m)
参数：d : Nat -> Real>=0∞；hf : forall n, edist (f n) (f n.succ) <= d n；ha : Tendsto
 f atTop (𝓝 a)；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_tendsto`：le_of_tendsto {x : Filter β} [hx : NeBot x] (lim : Tendst
o f x (𝓝 a)) (h : forallᶠ c in x, f c <= b) : a <= b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Tendsto.edist`：Filter.Tendsto.edist {f g : β -> α} {x : Filter β}
 {a b : α} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (fun x =>
 edist (f …
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.mem_atTop_sets`：mem_atTop_sets {s : Set α} : s in (atTop : Filter
 α) ↔ exists a : α, forall b, a <= b -> b in s
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `edist_le_Ico_sum_of_edist_le`：edist_le_Ico_sum_of_edist_le {f : Nat -> α
} {m n} (hmn : m <= n) {d : Nat -> Real>=0∞} (hd : forall {k}, m <= k -> k < n -
> edist (f k) (f (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_Ico_eq_sum_range`：∀ {M : Type u_3} [inst : AddCommMonoid M] (
f : ℕ → M) (m n : ℕ),   ∑ k ∈ Finset.Ico m n, f k = ∑ k ∈ Finset.range (n - m), 
f (m + k)
· 使用定理 `Summable.sum_le_tsum`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilt
er ι} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [i
nst_3 : To…
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f

--- 原说明 ---
If `edist (f n) (f (n+1))` is bounded above by a function `d : ℕ → ℝ≥0∞`,
then the distance from `f 0` to the limit is bounded by `∑'_{k=0}^∞ d k`.
-/
theorem edist_le_tsum_of_edist_le_of_tendsto₀ {f : ℕ → α} (d : ℕ → ℝ≥0∞)
    (hf : ∀ n, edist (f n) (f n.succ) ≤ d n) {a : α} (ha : Tendsto f atTop (𝓝 a)) :
    edist (f 0) a ≤ ∑' m, d m := by simpa using edist_le_tsum_of_edist_le_of_tendsto d hf ha 0


namespace ENNReal

variable {α : Type*} (s : Set α)

/-
**ENNReal.tsum_set_one** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：tsum_set_one : ∑' _ : s, (1 : Real>=0∞) = s.encard
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_or_infinite`：∀ {α : Type u} (s : Set α), s.Finite ∨ s.Infinit
e
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] [inst_3 : Fin
ty…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.card_attach`：card_attach : #s.attach = #s
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Set.encard_coe_eq_coe_finsetCard`：∀ {α : Type u_1} (s : Finset α), (↑s).
encard = ↑s.card
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.infinite_coe_iff`：infinite_coe_iff {s : Set α} : Infinite s ↔ s.Infi
nite
· 使用定理 `ENNReal.tsum_const_eq_top_of_ne_zero`：tsum_const_eq_top_of_ne_zero {α : 
Type*} [Infinite α] {c : Real>=0∞} (hc : c != 0) : ∑' _ : α, c = ∞
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
· 使用定理 `Set.encard_eq_top`：∀ {α : Type u_1} {s : Set α}, s.Infinite → s.encard =
 ⊤
· 使用定理 `ENat.toENNReal_top`：toENNReal_top : ((⊤ : Nat∞) : Real>=0∞) = ⊤
-/
lemma tsum_set_one : ∑' _ : s, (1 : ℝ≥0∞) = s.encard := by
  obtain (hfin | hinf) := Set.finite_or_infinite s
  · lift s to Finset α using hfin
    simp [tsum_fintype]
  · have : Infinite s := infinite_coe_iff.mpr hinf
    rw [tsum_const_eq_top_of_ne_zero one_ne_zero, encard_eq_top hinf, ENat.toENNReal_top]
/-
**ENNReal.tsum_set_const** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：tsum_set_const (c : Real>=0∞) : ∑' _ : s, c = s.encard * c
参数：c : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tsum_set_const (c : ℝ≥0∞) : ∑' _ : s, c = s.encard * c := by
  simp [← tsum_set_one, ← ENNReal.tsum_mul_right]

@[simp]
/-
**ENNReal.tsum_one** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：tsum_one : ∑' _ : α, (1 : Real>=0∞) = ENat.card α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsum_univ`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] (f : β → α),   ∑' (x : ↑Set.univ), f ↑x = ∑' (x : β),…
· 使用定理 `Set.encard_univ`：∀ (α : Type u_3), Set.univ.encard = ENat.card α
· 使用引理 `ENNReal.tsum_set_one`：tsum_set_one : ∑' _ : s, (1 : Real>=0∞) = s.encard
-/
lemma tsum_one : ∑' _ : α, (1 : ℝ≥0∞) = ENat.card α := by
  rw [← tsum_univ]; simpa [encard_univ] using tsum_set_one univ

@[simp]
/-
**ENNReal.tsum_const** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：tsum_const (c : Real>=0∞) : ∑' _ : α, c = ENat.card α * c
参数：c : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsum_univ`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] (f : β → α),   ∑' (x : ↑Set.univ), f ↑x = ∑' (x : β),…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.encard_univ`：∀ (α : Type u_3), Set.univ.encard = ENat.card α
· 使用引理 `ENNReal.tsum_set_const`：tsum_set_const (c : Real>=0∞) : ∑' _ : s, c = s.
encard * c
-/
lemma tsum_const (c : ℝ≥0∞) : ∑' _ : α, c = ENat.card α * c := by
  rw [← tsum_univ]; simpa [encard_univ] using tsum_set_const univ c

end ENNReal

