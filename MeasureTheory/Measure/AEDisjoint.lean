/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Almost everywhere disjoint sets

We say that sets `s` and `t` are `μ`-a.e. disjoint (see `MeasureTheory.AEDisjoint`) if their
intersection has measure zero. This assumption can be used instead of `Disjoint` in most theorems in
measure theory.
-/

@[expose] public section


open Set Function

namespace MeasureTheory

variable {ι α : Type*} {m : MeasurableSpace α} (μ : Measure α)

/-- Two sets are said to be `μ`-a.e. disjoint if their intersection has measure zero. -/
/-
**MeasureTheory.AEDisjoint** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：AEDisjoint (s t : Set α)
参数：s t : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two sets are said to be `μ`-a.e. disjoint if their intersection has measure zero
.
-/
def AEDisjoint (s t : Set α) :=
  μ (s ∩ t) = 0

variable {μ} {s t u v : Set α}

/-- If `s : ι → Set α` is a countable family of pairwise a.e. disjoint sets, then there exists a
family of measurable null sets `t i` such that `s i \ t i` are pairwise disjoint. -/
/-
**MeasureTheory.exists_null_pairwise_disjoint_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：exists_null_pairwise_disjoint_sdiff [Countable ι] {s : ι -> Set α} (hd : P
airwise (AEDisjoint μ on s)) : exists t : ι -> Set α, (forall i, MeasurableSet (
t i)) ∧ (forall i, μ (t i) = 0) ∧ Pairwise (Disjoint on fun i => s i \ t i)
参数：hd : Pairwise (AEDisjoint μ on s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.measure_biUnion_null_iff`：measure_biUnion_null_iff {I : Se
t ι} (hI : I.Countable) {s : ι -> Set α} : μ (⋃ i in I, s i) = 0 ↔ forall i in I
, μ (s i) = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `SetCoe.countable`：∀ {α : Type u} [Countable α] (s : Set α), Countable ↑s
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s

--- 原说明 ---
If `s : ι → Set α` is a countable family of pairwise a.e. disjoint sets, then th
ere exists a
family of measurable null sets `t i` such that `s i \ t i` are pairwise disjoint
.
-/
theorem exists_null_pairwise_disjoint_sdiff [Countable ι] {s : ι → Set α}
    (hd : Pairwise (AEDisjoint μ on s)) : ∃ t : ι → Set α, (∀ i, MeasurableSet (t i)) ∧
    (∀ i, μ (t i) = 0) ∧ Pairwise (Disjoint on fun i => s i \ t i) := by
  refine ⟨fun i => toMeasurable μ (s i ∩ ⋃ j ∈ ({i}ᶜ : Set ι), s j), fun i =>
    measurableSet_toMeasurable _ _, fun i => ?_, ?_⟩
  · simp only [measure_toMeasurable, inter_iUnion]
    exact (measure_biUnion_null_iff <| to_countable _).2 fun j hj => hd (Ne.symm hj)
  · simp only [Pairwise, disjoint_left, onFun, mem_sdiff, not_and, and_imp, Classical.not_not]
    intro i j hne x hi hU hj
    replace hU : x ∉ s i ∩ iUnion fun j ↦ iUnion fun _ ↦ s j :=
      fun h ↦ hU (subset_toMeasurable _ _ h)
    simp only [mem_inter_iff, mem_iUnion, not_and, not_exists] at hU
    exact (hU hi j hne.symm hj).elim

@[deprecated (since := "2026-06-03")]
alias exists_null_pairwise_disjoint_diff := exists_null_pairwise_disjoint_sdiff

namespace AEDisjoint

/-
**MeasureTheory.AEDisjoint.eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEDisjoin
t`。
形式化陈述：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {s 
t : Set α},   MeasureTheory.AEDisjoint μ s t → μ (s ∩ t) = 0
参数：s ∩ t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem eq (h : AEDisjoint μ s t) : μ (s ∩ t) = 0 :=
  h

@[symm]
/-
**MeasureTheory.AEDisjoint.symm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEDisjo
int`。
形式化陈述：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {s 
t : Set α},   MeasureTheory.AEDisjoint μ s t → MeasureTheory.AEDisjoint μ t s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.AEDisjoint.eq_1`：∀ {α : Type u_2} {m : MeasurableSpace α} 
(μ : MeasureTheory.Measure α) (s t : Set α),   MeasureTheory.AEDisjoint μ s t = 
(μ (s ∩ t) = 0)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
-/
protected theorem symm (h : AEDisjoint μ s t) : AEDisjoint μ t s := by rwa [AEDisjoint, inter_comm]
/-
**MeasureTheory.AEDisjoint.stdSymm** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.AEDi
sjoint`。
形式化陈述：stdSymm : Std.Symm (AEDisjoint μ) where symm _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEDisjoint.symm`：∀ {α : Type u_2} {m : MeasurableSpace α} 
{μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.AEDisjoint μ s t → 
MeasureTheory.AEDis…
-/
instance stdSymm : Std.Symm (AEDisjoint μ) where
  symm _ _ := AEDisjoint.symm

@[deprecated (since := "2026-06-10")] protected alias symmetric := AEDisjoint.stdSymm
/-
**MeasureTheory.AEDisjoint.comm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEDisjo
int`。
形式化陈述：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {s 
t : Set α},   MeasureTheory.AEDisjoint μ s t ↔ MeasureTheory.AEDisjoint μ t s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEDisjoint.symm`：∀ {α : Type u_2} {m : MeasurableSpace α} 
{μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.AEDisjoint μ s t → 
MeasureTheory.AEDis…
-/
protected theorem comm : AEDisjoint μ s t ↔ AEDisjoint μ t s :=
  ⟨AEDisjoint.symm, AEDisjoint.symm⟩
/-
**MeasureTheory.AEDisjoint._root_.Disjoint.aedisjoint** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.AEDisjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.Disjoint.aedisjoint (h : Disjoint s t) : AEDisjoint μ s t := by
  rw [AEDisjoint, disjoint_iff_inter_eq_empty.1 h, measure_empty]
/-
**MeasureTheory.AEDisjoint._root_.Pairwise.aedisjoint** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.AEDisjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.Pairwise.aedisjoint {f : ι → Set α} (hf : Pairwise (Disjoint on f)) :
    Pairwise (AEDisjoint μ on f) :=
  hf.mono fun _i _j h => h.aedisjoint
/-
**MeasureTheory.AEDisjoint._root_.Set.PairwiseDisjoint.aedisjoint** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory.AEDisjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.Set.PairwiseDisjoint.aedisjoint {f : ι → Set α} {s : Set ι}
    (hf : s.PairwiseDisjoint f) : s.Pairwise (AEDisjoint μ on f) :=
  hf.mono' fun _i _j h => h.aedisjoint
/-
**MeasureTheory.AEDisjoint.mono_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEDi
sjoint`。
形式化陈述：mono_ae (h : AEDisjoint μ s t) (hu : u <=ᵐ[μ] s) (hv : v <=ᵐ[μ] t) : AEDis
joint μ u v
参数：h : AEDisjoint μ s t；hu : u <=ᵐ[μ] s；hv : v <=ᵐ[μ] t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.measure_mono_null_ae`：measure_mono_null_ae (H : s <=ᵐ[μ] t
) (ht : μ t = 0) : μ s = 0
· 使用定理 `Filter.EventuallyLE.inter`：∀ {α : Type u} {s t s' t' : Set α} {l : Filte
r α}, s ≤ᶠ[l] t → s' ≤ᶠ[l] t' → s ∩ s' ≤ᶠ[l] t ∩ t'
-/
theorem mono_ae (h : AEDisjoint μ s t) (hu : u ≤ᵐ[μ] s) (hv : v ≤ᵐ[μ] t) : AEDisjoint μ u v :=
  measure_mono_null_ae (hu.inter hv) h
/-
**MeasureTheory.AEDisjoint.mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEDisjo
int`。
形式化陈述：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {s 
t u v : Set α},   MeasureTheory.AEDisjoint μ s t → u ⊆ s → v ⊆ t → MeasureTheory
.AEDisjoint μ u v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEDisjoint.mono_ae`：mono_ae (h : AEDisjoint μ s t) (hu : u
 <=ᵐ[μ] s) (hv : v <=ᵐ[μ] t) : AEDisjoint μ u v
· 使用定理 `LE.le.eventuallyLE`：LE.le.eventuallyLE {α} {l : Filter α} {s t : Set α} 
(h : s subseteq t) : s <=ᶠ[l] t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
protected theorem mono (h : AEDisjoint μ s t) (hu : u ⊆ s) (hv : v ⊆ t) : AEDisjoint μ u v :=
  mono_ae h (LE.le.eventuallyLE hu) (LE.le.eventuallyLE hv)
/-
**MeasureTheory.AEDisjoint.congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEDisj
oint`。
形式化陈述：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {s 
t u v : Set α},   MeasureTheory.AEDisjoint μ s t → u =ᵐ[μ] s → v =ᵐ[μ] t → Measu
reTheory.AEDisjoint μ u v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEDisjoint.mono_ae`：mono_ae (h : AEDisjoint μ s t) (hu : u
 <=ᵐ[μ] s) (hv : v <=ᵐ[μ] t) : AEDisjoint μ u v
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
-/
protected theorem congr (h : AEDisjoint μ s t) (hu : u =ᵐ[μ] s) (hv : v =ᵐ[μ] t) :
    AEDisjoint μ u v :=
  mono_ae h (Filter.EventuallyEq.le hu) (Filter.EventuallyEq.le hv)

@[simp]
/-
**MeasureTheory.AEDisjoint.iUnion_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.AEDisjoint`。
形式化陈述：iUnion_left_iff {ι : Sort*} [Countable ι] {s : ι -> Set α} : AEDisjoint μ 
(⋃ i, s i) t ↔ forall i, AEDisjoint μ (s i) t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_inter`：iUnion_inter (s : Set β) (t : ι -> Set β) : (⋃ i, t i)
 inter s = ⋃ i, t i inter s
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iUnion_left_iff {ι : Sort*} [Countable ι] {s : ι → Set α} :
    AEDisjoint μ (⋃ i, s i) t ↔ ∀ i, AEDisjoint μ (s i) t := by
  simp only [AEDisjoint, iUnion_inter, measure_iUnion_null_iff]

@[simp]
/-
**MeasureTheory.AEDisjoint.iUnion_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.AEDisjoint`。
形式化陈述：iUnion_right_iff {ι : Sort*} [Countable ι] {t : ι -> Set α} : AEDisjoint μ
 s (⋃ i, t i) ↔ forall i, AEDisjoint μ s (t i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iUnion_right_iff {ι : Sort*} [Countable ι] {t : ι → Set α} :
    AEDisjoint μ s (⋃ i, t i) ↔ ∀ i, AEDisjoint μ s (t i) := by
  simp only [AEDisjoint, inter_iUnion, measure_iUnion_null_iff]

@[simp]
/-
**MeasureTheory.AEDisjoint.union_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.AEDisjoint`。
形式化陈述：union_left_iff : AEDisjoint μ (s union t) u ↔ AEDisjoint μ s u ∧ AEDisjoin
t μ t u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_eq_iUnion`：union_eq_iUnion {s₁ s₂ : Set α} : s₁ union s₂ = ⋃ b
 : Bool, cond b s₁ s₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem union_left_iff : AEDisjoint μ (s ∪ t) u ↔ AEDisjoint μ s u ∧ AEDisjoint μ t u := by
  simp [union_eq_iUnion, and_comm]

@[simp]
/-
**MeasureTheory.AEDisjoint.union_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.AEDisjoint`。
形式化陈述：union_right_iff : AEDisjoint μ s (t union u) ↔ AEDisjoint μ s t ∧ AEDisjoi
nt μ s u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_eq_iUnion`：union_eq_iUnion {s₁ s₂ : Set α} : s₁ union s₂ = ⋃ b
 : Bool, cond b s₁ s₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem union_right_iff : AEDisjoint μ s (t ∪ u) ↔ AEDisjoint μ s t ∧ AEDisjoint μ s u := by
  simp [union_eq_iUnion, and_comm]
/-
**MeasureTheory.AEDisjoint.union_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.A
EDisjoint`。
形式化陈述：union_left (hs : AEDisjoint μ s u) (ht : AEDisjoint μ t u) : AEDisjoint μ 
(s union t) u
参数：hs : AEDisjoint μ s u；ht : AEDisjoint μ t u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.AEDisjoint.union_left_iff`：union_left_iff : AEDisjoint μ (
s union t) u ↔ AEDisjoint μ s u ∧ AEDisjoint μ t u
-/
theorem union_left (hs : AEDisjoint μ s u) (ht : AEDisjoint μ t u) : AEDisjoint μ (s ∪ t) u :=
  union_left_iff.mpr ⟨hs, ht⟩
/-
**MeasureTheory.AEDisjoint.union_right** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
AEDisjoint`。
形式化陈述：union_right (ht : AEDisjoint μ s t) (hu : AEDisjoint μ s u) : AEDisjoint μ
 s (t union u)
参数：ht : AEDisjoint μ s t；hu : AEDisjoint μ s u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.AEDisjoint.union_right_iff`：union_right_iff : AEDisjoint μ
 s (t union u) ↔ AEDisjoint μ s t ∧ AEDisjoint μ s u
-/
theorem union_right (ht : AEDisjoint μ s t) (hu : AEDisjoint μ s u) : AEDisjoint μ s (t ∪ u) :=
  union_right_iff.2 ⟨ht, hu⟩
/-
**MeasureTheory.AEDisjoint.sdiff_ae_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.AEDisjoint`。
形式化陈述：sdiff_ae_eq_left (h : AEDisjoint μ s t) : (s \ t : Set α) =ᵐ[μ] s
参数：h : AEDisjoint μ s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.sdiff_null_ae_eq_self`：sdiff_null_ae_eq_self (ht : μ t = 0
) : (s \ t : Set α) =ᵐ[μ] s
· 使用定理 `Set.sdiff_self_inter`：sdiff_self_inter {s t : Set α} : s \ (s inter t) =
 s \ t
-/
theorem sdiff_ae_eq_left (h : AEDisjoint μ s t) : (s \ t : Set α) =ᵐ[μ] s :=
  @sdiff_self_inter _ s t ▸ sdiff_null_ae_eq_self h

@[deprecated (since := "2026-06-03")] alias diff_ae_eq_left := sdiff_ae_eq_left
/-
**MeasureTheory.AEDisjoint.sdiff_ae_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.AEDisjoint`。
形式化陈述：sdiff_ae_eq_right (h : AEDisjoint μ s t) : (t \ s : Set α) =ᵐ[μ] t
参数：h : AEDisjoint μ s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEDisjoint.sdiff_ae_eq_left`：sdiff_ae_eq_left (h : AEDisjo
int μ s t) : (s \ t : Set α) =ᵐ[μ] s
· 使用定理 `MeasureTheory.AEDisjoint.symm`：∀ {α : Type u_2} {m : MeasurableSpace α} 
{μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.AEDisjoint μ s t → 
MeasureTheory.AEDis…
-/
theorem sdiff_ae_eq_right (h : AEDisjoint μ s t) : (t \ s : Set α) =ᵐ[μ] t :=
  sdiff_ae_eq_left <| AEDisjoint.symm h

@[deprecated (since := "2026-06-03")] alias diff_ae_eq_right := sdiff_ae_eq_right
/-
**MeasureTheory.AEDisjoint.measure_sdiff_left** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.AEDisjoint`。
形式化陈述：measure_sdiff_left (h : AEDisjoint μ s t) : μ (s \ t) = μ s
参数：h : AEDisjoint μ s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEDisjoint.sdiff_ae_eq_left`：sdiff_ae_eq_left (h : AEDisjo
int μ s t) : (s \ t : Set α) =ᵐ[μ] s
-/
theorem measure_sdiff_left (h : AEDisjoint μ s t) : μ (s \ t) = μ s :=
  measure_congr <| AEDisjoint.sdiff_ae_eq_left h

@[deprecated (since := "2026-06-03")] alias measure_diff_left := measure_sdiff_left
/-
**MeasureTheory.AEDisjoint.measure_sdiff_right** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.AEDisjoint`。
形式化陈述：measure_sdiff_right (h : AEDisjoint μ s t) : μ (t \ s) = μ t
参数：h : AEDisjoint μ s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEDisjoint.sdiff_ae_eq_right`：sdiff_ae_eq_right (h : AEDis
joint μ s t) : (t \ s : Set α) =ᵐ[μ] t
-/
theorem measure_sdiff_right (h : AEDisjoint μ s t) : μ (t \ s) = μ t :=
  measure_congr <| AEDisjoint.sdiff_ae_eq_right h

@[deprecated (since := "2026-06-03")] alias measure_diff_right := measure_sdiff_right

/-- If `s` and `t` are `μ`-a.e. disjoint, then `s \ u` and `t` are disjoint for some measurable null
set `u`. -/
/-
**MeasureTheory.AEDisjoint.exists_disjoint_diff** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.AEDisjoint`。
形式化陈述：exists_disjoint_diff (h : AEDisjoint μ s t) : exists u, MeasurableSet u ∧ 
μ u = 0 ∧ Disjoint (s \ u) t
参数：h : AEDisjoint μ s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用定理 `disjoint_sdiff_self_left`：disjoint_sdiff_self_left : Disjoint (y \ x) x

--- 原说明 ---
If `s` and `t` are `μ`-a.e. disjoint, then `s \ u` and `t` are disjoint for some
 measurable null
set `u`.
-/
theorem exists_disjoint_diff (h : AEDisjoint μ s t) :
    ∃ u, MeasurableSet u ∧ μ u = 0 ∧ Disjoint (s \ u) t :=
  ⟨toMeasurable μ (s ∩ t), measurableSet_toMeasurable _ _, (measure_toMeasurable _).trans h,
    disjoint_sdiff_self_left.mono_left (b := s \ t) fun x hx => by
      simpa using ⟨hx.1, fun hxt => hx.2 <| subset_toMeasurable _ _ ⟨hx.1, hxt⟩⟩⟩
/-
**MeasureTheory.AEDisjoint.of_null_right** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.AEDisjoint`。
形式化陈述：of_null_right (h : μ t = 0) : AEDisjoint μ s t
参数：h : μ t = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem of_null_right (h : μ t = 0) : AEDisjoint μ s t :=
  measure_mono_null inter_subset_right h
/-
**MeasureTheory.AEDisjoint.of_null_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.AEDisjoint`。
形式化陈述：of_null_left (h : μ s = 0) : AEDisjoint μ s t
参数：h : μ s = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEDisjoint.symm`：∀ {α : Type u_2} {m : MeasurableSpace α} 
{μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.AEDisjoint μ s t → 
MeasureTheory.AEDis…
· 使用定理 `MeasureTheory.AEDisjoint.of_null_right`：of_null_right (h : μ t = 0) : AE
Disjoint μ s t
-/
theorem of_null_left (h : μ s = 0) : AEDisjoint μ s t :=
  AEDisjoint.symm (of_null_right h)

end AEDisjoint

/-
**MeasureTheory.aedisjoint_compl_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aedisjoint_compl_left : AEDisjoint μ sᶜ s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t
· 使用定理 `disjoint_compl_left`：disjoint_compl_left : Disjoint aᶜ a
-/
theorem aedisjoint_compl_left : AEDisjoint μ sᶜ s :=
  (@disjoint_compl_left _ _ s).aedisjoint
/-
**MeasureTheory.aedisjoint_compl_right** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：aedisjoint_compl_right : AEDisjoint μ s sᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
-/
theorem aedisjoint_compl_right : AEDisjoint μ s sᶜ :=
  (@disjoint_compl_right _ _ s).aedisjoint

end MeasureTheory

