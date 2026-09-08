/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Tactic.Group
public import Mathlib.Topology.UrysohnsLemma

/-!
# Everywhere positive sets in measure spaces

A set `s` in a topological space with a measure `μ` is *everywhere positive* (also called
*self-supporting*) if any neighborhood `n` of any point of `s` satisfies `μ (s ∩ n) > 0`.

## Main definitions and results

* `μ.IsEverywherePos s` registers that, for any point in `s`, all its neighborhoods have positive
  measure inside `s`.
* `μ.everywherePosSubset s` is the subset of `s` made of those points all of whose neighborhoods
  have positive measure inside `s`.
* `everywherePosSubset_ae_eq` shows that `s` and `μ.everywherePosSubset s` coincide almost
  everywhere if `μ` is inner regular and `s` is measurable.
* `isEverywherePos_everywherePosSubset` shows that `μ.everywherePosSubset s` satisfies the property
  `μ.IsEverywherePos` if `μ` is inner regular and `s` is measurable.

The latter two statements have also versions when `μ` is inner regular for finite measure sets,
assuming additionally that `s` has finite measure.

* `IsEverywherePos.IsGδ` proves that an everywhere positive compact closed set is a Gδ set,
  in a topological group with a left-invariant measure. This is a nontrivial statement, used
  crucially in the study of the uniqueness of Haar measures.
* `innerRegularWRT_preimage_one_hasCompactSupport_measure_ne_top`: for a Haar measure, any
  finite measure set can be approximated from inside by level sets of continuous
  compactly supported functions. This property is also known as completion-regularity of Haar
  measures.
-/

@[expose] public section

open scoped Topology ENNReal NNReal
open Set Filter

namespace MeasureTheory.Measure

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]

/-- A set `s` is *everywhere positive* (also called *self-supporting*) with respect to a
measure `μ` if it has positive measure around each of its points, i.e., if all neighborhoods `n`
of points of `s` satisfy `μ (s ∩ n) > 0`. -/
/-
**MeasureTheory.Measure.IsEverywherePos** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：IsEverywherePos (μ : Measure α) (s : Set α) : Prop
参数：μ : Measure α；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s` is *everywhere positive* (also called *self-supporting*) with respect 
to a
measure `μ` if it has positive measure around each of its points, i.e., if all n
eighborhoods `n`
of points of `s` satisfy `μ (s ∩ n) > 0`.
-/
def IsEverywherePos (μ : Measure α) (s : Set α) : Prop :=
  ∀ x ∈ s, ∀ n ∈ 𝓝[s] x, 0 < μ n

/-- The everywhere positive subset of a set is the subset made of those points all of whose
neighborhoods have positive measure inside the set. -/
/-
**MeasureTheory.Measure.everywherePosSubset** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：everywherePosSubset (μ : Measure α) (s : Set α) : Set α
参数：μ : Measure α；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The everywhere positive subset of a set is the subset made of those points all o
f whose
neighborhoods have positive measure inside the set.
-/
def everywherePosSubset (μ : Measure α) (s : Set α) : Set α :=
  {x | x ∈ s ∧ ∀ n ∈ 𝓝[s] x, 0 < μ n}
/-
**MeasureTheory.Measure.everywherePosSubset_subset** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：everywherePosSubset_subset (μ : Measure α) (s : Set α) : μ.everywherePosSu
bset s subseteq s
参数：μ : Measure α；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma everywherePosSubset_subset (μ : Measure α) (s : Set α) : μ.everywherePosSubset s ⊆ s :=
  fun _x hx ↦ hx.1

/-- The everywhere positive subset of a set is obtained by removing an open set. -/
/-
**MeasureTheory.Measure.exists_isOpen_everywherePosSubset_eq_sdiff** 是 Mathlib 中
的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：exists_isOpen_everywherePosSubset_eq_sdiff (μ : Measure α) (s : Set α) : e
xists u, IsOpen u ∧ μ.everywherePosSubset s = s \ u
参数：μ : Measure α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsWithin_iff_exists_mem_nhds_inter`：mem_nhdsWithin_iff_exists_mem_
nhds_inter {t : Set α} {a : α} {s : Set α} : t in 𝓝[s] a ↔ exists u in 𝓝 a, u in
ter s subseteq t
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.inter_subset_inter_left`：inter_subset_inter_left {s t : Set α} (u : 
Set α) (H : s subseteq t) : s inter u subseteq t inter u
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The everywhere positive subset of a set is obtained by removing an open set.
-/
lemma exists_isOpen_everywherePosSubset_eq_sdiff (μ : Measure α) (s : Set α) :
    ∃ u, IsOpen u ∧ μ.everywherePosSubset s = s \ u := by
  refine ⟨{x | ∃ n ∈ 𝓝[s] x, μ n = 0}, ?_, by ext x; simp [everywherePosSubset, pos_iff_ne_zero]⟩
  rw [isOpen_iff_mem_nhds]
  intro x ⟨n, ns, hx⟩
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 ns with ⟨v, vx, hv⟩
  rcases mem_nhds_iff.1 vx with ⟨w, wv, w_open, xw⟩
  have A : w ⊆ {x | ∃ n ∈ 𝓝[s] x, μ n = 0} := by
    intro y yw
    refine ⟨s ∩ w, inter_mem_nhdsWithin _ (w_open.mem_nhds yw), measure_mono_null ?_ hx⟩
    rw [inter_comm]
    exact (inter_subset_inter_left _ wv).trans hv
  have B : w ∈ 𝓝 x := w_open.mem_nhds xw
  exact mem_of_superset B A

@[deprecated (since := "2026-06-03")]
alias exists_isOpen_everywherePosSubset_eq_diff := exists_isOpen_everywherePosSubset_eq_sdiff

variable {μ ν : Measure α} {s k : Set α}
/-
**MeasureTheory.Measure._root_.MeasurableSet.everywherePosSubset** 是 Mathlib 中的一
个引理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma _root_.MeasurableSet.everywherePosSubset [OpensMeasurableSpace α]
    (hs : MeasurableSet s) :
    MeasurableSet (μ.everywherePosSubset s) := by
  rcases exists_isOpen_everywherePosSubset_eq_sdiff μ s with ⟨u, u_open, hu⟩
  rw [hu]
  exact hs.diff u_open.measurableSet
/-
**MeasureTheory.Measure._root_.IsClosed.everywherePosSubset** 是 Mathlib 中的一个引理，位
于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma _root_.IsClosed.everywherePosSubset (hs : IsClosed s) :
    IsClosed (μ.everywherePosSubset s) := by
  rcases exists_isOpen_everywherePosSubset_eq_sdiff μ s with ⟨u, u_open, hu⟩
  rw [hu]
  exact hs.sdiff u_open
/-
**MeasureTheory.Measure._root_.IsCompact.everywherePosSubset** 是 Mathlib 中的一个引理，
位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma _root_.IsCompact.everywherePosSubset (hs : IsCompact s) :
    IsCompact (μ.everywherePosSubset s) := by
  rcases exists_isOpen_everywherePosSubset_eq_sdiff μ s with ⟨u, u_open, hu⟩
  rw [hu]
  exact hs.diff u_open

/-- Any compact set contained in `s \ μ.everywherePosSubset s` has zero measure. -/
/-
**MeasureTheory.Measure.measure_eq_zero_of_subset_sdiff_everywherePosSubset** 是 
Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：measure_eq_zero_of_subset_sdiff_everywherePosSubset (hk : IsCompact k) (h'
k : k subseteq s \ μ.everywherePosSubset s) : μ k = 0
参数：hk : IsCompact k；h'k : k subseteq s \ μ.everywherePosSubset s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.induction_on`：IsCompact.induction_on (hs : IsCompact s) {p : S
et X -> Prop} (he : p ∅) (hmono : forall ⦃s t⦄, s subseteq t -> p t -> p s) (hun
ion : forall…
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.measure_union_null`：measure_union_null (hs : μ s = 0) (ht 
: μ t = 0) : μ (s union t) = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s

--- 原说明 ---
Any compact set contained in `s \ μ.everywherePosSubset s` has zero measure.
-/
lemma measure_eq_zero_of_subset_sdiff_everywherePosSubset
    (hk : IsCompact k) (h'k : k ⊆ s \ μ.everywherePosSubset s) : μ k = 0 := by
  apply hk.induction_on (p := fun t ↦ μ t = 0)
  · exact measure_empty
  · exact fun s t hst ht ↦ measure_mono_null hst ht
  · exact fun s t hs ht ↦ measure_union_null hs ht
  · intro x hx
    obtain ⟨u, ux, hu⟩ : ∃ u ∈ 𝓝[s] x, μ u = 0 := by
      simpa [everywherePosSubset, (h'k hx).1] using (h'k hx).2
    exact ⟨u, nhdsWithin_mono x (h'k.trans sdiff_subset) ux, hu⟩

/-- In a space with an inner regular measure, any measurable set coincides almost everywhere with
its everywhere positive subset. -/
/-
**MeasureTheory.Measure.everywherePosSubset_ae_eq** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory.Measure`。
形式化陈述：everywherePosSubset_ae_eq [OpensMeasurableSpace α] [InnerRegular μ] (hs : 
MeasurableSet s) : μ.everywherePosSubset s =ᵐ[μ] s
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.sdiff_eq_empty`：sdiff_eq_empty {s t : Set α} : s \ t = ∅ ↔ s subsete
q t
· 使用引理 `MeasureTheory.Measure.everywherePosSubset_subset`：everywherePosSubset_su
bset (μ : Measure α) (s : Set α) : μ.everywherePosSubset s subseteq s
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasurableSet.measure_eq_iSup_isCompact`：∀ {α : Type u_1} [inst : Measur
ableSpace α] [inst_1 : TopologicalSpace α] ⦃U : Set α⦄,   MeasurableSet U → ∀ (μ
 : MeasureTheory.Measure α) […
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用定理 `MeasurableSet.everywherePosSubset`：∀ {α : Type u_1} [inst : TopologicalS
pace α] [inst_1 : MeasurableSpace α] {μ : MeasureTheory.Measure α} {s : Set α}  
 [OpensMeasurableSpace …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `MeasureTheory.Measure.measure_eq_zero_of_subset_sdiff_everywherePosSubse
t`：measure_eq_zero_of_subset_sdiff_everywherePosSubset (hk : IsCompact k) (h'k :
 k subseteq s \ μ.everywherePosSubset s) : μ k = 0

--- 原说明 ---
In a space with an inner regular measure, any measurable set coincides almost ev
erywhere with
its everywhere positive subset.
-/
lemma everywherePosSubset_ae_eq [OpensMeasurableSpace α] [InnerRegular μ] (hs : MeasurableSet s) :
    μ.everywherePosSubset s =ᵐ[μ] s := by
  simp only [ae_eq_set, sdiff_eq_empty.mpr (everywherePosSubset_subset μ s), measure_empty,
    true_and, (hs.diff hs.everywherePosSubset).measure_eq_iSup_isCompact, ENNReal.iSup_eq_zero]
  intro k hk h'k
  exact measure_eq_zero_of_subset_sdiff_everywherePosSubset h'k hk

/-- In a space with an inner regular measure for finite measure sets, any measurable set of finite
measure coincides almost everywhere with its everywhere positive subset. -/
/-
**MeasureTheory.Measure.everywherePosSubset_ae_eq_of_measure_ne_top** 是 Mathlib 
中的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：everywherePosSubset_ae_eq_of_measure_ne_top [OpensMeasurableSpace α] [Inne
rRegularCompactLTTop μ] (hs : MeasurableSet s) (h's : μ s != ∞) : μ.everywherePo
sSubset s =ᵐ[μ] s
参数：hs : MeasurableSet s；h's : μ s != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.sdiff_eq_empty`：sdiff_eq_empty {s t : Set α} : s \ t = ∅ ↔ s subsete
q t
· 使用引理 `MeasureTheory.Measure.everywherePosSubset_subset`：everywherePosSubset_su
bset (μ : Measure α) (s : Set α) : μ.everywherePosSubset s subseteq s
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasurableSet.measure_eq_iSup_isCompact_of_ne_top`：∀ {α : Type u_1} [ins
t : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace 
α]   [μ.InnerRegularCompactLTTop] ⦃A : …
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用定理 `MeasurableSet.everywherePosSubset`：∀ {α : Type u_1} [inst : TopologicalS
pace α] [inst_1 : MeasurableSpace α] {μ : MeasureTheory.Measure α} {s : Set α}  
 [OpensMeasurableSpace …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `MeasureTheory.Measure.measure_eq_zero_of_subset_sdiff_everywherePosSubse
t`：measure_eq_zero_of_subset_sdiff_everywherePosSubset (hk : IsCompact k) (h'k :
 k subseteq s \ μ.everywherePosSubset s) : μ k = 0

--- 原说明 ---
In a space with an inner regular measure for finite measure sets, any measurable
 set of finite
measure coincides almost everywhere with its everywhere positive subset.
-/
lemma everywherePosSubset_ae_eq_of_measure_ne_top
    [OpensMeasurableSpace α] [InnerRegularCompactLTTop μ] (hs : MeasurableSet s) (h's : μ s ≠ ∞) :
    μ.everywherePosSubset s =ᵐ[μ] s := by
  have A : μ (s \ μ.everywherePosSubset s) ≠ ∞ :=
    ((measure_mono sdiff_subset).trans_lt h's.lt_top).ne
  simp only [ae_eq_set, sdiff_eq_empty.mpr (everywherePosSubset_subset μ s), measure_empty,
    true_and, (hs.diff hs.everywherePosSubset).measure_eq_iSup_isCompact_of_ne_top A,
    ENNReal.iSup_eq_zero]
  intro k hk h'k
  exact measure_eq_zero_of_subset_sdiff_everywherePosSubset h'k hk

/-- In a space with an inner regular measure, the everywhere positive subset of a measurable set
is itself everywhere positive. This is not obvious as `μ.everywherePosSubset s` is defined as
the points whose neighborhoods intersect `s` along positive measure subsets, but this does not
say they also intersect `μ.everywherePosSubset s` along positive measure subsets. -/
/-
**MeasureTheory.Measure.isEverywherePos_everywherePosSubset** 是 Mathlib 中的一个引理，位
于命名空间 `MeasureTheory.Measure`。
形式化陈述：isEverywherePos_everywherePosSubset [OpensMeasurableSpace α] [InnerRegular
 μ] (hs : MeasurableSet s) : μ.IsEverywherePos (μ.everywherePosSubset s)
参数：hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsWithin_iff_exists_mem_nhds_inter`：mem_nhdsWithin_iff_exists_mem_
nhds_inter {t : Set α} {a : α} {s : Set α} : t in 𝓝[s] a ↔ exists u in 𝓝 a, u in
ter s subseteq t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_eq_set_inter`：ae_eq_set_inter {s' t' : Set α} (h : s =ᵐ
[μ] t) (h' : s' =ᵐ[μ] t') : (s inter s' : Set α) =ᵐ[μ] (t inter t' : Set α)
· 使用引理 `MeasureTheory.ae_eq_refl`：ae_eq_refl (f : α -> β) : f =ᵐ[μ] f
· 使用引理 `MeasureTheory.Measure.everywherePosSubset_ae_eq`：everywherePosSubset_ae_
eq [OpensMeasurableSpace α] [InnerRegular μ] (hs : MeasurableSet s) : μ.everywhe
rePosSubset s =ᵐ[μ] s
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.EventuallyEq.measure_eq`：∀ {α : Type u_1} {F : Type u_3} [inst : 
FunLike F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   {μ :
 F} {s t : Set α}, s…
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t

--- 原说明 ---
In a space with an inner regular measure, the everywhere positive subset of a me
asurable set
is itself everywhere positive. This is not obvious as `μ.everywherePosSubset s` 
is defined as
the points whose neighborhoods intersect `s` along positive measure subsets, but
 this does not
say they also intersect `μ.everywherePosSubset s` along positive measure subsets
.
-/
lemma isEverywherePos_everywherePosSubset
    [OpensMeasurableSpace α] [InnerRegular μ] (hs : MeasurableSet s) :
    μ.IsEverywherePos (μ.everywherePosSubset s) := by
  intro x hx n hn
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hn with ⟨u, u_mem, hu⟩
  have A : 0 < μ (u ∩ s) := by
    have : u ∩ s ∈ 𝓝[s] x := by rw [inter_comm]; exact inter_mem_nhdsWithin s u_mem
    exact hx.2 _ this
  have B : (u ∩ μ.everywherePosSubset s : Set α) =ᵐ[μ] (u ∩ s : Set α) :=
    ae_eq_set_inter (ae_eq_refl _) (everywherePosSubset_ae_eq hs)
  rw [← B.measure_eq] at A
  exact A.trans_le (measure_mono hu)

/-- In a space with an inner regular measure for finite measure sets, the everywhere positive subset
of a measurable set of finite measure is itself everywhere positive. This is not obvious as
`μ.everywherePosSubset s` is defined as the points whose neighborhoods intersect `s` along positive
measure subsets, but this does not say they also intersect `μ.everywherePosSubset s` along positive
measure subsets. -/
/-
**MeasureTheory.Measure.isEverywherePos_everywherePosSubset_of_measure_ne_top** 
是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：isEverywherePos_everywherePosSubset_of_measure_ne_top [OpensMeasurableSpac
e α] [InnerRegularCompactLTTop μ] (hs : MeasurableSet s) (h's : μ s != ∞) : μ.Is
EverywherePos (μ.everywherePosSubset s)
参数：hs : MeasurableSet s；h's : μ s != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsWithin_iff_exists_mem_nhds_inter`：mem_nhdsWithin_iff_exists_mem_
nhds_inter {t : Set α} {a : α} {s : Set α} : t in 𝓝[s] a ↔ exists u in 𝓝 a, u in
ter s subseteq t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_eq_set_inter`：ae_eq_set_inter {s' t' : Set α} (h : s =ᵐ
[μ] t) (h' : s' =ᵐ[μ] t') : (s inter s' : Set α) =ᵐ[μ] (t inter t' : Set α)
· 使用引理 `MeasureTheory.ae_eq_refl`：ae_eq_refl (f : α -> β) : f =ᵐ[μ] f
· 使用引理 `MeasureTheory.Measure.everywherePosSubset_ae_eq_of_measure_ne_top`：every
wherePosSubset_ae_eq_of_measure_ne_top [OpensMeasurableSpace α] [InnerRegularCom
pactLTTop μ] (hs : MeasurableSet s) (h's : μ s != ∞) : …
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.EventuallyEq.measure_eq`：∀ {α : Type u_1} {F : Type u_3} [inst : 
FunLike F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   {μ :
 F} {s t : Set α}, s…
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t

--- 原说明 ---
In a space with an inner regular measure for finite measure sets, the everywhere
 positive subset
of a measurable set of finite measure is itself everywhere positive. This is not
 obvious as
`μ.everywherePosSubset s` is defined as the points whose neighborhoods intersect
 `s` along positive
measure subsets, but this does not say they also intersect `μ.everywherePosSubse
t s` along positive
measure subsets.
-/
lemma isEverywherePos_everywherePosSubset_of_measure_ne_top
    [OpensMeasurableSpace α] [InnerRegularCompactLTTop μ] (hs : MeasurableSet s) (h's : μ s ≠ ∞) :
    μ.IsEverywherePos (μ.everywherePosSubset s) := by
  intro x hx n hn
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hn with ⟨u, u_mem, hu⟩
  have A : 0 < μ (u ∩ s) := by
    have : u ∩ s ∈ 𝓝[s] x := by rw [inter_comm]; exact inter_mem_nhdsWithin s u_mem
    exact hx.2 _ this
  have B : (u ∩ μ.everywherePosSubset s : Set α) =ᵐ[μ] (u ∩ s : Set α) :=
    ae_eq_set_inter (ae_eq_refl _) (everywherePosSubset_ae_eq_of_measure_ne_top hs h's)
  rw [← B.measure_eq] at A
  exact A.trans_le (measure_mono hu)
/-
**MeasureTheory.Measure.IsEverywherePos.smul_measure** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure.IsEverywherePos`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1 : MeasurableSpace α] 
{μ : MeasureTheory.Measure α} {s : Set α},   μ.IsEverywherePos s → ∀ {c : ENNRea
l}, c ≠ 0 → (c • μ).IsEverywherePos s
参数：c • μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
-/
lemma IsEverywherePos.smul_measure (hs : IsEverywherePos μ s) {c : ℝ≥0∞} (hc : c ≠ 0) :
    IsEverywherePos (c • μ) s :=
  fun x hx n hn ↦ by simpa [hc.bot_lt, hs x hx n hn] using hc.bot_lt
/-
**MeasureTheory.Measure.IsEverywherePos.smul_measure_nnreal** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.Measure.IsEverywherePos`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1 : MeasurableSpace α] 
{μ : MeasureTheory.Measure α} {s : Set α},   μ.IsEverywherePos s → ∀ {c : NNReal
}, c ≠ 0 → (c • μ).IsEverywherePos s
参数：c • μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.IsEverywherePos.smul_measure`：∀ {α : Type u_1} [in
st : TopologicalSpace α] [inst_1 : MeasurableSpace α] {μ : MeasureTheory.Measure
 α} {s : Set α},   μ.IsEverywherePos s →…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma IsEverywherePos.smul_measure_nnreal (hs : IsEverywherePos μ s) {c : ℝ≥0} (hc : c ≠ 0) :
    IsEverywherePos (c • μ) s :=
  hs.smul_measure (by simpa using hc)

/-- If two measures coincide locally, then a set which is everywhere positive for the former is
also everywhere positive for the latter. -/
/-
**MeasureTheory.Measure.IsEverywherePos.of_forall_exists_nhds_eq** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.Measure.IsEverywherePos`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1 : MeasurableSpace α] 
{μ ν : MeasureTheory.Measure α} {s : Set α},   μ.IsEverywherePos s → (∀ x ∈ s, ∃
 t ∈ nhds x, ∀ u ⊆ t, ν u = μ u) → ν.IsEverywherePos s
参数：∀ x ∈ s, ∃ t ∈ nhds x, ∀ u ⊆ t, ν u = μ u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a

--- 原说明 ---
If two measures coincide locally, then a set which is everywhere positive for th
e former is
also everywhere positive for the latter.
-/
lemma IsEverywherePos.of_forall_exists_nhds_eq (hs : IsEverywherePos μ s)
    (h : ∀ x ∈ s, ∃ t ∈ 𝓝 x, ∀ u ⊆ t, ν u = μ u) : IsEverywherePos ν s := by
  intro x hx n hn
  rcases h x hx with ⟨t, t_mem, ht⟩
  grw [← inter_subset_left (s := n)]
  rw [ht (n ∩ t) inter_subset_right]
  exact hs x hx _ (inter_mem hn (mem_nhdsWithin_of_mem_nhds t_mem))

/-- If two measures coincide locally, then a set is everywhere positive for the former iff it is
everywhere positive for the latter. -/
/-
**MeasureTheory.Measure.isEverywherePos_iff_of_forall_exists_nhds_eq** 是 Mathlib
 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：isEverywherePos_iff_of_forall_exists_nhds_eq (h : forall x in s, exists t 
in 𝓝 x, forall u subseteq t, ν u = μ u) : IsEverywherePos ν s ↔ IsEverywherePos 
μ s
参数：h : forall x in s, exists t in 𝓝 x, forall u subseteq t, ν u = μ u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.IsEverywherePos.of_forall_exists_nhds_eq`：∀ {α : T
ype u_1} [inst : TopologicalSpace α] [inst_1 : MeasurableSpace α] {μ ν : Measure
Theory.Measure α} {s : Set α},   μ.IsEverywherePos s…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If two measures coincide locally, then a set is everywhere positive for the form
er iff it is
everywhere positive for the latter.
-/
lemma isEverywherePos_iff_of_forall_exists_nhds_eq (h : ∀ x ∈ s, ∃ t ∈ 𝓝 x, ∀ u ⊆ t, ν u = μ u) :
    IsEverywherePos ν s ↔ IsEverywherePos μ s := by
  refine ⟨fun H ↦ H.of_forall_exists_nhds_eq ?_, fun H ↦ H.of_forall_exists_nhds_eq h⟩
  intro x hx
  rcases h x hx with ⟨t, ht, h't⟩
  exact ⟨t, ht, fun u hu ↦ (h't u hu).symm⟩

/-- An open set is everywhere positive for a measure which is positive on open sets. -/
/-
**MeasureTheory.Measure._root_.IsOpen.isEverywherePos** 是 Mathlib 中的一个引理，位于命名空间 
`MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An open set is everywhere positive for a measure which is positive on open sets.
-/
lemma _root_.IsOpen.isEverywherePos [IsOpenPosMeasure μ] (hs : IsOpen s) : IsEverywherePos μ s := by
  intro x xs n hn
  rcases mem_nhdsWithin.1 hn with ⟨u, u_open, xu, hu⟩
  apply lt_of_lt_of_le _ (measure_mono hu)
  exact (u_open.inter hs).measure_pos μ ⟨x, ⟨xu, xs⟩⟩

section IsTopologicalGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
  [IsMulLeftInvariant μ] [IsFiniteMeasureOnCompacts μ] [InnerRegularCompactLTTop μ]

open scoped Pointwise

/-- If a compact closed set is everywhere positive with respect to a left-invariant measure on a
topological group, then it is a Gδ set. This is nontrivial, as there is no second-countability or
metrizability assumption in the statement, so a general compact closed set has no reason to be
a countable intersection of open sets. -/
@[to_additive
/-- If a compact closed set is everywhere positive with respect to a left-invariant measure on a
topological additive group, then it is a Gδ set. This is nontrivial, as there is no
second-countability or metrizability assumption in the statement, so a general compact closed set
has no reason to be a countable intersection of open sets. -/]
/-
**MeasureTheory.Measure.IsEverywherePos.IsGdelta_of_isMulLeftInvariant** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory.Measure.IsEverywherePos`。
形式化陈述：∀ {G : Type u_2} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopolog
icalGroup G] [LocallyCompactSpace G]   [inst_4 : MeasurableSpace G] [BorelSpace 
G] {μ : MeasureTheory.Measure G} [μ.IsMulLeftInvariant]   [MeasureTheory.IsFinit
eMeasureOnCompacts μ] [μ.InnerRegularCompactLTTop] {k : Set G},   μ.IsEverywhere
Pos k → IsCompact k → IsClosed k → IsGδ k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_seq_strictAnti_tendsto'`：exists_seq_strictAnti_tendsto' [DenselyO
rdered α] [FirstCountableTopology α] {x y : α} (hy : x < y) : exists u : Nat -> 
α, StrictAnti u ∧ (f…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
· 使用定理 `exists_open_nhds_one_mul_subset`：exists_open_nhds_one_mul_subset {U : Se
t M} (hU : U in 𝓝 (1 : M)) : exists V : Set M, IsOpen V ∧ (1 : M) in V ∧ V * V s
ubseteq U
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用引理 `MeasureTheory.eventually_nhds_one_measure_smul_sdiff_lt`：eventually_nhds
_one_measure_smul_sdiff_lt [LocallyCompactSpace G] [IsFiniteMeasureOnCompacts μ]
 [InnerRegularCompactLTTop μ] {k : Set G} (hk…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `IsCompact.exists_mapClusterPt`：IsCompact.exists_mapClusterPt {ι : Type*}
 (hs : IsCompact s) {f : Filter ι} [NeBot f] {u : ι -> X} (hf : Filter.map u f <
= 𝓟 s) : exists x i…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
（共 88 条，此处仅展示前 30 条）
-/
lemma IsEverywherePos.IsGdelta_of_isMulLeftInvariant
    {k : Set G} (h : μ.IsEverywherePos k) (hk : IsCompact k) (h'k : IsClosed k) :
    IsGδ k := by
  /- Consider a decreasing sequence of open neighborhoods `Vₙ` of the identity, such that `g k \ k`
  has small measure for all `g ∈ Vₙ`. We claim that `k = ⋂ Vₙ k`, which proves
  the lemma as the sets on the right are open. The inclusion `⊆` is trivial.
  Let us show the converse. Take `x` in the intersection. For each `n`, write `x = vₙ yₙ` with
  `vₙ ∈ Vₙ` and `yₙ ∈ k`. Let `z ∈ k` be a cluster value of `yₙ`, by compactness. As multiplication
  by `vₙ = x yₙ⁻¹ ∈ Vₙ` changes the measure of `k` by very little, passing to the limit we get
  `μ (x z⁻¹ k \ k) = 0`. By invariance of the measure under `z x ⁻¹`, we get `μ (k \ z x⁻¹ k) = 0`.
  Assume `x ∉ k`. Then `z ∈ k \ z x⁻¹ k`. Even more, this set is a neighborhood of `z` within `k`
  (as `z x⁻¹ k` is closed), and it has zero measure. This contradicts the fact that `k` has
  positive measure around the point `z`. -/
  obtain ⟨u, -, u_mem, u_lim⟩ : ∃ u, StrictAnti u ∧ (∀ (n : ℕ), u n ∈ Ioo 0 1)
    ∧ Tendsto u atTop (𝓝 0) := exists_seq_strictAnti_tendsto' (zero_lt_one : (0 : ℝ≥0∞) < 1)
  have : ∀ n, ∃ (W : Set G), IsOpen W ∧ 1 ∈ W ∧ ∀ g ∈ W * W, μ ((g • k) \ k) < u n :=
    fun n ↦ exists_open_nhds_one_mul_subset
      (eventually_nhds_one_measure_smul_sdiff_lt hk h'k (u_mem n).1.ne')
  choose W W_open mem_W hW using this
  let V n := ⋂ i ∈ Finset.range n, W i
  suffices ⋂ n, V n * k ⊆ k by
    replace : k = ⋂ n, V n * k := by
      apply Subset.antisymm (subset_iInter_iff.2 (fun n ↦ ?_)) this
      exact subset_mul_right k (by simp [V, mem_W])
    rw [this]
    refine .iInter_of_isOpen fun n ↦ ?_
    exact .mul_right (isOpen_biInter_finset (fun i _hi ↦ W_open i))
  intro x hx
  choose v hv y hy hvy using mem_iInter.1 hx
  obtain ⟨z, zk, hz⟩ : ∃ z ∈ k, MapClusterPt z atTop y := hk.exists_mapClusterPt (by simp [hy])
  have A n : μ (((x * z⁻¹) • k) \ k) ≤ u n := by
    apply le_of_lt (hW _ _ ?_)
    have : W n * {z} ∈ 𝓝 z := (IsOpen.mul_right (W_open n)).mem_nhds (by simp [mem_W])
    obtain ⟨i, hi, ni⟩ : ∃ i, y i ∈ W n * {z} ∧ n < i :=
      ((hz.frequently this).and_eventually (eventually_gt_atTop n)).exists
    refine ⟨x * (y i) ⁻¹, ?_, y i * z⁻¹, by simpa using hi, by group⟩
    have I : V i ⊆ W n := iInter₂_subset n (by simp [ni])
    have J : x * (y i)⁻¹ ∈ V i := by simpa [← hvy i] using hv i
    exact I J
  have B : μ (((x * z⁻¹) • k) \ k) = 0 :=
    le_antisymm (ge_of_tendsto u_lim (Eventually.of_forall A)) bot_le
  have C : μ (k \ (z * x⁻¹) • k) = 0 := by
    have : μ ((z * x⁻¹) • (((x * z⁻¹) • k) \ k)) = 0 := by rwa [measure_smul]
    rw [← this, smul_set_sdiff, smul_smul]
    group
    simp
  by_contra H
  have : k ∩ ((z * x⁻¹) • k)ᶜ ∈ 𝓝[k] z := by
    apply inter_mem_nhdsWithin k
    apply IsOpen.mem_nhds (by simpa using h'k.smul _)
    push _ ∈ _
    contrapose H
    simpa [mem_smul_set_iff_inv_smul_mem] using H
  have : 0 < μ (k \ ((z * x⁻¹) • k)) := h z zk _ this
  exact lt_irrefl _ (C.le.trans_lt this)

/-- **Halmos' theorem: Haar measure is completion regular.** More precisely, any finite measure
set can be approximated from inside by a level set of a continuous function with compact support. -/
@[to_additive innerRegularWRT_preimage_one_hasCompactSupport_measure_ne_top_of_addGroup
/-- **Halmos' theorem: Haar measure is completion regular.** More precisely, any finite measure
set can be approximated from inside by a level set of a continuous function with compact
support. -/]
/-
**MeasureTheory.Measure.innerRegularWRT_preimage_one_hasCompactSupport_measure_n
e_top_of_group** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：innerRegularWRT_preimage_one_hasCompactSupport_measure_ne_top_of_group : I
nnerRegularWRT μ (fun s => exists (f : G -> Real), Continuous f ∧ HasCompactSupp
ort f ∧ s = f ⁻¹' {1}) (fun s => MeasurableSet s ∧ μ s != ∞)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.InnerRegularWRT.trans`：trans {q' : Set α -> Prop} 
(H : InnerRegularWRT μ p q) (H' : InnerRegularWRT μ q q') : InnerRegularWRT μ p 
q'
· 使用定理 `IsCompact.everywherePosSubset`：∀ {α : Type u_1} [inst : TopologicalSpace
 α] [inst_1 : MeasurableSpace α] {μ : MeasureTheory.Measure α} {s : Set α},   Is
Compact s → IsCompa…
· 使用定理 `IsClosed.everywherePosSubset`：∀ {α : Type u_1} [inst : TopologicalSpace 
α] [inst_1 : MeasurableSpace α] {μ : MeasureTheory.Measure α} {s : Set α},   IsC
losed s → IsClosed…
· 使用引理 `MeasureTheory.Measure.everywherePosSubset_subset`：everywherePosSubset_su
bset (μ : Measure α) (s : Set α) : μ.everywherePosSubset s subseteq s
· 使用引理 `MeasureTheory.Measure.isEverywherePos_everywherePosSubset_of_measure_ne_
top`：isEverywherePos_everywherePosSubset_of_measure_ne_top [OpensMeasurableSpace
 α] [InnerRegularCompactLTTop μ] (hs : MeasurableSet s) (h's : μ …
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `IsCompact.measure_lt_top`：∀ {α : Type u_1} {m0 : MeasurableSpace α} [ins
t : TopologicalSpace α] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsFiniteM
easureOnCompac…
· 使用定理 `MeasureTheory.Measure.IsEverywherePos.IsGdelta_of_isMulLeftInvariant`：∀ 
{G : Type u_2} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGrou
p G] [LocallyCompactSpace G]   [inst_4 : MeasurableSpace G…
· 使用定理 `exists_continuous_one_zero_of_isCompact_of_isGδ`：exists_continuous_one_z
ero_of_isCompact_of_isGδ [RegularSpace X] [LocallyCompactSpace X] {s t : Set X} 
(hs : IsCompact s) (h's : IsGδ s) (ht…
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `isClosed_empty`：isClosed_empty : IsClosed (∅ : Set X)
· 使用定理 `Set.disjoint_empty`：∀ {α : Type u} (s : Set α), Disjoint s ∅
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.Measure.everywherePosSubset_ae_eq_of_measure_ne_top`：every
wherePosSubset_ae_eq_of_measure_ne_top [OpensMeasurableSpace α] [InnerRegularCom
pactLTTop μ] (hs : MeasurableSet s) (h's : μ s != ∞) : …
· 使用引理 `MeasureTheory.innerRegularWRT_isCompact_isClosed_measure_ne_top_of_group
`：innerRegularWRT_isCompact_isClosed_measure_ne_top_of_group [h : InnerRegularCo
mpactLTTop μ] : InnerRegularWRT μ (fun s => IsCompact s ∧ IsCl…
-/
theorem innerRegularWRT_preimage_one_hasCompactSupport_measure_ne_top_of_group :
    InnerRegularWRT μ (fun s ↦ ∃ (f : G → ℝ), Continuous f ∧ HasCompactSupport f ∧ s = f ⁻¹' {1})
    (fun s ↦ MeasurableSet s ∧ μ s ≠ ∞) := by
  /- First, approximate a measurable set from inside by a compact closed set `K`. Then notice that
  the everywhere positive subset of `K` is a Gδ,
  by Lemma `IsEverywherePos.IsGdelta_of_isMulLeftInvariant`, and therefore the level set of a
  continuous compactly supported function. Moreover, it has the same measure as `K`. -/
  apply InnerRegularWRT.trans _ innerRegularWRT_isCompact_isClosed_measure_ne_top_of_group
  intro K ⟨K_comp, K_closed⟩ r hr
  let L := μ.everywherePosSubset K
  have L_comp : IsCompact L := K_comp.everywherePosSubset
  have L_closed : IsClosed L := K_closed.everywherePosSubset
  refine ⟨L, everywherePosSubset_subset μ K, ?_, ?_⟩
  · have : μ.IsEverywherePos L :=
      isEverywherePos_everywherePosSubset_of_measure_ne_top K_closed.measurableSet
      K_comp.measure_lt_top.ne
    have L_Gδ : IsGδ L := this.IsGdelta_of_isMulLeftInvariant L_comp L_closed
    obtain ⟨⟨f, f_cont⟩, Lf, -, f_comp, -⟩ : ∃ f : C(G, ℝ), L = f ⁻¹' {1} ∧ EqOn f 0 ∅
        ∧ HasCompactSupport f ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 :=
      exists_continuous_one_zero_of_isCompact_of_isGδ L_comp L_Gδ isClosed_empty
        (disjoint_empty L)
    exact ⟨f, f_cont, f_comp, Lf⟩
  · convert! hr using 1
    apply measure_congr
    exact everywherePosSubset_ae_eq_of_measure_ne_top K_closed.measurableSet
      K_comp.measure_lt_top.ne

end IsTopologicalGroup

end Measure

end MeasureTheory

