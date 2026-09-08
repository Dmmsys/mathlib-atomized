/-
Copyright (c) 2025 Stefano Rocca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Stefano Rocca
-/
module

public import Mathlib.MeasureTheory.Group.Action

/-!
# Følner sequences and filters - definitions and properties

This file defines Følner sequences and filters for measurable spaces acted on by a group.

## Definitions

* `IsFoelner G μ l F` : Consider a group `G` acting on a measure space `X`.
  A sequence of sets `F : ι → Set X` is **Følner** with respect to the `G`-action, the measure `μ`,
  and a filter `l` on the indexing type `ι`, if:
  1. Eventually, as `i` tends to `l`, the set `F i` is measurable with finite non-zero measure,
  2. For all `g : G`, `μ ((g • F i) ∆ F i) / μ (F i)` tends to `0`.

* `IsFoelner.mean μ u F s` : The limit along an ultrafilter `u` of the density of a set `s`
  with respect to a Følner sequence `F` in the measure space `X`.

* `maxFoelner G μ` : The maximal Følner filter with respect to some group `G` acting on a
  measure space `X` is the pullback of `𝓝 0` along the map `s ↦ μ (g • s) / μ s` over measurable
  sets of finite non-zero measure.

* `IsAddFoelner G μ l F`: the analog of `IsFoelner G μ l F` for an additive group action

## Main results

* `IsFoelner.amenable` : If there exists a non-trivial Følner filter with respect to some
  group `G` acting on a measure space `X`, then there exists a `G`-invariant finitely additive
  probability measure on `X`.

* `isFoelner_iff_tendsto` : A sequence of sets is Følner if and only if it tends to the
  maximal Følner filter.
  The attribute "maximal" of the latter comes from the direct implication of this theorem :
  if `IsFoelner G μ l F` then the push-forward filter `map F l ≤ maxFoelner G μ`.

* `amenable_of_maxFoelner_neBot` : If the maximal Følner filter is non-trivial,
  then there exists a `G`-invariant finitely additive probability measure on `X`.

## Temporary design adaptations

* In the current version, we refer to the amenability of the action of a group on a measure space
  (e.g. in `IsFoelner.amenable` and `amenable_of_maxFoelner_neBot`), even though a definition of
  amenability has not yet been given in Mathlib.
  This is because there are different notions of amenability for groups and for group actions,
  and a Mathlib definition should be provided at the greatest level of generality, on which there
  has not yet been a general consensus.
  At the present moment, `amenable` corresponds to the existence of a `G`-invariant finitely
  additive probability measure.

## Tags

Foelner, Følner filter, amenability, amenable group
-/

@[expose] public section

open MeasureTheory Filter Set Tendsto
open scoped ENNReal Pointwise symmDiff Topology Filter

variable {G X : Type*} [MeasurableSpace X] {μ : Measure X} [Group G] [MulAction G X]
variable {ι : Type*} {l : Filter ι} {u : Ultrafilter ι} {F : ι → Set X}

variable (G : Type*) {X : Type*} [MeasurableSpace X] (μ : Measure X) [AddGroup G] [AddAction G X]
         {ι : Type*} (l : Filter ι) (F : ι → Set X) in
/-- Consider an additive group `G` acting on a measure space `X`.
  A sequence of sets `F : ι → Set X` is **Følner** with respect to the `G`-action,
  the measure `μ`, and a filter `l` on the indexing type `ι`, if:
  1. Each `s` in `l` is eventually measurable with finite non-zero measure,
  2. For all `g : G`, `μ ((g +ᵥ F i) ∆ F i) / μ (F i)` tends to `0`. -/
@[mk_iff]
/-
**IsAddFoelner** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_4) →   {X : Type u_5} →     [inst : MeasurableSpace X] →      
 MeasureTheory.Measure X → [inst : AddGroup G] → [AddAction G X] → {ι : Type u_6
} → Filter ι → (ι → Set X) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Consider an additive group `G` acting on a measure space `X`.
  A sequence of sets `F : ι → Set X` is **Følner** with respect to the `G`-actio
n,
  the measure `μ`, and a filter `l` on the indexing type `ι`, if:
  1. Each `s` in `l` is eventually measurable with finite non-zero measure,
  2. For all `g : G`, `μ ((g +ᵥ F i) ∆ F i) / μ (F i)` tends to `0`.
-/
structure IsAddFoelner : Prop where
  eventually_measurableSet : ∀ᶠ i in l, MeasurableSet (F i)
  eventually_meas_ne_zero : ∀ᶠ i in l, μ (F i) ≠ 0
  eventually_meas_ne_top : ∀ᶠ i in l, μ (F i) ≠ ∞
  tendsto_meas_vadd_symmDiff (g : G) : Tendsto (fun i ↦ μ ((g +ᵥ F i) ∆ F i) / μ (F i)) l (𝓝 0)

variable (G μ l F) in
/-- Consider a group `G` acting on a measure space `X`.
  A sequence of sets `F : ι → Set X` is **Følner** with respect to the `G`-action,
  the measure `μ`, and a filter `l` on the indexing type `ι`, if:
  1. Each `s` in `l` is eventually measurable with finite non-zero measure,
  2. For all `g : G`, `μ ((g • F i) ∆ F i) / μ (F i)` tends to `0`. -/
@[mk_iff]
/-
**IsFoelner** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_1) →   {X : Type u_2} →     [inst : MeasurableSpace X] →      
 MeasureTheory.Measure X → [inst : Group G] → [MulAction G X] → {ι : Type u_3} →
 Filter ι → (ι → Set X) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Consider a group `G` acting on a measure space `X`.
  A sequence of sets `F : ι → Set X` is **Følner** with respect to the `G`-actio
n,
  the measure `μ`, and a filter `l` on the indexing type `ι`, if:
  1. Each `s` in `l` is eventually measurable with finite non-zero measure,
  2. For all `g : G`, `μ ((g • F i) ∆ F i) / μ (F i)` tends to `0`.
-/
structure IsFoelner : Prop where
  eventually_measurableSet : ∀ᶠ i in l, MeasurableSet (F i)
  eventually_meas_ne_zero : ∀ᶠ i in l, μ (F i) ≠ 0
  eventually_meas_ne_top : ∀ᶠ i in l, μ (F i) ≠ ∞
  tendsto_meas_smul_symmDiff (g : G) : Tendsto (fun i ↦ μ ((g • F i) ∆ F i) / μ (F i)) l (𝓝 0)

attribute [to_additive IsAddFoelner] IsFoelner
attribute [to_additive existing isAddFoelner_iff] isFoelner_iff

namespace IsFoelner

/-- The constant sequence `X` is Følner if `X` has finite measure. -/
@[to_additive /--The constant sequence `X` is Følner if `X` has finite measure. -/]
/-
**IsFoelner.univ_of_isFiniteMeasure** 是 Mathlib 中的一个定理，位于命名空间 `IsFoelner`。
形式化陈述：univ_of_isFiniteMeasure [NeZero μ] [IsFiniteMeasure μ] : IsFoelner G μ l (
fun _ => .univ) where eventually_measurableSet
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.instNeZeroENNRealCoeSetUniv`：∀ {α : Type u_1} {m0 
: MeasurableSpace α} {μ : MeasureTheory.Measure α} [NeZero μ], NeZero (μ Set.uni
v)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.smul_set_univ`：smul_set_univ : a • (univ : Set β) = univ
· 使用定理 `symmDiff_self`：symmDiff_self : a ∆ a = ⊥
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ENNReal.zero_div`：∀ {a : ENNReal}, 0 / a = 0
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
The constant sequence `X` is Følner if `X` has finite measure.
-/
theorem univ_of_isFiniteMeasure [NeZero μ] [IsFiniteMeasure μ] :
    IsFoelner G μ l (fun _ ↦ .univ) where
  eventually_measurableSet := by simp
  eventually_meas_ne_zero := by simp [NeZero.ne]
  eventually_meas_ne_top := by simp
  tendsto_meas_smul_symmDiff := by simp [tendsto_const_nhds]

@[to_additive]
/-
**IsFoelner.mono** 是 Mathlib 中的一个定理，位于命名空间 `IsFoelner`。
形式化陈述：mono {l' : Filter ι} (hfoel : IsFoelner G μ l F) (hle : l' <= l) : IsFoeln
er G μ l' F where eventually_measurableSet
参数：hfoel : IsFoelner G μ l F；hle : l' <= l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `IsFoelner.eventually_measurableSet`：∀ {G : Type u_1} {X : Type u_2} [ins
t : MeasurableSpace X] {μ : MeasureTheory.Measure X} [inst_1 : Group G]   [inst_
2 : MulAction G X] {ι : …
· 使用定理 `IsFoelner.eventually_meas_ne_zero`：∀ {G : Type u_1} {X : Type u_2} [inst
 : MeasurableSpace X] {μ : MeasureTheory.Measure X} [inst_1 : Group G]   [inst_2
 : MulAction G X] {ι : …
· 使用定理 `IsFoelner.eventually_meas_ne_top`：∀ {G : Type u_1} {X : Type u_2} [inst 
: MeasurableSpace X] {μ : MeasureTheory.Measure X} [inst_1 : Group G]   [inst_2 
: MulAction G X] {ι : …
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `IsFoelner.tendsto_meas_smul_symmDiff`：∀ {G : Type u_1} {X : Type u_2} [i
nst : MeasurableSpace X] {μ : MeasureTheory.Measure X} [inst_1 : Group G]   [ins
t_2 : MulAction G X] {ι : …
-/
theorem mono {l' : Filter ι} (hfoel : IsFoelner G μ l F) (hle : l' ≤ l) :
    IsFoelner G μ l' F where
  eventually_measurableSet := hfoel.eventually_measurableSet.filter_mono hle
  eventually_meas_ne_zero := hfoel.eventually_meas_ne_zero.filter_mono hle
  eventually_meas_ne_top := hfoel.eventually_meas_ne_top.filter_mono hle
  tendsto_meas_smul_symmDiff (g : G) := Tendsto.mono_left (hfoel.tendsto_meas_smul_symmDiff g) hle

@[to_additive]
/-
**IsFoelner.comp_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `IsFoelner`。
形式化陈述：comp_tendsto {ι' : Type*} {l' : Filter ι'} {φ : ι' -> ι} (hfoel : IsFoelne
r G μ l F) (htendsto : Tendsto φ l' l) : IsFoelner G μ l' (F ∘ φ) where eventual
ly_measurableSet
参数：hfoel : IsFoelner G μ l F；htendsto : Tendsto φ l' l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `IsFoelner.eventually_measurableSet`：∀ {G : Type u_1} {X : Type u_2} [ins
t : MeasurableSpace X] {μ : MeasureTheory.Measure X} [inst_1 : Group G]   [inst_
2 : MulAction G X] {ι : …
· 使用定理 `IsFoelner.eventually_meas_ne_zero`：∀ {G : Type u_1} {X : Type u_2} [inst
 : MeasurableSpace X] {μ : MeasureTheory.Measure X} [inst_1 : Group G]   [inst_2
 : MulAction G X] {ι : …
· 使用定理 `IsFoelner.eventually_meas_ne_top`：∀ {G : Type u_1} {X : Type u_2} [inst 
: MeasurableSpace X] {μ : MeasureTheory.Measure X} [inst_1 : Group G]   [inst_2 
: MulAction G X] {ι : …
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `IsFoelner.tendsto_meas_smul_symmDiff`：∀ {G : Type u_1} {X : Type u_2} [i
nst : MeasurableSpace X] {μ : MeasureTheory.Measure X} [inst_1 : Group G]   [ins
t_2 : MulAction G X] {ι : …
-/
theorem comp_tendsto {ι' : Type*} {l' : Filter ι'} {φ : ι' → ι} (hfoel : IsFoelner G μ l F)
    (htendsto : Tendsto φ l' l) :
    IsFoelner G μ l' (F ∘ φ) where
  eventually_measurableSet := htendsto.eventually hfoel.eventually_measurableSet
  eventually_meas_ne_zero := htendsto.eventually hfoel.eventually_meas_ne_zero
  eventually_meas_ne_top := htendsto.eventually hfoel.eventually_meas_ne_top
  tendsto_meas_smul_symmDiff (g : G) := (hfoel.tendsto_meas_smul_symmDiff g).comp htendsto

variable (μ u F) in
/-- The limit along an ultrafilter of the density of a set with respect to a sequence in `X`. -/
@[to_additive
/-- The limit along an ultrafilter of the density of a set with respect to a sequence in `X`. -/]
/-
**IsFoelner.mean** 是 Mathlib 中的一个定义，位于命名空间 `IsFoelner`。
形式化陈述：mean (s : Set X)
参数：s : Set X。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
noncomputable def mean (s : Set X) :=
  limUnder u (fun i ↦ μ (s ∩ F i) / μ (F i))

@[to_additive]
/-
**IsFoelner.tendsto_nhds_mean** 是 Mathlib 中的一个定理，位于命名空间 `IsFoelner`。
形式化陈述：tendsto_nhds_mean (hfoel : IsFoelner G μ u F) (s : Set X) : Tendsto (fun i
 => μ (s inter F i) / μ (F i)) u (𝓝 (mean μ u F s))
参数：hfoel : IsFoelner G μ u F；s : Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `IsFoelner.eventually_meas_ne_top`：∀ {G : Type u_1} {X : Type u_2} [inst 
: MeasurableSpace X] {μ : MeasureTheory.Measure X} [inst_1 : Group G]   [inst_2 
: MulAction G X] {ι : …
· 使用定理 `IsFoelner.eventually_meas_ne_zero`：∀ {G : Type u_1} {X : Type u_2} [inst
 : MeasurableSpace X] {μ : MeasureTheory.Measure X} [inst_1 : Group G]   [inst_2
 : MulAction G X] {ι : …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.div_le_iff`：∀ {x y z : ENNReal}, y ≠ 0 → y ≠ ⊤ → (x / y ≤ z ↔ x 
≤ z * y)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `MeasureTheory.OuterMeasure.mono`：∀ {α : Type u_2} (self : MeasureTheory.
OuterMeasure α) {s₁ s₂ : Set α}, s₁ ⊆ s₂ → self.measureOf s₁ ≤ self.measureOf s₂
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `IsCompact.ultrafilter_le_nhds'`：∀ {X : Type u} [inst : TopologicalSpace 
X] {s : Set X},   IsCompact s → ∀ (f : Ultrafilter X), s ∈ f → ∃ x ∈ s, ↑f ≤ nhd
s x
· 使用定理 `CompactIccSpace.isCompact_Icc`：∀ {α : Type u_1} {inst : TopologicalSpace
 α} {inst_1 : Preorder α} [self : CompactIccSpace α] {a b : α},   IsCompact (Set
.Icc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `tendsto_nhds_limUnder`：tendsto_nhds_limUnder {f : Filter α} {g : α -> X}
 (h : exists x, Tendsto g f (𝓝 x)) : Tendsto g f (𝓝 (@limUnder _ _ _ h.nonempty 
f g))
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem tendsto_nhds_mean (hfoel : IsFoelner G μ u F) (s : Set X) :
    Tendsto (fun i ↦ μ (s ∩ F i) / μ (F i)) u (𝓝 (mean μ u F s)) := by
  have mem_Icc : ∀ᶠ i in u, μ (s ∩ F i) / μ (F i) ∈ Icc 0 1 := by
    filter_upwards [hfoel.eventually_meas_ne_zero, hfoel.eventually_meas_ne_top] with i hi hi'
    simpa [ENNReal.div_le_iff hi hi'] using μ.mono inter_subset_right
  obtain ⟨x, hx⟩ := isCompact_Icc.ultrafilter_le_nhds'
    (u.map (fun i ↦ μ (s ∩ F i) / μ (F i))) (mem_map.1 mem_Icc)
  exact tendsto_nhds_limUnder (by use x; exact hx.2)

@[to_additive]
/-
**IsFoelner.mean_univ_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `IsFoelner`。
形式化陈述：mean_univ_eq_one (hfoel : IsFoelner G μ u F) : mean μ u F .univ = 1
参数：hfoel : IsFoelner G μ u F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_unique_of_eventuallyEq`：tendsto_nhds_unique_of_eventuallyEq
 [T2Space X] {f g : Y -> X} {l : Filter Y} {a b : X} [NeBot l] (ha : Tendsto f l
 (𝓝 a)) (hb : Tendsto g l…
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `IsFoelner.tendsto_nhds_mean`：tendsto_nhds_mean (hfoel : IsFoelner G μ u 
F) (s : Set X) : Tendsto (fun i => μ (s inter F i) / μ (F i)) u (𝓝 (mean μ u F s
))
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `IsFoelner.eventually_meas_ne_top`：∀ {G : Type u_1} {X : Type u_2} [inst 
: MeasurableSpace X] {μ : MeasureTheory.Measure X} [inst_1 : Group G]   [inst_2 
: MulAction G X] {ι : …
· 使用定理 `IsFoelner.eventually_meas_ne_zero`：∀ {G : Type u_1} {X : Type u_2} [inst
 : MeasurableSpace X] {μ : MeasureTheory.Measure X} [inst_1 : Group G]   [inst_2
 : MulAction G X] {ι : …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `ENNReal.div_self`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a / a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mean_univ_eq_one (hfoel : IsFoelner G μ u F) :
    mean μ u F .univ = 1 := by
  refine tendsto_nhds_unique_of_eventuallyEq (hfoel.tendsto_nhds_mean _) tendsto_const_nhds ?_
  filter_upwards [hfoel.eventually_meas_ne_zero, hfoel.eventually_meas_ne_top] with i hi hi'
  simp [ENNReal.div_self hi hi']

@[to_additive]
/-
**IsFoelner.mean_union_eq_add_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `IsFoelner`。
形式化陈述：mean_union_eq_add_of_disjoint (hfoel : IsFoelner G μ u F) (s t : Set X) (h
t : MeasurableSet t) (hdisj : Disjoint s t) : mean μ u F (s union t) = mean μ u 
F s + mean μ u F t
参数：hfoel : IsFoelner G μ u F；s t : Set X；ht : MeasurableSet t；hdisj : Disjoint s
 t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_unique_of_eventuallyEq`：tendsto_nhds_unique_of_eventuallyEq
 [T2Space X] {f g : Y -> X} {l : Filter Y} {a b : X} [NeBot l] (ha : Tendsto f l
 (𝓝 a)) (hb : Tendsto g l…
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `IsFoelner.tendsto_nhds_mean`：tendsto_nhds_mean (hfoel : IsFoelner G μ u 
F) (s : Set X) : Tendsto (fun i => μ (s inter F i) / μ (F i)) u (𝓝 (mean μ u F s
))
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `IsFoelner.eventually_measurableSet`：∀ {G : Type u_1} {X : Type u_2} [ins
t : MeasurableSpace X] {μ : MeasureTheory.Measure X} [inst_1 : Group G]   [inst_
2 : MulAction G X] {ι : …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_inter_distrib_right`：union_inter_distrib_right (s t u : Set α)
 : (s union t) inter u = s inter u union t inter u
· 使用定理 `MeasureTheory.measure_union`：measure_union (hd : Disjoint s₁ s₂) (h : Me
asurableSet s₂) : μ (s₁ union s₂) = μ s₁ + μ s₂
· 使用定理 `Disjoint.inter_right`：inter_right (u : Set α) (h : Disjoint s t) : Disjo
int s (t inter u)
· 使用定理 `Disjoint.inter_left`：inter_left (u : Set α) (h : Disjoint s t) : Disjoin
t (s inter u) t
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `ENNReal.add_div`：∀ {a b c : ENNReal}, (a + b) / c = a / c + b / c
-/
theorem mean_union_eq_add_of_disjoint (hfoel : IsFoelner G μ u F)
    (s t : Set X) (ht : MeasurableSet t) (hdisj : Disjoint s t) :
    mean μ u F (s ∪ t) = mean μ u F s + mean μ u F t := by
  refine tendsto_nhds_unique_of_eventuallyEq
    (hfoel.tendsto_nhds_mean _) (hfoel.tendsto_nhds_mean _ |>.add <| hfoel.tendsto_nhds_mean _) ?_
  filter_upwards [hfoel.eventually_measurableSet] with i hi
  rw [union_inter_distrib_right,
    measure_union (hdisj.inter_left _ |>.inter_right _) (ht.inter hi), ENNReal.add_div]

@[to_additive]
/-
**IsFoelner.tendsto_meas_smul_symmDiff_smul** 是 Mathlib 中的一个定理，位于命名空间 `IsFoelner
`。
形式化陈述：tendsto_meas_smul_symmDiff_smul [SMulInvariantMeasure G X μ] (hfoel : IsFo
elner G μ u F) (g h : G) : Tendsto (fun i => μ ((g • F i) ∆ (h • F i)) / μ (F i)
) u (𝓝 0)
参数：hfoel : IsFoelner G μ u F；g h : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.measure_inv_smul_symmDiff`：measure_inv_smul_symmDiff (c : 
G) (s t : Set α) : μ ((c⁻¹ • s) ∆ t) = μ (s ∆ (c • t))
· 使用定理 `IsFoelner.tendsto_meas_smul_symmDiff`：∀ {G : Type u_1} {X : Type u_2} [i
nst : MeasurableSpace X] {μ : MeasureTheory.Measure X} [inst_1 : Group G]   [ins
t_2 : MulAction G X] {ι : …
-/
theorem tendsto_meas_smul_symmDiff_smul [SMulInvariantMeasure G X μ]
    (hfoel : IsFoelner G μ u F) (g h : G) :
    Tendsto (fun i ↦ μ ((g • F i) ∆ (h • F i)) / μ (F i)) u (𝓝 0) := by
  simpa [← smul_smul] using hfoel.tendsto_meas_smul_symmDiff (h⁻¹ * g)

@[to_additive]
/-
**IsFoelner.mean_smul_eq_mean_smul** 是 Mathlib 中的一个定理，位于命名空间 `IsFoelner`。
形式化陈述：mean_smul_eq_mean_smul [SMulInvariantMeasure G X μ] (hfoel : IsFoelner G μ
 u F) (g h : G) (s : Set X) : mean μ u F (g • s) = mean μ u F (h • s)
参数：hfoel : IsFoelner G μ u F；g h : G；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `le_of_tendsto_of_tendsto`：le_of_tendsto_of_tendsto {f g : β -> α} {b : F
ilter β} {a₁ a₂ : α} [hb : NeBot b] (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g b 
(𝓝 a₂)) (h : f…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `IsFoelner.tendsto_nhds_mean`：tendsto_nhds_mean (hfoel : IsFoelner G μ u 
F) (s : Set X) : Tendsto (fun i => μ (s inter F i) / μ (F i)) u (𝓝 (mean μ u F s
))
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `IsFoelner.tendsto_meas_smul_symmDiff_smul`：tendsto_meas_smul_symmDiff_sm
ul [SMulInvariantMeasure G X μ] (hfoel : IsFoelner G μ u F) (g h : G) : Tendsto 
(fun i => μ ((g • F i) ∆ (h • F…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `IsFoelner.eventually_meas_ne_zero`：∀ {G : Type u_1} {X : Type u_2} [inst
 : MeasurableSpace X] {μ : MeasureTheory.Measure X} [inst_1 : Group G]   [inst_2
 : MulAction G X] {ι : …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `ENNReal.sub_div`：∀ {a b c : ENNReal}, (0 < b → b < a → c ≠ 0) → (a - b) 
/ c = a / c - b / c
· 使用定理 `ENNReal.div_le_div_right`：∀ {a b : ENNReal}, a ≤ b → ∀ (c : ENNReal), a 
/ c ≤ b / c
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.inter_symmDiff_distrib_left`：inter_symmDiff_distrib_left (s t u : Se
t α) : s inter t ∆ u = (s inter t) ∆ (s inter u)
· 使用定理 `MeasureTheory.le_measure_symmDiff`：le_measure_symmDiff : μ s₁ - μ s₂ <= 
μ (s₁ ∆ s₂)
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
-/
theorem mean_smul_eq_mean_smul [SMulInvariantMeasure G X μ]
    (hfoel : IsFoelner G μ u F) (g h : G) (s : Set X) :
    mean μ u F (g • s) = mean μ u F (h • s) := by
  suffices hle : ∀ g h, mean μ u F (g • s) ≤ mean μ u F (h • s) by
    exact le_antisymm (hle g h) (hle h g)
  intro g h
  rw [← add_zero <| mean μ u F (h • s)]
  refine le_of_tendsto_of_tendsto
    (hfoel.tendsto_nhds_mean (g • s))
    (hfoel.tendsto_nhds_mean (h • s) |>.add <| hfoel.tendsto_meas_smul_symmDiff_smul g⁻¹ h⁻¹) ?_
  filter_upwards [hfoel.eventually_meas_ne_zero] with i hi
  rw [← tsub_le_iff_left, ← ENNReal.sub_div <| fun _ _ ↦ hi]
  refine ENNReal.div_le_div_right (le_trans ?_ (measure_mono <| @inter_subset_right _ s _)) _
  simpa [inter_symmDiff_distrib_left, ← measure_inter_inv_smul] using le_measure_symmDiff

@[to_additive]
/-
**IsFoelner.mean_smul_eq_mean** 是 Mathlib 中的一个定理，位于命名空间 `IsFoelner`。
形式化陈述：mean_smul_eq_mean [SMulInvariantMeasure G X μ] (hfoel : IsFoelner G μ u F)
 (g : G) (s : Set X) : mean μ u F (g • s) = mean μ u F s
参数：hfoel : IsFoelner G μ u F；g : G；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `IsFoelner.mean_smul_eq_mean_smul`：mean_smul_eq_mean_smul [SMulInvariantM
easure G X μ] (hfoel : IsFoelner G μ u F) (g h : G) (s : Set X) : mean μ u F (g 
• s) = mean μ u F (h •…
-/
theorem mean_smul_eq_mean [SMulInvariantMeasure G X μ]
    (hfoel : IsFoelner G μ u F) (g : G) (s : Set X) :
    mean μ u F (g • s) = mean μ u F s := by
  simpa using hfoel.mean_smul_eq_mean_smul g 1 s

/-- If there exists a non-trivial Følner filter with respect to some group `G` acting on a measure
    space `X`, then there exists a `G`-invariant finitely additive probability measure on `X`. -/
@[to_additive
/-- If there exists a non-trivial Følner filter with respect to some additive group
    `G` acting on a measure space `X`, then there exists a `G`-invariant finitely additive
    probability measure on `X`. -/]
/-
**IsFoelner.amenable** 是 Mathlib 中的一个定理，位于命名空间 `IsFoelner`。
形式化陈述：amenable [SMulInvariantMeasure G X μ] [NeBot l] (hfoel : IsFoelner G μ l F
) : exists m : Set X -> Real>=0∞, m .univ = 1 ∧ (forall s t, MeasurableSet t -> 
Disjoint s t -> m (s union t) = m s + m t) ∧ forall (g : G) (s : Set X), m (g • 
s) = m s
参数：hfoel : IsFoelner G μ l F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFoelner.mean_univ_eq_one`：mean_univ_eq_one (hfoel : IsFoelner G μ u F)
 : mean μ u F .univ = 1
· 使用定理 `IsFoelner.mono`：mono {l' : Filter ι} (hfoel : IsFoelner G μ l F) (hle : 
l' <= l) : IsFoelner G μ l' F where eventually_measurableSet
· 使用定理 `Ultrafilter.of_le`：of_le (f : Filter α) [NeBot f] : ↑(of f) <= f
· 使用定理 `IsFoelner.mean_union_eq_add_of_disjoint`：mean_union_eq_add_of_disjoint (
hfoel : IsFoelner G μ u F) (s t : Set X) (ht : MeasurableSet t) (hdisj : Disjoin
t s t) : mean μ u F (s union …
· 使用定理 `IsFoelner.mean_smul_eq_mean`：mean_smul_eq_mean [SMulInvariantMeasure G X
 μ] (hfoel : IsFoelner G μ u F) (g : G) (s : Set X) : mean μ u F (g • s) = mean 
μ u F s
-/
theorem amenable [SMulInvariantMeasure G X μ] [NeBot l] (hfoel : IsFoelner G μ l F) :
    ∃ m : Set X → ℝ≥0∞, m .univ = 1 ∧
      (∀ s t, MeasurableSet t → Disjoint s t → m (s ∪ t) = m s + m t) ∧
        ∀ (g : G) (s : Set X), m (g • s) = m s := by
  use mean μ (Ultrafilter.of l) F
  refine ⟨?_, ?_, ?_⟩
  · exact (hfoel.mono <| Ultrafilter.of_le l).mean_univ_eq_one
  · exact (hfoel.mono <| Ultrafilter.of_le l).mean_union_eq_add_of_disjoint
  · exact (hfoel.mono <| Ultrafilter.of_le l).mean_smul_eq_mean

end IsFoelner

variable (G μ) in
/-- The maximal Følner filter with respect to some group `G` acting on a
    measure space `X` is the pullback of `𝓝 0` along the map `s ↦ μ (g • s) / μ s`
    on measurable sets of finite non-zero measure. -/
@[to_additive maxAddFoelner
/-- The maximal Følner filter with respect to some additive group `G` acting
    on a measure space `X` is the pullback of `𝓝 0` along the map `s ↦ μ (g +ᵥ s) / μ s`
    on measurable sets of finite non-zero measure. -/]
/-
**maxFoelner** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：maxFoelner : Filter (Set X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def maxFoelner : Filter (Set X) :=
  𝓟 {s : Set X | MeasurableSet s ∧ μ s ≠ 0 ∧ μ s ≠ ∞} ⊓
  ⨅ (g : G), comap (fun s ↦ μ ((g • s) ∆ s) / μ s) (𝓝 0)

variable (l F) in
@[to_additive isAddFoelner_iff_tendsto]
/-
**isFoelner_iff_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isFoelner_iff_tendsto : IsFoelner G μ l F ↔ Tendsto F l (maxFoelner G μ)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isFoelner_iff_tendsto : IsFoelner G μ l F ↔ Tendsto F l (maxFoelner G μ) := by
  simp [maxFoelner, tendsto_inf, tendsto_iInf, isFoelner_iff, Function.comp_def, and_assoc]

variable (G μ) in
@[to_additive isAddFoelner_maxAddFoelner]
/-
**isFoelner_maxFoelner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isFoelner_maxFoelner : IsFoelner G μ (maxFoelner G μ) id
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isFoelner_iff_tendsto`：isFoelner_iff_tendsto : IsFoelner G μ l F ↔ Tends
to F l (maxFoelner G μ)
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
-/
theorem isFoelner_maxFoelner : IsFoelner G μ (maxFoelner G μ) id :=
  isFoelner_iff_tendsto _ _ |>.2 <| @tendsto_id _ (maxFoelner G μ)

@[to_additive amenable_of_maxAddFoelner_neBot]
/-
**amenable_of_maxFoelner_neBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：amenable_of_maxFoelner_neBot [SMulInvariantMeasure G X μ] [NeBot (maxFoeln
er G μ)] : exists m : Set X -> Real>=0∞, m .univ = 1 ∧ (forall s t, MeasurableSe
t t -> Disjoint s t -> m (s union t) = m s + m t) ∧ forall (g : G) (s : Set X), 
m (g • s) = m s
参数：maxFoelner G μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFoelner.amenable`：amenable [SMulInvariantMeasure G X μ] [NeBot l] (hfo
el : IsFoelner G μ l F) : exists m : Set X -> Real>=0∞, m .univ = 1 ∧ (forall s 
t, Measu…
· 使用定理 `isFoelner_maxFoelner`：isFoelner_maxFoelner : IsFoelner G μ (maxFoelner G
 μ) id
-/
theorem amenable_of_maxFoelner_neBot [SMulInvariantMeasure G X μ] [NeBot (maxFoelner G μ)] :
    ∃ m : Set X → ℝ≥0∞, m .univ = 1 ∧
      (∀ s t, MeasurableSet t → Disjoint s t → m (s ∪ t) = m s + m t) ∧
        ∀ (g : G) (s : Set X), m (g • s) = m s :=
  IsFoelner.amenable <| isFoelner_maxFoelner G μ
