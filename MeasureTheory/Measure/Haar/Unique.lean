/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.EverywherePos
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.ContinuousMap.Ordered

/-!
# Uniqueness of Haar measure in locally compact groups

## Main results

In a locally compact group, we prove that two left-invariant measures `μ'` and `μ` which are finite
on compact sets coincide, up to a normalizing scalar that we denote with `haarScalarFactor μ' μ`,
in the following sense:
* `integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport`: they give the same value to the
  integral of continuous compactly supported functions, up to a scalar.
* `measure_isMulInvariant_eq_smul_of_isCompact_closure`: they give the same value to sets with
  compact closure, up to a scalar.
* `measure_isHaarMeasure_eq_smul_of_isOpen`: they give the same value to open sets, up to a scalar.

To get genuine equality of measures, we typically need additional regularity assumptions:

* `isMulLeftInvariant_eq_smul_of_innerRegular`: two left invariant measures which are
  inner regular coincide up to a scalar.
* `isMulLeftInvariant_eq_smul_of_regular`: two left invariant measures which are
  regular coincide up to a scalar.
* `isHaarMeasure_eq_smul`: in a second countable space, two Haar measures coincide up to a
  scalar.
* `isMulInvariant_eq_smul_of_compactSpace`: two left-invariant measures on a compact group coincide
  up to a scalar.
* `isHaarMeasure_eq_of_isProbabilityMeasure`: two Haar measures which are probability measures
  coincide exactly.

In general, uniqueness statements for Haar measures in the literature make some assumption of
regularity, either regularity or inner regularity. We have tried to minimize the assumptions in the
theorems above, and cover the different results that exist in the literature.

## Implementation

The first result `integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport` is classical. To prove
it, we use a change of variables to express integrals with respect to a left-invariant measure as
integrals with respect to a given right-invariant measure (with a suitable density function).
The uniqueness readily follows.

Uniqueness results for the measure of compact sets and open sets, without any regularity assumption,
are significantly harder. They rely on the completion-regularity of the standard regular Haar
measure. We follow McQuillan's answer at https://mathoverflow.net/questions/456670/.

On second-countable groups, one can arrive to slightly different uniqueness results by using that
the operations are measurable. In particular, one can get uniqueness assuming σ-finiteness of
the measures but discarding the assumption that they are finite on compact sets. See
`haarMeasure_unique` in the file `Mathlib/MeasureTheory/Measure/Haar/Basic.lean`.

## References

[Halmos, Measure Theory][halmos1950measure]
[Fremlin, *Measure Theory* (volume 4)][fremlin_vol4]
-/

@[expose] public section

open Filter Set TopologicalSpace Function MeasureTheory Measure
open scoped Uniformity Topology ENNReal Pointwise NNReal

namespace MeasureTheory

/-- The parameterized integral `x ↦ ∫ y, g (y⁻¹ * x) ∂μ` depends continuously on `y` when `g` is a
compactly supported continuous function on a topological group `G`, and `μ` is finite on compact
sets. -/
@[to_additive /-- The parameterized integral `x ↦ ∫ y, g (-y + x) ∂μ` depends continuously on `y`
when `g` is a compactly supported continuous function on a topological additive group `G`, and `μ`
is finite on compact sets. -/]
/-
**MeasureTheory.continuous_integral_apply_inv_mul** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory`。
形式化陈述：continuous_integral_apply_inv_mul {G : Type*} [TopologicalSpace G] [Locall
yCompactSpace G] [Group G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpac
e G] {μ : Measure G} [IsFiniteMeasureOnCompacts μ] {E : Type*} [NormedAddCommGro
up E] [NormedSpace Real E] {g : G -> E} (hg : Continuous g) (h'g : HasCompactSup
port g) : Continuous (fun (x : G) => ∫ y, g (y⁻¹ * x) ∂μ)
参数：hg : Continuous g；h'g : HasCompactSupport g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `WeaklyLocallyCompactSpace.exists_compact_mem_nhds`：∀ {X : Type u_3} {ins
t : TopologicalSpace X} [self : WeaklyLocallyCompactSpace X] (x : X), ∃ s, IsCom
pact s ∧ s ∈ nhds x
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用引理 `IsCompact.smul_set`：IsCompact.smul_set {k : Set M} {u : Set X} (hk : IsC
ompact k) (hu : IsCompact u) : IsCompact (k • u)
· 使用定理 `IsTopologicalTorsor.toContinuousSMul`：∀ {V : Type u_1} {inst : Group V} 
{inst_1 : TopologicalSpace V} {P : Type u_2} {inst_2 : Torsor V P}   {inst_3 : T
opologicalSpace P} [self :…
· 使用定理 `instIsTopologicalTorsor`：∀ {G : Type u_1} [inst : Group G] [inst_1 : Top
ologicalSpace G] [IsTopologicalGroup G], IsTopologicalTorsor G
· 使用定理 `IsCompact.inv`：IsCompact.inv (hs : IsCompact s) : IsCompact s⁻¹
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用引理 `continuousOn_integral_of_compact_support`：continuousOn_integral_of_compa
ct_support {f : X -> Y -> E} {s : Set X} {k : Set Y} [IsFiniteMeasureOnCompacts 
μ] (hk : IsCompact k) (hf : Co…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Continuous.inv`：Continuous.inv (hf : Continuous f) : Continuous f⁻¹
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `subset_tsupport`：∀ {X : Type u_1} {α : Type u_2} [inst : Zero α] [inst_1
 : TopologicalSpace X] (f : X → α),   Function.support f ⊆ tsupport f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousOn.continuousAt`：ContinuousOn.continuousAt (h : ContinuousOn f
 s) (hx : s in 𝓝 x) : ContinuousAt f x
-/
lemma continuous_integral_apply_inv_mul
    {G : Type*} [TopologicalSpace G] [LocallyCompactSpace G] [Group G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    {μ : Measure G} [IsFiniteMeasureOnCompacts μ] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : G → E}
    (hg : Continuous g) (h'g : HasCompactSupport g) :
    Continuous (fun (x : G) ↦ ∫ y, g (y⁻¹ * x) ∂μ) := by
  let k := tsupport g
  have k_comp : IsCompact k := h'g
  apply continuous_iff_continuousAt.2 (fun x₀ ↦ ?_)
  obtain ⟨t, t_comp, ht⟩ : ∃ t, IsCompact t ∧ t ∈ 𝓝 x₀ := exists_compact_mem_nhds x₀
  let k' : Set G := t • k⁻¹
  have k'_comp : IsCompact k' := t_comp.smul_set k_comp.inv
  have A : ContinuousOn (fun (x : G) ↦ ∫ y, g (y⁻¹ * x) ∂μ) t := by
    apply continuousOn_integral_of_compact_support k'_comp
    · exact (hg.comp (continuous_snd.inv.mul continuous_fst)).continuousOn
    · intro p x hp hx
      contrapose! hx
      refine ⟨p, hp, p⁻¹ * x, ?_, by simp⟩
      simpa only [Set.mem_inv, mul_inv_rev, inv_inv] using subset_tsupport _ hx
  exact A.continuousAt ht

namespace Measure

section Group

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

/-!
### Uniqueness of integrals of compactly supported functions

Two left invariant measures coincide when integrating continuous compactly supported functions,
up to a scalar that we denote with `haarScalarFactor μ' μ `.

This is proved by relating the integral for arbitrary left invariant and right invariant measures,
applying a version of Fubini.
As one may use the same right invariant measure, this shows that two different left invariant
measures will give the same integral, up to some fixed scalar.
-/

/-- In a group with a left invariant measure `μ` and a right invariant measure `ν`, one can express
integrals with respect to `μ` as integrals with respect to `ν` up to a constant scaling factor
(given in the statement as `∫ x, g x ∂μ` where `g` is a fixed reference function) and an
explicit density `y ↦ 1/∫ z, g (z⁻¹ * y) ∂ν`. -/
@[to_additive /-- In an additive group with a left invariant measure `μ` and a right invariant
measure `ν`, one can express integrals with respect to `μ` as integrals with respect to `ν` up to a
constant scaling factor (given in the statement as `∫ x, g x ∂μ` where `g` is a fixed reference
function) and an explicit density `y ↦ 1/∫ z, g (-z + y) ∂ν`. -/]
/-
**MeasureTheory.Measure.integral_isMulLeftInvariant_isMulRightInvariant_combo** 
是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：integral_isMulLeftInvariant_isMulRightInvariant_combo {μ ν : Measure G} [I
sFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] [IsMulLeftInvariant μ]
 [IsMulRightInvariant ν] [IsOpenPosMeasure ν] {f g : G -> Real} (hf : Continuous
 f) (h'f : HasCompactSupport f) (hg : Continuous g) (h'g : HasCompactSupport g) 
(g_nonneg : 0 <= g) {x₀ : G} (g_pos : g x₀ != 0) : ∫ x, f x ∂μ = (∫ y, f y * (∫ 
z, g (z⁻¹ * y) ∂ν)⁻¹ ∂ν) * ∫ x, g x ∂μ
参数：hf : Continuous f；h'f : HasCompactSupport f；hg : Continuous g；h'g : HasCompac
tSupport g；g_nonneg : 0 <= g；g_pos : g x₀ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasCompactSupport.eq_zero_or_locallyCompactSpace_of_group`：HasCompactSup
port.eq_zero_or_locallyCompactSpace_of_group [TopologicalSpace α] [Zero α] [T1Sp
ace α] {f : G -> α} (hf : HasCompactSupport f) …
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeasureTheory.continuous_integral_apply_inv_mul`：continuous_integral_app
ly_inv_mul {G : Type*} [TopologicalSpace G] [LocallyCompactSpace G] [Group G] [I
sTopologicalGroup G] [MeasurableSpace…
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Continuous.mul_const`：Continuous.mul_const (hf : Continuous f) (b : M) :
 Continuous (f · * b)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integral_pos_iff_support_of_nonneg`：integral_pos_iff_suppo
rt_of_nonneg {f : α -> Real} (hf : 0 <= f) (hfi : Integrable f μ) : (0 < ∫ x, f 
x ∂μ) ↔ 0 < μ (Function.support f)
· 使用定理 `Continuous.integrable_of_hasCompactSupport`：Continuous.integrable_of_has
CompactSupport (hf : Continuous f) (hcf : HasCompactSupport f) : Integrable f μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasCompactSupport.comp_homeomorph`：∀ {X : Type u_9} {Y : Type u_10} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {M : Type u_11}   [inst_2 
: Zero M] {f : Y → M}, …
· 使用定理 `IsOpen.measure_pos`：∀ {X : Type u_1} [inst : TopologicalSpace X] {m : Me
asurableSpace X} (μ : MeasureTheory.Measure X) [μ.IsOpenPosMeasure]   {U : Set X
}, IsOpe…
· 使用定理 `Continuous.isOpen_support`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topol
ogicalSpace X] [T1Space X] [inst_2 : Zero X] [inst_3 : TopologicalSpace Y]   {f 
: Y → X}, Conti…
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
（共 78 条，此处仅展示前 30 条）
-/
lemma integral_isMulLeftInvariant_isMulRightInvariant_combo
    {μ ν : Measure G} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    [IsMulLeftInvariant μ] [IsMulRightInvariant ν] [IsOpenPosMeasure ν]
    {f g : G → ℝ} (hf : Continuous f) (h'f : HasCompactSupport f)
    (hg : Continuous g) (h'g : HasCompactSupport g) (g_nonneg : 0 ≤ g) {x₀ : G} (g_pos : g x₀ ≠ 0) :
    ∫ x, f x ∂μ = (∫ y, f y * (∫ z, g (z⁻¹ * y) ∂ν)⁻¹ ∂ν) * ∫ x, g x ∂μ := by
  -- The group has to be locally compact, otherwise all integrals vanish and the result is trivial.
  rcases h'f.eq_zero_or_locallyCompactSpace_of_group hf with Hf | Hf
  · simp [Hf]
  let D : G → ℝ := fun (x : G) ↦ ∫ y, g (y⁻¹ * x) ∂ν
  have D_cont : Continuous D := continuous_integral_apply_inv_mul hg h'g
  have D_pos : ∀ x, 0 < D x := by
    intro x
    have C : Continuous (fun y ↦ g (y⁻¹ * x)) := by fun_prop
    apply (integral_pos_iff_support_of_nonneg _ _).2
    · apply C.isOpen_support.measure_pos ν
      exact ⟨x * x₀⁻¹, by simpa using g_pos⟩
    · exact fun y ↦ g_nonneg (y⁻¹ * x)
    · apply C.integrable_of_hasCompactSupport
      exact h'g.comp_homeomorph ((Homeomorph.inv G).trans (Homeomorph.mulRight x))
  calc
  ∫ x, f x ∂μ = ∫ x, f x * (D x)⁻¹ * D x ∂μ := by
    congr with x; rw [mul_assoc, inv_mul_cancel₀ (D_pos x).ne', mul_one]
  _ = ∫ x, (∫ y, f x * (D x)⁻¹ * g (y⁻¹ * x) ∂ν) ∂μ := by simp_rw [D, integral_const_mul]
  _ = ∫ y, (∫ x, f x * (D x)⁻¹ * g (y⁻¹ * x) ∂μ) ∂ν := by
      apply integral_integral_swap_of_hasCompactSupport
      · apply Continuous.mul
        · exact (hf.comp continuous_fst).mul
            ((D_cont.comp continuous_fst).inv₀ (fun x ↦ (D_pos _).ne'))
        · exact hg.comp (continuous_snd.inv.mul continuous_fst)
      · let K := tsupport f
        have K_comp : IsCompact K := h'f
        let L := tsupport g
        have L_comp : IsCompact L := h'g
        let M := (fun (p : G × G) ↦ p.1 * p.2⁻¹) '' (K ×ˢ L)
        have M_comp : IsCompact M :=
          (K_comp.prod L_comp).image (continuous_fst.mul continuous_snd.inv)
        have M'_comp : IsCompact (closure M) := M_comp.closure
        have : ∀ (p : G × G), p ∉ K ×ˢ closure M → f p.1 * (D p.1)⁻¹ * g (p.2⁻¹ * p.1) = 0 := by
          rintro ⟨x, y⟩ hxy
          by_cases H : x ∈ K; swap
          · simp [image_eq_zero_of_notMem_tsupport H]
          have : g (y⁻¹ * x) = 0 := by
            apply image_eq_zero_of_notMem_tsupport
            contrapose hxy
            simp only [mem_prod, H, true_and]
            apply subset_closure
            simp only [M, mem_image, mem_prod, Prod.exists]
            exact ⟨x, y⁻¹ * x, ⟨H, hxy⟩, by group⟩
          simp [this]
        apply HasCompactSupport.intro' (K_comp.prod M'_comp) ?_ this
        exact (isClosed_tsupport f).prod isClosed_closure
  _ = ∫ y, (∫ x, f (y * x) * (D (y * x))⁻¹ * g x ∂μ) ∂ν := by
      congr with y
      rw [← integral_mul_left_eq_self _ y]
      simp
  _ = ∫ x, (∫ y, f (y * x) * (D (y * x))⁻¹ * g x ∂ν) ∂μ := by
      apply (integral_integral_swap_of_hasCompactSupport _ _).symm
      · apply Continuous.mul ?_ (hg.comp continuous_fst)
        exact (hf.comp (continuous_snd.mul continuous_fst)).mul
          ((D_cont.comp (continuous_snd.mul continuous_fst)).inv₀ (fun x ↦ (D_pos _).ne'))
      · let K := tsupport f
        have K_comp : IsCompact K := h'f
        let L := tsupport g
        have L_comp : IsCompact L := h'g
        let M := (fun (p : G × G) ↦ p.1 * p.2⁻¹) '' (K ×ˢ L)
        have M_comp : IsCompact M :=
          (K_comp.prod L_comp).image (continuous_fst.mul continuous_snd.inv)
        have M'_comp : IsCompact (closure M) := M_comp.closure
        have : ∀ (p : G × G), p ∉ L ×ˢ closure M →
            f (p.2 * p.1) * (D (p.2 * p.1))⁻¹ * g p.1 = 0 := by
          rintro ⟨x, y⟩ hxy
          by_cases H : x ∈ L; swap
          · simp [image_eq_zero_of_notMem_tsupport H]
          have : f (y * x) = 0 := by
            apply image_eq_zero_of_notMem_tsupport
            contrapose hxy
            simp only [mem_prod, H, true_and]
            apply subset_closure
            simp only [M, mem_image, mem_prod, Prod.exists]
            exact ⟨y * x, x, ⟨hxy, H⟩, by group⟩
          simp [this]
        apply HasCompactSupport.intro' (L_comp.prod M'_comp) ?_ this
        exact (isClosed_tsupport g).prod isClosed_closure
  _ = ∫ x, (∫ y, f y * (D y)⁻¹ ∂ν) * g x ∂μ := by
      simp_rw [integral_mul_const]
      congr with x
      conv_rhs => rw [← integral_mul_right_eq_self _ x]
  _ = (∫ y, f y * (D y)⁻¹ ∂ν) * ∫ x, g x ∂μ := integral_const_mul _ _

/-- Given two left-invariant measures which are finite on
compacts, they coincide in the following sense: they give the same value to the integral of
continuous compactly supported functions, up to a multiplicative constant. -/
@[to_additive exists_integral_isAddLeftInvariant_eq_smul_of_hasCompactSupport
/-- Given two left-invariant measures which are finite on
compacts, they coincide in the following sense: they give the same value to the integral of
continuous compactly supported functions, up to a multiplicative constant. -/]
/-
**MeasureTheory.Measure.exists_integral_isMulLeftInvariant_eq_smul_of_hasCompact
Support** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：exists_integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport (μ' μ : Me
asure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'
] : exists (c : Real>=0), forall (f : G -> Real), Continuous f -> HasCompactSupp
ort f -> ∫ x, f x ∂μ' = ∫ x, f x ∂(c • μ)
参数：μ' μ : Measure G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `exists_continuous_nonneg_pos`：exists_continuous_nonneg_pos [RegularSpace
 X] [LocallyCompactSpace X] (x : X) : exists f : C(X, Real), HasCompactSupport f
 ∧ 0 <= (f : X -> …
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero`：Continuous.
integral_pos_of_hasCompactSupport_nonneg_nonzero [IsFiniteMeasureOnCompacts μ] {
f : X -> Real} {x : X} (f_cont : Continuous f) (f…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u_3}
 {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}   {
μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Partia
lOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a⁻¹ ↔ 0 ≤ a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `MeasureTheory.integral_nonneg`：integral_nonneg {f : α -> E} (hf : 0 <= f
) : 0 <= ∫ x, f x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用引理 `MeasureTheory.Measure.integral_isMulLeftInvariant_isMulRightInvariant_co
mbo`：integral_isMulLeftInvariant_isMulRightInvariant_combo {μ ν : Measure G} [Is
FiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] [IsMulLe…
· 使用定理 `MeasureTheory.Measure.IsFiniteMeasureOnCompacts.inv`：∀ {G : Type u_1} [i
nst : MeasurableSpace G] [inst_1 : TopologicalSpace G] [BorelSpace G] {μ : Measu
reTheory.Measure G}   [inst_3 : Group G] …
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsMulLeftInvariant`：∀ {G : Type u_
3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}  
 {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `MeasureTheory.Measure.inv.instIsMulRightInvariant`：∀ {G : Type u_1} [ins
t : MeasurableSpace G] [inst_1 : DivisionMonoid G] [MeasurableMul G] [Measurable
Inv G]   {μ : MeasureTheory.Measure G} …
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `ContinuousInv.measurableInv`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Inv γ]   [ContinuousInv 
γ], MeasurableInv…
· 使用定理 `MeasureTheory.Measure.IsOpenPosMeasure.inv`：∀ {G : Type u_1} [inst : Mea
surableSpace G] [inst_1 : TopologicalSpace G] [BorelSpace G] {μ : MeasureTheory.
Measure G}   [inst_3 : Group G] …
（共 50 条，此处仅展示前 30 条）
-/
lemma exists_integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport (μ' μ : Measure G)
    [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] :
    ∃ (c : ℝ≥0), ∀ (f : G → ℝ), Continuous f → HasCompactSupport f →
      ∫ x, f x ∂μ' = ∫ x, f x ∂(c • μ) := by
  -- The group has to be locally compact, otherwise all integrals vanish and the result is trivial.
  by_cases H : LocallyCompactSpace G; swap
  · refine ⟨0, fun f f_cont f_comp ↦ ?_⟩
    rcases f_comp.eq_zero_or_locallyCompactSpace_of_group f_cont with hf | hf
    · simp [hf]
    · exact (H hf).elim
  -- Fix some nonzero continuous function with compact support `g`.
  obtain ⟨⟨g, g_cont⟩, g_comp, g_nonneg, g_one⟩ :
    ∃ (g : C(G, ℝ)), HasCompactSupport g ∧ 0 ≤ g ∧ g 1 ≠ 0 := exists_continuous_nonneg_pos 1
  have int_g_pos : 0 < ∫ x, g x ∂μ :=
    g_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero g_comp g_nonneg g_one
  -- The proportionality constant we are looking for will be the ratio of the integrals of `g`
  -- with respect to `μ'` and `μ`.
  let c : ℝ := (∫ x, g x ∂μ)⁻¹ * (∫ x, g x ∂μ')
  have c_nonneg : 0 ≤ c :=
    mul_nonneg (inv_nonneg.2 (integral_nonneg g_nonneg)) (integral_nonneg g_nonneg)
  refine ⟨.mk c c_nonneg, fun f f_cont f_comp ↦ ?_⟩
  /- use the lemma `integral_mulLeftInvariant_mulRightInvariant_combo` for `μ` and then `μ'`
  to reexpress the integral of `f` as the integral of `g` times a factor which only depends
  on a right-invariant measure `ν`. We use `ν = μ.inv` for convenience. -/
  let ν := μ.inv
  have A : ∫ x, f x ∂μ = (∫ y, f y * (∫ z, g (z⁻¹ * y) ∂ν)⁻¹ ∂ν) * ∫ x, g x ∂μ :=
    integral_isMulLeftInvariant_isMulRightInvariant_combo f_cont f_comp g_cont g_comp g_nonneg g_one
  rw [← mul_inv_eq_iff_eq_mul₀ int_g_pos.ne'] at A
  have B : ∫ x, f x ∂μ' = (∫ y, f y * (∫ z, g (z⁻¹ * y) ∂ν)⁻¹ ∂ν) * ∫ x, g x ∂μ' :=
    integral_isMulLeftInvariant_isMulRightInvariant_combo f_cont f_comp g_cont g_comp g_nonneg g_one
  /- Since the `ν`-factor is the same for `μ` and `μ'`, this gives the result. -/
  rw [← A, mul_assoc, mul_comm] at B
  simp [B, integral_smul_nnreal_measure, c, NNReal.smul_def]

open scoped Classical in
/-- Given two left-invariant measures which are finite on compacts, `haarScalarFactor μ' μ` is a
scalar such that `∫ f dμ' = (haarScalarFactor μ' μ) ∫ f dμ` for any compactly supported continuous
function `f`.

Note that there is a dissymmetry in the assumptions between `μ'` and `μ`: the measure `μ'` needs
only be finite on compact sets, while `μ` has to be finite on compact sets and positive on open
sets, i.e., a Haar measure, to exclude for instance the case where `μ = 0`, where the definition
doesn't make sense. -/
@[to_additive /-- Given two left-invariant measures which are finite on compacts,
`addHaarScalarFactor μ' μ` is a scalar such that `∫ f dμ' = (addHaarScalarFactor μ' μ) ∫ f dμ` for
any compactly supported continuous function `f`.

Note that there is a dissymmetry in the assumptions between `μ'` and `μ`: the measure `μ'` needs
only be finite on compact sets, while `μ` has to be finite on compact sets and positive on open
sets, i.e., an additive Haar measure, to exclude for instance the case where `μ = 0`, where the
definition doesn't make sense. -/]
/-
**MeasureTheory.Measure.haarScalarFactor** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：haarScalarFactor (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCo
mpacts μ'] [IsMulLeftInvariant μ'] : Real>=0
参数：μ' μ : Measure G。
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.exists_integral_isMulLeftInvariant_eq_smul_of_hasC
ompactSupport`：exists_integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport (
μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLe…
-/
noncomputable def haarScalarFactor
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] :
    ℝ≥0 :=
  if ¬ LocallyCompactSpace G then 1
  else (exists_integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport μ' μ).choose

/-- Two left invariant measures integrate in the same way continuous compactly supported functions,
up to the scalar `haarScalarFactor μ' μ`. See also
`measure_isMulInvariant_eq_smul_of_isCompact_closure`, which gives the same result for compact
sets, and `measure_isHaarMeasure_eq_smul_of_isOpen` for open sets. -/
@[to_additive integral_isAddLeftInvariant_eq_smul_of_hasCompactSupport
/-- Two left invariant measures integrate in the same way continuous compactly supported functions,
up to the scalar `addHaarScalarFactor μ' μ`. See also
`measure_isAddInvariant_eq_smul_of_isCompact_closure`, which gives the same result for compact
sets, and `measure_isAddHaarMeasure_eq_smul_of_isOpen` for open sets. -/]
/-
**MeasureTheory.Measure.integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport
** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport (μ' μ : Measure G
) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] {f : 
G -> Real} (hf : Continuous f) (h'f : HasCompactSupport f) : ∫ x, f x ∂μ' = ∫ x,
 f x ∂(haarScalarFactor μ' μ • μ)
参数：μ' μ : Measure G；hf : Continuous f；h'f : HasCompactSupport f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `HasCompactSupport.eq_zero_or_locallyCompactSpace_of_group`：HasCompactSup
port.eq_zero_or_locallyCompactSpace_of_group [TopologicalSpace α] [Zero α] [T1Sp
ace α] {f : G -> α} (hf : HasCompactSupport f) …
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeasureTheory.Measure.exists_integral_isMulLeftInvariant_eq_smul_of_hasC
ompactSupport`：exists_integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport (
μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLe…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ']
    {f : G → ℝ} (hf : Continuous f) (h'f : HasCompactSupport f) :
    ∫ x, f x ∂μ' = ∫ x, f x ∂(haarScalarFactor μ' μ • μ) := by
  rcases h'f.eq_zero_or_locallyCompactSpace_of_group hf with Hf | Hf
  · simp [Hf]
  · simp only [haarScalarFactor, Hf, not_true_eq_false, ite_false]
    exact (exists_integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport μ' μ).choose_spec
      f hf h'f

@[to_additive addHaarScalarFactor_eq_integral_div]
/-
**MeasureTheory.Measure.haarScalarFactor_eq_integral_div** 是 Mathlib 中的一个引理，位于命名
空间 `MeasureTheory.Measure`。
形式化陈述：haarScalarFactor_eq_integral_div (μ' μ : Measure G) [IsHaarMeasure μ] [IsF
initeMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] {f : G -> Real} (hf : Continu
ous f) (h'f : HasCompactSupport f) (int_nonzero : ∫ x, f x ∂μ != 0) : haarScalar
Factor μ' μ = (∫ x, f x ∂μ') / ∫ x, f x ∂μ
参数：μ' μ : Measure G；hf : Continuous f；h'f : HasCompactSupport f；int_nonzero : ∫ 
x, f x ∂μ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.integral_isMulLeftInvariant_eq_smul_of_hasCompactS
upport`：integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport (μ' μ : Measure
 G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvar…
· 使用定理 `EuclideanDomain.eq_div_of_mul_eq_left`：eq_div_of_mul_eq_left {a b c : R}
 (hb : b != 0) (h : a * b = c) : a = c / b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_smul_nnreal_measure`：integral_smul_nnreal_measure
 (f : α -> G) (c : Real>=0) : ∫ x, f x ∂(c • μ) = c • ∫ x, f x ∂μ
-/
lemma haarScalarFactor_eq_integral_div (μ' μ : Measure G) [IsHaarMeasure μ]
    [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] {f : G → ℝ} (hf : Continuous f)
    (h'f : HasCompactSupport f) (int_nonzero : ∫ x, f x ∂μ ≠ 0) :
    haarScalarFactor μ' μ = (∫ x, f x ∂μ') / ∫ x, f x ∂μ := by
  have := integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport μ' μ hf h'f
  rw [integral_smul_nnreal_measure] at this
  exact EuclideanDomain.eq_div_of_mul_eq_left int_nonzero this.symm

@[to_additive addHaarScalarFactor_eq_integral_div_of_continuous_nonneg_pos]
/-
**MeasureTheory.Measure.haarScalarFactor_eq_integral_div_of_continuous_nonneg_po
s** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：haarScalarFactor_eq_integral_div_of_continuous_nonneg_pos (μ' μ : Measure 
G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] {f :
 C(G, Real)} (hf : HasCompactSupport f ∧ 0 <= f ∧ f 1 != 0) : haarScalarFactor μ
' μ = (∫ x, f x ∂μ') / ∫ x, f x ∂μ
参数：μ' μ : Measure G；G, Real；hf : HasCompactSupport f ∧ 0 <= f ∧ f 1 != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero`：Continuous.
integral_pos_of_hasCompactSupport_nonneg_nonzero [IsFiniteMeasureOnCompacts μ] {
f : X -> Real} {x : X} (f_cont : Continuous f) (f…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u_3}
 {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}   {
μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun
· 使用引理 `MeasureTheory.Measure.haarScalarFactor_eq_integral_div`：haarScalarFactor
_eq_integral_div (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts
 μ'] [IsMulLeftInvariant μ'] {f : G -> Real}…
-/
lemma haarScalarFactor_eq_integral_div_of_continuous_nonneg_pos
    (μ' μ : Measure G) [IsHaarMeasure μ]
    [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ']
    {f : C(G, ℝ)} (hf : HasCompactSupport f ∧ 0 ≤ f ∧ f 1 ≠ 0) :
    haarScalarFactor μ' μ = (∫ x, f x ∂μ') / ∫ x, f x ∂μ := by
  obtain ⟨f_comp, f_nonneg, f_one⟩ := hf
  have int_f_ne_zero : ∫ (x : G), f x ∂μ ≠ 0 :=
    ne_of_gt (f.2.integral_pos_of_hasCompactSupport_nonneg_nonzero f_comp f_nonneg f_one)
  exact haarScalarFactor_eq_integral_div _ _ f.2 f_comp int_f_ne_zero

@[to_additive (attr := simp) addHaarScalarFactor_smul]
/-
**MeasureTheory.Measure.haarScalarFactor_smul** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：haarScalarFactor_smul [LocallyCompactSpace G] (μ' μ : Measure G) [IsHaarMe
asure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] {c : Real>=0} : 
haarScalarFactor (c • μ') μ = c • haarScalarFactor μ' μ
参数：μ' μ : Measure G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.IsFiniteMeasureOnCompacts.smul_nnreal`：∀ {α : Type u_1} {m
0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure α)
   [MeasureTheory.IsFiniteMeasureOnCompac…
· 使用定理 `exists_continuous_nonneg_pos`：exists_continuous_nonneg_pos [RegularSpace
 X] [LocallyCompactSpace X] (x : X) : exists f : C(X, Real), HasCompactSupport f
 ∧ 0 <= (f : X -> …
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `NNReal.coe_injective`：Function.Injective NNReal.toReal
· 使用引理 `MeasureTheory.Measure.haarScalarFactor_eq_integral_div_of_continuous_non
neg_pos`：haarScalarFactor_eq_integral_div_of_continuous_nonneg_pos (μ' μ : Measu
re G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInva…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_smul_nnreal_measure`：integral_smul_nnreal_measure
 (f : α -> G) (c : Real>=0) : ∫ x, f x ∂(c • μ) = c • ∫ x, f x ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `smul_div_assoc`：smul_div_assoc [DivInvMonoid β] [SMul α β] [IsScalarTowe
r α β β] (r : α) (x y : β) : r • x / y = r • (x / y)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma haarScalarFactor_smul [LocallyCompactSpace G] (μ' μ : Measure G) [IsHaarMeasure μ]
    [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] {c : ℝ≥0} :
    haarScalarFactor (c • μ') μ = c • haarScalarFactor μ' μ := by
  obtain ⟨g, hg⟩ := exists_continuous_nonneg_pos (1 : G)
  apply NNReal.coe_injective
  calc
    haarScalarFactor (c • μ') μ = (∫ x, g x ∂(c • μ')) / ∫ x, g x ∂μ :=
      haarScalarFactor_eq_integral_div_of_continuous_nonneg_pos _ _ hg
    _ = (c • (∫ x, g x ∂μ')) / ∫ x, g x ∂μ := by simp
    _ = c • ((∫ x, g x ∂μ') / ∫ x, g x ∂μ) := smul_div_assoc c _ _
    _ = c • haarScalarFactor μ' μ := by
      rw [← haarScalarFactor_eq_integral_div_of_continuous_nonneg_pos _ _ hg]

@[to_additive mul_addHaarScalarFactor_smul]
/-
**MeasureTheory.Measure.mul_haarScalarFactor_smul** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory.Measure`。
形式化陈述：mul_haarScalarFactor_smul [LocallyCompactSpace G] (μ' μ : Measure G) [IsHa
arMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] {c : Real>=0
} (hc : c != 0) : haveI : IsHaarMeasure (c • μ)
参数：μ' μ : Measure G；hc : c != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.nnreal_smul`：∀ {G : Type u_1} [inst 
: MeasurableSpace G] [inst_1 : Group G] [inst_2 : TopologicalSpace G]   (μ : Mea
sureTheory.Measure G) [μ.IsHaarMeasur…
· 使用定理 `exists_continuous_nonneg_pos`：exists_continuous_nonneg_pos [RegularSpace
 X] [LocallyCompactSpace X] (x : X) : exists f : C(X, Real), HasCompactSupport f
 ∧ 0 <= (f : X -> …
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `NNReal.coe_injective`：Function.Injective NNReal.toReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.haarScalarFactor_eq_integral_div_of_continuous_non
neg_pos`：haarScalarFactor_eq_integral_div_of_continuous_nonneg_pos (μ' μ : Measu
re G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInva…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.integral_smul_nnreal_measure`：integral_smul_nnreal_measure
 (f : α -> G) (c : Real>=0) : ∫ x, f x ∂(c • μ) = c • ∫ x, f x ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `NNReal.smul_def`：smul_def {M : Type*} [SMul Real M] (c : Real>=0) (x : M
) : c • x = (c : Real) • x
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用引理 `mul_div_mul_left`：mul_div_mul_left (a b : G₀) (hc : c != 0) : c * a / (c
 * b) = a / b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma mul_haarScalarFactor_smul [LocallyCompactSpace G] (μ' μ : Measure G)
    [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] {c : ℝ≥0}
    (hc : c ≠ 0) :
    haveI : IsHaarMeasure (c • μ) := IsHaarMeasure.nnreal_smul _ hc
    c * haarScalarFactor μ' (c • μ) = haarScalarFactor μ' μ := by
  have : IsHaarMeasure (c • μ) := IsHaarMeasure.nnreal_smul _ hc
  obtain ⟨g, hg⟩ := exists_continuous_nonneg_pos (1 : G)
  apply NNReal.coe_injective
  calc
    c * haarScalarFactor μ' (c • μ) = c * ((∫ x, g x ∂μ') / ∫ x, g x ∂(c • μ)) := by
      rw [haarScalarFactor_eq_integral_div_of_continuous_nonneg_pos _ _ hg]
    _ = c * ((∫ x, g x ∂μ') / (c • ∫ x, g x ∂μ)) := by simp
    _ = (∫ x, g x ∂μ') / (∫ x, g x ∂μ) := by
      rw [NNReal.smul_def, smul_eq_mul, ← mul_div_assoc]
      exact mul_div_mul_left (∫ (x : G), g x ∂μ') (∫ (x : G), g x ∂μ) (by simp [hc])
    _ = μ'.haarScalarFactor μ :=
      (haarScalarFactor_eq_integral_div_of_continuous_nonneg_pos _ _ hg).symm

@[to_additive addHaarScalarFactor_smul_smul]
/-
**MeasureTheory.Measure.haarScalarFactor_smul_smul** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：haarScalarFactor_smul_smul [LocallyCompactSpace G] (μ' μ : Measure G) [IsH
aarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] {c : Real>=
0} (hc : c != 0) : haveI : IsHaarMeasure (c • μ)
参数：μ' μ : Measure G；hc : c != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.nnreal_smul`：∀ {G : Type u_1} [inst 
: MeasurableSpace G] [inst_1 : Group G] [inst_2 : TopologicalSpace G]   (μ : Mea
sureTheory.Measure G) [μ.IsHaarMeasur…
· 使用定理 `MeasureTheory.IsFiniteMeasureOnCompacts.smul_nnreal`：∀ {α : Type u_1} {m
0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure α)
   [MeasureTheory.IsFiniteMeasureOnCompac…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.haarScalarFactor_smul`：haarScalarFactor_smul [Loca
llyCompactSpace G] (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompac
ts μ'] [IsMulLeftInvariant μ'] {c…
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用引理 `MeasureTheory.Measure.mul_haarScalarFactor_smul`：mul_haarScalarFactor_sm
ul [LocallyCompactSpace G] (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasure
OnCompacts μ'] [IsMulLeftInvariant μ'…
-/
lemma haarScalarFactor_smul_smul [LocallyCompactSpace G] (μ' μ : Measure G)
    [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] {c : ℝ≥0}
    (hc : c ≠ 0) :
    haveI : IsHaarMeasure (c • μ) := IsHaarMeasure.nnreal_smul _ hc
    haarScalarFactor (c • μ') (c • μ) = haarScalarFactor μ' μ := by
  rw [haarScalarFactor_smul, smul_eq_mul, mul_haarScalarFactor_smul _ _ hc]

@[to_additive (attr := simp)]
/-
**MeasureTheory.Measure.haarScalarFactor_self** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：haarScalarFactor_self (μ : Measure G) [IsHaarMeasure μ] : haarScalarFactor
 μ μ = 1
参数：μ : Measure G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsMulLeftInvariant`：∀ {G : Type u_
3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}  
 {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `exists_continuous_nonneg_pos`：exists_continuous_nonneg_pos [RegularSpace
 X] [LocallyCompactSpace X] (x : X) : exists f : C(X, Real), HasCompactSupport f
 ∧ 0 <= (f : X -> …
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero`：Continuous.
integral_pos_of_hasCompactSupport_nonneg_nonzero [IsFiniteMeasureOnCompacts μ] {
f : X -> Real} {x : X} (f_cont : Continuous f) (f…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u_3}
 {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}   {
μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `NNReal.coe_injective`：Function.Injective NNReal.toReal
· 使用引理 `MeasureTheory.Measure.haarScalarFactor_eq_integral_div_of_continuous_non
neg_pos`：haarScalarFactor_eq_integral_div_of_continuous_nonneg_pos (μ' μ : Measu
re G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInva…
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用引理 `MeasureTheory.Measure.exists_integral_isMulLeftInvariant_eq_smul_of_hasC
ompactSupport`：exists_integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport (
μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLe…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma haarScalarFactor_self (μ : Measure G) [IsHaarMeasure μ] :
    haarScalarFactor μ μ = 1 := by
  by_cases hG : LocallyCompactSpace G; swap
  · simp [haarScalarFactor, hG]
  obtain ⟨g, hg⟩ := exists_continuous_nonneg_pos (1 : G)
  have int_g_ne_zero : ∫ x, g x ∂μ ≠ 0 :=
    ne_of_gt (g.2.integral_pos_of_hasCompactSupport_nonneg_nonzero hg.1 hg.2.1 hg.2.2)
  apply NNReal.coe_injective
  calc
    haarScalarFactor μ μ = (∫ x, g x ∂μ) / ∫ x, g x ∂μ :=
      haarScalarFactor_eq_integral_div_of_continuous_nonneg_pos _ _ hg
    _ = 1 := div_self int_g_ne_zero

@[to_additive addHaarScalarFactor_eq_mul]
/-
**MeasureTheory.Measure.haarScalarFactor_eq_mul** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：haarScalarFactor_eq_mul (μ' μ ν : Measure G) [IsHaarMeasure μ] [IsHaarMeas
ure ν] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] : haarScalarFactor
 μ' ν = haarScalarFactor μ' μ * haarScalarFactor μ ν
参数：μ' μ ν : Measure G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsMulLeftInvariant`：∀ {G : Type u_
3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}  
 {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `exists_continuous_nonneg_pos`：exists_continuous_nonneg_pos [RegularSpace
 X] [LocallyCompactSpace X] (x : X) : exists f : C(X, Real), HasCompactSupport f
 ∧ 0 <= (f : X -> …
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.integral_isMulLeftInvariant_eq_smul_of_hasCompactS
upport`：integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport (μ' μ : Measure
 G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvar…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integral_pos_iff_support_of_nonneg`：integral_pos_iff_suppo
rt_of_nonneg {f : α -> Real} (hf : 0 <= f) (hfi : Integrable f μ) : (0 < ∫ x, f 
x ∂μ) ↔ 0 < μ (Function.support f)
· 使用定理 `Continuous.integrable_of_hasCompactSupport`：Continuous.integrable_of_has
CompactSupport (hf : Continuous f) (hcf : HasCompactSupport f) : Integrable f μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `IsOpen.measure_pos`：∀ {X : Type u_1} [inst : TopologicalSpace X] {m : Me
asurableSpace X} (μ : MeasureTheory.Measure X) [μ.IsOpenPosMeasure]   {U : Set X
}, IsOpe…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u_3}
 {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}   {
μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `Continuous.isOpen_support`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topol
ogicalSpace X] [T1Space X] [inst_2 : Zero X] [inst_3 : TopologicalSpace Y]   {f 
: Y → X}, Conti…
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_eq_mul_right_iff`：∀ {M₀ : Type u_1} [inst : MulZeroClass M₀] [IsRigh
tCancelMulZero M₀] {a b c : M₀}, a * c = b * c ↔ a = b ∨ c = 0
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `MeasureTheory.integral_smul_nnreal_measure`：integral_smul_nnreal_measure
 (f : α -> G) (c : Real>=0) : ∫ x, f x ∂(c • μ) = c • ∫ x, f x ∂μ
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 35 条，此处仅展示前 30 条）
-/
lemma haarScalarFactor_eq_mul (μ' μ ν : Measure G)
    [IsHaarMeasure μ] [IsHaarMeasure ν] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] :
    haarScalarFactor μ' ν = haarScalarFactor μ' μ * haarScalarFactor μ ν := by
  -- The group has to be locally compact, otherwise the scalar factor is 1 by definition.
  by_cases hG : LocallyCompactSpace G; swap
  · simp [haarScalarFactor, hG]
  -- Fix some nonzero continuous function with compact support `g`.
  obtain ⟨⟨g, g_cont⟩, g_comp, g_nonneg, g_one⟩ :
    ∃ (g : C(G, ℝ)), HasCompactSupport g ∧ 0 ≤ g ∧ g 1 ≠ 0 := exists_continuous_nonneg_pos 1
  have Z := integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport μ' μ g_cont g_comp
  simp only [integral_smul_nnreal_measure, smul_smul,
    integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport μ' ν g_cont g_comp,
    integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport μ ν g_cont g_comp] at Z
  have int_g_pos : 0 < ∫ x, g x ∂ν := by
    apply (integral_pos_iff_support_of_nonneg g_nonneg _).2
    · exact IsOpen.measure_pos ν g_cont.isOpen_support ⟨1, g_one⟩
    · exact g_cont.integrable_of_hasCompactSupport g_comp
  change (haarScalarFactor μ' ν : ℝ) * ∫ (x : G), g x ∂ν =
    (haarScalarFactor μ' μ * haarScalarFactor μ ν : ℝ≥0) * ∫ (x : G), g x ∂ν at Z
  simpa only [mul_eq_mul_right_iff (M₀ := ℝ), int_g_pos.ne', or_false, ← NNReal.eq_iff] using Z

@[to_additive]
/-
**MeasureTheory.Measure.haarScalarFactor_map** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：haarScalarFactor_map (μ' μ : Measure G) [IsHaarMeasure μ] [IsHaarMeasure μ
'] (φ : G ≃ₜ* G) : (map φ μ').haarScalarFactor (map φ μ) = μ'.haarScalarFactor μ
参数：μ' μ : Measure G；φ : G ≃ₜ* G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMulEquiv.isHaarMeasure_map`：∀ {G : Type u_1} [inst : Measurabl
eSpace G] [inst_1 : Group G] [inst_2 : TopologicalSpace G]   (μ : MeasureTheory.
Measure G) [μ.IsHaarMeasur…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsMulLeftInvariant`：∀ {G : Type u_
3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}  
 {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `exists_continuous_nonneg_pos`：exists_continuous_nonneg_pos [RegularSpace
 X] [LocallyCompactSpace X] (x : X) : exists f : C(X, Real), HasCompactSupport f
 ∧ 0 <= (f : X -> …
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero`：Continuous.
integral_pos_of_hasCompactSupport_nonneg_nonzero [IsFiniteMeasureOnCompacts μ] {
f : X -> Real} {x : X} (f_cont : Continuous f) (f…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u_3}
 {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}   {
μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_inj`：∀ {r₁ r₂ : NNReal}, ↑r₁ = ↑r₂ ↔ r₁ = r₂
· 使用引理 `MeasureTheory.Measure.haarScalarFactor_eq_integral_div_of_continuous_non
neg_pos`：haarScalarFactor_eq_integral_div_of_continuous_nonneg_pos (μ' μ : Measu
re G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInva…
· 使用引理 `MeasureTheory.Measure.haarScalarFactor_eq_integral_div`：haarScalarFactor
_eq_integral_div (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts
 μ'] [IsMulLeftInvariant μ'] {f : G -> Real}…
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
· 使用定理 `HasCompactSupport.comp_homeomorph`：∀ {X : Type u_9} {Y : Type u_10} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {M : Type u_11}   [inst_2 
: Zero M] {f : Y → M}, …
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `Continuous.aemeasurable`：Continuous.aemeasurable {f : α -> γ} (h : Conti
nuous f) {μ : Measure α} : AEMeasurable f μ
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `HomeomorphClass.instContinuousMapClass`：∀ {F : Type u_5} {α : Type u_6} 
{β : Type u_7} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst
_2 : EquivLike F α β] [Homeo…
· 使用定理 `ContinuousMulEquiv.instHomeomorphClass`：∀ {M : Type u_1} {N : Type u_2} 
[inst : TopologicalSpace M] [inst_1 : TopologicalSpace N] [inst_2 : Mul M]   [in
st_3 : Mul N], HomeomorphCla…
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 36 条，此处仅展示前 30 条）
-/
lemma haarScalarFactor_map (μ' μ : Measure G) [IsHaarMeasure μ] [IsHaarMeasure μ'] (φ : G ≃ₜ* G) :
    (map φ μ').haarScalarFactor (map φ μ) = μ'.haarScalarFactor μ := by
  -- The group has to be locally compact, otherwise the scalar factor is 1 by definition.
  by_cases hG : LocallyCompactSpace G; swap
  · simp [haarScalarFactor, hG]
  obtain ⟨⟨f, f_cont⟩, hf⟩ := exists_continuous_nonneg_pos (1 : G)
  have int_f_ne_zero : ∫ (x : G), f x ∂(map φ μ) ≠ 0 :=
    ne_of_gt (f_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero hf.1 hf.2.1 hf.2.2)
  rw [← NNReal.coe_inj, haarScalarFactor_eq_integral_div_of_continuous_nonneg_pos _ _ hf,
    haarScalarFactor_eq_integral_div μ' μ (f_cont.comp φ.continuous),
    integral_map (by fun_prop) (by fun_prop),
    integral_map (by fun_prop) (by fun_prop)]
  · rfl
  · exact hf.1.comp_homeomorph φ.toHomeomorph
  · change ∫ x, f (φ x) ∂μ ≠ 0
    rwa [← integral_map (by fun_prop) f_cont.aestronglyMeasurable]

/-- The scalar factor between two left-invariant measures is non-zero when both measures are
positive on open sets. -/
@[to_additive /-- The scalar factor between two left-invariant measures is non-zero when both
measures are positive on open sets. -/]
/-
**MeasureTheory.Measure.haarScalarFactor_pos_of_isHaarMeasure** 是 Mathlib 中的一个引理
，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：haarScalarFactor_pos_of_isHaarMeasure (μ' μ : Measure G) [IsHaarMeasure μ]
 [IsHaarMeasure μ'] : 0 < haarScalarFactor μ' μ
参数：μ' μ : Measure G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsMulLeftInvariant`：∀ {G : Type u_
3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}  
 {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.haarScalarFactor_self`：haarScalarFactor_self (μ : 
Measure G) [IsHaarMeasure μ] : haarScalarFactor μ μ = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `MeasureTheory.Measure.haarScalarFactor_eq_mul`：haarScalarFactor_eq_mul (
μ' μ ν : Measure G) [IsHaarMeasure μ] [IsHaarMeasure ν] [IsFiniteMeasureOnCompac
ts μ'] [IsMulLeftInvariant μ'] : ha…
-/
lemma haarScalarFactor_pos_of_isHaarMeasure (μ' μ : Measure G) [IsHaarMeasure μ]
    [IsHaarMeasure μ'] : 0 < haarScalarFactor μ' μ :=
  pos_iff_ne_zero.2 (fun H ↦ by simpa [H] using haarScalarFactor_eq_mul μ' μ μ')

/-!
### Uniqueness of measure of sets with compact closure

Two left invariant measures give the same measure to sets with compact closure, up to the
scalar `haarScalarFactor μ' μ`.

This is a tricky argument, typically not done in textbooks (the textbooks version all require one
version of regularity or another). Here is a sketch, based on
McQuillan's answer at https://mathoverflow.net/questions/456670/.

Assume for simplicity that all measures are normalized, so that the scalar factors are all `1`.
First, from the fact that `μ` and `μ'` integrate in the same way compactly supported functions,
they give the same measure to compact "zero sets", i.e., sets of the form `f⁻¹ {1}`
for `f` continuous and compactly supported.
See `measure_preimage_isMulLeftInvariant_eq_smul_of_hasCompactSupport`.

If `μ` is inner regular, a theorem of Halmos shows that any measurable set `s` of finite measure can
be approximated from inside by a compact zero set `k`. Then `μ s ≤ μ k + ε = μ' k + ε ≤ μ' s + ε`.
Letting `ε` tend to zero, one gets `μ s ≤ μ' s`.
See `smul_measure_isMulInvariant_le_of_isCompact_closure`.

Assume now that `s` is a measurable set of compact closure. It is contained in a compact
zero set `t`. The same argument applied to `t - s` gives `μ (t \ s) ≤ μ' (t \ s)`, i.e.,
`μ t - μ s ≤ μ' t - μ' s`. As `μ t = μ' t` (since these are zero sets), we get the inequality
`μ' s ≤ μ s`. Together with the previous one, this gives `μ' s = μ s`.
See `measure_isMulInvariant_eq_smul_of_isCompact_closure_of_innerRegularCompactLTTop`.

If neither `μ` nor `μ'` is inner regular, we can use the existence of another inner regular
left-invariant measure `ν`, so get `μ s = ν s = μ' s`, by applying twice the previous argument.
Here, the uniqueness argument uses the existence of a Haar measure with a nice behavior!
See `measure_isMulInvariant_eq_smul_of_isCompact_closure_of_measurableSet`.

Finally, if `s` has compact closure but is not measurable, its measure is the infimum of the
measures of its measurable supersets, and even of those contained in `closure s`. As `μ`
and `μ'` coincide on these supersets, this yields `μ s = μ' s`.
See `measure_isMulInvariant_eq_smul_of_isCompact_closure`.
-/

/-- Two left invariant measures give the same mass to level sets of continuous compactly supported
functions, up to the scalar `haarScalarFactor μ' μ`.

Auxiliary lemma in the proof of the more general
`measure_isMulInvariant_eq_smul_of_isCompact_closure`, which works for any set with
compact closure. -/
@[to_additive measure_preimage_isAddLeftInvariant_eq_smul_of_hasCompactSupport
/-- Two left invariant measures give the same mass to level sets of continuous compactly supported
functions, up to the scalar `addHaarScalarFactor μ' μ`.

Auxiliary lemma in the proof of the more general
`measure_isAddInvariant_eq_smul_of_isCompact_closure`, which works for any set with
compact closure. -/]
/-
**MeasureTheory.Measure.measure_preimage_isMulLeftInvariant_eq_smul_of_hasCompac
tSupport** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：measure_preimage_isMulLeftInvariant_eq_smul_of_hasCompactSupport (μ' μ : M
easure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ
'] {f : G -> Real} (hf : Continuous f) (h'f : HasCompactSupport f) : μ' (f ⁻¹' {
1}) = haarScalarFactor μ' μ • μ (f ⁻¹' {1})
参数：μ' μ : Measure G；hf : Continuous f；h'f : HasCompactSupport f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_seq_strictAnti_tendsto'`：exists_seq_strictAnti_tendsto' [DenselyO
rdered α] [FirstCountableTopology α] {x y : α} (hy : x < y) : exists u : Nat -> 
α, StrictAnti u ∧ (f…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
· 使用定理 `BoundedContinuousFunction.continuous`：∀ {α : Type u} {β : Type v} [inst 
: TopologicalSpace α] [inst_1 : PseudoMetricSpace β]   (f : BoundedContinuousFun
ction α β), Continuous ⇑f
· 使用定理 `MeasureTheory.tendsto_integral_of_dominated_convergence`：tendsto_integra
l_of_dominated_convergence {F : Nat -> α -> G} {f : α -> G} (bound : α -> Real) 
(F_measurable : forall n, AEStronglyMeasurabl…
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.IntegrableOn.integrable_indicator`：∀ {α : Type u_1} {ε' : 
Type u_4} {mα : MeasurableSpace α} {s : Set α} {μ : MeasureTheory.Measure α}   [
inst : TopologicalSpace ε'] [inst_1 :…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `enorm_one`：∀ {G : Type u_1} [inst : SeminormedAddCommGroup G] [inst_1 : 
One G] [NormOneClass G], ‖1‖ₑ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `IsCompact.measure_lt_top`：∀ {α : Type u_1} {m0 : MeasurableSpace α} [ins
t : TopologicalSpace α] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsFiniteM
easureOnCompac…
（共 88 条，此处仅展示前 30 条）
-/
lemma measure_preimage_isMulLeftInvariant_eq_smul_of_hasCompactSupport
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ']
    {f : G → ℝ} (hf : Continuous f) (h'f : HasCompactSupport f) :
    μ' (f ⁻¹' {1}) = haarScalarFactor μ' μ • μ (f ⁻¹' {1}) := by
  /- This follows from the fact that the two measures integrate in the same way continuous
  functions, by approximating the indicator function of `f ⁻¹' {1}` by continuous functions
  (namely `vₙ ∘ f` where `vₙ` is equal to `1` at `1`, and `0` outside of a small neighborhood
  `(1 - uₙ, 1 + uₙ)` where `uₙ` is a sequence tending to `0`).
  We use `vₙ = thickenedIndicator uₙ {1}` to take advantage of existing lemmas. -/
  obtain ⟨u, -, u_mem, u_lim⟩ : ∃ u, StrictAnti u ∧ (∀ (n : ℕ), u n ∈ Ioo 0 1)
    ∧ Tendsto u atTop (𝓝 0) := exists_seq_strictAnti_tendsto' (zero_lt_one : (0 : ℝ) < 1)
  let v : ℕ → ℝ → ℝ := fun n x ↦ thickenedIndicator (u_mem n).1 ({1} : Set ℝ) x
  have vf_cont n : Continuous ((v n) ∘ f) := by
    apply Continuous.comp (continuous_induced_dom.comp ?_) hf
    exact BoundedContinuousFunction.continuous (thickenedIndicator (u_mem n).left {1})
  have I : ∀ (ν : Measure G), IsFiniteMeasureOnCompacts ν →
      Tendsto (fun n ↦ ∫ x, v n (f x) ∂ν) atTop
      (𝓝 (∫ x, Set.indicator ({1} : Set ℝ) (fun _ ↦ 1) (f x) ∂ν)) := by
    intro ν hν
    apply tendsto_integral_of_dominated_convergence
        (bound := (tsupport f).indicator (fun (_ : G) ↦ (1 : ℝ)))
    · exact fun n ↦ (vf_cont n).aestronglyMeasurable
    · apply IntegrableOn.integrable_indicator _ (isClosed_tsupport f).measurableSet
      simpa using IsCompact.measure_lt_top h'f
    · refine fun n ↦ Eventually.of_forall (fun x ↦ ?_)
      by_cases hx : x ∈ tsupport f
      · simp only [v, Real.norm_eq_abs, NNReal.abs_eq, hx, indicator_of_mem]
        norm_cast
        exact thickenedIndicator_le_one _ _ _
      · simp only [v, Real.norm_eq_abs, NNReal.abs_eq, hx, not_false_eq_true, indicator_of_notMem]
        rw [thickenedIndicator_zero]
        · simp
        · simpa [image_eq_zero_of_notMem_tsupport hx] using (u_mem n).2.le
    · filter_upwards with x
      have T := tendsto_pi_nhds.1 (thickenedIndicator_tendsto_indicator_closure
        (fun n ↦ (u_mem n).1) u_lim ({1} : Set ℝ)) (f x)
      simp only [thickenedIndicator_apply, closure_singleton] at T
      convert! NNReal.tendsto_coe.2 T
      simp
  have M n : ∫ (x : G), v n (f x) ∂μ' = ∫ (x : G), v n (f x) ∂(haarScalarFactor μ' μ • μ) := by
    apply integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport μ' μ (vf_cont n)
    apply h'f.comp_left
    simp only [v, thickenedIndicator_apply, NNReal.coe_eq_zero]
    rw [thickenedIndicatorAux_zero (u_mem n).1]
    · simp only [ENNReal.toNNReal_zero]
    · simpa using (u_mem n).2.le
  have I1 := I μ' (by infer_instance)
  simp_rw [M] at I1
  have J1 : ∫ (x : G), indicator {1} (fun _ ↦ (1 : ℝ)) (f x) ∂μ'
      = ∫ (x : G), indicator {1} (fun _ ↦ 1) (f x) ∂(haarScalarFactor μ' μ • μ) :=
    tendsto_nhds_unique I1 (I (haarScalarFactor μ' μ • μ) (by infer_instance))
  have J2 : μ'.real (f ⁻¹' {1})
      = (haarScalarFactor μ' μ • μ).real (f ⁻¹' {1}) := by
    have : (fun x ↦ indicator {1} (fun _ ↦ (1 : ℝ)) (f x)) =
        (fun x ↦ indicator (f ⁻¹' {1}) (fun _ ↦ (1 : ℝ)) x) := by
      ext x
      exact (indicator_comp_right f (s := ({1} : Set ℝ)) (g := (fun _ ↦ (1 : ℝ))) (x := x)).symm
    have mf : MeasurableSet (f ⁻¹' {1}) := (isClosed_singleton.preimage hf).measurableSet
    simpa only [this, mf, integral_indicator_const, smul_eq_mul, mul_one, Pi.smul_apply,
      nnreal_smul_coe_apply, ENNReal.toReal_mul, ENNReal.coe_toReal] using J1
  have C : IsCompact (f ⁻¹' {1}) := h'f.isCompact_preimage hf isClosed_singleton (by simp)
  rw [measureReal_eq_measureReal_iff C.measure_lt_top.ne C.measure_lt_top.ne] at J2
  simpa using J2

/-- If an invariant measure is inner regular, then it gives less mass to sets with compact closure
than any other invariant measure, up to the scalar `haarScalarFactor μ' μ`.

Auxiliary lemma in the proof of the more general
`measure_isMulInvariant_eq_smul_of_isCompact_closure`, which gives equality for any
set with compact closure. -/
@[to_additive smul_measure_isAddInvariant_le_of_isCompact_closure
/-- If an invariant measure is inner regular, then it gives less mass to sets with compact closure
than any other invariant measure, up to the scalar `addHaarScalarFactor μ' μ`.

Auxiliary lemma in the proof of the more general
`measure_isAddInvariant_eq_smul_of_isCompact_closure`, which gives equality for any
set with compact closure. -/]
/-
**MeasureTheory.Measure.smul_measure_isMulInvariant_le_of_isCompact_closure** 是 
Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：smul_measure_isMulInvariant_le_of_isCompact_closure [LocallyCompactSpace G
] (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeft
Invariant μ'] [InnerRegularCompactLTTop μ] {s : Set G} (hs : MeasurableSet s) (h
's : IsCompact (closure s)) : haarScalarFactor μ' μ • μ s <= μ' s
参数：μ' μ : Measure G；hs : MeasurableSet s；h's : IsCompact (closure s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_forall_lt`：le_of_forall_lt (H : forall c, c < a -> c < b) : a <= b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `IsCompact.measure_lt_top`：∀ {α : Type u_1} {m0 : MeasurableSpace α} [ins
t : TopologicalSpace α] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsFiniteM
easureOnCompac…
· 使用定理 `MeasureTheory.IsFiniteMeasureOnCompacts.smul_nnreal`：∀ {α : Type u_1} {m
0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure α)
   [MeasureTheory.IsFiniteMeasureOnCompac…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `MeasureTheory.Measure.innerRegularWRT_preimage_one_hasCompactSupport_mea
sure_ne_top_of_group`：innerRegularWRT_preimage_one_hasCompactSupport_measure_ne_
top_of_group : InnerRegularWRT μ (fun s => exists (f : G -> Real), Continuous f 
∧ …
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsMulLeftInvariant`：∀ {G : Type u_
3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}  
 {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.measure_preimage_isMulLeftInvariant_eq_smul_of_has
CompactSupport`：measure_preimage_isMulLeftInvariant_eq_smul_of_hasCompactSupport
 (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulL…
-/
lemma smul_measure_isMulInvariant_le_of_isCompact_closure [LocallyCompactSpace G]
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ']
    [InnerRegularCompactLTTop μ]
    {s : Set G} (hs : MeasurableSet s) (h's : IsCompact (closure s)) :
    haarScalarFactor μ' μ • μ s ≤ μ' s := by
  apply le_of_forall_lt (fun r hr ↦ ?_)
  let ν := haarScalarFactor μ' μ • μ
  have : ν s ≠ ∞ := ((measure_mono subset_closure).trans_lt h's.measure_lt_top).ne
  obtain ⟨-, hf, ⟨f, f_cont, f_comp, rfl⟩, νf⟩ :
      ∃ K ⊆ s, (∃ f, Continuous f ∧ HasCompactSupport f ∧ K = f ⁻¹' {1}) ∧ r < ν K :=
    innerRegularWRT_preimage_one_hasCompactSupport_measure_ne_top_of_group ⟨hs, this⟩ r
      (by convert! hr)
  calc
  r < ν (f ⁻¹' {1}) := νf
  _ = μ' (f ⁻¹' {1}) :=
    (measure_preimage_isMulLeftInvariant_eq_smul_of_hasCompactSupport _ _ f_cont f_comp).symm
  _ ≤ μ' s := measure_mono hf

/-- If an invariant measure is inner regular, then it gives the same mass to measurable sets with
compact closure as any other invariant measure, up to the scalar `haarScalarFactor μ' μ`.

Auxiliary lemma in the proof of the more general
`measure_isMulInvariant_eq_smul_of_isCompact_closure`, which works for any set with
compact closure, and removes the inner regularity assumption. -/
@[to_additive measure_isAddInvariant_eq_smul_of_isCompact_closure_of_innerRegularCompactLTTop
/-- If an invariant measure is inner regular, then it gives the same mass to measurable sets with
compact closure as any other invariant measure, up to the scalar `addHaarScalarFactor μ' μ`.

Auxiliary lemma in the proof of the more general
`measure_isAddInvariant_eq_smul_of_isCompact_closure`, which works for any set with
compact closure, and removes the inner regularity assumption. -/]
/-
**MeasureTheory.Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure_of_i
nnerRegularCompactLTTop** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：measure_isMulInvariant_eq_smul_of_isCompact_closure_of_innerRegularCompact
LTTop [LocallyCompactSpace G] (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeas
ureOnCompacts μ'] [IsMulLeftInvariant μ'] [InnerRegularCompactLTTop μ] {s : Set 
G} (hs : MeasurableSet s) (h's : IsCompact (closure s)) : μ' s = haarScalarFacto
r μ' μ • μ s
参数：μ' μ : Measure G；hs : MeasurableSet s；h's : IsCompact (closure s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `exists_continuous_one_zero_of_isCompact`：exists_continuous_one_zero_of_i
sCompact [RegularSpace X] [LocallyCompactSpace X] {s t : Set X} (hs : IsCompact 
s) (ht : IsClosed t) (hd : Di…
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `isClosed_empty`：isClosed_empty : IsClosed (∅ : Set X)
· 使用定理 `Set.disjoint_empty`：∀ {α : Type u} (s : Set α), Disjoint s ∅
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasCompactSupport.isCompact_preimage`：∀ {α : Type u_2} {β : Type u_4} [i
nst : TopologicalSpace α] [inst_1 : Zero β] {f : α → β} [inst_2 : TopologicalSpa
ce β]   {K : Set β}, HasCo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用引理 `MeasureTheory.Measure.smul_measure_isMulInvariant_le_of_isCompact_closur
e`：smul_measure_isMulInvariant_le_of_isCompact_closure [LocallyCompactSpace G] (
μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts …
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `IsCompact.closure_of_subset`：IsCompact.closure_of_subset {s K : Set X} (
hK : IsCompact K) (h : s subseteq K) : IsCompact (closure s)
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用引理 `MeasureTheory.Measure.measure_preimage_isMulLeftInvariant_eq_smul_of_has
CompactSupport`：measure_preimage_isMulLeftInvariant_eq_smul_of_hasCompactSupport
 (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulL…
· 使用定理 `ENNReal.sub_le_sub_iff_left`：sub_le_sub_iff_left (h : c <= a) (h' : a !=
 ∞) : (a - b <= a - c) ↔ c <= b
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
（共 39 条，此处仅展示前 30 条）
-/
lemma measure_isMulInvariant_eq_smul_of_isCompact_closure_of_innerRegularCompactLTTop
    [LocallyCompactSpace G]
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ']
    [InnerRegularCompactLTTop μ]
    {s : Set G} (hs : MeasurableSet s) (h's : IsCompact (closure s)) :
    μ' s = haarScalarFactor μ' μ • μ s := by
  apply le_antisymm ?_ (smul_measure_isMulInvariant_le_of_isCompact_closure μ' μ hs h's)
  let ν := haarScalarFactor μ' μ • μ
  change μ' s ≤ ν s
  obtain ⟨⟨f, f_cont⟩, hf, -, f_comp, -⟩ : ∃ f : C(G, ℝ), EqOn f 1 (closure s) ∧ EqOn f 0 ∅
      ∧ HasCompactSupport f ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 :=
    exists_continuous_one_zero_of_isCompact h's isClosed_empty (disjoint_empty _)
  let t := f ⁻¹' {1}
  have t_closed : IsClosed t := isClosed_singleton.preimage f_cont
  have t_comp : IsCompact t := f_comp.isCompact_preimage f_cont isClosed_singleton (by simp)
  have st : s ⊆ t := (IsClosed.closure_subset_iff t_closed).mp hf
  have A : ν (t \ s) ≤ μ' (t \ s) := by
    apply smul_measure_isMulInvariant_le_of_isCompact_closure _ _ (t_closed.measurableSet.diff hs)
    exact t_comp.closure_of_subset sdiff_subset
  have B : μ' t = ν t :=
    measure_preimage_isMulLeftInvariant_eq_smul_of_hasCompactSupport _ _ f_cont f_comp
  rwa [measure_sdiff st hs.nullMeasurableSet, measure_sdiff st hs.nullMeasurableSet, ← B,
    ENNReal.sub_le_sub_iff_left] at A
  · exact measure_mono st
  · exact t_comp.measure_lt_top.ne
  · exact ((measure_mono st).trans_lt t_comp.measure_lt_top).ne
  · exact ((measure_mono st).trans_lt t_comp.measure_lt_top).ne

/-- Given an invariant measure then it gives the same mass to measurable sets with
compact closure as any other invariant measure, up to the scalar `haarScalarFactor μ' μ`.

Auxiliary lemma in the proof of the more general
`measure_isMulInvariant_eq_smul_of_isCompact_closure`, which removes the
measurability assumption. -/
@[to_additive measure_isAddInvariant_eq_smul_of_isCompact_closure_of_measurableSet
/-- Given an invariant measure then it gives the same mass to measurable sets with
compact closure as any other invariant measure, up to the scalar `addHaarScalarFactor μ' μ`.

Auxiliary lemma in the proof of the more general
`measure_isAddInvariant_eq_smul_of_isCompact_closure`, which removes the
measurability assumption. -/]
/-
**MeasureTheory.Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure_of_m
easurableSet** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：measure_isMulInvariant_eq_smul_of_isCompact_closure_of_measurableSet [Loca
llyCompactSpace G] (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompac
ts μ'] [IsMulLeftInvariant μ'] {s : Set G} (hs : MeasurableSet s) (h's : IsCompa
ct (closure s)) : μ' s = haarScalarFactor μ' μ • μ s
参数：μ' μ : Measure G；hs : MeasurableSet s；h's : IsCompact (closure s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.measure_isMulInvariant_eq_smul_of_isCompact_closur
e_of_innerRegularCompactLTTop`：measure_isMulInvariant_eq_smul_of_isCompact_closu
re_of_innerRegularCompactLTTop [LocallyCompactSpace G] (μ' μ : Measure G) [IsHaa
rMeasure μ]…
· 使用定理 `MeasureTheory.Measure.Regular.instInnerRegularCompactLTTop`：∀ {α : Type 
u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topologi
calSpace α] [μ.Regular],   μ.InnerRegularCompact…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsMulLeftInvariant`：∀ {G : Type u_
3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}  
 {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用引理 `MeasureTheory.Measure.haarScalarFactor_eq_mul`：haarScalarFactor_eq_mul (
μ' μ ν : Measure G) [IsHaarMeasure μ] [IsHaarMeasure ν] [IsFiniteMeasureOnCompac
ts μ'] [IsMulLeftInvariant μ'] : ha…
-/
lemma measure_isMulInvariant_eq_smul_of_isCompact_closure_of_measurableSet [LocallyCompactSpace G]
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ']
    {s : Set G} (hs : MeasurableSet s) (h's : IsCompact (closure s)) :
    μ' s = haarScalarFactor μ' μ • μ s := by
  let ν : Measure G := haar
  have A : μ' s = haarScalarFactor μ' ν • ν s :=
    measure_isMulInvariant_eq_smul_of_isCompact_closure_of_innerRegularCompactLTTop μ' ν hs h's
  have B : μ s = haarScalarFactor μ ν • ν s :=
    measure_isMulInvariant_eq_smul_of_isCompact_closure_of_innerRegularCompactLTTop μ ν hs h's
  rw [A, B, smul_smul, haarScalarFactor_eq_mul μ' μ ν]

/-- **Uniqueness of left-invariant measures**:
Given two left-invariant measures which are finite on compacts, they coincide in the following
sense: they give the same value to sets with compact closure, up to the multiplicative
constant `haarScalarFactor μ' μ`. -/
@[to_additive measure_isAddInvariant_eq_smul_of_isCompact_closure
/-- **Uniqueness of left-invariant measures**:
Given two left-invariant measures which are finite on compacts, they coincide in the following
sense: they give the same value to sets with compact closure, up to the multiplicative
constant `addHaarScalarFactor μ' μ`. -/]
/-
**MeasureTheory.Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure** 是 
Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：measure_isMulInvariant_eq_smul_of_isCompact_closure [LocallyCompactSpace G
] (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeft
Invariant μ'] {s : Set G} (h's : IsCompact (closure s)) : μ' s = haarScalarFacto
r μ' μ • μ s
参数：μ' μ : Measure G；h's : IsCompact (closure s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用引理 `MeasureTheory.Measure.measure_isMulInvariant_eq_smul_of_isCompact_closur
e_of_measurableSet`：measure_isMulInvariant_eq_smul_of_isCompact_closure_of_measu
rableSet [LocallyCompactSpace G] (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteM
…
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `IsCompact.closure_of_subset`：IsCompact.closure_of_subset {s K : Set X} (
hK : IsCompact K) (h : s subseteq K) : IsCompact (closure s)
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem measure_isMulInvariant_eq_smul_of_isCompact_closure [LocallyCompactSpace G]
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ']
    {s : Set G} (h's : IsCompact (closure s)) :
    μ' s = haarScalarFactor μ' μ • μ s := by
  let ν := haarScalarFactor μ' μ • μ
  apply le_antisymm
  · calc
    μ' s ≤ μ' ((toMeasurable ν s) ∩ (closure s)) :=
      measure_mono <| subset_inter (subset_toMeasurable ν s) subset_closure
    _ = ν ((toMeasurable ν s) ∩ (closure s)) := by
      apply measure_isMulInvariant_eq_smul_of_isCompact_closure_of_measurableSet _ _ _ _
      · exact (measurableSet_toMeasurable ν s).inter isClosed_closure.measurableSet
      · exact h's.closure_of_subset inter_subset_right
    _ ≤ ν (toMeasurable ν s) := measure_mono inter_subset_left
    _ = ν s := measure_toMeasurable s
  · calc
    ν s ≤ ν ((toMeasurable μ' s) ∩ (closure s)) :=
      measure_mono <| subset_inter (subset_toMeasurable μ' s) subset_closure
    _ = μ' ((toMeasurable μ' s) ∩ (closure s)) := by
      apply (measure_isMulInvariant_eq_smul_of_isCompact_closure_of_measurableSet _ _ _ _).symm
      · exact (measurableSet_toMeasurable μ' s).inter isClosed_closure.measurableSet
      · exact h's.closure_of_subset inter_subset_right
    _ ≤ μ' (toMeasurable μ' s) := measure_mono inter_subset_left
    _ = μ' s := measure_toMeasurable s

/-- **Uniqueness of Haar measures**:
Two Haar measures on a compact group coincide up to a multiplicative factor. -/
@[to_additive isAddInvariant_eq_smul_of_compactSpace
/-- **Uniqueness of additive Haar measures**:
Two additive Haar measures on a compact additive group coincide up to a multiplicative factor. -/]
/-
**MeasureTheory.Measure.isMulInvariant_eq_smul_of_compactSpace** 是 Mathlib 中的一个引
理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：isMulInvariant_eq_smul_of_compactSpace [CompactSpace G] (μ' μ : Measure G)
 [IsHaarMeasure μ] [IsMulLeftInvariant μ'] [IsFiniteMeasureOnCompacts μ'] : μ' =
 haarScalarFactor μ' μ • μ
参数：μ' μ : Measure G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.measure_isMulInvariant_eq_smul_of_isCompact_closur
e`：measure_isMulInvariant_eq_smul_of_isCompact_closure [LocallyCompactSpace G] (
μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts …
· 使用定理 `WeaklyLocallyCompactSpace.locallyCompactSpace`：∀ {X : Type u_1} [inst : 
TopologicalSpace X] [R1Space X] [WeaklyLocallyCompactSpace X], LocallyCompactSpa
ce X
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `instWeaklyLocallyCompactSpaceOfCompactSpace`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [CompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `IsClosed.isCompact`：IsClosed.isCompact [CompactSpace X] (h : IsClosed s)
 : IsCompact s
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
-/
lemma isMulInvariant_eq_smul_of_compactSpace [CompactSpace G] (μ' μ : Measure G)
    [IsHaarMeasure μ] [IsMulLeftInvariant μ'] [IsFiniteMeasureOnCompacts μ'] :
    μ' = haarScalarFactor μ' μ • μ := by
  ext s _hs
  exact measure_isMulInvariant_eq_smul_of_isCompact_closure _ _ isClosed_closure.isCompact

@[to_additive]
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) instInnerRegularOfIsHaarMeasureOfCompactSpace
    [CompactSpace G] (μ : Measure G) [IsMulLeftInvariant μ] [IsFiniteMeasureOnCompacts μ] :
    InnerRegular μ := by
  rw [isMulInvariant_eq_smul_of_compactSpace μ haar]
  infer_instance

@[to_additive]
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) instRegularOfIsHaarMeasureOfCompactSpace
    [CompactSpace G] (μ : Measure G) [IsMulLeftInvariant μ] [IsFiniteMeasureOnCompacts μ] :
    Regular μ := by
  rw [isMulInvariant_eq_smul_of_compactSpace μ haar]
  infer_instance

/-- **Uniqueness of Haar measures**:
Two Haar measures which are probability measures coincide. -/
@[to_additive /-- **Uniqueness of additive Haar measures**:
Two additive Haar measures which are probability measures coincide. -/]
/-
**MeasureTheory.Measure.isHaarMeasure_eq_of_isProbabilityMeasure** 是 Mathlib 中的一
个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：isHaarMeasure_eq_of_isProbabilityMeasure [LocallyCompactSpace G] (μ' μ : M
easure G) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [IsHaarMeasure μ] [
IsHaarMeasure μ'] : μ' = μ
参数：μ' μ : Measure G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `MeasureTheory.measure_univ_of_isMulLeftInvariant`：measure_univ_of_isMulL
eftInvariant [WeaklyLocallyCompactSpace G] [NoncompactSpace G] (μ : Measure G) [
IsOpenPosMeasure μ] [μ.IsMulLeftInvari…
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `not_compactSpace_iff`：not_compactSpace_iff : ¬CompactSpace X ↔ Noncompac
tSpace X
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u_3}
 {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}   {
μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsMulLeftInvariant`：∀ {G : Type u_
3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}  
 {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `MeasureTheory.Measure.measure_isMulInvariant_eq_smul_of_isCompact_closur
e`：measure_isMulInvariant_eq_smul_of_isCompact_closure [LocallyCompactSpace G] (
μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts …
· 使用定理 `IsClosed.isCompact`：IsClosed.isCompact [CompactSpace X] (h : IsClosed s)
 : IsCompact s
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isHaarMeasure_eq_of_isProbabilityMeasure [LocallyCompactSpace G] (μ' μ : Measure G)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [IsHaarMeasure μ] [IsHaarMeasure μ'] :
    μ' = μ := by
  have : CompactSpace G := by
    by_contra H
    rw [not_compactSpace_iff] at H
    simpa using measure_univ_of_isMulLeftInvariant μ
  have A s : μ' s = haarScalarFactor μ' μ • μ s :=
    measure_isMulInvariant_eq_smul_of_isCompact_closure _ _ isClosed_closure.isCompact
  have Z := A univ
  simp only [measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one, ENNReal.one_eq_coe] at Z
  ext s _hs
  simp [A s, ← Z]

/-!
### Uniqueness of measure of open sets

Two Haar measures give the same measure to open sets (or more generally to sets which are everywhere
positive), up to the scalar `haarScalarFactor μ' μ `.
-/

@[to_additive measure_isAddHaarMeasure_eq_smul_of_isEverywherePos]
/-
**MeasureTheory.Measure.measure_isHaarMeasure_eq_smul_of_isEverywherePos** 是 Mat
hlib 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：measure_isHaarMeasure_eq_smul_of_isEverywherePos [LocallyCompactSpace G] (
μ' μ : Measure G) [IsHaarMeasure μ] [IsHaarMeasure μ'] {s : Set G} (hs : Measura
bleSet s) (h's : IsEverywherePos μ s) : μ' s = haarScalarFactor μ' μ • μ s
参数：μ' μ : Measure G；hs : MeasurableSet s；h's : IsEverywherePos μ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsMulLeftInvariant`：∀ {G : Type u_
3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}  
 {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `WeaklyLocallyCompactSpace.exists_compact_mem_nhds`：∀ {X : Type u_3} {ins
t : TopologicalSpace X} [self : WeaklyLocallyCompactSpace X] (x : X), ∃ s, IsCom
pact s ∧ s ∈ nhds x
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `IsCompact.closure`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R1Space
 X] {K : Set X}, IsCompact K → IsCompact (closure K)
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `zorn_subset`：zorn_subset (S : Set (Set α)) (h : forall c subseteq S, IsC
hain (· subseteq ·) c -> exists ub in S, forall s in c, s subseteq ub) : exists 
m…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsChain.directedOn`：IsChain.directedOn (H : IsChain r s) : DirectedOn r 
s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.subset_biUnion_of_mem`：subset_biUnion_of_mem {s : Set α} {u : α -> S
et β} {x : α} (xs : x in s) : u x subseteq ⋃ x in s, u x
· 使用定理 `Maximal.prop`：∀ {α : Type u_1} [inst : LE α] {P : α → Prop} {x : α}, Max
imal P x → P x
· 使用定理 `Maximal.mem_of_prop_insert`：Maximal.mem_of_prop_insert (h : Maximal P s)
 (hx : P (insert x s)) : x in s
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mem_leftCoset`：mem_leftCoset {s : Set α} {x : α} (a : α) (hxS : x in s) 
: a * x in a • s
· 使用定理 `Set.mul_mem_mul`：mul_mem_mul : a in s -> b in t -> a * b in s * t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inv_mem_inv`：inv_mem_inv : a⁻¹ in s⁻¹ ↔ a in s
（共 111 条，此处仅展示前 30 条）

--- 原说明 ---
### Uniqueness of measure of open sets

Two Haar measures give the same measure to open sets (or more generally to sets 
which are everywhere
positive), up to the scalar `haarScalarFactor μ' μ `.
-/
theorem measure_isHaarMeasure_eq_smul_of_isEverywherePos [LocallyCompactSpace G]
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsHaarMeasure μ']
    {s : Set G} (hs : MeasurableSet s) (h's : IsEverywherePos μ s) :
    μ' s = haarScalarFactor μ' μ • μ s := by
  let ν := haarScalarFactor μ' μ • μ
  change μ' s = ν s
  /- Fix a compact neighborhood `k` of the identity, and consider a maximal disjoint family `m` of
  sets `x • k` centered at points in `s`. Then `s` is covered by the sets `x • (k * k⁻¹)` by
  maximality. If the family is countable, then since `μ'` and `ν` coincide in compact sets, and
  the measure of a countable disjoint union is the sum of the measures, we get `μ' s = ν s`.
  Otherwise, the family is uncountable, and each intersection with `s` has positive measure by
  the everywhere positivity assumption, so `ν s = ∞`, and `μ' s = ∞` in the same way. -/
  obtain ⟨k, k_comp, k_closed, k_mem⟩ : ∃ k, IsCompact k ∧ IsClosed k ∧ k ∈ 𝓝 (1 : G) := by
    rcases exists_compact_mem_nhds (1 : G) with ⟨k, hk, hmem⟩
    exact ⟨closure k, hk.closure, isClosed_closure, mem_of_superset hmem subset_closure⟩
  have one_k : 1 ∈ k := mem_of_mem_nhds k_mem
  let A : Set (Set G) := {t | t ⊆ s ∧ PairwiseDisjoint t (fun x ↦ x • k)}
  obtain ⟨m, m_max⟩ : ∃ m, Maximal (· ∈ A) m := by
    apply zorn_subset
    intro c cA hc
    refine ⟨⋃ a ∈ c, a, ⟨?_, ?_⟩, ?_⟩
    · simp only [iUnion_subset_iff]
      intro a ac x hx
      simp only [A, subset_def, mem_ofPred_eq] at cA
      exact (cA _ ac).1 x hx
    · rintro x hx y hy hxy
      simp only [mem_iUnion, exists_prop] at hx hy
      rcases hx with ⟨a, ac, xa⟩
      rcases hy with ⟨b, bc, yb⟩
      obtain ⟨m, mc, am, bm⟩ : ∃ m ∈ c, a ⊆ m ∧ b ⊆ m := hc.directedOn _ ac _ bc
      exact (cA mc).2 (am xa) (bm yb) hxy
    · intro a ac
      exact subset_biUnion_of_mem (u := id) ac
  obtain ⟨hms : m ⊆ s, hdj : PairwiseDisjoint m (fun x ↦ x • k)⟩ := m_max.prop
  have sm : s ⊆ ⋃ x ∈ m, x • (k * k⁻¹) := by
    intro y hy
    by_cases h'y : m ∪ {y} ∈ A
    · have ym : y ∈ m := m_max.mem_of_prop_insert (by simpa using h'y)
      have : y ∈ y • (k * k⁻¹) := by
        simpa using mem_leftCoset y (Set.mul_mem_mul one_k (Set.inv_mem_inv.mpr one_k))
      exact mem_biUnion ym this
    · obtain ⟨x, xm, -, z, zy, zx⟩ : ∃ x ∈ m, y ≠ x ∧ ∃ z, z ∈ y • k ∧ z ∈ x • k := by
        simpa [A, hms, hy, insert_subset_iff, pairwiseDisjoint_insert, hdj, not_disjoint_iff]
          using h'y
      have : y ∈ x • (k * k⁻¹) := by
        rw [show y = x * ((x⁻¹ * z) * (y⁻¹ * z)⁻¹) by group]
        have : (x⁻¹ * z) * (y⁻¹ * z)⁻¹ ∈ k * k⁻¹ := Set.mul_mem_mul ((mem_leftCoset_iff x).mp zx)
          (Set.inv_mem_inv.mpr ((mem_leftCoset_iff y).mp zy))
        exact mem_leftCoset x this
      exact mem_biUnion xm this
  rcases eq_empty_or_nonempty m with rfl | hm
  · simp only [mem_empty_iff_false, iUnion_of_empty, iUnion_empty, subset_empty_iff] at sm
    simp [sm]
  by_cases h'm : Set.Countable m
  · rcases h'm.exists_eq_range hm with ⟨f, rfl⟩
    have M i : MeasurableSet (disjointed (fun n ↦ s ∩ f n • (k * k⁻¹)) i) := by
      apply MeasurableSet.disjointed (fun j ↦ hs.inter ?_)
      have : IsClosed (k • k⁻¹) := IsClosed.smul_left_of_isCompact k_closed.inv k_comp
      exact (IsClosed.smul this (f j)).measurableSet
    simp only [mem_range, iUnion_exists, iUnion_iUnion_eq'] at sm
    have s_eq : s = ⋃ n, s ∩ (f n • (k * k⁻¹)) := by rwa [← inter_iUnion, eq_comm, inter_eq_left]
    have I : μ' s = ∑' n, μ' (disjointed (fun n ↦ s ∩ f n • (k * k⁻¹)) n) := by
      rw [← measure_iUnion (disjoint_disjointed _) M, iUnion_disjointed, ← s_eq]
    have J : ν s = ∑' n, ν (disjointed (fun n ↦ s ∩ f n • (k * k⁻¹)) n) := by
      rw [← measure_iUnion (disjoint_disjointed _) M, iUnion_disjointed, ← s_eq]
    rw [I, J]
    congr with n
    apply measure_isMulInvariant_eq_smul_of_isCompact_closure
    have : IsCompact (f n • (k * k⁻¹)) := IsCompact.smul (f n) (k_comp.mul k_comp.inv)
    exact this.closure_of_subset <| (disjointed_subset _ _).trans inter_subset_right
  · have H : ∀ (ρ : Measure G), IsEverywherePos ρ s → ρ s = ∞ := by
      intro ρ hρ
      have M : ∀ (i : ↑m), MeasurableSet (s ∩ (i : G) • k) :=
        fun i ↦ hs.inter (IsClosed.smul k_closed _).measurableSet
      contrapose! h'm
      have : ∑' (x : m), ρ (s ∩ ((x : G) • k)) < ∞ := by
        apply lt_of_le_of_lt (MeasureTheory.tsum_meas_le_meas_iUnion_of_disjoint _ M _) _
        · have I : PairwiseDisjoint m fun x ↦ s ∩ x • k :=
            hdj.mono (fun x ↦ inter_subset_right)
          exact I.on_injective Subtype.val_injective (fun x ↦ x.2)
        · exact lt_of_le_of_lt (measure_mono (by simp [inter_subset_left])) h'm.lt_top
      have C : Set.Countable (support fun (i : m) ↦ ρ (s ∩ (i : G) • k)) :=
        Summable.countable_support_ennreal this.ne
      have : support (fun (i : m) ↦ ρ (s ∩ (i : G) • k)) = univ := by
        refine eq_univ_iff_forall.2 fun i ↦ ?_
        refine ne_of_gt (hρ (i : G) (hms i.2) _ ?_)
        exact inter_mem_nhdsWithin s (by simpa)
      rw [this] at C
      have : Countable m := countable_univ_iff.mp C
      exact to_countable m
    have Hν : IsEverywherePos ν s :=
      h's.smul_measure_nnreal (haarScalarFactor_pos_of_isHaarMeasure _ _).ne'
    have Hμ' : IsEverywherePos μ' s := by
      apply Hν.of_forall_exists_nhds_eq (fun x _hx ↦ ?_)
      obtain ⟨t, t_comp, t_mem⟩ : ∃ t, IsCompact t ∧ t ∈ 𝓝 x := exists_compact_mem_nhds x
      refine ⟨t, t_mem, fun u hu ↦ ?_⟩
      apply measure_isMulInvariant_eq_smul_of_isCompact_closure
      exact t_comp.closure_of_subset hu
    rw [H ν Hν, H μ' Hμ']

/-- **Uniqueness of Haar measures**:
Given two Haar measures, they coincide in the following sense: they give the same value to open
sets, up to the multiplicative constant `haarScalarFactor μ' μ`. -/
@[to_additive measure_isAddHaarMeasure_eq_smul_of_isOpen
/-- **Uniqueness of Haar measures**:
Given two additive Haar measures, they coincide in the following sense: they give the same value to
open sets, up to the multiplicative constant `addHaarScalarFactor μ' μ`. -/]
/-
**MeasureTheory.Measure.measure_isHaarMeasure_eq_smul_of_isOpen** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：measure_isHaarMeasure_eq_smul_of_isOpen [LocallyCompactSpace G] (μ' μ : Me
asure G) [IsHaarMeasure μ] [IsHaarMeasure μ'] {s : Set G} (hs : IsOpen s) : μ' s
 = haarScalarFactor μ' μ • μ s
参数：μ' μ : Measure G；hs : IsOpen s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.measure_isHaarMeasure_eq_smul_of_isEverywherePos`：
measure_isHaarMeasure_eq_smul_of_isEverywherePos [LocallyCompactSpace G] (μ' μ :
 Measure G) [IsHaarMeasure μ] [IsHaarMeasure μ'] {s : Set G}…
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `IsOpen.isEverywherePos`：∀ {α : Type u_1} [inst : TopologicalSpace α] [in
st_1 : MeasurableSpace α] {μ : MeasureTheory.Measure α} {s : Set α}   [μ.IsOpenP
osMeasure], …
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u_3}
 {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}   {
μ : MeasureTheory.Measure G} [self : μ.IsHaa…
-/
theorem measure_isHaarMeasure_eq_smul_of_isOpen [LocallyCompactSpace G]
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsHaarMeasure μ'] {s : Set G} (hs : IsOpen s) :
    μ' s = haarScalarFactor μ' μ • μ s :=
  measure_isHaarMeasure_eq_smul_of_isEverywherePos μ' μ hs.measurableSet hs.isEverywherePos

/-!
### Uniqueness of Haar measure under regularity assumptions.
-/

/-- **Uniqueness of left-invariant measures**:
Given two left-invariant measures which are finite on
compacts and inner regular for finite measure sets with respect to compact sets,
they coincide in the following sense: they give the same value to finite measure sets,
up to a multiplicative constant. -/
@[to_additive /-- **Uniqueness of left-invariant measures**:
Given two left-invariant measures which are finite on
compacts and inner regular for finite measure sets with respect to compact sets,
they coincide in the following sense: they give the same value to finite measure sets,
up to a multiplicative constant. -/]
/-
**MeasureTheory.Measure.measure_isMulLeftInvariant_eq_smul_of_ne_top** 是 Mathlib
 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：measure_isMulLeftInvariant_eq_smul_of_ne_top [LocallyCompactSpace G] (μ' μ
 : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvaria
nt μ'] [InnerRegularCompactLTTop μ] [InnerRegularCompactLTTop μ'] {s : Set G} (h
s : μ s != ∞) (h's : μ' s != ∞) : μ' s = haarScalarFactor μ' μ • μ s
参数：μ' μ : Measure G；hs : μ s != ∞；h's : μ' s != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasurableSet.measure_eq_iSup_isCompact_of_ne_top`：∀ {α : Type u_1} [ins
t : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace 
α]   [μ.InnerRegularCompactLTTop] ⦃A : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `MeasureTheory.Measure.measure_isMulInvariant_eq_smul_of_isCompact_closur
e`：measure_isMulInvariant_eq_smul_of_isCompact_closure [LocallyCompactSpace G] (
μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts …
· 使用定理 `IsCompact.closure`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R1Space
 X] {K : Set X}, IsCompact K → IsCompact (closure K)
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
（共 36 条，此处仅展示前 30 条）
-/
lemma measure_isMulLeftInvariant_eq_smul_of_ne_top [LocallyCompactSpace G]
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ']
    [InnerRegularCompactLTTop μ] [InnerRegularCompactLTTop μ'] {s : Set G}
    (hs : μ s ≠ ∞) (h's : μ' s ≠ ∞) : μ' s = haarScalarFactor μ' μ • μ s := by
  /- We know that the measures integrate in the same way continuous compactly supported functions,
  up to the factor `c = haarScalarFactor μ' μ`. -/
  let c := haarScalarFactor μ' μ
  /- By regularity, every measurable set of finite measure may be approximated by compact sets.
  Therefore, the measures coincide on measurable sets of finite measure. -/
  have B : ∀ s, MeasurableSet s → μ s < ∞ → μ' s < ∞ → μ' s = (c • μ) s := by
    intro s s_meas hs h's
    have : (c • μ) s ≠ ∞ := by simp [ENNReal.mul_eq_top, hs.ne]
    rw [s_meas.measure_eq_iSup_isCompact_of_ne_top h's.ne,
        s_meas.measure_eq_iSup_isCompact_of_ne_top this]
    congr! 4 with K _Ks K_comp
    exact measure_isMulInvariant_eq_smul_of_isCompact_closure μ' μ K_comp.closure
  /- Finally, replace an arbitrary finite measure set with a measurable version, and use the
  version for measurable sets. -/
  let t := toMeasurable μ' s ∩ toMeasurable μ s
  have st : s ⊆ t := subset_inter (subset_toMeasurable μ' s) (subset_toMeasurable μ s)
  have mu'_t : μ' t = μ' s := by
    apply le_antisymm
    · exact (measure_mono inter_subset_left).trans (measure_toMeasurable s).le
    · exact measure_mono st
  have mu_t : μ t = μ s := by
    apply le_antisymm
    · exact (measure_mono inter_subset_right).trans (measure_toMeasurable s).le
    · exact measure_mono st
  simp only [← mu'_t, ← mu_t, nnreal_smul_coe_apply]
  apply B
  · exact (measurableSet_toMeasurable _ _).inter (measurableSet_toMeasurable _ _)
  · exact mu_t.le.trans_lt hs.lt_top
  · exact mu'_t.le.trans_lt h's.lt_top

/-- **Uniqueness of left-invariant measures**:
Given two left-invariant measures which are finite
on compacts and inner regular, they coincide up to a multiplicative constant. -/
@[to_additive isAddLeftInvariant_eq_smul_of_innerRegular
/-- **Uniqueness of left-invariant measures**:
Given two left-invariant measures which are finite
on compacts and inner regular, they coincide up to a multiplicative constant. -/]
/-
**MeasureTheory.Measure.isMulLeftInvariant_eq_smul_of_innerRegular** 是 Mathlib 中
的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：isMulLeftInvariant_eq_smul_of_innerRegular [LocallyCompactSpace G] (μ' μ :
 Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant
 μ'] [InnerRegular μ] [InnerRegular μ'] : μ' = haarScalarFactor μ' μ • μ
参数：μ' μ : Measure G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableSet.measure_eq_iSup_isCompact`：∀ {α : Type u_1} [inst : Measur
ableSpace α] [inst_1 : TopologicalSpace α] ⦃U : Set α⦄,   MeasurableSet U → ∀ (μ
 : MeasureTheory.Measure α) […
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `MeasureTheory.Measure.measure_isMulLeftInvariant_eq_smul_of_ne_top`：meas
ure_isMulLeftInvariant_eq_smul_of_ne_top [LocallyCompactSpace G] (μ' μ : Measure
 G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [Is…
· 使用定理 `MeasureTheory.Measure.InnerRegular.instInnerRegularCompactLTTop`：∀ {α : 
Type u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Top
ologicalSpace α]   [μ.InnerRegular], μ.InnerRegularCo…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `IsCompact.measure_lt_top`：∀ {α : Type u_1} {m0 : MeasurableSpace α} [ins
t : TopologicalSpace α] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsFiniteM
easureOnCompac…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
-/
lemma isMulLeftInvariant_eq_smul_of_innerRegular [LocallyCompactSpace G]
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ']
    [InnerRegular μ] [InnerRegular μ'] :
    μ' = haarScalarFactor μ' μ • μ := by
  ext s hs
  rw [hs.measure_eq_iSup_isCompact, hs.measure_eq_iSup_isCompact]
  congr! 4 with K _Ks K_comp
  exact measure_isMulLeftInvariant_eq_smul_of_ne_top μ' μ K_comp.measure_lt_top.ne
    K_comp.measure_lt_top.ne

/-- **Uniqueness of left-invariant measures**:
Given two left-invariant measures which are finite
on compacts and regular, they coincide up to a multiplicative constant. -/
@[to_additive isAddLeftInvariant_eq_smul_of_regular
/-- **Uniqueness of left-invariant measures**:
Given two left-invariant measures which are finite
on compacts and regular, they coincide up to a multiplicative constant. -/]
/-
**MeasureTheory.Measure.isMulLeftInvariant_eq_smul_of_regular** 是 Mathlib 中的一个引理
，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：isMulLeftInvariant_eq_smul_of_regular [LocallyCompactSpace G] (μ' μ : Meas
ure G) [IsHaarMeasure μ] [IsMulLeftInvariant μ'] [Regular μ] [Regular μ'] : μ' =
 haarScalarFactor μ' μ • μ
参数：μ' μ : Measure G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.Regular.toIsFiniteMeasureOnCompacts`：∀ {α : Type u
_1} {inst : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.
Measure α}   [self : μ.Regular], MeasureTheory.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOpen.measure_eq_iSup_isCompact`：∀ {α : Type u_1} [inst : MeasurableSpa
ce α] [inst_1 : TopologicalSpace α] ⦃U : Set α⦄,   IsOpen U → ∀ (μ : MeasureTheo
ry.Measure α) [μ.Regul…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `MeasureTheory.Measure.measure_isMulLeftInvariant_eq_smul_of_ne_top`：meas
ure_isMulLeftInvariant_eq_smul_of_ne_top [LocallyCompactSpace G] (μ' μ : Measure
 G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [Is…
· 使用定理 `MeasureTheory.Measure.Regular.instInnerRegularCompactLTTop`：∀ {α : Type 
u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topologi
calSpace α] [μ.Regular],   μ.InnerRegularCompact…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `IsCompact.measure_lt_top`：∀ {α : Type u_1} {m0 : MeasurableSpace α} [ins
t : TopologicalSpace α] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsFiniteM
easureOnCompac…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `MeasureTheory.Measure.OuterRegular.ext_isOpen`：ext_isOpen {ν : Measure α
} [OuterRegular μ] [OuterRegular ν] (hμν : forall U, IsOpen U -> μ U = ν U) : μ 
= ν
· 使用定理 `MeasureTheory.Measure.WeaklyRegular.toOuterRegular`：∀ {α : Type u_1} {in
st : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.Measure
 α}   [self : μ.WeaklyRegular], μ.OuterR…
· 使用定理 `MeasureTheory.Measure.Regular.weaklyRegular`：∀ {α : Type u_1} [inst : Me
asurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α] [R1
Space α]   [μ.Regular], μ.WeaklyR…
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
-/
lemma isMulLeftInvariant_eq_smul_of_regular [LocallyCompactSpace G]
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsMulLeftInvariant μ'] [Regular μ] [Regular μ'] :
    μ' = haarScalarFactor μ' μ • μ := by
  have A : ∀ U, IsOpen U → μ' U = (haarScalarFactor μ' μ • μ) U := by
    intro U hU
    rw [hU.measure_eq_iSup_isCompact, hU.measure_eq_iSup_isCompact]
    congr! 4 with K _KU K_comp
    exact measure_isMulLeftInvariant_eq_smul_of_ne_top μ' μ K_comp.measure_lt_top.ne
      K_comp.measure_lt_top.ne
  exact OuterRegular.ext_isOpen A

/-- **Uniqueness of left-invariant measures**:
Two Haar measures coincide up to a multiplicative constant in a second countable group. -/
@[to_additive isAddLeftInvariant_eq_smul
/-- **Uniqueness of left-invariant measures**:
Two additive Haar measures coincide up to a multiplicative constant in a second countable group. -/]
/-
**MeasureTheory.Measure.isMulLeftInvariant_eq_smul** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：isMulLeftInvariant_eq_smul [LocallyCompactSpace G] [SecondCountableTopolog
y G] (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulL
eftInvariant μ'] : μ' = haarScalarFactor μ' μ • μ
参数：μ' μ : Measure G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.isMulLeftInvariant_eq_smul_of_regular`：isMulLeftIn
variant_eq_smul_of_regular [LocallyCompactSpace G] (μ' μ : Measure G) [IsHaarMea
sure μ] [IsMulLeftInvariant μ'] [Regular μ] [Regu…
· 使用定理 `MeasureTheory.Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMea
sure`：∀ {X : Type u_3} [inst : TopologicalSpace X] [TopologicalSpace.PseudoMetri
zableSpace X] [SigmaCompactSpace X]   [inst_3 : MeasurableSpace X]…
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.of_regularSpace_secondCountableTo
pology`：∀ (X : Type u_1) [inst : TopologicalSpace X] [RegularSpace X] [SecondCou
ntableTopology X],   TopologicalSpace.PseudoMetrizableSpace X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `SeparableWeaklyLocallyCompactGroup.sigmaCompactSpace`：∀ {G : Type w} [in
st : TopologicalSpace G] [inst_1 : Group G] [IsTopologicalGroup G] [TopologicalS
pace.SeparableSpace G]   [WeaklyLocallyCom…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `MeasureTheory.isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts`：∀ {α 
: Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topol
ogicalSpace α]   [WeaklyLocallyCompactSpace α] [Measure…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
-/
lemma isMulLeftInvariant_eq_smul [LocallyCompactSpace G] [SecondCountableTopology G]
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] :
    μ' = haarScalarFactor μ' μ • μ :=
  isMulLeftInvariant_eq_smul_of_regular μ' μ
  -- one could use as well `isMulLeftInvariant_eq_smul_of_innerRegular`, as in a
  -- second countable topological space all Haar measures are regular and inner regular


/-- An invariant σ-finite measure is absolutely continuous with respect to a Haar measure in a
second countable group. -/
@[to_additive
/-- An invariant measure is absolutely continuous with respect to an additive Haar measure. -/]
/-
**MeasureTheory.Measure.absolutelyContinuous_isHaarMeasure** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.Measure`。
形式化陈述：absolutelyContinuous_isHaarMeasure [LocallyCompactSpace G] [SecondCountabl
eTopology G] (μ ν : Measure G) [SigmaFinite μ] [IsMulLeftInvariant μ] [IsHaarMea
sure ν] : μ ≪ ν
参数：μ ν : Measure G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `Torsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : Grou
p G} [self : Torsor G P], Nonempty P
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用引理 `MeasureTheory.Measure.isMulLeftInvariant_eq_smul`：isMulLeftInvariant_eq_
smul [LocallyCompactSpace G] [SecondCountableTopology G] (μ' μ : Measure G) [IsH
aarMeasure μ] [IsFiniteMeasureOnCompac…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.haarMeasure_unique`：haarMeasure_unique (μ : Measur
e G) [SigmaFinite μ] [IsMulLeftInvariant μ] (K₀ : PositiveCompacts G) : μ = μ K₀
 • haarMeasure K₀
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用引理 `MeasureTheory.Measure.smul_absolutelyContinuous`：smul_absolutelyContinuo
us {c : Real>=0∞} : c • μ ≪ μ
-/
theorem absolutelyContinuous_isHaarMeasure [LocallyCompactSpace G]
    [SecondCountableTopology G] (μ ν : Measure G)
    [SigmaFinite μ] [IsMulLeftInvariant μ] [IsHaarMeasure ν] : μ ≪ ν := by
  have K : PositiveCompacts G := Classical.arbitrary _
  have h : haarMeasure K = (haarScalarFactor (haarMeasure K) ν : ℝ≥0∞) • ν :=
    isMulLeftInvariant_eq_smul (haarMeasure K) ν
  rw [haarMeasure_unique μ K, h, smul_smul]
  exact smul_absolutelyContinuous

/-- A continuous surjective monoid homomorphism of topological groups with compact codomain
is measure preserving, provided that the Haar measures on the domain and on the codomain
have the same total mass.
-/
@[to_additive
  /-- A continuous surjective additive monoid homomorphism of topological groups with compact
  codomain is measure preserving, provided that the Haar measures on the domain and on the codomain
  have the same total mass. -/]
/-
**MeasureTheory.Measure._root_.MonoidHom.measurePreserving** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MonoidHom.measurePreserving
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    [MeasurableSpace H] [BorelSpace H]
    {μ : Measure G} [IsHaarMeasure μ] {ν : Measure H} [IsHaarMeasure ν]
    {f : G →* H} (hcont : Continuous f) (hsurj : Surjective f) (huniv : μ univ = ν univ) :
    MeasurePreserving f μ ν where
  measurable := hcont.measurable
  map_eq := by
    have : IsFiniteMeasure μ := ⟨by rw [huniv]; apply measure_lt_top⟩
    have : (μ.map f).IsHaarMeasure := isHaarMeasure_map_of_isFiniteMeasure μ f hcont hsurj
    set C : ℝ≥0 := haarScalarFactor (μ.map f) ν
    have hC : μ.map f = C • ν := isMulLeftInvariant_eq_smul_of_innerRegular _ _
    suffices C = 1 by rwa [this, one_smul] at hC
    have : C * ν univ = 1 * ν univ := by
      rw [one_mul, ← smul_eq_mul, ← ENNReal.smul_def, ← smul_apply, ← hC,
        map_apply hcont.measurable .univ, preimage_univ, huniv]
    rwa [ENNReal.mul_left_inj (NeZero.ne _) (measure_ne_top _ _), ENNReal.coe_eq_one] at this

end Group

section CommGroup

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsHaarMeasure μ]

/-- Any regular Haar measure is invariant under inversion in an abelian group. -/
@[to_additive
/-- Any regular additive Haar measure is invariant under negation in an abelian group. -/]
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsHaarMeasure.isInvInvariant_of_regular
    [LocallyCompactSpace G] [Regular μ] : IsInvInvariant μ := by
  -- the image measure is a Haar measure. By uniqueness up to multiplication, it is of the form
  -- `c μ`. Applying again inversion, one gets the measure `c^2 μ`. But since inversion is an
  -- involution, this is also `μ`. Hence, `c^2 = 1`, which implies `c = 1`.
  constructor
  let c : ℝ≥0∞ := haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := isMulLeftInvariant_eq_smul_of_regular μ.inv μ
  have : map Inv.inv (map Inv.inv μ) = c ^ 2 • μ := by
    rw [← inv_def μ, hc, Measure.map_smul, ← inv_def μ, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [map_map continuous_inv.measurable continuous_inv.measurable] at this
    simpa only [inv_involutive, Involutive.comp_self, Measure.map_id]
  have K : PositiveCompacts G := Classical.arbitrary _
  have : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
          K.isCompact.measure_lt_top.ne).1 this
  have : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective this
  rw [hc, this, one_smul]

/-- Any inner regular Haar measure is invariant under inversion in an abelian group. -/
@[to_additive
/-- Any regular additive Haar measure is invariant under negation in an abelian group. -/]
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsHaarMeasure.isInvInvariant_of_innerRegular
    [LocallyCompactSpace G] [InnerRegular μ] : IsInvInvariant μ := by
  -- the image measure is a Haar measure. By uniqueness up to multiplication, it is of the form
  -- `c μ`. Applying again inversion, one gets the measure `c^2 μ`. But since inversion is an
  -- involution, this is also `μ`. Hence, `c^2 = 1`, which implies `c = 1`.
  constructor
  let c : ℝ≥0∞ := haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := isMulLeftInvariant_eq_smul_of_innerRegular μ.inv μ
  have : map Inv.inv (map Inv.inv μ) = c ^ 2 • μ := by
    rw [← inv_def μ, hc, Measure.map_smul, ← inv_def μ, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [map_map continuous_inv.measurable continuous_inv.measurable] at this
    simpa only [inv_involutive, Involutive.comp_self, Measure.map_id]
  have K : PositiveCompacts G := Classical.arbitrary _
  have : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
          K.isCompact.measure_lt_top.ne).1 this
  have : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective this
  rw [hc, this, one_smul]

@[to_additive]
/-
**MeasureTheory.Measure.measurePreserving_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：measurePreserving_zpow [CompactSpace G] [RootableBy G Int] {n : Int} (hn :
 n != 0) : MeasurePreserving (fun g : G => g ^ n) μ μ
参数：hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.measurePreserving`：∀ {G : Type u_1} [inst : TopologicalSpace G
] [inst_1 : Group G] [IsTopologicalGroup G] [inst_3 : MeasurableSpace G]   [Bore
lSpace G] {H : Ty…
· 使用定理 `continuous_zpow`：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1 : Gr
oup G] [IsTopologicalGroup G] (z : ℤ), Continuous fun a => a ^ z
· 使用定理 `RootableBy.surjective_pow`：RootableBy.surjective_pow [RootableBy A α] {n
 : α} (hn : n != 0) : Function.Surjective fun a : A => a ^ n
-/
theorem measurePreserving_zpow [CompactSpace G] [RootableBy G ℤ] {n : ℤ} (hn : n ≠ 0) :
    MeasurePreserving (fun g : G => g ^ n) μ μ :=
  (zpowGroupHom n).measurePreserving (μ := μ) (continuous_zpow n)
    (RootableBy.surjective_pow G ℤ hn) rfl

@[to_additive]
/-
**MeasureTheory.Measure.MeasurePreserving.zpow** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure.MeasurePreserving`。
形式化陈述：∀ {G : Type u_1} [inst : CommGroup G] [inst_1 : TopologicalSpace G] [IsTop
ologicalGroup G] [inst_3 : MeasurableSpace G]   [BorelSpace G] (μ : MeasureTheor
y.Measure G) [μ.IsHaarMeasure] [CompactSpace G] [RootableBy G ℤ] {n : ℤ},   n ≠ 
0 →     ∀ {X : Type u_2} [inst_8 : MeasurableSpace X] {μ' : MeasureTheory.Measur
e X} {f : X → G},       MeasureTheory.MeasurePreserving f μ' μ → MeasureTheory.M
easurePreserving (fun x => f x ^ n) μ' μ
参数：μ : MeasureTheory.Measure G；fun x => f x ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.comp`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 :
 MeasurableSpace γ] {μa : …
· 使用定理 `MeasureTheory.Measure.measurePreserving_zpow`：measurePreserving_zpow [Co
mpactSpace G] [RootableBy G Int] {n : Int} (hn : n != 0) : MeasurePreserving (fu
n g : G => g ^ n) μ μ
-/
theorem MeasurePreserving.zpow [CompactSpace G] [RootableBy G ℤ]
    {n : ℤ} (hn : n ≠ 0) {X : Type*}
    [MeasurableSpace X] {μ' : Measure X} {f : X → G} (hf : MeasurePreserving f μ' μ) :
    MeasurePreserving (fun x => f x ^ n) μ' μ :=
  (measurePreserving_zpow μ hn).comp hf

end CommGroup

section DistribMulAction
variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A] [MeasurableSpace A]
  [TopologicalSpace A] [BorelSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
  [ContinuousConstSMul G A] {μ ν : Measure A} [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] {g : G}

variable (μ ν) in
/-
**MeasureTheory.Measure.addHaarScalarFactor_domSMul** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory.Measure`。
形式化陈述：addHaarScalarFactor_domSMul (g : Gᵈᵐᵃ) : addHaarScalarFactor (g • μ) (g • 
ν) = addHaarScalarFactor μ ν
参数：g : Gᵈᵐᵃ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousConstSMul.toMeasurableConstSMul`：∀ {M : Type u_7} {α : Type u_
8} [inst : TopologicalSpace α] [inst_1 : MeasurableSpace α] [BorelSpace α]   [in
st_3 : SMul M α] [ContinuousCon…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.domSMul`：∀ {G : Type u_3} {A : Ty
pe u_4} [inst : Group G] [inst_1 : AddCommGroup A] [inst_2 : DistribMulAction G 
A]   [inst_3 : MeasurableSpace A] [i…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `exists_continuous_nonneg_pos`：exists_continuous_nonneg_pos [RegularSpace
 X] [LocallyCompactSpace X] (x : X) : exists f : C(X, Real), HasCompactSupport f
 ∧ 0 <= (f : X -> …
· 使用定理 `IsTopologicalAddGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSp
ace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], RegularSpace G
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero`：Continuous.
integral_pos_of_hasCompactSupport_nonneg_nonzero [IsFiniteMeasureOnCompacts μ] {
f : X -> Real} {x : X} (f_cont : Continuous f) (f…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u
_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace 
G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `NNReal.coe_injective`：Function.Injective NNReal.toReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.addHaarScalarFactor_eq_integral_div`：∀ {G : Type u
_1} [inst : TopologicalSpace G] [inst_1 : AddGroup G] [inst_2 : IsTopologicalAdd
Group G]   [inst_3 : MeasurableSpace G] [inst_4…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `MeasureTheory.integral_domSMul`：integral_domSMul {G A : Type*} [Group G]
 [AddCommGroup A] [DistribMulAction G A] [MeasurableSpace A] [MeasurableConstSMu
l G A] {μ : Measure …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Continuous.fun_const_smul`：∀ {M : Type u_1} {α : Type u_2} {β : Type u_3
} [inst : TopologicalSpace α] [inst_1 : SMul M α] [ContinuousConstSMul M α]   [i
nst_3 : Topolog…
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `HasCompactSupport.comp_isClosedEmbedding`：∀ {α : Type u_2} {α' : Type u_
3} {β : Type u_4} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace α']   [
inst_2 : Zero β] {f : α → β}, …
· 使用定理 `Homeomorph.isClosedEmbedding`：isClosedEmbedding (h : X ≃ₜ Y) : IsClosedE
mbedding h
-/
lemma addHaarScalarFactor_domSMul (g : Gᵈᵐᵃ) :
    addHaarScalarFactor (g • μ) (g • ν) = addHaarScalarFactor μ ν := by
  obtain ⟨⟨f, f_cont⟩, f_comp, f_nonneg, f_zero⟩ :
    ∃ f : C(A, ℝ), HasCompactSupport f ∧ 0 ≤ f ∧ f 0 ≠ 0 := exists_continuous_nonneg_pos 0
  have int_f_ne_zero : ∫ x, f x ∂g • ν ≠ 0 :=
    (f_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero f_comp f_nonneg f_zero).ne'
  apply NNReal.coe_injective
  rw [addHaarScalarFactor_eq_integral_div (g • μ) (g • ν) f_cont f_comp int_f_ne_zero,
    integral_domSMul, integral_domSMul]
  refine (addHaarScalarFactor_eq_integral_div _ _ (by fun_prop) ?_ ?_).symm
  · exact f_comp.comp_isClosedEmbedding (Homeomorph.smul _).isClosedEmbedding
  · rw [← integral_domSMul]
    exact (f_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero f_comp f_nonneg f_zero).ne'

variable (μ) in
/-
**MeasureTheory.Measure.addHaarScalarFactor_smul_congr** 是 Mathlib 中的一个引理，位于命名空间
 `MeasureTheory.Measure`。
形式化陈述：addHaarScalarFactor_smul_congr (g : Gᵈᵐᵃ) : addHaarScalarFactor μ (g • μ) 
= addHaarScalarFactor ν (g • ν)
参数：g : Gᵈᵐᵃ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousConstSMul.toMeasurableConstSMul`：∀ {M : Type u_7} {α : Type u_
8} [inst : TopologicalSpace α] [inst_1 : MeasurableSpace α] [BorelSpace α]   [in
st_3 : SMul M α] [ContinuousCon…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.domSMul`：∀ {G : Type u_3} {A : Ty
pe u_4} [inst : Group G] [inst_1 : AddCommGroup A] [inst_2 : DistribMulAction G 
A]   [inst_3 : MeasurableSpace A] [i…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.addHaarScalarFactor_eq_mul`：∀ {G : Type u_1} [inst
 : TopologicalSpace G] [inst_1 : AddGroup G] [inst_2 : IsTopologicalAddGroup G] 
  [inst_3 : MeasurableSpace G] [inst_4…
· 使用引理 `MeasureTheory.Measure.addHaarScalarFactor_domSMul`：addHaarScalarFactor_d
omSMul (g : Gᵈᵐᵃ) : addHaarScalarFactor (g • μ) (g • ν) = addHaarScalarFactor μ 
ν
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma addHaarScalarFactor_smul_congr (g : Gᵈᵐᵃ) :
    addHaarScalarFactor μ (g • μ) = addHaarScalarFactor ν (g • ν) := by
  rw [addHaarScalarFactor_eq_mul _ (g • ν), addHaarScalarFactor_domSMul,
    mul_comm, ← addHaarScalarFactor_eq_mul]

variable (μ) in
/-
**MeasureTheory.Measure.addHaarScalarFactor_smul_congr'** 是 Mathlib 中的一个引理，位于命名空
间 `MeasureTheory.Measure`。
形式化陈述：addHaarScalarFactor_smul_congr' (g : Gᵈᵐᵃ) : addHaarScalarFactor (g • μ) μ
 = addHaarScalarFactor (g • ν) ν
参数：g : Gᵈᵐᵃ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousConstSMul.toMeasurableConstSMul`：∀ {M : Type u_7} {α : Type u_
8} [inst : TopologicalSpace α] [inst_1 : MeasurableSpace α] [BorelSpace α]   [in
st_3 : SMul M α] [ContinuousCon…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.domSMul`：∀ {G : Type u_3} {A : Ty
pe u_4} [inst : Group G] [inst_1 : AddCommGroup A] [inst_2 : DistribMulAction G 
A]   [inst_3 : MeasurableSpace A] [i…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.addHaarScalarFactor_eq_mul`：∀ {G : Type u_1} [inst
 : TopologicalSpace G] [inst_1 : AddGroup G] [inst_2 : IsTopologicalAddGroup G] 
  [inst_3 : MeasurableSpace G] [inst_4…
· 使用引理 `MeasureTheory.Measure.addHaarScalarFactor_domSMul`：addHaarScalarFactor_d
omSMul (g : Gᵈᵐᵃ) : addHaarScalarFactor (g • μ) (g • ν) = addHaarScalarFactor μ 
ν
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma addHaarScalarFactor_smul_congr' (g : Gᵈᵐᵃ) :
    addHaarScalarFactor (g • μ) μ = addHaarScalarFactor (g • ν) ν := by
  rw [addHaarScalarFactor_eq_mul _ (g • ν), addHaarScalarFactor_domSMul,
    mul_comm, ← addHaarScalarFactor_eq_mul]

end DistribMulAction
end Measure

end MeasureTheory

