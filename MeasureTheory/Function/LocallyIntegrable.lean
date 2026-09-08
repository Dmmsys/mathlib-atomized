/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Locally integrable functions

A function is called *locally integrable* (`MeasureTheory.LocallyIntegrable`) if it is integrable
on a neighborhood of every point. More generally, it is *locally integrable on `s`* if it is
locally integrable on a neighbourhood within `s` of any point of `s`.

This file contains properties of locally integrable functions, and integrability results
on compact sets.

## Main statements

* `Continuous.locallyIntegrable`: A continuous function is locally integrable.
* `ContinuousOn.locallyIntegrableOn`: A function which is continuous on `s` is locally
  integrable on `s`.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Function TopologicalSpace Bornology Filter

open scoped Topology Interval ENNReal

variable {X Y ε ε' ε'' E F R : Type*} [MeasurableSpace X] [TopologicalSpace X]
variable [MeasurableSpace Y] [TopologicalSpace Y]
variable [TopologicalSpace ε] [ContinuousENorm ε] [TopologicalSpace ε'] [ContinuousENorm ε']
  [TopologicalSpace ε''] [ESeminormedAddMonoid ε'']
  [NormedAddCommGroup E] [NormedAddCommGroup F] {f g : X → ε} {μ ν : Measure X} {s : Set X}

namespace MeasureTheory

section LocallyIntegrableOn

/-- A function `f : X → E` is *locally integrable on s*, for `s ⊆ X`, if for every `x ∈ s` there is
a neighbourhood of `x` within `s` on which `f` is integrable.

Note that this is, in general, strictly weaker than local integrability with respect to
`μ.restrict s`. For example, `fun (x : ℝ) ↦ 1/x` is locally integrable on `Set.Ioo 0 1` with
respect to the Lebesgue measure, but it is *not* locally integrable with respect to the
Lebesgue measure restricted to `Set.Ioo 0 1`. -/
/-
**MeasureTheory.LocallyIntegrableOn** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：LocallyIntegrableOn (f : X -> ε) (s : Set X) (μ : Measure X
参数：f : X -> ε；s : Set X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : X → E` is *locally integrable on s*, for `s ⊆ X`, if for every `
x ∈ s` there is
a neighbourhood of `x` within `s` on which `f` is integrable.

Note that this is, in general, strictly weaker than local integrability with res
pect to
`μ.restrict s`. For example, `fun (x : ℝ) ↦ 1/x` is locally integrable on `Set.I
oo 0 1` with
respect to the Lebesgue measure, but it is *not* locally integrable with respect
 to the
Lebesgue measure restricted to `Set.Ioo 0 1`.
-/
def LocallyIntegrableOn (f : X → ε) (s : Set X) (μ : Measure X := by volume_tac) : Prop :=
  ∀ x : X, x ∈ s → IntegrableAtFilter f (𝓝[s] x) μ

@[gcongr]
/-
**MeasureTheory.LocallyIntegrableOn.mono_set** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.LocallyIntegrableOn`。
形式化陈述：∀ {X : Type u_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : TopologicalSpace ε]   [inst_3 : ContinuousENorm ε] {f :
 X → ε} {μ : MeasureTheory.Measure X} {s : Set X},   MeasureTheory.LocallyIntegr
ableOn f s μ → ∀ {t : Set X}, t ⊆ s → MeasureTheory.LocallyIntegrableOn f t μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableAtFilter.filter_mono`：∀ {α : Type u_1} {ε : Type
 u_3} {mα : MeasurableSpace α} {f : α → ε} {μ : MeasureTheory.Measure α}   [inst
 : TopologicalSpace ε] [inst_1 : C…
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
-/
theorem LocallyIntegrableOn.mono_set (hf : LocallyIntegrableOn f s μ) {t : Set X}
    (hst : t ⊆ s) : LocallyIntegrableOn f t μ := fun x hx =>
  (hf x <| hst hx).filter_mono (nhdsWithin_mono x hst)
/-
**MeasureTheory.LocallyIntegrableOn.enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.LocallyIntegrableOn`。
形式化陈述：∀ {X : Type u_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : TopologicalSpace ε]   [inst_3 : ContinuousENorm ε] {f :
 X → ε} {μ : MeasureTheory.Measure X} {s : Set X},   MeasureTheory.LocallyIntegr
ableOn f s μ → MeasureTheory.LocallyIntegrableOn (fun x => ‖f x‖ₑ) s μ
参数：fun x => ‖f x‖ₑ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.enorm`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
-/
theorem LocallyIntegrableOn.enorm (hf : LocallyIntegrableOn f s μ) :
    LocallyIntegrableOn (‖f ·‖ₑ) s μ := fun t ht ↦
  let ⟨U, hU_nhd, hU_int⟩ := hf t ht
  ⟨U, hU_nhd, hU_int.enorm⟩
/-
**MeasureTheory.LocallyIntegrableOn.norm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.LocallyIntegrableOn`。
形式化陈述：∀ {X : Type u_1} {E : Type u_6} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : NormedAddCommGroup E]   {μ : MeasureTheory.Measure X} {
s : Set X} {f : X → E},   MeasureTheory.LocallyIntegrableOn f s μ → MeasureTheor
y.LocallyIntegrableOn (fun x => ‖f x‖) s μ
参数：fun x => ‖f x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
-/
theorem LocallyIntegrableOn.norm {f : X → E} (hf : LocallyIntegrableOn f s μ) :
    LocallyIntegrableOn (fun x => ‖f x‖) s μ := fun t ht =>
  let ⟨U, hU_nhd, hU_int⟩ := hf t ht
  ⟨U, hU_nhd, hU_int.norm⟩
/-
**MeasureTheory.LocallyIntegrableOn.mono_enorm** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.LocallyIntegrableOn`。
形式化陈述：∀ {X : Type u_1} {ε : Type u_3} {ε' : Type u_4} [inst : MeasurableSpace X]
 [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpace ε] [inst_3 : Continu
ousENorm ε] [inst_4 : TopologicalSpace ε']   [inst_5 : ContinuousENorm ε'] {f : 
X → ε} {μ : MeasureTheory.Measure X} {s : Set X},   MeasureTheory.LocallyIntegra
bleOn f s μ →     ∀ {g : X → ε'},       MeasureTheory.AEStronglyMeasurable g μ →
         (∀ᵐ (x : X) ∂μ, ‖g x‖ₑ ≤ ‖f x‖ₑ) → MeasureTheory.LocallyIntegrableOn g 
s μ
参数：∀ᵐ (x : X) ∂μ, ‖g x‖ₑ ≤ ‖f x‖ₑ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.mono_enorm`：∀ {α : Type u_1} {ε : Type u_5} {ε'
 : Type u_6} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : Top
ologicalSpace ε] [inst_1 …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.restrict`：∀ {α : Type u_1} {β : Type 
u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   {f : α → β},   Measur…
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
-/
theorem LocallyIntegrableOn.mono_enorm (hf : LocallyIntegrableOn f s μ) {g : X → ε'}
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ x ∂μ, ‖g x‖ₑ ≤ ‖f x‖ₑ) :
    LocallyIntegrableOn g s μ := by
  intro x hx
  rcases hf x hx with ⟨t, t_mem, ht⟩
  exact ⟨t, t_mem, ht.mono_enorm hg.restrict (ae_restrict_of_ae h)⟩
/-
**MeasureTheory.LocallyIntegrableOn.mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.LocallyIntegrableOn`。
形式化陈述：∀ {X : Type u_1} {E : Type u_6} {F : Type u_7} [inst : MeasurableSpace X] 
[inst_1 : TopologicalSpace X]   [inst_2 : NormedAddCommGroup E] [inst_3 : Normed
AddCommGroup F] {μ : MeasureTheory.Measure X} {s : Set X} {f : X → E},   Measure
Theory.LocallyIntegrableOn f s μ →     ∀ {g : X → F},       MeasureTheory.AEStro
nglyMeasurable g μ → (∀ᵐ (x : X) ∂μ, ‖g x‖ ≤ ‖f x‖) → MeasureTheory.LocallyInteg
rableOn g s μ
参数：∀ᵐ (x : X) ∂μ, ‖g x‖ ≤ ‖f x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.mono`：∀ {α : Type u_1} {β : Type u_2} {γ : Type
 u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedAddC
ommGroup β] [inst_1…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.restrict`：∀ {α : Type u_1} {β : Type 
u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   {f : α → β},   Measur…
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
-/
theorem LocallyIntegrableOn.mono {f : X → E} (hf : LocallyIntegrableOn f s μ) {g : X → F}
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖f x‖) :
    LocallyIntegrableOn g s μ := by
  intro x hx
  rcases hf x hx with ⟨t, t_mem, ht⟩
  exact ⟨t, t_mem, Integrable.mono ht hg.restrict (ae_restrict_of_ae h)⟩
/-
**MeasureTheory.LocallyIntegrableOn.mono_measure'** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.LocallyIntegrableOn`。
形式化陈述：∀ {X : Type u_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : TopologicalSpace ε]   [inst_3 : ContinuousENorm ε] {f :
 X → ε} {μ ν : MeasureTheory.Measure X} {s : Set X} [OpensMeasurableSpace X],   
MeasureTheory.LocallyIntegrableOn f s μ → ν.restrict s ≤ μ.restrict s → MeasureT
heory.LocallyIntegrableOn f s ν
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsWithin`：mem_nhdsWithin {t : Set α} {a : α} {s : Set α} : t in 𝓝[
s] a ↔ exists u, IsOpen u ∧ a in u ∧ u inter s subseteq t
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `MeasureTheory.IntegrableOn.mono_measure'`：∀ {α : Type u_1} {ε : Type u_3
} {mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ ν : MeasureTheory.Measure 
α}   [inst : TopologicalSpace …
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.restrict_restrict`：restrict_restrict (hs : Measura
bleSet s) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `MeasureTheory.Measure.restrict_mono`：restrict_mono {_m0 : MeasurableSpac
e α} ⦃s s' : Set α⦄ (hs : s subseteq s') ⦃μ ν : Measure α⦄ (hμν : μ <= ν) : μ.re
strict s <= ν.restrict s'
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma LocallyIntegrableOn.mono_measure' [OpensMeasurableSpace X] (hf : LocallyIntegrableOn f s μ)
    (h : ν.restrict s ≤ μ.restrict s) : LocallyIntegrableOn f s ν := by
  intro x hx
  obtain ⟨t, ht, hf⟩ := hf x hx
  obtain ⟨u, hu, hxu, hut⟩ := mem_nhdsWithin.mp ht
  refine ⟨u ∩ s, inter_mem (mem_nhdsWithin.mpr ⟨u, hu, hxu, inter_subset_left⟩) self_mem_nhdsWithin,
    ?_⟩
  refine hf.mono_set hut |>.mono_measure' ?_
  simp_rw [← restrict_restrict hu.measurableSet]
  gcongr

@[gcongr]
/-
**MeasureTheory.LocallyIntegrableOn.mono_measure** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.LocallyIntegrableOn`。
形式化陈述：∀ {X : Type u_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : TopologicalSpace ε]   [inst_3 : ContinuousENorm ε] {f :
 X → ε} {μ ν : MeasureTheory.Measure X} {s : Set X},   MeasureTheory.LocallyInte
grableOn f s μ → ν ≤ μ → MeasureTheory.LocallyIntegrableOn f s ν
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableAtFilter.mono_measure`：∀ {α : Type u_1} {ε : Typ
e u_3} {mα : MeasurableSpace α} {f : α → ε} {μ ν : MeasureTheory.Measure α}   [i
nst : TopologicalSpace ε] [inst_1 :…
-/
lemma LocallyIntegrableOn.mono_measure (hf : LocallyIntegrableOn f s μ) (h : ν ≤ μ) :
    LocallyIntegrableOn f s ν :=
  fun x hx ↦ (hf x hx).mono_measure h

@[gcongr]
/-
**MeasureTheory.LocallyIntegrableOn.congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.LocallyIntegrableOn`。
形式化陈述：∀ {X : Type u_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : TopologicalSpace ε]   [inst_3 : ContinuousENorm ε] {f g
 : X → ε} {μ : MeasureTheory.Measure X} {s : Set X},   f =ᵐ[μ.restrict s] g → Me
asureTheory.LocallyIntegrableOn f s μ → MeasureTheory.LocallyIntegrableOn g s μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `MeasureTheory.Integrable.congr`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `MeasureTheory.ae_mono`：ae_mono (h : μ <= ν) : ae μ <= ae ν
· 使用定理 `MeasureTheory.Measure.restrict_mono`：restrict_mono {_m0 : MeasurableSpac
e α} ⦃s s' : Set α⦄ (hs : s subseteq s') ⦃μ ν : Measure α⦄ (hμν : μ <= ν) : μ.re
strict s <= ν.restrict s'
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma LocallyIntegrableOn.congr (h : f =ᵐ[μ.restrict s] g) (hf : LocallyIntegrableOn f s μ) :
    LocallyIntegrableOn g s μ := by
  intro x hx
  obtain ⟨t, hxt, hft⟩ := hf x hx
  refine ⟨s ∩ t, inter_mem self_mem_nhdsWithin hxt, ?_⟩
  refine (hft.mono_set inter_subset_right).congr ?_
  refine h.filter_mono ?_
  gcongr
  exact inter_subset_left
/-
**MeasureTheory.locallyIntegrableOn_congr** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：locallyIntegrableOn_congr (h : f =ᵐ[μ.restrict s] g) : LocallyIntegrableOn
 f s μ ↔ LocallyIntegrableOn g s μ
参数：h : f =ᵐ[μ.restrict s] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.LocallyIntegrableOn.congr`：∀ {X : Type u_1} {ε : Type u_3}
 [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 : TopologicalS
pace ε]   [inst_3 : Continuou…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
lemma locallyIntegrableOn_congr (h : f =ᵐ[μ.restrict s] g) :
    LocallyIntegrableOn f s μ ↔ LocallyIntegrableOn g s μ :=
  ⟨(·.congr h), (·.congr h.symm)⟩
/-
**MeasureTheory.IntegrableOn.locallyIntegrableOn** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.IntegrableOn`。
形式化陈述：∀ {X : Type u_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : TopologicalSpace ε]   [inst_3 : ContinuousENorm ε] {f :
 X → ε} {μ : MeasureTheory.Measure X} {s : Set X},   MeasureTheory.IntegrableOn 
f s μ → MeasureTheory.LocallyIntegrableOn f s μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
-/
theorem IntegrableOn.locallyIntegrableOn (hf : IntegrableOn f s μ) : LocallyIntegrableOn f s μ :=
  fun _ _ => ⟨s, self_mem_nhdsWithin, hf⟩

/-- If a function is locally integrable on a compact set, then it is integrable on that set. -/
/-
**MeasureTheory.LocallyIntegrableOn.integrableOn_isCompact** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.LocallyIntegrableOn`。
形式化陈述：∀ {X : Type u_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : TopologicalSpace ε]   [inst_3 : ContinuousENorm ε] {f :
 X → ε} {μ : MeasureTheory.Measure X} {s : Set X}   [TopologicalSpace.PseudoMetr
izableSpace ε],   MeasureTheory.LocallyIntegrableOn f s μ → IsCompact s → Measur
eTheory.IntegrableOn f s μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.induction_on`：IsCompact.induction_on (hs : IsCompact s) {p : S
et X -> Prop} (he : p ∅) (hmono : forall ⦃s t⦄, s subseteq t -> p t -> p s) (hun
ion : forall…
· 使用定理 `MeasureTheory.integrableOn_empty`：integrableOn_empty : IntegrableOn f ∅ 
μ
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrableOn_union`：integrableOn_union [PseudoMetrizableSp
ace ε] : IntegrableOn f (s union t) μ ↔ IntegrableOn f s μ ∧ IntegrableOn f t μ

--- 原说明 ---
If a function is locally integrable on a compact set, then it is integrable on t
hat set.
-/
theorem LocallyIntegrableOn.integrableOn_isCompact [PseudoMetrizableSpace ε]
    (hf : LocallyIntegrableOn f s μ) (hs : IsCompact s) : IntegrableOn f s μ :=
  IsCompact.induction_on hs integrableOn_empty (fun _u _v huv hv => hv.mono_set huv)
    (fun _u _v hu hv => integrableOn_union.mpr ⟨hu, hv⟩) hf
/-
**MeasureTheory.LocallyIntegrableOn.integrableOn_compact_subset** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.LocallyIntegrableOn`。
形式化陈述：∀ {X : Type u_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : TopologicalSpace ε]   [inst_3 : ContinuousENorm ε] {f :
 X → ε} {μ : MeasureTheory.Measure X} {s : Set X}   [TopologicalSpace.PseudoMetr
izableSpace ε],   MeasureTheory.LocallyIntegrableOn f s μ → ∀ {t : Set X}, t ⊆ s
 → IsCompact t → MeasureTheory.IntegrableOn f t μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.LocallyIntegrableOn.integrableOn_isCompact`：∀ {X : Type u_
1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst
_2 : TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `MeasureTheory.LocallyIntegrableOn.mono_set`：∀ {X : Type u_1} {ε : Type u
_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 : Topologic
alSpace ε]   [inst_3 : Continuou…
-/
theorem LocallyIntegrableOn.integrableOn_compact_subset [PseudoMetrizableSpace ε]
    (hf : LocallyIntegrableOn f s μ) {t : Set X} (hst : t ⊆ s) (ht : IsCompact t) :
    IntegrableOn f t μ :=
  (hf.mono_set hst).integrableOn_isCompact ht

/-- If a function `f` is locally integrable on a set `s` in a second countable topological space,
then there exist countably many open sets `u` covering `s` such that `f` is integrable on each
set `u ∩ s`. -/
/-
**MeasureTheory.LocallyIntegrableOn.exists_countable_integrableOn** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory.LocallyIntegrableOn`。
形式化陈述：∀ {X : Type u_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : TopologicalSpace ε]   [inst_3 : ContinuousENorm ε] {f :
 X → ε} {μ : MeasureTheory.Measure X} {s : Set X} [SecondCountableTopology X],  
 MeasureTheory.LocallyIntegrableOn f s μ →     ∃ T, T.Countable ∧ (∀ u ∈ T, IsOp
en u) ∧ s ⊆ ⋃ u ∈ T, u ∧ ∀ u ∈ T, MeasureTheory.IntegrableOn f (u ∩ s) μ
参数：∀ u ∈ T, IsOpen u；u ∩ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsWithin`：mem_nhdsWithin {t : Set α} {a : α} {s : Set α} : t in 𝓝[
s] a ↔ exists u, IsOpen u ∧ a in u ∧ u inter s subseteq t
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `Set.mem_iUnion_of_mem`：mem_iUnion_of_mem {s : ι -> Set α} {a : α} (i : ι
) (ha : a in s i) : a in ⋃ i, s i
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `TopologicalSpace.isOpen_iUnion_countable`：isOpen_iUnion_countable [Secon
dCountableTopology α] {ι} (s : ι -> Set α) (H : forall i, IsOpen (s i)) : exists
 T : Set ι, T.Countable ∧ ⋃ i …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Countable.image`：∀ {α : Type u} {β : Type v} {s : Set α}, s.Countabl
e → ∀ (f : α → β), (f '' s).Countable
· 使用定理 `Set.biUnion_image`：biUnion_image : ⋃ x in f '' s, g x = ⋃ y in s, g (f y
)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If a function `f` is locally integrable on a set `s` in a second countable topol
ogical space,
then there exist countably many open sets `u` covering `s` such that `f` is inte
grable on each
set `u ∩ s`.
-/
theorem LocallyIntegrableOn.exists_countable_integrableOn [SecondCountableTopology X]
    (hf : LocallyIntegrableOn f s μ) : ∃ T : Set (Set X), T.Countable ∧
    (∀ u ∈ T, IsOpen u) ∧ (s ⊆ ⋃ u ∈ T, u) ∧ (∀ u ∈ T, IntegrableOn f (u ∩ s) μ) := by
  have : ∀ x : s, ∃ u, IsOpen u ∧ x.1 ∈ u ∧ IntegrableOn f (u ∩ s) μ := by
    rintro ⟨x, hx⟩
    rcases hf x hx with ⟨t, ht, h't⟩
    rcases mem_nhdsWithin.1 ht with ⟨u, u_open, x_mem, u_sub⟩
    exact ⟨u, u_open, x_mem, h't.mono_set u_sub⟩
  choose u u_open xu hu using this
  obtain ⟨T, T_count, hT⟩ : ∃ T : Set s, T.Countable ∧ s ⊆ ⋃ i ∈ T, u i := by
    have : s ⊆ ⋃ x : s, u x := fun y hy => mem_iUnion_of_mem ⟨y, hy⟩ (xu ⟨y, hy⟩)
    obtain ⟨T, hT_count, hT_un⟩ := isOpen_iUnion_countable u u_open
    exact ⟨T, hT_count, by rwa [hT_un]⟩
  refine ⟨u '' T, T_count.image _, ?_, by rwa [biUnion_image], ?_⟩
  · rintro v ⟨w, -, rfl⟩
    exact u_open _
  · rintro v ⟨w, -, rfl⟩
    exact hu _

/-- If a function `f` is locally integrable on a set `s` in a second countable topological space,
then there exists a sequence of open sets `u n` covering `s` such that `f` is integrable on each
set `u n ∩ s`. -/
/-
**MeasureTheory.LocallyIntegrableOn.exists_nat_integrableOn** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.LocallyIntegrableOn`。
形式化陈述：∀ {X : Type u_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : TopologicalSpace ε]   [inst_3 : ContinuousENorm ε] {f :
 X → ε} {μ : MeasureTheory.Measure X} {s : Set X} [SecondCountableTopology X],  
 MeasureTheory.LocallyIntegrableOn f s μ →     ∃ u, (∀ (n : ℕ), IsOpen (u n)) ∧ 
s ⊆ ⋃ n, u n ∧ ∀ (n : ℕ), MeasureTheory.IntegrableOn f (u n ∩ s) μ
参数：∀ (n : ℕ), IsOpen (u n)；n : ℕ；u n ∩ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.LocallyIntegrableOn.exists_countable_integrableOn`：∀ {X : 
Type u_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X
] [inst_2 : TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `Set.Countable.insert`：∀ {α : Type u} {s : Set α} (a : α), s.Countable → 
(insert a s).Countable
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.Countable.exists_eq_range`：∀ {α : Type u} {s : Set α}, s.Countable →
 s.Nonempty → ∃ f, s = Set.range f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_insert_iff`：mem_insert_iff {x a : α} {s : Set α} : x in insert a
 s ↔ x = a ∨ x in s
· 使用定理 `isOpen_empty`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen ∅
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `Set.mem_iUnion_of_mem`：mem_iUnion_of_mem {s : ι -> Set α} {a : α} (i : ι
) (ha : a in s i) : a in ⋃ i, s i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.empty_inter`：empty_inter (a : Set α) : ∅ inter a = ∅

--- 原说明 ---
If a function `f` is locally integrable on a set `s` in a second countable topol
ogical space,
then there exists a sequence of open sets `u n` covering `s` such that `f` is in
tegrable on each
set `u n ∩ s`.
-/
theorem LocallyIntegrableOn.exists_nat_integrableOn [SecondCountableTopology X]
    (hf : LocallyIntegrableOn f s μ) : ∃ u : ℕ → Set X,
    (∀ n, IsOpen (u n)) ∧ (s ⊆ ⋃ n, u n) ∧ (∀ n, IntegrableOn f (u n ∩ s) μ) := by
  rcases hf.exists_countable_integrableOn with ⟨T, T_count, T_open, sT, hT⟩
  let T' : Set (Set X) := insert ∅ T
  have T'_count : T'.Countable := Countable.insert ∅ T_count
  have T'_ne : T'.Nonempty := by simp only [T', insert_nonempty]
  rcases T'_count.exists_eq_range T'_ne with ⟨u, hu⟩
  refine ⟨u, ?_, ?_, ?_⟩
  · intro n
    have : u n ∈ T' := by rw [hu]; exact mem_range_self n
    rcases mem_insert_iff.1 this with h | h
    · rw [h]
      exact isOpen_empty
    · exact T_open _ h
  · intro x hx
    obtain ⟨v, hv, h'v⟩ : ∃ v, v ∈ T ∧ x ∈ v := by simpa only [mem_iUnion, exists_prop] using sT hx
    have : v ∈ range u := by rw [← hu]; exact subset_insert ∅ T hv
    obtain ⟨n, rfl⟩ : ∃ n, u n = v := by simpa only [mem_range] using this
    exact mem_iUnion_of_mem _ h'v
  · intro n
    have : u n ∈ T' := by rw [hu]; exact mem_range_self n
    rcases mem_insert_iff.1 this with h | h
    · simp only [h, empty_inter, integrableOn_empty]
    · exact hT _ h
/-
**MeasureTheory.LocallyIntegrableOn.aestronglyMeasurable** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.LocallyIntegrableOn`。
形式化陈述：∀ {X : Type u_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : TopologicalSpace ε]   [inst_3 : ContinuousENorm ε] {f :
 X → ε} {μ : MeasureTheory.Measure X} {s : Set X}   [TopologicalSpace.PseudoMetr
izableSpace ε] [SecondCountableTopology X],   MeasureTheory.LocallyIntegrableOn 
f s μ → MeasureTheory.AEStronglyMeasurable f (μ.restrict s)
参数：μ.restrict s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.LocallyIntegrableOn.exists_nat_integrableOn`：∀ {X : Type u
_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [ins
t_2 : TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iUnion_inter`：iUnion_inter (s : Set β) (t : ι -> Set β) : (⋃ i, t i)
 inter s = ⋃ i, t i inter s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
· 使用定理 `aestronglyMeasurable_iUnion_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Ty
pe u_4} [Countable ι] [inst : TopologicalSpace β] {m₀ : MeasurableSpace α}   {μ 
: MeasureTheory.Measu…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
-/
theorem LocallyIntegrableOn.aestronglyMeasurable [PseudoMetrizableSpace ε]
    [SecondCountableTopology X] (hf : LocallyIntegrableOn f s μ) :
    AEStronglyMeasurable f (μ.restrict s) := by
  rcases hf.exists_nat_integrableOn with ⟨u, -, su, hu⟩
  have : s = ⋃ n, u n ∩ s := by rw [← iUnion_inter]; exact (inter_eq_right.mpr su).symm
  rw [this, aestronglyMeasurable_iUnion_iff]
  exact fun i : ℕ => (hu i).aestronglyMeasurable

/-- If `s` is locally closed (e.g. open or closed), then `f` is locally integrable on `s` iff it is
integrable on every compact subset contained in `s`. -/
/-
**MeasureTheory.locallyIntegrableOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：locallyIntegrableOn_iff [PseudoMetrizableSpace ε] [LocallyCompactSpace X] 
(hs : IsLocallyClosed s) : LocallyIntegrableOn f s μ ↔ forall (k : Set X), k sub
seteq s -> IsCompact k -> IntegrableOn f k μ
参数：hs : IsLocallyClosed s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.LocallyIntegrableOn.integrableOn_compact_subset`：∀ {X : Ty
pe u_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] 
[inst_2 : TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `exists_compact_subset`：exists_compact_subset [LocallyCompactSpace X] {x 
: X} {U : Set X} (hU : IsOpen U) (hx : x in U) : exists K : Set X, IsCompact K ∧
 x in inter…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_inter_of_mem`：nhdsWithin_inter_of_mem {a : α} {s t : Set α} (
h : s in 𝓝[t] a) : 𝓝[s inter t] a = 𝓝[t] a
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsCompact.inter_left`：IsCompact.inter_left (ht : IsCompact t) (hs : IsCl
osed s) : IsCompact (s inter t)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `s` is locally closed (e.g. open or closed), then `f` is locally integrable o
n `s` iff it is
integrable on every compact subset contained in `s`.
-/
theorem locallyIntegrableOn_iff [PseudoMetrizableSpace ε]
    [LocallyCompactSpace X] (hs : IsLocallyClosed s) :
    LocallyIntegrableOn f s μ ↔ ∀ (k : Set X), k ⊆ s → IsCompact k → IntegrableOn f k μ := by
  refine ⟨fun hf k hk ↦ hf.integrableOn_compact_subset hk, fun hf x hx ↦ ?_⟩
  rcases hs with ⟨U, Z, hU, hZ, rfl⟩
  rcases exists_compact_subset hU hx.1 with ⟨K, hK, hxK, hKU⟩
  rw [nhdsWithin_inter_of_mem (nhdsWithin_le_nhds <| hU.mem_nhds hx.1)]
  refine ⟨Z ∩ K, inter_mem_nhdsWithin _ (mem_interior_iff_mem_nhds.1 hxK), ?_⟩
  exact hf (Z ∩ K) (fun y hy ↦ ⟨hKU hy.2, hy.1⟩) (.inter_left hK hZ)
/-
**MeasureTheory._root_.ContinuousLinearMap.locallyIntegrableOn_comp** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousLinearMap.locallyIntegrableOn_comp {E H 𝕜 𝕜' : Type*}
    [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
    [NormedAddCommGroup E] [NormedSpace 𝕜' E] [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    {σ : 𝕜 →+* 𝕜'} [RingHomIsometric σ] {f : X → H} (L : H →SL[σ] E)
    (hf : LocallyIntegrableOn f s μ) : LocallyIntegrableOn (L ∘ f) s μ :=
  (L.integrableAtFilter_comp <| hf · ·)
/-
**MeasureTheory.LocallyIntegrableOn.add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.LocallyIntegrableOn`。
形式化陈述：∀ {X : Type u_1} {ε'' : Type u_5} [inst : MeasurableSpace X] [inst_1 : Top
ologicalSpace X]   [inst_2 : TopologicalSpace ε''] [inst_3 : ESeminormedAddMonoi
d ε''] {μ : MeasureTheory.Measure X} {s : Set X}   [ContinuousAdd ε''] {f g : X 
→ ε''},   MeasureTheory.LocallyIntegrableOn f s μ →     MeasureTheory.LocallyInt
egrableOn g s μ → MeasureTheory.LocallyIntegrableOn (f + g) s μ
参数：f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableAtFilter.add`：∀ {α : Type u_1} {ε' : Type u_4} {
mα : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε
']   [inst_1 : ESeminormed…
-/
protected theorem LocallyIntegrableOn.add [ContinuousAdd ε''] {f g : X → ε''}
    (hf : LocallyIntegrableOn f s μ) (hg : LocallyIntegrableOn g s μ) :
    LocallyIntegrableOn (f + g) s μ := fun x hx ↦ (hf x hx).add (hg x hx)

-- TODO: once mathlib has an ENormedAddCommSubMonoid, generalise this lemma also
/-
**MeasureTheory.LocallyIntegrableOn.sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.LocallyIntegrableOn`。
形式化陈述：∀ {X : Type u_1} {E : Type u_6} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : NormedAddCommGroup E]   {μ : MeasureTheory.Measure X} {
s : Set X} {f g : X → E},   MeasureTheory.LocallyIntegrableOn f s μ →     Measur
eTheory.LocallyIntegrableOn g s μ → MeasureTheory.LocallyIntegrableOn (f - g) s 
μ
参数：f - g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableAtFilter.sub`：∀ {α : Type u_1} {E : Type u_5} {m
α : MeasurableSpace α} [inst : NormedAddCommGroup E] {μ : MeasureTheory.Measure 
α}   {l : Filter α} {f g :…
-/
protected theorem LocallyIntegrableOn.sub
    {f g : X → E} (hf : LocallyIntegrableOn f s μ) (hg : LocallyIntegrableOn g s μ) :
    LocallyIntegrableOn (f - g) s μ := fun x hx ↦ (hf x hx).sub (hg x hx)
/-
**MeasureTheory.LocallyIntegrableOn.neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.LocallyIntegrableOn`。
形式化陈述：∀ {X : Type u_1} {E : Type u_6} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : NormedAddCommGroup E]   {μ : MeasureTheory.Measure X} {
s : Set X} {f : X → E},   MeasureTheory.LocallyIntegrableOn f s μ → MeasureTheor
y.LocallyIntegrableOn (-f) s μ
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableAtFilter.neg`：∀ {α : Type u_1} {E : Type u_5} {m
α : MeasurableSpace α} [inst : NormedAddCommGroup E] {μ : MeasureTheory.Measure 
α}   {l : Filter α} {f : α…
-/
protected theorem LocallyIntegrableOn.neg {f : X → E} (hf : LocallyIntegrableOn f s μ) :
    LocallyIntegrableOn (-f) s μ := fun x hx ↦ (hf x hx).neg
/-
**MeasureTheory.locallyIntegrableOn_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：∀ {X : Type u_1} {E : Type u_6} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : NormedAddCommGroup E]   {μ : MeasureTheory.Measure X} {
s : Set X} {f : X → E},   MeasureTheory.LocallyIntegrableOn (-f) s μ ↔ MeasureTh
eory.LocallyIntegrableOn f s μ
参数：-f。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem locallyIntegrableOn_neg_iff {f : X → E} :
    LocallyIntegrableOn (-f) s μ ↔ LocallyIntegrableOn f s μ := by
  unfold LocallyIntegrableOn
  simp_rw [MeasureTheory.integrableAtFilter_neg_iff]

-- TODO: generalise this to ENormed spaces, once there are suitable typeclasses
/-
**MeasureTheory.LocallyIntegrableOn.smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.LocallyIntegrableOn`。
形式化陈述：∀ {X : Type u_1} {E : Type u_6} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : NormedAddCommGroup E]   {μ : MeasureTheory.Measure X} {
s : Set X} {𝕜 : Type u_9} [inst_3 : NormedField 𝕜] [inst_4 : NormedSpace 𝕜 E]   
{f : X → E}, MeasureTheory.LocallyIntegrableOn f s μ → ∀ (c : 𝕜), MeasureTheory.
LocallyIntegrableOn (c • f) s μ
参数：c : 𝕜；c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableAtFilter.smul`：∀ {α : Type u_1} {E : Type u_5} {
mα : MeasurableSpace α} [inst : NormedAddCommGroup E] {μ : MeasureTheory.Measure
 α}   {l : Filter α} {𝕜 : T…
-/
protected theorem LocallyIntegrableOn.smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    {f : X → E} (hf : LocallyIntegrableOn f s μ) (c : 𝕜) :
  LocallyIntegrableOn (c • f) s μ := fun x hx ↦ (hf x hx).smul c

-- TODO: generalise this to ENormed spaces, once there are suitable typeclasses
/-
**MeasureTheory.locallyIntegrableOn_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：∀ {X : Type u_1} {E : Type u_6} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : NormedAddCommGroup E]   {μ : MeasureTheory.Measure X} {
s : Set X} {𝕜 : Type u_9} [inst_3 : NormedField 𝕜] [inst_4 : NormedSpace 𝕜 E]   
{f : X → E} (c : 𝕜), MeasureTheory.LocallyIntegrableOn (c • f) s μ ↔ c = 0 ∨ Mea
sureTheory.LocallyIntegrableOn f s μ
参数：c : 𝕜；c • f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem locallyIntegrableOn_smul_iff {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    {f : X → E} (c : 𝕜) :
    LocallyIntegrableOn (c • f) s μ ↔ c = 0 ∨ LocallyIntegrableOn f s μ := by
  unfold LocallyIntegrableOn
  grind [integrableAtFilter_smul_iff]

end LocallyIntegrableOn

/-- A function `f : X → ε` is *locally integrable* if it is integrable on a neighborhood of every
point. In particular, it is integrable on all compact sets,
see `LocallyIntegrable.integrableOn_isCompact`. -/
/-
**MeasureTheory.LocallyIntegrable** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：LocallyIntegrable (f : X -> ε) (μ : Measure X
参数：f : X -> ε。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : X → ε` is *locally integrable* if it is integrable on a neighbor
hood of every
point. In particular, it is integrable on all compact sets,
see `LocallyIntegrable.integrableOn_isCompact`.
-/
def LocallyIntegrable (f : X → ε) (μ : Measure X := by volume_tac) : Prop :=
  ∀ x : X, IntegrableAtFilter f (𝓝 x) μ
/-
**MeasureTheory.locallyIntegrable_comap** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：locallyIntegrable_comap (hs : MeasurableSet s) : LocallyIntegrable (fun x 
: s => f x) (μ.comap Subtype.val) ↔ LocallyIntegrableOn f s μ
参数：hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `MeasurableEmbedding.integrableAtFilter_iff_comap`：∀ {α : Type u_1} {β : 
Type u_2} {ε : Type u_3} {mα : MeasurableSpace α} [inst : TopologicalSpace ε]   
[inst_1 : ContinuousENorm ε] {l : Filt…
· 使用定理 `MeasurableEmbedding.subtype_coe`：subtype_coe (hs : MeasurableSet s) : Me
asurableEmbedding ((↑) : s -> α) where injective
-/
theorem locallyIntegrable_comap (hs : MeasurableSet s) :
    LocallyIntegrable (fun x : s ↦ f x) (μ.comap Subtype.val) ↔ LocallyIntegrableOn f s μ := by
  simp_rw [LocallyIntegrableOn, Subtype.forall', ← map_nhds_subtype_val]
  exact forall_congr' fun _ ↦ (MeasurableEmbedding.subtype_coe hs).integrableAtFilter_iff_comap.symm
/-
**MeasureTheory.locallyIntegrableOn_univ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：locallyIntegrableOn_univ : LocallyIntegrableOn f univ μ ↔ LocallyIntegrabl
e f μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem locallyIntegrableOn_univ : LocallyIntegrableOn f univ μ ↔ LocallyIntegrable f μ := by
  simp only [LocallyIntegrableOn, nhdsWithin_univ, mem_univ, true_imp_iff]; rfl
/-
**MeasureTheory.LocallyIntegrable.locallyIntegrableOn** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.LocallyIntegrable`。
形式化陈述：∀ {X : Type u_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : TopologicalSpace ε]   [inst_3 : ContinuousENorm ε] {f :
 X → ε} {μ : MeasureTheory.Measure X},   MeasureTheory.LocallyIntegrable f μ → ∀
 (s : Set X), MeasureTheory.LocallyIntegrableOn f s μ
参数：s : Set X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableAtFilter.filter_mono`：∀ {α : Type u_1} {ε : Type
 u_3} {mα : MeasurableSpace α} {f : α → ε} {μ : MeasureTheory.Measure α}   [inst
 : TopologicalSpace ε] [inst_1 : C…
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
-/
theorem LocallyIntegrable.locallyIntegrableOn (hf : LocallyIntegrable f μ) (s : Set X) :
    LocallyIntegrableOn f s μ := fun x _ => (hf x).filter_mono nhdsWithin_le_nhds
/-
**MeasureTheory.Integrable.locallyIntegrable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Integrable`。
形式化陈述：∀ {X : Type u_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : TopologicalSpace ε]   [inst_3 : ContinuousENorm ε] {f :
 X → ε} {μ : MeasureTheory.Measure X},   MeasureTheory.Integrable f μ → MeasureT
heory.LocallyIntegrable f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.integrableAtFilter`：∀ {α : Type u_1} {ε : Type 
u_3} {mα : MeasurableSpace α} {f : α → ε} {μ : MeasureTheory.Measure α}   [inst 
: TopologicalSpace ε] [inst_1 : C…
-/
theorem Integrable.locallyIntegrable (hf : Integrable f μ) : LocallyIntegrable f μ := fun _ =>
  hf.integrableAtFilter _
/-
**MeasureTheory.LocallyIntegrable.mono_enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.LocallyIntegrable`。
形式化陈述：∀ {X : Type u_1} {ε : Type u_3} {ε' : Type u_4} [inst : MeasurableSpace X]
 [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpace ε] [inst_3 : Continu
ousENorm ε] [inst_4 : TopologicalSpace ε']   [inst_5 : ContinuousENorm ε'] {f : 
X → ε} {μ : MeasureTheory.Measure X},   MeasureTheory.LocallyIntegrable f μ →   
  ∀ {g : X → ε'},       MeasureTheory.AEStronglyMeasurable g μ → (∀ᵐ (x : X) ∂μ,
 ‖g x‖ₑ ≤ ‖f x‖ₑ) → MeasureTheory.LocallyIntegrable g μ
参数：∀ᵐ (x : X) ∂μ, ‖g x‖ₑ ≤ ‖f x‖ₑ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.locallyIntegrableOn_univ`：locallyIntegrableOn_univ : Local
lyIntegrableOn f univ μ ↔ LocallyIntegrable f μ
· 使用定理 `MeasureTheory.LocallyIntegrableOn.mono_enorm`：∀ {X : Type u_1} {ε : Type
 u_3} {ε' : Type u_4} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X]  
 [inst_2 : TopologicalSpace ε] [in…
-/
theorem LocallyIntegrable.mono_enorm (hf : LocallyIntegrable f μ) {g : X → ε'}
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ x ∂μ, ‖g x‖ₑ ≤ ‖f x‖ₑ) :
    LocallyIntegrable g μ := by
  rw [← locallyIntegrableOn_univ] at hf ⊢
  exact hf.mono_enorm hg h
/-
**MeasureTheory.LocallyIntegrable.mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
LocallyIntegrable`。
形式化陈述：∀ {X : Type u_1} {E : Type u_6} {F : Type u_7} [inst : MeasurableSpace X] 
[inst_1 : TopologicalSpace X]   [inst_2 : NormedAddCommGroup E] [inst_3 : Normed
AddCommGroup F] {μ : MeasureTheory.Measure X} {f : X → E},   MeasureTheory.Local
lyIntegrable f μ →     ∀ {g : X → F},       MeasureTheory.AEStronglyMeasurable g
 μ → (∀ᵐ (x : X) ∂μ, ‖g x‖ ≤ ‖f x‖) → MeasureTheory.LocallyIntegrable g μ
参数：∀ᵐ (x : X) ∂μ, ‖g x‖ ≤ ‖f x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.locallyIntegrableOn_univ`：locallyIntegrableOn_univ : Local
lyIntegrableOn f univ μ ↔ LocallyIntegrable f μ
· 使用定理 `MeasureTheory.LocallyIntegrableOn.mono`：∀ {X : Type u_1} {E : Type u_6} 
{F : Type u_7} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X]   [inst_
2 : NormedAddCommGroup E] [i…
-/
theorem LocallyIntegrable.mono {f : X → E} (hf : LocallyIntegrable f μ) {g : X → F}
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖f x‖) :
    LocallyIntegrable g μ := by
  rw [← locallyIntegrableOn_univ] at hf ⊢
  exact hf.mono hg h

@[gcongr]
/-
**MeasureTheory.LocallyIntegrable.mono_measure** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.LocallyIntegrable`。
形式化陈述：∀ {X : Type u_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : TopologicalSpace ε]   [inst_3 : ContinuousENorm ε] {f :
 X → ε} {μ ν : MeasureTheory.Measure X},   MeasureTheory.LocallyIntegrable f μ →
 ν ≤ μ → MeasureTheory.LocallyIntegrable f ν
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableAtFilter.mono_measure`：∀ {α : Type u_1} {ε : Typ
e u_3} {mα : MeasurableSpace α} {f : α → ε} {μ ν : MeasureTheory.Measure α}   [i
nst : TopologicalSpace ε] [inst_1 :…
-/
lemma LocallyIntegrable.mono_measure (hf : LocallyIntegrable f μ) (h : ν ≤ μ) :
    LocallyIntegrable f ν :=
  (hf · |>.mono_measure h)

@[gcongr]
/-
**MeasureTheory.LocallyIntegrable.congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.LocallyIntegrable`。
形式化陈述：∀ {X : Type u_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : TopologicalSpace ε]   [inst_3 : ContinuousENorm ε] {f g
 : X → ε} {μ : MeasureTheory.Measure X},   MeasureTheory.LocallyIntegrable f μ →
 f =ᵐ[μ] g → MeasureTheory.LocallyIntegrable g μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.IntegrableAtFilter.congr`：∀ {α : Type u_1} {ε : Type u_3} 
{mα : MeasurableSpace α} {f g : α → ε} {μ : MeasureTheory.Measure α}   [inst : T
opologicalSpace ε] [inst_1 :…
-/
lemma LocallyIntegrable.congr (hf : LocallyIntegrable f μ) (h : f =ᵐ[μ] g) :
    LocallyIntegrable g μ :=
  (hf · |>.congr h)
/-
**MeasureTheory.locallyIntegrable_congr** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
`。
形式化陈述：locallyIntegrable_congr (h : f =ᵐ[μ] g) : LocallyIntegrable f μ ↔ LocallyI
ntegrable g μ
参数：h : f =ᵐ[μ] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.LocallyIntegrable.congr`：∀ {X : Type u_1} {ε : Type u_3} [
inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 : TopologicalSpa
ce ε]   [inst_3 : Continuou…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
lemma locallyIntegrable_congr (h : f =ᵐ[μ] g) :
    LocallyIntegrable f μ ↔ LocallyIntegrable g μ :=
  ⟨(·.congr h), (·.congr h.symm)⟩

/-- If `f` is locally integrable with respect to `μ.restrict s`, it is locally integrable on `s`.
(See `locallyIntegrableOn_iff_locallyIntegrable_restrict` for an iff statement when `s` is
closed.) -/
/-
**MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：locallyIntegrableOn_of_locallyIntegrable_restrict [OpensMeasurableSpace X]
 (hf : LocallyIntegrable f (μ.restrict s)) : LocallyIntegrableOn f s μ
参数：hf : LocallyIntegrable f (μ.restrict s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.restrict_restrict`：restrict_restrict (hs : Measura
bleSet s) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …

--- 原说明 ---
If `f` is locally integrable with respect to `μ.restrict s`, it is locally integ
rable on `s`.
(See `locallyIntegrableOn_iff_locallyIntegrable_restrict` for an iff statement w
hen `s` is
closed.)
-/
theorem locallyIntegrableOn_of_locallyIntegrable_restrict [OpensMeasurableSpace X]
    (hf : LocallyIntegrable f (μ.restrict s)) : LocallyIntegrableOn f s μ := by
  intro x _
  obtain ⟨t, ht_mem, ht_int⟩ := hf x
  obtain ⟨u, hu_sub, hu_o, hu_mem⟩ := mem_nhds_iff.mp ht_mem
  refine ⟨_, inter_mem_nhdsWithin s (hu_o.mem_nhds hu_mem), ?_⟩
  simpa only [IntegrableOn, Measure.restrict_restrict hu_o.measurableSet, inter_comm] using
    ht_int.mono_set hu_sub

/-- If `s` is closed, being locally integrable on `s` w.r.t. `μ` is equivalent to being locally
integrable with respect to `μ.restrict s`. For the one-way implication without assuming `s` closed,
see `locallyIntegrableOn_of_locallyIntegrable_restrict`. -/
/-
**MeasureTheory.locallyIntegrableOn_iff_locallyIntegrable_restrict** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：locallyIntegrableOn_iff_locallyIntegrable_restrict [OpensMeasurableSpace X
] (hs : IsClosed s) : LocallyIntegrableOn f s μ ↔ LocallyIntegrable f (μ.restric
t s)
参数：hs : IsClosed s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsWithin`：mem_nhdsWithin {t : Set α} {a : α} {s : Set α} : t in 𝓝[
s] a ↔ exists u, IsOpen u ∧ a in u ∧ u inter s subseteq t
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `MeasureTheory.Measure.restrict_restrict`：restrict_restrict (hs : Measura
bleSet s) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.inter_compl_self`：inter_compl_self (s : Set α) : s inter sᶜ = ∅
· 使用定理 `MeasureTheory.integrableOn_empty`：integrableOn_empty : IntegrableOn f ∅ 
μ
· 使用定理 `MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict`：locally
IntegrableOn_of_locallyIntegrable_restrict [OpensMeasurableSpace X] (hf : Locall
yIntegrable f (μ.restrict s)) : LocallyIntegrableOn f…

--- 原说明 ---
If `s` is closed, being locally integrable on `s` w.r.t. `μ` is equivalent to be
ing locally
integrable with respect to `μ.restrict s`. For the one-way implication without a
ssuming `s` closed,
see `locallyIntegrableOn_of_locallyIntegrable_restrict`.
-/
theorem locallyIntegrableOn_iff_locallyIntegrable_restrict [OpensMeasurableSpace X]
    (hs : IsClosed s) : LocallyIntegrableOn f s μ ↔ LocallyIntegrable f (μ.restrict s) := by
  refine ⟨fun hf x => ?_, locallyIntegrableOn_of_locallyIntegrable_restrict⟩
  by_cases h : x ∈ s
  · obtain ⟨t, ht_nhds, ht_int⟩ := hf x h
    obtain ⟨u, hu_o, hu_x, hu_sub⟩ := mem_nhdsWithin.mp ht_nhds
    refine ⟨u, hu_o.mem_nhds hu_x, ?_⟩
    rw [IntegrableOn, restrict_restrict hu_o.measurableSet]
    exact ht_int.mono_set hu_sub
  · rw [← isOpen_compl_iff] at hs
    refine ⟨sᶜ, hs.mem_nhds h, ?_⟩
    rw [IntegrableOn, restrict_restrict, inter_comm, inter_compl_self, ← IntegrableOn]
    exacts [integrableOn_empty, hs.measurableSet]

/-- If a function is locally integrable, then it is integrable on any compact set. -/
/-
**MeasureTheory.LocallyIntegrable.integrableOn_isCompact** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.LocallyIntegrable`。
形式化陈述：∀ {X : Type u_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : TopologicalSpace ε]   [inst_3 : ContinuousENorm ε] {f :
 X → ε} {μ : MeasureTheory.Measure X} [TopologicalSpace.PseudoMetrizableSpace ε]
   {k : Set X}, MeasureTheory.LocallyIntegrable f μ → IsCompact k → MeasureTheor
y.IntegrableOn f k μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.LocallyIntegrableOn.integrableOn_isCompact`：∀ {X : Type u_
1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst
_2 : TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `MeasureTheory.LocallyIntegrable.locallyIntegrableOn`：∀ {X : Type u_1} {ε
 : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 : 
TopologicalSpace ε]   [inst_3 : Continuou…

--- 原说明 ---
If a function is locally integrable, then it is integrable on any compact set.
-/
theorem LocallyIntegrable.integrableOn_isCompact [PseudoMetrizableSpace ε]
    {k : Set X} (hf : LocallyIntegrable f μ) (hk : IsCompact k) : IntegrableOn f k μ :=
  (hf.locallyIntegrableOn k).integrableOn_isCompact hk

/-- If a function is locally integrable, then it is integrable on an open neighborhood of any
compact set. -/
/-
**MeasureTheory.LocallyIntegrable.integrableOn_nhds_isCompact** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.LocallyIntegrable`。
形式化陈述：∀ {X : Type u_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : TopologicalSpace ε]   [inst_3 : ContinuousENorm ε] {f :
 X → ε} {μ : MeasureTheory.Measure X} [TopologicalSpace.PseudoMetrizableSpace ε]
,   MeasureTheory.LocallyIntegrable f μ →     ∀ {k : Set X}, IsCompact k → ∃ u, 
IsOpen u ∧ k ⊆ u ∧ MeasureTheory.IntegrableOn f u μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.induction_on`：IsCompact.induction_on (hs : IsCompact s) {p : S
et X -> Prop} (he : p ∅) (hmono : forall ⦃s t⦄, s subseteq t -> p t -> p s) (hun
ion : forall…
· 使用定理 `isOpen_empty`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen ∅
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `MeasureTheory.integrableOn_empty`：integrableOn_empty : IntegrableOn f ∅ 
μ
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsOpen.union`：IsOpen.union (h₁ : IsOpen s₁) (h₂ : IsOpen s₂) : IsOpen (s
₁ union s₂)
· 使用定理 `Set.union_subset_union`：union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq s₂) (h₂ : t₁ subseteq t₂) : s₁ union t₁ subseteq s₂ union t₂
· 使用定理 `MeasureTheory.IntegrableOn.union`：∀ {α : Type u_1} {ε : Type u_3} {mα : 
MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   [in
st : TopologicalSpace …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …

--- 原说明 ---
If a function is locally integrable, then it is integrable on an open neighborho
od of any
compact set.
-/
theorem LocallyIntegrable.integrableOn_nhds_isCompact [PseudoMetrizableSpace ε]
    (hf : LocallyIntegrable f μ) {k : Set X} (hk : IsCompact k) :
    ∃ u, IsOpen u ∧ k ⊆ u ∧ IntegrableOn f u μ := by
  refine IsCompact.induction_on hk ?_ ?_ ?_ ?_
  · refine ⟨∅, isOpen_empty, Subset.rfl, integrableOn_empty⟩
  · rintro s t hst ⟨u, u_open, tu, hu⟩
    exact ⟨u, u_open, hst.trans tu, hu⟩
  · rintro s t ⟨u, u_open, su, hu⟩ ⟨v, v_open, tv, hv⟩
    exact ⟨u ∪ v, u_open.union v_open, union_subset_union su tv, hu.union hv⟩
  · intro x _
    rcases hf x with ⟨u, ux, hu⟩
    rcases mem_nhds_iff.1 ux with ⟨v, vu, v_open, xv⟩
    exact ⟨v, nhdsWithin_le_nhds (v_open.mem_nhds xv), v, v_open, Subset.rfl, hu.mono_set vu⟩
/-
**MeasureTheory.locallyIntegrable_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：locallyIntegrable_iff [PseudoMetrizableSpace ε] [LocallyCompactSpace X] : 
LocallyIntegrable f μ ↔ forall k : Set X, IsCompact k -> IntegrableOn f k μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.LocallyIntegrable.integrableOn_isCompact`：∀ {X : Type u_1}
 {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2
 : TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `WeaklyLocallyCompactSpace.exists_compact_mem_nhds`：∀ {X : Type u_3} {ins
t : TopologicalSpace X} [self : WeaklyLocallyCompactSpace X] (x : X), ∃ s, IsCom
pact s ∧ s ∈ nhds x
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
-/
theorem locallyIntegrable_iff [PseudoMetrizableSpace ε] [LocallyCompactSpace X] :
    LocallyIntegrable f μ ↔ ∀ k : Set X, IsCompact k → IntegrableOn f k μ :=
  ⟨fun hf _k hk => hf.integrableOn_isCompact hk, fun hf x =>
    let ⟨K, hK, h2K⟩ := exists_compact_mem_nhds x
    ⟨K, h2K, hf K hK⟩⟩
/-
**MeasureTheory.LocallyIntegrable.aestronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.LocallyIntegrable`。
形式化陈述：∀ {X : Type u_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : TopologicalSpace ε]   [inst_3 : ContinuousENorm ε] {f :
 X → ε} {μ : MeasureTheory.Measure X} [TopologicalSpace.PseudoMetrizableSpace ε]
   [SecondCountableTopology X], MeasureTheory.LocallyIntegrable f μ → MeasureThe
ory.AEStronglyMeasurable f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `MeasureTheory.LocallyIntegrableOn.aestronglyMeasurable`：∀ {X : Type u_1}
 {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2
 : TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.locallyIntegrableOn_univ`：locallyIntegrableOn_univ : Local
lyIntegrableOn f univ μ ↔ LocallyIntegrable f μ
-/
theorem LocallyIntegrable.aestronglyMeasurable [PseudoMetrizableSpace ε] [SecondCountableTopology X]
    (hf : LocallyIntegrable f μ) : AEStronglyMeasurable f μ := by
  simpa only [restrict_univ] using (locallyIntegrableOn_univ.mpr hf).aestronglyMeasurable

/-- If a function is locally integrable in a second countable topological space,
then there exists a sequence of open sets covering the space on which it is integrable. -/
/-
**MeasureTheory.LocallyIntegrable.exists_nat_integrableOn** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.LocallyIntegrable`。
形式化陈述：∀ {X : Type u_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : TopologicalSpace ε]   [inst_3 : ContinuousENorm ε] {f :
 X → ε} {μ : MeasureTheory.Measure X} [SecondCountableTopology X],   MeasureTheo
ry.LocallyIntegrable f μ →     ∃ u, (∀ (n : ℕ), IsOpen (u n)) ∧ ⋃ n, u n = Set.u
niv ∧ ∀ (n : ℕ), MeasureTheory.IntegrableOn f (u n) μ
参数：∀ (n : ℕ), IsOpen (u n)；n : ℕ；u n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.LocallyIntegrableOn.exists_nat_integrableOn`：∀ {X : Type u
_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [ins
t_2 : TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `MeasureTheory.LocallyIntegrable.locallyIntegrableOn`：∀ {X : Type u_1} {ε
 : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 : 
TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `Set.eq_univ_of_univ_subset`：∀ {α : Type u} {s : Set α}, Set.univ ⊆ s → s
 = Set.univ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a

--- 原说明 ---
If a function is locally integrable in a second countable topological space,
then there exists a sequence of open sets covering the space on which it is inte
grable.
-/
theorem LocallyIntegrable.exists_nat_integrableOn [SecondCountableTopology X]
    (hf : LocallyIntegrable f μ) : ∃ u : ℕ → Set X,
    (∀ n, IsOpen (u n)) ∧ ((⋃ n, u n) = univ) ∧ (∀ n, IntegrableOn f (u n) μ) := by
  rcases (hf.locallyIntegrableOn univ).exists_nat_integrableOn with ⟨u, u_open, u_union, hu⟩
  refine ⟨u, u_open, eq_univ_of_univ_subset u_union, fun n ↦ ?_⟩
  simpa only [inter_univ] using hu n
/-
**MeasureTheory.MemLp.locallyIntegrable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.MemLp`。
形式化陈述：∀ {X : Type u_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : TopologicalSpace ε]   [inst_3 : ContinuousENorm ε] {f :
 X → ε} {μ : MeasureTheory.Measure X} [MeasureTheory.IsLocallyFiniteMeasure μ]  
 {p : ENNReal}, MeasureTheory.MemLp f p μ → 1 ≤ p → MeasureTheory.LocallyIntegra
ble f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.finiteAt_nhds`：∀ {α : Type u_1} {m0 : MeasurableSp
ace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure α)   [MeasureTheor
y.IsLocallyFiniteMeasure …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.MemLp.mono_exponent`：∀ {α : Type u_1} {ε : Type u_2} {m : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → ε}   [inst : Topologic
alSpace ε] [inst_1 : Co…
· 使用定理 `MeasureTheory.Restrict.isFiniteMeasure`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {s : Set α} (μ : MeasureTheory.Measure α) [hs : Fact (μ s < ⊤)],   Mea
sureTheory.IsFiniteMeasure (…
· 使用定理 `MeasureTheory.MemLp.restrict`：∀ {α : Type u_1} {m0 : MeasurableSpace α} 
{p : ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : Topological
Space ε] [inst_1 :…
-/
theorem MemLp.locallyIntegrable [IsLocallyFiniteMeasure μ] {p : ℝ≥0∞}
    (hf : MemLp f p μ) (hp : 1 ≤ p) : LocallyIntegrable f μ := by
  intro x
  rcases μ.finiteAt_nhds x with ⟨U, hU, h'U⟩
  have : Fact (μ U < ⊤) := ⟨h'U⟩
  refine ⟨U, hU, ?_⟩
  rw [IntegrableOn, ← memLp_one_iff_integrable]
  apply (hf.restrict U).mono_exponent hp
/-
**MeasureTheory.locallyIntegrable_const_enorm** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：locallyIntegrable_const_enorm [IsLocallyFiniteMeasure μ] {c : ε} (hc : ‖c‖
ₑ != ∞) : LocallyIntegrable (fun _ => c) μ
参数：hc : ‖c‖ₑ != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.locallyIntegrable`：∀ {X : Type u_1} {ε : Type u_3} [
inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 : TopologicalSpa
ce ε]   [inst_3 : Continuou…
· 使用定理 `MeasureTheory.memLp_top_const_enorm`：memLp_top_const_enorm {c : ε'} (hc 
: ‖c‖ₑ != ⊤) : MemLp (fun _ : α => c) ∞ μ
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem locallyIntegrable_const_enorm [IsLocallyFiniteMeasure μ] {c : ε} (hc : ‖c‖ₑ ≠ ∞) :
    LocallyIntegrable (fun _ => c) μ :=
  (memLp_top_const_enorm hc).locallyIntegrable le_top
/-
**MeasureTheory.locallyIntegrable_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：locallyIntegrable_const [IsLocallyFiniteMeasure μ] (c : E) : LocallyIntegr
able (fun _ => c) μ
参数：c : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.locallyIntegrable_const_enorm`：locallyIntegrable_const_eno
rm [IsLocallyFiniteMeasure μ] {c : ε} (hc : ‖c‖ₑ != ∞) : LocallyIntegrable (fun 
_ => c) μ
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
-/
theorem locallyIntegrable_const [IsLocallyFiniteMeasure μ] (c : E) :
    LocallyIntegrable (fun _ => c) μ :=
  locallyIntegrable_const_enorm enorm_ne_top
/-
**MeasureTheory.locallyIntegrableOn_const_enorm** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：locallyIntegrableOn_const_enorm [IsLocallyFiniteMeasure μ] {c : ε} (hc : ‖
c‖ₑ != ∞) : LocallyIntegrableOn (fun _ => c) s μ
参数：hc : ‖c‖ₑ != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.LocallyIntegrable.locallyIntegrableOn`：∀ {X : Type u_1} {ε
 : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 : 
TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `MeasureTheory.locallyIntegrable_const_enorm`：locallyIntegrable_const_eno
rm [IsLocallyFiniteMeasure μ] {c : ε} (hc : ‖c‖ₑ != ∞) : LocallyIntegrable (fun 
_ => c) μ
-/
theorem locallyIntegrableOn_const_enorm [IsLocallyFiniteMeasure μ] {c : ε} (hc : ‖c‖ₑ ≠ ∞) :
    LocallyIntegrableOn (fun _ => c) s μ :=
  (locallyIntegrable_const_enorm hc).locallyIntegrableOn s
/-
**MeasureTheory.locallyIntegrableOn_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：locallyIntegrableOn_const [IsLocallyFiniteMeasure μ] (c : E) : LocallyInte
grableOn (fun _ => c) s μ
参数：c : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.locallyIntegrableOn_const_enorm`：locallyIntegrableOn_const
_enorm [IsLocallyFiniteMeasure μ] {c : ε} (hc : ‖c‖ₑ != ∞) : LocallyIntegrableOn
 (fun _ => c) s μ
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
-/
theorem locallyIntegrableOn_const [IsLocallyFiniteMeasure μ] (c : E) :
    LocallyIntegrableOn (fun _ => c) s μ :=
  locallyIntegrableOn_const_enorm enorm_ne_top
/-
**MeasureTheory.locallyIntegrable_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：locallyIntegrable_zero : LocallyIntegrable (fun _ => (0 : ε'')) μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.locallyIntegrable`：∀ {X : Type u_1} {ε : Type u
_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 : Topologic
alSpace ε]   [inst_3 : Continuou…
· 使用定理 `MeasureTheory.integrable_zero`：integrable_zero (μ : Measure α) : Integra
ble (0 : α -> ε') μ
-/
theorem locallyIntegrable_zero : LocallyIntegrable (fun _ ↦ (0 : ε'')) μ :=
  (integrable_zero X ε'' μ).locallyIntegrable
/-
**MeasureTheory.locallyIntegrableOn_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：locallyIntegrableOn_zero : LocallyIntegrableOn (fun _ => (0 : ε'')) s μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.LocallyIntegrable.locallyIntegrableOn`：∀ {X : Type u_1} {ε
 : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 : 
TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `MeasureTheory.locallyIntegrable_zero`：locallyIntegrable_zero : LocallyIn
tegrable (fun _ => (0 : ε'')) μ
-/
theorem locallyIntegrableOn_zero : LocallyIntegrableOn (fun _ ↦ (0 : ε'')) s μ :=
  locallyIntegrable_zero.locallyIntegrableOn s
/-
**MeasureTheory.LocallyIntegrable.indicator** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.LocallyIntegrable`。
形式化陈述：∀ {X : Type u_1} {ε'' : Type u_5} [inst : MeasurableSpace X] [inst_1 : Top
ologicalSpace X]   [inst_2 : TopologicalSpace ε''] [inst_3 : ESeminormedAddMonoi
d ε''] {μ : MeasureTheory.Measure X} {f : X → ε''},   MeasureTheory.LocallyInteg
rable f μ →     ∀ {s : Set X}, MeasurableSet s → MeasureTheory.LocallyIntegrable
 (s.indicator f) μ
参数：s.indicator f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableOn.indicator`：∀ {α : Type u_1} {ε' : Type u_4} {
mα : MeasurableSpace α} {s t : Set α} {μ : MeasureTheory.Measure α}   [inst : To
pologicalSpace ε'] [inst_1…
-/
theorem LocallyIntegrable.indicator {f : X → ε''} (hf : LocallyIntegrable f μ) {s : Set X}
    (hs : MeasurableSet s) : LocallyIntegrable (s.indicator f) μ := by
  intro x
  rcases hf x with ⟨U, hU, h'U⟩
  exact ⟨U, hU, h'U.indicator hs⟩
/-
**MeasureTheory.locallyIntegrable_map_homeomorph** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：locallyIntegrable_map_homeomorph [BorelSpace X] [BorelSpace Y] (e : X ≃ₜ Y
) {f : Y -> ε''} {μ : Measure X} : LocallyIntegrable f (Measure.map e μ) ↔ Local
lyIntegrable (f ∘ e) μ
参数：e : X ≃ₜ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.integrableOn_map_equiv`：integrableOn_map_equiv [Measurable
Space β] (e : α ≃ᵐ β) {f : β -> ε} {μ : Measure α} {s : Set β} : IntegrableOn f 
s (μ.map e) ↔ IntegrableOn…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.symm_apply_apply`：symm_apply_apply (h : X ≃ₜ Y) (x : X) : h.s
ymm (h x) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem locallyIntegrable_map_homeomorph [BorelSpace X] [BorelSpace Y] (e : X ≃ₜ Y) {f : Y → ε''}
    {μ : Measure X} : LocallyIntegrable f (Measure.map e μ) ↔ LocallyIntegrable (f ∘ e) μ := by
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · rcases h (e x) with ⟨U, hU, h'U⟩
    refine ⟨e ⁻¹' U, e.continuous.continuousAt.preimage_mem_nhds hU, ?_⟩
    exact (integrableOn_map_equiv e.toMeasurableEquiv).1 h'U
  · rcases h (e.symm x) with ⟨U, hU, h'U⟩
    refine ⟨e.symm ⁻¹' U, e.symm.continuous.continuousAt.preimage_mem_nhds hU, ?_⟩
    apply (integrableOn_map_equiv e.toMeasurableEquiv).2
    simp only [Homeomorph.toMeasurableEquiv_coe]
    convert! h'U
    ext x
    simp only [mem_preimage, Homeomorph.symm_apply_apply]
/-
**MeasureTheory.LocallyIntegrable.add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L
ocallyIntegrable`。
形式化陈述：∀ {X : Type u_1} {ε'' : Type u_5} [inst : MeasurableSpace X] [inst_1 : Top
ologicalSpace X]   [inst_2 : TopologicalSpace ε''] [inst_3 : ESeminormedAddMonoi
d ε''] {μ : MeasureTheory.Measure X} [ContinuousAdd ε'']   {f g : X → ε''},   Me
asureTheory.LocallyIntegrable f μ → MeasureTheory.LocallyIntegrable g μ → Measur
eTheory.LocallyIntegrable (f + g) μ
参数：f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableAtFilter.add`：∀ {α : Type u_1} {ε' : Type u_4} {
mα : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε
']   [inst_1 : ESeminormed…
-/
protected theorem LocallyIntegrable.add [ContinuousAdd ε''] {f g : X → ε''}
    (hf : LocallyIntegrable f μ) (hg : LocallyIntegrable g μ) : LocallyIntegrable (f + g) μ :=
  fun x ↦ (hf x).add (hg x)
/-
**MeasureTheory.LocallyIntegrable.sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L
ocallyIntegrable`。
形式化陈述：∀ {X : Type u_1} {E : Type u_6} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : NormedAddCommGroup E]   {μ : MeasureTheory.Measure X} {
f g : X → E},   MeasureTheory.LocallyIntegrable f μ → MeasureTheory.LocallyInteg
rable g μ → MeasureTheory.LocallyIntegrable (f - g) μ
参数：f - g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableAtFilter.sub`：∀ {α : Type u_1} {E : Type u_5} {m
α : MeasurableSpace α} [inst : NormedAddCommGroup E] {μ : MeasureTheory.Measure 
α}   {l : Filter α} {f g :…
-/
protected theorem LocallyIntegrable.sub {f g : X → E}
    (hf : LocallyIntegrable f μ) (hg : LocallyIntegrable g μ) : LocallyIntegrable (f - g) μ :=
  fun x ↦ (hf x).sub (hg x)
/-
**MeasureTheory.LocallyIntegrable.neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L
ocallyIntegrable`。
形式化陈述：∀ {X : Type u_1} {E : Type u_6} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : NormedAddCommGroup E]   {μ : MeasureTheory.Measure X} {
f : X → E},   MeasureTheory.LocallyIntegrable f μ → MeasureTheory.LocallyIntegra
ble (-f) μ
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableAtFilter.neg`：∀ {α : Type u_1} {E : Type u_5} {m
α : MeasurableSpace α} [inst : NormedAddCommGroup E] {μ : MeasureTheory.Measure 
α}   {l : Filter α} {f : α…
-/
protected theorem LocallyIntegrable.neg {f : X → E} (hf : LocallyIntegrable f μ) :
    LocallyIntegrable (-f) μ := fun x ↦ (hf x).neg
/-
**MeasureTheory.locallyIntegrable_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：∀ {X : Type u_1} {E : Type u_6} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : NormedAddCommGroup E]   {μ : MeasureTheory.Measure X} {
f : X → E},   MeasureTheory.LocallyIntegrable (-f) μ ↔ MeasureTheory.LocallyInte
grable f μ
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem locallyIntegrable_neg_iff {f : X → E} :
    LocallyIntegrable (-f) μ ↔ LocallyIntegrable f μ := by
  simp [← locallyIntegrableOn_univ]
/-
**MeasureTheory.LocallyIntegrable.smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
LocallyIntegrable`。
形式化陈述：∀ {X : Type u_1} {E : Type u_6} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : NormedAddCommGroup E]   {μ : MeasureTheory.Measure X} {
f : X → E} {𝕜 : Type u_9} [inst_3 : NormedAddCommGroup 𝕜] [inst_4 : SMulZeroClas
s 𝕜 E]   [IsBoundedSMul 𝕜 E], MeasureTheory.LocallyIntegrable f μ → ∀ (c : 𝕜), M
easureTheory.LocallyIntegrable (c • f) μ
参数：c : 𝕜；c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableAtFilter.smul`：∀ {α : Type u_1} {E : Type u_5} {
mα : MeasurableSpace α} [inst : NormedAddCommGroup E] {μ : MeasureTheory.Measure
 α}   {l : Filter α} {𝕜 : T…
-/
protected theorem LocallyIntegrable.smul {f : X → E} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    [SMulZeroClass 𝕜 E] [IsBoundedSMul 𝕜 E] (hf : LocallyIntegrable f μ) (c : 𝕜) :
    LocallyIntegrable (c • f) μ := fun x ↦ (hf x).smul c

-- TODO: generalise this to ENormed spaces, once there are suitable typeclasses
/-
**MeasureTheory.locallyIntegrable_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：∀ {X : Type u_1} {E : Type u_6} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : NormedAddCommGroup E]   {μ : MeasureTheory.Measure X} {
𝕜 : Type u_9} [inst_3 : NormedField 𝕜] [inst_4 : NormedSpace 𝕜 E] {f : X → E} (c
 : 𝕜),   MeasureTheory.LocallyIntegrable (c • f) μ ↔ c = 0 ∨ MeasureTheory.Local
lyIntegrable f μ
参数：c : 𝕜；c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem locallyIntegrable_smul_iff {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    {f : X → E} (c : 𝕜) :
    LocallyIntegrable (c • f) μ ↔ c = 0 ∨ LocallyIntegrable f μ := by
  simp [← locallyIntegrableOn_univ]

variable {ε''' : Type*} [TopologicalSpace ε'''] [ESeminormedAddCommMonoid ε''']
  [ContinuousAdd ε'''] in
/-
**MeasureTheory.locallyIntegrable_finsetSum'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：locallyIntegrable_finsetSum' {ι} (s : Finset ι) {f : ι -> X -> ε'''} (hf :
 forall i in s, LocallyIntegrable (f i) μ) : LocallyIntegrable (∑ i in s, f i) μ
参数：s : Finset ι；hf : forall i in s, LocallyIntegrable (f i) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_induction`：∀ {ι : Type u_1} {s : Finset ι} {M : Type u_7} [in
st : AddCommMonoid M] (f : ι → M) (p : M → Prop),   (∀ (a b : M), p a → p b → p 
(a + b)) →…
· 使用定理 `MeasureTheory.LocallyIntegrable.add`：∀ {X : Type u_1} {ε'' : Type u_5} [
inst : MeasurableSpace X] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalS
pace ε''] [inst_3 : ESemi…
· 使用定理 `MeasureTheory.locallyIntegrable_zero`：locallyIntegrable_zero : LocallyIn
tegrable (fun _ => (0 : ε'')) μ
-/
theorem locallyIntegrable_finsetSum' {ι} (s : Finset ι) {f : ι → X → ε'''}
    (hf : ∀ i ∈ s, LocallyIntegrable (f i) μ) : LocallyIntegrable (∑ i ∈ s, f i) μ :=
  Finset.sum_induction f (fun g => LocallyIntegrable g μ) (fun _ _ => LocallyIntegrable.add)
    locallyIntegrable_zero hf

@[deprecated (since := "2026-04-08")]
alias locallyIntegrable_finset_sum' := locallyIntegrable_finsetSum'

variable {ε''' : Type*} [TopologicalSpace ε'''] [ESeminormedAddCommMonoid ε''']
  [ContinuousAdd ε'''] in
/-
**MeasureTheory.locallyIntegrable_finsetSum** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：locallyIntegrable_finsetSum {ι} (s : Finset ι) {f : ι -> X -> ε'''} (hf : 
forall i in s, LocallyIntegrable (f i) μ) : LocallyIntegrable (fun a => ∑ i in s
, f i a) μ
参数：s : Finset ι；hf : forall i in s, LocallyIntegrable (f i) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.locallyIntegrable_finsetSum'`：locallyIntegrable_finsetSum'
 {ι} (s : Finset ι) {f : ι -> X -> ε'''} (hf : forall i in s, LocallyIntegrable 
(f i) μ) : LocallyIntegrable (∑ …
-/
theorem locallyIntegrable_finsetSum {ι} (s : Finset ι) {f : ι → X → ε'''}
    (hf : ∀ i ∈ s, LocallyIntegrable (f i) μ) : LocallyIntegrable (fun a ↦ ∑ i ∈ s, f i a) μ := by
  simpa only [← Finset.sum_apply] using locallyIntegrable_finsetSum' s hf

@[deprecated (since := "2026-04-08")]
alias locallyIntegrable_finset_sum := locallyIntegrable_finsetSum

/-- If `f` is locally integrable and `g` is continuous with compact support,
then `g • f` is integrable. -/
/-
**MeasureTheory.LocallyIntegrable.integrable_smul_left_of_hasCompactSupport** 是 
Mathlib 中的一个定理，位于命名空间 `MeasureTheory.LocallyIntegrable`。
形式化陈述：∀ {X : Type u_1} {E : Type u_6} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : NormedAddCommGroup E]   {μ : MeasureTheory.Measure X} {
𝕜 : Type u_9} [inst_3 : NormedRing 𝕜] [inst_4 : _root_.Module 𝕜 E] [IsBoundedSMu
l 𝕜 E]   [OpensMeasurableSpace X] [T2Space X] {f : X → E},   MeasureTheory.Local
lyIntegrable f μ →     ∀ {g : X → 𝕜}, Continuous g → HasCompactSupport g → Measu
reTheory.Integrable (fun x => g x • f x) μ
参数：fun x => g x • f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.indicator_eq_self`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {
s : Set α} {f : α → M}, s.indicator f = f ↔ Function.support f ⊆ s
· 使用定理 `Function.support_subset_iff'`：∀ {ι : Type u_1} {M : Type u_3} [inst : Ze
ro M] {f : ι → M} {s : Set ι}, Function.support f ⊆ s ↔ ∀ x ∉ s, f x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `image_eq_zero_of_notMem_tsupport`：∀ {X : Type u_1} {α : Type u_2} [inst 
: Zero α] [inst_1 : TopologicalSpace X] {f : X → α} {x : X},   x ∉ tsupport f → 
f x = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.indicator_smul`：indicator_smul (s : Set α) (r : α -> R) (f : α -> M)
 : indicator s (fun a => r a • f a) = fun a => r a • indicator s f a
· 使用定理 `MeasureTheory.Integrable.smul_of_top_right`：∀ {α : Type u_1} {β : Type u
_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommG
roup β]   {𝕜 : Type u_8} [inst_1…
· 使用定理 `MeasureTheory.integrable_indicator_iff`：integrable_indicator_iff (hs : M
easurableSet s) : Integrable (indicator s f) μ ↔ IntegrableOn f s μ
· 使用定理 `IsCompact.measurableSet`：IsCompact.measurableSet [T2Space α] (h : IsComp
act s) : MeasurableSet s
· 使用定理 `MeasureTheory.LocallyIntegrable.integrableOn_isCompact`：∀ {X : Type u_1}
 {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2
 : TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Continuous.memLp_top_of_hasCompactSupport`：∀ {E : Type u_4} [inst : Norm
edAddCommGroup E] {X : Type u_7} [inst_1 : TopologicalSpace X] [inst_2 : Measura
bleSpace X]   [OpensMeasurableS…

--- 原说明 ---
If `f` is locally integrable and `g` is continuous with compact support,
then `g • f` is integrable.
-/
theorem LocallyIntegrable.integrable_smul_left_of_hasCompactSupport
    {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    [OpensMeasurableSpace X] [T2Space X] {f : X → E} (hf : LocallyIntegrable f μ)
    {g : X → 𝕜} (hg : Continuous g) (h'g : HasCompactSupport g) :
    Integrable (fun x ↦ g x • f x) μ := by
  let K := tsupport g
  have hK : IsCompact K := h'g
  have : K.indicator (fun x ↦ g x • f x) = (fun x ↦ g x • f x) := by
    apply indicator_eq_self.2
    apply support_subset_iff'.2
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  rw [← this, indicator_smul]
  apply Integrable.smul_of_top_right
  · rw [integrable_indicator_iff hK.measurableSet]
    exact hf.integrableOn_isCompact hK
  · exact hg.memLp_top_of_hasCompactSupport h'g μ

/-- If `f` is locally integrable and `g` is continuous with compact support,
then `f • g` is integrable. -/
/-
**MeasureTheory.LocallyIntegrable.integrable_smul_right_of_hasCompactSupport** 是
 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.LocallyIntegrable`。
形式化陈述：∀ {X : Type u_1} {E : Type u_6} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : NormedAddCommGroup E]   {μ : MeasureTheory.Measure X} {
𝕜 : Type u_9} [inst_3 : NormedRing 𝕜] [inst_4 : _root_.Module 𝕜 E] [IsBoundedSMu
l 𝕜 E]   [OpensMeasurableSpace X] [T2Space X] {f : X → 𝕜},   MeasureTheory.Local
lyIntegrable f μ →     ∀ {g : X → E}, Continuous g → HasCompactSupport g → Measu
reTheory.Integrable (fun x => f x • g x) μ
参数：fun x => f x • g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.indicator_eq_self`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {
s : Set α} {f : α → M}, s.indicator f = f ↔ Function.support f ⊆ s
· 使用定理 `Function.support_subset_iff'`：∀ {ι : Type u_1} {M : Type u_3} [inst : Ze
ro M] {f : ι → M} {s : Set ι}, Function.support f ⊆ s ↔ ∀ x ∉ s, f x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `image_eq_zero_of_notMem_tsupport`：∀ {X : Type u_1} {α : Type u_2} [inst 
: Zero α] [inst_1 : TopologicalSpace X] {f : X → α} {x : X},   x ∉ tsupport f → 
f x = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.indicator_smul_left`：indicator_smul_left (s : Set α) (r : α -> R) (f
 : α -> M) : indicator s (fun a => r a • f a) = fun a => indicator s r a • f a
· 使用定理 `MeasureTheory.Integrable.smul_of_top_left`：∀ {α : Type u_1} {β : Type u_
2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGr
oup β]   {𝕜 : Type u_8} [inst_1…
· 使用定理 `MeasureTheory.integrable_indicator_iff`：integrable_indicator_iff (hs : M
easurableSet s) : Integrable (indicator s f) μ ↔ IntegrableOn f s μ
· 使用定理 `IsCompact.measurableSet`：IsCompact.measurableSet [T2Space α] (h : IsComp
act s) : MeasurableSet s
· 使用定理 `MeasureTheory.LocallyIntegrable.integrableOn_isCompact`：∀ {X : Type u_1}
 {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2
 : TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Continuous.memLp_top_of_hasCompactSupport`：∀ {E : Type u_4} [inst : Norm
edAddCommGroup E] {X : Type u_7} [inst_1 : TopologicalSpace X] [inst_2 : Measura
bleSpace X]   [OpensMeasurableS…

--- 原说明 ---
If `f` is locally integrable and `g` is continuous with compact support,
then `f • g` is integrable.
-/
theorem LocallyIntegrable.integrable_smul_right_of_hasCompactSupport
     {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
     [OpensMeasurableSpace X] [T2Space X] {f : X → 𝕜} (hf : LocallyIntegrable f μ)
     {g : X → E} (hg : Continuous g) (h'g : HasCompactSupport g) :
    Integrable (fun x ↦ f x • g x) μ := by
  let K := tsupport g
  have hK : IsCompact K := h'g
  have : K.indicator (fun x ↦ f x • g x) = (fun x ↦ f x • g x) := by
    apply indicator_eq_self.2
    apply support_subset_iff'.2
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  rw [← this, indicator_smul_left]
  apply Integrable.smul_of_top_left
  · rw [integrable_indicator_iff hK.measurableSet]
    exact hf.integrableOn_isCompact hK
  · exact hg.memLp_top_of_hasCompactSupport h'g μ

open Filter

variable [PseudoMetrizableSpace ε]
/-
**MeasureTheory.integrable_iff_integrableAtFilter_cocompact** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory`。
形式化陈述：integrable_iff_integrableAtFilter_cocompact : Integrable f μ ↔ (Integrable
AtFilter f (cocompact X) μ ∧ LocallyIntegrable f μ)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.integrableAtFilter`：∀ {α : Type u_1} {ε : Type 
u_3} {mα : MeasurableSpace α} {f : α → ε} {μ : MeasureTheory.Measure α}   [inst 
: TopologicalSpace ε] [inst_1 : C…
· 使用定理 `MeasureTheory.Integrable.locallyIntegrable`：∀ {X : Type u_1} {ε : Type u
_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 : Topologic
alSpace ε]   [inst_3 : Continuou…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_cocompact'`：mem_cocompact' : s in cocompact X ↔ exists t, IsC
ompact t ∧ sᶜ subseteq t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integrableOn_univ`：integrableOn_univ : IntegrableOn f univ
 μ ↔ Integrable f μ
· 使用定理 `Set.compl_union_self`：compl_union_self (s : Set α) : sᶜ union s = univ
· 使用定理 `MeasureTheory.integrableOn_union`：integrableOn_union [PseudoMetrizableSp
ace ε] : IntegrableOn f (s union t) μ ↔ IntegrableOn f s μ ∧ IntegrableOn f t μ
· 使用定理 `MeasureTheory.IntegrableOn.mono`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} {f : α → ε} {s t : Set α} {μ ν : MeasureTheory.Measure α}   [i
nst : TopologicalSpac…
· 使用定理 `MeasureTheory.LocallyIntegrable.integrableOn_isCompact`：∀ {X : Type u_1}
 {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2
 : TopologicalSpace ε]   [inst_3 : Continuou…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem integrable_iff_integrableAtFilter_cocompact :
    Integrable f μ ↔ (IntegrableAtFilter f (cocompact X) μ ∧ LocallyIntegrable f μ) := by
  refine ⟨fun hf ↦ ⟨hf.integrableAtFilter _, hf.locallyIntegrable⟩, fun ⟨⟨s, hsc, hs⟩, hloc⟩ ↦ ?_⟩
  obtain ⟨t, htc, ht⟩ := mem_cocompact'.mp hsc
  rewrite [← integrableOn_univ, ← compl_union_self s, integrableOn_union]
  exact ⟨(hloc.integrableOn_isCompact htc).mono ht le_rfl, hs⟩
/-
**MeasureTheory.integrable_iff_integrableAtFilter_atBot_atTop** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_iff_integrableAtFilter_atBot_atTop [PseudoMetrizableSpace ε''] 
{f : X -> ε''} [LinearOrder X] [CompactIccSpace X] : Integrable f μ ↔ (Integrabl
eAtFilter f atBot μ ∧ IntegrableAtFilter f atTop μ) ∧ LocallyIntegrable f μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.integrableAtFilter`：∀ {α : Type u_1} {ε : Type 
u_3} {mα : MeasurableSpace α} {f : α → ε} {μ : MeasureTheory.Measure α}   [inst 
: TopologicalSpace ε] [inst_1 : C…
· 使用定理 `MeasureTheory.Integrable.locallyIntegrable`：∀ {X : Type u_1} {ε : Type u
_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 : Topologic
alSpace ε]   [inst_3 : Continuou…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrable_iff_integrableAtFilter_cocompact`：integrable_if
f_integrableAtFilter_cocompact : Integrable f μ ↔ (IntegrableAtFilter f (cocompa
ct X) μ ∧ LocallyIntegrable f μ)
· 使用定理 `MeasureTheory.IntegrableAtFilter.filter_mono`：∀ {α : Type u_1} {ε : Type
 u_3} {mα : MeasurableSpace α} {f : α → ε} {μ : MeasureTheory.Measure α}   [inst
 : TopologicalSpace ε] [inst_1 : C…
· 使用定理 `cocompact_le_atBot_atTop`：cocompact_le_atBot_atTop [CompactIccSpace α] :
 cocompact α <= atBot ⊔ atTop
· 使用定理 `MeasureTheory.IntegrableAtFilter.sup_iff`：∀ {α : Type u_1} {ε' : Type u_
4} {mα : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpa
ce ε']   [inst_1 : ESeminormed…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem integrable_iff_integrableAtFilter_atBot_atTop
    [PseudoMetrizableSpace ε''] {f : X → ε''} [LinearOrder X] [CompactIccSpace X] :
    Integrable f μ ↔
    (IntegrableAtFilter f atBot μ ∧ IntegrableAtFilter f atTop μ) ∧ LocallyIntegrable f μ := by
  constructor
  · exact fun hf ↦ ⟨⟨hf.integrableAtFilter _, hf.integrableAtFilter _⟩, hf.locallyIntegrable⟩
  · refine fun h ↦ integrable_iff_integrableAtFilter_cocompact.mpr ⟨?_, h.2⟩
    exact (IntegrableAtFilter.sup_iff.mpr h.1).filter_mono cocompact_le_atBot_atTop
/-
**MeasureTheory.integrable_iff_integrableAtFilter_atBot** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：integrable_iff_integrableAtFilter_atBot [LinearOrder X] [OrderTop X] [Comp
actIccSpace X] : Integrable f μ ↔ IntegrableAtFilter f atBot μ ∧ LocallyIntegrab
le f μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.integrableAtFilter`：∀ {α : Type u_1} {ε : Type 
u_3} {mα : MeasurableSpace α} {f : α → ε} {μ : MeasureTheory.Measure α}   [inst 
: TopologicalSpace ε] [inst_1 : C…
· 使用定理 `MeasureTheory.Integrable.locallyIntegrable`：∀ {X : Type u_1} {ε : Type u
_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 : Topologic
alSpace ε]   [inst_3 : Continuou…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrable_iff_integrableAtFilter_cocompact`：integrable_if
f_integrableAtFilter_cocompact : Integrable f μ ↔ (IntegrableAtFilter f (cocompa
ct X) μ ∧ LocallyIntegrable f μ)
· 使用定理 `MeasureTheory.IntegrableAtFilter.filter_mono`：∀ {α : Type u_1} {ε : Type
 u_3} {mα : MeasurableSpace α} {f : α → ε} {μ : MeasureTheory.Measure α}   [inst
 : TopologicalSpace ε] [inst_1 : C…
· 使用定理 `cocompact_le_atBot`：cocompact_le_atBot [OrderTop α] [CompactIccSpace α] 
: cocompact α <= atBot
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem integrable_iff_integrableAtFilter_atBot [LinearOrder X] [OrderTop X] [CompactIccSpace X] :
    Integrable f μ ↔ IntegrableAtFilter f atBot μ ∧ LocallyIntegrable f μ := by
  constructor
  · exact fun hf ↦ ⟨hf.integrableAtFilter _, hf.locallyIntegrable⟩
  · refine fun h ↦ integrable_iff_integrableAtFilter_cocompact.mpr ⟨?_, h.2⟩
    exact h.1.filter_mono cocompact_le_atBot
/-
**MeasureTheory.integrable_iff_integrableAtFilter_atTop** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：integrable_iff_integrableAtFilter_atTop [LinearOrder X] [OrderBot X] [Comp
actIccSpace X] : Integrable f μ ↔ IntegrableAtFilter f atTop μ ∧ LocallyIntegrab
le f μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_iff_integrableAtFilter_atBot`：integrable_iff_in
tegrableAtFilter_atBot [LinearOrder X] [OrderTop X] [CompactIccSpace X] : Integr
able f μ ↔ IntegrableAtFilter f atBot μ ∧ L…
· 使用定理 `instCompactIccSpaceOrderDual`：∀ {α : Type u_1} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [CompactIccSpace α], CompactIccSpace αᵒᵈ
-/
theorem integrable_iff_integrableAtFilter_atTop [LinearOrder X] [OrderBot X] [CompactIccSpace X] :
    Integrable f μ ↔ IntegrableAtFilter f atTop μ ∧ LocallyIntegrable f μ :=
  integrable_iff_integrableAtFilter_atBot (X := Xᵒᵈ)

variable {a : X}
/-
**MeasureTheory.integrableOn_Iic_iff_integrableAtFilter_atBot** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory`。
形式化陈述：integrableOn_Iic_iff_integrableAtFilter_atBot [LinearOrder X] [CompactIccS
pace X] : IntegrableOn f (Iic a) μ ↔ IntegrableAtFilter f atBot μ ∧ LocallyInteg
rableOn f (Iic a) μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Iic_mem_atBot`：∀ {α : Type u_3} [inst : Preorder α] (a : α), Set.
Iic a ∈ Filter.atBot
· 使用定理 `MeasureTheory.IntegrableOn.locallyIntegrableOn`：∀ {X : Type u_1} {ε : Ty
pe u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 : Topol
ogicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_atBot_sets`：∀ {α : Type u_3} [inst : Preorder α] [IsCodirecte
dOrder α] [Nonempty α] {s : Set α},   s ∈ Filter.atBot ↔ ∃ a, ∀ b ≤ a, b ∈ s
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `MeasureTheory.IntegrableOn.mono`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} {f : α → ε} {s t : Set α} {μ ν : MeasureTheory.Measure α}   [i
nst : TopologicalSpac…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrableOn_union`：integrableOn_union [PseudoMetrizableSp
ace ε] : IntegrableOn f (s union t) μ ↔ IntegrableOn f s μ ∧ IntegrableOn f t μ
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.LocallyIntegrableOn.integrableOn_compact_subset`：∀ {X : Ty
pe u_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] 
[inst_2 : TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `Set.Icc_subset_Iic_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Icc a b ⊆ Set.Iic b
· 使用定理 `CompactIccSpace.isCompact_Icc`：∀ {α : Type u_1} {inst : TopologicalSpace
 α} {inst_1 : Preorder α} [self : CompactIccSpace α] {a b : α},   IsCompact (Set
.Icc a b)
· 使用定理 `Set.Iic_subset_Iic_union_Icc`：Iic_subset_Iic_union_Icc : Iic b subseteq 
Iic a union Icc a b
-/
theorem integrableOn_Iic_iff_integrableAtFilter_atBot [LinearOrder X] [CompactIccSpace X] :
    IntegrableOn f (Iic a) μ ↔ IntegrableAtFilter f atBot μ ∧ LocallyIntegrableOn f (Iic a) μ := by
  refine ⟨fun h ↦ ⟨⟨Iic a, Iic_mem_atBot a, h⟩, h.locallyIntegrableOn⟩, fun ⟨⟨s, hsl, hs⟩, h⟩ ↦ ?_⟩
  have : Nonempty X := Nonempty.intro a
  obtain ⟨a', ha'⟩ := mem_atBot_sets.mp hsl
  refine (integrableOn_union.mpr ⟨hs.mono ha' le_rfl, ?_⟩).mono Iic_subset_Iic_union_Icc le_rfl
  exact h.integrableOn_compact_subset Icc_subset_Iic_self isCompact_Icc
/-
**MeasureTheory.integrableOn_Ici_iff_integrableAtFilter_atTop** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory`。
形式化陈述：integrableOn_Ici_iff_integrableAtFilter_atTop [LinearOrder X] [CompactIccS
pace X] : IntegrableOn f (Ici a) μ ↔ IntegrableAtFilter f atTop μ ∧ LocallyInteg
rableOn f (Ici a) μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrableOn_Iic_iff_integrableAtFilter_atBot`：integrableO
n_Iic_iff_integrableAtFilter_atBot [LinearOrder X] [CompactIccSpace X] : Integra
bleOn f (Iic a) μ ↔ IntegrableAtFilter f atBot μ …
· 使用定理 `instCompactIccSpaceOrderDual`：∀ {α : Type u_1} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [CompactIccSpace α], CompactIccSpace αᵒᵈ
-/
theorem integrableOn_Ici_iff_integrableAtFilter_atTop [LinearOrder X] [CompactIccSpace X] :
    IntegrableOn f (Ici a) μ ↔ IntegrableAtFilter f atTop μ ∧ LocallyIntegrableOn f (Ici a) μ :=
  integrableOn_Iic_iff_integrableAtFilter_atBot (X := Xᵒᵈ)
/-
**MeasureTheory.integrableOn_Iio_iff_integrableAtFilter_atBot_nhdsWithin** 是 Mat
hlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrableOn_Iio_iff_integrableAtFilter_atBot_nhdsWithin [LinearOrder X] [
CompactIccSpace X] [NoMinOrder X] [OrderTopology X] : IntegrableOn f (Iio a) μ ↔
 IntegrableAtFilter f atBot μ ∧ IntegrableAtFilter f (𝓝[<] a) μ ∧ LocallyIntegra
bleOn f (Iio a) μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Iio_mem_atBot`：∀ {α : Type u_3} [inst : Preorder α] [NoBotOrder α
] (x : α), Set.Iio x ∈ Filter.atBot
· 使用定理 `instNoBotOrderOfNoMinOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMinO
rder α], NoBotOrder α
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `MeasureTheory.IntegrableOn.locallyIntegrableOn`：∀ {X : Type u_1} {ε : Ty
pe u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 : Topol
ogicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsLT_iff_exists_Ioo_subset`：mem_nhdsLT_iff_exists_Ioo_subset [NoMi
nOrder α] {a : α} {s : Set α} : s in 𝓝[<] a ↔ exists l in Iio a, Ioo l a subsete
q s
· 使用定理 `MeasureTheory.IntegrableOn.mono`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} {f : α → ε} {s t : Set α} {μ ν : MeasureTheory.Measure α}   [i
nst : TopologicalSpac…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrableOn_union`：integrableOn_union [PseudoMetrizableSp
ace ε] : IntegrableOn f (s union t) μ ↔ IntegrableOn f s μ ∧ IntegrableOn f t μ
· 使用定理 `MeasureTheory.integrableOn_Iic_iff_integrableAtFilter_atBot`：integrableO
n_Iic_iff_integrableAtFilter_atBot [LinearOrder X] [CompactIccSpace X] : Integra
bleOn f (Iic a) μ ↔ IntegrableAtFilter f atBot μ …
· 使用定理 `MeasureTheory.LocallyIntegrableOn.mono_set`：∀ {X : Type u_1} {ε : Type u
_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 : Topologic
alSpace ε]   [inst_3 : Continuou…
· 使用定理 `Set.Iic_subset_Iio`：Iic_subset_Iio : Iic a subseteq Iio b ↔ a < b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Set.Iio_subset_Iic_union_Ioo`：Iio_subset_Iic_union_Ioo : Iio b subseteq 
Iic a union Ioo a b
-/
theorem integrableOn_Iio_iff_integrableAtFilter_atBot_nhdsWithin
    [LinearOrder X] [CompactIccSpace X] [NoMinOrder X] [OrderTopology X] :
    IntegrableOn f (Iio a) μ ↔ IntegrableAtFilter f atBot μ ∧
    IntegrableAtFilter f (𝓝[<] a) μ ∧ LocallyIntegrableOn f (Iio a) μ := by
  constructor
  · intro h
    exact ⟨⟨Iio a, Iio_mem_atBot a, h⟩, ⟨Iio a, self_mem_nhdsWithin, h⟩, h.locallyIntegrableOn⟩
  · intro ⟨hbot, ⟨s, hsl, hs⟩, hlocal⟩
    obtain ⟨s', ⟨hs'_mono, hs'⟩⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hsl
    refine (integrableOn_union.mpr ⟨?_, hs.mono hs' le_rfl⟩).mono Iio_subset_Iic_union_Ioo le_rfl
    exact integrableOn_Iic_iff_integrableAtFilter_atBot.mpr
      ⟨hbot, hlocal.mono_set (Iic_subset_Iio.mpr hs'_mono)⟩
/-
**MeasureTheory.integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin** 是 Mat
hlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin [LinearOrder X] [
CompactIccSpace X] [NoMaxOrder X] [OrderTopology X] : IntegrableOn f (Ioi a) μ ↔
 IntegrableAtFilter f atTop μ ∧ IntegrableAtFilter f (𝓝[>] a) μ ∧ LocallyIntegra
bleOn f (Ioi a) μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrableOn_Iio_iff_integrableAtFilter_atBot_nhdsWithin`：
integrableOn_Iio_iff_integrableAtFilter_atBot_nhdsWithin [LinearOrder X] [Compac
tIccSpace X] [NoMinOrder X] [OrderTopology X] : IntegrableOn…
· 使用定理 `instCompactIccSpaceOrderDual`：∀ {α : Type u_1} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [CompactIccSpace α], CompactIccSpace αᵒᵈ
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin
    [LinearOrder X] [CompactIccSpace X] [NoMaxOrder X] [OrderTopology X] :
    IntegrableOn f (Ioi a) μ ↔ IntegrableAtFilter f atTop μ ∧
    IntegrableAtFilter f (𝓝[>] a) μ ∧ LocallyIntegrableOn f (Ioi a) μ :=
  integrableOn_Iio_iff_integrableAtFilter_atBot_nhdsWithin (X := Xᵒᵈ)

end MeasureTheory

open MeasureTheory

section borel

variable [OpensMeasurableSpace X]
variable {K : Set X} {f : X → E} {a b : X}

/-- A continuous function `f` is locally integrable with respect to any locally finite measure. -/
/-
**Continuous.locallyIntegrable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.locallyIntegrable [IsLocallyFiniteMeasure μ] [SecondCountableTo
pologyEither X E] (hf : Continuous f) : LocallyIntegrable f μ
参数：hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.integrableAt_nhds`：Continuous.integrableAt_nhds [TopologicalS
pace α] [SecondCountableTopologyEither α E] [OpensMeasurableSpace α] {μ : Measur
e α} [IsLocallyFin…

--- 原说明 ---
A continuous function `f` is locally integrable with respect to any locally fini
te measure.
-/
theorem Continuous.locallyIntegrable [IsLocallyFiniteMeasure μ] [SecondCountableTopologyEither X E]
    (hf : Continuous f) : LocallyIntegrable f μ :=
  hf.integrableAt_nhds

/-- A function `f` continuous on a set `K` is locally integrable on this set with respect
to any locally finite measure. -/
/-
**ContinuousOn.locallyIntegrableOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.locallyIntegrableOn [IsLocallyFiniteMeasure μ] [SecondCountab
leTopologyEither X E] (hf : ContinuousOn f K) (hK : MeasurableSet K) : LocallyIn
tegrableOn f K μ
参数：hf : ContinuousOn f K；hK : MeasurableSet K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.integrableAt_nhdsWithin`：ContinuousOn.integrableAt_nhdsWith
in [TopologicalSpace α] [SecondCountableTopologyEither α E] [OpensMeasurableSpac
e α] {μ : Measure α} [IsLo…

--- 原说明 ---
A function `f` continuous on a set `K` is locally integrable on this set with re
spect
to any locally finite measure.
-/
theorem ContinuousOn.locallyIntegrableOn [IsLocallyFiniteMeasure μ]
    [SecondCountableTopologyEither X E] (hf : ContinuousOn f K)
    (hK : MeasurableSet K) : LocallyIntegrableOn f K μ := fun _x hx =>
  hf.integrableAt_nhdsWithin hK hx

/-- If `f` is continuous on a compact set `K`, then it is integrable on any measurable subset
`s ⊆ K` of finite measure. -/
/-
**ContinuousOn.integrableOn_of_subset_isCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.integrableOn_of_subset_isCompact (hf : ContinuousOn f K) (hK 
: IsCompact K) (hs : MeasurableSet s) (h's : s subseteq K) (mus : μ s != ∞) : In
tegrableOn f s μ
参数：hf : ContinuousOn f K；hK : IsCompact K；hs : MeasurableSet s；h's : s subseteq 
K；mus : μ s != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.aestronglyMeasurable_of_subset_isCompact`：ContinuousOn.aest
ronglyMeasurable_of_subset_isCompact [TopologicalSpace α] [OpensMeasurableSpace 
α] [TopologicalSpace β] [PseudoMetrizableSp…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `Bornology.IsBounded.exists_norm_le`：∀ {E : Type u_2} [inst : SeminormedA
ddGroup E] {s : Set E}, Bornology.IsBounded s → ∃ C, ∀ x ∈ s, ‖x‖ ≤ C
· 使用定理 `IsCompact.isBounded`：∀ {α : Type u} [inst : PseudoMetricSpace α] {s : Se
t α}, IsCompact s → Bornology.IsBounded s
· 使用定理 `IsCompact.image_of_continuousOn`：IsCompact.image_of_continuousOn {f : X 
-> Y} (hs : IsCompact s) (hf : ContinuousOn f s) : IsCompact (f '' s)
· 使用定理 `MeasureTheory.HasFiniteIntegral.of_bounded`：∀ {α : Type u_1} {β : Type u
_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommG
roup β]   [MeasureTheory.IsFinit…
· 使用定理 `MeasureTheory.Restrict.isFiniteMeasure`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {s : Set α} (μ : MeasureTheory.Measure α) [hs : Fact (μ s < ⊤)],   Mea
sureTheory.IsFiniteMeasure (…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_restrict_mem`：ae_restrict_mem (hs : MeasurableSet s) : 
forallᵐ x ∂μ.restrict s, x in s
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a

--- 原说明 ---
If `f` is continuous on a compact set `K`, then it is integrable on any measurab
le subset
`s ⊆ K` of finite measure.
-/
theorem ContinuousOn.integrableOn_of_subset_isCompact (hf : ContinuousOn f K)
    (hK : IsCompact K) (hs : MeasurableSet s) (h's : s ⊆ K) (mus : μ s ≠ ∞) :
    IntegrableOn f s μ := by
  refine ⟨hf.aestronglyMeasurable_of_subset_isCompact hK hs h's, ?_⟩
  have : Fact (μ s < ∞) := ⟨mus.lt_top⟩
  obtain ⟨C, hC⟩ : ∃ C, ∀ x ∈ f '' K, ‖x‖ ≤ C :=
    IsBounded.exists_norm_le (hK.image_of_continuousOn hf).isBounded
  apply HasFiniteIntegral.of_bounded (C := C)
  filter_upwards [ae_restrict_mem hs] with a ha using hC _ (mem_image_of_mem f (h's ha))

variable [IsFiniteMeasureOnCompacts μ]

/-- A function `f` continuous on a compact set `K` is integrable on this set with respect to any
locally finite measure. -/
/-
**ContinuousOn.integrableOn_compact'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.integrableOn_compact' (hK : IsCompact K) (h'K : MeasurableSet
 K) (hf : ContinuousOn f K) : IntegrableOn f K μ
参数：hK : IsCompact K；h'K : MeasurableSet K；hf : ContinuousOn f K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.integrableOn_of_subset_isCompact`：ContinuousOn.integrableOn
_of_subset_isCompact (hf : ContinuousOn f K) (hK : IsCompact K) (hs : Measurable
Set s) (h's : s subseteq K) (mus : …
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `IsCompact.measure_ne_top`：∀ {α : Type u_1} {m0 : MeasurableSpace α} [ins
t : TopologicalSpace α] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsFiniteM
easureOnCompac…

--- 原说明 ---
A function `f` continuous on a compact set `K` is integrable on this set with re
spect to any
locally finite measure.
-/
theorem ContinuousOn.integrableOn_compact'
    (hK : IsCompact K) (h'K : MeasurableSet K) (hf : ContinuousOn f K) :
    IntegrableOn f K μ :=
  hf.integrableOn_of_subset_isCompact hK h'K Subset.rfl hK.measure_ne_top
/-
**ContinuousOn.integrableOn_compact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.integrableOn_compact [T2Space X] (hK : IsCompact K) (hf : Con
tinuousOn f K) : IntegrableOn f K μ
参数：hK : IsCompact K；hf : ContinuousOn f K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.integrableOn_compact'`：ContinuousOn.integrableOn_compact' (
hK : IsCompact K) (h'K : MeasurableSet K) (hf : ContinuousOn f K) : IntegrableOn
 f K μ
· 使用定理 `IsCompact.measurableSet`：IsCompact.measurableSet [T2Space α] (h : IsComp
act s) : MeasurableSet s
-/
theorem ContinuousOn.integrableOn_compact [T2Space X]
    (hK : IsCompact K) (hf : ContinuousOn f K) : IntegrableOn f K μ :=
  hf.integrableOn_compact' hK hK.measurableSet
/-
**ContinuousOn.integrableOn_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.integrableOn_Icc [Preorder X] [CompactIccSpace X] [T2Space X]
 (hf : ContinuousOn f (Icc a b)) : IntegrableOn f (Icc a b) μ
参数：hf : ContinuousOn f (Icc a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.integrableOn_compact`：ContinuousOn.integrableOn_compact [T2
Space X] (hK : IsCompact K) (hf : ContinuousOn f K) : IntegrableOn f K μ
· 使用定理 `CompactIccSpace.isCompact_Icc`：∀ {α : Type u_1} {inst : TopologicalSpace
 α} {inst_1 : Preorder α} [self : CompactIccSpace α] {a b : α},   IsCompact (Set
.Icc a b)
-/
theorem ContinuousOn.integrableOn_Icc [Preorder X] [CompactIccSpace X] [T2Space X]
    (hf : ContinuousOn f (Icc a b)) : IntegrableOn f (Icc a b) μ :=
  hf.integrableOn_compact isCompact_Icc
/-
**Continuous.integrableOn_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.integrableOn_Icc [Preorder X] [CompactIccSpace X] [T2Space X] (
hf : Continuous f) : IntegrableOn f (Icc a b) μ
参数：hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.integrableOn_Icc`：ContinuousOn.integrableOn_Icc [Preorder X
] [CompactIccSpace X] [T2Space X] (hf : ContinuousOn f (Icc a b)) : IntegrableOn
 f (Icc a b) μ
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
-/
theorem Continuous.integrableOn_Icc [Preorder X] [CompactIccSpace X] [T2Space X]
    (hf : Continuous f) : IntegrableOn f (Icc a b) μ :=
  hf.continuousOn.integrableOn_Icc
/-
**Continuous.integrableOn_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.integrableOn_Ioc [Preorder X] [CompactIccSpace X] [T2Space X] (
hf : Continuous f) : IntegrableOn f (Ioc a b) μ
参数：hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `Continuous.integrableOn_Icc`：Continuous.integrableOn_Icc [Preorder X] [C
ompactIccSpace X] [T2Space X] (hf : Continuous f) : IntegrableOn f (Icc a b) μ
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
-/
theorem Continuous.integrableOn_Ioc [Preorder X] [CompactIccSpace X] [T2Space X]
    (hf : Continuous f) : IntegrableOn f (Ioc a b) μ :=
  hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self
/-
**ContinuousOn.integrableOn_uIcc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.integrableOn_uIcc [LinearOrder X] [CompactIccSpace X] [T2Spac
e X] (hf : ContinuousOn f [[a, b]]) : IntegrableOn f [[a, b]] μ
参数：hf : ContinuousOn f [[a, b]]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.integrableOn_Icc`：ContinuousOn.integrableOn_Icc [Preorder X
] [CompactIccSpace X] [T2Space X] (hf : ContinuousOn f (Icc a b)) : IntegrableOn
 f (Icc a b) μ
-/
theorem ContinuousOn.integrableOn_uIcc [LinearOrder X] [CompactIccSpace X] [T2Space X]
    (hf : ContinuousOn f [[a, b]]) : IntegrableOn f [[a, b]] μ :=
  hf.integrableOn_Icc
/-
**Continuous.integrableOn_uIcc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.integrableOn_uIcc [LinearOrder X] [CompactIccSpace X] [T2Space 
X] (hf : Continuous f) : IntegrableOn f [[a, b]] μ
参数：hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.integrableOn_Icc`：Continuous.integrableOn_Icc [Preorder X] [C
ompactIccSpace X] [T2Space X] (hf : Continuous f) : IntegrableOn f (Icc a b) μ
-/
theorem Continuous.integrableOn_uIcc [LinearOrder X] [CompactIccSpace X] [T2Space X]
    (hf : Continuous f) : IntegrableOn f [[a, b]] μ :=
  hf.integrableOn_Icc

open scoped Interval in
/-
**Continuous.integrableOn_uIoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.integrableOn_uIoc [LinearOrder X] [CompactIccSpace X] [T2Space 
X] (hf : Continuous f) : IntegrableOn f (Ι a b) μ
参数：hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.integrableOn_Ioc`：Continuous.integrableOn_Ioc [Preorder X] [C
ompactIccSpace X] [T2Space X] (hf : Continuous f) : IntegrableOn f (Ioc a b) μ
-/
theorem Continuous.integrableOn_uIoc [LinearOrder X] [CompactIccSpace X] [T2Space X]
    (hf : Continuous f) : IntegrableOn f (Ι a b) μ :=
  hf.integrableOn_Ioc

/-- A continuous function with compact support is integrable on the whole space. -/
/-
**Continuous.integrable_of_hasCompactSupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.integrable_of_hasCompactSupport (hf : Continuous f) (hcf : HasC
ompactSupport f) : Integrable f μ
参数：hf : Continuous f；hcf : HasCompactSupport f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.integrableOn_iff_integrable_of_support_subset`：integrableO
n_iff_integrable_of_support_subset {f : α -> ε'} (h1s : support f subseteq s) : 
IntegrableOn f s μ ↔ Integrable f μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `subset_tsupport`：∀ {X : Type u_1} {α : Type u_2} [inst : Zero α] [inst_1
 : TopologicalSpace X] (f : X → α),   Function.support f ⊆ tsupport f
· 使用定理 `ContinuousOn.integrableOn_compact'`：ContinuousOn.integrableOn_compact' (
hK : IsCompact K) (h'K : MeasurableSet K) (hf : ContinuousOn f K) : IntegrableOn
 f K μ
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `isClosed_tsupport`：∀ {X : Type u_1} {α : Type u_2} [inst : Zero α] [inst
_1 : TopologicalSpace X] (f : X → α), IsClosed (tsupport f)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s

--- 原说明 ---
A continuous function with compact support is integrable on the whole space.
-/
theorem Continuous.integrable_of_hasCompactSupport (hf : Continuous f) (hcf : HasCompactSupport f) :
    Integrable f μ :=
  (integrableOn_iff_integrable_of_support_subset (subset_tsupport f)).mp <|
    hf.continuousOn.integrableOn_compact' hcf (isClosed_tsupport _).measurableSet

end borel

open scoped ENNReal

section Monotone

variable [BorelSpace X] [ConditionallyCompleteLinearOrder X] [ConditionallyCompleteLinearOrder E]
  [OrderTopology X] [OrderTopology E] [SecondCountableTopology E] {p : ℝ≥0∞}
  {f : X → E}

/-
**MonotoneOn.memLp_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.memLp_top (hmono : MonotoneOn f s) {a b : X} (ha : IsLeast s a)
 (hb : IsGreatest s b) (h's : MeasurableSet s) : MemLp f ∞ (μ.restrict s)
参数：hmono : MonotoneOn f s；ha : IsLeast s a；hb : IsGreatest s b；h's : MeasurableS
et s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Metric.isBounded_of_bddAbove_of_bddBelow`：isBounded_of_bddAbove_of_bddBe
low {s : Set α} (h₁ : BddAbove s) (h₂ : BddBelow s) : IsBounded s
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isBounded_iff_forall_norm_le`：∀ {E : Type u_2} [inst : SeminormedAddGrou
p E] {s : Set E}, Bornology.IsBounded s ↔ ∃ C, ∀ x ∈ s, ‖x‖ ≤ C
· 使用定理 `MeasureTheory.memLp_top_const`：memLp_top_const (c : E) : MemLp (fun _ : 
α => c) ∞ μ
· 使用定理 `MeasureTheory.MemLp.mono`：∀ {α : Type u_1} {E : Type u_4} {F : Type u_5}
 {m0 : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : 
NormedAddCommG…
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `aemeasurable_restrict_of_monotoneOn`：aemeasurable_restrict_of_monotoneOn
 [LinearOrder β] [OrderClosedTopology β] {μ : Measure β} {s : Set β} (hs : Measu
rableSet s) {f : β -> α} …
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
-/
theorem MonotoneOn.memLp_top (hmono : MonotoneOn f s) {a b : X}
    (ha : IsLeast s a) (hb : IsGreatest s b) (h's : MeasurableSet s) :
    MemLp f ∞ (μ.restrict s) := by
  borelize E
  have hbelow : BddBelow (f '' s) := ⟨f a, fun x ⟨y, hy, hyx⟩ => hyx ▸ hmono ha.1 hy (ha.2 hy)⟩
  have habove : BddAbove (f '' s) := ⟨f b, fun x ⟨y, hy, hyx⟩ => hyx ▸ hmono hy hb.1 (hb.2 hy)⟩
  have : IsBounded (f '' s) := Metric.isBounded_of_bddAbove_of_bddBelow habove hbelow
  rcases isBounded_iff_forall_norm_le.mp this with ⟨C, hC⟩
  have A : MemLp (fun _ => C) ⊤ (μ.restrict s) := memLp_top_const _
  apply MemLp.mono A (aemeasurable_restrict_of_monotoneOn h's hmono).aestronglyMeasurable
  apply (ae_restrict_iff' h's).mpr
  apply ae_of_all _ fun y hy ↦ ?_
  exact (hC _ (mem_image_of_mem f hy)).trans (le_abs_self _)
/-
**MonotoneOn.memLp_of_measure_ne_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.memLp_of_measure_ne_top (hmono : MonotoneOn f s) {a b : X} (ha 
: IsLeast s a) (hb : IsGreatest s b) (hs : μ s != ∞) (h's : MeasurableSet s) : M
emLp f p (μ.restrict s)
参数：hmono : MonotoneOn f s；ha : IsLeast s a；hb : IsGreatest s b；hs : μ s != ∞；h's
 : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.mono_exponent_of_measure_support_ne_top`：∀ {α : Type
 u_1} {ε' : Type u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [ins
t : TopologicalSpace ε']   [inst_1 : ESeminormedA…
· 使用定理 `MonotoneOn.memLp_top`：MonotoneOn.memLp_top (hmono : MonotoneOn f s) {a b
 : X} (ha : IsLeast s a) (hb : IsGreatest s b) (h's : MeasurableSet s) : MemLp f
 ∞ (μ.rest…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem MonotoneOn.memLp_of_measure_ne_top (hmono : MonotoneOn f s) {a b : X}
    (ha : IsLeast s a) (hb : IsGreatest s b) (hs : μ s ≠ ∞) (h's : MeasurableSet s) :
    MemLp f p (μ.restrict s) :=
  (hmono.memLp_top ha hb h's).mono_exponent_of_measure_support_ne_top (s := univ)
    (by simp) (by simpa using hs) le_top
/-
**MonotoneOn.memLp_isCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.memLp_isCompact [IsFiniteMeasureOnCompacts μ] (hs : IsCompact s
) (hmono : MonotoneOn f s) : MemLp f p (μ.restrict s)
参数：hs : IsCompact s；hmono : MonotoneOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_empty`：restrict_empty : μ.restrict ∅ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonotoneOn.memLp_of_measure_ne_top`：MonotoneOn.memLp_of_measure_ne_top (
hmono : MonotoneOn f s) {a b : X} (ha : IsLeast s a) (hb : IsGreatest s b) (hs :
 μ s != ∞) (h's : Measur…
· 使用定理 `IsCompact.isLeast_sInf`：IsCompact.isLeast_sInf [ClosedIicTopology α] {s 
: Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : IsLeast s (sInf s)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `IsCompact.isGreatest_sSup`：IsCompact.isGreatest_sSup [ClosedIciTopology 
α] {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : IsGreatest s (sSup s)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `IsCompact.measure_lt_top`：∀ {α : Type u_1} {m0 : MeasurableSpace α} [ins
t : TopologicalSpace α] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsFiniteM
easureOnCompac…
· 使用定理 `IsCompact.measurableSet`：IsCompact.measurableSet [T2Space α] (h : IsComp
act s) : MeasurableSet s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
-/
theorem MonotoneOn.memLp_isCompact [IsFiniteMeasureOnCompacts μ] (hs : IsCompact s)
    (hmono : MonotoneOn f s) : MemLp f p (μ.restrict s) := by
  obtain rfl | h := s.eq_empty_or_nonempty
  · simp
  · exact hmono.memLp_of_measure_ne_top (hs.isLeast_sInf h) (hs.isGreatest_sSup h)
      hs.measure_lt_top.ne hs.measurableSet

set_option backward.isDefEq.respectTransparency.types false in
/-
**AntitoneOn.memLp_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.memLp_top (hanti : AntitoneOn f s) {a b : X} (ha : IsLeast s a)
 (hb : IsGreatest s b) (h's : MeasurableSet s) : MemLp f ∞ (μ.restrict s)
参数：hanti : AntitoneOn f s；ha : IsLeast s a；hb : IsGreatest s b；h's : MeasurableS
et s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.memLp_top`：MonotoneOn.memLp_top (hmono : MonotoneOn f s) {a b
 : X} (ha : IsLeast s a) (hb : IsGreatest s b) (h's : MeasurableSet s) : MemLp f
 ∞ (μ.rest…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instSecondCountableTopologyOrderDual`：∀ {α : Type u} [inst : Topological
Space α] [h : SecondCountableTopology α], SecondCountableTopology αᵒᵈ
-/
theorem AntitoneOn.memLp_top (hanti : AntitoneOn f s) {a b : X}
    (ha : IsLeast s a) (hb : IsGreatest s b) (h's : MeasurableSet s) :
    MemLp f ∞ (μ.restrict s) :=
  MonotoneOn.memLp_top (E := Eᵒᵈ) hanti ha hb h's

set_option backward.isDefEq.respectTransparency.types false in
/-
**AntitoneOn.memLp_of_measure_ne_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.memLp_of_measure_ne_top (hanti : AntitoneOn f s) {a b : X} (ha 
: IsLeast s a) (hb : IsGreatest s b) (hs : μ s != ∞) (h's : MeasurableSet s) : M
emLp f p (μ.restrict s)
参数：hanti : AntitoneOn f s；ha : IsLeast s a；hb : IsGreatest s b；hs : μ s != ∞；h's
 : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.memLp_of_measure_ne_top`：MonotoneOn.memLp_of_measure_ne_top (
hmono : MonotoneOn f s) {a b : X} (ha : IsLeast s a) (hb : IsGreatest s b) (hs :
 μ s != ∞) (h's : Measur…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instSecondCountableTopologyOrderDual`：∀ {α : Type u} [inst : Topological
Space α] [h : SecondCountableTopology α], SecondCountableTopology αᵒᵈ
-/
theorem AntitoneOn.memLp_of_measure_ne_top (hanti : AntitoneOn f s) {a b : X}
    (ha : IsLeast s a) (hb : IsGreatest s b) (hs : μ s ≠ ∞) (h's : MeasurableSet s) :
    MemLp f p (μ.restrict s) :=
  MonotoneOn.memLp_of_measure_ne_top (E := Eᵒᵈ) hanti ha hb hs h's

set_option backward.isDefEq.respectTransparency.types false in
/-
**AntitoneOn.memLp_isCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.memLp_isCompact [IsFiniteMeasureOnCompacts μ] (hs : IsCompact s
) (hanti : AntitoneOn f s) : MemLp f p (μ.restrict s)
参数：hs : IsCompact s；hanti : AntitoneOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.memLp_isCompact`：MonotoneOn.memLp_isCompact [IsFiniteMeasureO
nCompacts μ] (hs : IsCompact s) (hmono : MonotoneOn f s) : MemLp f p (μ.restrict
 s)
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instSecondCountableTopologyOrderDual`：∀ {α : Type u} [inst : Topological
Space α] [h : SecondCountableTopology α], SecondCountableTopology αᵒᵈ
-/
theorem AntitoneOn.memLp_isCompact [IsFiniteMeasureOnCompacts μ] (hs : IsCompact s)
    (hanti : AntitoneOn f s) : MemLp f p (μ.restrict s) :=
  MonotoneOn.memLp_isCompact (E := Eᵒᵈ) hs hanti
/-
**MonotoneOn.integrableOn_of_measure_ne_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.integrableOn_of_measure_ne_top (hmono : MonotoneOn f s) {a b : 
X} (ha : IsLeast s a) (hb : IsGreatest s b) (hs : μ s != ∞) (h's : MeasurableSet
 s) : IntegrableOn f s μ
参数：hmono : MonotoneOn f s；ha : IsLeast s a；hb : IsGreatest s b；hs : μ s != ∞；h's
 : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MonotoneOn.memLp_of_measure_ne_top`：MonotoneOn.memLp_of_measure_ne_top (
hmono : MonotoneOn f s) {a b : X} (ha : IsLeast s a) (hb : IsGreatest s b) (hs :
 μ s != ∞) (h's : Measur…
-/
theorem MonotoneOn.integrableOn_of_measure_ne_top (hmono : MonotoneOn f s) {a b : X}
    (ha : IsLeast s a) (hb : IsGreatest s b) (hs : μ s ≠ ∞) (h's : MeasurableSet s) :
    IntegrableOn f s μ :=
  memLp_one_iff_integrable.1 (hmono.memLp_of_measure_ne_top ha hb hs h's)
/-
**MonotoneOn.integrableOn_isCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.integrableOn_isCompact [IsFiniteMeasureOnCompacts μ] (hs : IsCo
mpact s) (hmono : MonotoneOn f s) : IntegrableOn f s μ
参数：hs : IsCompact s；hmono : MonotoneOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MonotoneOn.memLp_isCompact`：MonotoneOn.memLp_isCompact [IsFiniteMeasureO
nCompacts μ] (hs : IsCompact s) (hmono : MonotoneOn f s) : MemLp f p (μ.restrict
 s)
-/
theorem MonotoneOn.integrableOn_isCompact [IsFiniteMeasureOnCompacts μ] (hs : IsCompact s)
    (hmono : MonotoneOn f s) : IntegrableOn f s μ :=
  memLp_one_iff_integrable.1 (hmono.memLp_isCompact hs)
/-
**AntitoneOn.integrableOn_of_measure_ne_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.integrableOn_of_measure_ne_top (hanti : AntitoneOn f s) {a b : 
X} (ha : IsLeast s a) (hb : IsGreatest s b) (hs : μ s != ∞) (h's : MeasurableSet
 s) : IntegrableOn f s μ
参数：hanti : AntitoneOn f s；ha : IsLeast s a；hb : IsGreatest s b；hs : μ s != ∞；h's
 : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `AntitoneOn.memLp_of_measure_ne_top`：AntitoneOn.memLp_of_measure_ne_top (
hanti : AntitoneOn f s) {a b : X} (ha : IsLeast s a) (hb : IsGreatest s b) (hs :
 μ s != ∞) (h's : Measur…
-/
theorem AntitoneOn.integrableOn_of_measure_ne_top (hanti : AntitoneOn f s) {a b : X}
    (ha : IsLeast s a) (hb : IsGreatest s b) (hs : μ s ≠ ∞) (h's : MeasurableSet s) :
    IntegrableOn f s μ :=
  memLp_one_iff_integrable.1 (hanti.memLp_of_measure_ne_top ha hb hs h's)
/-
**AntitoneOn.integrableOn_isCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.integrableOn_isCompact [IsFiniteMeasureOnCompacts μ] (hs : IsCo
mpact s) (hanti : AntitoneOn f s) : IntegrableOn f s μ
参数：hs : IsCompact s；hanti : AntitoneOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `AntitoneOn.memLp_isCompact`：AntitoneOn.memLp_isCompact [IsFiniteMeasureO
nCompacts μ] (hs : IsCompact s) (hanti : AntitoneOn f s) : MemLp f p (μ.restrict
 s)
-/
theorem AntitoneOn.integrableOn_isCompact [IsFiniteMeasureOnCompacts μ] (hs : IsCompact s)
    (hanti : AntitoneOn f s) : IntegrableOn f s μ :=
  memLp_one_iff_integrable.1 (hanti.memLp_isCompact hs)
/-
**Monotone.locallyIntegrable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.locallyIntegrable [IsLocallyFiniteMeasure μ] (hmono : Monotone f)
 : LocallyIntegrable f μ
参数：hmono : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.finiteAt_nhds`：∀ {α : Type u_1} {m0 : MeasurableSp
ace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure α)   [MeasureTheor
y.IsLocallyFiniteMeasure …
· 使用定理 `exists_Icc_mem_subset_of_mem_nhds`：exists_Icc_mem_subset_of_mem_nhds {a 
: α} {s : Set α} (hs : s in 𝓝 a) : exists b c, a in Icc b c ∧ Icc b c in 𝓝 a ∧ I
cc b c subseteq s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MonotoneOn.integrableOn_of_measure_ne_top`：MonotoneOn.integrableOn_of_me
asure_ne_top (hmono : MonotoneOn f s) {a b : X} (ha : IsLeast s a) (hb : IsGreat
est s b) (hs : μ s != ∞) (h's :…
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s
· 使用定理 `isLeast_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b ≤ a → IsL
east (Set.Icc b a) b
· 使用定理 `isGreatest_Icc`：isGreatest_Icc (h : a <= b) : IsGreatest (Icc a b) b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `measurableSet_Icc`：measurableSet_Icc [OrderClosedTopology α] : Measurabl
eSet (Icc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
-/
theorem Monotone.locallyIntegrable [IsLocallyFiniteMeasure μ] (hmono : Monotone f) :
    LocallyIntegrable f μ := by
  intro x
  rcases μ.finiteAt_nhds x with ⟨U, hU, h'U⟩
  obtain ⟨a, b, xab, hab, abU⟩ : ∃ a b : X, x ∈ Icc a b ∧ Icc a b ∈ 𝓝 x ∧ Icc a b ⊆ U :=
    exists_Icc_mem_subset_of_mem_nhds hU
  have ab : a ≤ b := xab.1.trans xab.2
  refine ⟨Icc a b, hab, ?_⟩
  exact
    (hmono.monotoneOn _).integrableOn_of_measure_ne_top (isLeast_Icc ab) (isGreatest_Icc ab)
      ((measure_mono abU).trans_lt h'U).ne measurableSet_Icc

set_option backward.isDefEq.respectTransparency.types false in
/-
**Antitone.locallyIntegrable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.locallyIntegrable [IsLocallyFiniteMeasure μ] (hanti : Antitone f)
 : LocallyIntegrable f μ
参数：hanti : Antitone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.locallyIntegrable`：Monotone.locallyIntegrable [IsLocallyFiniteM
easure μ] (hmono : Monotone f) : LocallyIntegrable f μ
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instSecondCountableTopologyOrderDual`：∀ {α : Type u} [inst : Topological
Space α] [h : SecondCountableTopology α], SecondCountableTopology αᵒᵈ
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)
-/
theorem Antitone.locallyIntegrable [IsLocallyFiniteMeasure μ] (hanti : Antitone f) :
    LocallyIntegrable f μ :=
  hanti.dual_right.locallyIntegrable

end Monotone

namespace MeasureTheory

variable [OpensMeasurableSpace X] {A K : Set X}

section Mul

variable [NormedRing R] [SecondCountableTopologyEither X R] {g g' : X → R}

/-
**MeasureTheory.IntegrableOn.mul_continuousOn_of_subset** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.IntegrableOn`。
形式化陈述：∀ {X : Type u_1} {R : Type u_8} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] {μ : MeasureTheory.Measure X}   [OpensMeasurableSpace X] {A K : S
et X} [inst_3 : NormedRing R] [SecondCountableTopologyEither X R] {g g' : X → R}
,   MeasureTheory.IntegrableOn g A μ →     ContinuousOn g' K → MeasurableSet A →
 IsCompact K → A ⊆ K → MeasureTheory.IntegrableOn (fun x => g x * g' x) A μ
参数：fun x => g x * g' x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.exists_bound_of_continuousOn`：∀ {α : Type u_1} {E : Type u_2} 
[inst : SeminormedAddGroup E] [inst_1 : TopologicalSpace α] {s : Set α},   IsCom
pact s → ∀ {f : α → E}, Cont…
· 使用定理 `MeasureTheory.Integrable.mul_bdd`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜]   {f g : α
 → 𝕜} {c : ℝ},   Measu…
· 使用定理 `ContinuousOn.aestronglyMeasurable`：ContinuousOn.aestronglyMeasurable [To
pologicalSpace α] [TopologicalSpace β] [h : SecondCountableTopologyEither α β] [
OpensMeasurableSpace α]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `MeasureTheory.ae_restrict_of_forall_mem`：ae_restrict_of_forall_mem {μ : 
Measure α} {s : Set α} (hs : MeasurableSet s) {p : α -> Prop} (h : forall x in s
, p x) : forallᵐ (x : α) ∂μ.r…
-/
theorem IntegrableOn.mul_continuousOn_of_subset (hg : IntegrableOn g A μ) (hg' : ContinuousOn g' K)
    (hA : MeasurableSet A) (hK : IsCompact K) (hAK : A ⊆ K) :
    IntegrableOn (fun x => g x * g' x) A μ := by
  rcases IsCompact.exists_bound_of_continuousOn hK hg' with ⟨C, hC⟩
  exact hg.mul_bdd ((hg'.mono hAK).aestronglyMeasurable hA)
    (ae_restrict_of_forall_mem hA fun x hx => hC x (hAK hx))
/-
**MeasureTheory.IntegrableOn.mul_continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.IntegrableOn`。
形式化陈述：∀ {X : Type u_1} {R : Type u_8} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] {μ : MeasureTheory.Measure X}   [OpensMeasurableSpace X] {K : Set
 X} [inst_3 : NormedRing R] [SecondCountableTopologyEither X R] {g g' : X → R}  
 [T2Space X],   MeasureTheory.IntegrableOn g K μ →     ContinuousOn g' K → IsCom
pact K → MeasureTheory.IntegrableOn (fun x => g x * g' x) K μ
参数：fun x => g x * g' x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableOn.mul_continuousOn_of_subset`：∀ {X : Type u_1} 
{R : Type u_8} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] {μ : Mea
sureTheory.Measure X}   [OpensMeasurableSpa…
· 使用定理 `IsCompact.measurableSet`：IsCompact.measurableSet [T2Space α] (h : IsComp
act s) : MeasurableSet s
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
-/
theorem IntegrableOn.mul_continuousOn [T2Space X] (hg : IntegrableOn g K μ)
    (hg' : ContinuousOn g' K) (hK : IsCompact K) : IntegrableOn (fun x => g x * g' x) K μ :=
  hg.mul_continuousOn_of_subset hg' hK.measurableSet hK (Subset.refl _)
/-
**MeasureTheory.IntegrableOn.continuousOn_mul_of_subset** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.IntegrableOn`。
形式化陈述：∀ {X : Type u_1} {R : Type u_8} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] {μ : MeasureTheory.Measure X}   [OpensMeasurableSpace X] {A K : S
et X} [inst_3 : NormedRing R] [SecondCountableTopologyEither X R] {g g' : X → R}
,   ContinuousOn g K →     MeasureTheory.IntegrableOn g' A μ →       IsCompact K
 → MeasurableSet A → A ⊆ K → MeasureTheory.IntegrableOn (fun x => g x * g' x) A 
μ
参数：fun x => g x * g' x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.exists_bound_of_continuousOn`：∀ {α : Type u_1} {E : Type u_2} 
[inst : SeminormedAddGroup E] [inst_1 : TopologicalSpace α] {s : Set α},   IsCom
pact s → ∀ {f : α → E}, Cont…
· 使用定理 `MeasureTheory.Integrable.bdd_mul`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜]   {f g : α
 → 𝕜} {c : ℝ},   Measu…
· 使用定理 `ContinuousOn.aestronglyMeasurable`：ContinuousOn.aestronglyMeasurable [To
pologicalSpace α] [TopologicalSpace β] [h : SecondCountableTopologyEither α β] [
OpensMeasurableSpace α]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `MeasureTheory.ae_restrict_of_forall_mem`：ae_restrict_of_forall_mem {μ : 
Measure α} {s : Set α} (hs : MeasurableSet s) {p : α -> Prop} (h : forall x in s
, p x) : forallᵐ (x : α) ∂μ.r…
-/
theorem IntegrableOn.continuousOn_mul_of_subset (hg : ContinuousOn g K) (hg' : IntegrableOn g' A μ)
    (hK : IsCompact K) (hA : MeasurableSet A) (hAK : A ⊆ K) :
    IntegrableOn (fun x => g x * g' x) A μ := by
  rcases IsCompact.exists_bound_of_continuousOn hK hg with ⟨C, hC⟩
  exact hg'.bdd_mul ((hg.mono hAK).aestronglyMeasurable hA)
    (ae_restrict_of_forall_mem hA fun x hx => hC x (hAK hx))
/-
**MeasureTheory.IntegrableOn.continuousOn_mul** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.IntegrableOn`。
形式化陈述：∀ {X : Type u_1} {R : Type u_8} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] {μ : MeasureTheory.Measure X}   [OpensMeasurableSpace X] {K : Set
 X} [inst_3 : NormedRing R] [SecondCountableTopologyEither X R] {g g' : X → R}  
 [T2Space X],   ContinuousOn g K →     MeasureTheory.IntegrableOn g' K μ → IsCom
pact K → MeasureTheory.IntegrableOn (fun x => g x * g' x) K μ
参数：fun x => g x * g' x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableOn.continuousOn_mul_of_subset`：∀ {X : Type u_1} 
{R : Type u_8} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] {μ : Mea
sureTheory.Measure X}   [OpensMeasurableSpa…
· 使用定理 `IsCompact.measurableSet`：IsCompact.measurableSet [T2Space α] (h : IsComp
act s) : MeasurableSet s
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem IntegrableOn.continuousOn_mul [T2Space X] (hg : ContinuousOn g K)
    (hg' : IntegrableOn g' K μ) (hK : IsCompact K) : IntegrableOn (fun x => g x * g' x) K μ :=
  hg'.continuousOn_mul_of_subset hg hK hK.measurableSet Subset.rfl

end Mul

section SMul

variable {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-
**MeasureTheory.IntegrableOn.continuousOn_smul_of_subset** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.IntegrableOn`。
形式化陈述：∀ {X : Type u_1} {E : Type u_6} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : NormedAddCommGroup E]   {μ : MeasureTheory.Measure X} [
OpensMeasurableSpace X] {A K : Set X} {𝕜 : Type u_9} [inst_4 : NormedRing 𝕜]   [
inst_5 : _root_.Module 𝕜 E] [IsBoundedSMul 𝕜 E] [SecondCountableTopologyEither X
 𝕜] {f : X → 𝕜},   ContinuousOn f K →     ∀ {g : X → E},       MeasureTheory.Int
egrableOn g A μ →         IsCompact K → MeasurableSet A → A ⊆ K → MeasureTheory.
IntegrableOn (fun x => f x • g x) A μ
参数：fun x => f x • g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.exists_bound_of_continuousOn`：∀ {α : Type u_1} {E : Type u_2} 
[inst : SeminormedAddGroup E] [inst_1 : TopologicalSpace α] {s : Set α},   IsCom
pact s → ∀ {f : α → E}, Cont…
· 使用定理 `MeasureTheory.Integrable.bdd_smul`：∀ {α : Type u_1} {β : Type u_2} {m : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]  
 {𝕜 : Type u_8} [inst_1…
· 使用定理 `ContinuousOn.aestronglyMeasurable`：ContinuousOn.aestronglyMeasurable [To
pologicalSpace α] [TopologicalSpace β] [h : SecondCountableTopologyEither α β] [
OpensMeasurableSpace α]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `MeasureTheory.ae_restrict_of_forall_mem`：ae_restrict_of_forall_mem {μ : 
Measure α} {s : Set α} (hs : MeasurableSet s) {p : α -> Prop} (h : forall x in s
, p x) : forallᵐ (x : α) ∂μ.r…
-/
theorem IntegrableOn.continuousOn_smul_of_subset [SecondCountableTopologyEither X 𝕜] {f : X → 𝕜}
    (hf : ContinuousOn f K) {g : X → E} (hg : IntegrableOn g A μ)
    (hK : IsCompact K) (hA : MeasurableSet A) (hAK : A ⊆ K) :
    IntegrableOn (fun x => f x • g x) A μ := by
  rcases IsCompact.exists_bound_of_continuousOn hK hf with ⟨C, hC⟩
  exact hg.bdd_smul C ((hf.mono hAK).aestronglyMeasurable hA)
    (ae_restrict_of_forall_mem hA fun x hx => hC x (hAK hx))
/-
**MeasureTheory.IntegrableOn.continuousOn_smul** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.IntegrableOn`。
形式化陈述：∀ {X : Type u_1} {E : Type u_6} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : NormedAddCommGroup E]   {μ : MeasureTheory.Measure X} [
OpensMeasurableSpace X] {K : Set X} {𝕜 : Type u_9} [inst_4 : NormedRing 𝕜]   [in
st_5 : _root_.Module 𝕜 E] [IsBoundedSMul 𝕜 E] [T2Space X] [SecondCountableTopolo
gyEither X 𝕜] {g : X → E},   MeasureTheory.IntegrableOn g K μ →     ∀ {f : X → 𝕜
}, ContinuousOn f K → IsCompact K → MeasureTheory.IntegrableOn (fun x => f x • g
 x) K μ
参数：fun x => f x • g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableOn.continuousOn_smul_of_subset`：∀ {X : Type u_1}
 {E : Type u_6} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2
 : NormedAddCommGroup E]   {μ : MeasureTheor…
· 使用定理 `IsCompact.measurableSet`：IsCompact.measurableSet [T2Space α] (h : IsComp
act s) : MeasurableSet s
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem IntegrableOn.continuousOn_smul [T2Space X] [SecondCountableTopologyEither X 𝕜] {g : X → E}
    (hg : IntegrableOn g K μ) {f : X → 𝕜} (hf : ContinuousOn f K) (hK : IsCompact K) :
    IntegrableOn (fun x => f x • g x) K μ :=
  hg.continuousOn_smul_of_subset hf hK hK.measurableSet Subset.rfl
/-
**MeasureTheory.IntegrableOn.smul_continuousOn_of_subset** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.IntegrableOn`。
形式化陈述：∀ {X : Type u_1} {E : Type u_6} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : NormedAddCommGroup E]   {μ : MeasureTheory.Measure X} [
OpensMeasurableSpace X] {A K : Set X} {𝕜 : Type u_9} [inst_4 : NormedRing 𝕜]   [
inst_5 : _root_.Module 𝕜 E] [IsBoundedSMul 𝕜 E] [SecondCountableTopologyEither X
 E] {f : X → 𝕜},   MeasureTheory.IntegrableOn f A μ →     ∀ {g : X → E},       C
ontinuousOn g K → MeasurableSet A → IsCompact K → A ⊆ K → MeasureTheory.Integrab
leOn (fun x => f x • g x) A μ
参数：fun x => f x • g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.exists_bound_of_continuousOn`：∀ {α : Type u_1} {E : Type u_2} 
[inst : SeminormedAddGroup E] [inst_1 : TopologicalSpace α] {s : Set α},   IsCom
pact s → ∀ {f : α → E}, Cont…
· 使用定理 `MeasureTheory.Integrable.smul_bdd`：∀ {α : Type u_1} {β : Type u_2} {m : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]  
 {𝕜 : Type u_8} [inst_1…
· 使用定理 `ContinuousOn.aestronglyMeasurable`：ContinuousOn.aestronglyMeasurable [To
pologicalSpace α] [TopologicalSpace β] [h : SecondCountableTopologyEither α β] [
OpensMeasurableSpace α]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `MeasureTheory.ae_restrict_of_forall_mem`：ae_restrict_of_forall_mem {μ : 
Measure α} {s : Set α} (hs : MeasurableSet s) {p : α -> Prop} (h : forall x in s
, p x) : forallᵐ (x : α) ∂μ.r…
-/
theorem IntegrableOn.smul_continuousOn_of_subset [SecondCountableTopologyEither X E] {f : X → 𝕜}
    (hf : IntegrableOn f A μ) {g : X → E} (hg : ContinuousOn g K)
    (hA : MeasurableSet A) (hK : IsCompact K) (hAK : A ⊆ K) :
    IntegrableOn (fun x => f x • g x) A μ := by
  rcases IsCompact.exists_bound_of_continuousOn hK hg with ⟨C, hC⟩
  exact hf.smul_bdd C ((hg.mono hAK).aestronglyMeasurable hA)
    (ae_restrict_of_forall_mem hA fun x hx => hC x (hAK hx))
/-
**MeasureTheory.IntegrableOn.smul_continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.IntegrableOn`。
形式化陈述：∀ {X : Type u_1} {E : Type u_6} [inst : MeasurableSpace X] [inst_1 : Topol
ogicalSpace X] [inst_2 : NormedAddCommGroup E]   {μ : MeasureTheory.Measure X} [
OpensMeasurableSpace X] {K : Set X} {𝕜 : Type u_9} [inst_4 : NormedRing 𝕜]   [in
st_5 : _root_.Module 𝕜 E] [IsBoundedSMul 𝕜 E] [T2Space X] [SecondCountableTopolo
gyEither X E] {f : X → 𝕜},   MeasureTheory.IntegrableOn f K μ →     ∀ {g : X → E
}, ContinuousOn g K → IsCompact K → MeasureTheory.IntegrableOn (fun x => f x • g
 x) K μ
参数：fun x => f x • g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableOn.smul_continuousOn_of_subset`：∀ {X : Type u_1}
 {E : Type u_6} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2
 : NormedAddCommGroup E]   {μ : MeasureTheor…
· 使用定理 `IsCompact.measurableSet`：IsCompact.measurableSet [T2Space α] (h : IsComp
act s) : MeasurableSet s
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
-/
theorem IntegrableOn.smul_continuousOn [T2Space X] [SecondCountableTopologyEither X E] {f : X → 𝕜}
    (hf : IntegrableOn f K μ) {g : X → E} (hg : ContinuousOn g K) (hK : IsCompact K) :
    IntegrableOn (fun x => f x • g x) K μ :=
  hf.smul_continuousOn_of_subset hg hK.measurableSet hK (Subset.refl _)

end SMul

namespace LocallyIntegrableOn

/-
**MeasureTheory.LocallyIntegrableOn.continuousOn_mul** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.LocallyIntegrableOn`。
形式化陈述：continuousOn_mul [LocallyCompactSpace X] [T2Space X] [NormedRing R] [Secon
dCountableTopologyEither X R] {f g : X -> R} {s : Set X} (hf : LocallyIntegrable
On f s μ) (hg : ContinuousOn g s) (hs : IsLocallyClosed s) : LocallyIntegrableOn
 (fun x => g x * f x) s μ
参数：hf : LocallyIntegrableOn f s μ；hg : ContinuousOn g s；hs : IsLocallyClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.locallyIntegrableOn_iff`：locallyIntegrableOn_iff [PseudoMe
trizableSpace ε] [LocallyCompactSpace X] (hs : IsLocallyClosed s) : LocallyInteg
rableOn f s μ ↔ forall (k :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.IntegrableOn.continuousOn_mul`：∀ {X : Type u_1} {R : Type 
u_8} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] {μ : MeasureTheory
.Measure X}   [OpensMeasurableSpa…
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
-/
theorem continuousOn_mul [LocallyCompactSpace X] [T2Space X] [NormedRing R]
    [SecondCountableTopologyEither X R] {f g : X → R} {s : Set X} (hf : LocallyIntegrableOn f s μ)
    (hg : ContinuousOn g s) (hs : IsLocallyClosed s) :
    LocallyIntegrableOn (fun x => g x * f x) s μ := by
  rw [MeasureTheory.locallyIntegrableOn_iff hs] at hf ⊢
  exact fun k hk_sub hk_c => (hf k hk_sub hk_c).continuousOn_mul (hg.mono hk_sub) hk_c
/-
**MeasureTheory.LocallyIntegrableOn.mul_continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.LocallyIntegrableOn`。
形式化陈述：mul_continuousOn [LocallyCompactSpace X] [T2Space X] [NormedRing R] [Secon
dCountableTopologyEither X R] {f g : X -> R} {s : Set X} (hf : LocallyIntegrable
On f s μ) (hg : ContinuousOn g s) (hs : IsLocallyClosed s) : LocallyIntegrableOn
 (fun x => f x * g x) s μ
参数：hf : LocallyIntegrableOn f s μ；hg : ContinuousOn g s；hs : IsLocallyClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.locallyIntegrableOn_iff`：locallyIntegrableOn_iff [PseudoMe
trizableSpace ε] [LocallyCompactSpace X] (hs : IsLocallyClosed s) : LocallyInteg
rableOn f s μ ↔ forall (k :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.IntegrableOn.mul_continuousOn`：∀ {X : Type u_1} {R : Type 
u_8} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] {μ : MeasureTheory
.Measure X}   [OpensMeasurableSpa…
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
-/
theorem mul_continuousOn [LocallyCompactSpace X] [T2Space X] [NormedRing R]
    [SecondCountableTopologyEither X R] {f g : X → R} {s : Set X} (hf : LocallyIntegrableOn f s μ)
    (hg : ContinuousOn g s) (hs : IsLocallyClosed s) :
    LocallyIntegrableOn (fun x => f x * g x) s μ := by
  rw [MeasureTheory.locallyIntegrableOn_iff hs] at hf ⊢
  exact fun k hk_sub hk_c => (hf k hk_sub hk_c).mul_continuousOn (hg.mono hk_sub) hk_c
/-
**MeasureTheory.LocallyIntegrableOn.continuousOn_smul** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.LocallyIntegrableOn`。
形式化陈述：continuousOn_smul [LocallyCompactSpace X] [T2Space X] {𝕜 : Type*} [NormedR
ing 𝕜] [SecondCountableTopologyEither X 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] {f :
 X -> E} {g : X -> 𝕜} {s : Set X} (hs : IsLocallyClosed s) (hf : LocallyIntegrab
leOn f s μ) (hg : ContinuousOn g s) : LocallyIntegrableOn (fun x => g x • f x) s
 μ
参数：hs : IsLocallyClosed s；hf : LocallyIntegrableOn f s μ；hg : ContinuousOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.locallyIntegrableOn_iff`：locallyIntegrableOn_iff [PseudoMe
trizableSpace ε] [LocallyCompactSpace X] (hs : IsLocallyClosed s) : LocallyInteg
rableOn f s μ ↔ forall (k :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.IntegrableOn.continuousOn_smul`：∀ {X : Type u_1} {E : Type
 u_6} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 : NormedA
ddCommGroup E]   {μ : MeasureTheor…
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
-/
theorem continuousOn_smul [LocallyCompactSpace X] [T2Space X] {𝕜 : Type*} [NormedRing 𝕜]
    [SecondCountableTopologyEither X 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] {f : X → E} {g : X → 𝕜}
    {s : Set X} (hs : IsLocallyClosed s) (hf : LocallyIntegrableOn f s μ) (hg : ContinuousOn g s) :
    LocallyIntegrableOn (fun x => g x • f x) s μ := by
  rw [MeasureTheory.locallyIntegrableOn_iff hs] at hf ⊢
  exact fun k hk_sub hk_c => (hf k hk_sub hk_c).continuousOn_smul (hg.mono hk_sub) hk_c
/-
**MeasureTheory.LocallyIntegrableOn.smul_continuousOn** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.LocallyIntegrableOn`。
形式化陈述：smul_continuousOn [LocallyCompactSpace X] [T2Space X] {𝕜 : Type*} [NormedR
ing 𝕜] [SecondCountableTopologyEither X E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] {f :
 X -> 𝕜} {g : X -> E} {s : Set X} (hs : IsLocallyClosed s) (hf : LocallyIntegrab
leOn f s μ) (hg : ContinuousOn g s) : LocallyIntegrableOn (fun x => f x • g x) s
 μ
参数：hs : IsLocallyClosed s；hf : LocallyIntegrableOn f s μ；hg : ContinuousOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.locallyIntegrableOn_iff`：locallyIntegrableOn_iff [PseudoMe
trizableSpace ε] [LocallyCompactSpace X] (hs : IsLocallyClosed s) : LocallyInteg
rableOn f s μ ↔ forall (k :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.IntegrableOn.smul_continuousOn`：∀ {X : Type u_1} {E : Type
 u_6} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 : NormedA
ddCommGroup E]   {μ : MeasureTheor…
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
-/
theorem smul_continuousOn [LocallyCompactSpace X] [T2Space X] {𝕜 : Type*} [NormedRing 𝕜]
    [SecondCountableTopologyEither X E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] {f : X → 𝕜} {g : X → E}
    {s : Set X} (hs : IsLocallyClosed s) (hf : LocallyIntegrableOn f s μ) (hg : ContinuousOn g s) :
    LocallyIntegrableOn (fun x => f x • g x) s μ := by
  rw [MeasureTheory.locallyIntegrableOn_iff hs] at hf ⊢
  exact fun k hk_sub hk_c => (hf k hk_sub hk_c).smul_continuousOn (hg.mono hk_sub) hk_c

end LocallyIntegrableOn

namespace LocallyIntegrable

variable [LocallyCompactSpace X] [T2Space X] [NormedRing R] [SecondCountableTopologyEither X R]
  {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E]

/-
**MeasureTheory.LocallyIntegrable.continuous_mul** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.LocallyIntegrable`。
形式化陈述：continuous_mul {f g : X -> R} (hg : Continuous g) (hf : LocallyIntegrable 
f μ) : LocallyIntegrable (fun x => g x * f x) μ
参数：hg : Continuous g；hf : LocallyIntegrable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.locallyIntegrableOn_univ`：locallyIntegrableOn_univ : Local
lyIntegrableOn f univ μ ↔ LocallyIntegrable f μ
· 使用定理 `MeasureTheory.LocallyIntegrableOn.continuousOn_mul`：continuousOn_mul [Lo
callyCompactSpace X] [T2Space X] [NormedRing R] [SecondCountableTopologyEither X
 R] {f g : X -> R} {s : Set X} (hf : Loc…
· 使用定理 `MeasureTheory.LocallyIntegrable.locallyIntegrableOn`：∀ {X : Type u_1} {ε
 : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 : 
TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用引理 `IsOpen.isLocallyClosed`：IsOpen.isLocallyClosed (hs : IsOpen s) : IsLocal
lyClosed s
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
-/
theorem continuous_mul {f g : X → R} (hg : Continuous g)
    (hf : LocallyIntegrable f μ) : LocallyIntegrable (fun x => g x * f x) μ :=
  locallyIntegrableOn_univ.1 ((hf.locallyIntegrableOn univ).continuousOn_mul
    hg.continuousOn isOpen_univ.isLocallyClosed)
/-
**MeasureTheory.LocallyIntegrable.mul_continuous** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.LocallyIntegrable`。
形式化陈述：mul_continuous {f g : X -> R} (hg : Continuous g) (hf : LocallyIntegrable 
f μ) : LocallyIntegrable (fun x => f x * g x) μ
参数：hg : Continuous g；hf : LocallyIntegrable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.locallyIntegrableOn_univ`：locallyIntegrableOn_univ : Local
lyIntegrableOn f univ μ ↔ LocallyIntegrable f μ
· 使用定理 `MeasureTheory.LocallyIntegrableOn.mul_continuousOn`：mul_continuousOn [Lo
callyCompactSpace X] [T2Space X] [NormedRing R] [SecondCountableTopologyEither X
 R] {f g : X -> R} {s : Set X} (hf : Loc…
· 使用定理 `MeasureTheory.LocallyIntegrable.locallyIntegrableOn`：∀ {X : Type u_1} {ε
 : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 : 
TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用引理 `IsOpen.isLocallyClosed`：IsOpen.isLocallyClosed (hs : IsOpen s) : IsLocal
lyClosed s
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
-/
theorem mul_continuous {f g : X → R} (hg : Continuous g)
    (hf : LocallyIntegrable f μ) : LocallyIntegrable (fun x => f x * g x) μ :=
  locallyIntegrableOn_univ.1 ((hf.locallyIntegrableOn univ).mul_continuousOn
    hg.continuousOn isOpen_univ.isLocallyClosed)
/-
**MeasureTheory.LocallyIntegrable.continuous_smul** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.LocallyIntegrable`。
形式化陈述：continuous_smul [SecondCountableTopologyEither X 𝕜] {f : X -> E} {g : X ->
 𝕜} (hg : Continuous g) (hf : LocallyIntegrable f μ) : LocallyIntegrable (fun x 
=> g x • f x) μ
参数：hg : Continuous g；hf : LocallyIntegrable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.locallyIntegrableOn_univ`：locallyIntegrableOn_univ : Local
lyIntegrableOn f univ μ ↔ LocallyIntegrable f μ
· 使用定理 `MeasureTheory.LocallyIntegrableOn.continuousOn_smul`：continuousOn_smul [
LocallyCompactSpace X] [T2Space X] {𝕜 : Type*} [NormedRing 𝕜] [SecondCountableTo
pologyEither X 𝕜] [Module 𝕜 E] [IsBounded…
· 使用引理 `IsOpen.isLocallyClosed`：IsOpen.isLocallyClosed (hs : IsOpen s) : IsLocal
lyClosed s
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `MeasureTheory.LocallyIntegrable.locallyIntegrableOn`：∀ {X : Type u_1} {ε
 : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 : 
TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
-/
theorem continuous_smul [SecondCountableTopologyEither X 𝕜] {f : X → E} {g : X → 𝕜}
    (hg : Continuous g) (hf : LocallyIntegrable f μ) : LocallyIntegrable (fun x => g x • f x) μ :=
  locallyIntegrableOn_univ.1 ((hf.locallyIntegrableOn univ).continuousOn_smul
    isOpen_univ.isLocallyClosed hg.continuousOn)
/-
**MeasureTheory.LocallyIntegrable.smul_continuous** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.LocallyIntegrable`。
形式化陈述：smul_continuous [SecondCountableTopologyEither X E] {f : X -> 𝕜} {g : X ->
 E} (hg : Continuous g) (hf : LocallyIntegrable f μ) : LocallyIntegrable (fun x 
=> f x • g x) μ
参数：hg : Continuous g；hf : LocallyIntegrable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.locallyIntegrableOn_univ`：locallyIntegrableOn_univ : Local
lyIntegrableOn f univ μ ↔ LocallyIntegrable f μ
· 使用定理 `MeasureTheory.LocallyIntegrableOn.smul_continuousOn`：smul_continuousOn [
LocallyCompactSpace X] [T2Space X] {𝕜 : Type*} [NormedRing 𝕜] [SecondCountableTo
pologyEither X E] [Module 𝕜 E] [IsBounded…
· 使用引理 `IsOpen.isLocallyClosed`：IsOpen.isLocallyClosed (hs : IsOpen s) : IsLocal
lyClosed s
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `MeasureTheory.LocallyIntegrable.locallyIntegrableOn`：∀ {X : Type u_1} {ε
 : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 : 
TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
-/
theorem smul_continuous [SecondCountableTopologyEither X E] {f : X → 𝕜} {g : X → E}
    (hg : Continuous g) (hf : LocallyIntegrable f μ) : LocallyIntegrable (fun x => f x • g x) μ :=
  locallyIntegrableOn_univ.1 ((hf.locallyIntegrableOn univ).smul_continuousOn
    isOpen_univ.isLocallyClosed hg.continuousOn)

end LocallyIntegrable

end MeasureTheory

