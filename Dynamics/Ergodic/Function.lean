/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Function.AEEqFun

/-!
# Functions invariant under a (quasi)ergodic map

In this file we prove that an a.e. strongly measurable function `g : α → X`
that is a.e. invariant under a (quasi)ergodic map is a.e. equal to a constant.
We prove several versions of this statement with slightly different measurability assumptions.
We also formulate a version for `MeasureTheory.AEEqFun` functions
with all a.e. equalities replaced with equalities in the quotient space.
-/

public section

open Function Set Filter MeasureTheory Topology TopologicalSpace

variable {α X : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}

/-- Let `f : α → α` be a (quasi)ergodic map. Let `g : α → X` be a null-measurable function
from `α` to a nonempty space with a countable family of measurable sets
separating points of a set `s` such that `g x ∈ s` for a.e. `x`.
If `g` is a.e.-invariant under `f`, then `g` is a.e. constant. -/
/-
**QuasiErgodic.ae_eq_const_of_ae_eq_comp_of_ae_range** 是 Mathlib 中的一个定理，位于命名空间 `
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `f : α → α` be a (quasi)ergodic map. Let `g : α → X` be a null-measurable fu
nction
from `α` to a nonempty space with a countable family of measurable sets
separating points of a set `s` such that `g x ∈ s` for a.e. `x`.
If `g` is a.e.-invariant under `f`, then `g` is a.e. constant.
-/
theorem QuasiErgodic.ae_eq_const_of_ae_eq_comp_of_ae_range₀ [Nonempty X] [MeasurableSpace X]
    {s : Set X} [MeasurableSpace.CountablySeparated s] {f : α → α} {g : α → X}
    (h : QuasiErgodic f μ) (hs : ∀ᵐ x ∂μ, g x ∈ s) (hgm : NullMeasurable g μ)
    (hg_eq : g ∘ f =ᵐ[μ] g) :
    ∃ c, g =ᵐ[μ] const α c := by
  refine exists_eventuallyEq_const_of_eventually_mem_of_forall_separating MeasurableSet hs ?_
  refine fun U hU ↦ h.ae_mem_or_ae_notMem₀ (s := g ⁻¹' U) (hgm hU) ?_b
  refine (hg_eq.mono fun x hx ↦ ?_).set_eq
  rw [← preimage_comp, mem_preimage, mem_preimage, hx]

section CountableSeparatingOnUniv

variable [Nonempty X] [MeasurableSpace X] [MeasurableSpace.CountablySeparated X]
  {f : α → α} {g : α → X}

/-- Let `f : α → α` be a (pre)ergodic map.
Let `g : α → X` be a measurable function from `α` to a nonempty measurable space
with a countable family of measurable sets separating the points of `X`.
If `g` is invariant under `f`, then `g` is a.e. constant. -/
/-
**PreErgodic.ae_eq_const_of_ae_eq_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PreErgodic.ae_eq_const_of_ae_eq_comp (h : PreErgodic f μ) (hgm : Measurabl
e g) (hg_eq : g ∘ f = g) : exists c, g =ᵐ[μ] const α c
参数：h : PreErgodic f μ；hgm : Measurable g；hg_eq : g ∘ f = g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.exists_eventuallyEq_const_of_forall_separating`：exists_eventually
Eq_const_of_forall_separating [Nonempty β] (p : Set β -> Prop) [HasCountableSepa
ratingOn β p univ] (h : forall U, p U -> (f…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.instCountableInterFilterAe`：∀ {α : Type u_1} {F : Type u_2
} [inst : FunLike F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F
 α]   (μ : F), CountableInterF…
· 使用定理 `PreErgodic.ae_mem_or_ae_notMem`：ae_mem_or_ae_notMem (hf : PreErgodic f μ
) (hsm : MeasurableSet s) (hs : f ⁻¹' s = s) : (forallᵐ x ∂μ, x in s) ∨ forallᵐ 
x ∂μ, x ∉ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s

--- 原说明 ---
Let `f : α → α` be a (pre)ergodic map.
Let `g : α → X` be a measurable function from `α` to a nonempty measurable space
with a countable family of measurable sets separating the points of `X`.
If `g` is invariant under `f`, then `g` is a.e. constant.
-/
theorem PreErgodic.ae_eq_const_of_ae_eq_comp (h : PreErgodic f μ) (hgm : Measurable g)
    (hg_eq : g ∘ f = g) : ∃ c, g =ᵐ[μ] const α c :=
  exists_eventuallyEq_const_of_forall_separating MeasurableSet fun U hU ↦
    h.ae_mem_or_ae_notMem (s := g ⁻¹' U) (hgm hU) <| by rw [← preimage_comp, hg_eq]

/-- Let `f : α → α` be a quasi-ergodic map.
Let `g : α → X` be a null-measurable function from `α` to a nonempty measurable space
with a countable family of measurable sets separating the points of `X`.
If `g` is a.e.-invariant under `f`, then `g` is a.e. constant. -/
/-
**QuasiErgodic.ae_eq_const_of_ae_eq_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `f : α → α` be a quasi-ergodic map.
Let `g : α → X` be a null-measurable function from `α` to a nonempty measurable 
space
with a countable family of measurable sets separating the points of `X`.
If `g` is a.e.-invariant under `f`, then `g` is a.e. constant.
-/
theorem QuasiErgodic.ae_eq_const_of_ae_eq_comp₀ (h : QuasiErgodic f μ) (hgm : NullMeasurable g μ)
    (hg_eq : g ∘ f =ᵐ[μ] g) : ∃ c, g =ᵐ[μ] const α c :=
  h.ae_eq_const_of_ae_eq_comp_of_ae_range₀ (s := univ) univ_mem hgm hg_eq

/-- Let `f : α → α` be an ergodic map.
Let `g : α → X` be a null-measurable function from `α` to a nonempty measurable space
with a countable family of measurable sets separating the points of `X`.
If `g` is a.e.-invariant under `f`, then `g` is a.e. constant. -/
/-
**Ergodic.ae_eq_const_of_ae_eq_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `f : α → α` be an ergodic map.
Let `g : α → X` be a null-measurable function from `α` to a nonempty measurable 
space
with a countable family of measurable sets separating the points of `X`.
If `g` is a.e.-invariant under `f`, then `g` is a.e. constant.
-/
theorem Ergodic.ae_eq_const_of_ae_eq_comp₀ (h : Ergodic f μ) (hgm : NullMeasurable g μ)
    (hg_eq : g ∘ f =ᵐ[μ] g) : ∃ c, g =ᵐ[μ] const α c :=
  h.quasiErgodic.ae_eq_const_of_ae_eq_comp₀ hgm hg_eq

end CountableSeparatingOnUniv

variable [TopologicalSpace X] [MetrizableSpace X] [Nonempty X] {f : α → α}

namespace QuasiErgodic

/-- Let `f : α → α` be a quasi-ergodic map.
Let `g : α → X` be an a.e. strongly measurable function
from `α` to a nonempty metrizable topological space.
If `g` is a.e.-invariant under `f`, then `g` is a.e. constant. -/
/-
**QuasiErgodic.ae_eq_const_of_ae_eq_comp_ae** 是 Mathlib 中的一个定理，位于命名空间 `QuasiErgo
dic`。
形式化陈述：ae_eq_const_of_ae_eq_comp_ae {g : α -> X} (h : QuasiErgodic f μ) (hgm : AE
StronglyMeasurable g μ) (hg_eq : g ∘ f =ᵐ[μ] g) : exists c, g =ᵐ[μ] const α c
参数：h : QuasiErgodic f μ；hgm : AEStronglyMeasurable g μ；hg_eq : g ∘ f =ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEStronglyMeasurable.isSeparable_ae_range`：isSeparable_ae_
range (hf : AEStronglyMeasurable f μ) : exists t : Set β, IsSeparable t ∧ forall
ᵐ x ∂μ, f x in t
· 使用定理 `TopologicalSpace.IsSeparable.secondCountableTopology`：∀ {X : Type u_2} [
inst : TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X] {s : Set X
},   TopologicalSpace.IsSeparable s → Seco…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `QuasiErgodic.ae_eq_const_of_ae_eq_comp_of_ae_range₀`：QuasiErgodic.ae_eq_
const_of_ae_eq_comp_of_ae_range₀ [Nonempty X] [MeasurableSpace X] {s : Set X} [M
easurableSpace.CountablySeparated s] {f :…
· 使用定理 `BorelSpace.countablyGenerated`：∀ {α : Type u_6} [inst : TopologicalSpace
 α] [inst_1 : MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α],   M
easurableSpace.Coun…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `AEMeasurable.nullMeasurable`：∀ {α : Type u_1} {β : Type u_2} {m0 : Measu
rableSpace α} {mβ : MeasurableSpace β} {μ : MeasureTheory.Measure α}   {f : α → 
β}, AEMeasurable …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…

--- 原说明 ---
Let `f : α → α` be a quasi-ergodic map.
Let `g : α → X` be an a.e. strongly measurable function
from `α` to a nonempty metrizable topological space.
If `g` is a.e.-invariant under `f`, then `g` is a.e. constant.
-/
theorem ae_eq_const_of_ae_eq_comp_ae {g : α → X} (h : QuasiErgodic f μ)
    (hgm : AEStronglyMeasurable g μ) (hg_eq : g ∘ f =ᵐ[μ] g) : ∃ c, g =ᵐ[μ] const α c := by
  borelize X
  rcases hgm.isSeparable_ae_range with ⟨t, ht, hgt⟩
  have := ht.secondCountableTopology
  exact h.ae_eq_const_of_ae_eq_comp_of_ae_range₀ hgt hgm.aemeasurable.nullMeasurable hg_eq
/-
**QuasiErgodic.eq_const_of_compQuasiMeasurePreserving_eq** 是 Mathlib 中的一个定理，位于命名
空间 `QuasiErgodic`。
形式化陈述：eq_const_of_compQuasiMeasurePreserving_eq (h : QuasiErgodic f μ) {g : α ->
ₘ[μ] X} (hg_eq : g.compQuasiMeasurePreserving f h.1 = g) : exists c, g = .const 
α c
参数：h : QuasiErgodic f μ；hg_eq : g.compQuasiMeasurePreserving f h.1 = g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuasiErgodic.toQuasiMeasurePreserving`：∀ {α : Type u_1} {m : MeasurableS
pace α} {f : α → α} {μ : autoParam (MeasureTheory.Measure α) QuasiErgodic._auto_
1},   QuasiErgodic f μ → Me…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.AEEqFun.coeFn_compQuasiMeasurePreserving`：coeFn_compQuasiM
easurePreserving (g : β ->ₘ[ν] γ) (hf : QuasiMeasurePreserving f μ ν) : g.compQu
asiMeasurePreserving f hf =ᵐ[μ] g ∘ f
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuasiErgodic.ae_eq_const_of_ae_eq_comp_ae`：ae_eq_const_of_ae_eq_comp_ae 
{g : α -> X} (h : QuasiErgodic f μ) (hgm : AEStronglyMeasurable g μ) (hg_eq : g 
∘ f =ᵐ[μ] g) : exists c, g =ᵐ[μ…
· 使用定理 `MeasureTheory.AEEqFun.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topologic
alSpace β]   (f : α →ₘ[μ] β), Me…
· 使用定理 `MeasureTheory.AEEqFun.ext`：ext {f g : α ->ₘ[μ] β} (h : f =ᵐ[μ] g) : f = 
g
· 使用定理 `MeasureTheory.AEEqFun.coeFn_const`：coeFn_const (b : β) : (const α b : α 
->ₘ[μ] β) =ᵐ[μ] Function.const α b
-/
theorem eq_const_of_compQuasiMeasurePreserving_eq (h : QuasiErgodic f μ) {g : α →ₘ[μ] X}
    (hg_eq : g.compQuasiMeasurePreserving f h.1 = g) : ∃ c, g = .const α c :=
  have : g ∘ f =ᵐ[μ] g := (g.coeFn_compQuasiMeasurePreserving h.1).symm.trans
    (hg_eq.symm ▸ .refl _ _)
  let ⟨c, hc⟩ := h.ae_eq_const_of_ae_eq_comp_ae g.aestronglyMeasurable this
  ⟨c, AEEqFun.ext <| hc.trans (AEEqFun.coeFn_const _ _).symm⟩

end QuasiErgodic

namespace Ergodic

/-- Let `f : α → α` be an ergodic map.
Let `g : α → X` be an a.e. strongly measurable function
from `α` to a nonempty metrizable topological space.
If `g` is a.e.-invariant under `f`, then `g` is a.e. constant. -/
/-
**Ergodic.ae_eq_const_of_ae_eq_comp_ae** 是 Mathlib 中的一个定理，位于命名空间 `Ergodic`。
形式化陈述：ae_eq_const_of_ae_eq_comp_ae {g : α -> X} (h : Ergodic f μ) (hgm : AEStron
glyMeasurable g μ) (hg_eq : g ∘ f =ᵐ[μ] g) : exists c, g =ᵐ[μ] const α c
参数：h : Ergodic f μ；hgm : AEStronglyMeasurable g μ；hg_eq : g ∘ f =ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `QuasiErgodic.ae_eq_const_of_ae_eq_comp_ae`：ae_eq_const_of_ae_eq_comp_ae 
{g : α -> X} (h : QuasiErgodic f μ) (hgm : AEStronglyMeasurable g μ) (hg_eq : g 
∘ f =ᵐ[μ] g) : exists c, g =ᵐ[μ…
· 使用定理 `Ergodic.quasiErgodic`：quasiErgodic (hf : Ergodic f μ) : QuasiErgodic f μ

--- 原说明 ---
Let `f : α → α` be an ergodic map.
Let `g : α → X` be an a.e. strongly measurable function
from `α` to a nonempty metrizable topological space.
If `g` is a.e.-invariant under `f`, then `g` is a.e. constant.
-/
theorem ae_eq_const_of_ae_eq_comp_ae {g : α → X} (h : Ergodic f μ) (hgm : AEStronglyMeasurable g μ)
    (hg_eq : g ∘ f =ᵐ[μ] g) : ∃ c, g =ᵐ[μ] const α c :=
  h.quasiErgodic.ae_eq_const_of_ae_eq_comp_ae hgm hg_eq
/-
**Ergodic.eq_const_of_compMeasurePreserving_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ergodi
c`。
形式化陈述：eq_const_of_compMeasurePreserving_eq (h : Ergodic f μ) {g : α ->ₘ[μ] X} (h
g_eq : g.compMeasurePreserving f h.1 = g) : exists c, g = .const α c
参数：h : Ergodic f μ；hg_eq : g.compMeasurePreserving f h.1 = g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ergodic.toMeasurePreserving`：∀ {α : Type u_1} {m : MeasurableSpace α} {f
 : α → α} {μ : autoParam (MeasureTheory.Measure α) Ergodic._auto_1},   Ergodic f
 μ → MeasureTheor…
· 使用定理 `QuasiErgodic.eq_const_of_compQuasiMeasurePreserving_eq`：eq_const_of_comp
QuasiMeasurePreserving_eq (h : QuasiErgodic f μ) {g : α ->ₘ[μ] X} (hg_eq : g.com
pQuasiMeasurePreserving f h.1 = g) : exists …
· 使用定理 `Ergodic.quasiErgodic`：quasiErgodic (hf : Ergodic f μ) : QuasiErgodic f μ
-/
theorem eq_const_of_compMeasurePreserving_eq (h : Ergodic f μ) {g : α →ₘ[μ] X}
    (hg_eq : g.compMeasurePreserving f h.1 = g) : ∃ c, g = .const α c :=
  h.quasiErgodic.eq_const_of_compQuasiMeasurePreserving_eq hg_eq

end Ergodic

