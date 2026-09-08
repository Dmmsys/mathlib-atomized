/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.Topology.Order.CountableSeparating

/-!
# Radon-Nikodym derivative of invariant measures

Given two finite invariant measures of a self-map,
we prove that their singular parts, their absolutely continuous parts,
and their Radon-Nikodym derivatives are invariant too.

For the first two theorems, we only assume that one of the measures is finite
and the other is σ-finite.

## TODO

It isn't clear if the finiteness assumptions are optimal in this file.
We should either weaken them, or describe an example showing that it's impossible.
-/

public section

open MeasureTheory Measure Set

variable {X : Type*} {m : MeasurableSpace X} {μ ν : Measure X} [IsFiniteMeasure μ]

namespace MeasureTheory.MeasurePreserving

/-- The singular part of a finite invariant measure of a self-map
with respect to a σ-finite invariant measure is an invariant measure. -/
/-
**MeasureTheory.MeasurePreserving.singularPart** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.MeasurePreserving`。
形式化陈述：∀ {X : Type u_1} {m : MeasurableSpace X} {μ ν : MeasureTheory.Measure X} [
MeasureTheory.IsFiniteMeasure μ]   [MeasureTheory.SigmaFinite ν] {f : X → X},   
MeasureTheory.MeasurePreserving f μ μ →     MeasureTheory.MeasurePreserving f ν 
ν → MeasureTheory.MeasurePreserving f (μ.singularPart ν) (μ.singularPart ν)
参数：μ.singularPart ν；μ.singularPart ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.MutuallySingular.symm`：symm (h : ν ⟂ₘ μ) : μ ⟂ₘ ν
· 使用定理 `MeasureTheory.Measure.mutuallySingular_singularPart`：mutuallySingular_si
ngularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.singularPart_eq_restrict`：singularPart_eq_restrict
 {s : Set α} [μ.HaveLebesgueDecomposition ν] (hμs : μ.singularPart ν sᶜ = 0) (hν
s : ν s = 0) : μ.singularPart ν = μ.…
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.mem_ae_iff`：mem_ae_iff {s : Set α} : s in ae μ ↔ μ sᶜ = 0
· 使用定理 `Filter.eventuallyEq_univ`：eventuallyEq_univ {s : Set α} {l : Filter α} :
 s =ᶠ[l] univ ↔ s in l
· 使用定理 `MeasureTheory.ae_eq_univ_iff_measure_eq`：ae_eq_univ_iff_measure_eq [IsFi
niteMeasure μ] (hs : NullMeasurableSet s μ) : s =ᵐ[μ] univ ↔ μ s = μ univ
· 使用定理 `MeasureTheory.Measure.singularPart.instIsFiniteMeasure`：∀ {α : Type u_1}
 {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.IsFinite
Measure μ],   MeasureTheory.IsFiniteMeasure …
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `MeasureTheory.MeasurePreserving.measurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : 
autoParam (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.Measure.add_apply`：add_apply {_m : MeasurableSpace α} (μ₁ 
μ₂ : Measure α) (s : Set α) : (μ₁ + μ₂) s = μ₁ s + μ₂ s
· 使用定理 `MeasureTheory.withDensity_absolutelyContinuous`：withDensity_absolutelyCo
ntinuous {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) : μ.withDen
sity f ≪ μ
· 使用定理 `MeasureTheory.MeasurePreserving.measure_preimage`：measure_preimage {f : 
α -> β} (hf : MeasurePreserving f μa μb) {s : Set β} (hs : NullMeasurableSet s μ
b) : μa (f ⁻¹' s) = μb s
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `MeasureTheory.Measure.rnDeriv_add_singularPart`：rnDeriv_add_singularPart
 (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : ν.withDensity (μ.rnDeriv ν)
 + μ.singularPart ν = μ
· 使用定理 `MeasureTheory.measure_add_measure_compl`：measure_add_measure_compl (h : 
MeasurableSet s) : μ s + μ sᶜ = μ univ
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MeasureTheory.MeasurePreserving.preimage_null`：preimage_null {f : α -> β
} (hf : MeasurePreserving f μa μb) {s : Set β} (hs : μb s = 0) : μa (f ⁻¹' s) = 
0
· 使用定理 `MeasureTheory.MeasurePreserving.restrict_preimage`：restrict_preimage {f 
: α -> β} (hf : MeasurePreserving f μa μb) {s : Set β} (hs : MeasurableSet s) : 
MeasurePreserving f (μa.restrict (f ⁻¹'…

--- 原说明 ---
The singular part of a finite invariant measure of a self-map
with respect to a σ-finite invariant measure is an invariant measure.
-/
protected theorem singularPart [SigmaFinite ν] {f : X → X}
    (hfμ : MeasurePreserving f μ μ) (hfν : MeasurePreserving f ν ν) :
    MeasurePreserving f (μ.singularPart ν) (μ.singularPart ν) := by
  rcases (μ.mutuallySingular_singularPart ν).symm with ⟨s, hsm, hνs, hμs⟩
  convert! hfμ.restrict_preimage hsm using 1
  · refine singularPart_eq_restrict ?_ (hfν.preimage_null hνs)
    rw [← mem_ae_iff, ← Filter.eventuallyEq_univ,
      ae_eq_univ_iff_measure_eq (hfμ.measurable hsm).nullMeasurableSet]
    calc
      μ.singularPart ν (f ⁻¹' s) = (ν.withDensity (μ.rnDeriv ν) + μ.singularPart ν) (f ⁻¹' s) := by
        rw [← hfν.measure_preimage hsm.nullMeasurableSet] at hνs
        rw [add_apply, withDensity_absolutelyContinuous _ _ hνs, zero_add]
      _ = (ν.withDensity (μ.rnDeriv ν) + μ.singularPart ν) s := by
        rw [rnDeriv_add_singularPart, hfμ.measure_preimage hsm.nullMeasurableSet]
      _ = μ.singularPart ν s := by
        rw [add_apply, withDensity_absolutelyContinuous _ _ hνs, zero_add]
      _ = μ.singularPart ν univ := by
        rw [← measure_add_measure_compl hsm, hμs, add_zero]
  · exact singularPart_eq_restrict hμs hνs

/-- The absolutely continuous part of a finite invariant measure of a self-map
with respect to a σ-finite invariant measure is an invariant measure. -/
/-
**MeasureTheory.MeasurePreserving.withDensity_rnDeriv** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.MeasurePreserving`。
形式化陈述：∀ {X : Type u_1} {m : MeasurableSpace X} {μ ν : MeasureTheory.Measure X} [
MeasureTheory.IsFiniteMeasure μ]   [MeasureTheory.SigmaFinite ν] {f : X → X},   
MeasureTheory.MeasurePreserving f μ μ →     MeasureTheory.MeasurePreserving f ν 
ν →       MeasureTheory.MeasurePreserving f (ν.withDensity (μ.rnDeriv ν)) (ν.wit
hDensity (μ.rnDeriv ν))
参数：ν.withDensity (μ.rnDeriv ν)；ν.withDensity (μ.rnDeriv ν)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.measurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : 
autoParam (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.add_left_inj`：add_left_inj (h : a != ∞) : b + a = c + a ↔ b = c
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `MeasureTheory.Measure.singularPart.instIsFiniteMeasure`：∀ {α : Type u_1}
 {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.IsFinite
Measure μ],   MeasureTheory.IsFiniteMeasure …
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasureTheory.Measure.add_apply`：add_apply {_m : MeasurableSpace α} (μ₁ 
μ₂ : Measure α) (s : Set α) : (μ₁ + μ₂) s = μ₁ s + μ₂ s
· 使用引理 `MeasureTheory.Measure.rnDeriv_add_singularPart`：rnDeriv_add_singularPart
 (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : ν.withDensity (μ.rnDeriv ν)
 + μ.singularPart ν = μ
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.MeasurePreserving.measure_preimage`：measure_preimage {f : 
α -> β} (hf : MeasurePreserving f μa μb) {s : Set β} (hs : NullMeasurableSet s μ
b) : μa (f ⁻¹' s) = μb s
· 使用定理 `MeasureTheory.MeasurePreserving.singularPart`：∀ {X : Type u_1} {m : Meas
urableSpace X} {μ ν : MeasureTheory.Measure X} [MeasureTheory.IsFiniteMeasure μ]
   [MeasureTheory.SigmaFinite ν] {…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ

--- 原说明 ---
The absolutely continuous part of a finite invariant measure of a self-map
with respect to a σ-finite invariant measure is an invariant measure.
-/
protected theorem withDensity_rnDeriv [SigmaFinite ν] {f : X → X}
    (hfμ : MeasurePreserving f μ μ) (hfν : MeasurePreserving f ν ν) :
    MeasurePreserving f (ν.withDensity (μ.rnDeriv ν)) (ν.withDensity (μ.rnDeriv ν)) := by
  use hfμ.measurable
  ext s hs
  rw [← ENNReal.add_left_inj (measure_ne_top (μ.singularPart ν) s), map_apply hfμ.measurable hs,
    ← add_apply, rnDeriv_add_singularPart,
    ← (hfμ.singularPart hfν).measure_preimage hs.nullMeasurableSet, ← add_apply,
    rnDeriv_add_singularPart, hfμ.measure_preimage hs.nullMeasurableSet]

/-- The Radon-Nikodym derivative of a finite invariant measure of a self-map `f`
with respect to another finite invariant measure of `f` is a.e. invariant under `f`. -/
/-
**MeasureTheory.MeasurePreserving.rnDeriv_comp_aeEq** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.MeasurePreserving`。
形式化陈述：rnDeriv_comp_aeEq [IsFiniteMeasure ν] {f : X -> X} (hfμ : MeasurePreservin
g f μ μ) (hfν : MeasurePreserving f ν ν) : μ.rnDeriv ν ∘ f =ᵐ[ν] μ.rnDeriv ν
参数：hfμ : MeasurePreserving f μ μ；hfν : MeasurePreserving f ν ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用引理 `Filter.EventuallyEq.of_forall_eventually_lt_iff`：of_forall_eventually_lt
_iff (h : forall x, forallᶠ a in l, f a < x ↔ g a < x) : f =ᶠ[l] g
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `MeasureTheory.instCountableInterFilterAe`：∀ {α : Type u_1} {F : Type u_2
} [inst : FunLike F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F
 α]   (μ : F), CountableInterF…
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `measurableSet_Iio`：measurableSet_Iio [ClosedIciTopology α] : MeasurableS
et (Iio a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `MeasureTheory.measure_sdiff_symm`：measure_sdiff_symm (hs : NullMeasurabl
eSet s μ) (ht : NullMeasurableSet t μ) (h : μ s = μ t) (hfin : μ (s inter t) != 
∞) : μ (s \ t) = μ (t …
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `MeasureTheory.MeasurePreserving.measurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : 
autoParam (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.MeasurePreserving.measure_preimage`：measure_preimage {f : 
α -> β} (hf : MeasurePreserving f μa μb) {s : Set β} (hs : NullMeasurableSet s μ
b) : μa (f ⁻¹' s) = μb s
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.setLIntegral_rnDeriv`：setLIntegral_rnDeriv [HaveLe
besgueDecomposition μ ν] [SFinite ν] (hμν : μ ≪ ν) (s : Set α) : ∫⁻ x in s, μ.rn
Deriv ν x ∂ν = μ s
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.setLIntegral_strict_mono`：setLIntegral_strict_mono {f g : 
α -> Real>=0∞} {s : Set α} (hsm : MeasurableSet s) (hs : μ s != 0) (hg : Measura
ble g) (hfi : ∫⁻ x in s, f x…
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
The Radon-Nikodym derivative of a finite invariant measure of a self-map `f`
with respect to another finite invariant measure of `f` is a.e. invariant under 
`f`.
-/
theorem rnDeriv_comp_aeEq [IsFiniteMeasure ν] {f : X → X}
    (hfμ : MeasurePreserving f μ μ) (hfν : MeasurePreserving f ν ν) :
    μ.rnDeriv ν ∘ f =ᵐ[ν] μ.rnDeriv ν := by
  wlog hμν : μ ≪ ν generalizing μ
  · specialize this (hfμ.withDensity_rnDeriv hfν) (withDensity_absolutelyContinuous _ _)
    refine .trans (.trans ?_ this) (rnDeriv_withDensity ν (measurable_rnDeriv μ ν))
    apply hfν.quasiMeasurePreserving.ae_eq_comp
    exact (rnDeriv_withDensity ν (measurable_rnDeriv μ ν)).symm
  refine .of_forall_eventually_lt_iff fun c ↦ ?_
  set s := {a | μ.rnDeriv ν a < c}
  have hsm : MeasurableSet s := measurable_rnDeriv _ _ measurableSet_Iio
  have hμ_sdiff : μ (f ⁻¹' s \ s) = μ (s \ f ⁻¹' s) :=
    measure_sdiff_symm (hfμ.measurable hsm).nullMeasurableSet hsm.nullMeasurableSet
      (hfμ.measure_preimage hsm.nullMeasurableSet) (by finiteness)
  have hν_sdiff : ν (f ⁻¹' s \ s) = ν (s \ f ⁻¹' s) :=
    measure_sdiff_symm (hfν.measurable hsm).nullMeasurableSet hsm.nullMeasurableSet
      (hfν.measure_preimage hsm.nullMeasurableSet) (by finiteness)
  suffices f ⁻¹' s =ᵐ[ν] s from this.mem_iff
  suffices ν (f ⁻¹' s \ s) = 0 from (ae_le_set.mpr this).antisymm (ae_le_set.mpr <| hν_sdiff ▸ this)
  contrapose! hμ_sdiff with h₀
  apply ne_of_gt
  calc
    μ (s \ f ⁻¹' s) = ∫⁻ a in s \ f ⁻¹' s, μ.rnDeriv ν a ∂ν := (setLIntegral_rnDeriv hμν _).symm
    _ < ∫⁻ _ in s \ f ⁻¹' s, c ∂ν := by
      apply setLIntegral_strict_mono (hsm.diff (hfμ.measurable hsm)) (hν_sdiff ▸ h₀)
        measurable_const
      · rw [setLIntegral_rnDeriv hμν]
        finiteness
      · exact .of_forall fun x hx ↦ hx.1
    _ = ∫⁻ _ in f ⁻¹' s \ s, c ∂ν := by simp [hν_sdiff]
    _ ≤ ∫⁻ a in f ⁻¹' s \ s, μ.rnDeriv ν a ∂ν :=
      setLIntegral_mono (by fun_prop) (fun x hx ↦ not_lt.mp hx.2)
    _ = μ (f ⁻¹' s \ s) := setLIntegral_rnDeriv hμν _

end MeasureTheory.MeasurePreserving

