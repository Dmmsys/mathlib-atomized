/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Integration by parts for line derivatives

Let `f, g : E → ℝ` be two differentiable functions on a real vector space endowed with a Haar
measure. Then `∫ f * g' = - ∫ f' * g`, where `f'` and `g'` denote the derivatives of `f` and `g`
in a given direction `v`, provided that `f * g`, `f' * g` and `f * g'` are all integrable.

In this file, we prove this theorem as well as more general versions where the multiplication is
replaced by a general continuous bilinear form, giving versions both for the line derivative and
the Fréchet derivative. These results are derived from the one-dimensional version and a Fubini
argument.

## Main statements

* `integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable`: integration by parts
  in terms of line derivatives, with `HasLineDerivAt` assumptions and general bilinear form.
* `integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable`: integration by parts
  in terms of Fréchet derivatives, with `HasFDerivAt` assumptions and general bilinear form.
* `integral_bilinear_fderiv_right_eq_neg_left_of_integrable`: integration by parts
  in terms of Fréchet derivatives, written with `fderiv` assumptions and general bilinear form.
* `integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable`: integration by parts for scalar
  action, in terms of Fréchet derivatives, written with `fderiv` assumptions.
* `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`: integration by parts for scalar
  multiplication, in terms of Fréchet derivatives, written with `fderiv` assumptions.

## Implementation notes

A standard set of assumptions for integration by parts in a finite-dimensional real vector
space (without boundary term) is that the functions tend to zero at infinity and have integrable
derivatives. In this file, we instead assume that the functions are integrable and have integrable
derivatives. These sets of assumptions are not directly comparable (an integrable function with
integrable derivative does *not* have to tend to zero at infinity). The one we use is geared
towards applications to Fourier transforms.

TODO: prove similar theorems assuming that the functions tend to zero at infinity and have
integrable derivatives.
-/

public section

open MeasureTheory Measure Module Topology

variable {E F G W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup W]
  [NormedSpace ℝ W] [MeasurableSpace E] {μ : Measure E}

/-
**integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_aux1** 是 Math
lib 中的一个引理，位于命名空间 ``。
形式化陈述：integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_aux1 [Sig
maFinite μ] {f f' : E × Real -> F} {g g' : E × Real -> G} {B : F ->L[Real] G ->L
[Real] W} (hf'g : Integrable (fun x => B (f' x) (g x)) (μ.prod volume)) (hfg' : 
Integrable (fun x => B (f x) (g' x)) (μ.prod volume)) (hfg : Integrable (fun x =
> B (f x) (g x)) (μ.prod volume)) (hf : forall x in tsupport g, HasLineDerivAt R
eal f (f' x) x (0, 1)) (hg : forall x in tsupport f, HasLineDerivAt Real g (g' x
) x (0, 1)) : ∫ x, B (f x)
参数：hf'g : Integrable (fun x => B (f' x) (g x)) (μ.prod volume)；hfg' : Integrable
 (fun x => B (f x) (g' x)) (μ.prod volume)；hfg : Integrable (fun x => B (f x) (g
 x)) (μ.prod volume)；hf : forall x in tsupport g, HasLineDerivAt Real f (f' x) x
 (0, 1)；hg : forall x in tsupport f, HasLineDerivAt Real g (g' x) x (0, 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.integral_prod`：integral_prod (f : α × β -> E) (hf : Integr
able f (μ.prod ν)) : ∫ z, f z ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.prod_right_ae`：∀ {α : Type u_1} {β : Type u_2} 
{E : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {μ : Me
asureTheory.Measure α} {ν : …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrab
le`：integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable (hu : forall x 
in tsupport v, HasDerivAt u (u' x) x) (hv : forall x in tsupport…
· 使用定理 `tsupport_comp_subset_preimage`：∀ {X : Type u_1} {α : Type u_2} [inst : Z
ero α] [inst_1 : TopologicalSpace X] {Y : Type u_9}   [inst_2 : TopologicalSpace
 Y] (g : Y → α) {f …
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 46 条，此处仅展示前 30 条）
-/
lemma integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_aux1 [SigmaFinite μ]
    {f f' : E × ℝ → F} {g g' : E × ℝ → G} {B : F →L[ℝ] G →L[ℝ] W}
    (hf'g : Integrable (fun x ↦ B (f' x) (g x)) (μ.prod volume))
    (hfg' : Integrable (fun x ↦ B (f x) (g' x)) (μ.prod volume))
    (hfg : Integrable (fun x ↦ B (f x) (g x)) (μ.prod volume))
    (hf : ∀ x ∈ tsupport g, HasLineDerivAt ℝ f (f' x) x (0, 1))
    (hg : ∀ x ∈ tsupport f, HasLineDerivAt ℝ g (g' x) x (0, 1)) :
    ∫ x, B (f x) (g' x) ∂(μ.prod volume) = - ∫ x, B (f' x) (g x) ∂(μ.prod volume) := calc
  ∫ x, B (f x) (g' x) ∂(μ.prod volume)
    = ∫ x, (∫ t, B (f (x, t)) (g' (x, t))) ∂μ := integral_prod _ hfg'
  _ = ∫ x, (- ∫ t, B (f' (x, t)) (g (x, t))) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf'g.prod_right_ae, hfg'.prod_right_ae, hfg.prod_right_ae]
      with x hf'gx hfg'x hfgx
    apply integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable ?_ ?_ hfg'x hf'gx hfgx
    · intro t ht
      have : (x, t) ∈ tsupport g :=
        tsupport_comp_subset_preimage (f := fun y ↦ (x, y)) g (by fun_prop) ht
      convert! (hf (x, t) this).scomp_of_eq t ((hasDerivAt_id t).add (hasDerivAt_const t (-t)))
        (by simp) <;> simp
    · intro t ht
      have : (x, t) ∈ tsupport f :=
        tsupport_comp_subset_preimage (f := fun y ↦ (x, y)) f (by fun_prop) ht
      convert!
        (hg (x, t) this).scomp_of_eq t ((hasDerivAt_id t).add (hasDerivAt_const t (-t)))
          (by simp) <;> simp
  _ = - ∫ x, B (f' x) (g x) ∂(μ.prod volume) := by rw [integral_neg, integral_prod _ hf'g]

variable [BorelSpace E]
/-
**integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_aux2** 是 Math
lib 中的一个引理，位于命名空间 ``。
形式化陈述：integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_aux2 [Fin
iteDimensional Real E] {μ : Measure (E × Real)} [IsAddHaarMeasure μ] {f f' : E ×
 Real -> F} {g g' : E × Real -> G} {B : F ->L[Real] G ->L[Real] W} (hf'g : Integ
rable (fun x => B (f' x) (g x)) μ) (hfg' : Integrable (fun x => B (f x) (g' x)) 
μ) (hfg : Integrable (fun x => B (f x) (g x)) μ) (hf : forall x in tsupport g, H
asLineDerivAt Real f (f' x) x (0, 1)) (hg : forall x in tsupport f, HasLineDeriv
At Real g (g' x) x (0, 1))
参数：E × Real；hf'g : Integrable (fun x => B (f' x) (g x)) μ；hfg' : Integrable (fun
 x => B (f x) (g' x)) μ；hfg : Integrable (fun x => B (f x) (g x)) μ；hf : forall 
x in tsupport g, HasLineDerivAt Real f (f' x) x (0, 1)；hg : forall x in tsupport
 f, HasLineDerivAt Real g (g' x) x (0, 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Prod.instIsTopologicalAddGroup`：∀ {G : Type w} {H : Type x} [inst : Topo
logicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [inst_3 : Topo
logicalSpace H] [ins…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.Measure.prod.instIsFiniteMeasureOnCompacts`：∀ {α : Type u_
4} {β : Type u_5} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] {mα 
: MeasurableSpace α}   {mβ : MeasurableSpace β…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `MeasureTheory.Measure.isAddHaarMeasure_addHaarMeasure`：∀ {G : Type u_1} 
[inst : AddGroup G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGrou
p G]   [inst_3 : MeasurableSpace G] [inst_4…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `MeasureTheory.Measure.prod.instIsAddLeftInvariant`：∀ {G : Type u_1} [ins
t : MeasurableSpace G] [inst_1 : Add G] {μ : MeasureTheory.Measure G} [Measurabl
eAdd G]   [μ.IsAddLeftInvariant] [Measu…
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `MeasureTheory.Measure.isAddLeftInvariant_addHaarMeasure`：∀ {G : Type u_1
} [inst : AddGroup G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGr
oup G]   [inst_3 : MeasurableSpace G] [inst_4…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.sigmaFinite_addHaarMeasure`：∀ {G : Type u_1} [inst
 : AddGroup G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G] 
  [inst_3 : MeasurableSpace G] [inst_4…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
（共 44 条，此处仅展示前 30 条）
-/
lemma integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_aux2
    [FiniteDimensional ℝ E] {μ : Measure (E × ℝ)} [IsAddHaarMeasure μ]
    {f f' : E × ℝ → F} {g g' : E × ℝ → G} {B : F →L[ℝ] G →L[ℝ] W}
    (hf'g : Integrable (fun x ↦ B (f' x) (g x)) μ)
    (hfg' : Integrable (fun x ↦ B (f x) (g' x)) μ)
    (hfg : Integrable (fun x ↦ B (f x) (g x)) μ)
    (hf : ∀ x ∈ tsupport g, HasLineDerivAt ℝ f (f' x) x (0, 1))
    (hg : ∀ x ∈ tsupport f, HasLineDerivAt ℝ g (g' x) x (0, 1)) :
    ∫ x, B (f x) (g' x) ∂μ = - ∫ x, B (f' x) (g x) ∂μ := by
  let ν : Measure E := addHaar
  have A : ν.prod volume = (addHaarScalarFactor (ν.prod volume) μ) • μ :=
    isAddLeftInvariant_eq_smul _ _
  have Hf'g : Integrable (fun x ↦ B (f' x) (g x)) (ν.prod volume) := by
    rw [A]; exact hf'g.smul_measure_nnreal
  have Hfg' : Integrable (fun x ↦ B (f x) (g' x)) (ν.prod volume) := by
    rw [A]; exact hfg'.smul_measure_nnreal
  have Hfg : Integrable (fun x ↦ B (f x) (g x)) (ν.prod volume) := by
    rw [A]; exact hfg.smul_measure_nnreal
  rw [isAddLeftInvariant_eq_smul μ (ν.prod volume)]
  simp [integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_aux1 Hf'g Hfg' Hfg hf hg]

variable [FiniteDimensional ℝ E] [IsAddHaarMeasure μ]

/-- **Integration by parts for line derivatives**
Version with a general bilinear form `B`.
If `B f g` is integrable, as well as `B f' g` and `B f g'` where `f'` and `g'` are derivatives
of `f` and `g` in a given direction `v`, then `∫ B f g' = - ∫ B f' g`. -/
/-
**integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable** 是 Mathlib 中
的一个定理，位于命名空间 ``。
形式化陈述：integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable {f f' : E
 -> F} {g g' : E -> G} {v : E} {B : F ->L[Real] G ->L[Real] W} (hf'g : Integrabl
e (fun x => B (f' x) (g x)) μ) (hfg' : Integrable (fun x => B (f x) (g' x)) μ) (
hfg : Integrable (fun x => B (f x) (g x)) μ) (hf : forall x in tsupport g, HasLi
neDerivAt Real f (f' x) x v) (hg : forall x in tsupport f, HasLineDerivAt Real g
 (g' x) x v) : ∫ x, B (f x) (g' x) ∂μ = - ∫ x, B (f' x) (g x) ∂μ
参数：hf'g : Integrable (fun x => B (f' x) (g x)) μ；hfg' : Integrable (fun x => B (
f x) (g' x)) μ；hfg : Integrable (fun x => B (f x) (g x)) μ；hf : forall x in tsup
port g, HasLineDerivAt Real f (f' x) x v；hg : forall x in tsupport f, HasLineDer
ivAt Real g (g' x) x v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasLineDerivAt.lineDeriv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {F : Type u_2} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F
] {E : Type u_…
· 使用定理 `hasLineDerivAt_zero`：hasLineDerivAt_zero : HasLineDerivAt 𝕜 f 0 x 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `image_eq_zero_of_notMem_tsupport`：∀ {X : Type u_1} {α : Type u_2} [inst 
: Zero α] [inst_1 : TopologicalSpace X] {f : X → α} {x : X},   x ∉ tsupport f → 
f x = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nontrivial_iff`：nontrivial_iff : Nontrivial α ↔ exists x y : α, x != y
· 使用定理 `Module.finrank_prod`：Module.finrank_prod [Module.Finite R M] [Module.Fin
ite R M'] : finrank R (M × M') = finrank R M + finrank R M'
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Module.Free.function`：∀ (ι : Type u_1) (R : Type u_2) (M : Type u_3) [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [Fini
te ι] [Mod…
（共 90 条，此处仅展示前 30 条）

--- 原说明 ---
**Integration by parts for line derivatives**
Version with a general bilinear form `B`.
If `B f g` is integrable, as well as `B f' g` and `B f g'` where `f'` and `g'` a
re derivatives
of `f` and `g` in a given direction `v`, then `∫ B f g' = - ∫ B f' g`.
-/
theorem integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    {f f' : E → F} {g g' : E → G} {v : E} {B : F →L[ℝ] G →L[ℝ] W}
    (hf'g : Integrable (fun x ↦ B (f' x) (g x)) μ) (hfg' : Integrable (fun x ↦ B (f x) (g' x)) μ)
    (hfg : Integrable (fun x ↦ B (f x) (g x)) μ)
    (hf : ∀ x ∈ tsupport g, HasLineDerivAt ℝ f (f' x) x v)
    (hg : ∀ x ∈ tsupport f, HasLineDerivAt ℝ g (g' x) x v) :
    ∫ x, B (f x) (g' x) ∂μ = - ∫ x, B (f' x) (g x) ∂μ := by
  by_cases hW : CompleteSpace W; swap
  · simp [integral, hW]
  rcases eq_or_ne v 0 with rfl | hv
  · have Hf' x : B (f' x) (g x) = 0 := by
      by_cases hx : x ∈ tsupport g
      · simp [(hasLineDerivAt_zero (f := f) (x := x)).lineDeriv, (hf x hx).lineDeriv.symm]
      · simp [image_eq_zero_of_notMem_tsupport hx]
    have Hg' x : B (f x) (g' x) = 0 := by
      by_cases hx : x ∈ tsupport f
      · simp [(hasLineDerivAt_zero (f := g) (x := x)).lineDeriv, (hg x hx).lineDeriv.symm]
      · simp [image_eq_zero_of_notMem_tsupport hx]
    simp [Hf', Hg']
  have : Nontrivial E := nontrivial_iff.2 ⟨v, 0, hv⟩
  let n := finrank ℝ E
  let E' := Fin (n - 1) → ℝ
  obtain ⟨L, hL⟩ : ∃ L : E ≃L[ℝ] (E' × ℝ), L v = (0, 1) := by
    have : finrank ℝ (E' × ℝ) = n := by simpa [this, E'] using Nat.sub_add_cancel finrank_pos
    have L₀ : E ≃L[ℝ] (E' × ℝ) := (ContinuousLinearEquiv.ofFinrankEq this).symm
    obtain ⟨M, hM⟩ : ∃ M : (E' × ℝ) ≃L[ℝ] (E' × ℝ), M (L₀ v) = (0, 1) := by
      apply SeparatingDual.exists_continuousLinearEquiv_apply_eq
      · simpa using hv
      · simp
    exact ⟨L₀.trans M, by simp [hM]⟩
  let ν := Measure.map L μ
  suffices H : ∫ (x : E' × ℝ), (B (f (L.symm x))) (g' (L.symm x)) ∂ν =
      -∫ (x : E' × ℝ), (B (f' (L.symm x))) (g (L.symm x)) ∂ν by
    have : μ = Measure.map L.symm ν := by
      simp [ν, Measure.map_map L.symm.continuous.measurable L.continuous.measurable]
    have hL : IsClosedEmbedding L.symm := L.symm.toHomeomorph.isClosedEmbedding
    simpa [this, hL.integral_map] using H
  have L_emb : MeasurableEmbedding L := L.toHomeomorph.measurableEmbedding
  apply integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_aux2
  · simpa [ν, L_emb.integrable_map_iff, Function.comp_def] using hf'g
  · simpa [ν, L_emb.integrable_map_iff, Function.comp_def] using hfg'
  · simpa [ν, L_emb.integrable_map_iff, Function.comp_def] using hfg
  · intro x hx
    have : f = (f ∘ L.symm) ∘ (L : E →ₗ[ℝ] (E' × ℝ)) := by ext y; simp
    have h2x : L.symm x ∈ tsupport g :=
      (Set.ext_iff.mp (tsupport_comp_eq_preimage g L.symm.toHomeomorph) x).mp hx
    specialize hf (L.symm x) h2x
    rw [this] at hf
    convert! hf.of_comp using 1
    · simp
    · simp [← hL]
  · intro x hx
    have : g = (g ∘ L.symm) ∘ (L : E →ₗ[ℝ] (E' × ℝ)) := by ext y; simp
    have h2x : L.symm x ∈ tsupport f :=
      (Set.ext_iff.mp (tsupport_comp_eq_preimage f L.symm.toHomeomorph) x).mp hx
    specialize hg (L.symm x) h2x
    rw [this] at hg
    convert! hg.of_comp using 1
    · simp
    · simp [← hL]

/-- **Integration by parts for Fréchet derivatives**
Version with a general bilinear form `B`.
If `B f g` is integrable, as well as `B f' g` and `B f g'` where `f'` and `g'` are derivatives
of `f` and `g` in a given direction `v`, then `∫ B f g' = - ∫ B f' g`. -/
/-
**integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable {f : E -> F}
 {f' : E -> (E ->L[Real] F)} {g : E -> G} {g' : E -> (E ->L[Real] G)} {v : E} {B
 : F ->L[Real] G ->L[Real] W} (hf'g : Integrable (fun x => B (f' x v) (g x)) μ) 
(hfg' : Integrable (fun x => B (f x) (g' x v)) μ) (hfg : Integrable (fun x => B 
(f x) (g x)) μ) (hf : forall x in tsupport g, HasFDerivAt f (f' x) x) (hg : fora
ll x in tsupport f, HasFDerivAt g (g' x) x) : ∫ x, B (f x) (g' x v) ∂μ = - ∫ x, 
B (f' x v) (g x) ∂μ
参数：E ->L[Real] F；E ->L[Real] G；hf'g : Integrable (fun x => B (f' x v) (g x)) μ；h
fg' : Integrable (fun x => B (f x) (g' x v)) μ；hfg : Integrable (fun x => B (f x
) (g x)) μ；hf : forall x in tsupport g, HasFDerivAt f (f' x) x；hg : forall x in 
tsupport f, HasFDerivAt g (g' x) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable`：integr
al_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable {f f' : E -> F} {g g'
 : E -> G} {v : E} {B : F ->L[Real] G ->L[Real] W} (hf…
· 使用引理 `HasFDerivAt.hasLineDerivAt`：HasFDerivAt.hasLineDerivAt (hf : HasFDerivAt
 f L x) (v : E) : HasLineDerivAt 𝕜 f (L v) x v

--- 原说明 ---
**Integration by parts for Fréchet derivatives**
Version with a general bilinear form `B`.
If `B f g` is integrable, as well as `B f' g` and `B f g'` where `f'` and `g'` a
re derivatives
of `f` and `g` in a given direction `v`, then `∫ B f g' = - ∫ B f' g`.
-/
theorem integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable
    {f : E → F} {f' : E → (E →L[ℝ] F)}
    {g : E → G} {g' : E → (E →L[ℝ] G)} {v : E} {B : F →L[ℝ] G →L[ℝ] W}
    (hf'g : Integrable (fun x ↦ B (f' x v) (g x)) μ)
    (hfg' : Integrable (fun x ↦ B (f x) (g' x v)) μ)
    (hfg : Integrable (fun x ↦ B (f x) (g x)) μ)
    (hf : ∀ x ∈ tsupport g, HasFDerivAt f (f' x) x)
    (hg : ∀ x ∈ tsupport f, HasFDerivAt g (g' x) x) :
    ∫ x, B (f x) (g' x v) ∂μ = - ∫ x, B (f' x v) (g x) ∂μ :=
  integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable hf'g hfg' hfg
    (hf · · |>.hasLineDerivAt v) (hg · · |>.hasLineDerivAt v)

/-- **Integration by parts for Fréchet derivatives**
Version with a general bilinear form `B`.
If `B f g` is integrable, as well as `B f' g` and `B f g'` where `f'` and `g'` are the derivatives
of `f` and `g` in a given direction `v`, then `∫ B f g' = - ∫ B f' g`. -/
/-
**integral_bilinear_fderiv_right_eq_neg_left_of_integrable** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：integral_bilinear_fderiv_right_eq_neg_left_of_integrable {f : E -> F} {g :
 E -> G} {v : E} {B : F ->L[Real] G ->L[Real] W} (hf'g : Integrable (fun x => B 
(fderiv Real f x v) (g x)) μ) (hfg' : Integrable (fun x => B (f x) (fderiv Real 
g x v)) μ) (hfg : Integrable (fun x => B (f x) (g x)) μ) (hf : forall x in tsupp
ort g, DifferentiableAt Real f x) (hg : forall x in tsupport f, DifferentiableAt
 Real g x) : ∫ x, B (f x) (fderiv Real g x v) ∂μ = - ∫ x, B (fderiv Real f x v) 
(g x) ∂μ
参数：hf'g : Integrable (fun x => B (fderiv Real f x v) (g x)) μ；hfg' : Integrable 
(fun x => B (f x) (fderiv Real g x v)) μ；hfg : Integrable (fun x => B (f x) (g x
)) μ；hf : forall x in tsupport g, DifferentiableAt Real f x；hg : forall x in tsu
pport f, DifferentiableAt Real g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable`：integral_
bilinear_hasFDerivAt_right_eq_neg_left_of_integrable {f : E -> F} {f' : E -> (E 
->L[Real] F)} {g : E -> G} {g' : E -> (E ->L[Real] …
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x

--- 原说明 ---
**Integration by parts for Fréchet derivatives**
Version with a general bilinear form `B`.
If `B f g` is integrable, as well as `B f' g` and `B f g'` where `f'` and `g'` a
re the derivatives
of `f` and `g` in a given direction `v`, then `∫ B f g' = - ∫ B f' g`.
-/
theorem integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    {f : E → F} {g : E → G} {v : E} {B : F →L[ℝ] G →L[ℝ] W}
    (hf'g : Integrable (fun x ↦ B (fderiv ℝ f x v) (g x)) μ)
    (hfg' : Integrable (fun x ↦ B (f x) (fderiv ℝ g x v)) μ)
    (hfg : Integrable (fun x ↦ B (f x) (g x)) μ)
    (hf : ∀ x ∈ tsupport g, DifferentiableAt ℝ f x)
    (hg : ∀ x ∈ tsupport f, DifferentiableAt ℝ g x) :
    ∫ x, B (f x) (fderiv ℝ g x v) ∂μ = - ∫ x, B (fderiv ℝ f x v) (g x) ∂μ :=
  integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable hf'g hfg' hfg
    (hf · · |>.hasFDerivAt) (hg · · |>.hasFDerivAt)

variable {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    [NormedSpace 𝕜 G] [IsScalarTower ℝ 𝕜 G]

/-- **Integration by parts for Fréchet derivatives**
Version with a scalar function: `∫ f • g' = - ∫ f' • g` when `f • g'` and `f' • g` and `f • g`
are integrable, where `f'` and `g'` are the derivatives of `f` and `g` in a given direction `v`. -/
/-
**integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable {f : E -> 𝕜} {g : E 
-> G} {v : E} (hf'g : Integrable (fun x => fderiv Real f x v • g x) μ) (hfg' : I
ntegrable (fun x => f x • fderiv Real g x v) μ) (hfg : Integrable (fun x => f x 
• g x) μ) (hf : forall x in tsupport g, DifferentiableAt Real f x) (hg : forall 
x in tsupport f, DifferentiableAt Real g x) : ∫ x, f x • fderiv Real g x v ∂μ = 
- ∫ x, fderiv Real f x v • g x ∂μ
参数：hf'g : Integrable (fun x => fderiv Real f x v • g x) μ；hfg' : Integrable (fun
 x => f x • fderiv Real g x v) μ；hfg : Integrable (fun x => f x • g x) μ；hf : fo
rall x in tsupport g, DifferentiableAt Real f x；hg : forall x in tsupport f, Dif
ferentiableAt Real g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `integral_bilinear_fderiv_right_eq_neg_left_of_integrable`：integral_bilin
ear_fderiv_right_eq_neg_left_of_integrable {f : E -> F} {g : E -> G} {v : E} {B 
: F ->L[Real] G ->L[Real] W} (hf'g : Integrabl…

--- 原说明 ---
**Integration by parts for Fréchet derivatives**
Version with a scalar function: `∫ f • g' = - ∫ f' • g` when `f • g'` and `f' • 
g` and `f • g`
are integrable, where `f'` and `g'` are the derivatives of `f` and `g` in a give
n direction `v`.
-/
theorem integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    {f : E → 𝕜} {g : E → G} {v : E}
    (hf'g : Integrable (fun x ↦ fderiv ℝ f x v • g x) μ)
    (hfg' : Integrable (fun x ↦ f x • fderiv ℝ g x v) μ)
    (hfg : Integrable (fun x ↦ f x • g x) μ)
    (hf : ∀ x ∈ tsupport g, DifferentiableAt ℝ f x)
    (hg : ∀ x ∈ tsupport f, DifferentiableAt ℝ g x) :
    ∫ x, f x • fderiv ℝ g x v ∂μ = - ∫ x, fderiv ℝ f x v • g x ∂μ :=
  integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.lsmul ℝ 𝕜) hf'g hfg' hfg hf hg

/-- **Integration by parts for Fréchet derivatives**
Version with two scalar functions: `∫ f * g' = - ∫ f' * g` when `f * g'` and `f' * g` and `f * g`
are integrable, where `f'` and `g'` are the derivatives of `f` and `g` in a given direction `v`. -/
/-
**integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable {f : E -> 𝕜} {g : E ->
 𝕜} {v : E} (hf'g : Integrable (fun x => fderiv Real f x v * g x) μ) (hfg' : Int
egrable (fun x => f x * fderiv Real g x v) μ) (hfg : Integrable (fun x => f x * 
g x) μ) (hf : forall x in tsupport g, DifferentiableAt Real f x) (hg : forall x 
in tsupport f, DifferentiableAt Real g x) : ∫ x, f x * fderiv Real g x v ∂μ = - 
∫ x, fderiv Real f x v * g x ∂μ
参数：hf'g : Integrable (fun x => fderiv Real f x v * g x) μ；hfg' : Integrable (fun
 x => f x * fderiv Real g x v) μ；hfg : Integrable (fun x => f x * g x) μ；hf : fo
rall x in tsupport g, DifferentiableAt Real f x；hg : forall x in tsupport f, Dif
ferentiableAt Real g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `integral_bilinear_fderiv_right_eq_neg_left_of_integrable`：integral_bilin
ear_fderiv_right_eq_neg_left_of_integrable {f : E -> F} {g : E -> G} {v : E} {B 
: F ->L[Real] G ->L[Real] W} (hf'g : Integrabl…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
**Integration by parts for Fréchet derivatives**
Version with two scalar functions: `∫ f * g' = - ∫ f' * g` when `f * g'` and `f'
 * g` and `f * g`
are integrable, where `f'` and `g'` are the derivatives of `f` and `g` in a give
n direction `v`.
-/
theorem integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    {f : E → 𝕜} {g : E → 𝕜} {v : E}
    (hf'g : Integrable (fun x ↦ fderiv ℝ f x v * g x) μ)
    (hfg' : Integrable (fun x ↦ f x * fderiv ℝ g x v) μ)
    (hfg : Integrable (fun x ↦ f x * g x) μ)
    (hf : ∀ x ∈ tsupport g, DifferentiableAt ℝ f x)
    (hg : ∀ x ∈ tsupport f, DifferentiableAt ℝ g x) :
    ∫ x, f x * fderiv ℝ g x v ∂μ = - ∫ x, fderiv ℝ f x v * g x ∂μ :=
  integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ 𝕜) hf'g hfg' hfg hf hg
