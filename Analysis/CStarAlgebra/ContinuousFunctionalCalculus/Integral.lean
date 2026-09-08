/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Anatole Dedecker
-/
module

public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.MeasureTheory.SpecificCodomains.ContinuousMapZero
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integrals and the continuous functional calculus

This file gives results about integrals of the form `∫ x, cfc (f x) a`. Most notably, we show
that the integral commutes with the continuous functional calculus under appropriate conditions.

## Main declarations

+ `cfc_setIntegral` (resp. `cfc_integral`): given a function `f : X → 𝕜 → 𝕜`, we have that
  `cfc (fun r => ∫ x in s, f x r ∂μ) a = ∫ x in s, cfc (f x) a ∂μ`
  under appropriate conditions (resp. with `s = univ`)
+ `cfcₙ_setIntegral`, `cfcₙ_integral`: the same for the non-unital continuous functional calculus
+ `integrableOn_cfc`, `integrableOn_cfcₙ`, `integrable_cfc`, `integrable_cfcₙ`:
  functions of the form `fun x => cfc (f x) a` are integrable.

## Implementation Notes

The lemmas mentioned above are stated under much stricter hypotheses than necessary
(typically, simultaneous continuity of `f` in the parameter and the spectrum element).
They all come with primed version which only assume what's needed, and may be used together
with the API developed in `Mathlib.MeasureTheory.SpecificCodomains.ContinuousMap`.

## TODO

+ Lift this to the case where the CFC is over `ℝ≥0`
+ Use this to prove operator monotonicity and concavity/convexity of `rpow` and `log`
-/

public section

open MeasureTheory Topology
open scoped ContinuousMapZero

section unital

open ContinuousMap

variable {X : Type*} {𝕜 : Type*} {A : Type*} {p : A → Prop} [RCLike 𝕜]
  [MeasurableSpace X] {μ : Measure X}
  [NormedRing A] [StarRing A] [NormedAlgebra 𝕜 A]
  [ContinuousFunctionalCalculus 𝕜 A p]
  [CompleteSpace A]

/-
**cfcL_integral** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfcL_integral [NormedSpace Real A] (a : A) (f : X -> C(spectrum 𝕜 a, 𝕜)) (
hf₁ : Integrable f μ) (ha : p a
参数：a : A；f : X -> C(spectrum 𝕜 a, 𝕜)；hf₁ : Integrable f μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.integral_comp_comm`：integral_comp_comm [CompleteSpac
e E] (L : E ->L[𝕜] Fₗ) {φ : X -> E} (φ_int : Integrable φ μ) : ∫ x, L (φ x) ∂μ =
 L (∫ x, φ x ∂μ)
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `FrechetUrysohnSpace.to_sequentialSpace`：∀ {X : Type u_1} [inst : Topolog
icalSpace X] [FrechetUrysohnSpace X], SequentialSpace X
· 使用定理 `FirstCountableTopology.frechetUrysohnSpace`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] [FirstCountableTopology X], FrechetUrysohnSpace X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
-/
lemma cfcL_integral [NormedSpace ℝ A] (a : A) (f : X → C(spectrum 𝕜 a, 𝕜)) (hf₁ : Integrable f μ)
    (ha : p a := by cfc_tac) :
    ∫ x, cfcL (a := a) ha (f x) ∂μ = cfcL (a := a) ha (∫ x, f x ∂μ) := by
  rw [ContinuousLinearMap.integral_comp_comm _ hf₁]
/-
**cfcL_integrable** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfcL_integrable (a : A) (f : X -> C(spectrum 𝕜 a, 𝕜)) (hf₁ : Integrable f 
μ) (ha : p a
参数：a : A；f : X -> C(spectrum 𝕜 a, 𝕜)；hf₁ : Integrable f μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `ContinuousLinearMap.integrable_comp`：ContinuousLinearMap.integrable_comp
 {φ : α -> H} (L : H ->SL[σ] E) (φ_int : Integrable φ μ) : Integrable (fun a : α
 => L (φ a)) μ
-/
lemma cfcL_integrable (a : A) (f : X → C(spectrum 𝕜 a, 𝕜))
    (hf₁ : Integrable f μ) (ha : p a := by cfc_tac) :
    Integrable (fun x ↦ cfcL (a := a) ha (f x)) μ :=
  ContinuousLinearMap.integrable_comp _ hf₁
/-
**cfcHom_integral** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfcHom_integral [NormedSpace Real A] (a : A) (f : X -> C(spectrum 𝕜 a, 𝕜))
 (hf₁ : Integrable f μ) (ha : p a
参数：a : A；f : X -> C(spectrum 𝕜 a, 𝕜)；hf₁ : Integrable f μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用引理 `cfcL_integral`：cfcL_integral [NormedSpace Real A] (a : A) (f : X -> C(sp
ectrum 𝕜 a, 𝕜)) (hf₁ : Integrable f μ) (ha : p a
-/
lemma cfcHom_integral [NormedSpace ℝ A] (a : A) (f : X → C(spectrum 𝕜 a, 𝕜))
    (hf₁ : Integrable f μ) (ha : p a := by cfc_tac) :
    ∫ x, cfcHom (a := a) ha (f x) ∂μ = cfcHom (a := a) ha (∫ x, f x ∂μ) :=
  cfcL_integral a f hf₁ ha

/-- An integrability criterion for the continuous functional calculus.
For a version with stronger assumptions which in practice are often easier to verify, see
`integrable_cfc`. -/
/-
**integrable_cfc'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：integrable_cfc' (f : X -> 𝕜 -> 𝕜) (a : A) (hf : Integrable (fun x : X => m
kD ((spectrum 𝕜 a).domRestrict (f x)) 0) μ) (ha : p a
参数：f : X -> 𝕜 -> 𝕜；a : A；hf : Integrable (fun x : X => mkD ((spectrum 𝕜 a).domRe
strict (f x)) 0) μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `cfc_eq_cfcL_mkD`：cfc_eq_cfcL_mkD : cfc f a = cfcL (a
· 使用引理 `cfcL_integrable`：cfcL_integrable (a : A) (f : X -> C(spectrum 𝕜 a, 𝕜)) (
hf₁ : Integrable f μ) (ha : p a

--- 原说明 ---
An integrability criterion for the continuous functional calculus.
For a version with stronger assumptions which in practice are often easier to ve
rify, see
`integrable_cfc`.
-/
lemma integrable_cfc' (f : X → 𝕜 → 𝕜) (a : A)
    (hf : Integrable
      (fun x : X => mkD ((spectrum 𝕜 a).domRestrict (f x)) 0) μ)
    (ha : p a := by cfc_tac) :
    Integrable (fun x => cfc (f x) a) μ := by
  conv in cfc _ _ => rw [cfc_eq_cfcL_mkD _ a]
  exact cfcL_integrable _ _ hf ha

/-- An integrability criterion for the continuous functional calculus.
For a version with stronger assumptions which in practice are often easier to verify, see
`integrableOn_cfc`. -/
/-
**integrableOn_cfc'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：integrableOn_cfc' {s : Set X} (f : X -> 𝕜 -> 𝕜) (a : A) (hf : IntegrableOn
 (fun x : X => mkD ((spectrum 𝕜 a).domRestrict (f x)) 0) s μ) (ha : p a
参数：f : X -> 𝕜 -> 𝕜；a : A；hf : IntegrableOn (fun x : X => mkD ((spectrum 𝕜 a).dom
Restrict (f x)) 0) s μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用引理 `integrable_cfc'`：integrable_cfc' (f : X -> 𝕜 -> 𝕜) (a : A) (hf : Integra
ble (fun x : X => mkD ((spectrum 𝕜 a).domRestrict (f x)) 0) μ) (ha : p a

--- 原说明 ---
An integrability criterion for the continuous functional calculus.
For a version with stronger assumptions which in practice are often easier to ve
rify, see
`integrableOn_cfc`.
-/
lemma integrableOn_cfc' {s : Set X} (f : X → 𝕜 → 𝕜) (a : A)
    (hf : IntegrableOn
      (fun x : X => mkD ((spectrum 𝕜 a).domRestrict (f x)) 0) s μ)
    (ha : p a := by cfc_tac) :
    IntegrableOn (fun x => cfc (f x) a) s μ := by
  exact integrable_cfc' _ _ hf ha

open Set Function in
/-- An integrability criterion for the continuous functional calculus.
This version assumes joint continuity of `f`, see `integrable_cfc'` for a statement
with weaker assumptions. -/
/-
**integrable_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：integrable_cfc [TopologicalSpace X] [OpensMeasurableSpace X] (f : X -> 𝕜 -
> 𝕜) (bound : X -> Real) (a : A) [SecondCountableTopologyEither X C(spectrum 𝕜 a
, 𝕜)] (hf : ContinuousOn (uncurry f) (univ ×ˢ spectrum 𝕜 a)) (bound_ge : forallᵐ
 x ∂μ, forall z in spectrum 𝕜 a, ‖f x z‖ <= bound x) (bound_int : HasFiniteInteg
ral bound μ) (ha : p a
参数：f : X -> 𝕜 -> 𝕜；bound : X -> Real；a : A；spectrum 𝕜 a, 𝕜；hf : ContinuousOn (un
curry f) (univ ×ˢ spectrum 𝕜 a)；bound_ge : forallᵐ x ∂μ, forall z in spectrum 𝕜 
a, ‖f x z‖ <= bound x；bound_int : HasFiniteIntegral bound μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `integrable_cfc'`：integrable_cfc' (f : X -> 𝕜 -> 𝕜) (a : A) (hf : Integra
ble (fun x : X => mkD ((spectrum 𝕜 a).domRestrict (f x)) 0) μ) (ha : p a
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用引理 `ContinuousMap.aeStronglyMeasurable_mkD_restrict_of_uncurry`：aeStronglyMe
asurable_mkD_restrict_of_uncurry {t : Set Y} [CompactSpace t] [TopologicalSpace 
X] [OpensMeasurableSpace X] [SecondCountableTopo…
· 使用引理 `ContinuousMap.hasFiniteIntegral_mkD_restrict_of_bound`：hasFiniteIntegral
_mkD_restrict_of_bound {s : Set Y} [CompactSpace s] (f : X -> Y -> E) (g : C(s, 
E)) (f_ae_contOn : forallᵐ x ∂μ, Continuous…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.prodMk_right`：Continuous.prodMk_right (x : X) : Continuous fu
n y : Y => (x, y)
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
An integrability criterion for the continuous functional calculus.
This version assumes joint continuity of `f`, see `integrable_cfc'` for a statem
ent
with weaker assumptions.
-/
lemma integrable_cfc [TopologicalSpace X] [OpensMeasurableSpace X] (f : X → 𝕜 → 𝕜)
    (bound : X → ℝ) (a : A) [SecondCountableTopologyEither X C(spectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (univ ×ˢ spectrum 𝕜 a))
    (bound_ge : ∀ᵐ x ∂μ, ∀ z ∈ spectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    Integrable (fun x => cfc (f x) a) μ := by
  refine integrable_cfc' _ _ ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_mkD_restrict_of_uncurry _ _ hf
  · refine hasFiniteIntegral_mkD_restrict_of_bound f _ ?_ bound bound_int bound_ge
    exact .of_forall fun x ↦
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨Set.mem_univ _, hz⟩

open Set Function in
/-- An integrability criterion for the continuous functional calculus.
This version assumes joint continuity of `f`, see `integrableOn_cfc'` for a statement
with weaker assumptions. -/
/-
**integrableOn_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：integrableOn_cfc [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
 (hs : MeasurableSet s) (f : X -> 𝕜 -> 𝕜) (bound : X -> Real) (a : A) [SecondCou
ntableTopologyEither X C(spectrum 𝕜 a, 𝕜)] (hf : ContinuousOn (uncurry f) (s ×ˢ 
spectrum 𝕜 a)) (bound_ge : forallᵐ x ∂(μ.restrict s), forall z in spectrum 𝕜 a, 
‖f x z‖ <= bound x) (bound_int : HasFiniteIntegral bound (μ.restrict s)) (ha : p
 a
参数：hs : MeasurableSet s；f : X -> 𝕜 -> 𝕜；bound : X -> Real；a : A；spectrum 𝕜 a, 𝕜；
hf : ContinuousOn (uncurry f) (s ×ˢ spectrum 𝕜 a)；bound_ge : forallᵐ x ∂(μ.restr
ict s), forall z in spectrum 𝕜 a, ‖f x z‖ <= bound x；bound_int : HasFiniteIntegr
al bound (μ.restrict s)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `integrableOn_cfc'`：integrableOn_cfc' {s : Set X} (f : X -> 𝕜 -> 𝕜) (a : 
A) (hf : IntegrableOn (fun x : X => mkD ((spectrum 𝕜 a).domRestrict (f x)) 0) s 
μ) (ha …
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用引理 `ContinuousMap.aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry`：aeS
tronglyMeasurable_restrict_mkD_restrict_of_uncurry {s : Set X} {t : Set Y} [Comp
actSpace t] [TopologicalSpace X] [OpensMeasurableSpace X]…
· 使用引理 `ContinuousMap.hasFiniteIntegral_mkD_restrict_of_bound`：hasFiniteIntegral
_mkD_restrict_of_bound {s : Set Y} [CompactSpace s] (f : X -> Y -> E) (g : C(s, 
E)) (f_ae_contOn : forallᵐ x ∂μ, Continuous…
· 使用定理 `MeasureTheory.ae_restrict_of_forall_mem`：ae_restrict_of_forall_mem {μ : 
Measure α} {s : Set α} (hs : MeasurableSet s) {p : α -> Prop} (h : forall x in s
, p x) : forallᵐ (x : α) ∂μ.r…
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.prodMk_right`：Continuous.prodMk_right (x : X) : Continuous fu
n y : Y => (x, y)

--- 原说明 ---
An integrability criterion for the continuous functional calculus.
This version assumes joint continuity of `f`, see `integrableOn_cfc'` for a stat
ement
with weaker assumptions.
-/
lemma integrableOn_cfc [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
    (hs : MeasurableSet s) (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A)
    [SecondCountableTopologyEither X C(spectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (s ×ˢ spectrum 𝕜 a))
    (bound_ge : ∀ᵐ x ∂(μ.restrict s), ∀ z ∈ spectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    IntegrableOn (fun x => cfc (f x) a) s μ := by
  refine integrableOn_cfc' _ _ ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry hs _ _ hf
  · refine hasFiniteIntegral_mkD_restrict_of_bound f _ ?_ bound bound_int bound_ge
    exact ae_restrict_of_forall_mem hs fun x hx ↦
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨hx, hz⟩

open Set in
/-- The continuous functional calculus commutes with integration.
For a version with stronger assumptions which in practice are often easier to verify, see
`cfc_integral`. -/
/-
**cfc_integral'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_integral' [NormedSpace Real A] (f : X -> 𝕜 -> 𝕜) (a : A) (hf₁ : forall
ᵐ x ∂μ, ContinuousOn (f x) (spectrum 𝕜 a)) (hf₂ : Integrable (fun x : X => mkD (
(spectrum 𝕜 a).domRestrict (f x)) 0) μ) (ha : p a
参数：f : X -> 𝕜 -> 𝕜；a : A；hf₁ : forallᵐ x ∂μ, ContinuousOn (f x) (spectrum 𝕜 a)；h
f₂ : Integrable (fun x : X => mkD ((spectrum 𝕜 a).domRestrict (f x)) 0) μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContinuousMap.integral_apply`：ContinuousMap.integral_apply [NormedSpace 
Real E] [CompleteSpace E] {f : X -> C(Y, E)} (hf : Integrable f μ) (y : Y) : (∫ 
x, f x ∂μ) y = ∫ x…
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `ContinuousMap.mkD_apply_of_continuousOn`：mkD_apply_of_continuousOn {s : 
Set α} {f : α -> β} {g : C(s, β)} {x : s} (hf : ContinuousOn f s) : mkD (s.domRe
strict f) g x = f x
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_congr`：continuous_congr {g : X -> Y} (h : forall x, f x = g x
) : Continuous f ↔ Continuous g
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `cfc_eq_cfcL_mkD`：cfc_eq_cfcL_mkD : cfc f a = cfcL (a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `cfcL_integral`：cfcL_integral [NormedSpace Real A] (a : A) (f : X -> C(sp
ectrum 𝕜 a, 𝕜)) (hf₁ : Integrable f μ) (ha : p a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The continuous functional calculus commutes with integration.
For a version with stronger assumptions which in practice are often easier to ve
rify, see
`cfc_integral`.
-/
lemma cfc_integral' [NormedSpace ℝ A] (f : X → 𝕜 → 𝕜) (a : A)
    (hf₁ : ∀ᵐ x ∂μ, ContinuousOn (f x) (spectrum 𝕜 a))
    (hf₂ : Integrable
      (fun x : X => mkD ((spectrum 𝕜 a).domRestrict (f x)) 0) μ)
    (ha : p a := by cfc_tac) :
    cfc (fun z => ∫ x, f x z ∂μ) a = ∫ x, cfc (f x) a ∂μ := by
  have key₁ (z : spectrum 𝕜 a) :
      ∫ x, f x z ∂μ = (∫ x, mkD ((spectrum 𝕜 a).domRestrict (f x)) 0 ∂μ) z := by
    rw [integral_apply hf₂]
    refine integral_congr_ae ?_
    filter_upwards [hf₁] with x cont_x
    rw [mkD_apply_of_continuousOn cont_x]
  have key₂ (z : spectrum 𝕜 a) :
      ∫ x, f x z ∂μ = mkD ((spectrum 𝕜 a).domRestrict (fun z ↦ ∫ x, f x z ∂μ)) 0 z := by
    rw [mkD_apply_of_continuousOn]
    rw [continuousOn_iff_continuous_domRestrict]
    refine continuous_congr key₁ |>.mpr ?_
    exact map_continuous (∫ x, mkD ((spectrum 𝕜 a).domRestrict (f x)) 0 ∂μ)
  simp_rw [cfc_eq_cfcL_mkD _ a, cfcL_integral a _ hf₂ ha]
  congr
  ext z
  rw [← key₁, key₂]

open Set in
/-- The continuous functional calculus commutes with integration.
For a version with stronger assumptions which in practice are often easier to verify, see
`cfc_setIntegral`. -/
/-
**cfc_setIntegral'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_setIntegral' {s : Set X} [NormedSpace Real A] (f : X -> 𝕜 -> 𝕜) (a : A
) (hf₁ : forallᵐ x ∂(μ.restrict s), ContinuousOn (f x) (spectrum 𝕜 a)) (hf₂ : In
tegrableOn (fun x : X => mkD ((spectrum 𝕜 a).domRestrict (f x)) 0) s μ) (ha : p 
a
参数：f : X -> 𝕜 -> 𝕜；a : A；hf₁ : forallᵐ x ∂(μ.restrict s), ContinuousOn (f x) (sp
ectrum 𝕜 a)；hf₂ : IntegrableOn (fun x : X => mkD ((spectrum 𝕜 a).domRestrict (f 
x)) 0) s μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用引理 `cfc_integral'`：cfc_integral' [NormedSpace Real A] (f : X -> 𝕜 -> 𝕜) (a :
 A) (hf₁ : forallᵐ x ∂μ, ContinuousOn (f x) (spectrum 𝕜 a)) (hf₂ : Integrable (f
un …

--- 原说明 ---
The continuous functional calculus commutes with integration.
For a version with stronger assumptions which in practice are often easier to ve
rify, see
`cfc_setIntegral`.
-/
lemma cfc_setIntegral' {s : Set X} [NormedSpace ℝ A] (f : X → 𝕜 → 𝕜) (a : A)
    (hf₁ : ∀ᵐ x ∂(μ.restrict s), ContinuousOn (f x) (spectrum 𝕜 a))
    (hf₂ : IntegrableOn
      (fun x : X => mkD ((spectrum 𝕜 a).domRestrict (f x)) 0) s μ)
    (ha : p a := by cfc_tac) :
    cfc (fun z => ∫ x in s, f x z ∂μ) a = ∫ x in s, cfc (f x) a ∂μ :=
  cfc_integral' _ _ hf₁ hf₂ ha

open Function Set in
/-- The continuous functional calculus commutes with integration.
This version assumes joint continuity of `f`, see `cfc_integral'` for a statement
with weaker assumptions. -/
/-
**cfc_integral** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_integral [NormedSpace Real A] [TopologicalSpace X] [OpensMeasurableSpa
ce X] (f : X -> 𝕜 -> 𝕜) (bound : X -> Real) (a : A) [SecondCountableTopologyEith
er X C(spectrum 𝕜 a, 𝕜)] (hf : ContinuousOn (uncurry f) (univ ×ˢ spectrum 𝕜 a)) 
(bound_ge : forallᵐ x ∂μ, forall z in spectrum 𝕜 a, ‖f x z‖ <= bound x) (bound_i
nt : HasFiniteIntegral bound μ) (ha : p a
参数：f : X -> 𝕜 -> 𝕜；bound : X -> Real；a : A；spectrum 𝕜 a, 𝕜；hf : ContinuousOn (un
curry f) (univ ×ˢ spectrum 𝕜 a)；bound_ge : forallᵐ x ∂μ, forall z in spectrum 𝕜 
a, ‖f x z‖ <= bound x；bound_int : HasFiniteIntegral bound μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.prodMk_right`：Continuous.prodMk_right (x : X) : Continuous fu
n y : Y => (x, y)
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用引理 `cfc_integral'`：cfc_integral' [NormedSpace Real A] (f : X -> 𝕜 -> 𝕜) (a :
 A) (hf₁ : forallᵐ x ∂μ, ContinuousOn (f x) (spectrum 𝕜 a)) (hf₂ : Integrable (f
un …
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用引理 `ContinuousMap.aeStronglyMeasurable_mkD_restrict_of_uncurry`：aeStronglyMe
asurable_mkD_restrict_of_uncurry {t : Set Y} [CompactSpace t] [TopologicalSpace 
X] [OpensMeasurableSpace X] [SecondCountableTopo…
· 使用引理 `ContinuousMap.hasFiniteIntegral_mkD_restrict_of_bound`：hasFiniteIntegral
_mkD_restrict_of_bound {s : Set Y} [CompactSpace s] (f : X -> Y -> E) (g : C(s, 
E)) (f_ae_contOn : forallᵐ x ∂μ, Continuous…

--- 原说明 ---
The continuous functional calculus commutes with integration.
This version assumes joint continuity of `f`, see `cfc_integral'` for a statemen
t
with weaker assumptions.
-/
lemma cfc_integral [NormedSpace ℝ A] [TopologicalSpace X] [OpensMeasurableSpace X]
    (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A) [SecondCountableTopologyEither X C(spectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (univ ×ˢ spectrum 𝕜 a))
    (bound_ge : ∀ᵐ x ∂μ, ∀ z ∈ spectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    cfc (fun r => ∫ x, f x r ∂μ) a = ∫ x, cfc (f x) a ∂μ := by
  have : ∀ᵐ (x : X) ∂μ, ContinuousOn (f x) (spectrum 𝕜 a) := .of_forall fun x ↦
    hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨Set.mem_univ _, hz⟩
  refine cfc_integral' _ _ this ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_mkD_restrict_of_uncurry _ _ hf
  · exact hasFiniteIntegral_mkD_restrict_of_bound f _ this bound bound_int bound_ge

open Function Set in
/-- The continuous functional calculus commutes with integration.
This version assumes joint continuity of `f`, see `cfc_setIntegral'` for a statement
with weaker assumptions. -/
/-
**cfc_setIntegral** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_setIntegral [NormedSpace Real A] [TopologicalSpace X] [OpensMeasurable
Space X] {s : Set X} (hs : MeasurableSet s) (f : X -> 𝕜 -> 𝕜) (bound : X -> Real
) (a : A) [SecondCountableTopologyEither X C(spectrum 𝕜 a, 𝕜)] (hf : ContinuousO
n (uncurry f) (s ×ˢ spectrum 𝕜 a)) (bound_ge : forallᵐ x ∂(μ.restrict s), forall
 z in spectrum 𝕜 a, ‖f x z‖ <= bound x) (bound_int : HasFiniteIntegral bound (μ.
restrict s)) (ha : p a
参数：hs : MeasurableSet s；f : X -> 𝕜 -> 𝕜；bound : X -> Real；a : A；spectrum 𝕜 a, 𝕜；
hf : ContinuousOn (uncurry f) (s ×ˢ spectrum 𝕜 a)；bound_ge : forallᵐ x ∂(μ.restr
ict s), forall z in spectrum 𝕜 a, ‖f x z‖ <= bound x；bound_int : HasFiniteIntegr
al bound (μ.restrict s)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_restrict_of_forall_mem`：ae_restrict_of_forall_mem {μ : 
Measure α} {s : Set α} (hs : MeasurableSet s) {p : α -> Prop} (h : forall x in s
, p x) : forallᵐ (x : α) ∂μ.r…
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.prodMk_right`：Continuous.prodMk_right (x : X) : Continuous fu
n y : Y => (x, y)
· 使用引理 `cfc_setIntegral'`：cfc_setIntegral' {s : Set X} [NormedSpace Real A] (f :
 X -> 𝕜 -> 𝕜) (a : A) (hf₁ : forallᵐ x ∂(μ.restrict s), ContinuousOn (f x) (spec
trum 𝕜…
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用引理 `ContinuousMap.aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry`：aeS
tronglyMeasurable_restrict_mkD_restrict_of_uncurry {s : Set X} {t : Set Y} [Comp
actSpace t] [TopologicalSpace X] [OpensMeasurableSpace X]…
· 使用引理 `ContinuousMap.hasFiniteIntegral_mkD_restrict_of_bound`：hasFiniteIntegral
_mkD_restrict_of_bound {s : Set Y} [CompactSpace s] (f : X -> Y -> E) (g : C(s, 
E)) (f_ae_contOn : forallᵐ x ∂μ, Continuous…

--- 原说明 ---
The continuous functional calculus commutes with integration.
This version assumes joint continuity of `f`, see `cfc_setIntegral'` for a state
ment
with weaker assumptions.
-/
lemma cfc_setIntegral [NormedSpace ℝ A] [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
    (hs : MeasurableSet s) (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A)
    [SecondCountableTopologyEither X C(spectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (s ×ˢ spectrum 𝕜 a))
    (bound_ge : ∀ᵐ x ∂(μ.restrict s), ∀ z ∈ spectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    cfc (fun r => ∫ x in s, f x r ∂μ) a = ∫ x in s, cfc (f x) a ∂μ := by
  have : ∀ᵐ (x : X) ∂(μ.restrict s), ContinuousOn (f x) (spectrum 𝕜 a) :=
    ae_restrict_of_forall_mem hs fun x hx ↦
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨hx, hz⟩
  refine cfc_setIntegral' _ _ this ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry hs _ _ hf
  · exact hasFiniteIntegral_mkD_restrict_of_bound f _ this bound bound_int bound_ge

end unital

section nonunital

open ContinuousMapZero

variable {X : Type*} {𝕜 : Type*} {A : Type*} {p : A → Prop} [RCLike 𝕜]
  [MeasurableSpace X] {μ : Measure X} [NonUnitalNormedRing A] [StarRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
  [NonUnitalContinuousFunctionalCalculus 𝕜 A p]
  [CompleteSpace A]

/-
**cfc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{R : Type u_3} →   {A : Type u_4} →     {p : A → Prop} →       [inst : Com
mSemiring R] →         [inst_1 : StarRing R] →           [inst_2 : MetricSpace R
] →             [inst_3 : IsTopologicalSemiring R] →               [inst_4 : Con
tinuousStar R] →                 [inst_5 : TopologicalSpace A] →                
   [inst_6 : Ring A] →                     [inst_7 : StarRing A] →              
         [inst_8 : Algebra R A] → [instCFC : ContinuousFunctionalCalculus R A p]
 → (R → R) → A → A
参数：R → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cfcₙL_integral [NormedSpace ℝ A] (a : A) (f : X → C(quasispectrum 𝕜 a, 𝕜)₀)
    (hf₁ : Integrable f μ) (ha : p a := by cfc_tac) :
    ∫ x, cfcₙL (a := a) ha (f x) ∂μ = cfcₙL (a := a) ha (∫ x, f x ∂μ) := by
  rw [ContinuousLinearMap.integral_comp_comm _ hf₁]
/-
**cfc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{R : Type u_3} →   {A : Type u_4} →     {p : A → Prop} →       [inst : Com
mSemiring R] →         [inst_1 : StarRing R] →           [inst_2 : MetricSpace R
] →             [inst_3 : IsTopologicalSemiring R] →               [inst_4 : Con
tinuousStar R] →                 [inst_5 : TopologicalSpace A] →                
   [inst_6 : Ring A] →                     [inst_7 : StarRing A] →              
         [inst_8 : Algebra R A] → [instCFC : ContinuousFunctionalCalculus R A p]
 → (R → R) → A → A
参数：R → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cfcₙHom_integral [NormedSpace ℝ A] (a : A) (f : X → C(quasispectrum 𝕜 a, 𝕜)₀)
    (hf₁ : Integrable f μ) (ha : p a := by cfc_tac) :
    ∫ x, cfcₙHom (a := a) ha (f x) ∂μ = cfcₙHom (a := a) ha (∫ x, f x ∂μ) :=
  cfcₙL_integral a f hf₁ ha
/-
**cfc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{R : Type u_3} →   {A : Type u_4} →     {p : A → Prop} →       [inst : Com
mSemiring R] →         [inst_1 : StarRing R] →           [inst_2 : MetricSpace R
] →             [inst_3 : IsTopologicalSemiring R] →               [inst_4 : Con
tinuousStar R] →                 [inst_5 : TopologicalSpace A] →                
   [inst_6 : Ring A] →                     [inst_7 : StarRing A] →              
         [inst_8 : Algebra R A] → [instCFC : ContinuousFunctionalCalculus R A p]
 → (R → R) → A → A
参数：R → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cfcₙL_integrable (a : A) (f : X → C(quasispectrum 𝕜 a, 𝕜)₀)
    (hf₁ : Integrable f μ) (ha : p a := by cfc_tac) :
    Integrable (fun x ↦ cfcₙL (a := a) ha (f x)) μ :=
  ContinuousLinearMap.integrable_comp _ hf₁

/-- An integrability criterion for the continuous functional calculus.
For a version with stronger assumptions which in practice are often easier to verify, see
`integrable_cfcₙ`. -/
/-
**integrable_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：integrable_cfc [TopologicalSpace X] [OpensMeasurableSpace X] (f : X -> 𝕜 -
> 𝕜) (bound : X -> Real) (a : A) [SecondCountableTopologyEither X C(spectrum 𝕜 a
, 𝕜)] (hf : ContinuousOn (uncurry f) (univ ×ˢ spectrum 𝕜 a)) (bound_ge : forallᵐ
 x ∂μ, forall z in spectrum 𝕜 a, ‖f x z‖ <= bound x) (bound_int : HasFiniteInteg
ral bound μ) (ha : p a
参数：f : X -> 𝕜 -> 𝕜；bound : X -> Real；a : A；spectrum 𝕜 a, 𝕜；hf : ContinuousOn (un
curry f) (univ ×ˢ spectrum 𝕜 a)；bound_ge : forallᵐ x ∂μ, forall z in spectrum 𝕜 
a, ‖f x z‖ <= bound x；bound_int : HasFiniteIntegral bound μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `integrable_cfc'`：integrable_cfc' (f : X -> 𝕜 -> 𝕜) (a : A) (hf : Integra
ble (fun x : X => mkD ((spectrum 𝕜 a).domRestrict (f x)) 0) μ) (ha : p a
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用引理 `ContinuousMap.aeStronglyMeasurable_mkD_restrict_of_uncurry`：aeStronglyMe
asurable_mkD_restrict_of_uncurry {t : Set Y} [CompactSpace t] [TopologicalSpace 
X] [OpensMeasurableSpace X] [SecondCountableTopo…
· 使用引理 `ContinuousMap.hasFiniteIntegral_mkD_restrict_of_bound`：hasFiniteIntegral
_mkD_restrict_of_bound {s : Set Y} [CompactSpace s] (f : X -> Y -> E) (g : C(s, 
E)) (f_ae_contOn : forallᵐ x ∂μ, Continuous…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.prodMk_right`：Continuous.prodMk_right (x : X) : Continuous fu
n y : Y => (x, y)
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
An integrability criterion for the continuous functional calculus.
For a version with stronger assumptions which in practice are often easier to ve
rify, see
`integrable_cfcₙ`.
-/
lemma integrable_cfcₙ' (f : X → 𝕜 → 𝕜) (a : A)
    (hf : Integrable
      (fun x : X => mkD ((quasispectrum 𝕜 a).domRestrict (f x)) 0) μ)
    (ha : p a := by cfc_tac) :
    Integrable (fun x => cfcₙ (f x) a) μ := by
  conv in cfcₙ _ _ => rw [cfcₙ_eq_cfcₙL_mkD _ a]
  exact cfcₙL_integrable _ _ hf ha

/-- An integrability criterion for the continuous functional calculus.
For a version with stronger assumptions which in practice are often easier to verify, see
`integrableOn_cfcₙ`. -/
/-
**integrableOn_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：integrableOn_cfc [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
 (hs : MeasurableSet s) (f : X -> 𝕜 -> 𝕜) (bound : X -> Real) (a : A) [SecondCou
ntableTopologyEither X C(spectrum 𝕜 a, 𝕜)] (hf : ContinuousOn (uncurry f) (s ×ˢ 
spectrum 𝕜 a)) (bound_ge : forallᵐ x ∂(μ.restrict s), forall z in spectrum 𝕜 a, 
‖f x z‖ <= bound x) (bound_int : HasFiniteIntegral bound (μ.restrict s)) (ha : p
 a
参数：hs : MeasurableSet s；f : X -> 𝕜 -> 𝕜；bound : X -> Real；a : A；spectrum 𝕜 a, 𝕜；
hf : ContinuousOn (uncurry f) (s ×ˢ spectrum 𝕜 a)；bound_ge : forallᵐ x ∂(μ.restr
ict s), forall z in spectrum 𝕜 a, ‖f x z‖ <= bound x；bound_int : HasFiniteIntegr
al bound (μ.restrict s)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `integrableOn_cfc'`：integrableOn_cfc' {s : Set X} (f : X -> 𝕜 -> 𝕜) (a : 
A) (hf : IntegrableOn (fun x : X => mkD ((spectrum 𝕜 a).domRestrict (f x)) 0) s 
μ) (ha …
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用引理 `ContinuousMap.aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry`：aeS
tronglyMeasurable_restrict_mkD_restrict_of_uncurry {s : Set X} {t : Set Y} [Comp
actSpace t] [TopologicalSpace X] [OpensMeasurableSpace X]…
· 使用引理 `ContinuousMap.hasFiniteIntegral_mkD_restrict_of_bound`：hasFiniteIntegral
_mkD_restrict_of_bound {s : Set Y} [CompactSpace s] (f : X -> Y -> E) (g : C(s, 
E)) (f_ae_contOn : forallᵐ x ∂μ, Continuous…
· 使用定理 `MeasureTheory.ae_restrict_of_forall_mem`：ae_restrict_of_forall_mem {μ : 
Measure α} {s : Set α} (hs : MeasurableSet s) {p : α -> Prop} (h : forall x in s
, p x) : forallᵐ (x : α) ∂μ.r…
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.prodMk_right`：Continuous.prodMk_right (x : X) : Continuous fu
n y : Y => (x, y)

--- 原说明 ---
An integrability criterion for the continuous functional calculus.
For a version with stronger assumptions which in practice are often easier to ve
rify, see
`integrableOn_cfcₙ`.
-/
lemma integrableOn_cfcₙ' {s : Set X} (f : X → 𝕜 → 𝕜) (a : A)
    (hf : IntegrableOn
      (fun x : X => mkD ((quasispectrum 𝕜 a).domRestrict (f x)) 0) s μ)
    (ha : p a := by cfc_tac) :
    IntegrableOn (fun x => cfcₙ (f x) a) s μ := by
  exact integrable_cfcₙ' _ _ hf ha

open Set Function in
/-- An integrability criterion for the continuous functional calculus.
This version assumes joint continuity of `f`, see `integrable_cfcₙ'` for a statement
with weaker assumptions. -/
/-
**integrable_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：integrable_cfc [TopologicalSpace X] [OpensMeasurableSpace X] (f : X -> 𝕜 -
> 𝕜) (bound : X -> Real) (a : A) [SecondCountableTopologyEither X C(spectrum 𝕜 a
, 𝕜)] (hf : ContinuousOn (uncurry f) (univ ×ˢ spectrum 𝕜 a)) (bound_ge : forallᵐ
 x ∂μ, forall z in spectrum 𝕜 a, ‖f x z‖ <= bound x) (bound_int : HasFiniteInteg
ral bound μ) (ha : p a
参数：f : X -> 𝕜 -> 𝕜；bound : X -> Real；a : A；spectrum 𝕜 a, 𝕜；hf : ContinuousOn (un
curry f) (univ ×ˢ spectrum 𝕜 a)；bound_ge : forallᵐ x ∂μ, forall z in spectrum 𝕜 
a, ‖f x z‖ <= bound x；bound_int : HasFiniteIntegral bound μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `integrable_cfc'`：integrable_cfc' (f : X -> 𝕜 -> 𝕜) (a : A) (hf : Integra
ble (fun x : X => mkD ((spectrum 𝕜 a).domRestrict (f x)) 0) μ) (ha : p a
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用引理 `ContinuousMap.aeStronglyMeasurable_mkD_restrict_of_uncurry`：aeStronglyMe
asurable_mkD_restrict_of_uncurry {t : Set Y} [CompactSpace t] [TopologicalSpace 
X] [OpensMeasurableSpace X] [SecondCountableTopo…
· 使用引理 `ContinuousMap.hasFiniteIntegral_mkD_restrict_of_bound`：hasFiniteIntegral
_mkD_restrict_of_bound {s : Set Y} [CompactSpace s] (f : X -> Y -> E) (g : C(s, 
E)) (f_ae_contOn : forallᵐ x ∂μ, Continuous…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.prodMk_right`：Continuous.prodMk_right (x : X) : Continuous fu
n y : Y => (x, y)
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
An integrability criterion for the continuous functional calculus.
This version assumes joint continuity of `f`, see `integrable_cfcₙ'` for a state
ment
with weaker assumptions.
-/
lemma integrable_cfcₙ [TopologicalSpace X] [OpensMeasurableSpace X] (f : X → 𝕜 → 𝕜)
    (bound : X → ℝ) (a : A)
    [SecondCountableTopologyEither X C(quasispectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (univ ×ˢ quasispectrum 𝕜 a))
    (f_zero : ∀ᵐ x ∂μ, f x 0 = 0)
    (bound_ge : ∀ᵐ x ∂μ, ∀ z ∈ quasispectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    Integrable (fun x => cfcₙ (f x) a) μ := by
  refine integrable_cfcₙ' _ _ ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_mkD_restrict_of_uncurry _ _ hf f_zero
  · refine hasFiniteIntegral_mkD_restrict_of_bound f _ ?_ f_zero bound bound_int bound_ge
    exact .of_forall fun x ↦
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨Set.mem_univ _, hz⟩

open Set Function in
/-- An integrability criterion for the continuous functional calculus.
This version assumes joint continuity of `f`, see `integrableOn_cfcₙ'` for a statement
with weaker assumptions. -/
/-
**integrableOn_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：integrableOn_cfc [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
 (hs : MeasurableSet s) (f : X -> 𝕜 -> 𝕜) (bound : X -> Real) (a : A) [SecondCou
ntableTopologyEither X C(spectrum 𝕜 a, 𝕜)] (hf : ContinuousOn (uncurry f) (s ×ˢ 
spectrum 𝕜 a)) (bound_ge : forallᵐ x ∂(μ.restrict s), forall z in spectrum 𝕜 a, 
‖f x z‖ <= bound x) (bound_int : HasFiniteIntegral bound (μ.restrict s)) (ha : p
 a
参数：hs : MeasurableSet s；f : X -> 𝕜 -> 𝕜；bound : X -> Real；a : A；spectrum 𝕜 a, 𝕜；
hf : ContinuousOn (uncurry f) (s ×ˢ spectrum 𝕜 a)；bound_ge : forallᵐ x ∂(μ.restr
ict s), forall z in spectrum 𝕜 a, ‖f x z‖ <= bound x；bound_int : HasFiniteIntegr
al bound (μ.restrict s)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `integrableOn_cfc'`：integrableOn_cfc' {s : Set X} (f : X -> 𝕜 -> 𝕜) (a : 
A) (hf : IntegrableOn (fun x : X => mkD ((spectrum 𝕜 a).domRestrict (f x)) 0) s 
μ) (ha …
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用引理 `ContinuousMap.aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry`：aeS
tronglyMeasurable_restrict_mkD_restrict_of_uncurry {s : Set X} {t : Set Y} [Comp
actSpace t] [TopologicalSpace X] [OpensMeasurableSpace X]…
· 使用引理 `ContinuousMap.hasFiniteIntegral_mkD_restrict_of_bound`：hasFiniteIntegral
_mkD_restrict_of_bound {s : Set Y} [CompactSpace s] (f : X -> Y -> E) (g : C(s, 
E)) (f_ae_contOn : forallᵐ x ∂μ, Continuous…
· 使用定理 `MeasureTheory.ae_restrict_of_forall_mem`：ae_restrict_of_forall_mem {μ : 
Measure α} {s : Set α} (hs : MeasurableSet s) {p : α -> Prop} (h : forall x in s
, p x) : forallᵐ (x : α) ∂μ.r…
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.prodMk_right`：Continuous.prodMk_right (x : X) : Continuous fu
n y : Y => (x, y)

--- 原说明 ---
An integrability criterion for the continuous functional calculus.
This version assumes joint continuity of `f`, see `integrableOn_cfcₙ'` for a sta
tement
with weaker assumptions.
-/
lemma integrableOn_cfcₙ [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
    (hs : MeasurableSet s) (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A)
    [SecondCountableTopologyEither X C(quasispectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (s ×ˢ quasispectrum 𝕜 a))
    (f_zero : ∀ᵐ x ∂(μ.restrict s), f x 0 = 0)
    (bound_ge : ∀ᵐ x ∂(μ.restrict s), ∀ z ∈ quasispectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    IntegrableOn (fun x => cfcₙ (f x) a) s μ := by
  refine integrableOn_cfcₙ' _ _ ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry hs _ _ hf f_zero
  · refine hasFiniteIntegral_mkD_restrict_of_bound f _ ?_ f_zero bound bound_int bound_ge
    exact ae_restrict_of_forall_mem hs fun x hx ↦
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨hx, hz⟩

open Set in
/-- The continuous functional calculus commutes with integration.
For a version with stronger assumptions which in practice are often easier to verify, see
`cfcₙ_integral`. -/
/-
**cfc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{R : Type u_3} →   {A : Type u_4} →     {p : A → Prop} →       [inst : Com
mSemiring R] →         [inst_1 : StarRing R] →           [inst_2 : MetricSpace R
] →             [inst_3 : IsTopologicalSemiring R] →               [inst_4 : Con
tinuousStar R] →                 [inst_5 : TopologicalSpace A] →                
   [inst_6 : Ring A] →                     [inst_7 : StarRing A] →              
         [inst_8 : Algebra R A] → [instCFC : ContinuousFunctionalCalculus R A p]
 → (R → R) → A → A
参数：R → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The continuous functional calculus commutes with integration.
For a version with stronger assumptions which in practice are often easier to ve
rify, see
`cfcₙ_integral`.
-/
lemma cfcₙ_integral' [NormedSpace ℝ A] (f : X → 𝕜 → 𝕜) (a : A)
    (hf₁ : ∀ᵐ x ∂μ, ContinuousOn (f x) (quasispectrum 𝕜 a))
    (hf₂ : ∀ᵐ x ∂μ, f x 0 = 0)
    (hf₃ : Integrable
      (fun x : X => mkD ((quasispectrum 𝕜 a).domRestrict (f x)) 0) μ)
    (ha : p a := by cfc_tac) :
    cfcₙ (fun z => ∫ x, f x z ∂μ) a = ∫ x, cfcₙ (f x) a ∂μ := by
  have key₁ (z : quasispectrum 𝕜 a) :
      ∫ x, f x z ∂μ = (∫ x, mkD ((quasispectrum 𝕜 a).domRestrict (f x)) 0 ∂μ) z := by
    rw [integral_apply hf₃]
    refine integral_congr_ae ?_
    filter_upwards [hf₁, hf₂] with x cont_x zero_x
    rw [mkD_apply_of_continuousOn cont_x zero_x]
  have key₂ (z : quasispectrum 𝕜 a) :
      ∫ x, f x z ∂μ = mkD ((quasispectrum 𝕜 a).domRestrict (fun z ↦ ∫ x, f x z ∂μ)) 0 z := by
    rw [mkD_apply_of_continuousOn]
    · rw [continuousOn_iff_continuous_domRestrict]
      refine continuous_congr key₁ |>.mpr ?_
      exact map_continuous (∫ x, mkD ((quasispectrum 𝕜 a).domRestrict (f x)) 0 ∂μ)
    · exact integral_eq_zero_of_ae hf₂
  simp_rw [cfcₙ_eq_cfcₙL_mkD _ a, cfcₙL_integral a _ hf₃ ha]
  congr
  ext z
  rw [← key₁, key₂]

open Set in
/-- The continuous functional calculus commutes with integration.
For a version with stronger assumptions which in practice are often easier to verify, see
`cfcₙ_setIntegral`. -/
/-
**cfc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{R : Type u_3} →   {A : Type u_4} →     {p : A → Prop} →       [inst : Com
mSemiring R] →         [inst_1 : StarRing R] →           [inst_2 : MetricSpace R
] →             [inst_3 : IsTopologicalSemiring R] →               [inst_4 : Con
tinuousStar R] →                 [inst_5 : TopologicalSpace A] →                
   [inst_6 : Ring A] →                     [inst_7 : StarRing A] →              
         [inst_8 : Algebra R A] → [instCFC : ContinuousFunctionalCalculus R A p]
 → (R → R) → A → A
参数：R → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The continuous functional calculus commutes with integration.
For a version with stronger assumptions which in practice are often easier to ve
rify, see
`cfcₙ_setIntegral`.
-/
lemma cfcₙ_setIntegral' {s : Set X} [NormedSpace ℝ A] (f : X → 𝕜 → 𝕜) (a : A)
    (hf₁ : ∀ᵐ x ∂(μ.restrict s), ContinuousOn (f x) (quasispectrum 𝕜 a))
    (hf₂ : ∀ᵐ x ∂(μ.restrict s), f x 0 = 0)
    (hf₃ : IntegrableOn
      (fun x : X => mkD ((quasispectrum 𝕜 a).domRestrict (f x)) 0) s μ)
    (ha : p a := by cfc_tac) :
    cfcₙ (fun z => ∫ x in s, f x z ∂μ) a = ∫ x in s, cfcₙ (f x) a ∂μ :=
  cfcₙ_integral' _ _ hf₁ hf₂ hf₃ ha

open Function Set in
/-- The continuous functional calculus commutes with integration.
This version assumes joint continuity of `f`, see `cfcₙ_integral'` for a statement
with weaker assumptions. -/
/-
**cfc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{R : Type u_3} →   {A : Type u_4} →     {p : A → Prop} →       [inst : Com
mSemiring R] →         [inst_1 : StarRing R] →           [inst_2 : MetricSpace R
] →             [inst_3 : IsTopologicalSemiring R] →               [inst_4 : Con
tinuousStar R] →                 [inst_5 : TopologicalSpace A] →                
   [inst_6 : Ring A] →                     [inst_7 : StarRing A] →              
         [inst_8 : Algebra R A] → [instCFC : ContinuousFunctionalCalculus R A p]
 → (R → R) → A → A
参数：R → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The continuous functional calculus commutes with integration.
This version assumes joint continuity of `f`, see `cfcₙ_integral'` for a stateme
nt
with weaker assumptions.
-/
lemma cfcₙ_integral [NormedSpace ℝ A] [TopologicalSpace X] [OpensMeasurableSpace X]
    (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A)
    [SecondCountableTopologyEither X C(quasispectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (univ ×ˢ quasispectrum 𝕜 a))
    (f_zero : ∀ᵐ x ∂μ, f x 0 = 0)
    (bound_ge : ∀ᵐ x ∂μ, ∀ z ∈ quasispectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    cfcₙ (fun r => ∫ x, f x r ∂μ) a = ∫ x, cfcₙ (f x) a ∂μ := by
  have : ∀ᵐ (x : X) ∂μ, ContinuousOn (f x) (quasispectrum 𝕜 a) := .of_forall fun x ↦
    hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨Set.mem_univ _, hz⟩
  refine cfcₙ_integral' _ _ this f_zero ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_mkD_restrict_of_uncurry _ _ hf f_zero
  · exact hasFiniteIntegral_mkD_restrict_of_bound f _ this f_zero bound bound_int bound_ge

open Function Set in
/-- The continuous functional calculus commutes with integration.
This version assumes joint continuity of `f`, see `cfcₙ_setIntegral'` for a statement
with weaker assumptions. -/
/-
**cfc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{R : Type u_3} →   {A : Type u_4} →     {p : A → Prop} →       [inst : Com
mSemiring R] →         [inst_1 : StarRing R] →           [inst_2 : MetricSpace R
] →             [inst_3 : IsTopologicalSemiring R] →               [inst_4 : Con
tinuousStar R] →                 [inst_5 : TopologicalSpace A] →                
   [inst_6 : Ring A] →                     [inst_7 : StarRing A] →              
         [inst_8 : Algebra R A] → [instCFC : ContinuousFunctionalCalculus R A p]
 → (R → R) → A → A
参数：R → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The continuous functional calculus commutes with integration.
This version assumes joint continuity of `f`, see `cfcₙ_setIntegral'` for a stat
ement
with weaker assumptions.
-/
lemma cfcₙ_setIntegral [NormedSpace ℝ A] [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
    (hs : MeasurableSet s) (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A)
    [SecondCountableTopologyEither X C(quasispectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (s ×ˢ quasispectrum 𝕜 a))
    (f_zero : ∀ᵐ x ∂(μ.restrict s), f x 0 = 0)
    (bound_ge : ∀ᵐ x ∂(μ.restrict s), ∀ z ∈ quasispectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    cfcₙ (fun r => ∫ x in s, f x r ∂μ) a = ∫ x in s, cfcₙ (f x) a ∂μ := by
  have : ∀ᵐ (x : X) ∂(μ.restrict s), ContinuousOn (f x) (quasispectrum 𝕜 a) :=
    ae_restrict_of_forall_mem hs fun x hx ↦
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨hx, hz⟩
  refine cfcₙ_setIntegral' _ _ this f_zero ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry hs _ _ hf f_zero
  · exact hasFiniteIntegral_mkD_restrict_of_bound f _ this f_zero bound bound_int bound_ge

end nonunital

