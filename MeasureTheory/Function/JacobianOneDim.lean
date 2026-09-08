/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Change of variable formulas for integrals in dimension 1

We record in this file versions of the general change of variables formula in integrals for
functions from `ℝ` to `ℝ`. This makes it possible to replace the determinant of the Fréchet
derivative with the one-dimensional derivative.

We also give more specific versions of these theorems for monotone and antitone functions: this
makes it possible to drop the injectivity assumption of the general theorems, as the derivative
is zero on the set of non-injectivity, which means that it can be discarded.

See also `Mathlib/MeasureTheory/Integral/IntervalIntegral/IntegrationByParts.lean` for versions of
the change of variables formula in dimension 1 for non-monotone functions, formulated with
the interval integral and with stronger requirements on the integrand.
-/

public section


open MeasureTheory MeasureTheory.Measure Metric Filter Set Module Asymptotics
  TopologicalSpace ContinuousLinearMap

open scoped NNReal ENNReal Topology Pointwise

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set ℝ} {f f' : ℝ → ℝ}
  {g : ℝ → F}

namespace MeasureTheory

/-- Integrability in the change of variable formula for differentiable functions (one-variable
version): if a function `f` is injective and differentiable on a measurable set `s ⊆ ℝ`, then the
Lebesgue integral of a function `g : ℝ → ℝ≥0∞` on `f '' s` coincides with the Lebesgue integral
of `|(f' x)| * g ∘ f` on `s`. -/
/-
**MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory`。
形式化陈述：lintegral_image_eq_lintegral_abs_deriv_mul (hs : MeasurableSet s) (hf' : f
orall x in s, HasDerivWithinAt f (f' x) s x) (hf : InjOn f s) (g : Real -> Real>
=0∞) : ∫⁻ x in f '' s, g x = ∫⁻ x in s, ENNReal.ofReal (|f' x|) * g (f x)
参数：hs : MeasurableSet s；hf' : forall x in s, HasDerivWithinAt f (f' x) s x；hf : 
InjOn f s；g : Real -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.det_toSpanSingleton`：det_toSpanSingleton {𝕜 : Type*}
 [CommRing 𝕜] [TopologicalSpace 𝕜] [ContinuousMul 𝕜] (v : 𝕜) : (toSpanSingleton 
𝕜 v).det = v
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`：lintegral
_image_eq_lintegral_abs_det_fderiv_mul (hs : MeasurableSet s) (hf' : forall x in
 s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `HasDerivWithinAt.hasFDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…

--- 原说明 ---
Integrability in the change of variable formula for differentiable functions (on
e-variable
version): if a function `f` is injective and differentiable on a measurable set 
`s ⊆ ℝ`, then the
Lebesgue integral of a function `g : ℝ → ℝ≥0∞` on `f '' s` coincides with the Le
besgue integral
of `|(f' x)| * g ∘ f` on `s`.
-/
theorem lintegral_image_eq_lintegral_abs_deriv_mul
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hf : InjOn f s)
    (g : ℝ → ℝ≥0∞) :
    ∫⁻ x in f '' s, g x = ∫⁻ x in s, ENNReal.ofReal (|f' x|) * g (f x) := by
  simpa only [det_toSpanSingleton] using
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
      (fun x hx => (hf' x hx).hasFDerivWithinAt) hf g

/-- Integrability in the change of variable formula for differentiable functions (one-variable
version): if a function `f` is injective and differentiable on a measurable set `s ⊆ ℝ`, then a
function `g : ℝ → F` is integrable on `f '' s` if and only if `|(f' x)| • g ∘ f` is integrable on
`s`. -/
/-
**MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrableOn_image_iff_integrableOn_abs_deriv_smul (hs : MeasurableSet s) 
(hf' : forall x in s, HasDerivWithinAt f (f' x) s x) (hf : InjOn f s) (g : Real 
-> F) : IntegrableOn g (f '' s) ↔ IntegrableOn (fun x => |f' x| • g (f x)) s
参数：hs : MeasurableSet s；hf' : forall x in s, HasDerivWithinAt f (f' x) s x；hf : 
InjOn f s；g : Real -> F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearMap.det_toSpanSingleton`：det_toSpanSingleton {𝕜 : Type*}
 [CommRing 𝕜] [TopologicalSpace 𝕜] [ContinuousMul 𝕜] (v : 𝕜) : (toSpanSingleton 
𝕜 v).det = v
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `MeasureTheory.integrableOn_image_iff_integrableOn_abs_det_fderiv_smul`：i
ntegrableOn_image_iff_integrableOn_abs_det_fderiv_smul (hs : MeasurableSet s) (h
f' : forall x in s, HasFDerivWithinAt f (f' x) s x) (hf : I…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `HasDerivWithinAt.hasFDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…

--- 原说明 ---
Integrability in the change of variable formula for differentiable functions (on
e-variable
version): if a function `f` is injective and differentiable on a measurable set 
`s ⊆ ℝ`, then a
function `g : ℝ → F` is integrable on `f '' s` if and only if `|(f' x)| • g ∘ f`
 is integrable on
`s`.
-/
theorem integrableOn_image_iff_integrableOn_abs_deriv_smul
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hf : InjOn f s)
    (g : ℝ → F) : IntegrableOn g (f '' s) ↔ IntegrableOn (fun x => |f' x| • g (f x)) s := by
  simpa only [det_toSpanSingleton] using
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs
      (fun x hx => (hf' x hx).hasFDerivWithinAt) hf g

/-- Change of variable formula for differentiable functions (one-variable version): if a function
`f` is injective and differentiable on a measurable set `s ⊆ ℝ`, then the Bochner integral of a
function `g : ℝ → F` on `f '' s` coincides with the integral of `|(f' x)| • g ∘ f` on `s`. -/
/-
**MeasureTheory.integral_image_eq_integral_abs_deriv_smul** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：integral_image_eq_integral_abs_deriv_smul (hs : MeasurableSet s) (hf' : fo
rall x in s, HasDerivWithinAt f (f' x) s x) (hf : InjOn f s) (g : Real -> F) : ∫
 x in f '' s, g x = ∫ x in s, |f' x| • g (f x)
参数：hs : MeasurableSet s；hf' : forall x in s, HasDerivWithinAt f (f' x) s x；hf : 
InjOn f s；g : Real -> F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.det_toSpanSingleton`：det_toSpanSingleton {𝕜 : Type*}
 [CommRing 𝕜] [TopologicalSpace 𝕜] [ContinuousMul 𝕜] (v : 𝕜) : (toSpanSingleton 
𝕜 v).det = v
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`：integral_i
mage_eq_integral_abs_det_fderiv_smul (hs : MeasurableSet s) (hf' : forall x in s
, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s)…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `HasDerivWithinAt.hasFDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…

--- 原说明 ---
Change of variable formula for differentiable functions (one-variable version): 
if a function
`f` is injective and differentiable on a measurable set `s ⊆ ℝ`, then the Bochne
r integral of a
function `g : ℝ → F` on `f '' s` coincides with the integral of `|(f' x)| • g ∘ 
f` on `s`.
-/
theorem integral_image_eq_integral_abs_deriv_smul
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hf : InjOn f s) (g : ℝ → F) : ∫ x in f '' s, g x = ∫ x in s, |f' x| • g (f x) := by
  simpa only [det_toSpanSingleton] using
    integral_image_eq_integral_abs_det_fderiv_smul volume hs
      (fun x hx => (hf' x hx).hasFDerivWithinAt) hf g

/-- Technical structure theorem for monotone differentiable functions.

If a function `f` is monotone on a measurable set and has a derivative `f'`, one can decompose
the set as a disjoint union `a ∪ b ∪ c` of measurable sets where `a` is countable (the points which
are isolated on the left or on the right, where `f'` is not well controlled),
`f` is locally constant on `b` and `f' = 0` there (the preimages of the countably many points with
several preimages), and `f` is injective on `c` with nonnegative derivative (the other points). -/
/-
**MeasureTheory.exists_decomposition_of_monotoneOn_hasDerivWithinAt** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：exists_decomposition_of_monotoneOn_hasDerivWithinAt (hs : MeasurableSet s)
 (hf : MonotoneOn f s) (hf' : forall x in s, HasDerivWithinAt f (f' x) s x) : ex
ists (a b c : Set Real), a union (b union c) = s ∧ MeasurableSet a ∧ MeasurableS
et b ∧ MeasurableSet c ∧ Disjoint a (b union c) ∧ Disjoint b c ∧ a.Countable ∧ (
f '' b).Countable ∧ (forall x in b, f' x = 0) ∧ (forall x in c, 0 <= f' x) ∧ Inj
On f c
参数：hs : MeasurableSet s；hf : MonotoneOn f s；hf' : forall x in s, HasDerivWithinA
t f (f' x) s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Set.Countable.union`：∀ {α : Type u} {s t : Set α}, s.Countable → t.Count
able → (s ∪ t).Countable
· 使用定理 `countable_setOfPred_isolated_right_within`：countable_setOfPred_isolated_
right_within [SecondCountableTopology α] {s : Set α} : { x in s | 𝓝[s inter Ioi 
x] x = ⊥ }.Countable
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `countable_setOfPred_isolated_left_within`：countable_setOfPred_isolated_l
eft_within [SecondCountableTopology α] {s : Set α} : { x in s | 𝓝[s inter Iio x]
 x = ⊥ }.Countable
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用定理 `Set.Countable.measurableSet`：Set.Countable.measurableSet {s : Set α} (hs
 : s.Countable) : MeasurableSet s
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `MonotoneOn.countable_setOfPred_two_preimages`：MonotoneOn.countable_setOf
Pred_two_preimages [SecondCountableTopology α] (hf : MonotoneOn f s) : Set.Count
able {c | exists x y, x in s ∧ y i…
· 使用定理 `MonotoneOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s s₂ : Set α} {f : α →
 β} [inst : Preorder α] [inst_1 : Preorder β],   MonotoneOn f s → s₂ ⊆ s → Monot
oneOn…
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
（共 90 条，此处仅展示前 30 条）

--- 原说明 ---
Technical structure theorem for monotone differentiable functions.

If a function `f` is monotone on a measurable set and has a derivative `f'`, one
 can decompose
the set as a disjoint union `a ∪ b ∪ c` of measurable sets where `a` is countabl
e (the points which
are isolated on the left or on the right, where `f'` is not well controlled),
`f` is locally constant on `b` and `f' = 0` there (the preimages of the countabl
y many points with
several preimages), and `f` is injective on `c` with nonnegative derivative (the
 other points).
-/
theorem exists_decomposition_of_monotoneOn_hasDerivWithinAt (hs : MeasurableSet s)
    (hf : MonotoneOn f s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) :
    ∃ (a b c : Set ℝ), a ∪ (b ∪ c) = s ∧ MeasurableSet a ∧ MeasurableSet b ∧ MeasurableSet c ∧
    Disjoint a (b ∪ c) ∧ Disjoint b c ∧ a.Countable ∧ (f '' b).Countable ∧
    (∀ x ∈ b, f' x = 0) ∧ (∀ x ∈ c, 0 ≤ f' x) ∧ InjOn f c := by
  let a := {x ∈ s | 𝓝[s ∩ Ioi x] x = ⊥} ∪ {x ∈ s | 𝓝[s ∩ Iio x] x = ⊥}
  have a_count : a.Countable :=
    countable_setOfPred_isolated_right_within.union countable_setOfPred_isolated_left_within
  let s₁ := s \ a
  have hs₁ : MeasurableSet s₁ := hs.diff a_count.measurableSet
  let u : Set ℝ := {c | ∃ x y, x ∈ s₁ ∧ y ∈ s₁ ∧ x < y ∧ f x = c ∧ f y = c}
  have hu : Set.Countable u := MonotoneOn.countable_setOfPred_two_preimages (hf.mono sdiff_subset)
  let b := s₁ ∩ f ⁻¹' u
  have hb : MeasurableSet b := by
    have : b = ⋃ z ∈ u, s₁ ∩ f ⁻¹' {z} := by ext; simp [b]
    rw [this]
    apply MeasurableSet.biUnion hu (fun z hz ↦ ?_)
    obtain ⟨v, hv, tv⟩ : ∃ v, OrdConnected v ∧ (s \ a) ∩ f ⁻¹' {z} = (s \ a) ∩ v :=
      ordConnected_singleton.preimage_monotoneOn (hf.mono sdiff_subset)
    exact tv ▸ (hs.diff a_count.measurableSet).inter hv.measurableSet
  let c := s₁ \ b
  have hc : MeasurableSet c := hs₁.diff hb
  refine ⟨a, b, c, ?_, a_count.measurableSet, hb, hc, ?_, ?_, a_count, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [sdiff_self_inter, inter_union_sdiff, union_sdiff_self, mem_union, mem_ofPred_eq,
      or_iff_right_iff_imp, a, b, s₁, c]
    tauto
  · simpa [b, c, s₁] using disjoint_sdiff_right
  · simpa [c] using disjoint_sdiff_right
  · exact hu.mono (by simp [b])
  · /- We have to show that the derivative is `0` at `x ∈ b`. For that, we use that there is another
    point `p` with `f p = f x`, by definition of `b`. If `p < x`, then `f` is locally constant to
    the left of `x`. As `x` is not isolated to its left (since we are not in the set `a`), it
    follows that `f' x = 0`. The same argument works if `x < p`, using the right neighborhood
    instead. -/
    intro x hx
    obtain ⟨p, ps₁, px, fpx⟩ : ∃ p ∈ s₁, p ≠ x ∧ f p = f x := by
      rcases hx.2 with ⟨p, q, ps₁, qs₁, pq, hp, hq⟩
      rcases eq_or_ne p x with h'p | h'p
      · exact ⟨q, qs₁, (h'p.symm.le.trans_lt pq).ne', hq⟩
      · exact ⟨p, ps₁, h'p, hp⟩
    -- we treat separately the cases `p < x` and `x < p` as we couldn't unify their proofs nicely
    rcases lt_or_gt_of_ne px with px | px
    · have K : HasDerivWithinAt f 0 (s ∩ Ioo p x) x := by
        have E (y) (hy : y ∈ s ∩ Ioo p x) : f y = f x := by
          apply le_antisymm (hf hy.1 hx.1.1 hy.2.2.le)
          rw [← fpx]
          exact hf ps₁.1 hy.1 hy.2.1.le
        have : HasDerivWithinAt (fun y ↦ f x) 0 (s ∩ Ioo p x) x :=
          hasDerivWithinAt_const x (s ∩ Ioo p x) (f x)
        exact this.congr E rfl
      have K' : HasDerivWithinAt f (f' x) (s ∩ Ioo p x) x :=
        (hf' x hx.1.1).mono inter_subset_left
      apply UniqueDiffWithinAt.eq_deriv _ _ K' K
      have J1 : (s ∩ Ioo p x) \ {x} = s ∩ Ioo p x := by simp
      have J2 : 𝓝[s ∩ Ioo p x] x = 𝓝[s ∩ Iio x] x := by
        simp [nhdsWithin_inter, nhdsWithin_Ioo_eq_nhdsLT px]
      rw [uniqueDiffWithinAt_iff_accPt, accPt_principal_iff_nhdsWithin, J1, J2]
      simp only [mem_inter_iff, Set.mem_sdiff, hx.1.1, mem_union, mem_ofPred_eq, true_and, not_or,
        mem_preimage, b, s₁, a] at hx
      exact neBot_iff.2 hx.1.2
    · have K : HasDerivWithinAt f 0 (s ∩ Ioo x p) x := by
        have E (y) (hy : y ∈ s ∩ Ioo x p) : f y = f x := by
          apply le_antisymm _ (hf hx.1.1 hy.1 hy.2.1.le)
          rw [← fpx]
          exact hf hy.1 ps₁.1 hy.2.2.le
        have : HasDerivWithinAt (fun y ↦ f x) 0 (s ∩ Ioo x p) x :=
          hasDerivWithinAt_const x (s ∩ Ioo x p) (f x)
        exact this.congr E rfl
      have K' : HasDerivWithinAt f (f' x) (s ∩ Ioo x p) x :=
        (hf' x hx.1.1).mono inter_subset_left
      apply UniqueDiffWithinAt.eq_deriv _ _ K' K
      have J1 : (s ∩ Ioo x p) \ {x} = (s ∩ Ioo x p) := by simp
      have J2 : 𝓝[s ∩ Ioo x p] x = 𝓝[s ∩ Ioi x] x := by
        simp [nhdsWithin_inter, nhdsWithin_Ioo_eq_nhdsGT px]
      rw [uniqueDiffWithinAt_iff_accPt, accPt_principal_iff_nhdsWithin, J1, J2]
      simp only [mem_inter_iff, Set.mem_sdiff, hx.1.1, mem_union, mem_ofPred_eq, true_and, not_or,
        mem_preimage, b, s₁, a] at hx
      exact neBot_iff.2 hx.1.1
  · /- We have to show that the derivative is nonnegative at points of `c`. As these points are
    not isolated in `s`, this follows from the fact that `f` is monotone on `s`. -/
    intro x hx
    apply (hf' x hx.1.1).nonneg_of_monotoneOn _ hf
    simp only [Set.mem_sdiff, hx.1.1, mem_union, mem_ofPred_eq, true_and, not_or, c, s₁, a, b] at hx
    rw [accPt_principal_iff_nhdsWithin]
    have : (𝓝[s ∩ Iio x] x).NeBot := neBot_iff.2 hx.1.2
    apply this.mono
    apply nhdsWithin_mono
    rintro y ⟨yt, yx : y < x⟩
    exact ⟨yt, by simpa using yx.ne⟩
  · intro x hx y hy hxy
    contrapose! hxy
    wlog H : x < y generalizing x y with h
    · have : y < x := by order
      exact (h hy hx hxy.symm this).symm
    refine fun h ↦ hx.2 ⟨hx.1, ?_⟩
    exact ⟨x, y, hx.1, hy.1, H, rfl, h.symm⟩

/-- Change of variable formula for differentiable functions: if a real function `f` is
monotone and differentiable on a measurable set `s`, then the Lebesgue integral of a function
`u : ℝ → ℝ≥0∞` on `f '' s` coincides with the integral of `(f' x) * u ∘ f` on `s`.
Note that the measurability of `f '' s` is given by `MeasurableSet.image_of_monotoneOn`. -/
/-
**MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn (hs : MeasurableSet s
) (hf' : forall x in s, HasDerivWithinAt f (f' x) s x) (hf : MonotoneOn f s) (u 
: Real -> Real>=0∞) : ∫⁻ x in f '' s, u x = ∫⁻ x in s, ENNReal.ofReal (f' x) * u
 (f x)
参数：hs : MeasurableSet s；hf' : forall x in s, HasDerivWithinAt f (f' x) s x；hf : 
MonotoneOn f s；u : Real -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.exists_decomposition_of_monotoneOn_hasDerivWithinAt`：exist
s_decomposition_of_monotoneOn_hasDerivWithinAt (hs : MeasurableSet s) (hf : Mono
toneOn f s) (hf' : forall x in s, HasDerivWithinAt f (f…
· 使用定理 `MeasureTheory.setLIntegral_measure_zero`：setLIntegral_measure_zero (s : 
Set α) (f : α -> Real>=0∞) (hs' : μ s = 0) : ∫⁻ x in s, f x ∂μ = 0
· 使用定理 `Set.Countable.measure_zero`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {s
 : Set α},   s.Countable → ∀ (μ : MeasureTheory.Measure α) [MeasureTheory.NullSi
ngletonClass μ],…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_union`：lintegral_union {f : α -> Real>=0∞} {A B 
: Set α} (hB : MeasurableSet B) (hAB : Disjoint A B) : ∫⁻ a in A union B, f a ∂μ
 = ∫⁻ a in A, f a ∂…
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `MeasureTheory.setLIntegral_eq_zero`：setLIntegral_eq_zero {f : α -> Real>
=0∞} {s : Set α} (hs : MeasurableSet s) (h's : EqOn f 0 s) : ∫⁻ x in s, f x ∂μ =
 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.setLIntegral_congr`：setLIntegral_congr {f : α -> Real>=0∞}
 {s t : Set α} (h : s =ᵐ[μ] t) : ∫⁻ x in s, f x ∂μ = ∫⁻ x in t, f x ∂μ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
· 使用定理 `MeasureTheory.union_ae_eq_right_of_ae_eq_empty`：union_ae_eq_right_of_ae_
eq_empty (h : s =ᵐ[μ] (∅ : Set α)) : (s union t : Set α) =ᵐ[μ] t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_eq_empty`：ae_eq_empty : s =ᵐ[μ] (∅ : Set α) ↔ μ s = 0
· 使用定理 `Set.Countable.image`：∀ {α : Type u} {β : Type v} {s : Set α}, s.Countabl
e → ∀ (f : α → β), (f '' s).Countable
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `HasFDerivWithinAt.mono`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [ins
t_3 : Topolo…
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
Change of variable formula for differentiable functions: if a real function `f` 
is
monotone and differentiable on a measurable set `s`, then the Lebesgue integral 
of a function
`u : ℝ → ℝ≥0∞` on `f '' s` coincides with the integral of `(f' x) * u ∘ f` on `s
`.
Note that the measurability of `f '' s` is given by `MeasurableSet.image_of_mono
toneOn`.
-/
theorem lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hf : MonotoneOn f s) (u : ℝ → ℝ≥0∞) :
    ∫⁻ x in f '' s, u x = ∫⁻ x in s, ENNReal.ofReal (f' x) * u (f x) := by
  rcases exists_decomposition_of_monotoneOn_hasDerivWithinAt hs hf hf' with
    ⟨a, b, c, h_union, ha, hb, hc, h_disj, h_disj', a_count, fb_count, deriv_b, deriv_c, inj_c⟩
  have I : ∫⁻ x in s, ENNReal.ofReal (f' x) * u (f x)
      = ∫⁻ x in c, ENNReal.ofReal (f' x) * u (f x) := by
    have : ∫⁻ x in a, ENNReal.ofReal (f' x) * u (f x) = 0 :=
      setLIntegral_measure_zero a _ (a_count.measure_zero volume)
    rw [← h_union, lintegral_union (hb.union hc) h_disj, this, zero_add]
    have : ∫⁻ x in b, ENNReal.ofReal (f' x) * u (f x) = 0 :=
      setLIntegral_eq_zero hb (fun x hx ↦ by simp [deriv_b x hx])
    rw [lintegral_union hc h_disj', this, zero_add]
  have J : ∫⁻ x in f '' s, u x = ∫⁻ x in f '' c, u x := by
    apply setLIntegral_congr
    rw [← h_union, image_union, image_union]
    have A : (f '' a ∪ (f '' b ∪ f '' c) : Set ℝ) =ᵐ[volume] (f '' b ∪ f '' c : Set ℝ) := by
      refine union_ae_eq_right_of_ae_eq_empty (ae_eq_empty.mpr ?_)
      exact (a_count.image _).measure_zero _
    have B : (f '' b ∪ f '' c : Set ℝ) =ᵐ[volume] f '' c :=
      union_ae_eq_right_of_ae_eq_empty (ae_eq_empty.mpr (fb_count.measure_zero _))
    exact A.trans B
  rw [I, J]
  have c_s : c ⊆ s := by rw [← h_union]; exact subset_union_right.trans subset_union_right
  let F' : ℝ → (ℝ →L[ℝ] ℝ) := fun x ↦ ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (f' x)
  have hf' (x : ℝ) (hx : x ∈ c) : HasFDerivWithinAt f (F' x) c x :=
    (hf' x (c_s hx)).hasFDerivWithinAt.mono c_s
  have : ∫⁻ x in c, ENNReal.ofReal (f' x) * u (f x)
      = ∫⁻ x in c, ENNReal.ofReal (|(F' x).det|) * u (f x) := by
    apply setLIntegral_congr_fun hc (fun x hx ↦ ?_)
    simp only [LinearMap.det_ring, ContinuousLinearMap.coe_coe, ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self, smul_eq_mul, one_mul, F']
    rw [abs_of_nonneg (deriv_c x hx)]
  rw [this]
  exact lintegral_image_eq_lintegral_abs_det_fderiv_mul _ hc hf' inj_c _

/-- Change of variable formula for differentiable functions, set version: if a real function `f` is
monotone and differentiable on a measurable set `s`, then the measure of `f '' s` is given by the
integral of `f' x` on `s` .
Note that the measurability of `f '' s` is given by `MeasurableSet.image_of_monotoneOn`. -/
/-
**MeasureTheory.lintegral_deriv_eq_volume_image_of_monotoneOn** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_deriv_eq_volume_image_of_monotoneOn (hs : MeasurableSet s) (hf' 
: forall x in s, HasDerivWithinAt f (f' x) s x) (hf : MonotoneOn f s) : (∫⁻ x in
 s, ENNReal.ofReal (f' x)) = volume (f '' s)
参数：hs : MeasurableSet s；hf' : forall x in s, HasDerivWithinAt f (f' x) s x；hf : 
MonotoneOn f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn`：lint
egral_image_eq_lintegral_deriv_mul_of_monotoneOn (hs : MeasurableSet s) (hf' : f
orall x in s, HasDerivWithinAt f (f' x) s x) (hf : Monot…

--- 原说明 ---
Change of variable formula for differentiable functions, set version: if a real 
function `f` is
monotone and differentiable on a measurable set `s`, then the measure of `f '' s
` is given by the
integral of `f' x` on `s` .
Note that the measurability of `f '' s` is given by `MeasurableSet.image_of_mono
toneOn`.
-/
theorem lintegral_deriv_eq_volume_image_of_monotoneOn (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hf : MonotoneOn f s) :
    (∫⁻ x in s, ENNReal.ofReal (f' x)) = volume (f '' s) := by
  simpa using (lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn hs hf' hf 1).symm

/-- Integrability in the change of variable formula for differentiable functions: if a real
function `f` is monotone and differentiable on a measurable set `s`, then a function
`g : ℝ → F` is integrable on `f '' s` if and only if `f' x • g ∘ f` is integrable on `s` . -/
/-
**MeasureTheory.integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn** 是
 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn (hs : Measura
bleSet s) (hf' : forall x in s, HasDerivWithinAt f (f' x) s x) (hf : MonotoneOn 
f s) (g : Real -> F) : IntegrableOn g (f '' s) ↔ IntegrableOn (fun x => (f' x) •
 g (f x)) s
参数：hs : MeasurableSet s；hf' : forall x in s, HasDerivWithinAt f (f' x) s x；hf : 
MonotoneOn f s；g : Real -> F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.exists_decomposition_of_monotoneOn_hasDerivWithinAt`：exist
s_decomposition_of_monotoneOn_hasDerivWithinAt (hs : MeasurableSet s) (hf : Mono
toneOn f s) (hf' : forall x in s, HasDerivWithinAt f (f…
· 使用定理 `MeasureTheory.IntegrableOn.of_measure_zero`：∀ {α : Type u_1} {ε : Type u
_3} {mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure 
α}   [inst : TopologicalSpace ε]…
· 使用定理 `Set.Countable.measure_zero`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {s
 : Set α},   s.Countable → ∀ (μ : MeasureTheory.Measure α) [MeasureTheory.NullSi
ngletonClass μ],…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `MeasureTheory.IntegrableOn.congr_fun`：∀ {α : Type u_1} {ε : Type u_3} {m
α : MeasurableSpace α} {f g : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}  
 [inst : TopologicalSpace …
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasureTheory.integrableOn_congr_set_ae`：integrableOn_congr_set_ae (hst 
: s =ᵐ[μ] t) : IntegrableOn f s μ ↔ IntegrableOn f t μ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
· 使用定理 `MeasureTheory.union_ae_eq_right_of_ae_eq_empty`：union_ae_eq_right_of_ae_
eq_empty (h : s =ᵐ[μ] (∅ : Set α)) : (s union t : Set α) =ᵐ[μ] t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_eq_empty`：ae_eq_empty : s =ᵐ[μ] (∅ : Set α) ↔ μ s = 0
· 使用定理 `Set.Countable.image`：∀ {α : Type u} {β : Type v} {s : Set α}, s.Countabl
e → ∀ (f : α → β), (f '' s).Countable
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
Integrability in the change of variable formula for differentiable functions: if
 a real
function `f` is monotone and differentiable on a measurable set `s`, then a func
tion
`g : ℝ → F` is integrable on `f '' s` if and only if `f' x • g ∘ f` is integrabl
e on `s` .
-/
theorem integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hf : MonotoneOn f s) (g : ℝ → F) :
    IntegrableOn g (f '' s) ↔ IntegrableOn (fun x ↦ (f' x) • g (f x)) s := by
  rcases exists_decomposition_of_monotoneOn_hasDerivWithinAt hs hf hf' with
    ⟨a, b, c, h_union, ha, hb, hc, h_disj, h_disj', a_count, fb_count, deriv_b, deriv_c, inj_c⟩
  have I : IntegrableOn (fun x => (f' x) • g (f x)) s
      ↔ IntegrableOn (fun x => (f' x) • g (f x)) c := by
    have A : IntegrableOn (fun x ↦ f' x • g (f x)) a :=
      IntegrableOn.of_measure_zero (a_count.measure_zero volume)
    have B : IntegrableOn (fun x ↦ f' x • g (f x)) b := by
      have : IntegrableOn (fun x ↦ (0 : F)) b := by simp
      exact this.congr_fun (fun x hx ↦ by simp [deriv_b x hx]) hb
    simp only [← h_union, integrableOn_union, A, B, true_and]
  have J : IntegrableOn g (f '' s) ↔ IntegrableOn g (f '' c) := by
    apply integrableOn_congr_set_ae
    rw [← h_union, image_union, image_union]
    have A : (f '' a ∪ (f '' b ∪ f '' c) : Set ℝ) =ᵐ[volume] (f '' b ∪ f '' c : Set ℝ) := by
      refine union_ae_eq_right_of_ae_eq_empty (ae_eq_empty.mpr ?_)
      exact (a_count.image _).measure_zero _
    have B : (f '' b ∪ f '' c : Set ℝ) =ᵐ[volume] f '' c :=
      union_ae_eq_right_of_ae_eq_empty (ae_eq_empty.mpr (fb_count.measure_zero _))
    exact A.trans B
  rw [I, J]
  have c_s : c ⊆ s := by rw [← h_union]; exact subset_union_right.trans subset_union_right
  let F' : ℝ → (ℝ →L[ℝ] ℝ) := fun x ↦ ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (f' x)
  have hF' (x : ℝ) (hx : x ∈ c) : HasFDerivWithinAt f (F' x) c x :=
    (hf' x (c_s hx)).hasFDerivWithinAt.mono c_s
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul _ hc hF' inj_c]
  apply integrableOn_congr_fun (fun x hx ↦ ?_) hc
  simp only [LinearMap.det_ring, ContinuousLinearMap.coe_coe, ContinuousLinearMap.smulRight_apply,
    one_apply_eq_self, smul_eq_mul, one_mul, F']
  rw [abs_of_nonneg (deriv_c x hx)]

/-- Change of variable formula for differentiable functions: if a real function `f` is
monotone and differentiable on a measurable set `s`, then the Bochner integral of a function
`g : ℝ → F` on `f '' s` coincides with the integral of `(f' x) • g ∘ f` on `s` . -/
/-
**MeasureTheory.integral_image_eq_integral_deriv_smul_of_monotoneOn** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_image_eq_integral_deriv_smul_of_monotoneOn (hs : MeasurableSet s)
 (hf' : forall x in s, HasDerivWithinAt f (f' x) s x) (hf : MonotoneOn f s) (g :
 Real -> F) : ∫ x in f '' s, g x = ∫ x in s, f' x • g (f x)
参数：hs : MeasurableSet s；hf' : forall x in s, HasDerivWithinAt f (f' x) s x；hf : 
MonotoneOn f s；g : Real -> F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.integrableOn_image_iff_integrableOn_deriv_smul_of_monotone
On`：integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn (hs : Measurabl
eSet s) (hf' : forall x in s, HasDerivWithinAt f (f' x) s x) (hf…
· 使用定理 `MeasureTheory.exists_decomposition_of_monotoneOn_hasDerivWithinAt`：exist
s_decomposition_of_monotoneOn_hasDerivWithinAt (hs : MeasurableSet s) (hf : Mono
toneOn f s) (hf' : forall x in s, HasDerivWithinAt f (f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.setIntegral_measure_zero`：setIntegral_measure_zero (f : α 
-> G) {μ : Measure α} {s : Set α} (hs : μ s = 0) : ∫ x in s, f x ∂μ = 0
· 使用定理 `Set.Countable.measure_zero`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {s
 : Set α},   s.Countable → ∀ (μ : MeasureTheory.Measure α) [MeasureTheory.NullSi
ngletonClass μ],…
· 使用定理 `MeasureTheory.setIntegral_union`：setIntegral_union (hst : Disjoint s t) 
(ht : MeasurableSet t) (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ) : ∫
 x in s union t, f x …
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero`：setIntegral_eq_zero
_of_forall_eq_zero (ht_eq : forall x in t, f x = 0) : ∫ x in t, f x ∂μ = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.setIntegral_congr_set`：setIntegral_congr_set (hst : s =ᵐ[μ
] t) : ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
· 使用定理 `MeasureTheory.union_ae_eq_right_of_ae_eq_empty`：union_ae_eq_right_of_ae_
eq_empty (h : s =ᵐ[μ] (∅ : Set α)) : (s union t : Set α) =ᵐ[μ] t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_eq_empty`：ae_eq_empty : s =ᵐ[μ] (∅ : Set α) ↔ μ s = 0
· 使用定理 `Set.Countable.image`：∀ {α : Type u} {β : Type v} {s : Set α}, s.Countabl
e → ∀ (f : α → β), (f '' s).Countable
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
Change of variable formula for differentiable functions: if a real function `f` 
is
monotone and differentiable on a measurable set `s`, then the Bochner integral o
f a function
`g : ℝ → F` on `f '' s` coincides with the integral of `(f' x) • g ∘ f` on `s` .
-/
theorem integral_image_eq_integral_deriv_smul_of_monotoneOn (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hf : MonotoneOn f s) (g : ℝ → F) :
    ∫ x in f '' s, g x = ∫ x in s, f' x • g (f x) := by
  by_cases H : IntegrableOn g (f '' s); swap
  · rw [integral_undef H, integral_undef]
    simpa [integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn hs hf' hf] using! H
  have H' : IntegrableOn (fun x ↦ (f' x) • g (f x)) s :=
    (integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn hs hf' hf g).1 H
  rcases exists_decomposition_of_monotoneOn_hasDerivWithinAt hs hf hf' with
    ⟨a, b, c, h_union, ha, hb, hc, h_disj, h_disj', a_count, fb_count, deriv_b, deriv_c, inj_c⟩
  have a_s : a ⊆ s := by rw [← h_union]; exact subset_union_left
  have bc_s : b ∪ c ⊆ s := by rw [← h_union]; exact subset_union_right
  have b_s : b ⊆ s := by rw [← h_union]; exact subset_union_left.trans subset_union_right
  have c_s : c ⊆ s := by rw [← h_union]; exact subset_union_right.trans subset_union_right
  have I : ∫ x in s, f' x • g (f x) = ∫ x in c, f' x • g (f x) := by
    have : ∫ x in a, f' x • g (f x) = 0 :=
      setIntegral_measure_zero _ (a_count.measure_zero volume)
    rw [← h_union, setIntegral_union h_disj (hb.union hc) (H'.mono_set a_s) (H'.mono_set bc_s),
      this, zero_add]
    have : ∫ x in b, f' x • g (f x) = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero (fun x hx ↦ by simp [deriv_b x hx])
    rw [setIntegral_union h_disj' hc (H'.mono_set b_s) (H'.mono_set c_s), this, zero_add]
  have J : ∫ x in f '' s, g x = ∫ x in f '' c, g x := by
    apply setIntegral_congr_set
    rw [← h_union, image_union, image_union]
    have A : (f '' a ∪ (f '' b ∪ f '' c) : Set ℝ) =ᵐ[volume] (f '' b ∪ f '' c : Set ℝ) := by
      refine union_ae_eq_right_of_ae_eq_empty (ae_eq_empty.mpr ?_)
      exact (a_count.image _).measure_zero _
    have B : (f '' b ∪ f '' c : Set ℝ) =ᵐ[volume] f '' c :=
      union_ae_eq_right_of_ae_eq_empty (ae_eq_empty.mpr (fb_count.measure_zero _))
    exact A.trans B
  rw [I, J]
  let F' : ℝ → (ℝ →L[ℝ] ℝ) := fun x ↦ ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (f' x)
  have hF' (x : ℝ) (hx : x ∈ c) : HasFDerivWithinAt f (F' x) c x :=
    (hf' x (c_s hx)).hasFDerivWithinAt.mono c_s
  have : ∫ x in c, f' x • g (f x) = ∫ x in c, |(F' x).det| • g (f x) := by
    apply setIntegral_congr_fun hc (fun x hx ↦ ?_)
    simp only [LinearMap.det_ring, ContinuousLinearMap.coe_coe, ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self, smul_eq_mul, one_mul, F']
    rw [abs_of_nonneg (deriv_c x hx)]
  rw [this]
  exact integral_image_eq_integral_abs_det_fderiv_smul _ hc hF' inj_c _
/-
**MeasureTheory.integral_Icc_deriv_smul_of_deriv_nonneg** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：integral_Icc_deriv_smul_of_deriv_nonneg {a b : Real} {g : Real -> F} (hf :
 ContinuousOn f (Icc a b)) (hff' : forall x in Ioo a b, HasDerivAt f (f' x) x) (
hf' : forall x in Ioo a b, 0 <= f' x) (hab : a <= b) : ∫ x in Icc a b, f' x • g 
(f x) = ∫ u in Icc (f a) (f b), g u
参数：hf : ContinuousOn f (Icc a b)；hff' : forall x in Ioo a b, HasDerivAt f (f' x)
 x；hf' : forall x in Ioo a b, 0 <= f' x；hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `monotoneOn_of_deriv_nonneg`：monotoneOn_of_deriv_nonneg {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Icc`：convex_Icc (r s : β) : Convex 𝕜 (Icc r s)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_Icc`：interior_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} : int
erior (Icc a b) = Ioo a b
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
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `MeasureTheory.setIntegral_congr_set`：setIntegral_congr_set (hst : s =ᵐ[μ
] t) : ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousOn.image_Icc_of_monotoneOn`：ContinuousOn.image_Icc_of_monotone
On (hab : a <= b) (hf : ContinuousOn f (Icc a b)) (hmono : MonotoneOn f (Icc a b
)) : f '' Icc a b = Icc (f…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_eq_set`：ae_eq_set {s t : Set α} : s =ᵐ[μ] t ↔ μ (s \ t)
 = 0 ∧ μ (t \ s) = 0
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `Set.Finite.measure_zero`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {s : 
Set α},   s.Finite → ∀ (μ : MeasureTheory.Measure α) [MeasureTheory.NullSingleto
nClass μ], μ …
（共 42 条，此处仅展示前 30 条）
-/
theorem integral_Icc_deriv_smul_of_deriv_nonneg {a b : ℝ} {g : ℝ → F}
    (hf : ContinuousOn f (Icc a b))
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Ioo a b, 0 ≤ f' x) (hab : a ≤ b) :
    ∫ x in Icc a b, f' x • g (f x) = ∫ u in Icc (f a) (f b), g u := by
  have M : MonotoneOn f (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hf
    · rw [interior_Icc]
      exact fun z hz ↦ (hff' z hz).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro z hz
      simpa [(hff' z hz).deriv] using hf' z hz
  have A : ∫ u in Icc (f a) (f b), g u = ∫ u in f '' (Ioo a b), g u := by
    apply setIntegral_congr_set
    rw [← hf.image_Icc_of_monotoneOn hab M]
    refine ae_eq_set.2 ⟨?_, by simp [show f '' Ioo a b \ f '' Icc a b = ∅ by grind]⟩
    have : f '' (Icc a b) \ f '' Ioo a b ⊆ {f a, f b} := by grind
    apply measure_mono_null this
    apply Finite.measure_zero (by simp)
  rw [A, integral_Icc_eq_integral_Ioo,
    integral_image_eq_integral_deriv_smul_of_monotoneOn measurableSet_Ioo]
  · exact fun z hz ↦ (hff' z hz).hasDerivWithinAt
  · exact M.mono Ioo_subset_Icc_self
/-
**MeasureTheory.integrableOn_Icc_deriv_smul_iff_of_deriv_nonneg** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrableOn_Icc_deriv_smul_iff_of_deriv_nonneg {a b : Real} {g : Real -> 
F} (hf : ContinuousOn f (Icc a b)) (hff' : forall x in Ioo a b, HasDerivAt f (f'
 x) x) (hf' : forall x in Ioo a b, 0 <= f' x) (hab : a <= b) : IntegrableOn (fun
 x => (f' x) • g (f x)) (Icc a b) ↔ IntegrableOn g (Icc (f a) (f b))
参数：hf : ContinuousOn f (Icc a b)；hff' : forall x in Ioo a b, HasDerivAt f (f' x)
 x；hf' : forall x in Ioo a b, 0 <= f' x；hab : a <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `monotoneOn_of_deriv_nonneg`：monotoneOn_of_deriv_nonneg {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Icc`：convex_Icc (r s : β) : Convex 𝕜 (Icc r s)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_Icc`：interior_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} : int
erior (Icc a b) = Ioo a b
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
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `MeasureTheory.integrableOn_congr_set_ae`：integrableOn_congr_set_ae (hst 
: s =ᵐ[μ] t) : IntegrableOn f s μ ↔ IntegrableOn f t μ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousOn.image_Icc_of_monotoneOn`：ContinuousOn.image_Icc_of_monotone
On (hab : a <= b) (hf : ContinuousOn f (Icc a b)) (hmono : MonotoneOn f (Icc a b
)) : f '' Icc a b = Icc (f…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_eq_set`：ae_eq_set {s t : Set α} : s =ᵐ[μ] t ↔ μ (s \ t)
 = 0 ∧ μ (t \ s) = 0
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `Set.Finite.measure_zero`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {s : 
Set α},   s.Finite → ∀ (μ : MeasureTheory.Measure α) [MeasureTheory.NullSingleto
nClass μ], μ …
（共 56 条，此处仅展示前 30 条）
-/
theorem integrableOn_Icc_deriv_smul_iff_of_deriv_nonneg {a b : ℝ} {g : ℝ → F}
    (hf : ContinuousOn f (Icc a b))
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Ioo a b, 0 ≤ f' x) (hab : a ≤ b) :
    IntegrableOn (fun x ↦ (f' x) • g (f x)) (Icc a b) ↔ IntegrableOn g (Icc (f a) (f b)) := by
  have M : MonotoneOn f (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hf
    · rw [interior_Icc]
      exact fun z hz ↦ (hff' z hz).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro z hz
      simpa [(hff' z hz).deriv] using hf' z hz
  have A : IntegrableOn g (Icc (f a) (f b)) ↔ IntegrableOn g (f '' (Ioo a b)) := by
    apply integrableOn_congr_set_ae
    rw [← hf.image_Icc_of_monotoneOn hab M]
    refine ae_eq_set.2 ⟨?_, by simp [show f '' Ioo a b \ f '' Icc a b = ∅ by grind]⟩
    have : f '' (Icc a b) \ f '' Ioo a b ⊆ {f a, f b} := by grind
    apply measure_mono_null this
    apply Finite.measure_zero (by simp)
  rw [A, integrableOn_Icc_iff_integrableOn_Ioo,
    integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn measurableSet_Ioo]
  · exact fun z hz ↦ (hff' z hz).hasDerivWithinAt
  · exact M.mono Ioo_subset_Icc_self

/-- Change of variable formula for differentiable functions: if a real function `f` is
antitone and differentiable on a measurable set `s`, then the Lebesgue integral of a function
`u : ℝ → ℝ≥0∞` on `f '' s` coincides with the integral of `(-f' x) * u ∘ f` on `s`.
Note that the measurability of `f '' s` is given by `MeasurableSet.image_of_antitoneOn`. -/
/-
**MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn (hs : MeasurableSet s
) (hf' : forall x in s, HasDerivWithinAt f (f' x) s x) (hf : AntitoneOn f s) (u 
: Real -> Real>=0∞) : ∫⁻ x in f '' s, u x = ∫⁻ x in s, ENNReal.ofReal (-f' x) * 
u (f x)
参数：hs : MeasurableSet s；hf' : forall x in s, HasDerivWithinAt f (f' x) s x；hf : 
AntitoneOn f s；u : Real -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasDerivWithinAt.neg`：HasDerivWithinAt.neg (h : HasDerivWithinAt f f' s 
x) : HasDerivWithinAt (-f) (-f') s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn`：lint
egral_image_eq_lintegral_deriv_mul_of_monotoneOn (hs : MeasurableSet s) (hf' : f
orall x in s, HasDerivWithinAt f (f' x) s x) (hf : Monot…
· 使用定理 `AntitoneOn.neg`：∀ {α : Type u} {β : Type u_1} [inst : AddGroup α] [inst_
1 : Preorder α] [AddLeftMono α] [AddRightMono α]   [inst_4 : Preorder β] {f : β 
→ α}…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul`：lintegral_imag
e_eq_lintegral_abs_deriv_mul (hs : MeasurableSet s) (hf' : forall x in s, HasDer
ivWithinAt f (f' x) s x) (hf : InjOn f s) (g :…
· 使用定理 `MeasurableSet.image_of_monotoneOn`：MeasurableSet.image_of_monotoneOn [Se
condCountableTopology β] (ht : MeasurableSet t) (hg : MonotoneOn g t) : Measurab
leSet (g '' t)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `hasDerivWithinAt_neg`：hasDerivWithinAt_neg : HasDerivWithinAt Neg.neg (-
1) s x
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `neg_injective`：∀ {G : Type u_3} [inst : InvolutiveNeg G], Function.Injec
tive Neg.neg
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
Change of variable formula for differentiable functions: if a real function `f` 
is
antitone and differentiable on a measurable set `s`, then the Lebesgue integral 
of a function
`u : ℝ → ℝ≥0∞` on `f '' s` coincides with the integral of `(-f' x) * u ∘ f` on `
s`.
Note that the measurability of `f '' s` is given by `MeasurableSet.image_of_anti
toneOn`.
-/
theorem lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hf : AntitoneOn f s) (u : ℝ → ℝ≥0∞) :
    ∫⁻ x in f '' s, u x = ∫⁻ x in s, ENNReal.ofReal (-f' x) * u (f x) := by
  let n : ℝ → ℝ := (fun x ↦ -x)
  let e := n ∘ f
  have hg' (x) (hx : x ∈ s) : HasDerivWithinAt e (-f' x) s x := (hf' x hx).neg
  have A : ∫⁻ x in e '' s, u (n x) = ∫⁻ x in s, ENNReal.ofReal (-f' x) * (u ∘ n) (e x) := by
    rw [← lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn hs hg' hf.neg (u ∘ n)]; rfl
  have B : ∫⁻ x in n '' e '' s, u x = ∫⁻ x in e '' s, ENNReal.ofReal (|-1|) * u (n x) :=
    lintegral_image_eq_lintegral_abs_deriv_mul (hs.image_of_monotoneOn hf.neg)
      (fun x hx ↦ hasDerivWithinAt_neg _ _) neg_injective.injOn _
  simp only [abs_neg, abs_one, ENNReal.ofReal_one, one_mul] at B
  rw [A, ← image_comp] at B
  convert! B using 4 with x hx x <;> simp [n, e]

/-- Change of variable formula for differentiable functions, set version: if a real function `f` is
antitone and differentiable on a measurable set `s`, then the measure of `f '' s` is given by the
integral of `-f' x` on `s` .
Note that the measurability of `f '' s` is given by `MeasurableSet.image_of_antitoneOn`. -/
/-
**MeasureTheory.lintegral_deriv_eq_volume_image_of_antitoneOn** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_deriv_eq_volume_image_of_antitoneOn (hs : MeasurableSet s) (hf' 
: forall x in s, HasDerivWithinAt f (f' x) s x) (hf : AntitoneOn f s) : (∫⁻ x in
 s, ENNReal.ofReal (-f' x)) = volume (f '' s)
参数：hs : MeasurableSet s；hf' : forall x in s, HasDerivWithinAt f (f' x) s x；hf : 
AntitoneOn f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn`：lint
egral_image_eq_lintegral_deriv_mul_of_antitoneOn (hs : MeasurableSet s) (hf' : f
orall x in s, HasDerivWithinAt f (f' x) s x) (hf : Antit…

--- 原说明 ---
Change of variable formula for differentiable functions, set version: if a real 
function `f` is
antitone and differentiable on a measurable set `s`, then the measure of `f '' s
` is given by the
integral of `-f' x` on `s` .
Note that the measurability of `f '' s` is given by `MeasurableSet.image_of_anti
toneOn`.
-/
theorem lintegral_deriv_eq_volume_image_of_antitoneOn (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hf : AntitoneOn f s) :
    (∫⁻ x in s, ENNReal.ofReal (-f' x)) = volume (f '' s) := by
  simpa using (lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn hs hf' hf 1).symm

/-- Integrability in the change of variable formula for differentiable functions: if a real
function `f` is antitone and differentiable on a measurable set `s`, then a function
`g : ℝ → F` is integrable on `f '' s` if and only if `-f' x • g ∘ f` is integrable on `s` . -/
/-
**MeasureTheory.integrableOn_image_iff_integrableOn_deriv_smul_of_antitoneOn** 是
 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrableOn_image_iff_integrableOn_deriv_smul_of_antitoneOn (hs : Measura
bleSet s) (hf' : forall x in s, HasDerivWithinAt f (f' x) s x) (hf : AntitoneOn 
f s) (g : Real -> F) : IntegrableOn g (f '' s) ↔ IntegrableOn (fun x => (-f' x) 
• g (f x)) s
参数：hs : MeasurableSet s；hf' : forall x in s, HasDerivWithinAt f (f' x) s x；hf : 
AntitoneOn f s；g : Real -> F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasDerivWithinAt.neg`：HasDerivWithinAt.neg (h : HasDerivWithinAt f f' s 
x) : HasDerivWithinAt (-f) (-f') s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integrableOn_image_iff_integrableOn_deriv_smul_of_monotone
On`：integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn (hs : Measurabl
eSet s) (hf' : forall x in s, HasDerivWithinAt f (f' x) s x) (hf…
· 使用定理 `AntitoneOn.neg`：∀ {α : Type u} {β : Type u_1} [inst : AddGroup α] [inst_
1 : Preorder α] [AddLeftMono α] [AddRightMono α]   [inst_4 : Preorder β] {f : β 
→ α}…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul`：integr
ableOn_image_iff_integrableOn_abs_deriv_smul (hs : MeasurableSet s) (hf' : foral
l x in s, HasDerivWithinAt f (f' x) s x) (hf : InjOn f…
· 使用定理 `MeasurableSet.image_of_monotoneOn`：MeasurableSet.image_of_monotoneOn [Se
condCountableTopology β] (ht : MeasurableSet t) (hg : MonotoneOn g t) : Measurab
leSet (g '' t)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `hasDerivWithinAt_neg`：hasDerivWithinAt_neg : HasDerivWithinAt Neg.neg (-
1) s x
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `neg_injective`：∀ {G : Type u_3} [inst : InvolutiveNeg G], Function.Injec
tive Neg.neg
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
Integrability in the change of variable formula for differentiable functions: if
 a real
function `f` is antitone and differentiable on a measurable set `s`, then a func
tion
`g : ℝ → F` is integrable on `f '' s` if and only if `-f' x • g ∘ f` is integrab
le on `s` .
-/
theorem integrableOn_image_iff_integrableOn_deriv_smul_of_antitoneOn (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hf : AntitoneOn f s) (g : ℝ → F) :
    IntegrableOn g (f '' s) ↔ IntegrableOn (fun x ↦ (-f' x) • g (f x)) s := by
  let n : ℝ → ℝ := (fun x ↦ -x)
  let e := n ∘ f
  have hg' (x) (hx : x ∈ s) : HasDerivWithinAt e (-f' x) s x := (hf' x hx).neg
  have A : IntegrableOn (fun x ↦ g (n x)) (e '' s)
      ↔ IntegrableOn (fun x ↦ (-f' x) • (g ∘ n) (e x)) s := by
    rw [← integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn hs hg' hf.neg (g ∘ n)]; rfl
  have B : IntegrableOn g (n '' e '' s) ↔ IntegrableOn (fun x ↦ (|-1| : ℝ) • g (n x)) (e '' s) :=
    integrableOn_image_iff_integrableOn_abs_deriv_smul (hs.image_of_monotoneOn hf.neg)
      (fun x hx ↦ hasDerivWithinAt_neg _ _) neg_injective.injOn _
  simp only [abs_neg, abs_one, one_smul] at B
  rw [A, ← image_comp] at B
  convert! B using 3 with x hx x <;> simp [n, e]

/-- Change of variable formula for differentiable functions: if a real function `f` is
antitone and differentiable on a measurable set `s`, then the Bochner integral of a function
`g : ℝ → F` on `f '' s` coincides with the integral of `(-f' x) • g ∘ f` on `s` . -/
/-
**MeasureTheory.integral_image_eq_integral_deriv_smul_of_antitoneOn** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_image_eq_integral_deriv_smul_of_antitoneOn (hs : MeasurableSet s)
 (hf' : forall x in s, HasDerivWithinAt f (f' x) s x) (hf : AntitoneOn f s) (g :
 Real -> F) : ∫ x in f '' s, g x = ∫ x in s, (-f' x) • g (f x)
参数：hs : MeasurableSet s；hf' : forall x in s, HasDerivWithinAt f (f' x) s x；hf : 
AntitoneOn f s；g : Real -> F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasDerivWithinAt.neg`：HasDerivWithinAt.neg (h : HasDerivWithinAt f f' s 
x) : HasDerivWithinAt (-f) (-f') s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_image_eq_integral_deriv_smul_of_monotoneOn`：integ
ral_image_eq_integral_deriv_smul_of_monotoneOn (hs : MeasurableSet s) (hf' : for
all x in s, HasDerivWithinAt f (f' x) s x) (hf : Monoto…
· 使用定理 `AntitoneOn.neg`：∀ {α : Type u} {β : Type u_1} [inst : AddGroup α] [inst_
1 : Preorder α] [AddLeftMono α] [AddRightMono α]   [inst_4 : Preorder β] {f : β 
→ α}…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `MeasureTheory.integral_image_eq_integral_abs_deriv_smul`：integral_image_
eq_integral_abs_deriv_smul (hs : MeasurableSet s) (hf' : forall x in s, HasDeriv
WithinAt f (f' x) s x) (hf : InjOn f s) (g : …
· 使用定理 `MeasurableSet.image_of_monotoneOn`：MeasurableSet.image_of_monotoneOn [Se
condCountableTopology β] (ht : MeasurableSet t) (hg : MonotoneOn g t) : Measurab
leSet (g '' t)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `hasDerivWithinAt_neg`：hasDerivWithinAt_neg : HasDerivWithinAt Neg.neg (-
1) s x
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `neg_injective`：∀ {G : Type u_3} [inst : InvolutiveNeg G], Function.Injec
tive Neg.neg
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
Change of variable formula for differentiable functions: if a real function `f` 
is
antitone and differentiable on a measurable set `s`, then the Bochner integral o
f a function
`g : ℝ → F` on `f '' s` coincides with the integral of `(-f' x) • g ∘ f` on `s` 
.
-/
theorem integral_image_eq_integral_deriv_smul_of_antitoneOn (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hf : AntitoneOn f s) (g : ℝ → F) :
    ∫ x in f '' s, g x = ∫ x in s, (-f' x) • g (f x) := by
  let n : ℝ → ℝ := (fun x ↦ -x)
  let e := n ∘ f
  have hg' (x) (hx : x ∈ s) : HasDerivWithinAt e (-f' x) s x := (hf' x hx).neg
  have A : ∫ x in e '' s, g (n x) = ∫ x in s, (-f' x) • (g ∘ n) (e x) := by
    rw [← integral_image_eq_integral_deriv_smul_of_monotoneOn hs hg' hf.neg (g ∘ n)]; rfl
  have B : ∫ x in n '' e '' s, g x = ∫ x in e '' s, (|-1| : ℝ) • g (n x) :=
    integral_image_eq_integral_abs_deriv_smul (hs.image_of_monotoneOn hf.neg)
      (fun x hx ↦ hasDerivWithinAt_neg _ _) neg_injective.injOn _
  simp only [abs_neg, abs_one, one_smul] at B
  rw [A, ← image_comp] at B
  convert! B using 3 with x hx x <;> simp [n, e]

@[deprecated (since := "2026-03-19")] alias integral_image_eq_integral_deriv_smul_of_antitone :=
  integral_image_eq_integral_deriv_smul_of_antitoneOn
/-
**MeasureTheory.integral_Icc_deriv_smul_of_deriv_nonpos** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：integral_Icc_deriv_smul_of_deriv_nonpos {a b : Real} {g : Real -> F} (hf :
 ContinuousOn f (Icc a b)) (hff' : forall x in Ioo a b, HasDerivAt f (f' x) x) (
hf' : forall x in Ioo a b, f' x <= 0) (hab : a <= b) : ∫ x in Icc a b, f' x • g 
(f x) = - ∫ u in Icc (f b) (f a), g u
参数：hf : ContinuousOn f (Icc a b)；hff' : forall x in Ioo a b, HasDerivAt f (f' x)
 x；hf' : forall x in Ioo a b, f' x <= 0；hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `antitoneOn_of_deriv_nonpos`：antitoneOn_of_deriv_nonpos {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Icc`：convex_Icc (r s : β) : Convex 𝕜 (Icc r s)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_Icc`：interior_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} : int
erior (Icc a b) = Ioo a b
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
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `MeasureTheory.setIntegral_congr_set`：setIntegral_congr_set (hst : s =ᵐ[μ
] t) : ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousOn.image_Icc_of_antitoneOn`：ContinuousOn.image_Icc_of_antitone
On (hab : a <= b) (hf : ContinuousOn f (Icc a b)) (hmono : AntitoneOn f (Icc a b
)) : f '' Icc a b = Icc (f…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_eq_set`：ae_eq_set {s t : Set α} : s =ᵐ[μ] t ↔ μ (s \ t)
 = 0 ∧ μ (t \ s) = 0
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
（共 46 条，此处仅展示前 30 条）
-/
theorem integral_Icc_deriv_smul_of_deriv_nonpos {a b : ℝ} {g : ℝ → F}
    (hf : ContinuousOn f (Icc a b))
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Ioo a b, f' x ≤ 0) (hab : a ≤ b) :
    ∫ x in Icc a b, f' x • g (f x) = - ∫ u in Icc (f b) (f a), g u := by
  have M : AntitoneOn f (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b) hf
    · rw [interior_Icc]
      exact fun z hz ↦ (hff' z hz).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro z hz
      simpa [(hff' z hz).deriv] using hf' z hz
  have A : ∫ u in Icc (f b) (f a), g u = ∫ u in f '' (Ioo a b), g u := by
    apply setIntegral_congr_set
    rw [← hf.image_Icc_of_antitoneOn hab M]
    refine ae_eq_set.2 ⟨?_, by simp [show f '' Ioo a b \ f '' Icc a b = ∅ by grind]⟩
    have : f '' (Icc a b) \ f '' Ioo a b ⊆ {f a, f b} := by grind
    apply measure_mono_null this
    apply Finite.measure_zero (by simp)
  rw [A, integral_Icc_eq_integral_Ioo,
    integral_image_eq_integral_deriv_smul_of_antitoneOn measurableSet_Ioo (f' := f')]
  · simp [integral_neg]
  · exact fun z hz ↦ (hff' z hz).hasDerivWithinAt
  · exact M.mono Ioo_subset_Icc_self
/-
**MeasureTheory.integrableOn_Icc_deriv_smul_iff_of_deriv_nonpos** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrableOn_Icc_deriv_smul_iff_of_deriv_nonpos {a b : Real} {g : Real -> 
F} (hf : ContinuousOn f (Icc a b)) (hff' : forall x in Ioo a b, HasDerivAt f (f'
 x) x) (hf' : forall x in Ioo a b, f' x <= 0) (hab : a <= b) : IntegrableOn (fun
 x => (f' x) • g (f x)) (Icc a b) ↔ IntegrableOn g (Icc (f b) (f a))
参数：hf : ContinuousOn f (Icc a b)；hff' : forall x in Ioo a b, HasDerivAt f (f' x)
 x；hf' : forall x in Ioo a b, f' x <= 0；hab : a <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `antitoneOn_of_deriv_nonpos`：antitoneOn_of_deriv_nonpos {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Icc`：convex_Icc (r s : β) : Convex 𝕜 (Icc r s)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_Icc`：interior_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} : int
erior (Icc a b) = Ioo a b
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
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `MeasureTheory.integrableOn_congr_set_ae`：integrableOn_congr_set_ae (hst 
: s =ᵐ[μ] t) : IntegrableOn f s μ ↔ IntegrableOn f t μ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousOn.image_Icc_of_antitoneOn`：ContinuousOn.image_Icc_of_antitone
On (hab : a <= b) (hf : ContinuousOn f (Icc a b)) (hmono : AntitoneOn f (Icc a b
)) : f '' Icc a b = Icc (f…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_eq_set`：ae_eq_set {s t : Set α} : s =ᵐ[μ] t ↔ μ (s \ t)
 = 0 ∧ μ (t \ s) = 0
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
（共 58 条，此处仅展示前 30 条）
-/
theorem integrableOn_Icc_deriv_smul_iff_of_deriv_nonpos {a b : ℝ} {g : ℝ → F}
    (hf : ContinuousOn f (Icc a b))
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Ioo a b, f' x ≤ 0) (hab : a ≤ b) :
    IntegrableOn (fun x ↦ (f' x) • g (f x)) (Icc a b) ↔ IntegrableOn g (Icc (f b) (f a)) := by
  have M : AntitoneOn f (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b) hf
    · rw [interior_Icc]
      exact fun z hz ↦ (hff' z hz).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro z hz
      simpa [(hff' z hz).deriv] using hf' z hz
  have A : IntegrableOn g (Icc (f b) (f a)) ↔ IntegrableOn g (f '' (Ioo a b)) := by
    apply integrableOn_congr_set_ae
    rw [← hf.image_Icc_of_antitoneOn hab M]
    refine ae_eq_set.2 ⟨?_, by simp [show f '' Ioo a b \ f '' Icc a b = ∅ by grind]⟩
    have : f '' (Icc a b) \ f '' Ioo a b ⊆ {f a, f b} := by grind
    apply measure_mono_null this
    apply Finite.measure_zero (by simp)
  rw [A, integrableOn_Icc_iff_integrableOn_Ioo,
    integrableOn_image_iff_integrableOn_deriv_smul_of_antitoneOn measurableSet_Ioo (f' := f')]
  · simp
  · exact fun z hz ↦ (hff' z hz).hasDerivWithinAt
  · exact M.mono Ioo_subset_Icc_self

section WithDensity

/-
**MeasureTheory._root_.MeasurableEmbedding.withDensity_ofReal_comap_apply_eq_int
egral_abs_deriv_mul** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasurableEmbedding.withDensity_ofReal_comap_apply_eq_integral_abs_deriv_mul
    {f : ℝ → ℝ} (hf : MeasurableEmbedding f) {s : Set ℝ} (hs : MeasurableSet s)
    {g : ℝ → ℝ} (hg : ∀ᵐ x, x ∈ f '' s → 0 ≤ g x) (hf_int : IntegrableOn g (f '' s))
    {f' : ℝ → ℝ} (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) :
    (volume.withDensity (fun x ↦ ENNReal.ofReal (g x))).comap f s
      = ENNReal.ofReal (∫ x in s, |f' x| * g (f x)) := by
  rw [hf.withDensity_ofReal_comap_apply_eq_integral_abs_det_fderiv_mul volume hs
    hg hf_int hf']
  simp only [det_toSpanSingleton]
/-
**MeasureTheory._root_.MeasurableEquiv.withDensity_ofReal_map_symm_apply_eq_inte
gral_abs_deriv_mul** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasurableEquiv.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul
    (f : ℝ ≃ᵐ ℝ) {s : Set ℝ} (hs : MeasurableSet s)
    {g : ℝ → ℝ} (hg : ∀ᵐ x, x ∈ f '' s → 0 ≤ g x) (hf_int : IntegrableOn g (f '' s))
    {f' : ℝ → ℝ} (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) :
    (volume.withDensity (fun x ↦ ENNReal.ofReal (g x))).map f.symm s
      = ENNReal.ofReal (∫ x in s, |f' x| * g (f x)) := by
  rw [MeasurableEquiv.withDensity_ofReal_map_symm_apply_eq_integral_abs_det_fderiv_mul volume hs
      f hg hf_int hf']
  simp only [det_toSpanSingleton]
/-
**MeasureTheory._root_.MeasurableEmbedding.withDensity_ofReal_comap_apply_eq_int
egral_abs_deriv_mul'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasurableEmbedding.withDensity_ofReal_comap_apply_eq_integral_abs_deriv_mul'
    {f : ℝ → ℝ} (hf : MeasurableEmbedding f) {s : Set ℝ} (hs : MeasurableSet s)
    {f' : ℝ → ℝ} (hf' : ∀ x, HasDerivAt f (f' x) x)
    {g : ℝ → ℝ} (hg : 0 ≤ᵐ[volume] g) (hg_int : Integrable g) :
    (volume.withDensity (fun x ↦ ENNReal.ofReal (g x))).comap f s
      = ENNReal.ofReal (∫ x in s, |f' x| * g (f x)) :=
  hf.withDensity_ofReal_comap_apply_eq_integral_abs_deriv_mul hs
    (by filter_upwards [hg] with x hx using fun _ ↦ hx) hg_int.integrableOn
    (fun x _ => (hf' x).hasDerivWithinAt)
/-
**MeasureTheory._root_.MeasurableEquiv.withDensity_ofReal_map_symm_apply_eq_inte
gral_abs_deriv_mul'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasurableEquiv.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul'
    (f : ℝ ≃ᵐ ℝ) {s : Set ℝ} (hs : MeasurableSet s)
    {f' : ℝ → ℝ} (hf' : ∀ x, HasDerivAt f (f' x) x)
    {g : ℝ → ℝ} (hg : 0 ≤ᵐ[volume] g) (hg_int : Integrable g) :
    (volume.withDensity (fun x ↦ ENNReal.ofReal (g x))).map f.symm s
      = ENNReal.ofReal (∫ x in s, |f' x| * g (f x)) := by
  rw [MeasurableEquiv.withDensity_ofReal_map_symm_apply_eq_integral_abs_det_fderiv_mul volume hs
      f (by filter_upwards [hg] with x hx using fun _ ↦ hx) hg_int.integrableOn
      (fun x _ => (hf' x).hasDerivWithinAt)]
  simp only [det_toSpanSingleton]

end WithDensity

end MeasureTheory

