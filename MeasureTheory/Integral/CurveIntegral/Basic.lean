/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Field.Pointwise
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Integral of a 1-form along a path

In this file we define the integral of a 1-form along a path indexed by `[0, 1]`
and prove basic properties of this operation.

The integral `∫ᶜ x in γ, ω x` is defined as $\int_0^1 \omega(\gamma(t))(\gamma'(t))$.
More precisely, we use

- `Path.extend γ t` instead of `γ t`, because both derivatives and `intervalIntegral`
  expect globally defined functions;
- `derivWithin γ.extend (Set.Icc 0 1) t`, not `deriv γ.extend t`, for the derivative,
  so that it takes meaningful values at `t = 0` and `t = 1`,
  even though this does not affect the integral.

The argument `ω : E → E →L[𝕜] F` is a `𝕜`-linear 1-form on `E` taking values in `F`,
where `𝕜` is `ℝ` or `ℂ`.
The definition does not depend on `𝕜`, see `curveIntegral_restrictScalars` and nearby lemmas.
However, the fact that `𝕜 = ℝ` is not hardcoded
allows us to avoid inserting `ContinuousLinearMap.restrictScalars` here and there.

## Main definitions

- `curveIntegral ω γ`, notation `∫ᶜ x in γ, ω x`, is the integral of a 1-form `ω` along a path `γ`.
- `CurveIntegrable ω γ` is the predicate saying that the above integral makes sense.

## Main results

We prove that `curveIntegral` behaves well with respect to

- operations on `Path`s, see `curveIntegral_refl`, `curveIntegral_symm`, `curveIntegral_trans` etc;
- algebraic operations on 1-forms, see `curveIntegral_add` etc.

We also show that the derivative of `fun b ↦ ∫ᶜ x in Path.segment a b, ω x`
has derivative `ω a` at `b = a`.
We provide 2 versions of this result: one for derivative (`HasFDerivWithinAt`) within a convex set
and one for `HasFDerivAt`.

## Implementation notes

### Naming

In literature, the integral of a function or a 1-form along a path
is called “line integral”, “path integral”, “curve integral”, or “curvilinear integral”.

We use the name “curve integral” instead of other names for the following reasons:

- for many people whose mother tongue is not English,
  “line integral” sounds like an integral along a straight line;

- we reserve the name "path integral" for Feynman-style integrals over the space of paths.

### Usage of `ContinuousLinearMap`s for 1-forms

Similarly to the way `fderiv` uses continuous linear maps
while higher order derivatives use continuous multilinear maps,
this file uses `E → E →L[𝕜] F` instead of continuous alternating maps for 1-forms.

### Differentiability assumptions

The definitions in this file make sense if the path is a piecewise $C^1$ curve.
Poincaré lemma (formalization WIP, see #24019) implies that for a closed 1-form on an open set `U`,
the integral depends on the homotopy class of the path only,
thus we can define the integral along a continuous path
or an element of the fundamental groupoid of `U`.

### Usage of an extra field

The definitions in this file deal with `𝕜`-linear 1-forms.
This allows us to avoid using `ContinuousLinearMap.restrictScalars`
in `HasFDerivWithinAt.curveIntegral_segment_source`
and a future formalization of Poincaré lemma.
-/

@[expose] public section

open Metric MeasureTheory Topology Set Interval AffineMap Convex Filter
open scoped Pointwise unitInterval

section Defs

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {a b : E}

/-- The function `t ↦ ω (γ t) (γ' t)` which appears in the definition of a curve integral.

This definition is used to factor out common parts of lemmas
about `CurveIntegrable` and `curveIntegral`. -/
noncomputable irreducible_def curveIntegralFun (lemma := curveIntegralFun_def')
    (ω : E → E →L[𝕜] F) (γ : Path a b) (t : ℝ) : F :=
  letI : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  ω (γ.extend t) (derivWithin γ.extend I t)

/-- A 1-form `ω` is *curve integrable* along a path `γ`,
if the function `curveIntegralFun ω γ t = ω (γ t) (γ' t)` is integrable on `[0, 1]`.

The actual definition uses `Path.extend γ`,
because both interval integrals and derivatives expect globally defined functions.
-/
/-
**CurveIntegrable** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CurveIntegrable (ω : E -> E ->L[𝕜] F) (γ : Path a b) : Prop
参数：ω : E -> E ->L[𝕜] F；γ : Path a b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A 1-form `ω` is *curve integrable* along a path `γ`,
if the function `curveIntegralFun ω γ t = ω (γ t) (γ' t)` is integrable on `[0, 
1]`.

The actual definition uses `Path.extend γ`,
because both interval integrals and derivatives expect globally defined function
s.
-/
def CurveIntegrable (ω : E → E →L[𝕜] F) (γ : Path a b) : Prop :=
  IntervalIntegrable (curveIntegralFun ω γ) volume 0 1

/-- Integral of a 1-form `ω : E → E →L[𝕜] F` along a path `γ`,
defined as $\int_0^1 \omega(\gamma(t))(\gamma'(t))$.

The actual definition uses `curveIntegralFun` which uses `Path.extend γ`
and `derivWithin (Path.extend γ) (Set.Icc 0 1) t`,
because calculus-related definitions in Mathlib expect globally defined functions as arguments. -/
noncomputable irreducible_def curveIntegral (lemma := curveIntegral_def')
    (ω : E → E →L[𝕜] F) (γ : Path a b) : F :=
  letI : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  ∫ t in 0..1, curveIntegralFun ω γ t

@[inherit_doc curveIntegral]
notation3 "∫ᶜ "(...)" in " γ ", "r:67:(scoped ω => curveIntegral ω γ) => r

/-- curve integral is defined using Bochner integral,
thus it is defined as zero whenever the codomain is not a complete space. -/
/-
**curveIntegral_of_not_completeSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegral_of_not_completeSpace (h : ¬CompleteSpace F) (ω : E -> E ->L[
𝕜] F) (γ : Path a b) : ∫ᶜ x in γ, ω x = 0
参数：h : ¬CompleteSpace F；ω : E -> E ->L[𝕜] F；γ : Path a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `curveIntegral_def'`：∀ {𝕜 : Type u_4} {E : Type u_5} {F : Type u_6} [inst
 : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_
3 : Norm…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.integral_def`：∀ {α : Type u_6} {G : Type u_7} [inst : Norm
edAddCommGroup G] [inst_1 : NormedSpace ℝ G] {x : MeasurableSpace α}   (μ : Meas
ureTheory.Measur…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Set.Ioc_eq_empty`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, ¬b < a
 → Set.Ioc b a = ∅
· 使用定理 `MeasureTheory.Measure.restrict_empty`：restrict_empty : μ.restrict ∅ = 0
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
curve integral is defined using Bochner integral,
thus it is defined as zero whenever the codomain is not a complete space.
-/
theorem curveIntegral_of_not_completeSpace (h : ¬CompleteSpace F) (ω : E → E →L[𝕜] F)
    (γ : Path a b) : ∫ᶜ x in γ, ω x = 0 := by
  simp [curveIntegral, intervalIntegral, integral, h]
/-
**curveIntegralFun_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegralFun_def [NormedSpace Real E] (ω : E -> E ->L[𝕜] F) (γ : Path 
a b) (t : Real) : curveIntegralFun ω γ t = ω (γ.extend t) (derivWithin γ.extend 
I t)
参数：ω : E -> E ->L[𝕜] F；γ : Path a b；t : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `curveIntegralFun_def'`：∀ {𝕜 : Type u_4} {E : Type u_5} {F : Type u_6} [i
nst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [in
st_3 : Norm…
· 使用定理 `NormedSpace.restrictScalars_eq`：NormedSpace.restrictScalars_eq {E : Type
*} [SeminormedAddCommGroup E] [h : NormedSpace 𝕜 E] [NormedSpace 𝕜' E] [IsScalar
Tower 𝕜 𝕜' E] : Norm…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem curveIntegralFun_def [NormedSpace ℝ E] (ω : E → E →L[𝕜] F) (γ : Path a b) (t : ℝ) :
    curveIntegralFun ω γ t = ω (γ.extend t) (derivWithin γ.extend I t) := by
  simp +instances only [curveIntegralFun, NormedSpace.restrictScalars_eq]
/-
**curveIntegral_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegral_def [NormedSpace Real F] (ω : E -> E ->L[𝕜] F) (γ : Path a b
) : curveIntegral ω γ = ∫ t in 0..1, curveIntegralFun ω γ t
参数：ω : E -> E ->L[𝕜] F；γ : Path a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `curveIntegral_def'`：∀ {𝕜 : Type u_4} {E : Type u_5} {F : Type u_6} [inst
 : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_
3 : Norm…
· 使用定理 `NormedSpace.restrictScalars_eq`：NormedSpace.restrictScalars_eq {E : Type
*} [SeminormedAddCommGroup E] [h : NormedSpace 𝕜 E] [NormedSpace 𝕜' E] [IsScalar
Tower 𝕜 𝕜' E] : Norm…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem curveIntegral_def [NormedSpace ℝ F] (ω : E → E →L[𝕜] F) (γ : Path a b) :
    curveIntegral ω γ = ∫ t in 0..1, curveIntegralFun ω γ t := by
  simp +instances only [curveIntegral, NormedSpace.restrictScalars_eq]
/-
**curveIntegral_eq_intervalIntegral_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegral_eq_intervalIntegral_deriv [NormedSpace Real E] [NormedSpace 
Real F] (ω : E -> E ->L[𝕜] F) (γ : Path a b) : ∫ᶜ x in γ, ω x = ∫ t in 0..1, ω (
γ.extend t) (deriv γ.extend t)
参数：ω : E -> E ->L[𝕜] F；γ : Path a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `curveIntegral_def`：curveIntegral_def [NormedSpace Real F] (ω : E -> E ->
L[𝕜] F) (γ : Path a b) : curveIntegral ω γ = ∫ t in 0..1, curveIntegralFun ω γ t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `curveIntegralFun_def`：curveIntegralFun_def [NormedSpace Real E] (ω : E -
> E ->L[𝕜] F) (γ : Path a b) (t : Real) : curveIntegralFun ω γ t = ω (γ.extend t
) (derivWi…
· 使用定理 `intervalIntegral.integral_congr_ae_restrict`：integral_congr_ae_restrict 
{a b : Real} {f g : Real -> E} {μ : Measure Real} (h : f =ᵐ[μ.restrict (Ι a b)] 
g) : ∫ x in a..b, f x ∂μ = ∫ x in…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.uIoc_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoc a b = Set.Ioc a b
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.restrict_Ioo_eq_restrict_Ioc`：restrict_Ioo_eq_restrict_Ioc
 : μ.restrict (Ioo a b) = μ.restrict (Ioc a b)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.ae_restrict_mem`：ae_restrict_mem (hs : MeasurableSet s) : 
forallᵐ x ∂μ.restrict s, x in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `derivWithin_of_mem_nhds`：derivWithin_of_mem_nhds (h : s in 𝓝 x) : derivW
ithin f s x = deriv f x
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
-/
theorem curveIntegral_eq_intervalIntegral_deriv [NormedSpace ℝ E] [NormedSpace ℝ F]
    (ω : E → E →L[𝕜] F) (γ : Path a b) :
    ∫ᶜ x in γ, ω x = ∫ t in 0..1, ω (γ.extend t) (deriv γ.extend t) := by
  simp only [curveIntegral_def, curveIntegralFun_def]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le zero_le_one, ← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem (by measurability)] with x hx
  rw [derivWithin_of_mem_nhds (by simpa)]

end Defs

/-!
### Operations on paths
-/

section PathOperations

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {a b c d : E} {ω : E → E →L[𝕜] F}
  {γ γab : Path a b} {γbc : Path b c} {t : ℝ}

@[simp]
/-
**curveIntegralFun_refl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegralFun_refl (ω : E -> E ->L[𝕜] F) (a : E) : curveIntegralFun ω (
.refl a) = 0
参数：ω : E -> E ->L[𝕜] F；a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `curveIntegralFun_def'`：∀ {𝕜 : Type u_4} {E : Type u_5} {F : Type u_6} [i
nst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [in
st_3 : Norm…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `derivWithin_fun_const`：derivWithin_fun_const : derivWithin (fun _ => c) 
s = 0
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem curveIntegralFun_refl (ω : E → E →L[𝕜] F) (a : E) : curveIntegralFun ω (.refl a) = 0 := by
  ext
  simp [curveIntegralFun, ← Function.const_def]

@[simp]
/-
**curveIntegral_refl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegral_refl (ω : E -> E ->L[𝕜] F) (a : E) : ∫ᶜ x in .refl a, ω x = 
0
参数：ω : E -> E ->L[𝕜] F；a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `curveIntegral_def'`：∀ {𝕜 : Type u_4} {E : Type u_5} {F : Type u_6} [inst
 : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_
3 : Norm…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `curveIntegralFun_refl`：curveIntegralFun_refl (ω : E -> E ->L[𝕜] F) (a : 
E) : curveIntegralFun ω (.refl a) = 0
· 使用定理 `intervalIntegral.integral_zero`：integral_zero : (∫ _ in a..b, (0 : E) ∂μ
) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem curveIntegral_refl (ω : E → E →L[𝕜] F) (a : E) : ∫ᶜ x in .refl a, ω x = 0 := by
  simp [curveIntegral]

@[simp]
/-
**CurveIntegrable.refl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CurveIntegrable.refl (ω : E -> E ->L[𝕜] F) (a : E) : CurveIntegrable ω (.r
efl a)
参数：ω : E -> E ->L[𝕜] F；a : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `curveIntegralFun_refl`：curveIntegralFun_refl (ω : E -> E ->L[𝕜] F) (a : 
E) : curveIntegralFun ω (.refl a) = 0
-/
theorem CurveIntegrable.refl (ω : E → E →L[𝕜] F) (a : E) : CurveIntegrable ω (.refl a) := by
  simp [CurveIntegrable, Pi.zero_def]

@[simp]
/-
**curveIntegralFun_cast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegralFun_cast (ω : E -> E ->L[𝕜] F) (γ : Path a b) (hc : c = a) (h
d : d = b) : curveIntegralFun ω (γ.cast hc hd) = curveIntegralFun ω γ
参数：ω : E -> E ->L[𝕜] F；γ : Path a b；hc : c = a；hd : d = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `curveIntegralFun_def'`：∀ {𝕜 : Type u_4} {E : Type u_5} {F : Type u_6} [i
nst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [in
st_3 : Norm…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem curveIntegralFun_cast (ω : E → E →L[𝕜] F) (γ : Path a b) (hc : c = a) (hd : d = b) :
    curveIntegralFun ω (γ.cast hc hd) = curveIntegralFun ω γ := by
  ext t
  simp only [curveIntegralFun_def', Path.extend_cast]

@[simp]
/-
**curveIntegral_cast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegral_cast (ω : E -> E ->L[𝕜] F) (γ : Path a b) (hc : c = a) (hd :
 d = b) : ∫ᶜ x in γ.cast hc hd, ω x = ∫ᶜ x in γ, ω x
参数：ω : E -> E ->L[𝕜] F；γ : Path a b；hc : c = a；hd : d = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `curveIntegral_def'`：∀ {𝕜 : Type u_4} {E : Type u_5} {F : Type u_6} [inst
 : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_
3 : Norm…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `curveIntegralFun_cast`：curveIntegralFun_cast (ω : E -> E ->L[𝕜] F) (γ : 
Path a b) (hc : c = a) (hd : d = b) : curveIntegralFun ω (γ.cast hc hd) = curveI
ntegralFun …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem curveIntegral_cast (ω : E → E →L[𝕜] F) (γ : Path a b) (hc : c = a) (hd : d = b) :
    ∫ᶜ x in γ.cast hc hd, ω x = ∫ᶜ x in γ, ω x := by
  simp [curveIntegral]

@[simp]
/-
**curveIntegrable_cast_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegrable_cast_iff (hc : c = a) (hd : d = b) : CurveIntegrable ω (γ.
cast hc hd) ↔ CurveIntegrable ω γ
参数：hc : c = a；hd : d = b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `curveIntegralFun_cast`：curveIntegralFun_cast (ω : E -> E ->L[𝕜] F) (γ : 
Path a b) (hc : c = a) (hd : d = b) : curveIntegralFun ω (γ.cast hc hd) = curveI
ntegralFun …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem curveIntegrable_cast_iff (hc : c = a) (hd : d = b) :
    CurveIntegrable ω (γ.cast hc hd) ↔ CurveIntegrable ω γ := by
  simp [CurveIntegrable]

protected alias ⟨_, CurveIntegrable.cast⟩ := curveIntegrable_cast_iff
/-
**curveIntegralFun_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegralFun_symm_apply (ω : E -> E ->L[𝕜] F) (γ : Path a b) (t : Real
) : curveIntegralFun ω γ.symm t = -curveIntegralFun ω γ (1 - t)
参数：ω : E -> E ->L[𝕜] F；γ : Path a b；t : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `curveIntegralFun_def'`：∀ {𝕜 : Type u_4} {E : Type u_5} {F : Type u_6} [i
nst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [in
st_3 : Norm…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Path.extend_symm`：extend_symm (γ : Path x y) : γ.symm.extend = (γ.extend
 <| 1 - ·)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `derivWithin_comp_const_sub`：derivWithin_comp_const_sub : derivWithin (f 
<| a - ·) s x = -derivWithin f (a +ᵥ -s) (a - x)
· 使用定理 `Set.neg_Icc`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : PartialO
rder α] [IsOrderedAddMonoid α] (a b : α),   -Set.Icc a b = Set.Icc (-b) (-a)
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Set.vadd_Icc`：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : Linear
Order α] [IsOrderedAddMonoid α] [AddLeftReflectLE α]   [ExistsAddOfLE α] (a b c 
: …
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem curveIntegralFun_symm_apply (ω : E → E →L[𝕜] F) (γ : Path a b) (t : ℝ) :
    curveIntegralFun ω γ.symm t = -curveIntegralFun ω γ (1 - t) := by
  simp [curveIntegralFun, γ.extend_symm, derivWithin_comp_const_sub]

@[simp]
/-
**curveIntegralFun_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegralFun_symm (ω : E -> E ->L[𝕜] F) (γ : Path a b) : curveIntegral
Fun ω γ.symm = (-curveIntegralFun ω γ <| 1 - ·)
参数：ω : E -> E ->L[𝕜] F；γ : Path a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `curveIntegralFun_symm_apply`：curveIntegralFun_symm_apply (ω : E -> E ->L
[𝕜] F) (γ : Path a b) (t : Real) : curveIntegralFun ω γ.symm t = -curveIntegralF
un ω γ (1 - t)
-/
theorem curveIntegralFun_symm (ω : E → E →L[𝕜] F) (γ : Path a b) :
    curveIntegralFun ω γ.symm = (-curveIntegralFun ω γ <| 1 - ·) :=
  funext <| curveIntegralFun_symm_apply ω γ
/-
**CurveIntegrable.symm** 是 Mathlib 中的一个定理，位于命名空间 `CurveIntegrable`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : NormedAddCommGroup
 F] [inst_4 : NormedSpace 𝕜 F] {a b : E} {ω : E → E →L[𝕜] F}   {γ : Path a b}, C
urveIntegrable ω γ → CurveIntegrable ω γ.symm
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `curveIntegralFun_symm`：curveIntegralFun_symm (ω : E -> E ->L[𝕜] F) (γ : 
Path a b) : curveIntegralFun ω γ.symm = (-curveIntegralFun ω γ <| 1 - ·)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `IntervalIntegrable.symm`：∀ {ε : Type u_3} [inst : TopologicalSpace ε] [i
nst_1 : ENormedAddMonoid ε] {f : ℝ → ε} {a b : ℝ}   {μ : MeasureTheory.Measure ℝ
}, IntervalIn…
· 使用定理 `IntervalIntegrable.neg`：neg {f : Real -> E} (h : IntervalIntegrable f μ 
a b) : IntervalIntegrable (-f) μ a b
· 使用定理 `IntervalIntegrable.comp_sub_left`：comp_sub_left {f : Real -> E} (hf : In
tervalIntegrable f volume a b) (c : Real) (h : ‖f (min a b)‖ₑ != ∞
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
-/
protected theorem CurveIntegrable.symm (h : CurveIntegrable ω γ) : CurveIntegrable ω γ.symm := by
  simpa [CurveIntegrable] using! (h.comp_sub_left 1).neg.symm

@[simp]
/-
**curveIntegrable_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegrable_symm : CurveIntegrable ω γ.symm ↔ CurveIntegrable ω γ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Path.symm_symm`：symm_symm (γ : Path x y) : γ.symm.symm = γ
· 使用定理 `CurveIntegrable.symm`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [in
st : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [ins
t_3 : Norm…
-/
theorem curveIntegrable_symm : CurveIntegrable ω γ.symm ↔ CurveIntegrable ω γ :=
  ⟨fun h ↦ by simpa using h.symm, .symm⟩

@[simp]
/-
**curveIntegral_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegral_symm (ω : E -> E ->L[𝕜] F) (γ : Path a b) : ∫ᶜ x in γ.symm, 
ω x = -∫ᶜ x in γ, ω x
参数：ω : E -> E ->L[𝕜] F；γ : Path a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `curveIntegral_def'`：∀ {𝕜 : Type u_4} {E : Type u_5} {F : Type u_6} [inst
 : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_
3 : Norm…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `curveIntegralFun_symm`：curveIntegralFun_symm (ω : E -> E ->L[𝕜] F) (γ : 
Path a b) : curveIntegralFun ω γ.symm = (-curveIntegralFun ω γ <| 1 - ·)
· 使用定理 `intervalIntegral.integral_neg`：∀ {E : Type u_5} [inst : NormedAddCommGro
up E] [inst_1 : NormedSpace ℝ E] {a b : ℝ} {f : ℝ → E}   {μ : MeasureTheory.Meas
ure ℝ}, ∫ (x : ℝ) i…
· 使用定理 `intervalIntegral.integral_comp_sub_left`：integral_comp_sub_left (d) : (∫
 x in a..b, f (d - x)) = ∫ x in d - b..d - a, f x
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem curveIntegral_symm (ω : E → E →L[𝕜] F) (γ : Path a b) :
    ∫ᶜ x in γ.symm, ω x = -∫ᶜ x in γ, ω x := by
  simp [curveIntegral, curveIntegralFun_symm]
/-
**curveIntegralFun_trans_of_lt_half** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegralFun_trans_of_lt_half (ω : E -> E ->L[𝕜] F) (γab : Path a b) (
γbc : Path b c) (ht : t < 1 / 2) : curveIntegralFun ω (γab.trans γbc) t = (2 : N
at) • curveIntegralFun ω γab (2 * t)
参数：ω : E -> E ->L[𝕜] F；γab : Path a b；γbc : Path b c；ht : t < 1 / 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `eventually_le_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 :
 LinearOrder α] [ClosedIciTopology α] {a b : α},   a < b → ∀ᶠ (x : α) in nhds a,
 x ≤ b
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Path.extend_trans_of_le_half`：extend_trans_of_le_half (γ₁ : Path x y) (γ
₂ : Path y z) {t : Real} (ht : t <= 1 / 2) : (γ₁.trans γ₂).extend t = γ₁.extend 
(2 * t)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedField.smul_Icc`：smul_Icc : r • Icc a b = Icc (r * a) (r * b
)
· 使用定理 `two_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_eq_iff_eventuallyEq`：nhdsWithin_eq_iff_eventuallyEq {s t : Se
t α} {x : α} : 𝓝[s] x = 𝓝[t] x ↔ s =ᶠ[𝓝 x] t
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `notMem_closure_iff_nhdsWithin_eq_bot`：notMem_closure_iff_nhdsWithin_eq_b
ot : x ∉ closure s ↔ 𝓝[s] x = ⊥
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
（共 105 条，此处仅展示前 30 条）
-/
theorem curveIntegralFun_trans_of_lt_half (ω : E → E →L[𝕜] F) (γab : Path a b) (γbc : Path b c)
    (ht : t < 1 / 2) :
    curveIntegralFun ω (γab.trans γbc) t = (2 : ℕ) • curveIntegralFun ω γab (2 * t) := by
  let instE := NormedSpace.restrictScalars ℝ 𝕜 E
  have H₁ : (γab.trans γbc).extend =ᶠ[𝓝 t] (fun s ↦ γab.extend (2 * s)) :=
    (eventually_le_nhds ht).mono fun _ ↦ Path.extend_trans_of_le_half _ _
  have H₂ : (2 : ℝ) • I =ᶠ[𝓝 (2 * t)] I := by
    rw [LinearOrderedField.smul_Icc two_pos, mul_zero, mul_one, ← nhdsWithin_eq_iff_eventuallyEq]
    rcases lt_trichotomy t 0 with ht₀ | rfl | ht₀
    · rw [notMem_closure_iff_nhdsWithin_eq_bot.mp, notMem_closure_iff_nhdsWithin_eq_bot.mp] <;>
        simp_intro h <;> linarith
    · simp
    · rw [nhdsWithin_eq_nhds.2, nhdsWithin_eq_nhds.2] <;> simp [*] <;> linarith
  rw [curveIntegralFun_def, H₁.self_of_nhds, H₁.derivWithin_eq_of_nhds, curveIntegralFun_def,
    derivWithin_comp_mul_left, ofNat_smul_eq_nsmul, map_nsmul, derivWithin_congr_set H₂]
/-
**curveIntegralFun_trans_aeeq_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegralFun_trans_aeeq_left (ω : E -> E ->L[𝕜] F) (γab : Path a b) (γ
bc : Path b c) : curveIntegralFun ω (γab.trans γbc) =ᵐ[volume.restrict (Ι (0 : R
eal) (1 / 2))] fun t => (2 : Nat) • curveIntegralFun ω γab (2 * t)
参数：ω : E -> E ->L[𝕜] F；γab : Path a b；γbc : Path b c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.uIoc_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoc a b = Set.Ioc a b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.restrict_Ioo_eq_restrict_Ioc`：restrict_Ioo_eq_restrict_Ioc
 : μ.restrict (Ioo a b) = μ.restrict (Ioc a b)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.ae_restrict_mem`：ae_restrict_mem (hs : MeasurableSet s) : 
forallᵐ x ∂μ.restrict s, x in s
· 使用定理 `measurableSet_Ioo`：measurableSet_Ioo [OrderClosedTopology α] : Measurabl
eSet (Ioo a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `curveIntegralFun_trans_of_lt_half`：curveIntegralFun_trans_of_lt_half (ω 
: E -> E ->L[𝕜] F) (γab : Path a b) (γbc : Path b c) (ht : t < 1 / 2) : curveInt
egralFun ω (γab.trans γ…
-/
theorem curveIntegralFun_trans_aeeq_left (ω : E → E →L[𝕜] F) (γab : Path a b) (γbc : Path b c) :
    curveIntegralFun ω (γab.trans γbc) =ᵐ[volume.restrict (Ι (0 : ℝ) (1 / 2))]
      fun t ↦ (2 : ℕ) • curveIntegralFun ω γab (2 * t) := by
  rw [uIoc_of_le (by positivity), ← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ⟨ht₀, ht⟩
  exact curveIntegralFun_trans_of_lt_half ω γab γbc ht
/-
**curveIntegralFun_trans_of_half_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegralFun_trans_of_half_lt (ω : E -> E ->L[𝕜] F) (γab : Path a b) (
γbc : Path b c) (ht₀ : 1 / 2 < t) : curveIntegralFun ω (γab.trans γbc) t = (2 : 
Nat) • curveIntegralFun ω γbc (2 * t - 1)
参数：ω : E -> E ->L[𝕜] F；γab : Path a b；γbc : Path b c；ht₀ : 1 / 2 < t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Path.symm_symm`：symm_symm (γ : Path x y) : γ.symm.symm = γ
· 使用定理 `curveIntegralFun_symm_apply`：curveIntegralFun_symm_apply (ω : E -> E ->L
[𝕜] F) (γ : Path a b) (t : Real) : curveIntegralFun ω γ.symm t = -curveIntegralF
un ω γ (1 - t)
· 使用定理 `Path.trans_symm`：trans_symm (γ : Path x y) (γ' : Path y z) : (γ.trans γ'
).symm = γ'.symm.trans γ.symm
· 使用定理 `curveIntegralFun_trans_of_lt_half`：curveIntegralFun_trans_of_lt_half (ω 
: E -> E ->L[𝕜] F) (γab : Path a b) (γbc : Path b c) (ht : t < 1 / 2) : curveInt
egralFun ω (γab.trans γ…
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
（共 68 条，此处仅展示前 30 条）
-/
theorem curveIntegralFun_trans_of_half_lt (ω : E → E →L[𝕜] F) (γab : Path a b) (γbc : Path b c)
    (ht₀ : 1 / 2 < t) :
    curveIntegralFun ω (γab.trans γbc) t = (2 : ℕ) • curveIntegralFun ω γbc (2 * t - 1) := by
  rw [← (γab.trans γbc).symm_symm, curveIntegralFun_symm_apply, Path.trans_symm,
    curveIntegralFun_trans_of_lt_half (ht := by linarith), curveIntegralFun_symm_apply, smul_neg,
    neg_neg]
  congr 2
  ring
/-
**curveIntegralFun_trans_aeeq_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegralFun_trans_aeeq_right (ω : E -> E ->L[𝕜] F) (γab : Path a b) (
γbc : Path b c) : curveIntegralFun ω (γab.trans γbc) =ᵐ[volume.restrict (Ι (1 / 
2 : Real) 1)] fun t => (2 : Nat) • curveIntegralFun ω γbc (2 * t - 1)
参数：ω : E -> E ->L[𝕜] F；γab : Path a b；γbc : Path b c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.uIoc_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoc a b = Set.Ioc a b
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
（共 64 条，此处仅展示前 30 条）
-/
theorem curveIntegralFun_trans_aeeq_right (ω : E → E →L[𝕜] F) (γab : Path a b) (γbc : Path b c) :
    curveIntegralFun ω (γab.trans γbc) =ᵐ[volume.restrict (Ι (1 / 2 : ℝ) 1)]
      fun t ↦ (2 : ℕ) • curveIntegralFun ω γbc (2 * t - 1) := by
  rw [uIoc_of_le (by linarith), ← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ⟨ht₁, ht₂⟩
  exact curveIntegralFun_trans_of_half_lt ω γab γbc ht₁
/-
**CurveIntegrable.intervalIntegrable_curveIntegralFun_trans_left** 是 Mathlib 中的一
个定理，位于命名空间 ``。
形式化陈述：CurveIntegrable.intervalIntegrable_curveIntegralFun_trans_left (h : CurveI
ntegrable ω γab) (γbc : Path b c) : IntervalIntegrable (curveIntegralFun ω (γab.
trans γbc)) volume 0 (1 / 2)
参数：h : CurveIntegrable ω γab；γbc : Path b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntervalIntegrable.congr_ae`：IntervalIntegrable.congr_ae {g : Real -> ε}
 (hf : IntervalIntegrable f μ a b) (h : f =ᵐ[μ.restrict (Ι a b)] g) : IntervalIn
tegrable g μ a b
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ofNat_smul_eq_nsmul`：ofNat_smul_eq_nsmul (n : Nat) [n.AtLeastTwo] (b : M
) : (ofNat(n) : R) • b = ofNat(n) • b
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `IntervalIntegrable.smul`：smul {R : Type*} [NormedAddCommGroup R] [SMulZe
roClass R E] [IsBoundedSMul R E] {f : Real -> E} (h : IntervalIntegrable f μ a b
) (r : R) : I…
· 使用定理 `IntervalIntegrable.comp_mul_left`：comp_mul_left (hf : IntervalIntegrable
 f volume a b) {c : Real} (h : ‖f (min a b)‖ₑ != ∞
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `curveIntegralFun_trans_aeeq_left`：curveIntegralFun_trans_aeeq_left (ω : 
E -> E ->L[𝕜] F) (γab : Path a b) (γbc : Path b c) : curveIntegralFun ω (γab.tra
ns γbc) =ᵐ[volume.rest…
-/
theorem CurveIntegrable.intervalIntegrable_curveIntegralFun_trans_left
    (h : CurveIntegrable ω γab) (γbc : Path b c) :
    IntervalIntegrable (curveIntegralFun ω (γab.trans γbc)) volume 0 (1 / 2) := by
  refine .congr_ae ?_ (curveIntegralFun_trans_aeeq_left _ _ _).symm
  simpa [ofNat_smul_eq_nsmul] using! h.comp_mul_left.smul (2 : 𝕜)
/-
**CurveIntegrable.intervalIntegrable_curveIntegralFun_trans_right** 是 Mathlib 中的
一个定理，位于命名空间 ``。
形式化陈述：CurveIntegrable.intervalIntegrable_curveIntegralFun_trans_right (γab : Pat
h a b) (h : CurveIntegrable ω γbc) : IntervalIntegrable (curveIntegralFun ω (γab
.trans γbc)) volume (1 / 2) 1
参数：γab : Path a b；h : CurveIntegrable ω γbc。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntervalIntegrable.congr_ae`：IntervalIntegrable.congr_ae {g : Real -> ε}
 (hf : IntervalIntegrable f μ a b) (h : f =ᵐ[μ.restrict (Ι a b)] g) : IntervalIn
tegrable g μ a b
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ofNat_smul_eq_nsmul`：ofNat_smul_eq_nsmul (n : Nat) [n.AtLeastTwo] (b : M
) : (ofNat(n) : R) • b = ofNat(n) • b
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_self_div_two`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2
] (a : K), (a + a) / 2 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IntervalIntegrable.smul`：smul {R : Type*} [NormedAddCommGroup R] [SMulZe
roClass R E] [IsBoundedSMul R E] {f : Real -> E} (h : IntervalIntegrable f μ a b
) (r : R) : I…
· 使用定理 `IntervalIntegrable.comp_mul_left`：comp_mul_left (hf : IntervalIntegrable
 f volume a b) {c : Real} (h : ‖f (min a b)‖ₑ != ∞
· 使用定理 `IntervalIntegrable.comp_sub_right`：comp_sub_right (hf : IntervalIntegrab
le f volume a b) (c : Real) (h : ‖f (min a b)‖ₑ != ∞
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `curveIntegralFun_trans_aeeq_right`：curveIntegralFun_trans_aeeq_right (ω 
: E -> E ->L[𝕜] F) (γab : Path a b) (γbc : Path b c) : curveIntegralFun ω (γab.t
rans γbc) =ᵐ[volume.res…
-/
theorem CurveIntegrable.intervalIntegrable_curveIntegralFun_trans_right
    (γab : Path a b) (h : CurveIntegrable ω γbc) :
    IntervalIntegrable (curveIntegralFun ω (γab.trans γbc)) volume (1 / 2) 1 := by
  refine .congr_ae ?_ (curveIntegralFun_trans_aeeq_right _ _ _).symm
  simpa [ofNat_smul_eq_nsmul] using! h.comp_sub_right 1 |>.comp_mul_left (c := 2) |>.smul (2 : 𝕜)
/-
**CurveIntegrable.trans** 是 Mathlib 中的一个定理，位于命名空间 `CurveIntegrable`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : NormedAddCommGroup
 F] [inst_4 : NormedSpace 𝕜 F] {a b c : E} {ω : E → E →L[𝕜] F}   {γab : Path a b
} {γbc : Path b c}, CurveIntegrable ω γab → CurveIntegrable ω γbc → CurveIntegra
ble ω (γab.trans γbc)
参数：γab.trans γbc。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntervalIntegrable.trans`：trans {a b c : Real} (hab : IntervalIntegrable
 f μ a b) (hbc : IntervalIntegrable f μ b c) : IntervalIntegrable f μ a c
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CurveIntegrable.intervalIntegrable_curveIntegralFun_trans_left`：CurveInt
egrable.intervalIntegrable_curveIntegralFun_trans_left (h : CurveIntegrable ω γa
b) (γbc : Path b c) : IntervalIntegrable (curveInteg…
· 使用定理 `CurveIntegrable.intervalIntegrable_curveIntegralFun_trans_right`：CurveIn
tegrable.intervalIntegrable_curveIntegralFun_trans_right (γab : Path a b) (h : C
urveIntegrable ω γbc) : IntervalIntegrable (curveInte…
-/
protected theorem CurveIntegrable.trans (h₁ : CurveIntegrable ω γab) (h₂ : CurveIntegrable ω γbc) :
    CurveIntegrable ω (γab.trans γbc) :=
  (h₁.intervalIntegrable_curveIntegralFun_trans_left γbc).trans
    (h₂.intervalIntegrable_curveIntegralFun_trans_right γab)
/-
**curveIntegral_trans** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegral_trans (h₁ : CurveIntegrable ω γab) (h₂ : CurveIntegrable ω γ
bc) : ∫ᶜ x in γab.trans γbc, ω x = (∫ᶜ x in γab, ω x) + ∫ᶜ x in γbc, ω x
参数：h₁ : CurveIntegrable ω γab；h₂ : CurveIntegrable ω γbc。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `curveIntegral_def`：curveIntegral_def [NormedSpace Real F] (ω : E -> E ->
L[𝕜] F) (γ : Path a b) : curveIntegral ω γ = ∫ t in 0..1, curveIntegralFun ω γ t
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegral.integral_add_adjacent_intervals`：integral_add_adjacent_
intervals (hab : IntervalIntegrable f μ a b) (hbc : IntervalIntegrable f μ b c) 
: ((∫ x in a..b, f x ∂μ) + ∫ x in b..c…
· 使用定理 `CurveIntegrable.intervalIntegrable_curveIntegralFun_trans_left`：CurveInt
egrable.intervalIntegrable_curveIntegralFun_trans_left (h : CurveIntegrable ω γa
b) (γbc : Path b c) : IntervalIntegrable (curveInteg…
· 使用定理 `CurveIntegrable.intervalIntegrable_curveIntegralFun_trans_right`：CurveIn
tegrable.intervalIntegrable_curveIntegralFun_trans_right (γab : Path a b) (h : C
urveIntegrable ω γbc) : IntervalIntegrable (curveInte…
· 使用定理 `intervalIntegral.integral_congr_ae_restrict`：integral_congr_ae_restrict 
{a b : Real} {f g : Real -> E} {μ : Measure Real} (h : f =ᵐ[μ.restrict (Ι a b)] 
g) : ∫ x in a..b, f x ∂μ = ∫ x in…
· 使用定理 `curveIntegralFun_trans_aeeq_left`：curveIntegralFun_trans_aeeq_left (ω : 
E -> E ->L[𝕜] F) (γab : Path a b) (γbc : Path b c) : curveIntegralFun ω (γab.tra
ns γbc) =ᵐ[volume.rest…
· 使用定理 `curveIntegralFun_trans_aeeq_right`：curveIntegralFun_trans_aeeq_right (ω 
: E -> E ->L[𝕜] F) (γab : Path a b) (γbc : Path b c) : curveIntegralFun ω (γab.t
rans γbc) =ᵐ[volume.res…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ofNat_smul_eq_nsmul`：ofNat_smul_eq_nsmul (n : Nat) [n.AtLeastTwo] (b : M
) : (ofNat(n) : R) • b = ofNat(n) • b
· 使用定理 `intervalIntegral.integral_smul`：∀ {𝕜 : Type u_2} {E : Type u_5} [inst : 
NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {a b : ℝ}   {μ : MeasureTheory.
Measure ℝ} [inst_2 :…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `intervalIntegral.smul_integral_comp_mul_left`：smul_integral_comp_mul_lef
t (c) : (c • ∫ x in a..b, f (c * x)) = ∫ x in c * a..c * b, f x
· 使用定理 `intervalIntegral.integral_comp_sub_right`：integral_comp_sub_right (d) : 
(∫ x in a..b, f (x - d)) = ∫ x in a - d..b - d, f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
（共 38 条，此处仅展示前 30 条）
-/
theorem curveIntegral_trans (h₁ : CurveIntegrable ω γab) (h₂ : CurveIntegrable ω γbc) :
    ∫ᶜ x in γab.trans γbc, ω x = (∫ᶜ x in γab, ω x) + ∫ᶜ x in γbc, ω x := by
  let instF := NormedSpace.restrictScalars ℝ 𝕜 F
  rw [curveIntegral_def, ← intervalIntegral.integral_add_adjacent_intervals
    (h₁.intervalIntegrable_curveIntegralFun_trans_left γbc)
    (h₂.intervalIntegrable_curveIntegralFun_trans_right γab),
    intervalIntegral.integral_congr_ae_restrict (curveIntegralFun_trans_aeeq_left _ _ _),
    intervalIntegral.integral_congr_ae_restrict (curveIntegralFun_trans_aeeq_right _ _ _)]
  simp only [← ofNat_smul_eq_nsmul (R := ℝ)]
  rw [intervalIntegral.integral_smul, intervalIntegral.smul_integral_comp_mul_left,
    intervalIntegral.integral_smul,
    intervalIntegral.smul_integral_comp_mul_left (f := (curveIntegralFun ω γbc <| · - 1)),
    intervalIntegral.integral_comp_sub_right]
  simp only [curveIntegral_def]
  norm_num

set_option backward.isDefEq.respectTransparency.types false in
/-
**curveIntegralFun_segment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegralFun_segment [NormedSpace Real E] (ω : E -> E ->L[𝕜] F) (a b :
 E) {t : Real} (ht : t in I) : curveIntegralFun ω (.segment a b) t = ω (lineMap 
a b t) (b - a)
参数：ω : E -> E ->L[𝕜] F；a b : E；ht : t in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Path.eqOn_extend_segment`：eqOn_extend_segment (a b : E) : EqOn (Path.seg
ment a b).extend (AffineMap.lineMap a b) I
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `curveIntegralFun_def`：curveIntegralFun_def [NormedSpace Real E] (ω : E -
> E ->L[𝕜] F) (γ : Path a b) (t : Real) : curveIntegralFun ω γ t = ω (γ.extend t
) (derivWi…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `derivWithin_congr`：derivWithin_congr (hs : EqOn f₁ f s) (hx : f₁ x = f x
) : derivWithin f₁ s x = derivWithin f s x
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `AffineMap.hasDerivWithinAt_lineMap`：hasDerivWithinAt_lineMap : HasDerivW
ithinAt (lineMap a b) (b - a) s x
· 使用定理 `uniqueDiffOn_Icc_zero_one`：uniqueDiffOn_Icc_zero_one : UniqueDiffOn Real
 (Icc (0 : Real) 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem curveIntegralFun_segment [NormedSpace ℝ E] (ω : E → E →L[𝕜] F) (a b : E)
    {t : ℝ} (ht : t ∈ I) : curveIntegralFun ω (.segment a b) t = ω (lineMap a b t) (b - a) := by
  have := Path.eqOn_extend_segment a b
  simp only [curveIntegralFun_def, this ht, derivWithin_congr this (this ht),
    (hasDerivWithinAt_lineMap ..).derivWithin (uniqueDiffOn_Icc_zero_one t ht)]

set_option backward.isDefEq.respectTransparency.types false in
/-
**curveIntegrable_segment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegrable_segment [NormedSpace Real E] : CurveIntegrable ω (.segment
 a b) ↔ IntervalIntegrable (fun t => ω (lineMap a b t) (b - a)) volume 0 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CurveIntegrable.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [in
st : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [ins
t_3 : Norm…
· 使用定理 `intervalIntegrable_congr`：intervalIntegrable_congr {g : Real -> ε} (h : 
EqOn f g (Ι a b)) : IntervalIntegrable f μ a b ↔ IntervalIntegrable g μ a b
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Set.uIoc_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoc a b = Set.Ioc a b
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `Set.EqOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f₁ f₂ : 
α → β}, s₁ ⊆ s₂ → Set.EqOn f₁ f₂ s₂ → Set.EqOn f₁ f₂ s₁
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
· 使用定理 `curveIntegralFun_segment`：curveIntegralFun_segment [NormedSpace Real E] 
(ω : E -> E ->L[𝕜] F) (a b : E) {t : Real} (ht : t in I) : curveIntegralFun ω (.
segment a b) t…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem curveIntegrable_segment [NormedSpace ℝ E] :
    CurveIntegrable ω (.segment a b) ↔
      IntervalIntegrable (fun t ↦ ω (lineMap a b t) (b - a)) volume 0 1 := by
  rw [CurveIntegrable, intervalIntegrable_congr]
  rw [uIoc_of_le zero_le_one]
  exact .mono Ioc_subset_Icc_self fun _t ↦ curveIntegralFun_segment ω a b

set_option backward.isDefEq.respectTransparency.types false in
/-
**curveIntegral_segment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegral_segment [NormedSpace Real E] [NormedSpace Real F] (ω : E -> 
E ->L[𝕜] F) (a b : E) : ∫ᶜ x in .segment a b, ω x = ∫ t in 0..1, ω (lineMap a b 
t) (b - a)
参数：ω : E -> E ->L[𝕜] F；a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `curveIntegral_def`：curveIntegral_def [NormedSpace Real F] (ω : E -> E ->
L[𝕜] F) (γ : Path a b) : curveIntegral ω γ = ∫ t in 0..1, curveIntegralFun ω γ t
· 使用定理 `intervalIntegral.integral_congr`：integral_congr {a b : Real} (h : EqOn f
 g [[a, b]]) : ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ
· 使用定理 `curveIntegralFun_segment`：curveIntegralFun_segment [NormedSpace Real E] 
(ω : E -> E ->L[𝕜] F) (a b : E) {t : Real} (ht : t in I) : curveIntegralFun ω (.
segment a b) t…
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
theorem curveIntegral_segment [NormedSpace ℝ E] [NormedSpace ℝ F] (ω : E → E →L[𝕜] F) (a b : E) :
    ∫ᶜ x in .segment a b, ω x = ∫ t in 0..1, ω (lineMap a b t) (b - a) := by
  rw [curveIntegral_def]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [uIcc_of_le zero_le_one] at ht
  exact curveIntegralFun_segment ω a b ht

@[simp]
/-
**curveIntegral_segment_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegral_segment_const [NormedSpace Real E] [CompleteSpace F] (ω : E 
->L[𝕜] F) (a b : E) : ∫ᶜ _ in .segment a b, ω = ω (b - a)
参数：ω : E ->L[𝕜] F；a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `curveIntegral_segment`：curveIntegral_segment [NormedSpace Real E] [Norme
dSpace Real F] (ω : E -> E ->L[𝕜] F) (a b : E) : ∫ᶜ x in .segment a b, ω x = ∫ t
 in 0..1, ω…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `intervalIntegral.integral_sub`：integral_sub (hf : IntervalIntegrable f μ
 a b) (hg : IntervalIntegrable g μ a b) : ∫ x in a..b, f x - g x ∂μ = (∫ x in a.
.b, f x ∂μ) - ∫ x i…
· 使用定理 `intervalIntegral.integral_const`：integral_const [CompleteSpace E] (c : E
) : ∫ _ in a..b, c = (b - a) • c
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem curveIntegral_segment_const [NormedSpace ℝ E] [CompleteSpace F] (ω : E →L[𝕜] F) (a b : E) :
    ∫ᶜ _ in .segment a b, ω = ω (b - a) := by
  let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  simp [curveIntegral_segment]

set_option backward.isDefEq.respectTransparency.types false in
/-- If `‖ω z‖ ≤ C` at all points of the segment `[a -[ℝ] b]`,
then the curve integral `∫ᶜ x in .segment a b, ω x` has norm at most `C * ‖b - a‖`. -/
/-
**norm_curveIntegral_segment_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_curveIntegral_segment_le [NormedSpace Real E] {C : Real} (h : forall 
z in [a -[Real] b], ‖ω z‖ <= C) : ‖∫ᶜ x in .segment a b, ω x‖ <= C * ‖b - a‖
参数：h : forall z in [a -[Real] b], ‖ω z‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `curveIntegral_segment`：curveIntegral_segment [NormedSpace Real E] [Norme
dSpace Real F] (ω : E -> E ->L[𝕜] F) (a b : E) : ∫ᶜ x in .segment a b, ω x = ∫ t
 in 0..1, ω…
· 使用定理 `intervalIntegral.norm_integral_le_of_norm_le_const`：norm_integral_le_of_
norm_le_const {a b C : Real} {f : Real -> E} (h : forall x in Ι a b, ‖f x‖ <= C)
 : ‖∫ x in a..b, f x‖ <= C * |b - a|
· 使用定理 `ContinuousLinearMap.le_of_opNorm_le`：le_of_opNorm_le {c : Real} (h : ‖f‖
 <= c) (x : E) : ‖f x‖ <= c * ‖x‖
· 使用定理 `segment_eq_image_lineMap`：segment_eq_image_lineMap (x y : E) : [x -[𝕜] y
] = AffineMap.lineMap x y '' Icc (0 : 𝕜) 1
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
· 使用定理 `Set.uIoc_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoc a b = Set.Ioc a b
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `‖ω z‖ ≤ C` at all points of the segment `[a -[ℝ] b]`,
then the curve integral `∫ᶜ x in .segment a b, ω x` has norm at most `C * ‖b - a
‖`.
-/
theorem norm_curveIntegral_segment_le [NormedSpace ℝ E] {C : ℝ} (h : ∀ z ∈ [a -[ℝ] b], ‖ω z‖ ≤ C) :
    ‖∫ᶜ x in .segment a b, ω x‖ ≤ C * ‖b - a‖ := calc
  ‖∫ᶜ x in .segment a b, ω x‖ ≤ C * ‖b - a‖ * |1 - 0| := by
    let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
    rw [curveIntegral_segment]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht ↦ ?_
    rw [segment_eq_image_lineMap] at h
    rw [uIoc_of_le zero_le_one] at ht
    apply_rules [(ω _).le_of_opNorm_le, mem_image_of_mem, Ioc_subset_Icc_self]
  _ = C * ‖b - a‖ := by simp

/-- If a 1-form `ω` is continuous on a set `s`,
then it is curve integrable along any $C^1$ path in this set. -/
/-
**ContinuousOn.curveIntegrable_of_contDiffOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.curveIntegrable_of_contDiffOn [NormedSpace Real E] {s : Set E
} (hω : ContinuousOn ω s) (hγ : ContDiffOn Real 1 γ.extend I) (hγs : forall t, γ
 t in s) : CurveIntegrable ω γ
参数：hω : ContinuousOn ω s；hγ : ContDiffOn Real 1 γ.extend I；hγs : forall t, γ t i
n s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousOn.intervalIntegrable_of_Icc`：ContinuousOn.intervalIntegrable_
of_Icc {u : Real -> E} {a b : Real} (h : a <= b) (hu : ContinuousOn u (Icc a b))
 : IntervalIntegrable u μ a …
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `curveIntegralFun_def`：curveIntegralFun_def [NormedSpace Real E] (ω : E -
> E ->L[𝕜] F) (γ : Path a b) (t : Real) : curveIntegralFun ω γ t = ω (γ.extend t
) (derivWi…
· 使用定理 `ContinuousOn.clm_apply`：ContinuousOn.clm_apply {f : X -> E ->L[𝕜] F} {g 
: X -> E} {s : Set X} (hf : ContinuousOn f s) (hg : ContinuousOn g s) : Continuo
usOn (fun x …
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.pathExtend`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] {x y : X} {γ : Y → Path x y}   {f : Y →
 ℝ}, Contin…
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `ContDiffOn.continuousOn_derivWithin`：ContDiffOn.continuousOn_derivWithin
 (h : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s) (hn : 1 <= n) : ContinuousOn (
derivWithin f s) s
· 使用定理 `uniqueDiffOn_Icc_zero_one`：uniqueDiffOn_Icc_zero_one : UniqueDiffOn Real
 (Icc (0 : Real) 1)
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
If a 1-form `ω` is continuous on a set `s`,
then it is curve integrable along any $C^1$ path in this set.
-/
theorem ContinuousOn.curveIntegrable_of_contDiffOn [NormedSpace ℝ E] {s : Set E}
    (hω : ContinuousOn ω s) (hγ : ContDiffOn ℝ 1 γ.extend I) (hγs : ∀ t, γ t ∈ s) :
    CurveIntegrable ω γ := by
  apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
  simp only [funext (curveIntegralFun_def ω γ)]
  apply ContinuousOn.clm_apply
  · exact hω.comp (by fun_prop) fun _ _ ↦ hγs _
  · exact hγ.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl

end PathOperations

/-!
### Algebraic operations on the 1-form
-/

section Algebra

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {a b : E}
  {ω ω₁ ω₂ : E → E →L[𝕜] F} {γ : Path a b} {t : ℝ}

@[simp]
/-
**curveIntegralFun_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegralFun_add : curveIntegralFun (ω₁ + ω₂) γ = curveIntegralFun ω₁ 
γ + curveIntegralFun ω₂ γ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `curveIntegralFun_def'`：∀ {𝕜 : Type u_4} {E : Type u_5} {F : Type u_6} [i
nst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [in
st_3 : Norm…
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem curveIntegralFun_add :
    curveIntegralFun (ω₁ + ω₂) γ = curveIntegralFun ω₁ γ + curveIntegralFun ω₂ γ := by
  ext; simp [curveIntegralFun]
/-
**CurveIntegrable.add** 是 Mathlib 中的一个定理，位于命名空间 `CurveIntegrable`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : NormedAddCommGroup
 F] [inst_4 : NormedSpace 𝕜 F] {a b : E}   {ω₁ ω₂ : E → E →L[𝕜] F} {γ : Path a b
}, CurveIntegrable ω₁ γ → CurveIntegrable ω₂ γ → CurveIntegrable (ω₁ + ω₂) γ
参数：ω₁ + ω₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `curveIntegralFun_add`：curveIntegralFun_add : curveIntegralFun (ω₁ + ω₂) 
γ = curveIntegralFun ω₁ γ + curveIntegralFun ω₂ γ
· 使用定理 `IntervalIntegrable.add`：add [ContinuousAdd ε] (hf : IntervalIntegrable f
 μ a b) (hg : IntervalIntegrable g μ a b) : IntervalIntegrable (fun x => f x + g
 x) μ a b
-/
protected theorem CurveIntegrable.add (h₁ : CurveIntegrable ω₁ γ) (h₂ : CurveIntegrable ω₂ γ) :
    CurveIntegrable (ω₁ + ω₂) γ := by
  simpa [CurveIntegrable] using! IntervalIntegrable.add h₁ h₂

-- TODO: `to_fun` generates wrong lemma name
/-
**curveIntegral_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegral_add (h₁ : CurveIntegrable ω₁ γ) (h₂ : CurveIntegrable ω₂ γ) 
: curveIntegral (ω₁ + ω₂) γ = ∫ᶜ x in γ, ω₁ x + ∫ᶜ x in γ, ω₂ x
参数：h₁ : CurveIntegrable ω₁ γ；h₂ : CurveIntegrable ω₂ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `curveIntegral_def'`：∀ {𝕜 : Type u_4} {E : Type u_5} {F : Type u_6} [inst
 : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_
3 : Norm…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `curveIntegralFun_add`：curveIntegralFun_add : curveIntegralFun (ω₁ + ω₂) 
γ = curveIntegralFun ω₁ γ + curveIntegralFun ω₂ γ
· 使用定理 `intervalIntegral.integral_add`：∀ {E : Type u_5} [inst : NormedAddCommGro
up E] [inst_1 : NormedSpace ℝ E] {a b : ℝ} {f g : ℝ → E}   {μ : MeasureTheory.Me
asure ℝ},   Interva…
-/
theorem curveIntegral_add (h₁ : CurveIntegrable ω₁ γ) (h₂ : CurveIntegrable ω₂ γ) :
    curveIntegral (ω₁ + ω₂) γ = ∫ᶜ x in γ, ω₁ x + ∫ᶜ x in γ, ω₂ x := by
  let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  simp only [curveIntegral, curveIntegralFun_add]
  exact intervalIntegral.integral_add h₁ h₂
/-
**curveIntegral_fun_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegral_fun_add (h₁ : CurveIntegrable ω₁ γ) (h₂ : CurveIntegrable ω₂
 γ) : ∫ᶜ x in γ, (ω₁ x + ω₂ x) = ∫ᶜ x in γ, ω₁ x + ∫ᶜ x in γ, ω₂ x
参数：h₁ : CurveIntegrable ω₁ γ；h₂ : CurveIntegrable ω₂ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `curveIntegral_add`：curveIntegral_add (h₁ : CurveIntegrable ω₁ γ) (h₂ : C
urveIntegrable ω₂ γ) : curveIntegral (ω₁ + ω₂) γ = ∫ᶜ x in γ, ω₁ x + ∫ᶜ x in γ, 
ω₂ x
-/
theorem curveIntegral_fun_add (h₁ : CurveIntegrable ω₁ γ) (h₂ : CurveIntegrable ω₂ γ) :
    ∫ᶜ x in γ, (ω₁ x + ω₂ x) = ∫ᶜ x in γ, ω₁ x + ∫ᶜ x in γ, ω₂ x :=
  curveIntegral_add h₁ h₂

@[simp]
/-
**curveIntegralFun_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegralFun_zero : curveIntegralFun (0 : E -> E ->L[𝕜] F) γ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `curveIntegralFun_def'`：∀ {𝕜 : Type u_4} {E : Type u_5} {F : Type u_6} [i
nst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [in
st_3 : Norm…
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem curveIntegralFun_zero : curveIntegralFun (0 : E → E →L[𝕜] F) γ = 0 := by
  ext; simp [curveIntegralFun]

@[simp]
/-
**curveIntegralFun_fun_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegralFun_fun_zero : curveIntegralFun (fun _ => 0 : E -> E ->L[𝕜] F
) γ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `curveIntegralFun_zero`：curveIntegralFun_zero : curveIntegralFun (0 : E -
> E ->L[𝕜] F) γ = 0
-/
theorem curveIntegralFun_fun_zero : curveIntegralFun (fun _ ↦ 0 : E → E →L[𝕜] F) γ = 0 :=
  curveIntegralFun_zero

@[to_fun]
/-
**CurveIntegrable.zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CurveIntegrable.zero : CurveIntegrable (0 : E -> E ->L[𝕜] F) γ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `curveIntegralFun_zero`：curveIntegralFun_zero : curveIntegralFun (0 : E -
> E ->L[𝕜] F) γ = 0
-/
theorem CurveIntegrable.zero : CurveIntegrable (0 : E → E →L[𝕜] F) γ := by
  simp [CurveIntegrable, IntervalIntegrable.zero]

@[simp]
/-
**curveIntegral_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegral_zero : curveIntegral (0 : E -> E ->L[𝕜] F) γ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `curveIntegral_def'`：∀ {𝕜 : Type u_4} {E : Type u_5} {F : Type u_6} [inst
 : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_
3 : Norm…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `curveIntegralFun_zero`：curveIntegralFun_zero : curveIntegralFun (0 : E -
> E ->L[𝕜] F) γ = 0
· 使用定理 `intervalIntegral.integral_zero`：integral_zero : (∫ _ in a..b, (0 : E) ∂μ
) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem curveIntegral_zero : curveIntegral (0 : E → E →L[𝕜] F) γ = 0 := by simp [curveIntegral]

@[simp]
/-
**curveIntegral_fun_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegral_fun_zero : ∫ᶜ _ in γ, (0 : E ->L[𝕜] F) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `curveIntegral_zero`：curveIntegral_zero : curveIntegral (0 : E -> E ->L[𝕜
] F) γ = 0
-/
theorem curveIntegral_fun_zero : ∫ᶜ _ in γ, (0 : E →L[𝕜] F) = 0 := curveIntegral_zero

@[simp]
/-
**curveIntegralFun_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegralFun_neg : curveIntegralFun (-ω) γ = -curveIntegralFun ω γ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `curveIntegralFun_def'`：∀ {𝕜 : Type u_4} {E : Type u_5} {F : Type u_6} [i
nst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [in
st_3 : Norm…
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem curveIntegralFun_neg : curveIntegralFun (-ω) γ = -curveIntegralFun ω γ := by
  ext; simp [curveIntegralFun]

@[to_fun]
/-
**CurveIntegrable.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CurveIntegrable.neg (h : CurveIntegrable ω γ) : CurveIntegrable (-ω) γ
参数：h : CurveIntegrable ω γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `curveIntegralFun_neg`：curveIntegralFun_neg : curveIntegralFun (-ω) γ = -
curveIntegralFun ω γ
· 使用定理 `IntervalIntegrable.neg`：neg {f : Real -> E} (h : IntervalIntegrable f μ 
a b) : IntervalIntegrable (-f) μ a b
-/
theorem CurveIntegrable.neg (h : CurveIntegrable ω γ) : CurveIntegrable (-ω) γ := by
  simpa [CurveIntegrable] using IntervalIntegrable.neg h

@[simp]
/-
**curveIntegrable_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegrable_neg_iff : CurveIntegrable (-ω) γ ↔ CurveIntegrable ω γ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `CurveIntegrable.neg`：CurveIntegrable.neg (h : CurveIntegrable ω γ) : Cur
veIntegrable (-ω) γ
-/
theorem curveIntegrable_neg_iff : CurveIntegrable (-ω) γ ↔ CurveIntegrable ω γ :=
  ⟨fun h ↦ by simpa using h.neg, .neg⟩

@[simp]
/-
**curveIntegrable_fun_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegrable_fun_neg_iff : CurveIntegrable (-ω ·) γ ↔ CurveIntegrable ω
 γ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `curveIntegrable_neg_iff`：curveIntegrable_neg_iff : CurveIntegrable (-ω) 
γ ↔ CurveIntegrable ω γ
-/
theorem curveIntegrable_fun_neg_iff : CurveIntegrable (-ω ·) γ ↔ CurveIntegrable ω γ :=
  curveIntegrable_neg_iff

@[simp]
/-
**curveIntegral_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegral_neg : curveIntegral (-ω) γ = -∫ᶜ x in γ, ω x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `curveIntegral_def'`：∀ {𝕜 : Type u_4} {E : Type u_5} {F : Type u_6} [inst
 : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_
3 : Norm…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `curveIntegralFun_neg`：curveIntegralFun_neg : curveIntegralFun (-ω) γ = -
curveIntegralFun ω γ
· 使用定理 `intervalIntegral.integral_neg`：∀ {E : Type u_5} [inst : NormedAddCommGro
up E] [inst_1 : NormedSpace ℝ E] {a b : ℝ} {f : ℝ → E}   {μ : MeasureTheory.Meas
ure ℝ}, ∫ (x : ℝ) i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem curveIntegral_neg : curveIntegral (-ω) γ = -∫ᶜ x in γ, ω x := by
  simp [curveIntegral]

@[simp]
/-
**curveIntegral_fun_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegral_fun_neg : ∫ᶜ x in γ, -ω x = -∫ᶜ x in γ, ω x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `curveIntegral_neg`：curveIntegral_neg : curveIntegral (-ω) γ = -∫ᶜ x in γ
, ω x
-/
theorem curveIntegral_fun_neg : ∫ᶜ x in γ, -ω x = -∫ᶜ x in γ, ω x := curveIntegral_neg

@[simp]
/-
**curveIntegralFun_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegralFun_sub : curveIntegralFun (ω₁ - ω₂) γ = curveIntegralFun ω₁ 
γ - curveIntegralFun ω₂ γ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `curveIntegralFun_add`：curveIntegralFun_add : curveIntegralFun (ω₁ + ω₂) 
γ = curveIntegralFun ω₁ γ + curveIntegralFun ω₂ γ
· 使用定理 `curveIntegralFun_neg`：curveIntegralFun_neg : curveIntegralFun (-ω) γ = -
curveIntegralFun ω γ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem curveIntegralFun_sub :
    curveIntegralFun (ω₁ - ω₂) γ = curveIntegralFun ω₁ γ - curveIntegralFun ω₂ γ := by
  simp [sub_eq_add_neg]
/-
**CurveIntegrable.sub** 是 Mathlib 中的一个定理，位于命名空间 `CurveIntegrable`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : NormedAddCommGroup
 F] [inst_4 : NormedSpace 𝕜 F] {a b : E}   {ω₁ ω₂ : E → E →L[𝕜] F} {γ : Path a b
}, CurveIntegrable ω₁ γ → CurveIntegrable ω₂ γ → CurveIntegrable (ω₁ - ω₂) γ
参数：ω₁ - ω₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `CurveIntegrable.add`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [ins
t : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst
_3 : Norm…
· 使用定理 `CurveIntegrable.neg`：CurveIntegrable.neg (h : CurveIntegrable ω γ) : Cur
veIntegrable (-ω) γ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
protected theorem CurveIntegrable.sub (h₁ : CurveIntegrable ω₁ γ) (h₂ : CurveIntegrable ω₂ γ) :
    CurveIntegrable (ω₁ - ω₂) γ :=
  sub_eq_add_neg ω₁ ω₂ ▸ h₁.add h₂.neg
/-
**curveIntegral_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegral_sub (h₁ : CurveIntegrable ω₁ γ) (h₂ : CurveIntegrable ω₂ γ) 
: curveIntegral (ω₁ - ω₂) γ = ∫ᶜ x in γ, ω₁ x - ∫ᶜ x in γ, ω₂ x
参数：h₁ : CurveIntegrable ω₁ γ；h₂ : CurveIntegrable ω₂ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `curveIntegral_add`：curveIntegral_add (h₁ : CurveIntegrable ω₁ γ) (h₂ : C
urveIntegrable ω₂ γ) : curveIntegral (ω₁ + ω₂) γ = ∫ᶜ x in γ, ω₁ x + ∫ᶜ x in γ, 
ω₂ x
· 使用定理 `CurveIntegrable.neg`：CurveIntegrable.neg (h : CurveIntegrable ω γ) : Cur
veIntegrable (-ω) γ
· 使用定理 `curveIntegral_neg`：curveIntegral_neg : curveIntegral (-ω) γ = -∫ᶜ x in γ
, ω x
-/
theorem curveIntegral_sub (h₁ : CurveIntegrable ω₁ γ) (h₂ : CurveIntegrable ω₂ γ) :
    curveIntegral (ω₁ - ω₂) γ = ∫ᶜ x in γ, ω₁ x - ∫ᶜ x in γ, ω₂ x := by
  rw [sub_eq_add_neg, sub_eq_add_neg, curveIntegral_add h₁ h₂.neg, curveIntegral_neg]
/-
**curveIntegral_fun_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegral_fun_sub (h₁ : CurveIntegrable ω₁ γ) (h₂ : CurveIntegrable ω₂
 γ) : ∫ᶜ x in γ, (ω₁ x - ω₂ x) = ∫ᶜ x in γ, ω₁ x - ∫ᶜ x in γ, ω₂ x
参数：h₁ : CurveIntegrable ω₁ γ；h₂ : CurveIntegrable ω₂ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `curveIntegral_sub`：curveIntegral_sub (h₁ : CurveIntegrable ω₁ γ) (h₂ : C
urveIntegrable ω₂ γ) : curveIntegral (ω₁ - ω₂) γ = ∫ᶜ x in γ, ω₁ x - ∫ᶜ x in γ, 
ω₂ x
-/
theorem curveIntegral_fun_sub (h₁ : CurveIntegrable ω₁ γ) (h₂ : CurveIntegrable ω₂ γ) :
    ∫ᶜ x in γ, (ω₁ x - ω₂ x) = ∫ᶜ x in γ, ω₁ x - ∫ᶜ x in γ, ω₂ x :=
  curveIntegral_sub h₁ h₂


section RestrictScalars

variable {𝕝 : Type*} [RCLike 𝕝] [NormedSpace 𝕝 F] [NormedSpace 𝕝 E]
  [LinearMap.CompatibleSMul E F 𝕝 𝕜]

@[simp]
/-
**curveIntegralFun_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegralFun_restrictScalars : curveIntegralFun (fun t => (ω t).restri
ctScalars 𝕝) γ = curveIntegralFun ω γ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `curveIntegralFun_def`：curveIntegralFun_def [NormedSpace Real E] (ω : E -
> E ->L[𝕜] F) (γ : Path a b) (t : Real) : curveIntegralFun ω γ t = ω (γ.extend t
) (derivWi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem curveIntegralFun_restrictScalars :
    curveIntegralFun (fun t ↦ (ω t).restrictScalars 𝕝) γ = curveIntegralFun ω γ := by
  ext
  let : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  simp [curveIntegralFun_def]

@[simp]
/-
**curveIntegrable_restrictScalars_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegrable_restrictScalars_iff : CurveIntegrable (fun t => (ω t).rest
rictScalars 𝕝) γ ↔ CurveIntegrable ω γ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `curveIntegralFun_restrictScalars`：curveIntegralFun_restrictScalars : cur
veIntegralFun (fun t => (ω t).restrictScalars 𝕝) γ = curveIntegralFun ω γ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem curveIntegrable_restrictScalars_iff :
    CurveIntegrable (fun t ↦ (ω t).restrictScalars 𝕝) γ ↔ CurveIntegrable ω γ := by
  simp [CurveIntegrable]

@[simp]
/-
**curveIntegral_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegral_restrictScalars : ∫ᶜ x in γ, (ω x).restrictScalars 𝕝 = ∫ᶜ x 
in γ, ω x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `curveIntegral_def`：curveIntegral_def [NormedSpace Real F] (ω : E -> E ->
L[𝕜] F) (γ : Path a b) : curveIntegral ω γ = ∫ t in 0..1, curveIntegralFun ω γ t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `curveIntegralFun_restrictScalars`：curveIntegralFun_restrictScalars : cur
veIntegralFun (fun t => (ω t).restrictScalars 𝕝) γ = curveIntegralFun ω γ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem curveIntegral_restrictScalars :
    ∫ᶜ x in γ, (ω x).restrictScalars 𝕝 = ∫ᶜ x in γ, ω x := by
  let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  simp [curveIntegral_def]

end RestrictScalars

variable {𝕝 : Type*} [RCLike 𝕝] [NormedSpace 𝕝 F] [SMulCommClass 𝕜 𝕝 F] {c : 𝕝}

@[simp]
/-
**curveIntegralFun_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegralFun_smul : curveIntegralFun (c • ω) γ = c • curveIntegralFun 
ω γ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `curveIntegralFun_def'`：∀ {𝕜 : Type u_4} {E : Type u_5} {F : Type u_6} [i
nst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [in
st_3 : Norm…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem curveIntegralFun_smul : curveIntegralFun (c • ω) γ = c • curveIntegralFun ω γ := by
  ext
  simp [curveIntegralFun]
/-
**CurveIntegrable.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CurveIntegrable.smul (h : CurveIntegrable ω γ) : CurveIntegrable (c • ω) γ
参数：h : CurveIntegrable ω γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `curveIntegralFun_smul`：curveIntegralFun_smul : curveIntegralFun (c • ω) 
γ = c • curveIntegralFun ω γ
· 使用定理 `IntervalIntegrable.smul`：smul {R : Type*} [NormedAddCommGroup R] [SMulZe
roClass R E] [IsBoundedSMul R E] {f : Real -> E} (h : IntervalIntegrable f μ a b
) (r : R) : I…
-/
theorem CurveIntegrable.smul (h : CurveIntegrable ω γ) :
    CurveIntegrable (c • ω) γ := by
  simpa [CurveIntegrable] using IntervalIntegrable.smul h c

@[simp]
/-
**curveIntegrable_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegrable_smul_iff : CurveIntegrable (c • ω) γ ↔ c = 0 ∨ CurveIntegr
able ω γ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `CurveIntegrable.smul`：CurveIntegrable.smul (h : CurveIntegrable ω γ) : C
urveIntegrable (c • ω) γ
-/
theorem curveIntegrable_smul_iff : CurveIntegrable (c • ω) γ ↔ c = 0 ∨ CurveIntegrable ω γ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [CurveIntegrable.zero]
  · simp only [hc, false_or]
    refine ⟨fun h ↦ ?_, .smul⟩
    simpa [hc] using h.smul (c := c⁻¹)

@[simp]
/-
**curveIntegral_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegral_smul : curveIntegral (c • ω) γ = c • curveIntegral ω γ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `curveIntegral_def`：curveIntegral_def [NormedSpace Real F] (ω : E -> E ->
L[𝕜] F) (γ : Path a b) : curveIntegral ω γ = ∫ t in 0..1, curveIntegralFun ω γ t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `curveIntegralFun_smul`：curveIntegralFun_smul : curveIntegralFun (c • ω) 
γ = c • curveIntegralFun ω γ
· 使用定理 `intervalIntegral.integral_smul`：∀ {𝕜 : Type u_2} {E : Type u_5} [inst : 
NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {a b : ℝ}   {μ : MeasureTheory.
Measure ℝ} [inst_2 :…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem curveIntegral_smul : curveIntegral (c • ω) γ = c • curveIntegral ω γ := by
  let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  simp [curveIntegral_def, intervalIntegral.integral_smul]

@[simp]
/-
**curveIntegral_fun_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：curveIntegral_fun_smul : ∫ᶜ x in γ, c • ω x = c • ∫ᶜ x in γ, ω x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `curveIntegral_smul`：curveIntegral_smul : curveIntegral (c • ω) γ = c • c
urveIntegral ω γ
-/
theorem curveIntegral_fun_smul : ∫ᶜ x in γ, c • ω x = c • ∫ᶜ x in γ, ω x := curveIntegral_smul

end Algebra

section FDeriv

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {a b : E} {s : Set E} {ω : E → E →L[𝕜] F}

/-!
### Derivative of the curve integral w.r.t. the right endpoint

In this section we prove that the integral of `ω` along `[a -[ℝ] b]`, as a function of `b`,
has derivative `ω a` at `b = a`.
We provide several versions of this theorem, for `HasFDerivWithinAt` and `HasFDerivAt`,
as well as for continuity near a point and for continuity on the whole set or space.

Note that we take the derivative at the left endpoint of the segment.
Similar facts about the derivative at a different point are true
provided that `ω` is a closed 1-form (formalization WIP, see #24019).
-/

/-- The integral of `ω` along `[a -[ℝ] b]`, as a function of `b`, has derivative `ω a` at `b = a`.
This is a `HasFDerivWithinAt` version assuming that `ω` is continuous within a convex set `s`
in a neighborhood of `a` within `s`. -/
/-
**HasFDerivWithinAt.curveIntegral_segment_source'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.curveIntegral_segment_source' (hs : Convex Real s) (hω :
 forallᶠ x in 𝓝[s] a, ContinuousWithinAt ω s x) (ha : a in s) : HasFDerivWithinA
t (∫ᶜ x in .segment a ·, ω x) (ω a) s a
参数：hs : Convex Real s；hω : forallᶠ x in 𝓝[s] a, ContinuousWithinAt ω s x；ha : a 
in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Path.segment_same`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _r
oot_.Module ℝ E] [inst_2 : TopologicalSpace E]   [inst_3 : ContinuousAdd E] [ins
t_4 : C…
· 使用定理 `curveIntegral_refl`：curveIntegral_refl (ω : E -> E ->L[𝕜] F) (a : E) : ∫
ᶜ x in .refl a, ω x = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.mem_nhdsWithin_iff`：mem_nhdsWithin_iff {t : Set α} : s in 𝓝[t] x 
↔ exists ε > 0, ball x ε inter t subseteq s
· 使用定理 `Set.ofPred_and`：ofPred_and {p q : α -> Prop} : { a | p a ∧ q a } = { a |
 p a } inter { a | q a }
· 使用定理 `Filter.inter_mem_iff`：inter_mem_iff {s t : Set α} : s inter t in f ↔ s i
n f ∧ t in f
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.Eventually.self_of_nhdsWithin`：Filter.Eventually.self_of_nhdsWith
in {p : α -> Prop} {s : Set α} {x : α} (h : forallᶠ y in 𝓝[s] x, p y) (hx : x in
 s) : p x
· 使用定理 `Metric.closedBall_mem_nhds`：closedBall_mem_nhds (x : α) {ε : Real} (ε0 :
 0 < ε) : closedBall x ε in 𝓝 x
· 使用定理 `eventually_nhdsWithin_iff`：eventually_nhdsWithin_iff {a : α} {s : Set α}
 {p : α -> Prop} : (forallᶠ x in 𝓝[s] a, p x) ↔ forallᶠ x in 𝓝 a, x in s -> p x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Convex.segment_subset`：Convex.segment_subset (h : Convex 𝕜 s) {x y : E} 
(hx : x in s) (hy : y in s) : [x -[𝕜] y] subseteq s
· 使用定理 `Convex.inter`：Convex.inter {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 
t) : Convex 𝕜 (s inter t)
· 使用定理 `convex_ball`：convex_ball (a : E) (r : Real) : Convex Real (ball a r)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `curveIntegral_segment_const`：curveIntegral_segment_const [NormedSpace Re
al E] [CompleteSpace F] (ω : E ->L[𝕜] F) (a b : E) : ∫ᶜ _ in .segment a b, ω = ω
 (b - a)
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
The integral of `ω` along `[a -[ℝ] b]`, as a function of `b`, has derivative `ω 
a` at `b = a`.
This is a `HasFDerivWithinAt` version assuming that `ω` is continuous within a c
onvex set `s`
in a neighborhood of `a` within `s`.
-/
theorem HasFDerivWithinAt.curveIntegral_segment_source' (hs : Convex ℝ s)
    (hω : ∀ᶠ x in 𝓝[s] a, ContinuousWithinAt ω s x) (ha : a ∈ s) :
    HasFDerivWithinAt (∫ᶜ x in .segment a ·, ω x) (ω a) s a := by
  /- Given `ε > 0`, take a number `δ > 0` such that `ω` is continuous on `ball a δ ∩ s`
  and `‖ω z - ω a‖ ≤ ε` on this set.
  Then for `b ∈ ball a δ ∩ s`, we have
  `‖(∫ᶜ x in .segment a b, ω x) - ω a (b - a)‖
    = ‖(∫ᶜ x in .segment a b, ω x) - ∫ᶜ x in .segment a b, ω a‖
    ≤ ∫ x in 0..1, ‖ω x - ω a‖ * ‖b - a‖
    ≤ ε * ‖b - a‖`
  -/
  simp only [hasFDerivWithinAt_iff_isLittleO, Path.segment_same, curveIntegral_refl, sub_zero,
    Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ₀, hδ⟩ : ∃ δ > 0,
      ball a δ ∩ s ⊆ {z | ContinuousWithinAt ω s z ∧ dist (ω z) (ω a) ≤ ε} := by
    rw [← Metric.mem_nhdsWithin_iff, ofPred_and, inter_mem_iff]
    exact ⟨hω, (hω.self_of_nhdsWithin ha).eventually <| closedBall_mem_nhds _ hε⟩
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds _ hδ₀] with b hb hbs
  have hsub : [a -[ℝ] b] ⊆ ball a δ ∩ s :=
    ((convex_ball _ _).inter hs).segment_subset (by simp [*]) (by simp [*])
  rw [← curveIntegral_segment_const, ← curveIntegral_fun_sub]
  · refine norm_curveIntegral_segment_le fun z hz ↦ ?_
    simpa [dist_eq_norm] using (hδ (hsub hz)).2
  · rw [curveIntegrable_segment]
    refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one fun t ht ↦ ?_
    refine ((hδ ?_).1.eval_const _).comp AffineMap.lineMap_continuous.continuousWithinAt ?_
    · exact hsub <| lineMap_mem_segment ℝ a b ht
    · rw [mapsTo_iff_image_subset, ← segment_eq_image_lineMap]
      exact hs.segment_subset ha hbs
  · rw [curveIntegrable_segment]
    exact intervalIntegrable_const

/-- The integral of `ω` along `[a -[ℝ] b]`, as a function of `b`, has derivative `ω a` at `b = a`.
This is a `HasFDerivWithinAt` version assuming that `ω` is continuous on `s`. -/
/-
**HasFDerivWithinAt.curveIntegral_segment_source** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.curveIntegral_segment_source (hs : Convex Real s) (hω : 
ContinuousOn ω s) (ha : a in s) : HasFDerivWithinAt (∫ᶜ x in .segment a ·, ω x) 
(ω a) s a
参数：hs : Convex Real s；hω : ContinuousOn ω s；ha : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasFDerivWithinAt.curveIntegral_segment_source'`：HasFDerivWithinAt.curve
Integral_segment_source' (hs : Convex Real s) (hω : forallᶠ x in 𝓝[s] a, Continu
ousWithinAt ω s x) (ha : a in s) : Ha…
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a

--- 原说明 ---
The integral of `ω` along `[a -[ℝ] b]`, as a function of `b`, has derivative `ω 
a` at `b = a`.
This is a `HasFDerivWithinAt` version assuming that `ω` is continuous on `s`.
-/
theorem HasFDerivWithinAt.curveIntegral_segment_source (hs : Convex ℝ s) (hω : ContinuousOn ω s)
    (ha : a ∈ s) : HasFDerivWithinAt (∫ᶜ x in .segment a ·, ω x) (ω a) s a :=
  .curveIntegral_segment_source' hs (mem_of_superset self_mem_nhdsWithin hω) ha

/-- The integral of `ω` along `[a -[ℝ] b]`, as a function of `b`, has derivative `ω a` at `b = a`.
This is a `HasFDerivAt` version assuming that `ω` is continuous in a neighborhood of `a`. -/
/-
**HasFDerivAt.curveIntegral_segment_source'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.curveIntegral_segment_source' (hω : forallᶠ z in 𝓝 a, Continuo
usAt ω z) : HasFDerivAt (∫ᶜ x in .segment a ·, ω x) (ω a) a
参数：hω : forallᶠ z in 𝓝 a, ContinuousAt ω z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasFDerivWithinAt.hasFDerivAt_of_univ`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.M
odule 𝕜 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.curveIntegral_segment_source'`：HasFDerivWithinAt.curve
Integral_segment_source' (hs : Convex Real s) (hω : forallᶠ x in 𝓝[s] a, Continu
ousWithinAt ω s x) (ha : a in s) : Ha…
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
The integral of `ω` along `[a -[ℝ] b]`, as a function of `b`, has derivative `ω 
a` at `b = a`.
This is a `HasFDerivAt` version assuming that `ω` is continuous in a neighborhoo
d of `a`.
-/
theorem HasFDerivAt.curveIntegral_segment_source' (hω : ∀ᶠ z in 𝓝 a, ContinuousAt ω z) :
    HasFDerivAt (∫ᶜ x in .segment a ·, ω x) (ω a) a :=
  HasFDerivWithinAt.curveIntegral_segment_source' convex_univ
    (by simpa only [nhdsWithin_univ, continuousWithinAt_univ]) (mem_univ _) |>.hasFDerivAt_of_univ

/-- The integral of `ω` along `[a -[ℝ] b]`, as a function of `b`, has derivative `ω a` at `b = a`.
This is a `HasFDerivAt` version assuming that `ω` is continuous on the whole space. -/
/-
**HasFDerivAt.curveIntegral_segment_source** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.curveIntegral_segment_source (hω : Continuous ω) : HasFDerivAt
 (∫ᶜ x in .segment a ·, ω x) (ω a) a
参数：hω : Continuous ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasFDerivAt.curveIntegral_segment_source'`：HasFDerivAt.curveIntegral_seg
ment_source' (hω : forallᶠ z in 𝓝 a, ContinuousAt ω z) : HasFDerivAt (∫ᶜ x in .s
egment a ·, ω x) (ω a) a
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x

--- 原说明 ---
The integral of `ω` along `[a -[ℝ] b]`, as a function of `b`, has derivative `ω 
a` at `b = a`.
This is a `HasFDerivAt` version assuming that `ω` is continuous on the whole spa
ce.
-/
theorem HasFDerivAt.curveIntegral_segment_source (hω : Continuous ω) :
    HasFDerivAt (∫ᶜ x in .segment a ·, ω x) (ω a) a :=
  .curveIntegral_segment_source' <| .of_forall fun _ ↦ hω.continuousAt

end FDeriv

