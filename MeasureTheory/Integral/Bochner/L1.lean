/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.SetToL1

/-!
# Bochner integral

The Bochner integral extends the definition of the Lebesgue integral to functions that map from a
measure space into a Banach space (complete normed vector space). It is constructed here
for L1 functions by extending the integral on simple functions. See the file
`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` for the integral of functions
and corresponding API.

## Main definitions

The Bochner integral is defined through the extension process described in the file
`Mathlib/MeasureTheory/Integral/SetToL1.lean`, which follows these steps:

1. Define the integral of the indicator of a set. This is `weightedSMul μ s x = μ.real s • x`.
  `weightedSMul μ` is shown to be linear in the value `x` and `DominatedFinMeasAdditive`
  (defined in the file `Mathlib/MeasureTheory/Integral/SetToL1.lean`) with respect to the set `s`.

2. Define the integral on simple functions of the type `SimpleFunc α E` (notation : `α →ₛ E`)
  where `E` is a real normed space. (See `SimpleFunc.integral` for details.)

3. Transfer this definition to define the integral on `L1.simpleFunc α E` (notation :
  `α →₁ₛ[μ] E`), see `L1.simpleFunc.integral`. Show that this integral is a continuous linear
  map from `α →₁ₛ[μ] E` to `E`.

4. Define the Bochner integral on L1 functions by extending the integral on integrable simple
  functions `α →₁ₛ[μ] E` using `ContinuousLinearMap.extend` and the fact that the embedding of
  `α →₁ₛ[μ] E` into `α →₁[μ] E` is dense.

## Notation

* `α →ₛ E` : simple functions (defined in `Mathlib/MeasureTheory/Function/SimpleFunc.lean`)
* `α →₁[μ] E` : functions in L1 space, i.e., equivalence classes of integrable functions (defined in
                `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`)
* `α →₁ₛ[μ] E` : simple functions in L1 space, i.e., equivalence classes of integrable simple
                 functions (defined in `Mathlib/MeasureTheory/Function/SimpleFuncDenseLp.lean`)

Note: `ₛ` is typed using `\_s`. Sometimes it shows as a box if the font is missing.

## Tags

Bochner integral, simple function, function space, Lebesgue dominated convergence theorem

-/

@[expose] public section


assert_not_exists Differentiable

noncomputable section

open Filter ENNReal Set
open scoped NNReal ENNReal MeasureTheory

namespace MeasureTheory

variable {α E F 𝕜 : Type*}

section WeightedSMul

open ContinuousLinearMap

variable [NormedAddCommGroup F] [NormedSpace ℝ F] {m : MeasurableSpace α} {μ : Measure α}

/-- Given a set `s`, return the continuous linear map `fun x => μ.real s • x`. The extension
of that set function through `setToL1` gives the Bochner integral of L1 functions. -/
/-
**MeasureTheory.weightedSMul** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：weightedSMul {_ : MeasurableSpace α} (μ : Measure α) (s : Set α) : F ->L[R
eal] F
参数：μ : Measure α；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a set `s`, return the continuous linear map `fun x => μ.real s • x`. The e
xtension
of that set function through `setToL1` gives the Bochner integral of L1 function
s.
-/
def weightedSMul {_ : MeasurableSpace α} (μ : Measure α) (s : Set α) : F →L[ℝ] F :=
  μ.real s • ContinuousLinearMap.id ℝ F
/-
**MeasureTheory.weightedSMul_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：weightedSMul_apply {m : MeasurableSpace α} (μ : Measure α) (s : Set α) (x 
: F) : weightedSMul μ s x = μ.real s • x
参数：μ : Measure α；s : Set α；x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem weightedSMul_apply {m : MeasurableSpace α} (μ : Measure α) (s : Set α) (x : F) :
    weightedSMul μ s x = μ.real s • x := by simp [weightedSMul]

@[simp]
/-
**MeasureTheory.weightedSMul_zero_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：weightedSMul_zero_measure {m : MeasurableSpace α} : weightedSMul (0 : Meas
ure α) = (0 : Set α -> F ->L[Real] F)
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
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem weightedSMul_zero_measure {m : MeasurableSpace α} :
    weightedSMul (0 : Measure α) = (0 : Set α → F →L[ℝ] F) := by ext1; simp [weightedSMul]

@[simp]
/-
**MeasureTheory.weightedSMul_empty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：weightedSMul_empty {m : MeasurableSpace α} (μ : Measure α) : weightedSMul 
μ ∅ = (0 : F ->L[Real] F)
参数：μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.weightedSMul_apply`：weightedSMul_apply {m : MeasurableSpac
e α} (μ : Measure α) (s : Set α) (x : F) : weightedSMul μ s x = μ.real s • x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.measureReal_empty`：∀ {α : Type u_1} {x : MeasurableSpace α
} {μ : MeasureTheory.Measure α}, μ.real ∅ = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem weightedSMul_empty {m : MeasurableSpace α} (μ : Measure α) :
    weightedSMul μ ∅ = (0 : F →L[ℝ] F) := by ext1 x; rw [weightedSMul_apply]; simp
/-
**MeasureTheory.weightedSMul_add_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：weightedSMul_add_measure {m : MeasurableSpace α} (μ ν : Measure α) {s : Se
t α} (hμs : μ s != ∞) (hνs : ν s != ∞) : (weightedSMul (μ + ν) s : F ->L[Real] F
) = weightedSMul μ s + weightedSMul ν s
参数：μ ν : Measure α；hμs : μ s != ∞；hνs : ν s != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `FunLike.coe_add`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst : 
FunLike F α β] [inst_1 : Add F] [inst_2 : Add β]   [IsAddApply F α β] (f g : F),
 ⇑(f …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.weightedSMul_apply`：weightedSMul_apply {m : MeasurableSpac
e α} (μ : Measure α) (s : Set α) (x : F) : weightedSMul μ s x = μ.real s • x
· 使用定理 `MeasureTheory.measureReal_add_apply`：measureReal_add_apply {μ₁ μ₂ : Meas
ure α} (h₁ : μ₁ s != ∞
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
-/
theorem weightedSMul_add_measure {m : MeasurableSpace α} (μ ν : Measure α) {s : Set α}
    (hμs : μ s ≠ ∞) (hνs : ν s ≠ ∞) :
    (weightedSMul (μ + ν) s : F →L[ℝ] F) = weightedSMul μ s + weightedSMul ν s := by
  ext1 x
  push_cast
  simp_rw [Pi.add_apply, weightedSMul_apply]
  rw [measureReal_add_apply, add_smul]
/-
**MeasureTheory.weightedSMul_smul_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：weightedSMul_smul_measure {m : MeasurableSpace α} (μ : Measure α) (c : Rea
l>=0∞) {s : Set α} : (weightedSMul (c • μ) s : F ->L[Real] F) = c.toReal • weigh
tedSMul μ s
参数：μ : Measure α；c : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
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
· 使用定理 `MeasureTheory.weightedSMul_apply`：weightedSMul_apply {m : MeasurableSpac
e α} (μ : Measure α) (s : Set α) (x : F) : weightedSMul μ s x = μ.real s • x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.measureReal_ennreal_smul_apply`：∀ {α : Type u_1} {x : Meas
urableSpace α} {μ : MeasureTheory.Measure α} {s : Set α} (c : ENNReal),   (c • μ
).real s = c.toReal * μ.real s
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem weightedSMul_smul_measure {m : MeasurableSpace α} (μ : Measure α) (c : ℝ≥0∞) {s : Set α} :
    (weightedSMul (c • μ) s : F →L[ℝ] F) = c.toReal • weightedSMul μ s := by
  ext1 x
  simp [weightedSMul_apply, smul_smul]
/-
**MeasureTheory.weightedSMul_congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：weightedSMul_congr (s t : Set α) (hst : μ s = μ t) : (weightedSMul μ s : F
 ->L[Real] F) = weightedSMul μ t
参数：s t : Set α；hst : μ s = μ t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.weightedSMul_apply`：weightedSMul_apply {m : MeasurableSpac
e α} (μ : Measure α) (s : Set α) (x : F) : weightedSMul μ s x = μ.real s • x
-/
theorem weightedSMul_congr (s t : Set α) (hst : μ s = μ t) :
    (weightedSMul μ s : F →L[ℝ] F) = weightedSMul μ t := by
  ext1 x; simp_rw [weightedSMul_apply, measureReal_def]; congr 2
/-
**MeasureTheory.weightedSMul_null** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：weightedSMul_null {s : Set α} (h_zero : μ s = 0) : (weightedSMul μ s : F -
>L[Real] F) = 0
参数：h_zero : μ s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.weightedSMul_apply`：weightedSMul_apply {m : MeasurableSpac
e α} (μ : Measure α) (s : Set α) (x : F) : weightedSMul μ s x = μ.real s • x
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem weightedSMul_null {s : Set α} (h_zero : μ s = 0) : (weightedSMul μ s : F →L[ℝ] F) = 0 := by
  ext1 x; rw [weightedSMul_apply, measureReal_def, h_zero]; simp
/-
**MeasureTheory.weightedSMul_union'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：weightedSMul_union' (s t : Set α) (ht : MeasurableSet t) (hs_finite : μ s 
!= ∞) (ht_finite : μ t != ∞) (hdisj : Disjoint s t) : (weightedSMul μ (s union t
) : F ->L[Real] F) = weightedSMul μ s + weightedSMul μ t
参数：s t : Set α；ht : MeasurableSet t；hs_finite : μ s != ∞；ht_finite : μ t != ∞；hd
isj : Disjoint s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.weightedSMul_apply`：weightedSMul_apply {m : MeasurableSpac
e α} (μ : Measure α) (s : Set α) (x : F) : weightedSMul μ s x = μ.real s • x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.measureReal_union`：measureReal_union (hd : Disjoint s₁ s₂)
 (h : MeasurableSet s₂) (h₁ : μ s₁ != ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem weightedSMul_union' (s t : Set α) (ht : MeasurableSet t) (hs_finite : μ s ≠ ∞)
    (ht_finite : μ t ≠ ∞) (hdisj : Disjoint s t) :
    (weightedSMul μ (s ∪ t) : F →L[ℝ] F) = weightedSMul μ s + weightedSMul μ t := by
  ext1 x
  simp_rw [add_apply, weightedSMul_apply, measureReal_union hdisj ht, add_smul]

@[nolint unusedArguments]
/-
**MeasureTheory.weightedSMul_union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：weightedSMul_union (s t : Set α) (_hs : MeasurableSet s) (ht : MeasurableS
et t) (hs_finite : μ s != ∞) (ht_finite : μ t != ∞) (hdisj : Disjoint s t) : (we
ightedSMul μ (s union t) : F ->L[Real] F) = weightedSMul μ s + weightedSMul μ t
参数：s t : Set α；_hs : MeasurableSet s；ht : MeasurableSet t；hs_finite : μ s != ∞；h
t_finite : μ t != ∞；hdisj : Disjoint s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.weightedSMul_union'`：weightedSMul_union' (s t : Set α) (ht
 : MeasurableSet t) (hs_finite : μ s != ∞) (ht_finite : μ t != ∞) (hdisj : Disjo
int s t) : (weightedSMu…
-/
theorem weightedSMul_union (s t : Set α) (_hs : MeasurableSet s) (ht : MeasurableSet t)
    (hs_finite : μ s ≠ ∞) (ht_finite : μ t ≠ ∞) (hdisj : Disjoint s t) :
    (weightedSMul μ (s ∪ t) : F →L[ℝ] F) = weightedSMul μ s + weightedSMul μ t :=
  weightedSMul_union' s t ht hs_finite ht_finite hdisj
/-
**MeasureTheory.weightedSMul_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：weightedSMul_smul [SMul 𝕜 F] [SMulCommClass Real 𝕜 F] (c : 𝕜) (s : Set α) 
(x : F) : weightedSMul μ s (c • x) = c • weightedSMul μ s x
参数：c : 𝕜；s : Set α；x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.weightedSMul_apply`：weightedSMul_apply {m : MeasurableSpac
e α} (μ : Measure α) (s : Set α) (x : F) : weightedSMul μ s x = μ.real s • x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem weightedSMul_smul [SMul 𝕜 F] [SMulCommClass ℝ 𝕜 F] (c : 𝕜)
    (s : Set α) (x : F) : weightedSMul μ s (c • x) = c • weightedSMul μ s x := by
  simp_rw [weightedSMul_apply, smul_comm]
/-
**MeasureTheory.norm_weightedSMul_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：norm_weightedSMul_le (s : Set α) : ‖(weightedSMul μ s : F ->L[Real] F)‖ <=
 μ.real s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `ContinuousLinearMap.norm_id_le`：norm_id_le : ‖ContinuousLinearMap.id 𝕜 E
‖ <= 1
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_eq_self`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOr
der G] [IsOrderedAddMonoid G] {a : G}, |a| = a ↔ 0 ≤ a
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
-/
theorem norm_weightedSMul_le (s : Set α) : ‖(weightedSMul μ s : F →L[ℝ] F)‖ ≤ μ.real s :=
  calc
    ‖(weightedSMul μ s : F →L[ℝ] F)‖ = ‖μ.real s‖ * ‖ContinuousLinearMap.id ℝ F‖ :=
      norm_smul (μ.real s) (ContinuousLinearMap.id ℝ F)
    _ ≤ ‖μ.real s‖ :=
      ((mul_le_mul_of_nonneg_left norm_id_le (norm_nonneg _)).trans (mul_one _).le)
    _ = abs μ.real s := Real.norm_eq_abs _
    _ = μ.real s := abs_eq_self.mpr ENNReal.toReal_nonneg
/-
**MeasureTheory.dominatedFinMeasAdditive_weightedSMul** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：dominatedFinMeasAdditive_weightedSMul {_ : MeasurableSpace α} (μ : Measure
 α) : DominatedFinMeasAdditive μ (weightedSMul μ : Set α -> F ->L[Real] F) 1
参数：μ : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.weightedSMul_union`：weightedSMul_union (s t : Set α) (_hs 
: MeasurableSet s) (ht : MeasurableSet t) (hs_finite : μ s != ∞) (ht_finite : μ 
t != ∞) (hdisj : Disjo…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.norm_weightedSMul_le`：norm_weightedSMul_le (s : Set α) : ‖
(weightedSMul μ s : F ->L[Real] F)‖ <= μ.real s
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem dominatedFinMeasAdditive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) :
    DominatedFinMeasAdditive μ (weightedSMul μ : Set α → F →L[ℝ] F) 1 :=
  ⟨weightedSMul_union, fun s _ _ => (norm_weightedSMul_le s).trans (one_mul _).symm.le⟩
/-
**MeasureTheory.weightedSMul_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：weightedSMul_nonneg [PartialOrder F] [IsOrderedModule Real F] (s : Set α) 
(x : F) (hx : 0 <= x) : 0 <= weightedSMul μ s x
参数：s : Set α；x : F；hx : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用引理 `smul_nonneg`：smul_nonneg [PosSMulMono α β] (ha : 0 <= a) (hb : 0 <= b₁) 
: 0 <= a • b₁
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
-/
theorem weightedSMul_nonneg [PartialOrder F] [IsOrderedModule ℝ F]
    (s : Set α) (x : F) (hx : 0 ≤ x) : 0 ≤ weightedSMul μ s x := by
  simp only [weightedSMul, _root_.id, coe_id', smul_apply]
  exact smul_nonneg toReal_nonneg hx

end WeightedSMul

local infixr:25 " →ₛ " => SimpleFunc

namespace SimpleFunc

section PosPart

variable [LinearOrder E] [Zero E] [MeasurableSpace α]

/-- Positive part of a simple function. -/
/-
**MeasureTheory.SimpleFunc.posPart** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Simp
leFunc`。
形式化陈述：posPart (f : α ->ₛ E) : α ->ₛ E
参数：f : α ->ₛ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Positive part of a simple function.
-/
def posPart (f : α →ₛ E) : α →ₛ E :=
  f.map fun b => max b 0

/-- Negative part of a simple function. -/
/-
**MeasureTheory.SimpleFunc.negPart** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Simp
leFunc`。
形式化陈述：negPart [Neg E] (f : α ->ₛ E) : α ->ₛ E
参数：f : α ->ₛ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Negative part of a simple function.
-/
def negPart [Neg E] (f : α →ₛ E) : α →ₛ E :=
  posPart (-f)
/-
**MeasureTheory.SimpleFunc.posPart_map_norm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.SimpleFunc`。
形式化陈述：posPart_map_norm (f : α ->ₛ Real) : (posPart f).map norm = posPart f
参数：f : α ->ₛ Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.ext`：ext {f g : α ->ₛ β} (H : forall a, f a = g
 a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.map_apply`：map_apply (g : β -> γ) (f : α ->ₛ β)
 (a) : f.map g a = g (f a)
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem posPart_map_norm (f : α →ₛ ℝ) : (posPart f).map norm = posPart f := by
  ext; rw [map_apply, Real.norm_eq_abs, abs_of_nonneg]; exact le_max_right _ _
/-
**MeasureTheory.SimpleFunc.negPart_map_norm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.SimpleFunc`。
形式化陈述：negPart_map_norm (f : α ->ₛ Real) : (negPart f).map norm = negPart f
参数：f : α ->ₛ Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.negPart.eq_1`：∀ {α : Type u_1} {E : Type u_2} [
inst : LinearOrder E] [inst_1 : Zero E] [inst_2 : MeasurableSpace α] [inst_3 : N
eg E]   (f : MeasureTheory.…
· 使用定理 `MeasureTheory.SimpleFunc.posPart_map_norm`：posPart_map_norm (f : α ->ₛ R
eal) : (posPart f).map norm = posPart f
-/
theorem negPart_map_norm (f : α →ₛ ℝ) : (negPart f).map norm = negPart f := by
  rw [negPart]; exact posPart_map_norm _
/-
**MeasureTheory.SimpleFunc.posPart_sub_negPart** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.SimpleFunc`。
形式化陈述：posPart_sub_negPart (f : α ->ₛ Real) : f.posPart - f.negPart = f
参数：f : α ->ₛ Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.ext`：ext {f g : α ->ₛ β} (H : forall a, f a = g
 a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.coe_sub`：∀ {α : Type u_1} {β : Type u_2} [inst 
: MeasurableSpace α] [inst_1 : Sub β] (f g : MeasureTheory.SimpleFunc α β),   ⇑(
f - g) = ⇑f - ⇑g
· 使用定理 `max_zero_sub_eq_self`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : Lin
earOrder α] [AddLeftMono α] (a : α), max a 0 - max (-a) 0 = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem posPart_sub_negPart (f : α →ₛ ℝ) : f.posPart - f.negPart = f := by
  simp only [posPart, negPart]
  ext a
  rw [coe_sub]
  exact max_zero_sub_eq_self (f a)

end PosPart

section Integral

/-!
### The Bochner integral of simple functions

Define the Bochner integral of simple functions of the type `α →ₛ β` where `β` is a normed group,
and prove basic properties of this integral.
-/


open Finset

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {m : MeasurableSpace α} {μ : Measure α}

/-- Bochner integral of simple functions whose codomain is a real `NormedSpace`.
This is equal to `∑ x ∈ f.range, μ.real (f ⁻¹' {x}) • x` (see `integral_eq`). -/
/-
**MeasureTheory.SimpleFunc.integral** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Sim
pleFunc`。
形式化陈述：integral {_ : MeasurableSpace α} (μ : Measure α) (f : α ->ₛ F) : F
参数：μ : Measure α；f : α ->ₛ F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bochner integral of simple functions whose codomain is a real `NormedSpace`.
This is equal to `∑ x ∈ f.range, μ.real (f ⁻¹' {x}) • x` (see `integral_eq`).
-/
def integral {_ : MeasurableSpace α} (μ : Measure α) (f : α →ₛ F) : F :=
  f.setToSimpleFunc (weightedSMul μ)
/-
**MeasureTheory.SimpleFunc.integral_def** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.SimpleFunc`。
形式化陈述：integral_def {_ : MeasurableSpace α} (μ : Measure α) (f : α ->ₛ F) : f.int
egral μ = f.setToSimpleFunc (weightedSMul μ)
参数：μ : Measure α；f : α ->ₛ F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem integral_def {_ : MeasurableSpace α} (μ : Measure α) (f : α →ₛ F) :
    f.integral μ = f.setToSimpleFunc (weightedSMul μ) := rfl
/-
**MeasureTheory.SimpleFunc.integral_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
SimpleFunc`。
形式化陈述：integral_eq {m : MeasurableSpace α} (μ : Measure α) (f : α ->ₛ F) : f.inte
gral μ = ∑ x in f.range, μ.real (f ⁻¹' {x}) • x
参数：μ : Measure α；f : α ->ₛ F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MeasureTheory.weightedSMul_apply`：weightedSMul_apply {m : MeasurableSpac
e α} (μ : Measure α) (s : Set α) (x : F) : weightedSMul μ s x = μ.real s • x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_eq {m : MeasurableSpace α} (μ : Measure α) (f : α →ₛ F) :
    f.integral μ = ∑ x ∈ f.range, μ.real (f ⁻¹' {x}) • x := by
  simp [integral, setToSimpleFunc, weightedSMul_apply]
/-
**MeasureTheory.SimpleFunc.integral_eq_sum_filter** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.SimpleFunc`。
形式化陈述：integral_eq_sum_filter [DecidablePred fun x : F => x != 0] {m : Measurable
Space α} (f : α ->ₛ F) (μ : Measure α) : f.integral μ = ∑ x in {x in f.range | x
 != 0}, μ.real (f ⁻¹' {x}) • x
参数：f : α ->ₛ F；μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_eq_sum_filter`：setToSimpleFunc_
eq_sum_filter [DecidablePred fun x => x != (0 : F)] {m : MeasurableSpace α} (T :
 Set α -> F ->L[Real] F') (f : α ->ₛ F) : se…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MeasureTheory.weightedSMul_apply`：weightedSMul_apply {m : MeasurableSpac
e α} (μ : Measure α) (s : Set α) (x : F) : weightedSMul μ s x = μ.real s • x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_eq_sum_filter [DecidablePred fun x : F => x ≠ 0] {m : MeasurableSpace α}
    (f : α →ₛ F) (μ : Measure α) :
    f.integral μ = ∑ x ∈ {x ∈ f.range | x ≠ 0}, μ.real (f ⁻¹' {x}) • x := by
  simp_rw [integral_def, setToSimpleFunc_eq_sum_filter, weightedSMul_apply]

/-- The Bochner integral is equal to a sum over any set that includes `f.range` (except `0`). -/
/-
**MeasureTheory.SimpleFunc.integral_eq_sum_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.SimpleFunc`。
形式化陈述：integral_eq_sum_of_subset [DecidablePred fun x : F => x != 0] {f : α ->ₛ F
} {s : Finset F} (hs : {x in f.range | x != 0} subseteq s) : f.integral μ = ∑ x 
in s, μ.real (f ⁻¹' {x}) • x
参数：hs : {x in f.range | x != 0} subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.integral_eq_sum_filter`：integral_eq_sum_filter 
[DecidablePred fun x : F => x != 0] {m : MeasurableSpace α} (f : α ->ₛ F) (μ : M
easure α) : f.integral μ = ∑ x in {x …
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_eq_empty`：preimage_eq_empty {s : Set β} (h : Disjoint s (ra
nge f)) : f ⁻¹' s = ∅
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MeasureTheory.SimpleFunc.mem_range`：mem_range {f : α ->ₛ β} {b} : b in f
.range ↔ b in range f
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.measureReal_empty`：∀ {α : Type u_1} {x : MeasurableSpace α
} {μ : MeasureTheory.Measure α}, μ.real ∅ = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0

--- 原说明 ---
The Bochner integral is equal to a sum over any set that includes `f.range` (exc
ept `0`).
-/
theorem integral_eq_sum_of_subset [DecidablePred fun x : F => x ≠ 0] {f : α →ₛ F} {s : Finset F}
    (hs : {x ∈ f.range | x ≠ 0} ⊆ s) :
    f.integral μ = ∑ x ∈ s, μ.real (f ⁻¹' {x}) • x := by
  rw [SimpleFunc.integral_eq_sum_filter, Finset.sum_subset hs]
  rintro x - hx; rw [Finset.mem_filter, not_and_or, Ne, Classical.not_not] at hx
  rcases hx.symm with (rfl | hx)
  · simp
  rw [SimpleFunc.mem_range] at hx
  rw [preimage_eq_empty] <;> simp [Set.disjoint_singleton_left, hx]

@[simp]
/-
**MeasureTheory.SimpleFunc.integral_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.SimpleFunc`。
形式化陈述：integral_const {m : MeasurableSpace α} (μ : Measure α) (y : F) : (const α 
y).integral μ = μ.real univ • y
参数：μ : Measure α；y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.integral_eq_sum_of_subset`：integral_eq_sum_of_s
ubset [DecidablePred fun x : F => x != 0] {f : α ->ₛ F} {s : Finset F} (hs : {x 
in f.range | x != 0} subseteq s) : f.int…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
· 使用定理 `MeasureTheory.SimpleFunc.range_const_subset`：range_const_subset (α) [Mea
surableSpace α] (b : β) : (const α b).range subseteq {b}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_const {m : MeasurableSpace α} (μ : Measure α) (y : F) :
    (const α y).integral μ = μ.real univ • y := by
  classical
  calc
    (const α y).integral μ = ∑ z ∈ {y}, μ.real (const α y ⁻¹' {z}) • z :=
      integral_eq_sum_of_subset <| (filter_subset _ _).trans (range_const_subset _ _)
    _ = μ.real univ • y := by simp [Set.preimage]

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**MeasureTheory.SimpleFunc.integral_piecewise_zero** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.SimpleFunc`。
形式化陈述：integral_piecewise_zero {m : MeasurableSpace α} (f : α ->ₛ F) (μ : Measure
 α) {s : Set α} (hs : MeasurableSet s) : (piecewise s hs f 0).integral μ = f.int
egral (μ.restrict s)
参数：f : α ->ₛ F；μ : Measure α；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.SimpleFunc.integral_eq_sum_of_subset`：integral_eq_sum_of_s
ubset [DecidablePred fun x : F => x != 0] {f : α ->ₛ F} {s : Finset F} (hs : {x 
in f.range | x != 0} subseteq s) : f.int…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.piecewise_eq_indicator`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero
 M] {s : Set α} {f : α → M} [inst_1 : DecidablePred fun x => x ∈ s],   s.piecewi
se f 0 = s.indic…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Set.indicator_preimage_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst 
: Zero M] (s : Set α) (f : α → M) {t : Set M},   0 ∉ t → s.indicator f ⁻¹' t = f
 ⁻¹' t ∩ s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `MeasureTheory.measureReal_restrict_apply`：measureReal_restrict_apply (ht
 : MeasurableSet t) : (μ.restrict s).real t = μ.real (t inter s)
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_preimage`：measurableSet_preimage 
(f : α ->ₛ β) (s) : MeasurableSet (f ⁻¹' s)
· 使用定理 `MeasureTheory.SimpleFunc.integral_eq_sum_filter`：integral_eq_sum_filter 
[DecidablePred fun x : F => x != 0] {m : MeasurableSpace α} (f : α ->ₛ F) (μ : M
easure α) : f.integral μ = ∑ x in {x …
-/
theorem integral_piecewise_zero {m : MeasurableSpace α} (f : α →ₛ F) (μ : Measure α) {s : Set α}
    (hs : MeasurableSet s) : (piecewise s hs f 0).integral μ = f.integral (μ.restrict s) := by
  classical
  refine (integral_eq_sum_of_subset ?_).trans
      ((sum_congr rfl fun y hy => ?_).trans (integral_eq_sum_filter _ _).symm)
  · intro y hy
    simp only [mem_filter, mem_range, coe_piecewise, coe_zero, piecewise_eq_indicator,
      mem_range_indicator] at *
    rcases hy with ⟨⟨rfl, -⟩ | ⟨x, -, rfl⟩, h₀⟩
    exacts [(h₀ rfl).elim, ⟨Set.mem_range_self _, h₀⟩]
  · dsimp
    rw [Set.piecewise_eq_indicator, indicator_preimage_of_notMem,
      measureReal_restrict_apply (f.measurableSet_preimage _)]
    exact fun h₀ => (mem_filter.1 hy).2 (Eq.symm h₀)

/-- Calculate the integral of `g ∘ f : α →ₛ F`, where `f` is an integrable function from `α` to `E`
and `g` is a function from `E` to `F`. We require `g 0 = 0` so that `g ∘ f` is integrable. -/
/-
**MeasureTheory.SimpleFunc.map_integral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.SimpleFunc`。
形式化陈述：map_integral (f : α ->ₛ E) (g : E -> F) (hf : Integrable f μ) (hg : g 0 = 
0) : (f.map g).integral μ = ∑ x in f.range, (μ.real (f ⁻¹' {x})) • g x
参数：f : α ->ₛ E；g : E -> F；hf : Integrable f μ；hg : g 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.map_setToSimpleFunc`：map_setToSimpleFunc (T : S
et α -> F ->L[Real] F') (h_add : FinMeasAdditive μ T) {f : α ->ₛ G} (hf : Integr
able f μ) {g : G -> F} (hg : g 0 =…
· 使用定理 `MeasureTheory.weightedSMul_union`：weightedSMul_union (s t : Set α) (_hs 
: MeasurableSet s) (ht : MeasurableSet t) (hs_finite : μ s != ∞) (ht_finite : μ 
t != ∞) (hdisj : Disjo…

--- 原说明 ---
Calculate the integral of `g ∘ f : α →ₛ F`, where `f` is an integrable function 
from `α` to `E`
and `g` is a function from `E` to `F`. We require `g 0 = 0` so that `g ∘ f` is i
ntegrable.
-/
theorem map_integral (f : α →ₛ E) (g : E → F) (hf : Integrable f μ) (hg : g 0 = 0) :
    (f.map g).integral μ = ∑ x ∈ f.range, (μ.real (f ⁻¹' {x})) • g x :=
  map_setToSimpleFunc _ weightedSMul_union hf hg

/-- `SimpleFunc.integral` and `SimpleFunc.lintegral` agree when the integrand has type
`α →ₛ ℝ≥0∞`. But since `ℝ≥0∞` is not a `NormedSpace`, we need some form of coercion.
See `integral_eq_lintegral` for a simpler version. -/
/-
**MeasureTheory.SimpleFunc.integral_eq_lintegral'** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.SimpleFunc`。
形式化陈述：integral_eq_lintegral' {f : α ->ₛ E} {g : E -> Real>=0∞} (hf : Integrable 
f μ) (hg0 : g 0 = 0) (ht : forall b, g b != ∞) : (f.map (ENNReal.toReal ∘ g)).in
tegral μ = ENNReal.toReal (∫⁻ a, g (f a) ∂μ)
参数：hf : Integrable f μ；hg0 : g 0 = 0；ht : forall b, g b != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.SimpleFunc.integrable_iff_finMeasSupp`：integrable_iff_finM
easSupp {f : α ->ₛ E} : Integrable f μ ↔ f.FinMeasSupp μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_eq_lintegral`：∀ {α : Type u_1} {m : M
easurableSpace α} (f : MeasureTheory.SimpleFunc α ENNReal) (μ : MeasureTheory.Me
asure α),   ∫⁻ (a : α), f a ∂μ = f.li…
· 使用定理 `MeasureTheory.SimpleFunc.map_integral`：map_integral (f : α ->ₛ E) (g : E
 -> F) (hf : Integrable f μ) (hg : g 0 = 0) : (f.map g).integral μ = ∑ x in f.ra
nge, (μ.real (f ⁻¹' {x})) •…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.SimpleFunc.map_lintegral`：map_lintegral (g : β -> Real>=0∞
) (f : α ->ₛ β) : (f.map g).lintegral μ = ∑ x in f.range, g x * μ (f ⁻¹' {x})
· 使用定理 `ENNReal.toReal_sum`：toReal_sum {s : Finset α} {f : α -> Real>=0∞} (hf : 
forall a in s, f a != ∞) : ENNReal.toReal (∑ a in s, f a) = ∑ a in s, ENNReal.to
Real (f …
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `WithTop.zero_ne_top`：∀ {α : Type u} [inst : Zero α], 0 ≠ ⊤
· 使用定理 `ENNReal.mul_ne_top`：mul_ne_top : a != ∞ -> b != ∞ -> a * b != ∞
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.SimpleFunc.FinMeasSupp.meas_preimage_singleton_ne_zero`：me
as_preimage_singleton_ne_zero (h : f.FinMeasSupp μ) {y : β} (hy : y != 0) : μ (f
 ⁻¹' {y}) < ∞
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal

--- 原说明 ---
`SimpleFunc.integral` and `SimpleFunc.lintegral` agree when the integrand has ty
pe
`α →ₛ ℝ≥0∞`. But since `ℝ≥0∞` is not a `NormedSpace`, we need some form of coerc
ion.
See `integral_eq_lintegral` for a simpler version.
-/
theorem integral_eq_lintegral' {f : α →ₛ E} {g : E → ℝ≥0∞} (hf : Integrable f μ) (hg0 : g 0 = 0)
    (ht : ∀ b, g b ≠ ∞) :
    (f.map (ENNReal.toReal ∘ g)).integral μ = ENNReal.toReal (∫⁻ a, g (f a) ∂μ) := by
  have hf' : f.FinMeasSupp μ := integrable_iff_finMeasSupp.1 hf
  simp only [← map_apply g f, lintegral_eq_lintegral]
  rw [map_integral f _ hf, map_lintegral, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_eq_mul, toReal_mul, mul_comm, Function.comp_apply, measureReal_def]
  · rintro a -
    by_cases a0 : a = 0
    · rw [a0, hg0, zero_mul]; exact WithTop.zero_ne_top
    · apply mul_ne_top (ht a) (hf'.meas_preimage_singleton_ne_zero a0).ne
  · simp [hg0]

variable [NormedSpace ℝ E]
/-
**MeasureTheory.SimpleFunc.integral_congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.SimpleFunc`。
形式化陈述：integral_congr {f g : α ->ₛ E} (hf : Integrable f μ) (h : f =ᵐ[μ] g) : f.i
ntegral μ = g.integral μ
参数：hf : Integrable f μ；h : f =ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_congr`：setToSimpleFunc_congr (T
 : Set α -> E ->L[Real] F) (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s
 = 0) (h_add : FinMeasAdditive μ T) …
· 使用定理 `MeasureTheory.weightedSMul_null`：weightedSMul_null {s : Set α} (h_zero :
 μ s = 0) : (weightedSMul μ s : F ->L[Real] F) = 0
· 使用定理 `MeasureTheory.weightedSMul_union`：weightedSMul_union (s t : Set α) (_hs 
: MeasurableSet s) (ht : MeasurableSet t) (hs_finite : μ s != ∞) (ht_finite : μ 
t != ∞) (hdisj : Disjo…
-/
theorem integral_congr {f g : α →ₛ E} (hf : Integrable f μ) (h : f =ᵐ[μ] g) :
    f.integral μ = g.integral μ :=
  setToSimpleFunc_congr (weightedSMul μ) (fun _ _ => weightedSMul_null) weightedSMul_union hf h

/-- `SimpleFunc.integral` and `SimpleFunc.lintegral` agree when the integrand has type
`α →ₛ ℝ≥0∞`. But since `ℝ≥0∞` is not a `NormedSpace`, we need some form of coercion. -/
/-
**MeasureTheory.SimpleFunc.integral_eq_lintegral** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.SimpleFunc`。
形式化陈述：integral_eq_lintegral {f : α ->ₛ Real} (hf : Integrable f μ) (h_pos : 0 <=
ᵐ[μ] f) : f.integral μ = ENNReal.toReal (∫⁻ a, ENNReal.ofReal (f a) ∂μ)
参数：hf : Integrable f μ；h_pos : 0 <=ᵐ[μ] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.integral_eq_lintegral'`：integral_eq_lintegral' 
{f : α ->ₛ E} {g : E -> Real>=0∞} (hf : Integrable f μ) (hg0 : g 0 = 0) (ht : fo
rall b, g b != ∞) : (f.map (ENNReal.t…
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `ENNReal.ofReal_ne_top`：ofReal_ne_top {r : Real} : ENNReal.ofReal r != ∞
· 使用定理 `MeasureTheory.SimpleFunc.integral_congr`：integral_congr {f g : α ->ₛ E} 
(hf : Integrable f μ) (h : f =ᵐ[μ] g) : f.integral μ = g.integral μ

--- 原说明 ---
`SimpleFunc.integral` and `SimpleFunc.lintegral` agree when the integrand has ty
pe
`α →ₛ ℝ≥0∞`. But since `ℝ≥0∞` is not a `NormedSpace`, we need some form of coerc
ion.
-/
theorem integral_eq_lintegral {f : α →ₛ ℝ} (hf : Integrable f μ) (h_pos : 0 ≤ᵐ[μ] f) :
    f.integral μ = ENNReal.toReal (∫⁻ a, ENNReal.ofReal (f a) ∂μ) := by
  have : f =ᵐ[μ] f.map (ENNReal.toReal ∘ ENNReal.ofReal) :=
    h_pos.mono fun a h => (ENNReal.toReal_ofReal h).symm
  rw [← integral_eq_lintegral' hf]
  exacts [integral_congr hf this, ENNReal.ofReal_zero, fun b => ENNReal.ofReal_ne_top]
/-
**MeasureTheory.SimpleFunc.integral_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.SimpleFunc`。
形式化陈述：integral_add {f g : α ->ₛ E} (hf : Integrable f μ) (hg : Integrable g μ) :
 integral μ (f + g) = integral μ f + integral μ g
参数：hf : Integrable f μ；hg : Integrable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_add`：setToSimpleFunc_add (T : S
et α -> E ->L[Real] F) (h_add : FinMeasAdditive μ T) {f g : α ->ₛ E} (hf : Integ
rable f μ) (hg : Integrable g μ) :…
· 使用定理 `MeasureTheory.weightedSMul_union`：weightedSMul_union (s t : Set α) (_hs 
: MeasurableSet s) (ht : MeasurableSet t) (hs_finite : μ s != ∞) (ht_finite : μ 
t != ∞) (hdisj : Disjo…
-/
theorem integral_add {f g : α →ₛ E} (hf : Integrable f μ) (hg : Integrable g μ) :
    integral μ (f + g) = integral μ f + integral μ g :=
  setToSimpleFunc_add _ weightedSMul_union hf hg
/-
**MeasureTheory.SimpleFunc.integral_neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.SimpleFunc`。
形式化陈述：integral_neg {f : α ->ₛ E} (hf : Integrable f μ) : integral μ (-f) = -inte
gral μ f
参数：hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_neg`：setToSimpleFunc_neg (T : S
et α -> E ->L[Real] F) (h_add : FinMeasAdditive μ T) {f : α ->ₛ E} (hf : Integra
ble f μ) : setToSimpleFunc T (-f) …
· 使用定理 `MeasureTheory.weightedSMul_union`：weightedSMul_union (s t : Set α) (_hs 
: MeasurableSet s) (ht : MeasurableSet t) (hs_finite : μ s != ∞) (ht_finite : μ 
t != ∞) (hdisj : Disjo…
-/
theorem integral_neg {f : α →ₛ E} (hf : Integrable f μ) : integral μ (-f) = -integral μ f :=
  setToSimpleFunc_neg _ weightedSMul_union hf
/-
**MeasureTheory.SimpleFunc.integral_sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.SimpleFunc`。
形式化陈述：integral_sub {f g : α ->ₛ E} (hf : Integrable f μ) (hg : Integrable g μ) :
 integral μ (f - g) = integral μ f - integral μ g
参数：hf : Integrable f μ；hg : Integrable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_sub`：setToSimpleFunc_sub (T : S
et α -> E ->L[Real] F) (h_add : FinMeasAdditive μ T) {f g : α ->ₛ E} (hf : Integ
rable f μ) (hg : Integrable g μ) :…
· 使用定理 `MeasureTheory.weightedSMul_union`：weightedSMul_union (s t : Set α) (_hs 
: MeasurableSet s) (ht : MeasurableSet t) (hs_finite : μ s != ∞) (ht_finite : μ 
t != ∞) (hdisj : Disjo…
-/
theorem integral_sub {f g : α →ₛ E} (hf : Integrable f μ) (hg : Integrable g μ) :
    integral μ (f - g) = integral μ f - integral μ g :=
  setToSimpleFunc_sub _ weightedSMul_union hf hg
/-
**MeasureTheory.SimpleFunc.integral_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.SimpleFunc`。
形式化陈述：integral_smul [DistribSMul 𝕜 E] [SMulCommClass Real 𝕜 E] (c : 𝕜) {f : α ->
ₛ E} (hf : Integrable f μ) : integral μ (c • f) = c • integral μ f
参数：c : 𝕜；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_smul`：setToSimpleFunc_smul {E} 
[NormedAddCommGroup E] [SMulZeroClass 𝕜 E] [NormedSpace Real E] [DistribSMul 𝕜 F
] (T : Set α -> E ->L[Real] F) (h_a…
· 使用定理 `MeasureTheory.weightedSMul_union`：weightedSMul_union (s t : Set α) (_hs 
: MeasurableSet s) (ht : MeasurableSet t) (hs_finite : μ s != ∞) (ht_finite : μ 
t != ∞) (hdisj : Disjo…
· 使用定理 `MeasureTheory.weightedSMul_smul`：weightedSMul_smul [SMul 𝕜 F] [SMulCommC
lass Real 𝕜 F] (c : 𝕜) (s : Set α) (x : F) : weightedSMul μ s (c • x) = c • weig
htedSMul μ s x
-/
theorem integral_smul [DistribSMul 𝕜 E] [SMulCommClass ℝ 𝕜 E]
    (c : 𝕜) {f : α →ₛ E} (hf : Integrable f μ) :
    integral μ (c • f) = c • integral μ f :=
  setToSimpleFunc_smul _ weightedSMul_union weightedSMul_smul c hf
/-
**MeasureTheory.SimpleFunc.norm_setToSimpleFunc_le_integral_norm** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.SimpleFunc`。
形式化陈述：norm_setToSimpleFunc_le_integral_norm (T : Set α -> E ->L[Real] F) {C : Re
al} (hT_norm : forall s, MeasurableSet s -> μ s < ∞ -> ‖T s‖ <= C * μ.real s) {f
 : α ->ₛ E} (hf : Integrable f μ) : ‖f.setToSimpleFunc T‖ <= C * (f.map norm).in
tegral μ
参数：T : Set α -> E ->L[Real] F；hT_norm : forall s, MeasurableSet s -> μ s < ∞ -> 
‖T s‖ <= C * μ.real s；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.norm_setToSimpleFunc_le_sum_mul_norm_of_integra
ble`：norm_setToSimpleFunc_le_sum_mul_norm_of_integrable (T : Set α -> E ->L[Real
] F') {C : Real} (hT_norm : forall s, MeasurableSet s -> μ s < ∞ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.map_integral`：map_integral (f : α ->ₛ E) (g : E
 -> F) (hf : Integrable f μ) (hg : g 0 = 0) : (f.map g).integral μ = ∑ x in f.ra
nge, (μ.real (f ⁻¹' {x})) •…
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_setToSimpleFunc_le_integral_norm (T : Set α → E →L[ℝ] F) {C : ℝ}
    (hT_norm : ∀ s, MeasurableSet s → μ s < ∞ → ‖T s‖ ≤ C * μ.real s) {f : α →ₛ E}
    (hf : Integrable f μ) : ‖f.setToSimpleFunc T‖ ≤ C * (f.map norm).integral μ :=
  calc
    ‖f.setToSimpleFunc T‖ ≤ C * ∑ x ∈ f.range, μ.real (f ⁻¹' {x}) * ‖x‖ :=
      norm_setToSimpleFunc_le_sum_mul_norm_of_integrable T hT_norm f hf
    _ = C * (f.map norm).integral μ := by
      rw [map_integral f norm hf norm_zero]; simp_rw [smul_eq_mul]
/-
**MeasureTheory.SimpleFunc.norm_integral_le_integral_norm** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.SimpleFunc`。
形式化陈述：norm_integral_le_integral_norm (f : α ->ₛ E) (hf : Integrable f μ) : ‖f.in
tegral μ‖ <= (f.map norm).integral μ
参数：f : α ->ₛ E；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.SimpleFunc.norm_setToSimpleFunc_le_integral_norm`：norm_set
ToSimpleFunc_le_integral_norm (T : Set α -> E ->L[Real] F) {C : Real} (hT_norm :
 forall s, MeasurableSet s -> μ s < ∞ -> ‖T s‖ <= C …
· 使用定理 `MeasureTheory.norm_weightedSMul_le`：norm_weightedSMul_le (s : Set α) : ‖
(weightedSMul μ s : F ->L[Real] F)‖ <= μ.real s
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem norm_integral_le_integral_norm (f : α →ₛ E) (hf : Integrable f μ) :
    ‖f.integral μ‖ ≤ (f.map norm).integral μ := by
  refine (norm_setToSimpleFunc_le_integral_norm _ (fun s _ _ => ?_) hf).trans (one_mul _).le
  exact (norm_weightedSMul_le s).trans (one_mul _).symm.le
/-
**MeasureTheory.SimpleFunc.integral_add_measure** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.SimpleFunc`。
形式化陈述：integral_add_measure {ν} (f : α ->ₛ E) (hf : Integrable f (μ + ν)) : f.int
egral (μ + ν) = f.integral μ + f.integral ν
参数：f : α ->ₛ E；hf : Integrable f (μ + ν)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_add_left'`：setToSimpleFunc_add_
left' (T T' T'' : Set α -> E ->L[Real] F) (h_add : forall s, MeasurableSet s -> 
μ s < ∞ -> T'' s = T s + T' s) {f : α ->…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.weightedSMul_add_measure`：weightedSMul_add_measure {m : Me
asurableSpace α} (μ ν : Measure α) {s : Set α} (hμs : μ s != ∞) (hνs : ν s != ∞)
 : (weightedSMul (μ + ν) s :…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ENNReal.add_ne_top`：add_ne_top : a + b != ∞ ↔ a != ∞ ∧ b != ∞
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `MeasureTheory.Measure.coe_add`：coe_add {_m : MeasurableSpace α} (μ₁ μ₂ :
 Measure α) : ⇑(μ₁ + μ₂) = μ₁ + μ₂
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem integral_add_measure {ν} (f : α →ₛ E) (hf : Integrable f (μ + ν)) :
    f.integral (μ + ν) = f.integral μ + f.integral ν := by
  simp_rw [integral_def]
  refine setToSimpleFunc_add_left'
    (weightedSMul μ) (weightedSMul ν) (weightedSMul (μ + ν)) (fun s _ hμνs => ?_) hf
  rw [lt_top_iff_ne_top, Measure.coe_add, Pi.add_apply, ENNReal.add_ne_top] at hμνs
  rw [weightedSMul_add_measure _ _ hμνs.1 hμνs.2]

section Order

variable [PartialOrder F] [IsOrderedAddMonoid F] [IsOrderedModule ℝ F]

/-
**MeasureTheory.SimpleFunc.integral_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory.SimpleFunc`。
形式化陈述：integral_nonneg {f : α ->ₛ F} (hf : 0 <=ᵐ[μ] f) : 0 <= f.integral μ
参数：hf : 0 <=ᵐ[μ] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.integral_eq`：integral_eq {m : MeasurableSpace α
} (μ : Measure α) (f : α ->ₛ F) : f.integral μ = ∑ x in f.range, μ.real (f ⁻¹' {
x}) • x
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.SimpleFunc.forall_mem_range`：forall_mem_range {f : α ->ₛ β
} {p : β -> Prop} : (forall y in f.range, p y) ↔ forall x, p (f x)
· 使用引理 `smul_nonneg`：smul_nonneg [PosSMulMono α β] (ha : 0 <= a) (hb : 0 <= b₁) 
: 0 <= a • b₁
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `MeasureTheory.measureReal_nonneg`：∀ {α : Type u_1} {x : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α}, 0 ≤ μ.real s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `le_of_le_of_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.ae_iff`：ae_iff {p : α -> Prop} : (forallᵐ a ∂μ, p a) ↔ μ {
 a | ¬p a } = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
lemma integral_nonneg {f : α →ₛ F} (hf : 0 ≤ᵐ[μ] f) :
    0 ≤ f.integral μ := by
  rw [integral_eq]
  apply Finset.sum_nonneg
  rw [forall_mem_range]
  intro y
  by_cases hy : 0 ≤ f y
  · positivity
  · suffices μ (f ⁻¹' {f y}) = 0 by simp [this, measureReal_def]
    rw [← nonpos_iff_eq_zero]
    refine le_of_le_of_eq (measure_mono fun x hx ↦ ?_) (ae_iff.mp hf)
    simp only [Set.mem_preimage, mem_singleton_iff, mem_ofPred_eq] at hx ⊢
    exact hx ▸ hy
/-
**MeasureTheory.SimpleFunc.integral_mono** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y.SimpleFunc`。
形式化陈述：integral_mono {f g : α ->ₛ F} (h : f <=ᵐ[μ] g) (hf : Integrable f μ) (hg :
 Integrable g μ) : f.integral μ <= g.integral μ
参数：h : f <=ᵐ[μ] g；hf : Integrable f μ；hg : Integrable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.SimpleFunc.integral_sub`：integral_sub {f g : α ->ₛ E} (hf 
: Integrable f μ) (hg : Integrable g μ) : integral μ (f - g) = integral μ f - in
tegral μ g
· 使用引理 `MeasureTheory.SimpleFunc.integral_nonneg`：integral_nonneg {f : α ->ₛ F} 
(hf : 0 <=ᵐ[μ] f) : 0 <= f.integral μ
· 使用定理 `MeasureTheory.sub_nonneg_ae`：∀ {α : Type u_2} {m0 : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {β : Type u_7} [inst : AddGroup β]   [inst_1 : LE β
] [AddRightMono β…
-/
lemma integral_mono {f g : α →ₛ F} (h : f ≤ᵐ[μ] g) (hf : Integrable f μ) (hg : Integrable g μ) :
    f.integral μ ≤ g.integral μ := by
  rw [← sub_nonneg, ← integral_sub hg hf]
  rw [← sub_nonneg_ae] at h
  exact integral_nonneg h
/-
**MeasureTheory.SimpleFunc.integral_mono_measure** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory.SimpleFunc`。
形式化陈述：integral_mono_measure {ν} {f : α ->ₛ F} (hf : 0 <=ᵐ[ν] f) (hμν : μ <= ν) (
hfν : Integrable f ν) : f.integral μ <= f.integral ν
参数：hf : 0 <=ᵐ[ν] f；hμν : μ <= ν；hfν : Integrable f ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.integral_eq`：integral_eq {m : MeasurableSpace α
} (μ : Measure α) (f : α ->ₛ F) : f.integral μ = ∑ x in f.range, μ.real (f ⁻¹' {
x}) • x
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α
} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_
3 : Zero β] [SMulP…
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.SimpleFunc.integrable_iff`：integrable_iff {f : α ->ₛ E} : 
Integrable f μ ↔ forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `MeasureTheory.Measure.measure_mono_left`：∀ {α : Type u_1} {m0 : Measurab
leSpace α} {μ ν : MeasureTheory.Measure α}, μ ≤ ν → ∀ (s : Set α), μ s ≤ ν s
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.ae_iff`：ae_iff {p : α -> Prop} : (forallᵐ a ∂μ, p a) ↔ μ {
 a | ¬p a } = 0
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
lemma integral_mono_measure {ν} {f : α →ₛ F} (hf : 0 ≤ᵐ[ν] f) (hμν : μ ≤ ν) (hfν : Integrable f ν) :
    f.integral μ ≤ f.integral ν := by
  simp only [integral_eq]
  apply Finset.sum_le_sum
  simp only [forall_mem_range]
  intro x
  by_cases hx : 0 ≤ f x
  · obtain (hx | hx) := hx.eq_or_lt
    · simp [← hx]
    simp only [measureReal_def]
    gcongr
    exact integrable_iff.mp hfν (f x) hx.ne' |>.ne
  · suffices ν (f ⁻¹' {f x}) = 0 by
      have A : μ (f ⁻¹' {f x}) = 0 := by simpa using (hμν _ |>.trans_eq this)
      simp [measureReal_def, A, this]
    rw [← nonpos_iff_eq_zero, ← ae_iff.mp hf]
    refine measure_mono fun y hy ↦ ?_
    simp_all

end Order

end Integral

end SimpleFunc

namespace L1

open AEEqFun Lp.simpleFunc Lp

variable [NormedAddCommGroup E] {m : MeasurableSpace α} {μ : Measure α}

namespace SimpleFunc

/-
**MeasureTheory.L1.SimpleFunc.norm_eq_integral** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.L1.SimpleFunc`。
形式化陈述：norm_eq_integral (f : α ->₁ₛ[μ] E) : ‖f‖ = ((toSimpleFunc f).map norm).int
egral μ
参数：f : α ->₁ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L1.SimpleFunc.norm_eq_sum_mul`：norm_eq_sum_mul (f : α ->₁ₛ
[μ] G) : ‖f‖ = ∑ x in (toSimpleFunc f).range, μ.real (toSimpleFunc f ⁻¹' {x}) * 
‖x‖
· 使用定理 `MeasureTheory.SimpleFunc.map_integral`：map_integral (f : α ->ₛ E) (g : E
 -> F) (hf : Integrable f μ) (hg : g 0 = 0) : (f.map g).integral μ = ∑ x in f.ra
nge, (μ.real (f ⁻¹' {x})) •…
· 使用定理 `MeasureTheory.L1.SimpleFunc.integrable`：∀ {α : Type u_1} {E : Type u_4} 
[inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {μ : MeasureTheory.Me
asure α}   (f : ↥(α →₁ₛ[μ] E…
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_eq_integral (f : α →₁ₛ[μ] E) : ‖f‖ = ((toSimpleFunc f).map norm).integral μ := by
  rw [norm_eq_sum_mul f, (toSimpleFunc f).map_integral norm (SimpleFunc.integrable f) norm_zero]
  simp_rw [smul_eq_mul]

section PosPart

/-- Positive part of a simple function in L1 space. -/
nonrec def posPart (f : α →₁ₛ[μ] ℝ) : α →₁ₛ[μ] ℝ :=
  ⟨Lp.posPart (f : α →₁[μ] ℝ), by
    rcases f with ⟨f, s, hsf⟩
    use s.posPart
    simp only [SimpleFunc.posPart, SimpleFunc.coe_map, Function.comp_def, coe_posPart, ← hsf,
      posPart_mk] ⟩

/-- Negative part of a simple function in L1 space. -/
/-
**MeasureTheory.L1.SimpleFunc.negPart** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.L
1.SimpleFunc`。
形式化陈述：negPart (f : α ->₁ₛ[μ] Real) : α ->₁ₛ[μ] Real
参数：f : α ->₁ₛ[μ] Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Negative part of a simple function in L1 space.
-/
def negPart (f : α →₁ₛ[μ] ℝ) : α →₁ₛ[μ] ℝ :=
  posPart (-f)

@[norm_cast]
/-
**MeasureTheory.L1.SimpleFunc.coe_posPart** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.L1.SimpleFunc`。
形式化陈述：coe_posPart (f : α ->₁ₛ[μ] Real) : (posPart f : α ->₁[μ] Real) = Lp.posPar
t (f : α ->₁[μ] Real)
参数：f : α ->₁ₛ[μ] Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem coe_posPart (f : α →₁ₛ[μ] ℝ) : (posPart f : α →₁[μ] ℝ) = Lp.posPart (f : α →₁[μ] ℝ) := rfl

@[norm_cast]
/-
**MeasureTheory.L1.SimpleFunc.coe_negPart** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.L1.SimpleFunc`。
形式化陈述：coe_negPart (f : α ->₁ₛ[μ] Real) : (negPart f : α ->₁[μ] Real) = Lp.negPar
t (f : α ->₁[μ] Real)
参数：f : α ->₁ₛ[μ] Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem coe_negPart (f : α →₁ₛ[μ] ℝ) : (negPart f : α →₁[μ] ℝ) = Lp.negPart (f : α →₁[μ] ℝ) := rfl

end PosPart

section SimpleFuncIntegral

/-!
### The Bochner integral of `L1`

Define the Bochner integral on `α →₁ₛ[μ] E` by extension from the simple functions `α →₁ₛ[μ] E`,
and prove basic properties of this integral. -/

variable [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [NormedSpace ℝ E] [SMulCommClass ℝ 𝕜 E]

attribute [local instance] simpleFunc.isBoundedSMul simpleFunc.module simpleFunc.normedSpace

/-- The Bochner integral over simple functions in L1 space. -/
/-
**MeasureTheory.L1.SimpleFunc.integral** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.
L1.SimpleFunc`。
形式化陈述：integral (f : α ->₁ₛ[μ] E) : E
参数：f : α ->₁ₛ[μ] E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Bochner integral over simple functions in L1 space.
-/
def integral (f : α →₁ₛ[μ] E) : E :=
  (toSimpleFunc f).integral μ
/-
**MeasureTheory.L1.SimpleFunc.integral_eq_integral** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.L1.SimpleFunc`。
形式化陈述：integral_eq_integral (f : α ->₁ₛ[μ] E) : integral f = (toSimpleFunc f).int
egral μ
参数：f : α ->₁ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem integral_eq_integral (f : α →₁ₛ[μ] E) : integral f = (toSimpleFunc f).integral μ := rfl

nonrec theorem integral_eq_lintegral {f : α →₁ₛ[μ] ℝ} (h_pos : 0 ≤ᵐ[μ] toSimpleFunc f) :
    integral f = ENNReal.toReal (∫⁻ a, ENNReal.ofReal ((toSimpleFunc f) a) ∂μ) := by
  rw [integral, SimpleFunc.integral_eq_lintegral (SimpleFunc.integrable f) h_pos]
/-
**MeasureTheory.L1.SimpleFunc.integral_eq_setToL1S** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.L1.SimpleFunc`。
形式化陈述：integral_eq_setToL1S (f : α ->₁ₛ[μ] E) : integral f = setToL1S (weightedSM
ul μ) f
参数：f : α ->₁ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem integral_eq_setToL1S (f : α →₁ₛ[μ] E) : integral f = setToL1S (weightedSMul μ) f := rfl

nonrec theorem integral_congr {f g : α →₁ₛ[μ] E} (h : toSimpleFunc f =ᵐ[μ] toSimpleFunc g) :
    integral f = integral g :=
  SimpleFunc.integral_congr (SimpleFunc.integrable f) h
/-
**MeasureTheory.L1.SimpleFunc.integral_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.L1.SimpleFunc`。
形式化陈述：integral_add (f g : α ->₁ₛ[μ] E) : integral (f + g) = integral f + integra
l g
参数：f g : α ->₁ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.L1.SimpleFunc.setToL1S_add`：setToL1S_add (T : Set α -> E -
>L[Real] F) (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s = 0) (h_add : 
FinMeasAdditive μ T) (f g : α …
· 使用定理 `MeasureTheory.weightedSMul_null`：weightedSMul_null {s : Set α} (h_zero :
 μ s = 0) : (weightedSMul μ s : F ->L[Real] F) = 0
· 使用定理 `MeasureTheory.weightedSMul_union`：weightedSMul_union (s t : Set α) (_hs 
: MeasurableSet s) (ht : MeasurableSet t) (hs_finite : μ s != ∞) (ht_finite : μ 
t != ∞) (hdisj : Disjo…
-/
theorem integral_add (f g : α →₁ₛ[μ] E) : integral (f + g) = integral f + integral g :=
  setToL1S_add _ (fun _ _ => weightedSMul_null) weightedSMul_union _ _
/-
**MeasureTheory.L1.SimpleFunc.integral_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.L1.SimpleFunc`。
形式化陈述：integral_smul (c : 𝕜) (f : α ->₁ₛ[μ] E) : integral (c • f) = c • integral 
f
参数：c : 𝕜；f : α ->₁ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.L1.SimpleFunc.setToL1S_smul`：setToL1S_smul [DistribSMul 𝕜 
F] (T : Set α -> E ->L[Real] F) (h_zero : forall s, MeasurableSet s -> μ s = 0 -
> T s = 0) (h_add : FinMeasAddi…
· 使用定理 `MeasureTheory.weightedSMul_null`：weightedSMul_null {s : Set α} (h_zero :
 μ s = 0) : (weightedSMul μ s : F ->L[Real] F) = 0
· 使用定理 `MeasureTheory.weightedSMul_union`：weightedSMul_union (s t : Set α) (_hs 
: MeasurableSet s) (ht : MeasurableSet t) (hs_finite : μ s != ∞) (ht_finite : μ 
t != ∞) (hdisj : Disjo…
· 使用定理 `MeasureTheory.weightedSMul_smul`：weightedSMul_smul [SMul 𝕜 F] [SMulCommC
lass Real 𝕜 F] (c : 𝕜) (s : Set α) (x : F) : weightedSMul μ s (c • x) = c • weig
htedSMul μ s x
-/
theorem integral_smul (c : 𝕜) (f : α →₁ₛ[μ] E) : integral (c • f) = c • integral f :=
  setToL1S_smul _ (fun _ _ => weightedSMul_null) weightedSMul_union weightedSMul_smul c f
/-
**MeasureTheory.L1.SimpleFunc.norm_integral_le_norm** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.L1.SimpleFunc`。
形式化陈述：norm_integral_le_norm (f : α ->₁ₛ[μ] E) : ‖integral f‖ <= ‖f‖
参数：f : α ->₁ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L1.SimpleFunc.integral.eq_1`：∀ {α : Type u_1} {E : Type u_
2} [inst : NormedAddCommGroup E] {m : MeasurableSpace α} {μ : MeasureTheory.Meas
ure α}   [inst_1 : NormedSpace …
· 使用定理 `MeasureTheory.L1.SimpleFunc.norm_eq_integral`：norm_eq_integral (f : α ->
₁ₛ[μ] E) : ‖f‖ = ((toSimpleFunc f).map norm).integral μ
· 使用定理 `MeasureTheory.SimpleFunc.norm_integral_le_integral_norm`：norm_integral_l
e_integral_norm (f : α ->ₛ E) (hf : Integrable f μ) : ‖f.integral μ‖ <= (f.map n
orm).integral μ
· 使用定理 `MeasureTheory.L1.SimpleFunc.integrable`：∀ {α : Type u_1} {E : Type u_4} 
[inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {μ : MeasureTheory.Me
asure α}   (f : ↥(α →₁ₛ[μ] E…
-/
theorem norm_integral_le_norm (f : α →₁ₛ[μ] E) : ‖integral f‖ ≤ ‖f‖ := by
  rw [integral, norm_eq_integral]
  exact (toSimpleFunc f).norm_integral_le_integral_norm (SimpleFunc.integrable f)

variable (α E μ 𝕜)

/-- The Bochner integral over simple functions in L1 space as a continuous linear map. -/
/-
**MeasureTheory.L1.SimpleFunc.integralCLM'** 是 Mathlib 中的一个定义，位于命名空间 `MeasureThe
ory.L1.SimpleFunc`。
形式化陈述：integralCLM' : (α ->₁ₛ[μ] E) ->L[𝕜] E
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.L1.SimpleFunc.integral_add`：integral_add (f g : α ->₁ₛ[μ] 
E) : integral (f + g) = integral f + integral g
· 使用定理 `MeasureTheory.L1.SimpleFunc.integral_smul`：integral_smul (c : 𝕜) (f : α 
->₁ₛ[μ] E) : integral (c • f) = c • integral f

--- 原说明 ---
The Bochner integral over simple functions in L1 space as a continuous linear ma
p.
-/
def integralCLM' : (α →₁ₛ[μ] E) →L[𝕜] E :=
  LinearMap.mkContinuous ⟨⟨integral, integral_add⟩, integral_smul⟩ 1 fun f =>
    le_trans (norm_integral_le_norm _) <| by rw [one_mul]

/-- The Bochner integral over simple functions in L1 space as a continuous linear map over ℝ. -/
/-
**MeasureTheory.L1.SimpleFunc.integralCLM** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheo
ry.L1.SimpleFunc`。
形式化陈述：integralCLM : (α ->₁ₛ[μ] E) ->L[Real] E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Bochner integral over simple functions in L1 space as a continuous linear ma
p over ℝ.
-/
def integralCLM : (α →₁ₛ[μ] E) →L[ℝ] E :=
  integralCLM' α E ℝ μ

variable {α E μ 𝕜}

local notation "Integral" => integralCLM α E μ

open ContinuousLinearMap
/-
**MeasureTheory.L1.SimpleFunc.norm_Integral_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.L1.SimpleFunc`。
形式化陈述：norm_Integral_le_one : ‖Integral‖ <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.mkContinuous_norm_le`：mkContinuous_norm_le (f : E ->ₛₗ[σ₁₂] F)
 {C : Real} (hC : 0 <= C) (h : forall x, ‖f x‖ <= C * ‖x‖) : ‖f.mkContinuous C h
‖ <= C
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.L1.SimpleFunc.integral_add`：integral_add (f g : α ->₁ₛ[μ] 
E) : integral (f + g) = integral f + integral g
· 使用定理 `MeasureTheory.L1.SimpleFunc.integral_smul`：integral_smul (c : 𝕜) (f : α 
->₁ₛ[μ] E) : integral (c • f) = c • integral f
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MeasureTheory.L1.SimpleFunc.norm_integral_le_norm`：norm_integral_le_norm
 (f : α ->₁ₛ[μ] E) : ‖integral f‖ <= ‖f‖
-/
theorem norm_Integral_le_one : ‖Integral‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one fun f ↦ by
    simpa [one_mul] using norm_integral_le_norm f

section PosPart

/-
**MeasureTheory.L1.SimpleFunc.posPart_toSimpleFunc** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.L1.SimpleFunc`。
形式化陈述：posPart_toSimpleFunc (f : α ->₁ₛ[μ] Real) : toSimpleFunc (posPart f) =ᵐ[μ]
 (toSimpleFunc f).posPart
参数：f : α ->₁ₛ[μ] Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Lp.simpleFunc.toSimpleFunc_eq_toFun`：toSimpleFunc_eq_toFun
 (f : Lp.simpleFunc E p μ) : toSimpleFunc f =ᵐ[μ] f
· 使用定理 `MeasureTheory.Lp.coeFn_posPart`：coeFn_posPart (f : Lp Real p μ) : ⇑(posP
art f) =ᵐ[μ] fun a => max (f a) 0
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
-/
theorem posPart_toSimpleFunc (f : α →₁ₛ[μ] ℝ) :
    toSimpleFunc (posPart f) =ᵐ[μ] (toSimpleFunc f).posPart := by
  have eq : ∀ a, (toSimpleFunc f).posPart a = max ((toSimpleFunc f) a) 0 := fun a => rfl
  have ae_eq : ∀ᵐ a ∂μ, toSimpleFunc (posPart f) a = max ((toSimpleFunc f) a) 0 := by
    filter_upwards [toSimpleFunc_eq_toFun (posPart f), Lp.coeFn_posPart (f : α →₁[μ] ℝ),
      toSimpleFunc_eq_toFun f] with _ _ h₂ h₃
    convert! h₂ using 1
    rw [h₃]
  refine ae_eq.mono fun a h => ?_
  rw [h, eq]
/-
**MeasureTheory.L1.SimpleFunc.negPart_toSimpleFunc** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.L1.SimpleFunc`。
形式化陈述：negPart_toSimpleFunc (f : α ->₁ₛ[μ] Real) : toSimpleFunc (negPart f) =ᵐ[μ]
 (toSimpleFunc f).negPart
参数：f : α ->₁ₛ[μ] Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L1.SimpleFunc.negPart.eq_1`：∀ {α : Type u_1} {m : Measurab
leSpace α} {μ : MeasureTheory.Measure α} (f : ↥(α →₁ₛ[μ] ℝ)),   MeasureTheory.L1
.SimpleFunc.negPart f = Measur…
· 使用定理 `MeasureTheory.SimpleFunc.negPart.eq_1`：∀ {α : Type u_1} {E : Type u_2} [
inst : LinearOrder E] [inst_1 : Zero E] [inst_2 : MeasurableSpace α] [inst_3 : N
eg E]   (f : MeasureTheory.…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Lp.simpleFunc.neg_toSimpleFunc`：neg_toSimpleFunc (f : Lp.s
impleFunc E p μ) : toSimpleFunc (-f) =ᵐ[μ] -toSimpleFunc f
· 使用定理 `MeasureTheory.L1.SimpleFunc.posPart_toSimpleFunc`：posPart_toSimpleFunc (
f : α ->₁ₛ[μ] Real) : toSimpleFunc (posPart f) =ᵐ[μ] (toSimpleFunc f).posPart
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem negPart_toSimpleFunc (f : α →₁ₛ[μ] ℝ) :
    toSimpleFunc (negPart f) =ᵐ[μ] (toSimpleFunc f).negPart := by
  rw [SimpleFunc.negPart, MeasureTheory.SimpleFunc.negPart]
  filter_upwards [posPart_toSimpleFunc (-f), neg_toSimpleFunc f]
  intro a h₁ h₂
  rw [h₁]
  change max _ _ = max _ _
  rw [h₂]
  simp
/-
**MeasureTheory.L1.SimpleFunc.integral_eq_norm_posPart_sub** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.L1.SimpleFunc`。
形式化陈述：integral_eq_norm_posPart_sub (f : α ->₁ₛ[μ] Real) : integral f = ‖posPart 
f‖ - ‖negPart f‖
参数：f : α ->₁ₛ[μ] Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.L1.SimpleFunc.posPart_toSimpleFunc`：posPart_toSimpleFunc (
f : α ->₁ₛ[μ] Real) : toSimpleFunc (posPart f) =ᵐ[μ] (toSimpleFunc f).posPart
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.map_apply`：map_apply (g : β -> γ) (f : α ->ₛ β)
 (a) : f.map g a = g (f a)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SimpleFunc.posPart_map_norm`：posPart_map_norm (f : α ->ₛ R
eal) : (posPart f).map norm = posPart f
· 使用定理 `MeasureTheory.L1.SimpleFunc.negPart_toSimpleFunc`：negPart_toSimpleFunc (
f : α ->₁ₛ[μ] Real) : toSimpleFunc (negPart f) =ᵐ[μ] (toSimpleFunc f).negPart
· 使用定理 `MeasureTheory.SimpleFunc.negPart_map_norm`：negPart_map_norm (f : α ->ₛ R
eal) : (negPart f).map norm = negPart f
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.L1.SimpleFunc.integral.eq_1`：∀ {α : Type u_1} {E : Type u_
2} [inst : NormedAddCommGroup E] {m : MeasurableSpace α} {μ : MeasureTheory.Meas
ure α}   [inst_1 : NormedSpace …
· 使用定理 `MeasureTheory.L1.SimpleFunc.norm_eq_integral`：norm_eq_integral (f : α ->
₁ₛ[μ] E) : ‖f‖ = ((toSimpleFunc f).map norm).integral μ
· 使用定理 `MeasureTheory.SimpleFunc.integral_sub`：integral_sub {f g : α ->ₛ E} (hf 
: Integrable f μ) (hg : Integrable g μ) : integral μ (f - g) = integral μ f - in
tegral μ g
· 使用定理 `MeasureTheory.Integrable.congr`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
· 使用定理 `MeasureTheory.Integrable.pos_part`：∀ {α : Type u_1} {m : MeasurableSpace
 α} {μ : MeasureTheory.Measure α} {f : α → ℝ},   MeasureTheory.Integrable f μ → 
MeasureTheory.Integrabl…
· 使用定理 `MeasureTheory.L1.SimpleFunc.integrable`：∀ {α : Type u_1} {E : Type u_4} 
[inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {μ : MeasureTheory.Me
asure α}   (f : ↥(α →₁ₛ[μ] E…
· 使用定理 `MeasureTheory.Integrable.neg_part`：∀ {α : Type u_1} {m : MeasurableSpace
 α} {μ : MeasureTheory.Measure α} {f : α → ℝ},   MeasureTheory.Integrable f μ → 
MeasureTheory.Integrabl…
· 使用定理 `MeasureTheory.SimpleFunc.integral_congr`：integral_congr {f g : α ->ₛ E} 
(hf : Integrable f μ) (h : f =ᵐ[μ] g) : f.integral μ = g.integral μ
· 使用定理 `MeasureTheory.SimpleFunc.sub_apply`：∀ {α : Type u_1} {β : Type u_2} [ins
t : MeasurableSpace α] [inst_1 : Sub β] (f g : MeasureTheory.SimpleFunc α β)   (
x : α), (f - g) x = f x …
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `MeasureTheory.SimpleFunc.posPart_sub_negPart`：posPart_sub_negPart (f : α
 ->ₛ Real) : f.posPart - f.negPart = f
-/
theorem integral_eq_norm_posPart_sub (f : α →₁ₛ[μ] ℝ) : integral f = ‖posPart f‖ - ‖negPart f‖ := by
  -- Convert things in `L¹` to their `SimpleFunc` counterpart
  have ae_eq₁ : (toSimpleFunc f).posPart =ᵐ[μ] (toSimpleFunc (posPart f)).map norm := by
    filter_upwards [posPart_toSimpleFunc f] with _ h
    rw [SimpleFunc.map_apply, h]
    conv_lhs => rw [← SimpleFunc.posPart_map_norm, SimpleFunc.map_apply]
  -- Convert things in `L¹` to their `SimpleFunc` counterpart
  have ae_eq₂ : (toSimpleFunc f).negPart =ᵐ[μ] (toSimpleFunc (negPart f)).map norm := by
    filter_upwards [negPart_toSimpleFunc f] with _ h
    rw [SimpleFunc.map_apply, h]
    conv_lhs => rw [← SimpleFunc.negPart_map_norm, SimpleFunc.map_apply]
  rw [integral, norm_eq_integral, norm_eq_integral, ← SimpleFunc.integral_sub]
  · change (toSimpleFunc f).integral μ =
      ((toSimpleFunc (posPart f)).map norm - (toSimpleFunc (negPart f)).map norm).integral μ
    apply MeasureTheory.SimpleFunc.integral_congr (SimpleFunc.integrable f)
    filter_upwards [ae_eq₁, ae_eq₂] with _ h₁ h₂
    rw [SimpleFunc.sub_apply, ← h₁, ← h₂]
    exact DFunLike.congr_fun (toSimpleFunc f).posPart_sub_negPart.symm _
  · exact (SimpleFunc.integrable f).pos_part.congr ae_eq₁
  · exact (SimpleFunc.integrable f).neg_part.congr ae_eq₂

end PosPart

end SimpleFuncIntegral

end SimpleFunc

open L1.SimpleFunc

local notation "Integral" => @integralCLM α E _ _ _ _ _ μ _

variable [NormedSpace ℝ E] [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [SMulCommClass ℝ 𝕜 E]
  [CompleteSpace E]

section IntegrationInL1

attribute [local instance] simpleFunc.isBoundedSMul simpleFunc.module

open ContinuousLinearMap

variable (𝕜) in
/-- The Bochner integral in L1 space as a continuous linear map. -/
nonrec def integralCLM' : (α →₁[μ] E) →L[𝕜] E :=
  (integralCLM' α E 𝕜 μ).extend (coeToLp α E 𝕜)

/-- The Bochner integral in L1 space as a continuous linear map over ℝ. -/
/-
**MeasureTheory.L1.integralCLM** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.L1`。
形式化陈述：integralCLM : (α ->₁[μ] E) ->L[Real] E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Bochner integral in L1 space as a continuous linear map over ℝ.
-/
def integralCLM : (α →₁[μ] E) →L[ℝ] E :=
  integralCLM' ℝ

/-- The Bochner integral in L1 space -/
irreducible_def integral : (α →₁[μ] E) → E :=
  integralCLM

/-
**MeasureTheory.L1.integral_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L1`。
形式化陈述：integral_eq (f : α ->₁[μ] E) : integral f = integralCLM f
参数：f : α ->₁[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.L1.integral_def`：∀ {α : Type u_5} {E : Type u_6} [inst : N
ormedAddCommGroup E] {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [in
st_1 : NormedSpace …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_eq (f : α →₁[μ] E) : integral f = integralCLM f := by
  simp only [integral]
/-
**MeasureTheory.L1.integral_eq_setToL1** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
L1`。
形式化陈述：integral_eq_setToL1 (f : α ->₁[μ] E) : integral f = setToL1 (dominatedFinM
easAdditive_weightedSMul μ) f
参数：f : α ->₁[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.L1.integral_def`：∀ {α : Type u_5} {E : Type u_6} [inst : N
ormedAddCommGroup E] {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [in
st_1 : NormedSpace …
-/
theorem integral_eq_setToL1 (f : α →₁[μ] E) :
    integral f = setToL1 (dominatedFinMeasAdditive_weightedSMul μ) f := by
  simp only [integral]; rfl

@[norm_cast]
/-
**MeasureTheory.L1.SimpleFunc.integral_L1_eq_integral** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.L1.SimpleFunc`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} [inst : NormedAddCommGroup E] {m : Measura
bleSpace α} {μ : MeasureTheory.Measure α}   [inst_1 : NormedSpace ℝ E] [inst_2 :
 CompleteSpace E] (f : ↥(α →₁ₛ[μ] E)),   MeasureTheory.L1.integral ↑f = MeasureT
heory.L1.SimpleFunc.integral f
参数：f : ↥(α →₁ₛ[μ] E)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.L1.integral_def`：∀ {α : Type u_5} {E : Type u_6} [inst : N
ormedAddCommGroup E] {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [in
st_1 : NormedSpace …
· 使用定理 `MeasureTheory.L1.setToL1_eq_setToL1SCLM`：setToL1_eq_setToL1SCLM (hT : Do
minatedFinMeasAdditive μ T C) (f : α ->₁ₛ[μ] E) : setToL1 hT f = setToL1SCLM α E
 μ hT f
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
-/
theorem SimpleFunc.integral_L1_eq_integral (f : α →₁ₛ[μ] E) :
    L1.integral (f : α →₁[μ] E) = SimpleFunc.integral f := by
  simp only [integral, L1.integral]
  exact setToL1_eq_setToL1SCLM (dominatedFinMeasAdditive_weightedSMul μ) f

@[norm_cast]
/-
**MeasureTheory.L1.SimpleFunc.integralCLM'_L1_eq_integral** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.L1.SimpleFunc`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {𝕜 : Type u_4} [inst : NormedAddCommGroup 
E] {m : MeasurableSpace α}   {μ : MeasureTheory.Measure α} [inst_1 : NormedSpace
 ℝ E] [inst_2 : NormedRing 𝕜] [inst_3 : _root_.Module 𝕜 E]   [inst_4 : IsBounded
SMul 𝕜 E] [inst_5 : SMulCommClass ℝ 𝕜 E] [inst_6 : CompleteSpace E] (f : ↥(α →₁ₛ
[μ] E)),   (MeasureTheory.L1.integralCLM' 𝕜) ↑f = MeasureTheory.L1.SimpleFunc.in
tegral f
参数：f : ↥(α →₁ₛ[μ] E)；MeasureTheory.L1.integralCLM' 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousLinearMap.extend_eq`：extend_eq (h_dense : DenseRange e) (h_e :
 IsUniformInducing e) (x : E) : extend f e (e x) = f x
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.Lp.simpleFunc.denseRange`：∀ {α : Type u_1} {E : Type u_4} 
[inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {p : ENNReal}   {μ : 
MeasureTheory.Measure α} [in…
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `MeasureTheory.Lp.simpleFunc.isUniformInducing`：isUniformInducing : IsUni
formInducing ((↑) : Lp.simpleFunc E p μ -> Lp E p μ)
-/
theorem SimpleFunc.integralCLM'_L1_eq_integral (f : α →₁ₛ[μ] E) :
    L1.integralCLM' 𝕜 (f : α →₁[μ] E) = SimpleFunc.integral f := by
  apply ContinuousLinearMap.extend_eq _ _ simpleFunc.isUniformInducing
  exact simpleFunc.denseRange one_ne_top

variable (𝕜) in
/-
**MeasureTheory.L1.integral_eq'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L1`。
形式化陈述：integral_eq' (f : α ->₁[μ] E) : integral f = integralCLM' 𝕜 f
参数：f : α ->₁[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `isClosed_property`：isClosed_property [TopologicalSpace β] {e : α -> β} {
p : β -> Prop} (he : DenseRange e) (hp : IsClosed { x | p x }) (h : forall a, p 
(e a)) …
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.Lp.simpleFunc.denseRange`：∀ {α : Type u_1} {E : Type u_4} 
[inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {p : ENNReal}   {μ : 
MeasureTheory.Measure α} [in…
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L1.integral_def`：∀ {α : Type u_5} {E : Type u_6} [inst : N
ormedAddCommGroup E] {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [in
st_1 : NormedSpace …
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.L1.SimpleFunc.integral_L1_eq_integral`：∀ {α : Type u_1} {E
 : Type u_2} [inst : NormedAddCommGroup E] {m : MeasurableSpace α} {μ : MeasureT
heory.Measure α}   [inst_1 : NormedSpace …
· 使用定理 `MeasureTheory.L1.SimpleFunc.integralCLM'_L1_eq_integral`：∀ {α : Type u_1
} {E : Type u_2} {𝕜 : Type u_4} [inst : NormedAddCommGroup E] {m : MeasurableSpa
ce α}   {μ : MeasureTheory.Measure α} [inst_1…
-/
theorem integral_eq' (f : α →₁[μ] E) : integral f = integralCLM' 𝕜 f := by
  apply isClosed_property (simpleFunc.denseRange one_ne_top)
    (isClosed_eq _ (integralCLM' 𝕜).continuous) _ f
  · simp_rw [integral_def]
    exact (integralCLM (E := E)).continuous
  intro f
  norm_cast

variable (α E)

@[simp]
/-
**MeasureTheory.L1.integral_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L1`。
形式化陈述：integral_zero : integral (0 : α ->₁[μ] E) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.L1.integral_def`：∀ {α : Type u_5} {E : Type u_6} [inst : N
ormedAddCommGroup E] {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [in
st_1 : NormedSpace …
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
-/
theorem integral_zero : integral (0 : α →₁[μ] E) = 0 := by
  simp only [integral]
  exact map_zero integralCLM

variable {α E}

@[integral_simps]
/-
**MeasureTheory.L1.integral_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L1`。
形式化陈述：integral_add (f g : α ->₁[μ] E) : integral (f + g) = integral f + integral
 g
参数：f g : α ->₁[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.L1.integral_def`：∀ {α : Type u_5} {E : Type u_6} [inst : N
ormedAddCommGroup E] {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [in
st_1 : NormedSpace …
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
theorem integral_add (f g : α →₁[μ] E) : integral (f + g) = integral f + integral g := by
  simp only [integral]
  exact map_add integralCLM f g

@[integral_simps]
/-
**MeasureTheory.L1.integral_neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L1`。
形式化陈述：integral_neg (f : α ->₁[μ] E) : integral (-f) = -integral f
参数：f : α ->₁[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.L1.integral_def`：∀ {α : Type u_5} {E : Type u_6} [inst : N
ormedAddCommGroup E] {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [in
st_1 : NormedSpace …
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
-/
theorem integral_neg (f : α →₁[μ] E) : integral (-f) = -integral f := by
  simp only [integral]
  exact map_neg integralCLM f

@[integral_simps]
/-
**MeasureTheory.L1.integral_sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L1`。
形式化陈述：integral_sub (f g : α ->₁[μ] E) : integral (f - g) = integral f - integral
 g
参数：f g : α ->₁[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.L1.integral_def`：∀ {α : Type u_5} {E : Type u_6} [inst : N
ormedAddCommGroup E] {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [in
st_1 : NormedSpace …
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
-/
theorem integral_sub (f g : α →₁[μ] E) : integral (f - g) = integral f - integral g := by
  simp only [integral]
  exact map_sub integralCLM f g

@[integral_simps]
/-
**MeasureTheory.L1.integral_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L1`。
形式化陈述：integral_smul (c : 𝕜) (f : α ->₁[μ] E) : integral (c • f) = c • integral f
参数：c : 𝕜；f : α ->₁[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L1.integral_eq'`：integral_eq' (f : α ->₁[μ] E) : integral 
f = integralCLM' 𝕜 f
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
theorem integral_smul (c : 𝕜) (f : α →₁[μ] E) : integral (c • f) = c • integral f := by
  rw [integral_eq' 𝕜 f, integral_eq' 𝕜 (c • f), map_smul (integralCLM' 𝕜) c f]
/-
**MeasureTheory.L1.norm_Integral_le_one** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.L1`。
形式化陈述：norm_Integral_le_one : ‖integralCLM (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.L1.norm_setToL1_le`：norm_setToL1_le (hT : DominatedFinMeas
Additive μ T C) (hC : 0 <= C) : ‖setToL1 hT‖ <= C
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
theorem norm_Integral_le_one : ‖integralCLM (α := α) (E := E) (μ := μ)‖ ≤ 1 :=
  norm_setToL1_le (dominatedFinMeasAdditive_weightedSMul μ) zero_le_one
/-
**MeasureTheory.L1.nnnorm_Integral_le_one** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.L1`。
形式化陈述：nnnorm_Integral_le_one : ‖integralCLM (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.L1.norm_Integral_le_one`：norm_Integral_le_one : ‖integralC
LM (α
-/
theorem nnnorm_Integral_le_one : ‖integralCLM (α := α) (E := E) (μ := μ)‖₊ ≤ 1 :=
  norm_Integral_le_one
/-
**MeasureTheory.L1.norm_integral_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L1`
。
形式化陈述：norm_integral_le (f : α ->₁[μ] E) : ‖integral f‖ <= ‖f‖
参数：f : α ->₁[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.L1.integral_def`：∀ {α : Type u_5} {E : Type u_6} [inst : N
ormedAddCommGroup E] {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [in
st_1 : NormedSpace …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `MeasureTheory.L1.norm_Integral_le_one`：norm_Integral_le_one : ‖integralC
LM (α
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem norm_integral_le (f : α →₁[μ] E) : ‖integral f‖ ≤ ‖f‖ :=
  calc
    ‖integral f‖ = ‖integralCLM f‖ := by simp only [integral]
    _ ≤ ‖integralCLM (α := α) (μ := μ)‖ * ‖f‖ := le_opNorm _ _
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right norm_Integral_le_one <| norm_nonneg _
    _ = ‖f‖ := one_mul _
/-
**MeasureTheory.L1.nnnorm_integral_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L
1`。
形式化陈述：nnnorm_integral_le (f : α ->₁[μ] E) : ‖integral f‖₊ <= ‖f‖₊
参数：f : α ->₁[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.L1.norm_integral_le`：norm_integral_le (f : α ->₁[μ] E) : ‖
integral f‖ <= ‖f‖
-/
theorem nnnorm_integral_le (f : α →₁[μ] E) : ‖integral f‖₊ ≤ ‖f‖₊ :=
  norm_integral_le f

@[continuity]
/-
**MeasureTheory.L1.continuous_integral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
L1`。
形式化陈述：continuous_integral : Continuous fun f : α ->₁[μ] E => integral f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.L1.integral_def`：∀ {α : Type u_5} {E : Type u_6} [inst : N
ormedAddCommGroup E] {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [in
st_1 : NormedSpace …
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
theorem continuous_integral : Continuous fun f : α →₁[μ] E => integral f := by
  simp only [integral]
  exact L1.integralCLM.continuous

section PosPart

/-
**MeasureTheory.L1.integral_eq_norm_posPart_sub** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.L1`。
形式化陈述：integral_eq_norm_posPart_sub (f : α ->₁[μ] Real) : integral f = ‖Lp.posPar
t f‖ - ‖Lp.negPart f‖
参数：f : α ->₁[μ] Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `isClosed_property`：isClosed_property [TopologicalSpace β] {e : α -> β} {
p : β -> Prop} (he : DenseRange e) (hp : IsClosed { x | p x }) (h : forall a, p 
(e a)) …
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.Lp.simpleFunc.denseRange`：∀ {α : Type u_1} {E : Type u_4} 
[inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {p : ENNReal}   {μ : 
MeasureTheory.Measure α} [in…
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L1.integral_def`：∀ {α : Type u_5} {E : Type u_6} [inst : N
ormedAddCommGroup E] {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [in
st_1 : NormedSpace …
· 使用定理 `ContinuousLinearMap.cont`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiri
ng R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_3}   [inst_2 : Topological
Space M] [inst…
· 使用定理 `Continuous.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpace
 X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : X 
→ G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_norm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Continu
ous fun a => ‖a‖
· 使用定理 `MeasureTheory.Lp.continuous_posPart`：continuous_posPart [Fact (1 <= p)] 
: Continuous fun f : Lp Real p μ => posPart f
· 使用定理 `MeasureTheory.Lp.continuous_negPart`：continuous_negPart [Fact (1 <= p)] 
: Continuous fun f : Lp Real p μ => negPart f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.L1.SimpleFunc.integral_L1_eq_integral`：∀ {α : Type u_1} {E
 : Type u_2} [inst : NormedAddCommGroup E] {m : MeasurableSpace α} {μ : MeasureT
heory.Measure α}   [inst_1 : NormedSpace …
· 使用定理 `MeasureTheory.L1.SimpleFunc.integral_eq_norm_posPart_sub`：integral_eq_no
rm_posPart_sub (f : α ->₁ₛ[μ] Real) : integral f = ‖posPart f‖ - ‖negPart f‖
-/
theorem integral_eq_norm_posPart_sub (f : α →₁[μ] ℝ) :
    integral f = ‖Lp.posPart f‖ - ‖Lp.negPart f‖ := by
  -- Use `isClosed_property` and `isClosed_eq`
  refine @isClosed_property _ _ _ ((↑) : (α →₁ₛ[μ] ℝ) → α →₁[μ] ℝ)
      (fun f : α →₁[μ] ℝ => integral f = ‖Lp.posPart f‖ - ‖Lp.negPart f‖)
      (simpleFunc.denseRange one_ne_top) (isClosed_eq ?_ ?_) ?_ f
  · simp only [integral]
    exact cont _
  · refine Continuous.sub (continuous_norm.comp Lp.continuous_posPart)
      (continuous_norm.comp Lp.continuous_negPart)
  -- Show that the property holds for all simple functions in the `L¹` space.
  · intro s
    norm_cast
    exact SimpleFunc.integral_eq_norm_posPart_sub _

end PosPart

end IntegrationInL1

end L1

end MeasureTheory

