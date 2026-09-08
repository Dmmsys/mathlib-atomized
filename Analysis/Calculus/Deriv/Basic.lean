/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.TangentCone.DimOne
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!

# One-dimensional derivatives

This file defines the derivative of a function `f : 𝕜 → F` where `𝕜` is a
normed field and `F` is a normed space over this field. The derivative of
such a function `f` at a point `x` is given by an element `f' : F`.

The theory is developed analogously to the [Fréchet
derivatives](./fderiv.html). We first introduce predicates defined in terms
of the corresponding predicates for Fréchet derivatives:

- `HasDerivAtFilter f f' L` states that the function `f` has the
  derivative `f'` along the filter `L : Filter (𝕜 × 𝕜)`.

- `HasDerivWithinAt f f' s x` states that the function `f` has the
  derivative `f'` at the point `x` within the subset `s`.

- `HasDerivAt f f' x` states that the function `f` has the derivative `f'`
  at the point `x`.

- `HasStrictDerivAt f f' x` states that the function `f` has the derivative `f'`
  at the point `x` in the sense of strict differentiability, i.e.,
  `f y - f z = (y - z) • f' + o (y - z)` as `y, z → x`.

For the last two notions we also define a functional version:

- `derivWithin f s x` is a derivative of `f` at `x` within `s`. If the
  derivative does not exist, then `derivWithin f s x` equals zero.

- `deriv f x` is a derivative of `f` at `x`. If the derivative does not
  exist, then `deriv f x` equals zero.

The theorems `fderivWithin_derivWithin` and `fderiv_deriv` show that the
one-dimensional derivatives coincide with the general Fréchet derivatives.

We also show the existence and compute the derivatives of:
  - constants
  - the identity function
  - linear maps (in `Linear.lean`)
  - addition (in `Add.lean`)
  - sum of finitely many functions (in `Add.lean`)
  - negation (in `Add.lean`)
  - subtraction (in `Add.lean`)
  - star (in `Star.lean`)
  - multiplication of two functions in `𝕜 → 𝕜` (in `Mul.lean`)
  - multiplication of a function in `𝕜 → 𝕜` and of a function in `𝕜 → E` (in `Mul.lean`)
  - powers of a function (in `Pow.lean` and `ZPow.lean`)
  - inverse `x → x⁻¹` (in `Inv.lean`)
  - division (in `Inv.lean`)
  - composition of a function in `𝕜 → F` with a function in `𝕜 → 𝕜` (in `Comp.lean`)
  - composition of a function in `F → E` with a function in `𝕜 → F` (in `Comp.lean`)
  - inverse function (assuming that it exists; the inverse function theorem is in `Inverse.lean`)
  - polynomials (in `Polynomial.lean`)

For most binary operations we also define `const_op` and `op_const` theorems for the cases when
the first or second argument is a constant. This makes writing chains of `HasDerivAt`'s easier,
and they more frequently lead to the desired result.

We set up the simplifier so that it can compute the derivative of simple functions. For instance,
```lean
example (x : ℝ) :
    deriv (fun x ↦ cos (sin x) * exp x) x = (cos (sin x) - sin (sin x) * cos x) * exp x := by
  simp; ring
```

The relationship between the derivative of a function and its definition from a standard
undergraduate course as the limit of the slope `(f y - f x) / (y - x)` as `y` tends to `𝓝[≠] x`
is developed in the file `Mathlib/Analysis/Calculus/Deriv/Slope.lean`.

## Implementation notes

Most of the theorems are direct restatements of the corresponding theorems
for Fréchet derivatives.

The strategy to construct simp lemmas that give the simplifier the possibility to compute
derivatives is the same as the one for differentiability statements, as explained in
`Mathlib/Analysis/Calculus/FDeriv/Basic.lean`. See the explanations there.
-/

@[expose] public section

universe u v w

noncomputable section

open scoped Topology ENNReal NNReal
open Filter Asymptotics Set

open ContinuousLinearMap (smulRight toSpanSingleton_inj toSpanSingleton)

section TVS

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

section
variable [ContinuousSMul 𝕜 F]

/-- `f` has the derivative `f'` along the filter `L`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `(x', x)` converges along the filter `L`.
-/
/-
**HasDerivAtFilter** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HasDerivAtFilter (f : 𝕜 -> F) (f' : F) (L : Filter (𝕜 × 𝕜))
参数：f : 𝕜 -> F；f' : F；L : Filter (𝕜 × 𝕜)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` has the derivative `f'` along the filter `L`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `(x', x)` converges alon
g the filter `L`.
-/
def HasDerivAtFilter (f : 𝕜 → F) (f' : F) (L : Filter (𝕜 × 𝕜)) :=
  HasFDerivAtFilter f (toSpanSingleton 𝕜 f') L

/-- `f` has the derivative `f'` at the point `x` within the subset `s`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges to `x` inside `s`.
-/
/-
**HasDerivWithinAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HasDerivWithinAt (f : 𝕜 -> F) (f' : F) (s : Set 𝕜) (x : 𝕜)
参数：f : 𝕜 -> F；f' : F；s : Set 𝕜；x : 𝕜。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` has the derivative `f'` at the point `x` within the subset `s`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges to `x` in
side `s`.
-/
def HasDerivWithinAt (f : 𝕜 → F) (f' : F) (s : Set 𝕜) (x : 𝕜) :=
  HasDerivAtFilter f f' (𝓝[s] x ×ˢ pure x)

/-- `f` has the derivative `f'` at the point `x`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges to `x`.
-/
/-
**HasDerivAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HasDerivAt (f : 𝕜 -> F) (f' : F) (x : 𝕜)
参数：f : 𝕜 -> F；f' : F；x : 𝕜。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` has the derivative `f'` at the point `x`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges to `x`.
-/
def HasDerivAt (f : 𝕜 → F) (f' : F) (x : 𝕜) :=
  HasDerivAtFilter f f' (𝓝 x ×ˢ pure x)

/-- `f` has the derivative `f'` at the point `x` in the sense of strict differentiability.

That is, `f y - f z = (y - z) • f' + o(y - z)` as `y, z → x`. -/
/-
**HasStrictDerivAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HasStrictDerivAt (f : 𝕜 -> F) (f' : F) (x : 𝕜)
参数：f : 𝕜 -> F；f' : F；x : 𝕜。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` has the derivative `f'` at the point `x` in the sense of strict differentiab
ility.

That is, `f y - f z = (y - z) • f' + o(y - z)` as `y, z → x`.
-/
def HasStrictDerivAt (f : 𝕜 → F) (f' : F) (x : 𝕜) :=
  HasDerivAtFilter f f' (𝓝 (x, x))

end
/-- Derivative of `f` at the point `x` within the set `s`, if it exists.  Zero otherwise.

If the derivative exists (i.e., `∃ f', HasDerivWithinAt f f' s x`), then
`f x' = f x + (x' - x) • derivWithin f s x + o(x' - x)` where `x'` converges to `x` inside `s`.
-/
/-
**derivWithin** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：derivWithin (f : 𝕜 -> F) (s : Set 𝕜) (x : 𝕜)
参数：f : 𝕜 -> F；s : Set 𝕜；x : 𝕜。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Derivative of `f` at the point `x` within the set `s`, if it exists.  Zero other
wise.

If the derivative exists (i.e., `∃ f', HasDerivWithinAt f f' s x`), then
`f x' = f x + (x' - x) • derivWithin f s x + o(x' - x)` where `x'` converges to 
`x` inside `s`.
-/
def derivWithin (f : 𝕜 → F) (s : Set 𝕜) (x : 𝕜) :=
  fderivWithin 𝕜 f s x 1

/-- Derivative of `f` at the point `x`, if it exists.  Zero otherwise.

If the derivative exists (i.e., `∃ f', HasDerivAt f f' x`), then
`f x' = f x + (x' - x) • deriv f x + o(x' - x)` where `x'` converges to `x`.
-/
/-
**deriv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：deriv (f : 𝕜 -> F) (x : 𝕜)
参数：f : 𝕜 -> F；x : 𝕜。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Derivative of `f` at the point `x`, if it exists.  Zero otherwise.

If the derivative exists (i.e., `∃ f', HasDerivAt f f' x`), then
`f x' = f x + (x' - x) • deriv f x + o(x' - x)` where `x'` converges to `x`.
-/
def deriv (f : 𝕜 → F) (x : 𝕜) :=
  fderiv 𝕜 f x 1

variable {f f₀ f₁ : 𝕜 → F}
variable {f' f₀' f₁' g' : F}
variable {x : 𝕜}
variable {s t : Set 𝕜}
variable {L : Filter (𝕜 × 𝕜)}

section
variable [ContinuousSMul 𝕜 F]
/-- Expressing `HasFDerivAtFilter f f' x L` in terms of `HasDerivAtFilter` -/
/-
**hasFDerivAtFilter_iff_hasDerivAtFilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAtFilter_iff_hasDerivAtFilter {f' : 𝕜 ->L[𝕜] F} : HasFDerivAtFilt
er f f' L ↔ HasDerivAtFilter f (f' 1) L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.toSpanSingleton_apply_map_one`：∀ (R₁ : Type u_1) [in
st : Semiring R₁] {M₂ : Type u_6} [inst_1 : TopologicalSpace M₂] [inst_2 : AddCo
mmMonoid M₂]   [inst_3 : _root_.Module …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Expressing `HasFDerivAtFilter f f' x L` in terms of `HasDerivAtFilter`
-/
theorem hasFDerivAtFilter_iff_hasDerivAtFilter {f' : 𝕜 →L[𝕜] F} :
    HasFDerivAtFilter f f' L ↔ HasDerivAtFilter f (f' 1) L := by simp [HasDerivAtFilter]

alias ⟨HasFDerivAtFilter.hasDerivAtFilter, _⟩ := hasFDerivAtFilter_iff_hasDerivAtFilter
/-
**hasDerivAtFilter_iff_hasFDerivAtFilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAtFilter_iff_hasFDerivAtFilter : HasDerivAtFilter f f' L ↔ HasFDer
ivAtFilter f (toSpanSingleton 𝕜 f') L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem hasDerivAtFilter_iff_hasFDerivAtFilter :
    HasDerivAtFilter f f' L ↔ HasFDerivAtFilter f (toSpanSingleton 𝕜 f') L :=
  .rfl

alias ⟨HasDerivAtFilter.hasFDerivAtFilter, _⟩ := hasDerivAtFilter_iff_hasFDerivAtFilter

/-- Expressing `HasFDerivWithinAt f f' s x` in terms of `HasDerivWithinAt` -/
/-
**hasFDerivWithinAt_iff_hasDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_iff_hasDerivWithinAt {f' : 𝕜 ->L[𝕜] F} : HasFDerivWithin
At f f' s x ↔ HasDerivWithinAt f (f' 1) s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_iff_hasDerivAtFilter`：hasFDerivAtFilter_iff_hasDerivAt
Filter {f' : 𝕜 ->L[𝕜] F} : HasFDerivAtFilter f f' L ↔ HasDerivAtFilter f (f' 1) 
L

--- 原说明 ---
Expressing `HasFDerivWithinAt f f' s x` in terms of `HasDerivWithinAt`
-/
theorem hasFDerivWithinAt_iff_hasDerivWithinAt {f' : 𝕜 →L[𝕜] F} :
    HasFDerivWithinAt f f' s x ↔ HasDerivWithinAt f (f' 1) s x :=
  hasFDerivAtFilter_iff_hasDerivAtFilter

alias ⟨HasFDerivWithinAt.hasDerivWithinAt, _⟩ := hasFDerivWithinAt_iff_hasDerivWithinAt

/-- Expressing `HasDerivWithinAt f f' s x` in terms of `HasFDerivWithinAt` -/
/-
**hasDerivWithinAt_iff_hasFDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_iff_hasFDerivWithinAt {f' : F} : HasDerivWithinAt f f' s 
x ↔ HasFDerivWithinAt f (toSpanSingleton 𝕜 f') s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Expressing `HasDerivWithinAt f f' s x` in terms of `HasFDerivWithinAt`
-/
theorem hasDerivWithinAt_iff_hasFDerivWithinAt {f' : F} :
    HasDerivWithinAt f f' s x ↔ HasFDerivWithinAt f (toSpanSingleton 𝕜 f') s x :=
  Iff.rfl

alias ⟨HasDerivWithinAt.hasFDerivWithinAt, _⟩ :=
  hasDerivWithinAt_iff_hasFDerivWithinAt

/-- Expressing `HasFDerivAt f f' x` in terms of `HasDerivAt` -/
/-
**hasFDerivAt_iff_hasDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_iff_hasDerivAt {f' : 𝕜 ->L[𝕜] F} : HasFDerivAt f f' x ↔ HasDer
ivAt f (f' 1) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_iff_hasDerivAtFilter`：hasFDerivAtFilter_iff_hasDerivAt
Filter {f' : 𝕜 ->L[𝕜] F} : HasFDerivAtFilter f f' L ↔ HasDerivAtFilter f (f' 1) 
L

--- 原说明 ---
Expressing `HasFDerivAt f f' x` in terms of `HasDerivAt`
-/
theorem hasFDerivAt_iff_hasDerivAt {f' : 𝕜 →L[𝕜] F} : HasFDerivAt f f' x ↔ HasDerivAt f (f' 1) x :=
  hasFDerivAtFilter_iff_hasDerivAtFilter

alias ⟨HasFDerivAt.hasDerivAt, _⟩ := hasFDerivAt_iff_hasDerivAt

/-- Expressing `HasDerivAt f f' x` in terms of `HasFDerivAt` -/
/-
**hasDerivAt_iff_hasFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_iff_hasFDerivAt {f' : F} : HasDerivAt f f' x ↔ HasFDerivAt f (t
oSpanSingleton 𝕜 f') x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Expressing `HasDerivAt f f' x` in terms of `HasFDerivAt`
-/
theorem hasDerivAt_iff_hasFDerivAt {f' : F} :
    HasDerivAt f f' x ↔ HasFDerivAt f (toSpanSingleton 𝕜 f') x :=
  Iff.rfl

alias ⟨HasDerivAt.hasFDerivAt, _⟩ := hasDerivAt_iff_hasFDerivAt
/-
**hasStrictFDerivAt_iff_hasStrictDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_iff_hasStrictDerivAt {f' : 𝕜 ->L[𝕜] F} : HasStrictFDeriv
At f f' x ↔ HasStrictDerivAt f (f' 1) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_iff_hasDerivAtFilter`：hasFDerivAtFilter_iff_hasDerivAt
Filter {f' : 𝕜 ->L[𝕜] F} : HasFDerivAtFilter f f' L ↔ HasDerivAtFilter f (f' 1) 
L
-/
theorem hasStrictFDerivAt_iff_hasStrictDerivAt {f' : 𝕜 →L[𝕜] F} :
    HasStrictFDerivAt f f' x ↔ HasStrictDerivAt f (f' 1) x :=
  hasFDerivAtFilter_iff_hasDerivAtFilter

protected alias ⟨HasStrictFDerivAt.hasStrictDerivAt, _⟩ :=
  hasStrictFDerivAt_iff_hasStrictDerivAt
/-
**hasStrictDerivAt_iff_hasStrictFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictDerivAt_iff_hasStrictFDerivAt : HasStrictDerivAt f f' x ↔ HasStri
ctFDerivAt f (toSpanSingleton 𝕜 f') x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem hasStrictDerivAt_iff_hasStrictFDerivAt :
    HasStrictDerivAt f f' x ↔ HasStrictFDerivAt f (toSpanSingleton 𝕜 f') x :=
  Iff.rfl

alias ⟨HasStrictDerivAt.hasStrictFDerivAt, _⟩ := hasStrictDerivAt_iff_hasStrictFDerivAt

end

/-
**derivWithin_zero_of_not_differentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_zero_of_not_differentiableWithinAt (h : ¬DifferentiableWithinA
t 𝕜 f s x) : derivWithin f s x = 0
参数：h : ¬DifferentiableWithinAt 𝕜 f s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_zero_of_not_differentiableWithinAt`：fderivWithin_zero_of_no
t_differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) : fderivWithin 𝕜 
f s x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem derivWithin_zero_of_not_differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) :
    derivWithin f s x = 0 := by
  unfold derivWithin
  rw [fderivWithin_zero_of_not_differentiableWithinAt h]
  simp
/-
**differentiableWithinAt_of_derivWithin_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_of_derivWithin_ne_zero (h : derivWithin f s x != 0)
 : DifferentiableWithinAt 𝕜 f s x
参数：h : derivWithin f s x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用定理 `derivWithin_zero_of_not_differentiableWithinAt`：derivWithin_zero_of_not_
differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) : derivWithin f s x
 = 0
-/
theorem differentiableWithinAt_of_derivWithin_ne_zero (h : derivWithin f s x ≠ 0) :
    DifferentiableWithinAt 𝕜 f s x :=
  not_imp_comm.1 derivWithin_zero_of_not_differentiableWithinAt h

end TVS

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {f f₀ f₁ : 𝕜 → F}
variable {f' f₀' f₁' g' : F}
variable {x : 𝕜}
variable {s t : Set 𝕜}
variable {L L₁ L₂ : Filter (𝕜 × 𝕜)}

/-
**derivWithin_zero_of_not_accPt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_zero_of_not_accPt (h : ¬AccPt x (𝓟 s)) : derivWithin f s x = 0
参数：h : ¬AccPt x (𝓟 s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `derivWithin.eq_1`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F :
 Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 : Topo
logica…
· 使用定理 `fderivWithin_zero_of_not_accPt`：fderivWithin_zero_of_not_accPt (h : ¬Acc
Pt x (𝓟 s)) : fderivWithin 𝕜 f s x = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
-/
theorem derivWithin_zero_of_not_accPt (h : ¬AccPt x (𝓟 s)) : derivWithin f s x = 0 := by
  rw [derivWithin, fderivWithin_zero_of_not_accPt h, zero_apply]
/-
**derivWithin_zero_of_not_uniqueDiffWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_zero_of_not_uniqueDiffWithinAt (h : ¬UniqueDiffWithinAt 𝕜 s x)
 : derivWithin f s x = 0
参数：h : ¬UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `derivWithin_zero_of_not_accPt`：derivWithin_zero_of_not_accPt (h : ¬AccPt
 x (𝓟 s)) : derivWithin f s x = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `AccPt.uniqueDiffWithinAt`：∀ {𝕜 : Type u_1} [inst : NormedDivisionRing 𝕜]
 {s : Set 𝕜} {x : 𝕜},   AccPt x (Filter.principal s) → UniqueDiffWithinAt 𝕜 s x
-/
theorem derivWithin_zero_of_not_uniqueDiffWithinAt (h : ¬UniqueDiffWithinAt 𝕜 s x) :
    derivWithin f s x = 0 :=
  derivWithin_zero_of_not_accPt <| mt AccPt.uniqueDiffWithinAt h
/-
**derivWithin_zero_of_notMem_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_zero_of_notMem_closure (h : x ∉ closure s) : derivWithin f s x
 = 0
参数：h : x ∉ closure s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `derivWithin.eq_1`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F :
 Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 : Topo
logica…
· 使用定理 `fderivWithin_zero_of_notMem_closure`：fderivWithin_zero_of_notMem_closure
 (h : x ∉ closure s) : fderivWithin 𝕜 f s x = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
-/
theorem derivWithin_zero_of_notMem_closure (h : x ∉ closure s) : derivWithin f s x = 0 := by
  rw [derivWithin, fderivWithin_zero_of_notMem_closure h, zero_apply]
/-
**deriv_zero_of_not_differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_zero_of_not_differentiableAt (h : ¬DifferentiableAt 𝕜 f x) : deriv f
 x = 0
参数：h : ¬DifferentiableAt 𝕜 f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderiv_zero_of_not_differentiableAt`：fderiv_zero_of_not_differentiableAt
 (h : ¬DifferentiableAt 𝕜 f x) : fderiv 𝕜 f x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem deriv_zero_of_not_differentiableAt (h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0 := by
  unfold deriv
  rw [fderiv_zero_of_not_differentiableAt h]
  simp
/-
**differentiableAt_of_deriv_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_of_deriv_ne_zero (h : deriv f x != 0) : DifferentiableAt 
𝕜 f x
参数：h : deriv f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用定理 `deriv_zero_of_not_differentiableAt`：deriv_zero_of_not_differentiableAt (
h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0
-/
theorem differentiableAt_of_deriv_ne_zero (h : deriv f x ≠ 0) : DifferentiableAt 𝕜 f x :=
  not_imp_comm.1 deriv_zero_of_not_differentiableAt h
/-
**UniqueDiffWithinAt.eq_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueDiffWithinAt.eq_deriv (s : Set 𝕜) (H : UniqueDiffWithinAt 𝕜 s x) (h 
: HasDerivWithinAt f f' s x) (h₁ : HasDerivWithinAt f f₁' s x) : f' = f₁'
参数：s : Set 𝕜；H : UniqueDiffWithinAt 𝕜 s x；h : HasDerivWithinAt f f' s x；h₁ : Has
DerivWithinAt f f₁' s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ContinuousLinearMap.toSpanSingleton_inj`：∀ {R₁ : Type u_1} [inst : Semir
ing R₁] {M₂ : Type u_6} [inst_1 : TopologicalSpace M₂] [inst_2 : AddCommMonoid M
₂]   [inst_3 : _root_.Module …
· 使用定理 `UniqueDiffWithinAt.eq`：UniqueDiffWithinAt.eq (H : UniqueDiffWithinAt 𝕜 s
 x) (hf : HasFDerivWithinAt f f' s x) (hg : HasFDerivWithinAt f f₁' s x) : f' = 
f₁'
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem UniqueDiffWithinAt.eq_deriv (s : Set 𝕜) (H : UniqueDiffWithinAt 𝕜 s x)
    (h : HasDerivWithinAt f f' s x) (h₁ : HasDerivWithinAt f f₁' s x) : f' = f₁' :=
  toSpanSingleton_inj.mp <| UniqueDiffWithinAt.eq H h h₁
/-
**hasDerivAtFilter_iff_isLittleO** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAtFilter_iff_isLittleO : HasDerivAtFilter f f' L ↔ (fun p => f p.1
 - f p.2 - (p.1 - p.2) • f') =o[L] fun p => p.1 - p.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_iff_isLittleO`：hasFDerivAtFilter_iff_isLittleO {L : Fi
lter (E × E)} : HasFDerivAtFilter f f' L ↔ (fun p => f p.1 - f p.2 - f' (p.1 - p
.2)) =o[L] fun p => p…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem hasDerivAtFilter_iff_isLittleO :
    HasDerivAtFilter f f' L ↔
      (fun p => f p.1 - f p.2 - (p.1 - p.2) • f') =o[L] fun p => p.1 - p.2 :=
  hasFDerivAtFilter_iff_isLittleO ..
/-
**hasDerivAtFilter_iff_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAtFilter_iff_tendsto : HasDerivAtFilter f f' L ↔ Tendsto (fun p =>
 ‖p.1 - p.2‖⁻¹ * ‖f p.1 - f p.2 - (p.1 - p.2) • f'‖) L (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_iff_tendsto`：hasFDerivAtFilter_iff_tendsto : HasFDeriv
AtFilter f f' L ↔ Tendsto (fun p => ‖p.1 - p.2‖⁻¹ * ‖f p.1 - f p.2 - f' (p.1 - p
.2)‖) L (𝓝 0)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem hasDerivAtFilter_iff_tendsto :
    HasDerivAtFilter f f' L ↔
      Tendsto (fun p ↦ ‖p.1 - p.2‖⁻¹ * ‖f p.1 - f p.2 - (p.1 - p.2) • f'‖) L (𝓝 0) :=
  hasFDerivAtFilter_iff_tendsto
/-
**hasDerivWithinAt_iff_isLittleO** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_iff_isLittleO : HasDerivWithinAt f f' s x ↔ (fun x' : 𝕜 =
> f x' - f x - (x' - x) • f') =o[𝓝[s] x] fun x' => x' - x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivWithinAt_iff_isLittleO`：hasFDerivWithinAt_iff_isLittleO : HasFD
erivWithinAt f f' s x ↔ (fun x' => f x' - f x - f' (x' - x)) =o[𝓝[s] x] (fun x' 
=> x' - x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem hasDerivWithinAt_iff_isLittleO :
    HasDerivWithinAt f f' s x ↔
      (fun x' : 𝕜 => f x' - f x - (x' - x) • f') =o[𝓝[s] x] fun x' => x' - x :=
  hasFDerivWithinAt_iff_isLittleO

alias ⟨HasDerivWithinAt.isLittleO, HasDerivWithinAt.of_isLittleO⟩ := hasDerivWithinAt_iff_isLittleO
/-
**hasDerivWithinAt_iff_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_iff_tendsto : HasDerivWithinAt f f' s x ↔ Tendsto (fun x'
 => ‖x' - x‖⁻¹ * ‖f x' - f x - (x' - x) • f'‖) (𝓝[s] x) (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivWithinAt_iff_tendsto`：hasFDerivWithinAt_iff_tendsto : HasFDeriv
WithinAt f f' s x ↔ Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - f' (x' - x)‖) 
(𝓝[s] x) (𝓝 0)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem hasDerivWithinAt_iff_tendsto :
    HasDerivWithinAt f f' s x ↔
      Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - (x' - x) • f'‖) (𝓝[s] x) (𝓝 0) :=
  hasFDerivWithinAt_iff_tendsto
/-
**hasDerivAt_iff_isLittleO** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_iff_isLittleO : HasDerivAt f f' x ↔ (fun x' : 𝕜 => f x' - f x -
 (x' - x) • f') =o[𝓝 x] fun x' => x' - x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAt_iff_isLittleO`：hasFDerivAt_iff_isLittleO : HasFDerivAt f f' 
x ↔ (fun x' => f x' - f x - f' (x' - x)) =o[𝓝 x] (fun x' => x' - x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem hasDerivAt_iff_isLittleO :
    HasDerivAt f f' x ↔ (fun x' : 𝕜 => f x' - f x - (x' - x) • f') =o[𝓝 x] fun x' => x' - x :=
  hasFDerivAt_iff_isLittleO ..

alias ⟨HasDerivAt.isLittleO, HasDerivAt.of_isLittleO⟩ := hasDerivAt_iff_isLittleO
/-
**hasDerivAt_iff_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_iff_tendsto : HasDerivAt f f' x ↔ Tendsto (fun x' => ‖x' - x‖⁻¹
 * ‖f x' - f x - (x' - x) • f'‖) (𝓝 x) (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAt_iff_tendsto`：hasFDerivAt_iff_tendsto : HasFDerivAt f f' x ↔ 
Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - f' (x' - x)‖) (𝓝 x) (𝓝 0)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem hasDerivAt_iff_tendsto :
    HasDerivAt f f' x ↔ Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - (x' - x) • f'‖) (𝓝 x) (𝓝 0) :=
  hasFDerivAt_iff_tendsto
/-
**HasDerivAtFilter.isBigO_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAtFilter.isBigO_sub (h : HasDerivAtFilter f f' L) : (fun p => f p.
1 - f p.2) =O[L] fun p => p.1 - p.2
参数：h : HasDerivAtFilter f f' L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivAtFilter.isBigO_sub`：HasFDerivAtFilter.isBigO_sub (h : HasFDeri
vAtFilter f f' L) : (fun p => f p.1 - f p.2) =O[L] fun p => p.1 - p.2
-/
theorem HasDerivAtFilter.isBigO_sub (h : HasDerivAtFilter f f' L) :
    (fun p => f p.1 - f p.2) =O[L] fun p => p.1 - p.2 :=
  HasFDerivAtFilter.isBigO_sub h
/-
**HasDerivAt.isBigO_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.isBigO_sub (h : HasDerivAt f f' x) : (f · - f x) =O[𝓝 x] (· - x
)
参数：h : HasDerivAt f f' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivAt.isBigO_sub`：HasFDerivAt.isBigO_sub (h : HasFDerivAt f f' x₀)
 : (f · - f x₀) =O[𝓝 x₀] (· - x₀)
· 使用定理 `HasDerivAt.hasFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
-/
theorem HasDerivAt.isBigO_sub (h : HasDerivAt f f' x) : (f · - f x) =O[𝓝 x] (· - x) :=
  h.hasFDerivAt.isBigO_sub

/-- This theorem holds for any T2 TVS, see `isClosedEmbedding_smul_left`,
but this would require more imports.

The proof for a TVS is more complicated, and we wouldn't benefit from that form here,
so we prove a weaker version as a private lemma instead. -/
/-
**isInducing_toSpanSingleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This theorem holds for any T2 TVS, see `isClosedEmbedding_smul_left`,
but this would require more imports.

The proof for a TVS is more complicated, and we wouldn't benefit from that form 
here,
so we prove a weaker version as a private lemma instead.
-/
private lemma isInducing_toSpanSingleton (hf' : f' ≠ 0) :
    Topology.IsInducing (toSpanSingleton 𝕜 f') := by
  refine AntilipschitzWith.isInducing (K := ‖f'‖₊⁻¹) ?_ (map_continuous _)
  simp [antilipschitzWith_iff_le_mul_dist, dist_eq_norm, ← sub_smul, norm_smul, field]
/-
**HasDerivAtFilter.isEquivalent_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAtFilter.isEquivalent_sub (hf : HasDerivAtFilter f f' L) (hf' : f'
 != 0) : (fun p => f p.1 - f p.2) ~[L] (fun p => (p.1 - p.2) • f')
参数：hf : HasDerivAtFilter f f' L；hf' : f' != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivAtFilter.isEquivalent_sub`：HasFDerivAtFilter.isEquivalent_sub (
hf : HasFDerivAtFilter f f' L) (hf' : Topology.IsInducing f') : (fun p => f p.1 
- f p.2) ~[L] (fun p => …
· 使用定理 `_private.Mathlib.Analysis.Calculus.Deriv.Basic.0.isInducing_toSpanSingle
ton`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F : Type v} [inst_1 : No
rmedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f' : F}, f' ≠ 0…
-/
theorem HasDerivAtFilter.isEquivalent_sub (hf : HasDerivAtFilter f f' L) (hf' : f' ≠ 0) :
    (fun p ↦ f p.1 - f p.2) ~[L] (fun p ↦ (p.1 - p.2) • f') :=
  HasFDerivAtFilter.isEquivalent_sub hf <| isInducing_toSpanSingleton hf'
/-
**HasDerivAtFilter.isTheta_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAtFilter.isTheta_sub (hf : HasDerivAtFilter f f' L) (hf' : f' != 0
) : (fun p => f p.1 - f p.2) =Θ[L] (fun p => p.1 - p.2)
参数：hf : HasDerivAtFilter f f' L；hf' : f' != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivAtFilter.isTheta_sub`：HasFDerivAtFilter.isTheta_sub (hf : HasFD
erivAtFilter f f' L) (hf' : Topology.IsInducing f') : (fun p => f p.1 - f p.2) =
Θ[L] (fun p => p.1 …
· 使用定理 `_private.Mathlib.Analysis.Calculus.Deriv.Basic.0.isInducing_toSpanSingle
ton`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F : Type v} [inst_1 : No
rmedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f' : F}, f' ≠ 0…
-/
theorem HasDerivAtFilter.isTheta_sub (hf : HasDerivAtFilter f f' L) (hf' : f' ≠ 0) :
    (fun p ↦ f p.1 - f p.2) =Θ[L] (fun p ↦ p.1 - p.2) :=
  HasFDerivAtFilter.isTheta_sub hf <| isInducing_toSpanSingleton hf'

@[deprecated HasDerivAtFilter.isTheta_sub (since := "2026-02-04")]
/-
**HasDerivAtFilter.isBigO_sub_rev** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAtFilter.isBigO_sub_rev (hf : HasDerivAtFilter f f' L) (hf' : f' !
= 0) : (fun p => p.1 - p.2) =O[L] fun p => f p.1 - f p.2
参数：hf : HasDerivAtFilter f f' L；hf' : f' != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Asymptotics.IsTheta.isBigO_symm`：∀ {α : Type u_1} {E : Type u_3} {F : Ty
pe u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}
,   f =Θ[l] g → g =O[…
· 使用定理 `HasDerivAtFilter.isTheta_sub`：HasDerivAtFilter.isTheta_sub (hf : HasDeri
vAtFilter f f' L) (hf' : f' != 0) : (fun p => f p.1 - f p.2) =Θ[L] (fun p => p.1
 - p.2)
-/
theorem HasDerivAtFilter.isBigO_sub_rev (hf : HasDerivAtFilter f f' L) (hf' : f' ≠ 0) :
    (fun p => p.1 - p.2) =O[L] fun p => f p.1 - f p.2 :=
  hf.isTheta_sub hf' |>.isBigO_symm
/-
**HasStrictDerivAt.hasDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.hasDerivAt (h : HasStrictDerivAt f f' x) : HasDerivAt f f
' x
参数：h : HasStrictDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `HasStrictDerivAt.hasStrictFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
-/
theorem HasStrictDerivAt.hasDerivAt (h : HasStrictDerivAt f f' x) : HasDerivAt f f' x :=
  h.hasStrictFDerivAt.hasFDerivAt
/-
**hasDerivWithinAt_congr_set'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_congr_set' {s t : Set 𝕜} (y : 𝕜) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) 
: HasDerivWithinAt f f' s x ↔ HasDerivWithinAt f f' t x
参数：y : 𝕜；h : s =ᶠ[𝓝[{y}ᶜ] x] t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivWithinAt_congr_set'`：hasFDerivWithinAt_congr_set' [T1Space E] (
y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt 
f f' t x
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem hasDerivWithinAt_congr_set' {s t : Set 𝕜} (y : 𝕜) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    HasDerivWithinAt f f' s x ↔ HasDerivWithinAt f f' t x :=
  hasFDerivWithinAt_congr_set' y h
/-
**hasDerivWithinAt_congr_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_congr_set {s t : Set 𝕜} (h : s =ᶠ[𝓝 x] t) : HasDerivWithi
nAt f f' s x ↔ HasDerivWithinAt f f' t x
参数：h : s =ᶠ[𝓝 x] t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivWithinAt_congr_set`：hasFDerivWithinAt_congr_set (h : s =ᶠ[𝓝 x] 
t) : HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt f f' t x
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem hasDerivWithinAt_congr_set {s t : Set 𝕜} (h : s =ᶠ[𝓝 x] t) :
    HasDerivWithinAt f f' s x ↔ HasDerivWithinAt f f' t x :=
  hasFDerivWithinAt_congr_set h

alias ⟨HasDerivWithinAt.congr_set, _⟩ := hasDerivWithinAt_congr_set

@[simp]
/-
**hasDerivWithinAt_sdiff_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_sdiff_singleton : HasDerivWithinAt f f' (s \ {x}) x ↔ Has
DerivWithinAt f f' s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivWithinAt_sdiff_singleton`：hasFDerivWithinAt_sdiff_singleton [T1
Space E] (y : E) : HasFDerivWithinAt f f' (s \ {y}) x ↔ HasFDerivWithinAt f f' s
 x
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem hasDerivWithinAt_sdiff_singleton :
    HasDerivWithinAt f f' (s \ {x}) x ↔ HasDerivWithinAt f f' s x :=
  hasFDerivWithinAt_sdiff_singleton _

@[deprecated (since := "2026-06-03")]
alias hasDerivWithinAt_diff_singleton := hasDerivWithinAt_sdiff_singleton

@[simp]
/-
**hasDerivWithinAt_Ioi_iff_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_Ioi_iff_Ici [PartialOrder 𝕜] : HasDerivWithinAt f f' (Ioi
 x) x ↔ HasDerivWithinAt f f' (Ici x) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ici_sdiff_left`：∀ {α : Type u_1} [inst : PartialOrder α] {a : α}, Se
t.Ici a \ {a} = Set.Ioi a
· 使用定理 `hasDerivWithinAt_sdiff_singleton`：hasDerivWithinAt_sdiff_singleton : Has
DerivWithinAt f f' (s \ {x}) x ↔ HasDerivWithinAt f f' s x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem hasDerivWithinAt_Ioi_iff_Ici [PartialOrder 𝕜] :
    HasDerivWithinAt f f' (Ioi x) x ↔ HasDerivWithinAt f f' (Ici x) x := by
  rw [← Ici_sdiff_left, hasDerivWithinAt_sdiff_singleton]

alias ⟨HasDerivWithinAt.Ici_of_Ioi, HasDerivWithinAt.Ioi_of_Ici⟩ := hasDerivWithinAt_Ioi_iff_Ici

@[simp]
/-
**hasDerivWithinAt_Iio_iff_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_Iio_iff_Iic [PartialOrder 𝕜] : HasDerivWithinAt f f' (Iio
 x) x ↔ HasDerivWithinAt f f' (Iic x) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Iic_sdiff_right`：Iic_sdiff_right : Iic a \ {a} = Iio a
· 使用定理 `hasDerivWithinAt_sdiff_singleton`：hasDerivWithinAt_sdiff_singleton : Has
DerivWithinAt f f' (s \ {x}) x ↔ HasDerivWithinAt f f' s x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem hasDerivWithinAt_Iio_iff_Iic [PartialOrder 𝕜] :
    HasDerivWithinAt f f' (Iio x) x ↔ HasDerivWithinAt f f' (Iic x) x := by
  rw [← Iic_sdiff_right, hasDerivWithinAt_sdiff_singleton]

alias ⟨HasDerivWithinAt.Iic_of_Iio, HasDerivWithinAt.Iio_of_Iic⟩ := hasDerivWithinAt_Iio_iff_Iic
/-
**HasDerivWithinAt.Ioi_iff_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.Ioi_iff_Ioo [LinearOrder 𝕜] [OrderClosedTopology 𝕜] {x y 
: 𝕜} (h : x < y) : HasDerivWithinAt f f' (Ioo x y) x ↔ HasDerivWithinAt f f' (Io
i x) x
参数：h : x < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivWithinAt_inter`：hasFDerivWithinAt_inter (h : t in 𝓝 x) : HasFDe
rivWithinAt f f' (s inter t) x ↔ HasFDerivWithinAt f f' s x
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Iio_mem_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Linea
rOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Iio a ∈ nhds b
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
-/
theorem HasDerivWithinAt.Ioi_iff_Ioo [LinearOrder 𝕜] [OrderClosedTopology 𝕜] {x y : 𝕜} (h : x < y) :
    HasDerivWithinAt f f' (Ioo x y) x ↔ HasDerivWithinAt f f' (Ioi x) x :=
  hasFDerivWithinAt_inter <| Iio_mem_nhds h

alias ⟨HasDerivWithinAt.Ioi_of_Ioo, HasDerivWithinAt.Ioo_of_Ioi⟩ := HasDerivWithinAt.Ioi_iff_Ioo
/-
**hasDerivAt_iff_isLittleO_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_iff_isLittleO_nhds_zero : HasDerivAt f f' x ↔ (fun h => f (x + 
h) - f x - h • f') =o[𝓝 0] fun h => h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAt_iff_isLittleO_nhds_zero`：hasFDerivAt_iff_isLittleO_nhds_zero
 : HasFDerivAt f f' x ↔ (fun h : E => f (x + h) - f x - f' h) =o[𝓝 0] fun h => h
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem hasDerivAt_iff_isLittleO_nhds_zero :
    HasDerivAt f f' x ↔ (fun h => f (x + h) - f x - h • f') =o[𝓝 0] fun h => h :=
  hasFDerivAt_iff_isLittleO_nhds_zero
/-
**HasDerivAtFilter.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAtFilter.mono (h : HasDerivAtFilter f f' L₂) (hst : L₁ <= L₂) : Ha
sDerivAtFilter f f' L₁
参数：h : HasDerivAtFilter f f' L₂；hst : L₁ <= L₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivAtFilter.mono`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [ins
t_3 : Topolo…
-/
theorem HasDerivAtFilter.mono (h : HasDerivAtFilter f f' L₂) (hst : L₁ ≤ L₂) :
    HasDerivAtFilter f f' L₁ :=
  HasFDerivAtFilter.mono h hst
/-
**HasDerivWithinAt.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.mono (h : HasDerivWithinAt f f' t x) (hst : s subseteq t)
 : HasDerivWithinAt f f' s x
参数：h : HasDerivWithinAt f f' t x；hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.mono`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [ins
t_3 : Topolo…
-/
theorem HasDerivWithinAt.mono (h : HasDerivWithinAt f f' t x) (hst : s ⊆ t) :
    HasDerivWithinAt f f' s x :=
  HasFDerivWithinAt.mono h hst
/-
**HasDerivWithinAt.mono_of_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.mono_of_mem_nhdsWithin (h : HasDerivWithinAt f f' t x) (h
st : t in 𝓝[s] x) : HasDerivWithinAt f f' s x
参数：h : HasDerivWithinAt f f' t x；hst : t in 𝓝[s] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.mono_of_mem_nhdsWithin`：HasFDerivWithinAt.mono_of_mem_
nhdsWithin (h : HasFDerivWithinAt f f' t x) (hst : t in 𝓝[s] x) : HasFDerivWithi
nAt f f' s x
-/
theorem HasDerivWithinAt.mono_of_mem_nhdsWithin (h : HasDerivWithinAt f f' t x) (hst : t ∈ 𝓝[s] x) :
    HasDerivWithinAt f f' s x :=
  HasFDerivWithinAt.mono_of_mem_nhdsWithin h hst
/-
**HasDerivAt.hasDerivAtFilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.hasDerivAtFilter (h : HasDerivAt f f' x) (hL : L <= 𝓝 x ×ˢ pure
 x) : HasDerivAtFilter f f' L
参数：h : HasDerivAt f f' x；hL : L <= 𝓝 x ×ˢ pure x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivAt.hasFDerivAtFilter`：HasFDerivAt.hasFDerivAtFilter (h : HasFDe
rivAt f f' x) (hL : L <= 𝓝 x ×ˢ pure x) : HasFDerivAtFilter f f' L
-/
theorem HasDerivAt.hasDerivAtFilter (h : HasDerivAt f f' x) (hL : L ≤ 𝓝 x ×ˢ pure x) :
    HasDerivAtFilter f f' L :=
  HasFDerivAt.hasFDerivAtFilter h hL
/-
**HasDerivAt.hasDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.hasDerivWithinAt (h : HasDerivAt f f' x) : HasDerivWithinAt f f
' s x
参数：h : HasDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivAt.hasFDerivWithinAt`：HasFDerivAt.hasFDerivWithinAt (h : HasFDe
rivAt f f' x) : HasFDerivWithinAt f f' s x
-/
theorem HasDerivAt.hasDerivWithinAt (h : HasDerivAt f f' x) : HasDerivWithinAt f f' s x :=
  HasFDerivAt.hasFDerivWithinAt h
/-
**HasDerivWithinAt.differentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.differentiableWithinAt (h : HasDerivWithinAt f f' s x) : 
DifferentiableWithinAt 𝕜 f s x
参数：h : HasDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
-/
theorem HasDerivWithinAt.differentiableWithinAt (h : HasDerivWithinAt f f' s x) :
    DifferentiableWithinAt 𝕜 f s x :=
  HasFDerivWithinAt.differentiableWithinAt h
/-
**HasDerivAt.differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.differentiableAt (h : HasDerivAt f f' x) : DifferentiableAt 𝕜 f
 x
参数：h : HasDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
-/
theorem HasDerivAt.differentiableAt (h : HasDerivAt f f' x) : DifferentiableAt 𝕜 f x :=
  HasFDerivAt.differentiableAt h

@[simp]
/-
**hasDerivWithinAt_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_univ : HasDerivWithinAt f f' univ x ↔ HasDerivAt f f' x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivWithinAt_univ`：hasFDerivWithinAt_univ : HasFDerivWithinAt f f' 
univ x ↔ HasFDerivAt f f' x
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem hasDerivWithinAt_univ : HasDerivWithinAt f f' univ x ↔ HasDerivAt f f' x :=
  hasFDerivWithinAt_univ
/-
**HasDerivAt.unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.unique (h₀ : HasDerivAt f f₀' x) (h₁ : HasDerivAt f f₁' x) : f₀
' = f₁'
参数：h₀ : HasDerivAt f f₀' x；h₁ : HasDerivAt f f₁' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ContinuousLinearMap.toSpanSingleton_inj`：∀ {R₁ : Type u_1} [inst : Semir
ing R₁] {M₂ : Type u_6} [inst_1 : TopologicalSpace M₂] [inst_2 : AddCommMonoid M
₂]   [inst_3 : _root_.Module …
· 使用定理 `HasFDerivAt.unique`：HasFDerivAt.unique (h₀ : HasFDerivAt f f' x) (h₁ : H
asFDerivAt f f₁' x) : f' = f₁'
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasDerivAt.hasFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
-/
theorem HasDerivAt.unique (h₀ : HasDerivAt f f₀' x) (h₁ : HasDerivAt f f₁' x) : f₀' = f₁' :=
  toSpanSingleton_inj.mp <| h₀.hasFDerivAt.unique h₁
/-
**hasDerivWithinAt_inter'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_inter' (h : t in 𝓝[s] x) : HasDerivWithinAt f f' (s inter
 t) x ↔ HasDerivWithinAt f f' s x
参数：h : t in 𝓝[s] x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivWithinAt_inter'`：hasFDerivWithinAt_inter' (h : t in 𝓝[s] x) : H
asFDerivWithinAt f f' (s inter t) x ↔ HasFDerivWithinAt f f' s x
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem hasDerivWithinAt_inter' (h : t ∈ 𝓝[s] x) :
    HasDerivWithinAt f f' (s ∩ t) x ↔ HasDerivWithinAt f f' s x :=
  hasFDerivWithinAt_inter' h
/-
**hasDerivWithinAt_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_inter (h : t in 𝓝 x) : HasDerivWithinAt f f' (s inter t) 
x ↔ HasDerivWithinAt f f' s x
参数：h : t in 𝓝 x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivWithinAt_inter`：hasFDerivWithinAt_inter (h : t in 𝓝 x) : HasFDe
rivWithinAt f f' (s inter t) x ↔ HasFDerivWithinAt f f' s x
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem hasDerivWithinAt_inter (h : t ∈ 𝓝 x) :
    HasDerivWithinAt f f' (s ∩ t) x ↔ HasDerivWithinAt f f' s x :=
  hasFDerivWithinAt_inter h
/-
**HasDerivWithinAt.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.union (hs : HasDerivWithinAt f f' s x) (ht : HasDerivWith
inAt f f' t x) : HasDerivWithinAt f f' (s union t) x
参数：hs : HasDerivWithinAt f f' s x；ht : HasDerivWithinAt f f' t x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.union`：HasFDerivWithinAt.union (hs : HasFDerivWithinAt
 f f' s x) (ht : HasFDerivWithinAt f f' t x) : HasFDerivWithinAt f f' (s union t
) x
· 使用定理 `HasDerivWithinAt.hasFDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
-/
theorem HasDerivWithinAt.union (hs : HasDerivWithinAt f f' s x) (ht : HasDerivWithinAt f f' t x) :
    HasDerivWithinAt f f' (s ∪ t) x :=
  hs.hasFDerivWithinAt.union ht.hasFDerivWithinAt
/-
**HasDerivWithinAt.hasDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.hasDerivAt (h : HasDerivWithinAt f f' s x) (hs : s in 𝓝 x
) : HasDerivAt f f' x
参数：h : HasDerivWithinAt f f' s x；hs : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.hasFDerivAt`：HasFDerivWithinAt.hasFDerivAt (h : HasFDe
rivWithinAt f f' s x) (hs : s in 𝓝 x) : HasFDerivAt f f' x
-/
theorem HasDerivWithinAt.hasDerivAt (h : HasDerivWithinAt f f' s x) (hs : s ∈ 𝓝 x) :
    HasDerivAt f f' x :=
  HasFDerivWithinAt.hasFDerivAt h hs
/-
**DifferentiableWithinAt.hasDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.hasDerivWithinAt (h : DifferentiableWithinAt 𝕜 f s 
x) : HasDerivWithinAt f (derivWithin f s x) s x
参数：h : DifferentiableWithinAt 𝕜 f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.hasDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.hasDerivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) :
    HasDerivWithinAt f (derivWithin f s x) s x :=
  h.hasFDerivWithinAt.hasDerivWithinAt
/-
**DifferentiableAt.hasDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.hasDerivAt (h : DifferentiableAt 𝕜 f x) : HasDerivAt f (d
eriv f x) x
参数：h : DifferentiableAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.hasDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.hasDerivAt (h : DifferentiableAt 𝕜 f x) : HasDerivAt f (deriv f x) x :=
  h.hasFDerivAt.hasDerivAt

@[simp]
/-
**hasDerivAt_deriv_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_deriv_iff : HasDerivAt f (deriv f x) x ↔ DifferentiableAt 𝕜 f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem hasDerivAt_deriv_iff : HasDerivAt f (deriv f x) x ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun h => h.differentiableAt, fun h => h.hasDerivAt⟩

@[simp]
/-
**hasDerivWithinAt_derivWithin_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_derivWithin_iff : HasDerivWithinAt f (derivWithin f s x) 
s x ↔ DifferentiableWithinAt 𝕜 f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.differentiableWithinAt`：HasDerivWithinAt.differentiable
WithinAt (h : HasDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
-/
theorem hasDerivWithinAt_derivWithin_iff :
    HasDerivWithinAt f (derivWithin f s x) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h => h.differentiableWithinAt, fun h => h.hasDerivWithinAt⟩
/-
**DifferentiableOn.hasDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.hasDerivAt (h : DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x) :
 HasDerivAt f (deriv f x) x
参数：h : DifferentiableOn 𝕜 f s；hs : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.hasDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `DifferentiableOn.hasFDerivAt`：DifferentiableOn.hasFDerivAt (h : Differen
tiableOn 𝕜 f s) (hs : s in 𝓝 x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableOn.hasDerivAt (h : DifferentiableOn 𝕜 f s) (hs : s ∈ 𝓝 x) :
    HasDerivAt f (deriv f x) x :=
  (h.hasFDerivAt hs).hasDerivAt
/-
**HasDerivAt.deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x = f'
参数：h : HasDerivAt f f' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.unique`：HasDerivAt.unique (h₀ : HasDerivAt f f₀' x) (h₁ : Has
DerivAt f f₁' x) : f₀' = f₁'
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
-/
theorem HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x = f' :=
  h.differentiableAt.hasDerivAt.unique h
/-
**deriv_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_eq {f' : 𝕜 -> F} (h : forall x, HasDerivAt f (f' x) x) : deriv f = f
'
参数：h : forall x, HasDerivAt f (f' x) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
-/
theorem deriv_eq {f' : 𝕜 → F} (h : ∀ x, HasDerivAt f (f' x) x) : deriv f = f' :=
  funext fun x => (h x).deriv
/-
**HasDerivWithinAt.derivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.derivWithin (h : HasDerivWithinAt f f' s x) (hxs : Unique
DiffWithinAt 𝕜 s x) : derivWithin f s x = f'
参数：h : HasDerivWithinAt f f' s x；hxs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `UniqueDiffWithinAt.eq_deriv`：UniqueDiffWithinAt.eq_deriv (s : Set 𝕜) (H 
: UniqueDiffWithinAt 𝕜 s x) (h : HasDerivWithinAt f f' s x) (h₁ : HasDerivWithin
At f f₁' s x) : f…
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
· 使用定理 `HasDerivWithinAt.differentiableWithinAt`：HasDerivWithinAt.differentiable
WithinAt (h : HasDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
-/
theorem HasDerivWithinAt.derivWithin (h : HasDerivWithinAt f f' s x)
    (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f' :=
  hxs.eq_deriv _ h.differentiableWithinAt.hasDerivWithinAt h
/-
**fderivWithin_derivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_derivWithin : (fderivWithin 𝕜 f s x : 𝕜 -> F) 1 = derivWithin
 f s x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fderivWithin_derivWithin : (fderivWithin 𝕜 f s x : 𝕜 → F) 1 = derivWithin f s x :=
  rfl
/-
**toSpanSingleton_derivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toSpanSingleton_derivWithin : toSpanSingleton 𝕜 (derivWithin f s x) = fder
ivWithin 𝕜 f s x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.toSpanSingleton_apply_map_one`：∀ (R₁ : Type u_1) [in
st : Semiring R₁] {M₂ : Type u_6} [inst_1 : TopologicalSpace M₂] [inst_2 : AddCo
mmMonoid M₂]   [inst_3 : _root_.Module …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toSpanSingleton_derivWithin :
    toSpanSingleton 𝕜 (derivWithin f s x) = fderivWithin 𝕜 f s x := by simp [derivWithin]
/-
**norm_derivWithin_eq_norm_fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_derivWithin_eq_norm_fderivWithin : ‖derivWithin f s x‖ = ‖fderivWithi
n 𝕜 f s x‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.norm_toSpanSingleton`：∀ {𝕜 : Type u_1} {E : Type u_4
} [inst : SeminormedAddCommGroup E] [inst_1 : NontriviallyNormedField 𝕜]   [inst
_2 : NormedSpace 𝕜 E] (x : E),…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_derivWithin_eq_norm_fderivWithin : ‖derivWithin f s x‖ = ‖fderivWithin 𝕜 f s x‖ := by
  simp [← toSpanSingleton_derivWithin]
/-
**fderiv_apply_one_eq_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_apply_one_eq_deriv : (fderiv 𝕜 f x : 𝕜 -> F) 1 = deriv f x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fderiv_apply_one_eq_deriv : (fderiv 𝕜 f x : 𝕜 → F) 1 = deriv f x := rfl

@[simp]
/-
**fderiv_eq_smul_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_eq_smul_deriv (y : 𝕜) : (fderiv 𝕜 f x : 𝕜 -> F) y = y • deriv f x
参数：y : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `fderiv_apply_one_eq_deriv`：fderiv_apply_one_eq_deriv : (fderiv 𝕜 f x : 𝕜
 -> F) 1 = deriv f x
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fderiv_eq_smul_deriv (y : 𝕜) : (fderiv 𝕜 f x : 𝕜 → F) y = y • deriv f x := by
  rw [← fderiv_apply_one_eq_deriv, ← map_smul]
  simp only [smul_eq_mul, mul_one]
/-
**toSpanSingleton_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toSpanSingleton_deriv : toSpanSingleton 𝕜 (deriv f x) = fderiv 𝕜 f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.toSpanSingleton_apply_map_one`：∀ (R₁ : Type u_1) [in
st : Semiring R₁] {M₂ : Type u_6} [inst_1 : TopologicalSpace M₂] [inst_2 : AddCo
mmMonoid M₂]   [inst_3 : _root_.Module …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toSpanSingleton_deriv : toSpanSingleton 𝕜 (deriv f x) = fderiv 𝕜 f x := by
  simp only [deriv, ContinuousLinearMap.toSpanSingleton_apply_map_one]
/-
**fderiv_eq_deriv_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：fderiv_eq_deriv_mul {f : 𝕜 -> 𝕜} {x y : 𝕜} : (fderiv 𝕜 f x : 𝕜 -> 𝕜) y = (
deriv f x) * y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderiv_eq_smul_deriv`：fderiv_eq_smul_deriv (y : 𝕜) : (fderiv 𝕜 f x : 𝕜 -
> F) y = y • deriv f x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fderiv_eq_deriv_mul {f : 𝕜 → 𝕜} {x y : 𝕜} : (fderiv 𝕜 f x : 𝕜 → 𝕜) y = (deriv f x) * y := by
  simp [mul_comm]
/-
**norm_deriv_eq_norm_fderiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_deriv_eq_norm_fderiv : ‖deriv f x‖ = ‖fderiv 𝕜 f x‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.norm_toSpanSingleton`：∀ {𝕜 : Type u_1} {E : Type u_4
} [inst : SeminormedAddCommGroup E] [inst_1 : NontriviallyNormedField 𝕜]   [inst
_2 : NormedSpace 𝕜 E] (x : E),…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_deriv_eq_norm_fderiv : ‖deriv f x‖ = ‖fderiv 𝕜 f x‖ := by
  simp [← toSpanSingleton_deriv]
/-
**DifferentiableAt.derivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.derivWithin (h : DifferentiableAt 𝕜 f x) (hxs : UniqueDif
fWithinAt 𝕜 s x) : derivWithin f s x = deriv f x
参数：h : DifferentiableAt 𝕜 f x；hxs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DifferentiableAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem DifferentiableAt.derivWithin (h : DifferentiableAt 𝕜 f x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin f s x = deriv f x := by
  unfold _root_.derivWithin deriv
  rw [h.fderivWithin hxs]
/-
**HasDerivWithinAt.deriv_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.deriv_eq_zero (hd : HasDerivWithinAt f 0 s x) (H : Unique
DiffWithinAt 𝕜 s x) : deriv f x = 0
参数：hd : HasDerivWithinAt f 0 s x；H : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `em'`：em' (p : Prop) : ¬p ∨ p
· 使用定理 `deriv_zero_of_not_differentiableAt`：deriv_zero_of_not_differentiableAt (
h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0
· 使用定理 `UniqueDiffWithinAt.eq_deriv`：UniqueDiffWithinAt.eq_deriv (s : Set 𝕜) (H 
: UniqueDiffWithinAt 𝕜 s x) (h : HasDerivWithinAt f f' s x) (h₁ : HasDerivWithin
At f f₁' s x) : f…
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem HasDerivWithinAt.deriv_eq_zero (hd : HasDerivWithinAt f 0 s x)
    (H : UniqueDiffWithinAt 𝕜 s x) : deriv f x = 0 :=
  (em' (DifferentiableAt 𝕜 f x)).elim deriv_zero_of_not_differentiableAt fun h =>
    H.eq_deriv _ h.hasDerivAt.hasDerivWithinAt hd
/-
**derivWithin_of_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_of_mem_nhdsWithin (st : t in 𝓝[s] x) (ht : UniqueDiffWithinAt 
𝕜 s x) (h : DifferentiableWithinAt 𝕜 f t x) : derivWithin f s x = derivWithin f 
t x
参数：st : t in 𝓝[s] x；ht : UniqueDiffWithinAt 𝕜 s x；h : DifferentiableWithinAt 𝕜 f
 t x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.mono_of_mem_nhdsWithin`：HasDerivWithinAt.mono_of_mem_nh
dsWithin (h : HasDerivWithinAt f f' t x) (hst : t in 𝓝[s] x) : HasDerivWithinAt 
f f' s x
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
-/
theorem derivWithin_of_mem_nhdsWithin (st : t ∈ 𝓝[s] x) (ht : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f t x) : derivWithin f s x = derivWithin f t x :=
  ((DifferentiableWithinAt.hasDerivWithinAt h).mono_of_mem_nhdsWithin st).derivWithin ht
/-
**derivWithin_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_subset (st : s subseteq t) (ht : UniqueDiffWithinAt 𝕜 s x) (h 
: DifferentiableWithinAt 𝕜 f t x) : derivWithin f s x = derivWithin f t x
参数：st : s subseteq t；ht : UniqueDiffWithinAt 𝕜 s x；h : DifferentiableWithinAt 𝕜 
f t x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.mono`：HasDerivWithinAt.mono (h : HasDerivWithinAt f f' 
t x) (hst : s subseteq t) : HasDerivWithinAt f f' s x
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
-/
theorem derivWithin_subset (st : s ⊆ t) (ht : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f t x) : derivWithin f s x = derivWithin f t x :=
  ((DifferentiableWithinAt.hasDerivWithinAt h).mono st).derivWithin ht
/-
**derivWithin_congr_set'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_congr_set' (y : 𝕜) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : derivWithin f s x
 = derivWithin f t x
参数：y : 𝕜；h : s =ᶠ[𝓝[{y}ᶜ] x] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_congr_set'`：fderivWithin_congr_set' [T1Space E] (y : E) (h 
: s =ᶠ[𝓝[{y}ᶜ] x] t) : fderivWithin 𝕜 f s x = fderivWithin 𝕜 f t x
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem derivWithin_congr_set' (y : 𝕜) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    derivWithin f s x = derivWithin f t x := by simp only [derivWithin, fderivWithin_congr_set' y h]
/-
**derivWithin_congr_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_congr_set (h : s =ᶠ[𝓝 x] t) : derivWithin f s x = derivWithin 
f t x
参数：h : s =ᶠ[𝓝 x] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_congr_set`：fderivWithin_congr_set (h : s =ᶠ[𝓝 x] t) : fderi
vWithin 𝕜 f s x = fderivWithin 𝕜 f t x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem derivWithin_congr_set (h : s =ᶠ[𝓝 x] t) : derivWithin f s x = derivWithin f t x := by
  simp only [derivWithin, fderivWithin_congr_set h]

@[simp]
/-
**derivWithin_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_univ : derivWithin f univ = deriv f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_univ`：fderivWithin_univ : fderivWithin 𝕜 f univ = fderiv 𝕜 
f
-/
theorem derivWithin_univ : derivWithin f univ = deriv f := by
  ext
  unfold derivWithin deriv
  rw [fderivWithin_univ]
/-
**derivWithin_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_inter (ht : t in 𝓝 x) : derivWithin f (s inter t) x = derivWit
hin f s x
参数：ht : t in 𝓝 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_inter`：fderivWithin_inter (ht : t in 𝓝 x) : fderivWithin 𝕜 
f (s inter t) x = fderivWithin 𝕜 f s x
-/
theorem derivWithin_inter (ht : t ∈ 𝓝 x) : derivWithin f (s ∩ t) x = derivWithin f s x := by
  unfold derivWithin
  rw [fderivWithin_inter ht]
/-
**derivWithin_of_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_of_mem_nhds (h : s in 𝓝 x) : derivWithin f s x = deriv f x
参数：h : s in 𝓝 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_of_mem_nhds`：fderivWithin_of_mem_nhds (h : s in 𝓝 x) : fder
ivWithin 𝕜 f s x = fderiv 𝕜 f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem derivWithin_of_mem_nhds (h : s ∈ 𝓝 x) : derivWithin f s x = deriv f x := by
  simp only [derivWithin, deriv, fderivWithin_of_mem_nhds h]
/-
**derivWithin_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_of_isOpen (hs : IsOpen s) (hx : x in s) : derivWithin f s x = 
deriv f x
参数：hs : IsOpen s；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `derivWithin_of_mem_nhds`：derivWithin_of_mem_nhds (h : s in 𝓝 x) : derivW
ithin f s x = deriv f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
theorem derivWithin_of_isOpen (hs : IsOpen s) (hx : x ∈ s) : derivWithin f s x = deriv f x :=
  derivWithin_of_mem_nhds (hs.mem_nhds hx)
/-
**deriv_eqOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：deriv_eqOn {f' : 𝕜 -> F} (hs : IsOpen s) (hf' : forall x in s, HasDerivWit
hinAt f (f' x) s x) : s.EqOn (deriv f) f'
参数：hs : IsOpen s；hf' : forall x in s, HasDerivWithinAt f (f' x) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `derivWithin_of_isOpen`：derivWithin_of_isOpen (hs : IsOpen s) (hx : x in 
s) : derivWithin f s x = deriv f x
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `IsOpen.uniqueDiffWithinAt`：IsOpen.uniqueDiffWithinAt (hs : IsOpen s) (xs
 : x in s) : UniqueDiffWithinAt 𝕜 s x
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
-/
lemma deriv_eqOn {f' : 𝕜 → F} (hs : IsOpen s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) :
    s.EqOn (deriv f) f' := fun x hx ↦ by
  rw [← derivWithin_of_isOpen hs hx, (hf' _ hx).derivWithin <| hs.uniqueDiffWithinAt hx]
/-
**deriv_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_mem_iff {f : 𝕜 -> F} {s : Set F} {x : 𝕜} : deriv f x in s ↔ Differen
tiableAt 𝕜 f x ∧ deriv f x in s ∨ ¬DifferentiableAt 𝕜 f x ∧ (0 : F) in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `deriv_zero_of_not_differentiableAt`：deriv_zero_of_not_differentiableAt (
h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem deriv_mem_iff {f : 𝕜 → F} {s : Set F} {x : 𝕜} :
    deriv f x ∈ s ↔
      DifferentiableAt 𝕜 f x ∧ deriv f x ∈ s ∨ ¬DifferentiableAt 𝕜 f x ∧ (0 : F) ∈ s := by
  by_cases hx : DifferentiableAt 𝕜 f x <;> simp [deriv_zero_of_not_differentiableAt, *]
/-
**derivWithin_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_mem_iff {f : 𝕜 -> F} {t : Set 𝕜} {s : Set F} {x : 𝕜} : derivWi
thin f t x in s ↔ DifferentiableWithinAt 𝕜 f t x ∧ derivWithin f t x in s ∨ ¬Dif
ferentiableWithinAt 𝕜 f t x ∧ (0 : F) in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `derivWithin_zero_of_not_differentiableWithinAt`：derivWithin_zero_of_not_
differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) : derivWithin f s x
 = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem derivWithin_mem_iff {f : 𝕜 → F} {t : Set 𝕜} {s : Set F} {x : 𝕜} :
    derivWithin f t x ∈ s ↔
      DifferentiableWithinAt 𝕜 f t x ∧ derivWithin f t x ∈ s ∨
        ¬DifferentiableWithinAt 𝕜 f t x ∧ (0 : F) ∈ s := by
  by_cases hx : DifferentiableWithinAt 𝕜 f t x <;>
    simp [derivWithin_zero_of_not_differentiableWithinAt, *]
/-
**differentiableWithinAt_Ioi_iff_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_Ioi_iff_Ici [PartialOrder 𝕜] : DifferentiableWithin
At 𝕜 f (Ioi x) x ↔ DifferentiableWithinAt 𝕜 f (Ici x) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.differentiableWithinAt`：HasDerivWithinAt.differentiable
WithinAt (h : HasDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasDerivWithinAt.Ici_of_Ioi`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F]
 {f : 𝕜 → F} {f' …
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
· 使用定理 `HasDerivWithinAt.Ioi_of_Ici`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F]
 {f : 𝕜 → F} {f' …
-/
theorem differentiableWithinAt_Ioi_iff_Ici [PartialOrder 𝕜] :
    DifferentiableWithinAt 𝕜 f (Ioi x) x ↔ DifferentiableWithinAt 𝕜 f (Ici x) x :=
  ⟨fun h => h.hasDerivWithinAt.Ici_of_Ioi.differentiableWithinAt, fun h =>
    h.hasDerivWithinAt.Ioi_of_Ici.differentiableWithinAt⟩

-- Golfed while splitting the file
/-
**derivWithin_Ioi_eq_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_Ioi_eq_Ici {E : Type*} [NormedAddCommGroup E] [NormedSpace Rea
l E] (f : Real -> E) (x : Real) : derivWithin f (Ioi x) x = derivWithin f (Ici x
) x
参数：f : Real -> E；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.Ici_of_Ioi`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F]
 {f : 𝕜 → F} {f' …
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `differentiableWithinAt_Ioi_iff_Ici`：differentiableWithinAt_Ioi_iff_Ici [
PartialOrder 𝕜] : DifferentiableWithinAt 𝕜 f (Ioi x) x ↔ DifferentiableWithinAt 
𝕜 f (Ici x) x
· 使用定理 `UniqueDiffOn.eq`：UniqueDiffOn.eq (H : UniqueDiffOn 𝕜 s) (hx : x in s) (h
 : HasFDerivWithinAt f f' s x) (h₁ : HasFDerivWithinAt f f₁' s x) : f' = f₁'
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
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `uniqueDiffOn_Ici`：uniqueDiffOn_Ici (a : Real) : UniqueDiffOn Real (Ici a
)
· 使用定理 `Set.self_mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Ici a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `derivWithin_zero_of_not_differentiableWithinAt`：derivWithin_zero_of_not_
differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) : derivWithin f s x
 = 0
-/
theorem derivWithin_Ioi_eq_Ici {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E)
    (x : ℝ) : derivWithin f (Ioi x) x = derivWithin f (Ici x) x := by
  by_cases H : DifferentiableWithinAt ℝ f (Ioi x) x
  · have A := H.hasDerivWithinAt.Ici_of_Ioi
    have B := (differentiableWithinAt_Ioi_iff_Ici.1 H).hasDerivWithinAt
    simpa using (uniqueDiffOn_Ici x).eq self_mem_Ici A B
  · rw [derivWithin_zero_of_not_differentiableWithinAt H,
      derivWithin_zero_of_not_differentiableWithinAt]
    rwa [differentiableWithinAt_Ioi_iff_Ici] at H

section congr

/-! ### Congruence properties of derivatives -/

/-
**Filter.EventuallyEq.hasDerivAtFilter_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.hasDerivAtFilter_iff (h₀ : Prod.map f₀ f₀ =ᶠ[L] Prod.m
ap f₁ f₁) (h₁ : f₀' = f₁') : HasDerivAtFilter f₀ f₀' L ↔ HasDerivAtFilter f₁ f₁'
 L
参数：h₀ : Prod.map f₀ f₀ =ᶠ[L] Prod.map f₁ f₁；h₁ : f₀' = f₁'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.hasFDerivAtFilter_iff`：Filter.EventuallyEq.hasFDeriv
AtFilter_iff (h₀ : Prod.map f₀ f₀ =ᶠ[L] Prod.map f₁ f₁) (h₁ : forall x, f₀' x = 
f₁' x) : HasFDerivAtFilter f₀ f…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.toSpanSingleton.congr_simp`：∀ (R₁ : Type u_1) [inst 
: Semiring R₁] {M₁ : Type u_4} [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommM
onoid M₁]   [inst_3 : _root_.Module …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
### Congruence properties of derivatives
-/
theorem Filter.EventuallyEq.hasDerivAtFilter_iff (h₀ : Prod.map f₀ f₀ =ᶠ[L] Prod.map f₁ f₁)
    (h₁ : f₀' = f₁') : HasDerivAtFilter f₀ f₀' L ↔ HasDerivAtFilter f₁ f₁' L :=
  h₀.hasFDerivAtFilter_iff (by simp [h₁])
/-
**HasDerivAtFilter.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAtFilter.congr_of_eventuallyEq (h : HasDerivAtFilter f f' L) (hL :
 Prod.map f₁ f₁ =ᶠ[L] Prod.map f f) : HasDerivAtFilter f₁ f' L
参数：h : HasDerivAtFilter f f' L；hL : Prod.map f₁ f₁ =ᶠ[L] Prod.map f f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyEq.hasDerivAtFilter_iff`：Filter.EventuallyEq.hasDerivAt
Filter_iff (h₀ : Prod.map f₀ f₀ =ᶠ[L] Prod.map f₁ f₁) (h₁ : f₀' = f₁') : HasDeri
vAtFilter f₀ f₀' L ↔ HasDerivA…
-/
theorem HasDerivAtFilter.congr_of_eventuallyEq (h : HasDerivAtFilter f f' L)
    (hL : Prod.map f₁ f₁ =ᶠ[L] Prod.map f f) :
    HasDerivAtFilter f₁ f' L := by
  rwa [hL.hasDerivAtFilter_iff rfl]
/-
**HasDerivWithinAt.congr_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.congr_mono (h : HasDerivWithinAt f f' s x) (ht : forall x
 in t, f₁ x = f x) (hx : f₁ x = f x) (h₁ : t subseteq s) : HasDerivWithinAt f₁ f
' t x
参数：h : HasDerivWithinAt f f' s x；ht : forall x in t, f₁ x = f x；hx : f₁ x = f x；
h₁ : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.congr_mono`：HasFDerivWithinAt.congr_mono (h : HasFDeri
vWithinAt f f' s x) (ht : EqOn f₁ f t) (hx : f₁ x = f x) (h₁ : t subseteq s) : H
asFDerivWithinAt f…
-/
theorem HasDerivWithinAt.congr_mono (h : HasDerivWithinAt f f' s x) (ht : ∀ x ∈ t, f₁ x = f x)
    (hx : f₁ x = f x) (h₁ : t ⊆ s) : HasDerivWithinAt f₁ f' t x :=
  HasFDerivWithinAt.congr_mono h ht hx h₁
/-
**HasDerivWithinAt.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.congr (h : HasDerivWithinAt f f' s x) (hs : forall x in s
, f₁ x = f x) (hx : f₁ x = f x) : HasDerivWithinAt f₁ f' s x
参数：h : HasDerivWithinAt f f' s x；hs : forall x in s, f₁ x = f x；hx : f₁ x = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.congr_mono`：HasDerivWithinAt.congr_mono (h : HasDerivWi
thinAt f f' s x) (ht : forall x in t, f₁ x = f x) (hx : f₁ x = f x) (h₁ : t subs
eteq s) : HasDeri…
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
-/
theorem HasDerivWithinAt.congr (h : HasDerivWithinAt f f' s x) (hs : ∀ x ∈ s, f₁ x = f x)
    (hx : f₁ x = f x) : HasDerivWithinAt f₁ f' s x :=
  h.congr_mono hs hx (Subset.refl _)
/-
**HasDerivWithinAt.congr_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.congr_of_mem (h : HasDerivWithinAt f f' s x) (hs : forall
 x in s, f₁ x = f x) (hx : x in s) : HasDerivWithinAt f₁ f' s x
参数：h : HasDerivWithinAt f f' s x；hs : forall x in s, f₁ x = f x；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.congr`：HasDerivWithinAt.congr (h : HasDerivWithinAt f f
' s x) (hs : forall x in s, f₁ x = f x) (hx : f₁ x = f x) : HasDerivWithinAt f₁ 
f' s x
-/
theorem HasDerivWithinAt.congr_of_mem (h : HasDerivWithinAt f f' s x) (hs : ∀ x ∈ s, f₁ x = f x)
    (hx : x ∈ s) : HasDerivWithinAt f₁ f' s x :=
  h.congr hs (hs _ hx)
/-
**HasDerivWithinAt.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.congr_of_eventuallyEq (h : HasDerivWithinAt f f' s x) (h₁
 : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasDerivWithinAt f₁ f' s x
参数：h : HasDerivWithinAt f f' s x；h₁ : f₁ =ᶠ[𝓝[s] x] f；hx : f₁ x = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.congr_of_eventuallyEq`：HasDerivAtFilter.congr_of_eventu
allyEq (h : HasDerivAtFilter f f' L) (hL : Prod.map f₁ f₁ =ᶠ[L] Prod.map f f) : 
HasDerivAtFilter f₁ f' L
· 使用定理 `Filter.EventuallyEq.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u
_3} {δ : Type u_6} {la : Filter α} {fa ga : α → γ},   fa =ᶠ[la] ga → ∀ {lb : Fil
ter β} {fb gb : β…
-/
theorem HasDerivWithinAt.congr_of_eventuallyEq (h : HasDerivWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasDerivWithinAt f₁ f' s x :=
  HasDerivAtFilter.congr_of_eventuallyEq h <| h₁.prodMap hx
/-
**Filter.EventuallyEq.hasDerivWithinAt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.hasDerivWithinAt_iff (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x
 = f x) : HasDerivWithinAt f₁ f' s x ↔ HasDerivWithinAt f f' s x
参数：h₁ : f₁ =ᶠ[𝓝[s] x] f；hx : f₁ x = f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.congr_of_eventuallyEq`：HasDerivWithinAt.congr_of_eventu
allyEq (h : HasDerivWithinAt f f' s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) 
: HasDerivWithinAt f₁ f' s x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Filter.EventuallyEq.hasDerivWithinAt_iff (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    HasDerivWithinAt f₁ f' s x ↔ HasDerivWithinAt f f' s x :=
  ⟨fun h' ↦ h'.congr_of_eventuallyEq h₁.symm hx.symm, fun h' ↦ h'.congr_of_eventuallyEq h₁ hx⟩
/-
**HasDerivWithinAt.congr_of_eventuallyEq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.congr_of_eventuallyEq_of_mem (h : HasDerivWithinAt f f' s
 x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x in s) : HasDerivWithinAt f₁ f' s x
参数：h : HasDerivWithinAt f f' s x；h₁ : f₁ =ᶠ[𝓝[s] x] f；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.congr_of_eventuallyEq`：HasDerivWithinAt.congr_of_eventu
allyEq (h : HasDerivWithinAt f f' s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) 
: HasDerivWithinAt f₁ f' s x
· 使用定理 `Filter.EventuallyEq.eq_of_nhdsWithin`：Filter.EventuallyEq.eq_of_nhdsWith
in {s : Set α} {f g : α -> β} {a : α} (h : f =ᶠ[𝓝[s] a] g) (hmem : a in s) : f a
 = g a
-/
theorem HasDerivWithinAt.congr_of_eventuallyEq_of_mem (h : HasDerivWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) : HasDerivWithinAt f₁ f' s x :=
  h.congr_of_eventuallyEq h₁ (h₁.eq_of_nhdsWithin hx)
/-
**Filter.EventuallyEq.hasDerivWithinAt_iff_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.hasDerivWithinAt_iff_of_mem (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx
 : x in s) : HasDerivWithinAt f₁ f' s x ↔ HasDerivWithinAt f f' s x
参数：h₁ : f₁ =ᶠ[𝓝[s] x] f；hx : x in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.congr_of_eventuallyEq_of_mem`：HasDerivWithinAt.congr_of
_eventuallyEq_of_mem (h : HasDerivWithinAt f f' s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx 
: x in s) : HasDerivWithinAt f₁ f' …
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem Filter.EventuallyEq.hasDerivWithinAt_iff_of_mem (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) :
    HasDerivWithinAt f₁ f' s x ↔ HasDerivWithinAt f f' s x :=
  ⟨fun h' ↦ h'.congr_of_eventuallyEq_of_mem h₁.symm hx,
  fun h' ↦ h'.congr_of_eventuallyEq_of_mem h₁ hx⟩

/-- If `f` has derivative `f'` in the strict sense and `f x' = f₁ x'` near `x`,
then `f₁` has the same derivative in the strict sense.

Note that this lemma assumes `f =ᶠ[𝓝 x] f₁`, while other lemmas in this file assume `f₁ =ᶠ[𝓝 x] f`.
This is done for backward compatibility, and may change in the future.
See [Zulip discussion](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/MyProp.2Econgr_*.20lemmas.2C.20LHS.20vs.20RHS/with/572593573).
-/
/-
**HasStrictDerivAt.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.congr_of_eventuallyEq (h : HasStrictDerivAt f f' x) (h₁ :
 f =ᶠ[𝓝 x] f₁) : HasStrictDerivAt f₁ f' x
参数：h : HasStrictDerivAt f f' x；h₁ : f =ᶠ[𝓝 x] f₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.congr_of_eventuallyEq`：HasDerivAtFilter.congr_of_eventu
allyEq (h : HasDerivAtFilter f f' L) (hL : Prod.map f₁ f₁ =ᶠ[L] Prod.map f f) : 
HasDerivAtFilter f₁ f' L
· 使用定理 `Filter.EventuallyEq.prodMap_nhds`：Filter.EventuallyEq.prodMap_nhds {α β 
: Type*} {f₁ f₂ : X -> α} {g₁ g₂ : Y -> β} {x : X} {y : Y} (hf : f₁ =ᶠ[𝓝 x] f₂) 
(hg : g₁ =ᶠ[𝓝 y] g₂) :…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f

--- 原说明 ---
If `f` has derivative `f'` in the strict sense and `f x' = f₁ x'` near `x`,
then `f₁` has the same derivative in the strict sense.

Note that this lemma assumes `f =ᶠ[𝓝 x] f₁`, while other lemmas in this file ass
ume `f₁ =ᶠ[𝓝 x] f`.
This is done for backward compatibility, and may change in the future.
See [Zulip discussion](https://leanprover.zulipchat.com/#narrow/channel/287929-m
athlib4/topic/MyProp.2Econgr_*.20lemmas.2C.20LHS.20vs.20RHS/with/572593573).
-/
theorem HasStrictDerivAt.congr_of_eventuallyEq (h : HasStrictDerivAt f f' x) (h₁ : f =ᶠ[𝓝 x] f₁) :
    HasStrictDerivAt f₁ f' x :=
  HasDerivAtFilter.congr_of_eventuallyEq h (h₁.symm.prodMap_nhds h₁.symm)
/-
**HasStrictDerivAt.congr_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.congr_deriv (h : HasStrictDerivAt f f' x) (h' : f' = g') 
: HasStrictDerivAt f g' x
参数：h : HasStrictDerivAt f f' x；h' : f' = g'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasStrictFDerivAt.congr_fderiv`：HasStrictFDerivAt.congr_fderiv (h : HasS
trictFDerivAt f f' x) (h' : f' = g') : HasStrictFDerivAt f g' x
· 使用定理 `HasStrictDerivAt.hasStrictFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem HasStrictDerivAt.congr_deriv (h : HasStrictDerivAt f f' x) (h' : f' = g') :
    HasStrictDerivAt f g' x :=
  h.hasStrictFDerivAt.congr_fderiv <| congr_arg _ h'
/-
**HasDerivAt.congr_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.congr_deriv (h : HasDerivAt f f' x) (h' : f' = g') : HasDerivAt
 f g' x
参数：h : HasDerivAt f f' x；h' : f' = g'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivAt.congr_fderiv`：HasFDerivAt.congr_fderiv (h : HasFDerivAt f f'
 x) (h' : f' = g') : HasFDerivAt f g' x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem HasDerivAt.congr_deriv (h : HasDerivAt f f' x) (h' : f' = g') : HasDerivAt f g' x :=
  HasFDerivAt.congr_fderiv h <| congr_arg _ h'
/-
**HasDerivWithinAt.congr_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.congr_deriv (h : HasDerivWithinAt f f' s x) (h' : f' = g'
) : HasDerivWithinAt f g' s x
参数：h : HasDerivWithinAt f f' s x；h' : f' = g'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.congr_fderiv`：HasFDerivWithinAt.congr_fderiv (h : HasF
DerivWithinAt f f' s x) (h' : f' = g') : HasFDerivWithinAt f g' s x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem HasDerivWithinAt.congr_deriv (h : HasDerivWithinAt f f' s x) (h' : f' = g') :
    HasDerivWithinAt f g' s x :=
  HasFDerivWithinAt.congr_fderiv h <| congr_arg _ h'
/-
**HasDerivAt.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.congr_of_eventuallyEq (h : HasDerivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] 
f) : HasDerivAt f₁ f' x
参数：h : HasDerivAt f f' x；h₁ : f₁ =ᶠ[𝓝 x] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.congr_of_eventuallyEq`：HasDerivAtFilter.congr_of_eventu
allyEq (h : HasDerivAtFilter f f' L) (hL : Prod.map f₁ f₁ =ᶠ[L] Prod.map f f) : 
HasDerivAtFilter f₁ f' L
· 使用定理 `Filter.EventuallyEq.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u
_3} {δ : Type u_6} {la : Filter α} {fa ga : α → γ},   fa =ᶠ[la] ga → ∀ {lb : Fil
ter β} {fb gb : β…
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
-/
theorem HasDerivAt.congr_of_eventuallyEq (h : HasDerivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
    HasDerivAt f₁ f' x :=
  HasDerivAtFilter.congr_of_eventuallyEq h <| h₁.prodMap <| h₁.filter_mono <| pure_le_nhds _
/-
**Filter.EventuallyEq.hasDerivAt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.hasDerivAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) : HasDerivAt f₀ f' 
x ↔ HasDerivAt f₁ f' x
参数：h : f₀ =ᶠ[𝓝 x] f₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.congr_of_eventuallyEq`：HasDerivAt.congr_of_eventuallyEq (h : 
HasDerivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) : HasDerivAt f₁ f' x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem Filter.EventuallyEq.hasDerivAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) :
    HasDerivAt f₀ f' x ↔ HasDerivAt f₁ f' x :=
  ⟨fun h' ↦ h'.congr_of_eventuallyEq h.symm, fun h' ↦ h'.congr_of_eventuallyEq h⟩
/-
**Filter.EventuallyEq.derivWithin_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.derivWithin_eq (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x
) : derivWithin f₁ s x = derivWithin f s x
参数：hs : f₁ =ᶠ[𝓝[s] x] f；hx : f₁ x = f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyEq.fderivWithin_eq`：Filter.EventuallyEq.fderivWithin_eq
 (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : fderivWithin 𝕜 f₁ s x = fderivWithin
 𝕜 f s x
-/
theorem Filter.EventuallyEq.derivWithin_eq (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    derivWithin f₁ s x = derivWithin f s x := by
  unfold derivWithin
  rw [hs.fderivWithin_eq hx]
/-
**Filter.EventuallyEq.derivWithin_eq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.derivWithin_eq_of_mem (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : x i
n s) : derivWithin f₁ s x = derivWithin f s x
参数：hs : f₁ =ᶠ[𝓝[s] x] f；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.derivWithin_eq`：Filter.EventuallyEq.derivWithin_eq (
hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : derivWithin f₁ s x = derivWithin f s x
· 使用定理 `Filter.Eventually.self_of_nhdsWithin`：Filter.Eventually.self_of_nhdsWith
in {p : α -> Prop} {s : Set α} {x : α} (h : forallᶠ y in 𝓝[s] x, p y) (hx : x in
 s) : p x
-/
theorem Filter.EventuallyEq.derivWithin_eq_of_mem (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) :
    derivWithin f₁ s x = derivWithin f s x :=
  hs.derivWithin_eq <| hs.self_of_nhdsWithin hx
/-
**Filter.EventuallyEq.derivWithin_eq_of_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.derivWithin_eq_of_nhds (hs : f₁ =ᶠ[𝓝 x] f) : derivWith
in f₁ s x = derivWithin f s x
参数：hs : f₁ =ᶠ[𝓝 x] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.derivWithin_eq`：Filter.EventuallyEq.derivWithin_eq (
hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : derivWithin f₁ s x = derivWithin f s x
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Filter.Eventually.self_of_nhds`：Filter.Eventually.self_of_nhds {p : X ->
 Prop} (h : forallᶠ y in 𝓝 x, p y) : p x
-/
theorem Filter.EventuallyEq.derivWithin_eq_of_nhds (hs : f₁ =ᶠ[𝓝 x] f) :
    derivWithin f₁ s x = derivWithin f s x :=
  (hs.filter_mono nhdsWithin_le_nhds).derivWithin_eq hs.self_of_nhds
/-
**derivWithin_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_congr (hs : EqOn f₁ f s) (hx : f₁ x = f x) : derivWithin f₁ s 
x = derivWithin f s x
参数：hs : EqOn f₁ f s；hx : f₁ x = f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_congr`：fderivWithin_congr (hs : EqOn f₁ f s) (hx : f₁ x = f
 x) : fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x
-/
theorem derivWithin_congr (hs : EqOn f₁ f s) (hx : f₁ x = f x) :
    derivWithin f₁ s x = derivWithin f s x := by
  unfold derivWithin
  rw [fderivWithin_congr hs hx]
/-
**Set.EqOn.deriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.EqOn.deriv {f g : 𝕜 -> F} {s : Set 𝕜} (hfg : s.EqOn f g) (hs : IsOpen 
s) : s.EqOn (deriv f) (deriv g)
参数：hfg : s.EqOn f g；hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `derivWithin_of_isOpen`：derivWithin_of_isOpen (hs : IsOpen s) (hx : x in 
s) : derivWithin f s x = deriv f x
· 使用定理 `derivWithin_congr`：derivWithin_congr (hs : EqOn f₁ f s) (hx : f₁ x = f x
) : derivWithin f₁ s x = derivWithin f s x
-/
lemma Set.EqOn.deriv {f g : 𝕜 → F} {s : Set 𝕜} (hfg : s.EqOn f g) (hs : IsOpen s) :
    s.EqOn (deriv f) (deriv g) := by
  intro x hx
  rw [← derivWithin_of_isOpen hs hx, ← derivWithin_of_isOpen hs hx]
  exact derivWithin_congr hfg (hfg hx)
/-
**Filter.EventuallyEq.deriv_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.deriv_eq (hL : f₁ =ᶠ[𝓝 x] f) : deriv f₁ x = deriv f x
参数：hL : f₁ =ᶠ[𝓝 x] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyEq.fderiv_eq`：Filter.EventuallyEq.fderiv_eq (h : f₁ =ᶠ[
𝓝 x] f) : fderiv 𝕜 f₁ x = fderiv 𝕜 f x
-/
theorem Filter.EventuallyEq.deriv_eq (hL : f₁ =ᶠ[𝓝 x] f) : deriv f₁ x = deriv f x := by
  unfold deriv
  rwa [Filter.EventuallyEq.fderiv_eq]
/-
**Filter.EventuallyEq.derivWithin'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.derivWithin' (h : f₁ =ᶠ[𝓝[s] x] f) (ht : t subseteq s)
 : derivWithin f₁ t =ᶠ[𝓝[s] x] derivWithin f t
参数：h : f₁ =ᶠ[𝓝[s] x] f；ht : t subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
· 使用定理 `Filter.EventuallyEq.fderivWithin'`：Filter.EventuallyEq.fderivWithin' (hs
 : f₁ =ᶠ[𝓝[s] x] f) (ht : t subseteq s) : fderivWithin 𝕜 f₁ t =ᶠ[𝓝[s] x] fderivW
ithin 𝕜 f t
-/
lemma Filter.EventuallyEq.derivWithin' (h : f₁ =ᶠ[𝓝[s] x] f) (ht : t ⊆ s) :
    derivWithin f₁ t =ᶠ[𝓝[s] x] derivWithin f t := by
  unfold derivWithin
  exact h.fderivWithin' ht |>.fun_comp (fun a ↦ a 1)
/-
**Filter.EventuallyEq.derivWithin** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq
`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F : Type v} [inst_1 : N
ormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f f₁ : 𝕜 → F} {x : 𝕜} {s : Se
t 𝕜},   f₁ =ᶠ[nhdsWithin x s] f → derivWithin f₁ s =ᶠ[nhdsWithin x s] derivWithi
n f s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.EventuallyEq.derivWithin'`：Filter.EventuallyEq.derivWithin' (h : 
f₁ =ᶠ[𝓝[s] x] f) (ht : t subseteq s) : derivWithin f₁ t =ᶠ[𝓝[s] x] derivWithin f
 t
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
protected lemma Filter.EventuallyEq.derivWithin (h : f₁ =ᶠ[𝓝[s] x] f) :
    derivWithin f₁ s =ᶠ[𝓝[s] x] derivWithin f s := h.derivWithin' Subset.rfl
/-
**Filter.EventuallyEq.deriv** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F : Type v} [inst_1 : N
ormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f f₁ : 𝕜 → F} {x : 𝕜}, f₁ =ᶠ[
nhds x] f → deriv f₁ =ᶠ[nhds x] deriv f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.EventuallyEq.eventuallyEq_nhds`：Filter.EventuallyEq.eventuallyEq_
nhds {f g : X -> α} (h : f =ᶠ[𝓝 x] g) : forallᶠ y in 𝓝 x, f =ᶠ[𝓝 y] g
· 使用定理 `Filter.EventuallyEq.deriv_eq`：Filter.EventuallyEq.deriv_eq (hL : f₁ =ᶠ[𝓝
 x] f) : deriv f₁ x = deriv f x
-/
protected theorem Filter.EventuallyEq.deriv (h : f₁ =ᶠ[𝓝 x] f) : deriv f₁ =ᶠ[𝓝 x] deriv f :=
  h.eventuallyEq_nhds.mono fun _ h => h.deriv_eq
/-
**Filter.EventuallyEq.nhdsNE_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.nhdsNE_deriv (h : f₁ =ᶠ[𝓝[!=] x] f) : deriv f₁ =ᶠ[𝓝[!=
] x] deriv f
参数：h : f₁ =ᶠ[𝓝[!=] x] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eventually_nhdsNE_eventually_nhds_iff`：eventually_nhdsNE_eventually_nhds
_iff [T1Space X] {a : X} {p : X -> Prop} : (forallᶠ y in 𝓝[!=] a, forallᶠ x in 𝓝
 y, p x) ↔ forallᶠ x in 𝓝[!…
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.EventuallyEq.deriv`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFiel
d 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {
f f₁ : 𝕜 → F} {…
-/
theorem Filter.EventuallyEq.nhdsNE_deriv (h : f₁ =ᶠ[𝓝[≠] x] f) : deriv f₁ =ᶠ[𝓝[≠] x] deriv f := by
  rw [Filter.EventuallyEq, ← eventually_nhdsNE_eventually_nhds_iff] at *
  filter_upwards [h] with y hy
  apply Filter.EventuallyEq.deriv hy

end congr

section id

/-! ### Derivative of the identity -/

variable (s x L)

/-
**hasDerivAtFilter_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAtFilter_id : HasDerivAtFilter id 1 L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.hasDerivAtFilter`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `hasFDerivAtFilter_id`：hasFDerivAtFilter_id (L : Filter (E × E)) : HasFDe
rivAtFilter id (.id 𝕜 E) L
-/
theorem hasDerivAtFilter_id : HasDerivAtFilter id 1 L :=
  (hasFDerivAtFilter_id L).hasDerivAtFilter
/-
**hasDerivWithinAt_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_id : HasDerivWithinAt id 1 s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAtFilter_id`：hasDerivAtFilter_id : HasDerivAtFilter id 1 L
-/
theorem hasDerivWithinAt_id : HasDerivWithinAt id 1 s x :=
  hasDerivAtFilter_id _
/-
**hasDerivAt_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_id : HasDerivAt id 1 x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAtFilter_id`：hasDerivAtFilter_id : HasDerivAtFilter id 1 L
-/
theorem hasDerivAt_id : HasDerivAt id 1 x :=
  hasDerivAtFilter_id _
/-
**hasDerivAt_id'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_id' : HasDerivAt (fun x : 𝕜 => x) 1 x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAtFilter_id`：hasDerivAtFilter_id : HasDerivAtFilter id 1 L
-/
theorem hasDerivAt_id' : HasDerivAt (fun x : 𝕜 => x) 1 x :=
  hasDerivAtFilter_id _
/-
**hasStrictDerivAt_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictDerivAt_id : HasStrictDerivAt id 1 x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAtFilter_id`：hasDerivAtFilter_id : HasDerivAtFilter id 1 L
-/
theorem hasStrictDerivAt_id : HasStrictDerivAt id 1 x :=
  hasDerivAtFilter_id _
/-
**deriv_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_id : deriv id x = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `hasDerivAt_id`：hasDerivAt_id : HasDerivAt id 1 x
-/
theorem deriv_id : deriv id x = 1 :=
  HasDerivAt.deriv (hasDerivAt_id x)

@[simp]
/-
**deriv_id'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_id' : deriv (@id 𝕜) = fun _ => 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `deriv_id`：deriv_id : deriv id x = 1
-/
theorem deriv_id' : deriv (@id 𝕜) = fun _ => 1 :=
  funext deriv_id

/-- Variant with `fun x => x` rather than `id` -/
@[simp]
/-
**deriv_id''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_id'' : (deriv fun x : 𝕜 => x) = fun _ => 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `deriv_id'`：deriv_id' : deriv (@id 𝕜) = fun _ => 1

--- 原说明 ---
Variant with `fun x => x` rather than `id`
-/
theorem deriv_id'' : (deriv fun x : 𝕜 => x) = fun _ => 1 :=
  deriv_id'
/-
**derivWithin_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_id (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin id s x = 1
参数：hxs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `hasDerivWithinAt_id`：hasDerivWithinAt_id : HasDerivWithinAt id 1 s x
-/
theorem derivWithin_id (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin id s x = 1 :=
  (hasDerivWithinAt_id x s).derivWithin hxs

/-- Variant with `fun x => x` rather than `id` -/
/-
**derivWithin_id'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_id' (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin (fun x => x
) s x = 1
参数：hxs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `derivWithin_id`：derivWithin_id (hxs : UniqueDiffWithinAt 𝕜 s x) : derivW
ithin id s x = 1

--- 原说明 ---
Variant with `fun x => x` rather than `id`
-/
theorem derivWithin_id' (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin (fun x => x) s x = 1 :=
  derivWithin_id x s hxs

end id

section Const

/-! ### Derivative of constant functions

This include the constant functions `0`, `1`, `Nat.cast n`, `Int.cast z`, and other numerals.
-/

variable (c : F) (s x L)

/-
**hasDerivAtFilter_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAtFilter_const : HasDerivAtFilter (fun _ => c) 0 L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.hasDerivAtFilter`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `hasFDerivAtFilter_const`：hasFDerivAtFilter_const (c : F) (L : Filter (E 
× E)) : HasFDerivAtFilter (fun _ => c) (0 : E ->L[𝕜] F) L
-/
theorem hasDerivAtFilter_const : HasDerivAtFilter (fun _ => c) 0 L :=
  (hasFDerivAtFilter_const c L).hasDerivAtFilter
/-
**hasDerivAtFilter_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAtFilter_zero : HasDerivAtFilter (0 : 𝕜 -> F) 0 L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAtFilter_const`：hasDerivAtFilter_const : HasDerivAtFilter (fun _
 => c) 0 L
-/
theorem hasDerivAtFilter_zero : HasDerivAtFilter (0 : 𝕜 → F) 0 L :=
  hasDerivAtFilter_const _ _
/-
**hasDerivAtFilter_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAtFilter_one [One F] : HasDerivAtFilter (1 : 𝕜 -> F) 0 L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAtFilter_const`：hasDerivAtFilter_const : HasDerivAtFilter (fun _
 => c) 0 L
-/
theorem hasDerivAtFilter_one [One F] : HasDerivAtFilter (1 : 𝕜 → F) 0 L :=
  hasDerivAtFilter_const _ _
/-
**hasDerivAtFilter_natCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAtFilter_natCast [NatCast F] (n : Nat) : HasDerivAtFilter (n : 𝕜 -
> F) 0 L
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAtFilter_const`：hasDerivAtFilter_const : HasDerivAtFilter (fun _
 => c) 0 L
-/
theorem hasDerivAtFilter_natCast [NatCast F] (n : ℕ) : HasDerivAtFilter (n : 𝕜 → F) 0 L :=
  hasDerivAtFilter_const _ _
/-
**hasDerivAtFilter_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAtFilter_intCast [IntCast F] (z : Int) : HasDerivAtFilter (z : 𝕜 -
> F) 0 L
参数：z : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAtFilter_const`：hasDerivAtFilter_const : HasDerivAtFilter (fun _
 => c) 0 L
-/
theorem hasDerivAtFilter_intCast [IntCast F] (z : ℤ) : HasDerivAtFilter (z : 𝕜 → F) 0 L :=
  hasDerivAtFilter_const _ _
/-
**hasDerivAtFilter_ofNat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAtFilter_ofNat (n : Nat) [OfNat F n] : HasDerivAtFilter (ofNat(n) 
: 𝕜 -> F) 0 L
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAtFilter_const`：hasDerivAtFilter_const : HasDerivAtFilter (fun _
 => c) 0 L
-/
theorem hasDerivAtFilter_ofNat (n : ℕ) [OfNat F n] : HasDerivAtFilter (ofNat(n) : 𝕜 → F) 0 L :=
  hasDerivAtFilter_const _ _
/-
**hasStrictDerivAt_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictDerivAt_const : HasStrictDerivAt (fun _ => c) 0 x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAtFilter_const`：hasDerivAtFilter_const : HasDerivAtFilter (fun _
 => c) 0 L
-/
theorem hasStrictDerivAt_const : HasStrictDerivAt (fun _ => c) 0 x :=
  hasDerivAtFilter_const _ _
/-
**hasStrictDerivAt_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictDerivAt_zero : HasStrictDerivAt (0 : 𝕜 -> F) 0 x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasStrictDerivAt_const`：hasStrictDerivAt_const : HasStrictDerivAt (fun _
 => c) 0 x
-/
theorem hasStrictDerivAt_zero : HasStrictDerivAt (0 : 𝕜 → F) 0 x :=
  hasStrictDerivAt_const _ _
/-
**hasStrictDerivAt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictDerivAt_one [One F] : HasStrictDerivAt (1 : 𝕜 -> F) 0 x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasStrictDerivAt_const`：hasStrictDerivAt_const : HasStrictDerivAt (fun _
 => c) 0 x
-/
theorem hasStrictDerivAt_one [One F] : HasStrictDerivAt (1 : 𝕜 → F) 0 x :=
  hasStrictDerivAt_const _ _
/-
**hasStrictDerivAt_natCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictDerivAt_natCast [NatCast F] (n : Nat) : HasStrictDerivAt (n : 𝕜 -
> F) 0 x
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasStrictDerivAt_const`：hasStrictDerivAt_const : HasStrictDerivAt (fun _
 => c) 0 x
-/
theorem hasStrictDerivAt_natCast [NatCast F] (n : ℕ) : HasStrictDerivAt (n : 𝕜 → F) 0 x :=
  hasStrictDerivAt_const _ _
/-
**hasStrictDerivAt_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictDerivAt_intCast [IntCast F] (z : Int) : HasStrictDerivAt (z : 𝕜 -
> F) 0 x
参数：z : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasStrictDerivAt_const`：hasStrictDerivAt_const : HasStrictDerivAt (fun _
 => c) 0 x
-/
theorem hasStrictDerivAt_intCast [IntCast F] (z : ℤ) : HasStrictDerivAt (z : 𝕜 → F) 0 x :=
  hasStrictDerivAt_const _ _
/-
**HasStrictDerivAt_ofNat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt_ofNat (n : Nat) [OfNat F n] : HasStrictDerivAt (ofNat(n) 
: 𝕜 -> F) 0 x
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasStrictDerivAt_const`：hasStrictDerivAt_const : HasStrictDerivAt (fun _
 => c) 0 x
-/
theorem HasStrictDerivAt_ofNat (n : ℕ) [OfNat F n] : HasStrictDerivAt (ofNat(n) : 𝕜 → F) 0 x :=
  hasStrictDerivAt_const _ _
/-
**hasDerivWithinAt_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_const : HasDerivWithinAt (fun _ => c) 0 s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAtFilter_const`：hasDerivAtFilter_const : HasDerivAtFilter (fun _
 => c) 0 L
-/
theorem hasDerivWithinAt_const : HasDerivWithinAt (fun _ => c) 0 s x :=
  hasDerivAtFilter_const _ _
/-
**hasDerivWithinAt_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_zero : HasDerivWithinAt (0 : 𝕜 -> F) 0 s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAtFilter_zero`：hasDerivAtFilter_zero : HasDerivAtFilter (0 : 𝕜 -
> F) 0 L
-/
theorem hasDerivWithinAt_zero : HasDerivWithinAt (0 : 𝕜 → F) 0 s x :=
  hasDerivAtFilter_zero _
/-
**hasDerivWithinAt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_one [One F] : HasDerivWithinAt (1 : 𝕜 -> F) 0 s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivWithinAt_const`：hasDerivWithinAt_const : HasDerivWithinAt (fun _
 => c) 0 s x
-/
theorem hasDerivWithinAt_one [One F] : HasDerivWithinAt (1 : 𝕜 → F) 0 s x :=
  hasDerivWithinAt_const _ _ _
/-
**hasDerivWithinAt_natCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_natCast [NatCast F] (n : Nat) : HasDerivWithinAt (n : 𝕜 -
> F) 0 s x
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivWithinAt_const`：hasDerivWithinAt_const : HasDerivWithinAt (fun _
 => c) 0 s x
-/
theorem hasDerivWithinAt_natCast [NatCast F] (n : ℕ) : HasDerivWithinAt (n : 𝕜 → F) 0 s x :=
  hasDerivWithinAt_const _ _ _
/-
**hasDerivWithinAt_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_intCast [IntCast F] (z : Int) : HasDerivWithinAt (z : 𝕜 -
> F) 0 s x
参数：z : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivWithinAt_const`：hasDerivWithinAt_const : HasDerivWithinAt (fun _
 => c) 0 s x
-/
theorem hasDerivWithinAt_intCast [IntCast F] (z : ℤ) : HasDerivWithinAt (z : 𝕜 → F) 0 s x :=
  hasDerivWithinAt_const _ _ _
/-
**hasDerivWithinAt_ofNat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_ofNat (n : Nat) [OfNat F n] : HasDerivWithinAt (ofNat(n) 
: 𝕜 -> F) 0 s x
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivWithinAt_const`：hasDerivWithinAt_const : HasDerivWithinAt (fun _
 => c) 0 s x
-/
theorem hasDerivWithinAt_ofNat (n : ℕ) [OfNat F n] : HasDerivWithinAt (ofNat(n) : 𝕜 → F) 0 s x :=
  hasDerivWithinAt_const _ _ _
/-
**hasDerivAt_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_const : HasDerivAt (fun _ => c) 0 x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAtFilter_const`：hasDerivAtFilter_const : HasDerivAtFilter (fun _
 => c) 0 L
-/
theorem hasDerivAt_const : HasDerivAt (fun _ => c) 0 x :=
  hasDerivAtFilter_const _ _

@[simp]
/-
**hasDerivAt_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_zero : HasDerivAt (0 : 𝕜 -> F) 0 x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAtFilter_zero`：hasDerivAtFilter_zero : HasDerivAtFilter (0 : 𝕜 -
> F) 0 L
-/
theorem hasDerivAt_zero : HasDerivAt (0 : 𝕜 → F) 0 x :=
  hasDerivAtFilter_zero _
/-
**hasDerivAt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_one [One F] : HasDerivAt (1 : 𝕜 -> F) 0 x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAt_const`：hasDerivAt_const : HasDerivAt (fun _ => c) 0 x
-/
theorem hasDerivAt_one [One F] : HasDerivAt (1 : 𝕜 → F) 0 x :=
  hasDerivAt_const _ _
/-
**hasDerivAt_natCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_natCast [NatCast F] (n : Nat) : HasDerivAt (n : 𝕜 -> F) 0 x
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAt_const`：hasDerivAt_const : HasDerivAt (fun _ => c) 0 x
-/
theorem hasDerivAt_natCast [NatCast F] (n : ℕ) : HasDerivAt (n : 𝕜 → F) 0 x :=
  hasDerivAt_const _ _
/-
**hasDerivAt_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_intCast [IntCast F] (z : Int) : HasDerivAt (z : 𝕜 -> F) 0 x
参数：z : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAt_const`：hasDerivAt_const : HasDerivAt (fun _ => c) 0 x
-/
theorem hasDerivAt_intCast [IntCast F] (z : ℤ) : HasDerivAt (z : 𝕜 → F) 0 x :=
  hasDerivAt_const _ _
/-
**hasDerivAt_ofNat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_ofNat (n : Nat) [OfNat F n] : HasDerivAt (ofNat(n) : 𝕜 -> F) 0 
x
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAt_const`：hasDerivAt_const : HasDerivAt (fun _ => c) 0 x
-/
theorem hasDerivAt_ofNat (n : ℕ) [OfNat F n] : HasDerivAt (ofNat(n) : 𝕜 → F) 0 x :=
  hasDerivAt_const _ _
/-
**deriv_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_const : deriv (fun _ => c) x = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `hasDerivAt_const`：hasDerivAt_const : HasDerivAt (fun _ => c) 0 x
-/
theorem deriv_const : deriv (fun _ => c) x = 0 :=
  HasDerivAt.deriv (hasDerivAt_const x c)

@[simp]
/-
**deriv_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_const' : (deriv fun _ : 𝕜 => c) = fun _ => 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `deriv_const`：deriv_const : deriv (fun _ => c) x = 0
-/
theorem deriv_const' : (deriv fun _ : 𝕜 => c) = fun _ => 0 :=
  funext fun x => deriv_const x c

@[simp]
/-
**deriv_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_zero : deriv (0 : 𝕜 -> F) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `deriv_const`：deriv_const : deriv (fun _ => c) x = 0
-/
theorem deriv_zero : deriv (0 : 𝕜 → F) = 0 := funext fun _ => deriv_const _ _

@[simp]
/-
**deriv_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_one [One F] : deriv (1 : 𝕜 -> F) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `deriv_const`：deriv_const : deriv (fun _ => c) x = 0
-/
theorem deriv_one [One F] : deriv (1 : 𝕜 → F) = 0 := funext fun _ => deriv_const _ _

@[simp]
/-
**deriv_natCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_natCast [NatCast F] (n : Nat) : deriv (n : 𝕜 -> F) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `deriv_const`：deriv_const : deriv (fun _ => c) x = 0
-/
theorem deriv_natCast [NatCast F] (n : ℕ) : deriv (n : 𝕜 → F) = 0 := funext fun _ => deriv_const _ _

@[simp]
/-
**deriv_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_intCast [IntCast F] (z : Int) : deriv (z : 𝕜 -> F) = 0
参数：z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `deriv_const`：deriv_const : deriv (fun _ => c) x = 0
-/
theorem deriv_intCast [IntCast F] (z : ℤ) : deriv (z : 𝕜 → F) = 0 := funext fun _ => deriv_const _ _

@[simp low]
/-
**deriv_ofNat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_ofNat (n : Nat) [OfNat F n] : deriv (ofNat(n) : 𝕜 -> F) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `deriv_const`：deriv_const : deriv (fun _ => c) x = 0
-/
theorem deriv_ofNat (n : ℕ) [OfNat F n] : deriv (ofNat(n) : 𝕜 → F) = 0 :=
  funext fun _ => deriv_const _ _

@[simp]
/-
**derivWithin_fun_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_fun_const : derivWithin (fun _ => c) s = 0
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
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `fderivWithin_fun_const`：fderivWithin_fun_const (c : F) : fderivWithin 𝕜 
(fun _ => c) s = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem derivWithin_fun_const : derivWithin (fun _ => c) s = 0 := by
  ext; simp [derivWithin]

@[simp]
/-
**derivWithin_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_const : derivWithin (Function.const 𝕜 c) s = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `derivWithin_fun_const`：derivWithin_fun_const : derivWithin (fun _ => c) 
s = 0
-/
theorem derivWithin_const : derivWithin (Function.const 𝕜 c) s = 0 :=
  derivWithin_fun_const _ _

@[simp]
/-
**derivWithin_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_zero : derivWithin (0 : 𝕜 -> F) s = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `derivWithin_const`：derivWithin_const : derivWithin (Function.const 𝕜 c) 
s = 0
-/
theorem derivWithin_zero : derivWithin (0 : 𝕜 → F) s = 0 := derivWithin_const _ _

@[simp]
/-
**derivWithin_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_one [One F] : derivWithin (1 : 𝕜 -> F) s = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `derivWithin_const`：derivWithin_const : derivWithin (Function.const 𝕜 c) 
s = 0
-/
theorem derivWithin_one [One F] : derivWithin (1 : 𝕜 → F) s = 0 := derivWithin_const _ _

@[simp]
/-
**derivWithin_natCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_natCast [NatCast F] (n : Nat) : derivWithin (n : 𝕜 -> F) s = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `derivWithin_const`：derivWithin_const : derivWithin (Function.const 𝕜 c) 
s = 0
-/
theorem derivWithin_natCast [NatCast F] (n : ℕ) : derivWithin (n : 𝕜 → F) s = 0 :=
  derivWithin_const _ _

@[simp]
/-
**derivWithin_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_intCast [IntCast F] (z : Int) : derivWithin (z : 𝕜 -> F) s = 0
参数：z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `derivWithin_const`：derivWithin_const : derivWithin (Function.const 𝕜 c) 
s = 0
-/
theorem derivWithin_intCast [IntCast F] (z : ℤ) : derivWithin (z : 𝕜 → F) s = 0 :=
  derivWithin_const _ _

@[simp low]
/-
**derivWithin_ofNat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_ofNat (n : Nat) [OfNat F n] : derivWithin (ofNat(n) : 𝕜 -> F) 
s = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `derivWithin_const`：derivWithin_const : derivWithin (Function.const 𝕜 c) 
s = 0
-/
theorem derivWithin_ofNat (n : ℕ) [OfNat F n] : derivWithin (ofNat(n) : 𝕜 → F) s = 0 :=
  derivWithin_const _ _

end Const

section Continuous

/-! ### Continuity of a function admitting a derivative -/

/-
**HasDerivAtFilter.tendsto_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAtFilter.tendsto_nhds {L : Filter 𝕜} (hL : L <= 𝓝 x) (h : HasDeriv
AtFilter f f' (L ×ˢ pure x)) : Tendsto f L (𝓝 (f x))
参数：hL : L <= 𝓝 x；h : HasDerivAtFilter f f' (L ×ˢ pure x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivAtFilter.tendsto_nhds`：HasFDerivAtFilter.tendsto_nhds {L : Filt
er E} (hL : L <= 𝓝 x) (h : HasFDerivAtFilter f f' (L ×ˢ pure x)) : Tendsto f L (
𝓝 (f x))
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasDerivAtFilter.hasFDerivAtFilter`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…

--- 原说明 ---
### Continuity of a function admitting a derivative
-/
theorem HasDerivAtFilter.tendsto_nhds {L : Filter 𝕜} (hL : L ≤ 𝓝 x)
    (h : HasDerivAtFilter f f' (L ×ˢ pure x)) :
    Tendsto f L (𝓝 (f x)) :=
  h.hasFDerivAtFilter.tendsto_nhds hL
/-
**HasDerivWithinAt.continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.continuousWithinAt (h : HasDerivWithinAt f f' s x) : Cont
inuousWithinAt f s x
参数：h : HasDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.tendsto_nhds`：HasDerivAtFilter.tendsto_nhds {L : Filter
 𝕜} (hL : L <= 𝓝 x) (h : HasDerivAtFilter f f' (L ×ˢ pure x)) : Tendsto f L (𝓝 (
f x))
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem HasDerivWithinAt.continuousWithinAt (h : HasDerivWithinAt f f' s x) :
    ContinuousWithinAt f s x :=
  HasDerivAtFilter.tendsto_nhds inf_le_left h
/-
**HasDerivAt.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.continuousAt (h : HasDerivAt f f' x) : ContinuousAt f x
参数：h : HasDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.tendsto_nhds`：HasDerivAtFilter.tendsto_nhds {L : Filter
 𝕜} (hL : L <= 𝓝 x) (h : HasDerivAtFilter f f' (L ×ˢ pure x)) : Tendsto f L (𝓝 (
f x))
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem HasDerivAt.continuousAt (h : HasDerivAt f f' x) : ContinuousAt f x :=
  HasDerivAtFilter.tendsto_nhds le_rfl h
/-
**HasDerivWithinAt.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.continuousOn {f f' : 𝕜 -> F} (h : forall x in s, HasDeriv
WithinAt f (f' x) s x) : ContinuousOn f s
参数：h : forall x in s, HasDerivWithinAt f (f' x) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.continuousWithinAt`：HasDerivWithinAt.continuousWithinAt
 (h : HasDerivWithinAt f f' s x) : ContinuousWithinAt f s x
-/
theorem HasDerivWithinAt.continuousOn {f f' : 𝕜 → F} (h : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) :
    ContinuousOn f s := fun x hx => (h x hx).continuousWithinAt
/-
**HasDerivAt.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `HasDerivAt`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F : Type v} [inst_1 : N
ormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {s : Set 𝕜} {f f' : 𝕜 → F}, (∀
 x ∈ s, HasDerivAt f (f' x) x) → ContinuousOn f s
参数：∀ x ∈ s, HasDerivAt f (f' x) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `HasDerivAt.continuousAt`：HasDerivAt.continuousAt (h : HasDerivAt f f' x)
 : ContinuousAt f x
-/
protected theorem HasDerivAt.continuousOn {f f' : 𝕜 → F} (hderiv : ∀ x ∈ s, HasDerivAt f (f' x) x) :
    ContinuousOn f s := fun x hx => (hderiv x hx).continuousAt.continuousWithinAt

end Continuous

section MeanValue

/-- Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-lipschitz
on a neighborhood of `x₀` then its derivative at `x₀` has norm bounded by `C`. This version
only assumes that `‖f x - f x₀‖ ≤ C * ‖x - x₀‖` in a neighborhood of `x`. -/
/-
**HasDerivAt.le_of_lip'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.le_of_lip' {f : 𝕜 -> F} {f' : F} {x₀ : 𝕜} (hf : HasDerivAt f f'
 x₀) {C : Real} (hC₀ : 0 <= C) (hlip : forallᶠ x in 𝓝 x₀, ‖f x - f x₀‖ <= C * ‖x
 - x₀‖) : ‖f'‖ <= C
参数：hf : HasDerivAt f f' x₀；hC₀ : 0 <= C；hlip : forallᶠ x in 𝓝 x₀, ‖f x - f x₀‖ <
= C * ‖x - x₀‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.norm_toSpanSingleton`：∀ {𝕜 : Type u_1} {E : Type u_4
} [inst : SeminormedAddCommGroup E] [inst_1 : NontriviallyNormedField 𝕜]   [inst
_2 : NormedSpace 𝕜 E] (x : E),…
· 使用定理 `HasFDerivAt.le_of_lip'`：HasFDerivAt.le_of_lip' {f : E -> F} {f' : E ->L[
𝕜] F} {x₀ : E} (hf : HasFDerivAt f f' x₀) {C : Real} (hC₀ : 0 <= C) (hlip : fora
llᶠ x in 𝓝 x…
· 使用定理 `HasDerivAt.hasFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…

--- 原说明 ---
Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-
lipschitz
on a neighborhood of `x₀` then its derivative at `x₀` has norm bounded by `C`. T
his version
only assumes that `‖f x - f x₀‖ ≤ C * ‖x - x₀‖` in a neighborhood of `x`.
-/
theorem HasDerivAt.le_of_lip' {f : 𝕜 → F} {f' : F} {x₀ : 𝕜} (hf : HasDerivAt f f' x₀)
    {C : ℝ} (hC₀ : 0 ≤ C) (hlip : ∀ᶠ x in 𝓝 x₀, ‖f x - f x₀‖ ≤ C * ‖x - x₀‖) :
    ‖f'‖ ≤ C := by
  simpa using HasFDerivAt.le_of_lip' hf.hasFDerivAt hC₀ hlip

/-- Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-lipschitz
on a neighborhood of `x₀` then its derivative at `x₀` has norm bounded by `C`. -/
/-
**HasDerivAt.le_of_lipschitzOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.le_of_lipschitzOn {f : 𝕜 -> F} {f' : F} {x₀ : 𝕜} (hf : HasDeriv
At f f' x₀) {s : Set 𝕜} (hs : s in 𝓝 x₀) {C : Real>=0} (hlip : LipschitzOnWith C
 f s) : ‖f'‖ <= C
参数：hf : HasDerivAt f f' x₀；hs : s in 𝓝 x₀；hlip : LipschitzOnWith C f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.norm_toSpanSingleton`：∀ {𝕜 : Type u_1} {E : Type u_4
} [inst : SeminormedAddCommGroup E] [inst_1 : NontriviallyNormedField 𝕜]   [inst
_2 : NormedSpace 𝕜 E] (x : E),…
· 使用定理 `HasFDerivAt.le_of_lipschitzOn`：HasFDerivAt.le_of_lipschitzOn {f : E -> F
} {f' : E ->L[𝕜] F} {x₀ : E} (hf : HasFDerivAt f f' x₀) {s : Set E} (hs : s in 𝓝
 x₀) {C : Real>=0} …
· 使用定理 `HasDerivAt.hasFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…

--- 原说明 ---
Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-
lipschitz
on a neighborhood of `x₀` then its derivative at `x₀` has norm bounded by `C`.
-/
theorem HasDerivAt.le_of_lipschitzOn {f : 𝕜 → F} {f' : F} {x₀ : 𝕜} (hf : HasDerivAt f f' x₀)
    {s : Set 𝕜} (hs : s ∈ 𝓝 x₀) {C : ℝ≥0} (hlip : LipschitzOnWith C f s) : ‖f'‖ ≤ C := by
  simpa using HasFDerivAt.le_of_lipschitzOn hf.hasFDerivAt hs hlip

/-- Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-lipschitz
then its derivative at `x₀` has norm bounded by `C`. -/
/-
**HasDerivAt.le_of_lipschitz** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.le_of_lipschitz {f : 𝕜 -> F} {f' : F} {x₀ : 𝕜} (hf : HasDerivAt
 f f' x₀) {C : Real>=0} (hlip : LipschitzWith C f) : ‖f'‖ <= C
参数：hf : HasDerivAt f f' x₀；hlip : LipschitzWith C f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.norm_toSpanSingleton`：∀ {𝕜 : Type u_1} {E : Type u_4
} [inst : SeminormedAddCommGroup E] [inst_1 : NontriviallyNormedField 𝕜]   [inst
_2 : NormedSpace 𝕜 E] (x : E),…
· 使用定理 `HasFDerivAt.le_of_lipschitz`：HasFDerivAt.le_of_lipschitz {f : E -> F} {f
' : E ->L[𝕜] F} {x₀ : E} (hf : HasFDerivAt f f' x₀) {C : Real>=0} (hlip : Lipsch
itzWith C f) : ‖f…
· 使用定理 `HasDerivAt.hasFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…

--- 原说明 ---
Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-
lipschitz
then its derivative at `x₀` has norm bounded by `C`.
-/
theorem HasDerivAt.le_of_lipschitz {f : 𝕜 → F} {f' : F} {x₀ : 𝕜} (hf : HasDerivAt f f' x₀)
    {C : ℝ≥0} (hlip : LipschitzWith C f) : ‖f'‖ ≤ C := by
  simpa using HasFDerivAt.le_of_lipschitz hf.hasFDerivAt hlip

/-- Converse to the mean value inequality: if `f` is `C`-lipschitz
on a neighborhood of `x₀` then its derivative at `x₀` has norm bounded by `C`. This version
only assumes that `‖f x - f x₀‖ ≤ C * ‖x - x₀‖` in a neighborhood of `x`. -/
/-
**norm_deriv_le_of_lip'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_deriv_le_of_lip' {f : 𝕜 -> F} {x₀ : 𝕜} {C : Real} (hC₀ : 0 <= C) (hli
p : forallᶠ x in 𝓝 x₀, ‖f x - f x₀‖ <= C * ‖x - x₀‖) : ‖deriv f x₀‖ <= C
参数：hC₀ : 0 <= C；hlip : forallᶠ x in 𝓝 x₀, ‖f x - f x₀‖ <= C * ‖x - x₀‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_deriv_eq_norm_fderiv`：norm_deriv_eq_norm_fderiv : ‖deriv f x‖ = ‖fd
eriv 𝕜 f x‖
· 使用定理 `norm_fderiv_le_of_lip'`：norm_fderiv_le_of_lip' {f : E -> F} {x₀ : E} {C 
: Real} (hC₀ : 0 <= C) (hlip : forallᶠ x in 𝓝 x₀, ‖f x - f x₀‖ <= C * ‖x - x₀‖) 
: ‖fderiv 𝕜 …

--- 原说明 ---
Converse to the mean value inequality: if `f` is `C`-lipschitz
on a neighborhood of `x₀` then its derivative at `x₀` has norm bounded by `C`. T
his version
only assumes that `‖f x - f x₀‖ ≤ C * ‖x - x₀‖` in a neighborhood of `x`.
-/
theorem norm_deriv_le_of_lip' {f : 𝕜 → F} {x₀ : 𝕜}
    {C : ℝ} (hC₀ : 0 ≤ C) (hlip : ∀ᶠ x in 𝓝 x₀, ‖f x - f x₀‖ ≤ C * ‖x - x₀‖) :
    ‖deriv f x₀‖ ≤ C := by
  simpa [norm_deriv_eq_norm_fderiv] using norm_fderiv_le_of_lip' 𝕜 hC₀ hlip

/-- Converse to the mean value inequality: if `f` is `C`-lipschitz
on a neighborhood of `x₀` then its derivative at `x₀` has norm bounded by `C`.
Version using `deriv`. -/
/-
**norm_deriv_le_of_lipschitzOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_deriv_le_of_lipschitzOn {f : 𝕜 -> F} {x₀ : 𝕜} {s : Set 𝕜} (hs : s in 
𝓝 x₀) {C : Real>=0} (hlip : LipschitzOnWith C f s) : ‖deriv f x₀‖ <= C
参数：hs : s in 𝓝 x₀；hlip : LipschitzOnWith C f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_deriv_eq_norm_fderiv`：norm_deriv_eq_norm_fderiv : ‖deriv f x‖ = ‖fd
eriv 𝕜 f x‖
· 使用定理 `norm_fderiv_le_of_lipschitzOn`：norm_fderiv_le_of_lipschitzOn {f : E -> F
} {x₀ : E} {s : Set E} (hs : s in 𝓝 x₀) {C : Real>=0} (hlip : LipschitzOnWith C 
f s) : ‖fderiv 𝕜 f …

--- 原说明 ---
Converse to the mean value inequality: if `f` is `C`-lipschitz
on a neighborhood of `x₀` then its derivative at `x₀` has norm bounded by `C`.
Version using `deriv`.
-/
theorem norm_deriv_le_of_lipschitzOn {f : 𝕜 → F} {x₀ : 𝕜} {s : Set 𝕜} (hs : s ∈ 𝓝 x₀)
    {C : ℝ≥0} (hlip : LipschitzOnWith C f s) : ‖deriv f x₀‖ ≤ C := by
  simpa [norm_deriv_eq_norm_fderiv] using norm_fderiv_le_of_lipschitzOn 𝕜 hs hlip

/-- Converse to the mean value inequality: if `f` is `C`-lipschitz then
its derivative at `x₀` has norm bounded by `C`.
Version using `deriv`. -/
/-
**norm_deriv_le_of_lipschitz** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_deriv_le_of_lipschitz {f : 𝕜 -> F} {x₀ : 𝕜} {C : Real>=0} (hlip : Lip
schitzWith C f) : ‖deriv f x₀‖ <= C
参数：hlip : LipschitzWith C f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_deriv_eq_norm_fderiv`：norm_deriv_eq_norm_fderiv : ‖deriv f x‖ = ‖fd
eriv 𝕜 f x‖
· 使用定理 `norm_fderiv_le_of_lipschitz`：norm_fderiv_le_of_lipschitz {f : E -> F} {x
₀ : E} {C : Real>=0} (hlip : LipschitzWith C f) : ‖fderiv 𝕜 f x₀‖ <= C

--- 原说明 ---
Converse to the mean value inequality: if `f` is `C`-lipschitz then
its derivative at `x₀` has norm bounded by `C`.
Version using `deriv`.
-/
theorem norm_deriv_le_of_lipschitz {f : 𝕜 → F} {x₀ : 𝕜}
    {C : ℝ≥0} (hlip : LipschitzWith C f) : ‖deriv f x₀‖ ≤ C := by
  simpa [norm_deriv_eq_norm_fderiv] using norm_fderiv_le_of_lipschitz 𝕜 hlip

end MeanValue

section Semilinear

variable {σ σ' : RingHom 𝕜 𝕜} [RingHomIsometric σ] [RingHomInvPair σ σ']
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] (L : F →SL[σ] F')

variable (σ')

set_option backward.isDefEq.respectTransparency false in
/-- If `L` is a `σ`-semilinear map, and `f` has Fréchet derivative `f'` at `x`, then `L ∘ f ∘ σ⁻¹`
has Fréchet derivative `L ∘ f'` at `σ x`. -/
/-
**HasDerivAt.comp_semilinear** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasDerivAt.comp_semilinear (hf : HasDerivAt f f' x) : HasDerivAt (L ∘ f ∘ 
σ') (L f') (σ x)
参数：hf : HasDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用引理 `RingHomIsometric.inv`：RingHomIsometric.inv {𝕜₁ 𝕜₂ : Type*} [SeminormedRi
ng 𝕜₁] [SeminormedRing 𝕜₂] (σ : 𝕜₁ ->+* 𝕜₂) {σ' : 𝕜₂ ->+* 𝕜₁} [RingHomInvPair σ 
σ'] [RingH…
· 使用定理 `Isometry.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSp
ace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Continuous f
· 使用引理 `RingHom.isometry`：RingHom.isometry {𝕜₁ 𝕜₂ : Type*} [SeminormedRing 𝕜₁] [
SeminormedRing 𝕜₂] (σ : 𝕜₁ ->+* 𝕜₂) [RingHomIsometric σ] : Isometry σ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasDerivAt_iff_hasFDerivAt`：hasDerivAt_iff_hasFDerivAt {f' : F} : HasDer
ivAt f f' x ↔ HasFDerivAt f (toSpanSingleton 𝕜 f') x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `ContinuousLinearMap.ext_ring`：ext_ring [TopologicalSpace R₁] {f g : R₁ -
>L[R₁] M₁} (h : f 1 = g 1) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `RingHom.toSemilinearMap_apply`：∀ {R : Type u_1} {S : Type u_5} [inst : S
emiring R] [inst_1 : Semiring S] (f : R →+* S) (a : R),   f.toSemilinearMap a = 
(↑↑f).toFun a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `HasFDerivAt.comp_semilinear`：HasFDerivAt.comp_semilinear {f : V -> W} {z
 : V'} {f' : V ->L[𝕜] W} (hf : HasFDerivAt f f' (R z)) : HasFDerivAt (L ∘ f ∘ R)
 (L.comp (f'.comp…
· 使用定理 `RingHomInvPair.comp_apply_eq`：comp_apply_eq {x : R₁} : σ' (σ x) = x

--- 原说明 ---
If `L` is a `σ`-semilinear map, and `f` has Fréchet derivative `f'` at `x`, then
 `L ∘ f ∘ σ⁻¹`
has Fréchet derivative `L ∘ f'` at `σ x`.
-/
lemma HasDerivAt.comp_semilinear (hf : HasDerivAt f f' x) :
    HasDerivAt (L ∘ f ∘ σ') (L f') (σ x) := by
  have : RingHomIsometric σ' := .inv σ
  let R : 𝕜 →SL[σ'] 𝕜 := ⟨σ'.toSemilinearMap, σ'.isometry.continuous⟩
  have hR (k : 𝕜) : R k = σ' k := rfl
  rw [hasDerivAt_iff_hasFDerivAt]
  convert! HasFDerivAt.comp_semilinear L R (f' := toSpanSingleton 𝕜 f') ?_
  · ext
    simp [R]
  · rwa [← hasDerivAt_iff_hasFDerivAt, hR, RingHomInvPair.comp_apply_eq]

/-- If `f` is differentiable at `x`, and `L` is `σ`-semilinear, then `L ∘ f ∘ σ⁻¹` is
differentiable at `σ x`. -/
/-
**DifferentiableAt.comp_semilinear** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is differentiable at `x`, and `L` is `σ`-semilinear, then `L ∘ f ∘ σ⁻¹` i
s
differentiable at `σ x`.
-/
lemma DifferentiableAt.comp_semilinear₁ (hf : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (L ∘ f ∘ σ') (σ x) :=
  (hf.hasDerivAt.comp_semilinear σ' L).differentiableAt

variable (σ) {f : 𝕜 → 𝕜} {f' : 𝕜}

/-- If `f` has derivative `f'` at `x`, and `σ, σ'` are mutually inverse normed-ring automorphisms,
then `σ ∘ f ∘ σ'` has derivative `σ f'` at `σ x`. -/
/-
**HasDerivAt.comp_ringHom** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasDerivAt.comp_ringHom (hf : HasDerivAt f f' x) : HasDerivAt (σ ∘ f ∘ σ')
 (σ f') (σ x)
参数：hf : HasDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用引理 `HasDerivAt.comp_semilinear`：HasDerivAt.comp_semilinear (hf : HasDerivAt 
f f' x) : HasDerivAt (L ∘ f ∘ σ') (L f') (σ x)
· 使用定理 `Isometry.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSp
ace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Continuous f
· 使用引理 `RingHom.isometry`：RingHom.isometry {𝕜₁ 𝕜₂ : Type*} [SeminormedRing 𝕜₁] [
SeminormedRing 𝕜₂] (σ : 𝕜₁ ->+* 𝕜₂) [RingHomIsometric σ] : Isometry σ

--- 原说明 ---
If `f` has derivative `f'` at `x`, and `σ, σ'` are mutually inverse normed-ring 
automorphisms,
then `σ ∘ f ∘ σ'` has derivative `σ f'` at `σ x`.
-/
lemma HasDerivAt.comp_ringHom (hf : HasDerivAt f f' x) : HasDerivAt (σ ∘ f ∘ σ') (σ f') (σ x) :=
  hf.comp_semilinear σ' ⟨σ.toSemilinearMap, σ.isometry.continuous⟩

/-- If `f` is differentiable at `x`, and `L` is `σ`-semilinear, then `L ∘ f ∘ σ⁻¹` is
differentiable at `σ x`. -/
/-
**DifferentiableAt.comp_ringHom** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DifferentiableAt.comp_ringHom (hf : DifferentiableAt 𝕜 f x) : Differentiab
leAt 𝕜 (σ ∘ f ∘ σ') (σ x)
参数：hf : DifferentiableAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用引理 `HasDerivAt.comp_ringHom`：HasDerivAt.comp_ringHom (hf : HasDerivAt f f' x
) : HasDerivAt (σ ∘ f ∘ σ') (σ f') (σ x)
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x

--- 原说明 ---
If `f` is differentiable at `x`, and `L` is `σ`-semilinear, then `L ∘ f ∘ σ⁻¹` i
s
differentiable at `σ x`.
-/
lemma DifferentiableAt.comp_ringHom (hf : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (σ ∘ f ∘ σ') (σ x) :=
  (hf.hasDerivAt.comp_ringHom σ σ').differentiableAt

end Semilinear

