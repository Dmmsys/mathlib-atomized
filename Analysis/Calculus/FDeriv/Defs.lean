/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Asymptotics.TVS

/-!
# The Fréchet derivative: definition

Let `E` and `F` be normed spaces, `f : E → F`, and `f' : E →L[𝕜] F` a
continuous 𝕜-linear map, where `𝕜` is a non-discrete normed field. Then

  `HasFDerivWithinAt f f' s x`

says that `f` has derivative `f'` at `x`, where the domain of interest
is restricted to `s`. We also have

  `HasFDerivAt f f' x := HasFDerivWithinAt f f' x univ`

Finally,

  `HasStrictFDerivAt f f' x`

means that `f : E → F` has derivative `f' : E →L[𝕜] F` in the sense of strict differentiability,
i.e., `f y - f z - f'(y - z) = o(y - z)` as `y, z → x`. This notion is used in the inverse
function theorem, and is defined here only to avoid proving theorems like
`IsBoundedBilinearMap.hasFDerivAt` twice: first for `HasFDerivAt`, then for
`HasStrictFDerivAt`.

This file `Defs.lean` is intended to just contain the definitions and the bare minimum of
supporting lemmas; a much wider range of elementary properties are proved in the file  `Basic.lean`.

Other files in the folder `Analysis/Calculus/FDeriv/` contain the usual formulas
(and existence assertions) for the derivative of
* constants (`Const.lean`)
* the identity
* bounded linear maps (`Linear.lean`)
* bounded bilinear maps (`Bilinear.lean`)
* sum of two functions (`Add.lean`)
* sum of finitely many functions (`Add.lean`)
* multiplication of a function by a scalar constant (`Add.lean`)
* negative of a function (`Add.lean`)
* subtraction of two functions (`Add.lean`)
* multiplication of a function by a scalar function (`Mul.lean`)
* multiplication of two scalar functions (`Mul.lean`)
* composition of functions (the chain rule) (`Comp.lean`)
* inverse function (`Mul.lean`)
  (assuming that it exists; the inverse function theorem is in `../Inverse.lean`)

## Implementation details

The derivative is defined in terms of the `IsLittleOTVS` relation to ensure the definition does not
ingrain a choice of norm, and is then quickly translated to the more convenient `IsLittleO` in the
subsequent theorems. It is also characterized in terms of the `Tendsto` relation.

We also introduce predicates `DifferentiableWithinAt 𝕜 f s x` (where `𝕜` is the base field,
`f` the function to be differentiated, `x` the point at which the derivative is asserted to exist,
and `s` the set along which the derivative is defined), as well as `DifferentiableAt 𝕜 f x`,
`DifferentiableOn 𝕜 f s` and `Differentiable 𝕜 f` to express the existence of a derivative.

To be able to compute with derivatives, we write `fderivWithin 𝕜 f s x` and `fderiv 𝕜 f x`
for some choice of a derivative if it exists, and the zero function otherwise. This choice only
behaves well along sets for which the derivative is unique, i.e., those for which the tangent
directions span a dense subset of the whole space. The predicates `UniqueDiffWithinAt s x` and
`UniqueDiffOn s`, defined in `TangentCone.lean` express this property. We prove that indeed
they imply the uniqueness of the derivative. This is satisfied for open subsets, and in particular
for `univ`. This uniqueness only holds when the field is non-discrete, which we request at the very
beginning: otherwise, a derivative can be defined, but it has no interesting properties whatsoever.

## TODO

Generalize more results to topological vector spaces.

## Tags

derivative, differentiable, Fréchet, calculus

-/

@[expose] public section

open Filter Asymptotics ContinuousLinearMap Set Metric Topology NNReal ENNReal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

noncomputable section TVS
/-!
## Definitions valid in an arbitrary topological vector space
-/

variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- A function `f` has the continuous linear map `f'` as derivative along the filter `L` if
`f x₁ = f x₂ + f' (x₁ - x₂) + o (x₁ - x₂)` when `x = (x₁, x₂)` converges along the filter `L`.
This definition is designed to be specialized

- for `L = 𝓝 (x, x)` (in `HasStrictFDerivAt`),
  giving rise to the derivative in the sense of strict differentiability;
- for `L = 𝓝 x ×ˢ pure x` (in `HasFDerivAt`), giving rise to the usual notion of Fréchet derivative;
- for `L = 𝓝[s] x ×ˢ pure x` (in `HasFDerivWithinAt`),
  giving rise to the notion of Fréchet derivative along the set `s`.
-/
@[mk_iff hasFDerivAtFilter_iff_isLittleOTVS]
/-
**HasFDerivAtFilter** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : AddCommGroup E] →         [inst_2 : _root_.Module 𝕜 E] →     
      [inst_3 : TopologicalSpace E] →             {F : Type u_3} →              
 [inst_4 : AddCommGroup F] →                 [inst_5 : _root_.Module 𝕜 F] →     
              [inst_6 : TopologicalSpace F] → (E → F) → (E →L[𝕜] F) → Filter (E 
× E) → Prop
参数：E → F；E →L[𝕜] F；E × E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` has the continuous linear map `f'` as derivative along the filter
 `L` if
`f x₁ = f x₂ + f' (x₁ - x₂) + o (x₁ - x₂)` when `x = (x₁, x₂)` converges along t
he filter `L`.
This definition is designed to be specialized

- for `L = 𝓝 (x, x)` (in `HasStrictFDerivAt`),
  giving rise to the derivative in the sense of strict differentiability;
- for `L = 𝓝 x ×ˢ pure x` (in `HasFDerivAt`), giving rise to the usual notion of
 Fréchet derivative;
- for `L = 𝓝[s] x ×ˢ pure x` (in `HasFDerivWithinAt`),
  giving rise to the notion of Fréchet derivative along the set `s`.
-/
structure HasFDerivAtFilter (f : E → F) (f' : E →L[𝕜] F) (L : Filter (E × E)) : Prop where
  of_isLittleOTVS ::
    isLittleOTVS : (fun p ↦ f p.1 - f p.2 - f' (p.1 - p.2)) =o[𝕜; L] (fun p ↦ p.1 - p.2)

/-- A function `f` has the continuous linear map `f'` as derivative at `x` within a set `s` if
`f x' = f x + f' (x' - x) + o (x' - x)` when `x'` tends to `x` inside `s`. -/
@[fun_prop]
/-
**HasFDerivWithinAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt (f : E -> F) (f' : E ->L[𝕜] F) (s : Set E) (x : E)
参数：f : E -> F；f' : E ->L[𝕜] F；s : Set E；x : E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` has the continuous linear map `f'` as derivative at `x` within a 
set `s` if
`f x' = f x + f' (x' - x) + o (x' - x)` when `x'` tends to `x` inside `s`.
-/
def HasFDerivWithinAt (f : E → F) (f' : E →L[𝕜] F) (s : Set E) (x : E) :=
  HasFDerivAtFilter f f' (𝓝[s] x ×ˢ pure x)

/-- A function `f` has the continuous linear map `f'` as derivative at `x` if
`f x' = f x + f' (x' - x) + o (x' - x)` when `x'` tends to `x`. -/
@[fun_prop]
/-
**HasFDerivAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HasFDerivAt (f : E -> F) (f' : E ->L[𝕜] F) (x : E)
参数：f : E -> F；f' : E ->L[𝕜] F；x : E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` has the continuous linear map `f'` as derivative at `x` if
`f x' = f x + f' (x' - x) + o (x' - x)` when `x'` tends to `x`.
-/
def HasFDerivAt (f : E → F) (f' : E →L[𝕜] F) (x : E) :=
  HasFDerivAtFilter f f' (𝓝 x ×ˢ pure x)

/-- A function `f` has derivative `f'` at `a` in the sense of *strict differentiability*
if `f x - f y - f' (x - y) = o(x - y)` as `x, y → a`. This form of differentiability is required,
e.g., by the inverse function theorem. Any `C^1` function on a vector space over `ℝ` is strictly
differentiable but this definition works, e.g., for vector spaces over `p`-adic numbers. -/
@[fun_prop]
/-
**HasStrictFDerivAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt (f : E -> F) (f' : E ->L[𝕜] F) (x : E)
参数：f : E -> F；f' : E ->L[𝕜] F；x : E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` has derivative `f'` at `a` in the sense of *strict differentiabil
ity*
if `f x - f y - f' (x - y) = o(x - y)` as `x, y → a`. This form of differentiabi
lity is required,
e.g., by the inverse function theorem. Any `C^1` function on a vector space over
 `ℝ` is strictly
differentiable but this definition works, e.g., for vector spaces over `p`-adic 
numbers.
-/
def HasStrictFDerivAt (f : E → F) (f' : E →L[𝕜] F) (x : E) :=
  HasFDerivAtFilter f f' (𝓝 (x, x))

variable (𝕜)

/-- A function `f` is differentiable at a point `x` within a set `s` if it admits a derivative
there (possibly non-unique). -/
@[fun_prop]
/-
**DifferentiableWithinAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt (f : E -> F) (s : Set E) (x : E)
参数：f : E -> F；s : Set E；x : E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` is differentiable at a point `x` within a set `s` if it admits a 
derivative
there (possibly non-unique).
-/
def DifferentiableWithinAt (f : E → F) (s : Set E) (x : E) :=
  ∃ f' : E →L[𝕜] F, HasFDerivWithinAt f f' s x

/-- A function `f` is differentiable at a point `x` if it admits a derivative there (possibly
non-unique). -/
@[fun_prop]
/-
**DifferentiableAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DifferentiableAt (f : E -> F) (x : E)
参数：f : E -> F；x : E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` is differentiable at a point `x` if it admits a derivative there 
(possibly
non-unique).
-/
def DifferentiableAt (f : E → F) (x : E) :=
  ∃ f' : E →L[𝕜] F, HasFDerivAt f f' x

open scoped Classical in
/-- If `f` has a derivative at `x` within `s`, then `fderivWithin 𝕜 f s x` is such a derivative.
Otherwise, it is set to `0`. We also set it to be zero, if zero is one of possible derivatives. -/
irreducible_def fderivWithin (f : E → F) (s : Set E) (x : E) : E →L[𝕜] F :=
  if HasFDerivWithinAt f (0 : E →L[𝕜] F) s x
    then 0
  else if h : DifferentiableWithinAt 𝕜 f s x
    then Classical.choose h
  else 0

/-- If `f` has a derivative at `x`, then `fderiv 𝕜 f x` is such a derivative. Otherwise, it is
set to `0`. -/
irreducible_def fderiv (f : E → F) (x : E) : E →L[𝕜] F :=
  fderivWithin 𝕜 f univ x

/-- `DifferentiableOn 𝕜 f s` means that `f` is differentiable within `s` at any point of `s`. -/
@[fun_prop]
/-
**DifferentiableOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DifferentiableOn (f : E -> F) (s : Set E)
参数：f : E -> F；s : Set E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`DifferentiableOn 𝕜 f s` means that `f` is differentiable within `s` at any poin
t of `s`.
-/
def DifferentiableOn (f : E → F) (s : Set E) :=
  ∀ x ∈ s, DifferentiableWithinAt 𝕜 f s x

/-- `Differentiable 𝕜 f` means that `f` is differentiable at any point. -/
@[fun_prop]
/-
**Differentiable** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Differentiable (f : E -> F)
参数：f : E -> F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Differentiable 𝕜 f` means that `f` is differentiable at any point.
-/
def Differentiable (f : E → F) :=
  ∀ x, DifferentiableAt 𝕜 f x

variable {𝕜}
variable {f f₀ f₁ g : E → F}
variable {f' f₀' f₁' g' : E →L[𝕜] F}
variable {x : E}
variable {s : Set E}
variable {L : Filter E}
/-
**hasFDerivAt_iff_isLittleOTVS** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_iff_isLittleOTVS : HasFDerivAt f f' x ↔ (fun x' => f x' - f x 
- f' (x' - x)) =o[𝕜; 𝓝 x] (fun x' => x' - x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.prod_pure`：prod_pure {b : β} : f ×ˢ pure b = map (fun a => (a, b)
) f
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasFDerivAt_iff_isLittleOTVS :
    HasFDerivAt f f' x ↔ (fun x' ↦ f x' - f x - f' (x' - x)) =o[𝕜; 𝓝 x] (fun x' ↦ x' - x) := by
  simp [HasFDerivAt, hasFDerivAtFilter_iff_isLittleOTVS, Function.comp_def]

alias ⟨HasFDerivAt.isLittleOTVS, HasFDerivAt.of_isLittleOTVS⟩ := hasFDerivAt_iff_isLittleOTVS
/-
**hasFDerivWithinAt_iff_isLittleOTVS** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_iff_isLittleOTVS : HasFDerivWithinAt f f' s x ↔ (fun x' 
=> f x' - f x - f' (x' - x)) =o[𝕜; 𝓝[s] x] (fun x' => x' - x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.prod_pure`：prod_pure {b : β} : f ×ˢ pure b = map (fun a => (a, b)
) f
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasFDerivWithinAt_iff_isLittleOTVS :
    HasFDerivWithinAt f f' s x ↔
      (fun x' ↦ f x' - f x - f' (x' - x)) =o[𝕜; 𝓝[s] x] (fun x' ↦ x' - x) := by
  simp [HasFDerivWithinAt, hasFDerivAtFilter_iff_isLittleOTVS, Function.comp_def]

alias ⟨HasFDerivWithinAt.isLittleOTVS, HasFDerivWithinAt.of_isLittleOTVS⟩ :=
  hasFDerivWithinAt_iff_isLittleOTVS
/-
**hasStrictFDerivAt_iff_isLittleOTVS** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_iff_isLittleOTVS : HasStrictFDerivAt f f' x ↔ (fun p => 
f p.1 - f p.2 - f' (p.1 - p.2)) =o[𝕜; 𝓝 (x, x)] (fun p => p.1 - p.2)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_iff_isLittleOTVS`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Modu
le 𝕜 E] [inst_3 : Topolo…
-/
theorem hasStrictFDerivAt_iff_isLittleOTVS :
    HasStrictFDerivAt f f' x ↔
      (fun p ↦ f p.1 - f p.2 - f' (p.1 - p.2)) =o[𝕜; 𝓝 (x, x)] (fun p ↦ p.1 - p.2) :=
  hasFDerivAtFilter_iff_isLittleOTVS ..
/-
**fderivWithin_zero_of_not_differentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_zero_of_not_differentiableWithinAt (h : ¬DifferentiableWithin
At 𝕜 f s x) : fderivWithin 𝕜 f s x = 0
参数：h : ¬DifferentiableWithinAt 𝕜 f s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_def`：∀ (𝕜 : Type u_4) [inst : NontriviallyNormedField 𝕜] {E
 : Type u_5} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : 
Topolo…
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fderivWithin_zero_of_not_differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) :
    fderivWithin 𝕜 f s x = 0 := by
  simp [fderivWithin, h]

@[simp]
/-
**fderivWithin_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_univ : fderivWithin 𝕜 f univ = fderiv 𝕜 f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderiv_def`：∀ (𝕜 : Type u_4) [inst : NontriviallyNormedField 𝕜] {E : Typ
e u_5} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : Topolo
…
-/
theorem fderivWithin_univ : fderivWithin 𝕜 f univ = fderiv 𝕜 f := by
  ext
  rw [fderiv]

end TVS

section Normed
/-!
## Reformulations for seminormed spaces
-/

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f : E → F} {f' : E →L[𝕜] F} {s : Set E} {x : E}

/-
**hasFDerivAtFilter_iff_isLittleO** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAtFilter_iff_isLittleO {L : Filter (E × E)} : HasFDerivAtFilter f
 f' L ↔ (fun p => f p.1 - f p.2 - f' (p.1 - p.2)) =o[L] fun p => p.1 - p.2
参数：E × E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `hasFDerivAtFilter_iff_isLittleOTVS`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Modu
le 𝕜 E] [inst_3 : Topolo…
· 使用引理 `Asymptotics.isLittleOTVS_iff_isLittleO`：isLittleOTVS_iff_isLittleO : f =
o[𝕜; l] g ↔ f =o[l] g
-/
theorem hasFDerivAtFilter_iff_isLittleO {L : Filter (E × E)} :
    HasFDerivAtFilter f f' L ↔ (fun p => f p.1 - f p.2 - f' (p.1 - p.2)) =o[L] fun p => p.1 - p.2 :=
  (hasFDerivAtFilter_iff_isLittleOTVS ..).trans isLittleOTVS_iff_isLittleO

alias ⟨HasFDerivAtFilter.isLittleO, HasFDerivAtFilter.of_isLittleO⟩ :=
  hasFDerivAtFilter_iff_isLittleO
/-
**hasFDerivAt_iff_isLittleO** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_iff_isLittleO : HasFDerivAt f f' x ↔ (fun x' => f x' - f x - f
' (x' - x)) =o[𝓝 x] (fun x' => x' - x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `hasFDerivAt_iff_isLittleOTVS`：hasFDerivAt_iff_isLittleOTVS : HasFDerivAt
 f f' x ↔ (fun x' => f x' - f x - f' (x' - x)) =o[𝕜; 𝓝 x] (fun x' => x' - x)
· 使用引理 `Asymptotics.isLittleOTVS_iff_isLittleO`：isLittleOTVS_iff_isLittleO : f =
o[𝕜; l] g ↔ f =o[l] g
-/
theorem hasFDerivAt_iff_isLittleO :
    HasFDerivAt f f' x ↔ (fun x' ↦ f x' - f x - f' (x' - x)) =o[𝓝 x] (fun x' ↦ x' - x) :=
  hasFDerivAt_iff_isLittleOTVS.trans isLittleOTVS_iff_isLittleO

alias ⟨HasFDerivAt.isLittleO, HasFDerivAt.of_isLittleO⟩ := hasFDerivAt_iff_isLittleO
/-
**hasFDerivWithinAt_iff_isLittleO** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_iff_isLittleO : HasFDerivWithinAt f f' s x ↔ (fun x' => 
f x' - f x - f' (x' - x)) =o[𝓝[s] x] (fun x' => x' - x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `hasFDerivWithinAt_iff_isLittleOTVS`：hasFDerivWithinAt_iff_isLittleOTVS :
 HasFDerivWithinAt f f' s x ↔ (fun x' => f x' - f x - f' (x' - x)) =o[𝕜; 𝓝[s] x]
 (fun x' => x' - x)
· 使用引理 `Asymptotics.isLittleOTVS_iff_isLittleO`：isLittleOTVS_iff_isLittleO : f =
o[𝕜; l] g ↔ f =o[l] g
-/
theorem hasFDerivWithinAt_iff_isLittleO :
    HasFDerivWithinAt f f' s x ↔
      (fun x' ↦ f x' - f x - f' (x' - x)) =o[𝓝[s] x] (fun x' ↦ x' - x) :=
  hasFDerivWithinAt_iff_isLittleOTVS.trans isLittleOTVS_iff_isLittleO

alias ⟨HasFDerivWithinAt.isLittleO, HasFDerivWithinAt.of_isLittleO⟩ :=
  hasFDerivWithinAt_iff_isLittleO
/-
**hasStrictFDerivAt_iff_isLittleO** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_iff_isLittleO : HasStrictFDerivAt f f' x ↔ (fun p : E × 
E => f p.1 - f p.2 - f' (p.1 - p.2)) =o[𝓝 (x, x)] fun p : E × E => p.1 - p.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `hasStrictFDerivAt_iff_isLittleOTVS`：hasStrictFDerivAt_iff_isLittleOTVS :
 HasStrictFDerivAt f f' x ↔ (fun p => f p.1 - f p.2 - f' (p.1 - p.2)) =o[𝕜; 𝓝 (x
, x)] (fun p => p.1 - p.…
· 使用引理 `Asymptotics.isLittleOTVS_iff_isLittleO`：isLittleOTVS_iff_isLittleO : f =
o[𝕜; l] g ↔ f =o[l] g
-/
theorem hasStrictFDerivAt_iff_isLittleO :
    HasStrictFDerivAt f f' x ↔
      (fun p : E × E => f p.1 - f p.2 - f' (p.1 - p.2)) =o[𝓝 (x, x)] fun p : E × E => p.1 - p.2 :=
  (hasStrictFDerivAt_iff_isLittleOTVS ..).trans isLittleOTVS_iff_isLittleO

alias ⟨HasStrictFDerivAt.isLittleO, HasStrictFDerivAt.of_isLittleO⟩ :=
  hasStrictFDerivAt_iff_isLittleO

end Normed

