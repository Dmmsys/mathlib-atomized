/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Line derivatives

We define the line derivative of a function `f : E → F`, at a point `x : E` along a vector `v : E`,
as the element `f' : F` such that `f (x + t • v) = f x + t • f' + o (t)` as `t` tends to `0` in
the scalar field `𝕜`, if it exists. It is denoted by `lineDeriv 𝕜 f x v`.

This notion is generally less well behaved than the full Fréchet derivative (for instance, the
composition of functions which are line-differentiable is not line-differentiable in general).
The Fréchet derivative should therefore be favored over this one in general, although the line
derivative may sometimes prove handy.

The line derivative in direction `v` is also called the Gateaux derivative in direction `v`,
although the term "Gateaux derivative" is sometimes reserved for the situation where there is
such a derivative in all directions, for the map `v ↦ lineDeriv 𝕜 f x v` (which doesn't have to be
linear in general).

## Main definition and results

We mimic the definitions and statements for the Fréchet derivative and the one-dimensional
derivative. We define in particular the following objects:

* `LineDifferentiableWithinAt 𝕜 f s x v`
* `LineDifferentiableAt 𝕜 f x v`
* `HasLineDerivWithinAt 𝕜 f f' s x v`
* `HasLineDerivAt 𝕜 f s x v`
* `lineDerivWithin 𝕜 f s x v`
* `lineDeriv 𝕜 f x v`

and develop about them a basic API inspired by the one for the Fréchet derivative.

We depart from the Fréchet derivative in two places, as the dependence of the following predicates
on the direction would make them barely usable:
* We do not define an analogue of the predicate `UniqueDiffOn`;
* We do not define `LineDifferentiableOn` nor `LineDifferentiable`.
-/

@[expose] public section

noncomputable section

open scoped Topology Filter ENNReal NNReal

open Filter Asymptotics Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section Module
/-!
Results that do not rely on a topological structure on `E`
-/

variable (𝕜)
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]

/-- `f` has the derivative `f'` at the point `x` along the direction `v` in the set `s`.
That is, `f (x + t v) = f x + t • f' + o (t)` when `t` tends to `0` and `x + t v ∈ s`.
Note that this definition is less well behaved than the total Fréchet derivative, which
should generally be favored over this one. -/
/-
**HasLineDerivWithinAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HasLineDerivWithinAt (f : E -> F) (f' : F) (s : Set E) (x : E) (v : E)
参数：f : E -> F；f' : F；s : Set E；x : E；v : E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` has the derivative `f'` at the point `x` along the direction `v` in the set 
`s`.
That is, `f (x + t v) = f x + t • f' + o (t)` when `t` tends to `0` and `x + t v
 ∈ s`.
Note that this definition is less well behaved than the total Fréchet derivative
, which
should generally be favored over this one.
-/
def HasLineDerivWithinAt (f : E → F) (f' : F) (s : Set E) (x : E) (v : E) :=
  HasDerivWithinAt (fun t ↦ f (x + t • v)) f' ((fun t ↦ x + t • v) ⁻¹' s) (0 : 𝕜)

/-- `f` has the derivative `f'` at the point `x` along the direction `v`.
That is, `f (x + t v) = f x + t • f' + o (t)` when `t` tends to `0`.
Note that this definition is less well behaved than the total Fréchet derivative, which
should generally be favored over this one. -/
/-
**HasLineDerivAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HasLineDerivAt (f : E -> F) (f' : F) (x : E) (v : E)
参数：f : E -> F；f' : F；x : E；v : E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` has the derivative `f'` at the point `x` along the direction `v`.
That is, `f (x + t v) = f x + t • f' + o (t)` when `t` tends to `0`.
Note that this definition is less well behaved than the total Fréchet derivative
, which
should generally be favored over this one.
-/
def HasLineDerivAt (f : E → F) (f' : F) (x : E) (v : E) :=
  HasDerivAt (fun t ↦ f (x + t • v)) f' (0 : 𝕜)

/-- `f` is line-differentiable at the point `x` in the direction `v` in the set `s` if there
exists `f'` such that `f (x + t v) = f x + t • f' + o (t)` when `t` tends to `0` and `x + t v ∈ s`.
-/
/-
**LineDifferentiableWithinAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LineDifferentiableWithinAt (f : E -> F) (s : Set E) (x : E) (v : E) : Prop
参数：f : E -> F；s : Set E；x : E；v : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` is line-differentiable at the point `x` in the direction `v` in the set `s` 
if there
exists `f'` such that `f (x + t v) = f x + t • f' + o (t)` when `t` tends to `0`
 and `x + t v ∈ s`.
-/
def LineDifferentiableWithinAt (f : E → F) (s : Set E) (x : E) (v : E) : Prop :=
  DifferentiableWithinAt 𝕜 (fun t ↦ f (x + t • v)) ((fun t ↦ x + t • v) ⁻¹' s) (0 : 𝕜)

/-- `f` is line-differentiable at the point `x` in the direction `v` if there
exists `f'` such that `f (x + t v) = f x + t • f' + o (t)` when `t` tends to `0`. -/
/-
**LineDifferentiableAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LineDifferentiableAt (f : E -> F) (x : E) (v : E) : Prop
参数：f : E -> F；x : E；v : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` is line-differentiable at the point `x` in the direction `v` if there
exists `f'` such that `f (x + t v) = f x + t • f' + o (t)` when `t` tends to `0`
.
-/
def LineDifferentiableAt (f : E → F) (x : E) (v : E) : Prop :=
  DifferentiableAt 𝕜 (fun t ↦ f (x + t • v)) (0 : 𝕜)

/-- Line derivative of `f` at the point `x` in the direction `v` within the set `s`, if it exists.
Zero otherwise.

If the line derivative exists (i.e., `∃ f', HasLineDerivWithinAt 𝕜 f f' s x v`), then
`f (x + t v) = f x + t lineDerivWithin 𝕜 f s x v + o (t)` when `t` tends to `0` and `x + t v ∈ s`.
-/
/-
**lineDerivWithin** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：lineDerivWithin (f : E -> F) (s : Set E) (x : E) (v : E) : F
参数：f : E -> F；s : Set E；x : E；v : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Line derivative of `f` at the point `x` in the direction `v` within the set `s`,
 if it exists.
Zero otherwise.

If the line derivative exists (i.e., `∃ f', HasLineDerivWithinAt 𝕜 f f' s x v`),
 then
`f (x + t v) = f x + t lineDerivWithin 𝕜 f s x v + o (t)` when `t` tends to `0` 
and `x + t v ∈ s`.
-/
def lineDerivWithin (f : E → F) (s : Set E) (x : E) (v : E) : F :=
  derivWithin (fun t ↦ f (x + t • v)) ((fun t ↦ x + t • v) ⁻¹' s) (0 : 𝕜)

/-- Line derivative of `f` at the point `x` in the direction `v`, if it exists.  Zero otherwise.

If the line derivative exists (i.e., `∃ f', HasLineDerivAt 𝕜 f f' x v`), then
`f (x + t v) = f x + t lineDeriv 𝕜 f x v + o (t)` when `t` tends to `0`.
-/
/-
**lineDeriv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：lineDeriv (f : E -> F) (x : E) (v : E) : F
参数：f : E -> F；x : E；v : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Line derivative of `f` at the point `x` in the direction `v`, if it exists.  Zer
o otherwise.

If the line derivative exists (i.e., `∃ f', HasLineDerivAt 𝕜 f f' x v`), then
`f (x + t v) = f x + t lineDeriv 𝕜 f x v + o (t)` when `t` tends to `0`.
-/
def lineDeriv (f : E → F) (x : E) (v : E) : F :=
  deriv (fun t ↦ f (x + t • v)) (0 : 𝕜)

variable {𝕜}
variable {f f₁ : E → F} {f' f₀' f₁' : F} {s t : Set E} {x v : E}
/-
**HasLineDerivWithinAt.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasLineDerivWithinAt.mono (hf : HasLineDerivWithinAt 𝕜 f f' s x v) (hst : 
t subseteq s) : HasLineDerivWithinAt 𝕜 f f' t x v
参数：hf : HasLineDerivWithinAt 𝕜 f f' s x v；hst : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.mono`：HasDerivWithinAt.mono (h : HasDerivWithinAt f f' 
t x) (hst : s subseteq t) : HasDerivWithinAt f f' s x
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
-/
lemma HasLineDerivWithinAt.mono (hf : HasLineDerivWithinAt 𝕜 f f' s x v) (hst : t ⊆ s) :
    HasLineDerivWithinAt 𝕜 f f' t x v :=
  HasDerivWithinAt.mono hf (preimage_mono hst)
/-
**HasLineDerivAt.hasLineDerivWithinAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasLineDerivAt.hasLineDerivWithinAt (hf : HasLineDerivAt 𝕜 f f' x v) (s : 
Set E) : HasLineDerivWithinAt 𝕜 f f' s x v
参数：hf : HasLineDerivAt 𝕜 f f' x v；s : Set E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
-/
lemma HasLineDerivAt.hasLineDerivWithinAt (hf : HasLineDerivAt 𝕜 f f' x v) (s : Set E) :
    HasLineDerivWithinAt 𝕜 f f' s x v :=
  HasDerivAt.hasDerivWithinAt hf
/-
**HasLineDerivWithinAt.lineDifferentiableWithinAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasLineDerivWithinAt.lineDifferentiableWithinAt (hf : HasLineDerivWithinAt
 𝕜 f f' s x v) : LineDifferentiableWithinAt 𝕜 f s x v
参数：hf : HasLineDerivWithinAt 𝕜 f f' s x v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.differentiableWithinAt`：HasDerivWithinAt.differentiable
WithinAt (h : HasDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
-/
lemma HasLineDerivWithinAt.lineDifferentiableWithinAt (hf : HasLineDerivWithinAt 𝕜 f f' s x v) :
    LineDifferentiableWithinAt 𝕜 f s x v :=
  HasDerivWithinAt.differentiableWithinAt hf
/-
**HasLineDerivAt.lineDifferentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasLineDerivAt.lineDifferentiableAt (hf : HasLineDerivAt 𝕜 f f' x v) : Lin
eDifferentiableAt 𝕜 f x v
参数：hf : HasLineDerivAt 𝕜 f f' x v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
-/
theorem HasLineDerivAt.lineDifferentiableAt (hf : HasLineDerivAt 𝕜 f f' x v) :
    LineDifferentiableAt 𝕜 f x v :=
  HasDerivAt.differentiableAt hf
/-
**LineDifferentiableWithinAt.hasLineDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LineDifferentiableWithinAt.hasLineDerivWithinAt (h : LineDifferentiableWit
hinAt 𝕜 f s x v) : HasLineDerivWithinAt 𝕜 f (lineDerivWithin 𝕜 f s x v) s x v
参数：h : LineDifferentiableWithinAt 𝕜 f s x v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
-/
theorem LineDifferentiableWithinAt.hasLineDerivWithinAt (h : LineDifferentiableWithinAt 𝕜 f s x v) :
    HasLineDerivWithinAt 𝕜 f (lineDerivWithin 𝕜 f s x v) s x v :=
  DifferentiableWithinAt.hasDerivWithinAt h
/-
**LineDifferentiableAt.hasLineDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LineDifferentiableAt.hasLineDerivAt (h : LineDifferentiableAt 𝕜 f x v) : H
asLineDerivAt 𝕜 f (lineDeriv 𝕜 f x v) x v
参数：h : LineDifferentiableAt 𝕜 f x v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem LineDifferentiableAt.hasLineDerivAt (h : LineDifferentiableAt 𝕜 f x v) :
    HasLineDerivAt 𝕜 f (lineDeriv 𝕜 f x v) x v :=
  DifferentiableAt.hasDerivAt h
/-
**hasLineDerivWithinAt_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {F : Type u_2} [inst_1
 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {E : Type u_3} [inst_3 : A
ddCommGroup E] [inst_4 : _root_.Module 𝕜 E] {f : E → F} {f' : F}   {x v : E}, Ha
sLineDerivWithinAt 𝕜 f f' Set.univ x v ↔ HasLineDerivAt 𝕜 f f' x v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma hasLineDerivWithinAt_univ :
    HasLineDerivWithinAt 𝕜 f f' univ x v ↔ HasLineDerivAt 𝕜 f f' x v := by
  simp only [HasLineDerivWithinAt, HasLineDerivAt, preimage_univ, hasDerivWithinAt_univ]
/-
**lineDerivWithin_zero_of_not_lineDifferentiableWithinAt** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：lineDerivWithin_zero_of_not_lineDifferentiableWithinAt (h : ¬LineDifferent
iableWithinAt 𝕜 f s x v) : lineDerivWithin 𝕜 f s x v = 0
参数：h : ¬LineDifferentiableWithinAt 𝕜 f s x v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `derivWithin_zero_of_not_differentiableWithinAt`：derivWithin_zero_of_not_
differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) : derivWithin f s x
 = 0
-/
theorem lineDerivWithin_zero_of_not_lineDifferentiableWithinAt
    (h : ¬LineDifferentiableWithinAt 𝕜 f s x v) :
    lineDerivWithin 𝕜 f s x v = 0 :=
  derivWithin_zero_of_not_differentiableWithinAt h
/-
**lineDeriv_zero_of_not_lineDifferentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lineDeriv_zero_of_not_lineDifferentiableAt (h : ¬LineDifferentiableAt 𝕜 f 
x v) : lineDeriv 𝕜 f x v = 0
参数：h : ¬LineDifferentiableAt 𝕜 f x v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `deriv_zero_of_not_differentiableAt`：deriv_zero_of_not_differentiableAt (
h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0
-/
theorem lineDeriv_zero_of_not_lineDifferentiableAt (h : ¬LineDifferentiableAt 𝕜 f x v) :
    lineDeriv 𝕜 f x v = 0 :=
  deriv_zero_of_not_differentiableAt h
/-
**hasLineDerivAt_iff_isLittleO_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasLineDerivAt_iff_isLittleO_nhds_zero : HasLineDerivAt 𝕜 f f' x v ↔ (fun 
t : 𝕜 => f (x + t • v) - f x - t • f') =o[𝓝 0] fun t => t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasLineDerivAt_iff_isLittleO_nhds_zero :
    HasLineDerivAt 𝕜 f f' x v ↔
      (fun t : 𝕜 => f (x + t • v) - f x - t • f') =o[𝓝 0] fun t => t := by
  simp only [HasLineDerivAt, hasDerivAt_iff_isLittleO_nhds_zero, zero_add, zero_smul, add_zero]
/-
**HasLineDerivAt.unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasLineDerivAt.unique (h₀ : HasLineDerivAt 𝕜 f f₀' x v) (h₁ : HasLineDeriv
At 𝕜 f f₁' x v) : f₀' = f₁'
参数：h₀ : HasLineDerivAt 𝕜 f f₀' x v；h₁ : HasLineDerivAt 𝕜 f f₁' x v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.unique`：HasDerivAt.unique (h₀ : HasDerivAt f f₀' x) (h₁ : Has
DerivAt f f₁' x) : f₀' = f₁'
-/
theorem HasLineDerivAt.unique (h₀ : HasLineDerivAt 𝕜 f f₀' x v) (h₁ : HasLineDerivAt 𝕜 f f₁' x v) :
    f₀' = f₁' :=
  HasDerivAt.unique h₀ h₁
/-
**HasLineDerivAt.lineDeriv** 是 Mathlib 中的一个定理，位于命名空间 `HasLineDerivAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {F : Type u_2} [inst_1
 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {E : Type u_3} [inst_3 : A
ddCommGroup E] [inst_4 : _root_.Module 𝕜 E] {f : E → F} {f' : F}   {x v : E}, Ha
sLineDerivAt 𝕜 f f' x v → lineDeriv 𝕜 f x v = f'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasLineDerivAt.unique`：HasLineDerivAt.unique (h₀ : HasLineDerivAt 𝕜 f f₀
' x v) (h₁ : HasLineDerivAt 𝕜 f f₁' x v) : f₀' = f₁'
· 使用定理 `LineDifferentiableAt.hasLineDerivAt`：LineDifferentiableAt.hasLineDerivAt
 (h : LineDifferentiableAt 𝕜 f x v) : HasLineDerivAt 𝕜 f (lineDeriv 𝕜 f x v) x v
· 使用定理 `HasLineDerivAt.lineDifferentiableAt`：HasLineDerivAt.lineDifferentiableAt
 (hf : HasLineDerivAt 𝕜 f f' x v) : LineDifferentiableAt 𝕜 f x v
-/
protected theorem HasLineDerivAt.lineDeriv (h : HasLineDerivAt 𝕜 f f' x v) :
    lineDeriv 𝕜 f x v = f' := by
  rw [h.unique h.lineDifferentiableAt.hasLineDerivAt]
/-
**lineDifferentiableWithinAt_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lineDifferentiableWithinAt_univ : LineDifferentiableWithinAt 𝕜 f univ x v 
↔ LineDifferentiableAt 𝕜 f x v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lineDifferentiableWithinAt_univ :
    LineDifferentiableWithinAt 𝕜 f univ x v ↔ LineDifferentiableAt 𝕜 f x v := by
  simp only [LineDifferentiableWithinAt, LineDifferentiableAt, preimage_univ,
    differentiableWithinAt_univ]
/-
**LineDifferentiableAt.lineDifferentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LineDifferentiableAt.lineDifferentiableWithinAt (h : LineDifferentiableAt 
𝕜 f x v) : LineDifferentiableWithinAt 𝕜 f s x v
参数：h : LineDifferentiableAt 𝕜 f x v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.mono`：DifferentiableWithinAt.mono (h : Differenti
ableWithinAt 𝕜 f t x) (st : s subseteq t) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `differentiableWithinAt_univ`：differentiableWithinAt_univ : Differentiabl
eWithinAt 𝕜 f univ x ↔ DifferentiableAt 𝕜 f x
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem LineDifferentiableAt.lineDifferentiableWithinAt (h : LineDifferentiableAt 𝕜 f x v) :
    LineDifferentiableWithinAt 𝕜 f s x v :=
  (differentiableWithinAt_univ.2 h).mono (subset_univ _)

@[simp]
/-
**lineDerivWithin_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lineDerivWithin_univ : lineDerivWithin 𝕜 f univ x v = lineDeriv 𝕜 f x v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `derivWithin_univ`：derivWithin_univ : derivWithin f univ = deriv f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lineDerivWithin_univ : lineDerivWithin 𝕜 f univ x v = lineDeriv 𝕜 f x v := by
  simp [lineDerivWithin, lineDeriv]
/-
**LineDifferentiableWithinAt.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LineDifferentiableWithinAt.mono (h : LineDifferentiableWithinAt 𝕜 f t x v)
 (st : s subseteq t) : LineDifferentiableWithinAt 𝕜 f s x v
参数：h : LineDifferentiableWithinAt 𝕜 f t x v；st : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasLineDerivWithinAt.lineDifferentiableWithinAt`：HasLineDerivWithinAt.li
neDifferentiableWithinAt (hf : HasLineDerivWithinAt 𝕜 f f' s x v) : LineDifferen
tiableWithinAt 𝕜 f s x v
· 使用引理 `HasLineDerivWithinAt.mono`：HasLineDerivWithinAt.mono (hf : HasLineDerivW
ithinAt 𝕜 f f' s x v) (hst : t subseteq s) : HasLineDerivWithinAt 𝕜 f f' t x v
· 使用定理 `LineDifferentiableWithinAt.hasLineDerivWithinAt`：LineDifferentiableWithi
nAt.hasLineDerivWithinAt (h : LineDifferentiableWithinAt 𝕜 f s x v) : HasLineDer
ivWithinAt 𝕜 f (lineDerivWithin 𝕜 f s…
-/
theorem LineDifferentiableWithinAt.mono (h : LineDifferentiableWithinAt 𝕜 f t x v) (st : s ⊆ t) :
    LineDifferentiableWithinAt 𝕜 f s x v :=
  (h.hasLineDerivWithinAt.mono st).lineDifferentiableWithinAt
/-
**HasLineDerivWithinAt.congr_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasLineDerivWithinAt.congr_mono (h : HasLineDerivWithinAt 𝕜 f f' s x v) (h
t : EqOn f₁ f t) (hx : f₁ x = f x) (h₁ : t subseteq s) : HasLineDerivWithinAt 𝕜 
f₁ f' t x v
参数：h : HasLineDerivWithinAt 𝕜 f f' s x v；ht : EqOn f₁ f t；hx : f₁ x = f x；h₁ : t
 subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.congr_mono`：HasDerivWithinAt.congr_mono (h : HasDerivWi
thinAt f f' s x) (ht : forall x in t, f₁ x = f x) (hx : f₁ x = f x) (h₁ : t subs
eteq s) : HasDeri…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
-/
theorem HasLineDerivWithinAt.congr_mono (h : HasLineDerivWithinAt 𝕜 f f' s x v) (ht : EqOn f₁ f t)
    (hx : f₁ x = f x) (h₁ : t ⊆ s) : HasLineDerivWithinAt 𝕜 f₁ f' t x v :=
  HasDerivWithinAt.congr_mono h (fun _ hy ↦ ht hy) (by simpa using hx) (preimage_mono h₁)
/-
**HasLineDerivWithinAt.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasLineDerivWithinAt.congr (h : HasLineDerivWithinAt 𝕜 f f' s x v) (hs : E
qOn f₁ f s) (hx : f₁ x = f x) : HasLineDerivWithinAt 𝕜 f₁ f' s x v
参数：h : HasLineDerivWithinAt 𝕜 f f' s x v；hs : EqOn f₁ f s；hx : f₁ x = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasLineDerivWithinAt.congr_mono`：HasLineDerivWithinAt.congr_mono (h : Ha
sLineDerivWithinAt 𝕜 f f' s x v) (ht : EqOn f₁ f t) (hx : f₁ x = f x) (h₁ : t su
bseteq s) : HasLineDe…
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
-/
theorem HasLineDerivWithinAt.congr (h : HasLineDerivWithinAt 𝕜 f f' s x v) (hs : EqOn f₁ f s)
    (hx : f₁ x = f x) : HasLineDerivWithinAt 𝕜 f₁ f' s x v :=
  h.congr_mono hs hx (Subset.refl _)
/-
**HasLineDerivWithinAt.congr'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasLineDerivWithinAt.congr' (h : HasLineDerivWithinAt 𝕜 f f' s x v) (hs : 
EqOn f₁ f s) (hx : x in s) : HasLineDerivWithinAt 𝕜 f₁ f' s x v
参数：h : HasLineDerivWithinAt 𝕜 f f' s x v；hs : EqOn f₁ f s；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasLineDerivWithinAt.congr`：HasLineDerivWithinAt.congr (h : HasLineDeriv
WithinAt 𝕜 f f' s x v) (hs : EqOn f₁ f s) (hx : f₁ x = f x) : HasLineDerivWithin
At 𝕜 f₁ f' s x v
-/
theorem HasLineDerivWithinAt.congr' (h : HasLineDerivWithinAt 𝕜 f f' s x v)
    (hs : EqOn f₁ f s) (hx : x ∈ s) :
    HasLineDerivWithinAt 𝕜 f₁ f' s x v :=
  h.congr hs (hs hx)
/-
**LineDifferentiableWithinAt.congr_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LineDifferentiableWithinAt.congr_mono (h : LineDifferentiableWithinAt 𝕜 f 
s x v) (ht : EqOn f₁ f t) (hx : f₁ x = f x) (h₁ : t subseteq s) : LineDifferenti
ableWithinAt 𝕜 f₁ t x v
参数：h : LineDifferentiableWithinAt 𝕜 f s x v；ht : EqOn f₁ f t；hx : f₁ x = f x；h₁ 
: t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.differentiableWithinAt`：HasDerivWithinAt.differentiable
WithinAt (h : HasDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasLineDerivWithinAt.congr_mono`：HasLineDerivWithinAt.congr_mono (h : Ha
sLineDerivWithinAt 𝕜 f f' s x v) (ht : EqOn f₁ f t) (hx : f₁ x = f x) (h₁ : t su
bseteq s) : HasLineDe…
· 使用定理 `LineDifferentiableWithinAt.hasLineDerivWithinAt`：LineDifferentiableWithi
nAt.hasLineDerivWithinAt (h : LineDifferentiableWithinAt 𝕜 f s x v) : HasLineDer
ivWithinAt 𝕜 f (lineDerivWithin 𝕜 f s…
-/
theorem LineDifferentiableWithinAt.congr_mono (h : LineDifferentiableWithinAt 𝕜 f s x v)
    (ht : EqOn f₁ f t) (hx : f₁ x = f x) (h₁ : t ⊆ s) :
    LineDifferentiableWithinAt 𝕜 f₁ t x v :=
  (HasLineDerivWithinAt.congr_mono h.hasLineDerivWithinAt ht hx h₁).differentiableWithinAt
/-
**LineDifferentiableWithinAt.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LineDifferentiableWithinAt.congr (h : LineDifferentiableWithinAt 𝕜 f s x v
) (ht : forall x in s, f₁ x = f x) (hx : f₁ x = f x) : LineDifferentiableWithinA
t 𝕜 f₁ s x v
参数：h : LineDifferentiableWithinAt 𝕜 f s x v；ht : forall x in s, f₁ x = f x；hx : 
f₁ x = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LineDifferentiableWithinAt.congr_mono`：LineDifferentiableWithinAt.congr_
mono (h : LineDifferentiableWithinAt 𝕜 f s x v) (ht : EqOn f₁ f t) (hx : f₁ x = 
f x) (h₁ : t subseteq s) : …
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
-/
theorem LineDifferentiableWithinAt.congr (h : LineDifferentiableWithinAt 𝕜 f s x v)
    (ht : ∀ x ∈ s, f₁ x = f x) (hx : f₁ x = f x) :
    LineDifferentiableWithinAt 𝕜 f₁ s x v :=
  LineDifferentiableWithinAt.congr_mono h ht hx (Subset.refl _)
/-
**lineDerivWithin_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lineDerivWithin_congr (hs : EqOn f₁ f s) (hx : f₁ x = f x) : lineDerivWith
in 𝕜 f₁ s x v = lineDerivWithin 𝕜 f s x v
参数：hs : EqOn f₁ f s；hx : f₁ x = f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `derivWithin_congr`：derivWithin_congr (hs : EqOn f₁ f s) (hx : f₁ x = f x
) : derivWithin f₁ s x = derivWithin f s x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem lineDerivWithin_congr (hs : EqOn f₁ f s) (hx : f₁ x = f x) :
    lineDerivWithin 𝕜 f₁ s x v = lineDerivWithin 𝕜 f s x v :=
  derivWithin_congr (fun _ hy ↦ hs hy) (by simpa using hx)
/-
**lineDerivWithin_congr'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lineDerivWithin_congr' (hs : EqOn f₁ f s) (hx : x in s) : lineDerivWithin 
𝕜 f₁ s x v = lineDerivWithin 𝕜 f s x v
参数：hs : EqOn f₁ f s；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lineDerivWithin_congr`：lineDerivWithin_congr (hs : EqOn f₁ f s) (hx : f₁
 x = f x) : lineDerivWithin 𝕜 f₁ s x v = lineDerivWithin 𝕜 f s x v
-/
theorem lineDerivWithin_congr' (hs : EqOn f₁ f s) (hx : x ∈ s) :
    lineDerivWithin 𝕜 f₁ s x v = lineDerivWithin 𝕜 f s x v :=
  lineDerivWithin_congr hs (hs hx)
/-
**hasLineDerivAt_iff_tendsto_slope_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasLineDerivAt_iff_tendsto_slope_zero : HasLineDerivAt 𝕜 f f' x v ↔ Tendst
o (fun (t : 𝕜) => t⁻¹ • (f (x + t • v) - f x)) (𝓝[!=] 0) (𝓝 f')
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasLineDerivAt_iff_tendsto_slope_zero :
    HasLineDerivAt 𝕜 f f' x v ↔
      Tendsto (fun (t : 𝕜) ↦ t⁻¹ • (f (x + t • v) - f x)) (𝓝[≠] 0) (𝓝 f') := by
  simp only [HasLineDerivAt, hasDerivAt_iff_tendsto_slope_zero, zero_add,
    zero_smul, add_zero]

alias ⟨HasLineDerivAt.tendsto_slope_zero, _⟩ := hasLineDerivAt_iff_tendsto_slope_zero
/-
**HasLineDerivAt.tendsto_slope_zero_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasLineDerivAt.tendsto_slope_zero_right [Preorder 𝕜] (h : HasLineDerivAt 𝕜
 f f' x v) : Tendsto (fun (t : 𝕜) => t⁻¹ • (f (x + t • v) - f x)) (𝓝[>] 0) (𝓝 f'
)
参数：h : HasLineDerivAt 𝕜 f f' x v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `HasLineDerivAt.tendsto_slope_zero`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {F : Type u_2} [inst_1 : NormedAddCommGroup F]   [inst_2 : Normed
Space 𝕜 F] {E : Type u_…
· 使用定理 `nhdsGT_le_nhdsNE`：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1 :
 Preorder α] (a : α), nhdsWithin a (Set.Ioi a) ≤ nhdsWithin a {a}ᶜ
-/
theorem HasLineDerivAt.tendsto_slope_zero_right [Preorder 𝕜] (h : HasLineDerivAt 𝕜 f f' x v) :
    Tendsto (fun (t : 𝕜) ↦ t⁻¹ • (f (x + t • v) - f x)) (𝓝[>] 0) (𝓝 f') :=
  h.tendsto_slope_zero.mono_left (nhdsGT_le_nhdsNE 0)
/-
**HasLineDerivAt.tendsto_slope_zero_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasLineDerivAt.tendsto_slope_zero_left [Preorder 𝕜] (h : HasLineDerivAt 𝕜 
f f' x v) : Tendsto (fun (t : 𝕜) => t⁻¹ • (f (x + t • v) - f x)) (𝓝[<] 0) (𝓝 f')
参数：h : HasLineDerivAt 𝕜 f f' x v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `HasLineDerivAt.tendsto_slope_zero`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {F : Type u_2} [inst_1 : NormedAddCommGroup F]   [inst_2 : Normed
Space 𝕜 F] {E : Type u_…
· 使用定理 `nhdsLT_le_nhdsNE`：nhdsLT_le_nhdsNE (a : α) : 𝓝[<] a <= 𝓝[!=] a
-/
theorem HasLineDerivAt.tendsto_slope_zero_left [Preorder 𝕜] (h : HasLineDerivAt 𝕜 f f' x v) :
    Tendsto (fun (t : 𝕜) ↦ t⁻¹ • (f (x + t • v) - f x)) (𝓝[<] 0) (𝓝 f') :=
  h.tendsto_slope_zero.mono_left (nhdsLT_le_nhdsNE 0)
/-
**HasLineDerivWithinAt.hasLineDerivAt'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasLineDerivWithinAt.hasLineDerivAt' (h : HasLineDerivWithinAt 𝕜 f f' s x 
v) (hs : forallᶠ t : 𝕜 in 𝓝 0, x + t • v in s) : HasLineDerivAt 𝕜 f f' x v
参数：h : HasLineDerivWithinAt 𝕜 f f' s x v；hs : forallᶠ t : 𝕜 in 𝓝 0, x + t • v in
 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.hasDerivAt`：HasDerivWithinAt.hasDerivAt (h : HasDerivWi
thinAt f f' s x) (hs : s in 𝓝 x) : HasDerivAt f f' x
-/
theorem HasLineDerivWithinAt.hasLineDerivAt'
    (h : HasLineDerivWithinAt 𝕜 f f' s x v) (hs : ∀ᶠ t : 𝕜 in 𝓝 0, x + t • v ∈ s) :
    HasLineDerivAt 𝕜 f f' x v :=
  h.hasDerivAt hs

end Module

section NormedSpace

/-!
Results that need a normed space structure on `E`
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f f₀ f₁ : E → F} {f' : F} {s t : Set E} {x v : E} {L : E →L[𝕜] F}

/-
**HasLineDerivWithinAt.mono_of_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasLineDerivWithinAt.mono_of_mem_nhdsWithin (h : HasLineDerivWithinAt 𝕜 f 
f' t x v) (hst : t in 𝓝[s] x) : HasLineDerivWithinAt 𝕜 f f' s x v
参数：h : HasLineDerivWithinAt 𝕜 f f' t x v；hst : t in 𝓝[s] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.mono_of_mem_nhdsWithin`：HasDerivWithinAt.mono_of_mem_nh
dsWithin (h : HasDerivWithinAt f f' t x) (hst : t in 𝓝[s] x) : HasDerivWithinAt 
f f' s x
· 使用定理 `ContinuousWithinAt.preimage_mem_nhdsWithin''`：ContinuousWithinAt.preimag
e_mem_nhdsWithin'' {y : β} {s t : Set β} (h : ContinuousWithinAt f (f ⁻¹' s) x) 
(ht : t in 𝓝[s] y) (hxy : y = f x)…
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `Continuous.const_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [SeparatelyContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSp
ace X] {f …
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem HasLineDerivWithinAt.mono_of_mem_nhdsWithin
    (h : HasLineDerivWithinAt 𝕜 f f' t x v) (hst : t ∈ 𝓝[s] x) :
    HasLineDerivWithinAt 𝕜 f f' s x v := by
  apply HasDerivWithinAt.mono_of_mem_nhdsWithin h
  apply ContinuousWithinAt.preimage_mem_nhdsWithin'' _ hst (by simp)
  apply Continuous.continuousWithinAt; fun_prop
/-
**HasLineDerivWithinAt.hasLineDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasLineDerivWithinAt.hasLineDerivAt (h : HasLineDerivWithinAt 𝕜 f f' s x v
) (hs : s in 𝓝 x) : HasLineDerivAt 𝕜 f f' x v
参数：h : HasLineDerivWithinAt 𝕜 f f' s x v；hs : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasLineDerivWithinAt.hasLineDerivAt'`：HasLineDerivWithinAt.hasLineDerivA
t' (h : HasLineDerivWithinAt 𝕜 f f' s x v) (hs : forallᶠ t : 𝕜 in 𝓝 0, x + t • v
 in s) : HasLineDerivAt 𝕜 …
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `Continuous.const_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [SeparatelyContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSp
ace X] {f …
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem HasLineDerivWithinAt.hasLineDerivAt
    (h : HasLineDerivWithinAt 𝕜 f f' s x v) (hs : s ∈ 𝓝 x) :
    HasLineDerivAt 𝕜 f f' x v :=
  h.hasLineDerivAt' <| (Continuous.tendsto' (by fun_prop) 0 _ (by simp)).eventually hs
/-
**LineDifferentiableWithinAt.lineDifferentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LineDifferentiableWithinAt.lineDifferentiableAt (h : LineDifferentiableWit
hinAt 𝕜 f s x v) (hs : s in 𝓝 x) : LineDifferentiableAt 𝕜 f x v
参数：h : LineDifferentiableWithinAt 𝕜 f s x v；hs : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasLineDerivAt.lineDifferentiableAt`：HasLineDerivAt.lineDifferentiableAt
 (hf : HasLineDerivAt 𝕜 f f' x v) : LineDifferentiableAt 𝕜 f x v
· 使用定理 `HasLineDerivWithinAt.hasLineDerivAt`：HasLineDerivWithinAt.hasLineDerivAt
 (h : HasLineDerivWithinAt 𝕜 f f' s x v) (hs : s in 𝓝 x) : HasLineDerivAt 𝕜 f f'
 x v
· 使用定理 `LineDifferentiableWithinAt.hasLineDerivWithinAt`：LineDifferentiableWithi
nAt.hasLineDerivWithinAt (h : LineDifferentiableWithinAt 𝕜 f s x v) : HasLineDer
ivWithinAt 𝕜 f (lineDerivWithin 𝕜 f s…
-/
theorem LineDifferentiableWithinAt.lineDifferentiableAt (h : LineDifferentiableWithinAt 𝕜 f s x v)
    (hs : s ∈ 𝓝 x) : LineDifferentiableAt 𝕜 f x v :=
  (h.hasLineDerivWithinAt.hasLineDerivAt hs).lineDifferentiableAt
/-
**HasFDerivWithinAt.hasLineDerivWithinAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.hasLineDerivWithinAt (hf : HasFDerivWithinAt f L s x) (v
 : E) : HasLineDerivWithinAt 𝕜 f (L v) s x v
参数：hf : HasFDerivWithinAt f L s x；v : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `HasDerivAt.add`：HasDerivAt.add (hf : HasDerivAt f f' x) (hg : HasDerivAt
 g g' x) : HasDerivAt (f + g) (f' + g') x
· 使用定理 `hasDerivAt_const`：hasDerivAt_const : HasDerivAt (fun _ => c) 0 x
· 使用定理 `HasDerivAt.smul_const`：HasDerivAt.smul_const (hc : HasDerivAt c c' x) (f
 : F) : HasDerivAt (fun y => c y • f) (c' • f) x
· 使用定理 `hasDerivAt_id'`：hasDerivAt_id' : HasDerivAt (fun x : 𝕜 => x) 1 x
· 使用定理 `HasFDerivWithinAt.comp_hasDerivWithinAt`：HasFDerivWithinAt.comp_hasDeriv
WithinAt {t : Set F} (hl : HasFDerivWithinAt l l' t (f x)) (hf : HasDerivWithinA
t f f' s x) (hst : MapsTo f s…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasDerivWithinAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
-/
lemma HasFDerivWithinAt.hasLineDerivWithinAt (hf : HasFDerivWithinAt f L s x) (v : E) :
    HasLineDerivWithinAt 𝕜 f (L v) s x v := by
  let F := fun (t : 𝕜) ↦ x + t • v
  rw [show x = F (0 : 𝕜) by simp [F]] at hf
  have A : HasDerivWithinAt F (0 + (1 : 𝕜) • v) (F ⁻¹' s) 0 :=
    ((hasDerivAt_const (0 : 𝕜) x).add ((hasDerivAt_id' (0 : 𝕜)).smul_const v)).hasDerivWithinAt
  simp only [one_smul, zero_add] at A
  exact hf.comp_hasDerivWithinAt (x := (0 : 𝕜)) A (mapsTo_preimage F s)
/-
**DifferentiableWithinAt.lineDifferentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：DifferentiableWithinAt.lineDifferentiableWithinAt (hf : DifferentiableWith
inAt 𝕜 f s x) : LineDifferentiableWithinAt 𝕜 f s x v
参数：hf : DifferentiableWithinAt 𝕜 f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasLineDerivWithinAt.lineDifferentiableWithinAt`：HasLineDerivWithinAt.li
neDifferentiableWithinAt (hf : HasLineDerivWithinAt 𝕜 f f' s x v) : LineDifferen
tiableWithinAt 𝕜 f s x v
· 使用引理 `HasFDerivWithinAt.hasLineDerivWithinAt`：HasFDerivWithinAt.hasLineDerivWi
thinAt (hf : HasFDerivWithinAt f L s x) (v : E) : HasLineDerivWithinAt 𝕜 f (L v)
 s x v
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.lineDifferentiableWithinAt
    (hf : DifferentiableWithinAt 𝕜 f s x) :
    LineDifferentiableWithinAt 𝕜 f s x v :=
  hf.hasFDerivWithinAt.hasLineDerivWithinAt _ |>.lineDifferentiableWithinAt
/-
**HasFDerivAt.hasLineDerivAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasFDerivAt.hasLineDerivAt (hf : HasFDerivAt f L x) (v : E) : HasLineDeriv
At 𝕜 f (L v) x v
参数：hf : HasFDerivAt f L x；v : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasLineDerivWithinAt_univ`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type u_2} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 
F] {E : Type u_…
· 使用引理 `HasFDerivWithinAt.hasLineDerivWithinAt`：HasFDerivWithinAt.hasLineDerivWi
thinAt (hf : HasFDerivWithinAt f L s x) (v : E) : HasLineDerivWithinAt 𝕜 f (L v)
 s x v
· 使用定理 `HasFDerivAt.hasFDerivWithinAt`：HasFDerivAt.hasFDerivWithinAt (h : HasFDe
rivAt f f' x) : HasFDerivWithinAt f f' s x
-/
lemma HasFDerivAt.hasLineDerivAt (hf : HasFDerivAt f L x) (v : E) :
    HasLineDerivAt 𝕜 f (L v) x v := by
  rw [← hasLineDerivWithinAt_univ]
  exact hf.hasFDerivWithinAt.hasLineDerivWithinAt v
/-
**DifferentiableAt.lineDifferentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.lineDifferentiableAt (hf : DifferentiableAt 𝕜 f x) : Line
DifferentiableAt 𝕜 f x v
参数：hf : DifferentiableAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasLineDerivAt.lineDifferentiableAt`：HasLineDerivAt.lineDifferentiableAt
 (hf : HasLineDerivAt 𝕜 f f' x v) : LineDifferentiableAt 𝕜 f x v
· 使用引理 `HasFDerivAt.hasLineDerivAt`：HasFDerivAt.hasLineDerivAt (hf : HasFDerivAt
 f L x) (v : E) : HasLineDerivAt 𝕜 f (L v) x v
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.lineDifferentiableAt (hf : DifferentiableAt 𝕜 f x) :
    LineDifferentiableAt 𝕜 f x v :=
  hf.hasFDerivAt.hasLineDerivAt _ |>.lineDifferentiableAt
/-
**DifferentiableAt.lineDeriv_eq_fderiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DifferentiableAt.lineDeriv_eq_fderiv (hf : DifferentiableAt 𝕜 f x) : lineD
eriv 𝕜 f x v = fderiv 𝕜 f x v
参数：hf : DifferentiableAt 𝕜 f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasLineDerivAt.lineDeriv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {F : Type u_2} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F
] {E : Type u_…
· 使用引理 `HasFDerivAt.hasLineDerivAt`：HasFDerivAt.hasLineDerivAt (hf : HasFDerivAt
 f L x) (v : E) : HasLineDerivAt 𝕜 f (L v) x v
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
lemma DifferentiableAt.lineDeriv_eq_fderiv (hf : DifferentiableAt 𝕜 f x) :
    lineDeriv 𝕜 f x v = fderiv 𝕜 f x v :=
  (hf.hasFDerivAt.hasLineDerivAt v).lineDeriv
/-
**LineDifferentiableWithinAt.mono_of_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：LineDifferentiableWithinAt.mono_of_mem_nhdsWithin (h : LineDifferentiableW
ithinAt 𝕜 f s x v) (hst : s in 𝓝[t] x) : LineDifferentiableWithinAt 𝕜 f t x v
参数：h : LineDifferentiableWithinAt 𝕜 f s x v；hst : s in 𝓝[t] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasLineDerivWithinAt.lineDifferentiableWithinAt`：HasLineDerivWithinAt.li
neDifferentiableWithinAt (hf : HasLineDerivWithinAt 𝕜 f f' s x v) : LineDifferen
tiableWithinAt 𝕜 f s x v
· 使用定理 `HasLineDerivWithinAt.mono_of_mem_nhdsWithin`：HasLineDerivWithinAt.mono_o
f_mem_nhdsWithin (h : HasLineDerivWithinAt 𝕜 f f' t x v) (hst : t in 𝓝[s] x) : H
asLineDerivWithinAt 𝕜 f f' s x v
· 使用定理 `LineDifferentiableWithinAt.hasLineDerivWithinAt`：LineDifferentiableWithi
nAt.hasLineDerivWithinAt (h : LineDifferentiableWithinAt 𝕜 f s x v) : HasLineDer
ivWithinAt 𝕜 f (lineDerivWithin 𝕜 f s…
-/
theorem LineDifferentiableWithinAt.mono_of_mem_nhdsWithin (h : LineDifferentiableWithinAt 𝕜 f s x v)
    (hst : s ∈ 𝓝[t] x) : LineDifferentiableWithinAt 𝕜 f t x v :=
  (h.hasLineDerivWithinAt.mono_of_mem_nhdsWithin hst).lineDifferentiableWithinAt
/-
**lineDerivWithin_of_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lineDerivWithin_of_mem_nhds (h : s in 𝓝 x) : lineDerivWithin 𝕜 f s x v = l
ineDeriv 𝕜 f x v
参数：h : s in 𝓝 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `derivWithin_of_mem_nhds`：derivWithin_of_mem_nhds (h : s in 𝓝 x) : derivW
ithin f s x = deriv f x
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Continuous.const_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [SeparatelyContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSp
ace X] {f …
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem lineDerivWithin_of_mem_nhds (h : s ∈ 𝓝 x) :
    lineDerivWithin 𝕜 f s x v = lineDeriv 𝕜 f x v := by
  apply derivWithin_of_mem_nhds
  apply (Continuous.continuousAt _).preimage_mem_nhds (by simpa using h)
  fun_prop
/-
**lineDerivWithin_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lineDerivWithin_of_isOpen (hs : IsOpen s) (hx : x in s) : lineDerivWithin 
𝕜 f s x v = lineDeriv 𝕜 f x v
参数：hs : IsOpen s；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lineDerivWithin_of_mem_nhds`：lineDerivWithin_of_mem_nhds (h : s in 𝓝 x) 
: lineDerivWithin 𝕜 f s x v = lineDeriv 𝕜 f x v
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
theorem lineDerivWithin_of_isOpen (hs : IsOpen s) (hx : x ∈ s) :
    lineDerivWithin 𝕜 f s x v = lineDeriv 𝕜 f x v :=
  lineDerivWithin_of_mem_nhds (hs.mem_nhds hx)
/-
**hasLineDerivWithinAt_congr_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasLineDerivWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) : HasLineDerivWithinAt 𝕜 
f f' s x v ↔ HasLineDerivWithinAt 𝕜 f f' t x v
参数：h : s =ᶠ[𝓝 x] t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivWithinAt_congr_set`：hasDerivWithinAt_congr_set {s t : Set 𝕜} (h 
: s =ᶠ[𝓝 x] t) : HasDerivWithinAt f f' s x ↔ HasDerivWithinAt f f' t x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Continuous.const_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [SeparatelyContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSp
ace X] {f …
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
-/
theorem hasLineDerivWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) :
    HasLineDerivWithinAt 𝕜 f f' s x v ↔ HasLineDerivWithinAt 𝕜 f f' t x v := by
  apply hasDerivWithinAt_congr_set
  let F := fun (t : 𝕜) ↦ x + t • v
  have B : ContinuousAt F 0 := by apply Continuous.continuousAt; fun_prop
  have : s =ᶠ[𝓝 (F 0)] t := by convert! h; simp [F]
  exact B.preimage_mem_nhds this
/-
**lineDifferentiableWithinAt_congr_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lineDifferentiableWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) : LineDifferentiabl
eWithinAt 𝕜 f s x v ↔ LineDifferentiableWithinAt 𝕜 f t x v
参数：h : s =ᶠ[𝓝 x] t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasLineDerivWithinAt.lineDifferentiableWithinAt`：HasLineDerivWithinAt.li
neDifferentiableWithinAt (hf : HasLineDerivWithinAt 𝕜 f f' s x v) : LineDifferen
tiableWithinAt 𝕜 f s x v
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `hasLineDerivWithinAt_congr_set`：hasLineDerivWithinAt_congr_set (h : s =ᶠ
[𝓝 x] t) : HasLineDerivWithinAt 𝕜 f f' s x v ↔ HasLineDerivWithinAt 𝕜 f f' t x v
· 使用定理 `LineDifferentiableWithinAt.hasLineDerivWithinAt`：LineDifferentiableWithi
nAt.hasLineDerivWithinAt (h : LineDifferentiableWithinAt 𝕜 f s x v) : HasLineDer
ivWithinAt 𝕜 f (lineDerivWithin 𝕜 f s…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem lineDifferentiableWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) :
    LineDifferentiableWithinAt 𝕜 f s x v ↔ LineDifferentiableWithinAt 𝕜 f t x v :=
  ⟨fun h' ↦ ((hasLineDerivWithinAt_congr_set h).1
    h'.hasLineDerivWithinAt).lineDifferentiableWithinAt,
  fun h' ↦ ((hasLineDerivWithinAt_congr_set h.symm).1
    h'.hasLineDerivWithinAt).lineDifferentiableWithinAt⟩
/-
**lineDerivWithin_congr_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lineDerivWithin_congr_set (h : s =ᶠ[𝓝 x] t) : lineDerivWithin 𝕜 f s x v = 
lineDerivWithin 𝕜 f t x v
参数：h : s =ᶠ[𝓝 x] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `derivWithin_congr_set`：derivWithin_congr_set (h : s =ᶠ[𝓝 x] t) : derivWi
thin f s x = derivWithin f t x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Continuous.const_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [SeparatelyContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSp
ace X] {f …
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
-/
theorem lineDerivWithin_congr_set (h : s =ᶠ[𝓝 x] t) :
    lineDerivWithin 𝕜 f s x v = lineDerivWithin 𝕜 f t x v := by
  apply derivWithin_congr_set
  let F := fun (t : 𝕜) ↦ x + t • v
  have B : ContinuousAt F 0 := by apply Continuous.continuousAt; fun_prop
  have : s =ᶠ[𝓝 (F 0)] t := by convert! h; simp [F]
  exact B.preimage_mem_nhds this
/-
**Filter.EventuallyEq.hasLineDerivAt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.hasLineDerivAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) : HasLineDerivA
t 𝕜 f₀ f' x v ↔ HasLineDerivAt 𝕜 f₁ f' x v
参数：h : f₀ =ᶠ[𝓝 x] f₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.hasDerivAt_iff`：Filter.EventuallyEq.hasDerivAt_iff (
h : f₀ =ᶠ[𝓝 x] f₁) : HasDerivAt f₀ f' x ↔ HasDerivAt f₁ f' x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Continuous.const_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [SeparatelyContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSp
ace X] {f …
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
-/
theorem Filter.EventuallyEq.hasLineDerivAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) :
    HasLineDerivAt 𝕜 f₀ f' x v ↔ HasLineDerivAt 𝕜 f₁ f' x v := by
  apply hasDerivAt_iff
  let F := fun (t : 𝕜) ↦ x + t • v
  have B : ContinuousAt F 0 := by apply Continuous.continuousAt; fun_prop
  have : f₀ =ᶠ[𝓝 (F 0)] f₁ := by convert! h; simp [F]
  exact B.preimage_mem_nhds this
/-
**Filter.EventuallyEq.lineDifferentiableAt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.lineDifferentiableAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) : LineDif
ferentiableAt 𝕜 f₀ x v ↔ LineDifferentiableAt 𝕜 f₁ x v
参数：h : f₀ =ᶠ[𝓝 x] f₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasLineDerivAt.lineDifferentiableAt`：HasLineDerivAt.lineDifferentiableAt
 (hf : HasLineDerivAt 𝕜 f f' x v) : LineDifferentiableAt 𝕜 f x v
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.EventuallyEq.hasLineDerivAt_iff`：Filter.EventuallyEq.hasLineDeriv
At_iff (h : f₀ =ᶠ[𝓝 x] f₁) : HasLineDerivAt 𝕜 f₀ f' x v ↔ HasLineDerivAt 𝕜 f₁ f'
 x v
· 使用定理 `LineDifferentiableAt.hasLineDerivAt`：LineDifferentiableAt.hasLineDerivAt
 (h : LineDifferentiableAt 𝕜 f x v) : HasLineDerivAt 𝕜 f (lineDeriv 𝕜 f x v) x v
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem Filter.EventuallyEq.lineDifferentiableAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) :
    LineDifferentiableAt 𝕜 f₀ x v ↔ LineDifferentiableAt 𝕜 f₁ x v :=
  ⟨fun h' ↦ (h.hasLineDerivAt_iff.1 h'.hasLineDerivAt).lineDifferentiableAt,
  fun h' ↦ (h.hasLineDerivAt_iff.2 h'.hasLineDerivAt).lineDifferentiableAt⟩
/-
**Filter.EventuallyEq.hasLineDerivWithinAt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.hasLineDerivWithinAt_iff (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : 
f₀ x = f₁ x) : HasLineDerivWithinAt 𝕜 f₀ f' s x v ↔ HasLineDerivWithinAt 𝕜 f₁ f'
 s x v
参数：h : f₀ =ᶠ[𝓝[s] x] f₁；hx : f₀ x = f₁ x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.hasDerivWithinAt_iff`：Filter.EventuallyEq.hasDerivWi
thinAt_iff (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasDerivWithinAt f₁ f' s x
 ↔ HasDerivWithinAt f f' s x
· 使用定理 `Continuous.const_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [SeparatelyContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSp
ace X] {f …
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `ContinuousWithinAt.preimage_mem_nhdsWithin''`：ContinuousWithinAt.preimag
e_mem_nhdsWithin'' {y : β} {s t : Set β} (h : ContinuousWithinAt f (f ⁻¹' s) x) 
(ht : t in 𝓝[s] y) (hxy : y = f x)…
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem Filter.EventuallyEq.hasLineDerivWithinAt_iff (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x) :
    HasLineDerivWithinAt 𝕜 f₀ f' s x v ↔ HasLineDerivWithinAt 𝕜 f₁ f' s x v := by
  apply hasDerivWithinAt_iff
  · have A : Continuous (fun (t : 𝕜) ↦ x + t • v) := by fun_prop
    exact A.continuousWithinAt.preimage_mem_nhdsWithin'' h (by simp)
  · simpa using hx
/-
**Filter.EventuallyEq.hasLineDerivWithinAt_iff_of_mem** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：Filter.EventuallyEq.hasLineDerivWithinAt_iff_of_mem (h : f₀ =ᶠ[𝓝[s] x] f₁)
 (hx : x in s) : HasLineDerivWithinAt 𝕜 f₀ f' s x v ↔ HasLineDerivWithinAt 𝕜 f₁ 
f' s x v
参数：h : f₀ =ᶠ[𝓝[s] x] f₁；hx : x in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.hasLineDerivWithinAt_iff`：Filter.EventuallyEq.hasLin
eDerivWithinAt_iff (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x) : HasLineDerivWithi
nAt 𝕜 f₀ f' s x v ↔ HasLineDerivWi…
· 使用定理 `Filter.EventuallyEq.eq_of_nhdsWithin`：Filter.EventuallyEq.eq_of_nhdsWith
in {s : Set α} {f g : α -> β} {a : α} (h : f =ᶠ[𝓝[s] a] g) (hmem : a in s) : f a
 = g a
-/
theorem Filter.EventuallyEq.hasLineDerivWithinAt_iff_of_mem (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : x ∈ s) :
    HasLineDerivWithinAt 𝕜 f₀ f' s x v ↔ HasLineDerivWithinAt 𝕜 f₁ f' s x v :=
  h.hasLineDerivWithinAt_iff (h.eq_of_nhdsWithin hx)
/-
**Filter.EventuallyEq.lineDifferentiableWithinAt_iff** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：Filter.EventuallyEq.lineDifferentiableWithinAt_iff (h : f₀ =ᶠ[𝓝[s] x] f₁) 
(hx : f₀ x = f₁ x) : LineDifferentiableWithinAt 𝕜 f₀ s x v ↔ LineDifferentiableW
ithinAt 𝕜 f₁ s x v
参数：h : f₀ =ᶠ[𝓝[s] x] f₁；hx : f₀ x = f₁ x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasLineDerivWithinAt.lineDifferentiableWithinAt`：HasLineDerivWithinAt.li
neDifferentiableWithinAt (hf : HasLineDerivWithinAt 𝕜 f f' s x v) : LineDifferen
tiableWithinAt 𝕜 f s x v
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.EventuallyEq.hasLineDerivWithinAt_iff`：Filter.EventuallyEq.hasLin
eDerivWithinAt_iff (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x) : HasLineDerivWithi
nAt 𝕜 f₀ f' s x v ↔ HasLineDerivWi…
· 使用定理 `LineDifferentiableWithinAt.hasLineDerivWithinAt`：LineDifferentiableWithi
nAt.hasLineDerivWithinAt (h : LineDifferentiableWithinAt 𝕜 f s x v) : HasLineDer
ivWithinAt 𝕜 f (lineDerivWithin 𝕜 f s…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem Filter.EventuallyEq.lineDifferentiableWithinAt_iff
    (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x) :
    LineDifferentiableWithinAt 𝕜 f₀ s x v ↔ LineDifferentiableWithinAt 𝕜 f₁ s x v :=
  ⟨fun h' ↦ ((h.hasLineDerivWithinAt_iff hx).1 h'.hasLineDerivWithinAt).lineDifferentiableWithinAt,
  fun h' ↦ ((h.hasLineDerivWithinAt_iff hx).2 h'.hasLineDerivWithinAt).lineDifferentiableWithinAt⟩
/-
**Filter.EventuallyEq.lineDifferentiableWithinAt_iff_of_mem** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：Filter.EventuallyEq.lineDifferentiableWithinAt_iff_of_mem (h : f₀ =ᶠ[𝓝[s] 
x] f₁) (hx : x in s) : LineDifferentiableWithinAt 𝕜 f₀ s x v ↔ LineDifferentiabl
eWithinAt 𝕜 f₁ s x v
参数：h : f₀ =ᶠ[𝓝[s] x] f₁；hx : x in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.lineDifferentiableWithinAt_iff`：Filter.EventuallyEq.
lineDifferentiableWithinAt_iff (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x) : LineD
ifferentiableWithinAt 𝕜 f₀ s x v ↔ LineD…
· 使用定理 `Filter.EventuallyEq.eq_of_nhdsWithin`：Filter.EventuallyEq.eq_of_nhdsWith
in {s : Set α} {f g : α -> β} {a : α} (h : f =ᶠ[𝓝[s] a] g) (hmem : a in s) : f a
 = g a
-/
theorem Filter.EventuallyEq.lineDifferentiableWithinAt_iff_of_mem
    (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : x ∈ s) :
    LineDifferentiableWithinAt 𝕜 f₀ s x v ↔ LineDifferentiableWithinAt 𝕜 f₁ s x v :=
  h.lineDifferentiableWithinAt_iff (h.eq_of_nhdsWithin hx)
/-
**HasLineDerivWithinAt.congr_of_eventuallyEq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasLineDerivWithinAt.congr_of_eventuallyEq (hf : HasLineDerivWithinAt 𝕜 f 
f' s x v) (h'f : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasLineDerivWithinAt 𝕜 f₁ 
f' s x v
参数：hf : HasLineDerivWithinAt 𝕜 f f' s x v；h'f : f₁ =ᶠ[𝓝[s] x] f；hx : f₁ x = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.EventuallyEq.hasLineDerivWithinAt_iff`：Filter.EventuallyEq.hasLin
eDerivWithinAt_iff (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x) : HasLineDerivWithi
nAt 𝕜 f₀ f' s x v ↔ HasLineDerivWi…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma HasLineDerivWithinAt.congr_of_eventuallyEq (hf : HasLineDerivWithinAt 𝕜 f f' s x v)
    (h'f : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasLineDerivWithinAt 𝕜 f₁ f' s x v :=
  h'f.symm.hasLineDerivWithinAt_iff hx.symm |>.mp hf
/-
**HasLineDerivAt.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasLineDerivAt.congr_of_eventuallyEq (h : HasLineDerivAt 𝕜 f f' x v) (h₁ :
 f₁ =ᶠ[𝓝 x] f) : HasLineDerivAt 𝕜 f₁ f' x v
参数：h : HasLineDerivAt 𝕜 f f' x v；h₁ : f₁ =ᶠ[𝓝 x] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.EventuallyEq.hasLineDerivAt_iff`：Filter.EventuallyEq.hasLineDeriv
At_iff (h : f₀ =ᶠ[𝓝 x] f₁) : HasLineDerivAt 𝕜 f₀ f' x v ↔ HasLineDerivAt 𝕜 f₁ f'
 x v
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem HasLineDerivAt.congr_of_eventuallyEq (h : HasLineDerivAt 𝕜 f f' x v) (h₁ : f₁ =ᶠ[𝓝 x] f) :
    HasLineDerivAt 𝕜 f₁ f' x v :=
  (EventuallyEq.hasLineDerivAt_iff h₁.symm).mp h
/-
**LineDifferentiableWithinAt.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LineDifferentiableWithinAt.congr_of_eventuallyEq (h : LineDifferentiableWi
thinAt 𝕜 f s x v) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : LineDifferentiableW
ithinAt 𝕜 f₁ s x v
参数：h : LineDifferentiableWithinAt 𝕜 f s x v；h₁ : f₁ =ᶠ[𝓝[s] x] f；hx : f₁ x = f x
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.differentiableWithinAt`：HasDerivWithinAt.differentiable
WithinAt (h : HasDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用引理 `HasLineDerivWithinAt.congr_of_eventuallyEq`：HasLineDerivWithinAt.congr_o
f_eventuallyEq (hf : HasLineDerivWithinAt 𝕜 f f' s x v) (h'f : f₁ =ᶠ[𝓝[s] x] f) 
(hx : f₁ x = f x) : HasLineDeriv…
· 使用定理 `LineDifferentiableWithinAt.hasLineDerivWithinAt`：LineDifferentiableWithi
nAt.hasLineDerivWithinAt (h : LineDifferentiableWithinAt 𝕜 f s x v) : HasLineDer
ivWithinAt 𝕜 f (lineDerivWithin 𝕜 f s…
-/
theorem LineDifferentiableWithinAt.congr_of_eventuallyEq (h : LineDifferentiableWithinAt 𝕜 f s x v)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : LineDifferentiableWithinAt 𝕜 f₁ s x v :=
  (h.hasLineDerivWithinAt.congr_of_eventuallyEq h₁ hx).differentiableWithinAt
/-
**LineDifferentiableAt.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LineDifferentiableAt.congr_of_eventuallyEq (h : LineDifferentiableAt 𝕜 f x
 v) (hL : f₁ =ᶠ[𝓝 x] f) : LineDifferentiableAt 𝕜 f₁ x v
参数：h : LineDifferentiableAt 𝕜 f x v；hL : f₁ =ᶠ[𝓝 x] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.EventuallyEq.lineDifferentiableAt_iff`：Filter.EventuallyEq.lineDi
fferentiableAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) : LineDifferentiableAt 𝕜 f₀ x v ↔ LineDif
ferentiableAt 𝕜 f₁ x v
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem LineDifferentiableAt.congr_of_eventuallyEq
    (h : LineDifferentiableAt 𝕜 f x v) (hL : f₁ =ᶠ[𝓝 x] f) :
    LineDifferentiableAt 𝕜 f₁ x v :=
  hL.symm.lineDifferentiableAt_iff.mp h
/-
**Filter.EventuallyEq.lineDerivWithin_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.lineDerivWithin_eq (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x =
 f x) : lineDerivWithin 𝕜 f₁ s x v = lineDerivWithin 𝕜 f s x v
参数：hs : f₁ =ᶠ[𝓝[s] x] f；hx : f₁ x = f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.derivWithin_eq`：Filter.EventuallyEq.derivWithin_eq (
hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : derivWithin f₁ s x = derivWithin f s x
· 使用定理 `Continuous.const_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [SeparatelyContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSp
ace X] {f …
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `ContinuousWithinAt.preimage_mem_nhdsWithin''`：ContinuousWithinAt.preimag
e_mem_nhdsWithin'' {y : β} {s t : Set β} (h : ContinuousWithinAt f (f ⁻¹' s) x) 
(ht : t in 𝓝[s] y) (hxy : y = f x)…
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem Filter.EventuallyEq.lineDerivWithin_eq (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    lineDerivWithin 𝕜 f₁ s x v = lineDerivWithin 𝕜 f s x v := by
  apply derivWithin_eq ?_ (by simpa using hx)
  have A : Continuous (fun (t : 𝕜) ↦ x + t • v) := by fun_prop
  exact A.continuousWithinAt.preimage_mem_nhdsWithin'' hs (by simp)
/-
**Filter.EventuallyEq.lineDerivWithin_eq_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.lineDerivWithin_eq_nhds (h : f₁ =ᶠ[𝓝 x] f) : lineDeriv
Within 𝕜 f₁ s x v = lineDerivWithin 𝕜 f s x v
参数：h : f₁ =ᶠ[𝓝 x] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.lineDerivWithin_eq`：Filter.EventuallyEq.lineDerivWit
hin_eq (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : lineDerivWithin 𝕜 f₁ s x v = l
ineDerivWithin 𝕜 f s x v
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Filter.Eventually.self_of_nhds`：Filter.Eventually.self_of_nhds {p : X ->
 Prop} (h : forallᶠ y in 𝓝 x, p y) : p x
-/
theorem Filter.EventuallyEq.lineDerivWithin_eq_nhds (h : f₁ =ᶠ[𝓝 x] f) :
    lineDerivWithin 𝕜 f₁ s x v = lineDerivWithin 𝕜 f s x v :=
  (h.filter_mono nhdsWithin_le_nhds).lineDerivWithin_eq h.self_of_nhds
/-
**Filter.EventuallyEq.lineDeriv_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.lineDeriv_eq (h : f₁ =ᶠ[𝓝 x] f) : lineDeriv 𝕜 f₁ x v =
 lineDeriv 𝕜 f x v
参数：h : f₁ =ᶠ[𝓝 x] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lineDerivWithin_univ`：lineDerivWithin_univ : lineDerivWithin 𝕜 f univ x 
v = lineDeriv 𝕜 f x v
· 使用定理 `Filter.EventuallyEq.lineDerivWithin_eq_nhds`：Filter.EventuallyEq.lineDer
ivWithin_eq_nhds (h : f₁ =ᶠ[𝓝 x] f) : lineDerivWithin 𝕜 f₁ s x v = lineDerivWith
in 𝕜 f s x v
-/
theorem Filter.EventuallyEq.lineDeriv_eq (h : f₁ =ᶠ[𝓝 x] f) :
    lineDeriv 𝕜 f₁ x v = lineDeriv 𝕜 f x v := by
  rw [← lineDerivWithin_univ, ← lineDerivWithin_univ, h.lineDerivWithin_eq_nhds]

/-- Converse to the mean value inequality: if `f` is line differentiable at `x₀` and `C`-lipschitz
on a neighborhood of `x₀` then its line derivative at `x₀` in the direction `v` has norm
bounded by `C * ‖v‖`. This version only assumes that `‖f x - f x₀‖ ≤ C * ‖x - x₀‖` in a
neighborhood of `x`. -/
/-
**HasLineDerivAt.le_of_lip'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasLineDerivAt.le_of_lip' {f : E -> F} {f' : F} {x₀ : E} (hf : HasLineDeri
vAt 𝕜 f f' x₀ v) {C : Real} (hC₀ : 0 <= C) (hlip : forallᶠ x in 𝓝 x₀, ‖f x - f x
₀‖ <= C * ‖x - x₀‖) : ‖f'‖ <= C * ‖v‖
参数：hf : HasLineDerivAt 𝕜 f f' x₀ v；hC₀ : 0 <= C；hlip : forallᶠ x in 𝓝 x₀, ‖f x -
 f x₀‖ <= C * ‖x - x₀‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.le_of_lip'`：HasDerivAt.le_of_lip' {f : 𝕜 -> F} {f' : F} {x₀ :
 𝕜} (hf : HasDerivAt f f' x₀) {C : Real} (hC₀ : 0 <= C) (hlip : forallᶠ x in 𝓝 x
₀, ‖f x - f…
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Continuous.const_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [SeparatelyContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSp
ace X] {f …
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
Converse to the mean value inequality: if `f` is line differentiable at `x₀` and
 `C`-lipschitz
on a neighborhood of `x₀` then its line derivative at `x₀` in the direction `v` 
has norm
bounded by `C * ‖v‖`. This version only assumes that `‖f x - f x₀‖ ≤ C * ‖x - x₀
‖` in a
neighborhood of `x`.
-/
theorem HasLineDerivAt.le_of_lip' {f : E → F} {f' : F} {x₀ : E} (hf : HasLineDerivAt 𝕜 f f' x₀ v)
    {C : ℝ} (hC₀ : 0 ≤ C) (hlip : ∀ᶠ x in 𝓝 x₀, ‖f x - f x₀‖ ≤ C * ‖x - x₀‖) :
    ‖f'‖ ≤ C * ‖v‖ := by
  apply HasDerivAt.le_of_lip' hf (by positivity)
  have A : Continuous (fun (t : 𝕜) ↦ x₀ + t • v) := by fun_prop
  have : ∀ᶠ x in 𝓝 (x₀ + (0 : 𝕜) • v), ‖f x - f x₀‖ ≤ C * ‖x - x₀‖ := by simpa using hlip
  filter_upwards [(A.continuousAt (x := 0)).preimage_mem_nhds this] with t ht
  simp only [preimage_ofPred_eq, add_sub_cancel_left, norm_smul, mem_ofPred_eq,
    mul_comm (‖t‖)] at ht
  simpa [mul_assoc] using ht

/-- Converse to the mean value inequality: if `f` is line differentiable at `x₀` and `C`-lipschitz
on a neighborhood of `x₀` then its line derivative at `x₀` in the direction `v` has norm
bounded by `C * ‖v‖`. This version only assumes that `‖f x - f x₀‖ ≤ C * ‖x - x₀‖` in a
neighborhood of `x`. -/
/-
**HasLineDerivAt.le_of_lipschitzOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasLineDerivAt.le_of_lipschitzOn {f : E -> F} {f' : F} {x₀ : E} (hf : HasL
ineDerivAt 𝕜 f f' x₀ v) {s : Set E} (hs : s in 𝓝 x₀) {C : Real>=0} (hlip : Lipsc
hitzOnWith C f s) : ‖f'‖ <= C * ‖v‖
参数：hf : HasLineDerivAt 𝕜 f f' x₀ v；hs : s in 𝓝 x₀；hlip : LipschitzOnWith C f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasLineDerivAt.le_of_lip'`：HasLineDerivAt.le_of_lip' {f : E -> F} {f' : 
F} {x₀ : E} (hf : HasLineDerivAt 𝕜 f f' x₀ v) {C : Real} (hC₀ : 0 <= C) (hlip : 
forallᶠ x in 𝓝 …
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LipschitzOnWith.norm_sub_le`：∀ {E : Type u_2} {F : Type u_3} [inst : Sem
inormedAddCommGroup E] [inst_1 : SeminormedAddCommGroup F] {f : E → F}   {C : NN
Real} {s : Set E}…
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s

--- 原说明 ---
Converse to the mean value inequality: if `f` is line differentiable at `x₀` and
 `C`-lipschitz
on a neighborhood of `x₀` then its line derivative at `x₀` in the direction `v` 
has norm
bounded by `C * ‖v‖`. This version only assumes that `‖f x - f x₀‖ ≤ C * ‖x - x₀
‖` in a
neighborhood of `x`.
-/
theorem HasLineDerivAt.le_of_lipschitzOn
    {f : E → F} {f' : F} {x₀ : E} (hf : HasLineDerivAt 𝕜 f f' x₀ v)
    {s : Set E} (hs : s ∈ 𝓝 x₀) {C : ℝ≥0} (hlip : LipschitzOnWith C f s) :
    ‖f'‖ ≤ C * ‖v‖ := by
  refine hf.le_of_lip' C.coe_nonneg ?_
  filter_upwards [hs] with x hx using hlip.norm_sub_le hx (mem_of_mem_nhds hs)

/-- Converse to the mean value inequality: if `f` is line differentiable at `x₀` and `C`-lipschitz
then its line derivative at `x₀` in the direction `v` has norm bounded by `C * ‖v‖`. -/
/-
**HasLineDerivAt.le_of_lipschitz** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasLineDerivAt.le_of_lipschitz {f : E -> F} {f' : F} {x₀ : E} (hf : HasLin
eDerivAt 𝕜 f f' x₀ v) {C : Real>=0} (hlip : LipschitzWith C f) : ‖f'‖ <= C * ‖v‖
参数：hf : HasLineDerivAt 𝕜 f f' x₀ v；hlip : LipschitzWith C f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasLineDerivAt.le_of_lipschitzOn`：HasLineDerivAt.le_of_lipschitzOn {f : 
E -> F} {f' : F} {x₀ : E} (hf : HasLineDerivAt 𝕜 f f' x₀ v) {s : Set E} (hs : s 
in 𝓝 x₀) {C : Real>=0}…
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lipschitzOnWith_univ`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricS
pace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   LipschitzOnW
ith K f Se…

--- 原说明 ---
Converse to the mean value inequality: if `f` is line differentiable at `x₀` and
 `C`-lipschitz
then its line derivative at `x₀` in the direction `v` has norm bounded by `C * ‖
v‖`.
-/
theorem HasLineDerivAt.le_of_lipschitz
    {f : E → F} {f' : F} {x₀ : E} (hf : HasLineDerivAt 𝕜 f f' x₀ v)
    {C : ℝ≥0} (hlip : LipschitzWith C f) : ‖f'‖ ≤ C * ‖v‖ :=
  hf.le_of_lipschitzOn univ_mem (lipschitzOnWith_univ.2 hlip)

variable (𝕜)

/-- Converse to the mean value inequality: if `f` is `C`-lipschitz
on a neighborhood of `x₀` then its line derivative at `x₀` in the direction `v` has norm
bounded by `C * ‖v‖`. This version only assumes that `‖f x - f x₀‖ ≤ C * ‖x - x₀‖` in a
neighborhood of `x`.
Version using `lineDeriv`. -/
/-
**norm_lineDeriv_le_of_lip'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_lineDeriv_le_of_lip' {f : E -> F} {x₀ : E} {C : Real} (hC₀ : 0 <= C) 
(hlip : forallᶠ x in 𝓝 x₀, ‖f x - f x₀‖ <= C * ‖x - x₀‖) : ‖lineDeriv 𝕜 f x₀ v‖ 
<= C * ‖v‖
参数：hC₀ : 0 <= C；hlip : forallᶠ x in 𝓝 x₀, ‖f x - f x₀‖ <= C * ‖x - x₀‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_deriv_le_of_lip'`：norm_deriv_le_of_lip' {f : 𝕜 -> F} {x₀ : 𝕜} {C : 
Real} (hC₀ : 0 <= C) (hlip : forallᶠ x in 𝓝 x₀, ‖f x - f x₀‖ <= C * ‖x - x₀‖) : 
‖deriv f x₀…
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Continuous.const_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [SeparatelyContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSp
ace X] {f …
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
Converse to the mean value inequality: if `f` is `C`-lipschitz
on a neighborhood of `x₀` then its line derivative at `x₀` in the direction `v` 
has norm
bounded by `C * ‖v‖`. This version only assumes that `‖f x - f x₀‖ ≤ C * ‖x - x₀
‖` in a
neighborhood of `x`.
Version using `lineDeriv`.
-/
theorem norm_lineDeriv_le_of_lip' {f : E → F} {x₀ : E}
    {C : ℝ} (hC₀ : 0 ≤ C) (hlip : ∀ᶠ x in 𝓝 x₀, ‖f x - f x₀‖ ≤ C * ‖x - x₀‖) :
    ‖lineDeriv 𝕜 f x₀ v‖ ≤ C * ‖v‖ := by
  apply norm_deriv_le_of_lip' (by positivity)
  have A : Continuous (fun (t : 𝕜) ↦ x₀ + t • v) := by fun_prop
  have : ∀ᶠ x in 𝓝 (x₀ + (0 : 𝕜) • v), ‖f x - f x₀‖ ≤ C * ‖x - x₀‖ := by simpa using hlip
  filter_upwards [(A.continuousAt (x := 0)).preimage_mem_nhds this] with t ht
  simp only [preimage_ofPred_eq, add_sub_cancel_left, norm_smul, mem_ofPred_eq,
    mul_comm (‖t‖)] at ht
  simpa [mul_assoc] using ht

/-- Converse to the mean value inequality: if `f` is `C`-lipschitz on a neighborhood of `x₀`
then its line derivative at `x₀` in the direction `v` has norm bounded by `C * ‖v‖`.
Version using `lineDeriv`. -/
/-
**norm_lineDeriv_le_of_lipschitzOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_lineDeriv_le_of_lipschitzOn {f : E -> F} {x₀ : E} {s : Set E} (hs : s
 in 𝓝 x₀) {C : Real>=0} (hlip : LipschitzOnWith C f s) : ‖lineDeriv 𝕜 f x₀ v‖ <=
 C * ‖v‖
参数：hs : s in 𝓝 x₀；hlip : LipschitzOnWith C f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_lineDeriv_le_of_lip'`：norm_lineDeriv_le_of_lip' {f : E -> F} {x₀ : 
E} {C : Real} (hC₀ : 0 <= C) (hlip : forallᶠ x in 𝓝 x₀, ‖f x - f x₀‖ <= C * ‖x -
 x₀‖) : ‖lineDe…
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LipschitzOnWith.norm_sub_le`：∀ {E : Type u_2} {F : Type u_3} [inst : Sem
inormedAddCommGroup E] [inst_1 : SeminormedAddCommGroup F] {f : E → F}   {C : NN
Real} {s : Set E}…
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s

--- 原说明 ---
Converse to the mean value inequality: if `f` is `C`-lipschitz on a neighborhood
 of `x₀`
then its line derivative at `x₀` in the direction `v` has norm bounded by `C * ‖
v‖`.
Version using `lineDeriv`.
-/
theorem norm_lineDeriv_le_of_lipschitzOn {f : E → F} {x₀ : E} {s : Set E} (hs : s ∈ 𝓝 x₀)
    {C : ℝ≥0} (hlip : LipschitzOnWith C f s) : ‖lineDeriv 𝕜 f x₀ v‖ ≤ C * ‖v‖ := by
  refine norm_lineDeriv_le_of_lip' 𝕜 C.coe_nonneg ?_
  filter_upwards [hs] with x hx using hlip.norm_sub_le hx (mem_of_mem_nhds hs)

/-- Converse to the mean value inequality: if `f` is `C`-lipschitz then
its line derivative at `x₀` in the direction `v` has norm bounded by `C * ‖v‖`.
Version using `lineDeriv`. -/
/-
**norm_lineDeriv_le_of_lipschitz** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_lineDeriv_le_of_lipschitz {f : E -> F} {x₀ : E} {C : Real>=0} (hlip :
 LipschitzWith C f) : ‖lineDeriv 𝕜 f x₀ v‖ <= C * ‖v‖
参数：hlip : LipschitzWith C f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_lineDeriv_le_of_lipschitzOn`：norm_lineDeriv_le_of_lipschitzOn {f : 
E -> F} {x₀ : E} {s : Set E} (hs : s in 𝓝 x₀) {C : Real>=0} (hlip : LipschitzOnW
ith C f s) : ‖lineDeri…
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lipschitzOnWith_univ`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricS
pace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   LipschitzOnW
ith K f Se…

--- 原说明 ---
Converse to the mean value inequality: if `f` is `C`-lipschitz then
its line derivative at `x₀` in the direction `v` has norm bounded by `C * ‖v‖`.
Version using `lineDeriv`.
-/
theorem norm_lineDeriv_le_of_lipschitz {f : E → F} {x₀ : E}
    {C : ℝ≥0} (hlip : LipschitzWith C f) : ‖lineDeriv 𝕜 f x₀ v‖ ≤ C * ‖v‖ :=
  norm_lineDeriv_le_of_lipschitzOn 𝕜 univ_mem (lipschitzOnWith_univ.2 hlip)

end NormedSpace

section Zero

variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] {f : E → F} {s : Set E} {x : E}

/-
**hasLineDerivWithinAt_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasLineDerivWithinAt_zero : HasLineDerivWithinAt 𝕜 f 0 s x 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HasDerivWithinAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem hasLineDerivWithinAt_zero : HasLineDerivWithinAt 𝕜 f 0 s x 0 := by
  simp [HasLineDerivWithinAt, hasDerivWithinAt_const]
/-
**hasLineDerivAt_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasLineDerivAt_zero : HasLineDerivAt 𝕜 f 0 x 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem hasLineDerivAt_zero : HasLineDerivAt 𝕜 f 0 x 0 := by
  simp [HasLineDerivAt, hasDerivAt_const]
/-
**lineDifferentiableWithinAt_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lineDifferentiableWithinAt_zero : LineDifferentiableWithinAt 𝕜 f s x 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasLineDerivWithinAt.lineDifferentiableWithinAt`：HasLineDerivWithinAt.li
neDifferentiableWithinAt (hf : HasLineDerivWithinAt 𝕜 f f' s x v) : LineDifferen
tiableWithinAt 𝕜 f s x v
· 使用定理 `hasLineDerivWithinAt_zero`：hasLineDerivWithinAt_zero : HasLineDerivWithi
nAt 𝕜 f 0 s x 0
-/
theorem lineDifferentiableWithinAt_zero : LineDifferentiableWithinAt 𝕜 f s x 0 :=
  hasLineDerivWithinAt_zero.lineDifferentiableWithinAt
/-
**lineDifferentiableAt_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lineDifferentiableAt_zero : LineDifferentiableAt 𝕜 f x 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasLineDerivAt.lineDifferentiableAt`：HasLineDerivAt.lineDifferentiableAt
 (hf : HasLineDerivAt 𝕜 f f' x v) : LineDifferentiableAt 𝕜 f x v
· 使用定理 `hasLineDerivAt_zero`：hasLineDerivAt_zero : HasLineDerivAt 𝕜 f 0 x 0
-/
theorem lineDifferentiableAt_zero : LineDifferentiableAt 𝕜 f x 0 :=
  hasLineDerivAt_zero.lineDifferentiableAt
/-
**lineDeriv_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lineDeriv_zero : lineDeriv 𝕜 f x 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasLineDerivAt.lineDeriv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {F : Type u_2} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F
] {E : Type u_…
· 使用定理 `hasLineDerivAt_zero`：hasLineDerivAt_zero : HasLineDerivAt 𝕜 f 0 x 0
-/
theorem lineDeriv_zero : lineDeriv 𝕜 f x 0 = 0 :=
  hasLineDerivAt_zero.lineDeriv

end Zero

section CompRight

variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]
  {E' : Type*} [AddCommGroup E'] [Module 𝕜 E']
  {f : E → F} {f' : F} {x : E'} {L : E' →ₗ[𝕜] E}

/-
**HasLineDerivAt.of_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasLineDerivAt.of_comp {v : E'} (hf : HasLineDerivAt 𝕜 (f ∘ L) f' x v) : H
asLineDerivAt 𝕜 f f' (L x) (L v)
参数：hf : HasLineDerivAt 𝕜 (f ∘ L) f' x v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
-/
theorem HasLineDerivAt.of_comp {v : E'} (hf : HasLineDerivAt 𝕜 (f ∘ L) f' x v) :
    HasLineDerivAt 𝕜 f f' (L x) (L v) := by
  simpa [HasLineDerivAt] using hf
/-
**LineDifferentiableAt.of_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LineDifferentiableAt.of_comp {v : E'} (hf : LineDifferentiableAt 𝕜 (f ∘ L)
 x v) : LineDifferentiableAt 𝕜 f (L x) (L v)
参数：hf : LineDifferentiableAt 𝕜 (f ∘ L) x v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasLineDerivAt.lineDifferentiableAt`：HasLineDerivAt.lineDifferentiableAt
 (hf : HasLineDerivAt 𝕜 f f' x v) : LineDifferentiableAt 𝕜 f x v
· 使用定理 `HasLineDerivAt.of_comp`：HasLineDerivAt.of_comp {v : E'} (hf : HasLineDer
ivAt 𝕜 (f ∘ L) f' x v) : HasLineDerivAt 𝕜 f f' (L x) (L v)
· 使用定理 `LineDifferentiableAt.hasLineDerivAt`：LineDifferentiableAt.hasLineDerivAt
 (h : LineDifferentiableAt 𝕜 f x v) : HasLineDerivAt 𝕜 f (lineDeriv 𝕜 f x v) x v
-/
theorem LineDifferentiableAt.of_comp {v : E'} (hf : LineDifferentiableAt 𝕜 (f ∘ L) x v) :
    LineDifferentiableAt 𝕜 f (L x) (L v) :=
  hf.hasLineDerivAt.of_comp.lineDifferentiableAt

end CompRight

section SMul

variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] {f : E → F} {s : Set E} {x v : E} {f' : F}

/-
**HasLineDerivWithinAt.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasLineDerivWithinAt.smul (h : HasLineDerivWithinAt 𝕜 f f' s x v) (c : 𝕜) 
: HasLineDerivWithinAt 𝕜 f (c • f') s x (c • v)
参数：h : HasLineDerivWithinAt 𝕜 f f' s x v；c : 𝕜。
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
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `HasDerivAt.const_smul`：HasDerivAt.const_smul (c : R) (hf : HasDerivAt f 
f' x) : HasDerivAt (c • f) (c • f') x
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `hasDerivAt_id`：hasDerivAt_id : HasDerivAt id 1 x
· 使用定理 `HasDerivWithinAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `HasDerivWithinAt.scomp`：HasDerivWithinAt.scomp (hg : HasDerivWithinAt g₁
 g₁' t' (h x)) (hh : HasDerivWithinAt h h' s x) (hst : MapsTo h s t') : HasDeriv
WithinAt (g₁…
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem HasLineDerivWithinAt.smul (h : HasLineDerivWithinAt 𝕜 f f' s x v) (c : 𝕜) :
    HasLineDerivWithinAt 𝕜 f (c • f') s x (c • v) := by
  simp only [HasLineDerivWithinAt] at h ⊢
  let g := fun (t : 𝕜) ↦ c • t
  let s' := (fun (t : 𝕜) ↦ x + t • v) ⁻¹' s
  have A : HasDerivAt g c 0 := by simpa using! (hasDerivAt_id (0 : 𝕜)).const_smul c
  have B : HasDerivWithinAt (fun t ↦ f (x + t • v)) f' s' (g 0) := by simpa [g] using! h
  have Z := B.scomp (0 : 𝕜) A.hasDerivWithinAt (mapsTo_preimage g s')
  simp only [g, s', Function.comp_def, smul_eq_mul, mul_comm c, ← smul_smul] at Z
  convert! Z
  ext t
  simp [← smul_smul]
/-
**hasLineDerivWithinAt_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasLineDerivWithinAt_smul_iff {c : 𝕜} (hc : c != 0) : HasLineDerivWithinAt
 𝕜 f (c • f') s x (c • v) ↔ HasLineDerivWithinAt 𝕜 f f' s x v
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasLineDerivWithinAt.smul`：HasLineDerivWithinAt.smul (h : HasLineDerivWi
thinAt 𝕜 f f' s x v) (c : 𝕜) : HasLineDerivWithinAt 𝕜 f (c • f') s x (c • v)
-/
theorem hasLineDerivWithinAt_smul_iff {c : 𝕜} (hc : c ≠ 0) :
    HasLineDerivWithinAt 𝕜 f (c • f') s x (c • v) ↔ HasLineDerivWithinAt 𝕜 f f' s x v :=
  ⟨fun h ↦ by simpa [smul_smul, inv_mul_cancel₀ hc] using h.smul (c ⁻¹), fun h ↦ h.smul c⟩
/-
**HasLineDerivAt.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasLineDerivAt.smul (h : HasLineDerivAt 𝕜 f f' x v) (c : 𝕜) : HasLineDeriv
At 𝕜 f (c • f') x (c • v)
参数：h : HasLineDerivAt 𝕜 f f' x v；c : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasLineDerivWithinAt.smul`：HasLineDerivWithinAt.smul (h : HasLineDerivWi
thinAt 𝕜 f f' s x v) (c : 𝕜) : HasLineDerivWithinAt 𝕜 f (c • f') s x (c • v)
-/
theorem HasLineDerivAt.smul (h : HasLineDerivAt 𝕜 f f' x v) (c : 𝕜) :
    HasLineDerivAt 𝕜 f (c • f') x (c • v) := by
  simp only [← hasLineDerivWithinAt_univ] at h ⊢
  exact HasLineDerivWithinAt.smul h c
/-
**hasLineDerivAt_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasLineDerivAt_smul_iff {c : 𝕜} (hc : c != 0) : HasLineDerivAt 𝕜 f (c • f'
) x (c • v) ↔ HasLineDerivAt 𝕜 f f' x v
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasLineDerivAt.smul`：HasLineDerivAt.smul (h : HasLineDerivAt 𝕜 f f' x v)
 (c : 𝕜) : HasLineDerivAt 𝕜 f (c • f') x (c • v)
-/
theorem hasLineDerivAt_smul_iff {c : 𝕜} (hc : c ≠ 0) :
    HasLineDerivAt 𝕜 f (c • f') x (c • v) ↔ HasLineDerivAt 𝕜 f f' x v :=
  ⟨fun h ↦ by simpa [smul_smul, inv_mul_cancel₀ hc] using h.smul (c ⁻¹), fun h ↦ h.smul c⟩
/-
**LineDifferentiableWithinAt.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LineDifferentiableWithinAt.smul (h : LineDifferentiableWithinAt 𝕜 f s x v)
 (c : 𝕜) : LineDifferentiableWithinAt 𝕜 f s x (c • v)
参数：h : LineDifferentiableWithinAt 𝕜 f s x v；c : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasLineDerivWithinAt.lineDifferentiableWithinAt`：HasLineDerivWithinAt.li
neDifferentiableWithinAt (hf : HasLineDerivWithinAt 𝕜 f f' s x v) : LineDifferen
tiableWithinAt 𝕜 f s x v
· 使用定理 `HasLineDerivWithinAt.smul`：HasLineDerivWithinAt.smul (h : HasLineDerivWi
thinAt 𝕜 f f' s x v) (c : 𝕜) : HasLineDerivWithinAt 𝕜 f (c • f') s x (c • v)
· 使用定理 `LineDifferentiableWithinAt.hasLineDerivWithinAt`：LineDifferentiableWithi
nAt.hasLineDerivWithinAt (h : LineDifferentiableWithinAt 𝕜 f s x v) : HasLineDer
ivWithinAt 𝕜 f (lineDerivWithin 𝕜 f s…
-/
theorem LineDifferentiableWithinAt.smul (h : LineDifferentiableWithinAt 𝕜 f s x v) (c : 𝕜) :
    LineDifferentiableWithinAt 𝕜 f s x (c • v) :=
  (h.hasLineDerivWithinAt.smul c).lineDifferentiableWithinAt
/-
**lineDifferentiableWithinAt_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lineDifferentiableWithinAt_smul_iff {c : 𝕜} (hc : c != 0) : LineDifferenti
ableWithinAt 𝕜 f s x (c • v) ↔ LineDifferentiableWithinAt 𝕜 f s x v
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `LineDifferentiableWithinAt.smul`：LineDifferentiableWithinAt.smul (h : Li
neDifferentiableWithinAt 𝕜 f s x v) (c : 𝕜) : LineDifferentiableWithinAt 𝕜 f s x
 (c • v)
-/
theorem lineDifferentiableWithinAt_smul_iff {c : 𝕜} (hc : c ≠ 0) :
    LineDifferentiableWithinAt 𝕜 f s x (c • v) ↔ LineDifferentiableWithinAt 𝕜 f s x v :=
  ⟨fun h ↦ by simpa [smul_smul, inv_mul_cancel₀ hc] using h.smul (c ⁻¹), fun h ↦ h.smul c⟩
/-
**LineDifferentiableAt.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LineDifferentiableAt.smul (h : LineDifferentiableAt 𝕜 f x v) (c : 𝕜) : Lin
eDifferentiableAt 𝕜 f x (c • v)
参数：h : LineDifferentiableAt 𝕜 f x v；c : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasLineDerivAt.lineDifferentiableAt`：HasLineDerivAt.lineDifferentiableAt
 (hf : HasLineDerivAt 𝕜 f f' x v) : LineDifferentiableAt 𝕜 f x v
· 使用定理 `HasLineDerivAt.smul`：HasLineDerivAt.smul (h : HasLineDerivAt 𝕜 f f' x v)
 (c : 𝕜) : HasLineDerivAt 𝕜 f (c • f') x (c • v)
· 使用定理 `LineDifferentiableAt.hasLineDerivAt`：LineDifferentiableAt.hasLineDerivAt
 (h : LineDifferentiableAt 𝕜 f x v) : HasLineDerivAt 𝕜 f (lineDeriv 𝕜 f x v) x v
-/
theorem LineDifferentiableAt.smul (h : LineDifferentiableAt 𝕜 f x v) (c : 𝕜) :
    LineDifferentiableAt 𝕜 f x (c • v) :=
  (h.hasLineDerivAt.smul c).lineDifferentiableAt
/-
**lineDifferentiableAt_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lineDifferentiableAt_smul_iff {c : 𝕜} (hc : c != 0) : LineDifferentiableAt
 𝕜 f x (c • v) ↔ LineDifferentiableAt 𝕜 f x v
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `LineDifferentiableAt.smul`：LineDifferentiableAt.smul (h : LineDifferenti
ableAt 𝕜 f x v) (c : 𝕜) : LineDifferentiableAt 𝕜 f x (c • v)
-/
theorem lineDifferentiableAt_smul_iff {c : 𝕜} (hc : c ≠ 0) :
    LineDifferentiableAt 𝕜 f x (c • v) ↔ LineDifferentiableAt 𝕜 f x v :=
  ⟨fun h ↦ by simpa [smul_smul, inv_mul_cancel₀ hc] using h.smul (c ⁻¹), fun h ↦ h.smul c⟩
/-
**lineDeriv_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lineDeriv_smul {c : 𝕜} : lineDeriv 𝕜 f x (c • v) = c • lineDeriv 𝕜 f x v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `lineDeriv_zero`：lineDeriv_zero : lineDeriv 𝕜 f x 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasLineDerivAt.lineDeriv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {F : Type u_2} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F
] {E : Type u_…
· 使用定理 `HasLineDerivAt.smul`：HasLineDerivAt.smul (h : HasLineDerivAt 𝕜 f f' x v)
 (c : 𝕜) : HasLineDerivAt 𝕜 f (c • f') x (c • v)
· 使用定理 `LineDifferentiableAt.hasLineDerivAt`：LineDifferentiableAt.hasLineDerivAt
 (h : LineDifferentiableAt 𝕜 f x v) : HasLineDerivAt 𝕜 f (lineDeriv 𝕜 f x v) x v
· 使用定理 `lineDifferentiableAt_smul_iff`：lineDifferentiableAt_smul_iff {c : 𝕜} (hc
 : c != 0) : LineDifferentiableAt 𝕜 f x (c • v) ↔ LineDifferentiableAt 𝕜 f x v
· 使用定理 `lineDeriv_zero_of_not_lineDifferentiableAt`：lineDeriv_zero_of_not_lineDi
fferentiableAt (h : ¬LineDifferentiableAt 𝕜 f x v) : lineDeriv 𝕜 f x v = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem lineDeriv_smul {c : 𝕜} : lineDeriv 𝕜 f x (c • v) = c • lineDeriv 𝕜 f x v := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [lineDeriv_zero]
  by_cases H : LineDifferentiableAt 𝕜 f x v
  · exact (H.hasLineDerivAt.smul c).lineDeriv
  · have H' : ¬ (LineDifferentiableAt 𝕜 f x (c • v)) := by
      simpa [lineDifferentiableAt_smul_iff hc] using H
    simp [lineDeriv_zero_of_not_lineDifferentiableAt, H, H']
/-
**lineDeriv_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lineDeriv_neg : lineDeriv 𝕜 f x (-v) = - lineDeriv 𝕜 f x v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_one_smul`：neg_one_smul (x : M) : (-1 : R) • x = -x
· 使用定理 `lineDeriv_smul`：lineDeriv_smul {c : 𝕜} : lineDeriv 𝕜 f x (c • v) = c • l
ineDeriv 𝕜 f x v
-/
theorem lineDeriv_neg : lineDeriv 𝕜 f x (-v) = - lineDeriv 𝕜 f x v := by
  rw [← neg_one_smul (R := 𝕜) v, lineDeriv_smul, neg_one_smul]

end SMul

