/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Operator.Asymptotics
public import Mathlib.Analysis.Calculus.TangentCone.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.TangentCone.DimOne

/-!
# The Fréchet derivative: basic properties

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

## Main results

This file builds on the bare-bones definition given in `Defs.lean` by establishing a variety of
relatively straightforward properties of the derivative.

Deeper properties are defined in other files in the folder `Analysis/Calculus/FDeriv/`, which
contain the usual formulas (and existence assertions) for the derivative of
* constants (`Const.lean`)
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

For most binary operations we also define `const_op` and `op_const` theorems for the cases when
the first or second argument is a constant. This makes writing chains of `HasDerivAt`'s easier,
and they more frequently lead to the desired result.

One can also interpret the derivative of a function `f : 𝕜 → E` as an element of `E` (by identifying
a linear function from `𝕜` to `E` with its value at `1`). Results on the Fréchet derivative are
translated to this more elementary point of view on the derivative in the file `Deriv.lean`. The
derivative of polynomials is handled there, as it is naturally one-dimensional.

The simplifier is set up to prove automatically that some functions are differentiable, or
differentiable at a point (but not differentiable on a set or within a set at a point, as checking
automatically that the good domains are mapped one to the other when using composition is not
something the simplifier can easily do). This means that one can write
`example (x : ℝ) : Differentiable ℝ (fun x ↦ sin (exp (3 + x^2)) - 5 * cos x) := by simp`.
If there are divisions, one needs to supply to the simplifier proofs that the denominators do
not vanish, as in
```lean
example (x : ℝ) (h : 1 + sin x ≠ 0) : DifferentiableAt ℝ (fun x ↦ exp x / (1 + sin x)) x := by
  simp [h]
```
Of course, these examples only work once `exp`, `cos` and `sin` have been shown to be
differentiable, in `Mathlib/Analysis/SpecialFunctions/Trigonometric/Deriv.lean`.

The simplifier is not set up to compute the Fréchet derivative of maps (as these are in general
complicated multidimensional linear maps), but it will compute one-dimensional derivatives,
see `Deriv.lean`.

## Implementation details

For a discussion of the definitions and their rationale, see the file docstring of
`Mathlib.Analysis.Calculus.FDeriv.Defs`.

To make sure that the simplifier can prove automatically that functions are differentiable, we tag
many lemmas with the `simp` attribute, for instance those saying that the sum of differentiable
functions is differentiable, as well as their product, their Cartesian product, and so on. A notable
exception is the chain rule: we do not mark as a simp lemma the fact that, if `f` and `g` are
differentiable, then their composition also is: `simp` would always be able to match this lemma,
by taking `f` or `g` to be the identity. Instead, for every reasonable function (say, `exp`),
we add a lemma that if `f` is differentiable then so is `(fun x ↦ exp (f x))`. This means adding
some boilerplate lemmas, but these can also be useful in their own right.

## TODO

Generalize more results to topological vector spaces.

## Tags

derivative, differentiable, Fréchet, calculus

-/

public section

open Filter Asymptotics ContinuousLinearMap Set Metric Topology NNReal ENNReal

noncomputable section

section
section DerivativeUniqueness
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul 𝕜 E]
variable {F : Type*} [AddCommGroup F] [Module 𝕜 F]
  [TopologicalSpace F] [ContinuousAdd F] [ContinuousSMul 𝕜 F]

variable {f : E → F}
variable {f' f₁' : E →L[𝕜] F}
variable {x : E}
variable {s : Set E}

/-!
### Uniqueness of the derivative

In this section, we discuss the uniqueness of the derivative.
We prove that the definitions `UniqueDiffWithinAt` and `UniqueDiffOn` indeed imply the
uniqueness of the derivative. -/

/-- If a function f has a derivative f' at x, a rescaled version of f around x converges to f',
i.e., `n (f (x + (1/n) v) - f x)` converges to `f' v`. More generally, if `d n` tends to zero
and `c n * d n` tends to `v`, then `c n * (f (x + d n) - f x)` tends to `f' v`. This lemma expresses
this fact, for functions having a derivative within a set. Its specific formulation is useful for
tangent cone related discussions. -/
/-
**HasFDerivWithinAt.lim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.lim (h : HasFDerivWithinAt f f' s x) {α : Type*} {l : Fi
lter α} {c : α -> 𝕜} {d : α -> E} {v : E} (dlim : Tendsto d l (𝓝 0)) (dtop : for
allᶠ n in l, x + d n in s) (cdlim : Tendsto (fun n => c n • d n) l (𝓝 v)) : Tend
sto (fun n => c n • (f (x + d n) - f x)) l (𝓝 (f' v))
参数：h : HasFDerivWithinAt f f' s x；dlim : Tendsto d l (𝓝 0)；dtop : forallᶠ n in l
, x + d n in s；cdlim : Tendsto (fun n => c n • d n) l (𝓝 v)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_nhdsWithin_iff`：tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s
 : Set α} {f : β -> α} : Tendsto f l (𝓝[s] a) ↔ Tendsto f l (𝓝 a) ∧ forallᶠ n in
 l, f n in s
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `Asymptotics.IsLittleOTVS.smul_left`：∀ {α : Type u_1} {𝕜 : Type u_3} {E :
 Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddComm
Group E] [inst_2 : Topol…
· 使用定理 `Asymptotics.IsLittleOTVS.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {
𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]  
 [inst_1 : AddCommGroup E] …
· 使用定理 `HasFDerivWithinAt.isLittleOTVS`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `Asymptotics.Filter.Tendsto.isBigOTVS_one`：∀ {α : Type u_1} (𝕜 : Type u_3
) {E : Type u_4} [inst : NontriviallyNormedField 𝕜] [inst_1 : AddCommGroup E]   
[inst_2 : TopologicalSpace E] …
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `Asymptotics.isLittleOTVS_one`：isLittleOTVS_one [ContinuousSMul 𝕜 E] : f 
=o[𝕜; l] (1 : α -> 𝕜) ↔ Tendsto f l (𝓝 0)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…

--- 原说明 ---
If a function f has a derivative f' at x, a rescaled version of f around x conve
rges to f',
i.e., `n (f (x + (1/n) v) - f x)` converges to `f' v`. More generally, if `d n` 
tends to zero
and `c n * d n` tends to `v`, then `c n * (f (x + d n) - f x)` tends to `f' v`. 
This lemma expresses
this fact, for functions having a derivative within a set. Its specific formulat
ion is useful for
tangent cone related discussions.
-/
theorem HasFDerivWithinAt.lim (h : HasFDerivWithinAt f f' s x) {α : Type*} {l : Filter α}
    {c : α → 𝕜} {d : α → E} {v : E} (dlim : Tendsto d l (𝓝 0)) (dtop : ∀ᶠ n in l, x + d n ∈ s)
    (cdlim : Tendsto (fun n => c n • d n) l (𝓝 v)) :
    Tendsto (fun n => c n • (f (x + d n) - f x)) l (𝓝 (f' v)) := by
  have tendsto_arg : Tendsto (fun n => x + d n) l (𝓝[s] x) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨by simpa using tendsto_const_nhds.add dlim, dtop⟩
  have := calc
    (fun n ↦ c n • (f (x + d n) - f x) - f' (c n • d n)) =o[𝕜; l] fun n ↦ c n • d n := by
      simpa [smul_sub] using h.isLittleOTVS.comp_tendsto tendsto_arg |>.smul_left c
    _ =O[𝕜; l] (1 : α → 𝕜) := cdlim.isBigOTVS_one _
  rw [isLittleOTVS_one] at this
  simpa using this.add <| ((map_continuous f').tendsto v).comp cdlim

variable [T2Space F]

/-- If `f'` and `f₁'` are two derivatives of `f` within `s` at `x`, then they are equal on the
tangent cone to `s` at `x` -/
/-
**HasFDerivWithinAt.unique_on** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.unique_on (hf : HasFDerivWithinAt f f' s x) (hg : HasFDe
rivWithinAt f f₁' s x) : EqOn f' f₁' (tangentConeAt 𝕜 s x)
参数：hf : HasFDerivWithinAt f f' s x；hg : HasFDerivWithinAt f f₁' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_fun_of_mem_tangentConeAt`：exists_fun_of_mem_tangentConeAt (h : y 
in tangentConeAt R s x) : exists (α : Type (max u v)) (l : Filter α) (_hl : l.Ne
Bot) (c : α -> R) (d …
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `HasFDerivWithinAt.lim`：HasFDerivWithinAt.lim (h : HasFDerivWithinAt f f'
 s x) {α : Type*} {l : Filter α} {c : α -> 𝕜} {d : α -> E} {v : E} (dlim : Tends
to d l (𝓝 0…

--- 原说明 ---
If `f'` and `f₁'` are two derivatives of `f` within `s` at `x`, then they are eq
ual on the
tangent cone to `s` at `x`
-/
theorem HasFDerivWithinAt.unique_on (hf : HasFDerivWithinAt f f' s x)
    (hg : HasFDerivWithinAt f f₁' s x) : EqOn f' f₁' (tangentConeAt 𝕜 s x) := by
  intro y hy
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  exact tendsto_nhds_unique (hf.lim hd₀ hds hcd) (hg.lim hd₀ hds hcd)

/-- `UniqueDiffWithinAt` achieves its goal: it implies the uniqueness of the derivative. -/
/-
**UniqueDiffWithinAt.eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueDiffWithinAt.eq (H : UniqueDiffWithinAt 𝕜 s x) (hf : HasFDerivWithin
At f f' s x) (hg : HasFDerivWithinAt f f₁' s x) : f' = f₁'
参数：H : UniqueDiffWithinAt 𝕜 s x；hf : HasFDerivWithinAt f f' s x；hg : HasFDerivWi
thinAt f f₁' s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext_on`：ext_on [T2Space M₂] {s : Set M₁} (hs : Dense
 (Submodule.span R₁ s : Set M₁)) {f g : M₁ ->SL[σ₁₂] M₂} (h : Set.EqOn f g s) : 
f = g
· 使用定理 `UniqueDiffWithinAt.dense_tangentConeAt`：∀ {R : Type u} {E : Type v} [ins
t : Semiring R] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module R E]   [inst_3
 : TopologicalSpace E] {s : …
· 使用定理 `HasFDerivWithinAt.unique_on`：HasFDerivWithinAt.unique_on (hf : HasFDeriv
WithinAt f f' s x) (hg : HasFDerivWithinAt f f₁' s x) : EqOn f' f₁' (tangentCone
At 𝕜 s x)

--- 原说明 ---
`UniqueDiffWithinAt` achieves its goal: it implies the uniqueness of the derivat
ive.
-/
theorem UniqueDiffWithinAt.eq (H : UniqueDiffWithinAt 𝕜 s x) (hf : HasFDerivWithinAt f f' s x)
    (hg : HasFDerivWithinAt f f₁' s x) : f' = f₁' :=
  ContinuousLinearMap.ext_on H.1 (hf.unique_on hg)
/-
**UniqueDiffOn.eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueDiffOn.eq (H : UniqueDiffOn 𝕜 s) (hx : x in s) (h : HasFDerivWithinA
t f f' s x) (h₁ : HasFDerivWithinAt f f₁' s x) : f' = f₁'
参数：H : UniqueDiffOn 𝕜 s；hx : x in s；h : HasFDerivWithinAt f f' s x；h₁ : HasFDeri
vWithinAt f f₁' s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueDiffWithinAt.eq`：UniqueDiffWithinAt.eq (H : UniqueDiffWithinAt 𝕜 s
 x) (hf : HasFDerivWithinAt f f' s x) (hg : HasFDerivWithinAt f f₁' s x) : f' = 
f₁'
-/
theorem UniqueDiffOn.eq (H : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (h : HasFDerivWithinAt f f' s x)
    (h₁ : HasFDerivWithinAt f f₁' s x) : f' = f₁' :=
  (H x hx).eq h h₁
/-
**HasFDerivAt.unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.unique (h₀ : HasFDerivAt f f' x) (h₁ : HasFDerivAt f f₁' x) : 
f' = f₁'
参数：h₀ : HasFDerivAt f f' x；h₁ : HasFDerivAt f f₁' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueDiffWithinAt.eq`：UniqueDiffWithinAt.eq (H : UniqueDiffWithinAt 𝕜 s
 x) (hf : HasFDerivWithinAt f f' s x) (hg : HasFDerivWithinAt f f₁' s x) : f' = 
f₁'
· 使用定理 `uniqueDiffWithinAt_univ`：uniqueDiffWithinAt_univ : UniqueDiffWithinAt 𝕜 
univ x
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `HasFDerivAt.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E
 : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : 
Topolo…
-/
theorem HasFDerivAt.unique (h₀ : HasFDerivAt f f' x) (h₁ : HasFDerivAt f f₁' x) : f' = f₁' := by
  rw [HasFDerivAt, ← nhdsWithin_univ] at *
  exact uniqueDiffWithinAt_univ.eq h₀ h₁

end DerivativeUniqueness

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

variable {f f₀ f₁ g : E → F}
variable {f' f₀' f₁' g' : E →L[𝕜] F}
variable {x : E}
variable {s t : Set E}
variable {L L₁ L₂ : Filter (E × E)}

section FDerivProperties

/-! ### Basic properties of the derivative -/

nonrec theorem HasFDerivAtFilter.mono (h : HasFDerivAtFilter f f' L₂) (hst : L₁ ≤ L₂) :
    HasFDerivAtFilter f f' L₁ :=
  .of_isLittleOTVS <| h.isLittleOTVS.mono hst

/-
**HasFDerivWithinAt.mono_of_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.mono_of_mem_nhdsWithin (h : HasFDerivWithinAt f f' t x) 
(hst : t in 𝓝[s] x) : HasFDerivWithinAt f f' s x
参数：h : HasFDerivWithinAt f f' t x；hst : t in 𝓝[s] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.mono`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [ins
t_3 : Topolo…
· 使用定理 `Filter.prod_mono_left`：prod_mono_left (g : Filter β) {f₁ f₂ : Filter α} 
(hf : f₁ <= f₂) : f₁ ×ˢ g <= f₂ ×ˢ g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nhdsWithin_le_iff`：nhdsWithin_le_iff {s t : Set α} {x : α} : 𝓝[s] x <= 𝓝
[t] x ↔ t in 𝓝[s] x
-/
theorem HasFDerivWithinAt.mono_of_mem_nhdsWithin
    (h : HasFDerivWithinAt f f' t x) (hst : t ∈ 𝓝[s] x) :
    HasFDerivWithinAt f f' s x :=
  h.mono <| prod_mono_left _ (nhdsWithin_le_iff.mpr hst)

nonrec theorem HasFDerivWithinAt.mono (h : HasFDerivWithinAt f f' t x) (hst : s ⊆ t) :
    HasFDerivWithinAt f f' s x :=
  h.mono <| by gcongr
/-
**HasFDerivAt.hasFDerivAtFilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.hasFDerivAtFilter (h : HasFDerivAt f f' x) (hL : L <= 𝓝 x ×ˢ p
ure x) : HasFDerivAtFilter f f' L
参数：h : HasFDerivAt f f' x；hL : L <= 𝓝 x ×ˢ pure x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.mono`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [ins
t_3 : Topolo…
-/
theorem HasFDerivAt.hasFDerivAtFilter (h : HasFDerivAt f f' x) (hL : L ≤ 𝓝 x ×ˢ pure x) :
    HasFDerivAtFilter f f' L :=
  h.mono hL

@[fun_prop]
/-
**HasFDerivAt.hasFDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.hasFDerivWithinAt (h : HasFDerivAt f f' x) : HasFDerivWithinAt
 f f' s x
参数：h : HasFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.hasFDerivAtFilter`：HasFDerivAt.hasFDerivAtFilter (h : HasFDe
rivAt f f' x) (hL : L <= 𝓝 x ×ˢ pure x) : HasFDerivAtFilter f f' L
· 使用定理 `Filter.prod_mono_left`：prod_mono_left (g : Filter β) {f₁ f₂ : Filter α} 
(hf : f₁ <= f₂) : f₁ ×ˢ g <= f₂ ×ˢ g
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
-/
theorem HasFDerivAt.hasFDerivWithinAt (h : HasFDerivAt f f' x) : HasFDerivWithinAt f f' s x :=
  h.hasFDerivAtFilter <| prod_mono_left _ nhdsWithin_le_nhds

@[fun_prop]
/-
**HasFDerivWithinAt.differentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.differentiableWithinAt (h : HasFDerivWithinAt f f' s x) 
: DifferentiableWithinAt 𝕜 f s x
参数：h : HasFDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasFDerivWithinAt.differentiableWithinAt (h : HasFDerivWithinAt f f' s x) :
    DifferentiableWithinAt 𝕜 f s x :=
  ⟨f', h⟩

@[fun_prop]
/-
**HasFDerivAt.differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.differentiableAt (h : HasFDerivAt f f' x) : DifferentiableAt 𝕜
 f x
参数：h : HasFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasFDerivAt.differentiableAt (h : HasFDerivAt f f' x) : DifferentiableAt 𝕜 f x :=
  ⟨f', h⟩

@[simp]
/-
**hasFDerivWithinAt_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_univ : HasFDerivWithinAt f f' univ x ↔ HasFDerivAt f f' 
x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasFDerivWithinAt_univ : HasFDerivWithinAt f f' univ x ↔ HasFDerivAt f f' x := by
  simp only [HasFDerivWithinAt, nhdsWithin_univ, HasFDerivAt]

alias ⟨HasFDerivWithinAt.hasFDerivAt_of_univ, _⟩ := hasFDerivWithinAt_univ
/-
**differentiableWithinAt_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_univ : DifferentiableWithinAt 𝕜 f univ x ↔ Differen
tiableAt 𝕜 f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem differentiableWithinAt_univ :
    DifferentiableWithinAt 𝕜 f univ x ↔ DifferentiableAt 𝕜 f x := by
  simp only [DifferentiableWithinAt, hasFDerivWithinAt_univ, DifferentiableAt]
/-
**fderiv_zero_of_not_differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_zero_of_not_differentiableAt (h : ¬DifferentiableAt 𝕜 f x) : fderiv
 𝕜 f x = 0
参数：h : ¬DifferentiableAt 𝕜 f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderiv_def`：∀ (𝕜 : Type u_4) [inst : NontriviallyNormedField 𝕜] {E : Typ
e u_5} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : Topolo
…
· 使用定理 `fderivWithin_zero_of_not_differentiableWithinAt`：fderivWithin_zero_of_no
t_differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) : fderivWithin 𝕜 
f s x = 0
· 使用定理 `differentiableWithinAt_univ`：differentiableWithinAt_univ : Differentiabl
eWithinAt 𝕜 f univ x ↔ DifferentiableAt 𝕜 f x
-/
theorem fderiv_zero_of_not_differentiableAt (h : ¬DifferentiableAt 𝕜 f x) : fderiv 𝕜 f x = 0 := by
  rw [fderiv, fderivWithin_zero_of_not_differentiableWithinAt]
  rwa [differentiableWithinAt_univ]
/-
**hasFDerivWithinAt_of_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_of_mem_nhds (h : s in 𝓝 x) : HasFDerivWithinAt f f' s x 
↔ HasFDerivAt f f' x
参数：h : s in 𝓝 x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasFDerivAt.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E
 : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : 
Topolo…
· 使用定理 `HasFDerivWithinAt.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [ins
t_3 : Topolo…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nhdsWithin_eq_nhds`：∀ {α : Type u_1} [inst : TopologicalSpace α] {a : α}
 {s : Set α}, nhdsWithin a s = nhds a ↔ s ∈ nhds a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem hasFDerivWithinAt_of_mem_nhds (h : s ∈ 𝓝 x) :
    HasFDerivWithinAt f f' s x ↔ HasFDerivAt f f' x := by
  rw [HasFDerivAt, HasFDerivWithinAt, nhdsWithin_eq_nhds.mpr h]
/-
**hasFDerivWithinAt_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_of_isOpen (h : IsOpen s) (hx : x in s) : HasFDerivWithin
At f f' s x ↔ HasFDerivAt f f' x
参数：h : IsOpen s；hx : x in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivWithinAt_of_mem_nhds`：hasFDerivWithinAt_of_mem_nhds (h : s in 𝓝
 x) : HasFDerivWithinAt f f' s x ↔ HasFDerivAt f f' x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
lemma hasFDerivWithinAt_of_isOpen (h : IsOpen s) (hx : x ∈ s) :
    HasFDerivWithinAt f f' s x ↔ HasFDerivAt f f' x :=
  hasFDerivWithinAt_of_mem_nhds (h.mem_nhds hx)

@[simp]
/-
**hasFDerivWithinAt_insert_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_insert_self : HasFDerivWithinAt f f' (insert x s) x ↔ Ha
sFDerivWithinAt f f' s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Asymptotics.isLittleOTVS_insert`：isLittleOTVS_insert [TopologicalSpace α
] {x : α} {s : Set α} (h : f x = 0) : f =o[𝕜; 𝓝[insert x s] x] g ↔ f =o[𝕜; (𝓝[s]
 x)] g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
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
theorem hasFDerivWithinAt_insert_self :
    HasFDerivWithinAt f f' (insert x s) x ↔ HasFDerivWithinAt f f' s x := by
  simp_rw [hasFDerivWithinAt_iff_isLittleOTVS]
  apply isLittleOTVS_insert
  simp only [sub_self, map_zero]

protected alias ⟨_, HasFDerivWithinAt.insert⟩ := hasFDerivWithinAt_insert_self
/-
**HasFDerivWithinAt.of_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.of_insert {y : E} (h : HasFDerivWithinAt f f' (insert y 
s) x) : HasFDerivWithinAt f f' s x
参数：h : HasFDerivWithinAt f f' (insert y s) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.mono`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [ins
t_3 : Topolo…
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
-/
theorem HasFDerivWithinAt.of_insert {y : E} (h : HasFDerivWithinAt f f' (insert y s) x) :
    HasFDerivWithinAt f f' s x :=
  h.mono <| subset_insert y s

@[simp]
/-
**hasFDerivWithinAt_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_insert [T1Space E] {y : E} : HasFDerivWithinAt f f' (ins
ert y s) x ↔ HasFDerivWithinAt f f' s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `hasFDerivWithinAt_insert_self`：hasFDerivWithinAt_insert_self : HasFDeriv
WithinAt f f' (insert x s) x ↔ HasFDerivWithinAt f f' s x
· 使用定理 `HasFDerivWithinAt.of_insert`：HasFDerivWithinAt.of_insert {y : E} (h : Ha
sFDerivWithinAt f f' (insert y s) x) : HasFDerivWithinAt f f' s x
· 使用定理 `HasFDerivWithinAt.mono_of_mem_nhdsWithin`：HasFDerivWithinAt.mono_of_mem_
nhdsWithin (h : HasFDerivWithinAt f f' t x) (hst : t in 𝓝[s] x) : HasFDerivWithi
nAt f f' s x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_insert_of_ne`：nhdsWithin_insert_of_ne [T1Space X] {x y : X} {
s : Set X} (hxy : x != y) : 𝓝[insert y s] x = 𝓝[s] x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem hasFDerivWithinAt_insert [T1Space E] {y : E} :
    HasFDerivWithinAt f f' (insert y s) x ↔ HasFDerivWithinAt f f' s x := by
  rcases eq_or_ne x y with (rfl | h)
  · apply hasFDerivWithinAt_insert_self
  · refine ⟨.of_insert, fun hf => hf.mono_of_mem_nhdsWithin ?_⟩
    simp_rw [nhdsWithin_insert_of_ne h, self_mem_nhdsWithin]

alias ⟨_, HasFDerivWithinAt.insert'⟩ := hasFDerivWithinAt_insert

@[simp]
/-
**hasFDerivWithinAt_sdiff_singleton_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_sdiff_singleton_self : HasFDerivWithinAt f f' (s \ {x}) 
x ↔ HasFDerivWithinAt f f' s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasFDerivWithinAt_insert_self`：hasFDerivWithinAt_insert_self : HasFDeriv
WithinAt f f' (insert x s) x ↔ HasFDerivWithinAt f f' s x
· 使用引理 `Set.insert_sdiff_singleton`：insert_sdiff_singleton : insert a (s \ {a}) 
= insert a s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem hasFDerivWithinAt_sdiff_singleton_self :
    HasFDerivWithinAt f f' (s \ {x}) x ↔ HasFDerivWithinAt f f' s x := by
  rw [← hasFDerivWithinAt_insert_self, insert_sdiff_singleton, hasFDerivWithinAt_insert_self]

@[deprecated (since := "2026-06-03")]
alias hasFDerivWithinAt_diff_singleton_self := hasFDerivWithinAt_sdiff_singleton_self

@[simp]
/-
**hasFDerivWithinAt_sdiff_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_sdiff_singleton [T1Space E] (y : E) : HasFDerivWithinAt 
f f' (s \ {y}) x ↔ HasFDerivWithinAt f f' s x
参数：y : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasFDerivWithinAt_insert`：hasFDerivWithinAt_insert [T1Space E] {y : E} :
 HasFDerivWithinAt f f' (insert y s) x ↔ HasFDerivWithinAt f f' s x
· 使用引理 `Set.insert_sdiff_singleton`：insert_sdiff_singleton : insert a (s \ {a}) 
= insert a s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem hasFDerivWithinAt_sdiff_singleton [T1Space E] (y : E) :
    HasFDerivWithinAt f f' (s \ {y}) x ↔ HasFDerivWithinAt f f' s x := by
  rw [← hasFDerivWithinAt_insert, insert_sdiff_singleton, hasFDerivWithinAt_insert]

@[deprecated (since := "2026-06-03")]
alias hasFDerivWithinAt_diff_singleton := hasFDerivWithinAt_sdiff_singleton

@[simp]
/-
**HasFDerivWithinAt.empty** 是 Mathlib 中的一个定理，位于命名空间 `HasFDerivWithinAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : TopologicalSpace E] 
{F : Type u_3} [inst_4 : AddCommGroup F]   [inst_5 : _root_.Module 𝕜 F] [inst_6 
: TopologicalSpace F] {f : E → F} {f' : E →L[𝕜] F} {x : E},   HasFDerivWithinAt 
f f' ∅ x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhdsWithin_empty`：nhdsWithin_empty (a : α) : 𝓝[∅] a = ⊥
· 使用定理 `Filter.prod_pure`：prod_pure {b : β} : f ×ˢ pure b = map (fun a => (a, b)
) f
· 使用定理 `Filter.map_bot`：∀ {α : Type u_1} {β : Type u_2} {m : α → β}, Filter.map 
m ⊥ = ⊥
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
-/
protected theorem HasFDerivWithinAt.empty : HasFDerivWithinAt f f' ∅ x := by
  simp [HasFDerivWithinAt, hasFDerivAtFilter_iff_isLittleOTVS]

@[simp]
/-
**DifferentiableWithinAt.empty** 是 Mathlib 中的一个定理，位于命名空间 `DifferentiableWithinAt
`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : TopologicalSpace E] 
{F : Type u_3} [inst_4 : AddCommGroup F]   [inst_5 : _root_.Module 𝕜 F] [inst_6 
: TopologicalSpace F] {f : E → F} {x : E}, DifferentiableWithinAt 𝕜 f ∅ x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.empty`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [in
st_3 : Topolo…
-/
protected theorem DifferentiableWithinAt.empty : DifferentiableWithinAt 𝕜 f ∅ x :=
  ⟨0, .empty⟩

@[fun_prop]
/-
**differentiableOn_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_empty : DifferentiableOn 𝕜 f ∅
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem differentiableOn_empty : DifferentiableOn 𝕜 f ∅ := fun _ => False.elim
/-
**HasFDerivWithinAt.of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.of_finite [T1Space E] (h : s.Finite) : HasFDerivWithinAt
 f f' s x
参数：h : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.induction_on`：∀ {α : Type u} {motive : (s : Set α) → s.Finite
 → Prop} (s : Set α) (hs : s.Finite),   motive ∅ ⋯ → (∀ {a : α} {s : Set α}, a ∉
 s → ∀ (hs : …
· 使用定理 `HasFDerivWithinAt.empty`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [in
st_3 : Topolo…
· 使用定理 `HasFDerivWithinAt.insert'`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [
inst_3 : Topolo…
-/
theorem HasFDerivWithinAt.of_finite [T1Space E] (h : s.Finite) : HasFDerivWithinAt f f' s x := by
  induction s, h using Set.Finite.induction_on with
  | empty => exact .empty
  | insert _ _ ih => exact ih.insert'
/-
**DifferentiableWithinAt.of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.of_finite [T1Space E] (h : s.Finite) : Differentiab
leWithinAt 𝕜 f s x
参数：h : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.of_finite`：HasFDerivWithinAt.of_finite [T1Space E] (h 
: s.Finite) : HasFDerivWithinAt f f' s x
-/
theorem DifferentiableWithinAt.of_finite [T1Space E] (h : s.Finite) :
    DifferentiableWithinAt 𝕜 f s x :=
  ⟨0, .of_finite h⟩

@[simp]
/-
**HasFDerivWithinAt.singleton** 是 Mathlib 中的一个定理，位于命名空间 `HasFDerivWithinAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : TopologicalSpace E] 
{F : Type u_3} [inst_4 : AddCommGroup F]   [inst_5 : _root_.Module 𝕜 F] [inst_6 
: TopologicalSpace F] {f : E → F} {f' : E →L[𝕜] F} {x : E} [T1Space E] {y : E}, 
  HasFDerivWithinAt f f' {x} y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.of_finite`：HasFDerivWithinAt.of_finite [T1Space E] (h 
: s.Finite) : HasFDerivWithinAt f f' s x
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
-/
protected theorem HasFDerivWithinAt.singleton [T1Space E] {y} : HasFDerivWithinAt f f' {x} y :=
  .of_finite <| finite_singleton _

@[simp]
/-
**DifferentiableWithinAt.singleton** 是 Mathlib 中的一个定理，位于命名空间 `DifferentiableWith
inAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : TopologicalSpace E] 
{F : Type u_3} [inst_4 : AddCommGroup F]   [inst_5 : _root_.Module 𝕜 F] [inst_6 
: TopologicalSpace F] {f : E → F} {x : E} [T1Space E] {y : E},   DifferentiableW
ithinAt 𝕜 f {x} y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.singleton`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E]
 [inst_3 : Topolo…
-/
protected theorem DifferentiableWithinAt.singleton [T1Space E] {y} :
    DifferentiableWithinAt 𝕜 f {x} y :=
  ⟨0, .singleton⟩
/-
**HasFDerivWithinAt.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.of_subsingleton [T1Space E] (h : s.Subsingleton) : HasFD
erivWithinAt f f' s x
参数：h : s.Subsingleton。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.of_finite`：HasFDerivWithinAt.of_finite [T1Space E] (h 
: s.Finite) : HasFDerivWithinAt f f' s x
· 使用定理 `Set.Subsingleton.finite`：∀ {α : Type u} {s : Set α}, s.Subsingleton → s.
Finite
-/
theorem HasFDerivWithinAt.of_subsingleton [T1Space E] (h : s.Subsingleton) :
    HasFDerivWithinAt f f' s x :=
  .of_finite h.finite
/-
**DifferentiableWithinAt.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.of_subsingleton [T1Space E] (h : s.Subsingleton) : 
DifferentiableWithinAt 𝕜 f s x
参数：h : s.Subsingleton。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.of_finite`：DifferentiableWithinAt.of_finite [T1Sp
ace E] (h : s.Finite) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `Set.Subsingleton.finite`：∀ {α : Type u} {s : Set α}, s.Subsingleton → s.
Finite
-/
theorem DifferentiableWithinAt.of_subsingleton [T1Space E] (h : s.Subsingleton) :
    DifferentiableWithinAt 𝕜 f s x :=
  .of_finite h.finite

@[fun_prop]
/-
**HasStrictFDerivAt.hasFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `HasStrictFDerivAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : TopologicalSpace E] 
{F : Type u_3} [inst_4 : AddCommGroup F]   [inst_5 : _root_.Module 𝕜 F] [inst_6 
: TopologicalSpace F] {f : E → F} {f' : E →L[𝕜] F} {x : E},   HasStrictFDerivAt 
f f' x → HasFDerivAt f f' x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.of_isLittleOTVS`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E]
 [inst_3 : Topolo…
· 使用定理 `Asymptotics.IsLittleOTVS.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {
𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]  
 [inst_1 : AddCommGroup E] …
· 使用定理 `HasFDerivAtFilter.isLittleOTVS`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
protected theorem HasStrictFDerivAt.hasFDerivAt (hf : HasStrictFDerivAt f f' x) :
    HasFDerivAt f f' x :=
  .of_isLittleOTVS <| by
    simpa only using! hf.isLittleOTVS.comp_tendsto (tendsto_id.prodMk_nhds tendsto_const_nhds)
/-
**HasStrictFDerivAt.differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 `HasStrictFDerivA
t`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : TopologicalSpace E] 
{F : Type u_3} [inst_4 : AddCommGroup F]   [inst_5 : _root_.Module 𝕜 F] [inst_6 
: TopologicalSpace F] {f : E → F} {f' : E →L[𝕜] F} {x : E},   HasStrictFDerivAt 
f f' x → DifferentiableAt 𝕜 f x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
-/
protected theorem HasStrictFDerivAt.differentiableAt (hf : HasStrictFDerivAt f f' x) :
    DifferentiableAt 𝕜 f x :=
  hf.hasFDerivAt.differentiableAt

/-- Directional derivative agrees with `HasFDeriv`. -/
/-
**HasFDerivAt.lim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.lim [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [
ContinuousSMul 𝕜 F] (hf : HasFDerivAt f f' x) (v : E) {α : Type*} {c : α -> 𝕜} {
l : Filter α} (hc : Tendsto (fun n => ‖c n‖) l atTop) : Tendsto (fun n => c n • 
(f (x + (c n)⁻¹ • v) - f x)) l (𝓝 (f' v))
参数：hf : HasFDerivAt f f' x；v : E；hc : Tendsto (fun n => ‖c n‖) l atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.lim`：HasFDerivWithinAt.lim (h : HasFDerivWithinAt f f'
 s x) {α : Type*} {l : Filter α} {c : α -> 𝕜} {d : α -> E} {v : E} (dlim : Tends
to d l (𝓝 0…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasFDerivWithinAt_univ`：hasFDerivWithinAt_univ : HasFDerivWithinAt f f' 
univ x ↔ HasFDerivAt f f' x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Filter.Tendsto.smul`：Filter.Tendsto.smul {f : α -> M} {g : α -> X} {l : 
Filter α} {c : M} {a : X} (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l (𝓝 a)) : Te
ndsto (fu…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_inv₀_cobounded`：tendsto_inv₀_cobounded : Tendsto Inv.inv 
(cobounded α) (𝓝 0)
· 使用定理 `tendsto_norm_atTop_iff_cobounded`：∀ {α : Type u_1} {E : Type u_2} [inst 
: SeminormedAddGroup E] {f : α → E} {l : Filter α},   Filter.Tendsto (fun x => ‖
f x‖) l Filter.atTop ↔…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `tendsto_nhds_of_eventually_eq`：tendsto_nhds_of_eventually_eq {l : Filter
 α} {f : α -> X} (h : forallᶠ x' in l, f x' = x) : Tendsto f l (𝓝 x)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `eventually_ne_of_tendsto_norm_atTop`：∀ {α : Type u_1} {E : Type u_4} [in
st : SeminormedAddGroup E] {l : Filter α} {f : α → E},   Filter.Tendsto (fun y =
> ‖f y‖) l Filter.atTop →…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Directional derivative agrees with `HasFDeriv`.
-/
theorem HasFDerivAt.lim
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F]
    (hf : HasFDerivAt f f' x) (v : E) {α : Type*} {c : α → 𝕜} {l : Filter α}
    (hc : Tendsto (fun n => ‖c n‖) l atTop) :
    Tendsto (fun n => c n • (f (x + (c n)⁻¹ • v) - f x)) l (𝓝 (f' v)) := by
  refine (hasFDerivWithinAt_univ.2 hf).lim ?_ (.of_forall fun _ ↦ mem_univ _) ?_
  · rw [tendsto_norm_atTop_iff_cobounded] at hc
    simpa using (tendsto_inv₀_cobounded.comp hc).smul (tendsto_const_nhds (x := v))
  · refine tendsto_nhds_of_eventually_eq ?_
    refine (eventually_ne_of_tendsto_norm_atTop hc (0 : 𝕜)).mono fun y hy => ?_
    simp [hy]
/-
**hasFDerivWithinAt_inter'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_inter' (h : t in 𝓝[s] x) : HasFDerivWithinAt f f' (s int
er t) x ↔ HasFDerivWithinAt f f' s x
参数：h : t in 𝓝[s] x。
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
· 使用定理 `nhdsWithin_restrict''`：nhdsWithin_restrict'' {a : α} (s : Set α) {t : Se
t α} (h : t in 𝓝[s] a) : 𝓝[s] a = 𝓝[s inter t] a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasFDerivWithinAt_inter' (h : t ∈ 𝓝[s] x) :
    HasFDerivWithinAt f f' (s ∩ t) x ↔ HasFDerivWithinAt f f' s x := by
  simp [HasFDerivWithinAt, nhdsWithin_restrict'' s h]
/-
**hasFDerivWithinAt_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_inter (h : t in 𝓝 x) : HasFDerivWithinAt f f' (s inter t
) x ↔ HasFDerivWithinAt f f' s x
参数：h : t in 𝓝 x。
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
· 使用定理 `nhdsWithin_restrict'`：nhdsWithin_restrict' {a : α} (s : Set α) {t : Set 
α} (h : t in 𝓝 a) : 𝓝[s] a = 𝓝[s inter t] a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasFDerivWithinAt_inter (h : t ∈ 𝓝 x) :
    HasFDerivWithinAt f f' (s ∩ t) x ↔ HasFDerivWithinAt f f' s x := by
  simp [HasFDerivWithinAt, nhdsWithin_restrict' s h]
/-
**HasFDerivWithinAt.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.union (hs : HasFDerivWithinAt f f' s x) (ht : HasFDerivW
ithinAt f f' t x) : HasFDerivWithinAt f f' (s union t) x
参数：hs : HasFDerivWithinAt f f' s x；ht : HasFDerivWithinAt f f' t x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_union`：nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s union t] 
a = 𝓝[s] a ⊔ 𝓝[t] a
· 使用定理 `Asymptotics.IsLittleOTVS.sup`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type 
u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup 
E] [inst_2 : Topol…
-/
theorem HasFDerivWithinAt.union (hs : HasFDerivWithinAt f f' s x)
    (ht : HasFDerivWithinAt f f' t x) : HasFDerivWithinAt f f' (s ∪ t) x := by
  simp only [hasFDerivWithinAt_iff_isLittleOTVS, nhdsWithin_union] at *
  exact hs.sup ht
/-
**HasFDerivWithinAt.hasFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.hasFDerivAt (h : HasFDerivWithinAt f f' s x) (hs : s in 
𝓝 x) : HasFDerivAt f f' x
参数：h : HasFDerivWithinAt f f' s x；hs : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasFDerivWithinAt_univ`：hasFDerivWithinAt_univ : HasFDerivWithinAt f f' 
univ x ↔ HasFDerivAt f f' x
· 使用定理 `hasFDerivWithinAt_inter`：hasFDerivWithinAt_inter (h : t in 𝓝 x) : HasFDe
rivWithinAt f f' (s inter t) x ↔ HasFDerivWithinAt f f' s x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
-/
theorem HasFDerivWithinAt.hasFDerivAt (h : HasFDerivWithinAt f f' s x) (hs : s ∈ 𝓝 x) :
    HasFDerivAt f f' x := by
  rwa [← univ_inter s, hasFDerivWithinAt_inter hs, hasFDerivWithinAt_univ] at h
/-
**DifferentiableWithinAt.differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.differentiableAt (h : DifferentiableWithinAt 𝕜 f s 
x) (hs : s in 𝓝 x) : DifferentiableAt 𝕜 f x
参数：h : DifferentiableWithinAt 𝕜 f s x；hs : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `HasFDerivWithinAt.hasFDerivAt`：HasFDerivWithinAt.hasFDerivAt (h : HasFDe
rivWithinAt f f' s x) (hs : s in 𝓝 x) : HasFDerivAt f f' x
-/
theorem DifferentiableWithinAt.differentiableAt (h : DifferentiableWithinAt 𝕜 f s x)
    (hs : s ∈ 𝓝 x) : DifferentiableAt 𝕜 f x :=
  h.imp fun _ hf' => hf'.hasFDerivAt hs

/-- If `x` is isolated in `s`, then `f` has any derivative at `x` within `s`,
as this statement is empty. -/
/-
**HasFDerivWithinAt.of_not_accPt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.of_not_accPt (h : ¬AccPt x (𝓟 s)) : HasFDerivWithinAt f 
f' s x
参数：h : ¬AccPt x (𝓟 s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasFDerivWithinAt_sdiff_singleton_self`：hasFDerivWithinAt_sdiff_singleto
n_self : HasFDerivWithinAt f f' (s \ {x}) x ↔ HasFDerivWithinAt f f' s x
· 使用定理 `hasFDerivWithinAt_iff_isLittleOTVS`：hasFDerivWithinAt_iff_isLittleOTVS :
 HasFDerivWithinAt f f' s x ↔ (fun x' => f x' - f x - f' (x' - x)) =o[𝕜; 𝓝[s] x]
 (fun x' => x' - x)
· 使用定理 `Filter.not_neBot`：not_neBot {f : Filter α} : ¬f.NeBot ↔ f = ⊥
· 使用定理 `accPt_principal_iff_nhdsWithin`：accPt_principal_iff_nhdsWithin : AccPt x
 (𝓟 s) ↔ (𝓝[s \ {x}] x).NeBot
· 使用定理 `Asymptotics.IsLittleOTVS.bot`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type 
u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup 
E] [inst_2 : Topol…

--- 原说明 ---
If `x` is isolated in `s`, then `f` has any derivative at `x` within `s`,
as this statement is empty.
-/
theorem HasFDerivWithinAt.of_not_accPt (h : ¬AccPt x (𝓟 s)) :
    HasFDerivWithinAt f f' s x := by
  rw [accPt_principal_iff_nhdsWithin, not_neBot] at h
  rw [← hasFDerivWithinAt_sdiff_singleton_self, hasFDerivWithinAt_iff_isLittleOTVS, h]
  exact .bot

/-- If `x` is not in the closure of `s`, then `f` has any derivative at `x` within `s`,
as this statement is empty. -/
/-
**HasFDerivWithinAt.of_notMem_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.of_notMem_closure (h : x ∉ closure s) : HasFDerivWithinA
t f f' s x
参数：h : x ∉ closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.of_not_accPt`：HasFDerivWithinAt.of_not_accPt (h : ¬Acc
Pt x (𝓟 s)) : HasFDerivWithinAt f f' s x
· 使用定理 `ClusterPt.mem_closure`：∀ {X : Type u} [inst : TopologicalSpace X] {x : X
} {s : Set X}, ClusterPt x (Filter.principal s) → x ∈ closure s
· 使用定理 `AccPt.clusterPt`：AccPt.clusterPt {x : X} {F : Filter X} (h : AccPt x F) 
: ClusterPt x F

--- 原说明 ---
If `x` is not in the closure of `s`, then `f` has any derivative at `x` within `
s`,
as this statement is empty.
-/
theorem HasFDerivWithinAt.of_notMem_closure (h : x ∉ closure s) : HasFDerivWithinAt f f' s x :=
  .of_not_accPt (h ·.clusterPt.mem_closure)
/-
**fderivWithin_zero_of_not_accPt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_zero_of_not_accPt (h : ¬AccPt x (𝓟 s)) : fderivWithin 𝕜 f s x
 = 0
参数：h : ¬AccPt x (𝓟 s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_def`：∀ (𝕜 : Type u_4) [inst : NontriviallyNormedField 𝕜] {E
 : Type u_5} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : 
Topolo…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `HasFDerivWithinAt.of_not_accPt`：HasFDerivWithinAt.of_not_accPt (h : ¬Acc
Pt x (𝓟 s)) : HasFDerivWithinAt f f' s x
-/
theorem fderivWithin_zero_of_not_accPt (h : ¬AccPt x (𝓟 s)) :
    fderivWithin 𝕜 f s x = 0 := by
  rw [fderivWithin, if_pos (.of_not_accPt h)]
/-
**fderivWithin_zero_of_notMem_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_zero_of_notMem_closure (h : x ∉ closure s) : fderivWithin 𝕜 f
 s x = 0
参数：h : x ∉ closure s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fderivWithin_zero_of_not_accPt`：fderivWithin_zero_of_not_accPt (h : ¬Acc
Pt x (𝓟 s)) : fderivWithin 𝕜 f s x = 0
· 使用定理 `ClusterPt.mem_closure`：∀ {X : Type u} [inst : TopologicalSpace X] {x : X
} {s : Set X}, ClusterPt x (Filter.principal s) → x ∈ closure s
· 使用定理 `AccPt.clusterPt`：AccPt.clusterPt {x : X} {F : Filter X} (h : AccPt x F) 
: ClusterPt x F
-/
theorem fderivWithin_zero_of_notMem_closure (h : x ∉ closure s) :
    fderivWithin 𝕜 f s x = 0 :=
  fderivWithin_zero_of_not_accPt (h ·.clusterPt.mem_closure)
/-
**fderivWithin_zero_of_not_uniqueDiffWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_zero_of_not_uniqueDiffWithinAt {f : 𝕜 -> F} {x : 𝕜} {s : Set 
𝕜} (h : ¬UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 f s x = 0
参数：h : ¬UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fderivWithin_zero_of_not_accPt`：fderivWithin_zero_of_not_accPt (h : ¬Acc
Pt x (𝓟 s)) : fderivWithin 𝕜 f s x = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `AccPt.uniqueDiffWithinAt`：∀ {𝕜 : Type u_1} [inst : NormedDivisionRing 𝕜]
 {s : Set 𝕜} {x : 𝕜},   AccPt x (Filter.principal s) → UniqueDiffWithinAt 𝕜 s x
-/
theorem fderivWithin_zero_of_not_uniqueDiffWithinAt {f : 𝕜 → F} {x : 𝕜} {s : Set 𝕜}
    (h : ¬UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 f s x = 0 :=
  fderivWithin_zero_of_not_accPt <| mt AccPt.uniqueDiffWithinAt h
/-
**DifferentiableWithinAt.hasFDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.hasFDerivWithinAt (h : DifferentiableWithinAt 𝕜 f s
 x) : HasFDerivWithinAt f (fderivWithin 𝕜 f s x) s x
参数：h : DifferentiableWithinAt 𝕜 f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `fderivWithin_def`：∀ (𝕜 : Type u_4) [inst : NontriviallyNormedField 𝕜] {E
 : Type u_5} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : 
Topolo…
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem DifferentiableWithinAt.hasFDerivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) :
    HasFDerivWithinAt f (fderivWithin 𝕜 f s x) s x := by
  simp only [fderivWithin, dif_pos h]
  split_ifs with h₀
  exacts [h₀, Classical.choose_spec h]
/-
**DifferentiableAt.hasFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.hasFDerivAt (h : DifferentiableAt 𝕜 f x) : HasFDerivAt f 
(fderiv 𝕜 f x) x
参数：h : DifferentiableAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderiv_def`：∀ (𝕜 : Type u_4) [inst : NontriviallyNormedField 𝕜] {E : Typ
e u_5} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : Topolo
…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasFDerivWithinAt_univ`：hasFDerivWithinAt_univ : HasFDerivWithinAt f f' 
univ x ↔ HasFDerivAt f f' x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
· 使用定理 `differentiableWithinAt_univ`：differentiableWithinAt_univ : Differentiabl
eWithinAt 𝕜 f univ x ↔ DifferentiableAt 𝕜 f x
-/
theorem DifferentiableAt.hasFDerivAt (h : DifferentiableAt 𝕜 f x) :
    HasFDerivAt f (fderiv 𝕜 f x) x := by
  rw [fderiv, ← hasFDerivWithinAt_univ]
  rw [← differentiableWithinAt_univ] at h
  exact h.hasFDerivWithinAt
/-
**DifferentiableOn.hasFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.hasFDerivAt (h : DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x) 
: HasFDerivAt f (fderiv 𝕜 f x) x
参数：h : DifferentiableOn 𝕜 f s；hs : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
· 使用定理 `DifferentiableWithinAt.differentiableAt`：DifferentiableWithinAt.differen
tiableAt (h : DifferentiableWithinAt 𝕜 f s x) (hs : s in 𝓝 x) : DifferentiableAt
 𝕜 f x
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
-/
theorem DifferentiableOn.hasFDerivAt (h : DifferentiableOn 𝕜 f s) (hs : s ∈ 𝓝 x) :
    HasFDerivAt f (fderiv 𝕜 f x) x :=
  ((h x (mem_of_mem_nhds hs)).differentiableAt hs).hasFDerivAt
/-
**DifferentiableOn.differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.differentiableAt (h : DifferentiableOn 𝕜 f s) (hs : s in 
𝓝 x) : DifferentiableAt 𝕜 f x
参数：h : DifferentiableOn 𝕜 f s；hs : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `DifferentiableOn.hasFDerivAt`：DifferentiableOn.hasFDerivAt (h : Differen
tiableOn 𝕜 f s) (hs : s in 𝓝 x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableOn.differentiableAt (h : DifferentiableOn 𝕜 f s) (hs : s ∈ 𝓝 x) :
    DifferentiableAt 𝕜 f x :=
  (h.hasFDerivAt hs).differentiableAt
/-
**DifferentiableOn.eventually_differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.eventually_differentiableAt (h : DifferentiableOn 𝕜 f s) 
(hs : s in 𝓝 x) : forallᶠ y in 𝓝 x, DifferentiableAt 𝕜 f y
参数：h : DifferentiableOn 𝕜 f s；hs : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_eventually_nhds`：eventually_eventually_nhds {p : X -> Prop} :
 (forallᶠ y in 𝓝 x, forallᶠ x in 𝓝 y, p x) ↔ forallᶠ x in 𝓝 x, p x
· 使用定理 `DifferentiableOn.differentiableAt`：DifferentiableOn.differentiableAt (h 
: DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x) : DifferentiableAt 𝕜 f x
-/
theorem DifferentiableOn.eventually_differentiableAt (h : DifferentiableOn 𝕜 f s) (hs : s ∈ 𝓝 x) :
    ∀ᶠ y in 𝓝 x, DifferentiableAt 𝕜 f y :=
  (eventually_eventually_nhds.2 hs).mono fun _ => h.differentiableAt
/-
**HasFDerivAt.fderiv** 是 Mathlib 中的一个定理，位于命名空间 `HasFDerivAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : TopologicalSpace E] 
{F : Type u_3} [inst_4 : AddCommGroup F]   [inst_5 : _root_.Module 𝕜 F] [inst_6 
: TopologicalSpace F] {f : E → F} {f' : E →L[𝕜] F} {x : E} [ContinuousAdd E]   [
ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F], HasFDeri
vAt f f' x → fderiv 𝕜 f x = f'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasFDerivAt.unique`：HasFDerivAt.unique (h₀ : HasFDerivAt f f' x) (h₁ : H
asFDerivAt f f₁' x) : f' = f₁'
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
-/
protected theorem HasFDerivAt.fderiv
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
    (h : HasFDerivAt f f' x) :
    fderiv 𝕜 f x = f' := by
  rw [h.unique h.differentiableAt.hasFDerivAt]
/-
**fderiv_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_eq [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [Contin
uousSMul 𝕜 F] [T2Space F] {f' : E -> E ->L[𝕜] F} (h : forall x, HasFDerivAt f (f
' x) x) : fderiv 𝕜 f = f'
参数：h : forall x, HasFDerivAt f (f' x) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
-/
theorem fderiv_eq
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
    {f' : E → E →L[𝕜] F} (h : ∀ x, HasFDerivAt f (f' x) x) : fderiv 𝕜 f = f' :=
  funext fun x => (h x).fderiv
/-
**HasFDerivWithinAt.fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 `HasFDerivWithinAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : TopologicalSpace E] 
{F : Type u_3} [inst_4 : AddCommGroup F]   [inst_5 : _root_.Module 𝕜 F] [inst_6 
: TopologicalSpace F] {f : E → F} {f' : E →L[𝕜] F} {x : E} {s : Set E}   [Contin
uousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space 
F],   HasFDerivWithinAt f f' s x → UniqueDiffWithinAt 𝕜 s x → fderivWithin 𝕜 f s
 x = f'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UniqueDiffWithinAt.eq`：UniqueDiffWithinAt.eq (H : UniqueDiffWithinAt 𝕜 s
 x) (hf : HasFDerivWithinAt f f' s x) (hg : HasFDerivWithinAt f f₁' s x) : f' = 
f₁'
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
-/
protected theorem HasFDerivWithinAt.fderivWithin
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
    (h : HasFDerivWithinAt f f' s x)
    (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 f s x = f' :=
  (hxs.eq h h.differentiableWithinAt.hasFDerivWithinAt).symm
/-
**DifferentiableWithinAt.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.mono (h : DifferentiableWithinAt 𝕜 f t x) (st : s s
ubseteq t) : DifferentiableWithinAt 𝕜 f s x
参数：h : DifferentiableWithinAt 𝕜 f t x；st : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.mono`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [ins
t_3 : Topolo…
-/
theorem DifferentiableWithinAt.mono (h : DifferentiableWithinAt 𝕜 f t x) (st : s ⊆ t) :
    DifferentiableWithinAt 𝕜 f s x := by
  rcases h with ⟨f', hf'⟩
  exact ⟨f', hf'.mono st⟩
/-
**DifferentiableWithinAt.mono_of_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.mono_of_mem_nhdsWithin (h : DifferentiableWithinAt 
𝕜 f s x) {t : Set E} (hst : s in 𝓝[t] x) : DifferentiableWithinAt 𝕜 f t x
参数：h : DifferentiableWithinAt 𝕜 f s x；hst : s in 𝓝[t] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasFDerivWithinAt.mono_of_mem_nhdsWithin`：HasFDerivWithinAt.mono_of_mem_
nhdsWithin (h : HasFDerivWithinAt f f' t x) (hst : t in 𝓝[s] x) : HasFDerivWithi
nAt f f' s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.mono_of_mem_nhdsWithin
    (h : DifferentiableWithinAt 𝕜 f s x) {t : Set E} (hst : s ∈ 𝓝[t] x) :
    DifferentiableWithinAt 𝕜 f t x :=
  (h.hasFDerivWithinAt.mono_of_mem_nhdsWithin hst).differentiableWithinAt
/-
**DifferentiableWithinAt.congr_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.congr_nhds (h : DifferentiableWithinAt 𝕜 f s x) {t 
: Set E} (hst : 𝓝[s] x = 𝓝[t] x) : DifferentiableWithinAt 𝕜 f t x
参数：h : DifferentiableWithinAt 𝕜 f s x；hst : 𝓝[s] x = 𝓝[t] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.mono_of_mem_nhdsWithin`：DifferentiableWithinAt.mo
no_of_mem_nhdsWithin (h : DifferentiableWithinAt 𝕜 f s x) {t : Set E} (hst : s i
n 𝓝[t] x) : DifferentiableWithinAt …
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
-/
theorem DifferentiableWithinAt.congr_nhds (h : DifferentiableWithinAt 𝕜 f s x) {t : Set E}
    (hst : 𝓝[s] x = 𝓝[t] x) : DifferentiableWithinAt 𝕜 f t x :=
  h.mono_of_mem_nhdsWithin <| hst ▸ self_mem_nhdsWithin
/-
**differentiableWithinAt_congr_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_congr_nhds {t : Set E} (hst : 𝓝[s] x = 𝓝[t] x) : Di
fferentiableWithinAt 𝕜 f s x ↔ DifferentiableWithinAt 𝕜 f t x
参数：hst : 𝓝[s] x = 𝓝[t] x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.congr_nhds`：DifferentiableWithinAt.congr_nhds (h 
: DifferentiableWithinAt 𝕜 f s x) {t : Set E} (hst : 𝓝[s] x = 𝓝[t] x) : Differen
tiableWithinAt 𝕜 f t x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem differentiableWithinAt_congr_nhds {t : Set E} (hst : 𝓝[s] x = 𝓝[t] x) :
    DifferentiableWithinAt 𝕜 f s x ↔ DifferentiableWithinAt 𝕜 f t x :=
  ⟨fun h => h.congr_nhds hst, fun h => h.congr_nhds hst.symm⟩
/-
**differentiableWithinAt_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_inter (ht : t in 𝓝 x) : DifferentiableWithinAt 𝕜 f 
(s inter t) x ↔ DifferentiableWithinAt 𝕜 f s x
参数：ht : t in 𝓝 x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `hasFDerivWithinAt_inter`：hasFDerivWithinAt_inter (h : t in 𝓝 x) : HasFDe
rivWithinAt f f' (s inter t) x ↔ HasFDerivWithinAt f f' s x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem differentiableWithinAt_inter (ht : t ∈ 𝓝 x) :
    DifferentiableWithinAt 𝕜 f (s ∩ t) x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp only [DifferentiableWithinAt, hasFDerivWithinAt_inter ht]
/-
**differentiableWithinAt_inter'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_inter' (ht : t in 𝓝[s] x) : DifferentiableWithinAt 
𝕜 f (s inter t) x ↔ DifferentiableWithinAt 𝕜 f s x
参数：ht : t in 𝓝[s] x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `hasFDerivWithinAt_inter'`：hasFDerivWithinAt_inter' (h : t in 𝓝[s] x) : H
asFDerivWithinAt f f' (s inter t) x ↔ HasFDerivWithinAt f f' s x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem differentiableWithinAt_inter' (ht : t ∈ 𝓝[s] x) :
    DifferentiableWithinAt 𝕜 f (s ∩ t) x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp only [DifferentiableWithinAt, hasFDerivWithinAt_inter' ht]
/-
**differentiableWithinAt_insert_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_insert_self : DifferentiableWithinAt 𝕜 f (insert x 
s) x ↔ DifferentiableWithinAt 𝕜 f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.mono`：DifferentiableWithinAt.mono (h : Differenti
ableWithinAt 𝕜 f t x) (st : s subseteq t) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasFDerivWithinAt.insert`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [i
nst_3 : Topolo…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem differentiableWithinAt_insert_self :
    DifferentiableWithinAt 𝕜 f (insert x s) x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h ↦ h.mono (subset_insert x s), fun h ↦ h.hasFDerivWithinAt.insert.differentiableWithinAt⟩

protected alias ⟨_, DifferentiableWithinAt.insert⟩ := differentiableWithinAt_insert_self
/-
**DifferentiableWithinAt.of_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.of_insert {y : E} (h : DifferentiableWithinAt 𝕜 f (
insert y s) x) : DifferentiableWithinAt 𝕜 f s x
参数：h : DifferentiableWithinAt 𝕜 f (insert y s) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.mono`：DifferentiableWithinAt.mono (h : Differenti
ableWithinAt 𝕜 f t x) (st : s subseteq t) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
-/
theorem DifferentiableWithinAt.of_insert {y : E} (h : DifferentiableWithinAt 𝕜 f (insert y s) x) :
    DifferentiableWithinAt 𝕜 f s x :=
  h.mono <| subset_insert _ _
/-
**differentiableWithinAt_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_insert [T1Space E] {y : E} : DifferentiableWithinAt
 𝕜 f (insert y s) x ↔ DifferentiableWithinAt 𝕜 f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem differentiableWithinAt_insert [T1Space E] {y : E} :
    DifferentiableWithinAt 𝕜 f (insert y s) x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp only [DifferentiableWithinAt, hasFDerivWithinAt_insert]

alias ⟨_, DifferentiableWithinAt.insert'⟩ := differentiableWithinAt_insert
/-
**DifferentiableAt.differentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.differentiableWithinAt (h : DifferentiableAt 𝕜 f x) : Dif
ferentiableWithinAt 𝕜 f s x
参数：h : DifferentiableAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.mono`：DifferentiableWithinAt.mono (h : Differenti
ableWithinAt 𝕜 f t x) (st : s subseteq t) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `differentiableWithinAt_univ`：differentiableWithinAt_univ : Differentiabl
eWithinAt 𝕜 f univ x ↔ DifferentiableAt 𝕜 f x
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem DifferentiableAt.differentiableWithinAt (h : DifferentiableAt 𝕜 f x) :
    DifferentiableWithinAt 𝕜 f s x :=
  (differentiableWithinAt_univ.2 h).mono (subset_univ _)

@[fun_prop]
/-
**Differentiable.differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.differentiableAt (h : Differentiable 𝕜 f) : DifferentiableA
t 𝕜 f x
参数：h : Differentiable 𝕜 f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Differentiable.differentiableAt (h : Differentiable 𝕜 f) : DifferentiableAt 𝕜 f x :=
  h x
/-
**DifferentiableAt.fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 `DifferentiableAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : TopologicalSpace E] 
{F : Type u_3} [inst_4 : AddCommGroup F]   [inst_5 : _root_.Module 𝕜 F] [inst_6 
: TopologicalSpace F] {f : E → F} {x : E} {s : Set E} [ContinuousAdd E]   [Conti
nuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F],   Differentia
bleAt 𝕜 f x → UniqueDiffWithinAt 𝕜 s x → fderivWithin 𝕜 f s x = fderiv 𝕜 f x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `HasFDerivAt.hasFDerivWithinAt`：HasFDerivAt.hasFDerivWithinAt (h : HasFDe
rivAt f f' x) : HasFDerivWithinAt f f' s x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
protected theorem DifferentiableAt.fderivWithin
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
    (h : DifferentiableAt 𝕜 f x)
    (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 f s x = fderiv 𝕜 f x :=
  h.hasFDerivAt.hasFDerivWithinAt.fderivWithin hxs
/-
**DifferentiableOn.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t) (st : s subseteq t) : D
ifferentiableOn 𝕜 f s
参数：h : DifferentiableOn 𝕜 f t；st : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.mono`：DifferentiableWithinAt.mono (h : Differenti
ableWithinAt 𝕜 f t x) (st : s subseteq t) : DifferentiableWithinAt 𝕜 f s x
-/
theorem DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t) (st : s ⊆ t) : DifferentiableOn 𝕜 f s :=
  fun x hx => (h x (st hx)).mono st
/-
**differentiableOn_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_univ : DifferentiableOn 𝕜 f univ ↔ Differentiable 𝕜 f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem differentiableOn_univ : DifferentiableOn 𝕜 f univ ↔ Differentiable 𝕜 f := by
  simp only [DifferentiableOn, Differentiable, differentiableWithinAt_univ, mem_univ,
    forall_true_left]

@[fun_prop]
/-
**Differentiable.differentiableOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.differentiableOn (h : Differentiable 𝕜 f) : DifferentiableO
n 𝕜 f s
参数：h : Differentiable 𝕜 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.mono`：DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t
) (st : s subseteq t) : DifferentiableOn 𝕜 f s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `differentiableOn_univ`：differentiableOn_univ : DifferentiableOn 𝕜 f univ
 ↔ Differentiable 𝕜 f
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem Differentiable.differentiableOn (h : Differentiable 𝕜 f) : DifferentiableOn 𝕜 f s :=
  (differentiableOn_univ.2 h).mono (subset_univ _)
/-
**differentiableOn_of_locally_differentiableOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_of_locally_differentiableOn (h : forall x in s, exists u,
 IsOpen u ∧ x in u ∧ DifferentiableOn 𝕜 f (s inter u)) : DifferentiableOn 𝕜 f s
参数：h : forall x in s, exists u, IsOpen u ∧ x in u ∧ DifferentiableOn 𝕜 f (s inte
r u)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `differentiableWithinAt_inter`：differentiableWithinAt_inter (ht : t in 𝓝 
x) : DifferentiableWithinAt 𝕜 f (s inter t) x ↔ DifferentiableWithinAt 𝕜 f s x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
theorem differentiableOn_of_locally_differentiableOn
    (h : ∀ x ∈ s, ∃ u, IsOpen u ∧ x ∈ u ∧ DifferentiableOn 𝕜 f (s ∩ u)) :
    DifferentiableOn 𝕜 f s := by
  intro x xs
  rcases h x xs with ⟨t, t_open, xt, ht⟩
  exact (differentiableWithinAt_inter (IsOpen.mem_nhds t_open xt)).1 (ht x ⟨xs, xt⟩)
/-
**fderivWithin_of_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_of_mem_nhdsWithin [ContinuousAdd E] [ContinuousSMul 𝕜 E] [Con
tinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F] (st : t in 𝓝[s] x) (ht : UniqueDi
ffWithinAt 𝕜 s x) (h : DifferentiableWithinAt 𝕜 f t x) : fderivWithin 𝕜 f s x = 
fderivWithin 𝕜 f t x
参数：st : t in 𝓝[s] x；ht : UniqueDiffWithinAt 𝕜 s x；h : DifferentiableWithinAt 𝕜 f
 t x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `HasFDerivWithinAt.mono_of_mem_nhdsWithin`：HasFDerivWithinAt.mono_of_mem_
nhdsWithin (h : HasFDerivWithinAt f f' t x) (hst : t in 𝓝[s] x) : HasFDerivWithi
nAt f f' s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_of_mem_nhdsWithin
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
    (st : t ∈ 𝓝[s] x) (ht : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f t x) : fderivWithin 𝕜 f s x = fderivWithin 𝕜 f t x :=
  ((DifferentiableWithinAt.hasFDerivWithinAt h).mono_of_mem_nhdsWithin st).fderivWithin ht
/-
**fderivWithin_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_subset (st : s subseteq t) (ht : UniqueDiffWithinAt 𝕜 s x) [C
ontinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2S
pace F] (h : DifferentiableWithinAt 𝕜 f t x) : fderivWithin 𝕜 f s x = fderivWith
in 𝕜 f t x
参数：st : s subseteq t；ht : UniqueDiffWithinAt 𝕜 s x；h : DifferentiableWithinAt 𝕜 
f t x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fderivWithin_of_mem_nhdsWithin`：fderivWithin_of_mem_nhdsWithin [Continuo
usAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
 (st : t in 𝓝[s] x) …
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
-/
theorem fderivWithin_subset (st : s ⊆ t) (ht : UniqueDiffWithinAt 𝕜 s x)
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
    (h : DifferentiableWithinAt 𝕜 f t x) : fderivWithin 𝕜 f s x = fderivWithin 𝕜 f t x :=
  fderivWithin_of_mem_nhdsWithin (nhdsWithin_mono _ st self_mem_nhdsWithin) ht h

set_option backward.isDefEq.respectTransparency false in
/-
**fderivWithin_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_inter (ht : t in 𝓝 x) : fderivWithin 𝕜 f (s inter t) x = fder
ivWithin 𝕜 f s x
参数：ht : t in 𝓝 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `hasFDerivWithinAt_inter`：hasFDerivWithinAt_inter (h : t in 𝓝 x) : HasFDe
rivWithinAt f f' (s inter t) x ↔ HasFDerivWithinAt f f' s x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `fderivWithin_def`：∀ (𝕜 : Type u_4) [inst : NontriviallyNormedField 𝕜] {E
 : Type u_5} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : 
Topolo…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Classical.choose.congr_simp`：∀ {α : Sort u} {p p_1 : α → Prop} (e_p : p 
= p_1) (h : ∃ x, p x), Classical.choose h = Classical.choose ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fderivWithin_inter (ht : t ∈ 𝓝 x) : fderivWithin 𝕜 f (s ∩ t) x = fderivWithin 𝕜 f s x := by
  classical
  simp [fderivWithin, hasFDerivWithinAt_inter ht, DifferentiableWithinAt]
/-
**fderivWithin_of_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_of_mem_nhds (h : s in 𝓝 x) : fderivWithin 𝕜 f s x = fderiv 𝕜 
f x
参数：h : s in 𝓝 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `fderivWithin_univ`：fderivWithin_univ : fderivWithin 𝕜 f univ = fderiv 𝕜 
f
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `fderivWithin_inter`：fderivWithin_inter (ht : t in 𝓝 x) : fderivWithin 𝕜 
f (s inter t) x = fderivWithin 𝕜 f s x
-/
theorem fderivWithin_of_mem_nhds (h : s ∈ 𝓝 x) : fderivWithin 𝕜 f s x = fderiv 𝕜 f x := by
  rw [← fderivWithin_univ, ← univ_inter s, fderivWithin_inter h]
/-
**fderivWithin_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_of_isOpen (hs : IsOpen s) (hx : x in s) : fderivWithin 𝕜 f s 
x = fderiv 𝕜 f x
参数：hs : IsOpen s；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fderivWithin_of_mem_nhds`：fderivWithin_of_mem_nhds (h : s in 𝓝 x) : fder
ivWithin 𝕜 f s x = fderiv 𝕜 f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
theorem fderivWithin_of_isOpen (hs : IsOpen s) (hx : x ∈ s) : fderivWithin 𝕜 f s x = fderiv 𝕜 f x :=
  fderivWithin_of_mem_nhds (hs.mem_nhds hx)
/-
**fderivWithin_eq_fderiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_eq_fderiv [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousA
dd F] [ContinuousSMul 𝕜 F] [T2Space F] (hs : UniqueDiffWithinAt 𝕜 s x) (h : Diff
erentiableAt 𝕜 f x) : fderivWithin 𝕜 f s x = fderiv 𝕜 f x
参数：hs : UniqueDiffWithinAt 𝕜 s x；h : DifferentiableAt 𝕜 f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `fderivWithin_univ`：fderivWithin_univ : fderivWithin 𝕜 f univ = fderiv 𝕜 
f
· 使用定理 `fderivWithin_subset`：fderivWithin_subset (st : s subseteq t) (ht : Uniqu
eDiffWithinAt 𝕜 s x) [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [C
ontinuous…
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
-/
theorem fderivWithin_eq_fderiv
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
    (hs : UniqueDiffWithinAt 𝕜 s x) (h : DifferentiableAt 𝕜 f x) :
    fderivWithin 𝕜 f s x = fderiv 𝕜 f x := by
  rw [← fderivWithin_univ]
  exact fderivWithin_subset (subset_univ _) hs h.differentiableWithinAt
/-
**fderiv_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_mem_iff {f : E -> F} {s : Set (E ->L[𝕜] F)} {x : E} : fderiv 𝕜 f x 
in s ↔ DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x in s ∨ ¬DifferentiableAt 𝕜 f x ∧ (0
 : E ->L[𝕜] F) in s
参数：E ->L[𝕜] F。
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
· 使用定理 `fderiv_zero_of_not_differentiableAt`：fderiv_zero_of_not_differentiableAt
 (h : ¬DifferentiableAt 𝕜 f x) : fderiv 𝕜 f x = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem fderiv_mem_iff {f : E → F} {s : Set (E →L[𝕜] F)} {x : E} : fderiv 𝕜 f x ∈ s ↔
    DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x ∈ s ∨ ¬DifferentiableAt 𝕜 f x ∧ (0 : E →L[𝕜] F) ∈ s := by
  by_cases hx : DifferentiableAt 𝕜 f x <;> simp [fderiv_zero_of_not_differentiableAt, *]
/-
**fderivWithin_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_mem_iff {f : E -> F} {t : Set E} {s : Set (E ->L[𝕜] F)} {x : 
E} : fderivWithin 𝕜 f t x in s ↔ DifferentiableWithinAt 𝕜 f t x ∧ fderivWithin 𝕜
 f t x in s ∨ ¬DifferentiableWithinAt 𝕜 f t x ∧ (0 : E ->L[𝕜] F) in s
参数：E ->L[𝕜] F。
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
· 使用定理 `fderivWithin_zero_of_not_differentiableWithinAt`：fderivWithin_zero_of_no
t_differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) : fderivWithin 𝕜 
f s x = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem fderivWithin_mem_iff {f : E → F} {t : Set E} {s : Set (E →L[𝕜] F)} {x : E} :
    fderivWithin 𝕜 f t x ∈ s ↔
      DifferentiableWithinAt 𝕜 f t x ∧ fderivWithin 𝕜 f t x ∈ s ∨
        ¬DifferentiableWithinAt 𝕜 f t x ∧ (0 : E →L[𝕜] F) ∈ s := by
  by_cases hx : DifferentiableWithinAt 𝕜 f t x <;>
    simp [fderivWithin_zero_of_not_differentiableWithinAt, *]

end FDerivProperties

/-! ### Being differentiable on a union of open sets can be tested on each set -/
section differentiableOn_union

/-- If a function is differentiable on two open sets, it is also differentiable on their union. -/
/-
**DifferentiableOn.union_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DifferentiableOn.union_of_isOpen (hf : DifferentiableOn 𝕜 f s) (hf' : Diff
erentiableOn 𝕜 f t) (hs : IsOpen s) (ht : IsOpen t) : DifferentiableOn 𝕜 f (s un
ion t)
参数：hf : DifferentiableOn 𝕜 f s；hf' : DifferentiableOn 𝕜 f t；hs : IsOpen s；ht : I
sOpen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `DifferentiableWithinAt.differentiableAt`：DifferentiableWithinAt.differen
tiableAt (h : DifferentiableWithinAt 𝕜 f s x) (hs : s in 𝓝 x) : DifferentiableAt
 𝕜 f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x

--- 原说明 ---
If a function is differentiable on two open sets, it is also differentiable on t
heir union.
-/
lemma DifferentiableOn.union_of_isOpen
    (hf : DifferentiableOn 𝕜 f s) (hf' : DifferentiableOn 𝕜 f t)
    (hs : IsOpen s) (ht : IsOpen t) :
    DifferentiableOn 𝕜 f (s ∪ t) := by
  intro x hx
  obtain (hx | hx) := hx
  · exact (hf x hx).differentiableAt (hs.mem_nhds hx) |>.differentiableWithinAt
  · exact (hf' x hx).differentiableAt (ht.mem_nhds hx) |>.differentiableWithinAt

/-- A function is differentiable on two open sets iff it is differentiable on their union. -/
/-
**differentiableOn_union_iff_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：differentiableOn_union_iff_of_isOpen (hs : IsOpen s) (ht : IsOpen t) : Dif
ferentiableOn 𝕜 f (s union t) ↔ DifferentiableOn 𝕜 f s ∧ DifferentiableOn 𝕜 f t
参数：hs : IsOpen s；ht : IsOpen t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.mono`：DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t
) (st : s subseteq t) : DifferentiableOn 𝕜 f s
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用引理 `DifferentiableOn.union_of_isOpen`：DifferentiableOn.union_of_isOpen (hf :
 DifferentiableOn 𝕜 f s) (hf' : DifferentiableOn 𝕜 f t) (hs : IsOpen s) (ht : Is
Open t) : Differentiab…

--- 原说明 ---
A function is differentiable on two open sets iff it is differentiable on their 
union.
-/
lemma differentiableOn_union_iff_of_isOpen (hs : IsOpen s) (ht : IsOpen t) :
    DifferentiableOn 𝕜 f (s ∪ t) ↔ DifferentiableOn 𝕜 f s ∧ DifferentiableOn 𝕜 f t :=
  ⟨fun h ↦ ⟨h.mono subset_union_left, h.mono subset_union_right⟩,
    fun ⟨hfs, hft⟩ ↦ DifferentiableOn.union_of_isOpen hfs hft hs ht⟩
/-
**differentiable_of_differentiableOn_union_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：differentiable_of_differentiableOn_union_of_isOpen (hf : DifferentiableOn 
𝕜 f s) (hf' : DifferentiableOn 𝕜 f t) (hst : s union t = univ) (hs : IsOpen s) (
ht : IsOpen t) : Differentiable 𝕜 f
参数：hf : DifferentiableOn 𝕜 f s；hf' : DifferentiableOn 𝕜 f t；hst : s union t = un
iv；hs : IsOpen s；ht : IsOpen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `differentiableOn_univ`：differentiableOn_univ : DifferentiableOn 𝕜 f univ
 ↔ Differentiable 𝕜 f
· 使用引理 `DifferentiableOn.union_of_isOpen`：DifferentiableOn.union_of_isOpen (hf :
 DifferentiableOn 𝕜 f s) (hf' : DifferentiableOn 𝕜 f t) (hs : IsOpen s) (ht : Is
Open t) : Differentiab…
-/
lemma differentiable_of_differentiableOn_union_of_isOpen (hf : DifferentiableOn 𝕜 f s)
    (hf' : DifferentiableOn 𝕜 f t) (hst : s ∪ t = univ) (hs : IsOpen s) (ht : IsOpen t) :
    Differentiable 𝕜 f := by
  rw [← differentiableOn_univ, ← hst]
  exact hf.union_of_isOpen hf' hs ht

/-- If a function is differentiable on open sets `s i`, it is differentiable on their union. -/
/-
**DifferentiableOn.iUnion_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DifferentiableOn.iUnion_of_isOpen {ι : Type*} {s : ι -> Set E} (hf : foral
l i : ι, DifferentiableOn 𝕜 f (s i)) (hs : forall i, IsOpen (s i)) : Differentia
bleOn 𝕜 f (⋃ i, s i)
参数：hf : forall i : ι, DifferentiableOn 𝕜 f (s i)；hs : forall i, IsOpen (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `DifferentiableOn.differentiableAt`：DifferentiableOn.differentiableAt (h 
: DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x) : DifferentiableAt 𝕜 f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x

--- 原说明 ---
If a function is differentiable on open sets `s i`, it is differentiable on thei
r union.
-/
lemma DifferentiableOn.iUnion_of_isOpen {ι : Type*} {s : ι → Set E}
    (hf : ∀ i : ι, DifferentiableOn 𝕜 f (s i)) (hs : ∀ i, IsOpen (s i)) :
    DifferentiableOn 𝕜 f (⋃ i, s i) := by
  rintro x ⟨si, ⟨i, rfl⟩, hxsi⟩
  exact (hf i).differentiableAt ((hs i).mem_nhds hxsi) |>.differentiableWithinAt

/-- A function is differentiable on a union of open sets `s i`
iff it is differentiable on each `s i`. -/
/-
**differentiableOn_iUnion_iff_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：differentiableOn_iUnion_iff_of_isOpen {ι : Type*} {s : ι -> Set E} (hs : f
orall i, IsOpen (s i)) : DifferentiableOn 𝕜 f (⋃ i, s i) ↔ forall i : ι, Differe
ntiableOn 𝕜 f (s i)
参数：hs : forall i, IsOpen (s i)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.mono`：DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t
) (st : s subseteq t) : DifferentiableOn 𝕜 f s
· 使用定理 `Set.subset_iUnion_of_subset`：subset_iUnion_of_subset {s : Set α} {t : ι 
-> Set α} (i : ι) (h : s subseteq t i) : s subseteq ⋃ i, t i
· 使用引理 `DifferentiableOn.iUnion_of_isOpen`：DifferentiableOn.iUnion_of_isOpen {ι 
: Type*} {s : ι -> Set E} (hf : forall i : ι, DifferentiableOn 𝕜 f (s i)) (hs : 
forall i, IsOpen (s i))…

--- 原说明 ---
A function is differentiable on a union of open sets `s i`
iff it is differentiable on each `s i`.
-/
lemma differentiableOn_iUnion_iff_of_isOpen {ι : Type*} {s : ι → Set E}
    (hs : ∀ i, IsOpen (s i)) :
    DifferentiableOn 𝕜 f (⋃ i, s i) ↔ ∀ i : ι, DifferentiableOn 𝕜 f (s i) :=
  ⟨fun h i ↦ h.mono <| subset_iUnion_of_subset i fun _ a ↦ a,
   fun h ↦ DifferentiableOn.iUnion_of_isOpen h hs⟩
/-
**differentiable_of_differentiableOn_iUnion_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：differentiable_of_differentiableOn_iUnion_of_isOpen {ι : Type*} {s : ι -> 
Set E} (hf : forall i : ι, DifferentiableOn 𝕜 f (s i)) (hs : forall i, IsOpen (s
 i)) (hs' : ⋃ i, s i = univ) : Differentiable 𝕜 f
参数：hf : forall i : ι, DifferentiableOn 𝕜 f (s i)；hs : forall i, IsOpen (s i)；hs'
 : ⋃ i, s i = univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `differentiableOn_univ`：differentiableOn_univ : DifferentiableOn 𝕜 f univ
 ↔ Differentiable 𝕜 f
· 使用引理 `DifferentiableOn.iUnion_of_isOpen`：DifferentiableOn.iUnion_of_isOpen {ι 
: Type*} {s : ι -> Set E} (hf : forall i : ι, DifferentiableOn 𝕜 f (s i)) (hs : 
forall i, IsOpen (s i))…
-/
lemma differentiable_of_differentiableOn_iUnion_of_isOpen {ι : Type*} {s : ι → Set E}
    (hf : ∀ i : ι, DifferentiableOn 𝕜 f (s i))
    (hs : ∀ i, IsOpen (s i)) (hs' : ⋃ i, s i = univ) :
    Differentiable 𝕜 f := by
  rw [← differentiableOn_univ, ← hs']
  exact DifferentiableOn.iUnion_of_isOpen hf hs

end differentiableOn_union

/-! ### Asymptotics, both spaces are TVS

In this section we prove big-O and little-O lemmas about differentiable functions
between two topological vector spaces.
-/
section Asymptotics
variable [ContinuousAdd F] [ContinuousSMul 𝕜 F]

/-
**HasFDerivAtFilter.isBigOTVS_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAtFilter.isBigOTVS_sub (hf : HasFDerivAtFilter f f' L) : (fun p =
> f p.1 - f p.2) =O[𝕜; L] fun p => p.1 - p.2
参数：hf : HasFDerivAtFilter f f' L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Asymptotics.IsBigOTVS.fun_add`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type
 u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup
 E] [inst_2 : Topol…
· 使用定理 `Asymptotics.IsLittleOTVS.isBigOTVS`：∀ {α : Type u_1} {𝕜 : Type u_3} {E :
 Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddComm
Group E] [inst_2 : Topol…
· 使用定理 `HasFDerivAtFilter.isLittleOTVS`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `ContinuousLinearMap.isBigOTVS_comp`：∀ {α : Type u_1} {𝕜 : Type u_3} {E :
 Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddComm
Group E] [inst_2 : Topol…
-/
theorem HasFDerivAtFilter.isBigOTVS_sub (hf : HasFDerivAtFilter f f' L) :
    (fun p => f p.1 - f p.2) =O[𝕜; L] fun p => p.1 - p.2 := by
  simpa using hf.isLittleOTVS.isBigOTVS.fun_add f'.isBigOTVS_comp
/-
**HasStrictFDerivAt.isBigOTVS_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.isBigOTVS_sub (hf : HasStrictFDerivAt f f' x) : (fun p :
 E × E => f p.1 - f p.2) =O[𝕜; 𝓝 (x, x)] fun p : E × E => p.1 - p.2
参数：hf : HasStrictFDerivAt f f' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.isBigOTVS_sub`：HasFDerivAtFilter.isBigOTVS_sub (hf : H
asFDerivAtFilter f f' L) : (fun p => f p.1 - f p.2) =O[𝕜; L] fun p => p.1 - p.2
-/
theorem HasStrictFDerivAt.isBigOTVS_sub (hf : HasStrictFDerivAt f f' x) :
    (fun p : E × E => f p.1 - f p.2) =O[𝕜; 𝓝 (x, x)] fun p : E × E => p.1 - p.2 :=
  HasFDerivAtFilter.isBigOTVS_sub hf
/-
**HasFDerivWithinAt.isBigOTVS_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.isBigOTVS_sub (h : HasFDerivWithinAt f f' s x) : (f · - 
f x) =O[𝕜; 𝓝[s] x] (· - x)
参数：h : HasFDerivWithinAt f f' s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.prod_pure`：prod_pure {b : β} : f ×ˢ pure b = map (fun a => (a, b)
) f
· 使用定理 `HasFDerivAtFilter.isBigOTVS_sub`：HasFDerivAtFilter.isBigOTVS_sub (hf : H
asFDerivAtFilter f f' L) : (fun p => f p.1 - f p.2) =O[𝕜; L] fun p => p.1 - p.2
-/
theorem HasFDerivWithinAt.isBigOTVS_sub (h : HasFDerivWithinAt f f' s x) :
    (f · - f x) =O[𝕜; 𝓝[s] x] (· - x) := by
  simpa using! HasFDerivAtFilter.isBigOTVS_sub h
/-
**DifferentiableWithinAt.isBigOTVS_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.isBigOTVS_sub (h : DifferentiableWithinAt 𝕜 f s x) 
: (f · - f x) =O[𝕜; 𝓝[s] x] (· - x)
参数：h : DifferentiableWithinAt 𝕜 f s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.isBigOTVS_sub`：HasFDerivWithinAt.isBigOTVS_sub (h : Ha
sFDerivWithinAt f f' s x) : (f · - f x) =O[𝕜; 𝓝[s] x] (· - x)
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
lemma DifferentiableWithinAt.isBigOTVS_sub (h : DifferentiableWithinAt 𝕜 f s x) :
    (f · - f x) =O[𝕜; 𝓝[s] x] (· - x) :=
  h.hasFDerivWithinAt.isBigOTVS_sub
/-
**HasFDerivAt.isBigOTVS_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.isBigOTVS_sub (h : HasFDerivAt f f' x) : (f · - f x) =O[𝕜; 𝓝 x
] (· - x)
参数：h : HasFDerivAt f f' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.prod_pure`：prod_pure {b : β} : f ×ˢ pure b = map (fun a => (a, b)
) f
· 使用定理 `HasFDerivAtFilter.isBigOTVS_sub`：HasFDerivAtFilter.isBigOTVS_sub (hf : H
asFDerivAtFilter f f' L) : (fun p => f p.1 - f p.2) =O[𝕜; L] fun p => p.1 - p.2
-/
theorem HasFDerivAt.isBigOTVS_sub (h : HasFDerivAt f f' x) : (f · - f x) =O[𝕜; 𝓝 x] (· - x) := by
  simpa using! HasFDerivAtFilter.isBigOTVS_sub h
/-
**DifferentiableAt.isBigOTVS_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.isBigOTVS_sub (h : DifferentiableAt 𝕜 f x) : (f · - f x) 
=O[𝕜; 𝓝 x] (· - x)
参数：h : DifferentiableAt 𝕜 f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.isBigOTVS_sub`：HasFDerivAt.isBigOTVS_sub (h : HasFDerivAt f 
f' x) : (f · - f x) =O[𝕜; 𝓝 x] (· - x)
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.isBigOTVS_sub (h : DifferentiableAt 𝕜 f x) :
    (f · - f x) =O[𝕜; 𝓝 x] (· - x) :=
  h.hasFDerivAt.isBigOTVS_sub

end Asymptotics

section Continuous

/-! ### Deducing continuity from differentiability -/
variable [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F]

/-
**HasFDerivAtFilter.tendsto_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAtFilter.tendsto_nhds {L : Filter E} (hL : L <= 𝓝 x) (h : HasFDer
ivAtFilter f f' (L ×ˢ pure x)) : Tendsto f L (𝓝 (f x))
参数：hL : L <= 𝓝 x；h : HasFDerivAtFilter f f' (L ×ˢ pure x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.trans_isLittleOTVS`：∀ {α : Type u_1} {𝕜 : Type u_3
} {E : Type u_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜
]   [inst_1 : AddCommGroup E] …
· 使用定理 `Asymptotics.IsBigOTVS.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {𝕜 :
 Type u_3} {E : Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [i
nst_1 : AddCommGroup E] …
· 使用定理 `HasFDerivAtFilter.isBigOTVS_sub`：HasFDerivAtFilter.isBigOTVS_sub (hf : H
asFDerivAtFilter f f' L) : (fun p => f p.1 - f p.2) =O[𝕜; L] fun p => p.1 - p.2
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Filter.prod_pure`：prod_pure {b : β} : f ×ˢ pure b = map (fun a => (a, b)
) f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Asymptotics.isLittleOTVS_one`：isLittleOTVS_one [ContinuousSMul 𝕜 E] : f 
=o[𝕜; l] (1 : α -> 𝕜) ↔ Tendsto f l (𝓝 0)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `Filter.Tendsto.add_const`：∀ {M : Type u_1} [inst : TopologicalSpace M] [
inst_1 : Add M] [SeparatelyContinuousAdd M] {α : Type u_2} {f : α → M}   {x : Fi
lter α} {a : M…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_id'`：tendsto_id' {x y : Filter α} : Tendsto id x y ↔ x <=
 y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem HasFDerivAtFilter.tendsto_nhds {L : Filter E} (hL : L ≤ 𝓝 x)
    (h : HasFDerivAtFilter f f' (L ×ˢ pure x)) :
    Tendsto f L (𝓝 (f x)) := by
  have : (f · - f x) =o[𝕜; L] (1 : E → 𝕜) := by
    refine h.isBigOTVS_sub |>.comp_tendsto prod_pure.ge |>.trans_isLittleOTVS ?_
    rw [isLittleOTVS_one]
    simpa [sub_eq_add_neg] using! (tendsto_id'.mpr hL).add_const (-x)
  rw [isLittleOTVS_one] at this
  simpa using! this.add_const (f x)
/-
**HasFDerivWithinAt.continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.continuousWithinAt (h : HasFDerivWithinAt f f' s x) : Co
ntinuousWithinAt f s x
参数：h : HasFDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.tendsto_nhds`：HasFDerivAtFilter.tendsto_nhds {L : Filt
er E} (hL : L <= 𝓝 x) (h : HasFDerivAtFilter f f' (L ×ˢ pure x)) : Tendsto f L (
𝓝 (f x))
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem HasFDerivWithinAt.continuousWithinAt (h : HasFDerivWithinAt f f' s x) :
    ContinuousWithinAt f s x :=
  HasFDerivAtFilter.tendsto_nhds inf_le_left h
/-
**HasFDerivAt.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.continuousAt (h : HasFDerivAt f f' x) : ContinuousAt f x
参数：h : HasFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.tendsto_nhds`：HasFDerivAtFilter.tendsto_nhds {L : Filt
er E} (hL : L <= 𝓝 x) (h : HasFDerivAtFilter f f' (L ×ˢ pure x)) : Tendsto f L (
𝓝 (f x))
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem HasFDerivAt.continuousAt (h : HasFDerivAt f f' x) : ContinuousAt f x :=
  HasFDerivAtFilter.tendsto_nhds le_rfl h

@[fun_prop]
/-
**DifferentiableWithinAt.continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.continuousWithinAt (h : DifferentiableWithinAt 𝕜 f 
s x) : ContinuousWithinAt f s x
参数：h : DifferentiableWithinAt 𝕜 f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.continuousWithinAt`：HasFDerivWithinAt.continuousWithin
At (h : HasFDerivWithinAt f f' s x) : ContinuousWithinAt f s x
-/
theorem DifferentiableWithinAt.continuousWithinAt (h : DifferentiableWithinAt 𝕜 f s x) :
    ContinuousWithinAt f s x :=
  let ⟨_, hf'⟩ := h
  hf'.continuousWithinAt

@[fun_prop]
/-
**DifferentiableAt.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.continuousAt (h : DifferentiableAt 𝕜 f x) : ContinuousAt 
f x
参数：h : DifferentiableAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.continuousAt`：HasFDerivAt.continuousAt (h : HasFDerivAt f f'
 x) : ContinuousAt f x
-/
theorem DifferentiableAt.continuousAt (h : DifferentiableAt 𝕜 f x) : ContinuousAt f x :=
  let ⟨_, hf'⟩ := h
  hf'.continuousAt

@[fun_prop]
/-
**DifferentiableOn.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.continuousOn (h : DifferentiableOn 𝕜 f s) : ContinuousOn 
f s
参数：h : DifferentiableOn 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.continuousWithinAt`：DifferentiableWithinAt.contin
uousWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : ContinuousWithinAt f s x
-/
theorem DifferentiableOn.continuousOn (h : DifferentiableOn 𝕜 f s) : ContinuousOn f s := fun x hx =>
  (h x hx).continuousWithinAt

@[fun_prop]
/-
**Differentiable.continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.continuous (h : Differentiable 𝕜 f) : Continuous f
参数：h : Differentiable 𝕜 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `DifferentiableAt.continuousAt`：DifferentiableAt.continuousAt (h : Differ
entiableAt 𝕜 f x) : ContinuousAt f x
-/
theorem Differentiable.continuous (h : Differentiable 𝕜 f) : Continuous f :=
  continuous_iff_continuousAt.2 fun x => (h x).continuousAt
/-
**HasStrictFDerivAt.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 `HasStrictFDerivAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : TopologicalSpace E] 
{F : Type u_3} [inst_4 : AddCommGroup F]   [inst_5 : _root_.Module 𝕜 F] [inst_6 
: TopologicalSpace F] {f : E → F} {f' : E →L[𝕜] F} {x : E} [ContinuousAdd E]   [
ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F], HasStrictFDerivAt f 
f' x → ContinuousAt f x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.continuousAt`：HasFDerivAt.continuousAt (h : HasFDerivAt f f'
 x) : ContinuousAt f x
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
-/
protected theorem HasStrictFDerivAt.continuousAt (hf : HasStrictFDerivAt f f' x) :
    ContinuousAt f x :=
  hf.hasFDerivAt.continuousAt

end Continuous

section id

/-! ### Derivative of the identity -/

/-
**hasFDerivAtFilter_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAtFilter_id (L : Filter (E × E)) : HasFDerivAtFilter id (.id 𝕜 E)
 L
参数：L : Filter (E × E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleOTVS.congr_left`：∀ {α : Type u_1} {𝕜 : Type u_3} {E 
: Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCom
mGroup E] [inst_2 : Topol…
· 使用定理 `Asymptotics.IsLittleOTVS.zero`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type
 u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup
 E] [inst_2 : Topol…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
### Derivative of the identity
-/
theorem hasFDerivAtFilter_id (L : Filter (E × E)) : HasFDerivAtFilter id (.id 𝕜 E) L :=
  .of_isLittleOTVS <| (IsLittleOTVS.zero _ _).congr_left <| by simp

@[fun_prop]
/-
**hasStrictFDerivAt_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_id (x : E) : HasStrictFDerivAt id (.id 𝕜 E) x
参数：x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_id`：hasFDerivAtFilter_id (L : Filter (E × E)) : HasFDe
rivAtFilter id (.id 𝕜 E) L
-/
theorem hasStrictFDerivAt_id (x : E) : HasStrictFDerivAt id (.id 𝕜 E) x :=
  hasFDerivAtFilter_id _

@[fun_prop]
/-
**hasFDerivWithinAt_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_id (x : E) (s : Set E) : HasFDerivWithinAt id (.id 𝕜 E) 
s x
参数：x : E；s : Set E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_id`：hasFDerivAtFilter_id (L : Filter (E × E)) : HasFDe
rivAtFilter id (.id 𝕜 E) L
-/
theorem hasFDerivWithinAt_id (x : E) (s : Set E) : HasFDerivWithinAt id (.id 𝕜 E) s x :=
  hasFDerivAtFilter_id _

@[fun_prop]
/-
**hasFDerivAt_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_id (x : E) : HasFDerivAt id (.id 𝕜 E) x
参数：x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_id`：hasFDerivAtFilter_id (L : Filter (E × E)) : HasFDe
rivAtFilter id (.id 𝕜 E) L
-/
theorem hasFDerivAt_id (x : E) : HasFDerivAt id (.id 𝕜 E) x :=
  hasFDerivAtFilter_id _

@[to_fun (attr := simp, fun_prop) differentiableAt_fun_id]
/-
**differentiableAt_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_id : DifferentiableAt 𝕜 id x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `hasFDerivAt_id`：hasFDerivAt_id (x : E) : HasFDerivAt id (.id 𝕜 E) x
-/
theorem differentiableAt_id : DifferentiableAt 𝕜 id x :=
  (hasFDerivAt_id x).differentiableAt

@[to_fun (attr := fun_prop) differentiableWithinAt_fun_id]
/-
**differentiableWithinAt_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_id : DifferentiableWithinAt 𝕜 id s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x
-/
theorem differentiableWithinAt_id : DifferentiableWithinAt 𝕜 id s x :=
  differentiableAt_id.differentiableWithinAt

@[deprecated (since := "2026-05-17")]
alias differentiableWithinAt_id' := differentiableWithinAt_fun_id

@[to_fun (attr := simp, fun_prop) differentiable_fun_id]
/-
**differentiable_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiable_id : Differentiable 𝕜 (id : E -> E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x
-/
theorem differentiable_id : Differentiable 𝕜 (id : E → E) := fun _ => differentiableAt_id

@[fun_prop]
/-
**differentiableOn_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_id : DifferentiableOn 𝕜 id s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.differentiableOn`：Differentiable.differentiableOn (h : Di
fferentiable 𝕜 f) : DifferentiableOn 𝕜 f s
· 使用定理 `differentiable_id`：differentiable_id : Differentiable 𝕜 (id : E -> E)
-/
theorem differentiableOn_id : DifferentiableOn 𝕜 id s :=
  differentiable_id.differentiableOn

@[to_fun (attr := simp) fderiv_fun_id]
/-
**fderiv_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_id [ContinuousAdd E] [ContinuousSMul 𝕜 E] [T2Space E] : fderiv 𝕜 id
 x = .id 𝕜 E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `hasFDerivAt_id`：hasFDerivAt_id (x : E) : HasFDerivAt id (.id 𝕜 E) x
-/
theorem fderiv_id [ContinuousAdd E] [ContinuousSMul 𝕜 E] [T2Space E] : fderiv 𝕜 id x = .id 𝕜 E :=
  HasFDerivAt.fderiv (hasFDerivAt_id x)

@[deprecated (since := "2026-05-17")] alias fderiv_id' := fderiv_fun_id

@[to_fun fderivWithin_fun_id]
/-
**fderivWithin_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_id [ContinuousAdd E] [ContinuousSMul 𝕜 E] [T2Space E] (hxs : 
UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 id s x = .id 𝕜 E
参数：hxs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DifferentiableAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x
· 使用定理 `fderiv_id`：fderiv_id [ContinuousAdd E] [ContinuousSMul 𝕜 E] [T2Space E] 
: fderiv 𝕜 id x = .id 𝕜 E
-/
theorem fderivWithin_id [ContinuousAdd E] [ContinuousSMul 𝕜 E] [T2Space E]
    (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 id s x = .id 𝕜 E := by
  rw [DifferentiableAt.fderivWithin differentiableAt_id hxs]
  exact fderiv_id

@[deprecated (since := "2026-05-17")] alias fderivWithin_id' := fderivWithin_fun_id

end id

end

section NormedCodomain
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {f : E → F}
variable {f' : E →L[𝕜] F}
variable {x x₀ : E}
variable {s : Set E}
variable {L : Filter (E × E)}

/-
**HasFDerivAtFilter.isEquivalent_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAtFilter.isEquivalent_sub (hf : HasFDerivAtFilter f f' L) (hf' : 
Topology.IsInducing f') : (fun p => f p.1 - f p.2) ~[L] (fun p => f' (p.1 - p.2)
)
参数：hf : HasFDerivAtFilter f f' L；hf' : Topology.IsInducing f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsEquivalent.eq_1`：∀ {α : Type u_1} {E' : Type u_6} [inst : 
SeminormedAddCommGroup E'] (l : Filter α) (u v : α → E'),   Asymptotics.IsEquiva
lent l u v = (u - v…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Asymptotics.isLittleOTVS_iff_isLittleO`：isLittleOTVS_iff_isLittleO : f =
o[𝕜; l] g ↔ f =o[l] g
· 使用定理 `Asymptotics.IsLittleOTVS.trans_isBigOTVS`：∀ {α : Type u_1} {𝕜 : Type u_3
} {E : Type u_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜
]   [inst_1 : AddCommGroup E] …
· 使用定理 `HasFDerivAtFilter.isLittleOTVS`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `Asymptotics.IsThetaTVS.isBigOTVS`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : T
ype u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGr
oup E] [inst_2 : Topol…
· 使用定理 `Asymptotics.IsThetaTVS.symm`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u
_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup E
] [inst_2 : Topol…
· 使用定理 `ContinuousLinearMap.isThetaTVS_comp`：∀ {α : Type u_1} {𝕜 : Type u_3} {E 
: Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCom
mGroup E] [inst_2 : Topol…
-/
theorem HasFDerivAtFilter.isEquivalent_sub (hf : HasFDerivAtFilter f f' L)
    (hf' : Topology.IsInducing f') :
    (fun p ↦ f p.1 - f p.2) ~[L] (fun p ↦ f' (p.1 - p.2)) := by
  rw [IsEquivalent, ← isLittleOTVS_iff_isLittleO (𝕜 := 𝕜)]
  exact hf.isLittleOTVS.trans_isBigOTVS <| f'.isThetaTVS_comp hf' |>.symm.isBigOTVS
/-
**HasFDerivAtFilter.isThetaTVS_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAtFilter.isThetaTVS_sub (hf : HasFDerivAtFilter f f' L) (hf' : To
pology.IsInducing f') : (fun p => f p.1 - f p.2) =Θ[𝕜; L] (fun p => p.1 - p.2)
参数：hf : HasFDerivAtFilter f f' L；hf' : Topology.IsInducing f'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsThetaTVS.trans`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type 
u_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜]   [inst_1 
: AddCommGroup E] …
· 使用定理 `Asymptotics.IsTheta.isThetaTVS`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Typ
e u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : SeminormedA
ddCommGroup E] [inst…
· 使用定理 `Asymptotics.IsEquivalent.isTheta`：∀ {α : Type u_1} {β : Type u_2} [inst 
: NormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent
 l u v → u =Θ[l] v
· 使用定理 `HasFDerivAtFilter.isEquivalent_sub`：HasFDerivAtFilter.isEquivalent_sub (
hf : HasFDerivAtFilter f f' L) (hf' : Topology.IsInducing f') : (fun p => f p.1 
- f p.2) ~[L] (fun p => …
· 使用定理 `ContinuousLinearMap.isThetaTVS_comp`：∀ {α : Type u_1} {𝕜 : Type u_3} {E 
: Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCom
mGroup E] [inst_2 : Topol…
-/
theorem HasFDerivAtFilter.isThetaTVS_sub (hf : HasFDerivAtFilter f f' L)
    (hf' : Topology.IsInducing f') :
    (fun p ↦ f p.1 - f p.2) =Θ[𝕜; L] (fun p ↦ p.1 - p.2) :=
  hf.isEquivalent_sub hf' |>.isTheta.isThetaTVS.trans <| f'.isThetaTVS_comp hf'
/-
**HasFDerivAt.isEquivalent_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.isEquivalent_sub (hf : HasFDerivAt f f' x) (hf' : Topology.IsI
nducing f') : (f · - f x) ~[𝓝 x] (f' <| · - x)
参数：hf : HasFDerivAt f f' x；hf' : Topology.IsInducing f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.prod_pure`：prod_pure {b : β} : f ×ˢ pure b = map (fun a => (a, b)
) f
· 使用定理 `HasFDerivAtFilter.isEquivalent_sub`：HasFDerivAtFilter.isEquivalent_sub (
hf : HasFDerivAtFilter f f' L) (hf' : Topology.IsInducing f') : (fun p => f p.1 
- f p.2) ~[L] (fun p => …
-/
theorem HasFDerivAt.isEquivalent_sub (hf : HasFDerivAt f f' x) (hf' : Topology.IsInducing f') :
    (f · - f x) ~[𝓝 x] (f' <| · - x) := by
  simpa using! HasFDerivAtFilter.isEquivalent_sub hf hf'
/-
**HasFDerivAt.isThetaTVS_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.isThetaTVS_sub (hf : HasFDerivAt f f' x) (hf' : Topology.IsInd
ucing f') : (f · - f x) =Θ[𝕜; 𝓝 x] (· - x)
参数：hf : HasFDerivAt f f' x；hf' : Topology.IsInducing f'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.prod_pure`：prod_pure {b : β} : f ×ˢ pure b = map (fun a => (a, b)
) f
· 使用定理 `HasFDerivAtFilter.isThetaTVS_sub`：HasFDerivAtFilter.isThetaTVS_sub (hf :
 HasFDerivAtFilter f f' L) (hf' : Topology.IsInducing f') : (fun p => f p.1 - f 
p.2) =Θ[𝕜; L] (fun p =…
-/
theorem HasFDerivAt.isThetaTVS_sub (hf : HasFDerivAt f f' x) (hf' : Topology.IsInducing f') :
    (f · - f x) =Θ[𝕜; 𝓝 x] (· - x) := by
  simpa [IsThetaTVS] using! HasFDerivAtFilter.isThetaTVS_sub hf hf'
/-
**HasFDerivWithinAt.isEquivalent_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.isEquivalent_sub (hf : HasFDerivWithinAt f f' s x) (hf' 
: Topology.IsInducing f') : (f · - f x) ~[𝓝[s] x] (f' <| · - x)
参数：hf : HasFDerivWithinAt f f' s x；hf' : Topology.IsInducing f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.prod_pure`：prod_pure {b : β} : f ×ˢ pure b = map (fun a => (a, b)
) f
· 使用定理 `HasFDerivAtFilter.isEquivalent_sub`：HasFDerivAtFilter.isEquivalent_sub (
hf : HasFDerivAtFilter f f' L) (hf' : Topology.IsInducing f') : (fun p => f p.1 
- f p.2) ~[L] (fun p => …
-/
theorem HasFDerivWithinAt.isEquivalent_sub (hf : HasFDerivWithinAt f f' s x)
    (hf' : Topology.IsInducing f') :
    (f · - f x) ~[𝓝[s] x] (f' <| · - x) := by
  simpa using! HasFDerivAtFilter.isEquivalent_sub hf hf'
/-
**HasFDerivWithinAt.isThetaTVS_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.isThetaTVS_sub (hf : HasFDerivWithinAt f f' s x) (hf' : 
Topology.IsInducing f') : (f · - f x) =Θ[𝕜; 𝓝[s] x] (· - x)
参数：hf : HasFDerivWithinAt f f' s x；hf' : Topology.IsInducing f'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.prod_pure`：prod_pure {b : β} : f ×ˢ pure b = map (fun a => (a, b)
) f
· 使用定理 `HasFDerivAtFilter.isThetaTVS_sub`：HasFDerivAtFilter.isThetaTVS_sub (hf :
 HasFDerivAtFilter f f' L) (hf' : Topology.IsInducing f') : (fun p => f p.1 - f 
p.2) =Θ[𝕜; L] (fun p =…
-/
theorem HasFDerivWithinAt.isThetaTVS_sub (hf : HasFDerivWithinAt f f' s x)
    (hf' : Topology.IsInducing f') :
    (f · - f x) =Θ[𝕜; 𝓝[s] x] (· - x) := by
  simpa [IsThetaTVS] using! HasFDerivAtFilter.isThetaTVS_sub hf hf'
/-
**HasStrictFDerivAt.isEquivalent_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.isEquivalent_sub (hf : HasStrictFDerivAt f f' x) (hf' : 
Topology.IsInducing f') : (fun p : E × E => f p.1 - f p.2) ~[𝓝 (x, x)] (fun p =>
 f' (p.1 - p.2))
参数：hf : HasStrictFDerivAt f f' x；hf' : Topology.IsInducing f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.isEquivalent_sub`：HasFDerivAtFilter.isEquivalent_sub (
hf : HasFDerivAtFilter f f' L) (hf' : Topology.IsInducing f') : (fun p => f p.1 
- f p.2) ~[L] (fun p => …
-/
theorem HasStrictFDerivAt.isEquivalent_sub (hf : HasStrictFDerivAt f f' x)
    (hf' : Topology.IsInducing f') :
    (fun p : E × E ↦ f p.1 - f p.2) ~[𝓝 (x, x)] (fun p ↦ f' (p.1 - p.2)) :=
  HasFDerivAtFilter.isEquivalent_sub hf hf'
/-
**HasStrictFDerivAt.isThetaTVS_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.isThetaTVS_sub (hf : HasStrictFDerivAt f f' x) (hf' : To
pology.IsInducing f') : (fun p : E × E => f p.1 - f p.2) =Θ[𝕜; 𝓝 (x, x)] (fun p 
=> p.1 - p.2)
参数：hf : HasStrictFDerivAt f f' x；hf' : Topology.IsInducing f'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.isThetaTVS_sub`：HasFDerivAtFilter.isThetaTVS_sub (hf :
 HasFDerivAtFilter f f' L) (hf' : Topology.IsInducing f') : (fun p => f p.1 - f 
p.2) =Θ[𝕜; L] (fun p =…
-/
theorem HasStrictFDerivAt.isThetaTVS_sub (hf : HasStrictFDerivAt f f' x)
    (hf' : Topology.IsInducing f') :
    (fun p : E × E ↦ f p.1 - f p.2) =Θ[𝕜; 𝓝 (x, x)] (fun p ↦ p.1 - p.2) :=
  HasFDerivAtFilter.isThetaTVS_sub hf hf'

end NormedCodomain

-- These lemmas won't generalize to Topological Vector Spaces, at least without changing the
-- statement.
section not_TVS
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {f : E → F}
variable {f' : E →L[𝕜] F}
variable {x x₀ : E}
variable {s : Set E}
variable {L : Filter (E × E)}

/-
**hasFDerivAtFilter_iff_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAtFilter_iff_tendsto : HasFDerivAtFilter f f' L ↔ Tendsto (fun p 
=> ‖p.1 - p.2‖⁻¹ * ‖f p.1 - f p.2 - f' (p.1 - p.2)‖) L (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasFDerivAtFilter_iff_isLittleO`：hasFDerivAtFilter_iff_isLittleO {L : Fi
lter (E × E)} : HasFDerivAtFilter f f' L ↔ (fun p => f p.1 - f p.2 - f' (p.1 - p
.2)) =o[L] fun p => p…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Asymptotics.isLittleO_norm_left`：isLittleO_norm_left : (fun x => ‖f' x‖)
 =o[l] g ↔ f' =o[l] g
· 使用定理 `Asymptotics.isLittleO_norm_right`：isLittleO_norm_right : (f =o[l] fun x 
=> ‖g' x‖) ↔ f =o[l] g'
· 使用定理 `Asymptotics.isLittleO_iff_tendsto`：isLittleO_iff_tendsto {f g : α -> 𝕜} 
(hgf : forall x, g x = 0 -> f x = 0) : f =o[l] g ↔ Tendsto (fun x => f x / g x) 
l (𝓝 0)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
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
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasFDerivAtFilter_iff_tendsto :
    HasFDerivAtFilter f f' L ↔
      Tendsto (fun p => ‖p.1 - p.2‖⁻¹ * ‖f p.1 - f p.2 - f' (p.1 - p.2)‖) L (𝓝 0) := by
  rw [hasFDerivAtFilter_iff_isLittleO, ← isLittleO_norm_left, ← isLittleO_norm_right,
    isLittleO_iff_tendsto]
  · simp [div_eq_inv_mul]
  · simp +contextual [sub_eq_zero]
/-
**hasFDerivWithinAt_iff_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_iff_tendsto : HasFDerivWithinAt f f' s x ↔ Tendsto (fun 
x' => ‖x' - x‖⁻¹ * ‖f x' - f x - f' (x' - x)‖) (𝓝[s] x) (𝓝 0)
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
theorem hasFDerivWithinAt_iff_tendsto :
    HasFDerivWithinAt f f' s x ↔
      Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - f' (x' - x)‖) (𝓝[s] x) (𝓝 0) := by
  simp [HasFDerivWithinAt, hasFDerivAtFilter_iff_tendsto, Function.comp_def]
/-
**hasFDerivAt_iff_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_iff_tendsto : HasFDerivAt f f' x ↔ Tendsto (fun x' => ‖x' - x‖
⁻¹ * ‖f x' - f x - f' (x' - x)‖) (𝓝 x) (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasFDerivWithinAt_univ`：hasFDerivWithinAt_univ : HasFDerivWithinAt f f' 
univ x ↔ HasFDerivAt f f' x
· 使用定理 `hasFDerivWithinAt_iff_tendsto`：hasFDerivWithinAt_iff_tendsto : HasFDeriv
WithinAt f f' s x ↔ Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - f' (x' - x)‖) 
(𝓝[s] x) (𝓝 0)
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem hasFDerivAt_iff_tendsto :
    HasFDerivAt f f' x ↔
      Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - f' (x' - x)‖) (𝓝 x) (𝓝 0) := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_iff_tendsto, nhdsWithin_univ]
/-
**hasFDerivAt_iff_isLittleO_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_iff_isLittleO_nhds_zero : HasFDerivAt f f' x ↔ (fun h : E => f
 (x + h) - f x - f' h) =o[𝓝 0] fun h => h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasFDerivAt_iff_isLittleO`：hasFDerivAt_iff_isLittleO : HasFDerivAt f f' 
x ↔ (fun x' => f x' - f x - f' (x' - x)) =o[𝓝 x] (fun x' => x' - x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_add_left_nhds_zero`：∀ {G : Type w} [inst : TopologicalSpace G] [inst
_1 : AddGroup G] [IsTopologicalAddGroup G] (x : G),   Filter.map (fun x_1 => x +
 x_1) (nhds …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Asymptotics.isLittleO_map`：isLittleO_map {k : β -> α} {l : Filter β} : f
 =o[map k l] g ↔ (f ∘ k) =o[l] (g ∘ k)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasFDerivAt_iff_isLittleO_nhds_zero :
    HasFDerivAt f f' x ↔ (fun h : E => f (x + h) - f x - f' h) =o[𝓝 0] fun h => h := by
  rw [hasFDerivAt_iff_isLittleO, ← map_add_left_nhds_zero x, isLittleO_map]
  simp [Function.comp_def]
/-
**HasStrictFDerivAt.isBigO_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.isBigO_sub (hf : HasStrictFDerivAt f f' x) : (fun p : E 
× E => f p.1 - f p.2) =O[𝓝 (x, x)] fun p : E × E => p.1 - p.2
参数：hf : HasStrictFDerivAt f f' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.isBigO`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type 
u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : SeminormedAdd
CommGroup E] [inst…
· 使用定理 `HasStrictFDerivAt.isBigOTVS_sub`：HasStrictFDerivAt.isBigOTVS_sub (hf : H
asStrictFDerivAt f f' x) : (fun p : E × E => f p.1 - f p.2) =O[𝕜; 𝓝 (x, x)] fun 
p : E × E => p.1 - p.…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem HasStrictFDerivAt.isBigO_sub (hf : HasStrictFDerivAt f f' x) :
    (fun p : E × E => f p.1 - f p.2) =O[𝓝 (x, x)] fun p : E × E => p.1 - p.2 :=
  hf.isBigOTVS_sub.isBigO
/-
**HasFDerivAtFilter.isBigO_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAtFilter.isBigO_sub (h : HasFDerivAtFilter f f' L) : (fun p => f 
p.1 - f p.2) =O[L] fun p => p.1 - p.2
参数：h : HasFDerivAtFilter f f' L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.isBigO`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type 
u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : SeminormedAdd
CommGroup E] [inst…
· 使用定理 `HasFDerivAtFilter.isBigOTVS_sub`：HasFDerivAtFilter.isBigOTVS_sub (hf : H
asFDerivAtFilter f f' L) : (fun p => f p.1 - f p.2) =O[𝕜; L] fun p => p.1 - p.2
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem HasFDerivAtFilter.isBigO_sub (h : HasFDerivAtFilter f f' L) :
    (fun p => f p.1 - f p.2) =O[L] fun p => p.1 - p.2 :=
  h.isBigOTVS_sub.isBigO
/-
**HasFDerivWithinAt.isBigO_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.isBigO_sub (h : HasFDerivWithinAt f f' s x₀) : (f · - f 
x₀) =O[𝓝[s] x₀] (· - x₀)
参数：h : HasFDerivWithinAt f f' s x₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.isBigO`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type 
u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : SeminormedAdd
CommGroup E] [inst…
· 使用定理 `HasFDerivWithinAt.isBigOTVS_sub`：HasFDerivWithinAt.isBigOTVS_sub (h : Ha
sFDerivWithinAt f f' s x) : (f · - f x) =O[𝕜; 𝓝[s] x] (· - x)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem HasFDerivWithinAt.isBigO_sub (h : HasFDerivWithinAt f f' s x₀) :
    (f · - f x₀) =O[𝓝[s] x₀] (· - x₀) :=
  h.isBigOTVS_sub.isBigO
/-
**DifferentiableWithinAt.isBigO_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.isBigO_sub (h : DifferentiableWithinAt 𝕜 f s x₀) : 
(f · - f x₀) =O[𝓝[s] x₀] (· - x₀)
参数：h : DifferentiableWithinAt 𝕜 f s x₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.isBigO_sub`：HasFDerivWithinAt.isBigO_sub (h : HasFDeri
vWithinAt f f' s x₀) : (f · - f x₀) =O[𝓝[s] x₀] (· - x₀)
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
lemma DifferentiableWithinAt.isBigO_sub (h : DifferentiableWithinAt 𝕜 f s x₀) :
    (f · - f x₀) =O[𝓝[s] x₀] (· - x₀) :=
  h.hasFDerivWithinAt.isBigO_sub
/-
**HasFDerivAt.isBigO_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.isBigO_sub (h : HasFDerivAt f f' x₀) : (f · - f x₀) =O[𝓝 x₀] (
· - x₀)
参数：h : HasFDerivAt f f' x₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.isBigO`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type 
u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : SeminormedAdd
CommGroup E] [inst…
· 使用定理 `HasFDerivAt.isBigOTVS_sub`：HasFDerivAt.isBigOTVS_sub (h : HasFDerivAt f 
f' x) : (f · - f x) =O[𝕜; 𝓝 x] (· - x)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem HasFDerivAt.isBigO_sub (h : HasFDerivAt f f' x₀) : (f · - f x₀) =O[𝓝 x₀] (· - x₀) :=
  h.isBigOTVS_sub.isBigO
/-
**DifferentiableAt.isBigO_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.isBigO_sub (h : DifferentiableAt 𝕜 f x₀) : (f · - f x₀) =
O[𝓝 x₀] (· - x₀)
参数：h : DifferentiableAt 𝕜 f x₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.isBigO_sub`：HasFDerivAt.isBigO_sub (h : HasFDerivAt f f' x₀)
 : (f · - f x₀) =O[𝓝 x₀] (· - x₀)
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.isBigO_sub (h : DifferentiableAt 𝕜 f x₀) :
    (f · - f x₀) =O[𝓝 x₀] (· - x₀) :=
  h.hasFDerivAt.isBigO_sub
/-
**Asymptotics.IsBigO.hasFDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Asymptotics.IsBigO.hasFDerivWithinAt {n : Nat} (h : f =O[𝓝[s] x₀] fun x =>
 ‖x - x₀‖ ^ n) (hx₀ : x₀ in s) (hn : 1 < n) : HasFDerivWithinAt f (0 : E ->L[𝕜] 
F) s x₀
参数：h : f =O[𝓝[s] x₀] fun x => ‖x - x₀‖ ^ n；hx₀ : x₀ in s；hn : 1 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Asymptotics.IsBigO.eq_zero_of_norm_pow_within`：∀ {E'' : Type u_9} {F'' :
 Type u_10} [inst : NormedAddCommGroup E''] [inst_1 : NormedAddCommGroup F''] {f
 : E'' → F''}   {s : Set E''} {x₀ :…
· 使用定理 `LT.lt.ne_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Asymptotics.IsBigO.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} {G :
 Type u_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : Seminor
medAddCommGroup F'] {l :…
· 使用定理 `Asymptotics.IsLittleO.mono`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_
4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}   {l l' : Filter α}
, f =o[l'] g → l…
· 使用定理 `Asymptotics.isLittleO_pow_sub_sub`：isLittleO_pow_sub_sub (x₀ : E') {m : 
Nat} (h : 1 < m) : (fun x => ‖x - x₀‖ ^ m) =o[𝓝 x₀] fun x => x - x₀
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
-/
theorem Asymptotics.IsBigO.hasFDerivWithinAt {n : ℕ}
    (h : f =O[𝓝[s] x₀] fun x => ‖x - x₀‖ ^ n) (hx₀ : x₀ ∈ s) (hn : 1 < n) :
    HasFDerivWithinAt f (0 : E →L[𝕜] F) s x₀ := by
  simp_rw [hasFDerivWithinAt_iff_isLittleO,
    h.eq_zero_of_norm_pow_within hx₀ hn.ne_bot, zero_apply, sub_zero,
    h.trans_isLittleO ((isLittleO_pow_sub_sub x₀ hn).mono nhdsWithin_le_nhds)]
/-
**Asymptotics.IsBigO.hasFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Asymptotics.IsBigO.hasFDerivAt {x₀ : E} {n : Nat} (h : f =O[𝓝 x₀] fun x =>
 ‖x - x₀‖ ^ n) (hn : 1 < n) : HasFDerivAt f (0 : E ->L[𝕜] F) x₀
参数：h : f =O[𝓝 x₀] fun x => ‖x - x₀‖ ^ n；hn : 1 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.hasFDerivAt_of_univ`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.M
odule 𝕜 E] [inst_3 : Topolo…
· 使用定理 `Asymptotics.IsBigO.hasFDerivWithinAt`：Asymptotics.IsBigO.hasFDerivWithin
At {n : Nat} (h : f =O[𝓝[s] x₀] fun x => ‖x - x₀‖ ^ n) (hx₀ : x₀ in s) (hn : 1 <
 n) : HasFDerivWithinAt f …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem Asymptotics.IsBigO.hasFDerivAt {x₀ : E} {n : ℕ} (h : f =O[𝓝 x₀] fun x => ‖x - x₀‖ ^ n)
    (hn : 1 < n) : HasFDerivAt f (0 : E →L[𝕜] F) x₀ := by
  rw [← nhdsWithin_univ] at h
  exact (h.hasFDerivWithinAt (mem_univ _) hn).hasFDerivAt_of_univ
/-
**HasStrictFDerivAt.isTheta_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.isTheta_sub (hf : HasStrictFDerivAt f f' x) (hf' : Topol
ogy.IsInducing f') : (fun p : E × E => f p.1 - f p.2) =Θ[𝓝 (x, x)] (fun p => p.1
 - p.2)
参数：hf : HasStrictFDerivAt f f' x；hf' : Topology.IsInducing f'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsThetaTVS.isTheta`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Typ
e u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : SeminormedA
ddCommGroup E] [inst…
· 使用定理 `HasStrictFDerivAt.isThetaTVS_sub`：HasStrictFDerivAt.isThetaTVS_sub (hf :
 HasStrictFDerivAt f f' x) (hf' : Topology.IsInducing f') : (fun p : E × E => f 
p.1 - f p.2) =Θ[𝕜; 𝓝 (…
-/
theorem HasStrictFDerivAt.isTheta_sub (hf : HasStrictFDerivAt f f' x)
    (hf' : Topology.IsInducing f') :
    (fun p : E × E ↦ f p.1 - f p.2) =Θ[𝓝 (x, x)] (fun p ↦ p.1 - p.2) :=
  hf.isThetaTVS_sub hf' |>.isTheta
/-
**HasFDerivAtFilter.isTheta_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAtFilter.isTheta_sub (hf : HasFDerivAtFilter f f' L) (hf' : Topol
ogy.IsInducing f') : (fun p => f p.1 - f p.2) =Θ[L] (fun p => p.1 - p.2)
参数：hf : HasFDerivAtFilter f f' L；hf' : Topology.IsInducing f'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsThetaTVS.isTheta`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Typ
e u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : SeminormedA
ddCommGroup E] [inst…
· 使用定理 `HasFDerivAtFilter.isThetaTVS_sub`：HasFDerivAtFilter.isThetaTVS_sub (hf :
 HasFDerivAtFilter f f' L) (hf' : Topology.IsInducing f') : (fun p => f p.1 - f 
p.2) =Θ[𝕜; L] (fun p =…
-/
theorem HasFDerivAtFilter.isTheta_sub (hf : HasFDerivAtFilter f f' L)
    (hf' : Topology.IsInducing f') :
    (fun p ↦ f p.1 - f p.2) =Θ[L] (fun p ↦ p.1 - p.2) :=
  hf.isThetaTVS_sub hf' |>.isTheta
/-
**HasFDerivWithinAt.isTheta_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.isTheta_sub (hf : HasFDerivWithinAt f f' s x) (hf' : Top
ology.IsInducing f') : (f · - f x) =Θ[𝓝[s] x] (· - x)
参数：hf : HasFDerivWithinAt f f' s x；hf' : Topology.IsInducing f'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsThetaTVS.isTheta`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Typ
e u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : SeminormedA
ddCommGroup E] [inst…
· 使用定理 `HasFDerivWithinAt.isThetaTVS_sub`：HasFDerivWithinAt.isThetaTVS_sub (hf :
 HasFDerivWithinAt f f' s x) (hf' : Topology.IsInducing f') : (f · - f x) =Θ[𝕜; 
𝓝[s] x] (· - x)
-/
theorem HasFDerivWithinAt.isTheta_sub (hf : HasFDerivWithinAt f f' s x)
    (hf' : Topology.IsInducing f') :
    (f · - f x) =Θ[𝓝[s] x] (· - x) :=
  hf.isThetaTVS_sub hf' |>.isTheta
/-
**HasFDerivAt.isTheta_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.isTheta_sub (hf : HasFDerivAt f f' x) (hf' : Topology.IsInduci
ng f') : (f · - f x) =Θ[𝓝 x] (· - x)
参数：hf : HasFDerivAt f f' x；hf' : Topology.IsInducing f'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsThetaTVS.isTheta`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Typ
e u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : SeminormedA
ddCommGroup E] [inst…
· 使用定理 `HasFDerivAt.isThetaTVS_sub`：HasFDerivAt.isThetaTVS_sub (hf : HasFDerivAt
 f f' x) (hf' : Topology.IsInducing f') : (f · - f x) =Θ[𝕜; 𝓝 x] (· - x)
-/
theorem HasFDerivAt.isTheta_sub (hf : HasFDerivAt f f' x) (hf' : Topology.IsInducing f') :
    (f · - f x) =Θ[𝓝 x] (· - x) :=
  hf.isThetaTVS_sub hf' |>.isTheta

section Lipschitz
/-! ### Estimates on the norm of the derivative vs Lipschitz-like estimates on `f` -/

/-- If `f` is strictly differentiable at `x` with derivative `f'` and `K > ‖f'‖₊`, then `f` is
`K`-Lipschitz in a neighborhood of `x`. -/
/-
**HasStrictFDerivAt.exists_lipschitzOnWith_of_nnnorm_lt** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：HasStrictFDerivAt.exists_lipschitzOnWith_of_nnnorm_lt (hf : HasStrictFDeri
vAt f f' x) (K : Real>=0) (hK : ‖f'‖₊ < K) : exists s in 𝓝 x, LipschitzOnWith K 
f s
参数：hf : HasStrictFDerivAt f f' x；K : Real>=0；hK : ‖f'‖₊ < K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.add_isBigOWith`：∀ {α : Type u_1} {F : Type u_4} {E
' : Type u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {c₁ c₂ : ℝ}  
 {g : α → F} {l : Filter α…
· 使用定理 `HasStrictFDerivAt.isLittleO`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : SeminormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {F : Typ…
· 使用定理 `ContinuousLinearMap.isBigOWith_comp`：isBigOWith_comp [RingHomIsometric σ
₂₃] {α : Type*} (g : F ->SL[σ₂₃] G) (f : α -> F) (l : Filter α) : IsBigOWith ‖g‖
 l (fun x' => g (f x')) f
· 使用定理 `exists_nhds_square`：exists_nhds_square {s : Set (X × X)} {x : X} (hx : s
 in 𝓝 (x, x)) : exists U : Set X, IsOpen U ∧ x in U ∧ U ×ˢ U subseteq s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lipschitzOnWith_iff_norm_sub_le`：∀ {E : Type u_2} {F : Type u_3} [inst :
 SeminormedAddCommGroup E] [inst_1 : SeminormedAddCommGroup F] {f : E → F}   {C 
: NNReal} {s : Set E}…
· 使用定理 `Set.mk_mem_prod`：mk_mem_prod (ha : a in s) (hb : b in t) : (a, b) in s ×
ˢ t

--- 原说明 ---
If `f` is strictly differentiable at `x` with derivative `f'` and `K > ‖f'‖₊`, t
hen `f` is
`K`-Lipschitz in a neighborhood of `x`.
-/
theorem HasStrictFDerivAt.exists_lipschitzOnWith_of_nnnorm_lt (hf : HasStrictFDerivAt f f' x)
    (K : ℝ≥0) (hK : ‖f'‖₊ < K) : ∃ s ∈ 𝓝 x, LipschitzOnWith K f s := by
  have := hf.isLittleO.add_isBigOWith (f'.isBigOWith_comp _ _) hK
  simp only [sub_add_cancel, IsBigOWith] at this
  rcases exists_nhds_square this with ⟨U, Uo, xU, hU⟩
  exact
    ⟨U, Uo.mem_nhds xU, lipschitzOnWith_iff_norm_sub_le.2 fun x hx y hy => hU (mk_mem_prod hx hy)⟩

/-- If `f` is strictly differentiable at `x` with derivative `f'`, then `f` is Lipschitz in a
neighborhood of `x`. See also `HasStrictFDerivAt.exists_lipschitzOnWith_of_nnnorm_lt` for a
more precise statement. -/
/-
**HasStrictFDerivAt.exists_lipschitzOnWith** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.exists_lipschitzOnWith (hf : HasStrictFDerivAt f f' x) :
 exists K, exists s in 𝓝 x, LipschitzOnWith K f s
参数：hf : HasStrictFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `HasStrictFDerivAt.exists_lipschitzOnWith_of_nnnorm_lt`：HasStrictFDerivAt
.exists_lipschitzOnWith_of_nnnorm_lt (hf : HasStrictFDerivAt f f' x) (K : Real>=
0) (hK : ‖f'‖₊ < K) : exists s in 𝓝 x, Lips…
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `IsStrictOrderedRing.toNoMaxOrder`：∀ {R : Type u} [inst : Semiring R] [in
st_1 : PartialOrder R] [IsStrictOrderedRing R], NoMaxOrder R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal

--- 原说明 ---
If `f` is strictly differentiable at `x` with derivative `f'`, then `f` is Lipsc
hitz in a
neighborhood of `x`. See also `HasStrictFDerivAt.exists_lipschitzOnWith_of_nnnor
m_lt` for a
more precise statement.
-/
theorem HasStrictFDerivAt.exists_lipschitzOnWith (hf : HasStrictFDerivAt f f' x) :
    ∃ K, ∃ s ∈ 𝓝 x, LipschitzOnWith K f s :=
  (exists_gt _).imp hf.exists_lipschitzOnWith_of_nnnorm_lt

/-- Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-lipschitz
on a neighborhood of `x₀` then its derivative at `x₀` has norm bounded by `C`. This version
only assumes that `‖f x - f x₀‖ ≤ C * ‖x - x₀‖` in a neighborhood of `x`. -/
/-
**HasFDerivAt.le_of_lip'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.le_of_lip' {f : E -> F} {f' : E ->L[𝕜] F} {x₀ : E} (hf : HasFD
erivAt f f' x₀) {C : Real} (hC₀ : 0 <= C) (hlip : forallᶠ x in 𝓝 x₀, ‖f x - f x₀
‖ <= C * ‖x - x₀‖) : ‖f'‖ <= C
参数：hf : HasFDerivAt f f' x₀；hC₀ : 0 <= C；hlip : forallᶠ x in 𝓝 x₀, ‖f x - f x₀‖ 
<= C * ‖x - x₀‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_forall_pos_le_add`：∀ {α : Type u} [inst : LinearOrder α] [DenselyO
rdered α] [inst_2 : AddMonoid α] [ExistsAddOfLE α] [AddLeftReflectLT α]   {a b :
 α}, (∀ (ε : …
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
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ContinuousLinearMap.opNorm_le_of_nhds_zero`：opNorm_le_of_nhds_zero {f : 
E ->SL[σ₁₂] F} {C : Real} (hC : 0 <= C) (hf : forallᶠ x in 𝓝 (0 : E), ‖f x‖ <= C
 * ‖x‖) : ‖f‖ <= C
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_add_left_nhds_zero`：∀ {G : Type w} [inst : TopologicalSpace G] [inst
_1 : AddGroup G] [IsTopologicalAddGroup G] (x : G),   Filter.map (fun x_1 => x +
 x_1) (nhds …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.isLittleO_iff`：isLittleO_iff : f =o[l] g ↔ forall ⦃c : Real⦄
, 0 < c -> forallᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `hasFDerivAt_iff_isLittleO_nhds_zero`：hasFDerivAt_iff_isLittleO_nhds_zero
 : HasFDerivAt f f' x ↔ (fun h : E => f (x + h) - f x - f' h) =o[𝓝 0] fun h => h
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `norm_le_insert`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (u v : E)
, ‖v‖ ≤ ‖u‖ + ‖u - v‖
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R

--- 原说明 ---
Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-
lipschitz
on a neighborhood of `x₀` then its derivative at `x₀` has norm bounded by `C`. T
his version
only assumes that `‖f x - f x₀‖ ≤ C * ‖x - x₀‖` in a neighborhood of `x`.
-/
theorem HasFDerivAt.le_of_lip' {f : E → F} {f' : E →L[𝕜] F} {x₀ : E} (hf : HasFDerivAt f f' x₀)
    {C : ℝ} (hC₀ : 0 ≤ C) (hlip : ∀ᶠ x in 𝓝 x₀, ‖f x - f x₀‖ ≤ C * ‖x - x₀‖) : ‖f'‖ ≤ C := by
  refine le_of_forall_pos_le_add fun ε ε0 => opNorm_le_of_nhds_zero ?_ ?_
  · exact add_nonneg hC₀ ε0.le
  rw [← map_add_left_nhds_zero x₀, eventually_map] at hlip
  filter_upwards [isLittleO_iff.1 (hasFDerivAt_iff_isLittleO_nhds_zero.1 hf) ε0, hlip] with y hy hyC
  rw [add_sub_cancel_left] at hyC
  calc
    ‖f' y‖ ≤ ‖f (x₀ + y) - f x₀‖ + ‖f (x₀ + y) - f x₀ - f' y‖ := norm_le_insert _ _
    _ ≤ C * ‖y‖ + ε * ‖y‖ := add_le_add hyC hy
    _ = (C + ε) * ‖y‖ := (add_mul _ _ _).symm

/-- Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-lipschitz
on a neighborhood of `x₀` then its derivative at `x₀` has norm bounded by `C`. -/
/-
**HasFDerivAt.le_of_lipschitzOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.le_of_lipschitzOn {f : E -> F} {f' : E ->L[𝕜] F} {x₀ : E} (hf 
: HasFDerivAt f f' x₀) {s : Set E} (hs : s in 𝓝 x₀) {C : Real>=0} (hlip : Lipsch
itzOnWith C f s) : ‖f'‖ <= C
参数：hf : HasFDerivAt f f' x₀；hs : s in 𝓝 x₀；hlip : LipschitzOnWith C f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.le_of_lip'`：HasFDerivAt.le_of_lip' {f : E -> F} {f' : E ->L[
𝕜] F} {x₀ : E} (hf : HasFDerivAt f f' x₀) {C : Real} (hC₀ : 0 <= C) (hlip : fora
llᶠ x in 𝓝 x…
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LipschitzOnWith.norm_sub_le`：∀ {E : Type u_2} {F : Type u_3} [inst : Sem
inormedAddCommGroup E] [inst_1 : SeminormedAddCommGroup F] {f : E → F}   {C : NN
Real} {s : Set E}…
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s

--- 原说明 ---
Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-
lipschitz
on a neighborhood of `x₀` then its derivative at `x₀` has norm bounded by `C`.
-/
theorem HasFDerivAt.le_of_lipschitzOn
    {f : E → F} {f' : E →L[𝕜] F} {x₀ : E} (hf : HasFDerivAt f f' x₀)
    {s : Set E} (hs : s ∈ 𝓝 x₀) {C : ℝ≥0} (hlip : LipschitzOnWith C f s) : ‖f'‖ ≤ C := by
  refine hf.le_of_lip' C.coe_nonneg ?_
  filter_upwards [hs] with x hx using hlip.norm_sub_le hx (mem_of_mem_nhds hs)

/-- Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-lipschitz
then its derivative at `x₀` has norm bounded by `C`. -/
/-
**HasFDerivAt.le_of_lipschitz** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.le_of_lipschitz {f : E -> F} {f' : E ->L[𝕜] F} {x₀ : E} (hf : 
HasFDerivAt f f' x₀) {C : Real>=0} (hlip : LipschitzWith C f) : ‖f'‖ <= C
参数：hf : HasFDerivAt f f' x₀；hlip : LipschitzWith C f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.le_of_lipschitzOn`：HasFDerivAt.le_of_lipschitzOn {f : E -> F
} {f' : E ->L[𝕜] F} {x₀ : E} (hf : HasFDerivAt f f' x₀) {s : Set E} (hs : s in 𝓝
 x₀) {C : Real>=0} …
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lipschitzOnWith_univ`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricS
pace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   LipschitzOnW
ith K f Se…

--- 原说明 ---
Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-
lipschitz
then its derivative at `x₀` has norm bounded by `C`.
-/
theorem HasFDerivAt.le_of_lipschitz {f : E → F} {f' : E →L[𝕜] F} {x₀ : E} (hf : HasFDerivAt f f' x₀)
    {C : ℝ≥0} (hlip : LipschitzWith C f) : ‖f'‖ ≤ C :=
  hf.le_of_lipschitzOn univ_mem (lipschitzOnWith_univ.2 hlip)

variable (𝕜)

/-- Converse to the mean value inequality: if `f` is `C`-lipschitz
on a neighborhood of `x₀` then its derivative at `x₀` has norm bounded by `C`. This version
only assumes that `‖f x - f x₀‖ ≤ C * ‖x - x₀‖` in a neighborhood of `x`. -/
/-
**norm_fderiv_le_of_lip'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_fderiv_le_of_lip' {f : E -> F} {x₀ : E} {C : Real} (hC₀ : 0 <= C) (hl
ip : forallᶠ x in 𝓝 x₀, ‖f x - f x₀‖ <= C * ‖x - x₀‖) : ‖fderiv 𝕜 f x₀‖ <= C
参数：hC₀ : 0 <= C；hlip : forallᶠ x in 𝓝 x₀, ‖f x - f x₀‖ <= C * ‖x - x₀‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.le_of_lip'`：HasFDerivAt.le_of_lip' {f : E -> F} {f' : E ->L[
𝕜] F} {x₀ : E} (hf : HasFDerivAt f f' x₀) {C : Real} (hC₀ : 0 <= C) (hlip : fora
llᶠ x in 𝓝 x…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderiv_zero_of_not_differentiableAt`：fderiv_zero_of_not_differentiableAt
 (h : ¬DifferentiableAt 𝕜 f x) : fderiv 𝕜 f x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
Converse to the mean value inequality: if `f` is `C`-lipschitz
on a neighborhood of `x₀` then its derivative at `x₀` has norm bounded by `C`. T
his version
only assumes that `‖f x - f x₀‖ ≤ C * ‖x - x₀‖` in a neighborhood of `x`.
-/
theorem norm_fderiv_le_of_lip' {f : E → F} {x₀ : E}
    {C : ℝ} (hC₀ : 0 ≤ C) (hlip : ∀ᶠ x in 𝓝 x₀, ‖f x - f x₀‖ ≤ C * ‖x - x₀‖) :
    ‖fderiv 𝕜 f x₀‖ ≤ C := by
  by_cases hf : DifferentiableAt 𝕜 f x₀
  · exact hf.hasFDerivAt.le_of_lip' hC₀ hlip
  · rw [fderiv_zero_of_not_differentiableAt hf]
    simp [hC₀]

/-- Converse to the mean value inequality: if `f` is `C`-lipschitz
on a neighborhood of `x₀` then its derivative at `x₀` has norm bounded by `C`.
Version using `fderiv`. -/
/-
**norm_fderiv_le_of_lipschitzOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_fderiv_le_of_lipschitzOn {f : E -> F} {x₀ : E} {s : Set E} (hs : s in
 𝓝 x₀) {C : Real>=0} (hlip : LipschitzOnWith C f s) : ‖fderiv 𝕜 f x₀‖ <= C
参数：hs : s in 𝓝 x₀；hlip : LipschitzOnWith C f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_fderiv_le_of_lip'`：norm_fderiv_le_of_lip' {f : E -> F} {x₀ : E} {C 
: Real} (hC₀ : 0 <= C) (hlip : forallᶠ x in 𝓝 x₀, ‖f x - f x₀‖ <= C * ‖x - x₀‖) 
: ‖fderiv 𝕜 …
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LipschitzOnWith.norm_sub_le`：∀ {E : Type u_2} {F : Type u_3} [inst : Sem
inormedAddCommGroup E] [inst_1 : SeminormedAddCommGroup F] {f : E → F}   {C : NN
Real} {s : Set E}…
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s

--- 原说明 ---
Converse to the mean value inequality: if `f` is `C`-lipschitz
on a neighborhood of `x₀` then its derivative at `x₀` has norm bounded by `C`.
Version using `fderiv`.
-/
theorem norm_fderiv_le_of_lipschitzOn {f : E → F} {x₀ : E} {s : Set E} (hs : s ∈ 𝓝 x₀)
    {C : ℝ≥0} (hlip : LipschitzOnWith C f s) : ‖fderiv 𝕜 f x₀‖ ≤ C := by
  refine norm_fderiv_le_of_lip' 𝕜 C.coe_nonneg ?_
  filter_upwards [hs] with x hx using hlip.norm_sub_le hx (mem_of_mem_nhds hs)

/-- Converse to the mean value inequality: if `f` is `C`-lipschitz then
its derivative at `x₀` has norm bounded by `C`.
Version using `fderiv`. -/
/-
**norm_fderiv_le_of_lipschitz** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_fderiv_le_of_lipschitz {f : E -> F} {x₀ : E} {C : Real>=0} (hlip : Li
pschitzWith C f) : ‖fderiv 𝕜 f x₀‖ <= C
参数：hlip : LipschitzWith C f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_fderiv_le_of_lipschitzOn`：norm_fderiv_le_of_lipschitzOn {f : E -> F
} {x₀ : E} {s : Set E} (hs : s in 𝓝 x₀) {C : Real>=0} (hlip : LipschitzOnWith C 
f s) : ‖fderiv 𝕜 f …
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lipschitzOnWith_univ`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricS
pace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   LipschitzOnW
ith K f Se…

--- 原说明 ---
Converse to the mean value inequality: if `f` is `C`-lipschitz then
its derivative at `x₀` has norm bounded by `C`.
Version using `fderiv`.
-/
theorem norm_fderiv_le_of_lipschitz {f : E → F} {x₀ : E}
    {C : ℝ≥0} (hlip : LipschitzWith C f) : ‖fderiv 𝕜 f x₀‖ ≤ C :=
  norm_fderiv_le_of_lipschitzOn 𝕜 univ_mem (lipschitzOnWith_univ.2 hlip)

end Lipschitz

end not_TVS

section Semilinear
/-!
## Results involving semilinear maps
-/
variable {𝕜 V V' W W' : Type*} [NontriviallyNormedField 𝕜] {σ σ' : RingHom 𝕜 𝕜}
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup V'] [NormedSpace 𝕜 V']
  [NormedAddCommGroup W] [NormedSpace 𝕜 W] [NormedAddCommGroup W'] [NormedSpace 𝕜 W']
  [RingHomIsometric σ] [RingHomInvPair σ σ'] (L : W →SL[σ] W') (R : V' →SL[σ'] V)

/-- If `L` and `R` are semilinear maps whose composite is linear, and `f` has Fréchet derivative
`f'` at `R z`, then `L ∘ f ∘ R` has Fréchet derivative `L ∘ f' ∘ R` at `z`. -/
/-
**HasFDerivAt.comp_semilinear** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasFDerivAt.comp_semilinear {f : V -> W} {z : V'} {f' : V ->L[𝕜] W} (hf : 
HasFDerivAt f f' (R z)) : HasFDerivAt (L ∘ f ∘ R) (L.comp (f'.comp R)) z
参数：hf : HasFDerivAt f f' (R z)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHomIsometric.inv`：RingHomIsometric.inv {𝕜₁ 𝕜₂ : Type*} [SeminormedRi
ng 𝕜₁] [SeminormedRing 𝕜₂] (σ : 𝕜₁ ->+* 𝕜₂) {σ' : 𝕜₂ ->+* 𝕜₁} [RingHomInvPair σ 
σ'] [RingH…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasFDerivAt_iff_isLittleO_nhds_zero`：hasFDerivAt_iff_isLittleO_nhds_zero
 : HasFDerivAt f f' x ↔ (fun h : E => f (x + h) - f x - f' h) =o[𝓝 0] fun h => h
· 使用定理 `Asymptotics.IsLittleO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E :
 Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α →
 F}   {l : Filter α}, f …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `ContinuousLinearMap.map_zero`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : 
Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 
: TopologicalSpace…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Asymptotics.IsLittleO.trans_isBigO`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} {G' : Type u_8} [inst : Norm E] [inst_1 : Norm F]   [inst_2 : Seminor
medAddCommGroup G'] {l :…
· 使用定理 `Asymptotics.IsBigO.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} {G :
 Type u_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : Seminor
medAddCommGroup F'] {l :…
· 使用定理 `ContinuousLinearMap.isBigO_comp`：isBigO_comp [RingHomIsometric σ₂₃] {α :
 Type*} (g : F ->SL[σ₂₃] G) (f : α -> F) (l : Filter α) : (fun x' => g (f x')) =
O[l] f
· 使用定理 `ContinuousLinearMap.isBigO_id`：isBigO_id : f =O[l] fun x => x

--- 原说明 ---
If `L` and `R` are semilinear maps whose composite is linear, and `f` has Fréche
t derivative
`f'` at `R z`, then `L ∘ f ∘ R` has Fréchet derivative `L ∘ f' ∘ R` at `z`.
-/
lemma HasFDerivAt.comp_semilinear {f : V → W} {z : V'} {f' : V →L[𝕜] W}
    (hf : HasFDerivAt f f' (R z)) : HasFDerivAt (L ∘ f ∘ R) (L.comp (f'.comp R)) z := by
  have : RingHomIsometric σ' := .inv σ
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at ⊢ hf
  have := hf.comp_tendsto (R.map_zero ▸ R.continuous.continuousAt.tendsto)
  simpa using ((L.isBigO_comp _ _).trans_isLittleO this).trans_isBigO (R.isBigO_id _)

/-- If `L` and `R` are semilinear maps whose composite is linear, and `f` is differentiable at
`R z`, then `L ∘ f ∘ R` is differentiable at `z`. -/
/-
**DifferentiableAt.comp_semilinear** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `L` and `R` are semilinear maps whose composite is linear, and `f` is differe
ntiable at
`R z`, then `L ∘ f ∘ R` is differentiable at `z`.
-/
lemma DifferentiableAt.comp_semilinear₂ {f : V → W} {z : V'} (hf : DifferentiableAt 𝕜 f (R z)) :
    DifferentiableAt 𝕜 (L ∘ f ∘ R) z := by
  simpa using (hf.hasFDerivAt.comp_semilinear L R).differentiableAt

end Semilinear

