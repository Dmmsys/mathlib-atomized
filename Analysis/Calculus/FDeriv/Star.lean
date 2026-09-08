/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Topology.Algebra.Module.Star

/-!
# Star operations on derivatives

This file contains the usual formulas (and existence assertions) for the Fréchet derivative of the
star operation. For detailed documentation of the Fréchet derivative, see the module docstring of
`Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

Most of the results in this file only apply when the field that the derivative is respect to has a
trivial star operation; which as should be expected rules out `𝕜 = ℂ`. The exceptions are
`HasFDerivAt.star_star` and `DifferentiableAt.star_star`, showing that `star ∘ f ∘ star` is
differentiable when `f` is (and giving a formula for its derivative).
-/

public section


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [StarRing 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [StarAddMonoid F] [NormedSpace 𝕜 F] [StarModule 𝕜 F]
  [ContinuousStar F]

variable {f : E → F} {f' : E →L[𝕜] F} {x : E} {s : Set E} {L : Filter (E × E)}

section TrivialStar

variable [TrivialStar 𝕜]

/-
**HasFDerivAtFilter.star** 是 Mathlib 中的一个定理，位于命名空间 `HasFDerivAtFilter`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] [inst_1 : StarRing 𝕜] 
{E : Type u_2} [inst_2 : NormedAddCommGroup E]   [inst_3 : NormedSpace 𝕜 E] {F :
 Type u_3} [inst_4 : NormedAddCommGroup F] [inst_5 : StarAddMonoid F]   [inst_6 
: NormedSpace 𝕜 F] [inst_7 : StarModule 𝕜 F] [inst_8 : ContinuousStar F] {f : E 
→ F} {f' : E →L[𝕜] F}   {L : Filter (E × E)} [inst_9 : TrivialStar 𝕜],   HasFDer
ivAtFilter f f' L → HasFDerivAtFilter (fun x => star (f x)) (↑(starL' 𝕜) ∘SL f')
 L
参数：E × E；fun x => star (f x)；↑(starL' 𝕜) ∘SL f'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.comp`：HasFDerivAtFilter.comp {g : F -> G} {g' : F ->L[
𝕜] G} {L' : Filter (F × F)} (hg : HasFDerivAtFilter g g' L') (hf : HasFDerivAtFi
lter f f' L)…
· 使用定理 `ContinuousLinearMap.hasFDerivAtFilter`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.M
odule 𝕜 E] [inst_3 : Topolo…
· 使用定理 `Filter.tendsto_map`：tendsto_map {f : α -> β} {x : Filter α} : Tendsto f 
x (map f x)
-/
protected theorem HasFDerivAtFilter.star (h : HasFDerivAtFilter f f' L) :
    HasFDerivAtFilter (fun x => star (f x)) (((starL' 𝕜 : F ≃L[𝕜] F) : F →L[𝕜] F) ∘L f') L :=
  (starL' 𝕜 : F ≃L[𝕜] F).toContinuousLinearMap.hasFDerivAtFilter.comp h Filter.tendsto_map

@[fun_prop]
/-
**HasStrictFDerivAt.star** 是 Mathlib 中的一个定理，位于命名空间 `HasStrictFDerivAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] [inst_1 : StarRing 𝕜] 
{E : Type u_2} [inst_2 : NormedAddCommGroup E]   [inst_3 : NormedSpace 𝕜 E] {F :
 Type u_3} [inst_4 : NormedAddCommGroup F] [inst_5 : StarAddMonoid F]   [inst_6 
: NormedSpace 𝕜 F] [inst_7 : StarModule 𝕜 F] [inst_8 : ContinuousStar F] {f : E 
→ F} {f' : E →L[𝕜] F} {x : E}   [inst_9 : TrivialStar 𝕜], HasStrictFDerivAt f f'
 x → HasStrictFDerivAt (fun x => star (f x)) (↑(starL' 𝕜) ∘SL f') x
参数：fun x => star (f x)；↑(starL' 𝕜) ∘SL f'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.star`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] [inst_1 : StarRing 𝕜] {E : Type u_2} [inst_2 : NormedAddCommGroup E]   [inst
_3 : NormedS…
-/
protected theorem HasStrictFDerivAt.star (h : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => star (f x)) (((starL' 𝕜 : F ≃L[𝕜] F) : F →L[𝕜] F) ∘L f') x :=
  HasFDerivAtFilter.star h

@[fun_prop]
/-
**HasFDerivWithinAt.star** 是 Mathlib 中的一个定理，位于命名空间 `HasFDerivWithinAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] [inst_1 : StarRing 𝕜] 
{E : Type u_2} [inst_2 : NormedAddCommGroup E]   [inst_3 : NormedSpace 𝕜 E] {F :
 Type u_3} [inst_4 : NormedAddCommGroup F] [inst_5 : StarAddMonoid F]   [inst_6 
: NormedSpace 𝕜 F] [inst_7 : StarModule 𝕜 F] [inst_8 : ContinuousStar F] {f : E 
→ F} {f' : E →L[𝕜] F} {x : E}   {s : Set E} [inst_9 : TrivialStar 𝕜],   HasFDeri
vWithinAt f f' s x → HasFDerivWithinAt (fun x => star (f x)) (↑(starL' 𝕜) ∘SL f'
) s x
参数：fun x => star (f x)；↑(starL' 𝕜) ∘SL f'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.star`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] [inst_1 : StarRing 𝕜] {E : Type u_2} [inst_2 : NormedAddCommGroup E]   [inst
_3 : NormedS…
-/
protected theorem HasFDerivWithinAt.star (h : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => star (f x)) (((starL' 𝕜 : F ≃L[𝕜] F) : F →L[𝕜] F) ∘L f') s x :=
  HasFDerivAtFilter.star h

@[fun_prop]
/-
**HasFDerivAt.star** 是 Mathlib 中的一个定理，位于命名空间 `HasFDerivAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] [inst_1 : StarRing 𝕜] 
{E : Type u_2} [inst_2 : NormedAddCommGroup E]   [inst_3 : NormedSpace 𝕜 E] {F :
 Type u_3} [inst_4 : NormedAddCommGroup F] [inst_5 : StarAddMonoid F]   [inst_6 
: NormedSpace 𝕜 F] [inst_7 : StarModule 𝕜 F] [inst_8 : ContinuousStar F] {f : E 
→ F} {f' : E →L[𝕜] F} {x : E}   [inst_9 : TrivialStar 𝕜], HasFDerivAt f f' x → H
asFDerivAt (fun x => star (f x)) (↑(starL' 𝕜) ∘SL f') x
参数：fun x => star (f x)；↑(starL' 𝕜) ∘SL f'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.star`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] [inst_1 : StarRing 𝕜] {E : Type u_2} [inst_2 : NormedAddCommGroup E]   [inst
_3 : NormedS…
-/
protected theorem HasFDerivAt.star (h : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => star (f x)) (((starL' 𝕜 : F ≃L[𝕜] F) : F →L[𝕜] F) ∘L f') x :=
  HasFDerivAtFilter.star h

@[fun_prop]
/-
**DifferentiableWithinAt.star** 是 Mathlib 中的一个定理，位于命名空间 `DifferentiableWithinAt`
。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] [inst_1 : StarRing 𝕜] 
{E : Type u_2} [inst_2 : NormedAddCommGroup E]   [inst_3 : NormedSpace 𝕜 E] {F :
 Type u_3} [inst_4 : NormedAddCommGroup F] [inst_5 : StarAddMonoid F]   [inst_6 
: NormedSpace 𝕜 F] [StarModule 𝕜 F] [ContinuousStar F] {f : E → F} {x : E} {s : 
Set E} [TrivialStar 𝕜],   DifferentiableWithinAt 𝕜 f s x → DifferentiableWithinA
t 𝕜 (fun y => star (f y)) s x
参数：fun y => star (f y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasFDerivWithinAt.star`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] [inst_1 : StarRing 𝕜] {E : Type u_2} [inst_2 : NormedAddCommGroup E]   [inst
_3 : NormedS…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
protected theorem DifferentiableWithinAt.star (h : DifferentiableWithinAt 𝕜 f s x) :
    DifferentiableWithinAt 𝕜 (fun y => star (f y)) s x :=
  h.hasFDerivWithinAt.star.differentiableWithinAt

@[simp]
/-
**differentiableWithinAt_star_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_star_iff : DifferentiableWithinAt 𝕜 (fun y => star 
(f y)) s x ↔ DifferentiableWithinAt 𝕜 f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.comp_differentiableWithinAt_iff`：comp_differentiab
leWithinAt_iff {f : G -> E} {s : Set G} {x : G} : DifferentiableWithinAt 𝕜 (iso 
∘ f) s x ↔ DifferentiableWithinAt 𝕜 f s x
-/
theorem differentiableWithinAt_star_iff :
    DifferentiableWithinAt 𝕜 (fun y => star (f y)) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  (starL' 𝕜 : F ≃L[𝕜] F).comp_differentiableWithinAt_iff

@[fun_prop]
/-
**DifferentiableAt.star** 是 Mathlib 中的一个定理，位于命名空间 `DifferentiableAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] [inst_1 : StarRing 𝕜] 
{E : Type u_2} [inst_2 : NormedAddCommGroup E]   [inst_3 : NormedSpace 𝕜 E] {F :
 Type u_3} [inst_4 : NormedAddCommGroup F] [inst_5 : StarAddMonoid F]   [inst_6 
: NormedSpace 𝕜 F] [StarModule 𝕜 F] [ContinuousStar F] {f : E → F} {x : E} [Triv
ialStar 𝕜],   DifferentiableAt 𝕜 f x → DifferentiableAt 𝕜 (fun y => star (f y)) 
x
参数：fun y => star (f y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `HasFDerivAt.star`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] [i
nst_1 : StarRing 𝕜] {E : Type u_2} [inst_2 : NormedAddCommGroup E]   [inst_3 : N
ormedS…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
protected theorem DifferentiableAt.star (h : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (fun y => star (f y)) x :=
  h.hasFDerivAt.star.differentiableAt

@[simp]
/-
**differentiableAt_star_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_star_iff : DifferentiableAt 𝕜 (fun y => star (f y)) x ↔ D
ifferentiableAt 𝕜 f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.comp_differentiableAt_iff`：comp_differentiableAt_i
ff {f : G -> E} {x : G} : DifferentiableAt 𝕜 (iso ∘ f) x ↔ DifferentiableAt 𝕜 f 
x
-/
theorem differentiableAt_star_iff :
    DifferentiableAt 𝕜 (fun y => star (f y)) x ↔ DifferentiableAt 𝕜 f x :=
  (starL' 𝕜 : F ≃L[𝕜] F).comp_differentiableAt_iff

@[fun_prop]
/-
**DifferentiableOn.star** 是 Mathlib 中的一个定理，位于命名空间 `DifferentiableOn`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] [inst_1 : StarRing 𝕜] 
{E : Type u_2} [inst_2 : NormedAddCommGroup E]   [inst_3 : NormedSpace 𝕜 E] {F :
 Type u_3} [inst_4 : NormedAddCommGroup F] [inst_5 : StarAddMonoid F]   [inst_6 
: NormedSpace 𝕜 F] [StarModule 𝕜 F] [ContinuousStar F] {f : E → F} {s : Set E} [
TrivialStar 𝕜],   DifferentiableOn 𝕜 f s → DifferentiableOn 𝕜 (fun y => star (f 
y)) s
参数：fun y => star (f y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.star`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] [inst_1 : StarRing 𝕜] {E : Type u_2} [inst_2 : NormedAddCommGroup E]   
[inst_3 : NormedS…
-/
protected theorem DifferentiableOn.star (h : DifferentiableOn 𝕜 f s) :
    DifferentiableOn 𝕜 (fun y => star (f y)) s := fun x hx => (h x hx).star

@[simp]
/-
**differentiableOn_star_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_star_iff : DifferentiableOn 𝕜 (fun y => star (f y)) s ↔ D
ifferentiableOn 𝕜 f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.comp_differentiableOn_iff`：comp_differentiableOn_i
ff {f : G -> E} {s : Set G} : DifferentiableOn 𝕜 (iso ∘ f) s ↔ DifferentiableOn 
𝕜 f s
-/
theorem differentiableOn_star_iff :
    DifferentiableOn 𝕜 (fun y => star (f y)) s ↔ DifferentiableOn 𝕜 f s :=
  (starL' 𝕜 : F ≃L[𝕜] F).comp_differentiableOn_iff

@[fun_prop]
/-
**Differentiable.star** 是 Mathlib 中的一个定理，位于命名空间 `Differentiable`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] [inst_1 : StarRing 𝕜] 
{E : Type u_2} [inst_2 : NormedAddCommGroup E]   [inst_3 : NormedSpace 𝕜 E] {F :
 Type u_3} [inst_4 : NormedAddCommGroup F] [inst_5 : StarAddMonoid F]   [inst_6 
: NormedSpace 𝕜 F] [StarModule 𝕜 F] [ContinuousStar F] {f : E → F} [TrivialStar 
𝕜],   Differentiable 𝕜 f → Differentiable 𝕜 fun y => star (f y)
参数：f y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.star`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] [inst_1 : StarRing 𝕜] {E : Type u_2} [inst_2 : NormedAddCommGroup E]   [inst_
3 : NormedS…
-/
protected theorem Differentiable.star (h : Differentiable 𝕜 f) :
    Differentiable 𝕜 fun y => star (f y) :=
  fun x => (h x).star

@[simp]
/-
**differentiable_star_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiable_star_iff : (Differentiable 𝕜 fun y => star (f y)) ↔ Differe
ntiable 𝕜 f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.comp_differentiable_iff`：comp_differentiable_iff {
f : G -> E} : Differentiable 𝕜 (iso ∘ f) ↔ Differentiable 𝕜 f
-/
theorem differentiable_star_iff : (Differentiable 𝕜 fun y => star (f y)) ↔ Differentiable 𝕜 f :=
  (starL' 𝕜 : F ≃L[𝕜] F).comp_differentiable_iff
/-
**fderivWithin_star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_star (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 (fun y
 => star (f y)) s x = ((starL' 𝕜 : F ≃L[𝕜] F) : F ->L[𝕜] F) ∘L fderivWithin 𝕜 f 
s x
参数：hxs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.comp_fderivWithin`：comp_fderivWithin {f : G -> E} 
{s : Set G} {x : G} (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 (iso ∘ f) 
s x = (iso : E ->L[𝕜] F).comp…
-/
theorem fderivWithin_star (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun y => star (f y)) s x =
      ((starL' 𝕜 : F ≃L[𝕜] F) : F →L[𝕜] F) ∘L fderivWithin 𝕜 f s x :=
  (starL' 𝕜 : F ≃L[𝕜] F).comp_fderivWithin hxs

@[simp]
/-
**fderiv_star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_star : fderiv 𝕜 (fun y => star (f y)) x = ((starL' 𝕜 : F ≃L[𝕜] F) :
 F ->L[𝕜] F) ∘L fderiv 𝕜 f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.comp_fderiv`：comp_fderiv {f : G -> E} {x : G} : fd
eriv 𝕜 (iso ∘ f) x = (iso : E ->L[𝕜] F).comp (fderiv 𝕜 f x)
-/
theorem fderiv_star :
    fderiv 𝕜 (fun y => star (f y)) x = ((starL' 𝕜 : F ≃L[𝕜] F) : F →L[𝕜] F) ∘L fderiv 𝕜 f x :=
  (starL' 𝕜 : F ≃L[𝕜] F).comp_fderiv

end TrivialStar

section NontrivialStar

/-!
## Composing on the left and right with `star`
-/

variable [StarAddMonoid E] [StarModule 𝕜 E] [ContinuousStar E] [NormedStarGroup 𝕜]

/-- If `f` has derivative `f'` at `z`, then `star ∘ f ∘ star` has derivative `starL ∘ f' ∘ starL`
at `star z`. -/
@[fun_prop]
/-
**HasFDerivAt.star_star** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasFDerivAt.star_star {f : E -> F} {z : E} {f' : E ->L[𝕜] F} (hf : HasFDer
ivAt f f' z) : HasFDerivAt (star ∘ f ∘ star) ((starL 𝕜).toContinuousLinearMap.co
mp <| f'.comp (starL 𝕜).toContinuousLinearMap) (star z)
参数：hf : HasFDerivAt f f' z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasFDerivAt.comp_semilinear`：HasFDerivAt.comp_semilinear {f : V -> W} {z
 : V'} {f' : V ->L[𝕜] W} (hf : HasFDerivAt f f' (R z)) : HasFDerivAt (L ∘ f ∘ R)
 (L.comp (f'.comp…
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `starL_apply`：∀ (R : Type u_1) {A : Type u_2} [inst : CommSemiring R] [in
st_1 : StarRing R] [inst_2 : AddCommMonoid A]   [inst_3 : StarAddMonoid A] [inst
_…
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r

--- 原说明 ---
If `f` has derivative `f'` at `z`, then `star ∘ f ∘ star` has derivative `starL 
∘ f' ∘ starL`
at `star z`.
-/
lemma HasFDerivAt.star_star {f : E → F} {z : E} {f' : E →L[𝕜] F} (hf : HasFDerivAt f f' z) :
    HasFDerivAt (star ∘ f ∘ star)
      ((starL 𝕜).toContinuousLinearMap.comp <| f'.comp (starL 𝕜).toContinuousLinearMap) (star z) :=
  .comp_semilinear (starL 𝕜).toContinuousLinearMap (starL 𝕜).toContinuousLinearMap
    (by simpa using hf)

/-- If `f` is differentiable at `z`, then `star ∘ f ∘ star` is differentiable at `star z`. -/
@[fun_prop]
/-
**DifferentiableAt.star_star** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DifferentiableAt.star_star {f : E -> F} {z : E} (hf : DifferentiableAt 𝕜 f
 z) : DifferentiableAt 𝕜 (star ∘ f ∘ star) (star z)
参数：hf : DifferentiableAt 𝕜 f z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用引理 `HasFDerivAt.star_star`：HasFDerivAt.star_star {f : E -> F} {z : E} {f' : 
E ->L[𝕜] F} (hf : HasFDerivAt f f' z) : HasFDerivAt (star ∘ f ∘ star) ((starL 𝕜)
.toContinuo…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x

--- 原说明 ---
If `f` is differentiable at `z`, then `star ∘ f ∘ star` is differentiable at `st
ar z`.
-/
lemma DifferentiableAt.star_star {f : E → F} {z : E} (hf : DifferentiableAt 𝕜 f z) :
    DifferentiableAt 𝕜 (star ∘ f ∘ star) (star z) :=
  hf.hasFDerivAt.star_star.differentiableAt

end NontrivialStar

