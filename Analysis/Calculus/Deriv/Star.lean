/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Star

/-!
# Star operations on derivatives

This file contains the usual formulas (and existence assertions) for the derivative of the star
operation.

Most of the results in this file only apply when the field that the derivative is respect to has a
trivial star operation; which as should be expected rules out `𝕜 = ℂ`. The exceptions are
`HasDerivAt.conj_conj` and `DifferentiableAt.conj_conj`, showing that `conj ∘ f ∘ conj` is
differentiable when `f` is (and giving a formula for its derivative).
-/

public section

universe u v w

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [StarRing 𝕜]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [StarAddMonoid F] [StarModule 𝕜 F]
  [ContinuousStar F] {f : 𝕜 → F} {f' : F} {x : 𝕜}

/-! ### Derivative of `x ↦ star x` -/

section TrivialStar

variable [TrivialStar 𝕜] {s : Set 𝕜} {L : Filter (𝕜 × 𝕜)}

set_option backward.isDefEq.respectTransparency.types false in
/-
**HasDerivAtFilter.star** 是 Mathlib 中的一个定理，位于命名空间 `HasDerivAtFilter`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] [inst_1 : StarRing 𝕜] {F
 : Type v} [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace 𝕜 F] [inst_4 
: StarAddMonoid F] [StarModule 𝕜 F] [ContinuousStar F] {f : 𝕜 → F} {f' : F}   [T
rivialStar 𝕜] {L : Filter (𝕜 × 𝕜)}, HasDerivAtFilter f f' L → HasDerivAtFilter (
fun x => star (f x)) (star f') L
参数：𝕜 × 𝕜；fun x => star (f x)；star f'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `starL'_apply`：∀ (R : Type u_1) {A : Type u_2} [inst : CommSemiring R] [i
nst_1 : StarRing R] [inst_2 : AddCommMonoid A]   [inst_3 : StarAddMonoid A] [ins
t_…
· 使用定理 `HasFDerivAtFilter.hasDerivAtFilter`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `HasFDerivAtFilter.star`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] [inst_1 : StarRing 𝕜] {E : Type u_2} [inst_2 : NormedAddCommGroup E]   [inst
_3 : NormedS…
· 使用定理 `HasDerivAtFilter.hasFDerivAtFilter`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
-/
protected theorem HasDerivAtFilter.star (h : HasDerivAtFilter f f' L) :
    HasDerivAtFilter (fun x => star (f x)) (star f') L := by
  simpa using h.hasFDerivAtFilter.star.hasDerivAtFilter
/-
**HasDerivWithinAt.star** 是 Mathlib 中的一个定理，位于命名空间 `HasDerivWithinAt`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] [inst_1 : StarRing 𝕜] {F
 : Type v} [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace 𝕜 F] [inst_4 
: StarAddMonoid F] [StarModule 𝕜 F] [ContinuousStar F] {f : 𝕜 → F} {f' : F} {x :
 𝕜}   [TrivialStar 𝕜] {s : Set 𝕜}, HasDerivWithinAt f f' s x → HasDerivWithinAt 
(fun x => star (f x)) (star f') s x
参数：fun x => star (f x)；star f'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.star`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 [inst_1 : StarRing 𝕜] {F : Type v} [inst_2 : NormedAddCommGroup F]   [inst_3 : 
NormedSpace…
-/
protected theorem HasDerivWithinAt.star (h : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => star (f x)) (star f') s x :=
  HasDerivAtFilter.star h
/-
**HasDerivAt.star** 是 Mathlib 中的一个定理，位于命名空间 `HasDerivAt`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] [inst_1 : StarRing 𝕜] {F
 : Type v} [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace 𝕜 F] [inst_4 
: StarAddMonoid F] [StarModule 𝕜 F] [ContinuousStar F] {f : 𝕜 → F} {f' : F} {x :
 𝕜}   [TrivialStar 𝕜], HasDerivAt f f' x → HasDerivAt (fun x => star (f x)) (sta
r f') x
参数：fun x => star (f x)；star f'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.star`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 [inst_1 : StarRing 𝕜] {F : Type v} [inst_2 : NormedAddCommGroup F]   [inst_3 : 
NormedSpace…
-/
protected theorem HasDerivAt.star (h : HasDerivAt f f' x) :
    HasDerivAt (fun x => star (f x)) (star f') x :=
  HasDerivAtFilter.star h

protected nonrec theorem HasStrictDerivAt.star (h : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => star (f x)) (star f') x :=
  HasDerivAtFilter.star h
/-
**derivWithin.star** 是 Mathlib 中的一个定理，位于命名空间 `derivWithin`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] [inst_1 : StarRing 𝕜] {F
 : Type v} [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace 𝕜 F] [inst_4 
: StarAddMonoid F] [StarModule 𝕜 F] [ContinuousStar F] {f : 𝕜 → F} {x : 𝕜}   [Tr
ivialStar 𝕜] {s : Set 𝕜}, derivWithin (fun y => star (f y)) s x = star (derivWit
hin f s x)
参数：fun y => star (f y)；derivWithin f s x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `fderivWithin_star`：fderivWithin_star (hxs : UniqueDiffWithinAt 𝕜 s x) : 
fderivWithin 𝕜 (fun y => star (f y)) s x = ((starL' 𝕜 : F ≃L[𝕜] F) : F ->L[𝕜] F)
 ∘L fde…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `derivWithin_zero_of_not_uniqueDiffWithinAt`：derivWithin_zero_of_not_uniq
ueDiffWithinAt (h : ¬UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = 0
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem derivWithin.star :
    derivWithin (fun y => star (f y)) s x = star (derivWithin f s x) := by
  by_cases hxs : UniqueDiffWithinAt 𝕜 s x
  · exact DFunLike.congr_fun (fderivWithin_star hxs) _
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hxs]
/-
**deriv.star** 是 Mathlib 中的一个定理，位于命名空间 `deriv`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] [inst_1 : StarRing 𝕜] {F
 : Type v} [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace 𝕜 F] [inst_4 
: StarAddMonoid F] [StarModule 𝕜 F] [ContinuousStar F] {f : 𝕜 → F} {x : 𝕜}   [Tr
ivialStar 𝕜], deriv (fun y => star (f y)) x = star (deriv f x)
参数：fun y => star (f y)；deriv f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `fderiv_star`：fderiv_star : fderiv 𝕜 (fun y => star (f y)) x = ((starL' 𝕜
 : F ≃L[𝕜] F) : F ->L[𝕜] F) ∘L fderiv 𝕜 f x
-/
protected theorem deriv.star : deriv (fun y => star (f y)) x = star (deriv f x) :=
  DFunLike.congr_fun fderiv_star _

@[simp]
/-
**deriv.star'** 是 Mathlib 中的一个定理，位于命名空间 `deriv`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] [inst_1 : StarRing 𝕜] {F
 : Type v} [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace 𝕜 F] [inst_4 
: StarAddMonoid F] [StarModule 𝕜 F] [ContinuousStar F] {f : 𝕜 → F} [TrivialStar 
𝕜],   (deriv fun y => star (f y)) = fun x => star (deriv f x)
参数：deriv fun y => star (f y)；deriv f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `deriv.star`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] [inst_1 : 
StarRing 𝕜] {F : Type v} [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace
…
-/
protected theorem deriv.star' : (deriv fun y => star (f y)) = fun x => star (deriv f x) :=
  funext fun _ => deriv.star

end TrivialStar

section NontrivialStar

variable [NormedStarGroup 𝕜]

open scoped ComplexConjugate

/-- If `f` has derivative `f'` at `z`, then `star ∘ f ∘ conj` has derivative `star f'` at
`conj z`. -/
/-
**HasDerivAt.star_conj** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasDerivAt.star_conj {f : 𝕜 -> F} {f' : F} (hf : HasDerivAt f f' x) : HasD
erivAt (star ∘ f ∘ conj) (star f') (conj x)
参数：hf : HasDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasDerivAt_iff_hasFDerivAt`：hasDerivAt_iff_hasFDerivAt {f' : F} : HasDer
ivAt f f' x ↔ HasFDerivAt f (toSpanSingleton 𝕜 f') x
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E
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
· 使用定理 `starL_apply`：∀ (R : Type u_1) {A : Type u_2} [inst : CommSemiring R] [in
st_1 : StarRing R] [inst_2 : AddCommMonoid A]   [inst_3 : StarAddMonoid A] [inst
_…
· 使用定理 `star_one`：star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `HasFDerivAt.star_star`：HasFDerivAt.star_star {f : E -> F} {z : E} {f' : 
E ->L[𝕜] F} (hf : HasFDerivAt f f' z) : HasFDerivAt (star ∘ f ∘ star) ((starL 𝕜)
.toContinuo…
· 使用定理 `HasDerivAt.hasFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…

--- 原说明 ---
If `f` has derivative `f'` at `z`, then `star ∘ f ∘ conj` has derivative `star f
'` at
`conj z`.
-/
lemma HasDerivAt.star_conj {f : 𝕜 → F} {f' : F} (hf : HasDerivAt f f' x) :
    HasDerivAt (star ∘ f ∘ conj) (star f') (conj x) := by
  rw [hasDerivAt_iff_hasFDerivAt]
  convert! hf.hasFDerivAt.star_star
  ext
  simp

/-- A function `f` has derivative `f'` at `z` iff `star ∘ f ∘ conj` has derivative `star f'` at
`conj z`. -/
@[simp]
/-
**hasDerivAt_star_conj_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasDerivAt_star_conj_iff {f : 𝕜 -> F} {x : 𝕜} {f' : F} : HasDerivAt (star 
∘ f ∘ conj) f' x ↔ HasDerivAt f (star f') (conj x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `RingHomCompTriple.comp_apply`：comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
 {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `HasDerivAt.star_conj`：HasDerivAt.star_conj {f : 𝕜 -> F} {f' : F} (hf : H
asDerivAt f f' x) : HasDerivAt (star ∘ f ∘ conj) (star f') (conj x)

--- 原说明 ---
A function `f` has derivative `f'` at `z` iff `star ∘ f ∘ conj` has derivative `
star f'` at
`conj z`.
-/
lemma hasDerivAt_star_conj_iff {f : 𝕜 → F} {x : 𝕜} {f' : F} :
    HasDerivAt (star ∘ f ∘ conj) f' x ↔ HasDerivAt f (star f') (conj x) :=
  ⟨fun hf ↦ by convert! hf.star_conj; simp [Function.comp_def],
    fun hf ↦ by convert! hf.star_conj <;> simp⟩

/-- If `f` has derivative `f'` at `z`, then `conj ∘ f ∘ conj` has derivative `conj f'` at
`conj z`. -/
/-
**HasDerivAt.conj_conj** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasDerivAt.conj_conj {f : 𝕜 -> 𝕜} {f' : 𝕜} (hf : HasDerivAt f f' x) : HasD
erivAt (conj ∘ f ∘ conj) (conj f') (conj x)
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
· 使用引理 `HasDerivAt.star_conj`：HasDerivAt.star_conj {f : 𝕜 -> F} {f' : F} (hf : H
asDerivAt f f' x) : HasDerivAt (star ∘ f ∘ conj) (star f') (conj x)
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E

--- 原说明 ---
If `f` has derivative `f'` at `z`, then `conj ∘ f ∘ conj` has derivative `conj f
'` at
`conj z`.
-/
lemma HasDerivAt.conj_conj {f : 𝕜 → 𝕜} {f' : 𝕜} (hf : HasDerivAt f f' x) :
    HasDerivAt (conj ∘ f ∘ conj) (conj f') (conj x) :=
  hf.star_conj

/-- A function `f` has derivative `f'` at `z` iff `conj ∘ f ∘ conj` has derivative `conj f'` at
`conj z`. -/
@[simp]
/-
**hasDerivAt_conj_conj_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasDerivAt_conj_conj_iff {f : 𝕜 -> 𝕜} {x f' : 𝕜} : HasDerivAt (conj ∘ f ∘ 
conj) f' x ↔ HasDerivAt f (conj f') (conj x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `hasDerivAt_star_conj_iff`：hasDerivAt_star_conj_iff {f : 𝕜 -> F} {x : 𝕜} 
{f' : F} : HasDerivAt (star ∘ f ∘ conj) f' x ↔ HasDerivAt f (star f') (conj x)
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E

--- 原说明 ---
A function `f` has derivative `f'` at `z` iff `conj ∘ f ∘ conj` has derivative `
conj f'` at
`conj z`.
-/
lemma hasDerivAt_conj_conj_iff {f : 𝕜 → 𝕜} {x f' : 𝕜} :
    HasDerivAt (conj ∘ f ∘ conj) f' x ↔ HasDerivAt f (conj f') (conj x) :=
  hasDerivAt_star_conj_iff

/-- If `f` is differentiable at `conj z`, then `star ∘ f ∘ conj` is differentiable at `z`. -/
/-
**DifferentiableAt.star_conj** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DifferentiableAt.star_conj {f : 𝕜 -> F} (hf : DifferentiableAt 𝕜 f x) : Di
fferentiableAt 𝕜 (star ∘ f ∘ conj) (conj x)
参数：hf : DifferentiableAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DifferentiableAt.star_star`：DifferentiableAt.star_star {f : E -> F} {z :
 E} (hf : DifferentiableAt 𝕜 f z) : DifferentiableAt 𝕜 (star ∘ f ∘ star) (star z
)
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E

--- 原说明 ---
If `f` is differentiable at `conj z`, then `star ∘ f ∘ conj` is differentiable a
t `z`.
-/
lemma DifferentiableAt.star_conj {f : 𝕜 → F} (hf : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (star ∘ f ∘ conj) (conj x) :=
  hf.star_star

/-- A function `f` is differentiable at `conj z` iff `star ∘ f ∘ conj` is differentiable at `z`. -/
@[simp]
/-
**differentiableAt_star_conj_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：differentiableAt_star_conj_iff {f : 𝕜 -> F} : DifferentiableAt 𝕜 (star ∘ f
 ∘ conj) x ↔ DifferentiableAt 𝕜 f (conj x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `RingHomCompTriple.comp_apply`：comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
 {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `DifferentiableAt.star_conj`：DifferentiableAt.star_conj {f : 𝕜 -> F} (hf 
: DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (star ∘ f ∘ conj) (conj x)

--- 原说明 ---
A function `f` is differentiable at `conj z` iff `star ∘ f ∘ conj` is differenti
able at `z`.
-/
lemma differentiableAt_star_conj_iff {f : 𝕜 → F} :
    DifferentiableAt 𝕜 (star ∘ f ∘ conj) x ↔ DifferentiableAt 𝕜 f (conj x) :=
  ⟨fun hf ↦ by convert! hf.star_conj; simp [Function.comp_def],
    fun hf ↦ by convert! hf.star_conj; simp⟩

/-- If `f` is differentiable at `conj z`, then `conj ∘ f ∘ conj` is differentiable at `z`. -/
/-
**DifferentiableAt.conj_conj** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DifferentiableAt.conj_conj {f : 𝕜 -> 𝕜} (hf : DifferentiableAt 𝕜 f x) : Di
fferentiableAt 𝕜 (conj ∘ f ∘ conj) (conj x)
参数：hf : DifferentiableAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DifferentiableAt.star_star`：DifferentiableAt.star_star {f : E -> F} {z :
 E} (hf : DifferentiableAt 𝕜 f z) : DifferentiableAt 𝕜 (star ∘ f ∘ star) (star z
)
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E

--- 原说明 ---
If `f` is differentiable at `conj z`, then `conj ∘ f ∘ conj` is differentiable a
t `z`.
-/
lemma DifferentiableAt.conj_conj {f : 𝕜 → 𝕜} (hf : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (conj ∘ f ∘ conj) (conj x) :=
  hf.star_star

/-- A function `f` is differentiable at `conj z` iff `conj ∘ f ∘ conj` is differentiable at `z`. -/
@[simp]
/-
**differentiableAt_conj_conj_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：differentiableAt_conj_conj_iff {f : 𝕜 -> 𝕜} : DifferentiableAt 𝕜 (conj ∘ f
 ∘ conj) x ↔ DifferentiableAt 𝕜 f (conj x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `differentiableAt_star_conj_iff`：differentiableAt_star_conj_iff {f : 𝕜 ->
 F} : DifferentiableAt 𝕜 (star ∘ f ∘ conj) x ↔ DifferentiableAt 𝕜 f (conj x)
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E

--- 原说明 ---
A function `f` is differentiable at `conj z` iff `conj ∘ f ∘ conj` is differenti
able at `z`.
-/
lemma differentiableAt_conj_conj_iff {f : 𝕜 → 𝕜} :
    DifferentiableAt 𝕜 (conj ∘ f ∘ conj) x ↔ DifferentiableAt 𝕜 f (conj x) :=
  differentiableAt_star_conj_iff

/-- The derivative of `star ∘ f ∘ conj` is `star ∘ deriv f ∘ conj`. -/
@[simp]
/-
**deriv_star_conj** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：deriv_star_conj {f : 𝕜 -> F} : deriv (star ∘ f ∘ conj) = star ∘ deriv f ∘ 
conj
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHomCompTriple.comp_apply`：comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
 {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用引理 `HasDerivAt.star_conj`：HasDerivAt.star_conj {f : 𝕜 -> F} {f' : F} (hf : H
asDerivAt f f' x) : HasDerivAt (star ∘ f ∘ conj) (star f') (conj x)
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `differentiableAt_star_conj_iff`：differentiableAt_star_conj_iff {f : 𝕜 ->
 F} : DifferentiableAt 𝕜 (star ∘ f ∘ conj) x ↔ DifferentiableAt 𝕜 f (conj x)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `deriv_zero_of_not_differentiableAt`：deriv_zero_of_not_differentiableAt (
h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0

--- 原说明 ---
The derivative of `star ∘ f ∘ conj` is `star ∘ deriv f ∘ conj`.
-/
lemma deriv_star_conj {f : 𝕜 → F} :
    deriv (star ∘ f ∘ conj) = star ∘ deriv f ∘ conj := by
  ext z
  by_cases hf : DifferentiableAt 𝕜 f (conj z)
  · convert! hf.hasDerivAt.star_conj.deriv; simp
  · have := differentiableAt_star_conj_iff.not.2 hf
    simp_all [deriv_zero_of_not_differentiableAt]

/-- The derivative of `conj ∘ f ∘ conj` is `conj ∘ deriv f ∘ conj`. -/
@[simp]
/-
**deriv_conj_conj** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：deriv_conj_conj {f : 𝕜 -> 𝕜} : deriv (conj ∘ f ∘ conj) = conj ∘ deriv f ∘ 
conj
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `deriv_star_conj`：deriv_star_conj {f : 𝕜 -> F} : deriv (star ∘ f ∘ conj) 
= star ∘ deriv f ∘ conj
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E

--- 原说明 ---
The derivative of `conj ∘ f ∘ conj` is `conj ∘ deriv f ∘ conj`.
-/
lemma deriv_conj_conj {f : 𝕜 → 𝕜} :
    deriv (conj ∘ f ∘ conj) = conj ∘ deriv f ∘ conj := deriv_star_conj

end NontrivialStar

