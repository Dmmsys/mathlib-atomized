/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.Normed.Group.ZeroAtInfty
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic.FunProp
public import Mathlib.Topology.Algebra.UniformFilterBasis

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Tactic.MoveAdd


/-!
# Schwartz space

This file defines the Schwartz space. Usually, the Schwartz space is defined as the set of smooth
functions $f : ℝ^n → ℂ$ such that there exists $C_{αβ} > 0$ with $$|x^α ∂^β f(x)| < C_{αβ}$$ for
all $x ∈ ℝ^n$ and for all multiindices $α, β$.
In mathlib, we use a slightly different approach and define the Schwartz space as all
smooth functions `f : E → F`, where `E` and `F` are real normed vector spaces such that for all
natural numbers `k` and `n` we have uniform bounds `‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ < C`.
This approach completely avoids using partial derivatives as well as polynomials.
We construct the topology on the Schwartz space by a family of seminorms, which are the best
constants in the above estimates. The abstract theory of topological vector spaces developed in
`SeminormFamily.moduleFilterBasis` and `WithSeminorms.toLocallyConvexSpace` turns the
Schwartz space into a locally convex topological vector space.

## Main definitions

* `SchwartzMap`: The Schwartz space is the space of smooth functions such that all derivatives
  decay faster than any power of `‖x‖`.
* `SchwartzMap.seminorm`: The family of seminorms as described above
* `SchwartzMap.compCLM`: Composition with a function on the right as a continuous linear map
  `𝓢(E, F) →L[𝕜] 𝓢(D, F)`, provided that the function is temperate and grows polynomially near
  infinity
* `SchwartzMap.integralCLM`: Integration as a continuous linear map `𝓢(ℝ, F) →L[ℝ] F`

## Main statements

* `SchwartzMap.instIsUniformAddGroup` and `SchwartzMap.instLocallyConvexSpace`: The Schwartz space
  is a locally convex topological vector space.
* `SchwartzMap.one_add_le_sup_seminorm_apply`: For a Schwartz function `f` there is a uniform bound
  on `(1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ n f x‖`.

## Implementation details

The implementation of the seminorms is taken almost literally from `ContinuousLinearMap.opNorm`.

## Notation

* `𝓢(E, F)`: The Schwartz space `SchwartzMap E F` localized in `SchwartzSpace`

## Tags

Schwartz space, tempered distributions
-/

@[expose] public noncomputable section

open scoped Nat NNReal ContDiff

variable {ι 𝕜 𝕜' D E F G H V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (E F) in
/-- A function is a Schwartz function if it is smooth and all derivatives decay faster than
  any power of `‖x‖`. -/
/-
**SchwartzMap** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(E : Type u_5) →   (F : Type u_6) →     [inst : NormedAddCommGroup E] →   
    [NormedSpace ℝ E] → [inst : NormedAddCommGroup F] → [NormedSpace ℝ F] → Type
 (max u_5 u_6)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function is a Schwartz function if it is smooth and all derivatives decay fast
er than
  any power of `‖x‖`.
-/
structure SchwartzMap where
  /-- The underlying function.

  Do NOT use directly. Use the coercion instead. -/
  toFun : E → F
  smooth' : ContDiff ℝ ∞ toFun
  decay' : ∀ k n : ℕ, ∃ C : ℝ, ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n toFun x‖ ≤ C

/-- A function is a Schwartz function if it is smooth and all derivatives decay faster than
  any power of `‖x‖`. -/
scoped[SchwartzMap] notation "𝓢(" E ", " F ")" => SchwartzMap E F

namespace SchwartzMap

/-
**SchwartzMap.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
形式化陈述：instFunLike : FunLike 𝓢(E, F) E F where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike 𝓢(E, F) E F where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; congr

/-- All derivatives of a Schwartz function are rapidly decaying. -/
/-
**SchwartzMap.decay** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：decay (f : 𝓢(E, F)) (k n : Nat) : exists C : Real, 0 < C ∧ forall x, ‖x‖ ^
 k * ‖iteratedFDeriv Real n f x‖ <= C
参数：f : 𝓢(E, F)；k n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.decay'`：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAddCom
mGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 :
 NormedS…
· 使用定理 `lt_max_of_lt_right`：lt_max_of_lt_right (h : a < c) : a < max b c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b

--- 原说明 ---
All derivatives of a Schwartz function are rapidly decaying.
-/
theorem decay (f : 𝓢(E, F)) (k n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  rcases f.decay' k n with ⟨C, hC⟩
  exact ⟨max C 1, by positivity, fun x => (hC x).trans (le_max_left _ _)⟩

/-- Every Schwartz function is smooth. -/
@[fun_prop]
/-
**SchwartzMap.smooth** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：smooth (f : 𝓢(E, F)) (n : Nat∞) : ContDiff Real n f
参数：f : 𝓢(E, F)；n : Nat∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.of_le`：ContDiff.of_le (h : ContDiff 𝕜 n f) (hmn : m <= n) : Con
tDiff 𝕜 m f
· 使用定理 `SchwartzMap.smooth'`：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAddCo
mmGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 
: NormedS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_top`：le_top : a <= ⊤

--- 原说明 ---
Every Schwartz function is smooth.
-/
theorem smooth (f : 𝓢(E, F)) (n : ℕ∞) : ContDiff ℝ n f :=
  f.smooth'.of_le (mod_cast le_top)

/-- Every Schwartz function is smooth at any point. -/
@[fun_prop]
/-
**SchwartzMap.contDiffAt** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：contDiffAt (f : 𝓢(E, F)) (n : Nat∞) {x : E} : ContDiffAt Real n f x
参数：f : 𝓢(E, F)；n : Nat∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `SchwartzMap.smooth`：smooth (f : 𝓢(E, F)) (n : Nat∞) : ContDiff Real n f

--- 原说明 ---
Every Schwartz function is smooth at any point.
-/
theorem contDiffAt (f : 𝓢(E, F)) (n : ℕ∞) {x : E} : ContDiffAt ℝ n f x :=
  (f.smooth n).contDiffAt

/-- Every Schwartz function is continuous. -/
@[continuity, fun_prop]
/-
**SchwartzMap.continuous** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F] (f :
 SchwartzMap E F), Continuous ⇑f
参数：f : SchwartzMap E F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.continuous`：ContDiff.continuous (h : ContDiff 𝕜 n f) : Continuo
us f
· 使用定理 `SchwartzMap.smooth`：smooth (f : 𝓢(E, F)) (n : Nat∞) : ContDiff Real n f

--- 原说明 ---
Every Schwartz function is continuous.
-/
protected theorem continuous (f : 𝓢(E, F)) : Continuous f :=
  (f.smooth 0).continuous
/-
**SchwartzMap.instContinuousMapClass** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
形式化陈述：instContinuousMapClass : ContinuousMapClass 𝓢(E, F) E F where map_continuo
us
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.continuous`：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAd
dCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst
_3 : NormedS…
-/
instance instContinuousMapClass : ContinuousMapClass 𝓢(E, F) E F where
  map_continuous := SchwartzMap.continuous

/-- Every Schwartz function is differentiable. -/
@[fun_prop]
/-
**SchwartzMap.differentiable** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F] (f :
 SchwartzMap E F), Differentiable ℝ ⇑f
参数：f : SchwartzMap E F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.differentiable`：ContDiff.differentiable (h : ContDiff 𝕜 n f) (h
n : n != 0) : Differentiable 𝕜 f
· 使用定理 `SchwartzMap.smooth`：smooth (f : 𝓢(E, F)) (n : Nat∞) : ContDiff Real n f
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞

--- 原说明 ---
Every Schwartz function is differentiable.
-/
protected theorem differentiable (f : 𝓢(E, F)) : Differentiable ℝ f :=
  (f.smooth 1).differentiable one_ne_zero

/-- Every Schwartz function is differentiable at any point. -/
@[fun_prop]
/-
**SchwartzMap.differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F] (f :
 SchwartzMap E F) {x : E}, DifferentiableAt ℝ (⇑f) x
参数：f : SchwartzMap E F；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.differentiableAt`：Differentiable.differentiableAt (h : Di
fferentiable 𝕜 f) : DifferentiableAt 𝕜 f x
· 使用定理 `SchwartzMap.differentiable`：∀ {E : Type u_5} {F : Type u_6} [inst : Norm
edAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [
inst_3 : NormedS…

--- 原说明 ---
Every Schwartz function is differentiable at any point.
-/
protected theorem differentiableAt (f : 𝓢(E, F)) {x : E} : DifferentiableAt ℝ f x :=
  f.differentiable.differentiableAt

@[ext]
/-
**SchwartzMap.ext** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：ext {f g : 𝓢(E, F)} (h : forall x, (f : E -> F) x = g x) : f = g
参数：E, F；h : forall x, (f : E -> F) x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : 𝓢(E, F)} (h : ∀ x, (f : E → F) x = g x) : f = g :=
  DFunLike.ext f g h

section IsBigO

open Asymptotics Filter

variable (f : 𝓢(E, F))

/-- Auxiliary lemma, used in proving the more general result `isBigO_cocompact_rpow`. -/
/-
**SchwartzMap.isBigO_cocompact_zpow_neg_nat** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzM
ap`。
形式化陈述：isBigO_cocompact_zpow_neg_nat (k : Nat) : f =O[cocompact E] (‖·‖ ^ (-k : I
nt))
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.decay`：decay (f : 𝓢(E, F)) (k n : Nat) : exists C : Real, 0 
< C ∧ forall x, ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖ <= C
· 使用定理 `Asymptotics.IsBigO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u_20
} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F), f 
=O[l] g = ∃ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `Filter.cocompact_le_cofinite`：cocompact_le_cofinite : cocompact X <= cof
inite
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.eventually_cofinite_ne`：eventually_cofinite_ne (x : α) : forallᶠ 
a in cofinite, a != x
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `zpow_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialO
rder G₀] [PosMulReflectLT G₀] {a : G₀}   [ZeroLEOneClass G₀], 0 < a → ∀ (n : ℤ…
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `le_div_iff₀'`：le_div_iff₀' (hc : 0 < c) : a <= b / c ↔ c * a <= b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_iteratedFDeriv_zero`：norm_iteratedFDeriv_zero : ‖iteratedFDeriv 𝕜 0
 f x‖ = ‖f x‖

--- 原说明 ---
Auxiliary lemma, used in proving the more general result `isBigO_cocompact_rpow`
.
-/
theorem isBigO_cocompact_zpow_neg_nat (k : ℕ) :
    f =O[cocompact E] (‖·‖ ^ (-k : ℤ)) := by
  obtain ⟨d, _, hd'⟩ := f.decay k 0
  simp only [norm_iteratedFDeriv_zero] at hd'
  simp_rw [Asymptotics.IsBigO, Asymptotics.IsBigOWith]
  refine ⟨d, Filter.Eventually.filter_mono Filter.cocompact_le_cofinite ?_⟩
  refine (Filter.eventually_cofinite_ne 0).mono fun x hx ↦ ?_
  rw [Real.norm_of_nonneg (by positivity), zpow_neg, ← div_eq_mul_inv, le_div_iff₀' (by positivity)]
  exact hd' x
/-
**SchwartzMap.isBigO_cocompact_rpow** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：isBigO_cocompact_rpow [ProperSpace E] (s : Real) : f =O[cocompact E] (‖·‖ 
^ s)
参数：s : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `neg_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftMono 
α] [AddRightMono α] {a b : α}, -a ≤ b ↔ -b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Nat.le_ceil`：le_ceil (a : R) : a <= ⌈a⌉₊
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `SchwartzMap.isBigO_cocompact_zpow_neg_nat`：isBigO_cocompact_zpow_neg_nat
 (k : Nat) : f =O[cocompact E] (‖·‖ ^ (-k : Int))
· 使用定理 `Asymptotics.IsBigO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u_20
} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F), f 
=O[l] g = ∃ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `zpow_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialO
rder G₀] [PosMulReflectLT G₀] {a : G₀}   [ZeroLEOneClass G₀], 0 < a → ∀ (n : ℤ…
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_intCast`：rpow_intCast (x : Real) (n : Int) : x ^ (n : Real) = 
x ^ n
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
（共 33 条，此处仅展示前 30 条）
-/
theorem isBigO_cocompact_rpow [ProperSpace E] (s : ℝ) :
    f =O[cocompact E] (‖·‖ ^ s) := by
  let k := ⌈-s⌉₊
  have hk : -(k : ℝ) ≤ s := neg_le.mp (Nat.le_ceil (-s))
  refine (isBigO_cocompact_zpow_neg_nat f k).trans ?_
  suffices (fun x : ℝ ↦ x ^ (-k : ℤ)) =O[atTop] fun x : ℝ ↦ x ^ s
    from this.comp_tendsto tendsto_norm_cocompact_atTop
  simp_rw [Asymptotics.IsBigO, Asymptotics.IsBigOWith]
  refine ⟨1, (Filter.eventually_ge_atTop 1).mono fun x hx ↦ ?_⟩
  rw [one_mul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
    ← Real.rpow_intCast, Int.cast_neg, Int.cast_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hx hk
/-
**SchwartzMap.isBigO_cocompact_zpow** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：isBigO_cocompact_zpow [ProperSpace E] (k : Int) : f =O[cocompact E] (‖·‖ ^
 k)
参数：k : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_intCast`：rpow_intCast (x : Real) (n : Int) : x ^ (n : Real) = 
x ^ n
· 使用定理 `SchwartzMap.isBigO_cocompact_rpow`：isBigO_cocompact_rpow [ProperSpace E]
 (s : Real) : f =O[cocompact E] (‖·‖ ^ s)
-/
theorem isBigO_cocompact_zpow [ProperSpace E] (k : ℤ) :
    f =O[cocompact E] (‖·‖ ^ k) := by
  simpa only [Real.rpow_intCast] using isBigO_cocompact_rpow f k

end IsBigO

open Filter Topology in
/-
**SchwartzMap.tendsto_cocompact** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：tendsto_cocompact [ProperSpace E] (f : 𝓢(E, F)) : Tendsto f (cocompact E) 
(𝓝 0)
参数：f : 𝓢(E, F)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans_tendsto`：∀ {α : Type u_1} {E'' : Type u_9} {F''
 : Type u_10} [inst : NormedAddCommGroup E''] [inst_1 : NormedAddCommGroup F''] 
  {f'' : α → E''} {g''…
· 使用定理 `SchwartzMap.isBigO_cocompact_rpow`：isBigO_cocompact_rpow [ProperSpace E]
 (s : Real) : f =O[cocompact E] (‖·‖ ^ s)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_neg_one`：rpow_neg_one (x : Real) : x ^ (-1 : Real) = x⁻¹
· 使用定理 `Filter.Tendsto.inv_tendsto_atTop`：Filter.Tendsto.inv_tendsto_atTop (h : 
Tendsto f l atTop) : Tendsto f⁻¹ l (𝓝 0)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `tendsto_norm_cocompact_atTop`：∀ {E : Type u_2} [inst : SeminormedAddGrou
p E] [ProperSpace E], Filter.Tendsto norm (Filter.cocompact E) Filter.atTop
-/
theorem tendsto_cocompact [ProperSpace E] (f : 𝓢(E, F)) :
    Tendsto f (cocompact E) (𝓝 0) := by
  apply (isBigO_cocompact_rpow f (-1)).trans_tendsto
  simp_rw [Real.rpow_neg_one]
  exact tendsto_norm_cocompact_atTop.inv_tendsto_atTop

section Aux

/-
**SchwartzMap.bounds_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem bounds_nonempty (k n : ℕ) (f : 𝓢(E, F)) :
    ∃ c : ℝ, c ∈ { c : ℝ | 0 ≤ c ∧ ∀ x : E, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ c } :=
  let ⟨M, hMp, hMb⟩ := f.decay k n
  ⟨M, le_of_lt hMp, hMb⟩
/-
**SchwartzMap.bounds_bddBelow** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem bounds_bddBelow (k n : ℕ) (f : 𝓢(E, F)) :
    BddBelow { c | 0 ≤ c ∧ ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ c } :=
  ⟨0, fun _ ⟨hn, _⟩ => hn⟩
/-
**SchwartzMap.decay_add_le_aux** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem decay_add_le_aux (k n : ℕ) (f g : 𝓢(E, F)) (x : E) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n ((f : E → F) + (g : E → F)) x‖ ≤
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ + ‖x‖ ^ k * ‖iteratedFDeriv ℝ n g x‖ := by
  rw [← mul_add]
  gcongr _ * ?_
  rw [iteratedFDeriv_add_apply (f.smooth _).contDiffAt (g.smooth _).contDiffAt]
  exact norm_add_le _ _
/-
**SchwartzMap.decay_neg_aux** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem decay_neg_aux (k n : ℕ) (f : 𝓢(E, F)) (x : E) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (-f : E → F) x‖ = ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ := by
  rw [iteratedFDeriv_neg_apply, norm_neg]

variable [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F] in
/-
**SchwartzMap.decay_smul_aux** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem decay_smul_aux (k n : ℕ) (f : 𝓢(E, F)) (c : 𝕜) (x : E) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (c • (f : E → F)) x‖ =
      ‖c‖ * ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ := by
  rw [mul_comm ‖c‖, mul_assoc, iteratedFDeriv_const_smul_apply (f.smooth _).contDiffAt,
    norm_smul c (iteratedFDeriv ℝ n (⇑f) x)]

end Aux

section SeminormAux

/-- Helper definition for the seminorms of the Schwartz space. -/
/-
**SchwartzMap.seminormAux** 是 Mathlib 中的一个定义，位于命名空间 `SchwartzMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper definition for the seminorms of the Schwartz space.
-/
private protected def seminormAux (k n : ℕ) (f : 𝓢(E, F)) : ℝ :=
  sInf { c | 0 ≤ c ∧ ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ c }
/-
**SchwartzMap.seminormAux_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem seminormAux_nonneg (k n : ℕ) (f : 𝓢(E, F)) : 0 ≤ f.seminormAux k n :=
  le_csInf (bounds_nonempty k n f) fun _ ⟨hx, _⟩ => hx
/-
**SchwartzMap.le_seminormAux** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem le_seminormAux (k n : ℕ) (f : 𝓢(E, F)) (x : E) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ f.seminormAux k n :=
  le_csInf (bounds_nonempty k n f) fun _ ⟨_, h⟩ => h x

/-- If one controls the norm of every `A x`, then one controls the norm of `A`. -/
/-
**SchwartzMap.seminormAux_le_bound** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If one controls the norm of every `A x`, then one controls the norm of `A`.
-/
private theorem seminormAux_le_bound (k n : ℕ) (f : 𝓢(E, F)) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ M) : f.seminormAux k n ≤ M :=
  csInf_le (bounds_bddBelow k n f) ⟨hMp, hM⟩

end SeminormAux

/-! ### Algebraic properties -/

section SMul

variable [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F] [NormedField 𝕜'] [NormedSpace 𝕜' F]
  [SMulCommClass ℝ 𝕜' F]

/-
**SchwartzMap.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
形式化陈述：instSMul : SMul 𝕜 𝓢(E, F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul : SMul 𝕜 𝓢(E, F) :=
  ⟨fun c f =>
    { toFun := c • (f : E → F)
      smooth' := by exact (f.smooth _).const_smul c
      decay' k n := by
        use f.seminormAux k n * ‖c‖
        intro x
        calc
          ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (c • ⇑f) x‖ = ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ * ‖c‖ := by
            rw [mul_comm _ ‖c‖, ← mul_assoc]
            exact decay_smul_aux k n f c x
          _ ≤ SchwartzMap.seminormAux k n f * ‖c‖ := by
            gcongr
            apply f.le_seminormAux }⟩
/-
**SchwartzMap.** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSMulApply 𝕜 𝓢(E, F) E F where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias smul_apply := smul_apply
/-
**SchwartzMap.instIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
形式化陈述：instIsScalarTower [SMul 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' F] : IsScalarTower 𝕜 𝕜' 
𝓢(E, F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FunLike.isScalarTower`：∀ {M : Type u_1} {M' : Type u_2} {F : Type u_3} {
α : Type u_4} {β : Type u_5} [i : FunLike F α β] [inst : SMul M β]   [inst_1 : S
Mul M' β] […
· 使用定理 `SchwartzMap.instIsSMulApply`：∀ {𝕜 : Type u_2} {E : Type u_5} {F : Type u
_6} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedA
ddCommGroup F] [i…
-/
instance instIsScalarTower [SMul 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' F] : IsScalarTower 𝕜 𝕜' 𝓢(E, F) :=
  FunLike.isScalarTower
/-
**SchwartzMap.instSMulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
形式化陈述：instSMulCommClass [SMulCommClass 𝕜 𝕜' F] : SMulCommClass 𝕜 𝕜' 𝓢(E, F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FunLike.smulCommClass`：∀ {M : Type u_1} {M' : Type u_2} {F : Type u_3} {
α : Type u_4} {β : Type u_5} [i : FunLike F α β] [inst : SMul M β]   [inst_1 : S
Mul M' β] […
· 使用定理 `SchwartzMap.instIsSMulApply`：∀ {𝕜 : Type u_2} {E : Type u_5} {F : Type u
_6} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedA
ddCommGroup F] [i…
-/
instance instSMulCommClass [SMulCommClass 𝕜 𝕜' F] : SMulCommClass 𝕜 𝕜' 𝓢(E, F) :=
  FunLike.smulCommClass
/-
**SchwartzMap.seminormAux_smul_le** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem seminormAux_smul_le (k n : ℕ) (c : 𝕜) (f : 𝓢(E, F)) :
    (c • f).seminormAux k n ≤ ‖c‖ * f.seminormAux k n := by
  refine (c • f).seminormAux_le_bound k n (mul_nonneg (norm_nonneg _) (seminormAux_nonneg _ _ _))
      fun x => (decay_smul_aux k n f c x).trans_le ?_
  rw [mul_assoc]
  gcongr
  exact f.le_seminormAux k n x
/-
**SchwartzMap.instNSMul** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
形式化陈述：instNSMul : SMul Nat 𝓢(E, F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNSMul : SMul ℕ 𝓢(E, F) :=
  ⟨fun c f =>
    { toFun := c • (f : E → F)
      smooth' := by exact (f.smooth _).const_smul c
      decay' := by simpa [← Nat.cast_smul_eq_nsmul ℝ] using! ((c : ℝ) • f).decay' }⟩
/-
**SchwartzMap.** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSMulApply ℕ 𝓢(E, F) E F where
  smul_apply _ _ _ := rfl
/-
**SchwartzMap.instZSMul** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
形式化陈述：instZSMul : SMul Int 𝓢(E, F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZSMul : SMul ℤ 𝓢(E, F) :=
  ⟨fun c f =>
    { toFun := c • (f : E → F)
      smooth' := by exact (f.smooth _).const_smul c
      decay' := by simpa [← Int.cast_smul_eq_zsmul ℝ] using! ((c : ℝ) • f).decay' }⟩
/-
**SchwartzMap.** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSMulApply ℤ 𝓢(E, F) E F where
  smul_apply _ _ _ := rfl

end SMul

section Zero

/-
**SchwartzMap.instZero** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
形式化陈述：instZero : Zero 𝓢(E, F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZero : Zero 𝓢(E, F) :=
  ⟨{  toFun := fun _ => 0
      smooth' := by exact contDiff_const
      decay' := fun _ _ => ⟨1, fun _ => by simp⟩ }⟩
/-
**SchwartzMap.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
形式化陈述：instInhabited : Inhabited 𝓢(E, F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited : Inhabited 𝓢(E, F) :=
  ⟨0⟩
/-
**SchwartzMap.** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZeroApply 𝓢(E, F) E F where
  zero_apply _ := rfl

@[deprecated (since := "2026-06-10")] alias coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-06-10")] alias coeFn_zero := FunLike.coe_zero

@[deprecated (since := "2026-06-10")] protected alias zero_apply := zero_apply
/-
**SchwartzMap.seminormAux_zero** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem seminormAux_zero (k n : ℕ) : (0 : 𝓢(E, F)).seminormAux k n = 0 :=
  le_antisymm (seminormAux_le_bound k n _ rfl.le fun _ => by simp [FunLike.coe_zero])
    (seminormAux_nonneg _ _ _)

end Zero

section Neg

/-
**SchwartzMap.instNeg** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
形式化陈述：instNeg : Neg 𝓢(E, F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNeg : Neg 𝓢(E, F) :=
  ⟨fun f =>
    ⟨-f, by exact (f.smooth _).neg, fun k n => by
      use f.seminormAux k n
      intro x
      grw [f.decay_neg_aux k n x, f.le_seminormAux k n x]⟩⟩
/-
**SchwartzMap.** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsNegApply 𝓢(E, F) E F where
  neg_apply _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias neg_apply := neg_apply

end Neg

section Add

/-
**SchwartzMap.instAdd** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
形式化陈述：instAdd : Add 𝓢(E, F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAdd : Add 𝓢(E, F) :=
  ⟨fun f g =>
    ⟨f + g, by exact (f.smooth _).add (g.smooth _), fun k n => by
      use f.seminormAux k n + g.seminormAux k n
      intro x
      grw [decay_add_le_aux k n f g x, f.le_seminormAux k n x, g.le_seminormAux k n x]⟩⟩
/-
**SchwartzMap.** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsAddApply 𝓢(E, F) E F where
  add_apply _ _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias add_apply := add_apply
/-
**SchwartzMap.seminormAux_add_le** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem seminormAux_add_le (k n : ℕ) (f g : 𝓢(E, F)) :
    (f + g).seminormAux k n ≤ f.seminormAux k n + g.seminormAux k n :=
  (f + g).seminormAux_le_bound k n
    (add_nonneg (seminormAux_nonneg _ _ _) (seminormAux_nonneg _ _ _)) fun x =>
    (decay_add_le_aux k n f g x).trans <|
      add_le_add (f.le_seminormAux k n x) (g.le_seminormAux k n x)

end Add

section Sub

/-
**SchwartzMap.instSub** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
形式化陈述：instSub : Sub 𝓢(E, F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSub : Sub 𝓢(E, F) :=
  ⟨fun f g =>
    ⟨f - g, by exact (f.smooth _).sub (g.smooth _), by
      intro k n
      refine ⟨f.seminormAux k n + g.seminormAux k n, fun x => ?_⟩
      grw [← f.le_seminormAux k n x, ← g.le_seminormAux k n x]
      rw [sub_eq_add_neg]
      rw [← decay_neg_aux k n g x]
      exact decay_add_le_aux k n f (-g) x⟩⟩
/-
**SchwartzMap.** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSubApply 𝓢(E, F) E F where
  sub_apply _ _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias sub_apply := sub_apply

end Sub

section AddCommGroup

/-
**SchwartzMap.instAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
形式化陈述：instAddCommGroup : AddCommGroup 𝓢(E, F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommGroup : AddCommGroup 𝓢(E, F) := fast_instance% FunLike.addCommGroup

@[deprecated (since := "2026-06-10")] protected alias sum_apply := sum_apply

variable (E F)

@[deprecated (since := "2026-06-10")] alias coeHom := FunLike.coeAddMonoidHom

variable {E F}

@[deprecated (since := "2026-06-10")] alias coe_coeHom := FunLike.coe_coeAddMonoidHom

@[deprecated (since := "2026-06-10")] alias coeHom_injective := FunLike.coeAddMonoidHom_injective

end AddCommGroup

section Module

variable [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-
**SchwartzMap.instModule** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
形式化陈述：instModule : Module 𝕜 𝓢(E, F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModule : Module 𝕜 𝓢(E, F) := fast_instance% FunLike.module

end Module

section Seminorms

/-! ### Seminorms on Schwartz space -/


variable [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
variable (𝕜)

/-- The seminorms of the Schwartz space given by the best constants in the definition of
`𝓢(E, F)`. -/
@[no_expose]
/-
**SchwartzMap.seminorm** 是 Mathlib 中的一个定义，位于命名空间 `SchwartzMap`。
形式化陈述：(𝕜 : Type u_2) →   {E : Type u_5} →     {F : Type u_6} →       [inst : Nor
medAddCommGroup E] →         [inst_1 : NormedSpace ℝ E] →           [inst_2 : No
rmedAddCommGroup F] →             [inst_3 : NormedSpace ℝ F] →               [in
st_4 : NormedField 𝕜] →                 [inst_5 : NormedSpace 𝕜 F] → [inst_6 : S
MulCommClass ℝ 𝕜 F] → ℕ → ℕ → Seminorm 𝕜 (SchwartzMap E F)
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Analysis.Distribution.SchwartzSpace.Basic.0.SchwartzMap
.seminormAux_zero`：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAddCommGroup E]
 [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedS…
· 使用定理 `_private.Mathlib.Analysis.Distribution.SchwartzSpace.Basic.0.SchwartzMap
.seminormAux_add_le`：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAddCommGroup 
E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : Normed
S…
· 使用定理 `_private.Mathlib.Analysis.Distribution.SchwartzSpace.Basic.0.SchwartzMap
.seminormAux_smul_le`：∀ {𝕜 : Type u_2} {E : Type u_5} {F : Type u_6} [inst : Nor
medAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] 
[i…

--- 原说明 ---
The seminorms of the Schwartz space given by the best constants in the definitio
n of
`𝓢(E, F)`.
-/
protected def seminorm (k n : ℕ) : Seminorm 𝕜 𝓢(E, F) :=
  Seminorm.ofSMulLE (SchwartzMap.seminormAux k n) (seminormAux_zero k n) (seminormAux_add_le k n)
    (seminormAux_smul_le k n)

/-- The seminorm is given by infimum over all `c` such that the estimate
`‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ c` holds.

Note that it is usually better to use `seminorm_le_bound` or `le_seminorm` instead of this lemma. -/
/-
**SchwartzMap.seminorm_apply** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：seminorm_apply {k n : Nat} (f : 𝓢(E, F)) : SchwartzMap.seminorm 𝕜 k n f = 
sInf { c | 0 <= c ∧ forall x, ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖ <= c }
参数：f : 𝓢(E, F)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The seminorm is given by infimum over all `c` such that the estimate
`‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ c` holds.

Note that it is usually better to use `seminorm_le_bound` or `le_seminorm` inste
ad of this lemma.
-/
theorem seminorm_apply {k n : ℕ} (f : 𝓢(E, F)) : SchwartzMap.seminorm 𝕜 k n f =
    sInf { c | 0 ≤ c ∧ ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ c } := by rfl

/-- If one controls the seminorm for every `x`, then one controls the seminorm. -/
/-
**SchwartzMap.seminorm_le_bound** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：seminorm_le_bound (k n : Nat) (f : 𝓢(E, F)) {M : Real} (hMp : 0 <= M) (hM 
: forall x, ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖ <= M) : SchwartzMap.seminorm 𝕜
 k n f <= M
参数：k n : Nat；f : 𝓢(E, F)；hMp : 0 <= M；hM : forall x, ‖x‖ ^ k * ‖iteratedFDeriv R
eal n f x‖ <= M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Analysis.Distribution.SchwartzSpace.Basic.0.SchwartzMap
.seminormAux_le_bound`：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : Norm
edS…

--- 原说明 ---
If one controls the seminorm for every `x`, then one controls the seminorm.
-/
theorem seminorm_le_bound (k n : ℕ) (f : 𝓢(E, F)) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ M) : SchwartzMap.seminorm 𝕜 k n f ≤ M :=
  f.seminormAux_le_bound k n hMp hM

/-- If one controls the seminorm for every `x`, then one controls the seminorm.

Variant for functions `𝓢(ℝ, F)`. -/
/-
**SchwartzMap.seminorm_le_bound'** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：seminorm_le_bound' (k n : Nat) (f : 𝓢(Real, F)) {M : Real} (hMp : 0 <= M) 
(hM : forall x, |x| ^ k * ‖iteratedDeriv n f x‖ <= M) : SchwartzMap.seminorm 𝕜 k
 n f <= M
参数：k n : Nat；f : 𝓢(Real, F)；hMp : 0 <= M；hM : forall x, |x| ^ k * ‖iteratedDeriv
 n f x‖ <= M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.seminorm_le_bound`：seminorm_le_bound (k n : Nat) (f : 𝓢(E, F
)) {M : Real} (hMp : 0 <= M) (hM : forall x, ‖x‖ ^ k * ‖iteratedFDeriv Real n f 
x‖ <= M) : Schwartz…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_iteratedFDeriv_eq_norm_iteratedDeriv`：norm_iteratedFDeriv_eq_norm_i
teratedDeriv : ‖iteratedFDeriv 𝕜 n f x‖ = ‖iteratedDeriv n f x‖

--- 原说明 ---
If one controls the seminorm for every `x`, then one controls the seminorm.

Variant for functions `𝓢(ℝ, F)`.
-/
theorem seminorm_le_bound' (k n : ℕ) (f : 𝓢(ℝ, F)) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ x, |x| ^ k * ‖iteratedDeriv n f x‖ ≤ M) : SchwartzMap.seminorm 𝕜 k n f ≤ M := by
  refine seminorm_le_bound 𝕜 k n f hMp ?_
  simpa only [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]

/-- The seminorm controls the Schwartz estimate for any fixed `x`. -/
/-
**SchwartzMap.le_seminorm** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：le_seminorm (k n : Nat) (f : 𝓢(E, F)) (x : E) : ‖x‖ ^ k * ‖iteratedFDeriv 
Real n f x‖ <= SchwartzMap.seminorm 𝕜 k n f
参数：k n : Nat；f : 𝓢(E, F)；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Analysis.Distribution.SchwartzSpace.Basic.0.SchwartzMap
.le_seminormAux`：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAddCommGroup E] [
inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedS…

--- 原说明 ---
The seminorm controls the Schwartz estimate for any fixed `x`.
-/
theorem le_seminorm (k n : ℕ) (f : 𝓢(E, F)) (x : E) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ SchwartzMap.seminorm 𝕜 k n f :=
  f.le_seminormAux k n x

/-- The seminorm controls the Schwartz estimate for any fixed `x`.

Variant for functions `𝓢(ℝ, F)`. -/
/-
**SchwartzMap.le_seminorm'** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：le_seminorm' (k n : Nat) (f : 𝓢(Real, F)) (x : Real) : |x| ^ k * ‖iterated
Deriv n f x‖ <= SchwartzMap.seminorm 𝕜 k n f
参数：k n : Nat；f : 𝓢(Real, F)；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.le_seminorm`：le_seminorm (k n : Nat) (f : 𝓢(E, F)) (x : E) :
 ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖ <= SchwartzMap.seminorm 𝕜 k n f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `norm_iteratedFDeriv_eq_norm_iteratedDeriv`：norm_iteratedFDeriv_eq_norm_i
teratedDeriv : ‖iteratedFDeriv 𝕜 n f x‖ = ‖iteratedDeriv n f x‖

--- 原说明 ---
The seminorm controls the Schwartz estimate for any fixed `x`.

Variant for functions `𝓢(ℝ, F)`.
-/
theorem le_seminorm' (k n : ℕ) (f : 𝓢(ℝ, F)) (x : ℝ) :
    |x| ^ k * ‖iteratedDeriv n f x‖ ≤ SchwartzMap.seminorm 𝕜 k n f := by
  have := le_seminorm 𝕜 k n f x
  rwa [← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
/-
**SchwartzMap.norm_iteratedFDeriv_le_seminorm** 是 Mathlib 中的一个定理，位于命名空间 `Schwart
zMap`。
形式化陈述：norm_iteratedFDeriv_le_seminorm (f : 𝓢(E, F)) (n : Nat) (x₀ : E) : ‖iterat
edFDeriv Real n f x₀‖ <= (SchwartzMap.seminorm 𝕜 0 n) f
参数：f : 𝓢(E, F)；n : Nat；x₀ : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.le_seminorm`：le_seminorm (k n : Nat) (f : 𝓢(E, F)) (x : E) :
 ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖ <= SchwartzMap.seminorm 𝕜 k n f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
-/
theorem norm_iteratedFDeriv_le_seminorm (f : 𝓢(E, F)) (n : ℕ) (x₀ : E) :
    ‖iteratedFDeriv ℝ n f x₀‖ ≤ (SchwartzMap.seminorm 𝕜 0 n) f := by
  have := SchwartzMap.le_seminorm 𝕜 0 n f x₀
  rwa [pow_zero, one_mul] at this
/-
**SchwartzMap.norm_pow_mul_le_seminorm** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：norm_pow_mul_le_seminorm (f : 𝓢(E, F)) (k : Nat) (x₀ : E) : ‖x₀‖ ^ k * ‖f 
x₀‖ <= (SchwartzMap.seminorm 𝕜 k 0) f
参数：f : 𝓢(E, F)；k : Nat；x₀ : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.le_seminorm`：le_seminorm (k n : Nat) (f : 𝓢(E, F)) (x : E) :
 ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖ <= SchwartzMap.seminorm 𝕜 k n f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_iteratedFDeriv_zero`：norm_iteratedFDeriv_zero : ‖iteratedFDeriv 𝕜 0
 f x‖ = ‖f x‖
-/
theorem norm_pow_mul_le_seminorm (f : 𝓢(E, F)) (k : ℕ) (x₀ : E) :
    ‖x₀‖ ^ k * ‖f x₀‖ ≤ (SchwartzMap.seminorm 𝕜 k 0) f := by
  have := SchwartzMap.le_seminorm 𝕜 k 0 f x₀
  rwa [norm_iteratedFDeriv_zero] at this
/-
**SchwartzMap.norm_le_seminorm** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：norm_le_seminorm (f : 𝓢(E, F)) (x₀ : E) : ‖f x₀‖ <= (SchwartzMap.seminorm 
𝕜 0 0) f
参数：f : 𝓢(E, F)；x₀ : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.norm_pow_mul_le_seminorm`：norm_pow_mul_le_seminorm (f : 𝓢(E,
 F)) (k : Nat) (x₀ : E) : ‖x₀‖ ^ k * ‖f x₀‖ <= (SchwartzMap.seminorm 𝕜 k 0) f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
-/
theorem norm_le_seminorm (f : 𝓢(E, F)) (x₀ : E) : ‖f x₀‖ ≤ (SchwartzMap.seminorm 𝕜 0 0) f := by
  have := norm_pow_mul_le_seminorm 𝕜 f 0 x₀
  rwa [pow_zero, one_mul] at this

variable (E F)

/-- The family of Schwartz seminorms. -/
/-
**SchwartzMap._root_.schwartzSeminormFamily** 是 Mathlib 中的一个定义，位于命名空间 `SchwartzM
ap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of Schwartz seminorms.
-/
def _root_.schwartzSeminormFamily : SeminormFamily 𝕜 𝓢(E, F) (ℕ × ℕ) :=
  fun m => SchwartzMap.seminorm 𝕜 m.1 m.2

@[simp]
/-
**SchwartzMap.schwartzSeminormFamily_apply** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMa
p`。
形式化陈述：schwartzSeminormFamily_apply (n k : Nat) : schwartzSeminormFamily 𝕜 E F (n
, k) = SchwartzMap.seminorm 𝕜 n k
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem schwartzSeminormFamily_apply (n k : ℕ) :
    schwartzSeminormFamily 𝕜 E F (n, k) = SchwartzMap.seminorm 𝕜 n k :=
  rfl

@[simp]
/-
**SchwartzMap.schwartzSeminormFamily_apply_zero** 是 Mathlib 中的一个定理，位于命名空间 `Schwa
rtzMap`。
形式化陈述：schwartzSeminormFamily_apply_zero : schwartzSeminormFamily 𝕜 E F 0 = Schwa
rtzMap.seminorm 𝕜 0 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem schwartzSeminormFamily_apply_zero :
    schwartzSeminormFamily 𝕜 E F 0 = SchwartzMap.seminorm 𝕜 0 0 :=
  rfl

variable {𝕜 E F}

/-- A more convenient version of `le_sup_seminorm_apply`.

The set `Finset.Iic m` is the set of all pairs `(k', n')` with `k' ≤ m.1` and `n' ≤ m.2`.
Note that the constant is far from optimal. -/
/-
**SchwartzMap.one_add_le_sup_seminorm_apply** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzM
ap`。
形式化陈述：one_add_le_sup_seminorm_apply {m : Nat × Nat} {k n : Nat} (hk : k <= m.1) 
(hn : n <= m.2) (f : 𝓢(E, F)) (x : E) : (1 + ‖x‖) ^ k * ‖iteratedFDeriv Real n f
 x‖ <= 2 ^ m.1 * (Finset.Iic m).sup (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2) f
参数：hk : k <= m.1；hn : n <= m.2；f : 𝓢(E, F)；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_pow`：add_pow [CommSemiring R] (x y : R) (n : Nat) : (x + y) ^ n = ∑ 
m in range (n + 1), x ^ m * y ^ (n - m) * n.choose m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sum_range_choose`：sum_range_choose (n : Nat) : (∑ m in range (n + 1)
, n.choose m) = 2 ^ n
· 使用引理 `Nat.cast_sum`：cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι ->
 Nat) : ↑(∑ x in s, f x : Nat) = ∑ x in s, (f x : R)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Finset.sum_le_sum_of_subset_of_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [
inst : AddCommMonoid N] [inst_1 : Preorder N] {f : ι → N} {s t : Finset ι}   [Ad
dLeftMono N], s ⊆ t → (∀ i …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
A more convenient version of `le_sup_seminorm_apply`.

The set `Finset.Iic m` is the set of all pairs `(k', n')` with `k' ≤ m.1` and `n
' ≤ m.2`.
Note that the constant is far from optimal.
-/
theorem one_add_le_sup_seminorm_apply {m : ℕ × ℕ} {k n : ℕ} (hk : k ≤ m.1) (hn : n ≤ m.2)
    (f : 𝓢(E, F)) (x : E) :
    (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤
      2 ^ m.1 * (Finset.Iic m).sup (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2) f := by
  rw [add_comm, add_pow]
  simp only [one_pow, mul_one, Finset.sum_mul]
  norm_cast
  rw [← Nat.sum_range_choose m.1]
  push_cast
  rw [Finset.sum_mul]
  have hk' : Finset.range (k + 1) ⊆ Finset.range (m.1 + 1) := by grind
  grw [hk']
  gcongr ∑ _i ∈ Finset.range (m.1 + 1), ?_ with i hi
  move_mul [(Nat.choose k i : ℝ), (Nat.choose m.1 i : ℝ)]
  gcongr
  grw [le_seminorm 𝕜 i n f x]
  apply Seminorm.le_def.1
  exact Finset.le_sup_of_le (Finset.mem_Iic.2 <|
    Prod.mk_le_mk.2 ⟨Finset.mem_range_succ_iff.mp hi, hn⟩) le_rfl

end Seminorms

section Topology

/-! ### The topology on the Schwartz space -/


variable [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
variable (𝕜 E F)

/-
**SchwartzMap.instTopologicalSpace** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
形式化陈述：instTopologicalSpace : TopologicalSpace 𝓢(E, F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instTopologicalSpace : TopologicalSpace 𝓢(E, F) :=
  (schwartzSeminormFamily ℝ E F).moduleFilterBasis.topology'
/-
**SchwartzMap._root_.schwartz_withSeminorms** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzM
ap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.schwartz_withSeminorms : WithSeminorms (schwartzSeminormFamily 𝕜 E F) := by
  have A : WithSeminorms (schwartzSeminormFamily ℝ E F) := ⟨rfl⟩
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf] at A ⊢
  rw [A]
  rfl

variable {𝕜 E F}
/-
**SchwartzMap.instContinuousSMul** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
形式化陈述：instContinuousSMul : ContinuousSMul 𝕜 𝓢(E, F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithSeminorms.withSeminorms_eq`：WithSeminorms.withSeminorms_eq {p : Semi
normFamily 𝕜 E ι} [t : TopologicalSpace E] (hp : WithSeminorms p) : t = p.module
FilterBasis.topology
· 使用定理 `schwartz_withSeminorms`：∀ (𝕜 : Type u_2) (E : Type u_5) (F : Type u_6) [
inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCom
mGroup F] [i…
· 使用定理 `ModuleFilterBasis.continuousSMul`：∀ {R : Type u_1} {M : Type u_2} [inst 
: Ring R] [inst_1 : TopologicalSpace R] [inst_2 : AddCommGroup M]   [inst_3 : _r
oot_.Module R M] (B : …
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
-/
instance instContinuousSMul : ContinuousSMul 𝕜 𝓢(E, F) := by
  rw [(schwartz_withSeminorms 𝕜 E F).withSeminorms_eq]
  exact (schwartzSeminormFamily 𝕜 E F).moduleFilterBasis.continuousSMul
/-
**SchwartzMap.instIsTopologicalAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
形式化陈述：instIsTopologicalAddGroup : IsTopologicalAddGroup 𝓢(E, F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddGroupFilterBasis.isTopologicalAddGroup`：∀ {G : Type u} [inst : AddGro
up G] (B : AddGroupFilterBasis G), IsTopologicalAddGroup G
-/
instance instIsTopologicalAddGroup : IsTopologicalAddGroup 𝓢(E, F) :=
  (schwartzSeminormFamily ℝ E F).addGroupFilterBasis.isTopologicalAddGroup
/-
**SchwartzMap.instUniformSpace** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
形式化陈述：instUniformSpace : UniformSpace 𝓢(E, F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instUniformSpace : UniformSpace 𝓢(E, F) :=
  fast_instance% (schwartzSeminormFamily ℝ E F).addGroupFilterBasis.uniformSpace
/-
**SchwartzMap.instIsUniformAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
形式化陈述：instIsUniformAddGroup : IsUniformAddGroup 𝓢(E, F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddGroupFilterBasis.isUniformAddGroup`：∀ {G : Type u_1} [inst : AddCommG
roup G] (B : AddGroupFilterBasis G), IsUniformAddGroup G
-/
instance instIsUniformAddGroup : IsUniformAddGroup 𝓢(E, F) :=
  (schwartzSeminormFamily ℝ E F).addGroupFilterBasis.isUniformAddGroup
/-
**SchwartzMap.instLocallyConvexSpace** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
形式化陈述：instLocallyConvexSpace : LocallyConvexSpace Real 𝓢(E, F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `WithSeminorms.toLocallyConvexSpace`：WithSeminorms.toLocallyConvexSpace {
p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p) : LocallyConvexSpace Real E
· 使用定理 `schwartz_withSeminorms`：∀ (𝕜 : Type u_2) (E : Type u_5) (F : Type u_6) [
inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCom
mGroup F] [i…
-/
instance instLocallyConvexSpace : LocallyConvexSpace ℝ 𝓢(E, F) :=
  (schwartz_withSeminorms ℝ E F).toLocallyConvexSpace
/-
**SchwartzMap.instFirstCountableTopology** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`
。
形式化陈述：instFirstCountableTopology : FirstCountableTopology 𝓢(E, F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `WithSeminorms.firstCountableTopology`：WithSeminorms.firstCountableTopolo
gy (hp : WithSeminorms p) : FirstCountableTopology E
· 使用定理 `instCountableProd`：∀ {α : Type u} {β : Type v} [Countable α] [Countable 
β], Countable (α × β)
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `schwartz_withSeminorms`：∀ (𝕜 : Type u_2) (E : Type u_5) (F : Type u_6) [
inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCom
mGroup F] [i…
-/
instance instFirstCountableTopology : FirstCountableTopology 𝓢(E, F) :=
  (schwartz_withSeminorms ℝ E F).firstCountableTopology

end Topology

@[fun_prop]
/-
**SchwartzMap.hasTemperateGrowth** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：hasTemperateGrowth (f : 𝓢(E, F)) : Function.HasTemperateGrowth f
参数：f : 𝓢(E, F)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.smooth`：smooth (f : 𝓢(E, F)) (n : Nat∞) : ContDiff Real n f
· 使用定理 `SchwartzMap.decay`：decay (f : 𝓢(E, F)) (k n : Nat) : exists C : Real, 0 
< C ∧ forall x, ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖ <= C
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem hasTemperateGrowth (f : 𝓢(E, F)) : Function.HasTemperateGrowth f := by
  refine ⟨smooth f ⊤, fun n => ?_⟩
  rcases f.decay 0 n with ⟨C, Cpos, hC⟩
  exact ⟨0, C, by simpa using hC⟩

section HasCompactSupport

/-- A smooth compactly supported function is a Schwartz function. -/
@[simps]
/-
**SchwartzMap._root_.HasCompactSupport.toSchwartzMap** 是 Mathlib 中的一个定义，位于命名空间 `
SchwartzMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A smooth compactly supported function is a Schwartz function.
-/
def _root_.HasCompactSupport.toSchwartzMap {f : E → F} (h₁ : HasCompactSupport f)
    (h₂ : ContDiff ℝ ∞ f) : 𝓢(E, F) where
  toFun := f
  smooth' := h₂
  decay' k n := by
    set g := fun x ↦ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖
    have hg₁ : Continuous g := by
      apply Continuous.mul (by fun_prop)
      exact (h₂.of_le (mod_cast le_top)).continuous_iteratedFDeriv'.norm
    have hg₂ : HasCompactSupport g := (h₁.iteratedFDeriv _).norm.mul_left
    obtain ⟨x₀, hx₀⟩ := hg₁.exists_forall_ge_of_hasCompactSupport hg₂
    exact ⟨g x₀, hx₀⟩

end HasCompactSupport

section CLM

/-! ### Construction of continuous linear maps between Schwartz spaces -/


variable [NormedField 𝕜] [NormedField 𝕜']
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedSpace 𝕜 E] [SMulCommClass ℝ 𝕜 E]
variable [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace 𝕜' G] [SMulCommClass ℝ 𝕜' G]
variable {σ : 𝕜 →+* 𝕜'}

/-- Create a semilinear map between Schwartz spaces.

Note: This is a helper definition for `mkCLM`. -/
/-
**SchwartzMap.mkLM** 是 Mathlib 中的一个定义，位于命名空间 `SchwartzMap`。
形式化陈述：mkLM (A : 𝓢(D, E) -> F -> G) (hadd : forall (f g : 𝓢(D, E)) (x), A (f + g)
 x = A f x + A g x) (hsmul : forall (a : 𝕜) (f : 𝓢(D, E)) (x), A (a • f) x = σ a
 • A f x) (hsmooth : forall f : 𝓢(D, E), ContDiff Real ∞ (A f)) (hbound : forall
 n : Nat × Nat, exists (s : Finset (Nat × Nat)) (C : Real), 0 <= C ∧ forall (f :
 𝓢(D, E)) (x : F), ‖x‖ ^ n.fst * ‖iteratedFDeriv Real n.snd (A f) x‖ <= C * s.su
p (schwartzSeminormFamily 𝕜 D E) f) : 𝓢(D, E) ->ₛₗ[σ] 𝓢(F, G) where toFun f
参数：A : 𝓢(D, E) -> F -> G；hadd : forall (f g : 𝓢(D, E)) (x), A (f + g) x = A f x 
+ A g x；hsmul : forall (a : 𝕜) (f : 𝓢(D, E)) (x), A (a • f) x = σ a • A f x；hsmo
oth : forall f : 𝓢(D, E), ContDiff Real ∞ (A f)；hbound : forall n : Nat × Nat, e
xists (s : Finset (Nat × Nat)) (C : Real), 0 <= C ∧ forall (f : 𝓢(D, E)) (x : F)
, ‖x‖ ^ n.fst * ‖iteratedFDeriv Real n.snd (A f) x‖ <= C * s.sup (schwartzSemino
rmFamily 𝕜 D E) f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Create a semilinear map between Schwartz spaces.

Note: This is a helper definition for `mkCLM`.
-/
def mkLM (A : 𝓢(D, E) → F → G) (hadd : ∀ (f g : 𝓢(D, E)) (x), A (f + g) x = A f x + A g x)
    (hsmul : ∀ (a : 𝕜) (f : 𝓢(D, E)) (x), A (a • f) x = σ a • A f x)
    (hsmooth : ∀ f : 𝓢(D, E), ContDiff ℝ ∞ (A f))
    (hbound : ∀ n : ℕ × ℕ, ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : 𝓢(D, E)) (x : F),
      ‖x‖ ^ n.fst * ‖iteratedFDeriv ℝ n.snd (A f) x‖ ≤ C * s.sup (schwartzSeminormFamily 𝕜 D E) f) :
    𝓢(D, E) →ₛₗ[σ] 𝓢(F, G) where
  toFun f :=
    { toFun := A f
      smooth' := hsmooth f
      decay' := by
        intro k n
        rcases hbound ⟨k, n⟩ with ⟨s, C, _, h⟩
        exact ⟨C * (s.sup (schwartzSeminormFamily 𝕜 D E)) f, h f⟩ }
  map_add' f g := ext (hadd f g)
  map_smul' a f := ext (hsmul a f)

/-- Create a continuous semilinear map between Schwartz spaces.

For an example of using this definition, see `fderivCLM`. -/
/-
**SchwartzMap.mkCLM** 是 Mathlib 中的一个定义，位于命名空间 `SchwartzMap`。
形式化陈述：mkCLM [RingHomIsometric σ] (A : 𝓢(D, E) -> F -> G) (hadd : forall (f g : 𝓢
(D, E)) (x), A (f + g) x = A f x + A g x) (hsmul : forall (a : 𝕜) (f : 𝓢(D, E)) 
(x), A (a • f) x = σ a • A f x) (hsmooth : forall f : 𝓢(D, E), ContDiff Real ∞ (
A f)) (hbound : forall n : Nat × Nat, exists (s : Finset (Nat × Nat)) (C : Real)
, 0 <= C ∧ forall (f : 𝓢(D, E)) (x : F), ‖x‖ ^ n.fst * ‖iteratedFDeriv Real n.sn
d (A f) x‖ <= C * s.sup (schwartzSeminormFamily 𝕜 D E) f) : 𝓢(D, E) ->SL[σ] 𝓢(F,
 G) where cont
参数：A : 𝓢(D, E) -> F -> G；hadd : forall (f g : 𝓢(D, E)) (x), A (f + g) x = A f x 
+ A g x；hsmul : forall (a : 𝕜) (f : 𝓢(D, E)) (x), A (a • f) x = σ a • A f x；hsmo
oth : forall f : 𝓢(D, E), ContDiff Real ∞ (A f)；hbound : forall n : Nat × Nat, e
xists (s : Finset (Nat × Nat)) (C : Real), 0 <= C ∧ forall (f : 𝓢(D, E)) (x : F)
, ‖x‖ ^ n.fst * ‖iteratedFDeriv Real n.snd (A f) x‖ <= C * s.sup (schwartzSemino
rmFamily 𝕜 D E) f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Create a continuous semilinear map between Schwartz spaces.

For an example of using this definition, see `fderivCLM`.
-/
def mkCLM [RingHomIsometric σ] (A : 𝓢(D, E) → F → G)
    (hadd : ∀ (f g : 𝓢(D, E)) (x), A (f + g) x = A f x + A g x)
    (hsmul : ∀ (a : 𝕜) (f : 𝓢(D, E)) (x), A (a • f) x = σ a • A f x)
    (hsmooth : ∀ f : 𝓢(D, E), ContDiff ℝ ∞ (A f))
    (hbound : ∀ n : ℕ × ℕ, ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : 𝓢(D, E)) (x : F),
      ‖x‖ ^ n.fst * ‖iteratedFDeriv ℝ n.snd (A f) x‖ ≤ C * s.sup (schwartzSeminormFamily 𝕜 D E) f) :
    𝓢(D, E) →SL[σ] 𝓢(F, G) where
  cont := by
    change Continuous (mkLM A hadd hsmul hsmooth hbound : 𝓢(D, E) →ₛₗ[σ] 𝓢(F, G))
    refine
      WithSeminorms.continuous_of_isBounded (schwartz_withSeminorms 𝕜 D E)
        (schwartz_withSeminorms 𝕜' F G) _ fun n => ?_
    rcases hbound n with ⟨s, C, hC, h⟩
    refine ⟨s, ⟨C, hC⟩, fun f => ?_⟩
    exact (mkLM A hadd hsmul hsmooth hbound f).seminorm_le_bound 𝕜' n.1 n.2 (by positivity) (h f)
  toLinearMap := mkLM A hadd hsmul hsmooth hbound

/-- Define a continuous semilinear map from Schwartz space to a normed space. -/
/-
**SchwartzMap.mkCLMtoNormedSpace** 是 Mathlib 中的一个定义，位于命名空间 `SchwartzMap`。
形式化陈述：mkCLMtoNormedSpace [RingHomIsometric σ] (A : 𝓢(D, E) -> G) (hadd : forall 
(f g : 𝓢(D, E)), A (f + g) = A f + A g) (hsmul : forall (a : 𝕜) (f : 𝓢(D, E)), A
 (a • f) = σ a • A f) (hbound : exists (s : Finset (Nat × Nat)) (C : Real), 0 <=
 C ∧ forall (f : 𝓢(D, E)), ‖A f‖ <= C * s.sup (schwartzSeminormFamily 𝕜 D E) f) 
: 𝓢(D, E) ->SL[σ] G
参数：A : 𝓢(D, E) -> G；hadd : forall (f g : 𝓢(D, E)), A (f + g) = A f + A g；hsmul :
 forall (a : 𝕜) (f : 𝓢(D, E)), A (a • f) = σ a • A f；hbound : exists (s : Finset
 (Nat × Nat)) (C : Real), 0 <= C ∧ forall (f : 𝓢(D, E)), ‖A f‖ <= C * s.sup (sch
wartzSeminormFamily 𝕜 D E) f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define a continuous semilinear map from Schwartz space to a normed space.
-/
def mkCLMtoNormedSpace [RingHomIsometric σ] (A : 𝓢(D, E) → G)
    (hadd : ∀ (f g : 𝓢(D, E)), A (f + g) = A f + A g)
    (hsmul : ∀ (a : 𝕜) (f : 𝓢(D, E)), A (a • f) = σ a • A f)
    (hbound : ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : 𝓢(D, E)),
      ‖A f‖ ≤ C * s.sup (schwartzSeminormFamily 𝕜 D E) f) :
    𝓢(D, E) →SL[σ] G :=
  letI f : 𝓢(D, E) →ₛₗ[σ] G :=
    { toFun := (A ·)
      map_add' := hadd
      map_smul' := hsmul }
  { toLinearMap := f
    cont := by
      change Continuous (LinearMap.mk _ _)
      apply WithSeminorms.continuous_normedSpace_rng G (schwartz_withSeminorms 𝕜 D E)
      rcases hbound with ⟨s, C, hC, h⟩
      exact ⟨s, ⟨C, hC⟩, h⟩ }

end CLM

section EvalCLM

variable [NormedField 𝕜]
variable [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace 𝕜 G] [SMulCommClass ℝ 𝕜 G]

variable (𝕜 E G) in
/-- The map applying a vector to Hom-valued Schwartz function as a continuous linear map. -/
/-
**SchwartzMap.evalCLM** 是 Mathlib 中的一个定义，位于命名空间 `SchwartzMap`。
形式化陈述：(𝕜 : Type u_2) →   (E : Type u_5) →     {F : Type u_6} →       (G : Type u
_7) →         [inst : NormedAddCommGroup E] →           [inst_1 : NormedSpace ℝ 
E] →             [inst_2 : NormedAddCommGroup F] →               [inst_3 : Norme
dSpace ℝ F] →                 [inst_4 : NormedField 𝕜] →                   [inst
_5 : NormedAddCommGroup G] →                     [inst_6 : NormedSpace ℝ G] →   
                    [inst_7 : NormedSpace 𝕜 G] →                         [inst_8
 : SMulCommClass ℝ 𝕜 G] → F → SchwartzMap E (F →L[ℝ] G) →L[𝕜] SchwartzMap E G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map applying a vector to Hom-valued Schwartz function as a continuous linear
 map.
-/
protected def evalCLM (m : F) : 𝓢(E, F →L[ℝ] G) →L[𝕜] 𝓢(E, G) :=
  mkCLM (fun f x => f x m) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun f => ContDiff.clm_apply f.2 contDiff_const) <| by
  rintro ⟨k, n⟩
  use {(k, n)}, ‖m‖, norm_nonneg _
  intro f x
  simp only [Finset.sup_singleton, schwartzSeminormFamily_apply]
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (f · m) x‖ ≤ ‖x‖ ^ k * (‖m‖ * ‖iteratedFDeriv ℝ n f x‖) := by
      gcongr
      exact norm_iteratedFDeriv_clm_apply_const (f.smooth _).contDiffAt le_rfl
    _ ≤ ‖m‖ * SchwartzMap.seminorm 𝕜 k n f := by
      move_mul [‖m‖]
      gcongr
      apply le_seminorm

@[simp]
/-
**SchwartzMap.evalCLM_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：evalCLM_apply_apply (f : 𝓢(E, F ->L[Real] G)) (m : F) (x : E) : SchwartzMa
p.evalCLM 𝕜 E G m f x = f x m
参数：f : 𝓢(E, F ->L[Real] G)；m : F；x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem evalCLM_apply_apply (f : 𝓢(E, F →L[ℝ] G)) (m : F) (x : E) :
    SchwartzMap.evalCLM 𝕜 E G m f x = f x m := rfl

end EvalCLM

section Multiplication

variable [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedSpace 𝕜 F]

section bilin

variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 G]

/-- The map `f ↦ (x ↦ B (f x) (g x))` as a continuous `𝕜`-linear map on Schwartz space,
where `B` is a continuous `𝕜`-linear map and `g` is a function of temperate growth. -/
/-
**SchwartzMap.bilinLeftCLM** 是 Mathlib 中的一个定义，位于命名空间 `SchwartzMap`。
形式化陈述：bilinLeftCLM (B : E ->L[𝕜] F ->L[𝕜] G) {g : D -> F} (hg : g.HasTemperateGr
owth) : 𝓢(D, E) ->L[𝕜] 𝓢(D, G)
参数：B : E ->L[𝕜] F ->L[𝕜] G；hg : g.HasTemperateGrowth。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `f ↦ (x ↦ B (f x) (g x))` as a continuous `𝕜`-linear map on Schwartz spa
ce,
where `B` is a continuous `𝕜`-linear map and `g` is a function of temperate grow
th.
-/
def bilinLeftCLM (B : E →L[𝕜] F →L[𝕜] G) {g : D → F} (hg : g.HasTemperateGrowth) :
    𝓢(D, E) →L[𝕜] 𝓢(D, G) :=
  mkCLM (fun f x => B (f x) (g x))
    (fun _ _ _ => by simp) (fun _ _ _ => by simp)
    (fun f => (B.bilinearRestrictScalars ℝ).isBoundedBilinearMap.contDiff.comp
      ((f.smooth ⊤).prodMk hg.1)) <| by
  rintro ⟨k, n⟩
  rcases hg.norm_iteratedFDeriv_le_uniform n with ⟨l, C, hC, hgrowth⟩
  use
    Finset.Iic (l + k, n), ‖B‖ * ((n : ℝ) + (1 : ℝ)) * n.choose (n / 2) * (C * 2 ^ (l + k)),
    by positivity
  intro f x
  have hxk : 0 ≤ ‖x‖ ^ k := by positivity
  simp_rw [← ContinuousLinearMap.bilinearRestrictScalars_apply_apply ℝ B]
  have hnorm_mul :=
    ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear (B.bilinearRestrictScalars ℝ)
    (f.smooth ⊤) hg.1 x (n := n) (mod_cast le_top)
  grw [hnorm_mul]
  rw [ContinuousLinearMap.norm_bilinearRestrictScalars]
  move_mul [‖B‖, ‖B‖]
  gcongr ?_ * _
  rw [Finset.mul_sum]
  have : (∑ _x ∈ Finset.range (n + 1), (1 : ℝ)) = n + 1 := by simp
  simp_rw [mul_assoc ((n : ℝ) + 1)]
  rw [← this, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  simp only [one_mul]
  move_mul [(Nat.choose n i : ℝ), (Nat.choose n (n / 2) : ℝ)]
  gcongr ?_ * ?_
  swap
  · norm_cast
    exact i.choose_le_middle n
  specialize hgrowth (n - i) (by simp only [tsub_le_self]) x
  grw [hgrowth]
  move_mul [C]
  gcongr ?_ * C
  rw [Finset.mem_range_succ_iff] at hi
  change i ≤ (l + k, n).snd at hi
  refine le_trans ?_ (one_add_le_sup_seminorm_apply le_rfl hi f x)
  rw [pow_add]
  move_mul [(1 + ‖x‖) ^ l]
  gcongr
  simp

@[simp]
/-
**SchwartzMap.bilinLeftCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：bilinLeftCLM_apply (B : E ->L[𝕜] F ->L[𝕜] G) {g : D -> F} (hg : g.HasTempe
rateGrowth) (f : 𝓢(D, E)) : bilinLeftCLM B hg f = fun x => B (f x) (g x)
参数：B : E ->L[𝕜] F ->L[𝕜] G；hg : g.HasTemperateGrowth；f : 𝓢(D, E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
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
-/
theorem bilinLeftCLM_apply (B : E →L[𝕜] F →L[𝕜] G) {g : D → F} (hg : g.HasTemperateGrowth)
    (f : 𝓢(D, E)) : bilinLeftCLM B hg f = fun x => B (f x) (g x) := rfl

end bilin

section smul

variable (F) in
open scoped Classical in
/-- The map `f ↦ (x ↦ g x • f x)` as a continuous `𝕜`-linear map on Schwartz space,
where `g` is a function of temperate growth. -/
/-
**SchwartzMap.smulLeftCLM** 是 Mathlib 中的一个定义，位于命名空间 `SchwartzMap`。
形式化陈述：smulLeftCLM (g : E -> 𝕜) : 𝓢(E, F) ->L[𝕜] 𝓢(E, F)
参数：g : E -> 𝕜。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `f ↦ (x ↦ g x • f x)` as a continuous `𝕜`-linear map on Schwartz space,
where `g` is a function of temperate growth.
-/
def smulLeftCLM (g : E → 𝕜) : 𝓢(E, F) →L[𝕜] 𝓢(E, F) :=
  if hg : g.HasTemperateGrowth then
    SchwartzMap.bilinLeftCLM (ContinuousLinearMap.lsmul 𝕜 𝕜).flip hg
  else 0
/-
**SchwartzMap.smulLeftCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：smulLeftCLM_apply {g : E -> 𝕜} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) :
 smulLeftCLM F g f = fun x => g x • f x
参数：hg : g.HasTemperateGrowth；f : 𝓢(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smulLeftCLM_apply {g : E → 𝕜} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) :
    smulLeftCLM F g f = fun x ↦ g x • f x := by
  simp [smulLeftCLM, hg]

@[simp]
/-
**SchwartzMap.smulLeftCLM_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：smulLeftCLM_apply_apply {g : E -> 𝕜} (hg : g.HasTemperateGrowth) (f : 𝓢(E,
 F)) (x : E) : smulLeftCLM F g f x = g x • f x
参数：hg : g.HasTemperateGrowth；f : 𝓢(E, F)；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `SchwartzMap.smulLeftCLM_apply`：smulLeftCLM_apply {g : E -> 𝕜} (hg : g.Ha
sTemperateGrowth) (f : 𝓢(E, F)) : smulLeftCLM F g f = fun x => g x • f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smulLeftCLM_apply_apply {g : E → 𝕜} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) (x : E) :
    smulLeftCLM F g f x = g x • f x := by
  simp [smulLeftCLM_apply hg]

@[simp]
/-
**SchwartzMap.smulLeftCLM_const** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：smulLeftCLM_const (c : 𝕜) : smulLeftCLM F (fun (_ : E) => c) = c • Continu
ousLinearMap.id 𝕜 _
参数：c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
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
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `SchwartzMap.ext`：ext {f g : 𝓢(E, F)} (h : forall x, (f : E -> F) x = g x
) : f = g
· 使用定理 `Function.HasTemperateGrowth.const`：∀ {E : Type u_5} {F : Type u_6} [inst
 : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup
 F]   [inst_3 : NormedS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SchwartzMap.smulLeftCLM_apply_apply`：smulLeftCLM_apply_apply {g : E -> 𝕜
} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) (x : E) : smulLeftCLM F g f x = g x 
• f x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `SchwartzMap.instIsSMulApply`：∀ {𝕜 : Type u_2} {E : Type u_5} {F : Type u
_6} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedA
ddCommGroup F] [i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smulLeftCLM_const (c : 𝕜) :
    smulLeftCLM F (fun (_ : E) ↦ c) = c • ContinuousLinearMap.id 𝕜 _ := by
  ext f x
  have : (fun (_ : E) ↦ c).HasTemperateGrowth := by fun_prop
  simp [this]

@[simp]
/-
**SchwartzMap.smulLeftCLM_smulLeftCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzM
ap`。
形式化陈述：smulLeftCLM_smulLeftCLM_apply {g₁ g₂ : E -> 𝕜} (hg₁ : g₁.HasTemperateGrowt
h) (hg₂ : g₂.HasTemperateGrowth) (f : 𝓢(E, F)) : smulLeftCLM F g₁ (smulLeftCLM F
 g₂ f) = smulLeftCLM F (g₁ * g₂) f
参数：hg₁ : g₁.HasTemperateGrowth；hg₂ : g₂.HasTemperateGrowth；f : 𝓢(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.ext`：ext {f g : 𝓢(E, F)} (h : forall x, (f : E -> F) x = g x
) : f = g
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SchwartzMap.smulLeftCLM_apply_apply`：smulLeftCLM_apply_apply {g : E -> 𝕜
} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) (x : E) : smulLeftCLM F g f x = g x 
• f x
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Function.HasTemperateGrowth.mul`：∀ {R : Type u_3} {E : Type u_5} [inst :
 NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedRing R]   [ins
t_3 : NormedAlgebra ℝ…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smulLeftCLM_smulLeftCLM_apply {g₁ g₂ : E → 𝕜} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) (f : 𝓢(E, F)) :
    smulLeftCLM F g₁ (smulLeftCLM F g₂ f) = smulLeftCLM F (g₁ * g₂) f := by
  ext x
  simp [smul_smul, hg₁, hg₂, hg₁.mul hg₂]
/-
**SchwartzMap.smulLeftCLM_compL_smulLeftCLM** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzM
ap`。
形式化陈述：smulLeftCLM_compL_smulLeftCLM {g₁ g₂ : E -> 𝕜} (hg₁ : g₁.HasTemperateGrowt
h) (hg₂ : g₂.HasTemperateGrowth) : smulLeftCLM F g₁ ∘L smulLeftCLM F g₂ = smulLe
ftCLM F (g₁ * g₂)
参数：hg₁ : g₁.HasTemperateGrowth；hg₂ : g₂.HasTemperateGrowth。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
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
· 使用定理 `SchwartzMap.smulLeftCLM_smulLeftCLM_apply`：smulLeftCLM_smulLeftCLM_apply
 {g₁ g₂ : E -> 𝕜} (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) (f
 : 𝓢(E, F)) : smulLeftCLM F g₁ …
-/
theorem smulLeftCLM_compL_smulLeftCLM {g₁ g₂ : E → 𝕜} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) :
    smulLeftCLM F g₁ ∘L smulLeftCLM F g₂ = smulLeftCLM F (g₁ * g₂) := by
  ext1 f
  exact smulLeftCLM_smulLeftCLM_apply hg₁ hg₂ f
/-
**SchwartzMap.smulLeftCLM_smul** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：smulLeftCLM_smul {g : E -> 𝕜} (hg : g.HasTemperateGrowth) (c : 𝕜) : smulLe
ftCLM F (c • g) = c • smulLeftCLM F g
参数：hg : g.HasTemperateGrowth；c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.HasTemperateGrowth.const`：∀ {E : Type u_5} {F : Type u_6} [inst
 : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup
 F]   [inst_3 : NormedS…
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
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `SchwartzMap.smulLeftCLM_const`：smulLeftCLM_const (c : 𝕜) : smulLeftCLM F
 (fun (_ : E) => c) = c • ContinuousLinearMap.id 𝕜 _
· 使用定理 `ContinuousLinearMap.id_comp`：id_comp (f : M₁ ->SL[σ₁₂] M₂) : .id R₂ M₂ ∘
SL f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SchwartzMap.smulLeftCLM_compL_smulLeftCLM`：smulLeftCLM_compL_smulLeftCLM
 {g₁ g₂ : E -> 𝕜} (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) : 
smulLeftCLM F g₁ ∘L smulLeftCLM…
-/
theorem smulLeftCLM_smul {g : E → 𝕜} (hg : g.HasTemperateGrowth) (c : 𝕜) :
    smulLeftCLM F (c • g) = c • smulLeftCLM F g := by
  have : (fun (_ : E) ↦ c).HasTemperateGrowth := by fun_prop
  convert! (smulLeftCLM_compL_smulLeftCLM this hg).symm using 1
  simp
/-
**SchwartzMap.smulLeftCLM_add** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：smulLeftCLM_add {g₁ g₂ : E -> 𝕜} (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.H
asTemperateGrowth) : smulLeftCLM F (g₁ + g₂) = smulLeftCLM F g₁ + smulLeftCLM F 
g₂
参数：hg₁ : g₁.HasTemperateGrowth；hg₂ : g₂.HasTemperateGrowth。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
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
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SchwartzMap.ext`：ext {f g : 𝓢(E, F)} (h : forall x, (f : E -> F) x = g x
) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SchwartzMap.smulLeftCLM_apply_apply`：smulLeftCLM_apply_apply {g : E -> 𝕜
} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) (x : E) : smulLeftCLM F g f x = g x 
• f x
· 使用定理 `Function.HasTemperateGrowth.add`：∀ {E : Type u_5} {F : Type u_6} [inst :
 NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F
]   [inst_3 : NormedS…
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `SchwartzMap.instIsAddApply`：∀ {E : Type u_5} {F : Type u_6} [inst : Norm
edAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [
inst_3 : NormedS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smulLeftCLM_add {g₁ g₂ : E → 𝕜} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) :
    smulLeftCLM F (g₁ + g₂) = smulLeftCLM F g₁ + smulLeftCLM F g₂ := by
  ext f x
  simp [hg₁, hg₂, hg₁.add hg₂, add_smul]
/-
**SchwartzMap.smulLeftCLM_sub** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：smulLeftCLM_sub {g₁ g₂ : E -> 𝕜} (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.H
asTemperateGrowth) : smulLeftCLM F (g₁ - g₂) = smulLeftCLM F g₁ - smulLeftCLM F 
g₂
参数：hg₁ : g₁.HasTemperateGrowth；hg₂ : g₂.HasTemperateGrowth。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
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
· 使用定理 `SchwartzMap.ext`：ext {f g : 𝓢(E, F)} (h : forall x, (f : E -> F) x = g x
) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SchwartzMap.smulLeftCLM_apply_apply`：smulLeftCLM_apply_apply {g : E -> 𝕜
} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) (x : E) : smulLeftCLM F g f x = g x 
• f x
· 使用定理 `Function.HasTemperateGrowth.sub`：∀ {E : Type u_5} {F : Type u_6} [inst :
 NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F
]   [inst_3 : NormedS…
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Sub β}   {inst_2 : Sub F} [self : IsSu…
· 使用定理 `ContinuousLinearMap.instIsSubApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `SchwartzMap.instIsSubApply`：∀ {E : Type u_5} {F : Type u_6} [inst : Norm
edAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [
inst_3 : NormedS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smulLeftCLM_sub {g₁ g₂ : E → 𝕜} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) :
    smulLeftCLM F (g₁ - g₂) = smulLeftCLM F g₁ - smulLeftCLM F g₂ := by
  ext f x
  simp [hg₁, hg₂, hg₁.sub hg₂, sub_smul]
/-
**SchwartzMap.smulLeftCLM_neg** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：smulLeftCLM_neg {g : E -> 𝕜} (hg : g.HasTemperateGrowth) : smulLeftCLM F (
-g) = -smulLeftCLM F g
参数：hg : g.HasTemperateGrowth。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
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
· 使用定理 `SchwartzMap.ext`：ext {f g : 𝓢(E, F)} (h : forall x, (f : E -> F) x = g x
) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SchwartzMap.smulLeftCLM_apply_apply`：smulLeftCLM_apply_apply {g : E -> 𝕜
} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) (x : E) : smulLeftCLM F g f x = g x 
• f x
· 使用定理 `Function.HasTemperateGrowth.neg`：∀ {E : Type u_5} {F : Type u_6} [inst :
 NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F
]   [inst_3 : NormedS…
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `SchwartzMap.instIsNegApply`：∀ {E : Type u_5} {F : Type u_6} [inst : Norm
edAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [
inst_3 : NormedS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smulLeftCLM_neg {g : E → 𝕜} (hg : g.HasTemperateGrowth) :
    smulLeftCLM F (-g) = -smulLeftCLM F g := by
  ext f x
  simp [hg, hg.neg, neg_smul]
/-
**SchwartzMap.smulLeftCLM_fun_neg** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：smulLeftCLM_fun_neg {g : E -> 𝕜} (hg : g.HasTemperateGrowth) : smulLeftCLM
 F (fun x => -g x) = -smulLeftCLM F g
参数：hg : g.HasTemperateGrowth。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.smulLeftCLM_neg`：smulLeftCLM_neg {g : E -> 𝕜} (hg : g.HasTem
perateGrowth) : smulLeftCLM F (-g) = -smulLeftCLM F g
-/
theorem smulLeftCLM_fun_neg {g : E → 𝕜} (hg : g.HasTemperateGrowth) :
    smulLeftCLM F (fun x ↦ -g x) = -smulLeftCLM F g :=
  smulLeftCLM_neg hg
/-
**SchwartzMap.smulLeftCLM_sum** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：smulLeftCLM_sum {g : ι -> E -> 𝕜} {s : Finset ι} (hg : forall i in s, (g i
).HasTemperateGrowth) : smulLeftCLM F (fun x => ∑ i in s, g i x) = ∑ i in s, smu
lLeftCLM F (g i)
参数：hg : forall i in s, (g i).HasTemperateGrowth。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
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
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SchwartzMap.ext`：ext {f g : 𝓢(E, F)} (h : forall x, (f : E -> F) x = g x
) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SchwartzMap.smulLeftCLM_apply_apply`：smulLeftCLM_apply_apply {g : E -> 𝕜
} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) (x : E) : smulLeftCLM F g f x = g x 
• f x
· 使用定理 `Function.HasTemperateGrowth.sum`：∀ {ι : Type u_1} {E : Type u_5} {F : Ty
pe u_6} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : Nor
medAddCommGroup F] [i…
· 使用定理 `Finset.sum_smul`：Finset.sum_smul {f : ι -> R} {s : Finset ι} {x : M} : (
∑ i in s, f i) • x = ∑ i in s, f i • x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `SchwartzMap.instIsZeroApply`：∀ {E : Type u_5} {F : Type u_6} [inst : Nor
medAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   
[inst_3 : NormedS…
· 使用定理 `SchwartzMap.instIsAddApply`：∀ {E : Type u_5} {F : Type u_6} [inst : Norm
edAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [
inst_3 : NormedS…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smulLeftCLM_sum {g : ι → E → 𝕜} {s : Finset ι} (hg : ∀ i ∈ s, (g i).HasTemperateGrowth) :
    smulLeftCLM F (fun x ↦ ∑ i ∈ s, g i x) = ∑ i ∈ s, smulLeftCLM F (g i) := by
  ext f x
  simp +contextual [Function.HasTemperateGrowth.sum hg, Finset.sum_smul, hg]

variable {𝕜' : Type*} [RCLike 𝕜'] [NormedSpace 𝕜' F]

variable (𝕜') in
/-
**SchwartzMap.smulLeftCLM_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：smulLeftCLM_ofReal {g : E -> Real} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F
)) : smulLeftCLM F (fun x => RCLike.ofReal (K
参数：hg : g.HasTemperateGrowth；f : 𝓢(E, F)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.ext`：ext {f g : 𝓢(E, F)} (h : forall x, (f : E -> F) x = g x
) : f = g
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SchwartzMap.smulLeftCLM_apply_apply`：smulLeftCLM_apply_apply {g : E -> 𝕜
} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) (x : E) : smulLeftCLM F g f x = g x 
• f x
· 使用定理 `Function.HasTemperateGrowth.comp`：∀ {D : Type u_4} {E : Type u_5} {F : T
ype u_6} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : No
rmedAddCommGroup F] [i…
· 使用定理 `Function.RCLike.hasTemperateGrowth_ofReal`：∀ (𝕜 : Type u_2) [inst : RCLi
ke 𝕜], Function.HasTemperateGrowth RCLike.ofReal
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
-/
theorem smulLeftCLM_ofReal {g : E → ℝ} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) :
    smulLeftCLM F (fun x ↦ RCLike.ofReal (K := 𝕜') (g x)) f = smulLeftCLM F g f := by
  ext x
  rw [smulLeftCLM_apply_apply (by fun_prop), smulLeftCLM_apply_apply (by fun_prop),
    algebraMap_smul]
/-
**SchwartzMap.smulLeftCLM_real_smul** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：smulLeftCLM_real_smul {g : E -> 𝕜'} (hg : g.HasTemperateGrowth) (c : Real)
 : smulLeftCLM F (c • g) = c • smulLeftCLM F g
参数：hg : g.HasTemperateGrowth；c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.real_smul_eq_coe_smul`：real_smul_eq_coe_smul [AddCommGroup E] [Mo
dule K E] [Module Real E] [IsScalarTower Real K E] (r : Real) (x : E) : r • x = 
(r : K) • x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `SchwartzMap.smulLeftCLM_smul`：smulLeftCLM_smul {g : E -> 𝕜} (hg : g.HasT
emperateGrowth) (c : 𝕜) : smulLeftCLM F (c • g) = c • smulLeftCLM F g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem smulLeftCLM_real_smul {g : E → 𝕜'} (hg : g.HasTemperateGrowth) (c : ℝ) :
    smulLeftCLM F (c • g) = c • smulLeftCLM F g := by
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜') c, smulLeftCLM_smul hg,
    ← RCLike.real_smul_eq_coe_smul c]
/-
**SchwartzMap.tsupport_smulLeftCLM_subset** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap
`。
形式化陈述：tsupport_smulLeftCLM_subset (g : E -> 𝕜) (f : 𝓢(E, F)) : tsupport (smulLef
tCLM F g f) subseteq tsupport f inter tsupport g
参数：g : E -> 𝕜；f : 𝓢(E, F)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SchwartzMap.smulLeftCLM_apply`：smulLeftCLM_apply {g : E -> 𝕜} (hg : g.Ha
sTemperateGrowth) (f : 𝓢(E, F)) : smulLeftCLM F g f = fun x => g x • f x
· 使用定理 `tsupport_smul_subset_right`：tsupport_smul_subset_right {M α} [Zero α] [S
MulZeroClass M α] (f : X -> M) (g : X -> α) : (tsupport fun x => f x • g x) subs
eteq tsupport g
· 使用定理 `tsupport_smul_subset_left`：tsupport_smul_subset_left {M α} [Zero M] [Zer
o α] [SMulWithZero M α] (f : X -> M) (g : X -> α) : (tsupport fun x => f x • g x
) subseteq tsup…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `FunLike.coe_zero`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst :
 FunLike F α β] [inst_1 : Zero F] [inst_2 : Zero β]   [IsZeroApply F α β], ⇑0 = 
0
· 使用定理 `SchwartzMap.instIsZeroApply`：∀ {E : Type u_5} {F : Type u_6} [inst : Nor
medAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   
[inst_3 : NormedS…
· 使用定理 `tsupport_zero`：∀ {X : Type u_1} {α : Type u_2} [inst : Zero α] [inst_1 :
 TopologicalSpace X], tsupport 0 = ∅
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem tsupport_smulLeftCLM_subset (g : E → 𝕜) (f : 𝓢(E, F)) :
    tsupport (smulLeftCLM F g f) ⊆ tsupport f ∩ tsupport g := by
  by_cases hg : g.HasTemperateGrowth
  · simpa [smulLeftCLM_apply hg] using
      ⟨tsupport_smul_subset_right g f, tsupport_smul_subset_left g f⟩
  · simp [smulLeftCLM, hg, FunLike.coe_zero]

end smul

section pairing

variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 G]

/-- The bilinear pairing of Schwartz functions.

The continuity in the left argument is provided in `SchwartzMap.pairing_continuous_left`. -/
/-
**SchwartzMap.pairing** 是 Mathlib 中的一个定义，位于命名空间 `SchwartzMap`。
形式化陈述：pairing (B : E ->L[𝕜] F ->L[𝕜] G) : 𝓢(D, E) ->ₗ[𝕜] 𝓢(D, F) ->L[𝕜] 𝓢(D, G) 
where toFun f
参数：B : E ->L[𝕜] F ->L[𝕜] G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.hasTemperateGrowth`：hasTemperateGrowth (f : 𝓢(E, F)) : Funct
ion.HasTemperateGrowth f

--- 原说明 ---
The bilinear pairing of Schwartz functions.

The continuity in the left argument is provided in `SchwartzMap.pairing_continuo
us_left`.
-/
def pairing (B : E →L[𝕜] F →L[𝕜] G) : 𝓢(D, E) →ₗ[𝕜] 𝓢(D, F) →L[𝕜] 𝓢(D, G) where
  toFun f := bilinLeftCLM B.flip f.hasTemperateGrowth
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
/-
**SchwartzMap.pairing_apply** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：pairing_apply (B : E ->L[𝕜] F ->L[𝕜] G) (f : 𝓢(D, E)) (g : 𝓢(D, F)) : pair
ing B f g = fun x => B (f x) (g x)
参数：B : E ->L[𝕜] F ->L[𝕜] G；f : 𝓢(D, E)；g : 𝓢(D, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
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
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
-/
theorem pairing_apply (B : E →L[𝕜] F →L[𝕜] G) (f : 𝓢(D, E)) (g : 𝓢(D, F)) :
    pairing B f g = fun x ↦ B (f x) (g x) := rfl

@[simp]
/-
**SchwartzMap.pairing_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：pairing_apply_apply (B : E ->L[𝕜] F ->L[𝕜] G) (f : 𝓢(D, E)) (g : 𝓢(D, F)) 
(x : D) : pairing B f g x = B (f x) (g x)
参数：B : E ->L[𝕜] F ->L[𝕜] G；f : 𝓢(D, E)；g : 𝓢(D, F)；x : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
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
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
-/
theorem pairing_apply_apply (B : E →L[𝕜] F →L[𝕜] G) (f : 𝓢(D, E)) (g : 𝓢(D, F)) (x : D) :
    pairing B f g x = B (f x) (g x) := rfl

/-- The pairing is continuous in the left argument.

Note that since `𝓢(E, F)` is not a normed space, uncurried and curried continuity do not
coincide. -/
/-
**SchwartzMap.pairing_continuous_left** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：pairing_continuous_left (B : E ->L[𝕜] F ->L[𝕜] G) (g : 𝓢(D, F)) : Continuo
us (pairing B · g)
参数：B : E ->L[𝕜] F ->L[𝕜] G；g : 𝓢(D, F)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
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
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…

--- 原说明 ---
The pairing is continuous in the left argument.

Note that since `𝓢(E, F)` is not a normed space, uncurried and curried continuit
y do not
coincide.
-/
theorem pairing_continuous_left (B : E →L[𝕜] F →L[𝕜] G) (g : 𝓢(D, F)) :
    Continuous (pairing B · g) := (pairing B.flip g).continuous

end pairing

open ContinuousLinearMap

variable (𝕜 F) in
/-- Scalar multiplication with a continuous linear map as a continuous linear map on Schwartz
functions. -/
/-
**SchwartzMap.smulRightCLM** 是 Mathlib 中的一个定义，位于命名空间 `SchwartzMap`。
形式化陈述：smulRightCLM (L : E ->L[Real] G ->L[Real] Real) : 𝓢(E, F) ->L[𝕜] 𝓢(E, G ->
L[Real] F)
参数：L : E ->L[Real] G ->L[Real] Real。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ

--- 原说明 ---
Scalar multiplication with a continuous linear map as a continuous linear map on
 Schwartz
functions.
-/
def smulRightCLM (L : E →L[ℝ] G →L[ℝ] ℝ) : 𝓢(E, F) →L[𝕜] 𝓢(E, G →L[ℝ] F) :=
  mkCLM (fun f x ↦ (L x).smulRight (f x)) (by intros; ext; simp)
    (by intro c g x; ext v; simpa using smul_comm (L x v) c (g x))
    (by fun_prop) <| by
      intro ⟨k, n⟩
      use {(k + 1, n), (k, n - 1)}, 2 * ‖L‖ * (max 1 n), by positivity
      intro f x
      calc
        _ ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i) *
            ‖iteratedFDeriv ℝ i L x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖ := by
          gcongr 1
          exact norm_iteratedFDeriv_le_of_bilinear_of_le_one (smulRightL ℝ G F)
            (by fun_prop) (f.smooth ⊤) x (mod_cast le_top) norm_smulRightL_le
        _ ≤ ‖x‖ ^ k *
            (‖L x‖ * ‖iteratedFDeriv ℝ n f x‖ + n * ‖L‖ * ‖iteratedFDeriv ℝ (n - 1) f x‖) := by
          gcongr 1
          rw [Finset.sum_range_succ', add_comm]
          cases n with
          | zero => simp
          | succ n =>
            have : ∑ k ∈ Finset.range n,
                (((n + 1).choose (k + 1 + 1)) : ℝ) * ‖iteratedFDeriv ℝ (k + 1 + 1) L x‖ *
                ‖iteratedFDeriv ℝ (n + 1 - (k + 1 + 1)) f x‖ = 0 := by
              apply Finset.sum_eq_zero
              simp [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_const]
            simp [Finset.sum_range_succ', this]
        _ = ‖x‖ ^ k * ‖L x‖ * ‖iteratedFDeriv ℝ n f x‖ +
              ‖x‖ ^ k * n * ‖L‖ * ‖iteratedFDeriv ℝ (n - 1) f x‖ := by ring
        _ ≤ ‖L‖ * 1 * (SchwartzMap.seminorm 𝕜 (k + 1) n) f +
              ‖L‖ * n * (SchwartzMap.seminorm 𝕜 k (n - 1) f) := by
          grw [le_opNorm, ← le_seminorm 𝕜 (k + 1) n f x, ← le_seminorm 𝕜 k (n - 1) f x]
          apply le_of_eq
          ring
        _ ≤ ‖L‖ * max 1 n *
            max ((SchwartzMap.seminorm 𝕜 (k + 1) n) f) ((SchwartzMap.seminorm 𝕜 k (n - 1)) f) +
            ‖L‖ * max 1 n *
            max ((SchwartzMap.seminorm 𝕜 (k + 1) n) f) ((SchwartzMap.seminorm 𝕜 k (n - 1)) f) := by
          gcongr <;> simp
        _ = _ := by
          simp only [Finset.sup_insert, schwartzSeminormFamily_apply, Finset.sup_singleton,
            Seminorm.coe_sup, Pi.sup_apply]
          ring

@[simp]
/-
**SchwartzMap.smulRightCLM_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：smulRightCLM_apply_apply (L : E ->L[Real] G ->L[Real] Real) (f : 𝓢(E, F)) 
(x : E) : smulRightCLM 𝕜 F L f x = (L x).smulRight (f x)
参数：L : E ->L[Real] G ->L[Real] Real；f : 𝓢(E, F)；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
-/
theorem smulRightCLM_apply_apply (L : E →L[ℝ] G →L[ℝ] ℝ) (f : 𝓢(E, F)) (x : E) :
    smulRightCLM 𝕜 F L f x = (L x).smulRight (f x) := rfl

end Multiplication

section Comp

variable (𝕜)
variable [RCLike 𝕜]
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedSpace 𝕜 F]

/-- Composition with a function on the right is a continuous linear map on Schwartz space
provided that the function is temperate and growths polynomially near infinity. -/
/-
**SchwartzMap.compCLM** 是 Mathlib 中的一个定义，位于命名空间 `SchwartzMap`。
形式化陈述：compCLM {g : D -> E} (hg : g.HasTemperateGrowth) (hg_upper : exists (k : N
at) (C : Real), forall x, ‖x‖ <= C * (1 + ‖g x‖) ^ k) : 𝓢(E, F) ->L[𝕜] 𝓢(D, F)
参数：hg : g.HasTemperateGrowth；hg_upper : exists (k : Nat) (C : Real), forall x, ‖
x‖ <= C * (1 + ‖g x‖) ^ k。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition with a function on the right is a continuous linear map on Schwartz 
space
provided that the function is temperate and growths polynomially near infinity.
-/
def compCLM {g : D → E} (hg : g.HasTemperateGrowth)
    (hg_upper : ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖g x‖) ^ k) : 𝓢(E, F) →L[𝕜] 𝓢(D, F) :=
  mkCLM (fun f => f ∘ g) (fun _ _ _ => by simp) (fun _ _ _ => rfl)
    (fun f => (f.smooth ⊤).comp hg.1) <| by
  rintro ⟨k, n⟩
  rcases hg.norm_iteratedFDeriv_le_uniform n with ⟨l, C, hC, hgrowth⟩
  rcases hg_upper with ⟨kg, Cg, hg_upper'⟩
  have hCg : 1 ≤ 1 + Cg := by
    refine le_add_of_nonneg_right ?_
    specialize hg_upper' 0
    rw [norm_zero] at hg_upper'
    exact nonneg_of_mul_nonneg_left hg_upper' (by positivity)
  let k' := kg * (k + l * n)
  use Finset.Iic (k', n), (1 + Cg) ^ (k + l * n) * ((C + 1) ^ n * n ! * 2 ^ k'), by positivity
  intro f x
  let seminorm_f := ((Finset.Iic (k', n)).sup (schwartzSeminormFamily 𝕜 _ _)) f
  have hg_upper'' : (1 + ‖x‖) ^ (k + l * n) ≤ (1 + Cg) ^ (k + l * n) * (1 + ‖g x‖) ^ k' := by
    rw [pow_mul, ← mul_pow]
    gcongr
    rw [add_mul]
    refine add_le_add ?_ (hg_upper' x)
    nth_rw 1 [← one_mul (1 : ℝ)]
    gcongr
    apply one_le_pow₀
    simp only [le_add_iff_nonneg_right, norm_nonneg]
  have hbound (i) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i f (g x)‖ ≤ 2 ^ k' * seminorm_f / (1 + ‖g x‖) ^ k' := by
    have hpos : 0 < (1 + ‖g x‖) ^ k' := by positivity
    rw [le_div_iff₀' hpos]
    change i ≤ (k', n).snd at hi
    exact one_add_le_sup_seminorm_apply le_rfl hi _ _
  have hgrowth' (N : ℕ) (hN₁ : 1 ≤ N) (hN₂ : N ≤ n) :
      ‖iteratedFDeriv ℝ N g x‖ ≤ ((C + 1) * (1 + ‖x‖) ^ l) ^ N := by
    refine (hgrowth N hN₂ x).trans ?_
    rw [mul_pow]
    have hN₁' := (lt_of_lt_of_le zero_lt_one hN₁).ne'
    gcongr
    · exact le_trans (by simp) (le_self_pow₀ (by simp [hC]) hN₁')
    · refine le_self_pow₀ (one_le_pow₀ ?_) hN₁'
      simp only [le_add_iff_nonneg_right, norm_nonneg]
  have := norm_iteratedFDeriv_comp_le (f.smooth ⊤) hg.1 (mod_cast le_top) x hbound hgrowth'
  have hxk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k :=
    pow_le_pow_left₀ (norm_nonneg _) (by simp only [zero_le_one, le_add_iff_nonneg_left]) _
  grw [hxk, this]
  have rearrange :
    (1 + ‖x‖) ^ k *
        (n ! * (2 ^ k' * seminorm_f / (1 + ‖g x‖) ^ k') * ((C + 1) * (1 + ‖x‖) ^ l) ^ n) =
      (1 + ‖x‖) ^ (k + l * n) / (1 + ‖g x‖) ^ k' *
        ((C + 1) ^ n * n ! * 2 ^ k' * seminorm_f) := by
    rw [mul_pow, pow_add, ← pow_mul]
    ring
  rw [rearrange]
  have hgxk' : 0 < (1 + ‖g x‖) ^ k' := by positivity
  rw [← div_le_iff₀ hgxk'] at hg_upper''
  grw [hg_upper'', ← mul_assoc]
/-
**SchwartzMap.compCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：∀ (𝕜 : Type u_2) {D : Type u_4} {E : Type u_5} {F : Type u_6} [inst : Norm
edAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [
inst_3 : NormedSpace ℝ F] [inst_4 : RCLike 𝕜] [inst_5 : NormedAddCommGroup D]   
[inst_6 : NormedSpace ℝ D] [inst_7 : NormedSpace 𝕜 F] {g : D → E} (hg : Function
.HasTemperateGrowth g)   (hg_upper : ∃ k C, ∀ (x : D), ‖x‖ ≤ C * (1 + ‖g x‖) ^ k
) (f : SchwartzMap E F),   ⇑((SchwartzMap.compCLM 𝕜 hg hg_upper) f) = ⇑f ∘ g
参数：𝕜 : Type u_2；hg : Function.HasTemperateGrowth g；hg_upper : ∃ k C, ∀ (x : D), 
‖x‖ ≤ C * (1 + ‖g x‖) ^ k；f : SchwartzMap E F；(SchwartzMap.compCLM 𝕜 hg hg_upper
) f。
黑盒证明引用了以下数学事实（定理与引理）：
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
-/
@[simp] lemma compCLM_apply {g : D → E} (hg : g.HasTemperateGrowth)
    (hg_upper : ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖g x‖) ^ k) (f : 𝓢(E, F)) :
    compCLM 𝕜 hg hg_upper f = f ∘ g := rfl

/-- Composition with a function on the right is a continuous linear map on Schwartz space
provided that the function is temperate and antilipschitz. -/
/-
**SchwartzMap.compCLMOfAntilipschitz** 是 Mathlib 中的一个定义，位于命名空间 `SchwartzMap`。
形式化陈述：compCLMOfAntilipschitz {K : Real>=0} {g : D -> E} (hg : g.HasTemperateGrow
th) (h'g : AntilipschitzWith K g) : 𝓢(E, F) ->L[𝕜] 𝓢(D, F)
参数：hg : g.HasTemperateGrowth；h'g : AntilipschitzWith K g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition with a function on the right is a continuous linear map on Schwartz 
space
provided that the function is temperate and antilipschitz.
-/
def compCLMOfAntilipschitz {K : ℝ≥0} {g : D → E}
    (hg : g.HasTemperateGrowth) (h'g : AntilipschitzWith K g) :
    𝓢(E, F) →L[𝕜] 𝓢(D, F) := by
  refine compCLM 𝕜 hg ⟨1, K * max 1 ‖g 0‖, fun x ↦ ?_⟩
  calc
  ‖x‖ ≤ K * ‖g x - g 0‖ := by
    rw [← dist_zero_right, ← dist_eq_norm]
    apply h'g.le_mul_dist
  _ ≤ K * (‖g x‖ + ‖g 0‖) := by
    gcongr
    exact norm_sub_le _ _
  _ ≤ K * (‖g x‖ + max 1 ‖g 0‖) := by
    gcongr
    exact le_max_right _ _
  _ ≤ (K * max 1 ‖g 0‖ : ℝ) * (1 + ‖g x‖) ^ 1 := by
    simp only [mul_add, add_comm (K * ‖g x‖), pow_one, mul_one, add_le_add_iff_left]
    gcongr
    exact le_mul_of_one_le_right (by positivity) (le_max_left _ _)
/-
**SchwartzMap.compCLMOfAntilipschitz_apply** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMa
p`。
形式化陈述：∀ (𝕜 : Type u_2) {D : Type u_4} {E : Type u_5} {F : Type u_6} [inst : Norm
edAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [
inst_3 : NormedSpace ℝ F] [inst_4 : RCLike 𝕜] [inst_5 : NormedAddCommGroup D]   
[inst_6 : NormedSpace ℝ D] [inst_7 : NormedSpace 𝕜 F] {K : NNReal} {g : D → E} (
hg : Function.HasTemperateGrowth g)   (h'g : AntilipschitzWith K g) (f : Schwart
zMap E F), ⇑((SchwartzMap.compCLMOfAntilipschitz 𝕜 hg h'g) f) = ⇑f ∘ g
参数：𝕜 : Type u_2；hg : Function.HasTemperateGrowth g；h'g : AntilipschitzWith K g；f
 : SchwartzMap E F；(SchwartzMap.compCLMOfAntilipschitz 𝕜 hg h'g) f。
黑盒证明引用了以下数学事实（定理与引理）：
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
-/
@[simp] lemma compCLMOfAntilipschitz_apply {K : ℝ≥0} {g : D → E} (hg : g.HasTemperateGrowth)
    (h'g : AntilipschitzWith K g) (f : 𝓢(E, F)) :
    compCLMOfAntilipschitz 𝕜 hg h'g f = f ∘ g := rfl

/-- Composition with a continuous linear equiv on the right is a continuous linear map on
Schwartz space. -/
/-
**SchwartzMap.compCLMOfContinuousLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Schwartz
Map`。
形式化陈述：compCLMOfContinuousLinearEquiv (g : D ≃L[Real] E) : 𝓢(E, F) ->L[𝕜] 𝓢(D, F)
参数：g : D ≃L[Real] E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition with a continuous linear equiv on the right is a continuous linear m
ap on
Schwartz space.
-/
def compCLMOfContinuousLinearEquiv (g : D ≃L[ℝ] E) :
    𝓢(E, F) →L[𝕜] 𝓢(D, F) :=
  compCLMOfAntilipschitz 𝕜 (g.toContinuousLinearMap.hasTemperateGrowth) g.antilipschitz
/-
**SchwartzMap.compCLMOfContinuousLinearEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Sc
hwartzMap`。
形式化陈述：∀ (𝕜 : Type u_2) {D : Type u_4} {E : Type u_5} {F : Type u_6} [inst : Norm
edAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [
inst_3 : NormedSpace ℝ F] [inst_4 : RCLike 𝕜] [inst_5 : NormedAddCommGroup D]   
[inst_6 : NormedSpace ℝ D] [inst_7 : NormedSpace 𝕜 F] (g : D ≃L[ℝ] E) (f : Schwa
rtzMap E F),   ⇑((SchwartzMap.compCLMOfContinuousLinearEquiv 𝕜 g) f) = ⇑f ∘ ⇑g
参数：𝕜 : Type u_2；g : D ≃L[ℝ] E；f : SchwartzMap E F；(SchwartzMap.compCLMOfContinuo
usLinearEquiv 𝕜 g) f。
黑盒证明引用了以下数学事实（定理与引理）：
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
-/
@[simp] lemma compCLMOfContinuousLinearEquiv_apply (g : D ≃L[ℝ] E) (f : 𝓢(E, F)) :
    compCLMOfContinuousLinearEquiv 𝕜 g f = f ∘ g := rfl

variable [NontriviallyNormedField 𝕜'] [NormedAlgebra ℝ 𝕜'] [NormedSpace 𝕜' F]
/-
**SchwartzMap.smulLeftCLM_compCLMOfContinuousLinearEquiv** 是 Mathlib 中的一个定理，位于命名
空间 `SchwartzMap`。
形式化陈述：smulLeftCLM_compCLMOfContinuousLinearEquiv {u : D -> 𝕜'} (hu : u.HasTemper
ateGrowth) (g : D ≃L[Real] E) (f : 𝓢(E, F)) : smulLeftCLM F u (compCLMOfContinuo
usLinearEquiv 𝕜 g f) = compCLMOfContinuousLinearEquiv 𝕜 g (smulLeftCLM F (u ∘ g.
symm) f)
参数：hu : u.HasTemperateGrowth；g : D ≃L[Real] E；f : 𝓢(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.ext`：ext {f g : 𝓢(E, F)} (h : forall x, (f : E -> F) x = g x
) : f = g
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
· 使用定理 `Function.HasTemperateGrowth.comp`：∀ {D : Type u_4} {E : Type u_5} {F : T
ype u_6} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : No
rmedAddCommGroup F] [i…
· 使用定理 `ContinuousLinearEquiv.hasTemperateGrowth`：∀ {E : Type u_5} {F : Type u_6
} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCo
mmGroup F]   [inst_3 : NormedS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SchwartzMap.smulLeftCLM_apply_apply`：smulLeftCLM_apply_apply {g : E -> 𝕜
} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) (x : E) : smulLeftCLM F g f x = g x 
• f x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smulLeftCLM_compCLMOfContinuousLinearEquiv {u : D → 𝕜'} (hu : u.HasTemperateGrowth)
    (g : D ≃L[ℝ] E) (f : 𝓢(E, F)) :
    smulLeftCLM F u (compCLMOfContinuousLinearEquiv 𝕜 g f) =
    compCLMOfContinuousLinearEquiv 𝕜 g (smulLeftCLM F (u ∘ g.symm) f) := by
  ext x
  have hu' : (u ∘ g.symm).HasTemperateGrowth := by fun_prop
  simp [smulLeftCLM_apply_apply hu, smulLeftCLM_apply_apply hu']

end Comp

section Postcomp

variable [RCLike 𝕜]
  [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedSpace 𝕜 H]

/-- Postcomposition with a continuous linear map is a continuous linear map on Schwartz
functions. -/
/-
**SchwartzMap.postcompCLM** 是 Mathlib 中的一个定义，位于命名空间 `SchwartzMap`。
形式化陈述：postcompCLM (L : F ->L[𝕜] G) : 𝓢(E, F) ->L[𝕜] 𝓢(E, G)
参数：L : F ->L[𝕜] G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Postcomposition with a continuous linear map is a continuous linear map on Schwa
rtz
functions.
-/
def postcompCLM (L : F →L[𝕜] G) : 𝓢(E, F) →L[𝕜] 𝓢(E, G) :=
  mkCLM (fun f ↦ L ∘ f) (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp)
    (fun f ↦ (L.restrictScalars ℝ).contDiff.comp (f.smooth ⊤)) <| by
  intro ⟨k, n⟩
  use {⟨k, n⟩}, ‖L‖, by positivity
  intro f x
  simp only [Finset.sup_singleton, schwartzSeminormFamily_apply]
  calc
    _ = ‖x‖ ^ k * ‖(L.restrictScalars ℝ).compContinuousMultilinearMap
        (iteratedFDeriv ℝ n f x)‖ := by
      congr
      exact (L.restrictScalars ℝ).iteratedFDeriv_comp_left f.smooth'.contDiffAt (mod_cast le_top)
    _ ≤ ‖x‖ ^ k * (‖L‖ * ‖iteratedFDeriv ℝ n f x‖) := by
      gcongr
      apply (L.restrictScalars ℝ).norm_compContinuousMultilinearMap_le
    _ = ‖L‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) := by ring
    _ ≤ ‖L‖ * (SchwartzMap.seminorm 𝕜 k n) f := by
      grw [le_seminorm 𝕜 k n f x]

@[simp]
/-
**SchwartzMap.postcompCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：postcompCLM_apply (L : F ->L[𝕜] G) (f : 𝓢(E, F)) (x : E) : f.postcompCLM L
 x = L (f x)
参数：L : F ->L[𝕜] G；f : 𝓢(E, F)；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
-/
theorem postcompCLM_apply (L : F →L[𝕜] G) (f : 𝓢(E, F)) (x : E) : f.postcompCLM L x = L (f x) :=
  rfl

@[simp]
/-
**SchwartzMap.postcompCLM_postcompCLM** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：postcompCLM_postcompCLM (L₁ : F ->L[𝕜] G) (L₂ : G ->L[𝕜] H) (f : 𝓢(E, F)) 
: (f.postcompCLM L₁).postcompCLM L₂ = f.postcompCLM (L₂ ∘L L₁)
参数：L₁ : F ->L[𝕜] G；L₂ : G ->L[𝕜] H；f : 𝓢(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
-/
theorem postcompCLM_postcompCLM (L₁ : F →L[𝕜] G) (L₂ : G →L[𝕜] H) (f : 𝓢(E, F)) :
  (f.postcompCLM L₁).postcompCLM L₂ = f.postcompCLM (L₂ ∘L L₁) := rfl

end Postcomp

section Translate

variable [RCLike 𝕜] [NormedSpace 𝕜 F]

variable (𝕜) in
/-- Translating the argument as a continuous linear map on Schwartz space. -/
/-
**SchwartzMap.compSubConstCLM** 是 Mathlib 中的一个定义，位于命名空间 `SchwartzMap`。
形式化陈述：compSubConstCLM (a : E) : 𝓢(E, F) ->L[𝕜] 𝓢(E, F)
参数：a : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Translating the argument as a continuous linear map on Schwartz space.
-/
def compSubConstCLM (a : E) : 𝓢(E, F) →L[𝕜] 𝓢(E, F) :=
  compCLMOfAntilipschitz (g := fun x ↦ x - a) (K := 1) 𝕜 (by fun_prop)
    (fun _ _ ↦ by simp [edist_dist, dist_eq_norm])

@[simp]
/-
**SchwartzMap.compSubConstCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：compSubConstCLM_apply (f : 𝓢(E, F)) (a x : E) : f.compSubConstCLM 𝕜 a x = 
f (x - a)
参数：f : 𝓢(E, F)；a x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
-/
theorem compSubConstCLM_apply (f : 𝓢(E, F)) (a x : E) :
    f.compSubConstCLM 𝕜 a x = f (x - a) := rfl

@[simp]
/-
**SchwartzMap.compSubConstCLM_zero** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：compSubConstCLM_zero : compSubConstCLM 𝕜 (0 : E) (F
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
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
· 使用定理 `SchwartzMap.ext`：ext {f g : 𝓢(E, F)} (h : forall x, (f : E -> F) x = g x
) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem compSubConstCLM_zero : compSubConstCLM 𝕜 (0 : E) (F := F) = ContinuousLinearMap.id _ _ := by
  ext f x
  simp

@[simp]
/-
**SchwartzMap.compSubConstCLM_comp** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：compSubConstCLM_comp (f : 𝓢(E, F)) (a b : E) : (f.compSubConstCLM 𝕜 a).com
pSubConstCLM 𝕜 b = f.compSubConstCLM 𝕜 (a + b)
参数：f : 𝓢(E, F)；a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.ext`：ext {f g : 𝓢(E, F)} (h : forall x, (f : E -> F) x = g x
) : f = g
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
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_add_eq_sub_sub_swap`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (
a b c : α), a - (b + c) = a - c - b
-/
theorem compSubConstCLM_comp (f : 𝓢(E, F)) (a b : E) :
    (f.compSubConstCLM 𝕜 a).compSubConstCLM 𝕜 b = f.compSubConstCLM 𝕜 (a + b) := by
  ext x
  simp only [compSubConstCLM_apply]
  congr 1
  exact (sub_add_eq_sub_sub_swap x a b).symm

end Translate

section Integration

/-! ### Integration -/


open Real Complex Filter MeasureTheory MeasureTheory.Measure Module

variable [RCLike 𝕜]
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace 𝕜 V]
variable [MeasurableSpace D]

variable {μ : Measure D} [hμ : HasTemperateGrowth μ]

attribute [local instance 101] secondCountableTopologyEither_of_left

variable (𝕜 μ) in
/-
**SchwartzMap.integral_pow_mul_iteratedFDeriv_le** 是 Mathlib 中的一个引理，位于命名空间 `Schw
artzMap`。
形式化陈述：integral_pow_mul_iteratedFDeriv_le (f : 𝓢(D, V)) (k n : Nat) : ∫ x, ‖x‖ ^ 
k * ‖iteratedFDeriv Real n f x‖ ∂μ <= 2 ^ μ.integrablePower * (∫ x, (1 + ‖x‖) ^ 
(- (μ.integrablePower : Real)) ∂μ) * (SchwartzMap.seminorm 𝕜 0 n f + SchwartzMap
.seminorm 𝕜 (k + μ.integrablePower) n f)
参数：f : 𝓢(D, V)；k n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `integral_pow_mul_le_of_le_of_pow_mul_le`：∀ {E : Type u_5} {F : Type u_6}
 [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E]   [inst_2 : NormedAd
dCommGroup F] {μ : MeasureThe…
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
· 使用定理 `SchwartzMap.norm_iteratedFDeriv_le_seminorm`：norm_iteratedFDeriv_le_semi
norm (f : 𝓢(E, F)) (n : Nat) (x₀ : E) : ‖iteratedFDeriv Real n f x₀‖ <= (Schwart
zMap.seminorm 𝕜 0 n) f
· 使用定理 `SchwartzMap.le_seminorm`：le_seminorm (k n : Nat) (f : 𝓢(E, F)) (x : E) :
 ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖ <= SchwartzMap.seminorm 𝕜 k n f
-/
lemma integral_pow_mul_iteratedFDeriv_le (f : 𝓢(D, V)) (k n : ℕ) :
    ∫ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ∂μ ≤ 2 ^ μ.integrablePower *
      (∫ x, (1 + ‖x‖) ^ (- (μ.integrablePower : ℝ)) ∂μ) *
        (SchwartzMap.seminorm 𝕜 0 n f + SchwartzMap.seminorm 𝕜 (k + μ.integrablePower) n f) :=
  integral_pow_mul_le_of_le_of_pow_mul_le (norm_iteratedFDeriv_le_seminorm ℝ _ _)
    (le_seminorm ℝ _ _ _)

variable [BorelSpace D] [SecondCountableTopology D]

variable (μ) in
/-
**SchwartzMap.integrable_pow_mul_iteratedFDeriv** 是 Mathlib 中的一个引理，位于命名空间 `Schwa
rtzMap`。
形式化陈述：integrable_pow_mul_iteratedFDeriv (f : 𝓢(D, V)) (k n : Nat) : Integrable (
fun x => ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖) μ
参数：f : 𝓢(D, V)；k n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `integrable_of_le_of_pow_mul_le`：∀ {E : Type u_5} {F : Type u_6} [inst : 
NormedAddCommGroup E] [inst_1 : MeasurableSpace E]   [inst_2 : NormedAddCommGrou
p F] [BorelSpace E] …
· 使用定理 `SchwartzMap.norm_iteratedFDeriv_le_seminorm`：norm_iteratedFDeriv_le_semi
norm (f : 𝓢(E, F)) (n : Nat) (x₀ : E) : ‖iteratedFDeriv Real n f x₀‖ <= (Schwart
zMap.seminorm 𝕜 0 n) f
· 使用定理 `SchwartzMap.le_seminorm`：le_seminorm (k n : Nat) (f : 𝓢(E, F)) (x : E) :
 ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖ <= SchwartzMap.seminorm 𝕜 k n f
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_left`：∀ (α : Type u_6) (β : Type u_7) [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolog
y α],   SecondCountableTopo…
· 使用定理 `ContDiff.continuous_iteratedFDeriv`：ContDiff.continuous_iteratedFDeriv {
m : Nat} (hm : m <= n) (hf : ContDiff 𝕜 n f) : Continuous fun x => iteratedFDeri
v 𝕜 m f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `SchwartzMap.smooth`：smooth (f : 𝓢(E, F)) (n : Nat∞) : ContDiff Real n f
-/
lemma integrable_pow_mul_iteratedFDeriv
    (f : 𝓢(D, V))
    (k n : ℕ) : Integrable (fun x ↦ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) μ :=
  integrable_of_le_of_pow_mul_le (norm_iteratedFDeriv_le_seminorm ℝ _ _) (le_seminorm ℝ _ _ _)
    ((f.smooth ⊤).continuous_iteratedFDeriv (mod_cast le_top)).aestronglyMeasurable

variable (μ) in
/-
**SchwartzMap.integrable_pow_mul** 是 Mathlib 中的一个引理，位于命名空间 `SchwartzMap`。
形式化陈述：integrable_pow_mul (f : 𝓢(D, V)) (k : Nat) : Integrable (fun x => ‖x‖ ^ k 
* ‖f x‖) μ
参数：f : 𝓢(D, V)；k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_iteratedFDeriv_zero`：norm_iteratedFDeriv_zero : ‖iteratedFDeriv 𝕜 0
 f x‖ = ‖f x‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `SchwartzMap.integrable_pow_mul_iteratedFDeriv`：integrable_pow_mul_iterat
edFDeriv (f : 𝓢(D, V)) (k n : Nat) : Integrable (fun x => ‖x‖ ^ k * ‖iteratedFDe
riv Real n f x‖) μ
-/
lemma integrable_pow_mul (f : 𝓢(D, V))
    (k : ℕ) : Integrable (fun x ↦ ‖x‖ ^ k * ‖f x‖) μ := by
  convert! integrable_pow_mul_iteratedFDeriv μ f k 0 with x
  simp

@[fun_prop]
/-
**SchwartzMap.integrable** 是 Mathlib 中的一个引理，位于命名空间 `SchwartzMap`。
形式化陈述：integrable (f : 𝓢(D, V)) : Integrable f μ
参数：f : 𝓢(D, V)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.mono`：∀ {α : Type u_1} {β : Type u_2} {γ : Type
 u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedAddC
ommGroup β] [inst_1…
· 使用引理 `SchwartzMap.integrable_pow_mul`：integrable_pow_mul (f : 𝓢(D, V)) (k : Na
t) : Integrable (fun x => ‖x‖ ^ k * ‖f x‖) μ
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_left`：∀ (α : Type u_6) (β : Type u_7) [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolog
y α],   SecondCountableTopo…
· 使用定理 `SchwartzMap.continuous`：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAd
dCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst
_3 : NormedS…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
-/
lemma integrable (f : 𝓢(D, V)) : Integrable f μ :=
  (f.integrable_pow_mul μ 0).mono f.continuous.aestronglyMeasurable
    (Eventually.of_forall (fun _ ↦ by simp))

variable (𝕜 μ) in
/-- The integral as a continuous linear map from Schwartz space to the codomain. -/
/-
**SchwartzMap.integralCLM** 是 Mathlib 中的一个定义，位于命名空间 `SchwartzMap`。
形式化陈述：integralCLM : 𝓢(D, V) ->L[𝕜] V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The integral as a continuous linear map from Schwartz space to the codomain.
-/
def integralCLM : 𝓢(D, V) →L[𝕜] V := by
  refine mkCLMtoNormedSpace (∫ x, · x ∂μ)
    (fun f g ↦ integral_add f.integrable g.integrable) (integral_smul · ·) ?_
  rcases hμ.exists_integrable with ⟨n, h⟩
  let m := (n, 0)
  use Finset.Iic m, 2 ^ n * ∫ x : D, (1 + ‖x‖) ^ (- (n : ℝ)) ∂μ
  refine ⟨by positivity, fun f ↦ (norm_integral_le_integral_norm f).trans ?_⟩
  have h' : ∀ x, ‖f x‖ ≤ (1 + ‖x‖) ^ (-(n : ℝ)) *
      (2 ^ n * ((Finset.Iic m).sup (fun m' => SchwartzMap.seminorm 𝕜 m'.1 m'.2) f)) := by
    intro x
    rw [rpow_neg (by positivity), ← div_eq_inv_mul, le_div_iff₀' (by positivity), rpow_natCast]
    simpa using one_add_le_sup_seminorm_apply (m := m) (k := n) (n := 0) le_rfl le_rfl f x
  apply (integral_mono (by simpa using f.integrable_pow_mul μ 0) _ h').trans
  · unfold schwartzSeminormFamily
    rw [integral_mul_const, ← mul_assoc, mul_comm (2 ^ n)]
  apply h.mul_const

variable (𝕜) in
@[simp]
/-
**SchwartzMap.integralCLM_apply** 是 Mathlib 中的一个引理，位于命名空间 `SchwartzMap`。
形式化陈述：integralCLM_apply (f : 𝓢(D, V)) : integralCLM 𝕜 μ f = ∫ x, f x ∂μ
参数：f : 𝓢(D, V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
-/
lemma integralCLM_apply (f : 𝓢(D, V)) : integralCLM 𝕜 μ f = ∫ x, f x ∂μ := by rfl

end Integration

section BoundedContinuousFunction

/-! ### Inclusion into the space of bounded continuous functions -/


open scoped BoundedContinuousFunction

/-
**SchwartzMap.instBoundedContinuousMapClass** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzM
ap`。
形式化陈述：instBoundedContinuousMapClass : BoundedContinuousMapClass 𝓢(E, F) E F wher
e __
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `BoundedContinuousFunction.dist_le_two_norm'`：dist_le_two_norm' {f : γ ->
 β} {C : Real} (hC : forall x, ‖f x‖ <= C) (x y : γ) : dist (f x) (f y) <= 2 * C
· 使用定理 `SchwartzMap.norm_le_seminorm`：norm_le_seminorm (f : 𝓢(E, F)) (x₀ : E) : 
‖f x₀‖ <= (SchwartzMap.seminorm 𝕜 0 0) f
-/
instance instBoundedContinuousMapClass : BoundedContinuousMapClass 𝓢(E, F) E F where
  __ := instContinuousMapClass
  map_bounded := fun f ↦ ⟨2 * (SchwartzMap.seminorm ℝ 0 0) f,
    (BoundedContinuousFunction.dist_le_two_norm' (norm_le_seminorm ℝ f))⟩

/-- Schwartz functions as bounded continuous functions -/
/-
**SchwartzMap.toBoundedContinuousFunction** 是 Mathlib 中的一个定义，位于命名空间 `SchwartzMap
`。
形式化陈述：toBoundedContinuousFunction (f : 𝓢(E, F)) : E ->ᵇ F
参数：f : 𝓢(E, F)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.continuous`：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAd
dCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst
_3 : NormedS…

--- 原说明 ---
Schwartz functions as bounded continuous functions
-/
def toBoundedContinuousFunction (f : 𝓢(E, F)) : E →ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroup f (SchwartzMap.continuous f)
    (SchwartzMap.seminorm ℝ 0 0 f) (norm_le_seminorm ℝ f)

@[simp]
/-
**SchwartzMap.toBoundedContinuousFunction_apply** 是 Mathlib 中的一个定理，位于命名空间 `Schwa
rtzMap`。
形式化陈述：toBoundedContinuousFunction_apply (f : 𝓢(E, F)) (x : E) : f.toBoundedConti
nuousFunction x = f x
参数：f : 𝓢(E, F)；x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toBoundedContinuousFunction_apply (f : 𝓢(E, F)) (x : E) :
    f.toBoundedContinuousFunction x = f x :=
  rfl

/-- Schwartz functions as continuous functions -/
/-
**SchwartzMap.toContinuousMap** 是 Mathlib 中的一个定义，位于命名空间 `SchwartzMap`。
形式化陈述：toContinuousMap (f : 𝓢(E, F)) : C(E, F)
参数：f : 𝓢(E, F)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Schwartz functions as continuous functions
-/
def toContinuousMap (f : 𝓢(E, F)) : C(E, F) :=
  f.toBoundedContinuousFunction.toContinuousMap
/-
**SchwartzMap.norm_toBoundedContinuousFunction_le** 是 Mathlib 中的一个定理，位于命名空间 `Sch
wartzMap`。
形式化陈述：norm_toBoundedContinuousFunction_le (f : 𝓢(E, F)) : ‖f.toBoundedContinuous
Function‖ <= SchwartzMap.seminorm Real 0 0 f
参数：f : 𝓢(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.norm_ofNormedAddCommGroup_le`：norm_ofNormedAdd
CommGroup_le {f : α -> β} (hfc : Continuous f) {C : Real} (hC : 0 <= C) (hfC : f
orall x, ‖f x‖ <= C) : ‖ofNormedAddCommGroup…
· 使用定理 `SchwartzMap.continuous`：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAd
dCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst
_3 : NormedS…
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
-/
theorem norm_toBoundedContinuousFunction_le (f : 𝓢(E, F)) :
    ‖f.toBoundedContinuousFunction‖ ≤ SchwartzMap.seminorm ℝ 0 0 f :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le f.continuous (by positivity) _

variable (𝕜 E F)
variable [RCLike 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- The inclusion map from Schwartz functions to bounded continuous functions as a continuous linear
map. -/
/-
**SchwartzMap.toBoundedContinuousFunctionCLM** 是 Mathlib 中的一个定义，位于命名空间 `Schwartz
Map`。
形式化陈述：toBoundedContinuousFunctionCLM : 𝓢(E, F) ->L[𝕜] E ->ᵇ F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion map from Schwartz functions to bounded continuous functions as a c
ontinuous linear
map.
-/
def toBoundedContinuousFunctionCLM : 𝓢(E, F) →L[𝕜] E →ᵇ F :=
  mkCLMtoNormedSpace toBoundedContinuousFunction (by intros; ext; simp) (by intros; ext; simp)
    (⟨{0}, 1, zero_le_one, by
      simpa [BoundedContinuousFunction.norm_le (apply_nonneg _ _)] using norm_le_seminorm 𝕜 ⟩)

@[simp]
/-
**SchwartzMap.toBoundedContinuousFunctionCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 `Sc
hwartzMap`。
形式化陈述：toBoundedContinuousFunctionCLM_apply (f : 𝓢(E, F)) (x : E) : toBoundedCont
inuousFunctionCLM 𝕜 E F f x = f x
参数：f : 𝓢(E, F)；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem toBoundedContinuousFunctionCLM_apply (f : 𝓢(E, F)) (x : E) :
    toBoundedContinuousFunctionCLM 𝕜 E F f x = f x :=
  rfl
/-
**SchwartzMap.toBoundedContinuousFunctionCLM_injective** 是 Mathlib 中的一个定理，位于命名空间
 `SchwartzMap`。
形式化陈述：toBoundedContinuousFunctionCLM_injective : Function.Injective (toBoundedCo
ntinuousFunctionCLM .. : 𝓢(E, F) ->L[𝕜] E ->ᵇ F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem toBoundedContinuousFunctionCLM_injective :
    Function.Injective (toBoundedContinuousFunctionCLM .. : 𝓢(E, F) →L[𝕜] E →ᵇ F) :=
  fun _ _ h ↦ DFunLike.ext _ _ fun x ↦ DFunLike.congr_fun h x
/-
**SchwartzMap.** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : T3Space 𝓢(E, F) :=
  suffices T2Space 𝓢(E, F) from inferInstance
  .of_injective_continuous (toBoundedContinuousFunctionCLM_injective ℝ ..)
    (ContinuousLinearMap.continuous _)

end BoundedContinuousFunction

section ZeroAtInfty

open scoped ZeroAtInfty

variable [ProperSpace E]

/-
**SchwartzMap.instZeroAtInftyContinuousMapClass** 是 Mathlib 中的一个实例，位于命名空间 `Schwa
rtzMap`。
形式化陈述：instZeroAtInftyContinuousMapClass : ZeroAtInftyContinuousMapClass 𝓢(E, F) 
E F where __
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.tendsto_cocompact`：tendsto_cocompact [ProperSpace E] (f : 𝓢(
E, F)) : Tendsto f (cocompact E) (𝓝 0)
-/
instance instZeroAtInftyContinuousMapClass : ZeroAtInftyContinuousMapClass 𝓢(E, F) E F where
  __ := instContinuousMapClass
  zero_at_infty := tendsto_cocompact

/-- Schwartz functions as continuous functions vanishing at infinity. -/
/-
**SchwartzMap.toZeroAtInfty** 是 Mathlib 中的一个定义，位于命名空间 `SchwartzMap`。
形式化陈述：toZeroAtInfty (f : 𝓢(E, F)) : C₀(E, F) where toFun
参数：f : 𝓢(E, F)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.tendsto_cocompact`：tendsto_cocompact [ProperSpace E] (f : 𝓢(
E, F)) : Tendsto f (cocompact E) (𝓝 0)

--- 原说明 ---
Schwartz functions as continuous functions vanishing at infinity.
-/
def toZeroAtInfty (f : 𝓢(E, F)) : C₀(E, F) where
  toFun := f
  zero_at_infty' := tendsto_cocompact f
/-
**SchwartzMap.toZeroAtInfty_apply** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F] [ins
t_4 : ProperSpace E] (f : SchwartzMap E F) (x : E), f.toZeroAtInfty x = f x
参数：f : SchwartzMap E F；x : E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toZeroAtInfty_apply (f : 𝓢(E, F)) (x : E) : f.toZeroAtInfty x = f x :=
  rfl
/-
**SchwartzMap.toZeroAtInfty_toBCF** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F] [ins
t_4 : ProperSpace E] (f : SchwartzMap E F),   f.toZeroAtInfty.toBCF = f.toBounde
dContinuousFunction
参数：f : SchwartzMap E F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toZeroAtInfty_toBCF (f : 𝓢(E, F)) :
    f.toZeroAtInfty.toBCF = f.toBoundedContinuousFunction :=
  rfl
/-
**SchwartzMap.norm_toZeroAtInfty** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F] [ins
t_4 : ProperSpace E] (f : SchwartzMap E F),   ‖f.toZeroAtInfty‖ = ‖f.toBoundedCo
ntinuousFunction‖
参数：f : SchwartzMap E F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZeroAtInftyContinuousMap.norm_toBCF_eq_norm`：norm_toBCF_eq_norm {f : C₀(
α, β)} : ‖f.toBCF‖ = ‖f‖
· 使用定理 `SchwartzMap.toZeroAtInfty_toBCF`：∀ {E : Type u_5} {F : Type u_6} [inst :
 NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F
]   [inst_3 : NormedS…
-/
@[simp] theorem norm_toZeroAtInfty (f : 𝓢(E, F)) :
    ‖f.toZeroAtInfty‖ = ‖f.toBoundedContinuousFunction‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm, toZeroAtInfty_toBCF]

variable (𝕜 E F)
variable [RCLike 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- The inclusion map from Schwartz functions to continuous functions vanishing at infinity as a
continuous linear map. -/
/-
**SchwartzMap.toZeroAtInftyCLM** 是 Mathlib 中的一个定义，位于命名空间 `SchwartzMap`。
形式化陈述：toZeroAtInftyCLM : 𝓢(E, F) ->L[𝕜] C₀(E, F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion map from Schwartz functions to continuous functions vanishing at i
nfinity as a
continuous linear map.
-/
def toZeroAtInftyCLM : 𝓢(E, F) →L[𝕜] C₀(E, F) :=
  mkCLMtoNormedSpace toZeroAtInfty (by intros; ext; simp) (by intros; ext; simp)
    (⟨{0}, 1, zero_le_one, by simpa [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm,
      BoundedContinuousFunction.norm_le (apply_nonneg _ _)] using norm_le_seminorm 𝕜 ⟩)
/-
**SchwartzMap.toZeroAtInftyCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：∀ (𝕜 : Type u_2) (E : Type u_5) (F : Type u_6) [inst : NormedAddCommGroup 
E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [inst_3 : Normed
Space ℝ F] [inst_4 : ProperSpace E] [inst_5 : RCLike 𝕜]   [inst_6 : NormedSpace 
𝕜 F] [inst_7 : SMulCommClass ℝ 𝕜 F] (f : SchwartzMap E F) (x : E),   ((SchwartzM
ap.toZeroAtInftyCLM 𝕜 E F) f) x = f x
参数：𝕜 : Type u_2；E : Type u_5；F : Type u_6；f : SchwartzMap E F；x : E；(SchwartzMap
.toZeroAtInftyCLM 𝕜 E F) f。
黑盒证明引用了以下数学事实（定理与引理）：
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
-/
@[simp] theorem toZeroAtInftyCLM_apply (f : 𝓢(E, F)) (x : E) : toZeroAtInftyCLM 𝕜 E F f x = f x :=
  rfl

end ZeroAtInfty

section Lp

/-! ### Inclusion into L^p space -/

open MeasureTheory
open scoped NNReal ENNReal

variable [NormedAddCommGroup D] [MeasurableSpace D] [MeasurableSpace E] [OpensMeasurableSpace E]
  [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

variable (𝕜 F) in
/-- The `L^p` norm of a Schwartz function is controlled by a finite family of Schwartz seminorms.

The maximum index `k` and the constant `C` depend on `p` and `μ`.
-/
/-
**SchwartzMap.eLpNorm_le_seminorm** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：eLpNorm_le_seminorm (p : Real>=0∞) (μ : Measure E
参数：p : Real>=0∞。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.HasTemperateGrowth.exists_eLpNorm_lt_top`：∀ {E : T
ype u_5} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E] (p : ENNReal
) {μ : MeasureTheory.Measure E},   μ.HasTemperateGro…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `lt_add_of_pos_of_le`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
Preorder α] [AddRightStrictMono α] {a b c : α},   0 < a → b ≤ c → b < a + c
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.rpow_neg_natCast`：rpow_neg_natCast (x : Real) (n : Nat) : x ^ (-n :
 Real) = x ^ (-n : Int)
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 90 条，此处仅展示前 30 条）

--- 原说明 ---
The `L^p` norm of a Schwartz function is controlled by a finite family of Schwar
tz seminorms.

The maximum index `k` and the constant `C` depend on `p` and `μ`.
-/
theorem eLpNorm_le_seminorm (p : ℝ≥0∞) (μ : Measure E := by volume_tac)
    [hμ : μ.HasTemperateGrowth] :
    ∃ (k : ℕ) (C : ℝ≥0), ∀ (f : 𝓢(E, F)), eLpNorm f p μ ≤
      C * ENNReal.ofReal ((Finset.Iic (k, 0)).sup (schwartzSeminormFamily 𝕜 E F) f) := by
  -- Apply Hölder's inequality `‖f‖_p ≤ ‖f₁‖_p * ‖f₂‖_∞` to obtain the `L^p` norm of `f = f₁ • f₂`
  -- using `f₁ = (1 + ‖x‖) ^ (-k)` and `f₂ = (1 + ‖x‖) ^ k • f x`.
  rcases hμ.exists_eLpNorm_lt_top p with ⟨k, hk⟩
  refine ⟨k, (eLpNorm (fun x ↦ (1 + ‖x‖) ^ (-k : ℝ)) p μ).toNNReal * 2 ^ k, fun f ↦ ?_⟩
  have h_one_add (x : E) : 0 < 1 + ‖x‖ := lt_add_of_pos_of_le zero_lt_one (norm_nonneg x)
  calc eLpNorm (⇑f) p μ
  _ = eLpNorm ((fun x : E ↦ (1 + ‖x‖) ^ (-k : ℝ)) • fun x ↦ (1 + ‖x‖) ^ k • f x) p μ := by
    refine congrArg (eLpNorm · p μ) (funext fun x ↦ ?_)
    simp [(h_one_add x).ne']
  _ ≤ eLpNorm (fun x ↦ (1 + ‖x‖) ^ (-k : ℝ)) p μ * eLpNorm (fun x ↦ (1 + ‖x‖) ^ k • f x) ⊤ μ := by
    refine eLpNorm_smul_le_eLpNorm_mul_eLpNorm_top p _ ?_
    refine Continuous.aestronglyMeasurable ?_
    exact .rpow_const (by fun_prop) fun x ↦ .inl (h_one_add x).ne'
  _ ≤ eLpNorm (fun x ↦ (1 + ‖x‖) ^ (-k : ℝ)) p μ *
      (2 ^ k * ENNReal.ofReal (((Finset.Iic (k, 0)).sup (schwartzSeminormFamily 𝕜 E F)) f)) := by
    gcongr
    refine eLpNormEssSup_le_of_ae_nnnorm_bound (ae_of_all μ fun x ↦ ?_)
    rw [← norm_toNNReal, Real.toNNReal_le_iff_le_coe]
    simpa [norm_smul, abs_of_nonneg (h_one_add x).le] using!
      one_add_le_sup_seminorm_apply (m := (k, 0)) (le_refl k) (le_refl 0) f x
  _ = _ := by
    rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hk.ne]
    simp only [ENNReal.coe_pow, ENNReal.coe_ofNat]
    ring

/-- The `L^p` norm of a Schwartz function is finite. -/
/-
**SchwartzMap.eLpNorm_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：eLpNorm_lt_top (f : 𝓢(E, F)) (p : Real>=0∞) (μ : Measure E
参数：f : 𝓢(E, F)；p : Real>=0∞。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.eLpNorm_le_seminorm`：eLpNorm_le_seminorm (p : Real>=0∞) (μ :
 Measure E
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `ENNReal.ofReal_lt_top`：∀ {r : ℝ}, ENNReal.ofReal r < ⊤

--- 原说明 ---
The `L^p` norm of a Schwartz function is finite.
-/
theorem eLpNorm_lt_top (f : 𝓢(E, F)) (p : ℝ≥0∞) (μ : Measure E := by volume_tac)
    [hμ : μ.HasTemperateGrowth] : eLpNorm f p μ < ⊤ := by
  rcases eLpNorm_le_seminorm ℝ F p μ with ⟨k, C, hC⟩
  exact lt_of_le_of_lt (hC f) (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top)

variable [SecondCountableTopologyEither E F]

/-- Schwartz functions are in `L^∞`; does not require `hμ.HasTemperateGrowth`. -/
/-
**SchwartzMap.memLp_top** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：memLp_top (f : 𝓢(E, F)) (μ : Measure E
参数：f : 𝓢(E, F)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.decay`：decay (f : 𝓢(E, F)) (k n : Nat) : exists C : Real, 0 
< C ∧ forall x, ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖ <= C
· 使用定理 `MeasureTheory.memLp_top_of_bound`：memLp_top_of_bound {f : α -> E} (hf : 
AEStronglyMeasurable f μ) (C : Real) (hfC : forallᵐ x ∂μ, ‖f x‖ <= C) : MemLp f 
∞ μ
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `SchwartzMap.continuous`：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAd
dCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst
_3 : NormedS…
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `norm_iteratedFDeriv_zero`：norm_iteratedFDeriv_zero : ‖iteratedFDeriv 𝕜 0
 f x‖ = ‖f x‖
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
Schwartz functions are in `L^∞`; does not require `hμ.HasTemperateGrowth`.
-/
theorem memLp_top (f : 𝓢(E, F)) (μ : Measure E := by volume_tac) : MemLp f ⊤ μ := by
  rcases f.decay 0 0 with ⟨C, _, hC⟩
  refine memLp_top_of_bound f.continuous.aestronglyMeasurable C (ae_of_all μ fun x ↦ ?_)
  simpa using hC x

/-- Schwartz functions are in `L^p` for any `p`. -/
/-
**SchwartzMap.memLp** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：memLp (f : 𝓢(E, F)) (p : Real>=0∞) (μ : Measure E
参数：f : 𝓢(E, F)；p : Real>=0∞。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `SchwartzMap.continuous`：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAd
dCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst
_3 : NormedS…
· 使用定理 `SchwartzMap.eLpNorm_lt_top`：eLpNorm_lt_top (f : 𝓢(E, F)) (p : Real>=0∞) 
(μ : Measure E

--- 原说明 ---
Schwartz functions are in `L^p` for any `p`.
-/
theorem memLp (f : 𝓢(E, F)) (p : ℝ≥0∞) (μ : Measure E := by volume_tac)
    [hμ : μ.HasTemperateGrowth] : MemLp f p μ :=
  ⟨f.continuous.aestronglyMeasurable, f.eLpNorm_lt_top p μ⟩

/-- Map a Schwartz function to an `Lp` function for any `p`. -/
/-
**SchwartzMap.toLp** 是 Mathlib 中的一个定义，位于命名空间 `SchwartzMap`。
形式化陈述：toLp (f : 𝓢(E, F)) (p : Real>=0∞) (μ : Measure E
参数：f : 𝓢(E, F)；p : Real>=0∞。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.memLp`：memLp (f : 𝓢(E, F)) (p : Real>=0∞) (μ : Measure E

--- 原说明 ---
Map a Schwartz function to an `Lp` function for any `p`.
-/
def toLp (f : 𝓢(E, F)) (p : ℝ≥0∞) (μ : Measure E := by volume_tac) [hμ : μ.HasTemperateGrowth] :
    Lp F p μ := (f.memLp p μ).toLp
/-
**SchwartzMap.instCoeToLp** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
形式化陈述：instCoeToLp {p : Real>=0∞} {μ : Measure E} [hμ : μ.HasTemperateGrowth] : C
oe 𝓢(E, F) (Lp F p μ) where coe
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCoeToLp {p : ℝ≥0∞} {μ : Measure E} [hμ : μ.HasTemperateGrowth] :
    Coe 𝓢(E, F) (Lp F p μ) where
  coe := (SchwartzMap.toLp · p μ)
/-
**SchwartzMap.coeFn_toLp** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：coeFn_toLp (f : 𝓢(E, F)) (p : Real>=0∞) (μ : Measure E
参数：f : 𝓢(E, F)；p : Real>=0∞。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.coeFn_toLp`：coeFn_toLp {f : α -> E} (hf : MemLp f p 
μ) : hf.toLp f =ᵐ[μ] f
· 使用定理 `SchwartzMap.memLp`：memLp (f : 𝓢(E, F)) (p : Real>=0∞) (μ : Measure E
-/
theorem coeFn_toLp (f : 𝓢(E, F)) (p : ℝ≥0∞) (μ : Measure E := by volume_tac)
    [hμ : μ.HasTemperateGrowth] : f.toLp p μ =ᵐ[μ] f := (f.memLp p μ).coeFn_toLp
/-
**SchwartzMap.norm_toLp** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：norm_toLp {f : 𝓢(E, F)} {p : Real>=0∞} {μ : Measure E} [hμ : μ.HasTemperat
eGrowth] : ‖f.toLp p μ‖ = ENNReal.toReal (eLpNorm f p μ)
参数：E, F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.norm_def`：norm_def (f : Lp E p μ) : ‖f‖ = ENNReal.toRea
l (eLpNorm f p μ)
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `SchwartzMap.coeFn_toLp`：coeFn_toLp (f : 𝓢(E, F)) (p : Real>=0∞) (μ : Mea
sure E
-/
theorem norm_toLp {f : 𝓢(E, F)} {p : ℝ≥0∞} {μ : Measure E} [hμ : μ.HasTemperateGrowth] :
    ‖f.toLp p μ‖ = ENNReal.toReal (eLpNorm f p μ) := by
  rw [Lp.norm_def, eLpNorm_congr_ae (coeFn_toLp f p μ)]
/-
**SchwartzMap.norm_toLp'** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：norm_toLp' {f : 𝓢(E, F)} {p : Real>=0∞} {μ : Measure E} (hp₁ : p != 0) (hp
₂ : p != ⊤) [hμ : μ.HasTemperateGrowth] : ‖f.toLp p μ‖ = (∫ x, ‖f x‖ ^ p.toReal 
∂μ) ^ p.toReal⁻¹
参数：E, F；hp₁ : p != 0；hp₂ : p != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SchwartzMap.norm_toLp`：norm_toLp {f : 𝓢(E, F)} {p : Real>=0∞} {μ : Measu
re E} [hμ : μ.HasTemperateGrowth] : ‖f.toLp p μ‖ = ENNReal.toReal (eLpNorm f p μ
)
· 使用定理 `MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm`：∀ {α : Type u_1} {m :
 MeasurableSpace α} {μ : MeasureTheory.Measure α} {H : Type u_6} [inst : NormedA
ddCommGroup H]   {f : α → H} {p : ENNRe…
· 使用定理 `SchwartzMap.memLp`：memLp (f : 𝓢(E, F)) (p : Real>=0∞) (μ : Measure E
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用引理 `MeasureTheory.integral_nonneg`：integral_nonneg {f : α -> E} (hf : 0 <= f
) : 0 <= ∫ x, f x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem norm_toLp' {f : 𝓢(E, F)} {p : ℝ≥0∞} {μ : Measure E} (hp₁ : p ≠ 0) (hp₂ : p ≠ ⊤)
    [hμ : μ.HasTemperateGrowth] :
    ‖f.toLp p μ‖ = (∫ x, ‖f x‖ ^ p.toReal ∂μ) ^ p.toReal⁻¹ := by
  rw [norm_toLp, MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm hp₁ hp₂ (f.memLp p μ),
    ENNReal.toReal_ofReal (by positivity)]
/-
**SchwartzMap.norm_toLp_one** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：norm_toLp_one {f : 𝓢(E, F)} {μ : Measure E} [hμ : μ.HasTemperateGrowth] : 
‖f.toLp 1 μ‖ = ∫ x, ‖f x‖ ∂μ
参数：E, F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `SchwartzMap.norm_toLp'`：norm_toLp' {f : 𝓢(E, F)} {p : Real>=0∞} {μ : Mea
sure E} (hp₁ : p != 0) (hp₂ : p != ⊤) [hμ : μ.HasTemperateGrowth] : ‖f.toLp p μ‖
 = (∫ x, ‖f …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem norm_toLp_one {f : 𝓢(E, F)} {μ : Measure E} [hμ : μ.HasTemperateGrowth] :
    ‖f.toLp 1 μ‖ = ∫ x, ‖f x‖ ∂μ := by
  simpa using norm_toLp' (p := 1) (by simp) (by simp)
/-
**SchwartzMap.norm_toLp_top_le** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：norm_toLp_top_le {f : 𝓢(E, F)} {μ : Measure E} [hμ : μ.HasTemperateGrowth]
 : ‖f.toLp ⊤ μ‖ <= SchwartzMap.seminorm Real 0 0 f
参数：E, F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SchwartzMap.norm_toLp`：norm_toLp {f : 𝓢(E, F)} {p : Real>=0∞} {μ : Measu
re E} [hμ : μ.HasTemperateGrowth] : ‖f.toLp p μ‖ = ENNReal.toReal (eLpNorm f p μ
)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_le_ofReal_iff`：ofReal_le_ofReal_iff {p q : Real} (h : 0 <
= q) : ENNReal.ofReal p <= ENNReal.ofReal q ↔ p <= q
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `MeasureTheory.MemLp.eLpNorm_ne_top`：∀ {α : Type u_1} {ε : Type u_2} {m0 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} [inst : ENorm ε
]   [inst_1 : Topologica…
· 使用定理 `SchwartzMap.memLp_top`：memLp_top (f : 𝓢(E, F)) (μ : Measure E
· 使用定理 `MeasureTheory.eLpNormEssSup_le_of_ae_bound`：eLpNormEssSup_le_of_ae_bound
 {f : α -> F} {C : Real} (hfC : forallᵐ x ∂μ, ‖f x‖ <= C) : eLpNormEssSup f μ <=
 ENNReal.ofReal C
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `SchwartzMap.norm_le_seminorm`：norm_le_seminorm (f : 𝓢(E, F)) (x₀ : E) : 
‖f x₀‖ <= (SchwartzMap.seminorm 𝕜 0 0) f
-/
theorem norm_toLp_top_le {f : 𝓢(E, F)} {μ : Measure E} [hμ : μ.HasTemperateGrowth] :
    ‖f.toLp ⊤ μ‖ ≤ SchwartzMap.seminorm ℝ 0 0 f := by
  rw [norm_toLp, ← ENNReal.ofReal_le_ofReal_iff (by positivity),
    ENNReal.ofReal_toReal (memLp_top f μ).eLpNorm_ne_top]
  exact eLpNormEssSup_le_of_ae_bound <| .of_forall <| norm_le_seminorm ℝ f
/-
**SchwartzMap.injective_toLp** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：injective_toLp (p : Real>=0∞) (μ : Measure E
参数：p : Real>=0∞。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `SchwartzMap.memLp`：memLp (f : 𝓢(E, F)) (p : Real>=0∞) (μ : Measure E
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Continuous.ae_eq_iff_eq`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] {m : MeasurableSpace X} [inst_1 : TopologicalSpace Y]   [T2Space Y]
 (μ : Measure…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SchwartzMap.continuous`：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAd
dCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst
_3 : NormedS…
-/
theorem injective_toLp (p : ℝ≥0∞) (μ : Measure E := by volume_tac) [hμ : μ.HasTemperateGrowth]
    [μ.IsOpenPosMeasure] : Function.Injective (fun f : 𝓢(E, F) ↦ f.toLp p μ) :=
  fun f g ↦ by simpa [toLp] using (Continuous.ae_eq_iff_eq μ f.continuous g.continuous).mp

variable (𝕜 F) in
/-
**SchwartzMap.norm_toLp_le_seminorm** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：norm_toLp_le_seminorm (p : Real>=0∞) (μ : Measure E
参数：p : Real>=0∞。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `SchwartzMap.eLpNorm_le_seminorm`：eLpNorm_le_seminorm (p : Real>=0∞) (μ :
 Measure E
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SchwartzMap.norm_toLp`：norm_toLp {f : 𝓢(E, F)} {p : Real>=0∞} {μ : Measu
re E} [hμ : μ.HasTemperateGrowth] : ‖f.toLp p μ‖ = ENNReal.toReal (eLpNorm f p μ
)
· 使用定理 `ENNReal.toReal_le_of_le_ofReal`：toReal_le_of_le_ofReal {a : Real>=0∞} {b
 : Real} (hb : 0 <= b) (h : a <= ENNReal.ofReal b) : ENNReal.toReal a <= b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `ENNReal.ofReal_mul`：ofReal_mul {p q : Real} (hp : 0 <= p) : ENNReal.ofRe
al (p * q) = ENNReal.ofReal p * ENNReal.ofReal q
· 使用定理 `NNReal.zero_le_coe`：zero_le_coe {q : Real>=0} : 0 <= (q : Real)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.ofReal_coe_nnreal`：∀ {p : NNReal}, ENNReal.ofReal ↑p = ↑p
-/
theorem norm_toLp_le_seminorm (p : ℝ≥0∞) (μ : Measure E := by volume_tac)
    [hμ : μ.HasTemperateGrowth] :
    ∃ k C, 0 ≤ C ∧ ∀ (f : 𝓢(E, F)), ‖f.toLp p μ‖ ≤
      C * (Finset.Iic (k, 0)).sup (schwartzSeminormFamily 𝕜 E F) f := by
  rcases eLpNorm_le_seminorm 𝕜 F p μ with ⟨k, C, hC⟩
  refine ⟨k, C, C.coe_nonneg, fun f ↦ ?_⟩
  rw [norm_toLp]
  refine ENNReal.toReal_le_of_le_ofReal (by simp [mul_nonneg]) ?_
  rw [ENNReal.ofReal_mul NNReal.zero_le_coe]
  simpa using hC f

variable (𝕜 F) in
/-- Continuous linear map from Schwartz functions to `L^p`. -/
/-
**SchwartzMap.toLpCLM** 是 Mathlib 中的一个定义，位于命名空间 `SchwartzMap`。
形式化陈述：toLpCLM (p : Real>=0∞) [Fact (1 <= p)] (μ : Measure E
参数：p : Real>=0∞；1 <= p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous linear map from Schwartz functions to `L^p`.
-/
def toLpCLM (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure E := by volume_tac)
    [hμ : μ.HasTemperateGrowth] : 𝓢(E, F) →L[𝕜] Lp F p μ :=
  mkCLMtoNormedSpace (fun f ↦ f.toLp p μ) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) <| by
    rcases norm_toLp_le_seminorm 𝕜 F p μ with ⟨k, C, hC_pos, hC⟩
    exact ⟨Finset.Iic (k, 0), C, hC_pos, hC⟩
/-
**SchwartzMap.toLpCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：∀ {𝕜 : Type u_2} {E : Type u_5} {F : Type u_6} [inst : NormedAddCommGroup 
E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [inst_3 : Normed
Space ℝ F] [inst_4 : MeasurableSpace E]   [inst_5 : OpensMeasurableSpace E] [ins
t_6 : NormedField 𝕜] [inst_7 : NormedSpace 𝕜 F] [inst_8 : SMulCommClass ℝ 𝕜 F]  
 [inst_9 : SecondCountableTopologyEither E F] {p : ENNReal} [inst_10 : Fact (1 ≤
 p)] {μ : MeasureTheory.Measure E}   [hμ : μ.HasTemperateGrowth] {f : SchwartzMa
p E F}, (SchwartzMap.toLpCLM 𝕜 F p μ) f = f.toLp p μ
参数：1 ≤ p；SchwartzMap.toLpCLM 𝕜 F p μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
@[simp] theorem toLpCLM_apply {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure E} [hμ : μ.HasTemperateGrowth]
    {f : 𝓢(E, F)} : toLpCLM 𝕜 F p μ f = f.toLp p μ := rfl

@[fun_prop]
/-
**SchwartzMap.continuous_toLp** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：continuous_toLp {p : Real>=0∞} [Fact (1 <= p)] {μ : Measure E} [hμ : μ.Has
TemperateGrowth] : Continuous (fun f : 𝓢(E, F) => f.toLp p μ)
参数：1 <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem continuous_toLp {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure E} [hμ : μ.HasTemperateGrowth] :
    Continuous (fun f : 𝓢(E, F) ↦ f.toLp p μ) := (toLpCLM ℝ F p μ).continuous

/-- Schwartz functions are dense in `Lp`. -/
/-
**SchwartzMap.denseRange_toLpCLM** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：denseRange_toLpCLM [FiniteDimensional Real E] [BorelSpace E] {p : Real>=0∞
} (hp : p != ⊤) [hp' : Fact (1 <= p)] {μ : Measure E} [hμ : μ.HasTemperateGrowth
] [IsFiniteMeasureOnCompacts μ] : DenseRange (SchwartzMap.toLpCLM Real F p μ)
参数：hp : p != ⊤；1 <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_closure_iff_nhds_basis`：mem_closure_iff_nhds_basis {p : ι -> Prop} {
s : ι -> Set X} (h : (𝓝 x).HasBasis p s) : x in closure t ↔ forall i, p i -> exi
sts y in t, y in…
· 使用定理 `Metric.nhds_basis_closedBall`：nhds_basis_closedBall : (𝓝 x).HasBasis (fu
n ε : Real => 0 < ε) (closedBall x)
· 使用定理 `MeasureTheory.MemLp.exist_eLpNorm_sub_le`：exist_eLpNorm_sub_le {p : Real
>=0∞} (hp : p != ⊤) (hp₂ : 1 <= p) {f : E -> F} (hf : MemLp f p μ) {ε : Real} (h
ε : 0 < ε) : exists g, HasComp…
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `SchwartzMap.coeFn_toLp`：coeFn_toLp (f : 𝓢(E, F)) (p : Real>=0∞) (μ : Mea
sure E
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasCompactSupport.toSchwartzMap_toFun`：∀ {E : Type u_5} {F : Type u_6} [
inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommG
roup F]   [inst_3 : NormedS…
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Lp.dist_def`：dist_def (f g : Lp E p μ) : dist f g = (eLpNo
rm (⇑f - ⇑g) p μ).toReal
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
Schwartz functions are dense in `Lp`.
-/
theorem denseRange_toLpCLM [FiniteDimensional ℝ E] [BorelSpace E] {p : ℝ≥0∞} (hp : p ≠ ⊤)
    [hp' : Fact (1 ≤ p)] {μ : Measure E} [hμ : μ.HasTemperateGrowth] [IsFiniteMeasureOnCompacts μ] :
    DenseRange (SchwartzMap.toLpCLM ℝ F p μ) := by
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε ↦ ?_
  obtain ⟨g, hg₁, hg₂, hg₃⟩ := MemLp.exist_eLpNorm_sub_le hp hp'.out (Lp.memLp f) hε
  use (hg₁.toSchwartzMap hg₂).toLp p μ
  have : (f : E → F) - ((hg₁.toSchwartzMap hg₂).toLp p μ : E → F) =ᵐ[μ] (f : E → F) - g := by
    filter_upwards [(hg₁.toSchwartzMap hg₂).coeFn_toLp p μ]
    simp
  simp only [Set.mem_range, toLpCLM_apply, exists_apply_eq_apply, Metric.mem_closedBall', true_and,
    Lp.dist_def, eLpNorm_congr_ae this]
  grw [hg₃, ENNReal.toReal_ofReal hε.le]
  simp

end Lp

section L2

open MeasureTheory

variable [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]

@[simp]
/-
**SchwartzMap.inner_toL2_toL2_eq** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：inner_toL2_toL2_eq (f g : 𝓢(H, V)) (μ : Measure H
参数：f g : 𝓢(H, V)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountableTopologyEither_of_left`：∀ (α : Type u_6) (β : Type u_7) [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolog
y α],   SecondCountableTopo…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `SchwartzMap.coeFn_toLp`：coeFn_toLp (f : 𝓢(E, F)) (p : Real>=0∞) (μ : Mea
sure E
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem inner_toL2_toL2_eq (f g : 𝓢(H, V)) (μ : Measure H := by volume_tac) [μ.HasTemperateGrowth] :
    inner ℂ (f.toLp 2 μ) (g.toLp 2 μ) = ∫ x, inner ℂ (f x) (g x) ∂μ := by
  apply integral_congr_ae
  have hf_ae := f.coeFn_toLp 2 μ
  have hg_ae := g.coeFn_toLp 2 μ
  filter_upwards [hf_ae, hg_ae] with _ hf hg
  rw [hf, hg]

end L2

end SchwartzMap

