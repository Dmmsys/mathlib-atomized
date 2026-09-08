/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
public import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio

/-!
# The real function `fun x ↦ x * log x + 1 - x`

We define `klFun x = x * log x + 1 - x`. That function is notable because the Kullback-Leibler
divergence is an f-divergence for `klFun`. That is, the Kullback-Leibler divergence is an integral
of `klFun` composed with a Radon-Nikodym derivative.

For probability measures, any function `f` that differs from `klFun` by an affine function of the
form `x ↦ a * (x - 1)` would give the same value for the integral
`∫ x, f (μ.rnDeriv ν x).toReal ∂ν`.
However, `klFun` is the particular choice among those that satisfies `klFun 1 = 0` and
`deriv klFun 1 = 0`, which ensures that desirable properties of the Kullback-Leibler divergence
extend to other finite measures: it is nonnegative and zero iff the two measures are equal.

## Main definitions

* `klFun`: the function `fun x : ℝ ↦ x * log x + 1 - x`.

This is a continuous nonnegative, strictly convex function on $[0,∞)$, with minimum value 0 at 1.

## Main statements

* `integrable_klFun_rnDeriv_iff`: For two finite measures `μ ≪ ν`, the function
  `x ↦ klFun (μ.rnDeriv ν x).toReal` is integrable with respect to `ν` iff the log-likelihood ratio
  `llr μ ν` is integrable with respect to `μ`.
* `integral_klFun_rnDeriv`: For two finite measures `μ ≪ ν` such that `llr μ ν` is integrable with
  respect to `μ`,
  `∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν = ∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ`.

-/

@[expose] public section

open Real MeasureTheory Filter Set

namespace InformationTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {x : ℝ}

/-- The function `x : ℝ ↦ x * log x + 1 - x`.
The Kullback-Leibler divergence is an f-divergence for this function. -/
/-
**InformationTheory.klFun** 是 Mathlib 中的一个定义，位于命名空间 `InformationTheory`。
形式化陈述：klFun (x : Real) : Real
参数：x : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function `x : ℝ ↦ x * log x + 1 - x`.
The Kullback-Leibler divergence is an f-divergence for this function.
-/
noncomputable def klFun (x : ℝ) : ℝ := x * log x + 1 - x
/-
**InformationTheory.klFun_apply** 是 Mathlib 中的一个引理，位于命名空间 `InformationTheory`。
形式化陈述：klFun_apply (x : Real) : klFun x = x * log x + 1 - x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma klFun_apply (x : ℝ) : klFun x = x * log x + 1 - x := rfl
/-
**InformationTheory.klFun_zero** 是 Mathlib 中的一个引理，位于命名空间 `InformationTheory`。
形式化陈述：klFun_zero : klFun 0 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma klFun_zero : klFun 0 = 1 := by simp [klFun]
/-
**InformationTheory.klFun_one** 是 Mathlib 中的一个引理，位于命名空间 `InformationTheory`。
形式化陈述：klFun_one : klFun 1 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma klFun_one : klFun 1 = 0 := by simp [klFun]

/-- `klFun` is strictly convex on $[0,∞)$. -/
/-
**InformationTheory.strictConvexOn_klFun** 是 Mathlib 中的一个引理，位于命名空间 `InformationT
heory`。
形式化陈述：strictConvexOn_klFun : StrictConvexOn Real (Ici 0) klFun
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvexOn.sub_concaveOn`：StrictConvexOn.sub_concaveOn (hf : StrictC
onvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) : StrictConvexOn 𝕜 s (f - g)
· 使用定理 `StrictConvexOn.add_convexOn`：StrictConvexOn.add_convexOn (hf : StrictCon
vexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) : StrictConvexOn 𝕜 s (f + g)
· 使用引理 `Real.strictConvexOn_mul_log`：strictConvexOn_mul_log : StrictConvexOn Rea
l (Set.Ici (0 : Real)) (fun x => x * log x)
· 使用定理 `convexOn_const`：convexOn_const (c : β) (hs : Convex 𝕜 s) : ConvexOn 𝕜 s 
fun _ : E => c
· 使用定理 `convex_Ici`：convex_Ici (r : β) : Convex 𝕜 (Ici r)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `concaveOn_id`：concaveOn_id {s : Set β} (hs : Convex 𝕜 s) : ConcaveOn 𝕜 s
 _root_.id

--- 原说明 ---
`klFun` is strictly convex on $[0,∞)$.
-/
lemma strictConvexOn_klFun : StrictConvexOn ℝ (Ici 0) klFun :=
  (strictConvexOn_mul_log.add_convexOn (convexOn_const _ (convex_Ici _))).sub_concaveOn
    (concaveOn_id (convex_Ici _))

/-- `klFun` is convex on $[0,∞)$. -/
/-
**InformationTheory.convexOn_klFun** 是 Mathlib 中的一个引理，位于命名空间 `InformationTheory`
。
形式化陈述：convexOn_klFun : ConvexOn Real (Ici 0) klFun
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvexOn.convexOn`：StrictConvexOn.convexOn {s : Set E} {f : E -> β
} (hf : StrictConvexOn 𝕜 s f) : ConvexOn 𝕜 s f
· 使用引理 `InformationTheory.strictConvexOn_klFun`：strictConvexOn_klFun : StrictCon
vexOn Real (Ici 0) klFun

--- 原说明 ---
`klFun` is convex on $[0,∞)$.
-/
lemma convexOn_klFun : ConvexOn ℝ (Ici 0) klFun := strictConvexOn_klFun.convexOn

/-- `klFun` is convex on $(0,∞)$.
This is an often useful consequence of `convexOn_klFun`, which states convexity on $[0, ∞)$. -/
/-
**InformationTheory.convexOn_Ioi_klFun** 是 Mathlib 中的一个引理，位于命名空间 `InformationThe
ory`。
形式化陈述：convexOn_Ioi_klFun : ConvexOn Real (Ioi 0) klFun
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.subset`：ConvexOn.subset {t : Set E} (hf : ConvexOn 𝕜 t f) (hst 
: s subseteq t) (hs : Convex 𝕜 s) : ConvexOn 𝕜 s f
· 使用引理 `InformationTheory.convexOn_klFun`：convexOn_klFun : ConvexOn Real (Ici 0)
 klFun
· 使用定理 `Set.Ioi_subset_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b ≤ 
a → Set.Ioi a ⊆ Set.Ici b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `convex_Ioi`：convex_Ioi (r : β) : Convex 𝕜 (Ioi r)
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
`klFun` is convex on $(0,∞)$.
This is an often useful consequence of `convexOn_klFun`, which states convexity 
on $[0, ∞)$.
-/
lemma convexOn_Ioi_klFun : ConvexOn ℝ (Ioi 0) klFun :=
  convexOn_klFun.subset (Ioi_subset_Ici le_rfl) (convex_Ioi _)

/-- `klFun` is continuous. -/
@[continuity, fun_prop]
/-
**InformationTheory.continuous_klFun** 是 Mathlib 中的一个引理，位于命名空间 `InformationTheor
y`。
形式化陈述：continuous_klFun : Continuous klFun
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g 
: X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Continuous.add_const`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [SeparatelyContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSp
ace X] {f …
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
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
· 使用引理 `Real.continuous_mul_log`：continuous_mul_log : Continuous fun x => x * lo
g x
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)

--- 原说明 ---
`klFun` is continuous.
-/
lemma continuous_klFun : Continuous klFun := by unfold klFun; fun_prop

/-- `klFun` is measurable. -/
@[fun_prop]
/-
**InformationTheory.measurable_klFun** 是 Mathlib 中的一个引理，位于命名空间 `InformationTheor
y`。
形式化陈述：measurable_klFun : Measurable klFun
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用引理 `InformationTheory.continuous_klFun`：continuous_klFun : Continuous klFun

--- 原说明 ---
`klFun` is measurable.
-/
lemma measurable_klFun : Measurable klFun := continuous_klFun.measurable

/-- `klFun` is strongly measurable. -/
@[fun_prop]
/-
**InformationTheory.stronglyMeasurable_klFun** 是 Mathlib 中的一个引理，位于命名空间 `Informat
ionTheory`。
形式化陈述：stronglyMeasurable_klFun : StronglyMeasurable klFun
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : TopologicalSp
ace β] [Topological…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用引理 `InformationTheory.measurable_klFun`：measurable_klFun : Measurable klFun

--- 原说明 ---
`klFun` is strongly measurable.
-/
lemma stronglyMeasurable_klFun : StronglyMeasurable klFun := measurable_klFun.stronglyMeasurable

section Derivatives

/-- The derivative of `klFun` at `x ≠ 0` is `log x`. -/
/-
**InformationTheory.hasDerivAt_klFun** 是 Mathlib 中的一个引理，位于命名空间 `InformationTheor
y`。
形式化陈述：hasDerivAt_klFun (hx : x != 0) : HasDerivAt klFun (log x) x
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The derivative of `klFun` at `x ≠ 0` is `log x`.
-/
lemma hasDerivAt_klFun (hx : x ≠ 0) : HasDerivAt klFun (log x) x := by
  convert! ((hasDerivAt_mul_log hx).add (hasDerivAt_const x 1)).sub (hasDerivAt_id x) using 1
  ring
/-
**InformationTheory.not_differentiableAt_klFun_zero** 是 Mathlib 中的一个引理，位于命名空间 `I
nformationTheory`。
形式化陈述：not_differentiableAt_klFun_zero : ¬ DifferentiableAt Real klFun 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Real.not_DifferentiableAt_log_mul_zero`：not_DifferentiableAt_log_mul_zer
o : ¬ DifferentiableAt Real (fun x => x * log x) 0
-/
lemma not_differentiableAt_klFun_zero : ¬ DifferentiableAt ℝ klFun 0 := by
  unfold klFun; simpa using not_DifferentiableAt_log_mul_zero

/-- The derivative of `klFun` is `log x`. This also holds at `x = 0` although `klFun` is not
differentiable there since the default value of `deriv` in that case is 0. -/
@[simp]
/-
**InformationTheory.deriv_klFun** 是 Mathlib 中的一个引理，位于命名空间 `InformationTheory`。
形式化陈述：deriv_klFun : deriv klFun = log
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `deriv_zero_of_not_differentiableAt`：deriv_zero_of_not_differentiableAt (
h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0
· 使用引理 `InformationTheory.not_differentiableAt_klFun_zero`：not_differentiableAt_
klFun_zero : ¬ DifferentiableAt Real klFun 0
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用引理 `InformationTheory.hasDerivAt_klFun`：hasDerivAt_klFun (hx : x != 0) : Has
DerivAt klFun (log x) x

--- 原说明 ---
The derivative of `klFun` is `log x`. This also holds at `x = 0` although `klFun
` is not
differentiable there since the default value of `deriv` in that case is 0.
-/
lemma deriv_klFun : deriv klFun = log := by
  ext x
  by_cases h0 : x = 0
  · simp only [h0, log_zero]
    exact deriv_zero_of_not_differentiableAt not_differentiableAt_klFun_zero
  · exact (hasDerivAt_klFun h0).deriv
/-
**InformationTheory.not_differentiableWithinAt_klFun_Ioi_zero** 是 Mathlib 中的一个引理
，位于命名空间 `InformationTheory`。
形式化陈述：not_differentiableWithinAt_klFun_Ioi_zero : ¬ DifferentiableWithinAt Real 
klFun (Ioi 0) 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_differentiableWithinAt_of_deriv_tendsto_atBot_Ioi`：not_differentiabl
eWithinAt_of_deriv_tendsto_atBot_Ioi (f : Real -> Real) {a : Real} (hf : Tendsto
 (deriv f) (𝓝[>] a) atBot) : ¬ Differentiab…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `InformationTheory.deriv_klFun`：deriv_klFun : deriv klFun = log
· 使用引理 `Real.tendsto_log_nhdsGT_zero`：tendsto_log_nhdsGT_zero : Tendsto log (𝓝[>
] 0) atBot
-/
lemma not_differentiableWithinAt_klFun_Ioi_zero : ¬ DifferentiableWithinAt ℝ klFun (Ioi 0) 0 := by
  refine not_differentiableWithinAt_of_deriv_tendsto_atBot_Ioi _ ?_
  rw [deriv_klFun]
  exact tendsto_log_nhdsGT_zero
/-
**InformationTheory.not_differentiableWithinAt_klFun_Iio_zero** 是 Mathlib 中的一个引理
，位于命名空间 `InformationTheory`。
形式化陈述：not_differentiableWithinAt_klFun_Iio_zero : ¬ DifferentiableWithinAt Real 
klFun (Iio 0) 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_differentiableWithinAt_of_deriv_tendsto_atBot_Iio`：not_differentiabl
eWithinAt_of_deriv_tendsto_atBot_Iio (f : Real -> Real) {a : Real} (hf : Tendsto
 (deriv f) (𝓝[<] a) atBot) : ¬ Differentiab…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `InformationTheory.deriv_klFun`：deriv_klFun : deriv klFun = log
· 使用引理 `Real.tendsto_log_nhdsLT_zero`：tendsto_log_nhdsLT_zero : Tendsto log (𝓝[<
] 0) atBot
-/
lemma not_differentiableWithinAt_klFun_Iio_zero : ¬ DifferentiableWithinAt ℝ klFun (Iio 0) 0 := by
  refine not_differentiableWithinAt_of_deriv_tendsto_atBot_Iio _ ?_
  rw [deriv_klFun]
  exact tendsto_log_nhdsLT_zero

/-- The right derivative of `klFun` is `log x`. This also holds at `x = 0` although `klFun` is not
differentiable there since the default value of `derivWithin` in that case is 0. -/
@[simp]
/-
**InformationTheory.rightDeriv_klFun** 是 Mathlib 中的一个引理，位于命名空间 `InformationTheor
y`。
形式化陈述：rightDeriv_klFun : derivWithin klFun (Ioi x) x = log x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `derivWithin_zero_of_not_differentiableWithinAt`：derivWithin_zero_of_not_
differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) : derivWithin f s x
 = 0
· 使用引理 `InformationTheory.not_differentiableWithinAt_klFun_Ioi_zero`：not_differe
ntiableWithinAt_klFun_Ioi_zero : ¬ DifferentiableWithinAt Real klFun (Ioi 0) 0
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用引理 `InformationTheory.hasDerivAt_klFun`：hasDerivAt_klFun (hx : x != 0) : Has
DerivAt klFun (log x) x
· 使用定理 `uniqueDiffWithinAt_Ioi`：uniqueDiffWithinAt_Ioi (a : Real) : UniqueDiffWi
thinAt Real (Ioi a) a

--- 原说明 ---
The right derivative of `klFun` is `log x`. This also holds at `x = 0` although 
`klFun` is not
differentiable there since the default value of `derivWithin` in that case is 0.
-/
lemma rightDeriv_klFun : derivWithin klFun (Ioi x) x = log x := by
  by_cases h0 : x = 0
  · simp only [h0, log_zero]
    exact derivWithin_zero_of_not_differentiableWithinAt not_differentiableWithinAt_klFun_Ioi_zero
  · exact (hasDerivAt_klFun h0).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi x)

/-- The left derivative of `klFun` is `log x`. This also holds at `x = 0` although `klFun` is not
differentiable there since the default value of `derivWithin` in that case is 0. -/
@[simp]
/-
**InformationTheory.leftDeriv_klFun** 是 Mathlib 中的一个引理，位于命名空间 `InformationTheory
`。
形式化陈述：leftDeriv_klFun : derivWithin klFun (Iio x) x = log x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `derivWithin_zero_of_not_differentiableWithinAt`：derivWithin_zero_of_not_
differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) : derivWithin f s x
 = 0
· 使用引理 `InformationTheory.not_differentiableWithinAt_klFun_Iio_zero`：not_differe
ntiableWithinAt_klFun_Iio_zero : ¬ DifferentiableWithinAt Real klFun (Iio 0) 0
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用引理 `InformationTheory.hasDerivAt_klFun`：hasDerivAt_klFun (hx : x != 0) : Has
DerivAt klFun (log x) x
· 使用定理 `uniqueDiffWithinAt_Iio`：uniqueDiffWithinAt_Iio (a : Real) : UniqueDiffWi
thinAt Real (Iio a) a

--- 原说明 ---
The left derivative of `klFun` is `log x`. This also holds at `x = 0` although `
klFun` is not
differentiable there since the default value of `derivWithin` in that case is 0.
-/
lemma leftDeriv_klFun : derivWithin klFun (Iio x) x = log x := by
  by_cases h0 : x = 0
  · simp only [h0, log_zero]
    exact derivWithin_zero_of_not_differentiableWithinAt not_differentiableWithinAt_klFun_Iio_zero
  · exact (hasDerivAt_klFun h0).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio x)
/-
**InformationTheory.rightDeriv_klFun_one** 是 Mathlib 中的一个引理，位于命名空间 `InformationT
heory`。
形式化陈述：rightDeriv_klFun_one : derivWithin klFun (Ioi 1) 1 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `InformationTheory.rightDeriv_klFun`：rightDeriv_klFun : derivWithin klFun
 (Ioi x) x = log x
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightDeriv_klFun_one : derivWithin klFun (Ioi 1) 1 = 0 := by simp
/-
**InformationTheory.leftDeriv_klFun_one** 是 Mathlib 中的一个引理，位于命名空间 `InformationTh
eory`。
形式化陈述：leftDeriv_klFun_one : derivWithin klFun (Iio 1) 1 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `InformationTheory.leftDeriv_klFun`：leftDeriv_klFun : derivWithin klFun (
Iio x) x = log x
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftDeriv_klFun_one : derivWithin klFun (Iio 1) 1 = 0 := by simp
/-
**InformationTheory.tendsto_rightDeriv_klFun_atTop** 是 Mathlib 中的一个引理，位于命名空间 `In
formationTheory`。
形式化陈述：tendsto_rightDeriv_klFun_atTop : Tendsto (fun x => derivWithin klFun (Ioi 
x) x) atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `InformationTheory.rightDeriv_klFun`：rightDeriv_klFun : derivWithin klFun
 (Ioi x) x = log x
· 使用定理 `Real.tendsto_log_atTop`：tendsto_log_atTop : Tendsto log atTop atTop
-/
lemma tendsto_rightDeriv_klFun_atTop :
    Tendsto (fun x ↦ derivWithin klFun (Ioi x) x) atTop atTop := by
  simp only [rightDeriv_klFun]
  exact tendsto_log_atTop

end Derivatives

/-
**InformationTheory.isMinOn_klFun** 是 Mathlib 中的一个引理，位于命名空间 `InformationTheory`。
形式化陈述：isMinOn_klFun : IsMinOn klFun (Ici 0) 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.isMinOn_of_rightDeriv_eq_zero`：isMinOn_of_rightDeriv_eq_zero (h
f : ConvexOn Real S f) (hx : x in interior S) (hf_rd : derivWithin f (Ioi x) x =
 0) : IsMinOn f S x
· 使用引理 `InformationTheory.convexOn_klFun`：convexOn_klFun : ConvexOn Real (Ici 0)
 klFun
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_Ici'`：interior_Ici' {a : α} (ha : (Iio a).Nonempty) : interior 
(Ici a) = Ioi a
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
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `InformationTheory.rightDeriv_klFun`：rightDeriv_klFun : derivWithin klFun
 (Ioi x) x = log x
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isMinOn_klFun : IsMinOn klFun (Ici 0) 1 :=
  convexOn_klFun.isMinOn_of_rightDeriv_eq_zero (by simp) (by simp)

/-- The function `klFun` is nonnegative on `[0,∞)`. -/
/-
**InformationTheory.klFun_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `InformationTheory`。
形式化陈述：klFun_nonneg (hx : 0 <= x) : 0 <= klFun x
参数：hx : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `InformationTheory.isMinOn_klFun`：isMinOn_klFun : IsMinOn klFun (Ici 0) 1
· 使用引理 `InformationTheory.klFun_one`：klFun_one : klFun 1 = 0

--- 原说明 ---
The function `klFun` is nonnegative on `[0,∞)`.
-/
lemma klFun_nonneg (hx : 0 ≤ x) : 0 ≤ klFun x := klFun_one ▸ isMinOn_klFun hx
/-
**InformationTheory.klFun_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `InformationTheo
ry`。
形式化陈述：klFun_eq_zero_iff (hx : 0 <= x) : klFun x = 0 ↔ x = 1
参数：hx : 0 <= x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictConvexOn.eq_of_isMinOn`：StrictConvexOn.eq_of_isMinOn (hf : StrictC
onvexOn 𝕜 s f) (hfx : IsMinOn f s x) (hfy : IsMinOn f s y) (hx : x in s) (hy : y
 in s) : x = y
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用引理 `InformationTheory.strictConvexOn_klFun`：strictConvexOn_klFun : StrictCon
vexOn Real (Ici 0) klFun
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isMinOn_iff`：isMinOn_iff : IsMinOn f s a ↔ forall x in s, f a <= f x
· 使用引理 `InformationTheory.klFun_nonneg`：klFun_nonneg (hx : 0 <= x) : 0 <= klFun 
x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `InformationTheory.isMinOn_klFun`：isMinOn_klFun : IsMinOn klFun (Ici 0) 1
· 使用引理 `zero_le_one'`：zero_le_one' (α) [Zero α] [One α] [LE α] [ZeroLEOneClass α
] : (0 : α) <= 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma klFun_eq_zero_iff (hx : 0 ≤ x) : klFun x = 0 ↔ x = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [klFun_apply, h]⟩
  exact strictConvexOn_klFun.eq_of_isMinOn (isMinOn_iff.mpr fun y hy ↦ h ▸ klFun_nonneg hy)
    isMinOn_klFun hx (zero_le_one' ℝ)
/-
**InformationTheory.tendsto_klFun_atTop** 是 Mathlib 中的一个引理，位于命名空间 `InformationTh
eory`。
形式化陈述：tendsto_klFun_atTop : Tendsto klFun atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
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
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
（共 39 条，此处仅展示前 30 条）
-/
lemma tendsto_klFun_atTop : Tendsto klFun atTop atTop := by
  have : klFun = (fun x ↦ x * (log x - 1) + 1) := by unfold klFun; ext; ring
  rw [this]
  refine Tendsto.atTop_add ?_ tendsto_const_nhds
  refine tendsto_id.atTop_mul_atTop₀ ?_
  exact tendsto_log_atTop.atTop_add tendsto_const_nhds

section Integral

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- For two finite measures `μ ≪ ν`, the function `x ↦ klFun (μ.rnDeriv ν x).toReal` is integrable
with respect to `ν` iff `llr μ ν` is integrable with respect to `μ`. -/
/-
**InformationTheory.integrable_klFun_rnDeriv_iff** 是 Mathlib 中的一个引理，位于命名空间 `Info
rmationTheory`。
形式化陈述：integrable_klFun_rnDeriv_iff (hμν : μ ≪ ν) : Integrable (fun x => klFun (μ
.rnDeriv ν x).toReal) ν ↔ Integrable (llr μ ν) μ
参数：hμν : μ ≪ ν。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.integrable_add_iff_integrable_left'`：integrable_add_iff_in
tegrable_left' {f g : α -> β} (hf : Integrable f μ) : Integrable (fun x => g x +
 f x) μ ↔ Integrable g μ
· 使用定理 `MeasureTheory.Integrable.sub'`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
g : α → β},   Measu…
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `MeasureTheory.Measure.integrable_toReal_rnDeriv`：∀ {𝓧 : Type u_1} {m𝓧 : 
MeasurableSpace 𝓧} {μ ν : MeasureTheory.Measure 𝓧} [MeasureTheory.IsFiniteMeasur
e μ],   MeasureTheory.Integrable (fun…
· 使用引理 `MeasureTheory.integrable_rnDeriv_mul_log_iff`：integrable_rnDeriv_mul_log
_iff [SigmaFinite μ] [μ.HaveLebesgueDecomposition ν] (hμν : μ ≪ ν) : Integrable 
(fun a => (μ.rnDeriv ν a).toReal *…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `InformationTheory.klFun.eq_1`：∀ (x : ℝ), InformationTheory.klFun x = x *
 Real.log x + 1 - x
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)

--- 原说明 ---
For two finite measures `μ ≪ ν`, the function `x ↦ klFun (μ.rnDeriv ν x).toReal`
 is integrable
with respect to `ν` iff `llr μ ν` is integrable with respect to `μ`.
-/
lemma integrable_klFun_rnDeriv_iff (hμν : μ ≪ ν) :
    Integrable (fun x ↦ klFun (μ.rnDeriv ν x).toReal) ν ↔ Integrable (llr μ ν) μ := by
  suffices Integrable (fun x ↦ (μ.rnDeriv ν x).toReal * log (μ.rnDeriv ν x).toReal
      + (1 - (μ.rnDeriv ν x).toReal)) ν ↔ Integrable (llr μ ν) μ by
    convert! this using 3 with x
    rw [klFun, add_sub_assoc]
  rw [integrable_add_iff_integrable_left', integrable_rnDeriv_mul_log_iff hμν]
  fun_prop
/-
**InformationTheory.integral_klFun_rnDeriv** 是 Mathlib 中的一个引理，位于命名空间 `Informatio
nTheory`。
形式化陈述：integral_klFun_rnDeriv (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) : ∫ 
x, klFun (μ.rnDeriv ν x).toReal ∂ν = ∫ x, llr μ ν x ∂μ + ν.real univ - μ.real un
iv
参数：hμν : μ ≪ ν；h_int : Integrable (llr μ ν) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.Integrable.add`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [ins
t_1 : ESeminormedA…
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
· 使用引理 `MeasureTheory.integrable_rnDeriv_mul_log_iff`：integrable_rnDeriv_mul_log
_iff [SigmaFinite μ] [μ.HaveLebesgueDecomposition ν] (hμν : μ ≪ ν) : Integrable 
(fun a => (μ.rnDeriv ν a).toReal *…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `MeasureTheory.Measure.integrable_toReal_rnDeriv`：∀ {𝓧 : Type u_1} {m𝓧 : 
MeasurableSpace 𝓧} {μ ν : MeasureTheory.Measure 𝓧} [MeasureTheory.IsFiniteMeasur
e μ],   MeasureTheory.Integrable (fun…
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用引理 `MeasureTheory.Measure.integral_toReal_rnDeriv`：integral_toReal_rnDeriv [
SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) : ∫ x, (μ.rnDeriv ν x).toReal ∂ν = 
μ.real Set.univ
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MeasureTheory.integral_rnDeriv_smul`：integral_rnDeriv_smul (hμν : μ ≪ ν)
 : ∫ x, (μ.rnDeriv ν x).toReal • f x ∂ν = ∫ x, f x ∂μ
-/
lemma integral_klFun_rnDeriv (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    ∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν
      = ∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ := by
  unfold klFun
  rw [integral_sub, integral_add, integral_const, Measure.integral_toReal_rnDeriv hμν, smul_eq_mul,
    mul_one]
  · congr 2
    exact integral_rnDeriv_smul hμν
  · rwa [integrable_rnDeriv_mul_log_iff hμν]
  · fun_prop
  · refine Integrable.add ?_ (integrable_const _)
    rwa [integrable_rnDeriv_mul_log_iff hμν]
  · fun_prop

end Integral

end InformationTheory

