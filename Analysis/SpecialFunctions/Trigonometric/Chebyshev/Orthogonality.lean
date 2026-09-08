/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Polynomial

/-!
# Chebyshev polynomials over the reals: orthogonality

Chebyshev T polynomials are orthogonal with respect to `√(1 - x ^ 2)⁻¹`.

## Main statements

* `integrable_measureT`: continuous functions are integrable with respect to Lebesgue measure
  scaled by `√(1 - x ^ 2)⁻¹` and restricted to `(-1, 1]`.
* `integral_eval_T_real_mul_evalT_real_measureT_of_ne`:
  if `n ≠ m` then the integral of `T_n * T_m` equals `0`.
* `integral_eval_T_real_mul_self_measureT_zero`:
  if `n = m = 0` then the integral equals `π`.
* `integral_eval_T_real_mul_self_measureT_of_ne_zero`:
  if `n = m ≠ 0` then the integral equals `π / 2`.

## TODO

* Prove that Chebyshev U polynomials are orthogonal with respect to `√(1 - x ^ 2)`
* Bundle Chebyshev T polynomials into a HilbertBasis for MeasureTheory.Lp ℝ 2 measureT

-/
public section

namespace Polynomial.Chebyshev

open Real intervalIntegral MeasureTheory

open scoped NNReal

/-- Lebesgue measure scaled by √(1 - x ^ 2)⁻¹. -/
/-
**Polynomial.Chebyshev.measureT** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.Chebyshev`
。
形式化陈述：measureT : Measure Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lebesgue measure scaled by √(1 - x ^ 2)⁻¹.
-/
noncomputable def measureT : Measure ℝ :=
  (volume.withDensity
    fun x ↦ ENNReal.ofNNReal (.mk (√(1 - x ^ 2)⁻¹) (by positivity))).restrict (Set.Ioc (-1) 1)
/-
**Polynomial.Chebyshev.integral_measureT** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.C
hebyshev`。
形式化陈述：integral_measureT (f : Real -> Real) : ∫ x, f x ∂measureT = ∫ x in -1..1, 
f x * √(1 - x ^ 2)⁻¹
参数：f : Real -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `Mathlib.Meta.NormNum.isInt_le_true`：∀ {α : Type u_1} [inst : Ring α] [in
st_1 : PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : ℤ},   Mathlib.Meta.N
ormNum.IsInt a a' → Math…
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Ortho
gonality.0.Polynomial.Chebyshev.measureT.eq_1`：Polynomial.Chebyshev.measureT =  
 (MeasureTheory.volume.withDensity fun x => ↑(NNReal.mk √(1 - x ^ 2)⁻¹ ⋯)).restr
ict (Set.Ioc (-1) 1)
· 使用定理 `MeasureTheory.restrict_withDensity`：restrict_withDensity {s : Set α} (hs
 : MeasurableSet s) (f : α -> Real>=0∞) : (μ.withDensity f).restrict s = (μ.rest
rict s).withDensity f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `integral_withDensity_eq_integral_smul`：integral_withDensity_eq_integral_
smul {f : X -> Real>=0} (f_meas : Measurable f) (g : X -> E) : ∫ x, g x ∂μ.withD
ensity (fun x => f x) = ∫ x…
· 使用定理 `Measurable.nnreal_mk`：Measurable.nnreal_mk {f : α -> Real} (hf : Measura
ble f) {h'f : forall x, 0 <= f x} : Measurable (fun x => NNReal.mk (f x) (h'f x)
)
· 使用定理 `Measurable.sqrt`：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℝ}, M
easurable f → Measurable fun x => √(f x)
· 使用定理 `Measurable.fun_inv`：∀ {G : Type u_2} {α : Type u_3} [inst : Inv G] [inst
_1 : MeasurableSpace G] [MeasurableInv G] {m : MeasurableSpace α}   {f : α → G},
 Measura…
· 使用定理 `ContinuousInv₀.measurableInv`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : GroupWithZero γ]   [T1S
pace γ] [Continuou…
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `Measurable.const_sub`：∀ {G : Type u_2} {α : Type u_3} [inst : Measurable
Space G] [inst_1 : Sub G] {m : MeasurableSpace α} {f : α → G}   [MeasurableSub G
], Measura…
· 使用定理 `ContinuousSub.measurableSub`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Sub γ]   [ContinuousSub 
γ], MeasurableSub…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Measurable.pow_const`：Measurable.pow_const (hf : Measurable f) (c : γ) :
 Measurable fun x => f x ^ c
（共 46 条，此处仅展示前 30 条）
-/
theorem integral_measureT (f : ℝ → ℝ) :
    ∫ x, f x ∂measureT = ∫ x in -1..1, f x * √(1 - x ^ 2)⁻¹ := by
  rw [integral_of_le (by norm_num), measureT,
    restrict_withDensity (by measurability),
    integral_withDensity_eq_integral_smul (by fun_prop)]
  congr! 2 with x hx
  simp [NNReal.smul_def, mul_comm]
/-
**Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv** 是 Mathlib 中的一个定理
，位于命名空间 `Polynomial.Chebyshev`。
形式化陈述：intervalIntegrable_sqrt_one_sub_sq_inv : IntervalIntegrable (fun x => √(1 
- x ^ 2)⁻¹) volume (-1) 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegrable_iff`：intervalIntegrable_iff : IntervalIntegrable f μ 
a b ↔ IntegrableOn f (Ι a b) μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `intervalIntegral.integrableOn_deriv_of_nonneg`：integrableOn_deriv_of_non
neg (hcont : ContinuousOn g (Icc a b)) (hderiv : forall x in Ioo a b, HasDerivAt
 g (g' x) x) (g'pos : forall x in I…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.neg`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpace
 X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f : X → 
G}, …
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Real.continuous_arccos`：continuous_arccos : Continuous arccos
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `Real.sqrt_inv`：sqrt_inv (x : Real) : √x⁻¹ = (√x)⁻¹
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `HasDerivAt.neg`：HasDerivAt.neg (h : HasDerivAt f f' x) : HasDerivAt (-f)
 (-f') x
· 使用定理 `Real.hasDerivAt_arccos`：hasDerivAt_arccos {x : Real} (h₁ : x != -1) (h₂ 
: x != 1) : HasDerivAt arccos (-(1 / √(1 - x ^ 2))) x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
（共 33 条，此处仅展示前 30 条）
-/
theorem intervalIntegrable_sqrt_one_sub_sq_inv :
    IntervalIntegrable (fun x ↦ √(1 - x ^ 2)⁻¹) volume (-1) 1 := by
  rw [intervalIntegrable_iff]
  refine integrableOn_deriv_of_nonneg continuous_arccos.neg.continuousOn (fun x hx ↦ ?_) (by simp)
  simpa using! (hasDerivAt_arccos (by aesop) (by aesop)).neg
/-
**Polynomial.Chebyshev.integrable_measureT** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
.Chebyshev`。
形式化陈述：integrable_measureT {f : Real -> Real} (hf : ContinuousOn f (Set.Icc (-1) 
1)) : Integrable f measureT
参数：hf : ContinuousOn f (Set.Icc (-1) 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.uIcc_of_lt`：uIcc_of_lt (h : a < b) : [[a, b]] = Icc a b
· 使用定理 `Mathlib.Meta.NormNum.isInt_lt_true`：∀ {α : Type u_1} [inst : Ring α] [in
st_1 : PartialOrder α] [IsOrderedRing α] [Nontrivial α] {a b : α} {a' b' : ℤ},  
 Mathlib.Meta.NormNum.Is…
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IntervalIntegrable.continuousOn_mul`：continuousOn_mul {f g : Real -> A} 
(hf : IntervalIntegrable f μ a b) (hg : ContinuousOn g [[a, b]]) : IntervalInteg
rable (fun x => g x * f x…
· 使用定理 `Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv`：intervalInt
egrable_sqrt_one_sub_sq_inv : IntervalIntegrable (fun x => √(1 - x ^ 2)⁻¹) volum
e (-1) 1
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Ortho
gonality.0.Polynomial.Chebyshev.measureT.eq_1`：Polynomial.Chebyshev.measureT =  
 (MeasureTheory.volume.withDensity fun x => ↑(NNReal.mk √(1 - x ^ 2)⁻¹ ⋯)).restr
ict (Set.Ioc (-1) 1)
· 使用定理 `MeasureTheory.restrict_withDensity`：restrict_withDensity {s : Set α} (hs
 : MeasurableSet s) (f : α -> Real>=0∞) : (μ.withDensity f).restrict s = (μ.rest
rict s).withDensity f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.integrable_withDensity_iff`：integrable_withDensity_iff {f 
: α -> Real>=0∞} (hf : Measurable f) (hflt : forallᵐ x ∂μ, f x < ∞) {g : α -> Re
al} : Integrable g (μ.withDens…
· 使用定理 `Measurable.coe_nnreal_ennreal`：Measurable.coe_nnreal_ennreal {f : α -> R
eal>=0} (hf : Measurable f) : Measurable fun x => (f x : Real>=0∞)
· 使用定理 `Measurable.nnreal_mk`：Measurable.nnreal_mk {f : α -> Real} (hf : Measura
ble f) {h'f : forall x, 0 <= f x} : Measurable (fun x => NNReal.mk (f x) (h'f x)
)
· 使用定理 `Measurable.sqrt`：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℝ}, M
easurable f → Measurable fun x => √(f x)
· 使用定理 `Measurable.fun_inv`：∀ {G : Type u_2} {α : Type u_3} [inst : Inv G] [inst
_1 : MeasurableSpace G] [MeasurableInv G] {m : MeasurableSpace α}   {f : α → G},
 Measura…
· 使用定理 `ContinuousInv₀.measurableInv`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : GroupWithZero γ]   [T1S
pace γ] [Continuou…
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `Measurable.const_sub`：∀ {G : Type u_2} {α : Type u_3} [inst : Measurable
Space G] [inst_1 : Sub G] {m : MeasurableSpace α} {f : α → G}   [MeasurableSub G
], Measura…
· 使用定理 `ContinuousSub.measurableSub`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Sub γ]   [ContinuousSub 
γ], MeasurableSub…
（共 53 条，此处仅展示前 30 条）
-/
theorem integrable_measureT {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (-1) 1)) :
    Integrable f measureT := by
  replace hf : ContinuousOn f (Set.uIcc (-1) 1) := by rwa [Set.uIcc_of_lt (by norm_num)]
  have := intervalIntegrable_sqrt_one_sub_sq_inv.continuousOn_mul hf
  rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num)] at this
  rw [measureT, restrict_withDensity (by measurability),
    integrable_withDensity_iff (by fun_prop) (by simp)]
  unfold IntegrableOn at this
  convert! this

open Set in
/-
**Polynomial.Chebyshev.integral_measureT_eq_integral_cos** 是 Mathlib 中的一个定理，位于命名
空间 `Polynomial.Chebyshev`。
形式化陈述：integral_measureT_eq_integral_cos {f : Real -> Real} : ∫ x, f x ∂measureT 
= ∫ θ in 0..π, f (cos θ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Chebyshev.integral_measureT`：integral_measureT (f : Real -> R
eal) : ∫ x, f x ∂measureT = ∫ x in -1..1, f x * √(1 - x ^ 2)⁻¹
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_symm`：integral_symm (a b) : ∫ x in b..a, f x ∂
μ = -∫ x in a..b, f x ∂μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegral.integral_neg`：∀ {E : Type u_5} [inst : NormedAddCommGro
up E] [inst_1 : NormedSpace ℝ E] {a b : ℝ} {f : ℝ → E}   {μ : MeasureTheory.Meas
ure ℝ}, ∫ (x : ℝ) i…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.sqrt_inv`：sqrt_inv (x : Real) : √x⁻¹ = (√x)⁻¹
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos`：integral_comp_
mul_deriv_of_deriv_nonpos {f f' g : Real -> Real} (hf : ContinuousOn f [[a, b]])
 (hff' : forall x in Ioo (min a b) (max a b), …
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Real.continuous_arccos`：continuous_arccos : Continuous arccos
· 使用定理 `Real.hasDerivAt_arccos`：hasDerivAt_arccos {x : Real} (h₁ : x != -1) (h₂ 
: x != 1) : HasDerivAt arccos (-(1 / √(1 - x ^ 2))) x
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `intervalIntegral.integral_congr`：integral_congr {a b : Real} (h : EqOn f
 g [[a, b]]) : ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ
· 使用定理 `Real.cos_arccos`：cos_arccos {x : Real} (hx₁ : -1 <= x) (hx₂ : x <= 1) : 
cos (arccos x) = x
（共 33 条，此处仅展示前 30 条）
-/
theorem integral_measureT_eq_integral_cos {f : ℝ → ℝ} :
    ∫ x, f x ∂measureT = ∫ θ in 0..π, f (cos θ) := calc
  ∫ x, f x ∂measureT = ∫ x in -1..1, f x * √(1 - x ^ 2)⁻¹ := integral_measureT f
  _ = ∫ x in 1..-1, f x * -(√(1 - x ^ 2)⁻¹) := by
    rw [integral_symm, ← intervalIntegral.integral_neg]
    simp
  _ = ∫ θ in (arccos 1)..(arccos (-1)), f (cos θ) := by
    rw [← integral_comp_mul_deriv_of_deriv_nonpos (f' := fun x => -(1 / √(1 - x ^ 2)))]
    · simp_rw [Function.comp_apply]
      exact integral_congr <| fun x hx => by simp [cos_arccos (x := x) (by aesop) (by aesop)]
    · fun_prop
    · exact fun x hx ↦ (hasDerivAt_arccos (by aesop) (by aesop))
    · simp
  _ = ∫ θ in 0..π, f (cos θ) := by simp

@[deprecated (since := "2026-03-19")]
alias integral_measureT_eq_integral_cos_of_continuous := integral_measureT_eq_integral_cos
/-
**Polynomial.Chebyshev.integral_eval_T_real_measureT_zero** 是 Mathlib 中的一个定理，位于命
名空间 `Polynomial.Chebyshev`。
形式化陈述：integral_eval_T_real_measureT_zero : ∫ x, (T Real 0).eval x ∂measureT = π
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Chebyshev.integral_measureT_eq_integral_cos`：integral_measure
T_eq_integral_cos {f : Real -> Real} : ∫ x, f x ∂measureT = ∫ θ in 0..π, f (cos 
θ)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.Chebyshev.T_zero`：T_zero : T R 0 = 1
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `intervalIntegral.integral_const`：integral_const [CompleteSpace E] (c : E
) : ∫ _ in a..b, c = (b - a) • c
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_eval_T_real_measureT_zero :
    ∫ x, (T ℝ 0).eval x ∂measureT = π := by
  rw [integral_measureT_eq_integral_cos]; simp
/-
**Polynomial.Chebyshev.integral_eval_T_real_measureT_of_ne_zero** 是 Mathlib 中的一个
定理，位于命名空间 `Polynomial.Chebyshev`。
形式化陈述：integral_eval_T_real_measureT_of_ne_zero {n : Int} (hn : n != 0) : ∫ x, (T
 Real n).eval x ∂measureT = 0
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Int.cast_ne_zero`：cast_ne_zero : (n : α) != 0 ↔ n != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `intervalIntegral.integral_congr`：integral_congr {a b : Real} (h : EqOn f
 g [[a, b]]) : ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Real.deriv_sin`：deriv_sin : deriv sin = cos
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_deriv_of_contDiffOn_Icc`：integral_deriv_of_con
tDiffOn_Icc (h : ContDiffOn Real 1 f (Icc a b)) (hab : a <= b) : ∫ x in a..b, de
riv f x = f b - f a
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `Real.contDiff_sin`：contDiff_sin {n} : ContDiff Real n sin
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Int.cast_pos`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : 
PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {n : ℤ}, 0 < ↑n 
↔ …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.sin_int_mul_pi`：sin_int_mul_pi (n : Int) : sin (n * π) = 0
· 使用定理 `Real.sin_zero`：sin_zero : sin 0 = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `intervalIntegral.integral_symm`：integral_symm (a b) : ∫ x in b..a, f x ∂
μ = -∫ x in a..b, f x ∂μ
· 使用定理 `mul_nonpos_of_nonpos_of_nonneg`：mul_nonpos_of_nonpos_of_nonneg [MulPosMo
no α] (ha : a <= 0) (hb : 0 <= b) : a * b <= 0
（共 46 条，此处仅展示前 30 条）
-/
theorem integral_eval_T_real_measureT_of_ne_zero {n : ℤ} (hn : n ≠ 0) :
    ∫ x, (T ℝ n).eval x ∂measureT = 0 := by
  have hn' : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  suffices ∫ θ in 0..n * π, cos θ = 0 by
    rw [integral_measureT_eq_integral_cos]
    simp_rw [T_real_cos]
    rwa [integral_comp_mul_left _ (Int.cast_ne_zero.mpr hn), smul_eq_zero_iff_right (by aesop),
      mul_zero]
  trans ∫ θ in 0..n * π, (deriv sin) θ
  · refine integral_congr <| fun x hx => (congrFun deriv_sin x).symm
  by_cases! 0 ≤ n
  case pos => rw [integral_deriv_of_contDiffOn_Icc contDiff_sin.contDiffOn (by positivity)]; simp
  case neg hn =>
    rw [integral_symm, integral_deriv_of_contDiffOn_Icc contDiff_sin.contDiffOn]
    · simp
    exact mul_nonpos_of_nonpos_of_nonneg (Int.cast_nonpos.mpr <| le_of_lt hn) pi_nonneg
/-
**Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT** 是 Mathlib
 中的一个定理，位于命名空间 `Polynomial.Chebyshev`。
形式化陈述：integral_eval_T_real_mul_eval_T_real_measureT (n m : Int) : ∫ x, (T Real n
).eval x * (T Real m).eval x ∂measureT = ((∫ x, (T Real (n + m)).eval x ∂measure
T) + (∫ x, (T Real (n - m)).eval x ∂measureT)) / 2
参数：n m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.Chebyshev.T_mul_T`：T_mul_T (m k : Int) : 2 * T R m * T R k = 
T R (m + k) + T R (m - k)
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用定理 `Polynomial.Chebyshev.integrable_measureT`：integrable_measureT {f : Real 
-> Real} (hf : ContinuousOn f (Set.Icc (-1) 1)) : Integrable f measureT
· 使用定理 `Polynomial.continuousOn`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : 
TopologicalSpace R] [IsTopologicalSemiring R] (p : Polynomial R)   {s : Set R}, 
ContinuousOn …
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.integral_const_mul`：integral_const_mul {L : Type*} [RCLike
 L] (r : L) (f : α -> L) : ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `Polynomial.eval_ofNat`：eval_ofNat (n : Nat) [n.AtLeastTwo] (a : R) : (of
Nat(n) : R[X]).eval a = ofNat(n)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
-/
theorem integral_eval_T_real_mul_eval_T_real_measureT (n m : ℤ) :
    ∫ x, (T ℝ n).eval x * (T ℝ m).eval x ∂measureT =
    ((∫ x, (T ℝ (n + m)).eval x ∂measureT) +
     (∫ x, (T ℝ (n - m)).eval x ∂measureT)) / 2 := by
  suffices ∫ x, (2 * T ℝ n * T ℝ m).eval x ∂measureT =
      (∫ x, (T ℝ (n + m)).eval x ∂measureT) +
      (∫ x, (T ℝ (n - m)).eval x ∂measureT) by
    simp_rw [eval_mul, eval_ofNat, mul_assoc] at this
    rw [MeasureTheory.integral_const_mul] at this
    grind
  simp_rw [T_mul_T, eval_add]
  rw [MeasureTheory.integral_add
    (integrable_measureT (by fun_prop)) (integrable_measureT (by fun_prop))]
/-
**Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT_of_ne** 是 M
athlib 中的一个定理，位于命名空间 `Polynomial.Chebyshev`。
形式化陈述：integral_eval_T_real_mul_eval_T_real_measureT_of_ne {n m : Nat} (h : n != 
m) : ∫ x, (T Real n).eval x * (T Real m).eval x ∂measureT = 0
参数：h : n != m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT`：inte
gral_eval_T_real_mul_eval_T_real_measureT (n m : Int) : ∫ x, (T Real n).eval x *
 (T Real m).eval x ∂measureT = ((∫ x, (T Real (n + m)).e…
· 使用定理 `Polynomial.Chebyshev.integral_eval_T_real_measureT_of_ne_zero`：integral_
eval_T_real_measureT_of_ne_zero {n : Int} (hn : n != 0) : ∫ x, (T Real n).eval x
 ∂measureT = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_eval_T_real_mul_eval_T_real_measureT_of_ne {n m : ℕ} (h : n ≠ m) :
    ∫ x, (T ℝ n).eval x * (T ℝ m).eval x ∂measureT = 0 := by
  rw [integral_eval_T_real_mul_eval_T_real_measureT,
    integral_eval_T_real_measureT_of_ne_zero (by grind),
    integral_eval_T_real_measureT_of_ne_zero (by grind)]
  simp
/-
**Polynomial.Chebyshev.integral_eval_T_real_mul_self_measureT_zero** 是 Mathlib 中
的一个定理，位于命名空间 `Polynomial.Chebyshev`。
形式化陈述：integral_eval_T_real_mul_self_measureT_zero : ∫ x, (T Real 0).eval x * (T 
Real 0).eval x ∂measureT = π
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.Chebyshev.T_zero`：T_zero : T R 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.Chebyshev.integral_eval_T_real_measureT_zero`：integral_eval_T
_real_measureT_zero : ∫ x, (T Real 0).eval x ∂measureT = π
-/
theorem integral_eval_T_real_mul_self_measureT_zero :
    ∫ x, (T ℝ 0).eval x * (T ℝ 0).eval x ∂measureT = π := by
  simp_rw [← eval_mul, show (T ℝ 0) * (T ℝ 0) = T ℝ 0 by simp]
  exact integral_eval_T_real_measureT_zero
/-
**Polynomial.Chebyshev.integral_T_real_mul_self_measureT_of_ne_zero** 是 Mathlib 
中的一个定理，位于命名空间 `Polynomial.Chebyshev`。
形式化陈述：integral_T_real_mul_self_measureT_of_ne_zero {n : Nat} (hn : n != 0) : ∫ x
, (T Real n).eval x * (T Real n).eval x ∂measureT = π / 2
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT`：inte
gral_eval_T_real_mul_eval_T_real_measureT (n m : Int) : ∫ x, (T Real n).eval x *
 (T Real m).eval x ∂measureT = ((∫ x, (T Real (n + m)).e…
· 使用定理 `Polynomial.Chebyshev.integral_eval_T_real_measureT_of_ne_zero`：integral_
eval_T_real_measureT_of_ne_zero {n : Int} (hn : n != 0) : ∫ x, (T Real n).eval x
 ∂measureT = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Polynomial.Chebyshev.integral_eval_T_real_measureT_zero`：integral_eval_T
_real_measureT_zero : ∫ x, (T Real 0).eval x ∂measureT = π
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem integral_T_real_mul_self_measureT_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    ∫ x, (T ℝ n).eval x * (T ℝ n).eval x ∂measureT = π / 2 := by
  rw [integral_eval_T_real_mul_eval_T_real_measureT,
    integral_eval_T_real_measureT_of_ne_zero (by grind), sub_self,
    integral_eval_T_real_measureT_zero, zero_add]

end Polynomial.Chebyshev

