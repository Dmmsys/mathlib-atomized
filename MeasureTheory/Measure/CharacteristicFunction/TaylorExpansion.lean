/-
Copyright (c) 2024 Thomas Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Zhu, Etienne Marion
-/
module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Probability.Notation

/-!
# Taylor expansion of the characteristic function

This file provides the Taylor expansion of the characteristic function of a measure at `0`.

## Main statements

* `taylorWithinEval_charFun_zero`: If a finite measure `μ` over `ℝ` admits a moment of order `n`,
  then the Taylor expansion of its characteristic function at `0` at order `n` is given by
  `t ↦ ∑ k ∈ Finset.range (n + 1), (k ! : ℂ)⁻¹ * (t * I) ^ k * ∫ x, x ^ k ∂μ`.

## Tags

characteristic function, Taylor expansion
-/

public section


open ProbabilityTheory Complex Set VectorFourier
open scoped Nat RealInnerProductSpace Topology

namespace MeasureTheory

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {μ : Measure E} [IsFiniteMeasure μ]

/-- The characteristic function of a finite measure with a moment of order `n` is `C^n`.
See `contDiff_charFun'` for the version proving `C^∞` by assuming all moments exist. -/
@[fun_prop]
/-
**MeasureTheory.contDiff_charFun** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：contDiff_charFun {n : Nat} (hint : MemLp id n μ) : ContDiff Real n (charFu
n μ)
参数：hint : MemLp id n μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `MeasureTheory.charFun_eq_fourierIntegral'`：charFun_eq_fourierIntegral' (
t : E) : charFun μ t = VectorFourier.fourierIntegral fourierChar μ (innerₗ E) 1 
(-(2 * π)⁻¹ • t)
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `VectorFourier.contDiff_fourierIntegral`：contDiff_fourierIntegral {N : Na
t∞} (hf : forall (n : Nat), n <= N -> Integrable (fun v => ‖v‖ ^ n * ‖f v‖) μ) :
 ContDiff Real N (fourierInt…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CStarRing.norm_of_mem_unitary`：norm_of_mem_unitary [Nontrivial E] {U : E
} (hU : U in unitary E) : ‖U‖ = 1
· 使用定理 `RCLike.instCStarRing`：∀ {K : Type u_1} [inst : RCLike K], CStarRing K
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MeasureTheory.MemLp.integrable_norm_pow'`：∀ {α : Type u_1} {β : Type u_2
} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGro
up β]   [MeasureTheory.IsFinit…
· 使用定理 `MeasureTheory.MemLp.mono_exponent`：∀ {α : Type u_1} {ε : Type u_2} {m : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → ε}   [inst : Topologic
alSpace ε] [inst_1 : Co…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
The characteristic function of a finite measure with a moment of order `n` is `C
^n`.
See `contDiff_charFun'` for the version proving `C^∞` by assuming all moments ex
ist.
-/
theorem contDiff_charFun {n : ℕ} (hint : MemLp id n μ) :
    ContDiff ℝ n (charFun μ) := by
  simp_rw [funext charFun_eq_fourierIntegral']
  refine (contDiff_fourierIntegral (L := innerSL ℝ) fun k hk ↦ ?_).comp (by fun_prop)
  simp only [Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one]
  refine MemLp.integrable_norm_pow' (hint.mono_exponent (by simp_all))

/-- The characteristic function of a measure with all moments is `C^∞`. See `contDiff_charFun`
for the version proving only `C^n` by only assuming that the moment of order `n` exists. -/
@[fun_prop]
/-
**MeasureTheory.contDiff_charFun'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：contDiff_charFun' {n : Nat∞} (hint : forall (k : Nat), MemLp id k μ) : Con
tDiff Real n (charFun μ)
参数：hint : forall (k : Nat), MemLp id k μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `MeasureTheory.charFun_eq_fourierIntegral'`：charFun_eq_fourierIntegral' (
t : E) : charFun μ t = VectorFourier.fourierIntegral fourierChar μ (innerₗ E) 1 
(-(2 * π)⁻¹ • t)
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `VectorFourier.contDiff_fourierIntegral`：contDiff_fourierIntegral {N : Na
t∞} (hf : forall (n : Nat), n <= N -> Integrable (fun v => ‖v‖ ^ n * ‖f v‖) μ) :
 ContDiff Real N (fourierInt…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CStarRing.norm_of_mem_unitary`：norm_of_mem_unitary [Nontrivial E] {U : E
} (hU : U in unitary E) : ‖U‖ = 1
· 使用定理 `RCLike.instCStarRing`：∀ {K : Type u_1} [inst : RCLike K], CStarRing K
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MeasureTheory.MemLp.integrable_norm_pow'`：∀ {α : Type u_1} {β : Type u_2
} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGro
up β]   [MeasureTheory.IsFinit…
· 使用定理 `MeasureTheory.MemLp.mono_exponent`：∀ {α : Type u_1} {ε : Type u_2} {m : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → ε}   [inst : Topologic
alSpace ε] [inst_1 : Co…
· 使用定理 `contDiff_const_smul`：contDiff_const_smul (c : R) : ContDiff 𝕜 n fun p : 
F => c • p
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …

--- 原说明 ---
The characteristic function of a measure with all moments is `C^∞`. See `contDif
f_charFun`
for the version proving only `C^n` by only assuming that the moment of order `n`
 exists.
-/
theorem contDiff_charFun' {n : ℕ∞} (hint : ∀ (k : ℕ), MemLp id k μ) :
    ContDiff ℝ n (charFun μ) := by
  simp_rw [funext charFun_eq_fourierIntegral']
  refine (contDiff_fourierIntegral (L := innerSL ℝ) fun k hk ↦ ?_).comp (by fun_prop)
  simp only [Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one]
  refine MemLp.integrable_norm_pow' ((hint k).mono_exponent (by simp_all))

@[fun_prop]
/-
**MeasureTheory.continuous_charFun** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：continuous_charFun : Continuous (charFun μ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiff_zero`：contDiff_zero : ContDiff 𝕜 0 f ↔ Continuous f
· 使用定理 `MeasureTheory.contDiff_charFun`：contDiff_charFun {n : Nat} (hint : MemLp
 id n μ) : ContDiff Real n (charFun μ)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `aestronglyMeasurable_id`：∀ {α : Type u_5} [inst : TopologicalSpace α] [T
opologicalSpace.PseudoMetrizableSpace α] {x : MeasurableSpace α}   [OpensMeasura
bleSpace α] […
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
-/
lemma continuous_charFun : Continuous (charFun μ) := by
  refine contDiff_zero.1 (contDiff_charFun ?_)
  simpa using by fun_prop
/-
**MeasureTheory.iteratedFDeriv_charFun** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：iteratedFDeriv_charFun {n : Nat} {t : E} (hint : MemLp id n μ) (x : Fin n 
-> E) : iteratedFDeriv Real n (charFun μ) t x = I ^ n * ∫ y, (∏ i, ⟪y, x i⟫) * e
xp (⟪y, t⟫ * I) ∂μ
参数：hint : MemLp id n μ；x : Fin n -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CStarRing.norm_of_mem_unitary`：norm_of_mem_unitary [Nontrivial E] {U : E
} (hU : U in unitary E) : ‖U‖ = 1
· 使用定理 `RCLike.instCStarRing`：∀ {K : Type u_1} [inst : RCLike K], CStarRing K
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MeasureTheory.MemLp.integrable_norm_pow'`：∀ {α : Type u_1} {β : Type u_2
} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGro
up β]   [MeasureTheory.IsFinit…
· 使用定理 `MeasureTheory.MemLp.mono_exponent`：∀ {α : Type u_1} {ε : Type u_2} {m : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → ε}   [inst : Topologic
alSpace ε] [inst_1 : Co…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
（共 119 条，此处仅展示前 30 条）
-/
theorem iteratedFDeriv_charFun {n : ℕ} {t : E} (hint : MemLp id n μ) (x : Fin n → E) :
    iteratedFDeriv ℝ n (charFun μ) t x = I ^ n * ∫ y, (∏ i, ⟪y, x i⟫) * exp (⟪y, t⟫ * I) ∂μ := by
  have h : innerₗ E = (innerSL ℝ).toLinearMap₁₂ := rfl
  have hint' (k : ℕ) (hk : k ≤ (n : ℕ∞)) : Integrable (fun x ↦ ‖x‖ ^ k * ‖(1 : E → ℂ) x‖) μ := by
    simp only [Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one]
    refine MemLp.integrable_norm_pow' (hint.mono_exponent (by simp_all))
  simp_rw [funext charFun_eq_fourierIntegral']
  rw [iteratedFDeriv_comp_const_smul]
  swap
  · rw [h]
    exact contDiff_fourierIntegral _ hint'
  simp only [mul_inv_rev, neg_smul]
  rw [h, iteratedFDeriv_fourierIntegral _ hint' (by fun_prop) le_rfl]
  simp only [smul_apply, real_smul, ofReal_pow, ofReal_neg, ofReal_mul, ofReal_inv, ofReal_ofNat,
    ofReal_prod]
  rw [fourierIntegral_continuousMultilinearMap_apply Real.continuous_fourierChar]
  swap;
  · exact integrable_fourierPowSMulRight _ (by simpa using hint.integrable_norm_pow') (by fun_prop)
  simp only [fourierIntegral, Real.fourierChar, Circle.coe_exp, ofReal_mul,
    ofReal_ofNat, innerSL, map_neg, map_smul, ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
    LinearMap.mkContinuous₂_apply, innerₛₗ_apply_apply, smul_eq_mul, neg_neg, AddChar.coe_mk,
    ofReal_inv, fourierPowSMulRight_apply, Pi.ofNat_apply, real_smul, ofReal_prod, mul_one,
    Circle.smul_def]
  simp_rw [mul_left_comm (exp _), integral_const_mul, ← mul_assoc, ← mul_pow]
  field_simp
  congr with
  ring

end InnerProductSpace

section Real

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

/-
**MeasureTheory.iteratedDeriv_charFun** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：iteratedDeriv_charFun {n : Nat} {t : Real} (hint : MemLp id n μ) : iterate
dDeriv n (charFun μ) t = I ^ n * ∫ x, x ^ n * exp (t * x * I) ∂μ
参数：hint : MemLp id n μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDeriv.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{F : Type u_2} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] (n :
 ℕ) (f :…
· 使用定理 `MeasureTheory.iteratedFDeriv_charFun`：iteratedFDeriv_charFun {n : Nat} {
t : E} (hint : MemLp id n μ) (x : Fin n -> E) : iteratedFDeriv Real n (charFun μ
) t x = I ^ n * ∫ y, (∏ i,…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `conj_trivial`：∀ {R : Type u} [inst : CommSemiring R] [inst_1 : StarRing 
R] [TrivialStar R] (a : R), (starRingEnd R) a = a
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDeriv_charFun {n : ℕ} {t : ℝ} (hint : MemLp id n μ) :
    iteratedDeriv n (charFun μ) t = I ^ n * ∫ x, x ^ n * exp (t * x * I) ∂μ := by
  rw [iteratedDeriv, iteratedFDeriv_charFun hint]
  simp
/-
**MeasureTheory.iteratedDeriv_charFun_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：iteratedDeriv_charFun_zero {n : Nat} (hint : MemLp id n μ) : iteratedDeriv
 n (charFun μ) 0 = I ^ n * ∫ x, x ^ n ∂μ
参数：hint : MemLp id n μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.iteratedDeriv_charFun`：iteratedDeriv_charFun {n : Nat} {t 
: Real} (hint : MemLp id n μ) : iteratedDeriv n (charFun μ) t = I ^ n * ∫ x, x ^
 n * exp (t * x * I) ∂μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Complex.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `integral_complex_ofReal`：integral_complex_ofReal {f : X -> Real} : ∫ x, 
(f x : Complex) ∂μ = ∫ x, f x ∂μ
-/
theorem iteratedDeriv_charFun_zero {n : ℕ} (hint : MemLp id n μ) :
    iteratedDeriv n (charFun μ) 0 = I ^ n * ∫ x, x ^ n ∂μ := by
  simp [iteratedDeriv_charFun hint]
  norm_cast
/-
**MeasureTheory.taylorWithinEval_charFun_zero** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory`。
形式化陈述：taylorWithinEval_charFun_zero {n : Nat} (hint : MemLp id n μ) (t : Real) :
 taylorWithinEval (charFun μ) n univ 0 t = ∑ k in Finset.range (n + 1), (k ! : C
omplex)⁻¹ * (t * I) ^ k * ∫ x, x ^ k ∂μ
参数：hint : MemLp id n μ；t : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `taylor_within_apply`：taylor_within_apply (f : Real -> E) (n : Nat) (s : 
Set Real) (x₀ x : Real) : taylorWithinEval f n s x₀ x = ∑ k in Finset.range (n +
 1), ((k …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `RCLike.real_smul_eq_coe_mul`：real_smul_eq_coe_mul (r : Real) (z : K) : r
 • z = (r : K) * z
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `algebraMap.coe_mul`：coe_mul (a b : R) : (↑(a * b : R) : A) = ↑a * ↑b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : K) = (r : K)⁻
¹
· 使用定理 `algebraMap.coe_natCast`：coe_natCast (a : Nat) : (↑(a : R) : A) = a
· 使用定理 `algebraMap.coe_pow`：coe_pow (a : R) (n : Nat) : (↑(a ^ n : R) : A) = (a 
: A) ^ n
· 使用定理 `MeasureTheory.MemLp.mono_exponent`：∀ {α : Type u_1} {ε : Type u_2} {m : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → ε}   [inst : Topologic
alSpace ε] [inst_1 : Co…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_univ`：iteratedDerivWithin_univ : iteratedDerivWithin
 n f univ = iteratedDeriv n f
· 使用定理 `MeasureTheory.iteratedDeriv_charFun_zero`：iteratedDeriv_charFun_zero {n 
: Nat} (hint : MemLp id n μ) : iteratedDeriv n (charFun μ) 0 = I ^ n * ∫ x, x ^ 
n ∂μ
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma taylorWithinEval_charFun_zero {n : ℕ} (hint : MemLp id n μ) (t : ℝ) :
    taylorWithinEval (charFun μ) n univ 0 t
      = ∑ k ∈ Finset.range (n + 1), (k ! : ℂ)⁻¹ * (t * I) ^ k * ∫ x, x ^ k ∂μ := by
  simp_rw [taylor_within_apply, sub_zero, RCLike.real_smul_eq_coe_mul]
  refine Finset.sum_congr rfl fun k hkn ↦ ?_
  push_cast
  have hint' : MemLp id k μ := hint.mono_exponent (by simp_all)
  simp [iteratedDeriv_charFun_zero hint', mul_pow, mul_comm, mul_assoc, mul_left_comm]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ℝ}
/-
**MeasureTheory.taylorWithinEval_charFun_two_zero** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory`。
形式化陈述：taylorWithinEval_charFun_two_zero (hX : AEMeasurable X P) (hint : MemLp id
 2 (P.map X)) (t : Real) : taylorWithinEval (charFun (P.map X)) 2 univ 0 t = 1 +
 (P[X] : Real) * t * I - (P[X ^ 2] : Real) * t ^ 2 / 2
参数：hX : AEMeasurable X P；hint : MemLp id 2 (P.map X)；t : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.Measure.isProbabilityMeasure_map`：∀ {α : Type u_1} {β : Ty
pe u_2} {m0 : MeasurableSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.M
easure α}   [MeasureTheory.IsProbabi…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `MeasureTheory.probReal_univ`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ],   μ.real Se
t.univ = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `aestronglyMeasurable_id`：∀ {α : Type u_5} [inst : TopologicalSpace α] [T
opologicalSpace.PseudoMetrizableSpace α] {x : MeasurableSpace α}   [OpensMeasura
bleSpace α] […
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.fun_pow`：∀ {α : Type u_1} {β : Type u
_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Me
asure α}   {f : α → β} [inst_1 :…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
（共 102 条，此处仅展示前 30 条）
-/
lemma taylorWithinEval_charFun_two_zero (hX : AEMeasurable X P)
    (hint : MemLp id 2 (P.map X)) (t : ℝ) :
    taylorWithinEval (charFun (P.map X)) 2 univ 0 t =
      1 + (P[X] : ℝ) * t * I - (P[X ^ 2] : ℝ) * t ^ 2 / 2 := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX
  convert! taylorWithinEval_charFun_zero hint t with x
  simp only [Pi.pow_apply, Nat.reduceAdd, Finset.sum_range_succ, Finset.range_one,
    Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, mul_one,
    integral_const, probReal_univ, smul_eq_mul, ofReal_one, Nat.factorial_one, pow_one, one_mul,
    Nat.factorial_two, Nat.cast_ofNat]
  rw [integral_map, integral_map]
  any_goals fun_prop
  simp [field]
  ring
/-
**MeasureTheory.taylorWithinEval_charFun_two_zero'** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory`。
形式化陈述：taylorWithinEval_charFun_two_zero' (hX : AEMeasurable X P) (h0 : P[X] = 0)
 (h1 : P[X ^ 2] = 1) (t : Real) : taylorWithinEval (charFun (P.map X)) 2 univ 0 
t = 1 - t ^ 2 / 2
参数：hX : AEMeasurable X P；h0 : P[X] = 0；h1 : P[X ^ 2] = 1；t : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.taylorWithinEval_charFun_two_zero`：taylorWithinEval_charFu
n_two_zero (hX : AEMeasurable X P) (hint : MemLp id 2 (P.map X)) (t : Real) : ta
ylorWithinEval (charFun (P.map X)) 2 …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.memLp_two_iff_integrable_sq`：memLp_two_iff_integrable_sq {
f : α -> Real} (hf : AEStronglyMeasurable f μ) : MemLp f 2 μ ↔ Integrable (fun x
 => f x ^ 2) μ
· 使用定理 `aestronglyMeasurable_id`：∀ {α : Type u_5} [inst : TopologicalSpace α] [T
opologicalSpace.PseudoMetrizableSpace α] {x : MeasurableSpace α}   [OpensMeasura
bleSpace α] […
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.Integrable.of_integral_ne_zero`：∀ {α : Type u_1} {G : Type
 u_5} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : MeasurableSp
ace α}   {μ : MeasureTheory.Measur…
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.fun_pow`：∀ {α : Type u_1} {β : Type u
_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Me
asure α}   {f : α → β} [inst_1 :…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma taylorWithinEval_charFun_two_zero' (hX : AEMeasurable X P)
    (h0 : P[X] = 0) (h1 : P[X ^ 2] = 1) (t : ℝ) :
    taylorWithinEval (charFun (P.map X)) 2 univ 0 t = 1 - t ^ 2 / 2 := by
  rw [taylorWithinEval_charFun_two_zero hX, h0, h1]
  · simp
  refine (memLp_two_iff_integrable_sq (by fun_prop)).2 (.of_integral_ne_zero ?_)
  rw [integral_map]
  any_goals fun_prop
  simp [← Pi.pow_apply, h1]
/-
**MeasureTheory.taylor_charFun_two** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：taylor_charFun_two (hX : AEMeasurable X P) (h0 : P[X] = 0) (h1 : P[X ^ 2] 
= 1) : (fun t => charFun (P.map X) t - (1 - t ^ 2 / 2)) =o[𝓝 0] fun t => t ^ 2
参数：hX : AEMeasurable X P；h0 : P[X] = 0；h1 : P[X ^ 2] = 1。
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.taylorWithinEval_charFun_two_zero'`：taylorWithinEval_charF
un_two_zero' (hX : AEMeasurable X P) (h0 : P[X] = 0) (h1 : P[X ^ 2] = 1) (t : Re
al) : taylorWithinEval (charFun (P.map…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `taylor_isLittleO_univ`：taylor_isLittleO_univ {f : Real -> E} {x₀ : Real}
 {n : Nat} (hf : ContDiff Real n f) : (fun x => f x - taylorWithinEval f n univ 
x₀ x) =o[𝓝 …
· 使用定理 `MeasureTheory.contDiff_charFun`：contDiff_charFun {n : Nat} (hint : MemLp
 id n μ) : ContDiff Real n (charFun μ)
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.memLp_two_iff_integrable_sq`：memLp_two_iff_integrable_sq {
f : α -> Real} (hf : AEStronglyMeasurable f μ) : MemLp f 2 μ ↔ Integrable (fun x
 => f x ^ 2) μ
· 使用定理 `aestronglyMeasurable_id`：∀ {α : Type u_5} [inst : TopologicalSpace α] [T
opologicalSpace.PseudoMetrizableSpace α] {x : MeasurableSpace α}   [OpensMeasura
bleSpace α] […
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.Integrable.of_integral_ne_zero`：∀ {α : Type u_1} {G : Type
 u_5} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : MeasurableSp
ace α}   {μ : MeasureTheory.Measur…
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.fun_pow`：∀ {α : Type u_1} {β : Type u
_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Me
asure α}   {f : α → β} [inst_1 :…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
（共 31 条，此处仅展示前 30 条）
-/
lemma taylor_charFun_two (hX : AEMeasurable X P) (h0 : P[X] = 0) (h1 : P[X ^ 2] = 1) :
    (fun t ↦ charFun (P.map X) t - (1 - t ^ 2 / 2)) =o[𝓝 0] fun t ↦ t ^ 2 := by
  simp_rw [← taylorWithinEval_charFun_two_zero' (by fun_prop) h0 h1]
  convert! taylor_isLittleO_univ ?_
  · simp
  refine contDiff_charFun <|
    (memLp_two_iff_integrable_sq (by fun_prop)).2 (.of_integral_ne_zero ?_)
  rw [integral_map]
  any_goals fun_prop
  simp_all

end Real

end MeasureTheory

