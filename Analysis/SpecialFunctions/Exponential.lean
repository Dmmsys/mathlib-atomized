/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Eric Wieser
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Topology.MetricSpace.CauSeqFilter

/-!
# Calculus results on exponential in a Banach algebra

In this file, we prove basic properties about the derivative of the exponential map `exp`
in a Banach algebra `𝔸` over a field `𝕂`. We keep them separate from the main file
`Analysis.Normed.Algebra.Exponential` in order to minimize dependencies.

## Main results

We prove most results for an arbitrary field `𝕂`, and then specialize to `𝕂 = ℝ` or `𝕂 = ℂ`.

### General case

- `hasStrictFDerivAt_exp_zero_of_radius_pos` : `NormedSpace.exp` has strict Fréchet derivative
  `1 : 𝔸 →L[𝕂] 𝔸` at zero, as long as it converges on a neighborhood of zero
  (see also `hasStrictDerivAt_exp_zero_of_radius_pos` for the case `𝔸 = 𝕂`)
- `hasStrictFDerivAt_exp_of_lt_radius` : if `𝕂` has characteristic zero and `𝔸` is commutative,
  then given a point `x` in the disk of convergence, `NormedSpace.exp` has strict Fréchet
  derivative `NormedSpace.exp x • 1 : 𝔸 →L[𝕂] 𝔸` at x
  (see also `hasStrictDerivAt_exp_of_lt_radius` for the case `𝔸 = 𝕂`)
- `hasStrictFDerivAt_exp_smul_const_of_mem_ball`: even when `𝔸` is non-commutative,
  if we have an intermediate algebra `𝕊` which is commutative, the function
  `(u : 𝕊) ↦ NormedSpace.exp (u • x)`, still has strict Fréchet derivative
  `NormedSpace.exp (t • x) • (1 : 𝕊 →L[𝕂] 𝕊).smulRight x` at `t` if
  `t • x` is in the radius of convergence.

### `𝕂 = ℝ` or `𝕂 = ℂ`

- `hasStrictFDerivAt_exp_zero` : `NormedSpace.exp` has strict Fréchet derivative `1 : 𝔸 →L[𝕂] 𝔸`
  at zero (see also `hasStrictDerivAt_exp_zero` for the case `𝔸 = 𝕂`)
- `hasStrictFDerivAt_exp` : if `𝔸` is commutative, then given any point `x`, `NormedSpace.exp`
  has strict Fréchet derivative `NormedSpace.exp x • 1 : 𝔸 →L[𝕂] 𝔸` at x
  (see also `hasStrictDerivAt_exp` for the case `𝔸 = 𝕂`)
- `hasStrictFDerivAt_exp_smul_const`: even when `𝔸` is non-commutative, if we have
  an intermediate algebra `𝕊` which is commutative, the function
  `(u : 𝕊) ↦ NormedSpace.exp (u • x)` still has strict Fréchet derivative
  `NormedSpace.exp (t • x) • (1 : 𝔸 →L[𝕂] 𝔸).smulRight x` at `t`.

### Compatibility with `Real.exp` and `Complex.exp`

- `Complex.exp_eq_exp_ℂ` : `Complex.exp = NormedSpace.exp ℂ ℂ`
- `Real.exp_eq_exp_ℝ` : `Real.exp = NormedSpace.exp ℝ ℝ`

-/

public section


open Filter RCLike ContinuousMultilinearMap NormedField NormedSpace Asymptotics

open scoped Nat Topology ENNReal

section AnyFieldAnyAlgebra

variable {𝕂 𝔸 : Type*} [NontriviallyNormedField 𝕂] [NormedRing 𝔸] [CharZero 𝕂] [NormedAlgebra 𝕂 𝔸]
  [CompleteSpace 𝔸]

/-- The exponential in a Banach algebra `𝔸` over a normed field `𝕂` has strict Fréchet derivative
`1 : 𝔸 →L[𝕂] 𝔸` at zero, as long as it converges on a neighborhood of zero. -/
/-
**hasStrictFDerivAt_exp_zero_of_radius_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_exp_zero_of_radius_pos (h : 0 < (expSeries 𝕂 𝔸).radius) 
: HasStrictFDerivAt exp (1 : 𝔸 ->L[𝕂] 𝔸) 0
参数：h : 0 < (expSeries 𝕂 𝔸).radius。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.expSeries_apply_eq`：expSeries_apply_eq (x : 𝔸) (n : Nat) : (
expSeries 𝕂 𝔸 n fun _ => x) = (n !⁻¹ : 𝕂) • x ^ n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasFPowerSeriesAt.hasStrictFDerivAt`：HasFPowerSeriesAt.hasStrictFDerivAt
 (h : HasFPowerSeriesAt f p x) : HasStrictFDerivAt f (continuousMultilinearCurry
Fin1 𝕜 E F (p 1)) x
· 使用定理 `NormedSpace.hasFPowerSeriesAt_exp_zero_of_radius_pos`：hasFPowerSeriesAt_
exp_zero_of_radius_pos [CharZero 𝕂] (h : 0 < (expSeries 𝕂 𝔸).radius) : HasFPower
SeriesAt exp (expSeries 𝕂 𝔸) 0

--- 原说明 ---
The exponential in a Banach algebra `𝔸` over a normed field `𝕂` has strict Fréch
et derivative
`1 : 𝔸 →L[𝕂] 𝔸` at zero, as long as it converges on a neighborhood of zero.
-/
theorem hasStrictFDerivAt_exp_zero_of_radius_pos (h : 0 < (expSeries 𝕂 𝔸).radius) :
    HasStrictFDerivAt exp (1 : 𝔸 →L[𝕂] 𝔸) 0 := by
  convert! (hasFPowerSeriesAt_exp_zero_of_radius_pos h).hasStrictFDerivAt
  ext x
  change x = expSeries 𝕂 𝔸 1 fun _ => x
  simp [expSeries_apply_eq, Nat.factorial]

/-- The exponential in a Banach algebra `𝔸` over a normed field `𝕂` has Fréchet derivative
`1 : 𝔸 →L[𝕂] 𝔸` at zero, as long as it converges on a neighborhood of zero. -/
/-
**hasFDerivAt_exp_zero_of_radius_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_exp_zero_of_radius_pos (h : 0 < (expSeries 𝕂 𝔸).radius) : HasF
DerivAt exp (1 : 𝔸 ->L[𝕂] 𝔸) 0
参数：h : 0 < (expSeries 𝕂 𝔸).radius。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `hasStrictFDerivAt_exp_zero_of_radius_pos`：hasStrictFDerivAt_exp_zero_of_
radius_pos (h : 0 < (expSeries 𝕂 𝔸).radius) : HasStrictFDerivAt exp (1 : 𝔸 ->L[𝕂
] 𝔸) 0

--- 原说明 ---
The exponential in a Banach algebra `𝔸` over a normed field `𝕂` has Fréchet deri
vative
`1 : 𝔸 →L[𝕂] 𝔸` at zero, as long as it converges on a neighborhood of zero.
-/
theorem hasFDerivAt_exp_zero_of_radius_pos (h : 0 < (expSeries 𝕂 𝔸).radius) :
    HasFDerivAt exp (1 : 𝔸 →L[𝕂] 𝔸) 0 :=
  (hasStrictFDerivAt_exp_zero_of_radius_pos h).hasFDerivAt

end AnyFieldAnyAlgebra

section AnyFieldCommAlgebra

variable {𝕂 𝔸 : Type*} [NontriviallyNormedField 𝕂] [NormedCommRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [CompleteSpace 𝔸] [CharZero 𝕂]

/-- The exponential map in a commutative Banach algebra `𝔸` over a normed field `𝕂` of
characteristic zero has Fréchet derivative `NormedSpace.exp x • 1 : 𝔸 →L[𝕂] 𝔸`
at any point `x` in the disk of convergence. -/
/-
**hasFDerivAt_exp_of_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_exp_of_mem_ball {x : 𝔸} (hx : x in Metric.eball (0 : 𝔸) (expSe
ries 𝕂 𝔸).radius) : HasFDerivAt exp (exp x • (1 : 𝔸 ->L[𝕂] 𝔸)) x
参数：hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasFDerivAt_iff_isLittleO_nhds_zero`：hasFDerivAt_iff_isLittleO_nhds_zero
 : HasFDerivAt f f' x ↔ (fun h : E => f (x + h) - f x - f' h) =o[𝓝 0] fun h => h
· 使用定理 `Metric.eball_mem_nhds`：eball_mem_nhds (x : α) {ε : Real>=0∞} (ε0 : 0 < ε
) : eball x ε in 𝓝 x
· 使用定理 `LT.lt.pos`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `NormedSpace.exp_add_of_mem_ball`：exp_add_of_mem_ball [CharZero 𝕂] {x y :
 𝔸} (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) (hy : y in Metric.eb
all (0 : 𝔸) (expSerie…
· 使用定理 `NormedSpace.exp_zero`：exp_zero : exp (0 : 𝔸) = 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `ContinuousLinearMap.id_apply`：id_apply (x : M₁) : ContinuousLinearMap.id
 R₁ M₁ x = x
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
The exponential map in a commutative Banach algebra `𝔸` over a normed field `𝕂` 
of
characteristic zero has Fréchet derivative `NormedSpace.exp x • 1 : 𝔸 →L[𝕂] 𝔸`
at any point `x` in the disk of convergence.
-/
theorem hasFDerivAt_exp_of_mem_ball {x : 𝔸}
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasFDerivAt exp (exp x • (1 : 𝔸 →L[𝕂] 𝔸)) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  suffices
    (fun h => exp x * (exp (0 + h) - exp 0 - ContinuousLinearMap.id 𝕂 𝔸 h)) =ᶠ[𝓝 0] fun h =>
      exp (x + h) - exp x - exp x • ContinuousLinearMap.id 𝕂 𝔸 h by
    refine (IsLittleO.const_mul_left ?_ _).congr' this (EventuallyEq.refl _ _)
    rw [← hasFDerivAt_iff_isLittleO_nhds_zero]
    exact hasFDerivAt_exp_zero_of_radius_pos hx.pos
  have : ∀ᶠ h in 𝓝 (0 : 𝔸), h ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius :=
    Metric.eball_mem_nhds _ hx.pos
  filter_upwards [this] with _ hh
  rw [exp_add_of_mem_ball hx hh, exp_zero, zero_add, ContinuousLinearMap.id_apply, smul_eq_mul]
  ring

/-- The exponential map in a commutative Banach algebra `𝔸` over a normed field `𝕂` of
characteristic zero has strict Fréchet derivative `NormedSpace.exp x • 1 : 𝔸 →L[𝕂] 𝔸`
at any point `x` in the disk of convergence. -/
/-
**hasStrictFDerivAt_exp_of_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_exp_of_mem_ball {x : 𝔸} (hx : x in Metric.eball (0 : 𝔸) 
(expSeries 𝕂 𝔸).radius) : HasStrictFDerivAt exp (exp x • (1 : 𝔸 ->L[𝕂] 𝔸)) x
参数：hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
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
· 使用定理 `NormedSpace.analyticAt_exp_of_mem_ball`：analyticAt_exp_of_mem_ball [Char
Zero 𝕂] (x : 𝔸) (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : Analyt
icAt 𝕂 exp x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFPowerSeriesAt.hasStrictFDerivAt`：HasFPowerSeriesAt.hasStrictFDerivAt
 (h : HasFPowerSeriesAt f p x) : HasStrictFDerivAt f (continuousMultilinearCurry
Fin1 𝕜 E F (p 1)) x
· 使用定理 `HasFDerivAt.unique`：HasFDerivAt.unique (h₀ : HasFDerivAt f f' x) (h₁ : H
asFDerivAt f f₁' x) : f' = f₁'
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFPowerSeriesAt.hasFDerivAt`：HasFPowerSeriesAt.hasFDerivAt (h : HasFPo
werSeriesAt f p x) : HasFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p 1)) 
x
· 使用定理 `hasFDerivAt_exp_of_mem_ball`：hasFDerivAt_exp_of_mem_ball {x : 𝔸} (hx : x
 in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : HasFDerivAt exp (exp x • (1 :
 𝔸 ->L[𝕂] 𝔸)) x

--- 原说明 ---
The exponential map in a commutative Banach algebra `𝔸` over a normed field `𝕂` 
of
characteristic zero has strict Fréchet derivative `NormedSpace.exp x • 1 : 𝔸 →L[
𝕂] 𝔸`
at any point `x` in the disk of convergence.
-/
theorem hasStrictFDerivAt_exp_of_mem_ball {x : 𝔸}
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasStrictFDerivAt exp (exp x • (1 : 𝔸 →L[𝕂] 𝔸)) x :=
  let ⟨_, hp⟩ := analyticAt_exp_of_mem_ball x hx
  hp.hasFDerivAt.unique (hasFDerivAt_exp_of_mem_ball hx) ▸ hp.hasStrictFDerivAt

end AnyFieldCommAlgebra

section deriv

variable {𝕂 : Type*} [NontriviallyNormedField 𝕂] [CompleteSpace 𝕂] [CharZero 𝕂]

/-- The exponential map in a complete normed field `𝕂` of characteristic zero has strict derivative
`NormedSpace.exp x` at any point `x` in the disk of convergence. -/
/-
**hasStrictDerivAt_exp_of_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictDerivAt_exp_of_mem_ball {x : 𝕂} (hx : x in Metric.eball (0 : 𝕂) (
expSeries 𝕂 𝕂).radius) : HasStrictDerivAt exp (exp x) x
参数：hx : x in Metric.eball (0 : 𝕂) (expSeries 𝕂 𝕂).radius。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
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
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_apply_eq_self`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : Fu
nLike F α α} {inst_1 : One F} [self : IsOneApplyEqSelf F α]   (x : α), 1 x = x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `HasStrictFDerivAt.hasStrictDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `hasStrictFDerivAt_exp_of_mem_ball`：hasStrictFDerivAt_exp_of_mem_ball {x 
: 𝔸} (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : HasStrictFDerivAt
 exp (exp x • (1 : 𝔸 ->…

--- 原说明 ---
The exponential map in a complete normed field `𝕂` of characteristic zero has st
rict derivative
`NormedSpace.exp x` at any point `x` in the disk of convergence.
-/
theorem hasStrictDerivAt_exp_of_mem_ball {x : 𝕂}
    (hx : x ∈ Metric.eball (0 : 𝕂) (expSeries 𝕂 𝕂).radius) :
    HasStrictDerivAt exp (exp x) x := by
  simpa using (hasStrictFDerivAt_exp_of_mem_ball hx).hasStrictDerivAt

/-- The exponential map in a complete normed field `𝕂` of characteristic zero has derivative
`NormedSpace.exp x` at any point `x` in the disk of convergence. -/
/-
**hasDerivAt_exp_of_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_exp_of_mem_ball {x : 𝕂} (hx : x in Metric.eball (0 : 𝕂) (expSer
ies 𝕂 𝕂).radius) : HasDerivAt exp (exp x) x
参数：hx : x in Metric.eball (0 : 𝕂) (expSeries 𝕂 𝕂).radius。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `hasStrictDerivAt_exp_of_mem_ball`：hasStrictDerivAt_exp_of_mem_ball {x : 
𝕂} (hx : x in Metric.eball (0 : 𝕂) (expSeries 𝕂 𝕂).radius) : HasStrictDerivAt ex
p (exp x) x

--- 原说明 ---
The exponential map in a complete normed field `𝕂` of characteristic zero has de
rivative
`NormedSpace.exp x` at any point `x` in the disk of convergence.
-/
theorem hasDerivAt_exp_of_mem_ball {x : 𝕂}
    (hx : x ∈ Metric.eball (0 : 𝕂) (expSeries 𝕂 𝕂).radius) : HasDerivAt exp (exp x) x :=
  (hasStrictDerivAt_exp_of_mem_ball hx).hasDerivAt

/-- The exponential map in a complete normed field `𝕂` of characteristic zero has strict derivative
`1` at zero, as long as it converges on a neighborhood of zero. -/
/-
**hasStrictDerivAt_exp_zero_of_radius_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictDerivAt_exp_zero_of_radius_pos (h : 0 < (expSeries 𝕂 𝕂).radius) :
 HasStrictDerivAt exp (1 : 𝕂) 0
参数：h : 0 < (expSeries 𝕂 𝕂).radius。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `HasStrictFDerivAt.hasStrictDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `hasStrictFDerivAt_exp_zero_of_radius_pos`：hasStrictFDerivAt_exp_zero_of_
radius_pos (h : 0 < (expSeries 𝕂 𝔸).radius) : HasStrictFDerivAt exp (1 : 𝔸 ->L[𝕂
] 𝔸) 0

--- 原说明 ---
The exponential map in a complete normed field `𝕂` of characteristic zero has st
rict derivative
`1` at zero, as long as it converges on a neighborhood of zero.
-/
theorem hasStrictDerivAt_exp_zero_of_radius_pos (h : 0 < (expSeries 𝕂 𝕂).radius) :
    HasStrictDerivAt exp (1 : 𝕂) 0 :=
  (hasStrictFDerivAt_exp_zero_of_radius_pos h).hasStrictDerivAt

/-- The exponential map in a complete normed field `𝕂` of characteristic zero has derivative
`1` at zero, as long as it converges on a neighborhood of zero. -/
/-
**hasDerivAt_exp_zero_of_radius_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_exp_zero_of_radius_pos (h : 0 < (expSeries 𝕂 𝕂).radius) : HasDe
rivAt exp (1 : 𝕂) 0
参数：h : 0 < (expSeries 𝕂 𝕂).radius。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `hasStrictDerivAt_exp_zero_of_radius_pos`：hasStrictDerivAt_exp_zero_of_ra
dius_pos (h : 0 < (expSeries 𝕂 𝕂).radius) : HasStrictDerivAt exp (1 : 𝕂) 0

--- 原说明 ---
The exponential map in a complete normed field `𝕂` of characteristic zero has de
rivative
`1` at zero, as long as it converges on a neighborhood of zero.
-/
theorem hasDerivAt_exp_zero_of_radius_pos (h : 0 < (expSeries 𝕂 𝕂).radius) :
    HasDerivAt exp (1 : 𝕂) 0 :=
  (hasStrictDerivAt_exp_zero_of_radius_pos h).hasDerivAt

end deriv

section RCLikeAnyAlgebra

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-- The exponential in a Banach algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` has strict Fréchet derivative
`1 : 𝔸 →L[𝕂] 𝔸` at zero. -/
/-
**hasStrictFDerivAt_exp_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_exp_zero : HasStrictFDerivAt exp (1 : 𝔸 ->L[𝕂] 𝔸) 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasStrictFDerivAt_exp_zero_of_radius_pos`：hasStrictFDerivAt_exp_zero_of_
radius_pos (h : 0 < (expSeries 𝕂 𝔸).radius) : HasStrictFDerivAt exp (1 : 𝔸 ->L[𝕂
] 𝔸) 0
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `NormedSpace.expSeries_radius_pos`：expSeries_radius_pos : 0 < (expSeries 
𝕂 𝔸).radius
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …

--- 原说明 ---
The exponential in a Banach algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` has strict Fréch
et derivative
`1 : 𝔸 →L[𝕂] 𝔸` at zero.
-/
theorem hasStrictFDerivAt_exp_zero : HasStrictFDerivAt exp (1 : 𝔸 →L[𝕂] 𝔸) 0 :=
  hasStrictFDerivAt_exp_zero_of_radius_pos (expSeries_radius_pos 𝕂 𝔸)

/-- The exponential in a Banach algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` has Fréchet derivative
`1 : 𝔸 →L[𝕂] 𝔸` at zero. -/
/-
**hasFDerivAt_exp_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_exp_zero : HasFDerivAt exp (1 : 𝔸 ->L[𝕂] 𝔸) 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `hasStrictFDerivAt_exp_zero`：hasStrictFDerivAt_exp_zero : HasStrictFDeriv
At exp (1 : 𝔸 ->L[𝕂] 𝔸) 0

--- 原说明 ---
The exponential in a Banach algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` has Fréchet deri
vative
`1 : 𝔸 →L[𝕂] 𝔸` at zero.
-/
theorem hasFDerivAt_exp_zero : HasFDerivAt exp (1 : 𝔸 →L[𝕂] 𝔸) 0 :=
  hasStrictFDerivAt_exp_zero.hasFDerivAt

end RCLikeAnyAlgebra

section RCLikeCommAlgebra

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedCommRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-- The exponential map in a commutative Banach algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` has strict
Fréchet derivative `NormedSpace.exp x • 1 : 𝔸 →L[𝕂] 𝔸` at any point `x`. -/
/-
**hasStrictFDerivAt_exp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_exp {x : 𝔸} : HasStrictFDerivAt exp (exp x • (1 : 𝔸 ->L[
𝕂] 𝔸)) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasStrictFDerivAt_exp_of_mem_ball`：hasStrictFDerivAt_exp_of_mem_ball {x 
: 𝔸} (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : HasStrictFDerivAt
 exp (exp x • (1 : 𝔸 ->…
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.expSeries_radius_eq_top`：expSeries_radius_eq_top : (expSerie
s 𝕂 𝔸).radius = ∞
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …

--- 原说明 ---
The exponential map in a commutative Banach algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` 
has strict
Fréchet derivative `NormedSpace.exp x • 1 : 𝔸 →L[𝕂] 𝔸` at any point `x`.
-/
theorem hasStrictFDerivAt_exp {x : 𝔸} : HasStrictFDerivAt exp (exp x • (1 : 𝔸 →L[𝕂] 𝔸)) x :=
  hasStrictFDerivAt_exp_of_mem_ball ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

/-- The exponential map in a commutative Banach algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` has
Fréchet derivative `NormedSpace.exp x • 1 : 𝔸 →L[𝕂] 𝔸` at any point `x`. -/
/-
**hasFDerivAt_exp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_exp {x : 𝔸} : HasFDerivAt exp (exp x • (1 : 𝔸 ->L[𝕂] 𝔸)) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
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
· 使用定理 `hasStrictFDerivAt_exp`：hasStrictFDerivAt_exp {x : 𝔸} : HasStrictFDerivAt
 exp (exp x • (1 : 𝔸 ->L[𝕂] 𝔸)) x

--- 原说明 ---
The exponential map in a commutative Banach algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` 
has
Fréchet derivative `NormedSpace.exp x • 1 : 𝔸 →L[𝕂] 𝔸` at any point `x`.
-/
theorem hasFDerivAt_exp {x : 𝔸} : HasFDerivAt exp (exp x • (1 : 𝔸 →L[𝕂] 𝔸)) x :=
  hasStrictFDerivAt_exp.hasFDerivAt

end RCLikeCommAlgebra

section DerivRCLike

variable {𝕂 : Type*} [RCLike 𝕂]

/-- The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has strict derivative `NormedSpace.exp x`
at any point `x`. -/
/-
**hasStrictDerivAt_exp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictDerivAt_exp {x : 𝕂} : HasStrictDerivAt exp (exp x) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasStrictDerivAt_exp_of_mem_ball`：hasStrictDerivAt_exp_of_mem_ball {x : 
𝕂} (hx : x in Metric.eball (0 : 𝕂) (expSeries 𝕂 𝕂).radius) : HasStrictDerivAt ex
p (exp x) x
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.expSeries_radius_eq_top`：expSeries_radius_eq_top : (expSerie
s 𝕂 𝔸).radius = ∞
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …

--- 原说明 ---
The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has strict derivative `NormedSpace.exp
 x`
at any point `x`.
-/
theorem hasStrictDerivAt_exp {x : 𝕂} : HasStrictDerivAt exp (exp x) x :=
  hasStrictDerivAt_exp_of_mem_ball ((expSeries_radius_eq_top 𝕂 𝕂).symm ▸ edist_lt_top _ _)

/-- The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has derivative `NormedSpace.exp x`
at any point `x`. -/
/-
**hasDerivAt_exp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_exp {x : 𝕂} : HasDerivAt exp (exp x) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `hasStrictDerivAt_exp`：hasStrictDerivAt_exp {x : 𝕂} : HasStrictDerivAt ex
p (exp x) x

--- 原说明 ---
The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has derivative `NormedSpace.exp x`
at any point `x`.
-/
theorem hasDerivAt_exp {x : 𝕂} : HasDerivAt exp (exp x) x :=
  hasStrictDerivAt_exp.hasDerivAt

/-- The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has strict derivative `1` at zero. -/
/-
**hasStrictDerivAt_exp_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictDerivAt_exp_zero : HasStrictDerivAt exp (1 : 𝕂) 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasStrictDerivAt_exp_zero_of_radius_pos`：hasStrictDerivAt_exp_zero_of_ra
dius_pos (h : 0 < (expSeries 𝕂 𝕂).radius) : HasStrictDerivAt exp (1 : 𝕂) 0
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `NormedSpace.expSeries_radius_pos`：expSeries_radius_pos : 0 < (expSeries 
𝕂 𝔸).radius
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …

--- 原说明 ---
The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has strict derivative `1` at zero.
-/
theorem hasStrictDerivAt_exp_zero : HasStrictDerivAt exp (1 : 𝕂) 0 :=
  hasStrictDerivAt_exp_zero_of_radius_pos (expSeries_radius_pos 𝕂 𝕂)

/-- The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has derivative `1` at zero. -/
/-
**hasDerivAt_exp_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_exp_zero : HasDerivAt exp (1 : 𝕂) 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `hasStrictDerivAt_exp_zero`：hasStrictDerivAt_exp_zero : HasStrictDerivAt 
exp (1 : 𝕂) 0

--- 原说明 ---
The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has derivative `1` at zero.
-/
theorem hasDerivAt_exp_zero : HasDerivAt exp (1 : 𝕂) 0 :=
  hasStrictDerivAt_exp_zero.hasDerivAt

end DerivRCLike

/-
**Complex.exp_eq_exp_** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Complex.exp_eq_exp_ℂ : Complex.exp = NormedSpace.exp := by
  refine funext fun x => ?_
  rw [Complex.exp, exp_eq_tsum_div]
  exact tendsto_nhds_unique x.exp'.tendsto_limit (expSeries_div_summable x).hasSum.tendsto_sum_nat
/-
**Real.exp_eq_exp_** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Real.exp_eq_exp_ℝ : Real.exp = NormedSpace.exp := by
  ext x; exact mod_cast congr_fun Complex.exp_eq_exp_ℂ x

/-! ### Derivative of $\exp (ux)$ by $u$

Note that since for `x : 𝔸` we have `NormedRing 𝔸` not `NormedCommRing 𝔸`, we cannot deduce
these results from `hasFDerivAt_exp_of_mem_ball` applied to the algebra `𝔸`.

One possible solution for that would be to apply `hasFDerivAt_exp_of_mem_ball` to the
commutative algebra `Algebra.elementalAlgebra 𝕊 x`. Unfortunately we don't have all the required
API, so we leave that to a future refactor (see https://github.com/leanprover-community/mathlib3/pull/19062 for discussion).

We could also go the other way around and deduce `hasFDerivAt_exp_of_mem_ball` from
`hasFDerivAt_exp_smul_const_of_mem_ball` applied to `𝕊 := 𝔸`, `x := (1 : 𝔸)`, and `t := x`.
However, doing so would make the aforementioned `elementalAlgebra` refactor harder, so for now we
just prove these two lemmas independently.

A last strategy would be to deduce everything from the more general non-commutative case,
$$\frac{d}{dt}e^{x(t)} = \int_0^1 e^{sx(t)} \left(\frac{d}{dt}e^{x(t)}\right) e^{(1-s)x(t)} ds$$
but this is harder to prove, and typically is shown by going via these results first.

TODO: prove this result too!
-/


section exp_smul

variable {𝕂 𝕊 𝔸 : Type*}
variable (𝕂)

open scoped Topology

open Asymptotics Filter

section MemBall

variable [NontriviallyNormedField 𝕂] [CharZero 𝕂]
variable [NormedCommRing 𝕊] [NormedRing 𝔸]
variable [NormedSpace 𝕂 𝕊] [NormedAlgebra 𝕂 𝔸] [Algebra 𝕊 𝔸] [ContinuousSMul 𝕊 𝔸]
variable [IsScalarTower 𝕂 𝕊 𝔸]
variable [CompleteSpace 𝔸]

/-
**hasFDerivAt_exp_smul_const_of_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_exp_smul_const_of_mem_ball (x : 𝔸) (t : 𝕊) (htx : t • x in Met
ric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : HasFDerivAt (fun u : 𝕊 => exp (u • x
)) (exp (t • x) • (1 : 𝕊 ->L[𝕂] 𝕊).smulRight x) t
参数：x : 𝔸；t : 𝕊；htx : t • x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasFDerivAt_iff_isLittleO_nhds_zero`：hasFDerivAt_iff_isLittleO_nhds_zero
 : HasFDerivAt f f' x ↔ (fun h : E => f (x + h) - f x - f' h) =o[𝓝 0] fun h => h
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Filter.Tendsto.smul_const`：Filter.Tendsto.smul_const {f : α -> M} {l : F
ilter α} {c : M} (hf : Tendsto f l (𝓝 c)) (a : X) : Tendsto (fun x => f x • a) l
 (𝓝 (c • a))
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Metric.eball_mem_nhds`：eball_mem_nhds (x : α) {ε : Real>=0∞} (ε0 : 0 < ε
) : eball x ε in 𝓝 x
· 使用定理 `LT.lt.pos`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `Commute.smul_right`：Commute.smul_right [Mul α] [SMulCommClass M α α] [Is
ScalarTower M α α] {a b : α} (h : Commute a b) (r : M) : Commute a (r • b)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `Commute.smul_left`：Commute.smul_left [Mul α] [SMulCommClass M α α] [IsSc
alarTower M α α] {a b : α} (h : Commute a b) (r : M) : Commute (r • a) b
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `NormedSpace.exp_add_of_commute_of_mem_ball`：exp_add_of_commute_of_mem_ba
ll [CharZero 𝕂] {x y : 𝔸} (hxy : Commute x y) (hx : x in Metric.eball (0 : 𝔸) (e
xpSeries 𝕂 𝔸).radius) (hy : y in…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `NormedSpace.exp_zero`：exp_zero : exp (0 : 𝔸) = 1
· 使用定理 `ContinuousLinearMap.smulRight_apply`：smulRight_apply {c : M₁ ->L[R] S} {
f : M₂} {x : M₁} : (smulRight c f : M₁ -> M₂) x = c x • f
· 使用定理 `one_apply_eq_self`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : Fu
nLike F α α} {inst_1 : One F} [self : IsOneApplyEqSelf F α]   (x : α), 1 x = x
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
（共 39 条，此处仅展示前 30 条）
-/
theorem hasFDerivAt_exp_smul_const_of_mem_ball (x : 𝔸) (t : 𝕊)
    (htx : t • x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasFDerivAt (fun u : 𝕊 => exp (u • x)) (exp (t • x) • (1 : 𝕊 →L[𝕂] 𝕊).smulRight x) t := by
  -- TODO: prove this via `hasFDerivAt_exp_of_mem_ball` using the commutative ring
  -- `Algebra.elementalAlgebra 𝕊 x`. See https://github.com/leanprover-community/mathlib3/pull/19062 for discussion.
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  suffices (fun (h : 𝕊) => exp (t • x) *
      (exp ((0 + h) • x) - exp ((0 : 𝕊) • x) - ((1 : 𝕊 →L[𝕂] 𝕊).smulRight x) h)) =ᶠ[𝓝 0]
        fun h =>
          exp ((t + h) • x) - exp (t • x) - (exp (t • x) • (1 : 𝕊 →L[𝕂] 𝕊).smulRight x) h by
    apply (IsLittleO.const_mul_left _ _).congr' this (EventuallyEq.refl _ _)
    rw [← hasFDerivAt_iff_isLittleO_nhds_zero (f := fun u => exp (u • x))
      (f' := (1 : 𝕊 →L[𝕂] 𝕊).smulRight x) (x := 0)]
    have : HasFDerivAt exp (1 : 𝔸 →L[𝕂] 𝔸) ((1 : 𝕊 →L[𝕂] 𝕊).smulRight x 0) := by
      rw [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, zero_smul]
      exact hasFDerivAt_exp_zero_of_radius_pos htx.pos
    exact this.comp 0 ((1 : 𝕊 →L[𝕂] 𝕊).smulRight x).hasFDerivAt
  have : Tendsto (fun h : 𝕊 => h • x) (𝓝 0) (𝓝 0) := by
    rw [← zero_smul 𝕊 x]
    exact tendsto_id.smul_const x
  have : ∀ᶠ h in 𝓝 (0 : 𝕊), h • x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius :=
    this.eventually (Metric.eball_mem_nhds _ htx.pos)
  filter_upwards [this] with h hh
  have : Commute (t • x) (h • x) := ((Commute.refl x).smul_left t).smul_right h
  rw [add_smul t h, exp_add_of_commute_of_mem_ball this htx hh, zero_add, zero_smul, exp_zero,
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self,
    smul_apply, ContinuousLinearMap.smulRight_apply, one_apply_eq_self, smul_eq_mul,
    mul_sub_left_distrib, mul_sub_left_distrib, mul_one]
/-
**hasFDerivAt_exp_smul_const_of_mem_ball'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_exp_smul_const_of_mem_ball' (x : 𝔸) (t : 𝕊) (htx : t • x in Me
tric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : HasFDerivAt (fun u : 𝕊 => exp (u • 
x)) (((1 : 𝕊 ->L[𝕂] 𝕊).smulRight x).smulRight (exp (t • x))) t
参数：x : 𝔸；t : 𝕊；htx : t • x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
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
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `Commute.exp_right`：∀ {𝔸 : Type u_2} [inst : Ring 𝔸] [inst_1 : Topologica
lSpace 𝔸] [inst_2 : IsTopologicalRing 𝔸] [T2Space 𝔸] {x y : 𝔸},   Commute x y → 
Commute…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `Commute.smul_right`：Commute.smul_right [Mul α] [SMulCommClass M α α] [Is
ScalarTower M α α] {a b : α} (h : Commute a b) (r : M) : Commute a (r • b)
· 使用引理 `Commute.smul_left`：Commute.smul_left [Mul α] [SMulCommClass M α α] [IsSc
alarTower M α α] {a b : α} (h : Commute a b) (r : M) : Commute (r • a) b
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
· 使用定理 `hasFDerivAt_exp_smul_const_of_mem_ball`：hasFDerivAt_exp_smul_const_of_me
m_ball (x : 𝔸) (t : 𝕊) (htx : t • x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radi
us) : HasFDerivAt (fun u : 𝕊…
-/
theorem hasFDerivAt_exp_smul_const_of_mem_ball' (x : 𝔸) (t : 𝕊)
    (htx : t • x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasFDerivAt (fun u : 𝕊 => exp (u • x))
      (((1 : 𝕊 →L[𝕂] 𝕊).smulRight x).smulRight (exp (t • x))) t := by
  convert! hasFDerivAt_exp_smul_const_of_mem_ball 𝕂 _ _ htx using 1
  ext t'
  change Commute (t' • x) (exp (t • x))
  exact (((Commute.refl x).smul_left t').smul_right t).exp_right
/-
**hasStrictFDerivAt_exp_smul_const_of_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_exp_smul_const_of_mem_ball (x : 𝔸) (t : 𝕊) (htx : t • x 
in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : HasStrictFDerivAt (fun u : 𝕊 =
> exp (u • x)) (exp (t • x) • (1 : 𝕊 ->L[𝕂] 𝕊).smulRight x) t
参数：x : 𝔸；t : 𝕊；htx : t • x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
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
· 使用定理 `NormedSpace.analyticAt_exp_of_mem_ball`：analyticAt_exp_of_mem_ball [Char
Zero 𝕂] (x : 𝔸) (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : Analyt
icAt 𝕂 exp x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
· 使用定理 `HasFPowerSeriesAt.hasStrictFDerivAt`：HasFPowerSeriesAt.hasStrictFDerivAt
 (h : HasFPowerSeriesAt f p x) : HasStrictFDerivAt f (continuousMultilinearCurry
Fin1 𝕜 E F (p 1)) x
· 使用定理 `ContinuousLinearMap.hasStrictFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.M
odule 𝕜 E] [inst_3 : Topolo…
· 使用定理 `hasFDerivAt_exp_smul_const_of_mem_ball`：hasFDerivAt_exp_smul_const_of_me
m_ball (x : 𝔸) (t : 𝕊) (htx : t • x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radi
us) : HasFDerivAt (fun u : 𝕊…
· 使用定理 `HasFDerivAt.unique`：HasFDerivAt.unique (h₀ : HasFDerivAt f f' x) (h₁ : H
asFDerivAt f f₁' x) : f' = f₁'
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
-/
theorem hasStrictFDerivAt_exp_smul_const_of_mem_ball (x : 𝔸) (t : 𝕊)
    (htx : t • x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasStrictFDerivAt (fun u : 𝕊 => exp (u • x))
      (exp (t • x) • (1 : 𝕊 →L[𝕂] 𝕊).smulRight x) t :=
  let ⟨_, hp⟩ := analyticAt_exp_of_mem_ball (t • x) htx
  have deriv₁ : HasStrictFDerivAt (fun u : 𝕊 => exp (u • x)) _ t :=
    hp.hasStrictFDerivAt.comp t ((ContinuousLinearMap.id 𝕂 𝕊).smulRight x).hasStrictFDerivAt
  have deriv₂ : HasFDerivAt (fun u : 𝕊 => exp (u • x)) _ t :=
    hasFDerivAt_exp_smul_const_of_mem_ball 𝕂 x t htx
  deriv₁.hasFDerivAt.unique deriv₂ ▸ deriv₁
/-
**hasStrictFDerivAt_exp_smul_const_of_mem_ball'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_exp_smul_const_of_mem_ball' (x : 𝔸) (t : 𝕊) (htx : t • x
 in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : HasStrictFDerivAt (fun u : 𝕊 
=> exp (u • x)) (((1 : 𝕊 ->L[𝕂] 𝕊).smulRight x).smulRight (exp (t • x))) t
参数：x : 𝔸；t : 𝕊；htx : t • x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NormedSpace.analyticAt_exp_of_mem_ball`：analyticAt_exp_of_mem_ball [Char
Zero 𝕂] (x : 𝔸) (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : Analyt
icAt 𝕂 exp x
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
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `Commute.exp_right`：∀ {𝔸 : Type u_2} [inst : Ring 𝔸] [inst_1 : Topologica
lSpace 𝔸] [inst_2 : IsTopologicalRing 𝔸] [T2Space 𝔸] {x y : 𝔸},   Commute x y → 
Commute…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `Commute.smul_right`：Commute.smul_right [Mul α] [SMulCommClass M α α] [Is
ScalarTower M α α] {a b : α} (h : Commute a b) (r : M) : Commute a (r • b)
· 使用引理 `Commute.smul_left`：Commute.smul_left [Mul α] [SMulCommClass M α α] [IsSc
alarTower M α α] {a b : α} (h : Commute a b) (r : M) : Commute (r • a) b
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
· 使用定理 `hasStrictFDerivAt_exp_smul_const_of_mem_ball`：hasStrictFDerivAt_exp_smul
_const_of_mem_ball (x : 𝔸) (t : 𝕊) (htx : t • x in Metric.eball (0 : 𝔸) (expSeri
es 𝕂 𝔸).radius) : HasStrictFDerivA…
-/
theorem hasStrictFDerivAt_exp_smul_const_of_mem_ball' (x : 𝔸) (t : 𝕊)
    (htx : t • x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasStrictFDerivAt (fun u : 𝕊 => exp (u • x))
      (((1 : 𝕊 →L[𝕂] 𝕊).smulRight x).smulRight (exp (t • x))) t := by
  let ⟨_, _⟩ := analyticAt_exp_of_mem_ball (t • x) htx
  convert! hasStrictFDerivAt_exp_smul_const_of_mem_ball 𝕂 _ _ htx using 1
  ext t'
  change Commute (t' • x) (exp (t • x))
  exact (((Commute.refl x).smul_left t').smul_right t).exp_right

variable {𝕂}
/-
**hasStrictDerivAt_exp_smul_const_of_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictDerivAt_exp_smul_const_of_mem_ball (x : 𝔸) (t : 𝕂) (htx : t • x i
n Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : HasStrictDerivAt (fun u : 𝕂 => 
exp (u • x)) (exp (t • x) * x) t
参数：x : 𝔸；t : 𝕂；htx : t • x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
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
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_apply_eq_self`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : Fu
nLike F α α} {inst_1 : One F} [self : IsOneApplyEqSelf F α]   (x : α), 1 x = x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasStrictFDerivAt.hasStrictDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `hasStrictFDerivAt_exp_smul_const_of_mem_ball`：hasStrictFDerivAt_exp_smul
_const_of_mem_ball (x : 𝔸) (t : 𝕊) (htx : t • x in Metric.eball (0 : 𝔸) (expSeri
es 𝕂 𝔸).radius) : HasStrictFDerivA…
-/
theorem hasStrictDerivAt_exp_smul_const_of_mem_ball (x : 𝔸) (t : 𝕂)
    (htx : t • x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasStrictDerivAt (fun u : 𝕂 => exp (u • x)) (exp (t • x) * x) t := by
  simpa using (hasStrictFDerivAt_exp_smul_const_of_mem_ball 𝕂 x t htx).hasStrictDerivAt
/-
**hasStrictDerivAt_exp_smul_const_of_mem_ball'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictDerivAt_exp_smul_const_of_mem_ball' (x : 𝔸) (t : 𝕂) (htx : t • x 
in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : HasStrictDerivAt (fun u : 𝕂 =>
 exp (u • x)) (x * exp (t • x)) t
参数：x : 𝔸；t : 𝕂；htx : t • x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_apply_eq_self`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : Fu
nLike F α α} {inst_1 : One F} [self : IsOneApplyEqSelf F α]   (x : α), 1 x = x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasStrictFDerivAt.hasStrictDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `hasStrictFDerivAt_exp_smul_const_of_mem_ball'`：hasStrictFDerivAt_exp_smu
l_const_of_mem_ball' (x : 𝔸) (t : 𝕊) (htx : t • x in Metric.eball (0 : 𝔸) (expSe
ries 𝕂 𝔸).radius) : HasStrictFDeriv…
-/
theorem hasStrictDerivAt_exp_smul_const_of_mem_ball' (x : 𝔸) (t : 𝕂)
    (htx : t • x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasStrictDerivAt (fun u : 𝕂 => exp (u • x)) (x * exp (t • x)) t := by
  simpa using (hasStrictFDerivAt_exp_smul_const_of_mem_ball' 𝕂 x t htx).hasStrictDerivAt
/-
**hasDerivAt_exp_smul_const_of_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_exp_smul_const_of_mem_ball (x : 𝔸) (t : 𝕂) (htx : t • x in Metr
ic.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : HasDerivAt (fun u : 𝕂 => exp (u • x))
 (exp (t • x) * x) t
参数：x : 𝔸；t : 𝕂；htx : t • x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `hasStrictDerivAt_exp_smul_const_of_mem_ball`：hasStrictDerivAt_exp_smul_c
onst_of_mem_ball (x : 𝔸) (t : 𝕂) (htx : t • x in Metric.eball (0 : 𝔸) (expSeries
 𝕂 𝔸).radius) : HasStrictDerivAt …
-/
theorem hasDerivAt_exp_smul_const_of_mem_ball (x : 𝔸) (t : 𝕂)
    (htx : t • x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasDerivAt (fun u : 𝕂 => exp (u • x)) (exp (t • x) * x) t :=
  (hasStrictDerivAt_exp_smul_const_of_mem_ball x t htx).hasDerivAt
/-
**hasDerivAt_exp_smul_const_of_mem_ball'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_exp_smul_const_of_mem_ball' (x : 𝔸) (t : 𝕂) (htx : t • x in Met
ric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : HasDerivAt (fun u : 𝕂 => exp (u • x)
) (x * exp (t • x)) t
参数：x : 𝔸；t : 𝕂；htx : t • x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `hasStrictDerivAt_exp_smul_const_of_mem_ball'`：hasStrictDerivAt_exp_smul_
const_of_mem_ball' (x : 𝔸) (t : 𝕂) (htx : t • x in Metric.eball (0 : 𝔸) (expSeri
es 𝕂 𝔸).radius) : HasStrictDerivAt…
-/
theorem hasDerivAt_exp_smul_const_of_mem_ball' (x : 𝔸) (t : 𝕂)
    (htx : t • x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasDerivAt (fun u : 𝕂 => exp (u • x)) (x * exp (t • x)) t :=
  (hasStrictDerivAt_exp_smul_const_of_mem_ball' x t htx).hasDerivAt

end MemBall

section RCLike

variable [RCLike 𝕂]
variable [NormedCommRing 𝕊] [NormedRing 𝔸]
variable [NormedAlgebra 𝕂 𝕊] [NormedAlgebra 𝕂 𝔸] [Algebra 𝕊 𝔸] [ContinuousSMul 𝕊 𝔸]
variable [IsScalarTower 𝕂 𝕊 𝔸]
variable [CompleteSpace 𝔸]

/-
**hasFDerivAt_exp_smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_exp_smul_const (x : 𝔸) (t : 𝕊) : HasFDerivAt (fun u : 𝕊 => exp
 (u • x)) (exp (t • x) • (1 : 𝕊 ->L[𝕂] 𝕊).smulRight x) t
参数：x : 𝔸；t : 𝕊。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAt_exp_smul_const_of_mem_ball`：hasFDerivAt_exp_smul_const_of_me
m_ball (x : 𝔸) (t : 𝕊) (htx : t • x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radi
us) : HasFDerivAt (fun u : 𝕊…
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.expSeries_radius_eq_top`：expSeries_radius_eq_top : (expSerie
s 𝕂 𝔸).radius = ∞
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem hasFDerivAt_exp_smul_const (x : 𝔸) (t : 𝕊) :
    HasFDerivAt (fun u : 𝕊 => exp (u • x)) (exp (t • x) • (1 : 𝕊 →L[𝕂] 𝕊).smulRight x) t :=
  hasFDerivAt_exp_smul_const_of_mem_ball 𝕂 _ _ <|
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _
/-
**hasFDerivAt_exp_smul_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_exp_smul_const' (x : 𝔸) (t : 𝕊) : HasFDerivAt (fun u : 𝕊 => ex
p (u • x)) (((1 : 𝕊 ->L[𝕂] 𝕊).smulRight x).smulRight (exp (t • x))) t
参数：x : 𝔸；t : 𝕊。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAt_exp_smul_const_of_mem_ball'`：hasFDerivAt_exp_smul_const_of_m
em_ball' (x : 𝔸) (t : 𝕊) (htx : t • x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).ra
dius) : HasFDerivAt (fun u : …
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.expSeries_radius_eq_top`：expSeries_radius_eq_top : (expSerie
s 𝕂 𝔸).radius = ∞
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem hasFDerivAt_exp_smul_const' (x : 𝔸) (t : 𝕊) :
    HasFDerivAt (fun u : 𝕊 => exp (u • x))
      (((1 : 𝕊 →L[𝕂] 𝕊).smulRight x).smulRight (exp (t • x))) t :=
  hasFDerivAt_exp_smul_const_of_mem_ball' 𝕂 _ _ <|
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _
/-
**hasStrictFDerivAt_exp_smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_exp_smul_const (x : 𝔸) (t : 𝕊) : HasStrictFDerivAt (fun 
u : 𝕊 => exp (u • x)) (exp (t • x) • (1 : 𝕊 ->L[𝕂] 𝕊).smulRight x) t
参数：x : 𝔸；t : 𝕊。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasStrictFDerivAt_exp_smul_const_of_mem_ball`：hasStrictFDerivAt_exp_smul
_const_of_mem_ball (x : 𝔸) (t : 𝕊) (htx : t • x in Metric.eball (0 : 𝔸) (expSeri
es 𝕂 𝔸).radius) : HasStrictFDerivA…
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.expSeries_radius_eq_top`：expSeries_radius_eq_top : (expSerie
s 𝕂 𝔸).radius = ∞
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem hasStrictFDerivAt_exp_smul_const (x : 𝔸) (t : 𝕊) :
    HasStrictFDerivAt (fun u : 𝕊 => exp (u • x))
      (exp (t • x) • (1 : 𝕊 →L[𝕂] 𝕊).smulRight x) t :=
  hasStrictFDerivAt_exp_smul_const_of_mem_ball 𝕂 _ _ <|
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _
/-
**hasStrictFDerivAt_exp_smul_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_exp_smul_const' (x : 𝔸) (t : 𝕊) : HasStrictFDerivAt (fun
 u : 𝕊 => exp (u • x)) (((1 : 𝕊 ->L[𝕂] 𝕊).smulRight x).smulRight (exp (t • x))) 
t
参数：x : 𝔸；t : 𝕊。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasStrictFDerivAt_exp_smul_const_of_mem_ball'`：hasStrictFDerivAt_exp_smu
l_const_of_mem_ball' (x : 𝔸) (t : 𝕊) (htx : t • x in Metric.eball (0 : 𝔸) (expSe
ries 𝕂 𝔸).radius) : HasStrictFDeriv…
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.expSeries_radius_eq_top`：expSeries_radius_eq_top : (expSerie
s 𝕂 𝔸).radius = ∞
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem hasStrictFDerivAt_exp_smul_const' (x : 𝔸) (t : 𝕊) :
    HasStrictFDerivAt (fun u : 𝕊 => exp (u • x))
      (((1 : 𝕊 →L[𝕂] 𝕊).smulRight x).smulRight (exp (t • x))) t :=
  hasStrictFDerivAt_exp_smul_const_of_mem_ball' 𝕂 _ _ <|
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

variable {𝕂}
/-
**hasStrictDerivAt_exp_smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictDerivAt_exp_smul_const (x : 𝔸) (t : 𝕂) : HasStrictDerivAt (fun u 
: 𝕂 => exp (u • x)) (exp (t • x) * x) t
参数：x : 𝔸；t : 𝕂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasStrictDerivAt_exp_smul_const_of_mem_ball`：hasStrictDerivAt_exp_smul_c
onst_of_mem_ball (x : 𝔸) (t : 𝕂) (htx : t • x in Metric.eball (0 : 𝔸) (expSeries
 𝕂 𝔸).radius) : HasStrictDerivAt …
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.expSeries_radius_eq_top`：expSeries_radius_eq_top : (expSerie
s 𝕂 𝔸).radius = ∞
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem hasStrictDerivAt_exp_smul_const (x : 𝔸) (t : 𝕂) :
    HasStrictDerivAt (fun u : 𝕂 => exp (u • x)) (exp (t • x) * x) t :=
  hasStrictDerivAt_exp_smul_const_of_mem_ball _ _ <|
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _
/-
**hasStrictDerivAt_exp_smul_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictDerivAt_exp_smul_const' (x : 𝔸) (t : 𝕂) : HasStrictDerivAt (fun u
 : 𝕂 => exp (u • x)) (x * exp (t • x)) t
参数：x : 𝔸；t : 𝕂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasStrictDerivAt_exp_smul_const_of_mem_ball'`：hasStrictDerivAt_exp_smul_
const_of_mem_ball' (x : 𝔸) (t : 𝕂) (htx : t • x in Metric.eball (0 : 𝔸) (expSeri
es 𝕂 𝔸).radius) : HasStrictDerivAt…
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.expSeries_radius_eq_top`：expSeries_radius_eq_top : (expSerie
s 𝕂 𝔸).radius = ∞
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem hasStrictDerivAt_exp_smul_const' (x : 𝔸) (t : 𝕂) :
    HasStrictDerivAt (fun u : 𝕂 => exp (u • x)) (x * exp (t • x)) t :=
  hasStrictDerivAt_exp_smul_const_of_mem_ball' _ _ <|
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _
/-
**hasDerivAt_exp_smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_exp_smul_const (x : 𝔸) (t : 𝕂) : HasDerivAt (fun u : 𝕂 => exp (
u • x)) (exp (t • x) * x) t
参数：x : 𝔸；t : 𝕂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAt_exp_smul_const_of_mem_ball`：hasDerivAt_exp_smul_const_of_mem_
ball (x : 𝔸) (t : 𝕂) (htx : t • x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius
) : HasDerivAt (fun u : 𝕂 =…
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.expSeries_radius_eq_top`：expSeries_radius_eq_top : (expSerie
s 𝕂 𝔸).radius = ∞
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem hasDerivAt_exp_smul_const (x : 𝔸) (t : 𝕂) :
    HasDerivAt (fun u : 𝕂 => exp (u • x)) (exp (t • x) * x) t :=
  hasDerivAt_exp_smul_const_of_mem_ball _ _ <| (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _
/-
**hasDerivAt_exp_smul_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_exp_smul_const' (x : 𝔸) (t : 𝕂) : HasDerivAt (fun u : 𝕂 => exp 
(u • x)) (x * exp (t • x)) t
参数：x : 𝔸；t : 𝕂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAt_exp_smul_const_of_mem_ball'`：hasDerivAt_exp_smul_const_of_mem
_ball' (x : 𝔸) (t : 𝕂) (htx : t • x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radi
us) : HasDerivAt (fun u : 𝕂 …
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.expSeries_radius_eq_top`：expSeries_radius_eq_top : (expSerie
s 𝕂 𝔸).radius = ∞
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem hasDerivAt_exp_smul_const' (x : 𝔸) (t : 𝕂) :
    HasDerivAt (fun u : 𝕂 => exp (u • x)) (x * exp (t • x)) t :=
  hasDerivAt_exp_smul_const_of_mem_ball' _ _ <|
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

variable (𝕂) in
@[fun_prop]
/-
**differentiable_exp_smul_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：differentiable_exp_smul_const (x : 𝔸) : Differentiable 𝕂 (fun t : 𝕂 => exp
 (t • x))
参数：x : 𝔸。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `hasDerivAt_exp_smul_const`：hasDerivAt_exp_smul_const (x : 𝔸) (t : 𝕂) : H
asDerivAt (fun u : 𝕂 => exp (u • x)) (exp (t • x) * x) t
-/
lemma differentiable_exp_smul_const (x : 𝔸) :
    Differentiable 𝕂 (fun t : 𝕂 ↦ exp (t • x)) :=
  (⟨_, hasDerivAt_exp_smul_const x ·⟩)

@[fun_prop]
/-
**differentiableAt_exp_smul_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：differentiableAt_exp_smul_const (x : 𝔸) (r : 𝕂) : DifferentiableAt 𝕂 (fun 
t : 𝕂 => exp (t • x)) r
参数：x : 𝔸；r : 𝕂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.differentiableAt`：Differentiable.differentiableAt (h : Di
fferentiable 𝕜 f) : DifferentiableAt 𝕜 f x
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用引理 `differentiable_exp_smul_const`：differentiable_exp_smul_const (x : 𝔸) : D
ifferentiable 𝕂 (fun t : 𝕂 => exp (t • x))
-/
lemma differentiableAt_exp_smul_const (x : 𝔸) (r : 𝕂) :
    DifferentiableAt 𝕂 (fun t : 𝕂 ↦ exp (t • x)) r :=
  differentiable_exp_smul_const 𝕂 x |>.differentiableAt

end RCLike

end exp_smul

section tsum_tprod

variable {𝔸 : Type*} [NormedCommRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]

/-- If `f` has sum `a`, then `NormedSpace.exp ∘ f` has product `NormedSpace.exp a`. -/
/-
**HasSum.exp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasSum.exp {ι : Type*} {f : ι -> 𝔸} {a : 𝔸} (h : HasSum f a) : HasProd (ex
p ∘ f) (exp a)
参数：h : HasSum f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `NormedSpace.exp_sum`：exp_sum {ι} (s : Finset ι) (f : ι -> 𝔸) : exp (∑ i 
in s, f i) = ∏ i in s, exp (f i)
· 使用定理 `Filter.Tendsto.exp`：∀ {𝔸 : Type u_1} [inst : NormedRing 𝔸] [NormedAlgebr
a ℚ 𝔸] [CompleteSpace 𝔸] {α : Type u_3} {l : Filter α} {f : α → 𝔸}   {a : 𝔸}, Fi
lter.Ten…

--- 原说明 ---
If `f` has sum `a`, then `NormedSpace.exp ∘ f` has product `NormedSpace.exp a`.
-/
lemma HasSum.exp {ι : Type*} {f : ι → 𝔸} {a : 𝔸} (h : HasSum f a) :
    HasProd (exp ∘ f) (exp a) :=
  Tendsto.congr (fun s ↦ exp_sum s f) <| Tendsto.exp h

end tsum_tprod

