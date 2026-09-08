/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# The Gamma function

This file defines the `Γ` function (of a real or complex variable `s`). We define this by Euler's
integral `Γ(s) = ∫ x in Ioi 0, exp (-x) * x ^ (s - 1)` in the range where this integral converges
(i.e., for `0 < s` in the real case, and `0 < re s` in the complex case).

We show that this integral satisfies `Γ(1) = 1` and `Γ(s + 1) = s * Γ(s)`; hence we can define
`Γ(s)` for all `s` as the unique function satisfying this recurrence and agreeing with Euler's
integral in the convergence range. (If `s = -n` for `n ∈ ℕ`, then the function is undefined, and we
set it to be `0` by convention.)

## Gamma function: main statements (complex case)

* `Complex.Gamma`: the `Γ` function (of a complex variable).
* `Complex.Gamma_eq_integral`: for `0 < re s`, `Γ(s)` agrees with Euler's integral.
* `Complex.Gamma_add_one`: for all `s : ℂ` with `s ≠ 0`, we have `Γ (s + 1) = s Γ(s)`.
* `Complex.Gamma_nat_eq_factorial`: for all `n : ℕ` we have `Γ (n + 1) = n!`.

## Gamma function: main statements (real case)

* `Real.Gamma`: the `Γ` function (of a real variable).
* Real counterparts of all the properties of the complex Gamma function listed above:
  `Real.Gamma_eq_integral`, `Real.Gamma_add_one`, `Real.Gamma_nat_eq_factorial`.

## Tags

Gamma
-/

public section


noncomputable section


open Filter intervalIntegral Set Real MeasureTheory Asymptotics

open scoped Nat Topology ComplexConjugate

namespace Real

/-- Asymptotic bound for the `Γ` function integrand. -/
/-
**Real.Gamma_integrand_isLittleO** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：Gamma_integrand_isLittleO (s : Real) : (fun x : Real => exp (-x) * x ^ s) 
=o[atTop] fun x : Real => exp (-(1 / 2) * x)
参数：s : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isLittleO_of_tendsto`：∀ {α : Type u_1} {𝕜 : Type u_15} [inst
 : NormedDivisionRing 𝕜] {l : Filter α} {f g : α → 𝕜},   (∀ (x : α), g x = 0 → f
 x = 0) → Filter.Tends…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.exp_neg`：∀ (x : ℝ), Real.exp (-x) = (Real.exp x)⁻¹
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₂`：mul_eq_eval₂ [CommGroupWithZer
o M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) : (
(r₁, x) ::ᵣ l₁).eval * ((r₂, x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
（共 59 条，此处仅展示前 30 条）

--- 原说明 ---
Asymptotic bound for the `Γ` function integrand.
-/
theorem Gamma_integrand_isLittleO (s : ℝ) :
    (fun x : ℝ => exp (-x) * x ^ s) =o[atTop] fun x : ℝ => exp (-(1 / 2) * x) := by
  refine isLittleO_of_tendsto (fun x hx => ?_) ?_
  · exfalso; exact (exp_pos (-(1 / 2) * x)).ne' hx
  have : (fun x : ℝ => exp (-x) * x ^ s / exp (-(1 / 2) * x)) =
      (fun x : ℝ => exp (1 / 2 * x) / x ^ s)⁻¹ := by
    ext1 x
    simp [field, ← exp_nsmul, exp_neg]
  rw [this]
  exact (tendsto_exp_mul_div_rpow_atTop s (1 / 2) one_half_pos).inv_tendsto_atTop

/-- The Euler integral for the `Γ` function converges for positive real `s`. -/
/-
**Real.GammaIntegral_convergent** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：GammaIntegral_convergent {s : Real} (h : 0 < s) : IntegrableOn (fun x : Re
al => exp (-x) * x ^ (s - 1)) (Ioi 0)
参数：h : 0 < s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ioc_union_Ioi_eq_Ioi`：Ioc_union_Ioi_eq_Ioi (h : a <= b) : Ioc a b un
ion Ioi b = Ioi a
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `MeasureTheory.integrableOn_union`：integrableOn_union [PseudoMetrizableSp
ace ε] : IntegrableOn f (s union t) μ ↔ IntegrableOn f s μ ∧ IntegrableOn f t μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `integrableOn_Icc_iff_integrableOn_Ioc`：integrableOn_Icc_iff_integrableOn
_Ioc (ha : ‖f a‖ₑ != ∞
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `intervalIntegrable_iff_integrableOn_Icc_of_le`：intervalIntegrable_iff_in
tegrableOn_Icc_of_le [NullSingletonClass μ] (hab : a <= b) (ha : ‖f a‖ₑ != ∞
· 使用定理 `IntervalIntegrable.continuousOn_mul`：continuousOn_mul {f g : Real -> A} 
(hf : IntervalIntegrable f μ a b) (hg : ContinuousOn g [[a, b]]) : IntervalInteg
rable (fun x => g x * f x…
· 使用定理 `intervalIntegral.intervalIntegrable_rpow'`：intervalIntegrable_rpow' {r :
 Real} (h : -1 < r) : IntervalIntegrable (fun x => x ^ r) volume a b
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 74 条，此处仅展示前 30 条）

--- 原说明 ---
The Euler integral for the `Γ` function converges for positive real `s`.
-/
theorem GammaIntegral_convergent {s : ℝ} (h : 0 < s) :
    IntegrableOn (fun x : ℝ => exp (-x) * x ^ (s - 1)) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (@zero_le_one ℝ _ _ _ _), integrableOn_union]
  constructor
  · rw [← integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
      ((intervalIntegrable_rpow' (by linarith)).continuousOn_mul continuousOn_id.neg.rexp)
  · exact integrable_of_isBigO_exp_neg one_half_pos
      (continuousOn_id.neg.rexp.mul (continuousOn_id.rpow_const (by grind)))
      (Gamma_integrand_isLittleO _).isBigO

end Real

namespace Complex

/- Technical note: In defining the Gamma integrand exp (-x) * x ^ (s - 1) for s complex, we have to
make a choice between ↑(Real.exp (-x)), Complex.exp (↑(-x)), and Complex.exp (-↑x), all of which are
equal but not definitionally so. We use the first of these throughout. -/
/-- The integral defining the `Γ` function converges for complex `s` with `0 < re s`.

This is proved by reduction to the real case. -/
/-
**Complex.GammaIntegral_convergent** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：GammaIntegral_convergent {s : Complex} (hs : 0 < s.re) : IntegrableOn (fun
 x => (-x).exp * x ^ (s - 1) : Real -> Complex) (Ioi 0)
参数：hs : 0 < s.re。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.aestronglyMeasurable`：ContinuousOn.aestronglyMeasurable [To
pologicalSpace α] [TopologicalSpace β] [h : SecondCountableTopologyEither α β] [
OpensMeasurableSpace α]…
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `ContinuousOn.mul`：ContinuousOn.mul (hf : ContinuousOn f s) (hg : Continu
ousOn g s) : ContinuousOn (f * g) s
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
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `Continuous.rexp`：Continuous.rexp (h : Continuous f) : Continuous fun y =
> exp (f y)
· 使用定理 `ContinuousNeg.continuous_neg`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Neg G} [self : ContinuousNeg G], Continuous fun a => -a
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `continuousOn_of_forall_continuousAt`：continuousOn_of_forall_continuousAt
 (hcont : forall x in s, ContinuousAt f x) : ContinuousOn f s
· 使用定理 `continuousAt_cpow_const`：continuousAt_cpow_const {a b : Complex} (ha : a
 in slitPlane) : ContinuousAt (· ^ b) a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.ofReal_mem_slitPlane`：∀ {x : ℝ}, ↑x ∈ Complex.slitPlane ↔ 0 < x
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
The integral defining the `Γ` function converges for complex `s` with `0 < re s`
.

This is proved by reduction to the real case.
-/
theorem GammaIntegral_convergent {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x => (-x).exp * x ^ (s - 1) : ℝ → ℂ) (Ioi 0) := by
  constructor
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    apply (continuous_ofReal.comp continuous_neg.rexp).continuousOn.mul
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have : ContinuousAt (fun x : ℂ => x ^ (s - 1)) ↑x :=
      continuousAt_cpow_const <| ofReal_mem_slitPlane.2 hx
    exact ContinuousAt.comp this continuous_ofReal.continuousAt
  · rw [← hasFiniteIntegral_norm_iff]
    refine HasFiniteIntegral.congr (Real.GammaIntegral_convergent hs).2 ?_
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    filter_upwards with x hx
    rw [norm_mul, Complex.norm_of_nonneg <| le_of_lt <| exp_pos <| -x,
      norm_cpow_eq_rpow_re_of_pos hx _]
    simp

/-- Euler's integral for the `Γ` function (of a complex variable `s`), defined as
`∫ x in Ioi 0, exp (-x) * x ^ (s - 1)`.

See `Complex.GammaIntegral_convergent` for a proof of the convergence of the integral for
`0 < re s`. -/
/-
**Complex.GammaIntegral** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：ℂ → ℂ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Euler's integral for the `Γ` function (of a complex variable `s`), defined as
`∫ x in Ioi 0, exp (-x) * x ^ (s - 1)`.

See `Complex.GammaIntegral_convergent` for a proof of the convergence of the int
egral for
`0 < re s`.
-/
@[expose] def GammaIntegral (s : ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), ↑(-x).exp * ↑x ^ (s - 1)
/-
**Complex.GammaIntegral_conj** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：GammaIntegral_conj (s : Complex) : GammaIntegral (conj s) = conj (GammaInt
egral s)
参数：s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.GammaIntegral.eq_1`：∀ (s : ℂ), s.GammaIntegral = ∫ (x : ℝ) in Se
t.Ioi 0, ↑(Real.exp (-x)) * ↑x ^ (s - 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `integral_conj`：integral_conj {f : X -> 𝕜} : ∫ x, conj (f x) ∂μ = conj (∫
 x, f x ∂μ)
· 使用定理 `MeasureTheory.setIntegral_congr_fun`：setIntegral_congr_fun (hs : Measura
bleSet s) (h : EqOn f g s) : ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Complex.conj_ofReal`：conj_ofReal (r : Real) : conj (r : Complex) = r
· 使用定理 `Complex.cpow_def_of_ne_zero`：cpow_def_of_ne_zero {x : Complex} (hx : x !
= 0) (y : Complex) : x ^ y = exp (log x * y)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.ofReal_ne_zero`：ofReal_ne_zero {z : Real} : (z : Complex) != 0 ↔
 z != 0
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Complex.exp_conj`：exp_conj : exp (conj x) = conj (exp x)
· 使用定理 `Complex.ofReal_log`：ofReal_log {x : Real} (hx : 0 <= x) : (x.log : Compl
ex) = log x
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem GammaIntegral_conj (s : ℂ) : GammaIntegral (conj s) = conj (GammaIntegral s) := by
  rw [GammaIntegral, GammaIntegral, ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [map_mul, conj_ofReal, cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hx)),
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hx)), ← exp_conj, map_mul,
    ← ofReal_log (le_of_lt hx), conj_ofReal, map_sub, map_one]
/-
**Complex.GammaIntegral_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：GammaIntegral_ofReal (s : Real) : GammaIntegral ↑s = ↑(∫ x : Real in Ioi 0
, Real.exp (-x) * x ^ (s - 1))
参数：s : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.GammaIntegral.eq_1`：∀ (s : ℂ), s.GammaIntegral = ∫ (x : ℝ) in Se
t.Ioi 0, ↑(Real.exp (-x)) * ↑x ^ (s - 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `integral_ofReal`：integral_ofReal {f : X -> Real} : ∫ x, (f x : 𝕜) ∂μ = ↑
(∫ x, f x ∂μ)
· 使用定理 `MeasureTheory.setIntegral_congr_fun`：setIntegral_congr_fun (hs : Measura
bleSet s) (h : EqOn f g s) : ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.ofReal_cpow`：ofReal_cpow {x : Real} (hx : 0 <= x) (y : Real) : (
(x ^ y : Real) : Complex) = (x : Complex) ^ (y : Complex)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.ofReal_exp`：ofReal_exp (x : Real) : (Real.exp x : Complex) = exp
 x
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `Complex.ofReal_sub`：ofReal_sub (r s : Real) : ((r - s : Real) : Complex)
 = r - s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem GammaIntegral_ofReal (s : ℝ) :
    GammaIntegral ↑s = ↑(∫ x : ℝ in Ioi 0, Real.exp (-x) * x ^ (s - 1)) := by
  have : ∀ r : ℝ, Complex.ofReal r = @RCLike.ofReal ℂ _ r := fun r => rfl
  rw [GammaIntegral]
  conv_rhs => rw [this, ← _root_.integral_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro x hx; dsimp only
  conv_rhs => rw [← this]
  rw [ofReal_mul, ofReal_cpow (mem_Ioi.mp hx).le]
  simp

@[simp]
/-
**Complex.GammaIntegral_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：GammaIntegral_one : GammaIntegral 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.GammaIntegral_ofReal`：GammaIntegral_ofReal (s : Real) : GammaInt
egral ↑s = ↑(∫ x : Real in Ioi 0, Real.exp (-x) * x ^ (s - 1))
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `integral_exp_neg_Ioi_zero`：integral_exp_neg_Ioi_zero : (∫ x : Real in Io
i 0, exp (-x)) = 1
-/
theorem GammaIntegral_one : GammaIntegral 1 = 1 := by
  simpa only [← ofReal_one, GammaIntegral_ofReal, ofReal_inj, sub_self, rpow_zero,
    mul_one] using integral_exp_neg_Ioi_zero

end Complex

/-! Now we establish the recurrence relation `Γ(s + 1) = s * Γ(s)` using integration by parts. -/


namespace Complex

section GammaRecurrence

/-- The indefinite version of the `Γ` function, `Γ(s, X) = ∫ x ∈ 0..X, exp(-x) x ^ (s - 1)`. -/
/-
**Complex.partialGamma** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：ℂ → ℝ → ℂ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The indefinite version of the `Γ` function, `Γ(s, X) = ∫ x ∈ 0..X, exp(-x) x ^ (
s - 1)`.
-/
@[expose] def partialGamma (s : ℂ) (X : ℝ) : ℂ :=
  ∫ x in 0..X, (-x).exp * x ^ (s - 1)
/-
**Complex.tendsto_partialGamma** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：tendsto_partialGamma {s : Complex} (hs : 0 < s.re) : Tendsto (fun X : Real
 => partialGamma s X) atTop (𝓝 <| GammaIntegral s)
参数：hs : 0 < s.re。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.intervalIntegral_tendsto_integral_Ioi`：intervalIntegral_te
ndsto_integral_Ioi (a : Real) (hfi : IntegrableOn f (Ioi a) μ) (hb : Tendsto b l
 atTop) : Tendsto (fun i => ∫ x in a..b i…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Complex.GammaIntegral_convergent`：GammaIntegral_convergent {s : Complex}
 (hs : 0 < s.re) : IntegrableOn (fun x => (-x).exp * x ^ (s - 1) : Real -> Compl
ex) (Ioi 0)
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
-/
theorem tendsto_partialGamma {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun X : ℝ => partialGamma s X) atTop (𝓝 <| GammaIntegral s) :=
  intervalIntegral_tendsto_integral_Ioi 0 (GammaIntegral_convergent hs) tendsto_id
/-
**Complex.Gamma_integrand_intervalIntegrable** 是 Mathlib 中的一个定理，位于命名空间 `Complex`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem Gamma_integrand_intervalIntegrable (s : ℂ) {X : ℝ} (hs : 0 < s.re) (hX : 0 ≤ X) :
    IntervalIntegrable (fun x => (-x).exp * x ^ (s - 1) : ℝ → ℂ) volume 0 X := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hX]
  exact IntegrableOn.mono_set (GammaIntegral_convergent hs) Ioc_subset_Ioi_self
/-
**Complex.Gamma_integrand_deriv_integrable_A** 是 Mathlib 中的一个定理，位于命名空间 `Complex`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem Gamma_integrand_deriv_integrable_A {s : ℂ} (hs : 0 < s.re) {X : ℝ} (hX : 0 ≤ X) :
    IntervalIntegrable (fun x => -((-x).exp * x ^ s) : ℝ → ℂ) volume 0 X := by
  convert! (Gamma_integrand_intervalIntegrable (s + 1) _ hX).neg
  · simp only [ofReal_exp, ofReal_neg, add_sub_cancel_right]; rfl
  · simp only [add_re, one_re]; linarith
/-
**Complex.Gamma_integrand_deriv_integrable_B** 是 Mathlib 中的一个定理，位于命名空间 `Complex`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem Gamma_integrand_deriv_integrable_B {s : ℂ} (hs : 0 < s.re) {Y : ℝ} (hY : 0 ≤ Y) :
    IntervalIntegrable (fun x : ℝ => (-x).exp * (s * x ^ (s - 1)) : ℝ → ℂ) volume 0 Y := by
  have : (fun x => (-x).exp * (s * x ^ (s - 1)) : ℝ → ℂ) =
      (fun x => s * ((-x).exp * x ^ (s - 1)) : ℝ → ℂ) := by ext1; ring
  rw [this, intervalIntegrable_iff_integrableOn_Ioc_of_le hY]
  constructor
  · refine (continuousOn_const.mul ?_).aestronglyMeasurable measurableSet_Ioc
    apply (continuous_ofReal.comp continuous_neg.rexp).continuousOn.mul
    apply continuousOn_of_forall_continuousAt
    intro x hx
    refine (?_ : ContinuousAt (fun x : ℂ => x ^ (s - 1)) _).comp continuous_ofReal.continuousAt
    exact continuousAt_cpow_const <| ofReal_mem_slitPlane.2 hx.1
  rw [← hasFiniteIntegral_norm_iff]
  simp_rw [norm_mul]
  refine (((Real.GammaIntegral_convergent hs).mono_set
    Ioc_subset_Ioi_self).hasFiniteIntegral.congr ?_).const_mul _
  rw [EventuallyEq, ae_restrict_iff']
  · filter_upwards with x hx
    rw [Complex.norm_of_nonneg (exp_pos _).le, norm_cpow_eq_rpow_re_of_pos hx.1]
    simp
  · exact measurableSet_Ioc

/-- The recurrence relation for the indefinite version of the `Γ` function. -/
/-
**Complex.partialGamma_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：partialGamma_add_one {s : Complex} (hs : 0 < s.re) {X : Real} (hX : 0 <= X
) : partialGamma (s + 1) X = s * partialGamma s X - (-X).exp * X ^ s
参数：hs : 0 < s.re；hX : 0 <= X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.partialGamma.eq_1`：∀ (s : ℂ) (X : ℝ), s.partialGamma X = ∫ (x : 
ℝ) in 0..X, ↑(Real.exp (-x)) * ↑x ^ (s - 1)
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `HasDerivAt.exp`：HasDerivAt.exp (hf : HasDerivAt f f' x) : HasDerivAt (fu
n x => Real.exp (f x)) (Real.exp (f x) * f') x
· 使用定理 `hasDerivAt_neg`：hasDerivAt_neg : HasDerivAt Neg.neg (-1) x
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `HasDerivAt.cpow_const`：HasDerivAt.cpow_const (hf : HasDerivAt f f' x) (h
0 : f x in slitPlane) : HasDerivAt (fun x => f x ^ c) (c * f x ^ (c - 1) * f') x
· 使用定理 `hasDerivAt_id`：hasDerivAt_id : HasDerivAt id 1 x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.ofReal_mem_slitPlane`：∀ {x : ℝ}, ↑x ∈ Complex.slitPlane ↔ 0 < x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `HasDerivAt.comp_ofReal`：HasDerivAt.comp_ofReal (hf : HasDerivAt e e' ↑z)
 : HasDerivAt (fun y : Real => e ↑y) e' z
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `HasDerivAt.mul`：HasDerivAt.mul (hc : HasDerivAt c c' x) (hd : HasDerivAt
 d d' x) : HasDerivAt (c * d) (c' * d x + c x * d') x
· 使用定理 `HasDerivAt.ofReal_comp`：HasDerivAt.ofReal_comp {f : Real -> Real} {u : R
eal} (hf : HasDerivAt f u z) : HasDerivAt (fun y : Real => ↑(f y) : Real -> Comp
lex) u z
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
（共 76 条，此处仅展示前 30 条）

--- 原说明 ---
The recurrence relation for the indefinite version of the `Γ` function.
-/
theorem partialGamma_add_one {s : ℂ} (hs : 0 < s.re) {X : ℝ} (hX : 0 ≤ X) :
    partialGamma (s + 1) X = s * partialGamma s X - (-X).exp * X ^ s := by
  rw [partialGamma, partialGamma, add_sub_cancel_right]
  have F_der_I : ∀ x : ℝ, x ∈ Ioo 0 X → HasDerivAt (fun x => (-x).exp * x ^ s : ℝ → ℂ)
      (-((-x).exp * x ^ s) + (-x).exp * (s * x ^ (s - 1))) x := by
    intro x hx
    have d1 : HasDerivAt (fun y : ℝ => (-y).exp) (-(-x).exp) x := by
      simpa using! (hasDerivAt_neg x).exp
    have d2 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ s) (s * x ^ (s - 1)) x := by
      have t := @HasDerivAt.cpow_const _ _ _ s (hasDerivAt_id ↑x) ?_
      · simpa only [mul_one] using! t.comp_ofReal
      · exact ofReal_mem_slitPlane.2 hx.1
    simpa only [ofReal_neg, neg_mul] using! d1.ofReal_comp.mul d2
  have cont := (continuous_ofReal.comp continuous_neg.rexp).mul (continuous_ofReal_cpow_const hs)
  have der_ible :=
    (Gamma_integrand_deriv_integrable_A hs hX).add (Gamma_integrand_deriv_integrable_B hs hX)
  have int_eval := integral_eq_sub_of_hasDerivAt_of_le hX cont.continuousOn F_der_I der_ible
  -- We are basically done here but manipulating the output into the right form is fiddly.
  apply_fun fun x : ℂ => -x at int_eval
  rw [intervalIntegral.integral_add (Gamma_integrand_deriv_integrable_A hs hX)
      (Gamma_integrand_deriv_integrable_B hs hX),
    intervalIntegral.integral_neg, neg_add, neg_neg] at int_eval
  rw [eq_sub_of_add_eq int_eval, sub_neg_eq_add, neg_sub, add_comm, add_sub]
  have hn : s ≠ 0 := by contrapose! hs; rw [hs, zero_re]
  simp only [Pi.mul_apply, Function.comp_apply, ofReal_zero, zero_cpow hn, mul_zero, add_zero,
    ← intervalIntegral.integral_const_mul]
  congr with x
  ring

/-- The recurrence relation for the `Γ` integral. -/
/-
**Complex.GammaIntegral_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：GammaIntegral_add_one {s : Complex} (hs : 0 < s.re) : GammaIntegral (s + 1
) = s * GammaIntegral s
参数：hs : 0 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventuallyEq_of_mem`：eventuallyEq_of_mem {l : Filter α} {f g : α 
-> β} {s : Set α} (hs : s in l) (h : EqOn f g s) : f =ᶠ[l] g
· 使用定理 `Filter.Ici_mem_atTop`：Ici_mem_atTop [Preorder α] (a : α) : Ici a in (atT
op : Filter α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.partialGamma_add_one`：partialGamma_add_one {s : Complex} (hs : 0
 < s.re) {X : Real} (hX : 0 <= X) : partialGamma (s + 1) X = s * partialGamma s 
X - (-X).exp * X ^…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ici
 b ↔ b ≤ x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
（共 102 条，此处仅展示前 30 条）

--- 原说明 ---
The recurrence relation for the `Γ` integral.
-/
theorem GammaIntegral_add_one {s : ℂ} (hs : 0 < s.re) :
    GammaIntegral (s + 1) = s * GammaIntegral s := by
  suffices Tendsto (s + 1).partialGamma atTop (𝓝 <| s * GammaIntegral s) by
    refine tendsto_nhds_unique ?_ this
    apply tendsto_partialGamma; rw [add_re, one_re]; linarith
  have : (fun X : ℝ => s * partialGamma s X - X ^ s * (-X).exp) =ᶠ[atTop]
      (s + 1).partialGamma := by
    apply eventuallyEq_of_mem (Ici_mem_atTop (0 : ℝ))
    intro X hX
    rw [partialGamma_add_one hs (mem_Ici.mp hX)]
    ring_nf
  refine Tendsto.congr' this ?_
  suffices Tendsto (fun X => -X ^ s * (-X).exp : ℝ → ℂ) atTop (𝓝 0) by
    simpa using! Tendsto.add (Tendsto.const_mul s (tendsto_partialGamma hs)) this
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have :
      (fun e : ℝ => ‖-(e : ℂ) ^ s * (-e).exp‖) =ᶠ[atTop] fun e : ℝ => e ^ s.re * (-1 * e).exp := by
    refine eventuallyEq_of_mem (Ioi_mem_atTop 0) ?_
    intro x hx; dsimp only
    rw [norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos hx,
      Complex.norm_of_nonneg (exp_pos (-x)).le, neg_mul, one_mul]
  exact (tendsto_congr' this).mpr (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ zero_lt_one)

end GammaRecurrence

/-! Now we define `Γ(s)` on the whole complex plane, by recursion. -/


section GammaDef

/-- The `n`th function in this family is `Γ(s)` if `-n < s.re`, and junk otherwise. -/
/-
**Complex.GammaAux** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`th function in this family is `Γ(s)` if `-n < s.re`, and junk otherwise.
-/
private noncomputable def GammaAux : ℕ → ℂ → ℂ
  | 0 => GammaIntegral
  | n + 1 => fun s : ℂ => GammaAux n (s + 1) / s
/-
**Complex.GammaAux_recurrence1** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem GammaAux_recurrence1 (s : ℂ) (n : ℕ) (h1 : -s.re < ↑n) :
    GammaAux n s = GammaAux n (s + 1) / s := by
  induction n generalizing s with
  | zero =>
    simp only [CharP.cast_eq_zero, Left.neg_neg_iff] at h1
    dsimp only [GammaAux]; rw [GammaIntegral_add_one h1]
    rw [mul_comm, mul_div_cancel_right₀]; contrapose! h1; rw [h1]
    simp
  | succ n hn =>
    dsimp only [GammaAux]
    have hh1 : -(s + 1).re < n := by
      rw [Nat.cast_add, Nat.cast_one] at h1
      rw [add_re, one_re]; linarith
    rw [← hn (s + 1) hh1]
/-
**Complex.GammaAux_recurrence2** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem GammaAux_recurrence2 (s : ℂ) (n : ℕ) (h1 : -s.re < ↑n) :
    GammaAux n s = GammaAux (n + 1) s := by
  rcases n with - | n
  · simp only [CharP.cast_eq_zero, Left.neg_neg_iff] at h1
    dsimp only [GammaAux]
    rw [GammaIntegral_add_one h1, mul_div_cancel_left₀]
    rintro rfl
    rw [zero_re] at h1
    exact h1.false
  · dsimp only [GammaAux]
    have : GammaAux n (s + 1 + 1) / (s + 1) = GammaAux n (s + 1) := by
      have hh1 : -(s + 1).re < n := by
        rw [Nat.cast_add, Nat.cast_one] at h1
        rw [add_re, one_re]; linarith
      rw [GammaAux_recurrence1 (s + 1) n hh1]
    rw [this]

/- This definition is deliberately not @[expose]'d, since `GammaAux` is not mathematically
interesting. -/
/-- The `Γ` function (of a complex variable `s`). -/
/-
**Complex.Gamma** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：ℂ → ℂ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Γ` function (of a complex variable `s`).
-/
@[irreducible, pp_nodot] def Gamma (s : ℂ) : ℂ :=
  GammaAux ⌊1 - s.re⌋₊ s
/-
**Complex.Gamma_eq_GammaAux** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem Gamma_eq_GammaAux (s : ℂ) (n : ℕ) (h1 : -s.re < ↑n) : Gamma s = GammaAux n s := by
  have u : ∀ k : ℕ, GammaAux (⌊1 - s.re⌋₊ + k) s = Gamma s := fun k ↦ by
    induction k with
    | zero => simp [Gamma]
    | succ k hk =>
      rw [← hk, ← add_assoc]
      refine (GammaAux_recurrence2 s (⌊1 - s.re⌋₊ + k) ?_).symm
      rw [Nat.cast_add]
      have i0 := Nat.sub_one_lt_floor (1 - s.re)
      simp only [sub_sub_cancel_left] at i0
      refine lt_add_of_lt_of_nonneg i0 ?_
      rw [← Nat.cast_zero, Nat.cast_le]; exact Nat.zero_le k
  convert! (u <| n - ⌊1 - s.re⌋₊).symm; rw [Nat.add_sub_of_le]
  by_cases h : 0 ≤ 1 - s.re
  · apply Nat.le_of_lt_succ
    exact_mod_cast lt_of_le_of_lt (Nat.floor_le h) (by linarith : 1 - s.re < n + 1)
  · rw [Nat.floor_of_nonpos]
    · lia
    · linarith

/-- The recurrence relation for the `Γ` function. -/
@[grind =]
/-
**Complex.Gamma_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：Gamma_add_one (s : Complex) (h2 : s != 0) : Gamma (s + 1) = s * Gamma s
参数：s : Complex；h2 : s != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a - b - a = -b
· 使用定理 `Nat.sub_one_lt_floor`：sub_one_lt_floor (a : R) : a - 1 < ⌊a⌋₊
· 使用定理 `Complex.add_re`：add_re (z w : Complex) : (z + w).re = z.re + w.re
· 使用定理 `Complex.one_re`：one_re : (1 : Complex).re = 1
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
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
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
（共 68 条，此处仅展示前 30 条）

--- 原说明 ---
The recurrence relation for the `Γ` function.
-/
theorem Gamma_add_one (s : ℂ) (h2 : s ≠ 0) : Gamma (s + 1) = s * Gamma s := by
  let n := ⌊1 - s.re⌋₊
  have t1 : -s.re < n := by simpa only [sub_sub_cancel_left] using Nat.sub_one_lt_floor (1 - s.re)
  have t2 : -(s + 1).re < n := by rw [add_re, one_re]; linarith
  rw [Gamma_eq_GammaAux s n t1, Gamma_eq_GammaAux (s + 1) n t2, GammaAux_recurrence1 s n t1]
  field
/-
**Complex.Gamma_eq_integral** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：Gamma_eq_integral {s : Complex} (hs : 0 < s.re) : Gamma s = GammaIntegral 
s
参数：hs : 0 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Gamma.Basic.0.Complex.Gamma_e
q_GammaAux`：∀ (s : ℂ) (n : ℕ), -s.re < ↑n → Complex.Gamma s = Complex.GammaAux✝ 
n s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Tactic.Linarith.add_lt_of_neg_of_le`：add_lt_of_neg_of_le [IsStri
ctOrderedRing α] {a b c : α} (ha : a < 0) (hbc : b <= c) : a + b < c
· 使用定理 `Mathlib.Tactic.Linarith.sub_neg_of_lt`：sub_neg_of_lt [IsOrderedRing α] {
a b : α} : a < b -> a - b < 0
（共 31 条，此处仅展示前 30 条）
-/
theorem Gamma_eq_integral {s : ℂ} (hs : 0 < s.re) : Gamma s = GammaIntegral s :=
  Gamma_eq_GammaAux s 0 (by norm_cast; linarith)

@[simp]
/-
**Complex.Gamma_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：Gamma_one : Gamma 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.Gamma_eq_integral`：Gamma_eq_integral {s : Complex} (hs : 0 < s.r
e) : Gamma s = GammaIntegral s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.GammaIntegral_one`：GammaIntegral_one : GammaIntegral 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Gamma_one : Gamma 1 = 1 := by rw [Gamma_eq_integral] <;> simp
/-
**Complex.Gamma_nat_eq_factorial** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：Gamma_nat_eq_factorial (n : Nat) : Gamma (n + 1) = n !
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Complex.Gamma_one`：Gamma_one : Gamma 1 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Complex.Gamma_add_one`：Gamma_add_one (s : Complex) (h2 : s != 0) : Gamma
 (s + 1) = s * Gamma s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
-/
theorem Gamma_nat_eq_factorial (n : ℕ) : Gamma (n + 1) = n ! := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Gamma_add_one n.succ <| Nat.cast_ne_zero.mpr <| Nat.succ_ne_zero n]
    simp only [Nat.cast_succ, Nat.factorial_succ, Nat.cast_mul]
    congr

@[simp]
/-
**Complex.Gamma_ofNat_eq_factorial** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：Gamma_ofNat_eq_factorial (n : Nat) [(n + 1).AtLeastTwo] : Gamma (ofNat(n +
 1) : Complex) = n !
参数：n : Nat；n + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Complex.Gamma_nat_eq_factorial`：Gamma_nat_eq_factorial (n : Nat) : Gamma
 (n + 1) = n !
-/
theorem Gamma_ofNat_eq_factorial (n : ℕ) [(n + 1).AtLeastTwo] :
    Gamma (ofNat(n + 1) : ℂ) = n ! :=
  mod_cast Gamma_nat_eq_factorial (n : ℕ)

/-- At `0` the Gamma function is undefined; by convention we assign it the value `0`. -/
@[simp]
/-
**Complex.Gamma_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：Gamma_zero : Gamma 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Gamma.Basic.0.Complex.Gamma.e
q_1`：∀ (s : ℂ), Complex.Gamma s = Complex.GammaAux✝ ⌊1 - s.re⌋₊ s
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Nat.floor_one`：floor_one : ⌊(1 : R)⌋₊ = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
At `0` the Gamma function is undefined; by convention we assign it the value `0`
.
-/
theorem Gamma_zero : Gamma 0 = 0 := by
  simp_rw [Gamma, zero_re, sub_zero, Nat.floor_one, GammaAux, div_zero]

/-- At `-n` for `n ∈ ℕ`, the Gamma function is undefined; by convention we assign it the value 0. -/
/-
**Complex.Gamma_neg_nat_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：Gamma_neg_nat_eq_zero (n : Nat) : Gamma (-n) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Complex.Gamma_zero`：Gamma_zero : Gamma 0 = 0
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `neg_add_cancel_comm`：∀ {G : Type u_1} [inst : AddCommGroup G] (a b : G),
 -a + b + a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Complex.Gamma_add_one`：Gamma_add_one (s : Complex) (h2 : s != 0) : Gamma
 (s + 1) = s * Gamma s

--- 原说明 ---
At `-n` for `n ∈ ℕ`, the Gamma function is undefined; by convention we assign it
 the value 0.
-/
theorem Gamma_neg_nat_eq_zero (n : ℕ) : Gamma (-n) = 0 := by
  induction n with
  | zero => rw [Nat.cast_zero, neg_zero, Gamma_zero]
  | succ n IH =>
    have A : -(n.succ : ℂ) ≠ 0 := by
      rw [neg_ne_zero, Nat.cast_ne_zero]
      apply Nat.succ_ne_zero
    have : -(n : ℂ) = -↑n.succ + 1 := by simp
    rw [this, Gamma_add_one _ A] at IH
    contrapose! IH
    exact mul_ne_zero A IH
/-
**Complex.Gamma_conj** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：Gamma_conj (s : Complex) : Gamma (conj s) = conj (Gamma s)
参数：s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Gamma.Basic.0.Complex.GammaAu
x.eq_1`：Complex.GammaAux✝ 0 = Complex.GammaIntegral
· 使用定理 `Complex.GammaIntegral_conj`：GammaIntegral_conj (s : Complex) : GammaInte
gral (conj s) = conj (GammaIntegral s)
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Gamma.Basic.0.Complex.GammaAu
x.eq_2`：∀ (n : ℕ), Complex.GammaAux✝ n.succ = fun s => Complex.GammaAux✝ n (s + 
1) / s
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Complex.conj_inv`：conj_inv (x : Complex) : conj x⁻¹ = (conj x)⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Gamma.Basic.0.Complex.Gamma.e
q_1`：∀ (s : ℂ), Complex.Gamma s = Complex.GammaAux✝ ⌊1 - s.re⌋₊ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Gamma_conj (s : ℂ) : Gamma (conj s) = conj (Gamma s) := by
  suffices ∀ (n : ℕ) (s : ℂ), GammaAux n (conj s) = conj (GammaAux n s) by
    simp [Gamma, this]
  intro n
  induction n with
  | zero => rw [GammaAux]; exact GammaIntegral_conj
  | succ n IH =>
    intro s
    rw [GammaAux]
    dsimp only
    rw [div_eq_mul_inv _ s, map_mul, conj_inv, ← div_eq_mul_inv]
    suffices conj s + 1 = conj (s + 1) by rw [this, IH]
    rw [map_add, map_one]

/-- Expresses the integral over `Ioi 0` of `t ^ (a - 1) * exp (-(r * t))` in terms of the Gamma
function, for complex `a`. -/
/-
**Complex.integral_cpow_mul_exp_neg_mul_Ioi** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：integral_cpow_mul_exp_neg_mul_Ioi {a : Complex} {r : Real} (ha : 0 < a.re)
 (hr : 0 < r) : ∫ (t : Real) in Ioi 0, t ^ (a - 1) * exp (-(r * t)) = (1 / r) ^ 
a * Gamma a
参数：ha : 0 < a.re；hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.cpow_one`：cpow_one (x : Complex) : x ^ (1 : Complex) = x
· 使用定理 `Complex.cpow_add`：cpow_add {x : Complex} (y z : Complex) (hx : x != 0) :
 x ^ (y + z) = x ^ y * x ^ z
· 使用定理 `one_div_ne_zero`：one_div_ne_zero {a : G₀} (h : a != 0) : 1 / a != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.ofReal_ne_zero`：ofReal_ne_zero {z : Real} : (z : Complex) != 0 ↔
 z != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `MeasureTheory.setIntegral_congr_fun`：setIntegral_congr_fun (hs : Measura
bleSet s) (h : EqOn f g s) : ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Complex.mul_cpow_ofReal_nonneg`：mul_cpow_ofReal_nonneg {a b : Real} (ha 
: 0 <= a) (hb : 0 <= b) (r : Complex) : ((a : Complex) * (b : Complex)) ^ r = (a
 : Complex) ^ r * (b…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `Complex.ofReal_one`：ofReal_one : ((1 : Real) : Complex) = 1
· 使用定理 `Complex.one_cpow`：one_cpow (x : Complex) : (1 : Complex) ^ x = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
Expresses the integral over `Ioi 0` of `t ^ (a - 1) * exp (-(r * t))` in terms o
f the Gamma
function, for complex `a`.
-/
lemma integral_cpow_mul_exp_neg_mul_Ioi {a : ℂ} {r : ℝ} (ha : 0 < a.re) (hr : 0 < r) :
    ∫ (t : ℝ) in Ioi 0, t ^ (a - 1) * exp (-(r * t)) = (1 / r) ^ a * Gamma a := by
  have aux : (1 / r : ℂ) ^ a = 1 / r * (1 / r) ^ (a - 1) := by
    nth_rewrite 2 [← cpow_one (1 / r : ℂ)]
    rw [← cpow_add _ _ (one_div_ne_zero <| ofReal_ne_zero.mpr hr.ne'), add_sub_cancel]
  calc
    _ = ∫ (t : ℝ) in Ioi 0, (1 / r) ^ (a - 1) * (r * t) ^ (a - 1) * exp (-(r * t)) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx ↦ ?_)
      rw [mem_Ioi] at hx
      rw [mul_cpow_ofReal_nonneg hr.le hx.le, ← mul_assoc, one_div, ← ofReal_inv,
        ← mul_cpow_ofReal_nonneg (inv_pos.mpr hr).le hr.le, ← ofReal_mul r⁻¹,
        inv_mul_cancel₀ hr.ne', ofReal_one, one_cpow, one_mul]
    _ = 1 / r * ∫ (t : ℝ) in Ioi 0, (1 / r) ^ (a - 1) * t ^ (a - 1) * exp (-t) := by
      simp_rw [← ofReal_mul]
      rw [integral_comp_mul_left_Ioi (fun x ↦ _ * x ^ (a - 1) * exp (-x)) _ hr, mul_zero,
        real_smul, ← one_div, ofReal_div, ofReal_one]
    _ = 1 / r * (1 / r : ℂ) ^ (a - 1) * (∫ (t : ℝ) in Ioi 0, t ^ (a - 1) * exp (-t)) := by
      simp_rw [← MeasureTheory.integral_const_mul, mul_assoc]
    _ = (1 / r) ^ a * Gamma a := by
      rw [aux, Gamma_eq_integral ha]
      congr 2 with x
      rw [ofReal_exp, ofReal_neg, mul_comm]

end GammaDef

end Complex

namespace Real

/-- The `Γ` function (of a real variable `s`). -/
/-
**Real.Gamma** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：ℝ → ℝ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Γ` function (of a real variable `s`).
-/
@[pp_nodot, expose] def Gamma (s : ℝ) : ℝ :=
  (Complex.Gamma s).re
/-
**Real.Gamma_eq_integral** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：Gamma_eq_integral {s : Real} (hs : 0 < s) : Gamma s = ∫ x in Ioi 0, exp (-
x) * x ^ (s - 1)
参数：hs : 0 < s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Gamma.eq_1`：∀ (s : ℝ), Real.Gamma s = (Complex.Gamma ↑s).re
· 使用定理 `Complex.Gamma_eq_integral`：Gamma_eq_integral {s : Complex} (hs : 0 < s.r
e) : Gamma s = GammaIntegral s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `RCLike.ofReal_pos`：ofReal_pos {x : Real} : 0 < (x : K) ↔ 0 < x
· 使用定理 `Complex.GammaIntegral_ofReal`：GammaIntegral_ofReal (s : Real) : GammaInt
egral ↑s = ↑(∫ x : Real in Ioi 0, Real.exp (-x) * x ^ (s - 1))
· 使用定理 `Complex.ofReal_re`：ofReal_re (r : Real) : Complex.re (r : Complex) = r
-/
theorem Gamma_eq_integral {s : ℝ} (hs : 0 < s) :
    Gamma s = ∫ x in Ioi 0, exp (-x) * x ^ (s - 1) := by
  rw [Gamma, Complex.Gamma_eq_integral (RCLike.ofReal_pos.mp hs), Complex.GammaIntegral_ofReal,
    Complex.ofReal_re]
/-
**Real.Gamma_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：Gamma_add_one {s : Real} (hs : s != 0) : Gamma (s + 1) = s * Gamma s
参数：hs : s != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
· 使用定理 `Complex.ofReal_one`：ofReal_one : ((1 : Real) : Complex) = 1
· 使用定理 `Complex.Gamma_add_one`：Gamma_add_one (s : Complex) (h2 : s != 0) : Gamma
 (s + 1) = s * Gamma s
· 使用定理 `Complex.ofReal_ne_zero`：ofReal_ne_zero {z : Real} : (z : Complex) != 0 ↔
 z != 0
· 使用定理 `Complex.re_ofReal_mul`：re_ofReal_mul (r : Real) (z : Complex) : (r * z).
re = r * z.re
-/
theorem Gamma_add_one {s : ℝ} (hs : s ≠ 0) : Gamma (s + 1) = s * Gamma s := by
  simp_rw [Gamma]
  rw [Complex.ofReal_add, Complex.ofReal_one, Complex.Gamma_add_one, Complex.re_ofReal_mul]
  rwa [Complex.ofReal_ne_zero]

@[simp]
/-
**Real.Gamma_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：Gamma_one : Gamma 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Gamma.eq_1`：∀ (s : ℝ), Real.Gamma s = (Complex.Gamma ↑s).re
· 使用定理 `Complex.ofReal_one`：ofReal_one : ((1 : Real) : Complex) = 1
· 使用定理 `Complex.Gamma_one`：Gamma_one : Gamma 1 = 1
· 使用定理 `Complex.one_re`：one_re : (1 : Complex).re = 1
-/
theorem Gamma_one : Gamma 1 = 1 := by
  rw [Gamma, Complex.ofReal_one, Complex.Gamma_one, Complex.one_re]
/-
**Real._root_.Complex.Gamma_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Complex.Gamma_ofReal (s : ℝ) : Complex.Gamma (s : ℂ) = Gamma s := by
  rw [Gamma, eq_comm, ← Complex.conj_eq_iff_re, ← Complex.Gamma_conj, Complex.conj_ofReal]
/-
**Real.Gamma_nat_eq_factorial** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：Gamma_nat_eq_factorial (n : Nat) : Gamma (n + 1) = n !
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Gamma.eq_1`：∀ (s : ℝ), Real.Gamma s = (Complex.Gamma ↑s).re
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
· 使用定理 `Complex.ofReal_natCast`：∀ (n : ℕ), ↑↑n = ↑n
· 使用定理 `Complex.ofReal_one`：ofReal_one : ((1 : Real) : Complex) = 1
· 使用定理 `Complex.Gamma_nat_eq_factorial`：Gamma_nat_eq_factorial (n : Nat) : Gamma
 (n + 1) = n !
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_re`：ofReal_re (r : Real) : Complex.re (r : Complex) = r
-/
theorem Gamma_nat_eq_factorial (n : ℕ) : Gamma (n + 1) = n ! := by
  rw [Gamma, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
    Complex.Gamma_nat_eq_factorial, ← Complex.ofReal_natCast, Complex.ofReal_re]

@[simp]
/-
**Real.Gamma_ofNat_eq_factorial** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：Gamma_ofNat_eq_factorial (n : Nat) [(n + 1).AtLeastTwo] : Gamma (ofNat(n +
 1) : Real) = n !
参数：n : Nat；n + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Real.Gamma_nat_eq_factorial`：Gamma_nat_eq_factorial (n : Nat) : Gamma (n
 + 1) = n !
-/
theorem Gamma_ofNat_eq_factorial (n : ℕ) [(n + 1).AtLeastTwo] :
    Gamma (ofNat(n + 1) : ℝ) = n ! :=
  mod_cast Gamma_nat_eq_factorial (n : ℕ)

/-- At `0` the Gamma function is undefined; by convention we assign it the value `0`. -/
@[simp]
/-
**Real.Gamma_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：Gamma_zero : Gamma 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.Gamma_ofReal`：∀ (s : ℝ), Complex.Gamma ↑s = ↑(Real.Gamma s)
· 使用定理 `Complex.Gamma_zero`：Gamma_zero : Gamma 0 = 0

--- 原说明 ---
At `0` the Gamma function is undefined; by convention we assign it the value `0`
.
-/
theorem Gamma_zero : Gamma 0 = 0 := by
  simpa only [← Complex.ofReal_zero, Complex.Gamma_ofReal, Complex.ofReal_inj] using
    Complex.Gamma_zero

/-- At `-n` for `n ∈ ℕ`, the Gamma function is undefined; by convention we assign it the value `0`.
-/
/-
**Real.Gamma_neg_nat_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：Gamma_neg_nat_eq_zero (n : Nat) : Gamma (-n) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.Gamma_ofReal`：∀ (s : ℝ), Complex.Gamma ↑s = ↑(Real.Gamma s)
· 使用定理 `Complex.Gamma_neg_nat_eq_zero`：Gamma_neg_nat_eq_zero (n : Nat) : Gamma (
-n) = 0

--- 原说明 ---
At `-n` for `n ∈ ℕ`, the Gamma function is undefined; by convention we assign it
 the value `0`.
-/
theorem Gamma_neg_nat_eq_zero (n : ℕ) : Gamma (-n) = 0 := by
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_neg, Complex.Gamma_ofReal,
    Complex.ofReal_eq_zero] using Complex.Gamma_neg_nat_eq_zero n
/-
**Real.Gamma_pos_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：Gamma_pos_of_pos {s : Real} (hs : 0 < s) : 0 < Gamma s
参数：hs : 0 < s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Gamma_eq_integral`：Gamma_eq_integral {s : Real} (hs : 0 < s) : Gamm
a s = ∫ x in Ioi 0, exp (-x) * x ^ (s - 1)
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
· 使用定理 `Function.mem_support`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M] {f
 : ι → M} {x : ι}, x ∈ Function.support f ↔ f x ≠ 0
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae`：setIntegral_pos_
iff_support_of_nonneg_ae {f : X -> Real} (hf : 0 <=ᵐ[μ.restrict s] f) (hfi : Int
egrableOn f s μ) : (0 < ∫ x in s, f x ∂μ) ↔ …
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.self_mem_ae_restrict`：self_mem_ae_restrict {s} (hs : Measu
rableSet s) : s in ae (μ.restrict s)
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.GammaIntegral_convergent`：GammaIntegral_convergent {s : Real} (h : 
0 < s) : IntegrableOn (fun x : Real => exp (-x) * x ^ (s - 1)) (Ioi 0)
· 使用定理 `Real.volume_Ioi`：volume_Ioi {a : Real} : volume (Ioi a) = ∞
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `ENNReal.ofReal_lt_top`：∀ {r : ℝ}, ENNReal.ofReal r < ⊤
-/
theorem Gamma_pos_of_pos {s : ℝ} (hs : 0 < s) : 0 < Gamma s := by
  rw [Gamma_eq_integral hs]
  have : (Function.support fun x : ℝ => exp (-x) * x ^ (s - 1)) ∩ Ioi 0 = Ioi 0 := by
    rw [inter_eq_right]
    intro x hx
    rw [Function.mem_support]
    exact mul_ne_zero (exp_pos _).ne' (rpow_pos_of_pos hx _).ne'
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · rw [this, volume_Ioi, ← ENNReal.ofReal_zero]
    exact ENNReal.ofReal_lt_top
  · refine eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi) ?_
    exact fun x hx => (mul_pos (exp_pos _) (rpow_pos_of_pos hx _)).le
  · exact GammaIntegral_convergent hs
/-
**Real.Gamma_nonneg_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：Gamma_nonneg_of_nonneg {s : Real} (hs : 0 <= s) : 0 <= Gamma s
参数：hs : 0 <= s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Gamma_zero`：Gamma_zero : Gamma 0 = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.Gamma_pos_of_pos`：Gamma_pos_of_pos {s : Real} (hs : 0 < s) : 0 < Ga
mma s
-/
theorem Gamma_nonneg_of_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ Gamma s := by
  obtain rfl | h := eq_or_lt_of_le hs
  · rw [Gamma_zero]
  · exact (Gamma_pos_of_pos h).le

open Complex in
/-- Expresses the integral over `Ioi 0` of `t ^ (a - 1) * exp (-(r * t))`, for positive real `r`,
in terms of the Gamma function. -/
/-
**Real.integral_rpow_mul_exp_neg_mul_Ioi** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：integral_rpow_mul_exp_neg_mul_Ioi {a r : Real} (ha : 0 < a) (hr : 0 < r) :
 ∫ t : Real in Ioi 0, t ^ (a - 1) * exp (-(r * t)) = (1 / r) ^ a * Gamma a
参数：ha : 0 < a；hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_inj`：ofReal_inj {z w : Real} : (z : Complex) = w ↔ z = w
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.Gamma_ofReal`：∀ (s : ℝ), Complex.Gamma ↑s = ↑(Real.Gamma s)
· 使用定理 `Complex.ofReal_cpow`：ofReal_cpow {x : Real} (hx : 0 <= x) (y : Real) : (
(x ^ y : Real) : Complex) = (x : Complex) ^ (y : Complex)
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Complex.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : Complex)
 = r / s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `integral_ofReal`：integral_ofReal {f : X -> Real} : ∫ x, (f x : 𝕜) ∂μ = ↑
(∫ x, f x ∂μ)
· 使用定理 `MeasureTheory.setIntegral_congr_fun`：setIntegral_congr_fun (hs : Measura
bleSet s) (h : EqOn f g s) : ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `RCLike.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : K) = r * 
s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
Expresses the integral over `Ioi 0` of `t ^ (a - 1) * exp (-(r * t))`, for posit
ive real `r`,
in terms of the Gamma function.
-/
lemma integral_rpow_mul_exp_neg_mul_Ioi {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∫ t : ℝ in Ioi 0, t ^ (a - 1) * exp (-(r * t)) = (1 / r) ^ a * Gamma a := by
  rw [← ofReal_inj, ofReal_mul, ← Gamma_ofReal, ofReal_cpow (by positivity), ofReal_div]
  convert! integral_cpow_mul_exp_neg_mul_Ioi (by rwa [ofReal_re] : 0 < (a : ℂ).re) hr
  refine integral_ofReal.symm.trans <| setIntegral_congr_fun measurableSet_Ioi (fun t ht ↦ ?_)
  norm_cast
  simp_rw [← ofReal_cpow ht.le, RCLike.ofReal_mul, coe_algebraMap]

open Lean.Meta Qq Mathlib.Meta.Positivity in
/-- The `positivity` extension which identifies expressions of the form `Gamma a`. -/
@[positivity Gamma (_ : ℝ)]
meta def _root_.Mathlib.Meta.Positivity.evalGamma : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(Gamma $a) =>
    match ← core q(inferInstance) (some q(inferInstance)) a with
    | .positive pa =>
      assertInstancesCommute
      pure (.positive q(Gamma_pos_of_pos $pa))
    | .nonnegative pa =>
      assertInstancesCommute
      pure (.nonnegative q(Gamma_nonneg_of_nonneg $pa))
    | _ => pure .none
  | _, _, _ => throwError "failed to match on Gamma application"

/-- The Gamma function does not vanish on `ℝ` (except at non-positive integers, where the function
is mathematically undefined and we set it to `0` by convention). -/
/-
**Real.Gamma_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：Gamma_ne_zero {s : Real} (hs : forall m : Nat, s != -m) : Gamma s != 0
参数：hs : forall m : Nat, s != -m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.Gamma_pos_of_pos`：Gamma_pos_of_pos {s : Real} (hs : 0 < s) : 0 < Ga
mma s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
（共 62 条，此处仅展示前 30 条）

--- 原说明 ---
The Gamma function does not vanish on `ℝ` (except at non-positive integers, wher
e the function
is mathematically undefined and we set it to `0` by convention).
-/
theorem Gamma_ne_zero {s : ℝ} (hs : ∀ m : ℕ, s ≠ -m) : Gamma s ≠ 0 := by
  suffices ∀ {n : ℕ}, -(n : ℝ) < s → Gamma s ≠ 0 by
    apply this
    swap
    · exact ⌊-s⌋₊ + 1
    rw [neg_lt, Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one _
  intro n
  induction n generalizing s with
  | zero =>
    intro hs
    refine (Gamma_pos_of_pos ?_).ne'
    rwa [Nat.cast_zero, neg_zero] at hs
  | succ _ n_ih =>
    intro hs'
    have : Gamma (s + 1) ≠ 0 := by
      apply n_ih
      · intro m
        specialize hs (1 + m)
        contrapose hs
        rw [← eq_sub_iff_add_eq] at hs
        rw [hs]
        push_cast
        ring
      · rw [Nat.cast_add, Nat.cast_one, neg_add] at hs'
        linarith
    rw [Gamma_add_one, mul_ne_zero_iff] at this
    · exact this.2
    · simpa using hs 0
/-
**Real.Gamma_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：Gamma_eq_zero_iff (s : Real) : Gamma s = 0 ↔ exists m : Nat, s = -m
参数：s : Real。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Real.Gamma_ne_zero`：Gamma_ne_zero {s : Real} (hs : forall m : Nat, s != 
-m) : Gamma s != 0
· 使用定理 `Real.Gamma_neg_nat_eq_zero`：Gamma_neg_nat_eq_zero (n : Nat) : Gamma (-n)
 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Gamma_eq_zero_iff (s : ℝ) : Gamma s = 0 ↔ ∃ m : ℕ, s = -m :=
  ⟨by contrapose!; exact Gamma_ne_zero, by rintro ⟨m, rfl⟩; exact Gamma_neg_nat_eq_zero m⟩

end Real

