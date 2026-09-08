/-
Copyright (c) 2022 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara
-/
module

public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Locally uniform limits of holomorphic functions

This file gathers some results about locally uniform limits of holomorphic functions on an open
subset of the complex plane.

## Main results

* `TendstoLocallyUniformlyOn.differentiableOn`: A locally uniform limit of holomorphic functions
  is holomorphic.
* `TendstoLocallyUniformlyOn.deriv`: Locally uniform convergence implies locally uniform
  convergence of the derivatives to the derivative of the limit.
-/

@[expose] public section


open Set Metric MeasureTheory Filter Complex intervalIntegral

open scoped Real Topology

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U K : Set ℂ}
  {z : ℂ} {M r δ : ℝ} {φ : Filter ι} {F : ι → ℂ → E} {f g : ℂ → E}

namespace Complex

section Cderiv

/-- A circle integral which coincides with `deriv f z` whenever one can apply the Cauchy formula for
the derivative. It is useful in the proof that locally uniform limits of holomorphic functions are
holomorphic, because it depends continuously on `f` for the uniform topology. -/
/-
**Complex.cderiv** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：cderiv (r : Real) (f : Complex -> E) (z : Complex) : E
参数：r : Real；f : Complex -> E；z : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A circle integral which coincides with `deriv f z` whenever one can apply the Ca
uchy formula for
the derivative. It is useful in the proof that locally uniform limits of holomor
phic functions are
holomorphic, because it depends continuously on `f` for the uniform topology.
-/
noncomputable def cderiv (r : ℝ) (f : ℂ → E) (z : ℂ) : E :=
  (2 * π * I : ℂ)⁻¹ • ∮ w in C(z, r), ((w - z) ^ 2)⁻¹ • f w
/-
**Complex.cderiv_eq_deriv** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：cderiv_eq_deriv [CompleteSpace E] (hU : IsOpen U) (hf : DifferentiableOn C
omplex f U) (hr : 0 < r) (hzr : closedBall z r subseteq U) : cderiv r f z = deri
v f z
参数：hU : IsOpen U；hf : DifferentiableOn Complex f U；hr : 0 < r；hzr : closedBall z
 r subseteq U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiab
le`：two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable {U : Set 
Complex} (hU : IsOpen U) {c w₀ : Complex} {R : Real} {f : Comple…
· 使用定理 `Metric.mem_ball_self`：mem_ball_self (h : 0 < ε) : x in ball x ε
-/
theorem cderiv_eq_deriv [CompleteSpace E] (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hr : 0 < r)
    (hzr : closedBall z r ⊆ U) : cderiv r f z = deriv f z :=
  two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable hU hzr hf (mem_ball_self hr)
/-
**Complex.norm_cderiv_le** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_cderiv_le (hr : 0 < r) (hf : forall w in sphere z r, ‖f w‖ <= M) : ‖c
deriv r f z‖ <= M / r
参数：hr : 0 < r；hf : forall w in sphere z r, ‖f w‖ <= M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NormedSpace.sphere_nonempty`：NormedSpace.sphere_nonempty {x : E} {r : Re
al} : (sphere x r).Nonempty ↔ 0 <= r
· 使用定理 `EMetric.instNontrivialTopologyOfNontrivial`：∀ {α : Type u_2} [inst : EMe
tricSpace α] [Nontrivial α], NontrivialTopology α
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `inv_mul_eq_div`：inv_mul_eq_div : a⁻¹ * b = b / a
· 使用引理 `div_le_div₀`：div_le_div₀ (hc : 0 <= c) (hac : a <= c) (hd : 0 < d) (hdb 
: d <= b) : a / b <= c / d
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `sq_pos_of_pos`：sq_pos_of_pos [PosMulStrictMono M₀] (ha : 0 < a) : 0 < a 
^ 2
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
（共 87 条，此处仅展示前 30 条）
-/
theorem norm_cderiv_le (hr : 0 < r) (hf : ∀ w ∈ sphere z r, ‖f w‖ ≤ M) :
    ‖cderiv r f z‖ ≤ M / r := by
  have hM : 0 ≤ M := by
    obtain ⟨w, hw⟩ : (sphere z r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
    exact (norm_nonneg _).trans (hf w hw)
  have h1 : ∀ w ∈ sphere z r, ‖((w - z) ^ 2)⁻¹ • f w‖ ≤ M / r ^ 2 := by
    intro w hw
    simp only [mem_sphere_iff_norm] at hw hf
    simp only [norm_smul, inv_mul_eq_div, hw, norm_inv, norm_pow]
    exact div_le_div₀ hM (hf w hw) (sq_pos_of_pos hr) le_rfl
  have h2 := circleIntegral.norm_integral_le_of_norm_le_const hr.le h1
  simp only [cderiv, norm_smul]
  refine (mul_le_mul le_rfl h2 (norm_nonneg _) (norm_nonneg _)).trans (le_of_eq ?_)
  simp [field, abs_of_nonneg Real.pi_pos.le]
/-
**Complex.cderiv_sub** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：cderiv_sub (hr : 0 < r) (hf : ContinuousOn f (sphere z r)) (hg : Continuou
sOn g (sphere z r)) : cderiv r (f - g) z = cderiv r f z - cderiv r g z
参数：hr : 0 < r；hf : ContinuousOn f (sphere z r)；hg : ContinuousOn g (sphere z r)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.inv₀`：ContinuousOn.inv₀ (hf : ContinuousOn f s) (h0 : foral
l x in s, f x != 0) : ContinuousOn f⁻¹ s
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.fun_pow`：∀ {M : Type u_3} {X : Type u_5} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace M] [inst_2 : Monoid M]   [ContinuousMul M] {f
 : X → M…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `Continuous.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g 
: X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `sq_eq_zero_iff`：sq_eq_zero_iff : a ^ 2 = 0 ↔ a = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `mem_sphere_iff_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] 
{a b : E} {r : ℝ}, b ∈ Metric.sphere a r ↔ ‖b - a‖ = r
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `circleIntegral.integral_sub`：integral_sub {f g : Complex -> E} {c : Comp
lex} {R : Real} (hf : CircleIntegrable f c R) (hg : CircleIntegrable g c R) : (∮
 z in C(c, R), f …
· 使用定理 `ContinuousOn.circleIntegrable`：ContinuousOn.circleIntegrable {f : Comple
x -> E} {c : Complex} {R : Real} (hR : 0 <= R) (hf : ContinuousOn f (sphere c R)
) : CircleIntegrabl…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ContinuousOn.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [i
nst : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalS
pace Y] [in…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem cderiv_sub (hr : 0 < r) (hf : ContinuousOn f (sphere z r))
    (hg : ContinuousOn g (sphere z r)) : cderiv r (f - g) z = cderiv r f z - cderiv r g z := by
  have h1 : ContinuousOn (fun w : ℂ => ((w - z) ^ 2)⁻¹) (sphere z r) := by
    refine ((continuous_id'.fun_sub continuous_const).fun_pow 2).continuousOn.inv₀
      fun w hw h => hr.ne ?_
    rwa [mem_sphere_iff_norm, sq_eq_zero_iff.mp h, norm_zero] at hw
  simp_rw [cderiv, ← smul_sub]
  congr 1
  simpa only [Pi.sub_apply, smul_sub] using
    circleIntegral.integral_sub ((h1.fun_smul hf).circleIntegrable hr.le)
      ((h1.fun_smul hg).circleIntegrable hr.le)
/-
**Complex.norm_cderiv_lt** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_cderiv_lt (hr : 0 < r) (hfM : forall w in sphere z r, ‖f w‖ < M) (hf 
: ContinuousOn f (sphere z r)) : ‖cderiv r f z‖ < M / r
参数：hr : 0 < r；hfM : forall w in sphere z r, ‖f w‖ < M；hf : ContinuousOn f (spher
e z r)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NormedSpace.sphere_nonempty`：NormedSpace.sphere_nonempty {x : E} {r : Re
al} : (sphere x r).Nonempty ↔ 0 <= r
· 使用定理 `EMetric.instNontrivialTopologyOfNontrivial`：∀ {α : Type u_2} [inst : EMe
tricSpace α] [Nontrivial α], NontrivialTopology α
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `continuous_norm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Continu
ous fun a => ‖a‖
· 使用定理 `IsCompact.exists_isMaxOn`：IsCompact.exists_isMaxOn [ClosedIciTopology α]
 {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β -> α} (hf : Continuou
sOn f s) : exi…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `isCompact_sphere`：isCompact_sphere {α : Type*} [PseudoMetricSpace α] [Pr
operSpace α] (x : α) (r : Real) : IsCompact (sphere x r)
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Complex.norm_cderiv_le`：norm_cderiv_le (hr : 0 < r) (hf : forall w in sp
here z r, ‖f w‖ <= M) : ‖cderiv r f z‖ <= M / r
· 使用引理 `div_lt_div_iff_of_pos_right`：div_lt_div_iff_of_pos_right (hc : 0 < c) : 
a / c < b / c ↔ a < b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
-/
theorem norm_cderiv_lt (hr : 0 < r) (hfM : ∀ w ∈ sphere z r, ‖f w‖ < M)
    (hf : ContinuousOn f (sphere z r)) : ‖cderiv r f z‖ < M / r := by
  obtain ⟨L, hL1, hL2⟩ : ∃ L < M, ∀ w ∈ sphere z r, ‖f w‖ ≤ L := by
    have e1 : (sphere z r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
    have e2 : ContinuousOn (fun w => ‖f w‖) (sphere z r) := continuous_norm.comp_continuousOn hf
    obtain ⟨x, hx, hx'⟩ := (isCompact_sphere z r).exists_isMaxOn e1 e2
    exact ⟨‖f x‖, hfM x hx, hx'⟩
  exact (norm_cderiv_le hr hL2).trans_lt ((div_lt_div_iff_of_pos_right hr).mpr hL1)
/-
**Complex.norm_cderiv_sub_lt** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_cderiv_sub_lt (hr : 0 < r) (hfg : forall w in sphere z r, ‖f w - g w‖
 < M) (hf : ContinuousOn f (sphere z r)) (hg : ContinuousOn g (sphere z r)) : ‖c
deriv r f z - cderiv r g z‖ < M / r
参数：hr : 0 < r；hfg : forall w in sphere z r, ‖f w - g w‖ < M；hf : ContinuousOn f 
(sphere z r)；hg : ContinuousOn g (sphere z r)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.norm_cderiv_lt`：norm_cderiv_lt (hr : 0 < r) (hfM : forall w in s
phere z r, ‖f w‖ < M) (hf : ContinuousOn f (sphere z r)) : ‖cderiv r f z‖ < M / 
r
· 使用定理 `ContinuousOn.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : 
X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Complex.cderiv_sub`：cderiv_sub (hr : 0 < r) (hf : ContinuousOn f (sphere
 z r)) (hg : ContinuousOn g (sphere z r)) : cderiv r (f - g) z = cderiv r f z - 
cderiv r…
-/
theorem norm_cderiv_sub_lt (hr : 0 < r) (hfg : ∀ w ∈ sphere z r, ‖f w - g w‖ < M)
    (hf : ContinuousOn f (sphere z r)) (hg : ContinuousOn g (sphere z r)) :
    ‖cderiv r f z - cderiv r g z‖ < M / r :=
  cderiv_sub hr hf hg ▸ norm_cderiv_lt hr hfg (hf.sub hg)
/-
**Complex._root_.TendstoUniformlyOn.cderiv** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.TendstoUniformlyOn.cderiv (hF : TendstoUniformlyOn F f φ (cthickening δ K))
    (hδ : 0 < δ) (hFn : ∀ᶠ n in φ, ContinuousOn (F n) (cthickening δ K)) :
    TendstoUniformlyOn (cderiv δ ∘ F) (cderiv δ f) φ K := by
  rcases φ.eq_or_neBot with rfl | hne
  · simp only [TendstoUniformlyOn, eventually_bot, imp_true_iff]
  have e1 : ContinuousOn f (cthickening δ K) := TendstoUniformlyOn.continuousOn hF hFn.frequently
  rw [tendstoUniformlyOn_iff] at hF ⊢
  rintro ε hε
  filter_upwards [hF (ε * δ) (mul_pos hε hδ), hFn] with n h h' z hz
  simp_rw [dist_eq_norm] at h ⊢
  have e2 : ∀ w ∈ sphere z δ, ‖f w - F n w‖ < ε * δ := fun w hw1 =>
    h w (closedBall_subset_cthickening hz δ (sphere_subset_closedBall hw1))
  have e3 := sphere_subset_closedBall.trans (closedBall_subset_cthickening hz δ)
  have hf : ContinuousOn f (sphere z δ) :=
    e1.mono (sphere_subset_closedBall.trans (closedBall_subset_cthickening hz δ))
  simpa only [mul_div_cancel_right₀ _ hδ.ne.symm] using! norm_cderiv_sub_lt hδ e2 hf (h'.mono e3)

end Cderiv

variable [CompleteSpace E]

section Weierstrass

/-
**Complex.tendstoUniformlyOn_deriv_of_cthickening_subset** 是 Mathlib 中的一个定理，位于命名
空间 `Complex`。
形式化陈述：tendstoUniformlyOn_deriv_of_cthickening_subset (hf : TendstoLocallyUniform
lyOn F f φ U) (hF : forallᶠ n in φ, DifferentiableOn Complex (F n) U) {δ : Real}
 (hδ : 0 < δ) (hK : IsCompact K) (hU : IsOpen U) (hKU : cthickening δ K subseteq
 U) : TendstoUniformlyOn (deriv ∘ F) (cderiv δ f) φ K
参数：hf : TendstoLocallyUniformlyOn F f φ U；hF : forallᶠ n in φ, DifferentiableOn 
Complex (F n) U；hδ : 0 < δ；hK : IsCompact K；hU : IsOpen U；hKU : cthickening δ K 
subseteq U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `DifferentiableOn.continuousOn`：DifferentiableOn.continuousOn (h : Differ
entiableOn 𝕜 f s) : ContinuousOn f s
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
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
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsCompact.cthickening`：∀ {α : Type u_2} [inst : PseudoMetricSpace α] [Pr
operSpace α] {s : Set α},   IsCompact s → ∀ {r : ℝ}, IsCompact (Metric.cthickeni
ng r s)
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendstoLocallyUniformlyOn_iff_forall_isCompact`：tendstoLocallyUniformlyO
n_iff_forall_isCompact [LocallyCompactSpace α] (hs : IsOpen s) : TendstoLocallyU
niformlyOn F f p s ↔ forall K, K sub…
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `TendstoUniformlyOn.congr`：TendstoUniformlyOn.congr {F' : ι -> α -> β} (h
f : TendstoUniformlyOn F f p s) (hff' : forallᶠ n in p, Set.EqOn (F n) (F' n) s)
 : TendstoUnif…
· 使用定理 `TendstoUniformlyOn.cderiv`：∀ {E : Type u_1} {ι : Type u_2} [inst : Norme
dAddCommGroup E] [inst_1 : NormedSpace ℂ E] {K : Set ℂ} {δ : ℝ}   {φ : Filter ι}
 {F : ι → ℂ → E…
· 使用定理 `Complex.cderiv_eq_deriv`：cderiv_eq_deriv [CompleteSpace E] (hU : IsOpen 
U) (hf : DifferentiableOn Complex f U) (hr : 0 < r) (hzr : closedBall z r subset
eq U) : cderi…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Metric.closedBall_subset_cthickening`：closedBall_subset_cthickening {α :
 Type*} [PseudoMetricSpace α] {x : α} {E : Set α} (hx : x in E) (δ : Real) : clo
sedBall x δ subseteq cthic…
-/
theorem tendstoUniformlyOn_deriv_of_cthickening_subset (hf : TendstoLocallyUniformlyOn F f φ U)
    (hF : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U) {δ : ℝ} (hδ : 0 < δ) (hK : IsCompact K)
    (hU : IsOpen U) (hKU : cthickening δ K ⊆ U) :
    TendstoUniformlyOn (deriv ∘ F) (cderiv δ f) φ K := by
  have h1 : ∀ᶠ n in φ, ContinuousOn (F n) (cthickening δ K) := by
    filter_upwards [hF] with n h using h.continuousOn.mono hKU
  have h2 : IsCompact (cthickening δ K) := hK.cthickening
  have h3 : TendstoUniformlyOn F f φ (cthickening δ K) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hf (cthickening δ K) hKU h2
  apply (h3.cderiv hδ h1).congr
  filter_upwards [hF] with n h z hz
  exact cderiv_eq_deriv hU h hδ ((closedBall_subset_cthickening hz δ).trans hKU)
/-
**Complex.exists_cthickening_tendstoUniformlyOn** 是 Mathlib 中的一个定理，位于命名空间 `Compl
ex`。
形式化陈述：exists_cthickening_tendstoUniformlyOn (hf : TendstoLocallyUniformlyOn F f 
φ U) (hF : forallᶠ n in φ, DifferentiableOn Complex (F n) U) (hK : IsCompact K) 
(hU : IsOpen U) (hKU : K subseteq U) : exists δ > 0, cthickening δ K subseteq U 
∧ TendstoUniformlyOn (deriv ∘ F) (cderiv δ f) φ K
参数：hf : TendstoLocallyUniformlyOn F f φ U；hF : forallᶠ n in φ, DifferentiableOn 
Complex (F n) U；hK : IsCompact K；hU : IsOpen U；hKU : K subseteq U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.exists_cthickening_subset_open`：∀ {α : Type u} [inst : PseudoE
MetricSpace α] {s t : Set α},   IsCompact s → IsOpen t → s ⊆ t → ∃ δ, 0 < δ ∧ Me
tric.cthickening δ s ⊆ t
· 使用定理 `Complex.tendstoUniformlyOn_deriv_of_cthickening_subset`：tendstoUniformly
On_deriv_of_cthickening_subset (hf : TendstoLocallyUniformlyOn F f φ U) (hF : fo
rallᶠ n in φ, DifferentiableOn Complex (F n)…
-/
theorem exists_cthickening_tendstoUniformlyOn (hf : TendstoLocallyUniformlyOn F f φ U)
    (hF : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ δ > 0, cthickening δ K ⊆ U ∧ TendstoUniformlyOn (deriv ∘ F) (cderiv δ f) φ K := by
  obtain ⟨δ, hδ, hKδ⟩ := hK.exists_cthickening_subset_open hU hKU
  exact ⟨δ, hδ, hKδ, tendstoUniformlyOn_deriv_of_cthickening_subset hf hF hδ hK hU hKδ⟩

/-- A locally uniform limit of holomorphic functions on an open domain of the complex plane is
holomorphic (the derivatives converge locally uniformly to that of the limit, which is proved
as `TendstoLocallyUniformlyOn.deriv`). -/
/-
**Complex._root_.TendstoLocallyUniformlyOn.differentiableOn** 是 Mathlib 中的一个定理，位
于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A locally uniform limit of holomorphic functions on an open domain of the comple
x plane is
holomorphic (the derivatives converge locally uniformly to that of the limit, wh
ich is proved
as `TendstoLocallyUniformlyOn.deriv`).
-/
theorem _root_.TendstoLocallyUniformlyOn.differentiableOn [φ.NeBot]
    (hf : TendstoLocallyUniformlyOn F f φ U) (hF : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U)
    (hU : IsOpen U) : DifferentiableOn ℂ f U := by
  rintro x hx
  obtain ⟨K, ⟨hKx, hK⟩, hKU⟩ := (compact_basis_nhds x).mem_iff.mp (hU.mem_nhds hx)
  obtain ⟨δ, _, _, h1⟩ := exists_cthickening_tendstoUniformlyOn hf hF hK hU hKU
  have h2 : interior K ⊆ U := interior_subset.trans hKU
  have h3 : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) (interior K) := by
    filter_upwards [hF] with n h using h.mono h2
  have h4 : TendstoLocallyUniformlyOn F f φ (interior K) := hf.mono h2
  have h5 : TendstoLocallyUniformlyOn (deriv ∘ F) (cderiv δ f) φ (interior K) :=
    h1.tendstoLocallyUniformlyOn.mono interior_subset
  have h6 : ∀ x ∈ interior K, HasDerivAt f (cderiv δ f x) x := fun x h =>
    hasDerivAt_of_tendsto_locally_uniformly_on' isOpen_interior h5 h3 (fun _ => h4.tendsto_at) h
  have h7 : DifferentiableOn ℂ f (interior K) := fun x hx =>
    (h6 x hx).differentiableAt.differentiableWithinAt
  exact (h7.differentiableAt (interior_mem_nhds.mpr hKx)).differentiableWithinAt
/-
**Complex._root_.TendstoLocallyUniformlyOn.deriv** 是 Mathlib 中的一个定理，位于命名空间 `Comp
lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.TendstoLocallyUniformlyOn.deriv (hf : TendstoLocallyUniformlyOn F f φ U)
    (hF : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U) (hU : IsOpen U) :
    TendstoLocallyUniformlyOn (deriv ∘ F) (deriv f) φ U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  rcases φ.eq_or_neBot with rfl | hne
  · simp only [TendstoUniformlyOn, eventually_bot, imp_true_iff]
  rintro K hKU hK
  obtain ⟨δ, hδ, hK4, h⟩ := exists_cthickening_tendstoUniformlyOn hf hF hK hU hKU
  refine h.congr_right fun z hz => cderiv_eq_deriv hU (hf.differentiableOn hF hU) hδ ?_
  exact (closedBall_subset_cthickening hz δ).trans hK4

end Weierstrass

section Tsums

/-- If the terms in the sum `∑' (i : ι), F i` are uniformly bounded on `U` by a
summable function, and each term in the sum is differentiable on `U`, then so is the sum. -/
/-
**Complex.differentiableOn_tsum_of_summable_norm** 是 Mathlib 中的一个定理，位于命名空间 `Comp
lex`。
形式化陈述：differentiableOn_tsum_of_summable_norm {u : ι -> Real} (hu : Summable u) (
hf : forall i : ι, DifferentiableOn Complex (F i) U) (hU : IsOpen U) (hF_le : fo
rall (i : ι) (w : Complex), w in U -> ‖F i w‖ <= u i) : DifferentiableOn Complex
 (fun w : Complex => ∑' i : ι, F i w) U
参数：hu : Summable u；hf : forall i : ι, DifferentiableOn Complex (F i) U；hU : IsOp
en U；hF_le : forall (i : ι) (w : Complex), w in U -> ‖F i w‖ <= u i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoUniformlyOn.tendstoLocallyUniformlyOn`：∀ {α : Type u_1} {β : Type
 u_2} {ι : Type u_4} [inst : TopologicalSpace α] [inst_1 : UniformSpace β] {F : 
ι → α → β}   {f : α → β} {s : Set …
· 使用定理 `tendstoUniformlyOn_tsum`：tendstoUniformlyOn_tsum {f : α -> β -> F} (hu :
 Summable u) {s : Set β} (hfu : forall n x, x in s -> ‖f n x‖ <= u n) : TendstoU
niformlyOn (f…
· 使用定理 `TendstoLocallyUniformlyOn.differentiableOn`：∀ {E : Type u_1} {ι : Type u
_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] {U : Set ℂ} {φ : Fi
lter ι}   {F : ι → ℂ → E} {f : ℂ…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `DifferentiableOn.fun_sum`：DifferentiableOn.fun_sum (h : forall i in u, D
ifferentiableOn 𝕜 (A i) s) : DifferentiableOn 𝕜 (fun y => ∑ i in u, A i y) s

--- 原说明 ---
If the terms in the sum `∑' (i : ι), F i` are uniformly bounded on `U` by a
summable function, and each term in the sum is differentiable on `U`, then so is
 the sum.
-/
theorem differentiableOn_tsum_of_summable_norm {u : ι → ℝ} (hu : Summable u)
    (hf : ∀ i : ι, DifferentiableOn ℂ (F i) U) (hU : IsOpen U)
    (hF_le : ∀ (i : ι) (w : ℂ), w ∈ U → ‖F i w‖ ≤ u i) :
    DifferentiableOn ℂ (fun w : ℂ => ∑' i : ι, F i w) U := by
  have hc := (tendstoUniformlyOn_tsum hu hF_le).tendstoLocallyUniformlyOn
  refine hc.differentiableOn (Eventually.of_forall fun s => ?_) hU
  exact DifferentiableOn.fun_sum fun i _ => hf i

/-- If the terms in the sum `∑' (i : ι), F i` are uniformly bounded on `U` by a
summable function, then the sum of `deriv F i` at a point in `U` is the derivative of the
sum. -/
/-
**Complex.hasSum_deriv_of_summable_norm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：hasSum_deriv_of_summable_norm {u : ι -> Real} (hu : Summable u) (hf : fora
ll i : ι, DifferentiableOn Complex (F i) U) (hU : IsOpen U) (hF_le : forall (i :
 ι) (w : Complex), w in U -> ‖F i w‖ <= u i) (hz : z in U) : HasSum (fun i : ι =
> deriv (F i) z) (deriv (fun w : Complex => ∑' i : ι, F i w) z)
参数：hu : Summable u；hf : forall i : ι, DifferentiableOn Complex (F i) U；hU : IsOp
en U；hF_le : forall (i : ι) (w : Complex), w in U -> ‖F i w‖ <= u i；hz : z in U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasSum.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [i
nst_1 : TopologicalSpace α] (f : β → α) (a : α)   (L : SummationFilter β), HasSu
m…
· 使用定理 `TendstoUniformlyOn.tendstoLocallyUniformlyOn`：∀ {α : Type u_1} {β : Type
 u_2} {ι : Type u_4} [inst : TopologicalSpace α] [inst_1 : UniformSpace β] {F : 
ι → α → β}   {f : α → β} {s : Set …
· 使用定理 `tendstoUniformlyOn_tsum`：tendstoUniformlyOn_tsum {f : α -> β -> F} (hu :
 Summable u) {s : Set β} (hfu : forall n x, x in s -> ‖f n x‖ <= u n) : TendstoU
niformlyOn (f…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `deriv_fun_sum`：deriv_fun_sum (h : forall i in u, DifferentiableAt 𝕜 (A i
) x) : deriv (fun y => ∑ i in u, A i y) x = ∑ i in u, deriv (A i) x
· 使用定理 `DifferentiableOn.differentiableAt`：DifferentiableOn.differentiableAt (h 
: DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x) : DifferentiableAt 𝕜 f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `TendstoLocallyUniformlyOn.tendsto_at`：TendstoLocallyUniformlyOn.tendsto_
at (hf : TendstoLocallyUniformlyOn F f p s) {a : α} (ha : a in s) : Tendsto (fun
 i => F i a) p (𝓝 (f a))
· 使用定理 `TendstoLocallyUniformlyOn.deriv`：∀ {E : Type u_1} {ι : Type u_2} [inst :
 NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] {U : Set ℂ} {φ : Filter ι}   {
F : ι → ℂ → E} {f : ℂ…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `DifferentiableOn.fun_sum`：DifferentiableOn.fun_sum (h : forall i in u, D
ifferentiableOn 𝕜 (A i) s) : DifferentiableOn 𝕜 (fun y => ∑ i in u, A i y) s

--- 原说明 ---
If the terms in the sum `∑' (i : ι), F i` are uniformly bounded on `U` by a
summable function, then the sum of `deriv F i` at a point in `U` is the derivati
ve of the
sum.
-/
theorem hasSum_deriv_of_summable_norm {u : ι → ℝ} (hu : Summable u)
    (hf : ∀ i : ι, DifferentiableOn ℂ (F i) U) (hU : IsOpen U)
    (hF_le : ∀ (i : ι) (w : ℂ), w ∈ U → ‖F i w‖ ≤ u i) (hz : z ∈ U) :
    HasSum (fun i : ι => deriv (F i) z) (deriv (fun w : ℂ => ∑' i : ι, F i w) z) := by
  rw [HasSum]
  have hc := (tendstoUniformlyOn_tsum hu hF_le).tendstoLocallyUniformlyOn
  convert!
    (hc.deriv (Eventually.of_forall fun s => DifferentiableOn.fun_sum fun i _ => hf i)
          hU).tendsto_at
      hz using 1
  ext1 s
  exact (deriv_fun_sum fun i _ => (hf i).differentiableAt (hU.mem_nhds hz)).symm

end Tsums

section LogDeriv

/-- The logarithmic derivative of a sequence of functions converging locally uniformly to a
function is the logarithmic derivative of the limit function. -/
/-
**Complex.logDeriv_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：logDeriv_tendsto {ι : Type*} {p : Filter ι} {f : ι -> Complex -> Complex} 
{g : Complex -> Complex} {s : Set Complex} (hs : IsOpen s) {x : Complex} (hx : x
 in s) (hF : TendstoLocallyUniformlyOn f g p s) (hf : forallᶠ n in p, Differenti
ableOn Complex (f n) s) (hg : g x != 0) : Tendsto (fun n => logDeriv (f n) x) p 
(𝓝 (logDeriv g x))
参数：hs : IsOpen s；hx : x in s；hF : TendstoLocallyUniformlyOn f g p s；hf : forallᶠ
 n in p, DifferentiableOn Complex (f n) s；hg : g x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.div`：Filter.Tendsto.div {l : Filter α} {a b : G₀} (hf : T
endsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) (hy : b != 0) : Tendsto (f / g) l (𝓝 
(a / b))
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `TendstoLocallyUniformlyOn.tendsto_at`：TendstoLocallyUniformlyOn.tendsto_
at (hf : TendstoLocallyUniformlyOn F f p s) {a : α} (ha : a in s) : Tendsto (fun
 i => F i a) p (𝓝 (f a))
· 使用定理 `TendstoLocallyUniformlyOn.deriv`：∀ {E : Type u_1} {ι : Type u_2} [inst :
 NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] {U : Set ℂ} {φ : Filter ι}   {
F : ι → ℂ → E} {f : ℂ…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ

--- 原说明 ---
The logarithmic derivative of a sequence of functions converging locally uniform
ly to a
function is the logarithmic derivative of the limit function.
-/
theorem logDeriv_tendsto {ι : Type*} {p : Filter ι} {f : ι → ℂ → ℂ} {g : ℂ → ℂ}
    {s : Set ℂ} (hs : IsOpen s) {x : ℂ} (hx : x ∈ s) (hF : TendstoLocallyUniformlyOn f g p s)
    (hf : ∀ᶠ n in p, DifferentiableOn ℂ (f n) s) (hg : g x ≠ 0) :
    Tendsto (fun n ↦ logDeriv (f n) x) p (𝓝 (logDeriv g x)) :=
  ((hF.deriv hf hs).tendsto_at hx).div (hF.tendsto_at hx) hg

end LogDeriv

end Complex

