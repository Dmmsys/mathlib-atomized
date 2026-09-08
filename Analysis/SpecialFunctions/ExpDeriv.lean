/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Complex and real exponential

In this file we prove that `Complex.exp` and `Real.exp` are analytic functions.

## Tags

exp, derivative
-/

public section

assert_not_exists IsConformalMap Conformal

noncomputable section

open Filter Asymptotics Set Function
open scoped Topology

/-! ## `Complex.exp` -/

section

open Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f g : E → ℂ} {z : ℂ} {x : E} {s : Set E}

/-- The function `Complex.exp` is complex analytic. -/
/-
**analyticOnNhd_cexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticOnNhd_cexp : AnalyticOnNhd Complex exp univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.exp_eq_exp_ℂ`：Complex.exp = NormedSpace.exp
· 使用定理 `NormedSpace.exp_analytic`：exp_analytic (x : 𝔸) : AnalyticAt 𝕂 exp x
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ

--- 原说明 ---
The function `Complex.exp` is complex analytic.
-/
theorem analyticOnNhd_cexp : AnalyticOnNhd ℂ exp univ := by
  rw [Complex.exp_eq_exp_ℂ]
  exact fun x _ ↦ NormedSpace.exp_analytic x

/-- The function `Complex.exp` is complex analytic. -/
/-
**analyticOn_cexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticOn_cexp : AnalyticOn Complex exp univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticOnNhd.analyticOn`：AnalyticOnNhd.analyticOn (hf : AnalyticOnNhd 𝕜
 f s) : AnalyticOn 𝕜 f s
· 使用定理 `analyticOnNhd_cexp`：analyticOnNhd_cexp : AnalyticOnNhd Complex exp univ

--- 原说明 ---
The function `Complex.exp` is complex analytic.
-/
theorem analyticOn_cexp : AnalyticOn ℂ exp univ := analyticOnNhd_cexp.analyticOn

/-- The function `Complex.exp` is complex analytic. -/
@[fun_prop]
/-
**analyticAt_cexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticAt_cexp : AnalyticAt Complex exp z
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `analyticOnNhd_cexp`：analyticOnNhd_cexp : AnalyticOnNhd Complex exp univ
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
The function `Complex.exp` is complex analytic.
-/
theorem analyticAt_cexp : AnalyticAt ℂ exp z :=
  analyticOnNhd_cexp z (mem_univ _)

/-- The function `Complex.exp` is complex analytic. -/
/-
**analyticWithinAt_cexp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticWithinAt_cexp {s : Set Complex} {x : Complex} : AnalyticWithinAt C
omplex Complex.exp s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticAt.analyticWithinAt`：AnalyticAt.analyticWithinAt (hf : AnalyticA
t 𝕜 f x) : AnalyticWithinAt 𝕜 f s x
· 使用定理 `analyticAt_cexp`：analyticAt_cexp : AnalyticAt Complex exp z

--- 原说明 ---
The function `Complex.exp` is complex analytic.
-/
lemma analyticWithinAt_cexp {s : Set ℂ} {x : ℂ} :
    AnalyticWithinAt ℂ Complex.exp s x := by
  exact analyticAt_cexp.analyticWithinAt

/-- `exp ∘ f` is analytic -/
@[fun_prop]
/-
**AnalyticAt.cexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.cexp (fa : AnalyticAt Complex f x) : AnalyticAt Complex (exp ∘ 
f) x
参数：fa : AnalyticAt Complex f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.comp`：AnalyticAt.comp {g : F -> G} {f : E -> F} {x : E} (hg :
 AnalyticAt 𝕜 g (f x)) (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (g ∘ f) x
· 使用定理 `analyticAt_cexp`：analyticAt_cexp : AnalyticAt Complex exp z

--- 原说明 ---
`exp ∘ f` is analytic
-/
theorem AnalyticAt.cexp (fa : AnalyticAt ℂ f x) : AnalyticAt ℂ (exp ∘ f) x :=
  analyticAt_cexp.comp fa

/-- `exp ∘ f` is analytic -/
@[fun_prop]
/-
**AnalyticAt.cexp'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.cexp' (fa : AnalyticAt Complex f x) : AnalyticAt Complex (fun z
 => exp (f z)) x
参数：fa : AnalyticAt Complex f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.cexp`：AnalyticAt.cexp (fa : AnalyticAt Complex f x) : Analyti
cAt Complex (exp ∘ f) x

--- 原说明 ---
`exp ∘ f` is analytic
-/
theorem AnalyticAt.cexp' (fa : AnalyticAt ℂ f x) : AnalyticAt ℂ (fun z ↦ exp (f z)) x :=
  fa.cexp
/-
**AnalyticWithinAt.cexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.cexp (fa : AnalyticWithinAt Complex f s x) : AnalyticWith
inAt Complex (fun z => exp (f z)) s x
参数：fa : AnalyticWithinAt Complex f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.comp_analyticWithinAt`：AnalyticAt.comp_analyticWithinAt {g : 
F -> G} {f : E -> F} {x : E} {s : Set E} (hg : AnalyticAt 𝕜 g (f x)) (hf : Analy
ticWithinAt 𝕜 f s x) :…
· 使用定理 `analyticAt_cexp`：analyticAt_cexp : AnalyticAt Complex exp z
-/
theorem AnalyticWithinAt.cexp (fa : AnalyticWithinAt ℂ f s x) :
    AnalyticWithinAt ℂ (fun z ↦ exp (f z)) s x :=
  analyticAt_cexp.comp_analyticWithinAt fa

/-- `exp ∘ f` is analytic -/
/-
**AnalyticOnNhd.cexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.cexp (fs : AnalyticOnNhd Complex f s) : AnalyticOnNhd Comple
x (fun z => exp (f z)) s
参数：fs : AnalyticOnNhd Complex f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.comp`：AnalyticAt.comp {g : F -> G} {f : E -> F} {x : E} (hg :
 AnalyticAt 𝕜 g (f x)) (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (g ∘ f) x
· 使用定理 `analyticAt_cexp`：analyticAt_cexp : AnalyticAt Complex exp z

--- 原说明 ---
`exp ∘ f` is analytic
-/
theorem AnalyticOnNhd.cexp (fs : AnalyticOnNhd ℂ f s) : AnalyticOnNhd ℂ (fun z ↦ exp (f z)) s :=
  fun z n ↦ analyticAt_cexp.comp (fs z n)
/-
**AnalyticOn.cexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOn.cexp (fs : AnalyticOn Complex f s) : AnalyticOn Complex (fun z 
=> exp (f z)) s
参数：fs : AnalyticOn Complex f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticOnNhd.comp_analyticOn`：AnalyticOnNhd.comp_analyticOn {f : F -> G
} {g : E -> F} {s : Set F} {t : Set E} (hf : AnalyticOnNhd 𝕜 f s) (hg : Analytic
On 𝕜 g t) (h : Set.…
· 使用定理 `analyticOnNhd_cexp`：analyticOnNhd_cexp : AnalyticOnNhd Complex exp univ
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
theorem AnalyticOn.cexp (fs : AnalyticOn ℂ f s) : AnalyticOn ℂ (fun z ↦ exp (f z)) s :=
  analyticOnNhd_cexp.comp_analyticOn fs (mapsTo_univ _ _)

end

namespace Complex

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]

/-- The complex exponential is everywhere differentiable, with the derivative `exp x`. -/
/-
**Complex.hasDerivAt_exp** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：hasDerivAt_exp (x : Complex) : HasDerivAt exp (exp x) x
参数：x : Complex。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `hasDerivAt_iff_isLittleO_nhds_zero`：hasDerivAt_iff_isLittleO_nhds_zero :
 HasDerivAt f f' x ↔ (fun h => f (x + h) - f x - h • f') =o[𝓝 0] fun h => h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Asymptotics.IsBigO.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} {G :
 Type u_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : Seminor
medAddCommGroup F'] {l :…
· 使用定理 `Asymptotics.IsBigO.of_bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}   (
c : ℝ), (∀ᶠ (x : …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Complex.exp_bound_sq`：exp_bound_sq (x z : Complex) (hz : ‖z‖ <= 1) : ‖ex
p (x + z) - exp x - z • exp x‖ <= ‖exp x‖ * ‖z‖ ^ 2
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Asymptotics.isLittleO_pow_id`：isLittleO_pow_id {n : Nat} (h : 1 < n) : (
fun x : 𝕜 => x ^ n) =o[𝓝 0] fun x => x

--- 原说明 ---
The complex exponential is everywhere differentiable, with the derivative `exp x
`.
-/
theorem hasDerivAt_exp (x : ℂ) : HasDerivAt exp (exp x) x := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have : (1 : ℕ) < 2 := by simp
  refine (IsBigO.of_bound ‖exp x‖ ?_).trans_isLittleO (isLittleO_pow_id this)
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one]
  simp only [Metric.mem_ball, dist_zero_right, norm_pow]
  exact fun z hz => exp_bound_sq x z hz.le

@[simp]
/-
**Complex.differentiable_exp** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：differentiable_exp : Differentiable 𝕜 exp
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.restrictScalars`：DifferentiableAt.restrictScalars (h : 
DifferentiableAt 𝕜' f x) : DifferentiableAt 𝕜 f x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `Complex.hasDerivAt_exp`：hasDerivAt_exp (x : Complex) : HasDerivAt exp (e
xp x) x
-/
theorem differentiable_exp : Differentiable 𝕜 exp := fun x =>
  (hasDerivAt_exp x).differentiableAt.restrictScalars 𝕜

@[simp]
/-
**Complex.differentiableAt_exp** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：differentiableAt_exp {x : Complex} : DifferentiableAt 𝕜 exp x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.differentiable_exp`：differentiable_exp : Differentiable 𝕜 exp
-/
theorem differentiableAt_exp {x : ℂ} : DifferentiableAt 𝕜 exp x :=
  differentiable_exp x

@[simp]
/-
**Complex.deriv_exp** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：deriv_exp : deriv exp = exp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `Complex.hasDerivAt_exp`：hasDerivAt_exp (x : Complex) : HasDerivAt exp (e
xp x) x
-/
theorem deriv_exp : deriv exp = exp :=
  funext fun x => (hasDerivAt_exp x).deriv

@[simp]
/-
**Complex.iter_deriv_exp** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (n : ℕ), deriv^[n] Complex.exp = Complex.exp
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iter_deriv_exp : ∀ n : ℕ, deriv^[n] exp = exp
  | 0 => rfl
  | n + 1 => by rw [iterate_succ_apply, deriv_exp, iter_deriv_exp n]

@[fun_prop]
/-
**Complex.contDiff_exp** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：contDiff_exp {n : WithTop Nat∞} : ContDiff 𝕜 n exp
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOnNhd.contDiff`：AnalyticOnNhd.contDiff (hf : AnalyticOnNhd 𝕜 f u
niv) : ContDiff 𝕜 n f
· 使用引理 `AnalyticOnNhd.restrictScalars`：AnalyticOnNhd.restrictScalars (hf : Analy
ticOnNhd 𝕜' f s) : AnalyticOnNhd 𝕜 f s
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `analyticOnNhd_cexp`：analyticOnNhd_cexp : AnalyticOnNhd Complex exp univ
-/
theorem contDiff_exp {n : WithTop ℕ∞} : ContDiff 𝕜 n exp :=
  analyticOnNhd_cexp.restrictScalars.contDiff
/-
**Complex.hasStrictDerivAt_exp** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：hasStrictDerivAt_exp (x : Complex) : HasStrictDerivAt exp (exp x) x
参数：x : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.hasStrictDerivAt'`：ContDiffAt.hasStrictDerivAt' {f : 𝕂 -> F'}
 {f' : F'} {x : 𝕂} (hf : ContDiffAt 𝕂 n f x) (hf' : HasDerivAt f f' x) (hn : n !
= 0) : HasStrictDe…
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Complex.contDiff_exp`：contDiff_exp {n : WithTop Nat∞} : ContDiff 𝕜 n exp
· 使用定理 `Complex.hasDerivAt_exp`：hasDerivAt_exp (x : Complex) : HasDerivAt exp (e
xp x) x
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem hasStrictDerivAt_exp (x : ℂ) : HasStrictDerivAt exp (exp x) x :=
  contDiff_exp.contDiffAt.hasStrictDerivAt' (hasDerivAt_exp x) one_ne_zero
/-
**Complex.hasStrictFDerivAt_exp_real** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：hasStrictFDerivAt_exp_real (x : Complex) : HasStrictFDerivAt exp (exp x • 
(1 : Complex ->L[Real] Complex)) x
参数：x : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.complexToReal_fderiv`：HasStrictDerivAt.complexToReal_fd
eriv {f : Complex -> Complex} {f' x : Complex} (h : HasStrictDerivAt f f' x) : H
asStrictFDerivAt f (f' • (1…
· 使用定理 `Complex.hasStrictDerivAt_exp`：hasStrictDerivAt_exp (x : Complex) : HasSt
rictDerivAt exp (exp x) x
-/
theorem hasStrictFDerivAt_exp_real (x : ℂ) : HasStrictFDerivAt exp (exp x • (1 : ℂ →L[ℝ] ℂ)) x :=
  (hasStrictDerivAt_exp x).complexToReal_fderiv

end Complex

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] {f : 𝕜 → ℂ} {f' : ℂ} {x : 𝕜}
  {s : Set 𝕜}

/-
**HasStrictDerivAt.cexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.cexp (hf : HasStrictDerivAt f f' x) : HasStrictDerivAt (f
un x => Complex.exp (f x)) (Complex.exp (f x) * f') x
参数：hf : HasStrictDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasStrictDerivAt.comp`：HasStrictDerivAt.comp (hh₂ : HasStrictDerivAt h₂ 
h₂' (h x)) (hh : HasStrictDerivAt h h' x) : HasStrictDerivAt (h₂ ∘ h) (h₂' * h')
 x
· 使用定理 `Complex.hasStrictDerivAt_exp`：hasStrictDerivAt_exp (x : Complex) : HasSt
rictDerivAt exp (exp x) x
-/
theorem HasStrictDerivAt.cexp (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.exp (f x)) (Complex.exp (f x) * f') x :=
  (Complex.hasStrictDerivAt_exp (f x)).comp x hf
/-
**HasDerivAt.cexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.cexp (hf : HasDerivAt f f' x) : HasDerivAt (fun x => Complex.ex
p (f x)) (Complex.exp (f x) * f') x
参数：hf : HasDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.comp`：HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : H
asDerivAt h h' x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x
· 使用定理 `Complex.hasDerivAt_exp`：hasDerivAt_exp (x : Complex) : HasDerivAt exp (e
xp x) x
-/
theorem HasDerivAt.cexp (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Complex.exp (f x)) (Complex.exp (f x) * f') x :=
  (Complex.hasDerivAt_exp (f x)).comp x hf
/-
**HasDerivWithinAt.cexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.cexp (hf : HasDerivWithinAt f f' s x) : HasDerivWithinAt 
(fun x => Complex.exp (f x)) (Complex.exp (f x) * f') s x
参数：hf : HasDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.comp_hasDerivWithinAt`：HasDerivAt.comp_hasDerivWithinAt (hh₂ 
: HasDerivAt h₂ h₂' (h x)) (hh : HasDerivWithinAt h h' s x) : HasDerivWithinAt (
h₂ ∘ h) (h₂' * h') s x
· 使用定理 `Complex.hasDerivAt_exp`：hasDerivAt_exp (x : Complex) : HasDerivAt exp (e
xp x) x
-/
theorem HasDerivWithinAt.cexp (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.exp (f x)) (Complex.exp (f x) * f') s x :=
  (Complex.hasDerivAt_exp (f x)).comp_hasDerivWithinAt x hf
/-
**derivWithin_cexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_cexp (hf : DifferentiableWithinAt 𝕜 f s x) (hxs : UniqueDiffWi
thinAt 𝕜 s x) : derivWithin (fun x => Complex.exp (f x)) s x = Complex.exp (f x)
 * derivWithin f s x
参数：hf : DifferentiableWithinAt 𝕜 f s x；hxs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.cexp`：HasDerivWithinAt.cexp (hf : HasDerivWithinAt f f'
 s x) : HasDerivWithinAt (fun x => Complex.exp (f x)) (Complex.exp (f x) * f') s
 x
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
-/
theorem derivWithin_cexp (hf : DifferentiableWithinAt 𝕜 f s x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => Complex.exp (f x)) s x = Complex.exp (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.cexp.derivWithin hxs

@[simp]
/-
**deriv_cexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_cexp (hc : DifferentiableAt 𝕜 f x) : deriv (fun x => Complex.exp (f 
x)) x = Complex.exp (f x) * deriv f x
参数：hc : DifferentiableAt 𝕜 f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.cexp`：HasDerivAt.cexp (hf : HasDerivAt f f' x) : HasDerivAt (
fun x => Complex.exp (f x)) (Complex.exp (f x) * f') x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_cexp (hc : DifferentiableAt 𝕜 f x) :
    deriv (fun x => Complex.exp (f x)) x = Complex.exp (f x) * deriv f x :=
  hc.hasDerivAt.cexp.deriv

end

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : E → ℂ} {f' : E →L[𝕜] ℂ} {x : E} {s : Set E}

/-
**HasStrictFDerivAt.cexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.cexp (hf : HasStrictFDerivAt f f' x) : HasStrictFDerivAt
 (fun x => Complex.exp (f x)) (Complex.exp (f x) • f') x
参数：hf : HasStrictFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.comp_hasStrictFDerivAt`：HasStrictDerivAt.comp_hasStrict
FDerivAt {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x) (hh : HasStrictDerivAt h₂ h₂' (f x
)) (hf : HasStrictFDerivAt f …
· 使用定理 `Complex.hasStrictDerivAt_exp`：hasStrictDerivAt_exp (x : Complex) : HasSt
rictDerivAt exp (exp x) x
-/
theorem HasStrictFDerivAt.cexp (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Complex.exp (f x)) (Complex.exp (f x) • f') x :=
  (Complex.hasStrictDerivAt_exp (f x)).comp_hasStrictFDerivAt x hf
/-
**HasFDerivWithinAt.cexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.cexp (hf : HasFDerivWithinAt f f' s x) : HasFDerivWithin
At (fun x => Complex.exp (f x)) (Complex.exp (f x) • f') s x
参数：hf : HasFDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivWithinAt`：HasDerivAt.comp_hasFDerivWithinAt {f 
: E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFD
erivWithinAt f f' s x) …
· 使用定理 `Complex.hasDerivAt_exp`：hasDerivAt_exp (x : Complex) : HasDerivAt exp (e
xp x) x
-/
theorem HasFDerivWithinAt.cexp (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Complex.exp (f x)) (Complex.exp (f x) • f') s x :=
  (Complex.hasDerivAt_exp (f x)).comp_hasFDerivWithinAt x hf
/-
**HasFDerivAt.cexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.cexp (hf : HasFDerivAt f f' x) : HasFDerivAt (fun x => Complex
.exp (f x)) (Complex.exp (f x) • f') x
参数：hf : HasFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `hasFDerivWithinAt_univ`：hasFDerivWithinAt_univ : HasFDerivWithinAt f f' 
univ x ↔ HasFDerivAt f f' x
· 使用定理 `HasFDerivWithinAt.cexp`：HasFDerivWithinAt.cexp (hf : HasFDerivWithinAt f
 f' s x) : HasFDerivWithinAt (fun x => Complex.exp (f x)) (Complex.exp (f x) • f
') s x
· 使用定理 `HasFDerivAt.hasFDerivWithinAt`：HasFDerivAt.hasFDerivWithinAt (h : HasFDe
rivAt f f' x) : HasFDerivWithinAt f f' s x
-/
theorem HasFDerivAt.cexp (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Complex.exp (f x)) (Complex.exp (f x) • f') x :=
  hasFDerivWithinAt_univ.1 <| hf.hasFDerivWithinAt.cexp
/-
**DifferentiableWithinAt.cexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.cexp (hf : DifferentiableWithinAt 𝕜 f s x) : Differ
entiableWithinAt 𝕜 (fun x => Complex.exp (f x)) s x
参数：hf : DifferentiableWithinAt 𝕜 f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `HasFDerivWithinAt.cexp`：HasFDerivWithinAt.cexp (hf : HasFDerivWithinAt f
 f' s x) : HasFDerivWithinAt (fun x => Complex.exp (f x)) (Complex.exp (f x) • f
') s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.cexp (hf : DifferentiableWithinAt 𝕜 f s x) :
    DifferentiableWithinAt 𝕜 (fun x => Complex.exp (f x)) s x :=
  hf.hasFDerivWithinAt.cexp.differentiableWithinAt

@[simp, fun_prop]
/-
**DifferentiableAt.cexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.cexp (hc : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (
fun x => Complex.exp (f x)) x
参数：hc : DifferentiableAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `HasFDerivAt.cexp`：HasFDerivAt.cexp (hf : HasFDerivAt f f' x) : HasFDeriv
At (fun x => Complex.exp (f x)) (Complex.exp (f x) • f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.cexp (hc : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (fun x => Complex.exp (f x)) x :=
  hc.hasFDerivAt.cexp.differentiableAt
/-
**DifferentiableOn.cexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.cexp (hc : DifferentiableOn 𝕜 f s) : DifferentiableOn 𝕜 (
fun x => Complex.exp (f x)) s
参数：hc : DifferentiableOn 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.cexp`：DifferentiableWithinAt.cexp (hf : Different
iableWithinAt 𝕜 f s x) : DifferentiableWithinAt 𝕜 (fun x => Complex.exp (f x)) s
 x
-/
theorem DifferentiableOn.cexp (hc : DifferentiableOn 𝕜 f s) :
    DifferentiableOn 𝕜 (fun x => Complex.exp (f x)) s := fun x h => (hc x h).cexp

@[simp, fun_prop]
/-
**Differentiable.cexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.cexp (hc : Differentiable 𝕜 f) : Differentiable 𝕜 fun x => 
Complex.exp (f x)
参数：hc : Differentiable 𝕜 f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.cexp`：DifferentiableAt.cexp (hc : DifferentiableAt 𝕜 f 
x) : DifferentiableAt 𝕜 (fun x => Complex.exp (f x)) x
-/
theorem Differentiable.cexp (hc : Differentiable 𝕜 f) :
    Differentiable 𝕜 fun x => Complex.exp (f x) := fun x => (hc x).cexp

@[fun_prop]
/-
**ContDiff.cexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.cexp {n} (h : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => Complex.exp
 (f x)
参数：h : ContDiff 𝕜 n f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `Complex.contDiff_exp`：contDiff_exp {n : WithTop Nat∞} : ContDiff 𝕜 n exp
-/
theorem ContDiff.cexp {n} (h : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => Complex.exp (f x) :=
  Complex.contDiff_exp.comp h

@[fun_prop]
/-
**ContDiffAt.cexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.cexp {n} (hf : ContDiffAt 𝕜 n f x) : ContDiffAt 𝕜 n (fun x => C
omplex.exp (f x)) x
参数：hf : ContDiffAt 𝕜 n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Complex.contDiff_exp`：contDiff_exp {n : WithTop Nat∞} : ContDiff 𝕜 n exp
-/
theorem ContDiffAt.cexp {n} (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun x => Complex.exp (f x)) x :=
  Complex.contDiff_exp.contDiffAt.comp x hf

@[fun_prop]
/-
**ContDiffOn.cexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.cexp {n} (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 n (fun x => C
omplex.exp (f x)) s
参数：hf : ContDiffOn 𝕜 n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp_contDiffOn`：ContDiff.comp_contDiffOn {s : Set E} {g : F ->
 G} {f : E -> F} (hg : ContDiff 𝕜 n g) (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 
n (g ∘ f) s
· 使用定理 `Complex.contDiff_exp`：contDiff_exp {n : WithTop Nat∞} : ContDiff 𝕜 n exp
-/
theorem ContDiffOn.cexp {n} (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (fun x => Complex.exp (f x)) s :=
  Complex.contDiff_exp.comp_contDiffOn hf

@[fun_prop]
/-
**ContDiffWithinAt.cexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.cexp {n} (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWith
inAt 𝕜 n (fun x => Complex.exp (f x)) s x
参数：hf : ContDiffWithinAt 𝕜 n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp_contDiffWithinAt`：ContDiffAt.comp_contDiffWithinAt (x : 
E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWit
hinAt 𝕜 n (g ∘ f) s x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Complex.contDiff_exp`：contDiff_exp {n : WithTop Nat∞} : ContDiff 𝕜 n exp
-/
theorem ContDiffWithinAt.cexp {n} (hf : ContDiffWithinAt 𝕜 n f s x) :
    ContDiffWithinAt 𝕜 n (fun x => Complex.exp (f x)) s x :=
  Complex.contDiff_exp.contDiffAt.comp_contDiffWithinAt x hf

end

open Complex in
@[simp]
/-
**iteratedDeriv_cexp_const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_cexp_const_mul (n : Nat) (c : Complex) : (iteratedDeriv n fu
n s : Complex => exp (c * s)) = fun s => c ^ n * exp (c * s)
参数：n : Nat；c : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDeriv_comp_const_mul`：iteratedDeriv_comp_const_mul {n : Nat} {f 
: 𝕜 -> 𝕜} (h : ContDiff 𝕜 n f) (c : 𝕜) : iteratedDeriv n (fun x => f (c * x)) = 
fun x => c ^ n * i…
· 使用定理 `Complex.contDiff_exp`：contDiff_exp {n : WithTop Nat∞} : ContDiff 𝕜 n exp
· 使用定理 `iteratedDeriv_eq_iterate`：iteratedDeriv_eq_iterate : iteratedDeriv n f =
 deriv^[n] f
· 使用定理 `Complex.iter_deriv_exp`：∀ (n : ℕ), deriv^[n] Complex.exp = Complex.exp
-/
theorem iteratedDeriv_cexp_const_mul (n : ℕ) (c : ℂ) :
    (iteratedDeriv n fun s : ℂ => exp (c * s)) = fun s => c ^ n * exp (c * s) := by
  rw [iteratedDeriv_comp_const_mul contDiff_exp, iteratedDeriv_eq_iterate, iter_deriv_exp]

/-! ## `Real.exp` -/

section

open Real

variable {x : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {s : Set E}

/-- The function `Real.exp` is real analytic. -/
/-
**analyticOnNhd_rexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticOnNhd_rexp : AnalyticOnNhd Real exp univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.exp_eq_exp_ℝ`：Real.exp = NormedSpace.exp
· 使用定理 `NormedSpace.exp_analytic`：exp_analytic (x : 𝔸) : AnalyticAt 𝕂 exp x
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `NNRat.instContinuousSMulRatReal`：ContinuousSMul ℚ ℝ

--- 原说明 ---
The function `Real.exp` is real analytic.
-/
theorem analyticOnNhd_rexp : AnalyticOnNhd ℝ exp univ := by
  rw [Real.exp_eq_exp_ℝ]
  exact fun x _ ↦ NormedSpace.exp_analytic x

/-- The function `Real.exp` is real analytic. -/
/-
**analyticOn_rexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticOn_rexp : AnalyticOn Real exp univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticOnNhd.analyticOn`：AnalyticOnNhd.analyticOn (hf : AnalyticOnNhd 𝕜
 f s) : AnalyticOn 𝕜 f s
· 使用定理 `analyticOnNhd_rexp`：analyticOnNhd_rexp : AnalyticOnNhd Real exp univ

--- 原说明 ---
The function `Real.exp` is real analytic.
-/
theorem analyticOn_rexp : AnalyticOn ℝ exp univ := analyticOnNhd_rexp.analyticOn

/-- The function `Real.exp` is real analytic. -/
@[fun_prop]
/-
**analyticAt_rexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticAt_rexp : AnalyticAt Real exp x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `analyticOnNhd_rexp`：analyticOnNhd_rexp : AnalyticOnNhd Real exp univ
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
The function `Real.exp` is real analytic.
-/
theorem analyticAt_rexp : AnalyticAt ℝ exp x :=
  analyticOnNhd_rexp x (mem_univ _)

/-- The function `Real.exp` is real analytic. -/
/-
**analyticWithinAt_rexp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticWithinAt_rexp {s : Set Real} : AnalyticWithinAt Real Real.exp s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticAt.analyticWithinAt`：AnalyticAt.analyticWithinAt (hf : AnalyticA
t 𝕜 f x) : AnalyticWithinAt 𝕜 f s x
· 使用定理 `analyticAt_rexp`：analyticAt_rexp : AnalyticAt Real exp x

--- 原说明 ---
The function `Real.exp` is real analytic.
-/
lemma analyticWithinAt_rexp {s : Set ℝ} : AnalyticWithinAt ℝ Real.exp s x :=
  analyticAt_rexp.analyticWithinAt

/-- `exp ∘ f` is analytic -/
@[fun_prop]
/-
**AnalyticAt.rexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.rexp {x : E} (fa : AnalyticAt Real f x) : AnalyticAt Real (exp 
∘ f) x
参数：fa : AnalyticAt Real f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.comp`：AnalyticAt.comp {g : F -> G} {f : E -> F} {x : E} (hg :
 AnalyticAt 𝕜 g (f x)) (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (g ∘ f) x
· 使用定理 `analyticAt_rexp`：analyticAt_rexp : AnalyticAt Real exp x

--- 原说明 ---
`exp ∘ f` is analytic
-/
theorem AnalyticAt.rexp {x : E} (fa : AnalyticAt ℝ f x) : AnalyticAt ℝ (exp ∘ f) x :=
  analyticAt_rexp.comp fa

/-- `exp ∘ f` is analytic -/
@[fun_prop]
/-
**AnalyticAt.rexp'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.rexp' {x : E} (fa : AnalyticAt Real f x) : AnalyticAt Real (fun
 z => exp (f z)) x
参数：fa : AnalyticAt Real f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.rexp`：AnalyticAt.rexp {x : E} (fa : AnalyticAt Real f x) : An
alyticAt Real (exp ∘ f) x

--- 原说明 ---
`exp ∘ f` is analytic
-/
theorem AnalyticAt.rexp' {x : E} (fa : AnalyticAt ℝ f x) : AnalyticAt ℝ (fun z ↦ exp (f z)) x :=
  fa.rexp
/-
**AnalyticWithinAt.rexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.rexp {x : E} (fa : AnalyticWithinAt Real f s x) : Analyti
cWithinAt Real (fun z => exp (f z)) s x
参数：fa : AnalyticWithinAt Real f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.comp_analyticWithinAt`：AnalyticAt.comp_analyticWithinAt {g : 
F -> G} {f : E -> F} {x : E} {s : Set E} (hg : AnalyticAt 𝕜 g (f x)) (hf : Analy
ticWithinAt 𝕜 f s x) :…
· 使用定理 `analyticAt_rexp`：analyticAt_rexp : AnalyticAt Real exp x
-/
theorem AnalyticWithinAt.rexp {x : E} (fa : AnalyticWithinAt ℝ f s x) :
    AnalyticWithinAt ℝ (fun z ↦ exp (f z)) s x :=
  analyticAt_rexp.comp_analyticWithinAt fa

/-- `exp ∘ f` is analytic -/
/-
**AnalyticOnNhd.rexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.rexp {s : Set E} (fs : AnalyticOnNhd Real f s) : AnalyticOnN
hd Real (fun z => exp (f z)) s
参数：fs : AnalyticOnNhd Real f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.comp`：AnalyticAt.comp {g : F -> G} {f : E -> F} {x : E} (hg :
 AnalyticAt 𝕜 g (f x)) (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (g ∘ f) x
· 使用定理 `analyticAt_rexp`：analyticAt_rexp : AnalyticAt Real exp x

--- 原说明 ---
`exp ∘ f` is analytic
-/
theorem AnalyticOnNhd.rexp {s : Set E} (fs : AnalyticOnNhd ℝ f s) :
    AnalyticOnNhd ℝ (fun z ↦ exp (f z)) s :=
  fun z n ↦ analyticAt_rexp.comp (fs z n)
/-
**AnalyticOn.rexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOn.rexp (fs : AnalyticOn Real f s) : AnalyticOn Real (fun z => exp
 (f z)) s
参数：fs : AnalyticOn Real f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticOnNhd.comp_analyticOn`：AnalyticOnNhd.comp_analyticOn {f : F -> G
} {g : E -> F} {s : Set F} {t : Set E} (hf : AnalyticOnNhd 𝕜 f s) (hg : Analytic
On 𝕜 g t) (h : Set.…
· 使用定理 `analyticOnNhd_rexp`：analyticOnNhd_rexp : AnalyticOnNhd Real exp univ
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
theorem AnalyticOn.rexp (fs : AnalyticOn ℝ f s) : AnalyticOn ℝ (fun z ↦ exp (f z)) s :=
  analyticOnNhd_rexp.comp_analyticOn fs (mapsTo_univ _ _)

end

namespace Real

/-
**Real.hasStrictDerivAt_exp** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasStrictDerivAt_exp (x : Real) : HasStrictDerivAt exp (exp x) x
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.real_of_complex`：HasStrictDerivAt.real_of_complex (h : 
HasStrictDerivAt e e' z) : HasStrictDerivAt (fun x : Real => (e x).re) e'.re z
· 使用定理 `Complex.hasStrictDerivAt_exp`：hasStrictDerivAt_exp (x : Complex) : HasSt
rictDerivAt exp (exp x) x
-/
theorem hasStrictDerivAt_exp (x : ℝ) : HasStrictDerivAt exp (exp x) x :=
  (Complex.hasStrictDerivAt_exp x).real_of_complex
/-
**Real.hasDerivAt_exp** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasDerivAt_exp (x : Real) : HasDerivAt exp (exp x) x
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.real_of_complex`：HasDerivAt.real_of_complex (h : HasDerivAt e
 e' z) : HasDerivAt (fun x : Real => (e x).re) e'.re z
· 使用定理 `Complex.hasDerivAt_exp`：hasDerivAt_exp (x : Complex) : HasDerivAt exp (e
xp x) x
-/
theorem hasDerivAt_exp (x : ℝ) : HasDerivAt exp (exp x) x :=
  (Complex.hasDerivAt_exp x).real_of_complex

@[fun_prop]
/-
**Real.contDiff_exp** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：contDiff_exp {n : WithTop Nat∞} : ContDiff Real n exp
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.real_of_complex`：ContDiff.real_of_complex {n : WithTop Nat∞} (h
 : ContDiff Complex n e) : ContDiff Real n fun x : Real => (e x).re
· 使用定理 `Complex.contDiff_exp`：contDiff_exp {n : WithTop Nat∞} : ContDiff 𝕜 n exp
-/
theorem contDiff_exp {n : WithTop ℕ∞} : ContDiff ℝ n exp :=
  Complex.contDiff_exp.real_of_complex

@[simp]
/-
**Real.differentiable_exp** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiable_exp : Differentiable Real exp
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `Real.hasDerivAt_exp`：hasDerivAt_exp (x : Real) : HasDerivAt exp (exp x) 
x
-/
theorem differentiable_exp : Differentiable ℝ exp := fun x => (hasDerivAt_exp x).differentiableAt

@[simp]
/-
**Real.differentiableAt_exp** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiableAt_exp {x : Real} : DifferentiableAt Real exp x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.differentiable_exp`：differentiable_exp : Differentiable Real exp
-/
theorem differentiableAt_exp {x : ℝ} : DifferentiableAt ℝ exp x :=
  differentiable_exp x

@[simp]
/-
**Real.deriv_exp** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：deriv_exp : deriv exp = exp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `Real.hasDerivAt_exp`：hasDerivAt_exp (x : Real) : HasDerivAt exp (exp x) 
x
-/
theorem deriv_exp : deriv exp = exp :=
  funext fun x => (hasDerivAt_exp x).deriv

@[simp]
/-
**Real.iter_deriv_exp** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ (n : ℕ), deriv^[n] Real.exp = Real.exp
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iter_deriv_exp : ∀ n : ℕ, deriv^[n] exp = exp
  | 0 => rfl
  | n + 1 => by rw [iterate_succ_apply, deriv_exp, iter_deriv_exp n]

end Real

section

/-! Register lemmas for the derivatives of the composition of `Real.exp` with a differentiable
function, for standalone use and use with `simp`. -/


variable {f : ℝ → ℝ} {f' x : ℝ} {s : Set ℝ}

/-
**HasStrictDerivAt.exp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.exp (hf : HasStrictDerivAt f f' x) : HasStrictDerivAt (fu
n x => Real.exp (f x)) (Real.exp (f x) * f') x
参数：hf : HasStrictDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasStrictDerivAt.comp`：HasStrictDerivAt.comp (hh₂ : HasStrictDerivAt h₂ 
h₂' (h x)) (hh : HasStrictDerivAt h h' x) : HasStrictDerivAt (h₂ ∘ h) (h₂' * h')
 x
· 使用定理 `Real.hasStrictDerivAt_exp`：hasStrictDerivAt_exp (x : Real) : HasStrictDe
rivAt exp (exp x) x
-/
theorem HasStrictDerivAt.exp (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.exp (f x)) (Real.exp (f x) * f') x :=
  (Real.hasStrictDerivAt_exp (f x)).comp x hf
/-
**HasDerivAt.exp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.exp (hf : HasDerivAt f f' x) : HasDerivAt (fun x => Real.exp (f
 x)) (Real.exp (f x) * f') x
参数：hf : HasDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasDerivAt.comp`：HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : H
asDerivAt h h' x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x
· 使用定理 `Real.hasDerivAt_exp`：hasDerivAt_exp (x : Real) : HasDerivAt exp (exp x) 
x
-/
theorem HasDerivAt.exp (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Real.exp (f x)) (Real.exp (f x) * f') x :=
  (Real.hasDerivAt_exp (f x)).comp x hf
/-
**HasDerivWithinAt.exp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.exp (hf : HasDerivWithinAt f f' s x) : HasDerivWithinAt (
fun x => Real.exp (f x)) (Real.exp (f x) * f') s x
参数：hf : HasDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasDerivAt.comp_hasDerivWithinAt`：HasDerivAt.comp_hasDerivWithinAt (hh₂ 
: HasDerivAt h₂ h₂' (h x)) (hh : HasDerivWithinAt h h' s x) : HasDerivWithinAt (
h₂ ∘ h) (h₂' * h') s x
· 使用定理 `Real.hasDerivAt_exp`：hasDerivAt_exp (x : Real) : HasDerivAt exp (exp x) 
x
-/
theorem HasDerivWithinAt.exp (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.exp (f x)) (Real.exp (f x) * f') s x :=
  (Real.hasDerivAt_exp (f x)).comp_hasDerivWithinAt x hf
/-
**derivWithin_exp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_exp (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDiff
WithinAt Real s x) : derivWithin (fun x => Real.exp (f x)) s x = Real.exp (f x) 
* derivWithin f s x
参数：hf : DifferentiableWithinAt Real f s x；hxs : UniqueDiffWithinAt Real s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.exp`：HasDerivWithinAt.exp (hf : HasDerivWithinAt f f' s
 x) : HasDerivWithinAt (fun x => Real.exp (f x)) (Real.exp (f x) * f') s x
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
-/
theorem derivWithin_exp (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => Real.exp (f x)) s x = Real.exp (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.exp.derivWithin hxs

@[simp]
/-
**deriv_exp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_exp (hc : DifferentiableAt Real f x) : deriv (fun x => Real.exp (f x
)) x = Real.exp (f x) * deriv f x
参数：hc : DifferentiableAt Real f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.exp`：HasDerivAt.exp (hf : HasDerivAt f f' x) : HasDerivAt (fu
n x => Real.exp (f x)) (Real.exp (f x) * f') x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_exp (hc : DifferentiableAt ℝ f x) :
    deriv (fun x => Real.exp (f x)) x = Real.exp (f x) * deriv f x :=
  hc.hasDerivAt.exp.deriv

end

section

/-! Register lemmas for the derivatives of the composition of `Real.exp` with a differentiable
function, for standalone use and use with `simp`. -/


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {f' : StrongDual ℝ E}
  {x : E} {s : Set E}

@[fun_prop]
/-
**ContDiff.exp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.exp {n} (hf : ContDiff Real n f) : ContDiff Real n fun x => Real.
exp (f x)
参数：hf : ContDiff Real n f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `Real.contDiff_exp`：contDiff_exp {n : WithTop Nat∞} : ContDiff Real n exp
-/
theorem ContDiff.exp {n} (hf : ContDiff ℝ n f) : ContDiff ℝ n fun x => Real.exp (f x) :=
  Real.contDiff_exp.comp hf

@[fun_prop]
/-
**ContDiffAt.exp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.exp {n} (hf : ContDiffAt Real n f x) : ContDiffAt Real n (fun x
 => Real.exp (f x)) x
参数：hf : ContDiffAt Real n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Real.contDiff_exp`：contDiff_exp {n : WithTop Nat∞} : ContDiff Real n exp
-/
theorem ContDiffAt.exp {n} (hf : ContDiffAt ℝ n f x) : ContDiffAt ℝ n (fun x => Real.exp (f x)) x :=
  Real.contDiff_exp.contDiffAt.comp x hf

@[fun_prop]
/-
**ContDiffOn.exp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.exp {n} (hf : ContDiffOn Real n f s) : ContDiffOn Real n (fun x
 => Real.exp (f x)) s
参数：hf : ContDiffOn Real n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp_contDiffOn`：ContDiff.comp_contDiffOn {s : Set E} {g : F ->
 G} {f : E -> F} (hg : ContDiff 𝕜 n g) (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 
n (g ∘ f) s
· 使用定理 `Real.contDiff_exp`：contDiff_exp {n : WithTop Nat∞} : ContDiff Real n exp
-/
theorem ContDiffOn.exp {n} (hf : ContDiffOn ℝ n f s) : ContDiffOn ℝ n (fun x => Real.exp (f x)) s :=
  Real.contDiff_exp.comp_contDiffOn hf

@[fun_prop]
/-
**ContDiffWithinAt.exp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.exp {n} (hf : ContDiffWithinAt Real n f s x) : ContDiffWi
thinAt Real n (fun x => Real.exp (f x)) s x
参数：hf : ContDiffWithinAt Real n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp_contDiffWithinAt`：ContDiffAt.comp_contDiffWithinAt (x : 
E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWit
hinAt 𝕜 n (g ∘ f) s x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Real.contDiff_exp`：contDiff_exp {n : WithTop Nat∞} : ContDiff Real n exp
-/
theorem ContDiffWithinAt.exp {n} (hf : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun x => Real.exp (f x)) s x :=
  Real.contDiff_exp.contDiffAt.comp_contDiffWithinAt x hf
/-
**HasFDerivWithinAt.exp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.exp (hf : HasFDerivWithinAt f f' s x) : HasFDerivWithinA
t (fun x => Real.exp (f x)) (Real.exp (f x) • f') s x
参数：hf : HasFDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivWithinAt`：HasDerivAt.comp_hasFDerivWithinAt {f 
: E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFD
erivWithinAt f f' s x) …
· 使用定理 `Real.hasDerivAt_exp`：hasDerivAt_exp (x : Real) : HasDerivAt exp (exp x) 
x
-/
theorem HasFDerivWithinAt.exp (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Real.exp (f x)) (Real.exp (f x) • f') s x :=
  (Real.hasDerivAt_exp (f x)).comp_hasFDerivWithinAt x hf
/-
**HasFDerivAt.exp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.exp (hf : HasFDerivAt f f' x) : HasFDerivAt (fun x => Real.exp
 (f x)) (Real.exp (f x) • f') x
参数：hf : HasFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivAt`：HasDerivAt.comp_hasFDerivAt {f : E -> 𝕜'} {
f' : E ->L[𝕜] 𝕜'} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFDerivAt f f' x) :
 HasFDerivAt (h₂ …
· 使用定理 `Real.hasDerivAt_exp`：hasDerivAt_exp (x : Real) : HasDerivAt exp (exp x) 
x
-/
theorem HasFDerivAt.exp (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Real.exp (f x)) (Real.exp (f x) • f') x :=
  (Real.hasDerivAt_exp (f x)).comp_hasFDerivAt x hf
/-
**HasStrictFDerivAt.exp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.exp (hf : HasStrictFDerivAt f f' x) : HasStrictFDerivAt 
(fun x => Real.exp (f x)) (Real.exp (f x) • f') x
参数：hf : HasStrictFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.comp_hasStrictFDerivAt`：HasStrictDerivAt.comp_hasStrict
FDerivAt {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x) (hh : HasStrictDerivAt h₂ h₂' (f x
)) (hf : HasStrictFDerivAt f …
· 使用定理 `Real.hasStrictDerivAt_exp`：hasStrictDerivAt_exp (x : Real) : HasStrictDe
rivAt exp (exp x) x
-/
theorem HasStrictFDerivAt.exp (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Real.exp (f x)) (Real.exp (f x) • f') x :=
  (Real.hasStrictDerivAt_exp (f x)).comp_hasStrictFDerivAt x hf
/-
**DifferentiableWithinAt.exp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.exp (hf : DifferentiableWithinAt Real f s x) : Diff
erentiableWithinAt Real (fun x => Real.exp (f x)) s x
参数：hf : DifferentiableWithinAt Real f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
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
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasFDerivWithinAt.exp`：HasFDerivWithinAt.exp (hf : HasFDerivWithinAt f f
' s x) : HasFDerivWithinAt (fun x => Real.exp (f x)) (Real.exp (f x) • f') s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.exp (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun x => Real.exp (f x)) s x :=
  hf.hasFDerivWithinAt.exp.differentiableWithinAt

@[simp, fun_prop]
/-
**DifferentiableAt.exp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.exp (hc : DifferentiableAt Real f x) : DifferentiableAt R
eal (fun x => Real.exp (f x)) x
参数：hc : DifferentiableAt Real f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
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
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasFDerivAt.exp`：HasFDerivAt.exp (hf : HasFDerivAt f f' x) : HasFDerivAt
 (fun x => Real.exp (f x)) (Real.exp (f x) • f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.exp (hc : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun x => Real.exp (f x)) x :=
  hc.hasFDerivAt.exp.differentiableAt

@[fun_prop]
/-
**DifferentiableOn.exp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.exp (hc : DifferentiableOn Real f s) : DifferentiableOn R
eal (fun x => Real.exp (f x)) s
参数：hc : DifferentiableOn Real f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.exp`：DifferentiableWithinAt.exp (hf : Differentia
bleWithinAt Real f s x) : DifferentiableWithinAt Real (fun x => Real.exp (f x)) 
s x
-/
theorem DifferentiableOn.exp (hc : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (fun x => Real.exp (f x)) s := fun x h => (hc x h).exp

@[simp, fun_prop]
/-
**Differentiable.exp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.exp (hc : Differentiable Real f) : Differentiable Real fun 
x => Real.exp (f x)
参数：hc : Differentiable Real f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.exp`：DifferentiableAt.exp (hc : DifferentiableAt Real f
 x) : DifferentiableAt Real (fun x => Real.exp (f x)) x
-/
theorem Differentiable.exp (hc : Differentiable ℝ f) : Differentiable ℝ fun x => Real.exp (f x) :=
  fun x => (hc x).exp
/-
**fderivWithin_exp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_exp (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDif
fWithinAt Real s x) : fderivWithin Real (fun x => Real.exp (f x)) s x = Real.exp
 (f x) • fderivWithin Real f s x
参数：hf : DifferentiableWithinAt Real f s x；hxs : UniqueDiffWithinAt Real s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
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
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.exp`：HasFDerivWithinAt.exp (hf : HasFDerivWithinAt f f
' s x) : HasFDerivWithinAt (fun x => Real.exp (f x)) (Real.exp (f x) • f') s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_exp (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => Real.exp (f x)) s x = Real.exp (f x) • fderivWithin ℝ f s x :=
  hf.hasFDerivWithinAt.exp.fderivWithin hxs

@[simp]
/-
**fderiv_exp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_exp (hc : DifferentiableAt Real f x) : fderiv Real (fun x => Real.e
xp (f x)) x = Real.exp (f x) • fderiv Real f x
参数：hc : DifferentiableAt Real f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
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
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.exp`：HasFDerivAt.exp (hf : HasFDerivAt f f' x) : HasFDerivAt
 (fun x => Real.exp (f x)) (Real.exp (f x) • f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_exp (hc : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => Real.exp (f x)) x = Real.exp (f x) • fderiv ℝ f x :=
  hc.hasFDerivAt.exp.fderiv

end

open Real in
@[simp]
/-
**iteratedDeriv_exp_const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_exp_const_mul (n : Nat) (c : Real) : (iteratedDeriv n fun s 
=> exp (c * s)) = fun s => c ^ n * exp (c * s)
参数：n : Nat；c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDeriv_comp_const_mul`：iteratedDeriv_comp_const_mul {n : Nat} {f 
: 𝕜 -> 𝕜} (h : ContDiff 𝕜 n f) (c : 𝕜) : iteratedDeriv n (fun x => f (c * x)) = 
fun x => c ^ n * i…
· 使用定理 `Real.contDiff_exp`：contDiff_exp {n : WithTop Nat∞} : ContDiff Real n exp
· 使用定理 `iteratedDeriv_eq_iterate`：iteratedDeriv_eq_iterate : iteratedDeriv n f =
 deriv^[n] f
· 使用定理 `Real.iter_deriv_exp`：∀ (n : ℕ), deriv^[n] Real.exp = Real.exp
-/
theorem iteratedDeriv_exp_const_mul (n : ℕ) (c : ℝ) :
    (iteratedDeriv n fun s => exp (c * s)) = fun s => c ^ n * exp (c * s) := by
  rw [iteratedDeriv_comp_const_mul contDiff_exp, iteratedDeriv_eq_iterate, iter_deriv_exp]
