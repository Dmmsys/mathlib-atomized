/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# The Mean Value Property of Complex Differentiable Functions

This file established the classic mean value properties of complex differentiable functions,
computing the value of a function at the center of a circle as a circle average. It also provides
generalized versions that computing the value of a function at arbitrary points of a disk as circle
averages over suitable weighted functions.
-/

public section

open Complex Filter Function Metric Real Set Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f : ℂ → E} {R : ℝ} {c w : ℂ} {s : Set ℂ}

/-!
## Generalized Mean Value Properties

For a complex differentiable function `f`, the theorems in this section compute values of `f` in the
interior of a disk as circle averages of a weighted function.
-/

/--
The **Generalized Mean Value Property** of complex differentiable functions: If `f : ℂ → E` is
continuous on a closed disc of radius `R` and center `c`, and is complex differentiable at all but
countably many points of its interior, then for every point `w` in the disk, the circle average
`circleAverage (fun z ↦ ((z - c) * (z - w)⁻¹) • f z) c R` equals `f w`.
-/
/-
**circleAverage_sub_sub_inv_smul_of_differentiable_on_off_countable** 是 Mathlib 
中的一个定理，位于命名空间 ``。
形式化陈述：circleAverage_sub_sub_inv_smul_of_differentiable_on_off_countable (hs : s.
Countable) (h₁f : ContinuousOn f (closedBall c |R|)) (h₂f : forall z in ball c |
R| \ s, DifferentiableAt Complex f z) (hw : w in ball c |R|) : circleAverage (fu
n z => ((z - c) / (z - w)) • f z) c R = f w
参数：hs : s.Countable；h₁f : ContinuousOn f (closedBall c |R|)；h₂f : forall z in ba
ll c |R| \ s, DifferentiableAt Complex f z；hw : w in ball c |R|。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.circleAverage_abs_radius`：∀ {E : Type u_1} [inst : NormedAddCommGro
up E] [inst_1 : NormedSpace ℝ E] {f : ℂ → E} {c : ℂ} {R : ℝ},   Real.circleAvera
ge f c |R| = Real.c…
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.ball_eq_empty`：ball_eq_empty : ball x ε = ∅ ↔ ε <= 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.circleAverage_eq_circleIntegral`：circleAverage_eq_circleIntegral {F
 : Type*} [NormedAddCommGroup F] [NormedSpace Complex F] {f : Complex -> F} (h :
 R != 0) : circleAverage f…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `Complex.inv_I`：inv_I : I⁻¹ = -I
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `circleIntegral.integral_congr`：integral_congr {f g : Complex -> E} {c : 
Complex} {R : Real} (hR : 0 <= R) (h : EqOn f g (sphere c R)) : (∮ z in C(c, R),
 f z) = ∮ z in C(c,…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
（共 69 条，此处仅展示前 30 条）

--- 原说明 ---
The **Generalized Mean Value Property** of complex differentiable functions: If 
`f : ℂ → E` is
continuous on a closed disc of radius `R` and center `c`, and is complex differe
ntiable at all but
countably many points of its interior, then for every point `w` in the disk, the
 circle average
`circleAverage (fun z ↦ ((z - c) * (z - w)⁻¹) • f z) c R` equals `f w`.
-/
theorem circleAverage_sub_sub_inv_smul_of_differentiable_on_off_countable (hs : s.Countable)
    (h₁f : ContinuousOn f (closedBall c |R|)) (h₂f : ∀ z ∈ ball c |R| \ s, DifferentiableAt ℂ f z)
    (hw : w ∈ ball c |R|) :
    circleAverage (fun z ↦ ((z - c) / (z - w)) • f z) c R = f w := by
  rw [← circleAverage_abs_radius]
  rcases le_or_gt |R| 0 with hR | hR
  · simp_all [ball_eq_empty.2 hR]
  calc circleAverage (fun z ↦ ((z - c) * (z - w)⁻¹) • f z) c |R|
  _ = (2 * π * I)⁻¹ • (∮ z in C(c, |R|), (z - w)⁻¹ • f z) := by
    simp only [circleAverage_eq_circleIntegral hR.ne', mul_inv_rev, inv_I, neg_mul, neg_smul,
      neg_inj, ne_eq, mul_eq_zero, I_ne_zero, inv_eq_zero, ofReal_eq_zero, pi_ne_zero,
      OfNat.ofNat_ne_zero, or_self, not_false_eq_true, smul_right_inj]
    apply circleIntegral.integral_congr hR.le
    intro z hz
    match_scalars
    have : z - c ≠ 0 := by grind [ne_of_mem_sphere]
    grind
  _ = f w := by
    rw [circleIntegral_sub_inv_smul_of_differentiable_on_off_countable hs hw h₁f h₂f]
    match_scalars
    simp [field]

/--
The **Generalized Mean Value Property** of complex differentiable functions: If `f : ℂ → E` is
complex differentiable at all points of a closed disc of radius `R` and center `c`, then for every
point `w` in the disk, the circle average `circleAverage (fun z ↦ ((z - c) * (z - w)⁻¹) • f z) c R`
equals `f w`.
-/
/-
**DiffContOnCl.circleAverage_smul_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DiffContOnCl.circleAverage_smul_div (hf : DiffContOnCl Complex f (ball c |
R|)) (hw : w in ball c |R|) : circleAverage (fun z => ((z - c) / (z - w)) • f z)
 c R = f w
参数：hf : DiffContOnCl Complex f (ball c |R|)；hw : w in ball c |R|。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.ball_eq_empty`：ball_eq_empty : ball x ε = ∅ ↔ ε <= 0
· 使用定理 `circleAverage_sub_sub_inv_smul_of_differentiable_on_off_countable`：circl
eAverage_sub_sub_inv_smul_of_differentiable_on_off_countable (hs : s.Countable) 
(h₁f : ContinuousOn f (closedBall c |R|)) (h₂f : forall…
· 使用定理 `Set.countable_empty`：∀ {α : Type u}, ∅.Countable
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_ball`：closure_ball (x : E) {r : Real} (hr : r != 0) : closure (b
all x r) = closedBall x r
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_not_ge`：∀ {α : Type u_2} [inst : Preorder α] {a b : α}, ¬b ≤ a → a
 ≠ b
· 使用定理 `DiffContOnCl.continuousOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3
} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 :
 NormedAddCommG…
· 使用定理 `DifferentiableWithinAt.differentiableAt`：DifferentiableWithinAt.differen
tiableAt (h : DifferentiableWithinAt 𝕜 f s x) (hs : s in 𝓝 x) : DifferentiableAt
 𝕜 f x
· 使用定理 `DiffContOnCl.differentiableOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type
 u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst
_2 : NormedAddCommG…
· 使用定理 `Set.sdiff_empty`：sdiff_empty {s : Set α} : s \ ∅ = s
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)

--- 原说明 ---
The **Generalized Mean Value Property** of complex differentiable functions: If 
`f : ℂ → E` is
complex differentiable at all points of a closed disc of radius `R` and center `
c`, then for every
point `w` in the disk, the circle average `circleAverage (fun z ↦ ((z - c) * (z 
- w)⁻¹) • f z) c R`
equals `f w`.
-/
theorem DiffContOnCl.circleAverage_smul_div (hf : DiffContOnCl ℂ f (ball c |R|))
    (hw : w ∈ ball c |R|) :
    circleAverage (fun z ↦ ((z - c) / (z - w)) • f z) c R = f w := by
  by_cases hR : |R| ≤ 0
  · simp_all [ball_eq_empty.2 hR]
  apply circleAverage_sub_sub_inv_smul_of_differentiable_on_off_countable countable_empty _ _ hw
  · simpa [← closure_ball _ (ne_of_not_ge hR).symm] using hf.2
  · intro z hz
    rw [sdiff_empty] at hz
    apply (hf.1 z hz).differentiableAt (isOpen_ball.mem_nhds hz)

@[deprecated (since := "2026-02-11")]
alias circleAverage_sub_sub_inv_smul_of_differentiable_on := DiffContOnCl.circleAverage_smul_div

/-!
## Classic Mean Value Properties

For a complex differentiable function `f`, the theorems in this section compute value of `f` at the
center of a circle as a circle average of the function. This specializes the generalized mean value
properties discussed in the previous section.
-/

/--
The **Mean Value Property** of complex differentiable functions: If `f : ℂ → E` is continuous on a
closed disc of radius `R` and center `c`, and is complex differentiable at all but countably many
points of its interior, then the circle average `circleAverage f c R` equals `f c`.
-/
/-
**circleAverage_of_differentiable_on_off_countable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：circleAverage_of_differentiable_on_off_countable (hs : s.Countable) (h₁f :
 ContinuousOn f (closedBall c |R|)) (h₂f : forall z in ball c |R| \ s, Different
iableAt Complex f z) : circleAverage f c R = f c
参数：hs : s.Countable；h₁f : ContinuousOn f (closedBall c |R|)；h₂f : forall z in ba
ll c |R| \ s, DifferentiableAt Complex f z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.circleAverage_zero`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] 
[inst_1 : NormedSpace ℝ E] {f : ℂ → E} {c : ℂ} [CompleteSpace E],   Real.circleA
verage f c 0 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `circleAverage_sub_sub_inv_smul_of_differentiable_on_off_countable`：circl
eAverage_sub_sub_inv_smul_of_differentiable_on_off_countable (hs : s.Countable) 
(h₁f : ContinuousOn f (closedBall c |R|)) (h₂f : forall…
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Real.circleAverage_congr_sphere`：circleAverage_congr_sphere {f₁ f₂ : Com
plex -> E} (hf : Set.EqOn f₁ f₂ (sphere c |R|)) : circleAverage f₁ c R = circleA
verage f₂ c R
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
The **Mean Value Property** of complex differentiable functions: If `f : ℂ → E` 
is continuous on a
closed disc of radius `R` and center `c`, and is complex differentiable at all b
ut countably many
points of its interior, then the circle average `circleAverage f c R` equals `f 
c`.
-/
theorem circleAverage_of_differentiable_on_off_countable (hs : s.Countable)
    (h₁f : ContinuousOn f (closedBall c |R|)) (h₂f : ∀ z ∈ ball c |R| \ s, DifferentiableAt ℂ f z) :
    circleAverage f c R = f c := by
  by_cases hR : R = 0
  · simp [hR]
  · rw [← circleAverage_sub_sub_inv_smul_of_differentiable_on_off_countable hs h₁f h₂f (by aesop)]
    apply circleAverage_congr_sphere fun z hz ↦ ?_
    have : z - c ≠ 0 := by grind [ne_of_mem_sphere]
    simp_all

/--
The **Mean Value Property** of complex differentiable functions: If `f : ℂ → E` is complex
differentiable at all points of a closed disc of radius `R` and center `c`, then the circle average
`circleAverage f c R` equals `f c`.
-/
/-
**DiffContOnCl.circleAverage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DiffContOnCl.circleAverage (hf : DiffContOnCl Complex f (ball c |R|)) : ci
rcleAverage f c R = f c
参数：hf : DiffContOnCl Complex f (ball c |R|)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.circleAverage_zero`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] 
[inst_1 : NormedSpace ℝ E] {f : ℂ → E} {c : ℂ} [CompleteSpace E],   Real.circleA
verage f c 0 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DiffContOnCl.circleAverage_smul_div`：DiffContOnCl.circleAverage_smul_div
 (hf : DiffContOnCl Complex f (ball c |R|)) (hw : w in ball c |R|) : circleAvera
ge (fun z => ((z - c) / (…
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Real.circleAverage_congr_sphere`：circleAverage_congr_sphere {f₁ f₂ : Com
plex -> E} (hf : Set.EqOn f₁ f₂ (sphere c |R|)) : circleAverage f₁ c R = circleA
verage f₂ c R
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
The **Mean Value Property** of complex differentiable functions: If `f : ℂ → E` 
is complex
differentiable at all points of a closed disc of radius `R` and center `c`, then
 the circle average
`circleAverage f c R` equals `f c`.
-/
theorem DiffContOnCl.circleAverage (hf : DiffContOnCl ℂ f (ball c |R|)) :
    circleAverage f c R = f c := by
  by_cases hR : R = 0
  · simp [hR]
  · rw [← circleAverage_smul_div hf (by aesop)]
    apply circleAverage_congr_sphere fun z hz ↦ ?_
    have : z - c ≠ 0 := by grind [ne_of_mem_sphere]
    simp_all

@[deprecated (since := "2026-02-11")]
alias circleAverage_of_differentiable_on := DiffContOnCl.circleAverage
