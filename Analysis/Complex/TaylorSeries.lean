/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Convergence of Taylor series of holomorphic functions

We show that the Taylor series around some point `c : ℂ` of a function `f` that is complex
differentiable on the open ball of radius `r` around `c` converges to `f` on that open ball;
see `Complex.hasSum_taylorSeries_on_ball` and `Complex.taylorSeries_eq_on_ball` for versions
(in terms of `HasSum` and `tsum`, respectively) for functions to a complete normed
space over `ℂ`, and `Complex.taylorSeries_eq_on_ball'` for a variant when `f : ℂ → ℂ`.

There are corresponding statements for `Metric.eball`s; see
`Complex.hasSum_taylorSeries_on_eball`, `Complex.taylorSeries_eq_on_eball`
and `Complex.taylorSeries_eq_on_ball'`.

We also show that the Taylor series around some point `c : ℂ` of a function `f` that is complex
differentiable on all of `ℂ` converges to `f` on `ℂ`;
see `Complex.hasSum_taylorSeries_of_entire`, `Complex.taylorSeries_eq_of_entire` and
`Complex.taylorSeries_eq_of_entire'`.
-/

public section

namespace Complex

open Nat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] ⦃f : ℂ → E⦄

section ball

variable ⦃c : ℂ⦄ ⦃r : ℝ⦄ (hf : DifferentiableOn ℂ f (Metric.ball c r))
variable ⦃z : ℂ⦄ (hz : z ∈ Metric.ball c r)

include hf hz in
/-- A function that is complex differentiable on the open ball of radius `r` around `c`
is given by evaluating its Taylor series at `c` on this open ball. -/
/-
**Complex.hasSum_taylorSeries_on_ball** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：hasSum_taylorSeries_on_ball : HasSum (fun n : Nat => (n ! : Complex)⁻¹ • (
z - c) ^ n • iteratedDeriv n f c) (f z)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
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
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_ball'`：mem_ball' : y in ball x ε ↔ dist x y < ε
· 使用定理 `Metric.pos_of_mem_ball`：pos_of_mem_ball (hy : y in ball x ε) : 0 < ε
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.eball_coe`：Metric.eball_coe {x : α} {ε : Real>=0} : eball x ε = b
all x ε
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `HasFPowerSeriesOnBall.hasSum_iteratedFDeriv`：hasSum_iteratedFDeriv [Char
Zero 𝕜] {y : E} (hy : y in Metric.eball 0 r) : HasSum (fun n => (n ! : 𝕜)⁻¹ • it
eratedFDeriv 𝕜 n f x fun _ => y) …
· 使用定理 `DifferentiableOn.hasFPowerSeriesOnBall`：∀ {E : Type u} [inst : NormedAdd
CommGroup E] [inst_1 : NormedSpace ℂ E] [CompleteSpace E] {R : NNReal} {c : ℂ}  
 {f : ℂ → E},   Differentiab…
· 使用定理 `DifferentiableOn.mono`：DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t
) (st : s subseteq t) : DifferentiableOn 𝕜 f s
· 使用定理 `Metric.closedBall_subset_ball`：closedBall_subset_ball (h : ε₁ < ε₂) : cl
osedBall x ε₁ subseteq ball x ε₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Finset.card_fin`：Finset.card_fin (n : Nat) : #(univ : Finset (Fin n)) = 
n
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `ContinuousMultilinearMap.map_smul_univ`：map_smul_univ [Fintype ι] (c : ι
 -> R) (m : forall i, M₁ i) : (f fun i => c i • m i) = (∏ i, c i) • f m
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b

--- 原说明 ---
A function that is complex differentiable on the open ball of radius `r` around 
`c`
is given by evaluating its Taylor series at `c` on this open ball.
-/
lemma hasSum_taylorSeries_on_ball :
    HasSum (fun n : ℕ ↦ (n ! : ℂ)⁻¹ • (z - c) ^ n • iteratedDeriv n f c) (f z) := by
  obtain ⟨r', hr', hr'₀, hzr'⟩ : ∃ r' < r, 0 < r' ∧ z ∈ Metric.ball c r' := by
    obtain ⟨r', h₁, h₂⟩ := exists_between (Metric.mem_ball'.mp hz)
    exact ⟨r', h₂, Metric.pos_of_mem_ball h₁, Metric.mem_ball'.mpr h₁⟩
  lift r' to NNReal using hr'₀.le
  have hz' : z - c ∈ Metric.eball 0 r' := by
    rw [Metric.eball_coe]
    simpa only [mem_ball_iff_norm, sub_zero] using hzr'
  have H := (hf.mono <| Metric.closedBall_subset_ball hr').hasFPowerSeriesOnBall hr'₀
      |>.hasSum_iteratedFDeriv hz'
  simp only [add_sub_cancel] at H
  convert H with n
  simpa only [iteratedDeriv_eq_iteratedFDeriv, smul_eq_mul, mul_one, Finset.prod_const,
    Finset.card_fin]
    using ((iteratedFDeriv ℂ n f c).map_smul_univ (fun _ ↦ z - c) (fun _ ↦ 1)).symm

include hf hz in
/-- A function that is complex differentiable on the open ball of radius `r` around `c`
is given by evaluating its Taylor series at `c` on this open ball. -/
/-
**Complex.taylorSeries_eq_on_ball** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：taylorSeries_eq_on_ball : ∑' n : Nat, (n ! : Complex)⁻¹ • (z - c) ^ n • it
eratedDeriv n f c = f z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `Complex.hasSum_taylorSeries_on_ball`：hasSum_taylorSeries_on_ball : HasSu
m (fun n : Nat => (n ! : Complex)⁻¹ • (z - c) ^ n • iteratedDeriv n f c) (f z)

--- 原说明 ---
A function that is complex differentiable on the open ball of radius `r` around 
`c`
is given by evaluating its Taylor series at `c` on this open ball.
-/
lemma taylorSeries_eq_on_ball :
    ∑' n : ℕ, (n ! : ℂ)⁻¹ • (z - c) ^ n • iteratedDeriv n f c = f z :=
  (hasSum_taylorSeries_on_ball hf hz).tsum_eq

include hz in
/-- A function that is complex differentiable on the open ball of radius `r` around `c`
is given by evaluating its Taylor series at `c` on this open ball. -/
/-
**Complex.taylorSeries_eq_on_ball'** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：taylorSeries_eq_on_ball' {f : Complex -> Complex} (hf : DifferentiableOn C
omplex f (Metric.ball c r)) : ∑' n : Nat, (n ! : Complex)⁻¹ * iteratedDeriv n f 
c * (z - c) ^ n = f z
参数：hf : DifferentiableOn Complex f (Metric.ball c r)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `Complex.taylorSeries_eq_on_ball`：taylorSeries_eq_on_ball : ∑' n : Nat, (
n ! : Complex)⁻¹ • (z - c) ^ n • iteratedDeriv n f c = f z
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ

--- 原说明 ---
A function that is complex differentiable on the open ball of radius `r` around 
`c`
is given by evaluating its Taylor series at `c` on this open ball.
-/
lemma taylorSeries_eq_on_ball' {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball c r)) :
    ∑' n : ℕ, (n ! : ℂ)⁻¹ * iteratedDeriv n f c * (z - c) ^ n = f z := by
  convert! taylorSeries_eq_on_ball hf hz using 3 with n
  rw [mul_right_comm, smul_eq_mul, smul_eq_mul, mul_assoc]

end ball

section emetric

variable ⦃c : ℂ⦄ ⦃r : ENNReal⦄ (hf : DifferentiableOn ℂ f (Metric.eball c r))
variable ⦃z : ℂ⦄ (hz : z ∈ Metric.eball c r)

include hf hz in
/-- A function that is complex differentiable on the open ball of radius `r ≤ ∞` around `c`
is given by evaluating its Taylor series at `c` on this open ball. -/
/-
**Complex.hasSum_taylorSeries_on_eball** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：hasSum_taylorSeries_on_eball : HasSum (fun n : Nat => (n ! : Complex)⁻¹ • 
(z - c) ^ n • iteratedDeriv n f c) (f z)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_eball'`：mem_eball' : y in eball x ε ↔ edist x y < ε
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
· 使用引理 `Complex.hasSum_taylorSeries_on_ball`：hasSum_taylorSeries_on_ball : HasSu
m (fun n : Nat => (n ! : Complex)⁻¹ • (z - c) ^ n • iteratedDeriv n f c) (f z)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.eball_coe`：Metric.eball_coe {x : α} {ε : Real>=0} : eball x ε = b
all x ε
· 使用定理 `DifferentiableOn.mono`：DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t
) (st : s subseteq t) : DifferentiableOn 𝕜 f s
· 使用定理 `Metric.eball_subset_eball`：eball_subset_eball (h : ε₁ <= ε₂) : eball x ε
₁ subseteq eball x ε₂
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
A function that is complex differentiable on the open ball of radius `r ≤ ∞` aro
und `c`
is given by evaluating its Taylor series at `c` on this open ball.
-/
lemma hasSum_taylorSeries_on_eball :
    HasSum (fun n : ℕ ↦ (n ! : ℂ)⁻¹ • (z - c) ^ n • iteratedDeriv n f c) (f z) := by
  obtain ⟨r', hzr', hr'⟩ := exists_between (Metric.mem_eball'.mp hz)
  lift r' to NNReal using ne_top_of_lt hr'
  rw [← Metric.mem_eball', Metric.eball_coe] at hzr'
  refine hasSum_taylorSeries_on_ball ?_ hzr'
  rw [← Metric.eball_coe]
  exact hf.mono <| Metric.eball_subset_eball hr'.le

@[deprecated (since := "2026-01-24")]
alias hasSum_taylorSeries_on_emetric_ball := hasSum_taylorSeries_on_eball

include hf hz in
/-- A function that is complex differentiable on the open ball of radius `r ≤ ∞` around `c`
is given by evaluating its Taylor series at `c` on this open ball. -/
/-
**Complex.taylorSeries_eq_on_eball** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：taylorSeries_eq_on_eball : ∑' n : Nat, (n ! : Complex)⁻¹ • (z - c) ^ n • i
teratedDeriv n f c = f z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `Complex.hasSum_taylorSeries_on_eball`：hasSum_taylorSeries_on_eball : Has
Sum (fun n : Nat => (n ! : Complex)⁻¹ • (z - c) ^ n • iteratedDeriv n f c) (f z)

--- 原说明 ---
A function that is complex differentiable on the open ball of radius `r ≤ ∞` aro
und `c`
is given by evaluating its Taylor series at `c` on this open ball.
-/
lemma taylorSeries_eq_on_eball :
    ∑' n : ℕ, (n ! : ℂ)⁻¹ • (z - c) ^ n • iteratedDeriv n f c = f z :=
  (hasSum_taylorSeries_on_eball hf hz).tsum_eq

@[deprecated (since := "2026-01-24")]
alias taylorSeries_eq_on_emetric_ball := taylorSeries_eq_on_eball

include hz in
/-- A function that is complex differentiable on the open ball of radius `r ≤ ∞` around `c`
is given by evaluating its Taylor series at `c` on this open ball. -/
/-
**Complex.taylorSeries_eq_on_eball'** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：taylorSeries_eq_on_eball' {f : Complex -> Complex} (hf : DifferentiableOn 
Complex f (Metric.eball c r)) : ∑' n : Nat, (n ! : Complex)⁻¹ * iteratedDeriv n 
f c * (z - c) ^ n = f z
参数：hf : DifferentiableOn Complex f (Metric.eball c r)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `Complex.taylorSeries_eq_on_eball`：taylorSeries_eq_on_eball : ∑' n : Nat,
 (n ! : Complex)⁻¹ • (z - c) ^ n • iteratedDeriv n f c = f z
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ

--- 原说明 ---
A function that is complex differentiable on the open ball of radius `r ≤ ∞` aro
und `c`
is given by evaluating its Taylor series at `c` on this open ball.
-/
lemma taylorSeries_eq_on_eball' {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.eball c r)) :
    ∑' n : ℕ, (n ! : ℂ)⁻¹ * iteratedDeriv n f c * (z - c) ^ n = f z := by
  convert! taylorSeries_eq_on_eball hf hz using 3 with n
  rw [mul_right_comm, smul_eq_mul, smul_eq_mul, mul_assoc]

@[deprecated (since := "2026-01-24")]
alias taylorSeries_eq_on_emetric_ball' := taylorSeries_eq_on_eball'

end emetric

section entire

variable ⦃f : ℂ → E⦄ (hf : Differentiable ℂ f) (c z : ℂ)

include hf in
/-- A function that is complex differentiable on the complex plane is given by evaluating
its Taylor series at any point `c`. -/
/-
**Complex.hasSum_taylorSeries_of_entire** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：hasSum_taylorSeries_of_entire : HasSum (fun n : Nat => (n ! : Complex)⁻¹ •
 (z - c) ^ n • iteratedDeriv n f c) (f z)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.hasSum_taylorSeries_on_eball`：hasSum_taylorSeries_on_eball : Has
Sum (fun n : Nat => (n ! : Complex)⁻¹ • (z - c) ^ n • iteratedDeriv n f c) (f z)
· 使用定理 `Differentiable.differentiableOn`：Differentiable.differentiableOn (h : Di
fferentiable 𝕜 f) : DifferentiableOn 𝕜 f s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.mem_eball`：∀ {α : Type u} [inst : EDist α] {x y : α} {ε : ENNReal
}, y ∈ Metric.eball x ε ↔ edist y x < ε
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤

--- 原说明 ---
A function that is complex differentiable on the complex plane is given by evalu
ating
its Taylor series at any point `c`.
-/
lemma hasSum_taylorSeries_of_entire :
    HasSum (fun n : ℕ ↦ (n ! : ℂ)⁻¹ • (z - c) ^ n • iteratedDeriv n f c) (f z) :=
  hasSum_taylorSeries_on_eball hf.differentiableOn <| Metric.mem_eball.mpr <|
    edist_lt_top ..

include hf in
/-- A function that is complex differentiable on the complex plane is given by evaluating
its Taylor series at any point `c`. -/
/-
**Complex.taylorSeries_eq_of_entire** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：taylorSeries_eq_of_entire : ∑' n : Nat, (n ! : Complex)⁻¹ • (z - c) ^ n • 
iteratedDeriv n f c = f z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `Complex.hasSum_taylorSeries_of_entire`：hasSum_taylorSeries_of_entire : H
asSum (fun n : Nat => (n ! : Complex)⁻¹ • (z - c) ^ n • iteratedDeriv n f c) (f 
z)

--- 原说明 ---
A function that is complex differentiable on the complex plane is given by evalu
ating
its Taylor series at any point `c`.
-/
lemma taylorSeries_eq_of_entire :
    ∑' n : ℕ, (n ! : ℂ)⁻¹ • (z - c) ^ n • iteratedDeriv n f c = f z :=
  (hasSum_taylorSeries_of_entire hf c z).tsum_eq

/-- A function that is complex differentiable on the complex plane is given by evaluating
its Taylor series at any point `c`. -/
/-
**Complex.taylorSeries_eq_of_entire'** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：taylorSeries_eq_of_entire' {f : Complex -> Complex} (hf : Differentiable C
omplex f) : ∑' n : Nat, (n ! : Complex)⁻¹ * iteratedDeriv n f c * (z - c) ^ n = 
f z
参数：hf : Differentiable Complex f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `Complex.taylorSeries_eq_of_entire`：taylorSeries_eq_of_entire : ∑' n : Na
t, (n ! : Complex)⁻¹ • (z - c) ^ n • iteratedDeriv n f c = f z
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ

--- 原说明 ---
A function that is complex differentiable on the complex plane is given by evalu
ating
its Taylor series at any point `c`.
-/
lemma taylorSeries_eq_of_entire' {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    ∑' n : ℕ, (n ! : ℂ)⁻¹ * iteratedDeriv n f c * (z - c) ^ n = f z := by
  convert! taylorSeries_eq_of_entire hf c z using 3 with n
  rw [mul_right_comm, smul_eq_mul, smul_eq_mul, mul_assoc]

end entire

end Complex

