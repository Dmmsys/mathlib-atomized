/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.FactorizedRational
public import Mathlib.Analysis.Meromorphic.RCLike
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# Canonical Decomposition

If a function `f` is meromorphic on a compact set `U`, then it has only finitely many zeros and
poles on the disk, and the theorem `MeromorphicOn.extract_zeros_poles` can be used to re-write `f`
as `(∏ᶠ u, (· - u) ^ divisor f U u) • g`, where `g` is analytic without zeros on `U`. In case where
`U` is a disk, one consider a similar decomposition, called *Finite Canonical Decomposition* or
*Finite Blaschke Product* that replaces the factors `(· - u)` by canonical factors that take only
values of norm one on the boundary of the disk. This file introduces the canonical factors and
provides API for the canonical decomposition.

This file also formulates an extended version of the canonical decomposition that takes zeros on
poles on the boundary of the ball into account.

See Page 160f of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] for a detailed
discussion.
-/

@[expose] public section

namespace Complex

open ComplexConjugate Filter Function MeromorphicOn Metric Real Set Topology

variable {R : ℝ} {w : ℂ}

/-!
## Canonical Factors

Given `R : ℝ` and `w : ℂ`, the canonical factor `canonical R w : ℂ → ℂ` is meromorphic function in
normal form that has a single pole at `w`, no zeros, and takes values of norm one on the circle of
radius `R`.
-/

/--
Given `R : ℝ` and `w : ℂ`, the canonical factor is the function
`fun z ↦ (R ^ 2 - (conj w) * z) / (R * (z - w))`. In applications, one will typically consider a
setting where `w ∈ ball 0 R`.
-/
/-
**Complex.canonicalFactor** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：canonicalFactor (R : Real) (w : Complex) : Complex -> Complex
参数：R : Real；w : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `R : ℝ` and `w : ℂ`, the canonical factor is the function
`fun z ↦ (R ^ 2 - (conj w) * z) / (R * (z - w))`. In applications, one will typi
cally consider a
setting where `w ∈ ball 0 R`.
-/
noncomputable def canonicalFactor (R : ℝ) (w : ℂ) : ℂ → ℂ :=
  fun z ↦ (R ^ 2 - (conj w) * z) / (R * (z - w))
/-
**Complex.canonicalFactor_def** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：canonicalFactor_def (R : Real) (w : Complex) : canonicalFactor R w = fun z
 => (R ^ 2 - (conj w) * z) / (R * (z - w))
参数：R : Real；w : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma canonicalFactor_def (R : ℝ) (w : ℂ) :
    canonicalFactor R w = fun z ↦ (R ^ 2 - (conj w) * z) / (R * (z - w)) :=
  rfl
/-
**Complex.canonicalFactor_apply** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：canonicalFactor_apply (R : Real) (w z : Complex) : canonicalFactor R w z =
 (R ^ 2 - (conj w) * z) / (R * (z - w))
参数：R : Real；w z : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma canonicalFactor_apply (R : ℝ) (w z : ℂ) :
    canonicalFactor R w z = (R ^ 2 - (conj w) * z) / (R * (z - w)) :=
  rfl

@[simp]
/-
**Complex.canonicalFactor_apply_self** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：canonicalFactor_apply_self (R : Real) (w : Complex) : canonicalFactor R w 
w = 0
参数：R : Real；w : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma canonicalFactor_apply_self (R : ℝ) (w : ℂ) :
    canonicalFactor R w w = 0 := by
  simp [canonicalFactor_apply]

/-!
### Regularity properties
-/

variable (R w) in
/--
Canonical factors are meromorphic.
-/
/-
**Complex.meromorphic_canonicalFactor** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (R : ℝ) (w : ℂ), Meromorphic (Complex.canonicalFactor R w)
参数：R : ℝ；w : ℂ；Complex.canonicalFactor R w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicAt.fun_div`：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgeb
ra 𝕜 𝕜'] {x…
· 使用定理 `MeromorphicAt.fun_sub`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
x : 𝕜} {f g…
· 使用引理 `MeromorphicAt.const`：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) 
x
· 使用定理 `MeromorphicAt.fun_mul`：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgeb
ra 𝕜 𝕜'] {x…
· 使用引理 `MeromorphicAt.id`：id (x : 𝕜) : MeromorphicAt id x

--- 原说明 ---
Canonical factors are meromorphic.
-/
@[fun_prop] theorem meromorphic_canonicalFactor : Meromorphic (canonicalFactor R w) := by
  intro x
  unfold canonicalFactor
  fun_prop

open scoped ComplexOrder in
variable (R w) in
/--
The canonical factor `CanonicalFactor R w` is analytic on the complement of `w`.
-/
/-
**Complex.analyticOnNhd_canonicalFactor** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：analyticOnNhd_canonicalFactor : AnalyticOnNhd Complex (canonicalFactor R w
) {w}ᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.canonicalFactor_def`：canonicalFactor_def (R : Real) (w : Complex
) : canonicalFactor R w = fun z => (R ^ 2 - (conj w) * z) / (R * (z - w))
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AnalyticAt.fun_div`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {𝕝 :
 Type u_…
· 使用定理 `AnalyticAt.fun_sub`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 …
· 使用定理 `AnalyticAt.fun_mul`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {A :
 Type u_…
· 使用引理 `analyticAt_id`：analyticAt_id : AnalyticAt 𝕜 (id : E -> E) z
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Mathlib.Meta.Positivity.ofReal_ne_zero_of_ne_zero`：∀ {z : ℝ}, z ≠ 0 → ↑z
 ≠ 0

--- 原说明 ---
The canonical factor `CanonicalFactor R w` is analytic on the complement of `w`.
-/
theorem analyticOnNhd_canonicalFactor : AnalyticOnNhd ℂ (canonicalFactor R w) {w}ᶜ := by
  intro x hx
  rw [canonicalFactor_def]
  obtain (rfl | h) := eq_or_ne R 0
  · simpa using analyticAt_const
  have : x - w ≠ 0 := by grind
  fun_prop (disch := positivity)

/--
The canonical factor `CanonicalFactor R w` has a simple pole at `z = w`.
-/
/-
**Complex.meromorphicOrderAt_canonicalFactor** 是 Mathlib 中的一个定理，位于命名空间 `Complex`
。
形式化陈述：meromorphicOrderAt_canonicalFactor (h : w in ball 0 R) : meromorphicOrderA
t (canonicalFactor R w) w = -1
参数：h : w in ball 0 R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fun_meromorphicOrderAt_div`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {𝕜' : Type u_4} [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : Normed
Algebra 𝕜 𝕜'] {x…
· 使用定理 `MeromorphicAt.fun_sub`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
x : 𝕜} {f g…
· 使用引理 `MeromorphicAt.const`：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) 
x
· 使用定理 `MeromorphicAt.fun_mul`：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgeb
ra 𝕜 𝕜'] {x…
· 使用引理 `MeromorphicAt.id`：id (x : 𝕜) : MeromorphicAt id x
· 使用定理 `fun_meromorphicOrderAt_mul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {𝕜' : Type u_4} [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : Normed
Algebra 𝕜 𝕜'] {x…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff`：MeromorphicNFAt.meromorp
hicOrderAt_eq_zero_iff (hf : MeromorphicNFAt f x) : meromorphicOrderAt f x = 0 ↔
 f x != 0
· 使用定理 `AnalyticAt.meromorphicNFAt`：AnalyticAt.meromorphicNFAt (hf : AnalyticAt 
𝕜 f x) : MeromorphicNFAt f x
· 使用定理 `AnalyticAt.fun_sub`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 …
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `AnalyticAt.fun_mul`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {A :
 Type u_…
· 使用引理 `analyticAt_id`：analyticAt_id : AnalyticAt 𝕜 (id : E -> E) z
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.normSq_eq_conj_mul_self`：normSq_eq_conj_mul_self {z : Complex} :
 (normSq z : Complex) = conj z * z
· 使用引理 `Complex.normSq_eq_norm_sq`：normSq_eq_norm_sq (z : Complex) : normSq z = 
‖z‖ ^ 2
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
· 使用定理 `Complex.ofReal_inj`：ofReal_inj {z w : Real} : (z : Complex) = w ↔ z = w
· 使用引理 `sq_eq_sq₀`：sq_eq_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 = b ^ 2 ↔ a = b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Metric.pos_of_mem_ball`：pos_of_mem_ball (hy : y in ball x ε) : 0 < ε
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `mem_ball_iff_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] {a
 b : E} {r : ℝ}, b ∈ Metric.ball a r ↔ ‖b - a‖ < r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
The canonical factor `CanonicalFactor R w` has a simple pole at `z = w`.
-/
theorem meromorphicOrderAt_canonicalFactor (h : w ∈ ball 0 R) :
    meromorphicOrderAt (canonicalFactor R w) w = -1 := by
  unfold canonicalFactor
  rw [fun_meromorphicOrderAt_div (by fun_prop) (by fun_prop),
    fun_meromorphicOrderAt_mul (by fun_prop) (by fun_prop)]
  have : meromorphicOrderAt (fun z ↦ ↑R ^ 2 - (starRingEnd ℂ) w * z) w = 0 := by
    refine (MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff ?_).2 ?_
    · apply AnalyticAt.meromorphicNFAt
      fun_prop
    · rw [← normSq_eq_conj_mul_self, normSq_eq_norm_sq w, sub_ne_zero, ne_eq, ← ofReal_pow,
        ofReal_inj, sq_eq_sq₀ (pos_of_mem_ball h).le (norm_nonneg w)]
      rw [mem_ball_iff_norm, sub_zero] at h
      grind
  simp [this, meromorphicOrderAt_const, (pos_of_mem_ball h).ne',
    meromorphicOrderAt_id_sub_const]

/--
Canonical factors are meromorphic in normal form.
-/
/-
**Complex.meromorphicNFOn_canonicalFactor** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：meromorphicNFOn_canonicalFactor (h : w in ball 0 R) : MeromorphicNFOn (can
onicalFactor R w) Set.univ
参数：h : w in ball 0 R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `meromorphicNFAt_iff_analyticAt_or`：meromorphicNFAt_iff_analyticAt_or : M
eromorphicNFAt f x ↔ AnalyticAt 𝕜 f x ∨ (MeromorphicAt f x ∧ meromorphicOrderAt 
f x < 0 ∧ f x = 0)
· 使用定理 `Complex.meromorphic_canonicalFactor`：∀ (R : ℝ) (w : ℂ), Meromorphic (Com
plex.canonicalFactor R w)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.meromorphicOrderAt_canonicalFactor`：meromorphicOrderAt_canonical
Factor (h : w in ball 0 R) : meromorphicOrderAt (canonicalFactor R w) w = -1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithTop.coe_lt_zero`：∀ {α : Type u} [inst : Zero α] [inst_1 : LT α] {a :
 α}, ↑a < 0 ↔ a < 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Complex.canonicalFactor_apply_self`：canonicalFactor_apply_self (R : Real
) (w : Complex) : canonicalFactor R w w = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AnalyticAt.meromorphicNFAt`：AnalyticAt.meromorphicNFAt (hf : AnalyticAt 
𝕜 f x) : MeromorphicNFAt f x
· 使用定理 `Complex.analyticOnNhd_canonicalFactor`：analyticOnNhd_canonicalFactor : A
nalyticOnNhd Complex (canonicalFactor R w) {w}ᶜ

--- 原说明 ---
Canonical factors are meromorphic in normal form.
-/
theorem meromorphicNFOn_canonicalFactor (h : w ∈ ball 0 R) :
    MeromorphicNFOn (canonicalFactor R w) Set.univ := by
  intro z hz
  obtain (rfl | h₁) := eq_or_ne z w
  · rw [meromorphicNFAt_iff_analyticAt_or]
    right
    refine ⟨meromorphic_canonicalFactor R z z, ?_, by simp⟩
    simpa [meromorphicOrderAt_canonicalFactor h] using WithTop.coe_lt_zero.mpr (by lia : -1 < 0)
  apply (analyticOnNhd_canonicalFactor R w z h₁).meromorphicNFAt

/-!
### Values of Canonical Factors
-/

open scoped ComplexOrder in
/--
The canonical factor `CanonicalFactor R w` has no zeros inside the ball of radius `R`.
-/
/-
**Complex.canonicalFactor_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：canonicalFactor_ne_zero {z : Complex} (hw : w in ball 0 R) (h₁z : z in clo
sedBall 0 R) (h₂z : z != w) : canonicalFactor R w z != 0
参数：hw : w in ball 0 R；h₁z : z in closedBall 0 R；h₂z : z != w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
· 使用定理 `RCLike.norm_conj`：norm_conj (z : K) : ‖conj z‖ = ‖z‖
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `abs_mul_abs_self`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder
 α] (a : α), |a| * |a| = a * a
· 使用引理 `Complex.canonicalFactor_apply`：canonicalFactor_apply (R : Real) (w z : C
omplex) : canonicalFactor R w z = (R ^ 2 - (conj w) * z) / (R * (z - w))
· 使用定理 `div_ne_zero`：div_ne_zero (ha : a != 0) (hb : b != 0) : a / b != 0
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Mathlib.Meta.Positivity.ofReal_pos`：∀ {x : ℝ}, 0 < x → 0 < ↑x
· 使用定理 `sub_ne_zero_of_ne`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a ≠ b → a - b ≠ 0

--- 原说明 ---
The canonical factor `CanonicalFactor R w` has no zeros inside the ball of radiu
s `R`.
-/
theorem canonicalFactor_ne_zero {z : ℂ} (hw : w ∈ ball 0 R) (h₁z : z ∈ closedBall 0 R)
    (h₂z : z ≠ w) :
    canonicalFactor R w z ≠ 0 := by
  obtain ⟨hR, hzw⟩ : 0 < R ∧ z - w ≠ 0 := by grind [mem_ball_zero_iff, norm_nonneg]
  simp only [mem_ball, dist_zero_right, mem_closedBall] at hw h₁z
  have h_num_ne_zero : R ^ 2 - conj w * z ≠ 0 := by
    suffices ‖conj w * z‖ < ‖(R : ℂ) ^ 2‖ by grind
    suffices ‖w‖ * ‖z‖ < R * R by simpa [sq]
    grw [h₁z]
    gcongr
  rw [canonicalFactor_apply]
  positivity

/--
The function `CanonicalFactor R w` vanishes only at `w`.
-/
/-
**Complex.canonicalFactor_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：canonicalFactor_eq_zero_iff {z : Complex} (hw : w in ball 0 R) (hz : z in 
ball 0 R) : canonicalFactor R w z = 0 ↔ z = w
参数：hw : w in ball 0 R；hz : z in ball 0 R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Complex.canonicalFactor_ne_zero`：canonicalFactor_ne_zero {z : Complex} (
hw : w in ball 0 R) (h₁z : z in closedBall 0 R) (h₂z : z != w) : canonicalFactor
 R w z != 0
· 使用定理 `Metric.ball_subset_closedBall`：ball_subset_closedBall : ball x ε subsete
q closedBall x ε
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.canonicalFactor_apply_self`：canonicalFactor_apply_self (R : Real
) (w : Complex) : canonicalFactor R w w = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
The function `CanonicalFactor R w` vanishes only at `w`.
-/
theorem canonicalFactor_eq_zero_iff {z : ℂ} (hw : w ∈ ball 0 R) (hz : z ∈ ball 0 R) :
    canonicalFactor R w z = 0 ↔ z = w := by
  constructor
  · contrapose
    exact canonicalFactor_ne_zero hw (ball_subset_closedBall hz)
  · simp_all

open scoped ComplexOrder in
/--
The canonical factor `CanonicalFactor R w` takes values of norm one on `sphere 0 R`.
-/
/-
**Complex.norm_canonicalFactor_eval_circle_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Com
plex`。
形式化陈述：norm_canonicalFactor_eval_circle_eq_one {z : Complex} (hw : w in ball 0 R)
 (hz : z in sphere 0 R) : ‖canonicalFactor R w z‖ = 1
参数：hw : w in ball 0 R；hz : z in sphere 0 R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.canonicalFactor.eq_1`：∀ (R : ℝ) (w z : ℂ), Complex.canonicalFact
or R w z = (↑R ^ 2 - (starRingEnd ℂ) w * z) / (↑R * (z - w))
· 使用定理 `norm_div`：norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖
· 使用引理 `div_eq_iff`：div_eq_iff (hb : b != 0) : a / b = c ↔ a = c * b
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `norm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖ = 
0 ↔ a = 0
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Mathlib.Meta.Positivity.ofReal_pos`：∀ {x : ℝ}, 0 < x → 0 < ↑x
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
· 使用引理 `Complex.normSq_eq_norm_sq`：normSq_eq_norm_sq (z : Complex) : normSq z = 
‖z‖ ^ 2
· 使用定理 `Complex.normSq_eq_conj_mul_self`：normSq_eq_conj_mul_self {z : Complex} :
 (normSq z : Complex) = conj z * z
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
· 使用定理 `RCLike.norm_conj`：norm_conj (z : K) : ‖conj z‖ = ‖z‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a

--- 原说明 ---
The canonical factor `CanonicalFactor R w` takes values of norm one on `sphere 0
 R`.
-/
theorem norm_canonicalFactor_eval_circle_eq_one {z : ℂ} (hw : w ∈ ball 0 R) (hz : z ∈ sphere 0 R) :
    ‖canonicalFactor R w z‖ = 1 := by
  obtain ⟨hR, hzw⟩ : 0 < R ∧ z - w ≠ 0 := by
    grind [mem_ball_zero_iff, norm_nonneg, mem_sphere_zero_iff_norm]
  rw [canonicalFactor, norm_div, div_eq_iff (by rw [ne_eq, norm_eq_zero]; positivity), one_mul]
  obtain rfl := by simpa [mem_sphere_zero_iff_norm] using hz
  rw [← ofReal_pow, ← normSq_eq_norm_sq, normSq_eq_conj_mul_self, ← sub_mul, mul_comm _ z]
  simp [← map_sub]

/-!
### Orders and Divisors
-/

/--
Canonical factors are nowhere locally constant zero.
-/
/-
**Complex.meromorphicOrderAt_canonicalFactor_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `C
omplex`。
形式化陈述：meromorphicOrderAt_canonicalFactor_ne_top {z : Complex} {R : Real} (w : Co
mplex) (hR : 0 < R) : meromorphicOrderAt (canonicalFactor R w) z != ⊤
参数：w : Complex；hR : 0 < R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Meromorphic.exists_meromorphicOrderAt_ne_top_iff_forall`：Meromorphic.exi
sts_meromorphicOrderAt_ne_top_iff_forall {f : 𝕜 -> E} (hf : Meromorphic f) : (ex
ists u, meromorphicOrderAt f u != ⊤) ↔ (foral…
· 使用定理 `Complex.meromorphic_canonicalFactor`：∀ (R : ℝ) (w : ℂ), Meromorphic (Com
plex.canonicalFactor R w)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.meromorphicOrderAt_canonicalFactor`：meromorphicOrderAt_canonical
Factor (h : w in ball 0 R) : meromorphicOrderAt (canonicalFactor R w) w = -1
· 使用定理 `Metric.mem_ball_self`：mem_ball_self (h : 0 < ε) : x in ball x ε
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff`：MeromorphicNFAt.meromorp
hicOrderAt_eq_zero_iff (hf : MeromorphicNFAt f x) : meromorphicOrderAt f x = 0 ↔
 f x != 0
· 使用定理 `AnalyticAt.meromorphicNFAt`：AnalyticAt.meromorphicNFAt (hf : AnalyticAt 
𝕜 f x) : MeromorphicNFAt f x
· 使用定理 `Complex.analyticOnNhd_canonicalFactor`：analyticOnNhd_canonicalFactor : A
nalyticOnNhd Complex (canonicalFactor R w) {w}ᶜ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p

--- 原说明 ---
Canonical factors are nowhere locally constant zero.
-/
theorem meromorphicOrderAt_canonicalFactor_ne_top {z : ℂ} {R : ℝ} (w : ℂ) (hR : 0 < R) :
    meromorphicOrderAt (canonicalFactor R w) z ≠ ⊤ := by
  apply (meromorphic_canonicalFactor R w).exists_meromorphicOrderAt_ne_top_iff_forall.1
  use 0
  by_cases hw : w = 0
  · simp_all [meromorphicOrderAt_canonicalFactor (mem_ball_self hR)]
  suffices meromorphicOrderAt (canonicalFactor R w) 0 = 0 by simp_all
  rw [MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff]
  · simp_all [canonicalFactor, ne_of_gt hR]
  · apply AnalyticAt.meromorphicNFAt
    apply analyticOnNhd_canonicalFactor
    grind

/--
The divisor of `CanonicalFactor R w` is `-w`.  In other words, the divisor function takes the value
-1 at `w` and is zero elsewhere.
-/
/-
**Complex.divisor_canonicalFactor** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：divisor_canonicalFactor (hw : w in ball 0 R) : MeromorphicOn.divisor (cano
nicalFactor R w) (ball 0 R) = -(Function.locallyFinsuppWithin.single w 1).restri
ct (Set.subset_univ (ball 0 R))
参数：hw : w in ball 0 R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.locallyFinsuppWithin.ext`：ext [Zero Y] {D₁ D₂ : locallyFinsuppW
ithin U Y} (h : forall a, D₁ a = D₂ a) : D₁ = D₂
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeromorphicOn.divisor_apply`：divisor_apply {f : 𝕜 -> E} (hf : Meromorphi
cOn f U) (hz : z in U) : divisor f U z = (meromorphicOrderAt f z).untop₀
· 使用定理 `Complex.meromorphic_canonicalFactor`：∀ (R : ℝ) (w : ℂ), Meromorphic (Com
plex.canonicalFactor R w)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Complex.meromorphicOrderAt_canonicalFactor`：meromorphicOrderAt_canonical
Factor (h : w in ball 0 R) : meromorphicOrderAt (canonicalFactor R w) w = -1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `WithTop.untop₀_neg`：∀ {α : Type u_1} [inst : AddCommGroup α] (a : WithTo
p α), (-a).untop₀ = -a.untop₀
· 使用定理 `WithTop.untop₀_one`：untop₀_one {α : Type*} [AddMonoidWithOne α] : (1 : W
ithTop α).untop₀ = 1
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Function.locallyFinsuppWithin.single_apply`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] {Y : Type u_2} [inst_1 : DecidableEq X] [inst_2 : Zero Y] {x₁ x
₂ : X}   {y : Y}, (Function.loca…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff`：MeromorphicNFAt.meromorp
hicOrderAt_eq_zero_iff (hf : MeromorphicNFAt f x) : meromorphicOrderAt f x = 0 ↔
 f x != 0
· 使用定理 `Complex.meromorphicNFOn_canonicalFactor`：meromorphicNFOn_canonicalFactor
 (h : w in ball 0 R) : MeromorphicNFOn (canonicalFactor R w) Set.univ
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Complex.canonicalFactor_ne_zero`：canonicalFactor_ne_zero {z : Complex} (
hw : w in ball 0 R) (h₁z : z in closedBall 0 R) (h₂z : z != w) : canonicalFactor
 R w z != 0
· 使用定理 `Metric.ball_subset_closedBall`：ball_subset_closedBall : ball x ε subsete
q closedBall x ε
· 使用引理 `WithTop.untop₀_zero`：untop₀_zero : untop₀ 0 = (0 : α)
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用引理 `Function.locallyFinsuppWithin.apply_eq_zero_of_notMem`：apply_eq_zero_of_
notMem [Zero Y] {z : X} (D : locallyFinsuppWithin U Y) (hz : z ∉ U) : D z = 0

--- 原说明 ---
The divisor of `CanonicalFactor R w` is `-w`.  In other words, the divisor funct
ion takes the value
-1 at `w` and is zero elsewhere.
-/
theorem divisor_canonicalFactor (hw : w ∈ ball 0 R) :
    MeromorphicOn.divisor (canonicalFactor R w) (ball 0 R)
      = -(Function.locallyFinsuppWithin.single w 1).restrict (Set.subset_univ (ball 0 R)) := by
  ext z
  by_cases hz : z ∈ ball 0 R
  · rw [MeromorphicOn.divisor_apply
      (fun z hz ↦ meromorphic_canonicalFactor R w z) hz]
    obtain (rfl | h₂z) := eq_or_ne z w
    · rw [meromorphicOrderAt_canonicalFactor hz]
      simp_all [Function.locallyFinsuppWithin.restrict_apply]
    · have : meromorphicOrderAt (canonicalFactor R w) z = 0 := by
        rw [(meromorphicNFOn_canonicalFactor hw (Set.mem_univ z)).meromorphicOrderAt_eq_zero_iff]
        exact canonicalFactor_ne_zero hw (ball_subset_closedBall hz) h₂z
      simp [this, h₂z, Function.locallyFinsuppWithin.restrict_apply, hz]
  · simp_all

/-!
## Canonical Decomposition

The canonical decomposition theorem shows that a meromorphic function `f` on a disk is equal, up to
modification over a discrete set, to a product of canonical factors and a meromorphic function `g`
without zeros or poles in the interior of the disk.

To simplify notation and avoid repetition, we introduce a structure, `CanonicalDecomp`, that bundles
the conclusions of the decomposition theorem.
-/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {R : ℝ} {c w : ℂ}
  {f g : ℂ → E}

/--
Given functions `f`, `g` and a real number `R`, the following convenience structure packs the
information relevant in the canonical decomposition.  The condition "`g` is without zeros or poles"
is formulated by saying that `g` is meromorphic in normal form and `g ≠ 0`.
-/
/-
**Complex.CanonicalDecomp** 是 Mathlib 中的一个结构，位于命名空间 `Complex`。
形式化陈述：CanonicalDecomp (f g : Complex -> E) (R : Real) : Prop where /-- A proof t
hat `f` is meromorphic on `closedBall 0 R`. -/ meromorphicOn : MeromorphicOn f (
closedBall 0 R) /-- A proof that `g` is meromorphic in normal form on `closedBal
l 0 R`. -/ meromorphicNFOn : MeromorphicNFOn g (closedBall 0 R) /-- A proof that
 `g` does not vanish in the interior of the ball. -/ ne_zero : forall u in (ball
 0 R), g u != 0 /-- A proof that `f` is equal, up to modification over a discret
e set, to a product of `g`
参数：f g : Complex -> E；R : Real。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given functions `f`, `g` and a real number `R`, the following convenience struct
ure packs the
information relevant in the canonical decomposition.  The condition "`g` is with
out zeros or poles"
is formulated by saying that `g` is meromorphic in normal form and `g ≠ 0`. -/
-/
structure CanonicalDecomp (f g : ℂ → E) (R : ℝ) : Prop where
  /-- A proof that `f` is meromorphic on `closedBall 0 R`. -/
  meromorphicOn : MeromorphicOn f (closedBall 0 R)
  /-- A proof that `g` is meromorphic in normal form on `closedBall 0 R`. -/
  meromorphicNFOn : MeromorphicNFOn g (closedBall 0 R)
  /-- A proof that `g` does not vanish in the interior of the ball. -/
  ne_zero : ∀ u ∈ (ball 0 R), g u ≠ 0
  /--
  A proof that `f` is equal, up to modification over a discrete set, to a product of `g` and
  canonical factors prescribed by the divisor of `f`.
  -/
  eventuallyEq : f =ᶠ[codiscreteWithin (closedBall 0 R)]
    (∏ᶠ u, (canonicalFactor R u) ^ (-MeromorphicOn.divisor f (ball 0 R) u)) • g

-- Auxiliary lemma for the proof of the canonical decomposition theorem: The factor in the canonical
-- decomposition is meromorphic in normal form.
/-
**Complex.canonicalDecomposition_aux** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma canonicalDecomposition_aux₁ (F : locallyFinsuppWithin (ball (0 : ℂ) R) ℤ) :
    MeromorphicNFOn (∏ᶠ u, (canonicalFactor R u) ^ (F u)) (ball (0 : ℂ) R) := by
  refine meromorphicNFOn_finprod (fun w ↦ ?_) fun z hz a ha b hb ↦ ?_
  · by_cases hw : w ∈ ball 0 R
    · exact fun _ _ ↦ (meromorphicNFOn_canonicalFactor hw).zpow (by trivial)
    · simp only [hw, not_false_eq_true, locallyFinsuppWithin.apply_eq_zero_of_notMem, zpow_zero]
      exact analyticOnNhd_const.meromorphicNFOn
  · have ⟨h₂a, h₂b⟩ : a ∈ ball 0 R ∧ b ∈ ball 0 R := by constructor <;> (by_contra; aesop)
    grind [eq_zero_of_zpow_eq_zero hb, eq_zero_of_zpow_eq_zero ha,
      canonicalFactor_eq_zero_iff h₂b hz, canonicalFactor_eq_zero_iff h₂a hz]

-- Auxiliary lemma for the proof of the canonical decomposition theorem: Write a function with
-- finite support as a linear combination of singleton indicator functions.
open Function.locallyFinsuppWithin in
/-
**Complex.sum_apply_smul_single_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma sum_apply_smul_single_eq_self
    {X : Type*} [TopologicalSpace X] [DecidableEq X] {U : Set X}
    {F : Function.locallyFinsuppWithin U ℤ} (h : F.support.Finite) :
    ∑ x ∈ h.toFinset, (F x) • ((single x (1 : ℤ)).restrict (subset_univ U)) = F := by
  ext z
  by_cases hz : z ∉ U
  · aesop
  simp only [coe_sum, coe_zsmul, zsmul_eq_mul, Finset.sum_apply, Pi.mul_apply, Pi.intCast_apply,
    Int.cast_eq, Function.locallyFinsuppWithin.restrict_apply]
  by_cases hz : z ∈ F.support
  · rw [← Finset.add_sum_erase _ _ (by aesop : z ∈ h.toFinset), Finset.sum_eq_zero (by aesop)]
    aesop
  · aesop

-- Auxiliary lemma for the proof of the canonical decomposition theorem: Exhibit the divisor of the
-- factor in the canonical decomposition as the negative of the divisor of `f`.
/-
**Complex.canonicalDecomposition_aux** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma canonicalDecomposition_aux₂ (h₁f : MeromorphicOn f (closedBall 0 R)) :
    divisor (∏ᶠ u, (canonicalFactor R u) ^ (divisor f (ball 0 R) u)) (ball 0 R)
      = -(divisor f (ball 0 R)) := by
  have η₀ : (-divisor f (ball 0 R)).support.Finite := by simp [h₁f.divisor_ball_support_finite]
  rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ (by aesop) η₀, divisor_prod]
  · simp_rw [divisor_zpow (fun z hz ↦ meromorphic_canonicalFactor R _ z)]
    conv_rhs => rw [← sum_apply_smul_single_eq_self η₀]
    apply Finset.sum_congr rfl fun x hx ↦ ?_
    rw [divisor_canonicalFactor, smul_neg, locallyFinsuppWithin.coe_neg, Pi.neg_apply, neg_smul]
    by_contra
    simp_all
  · intro z hz
    apply zpow (fun x hx ↦ meromorphic_canonicalFactor R z x)
  · intro z hz x hx
    rw [meromorphicOrderAt_zpow (meromorphic_canonicalFactor R z x)]
    lift (meromorphicOrderAt (canonicalFactor R z) x) to ℤ using
      (meromorphicOrderAt_canonicalFactor_ne_top z (pos_of_mem_ball hx)) with ℓ
    simp [← WithTop.coe_mul]

-- Auxiliary lemma for the proof of the canonical decomposition theorem: The (inverse of the) factor
-- in the canonical decomposition does not vanish identically.
/-
**Complex.canonicalDecomposition_aux** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma canonicalDecomposition_aux₃ {z : ℂ} (hR : 0 < R) :
    meromorphicOrderAt (∏ᶠ (c : ℂ), canonicalFactor R c ^ (divisor f (ball 0 R)) c) z ≠ ⊤ := by
  apply meromorphicOrderAt_finprod_ne_top
    (fun _ ↦ MeromorphicAt.zpow (meromorphic_canonicalFactor _ _ _) _)
  intro c
  rw [meromorphicOrderAt_zpow (meromorphic_canonicalFactor R c z)]
  lift meromorphicOrderAt (canonicalFactor R c) z to ℤ using
    (meromorphicOrderAt_canonicalFactor_ne_top c hR) with ℓ
  simp [← WithTop.coe_mul]

/--
**Canonical decomposition:** A meromorphic function `f` on a disk is equal, up to modification over
a discrete set, to a product of canonical factors and a meromorphic function `g` without zeros or
poles in the interior of the disk.
-/
/-
**Complex._root_.MeromorphicOn.exists_canonicalDecomp** 是 Mathlib 中的一个定理，位于命名空间 
`Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Canonical decomposition:** A meromorphic function `f` on a disk is equal, up t
o modification over
a discrete set, to a product of canonical factors and a meromorphic function `g`
 without zeros or
poles in the interior of the disk.
-/
theorem _root_.MeromorphicOn.exists_canonicalDecomp
    (h₁f : MeromorphicOn f (closedBall 0 R))
    (h₂f : ∀ u : (closedBall (0 : ℂ) R), meromorphicOrderAt f u ≠ ⊤) :
    ∃ g : ℂ → E, CanonicalDecomp f g R := by
  -- Trivial case: If `R` is non-positive, then the ball is empty.
  by_cases hR : R ≤ 0
  · use fun _ ↦ f 0
    exact {
      meromorphicOn := h₁f
      meromorphicNFOn := fun z hz ↦ AnalyticAt.meromorphicNFAt analyticAt_const
      ne_zero := by simp [ball_eq_empty.2 hR]
      eventuallyEq := by
        filter_upwards [self_mem_codiscreteWithin (closedBall 0 R)] with a ha
        have : R = 0 := by grind [nonneg_of_mem_closedBall ha]
        aesop
    }
  rw [not_le] at hR
  -- General case: The requirement that `f =ᶠ[…] (something) • g` implies that `g` must equal
  -- `(something)⁻¹ • g`, converted to a meromorphic function in normal form. The next lines define
  -- `g` in this way and establish basic properties.
  let φ := (∏ᶠ c, canonicalFactor R c ^ (divisor f (ball 0 R)) c) • f
  have hφ : MeromorphicOn φ (closedBall 0 R) := by
    apply smul (MeromorphicOn.finprod _) h₁f
    exact fun z ↦ zpow (fun z₁ hz₁ ↦ meromorphic_canonicalFactor _ _ _) _
  let g := toMeromorphicNFOn φ (closedBall 0 R)
  have h₃g : divisor g (ball 0 R) = 0 := by
    rw [divisor_congr_codiscreteWithin
        ((toMeromorphicNFOn_eqOn_codiscrete hφ).symm.filter_mono
        (codiscreteWithin_mono ball_subset_closedBall)) isOpen_ball,
      divisor_smul _ (fun x hx ↦ h₁f x (ball_subset_closedBall hx))
        (fun z _ ↦ canonicalDecomposition_aux₃ hR)
        (fun z hz ↦ h₂f ⟨z, ball_subset_closedBall hz⟩),
      canonicalDecomposition_aux₂ h₁f, neg_add_cancel]
    apply (canonicalDecomposition_aux₁ _).meromorphicOn
  have h₂g : MeromorphicNFOn g (closedBall 0 R) :=
    meromorphicNFOn_toMeromorphicNFOn φ (closedBall 0 R)
  have h₄g {z : ℂ} (hz : z ∈ closedBall 0 R) : meromorphicOrderAt g z ≠ ⊤ := by
    rw [meromorphicOrderAt_toMeromorphicNFOn hφ hz, meromorphicOrderAt_smul _ (h₁f z hz)]
    · simpa [h₂f ⟨z, hz⟩] using canonicalDecomposition_aux₃ hR
    · apply MeromorphicAt.finprod (fun x ↦ (meromorphic_canonicalFactor R x z).zpow _)
  -- Use the function `g` defined above and establish the required properties
  use g
  have η₀ : (-divisor f (ball 0 R)).support.Finite := by simp [h₁f.divisor_ball_support_finite]
  exact {
    meromorphicOn := h₁f
    meromorphicNFOn := meromorphicNFOn_toMeromorphicNFOn φ (closedBall 0 R)
    ne_zero := by
      intro z hz
      rw [← MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff (h₂g (ball_subset_closedBall hz))]
      have : divisor g (ball 0 R) z = 0 := by simp [h₃g]
      rw [divisor_apply (fun x hx ↦ (h₂g (ball_subset_closedBall hx)).meromorphicAt) hz] at this
      simpa [h₄g (ball_subset_closedBall hz)] using this
    eventuallyEq := by
      trans (∏ i ∈ η₀.toFinset, canonicalFactor R i ^ (-(divisor f (ball 0 R)) i)) • φ
      · unfold φ
        rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ (by aesop) η₀]
        · filter_upwards [codiscreteWithin_mono (by tauto) η₀.compl_mem_codiscrete,
            self_mem_codiscreteWithin (closedBall 0 R)] with a ha h₂a
          simp only [Pi.smul_apply', Finset.prod_apply, Pi.pow_apply]
          rw [← smul_assoc, ← Finset.prod_smul, Finset.prod_eq_one, one_smul]
          intro x hx
          rw [smul_eq_mul, ← zpow_add', neg_add_cancel, zpow_zero]
          simp_all only [ne_eq, Subtype.forall, mem_closedBall, dist_zero_right,
            locallyFinsuppWithin.support_neg, mem_compl_iff, mem_support, Decidable.not_not,
            Finite.mem_toFinset, neg_add_cancel, not_true_eq_false, neg_eq_zero, and_self, or_self,
            or_false]
          apply canonicalFactor_ne_zero _ (by simp_all) (by grind)
          by_contra h
          simp_all
      · rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ (by aesop) η₀]
        filter_upwards [toMeromorphicNFOn_eqOn_codiscrete hφ] using by simp_all [g]
  }

/--
Given a canonical decomposition `CanonicalDecomp f g R`, the function associated with the divisor of
`g` equals the function associated with the divisor of `f`, seen as a meromorphic function on the
sphere.
-/
/-
**Complex.CanonicalDecomp.divisor_eq_divisor** 是 Mathlib 中的一个定理，位于命名空间 `Complex.
CanonicalDecomp`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] 
{R : ℝ} {f g : ℂ → E} {x : ℂ},   Complex.CanonicalDecomp f g R →     0 < R → (Me
romorphicOn.divisor g (Metric.closedBall 0 R)) x = (MeromorphicOn.divisor f (Met
ric.sphere 0 R)) x
参数：MeromorphicOn.divisor g (Metric.closedBall 0 R)；MeromorphicOn.divisor f (Metr
ic.sphere 0 R)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff`：MeromorphicNFAt.meromorp
hicOrderAt_eq_zero_iff (hf : MeromorphicNFAt f x) : meromorphicOrderAt f x = 0 ↔
 f x != 0
· 使用定理 `Complex.CanonicalDecomp.meromorphicNFOn`：∀ {E : Type u_1} [inst : Normed
AddCommGroup E] [inst_1 : NormedSpace ℂ E] {f g : ℂ → E} {R : ℝ},   Complex.Cano
nicalDecomp f g R → Meromorph…
· 使用定理 `mem_closedBall_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] 
{a : E} {r : ℝ}, a ∈ Metric.closedBall 0 r ↔ ‖a‖ ≤ r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Complex.CanonicalDecomp.ne_zero`：∀ {E : Type u_1} [inst : NormedAddCommG
roup E] [inst_1 : NormedSpace ℂ E] {f g : ℂ → E} {R : ℝ},   Complex.CanonicalDec
omp f g R → ∀ u ∈ Met…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `MeromorphicOn.divisor_apply`：divisor_apply {f : 𝕜 -> E} (hf : Meromorphi
cOn f U) (hz : z in U) : divisor f U z = (meromorphicOrderAt f z).untop₀
· 使用定理 `MeromorphicNFOn.meromorphicOn`：MeromorphicNFOn.meromorphicOn (hf : Merom
orphicNFOn f U) : MeromorphicOn f U
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `WithTop.untop₀_zero`：untop₀_zero : untop₀ 0 = (0 : α)
· 使用引理 `Function.locallyFinsuppWithin.apply_eq_zero_of_notMem`：apply_eq_zero_of_
notMem [Zero Y] {z : X} (D : locallyFinsuppWithin U Y) (hz : z ∉ U) : D z = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `analyticAt_finprod`：analyticAt_finprod {α : Type*} {A : Type*} [NormedCo
mmRing A] [NormedAlgebra 𝕜 A] {f : α -> E -> A} {c : E} (h : forall a, AnalyticA
t 𝕜 (f a…
· 使用引理 `AnalyticAt.zpow`：AnalyticAt.zpow {f : E -> 𝕝} {z : E} {n : Int} (h₁f : A
nalyticAt 𝕜 f z) (h₂f : f z != 0) : AnalyticAt 𝕜 (f ^ n) z
· 使用定理 `Complex.analyticOnNhd_canonicalFactor`：analyticOnNhd_canonicalFactor : A
nalyticOnNhd Complex (canonicalFactor R w) {w}ᶜ
· 使用定理 `Complex.canonicalFactor_ne_zero`：canonicalFactor_ne_zero {z : Complex} (
hw : w in ball 0 R) (h₁z : z in closedBall 0 R) (h₂z : z != w) : canonicalFactor
 R w z != 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
（共 60 条，此处仅展示前 30 条）

--- 原说明 ---
Given a canonical decomposition `CanonicalDecomp f g R`, the function associated
 with the divisor of
`g` equals the function associated with the divisor of `f`, seen as a meromorphi
c function on the
sphere.
-/
theorem CanonicalDecomp.divisor_eq_divisor {x : ℂ} (D : CanonicalDecomp f g R) (hR : 0 < R) :
    divisor g (closedBall (0 : ℂ) R) x = divisor f (sphere 0 R) x := by
  rcases lt_trichotomy ‖x‖ R with h|h|h
  · -- The case where `x` is contained in `ball 0 R`. There, the divisor of `g` vanishes because `g`
    -- does not have zeros or poles. The divisor of `f` vanishes because `x` is not contained in the
    -- sphere.
    have : x ∉ sphere (0 : ℂ) R := by aesop
    have := (D.meromorphicNFOn (mem_closedBall_zero_iff.mpr h.le)).meromorphicOrderAt_eq_zero_iff.2
      (D.ne_zero x (by aesop))
    rw [divisor_apply D.meromorphicNFOn.meromorphicOn (mem_closedBall_zero_iff.mpr h.le)]
    simp_all
  · -- The case where `x` is contained in `sphere 0 R`. There, the orders of `f` and `g` agree
    -- because the canonical factors are analytic and do not vanish.
    have η₁ : AnalyticAt ℂ (∏ᶠ u, canonicalFactor R u ^ (-(divisor f (ball 0 R)) u)) x := by
      refine analyticAt_finprod fun a ↦ ?_
      by_cases ha : a ∈ ball 0 R
      · exact (analyticOnNhd_canonicalFactor _ _ _ (by aesop)).zpow
          (canonicalFactor_ne_zero ha (by aesop) (by aesop))
      · simp_all only [mem_ball, dist_zero_right, not_lt,
          locallyFinsuppWithin.apply_eq_zero_of_notMem, neg_zero, zpow_zero]
        exact analyticAt_const
    have η₀ : f =ᶠ[𝓝[≠] x] (∏ᶠ u, canonicalFactor R u ^ (-(divisor f (ball 0 R)) u)) • g := by
      refine MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
        (U := closedBall 0 R) (D.meromorphicOn x (by aesop))
        (η₁.meromorphicAt.smul (D.meromorphicNFOn.meromorphicOn x (by aesop))) (by aesop) ?_
        D.eventuallyEq
      rw [← closure_ball 0 hR.ne']
      exact isOpen_ball.perfect_closure.2
    have : meromorphicOrderAt (∏ᶠ u, canonicalFactor R u ^ (-(divisor f (ball 0 R)) u)) x = 0 := by
      refine η₁.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.2 (finprod_apply_ne_zero fun a ↦ ?_)
      by_cases ha : a ∈ ball 0 R
      · exact zpow_ne_zero _ (canonicalFactor_ne_zero ha (by aesop) (by aesop))
      · simp_all
    rw [divisor_apply (D.meromorphicOn.mono_set sphere_subset_closedBall) (by aesop),
      divisor_apply D.meromorphicNFOn.meromorphicOn (by aesop), meromorphicOrderAt_congr η₀,
      meromorphicOrderAt_smul η₁.meromorphicAt (D.meromorphicNFOn (by aesop)).meromorphicAt]
    simp_all
  · -- Trivial case: `x` is outside `closedBall 0 R`, so both divisors evaluate to zero.
    have : x ∉ sphere (0 : ℂ) R := by aesop
    simp_all

/-!
## Extended Canonical Decomposition

The extended canonical decomposition theorem shows that a meromorphic function `f` on a closed disk
is equal, up to modification over a discrete set, to a product of a non-vanishing analytic function,
canonical factors and meromorphic functions of the form `(x - const) ^ n` where `const` is on the
circumference of the disk.

To simplify notation and avoid repetition, we introduce a structure, `ECanonicalDecomp`, that
bundles the conclusions of the extended canonical decomposition theorem.
-/

/--
Given functions `f`, `g` and a real number `R`, the following convenience structure packs the
information relevant in the extended canonical decomposition.
-/
/-
**Complex.ECanonicalDecomp** 是 Mathlib 中的一个归纳类型，位于命名空间 `Complex`。
形式化陈述：{E : Type u_1} → [inst : NormedAddCommGroup E] → [NormedSpace ℂ E] → (ℂ → 
E) → (ℂ → E) → ℝ → Prop
参数：ℂ → E；ℂ → E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given functions `f`, `g` and a real number `R`, the following convenience struct
ure packs the
information relevant in the extended canonical decomposition.
-/
structure ECanonicalDecomp (f g : ℂ → E) (R : ℝ) where
  /-- A proof that `f` is meromorphic on `closedBall 0 R`. -/
  meromorphicOn : MeromorphicOn f (closedBall 0 R)
  /-- A proof that `g` is analytic in a neighborhood of `closedBall 0 R`. -/
  analyticOnNhd : AnalyticOnNhd ℂ g (closedBall 0 R)
  /-- A proof that `g` does not vanish on the closed ball. -/
  ne_zero : ∀ u ∈ (closedBall 0 R), g u ≠ 0
  /--
  A proof that `f` is equal, up to modification over a discrete set, to a product of `g`, canonical
  factors prescribed by the divisor of `f`, and a factorized rational function with poles and zeros
  only on the boundary of the ball.
  -/
  eventuallyEq : f =ᶠ[codiscreteWithin (closedBall 0 R)]
    ((∏ᶠ u, (canonicalFactor R u) ^ (-divisor f (ball 0 R) u))
    * (∏ᶠ v, (· - v) ^ (divisor f (sphere 0 R)) v)) • g

/--
**Extended canonical decomposition:** A meromorphic function on a closed disk is equal, up to
modification over a discrete set, to a product of a non-vanishing analytic function, canonical
factors and meromorphic functions of the form `(x - const) ^ n` where `const` is on the
circumference of the disk.
-/
/-
**Complex._root_.MeromorphicOn.exists_ecanonicalDecomp** 是 Mathlib 中的一个定理，位于命名空间
 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Extended canonical decomposition:** A meromorphic function on a closed disk is
 equal, up to
modification over a discrete set, to a product of a non-vanishing analytic funct
ion, canonical
factors and meromorphic functions of the form `(x - const) ^ n` where `const` is
 on the
circumference of the disk.
-/
theorem _root_.MeromorphicOn.exists_ecanonicalDecomp (h₁f : MeromorphicOn f (closedBall 0 R))
    (h₂f : ∀ u : (closedBall (0 : ℂ) R), meromorphicOrderAt f u ≠ ⊤) :
    ∃ h, ECanonicalDecomp f h R := by
  rcases gt_trichotomy 0 R with hR | hR | hR
  · use fun _ ↦ f 0
    exact {
      meromorphicOn := by simp_all
      analyticOnNhd := by simp_all
      ne_zero := by simp_all
      eventuallyEq := by
        simp_all only [closedBall_of_neg]
        filter_upwards [Filter.self_mem_codiscreteWithin ∅] with a ha
        tauto
    }
  · use fun _ ↦ meromorphicTrailingCoeffAt f 0
    exact {
      meromorphicOn := by simp_all
      analyticOnNhd _ _ := by fun_prop
      ne_zero := by
        simp only [hR.symm, closedBall_zero, mem_singleton_iff, ne_eq, forall_eq]
        apply MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero (h₁f 0 _) _
        <;> simp_all
      eventuallyEq := by
        simp only [hR.symm, closedBall_zero]
        apply subsingleton_singleton.mem_codiscreteWithin
    }
  obtain ⟨g, D⟩ := h₁f.exists_canonicalDecomp h₂f
  have h₄g : ∀ (u : closedBall (0 : ℂ) R), meromorphicOrderAt g u ≠ ⊤ := by
    rw [← D.meromorphicNFOn.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall
      (Metric.isConnected_closedBall hR.le)]
    have s₁ : (0 : ℂ) ∈ closedBall 0 R := by simp [hR.le]
    use ⟨0, s₁⟩
    simp [(D.meromorphicNFOn s₁).meromorphicOrderAt_eq_zero_iff.2 (D.ne_zero 0 (by simp [hR]))]
  obtain ⟨h, h₁h, h₂h, h₃h⟩ := D.meromorphicNFOn.meromorphicOn.extract_zeros_poles h₄g <|
    (divisor g (closedBall 0 R)).finiteSupport <| isCompact_closedBall 0 R
  use h
  exact {
    meromorphicOn := h₁f
    analyticOnNhd := h₁h
    ne_zero := (h₂h ⟨·, ·⟩)
    eventuallyEq := by
      filter_upwards [D.eventuallyEq, h₃h] with a h₁a h₂a
      simp_rw [← D.divisor_eq_divisor hR]
      simp_all [← smul_assoc]
    }
/-
**Complex.mulSupport_pow_subset_support** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma mulSupport_pow_subset_support {α β : Type*} [DivInvMonoid α] (f : β → α)
    (g : β → ℤ) : (fun x ↦ f x ^ g x).mulSupport ⊆ g.support := by
  simp only [mulSupport_subset_iff, ne_eq, mem_support]
  intro
  contrapose!
  simp +contextual

/--
Companion lemma to `MeromorphicOn.exists_ecanonicalDecomp`: In the setting of the extended canonical
decomposition, write the function `h` entirely in terms of `f`.
-/
/-
**Complex.ECanonicalDecomp.eq_smul_meromorphicTrailingCoeffAt** 是 Mathlib 中的一个定理
，位于命名空间 `Complex.ECanonicalDecomp`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] 
{R : ℝ} {w : ℂ} {f h : ℂ → E},   Complex.ECanonicalDecomp f h R →     w ∈ Metric
.closedBall 0 R →       0 < R →         h w =           ((∏ᶠ (i : ℂ),           
      meromorphicTrailingCoeffAt (Complex.canonicalFactor R i) w ^              
     (MeromorphicOn.divisor f (Metric.ball 0 R)) i) *               ∏ᶠ (i : ℂ), 
                meromorphicTrailingCoeffAt (fun x => x - i) w ^ (-MeromorphicOn.
divisor f (Metric.sphere 0 R)) i) •             meromorphicTrailingCoeffAt f w
参数：(∏ᶠ (i : ℂ),                 meromorphicTrailingCoeffAt (Complex.canonicalFac
tor R i) w ^                   (MeromorphicOn.divisor f (Metric.ball 0 R)) i) * 
              ∏ᶠ (i : ℂ),                 meromorphicTrailingCoeffAt (fun x => x
 - i) w ^ (-MeromorphicOn.divisor f (Metric.sphere 0 R)) i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `divisor_sphere_support_finite`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] [ProperSpace…
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用引理 `MeromorphicOn.divisor_ball_support_finite`：divisor_ball_support_finite [
ProperSpace 𝕜] {f : 𝕜 -> E} {R : Real} {c : 𝕜} (hf : MeromorphicOn f (closedBall
 c R)) : (divisor f (ball c R))…
· 使用定理 `Complex.ECanonicalDecomp.meromorphicOn`：∀ {E : Type u_1} [inst : NormedA
ddCommGroup E] [inst_1 : NormedSpace ℂ E] {f g : ℂ → E} {R : ℝ},   Complex.ECano
nicalDecomp f g R → Meromorp…
· 使用引理 `AnalyticAt.meromorphicAt`：AnalyticAt.meromorphicAt {f : 𝕜 -> E} {x : 𝕜} 
(hf : AnalyticAt 𝕜 f x) : MeromorphicAt f x
· 使用定理 `Complex.ECanonicalDecomp.analyticOnNhd`：∀ {E : Type u_1} [inst : NormedA
ddCommGroup E] [inst_1 : NormedSpace ℂ E] {f g : ℂ → E} {R : ℝ},   Complex.ECano
nicalDecomp f g R → Analytic…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `meromorphicTrailingCoeffAt_congr_nhdsNE`：meromorphicTrailingCoeffAt_cong
r_nhdsNE {f₁ f₂ : 𝕜 -> E} (h : f₁ =ᶠ[𝓝[!=] x] f₂) : meromorphicTrailingCoeffAt f
₁ x = meromorphicTrailingCoef…
· 使用定理 `MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_prepe
rfect`：eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect (hf : Mer
omorphicAt f x) (hg : MeromorphicAt g x) (hx : x in U) (hU : Preper…
· 使用引理 `MeromorphicAt.smul`：smul [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E] {f : 
𝕜 -> R} {g : 𝕜 -> E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) : Meromor
phicAt (…
· 使用引理 `MeromorphicAt.mul`：mul {f g : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (hg : Me
romorphicAt g x) : MeromorphicAt (f * g) x
· 使用定理 `MeromorphicAt.finprod`：finprod {x : 𝕜} (hf : forall i, MeromorphicAt (F 
i) x) : MeromorphicAt (∏ᶠ i, F i) x
· 使用引理 `MeromorphicAt.zpow`：zpow {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (n : Int
) : MeromorphicAt (f ^ n) x
· 使用引理 `Meromorphic.meromorphicAt`：meromorphicAt {x : 𝕜} (hf : Meromorphic f) : 
MeromorphicAt f x
· 使用定理 `Complex.meromorphic_canonicalFactor`：∀ (R : ℝ) (w : ℂ), Meromorphic (Com
plex.canonicalFactor R w)
· 使用定理 `MeromorphicAt.fun_sub`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
x : 𝕜} {f g…
· 使用引理 `MeromorphicAt.id`：id (x : 𝕜) : MeromorphicAt id x
· 使用引理 `MeromorphicAt.const`：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) 
x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_ball`：closure_ball (x : E) {r : Real} (hr : r != 0) : closure (b
all x r) = closedBall x r
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Perfect.acc`：∀ {α : Type u_1} [inst : TopologicalSpace α] {C : Set α}, P
erfect C → Preperfect C
· 使用定理 `IsOpen.perfect_closure`：IsOpen.perfect_closure [PerfectSpace α] {U : Set
 α} (hU : IsOpen U) : Perfect (closure U)
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
· 使用定理 `Complex.ECanonicalDecomp.eventuallyEq`：∀ {E : Type u_1} [inst : NormedAd
dCommGroup E] [inst_1 : NormedSpace ℂ E] {f g : ℂ → E} {R : ℝ},   Complex.ECanon
icalDecomp f g R →     f =ᶠ…
· 使用定理 `finprod_eq_prod_of_mulSupport_subset`：finprod_eq_prod_of_mulSupport_subs
et (f : α -> M) {s : Finset α} (h : mulSupport f subseteq s) : ∏ᶠ i, f i = ∏ i i
n s, f i
（共 60 条，此处仅展示前 30 条）

--- 原说明 ---
Companion lemma to `MeromorphicOn.exists_ecanonicalDecomp`: In the setting of th
e extended canonical
decomposition, write the function `h` entirely in terms of `f`.
-/
lemma ECanonicalDecomp.eq_smul_meromorphicTrailingCoeffAt
    {f h : ℂ → E} (D : ECanonicalDecomp f h R) (hw : w ∈ closedBall 0 R) (hR : 0 < R) :
    h w
      = ((∏ᶠ i, meromorphicTrailingCoeffAt (canonicalFactor R i) w ^ (divisor f (ball 0 R) i))
          * (∏ᶠ i, meromorphicTrailingCoeffAt (· - i) w ^ (-divisor f (sphere 0 R)) i))
          • meromorphicTrailingCoeffAt f w := by
  -- Finiteness properties and side results used throughout the proof
  let B₀R := ball (0 : ℂ) R
  let S₀R := sphere (0 : ℂ) R
  lift (divisor f S₀R).support to Finset ℂ using divisor_sphere_support_finite with t₁ ht₁
  lift (divisor f B₀R).support to Finset ℂ using D.meromorphicOn.divisor_ball_support_finite
    with t₂ ht₂
  have := (D.analyticOnNhd w hw).meromorphicAt
  rw [Eq.comm]
  -- Proof body: Substitute `f` using `h₁f` and compute
  calc ((∏ᶠ (i : ℂ), meromorphicTrailingCoeffAt (canonicalFactor R i) w ^ (divisor f B₀R) i)
      * ∏ᶠ (i : ℂ), meromorphicTrailingCoeffAt (· - i) w ^ (-divisor f S₀R) i)
      • meromorphicTrailingCoeffAt f w
    _ = ((∏ᶠ (i : ℂ), meromorphicTrailingCoeffAt (canonicalFactor R i) w ^ (divisor f B₀R) i)
      * ∏ᶠ (i : ℂ), meromorphicTrailingCoeffAt (· - i) w ^ (-divisor f S₀R) i)
      • meromorphicTrailingCoeffAt (((∏ᶠ (u : ℂ), canonicalFactor R u ^ (-(divisor f B₀R) u))
        * ∏ᶠ (v : ℂ), (· - v) ^ (divisor f S₀R) v) • h) w := by
      rw [meromorphicTrailingCoeffAt_congr_nhdsNE
        ((D.meromorphicOn w hw).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
        (by fun_prop) hw ?η₁ D.eventuallyEq)]
      case η₁ =>
        rw [← closure_ball _ hR.ne']
        exact isOpen_ball.perfect_closure.2
    _ = ((∏ i ∈ t₂, meromorphicTrailingCoeffAt (canonicalFactor R i) w ^ (divisor f B₀R) i)
      * ∏ i ∈ t₁, meromorphicTrailingCoeffAt (· - i) w ^ (-divisor f S₀R) i)
      • meromorphicTrailingCoeffAt (((∏ i ∈ t₂, canonicalFactor R i ^ (-(divisor f B₀R) i))
        * ∏ i ∈ t₁, (· - i) ^ (divisor f S₀R) i) • h) w := by
      rw [finprod_eq_prod_of_mulSupport_subset (s := t₂) _ _,
        finprod_eq_prod_of_mulSupport_subset (s := t₁) _ _,
        finprod_eq_prod_of_mulSupport_subset (s := t₂) _ _,
        finprod_eq_prod_of_mulSupport_subset (s := t₁) _ _]
      <;> simpa [ht₁, ht₂] using mulSupport_pow_subset_support ..
    _ = ((∏ i ∈ t₂, meromorphicTrailingCoeffAt (canonicalFactor R i) w ^ (divisor f B₀R) i)
      * ∏ i ∈ t₁, meromorphicTrailingCoeffAt (· - i) w ^ (-divisor f S₀R) i)
      • ((∏ n ∈ t₂, meromorphicTrailingCoeffAt (canonicalFactor R n ^ (-(divisor f B₀R) n)) w)
        * ∏ n ∈ t₁, meromorphicTrailingCoeffAt ((· - n) ^ (divisor f S₀R) n) w)
      • h w := by
      rw [MeromorphicAt.meromorphicTrailingCoeffAt_smul (by fun_prop)
        (D.analyticOnNhd w hw).meromorphicAt,
        MeromorphicAt.meromorphicTrailingCoeffAt_mul (by fun_prop) (by fun_prop),
        meromorphicTrailingCoeffAt_prod (by fun_prop),
        meromorphicTrailingCoeffAt_prod (by fun_prop),
        (D.analyticOnNhd w hw).meromorphicTrailingCoeffAt_of_ne_zero (D.ne_zero w hw)]
    _ = h w := by
      rw [smul_smul, mul_mul_mul_comm, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
        Finset.prod_eq_one ?η₁, Finset.prod_eq_one ?η₂, mul_one, one_smul]
      case η₁ =>
        intro x hx
        rw [MeromorphicAt.meromorphicTrailingCoeffAt_zpow (by fun_prop), ← zpow_add₀,
          add_neg_cancel, zpow_zero]
        apply MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero (by fun_prop)
          (meromorphicOrderAt_canonicalFactor_ne_top x hR)
      case η₂ =>
        intro x hx
        rw [MeromorphicAt.meromorphicTrailingCoeffAt_zpow (by fun_prop), ← zpow_add₀,
          locallyFinsuppWithin.coe_neg, Pi.neg_apply, neg_add_cancel, zpow_zero]
        rw [meromorphicTrailingCoeffAt_id_sub_const]
        grind

/--
Companion lemma to `MeromorphicOn.exists_ecanonicalDecomp`: In the setting of the extended canonical
decomposition, write the function `h` entirely in terms of `f`, under the assumption that `f` has
order zero.
-/
/-
**Complex.ECanonicalDecomp.eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrde
rAt** 是 Mathlib 中的一个定理，位于命名空间 `Complex.ECanonicalDecomp`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] 
{R : ℝ} {w : ℂ} {f h : ℂ → E},   Complex.ECanonicalDecomp f h R →     w ∈ Metric
.closedBall 0 R →       meromorphicOrderAt f w = 0 →         0 < R →           h
 w =             ((∏ᶠ (i : ℂ), Complex.canonicalFactor R i w ^ (MeromorphicOn.di
visor f (Metric.ball 0 R)) i) *                 ∏ᶠ (i : ℂ), (w - i) ^ (-Meromorp
hicOn.divisor f (Metric.sphere 0 R)) i) •               meromorphicTrailingCoeff
At f w
参数：(∏ᶠ (i : ℂ), Complex.canonicalFactor R i w ^ (MeromorphicOn.divisor f (Metric
.ball 0 R)) i) *                 ∏ᶠ (i : ℂ), (w - i) ^ (-MeromorphicOn.divisor f
 (Metric.sphere 0 R)) i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.ECanonicalDecomp.eq_smul_meromorphicTrailingCoeffAt`：∀ {E : Type
 u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] {R : ℝ} {w : ℂ} {
f h : ℂ → E},   Complex.ECanonicalDecomp f h R → …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Function.locallyFinsuppWithin.supportWithinDomain`：supportWithinDomain [
Zero Y] (D : locallyFinsuppWithin U Y) : D.support subseteq U
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeromorphicOn.divisor_apply`：divisor_apply {f : 𝕜 -> E} (hf : Meromorphi
cOn f U) (hz : z in U) : divisor f U z = (meromorphicOrderAt f z).untop₀
· 使用引理 `MeromorphicOn.mono_set`：mono_set {V : Set 𝕜} (hv : V subseteq U) : Merom
orphicOn f V
· 使用定理 `Complex.ECanonicalDecomp.meromorphicOn`：∀ {E : Type u_1} [inst : NormedA
ddCommGroup E] [inst_1 : NormedSpace ℂ E] {f g : ℂ → E} {R : ℝ},   Complex.ECano
nicalDecomp f g R → Meromorp…
· 使用定理 `Metric.ball_subset_closedBall`：ball_subset_closedBall : ball x ε subsete
q closedBall x ε
· 使用引理 `WithTop.untop₀_zero`：untop₀_zero : untop₀ 0 = (0 : α)
· 使用引理 `AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero`：AnalyticAt.meromorphic
TrailingCoeffAt_of_ne_zero (h₁ : AnalyticAt 𝕜 f x) (h₂ : f x != 0) : meromorphic
TrailingCoeffAt f x = f x
· 使用定理 `Complex.analyticOnNhd_canonicalFactor`：analyticOnNhd_canonicalFactor : A
nalyticOnNhd Complex (canonicalFactor R w) {w}ᶜ
· 使用定理 `Complex.canonicalFactor_ne_zero`：canonicalFactor_ne_zero {z : Complex} (
hw : w in ball 0 R) (h₁z : z in closedBall 0 R) (h₂z : z != w) : canonicalFactor
 R w z != 0
· 使用定理 `meromorphicTrailingCoeffAt_id_sub_const`：meromorphicTrailingCoeffAt_id_s
ub_const [DecidableEq 𝕜] {x y : 𝕜} : meromorphicTrailingCoeffAt (· - y) x = if x
 = y then 1 else x - y
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0

--- 原说明 ---
Companion lemma to `MeromorphicOn.exists_ecanonicalDecomp`: In the setting of th
e extended canonical
decomposition, write the function `h` entirely in terms of `f`, under the assump
tion that `f` has
order zero.
-/
lemma ECanonicalDecomp.eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrderAt
    {f h : ℂ → E} (D : ECanonicalDecomp f h R) (h₁w : w ∈ closedBall 0 R)
    (h₂w : meromorphicOrderAt f w = 0) (hR : 0 < R) :
    h w = ((∏ᶠ i, (canonicalFactor R i w) ^ (divisor f (ball 0 R) i))
          * (∏ᶠ i, (w - i) ^ (-divisor f (sphere 0 R)) i))
          • meromorphicTrailingCoeffAt f w := by
  rw [D.eq_smul_meromorphicTrailingCoeffAt h₁w hR]
  congr! 4 with x x
  · by_cases h₃x : (divisor f (ball 0 R)) x = 0
    · simp [h₃x]
    have h₁x : x ∈ ball 0 R := (divisor f (ball 0 R)).supportWithinDomain h₃x
    have h₂x : w ≠ x := by
      rintro rfl
      exact h₃x (by simp [(D.meromorphicOn.mono_set ball_subset_closedBall).divisor_apply h₁x, h₂w])
    rw [AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero
      (Complex.analyticOnNhd_canonicalFactor R x w h₂x)
      (Complex.canonicalFactor_ne_zero h₁x h₁w h₂x)]
  · by_cases h : x = w
    · simp_all [meromorphicTrailingCoeffAt_id_sub_const, divisor_def]
    grind [meromorphicTrailingCoeffAt_id_sub_const]

/--
Companion lemma to `MeromorphicOn.exists_ecanonicalDecomp`: In the setting of the extended canonical
decomposition, write the function `log ‖h‖` entirely in terms of `f`, under the assumption that `f`
has order zero.
-/
/-
**Complex.ECanonicalDecomp.log_norm_eq** 是 Mathlib 中的一个定理，位于命名空间 `Complex.ECanon
icalDecomp`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] 
{R : ℝ} {w : ℂ} {f h : ℂ → E},   Complex.ECanonicalDecomp f h R →     w ∈ Metric
.closedBall 0 R →       meromorphicOrderAt f w = 0 →         0 < R →           R
eal.log ‖h w‖ =             ∑ᶠ (i : ℂ), ↑((MeromorphicOn.divisor f (Metric.ball 
0 R)) i) * Real.log ‖Complex.canonicalFactor R i w‖ -                 ∑ᶠ (i : ℂ)
, ↑((MeromorphicOn.divisor f (Metric.sphere 0 R)) i) * Real.log ‖w - i‖ +       
        Real.log ‖meromorphicTrailingCoeffAt f w‖
参数：i : ℂ；(MeromorphicOn.divisor f (Metric.ball 0 R)) i；i : ℂ；(MeromorphicOn.divi
sor f (Metric.sphere 0 R)) i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `divisor_sphere_support_finite`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] [ProperSpace…
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用引理 `MeromorphicOn.divisor_ball_support_finite`：divisor_ball_support_finite [
ProperSpace 𝕜] {f : 𝕜 -> E} {R : Real} {c : 𝕜} (hf : MeromorphicOn f (closedBall
 c R)) : (divisor f (ball c R))…
· 使用定理 `Complex.ECanonicalDecomp.meromorphicOn`：∀ {E : Type u_1} [inst : NormedA
ddCommGroup E] [inst_1 : NormedSpace ℂ E] {f g : ℂ → E} {R : ℝ},   Complex.ECano
nicalDecomp f g R → Meromorp…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.ECanonicalDecomp.eq_smul_meromorphicTrailingCoeffAt_of_meromorph
icOrderAt`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace 
ℂ E] {R : ℝ} {w : ℂ} {f h : ℂ → E},   Complex.ECanonicalDecomp f h R → …
· 使用定理 `finprod_eq_prod_of_mulSupport_subset`：finprod_eq_prod_of_mulSupport_subs
et (f : α -> M) {s : Finset α} (h : mulSupport f subseteq s) : ∏ᶠ i, f i = ∏ i i
n s, f i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `_private.Mathlib.Analysis.Complex.CanonicalDecomposition.0.Complex.mulSu
pport_pow_subset_support`：∀ {α : Type u_2} {β : Type u_3} [inst : DivInvMonoid α
] (f : β → α) (g : β → ℤ),   (Function.mulSupport fun x => f x ^ g x) ⊆ Function
.suppo…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `Function.mulSupport_fun_inv`：mulSupport_fun_inv : (mulSupport fun x => (
f x)⁻¹) = mulSupport f
· 使用定理 `zpow_ne_zero`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀} (n : 
ℤ), a ≠ 0 → a ^ n ≠ 0
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用引理 `WithTop.untop₀_zero`：untop₀_zero : untop₀ 0 = (0 : α)
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
（共 59 条，此处仅展示前 30 条）

--- 原说明 ---
Companion lemma to `MeromorphicOn.exists_ecanonicalDecomp`: In the setting of th
e extended canonical
decomposition, write the function `log ‖h‖` entirely in terms of `f`, under the 
assumption that `f`
has order zero.
-/
lemma ECanonicalDecomp.log_norm_eq
    {f h : ℂ → E} (D : ECanonicalDecomp f h R) (h₁w : w ∈ closedBall 0 R)
    (h₂w : meromorphicOrderAt f w = 0)
    (hR : 0 < R) :
    Real.log ‖h w‖ = ((∑ᶠ i, (divisor f (ball 0 R) i) * Real.log ‖canonicalFactor R i w‖)
          - (∑ᶠ i, (divisor f (sphere 0 R) i) * Real.log ‖w - i‖))
          + Real.log ‖meromorphicTrailingCoeffAt f w‖ := by
  -- Finiteness properties and side results used throughout the proof
  let B₀R := ball (0 : ℂ) R
  let S₀R := sphere (0 : ℂ) R
  lift (divisor f S₀R).support to Finset ℂ using divisor_sphere_support_finite with t₁ ht₁
  lift (divisor f B₀R).support to Finset ℂ using D.meromorphicOn.divisor_ball_support_finite
    with t₂ ht₂
  calc Real.log ‖h w‖
    _ = log ‖((∏ᶠ (i : ℂ), canonicalFactor R i w ^ (divisor f B₀R) i)
        * ∏ᶠ (i : ℂ), (w - i) ^ (-divisor f S₀R) i) • meromorphicTrailingCoeffAt f w‖ := by
      rw [D.eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrderAt
        h₁w h₂w hR, finprod_eq_prod_of_mulSupport_subset (s := t₂) _ (by aesop)]
    _ = log ‖((∏ i ∈ t₂, canonicalFactor R i w ^ (divisor f B₀R) i)
        * ∏ i ∈ t₁, (w - i) ^ (-divisor f S₀R) i) • meromorphicTrailingCoeffAt f w‖ := by
      rw [finprod_eq_prod_of_mulSupport_subset (s := t₂) _ _,
        finprod_eq_prod_of_mulSupport_subset (s := t₁) _ _]
      <;> simpa [ht₁, ht₂] using mulSupport_pow_subset_support ..
    _ =  ∑ i ∈ t₂, log (‖canonicalFactor R i w‖ ^ (divisor f B₀R) i)
        + ∑ i ∈ t₁, log (‖w - i‖ ^ (-divisor f S₀R) i) + log ‖meromorphicTrailingCoeffAt f w‖ := by
      have η₀ (x) (hx : x ∈ t₁) : ‖w - x‖ ^ (-divisor f S₀R) x ≠ 0 := by
        refine zpow_ne_zero _ ?_
        rw [norm_ne_zero_iff, sub_ne_zero]
        rintro rfl
        simp_all [divisor_def, ← Finset.mem_coe]
      have η₁ (x) (hx : x ∈ t₂) : ‖canonicalFactor R x w‖ ^ (divisor f B₀R) x ≠ 0 := by
        refine zpow_ne_zero _ ?_
        rw [norm_ne_zero_iff]
        have h₁x : x ∈ ball 0 R := (divisor f B₀R).supportWithinDomain (ht₂ ▸ hx)
        refine canonicalFactor_ne_zero h₁x h₁w fun _ ↦ ?_
        simp_all [divisor_def, ← Finset.mem_coe]
      simp_rw [norm_smul, norm_mul, norm_prod, norm_zpow]
      rw [Real.log_mul (mul_ne_zero_iff.2 ⟨Finset.prod_ne_zero_iff.2 η₁,
          Finset.prod_ne_zero_iff.2 η₀⟩) ?_, Real.log_mul (Finset.prod_ne_zero_iff.2 η₁)
        (Finset.prod_ne_zero_iff.2 η₀), Real.log_prod η₁, Real.log_prod η₀]
      simpa using (D.meromorphicOn w h₁w).meromorphicTrailingCoeffAt_ne_zero (by simp [h₂w])
    _ = ((∑ᶠ i, (divisor f B₀R i) * Real.log ‖canonicalFactor R i w‖)
        - (∑ᶠ i, (divisor f S₀R i) * Real.log ‖w - i‖))
        + Real.log ‖meromorphicTrailingCoeffAt f w‖ := by
      rw [finsum_eq_sum_of_support_subset (s := t₂) _ ?η₀,
        finsum_eq_sum_of_support_subset (s := t₁) _ ?η₁]
      case η₀ | η₁ => intro _ _; simp_all [S₀R, B₀R]
      rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr! 3 with i hi i hi <;> simp

end Complex

