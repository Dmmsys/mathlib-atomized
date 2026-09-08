/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.MeasureTheory.Integral.IntervalAverage

/-!
# Circle Averages

For a function `f` on the complex plane, this file introduces the definition
`Real.circleAverage f c R` as a shorthand for the average of `f` on the circle with center `c` and
radius `R`, equipped with the rotation-invariant measure of total volume one. Like
`IntervalAverage`, this notion exists as a convenience. It avoids notationally inconvenient
compositions of `f` with `circleMap` and avoids the need to manually eliminate `2 * π` every time
an average is computed.

Note: Like the interval average defined in `Mathlib/MeasureTheory/Integral/IntervalAverage.lean`,
the `circleAverage` defined here is a purely measure-theoretic average. It should not be confused
with `circleIntegral`, which is the path integral over the circle path. The relevant integrability
property `circleAverage` is `CircleIntegrable`, as defined in
`Mathlib/MeasureTheory/Integral/CircleIntegral.lean`.

Implementation Note: Like `circleMap`, `circleAverage`s are defined for negative radii. The theorem
`circleAverage_congr_negRadius` shows that the average is independent of the radius' sign.
-/

@[expose] public section

open Complex Filter Metric Real Set Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {𝕜 : Type*} [NormedDivisionRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E] [SMulCommClass ℝ 𝕜 E]
  {f f₁ f₂ : ℂ → E} {c : ℂ} {R : ℝ} {a : 𝕜}

namespace Real

/-!
### Definition
-/

variable (f c R) in
/--
Define `circleAverage f c R` as the average value of `f` on the circle with center `c` and radius
`R`. This is a real notion, which should not be confused with the complex path integral notion
defined in `circleIntegral` (integrating with respect to `dz`).
-/
/-
**Real.circleAverage** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：circleAverage : E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define `circleAverage f c R` as the average value of `f` on the circle with cent
er `c` and radius
`R`. This is a real notion, which should not be confused with the complex path i
ntegral notion
defined in `circleIntegral` (integrating with respect to `dz`).
-/
noncomputable def circleAverage : E :=
  (2 * π)⁻¹ • ∫ θ in 0..2 * π, f (circleMap c R θ)
/-
**Real.circleAverage_def** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：circleAverage_def : circleAverage f c R = (2 * π)⁻¹ • ∫ θ in 0..2 * π, f (
circleMap c R θ)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma circleAverage_def :
    circleAverage f c R = (2 * π)⁻¹ • ∫ θ in 0..2 * π, f (circleMap c R θ) := rfl

/--
If 'f' is *not* circle integrable, then the circle average is zero by definition.
-/
/-
**Real.circleAverage.integral_undef** 是 Mathlib 中的一个定理，位于命名空间 `Real.circleAverag
e`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
{f : ℂ → E} {c : ℂ} {R : ℝ},   ¬CircleIntegrable f c R → Real.circleAverage f c 
R = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `intervalIntegral.integral_undef`：∀ {E : Type u_5} [inst : NormedAddCommG
roup E] [inst_1 : NormedSpace ℝ E] {a b : ℝ} {f : ℝ → E}   {μ : MeasureTheory.Me
asure ℝ}, ¬IntervalIn…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If 'f' is *not* circle integrable, then the circle average is zero by definition
.
-/
theorem circleAverage.integral_undef (hf : ¬CircleIntegrable f c R) :
    circleAverage f c R = 0 := by
  simp_all [circleAverage, CircleIntegrable, intervalIntegral.integral_undef]

/-- Expression of `circleAverage` in terms of interval averages. -/
/-
**Real.circleAverage_eq_intervalAverage** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：circleAverage_eq_intervalAverage : circleAverage f c R = ⨍ θ in 0..2 * π, 
f (circleMap c R θ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `interval_average_eq`：interval_average_eq (f : Real -> E) (a b : Real) : 
(⨍ x in a..b, f x) = (b - a)⁻¹ • ∫ x in a..b, f x
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Expression of `circleAverage` in terms of interval averages.
-/
lemma circleAverage_eq_intervalAverage :
    circleAverage f c R = ⨍ θ in 0..2 * π, f (circleMap c R θ) := by
  simp [circleAverage, interval_average_eq]

/-- Interval averages for zero radii equal values at the center point. -/
/-
**Real.circleAverage_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
{f : ℂ → E} {c : ℂ} [CompleteSpace E],   Real.circleAverage f c 0 = f c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.circleAverage.eq_1`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] 
[inst_1 : NormedSpace ℝ E] (f : ℂ → E) (c : ℂ) (R : ℝ),   Real.circleAverage f c
 R = (2 * Rea…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `circleMap_zero_radius`：circleMap_zero_radius (c : Complex) : circleMap c
 0 = const Real c
· 使用定理 `intervalIntegral.integral_const`：integral_const [CompleteSpace E] (c : E
) : ∫ _ in a..b, c = (b - a) • c
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Real.pi_ne_zero`：pi_ne_zero : π != 0
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Interval averages for zero radii equal values at the center point.
-/
@[simp] lemma circleAverage_zero [CompleteSpace E] :
    circleAverage f c 0 = f c := by
  rw [circleAverage]
  simp only [circleMap_zero_radius, Function.const_apply,
    intervalIntegral.integral_const, sub_zero,
    ← smul_assoc, smul_eq_mul, inv_mul_cancel₀ (mul_ne_zero two_ne_zero pi_ne_zero),
    one_smul]

/--
Expression of `circleAverage` with arbitrary center in terms of `circleAverage` with center zero.
-/
/-
**Real.circleAverage_map_add_const** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：circleAverage_map_add_const : circleAverage (fun z => f (z + c)) 0 R = cir
cleAverage f c R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c

--- 原说明 ---
Expression of `circleAverage` with arbitrary center in terms of `circleAverage` 
with center zero.
-/
lemma circleAverage_map_add_const :
    circleAverage (fun z ↦ f (z + c)) 0 R = circleAverage f c R := by
  unfold circleAverage circleMap
  congr
  ext θ
  simp only [zero_add]
  congr 1
  ring

/--
Expression of the `circleAverage` in terms of a `circleIntegral`.
-/
/-
**Real.circleAverage_eq_circleIntegral** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：circleAverage_eq_circleIntegral {F : Type*} [NormedAddCommGroup F] [Normed
Space Complex F] {f : Complex -> F} (h : R != 0) : circleAverage f c R = (2 * π 
* I)⁻¹ • (∮ z in C(c, R), (z - c)⁻¹ • f z)
参数：h : R != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `intervalIntegral.integral_smul`：∀ {𝕜 : Type u_2} {E : Type u_5} [inst : 
NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {a b : ℝ}   {μ : MeasureTheory.
Measure ℝ} [inst_2 :…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
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
（共 63 条，此处仅展示前 30 条）

--- 原说明 ---
Expression of the `circleAverage` in terms of a `circleIntegral`.
-/
theorem circleAverage_eq_circleIntegral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : ℂ → F} (h : R ≠ 0) :
    circleAverage f c R = (2 * π * I)⁻¹ • (∮ z in C(c, R), (z - c)⁻¹ • f z) := by
  calc circleAverage f c R
  _ = (↑(2 * π) : ℂ)⁻¹ • ∫ θ in 0..2 * π, f (circleMap c R θ) := by
    simp [circleAverage, ← coe_smul]
  _ = (2 * π * I)⁻¹ • ∫ θ in 0..2 * π, I • f (circleMap c R θ) := by
    rw [intervalIntegral.integral_smul, mul_inv_rev, smul_smul]
    match_scalars
    field
  _ = (2 * π * I)⁻¹ • (∮ z in C(c, R), (z - c)⁻¹ • f z) := by
    unfold circleIntegral
    congr with θ
    simp [deriv_circleMap, circleMap_sub_center, smul_smul]
    field_simp [circleMap_ne_center h]

/-!
## Congruence Lemmata
-/

/-- Circle averages do not change when shifting the angle. -/
/-
**Real.circleAverage_eq_integral_add** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：circleAverage_eq_integral_add (η : Real) : circleAverage f c R = (2 * π)⁻¹
 • ∫ θ in 0..2 * π, f (circleMap c R (θ + η))
参数：η : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_comp_add_right`：integral_comp_add_right (d) : 
(∫ x in a..b, f (x + d)) = ∫ x in a + d..b + d, f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `periodic_circleMap`：periodic_circleMap (c : Complex) (R : Real) : Period
ic (circleMap c R) (2 * π)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.Periodic.intervalIntegral_add_eq`：intervalIntegral_add_eq (hf :
 Periodic f T) (t s : Real) : ∫ x in t..t + T, f x = ∫ x in s..s + T, f x
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a

--- 原说明 ---
Circle averages do not change when shifting the angle.
-/
lemma circleAverage_eq_integral_add (η : ℝ) :
    circleAverage f c R = (2 * π)⁻¹ • ∫ θ in 0..2 * π, f (circleMap c R (θ + η)) := by
  rw [intervalIntegral.integral_comp_add_right (fun θ ↦ f (circleMap c R θ))]
  have t₀ : (fun θ ↦ f (circleMap c R θ)).Periodic (2 * π) :=
    fun x ↦ by simp [periodic_circleMap c R x]
  have := t₀.intervalIntegral_add_eq 0 η
  rw [zero_add, add_comm] at this
  rw [zero_add]
  simp only [circleAverage, mul_inv_rev]
  congr

/-- Circle averages do not change when replacing the radius by its negative. -/
/-
**Real.circleAverage_neg_radius** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
{f : ℂ → E} {c : ℂ} {R : ℝ},   Real.circleAverage f c (-R) = Real.circleAverage 
f c R
参数：-R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `circleMap_neg_radius`：circleMap_neg_radius {r x : Real} {c : Complex} : 
circleMap c (-r) x = circleMap c r (x + π)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Real.circleAverage_eq_integral_add`：circleAverage_eq_integral_add (η : R
eal) : circleAverage f c R = (2 * π)⁻¹ • ∫ θ in 0..2 * π, f (circleMap c R (θ + 
η))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Circle averages do not change when replacing the radius by its negative.
-/
@[simp] theorem circleAverage_neg_radius :
    circleAverage f c (-R) = circleAverage f c R := by
  unfold circleAverage
  simp_rw [circleMap_neg_radius, ← circleAverage_def, circleAverage_eq_integral_add π]

/-- Circle averages do not change when replacing the radius by its absolute value. -/
/-
**Real.circleAverage_abs_radius** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
{f : ℂ → E} {c : ℂ} {R : ℝ},   Real.circleAverage f c |R| = Real.circleAverage f
 c R
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `abs_of_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], a < 0 → |a| = -a
· 使用定理 `Real.circleAverage_neg_radius`：∀ {E : Type u_1} [inst : NormedAddCommGro
up E] [inst_1 : NormedSpace ℝ E] {f : ℂ → E} {c : ℂ} {R : ℝ},   Real.circleAvera
ge f c (-R) = Real.…

--- 原说明 ---
Circle averages do not change when replacing the radius by its absolute value.
-/
@[simp] theorem circleAverage_abs_radius :
    circleAverage f c |R| = circleAverage f c R := by
  by_cases! hR : 0 ≤ R
  · rw [abs_of_nonneg hR]
  · rw [abs_of_neg hR, circleAverage_neg_radius]

/-- If two functions agree outside of a discrete set in the circle, then their averages agree. -/
/-
**Real.circleAverage_congr_codiscreteWithin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：circleAverage_congr_codiscreteWithin (hf : f₁ =ᶠ[codiscreteWithin (sphere 
c |R|)] f₂) (hR : R != 0) : circleAverage f₁ c R = circleAverage f₂ c R
参数：hf : f₁ =ᶠ[codiscreteWithin (sphere c |R|)] f₂；hR : R != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.integral_congr_ae_restrict`：integral_congr_ae_restrict 
{a b : Real} {f g : Real -> E} {μ : Measure Real} (h : f =ᵐ[μ.restrict (Ι a b)] 
g) : ∫ x in a..b, f x ∂μ = ∫ x in…
· 使用定理 `ae_restrict_le_codiscreteWithin`：ae_restrict_le_codiscreteWithin {α : Ty
pe*} [MeasurableSpace α] [TopologicalSpace α] [SecondCountableTopology α] {μ : M
easure α} [NullSingle…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `measurableSet_uIoc`：measurableSet_uIoc [ClosedIicTopology α] : Measurabl
eSet (uIoc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用引理 `Filter.codiscreteWithin_mono`：Filter.codiscreteWithin_mono {U₁ U : Set X
} (hU : U₁ subseteq U) : codiscreteWithin U₁ <= codiscreteWithin U
· 使用定理 `trivial`：True
· 使用定理 `circleMap_preimage_codiscrete`：circleMap_preimage_codiscrete {c : Comple
x} {R : Real} (hR : R != 0) : map (circleMap c R) (codiscrete Real) <= codiscret
eWithin (sphere c |…

--- 原说明 ---
If two functions agree outside of a discrete set in the circle, then their avera
ges agree.
-/
theorem circleAverage_congr_codiscreteWithin
    (hf : f₁ =ᶠ[codiscreteWithin (sphere c |R|)] f₂) (hR : R ≠ 0) :
    circleAverage f₁ c R = circleAverage f₂ c R := by
  unfold circleAverage
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  apply ae_restrict_le_codiscreteWithin measurableSet_uIoc
  apply codiscreteWithin_mono (by tauto) (circleMap_preimage_codiscrete hR hf)

/-- If two functions agree on the circle, then their circle averages agree. -/
/-
**Real.circleAverage_congr_sphere** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：circleAverage_congr_sphere {f₁ f₂ : Complex -> E} (hf : Set.EqOn f₁ f₂ (sp
here c |R|)) : circleAverage f₁ c R = circleAverage f₂ c R
参数：hf : Set.EqOn f₁ f₂ (sphere c |R|)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.integral_congr`：integral_congr {a b : Real} (h : EqOn f
 g [[a, b]]) : ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `circleMap_mem_sphere'`：circleMap_mem_sphere' (c : Complex) (R : Real) (θ
 : Real) : circleMap c R θ in sphere c |R|
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
If two functions agree on the circle, then their circle averages agree.
-/
theorem circleAverage_congr_sphere {f₁ f₂ : ℂ → E} (hf : Set.EqOn f₁ f₂ (sphere c |R|)) :
    circleAverage f₁ c R = circleAverage f₂ c R := by
  unfold circleAverage
  congr 1
  exact intervalIntegral.integral_congr (fun x ↦ by simp [hf (circleMap_mem_sphere' c R x)])

/--
Express the circle average over an arbitrary circle as a circle average over the unit circle.
-/
/-
**Real.circleAverage_eq_circleAverage_zero_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：circleAverage_eq_circleAverage_zero_one : circleAverage f c R = (circleAve
rage (fun z => f (R * z + c)) 0 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.RingNF.add_assoc_rev`：add_assoc_rev (a b c : R) : a + (b 
+ c) = a + b + c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.RingNF.nat_rawCast_1`：nat_rawCast_1 : (Nat.rawCast 1 : R)
 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.RingNF.mul_assoc_rev`：mul_assoc_rev (a b c : R) : a * (b 
* c) = a * b * c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
Express the circle average over an arbitrary circle as a circle average over the
 unit circle.
-/
theorem circleAverage_eq_circleAverage_zero_one :
    circleAverage f c R = (circleAverage (fun z ↦ f (R * z + c)) 0 1) := by
  unfold circleAverage circleMap
  congr with θ
  ring_nf
  simp

/--
The circle average of a function `f` on the unit sphere equals the circle average of the function
`z ↦ f z⁻¹`.
-/
@[simp]
/-
**Real.circleAverage_zero_one_congr_inv** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：circleAverage_zero_one_congr_inv {f : Complex -> E} : circleAverage (f ·⁻¹
) 0 1 = circleAverage f 0 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `circleMap_zero_inv`：circleMap_zero_inv (R θ : Real) : (circleMap 0 R θ)⁻
¹ = circleMap 0 R⁻¹ (-θ)
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `intervalIntegral.integral_comp_neg`：integral_comp_neg : (∫ x in a..b, f 
(-x)) = ∫ x in -b..-a, f x
· 使用定理 `periodic_circleMap`：periodic_circleMap (c : Complex) (R : Real) : Period
ic (circleMap c R) (2 * π)
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Function.Periodic.intervalIntegral_add_eq`：intervalIntegral_add_eq (hf :
 Periodic f T) (t s : Real) : ∫ x in t..t + T, f x = ∫ x in s..s + T, f x

--- 原说明 ---
The circle average of a function `f` on the unit sphere equals the circle averag
e of the function
`z ↦ f z⁻¹`.
-/
theorem circleAverage_zero_one_congr_inv {f : ℂ → E} :
    circleAverage (f ·⁻¹) 0 1 = circleAverage f 0 1 := by
  unfold circleAverage
  congr 1
  calc ∫ θ in 0..2 * π, f (circleMap 0 1 θ)⁻¹
  _ = ∫ θ in 0..2 * π, f (circleMap 0 1 (-θ)) := by
    simp [circleMap_zero_inv]
  _ = ∫ θ in 0..2 * π, f (circleMap 0 1 θ) := by
    rw [intervalIntegral.integral_comp_neg (fun w ↦ f (circleMap 0 1 w))]
    have t₀ : Function.Periodic (fun w ↦ f (circleMap 0 1 w)) (2 * π) :=
      fun x ↦ by simp [periodic_circleMap 0 1 x]
    simpa using (t₀.intervalIntegral_add_eq (-(2 * π)) 0)

/-!
## Continuity
-/

/--
The circleMap for a fixed center is continuous as a function on `ℝ × ℝ`.
-/
/-
**Real.circleMap.continuous** 是 Mathlib 中的一个定理，位于命名空间 `Real.circleMap`。
形式化陈述：∀ {c : ℂ}, Continuous fun x => circleMap c x.1 x.2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.const_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.cexp`：Continuous.cexp (h : Continuous f) : Continuous fun y =
> exp (f y)
· 使用定理 `Continuous.mul_const`：Continuous.mul_const (hf : Continuous f) (b : M) :
 Continuous (f · * b)
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2

--- 原说明 ---
The circleMap for a fixed center is continuous as a function on `ℝ × ℝ`.
-/
@[fun_prop] lemma circleMap.continuous {c : ℂ} :
    Continuous (fun (x : ℝ × ℝ) ↦ circleMap c x.1 x.2) := by
  fun_prop [circleMap]

/--
The circle average of a continuous function is itself continuous, as a function
of the radius.
-/
/-
**Real.ContinuousOn.circleAverage** 是 Mathlib 中的一个定理，位于命名空间 `Real.ContinuousOn`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
{f : ℂ → E} {s : Set ℝ} {c : ℂ},   ContinuousOn f {z | ‖z - c‖ ∈ s} → (∀ r ∈ s, 
0 ≤ r) → ContinuousOn (Real.circleAverage f c) s
参数：∀ r ∈ s, 0 ≤ r；Real.circleAverage f c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `Continuous.const_smul`：Continuous.const_smul (hg : Continuous g) (c : M)
 : Continuous (c • g)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`：
continuous_parametric_intervalIntegral_of_continuous' (hf : Continuous f.uncurry
) (a₀ b₀ : Real) : Continuous fun x => ∫ t in a₀..b₀, f x t …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `circleMap_sub_center`：circleMap_sub_center (c : Complex) (R : Real) (θ :
 Real) : circleMap c R θ - c = circleMap 0 R θ
· 使用定理 `norm_circleMap_zero`：norm_circleMap_zero (R : Real) (θ : Real) : ‖circle
Map 0 R θ‖ = |R|
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Subtype.coe_prop`：coe_prop {S : Set α} (a : { a // a in S }) : ↑a in S
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Real.circleMap.continuous`：∀ {c : ℂ}, Continuous fun x => circleMap c x.
1 x.2
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2

--- 原说明 ---
The circle average of a continuous function is itself continuous, as a function
of the radius.
-/
theorem ContinuousOn.circleAverage {f : ℂ → E} {s : Set ℝ} {c : ℂ}
    (hf : ContinuousOn f {z : ℂ | ‖z - c‖ ∈ s})
    (hs : ∀ r ∈ s, 0 ≤ r) :
    ContinuousOn (circleAverage f c) s := by
  rw [continuousOn_iff_continuous_domRestrict] at *
  apply (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' _ _ _).const_smul
  have (x : s × ℝ) : circleMap c x.1 x.2 ∈ {z | ‖z - c‖ ∈ s} := by
    simp [abs_of_nonneg (hs x.1 (Subtype.coe_prop x.1))]
  apply hf.comp (f := (fun x ↦ ⟨circleMap c x.1 x.2, this x⟩))
  fun_prop

/--
The circle average of a continuous function is itself continuous, as a function
of the radius.
-/
/-
**Real.Continuous.circleAverage** 是 Mathlib 中的一个定理，位于命名空间 `Real.Continuous`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
{c : ℂ} {f : ℂ → E},   Continuous f → Continuous (Real.circleAverage f c)
参数：Real.circleAverage f c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.const_smul`：Continuous.const_smul (hg : Continuous g) (c : M)
 : Continuous (c • g)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`：
continuous_parametric_intervalIntegral_of_continuous' (hf : Continuous f.uncurry
) (a₀ b₀ : Real) : Continuous fun x => ∫ t in a₀..b₀, f x t …
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Real.circleMap.continuous`：∀ {c : ℂ}, Continuous fun x => circleMap c x.
1 x.2

--- 原说明 ---
The circle average of a continuous function is itself continuous, as a function
of the radius.
-/
@[fun_prop] theorem Continuous.circleAverage {f : ℂ → E} (hf : Continuous f) :
    Continuous (Real.circleAverage f c) := by
  apply (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' _ _ _).const_smul
  fun_prop

/--
Companion lemma to `ContinuousOn.circleAverage`: a function continuous on `Ioc r
R` and constant on `Ioo r R` is constant.
-/
/-
**Real.ContinuousOn.eq_of_eqOn_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Real.ContinuousOn`
。
形式化陈述：∀ {f : ℝ → ℝ} {c r R : ℝ}, ContinuousOn f (Set.Ioc r R) → r < R → Set.EqOn
 f (fun x => c) (Set.Ioo r R) → f R = c
参数：Set.Ioc r R；fun x => c；Set.Ioo r R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Ioc b a ↔ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_le_iff`：nhdsWithin_le_iff {s t : Set α} {x : α} : 𝓝[s] x <= 𝓝
[t] x ↔ t in 𝓝[s] x
· 使用定理 `mem_nhdsLT_iff_exists_Ioo_subset`：mem_nhdsLT_iff_exists_Ioo_subset [NoMi
nOrder α] {a : α} {s : Set α} : s in 𝓝[<] a ↔ exists l in Iio a, Ioo l a subsete
q s
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
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
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.eventuallyEq_of_mem`：eventuallyEq_of_mem {l : Filter α} {f g : α 
-> β} {s : Set α} (hs : s in l) (h : EqOn f g s) : f =ᶠ[l] g
· 使用定理 `Ioo_mem_nhdsLT`：Ioo_mem_nhdsLT (H : a < b) : Ioo a b in 𝓝[<] b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)

--- 原说明 ---
Companion lemma to `ContinuousOn.circleAverage`: a function continuous on `Ioc r
R` and constant on `Ioo r R` is constant.
-/
lemma ContinuousOn.eq_of_eqOn_Ioo {f : ℝ → ℝ} {c r R : ℝ}
    (h₁f : ContinuousOn f (Ioc r R)) (hR : r < R)
    (h₂f : EqOn f (fun _ ↦ c) (Ioo r R)) :
    f R = c := by
  have : Filter.Tendsto f (𝓝[Iio R] R) (𝓝 (f R)) := by
    apply (h₁f R (right_mem_Ioc.mpr hR)).mono_left
    rw [nhdsWithin_le_iff, mem_nhdsLT_iff_exists_Ioo_subset]
    use r
    simp_all [Ioo_subset_Ioc_self]
  apply tendsto_nhds_unique this (tendsto_const_nhds.congr' _)
  apply Filter.eventuallyEq_of_mem (Ioo_mem_nhdsLT hR) (fun _ hx ↦ (h₂f hx).symm)

/-!
## Constant Functions
-/

/--
The circle average of a constant function equals the constant.
-/
/-
**Real.circleAverage_const** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：circleAverage_const [CompleteSpace E] (a : E) (c : Complex) (R : Real) : c
ircleAverage (fun _ => a) c R = a
参数：a : E；c : Complex；R : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `intervalIntegral.integral_const`：integral_const [CompleteSpace E] (c : E
) : ∫ _ in a..b, c = (b - a) • c
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b : R}, a = a' → a'⁻¹ = b → a⁻¹ = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
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
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_mul`：∀ {R : Type u_2} [inst : Semifield R
] {a₁ : R} {a₂ : ℕ} {a₃ b₁ b₃ c : R},   a₁⁻¹ = b₁ → a₃⁻¹ = b₃ → b₃ * (b₁ ^ a₂ * 
Nat.rawCast 1) = c → (a₁…
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_raw_eq`：∀ {α : Type u} {n d : ℕ} [inst :
 DivisionSemiring α] {a : α}, Mathlib.Meta.NormNum.IsNNRat a n d → a = NNRat.raw
Cast n d
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.of_raw`：∀ (α : Type u_1) [inst : DivisionSe
miring α] (n d : ℕ), ↑d ≠ 0 → Mathlib.Meta.NormNum.IsNNRat (NNRat.rawCast n d) n
 d
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.den_nz`：∀ {α : Type u_1} [inst : DivisionSe
miring α] {a : α} {n d : ℕ}, Mathlib.Meta.NormNum.IsNNRat a n d → ↑d ≠ 0
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
The circle average of a constant function equals the constant.
-/
theorem circleAverage_const [CompleteSpace E] (a : E) (c : ℂ) (R : ℝ) :
    circleAverage (fun _ ↦ a) c R = a := by
  simp only [circleAverage, intervalIntegral.integral_const, ← smul_assoc, sub_zero, smul_eq_mul]
  ring_nf
  simp

/--
If `f x` equals `a` on for every point of the circle, then the circle average of `f` equals `a`.
-/
/-
**Real.circleAverage_const_on_circle** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：circleAverage_const_on_circle [CompleteSpace E] {a : E} (hf : forall x in 
Metric.sphere c |R|, f x = a) : circleAverage f c R = a
参数：hf : forall x in Metric.sphere c |R|, f x = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.circleAverage.eq_1`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] 
[inst_1 : NormedSpace ℝ E] (f : ℂ → E) (c : ℂ) (R : ℝ),   Real.circleAverage f c
 R = (2 * Rea…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `circleMap_mem_sphere'`：circleMap_mem_sphere' (c : Complex) (R : Real) (θ
 : Real) : circleMap c R θ in sphere c |R|
· 使用定理 `Real.circleAverage_const`：circleAverage_const [CompleteSpace E] (a : E) 
(c : Complex) (R : Real) : circleAverage (fun _ => a) c R = a

--- 原说明 ---
If `f x` equals `a` on for every point of the circle, then the circle average of
 `f` equals `a`.
-/
theorem circleAverage_const_on_circle [CompleteSpace E] {a : E}
    (hf : ∀ x ∈ Metric.sphere c |R|, f x = a) :
    circleAverage f c R = a := by
  rw [circleAverage]
  conv =>
    left; arg 2; arg 1
    intro θ
    rw [hf (circleMap c R θ) (circleMap_mem_sphere' c R θ)]
  apply circleAverage_const a c R

/-!
## Inequalities
-/

/--
Circle averages respect the `≤` relation.
-/
@[gcongr]
/-
**Real.circleAverage_mono** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：circleAverage_mono {c : Complex} {R : Real} {f₁ f₂ : Complex -> Real} (hf₁
 : CircleIntegrable f₁ c R) (hf₂ : CircleIntegrable f₂ c R) (h : forall x in Met
ric.sphere c |R|, f₁ x <= f₂ x) : circleAverage f₁ c R <= circleAverage f₂ c R
参数：hf₁ : CircleIntegrable f₁ c R；hf₂ : CircleIntegrable f₂ c R；h : forall x in M
etric.sphere c |R|, f₁ x <= f₂ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_le_mul_iff_of_pos_left`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Ze
ro α] [inst_2 : Preorder α] {a b c : α} [PosMulMono α] [PosMulReflectLE α],   0 
< a → (a * b ≤ a…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `intervalIntegral.integral_mono_on_of_le_Ioo`：integral_mono_on_of_le_Ioo 
[NullSingletonClass μ] (h : forall x in Ioo a b, f x <= g x) : (∫ u in a..b, f u
 ∂μ) <= ∫ u in a..b, g u ∂μ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `circleMap_sub_center`：circleMap_sub_center (c : Complex) (R : Real) (θ :
 Real) : circleMap c R θ - c = circleMap 0 R θ
· 使用定理 `norm_circleMap_zero`：norm_circleMap_zero (R : Real) (θ : Real) : ‖circle
Map 0 R θ‖ = |R|
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Circle averages respect the `≤` relation.
-/
theorem circleAverage_mono {c : ℂ} {R : ℝ} {f₁ f₂ : ℂ → ℝ} (hf₁ : CircleIntegrable f₁ c R)
    (hf₂ : CircleIntegrable f₂ c R) (h : ∀ x ∈ Metric.sphere c |R|, f₁ x ≤ f₂ x) :
    circleAverage f₁ c R ≤ circleAverage f₂ c R := by
  apply (mul_le_mul_iff_of_pos_left (by simp [pi_pos])).2
  apply intervalIntegral.integral_mono_on_of_le_Ioo (le_of_lt two_pi_pos) hf₁ hf₂
  exact fun x _ ↦ by simp [h (circleMap c R x)]

/--
If `f x` is smaller than `a` on for every point of the circle, then the circle average of `f` is
smaller than `a`.
-/
/-
**Real.circleAverage_mono_on_of_le_circle** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：circleAverage_mono_on_of_le_circle {f : Complex -> Real} {a : Real} (hf : 
CircleIntegrable f c R) (h₂f : forall x in Metric.sphere c |R|, f x <= a) : circ
leAverage f c R <= a
参数：hf : CircleIntegrable f c R；h₂f : forall x in Metric.sphere c |R|, f x <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.circleAverage_const`：circleAverage_const [CompleteSpace E] (a : E) 
(c : Complex) (R : Real) : circleAverage (fun _ => a) c R = a
· 使用定理 `Real.circleAverage.eq_1`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] 
[inst_1 : NormedSpace ℝ E] (f : ℂ → E) (c : ℂ) (R : ℝ),   Real.circleAverage f c
 R = (2 * Rea…
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_le_mul_iff_of_pos_left`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Ze
ro α] [inst_2 : Preorder α] {a b c : α} [PosMulMono α] [PosMulReflectLE α],   0 
< a → (a * b ≤ a…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `intervalIntegral.integral_mono_on_of_le_Ioo`：integral_mono_on_of_le_Ioo 
[NullSingletonClass μ] (h : forall x in Ioo a b, f x <= g x) : (∫ u in a..b, f u
 ∂μ) <= ∫ u in a..b, g u ∂μ
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `intervalIntegrable_const`：intervalIntegrable_const [IsLocallyFiniteMeasu
re μ] {c : E} : IntervalIntegrable (fun _ => c) μ a b
· 使用定理 `circleMap_mem_sphere'`：circleMap_mem_sphere' (c : Complex) (R : Real) (θ
 : Real) : circleMap c R θ in sphere c |R|

--- 原说明 ---
If `f x` is smaller than `a` on for every point of the circle, then the circle a
verage of `f` is
smaller than `a`.
-/
theorem circleAverage_mono_on_of_le_circle {f : ℂ → ℝ} {a : ℝ} (hf : CircleIntegrable f c R)
    (h₂f : ∀ x ∈ Metric.sphere c |R|, f x ≤ a) :
    circleAverage f c R ≤ a := by
  rw [← circleAverage_const a c |R|, circleAverage, circleAverage, smul_eq_mul, smul_eq_mul,
    mul_le_mul_iff_of_pos_left (inv_pos.2 two_pi_pos)]
  exact intervalIntegral.integral_mono_on_of_le_Ioo (le_of_lt two_pi_pos) hf
    intervalIntegrable_const (fun θ _ ↦ h₂f (circleMap c R θ) (circleMap_mem_sphere' c R θ))

/--
Analogue of `intervalIntegral.abs_integral_le_integral_abs`: The absolute value of a circle average
is less than or equal to the circle average of the absolute value of the function.
-/
/-
**Real.abs_circleAverage_le_circleAverage_abs** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：abs_circleAverage_le_circleAverage_abs {f : Complex -> Real} : |circleAver
age f c R| <= circleAverage |f| c R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.circleAverage.eq_1`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] 
[inst_1 : NormedSpace ℝ E] (f : ℂ → E) (c : ℂ) (R : ℝ),   Real.circleAverage f c
 R = (2 * Rea…
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `mul_le_mul_iff_of_pos_left`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Ze
ro α] [inst_2 : Preorder α] {a b c : α} [PosMulMono α] [PosMulReflectLE α],   0 
< a → (a * b ≤ a…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `intervalIntegral.abs_integral_le_integral_abs`：abs_integral_le_integral_
abs (hab : a <= b) : |∫ x in a..b, f x ∂μ| <= ∫ x in a..b, |f x| ∂μ
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
Analogue of `intervalIntegral.abs_integral_le_integral_abs`: The absolute value 
of a circle average
is less than or equal to the circle average of the absolute value of the functio
n.
-/
theorem abs_circleAverage_le_circleAverage_abs {f : ℂ → ℝ} :
    |circleAverage f c R| ≤ circleAverage |f| c R := by
  rw [circleAverage, circleAverage, smul_eq_mul, smul_eq_mul, abs_mul,
    abs_of_pos (inv_pos.2 two_pi_pos), mul_le_mul_iff_of_pos_left (inv_pos.2 two_pi_pos)]
  exact intervalIntegral.abs_integral_le_integral_abs (le_of_lt two_pi_pos)

/--
The circle average of a nonnegative function is nonnegative.
-/
/-
**Real.circleAverage_nonneg_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：circleAverage_nonneg_of_nonneg {c : Complex} {R : Real} {f : Complex -> Re
al} (h₂f : forall x in Metric.sphere c |R|, 0 <= f x) : 0 <= circleAverage f c R
参数：h₂f : forall x in Metric.sphere c |R|, 0 <= f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.circleAverage_const`：circleAverage_const [CompleteSpace E] (a : E) 
(c : Complex) (R : Real) : circleAverage (fun _ => a) c R = a
· 使用定理 `Real.circleAverage.eq_1`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] 
[inst_1 : NormedSpace ℝ E] (f : ℂ → E) (c : ℂ) (R : ℝ),   Real.circleAverage f c
 R = (2 * Rea…
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_le_mul_iff_of_pos_left`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Ze
ro α] [inst_2 : Preorder α] {a b c : α} [PosMulMono α] [PosMulReflectLE α],   0 
< a → (a * b ≤ a…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `intervalIntegral.integral_mono_on_of_le_Ioo`：integral_mono_on_of_le_Ioo 
[NullSingletonClass μ] (h : forall x in Ioo a b, f x <= g x) : (∫ u in a..b, f u
 ∂μ) <= ∫ u in a..b, g u ∂μ
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `intervalIntegrable_const`：intervalIntegrable_const [IsLocallyFiniteMeasu
re μ] {c : E} : IntervalIntegrable (fun _ => c) μ a b
· 使用定理 `circleMap_mem_sphere'`：circleMap_mem_sphere' (c : Complex) (R : Real) (θ
 : Real) : circleMap c R θ in sphere c |R|
· 使用定理 `Real.circleAverage.integral_undef`：∀ {E : Type u_1} [inst : NormedAddCom
mGroup E] [inst_1 : NormedSpace ℝ E] {f : ℂ → E} {c : ℂ} {R : ℝ},   ¬CircleInteg
rable f c R → Real.circ…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
The circle average of a nonnegative function is nonnegative.
-/
theorem circleAverage_nonneg_of_nonneg {c : ℂ} {R : ℝ} {f : ℂ → ℝ}
    (h₂f : ∀ x ∈ Metric.sphere c |R|, 0 ≤ f x) :
    0 ≤ circleAverage f c R := by
  by_cases hf : CircleIntegrable f c R
  · rw [← circleAverage_const 0 c |R|, circleAverage, circleAverage, smul_eq_mul, smul_eq_mul,
      mul_le_mul_iff_of_pos_left (inv_pos.2 two_pi_pos)]
    apply intervalIntegral.integral_mono_on_of_le_Ioo (le_of_lt two_pi_pos)
      intervalIntegrable_const hf (fun θ _ ↦ h₂f (circleMap c R θ) (circleMap_mem_sphere' c R θ))
  · rw [circleAverage.integral_undef hf]

/-!
## Commutativity with Linear Maps
-/

/-- Circle averages commute with continuous linear maps. -/
/-
**Real._root_.ContinuousLinearMap.circleAverage_comp_comm** 是 Mathlib 中的一个定理，位于命
名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Circle averages commute with continuous linear maps.
-/
theorem _root_.ContinuousLinearMap.circleAverage_comp_comm [CompleteSpace E] (L : E →L[ℝ] F)
    {f : ℂ → E} (hf : CircleIntegrable f c R) :
    circleAverage (L ∘ f) c R = L (circleAverage f c R) := by
  unfold circleAverage
  rw [map_smul]
  congr
  exact L.intervalIntegral_comp_comm hf

/-!
## Behaviour with Respect to Arithmetic Operations
-/

/-- Circle averages commute with scalar multiplication. -/
/-
**Real.circleAverage_smul** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：circleAverage_smul : circleAverage (a • f) c R = a • circleAverage f c R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `intervalIntegral.integral_smul`：∀ {𝕜 : Type u_2} {E : Type u_5} [inst : 
NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {a b : ℝ}   {μ : MeasureTheory.
Measure ℝ} [inst_2 :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Circle averages commute with scalar multiplication.
-/
theorem circleAverage_smul :
    circleAverage (a • f) c R = a • circleAverage f c R := by
  unfold circleAverage
  have := SMulCommClass.symm ℝ 𝕜 E
  rw [smul_comm]
  simp [intervalIntegral.integral_smul]

/-- Circle averages commute with scalar multiplication. -/
/-
**Real.circleAverage_fun_smul** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：circleAverage_fun_smul : circleAverage (fun z => a • f z) c R = a • circle
Average f c R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.circleAverage_smul`：circleAverage_smul : circleAverage (a • f) c R 
= a • circleAverage f c R

--- 原说明 ---
Circle averages commute with scalar multiplication.
-/
theorem circleAverage_fun_smul :
    circleAverage (fun z ↦ a • f z) c R = a • circleAverage f c R :=
  circleAverage_smul

/-- Circle averages commute with addition. -/
/-
**Real.circleAverage_add** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：circleAverage_add (hf₁ : CircleIntegrable f₁ c R) (hf₂ : CircleIntegrable 
f₂ c R) : circleAverage (f₁ + f₂) c R = circleAverage f₁ c R + circleAverage f₂ 
c R
参数：hf₁ : CircleIntegrable f₁ c R；hf₂ : CircleIntegrable f₂ c R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.circleAverage.eq_1`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] 
[inst_1 : NormedSpace ℝ E] (f : ℂ → E) (c : ℂ) (R : ℝ),   Real.circleAverage f c
 R = (2 * Rea…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `intervalIntegral.integral_add`：∀ {E : Type u_5} [inst : NormedAddCommGro
up E] [inst_1 : NormedSpace ℝ E] {a b : ℝ} {f g : ℝ → E}   {μ : MeasureTheory.Me
asure ℝ},   Interva…

--- 原说明 ---
Circle averages commute with addition.
-/
theorem circleAverage_add (hf₁ : CircleIntegrable f₁ c R) (hf₂ : CircleIntegrable f₂ c R) :
    circleAverage (f₁ + f₂) c R = circleAverage f₁ c R + circleAverage f₂ c R := by
  rw [circleAverage, circleAverage, circleAverage, ← smul_add]
  congr
  apply intervalIntegral.integral_add hf₁ hf₂

/-- Circle averages commute with addition. -/
/-
**Real.circleAverage_fun_add** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：circleAverage_fun_add {c : Complex} {R : Real} {f₁ f₂ : Complex -> E} (hf₁
 : CircleIntegrable f₁ c R) (hf₂ : CircleIntegrable f₂ c R) : circleAverage (fun
 z => f₁ z + f₂ z) c R = circleAverage f₁ c R + circleAverage f₂ c R
参数：hf₁ : CircleIntegrable f₁ c R；hf₂ : CircleIntegrable f₂ c R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.circleAverage_add`：circleAverage_add (hf₁ : CircleIntegrable f₁ c R
) (hf₂ : CircleIntegrable f₂ c R) : circleAverage (f₁ + f₂) c R = circleAverage 
f₁ c R + cir…

--- 原说明 ---
Circle averages commute with addition.
-/
theorem circleAverage_fun_add {c : ℂ} {R : ℝ} {f₁ f₂ : ℂ → E} (hf₁ : CircleIntegrable f₁ c R)
    (hf₂ : CircleIntegrable f₂ c R) :
    circleAverage (fun z ↦ f₁ z + f₂ z) c R = circleAverage f₁ c R + circleAverage f₂ c R :=
  circleAverage_add hf₁ hf₂

/-- Circle averages commute with sums. -/
/-
**Real.circleAverage_sum** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：circleAverage_sum {ι : Type*} {s : Finset ι} {f : ι -> Complex -> E} (h : 
forall i in s, CircleIntegrable (f i) c R) : circleAverage (∑ i in s, f i) c R =
 ∑ i in s, circleAverage (f i) c R
参数：h : forall i in s, CircleIntegrable (f i) c R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `intervalIntegral.integral_finsetSum`：∀ {E : Type u_5} [inst : NormedAddC
ommGroup E] [inst_1 : NormedSpace ℝ E] {a b : ℝ} {μ : MeasureTheory.Measure ℝ}  
 {ι : Type u_8} {s : Fins…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Circle averages commute with sums.
-/
theorem circleAverage_sum {ι : Type*} {s : Finset ι} {f : ι → ℂ → E}
    (h : ∀ i ∈ s, CircleIntegrable (f i) c R) :
    circleAverage (∑ i ∈ s, f i) c R = ∑ i ∈ s, circleAverage (f i) c R := by
  unfold circleAverage
  simp [← Finset.smul_sum, intervalIntegral.integral_finsetSum h]

/-- Circle averages commute with sums. -/
/-
**Real.circleAverage_fun_sum** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：circleAverage_fun_sum {ι : Type*} {s : Finset ι} {f : ι -> Complex -> E} (
h : forall i in s, CircleIntegrable (f i) c R) : circleAverage (fun z => ∑ i in 
s, f i z) c R = ∑ i in s, circleAverage (f i) c R
参数：h : forall i in s, CircleIntegrable (f i) c R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.circleAverage_sum`：circleAverage_sum {ι : Type*} {s : Finset ι} {f 
: ι -> Complex -> E} (h : forall i in s, CircleIntegrable (f i) c R) : circleAve
rage (∑ i in…

--- 原说明 ---
Circle averages commute with sums.
-/
theorem circleAverage_fun_sum {ι : Type*} {s : Finset ι} {f : ι → ℂ → E}
    (h : ∀ i ∈ s, CircleIntegrable (f i) c R) :
    circleAverage (fun z ↦ ∑ i ∈ s, f i z) c R = ∑ i ∈ s, circleAverage (f i) c R := by
  convert! circleAverage_sum h
  simp

/-- Circle averages commute with subtraction. -/
/-
**Real.circleAverage_sub** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：circleAverage_sub (hf₁ : CircleIntegrable f₁ c R) (hf₂ : CircleIntegrable 
f₂ c R) : circleAverage (f₁ - f₂) c R = circleAverage f₁ c R - circleAverage f₂ 
c R
参数：hf₁ : CircleIntegrable f₁ c R；hf₂ : CircleIntegrable f₂ c R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.circleAverage.eq_1`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] 
[inst_1 : NormedSpace ℝ E] (f : ℂ → E) (c : ℂ) (R : ℝ),   Real.circleAverage f c
 R = (2 * Rea…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `intervalIntegral.integral_sub`：integral_sub (hf : IntervalIntegrable f μ
 a b) (hg : IntervalIntegrable g μ a b) : ∫ x in a..b, f x - g x ∂μ = (∫ x in a.
.b, f x ∂μ) - ∫ x i…

--- 原说明 ---
Circle averages commute with subtraction.
-/
theorem circleAverage_sub (hf₁ : CircleIntegrable f₁ c R) (hf₂ : CircleIntegrable f₂ c R) :
    circleAverage (f₁ - f₂) c R = circleAverage f₁ c R - circleAverage f₂ c R := by
  rw [circleAverage, circleAverage, circleAverage, ← smul_sub]
  congr
  apply intervalIntegral.integral_sub hf₁ hf₂

/-- Circle averages commute with subtraction. -/
/-
**Real.circleAverage_fun_sub** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：circleAverage_fun_sub (hf₁ : CircleIntegrable f₁ c R) (hf₂ : CircleIntegra
ble f₂ c R) : circleAverage (fun z => f₁ z - f₂ z) c R = circleAverage f₁ c R - 
circleAverage f₂ c R
参数：hf₁ : CircleIntegrable f₁ c R；hf₂ : CircleIntegrable f₂ c R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.circleAverage_sub`：circleAverage_sub (hf₁ : CircleIntegrable f₁ c R
) (hf₂ : CircleIntegrable f₂ c R) : circleAverage (f₁ - f₂) c R = circleAverage 
f₁ c R - cir…

--- 原说明 ---
Circle averages commute with subtraction.
-/
theorem circleAverage_fun_sub (hf₁ : CircleIntegrable f₁ c R) (hf₂ : CircleIntegrable f₂ c R) :
    circleAverage (fun z ↦ f₁ z - f₂ z) c R = circleAverage f₁ c R - circleAverage f₂ c R :=
  circleAverage_sub hf₁ hf₂

end Real

