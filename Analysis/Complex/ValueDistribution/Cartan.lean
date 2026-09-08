/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Stefan Kebekus
-/

module

public import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
public import Mathlib.Analysis.Complex.ValueDistribution.Proximity.IntegralPresentation

/-!
# Cartan's Formula

This file establishes Cartan's classic formula,
`ValueDistribution.characteristic_top_eq_circleAverage_add_circleAverage`, describing the
characteristic function `characteristic f ⊤ r` as a sum of two circle averages,

- `circleAverage (logCounting f · r) 0 1` and
- `circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1`.

As a corollary, Cartan's formula implies the (surprisingly non-trivial) fact that the
characteristic function is monotone; this is stated in
`ValueDistribution.characteristic_monotoneOn`.

This file also establishes circle integrability of the function
`a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖` and computes values of the circle average.

## References

See Section VI.2 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] for a detailed
discussion.
-/

public section

open Filter Metric Real Set Topology

variable {f : ℂ → ℂ} {R : ℝ}

namespace ValueDistribution

/-!
## Terms in Cartan's formula
-/

/-
**ValueDistribution.log_trailingCoeff_eq_zero_on_unitSphere** 是 Mathlib 中的一个引理，位
于命名空间 `ValueDistribution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
## Terms in Cartan's formula
-/
private lemma log_trailingCoeff_eq_zero_on_unitSphere {a : ℂ} (h : 0 < meromorphicOrderAt f 0)
    (ha : a ∈ sphere 0 |1|) :
    log ‖meromorphicTrailingCoeffAt (f · - a) 0‖ = 0 := by
  simp_rw [sub_eq_neg_add]
  rw [(meromorphicAt_of_meromorphicOrderAt_ne_zero
    h.ne').meromorphicTrailingCoeffAt_fun_add_eq_left_of_lt]
  · aesop
  · rw [meromorphicOrderAt_const]
    aesop
/-
**ValueDistribution.eventuallyEq_log_trailingCoeff_of_meromorphicOrderAt_eq_zero
** 是 Mathlib 中的一个引理，位于命名空间 `ValueDistribution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma eventuallyEq_log_trailingCoeff_of_meromorphicOrderAt_eq_zero (h₁ : MeromorphicAt f 0)
    (h₂ : meromorphicOrderAt f 0 = 0) :
    (log ‖meromorphicTrailingCoeffAt f 0 - ·‖) =ᶠ[codiscreteWithin (sphere 0 |1|)]
      fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖ := by
  filter_upwards [self_mem_codiscreteWithin (sphere 0 |1|), compl_singleton_mem_codiscreteWithin
    (meromorphicTrailingCoeffAt f 0)] with a ha_sphere ha_ne
  congr
  rw [h₁.meromorphicTrailingCoeffAt_fun_sub_eq_sub
    (by fun_prop), meromorphicTrailingCoeffAt_const, sub_eq_add_neg]
  · simp only [meromorphicOrderAt_const]
    aesop
  · simp only [meromorphicTrailingCoeffAt_const, ne_eq]
    grind

/--
Circle integrability of the term `fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖` that
appears in Cartan's formula.
-/
/-
**ValueDistribution.circleIntegrable_log_meromorphicTrailingCoeffAt** 是 Mathlib 
中的一个定理，位于命名空间 `ValueDistribution`。
形式化陈述：circleIntegrable_log_meromorphicTrailingCoeffAt : CircleIntegrable (fun a 
=> log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeromorphicAt.meromorphicAt_fun_sub_iff_meromorphicAt₂`：meromorphicAt_fu
n_sub_iff_meromorphicAt₂ {f g : 𝕜 -> E} (hg : MeromorphicAt g x) : MeromorphicAt
 (fun z => f z - g z) x ↔ MeromorphicAt f x
· 使用引理 `MeromorphicAt.const`：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) 
x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `meromorphicTrailingCoeffAt_of_not_MeromorphicAt`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} …
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `circleIntegrable_congr`：circleIntegrable_congr {c : Complex} {R : Real} 
{f₁ f₂ : Complex -> E} (hf : Set.EqOn f₁ f₂ (sphere c |R|)) : CircleIntegrable f
₁ c R ↔ Circ…
· 使用定理 `MeromorphicAt.meromorphicTrailingCoeffAt_fun_sub_eq_left_of_lt`：Meromorp
hicAt.meromorphicTrailingCoeffAt_fun_sub_eq_left_of_lt {f₁ f₂ : 𝕜 -> E} (hf₂ : M
eromorphicAt f₂ x) (h : meromorphicOrderAt f₁ x < me…
· 使用定理 `meromorphicOrderAt_const`：meromorphicOrderAt_const (z₀ : 𝕜) (e : E) [Dec
idable (e = 0)] : meromorphicOrderAt (fun _ => e) z₀ = if e = 0 then ⊤ else (0 :
 WithTop Int)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `circleIntegrable_const`：circleIntegrable_const (a : E) (c : Complex) (R 
: Real) : CircleIntegrable (fun _ => a) c R
· 使用定理 `CircleIntegrable.congr_codiscreteWithin`：CircleIntegrable.congr_codiscre
teWithin {c : Complex} {R : Real} {f₁ f₂ : Complex -> E} (hf : f₁ =ᶠ[codiscreteW
ithin (sphere c |R|)] f₂) (hf…
· 使用定理 `_private.Mathlib.Analysis.Complex.ValueDistribution.Cartan.0.ValueDistri
bution.eventuallyEq_log_trailingCoeff_of_meromorphicOrderAt_eq_zero`：∀ {f : ℂ → 
ℂ},   MeromorphicAt f 0 →     meromorphicOrderAt f 0 = 0 →       (fun x => Real.
log ‖meromorphicTrailingCoeffAt f 0 - x‖) =ᶠ[Filt…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `norm_sub_rev`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), 
‖a - b‖ = ‖b - a‖
· 使用引理 `circleIntegrable_log_norm_sub_const`：circleIntegrable_log_norm_sub_const
 (r : Real) : CircleIntegrable (log ‖· - a‖) c r
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Circle integrability of the term `fun a ↦ log ‖meromorphicTrailingCoeffAt (f · -
 a) 0‖` that
appears in Cartan's formula.
-/
theorem circleIntegrable_log_meromorphicTrailingCoeffAt :
    CircleIntegrable (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 := by
  by_cases h: ¬MeromorphicAt f 0
  · have {a : ℂ} : ¬MeromorphicAt (fun x ↦ f x - a) 0 := by
      rwa [MeromorphicAt.meromorphicAt_fun_sub_iff_meromorphicAt₂ (by fun_prop)]
    simp_all
  rcases lt_trichotomy (meromorphicOrderAt f 0) 0 with hneg | hzero | hpos
  · refine (circleIntegrable_congr fun a ha ↦ ?_).2 (circleIntegrable_const
      (log ‖meromorphicTrailingCoeffAt f 0‖) 0 1)
    rw [(MeromorphicAt.const a 0).meromorphicTrailingCoeffAt_fun_sub_eq_left_of_lt]
    rw [meromorphicOrderAt_const]
    aesop
  · apply CircleIntegrable.congr_codiscreteWithin
     (eventuallyEq_log_trailingCoeff_of_meromorphicOrderAt_eq_zero (not_not.1 h) hzero)
    simpa [norm_sub_rev] using circleIntegrable_log_norm_sub_const 1
  · apply (circleIntegrable_congr _).2 (circleIntegrable_const 0 0 1)
    exact fun _ ↦ log_trailingCoeff_eq_zero_on_unitSphere hpos

/--
Circle average of the function `fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖` that appears
in Cartan's formula, in the case where `f` has a zero at the origin.
-/
/-
**ValueDistribution.circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromor
phicOrderAt_pos** 是 Mathlib 中的一个定理，位于命名空间 `ValueDistribution`。
形式化陈述：circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_po
s (h : 0 < meromorphicOrderAt f 0) : circleAverage (fun a => log ‖meromorphicTra
ilingCoeffAt (f · - a) 0‖) 0 1 = 0
参数：h : 0 < meromorphicOrderAt f 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.circleAverage_const_on_circle`：circleAverage_const_on_circle [Compl
eteSpace E] {a : E} (hf : forall x in Metric.sphere c |R|, f x = a) : circleAver
age f c R = a
· 使用定理 `_private.Mathlib.Analysis.Complex.ValueDistribution.Cartan.0.ValueDistri
bution.log_trailingCoeff_eq_zero_on_unitSphere`：∀ {f : ℂ → ℂ} {a : ℂ},   0 < mer
omorphicOrderAt f 0 → a ∈ Metric.sphere 0 |1| → Real.log ‖meromorphicTrailingCoe
ffAt (fun x => f x - a) 0‖ =…

--- 原说明 ---
Circle average of the function `fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a
) 0‖` that appears
in Cartan's formula, in the case where `f` has a zero at the origin.
-/
theorem circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_pos
    (h : 0 < meromorphicOrderAt f 0) :
    circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 = 0 :=
  circleAverage_const_on_circle (fun _ hx ↦ log_trailingCoeff_eq_zero_on_unitSphere h hx)

/--
Circle average of the function `fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖` that appears
in Cartan's formula, in the case where `f` has order zero at the origin.
-/
/-
**ValueDistribution.circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromor
phicOrderAt_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `ValueDistribution`。
形式化陈述：circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_eq
_zero (h : meromorphicOrderAt f 0 = 0) : circleAverage (fun a => log ‖meromorphi
cTrailingCoeffAt (f · - a) 0‖) 0 1 = log⁺ ‖meromorphicTrailingCoeffAt f 0‖
参数：h : meromorphicOrderAt f 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.circleAverage_congr_codiscreteWithin`：circleAverage_congr_codiscret
eWithin (hf : f₁ =ᶠ[codiscreteWithin (sphere c |R|)] f₂) (hR : R != 0) : circleA
verage f₁ c R = circleAverage f…
· 使用定理 `_private.Mathlib.Analysis.Complex.ValueDistribution.Cartan.0.ValueDistri
bution.eventuallyEq_log_trailingCoeff_of_meromorphicOrderAt_eq_zero`：∀ {f : ℂ → 
ℂ},   MeromorphicAt f 0 →     meromorphicOrderAt f 0 = 0 →       (fun x => Real.
log ‖meromorphicTrailingCoeffAt f 0 - x‖) =ᶠ[Filt…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_sub_rev`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), 
‖a - b‖ = ‖b - a‖
· 使用定理 `circleAverage_log_norm_sub_const_eq_posLog`：circleAverage_log_norm_sub_c
onst_eq_posLog : circleAverage (log ‖· - a‖) 0 1 = log⁺ ‖a‖
· 使用引理 `MeromorphicAt.meromorphicAt_fun_sub_iff_meromorphicAt₂`：meromorphicAt_fu
n_sub_iff_meromorphicAt₂ {f g : 𝕜 -> E} (hg : MeromorphicAt g x) : MeromorphicAt
 (fun z => f z - g z) x ↔ MeromorphicAt f x
· 使用引理 `MeromorphicAt.const`：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) 
x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `meromorphicTrailingCoeffAt_of_not_MeromorphicAt`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} …
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `Real.circleAverage_const`：circleAverage_const [CompleteSpace E] (a : E) 
(c : Complex) (R : Real) : circleAverage (fun _ => a) c R = a
· 使用定理 `Real.posLog_zero`：Real.posLog 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Circle average of the function `fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a
) 0‖` that appears
in Cartan's formula, in the case where `f` has order zero at the origin.
-/
theorem circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_eq_zero
    (h : meromorphicOrderAt f 0 = 0) :
    circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1
      = log⁺ ‖meromorphicTrailingCoeffAt f 0‖ := by
  by_cases hf : MeromorphicAt f 0
  · rw [← circleAverage_congr_codiscreteWithin
      (eventuallyEq_log_trailingCoeff_of_meromorphicOrderAt_eq_zero hf h) zero_ne_one.symm]
    simp_rw [norm_sub_rev]
    rw [circleAverage_log_norm_sub_const_eq_posLog]
  have {a : ℂ} : ¬ MeromorphicAt (fun x ↦ f x - a) 0 := by
    rwa [MeromorphicAt.meromorphicAt_fun_sub_iff_meromorphicAt₂ (by fun_prop)]
  simp_all [circleAverage_const]

/--
Circle average of the function `fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖` that appears
in Cartan's formula, in the case where `f` has a pole at the origin.
-/
/-
**ValueDistribution.circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromor
phicOrderAt_lt_zero** 是 Mathlib 中的一个定理，位于命名空间 `ValueDistribution`。
形式化陈述：circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_lt
_zero (h : meromorphicOrderAt f 0 < 0) : circleAverage (fun a => log ‖meromorphi
cTrailingCoeffAt (f · - a) 0‖) 0 1 = log ‖meromorphicTrailingCoeffAt f 0‖
参数：h : meromorphicOrderAt f 0 < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.circleAverage_congr_sphere`：circleAverage_congr_sphere {f₁ f₂ : Com
plex -> E} (hf : Set.EqOn f₁ f₂ (sphere c |R|)) : circleAverage f₁ c R = circleA
verage f₂ c R
· 使用定理 `MeromorphicAt.meromorphicTrailingCoeffAt_fun_sub_eq_left_of_lt`：Meromorp
hicAt.meromorphicTrailingCoeffAt_fun_sub_eq_left_of_lt {f₁ f₂ : 𝕜 -> E} (hf₂ : M
eromorphicAt f₂ x) (h : meromorphicOrderAt f₁ x < me…
· 使用引理 `MeromorphicAt.const`：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) 
x
· 使用定理 `meromorphicOrderAt_const`：meromorphicOrderAt_const (z₀ : 𝕜) (e : E) [Dec
idable (e = 0)] : meromorphicOrderAt (fun _ => e) z₀ = if e = 0 then ⊤ else (0 :
 WithTop Int)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Real.circleAverage_const`：circleAverage_const [CompleteSpace E] (a : E) 
(c : Complex) (R : Real) : circleAverage (fun _ => a) c R = a

--- 原说明 ---
Circle average of the function `fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a
) 0‖` that appears
in Cartan's formula, in the case where `f` has a pole at the origin.
-/
theorem circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_lt_zero
    (h : meromorphicOrderAt f 0 < 0) :
    circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1
      = log ‖meromorphicTrailingCoeffAt f 0‖ := by
  rw [circleAverage_congr_sphere (f₂ := fun _ ↦ log ‖meromorphicTrailingCoeffAt f 0‖),
    circleAverage_const]
  intro a ha
  simp only
  congr 2
  rw [(MeromorphicAt.const a 0).meromorphicTrailingCoeffAt_fun_sub_eq_left_of_lt]
  rw [meromorphicOrderAt_const]
  aesop

/- Specialized Jensen-type identity -/
/-
**ValueDistribution.logCounting_add_log_trailingCoeff_eq_circleAverage_add_logCo
unting_top** 是 Mathlib 中的一个引理，位于命名空间 `ValueDistribution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Specialized Jensen-type identity
-/
private lemma logCounting_add_log_trailingCoeff_eq_circleAverage_add_logCounting_top
    (h : Meromorphic f) (hR : R ≠ 0) (a : ℂ) :
    logCounting f a R + log ‖meromorphicTrailingCoeffAt (f · - a) 0‖ =
      circleAverage (log ‖f · - a‖) 0 R + logCounting f ⊤ R := by
  have : logCounting f a R - logCounting f ⊤ R = circleAverage (log ‖f · - a‖) 0 R
        - log ‖meromorphicTrailingCoeffAt (f · - a) 0‖ := by
    rw [logCounting_coe_eq_logCounting_sub_const_zero, ← logCounting_sub_const h]
    exact logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const (by fun_prop) hR
  linarith

/--
Circle integrability of the term `logCounting f · R` that appears in Cartan's formula.
-/
/-
**ValueDistribution.circleIntegrable_logCounting** 是 Mathlib 中的一个定理，位于命名空间 `Valu
eDistribution`。
形式化陈述：circleIntegrable_logCounting (h : Meromorphic f) : CircleIntegrable (logCo
unting f · R) 0 1
参数：h : Meromorphic f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ValueDistribution.logCounting.congr_simp`：∀ {𝕜 : Type u_1} [inst : Nontr
iviallyNormedField 𝕜] [inst_1 : ProperSpace 𝕜] {E : Type u_2}   [inst_2 : Normed
AddCommGroup E] [inst_3 : Norm…
· 使用定理 `ValueDistribution.logCounting_eval_zero`：∀ {𝕜 : Type u_1} [inst : Nontri
viallyNormedField 𝕜] [inst_1 : ProperSpace 𝕜] {E : Type u_2}   [inst_2 : NormedA
ddCommGroup E] [inst_3 : Norm…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_sub_of_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a + 
c = b → a = b - c
· 使用定理 `_private.Mathlib.Analysis.Complex.ValueDistribution.Cartan.0.ValueDistri
bution.logCounting_add_log_trailingCoeff_eq_circleAverage_add_logCounting_top`：∀
 {f : ℂ → ℂ} {R : ℝ},   Meromorphic f →     R ≠ 0 →       ∀ (a : ℂ),         Val
ueDistribution.logCounting f (↑a) R + Real.log ‖meromorphic…
· 使用定理 `CircleIntegrable.sub`：sub (hf : CircleIntegrable f c R) (hg : CircleInte
grable g c R) : CircleIntegrable (f - g) c R
· 使用定理 `CircleIntegrable.add`：add (hf : CircleIntegrable f c R) (hg : CircleInte
grable g c R) : CircleIntegrable (f + g) c R
· 使用定理 `ValueDistribution.circleIntegrable_circleAverage_log_norm_sub`：circleInt
egrable_circleAverage_log_norm_sub (h : Meromorphic f) : CircleIntegrable (fun a
 => circleAverage (log ‖f · - a‖) 0 R) 0 1
· 使用定理 `circleIntegrable_const`：circleIntegrable_const (a : E) (c : Complex) (R 
: Real) : CircleIntegrable (fun _ => a) c R
· 使用定理 `ValueDistribution.circleIntegrable_log_meromorphicTrailingCoeffAt`：circl
eIntegrable_log_meromorphicTrailingCoeffAt : CircleIntegrable (fun a => log ‖mer
omorphicTrailingCoeffAt (f · - a) 0‖) 0 1

--- 原说明 ---
Circle integrability of the term `logCounting f · R` that appears in Cartan's fo
rmula.
-/
theorem circleIntegrable_logCounting (h : Meromorphic f) :
    CircleIntegrable (logCounting f · R) 0 1 := by
  by_cases hR : R = 0
  · simp [hR, ValueDistribution.logCounting_eval_zero]
  convert circleIntegrable_circleAverage_log_norm_sub h |>.add
    (circleIntegrable_const (logCounting f ⊤ R) 0 1) |>.sub
    circleIntegrable_log_meromorphicTrailingCoeffAt
  simpa using eq_sub_of_add_eq
    (logCounting_add_log_trailingCoeff_eq_circleAverage_add_logCounting_top h hR _)

/-!
## Cartan's formula
-/

/--
**Cartan's formula** with the additive constant written explicitly as a circle average of the
logarithm of the first nonzero Laurent coefficient of `f - a` at the origin.

See `circleIntegrable_logCounting` and `circleIntegrable_log_meromorphicTrailingCoeffAt` for the
facts that the summands are actually circle integrable.
-/
/-
**ValueDistribution.characteristic_top_eq_circleAverage_add_circleAverage** 是 Ma
thlib 中的一个定理，位于命名空间 `ValueDistribution`。
形式化陈述：characteristic_top_eq_circleAverage_add_circleAverage (h : Meromorphic f) 
(hR : R != 0) : characteristic f ⊤ R = circleAverage (logCounting f · R) 0 1 + c
ircleAverage (fun a => log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1
参数：h : Meromorphic f；hR : R != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ValueDistribution.proximity_top`：proximity_top : proximity f ⊤ = circleA
verage (log⁺ ‖f ·‖) 0
· 使用定理 `ValueDistribution.circleAverage_circleAverage_eq_proximity_top`：circleAv
erage_circleAverage_eq_proximity_top (h : Meromorphic f) : (fun R => circleAvera
ge (fun a => circleAverage (log ‖f · - a‖) 0 R) 0 1)…
· 使用定理 `Real.circleAverage_fun_add`：circleAverage_fun_add {c : Complex} {R : Rea
l} {f₁ f₂ : Complex -> E} (hf₁ : CircleIntegrable f₁ c R) (hf₂ : CircleIntegrabl
e f₂ c R) : circ…
· 使用定理 `ValueDistribution.circleIntegrable_circleAverage_log_norm_sub`：circleInt
egrable_circleAverage_log_norm_sub (h : Meromorphic f) : CircleIntegrable (fun a
 => circleAverage (log ‖f · - a‖) 0 R) 0 1
· 使用定理 `circleIntegrable_const`：circleIntegrable_const (a : E) (c : Complex) (R 
: Real) : CircleIntegrable (fun _ => a) c R
· 使用定理 `Real.circleAverage_const`：circleAverage_const [CompleteSpace E] (a : E) 
(c : Complex) (R : Real) : circleAverage (fun _ => a) c R = a
· 使用定理 `Real.circleAverage_add`：circleAverage_add (hf₁ : CircleIntegrable f₁ c R
) (hf₂ : CircleIntegrable f₂ c R) : circleAverage (f₁ + f₂) c R = circleAverage 
f₁ c R + cir…
· 使用定理 `ValueDistribution.circleIntegrable_logCounting`：circleIntegrable_logCoun
ting (h : Meromorphic f) : CircleIntegrable (logCounting f · R) 0 1
· 使用定理 `ValueDistribution.circleIntegrable_log_meromorphicTrailingCoeffAt`：circl
eIntegrable_log_meromorphicTrailingCoeffAt : CircleIntegrable (fun a => log ‖mer
omorphicTrailingCoeffAt (f · - a) 0‖) 0 1
· 使用定理 `Real.circleAverage_congr_sphere`：circleAverage_congr_sphere {f₁ f₂ : Com
plex -> E} (hf : Set.EqOn f₁ f₂ (sphere c |R|)) : circleAverage f₁ c R = circleA
verage f₂ c R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `_private.Mathlib.Analysis.Complex.ValueDistribution.Cartan.0.ValueDistri
bution.logCounting_add_log_trailingCoeff_eq_circleAverage_add_logCounting_top`：∀
 {f : ℂ → ℂ} {R : ℝ},   Meromorphic f →     R ≠ 0 →       ∀ (a : ℂ),         Val
ueDistribution.logCounting f (↑a) R + Real.log ‖meromorphic…

--- 原说明 ---
**Cartan's formula** with the additive constant written explicitly as a circle a
verage of the
logarithm of the first nonzero Laurent coefficient of `f - a` at the origin.

See `circleIntegrable_logCounting` and `circleIntegrable_log_meromorphicTrailing
CoeffAt` for the
facts that the summands are actually circle integrable.
-/
theorem characteristic_top_eq_circleAverage_add_circleAverage (h : Meromorphic f) (hR : R ≠ 0) :
    characteristic f ⊤ R = circleAverage (logCounting f · R) 0 1
      + circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 := calc
  characteristic f ⊤ R
      = circleAverage (fun a ↦ circleAverage (log ‖f · - a‖) 0 R + logCounting f ⊤ R) 0 1 := by
      simp only [characteristic, proximity, ↓reduceDIte, Pi.add_apply]
      rw [← proximity_top, ← circleAverage_circleAverage_eq_proximity_top h,
        circleAverage_fun_add (circleIntegrable_circleAverage_log_norm_sub h)
          (circleIntegrable_const (logCounting f ⊤ R) 0 1), circleAverage_const]
    _ = circleAverage (logCounting f · R) 0 1
          + circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 := by
      rw [← circleAverage_add (circleIntegrable_logCounting h)
        circleIntegrable_log_meromorphicTrailingCoeffAt, circleAverage_congr_sphere]
      intro a ha
      simp [logCounting_add_log_trailingCoeff_eq_circleAverage_add_logCounting_top h hR a]

/--
**Cartan's formula** in the case where `0 < meromorphicOrderAt f 0`.
-/
/-
**ValueDistribution.characteristic_top_eq_circleAverage_of_meromorphicOrderAt_po
s** 是 Mathlib 中的一个定理，位于命名空间 `ValueDistribution`。
形式化陈述：characteristic_top_eq_circleAverage_of_meromorphicOrderAt_pos (h₁f : Merom
orphic f) (h₂f : 0 < meromorphicOrderAt f 0) (hR : R != 0) : characteristic f ⊤ 
R = circleAverage (logCounting f · R) 0 1
参数：h₁f : Meromorphic f；h₂f : 0 < meromorphicOrderAt f 0；hR : R != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ValueDistribution.characteristic_top_eq_circleAverage_add_circleAverage`
：characteristic_top_eq_circleAverage_add_circleAverage (h : Meromorphic f) (hR :
 R != 0) : characteristic f ⊤ R = circleAverage (logCounting …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ValueDistribution.circleAverage_log_norm_meromorphicTrailingCoeffAt_of_m
eromorphicOrderAt_pos`：circleAverage_log_norm_meromorphicTrailingCoeffAt_of_mero
morphicOrderAt_pos (h : 0 < meromorphicOrderAt f 0) : circleAverage (fun a => lo
g ‖…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
**Cartan's formula** in the case where `0 < meromorphicOrderAt f 0`.
-/
theorem characteristic_top_eq_circleAverage_of_meromorphicOrderAt_pos
    (h₁f : Meromorphic f) (h₂f : 0 < meromorphicOrderAt f 0) (hR : R ≠ 0) :
    characteristic f ⊤ R = circleAverage (logCounting f · R) 0 1 := by
  rw [characteristic_top_eq_circleAverage_add_circleAverage h₁f hR]
  simp [circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_pos h₂f]

/--
Qualitative version of **Cartan's formula**: Away from the point `0`, the difference between
`characteristic f ⊤` and `fun R ↦ circleAverage (logCounting f · R) 0 1` is constant. This
qualitative version of Cartan's formula exists because the specific value of the constant does not
matter in practice.
-/
/-
**ValueDistribution.characteristic_top_eq_circleAverage_add_const** 是 Mathlib 中的
一个定理，位于命名空间 `ValueDistribution`。
形式化陈述：characteristic_top_eq_circleAverage_add_const (h : Meromorphic f) : exists
 const, forall R != 0, characteristic f ⊤ R = circleAverage (logCounting f · R) 
0 1 + const
参数：h : Meromorphic f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `ValueDistribution.characteristic_top_eq_circleAverage_add_circleAverage`
：characteristic_top_eq_circleAverage_add_circleAverage (h : Meromorphic f) (hR :
 R != 0) : characteristic f ⊤ R = circleAverage (logCounting …

--- 原说明 ---
Qualitative version of **Cartan's formula**: Away from the point `0`, the differ
ence between
`characteristic f ⊤` and `fun R ↦ circleAverage (logCounting f · R) 0 1` is cons
tant. This
qualitative version of Cartan's formula exists because the specific value of the
 constant does not
matter in practice.
-/
theorem characteristic_top_eq_circleAverage_add_const (h : Meromorphic f) :
    ∃ const, ∀ R ≠ 0, characteristic f ⊤ R = circleAverage (logCounting f · R) 0 1 + const :=
  ⟨circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1,
    fun _ hr ↦ characteristic_top_eq_circleAverage_add_circleAverage h hr⟩

/-!
## Application: Monotonicity of the Characteristic Function
-/

/--
The characteristic function is monotone on `(0, ∞)`. This result is surprisingly non-trivial, given
that the proximity function is not monotone in general.
-/
/-
**ValueDistribution.characteristic_monotoneOn** 是 Mathlib 中的一个定理，位于命名空间 `ValueDi
stribution`。
形式化陈述：characteristic_monotoneOn (h : Meromorphic f) : MonotoneOn (characteristic
 f ⊤) (Set.Ioi 0)
参数：h : Meromorphic f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ValueDistribution.characteristic_top_eq_circleAverage_add_circleAverage`
：characteristic_top_eq_circleAverage_add_circleAverage (h : Meromorphic f) (hR :
 R != 0) : characteristic f ⊤ R = circleAverage (logCounting …
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Real.circleAverage_mono`：circleAverage_mono {c : Complex} {R : Real} {f₁
 f₂ : Complex -> Real} (hf₁ : CircleIntegrable f₁ c R) (hf₂ : CircleIntegrable f
₂ c R) (h : f…
· 使用定理 `ValueDistribution.circleIntegrable_logCounting`：circleIntegrable_logCoun
ting (h : Meromorphic f) : CircleIntegrable (logCounting f · R) 0 1
· 使用定理 `ValueDistribution.logCounting_monotoneOn`：logCounting_monotoneOn {f : 𝕜 
-> E} {e : WithTop E} : MonotoneOn (logCounting f e) (Ioi 0)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
The characteristic function is monotone on `(0, ∞)`. This result is surprisingly
 non-trivial, given
that the proximity function is not monotone in general.
-/
theorem characteristic_monotoneOn (h : Meromorphic f) :
    MonotoneOn (characteristic f ⊤) (Set.Ioi 0) := by
  intro a ha b hb hab
  rw [characteristic_top_eq_circleAverage_add_circleAverage h ha.ne',
    characteristic_top_eq_circleAverage_add_circleAverage h hb.ne']
  gcongr <;> try exact circleIntegrable_logCounting h
  exact logCounting_monotoneOn ha hb hab

end ValueDistribution

