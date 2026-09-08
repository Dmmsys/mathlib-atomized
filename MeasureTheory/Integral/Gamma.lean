/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Integrals involving the Gamma function

In this file, we collect several integrals over `ℝ` or `ℂ` that evaluate in terms of the
`Real.Gamma` function.

-/

public section

open Real Set MeasureTheory MeasureTheory.Measure

section real

/-
**integral_rpow_mul_exp_neg_rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integral_rpow_mul_exp_neg_rpow {p q : Real} (hp : 0 < p) (hq : -1 < q) : ∫
 x in Ioi (0 : Real), x ^ q * exp (-x ^ p) = (1 / p) * Gamma ((q + 1) / p)
参数：hp : 0 < p；hq : -1 < q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_comp_rpow_Ioi`：integral_comp_rpow_Ioi (g : Real -
> E) {p : Real} (hp : p != 0) : ∫ x in Ioi 0, (|p| * x ^ (p - 1)) • g (x ^ p) = 
∫ y in Ioi 0, g y
· 使用定理 `one_div_ne_zero`：one_div_ne_zero {a : G₀} (h : a != 0) : 1 / a != 0
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_eq_self`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOr
der G] [IsOrderedAddMonoid G] {a : G}, |a| = a ↔ 0 ≤ a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `one_div_pos`：one_div_pos : 0 < 1 / a ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
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
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用引理 `one_div_mul_cancel`：one_div_mul_cancel (h : a != 0) : 1 / a * a = 1
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `div_mul_eq_mul_div`：div_mul_eq_mul_div : a / b * c = a * c / b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Real.rpow_add`：rpow_add (hx : 0 < x) (y z : Real) : x ^ (y + z) = x ^ y 
* x ^ z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
（共 85 条，此处仅展示前 30 条）
-/
theorem integral_rpow_mul_exp_neg_rpow {p q : ℝ} (hp : 0 < p) (hq : -1 < q) :
    ∫ x in Ioi (0 : ℝ), x ^ q * exp (-x ^ p) = (1 / p) * Gamma ((q + 1) / p) := by
  calc
    _ = ∫ (x : ℝ) in Ioi 0, (1 / p * x ^ (1 / p - 1)) • ((x ^ (1 / p)) ^ q * exp (-x)) := by
      rw [← integral_comp_rpow_Ioi _ (one_div_ne_zero (ne_of_gt hp)),
        abs_eq_self.mpr (le_of_lt (one_div_pos.mpr hp))]
      refine setIntegral_congr_fun measurableSet_Ioi (fun _ hx => ?_)
      rw [← rpow_mul (le_of_lt hx) _ p, one_div_mul_cancel (ne_of_gt hp), rpow_one]
    _ = ∫ (x : ℝ) in Ioi 0, 1 / p * exp (-x) * x ^ (1 / p - 1 + q / p) := by
      simp_rw [smul_eq_mul, mul_assoc]
      refine setIntegral_congr_fun measurableSet_Ioi (fun _ hx => ?_)
      rw [← rpow_mul (le_of_lt hx), div_mul_eq_mul_div, one_mul, rpow_add hx]
      ring_nf
    _ = (1 / p) * Gamma ((q + 1) / p) := by
      rw [Gamma_eq_integral (div_pos (neg_lt_iff_pos_add.mp hq) hp)]
      simp_rw [show 1 / p - 1 + q / p = (q + 1) / p - 1 by ring, ← integral_const_mul,
        ← mul_assoc]
/-
**integral_rpow_mul_exp_neg_mul_rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integral_rpow_mul_exp_neg_mul_rpow {p q b : Real} (hp : 0 < p) (hq : -1 < 
q) (hb : 0 < b) : ∫ x in Ioi (0 : Real), x ^ q * exp (-b * x ^ p) = b ^ (-(q + 1
) / p) * (1 / p) * Gamma ((q + 1) / p)
参数：hp : 0 < p；hq : -1 < q；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.mul_rpow`：mul_rpow (hx : 0 <= x) (hy : 0 <= y) : (x * y) ^ z = x ^ 
z * y ^ z
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Real.rpow_add`：rpow_add (hx : 0 < x) (y z : Real) : x ^ (y + z) = x ^ y 
* x ^ z
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MeasureTheory.integral_comp_mul_left_Ioi`：integral_comp_mul_left_Ioi (g 
: Real -> E) (a : Real) {b : Real} (hb : 0 < b) : ∫ x in Ioi a, g (b * x) = b⁻¹ 
• ∫ x in Ioi (b * a), g x
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `MeasureTheory.integral_const_mul`：integral_const_mul {L : Type*} [RCLike
 L] (r : L) (f : α -> L) : ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ
· 使用定理 `integral_rpow_mul_exp_neg_rpow`：integral_rpow_mul_exp_neg_rpow {p q : Re
al} (hp : 0 < p) (hq : -1 < q) : ∫ x in Ioi (0 : Real), x ^ q * exp (-x ^ p) = (
1 / p) * Gamma ((q +…
· 使用定理 `Real.rpow_neg_one`：rpow_neg_one (x : Real) : x ^ (-1 : Real) = x⁻¹
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
（共 65 条，此处仅展示前 30 条）
-/
theorem integral_rpow_mul_exp_neg_mul_rpow {p q b : ℝ} (hp : 0 < p) (hq : -1 < q) (hb : 0 < b) :
    ∫ x in Ioi (0 : ℝ), x ^ q * exp (-b * x ^ p) =
      b ^ (-(q + 1) / p) * (1 / p) * Gamma ((q + 1) / p) := by
  calc
    _ = ∫ x in Ioi (0 : ℝ), b ^ (-p⁻¹ * q) * ((b ^ p⁻¹ * x) ^ q * rexp (-(b ^ p⁻¹ * x) ^ p)) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun _ hx => ?_)
      rw [mul_rpow _ (le_of_lt hx), mul_rpow _ (le_of_lt hx), ← rpow_mul, ← rpow_mul,
        inv_mul_cancel₀, rpow_one, mul_assoc, ← mul_assoc, ← rpow_add, neg_mul p⁻¹, neg_add_cancel,
        rpow_zero, one_mul, neg_mul]
      all_goals positivity
    _ = (b ^ p⁻¹)⁻¹ * ∫ x in Ioi (0 : ℝ), b ^ (-p⁻¹ * q) * (x ^ q * rexp (-x ^ p)) := by
      rw [integral_comp_mul_left_Ioi (fun x => b ^ (-p⁻¹ * q) * (x ^ q * exp (-x ^ p))) 0,
        mul_zero, smul_eq_mul]
      all_goals positivity
    _ = b ^ (-(q + 1) / p) * (1 / p) * Gamma ((q + 1) / p) := by
      rw [integral_const_mul, integral_rpow_mul_exp_neg_rpow _ hq, mul_assoc, ← mul_assoc,
        ← rpow_neg_one, ← rpow_mul, ← rpow_add]
      · congr; ring
      all_goals positivity
/-
**integral_exp_neg_rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integral_exp_neg_rpow {p : Real} (hp : 0 < p) : ∫ x in Ioi (0 : Real), exp
 (-x ^ p) = Gamma (1 / p + 1)
参数：hp : 0 < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Real.Gamma_add_one`：Gamma_add_one {s : Real} (hs : s != 0) : Gamma (s + 
1) = s * Gamma s
· 使用定理 `one_div_ne_zero`：one_div_ne_zero {a : G₀} (h : a != 0) : 1 / a != 0
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `integral_rpow_mul_exp_neg_rpow`：integral_rpow_mul_exp_neg_rpow {p q : Re
al} (hp : 0 < p) (hq : -1 < q) : ∫ x in Ioi (0 : Real), x ^ q * exp (-x ^ p) = (
1 / p) * Gamma ((q +…
· 使用引理 `neg_one_lt_zero`：neg_one_lt_zero [ZeroLEOneClass R] [NeZero (1 : R)] [Ad
dLeftStrictMono R] : -1 < (0 : R)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem integral_exp_neg_rpow {p : ℝ} (hp : 0 < p) :
    ∫ x in Ioi (0 : ℝ), exp (-x ^ p) = Gamma (1 / p + 1) := by
  convert! (integral_rpow_mul_exp_neg_rpow hp neg_one_lt_zero) using 1
  · simp_rw [rpow_zero, one_mul]
  · rw [zero_add, Gamma_add_one (one_div_ne_zero (ne_of_gt hp))]
/-
**integral_exp_neg_mul_rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integral_exp_neg_mul_rpow {p b : Real} (hp : 0 < p) (hb : 0 < b) : ∫ x in 
Ioi (0 : Real), exp (-b * x ^ p) = b ^ (-1 / p) * Gamma (1 / p + 1)
参数：hp : 0 < p；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Real.Gamma_add_one`：Gamma_add_one {s : Real} (hs : s != 0) : Gamma (s + 
1) = s * Gamma s
· 使用定理 `one_div_ne_zero`：one_div_ne_zero {a : G₀} (h : a != 0) : 1 / a != 0
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `integral_rpow_mul_exp_neg_mul_rpow`：integral_rpow_mul_exp_neg_mul_rpow {
p q b : Real} (hp : 0 < p) (hq : -1 < q) (hb : 0 < b) : ∫ x in Ioi (0 : Real), x
 ^ q * exp (-b * x ^ p) …
· 使用引理 `neg_one_lt_zero`：neg_one_lt_zero [ZeroLEOneClass R] [NeZero (1 : R)] [Ad
dLeftStrictMono R] : -1 < (0 : R)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem integral_exp_neg_mul_rpow {p b : ℝ} (hp : 0 < p) (hb : 0 < b) :
    ∫ x in Ioi (0 : ℝ), exp (-b * x ^ p) = b ^ (-1 / p) * Gamma (1 / p + 1) := by
  convert! (integral_rpow_mul_exp_neg_mul_rpow hp neg_one_lt_zero hb) using 1
  · simp_rw [rpow_zero, one_mul]
  · rw [zero_add, Gamma_add_one (one_div_ne_zero (ne_of_gt hp)), mul_assoc]

end real

section complex

/-
**Complex.integral_rpow_mul_exp_neg_rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.integral_rpow_mul_exp_neg_rpow {p q : Real} (hp : 1 <= p) (hq : -2
 < q) : ∫ x : Complex, ‖x‖ ^ q * rexp (-‖x‖ ^ p) = (2 * π / p) * Real.Gamma ((q 
+ 2) / p)
参数：hp : 1 <= p；hq : -2 < q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.integral_comp_polarCoord_symm`：∀ {E : Type u_1} [inst : NormedAd
dCommGroup E] [inst_1 : NormedSpace ℝ E] (f : ℂ → E),   ∫ (p : ℝ × ℝ) in polarCo
ord.target, p.1 • f (↑Compl…
· 使用定理 `polarCoord_target`：polarCoord.target = Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) R
eal.pi
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.norm_polarCoord_symm`：norm_polarCoord_symm (p : Real × Real) : ‖
Complex.polarCoord.symm p‖ = |p.1|
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.setIntegral_prod_mul`：setIntegral_prod_mul {L : Type*} [RC
Like L] (f : α -> L) (g : β -> L) (s : Set α) (t : Set β) : ∫ z in s ×ˢ t, f z.1
 * g z.2 ∂μ.prod ν = (∫ …
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `MeasureTheory.Measure.volume_eq_prod`：volume_eq_prod (α β) [MeasureSpace
 α] [MeasureSpace β] : (volume : Measure (α × β)) = (volume : Measure α).prod (v
olume : Measure β)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
（共 111 条，此处仅展示前 30 条）
-/
theorem Complex.integral_rpow_mul_exp_neg_rpow {p q : ℝ} (hp : 1 ≤ p) (hq : -2 < q) :
    ∫ x : ℂ, ‖x‖ ^ q * rexp (-‖x‖ ^ p) = (2 * π / p) * Real.Gamma ((q + 2) / p) := by
  calc
    _ = ∫ x in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, x.1 * (|x.1| ^ q * rexp (-|x.1| ^ p)) := by
      rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
      simp_rw [Complex.norm_polarCoord_symm, smul_eq_mul]
    _ = (∫ x in Ioi (0 : ℝ), x * |x| ^ q * rexp (-|x| ^ p)) * ∫ _ in Ioo (-π) π, 1 := by
      rw [← setIntegral_prod_mul, volume_eq_prod]
      simp_rw [mul_one]
      congr! 2; ring
    _ = 2 * π * ∫ x in Ioi (0 : ℝ), x * |x| ^ q * rexp (-|x| ^ p) := by
      simp_rw [integral_const, measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter,
        volume_real_Ioo_of_le (a := -π) (b := π) (by linarith [pi_nonneg]),
        sub_neg_eq_add, ← two_mul, smul_eq_mul, mul_one, mul_comm]
    _ = 2 * π * ∫ x in Ioi (0 : ℝ), x ^ (q + 1) * rexp (-x ^ p) := by
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      rw [mem_Ioi] at hx
      rw [abs_eq_self.mpr hx.le, rpow_add hx, rpow_one]
      ring
    _ = (2 * Real.pi / p) * Real.Gamma ((q + 2) / p) := by
      rw [_root_.integral_rpow_mul_exp_neg_rpow (by linarith) (by linarith), add_assoc,
        one_add_one_eq_two]
      ring
/-
**Complex.integral_rpow_mul_exp_neg_mul_rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.integral_rpow_mul_exp_neg_mul_rpow {p q b : Real} (hp : 1 <= p) (h
q : -2 < q) (hb : 0 < b) : ∫ x : Complex, ‖x‖ ^ q * rexp (-b * ‖x‖ ^ p) = (2 * π
 / p) * b ^ (-(q + 2) / p) * Real.Gamma ((q + 2) / p)
参数：hp : 1 <= p；hq : -2 < q；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.integral_comp_polarCoord_symm`：∀ {E : Type u_1} [inst : NormedAd
dCommGroup E] [inst_1 : NormedSpace ℝ E] (f : ℂ → E),   ∫ (p : ℝ × ℝ) in polarCo
ord.target, p.1 • f (↑Compl…
· 使用定理 `polarCoord_target`：polarCoord.target = Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) R
eal.pi
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.norm_polarCoord_symm`：norm_polarCoord_symm (p : Real × Real) : ‖
Complex.polarCoord.symm p‖ = |p.1|
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.setIntegral_prod_mul`：setIntegral_prod_mul {L : Type*} [RC
Like L] (f : α -> L) (g : β -> L) (s : Set α) (t : Set β) : ∫ z in s ×ˢ t, f z.1
 * g z.2 ∂μ.prod ν = (∫ …
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `MeasureTheory.Measure.volume_eq_prod`：volume_eq_prod (α β) [MeasureSpace
 α] [MeasureSpace β] : (volume : Measure (α × β)) = (volume : Measure α).prod (v
olume : Measure β)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
（共 111 条，此处仅展示前 30 条）
-/
theorem Complex.integral_rpow_mul_exp_neg_mul_rpow {p q b : ℝ} (hp : 1 ≤ p) (hq : -2 < q)
    (hb : 0 < b) :
    ∫ x : ℂ, ‖x‖ ^ q * rexp (-b * ‖x‖ ^ p) = (2 * π / p) *
      b ^ (-(q + 2) / p) * Real.Gamma ((q + 2) / p) := by
  calc
    _ = ∫ x in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, x.1 * (|x.1| ^ q * rexp (-b * |x.1| ^ p)) := by
      rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
      simp_rw [Complex.norm_polarCoord_symm, smul_eq_mul]
    _ = (∫ x in Ioi (0 : ℝ), x * |x| ^ q * rexp (-b * |x| ^ p)) * ∫ _ in Ioo (-π) π, 1 := by
      rw [← setIntegral_prod_mul, volume_eq_prod]
      simp_rw [mul_one]
      congr! 2; ring
    _ = 2 * π * ∫ x in Ioi (0 : ℝ), x * |x| ^ q * rexp (-b * |x| ^ p) := by
      simp_rw [integral_const, measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter,
        volume_real_Ioo_of_le (a := -π) (b := π) (by linarith [pi_nonneg]),
        sub_neg_eq_add, ← two_mul, smul_eq_mul, mul_one, mul_comm]
    _ = 2 * π * ∫ x in Ioi (0 : ℝ), x ^ (q + 1) * rexp (-b * x ^ p) := by
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      rw [mem_Ioi] at hx
      rw [abs_eq_self.mpr hx.le, rpow_add hx, rpow_one]
      ring
    _ = (2 * π / p) * b ^ (-(q + 2) / p) * Real.Gamma ((q + 2) / p) := by
      rw [_root_.integral_rpow_mul_exp_neg_mul_rpow (by linarith) (by linarith) hb, add_assoc,
        one_add_one_eq_two]
      ring
/-
**Complex.integral_exp_neg_rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.integral_exp_neg_rpow {p : Real} (hp : 1 <= p) : ∫ x : Complex, re
xp (-‖x‖ ^ p) = π * Real.Gamma (2 / p + 1)
参数：hp : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Real.Gamma_add_one`：Gamma_add_one {s : Real} (hs : s != 0) : Gamma (s + 
1) = s * Gamma s
· 使用定理 `div_ne_zero`：div_ne_zero (ha : a != 0) (hb : b != 0) : a / b != 0
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
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
（共 74 条，此处仅展示前 30 条）
-/
theorem Complex.integral_exp_neg_rpow {p : ℝ} (hp : 1 ≤ p) :
    ∫ x : ℂ, rexp (-‖x‖ ^ p) = π * Real.Gamma (2 / p + 1) := by
  convert! (integral_rpow_mul_exp_neg_rpow hp (by linarith : (-2 : ℝ) < 0)) using 1
  · simp_rw [rpow_zero, one_mul]
  · rw [zero_add, Real.Gamma_add_one (div_ne_zero two_ne_zero (by linarith))]
    ring
/-
**Complex.integral_exp_neg_mul_rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.integral_exp_neg_mul_rpow {p b : Real} (hp : 1 <= p) (hb : 0 < b) 
: ∫ x : Complex, rexp (-b * ‖x‖ ^ p) = π * b ^ (-2 / p) * Real.Gamma (2 / p + 1)
参数：hp : 1 <= p；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Real.Gamma_add_one`：Gamma_add_one {s : Real} (hs : s != 0) : Gamma (s + 
1) = s * Gamma s
· 使用定理 `div_ne_zero`：div_ne_zero (ha : a != 0) (hb : b != 0) : a / b != 0
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
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
（共 74 条，此处仅展示前 30 条）
-/
theorem Complex.integral_exp_neg_mul_rpow {p b : ℝ} (hp : 1 ≤ p) (hb : 0 < b) :
    ∫ x : ℂ, rexp (-b * ‖x‖ ^ p) = π * b ^ (-2 / p) * Real.Gamma (2 / p + 1) := by
  convert! (integral_rpow_mul_exp_neg_mul_rpow hp (by linarith : (-2 : ℝ) < 0)) hb using 1
  · simp_rw [rpow_zero, one_mul]
  · rw [zero_add, Real.Gamma_add_one (div_ne_zero two_ne_zero (by linarith))]
    ring

end complex

