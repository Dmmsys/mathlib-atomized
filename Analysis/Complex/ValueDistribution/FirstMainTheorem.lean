/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction

/-!
# The First Main Theorem of Value Distribution Theory

The First Main Theorem of Value Distribution Theory is a two-part statement, establishing invariance
of the characteristic function `characteristic f ⊤` under modifications of `f`.

- If `f` is meromorphic on the complex plane, then the characteristic functions for the value `⊤` of
  the function `f` and `f⁻¹` agree up to a constant, see Proposition 2.1 on p. 168 of [Lang,
  *Introduction to Complex Hyperbolic Spaces*][MR886677].

- If `f` is meromorphic on the complex plane, then the characteristic functions for the value `⊤` of
  the function `f` and `f - const` agree up to a constant, see Proposition 2.2 on p. 168 of [Lang,
  *Introduction to Complex Hyperbolic Spaces*][MR886677]

See Section VI.2 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] or Section 1.1 of
[Noguchi-Winkelmann, *Nevanlinna Theory in Several Complex Variables and Diophantine
Approximation*][MR3156076] for a detailed discussion.
-/

public section
namespace ValueDistribution

open Asymptotics Filter Function.locallyFinsuppWithin MeromorphicAt MeromorphicOn Metric Real

section FirstPart

variable {f : ℂ → ℂ} {R : ℝ}

/-!
## First Part of the First Main Theorem
-/

/--
Helper lemma for the first part of the First Main Theorem: Given a meromorphic function `f`, compute
difference between the characteristic functions of `f` and of its inverse.
-/
/-
**ValueDistribution.characteristic_sub_characteristic_inv** 是 Mathlib 中的一个引理，位于命
名空间 `ValueDistribution`。
形式化陈述：characteristic_sub_characteristic_inv (h : Meromorphic f) : characteristic
 f ⊤ - characteristic f⁻¹ ⊤ = circleAverage (log ‖f ·‖) 0 - (divisor f Set.univ)
.logCounting
参数：h : Meromorphic f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `ValueDistribution.proximity_sub_proximity_inv_eq_circleAverage`：proximit
y_sub_proximity_inv_eq_circleAverage {f : Complex -> Complex} (h₁f : Meromorphic
 f) : proximity f ⊤ - proximity f⁻¹ ⊤ = circleAverag…
· 使用定理 `ValueDistribution.logCounting_inv`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] [inst_1 : ProperSpace 𝕜] {f : 𝕜 → 𝕜},   ValueDistribution.logCoun
ting f⁻¹ ⊤ = ValueDistr…
· 使用定理 `ValueDistribution.log_counting_zero_sub_logCounting_top`：log_counting_ze
ro_sub_logCounting_top {f : 𝕜 -> E} : (divisor f univ).logCounting = logCounting
 f 0 - logCounting f ⊤

--- 原说明 ---
Helper lemma for the first part of the First Main Theorem: Given a meromorphic f
unction `f`, compute
difference between the characteristic functions of `f` and of its inverse.
-/
lemma characteristic_sub_characteristic_inv (h : Meromorphic f) :
    characteristic f ⊤ - characteristic f⁻¹ ⊤ =
      circleAverage (log ‖f ·‖) 0 - (divisor f Set.univ).logCounting := by
  calc characteristic f ⊤ - characteristic f⁻¹ ⊤
  _ = proximity f ⊤ - proximity f⁻¹ ⊤ - (logCounting f⁻¹ ⊤ - logCounting f ⊤) := by
    unfold characteristic
    ring
  _ = circleAverage (log ‖f ·‖) 0 - (logCounting f⁻¹ ⊤ - logCounting f ⊤) := by
    rw [proximity_sub_proximity_inv_eq_circleAverage h]
  _ = circleAverage (log ‖f ·‖) 0 - (logCounting f 0 - logCounting f ⊤) := by
    rw [logCounting_inv]
  _ = circleAverage (log ‖f ·‖) 0 - (divisor f Set.univ).logCounting := by
    rw [← ValueDistribution.log_counting_zero_sub_logCounting_top]

set_option backward.isDefEq.respectTransparency.types false in
/--
Helper lemma for the first part of the First Main Theorem: Away from zero, the difference between
the characteristic functions of `f` and `f⁻¹` equals `log ‖meromorphicTrailingCoeffAt f 0‖`.
-/
/-
**ValueDistribution.characteristic_sub_characteristic_inv_of_ne_zero** 是 Mathlib
 中的一个引理，位于命名空间 `ValueDistribution`。
形式化陈述：characteristic_sub_characteristic_inv_of_ne_zero (hf : Meromorphic f) (hR 
: R != 0) : characteristic f ⊤ R - characteristic f⁻¹ ⊤ R = log ‖meromorphicTrai
lingCoeffAt f 0‖
参数：hf : Meromorphic f；hR : R != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ValueDistribution.characteristic_sub_characteristic_inv`：characteristic_
sub_characteristic_inv (h : Meromorphic f) : characteristic f ⊤ - characteristic
 f⁻¹ ⊤ = circleAverage (log ‖f ·‖) 0 - (divis…
· 使用定理 `Pi.sub_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Sub 
(G i)] (f g : (i : ι) → G i) (i : ι), (f - g) i = f i - g i
· 使用定理 `MeromorphicOn.circleAverage_log_norm`：MeromorphicOn.circleAverage_log_no
rm {c : Complex} {R : Real} {f : Complex -> Complex} (hR : R != 0) (h₁f : Meromo
rphicOn f (closedBall c |R…
· 使用引理 `Meromorphic.meromorphicOn`：meromorphicOn {s : Set 𝕜} (hf : Meromorphic f
) : MeromorphicOn f s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `trivial`：True
· 使用定理 `MeromorphicOn.divisor_restrict`：divisor_restrict {f : 𝕜 -> E} {V : Set 𝕜
} (hf : MeromorphicOn f U) (hV : V subseteq U) : (divisor f U).restrict hV = div
isor f V
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `Int.cast_ite`：cast_ite [IntCast R] (P : Prop) [Decidable P] (m n : Int) 
: ((ite P m n : Int) : R) = ite P (m : R) (n : R)
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `ZeroHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Zero M]
 [inst_1 : Zero N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_ze
ro' : toFun…
· 使用定理 `AddMonoidHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Ad
dZero M] [inst_1 : AddZero N] (toZeroHom toZeroHom_1 : ZeroHom M N)   (e_toZeroH
om : toZeroHom =…
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b

--- 原说明 ---
Helper lemma for the first part of the First Main Theorem: Away from zero, the d
ifference between
the characteristic functions of `f` and `f⁻¹` equals `log ‖meromorphicTrailingCo
effAt f 0‖`.
-/
lemma characteristic_sub_characteristic_inv_of_ne_zero
    (hf : Meromorphic f) (hR : R ≠ 0) :
    characteristic f ⊤ R - characteristic f⁻¹ ⊤ R = log ‖meromorphicTrailingCoeffAt f 0‖ := by
  calc characteristic f ⊤ R - characteristic f⁻¹ ⊤ R
  _ = (characteristic f ⊤ - characteristic f⁻¹ ⊤) R := by simp
  _ = circleAverage (log ‖f ·‖) 0 R - (divisor f Set.univ).logCounting R := by
    rw [characteristic_sub_characteristic_inv hf, Pi.sub_apply]
  _ = log ‖meromorphicTrailingCoeffAt f 0‖ := by
    rw [MeromorphicOn.circleAverage_log_norm hR hf.meromorphicOn]
    unfold Function.locallyFinsuppWithin.logCounting
    have : (divisor f (closedBall 0 |R|)) = (divisor f Set.univ).toClosedBall R :=
      (divisor_restrict hf.meromorphicOn (by tauto)).symm
    simp [this, toClosedBall, restrictMonoidHom, restrict_apply]

/--
Helper lemma for the first part of the First Main Theorem: At 0, the difference between the
characteristic functions of `f` and `f⁻¹` equals `log ‖f 0‖`.
-/
/-
**ValueDistribution.characteristic_sub_characteristic_inv_at_zero** 是 Mathlib 中的
一个引理，位于命名空间 `ValueDistribution`。
形式化陈述：characteristic_sub_characteristic_inv_at_zero (h : Meromorphic f) : charac
teristic f ⊤ 0 - characteristic f⁻¹ ⊤ 0 = log ‖f 0‖
参数：h : Meromorphic f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ValueDistribution.characteristic_sub_characteristic_inv`：characteristic_
sub_characteristic_inv (h : Meromorphic f) : characteristic f ⊤ - characteristic
 f⁻¹ ⊤ = circleAverage (log ‖f ·‖) 0 - (divis…
· 使用定理 `Pi.sub_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Sub 
(G i)] (f g : (i : ι) → G i) (i : ι), (f - g) i = f i - g i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.circleAverage_zero`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] 
[inst_1 : NormedSpace ℝ E] {f : ℂ → E} {c : ℂ} [CompleteSpace E],   Real.circleA
verage f c 0 …
· 使用定理 `Function.locallyFinsuppWithin.logCounting_eval_zero`：∀ {E : Type u_2} [i
nst : NormedAddCommGroup E] [inst_1 : ProperSpace E] (D : Function.locallyFinsup
p E ℤ),   Function.locallyFinsuppWithin.l…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a

--- 原说明 ---
Helper lemma for the first part of the First Main Theorem: At 0, the difference 
between the
characteristic functions of `f` and `f⁻¹` equals `log ‖f 0‖`.
-/
lemma characteristic_sub_characteristic_inv_at_zero (h : Meromorphic f) :
    characteristic f ⊤ 0 - characteristic f⁻¹ ⊤ 0 = log ‖f 0‖ := by
  calc characteristic f ⊤ 0 - characteristic f⁻¹ ⊤ 0
  _ = (characteristic f ⊤ - characteristic f⁻¹ ⊤) 0 := by simp
  _ = circleAverage (log ‖f ·‖) 0 0 - (divisor f Set.univ).logCounting 0 := by
    rw [ValueDistribution.characteristic_sub_characteristic_inv h, Pi.sub_apply]
  _ = log ‖f 0‖ := by
    simp

/--
First part of the First Main Theorem, quantitative version: If `f` is meromorphic on the complex
plane, then the difference between the characteristic functions of `f` and `f⁻¹` is bounded by an
explicit constant.
-/
/-
**ValueDistribution.characteristic_sub_characteristic_inv_le** 是 Mathlib 中的一个定理，
位于命名空间 `ValueDistribution`。
形式化陈述：characteristic_sub_characteristic_inv_le (hf : Meromorphic f) : |character
istic f ⊤ R - characteristic f⁻¹ ⊤ R| <= max |log ‖f 0‖| |log ‖meromorphicTraili
ngCoeffAt f 0‖|
参数：hf : Meromorphic f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `ValueDistribution.characteristic_sub_characteristic_inv_at_zero`：charact
eristic_sub_characteristic_inv_at_zero (h : Meromorphic f) : characteristic f ⊤ 
0 - characteristic f⁻¹ ⊤ 0 = log ‖f 0‖
· 使用引理 `ValueDistribution.characteristic_sub_characteristic_inv_of_ne_zero`：char
acteristic_sub_characteristic_inv_of_ne_zero (hf : Meromorphic f) (hR : R != 0) 
: characteristic f ⊤ R - characteristic f⁻¹ ⊤ R = log ‖m…

--- 原说明 ---
First part of the First Main Theorem, quantitative version: If `f` is meromorphi
c on the complex
plane, then the difference between the characteristic functions of `f` and `f⁻¹`
 is bounded by an
explicit constant.
-/
theorem characteristic_sub_characteristic_inv_le (hf : Meromorphic f) :
    |characteristic f ⊤ R - characteristic f⁻¹ ⊤ R|
      ≤ max |log ‖f 0‖| |log ‖meromorphicTrailingCoeffAt f 0‖| := by
  by_cases h : R = 0
  · simp [h, characteristic_sub_characteristic_inv_at_zero hf]
  · simp [characteristic_sub_characteristic_inv_of_ne_zero hf h]

/--
First part of the First Main Theorem, qualitative version: If `f` is meromorphic on the complex
plane, then the characteristic functions of `f` and `f⁻¹` agree asymptotically up to a bounded
function.
-/
/-
**ValueDistribution.isBigO_characteristic_sub_characteristic_inv** 是 Mathlib 中的一
个定理，位于命名空间 `ValueDistribution`。
形式化陈述：isBigO_characteristic_sub_characteristic_inv (h : Meromorphic f) : (charac
teristic f ⊤ - characteristic f⁻¹ ⊤) =O[atTop] (1 : Real -> Real)
参数：h : Meromorphic f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isBigO_of_le'`：isBigO_of_le' (hfg : forall x, ‖f x‖ <= c * ‖
g x‖) : f =O[l] g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `ValueDistribution.characteristic_sub_characteristic_inv_le`：characterist
ic_sub_characteristic_inv_le (hf : Meromorphic f) : |characteristic f ⊤ R - char
acteristic f⁻¹ ⊤ R| <= max |log ‖f 0‖| |log ‖mer…

--- 原说明 ---
First part of the First Main Theorem, qualitative version: If `f` is meromorphic
 on the complex
plane, then the characteristic functions of `f` and `f⁻¹` agree asymptotically u
p to a bounded
function.
-/
theorem isBigO_characteristic_sub_characteristic_inv (h : Meromorphic f) :
    (characteristic f ⊤ - characteristic f⁻¹ ⊤) =O[atTop] (1 : ℝ → ℝ) :=
  isBigO_of_le' (c := max |log ‖f 0‖| |log ‖meromorphicTrailingCoeffAt f 0‖|) _
    (fun R ↦ by simpa using characteristic_sub_characteristic_inv_le h (R := R))

end FirstPart

section SecondPart

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {a₀ : E} {f : ℂ → E}

/-!
## Second Part of the First Main Theorem
-/

/--
Second part of the First Main Theorem of Value Distribution Theory, quantitative version: If `f` is
meromorphic on the complex plane, then the characteristic functions (for value `⊤`) of `f` and
`f - a₀` differ at most by `log⁺ ‖a₀‖ + log 2`.
-/
/-
**ValueDistribution.abs_characteristic_sub_characteristic_shift_le** 是 Mathlib 中
的一个定理，位于命名空间 `ValueDistribution`。
形式化陈述：abs_characteristic_sub_characteristic_shift_le {r : Real} (h : Meromorphic
 f) : |characteristic f ⊤ r - characteristic (f · - a₀) ⊤ r| <= log⁺ ‖a₀‖ + log 
2
参数：h : Meromorphic f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicOn.circleIntegrable_posLog_norm`：MeromorphicOn.circleIntegrab
le_posLog_norm (hf : MeromorphicOn f (sphere c |R|)) : CircleIntegrable (log⁺ ‖f
 ·‖) c R
· 使用引理 `Meromorphic.meromorphicOn`：meromorphicOn {s : Set 𝕜} (hf : Meromorphic f
) : MeromorphicOn f s
· 使用定理 `MeromorphicOn.sub`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {
E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f g 
: 𝕜 → E…
· 使用引理 `MeromorphicOn.const`：const (e : E) {U : Set 𝕜} : MeromorphicOn (fun _ =>
 e) U
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Pi.sub_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Sub 
(G i)] (f g : (i : ι) → G i) (i : ι), (f - g) i = f i - g i
· 使用引理 `ValueDistribution.characteristic_sub_characteristic_eq_proximity_sub_pro
ximity`：characteristic_sub_characteristic_eq_proximity_sub_proximity (h : Meromo
rphic f) (a₀ : E) : characteristic f ⊤ - characteristic (f · - a₀) ⊤…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Real.circleAverage_sub`：circleAverage_sub (hf₁ : CircleIntegrable f₁ c R
) (hf₂ : CircleIntegrable f₂ c R) : circleAverage (f₁ - f₂) c R = circleAverage 
f₁ c R - cir…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Real.abs_circleAverage_le_circleAverage_abs`：abs_circleAverage_le_circle
Average_abs {f : Complex -> Real} : |circleAverage f c R| <= circleAverage |f| c
 R
· 使用定理 `Real.circleAverage_mono_on_of_le_circle`：circleAverage_mono_on_of_le_cir
cle {f : Complex -> Real} {a : Real} (hf : CircleIntegrable f c R) (h₂f : forall
 x in Metric.sphere c |R|, f …
· 使用定理 `CircleIntegrable.abs`：abs {f : Complex -> Real} (hf : CircleIntegrable f
 c R) : CircleIntegrable |f| c R
· 使用定理 `CircleIntegrable.sub`：sub (hf : CircleIntegrable f c R) (hg : CircleInte
grable g c R) : CircleIntegrable (f - g) c R
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用引理 `Real.posLog_norm_add_le`：posLog_norm_add_le {E : Type*} [SeminormedAddCo
mmGroup E] (a b : E) : log⁺ ‖a + b‖ <= log⁺ ‖a‖ + log⁺ ‖b‖ + log 2
· 使用定理 `abs_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], a ≤ 0 → |a| = -a
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
Second part of the First Main Theorem of Value Distribution Theory, quantitative
 version: If `f` is
meromorphic on the complex plane, then the characteristic functions (for value `
⊤`) of `f` and
`f - a₀` differ at most by `log⁺ ‖a₀‖ + log 2`.
-/
theorem abs_characteristic_sub_characteristic_shift_le {r : ℝ} (h : Meromorphic f) :
    |characteristic f ⊤ r - characteristic (f · - a₀) ⊤ r| ≤ log⁺ ‖a₀‖ + log 2 := by
  have h₁f : CircleIntegrable (fun x ↦ log⁺ ‖f x‖) 0 r :=
    h.meromorphicOn.circleIntegrable_posLog_norm
  have h₂f : CircleIntegrable (fun x ↦ log⁺ ‖f x - a₀‖) 0 r := by
    apply MeromorphicOn.circleIntegrable_posLog_norm
    apply h.meromorphicOn.sub (MeromorphicOn.const a₀)
  rw [← Pi.sub_apply, characteristic_sub_characteristic_eq_proximity_sub_proximity h]
  simp only [proximity, reduceDIte, Pi.sub_apply, ← circleAverage_sub h₁f h₂f]
  apply le_trans abs_circleAverage_le_circleAverage_abs
  apply circleAverage_mono_on_of_le_circle
  · apply (h₁f.sub h₂f).abs
  · intro θ hθ
    simp only [Pi.abs_apply, Pi.sub_apply]
    by_cases h : 0 ≤ log⁺ ‖f θ‖ - log⁺ ‖f θ - a₀‖
    · simpa [abs_of_nonneg h, sub_le_iff_le_add, add_comm (log⁺ ‖a₀‖ + log 2), ← add_assoc]
        using (posLog_norm_add_le (f θ - a₀) a₀)
    · simp only [abs_of_nonpos (le_of_not_ge h), neg_sub, tsub_le_iff_right,
        add_comm (log⁺ ‖a₀‖ + log 2), ← add_assoc]
      convert! posLog_norm_add_le (-f θ) a₀ using 2
      · rw [← norm_neg]
        abel_nf
      · simp

/--
Second part of the First Main Theorem of Value Distribution Theory, qualitative version: If `f` is
meromorphic on the complex plane, then the characteristic functions for the value `⊤` of the
function `f` and `f - a₀` agree asymptotically up to a bounded function.
-/
/-
**ValueDistribution.isBigO_characteristic_sub_characteristic_shift** 是 Mathlib 中
的一个定理，位于命名空间 `ValueDistribution`。
形式化陈述：isBigO_characteristic_sub_characteristic_shift (h : Meromorphic f) : (char
acteristic f ⊤ - characteristic (f · - a₀) ⊤) =O[atTop] (1 : Real -> Real)
参数：h : Meromorphic f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isBigO_of_le'`：isBigO_of_le' (hfg : forall x, ‖f x‖ <= c * ‖
g x‖) : f =O[l] g
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `ValueDistribution.abs_characteristic_sub_characteristic_shift_le`：abs_ch
aracteristic_sub_characteristic_shift_le {r : Real} (h : Meromorphic f) : |chara
cteristic f ⊤ r - characteristic (f · - a₀) ⊤ r| <= lo…

--- 原说明 ---
Second part of the First Main Theorem of Value Distribution Theory, qualitative 
version: If `f` is
meromorphic on the complex plane, then the characteristic functions for the valu
e `⊤` of the
function `f` and `f - a₀` agree asymptotically up to a bounded function.
-/
theorem isBigO_characteristic_sub_characteristic_shift (h : Meromorphic f) :
    (characteristic f ⊤ - characteristic (f · - a₀) ⊤) =O[atTop] (1 : ℝ → ℝ) :=
  isBigO_of_le' (c := log⁺ ‖a₀‖ + log 2) _
    (fun R ↦ by simpa using abs_characteristic_sub_characteristic_shift_le h)

end SecondPart

end ValueDistribution

