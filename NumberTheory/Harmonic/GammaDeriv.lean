/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Derivative of Γ at positive integers

We prove the formula for the derivative of `Real.Gamma` at a positive integer:

`deriv Real.Gamma (n + 1) = Nat.factorial n * (-Real.eulerMascheroniConstant + harmonic n)`

-/

public section

open Nat Set Filter Topology

local notation "γ" => Real.eulerMascheroniConstant

namespace Real

/-- Explicit formula for the derivative of the Gamma function at positive integers, in terms of
harmonic numbers and the Euler-Mascheroni constant `γ`. -/
/-
**Real.deriv_Gamma_nat** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：deriv_Gamma_nat (n : Nat) : deriv Gamma (n + 1) = n ! * (-γ + harmonic n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.convexOn_log_Gamma`：convexOn_log_Gamma : ConvexOn Real (Ioi 0) (log
 ∘ Gamma)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Gamma_add_one`：Gamma_add_one {s : Real} (hs : s != 0) : Gamma (s + 
1) = s * Gamma s
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.log_mul`：log_mul (hx : x != 0) (hy : y != 0) : log (x * y) = log x 
+ log y
· 使用定理 `Real.Gamma_pos_of_pos`：Gamma_pos_of_pos {s : Real} (hs : 0 < s) : 0 < Ga
mma s
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DifferentiableAt.log`：DifferentiableAt.log (hf : DifferentiableAt Real f
 x) (hx : f x != 0) : DifferentiableAt Real (fun x => log (f x)) x
· 使用定理 `Real.differentiableAt_Gamma`：differentiableAt_Gamma {s : Real} (hs : for
all m : Nat, s != -m) : DifferentiableAt Real Gamma s
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
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
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
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
（共 136 条，此处仅展示前 30 条）

--- 原说明 ---
Explicit formula for the derivative of the Gamma function at positive integers, 
in terms of
harmonic numbers and the Euler-Mascheroni constant `γ`.
-/
lemma deriv_Gamma_nat (n : ℕ) :
    deriv Gamma (n + 1) = n ! * (-γ + harmonic n) := by
  /- This follows from two properties of the function `f n = log (Gamma n)`:
  firstly, the elementary computation that `deriv f (n + 1) = deriv f n + 1 / n`, so that
  `deriv f n = deriv f 1 + harmonic n`; secondly, the convexity of `f` (the Bohr-Mollerup theorem),
  which shows that `deriv f n` is `log n + o(1)` as `n → ∞`. -/
  let f := log ∘ Gamma
  -- First reduce to computing derivative of `log ∘ Gamma`.
  suffices deriv (log ∘ Gamma) (n + 1) = -γ + harmonic n by
    rwa [Function.comp_def, deriv.log (differentiableAt_Gamma (fun m ↦ by linarith))
      (by positivity), Gamma_nat_eq_factorial, div_eq_iff_mul_eq (by positivity),
      mul_comm, Eq.comm] at this
  have hc : ConvexOn ℝ (Ioi 0) f := convexOn_log_Gamma
  have h_rec (x : ℝ) (hx : 0 < x) : f (x + 1) = f x + log x := by simp only [f, Function.comp_apply,
      Gamma_add_one hx.ne', log_mul hx.ne' (Gamma_pos_of_pos hx).ne', add_comm]
  have hder {x : ℝ} (hx : 0 < x) : DifferentiableAt ℝ f x := by
    refine ((differentiableAt_Gamma ?_).log (Gamma_ne_zero ?_)) <;>
    exact fun m ↦ ne_of_gt (by linarith)
  -- Express derivative at general `n` in terms of value at `1` using recurrence relation
  have hder_rec (x : ℝ) (hx : 0 < x) : deriv f (x + 1) = deriv f x + 1 / x := by
    rw [← deriv_comp_add_const, one_div, ← deriv_log,
      ← deriv_add (hder <| by positivity) (differentiableAt_log hx.ne')]
    apply EventuallyEq.deriv_eq
    filter_upwards [eventually_gt_nhds hx] using h_rec
  have hder_nat (n : ℕ) : deriv f (n + 1) = deriv f 1 + harmonic n := by
    induction n with
    | zero => simp
    | succ n hn =>
      rw [cast_succ, hder_rec (n + 1) (by positivity), hn, harmonic_succ]
      push_cast
      ring
  suffices -deriv f 1 = γ by rw [hder_nat n, ← this, neg_neg]
  -- Use convexity to show derivative of `f` at `n + 1` is between `log n` and `log (n + 1)`
  have derivLB (n : ℕ) (hn : 0 < n) : log n ≤ deriv f (n + 1) := by
    refine (le_of_eq ?_).trans <| hc.slope_le_deriv (mem_Ioi.mpr <| Nat.cast_pos.mpr hn)
      (by positivity : _ < (_ : ℝ)) (by linarith) (hder <| by positivity)
    rw [slope_def_field, show n + 1 - n = (1 : ℝ) by ring, div_one, h_rec n (by positivity),
      add_sub_cancel_left]
  have derivUB (n : ℕ) : deriv f (n + 1) ≤ log (n + 1) := by
    refine (hc.deriv_le_slope (by positivity : (0 : ℝ) < n + 1) (by positivity : (0 : ℝ) < n + 2)
        (by linarith) (hder <| by positivity)).trans (le_of_eq ?_)
    rw [slope_def_field, show n + 2 - (n + 1) = (1 : ℝ) by ring, div_one,
      show n + 2 = (n + 1) + (1 : ℝ) by ring, h_rec (n + 1) (by positivity), add_sub_cancel_left]
  -- deduce `-deriv f 1` is bounded above + below by sequences which both tend to `γ`
  apply le_antisymm
  · apply ge_of_tendsto tendsto_harmonic_sub_log
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [le_sub_iff_add_le', ← sub_eq_add_neg, sub_le_iff_le_add', ← hder_nat]
    exact derivLB n hn
  · apply le_of_tendsto tendsto_harmonic_sub_log_add_one
    filter_upwards with n
    rw [sub_le_iff_le_add', ← sub_eq_add_neg, le_sub_iff_add_le', ← hder_nat]
    exact derivUB n
/-
**Real.hasDerivAt_Gamma_nat** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：hasDerivAt_Gamma_nat (n : Nat) : HasDerivAt Gamma (n ! * (-γ + harmonic n)
) (n + 1)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
· 使用定理 `Real.differentiableAt_Gamma`：differentiableAt_Gamma {s : Real} (hs : for
all m : Nat, s != -m) : DifferentiableAt Real Gamma s
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
（共 45 条，此处仅展示前 30 条）
-/
lemma hasDerivAt_Gamma_nat (n : ℕ) :
    HasDerivAt Gamma (n ! * (-γ + harmonic n)) (n + 1) :=
  (deriv_Gamma_nat n).symm ▸
    (differentiableAt_Gamma fun m ↦ (by linarith : (n : ℝ) + 1 ≠ -m)).hasDerivAt
/-
**Real.eulerMascheroniConstant_eq_neg_deriv** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：eulerMascheroniConstant_eq_neg_deriv : γ = -deriv Gamma 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Real.deriv_Gamma_nat`：deriv_Gamma_nat (n : Nat) : deriv Gamma (n + 1) = 
n ! * (-γ + harmonic n)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Rat.cast_zero`：cast_zero : ((0 : Rat) : α) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
lemma eulerMascheroniConstant_eq_neg_deriv : γ = -deriv Gamma 1 := by
  rw [show (1 : ℝ) = ↑(0 : ℕ) + 1 by simp, deriv_Gamma_nat 0]
  simp
/-
**Real.hasDerivAt_Gamma_one** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：hasDerivAt_Gamma_one : HasDerivAt Gamma (-γ) 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Rat.cast_zero`：cast_zero : ((0 : Rat) : α) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `Real.hasDerivAt_Gamma_nat`：hasDerivAt_Gamma_nat (n : Nat) : HasDerivAt G
amma (n ! * (-γ + harmonic n)) (n + 1)
-/
lemma hasDerivAt_Gamma_one : HasDerivAt Gamma (-γ) 1 := by
  simpa only [factorial_zero, cast_one, harmonic_zero, Rat.cast_zero, add_zero, mul_neg, one_mul,
    cast_zero, zero_add] using hasDerivAt_Gamma_nat 0
/-
**Real.hasDerivAt_Gamma_one_half** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：hasDerivAt_Gamma_one_half : HasDerivAt Gamma (-√π * (γ + 2 * log 2)) (1 / 
2)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.differentiableAt_Gamma`：differentiableAt_Gamma {s : Real} (hs : for
all m : Nat, s != -m) : DifferentiableAt Real Gamma s
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonpos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, -a ≤ 0 ↔ 0 ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `two_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `DifferentiableAt.const_mul`：DifferentiableAt.const_mul (ha : Differentia
bleAt 𝕜 a x) (b : 𝔸) : DifferentiableAt 𝕜 (fun y => b * a y) x
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x
· 使用定理 `HasDerivAt.congr_deriv`：HasDerivAt.congr_deriv (h : HasDerivAt f f' x) (
h' : f' = g') : HasDerivAt f g' x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
· 使用定理 `one_half_pos`：one_half_pos : (0 : α) < 1 / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_fun_mul`：deriv_fun_mul (hc : DifferentiableAt 𝕜 c x) (hd : Differe
ntiableAt 𝕜 d x) : deriv (fun y => c y * d y) x = deriv c x * d x + c x * deriv 
d x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用引理 `HasDerivAt.comp_add_const`：HasDerivAt.comp_add_const (x a : 𝕜) (hf : Has
DerivAt f f' (x + a)) : HasDerivAt (fun x => f (x + a)) f' x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.Gamma_one_half_eq`：Real.Gamma_one_half_eq : Real.Gamma (1 / 2) = √π
（共 119 条，此处仅展示前 30 条）
-/
lemma hasDerivAt_Gamma_one_half : HasDerivAt Gamma (-√π * (γ + 2 * log 2)) (1 / 2) := by
  have h_diff {s : ℝ} (hs : 0 < s) : DifferentiableAt ℝ Gamma s :=
    differentiableAt_Gamma fun m ↦ ((neg_nonpos.mpr m.cast_nonneg).trans_lt hs).ne'
  have h_diff' {s : ℝ} (hs : 0 < s) : DifferentiableAt ℝ (fun s ↦ Gamma (2 * s)) s :=
    .comp (g := Gamma) _ (h_diff <| mul_pos two_pos hs) (differentiableAt_id.const_mul _)
  refine (h_diff one_half_pos).hasDerivAt.congr_deriv ?_
  -- We calculate the deriv of Gamma at 1/2 using the doubling formula, since we already know
  -- the derivative of Gamma at 1.
  calc deriv Gamma (1 / 2)
  _ = (deriv (fun s ↦ Gamma s * Gamma (s + 1 / 2)) (1 / 2)) + √π * γ := by
    rw [deriv_fun_mul, Gamma_one_half_eq,
      add_assoc, ← mul_add, deriv_comp_add_const,
      (by norm_num : 1 / 2 + 1 / 2 = (1 : ℝ)), Gamma_one, mul_one,
      eulerMascheroniConstant_eq_neg_deriv, add_neg_cancel, mul_zero, add_zero]
    · apply h_diff; simp -- s = 1
    · exact ((h_diff (by simp)).hasDerivAt.comp_add_const).differentiableAt -- s = 1
  _ = (deriv (fun s ↦ Gamma (2 * s) * 2 ^ (1 - 2 * s) * √π) (1 / 2)) + √π * γ := by
    rw [funext Gamma_mul_Gamma_add_half]
  _ = √π * (deriv (fun s ↦ Gamma (2 * s) * 2 ^ (1 - 2 * s)) (1 / 2) + γ) := by
    rw [mul_comm √π, mul_comm √π, deriv_mul_const, add_mul]
    apply DifferentiableAt.mul
    · exact .comp (g := Gamma) _ (by apply h_diff; simp) -- s = 1
        (differentiableAt_id.const_mul _)
    · exact (differentiableAt_const _).rpow (by fun_prop) two_ne_zero
  _ = √π * (deriv (fun s ↦ Gamma (2 * s)) (1 / 2) +
              deriv (fun s : ℝ ↦ 2 ^ (1 - 2 * s)) (1 / 2) + γ) := by
    rw [deriv_fun_mul]
    · simp
    · exact h_diff' one_half_pos
    · exact DifferentiableAt.rpow (by fun_prop) (by fun_prop) two_ne_zero
  _ = √π * (-2 * γ + deriv (fun s : ℝ ↦ 2 ^ (1 - 2 * s)) (1 / 2) + γ) := by
    congr 3
    change deriv (Gamma ∘ fun s ↦ 2 * s) _ = _
    rw [deriv_comp, deriv_const_mul_id, mul_one_div, div_self two_ne_zero]
    · rw [mul_comm, hasDerivAt_Gamma_one.deriv, mul_neg, neg_mul]
    · apply h_diff; simp -- s = 1
    · fun_prop
  _ = √π * (-2 * γ + -(2 * log 2) + γ) := by
    congr 3
    apply HasDerivAt.deriv
    have := HasDerivAt.rpow (hasDerivAt_const (1 / 2 : ℝ) (2 : ℝ))
      (?_ : HasDerivAt (fun s : ℝ ↦ 1 - 2 * s) (-2) (1 / 2)) two_pos
    · simpa
    simp_rw [mul_comm (2 : ℝ) _]
    apply HasDerivAt.const_sub
    exact hasDerivAt_mul_const (2 : ℝ)
  _ = -√π * (γ + 2 * log 2) := by ring

end Real

namespace Complex

open scoped Real

/-
**Complex.HasDerivAt.complex_of_real** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma HasDerivAt.complex_of_real {f : ℂ → ℂ} {g : ℝ → ℝ} {g' s : ℝ}
    (hf : DifferentiableAt ℂ f s) (hg : HasDerivAt g g' s) (hfg : ∀ s : ℝ, f ↑s = ↑(g s)) :
    HasDerivAt f ↑g' s := by
  refine HasDerivAt.congr_deriv hf.hasDerivAt ?_
  rw [← (funext hfg ▸ hf.hasDerivAt.comp_ofReal.deriv :)]
  exact hg.ofReal_comp.deriv
/-
**Complex.differentiableAt_Gamma_nat_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Complex`
。
形式化陈述：differentiableAt_Gamma_nat_add_one (n : Nat) : DifferentiableAt Complex Ga
mma (n + 1)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.differentiableAt_Gamma`：differentiableAt_Gamma (s : Complex) (hs
 : forall m : Nat, s != -m) : DifferentiableAt Complex Gamma s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Right.add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α]
 [inst_1 : Preorder α] [AddRightMono α] {a b : α}, 0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
lemma differentiableAt_Gamma_nat_add_one (n : ℕ) :
    DifferentiableAt ℂ Gamma (n + 1) := by
  refine differentiableAt_Gamma _ (fun m ↦ ?_)
  simp only [Ne, ← ofReal_natCast, ← ofReal_one, ← ofReal_add, ← ofReal_neg, ofReal_inj,
    eq_neg_iff_add_eq_zero]
  positivity
/-
**Complex.hasDerivAt_Gamma_nat** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：hasDerivAt_Gamma_nat (n : Nat) : HasDerivAt Gamma (n ! * (-γ + harmonic n)
) (n + 1)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
· 使用定理 `_private.Mathlib.NumberTheory.Harmonic.GammaDeriv.0.Complex.HasDerivAt.c
omplex_of_real`：∀ {f : ℂ → ℂ} {g : ℝ → ℝ} {g' s : ℝ},   DifferentiableAt ℂ f ↑s 
→ HasDerivAt g g' s → (∀ (s : ℝ), f ↑s = ↑(g s)) → HasDerivAt f ↑g' ↑s
· 使用引理 `Complex.differentiableAt_Gamma_nat_add_one`：differentiableAt_Gamma_nat_a
dd_one (n : Nat) : DifferentiableAt Complex Gamma (n + 1)
· 使用引理 `Real.hasDerivAt_Gamma_nat`：hasDerivAt_Gamma_nat (n : Nat) : HasDerivAt G
amma (n ! * (-γ + harmonic n)) (n + 1)
· 使用定理 `Complex.Gamma_ofReal`：∀ (s : ℝ), Complex.Gamma ↑s = ↑(Real.Gamma s)
-/
lemma hasDerivAt_Gamma_nat (n : ℕ) :
    HasDerivAt Gamma (n ! * (-γ + harmonic n)) (n + 1) := by
  exact_mod_cast HasDerivAt.complex_of_real
    (by exact_mod_cast differentiableAt_Gamma_nat_add_one n)
    (Real.hasDerivAt_Gamma_nat n) Gamma_ofReal

/-- Explicit formula for the derivative of the complex Gamma function at positive integers, in
terms of harmonic numbers and the Euler-Mascheroni constant `γ`. -/
/-
**Complex.deriv_Gamma_nat** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：deriv_Gamma_nat (n : Nat) : deriv Gamma (n + 1) = n ! * (-γ + harmonic n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用引理 `Complex.hasDerivAt_Gamma_nat`：hasDerivAt_Gamma_nat (n : Nat) : HasDerivA
t Gamma (n ! * (-γ + harmonic n)) (n + 1)

--- 原说明 ---
Explicit formula for the derivative of the complex Gamma function at positive in
tegers, in
terms of harmonic numbers and the Euler-Mascheroni constant `γ`.
-/
lemma deriv_Gamma_nat (n : ℕ) :
    deriv Gamma (n + 1) = n ! * (-γ + harmonic n) :=
  (hasDerivAt_Gamma_nat n).deriv
/-
**Complex.hasDerivAt_Gamma_one** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：hasDerivAt_Gamma_one : HasDerivAt Gamma (-γ) 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Rat.cast_zero`：cast_zero : ((0 : Rat) : α) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `Complex.hasDerivAt_Gamma_nat`：hasDerivAt_Gamma_nat (n : Nat) : HasDerivA
t Gamma (n ! * (-γ + harmonic n)) (n + 1)
-/
lemma hasDerivAt_Gamma_one : HasDerivAt Gamma (-γ) 1 := by
  simpa only [factorial_zero, cast_one, harmonic_zero, Rat.cast_zero, add_zero, mul_neg, one_mul,
    cast_zero, zero_add] using hasDerivAt_Gamma_nat 0
/-
**Complex.hasDerivAt_Gamma_one_half** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：hasDerivAt_Gamma_one_half : HasDerivAt Gamma (-√π * (γ + 2 * log 2)) (1 / 
2)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `_private.Mathlib.NumberTheory.Harmonic.GammaDeriv.0.Complex.HasDerivAt.c
omplex_of_real`：∀ {f : ℂ → ℂ} {g : ℝ → ℝ} {g' s : ℝ},   DifferentiableAt ℂ f ↑s 
→ HasDerivAt g g' s → (∀ (s : ℝ), f ↑s = ↑(g s)) → HasDerivAt f ↑g' ↑s
· 使用定理 `Complex.differentiableAt_Gamma`：differentiableAt_Gamma (s : Complex) (hs
 : forall m : Nat, s != -m) : DifferentiableAt Complex Gamma s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_natCast`：∀ (n : ℕ), ↑↑n = ↑n
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Complex.ofReal_inj`：ofReal_inj {z w : Real} : (z : Complex) = w ↔ z = w
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonpos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, -a ≤ 0 ↔ 0 ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `one_half_pos`：one_half_pos : (0 : α) < 1 / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Real.hasDerivAt_Gamma_one_half`：hasDerivAt_Gamma_one_half : HasDerivAt G
amma (-√π * (γ + 2 * log 2)) (1 / 2)
· 使用定理 `Complex.Gamma_ofReal`：∀ (s : ℝ), Complex.Gamma ↑s = ↑(Real.Gamma s)
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 34 条，此处仅展示前 30 条）
-/
lemma hasDerivAt_Gamma_one_half : HasDerivAt Gamma (-√π * (γ + 2 * log 2)) (1 / 2) := by
  have := HasDerivAt.complex_of_real
    (differentiableAt_Gamma _ ?_) Real.hasDerivAt_Gamma_one_half Gamma_ofReal
  · simpa only [neg_mul, one_div, ofReal_neg, ofReal_mul, ofReal_add, ofReal_ofNat, ofNat_log,
      ofReal_inv] using this
  · intro m
    rw [← ofReal_natCast, ← ofReal_neg, ne_eq, ofReal_inj]
    exact ((neg_nonpos.mpr m.cast_nonneg).trans_lt one_half_pos).ne'
/-
**Complex.hasDerivAt_Gamma** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasDerivAt_Gammaℂ_one : HasDerivAt Gammaℂ (-(γ + log (2 * π)) / π) 1 := by
  let f (s : ℂ) : ℂ := 2 * (2 * π) ^ (-s)
  have : HasDerivAt (fun s : ℂ ↦ 2 * (2 * π : ℂ) ^ (-s)) (-log (2 * π) / π) 1 := by
    have := (hasDerivAt_neg' (1 : ℂ)).const_cpow (c := 2 * π)
      (Or.inl (by exact_mod_cast Real.two_pi_pos.ne'))
    refine (this.const_mul 2).congr_deriv ?_
    rw [mul_neg_one, mul_neg, cpow_neg_one, ← div_eq_inv_mul, ← mul_div_assoc,
      mul_div_mul_left _ _ two_ne_zero, neg_div]
  have := this.mul hasDerivAt_Gamma_one
  rwa [Gamma_one, mul_one, cpow_neg_one, ← div_eq_mul_inv, ← div_div, div_self two_ne_zero,
    mul_comm (1 / _), mul_one_div, ← _root_.add_div, ← neg_add, add_comm] at this
/-
**Complex.hasDerivAt_Gamma** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasDerivAt_Gammaℝ_one : HasDerivAt Gammaℝ (-(γ + log (4 * π)) / 2) 1 := by
  let f (s : ℂ) : ℂ := π ^ (-s / 2)
  let g (s : ℂ) : ℂ := Gamma (s / 2)
  have aux : (π : ℂ) ^ (1 / 2 : ℂ) = ↑√π := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le, ofReal_div, ofReal_one, ofReal_ofNat]
  have aux2 : (√π : ℂ) ≠ 0 := by rw [ofReal_ne_zero]; positivity
  have hf : HasDerivAt f (-log π / 2 / √π) 1 := by
    have := ((hasDerivAt_neg (1 : ℂ)).div_const 2).const_cpow (c := π) (Or.inr (by simp))
    refine this.congr_deriv ?_
    rw [mul_assoc, ← mul_div_assoc, mul_neg_one, neg_div, cpow_neg, ← div_eq_inv_mul, aux]
  have hg : HasDerivAt g (-√π * (γ + 2 * log 2) / 2) 1 := by
    have := hasDerivAt_Gamma_one_half.comp 1 (?_ : HasDerivAt (fun s : ℂ ↦ s / 2) (1 / 2) 1)
    · rwa [mul_one_div] at this
    · exact (hasDerivAt_id _).div_const _
  refine HasDerivAt.congr_deriv (hf.mul hg) ?_
  simp only [f]
  rw [Gamma_one_half_eq, aux, div_mul_cancel₀ _ aux2, neg_div _ (1 : ℂ), cpow_neg, aux,
    mul_div_assoc, ← mul_assoc, mul_neg, inv_mul_cancel₀ aux2, neg_one_mul, ← neg_div,
    ← _root_.add_div, ← neg_add, add_comm, add_assoc, ← ofReal_log Real.pi_pos.le, ← ofReal_ofNat,
    ← ofReal_log zero_le_two,
    ← ofReal_mul, ← Nat.cast_ofNat (R := ℝ), ← Real.log_pow, ← ofReal_add,
    ← Real.log_mul (by positivity) (by positivity),
    Nat.cast_ofNat, ofReal_ofNat, ofReal_log (by positivity)]
  norm_num

end Complex

