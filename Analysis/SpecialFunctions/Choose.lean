/-
Copyright (c) 2025 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Data.Nat.Cast.Field
import Mathlib.Analysis.Asymptotics.Theta

/-!
# Binomial coefficients and factorial variants

This file proves asymptotic theorems for binomial coefficients and factorial variants.

## Main statements

* `isEquivalent_descFactorial` is the proof that `n.descFactorial k ~ n^k` as `n → ∞`.
* `isEquivalent_choose` is the proof that `n.choose k ~ n^k / k!` as `n → ∞`.
* `isTheta_choose` is the proof that `n.choose k = Θ(n^k)` as `n → ∞`.
-/

public section


open Asymptotics Filter Nat Topology

/-- `n.descFactorial k` is asymptotically equivalent to `n^k`. -/
/-
**isEquivalent_descFactorial** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isEquivalent_descFactorial (k : Nat) : (fun (n : Nat) => (n.descFactorial 
k : Real)) ~[atTop] (fun (n : Nat) => (n ^ k : Real))
参数：k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Asymptotics.IsEquivalent.refl`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u : α → β} {l : Filter α}, Asymptotics.IsEquivalent l u u
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Asymptotics.IsEquivalent.mul`：∀ {α : Type u_1} {β : Type u_3} [inst : No
rmedField β] {t u v w : α → β} {l : Filter α},   Asymptotics.IsEquivalent l t u 
→ Asymptotics.IsEq…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Asymptotics.isEquivalent_iff_tendsto_one`：isEquivalent_iff_tendsto_one (
hz : forallᶠ x in l, v x != 0) : u ~[l] v ↔ Tendsto (u / v) l (𝓝 1)
· 使用定理 `Filter.tendsto_add_atTop_iff_nat`：tendsto_add_atTop_iff_nat {f : Nat -> 
α} {l : Filter α} (k : Nat) : Tendsto (fun n => f (n + k)) atTop l ↔ Tendsto f a
tTop l
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `tendsto_natCast_div_add_atTop`：tendsto_natCast_div_add_atTop {𝕜 : Type*}
 [DivisionSemiring 𝕜] [TopologicalSpace 𝕜] [CharZero 𝕜] [ContinuousSMul Rat>=0 𝕜
] [IsTopologicalSem…
· 使用定理 `NNRat.instContinuousSMulOfIsScalarTowerOfRat`：∀ {R : Type u_1} [inst : T
opologicalSpace R] [inst_1 : MulAction ℚ R] [inst_2 : MulAction ℚ≥0 R] [IsScalar
Tower ℚ≥0 ℚ R]   [ContinuousSMul ℚ…
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
`n.descFactorial k` is asymptotically equivalent to `n^k`.
-/
lemma isEquivalent_descFactorial (k : ℕ) :
    (fun (n : ℕ) ↦ (n.descFactorial k : ℝ)) ~[atTop] (fun (n : ℕ) ↦ (n ^ k : ℝ)) := by
  induction k with
  | zero => simpa using IsEquivalent.refl
  | succ k h =>
    simp_rw [descFactorial_succ, cast_mul, _root_.pow_succ']
    refine IsEquivalent.mul ?_ h
    have hz : ∀ᶠ (x : ℕ) in atTop, (x : ℝ) ≠ 0 :=
      eventually_atTop.mpr ⟨1, fun n hn ↦ ne_of_gt (mod_cast hn)⟩
    rw [isEquivalent_iff_tendsto_one hz, ← tendsto_add_atTop_iff_nat k]
    simpa using tendsto_natCast_div_add_atTop (k : ℝ)

/-- `n.choose k` is asymptotically equivalent to `n^k / k!`. -/
/-
**isEquivalent_choose** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isEquivalent_choose (k : Nat) : (fun (n : Nat) => (n.choose k : Real)) ~[a
tTop] (fun (n : Nat) => (n ^ k / k.factorial : Real))
参数：k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.choose_eq_descFactorial_div_factorial`：choose_eq_descFactorial_div_f
actorial (n k : Nat) : n.choose k = n.descFactorial k / k !
· 使用引理 `Nat.cast_div`：cast_div (hnm : n ∣ m) (hn : (n : K) != 0) : (↑(m / n) : K
) = m / n
· 使用定理 `Nat.factorial_dvd_descFactorial`：factorial_dvd_descFactorial (n k : Nat)
 : k ! ∣ n.descFactorial k
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `Asymptotics.IsEquivalent.div`：∀ {α : Type u_1} {β : Type u_3} [inst : No
rmedField β] {t u v w : α → β} {l : Filter α},   Asymptotics.IsEquivalent l t u 
→ Asymptotics.IsEq…
· 使用引理 `isEquivalent_descFactorial`：isEquivalent_descFactorial (k : Nat) : (fun 
(n : Nat) => (n.descFactorial k : Real)) ~[atTop] (fun (n : Nat) => (n ^ k : Rea
l))
· 使用定理 `Asymptotics.IsEquivalent.refl`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u : α → β} {l : Filter α}, Asymptotics.IsEquivalent l u u

--- 原说明 ---
`n.choose k` is asymptotically equivalent to `n^k / k!`.
-/
theorem isEquivalent_choose (k : ℕ) :
    (fun (n : ℕ) ↦ (n.choose k : ℝ)) ~[atTop] (fun (n : ℕ) ↦ (n ^ k / k.factorial : ℝ)) := by
  conv_lhs =>
    intro n
    rw [choose_eq_descFactorial_div_factorial,
      cast_div (n.factorial_dvd_descFactorial k) (mod_cast k.factorial_ne_zero)]
  exact (isEquivalent_descFactorial k).div IsEquivalent.refl

/-- `n.choose k` is big-theta `n^k`. -/
/-
**isTheta_choose** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isTheta_choose (k : Nat) : (fun (n : Nat) => (n.choose k : Real)) =Θ[atTop
] (fun (n : Nat) => (n ^ k : Real))
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.trans_isTheta`：∀ {α : Type u_1} {β : Type u_2} 
{β₂ : Type u_3} [inst : NormedAddCommGroup β] [inst_1 : Norm β₂] {l : Filter α} 
  {f g₁ : α → β} {g₂ : α → β…
· 使用定理 `isEquivalent_choose`：isEquivalent_choose (k : Nat) : (fun (n : Nat) => (
n.choose k : Real)) ~[atTop] (fun (n : Nat) => (n ^ k / k.factorial : Real))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Asymptotics.IsTheta.const_mul_left`：∀ {α : Type u_1} {F : Type u_4} {𝕜 :
 Type u_14} [inst : Norm F] [inst_1 : NormedField 𝕜] {g : α → F} {l : Filter α} 
  {c : 𝕜} {f : α → 𝕜}, c…
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `Asymptotics.isTheta_rfl`：isTheta_rfl : f =Θ[l] f

--- 原说明 ---
`n.choose k` is big-theta `n^k`.
-/
theorem isTheta_choose (k : ℕ) :
    (fun (n : ℕ) ↦ (n.choose k : ℝ)) =Θ[atTop] (fun (n : ℕ) ↦ (n ^ k : ℝ)) := by
  apply (isEquivalent_choose k).trans_isTheta
  simp_rw [div_eq_mul_inv, mul_comm _ (_⁻¹)]
  exact isTheta_rfl.const_mul_left <| inv_ne_zero (mod_cast k.factorial_ne_zero)
