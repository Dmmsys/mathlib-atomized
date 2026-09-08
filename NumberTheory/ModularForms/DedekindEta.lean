/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
module

public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable
public import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

/-!
# Dedekind eta function

## Main definitions

* We define the Dedekind eta function as the infinite product
  `η(z) = q ^ 1/24 * ∏' (1 - q ^ (n + 1))` where `q = e ^ (2πiz)` and `z` is in the upper
  half-plane. The product is taken over all non-negative integers `n`. We then show it is
  non-vanishing and differentiable on the upper half-plane. Lastly, we compute its logarithmic
  derivative and show that it is a multiple of the Eisenstein series `E2`.

## References
* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], section 1.2
-/

@[expose] public section

open Set Function Complex
open UpperHalfPlane hiding I
open scoped Real

local notation "𝕢" => Periodic.qParam

local notation "ℍₒ" => upperHalfPlaneSet

namespace ModularForm

/-- The q term inside the product defining the eta function. It is defined as
`eta_q n z = e ^ (2 π i (n + 1) z)`. -/
/-
**ModularForm.eta_q** 是 Mathlib 中的一个缩写定义，位于命名空间 `ModularForm`。
形式化陈述：eta_q (n : Nat) (z : Complex)
参数：n : Nat；z : Complex。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The q term inside the product defining the eta function. It is defined as
`eta_q n z = e ^ (2 π i (n + 1) z)`.
-/
noncomputable abbrev eta_q (n : ℕ) (z : ℂ) := (𝕢 1 z) ^ (n + 1)
/-
**ModularForm.eta_q_eq_cexp** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：eta_q_eq_cexp (n : Nat) (z : Complex) : eta_q n z = cexp (2 * π * I * (n +
 1) * z)
参数：n : Nat；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
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
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.RingNF.add_assoc_rev`：add_assoc_rev (a b c : R) : a + (b 
+ c) = a + b + c
（共 37 条，此处仅展示前 30 条）
-/
lemma eta_q_eq_cexp (n : ℕ) (z : ℂ) : eta_q n z = cexp (2 * π * I * (n + 1) * z) := by
  simp [eta_q, Periodic.qParam, ← Complex.exp_nsmul]
  ring_nf
/-
**ModularForm.eta_q_eq_pow** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：eta_q_eq_pow (n : Nat) (z : Complex) : eta_q n z = cexp (2 * π * I * z) ^ 
(n + 1)
参数：n : Nat；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eta_q_eq_pow (n : ℕ) (z : ℂ) : eta_q n z = cexp (2 * π * I * z) ^ (n + 1) := by
  simp [eta_q, Periodic.qParam]
/-
**ModularForm.one_sub_eta_q_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：one_sub_eta_q_ne_zero (n : Nat) {z : Complex} (hz : z in ℍₒ) : 1 - eta_q n
 z != 0
参数：n : Nat；hz : z in ℍₒ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ModularForm.eta_q_eq_cexp`：eta_q_eq_cexp (n : Nat) (z : Complex) : eta_q
 n z = cexp (2 * π * I * (n + 1) * z)
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `Right.add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α]
 [inst_1 : Preorder α] [AddRightMono α] {a b : α}, 0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `UpperHalfPlane.norm_exp_two_pi_I_lt_one`：UpperHalfPlane.norm_exp_two_pi_
I_lt_one (τ : ℍ) : ‖(Complex.exp (2 * π * Complex.I * τ))‖ < 1
-/
lemma one_sub_eta_q_ne_zero (n : ℕ) {z : ℂ} (hz : z ∈ ℍₒ) : 1 - eta_q n z ≠ 0 := by
  rw [eta_q_eq_cexp, sub_ne_zero]
  intro h
  simpa [← mul_assoc, ← h] using norm_exp_two_pi_I_lt_one ⟨(n + 1) • z, by
    simpa [(show 0 < (n + 1 : ℝ) by positivity)] using hz⟩

/-- The eta function, whose value at z is `q^ 1 / 24 * ∏' 1 - q ^ (n + 1)` for `q = e ^ 2 π i z`. -/
/-
**ModularForm.eta** 是 Mathlib 中的一个定义，位于命名空间 `ModularForm`。
形式化陈述：eta (z : Complex)
参数：z : Complex。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The eta function, whose value at z is `q^ 1 / 24 * ∏' 1 - q ^ (n + 1)` for `q = 
e ^ 2 π i z`.
-/
noncomputable def eta (z : ℂ) := 𝕢 24 z * ∏' n, (1 - eta_q n z)

/-- Notation for the Dedekind eta function. -/
scoped[ModularForm] notation "η" => eta

/-- For `‖q‖ < 1`, the infinite product `∏ (1 - q^(n+1))` is multipliable. -/
/-
**ModularForm.multipliable_one_sub_pow** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：multipliable_one_sub_pow {q : Complex} (hq : ‖q‖ < 1) : Multipliable fun n
 : Nat => 1 - q ^ (n + 1)
参数：hq : ‖q‖ < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `multipliable_one_add_of_summable`：multipliable_one_add_of_summable [Comp
leteSpace R] (hf : Summable fun i => ‖f i‖) : Multipliable fun i => (1 + f i)
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `summable_nat_add_iff`：∀ {G : Type u_2} [inst : AddCommGroup G] [inst_1 :
 TopologicalSpace G] [IsTopologicalAddGroup G] {f : ℕ → G} (k : ℕ),   (Summable 
fun n => f…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `summable_geometric_of_lt_one`：summable_geometric_of_lt_one {r : Real} (h
₁ : 0 <= r) (h₂ : r < 1) : Summable fun n : Nat => r ^ n
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖

--- 原说明 ---
For `‖q‖ < 1`, the infinite product `∏ (1 - q^(n+1))` is multipliable.
-/
lemma multipliable_one_sub_pow {q : ℂ} (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ ↦ 1 - q ^ (n + 1) := by
  apply multipliable_one_add_of_summable (f := fun n ↦ -q ^ (n + 1))
  simpa using (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _) hq)

/-- The infinite product `∏ (1 - q^(n+1))` converges locally uniformly on the open unit disc,
with limit `q ↦ ∏' n, (1 - q^(n+1))`. -/
/-
**ModularForm.multipliableLocallyUniformlyOn_one_sub_pow** 是 Mathlib 中的一个引理，位于命名
空间 `ModularForm`。
形式化陈述：multipliableLocallyUniformlyOn_one_sub_pow : MultipliableLocallyUniformlyO
n (fun n q => 1 - q ^ (n + 1)) (Metric.ball (0 : Complex) 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `hasProdLocallyUniformlyOn_of_forall_compact`：hasProdLocallyUniformlyOn_o
f_forall_compact (hs : IsOpen s) [LocallyCompactSpace β] (h : forall K subseteq 
s, IsCompact K -> HasProdUniforml…
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `tendstoUniformlyOn_empty`：tendstoUniformlyOn_empty : TendstoUniformlyOn 
F f p ∅
· 使用定理 `IsCompact.exists_sSup_image_eq_and_ge`：IsCompact.exists_sSup_image_eq_an
d_ge [ClosedIciTopology α] {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f
 : β -> α} (hf : Continuous…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `ContinuousOn.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAdd
Group E] [inst_1 : TopologicalSpace α] {f : α → E} {s : Set α},   ContinuousOn f
 s → Co…
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用引理 `Summable.hasProdUniformlyOn_nat_one_add`：hasProdUniformlyOn_nat_one_add 
{f : Nat -> α -> R} (hK : IsCompact K) {u : Nat -> Real} (hu : Summable u) (h : 
forallᶠ n in atTop, forall x …
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `summable_nat_add_iff`：∀ {G : Type u_2} [inst : AddCommGroup G] [inst_1 :
 TopologicalSpace G] [IsTopologicalAddGroup G] {f : ℕ → G} (k : ℕ),   (Summable 
fun n => f…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `summable_geometric_of_lt_one`：summable_geometric_of_lt_one {r : Real} (h
₁ : 0 <= r) (h₂ : r < 1) : Summable fun n : Nat => r ^ n
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
The infinite product `∏ (1 - q^(n+1))` converges locally uniformly on the open u
nit disc,
with limit `q ↦ ∏' n, (1 - q^(n+1))`.
-/
lemma multipliableLocallyUniformlyOn_one_sub_pow :
    MultipliableLocallyUniformlyOn (fun n q ↦ 1 - q ^ (n + 1)) (Metric.ball (0 : ℂ) 1) := by
  use fun q ↦ ∏' n, (1 - q ^ (n + 1))
  simp_rw [sub_eq_add_neg]
  apply hasProdLocallyUniformlyOn_of_forall_compact Metric.isOpen_ball
  intro K hK hcK
  rcases K.eq_empty_or_nonempty with hN | hN
  · simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn, hN] using tendstoUniformlyOn_empty
  · obtain ⟨q₀, hq₀, _, HB⟩ := hcK.exists_sSup_image_eq_and_ge hN
      (show ContinuousOn (fun q : ℂ ↦ ‖q‖) K by fun_prop)
    refine ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _)
      (by simpa [Metric.mem_ball, dist_zero_right] using hK hq₀))).hasProdUniformlyOn_nat_one_add
      hcK (.of_forall fun n x hx ↦ ?_) (fun _ ↦ by fun_prop)
    simpa using pow_le_pow_left₀ (norm_nonneg _) (HB x hx) (n + 1)

/-- The infinite product `q ↦ ∏' n, (1 - q^(n+1))` is differentiable on the open unit disc. -/
/-
**ModularForm.differentiableOn_tprod_one_sub_pow** 是 Mathlib 中的一个引理，位于命名空间 `Modu
larForm`。
形式化陈述：differentiableOn_tprod_one_sub_pow : DifferentiableOn Complex (fun q => ∏'
 n, (1 - q ^ (n + 1))) (Metric.ball (0 : Complex) 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoLocallyUniformlyOn.differentiableOn`：∀ {E : Type u_1} {ι : Type u
_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] {U : Set ℂ} {φ : Fi
lter ι}   {F : ι → ℂ → E} {f : ℂ…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MultipliableLocallyUniformlyOn.hasProdLocallyUniformlyOn`：MultipliableLo
callyUniformlyOn.hasProdLocallyUniformlyOn (h : MultipliableLocallyUniformlyOn f
 s) : HasProdLocallyUniformlyOn f (∏' i, f i ·…
· 使用引理 `ModularForm.multipliableLocallyUniformlyOn_one_sub_pow`：multipliableLoca
llyUniformlyOn_one_sub_pow : MultipliableLocallyUniformlyOn (fun n q => 1 - q ^ 
(n + 1)) (Metric.ball (0 : Complex) 1)
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_fn`：Finset.prod_fn {α : Type*} {M : α -> Type*} {ι} [forall 
a, CommMonoid (M a)] (s : Finset ι) (g : ι -> forall a, M a) : ∏ c in s, g c = f
un a…
· 使用定理 `DifferentiableOn.finsetProd`：DifferentiableOn.finsetProd (hd : forall i 
in u, DifferentiableOn 𝕜 (f i) s) : DifferentiableOn 𝕜 (∏ i in u, f i) s
· 使用定理 `DifferentiableOn.const_sub`：DifferentiableOn.const_sub (hf : Differentia
bleOn 𝕜 f s) (c : F) : DifferentiableOn 𝕜 (fun y => c - f y) s
· 使用定理 `DifferentiableOn.fun_pow`：∀ {𝕜 : Type u_1} {𝔸 : Type u_2} {E : Type u_3}
 [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedRing 𝔸]   [inst_2 : NormedAd
dCommGroup E] …
· 使用定理 `differentiableOn_id`：differentiableOn_id : DifferentiableOn 𝕜 id s
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)

--- 原说明 ---
The infinite product `q ↦ ∏' n, (1 - q^(n+1))` is differentiable on the open uni
t disc.
-/
lemma differentiableOn_tprod_one_sub_pow :
    DifferentiableOn ℂ (fun q ↦ ∏' n, (1 - q ^ (n + 1))) (Metric.ball (0 : ℂ) 1) :=
  multipliableLocallyUniformlyOn_one_sub_pow.hasProdLocallyUniformlyOn.differentiableOn
    (.of_forall fun _ ↦ by simpa [Finset.prod_fn] using
      DifferentiableOn.finsetProd (fun _ _ ↦ by fun_prop)) Metric.isOpen_ball

/-- For any `k`, the function `q ↦ ∏' n, (1 - q^(n+1))^k` is differentiable on the
open unit disc. -/
/-
**ModularForm.differentiableOn_tprod_one_sub_pow_pow** 是 Mathlib 中的一个引理，位于命名空间 `
ModularForm`。
形式化陈述：differentiableOn_tprod_one_sub_pow_pow (k : Nat) : DifferentiableOn Comple
x (fun q => ∏' n, (1 - q ^ (n + 1)) ^ k) (Metric.ball (0 : Complex) 1)
参数：k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.congr`：DifferentiableOn.congr (h : DifferentiableOn 𝕜 f
 s) (h' : forall x in s, f₁ x = f x) : DifferentiableOn 𝕜 f₁ s
· 使用定理 `DifferentiableOn.fun_pow`：∀ {𝕜 : Type u_1} {𝔸 : Type u_2} {E : Type u_3}
 [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedRing 𝔸]   [inst_2 : NormedAd
dCommGroup E] …
· 使用引理 `ModularForm.differentiableOn_tprod_one_sub_pow`：differentiableOn_tprod_o
ne_sub_pow : DifferentiableOn Complex (fun q => ∏' n, (1 - q ^ (n + 1))) (Metric
.ball (0 : Complex) 1)
· 使用引理 `Multipliable.tprod_pow`：Multipliable.tprod_pow [L.NeBot] (hf : Multiplia
ble f L) (n : Nat) : ∏'[L] b, (f b) ^ n = (∏'[L] b, f b) ^ n
· 使用定理 `Complex.instT2Space`：T2Space ℂ
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
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `ModularForm.multipliable_one_sub_pow`：multipliable_one_sub_pow {q : Comp
lex} (hq : ‖q‖ < 1) : Multipliable fun n : Nat => 1 - q ^ (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖

--- 原说明 ---
For any `k`, the function `q ↦ ∏' n, (1 - q^(n+1))^k` is differentiable on the
open unit disc.
-/
lemma differentiableOn_tprod_one_sub_pow_pow (k : ℕ) :
    DifferentiableOn ℂ (fun q ↦ ∏' n, (1 - q ^ (n + 1)) ^ k) (Metric.ball (0 : ℂ) 1) :=
  (differentiableOn_tprod_one_sub_pow.fun_pow k).congr fun _ hq ↦
    (multipliable_one_sub_pow (by simpa using hq)).tprod_pow k
/-
**ModularForm.summable_eta_q** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：summable_eta_q (z : ℍ) : Summable fun n => ‖-eta_q n z‖
参数：z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `abs_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (z : E), |‖z‖| 
= ‖z‖
· 使用定理 `summable_geometric_of_lt_one`：summable_geometric_of_lt_one {r : Real} (h
₁ : 0 <= r) (h₂ : r < 1) : Summable fun n : Nat => r ^ n
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `UpperHalfPlane.norm_qParam_lt_one`：UpperHalfPlane.norm_qParam_lt_one (n 
: Nat) [NeZero n] (τ : ℍ) : ‖𝕢 n τ‖ < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem summable_eta_q (z : ℍ) : Summable fun n ↦ ‖-eta_q n z‖ := by
  simpa [summable_nat_add_iff] using
    summable_geometric_of_lt_one (norm_nonneg _) (mod_cast norm_qParam_lt_one 1 z)
/-
**ModularForm.multipliableLocallyUniformlyOn_eta** 是 Mathlib 中的一个引理，位于命名空间 `Modu
larForm`。
形式化陈述：multipliableLocallyUniformlyOn_eta : MultipliableLocallyUniformlyOn (fun n
 a => 1 - eta_q n a) ℍₒ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultipliableLocallyUniformlyOn.comp`：MultipliableLocallyUniformlyOn.comp
 {γ : Type*} [TopologicalSpace γ] {t : Set γ} (h : MultipliableLocallyUniformlyO
n f s) (h' : γ -> β) (hh …
· 使用引理 `ModularForm.multipliableLocallyUniformlyOn_one_sub_pow`：multipliableLoca
llyUniformlyOn_one_sub_pow : MultipliableLocallyUniformlyOn (fun n q => 1 - q ^ 
(n + 1)) (Metric.ball (0 : Complex) 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `UpperHalfPlane.norm_qParam_lt_one`：UpperHalfPlane.norm_qParam_lt_one (n 
: Nat) [NeZero n] (τ : ℍ) : ‖𝕢 n τ‖ < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用引理 `Function.Periodic.continuous_qParam`：continuous_qParam : Continuous (𝕢 h
)
-/
lemma multipliableLocallyUniformlyOn_eta :
    MultipliableLocallyUniformlyOn (fun n a ↦ 1 - eta_q n a) ℍₒ :=
  multipliableLocallyUniformlyOn_one_sub_pow.comp (𝕢 1)
    (fun z hz ↦ by simpa using norm_qParam_lt_one 1 ⟨z, hz⟩) (by fun_prop)
/-
**ModularForm.eta_tprod_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：eta_tprod_ne_zero {z : Complex} (hz : z in ℍₒ) : ∏' n, (1 - eta_q n z) != 
0
参数：hz : z in ℍₒ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `tprod_one_add_ne_zero_of_summable`：tprod_one_add_ne_zero_of_summable [Co
mpleteSpace R] [NormMulClass R] (hf : forall i, 1 + f i != 0) (hu : Summable (‖f
 ·‖)) : ∏' i : ι, (1 + …
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `ModularForm.one_sub_eta_q_ne_zero`：one_sub_eta_q_ne_zero (n : Nat) {z : 
Complex} (hz : z in ℍₒ) : 1 - eta_q n z != 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `ModularForm.summable_eta_q`：summable_eta_q (z : ℍ) : Summable fun n => ‖
-eta_q n z‖
-/
lemma eta_tprod_ne_zero {z : ℂ} (hz : z ∈ ℍₒ) : ∏' n, (1 - eta_q n z) ≠ 0 := by
  refine tprod_one_add_ne_zero_of_summable (f := fun n ↦ -eta_q n z) ?_ ?_
  · exact fun i ↦ by simpa using! one_sub_eta_q_ne_zero i hz
  · simpa [eta_q, ← summable_norm_iff] using! summable_eta_q ⟨z, hz⟩

/-- Eta is non-vanishing on the upper half plane. -/
/-
**ModularForm.eta_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：eta_ne_zero {z : Complex} (hz : z in ℍₒ) : η z != 0
参数：hz : z in ℍₒ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `Function.Periodic.qParam_ne_zero`：qParam_ne_zero (z : Complex) : 𝕢 h z !
= 0
· 使用引理 `ModularForm.eta_tprod_ne_zero`：eta_tprod_ne_zero {z : Complex} (hz : z i
n ℍₒ) : ∏' n, (1 - eta_q n z) != 0

--- 原说明 ---
Eta is non-vanishing on the upper half plane.
-/
lemma eta_ne_zero {z : ℂ} (hz : z ∈ ℍₒ) : η z ≠ 0 :=
  mul_ne_zero (Periodic.qParam_ne_zero z) (eta_tprod_ne_zero hz)
/-
**ModularForm.logDeriv_one_sub_cexp** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：logDeriv_one_sub_cexp (r : Complex) : logDeriv (fun z => 1 - r * cexp z) =
 fun z => -r * cexp z / (1 - r * cexp z)
参数：r : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `deriv_const_sub'`：deriv_const_sub' (c : F) : deriv (c - f ·) = (-deriv f
 ·)
· 使用定理 `deriv_fun_mul`：deriv_fun_mul (hc : DifferentiableAt 𝕜 c x) (hd : Differe
ntiableAt 𝕜 d x) : deriv (fun y => c y * d y) x = deriv c x * d x + c x * deriv 
d x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv_const'`：deriv_const' : (deriv fun _ : 𝕜 => c) = fun _ => 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Complex.deriv_exp`：deriv_exp : deriv exp = exp
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma logDeriv_one_sub_cexp (r : ℂ) : logDeriv (fun z ↦ 1 - r * cexp z) =
    fun z ↦ -r * cexp z / (1 - r * cexp z) := by
  ext z
  simp [logDeriv]
/-
**ModularForm.logDeriv_one_sub_mul_cexp_comp** 是 Mathlib 中的一个引理，位于命名空间 `ModularF
orm`。
形式化陈述：logDeriv_one_sub_mul_cexp_comp (r : Complex) {g : Complex -> Complex} (hg 
: Differentiable Complex g) : logDeriv ((fun z => 1 - r * cexp z) ∘ g) = fun z =
> -r * (deriv g z) * cexp (g z) / (1 - r * cexp (g z))
参数：r : Complex；hg : Differentiable Complex g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `logDeriv_comp`：logDeriv_comp {f : 𝕜' -> 𝕜'} {g : 𝕜 -> 𝕜'} {x : 𝕜} (hf : 
DifferentiableAt 𝕜' f (g x)) (hg : DifferentiableAt 𝕜 g x) : logDeriv (f ∘ g) x 
= l…
· 使用定理 `DifferentiableAt.const_sub`：DifferentiableAt.const_sub (hf : Differentia
bleAt 𝕜 f x) (c : F) : DifferentiableAt 𝕜 (fun y => c - f y) x
· 使用定理 `DifferentiableAt.const_mul`：DifferentiableAt.const_mul (ha : Differentia
bleAt 𝕜 a x) (b : 𝔸) : DifferentiableAt 𝕜 (fun y => b * a y) x
· 使用定理 `DifferentiableAt.cexp`：DifferentiableAt.cexp (hc : DifferentiableAt 𝕜 f 
x) : DifferentiableAt 𝕜 (fun x => Complex.exp (f x)) x
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x
· 使用引理 `ModularForm.logDeriv_one_sub_cexp`：logDeriv_one_sub_cexp (r : Complex) :
 logDeriv (fun z => 1 - r * cexp z) = fun z => -r * cexp z / (1 - r * cexp z)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
（共 41 条，此处仅展示前 30 条）
-/
lemma logDeriv_one_sub_mul_cexp_comp (r : ℂ) {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    logDeriv ((fun z ↦ 1 - r * cexp z) ∘ g) =
    fun z ↦ -r * (deriv g z) * cexp (g z) / (1 - r * cexp (g z)) := by
  ext y
  rw [logDeriv_comp (by fun_prop) (hg y), logDeriv_one_sub_cexp]
  ring
/-
**ModularForm.one_sub_eta_logDeriv_eq** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem one_sub_eta_logDeriv_eq (z : ℂ) (n : ℕ) :
    logDeriv (1 - eta_q n ·) z = 2 * π * I * (n + 1) * -eta_q n z / (1 - eta_q n z) := by
  have h2 : (fun x ↦ 1 - cexp (2 * ↑π * I * (n + 1) * x)) =
      ((fun z ↦ 1 - 1 * cexp z) ∘ fun x ↦ 2 * ↑π * I * (n + 1) * x) := by aesop
  simp_rw [eta_q_eq_cexp, h2, logDeriv_one_sub_mul_cexp_comp 1
    (g := fun x ↦ (2 * π * I * (n + 1) * x)) (by fun_prop), deriv_const_mul_id]
  simp
/-
**ModularForm.tsum_logDeriv_eta_q** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：tsum_logDeriv_eta_q (z : Complex) : ∑' n, logDeriv (fun x => 1 - eta_q n x
) z = (2 * π * I) * ∑' n, (n + 1) * (-eta_q n z) / (1 - eta_q n z)
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `_private.Mathlib.NumberTheory.ModularForms.DedekindEta.0.ModularForm.one
_sub_eta_logDeriv_eq`：∀ (z : ℂ) (n : ℕ),   logDeriv (fun x => 1 - ModularForm.et
a_q n x) z =     2 * ↑Real.pi * Complex.I * (↑n + 1) * -ModularForm.eta_q n z / 
(1…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsum_mul_left`：tsum_mul_left [T2Space α] : ∑'[L] x, a * f x = a * ∑'[L] 
x, f x
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instT2Space`：T2Space ℂ
-/
lemma tsum_logDeriv_eta_q (z : ℂ) : ∑' n, logDeriv (fun x ↦ 1 - eta_q n x) z =
    (2 * π * I) * ∑' n, (n + 1) * (-eta_q n z) / (1 - eta_q n z) := by
  rw [tsum_congr (one_sub_eta_logDeriv_eq z), ← tsum_mul_left]
  grind
/-
**ModularForm.differentiableAt_eta_tprod** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`
。
形式化陈述：differentiableAt_eta_tprod {z : Complex} (hz : z in ℍₒ) : DifferentiableAt
 Complex (fun x => ∏' n, (1 - eta_q n x)) z
参数：hz : z in ℍₒ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `UpperHalfPlane.norm_qParam_lt_one`：UpperHalfPlane.norm_qParam_lt_one (n 
: Nat) [NeZero n] (τ : ℍ) : ‖𝕢 n τ‖ < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
· 使用定理 `DifferentiableOn.differentiableAt`：DifferentiableOn.differentiableAt (h 
: DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x) : DifferentiableAt 𝕜 f x
· 使用引理 `ModularForm.differentiableOn_tprod_one_sub_pow`：differentiableOn_tprod_o
ne_sub_pow : DifferentiableOn Complex (fun q => ∏' n, (1 - q ^ (n + 1))) (Metric
.ball (0 : Complex) 1)
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
· 使用定理 `Differentiable.differentiableAt`：Differentiable.differentiableAt (h : Di
fferentiable 𝕜 f) : DifferentiableAt 𝕜 f x
· 使用引理 `Function.Periodic.differentiable_qParam`：differentiable_qParam : Differe
ntiable Complex (𝕢 h)
-/
lemma differentiableAt_eta_tprod {z : ℂ} (hz : z ∈ ℍₒ) :
    DifferentiableAt ℂ (fun x ↦ ∏' n, (1 - eta_q n x)) z := by
  have hq : 𝕢 1 z ∈ Metric.ball 0 1 := by simpa using norm_qParam_lt_one 1 ⟨z, hz⟩
  exact (differentiableOn_tprod_one_sub_pow.differentiableAt
    (Metric.isOpen_ball.mem_nhds hq)).comp z (by fun_prop)
/-
**ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet** 是 Mathlib 中的一个定理，位
于命名空间 `ModularForm`。
形式化陈述：differentiableAt_eta_of_mem_upperHalfPlaneSet {z : Complex} (hz : z in ℍₒ)
 : DifferentiableAt Complex eta z
参数：hz : z in ℍₒ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.mul`：DifferentiableAt.mul (ha : DifferentiableAt 𝕜 a x)
 (hb : DifferentiableAt 𝕜 b x) : DifferentiableAt 𝕜 (a * b) x
· 使用定理 `Differentiable.differentiableAt`：Differentiable.differentiableAt (h : Di
fferentiable 𝕜 f) : DifferentiableAt 𝕜 f x
· 使用引理 `Function.Periodic.differentiable_qParam`：differentiable_qParam : Differe
ntiable Complex (𝕢 h)
· 使用引理 `ModularForm.differentiableAt_eta_tprod`：differentiableAt_eta_tprod {z : 
Complex} (hz : z in ℍₒ) : DifferentiableAt Complex (fun x => ∏' n, (1 - eta_q n 
x)) z
-/
theorem differentiableAt_eta_of_mem_upperHalfPlaneSet {z : ℂ} (hz : z ∈ ℍₒ) :
    DifferentiableAt ℂ eta z :=
  .mul (by fun_prop) (differentiableAt_eta_tprod hz)
/-
**ModularForm.logDeriv_qParam** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：logDeriv_qParam (h : Real) (z : Complex) : logDeriv (𝕢 h) z = 2 * π * I / 
h
参数：h : Real；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `logDeriv_comp`：logDeriv_comp {f : 𝕜' -> 𝕜'} {g : 𝕜 -> 𝕜'} {x : 𝕜} (hf : 
DifferentiableAt 𝕜' f (g x)) (hg : DifferentiableAt 𝕜 g x) : logDeriv (f ∘ g) x 
= l…
· 使用定理 `DifferentiableAt.cexp`：DifferentiableAt.cexp (hc : DifferentiableAt 𝕜 f 
x) : DifferentiableAt 𝕜 (fun x => Complex.exp (f x)) x
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x
· 使用定理 `DifferentiableAt.const_mul`：DifferentiableAt.const_mul (ha : Differentia
bleAt 𝕜 a x) (b : 𝔸) : DifferentiableAt 𝕜 (fun y => b * a y) x
· 使用定理 `deriv_const_mul_id`：deriv_const_mul_id (c : 𝕜) : deriv (fun y => c * y) 
x = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Complex.logDeriv_exp`：Complex.logDeriv_exp : logDeriv (Complex.exp) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma logDeriv_qParam (h : ℝ) (z : ℂ) : logDeriv (𝕢 h) z = 2 * π * I / h := by
  have : 𝕢 h = cexp ∘ ((2 * π * I / h) * ·) := by
    ext
    grind [Periodic.qParam]
  rw [this, logDeriv_comp (by fun_prop) (by fun_prop), deriv_const_mul_id]
  simp [logDeriv_exp]
/-
**ModularForm.summable_logDeriv_one_sub_eta_q** 是 Mathlib 中的一个引理，位于命名空间 `Modular
Form`。
形式化陈述：summable_logDeriv_one_sub_eta_q {z : Complex} (hz : z in ℍₒ) : Summable fu
n i => logDeriv (1 - eta_q i ·) z
参数：hz : z in ℍₒ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `summable_norm_pow_mul_geometric_div_one_sub`：summable_norm_pow_mul_geome
tric_div_one_sub (k : Nat) {r : 𝕜} (hr : ‖r‖ < 1) : Summable fun n : Nat => n ^ 
k * r ^ n / (1 - r ^ n)
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `UpperHalfPlane.norm_qParam_lt_one`：UpperHalfPlane.norm_qParam_lt_one (n 
: Nat) [NeZero n] (τ : ℍ) : ‖𝕢 n τ‖ < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Summable.mul_left`：Summable.mul_left (a) (hf : Summable f L) : Summable 
(fun i => a * f i) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `summable_nat_add_iff`：∀ {G : Type u_2} [inst : AddCommGroup G] [inst_1 :
 TopologicalSpace G] [IsTopologicalAddGroup G] {f : ℕ → G} (k : ℕ),   (Summable 
fun n => f…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
lemma summable_logDeriv_one_sub_eta_q {z : ℂ} (hz : z ∈ ℍₒ) :
    Summable fun i ↦ logDeriv (1 - eta_q i ·) z := by
  have := summable_norm_pow_mul_geometric_div_one_sub 1 (norm_qParam_lt_one 1 ⟨z, hz⟩)
  convert! ((summable_nat_add_iff 1).mpr this).mul_left (-2 * π * I) using 1 with n
  grind [one_sub_eta_logDeriv_eq]

open EisensteinSeries in
/-
**ModularForm.logDeriv_eta_eq_E2** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：logDeriv_eta_eq_E2 (z : ℍ) : logDeriv eta z = (π * I / 12) * E2 z
参数：z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `logDeriv_mul`：logDeriv_mul {f g : 𝕜 -> 𝕜'} (x : 𝕜) (hf : f x != 0) (hg :
 g x != 0) (hdf : DifferentiableAt 𝕜 f x) (hdg : DifferentiableAt 𝕜 g x) : logDe
ri…
· 使用引理 `Function.Periodic.qParam_ne_zero`：qParam_ne_zero (z : Complex) : 𝕢 h z !
= 0
· 使用引理 `ModularForm.eta_tprod_ne_zero`：eta_tprod_ne_zero {z : Complex} (hz : z i
n ℍₒ) : ∏' n, (1 - eta_q n z) != 0
· 使用定理 `UpperHalfPlane.coe_im_pos`：∀ (self : UpperHalfPlane), 0 < (↑self).im
· 使用定理 `Differentiable.differentiableAt`：Differentiable.differentiableAt (h : Di
fferentiable 𝕜 f) : DifferentiableAt 𝕜 f x
· 使用引理 `Function.Periodic.differentiable_qParam`：differentiable_qParam : Differe
ntiable Complex (𝕢 h)
· 使用引理 `ModularForm.differentiableAt_eta_tprod`：differentiableAt_eta_tprod {z : 
Complex} (hz : z in ℍₒ) : DifferentiableAt Complex (fun x => ∏' n, (1 - eta_q n 
x)) z
· 使用定理 `logDeriv_tprod_eq_tsum`：logDeriv_tprod_eq_tsum {ι : Type*} {s : Set Comp
lex} (hs : IsOpen s) {x : Complex} (hx : x in s) {f : ι -> Complex -> Complex} (
hf : forall …
· 使用引理 `UpperHalfPlane.isOpen_upperHalfPlaneSet`：isOpen_upperHalfPlaneSet : IsOp
en ℍₒ
· 使用引理 `ModularForm.one_sub_eta_q_ne_zero`：one_sub_eta_q_ne_zero (n : Nat) {z : 
Complex} (hz : z in ℍₒ) : 1 - eta_q n z != 0
· 使用定理 `DifferentiableOn.const_sub`：DifferentiableOn.const_sub (hf : Differentia
bleOn 𝕜 f s) (c : F) : DifferentiableOn 𝕜 (fun y => c - f y) s
· 使用定理 `DifferentiableOn.fun_pow`：∀ {𝕜 : Type u_1} {𝔸 : Type u_2} {E : Type u_3}
 [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedRing 𝔸]   [inst_2 : NormedAd
dCommGroup E] …
· 使用定理 `Differentiable.differentiableOn`：Differentiable.differentiableOn (h : Di
fferentiable 𝕜 f) : DifferentiableOn 𝕜 f s
· 使用引理 `ModularForm.summable_logDeriv_one_sub_eta_q`：summable_logDeriv_one_sub_e
ta_q {z : Complex} (hz : z in ℍₒ) : Summable fun i => logDeriv (1 - eta_q i ·) z
· 使用引理 `ModularForm.multipliableLocallyUniformlyOn_eta`：multipliableLocallyUnifo
rmlyOn_eta : MultipliableLocallyUniformlyOn (fun n a => 1 - eta_q n a) ℍₒ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `ModularForm.logDeriv_qParam`：logDeriv_qParam (h : Real) (z : Complex) : 
logDeriv (𝕢 h) z = 2 * π * I / h
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ModularForm.tsum_logDeriv_eta_q`：tsum_logDeriv_eta_q (z : Complex) : ∑' 
n, logDeriv (fun x => 1 - eta_q n x) z = (2 * π * I) * ∑' n, (n + 1) * (-eta_q n
 z) / (1 - eta_q n z)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用引理 `EisensteinSeries.G2_eq_tsum_cexp`：G2_eq_tsum_cexp : G2 z = 2 * riemannZe
ta 2 - 8 * π ^ 2 * ∑' n : Nat+, σ 1 n * 𝕢 z ^ (n : Nat)
· 使用定理 `riemannZeta_two`：riemannZeta_two : riemannZeta 2 = (π : Complex) ^ 2 / 6
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `tsum_pow_div_one_sub_eq_tsum_sigma`：tsum_pow_div_one_sub_eq_tsum_sigma {
r : 𝕜} (hr : ‖r‖ < 1) (k : Nat) : ∑' n : Nat+, n ^ k * r ^ (n : Nat) / (1 - r ^ 
(n : Nat)) = ∑' n : Nat+…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
（共 49 条，此处仅展示前 30 条）
-/
lemma logDeriv_eta_eq_E2 (z : ℍ) : logDeriv eta z = (π * I / 12) * E2 z := by
  unfold eta
  rw [logDeriv_mul _ (Periodic.qParam_ne_zero _) (eta_tprod_ne_zero z.2) (by fun_prop)
    (differentiableAt_eta_tprod z.2)]
  have HG := logDeriv_tprod_eq_tsum isOpen_upperHalfPlaneSet z.2
    (one_sub_eta_q_ne_zero · z.2) (by fun_prop) (summable_logDeriv_one_sub_eta_q z.2)
    multipliableLocallyUniformlyOn_eta (eta_tprod_ne_zero z.2)
  simp only [logDeriv_qParam 24 z, HG, tsum_logDeriv_eta_q z, E2, one_div,
    mul_inv_rev, Pi.smul_apply, smul_eq_mul]
  rw [G2_eq_tsum_cexp, riemannZeta_two, ← tsum_pow_div_one_sub_eq_tsum_sigma
    (norm_exp_two_pi_I_lt_one z), mul_sub, sub_eq_add_neg, mul_add]
  simp [eta_q_eq_pow, ← tsum_mul_left, tsum_pnat_eq_tsum_succ (f := fun n ↦
        n * cexp (2 * π * I * z) ^ n / (1 - cexp (2 * π * I * z) ^ n)), ← tsum_neg]
  grind

end ModularForm

