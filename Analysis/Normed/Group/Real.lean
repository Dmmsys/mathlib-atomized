/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Group.Basic

/-!
# Norms on `ℝ` and `ℝ≥0`

We equip `ℝ`, `ℝ≥0`, and `ℝ≥0∞` with their natural norms / enorms.

## Tags

normed group
-/

public section


variable {𝓕 α ι κ E F G : Type*}

open Filter Function Metric Bornology
open ENNReal Filter NNReal Uniformity Pointwise Topology

namespace NNReal

/-
**NNReal.** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NNNorm ℝ≥0 where
  nnnorm x := x
/-
**NNReal.nnnorm_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ (x : NNReal), ‖x‖₊ = x
参数：x : NNReal。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma nnnorm_eq_self (x : ℝ≥0) : ‖x‖₊ = x := rfl

end NNReal

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ENorm ℝ≥0∞ where
  enorm x := x
/-
**enorm_eq_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (x : ENNReal), ‖x‖ₑ = x
参数：x : ENNReal。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma enorm_eq_self (x : ℝ≥0∞) : ‖x‖ₑ = x := rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : ENormedAddCommMonoid ℝ≥0∞ where
  continuous_enorm := continuous_id
  enorm_zero := by simp
  enorm_eq_zero := by simp
  enorm_add_le := by simp

namespace Real

variable {r : ℝ}

/-
**Real.norm** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：norm : Norm Real where norm r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance norm : Norm ℝ where
  norm r := |r|

@[simp]
/-
**Real.norm_eq_abs** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：norm_eq_abs (r : Real) : ‖r‖ = |r|
参数：r : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_eq_abs (r : ℝ) : ‖r‖ = |r| :=
  rfl
/-
**Real.normedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：normedAddCommGroup : NormedAddCommGroup Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance normedAddCommGroup : NormedAddCommGroup ℝ :=
  ⟨fun _r _y => by rw [Real.dist_eq, ← abs_neg, neg_sub, add_comm, sub_eq_add_neg, norm_eq_abs]⟩
/-
**Real.norm_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
参数：hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem norm_of_nonneg (hr : 0 ≤ r) : ‖r‖ = r :=
  abs_of_nonneg hr
/-
**Real.norm_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：norm_of_nonpos (hr : r <= 0) : ‖r‖ = -r
参数：hr : r <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], a ≤ 0 → |a| = -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem norm_of_nonpos (hr : r ≤ 0) : ‖r‖ = -r :=
  abs_of_nonpos hr
/-
**Real.le_norm_self** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：le_norm_self (r : Real) : r <= ‖r‖
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
-/
theorem le_norm_self (r : ℝ) : r ≤ ‖r‖ :=
  le_abs_self r
/-
**Real.norm_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：norm_natCast (n : Nat) : ‖(n : Real)‖ = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
-/
lemma norm_natCast (n : ℕ) : ‖(n : ℝ)‖ = n := abs_of_nonneg n.cast_nonneg
/-
**Real.nnnorm_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ (n : ℕ), ‖↑n‖₊ = ↑n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用引理 `Real.norm_natCast`：norm_natCast (n : Nat) : ‖(n : Real)‖ = n
-/
@[simp 1100] lemma nnnorm_natCast (n : ℕ) : ‖(n : ℝ)‖₊ = n := NNReal.eq <| norm_natCast _
/-
**Real.enorm_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ (n : ℕ), ‖↑n‖ₑ = ↑n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.nnnorm_natCast`：∀ (n : ℕ), ‖↑n‖₊ = ↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp 1100] lemma enorm_natCast (n : ℕ) : ‖(n : ℝ)‖ₑ = n := by simp [enorm]
/-
**Real.norm_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ (n : ℕ) [inst : n.AtLeastTwo], ‖OfNat.ofNat n‖ = OfNat.ofNat n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.norm_natCast`：norm_natCast (n : Nat) : ‖(n : Real)‖ = n
-/
@[simp 1100] lemma norm_ofNat (n : ℕ) [n.AtLeastTwo] :
    ‖(ofNat(n) : ℝ)‖ = ofNat(n) := norm_natCast n
/-
**Real.nnnorm_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ (n : ℕ) [inst : n.AtLeastTwo], ‖OfNat.ofNat n‖₊ = OfNat.ofNat n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.nnnorm_natCast`：∀ (n : ℕ), ‖↑n‖₊ = ↑n
-/
@[simp 1100] lemma nnnorm_ofNat (n : ℕ) [n.AtLeastTwo] :
    ‖(ofNat(n) : ℝ)‖₊ = ofNat(n) := nnnorm_natCast n
/-
**Real.norm_two** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：norm_two : ‖(2 : Real)‖ = 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
lemma norm_two : ‖(2 : ℝ)‖ = 2 := abs_of_pos zero_lt_two
/-
**Real.nnnorm_two** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：nnnorm_two : ‖(2 : Real)‖₊ = 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.nnnorm_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], ‖OfNat.ofNat n‖₊ = O
fNat.ofNat n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nnnorm_two : ‖(2 : ℝ)‖₊ = 2 := NNReal.eq <| by simp

@[simp 1100, norm_cast]
/-
**Real.norm_nnratCast** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：norm_nnratCast (q : Rat>=0) : ‖(q : Real)‖ = q
参数：q : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用引理 `NNRat.cast_nonneg`：NNRat.cast_nonneg (q : Rat>=0) : 0 <= (q : α)
-/
lemma norm_nnratCast (q : ℚ≥0) : ‖(q : ℝ)‖ = q := norm_of_nonneg q.cast_nonneg

@[simp 1100, norm_cast]
/-
**Real.nnnorm_nnratCast** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：nnnorm_nnratCast (q : Rat>=0) : ‖(q : Real)‖₊ = q
参数：q : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `Real.norm_nnratCast`：norm_nnratCast (q : Rat>=0) : ‖(q : Real)‖ = q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.mk.congr_simp`：∀ (x x_1 : ℝ) (e_x : x = x_1) (hx : 0 ≤ x), NNReal
.mk x hx = NNReal.mk x_1 ⋯
-/
lemma nnnorm_nnratCast (q : ℚ≥0) : ‖(q : ℝ)‖₊ = q := by
  simp [nnnorm]
  rfl
/-
**Real.nnnorm_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：nnnorm_of_nonneg (hr : 0 <= r) : ‖r‖₊ = .mk r hr
参数：hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
-/
theorem nnnorm_of_nonneg (hr : 0 ≤ r) : ‖r‖₊ = .mk r hr :=
  NNReal.eq <| norm_of_nonneg hr
/-
**Real.enorm_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：enorm_of_nonneg (hr : 0 <= r) : ‖r‖ₑ = .ofReal r
参数：hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.nnnorm_of_nonneg`：nnnorm_of_nonneg (hr : 0 <= r) : ‖r‖₊ = .mk r hr
· 使用定理 `NNReal.mk.congr_simp`：∀ (x x_1 : ℝ) (e_x : x = x_1) (hx : 0 ≤ x), NNReal
.mk x hx = NNReal.mk x_1 ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma enorm_of_nonneg (hr : 0 ≤ r) : ‖r‖ₑ = .ofReal r := by
  simp [enorm, nnnorm_of_nonneg hr, ENNReal.ofReal, toNNReal, hr]
/-
**Real.enorm_ofReal_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：enorm_ofReal_of_nonneg {a : Real} (ha : 0 <= a) : ‖ENNReal.ofReal a‖ₑ = ‖a
‖ₑ
参数：ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Real.enorm_of_nonneg`：enorm_of_nonneg (hr : 0 <= r) : ‖r‖ₑ = .ofReal r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma enorm_ofReal_of_nonneg {a : ℝ} (ha : 0 ≤ a) : ‖ENNReal.ofReal a‖ₑ = ‖a‖ₑ := by
  simp [Real.enorm_of_nonneg, ha]
/-
**Real.nnnorm_abs** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ (r : ℝ), ‖|r|‖₊ = ‖r‖₊
参数：r : ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `abs_abs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [AddL
eftMono α] [AddRightMono α] (a : α), |(|a|)| = |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.mk.congr_simp`：∀ (x x_1 : ℝ) (e_x : x = x_1) (hx : 0 ≤ x), NNReal
.mk x hx = NNReal.mk x_1 ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma nnnorm_abs (r : ℝ) : ‖|r|‖₊ = ‖r‖₊ := by simp [nnnorm]
/-
**Real.enorm_abs** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ (r : ℝ), ‖|r|‖ₑ = ‖r‖ₑ
参数：r : ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.nnnorm_abs`：∀ (r : ℝ), ‖|r|‖₊ = ‖r‖₊
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma enorm_abs (r : ℝ) : ‖|r|‖ₑ = ‖r‖ₑ := by simp [enorm]
/-
**Real.enorm_eq_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：enorm_eq_ofReal (hr : 0 <= r) : ‖r‖ₑ = .ofReal r
参数：hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ofReal_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ENN
Real.ofReal ‖x‖ = ‖x‖ₑ
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
-/
theorem enorm_eq_ofReal (hr : 0 ≤ r) : ‖r‖ₑ = .ofReal r := by
  rw [← ofReal_norm, norm_of_nonneg hr]
/-
**Real.enorm_toReal** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ {a : ENNReal}, a ≠ ⊤ → ‖a.toReal‖ₑ = a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.enorm_eq_ofReal`：enorm_eq_ofReal (hr : 0 <= r) : ‖r‖ₑ = .ofReal r
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma enorm_toReal {a : ℝ≥0∞} (ha : a ≠ ∞) : ‖a.toReal‖ₑ = a := by
  simp [enorm_eq_ofReal, ha]
/-
**Real.enorm_eq_ofReal_abs** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：enorm_eq_ofReal_abs (r : Real) : ‖r‖ₑ = ENNReal.ofReal |r|
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.enorm_eq_ofReal`：enorm_eq_ofReal (hr : 0 <= r) : ‖r‖ₑ = .ofReal r
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Real.enorm_abs`：∀ (r : ℝ), ‖|r|‖ₑ = ‖r‖ₑ
-/
theorem enorm_eq_ofReal_abs (r : ℝ) : ‖r‖ₑ = ENNReal.ofReal |r| := by
  rw [← enorm_eq_ofReal (abs_nonneg _), enorm_abs]
/-
**Real.toNNReal_eq_nnnorm_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：toNNReal_eq_nnnorm_of_nonneg (hr : 0 <= r) : r.toNNReal = ‖r‖₊
参数：hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.toNNReal_of_nonneg`：∀ {r : ℝ} (hr : 0 ≤ r), r.toNNReal = NNReal.mk 
r hr
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem toNNReal_eq_nnnorm_of_nonneg (hr : 0 ≤ r) : r.toNNReal = ‖r‖₊ := by
  rw [Real.toNNReal_of_nonneg hr]
  congr
  rw [Real.norm_eq_abs r, abs_of_nonneg hr]
/-
**Real.ofReal_le_enorm** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：ofReal_le_enorm (r : Real) : ENNReal.ofReal r <= ‖r‖ₑ
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.enorm_eq_ofReal_abs`：enorm_eq_ofReal_abs (r : Real) : ‖r‖ₑ = ENNRea
l.ofReal |r|
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
-/
theorem ofReal_le_enorm (r : ℝ) : ENNReal.ofReal r ≤ ‖r‖ₑ := by
  rw [enorm_eq_ofReal_abs]; gcongr; exact le_abs_self _

end Real

section SeminormedCommGroup

variable [SeminormedCommGroup E] [SeminormedCommGroup F] {a b : E} {r : ℝ}
variable {ε : Type*} [TopologicalSpace ε] [ESeminormedCommMonoid ε]

@[to_additive (attr := simp high) norm_norm] -- Higher priority as a shortcut lemma.
/-
**norm_norm'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_norm' (x : E) : ‖‖x‖‖ = ‖x‖
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `norm_nonneg'`：norm_nonneg' (a : E) : 0 <= ‖a‖
-/
lemma norm_norm' (x : E) : ‖‖x‖‖ = ‖x‖ := Real.norm_of_nonneg (norm_nonneg' _)

@[to_additive (attr := simp) nnnorm_norm]
/-
**nnnorm_norm'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nnnorm_norm' (x : E) : ‖‖x‖‖₊ = ‖x‖₊
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `norm_nonneg'`：norm_nonneg' (a : E) : 0 <= ‖a‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `norm_norm'`：norm_norm' (x : E) : ‖‖x‖‖ = ‖x‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.mk.congr_simp`：∀ (x x_1 : ℝ) (e_x : x = x_1) (hx : 0 ≤ x), NNReal
.mk x hx = NNReal.mk x_1 ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nnnorm_norm' (x : E) : ‖‖x‖‖₊ = ‖x‖₊ := by simp [nnnorm]

@[to_additive (attr := simp) enorm_norm]
/-
**enorm_norm'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：enorm_norm' (x : E) : ‖‖x‖‖ₑ = ‖x‖ₑ
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `nnnorm_norm'`：nnnorm_norm' (x : E) : ‖‖x‖‖₊ = ‖x‖₊
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma enorm_norm' (x : E) : ‖‖x‖‖ₑ = ‖x‖ₑ := by simp [enorm]
/-
**enorm_enorm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：enorm_enorm {ε : Type*} [ENorm ε] (x : ε) : ‖‖x‖ₑ‖ₑ = ‖x‖ₑ
参数：x : ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma enorm_enorm {ε : Type*} [ENorm ε] (x : ε) : ‖‖x‖ₑ‖ₑ = ‖x‖ₑ := by simp [enorm]

end SeminormedCommGroup

/-
**tendsto_norm_atTop_atTop** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_norm_atTop_atTop : Tendsto (norm : Real -> Real) atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_abs_atTop_atTop`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : LinearOrder G], Filter.Tendsto abs Filter.atTop Filter.atTop
-/
lemma tendsto_norm_atTop_atTop : Tendsto (norm : ℝ → ℝ) atTop atTop := tendsto_abs_atTop_atTop
