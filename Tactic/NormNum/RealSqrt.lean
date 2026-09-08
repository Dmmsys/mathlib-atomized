/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.Real.Sqrt

/-! # `norm_num` extension for `Real.sqrt`

This module defines a `norm_num` extension for `Real.sqrt` and `NNReal.sqrt`.
-/

public meta section

namespace Mathlib.Meta.NormNum

open Qq Lean Lean.Meta Elab.Tactic Mathlib.Meta.NormNum NNReal

/-
**Mathlib.Meta.NormNum.isNat_realSqrt** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：isNat_realSqrt {x : Real} {nx ny : Nat} (h : IsNat x nx) (hy : ny * ny = n
x) : IsNat √x ny
参数：h : IsNat x nx；hy : ny * ny = nx。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Real.sqrt_mul_self`：sqrt_mul_self (h : 0 <= x) : √(x * x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isNat_realSqrt {x : ℝ} {nx ny : ℕ} (h : IsNat x nx) (hy : ny * ny = nx) :
    IsNat √x ny := ⟨by simp [h.out, ← hy]⟩
/-
**Mathlib.Meta.NormNum.isNat_nnrealSqrt** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Meta.
NormNum`。
形式化陈述：isNat_nnrealSqrt {x : Real>=0} {nx ny : Nat} (h : IsNat x nx) (hy : ny * n
y = nx) : IsNat (NNReal.sqrt x) ny
参数：h : IsNat x nx；hy : ny * ny = nx。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `NNReal.sqrt_mul_self`：∀ (x : NNReal), NNReal.sqrt (x * x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isNat_nnrealSqrt {x : ℝ≥0} {nx ny : ℕ} (h : IsNat x nx) (hy : ny * ny = nx) :
    IsNat (NNReal.sqrt x) ny := ⟨by simp [h.out, ← hy]⟩
/-
**Mathlib.Meta.NormNum.isNNRat_nnrealSqrt_of_isNNRat** 是 Mathlib 中的一个引理，位于命名空间 `
Mathlib.Meta.NormNum`。
形式化陈述：isNNRat_nnrealSqrt_of_isNNRat {x : Real>=0} {n sn : Nat} {d sd : Nat} (hn 
: sn * sn = n) (hd : sd * sd = d) (h : IsNNRat x n d) : IsNNRat (NNReal.sqrt x) 
sn sd
参数：hn : sn * sn = n；hd : sd * sd = d；h : IsNNRat x n d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_self_ne_zero`：mul_self_ne_zero : a * a != 0 ↔ a != 0
· 使用定理 `NNReal.instNoZeroDivisors`：NoZeroDivisors NNReal
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Invertible.ne_zero`：Invertible.ne_zero [MulZeroOneClass α] (a : α) [Nont
rivial α] [Invertible a] : a != 0
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `NNReal.sqrt_mul`：sqrt_mul (x y : Real>=0) : sqrt (x * y) = sqrt x * sqrt
 y
· 使用定理 `NNReal.sqrt_mul_self`：∀ (x : NNReal), NNReal.sqrt (x * x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isNNRat_nnrealSqrt_of_isNNRat {x : ℝ≥0} {n sn : ℕ} {d sd : ℕ} (hn : sn * sn = n)
    (hd : sd * sd = d) (h : IsNNRat x n d) :
    IsNNRat (NNReal.sqrt x) sn sd := by
  obtain ⟨_, rfl⟩ := h
  refine ⟨?_, ?out⟩
  · apply invertibleOfNonzero
    rw [← mul_self_ne_zero, ← Nat.cast_mul, hd]
    exact Invertible.ne_zero _
  · simp [← hn, ← hd, NNReal.sqrt_mul]
/-
**Mathlib.Meta.NormNum.isNat_realSqrt_neg** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Met
a.NormNum`。
形式化陈述：isNat_realSqrt_neg {x : Real} {nx : Nat} (h : IsInt x (Int.negOfNat nx)) :
 IsNat √x (nat_lit 0)
参数：h : IsInt x (Int.negOfNat nx)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.out`：∀ {α : Type u} [inst : Ring α] {a : α} {
n : ℤ}, Mathlib.Meta.NormNum.IsInt a n → a = ↑n
· 使用定理 `Int.cast_negOfNat`：cast_negOfNat (n : Nat) : ((negOfNat n : Int) : R) = 
-n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma isNat_realSqrt_neg {x : ℝ} {nx : ℕ} (h : IsInt x (Int.negOfNat nx)) :
    IsNat √x (nat_lit 0) := ⟨by simp [Real.sqrt_eq_zero', h.out]⟩
/-
**Mathlib.Meta.NormNum.isNat_realSqrt_of_isRat_negOfNat** 是 Mathlib 中的一个引理，位于命名空
间 `Mathlib.Meta.NormNum`。
形式化陈述：isNat_realSqrt_of_isRat_negOfNat {x : Real} {num : Nat} {denom : Nat} (h :
 IsRat x (.negOfNat num) denom) : IsNat √x (nat_lit 0)
参数：h : IsRat x (.negOfNat num) denom。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `invOf_nonneg`：invOf_nonneg [Invertible a] : 0 <= ⅟a ↔ 0 <= a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_negOfNat`：cast_negOfNat (n : Nat) : ((negOfNat n : Int) : R) = 
-n
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isNat_realSqrt_of_isRat_negOfNat {x : ℝ} {num : ℕ} {denom : ℕ}
    (h : IsRat x (.negOfNat num) denom) : IsNat √x (nat_lit 0) := by
  refine ⟨?_⟩
  obtain ⟨inv, rfl⟩ := h
  have h₁ : 0 ≤ (num : ℚ) * ⅟(denom : ℝ) :=
    mul_nonneg (Nat.cast_nonneg' _) (invOf_nonneg.2 <| Nat.cast_nonneg' _)
  simpa [Nat.cast_zero, Real.sqrt_eq_zero', Int.cast_negOfNat, neg_mul, neg_nonpos] using h₁
/-
**Mathlib.Meta.NormNum.isNNRat_realSqrt_of_isNNRat** 是 Mathlib 中的一个引理，位于命名空间 `Ma
thlib.Meta.NormNum`。
形式化陈述：isNNRat_realSqrt_of_isNNRat {x : Real} {n sn : Nat} {d sd : Nat} (hn : sn 
* sn = n) (hd : sd * sd = d) (h : IsNNRat x n d) : IsNNRat √x sn sd
参数：hn : sn * sn = n；hd : sd * sd = d；h : IsNNRat x n d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_self_ne_zero`：mul_self_ne_zero : a * a != 0 ↔ a != 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Invertible.ne_zero`：Invertible.ne_zero [MulZeroOneClass α] (a : α) [Nont
rivial α] [Invertible a] : a != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `Real.sqrt_mul`：sqrt_mul {x : Real} (hx : 0 <= x) (y : Real) : √(x * y) =
 √x * √y
· 使用引理 `mul_self_nonneg`：mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLe
ftMono R] (a : R) : 0 <= a * a
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.sqrt_mul_self`：sqrt_mul_self (h : 0 <= x) : √(x * x) = x
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isNNRat_realSqrt_of_isNNRat {x : ℝ} {n sn : ℕ} {d sd : ℕ} (hn : sn * sn = n)
    (hd : sd * sd = d) (h : IsNNRat x n d) :
    IsNNRat √x sn sd := by
  obtain ⟨_, rfl⟩ := h
  refine ⟨?_, ?out⟩
  · apply invertibleOfNonzero
    rw [← mul_self_ne_zero, ← Nat.cast_mul, hd]
    exact Invertible.ne_zero _
  · simp [← hn, ← hd, Real.sqrt_mul (mul_self_nonneg ↑sn)]

/-- `norm_num` extension that evaluates the function `Real.sqrt`. -/
@[norm_num √_]
/-
**Mathlib.Meta.NormNum.evalRealSqrt** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Norm
Num`。
形式化陈述：evalRealSqrt : NormNumExt where eval {u α} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`norm_num` extension that evaluates the function `Real.sqrt`.
-/
def evalRealSqrt : NormNumExt where eval {u α} e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(√$x) =>
    match ← derive x with
    | .isBool _ _ => failure
    | .isNat sℝ ex pf =>
        let x := ex.natLit!
        let y := Nat.sqrt x
        unless y * y = x do failure
        have ey : Q(ℕ) := mkRawNatLit y
        have pf₁ : Q($ey * $ey = $ex) := (q(Eq.refl $ex) : Expr)
        assumeInstancesCommute
        return .isNat q($sℝ) q($ey) q(isNat_realSqrt $pf $pf₁)
    | .isNegNat _ ex pf =>
        -- Recall that `Real.sqrt` returns 0 for negative inputs
        assumeInstancesCommute
        return .isNat q(inferInstance) q(nat_lit 0) q(isNat_realSqrt_neg $pf)
    | .isNegNNRat sℝ eq n ed pf =>
        assumeInstancesCommute
        return .isNat q(inferInstance) q(nat_lit 0) q(isNat_realSqrt_of_isRat_negOfNat $pf)
    | .isNNRat sℝ eq n' ed pf =>
          let n : ℕ := n'.natLit!
          let d : ℕ := ed.natLit!
          let sn := Nat.sqrt n
          let sd := Nat.sqrt d
          unless sn * sn = n ∧ sd * sd = d do failure
          have esn : Q(ℕ) := mkRawNatLit sn
          have esd : Q(ℕ) := mkRawNatLit sd
          have hn : Q($esn * $esn = $n') := (q(Eq.refl $n') : Expr)
          have hd : Q($esd * $esd = $ed) := (q(Eq.refl $ed) : Expr)
          assumeInstancesCommute
          -- will never be an integer
          return .isNNRat q($sℝ) (sn / sd) _ q($esd) q(isNNRat_realSqrt_of_isNNRat $hn $hd $pf)
  | _ => failure

/-- `norm_num` extension that evaluates the function `NNReal.sqrt`. -/
@[norm_num NNReal.sqrt _]
/-
**Mathlib.Meta.NormNum.evalNNRealSqrt** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：evalNNRealSqrt : NormNumExt where eval {u α} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`norm_num` extension that evaluates the function `NNReal.sqrt`.
-/
def evalNNRealSqrt : NormNumExt where eval {u α} e := do
  match u, α, e with
  | 0, ~q(NNReal), ~q(NNReal.sqrt $x) =>
    match ← derive x with
    | .isBool _ _ => failure
    | .isNat sℝ ex pf =>
        let x := ex.natLit!
        let y := Nat.sqrt x
        unless y * y = x do failure
        have ey : Q(ℕ) := mkRawNatLit y
        have pf₁ : Q($ey * $ey = $ex) := (q(Eq.refl $ex) : Expr)
        assumeInstancesCommute
        return .isNat sℝ ey q(isNat_nnrealSqrt $pf $pf₁)
    | .isNegNat _ ex pf => failure
    | .isNNRat sℝ eq n' ed pf =>
        let n : ℕ := n'.natLit!
        let d : ℕ := ed.natLit!
        let sn := Nat.sqrt n
        let sd := Nat.sqrt d
        unless sn * sn = n ∧ sd * sd = d do failure
        have esn : Q(ℕ) := mkRawNatLit sn
        have esd : Q(ℕ) := mkRawNatLit sd
        have hn : Q($esn * $esn = $n') := (q(Eq.refl $n') : Expr)
        have hd : Q($esd * $esd = $ed) := (q(Eq.refl $ed) : Expr)
        assumeInstancesCommute
        -- will never be an integer
        return .isNNRat q($sℝ) (sn / sd) _ q($esd) q(isNNRat_nnrealSqrt_of_isNNRat $hn $hd $pf)
    | .isNegNNRat sℝ eq en ed pf => failure
  | _ => failure

end Mathlib.Meta.NormNum

