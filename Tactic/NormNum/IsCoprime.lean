/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.NormNum.GCD

/-! # `norm_num` extension for `IsCoprime`

This module defines a `norm_num` extension for `IsCoprime` over `ℤ`.

(While `IsCoprime` is defined over `ℕ`, since it uses Bezout's identity with `ℕ` coefficients
it does not correspond to the usual notion of coprime.)
-/

public meta section

namespace Mathlib.Meta

namespace NormNum

open Qq Lean Elab.Tactic Mathlib.Meta.NormNum

/-
**Mathlib.Meta.NormNum.int_not_isCoprime_helper** 是 Mathlib 中的一个定理，位于命名空间 `Mathl
ib.Meta.NormNum`。
形式化陈述：int_not_isCoprime_helper (x y : Int) (d : Nat) (hd : Int.gcd x y = d) (h :
 Nat.beq d 1 = false) : ¬ IsCoprime x y
参数：x y : Int；d : Nat；hd : Int.gcd x y = d；h : Nat.beq d 1 = false。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.isCoprime_iff_gcd_eq_one`：Int.isCoprime_iff_gcd_eq_one {m n : Int} :
 IsCoprime m n ↔ Int.gcd m n = 1
· 使用定理 `Nat.ne_of_beq_eq_false`：∀ {n m : ℕ}, n.beq m = false → ¬n = m
-/
theorem int_not_isCoprime_helper (x y : ℤ) (d : ℕ) (hd : Int.gcd x y = d)
    (h : Nat.beq d 1 = false) : ¬ IsCoprime x y := by
  rw [Int.isCoprime_iff_gcd_eq_one, hd]
  exact Nat.ne_of_beq_eq_false h
/-
**Mathlib.Meta.NormNum.isInt_isCoprime** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.N
ormNum`。
形式化陈述：∀ {x y nx ny : ℤ}, Mathlib.Meta.NormNum.IsInt x nx → Mathlib.Meta.NormNum.
IsInt y ny → IsCoprime nx ny → IsCoprime x y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isInt_isCoprime : {x y nx ny : ℤ} →
    IsInt x nx → IsInt y ny → IsCoprime nx ny → IsCoprime x y
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => h
/-
**Mathlib.Meta.NormNum.isInt_not_isCoprime** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Me
ta.NormNum`。
形式化陈述：∀ {x y nx ny : ℤ}, Mathlib.Meta.NormNum.IsInt x nx → Mathlib.Meta.NormNum.
IsInt y ny → ¬IsCoprime nx ny → ¬IsCoprime x y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isInt_not_isCoprime : {x y nx ny : ℤ} →
    IsInt x nx → IsInt y ny → ¬ IsCoprime nx ny → ¬ IsCoprime x y
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => h

/-- Evaluates `IsCoprime` for the given integer number literals.
Panics if `ex` or `ey` aren't integer number literals. -/
/-
**Mathlib.Meta.NormNum.proveIntIsCoprime** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta
.NormNum`。
形式化陈述：proveIntIsCoprime (ex ey : Q(Int)) : Q(IsCoprime $ex $ey) oplus Q(¬ IsCopr
ime $ex $ey)
参数：ex ey : Q(Int)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluates `IsCoprime` for the given integer number literals.
Panics if `ex` or `ey` aren't integer number literals.
-/
def proveIntIsCoprime (ex ey : Q(ℤ)) : Q(IsCoprime $ex $ey) ⊕ Q(¬ IsCoprime $ex $ey) :=
  let ⟨ed, pf⟩ := proveIntGCD ex ey
  if ed.natLit! = 1 then
    have pf' : Q(Int.gcd $ex $ey = 1) := pf
    Sum.inl q(Int.isCoprime_iff_gcd_eq_one.mpr $pf')
  else
    have h : Q(Nat.beq $ed 1 = false) := (q(Eq.refl false) : Expr)
    Sum.inr q(int_not_isCoprime_helper $ex $ey $ed $pf $h)

/-- Evaluates the `IsCoprime` predicate over `ℤ`. -/
@[norm_num IsCoprime (_ : ℤ) (_ : ℤ)]
/-
**Mathlib.Meta.NormNum.evalIntIsCoprime** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.
NormNum`。
形式化陈述：evalIntIsCoprime : NormNumExt where eval {_ _} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluates the `IsCoprime` predicate over `ℤ`.
-/
def evalIntIsCoprime : NormNumExt where eval {_ _} e := do
  let .app (.app _ (x : Q(ℤ))) (y : Q(ℤ)) ← Meta.whnfR e | failure
  let ⟨ex, p⟩ ← deriveInt x _
  let ⟨ey, q⟩ ← deriveInt y _
  match proveIntIsCoprime ex ey with
  | .inl pf =>
    have pf' : Q(IsCoprime $x $y) := q(isInt_isCoprime $p $q $pf)
    return .isTrue pf'
  | .inr pf =>
    have pf' : Q(¬ IsCoprime $x $y) := q(isInt_not_isCoprime $p $q $pf)
    return .isFalse pf'

end NormNum

end Mathlib.Meta

