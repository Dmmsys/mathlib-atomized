/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kyle Miller
-/
module

public meta import Batteries.Data.Nat.Basic
public import Mathlib.Tactic.NormNum

/-! # `norm_num` extension for `Nat.sqrt`

This module defines a `norm_num` extension for `Nat.sqrt`.
-/

public meta section

namespace Mathlib.Meta

namespace NormNum

open Qq Lean Elab.Tactic Mathlib.Meta.NormNum

/-
**Mathlib.Meta.NormNum.nat_sqrt_helper** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Meta.N
ormNum`。
形式化陈述：nat_sqrt_helper {x y r : Nat} (hr : y * y + r = x) (hle : Nat.ble r (2 * y
)) : Nat.sqrt x = y
参数：hr : y * y + r = x；hle : Nat.ble r (2 * y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用引理 `Nat.sqrt_add_eq'`：sqrt_add_eq' (n : Nat) (h : a <= n + n) : sqrt (n ^ 2 
+ a) = n
· 使用定理 `Nat.le_of_ble_eq_true`：∀ {n m : ℕ}, n.ble m = true → n ≤ m
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
-/
lemma nat_sqrt_helper {x y r : ℕ} (hr : y * y + r = x) (hle : Nat.ble r (2 * y)) :
    Nat.sqrt x = y := by
  rw [← hr, ← pow_two]
  rw [two_mul] at hle
  exact Nat.sqrt_add_eq' _ (Nat.le_of_ble_eq_true hle)
/-
**Mathlib.Meta.NormNum.isNat_sqrt** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormNu
m`。
形式化陈述：∀ {x nx z : ℕ}, Mathlib.Meta.NormNum.IsNat x nx → nx.sqrt = z → Mathlib.Me
ta.NormNum.IsNat x.sqrt z
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isNat_sqrt : {x nx z : ℕ} → IsNat x nx → Nat.sqrt nx = z → IsNat (Nat.sqrt x) z
  | _, _, _, ⟨rfl⟩, rfl => ⟨rfl⟩

/-- Given the natural number literal `ex`, returns its square root as a natural number literal
and an equality proof. Panics if `ex` isn't a natural number literal. -/
/-
**Mathlib.Meta.NormNum.proveNatSqrt** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Norm
Num`。
形式化陈述：proveNatSqrt (ex : Q(Nat)) : (ey : Q(Nat)) × Q(Nat.sqrt $ex = $ey)
参数：ex : Q(Nat)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given the natural number literal `ex`, returns its square root as a natural numb
er literal
and an equality proof. Panics if `ex` isn't a natural number literal.
-/
def proveNatSqrt (ex : Q(ℕ)) : (ey : Q(ℕ)) × Q(Nat.sqrt $ex = $ey) :=
  match ex.natLit! with
  | 0 => have : $ex =Q nat_lit 0 := ⟨⟩; ⟨q(nat_lit 0), q(Nat.sqrt_zero)⟩
  | 1 => have : $ex =Q nat_lit 1 := ⟨⟩; ⟨q(nat_lit 1), q(Nat.sqrt_one)⟩
  | x =>
    let y := Nat.sqrt x
    have ey : Q(ℕ) := mkRawNatLit y
    have er : Q(ℕ) := mkRawNatLit (x - y * y)
    have hr : Q($ey * $ey + $er = $ex) := (q(Eq.refl $ex) : Expr)
    have hle : Q(Nat.ble $er (2 * $ey)) := (q(Eq.refl true) : Expr)
    ⟨ey, q(nat_sqrt_helper $hr $hle)⟩

/-- Evaluates the `Nat.sqrt` function. -/
@[norm_num Nat.sqrt _]
/-
**Mathlib.Meta.NormNum.evalNatSqrt** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormN
um`。
形式化陈述：evalNatSqrt : NormNumExt where eval {_ _} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluates the `Nat.sqrt` function.
-/
def evalNatSqrt : NormNumExt where eval {_ _} e := do
  let .app _ (x : Q(ℕ)) ← Meta.whnfR e | failure
  let sℕ : Q(AddMonoidWithOne ℕ) := q(Nat.instAddMonoidWithOne)
  let ⟨ex, p⟩ ← deriveNat x sℕ
  let ⟨ey, pf⟩ := proveNatSqrt ex
  let pf' : Q(IsNat (Nat.sqrt $x) $ey) := q(isNat_sqrt $p $pf)
  return .isNat sℕ ey pf'

end NormNum

end Mathlib.Meta

