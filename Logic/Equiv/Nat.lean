/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.Nat.Pairing

/-!
# Equivalences involving `ℕ`

This file defines some additional constructive equivalences using `Encodable` and the pairing
function on `ℕ`.
-/

@[expose] public section

assert_not_exists Monoid

open Nat Function

namespace Equiv

variable {α : Type*}

/-- An equivalence between `Bool × ℕ` and `ℕ`, by mapping `(true, x)` to `2 * x + 1` and
`(false, x)` to `2 * x`. -/
@[simps]
/-
**Equiv.boolProdNatEquivNat** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：boolProdNatEquivNat : Bool × Nat ≃ Nat where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence between `Bool × ℕ` and `ℕ`, by mapping `(true, x)` to `2 * x + 1`
 and
`(false, x)` to `2 * x`.
-/
def boolProdNatEquivNat : Bool × ℕ ≃ ℕ where
  toFun := uncurry bit
  invFun n := ⟨n.bodd, n.div2⟩
  left_inv := fun ⟨b, n⟩ => by simp
  right_inv n := by simp

/-- An equivalence between `ℕ ⊕ ℕ` and `ℕ`, by mapping `(Sum.inl x)` to `2 * x` and `(Sum.inr x)` to
`2 * x + 1`.
-/
@[simps! symm_apply]
/-
**Equiv.natSumNatEquivNat** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：natSumNatEquivNat : Nat oplus Nat ≃ Nat
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
An equivalence between `ℕ ⊕ ℕ` and `ℕ`, by mapping `(Sum.inl x)` to `2 * x` and 
`(Sum.inr x)` to
`2 * x + 1`.
-/
def natSumNatEquivNat : ℕ ⊕ ℕ ≃ ℕ :=
  (boolProdEquivSum ℕ).symm.trans boolProdNatEquivNat

@[simp]
/-
**Equiv.natSumNatEquivNat_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：natSumNatEquivNat_apply : ⇑natSumNatEquivNat = Sum.elim (2 * ·) (2 * · + 1
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem natSumNatEquivNat_apply : ⇑natSumNatEquivNat = Sum.elim (2 * ·) (2 * · + 1) := by
  ext (x | x) <;> rfl

/-- An equivalence between `ℤ` and `ℕ`, through `ℤ ≃ ℕ ⊕ ℕ` and `ℕ ⊕ ℕ ≃ ℕ`.
-/
/-
**Equiv.intEquivNat** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：intEquivNat : Int ≃ Nat
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
An equivalence between `ℤ` and `ℕ`, through `ℤ ≃ ℕ ⊕ ℕ` and `ℕ ⊕ ℕ ≃ ℕ`.
-/
def intEquivNat : ℤ ≃ ℕ :=
  intEquivNatSumNat.trans natSumNatEquivNat

/-- An equivalence between `α × α` and `α`, given that there is an equivalence between `α` and `ℕ`.
-/
/-
**Equiv.prodEquivOfEquivNat** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：prodEquivOfEquivNat (e : α ≃ Nat) : α × α ≃ α
参数：e : α ≃ Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
An equivalence between `α × α` and `α`, given that there is an equivalence betwe
en `α` and `ℕ`.
-/
def prodEquivOfEquivNat (e : α ≃ ℕ) : α × α ≃ α :=
  calc
    α × α ≃ ℕ × ℕ := prodCongr e e
    _ ≃ ℕ := pairEquiv
    _ ≃ α := e.symm

end Equiv

