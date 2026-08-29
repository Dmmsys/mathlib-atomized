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
/--
Definition of `boolProdNatEquivNat` / `boolProdNatEquivNat` 的定义

English:
definition boolProdNatEquivNat
  signature: : Bool × Nat ≃ Nat where
  body: uncurry bit
  invFun n := ⟨n.bodd, n.div2⟩
  left_inv := fun ⟨b, n⟩ => by simp
  right_inv n := by simp

中文:
定义 boolProdNatEquivNat
  签名: : 布尔 × 自然数 ≃ 自然数 where
  定义体: uncurry bit
  invFun n := ⟨n.bodd, n.div2⟩
  left_inv := fun ⟨b, n⟩ => by simp
  right_inv n := by simp

Depends on / 依赖: uncurry
-/
def boolProdNatEquivNat : Bool × Nat ≃ Nat where
  toFun := uncurry bit
  invFun n := ⟨n.bodd, n.div2⟩
  left_inv := fun ⟨b, n⟩ => by simp
  right_inv n := by simp

/-- An equivalence between `ℕ ⊕ ℕ` and `ℕ`, by mapping `(Sum.inl x)` to `2 * x` and `(Sum.inr x)` to
`2 * x + 1`.
-/
@[simps! symm_apply]
/--
Definition of `natSumNatEquivNat` / `natSumNatEquivNat` 的定义

English:
definition natSumNatEquivNat
  signature: : Nat oplus Nat ≃ Nat
  body: (boolProdEquivSum Nat).symm.trans boolProdNatEquivNat

@[simp]

中文:
定义 natSumNatEquivNat
  签名: : 自然数 oplus 自然数 ≃ 自然数
  定义体: (boolProdEquivSum Nat).symm.trans boolProdNatEquivNat

@[simp]

Depends on / 依赖: boolProdEquivSum, boolProdNatEquivNat, symm.trans
-/
def natSumNatEquivNat : Nat oplus Nat ≃ Nat :=
  (boolProdEquivSum Nat).symm.trans boolProdNatEquivNat

@[simp]
/--
theorem `natSumNatEquivNat_apply` / 定理 `natSumNatEquivNat_apply`

English:
theorem natSumNatEquivNat_apply
  statement: ⇑natSumNatEquivNat = Sum.elim (2 * ·) (2 * · + 1)
  proof: by
  ext (x | x) <;> rfl

中文:
定理 natSumNatEquivNat_apply
  结论: ⇑natSum自然数Equiv自然数 = Sum.elim (2 * ·) (2 * · + 1)
  证明: by
  ext (x | x) <;> rfl
-/
theorem natSumNatEquivNat_apply : ⇑natSumNatEquivNat = Sum.elim (2 * ·) (2 * · + 1) := by
  ext (x | x) <;> rfl

/--
Definition of `intEquivNat` / `intEquivNat` 的定义

English:
definition intEquivNat
  signature: : Int ≃ Nat
  body: intEquivNatSumNat.trans natSumNatEquivNat

中文:
定义 intEquivNat
  签名: : 整数 ≃ 自然数
  定义体: intEquivNatSumNat.trans natSumNatEquivNat

Depends on / 依赖: intEquivNatSumNat, intEquivNatSumNat.trans, natSumNatEquivNat
-/
def intEquivNat : Int ≃ Nat :=
  intEquivNatSumNat.trans natSumNatEquivNat

/--
Definition of `prodEquivOfEquivNat` / `prodEquivOfEquivNat` 的定义

English:
definition prodEquivOfEquivNat
  signature: (e : α ≃ Nat)
  body: calc
    α × α ≃ Nat × Nat := prodCongr e e
    _ ≃ Nat := pairEquiv
    _ ≃ α := e.symm

中文:
定义 prodEquivOfEquivNat
  签名: (e : α ≃ 自然数)
  定义体: calc
    α × α ≃ Nat × Nat := prodCongr e e
    _ ≃ Nat := pairEquiv
    _ ≃ α := e.symm

Depends on / 依赖: e.symm, pairEquiv, prodCongr
-/
def prodEquivOfEquivNat (e : α ≃ Nat) : α × α ≃ α :=
  calc
    α × α ≃ Nat × Nat := prodCongr e e
    _ ≃ Nat := pairEquiv
    _ ≃ α := e.symm

end Equiv
