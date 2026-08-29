/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Ralf Stephan, Neil Strickland, Ruben Van de Velde
-/
module

public import Mathlib.Data.PNat.Defs
public import Mathlib.Logic.Equiv.Defs

/-!
# The equivalence between `ℕ+` and `ℕ`
-/

@[expose] public section

/-- An equivalence between `ℕ+` and `ℕ` given by `PNat.natPred` and `Nat.succPNat`. -/
@[simps -fullyApplied]
/--
Definition of `_root_.Equiv.pnatEquivNat` / `_root_.Equiv.pnatEquivNat` 的定义

English:
definition _root_.Equiv.pnatEquivNat
  signature: : Nat+ ≃ Nat where
  body: PNat.natPred
  invFun := Nat.succPNat
  left_inv := PNat.succPNat_natPred
  right_inv := Nat.natPred_succPNat

中文:
定义 _root_.等价.pnatEquiv自然数
  签名: : 自然数+ ≃ 自然数 where
  定义体: PNat.natPred
  invFun := Nat.succPNat
  left_inv := PNat.succPNat_natPred
  right_inv := Nat.natPred_succPNat

Depends on / 依赖: PNat.natPred, natPred
-/
def _root_.Equiv.pnatEquivNat : Nat+ ≃ Nat where
  toFun := PNat.natPred
  invFun := Nat.succPNat
  left_inv := PNat.succPNat_natPred
  right_inv := Nat.natPred_succPNat
