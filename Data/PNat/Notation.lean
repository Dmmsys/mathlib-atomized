/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Yury Kudryashov
-/
module

public import Mathlib.Data.Nat.Notation

/-! # Definition and notation for positive natural numbers -/

@[expose] public section

/--
Definition of `PNat` / `PNat` 的定义

English:
definition PNat
  body: { n : Nat // 0 < n } deriving DecidableEq

@[inherit_doc]
notation "Nat+" => PNat

中文:
定义 正自然数
  定义体: { n : Nat // 0 < n } deriving DecidableEq

@[inherit_doc]
notation "Nat+" => PNat

Depends on / 依赖: DecidableEq, deriving
-/
def PNat := { n : Nat // 0 < n } deriving DecidableEq

@[inherit_doc]
notation "Nat+" => PNat

/-- The underlying natural number -/
@[coe]
/--
Definition of `PNat.val` / `PNat.val` 的定义

English:
definition PNat.val
  signature: : Nat+ -> Nat
  body: Subtype.val

中文:
定义 正自然数.val
  签名: : 自然数+ -> 自然数
  定义体: Subtype.val

Depends on / 依赖: Subtype, Subtype.val
-/
def PNat.val : Nat+ -> Nat := Subtype.val

/--
Instance `coePNatNat` / 实例 `coePNatNat`

English:
instance coePNatNat
  signature: : Coe Nat+ Nat
  body: ⟨PNat.val⟩

中文:
实例 coeP自然数自然数
  签名: : Coe 自然数+ 自然数
  定义体: ⟨PNat.val⟩

Depends on / 依赖: PNat.val
-/
instance coePNatNat : Coe Nat+ Nat :=
  ⟨PNat.val⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Repr Nat+
  body: ⟨fun n n' => reprPrec n.1 n'⟩

中文:
实例 :
  签名: Repr 自然数+
  定义体: ⟨fun n n' => reprPrec n.1 n'⟩

Depends on / 依赖: reprPrec
-/
instance : Repr Nat+ :=
  ⟨fun n n' => reprPrec n.1 n'⟩
