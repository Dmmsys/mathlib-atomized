/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Yury Kudryashov
-/
module

public import Batteries.Tactic.Alias
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.TypeTags

/-! # Definition and notation for extended natural numbers -/

@[expose] public section

/--
Definition of `ENat` / `ENat` 的定义

English:
definition ENat
  signature: : Type
  body: WithTop Nat deriving Top, Inhabited

@[inherit_doc] notation "Nat∞" => ENat

中文:
定义 E自然数
  签名: : 类型
  定义体: WithTop Nat deriving Top, Inhabited

@[inherit_doc] notation "Nat∞" => ENat

Depends on / 依赖: Inhabited, WithTop, deriving
-/
def ENat : Type := WithTop Nat deriving Top, Inhabited

@[inherit_doc] notation "Nat∞" => ENat

namespace ENat

/--
Instance `instNatCast` / 实例 `instNatCast`

English:
instance instNatCast
  signature: : NatCast Nat∞
  body: ⟨WithTop.some⟩

中文:
实例 inst自然数Cast
  签名: : 自然数嵌入 自然数∞
  定义体: ⟨WithTop.some⟩

Depends on / 依赖: WithTop, WithTop.some
-/
instance instNatCast : NatCast Nat∞ := ⟨WithTop.some⟩

/-- Recursor for `ENat` using the preferred forms `⊤` and `↑a`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
/--
Definition of `recTopCoe` / `recTopCoe` 的定义

English:
definition recTopCoe
  signature: {C : Nat∞ -> Sort*} (top : C ⊤) (coe : forall a : Nat, C a)

中文:
定义 recTopCoe
  签名: {C : 自然数∞ -> 类型层*} (top : C ⊤) (coe : 对任意 a : 自然数, C a)
-/
def recTopCoe {C : Nat∞ -> Sort*} (top : C ⊤) (coe : forall a : Nat, C a) : forall n : Nat∞, C n
  | none => top
  | Option.some a => coe a

@[simp]
/--
theorem `recTopCoe_top` / 定理 `recTopCoe_top`

English:
theorem recTopCoe_top
  given: {C : Nat∞ -> Sort*} (d : C ⊤) (f : forall a : Nat, C a)
  proof: rfl

@[simp]

中文:
定理 recTopCoe_top
  条件: {C : 自然数∞ -> 类型层*} (d : C ⊤) (f : 对任意 a : 自然数, C a)
  证明: rfl

@[simp]
-/
theorem recTopCoe_top {C : Nat∞ -> Sort*} (d : C ⊤) (f : forall a : Nat, C a) :
    @recTopCoe C d f ⊤ = d :=
  rfl

@[simp]
/--
theorem `recTopCoe_natCast` / 定理 `recTopCoe_natCast`

English:
theorem recTopCoe_natCast
  given: {C : Nat∞ -> Sort*} (d : C ⊤) (f : forall a : Nat, C a) (x : Nat)
  proof: rfl

@[deprecated (since := "2026-07-17")] alias recTopCoe_coe := recTopCoe_natCast

中文:
定理 recTopCoe_natCast
  条件: {C : 自然数∞ -> 类型层*} (d : C ⊤) (f : 对任意 a : 自然数, C a) (x : 自然数)
  证明: rfl

@[deprecated (since := "2026-07-17")] alias recTopCoe_coe := recTopCoe_natCast
-/
theorem recTopCoe_natCast {C : Nat∞ -> Sort*} (d : C ⊤) (f : forall a : Nat, C a) (x : Nat) :
    @recTopCoe C d f ↑x = f x :=
  rfl

@[deprecated (since := "2026-07-17")] alias recTopCoe_coe := recTopCoe_natCast

end ENat
