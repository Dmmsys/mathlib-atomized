/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Nat.Cast.Prod

/-!
# The product of two `AddGroupWithOne`s.
-/

public section


namespace Prod

variable {α β : Type*} [AddGroupWithOne α] [AddGroupWithOne β]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddGroupWithOne (α × β)
  body: { Prod.instAddMonoidWithOne, Prod.instAddGroup with
    intCast := fun n => (n, n)
    intCast_ofNat := fun _ => by ext <;> simp
    intCast_negSucc := fun _ => by ext <;> simp }

@[simp]

中文:
实例 :
  签名: 加法带幺群 (α × β)
  定义体: { Prod.instAddMonoidWithOne, Prod.instAddGroup with
    intCast := fun n => (n, n)
    intCast_ofNat := fun _ => by ext <;> simp
    intCast_negSucc := fun _ => by ext <;> simp }

@[simp]

Depends on / 依赖: Prod.instAddGroup, Prod.instAddMonoidWithOne, instAddGroup, instAddMonoidWithOne, intCast, intCast_negSucc, intCast_ofNat
-/
instance : AddGroupWithOne (α × β) :=
  { Prod.instAddMonoidWithOne, Prod.instAddGroup with
    intCast := fun n => (n, n)
    intCast_ofNat := fun _ => by ext <;> simp
    intCast_negSucc := fun _ => by ext <;> simp }

@[simp]
/--
theorem `fst_intCast` / 定理 `fst_intCast`

English:
theorem fst_intCast
  given: (n : Int)
  statement: (n : α × β).fst = n
  proof: rfl

@[simp]

中文:
定理 fst_intCast
  条件: (n : 整数)
  结论: (n : α × β).fst = n
  证明: rfl

@[simp]
-/
theorem fst_intCast (n : Int) : (n : α × β).fst = n :=
  rfl

@[simp]
/--
theorem `snd_intCast` / 定理 `snd_intCast`

English:
theorem snd_intCast
  given: (n : Int)
  statement: (n : α × β).snd = n
  proof: rfl

中文:
定理 snd_intCast
  条件: (n : 整数)
  结论: (n : α × β).snd = n
  证明: rfl
-/
theorem snd_intCast (n : Int) : (n : α × β).snd = n :=
  rfl

end Prod
