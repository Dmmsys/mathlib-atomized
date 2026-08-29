/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Data.Nat.Cast.Defs

/-!
# The product of two `AddMonoidWithOne`s.
-/

public section

assert_not_exists MonoidWithZero

variable {α β : Type*}

namespace Prod

variable [AddMonoidWithOne α] [AddMonoidWithOne β]

/--
Instance `instAddMonoidWithOne` / 实例 `instAddMonoidWithOne`

English:
instance instAddMonoidWithOne
  signature: : AddMonoidWithOne (α × β)
  body: { Prod.instAddMonoid, @Prod.instOne α β _ _ with
    natCast := fun n => (n, n)
    natCast_zero := congr_arg₂ Prod.mk Nat.cast_zero Nat.cast_zero
    natCast_succ := fun _ => congr_arg₂ Prod.mk (Nat.cast_succ _) (Nat.cast_succ _) }

@[simp]

中文:
实例 instAddMonoidWithOne
  签名: : AddMonoidWithOne (α × β)
  定义体: { Prod.instAddMonoid, @Prod.instOne α β _ _ with
    natCast := fun n => (n, n)
    natCast_zero := congr_arg₂ Prod.mk Nat.cast_zero Nat.cast_zero
    natCast_succ := fun _ => congr_arg₂ Prod.mk (Nat.cast_succ _) (Nat.cast_succ _) }

@[simp]

Depends on / 依赖: Nat.cast_succ, Nat.cast_zero, Prod.instAddMonoid, Prod.instOne, Prod.mk, cast_succ, cast_zero, instAddMonoid, instOne, natCast, natCast_succ, natCast_zero
-/
instance instAddMonoidWithOne : AddMonoidWithOne (α × β) :=
  { Prod.instAddMonoid, @Prod.instOne α β _ _ with
    natCast := fun n => (n, n)
    natCast_zero := congr_arg₂ Prod.mk Nat.cast_zero Nat.cast_zero
    natCast_succ := fun _ => congr_arg₂ Prod.mk (Nat.cast_succ _) (Nat.cast_succ _) }

@[simp]
/--
theorem `fst_natCast` / 定理 `fst_natCast`

English:
theorem fst_natCast
  given: (n : Nat)
  statement: (n : α × β).fst = n
  proof: by induction n <;> simp [*]

@[simp]

中文:
定理 fst_natCast
  条件: (n : 自然数)
  结论: (n : α × β).fst = n
  证明: by induction n <;> simp [*]

@[simp]
-/
theorem fst_natCast (n : Nat) : (n : α × β).fst = n := by induction n <;> simp [*]

@[simp]
/--
theorem `fst_ofNat` / 定理 `fst_ofNat`

English:
theorem fst_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: rfl

@[simp]

中文:
定理 fst_ofNat
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: rfl

@[simp]
-/
theorem fst_ofNat (n : Nat) [n.AtLeastTwo] :
    (ofNat(n) : α × β).1 = (ofNat(n) : α) :=
  rfl

@[simp]
/--
theorem `snd_natCast` / 定理 `snd_natCast`

English:
theorem snd_natCast
  given: (n : Nat)
  statement: (n : α × β).snd = n
  proof: by induction n <;> simp [*]

@[simp]

中文:
定理 snd_natCast
  条件: (n : 自然数)
  结论: (n : α × β).snd = n
  证明: by induction n <;> simp [*]

@[simp]
-/
theorem snd_natCast (n : Nat) : (n : α × β).snd = n := by induction n <;> simp [*]

@[simp]
/--
theorem `snd_ofNat` / 定理 `snd_ofNat`

English:
theorem snd_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: rfl

中文:
定理 snd_ofNat
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: rfl
-/
theorem snd_ofNat (n : Nat) [n.AtLeastTwo] :
    (ofNat(n) : α × β).2 = (ofNat(n) : β) :=
  rfl

end Prod
