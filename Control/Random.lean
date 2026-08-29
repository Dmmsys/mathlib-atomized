/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

public import Mathlib.Control.ULiftable
public import Mathlib.Order.Fin.Basic

/-!
# Rand Monad and Random Class

This module provides tools for formulating computations guided by randomness and for
defining objects that can be created randomly.

## Main definitions

* `RandT` and `RandGT` monad transformers for computations guided by randomness;
* `Rand` and `RandG` monads as special cases of the above
* `Random` class for objects that can be generated randomly;
  * `random` to generate one object;
* `BoundedRandom` class for objects that can be generated randomly inside a range;
  * `randomR` to generate one object inside a range;
* `IO.runRand` to run a randomized computation inside any monad that has access to `stdGenRef`.

## References

* Similar library in Haskell: https://hackage.haskell.org/package/MonadRandom

-/

@[expose] public section

set_option autoImplicit true -- Note: this file uses `autoImplicit` pervasively

/--
Definition of `RandGT` / `RandGT` 的定义

English:
abbreviation RandGT
  signature: (g : Type)
  body: StateT (ULift g)

中文:
缩写 RandGT
  签名: (g : Type)
  定义体: StateT (ULift g)

Depends on / 依赖: StateT
-/
abbrev RandGT (g : Type) := StateT (ULift g)
/--
Definition of `RandG` / `RandG` 的定义

English:
abbreviation RandG
  signature: (g : Type)
  body: RandGT g Id

中文:
缩写 RandG
  签名: (g : Type)
  定义体: RandGT g Id

Depends on / 依赖: RandGT
-/
abbrev RandG (g : Type) := RandGT g Id

/--
Definition of `RandT` / `RandT` 的定义

English:
abbreviation RandT
  body: RandGT StdGen

中文:
缩写 RandT
  定义体: RandGT StdGen

Depends on / 依赖: RandGT, StdGen
-/
abbrev RandT := RandGT StdGen

/--
Definition of `Rand` / `Rand` 的定义

English:
abbreviation Rand
  body: RandG StdGen

中文:
缩写 Rand
  定义体: RandG StdGen

Depends on / 依赖: StdGen
-/
abbrev Rand := RandG StdGen

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MonadLift
  signature: m n] : MonadLiftT (RandGT g m) (RandGT g n) where
  body: fun s => x s

中文:
实例 [MonadLift
  签名: m n] : MonadLiftT (RandGT g m) (RandGT g n) where
  定义体: fun s => x s
-/
instance [MonadLift m n] : MonadLiftT (RandGT g m) (RandGT g n) where
  monadLift x := fun s => x s

/--
Definition of `Random` / `Random` 的定义

English:
class Random
  parameters: (m) (α : Type u)
  axioms and operations (1):
    - random([RandomGen g]) : RandGT g m α

中文:
类 Random
  参数: (m) (α : 类型u)
  公理与运算 (1 个):
    - random([RandomGen g]) : RandGT g m α

Depends on / 依赖: decidable_of_iff, lookup_isSome
-/
class Random (m) (α : Type u) where
  /-- Sample an element of this type from the provided generator. -/
  random [RandomGen g] : RandGT g m α

/--
Definition of `BoundedRandom` / `BoundedRandom` 的定义

English:
class BoundedRandom
  parameters: (m) (α : Type u) [Preorder α]
  axioms and operations (1):
    - randomR({g : Type} (lo hi : α) (h : lo <= hi) [RandomGen g]) : RandGT g m {a // lo <= a ∧ a <= hi}

中文:
类 BoundedRandom
  参数: (m) (α : 类型u) [Preorder α]
  公理与运算 (1 个):
    - randomR({g : Type} (lo hi : α) (h : lo <= hi) [RandomGen g]) : RandGT g m {a // lo <= a ∧ a <= hi}
-/
class BoundedRandom (m) (α : Type u) [Preorder α] where
  /-- Sample a bounded element of this type from the provided generator. -/
  randomR {g : Type} (lo hi : α) (h : lo <= hi) [RandomGen g] : RandGT g m {a // lo <= a ∧ a <= hi}

namespace Rand
/--
Definition of `next` / `next` 的定义

English:
definition next
  signature: [RandomGen g] [Monad m]
  body: do
  let rng := (← get).down
  let (res, new) := RandomGen.next rng
  set (ULift.up new)
  pure res

中文:
定义 next
  签名: [RandomGen g] [Monad m]
  定义体: do
  let rng := (← get).down
  let (res, new) := RandomGen.next rng
  set (ULift.up new)
  pure res
-/
def next [RandomGen g] [Monad m] : RandGT g m Nat := do
  let rng := (← get).down
  let (res, new) := RandomGen.next rng
  set (ULift.up new)
  pure res

/--
Definition of `split` / `split` 的定义

English:
definition split
  signature: {g : Type} [RandomGen g] [Monad m]
  body: do
  let rng := (← get).down
  let (r1, r2) := RandomGen.split rng
  set (ULift.up r1)
  pure r2

中文:
定义 split
  签名: {g : Type} [RandomGen g] [Monad m]
  定义体: do
  let rng := (← get).down
  let (r1, r2) := RandomGen.split rng
  set (ULift.up r1)
  pure r2
-/
def split {g : Type} [RandomGen g] [Monad m] : RandGT g m g := do
  let rng := (← get).down
  let (r1, r2) := RandomGen.split rng
  set (ULift.up r1)
  pure r2

/--
Definition of `range` / `range` 的定义

English:
definition range
  signature: {g : Type} [RandomGen g] [Monad m]
  body: do
  let rng := (← get).down
pure RandomGen.range rng

中文:
定义 range
  签名: {g : Type} [RandomGen g] [Monad m]
  定义体: do
  let rng := (← get).down
pure RandomGen.range rng
-/
def range {g : Type} [RandomGen g] [Monad m] : RandGT g m (Nat × Nat) := do
  let rng := (← get).down
pure RandomGen.range rng
end Rand

namespace Random

open Rand

variable [Monad m]

/--
Definition of `rand` / `rand` 的定义

English:
definition rand
  signature: (α : Type u) [Random m α] [RandomGen g]
  body: Random.random

中文:
定义 rand
  签名: (α : 类型u) [Random m α] [RandomGen g]
  定义体: Random.random

Depends on / 依赖: Random, Random.random, random
-/
def rand (α : Type u) [Random m α] [RandomGen g] : RandGT g m α := Random.random

/--
Definition of `randBound` / `randBound` 的定义

English:
definition randBound
  signature: (α : Type u)
  body: (BoundedRandom.randomR lo hi h : RandGT g _ _)

中文:
定义 randBound
  签名: (α : 类型u)
  定义体: (BoundedRandom.randomR lo hi h : RandGT g _ _)

Depends on / 依赖: BoundedRandom, BoundedRandom.randomR, RandGT, randomR
-/
def randBound (α : Type u)
    [Preorder α] [BoundedRandom m α] (lo hi : α) (h : lo <= hi) [RandomGen g] :
    RandGT g m {a // lo <= a ∧ a <= hi} :=
  (BoundedRandom.randomR lo hi h : RandGT g _ _)

/--
Definition of `randFin` / `randFin` 的定义

English:
definition randFin
  signature: {n : Nat} [NeZero n] [RandomGen g]
  body: fun ⟨g⟩ => pure .map (Fin.ofNat n) ULift.up randNat g 0 (n - 1)

中文:
定义 randFin
  签名: {n : 自然数} [NeZero n] [RandomGen g]
  定义体: fun ⟨g⟩ => pure .map (Fin.ofNat n) ULift.up randNat g 0 (n - 1)

Depends on / 依赖: Fin.ofNat, ULift.up, randNat
-/
def randFin {n : Nat} [NeZero n] [RandomGen g] : RandGT g m (Fin n) :=
fun ⟨g⟩ => pure .map (Fin.ofNat n) ULift.up randNat g 0 (n - 1)

instance {n : Nat} [NeZero n] : Random m (Fin n) where
  random := randFin

/--
Definition of `randBool` / `randBool` 的定义

English:
definition randBool
  signature: [RandomGen g]
  body: return (← rand (Fin 2)) == 1

中文:
定义 randBool
  签名: [RandomGen g]
  定义体: return (← rand (Fin 2)) == 1

Depends on / 依赖: return
-/
def randBool [RandomGen g] : RandGT g m Bool :=
  return (← rand (Fin 2)) == 1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Random m Bool
  body: randBool

中文:
实例 :
  签名: Random m 布尔
  定义体: randBool

Depends on / 依赖: randBool
-/
instance : Random m Bool where
  random := randBool

instance {α : Type u} [ULiftable m m'] [Random m α] : Random m' (ULift.{v} α) where
  random := ULiftable.up random

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BoundedRandom m Nat
  body: do
    let z ← rand (Fin (hi - lo + 1))
    pure ⟨
      lo + z.val, Nat.le_add_right _ _,
      Nat.add_le_of_le_sub' h (Nat.le_of_lt_add_one z.isLt)
    ⟩

中文:
实例 :
  签名: BoundedRandom m 自然数
  定义体: do
    let z ← rand (Fin (hi - lo + 1))
    pure ⟨
      lo + z.val, Nat.le_add_right _ _,
      Nat.add_le_of_le_sub' h (Nat.le_of_lt_add_one z.isLt)
    ⟩
-/
instance : BoundedRandom m Nat where
  randomR lo hi h _ := do
    let z ← rand (Fin (hi - lo + 1))
    pure ⟨
      lo + z.val, Nat.le_add_right _ _,
      Nat.add_le_of_le_sub' h (Nat.le_of_lt_add_one z.isLt)
    ⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BoundedRandom m Int
  body: do
    let ⟨z, _, h2⟩ ← randBound Nat 0 (Int.natAbs <| hi - lo) (Nat.zero_le _)
    pure ⟨
      z + lo,
      Int.le_add_of_nonneg_left (Int.natCast_nonneg z),
Int.add_le_of_le_sub_right Int.le_trans
        (Int.ofNat_le.mpr h2)
        (le_of_eq <| Int.natAbs_of_nonneg <| Int.sub_nonneg_of_le h)⟩

中文:
实例 :
  签名: BoundedRandom m 整数
  定义体: do
    let ⟨z, _, h2⟩ ← randBound Nat 0 (Int.natAbs <| hi - lo) (Nat.zero_le _)
    pure ⟨
      z + lo,
      Int.le_add_of_nonneg_left (Int.natCast_nonneg z),
Int.add_le_of_le_sub_right Int.le_trans
        (Int.ofNat_le.mpr h2)
        (le_of_eq <| Int.natAbs_of_nonneg <| Int.sub_nonneg_of_le h)⟩
-/
instance : BoundedRandom m Int where
  randomR lo hi h _ := do
    let ⟨z, _, h2⟩ ← randBound Nat 0 (Int.natAbs <| hi - lo) (Nat.zero_le _)
    pure ⟨
      z + lo,
      Int.le_add_of_nonneg_left (Int.natCast_nonneg z),
Int.add_le_of_le_sub_right Int.le_trans
        (Int.ofNat_le.mpr h2)
        (le_of_eq <| Int.natAbs_of_nonneg <| Int.sub_nonneg_of_le h)⟩

instance {n : Nat} : BoundedRandom m (Fin n) where
  randomR lo hi h _ := do
    let ⟨r, h1, h2⟩ ← randBound Nat lo.val hi.val h
    pure ⟨⟨r, Nat.lt_of_le_of_lt h2 hi.isLt⟩, h1, h2⟩

instance {α : Type u} [Preorder α] [ULiftable m m'] [BoundedRandom m α] [Monad m'] :
    BoundedRandom m' (ULift.{v} α) where
  randomR lo hi h := do
    let ⟨x⟩ ← ULiftable.up.{v} (BoundedRandom.randomR lo.down hi.down h)
    pure ⟨ULift.up x.val, x.prop⟩

end Random

namespace IO

variable {m : Type* -> Type*} {m₀ : Type -> Type}
variable [Monad m] [MonadLiftT (ST RealWorld) m₀] [ULiftable m₀ m]

/--
Definition of `runRand` / `runRand` 的定义

English:
definition runRand
  signature: (cmd : RandT m α)
  body: do
  let stdGen ← ULiftable.up (stdGenRef.get : m₀ _)
  let (res, new) ← StateT.run cmd stdGen
  let _ ← ULiftable.up (stdGenRef.set new.down : m₀ _)
  pure res

中文:
定义 runRand
  签名: (cmd : RandT m α)
  定义体: do
  let stdGen ← ULiftable.up (stdGenRef.get : m₀ _)
  let (res, new) ← StateT.run cmd stdGen
  let _ ← ULiftable.up (stdGenRef.set new.down : m₀ _)
  pure res
-/
def runRand (cmd : RandT m α) : m α := do
  let stdGen ← ULiftable.up (stdGenRef.get : m₀ _)
  let (res, new) ← StateT.run cmd stdGen
  let _ ← ULiftable.up (stdGenRef.set new.down : m₀ _)
  pure res

/--
Definition of `runRandWith` / `runRandWith` 的定义

English:
definition runRandWith
  signature: (seed : Nat) (cmd : RandT m α)
  body: do
pure (← cmd.run (ULift.up <| mkStdGen seed)).1

中文:
定义 runRandWith
  签名: (seed : 自然数) (cmd : RandT m α)
  定义体: do
pure (← cmd.run (ULift.up <| mkStdGen seed)).1
-/
def runRandWith (seed : Nat) (cmd : RandT m α) : m α := do
pure (← cmd.run (ULift.up <| mkStdGen seed)).1

end IO
