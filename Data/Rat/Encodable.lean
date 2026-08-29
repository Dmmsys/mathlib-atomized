/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Logic.Encodable.Basic
public import Mathlib.Data.Rat.Init

/-! # The rationals are `Encodable`.

As a consequence we also get the instance `Countable ℚ`.

This is kept separate from `Data.Rat.Defs` in order to minimize imports.
-/

public section


namespace Rat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Encodable Rat
  body: Encodable.ofEquiv (Σ n : Int, { d : Nat // 0 < d ∧ n.natAbs.Coprime d })
    ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, Nat.pos_of_ne_zero c, d⟩,
      fun ⟨a, b, c, d⟩ => ⟨a, b, Nat.pos_iff_ne_zero.mp c, d⟩,
      fun _ => rfl, fun ⟨_, _, _, _⟩ => rfl⟩

中文:
实例 :
  签名: 可编码 有理数
  定义体: Encodable.ofEquiv (Σ n : Int, { d : Nat // 0 < d ∧ n.natAbs.Coprime d })
    ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, Nat.pos_of_ne_zero c, d⟩,
      fun ⟨a, b, c, d⟩ => ⟨a, b, Nat.pos_iff_ne_zero.mp c, d⟩,
      fun _ => rfl, fun ⟨_, _, _, _⟩ => rfl⟩

Depends on / 依赖: Coprime, Encodable, Encodable.ofEquiv, Nat.pos_iff_ne_zero.mp, Nat.pos_of_ne_zero, n.natAbs.Coprime, natAbs, ofEquiv, pos_iff_ne_zero, pos_of_ne_zero
-/
instance : Encodable Rat :=
  Encodable.ofEquiv (Σ n : Int, { d : Nat // 0 < d ∧ n.natAbs.Coprime d })
    ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, Nat.pos_of_ne_zero c, d⟩,
      fun ⟨a, b, c, d⟩ => ⟨a, b, Nat.pos_iff_ne_zero.mp c, d⟩,
      fun _ => rfl, fun ⟨_, _, _, _⟩ => rfl⟩

end Rat
