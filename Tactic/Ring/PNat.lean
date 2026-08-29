/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public meta import Mathlib.Tactic.Ring.Basic
public meta import Mathlib.Data.PNat.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.Tactic.Ring.Basic

/-!
# Additional instances for `ring` over `PNat`

This adds some instances which enable `ring` to work on `PNat` even though it is not a commutative
semiring, by lifting to `Nat`.
-/

public meta section

namespace Mathlib.Tactic.Ring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CSLift Nat+ Nat
  body: PNat.val
  inj := PNat.coe_injective

中文:
实例 :
  签名: CSLift 自然数+ 自然数
  定义体: PNat.val
  inj := PNat.coe_injective

Depends on / 依赖: PNat.val
-/
instance : CSLift Nat+ Nat where
  lift := PNat.val
  inj := PNat.coe_injective

-- FIXME: this `no_index` seems to be in the wrong place, but
-- #synth CSLiftVal (3 : ℕ+) _ doesn't work otherwise
instance {n} : CSLiftVal (no_index (OfNat.ofNat (n + 1)) : Nat+) (n + 1) := ⟨rfl⟩

instance {n h} : CSLiftVal (Nat.toPNat n h) n := ⟨rfl⟩


instance {n} : CSLiftVal (Nat.succPNat n) (n + 1) := ⟨rfl⟩

instance {n} : CSLiftVal (Nat.toPNat' n) (n.pred + 1) := ⟨rfl⟩

instance {n k} : CSLiftVal (PNat.divExact n k) (n.div k + 1) := ⟨rfl⟩

instance {n n' k k'} [h1 : CSLiftVal (n : Nat+) n'] [h2 : CSLiftVal (k : Nat+) k'] :
    CSLiftVal (n + k) (n' + k') := ⟨by simp [h1.1, h2.1, CSLift.lift]⟩

instance {n n' k k'} [h1 : CSLiftVal (n : Nat+) n'] [h2 : CSLiftVal (k : Nat+) k'] :
    CSLiftVal (n * k) (n' * k') := ⟨by simp [h1.1, h2.1, CSLift.lift]⟩

instance {n n' k} [h1 : CSLiftVal (n : Nat+) n'] :
    CSLiftVal (n ^ k) (n' ^ k) := ⟨by simp [h1.1, CSLift.lift]⟩

end Ring

end Mathlib.Tactic
