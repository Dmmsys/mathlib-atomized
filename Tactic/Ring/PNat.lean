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

/-
**Mathlib.Tactic.Ring.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Ring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CSLift ℕ+ Nat where
  lift := PNat.val
  inj := PNat.coe_injective

-- FIXME: this `no_index` seems to be in the wrong place, but
-- #synth CSLiftVal (3 : ℕ+) _ doesn't work otherwise
/-
**Mathlib.Tactic.Ring.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Ring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n} : CSLiftVal (no_index (OfNat.ofNat (n + 1)) : ℕ+) (n + 1) := ⟨rfl⟩
/-
**Mathlib.Tactic.Ring.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Ring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n h} : CSLiftVal (Nat.toPNat n h) n := ⟨rfl⟩
/-
**Mathlib.Tactic.Ring.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Ring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n} : CSLiftVal (Nat.succPNat n) (n + 1) := ⟨rfl⟩
/-
**Mathlib.Tactic.Ring.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Ring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n} : CSLiftVal (Nat.toPNat' n) (n.pred + 1) := ⟨rfl⟩
/-
**Mathlib.Tactic.Ring.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Ring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n k} : CSLiftVal (PNat.divExact n k) (n.div k + 1) := ⟨rfl⟩
/-
**Mathlib.Tactic.Ring.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Ring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n n' k k'} [h1 : CSLiftVal (n : ℕ+) n'] [h2 : CSLiftVal (k : ℕ+) k'] :
    CSLiftVal (n + k) (n' + k') := ⟨by simp [h1.1, h2.1, CSLift.lift]⟩
/-
**Mathlib.Tactic.Ring.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Ring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n n' k k'} [h1 : CSLiftVal (n : ℕ+) n'] [h2 : CSLiftVal (k : ℕ+) k'] :
    CSLiftVal (n * k) (n' * k') := ⟨by simp [h1.1, h2.1, CSLift.lift]⟩
/-
**Mathlib.Tactic.Ring.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Ring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n n' k} [h1 : CSLiftVal (n : ℕ+) n'] :
    CSLiftVal (n ^ k) (n' ^ k) := ⟨by simp [h1.1, CSLift.lift]⟩

end Ring

end Mathlib.Tactic

