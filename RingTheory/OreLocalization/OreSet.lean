/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Kevin Klinge
-/
module

public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Ring.Regular
public import Mathlib.GroupTheory.OreLocalization.OreSet

/-!

# (Left) Ore sets and rings

This file contains results on left Ore sets for rings and monoids with zero.

## References

* https://ncatlab.org/nlab/show/Ore+set

-/

@[expose] public section

assert_not_exists RelIso

namespace OreLocalization

/-- Cancellability in monoids with zeros can act as a replacement for the `ore_right_cancel`
condition of an ore set. -/
@[instance_reducible]
/-
**OreLocalization.oreSetOfIsCancelMulZero** 是 Mathlib 中的一个定义，位于命名空间 `OreLocaliza
tion`。
形式化陈述：oreSetOfIsCancelMulZero {R : Type*} [MonoidWithZero R] [IsCancelMulZero R]
 {S : Submonoid R} (oreNum : R -> S -> R) (oreDenom : R -> S -> S) (ore_eq : for
all (r : R) (s : S), oreDenom r s * r = oreNum r s * s) : OreSet S
参数：oreNum : R -> S -> R；oreDenom : R -> S -> S；ore_eq : forall (r : R) (s : S), 
oreDenom r s * r = oreNum r s * s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cancellability in monoids with zeros can act as a replacement for the `ore_right
_cancel`
condition of an ore set.
-/
def oreSetOfIsCancelMulZero {R : Type*} [MonoidWithZero R] [IsCancelMulZero R]
    {S : Submonoid R} (oreNum : R → S → R) (oreDenom : R → S → S)
    (ore_eq : ∀ (r : R) (s : S), oreDenom r s * r = oreNum r s * s) : OreSet S :=
  { ore_right_cancel := fun _ _ s h => ⟨s, mul_eq_mul_left_iff.mpr (mul_eq_mul_right_iff.mp h)⟩
    oreNum
    oreDenom
    ore_eq }

@[deprecated (since := "2026-01-12")] alias oreSetOfCancelMonoidWithZero := oreSetOfIsCancelMulZero

/-- In rings without zero divisors, the first (cancellability) condition is always fulfilled,
it suffices to give a proof for the Ore condition itself. -/
@[instance_reducible]
/-
**OreLocalization.oreSetOfNoZeroDivisors** 是 Mathlib 中的一个定义，位于命名空间 `OreLocalizat
ion`。
形式化陈述：oreSetOfNoZeroDivisors {R : Type*} [Ring R] [NoZeroDivisors R] {S : Submon
oid R} (oreNum : R -> S -> R) (oreDenom : R -> S -> S) (ore_eq : forall (r : R) 
(s : S), oreDenom r s * r = oreNum r s * s) : OreSet S
参数：oreNum : R -> S -> R；oreDenom : R -> S -> S；ore_eq : forall (r : R) (s : S), 
oreDenom r s * r = oreNum r s * s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In rings without zero divisors, the first (cancellability) condition is always f
ulfilled,
it suffices to give a proof for the Ore condition itself.
-/
def oreSetOfNoZeroDivisors {R : Type*} [Ring R] [NoZeroDivisors R] {S : Submonoid R}
    (oreNum : R → S → R) (oreDenom : R → S → S)
    (ore_eq : ∀ (r : R) (s : S), oreDenom r s * r = oreNum r s * s) : OreSet S :=
  letI : IsCancelMulZero R := NoZeroDivisors.toIsCancelMulZero
  oreSetOfIsCancelMulZero oreNum oreDenom ore_eq
/-
**OreLocalization.nonempty_oreSet_iff** 是 Mathlib 中的一个引理，位于命名空间 `OreLocalization
`。
形式化陈述：nonempty_oreSet_iff {R : Type*} [Monoid R] {S : Submonoid R} : Nonempty (O
reSet S) ↔ (forall (r₁ r₂ : R) (s : S), r₁ * s = r₂ * s -> exists s' : S, s' * r
₁ = s' * r₂) ∧ (forall (r : R) (s : S), exists (r' : R) (s' : S), s' * r = r' * 
s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.ore_right_cancel`：ore_right_cancel (r₁ r₂ : R) (s : S) (
h : r₁ * s = r₂ * s) : exists s' : S, s' * r₁ = s' * r₂
· 使用定理 `OreLocalization.ore_eq`：ore_eq (r : R) (s : S) : oreDenom r s * r = oreN
um r s * s
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma nonempty_oreSet_iff {R : Type*} [Monoid R] {S : Submonoid R} :
    Nonempty (OreSet S) ↔ (∀ (r₁ r₂ : R) (s : S), r₁ * s = r₂ * s → ∃ s' : S, s' * r₁ = s' * r₂) ∧
      (∀ (r : R) (s : S), ∃ (r' : R) (s' : S), s' * r = r' * s) := by
  constructor
  · exact fun ⟨_⟩ ↦ ⟨ore_right_cancel, fun r s ↦ ⟨oreNum r s, oreDenom r s, ore_eq r s⟩⟩
  · intro ⟨H, H'⟩
    choose r' s' h using H'
    exact ⟨H, r', s', h⟩
/-
**OreLocalization.nonempty_oreSet_iff_of_noZeroDivisors** 是 Mathlib 中的一个引理，位于命名空
间 `OreLocalization`。
形式化陈述：nonempty_oreSet_iff_of_noZeroDivisors {R : Type*} [Ring R] [NoZeroDivisors
 R] {S : Submonoid R} : Nonempty (OreSet S) ↔ forall (r : R) (s : S), exists (r'
 : R) (s' : S), s' * r = r' * s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.ore_eq`：ore_eq (r : R) (s : S) : oreDenom r s * r = oreN
um r s * s
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma nonempty_oreSet_iff_of_noZeroDivisors {R : Type*} [Ring R] [NoZeroDivisors R]
    {S : Submonoid R} :
    Nonempty (OreSet S) ↔ ∀ (r : R) (s : S), ∃ (r' : R) (s' : S), s' * r = r' * s := by
  constructor
  · exact fun ⟨_⟩ ↦ fun r s ↦ ⟨oreNum r s, oreDenom r s, ore_eq r s⟩
  · intro H
    choose r' s' h using H
    exact ⟨oreSetOfNoZeroDivisors r' s' h⟩

end OreLocalization

