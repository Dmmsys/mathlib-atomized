/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Kevin Klinge
-/
module

public import Mathlib.Algebra.Group.Submonoid.Defs

/-!

# (Left) Ore sets

This defines left Ore sets on arbitrary monoids.

## References

* https://ncatlab.org/nlab/show/Ore+set

-/

@[expose] public section

assert_not_exists RelIso

namespace AddOreLocalization

/--
Definition of `AddOreSet` / `AddOreSet` 的定义

English:
class AddOreSet
  parameters: {R : Type*} [AddMonoid R] (S : AddSubmonoid R)
  axioms and operations (4):
    - ore_right_cancel : forall (r₁ r₂ : R) (s : S), r₁ + s = r₂ + s -> exists s' : S, s' + r₁ = s' + r₂
    - oreMin : R -> S -> R
    - oreSubtra : R -> S -> S
    - ore_eq : forall (r : R) (s : S), oreSubtra r s + r = oreMin r s + s

中文:
类 加法OreSet
  参数: {R : 类型} [加法幺半群 R] (S : 加法子幺半群 R)
  公理与运算 (4 个):
    - ore_right_cancel : 对任意 (r₁ r₂ : R) (s : S), r₁ + s = r₂ + s -> 存在 s' : S, s' + r₁ = s' + r₂
    - oreMin : R -> S -> R
    - oreSubtra : R -> S -> S
    - ore_eq : 对任意 (r : R) (s : S), oreSubtra r s + r = oreMin r s + s
-/
class AddOreSet {R : Type*} [AddMonoid R] (S : AddSubmonoid R) where
  /-- Common summands on the right can be turned into common summands on the left, a weak form of
cancellability. -/
  ore_right_cancel : forall (r₁ r₂ : R) (s : S), r₁ + s = r₂ + s -> exists s' : S, s' + r₁ = s' + r₂
  /-- The Ore minuend of a difference. -/
  oreMin : R -> S -> R
  /-- The Ore subtrahend of a difference. -/
  oreSubtra : R -> S -> S
  /-- The Ore condition of a difference, expressed in terms of `oreMin` and `oreSubtra`. -/
  ore_eq : forall (r : R) (s : S), oreSubtra r s + r = oreMin r s + s

end AddOreLocalization

namespace OreLocalization

section Monoid

/-- A submonoid `S` of a monoid `R` is (left) Ore if common factors on the right can be turned
into common factors on the left, and if each pair of `r : R` and `s : S` admits an Ore numerator
`v : R` and an Ore denominator `u : S` such that `u * r = v * s`. -/
@[to_additive AddOreLocalization.AddOreSet]
/--
Definition of `OreSet` / `OreSet` 的定义

English:
class OreSet
  parameters: {R : Type*} [Monoid R] (S : Submonoid R)
  axioms and operations (4):
    - ore_right_cancel : forall (r₁ r₂ : R) (s : S), r₁ * s = r₂ * s -> exists s' : S, s' * r₁ = s' * r₂
    - oreNum : R -> S -> R
    - oreDenom : R -> S -> S
    - ore_eq : forall (r : R) (s : S), oreDenom r s * r = oreNum r s * s

中文:
类 OreSet
  参数: {R : 类型} [幺半群 R] (S : 子幺半群 R)
  公理与运算 (4 个):
    - ore_right_cancel : 对任意 (r₁ r₂ : R) (s : S), r₁ * s = r₂ * s -> 存在 s' : S, s' * r₁ = s' * r₂
    - oreNum : R -> S -> R
    - oreDenom : R -> S -> S
    - ore_eq : 对任意 (r : R) (s : S), oreDenom r s * r = oreNum r s * s
-/
class OreSet {R : Type*} [Monoid R] (S : Submonoid R) where
  /-- Common factors on the right can be turned into common factors on the left, a weak form of
cancellability. -/
  ore_right_cancel : forall (r₁ r₂ : R) (s : S), r₁ * s = r₂ * s -> exists s' : S, s' * r₁ = s' * r₂
  /-- The Ore numerator of a fraction. -/
  oreNum : R -> S -> R
  /-- The Ore denominator of a fraction. -/
  oreDenom : R -> S -> S
  /-- The Ore condition of a fraction, expressed in terms of `oreNum` and `oreDenom`. -/
  ore_eq : forall (r : R) (s : S), oreDenom r s * r = oreNum r s * s

-- TODO: use this once it's available.
-- run_cmd to_additive.map_namespace `OreLocalization `AddOreLocalization

variable {R : Type*} [Monoid R] {S : Submonoid R} [OreSet S]

/-- Common factors on the right can be turned into common factors on the left, a weak form of
cancellability. -/
@[to_additive AddOreLocalization.ore_right_cancel]
/--
theorem `ore_right_cancel` / 定理 `ore_right_cancel`

English:
theorem ore_right_cancel
  given: (r₁ r₂ : R) (s : S) (h : r₁ * s = r₂ * s)
  statement: exists s' : S, s' * r₁ = s' * r₂
  proof: OreSet.ore_right_cancel r₁ r₂ s h

中文:
定理 ore_right_cancel
  条件: (r₁ r₂ : R) (s : S) (h : r₁ * s = r₂ * s)
  结论: 存在 s' : S, s' * r₁ = s' * r₂
  证明: OreSet.ore_right_cancel r₁ r₂ s h

Depends on / 依赖: OreSet, OreSet.ore_right_cancel, ore_right_cancel
-/
theorem ore_right_cancel (r₁ r₂ : R) (s : S) (h : r₁ * s = r₂ * s) : exists s' : S, s' * r₁ = s' * r₂ :=
  OreSet.ore_right_cancel r₁ r₂ s h

/-- The Ore numerator of a fraction. -/
@[to_additive AddOreLocalization.oreMin /-- The Ore minuend of a difference. -/]
/--
Definition of `oreNum` / `oreNum` 的定义

English:
definition oreNum
  signature: (r : R) (s : S)
  body: OreSet.oreNum r s

中文:
定义 oreNum
  签名: (r : R) (s : S)
  定义体: OreSet.oreNum r s

Depends on / 依赖: OreSet, OreSet.oreNum, oreNum
-/
def oreNum (r : R) (s : S) : R :=
  OreSet.oreNum r s

/-- The Ore denominator of a fraction. -/
@[to_additive AddOreLocalization.oreSubtra /-- The Ore subtrahend of a difference. -/]
/--
Definition of `oreDenom` / `oreDenom` 的定义

English:
definition oreDenom
  signature: (r : R) (s : S)
  body: OreSet.oreDenom r s

中文:
定义 oreDenom
  签名: (r : R) (s : S)
  定义体: OreSet.oreDenom r s

Depends on / 依赖: OreSet, OreSet.oreDenom, oreDenom
-/
def oreDenom (r : R) (s : S) : S :=
  OreSet.oreDenom r s

/-- The Ore condition of a fraction, expressed in terms of `oreNum` and `oreDenom`. -/
@[to_additive AddOreLocalization.add_ore_eq
  /-- The Ore condition of a difference, expressed in terms of `oreMin` and `oreSubtra`. -/]
/--
theorem `ore_eq` / 定理 `ore_eq`

English:
theorem ore_eq
  given: (r : R) (s : S)
  statement: oreDenom r s * r = oreNum r s * s
  proof: OreSet.ore_eq r s

中文:
定理 ore_eq
  条件: (r : R) (s : S)
  结论: oreDenom r s * r = oreNum r s * s
  证明: OreSet.ore_eq r s

Depends on / 依赖: OreSet, OreSet.ore_eq, ore_eq
-/
theorem ore_eq (r : R) (s : S) : oreDenom r s * r = oreNum r s * s :=
  OreSet.ore_eq r s

/-- The Ore condition bundled in a sigma type. This is useful in situations where we want to obtain
both witnesses and the condition for a given fraction. -/
@[to_additive AddOreLocalization.addOreCondition
/-- The Ore condition bundled in a sigma type. This is useful in situations where we want to obtain
both witnesses and the condition for a given difference. -/]
/--
Definition of `oreCondition` / `oreCondition` 的定义

English:
definition oreCondition
  signature: (r : R) (s : S)
  body: ⟨oreNum r s, oreDenom r s, ore_eq r s⟩

中文:
定义 oreCondition
  签名: (r : R) (s : S)
  定义体: ⟨oreNum r s, oreDenom r s, ore_eq r s⟩

Depends on / 依赖: oreDenom, oreNum, ore_eq
-/
def oreCondition (r : R) (s : S) : Σ' r' : R, Σ' s' : S, s' * r = r' * s :=
  ⟨oreNum r s, oreDenom r s, ore_eq r s⟩

/-- The trivial submonoid is an Ore set. -/
@[to_additive AddOreLocalization.addOreSetBot]
/--
Instance `oreSetBot` / 实例 `oreSetBot`

English:
instance oreSetBot
  signature: : OreSet (⊥ : Submonoid R) where
  body: ⟨s, by
      rcases s with ⟨s, hs⟩
      rw [Submonoid.mem_bot] at hs
      subst hs
      rw [mul_one]; rw [mul_one] at h
      subst h
      rfl⟩
  oreNum r _ := r
  oreDenom _ s := s
  ore_eq _ s := by
    rcases s with ⟨s, hs⟩
    rw [Submonoid.mem_bot] at hs
    simp [hs]

中文:
实例 oreSetBot
  签名: : OreSet (⊥ : 子幺半群 R) where
  定义体: ⟨s, by
      rcases s with ⟨s, hs⟩
      rw [Submonoid.mem_bot] at hs
      subst hs
      rw [mul_one]; rw [mul_one] at h
      subst h
      rfl⟩
  oreNum r _ := r
  oreDenom _ s := s
  ore_eq _ s := by
    rcases s with ⟨s, hs⟩
    rw [Submonoid.mem_bot] at hs
    simp [hs]

Depends on / 依赖: Submonoid, Submonoid.mem_bot, mem_bot, mul_one, oreDenom, oreNum, ore_eq
-/
instance oreSetBot : OreSet (⊥ : Submonoid R) where
  ore_right_cancel _ _ s h :=
    ⟨s, by
      rcases s with ⟨s, hs⟩
      rw [Submonoid.mem_bot] at hs
      subst hs
      rw [mul_one]; rw [mul_one] at h
      subst h
      rfl⟩
  oreNum r _ := r
  oreDenom _ s := s
  ore_eq _ s := by
    rcases s with ⟨s, hs⟩
    rw [Submonoid.mem_bot] at hs
    simp [hs]

/-- Every submonoid of a commutative monoid is an Ore set. -/
@[to_additive AddOreLocalization.addOreSetComm]
instance (priority := 100) oreSetComm {R} [CommMonoid R] (S : Submonoid R) : OreSet S where
  ore_right_cancel m n s h := ⟨s, by rw [mul_comm (s : R) n, mul_comm (s : R) m, h]⟩
  oreNum r _ := r
  oreDenom _ s := s
  ore_eq r s := by rw [mul_comm]

@[to_additive (attr := simp) AddOreLocalization.addOreSetComm_oreMin]
/--
lemma `oreSetComm_oreNum` / 引理 `oreSetComm_oreNum`

English:
lemma oreSetComm_oreNum
  given: {R : Type*} [CommMonoid R] (S : Submonoid R) (r : R) (s : S)
  proof: rfl

@[to_additive (attr := simp) AddOreLocalization.addOreSetComm_oreSubtra]

中文:
引理 oreSetComm_oreNum
  条件: {R : 类型} [交换幺半群 R] (S : 子幺半群 R) (r : R) (s : S)
  证明: rfl

@[to_additive (attr := simp) AddOreLocalization.addOreSetComm_oreSubtra]
-/
lemma oreSetComm_oreNum {R : Type*} [CommMonoid R] (S : Submonoid R) (r : R) (s : S) :
    oreNum r s = r := rfl

@[to_additive (attr := simp) AddOreLocalization.addOreSetComm_oreSubtra]
/--
lemma `oreSetComm_oreDenom` / 引理 `oreSetComm_oreDenom`

English:
lemma oreSetComm_oreDenom
  given: {R : Type*} [CommMonoid R] (S : Submonoid R) (r : R) (s : S)
  proof: rfl

中文:
引理 oreSetComm_oreDenom
  条件: {R : 类型} [交换幺半群 R] (S : 子幺半群 R) (r : R) (s : S)
  证明: rfl

Depends on / 依赖: CommSemiring, SymmetricAlgebra
-/
lemma oreSetComm_oreDenom {R : Type*} [CommMonoid R] (S : Submonoid R) (r : R) (s : S) :
    oreDenom r s = s := rfl

end Monoid

end OreLocalization
