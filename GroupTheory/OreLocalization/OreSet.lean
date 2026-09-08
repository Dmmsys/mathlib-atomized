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

/-- A submonoid `S` of an additive monoid `R` is (left) Ore if common summands on the right can be
turned into common summands on the left, and if each pair of `r : R` and `s : S` admits an Ore
minuend `v : R` and an Ore subtrahend `u : S` such that `u + r = v + s`. -/
/-
**AddOreLocalization.AddOreSet** 是 Mathlib 中的一个归纳类型，位于命名空间 `AddOreLocalization`。
形式化陈述：{R : Type u_1} → [inst : AddMonoid R] → AddSubmonoid R → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submonoid `S` of an additive monoid `R` is (left) Ore if common summands on th
e right can be
turned into common summands on the left, and if each pair of `r : R` and `s : S`
 admits an Ore
minuend `v : R` and an Ore subtrahend `u : S` such that `u + r = v + s`.
-/
class AddOreSet {R : Type*} [AddMonoid R] (S : AddSubmonoid R) where
  /-- Common summands on the right can be turned into common summands on the left, a weak form of
cancellability. -/
  ore_right_cancel : ∀ (r₁ r₂ : R) (s : S), r₁ + s = r₂ + s → ∃ s' : S, s' + r₁ = s' + r₂
  /-- The Ore minuend of a difference. -/
  oreMin : R → S → R
  /-- The Ore subtrahend of a difference. -/
  oreSubtra : R → S → S
  /-- The Ore condition of a difference, expressed in terms of `oreMin` and `oreSubtra`. -/
  ore_eq : ∀ (r : R) (s : S), oreSubtra r s + r = oreMin r s + s

end AddOreLocalization

namespace OreLocalization

section Monoid

/-- A submonoid `S` of a monoid `R` is (left) Ore if common factors on the right can be turned
into common factors on the left, and if each pair of `r : R` and `s : S` admits an Ore numerator
`v : R` and an Ore denominator `u : S` such that `u * r = v * s`. -/
@[to_additive AddOreLocalization.AddOreSet]
/-
**OreLocalization.OreSet** 是 Mathlib 中的一个归纳类型，位于命名空间 `OreLocalization`。
形式化陈述：{R : Type u_1} → [inst : Monoid R] → Submonoid R → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submonoid `S` of a monoid `R` is (left) Ore if common factors on the right can
 be turned
into common factors on the left, and if each pair of `r : R` and `s : S` admits 
an Ore numerator
`v : R` and an Ore denominator `u : S` such that `u * r = v * s`.
-/
class OreSet {R : Type*} [Monoid R] (S : Submonoid R) where
  /-- Common factors on the right can be turned into common factors on the left, a weak form of
cancellability. -/
  ore_right_cancel : ∀ (r₁ r₂ : R) (s : S), r₁ * s = r₂ * s → ∃ s' : S, s' * r₁ = s' * r₂
  /-- The Ore numerator of a fraction. -/
  oreNum : R → S → R
  /-- The Ore denominator of a fraction. -/
  oreDenom : R → S → S
  /-- The Ore condition of a fraction, expressed in terms of `oreNum` and `oreDenom`. -/
  ore_eq : ∀ (r : R) (s : S), oreDenom r s * r = oreNum r s * s

-- TODO: use this once it's available.
-- run_cmd to_additive.map_namespace `OreLocalization `AddOreLocalization

variable {R : Type*} [Monoid R] {S : Submonoid R} [OreSet S]

/-- Common factors on the right can be turned into common factors on the left, a weak form of
cancellability. -/
@[to_additive AddOreLocalization.ore_right_cancel]
/-
**OreLocalization.ore_right_cancel** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization`。
形式化陈述：ore_right_cancel (r₁ r₂ : R) (s : S) (h : r₁ * s = r₂ * s) : exists s' : S
, s' * r₁ = s' * r₂
参数：r₁ r₂ : R；s : S；h : r₁ * s = r₂ * s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.OreSet.ore_right_cancel`：∀ {R : Type u_1} {inst : Monoid
 R} {S : Submonoid R} [self : OreLocalization.OreSet S] (r₁ r₂ : R) (s : ↥S),   
r₁ * ↑s = r₂ * ↑s → ∃ s', ↑s'…

--- 原说明 ---
Common factors on the right can be turned into common factors on the left, a wea
k form of
cancellability.
-/
theorem ore_right_cancel (r₁ r₂ : R) (s : S) (h : r₁ * s = r₂ * s) : ∃ s' : S, s' * r₁ = s' * r₂ :=
  OreSet.ore_right_cancel r₁ r₂ s h

/-- The Ore numerator of a fraction. -/
@[to_additive AddOreLocalization.oreMin /-- The Ore minuend of a difference. -/]
/-
**OreLocalization.oreNum** 是 Mathlib 中的一个定义，位于命名空间 `OreLocalization`。
形式化陈述：oreNum (r : R) (s : S) : R
参数：r : R；s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Ore numerator of a fraction.
-/
def oreNum (r : R) (s : S) : R :=
  OreSet.oreNum r s

/-- The Ore denominator of a fraction. -/
@[to_additive AddOreLocalization.oreSubtra /-- The Ore subtrahend of a difference. -/]
/-
**OreLocalization.oreDenom** 是 Mathlib 中的一个定义，位于命名空间 `OreLocalization`。
形式化陈述：oreDenom (r : R) (s : S) : S
参数：r : R；s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Ore denominator of a fraction.
-/
def oreDenom (r : R) (s : S) : S :=
  OreSet.oreDenom r s

/-- The Ore condition of a fraction, expressed in terms of `oreNum` and `oreDenom`. -/
@[to_additive AddOreLocalization.add_ore_eq
  /-- The Ore condition of a difference, expressed in terms of `oreMin` and `oreSubtra`. -/]
/-
**OreLocalization.ore_eq** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization`。
形式化陈述：ore_eq (r : R) (s : S) : oreDenom r s * r = oreNum r s * s
参数：r : R；s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.OreSet.ore_eq`：∀ {R : Type u_1} {inst : Monoid R} {S : S
ubmonoid R} [self : OreLocalization.OreSet S] (r : R) (s : ↥S),   ↑(OreLocalizat
ion.OreSet.oreDenom…
-/
theorem ore_eq (r : R) (s : S) : oreDenom r s * r = oreNum r s * s :=
  OreSet.ore_eq r s

/-- The Ore condition bundled in a sigma type. This is useful in situations where we want to obtain
both witnesses and the condition for a given fraction. -/
@[to_additive AddOreLocalization.addOreCondition
/-- The Ore condition bundled in a sigma type. This is useful in situations where we want to obtain
both witnesses and the condition for a given difference. -/]
/-
**OreLocalization.oreCondition** 是 Mathlib 中的一个定义，位于命名空间 `OreLocalization`。
形式化陈述：oreCondition (r : R) (s : S) : Σ' r' : R, Σ' s' : S, s' * r = r' * s
参数：r : R；s : S。
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.ore_eq`：ore_eq (r : R) (s : S) : oreDenom r s * r = oreN
um r s * s
-/
def oreCondition (r : R) (s : S) : Σ' r' : R, Σ' s' : S, s' * r = r' * s :=
  ⟨oreNum r s, oreDenom r s, ore_eq r s⟩

/-- The trivial submonoid is an Ore set. -/
@[to_additive AddOreLocalization.addOreSetBot]
/-
**OreLocalization.oreSetBot** 是 Mathlib 中的一个实例，位于命名空间 `OreLocalization`。
形式化陈述：oreSetBot : OreSet (⊥ : Submonoid R) where ore_right_cancel _ _ s h
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial submonoid is an Ore set.
-/
instance oreSetBot : OreSet (⊥ : Submonoid R) where
  ore_right_cancel _ _ s h :=
    ⟨s, by
      rcases s with ⟨s, hs⟩
      rw [Submonoid.mem_bot] at hs
      subst hs
      rw [mul_one, mul_one] at h
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
/-
**OreLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `OreLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every submonoid of a commutative monoid is an Ore set.
-/
instance (priority := 100) oreSetComm {R} [CommMonoid R] (S : Submonoid R) : OreSet S where
  ore_right_cancel m n s h := ⟨s, by rw [mul_comm (s : R) n, mul_comm (s : R) m, h]⟩
  oreNum r _ := r
  oreDenom _ s := s
  ore_eq r s := by rw [mul_comm]

@[to_additive (attr := simp) AddOreLocalization.addOreSetComm_oreMin]
/-
**OreLocalization.oreSetComm_oreNum** 是 Mathlib 中的一个引理，位于命名空间 `OreLocalization`。
形式化陈述：oreSetComm_oreNum {R : Type*} [CommMonoid R] (S : Submonoid R) (r : R) (s 
: S) : oreNum r s = r
参数：S : Submonoid R；r : R；s : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma oreSetComm_oreNum {R : Type*} [CommMonoid R] (S : Submonoid R) (r : R) (s : S) :
    oreNum r s = r := rfl

@[to_additive (attr := simp) AddOreLocalization.addOreSetComm_oreSubtra]
/-
**OreLocalization.oreSetComm_oreDenom** 是 Mathlib 中的一个引理，位于命名空间 `OreLocalization
`。
形式化陈述：oreSetComm_oreDenom {R : Type*} [CommMonoid R] (S : Submonoid R) (r : R) (
s : S) : oreDenom r s = s
参数：S : Submonoid R；r : R；s : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma oreSetComm_oreDenom {R : Type*} [CommMonoid R] (S : Submonoid R) (r : R) (s : S) :
    oreDenom r s = s := rfl

end Monoid

end OreLocalization

