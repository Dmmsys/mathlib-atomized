/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.MulAction
public import Mathlib.Data.Set.BooleanAlgebra
public meta import Mathlib.Tactic.ToDual

/-!
# Definition of `orbit`, `fixedPoints` and `stabilizer`

This file defines orbits, stabilizers, and other objects defined in terms of actions.

## Main definitions

* `MulAction.orbit`
* `MulAction.fixedPoints`
* `MulAction.fixedBy`
* `MulAction.stabilizer`

-/

@[expose] public section

assert_not_exists MonoidWithZero DistribMulAction

universe u v

open scoped Pointwise

open Function

namespace MulAction

variable (M γ α : Type*) [SMul γ α] [Monoid M] [MulAction M α]

section Orbit

variable {α}

/-- The orbit of an element under an action. -/
@[to_additive /-- The orbit of an element under an action. -/]
/--
Definition of `orbit` / `orbit` 的定义

English:
definition orbit
  signature: (a : α)
  body: Set.range fun m : γ => m • a

中文:
定义 orbit
  签名: (a : α)
  定义体: Set.range fun m : γ => m • a

Depends on / 依赖: Set.range
-/
def orbit (a : α) :=
  Set.range fun m : γ => m • a

variable {γ}

@[to_additive]
/--
theorem `mem_orbit_iff` / 定理 `mem_orbit_iff`

English:
theorem mem_orbit_iff
  given: {a₁ a₂ : α}
  statement: a₂ in orbit γ a₁ ↔ exists x : γ, x • a₁ = a₂
  proof: Iff.rfl

@[to_additive (attr := simp)]

中文:
定理 mem_orbit_iff
  条件: {a₁ a₂ : α}
  结论: a₂ in orbit γ a₁ ↔ 存在 x : γ, x • a₁ = a₂
  证明: Iff.rfl

@[to_additive (attr := simp)]

Depends on / 依赖: Iff.rfl
-/
theorem mem_orbit_iff {a₁ a₂ : α} : a₂ in orbit γ a₁ ↔ exists x : γ, x • a₁ = a₂ :=
  Iff.rfl

@[to_additive (attr := simp)]
/--
theorem `mem_orbit` / 定理 `mem_orbit`

English:
theorem mem_orbit
  given: (a : α) (m : γ)
  statement: m • a in orbit γ a
  proof: ⟨m, rfl⟩

中文:
定理 mem_orbit
  条件: (a : α) (m : γ)
  结论: m • a in orbit γ a
  证明: ⟨m, rfl⟩
-/
theorem mem_orbit (a : α) (m : γ) : m • a in orbit γ a :=
  ⟨m, rfl⟩

variable {M}

@[to_additive]
/--
theorem `mem_orbit_of_mem_orbit` / 定理 `mem_orbit_of_mem_orbit`

English:
theorem mem_orbit_of_mem_orbit
  given: {a₁ a₂ : α} (m : M) (h : a₂ in orbit M a₁)
  proof: by
  obtain ⟨x, rfl⟩ := mem_orbit_iff.mp h
  simp [smul_smul]

@[to_additive (attr := simp)]

中文:
定理 mem_orbit_of_mem_orbit
  条件: {a₁ a₂ : α} (m : M) (h : a₂ in orbit M a₁)
  证明: by
  obtain ⟨x, rfl⟩ := mem_orbit_iff.mp h
  simp [smul_smul]

@[to_additive (attr := simp)]

Depends on / 依赖: mem_orbit_iff, mem_orbit_iff.mp, smul_smul
-/
theorem mem_orbit_of_mem_orbit {a₁ a₂ : α} (m : M) (h : a₂ in orbit M a₁) :
    m • a₂ in orbit M a₁ := by
  obtain ⟨x, rfl⟩ := mem_orbit_iff.mp h
  simp [smul_smul]

@[to_additive (attr := simp)]
/--
theorem `mem_orbit_self` / 定理 `mem_orbit_self`

English:
theorem mem_orbit_self
  given: (a : α)
  statement: a in orbit M a
  proof: ⟨1, by simp⟩

@[to_additive]

中文:
定理 mem_orbit_self
  条件: (a : α)
  结论: a in orbit M a
  证明: ⟨1, by simp⟩

@[to_additive]
-/
theorem mem_orbit_self (a : α) : a in orbit M a :=
  ⟨1, by simp⟩

@[to_additive]
/--
theorem `nonempty_orbit` / 定理 `nonempty_orbit`

English:
theorem nonempty_orbit
  given: (a : α)
  statement: Set.Nonempty (orbit M a)
  proof: Set.range_nonempty _

@[to_additive]

中文:
定理 nonempty_orbit
  条件: (a : α)
  结论: Set.Nonempty (orbit M a)
  证明: Set.range_nonempty _

@[to_additive]

Depends on / 依赖: Set.range_nonempty, range_nonempty
-/
theorem nonempty_orbit (a : α) : Set.Nonempty (orbit M a) :=
  Set.range_nonempty _

@[to_additive]
/--
theorem `mapsTo_smul_orbit` / 定理 `mapsTo_smul_orbit`

English:
theorem mapsTo_smul_orbit
  given: (m : M) (a : α)
  statement: Set.MapsTo (m • ·) (orbit M a) (orbit M a)
  proof: Set.mapsTo_iff_subset_preimage.mpr Set.range_subset_iff.mpr fun m' => ⟨m * m', mul_smul _ _ _⟩

@[to_additive]

中文:
定理 mapsTo_smul_orbit
  条件: (m : M) (a : α)
  结论: Set.MapsTo (m • ·) (orbit M a) (orbit M a)
  证明: Set.mapsTo_iff_subset_preimage.mpr Set.range_subset_iff.mpr fun m' => ⟨m * m', mul_smul _ _ _⟩

@[to_additive]

Depends on / 依赖: Set.mapsTo_iff_subset_preimage.mpr, Set.range_subset_iff.mpr, mapsTo_iff_subset_preimage, mul_smul, range_subset_iff
-/
theorem mapsTo_smul_orbit (m : M) (a : α) : Set.MapsTo (m • ·) (orbit M a) (orbit M a) :=
Set.mapsTo_iff_subset_preimage.mpr Set.range_subset_iff.mpr fun m' => ⟨m * m', mul_smul _ _ _⟩

@[to_additive]
/--
theorem `smul_orbit_subset` / 定理 `smul_orbit_subset`

English:
theorem smul_orbit_subset
  given: (m : M) (a : α)
  statement: m • orbit M a subseteq orbit M a
  proof: (mapsTo_smul_orbit m a).image_subset

@[to_additive]

中文:
定理 smul_orbit_subset
  条件: (m : M) (a : α)
  结论: m • orbit M a subseteq orbit M a
  证明: (mapsTo_smul_orbit m a).image_subset

@[to_additive]

Depends on / 依赖: image_subset, mapsTo_smul_orbit
-/
theorem smul_orbit_subset (m : M) (a : α) : m • orbit M a subseteq orbit M a :=
  (mapsTo_smul_orbit m a).image_subset

@[to_additive]
/--
theorem `orbit_smul_subset` / 定理 `orbit_smul_subset`

English:
theorem orbit_smul_subset
  given: (m : M) (a : α)
  statement: orbit M (m • a) subseteq orbit M a
  proof: Set.range_subset_iff.2 fun m' => mul_smul m' m a ▸ mem_orbit _ _

@[to_additive]

中文:
定理 orbit_smul_subset
  条件: (m : M) (a : α)
  结论: orbit M (m • a) subseteq orbit M a
  证明: Set.range_subset_iff.2 fun m' => mul_smul m' m a ▸ mem_orbit _ _

@[to_additive]

Depends on / 依赖: Set.range_subset_iff, mem_orbit, mul_smul, range_subset_iff
-/
theorem orbit_smul_subset (m : M) (a : α) : orbit M (m • a) subseteq orbit M a :=
  Set.range_subset_iff.2 fun m' => mul_smul m' m a ▸ mem_orbit _ _

@[to_additive]
instance {a : α} : MulAction M (orbit M a) where
  smul m := (mapsTo_smul_orbit m a).restrict _ _ _
  one_smul m := Subtype.ext (one_smul M (m : α))
  mul_smul m m' a' := Subtype.ext (mul_smul m m' (a' : α))

@[to_additive (attr := simp)]
/--
theorem `orbit.coe_smul` / 定理 `orbit.coe_smul`

English:
theorem orbit.coe_smul
  given: {a : α} {m : M} {a' : orbit M a}
  statement: ↑(m • a') = m • (a' : α)
  proof: rfl

@[to_additive]

中文:
定理 orbit.coe_smul
  条件: {a : α} {m : M} {a' : orbit M a}
  结论: ↑(m • a') = m • (a' : α)
  证明: rfl

@[to_additive]
-/
theorem orbit.coe_smul {a : α} {m : M} {a' : orbit M a} : ↑(m • a') = m • (a' : α) :=
  rfl

@[to_additive]
/--
lemma `orbit_submonoid_subset` / 引理 `orbit_submonoid_subset`

English:
lemma orbit_submonoid_subset
  given: (S : Submonoid M) (a : α)
  statement: orbit S a subseteq orbit M a
  proof: by
  rintro b ⟨g, rfl⟩
  exact mem_orbit _ _

@[to_additive]

中文:
引理 orbit_submonoid_subset
  条件: (S : Submonoid M) (a : α)
  结论: orbit S a subseteq orbit M a
  证明: by
  rintro b ⟨g, rfl⟩
  exact mem_orbit _ _

@[to_additive]

Depends on / 依赖: mem_orbit
-/
lemma orbit_submonoid_subset (S : Submonoid M) (a : α) : orbit S a subseteq orbit M a := by
  rintro b ⟨g, rfl⟩
  exact mem_orbit _ _

@[to_additive]
/--
lemma `mem_orbit_of_mem_orbit_submonoid` / 引理 `mem_orbit_of_mem_orbit_submonoid`

English:
lemma mem_orbit_of_mem_orbit_submonoid
  given: {S : Submonoid M} {a b : α} (h : a in orbit S b)
  proof: orbit_submonoid_subset S _ h

中文:
引理 mem_orbit_of_mem_orbit_submonoid
  条件: {S : Submonoid M} {a b : α} (h : a in orbit S b)
  证明: orbit_submonoid_subset S _ h

Depends on / 依赖: orbit_submonoid_subset
-/
lemma mem_orbit_of_mem_orbit_submonoid {S : Submonoid M} {a b : α} (h : a in orbit S b) :
    a in orbit M b :=
  orbit_submonoid_subset S _ h

end Orbit

section FixedPoints

/-- The set of elements fixed under the whole action. -/
@[to_additive /-- The set of elements fixed under the whole action. -/]
/--
Definition of `fixedPoints` / `fixedPoints` 的定义

English:
definition fixedPoints
  signature: : Set α
  body: { a : α | forall m : M, m • a = a }

中文:
定义 fixedPoints
  签名: : Set α
  定义体: { a : α | forall m : M, m • a = a }
-/
def fixedPoints : Set α :=
  { a : α | forall m : M, m • a = a }

variable {M} in
/-- `fixedBy m` is the set of elements fixed by `m`. -/
@[to_additive /-- `fixedBy m` is the set of elements fixed by `m`. -/]
/--
Definition of `fixedBy` / `fixedBy` 的定义

English:
definition fixedBy
  signature: (m : M)
  body: { x | m • x = x }

@[to_additive]

中文:
定义 fixedBy
  签名: (m : M)
  定义体: { x | m • x = x }

@[to_additive]
-/
def fixedBy (m : M) : Set α :=
  { x | m • x = x }

@[to_additive]
/--
theorem `fixed_eq_iInter_fixedBy` / 定理 `fixed_eq_iInter_fixedBy`

English:
theorem fixed_eq_iInter_fixedBy
  statement: fixedPoints M α = ⋂ m : M, fixedBy α m
  proof: Set.ext fun _ =>
    ⟨fun hx => Set.mem_iInter.2 fun m => hx m, fun hx m => (Set.mem_iInter.1 hx m :)⟩

中文:
定理 fixed_eq_iInter_fixedBy
  结论: fixedPoints M α = ⋂ m : M, fixedBy α m
  证明: Set.ext fun _ =>
    ⟨fun hx => Set.mem_iInter.2 fun m => hx m, fun hx m => (Set.mem_iInter.1 hx m :)⟩

Depends on / 依赖: Set.ext, Set.mem_iInter, mem_iInter
-/
theorem fixed_eq_iInter_fixedBy : fixedPoints M α = ⋂ m : M, fixedBy α m :=
  Set.ext fun _ =>
    ⟨fun hx => Set.mem_iInter.2 fun m => hx m, fun hx m => (Set.mem_iInter.1 hx m :)⟩

variable {M α}

@[to_additive (attr := simp)]
/--
theorem `mem_fixedPoints` / 定理 `mem_fixedPoints`

English:
theorem mem_fixedPoints
  given: {a : α}
  statement: a in fixedPoints M α ↔ forall m : M, m • a = a
  proof: Iff.rfl

@[to_additive (attr := simp, grind =)]

中文:
定理 mem_fixedPoints
  条件: {a : α}
  结论: a in fixedPoints M α ↔ 对任意 m : M, m • a = a
  证明: Iff.rfl

@[to_additive (attr := simp, grind =)]

Depends on / 依赖: Iff.rfl
-/
theorem mem_fixedPoints {a : α} : a in fixedPoints M α ↔ forall m : M, m • a = a :=
  Iff.rfl

@[to_additive (attr := simp, grind =)]
/--
theorem `mem_fixedBy` / 定理 `mem_fixedBy`

English:
theorem mem_fixedBy
  given: {m : M} {a : α}
  statement: a in fixedBy α m ↔ m • a = a
  proof: Iff.rfl

@[to_additive]

中文:
定理 mem_fixedBy
  条件: {m : M} {a : α}
  结论: a in fixedBy α m ↔ m • a = a
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem mem_fixedBy {m : M} {a : α} : a in fixedBy α m ↔ m • a = a :=
  Iff.rfl

@[to_additive]
/--
theorem `mem_fixedPoints'` / 定理 `mem_fixedPoints'`

English:
theorem mem_fixedPoints'
  given: {a : α}
  statement: a in fixedPoints M α ↔ forall a', a' in orbit M a -> a' = a
  proof: ⟨fun h _ h₁ =>
    let ⟨m, hm⟩ := mem_orbit_iff.1 h₁
    hm ▸ h m,
    fun h _ => h _ (mem_orbit _ _)⟩

中文:
定理 mem_fixedPoints'
  条件: {a : α}
  结论: a in fixedPoints M α ↔ 对任意 a', a' in orbit M a -> a' = a
  证明: ⟨fun h _ h₁ =>
    let ⟨m, hm⟩ := mem_orbit_iff.1 h₁
    hm ▸ h m,
    fun h _ => h _ (mem_orbit _ _)⟩

Depends on / 依赖: mem_orbit, mem_orbit_iff
-/
theorem mem_fixedPoints' {a : α} : a in fixedPoints M α ↔ forall a', a' in orbit M a -> a' = a :=
  ⟨fun h _ h₁ =>
    let ⟨m, hm⟩ := mem_orbit_iff.1 h₁
    hm ▸ h m,
    fun h _ => h _ (mem_orbit _ _)⟩

end FixedPoints

section Stabilizers

variable {α}

/-- The stabilizer of a point `a` as a submonoid of `M`. -/
@[to_additive /-- The stabilizer of a point `a` as an additive submonoid of `M`. -/]
/--
Definition of `stabilizerSubmonoid` / `stabilizerSubmonoid` 的定义

English:
definition stabilizerSubmonoid
  signature: (a : α)
  body: { m | m • a = a }
  one_mem' := one_smul _ a
  mul_mem' {m m'} (ha : m • a = a) (hb : m' • a = a) :=
    show (m * m') • a = a by rw [← smul_smul, hb, ha]

中文:
定义 stabilizerSubmonoid
  签名: (a : α)
  定义体: { m | m • a = a }
  one_mem' := one_smul _ a
  mul_mem' {m m'} (ha : m • a = a) (hb : m' • a = a) :=
    show (m * m') • a = a by rw [← smul_smul, hb, ha]
-/
def stabilizerSubmonoid (a : α) : Submonoid M where
  carrier := { m | m • a = a }
  one_mem' := one_smul _ a
  mul_mem' {m m'} (ha : m • a = a) (hb : m' • a = a) :=
    show (m * m') • a = a by rw [← smul_smul, hb, ha]

variable {M}

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] (a
  body: fun _ => inferInstanceAs Decidable (_ = _)

@[to_additive (attr := simp)]

中文:
实例 [DecidableEq
  签名: α] (a
  定义体: fun _ => inferInstanceAs Decidable (_ = _)

@[to_additive (attr := simp)]

Depends on / 依赖: Decidable
-/
instance [DecidableEq α] (a : α) : DecidablePred (· in stabilizerSubmonoid M a) :=
fun _ => inferInstanceAs Decidable (_ = _)

@[to_additive (attr := simp)]
/--
theorem `mem_stabilizerSubmonoid_iff` / 定理 `mem_stabilizerSubmonoid_iff`

English:
theorem mem_stabilizerSubmonoid_iff
  given: {a : α} {m : M}
  statement: m in stabilizerSubmonoid M a ↔ m • a = a
  proof: Iff.rfl

中文:
定理 mem_stabilizerSubmonoid_iff
  条件: {a : α} {m : M}
  结论: m in stabilizerSubmonoid M a ↔ m • a = a
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_stabilizerSubmonoid_iff {a : α} {m : M} : m in stabilizerSubmonoid M a ↔ m • a = a :=
  Iff.rfl

end Stabilizers

end MulAction

section FixedPoints

variable (M : Type u) (α : Type v) [Monoid M]

section Monoid

variable [Monoid α] [MulDistribMulAction M α]

/--
Definition of `FixedPoints.submonoid` / `FixedPoints.submonoid` 的定义

English:
definition FixedPoints.submonoid
  signature: : Submonoid α where
  body: MulAction.fixedPoints M α
  one_mem' := smul_one
  mul_mem' ha hb _ := by rw [smul_mul', ha, hb]

@[simp]

中文:
定义 FixedPoints.submonoid
  签名: : Submonoid α where
  定义体: MulAction.fixedPoints M α
  one_mem' := smul_one
  mul_mem' ha hb _ := by rw [smul_mul', ha, hb]

@[simp]

Depends on / 依赖: MulAction, MulAction.fixedPoints, fixedPoints
-/
def FixedPoints.submonoid : Submonoid α where
  carrier := MulAction.fixedPoints M α
  one_mem' := smul_one
  mul_mem' ha hb _ := by rw [smul_mul', ha, hb]

@[simp]
/--
lemma `FixedPoints.mem_submonoid` / 引理 `FixedPoints.mem_submonoid`

English:
lemma FixedPoints.mem_submonoid
  given: (a : α)
  statement: a in submonoid M α ↔ forall m : M, m • a = a
  proof: Iff.rfl

中文:
引理 FixedPoints.mem_submonoid
  条件: (a : α)
  结论: a in submonoid M α ↔ 对任意 m : M, m • a = a
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma FixedPoints.mem_submonoid (a : α) : a in submonoid M α ↔ forall m : M, m • a = a :=
  Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulCommClass M (FixedPoints.submonoid M α) α
  body: by simp_rw [Submonoid.smul_def, smul_eq_mul, smul_mul', x.2 g]

中文:
实例 :
  签名: SMulCommClass M (FixedPoints.submonoid M α) α
  定义体: by simp_rw [Submonoid.smul_def, smul_eq_mul, smul_mul', x.2 g]
-/
instance : SMulCommClass M (FixedPoints.submonoid M α) α where
  smul_comm g x y := by simp_rw [Submonoid.smul_def, smul_eq_mul, smul_mul', x.2 g]

end Monoid

section Group
namespace FixedPoints
variable [Group α] [MulDistribMulAction M α]

/--
Definition of `subgroup` / `subgroup` 的定义

English:
definition subgroup
  signature: : Subgroup α where
  body: submonoid M α
  inv_mem' ha _ := by rw [smul_inv', ha]

@[simp]

中文:
定义 subgroup
  签名: : Subgroup α where
  定义体: submonoid M α
  inv_mem' ha _ := by rw [smul_inv', ha]

@[simp]

Depends on / 依赖: ofFinsuppEquiv, submonoid
-/
def subgroup : Subgroup α where
  __ := submonoid M α
  inv_mem' ha _ := by rw [smul_inv', ha]

@[simp]
/--
lemma `mem_subgroup` / 引理 `mem_subgroup`

English:
lemma mem_subgroup
  given: (a : α)
  statement: a in FixedPoints.subgroup M α ↔ forall m : M, m • a = a
  proof: Iff.rfl

中文:
引理 mem_subgroup
  条件: (a : α)
  结论: a in FixedPoints.subgroup M α ↔ 对任意 m : M, m • a = a
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl, ofFinsuppEquiv
-/
lemma mem_subgroup (a : α) : a in FixedPoints.subgroup M α ↔ forall m : M, m • a = a :=
  Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulCommClass M (FixedPoints.subgroup M α) α
  body: inferInstanceAs (SMulCommClass M (FixedPoints.submonoid M α) α)

@[simp]

中文:
实例 :
  签名: SMulCommClass M (FixedPoints.subgroup M α) α
  定义体: inferInstanceAs (SMulCommClass M (FixedPoints.submonoid M α) α)

@[simp]

Depends on / 依赖: FixedPoints, FixedPoints.submonoid, SMulCommClass, submonoid
-/
instance : SMulCommClass M (FixedPoints.subgroup M α) α :=
  inferInstanceAs (SMulCommClass M (FixedPoints.submonoid M α) α)

@[simp]
/--
lemma `subgroup_toSubmonoid` / 引理 `subgroup_toSubmonoid`

English:
lemma subgroup_toSubmonoid
  statement: (FixedPoints.subgroup M α).toSubmonoid = submonoid M α
  proof: rfl

中文:
引理 subgroup_toSubmonoid
  结论: (FixedPoints.subgroup M α).toSubmonoid = submonoid M α
  证明: rfl
-/
lemma subgroup_toSubmonoid : (FixedPoints.subgroup M α).toSubmonoid = submonoid M α :=
  rfl

end FixedPoints
end Group
end FixedPoints

namespace MulAction
variable {G α β : Type*} [Group G] [MulAction G α] [MulAction G β]

section Orbit

@[to_additive (attr := simp)]
/--
theorem `orbit_smul` / 定理 `orbit_smul`

English:
theorem orbit_smul
  given: (g : G) (a : α)
  statement: orbit G (g • a) = orbit G a
  proof: (orbit_smul_subset g a).antisymm
    calc
      orbit G a = orbit G (g⁻¹ • g • a) := by rw [inv_smul_smul]
      _ subseteq orbit G (g • a) := orbit_smul_subset _ _

@[to_additive]

中文:
定理 orbit_smul
  条件: (g : G) (a : α)
  结论: orbit G (g • a) = orbit G a
  证明: (orbit_smul_subset g a).antisymm
    calc
      orbit G a = orbit G (g⁻¹ • g • a) := by rw [inv_smul_smul]
      _ subseteq orbit G (g • a) := orbit_smul_subset _ _

@[to_additive]

Depends on / 依赖: antisymm, inv_smul_smul, orbit_smul_subset, subseteq
-/
theorem orbit_smul (g : G) (a : α) : orbit G (g • a) = orbit G a :=
(orbit_smul_subset g a).antisymm
    calc
      orbit G a = orbit G (g⁻¹ • g • a) := by rw [inv_smul_smul]
      _ subseteq orbit G (g • a) := orbit_smul_subset _ _

@[to_additive]
/--
theorem `orbit_eq_iff` / 定理 `orbit_eq_iff`

English:
theorem orbit_eq_iff
  given: {a b : α}
  statement: orbit G a = orbit G b ↔ a in orbit G b
  proof: ⟨fun h => h ▸ mem_orbit_self _, fun ⟨_, hc⟩ => hc ▸ orbit_smul _ _⟩

@[to_additive]

中文:
定理 orbit_eq_iff
  条件: {a b : α}
  结论: orbit G a = orbit G b ↔ a in orbit G b
  证明: ⟨fun h => h ▸ mem_orbit_self _, fun ⟨_, hc⟩ => hc ▸ orbit_smul _ _⟩

@[to_additive]

Depends on / 依赖: mem_orbit_self, orbit_smul
-/
theorem orbit_eq_iff {a b : α} : orbit G a = orbit G b ↔ a in orbit G b :=
  ⟨fun h => h ▸ mem_orbit_self _, fun ⟨_, hc⟩ => hc ▸ orbit_smul _ _⟩

@[to_additive]
/--
theorem `mem_orbit_smul` / 定理 `mem_orbit_smul`

English:
theorem mem_orbit_smul
  given: (g : G) (a : α)
  statement: a in orbit G (g • a)
  proof: by
  simp only [orbit_smul, mem_orbit_self]

@[to_additive]

中文:
定理 mem_orbit_smul
  条件: (g : G) (a : α)
  结论: a in orbit G (g • a)
  证明: by
  simp only [orbit_smul, mem_orbit_self]

@[to_additive]

Depends on / 依赖: mem_orbit_self, orbit_smul
-/
theorem mem_orbit_smul (g : G) (a : α) : a in orbit G (g • a) := by
  simp only [orbit_smul, mem_orbit_self]

@[to_additive]
/--
theorem `smul_mem_orbit_smul` / 定理 `smul_mem_orbit_smul`

English:
theorem smul_mem_orbit_smul
  given: (g h : G) (a : α)
  statement: g • a in orbit G (h • a)
  proof: by
  simp only [orbit_smul, mem_orbit]

@[to_additive]

中文:
定理 smul_mem_orbit_smul
  条件: (g h : G) (a : α)
  结论: g • a in orbit G (h • a)
  证明: by
  simp only [orbit_smul, mem_orbit]

@[to_additive]

Depends on / 依赖: mem_orbit, orbit_smul
-/
theorem smul_mem_orbit_smul (g h : G) (a : α) : g • a in orbit G (h • a) := by
  simp only [orbit_smul, mem_orbit]

@[to_additive]
/--
Instance `instMulAction` / 实例 `instMulAction`

English:
instance instMulAction
  signature: (H : Subgroup G)
  body: inferInstanceAs (MulAction H.toSubmonoid α)

@[to_additive]

中文:
实例 instMulAction
  签名: (H : Subgroup G)
  定义体: inferInstanceAs (MulAction H.toSubmonoid α)

@[to_additive]

Depends on / 依赖: H.toSubmonoid, MulAction, toSubmonoid
-/
instance instMulAction (H : Subgroup G) : MulAction H α :=
  inferInstanceAs (MulAction H.toSubmonoid α)

@[to_additive]
/--
lemma `subgroup_smul_def` / 引理 `subgroup_smul_def`

English:
lemma subgroup_smul_def
  given: {H : Subgroup G} (a : H) (b : α)
  statement: a • b = (a : G) • b
  proof: rfl

@[to_additive]

中文:
引理 subgroup_smul_def
  条件: {H : Subgroup G} (a : H) (b : α)
  结论: a • b = (a : G) • b
  证明: rfl

@[to_additive]
-/
lemma subgroup_smul_def {H : Subgroup G} (a : H) (b : α) : a • b = (a : G) • b := rfl

@[to_additive]
/--
lemma `orbit_subgroup_subset` / 引理 `orbit_subgroup_subset`

English:
lemma orbit_subgroup_subset
  given: (H : Subgroup G) (a : α)
  statement: orbit H a subseteq orbit G a
  proof: orbit_submonoid_subset H.toSubmonoid a

@[to_additive]

中文:
引理 orbit_subgroup_subset
  条件: (H : Subgroup G) (a : α)
  结论: orbit H a subseteq orbit G a
  证明: orbit_submonoid_subset H.toSubmonoid a

@[to_additive]

Depends on / 依赖: H.toSubmonoid, orbit_submonoid_subset, toSubmonoid
-/
lemma orbit_subgroup_subset (H : Subgroup G) (a : α) : orbit H a subseteq orbit G a :=
  orbit_submonoid_subset H.toSubmonoid a

@[to_additive]
/--
lemma `mem_orbit_of_mem_orbit_subgroup` / 引理 `mem_orbit_of_mem_orbit_subgroup`

English:
lemma mem_orbit_of_mem_orbit_subgroup
  given: {H : Subgroup G} {a b : α} (h : a in orbit H b)
  proof: orbit_subgroup_subset H _ h

@[to_additive]

中文:
引理 mem_orbit_of_mem_orbit_subgroup
  条件: {H : Subgroup G} {a b : α} (h : a in orbit H b)
  证明: orbit_subgroup_subset H _ h

@[to_additive]

Depends on / 依赖: orbit_subgroup_subset
-/
lemma mem_orbit_of_mem_orbit_subgroup {H : Subgroup G} {a b : α} (h : a in orbit H b) :
    a in orbit G b :=
  orbit_subgroup_subset H _ h

@[to_additive]
/--
lemma `mem_orbit_symm` / 引理 `mem_orbit_symm`

English:
lemma mem_orbit_symm
  given: {a₁ a₂ : α}
  statement: a₁ in orbit G a₂ ↔ a₂ in orbit G a₁
  proof: by
  simp_rw [← orbit_eq_iff, eq_comm]

@[to_additive]

中文:
引理 mem_orbit_symm
  条件: {a₁ a₂ : α}
  结论: a₁ in orbit G a₂ ↔ a₂ in orbit G a₁
  证明: by
  simp_rw [← orbit_eq_iff, eq_comm]

@[to_additive]

Depends on / 依赖: eq_comm, orbit_eq_iff, simp_rw
-/
lemma mem_orbit_symm {a₁ a₂ : α} : a₁ in orbit G a₂ ↔ a₂ in orbit G a₁ := by
  simp_rw [← orbit_eq_iff, eq_comm]

@[to_additive]
/--
lemma `mem_subgroup_orbit_iff` / 引理 `mem_subgroup_orbit_iff`

English:
lemma mem_subgroup_orbit_iff
  given: {H : Subgroup G} {x : α} {a b : orbit G x}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨g, rfl⟩
    exact MulAction.mem_orbit _ g
  · rcases h with ⟨g, h⟩
    dsimp at h
    rw [subgroup_smul_def]; rw [← orbit.coe_smul]; rw [← Subtype.ext_iff] at h
    subst h
    exact MulAction.mem_orbit _ g

中文:
引理 mem_subgroup_orbit_iff
  条件: {H : Subgroup G} {x : α} {a b : orbit G x}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨g, rfl⟩
    exact MulAction.mem_orbit _ g
  · rcases h with ⟨g, h⟩
    dsimp at h
    rw [subgroup_smul_def]; rw [← orbit.coe_smul]; rw [← Subtype.ext_iff] at h
    subst h
    exact MulAction.mem_orbit _ g

Depends on / 依赖: MulAction, MulAction.mem_orbit, Subtype, Subtype.ext_iff, coe_smul, ext_iff, mem_orbit, orbit.coe_smul, subgroup_smul_def
-/
lemma mem_subgroup_orbit_iff {H : Subgroup G} {x : α} {a b : orbit G x} :
    a in MulAction.orbit H b ↔ (a : α) in MulAction.orbit H (b : α) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨g, rfl⟩
    exact MulAction.mem_orbit _ g
  · rcases h with ⟨g, h⟩
    dsimp at h
    rw [subgroup_smul_def]; rw [← orbit.coe_smul]; rw [← Subtype.ext_iff] at h
    subst h
    exact MulAction.mem_orbit _ g

variable (G α)

/-- The relation 'in the same orbit'. -/
@[to_additive /-- The relation 'in the same orbit'. -/]
/--
Definition of `orbitRel` / `orbitRel` 的定义

English:
definition orbitRel
  signature: : Setoid α where
  body: a in orbit G b
  iseqv := ⟨mem_orbit_self, mem_orbit_symm.mp, by grind [orbit_eq_iff]⟩

中文:
定义 orbitRel
  签名: : Setoid α where
  定义体: a in orbit G b
  iseqv := ⟨mem_orbit_self, mem_orbit_symm.mp, by grind [orbit_eq_iff]⟩
-/
def orbitRel : Setoid α where
  r a b := a in orbit G b
  iseqv := ⟨mem_orbit_self, mem_orbit_symm.mp, by grind [orbit_eq_iff]⟩

variable {G α}

@[to_additive]
/--
theorem `orbitRel_apply` / 定理 `orbitRel_apply`

English:
theorem orbitRel_apply
  given: {a b : α}
  statement: orbitRel G α a b ↔ a in orbit G b
  proof: Iff.rfl

中文:
定理 orbitRel_apply
  条件: {a b : α}
  结论: orbitRel G α a b ↔ a in orbit G b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem orbitRel_apply {a b : α} : orbitRel G α a b ↔ a in orbit G b :=
  Iff.rfl

/-- When you take a set `U` in `α`, push it down to the quotient, and pull back, you get the union
of the orbit of `U` under `G`. -/
@[to_additive
/-- When you take a set `U` in `α`, push it down to the quotient, and pull back, you get the union
of the orbit of `U` under `G`. -/]
/--
theorem `quotient_preimage_image_eq_union_mul` / 定理 `quotient_preimage_image_eq_union_mul`

English:
theorem quotient_preimage_image_eq_union_mul
  given: (U : Set α)
  proof: orbitRel G α
    Quotient.mk' ⁻¹' Quotient.mk' '' U = ⋃ g : G, (g • ·) '' U := by
  let := orbitRel G α
  set f : α -> Quotient (MulAction.orbitRel G α) := Quotient.mk'
  ext a
  constructor
  · rintro ⟨b, hb, hab⟩
    obtain ⟨g, rfl⟩ := Quotient.exact hab
    rw [Set.mem_iUnion]
    exact ⟨g⁻¹, g •

中文:
定理 quotient_preimage_image_eq_union_mul
  条件: (U : Set α)
  证明: orbitRel G α
    Quotient.mk' ⁻¹' Quotient.mk' '' U = ⋃ g : G, (g • ·) '' U := by
  let := orbitRel G α
  set f : α -> Quotient (MulAction.orbitRel G α) := Quotient.mk'
  ext a
  constructor
  · rintro ⟨b, hb, hab⟩
    obtain ⟨g, rfl⟩ := Quotient.exact hab
    rw [Set.mem_iUnion]
    exact ⟨g⁻¹, g •

Depends on / 依赖: orbitRel
-/
theorem quotient_preimage_image_eq_union_mul (U : Set α) :
    letI := orbitRel G α
    Quotient.mk' ⁻¹' Quotient.mk' '' U = ⋃ g : G, (g • ·) '' U := by
  let := orbitRel G α
  set f : α -> Quotient (MulAction.orbitRel G α) := Quotient.mk'
  ext a
  constructor
  · rintro ⟨b, hb, hab⟩
    obtain ⟨g, rfl⟩ := Quotient.exact hab
    rw [Set.mem_iUnion]
    exact ⟨g⁻¹, g • a, hb, inv_smul_smul g a⟩
  · intro hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨g, u, hu₁, hu₂⟩ := hx
    rw [Set.mem_preimage]; rw [Set.mem_image]
    refine ⟨g⁻¹ • a, ?_, by simp +instances [f, orbitRel, Quotient.eq']⟩
    rw [← hu₂]
    convert! hu₁
    simp only [inv_smul_smul]

@[to_additive]
/--
theorem `disjoint_image_image_iff` / 定理 `disjoint_image_image_iff`

English:
theorem disjoint_image_image_iff
  given: {U V : Set α}
  proof: orbitRel G α
    Disjoint (Quotient.mk' '' U) (Quotient.mk' '' V) ↔ forall x in U, forall g : G, g • x ∉ V := by
  let := orbitRel G α
  set f : α -> Quotient (MulAction.orbitRel G α) := Quotient.mk'
  refine
    ⟨fun h a a_in_U g g_in_V =>
      h.le_bot ⟨⟨a, a_in_U, Quotient.sound ⟨g⁻¹, ?_⟩⟩, ⟨g •

中文:
定理 disjoint_image_image_iff
  条件: {U V : Set α}
  证明: orbitRel G α
    Disjoint (Quotient.mk' '' U) (Quotient.mk' '' V) ↔ forall x in U, forall g : G, g • x ∉ V := by
  let := orbitRel G α
  set f : α -> Quotient (MulAction.orbitRel G α) := Quotient.mk'
  refine
    ⟨fun h a a_in_U g g_in_V =>
      h.le_bot ⟨⟨a, a_in_U, Quotient.sound ⟨g⁻¹, ?_⟩⟩, ⟨g •

Depends on / 依赖: orbitRel
-/
theorem disjoint_image_image_iff {U V : Set α} :
    letI := orbitRel G α
    Disjoint (Quotient.mk' '' U) (Quotient.mk' '' V) ↔ forall x in U, forall g : G, g • x ∉ V := by
  let := orbitRel G α
  set f : α -> Quotient (MulAction.orbitRel G α) := Quotient.mk'
  refine
    ⟨fun h a a_in_U g g_in_V =>
      h.le_bot ⟨⟨a, a_in_U, Quotient.sound ⟨g⁻¹, ?_⟩⟩, ⟨g • a, g_in_V, rfl⟩⟩, ?_⟩
  · simp
  · intro h
    rw [Set.disjoint_left]
    rintro _ ⟨b, hb₁, hb₂⟩ ⟨c, hc₁, hc₂⟩
    obtain ⟨g, rfl⟩ := Quotient.exact (hc₂.trans hb₂.symm)
    exact h b hb₁ g hc₁

@[to_additive]
/--
theorem `image_inter_image_iff` / 定理 `image_inter_image_iff`

English:
theorem image_inter_image_iff
  given: (U V : Set α)
  proof: orbitRel G α
    Quotient.mk' '' U inter Quotient.mk' '' V = ∅ ↔ forall x in U, forall g : G, g • x ∉ V :=
  Set.disjoint_iff_inter_eq_empty.symm.trans disjoint_image_image_iff

中文:
定理 image_inter_image_iff
  条件: (U V : Set α)
  证明: orbitRel G α
    Quotient.mk' '' U inter Quotient.mk' '' V = ∅ ↔ forall x in U, forall g : G, g • x ∉ V :=
  Set.disjoint_iff_inter_eq_empty.symm.trans disjoint_image_image_iff

Depends on / 依赖: orbitRel
-/
theorem image_inter_image_iff (U V : Set α) :
    letI := orbitRel G α
    Quotient.mk' '' U inter Quotient.mk' '' V = ∅ ↔ forall x in U, forall g : G, g • x ∉ V :=
  Set.disjoint_iff_inter_eq_empty.symm.trans disjoint_image_image_iff

variable (G α)

/-- The quotient by `MulAction.orbitRel`, given a name to enable dot notation. -/
@[to_additive
    /-- The quotient by `AddAction.orbitRel`, given a name to enable dot notation. -/]
/--
Definition of `orbitRel.Quotient` / `orbitRel.Quotient` 的定义

English:
abbreviation orbitRel.Quotient
  signature: : Type _
  body: _root_.Quotient orbitRel G α

中文:
缩写 orbitRel.Quotient
  签名: : Type _
  定义体: _root_.Quotient orbitRel G α

Depends on / 依赖: Quotient, _root_, _root_.Quotient, orbitRel
-/
abbrev orbitRel.Quotient : Type _ :=
_root_.Quotient orbitRel G α

variable {G α}

@[to_additive (attr := simp)]
/--
lemma `orbitRel.Quotient.quotient_smul_eq` / 引理 `orbitRel.Quotient.quotient_smul_eq`

English:
lemma orbitRel.Quotient.quotient_smul_eq
  given: {g : G} {a : α}
  proof: Quotient.eq.mpr ⟨g, rfl⟩

中文:
引理 orbitRel.Quotient.quotient_smul_eq
  条件: {g : G} {a : α}
  证明: Quotient.eq.mpr ⟨g, rfl⟩

Depends on / 依赖: Quotient, Quotient.eq.mpr
-/
lemma orbitRel.Quotient.quotient_smul_eq {g : G} {a : α} :
    ⟦g • a⟧ = (⟦a⟧ : orbitRel.Quotient G α) := Quotient.eq.mpr ⟨g, rfl⟩

/-- The orbit corresponding to an element of the quotient by `MulAction.orbitRel` -/
@[to_additive /-- The orbit corresponding to an element of the quotient by `AddAction.orbitRel` -/]
nonrec def orbitRel.Quotient.orbit (x : orbitRel.Quotient G α) : Set α :=
  Quotient.liftOn' x (orbit G) fun _ _ => MulAction.orbit_eq_iff.2

@[to_additive (attr := simp)]
/--
theorem `orbitRel.Quotient.orbit_mk` / 定理 `orbitRel.Quotient.orbit_mk`

English:
theorem orbitRel.Quotient.orbit_mk
  given: (a : α)
  proof: rfl

@[to_additive]

中文:
定理 orbitRel.Quotient.orbit_mk
  条件: (a : α)
  证明: rfl

@[to_additive]
-/
theorem orbitRel.Quotient.orbit_mk (a : α) :
    orbitRel.Quotient.orbit (Quotient.mk'' a : orbitRel.Quotient G α) = MulAction.orbit G a :=
  rfl

@[to_additive]
/--
theorem `orbitRel.Quotient.mem_orbit` / 定理 `orbitRel.Quotient.mem_orbit`

English:
theorem orbitRel.Quotient.mem_orbit
  given: {a : α} {x : orbitRel.Quotient G α}
  proof: by
  induction x using Quotient.inductionOn'
  rw [Quotient.eq'']
  rfl

中文:
定理 orbitRel.Quotient.mem_orbit
  条件: {a : α} {x : orbitRel.Quotient G α}
  证明: by
  induction x using Quotient.inductionOn'
  rw [Quotient.eq'']
  rfl

Depends on / 依赖: Quotient, Quotient.eq, Quotient.inductionOn, inductionOn
-/
theorem orbitRel.Quotient.mem_orbit {a : α} {x : orbitRel.Quotient G α} :
    a in x.orbit ↔ Quotient.mk'' a = x := by
  induction x using Quotient.inductionOn'
  rw [Quotient.eq'']
  rfl

/-- Note that `hφ = Quotient.out_eq'` is a useful choice here. -/
@[to_additive /-- Note that `hφ = Quotient.out_eq'` is a useful choice here. -/]
/--
theorem `orbitRel.Quotient.orbit_eq_orbit_out` / 定理 `orbitRel.Quotient.orbit_eq_orbit_out`

English:
theorem orbitRel.Quotient.orbit_eq_orbit_out
  statement: (x : orbitRel.Quotient G α)
  proof: by
  conv_lhs => rw [← hφ x]
  rfl

@[to_additive]

中文:
定理 orbitRel.Quotient.orbit_eq_orbit_out
  结论: (x : orbitRel.Quotient G α)
  证明: by
  conv_lhs => rw [← hφ x]
  rfl

@[to_additive]

Depends on / 依赖: Quotient, Quotient.mk, RightInverse, orbitRel
-/
theorem orbitRel.Quotient.orbit_eq_orbit_out (x : orbitRel.Quotient G α)
    {φ : orbitRel.Quotient G α -> α} (hφ : letI := orbitRel G α; RightInverse φ Quotient.mk') :
    orbitRel.Quotient.orbit x = MulAction.orbit G (φ x) := by
  conv_lhs => rw [← hφ x]
  rfl

@[to_additive]
/--
lemma `orbitRel.Quotient.orbit_injective` / 引理 `orbitRel.Quotient.orbit_injective`

English:
lemma orbitRel.Quotient.orbit_injective
  proof: by
  intro x y h
  simp_rw [orbitRel.Quotient.orbit_eq_orbit_out _ Quotient.out_eq', orbit_eq_iff,
    ← orbitRel_apply] at h
  simpa [← Quotient.eq''] using h

@[to_additive (attr := simp)]

中文:
引理 orbitRel.Quotient.orbit_injective
  证明: by
  intro x y h
  simp_rw [orbitRel.Quotient.orbit_eq_orbit_out _ Quotient.out_eq', orbit_eq_iff,
    ← orbitRel_apply] at h
  simpa [← Quotient.eq''] using h

@[to_additive (attr := simp)]

Depends on / 依赖: Quotient, Quotient.eq, Quotient.out_eq, orbitRel, orbitRel.Quotient.orbit_eq_orbit_out, orbitRel_apply, orbit_eq_iff, orbit_eq_orbit_out, out_eq, simp_rw
-/
lemma orbitRel.Quotient.orbit_injective :
    Injective (orbitRel.Quotient.orbit : orbitRel.Quotient G α -> Set α) := by
  intro x y h
  simp_rw [orbitRel.Quotient.orbit_eq_orbit_out _ Quotient.out_eq', orbit_eq_iff,
    ← orbitRel_apply] at h
  simpa [← Quotient.eq''] using h

@[to_additive (attr := simp)]
/--
lemma `orbitRel.Quotient.orbit_inj` / 引理 `orbitRel.Quotient.orbit_inj`

English:
lemma orbitRel.Quotient.orbit_inj
  given: {x y : orbitRel.Quotient G α}
  statement: x.orbit = y.orbit ↔ x = y
  proof: orbitRel.Quotient.orbit_injective.eq_iff

@[to_additive]

中文:
引理 orbitRel.Quotient.orbit_inj
  条件: {x y : orbitRel.Quotient G α}
  结论: x.orbit = y.orbit ↔ x = y
  证明: orbitRel.Quotient.orbit_injective.eq_iff

@[to_additive]

Depends on / 依赖: Quotient, eq_iff, orbitRel, orbitRel.Quotient.orbit_injective.eq_iff, orbit_injective
-/
lemma orbitRel.Quotient.orbit_inj {x y : orbitRel.Quotient G α} : x.orbit = y.orbit ↔ x = y :=
  orbitRel.Quotient.orbit_injective.eq_iff

@[to_additive]
/--
lemma `orbitRel.quotient_eq_of_quotient_subgroup_eq` / 引理 `orbitRel.quotient_eq_of_quotient_subgroup_eq`

English:
lemma orbitRel.quotient_eq_of_quotient_subgroup_eq
  statement: {H : Subgroup G} {a b : α}
  proof: by
  rw [@Quotient.eq] at h ⊢
  exact mem_orbit_of_mem_orbit_subgroup h

@[to_additive]

中文:
引理 orbitRel.quotient_eq_of_quotient_subgroup_eq
  结论: {H : Subgroup G} {a b : α}
  证明: by
  rw [@Quotient.eq] at h ⊢
  exact mem_orbit_of_mem_orbit_subgroup h

@[to_additive]

Depends on / 依赖: Quotient, Quotient.eq, mem_orbit_of_mem_orbit_subgroup
-/
lemma orbitRel.quotient_eq_of_quotient_subgroup_eq {H : Subgroup G} {a b : α}
    (h : (⟦a⟧ : orbitRel.Quotient H α) = ⟦b⟧) : (⟦a⟧ : orbitRel.Quotient G α) = ⟦b⟧ := by
  rw [@Quotient.eq] at h ⊢
  exact mem_orbit_of_mem_orbit_subgroup h

@[to_additive]
/--
lemma `orbitRel.quotient_eq_of_quotient_subgroup_eq'` / 引理 `orbitRel.quotient_eq_of_quotient_subgroup_eq'`

English:
lemma orbitRel.quotient_eq_of_quotient_subgroup_eq'
  statement: {H : Subgroup G} {a b : α}
  proof: orbitRel.quotient_eq_of_quotient_subgroup_eq h

@[to_additive]
nonrec lemma orbitRel.Quotient.nonempty_orbit (x : orbitRel.Quotient G α) :
    Set.Nonempty x.orbit := by
  rw [orbitRel.Quotient.orbit_eq_orbit_out x Quotient.out_eq']
  exact nonempty_orbit _

@[to_additive]
nonrec lemma orbitRel.Quot

中文:
引理 orbitRel.quotient_eq_of_quotient_subgroup_eq'
  结论: {H : Subgroup G} {a b : α}
  证明: orbitRel.quotient_eq_of_quotient_subgroup_eq h

@[to_additive]
nonrec lemma orbitRel.Quotient.nonempty_orbit (x : orbitRel.Quotient G α) :
    Set.Nonempty x.orbit := by
  rw [orbitRel.Quotient.orbit_eq_orbit_out x Quotient.out_eq']
  exact nonempty_orbit _

@[to_additive]
nonrec lemma orbitRel.Quot

Depends on / 依赖: orbitRel, orbitRel.quotient_eq_of_quotient_subgroup_eq, quotient_eq_of_quotient_subgroup_eq
-/
lemma orbitRel.quotient_eq_of_quotient_subgroup_eq' {H : Subgroup G} {a b : α}
    (h : (Quotient.mk'' a : orbitRel.Quotient H α) = Quotient.mk'' b) :
    (Quotient.mk'' a : orbitRel.Quotient G α) = Quotient.mk'' b :=
  orbitRel.quotient_eq_of_quotient_subgroup_eq h

@[to_additive]
nonrec lemma orbitRel.Quotient.nonempty_orbit (x : orbitRel.Quotient G α) :
    Set.Nonempty x.orbit := by
  rw [orbitRel.Quotient.orbit_eq_orbit_out x Quotient.out_eq']
  exact nonempty_orbit _

@[to_additive]
nonrec lemma orbitRel.Quotient.mapsTo_smul_orbit (g : G) (x : orbitRel.Quotient G α) :
    Set.MapsTo (g • ·) x.orbit x.orbit := by
  rw [orbitRel.Quotient.orbit_eq_orbit_out x Quotient.out_eq']
  exact mapsTo_smul_orbit g x.out

@[to_additive]
instance (x : orbitRel.Quotient G α) : MulAction G x.orbit where
  smul g := (orbitRel.Quotient.mapsTo_smul_orbit g x).restrict _ _ _
  one_smul a := Subtype.ext (one_smul G (a : α))
  mul_smul g g' a' := Subtype.ext (mul_smul g g' (a' : α))

@[to_additive (attr := simp)]
/--
lemma `orbitRel.Quotient.orbit.coe_smul` / 引理 `orbitRel.Quotient.orbit.coe_smul`

English:
lemma orbitRel.Quotient.orbit.coe_smul
  given: {g : G} {x : orbitRel.Quotient G α} {a : x.orbit}
  proof: rfl

@[to_additive (attr := norm_cast, simp)]

中文:
引理 orbitRel.Quotient.orbit.coe_smul
  条件: {g : G} {x : orbitRel.Quotient G α} {a : x.orbit}
  证明: rfl

@[to_additive (attr := norm_cast, simp)]
-/
lemma orbitRel.Quotient.orbit.coe_smul {g : G} {x : orbitRel.Quotient G α} {a : x.orbit} :
    ↑(g • a) = g • (a : α) :=
  rfl

@[to_additive (attr := norm_cast, simp)]
/--
lemma `orbitRel.Quotient.mem_subgroup_orbit_iff` / 引理 `orbitRel.Quotient.mem_subgroup_orbit_iff`

English:
lemma orbitRel.Quotient.mem_subgroup_orbit_iff
  statement: {H : Subgroup G} {x : orbitRel.Quotient G α}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨g, h⟩
    dsimp at h
    rw [subgroup_smul_def]; rw [← orbit.coe_smul]; rw [← Subtype.ext_iff] at h
    subst h
    exact MulAction.mem_orbit _ g
  · rcases h with ⟨g, rfl⟩
    exact MulAction.mem_orbit _ g

@[to_additive]

中文:
引理 orbitRel.Quotient.mem_subgroup_orbit_iff
  结论: {H : Subgroup G} {x : orbitRel.Quotient G α}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨g, h⟩
    dsimp at h
    rw [subgroup_smul_def]; rw [← orbit.coe_smul]; rw [← Subtype.ext_iff] at h
    subst h
    exact MulAction.mem_orbit _ g
  · rcases h with ⟨g, rfl⟩
    exact MulAction.mem_orbit _ g

@[to_additive]

Depends on / 依赖: MulAction, MulAction.mem_orbit, Subtype, Subtype.ext_iff, coe_smul, ext_iff, mem_orbit, orbit.coe_smul, subgroup_smul_def
-/
lemma orbitRel.Quotient.mem_subgroup_orbit_iff {H : Subgroup G} {x : orbitRel.Quotient G α}
    {a b : x.orbit} : (a : α) in MulAction.orbit H (b : α) ↔ a in MulAction.orbit H b := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨g, h⟩
    dsimp at h
    rw [subgroup_smul_def]; rw [← orbit.coe_smul]; rw [← Subtype.ext_iff] at h
    subst h
    exact MulAction.mem_orbit _ g
  · rcases h with ⟨g, rfl⟩
    exact MulAction.mem_orbit _ g

@[to_additive]
/--
lemma `orbitRel.Quotient.subgroup_quotient_eq_iff` / 引理 `orbitRel.Quotient.subgroup_quotient_eq_iff`

English:
lemma orbitRel.Quotient.subgroup_quotient_eq_iff
  statement: {H : Subgroup G} {x : orbitRel.Quotient G α}
  proof: by
  simp_rw [← @Quotient.mk''_eq_mk, Quotient.eq'']
  exact orbitRel.Quotient.mem_subgroup_orbit_iff.symm

@[to_additive]

中文:
引理 orbitRel.Quotient.subgroup_quotient_eq_iff
  结论: {H : Subgroup G} {x : orbitRel.Quotient G α}
  证明: by
  simp_rw [← @Quotient.mk''_eq_mk, Quotient.eq'']
  exact orbitRel.Quotient.mem_subgroup_orbit_iff.symm

@[to_additive]

Depends on / 依赖: Quotient, Quotient.eq, Quotient.mk, _eq_mk, mem_subgroup_orbit_iff, orbitRel, orbitRel.Quotient.mem_subgroup_orbit_iff.symm, simp_rw
-/
lemma orbitRel.Quotient.subgroup_quotient_eq_iff {H : Subgroup G} {x : orbitRel.Quotient G α}
    {a b : x.orbit} : (⟦a⟧ : orbitRel.Quotient H x.orbit) = ⟦b⟧ ↔
      (⟦↑a⟧ : orbitRel.Quotient H α) = ⟦↑b⟧ := by
  simp_rw [← @Quotient.mk''_eq_mk, Quotient.eq'']
  exact orbitRel.Quotient.mem_subgroup_orbit_iff.symm

@[to_additive]
/--
lemma `orbitRel.Quotient.mem_subgroup_orbit_iff'` / 引理 `orbitRel.Quotient.mem_subgroup_orbit_iff'`

English:
lemma orbitRel.Quotient.mem_subgroup_orbit_iff'
  statement: {H : Subgroup G} {x : orbitRel.Quotient G α}
  proof: by
  simp_rw [mem_orbit_symm (a₂ := c)]
  convert! Iff.rfl using 2
  rw [orbit_eq_iff]
  suffices hb : ↑b in orbitRel.Quotient.orbit (⟦a⟧ : orbitRel.Quotient H x.orbit) by
    rw [orbitRel.Quotient.orbit_eq_orbit_out (⟦a⟧ : orbitRel.Quotient H x.orbit) Quotient.out_eq']
       at hb
    rw [orbitRel

中文:
引理 orbitRel.Quotient.mem_subgroup_orbit_iff'
  结论: {H : Subgroup G} {x : orbitRel.Quotient G α}
  证明: by
  simp_rw [mem_orbit_symm (a₂ := c)]
  convert! Iff.rfl using 2
  rw [orbit_eq_iff]
  suffices hb : ↑b in orbitRel.Quotient.orbit (⟦a⟧ : orbitRel.Quotient H x.orbit) by
    rw [orbitRel.Quotient.orbit_eq_orbit_out (⟦a⟧ : orbitRel.Quotient H x.orbit) Quotient.out_eq']
       at hb
    rw [orbitRel

Depends on / 依赖: Iff.rfl, Quotient, Quotient.eq, Quotient.mk, Quotient.out_eq, _eq_mk, convert, mem_orbit, mem_orbit_symm, mem_subgroup_orbit_iff, orbitRel, orbitRel.Quotient, orbitRel.Quotient.mem_orbit, orbitRel.Quotient.mem_subgroup_orbit_iff, orbitRel.Quotient.orbit, orbitRel.Quotient.orbit_eq_orbit_out, orbitRel_apply, orbit_eq_iff, orbit_eq_orbit_out, out_eq
-/
lemma orbitRel.Quotient.mem_subgroup_orbit_iff' {H : Subgroup G} {x : orbitRel.Quotient G α}
    {a b : x.orbit} {c : α} (h : (⟦a⟧ : orbitRel.Quotient H x.orbit) = ⟦b⟧) :
    (a : α) in MulAction.orbit H c ↔ (b : α) in MulAction.orbit H c := by
  simp_rw [mem_orbit_symm (a₂ := c)]
  convert! Iff.rfl using 2
  rw [orbit_eq_iff]
  suffices hb : ↑b in orbitRel.Quotient.orbit (⟦a⟧ : orbitRel.Quotient H x.orbit) by
    rw [orbitRel.Quotient.orbit_eq_orbit_out (⟦a⟧ : orbitRel.Quotient H x.orbit) Quotient.out_eq']
       at hb
    rw [orbitRel.Quotient.mem_subgroup_orbit_iff]
    convert! hb using 1
    rw [orbit_eq_iff]; rw [← orbitRel_apply]; rw [← Quotient.eq'']; rw [Quotient.out_eq']; rw [@Quotient.mk''_eq_mk]
  rw [orbitRel.Quotient.mem_orbit]; rw [h]; rw [@Quotient.mk''_eq_mk]

variable (G) (α)

local notation "Ω" => orbitRel.Quotient G α

/-- Decomposition of a type `X` as a disjoint union of its orbits under a group action.

This version is expressed in terms of `MulAction.orbitRel.Quotient.orbit` instead of
`MulAction.orbit`, to avoid mentioning `Quotient.out`. -/
@[to_additive
  /-- Decomposition of a type `X` as a disjoint union of its orbits under an additive group action.

  This version is expressed in terms of `AddAction.orbitRel.Quotient.orbit` instead of
  `AddAction.orbit`, to avoid mentioning `Quotient.out`. -/]
/--
Definition of `selfEquivSigmaOrbits'` / `selfEquivSigmaOrbits'` 的定义

English:
definition selfEquivSigmaOrbits'
  signature: : α ≃ Σ ω : Ω, ω.orbit
  body: letI := orbitRel G α
  calc
    α ≃ Σ ω : Ω, { a // Quotient.mk' a = ω } := (Equiv.sigmaFiberEquiv Quotient.mk').symm
    _ ≃ Σ ω : Ω, ω.orbit :=
      Equiv.sigmaCongrRight fun _ =>
        Equiv.subtypeEquivRight fun _ => orbitRel.Quotient.mem_orbit.symm

中文:
定义 selfEquivSigmaOrbits'
  签名: : α ≃ Σ ω : Ω, ω.orbit
  定义体: letI := orbitRel G α
  calc
    α ≃ Σ ω : Ω, { a // Quotient.mk' a = ω } := (Equiv.sigmaFiberEquiv Quotient.mk').symm
    _ ≃ Σ ω : Ω, ω.orbit :=
      Equiv.sigmaCongrRight fun _ =>
        Equiv.subtypeEquivRight fun _ => orbitRel.Quotient.mem_orbit.symm

Depends on / 依赖: Equiv.sigmaCongrRight, Equiv.sigmaFiberEquiv, Equiv.subtypeEquivRight, Quotient, Quotient.mk, mem_orbit, orbitRel, orbitRel.Quotient.mem_orbit.symm, sigmaCongrRight, sigmaFiberEquiv, subtypeEquivRight
-/
def selfEquivSigmaOrbits' : α ≃ Σ ω : Ω, ω.orbit :=
  letI := orbitRel G α
  calc
    α ≃ Σ ω : Ω, { a // Quotient.mk' a = ω } := (Equiv.sigmaFiberEquiv Quotient.mk').symm
    _ ≃ Σ ω : Ω, ω.orbit :=
      Equiv.sigmaCongrRight fun _ =>
        Equiv.subtypeEquivRight fun _ => orbitRel.Quotient.mem_orbit.symm

/-- Decomposition of a type `X` as a disjoint union of its orbits under a group action. -/
@[to_additive /-- Decomposition of a type `X` as a disjoint union of its orbits under an additive
group action. -/]
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `selfEquivSigmaOrbits` / `selfEquivSigmaOrbits` 的定义

English:
definition selfEquivSigmaOrbits
  signature: : α ≃ Σ ω : Ω, orbit G ω.out
  body: (selfEquivSigmaOrbits' G α).trans
    Equiv.sigmaCongrRight fun _ =>
Equiv.setCongr orbitRel.Quotient.orbit_eq_orbit_out _ Quotient.out_eq'

中文:
定义 selfEquivSigmaOrbits
  签名: : α ≃ Σ ω : Ω, orbit G ω.out
  定义体: (selfEquivSigmaOrbits' G α).trans
    Equiv.sigmaCongrRight fun _ =>
Equiv.setCongr orbitRel.Quotient.orbit_eq_orbit_out _ Quotient.out_eq'

Depends on / 依赖: Equiv.setCongr, Equiv.sigmaCongrRight, Quotient, Quotient.out_eq, orbitRel, orbitRel.Quotient.orbit_eq_orbit_out, orbit_eq_orbit_out, out_eq, selfEquivSigmaOrbits, setCongr, sigmaCongrRight
-/
noncomputable def selfEquivSigmaOrbits : α ≃ Σ ω : Ω, orbit G ω.out :=
(selfEquivSigmaOrbits' G α).trans
    Equiv.sigmaCongrRight fun _ =>
Equiv.setCongr orbitRel.Quotient.orbit_eq_orbit_out _ Quotient.out_eq'

/-- Decomposition of a type `X` as a disjoint union of its orbits under a group action.
Phrased as a set union. See `MulAction.selfEquivSigmaOrbits` for the type isomorphism. -/
@[to_additive /-- Decomposition of a type `X` as a disjoint union of its orbits under an additive
group action. Phrased as a set union. See `AddAction.selfEquivSigmaOrbits` for the type
isomorphism. -/]
/--
lemma `univ_eq_iUnion_orbit` / 引理 `univ_eq_iUnion_orbit`

English:
lemma univ_eq_iUnion_orbit
  proof: by
  ext x
  simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
  exact ⟨Quotient.mk'' x, by simp⟩

中文:
引理 univ_eq_iUnion_orbit
  证明: by
  ext x
  simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
  exact ⟨Quotient.mk'' x, by simp⟩

Depends on / 依赖: Quotient, Quotient.mk, Set.mem_iUnion, Set.mem_univ, mem_iUnion, mem_univ, true_iff, x.orbit
-/
lemma univ_eq_iUnion_orbit :
    Set.univ (α := α) = ⋃ x : Ω, x.orbit := by
  ext x
  simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
  exact ⟨Quotient.mk'' x, by simp⟩

end Orbit

section Stabilizer

variable (G) in
/-- The stabilizer of an element under an action, i.e. what sends the element to itself.
A subgroup. -/
@[to_additive /-- The stabilizer of an element under an action, i.e. what sends the element to
itself. An additive subgroup. -/]
/--
Definition of `stabilizer` / `stabilizer` 的定义

English:
definition stabilizer
  signature: (a : α)
  body: { stabilizerSubmonoid G a with
    inv_mem' := fun {m} (ha : m • a = a) => show m⁻¹ • a = a by rw [inv_smul_eq_iff, ha] }

@[to_additive]

中文:
定义 stabilizer
  签名: (a : α)
  定义体: { stabilizerSubmonoid G a with
    inv_mem' := fun {m} (ha : m • a = a) => show m⁻¹ • a = a by rw [inv_smul_eq_iff, ha] }

@[to_additive]

Depends on / 依赖: inv_mem, inv_smul_eq_iff, stabilizerSubmonoid
-/
def stabilizer (a : α) : Subgroup G :=
  { stabilizerSubmonoid G a with
    inv_mem' := fun {m} (ha : m • a = a) => show m⁻¹ • a = a by rw [inv_smul_eq_iff, ha] }

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] (a
  body: fun _ => inferInstanceAs Decidable (_ = _)

@[to_additive (attr := simp)]

中文:
实例 [DecidableEq
  签名: α] (a
  定义体: fun _ => inferInstanceAs Decidable (_ = _)

@[to_additive (attr := simp)]

Depends on / 依赖: Decidable
-/
instance [DecidableEq α] (a : α) : DecidablePred (· in stabilizer G a) :=
fun _ => inferInstanceAs Decidable (_ = _)

@[to_additive (attr := simp)]
/--
theorem `mem_stabilizer_iff` / 定理 `mem_stabilizer_iff`

English:
theorem mem_stabilizer_iff
  given: {a : α} {g : G}
  statement: g in stabilizer G a ↔ g • a = a
  proof: Iff.rfl

@[to_additive]

中文:
定理 mem_stabilizer_iff
  条件: {a : α} {g : G}
  结论: g in stabilizer G a ↔ g • a = a
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem mem_stabilizer_iff {a : α} {g : G} : g in stabilizer G a ↔ g • a = a :=
  Iff.rfl

@[to_additive]
/--
lemma `le_stabilizer_smul_left` / 引理 `le_stabilizer_smul_left`

English:
lemma le_stabilizer_smul_left
  given: [SMul α β] [IsScalarTower G α β] (a : α) (b : β)
  proof: by
  simp_rw [SetLike.le_def, mem_stabilizer_iff, ← smul_assoc]; rintro a h; rw [h]

中文:
引理 le_stabilizer_smul_left
  条件: [SMul α β] [IsScalarTower G α β] (a : α) (b : β)
  证明: by
  simp_rw [SetLike.le_def, mem_stabilizer_iff, ← smul_assoc]; rintro a h; rw [h]

Depends on / 依赖: SetLike, SetLike.le_def, le_def, mem_stabilizer_iff, simp_rw, smul_assoc
-/
lemma le_stabilizer_smul_left [SMul α β] [IsScalarTower G α β] (a : α) (b : β) :
    stabilizer G a <= stabilizer G (a • b) := by
  simp_rw [SetLike.le_def, mem_stabilizer_iff, ← smul_assoc]; rintro a h; rw [h]

-- This lemma does not need `MulAction G α`, only `SMul G α`.
-- We use `G'` instead of `G` to locally reduce the typeclass assumptions.
@[to_additive]
/--
lemma `le_stabilizer_smul_right` / 引理 `le_stabilizer_smul_right`

English:
lemma le_stabilizer_smul_right
  statement: {G'} [Group G'] [SMul α β] [MulAction G' β]
  proof: by
  simp_rw [SetLike.le_def, mem_stabilizer_iff, smul_comm]; rintro a h; rw [h]

@[to_additive (attr := simp)]

中文:
引理 le_stabilizer_smul_right
  结论: {G'} [Group G'] [SMul α β] [MulAction G' β]
  证明: by
  simp_rw [SetLike.le_def, mem_stabilizer_iff, smul_comm]; rintro a h; rw [h]

@[to_additive (attr := simp)]

Depends on / 依赖: SetLike, SetLike.le_def, le_def, mem_stabilizer_iff, simp_rw, smul_comm
-/
lemma le_stabilizer_smul_right {G'} [Group G'] [SMul α β] [MulAction G' β]
    [SMulCommClass G' α β] (a : α) (b : β) :
    stabilizer G' b <= stabilizer G' (a • b) := by
  simp_rw [SetLike.le_def, mem_stabilizer_iff, smul_comm]; rintro a h; rw [h]

@[to_additive (attr := simp)]
/--
lemma `stabilizer_smul_eq_left` / 引理 `stabilizer_smul_eq_left`

English:
lemma stabilizer_smul_eq_left
  statement: [SMul α β] [IsScalarTower G α β] (a : α) (b : β)
  proof: by
  refine (le_stabilizer_smul_left _ _).antisymm' fun a ha => ?_
  simpa only [mem_stabilizer_iff, ← smul_assoc, h.eq_iff] using ha

@[to_additive (attr := simp)]

中文:
引理 stabilizer_smul_eq_left
  结论: [SMul α β] [IsScalarTower G α β] (a : α) (b : β)
  证明: by
  refine (le_stabilizer_smul_left _ _).antisymm' fun a ha => ?_
  simpa only [mem_stabilizer_iff, ← smul_assoc, h.eq_iff] using ha

@[to_additive (attr := simp)]

Depends on / 依赖: antisymm, eq_iff, h.eq_iff, le_stabilizer_smul_left, mem_stabilizer_iff, smul_assoc
-/
lemma stabilizer_smul_eq_left [SMul α β] [IsScalarTower G α β] (a : α) (b : β)
    (h : Injective (· • b : α -> β)) : stabilizer G (a • b) = stabilizer G a := by
  refine (le_stabilizer_smul_left _ _).antisymm' fun a ha => ?_
  simpa only [mem_stabilizer_iff, ← smul_assoc, h.eq_iff] using ha

@[to_additive (attr := simp)]
/--
lemma `stabilizer_smul_eq_right` / 引理 `stabilizer_smul_eq_right`

English:
lemma stabilizer_smul_eq_right
  given: {α} [Group α] [MulAction α β] [SMulCommClass G α β] (a : α) (b : β)
  proof: (le_stabilizer_smul_right _ _).antisymm' (le_stabilizer_smul_right a⁻¹ _).trans_eq by
    rw [inv_smul_smul]

@[to_additive (attr := simp)]

中文:
引理 stabilizer_smul_eq_right
  条件: {α} [Group α] [MulAction α β] [SMulCommClass G α β] (a : α) (b : β)
  证明: (le_stabilizer_smul_right _ _).antisymm' (le_stabilizer_smul_right a⁻¹ _).trans_eq by
    rw [inv_smul_smul]

@[to_additive (attr := simp)]

Depends on / 依赖: antisymm, inv_smul_smul, le_stabilizer_smul_right, trans_eq
-/
lemma stabilizer_smul_eq_right {α} [Group α] [MulAction α β] [SMulCommClass G α β] (a : α) (b : β) :
    stabilizer G (a • b) = stabilizer G b :=
(le_stabilizer_smul_right _ _).antisymm' (le_stabilizer_smul_right a⁻¹ _).trans_eq by
    rw [inv_smul_smul]

@[to_additive (attr := simp)]
/--
lemma `stabilizer_mul_eq_left` / 引理 `stabilizer_mul_eq_left`

English:
lemma stabilizer_mul_eq_left
  given: [Group α] [IsScalarTower G α α] (a b : α)
  proof: stabilizer_smul_eq_left a _ mul_left_injective _

@[to_additive (attr := simp)]

中文:
引理 stabilizer_mul_eq_left
  条件: [Group α] [IsScalarTower G α α] (a b : α)
  证明: stabilizer_smul_eq_left a _ mul_left_injective _

@[to_additive (attr := simp)]

Depends on / 依赖: mul_left_injective, stabilizer_smul_eq_left
-/
lemma stabilizer_mul_eq_left [Group α] [IsScalarTower G α α] (a b : α) :
stabilizer G (a * b) = stabilizer G a := stabilizer_smul_eq_left a _ mul_left_injective _

@[to_additive (attr := simp)]
/--
lemma `stabilizer_mul_eq_right` / 引理 `stabilizer_mul_eq_right`

English:
lemma stabilizer_mul_eq_right
  given: [Group α] [SMulCommClass G α α] (a b : α)
  proof: stabilizer_smul_eq_right a _

中文:
引理 stabilizer_mul_eq_right
  条件: [Group α] [SMulCommClass G α α] (a b : α)
  证明: stabilizer_smul_eq_right a _

Depends on / 依赖: FiniteDimensional, infer_instance, mk_rep, stabilizer_smul_eq_right, v.mk_rep, v.rep
-/
lemma stabilizer_mul_eq_right [Group α] [SMulCommClass G α α] (a b : α) :
    stabilizer G (a * b) = stabilizer G b := stabilizer_smul_eq_right a _

end Stabilizer

end MulAction
