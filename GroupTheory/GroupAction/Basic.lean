/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Data.Finite.Sigma
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Setoid.Basic
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Basic properties of group actions

This file primarily concerns itself with orbits, stabilizers, and other objects defined in terms of
actions. Despite this file being called `basic`, low-level helper lemmas for algebraic manipulation
of `•` belong elsewhere.

## Main definitions

* `MulAction.orbit`
* `MulAction.fixedPoints`
* `MulAction.fixedBy`
* `MulAction.stabilizer`

-/

@[expose] public section


universe u v

open Function Module
open scoped Pointwise

namespace MulAction

variable (M : Type u) [Monoid M] (α : Type v) [MulAction M α] {β : Type*} [MulAction M β]

section Orbit

variable {α M}

@[to_additive]
/--
lemma `fst_mem_orbit_of_mem_orbit` / 引理 `fst_mem_orbit_of_mem_orbit`

English:
lemma fst_mem_orbit_of_mem_orbit
  given: {x y : α × β} (h : x in MulAction.orbit M y)
  proof: by
  rcases h with ⟨g, rfl⟩
  exact mem_orbit _ _

@[to_additive]

中文:
引理 fst_mem_orbit_of_mem_orbit
  条件: {x y : α × β} (h : x in 乘法作用.orbit M y)
  证明: by
  rcases h with ⟨g, rfl⟩
  exact mem_orbit _ _

@[to_additive]

Depends on / 依赖: mem_orbit
-/
lemma fst_mem_orbit_of_mem_orbit {x y : α × β} (h : x in MulAction.orbit M y) :
    x.1 in MulAction.orbit M y.1 := by
  rcases h with ⟨g, rfl⟩
  exact mem_orbit _ _

@[to_additive]
/--
lemma `snd_mem_orbit_of_mem_orbit` / 引理 `snd_mem_orbit_of_mem_orbit`

English:
lemma snd_mem_orbit_of_mem_orbit
  given: {x y : α × β} (h : x in MulAction.orbit M y)
  proof: by
  rcases h with ⟨g, rfl⟩
  exact mem_orbit _ _

@[to_additive]

中文:
引理 snd_mem_orbit_of_mem_orbit
  条件: {x y : α × β} (h : x in 乘法作用.orbit M y)
  证明: by
  rcases h with ⟨g, rfl⟩
  exact mem_orbit _ _

@[to_additive]

Depends on / 依赖: mem_orbit
-/
lemma snd_mem_orbit_of_mem_orbit {x y : α × β} (h : x in MulAction.orbit M y) :
    x.2 in MulAction.orbit M y.2 := by
  rcases h with ⟨g, rfl⟩
  exact mem_orbit _ _

@[to_additive]
/--
lemma `_root_.Finite.finite_mulAction_orbit` / 引理 `_root_.Finite.finite_mulAction_orbit`

English:
lemma _root_.Finite.finite_mulAction_orbit
  given: [Finite M] (a : α)
  statement: Set.Finite (orbit M a)
  proof: Set.finite_range _

中文:
引理 _root_.有限.finite_mulAction_orbit
  条件: [有限 M] (a : α)
  结论: 集合.有限 (orbit M a)
  证明: Set.finite_range _

Depends on / 依赖: Set.finite_range, finite_range
-/
lemma _root_.Finite.finite_mulAction_orbit [Finite M] (a : α) : Set.Finite (orbit M a) :=
  Set.finite_range _

variable (M)

@[to_additive]
/--
theorem `orbit_eq_univ` / 定理 `orbit_eq_univ`

English:
theorem orbit_eq_univ
  given: [IsPretransitive M α] (a : α)
  statement: orbit M a = Set.univ
  proof: (surjective_smul M a).range_eq

中文:
定理 orbit_eq_univ
  条件: [是Pretransitive M α] (a : α)
  结论: orbit M a = 集合.univ
  证明: (surjective_smul M a).range_eq

Depends on / 依赖: range_eq, surjective_smul
-/
theorem orbit_eq_univ [IsPretransitive M α] (a : α) : orbit M a = Set.univ :=
  (surjective_smul M a).range_eq

end Orbit

section FixedPoints

variable {M α}

@[to_additive (attr := simp)]
/--
theorem `subsingleton_orbit_iff_mem_fixedPoints` / 定理 `subsingleton_orbit_iff_mem_fixedPoints`

English:
theorem subsingleton_orbit_iff_mem_fixedPoints
  given: {a : α}
  proof: by
  rw [mem_fixedPoints]
  constructor
  · exact fun h m => h (mem_orbit a m) (mem_orbit_self a)
  · rintro h _ ⟨m, rfl⟩ y ⟨p, rfl⟩
    simp only [h]

@[to_additive mem_fixedPoints_iff_card_orbit_eq_one]

中文:
定理 subsingleton_orbit_iff_mem_fixedPoints
  条件: {a : α}
  证明: by
  rw [mem_fixedPoints]
  constructor
  · exact fun h m => h (mem_orbit a m) (mem_orbit_self a)
  · rintro h _ ⟨m, rfl⟩ y ⟨p, rfl⟩
    simp only [h]

@[to_additive mem_fixedPoints_iff_card_orbit_eq_one]

Depends on / 依赖: mem_fixedPoints, mem_orbit, mem_orbit_self
-/
theorem subsingleton_orbit_iff_mem_fixedPoints {a : α} :
    (orbit M a).Subsingleton ↔ a in fixedPoints M α := by
  rw [mem_fixedPoints]
  constructor
  · exact fun h m => h (mem_orbit a m) (mem_orbit_self a)
  · rintro h _ ⟨m, rfl⟩ y ⟨p, rfl⟩
    simp only [h]

@[to_additive mem_fixedPoints_iff_card_orbit_eq_one]
/--
theorem `mem_fixedPoints_iff_card_orbit_eq_one` / 定理 `mem_fixedPoints_iff_card_orbit_eq_one`

English:
theorem mem_fixedPoints_iff_card_orbit_eq_one
  given: {a : α} [Fintype (orbit M a)]
  proof: by
  simp only [← subsingleton_orbit_iff_mem_fixedPoints, le_antisymm_iff,
    Fintype.card_le_one_iff_subsingleton, Nat.add_one_le_iff, Fintype.card_pos_iff,
    Set.subsingleton_coe, iff_self_and, Set.nonempty_coe_sort, nonempty_orbit, implies_true]

@[to_additive instDecidablePredMemSetFixedByAdd

中文:
定理 mem_fixedPoints_iff_card_orbit_eq_one
  条件: {a : α} [有限类型 (orbit M a)]
  证明: by
  simp only [← subsingleton_orbit_iff_mem_fixedPoints, le_antisymm_iff,
    Fintype.card_le_one_iff_subsingleton, Nat.add_one_le_iff, Fintype.card_pos_iff,
    Set.subsingleton_coe, iff_self_and, Set.nonempty_coe_sort, nonempty_orbit, implies_true]

@[to_additive instDecidablePredMemSetFixedByAdd

Depends on / 依赖: Fintype, Fintype.card_le_one_iff_subsingleton, Fintype.card_pos_iff, Nat.add_one_le_iff, Set.nonempty_coe_sort, Set.subsingleton_coe, add_one_le_iff, card_le_one_iff_subsingleton, card_pos_iff, iff_self_and, implies_true, le_antisymm_iff, nonempty_coe_sort, nonempty_orbit, subsingleton_coe, subsingleton_orbit_iff_mem_fixedPoints
-/
theorem mem_fixedPoints_iff_card_orbit_eq_one {a : α} [Fintype (orbit M a)] :
    a in fixedPoints M α ↔ Fintype.card (orbit M a) = 1 := by
  simp only [← subsingleton_orbit_iff_mem_fixedPoints, le_antisymm_iff,
    Fintype.card_le_one_iff_subsingleton, Nat.add_one_le_iff, Fintype.card_pos_iff,
    Set.subsingleton_coe, iff_self_and, Set.nonempty_coe_sort, nonempty_orbit, implies_true]

@[to_additive instDecidablePredMemSetFixedByAddOfDecidableEq]
instance (m : M) [DecidableEq β] :
    DecidablePred fun b : β => b in MulAction.fixedBy β m := fun b => by
  simp only [MulAction.mem_fixedBy]
  infer_instance

end FixedPoints

end MulAction

/--
theorem `smul_cancel_of_non_zero_divisor` / 定理 `smul_cancel_of_non_zero_divisor`

English:
theorem smul_cancel_of_non_zero_divisor
  statement: {M G : Type*} [Monoid M] [AddGroup G]
  proof: by
  rw [← sub_eq_zero]
  refine h _ ?_
  rw [smul_sub]; rw [h']; rw [sub_self]

中文:
定理 smul_cancel_of_non_zero_divisor
  结论: {M G : 类型} [幺半群 M] [加法群 G]
  证明: by
  rw [← sub_eq_zero]
  refine h _ ?_
  rw [smul_sub]; rw [h']; rw [sub_self]

Depends on / 依赖: smul_sub, sub_eq_zero, sub_self
-/
theorem smul_cancel_of_non_zero_divisor {M G : Type*} [Monoid M] [AddGroup G]
    [DistribMulAction M G] (k : M) (h : forall x : G, k • x = 0 -> x = 0) {a b : G} (h' : k • a = k • b) :
    a = b := by
  rw [← sub_eq_zero]
  refine h _ ?_
  rw [smul_sub]; rw [h']; rw [sub_self]

namespace MulAction
variable {G α β : Type*} [Group G] [MulAction G α] [MulAction G β]

/--
theorem `fixedPoints_of_subsingleton` / 定理 `fixedPoints_of_subsingleton`

English:
theorem fixedPoints_of_subsingleton
  given: [Subsingleton α]
  proof: by
  apply Set.eq_univ_of_forall
  simp only [mem_fixedPoints]
  intro x hx
  apply Subsingleton.elim ..

中文:
定理 fixedPoints_of_subsingleton
  条件: [子单例 α]
  证明: by
  apply Set.eq_univ_of_forall
  simp only [mem_fixedPoints]
  intro x hx
  apply Subsingleton.elim ..
-/
@[to_additive] theorem fixedPoints_of_subsingleton [Subsingleton α] :
    fixedPoints G α = .univ := by
  apply Set.eq_univ_of_forall
  simp only [mem_fixedPoints]
  intro x hx
  apply Subsingleton.elim ..

/-- If a group acts nontrivially, then the type is nontrivial -/
@[to_additive /-- If a subgroup acts nontrivially, then the type is nontrivial. -/]
/--
theorem `nontrivial_of_fixedPoints_ne_univ` / 定理 `nontrivial_of_fixedPoints_ne_univ`

English:
theorem nontrivial_of_fixedPoints_ne_univ
  given: (h : fixedPoints G α != .univ)
  proof: (subsingleton_or_nontrivial α).resolve_left fun _ => h fixedPoints_of_subsingleton

中文:
定理 nontrivial_of_fixedPoints_ne_univ
  条件: (h : fixedPoints G α != .univ)
  证明: (subsingleton_or_nontrivial α).resolve_left fun _ => h fixedPoints_of_subsingleton

Depends on / 依赖: fixedPoints_of_subsingleton, resolve_left, subsingleton_or_nontrivial
-/
theorem nontrivial_of_fixedPoints_ne_univ (h : fixedPoints G α != .univ) :
    Nontrivial α :=
  (subsingleton_or_nontrivial α).resolve_left fun _ => h fixedPoints_of_subsingleton

section Orbit

-- TODO: This proof is redoing a special case of `MulAction.IsInvariantBlock.isBlock`. Can we move
-- this lemma earlier to golf?
@[to_additive (attr := simp)]
/--
theorem `smul_orbit` / 定理 `smul_orbit`

English:
theorem smul_orbit
  given: (g : G) (a : α)
  statement: g • orbit G a = orbit G a
  proof: (smul_orbit_subset g a).antisymm
    calc
      orbit G a = g • g⁻¹ • orbit G a := (smul_inv_smul _ _).symm
      _ subseteq g • orbit G a := Set.image_mono (smul_orbit_subset _ _)

中文:
定理 smul_orbit
  条件: (g : G) (a : α)
  结论: g • orbit G a = orbit G a
  证明: (smul_orbit_subset g a).antisymm
    calc
      orbit G a = g • g⁻¹ • orbit G a := (smul_inv_smul _ _).symm
      _ subseteq g • orbit G a := Set.image_mono (smul_orbit_subset _ _)

Depends on / 依赖: Set.image_mono, antisymm, image_mono, smul_inv_smul, smul_orbit_subset, subseteq
-/
theorem smul_orbit (g : G) (a : α) : g • orbit G a = orbit G a :=
(smul_orbit_subset g a).antisymm
    calc
      orbit G a = g • g⁻¹ • orbit G a := (smul_inv_smul _ _).symm
      _ subseteq g • orbit G a := Set.image_mono (smul_orbit_subset _ _)

/-- The action of a group on an orbit is transitive. -/
@[to_additive /-- The action of an additive group on an orbit is transitive. -/]
instance (a : α) : IsPretransitive G (orbit G a) :=
  ⟨by
    rintro ⟨_, g, rfl⟩ ⟨_, h, rfl⟩
    use h * g⁻¹
    ext1
    simp [mul_smul]⟩

@[to_additive]
/--
lemma `orbitRel_subgroup_le` / 引理 `orbitRel_subgroup_le`

English:
lemma orbitRel_subgroup_le
  given: (H : Subgroup G)
  statement: orbitRel H α <= orbitRel G α
  proof: Setoid.le_def.2 mem_orbit_of_mem_orbit_subgroup

@[to_additive]

中文:
引理 orbitRel_subgroup_le
  条件: (H : 子群 G)
  结论: orbitRel H α <= orbitRel G α
  证明: Setoid.le_def.2 mem_orbit_of_mem_orbit_subgroup

@[to_additive]

Depends on / 依赖: Setoid, Setoid.le_def, le_def, mem_orbit_of_mem_orbit_subgroup
-/
lemma orbitRel_subgroup_le (H : Subgroup G) : orbitRel H α <= orbitRel G α :=
  Setoid.le_def.2 mem_orbit_of_mem_orbit_subgroup

@[to_additive]
/--
lemma `orbitRel_subgroupOf` / 引理 `orbitRel_subgroupOf`

English:
lemma orbitRel_subgroupOf
  given: (H K : Subgroup G)
  proof: by
  rw [← Subgroup.subgroupOf_map_subtype]
  ext x
  simp_rw [orbitRel_apply]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨⟨gv, gp⟩, rfl⟩
    simp only
    refine mem_orbit _ (⟨gv, ?_⟩ : Subgroup.map K.subtype (H.subgroupOf K))
    simpa using! gp
  · rcases h with ⟨⟨gv, gp⟩, rfl⟩
    sim

中文:
引理 orbitRel_subgroupOf
  条件: (H K : 子群 G)
  证明: by
  rw [← Subgroup.subgroupOf_map_subtype]
  ext x
  simp_rw [orbitRel_apply]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨⟨gv, gp⟩, rfl⟩
    simp only
    refine mem_orbit _ (⟨gv, ?_⟩ : Subgroup.map K.subtype (H.subgroupOf K))
    simpa using! gp
  · rcases h with ⟨⟨gv, gp⟩, rfl⟩
    sim

Depends on / 依赖: H.subgroupOf, K.subtype, Subgroup, Subgroup.map, Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.subgroupOf_map_subtype, mem_inf, mem_orbit, mem_subgroupOf, orbitRel_apply, simp_rw, subgroupOf, subgroupOf_map_subtype, subtype
-/
lemma orbitRel_subgroupOf (H K : Subgroup G) :
    orbitRel (H.subgroupOf K) α = orbitRel (H ⊓ K : Subgroup G) α := by
  rw [← Subgroup.subgroupOf_map_subtype]
  ext x
  simp_rw [orbitRel_apply]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨⟨gv, gp⟩, rfl⟩
    simp only
    refine mem_orbit _ (⟨gv, ?_⟩ : Subgroup.map K.subtype (H.subgroupOf K))
    simpa using! gp
  · rcases h with ⟨⟨gv, gp⟩, rfl⟩
    simp only
    simp only [Subgroup.subgroupOf_map_subtype, Subgroup.mem_inf] at gp
    refine mem_orbit _ (⟨⟨gv, ?_⟩, ?_⟩ : H.subgroupOf K)
    · exact gp.2
    · simp only [Subgroup.mem_subgroupOf]
      exact gp.1

variable (G α)

/-- An action is pretransitive if and only if the quotient by `MulAction.orbitRel` is a
subsingleton. -/
@[to_additive /-- An additive action is pretransitive if and only if the quotient by
`AddAction.orbitRel` is a subsingleton. -/]
/--
theorem `pretransitive_iff_subsingleton_quotient` / 定理 `pretransitive_iff_subsingleton_quotient`

English:
theorem pretransitive_iff_subsingleton_quotient
  proof: by
  refine ⟨fun _ => ⟨fun a b => ?_⟩, fun _ => ⟨fun a b => ?_⟩⟩
  · refine Quot.inductionOn a (fun x => ?_)
    exact Quot.inductionOn b (fun y => Quot.sound <| exists_smul_eq G y x)
  · have h : Quotient.mk (orbitRel G α) b = ⟦a⟧ := Subsingleton.elim _ _
    exact Quotient.eq''.mp h

中文:
定理 pretransitive_iff_subsingleton_quotient
  证明: by
  refine ⟨fun _ => ⟨fun a b => ?_⟩, fun _ => ⟨fun a b => ?_⟩⟩
  · refine Quot.inductionOn a (fun x => ?_)
    exact Quot.inductionOn b (fun y => Quot.sound <| exists_smul_eq G y x)
  · have h : Quotient.mk (orbitRel G α) b = ⟦a⟧ := Subsingleton.elim _ _
    exact Quotient.eq''.mp h

Depends on / 依赖: Quot.inductionOn, Quot.sound, Quotient, Quotient.eq, Quotient.mk, Subsingleton, Subsingleton.elim, exists_smul_eq, inductionOn, orbitRel
-/
theorem pretransitive_iff_subsingleton_quotient :
    IsPretransitive G α ↔ Subsingleton (orbitRel.Quotient G α) := by
  refine ⟨fun _ => ⟨fun a b => ?_⟩, fun _ => ⟨fun a b => ?_⟩⟩
  · refine Quot.inductionOn a (fun x => ?_)
    exact Quot.inductionOn b (fun y => Quot.sound <| exists_smul_eq G y x)
  · have h : Quotient.mk (orbitRel G α) b = ⟦a⟧ := Subsingleton.elim _ _
    exact Quotient.eq''.mp h

/-- If `α` is non-empty, an action is pretransitive if and only if the quotient has exactly one
element. -/
@[to_additive /-- If `α` is non-empty, an additive action is pretransitive if and only if the
quotient has exactly one element. -/]
/--
theorem `pretransitive_iff_unique_quotient_of_nonempty` / 定理 `pretransitive_iff_unique_quotient_of_nonempty`

English:
theorem pretransitive_iff_unique_quotient_of_nonempty
  given: [Nonempty α]
  proof: by
  rw [unique_iff_subsingleton_and_nonempty]; rw [pretransitive_iff_subsingleton_quotient]; rw [iff_self_and]
  exact fun _ => (nonempty_quotient_iff _).mpr inferInstance

中文:
定理 pretransitive_iff_unique_quotient_of_nonempty
  条件: [非空 α]
  证明: by
  rw [unique_iff_subsingleton_and_nonempty]; rw [pretransitive_iff_subsingleton_quotient]; rw [iff_self_and]
  exact fun _ => (nonempty_quotient_iff _).mpr inferInstance

Depends on / 依赖: iff_self_and, nonempty_quotient_iff, pretransitive_iff_subsingleton_quotient, unique_iff_subsingleton_and_nonempty
-/
theorem pretransitive_iff_unique_quotient_of_nonempty [Nonempty α] :
    IsPretransitive G α ↔ Nonempty (Unique <| orbitRel.Quotient G α) := by
  rw [unique_iff_subsingleton_and_nonempty]; rw [pretransitive_iff_subsingleton_quotient]; rw [iff_self_and]
  exact fun _ => (nonempty_quotient_iff _).mpr inferInstance

variable {G α}

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
instance (x : orbitRel.Quotient G α) : IsPretransitive G x.orbit where
  exists_smul_eq := by
    induction x using Quotient.inductionOn'
    rintro ⟨y, yh⟩ ⟨z, zh⟩
    rw [orbitRel.Quotient.mem_orbit]; rw [Quotient.eq''] at yh zh
    rcases yh with ⟨g, rfl⟩
    rcases zh with ⟨h, rfl⟩
    refine ⟨h * g⁻¹, ?_⟩
    ext
    simp [mul_smul]

variable (G) (α)

local notation "Ω" => orbitRel.Quotient G α

@[to_additive]
/--
lemma `_root_.Finite.of_finite_mulAction_orbitRel_quotient` / 引理 `_root_.Finite.of_finite_mulAction_orbitRel_quotient`

English:
lemma _root_.Finite.of_finite_mulAction_orbitRel_quotient
  given: [Finite G] [Finite Ω]
  statement: Finite α
  proof: by
  rw [(selfEquivSigmaOrbits' G _).finite_iff]
  have : forall g : Ω, Finite g.orbit := by
    intro g
    induction g using Quotient.inductionOn'
    simpa [Set.finite_coe_iff] using Finite.finite_mulAction_orbit _
  exact Finite.instSigma

中文:
引理 _root_.有限.of_finite_mulAction_orbitRel_quotient
  条件: [有限 G] [有限 Ω]
  结论: 有限 α
  证明: by
  rw [(selfEquivSigmaOrbits' G _).finite_iff]
  have : forall g : Ω, Finite g.orbit := by
    intro g
    induction g using Quotient.inductionOn'
    simpa [Set.finite_coe_iff] using Finite.finite_mulAction_orbit _
  exact Finite.instSigma

Depends on / 依赖: Finite, Finite.finite_mulAction_orbit, Finite.instSigma, Quotient, Quotient.inductionOn, Set.finite_coe_iff, finite_coe_iff, finite_iff, finite_mulAction_orbit, g.orbit, inductionOn, instSigma, selfEquivSigmaOrbits
-/
lemma _root_.Finite.of_finite_mulAction_orbitRel_quotient [Finite G] [Finite Ω] : Finite α := by
  rw [(selfEquivSigmaOrbits' G _).finite_iff]
  have : forall g : Ω, Finite g.orbit := by
    intro g
    induction g using Quotient.inductionOn'
    simpa [Set.finite_coe_iff] using Finite.finite_mulAction_orbit _
  exact Finite.instSigma

variable (β)

@[to_additive]
/--
lemma `orbitRel_le_fst` / 引理 `orbitRel_le_fst`

English:
lemma orbitRel_le_fst
  proof: Setoid.le_def.2 fst_mem_orbit_of_mem_orbit

@[to_additive]

中文:
引理 orbitRel_le_fst
  证明: Setoid.le_def.2 fst_mem_orbit_of_mem_orbit

@[to_additive]

Depends on / 依赖: Setoid, Setoid.le_def, fst_mem_orbit_of_mem_orbit, le_def
-/
lemma orbitRel_le_fst :
    orbitRel G (α × β) <= (orbitRel G α).comap Prod.fst :=
  Setoid.le_def.2 fst_mem_orbit_of_mem_orbit

@[to_additive]
/--
lemma `orbitRel_le_snd` / 引理 `orbitRel_le_snd`

English:
lemma orbitRel_le_snd
  proof: Setoid.le_def.2 snd_mem_orbit_of_mem_orbit

中文:
引理 orbitRel_le_snd
  证明: Setoid.le_def.2 snd_mem_orbit_of_mem_orbit

Depends on / 依赖: Setoid, Setoid.le_def, le_def, snd_mem_orbit_of_mem_orbit
-/
lemma orbitRel_le_snd :
    orbitRel G (α × β) <= (orbitRel G β).comap Prod.snd :=
  Setoid.le_def.2 snd_mem_orbit_of_mem_orbit

end Orbit

section Stabilizer

@[to_additive (attr := simp)]
/--
lemma `_root_.IsCancelSMul.stabilizer_eq_bot` / 引理 `_root_.IsCancelSMul.stabilizer_eq_bot`

English:
lemma _root_.IsCancelSMul.stabilizer_eq_bot
  given: [IsCancelSMul G α] (a : α)
  proof: .mpr fun _ hg => IsCancelSMul.eq_one_of_smul hg Subgroup.eq_bot_iff_forall _

@[to_additive]

中文:
引理 _root_.是消去标量乘法.stabilizer_eq_bot
  条件: [是消去标量乘法 G α] (a : α)
  证明: .mpr fun _ hg => IsCancelSMul.eq_one_of_smul hg Subgroup.eq_bot_iff_forall _

@[to_additive]

Depends on / 依赖: IsCancelSMul, IsCancelSMul.eq_one_of_smul, Subgroup, Subgroup.eq_bot_iff_forall, eq_bot_iff_forall, eq_one_of_smul
-/
lemma _root_.IsCancelSMul.stabilizer_eq_bot [IsCancelSMul G α] (a : α) :
    stabilizer G a = ⊥ :=
.mpr fun _ hg => IsCancelSMul.eq_one_of_smul hg Subgroup.eq_bot_iff_forall _

@[to_additive]
/--
lemma `_root_.isCancelSMul_iff_stabilizer_eq_bot` / 引理 `_root_.isCancelSMul_iff_stabilizer_eq_bot`

English:
lemma _root_.isCancelSMul_iff_stabilizer_eq_bot
  proof: by
  simp [isCancelSMul_iff_eq_one_of_smul_eq, Subgroup.eq_bot_iff_forall, forall_comm (α := G)]

中文:
引理 _root_.isCancelSMul_iff_stabilizer_eq_bot
  证明: by
  simp [isCancelSMul_iff_eq_one_of_smul_eq, Subgroup.eq_bot_iff_forall, forall_comm (α := G)]

Depends on / 依赖: Subgroup, Subgroup.eq_bot_iff_forall, eq_bot_iff_forall, forall_comm, isCancelSMul_iff_eq_one_of_smul_eq
-/
lemma _root_.isCancelSMul_iff_stabilizer_eq_bot :
    IsCancelSMul G α ↔ (forall a : α, stabilizer G a = ⊥) := by
  simp [isCancelSMul_iff_eq_one_of_smul_eq, Subgroup.eq_bot_iff_forall, forall_comm (α := G)]

/-- If the stabilizer of `a` is `S`, then the stabilizer of `g • a` is `gSg⁻¹`. -/
@[to_additive /-- If the stabilizer of `a` is `S`, then the stabilizer of `g +ᵥ a` is `g+S-g`. -/]
/--
theorem `stabilizer_smul_eq_stabilizer_map_conj` / 定理 `stabilizer_smul_eq_stabilizer_map_conj`

English:
theorem stabilizer_smul_eq_stabilizer_map_conj
  given: (g : G) (a : α)
  proof: by
  ext h
  rw [mem_stabilizer_iff]; rw [← smul_left_cancel_iff g⁻¹]; rw [smul_smul]; rw [smul_smul]; rw [smul_smul]; rw [inv_mul_cancel]; rw [one_smul]; rw [← mem_stabilizer_iff]; rw [Subgroup.mem_map_equiv]; rw [MulAut.conj_symm_apply]

中文:
定理 stabilizer_smul_eq_stabilizer_map_conj
  条件: (g : G) (a : α)
  证明: by
  ext h
  rw [mem_stabilizer_iff]; rw [← smul_left_cancel_iff g⁻¹]; rw [smul_smul]; rw [smul_smul]; rw [smul_smul]; rw [inv_mul_cancel]; rw [one_smul]; rw [← mem_stabilizer_iff]; rw [Subgroup.mem_map_equiv]; rw [MulAut.conj_symm_apply]

Depends on / 依赖: MulAut, MulAut.conj_symm_apply, Subgroup, Subgroup.mem_map_equiv, conj_symm_apply, inv_mul_cancel, mem_map_equiv, mem_stabilizer_iff, one_smul, smul_left_cancel_iff, smul_smul
-/
theorem stabilizer_smul_eq_stabilizer_map_conj (g : G) (a : α) :
    stabilizer G (g • a) = (stabilizer G a).map (MulAut.conj g).toMonoidHom := by
  ext h
  rw [mem_stabilizer_iff]; rw [← smul_left_cancel_iff g⁻¹]; rw [smul_smul]; rw [smul_smul]; rw [smul_smul]; rw [inv_mul_cancel]; rw [one_smul]; rw [← mem_stabilizer_iff]; rw [Subgroup.mem_map_equiv]; rw [MulAut.conj_symm_apply]

variable {g h k : G} {a b c : α}

/-- The natural group equivalence between the stabilizers of two elements in the same orbit. -/
@[to_additive /-- The isomorphism between the stabilizers of two elements in the same orbit. -/]
/--
Definition of `stabilizerEquivStabilizer` / `stabilizerEquivStabilizer` 的定义

English:
definition stabilizerEquivStabilizer
  signature: (hg : b = g • a)
  body: ((MulAut.conj g).subgroupMap (stabilizer G a)).trans
    (MulEquiv.subgroupCongr (by
      rw [hg]; rw [stabilizer_smul_eq_stabilizer_map_conj g a]; rw [← MulEquiv.toMonoidHom_eq_coe]))

@[to_additive]

中文:
定义 stabilizerEquivStabilizer
  签名: (hg : b = g • a)
  定义体: ((MulAut.conj g).subgroupMap (stabilizer G a)).trans
    (MulEquiv.subgroupCongr (by
      rw [hg]; rw [stabilizer_smul_eq_stabilizer_map_conj g a]; rw [← MulEquiv.toMonoidHom_eq_coe]))

@[to_additive]

Depends on / 依赖: MulAut, MulAut.conj, MulEquiv, MulEquiv.subgroupCongr, MulEquiv.toMonoidHom_eq_coe, stabilizer, stabilizer_smul_eq_stabilizer_map_conj, subgroupCongr, subgroupMap, toMonoidHom_eq_coe
-/
def stabilizerEquivStabilizer (hg : b = g • a) : stabilizer G a ≃* stabilizer G b :=
  ((MulAut.conj g).subgroupMap (stabilizer G a)).trans
    (MulEquiv.subgroupCongr (by
      rw [hg]; rw [stabilizer_smul_eq_stabilizer_map_conj g a]; rw [← MulEquiv.toMonoidHom_eq_coe]))

@[to_additive]
/--
theorem `stabilizerEquivStabilizer_apply` / 定理 `stabilizerEquivStabilizer_apply`

English:
theorem stabilizerEquivStabilizer_apply
  given: (hg : b = g • a) (x : stabilizer G a)
  proof: by
  simp [stabilizerEquivStabilizer]

@[to_additive]

中文:
定理 stabilizerEquivStabilizer_apply
  条件: (hg : b = g • a) (x : stabilizer G a)
  证明: by
  simp [stabilizerEquivStabilizer]

@[to_additive]

Depends on / 依赖: stabilizerEquivStabilizer
-/
theorem stabilizerEquivStabilizer_apply (hg : b = g • a) (x : stabilizer G a) :
    stabilizerEquivStabilizer hg x = MulAut.conj g x := by
  simp [stabilizerEquivStabilizer]

@[to_additive]
/--
theorem `stabilizerEquivStabilizer_symm_apply` / 定理 `stabilizerEquivStabilizer_symm_apply`

English:
theorem stabilizerEquivStabilizer_symm_apply
  given: (hg : b = g • a) (x : stabilizer G b)
  proof: by
  simp [stabilizerEquivStabilizer]

@[to_additive]

中文:
定理 stabilizerEquivStabilizer_symm_apply
  条件: (hg : b = g • a) (x : stabilizer G b)
  证明: by
  simp [stabilizerEquivStabilizer]

@[to_additive]

Depends on / 依赖: stabilizerEquivStabilizer
-/
theorem stabilizerEquivStabilizer_symm_apply (hg : b = g • a) (x : stabilizer G b) :
    (stabilizerEquivStabilizer hg).symm x = MulAut.conj g⁻¹ x := by
  simp [stabilizerEquivStabilizer]

@[to_additive]
/--
theorem `stabilizerEquivStabilizer_trans` / 定理 `stabilizerEquivStabilizer_trans`

English:
theorem stabilizerEquivStabilizer_trans
  statement: (hg : b = g • a) (hh : c = h • b) (hk : c = k • a)
  proof: by
  ext; simp [stabilizerEquivStabilizer_apply, H]

@[to_additive]

中文:
定理 stabilizerEquivStabilizer_trans
  结论: (hg : b = g • a) (hh : c = h • b) (hk : c = k • a)
  证明: by
  ext; simp [stabilizerEquivStabilizer_apply, H]

@[to_additive]

Depends on / 依赖: stabilizerEquivStabilizer_apply
-/
theorem stabilizerEquivStabilizer_trans (hg : b = g • a) (hh : c = h • b) (hk : c = k • a)
    (H : k = h * g) :
    (stabilizerEquivStabilizer hg).trans (stabilizerEquivStabilizer hh) =
      stabilizerEquivStabilizer hk := by
  ext; simp [stabilizerEquivStabilizer_apply, H]

@[to_additive]
/--
theorem `stabilizerEquivStabilizer_one` / 定理 `stabilizerEquivStabilizer_one`

English:
theorem stabilizerEquivStabilizer_one
  proof: by
  ext; simp [stabilizerEquivStabilizer_apply]

@[to_additive]

中文:
定理 stabilizerEquivStabilizer_one
  证明: by
  ext; simp [stabilizerEquivStabilizer_apply]

@[to_additive]

Depends on / 依赖: stabilizerEquivStabilizer_apply
-/
theorem stabilizerEquivStabilizer_one :
    stabilizerEquivStabilizer (one_smul G a).symm = MulEquiv.refl (stabilizer G a) := by
  ext; simp [stabilizerEquivStabilizer_apply]

@[to_additive]
/--
theorem `stabilizerEquivStabilizer_symm` / 定理 `stabilizerEquivStabilizer_symm`

English:
theorem stabilizerEquivStabilizer_symm
  given: (hg : b = g • a)
  proof: by
  ext x; simp [stabilizerEquivStabilizer]

@[to_additive]

中文:
定理 stabilizerEquivStabilizer_symm
  条件: (hg : b = g • a)
  证明: by
  ext x; simp [stabilizerEquivStabilizer]

@[to_additive]

Depends on / 依赖: stabilizerEquivStabilizer
-/
theorem stabilizerEquivStabilizer_symm (hg : b = g • a) :
    (stabilizerEquivStabilizer hg).symm =
      stabilizerEquivStabilizer (eq_inv_smul_iff.mpr hg.symm) := by
  ext x; simp [stabilizerEquivStabilizer]

@[to_additive]
/--
theorem `stabilizerEquivStabilizer_inv` / 定理 `stabilizerEquivStabilizer_inv`

English:
theorem stabilizerEquivStabilizer_inv
  given: (hg : b = g⁻¹ • a)
  proof: by
  ext; simp [stabilizerEquivStabilizer]

中文:
定理 stabilizerEquivStabilizer_inv
  条件: (hg : b = g⁻¹ • a)
  证明: by
  ext; simp [stabilizerEquivStabilizer]

Depends on / 依赖: stabilizerEquivStabilizer
-/
theorem stabilizerEquivStabilizer_inv (hg : b = g⁻¹ • a) :
    stabilizerEquivStabilizer hg =
      (stabilizerEquivStabilizer (inv_smul_eq_iff.mp hg.symm)).symm := by
  ext; simp [stabilizerEquivStabilizer]

/-- A isomorphism between the stabilizers of two elements in the same orbit. -/
@[to_additive /-- A isomorphism between the stabilizers of two elements in the same orbit. -/]
/--
Definition of `stabilizerEquivStabilizerOfOrbitRel` / `stabilizerEquivStabilizerOfOrbitRel` 的定义

English:
definition stabilizerEquivStabilizerOfOrbitRel
  signature: (h : orbitRel G α a b)
  body: (stabilizerEquivStabilizer (Classical.choose_spec h).symm).symm

中文:
定义 stabilizerEquivStabilizerOfOrbitRel
  签名: (h : orbitRel G α a b)
  定义体: (stabilizerEquivStabilizer (Classical.choose_spec h).symm).symm

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, stabilizerEquivStabilizer
-/
noncomputable def stabilizerEquivStabilizerOfOrbitRel (h : orbitRel G α a b) :
    stabilizer G a ≃* stabilizer G b :=
  (stabilizerEquivStabilizer (Classical.choose_spec h).symm).symm

end Stabilizer

end MulAction

namespace AddAction

@[deprecated (since := "2026-05-26")] alias stabilizer_vadd_eq_stabilizer_map_conj :=
  stabilizer_vadd_eq_stabilizer_map_addConj

end AddAction

/--
theorem `Equiv.swap_mem_stabilizer` / 定理 `Equiv.swap_mem_stabilizer`

English:
theorem Equiv.swap_mem_stabilizer
  given: {α : Type*} [DecidableEq α] {S : Set α} {a b : α}
  proof: by
  rw [MulAction.mem_stabilizer_iff]; rw [Set.ext_iff]; rw [← swap_inv]
  simp_rw [Set.mem_inv_smul_set_iff, Perm.smul_def, swap_apply_def]
  exact ⟨fun h => by simpa [Iff.comm] using h a, by intros; split_ifs <;> simp [*]⟩

中文:
定理 等价.swap_mem_stabilizer
  条件: {α : 类型} [DecidableEq α] {S : 集合 α} {a b : α}
  证明: by
  rw [MulAction.mem_stabilizer_iff]; rw [Set.ext_iff]; rw [← swap_inv]
  simp_rw [Set.mem_inv_smul_set_iff, Perm.smul_def, swap_apply_def]
  exact ⟨fun h => by simpa [Iff.comm] using h a, by intros; split_ifs <;> simp [*]⟩

Depends on / 依赖: Iff.comm, MulAction, MulAction.mem_stabilizer_iff, Perm.smul_def, Set.ext_iff, Set.mem_inv_smul_set_iff, ext_iff, intros, mem_inv_smul_set_iff, mem_stabilizer_iff, simp_rw, smul_def, split_ifs, swap_apply_def, swap_inv
-/
theorem Equiv.swap_mem_stabilizer {α : Type*} [DecidableEq α] {S : Set α} {a b : α} :
    Equiv.swap a b in MulAction.stabilizer (Equiv.Perm α) S ↔ (a in S ↔ b in S) := by
  rw [MulAction.mem_stabilizer_iff]; rw [Set.ext_iff]; rw [← swap_inv]
  simp_rw [Set.mem_inv_smul_set_iff, Perm.smul_def, swap_apply_def]
  exact ⟨fun h => by simpa [Iff.comm] using h a, by intros; split_ifs <;> simp [*]⟩

namespace MulAction

variable {G : Type*} [Group G] {α : Type*} [MulAction G α]

/-- To prove inclusion of a *subgroup* in a stabilizer, it is enough to prove inclusions. -/
@[to_additive
  /-- To prove inclusion of a *subgroup* in a stabilizer, it is enough to prove inclusions. -/]
/--
theorem `le_stabilizer_iff_smul_le` / 定理 `le_stabilizer_iff_smul_le`

English:
theorem le_stabilizer_iff_smul_le
  given: (s : Set α) (H : Subgroup G)
  proof: by
  constructor
  · intro hyp g hg
    apply Eq.subset
    rw [← mem_stabilizer_iff]
    exact hyp hg
  · intro hyp g hg
    rw [mem_stabilizer_iff]
    apply subset_antisymm (hyp g hg)
    intro x hx
    use g⁻¹ • x
    constructor
    · apply hyp g⁻¹ (inv_mem hg)
      simp only [Set.smul_mem_smu

中文:
定理 le_stabilizer_iff_smul_le
  条件: (s : 集合 α) (H : 子群 G)
  证明: by
  constructor
  · intro hyp g hg
    apply Eq.subset
    rw [← mem_stabilizer_iff]
    exact hyp hg
  · intro hyp g hg
    rw [mem_stabilizer_iff]
    apply subset_antisymm (hyp g hg)
    intro x hx
    use g⁻¹ • x
    constructor
    · apply hyp g⁻¹ (inv_mem hg)
      simp only [Set.smul_mem_smu

Depends on / 依赖: Eq.subset, Set.smul_mem_smul_set_iff, inv_mem, mem_stabilizer_iff, smul_inv_smul, smul_mem_smul_set_iff, subset, subset_antisymm
-/
theorem le_stabilizer_iff_smul_le (s : Set α) (H : Subgroup G) :
    H <= stabilizer G s ↔ forall g in H, g • s subseteq s := by
  constructor
  · intro hyp g hg
    apply Eq.subset
    rw [← mem_stabilizer_iff]
    exact hyp hg
  · intro hyp g hg
    rw [mem_stabilizer_iff]
    apply subset_antisymm (hyp g hg)
    intro x hx
    use g⁻¹ • x
    constructor
    · apply hyp g⁻¹ (inv_mem hg)
      simp only [Set.smul_mem_smul_set_iff, hx]
    · simp only [smul_inv_smul]

end MulAction

section
variable (R M : Type*) [Ring R] [IsDomain R] [AddCommGroup M] [Module R M] [IsTorsionFree R M]

variable {M} in
/--
lemma `Module.stabilizer_units_eq_bot_of_ne_zero` / 引理 `Module.stabilizer_units_eq_bot_of_ne_zero`

English:
lemma Module.stabilizer_units_eq_bot_of_ne_zero
  given: {x : M} (hx : x != 0)
  proof: by
  rw [eq_bot_iff]
  intro g (hg : g.val • x = x)
  ext
  rw [← sub_eq_zero]; rw [← smul_eq_zero_iff_left hx]; rw [Units.val_one]; rw [sub_smul]; rw [hg]; rw [one_smul]; rw [sub_self]

中文:
引理 模.stabilizer_units_eq_bot_of_ne_zero
  条件: {x : M} (hx : x != 0)
  证明: by
  rw [eq_bot_iff]
  intro g (hg : g.val • x = x)
  ext
  rw [← sub_eq_zero]; rw [← smul_eq_zero_iff_left hx]; rw [Units.val_one]; rw [sub_smul]; rw [hg]; rw [one_smul]; rw [sub_self]

Depends on / 依赖: Units.val_one, eq_bot_iff, g.val, one_smul, smul_eq_zero_iff_left, sub_eq_zero, sub_self, sub_smul, val_one
-/
lemma Module.stabilizer_units_eq_bot_of_ne_zero {x : M} (hx : x != 0) :
    MulAction.stabilizer Rˣ x = ⊥ := by
  rw [eq_bot_iff]
  intro g (hg : g.val • x = x)
  ext
  rw [← sub_eq_zero]; rw [← smul_eq_zero_iff_left hx]; rw [Units.val_one]; rw [sub_smul]; rw [hg]; rw [one_smul]; rw [sub_self]

end

/--
lemma `Multiplicative.mulAction_orbit` / 引理 `Multiplicative.mulAction_orbit`

English:
lemma Multiplicative.mulAction_orbit
  given: {α β : Type*} [VAdd α β] (b : β)
  proof: rfl

中文:
引理 Multiplicative.mulAction_orbit
  条件: {α β : 类型} [向量加法 α β] (b : β)
  证明: rfl
-/
@[simp] lemma Multiplicative.mulAction_orbit {α β : Type*} [VAdd α β] (b : β) :
    MulAction.orbit (Multiplicative α) b = AddAction.orbit α b :=
  rfl

/--
lemma `Additive.mulAction_orbit` / 引理 `Additive.mulAction_orbit`

English:
lemma Additive.mulAction_orbit
  given: {α β : Type*} [SMul α β] (b : β)
  proof: rfl

中文:
引理 加性.mulAction_orbit
  条件: {α β : 类型} [标量乘法 α β] (b : β)
  证明: rfl
-/
@[simp] lemma Additive.mulAction_orbit {α β : Type*} [SMul α β] (b : β) :
    AddAction.orbit (Additive α) b = MulAction.orbit α b :=
  rfl
