/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer
public import Mathlib.GroupTheory.GroupAction.Transitive
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.Tactic.Group

/-!
# SubMulActions on complements of invariant subsets

Given a `MulAction` of `G` on `α` and `s : Set α`,

- `SubMulAction.ofFixingSubgroup` is the action
  of `FixingSubgroup G s` on the complement `sᶜ` of `s`.

- We define equivariant maps that relate various of these `SubMulAction`s
  and permit to manipulate them in a relatively smooth way:

  * `SubMulAction.ofFixingSubgroup_equivariantMap`:
    the identity map from `sᶜ` to `α`, as an equivariant map
    relative to the injection of `FixingSubgroup G s` into `G`.

  * `SubMulAction.fixingSubgroupInsertEquiv M a s`: the
    multiplicative equivalence between `fixingSubgroup M (insert a s)`
    and `fixingSubgroup (stabilizer M a) s`

  * `SubMulAction.ofFixingSubgroup_insert_map`: the equivariant
    map between `SubMulAction.ofFixingSubgroup M (Set.insert a s)`
    and `SubMulAction.ofFixingSubgroup (MulAction.stabilizer M a) s`.

  * `SubMulAction.fixingSubgroupEquivFixingSubgroup`:
    the multiplicative equivalence between `SubMulAction.ofFixingSubgroup M s`
    and `SubMulAction.ofFixingSubgroup M t` induced by `g : M`
    such that `g • t = s`.

  * `SubMulAction.conjMap_ofFixingSubgroup`:
    the equivariant map between `SubMulAction.ofFixingSubgroup M t`
    and `SubMulAction.ofFixingSubgroup M s`
    induced by `g : M` such that `g • t = s`.

  * `SubMulAction.ofFixingSubgroup_of_inclusion`:
    the identity from `SubMulAction.ofFixingSubgroup M s`
    to `SubMulAction.ofFixingSubgroup M t`, when `t ⊆ s`,
    as an equivariant map.

  * `SubMulAction.ofFixingSubgroup_of_singleton`:
    the identity map from `SubMulAction.ofStabilizer M a`
    to `SubMulAction.ofFixingSubgroup M {a}`.

  * `SubMulAction.ofFixingSubgroup_of_eq`:
    the identity from `SubMulAction.ofFixingSubgroup M s`
    to `SubMulAction.ofFixingSubgroup M t`, when `s = t`,
    as an equivariant map.

  * `SubMulAction.ofFixingSubgroup.append`: appends
    an enumeration of `ofFixingSubgroup M s` at the end
    of an enumeration of `s`, as an equivariant map.

-/

@[expose] public section

open scoped Pointwise

open MulAction Function

namespace SubMulAction

variable (M : Type*) {α : Type*} [Group M] [MulAction M α] (s : Set α)

/-- The `SubMulAction` of `fixingSubgroup M s` on the complement of `s`. -/
@[to_additive /-- The `SubAddAction` of `fixingAddSubgroup M s` on the complement of `s`. -/]
/--
Definition of `ofFixingSubgroup` / `ofFixingSubgroup` 的定义

English:
definition ofFixingSubgroup
  signature: : SubMulAction (fixingSubgroup M s) α where
  body: sᶜ
  smul_mem' := fun ⟨c, hc⟩ x => by
    rw [← Subgroup.inv_mem_iff] at hc
    simp only [Set.mem_compl_iff, not_imp_not]
    intro hcx
    rwa [← one_smul M x, ← inv_mul_cancel c, mul_smul, (mem_fixingSubgroup_iff M).mp hc (c • x) hcx]

@[to_additive (attr := simp)]

中文:
定义 ofFixingSubgroup
  签名: : SubMul作用 (fixingSubgroup M s) α where
  定义体: sᶜ
  smul_mem' := fun ⟨c, hc⟩ x => by
    rw [← Subgroup.inv_mem_iff] at hc
    simp only [Set.mem_compl_iff, not_imp_not]
    intro hcx
    rwa [← one_smul M x, ← inv_mul_cancel c, mul_smul, (mem_fixingSubgroup_iff M).mp hc (c • x) hcx]

@[to_additive (attr := simp)]
-/
def ofFixingSubgroup : SubMulAction (fixingSubgroup M s) α where
  carrier := sᶜ
  smul_mem' := fun ⟨c, hc⟩ x => by
    rw [← Subgroup.inv_mem_iff] at hc
    simp only [Set.mem_compl_iff, not_imp_not]
    intro hcx
    rwa [← one_smul M x, ← inv_mul_cancel c, mul_smul, (mem_fixingSubgroup_iff M).mp hc (c • x) hcx]

@[to_additive (attr := simp)]
/--
theorem `ofFixingSubgroup_carrier` / 定理 `ofFixingSubgroup_carrier`

English:
theorem ofFixingSubgroup_carrier
  proof: rfl

中文:
定理 ofFixingSubgroup_carrier
  证明: rfl
-/
theorem ofFixingSubgroup_carrier :
    (ofFixingSubgroup M s).carrier = sᶜ := rfl

variable {s}

@[to_additive]
/--
theorem `mem_ofFixingSubgroup_iff` / 定理 `mem_ofFixingSubgroup_iff`

English:
theorem mem_ofFixingSubgroup_iff
  given: {x : α}
  proof: Iff.rfl

中文:
定理 mem_ofFixingSubgroup_iff
  条件: {x : α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_ofFixingSubgroup_iff {x : α} :
    x in ofFixingSubgroup M s ↔ x ∉ s :=
  Iff.rfl

variable {M}

@[to_additive]
/--
theorem `not_mem_of_mem_ofFixingSubgroup` / 定理 `not_mem_of_mem_ofFixingSubgroup`

English:
theorem not_mem_of_mem_ofFixingSubgroup
  given: (x : ofFixingSubgroup M s)
  proof: x.prop

@[to_additive]

中文:
定理 not_mem_of_mem_ofFixingSubgroup
  条件: (x : ofFixingSubgroup M s)
  证明: x.prop

@[to_additive]

Depends on / 依赖: x.prop
-/
theorem not_mem_of_mem_ofFixingSubgroup (x : ofFixingSubgroup M s) :
    ↑x ∉ s := x.prop

@[to_additive]
/--
theorem `disjoint_val_image` / 定理 `disjoint_val_image`

English:
theorem disjoint_val_image
  given: {t : Set (ofFixingSubgroup M s)}
  proof: by
  rw [Set.disjoint_iff]
  rintro a ⟨hbs, ⟨b, _, rfl⟩⟩; exact (b.prop hbs).elim

中文:
定理 disjoint_val_image
  条件: {t : 集合 (ofFixingSubgroup M s)}
  证明: by
  rw [Set.disjoint_iff]
  rintro a ⟨hbs, ⟨b, _, rfl⟩⟩; exact (b.prop hbs).elim

Depends on / 依赖: Set.disjoint_iff, b.prop, disjoint_iff
-/
theorem disjoint_val_image {t : Set (ofFixingSubgroup M s)} :
    Disjoint s (Subtype.val '' t) := by
  rw [Set.disjoint_iff]
  rintro a ⟨hbs, ⟨b, _, rfl⟩⟩; exact (b.prop hbs).elim

variable (M s) in
/-- The identity map of the `SubMulAction` of the `fixingSubgroup`
into the ambient set, as an equivariant map. -/
@[to_additive
/-- The identity map of the `SubAddAction` of the `fixingAddSubgroup`
into the ambient set, as an equivariant map. -/]
/--
Definition of `ofFixingSubgroup_equivariantMap` / `ofFixingSubgroup_equivariantMap` 的定义

English:
definition ofFixingSubgroup_equivariantMap
  signature: :
  body: x
  map_smul' _ _ := rfl

@[to_additive]

中文:
定义 ofFixingSubgroup_equivariantMap
  签名: :
  定义体: x
  map_smul' _ _ := rfl

@[to_additive]
-/
def ofFixingSubgroup_equivariantMap :
    ofFixingSubgroup M s ->ₑ[(fixingSubgroup M s).subtype] α where
  toFun x := x
  map_smul' _ _ := rfl

@[to_additive]
/--
theorem `ofFixingSubgroup_equivariantMap_injective` / 定理 `ofFixingSubgroup_equivariantMap_injective`

English:
theorem ofFixingSubgroup_equivariantMap_injective
  proof: by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  simpa [Subtype.mk.injEq] using! hxy

中文:
定理 ofFixingSubgroup_equivariantMap_injective
  证明: by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  simpa [Subtype.mk.injEq] using! hxy

Depends on / 依赖: Subtype, Subtype.mk.injEq
-/
theorem ofFixingSubgroup_equivariantMap_injective :
    Injective (ofFixingSubgroup_equivariantMap M s) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  simpa [Subtype.mk.injEq] using! hxy

section Comparisons

section Empty

@[to_additive]
/--
theorem `ofFixingSubgroupEmpty_equivariantMap_bijective` / 定理 `ofFixingSubgroupEmpty_equivariantMap_bijective`

English:
theorem ofFixingSubgroupEmpty_equivariantMap_bijective
  proof: by
  refine ⟨ofFixingSubgroup_equivariantMap_injective, fun x => ?_⟩
  exact ⟨⟨x, (mem_ofFixingSubgroup_iff M).mp (Set.notMem_empty x)⟩, rfl⟩

@[to_additive]

中文:
定理 ofFixingSubgroupEmpty_equivariantMap_bijective
  证明: by
  refine ⟨ofFixingSubgroup_equivariantMap_injective, fun x => ?_⟩
  exact ⟨⟨x, (mem_ofFixingSubgroup_iff M).mp (Set.notMem_empty x)⟩, rfl⟩

@[to_additive]

Depends on / 依赖: Set.notMem_empty, mem_ofFixingSubgroup_iff, notMem_empty, ofFixingSubgroup_equivariantMap_injective
-/
theorem ofFixingSubgroupEmpty_equivariantMap_bijective :
    Bijective (ofFixingSubgroup_equivariantMap M (∅ : Set α)) := by
  refine ⟨ofFixingSubgroup_equivariantMap_injective, fun x => ?_⟩
  exact ⟨⟨x, (mem_ofFixingSubgroup_iff M).mp (Set.notMem_empty x)⟩, rfl⟩

@[to_additive]
/--
theorem `of_fixingSubgroupEmpty_mapScalars_surjective` / 定理 `of_fixingSubgroupEmpty_mapScalars_surjective`

English:
theorem of_fixingSubgroupEmpty_mapScalars_surjective
  proof: fun g => ⟨⟨g, by simp⟩, rfl⟩

中文:
定理 of_fixingSubgroupEmpty_mapScalars_surjective
  证明: fun g => ⟨⟨g, by simp⟩, rfl⟩
-/
theorem of_fixingSubgroupEmpty_mapScalars_surjective :
    Surjective (fixingSubgroup M (∅ : Set α)).subtype :=
  fun g => ⟨⟨g, by simp⟩, rfl⟩

end Empty

section FixingSubgroupInsert

@[to_additive]
/--
theorem `mem_fixingSubgroup_insert_iff` / 定理 `mem_fixingSubgroup_insert_iff`

English:
theorem mem_fixingSubgroup_insert_iff
  given: {a : α} {s : Set α} {m : M}
  proof: by
  simp [mem_fixingSubgroup_iff]

@[to_additive]

中文:
定理 mem_fixingSubgroup_insert_iff
  条件: {a : α} {s : 集合 α} {m : M}
  证明: by
  simp [mem_fixingSubgroup_iff]

@[to_additive]

Depends on / 依赖: mem_fixingSubgroup_iff
-/
theorem mem_fixingSubgroup_insert_iff {a : α} {s : Set α} {m : M} :
    m in fixingSubgroup M (insert a s) ↔ m • a = a ∧ m in fixingSubgroup M s := by
  simp [mem_fixingSubgroup_iff]

@[to_additive]
/--
theorem `fixingSubgroup_of_insert` / 定理 `fixingSubgroup_of_insert`

English:
theorem fixingSubgroup_of_insert
  given: (a : α) (s : Set (ofStabilizer M a))
  proof: by
  ext m
  simp [mem_fixingSubgroup_iff, mem_ofStabilizer_iff, subgroup_smul_def, and_comm]

@[to_additive]

中文:
定理 fixingSubgroup_of_insert
  条件: (a : α) (s : 集合 (ofStabilizer M a))
  证明: by
  ext m
  simp [mem_fixingSubgroup_iff, mem_ofStabilizer_iff, subgroup_smul_def, and_comm]

@[to_additive]

Depends on / 依赖: and_comm, mem_fixingSubgroup_iff, mem_ofStabilizer_iff, subgroup_smul_def
-/
theorem fixingSubgroup_of_insert (a : α) (s : Set (ofStabilizer M a)) :
    fixingSubgroup M (insert a ((fun x => x.val) '' s)) =
      (fixingSubgroup (↥(stabilizer M a)) s).map (stabilizer M a).subtype := by
  ext m
  simp [mem_fixingSubgroup_iff, mem_ofStabilizer_iff, subgroup_smul_def, and_comm]

@[to_additive]
/--
theorem `mem_ofFixingSubgroup_insert_iff` / 定理 `mem_ofFixingSubgroup_insert_iff`

English:
theorem mem_ofFixingSubgroup_insert_iff
  given: {a : α} {s : Set (ofStabilizer M a)} {x : α}
  proof: by
  grind [mem_ofFixingSubgroup_iff, mem_ofStabilizer_iff]

中文:
定理 mem_ofFixingSubgroup_insert_iff
  条件: {a : α} {s : 集合 (ofStabilizer M a)} {x : α}
  证明: by
  grind [mem_ofFixingSubgroup_iff, mem_ofStabilizer_iff]

Depends on / 依赖: mem_ofFixingSubgroup_iff, mem_ofStabilizer_iff
-/
theorem mem_ofFixingSubgroup_insert_iff {a : α} {s : Set (ofStabilizer M a)} {x : α} :
    x in ofFixingSubgroup M (insert a ((fun x => x.val) '' s)) ↔
      exists (hx : x in ofStabilizer M a),
        (⟨x, hx⟩ : ofStabilizer M a) in ofFixingSubgroup (stabilizer M a) s := by
  grind [mem_ofFixingSubgroup_iff, mem_ofStabilizer_iff]

/-- The natural group isomorphism between fixing subgroups. -/
@[to_additive /-- The natural additive group isomorphism between fixing additive subgroups. -/]
/--
Definition of `fixingSubgroupInsertEquiv` / `fixingSubgroupInsertEquiv` 的定义

English:
definition fixingSubgroupInsertEquiv
  signature: (a : α) (s : Set (ofStabilizer M a))
  body: ⟨⟨(m : M), (mem_fixingSubgroup_iff M).mp m.prop a (Set.mem_insert _ _)⟩,
      fun ⟨x, hx⟩ => by
        simp only [← SetLike.coe_eq_coe]
        refine (mem_fixingSubgroup_iff M).mp m.prop _ (Set.mem_insert_of_mem a ?_)
        exact ⟨⟨x, (SubMulAction.mem_ofStabilizer_iff M a).mp x.prop⟩, hx, rfl⟩

中文:
定义 fixingSubgroupInsertEquiv
  签名: (a : α) (s : 集合 (ofStabilizer M a))
  定义体: ⟨⟨(m : M), (mem_fixingSubgroup_iff M).mp m.prop a (Set.mem_insert _ _)⟩,
      fun ⟨x, hx⟩ => by
        simp only [← SetLike.coe_eq_coe]
        refine (mem_fixingSubgroup_iff M).mp m.prop _ (Set.mem_insert_of_mem a ?_)
        exact ⟨⟨x, (SubMulAction.mem_ofStabilizer_iff M a).mp x.prop⟩, hx, rfl⟩

Depends on / 依赖: Set.mem_insert, m.prop, mem_fixingSubgroup_iff, mem_insert
-/
def fixingSubgroupInsertEquiv (a : α) (s : Set (ofStabilizer M a)) :
    fixingSubgroup M (insert a (Subtype.val '' s)) ≃* fixingSubgroup (stabilizer M a) s where
  toFun m := ⟨⟨(m : M), (mem_fixingSubgroup_iff M).mp m.prop a (Set.mem_insert _ _)⟩,
      fun ⟨x, hx⟩ => by
        simp only [← SetLike.coe_eq_coe]
        refine (mem_fixingSubgroup_iff M).mp m.prop _ (Set.mem_insert_of_mem a ?_)
        exact ⟨⟨x, (SubMulAction.mem_ofStabilizer_iff M a).mp x.prop⟩, hx, rfl⟩⟩
  map_mul' _ _ := by simp [← Subtype.coe_inj]
  invFun m := ⟨m, by simp [fixingSubgroup_of_insert]⟩
  left_inv _ := by simp
  right_inv _ := by simp

/-- The identity map of fixing subgroup of stabilizer
into the fixing subgroup of the extended set, as an equivariant map. -/
@[to_additive /-- The identity map of fixing additive subgroup of stabilizer
into the fixing additive subgroup of the extended set, as an equivariant map. -/]
/--
Definition of `ofFixingSubgroup_insert_map` / `ofFixingSubgroup_insert_map` 的定义

English:
definition ofFixingSubgroup_insert_map
  signature: (a : α) (s : Set (ofStabilizer M a))
  body: by
    choose hx hx' using (mem_ofFixingSubgroup_insert_iff.mp x.prop)
    exact ⟨_, hx'⟩
  map_smul' _ _ := rfl

@[to_additive (attr := simp)]

中文:
定义 ofFixingSubgroup_insert_map
  签名: (a : α) (s : 集合 (ofStabilizer M a))
  定义体: by
    choose hx hx' using (mem_ofFixingSubgroup_insert_iff.mp x.prop)
    exact ⟨_, hx'⟩
  map_smul' _ _ := rfl

@[to_additive (attr := simp)]

Depends on / 依赖: map_smul, mem_ofFixingSubgroup_insert_iff, mem_ofFixingSubgroup_insert_iff.mp, x.prop
-/
def ofFixingSubgroup_insert_map (a : α) (s : Set (ofStabilizer M a)) :
    ofFixingSubgroup M (insert a (Subtype.val '' s))
      ->ₑ[fixingSubgroupInsertEquiv a s]
        ofFixingSubgroup (stabilizer M a) s where
  toFun x := by
    choose hx hx' using (mem_ofFixingSubgroup_insert_iff.mp x.prop)
    exact ⟨_, hx'⟩
  map_smul' _ _ := rfl

@[to_additive (attr := simp)]
/--
theorem `ofFixingSubgroup_insert_map_apply` / 定理 `ofFixingSubgroup_insert_map_apply`

English:
theorem ofFixingSubgroup_insert_map_apply
  statement: {a : α} {s : Set (ofStabilizer M a)}
  proof: rfl

@[to_additive]

中文:
定理 ofFixingSubgroup_insert_map_apply
  结论: {a : α} {s : 集合 (ofStabilizer M a)}
  证明: rfl

@[to_additive]
-/
theorem ofFixingSubgroup_insert_map_apply {a : α} {s : Set (ofStabilizer M a)}
    {x : α} (hx : x in ofFixingSubgroup M (insert a (Subtype.val '' s))) :
    (ofFixingSubgroup_insert_map a s) ⟨x, hx⟩ = x :=
  rfl

@[to_additive]
/--
theorem `ofFixingSubgroup_insert_map_bijective` / 定理 `ofFixingSubgroup_insert_map_bijective`

English:
theorem ofFixingSubgroup_insert_map_bijective
  given: {a : α} {s : Set (ofStabilizer M a)}
  proof: by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    simpa only [← Subtype.coe_inj, ofFixingSubgroup_insert_map_apply] using h
  · rintro ⟨⟨x, hx1⟩, hx2⟩
    exact ⟨⟨x, mem_ofFixingSubgroup_insert_iff.mpr ⟨hx1, hx2⟩⟩, rfl⟩

中文:
定理 ofFixingSubgroup_insert_map_bijective
  条件: {a : α} {s : 集合 (ofStabilizer M a)}
  证明: by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    simpa only [← Subtype.coe_inj, ofFixingSubgroup_insert_map_apply] using h
  · rintro ⟨⟨x, hx1⟩, hx2⟩
    exact ⟨⟨x, mem_ofFixingSubgroup_insert_iff.mpr ⟨hx1, hx2⟩⟩, rfl⟩

Depends on / 依赖: Subtype, Subtype.coe_inj, coe_inj, mem_ofFixingSubgroup_insert_iff, mem_ofFixingSubgroup_insert_iff.mpr, ofFixingSubgroup_insert_map_apply
-/
theorem ofFixingSubgroup_insert_map_bijective {a : α} {s : Set (ofStabilizer M a)} :
    Bijective (ofFixingSubgroup_insert_map a s) := by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    simpa only [← Subtype.coe_inj, ofFixingSubgroup_insert_map_apply] using h
  · rintro ⟨⟨x, hx1⟩, hx2⟩
    exact ⟨⟨x, mem_ofFixingSubgroup_insert_iff.mpr ⟨hx1, hx2⟩⟩, rfl⟩

end FixingSubgroupInsert

section FixingSubgroupConj

variable {s t : Set α} {g : M}

@[to_additive]
/--
theorem `_root_.Set.conj_mem_fixingSubgroup` / 定理 `_root_.Set.conj_mem_fixingSubgroup`

English:
theorem _root_.Set.conj_mem_fixingSubgroup
  given: (hg : g • t = s) {k : M} (hk : k in fixingSubgroup M t)
  proof: by
  simp only [mem_fixingSubgroup_iff] at hk ⊢
  intro y hy
  rw [MulAut.conj_apply]; rw [eq_comm]; rw [mul_smul]; rw [mul_smul]; rw [← inv_smul_eq_iff]; rw [eq_comm]
  apply hk
  rw [← Set.mem_smul_set_iff_inv_smul_mem]; rw [hg]
  exact hy

中文:
定理 _root_.集合.conj_mem_fixingSubgroup
  条件: (hg : g • t = s) {k : M} (hk : k in fixingSubgroup M t)
  证明: by
  simp only [mem_fixingSubgroup_iff] at hk ⊢
  intro y hy
  rw [MulAut.conj_apply]; rw [eq_comm]; rw [mul_smul]; rw [mul_smul]; rw [← inv_smul_eq_iff]; rw [eq_comm]
  apply hk
  rw [← Set.mem_smul_set_iff_inv_smul_mem]; rw [hg]
  exact hy

Depends on / 依赖: MulAut, MulAut.conj_apply, Set.mem_smul_set_iff_inv_smul_mem, conj_apply, eq_comm, inv_smul_eq_iff, mem_fixingSubgroup_iff, mem_smul_set_iff_inv_smul_mem, mul_smul
-/
theorem _root_.Set.conj_mem_fixingSubgroup (hg : g • t = s) {k : M} (hk : k in fixingSubgroup M t) :
    MulAut.conj g k in fixingSubgroup M s := by
  simp only [mem_fixingSubgroup_iff] at hk ⊢
  intro y hy
  rw [MulAut.conj_apply]; rw [eq_comm]; rw [mul_smul]; rw [mul_smul]; rw [← inv_smul_eq_iff]; rw [eq_comm]
  apply hk
  rw [← Set.mem_smul_set_iff_inv_smul_mem]; rw [hg]
  exact hy

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/--
theorem `fixingSubgroup_map_conj_eq` / 定理 `fixingSubgroup_map_conj_eq`

English:
theorem fixingSubgroup_map_conj_eq
  given: (hg : g • t = s)
  proof: by
  ext k
  simp only [MulEquiv.toMonoidHom_eq_coe, Subgroup.mem_map, MonoidHom.coe_coe]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact Set.conj_mem_fixingSubgroup hg hn
  · intro hk
    use MulAut.conj g⁻¹ k
    constructor
    · apply Set.conj_mem_fixingSubgroup _ hk
      rw [inv_smul_eq_iff]; 

中文:
定理 fixingSubgroup_map_conj_eq
  条件: (hg : g • t = s)
  证明: by
  ext k
  simp only [MulEquiv.toMonoidHom_eq_coe, Subgroup.mem_map, MonoidHom.coe_coe]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact Set.conj_mem_fixingSubgroup hg hn
  · intro hk
    use MulAut.conj g⁻¹ k
    constructor
    · apply Set.conj_mem_fixingSubgroup _ hk
      rw [inv_smul_eq_iff]; 

Depends on / 依赖: MonoidHom, MonoidHom.coe_coe, MulAut, MulAut.conj, MulEquiv, MulEquiv.toMonoidHom_eq_coe, Set.conj_mem_fixingSubgroup, Subgroup, Subgroup.mem_map, coe_coe, conj_mem_fixingSubgroup, inv_smul_eq_iff, mem_map, toMonoidHom_eq_coe
-/
theorem fixingSubgroup_map_conj_eq (hg : g • t = s) :
    (fixingSubgroup M t).map (MulAut.conj g).toMonoidHom = fixingSubgroup M s := by
  ext k
  simp only [MulEquiv.toMonoidHom_eq_coe, Subgroup.mem_map, MonoidHom.coe_coe]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact Set.conj_mem_fixingSubgroup hg hn
  · intro hk
    use MulAut.conj g⁻¹ k
    constructor
    · apply Set.conj_mem_fixingSubgroup _ hk
      rw [inv_smul_eq_iff]; rw [hg]
    · simp [MulAut.conj]; group

variable (g s) in
/-- The `fixingSubgroup` of `g • s` is the conjugate of the `fixingSubgroup` of `s` by `g`. -/
@[to_additive /-- The `fixingAddSubgroup` of `g +ᵥ s` is the conjugate
of the `fixingAddSubgroup` of `s` by `g`. -/]
/--
theorem `fixingSubgroup_smul_eq_fixingSubgroup_map_conj` / 定理 `fixingSubgroup_smul_eq_fixingSubgroup_map_conj`

English:
theorem fixingSubgroup_smul_eq_fixingSubgroup_map_conj
  proof: (fixingSubgroup_map_conj_eq rfl).symm

中文:
定理 fixingSubgroup_smul_eq_fixingSubgroup_map_conj
  证明: (fixingSubgroup_map_conj_eq rfl).symm

Depends on / 依赖: fixingSubgroup_map_conj_eq
-/
theorem fixingSubgroup_smul_eq_fixingSubgroup_map_conj :
    fixingSubgroup M (g • s) = (fixingSubgroup M s).map (MulAut.conj g).toMonoidHom :=
  (fixingSubgroup_map_conj_eq rfl).symm

/-- The equivalence of `fixingSubgroup M t` with `fixingSubgroup M s`
  when `s` is a translate of `t`. -/
@[to_additive
/-- The equivalence of `fixingSubgroup M t` with `fixingSubgroup M s`
  when `s` is a translate of `t`. -/]
/--
Definition of `fixingSubgroupEquivFixingSubgroup` / `fixingSubgroupEquivFixingSubgroup` 的定义

English:
definition fixingSubgroupEquivFixingSubgroup
  signature: (hg : g • t = s)
  body: ((MulAut.conj g).subgroupMap (fixingSubgroup M t)).trans
    (MulEquiv.subgroupCongr (fixingSubgroup_map_conj_eq hg))

@[to_additive (attr := simp)]

中文:
定义 fixingSubgroupEquivFixingSubgroup
  签名: (hg : g • t = s)
  定义体: ((MulAut.conj g).subgroupMap (fixingSubgroup M t)).trans
    (MulEquiv.subgroupCongr (fixingSubgroup_map_conj_eq hg))

@[to_additive (attr := simp)]

Depends on / 依赖: MulAut, MulAut.conj, MulEquiv, MulEquiv.subgroupCongr, fixingSubgroup, fixingSubgroup_map_conj_eq, subgroupCongr, subgroupMap
-/
def fixingSubgroupEquivFixingSubgroup (hg : g • t = s) :
    fixingSubgroup M t ≃* fixingSubgroup M s :=
  ((MulAut.conj g).subgroupMap (fixingSubgroup M t)).trans
    (MulEquiv.subgroupCongr (fixingSubgroup_map_conj_eq hg))

@[to_additive (attr := simp)]
/--
theorem `fixingSubgroupEquivFixingSubgroup_coe_apply` / 定理 `fixingSubgroupEquivFixingSubgroup_coe_apply`

English:
theorem fixingSubgroupEquivFixingSubgroup_coe_apply
  given: (hg : g • t = s) (x : fixingSubgroup M t)
  proof: rfl

中文:
定理 fixingSubgroupEquivFixingSubgroup_coe_apply
  条件: (hg : g • t = s) (x : fixingSubgroup M t)
  证明: rfl
-/
theorem fixingSubgroupEquivFixingSubgroup_coe_apply (hg : g • t = s) (x : fixingSubgroup M t) :
    (fixingSubgroupEquivFixingSubgroup hg x : M) = MulAut.conj g x := rfl

/-- Conjugation induces an equivariant map between the `SubMulAction` of
the fixing subgroup of a subset and that of a translate. -/
@[to_additive
/-- Conjugation induces an equivariant map between the `SubAddAction` of
the fixing subgroup of a subset and that of a translate. -/]
/--
Definition of `conjMap_ofFixingSubgroup` / `conjMap_ofFixingSubgroup` 的定义

English:
definition conjMap_ofFixingSubgroup
  signature: (hg : g • t = s)
  body: fun ⟨x, hx⟩ =>
    ⟨g • x, by
      intro hgxt; apply hx
      rw [← hg] at hgxt
      exact Set.smul_mem_smul_set_iff.mp hgxt⟩
  map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ => by
    simp only [← SetLike.coe_eq_coe, subgroup_smul_def,
      SetLike.val_smul,
      fixingSubgroupEquivFixingSubgroup_coe_apply,


中文:
定义 conjMap_ofFixingSubgroup
  签名: (hg : g • t = s)
  定义体: fun ⟨x, hx⟩ =>
    ⟨g • x, by
      intro hgxt; apply hx
      rw [← hg] at hgxt
      exact Set.smul_mem_smul_set_iff.mp hgxt⟩
  map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ => by
    simp only [← SetLike.coe_eq_coe, subgroup_smul_def,
      SetLike.val_smul,
      fixingSubgroupEquivFixingSubgroup_coe_apply,

-/
def conjMap_ofFixingSubgroup (hg : g • t = s) :
    ofFixingSubgroup M t ->ₑ[fixingSubgroupEquivFixingSubgroup hg] ofFixingSubgroup M s where
  toFun := fun ⟨x, hx⟩ =>
    ⟨g • x, by
      intro hgxt; apply hx
      rw [← hg] at hgxt
      exact Set.smul_mem_smul_set_iff.mp hgxt⟩
  map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ => by
    simp only [← SetLike.coe_eq_coe, subgroup_smul_def,
      SetLike.val_smul,
      fixingSubgroupEquivFixingSubgroup_coe_apply,
      MulAut.conj_apply, mul_smul, inv_smul_smul]

@[to_additive (attr := simp)]
/--
theorem `conjMap_ofFixingSubgroup_coe_apply` / 定理 `conjMap_ofFixingSubgroup_coe_apply`

English:
theorem conjMap_ofFixingSubgroup_coe_apply
  given: {hg : g • t = s} (x : ofFixingSubgroup M t)
  proof: rfl

@[to_additive]

中文:
定理 conjMap_ofFixingSubgroup_coe_apply
  条件: {hg : g • t = s} (x : ofFixingSubgroup M t)
  证明: rfl

@[to_additive]
-/
theorem conjMap_ofFixingSubgroup_coe_apply {hg : g • t = s} (x : ofFixingSubgroup M t) :
    conjMap_ofFixingSubgroup hg x = g • (x : α) := rfl

@[to_additive]
/--
theorem `conjMap_ofFixingSubgroup_bijective` / 定理 `conjMap_ofFixingSubgroup_bijective`

English:
theorem conjMap_ofFixingSubgroup_bijective
  given: {s t : Set α} {g : M} {hst : g • s = t}
  proof: by
  constructor
  · rintro x y hxy
    simpa [← SetLike.coe_eq_coe] using hxy
  · rintro ⟨x, hx⟩
    rw [eq_comm]; rw [← inv_smul_eq_iff] at hst
    use (SubMulAction.conjMap_ofFixingSubgroup hst) ⟨x, hx⟩
    simp [← SetLike.coe_eq_coe]

中文:
定理 conjMap_ofFixingSubgroup_bijective
  条件: {s t : 集合 α} {g : M} {hst : g • s = t}
  证明: by
  constructor
  · rintro x y hxy
    simpa [← SetLike.coe_eq_coe] using hxy
  · rintro ⟨x, hx⟩
    rw [eq_comm]; rw [← inv_smul_eq_iff] at hst
    use (SubMulAction.conjMap_ofFixingSubgroup hst) ⟨x, hx⟩
    simp [← SetLike.coe_eq_coe]

Depends on / 依赖: SetLike, SetLike.coe_eq_coe, SubMulAction, SubMulAction.conjMap_ofFixingSubgroup, coe_eq_coe, conjMap_ofFixingSubgroup, eq_comm, inv_smul_eq_iff
-/
theorem conjMap_ofFixingSubgroup_bijective {s t : Set α} {g : M} {hst : g • s = t} :
    Bijective (conjMap_ofFixingSubgroup hst) := by
  constructor
  · rintro x y hxy
    simpa [← SetLike.coe_eq_coe] using hxy
  · rintro ⟨x, hx⟩
    rw [eq_comm]; rw [← inv_smul_eq_iff] at hst
    use (SubMulAction.conjMap_ofFixingSubgroup hst) ⟨x, hx⟩
    simp [← SetLike.coe_eq_coe]

end FixingSubgroupConj

variable {s t : Set α}

@[to_additive]
/--
lemma `mem_fixingSubgroup_union_iff` / 引理 `mem_fixingSubgroup_union_iff`

English:
lemma mem_fixingSubgroup_union_iff
  given: {g : M}
  proof: by
  simp [fixingSubgroup_union, Subgroup.mem_inf]

中文:
引理 mem_fixingSubgroup_union_iff
  条件: {g : M}
  证明: by
  simp [fixingSubgroup_union, Subgroup.mem_inf]

Depends on / 依赖: Subgroup, Subgroup.mem_inf, fixingSubgroup_union, mem_inf
-/
lemma mem_fixingSubgroup_union_iff {g : M} :
    g in fixingSubgroup M (s union t) ↔ g in fixingSubgroup M s ∧ g in fixingSubgroup M t := by
  simp [fixingSubgroup_union, Subgroup.mem_inf]

/-- The group morphism from `fixingSubgroup` of a union to the iterated `fixingSubgroup`. -/
@[to_additive
/-- The additive group morphism from `fixingAddSubgroup` of a union
to the iterated `fixingAddSubgroup`. -/]
/--
Definition of `fixingSubgroup_union_to_fixingSubgroup_of_fixingSubgroup` / `fixingSubgroup_union_to_fixingSubgroup_of_fixingSubgroup` 的定义

English:
definition fixingSubgroup_union_to_fixingSubgroup_of_fixingSubgroup
  signature: :
  body: ⟨⟨m, (mem_fixingSubgroup_union_iff.mp m.prop).1⟩, by
      rintro ⟨⟨x, hx⟩, hx'⟩
      simp only [Set.mem_preimage] at hx'
      simp only [← SetLike.coe_eq_coe, SubMulAction.val_smul_of_tower]
      exact (mem_fixingSubgroup_union_iff.mp m.prop).2 ⟨x, hx'⟩⟩
  map_one' := by simp
  map_mul' _ _ := b

中文:
定义 fixingSubgroup_union_to_fixingSubgroup_of_fixingSubgroup
  签名: :
  定义体: ⟨⟨m, (mem_fixingSubgroup_union_iff.mp m.prop).1⟩, by
      rintro ⟨⟨x, hx⟩, hx'⟩
      simp only [Set.mem_preimage] at hx'
      simp only [← SetLike.coe_eq_coe, SubMulAction.val_smul_of_tower]
      exact (mem_fixingSubgroup_union_iff.mp m.prop).2 ⟨x, hx'⟩⟩
  map_one' := by simp
  map_mul' _ _ := b

Depends on / 依赖: Set.mem_preimage, SetLike, SetLike.coe_eq_coe, SubMulAction, SubMulAction.val_smul_of_tower, coe_eq_coe, m.prop, map_mul, map_one, mem_fixingSubgroup_union_iff, mem_fixingSubgroup_union_iff.mp, mem_preimage, val_smul_of_tower
-/
def fixingSubgroup_union_to_fixingSubgroup_of_fixingSubgroup :
    fixingSubgroup M (s union t) ->*
      fixingSubgroup (fixingSubgroup M s) (Subtype.val ⁻¹' t : Set (ofFixingSubgroup M s)) where
  toFun m := ⟨⟨m, (mem_fixingSubgroup_union_iff.mp m.prop).1⟩, by
      rintro ⟨⟨x, hx⟩, hx'⟩
      simp only [Set.mem_preimage] at hx'
      simp only [← SetLike.coe_eq_coe, SubMulAction.val_smul_of_tower]
      exact (mem_fixingSubgroup_union_iff.mp m.prop).2 ⟨x, hx'⟩⟩
  map_one' := by simp
  map_mul' _ _ := by simp

variable (M s t) in
/-- The identity between the iterated `SubMulAction`
  of the `fixingSubgroup` and the `SubMulAction` of the `fixingSubgroup`
  of the union, as an equivariant map. -/
@[to_additive /-- The identity between the iterated `SubAddAction`
  of the `fixingAddSubgroup` and the `SubAddAction` of the `fixingAddSubgroup`
  of the union, as an equivariant map. -/]
/--
Definition of `map_ofFixingSubgroupUnion` / `map_ofFixingSubgroupUnion` 的定义

English:
definition map_ofFixingSubgroupUnion
  signature: :
  body: fun m => ⟨⟨m, by
        let hm := m.prop
        simp only [fixingSubgroup_union, Subgroup.mem_inf] at hm
        exact hm.left⟩, by
      let hm := m.prop
      simp only [fixingSubgroup_union, Subgroup.mem_inf] at hm
      rintro ⟨⟨x, hx⟩, hx'⟩
      simp only [Set.mem_preimage] at hx'
      simp

中文:
定义 map_ofFixingSubgroupUnion
  签名: :
  定义体: fun m => ⟨⟨m, by
        let hm := m.prop
        simp only [fixingSubgroup_union, Subgroup.mem_inf] at hm
        exact hm.left⟩, by
      let hm := m.prop
      simp only [fixingSubgroup_union, Subgroup.mem_inf] at hm
      rintro ⟨⟨x, hx⟩, hx'⟩
      simp only [Set.mem_preimage] at hx'
      simp

Depends on / 依赖: Set.mem_preimage, SetLike, SetLike.coe_eq_coe, SubMulAction, SubMulAction.val_smul_of_tower, Subgroup, Subgroup.mem_inf, Subtype, Subtype.val, coe_eq_coe, fixingSubgroup, fixingSubgroup_union, hm.left, hm.right, m.prop, mem_inf, mem_preimage, ofFixingSubgroup, val_smul_of_tower, x.prop
-/
def map_ofFixingSubgroupUnion :
    let ψ : fixingSubgroup M (s union t) ->
      fixingSubgroup (fixingSubgroup M s) (Subtype.val ⁻¹' t : Set (ofFixingSubgroup M s)) :=
      fun m => ⟨⟨m, by
        let hm := m.prop
        simp only [fixingSubgroup_union, Subgroup.mem_inf] at hm
        exact hm.left⟩, by
      let hm := m.prop
      simp only [fixingSubgroup_union, Subgroup.mem_inf] at hm
      rintro ⟨⟨x, hx⟩, hx'⟩
      simp only [Set.mem_preimage] at hx'
      simp only [← SetLike.coe_eq_coe, SubMulAction.val_smul_of_tower]
      exact hm.right ⟨x, hx'⟩⟩
    ofFixingSubgroup M (s union t) ->ₑ[ψ]
      ofFixingSubgroup (fixingSubgroup M s) (Subtype.val ⁻¹' t : Set (ofFixingSubgroup M s)) where
  toFun x :=
    ⟨⟨x, fun hx => x.prop (Set.mem_union_left t hx)⟩,
        fun hx => x.prop (by
          apply Set.mem_union_right s
          simpa only [Set.mem_preimage, Subtype.coe_mk] using hx)⟩
  map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ => by
    rw [← SetLike.coe_eq_coe]; rw [← SetLike.coe_eq_coe]
    exact subgroup_smul_def ⟨m, hm⟩ x

@[to_additive]
/--
theorem `map_ofFixingSubgroupUnion_def` / 定理 `map_ofFixingSubgroupUnion_def`

English:
theorem map_ofFixingSubgroupUnion_def
  given: (x : SubMulAction.ofFixingSubgroup M (s union t))
  proof: rfl

@[to_additive]

中文:
定理 map_ofFixingSubgroupUnion_def
  条件: (x : SubMul作用.ofFixingSubgroup M (s union t))
  证明: rfl

@[to_additive]
-/
theorem map_ofFixingSubgroupUnion_def (x : SubMulAction.ofFixingSubgroup M (s union t)) :
    ((SubMulAction.map_ofFixingSubgroupUnion M s t) x : α) = x :=
  rfl

@[to_additive]
/--
theorem `map_ofFixingSubgroupUnion_bijective` / 定理 `map_ofFixingSubgroupUnion_bijective`

English:
theorem map_ofFixingSubgroupUnion_bijective
  proof: by
  constructor
  · intro a b h
    simpa only [← SetLike.coe_eq_coe] using! h
  · rintro ⟨⟨a, ha⟩, ha'⟩
    suffices a in ofFixingSubgroup M (s union t) by
      exact ⟨⟨a, this⟩, rfl⟩
    intro hy
    rcases (Set.mem_union a s t).mp hy with h | h
    · exact ha h
    · apply ha'
      simpa only 

中文:
定理 map_ofFixingSubgroupUnion_bijective
  证明: by
  constructor
  · intro a b h
    simpa only [← SetLike.coe_eq_coe] using! h
  · rintro ⟨⟨a, ha⟩, ha'⟩
    suffices a in ofFixingSubgroup M (s union t) by
      exact ⟨⟨a, this⟩, rfl⟩
    intro hy
    rcases (Set.mem_union a s t).mp hy with h | h
    · exact ha h
    · apply ha'
      simpa only 

Depends on / 依赖: Set.mem_preimage, Set.mem_union, SetLike, SetLike.coe_eq_coe, coe_eq_coe, mem_preimage, mem_union, ofFixingSubgroup
-/
theorem map_ofFixingSubgroupUnion_bijective :
    Bijective (map_ofFixingSubgroupUnion M s t) := by
  constructor
  · intro a b h
    simpa only [← SetLike.coe_eq_coe] using! h
  · rintro ⟨⟨a, ha⟩, ha'⟩
    suffices a in ofFixingSubgroup M (s union t) by
      exact ⟨⟨a, this⟩, rfl⟩
    intro hy
    rcases (Set.mem_union a s t).mp hy with h | h
    · exact ha h
    · apply ha'
      simpa only [Set.mem_preimage]

variable (M) in
/-- The equivariant map on `SubMulAction.ofFixingSubgroup` given a set inclusion. -/
@[to_additive
/-- The equivariant map on `SubAddAction.ofFixingAddSubgroup` given a set inclusion. -/]
/--
Definition of `ofFixingSubgroup_of_inclusion` / `ofFixingSubgroup_of_inclusion` 的定义

English:
definition ofFixingSubgroup_of_inclusion
  signature: (hst : t subseteq s)
  body: ⟨y.val, fun h => y.prop (hst h)⟩
  map_smul' _ _ := rfl

@[to_additive]

中文:
定义 ofFixingSubgroup_of_inclusion
  签名: (hst : t subseteq s)
  定义体: ⟨y.val, fun h => y.prop (hst h)⟩
  map_smul' _ _ := rfl

@[to_additive]

Depends on / 依赖: y.prop, y.val
-/
def ofFixingSubgroup_of_inclusion (hst : t subseteq s) :
    ofFixingSubgroup M s
      ->ₑ[Subgroup.inclusion (fixingSubgroup_antitone M α hst)]
        ofFixingSubgroup M t where
  toFun y := ⟨y.val, fun h => y.prop (hst h)⟩
  map_smul' _ _ := rfl

@[to_additive]
/--
lemma `ofFixingSubgroup_of_inclusion_injective` / 引理 `ofFixingSubgroup_of_inclusion_injective`

English:
lemma ofFixingSubgroup_of_inclusion_injective
  given: {hst : t subseteq s}
  proof: by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  rw [← SetLike.coe_eq_coe] at hxy ⊢
  exact hxy

中文:
引理 ofFixingSubgroup_of_inclusion_injective
  条件: {hst : t subseteq s}
  证明: by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  rw [← SetLike.coe_eq_coe] at hxy ⊢
  exact hxy

Depends on / 依赖: SetLike, SetLike.coe_eq_coe, coe_eq_coe
-/
lemma ofFixingSubgroup_of_inclusion_injective {hst : t subseteq s} :
    Injective (ofFixingSubgroup_of_inclusion M hst) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  rw [← SetLike.coe_eq_coe] at hxy ⊢
  exact hxy

set_option backward.isDefEq.respectTransparency false in
variable (M) in
/-- The equivariant map between `SubMulAction.ofStabilizer M a`
and `ofFixingSubgroup M {a}`. -/
@[to_additive /-- The equivariant map between `SubAddAction.ofStabilizer M a`
and `ofFixingAddSubgroup M {a}`. -/]
/--
Definition of `ofFixingSubgroup_of_singleton` / `ofFixingSubgroup_of_singleton` 的定义

English:
definition ofFixingSubgroup_of_singleton
  signature: (a : α)
  body: fun ⟨m, hm⟩ =>
      ⟨m, ((mem_fixingSubgroup_iff M).mp hm) a (Set.mem_singleton a)⟩
    ofFixingSubgroup M ({a} : Set α) ->ₑ[φ] ofStabilizer M a where
  toFun x := ⟨x, by simp⟩
  map_smul' _ _ := rfl

@[to_additive]

中文:
定义 ofFixingSubgroup_of_singleton
  签名: (a : α)
  定义体: fun ⟨m, hm⟩ =>
      ⟨m, ((mem_fixingSubgroup_iff M).mp hm) a (Set.mem_singleton a)⟩
    ofFixingSubgroup M ({a} : Set α) ->ₑ[φ] ofStabilizer M a where
  toFun x := ⟨x, by simp⟩
  map_smul' _ _ := rfl

@[to_additive]
-/
def ofFixingSubgroup_of_singleton (a : α) :
    let φ : fixingSubgroup M ({a} : Set α) -> stabilizer M a := fun ⟨m, hm⟩ =>
      ⟨m, ((mem_fixingSubgroup_iff M).mp hm) a (Set.mem_singleton a)⟩
    ofFixingSubgroup M ({a} : Set α) ->ₑ[φ] ofStabilizer M a where
  toFun x := ⟨x, by simp⟩
  map_smul' _ _ := rfl

@[to_additive]
/--
theorem `ofFixingSubgroup_of_singleton_bijective` / 定理 `ofFixingSubgroup_of_singleton_bijective`

English:
theorem ofFixingSubgroup_of_singleton_bijective
  given: {a : α}
  proof: ⟨fun _ _ => id, fun x => ⟨x, rfl⟩⟩

中文:
定理 ofFixingSubgroup_of_singleton_bijective
  条件: {a : α}
  证明: ⟨fun _ _ => id, fun x => ⟨x, rfl⟩⟩
-/
theorem ofFixingSubgroup_of_singleton_bijective {a : α} :
    Bijective (ofFixingSubgroup_of_singleton M a) :=
  ⟨fun _ _ => id, fun x => ⟨x, rfl⟩⟩

variable (M) in
/-- The identity between the `SubMulAction`s of `fixingSubgroup`s
of equal sets, as an equivariant map. -/
@[to_additive /-- The identity between the `SubAddAction`s of `fixingAddSubgroup`s
of equal sets, as an equivariant map. -/]
/--
Definition of `ofFixingSubgroup_of_eq` / `ofFixingSubgroup_of_eq` 的定义

English:
definition ofFixingSubgroup_of_eq
  signature: (hst : s = t)
  body: MulEquiv.subgroupCongr (congrArg₂ _ rfl hst)
    ofFixingSubgroup M s ->ₑ[φ] ofFixingSubgroup M t where
  toFun := fun ⟨x, hx⟩ => ⟨x, by rw [← hst]; exact hx⟩
  map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ => rfl

@[to_additive (attr := simp)]

中文:
定义 ofFixingSubgroup_of_eq
  签名: (hst : s = t)
  定义体: MulEquiv.subgroupCongr (congrArg₂ _ rfl hst)
    ofFixingSubgroup M s ->ₑ[φ] ofFixingSubgroup M t where
  toFun := fun ⟨x, hx⟩ => ⟨x, by rw [← hst]; exact hx⟩
  map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ => rfl

@[to_additive (attr := simp)]

Depends on / 依赖: MulEquiv, MulEquiv.subgroupCongr, map_smul, ofFixingSubgroup, subgroupCongr
-/
def ofFixingSubgroup_of_eq (hst : s = t) :
    let φ : fixingSubgroup M s ≃* fixingSubgroup M t :=
      MulEquiv.subgroupCongr (congrArg₂ _ rfl hst)
    ofFixingSubgroup M s ->ₑ[φ] ofFixingSubgroup M t where
  toFun := fun ⟨x, hx⟩ => ⟨x, by rw [← hst]; exact hx⟩
  map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ => rfl

@[to_additive (attr := simp)]
/--
theorem `ofFixingSubgroup_of_eq_apply` / 定理 `ofFixingSubgroup_of_eq_apply`

English:
theorem ofFixingSubgroup_of_eq_apply
  statement: {hst : s = t}
  proof: rfl

@[to_additive]

中文:
定理 ofFixingSubgroup_of_eq_apply
  结论: {hst : s = t}
  证明: rfl

@[to_additive]
-/
theorem ofFixingSubgroup_of_eq_apply {hst : s = t}
    (x : ofFixingSubgroup M s) :
    ((ofFixingSubgroup_of_eq M hst x) : α) = x := rfl

@[to_additive]
/--
theorem `ofFixingSubgroup_of_eq_bijective` / 定理 `ofFixingSubgroup_of_eq_bijective`

English:
theorem ofFixingSubgroup_of_eq_bijective
  given: {hst : s = t}
  proof: ⟨fun _ _ hxy => by simpa [← SetLike.coe_eq_coe] using hxy,
    fun ⟨x, hxt⟩ => ⟨⟨x, by rwa [hst]⟩, by simp [← SetLike.coe_eq_coe]⟩⟩

中文:
定理 ofFixingSubgroup_of_eq_bijective
  条件: {hst : s = t}
  证明: ⟨fun _ _ hxy => by simpa [← SetLike.coe_eq_coe] using hxy,
    fun ⟨x, hxt⟩ => ⟨⟨x, by rwa [hst]⟩, by simp [← SetLike.coe_eq_coe]⟩⟩

Depends on / 依赖: SetLike, SetLike.coe_eq_coe, coe_eq_coe
-/
theorem ofFixingSubgroup_of_eq_bijective {hst : s = t} :
    Bijective (ofFixingSubgroup_of_eq M hst) :=
  ⟨fun _ _ hxy => by simpa [← SetLike.coe_eq_coe] using hxy,
    fun ⟨x, hxt⟩ => ⟨⟨x, by rwa [hst]⟩, by simp [← SetLike.coe_eq_coe]⟩⟩

end Comparisons

section Construction

open Function.Embedding Fin.Embedding

/-- Append `Fin m ↪ ofFixingSubgroup M s` at the end of an enumeration of `s`. -/
@[to_additive
/-- Append `Fin m ↪ ofFixingSubgroup M s` at the end of an enumeration of `s`. -/]
/--
Definition of `ofFixingSubgroup.append` / `ofFixingSubgroup.append` 的定义

English:
definition ofFixingSubgroup.append
  body: by
  have : Nonempty (Fin (s.ncard) ≃ s) :=
    Finite.card_eq.mp (by simp [Nat.card_coe_set_eq])
  let y := (Classical.choice this).toEmbedding
  apply Fin.Embedding.append (x := y.trans (subtype _)) (y := x.trans (subtype _))
  rw [Set.disjoint_iff_forall_ne]
  rintro _ ⟨j, rfl⟩ _ ⟨i, rfl⟩ H
  app

中文:
定义 ofFixingSubgroup.append
  定义体: by
  have : Nonempty (Fin (s.ncard) ≃ s) :=
    Finite.card_eq.mp (by simp [Nat.card_coe_set_eq])
  let y := (Classical.choice this).toEmbedding
  apply Fin.Embedding.append (x := y.trans (subtype _)) (y := x.trans (subtype _))
  rw [Set.disjoint_iff_forall_ne]
  rintro _ ⟨j, rfl⟩ _ ⟨i, rfl⟩ H
  app

Depends on / 依赖: Classical, Classical.choice, Embedding, Fin.Embedding.append, Finite, Finite.card_eq.mp, Function, Function.Embedding.subtype_apply, Nat.card_coe_set_eq, Nonempty, Set.disjoint_iff_forall_ne, Subtype, Subtype.coe_prop, append, card_coe_set_eq, card_eq, choice, coe_prop, disjoint_iff_forall_ne, s.ncard
-/
noncomputable def ofFixingSubgroup.append
    {n : Nat} [Finite s] (x : Fin n ↪ ofFixingSubgroup M s) :
    Fin (s.ncard + n) ↪ α := by
  have : Nonempty (Fin (s.ncard) ≃ s) :=
    Finite.card_eq.mp (by simp [Nat.card_coe_set_eq])
  let y := (Classical.choice this).toEmbedding
  apply Fin.Embedding.append (x := y.trans (subtype _)) (y := x.trans (subtype _))
  rw [Set.disjoint_iff_forall_ne]
  rintro _ ⟨j, rfl⟩ _ ⟨i, rfl⟩ H
  apply (x i).prop
  simp only [trans_apply, Function.Embedding.subtype_apply] at H
  simpa [H] using Subtype.coe_prop (y j)

@[to_additive]
/--
theorem `ofFixingSubgroup.append_left` / 定理 `ofFixingSubgroup.append_left`

English:
theorem ofFixingSubgroup.append_left
  statement: {n : Nat} [Finite s]
  proof: Finite.card_eq.mp (by simp [Nat.card_coe_set_eq])
    ofFixingSubgroup.append x (Fin.castAdd n i) = (Classical.choice Hs) i := by
  simp [ofFixingSubgroup.append]

@[to_additive]

中文:
定理 ofFixingSubgroup.append_left
  结论: {n : 自然数} [有限 s]
  证明: Finite.card_eq.mp (by simp [Nat.card_coe_set_eq])
    ofFixingSubgroup.append x (Fin.castAdd n i) = (Classical.choice Hs) i := by
  simp [ofFixingSubgroup.append]

@[to_additive]

Depends on / 依赖: Classical, Classical.choice, Fin.castAdd, Finite, Finite.card_eq.mp, Nat.card_coe_set_eq, append, card_coe_set_eq, card_eq, castAdd, choice, ofFixingSubgroup, ofFixingSubgroup.append
-/
theorem ofFixingSubgroup.append_left {n : Nat} [Finite s]
    (x : Fin n ↪ ofFixingSubgroup M s) (i : Fin s.ncard) :
    let Hs : Nonempty (Fin (s.ncard) ≃ s) :=
      Finite.card_eq.mp (by simp [Nat.card_coe_set_eq])
    ofFixingSubgroup.append x (Fin.castAdd n i) = (Classical.choice Hs) i := by
  simp [ofFixingSubgroup.append]

@[to_additive]
/--
theorem `ofFixingSubgroup.append_right` / 定理 `ofFixingSubgroup.append_right`

English:
theorem ofFixingSubgroup.append_right
  statement: {n : Nat} [Finite s]
  proof: by
  simp [ofFixingSubgroup.append]

中文:
定理 ofFixingSubgroup.append_right
  结论: {n : 自然数} [有限 s]
  证明: by
  simp [ofFixingSubgroup.append]

Depends on / 依赖: append, ofFixingSubgroup, ofFixingSubgroup.append
-/
theorem ofFixingSubgroup.append_right {n : Nat} [Finite s]
    (x : Fin n ↪ ofFixingSubgroup M s) (i : Fin n) :
    ofFixingSubgroup.append x (Fin.natAdd s.ncard i) = x i := by
  simp [ofFixingSubgroup.append]

end Construction

section TwoCriteria

open MulAction

/--
theorem `IsPretransitive.isPretransitive_ofFixingSubgroup_inter` / 定理 `IsPretransitive.isPretransitive_ofFixingSubgroup_inter`

English:
theorem IsPretransitive.isPretransitive_ofFixingSubgroup_inter
  proof: by
  rw [Ne]; rw [Set.top_eq_univ]; rw [← Set.compl_empty_iff]; rw [← Ne]; rw [← Set.nonempty_iff_ne_empty] at ha
  obtain ⟨a, ha⟩ := ha
  rw [Set.compl_union] at ha
  have ha' : a in (s inter g • s)ᶜ := by
    rw [Set.compl_inter]
    exact Set.mem_union_left _ ha.1
  rw [MulAction.isPretransitive_

中文:
定理 是Pretransitive.isPretransitive_ofFixingSubgroup_inter
  证明: by
  rw [Ne]; rw [Set.top_eq_univ]; rw [← Set.compl_empty_iff]; rw [← Ne]; rw [← Set.nonempty_iff_ne_empty] at ha
  obtain ⟨a, ha⟩ := ha
  rw [Set.compl_union] at ha
  have ha' : a in (s inter g • s)ᶜ := by
    rw [Set.compl_inter]
    exact Set.mem_union_left _ ha.1
  rw [MulAction.isPretransitive_

Depends on / 依赖: MulAction, MulAction.isPretransitive_iff_base, Set.compl_empty_iff, Set.compl_inter, Set.compl_union, Set.mem_inter_iff, Set.mem_union_left, Set.nonempty_iff_ne_empty, Set.top_eq_univ, compl_empty_iff, compl_inter, compl_union, exists_sm, hs.exists_sm, isPretransitive_iff_base, mem_inter_iff, mem_ofFixingSubgroup_iff, mem_union_left, nonempty_iff_ne_empty, not_and_or
-/
theorem IsPretransitive.isPretransitive_ofFixingSubgroup_inter
    (hs : IsPretransitive (fixingSubgroup M s) (ofFixingSubgroup M s))
    {g : M} (ha : s union g • s != ⊤) :
    IsPretransitive (fixingSubgroup M (s inter g • s)) (ofFixingSubgroup M (s inter g • s)) := by
  rw [Ne]; rw [Set.top_eq_univ]; rw [← Set.compl_empty_iff]; rw [← Ne]; rw [← Set.nonempty_iff_ne_empty] at ha
  obtain ⟨a, ha⟩ := ha
  rw [Set.compl_union] at ha
  have ha' : a in (s inter g • s)ᶜ := by
    rw [Set.compl_inter]
    exact Set.mem_union_left _ ha.1
  rw [MulAction.isPretransitive_iff_base (⟨a]; rw [ha'⟩ : ofFixingSubgroup M (s inter g • s))]
  rintro ⟨x, hx⟩
  rw [mem_ofFixingSubgroup_iff]; rw [Set.mem_inter_iff]; rw [not_and_or] at hx
  rcases hx with hx | hx
  · obtain ⟨⟨k, hk⟩, hkax⟩ := hs.exists_smul_eq ⟨a, ha.1⟩ ⟨x, hx⟩
    use ⟨k, fun ⟨y, hy⟩ => hk ⟨y, hy.1⟩⟩
    rwa [Subtype.ext_iff] at hkax ⊢
  · have hg'x : g⁻¹ • x in ofFixingSubgroup M s := mt Set.mem_smul_set_iff_inv_smul_mem.mpr hx
    have hg'a : g⁻¹ • a in ofFixingSubgroup M s := mt Set.mem_smul_set_iff_inv_smul_mem.mpr ha.2
    obtain ⟨⟨k, hk⟩, hkax⟩ := hs.exists_smul_eq ⟨g⁻¹ • a, hg'a⟩ ⟨g⁻¹ • x, hg'x⟩
    use ⟨g * k * g⁻¹, ?_⟩
    · simp only [← SetLike.coe_eq_coe] at hkax ⊢
      rwa [SetLike.val_smul, Subgroup.mk_smul, eq_inv_smul_iff, smul_smul, smul_smul] at hkax
    · rw [mem_fixingSubgroup_iff] at hk ⊢
      intro y hy
      rw [mul_smul]; rw [mul_smul]; rw [smul_eq_iff_eq_inv_smul g]
      exact hk _ (Set.mem_smul_set_iff_inv_smul_mem.mp hy.2)

/--
theorem `IsPreprimitive.isPreprimitive_ofFixingSubgroup_inter` / 定理 `IsPreprimitive.isPreprimitive_ofFixingSubgroup_inter`

English:
theorem IsPreprimitive.isPreprimitive_ofFixingSubgroup_inter
  proof: by
  have := IsPretransitive.isPretransitive_ofFixingSubgroup_inter hs.toIsPretransitive ha
  apply IsPreprimitive.of_card_lt (f := ofFixingSubgroup_of_inclusion M Set.inter_subset_left)
  rw [show Nat.card (ofFixingSubgroup M (s inter g • s)) = (s inter g • s)ᶜ.ncard from
    Nat.card_coe_set_eq _]

中文:
定理 是Preprimitive.isPreprimitive_ofFixingSubgroup_inter
  证明: by
  have := IsPretransitive.isPretransitive_ofFixingSubgroup_inter hs.toIsPretransitive ha
  apply IsPreprimitive.of_card_lt (f := ofFixingSubgroup_of_inclusion M Set.inter_subset_left)
  rw [show Nat.card (ofFixingSubgroup M (s inter g • s)) = (s inter g • s)ᶜ.ncard from
    Nat.card_coe_set_eq _]

Depends on / 依赖: IsPreprimitive, IsPreprimitive.of_card_lt, IsPretransitive, IsPretransitive.isPretransitive_ofFixingSubgroup_inter, Nat.card, Nat.card_coe_set_eq, Set.compl_inter, Set.inter_subset_left, Set.ncard_range_of_injective, Set.ncard_union_lt, card_coe_set_eq, compl_inter, hs.toIsPretransitive, inter_subset_left, isPretransitive_ofFixingSubgroup_inter, ncard_range_of_injective, ncard_union_lt, ofFixingSubgroup, ofFixingSubgroup_of_inclusion, ofFixingSubgroup_of_inclusion_injective
-/
theorem IsPreprimitive.isPreprimitive_ofFixingSubgroup_inter
    [Finite α]
    (hs : IsPreprimitive (fixingSubgroup M s) (ofFixingSubgroup M s))
    {g : M} (ha : s union g • s != ⊤) :
    IsPreprimitive (fixingSubgroup M (s inter g • s)) (ofFixingSubgroup M (s inter g • s)) := by
  have := IsPretransitive.isPretransitive_ofFixingSubgroup_inter hs.toIsPretransitive ha
  apply IsPreprimitive.of_card_lt (f := ofFixingSubgroup_of_inclusion M Set.inter_subset_left)
  rw [show Nat.card (ofFixingSubgroup M (s inter g • s)) = (s inter g • s)ᶜ.ncard from
    Nat.card_coe_set_eq _]; rw [Set.ncard_range_of_injective ofFixingSubgroup_of_inclusion_injective]; rw [show Nat.card (ofFixingSubgroup M s) = sᶜ.ncard from Nat.card_coe_set_eq _]; rw [Set.compl_inter]
  refine (Set.ncard_union_lt sᶜ.toFinite (g • s)ᶜ.toFinite ?_).trans_le ?_
  · rwa [Set.disjoint_compl_right_iff_subset, Set.compl_subset_iff_union]
  · rw [← Set.smul_set_compl, Set.ncard_smul_set, two_mul]

end TwoCriteria

end SubMulAction

section Pointwise

open MulAction Set

variable (G : Type*) [Group G] {α : Type*} [MulAction G α]

@[to_additive]
/--
theorem `MulAction.fixingSubgroup_le_stabilizer` / 定理 `MulAction.fixingSubgroup_le_stabilizer`

English:
theorem MulAction.fixingSubgroup_le_stabilizer
  given: (s : Set α)
  proof: by
  intro k hk
  rw [mem_stabilizer_iff]
  conv_rhs => rw [← Set.image_id s]
  apply Set.image_congr
  simpa only [mem_fixingSubgroup_iff, id] using hk

中文:
定理 乘法作用.fixingSubgroup_le_stabilizer
  条件: (s : 集合 α)
  证明: by
  intro k hk
  rw [mem_stabilizer_iff]
  conv_rhs => rw [← Set.image_id s]
  apply Set.image_congr
  simpa only [mem_fixingSubgroup_iff, id] using hk

Depends on / 依赖: Classical, Classical.dec, Quotient, Set.image_congr, Set.image_id, _root_, _root_.Quotient.fintype, conv_rhs, fintype, image_congr, image_id, mem_fixingSubgroup_iff, mem_stabilizer_iff
-/
theorem MulAction.fixingSubgroup_le_stabilizer (s : Set α) :
    fixingSubgroup G s <= stabilizer G s := by
  intro k hk
  rw [mem_stabilizer_iff]
  conv_rhs => rw [← Set.image_id s]
  apply Set.image_congr
  simpa only [mem_fixingSubgroup_iff, id] using hk

end Pointwise
