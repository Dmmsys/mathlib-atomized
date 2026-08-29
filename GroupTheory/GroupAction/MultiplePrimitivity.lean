/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup

/-! # Multiply preprimitive actions

Let `G` be a group acting on a type `α`.

* `MulAction.IsMultiplyPreprimitive` :
  The action is said to be `n`-primitive if, for every subset `s :
  Set α` with `n` elements, the actions f `stabilizer G s` on the
  complement of `s` is primitive.

* `MulAction.is_zero_preprimitive` : any action is 0-primitive

* `MulAction.is_one_preprimitive_iff` : an action is 1-primitive if and only if it is primitive

* `MulAction.isMultiplyPreprimitive_ofStabilizer`: if an action is `n + 1`-primitive,
  then the action of `stabilizer G a` on the complement of `{a}` is `n`-primitive.

* `MulAction.isMultiplyPreprimitive_succ_iff_ofStabilizer` :
  for `1 ≤ n`, an action is `n + 1`-primitive, then the action
  of `stabilizer G a` on the complement of `{a}` is `n`-primitive.
  ofFixingSubgroup.isMultiplyPreprimitive

* `MulAction.ofFixingSubgroup.isMultiplyPreprimitive`:
  If an action is `s.ncard + m`-primitive, then
  the action of `FixingSubgroup G s` on the complement of `s`
  is `m`-primitive.

-/

public section

open scoped Pointwise Cardinal

namespace MulAction

open SubMulAction

section Preprimitive

variable {G : Type*} [Group G] {α : Type*} [MulAction G α]

-- Rewriting lemmas for transitivity or primitivity

@[to_additive]
/--
theorem `isPreprimitive_of_fixingSubgroup_empty_iff` / 定理 `isPreprimitive_of_fixingSubgroup_empty_iff`

English:
theorem isPreprimitive_of_fixingSubgroup_empty_iff
  proof: isPreprimitive_congr
    of_fixingSubgroupEmpty_mapScalars_surjective
    ofFixingSubgroupEmpty_equivariantMap_bijective

@[to_additive]

中文:
定理 isPreprimitive_of_fixingSubgroup_empty_iff
  证明: isPreprimitive_congr
    of_fixingSubgroupEmpty_mapScalars_surjective
    ofFixingSubgroupEmpty_equivariantMap_bijective

@[to_additive]

Depends on / 依赖: isPreprimitive_congr, ofFixingSubgroupEmpty_equivariantMap_bijective, of_fixingSubgroupEmpty_mapScalars_surjective
-/
theorem isPreprimitive_of_fixingSubgroup_empty_iff :
    IsPreprimitive ↥(fixingSubgroup G (∅ : Set α))
    ↥(ofFixingSubgroup G (∅ : Set α)) ↔ IsPreprimitive G α :=
  isPreprimitive_congr
    of_fixingSubgroupEmpty_mapScalars_surjective
    ofFixingSubgroupEmpty_equivariantMap_bijective

@[to_additive]
/--
theorem `isPreprimitive_ofFixingSubgroup_conj_iff` / 定理 `isPreprimitive_ofFixingSubgroup_conj_iff`

English:
theorem isPreprimitive_ofFixingSubgroup_conj_iff
  given: {s : Set α} {g : G}
  proof: isPreprimitive_congr
    (fixingSubgroupEquivFixingSubgroup rfl).surjective
    conjMap_ofFixingSubgroup_bijective

@[to_additive]

中文:
定理 isPreprimitive_ofFixingSubgroup_conj_iff
  条件: {s : 集合 α} {g : G}
  证明: isPreprimitive_congr
    (fixingSubgroupEquivFixingSubgroup rfl).surjective
    conjMap_ofFixingSubgroup_bijective

@[to_additive]

Depends on / 依赖: conjMap_ofFixingSubgroup_bijective, fixingSubgroupEquivFixingSubgroup, isPreprimitive_congr, surjective
-/
theorem isPreprimitive_ofFixingSubgroup_conj_iff {s : Set α} {g : G} :
    IsPreprimitive (fixingSubgroup G s) (ofFixingSubgroup G s) ↔
      IsPreprimitive (fixingSubgroup G (g • s)) (ofFixingSubgroup G (g • s)) :=
  isPreprimitive_congr
    (fixingSubgroupEquivFixingSubgroup rfl).surjective
    conjMap_ofFixingSubgroup_bijective

@[to_additive]
/--
theorem `isPreprimitive_fixingSubgroup_insert_iff` / 定理 `isPreprimitive_fixingSubgroup_insert_iff`

English:
theorem isPreprimitive_fixingSubgroup_insert_iff
  given: {a : α} {t : Set (ofStabilizer G a)}
  proof: isPreprimitive_congr (fixingSubgroupInsertEquiv a t).surjective
    ofFixingSubgroup_insert_map_bijective

中文:
定理 isPreprimitive_fixingSubgroup_insert_iff
  条件: {a : α} {t : 集合 (ofStabilizer G a)}
  证明: isPreprimitive_congr (fixingSubgroupInsertEquiv a t).surjective
    ofFixingSubgroup_insert_map_bijective

Depends on / 依赖: fixingSubgroupInsertEquiv, isPreprimitive_congr, ofFixingSubgroup_insert_map_bijective, surjective
-/
theorem isPreprimitive_fixingSubgroup_insert_iff {a : α} {t : Set (ofStabilizer G a)} :
    IsPreprimitive ↥(fixingSubgroup G (insert a (Subtype.val '' t)))
      ↥(ofFixingSubgroup G (insert a (Subtype.val '' t))) ↔
      IsPreprimitive (fixingSubgroup (stabilizer G a) t)
        (ofFixingSubgroup (stabilizer G a) t) :=
  isPreprimitive_congr (fixingSubgroupInsertEquiv a t).surjective
    ofFixingSubgroup_insert_map_bijective

end Preprimitive

/-- An additive action is `n`-multiply preprimitive if it is `n`-multiply pretransitive
  and if, when `n ≥ 1`, for every set `s` of cardinality `n - 1`,
  the action of `fixingAddSubgroup M s` on the complement of `s` is preprimitive. -/
@[mk_iff]
/--
Definition of `_root_.AddAction.IsMultiplyPreprimitive` / `_root_.AddAction.IsMultiplyPreprimitive` 的定义

English:
class _root_.AddAction.IsMultiplyPreprimitive
  axioms and operations (2):
    - isMultiplyPretransitive((M α n)) : AddAction.IsMultiplyPretransitive M α n
    - isPreprimitive_ofFixingAddSubgroup((M n) {s : Set α} (hs : s.encard + 1 = n)) : AddAction.IsPreprimitive (fixingAddSubgroup M s) (SubAddAction.ofFixingAddSubgroup M s)

中文:
类 _root_.加法作用.是MultiplyPreprimitive
  公理与运算 (2 个):
    - isMultiplyPretransitive((M α n)) : 加法作用.IsMultiplyPretransitive M α n
    - isPreprimitive_ofFixingAddSubgroup((M n) {s : 集合 α} (hs : s.encard + 1 = n)) : 加法作用.是Preprimitive (fixingAddSubgroup M s) (SubAdd作用.ofFixingAddSubgroup M s)
-/
class _root_.AddAction.IsMultiplyPreprimitive
    (M α : Type*) [AddGroup M] [AddAction M α] (n : Nat) where
  /-- An `n`-preprimitive action is `n`-pretransitive. -/
  isMultiplyPretransitive (M α n) : AddAction.IsMultiplyPretransitive M α n
  /-- In an `n`-preprimitive action, the action of `fixingAddSubgroup M s`
  on `ofFixingAddSubgroup M s` is preprimitive, for all sets `s` such that `s.encard + 1 = n`. -/
  isPreprimitive_ofFixingAddSubgroup (M n) {s : Set α} (hs : s.encard + 1 = n) :
    AddAction.IsPreprimitive (fixingAddSubgroup M s) (SubAddAction.ofFixingAddSubgroup M s)

/-- A group action is `n`-multiply preprimitive if it is `n`-multiply
pretransitive and if, when `n ≥ 1`, for every set `s` of cardinality
`n - 1`, the action of `fixingSubgroup M s` on the complement of `s`
is preprimitive. -/
@[mk_iff, to_additive existing]
/--
Definition of `IsMultiplyPreprimitive` / `IsMultiplyPreprimitive` 的定义

English:
class IsMultiplyPreprimitive
  parameters: (M α : Type*) [Group M] [MulAction M α] (n : Nat)
  axioms and operations (2):
    - isMultiplyPretransitive((M α n)) : IsMultiplyPretransitive M α n
    - isPreprimitive_ofFixingSubgroup((M n) {s : Set α} (hs : s.encard + 1 = n)) : IsPreprimitive (fixingSubgroup M s) (ofFixingSubgroup M s)

中文:
类 是MultiplyPreprimitive
  参数: (M α : 类型) [群 M] [乘法作用 M α] (n : 自然数)
  公理与运算 (2 个):
    - isMultiplyPretransitive((M α n)) : IsMultiplyPretransitive M α n
    - isPreprimitive_ofFixingSubgroup((M n) {s : 集合 α} (hs : s.encard + 1 = n)) : 是Preprimitive (fixingSubgroup M s) (ofFixingSubgroup M s)
-/
class IsMultiplyPreprimitive (M α : Type*) [Group M] [MulAction M α] (n : Nat) where
  /-- An `n`-preprimitive action is `n`-pretransitive. -/
  isMultiplyPretransitive (M α n) : IsMultiplyPretransitive M α n
  /-- In an `n`-preprimitive action, the action of `fixingSubgroup M s` on `ofFixingSubgroup M s`
  is preprimitive, for all sets `s` such that `s.encard + 1 = n`. -/
  isPreprimitive_ofFixingSubgroup (M n) {s : Set α} (hs : s.encard + 1 = n) :
    IsPreprimitive (fixingSubgroup M s) (ofFixingSubgroup M s)

variable (M α : Type*) [Group M] [MulAction M α]

@[to_additive]
instance (n : Nat) [IsMultiplyPreprimitive M α n] :
    IsMultiplyPretransitive M α n :=
  IsMultiplyPreprimitive.isMultiplyPretransitive M α n

/-- Any action is `0`-preprimitive. -/
@[to_additive /-- Any action is `0`-preprimitive. -/]
/--
theorem `is_zero_preprimitive` / 定理 `is_zero_preprimitive`

English:
theorem is_zero_preprimitive
  statement: IsMultiplyPreprimitive M α 0 where
  proof: MulAction.is_zero_pretransitive
  isPreprimitive_ofFixingSubgroup hs := by simp at hs

中文:
定理 is_zero_preprimitive
  结论: 是MultiplyPreprimitive M α 0 where
  证明: MulAction.is_zero_pretransitive
  isPreprimitive_ofFixingSubgroup hs := by simp at hs

Depends on / 依赖: MulAction, MulAction.is_zero_pretransitive, is_zero_pretransitive, toMatrix
-/
theorem is_zero_preprimitive : IsMultiplyPreprimitive M α 0 where
  isMultiplyPretransitive := MulAction.is_zero_pretransitive
  isPreprimitive_ofFixingSubgroup hs := by simp at hs

/-- An action is preprimitive iff it is `1`-preprimitive. -/
@[to_additive
/-- An action is preprimitive iff it is `1`-preprimitive. -/]
/--
theorem `is_one_preprimitive_iff` / 定理 `is_one_preprimitive_iff`

English:
theorem is_one_preprimitive_iff
  proof: by
  constructor
  · intro H1
    rw [← isPreprimitive_of_fixingSubgroup_empty_iff]
    apply H1.isPreprimitive_ofFixingSubgroup (by simp)
  · intro h
    rw [isMultiplyPreprimitive_iff]
    constructor
    · exact is_one_pretransitive_iff.mpr h.toIsPretransitive
    · simpa using isPreprimitive_of_fixingSubgroup_empty_iff.mpr h

中文:
定理 is_one_preprimitive_iff
  证明: by
  constructor
  · intro H1
    rw [← isPreprimitive_of_fixingSubgroup_empty_iff]
    apply H1.isPreprimitive_ofFixingSubgroup (by simp)
  · intro h
    rw [isMultiplyPreprimitive_iff]
    constructor
    · exact is_one_pretransitive_iff.mpr h.toIsPretransitive
    · simpa using isPreprimitive_of_fixingSubgroup_empty_iff.mpr h

Depends on / 依赖: H1.isPreprimitive_ofFixingSubgroup, h.toIsPretransitive, isMultiplyPreprimitive_iff, isPreprimitive_ofFixingSubgroup, isPreprimitive_of_fixingSubgroup_empty_iff, isPreprimitive_of_fixingSubgroup_empty_iff.mpr, is_one_pretransitive_iff, is_one_pretransitive_iff.mpr, toIsPretransitive
-/
theorem is_one_preprimitive_iff :
    IsMultiplyPreprimitive M α 1 ↔ IsPreprimitive M α := by
  constructor
  · intro H1
    rw [← isPreprimitive_of_fixingSubgroup_empty_iff]
    apply H1.isPreprimitive_ofFixingSubgroup (by simp)
  · intro h
    rw [isMultiplyPreprimitive_iff]
    constructor
    · exact is_one_pretransitive_iff.mpr h.toIsPretransitive
    · simpa using isPreprimitive_of_fixingSubgroup_empty_iff.mpr h

/-- The action of `stabilizer M a` is one-less preprimitive. -/
@[to_additive /-- The action of `stabilizer M a` is one-less preprimitive. -/]
/--
theorem `isMultiplyPreprimitive_ofStabilizer` / 定理 `isMultiplyPreprimitive_ofStabilizer`

English:
theorem isMultiplyPreprimitive_ofStabilizer
  proof: by
  rcases Nat.lt_or_ge n 1 with h0 | h1
  · rw [Nat.lt_one_iff] at h0
    rw [h0]
    apply is_zero_preprimitive
  rw [isMultiplyPreprimitive_iff]
  constructor
  · rw [← ofStabilizer.isMultiplyPretransitive]
    exact IsMultiplyPreprimitive.isMultiplyPretransitive M α n.succ
  · intro s hs
    have : IsPreprimitive ↥(fixingSubgroup M (insert a (Subtype.val '' s)))
      ↥(ofFixingSubgroup M (insert a (Subtype.val '' s))) := by
      apply IsMultiplyPreprimitive.isPreprimitive_ofFixingSubgroup M n.succ
      rw [Set.encard_insert_of_notMem]; rw [Subtype.coe_injective.encard_image]; rw [hs]; rw [Nat.cast_succ]
      aesop
    exact IsPreprimitive.of_surjective ofFixingSubgroup_insert_map_bijective.surjective

中文:
定理 isMultiplyPreprimitive_ofStabilizer
  证明: by
  rcases Nat.lt_or_ge n 1 with h0 | h1
  · rw [Nat.lt_one_iff] at h0
    rw [h0]
    apply is_zero_preprimitive
  rw [isMultiplyPreprimitive_iff]
  constructor
  · rw [← ofStabilizer.isMultiplyPretransitive]
    exact IsMultiplyPreprimitive.isMultiplyPretransitive M α n.succ
  · intro s hs
    have : IsPreprimitive ↥(fixingSubgroup M (insert a (Subtype.val '' s)))
      ↥(ofFixingSubgroup M (insert a (Subtype.val '' s))) := by
      apply IsMultiplyPreprimitive.isPreprimitive_ofFixingSubgroup M n.succ
      rw [Set.encard_insert_of_notMem]; rw [Subtype.coe_injective.encard_image]; rw [hs]; rw [Nat.cast_succ]
      aesop
    exact IsPreprimitive.of_surjective ofFixingSubgroup_insert_map_bijective.surjective

Depends on / 依赖: IsMultiplyPreprimitive, IsMultiplyPreprimitive.isMultiplyPretransitive, IsMultiplyPreprimitive.isPreprimitive_ofFixingSubgroup, IsPreprimitive, LinearMap, LinearMap.toMatrix, Nat.lt_one_iff, Nat.lt_or_ge, QuadraticMap, QuadraticMap.associated_comp, Set.encard_insert_of_notMe, Subtype, Subtype.val, associated_comp, encard_insert_of_notMe, fixingSubgroup, insert, isMultiplyPreprimitive_iff, isMultiplyPretransitive, isPreprimitive_ofFixingSubgroup
-/
theorem isMultiplyPreprimitive_ofStabilizer
    [IsPretransitive M α] {n : Nat} {a : α} [IsMultiplyPreprimitive M α n.succ] :
    IsMultiplyPreprimitive (stabilizer M a) (SubMulAction.ofStabilizer M a) n := by
  rcases Nat.lt_or_ge n 1 with h0 | h1
  · rw [Nat.lt_one_iff] at h0
    rw [h0]
    apply is_zero_preprimitive
  rw [isMultiplyPreprimitive_iff]
  constructor
  · rw [← ofStabilizer.isMultiplyPretransitive]
    exact IsMultiplyPreprimitive.isMultiplyPretransitive M α n.succ
  · intro s hs
    have : IsPreprimitive ↥(fixingSubgroup M (insert a (Subtype.val '' s)))
      ↥(ofFixingSubgroup M (insert a (Subtype.val '' s))) := by
      apply IsMultiplyPreprimitive.isPreprimitive_ofFixingSubgroup M n.succ
      rw [Set.encard_insert_of_notMem]; rw [Subtype.coe_injective.encard_image]; rw [hs]; rw [Nat.cast_succ]
      aesop
    exact IsPreprimitive.of_surjective ofFixingSubgroup_insert_map_bijective.surjective

/-- A pretransitive action is `n.succ-`preprimitive
iff the action of stabilizers is `n`-preprimitive. -/
@[to_additive /-- A pretransitive action is `n.succ-`preprimitive
iff the action of stabilizers is `n`-preprimitive. -/]
/--
theorem `isMultiplyPreprimitive_succ_iff_ofStabilizer` / 定理 `isMultiplyPreprimitive_succ_iff_ofStabilizer`

English:
theorem isMultiplyPreprimitive_succ_iff_ofStabilizer
  proof: by
  constructor
  · apply isMultiplyPreprimitive_ofStabilizer
  · intro H
    rw [isMultiplyPreprimitive_iff]
    constructor
    · exact ofStabilizer.isMultiplyPretransitive.mpr H.isMultiplyPretransitive
    · intro s hs
      have : exists b : α, b in s := by
        rw [← Set.nonempty_def]; rw [Set.nonempty_iff_ne_empty]
        intro h
        apply not_lt.mpr hn
        rw [h]; rw [Set.encard_empty]; rw [zero_add]; rw [← Nat.cast_one]; rw [Nat.cast_inj]; rw [Nat.succ_inj] at hs
        simp only [← hs, zero_lt_one]
      obtain ⟨b, hb⟩ := this
      obtain ⟨g, hg : g • b = a⟩ := exists_smul_eq M b a
      rw [isPreprimitive_ofFixingSubgroup_conj_iff (g := g)]
      set s' := g • s with hs'
      let t : Set (SubMulAction.ofStabilizer M a) := Subtype.val ⁻¹' s'
      have hst : s' = insert a (Subtype.val '' t) := by
        ext x
        constructor
        · intro hxs
          by_cases hxa : x = a
          · simp [hxa]
          · exact Set.mem_insert_of_mem _
              ⟨⟨x, hxa⟩, by simp only [t, Set.mem_preimage]; exact hxs, rfl⟩
        · rw [Set.mem_insert_iff]
          rintro (⟨rfl⟩ | ⟨y, hy, rfl⟩)
          · simpa [s', ← hg]
          · simpa only using! hy
      rw [hst]; rw [isPreprimitive_fixingSubgroup_insert_iff]
      apply IsMultiplyPreprimitive.isPreprimitive_ofFixingSubgroup _ n
      apply ENat.add_left_injective_of_ne_top ENat.one_ne_top
      simp only
      rw [← Nat.cast_one]; rw [← Nat.cast_add]; rw [← hs]
      apply congr_arg₂ _ _ rfl
      rw [show s = g⁻¹ • s' by simp [hs'],
        ← Set.image_smul, (MulAction.injective g⁻¹).encard_image, hst]
      rw [Set.encard_insert_of_notMem]; rw [Subtype.coe_injective.encard_image]; rw [ENat.natCast_one]
      exact notMem_val_image M t

中文:
定理 isMultiplyPreprimitive_succ_iff_ofStabilizer
  证明: by
  constructor
  · apply isMultiplyPreprimitive_ofStabilizer
  · intro H
    rw [isMultiplyPreprimitive_iff]
    constructor
    · exact ofStabilizer.isMultiplyPretransitive.mpr H.isMultiplyPretransitive
    · intro s hs
      have : exists b : α, b in s := by
        rw [← Set.nonempty_def]; rw [Set.nonempty_iff_ne_empty]
        intro h
        apply not_lt.mpr hn
        rw [h]; rw [Set.encard_empty]; rw [zero_add]; rw [← Nat.cast_one]; rw [Nat.cast_inj]; rw [Nat.succ_inj] at hs
        simp only [← hs, zero_lt_one]
      obtain ⟨b, hb⟩ := this
      obtain ⟨g, hg : g • b = a⟩ := exists_smul_eq M b a
      rw [isPreprimitive_ofFixingSubgroup_conj_iff (g := g)]
      set s' := g • s with hs'
      let t : Set (SubMulAction.ofStabilizer M a) := Subtype.val ⁻¹' s'
      have hst : s' = insert a (Subtype.val '' t) := by
        ext x
        constructor
        · intro hxs
          by_cases hxa : x = a
          · simp [hxa]
          · exact Set.mem_insert_of_mem _
              ⟨⟨x, hxa⟩, by simp only [t, Set.mem_preimage]; exact hxs, rfl⟩
        · rw [Set.mem_insert_iff]
          rintro (⟨rfl⟩ | ⟨y, hy, rfl⟩)
          · simpa [s', ← hg]
          · simpa only using! hy
      rw [hst]; rw [isPreprimitive_fixingSubgroup_insert_iff]
      apply IsMultiplyPreprimitive.isPreprimitive_ofFixingSubgroup _ n
      apply ENat.add_left_injective_of_ne_top ENat.one_ne_top
      simp only
      rw [← Nat.cast_one]; rw [← Nat.cast_add]; rw [← hs]
      apply congr_arg₂ _ _ rfl
      rw [show s = g⁻¹ • s' by simp [hs'],
        ← Set.image_smul, (MulAction.injective g⁻¹).encard_image, hst]
      rw [Set.encard_insert_of_notMem]; rw [Subtype.coe_injective.encard_image]; rw [ENat.natCast_one]
      exact notMem_val_image M t

Depends on / 依赖: H.isMultiplyPretransitive, Nat.cast_inj, Nat.cast_one, Nat.succ_inj, Set.encard_empty, Set.nonempty_def, Set.nonempty_iff_ne_empty, cast_inj, cast_one, encard_empty, isMultiplyPreprimitive_iff, isMultiplyPreprimitive_ofStabilizer, isMultiplyPretransitive, nonempty_def, nonempty_iff_ne_empty, not_lt, not_lt.mpr, ofStabilizer, ofStabilizer.isMultiplyPretransitive.mpr, succ_inj
-/
theorem isMultiplyPreprimitive_succ_iff_ofStabilizer
    [IsPretransitive M α] {n : Nat} (hn : 1 <= n) {a : α} :
    IsMultiplyPreprimitive M α n.succ ↔
      IsMultiplyPreprimitive (stabilizer M a) (SubMulAction.ofStabilizer M a) n := by
  constructor
  · apply isMultiplyPreprimitive_ofStabilizer
  · intro H
    rw [isMultiplyPreprimitive_iff]
    constructor
    · exact ofStabilizer.isMultiplyPretransitive.mpr H.isMultiplyPretransitive
    · intro s hs
      have : exists b : α, b in s := by
        rw [← Set.nonempty_def]; rw [Set.nonempty_iff_ne_empty]
        intro h
        apply not_lt.mpr hn
        rw [h]; rw [Set.encard_empty]; rw [zero_add]; rw [← Nat.cast_one]; rw [Nat.cast_inj]; rw [Nat.succ_inj] at hs
        simp only [← hs, zero_lt_one]
      obtain ⟨b, hb⟩ := this
      obtain ⟨g, hg : g • b = a⟩ := exists_smul_eq M b a
      rw [isPreprimitive_ofFixingSubgroup_conj_iff (g := g)]
      set s' := g • s with hs'
      let t : Set (SubMulAction.ofStabilizer M a) := Subtype.val ⁻¹' s'
      have hst : s' = insert a (Subtype.val '' t) := by
        ext x
        constructor
        · intro hxs
          by_cases hxa : x = a
          · simp [hxa]
          · exact Set.mem_insert_of_mem _
              ⟨⟨x, hxa⟩, by simp only [t, Set.mem_preimage]; exact hxs, rfl⟩
        · rw [Set.mem_insert_iff]
          rintro (⟨rfl⟩ | ⟨y, hy, rfl⟩)
          · simpa [s', ← hg]
          · simpa only using! hy
      rw [hst]; rw [isPreprimitive_fixingSubgroup_insert_iff]
      apply IsMultiplyPreprimitive.isPreprimitive_ofFixingSubgroup _ n
      apply ENat.add_left_injective_of_ne_top ENat.one_ne_top
      simp only
      rw [← Nat.cast_one]; rw [← Nat.cast_add]; rw [← hs]
      apply congr_arg₂ _ _ rfl
      rw [show s = g⁻¹ • s' by simp [hs'],
        ← Set.image_smul, (MulAction.injective g⁻¹).encard_image, hst]
      rw [Set.encard_insert_of_notMem]; rw [Subtype.coe_injective.encard_image]; rw [ENat.natCast_one]
      exact notMem_val_image M t

/-- The fixator of a subset of cardinal `d` in an `n`-primitive action
acts `n-d`-primitively on the remaining (`d ≤ n`). -/
@[to_additive
/-- The fixator of a subset of cardinal `d` in an `n`-primitive action
acts `n-d`-primitively on the remaining (`d ≤ n`). -/]
/--
theorem `ofFixingSubgroup.isMultiplyPreprimitive` / 定理 `ofFixingSubgroup.isMultiplyPreprimitive`

English:
theorem ofFixingSubgroup.isMultiplyPreprimitive
  proof: by
    apply ofFixingSubgroup.isMultiplyPretransitive _ s hs
  isPreprimitive_ofFixingSubgroup {t} ht := by
    let t' : Set α := Subtype.val '' t
    have htt' : t = Subtype.val ⁻¹' t' :=
      (Set.preimage_image_eq _ Subtype.coe_injective).symm
    rw [htt']
    suffices IsPreprimitive (fixingSubgroup M (s union t')) (ofFixingSubgroup M (s union t')) by
      apply IsPreprimitive.of_surjective map_ofFixingSubgroupUnion_bijective.surjective
    apply IsMultiplyPreprimitive.isPreprimitive_ofFixingSubgroup _ n
    rw [Set.encard_union_eq _]
    · rw [Subtype.coe_injective.encard_image, add_assoc, ht,
        ← hs, Nat.cast_add, Set.Finite.cast_ncard_eq]
      exact Set.toFinite s
    · apply disjoint_val_image

中文:
定理 ofFixingSubgroup.isMultiplyPreprimitive
  证明: by
    apply ofFixingSubgroup.isMultiplyPretransitive _ s hs
  isPreprimitive_ofFixingSubgroup {t} ht := by
    let t' : Set α := Subtype.val '' t
    have htt' : t = Subtype.val ⁻¹' t' :=
      (Set.preimage_image_eq _ Subtype.coe_injective).symm
    rw [htt']
    suffices IsPreprimitive (fixingSubgroup M (s union t')) (ofFixingSubgroup M (s union t')) by
      apply IsPreprimitive.of_surjective map_ofFixingSubgroupUnion_bijective.surjective
    apply IsMultiplyPreprimitive.isPreprimitive_ofFixingSubgroup _ n
    rw [Set.encard_union_eq _]
    · rw [Subtype.coe_injective.encard_image, add_assoc, ht,
        ← hs, Nat.cast_add, Set.Finite.cast_ncard_eq]
      exact Set.toFinite s
    · apply disjoint_val_image

Depends on / 依赖: IsMultiplyPreprimitive, IsMultiplyPreprimitive.isPreprimitive_ofFixingSubgroup, IsPreprimitive, IsPreprimitive.of_surjective, Set.encard_union_e, Set.preimage_image_eq, Subtype, Subtype.coe_injective, Subtype.val, coe_injective, encard_union_e, fixingSubgroup, isMultiplyPretransitive, isPreprimitive_ofFixingSubgroup, map_ofFixingSubgroupUnion_bijective, map_ofFixingSubgroupUnion_bijective.surjective, ofFixingSubgroup, ofFixingSubgroup.isMultiplyPretransitive, of_surjective, preimage_image_eq
-/
theorem ofFixingSubgroup.isMultiplyPreprimitive
    {m n : Nat} [IsMultiplyPreprimitive M α n] {s : Set α} [Finite s] (hs : s.ncard + m = n) :
    IsMultiplyPreprimitive (fixingSubgroup M s) (SubMulAction.ofFixingSubgroup M s) m where
  isMultiplyPretransitive := by
    apply ofFixingSubgroup.isMultiplyPretransitive _ s hs
  isPreprimitive_ofFixingSubgroup {t} ht := by
    let t' : Set α := Subtype.val '' t
    have htt' : t = Subtype.val ⁻¹' t' :=
      (Set.preimage_image_eq _ Subtype.coe_injective).symm
    rw [htt']
    suffices IsPreprimitive (fixingSubgroup M (s union t')) (ofFixingSubgroup M (s union t')) by
      apply IsPreprimitive.of_surjective map_ofFixingSubgroupUnion_bijective.surjective
    apply IsMultiplyPreprimitive.isPreprimitive_ofFixingSubgroup _ n
    rw [Set.encard_union_eq _]
    · rw [Subtype.coe_injective.encard_image, add_assoc, ht,
        ← hs, Nat.cast_add, Set.Finite.cast_ncard_eq]
      exact Set.toFinite s
    · apply disjoint_val_image

/-- `n.succ`-pretransitivity implies `n`-preprimitivity. -/
@[to_additive /-- `n.succ`-pretransitivity implies `n`-preprimitivity. -/]
/--
theorem `isMultiplyPreprimitive_of_isMultiplyPretransitive_succ` / 定理 `isMultiplyPreprimitive_of_isMultiplyPretransitive_succ`

English:
theorem isMultiplyPreprimitive_of_isMultiplyPretransitive_succ
  statement: {n : Nat}
  proof: by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [hn]
    exact is_zero_preprimitive M α
  rw [isMultiplyPreprimitive_iff]
  constructor
  · exact isMultiplyPretransitive_of_le' (Nat.le_succ n) hα
  · intro s hs
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
    apply isPreprimitive_of_is_two_pretransitive
    have hs' : s.encard = m := by
      simp only [hm, Nat.succ_eq_add_one, zero_add, add_comm 1] at hs
      exact ENat.add_left_injective_of_ne_top ENat.one_ne_top hs
    have : Finite s := Set.finite_of_encard_eq_coe hs'
    apply ofFixingSubgroup.isMultiplyPretransitive (G := M) s (n := n.succ)
    simp [Set.ncard, hs', hm, add_comm 1]

中文:
定理 isMultiplyPreprimitive_of_isMultiplyPretransitive_succ
  结论: {n : 自然数}
  证明: by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [hn]
    exact is_zero_preprimitive M α
  rw [isMultiplyPreprimitive_iff]
  constructor
  · exact isMultiplyPretransitive_of_le' (Nat.le_succ n) hα
  · intro s hs
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
    apply isPreprimitive_of_is_two_pretransitive
    have hs' : s.encard = m := by
      simp only [hm, Nat.succ_eq_add_one, zero_add, add_comm 1] at hs
      exact ENat.add_left_injective_of_ne_top ENat.one_ne_top hs
    have : Finite s := Set.finite_of_encard_eq_coe hs'
    apply ofFixingSubgroup.isMultiplyPretransitive (G := M) s (n := n.succ)
    simp [Set.ncard, hs', hm, add_comm 1]

Depends on / 依赖: ENat.add_left_injective_of_ne_top, ENat.one_ne_top, Finite, Nat.eq_zero_or_pos, Nat.exists_eq_add_of_le, Nat.le_succ, Nat.succ_eq_add_one, Set.finite_of_encard_eq_coe, add_comm, add_left_injective_of_ne_top, encard, eq_zero_or_pos, exists_eq_add_of_le, finite_of_encard_eq_coe, isMultiplyPreprimitive_iff, isMultiplyPretransitive_of_le, isPreprimitive_of_is_two_pretransitive, is_zero_preprimitive, le_succ, one_ne_top
-/
theorem isMultiplyPreprimitive_of_isMultiplyPretransitive_succ {n : Nat}
    (hα : ↑n.succ <= ENat.card α) [IsMultiplyPretransitive M α n.succ] :
    IsMultiplyPreprimitive M α n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [hn]
    exact is_zero_preprimitive M α
  rw [isMultiplyPreprimitive_iff]
  constructor
  · exact isMultiplyPretransitive_of_le' (Nat.le_succ n) hα
  · intro s hs
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
    apply isPreprimitive_of_is_two_pretransitive
    have hs' : s.encard = m := by
      simp only [hm, Nat.succ_eq_add_one, zero_add, add_comm 1] at hs
      exact ENat.add_left_injective_of_ne_top ENat.one_ne_top hs
    have : Finite s := Set.finite_of_encard_eq_coe hs'
    apply ofFixingSubgroup.isMultiplyPretransitive (G := M) s (n := n.succ)
    simp [Set.ncard, hs', hm, add_comm 1]

/-- An `n`-preprimitive action is `m`-preprimitive for `m ≤ n`. -/
@[to_additive /-- An `n`-preprimitive action is `m`-preprimitive for `m ≤ n`. -/]
/--
theorem `isMultiplyPreprimitive_of_le` / 定理 `isMultiplyPreprimitive_of_le`

English:
theorem isMultiplyPreprimitive_of_le
  proof: by
  induction n with
  | zero => rw [Nat.eq_zero_of_le_zero hmn]; exact hn
  | succ n hrec =>
    rcases Nat.eq_or_lt_of_le hmn with hmn | hmn'
    · rw [hmn]; exact hn
    · apply hrec
        (isMultiplyPreprimitive_of_isMultiplyPretransitive_succ M α hα)
        (Nat.lt_succ_iff.mp hmn')
      · refine le_trans ?_ hα; rw [ENat.natCast_le_natCast]; exact Nat.le_succ n

中文:
定理 isMultiplyPreprimitive_of_le
  证明: by
  induction n with
  | zero => rw [Nat.eq_zero_of_le_zero hmn]; exact hn
  | succ n hrec =>
    rcases Nat.eq_or_lt_of_le hmn with hmn | hmn'
    · rw [hmn]; exact hn
    · apply hrec
        (isMultiplyPreprimitive_of_isMultiplyPretransitive_succ M α hα)
        (Nat.lt_succ_iff.mp hmn')
      · refine le_trans ?_ hα; rw [ENat.natCast_le_natCast]; exact Nat.le_succ n

Depends on / 依赖: ENat.natCast_le_natCast, Nat.eq_or_lt_of_le, Nat.eq_zero_of_le_zero, Nat.le_succ, Nat.lt_succ_iff.mp, eq_or_lt_of_le, eq_zero_of_le_zero, isMultiplyPreprimitive_of_isMultiplyPretransitive_succ, le_succ, le_trans, lt_succ_iff, natCast_le_natCast
-/
theorem isMultiplyPreprimitive_of_le
    {n : Nat} (hn : IsMultiplyPreprimitive M α n)
    {m : Nat} (hmn : m <= n) (hα : ↑n <= ENat.card α) :
    IsMultiplyPreprimitive M α m := by
  induction n with
  | zero => rw [Nat.eq_zero_of_le_zero hmn]; exact hn
  | succ n hrec =>
    rcases Nat.eq_or_lt_of_le hmn with hmn | hmn'
    · rw [hmn]; exact hn
    · apply hrec
        (isMultiplyPreprimitive_of_isMultiplyPretransitive_succ M α hα)
        (Nat.lt_succ_iff.mp hmn')
      · refine le_trans ?_ hα; rw [ENat.natCast_le_natCast]; exact Nat.le_succ n

variable {M α}

@[to_additive]
/--
theorem `IsMultiplyPreprimitive.of_bijective_map` / 定理 `IsMultiplyPreprimitive.of_bijective_map`

English:
theorem IsMultiplyPreprimitive.of_bijective_map
  proof: IsPretransitive.of_embedding hf.surjective
  isPreprimitive_ofFixingSubgroup {t} ht := by
    let s := f ⁻¹' t
    have hs' : f '' s = t := Set.image_preimage_eq t hf.surjective
    let φ' : fixingSubgroup M s -> fixingSubgroup N t := fun ⟨m, hm⟩ =>
      ⟨φ m, fun ⟨y, hy⟩ => by
        rw [← hs']; rw [Set.mem_image] at hy
        obtain ⟨x, hx, hx'⟩ := hy
        simp only
        rw [← hx']; rw [← map_smulₛₗ]
        apply congr_arg
        rw [mem_fixingSubgroup_iff] at hm
        exact hm x hx⟩
    let f' : SubMulAction.ofFixingSubgroup M s ->ₑ[φ'] SubMulAction.ofFixingSubgroup N t :=
      { toFun := fun ⟨x, hx⟩ => ⟨f.toFun x, fun h => hx (Set.mem_preimage.mp h)⟩
        map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ =>
          by
          rw [← SetLike.coe_eq_coe]
          exact f.map_smul' m x }
    have hf' : Function.Surjective f' := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx⟩ := hf.right y
      use ⟨x, ?_⟩
      · simpa only [f', ← Subtype.coe_inj] using! hx
      · intro h
        apply hy
        rw [← hs']
        exact ⟨x, h, hx⟩
    have : IsPreprimitive (fixingSubgroup M s) (ofFixingSubgroup M s) :=
      IsMultiplyPreprimitive.isPreprimitive_ofFixingSubgroup _ n
        (by rw [← ht, ← hs', hf.injective.encard_image])
    exact IsPreprimitive.of_surjective (f := f') (φ := φ') hf'

@[to_additive]

中文:
定理 是MultiplyPreprimitive.of_bijective_map
  证明: IsPretransitive.of_embedding hf.surjective
  isPreprimitive_ofFixingSubgroup {t} ht := by
    let s := f ⁻¹' t
    have hs' : f '' s = t := Set.image_preimage_eq t hf.surjective
    let φ' : fixingSubgroup M s -> fixingSubgroup N t := fun ⟨m, hm⟩ =>
      ⟨φ m, fun ⟨y, hy⟩ => by
        rw [← hs']; rw [Set.mem_image] at hy
        obtain ⟨x, hx, hx'⟩ := hy
        simp only
        rw [← hx']; rw [← map_smulₛₗ]
        apply congr_arg
        rw [mem_fixingSubgroup_iff] at hm
        exact hm x hx⟩
    let f' : SubMulAction.ofFixingSubgroup M s ->ₑ[φ'] SubMulAction.ofFixingSubgroup N t :=
      { toFun := fun ⟨x, hx⟩ => ⟨f.toFun x, fun h => hx (Set.mem_preimage.mp h)⟩
        map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ =>
          by
          rw [← SetLike.coe_eq_coe]
          exact f.map_smul' m x }
    have hf' : Function.Surjective f' := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx⟩ := hf.right y
      use ⟨x, ?_⟩
      · simpa only [f', ← Subtype.coe_inj] using! hx
      · intro h
        apply hy
        rw [← hs']
        exact ⟨x, h, hx⟩
    have : IsPreprimitive (fixingSubgroup M s) (ofFixingSubgroup M s) :=
      IsMultiplyPreprimitive.isPreprimitive_ofFixingSubgroup _ n
        (by rw [← ht, ← hs', hf.injective.encard_image])
    exact IsPreprimitive.of_surjective (f := f') (φ := φ') hf'

@[to_additive]

Depends on / 依赖: IsPretransitive, IsPretransitive.of_embedding, hf.surjective, of_embedding, surjective
-/
theorem IsMultiplyPreprimitive.of_bijective_map
    {N β : Type*} [Group N] [MulAction N β] {φ : M -> N}
    {f : α ->ₑ[φ] β} (hf : Function.Bijective f) {n : Nat}
    (h : IsMultiplyPreprimitive M α n) :
    IsMultiplyPreprimitive N β n where
  isMultiplyPretransitive := IsPretransitive.of_embedding hf.surjective
  isPreprimitive_ofFixingSubgroup {t} ht := by
    let s := f ⁻¹' t
    have hs' : f '' s = t := Set.image_preimage_eq t hf.surjective
    let φ' : fixingSubgroup M s -> fixingSubgroup N t := fun ⟨m, hm⟩ =>
      ⟨φ m, fun ⟨y, hy⟩ => by
        rw [← hs']; rw [Set.mem_image] at hy
        obtain ⟨x, hx, hx'⟩ := hy
        simp only
        rw [← hx']; rw [← map_smulₛₗ]
        apply congr_arg
        rw [mem_fixingSubgroup_iff] at hm
        exact hm x hx⟩
    let f' : SubMulAction.ofFixingSubgroup M s ->ₑ[φ'] SubMulAction.ofFixingSubgroup N t :=
      { toFun := fun ⟨x, hx⟩ => ⟨f.toFun x, fun h => hx (Set.mem_preimage.mp h)⟩
        map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ =>
          by
          rw [← SetLike.coe_eq_coe]
          exact f.map_smul' m x }
    have hf' : Function.Surjective f' := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx⟩ := hf.right y
      use ⟨x, ?_⟩
      · simpa only [f', ← Subtype.coe_inj] using! hx
      · intro h
        apply hy
        rw [← hs']
        exact ⟨x, h, hx⟩
    have : IsPreprimitive (fixingSubgroup M s) (ofFixingSubgroup M s) :=
      IsMultiplyPreprimitive.isPreprimitive_ofFixingSubgroup _ n
        (by rw [← ht, ← hs', hf.injective.encard_image])
    exact IsPreprimitive.of_surjective (f := f') (φ := φ') hf'

@[to_additive]
/--
theorem `isMultiplyPreprimitive_congr` / 定理 `isMultiplyPreprimitive_congr`

English:
theorem isMultiplyPreprimitive_congr
  proof: by
  refine ⟨IsMultiplyPreprimitive.of_bijective_map hf, ?_⟩
  intro H
  rw [isMultiplyPreprimitive_iff]
  constructor
  · exact (IsPretransitive.of_embedding_congr hφ hf).mpr H.isMultiplyPretransitive
  · intro s hs
    let t := f '' s
    let ψ : fixingSubgroup M s -> fixingSubgroup N t := fun ⟨g, hg⟩ => ⟨φ g, by
      simp only [mem_fixingSubgroup_iff] at hg ⊢
      intro y hy
      suffices exists x in s, y = f x by
        obtain ⟨x, hx, rfl⟩ := this
        rwa [← map_smulₛₗ, hg]
      obtain ⟨x, rfl⟩ := hf.surjective y
      simpa only [Set.mem_image, t, eq_comm] using! hy⟩
    let g : ofFixingSubgroup M s ->ₑ[ψ] ofFixingSubgroup N t := {
      toFun x := ⟨f x.val, by
        simp only [mem_ofFixingSubgroup_iff, Set.mem_image, hf.injective.eq_iff, exists_eq_right, t]
        exact x.prop⟩
      map_smul' m x := by simp [subgroup_smul_def, map_smulₛₗ, ψ] }
    rw [isPreprimitive_congr (f := g)]
    · apply H.isPreprimitive_ofFixingSubgroup
      simp [← hs, t, hf.injective.injOn.encard_image]
    · rintro ⟨k, hk⟩
      obtain ⟨k, rfl⟩ := hφ k
      suffices k in fixingSubgroup M s by
        use ⟨k, this⟩
      simp only [mem_fixingSubgroup_iff, t] at hk ⊢
      intro y hy
      apply hf.injective
      rw [map_smulₛₗ]; rw [hk]
      exact Set.mem_image_of_mem (⇑f) hy
    · constructor
      · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
        suffices f x = f y by
          simpa [← Subtype.coe_inj, hf.injective.eq_iff] using! this
        simpa only [g, ← Subtype.coe_inj] using! h
      · rintro ⟨x, hx⟩
        obtain ⟨y, rfl⟩ := hf.surjective x
        suffices y in ofFixingSubgroup M s by
          exact ⟨⟨y, this⟩, rfl⟩
        simp only [mem_ofFixingSubgroup_iff, Set.mem_image, not_exists, not_and, t] at hx ⊢
        exact fun hy => hx y hy rfl

中文:
定理 isMultiplyPreprimitive_congr
  证明: by
  refine ⟨IsMultiplyPreprimitive.of_bijective_map hf, ?_⟩
  intro H
  rw [isMultiplyPreprimitive_iff]
  constructor
  · exact (IsPretransitive.of_embedding_congr hφ hf).mpr H.isMultiplyPretransitive
  · intro s hs
    let t := f '' s
    let ψ : fixingSubgroup M s -> fixingSubgroup N t := fun ⟨g, hg⟩ => ⟨φ g, by
      simp only [mem_fixingSubgroup_iff] at hg ⊢
      intro y hy
      suffices exists x in s, y = f x by
        obtain ⟨x, hx, rfl⟩ := this
        rwa [← map_smulₛₗ, hg]
      obtain ⟨x, rfl⟩ := hf.surjective y
      simpa only [Set.mem_image, t, eq_comm] using! hy⟩
    let g : ofFixingSubgroup M s ->ₑ[ψ] ofFixingSubgroup N t := {
      toFun x := ⟨f x.val, by
        simp only [mem_ofFixingSubgroup_iff, Set.mem_image, hf.injective.eq_iff, exists_eq_right, t]
        exact x.prop⟩
      map_smul' m x := by simp [subgroup_smul_def, map_smulₛₗ, ψ] }
    rw [isPreprimitive_congr (f := g)]
    · apply H.isPreprimitive_ofFixingSubgroup
      simp [← hs, t, hf.injective.injOn.encard_image]
    · rintro ⟨k, hk⟩
      obtain ⟨k, rfl⟩ := hφ k
      suffices k in fixingSubgroup M s by
        use ⟨k, this⟩
      simp only [mem_fixingSubgroup_iff, t] at hk ⊢
      intro y hy
      apply hf.injective
      rw [map_smulₛₗ]; rw [hk]
      exact Set.mem_image_of_mem (⇑f) hy
    · constructor
      · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
        suffices f x = f y by
          simpa [← Subtype.coe_inj, hf.injective.eq_iff] using! this
        simpa only [g, ← Subtype.coe_inj] using! h
      · rintro ⟨x, hx⟩
        obtain ⟨y, rfl⟩ := hf.surjective x
        suffices y in ofFixingSubgroup M s by
          exact ⟨⟨y, this⟩, rfl⟩
        simp only [mem_ofFixingSubgroup_iff, Set.mem_image, not_exists, not_and, t] at hx ⊢
        exact fun hy => hx y hy rfl

Depends on / 依赖: H.isMultiplyPretransitive, IsMultiplyPreprimitive, IsMultiplyPreprimitive.of_bijective_map, IsPretransitive, IsPretransitive.of_embedding_congr, Set.mem_image, fixingSubgroup, hf.surjective, isMultiplyPreprimitive_iff, isMultiplyPretransitive, mem_fixingSubgroup_iff, mem_image, of_bijective_map, of_embedding_congr, surjective
-/
theorem isMultiplyPreprimitive_congr
    {N β : Type*} [Group N] [MulAction N β] {φ : M -> N} (hφ : Function.Surjective φ)
    {f : α ->ₑ[φ] β} (hf : Function.Bijective f) {n : Nat} :
    IsMultiplyPreprimitive M α n ↔ IsMultiplyPreprimitive N β n := by
  refine ⟨IsMultiplyPreprimitive.of_bijective_map hf, ?_⟩
  intro H
  rw [isMultiplyPreprimitive_iff]
  constructor
  · exact (IsPretransitive.of_embedding_congr hφ hf).mpr H.isMultiplyPretransitive
  · intro s hs
    let t := f '' s
    let ψ : fixingSubgroup M s -> fixingSubgroup N t := fun ⟨g, hg⟩ => ⟨φ g, by
      simp only [mem_fixingSubgroup_iff] at hg ⊢
      intro y hy
      suffices exists x in s, y = f x by
        obtain ⟨x, hx, rfl⟩ := this
        rwa [← map_smulₛₗ, hg]
      obtain ⟨x, rfl⟩ := hf.surjective y
      simpa only [Set.mem_image, t, eq_comm] using! hy⟩
    let g : ofFixingSubgroup M s ->ₑ[ψ] ofFixingSubgroup N t := {
      toFun x := ⟨f x.val, by
        simp only [mem_ofFixingSubgroup_iff, Set.mem_image, hf.injective.eq_iff, exists_eq_right, t]
        exact x.prop⟩
      map_smul' m x := by simp [subgroup_smul_def, map_smulₛₗ, ψ] }
    rw [isPreprimitive_congr (f := g)]
    · apply H.isPreprimitive_ofFixingSubgroup
      simp [← hs, t, hf.injective.injOn.encard_image]
    · rintro ⟨k, hk⟩
      obtain ⟨k, rfl⟩ := hφ k
      suffices k in fixingSubgroup M s by
        use ⟨k, this⟩
      simp only [mem_fixingSubgroup_iff, t] at hk ⊢
      intro y hy
      apply hf.injective
      rw [map_smulₛₗ]; rw [hk]
      exact Set.mem_image_of_mem (⇑f) hy
    · constructor
      · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
        suffices f x = f y by
          simpa [← Subtype.coe_inj, hf.injective.eq_iff] using! this
        simpa only [g, ← Subtype.coe_inj] using! h
      · rintro ⟨x, hx⟩
        obtain ⟨y, rfl⟩ := hf.surjective x
        suffices y in ofFixingSubgroup M s by
          exact ⟨⟨y, this⟩, rfl⟩
        simp only [mem_ofFixingSubgroup_iff, Set.mem_image, not_exists, not_and, t] at hx ⊢
        exact fun hy => hx y hy rfl

end MulAction
