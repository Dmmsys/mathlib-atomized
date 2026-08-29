/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Ruben Van de Velde
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Subsemigroup.Operations
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Monoid.Basic
public import Mathlib.Order.Atoms

/-!
# Facts about ordered structures and ordered instances on subgroups
-/

public section

open Subgroup

@[to_additive (attr := simp)]
/--
theorem `mabs_mem_iff` / 定理 `mabs_mem_iff`

English:
theorem mabs_mem_iff
  statement: {S G} [Group G] [LinearOrder G] {_ : SetLike S G}
  proof: by
  cases mabs_choice x <;> simp [*]

中文:
定理 mabs_mem_iff
  结论: {S G} [Group G] [LinearOrder G] {_ : SetLike S G}
  证明: by
  cases mabs_choice x <;> simp [*]

Depends on / 依赖: mabs_choice
-/
theorem mabs_mem_iff {S G} [Group G] [LinearOrder G] {_ : SetLike S G}
    [InvMemClass S G] {H : S} {x : G} : |x|ₘ in H ↔ x in H := by
  cases mabs_choice x <;> simp [*]

section ModularLattice

variable {C : Type*} [CommGroup C]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsModularLattice (Subgroup C)
  body: ⟨fun {x} y z xz a ha => by
    rw [mem_inf]; rw [mem_sup] at ha
    rcases ha with ⟨⟨b, hb, c, hc, rfl⟩, haz⟩
    rw [mem_sup]
    exact ⟨b, hb, c, mem_inf.2 ⟨hc, (mul_mem_cancel_left (xz hb)).1 haz⟩, rfl⟩⟩

中文:
实例 :
  签名: IsModularLattice (Subgroup C)
  定义体: ⟨fun {x} y z xz a ha => by
    rw [mem_inf]; rw [mem_sup] at ha
    rcases ha with ⟨⟨b, hb, c, hc, rfl⟩, haz⟩
    rw [mem_sup]
    exact ⟨b, hb, c, mem_inf.2 ⟨hc, (mul_mem_cancel_left (xz hb)).1 haz⟩, rfl⟩⟩

Depends on / 依赖: mem_inf, mem_sup, mul_mem_cancel_left
-/
instance : IsModularLattice (Subgroup C) :=
  ⟨fun {x} y z xz a ha => by
    rw [mem_inf]; rw [mem_sup] at ha
    rcases ha with ⟨⟨b, hb, c, hc, rfl⟩, haz⟩
    rw [mem_sup]
    exact ⟨b, hb, c, mem_inf.2 ⟨hc, (mul_mem_cancel_left (xz hb)).1 haz⟩, rfl⟩⟩

end ModularLattice

section Coatom
namespace Subgroup

variable {G : Type*} [Group G] (H : Subgroup G)

/--
theorem `NormalizerCondition.normal_of_coatom` / 定理 `NormalizerCondition.normal_of_coatom`

English:
theorem NormalizerCondition.normal_of_coatom
  given: (hnc : NormalizerCondition G) (hmax : IsCoatom H)
  proof: normalizer_eq_top_iff.mp (hmax.2 _ (hnc H (lt_top_iff_ne_top.mpr hmax.1)))

@[simp]

中文:
定理 NormalizerCondition.normal_of_coatom
  条件: (hnc : NormalizerCondition G) (hmax : IsCoatom H)
  证明: normalizer_eq_top_iff.mp (hmax.2 _ (hnc H (lt_top_iff_ne_top.mpr hmax.1)))

@[simp]

Depends on / 依赖: lt_top_iff_ne_top, lt_top_iff_ne_top.mpr, normalizer_eq_top_iff, normalizer_eq_top_iff.mp
-/
theorem NormalizerCondition.normal_of_coatom (hnc : NormalizerCondition G) (hmax : IsCoatom H) :
    H.Normal :=
  normalizer_eq_top_iff.mp (hmax.2 _ (hnc H (lt_top_iff_ne_top.mpr hmax.1)))

@[simp]
/--
theorem `isCoatom_comap` / 定理 `isCoatom_comap`

English:
theorem isCoatom_comap
  given: {H : Type*} [Group H] (f : G ≃* H) {K : Subgroup H}
  proof: OrderIso.isCoatom_iff (f.comapSubgroup) K

@[simp]

中文:
定理 isCoatom_comap
  条件: {H : 类型} [Group H] (f : G ≃* H) {K : Subgroup H}
  证明: OrderIso.isCoatom_iff (f.comapSubgroup) K

@[simp]

Depends on / 依赖: OrderIso, OrderIso.isCoatom_iff, comapSubgroup, f.comapSubgroup, isCoatom_iff
-/
theorem isCoatom_comap {H : Type*} [Group H] (f : G ≃* H) {K : Subgroup H} :
    IsCoatom (Subgroup.comap (f : G ->* H) K) ↔ IsCoatom K :=
  OrderIso.isCoatom_iff (f.comapSubgroup) K

@[simp]
/--
theorem `isCoatom_map` / 定理 `isCoatom_map`

English:
theorem isCoatom_map
  given: (f : G ≃* H) {K : Subgroup G}
  proof: OrderIso.isCoatom_iff (f.mapSubgroup) K

中文:
定理 isCoatom_map
  条件: (f : G ≃* H) {K : Subgroup G}
  证明: OrderIso.isCoatom_iff (f.mapSubgroup) K

Depends on / 依赖: OrderIso, OrderIso.isCoatom_iff, f.mapSubgroup, isCoatom_iff, mapSubgroup
-/
theorem isCoatom_map (f : G ≃* H) {K : Subgroup G} :
    IsCoatom (Subgroup.map (f : G ->* H) K) ↔ IsCoatom K :=
  OrderIso.isCoatom_iff (f.mapSubgroup) K

/--
lemma `isCoatom_comap_of_surjective` / 引理 `isCoatom_comap_of_surjective`

English:
lemma isCoatom_comap_of_surjective
  proof: by
  refine And.imp (fun hM => ?_) (fun hM => ?_) hM
  · rwa [← (comap_injective hφ).ne_iff, comap_top] at hM
  · intro K hK
    specialize hM (K.map φ)
    rw [← comap_lt_comap_of_surjective hφ]; rw [← (comap_injective hφ).eq_iff] at hM
    rw [comap_map_eq_self ((M.ker_le_comap φ).trans hK.le)]; r

中文:
引理 isCoatom_comap_of_surjective
  证明: by
  refine And.imp (fun hM => ?_) (fun hM => ?_) hM
  · rwa [← (comap_injective hφ).ne_iff, comap_top] at hM
  · intro K hK
    specialize hM (K.map φ)
    rw [← comap_lt_comap_of_surjective hφ]; rw [← (comap_injective hφ).eq_iff] at hM
    rw [comap_map_eq_self ((M.ker_le_comap φ).trans hK.le)]; r

Depends on / 依赖: And.imp, K.map, M.ker_le_comap, comap_injective, comap_lt_comap_of_surjective, comap_map_eq_self, comap_top, eq_iff, hK.le, ker_le_comap, ne_iff, specialize
-/
lemma isCoatom_comap_of_surjective
    {H : Type*} [Group H] {φ : G ->* H} (hφ : Function.Surjective φ)
    {M : Subgroup H} (hM : IsCoatom M) : IsCoatom (M.comap φ) := by
  refine And.imp (fun hM => ?_) (fun hM => ?_) hM
  · rwa [← (comap_injective hφ).ne_iff, comap_top] at hM
  · intro K hK
    specialize hM (K.map φ)
    rw [← comap_lt_comap_of_surjective hφ]; rw [← (comap_injective hφ).eq_iff] at hM
    rw [comap_map_eq_self ((M.ker_le_comap φ).trans hK.le)]; rw [comap_top] at hM
    exact hM hK

end Subgroup
end Coatom

namespace Subgroup

variable {G : Type*}

/-- A subgroup of an ordered group is an ordered group. -/
@[to_additive
/-- An additive subgroup of an additive ordered group is an additive ordered group. -/]
/--
Instance `toIsOrderedMonoid` / 实例 `toIsOrderedMonoid`

English:
instance toIsOrderedMonoid
  signature: [CommGroup G] [Preorder G] [IsOrderedMonoid G] (H : Subgroup G)
  body: Function.Injective.isOrderedMonoid Subtype.val (fun _ _ => rfl) .rfl

中文:
实例 toIsOrderedMonoid
  签名: [CommGroup G] [Preorder G] [IsOrderedMonoid G] (H : Subgroup G)
  定义体: Function.Injective.isOrderedMonoid Subtype.val (fun _ _ => rfl) .rfl

Depends on / 依赖: Function, Function.Injective.isOrderedMonoid, Injective, Subtype, Subtype.val, isOrderedMonoid
-/
instance toIsOrderedMonoid [CommGroup G] [Preorder G] [IsOrderedMonoid G] (H : Subgroup G) :
    IsOrderedMonoid H :=
  Function.Injective.isOrderedMonoid Subtype.val (fun _ _ => rfl) .rfl

end Subgroup

@[to_additive]
/--
lemma `Subsemigroup.strictMono_topEquiv` / 引理 `Subsemigroup.strictMono_topEquiv`

English:
lemma Subsemigroup.strictMono_topEquiv
  given: {G : Type*} [CommMonoid G] [Preorder G]
  proof: fun _ _ => id

@[to_additive]

中文:
引理 Subsemigroup.strictMono_topEquiv
  条件: {G : 类型} [CommMonoid G] [Preorder G]
  证明: fun _ _ => id

@[to_additive]
-/
lemma Subsemigroup.strictMono_topEquiv {G : Type*} [CommMonoid G] [Preorder G] :
    StrictMono (topEquiv (M := G)) := fun _ _ => id

@[to_additive]
/--
lemma `MulEquiv.strictMono_subsemigroupCongr` / 引理 `MulEquiv.strictMono_subsemigroupCongr`

English:
lemma MulEquiv.strictMono_subsemigroupCongr
  statement: {G : Type*}
  proof: fun _ _ => id

@[to_additive]

中文:
引理 MulEquiv.strictMono_subsemigroupCongr
  结论: {G : 类型}
  证明: fun _ _ => id

@[to_additive]
-/
lemma MulEquiv.strictMono_subsemigroupCongr {G : Type*}
    [CommMonoid G] [Preorder G] {S T : Subsemigroup G}
    (h : S = T) : StrictMono (subsemigroupCongr h) := fun _ _ => id

@[to_additive]
/--
lemma `MulEquiv.strictMono_symm` / 引理 `MulEquiv.strictMono_symm`

English:
lemma MulEquiv.strictMono_symm
  statement: {G G' : Type*} [CommMonoid G] [LinearOrder G]
  proof: by
  intro
  simp [← he.lt_iff_lt]

中文:
引理 MulEquiv.strictMono_symm
  结论: {G G' : 类型} [CommMonoid G] [LinearOrder G]
  证明: by
  intro
  simp [← he.lt_iff_lt]

Depends on / 依赖: he.lt_iff_lt, lt_iff_lt
-/
lemma MulEquiv.strictMono_symm {G G' : Type*} [CommMonoid G] [LinearOrder G]
    [CommMonoid G'] [Preorder G'] {e : G ≃* G'} (he : StrictMono e) : StrictMono e.symm := by
  intro
  simp [← he.lt_iff_lt]
