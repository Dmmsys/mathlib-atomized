/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.TypeTags.Hom

/-!
# `map` and `comap` for subgroups

We prove results about images and preimages of subgroups under group homomorphisms. The bundled
subgroups use bundled monoid homomorphisms.

Special thanks goes to Amelia Livingston and Yury Kudryashov for their help and inspiration.

## Main definitions

Notation used here:

- `G N` are `Group`s

- `H` is a `Subgroup` of `G`

- `x` is an element of type `G` or type `A`

- `f g : N →* G` are group homomorphisms

- `s k` are sets of elements of type `G`

Definitions in the file:

* `Subgroup.comap H f` : the preimage of a subgroup `H` along the group homomorphism `f` is also a
  subgroup

* `Subgroup.map f H` : the image of a subgroup `H` along the group homomorphism `f` is also a
  subgroup

## Implementation notes

Subgroup inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a subgroup's underlying set.

## Tags
subgroup, subgroups
-/

@[expose] public section

assert_not_exists IsOrderedMonoid Multiset Ring

open Function
open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']
variable {A : Type*} [AddGroup A]

namespace Subgroup

variable (H K : Subgroup G) {k : Set G}

open Set

variable {N : Type*} [Group N] {P : Type*} [Group P]

/-- The preimage of a subgroup along a monoid homomorphism is a subgroup. -/
@[to_additive
      /-- The preimage of an `AddSubgroup` along an `AddMonoid` homomorphism
      is an `AddSubgroup`. -/]
/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: {N : Type*} [Group N] (f : G ->* N) (H : Subgroup N)
  body: { H.toSubmonoid.comap f with
    carrier := f ⁻¹' H
    inv_mem' := fun {a} ha => show f a⁻¹ in H by rw [f.map_inv]; exact H.inv_mem ha }

@[to_additive (attr := simp)]

中文:
定义 comap
  签名: {N : 类型} [Group N] (f : G ->* N) (H : Subgroup N)
  定义体: { H.toSubmonoid.comap f with
    carrier := f ⁻¹' H
    inv_mem' := fun {a} ha => show f a⁻¹ in H by rw [f.map_inv]; exact H.inv_mem ha }

@[to_additive (attr := simp)]

Depends on / 依赖: H.inv_mem, H.toSubmonoid.comap, carrier, f.map_inv, inv_mem, map_inv, toSubmonoid
-/
def comap {N : Type*} [Group N] (f : G ->* N) (H : Subgroup N) : Subgroup G :=
  { H.toSubmonoid.comap f with
    carrier := f ⁻¹' H
    inv_mem' := fun {a} ha => show f a⁻¹ in H by rw [f.map_inv]; exact H.inv_mem ha }

@[to_additive (attr := simp)]
/--
theorem `coe_comap` / 定理 `coe_comap`

English:
theorem coe_comap
  given: (K : Subgroup N) (f : G ->* N)
  statement: (K.comap f : Set G) = f ⁻¹' K
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_comap
  条件: (K : Subgroup N) (f : G ->* N)
  结论: (K.comap f : Set G) = f ⁻¹' K
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_comap (K : Subgroup N) (f : G ->* N) : (K.comap f : Set G) = f ⁻¹' K :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mem_comap` / 定理 `mem_comap`

English:
theorem mem_comap
  given: {K : Subgroup N} {f : G ->* N} {x : G}
  statement: x in K.comap f ↔ f x in K
  proof: Iff.rfl

@[to_additive (attr := gcongr)]

中文:
定理 mem_comap
  条件: {K : Subgroup N} {f : G ->* N} {x : G}
  结论: x in K.comap f ↔ f x in K
  证明: Iff.rfl

@[to_additive (attr := gcongr)]

Depends on / 依赖: CompleteSemilatticeInf, Iff.rfl, PartialOrder, SaturatedSubmonoid, Submonoid, Submonoid.giSaturation, giSaturation, liftCompleteLattice
-/
theorem mem_comap {K : Subgroup N} {f : G ->* N} {x : G} : x in K.comap f ↔ f x in K :=
  Iff.rfl

@[to_additive (attr := gcongr)]
/--
theorem `comap_mono` / 定理 `comap_mono`

English:
theorem comap_mono
  given: {f : G ->* N} {K K' : Subgroup N}
  statement: K <= K' -> comap f K <= comap f K'
  proof: preimage_mono

@[to_additive]

中文:
定理 comap_mono
  条件: {f : G ->* N} {K K' : Subgroup N}
  结论: K <= K' -> comap f K <= comap f K'
  证明: preimage_mono

@[to_additive]

Depends on / 依赖: preimage_mono
-/
theorem comap_mono {f : G ->* N} {K K' : Subgroup N} : K <= K' -> comap f K <= comap f K' :=
  preimage_mono

@[to_additive]
/--
theorem `comap_comap` / 定理 `comap_comap`

English:
theorem comap_comap
  given: (K : Subgroup P) (g : N ->* P) (f : G ->* N)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 comap_comap
  条件: (K : Subgroup P) (g : N ->* P) (f : G ->* N)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem comap_comap (K : Subgroup P) (g : N ->* P) (f : G ->* N) :
    (K.comap g).comap f = K.comap (g.comp f) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `comap_id` / 定理 `comap_id`

English:
theorem comap_id
  given: (K : Subgroup N)
  statement: K.comap (MonoidHom.id _) = K
  proof: by
  ext
  rfl

@[simp]

中文:
定理 comap_id
  条件: (K : Subgroup N)
  结论: K.comap (MonoidHom.id _) = K
  证明: by
  ext
  rfl

@[simp]
-/
theorem comap_id (K : Subgroup N) : K.comap (MonoidHom.id _) = K := by
  ext
  rfl

@[simp]
/--
theorem `toAddSubgroup_comap` / 定理 `toAddSubgroup_comap`

English:
theorem toAddSubgroup_comap
  given: {G₂ : Type*} [Group G₂] (f : G ->* G₂) (s : Subgroup G₂)
  proof: rfl

@[simp]

中文:
定理 toAddSubgroup_comap
  条件: {G₂ : 类型} [Group G₂] (f : G ->* G₂) (s : Subgroup G₂)
  证明: rfl

@[simp]
-/
theorem toAddSubgroup_comap {G₂ : Type*} [Group G₂] (f : G ->* G₂) (s : Subgroup G₂) :
    s.toAddSubgroup.comap (MonoidHom.toAdditive f) = Subgroup.toAddSubgroup (s.comap f) := rfl

@[simp]
/--
theorem `_root_.AddSubgroup.toSubgroup_comap` / 定理 `_root_.AddSubgroup.toSubgroup_comap`

English:
theorem _root_.AddSubgroup.toSubgroup_comap
  statement: {A A₂ : Type*} [AddGroup A] [AddGroup A₂]
  proof: rfl

中文:
定理 _root_.AddSubgroup.toSubgroup_comap
  结论: {A A₂ : 类型} [AddGroup A] [AddGroup A₂]
  证明: rfl
-/
theorem _root_.AddSubgroup.toSubgroup_comap {A A₂ : Type*} [AddGroup A] [AddGroup A₂]
    (f : A ->+ A₂) (s : AddSubgroup A₂) :
    s.toSubgroup.comap (AddMonoidHom.toMultiplicative f) = AddSubgroup.toSubgroup (s.comap f) := rfl

/-- The image of a subgroup along a monoid homomorphism is a subgroup. -/
@[to_additive
      /-- The image of an `AddSubgroup` along an `AddMonoid` homomorphism
      is an `AddSubgroup`. -/]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : G ->* N) (H : Subgroup G)
  body: { H.toSubmonoid.map f with
    carrier := f '' H
    inv_mem' := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x⁻¹, H.inv_mem hx, f.map_inv x⟩ }

@[to_additive (attr := simp)]

中文:
定义 map
  签名: (f : G ->* N) (H : Subgroup G)
  定义体: { H.toSubmonoid.map f with
    carrier := f '' H
    inv_mem' := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x⁻¹, H.inv_mem hx, f.map_inv x⟩ }

@[to_additive (attr := simp)]

Depends on / 依赖: H.inv_mem, H.toSubmonoid.map, carrier, f.map_inv, inv_mem, map_inv, toSubmonoid
-/
def map (f : G ->* N) (H : Subgroup G) : Subgroup N :=
  { H.toSubmonoid.map f with
    carrier := f '' H
    inv_mem' := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x⁻¹, H.inv_mem hx, f.map_inv x⟩ }

@[to_additive (attr := simp)]
/--
theorem `coe_map` / 定理 `coe_map`

English:
theorem coe_map
  given: (f : G ->* N) (K : Subgroup G)
  statement: (K.map f : Set N) = f '' K
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_map
  条件: (f : G ->* N) (K : Subgroup G)
  结论: (K.map f : Set N) = f '' K
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_map (f : G ->* N) (K : Subgroup G) : (K.map f : Set N) = f '' K :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `map_toSubmonoid` / 定理 `map_toSubmonoid`

English:
theorem map_toSubmonoid
  given: (f : G ->* G') (K : Subgroup G)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 map_toSubmonoid
  条件: (f : G ->* G') (K : Subgroup G)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem map_toSubmonoid (f : G ->* G') (K : Subgroup G) :
    (Subgroup.map f K).toSubmonoid = Submonoid.map f K.toSubmonoid := rfl

@[to_additive (attr := simp)]
/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: {f : G ->* N} {K : Subgroup G} {y : N}
  statement: y in K.map f ↔ exists x in K, f x = y
  proof: Iff.rfl

@[to_additive]

中文:
定理 mem_map
  条件: {f : G ->* N} {K : Subgroup G} {y : N}
  结论: y in K.map f ↔ 存在 x in K, f x = y
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem mem_map {f : G ->* N} {K : Subgroup G} {y : N} : y in K.map f ↔ exists x in K, f x = y := Iff.rfl

@[to_additive]
/--
theorem `mem_map_of_mem` / 定理 `mem_map_of_mem`

English:
theorem mem_map_of_mem
  given: (f : G ->* N) {K : Subgroup G} {x : G} (hx : x in K)
  statement: f x in K.map f
  proof: mem_image_of_mem f hx

@[to_additive]

中文:
定理 mem_map_of_mem
  条件: (f : G ->* N) {K : Subgroup G} {x : G} (hx : x in K)
  结论: f x in K.map f
  证明: mem_image_of_mem f hx

@[to_additive]

Depends on / 依赖: mem_image_of_mem
-/
theorem mem_map_of_mem (f : G ->* N) {K : Subgroup G} {x : G} (hx : x in K) : f x in K.map f :=
  mem_image_of_mem f hx

@[to_additive]
/--
theorem `apply_coe_mem_map` / 定理 `apply_coe_mem_map`

English:
theorem apply_coe_mem_map
  given: (f : G ->* N) (K : Subgroup G) (x : K)
  statement: f x in K.map f
  proof: mem_map_of_mem f x.prop

@[to_additive (attr := gcongr)]

中文:
定理 apply_coe_mem_map
  条件: (f : G ->* N) (K : Subgroup G) (x : K)
  结论: f x in K.map f
  证明: mem_map_of_mem f x.prop

@[to_additive (attr := gcongr)]

Depends on / 依赖: mem_map_of_mem, x.prop
-/
theorem apply_coe_mem_map (f : G ->* N) (K : Subgroup G) (x : K) : f x in K.map f :=
  mem_map_of_mem f x.prop

@[to_additive (attr := gcongr)]
/--
theorem `map_mono` / 定理 `map_mono`

English:
theorem map_mono
  given: {f : G ->* N} {K K' : Subgroup G}
  statement: K <= K' -> map f K <= map f K'
  proof: image_mono

@[to_additive (attr := simp)]

中文:
定理 map_mono
  条件: {f : G ->* N} {K K' : Subgroup G}
  结论: K <= K' -> map f K <= map f K'
  证明: image_mono

@[to_additive (attr := simp)]

Depends on / 依赖: image_mono
-/
theorem map_mono {f : G ->* N} {K K' : Subgroup G} : K <= K' -> map f K <= map f K' :=
  image_mono

@[to_additive (attr := simp)]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: K.map (MonoidHom.id G) = K
  proof: SetLike.coe_injective image_id _

@[to_additive]

中文:
定理 map_id
  结论: K.map (MonoidHom.id G) = K
  证明: SetLike.coe_injective image_id _

@[to_additive]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, image_id
-/
theorem map_id : K.map (MonoidHom.id G) = K :=
SetLike.coe_injective image_id _

@[to_additive]
/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: (g : N ->* P) (f : G ->* N)
  statement: (K.map f).map g = K.map (g.comp f)
  proof: SetLike.coe_injective image_image _ _ _

@[to_additive (attr := simp)]

中文:
定理 map_map
  条件: (g : N ->* P) (f : G ->* N)
  结论: (K.map f).map g = K.map (g.comp f)
  证明: SetLike.coe_injective image_image _ _ _

@[to_additive (attr := simp)]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, image_image
-/
theorem map_map (g : N ->* P) (f : G ->* N) : (K.map f).map g = K.map (g.comp f) :=
SetLike.coe_injective image_image _ _ _

@[to_additive (attr := simp)]
/--
theorem `map_one_eq_bot` / 定理 `map_one_eq_bot`

English:
theorem map_one_eq_bot
  statement: K.map (1 : G ->* N) = ⊥
  proof: eq_bot_iff.mpr by
    rintro x ⟨y, _, rfl⟩
    simp

@[to_additive]

中文:
定理 map_one_eq_bot
  结论: K.map (1 : G ->* N) = ⊥
  证明: eq_bot_iff.mpr by
    rintro x ⟨y, _, rfl⟩
    simp

@[to_additive]

Depends on / 依赖: eq_bot_iff, eq_bot_iff.mpr
-/
theorem map_one_eq_bot : K.map (1 : G ->* N) = ⊥ :=
eq_bot_iff.mpr by
    rintro x ⟨y, _, rfl⟩
    simp

@[to_additive]
/--
theorem `mem_map_equiv` / 定理 `mem_map_equiv`

English:
theorem mem_map_equiv
  given: {f : G ≃* N} {K : Subgroup G} {x : N}
  proof: Set.mem_image_equiv

@[to_additive (attr := simp 1100)]

中文:
定理 mem_map_equiv
  条件: {f : G ≃* N} {K : Subgroup G} {x : N}
  证明: Set.mem_image_equiv

@[to_additive (attr := simp 1100)]

Depends on / 依赖: Set.mem_image_equiv, mem_image_equiv
-/
theorem mem_map_equiv {f : G ≃* N} {K : Subgroup G} {x : N} :
    x in K.map f.toMonoidHom ↔ f.symm x in K :=
  Set.mem_image_equiv

@[to_additive (attr := simp 1100)]
/--
theorem `mem_map_iff_mem` / 定理 `mem_map_iff_mem`

English:
theorem mem_map_iff_mem
  given: {f : G ->* N} (hf : Function.Injective f) {K : Subgroup G} {x : G}
  proof: hf.mem_set_image

@[to_additive]

中文:
定理 mem_map_iff_mem
  条件: {f : G ->* N} (hf : Function.Injective f) {K : Subgroup G} {x : G}
  证明: hf.mem_set_image

@[to_additive]

Depends on / 依赖: hf.mem_set_image, mem_set_image
-/
theorem mem_map_iff_mem {f : G ->* N} (hf : Function.Injective f) {K : Subgroup G} {x : G} :
    f x in K.map f ↔ x in K :=
  hf.mem_set_image

@[to_additive]
/--
theorem `map_equiv_eq_comap_symm'` / 定理 `map_equiv_eq_comap_symm'`

English:
theorem map_equiv_eq_comap_symm'
  given: (f : G ≃* N) (K : Subgroup G)
  proof: SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)

@[to_additive]

中文:
定理 map_equiv_eq_comap_symm'
  条件: (f : G ≃* N) (K : Subgroup G)
  证明: SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)

@[to_additive]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, f.toEquiv.image_eq_preimage_symm, image_eq_preimage_symm, toEquiv
-/
theorem map_equiv_eq_comap_symm' (f : G ≃* N) (K : Subgroup G) :
    K.map f.toMonoidHom = K.comap f.symm.toMonoidHom :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)

@[to_additive]
/--
theorem `map_equiv_eq_comap_symm` / 定理 `map_equiv_eq_comap_symm`

English:
theorem map_equiv_eq_comap_symm
  given: (f : G ≃* N) (K : Subgroup G)
  proof: map_equiv_eq_comap_symm' _ _

@[to_additive]

中文:
定理 map_equiv_eq_comap_symm
  条件: (f : G ≃* N) (K : Subgroup G)
  证明: map_equiv_eq_comap_symm' _ _

@[to_additive]

Depends on / 依赖: f.symm
-/
theorem map_equiv_eq_comap_symm (f : G ≃* N) (K : Subgroup G) :
    K.map f = K.comap (G := N) f.symm :=
  map_equiv_eq_comap_symm' _ _

@[to_additive]
/--
theorem `comap_equiv_eq_map_symm` / 定理 `comap_equiv_eq_map_symm`

English:
theorem comap_equiv_eq_map_symm
  given: (f : N ≃* G) (K : Subgroup G)
  proof: (map_equiv_eq_comap_symm f.symm K).symm

@[to_additive]

中文:
定理 comap_equiv_eq_map_symm
  条件: (f : N ≃* G) (K : Subgroup G)
  证明: (map_equiv_eq_comap_symm f.symm K).symm

@[to_additive]

Depends on / 依赖: K.map, f.symm
-/
theorem comap_equiv_eq_map_symm (f : N ≃* G) (K : Subgroup G) :
    K.comap (G := N) f = K.map f.symm :=
  (map_equiv_eq_comap_symm f.symm K).symm

@[to_additive]
/--
theorem `comap_equiv_eq_map_symm'` / 定理 `comap_equiv_eq_map_symm'`

English:
theorem comap_equiv_eq_map_symm'
  given: (f : N ≃* G) (K : Subgroup G)
  proof: (map_equiv_eq_comap_symm f.symm K).symm

@[to_additive]

中文:
定理 comap_equiv_eq_map_symm'
  条件: (f : N ≃* G) (K : Subgroup G)
  证明: (map_equiv_eq_comap_symm f.symm K).symm

@[to_additive]

Depends on / 依赖: f.symm, map_equiv_eq_comap_symm
-/
theorem comap_equiv_eq_map_symm' (f : N ≃* G) (K : Subgroup G) :
    K.comap f.toMonoidHom = K.map f.symm.toMonoidHom :=
  (map_equiv_eq_comap_symm f.symm K).symm

@[to_additive]
/--
theorem `map_symm_eq_iff_map_eq` / 定理 `map_symm_eq_iff_map_eq`

English:
theorem map_symm_eq_iff_map_eq
  given: {H : Subgroup N} {e : G ≃* N}
  proof: by
  constructor <;> rintro rfl
  · rw [map_map, ← MulEquiv.coe_monoidHom_trans, MulEquiv.symm_trans_self,
      MulEquiv.coe_monoidHom_refl, map_id]
  · rw [map_map, ← MulEquiv.coe_monoidHom_trans, MulEquiv.self_trans_symm,
      MulEquiv.coe_monoidHom_refl, map_id]

@[to_additive]

中文:
定理 map_symm_eq_iff_map_eq
  条件: {H : Subgroup N} {e : G ≃* N}
  证明: by
  constructor <;> rintro rfl
  · rw [map_map, ← MulEquiv.coe_monoidHom_trans, MulEquiv.symm_trans_self,
      MulEquiv.coe_monoidHom_refl, map_id]
  · rw [map_map, ← MulEquiv.coe_monoidHom_trans, MulEquiv.self_trans_symm,
      MulEquiv.coe_monoidHom_refl, map_id]

@[to_additive]

Depends on / 依赖: MulEquiv, MulEquiv.coe_monoidHom_refl, MulEquiv.coe_monoidHom_trans, MulEquiv.self_trans_symm, MulEquiv.symm_trans_self, coe_monoidHom_refl, coe_monoidHom_trans, map_id, map_map, self_trans_symm, symm_trans_self
-/
theorem map_symm_eq_iff_map_eq {H : Subgroup N} {e : G ≃* N} :
    H.map ↑e.symm = K ↔ K.map ↑e = H := by
  constructor <;> rintro rfl
  · rw [map_map, ← MulEquiv.coe_monoidHom_trans, MulEquiv.symm_trans_self,
      MulEquiv.coe_monoidHom_refl, map_id]
  · rw [map_map, ← MulEquiv.coe_monoidHom_trans, MulEquiv.self_trans_symm,
      MulEquiv.coe_monoidHom_refl, map_id]

@[to_additive]
/--
theorem `map_le_iff_le_comap` / 定理 `map_le_iff_le_comap`

English:
theorem map_le_iff_le_comap
  given: {f : G ->* N} {K : Subgroup G} {H : Subgroup N}
  proof: image_subset_iff

@[to_additive]

中文:
定理 map_le_iff_le_comap
  条件: {f : G ->* N} {K : Subgroup G} {H : Subgroup N}
  证明: image_subset_iff

@[to_additive]

Depends on / 依赖: image_subset_iff
-/
theorem map_le_iff_le_comap {f : G ->* N} {K : Subgroup G} {H : Subgroup N} :
    K.map f <= H ↔ K <= H.comap f :=
  image_subset_iff

@[to_additive]
/--
theorem `gc_map_comap` / 定理 `gc_map_comap`

English:
theorem gc_map_comap
  given: (f : G ->* N)
  statement: GaloisConnection (map f) (comap f)
  proof: fun _ _ =>
  map_le_iff_le_comap

@[to_additive]

中文:
定理 gc_map_comap
  条件: (f : G ->* N)
  结论: GaloisConnection (map f) (comap f)
  证明: fun _ _ =>
  map_le_iff_le_comap

@[to_additive]
-/
theorem gc_map_comap (f : G ->* N) : GaloisConnection (map f) (comap f) := fun _ _ =>
  map_le_iff_le_comap

@[to_additive]
/--
theorem `map_sup` / 定理 `map_sup`

English:
theorem map_sup
  given: (H K : Subgroup G) (f : G ->* N)
  statement: (H ⊔ K).map f = H.map f ⊔ K.map f
  proof: (gc_map_comap f).l_sup

@[to_additive]

中文:
定理 map_sup
  条件: (H K : Subgroup G) (f : G ->* N)
  结论: (H ⊔ K).map f = H.map f ⊔ K.map f
  证明: (gc_map_comap f).l_sup

@[to_additive]

Depends on / 依赖: gc_map_comap, l_sup
-/
theorem map_sup (H K : Subgroup G) (f : G ->* N) : (H ⊔ K).map f = H.map f ⊔ K.map f :=
  (gc_map_comap f).l_sup

@[to_additive]
/--
theorem `map_iSup` / 定理 `map_iSup`

English:
theorem map_iSup
  given: {ι : Sort*} (f : G ->* N) (s : ι -> Subgroup G)
  proof: (gc_map_comap f).l_iSup

@[to_additive]

中文:
定理 map_iSup
  条件: {ι : Sort*} (f : G ->* N) (s : ι -> Subgroup G)
  证明: (gc_map_comap f).l_iSup

@[to_additive]

Depends on / 依赖: gc_map_comap, l_iSup
-/
theorem map_iSup {ι : Sort*} (f : G ->* N) (s : ι -> Subgroup G) :
    (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup

@[to_additive]
/--
theorem `map_inf` / 定理 `map_inf`

English:
theorem map_inf
  given: (H K : Subgroup G) (f : G ->* N) (hf : Function.Injective f)
  proof: SetLike.coe_injective (Set.image_inter hf)

@[to_additive]

中文:
定理 map_inf
  条件: (H K : Subgroup G) (f : G ->* N) (hf : Function.Injective f)
  证明: SetLike.coe_injective (Set.image_inter hf)

@[to_additive]

Depends on / 依赖: Set.image_inter, SetLike, SetLike.coe_injective, coe_injective, image_inter
-/
theorem map_inf (H K : Subgroup G) (f : G ->* N) (hf : Function.Injective f) :
    (H ⊓ K).map f = H.map f ⊓ K.map f := SetLike.coe_injective (Set.image_inter hf)

@[to_additive]
/--
theorem `map_iInf` / 定理 `map_iInf`

English:
theorem map_iInf
  statement: {ι : Sort*} [Nonempty ι] (f : G ->* N) (hf : Function.Injective f)
  proof: by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

@[to_additive]

中文:
定理 map_iInf
  结论: {ι : Sort*} [Nonempty ι] (f : G ->* N) (hf : Function.Injective f)
  证明: by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

@[to_additive]

Depends on / 依赖: Set.injOn_of_injective, SetLike, SetLike.coe, SetLike.coe_injective, coe_injective, image_iInter_eq, injOn_of_injective
-/
theorem map_iInf {ι : Sort*} [Nonempty ι] (f : G ->* N) (hf : Function.Injective f)
    (s : ι -> Subgroup G) : (iInf s).map f = ⨅ i, (s i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

@[to_additive]
/--
theorem `comap_sup_comap_le` / 定理 `comap_sup_comap_le`

English:
theorem comap_sup_comap_le
  given: (H K : Subgroup N) (f : G ->* N)
  proof: Monotone.le_map_sup (fun _ _ => comap_mono) H K

@[to_additive]

中文:
定理 comap_sup_comap_le
  条件: (H K : Subgroup N) (f : G ->* N)
  证明: Monotone.le_map_sup (fun _ _ => comap_mono) H K

@[to_additive]

Depends on / 依赖: Monotone, Monotone.le_map_sup, comap_mono, le_map_sup
-/
theorem comap_sup_comap_le (H K : Subgroup N) (f : G ->* N) :
    comap f H ⊔ comap f K <= comap f (H ⊔ K) :=
  Monotone.le_map_sup (fun _ _ => comap_mono) H K

@[to_additive]
/--
theorem `iSup_comap_le` / 定理 `iSup_comap_le`

English:
theorem iSup_comap_le
  given: {ι : Sort*} (f : G ->* N) (s : ι -> Subgroup N)
  proof: Monotone.le_map_iSup fun _ _ => comap_mono

@[to_additive]

中文:
定理 iSup_comap_le
  条件: {ι : Sort*} (f : G ->* N) (s : ι -> Subgroup N)
  证明: Monotone.le_map_iSup fun _ _ => comap_mono

@[to_additive]

Depends on / 依赖: Monotone, Monotone.le_map_iSup, comap_mono, le_map_iSup
-/
theorem iSup_comap_le {ι : Sort*} (f : G ->* N) (s : ι -> Subgroup N) :
    ⨆ i, (s i).comap f <= (iSup s).comap f :=
  Monotone.le_map_iSup fun _ _ => comap_mono

@[to_additive]
/--
theorem `comap_inf` / 定理 `comap_inf`

English:
theorem comap_inf
  given: (H K : Subgroup N) (f : G ->* N)
  statement: (H ⊓ K).comap f = H.comap f ⊓ K.comap f
  proof: (gc_map_comap f).u_inf

@[to_additive]

中文:
定理 comap_inf
  条件: (H K : Subgroup N) (f : G ->* N)
  结论: (H ⊓ K).comap f = H.comap f ⊓ K.comap f
  证明: (gc_map_comap f).u_inf

@[to_additive]

Depends on / 依赖: gc_map_comap, u_inf
-/
theorem comap_inf (H K : Subgroup N) (f : G ->* N) : (H ⊓ K).comap f = H.comap f ⊓ K.comap f :=
  (gc_map_comap f).u_inf

@[to_additive]
/--
theorem `comap_iInf` / 定理 `comap_iInf`

English:
theorem comap_iInf
  given: {ι : Sort*} (f : G ->* N) (s : ι -> Subgroup N)
  proof: (gc_map_comap f).u_iInf

@[to_additive]

中文:
定理 comap_iInf
  条件: {ι : Sort*} (f : G ->* N) (s : ι -> Subgroup N)
  证明: (gc_map_comap f).u_iInf

@[to_additive]

Depends on / 依赖: gc_map_comap, u_iInf
-/
theorem comap_iInf {ι : Sort*} (f : G ->* N) (s : ι -> Subgroup N) :
    (iInf s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_iInf

@[to_additive]
/--
theorem `map_inf_le` / 定理 `map_inf_le`

English:
theorem map_inf_le
  given: (H K : Subgroup G) (f : G ->* N)
  statement: map f (H ⊓ K) <= map f H ⊓ map f K
  proof: le_inf (map_mono inf_le_left) (map_mono inf_le_right)

@[to_additive]

中文:
定理 map_inf_le
  条件: (H K : Subgroup G) (f : G ->* N)
  结论: map f (H ⊓ K) <= map f H ⊓ map f K
  证明: le_inf (map_mono inf_le_left) (map_mono inf_le_right)

@[to_additive]

Depends on / 依赖: inf_le_left, inf_le_right, le_inf, map_mono
-/
theorem map_inf_le (H K : Subgroup G) (f : G ->* N) : map f (H ⊓ K) <= map f H ⊓ map f K :=
  le_inf (map_mono inf_le_left) (map_mono inf_le_right)

@[to_additive]
/--
theorem `map_inf_eq` / 定理 `map_inf_eq`

English:
theorem map_inf_eq
  given: (H K : Subgroup G) (f : G ->* N) (hf : Function.Injective f)
  proof: by
  rw [← SetLike.coe_set_eq]
  simp [Set.image_inter hf]

@[to_additive (attr := simp)]

中文:
定理 map_inf_eq
  条件: (H K : Subgroup G) (f : G ->* N) (hf : Function.Injective f)
  证明: by
  rw [← SetLike.coe_set_eq]
  simp [Set.image_inter hf]

@[to_additive (attr := simp)]

Depends on / 依赖: Set.image_inter, SetLike, SetLike.coe_set_eq, coe_set_eq, image_inter
-/
theorem map_inf_eq (H K : Subgroup G) (f : G ->* N) (hf : Function.Injective f) :
    map f (H ⊓ K) = map f H ⊓ map f K := by
  rw [← SetLike.coe_set_eq]
  simp [Set.image_inter hf]

@[to_additive (attr := simp)]
/--
theorem `map_bot` / 定理 `map_bot`

English:
theorem map_bot
  given: (f : G ->* N)
  statement: (⊥ : Subgroup G).map f = ⊥
  proof: (gc_map_comap f).l_bot

@[to_additive]

中文:
定理 map_bot
  条件: (f : G ->* N)
  结论: (⊥ : Subgroup G).map f = ⊥
  证明: (gc_map_comap f).l_bot

@[to_additive]

Depends on / 依赖: gc_map_comap, l_bot
-/
theorem map_bot (f : G ->* N) : (⊥ : Subgroup G).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[to_additive]
/--
lemma `disjoint_map` / 引理 `disjoint_map`

English:
lemma disjoint_map
  given: {f : G ->* N} (hf : Function.Injective f) {H K : Subgroup G} (h : Disjoint H K)
  proof: by
  rw [disjoint_iff]; rw [← map_inf _ _ f hf]; rw [disjoint_iff.mp h]; rw [map_bot]

@[to_additive]

中文:
引理 disjoint_map
  条件: {f : G ->* N} (hf : Function.Injective f) {H K : Subgroup G} (h : Disjoint H K)
  证明: by
  rw [disjoint_iff]; rw [← map_inf _ _ f hf]; rw [disjoint_iff.mp h]; rw [map_bot]

@[to_additive]

Depends on / 依赖: disjoint_iff, disjoint_iff.mp, map_bot, map_inf
-/
lemma disjoint_map {f : G ->* N} (hf : Function.Injective f) {H K : Subgroup G} (h : Disjoint H K) :
    Disjoint (H.map f) (K.map f) := by
  rw [disjoint_iff]; rw [← map_inf _ _ f hf]; rw [disjoint_iff.mp h]; rw [map_bot]

@[to_additive]
/--
theorem `map_top_of_surjective` / 定理 `map_top_of_surjective`

English:
theorem map_top_of_surjective
  given: (f : G ->* N) (h : Function.Surjective f)
  statement: Subgroup.map f ⊤ = ⊤
  proof: by
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy⟩ := h x
  exact ⟨y, trivial, hy⟩

@[to_additive]

中文:
定理 map_top_of_surjective
  条件: (f : G ->* N) (h : Function.Surjective f)
  结论: Subgroup.map f ⊤ = ⊤
  证明: by
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy⟩ := h x
  exact ⟨y, trivial, hy⟩

@[to_additive]

Depends on / 依赖: eq_top_iff
-/
theorem map_top_of_surjective (f : G ->* N) (h : Function.Surjective f) : Subgroup.map f ⊤ = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy⟩ := h x
  exact ⟨y, trivial, hy⟩

@[to_additive]
/--
lemma `codisjoint_map` / 引理 `codisjoint_map`

English:
lemma codisjoint_map
  statement: {f : G ->* N} (hf : Function.Surjective f)
  proof: by
  rw [codisjoint_iff]; rw [← map_sup]; rw [codisjoint_iff.mp h]; rw [map_top_of_surjective _ hf]

@[to_additive (attr := simp)]

中文:
引理 codisjoint_map
  结论: {f : G ->* N} (hf : Function.Surjective f)
  证明: by
  rw [codisjoint_iff]; rw [← map_sup]; rw [codisjoint_iff.mp h]; rw [map_top_of_surjective _ hf]

@[to_additive (attr := simp)]

Depends on / 依赖: codisjoint_iff, codisjoint_iff.mp, map_sup, map_top_of_surjective
-/
lemma codisjoint_map {f : G ->* N} (hf : Function.Surjective f)
    {H K : Subgroup G} (h : Codisjoint H K) : Codisjoint (H.map f) (K.map f) := by
  rw [codisjoint_iff]; rw [← map_sup]; rw [codisjoint_iff.mp h]; rw [map_top_of_surjective _ hf]

@[to_additive (attr := simp)]
/--
lemma `map_equiv_top` / 引理 `map_equiv_top`

English:
lemma map_equiv_top
  given: {F : Type*} [EquivLike F G N] [MulEquivClass F G N] (f : F)
  proof: map_top_of_surjective _ (EquivLike.surjective f)

@[to_additive (attr := simp)]

中文:
引理 map_equiv_top
  条件: {F : 类型} [EquivLike F G N] [MulEquivClass F G N] (f : F)
  证明: map_top_of_surjective _ (EquivLike.surjective f)

@[to_additive (attr := simp)]

Depends on / 依赖: EquivLike, EquivLike.surjective, map_top_of_surjective, surjective
-/
lemma map_equiv_top {F : Type*} [EquivLike F G N] [MulEquivClass F G N] (f : F) :
    map (f : G ->* N) ⊤ = ⊤ :=
  map_top_of_surjective _ (EquivLike.surjective f)

@[to_additive (attr := simp)]
/--
theorem `comap_top` / 定理 `comap_top`

English:
theorem comap_top
  given: (f : G ->* N)
  statement: (⊤ : Subgroup N).comap f = ⊤
  proof: (gc_map_comap f).u_top

中文:
定理 comap_top
  条件: (f : G ->* N)
  结论: (⊤ : Subgroup N).comap f = ⊤
  证明: (gc_map_comap f).u_top

Depends on / 依赖: gc_map_comap, u_top
-/
theorem comap_top (f : G ->* N) : (⊤ : Subgroup N).comap f = ⊤ :=
  (gc_map_comap f).u_top

/-- For any subgroups `H` and `K`, view `H ⊓ K` as a subgroup of `K`. -/
@[to_additive /-- For any subgroups `H` and `K`, view `H ⊓ K` as a subgroup of `K`. -/]
/--
Definition of `subgroupOf` / `subgroupOf` 的定义

English:
definition subgroupOf
  signature: (H K : Subgroup G)
  body: H.comap K.subtype

中文:
定义 subgroupOf
  签名: (H K : Subgroup G)
  定义体: H.comap K.subtype

Depends on / 依赖: H.comap, K.subtype, subtype
-/
def subgroupOf (H K : Subgroup G) : Subgroup K :=
  H.comap K.subtype

/-- If `H ≤ K`, then `H` as a subgroup of `K` is isomorphic to `H`. -/
@[to_additive (attr := simps)
/-- If `H ≤ K`, then `H` as a subgroup of `K` is isomorphic to `H`. -/]
/--
Definition of `subgroupOfEquivOfLe` / `subgroupOfEquivOfLe` 的定义

English:
definition subgroupOfEquivOfLe
  signature: {G : Type*} [Group G] {H K : Subgroup G} (h : H <= K)
  body: ⟨g.1, g.2⟩
  invFun g := ⟨⟨g.1, h g.2⟩, g.2⟩
  map_mul' _g _h := rfl

@[to_additive]

中文:
定义 subgroupOfEquivOfLe
  签名: {G : 类型} [Group G] {H K : Subgroup G} (h : H <= K)
  定义体: ⟨g.1, g.2⟩
  invFun g := ⟨⟨g.1, h g.2⟩, g.2⟩
  map_mul' _g _h := rfl

@[to_additive]
-/
def subgroupOfEquivOfLe {G : Type*} [Group G] {H K : Subgroup G} (h : H <= K) :
    H.subgroupOf K ≃* H where
  toFun g := ⟨g.1, g.2⟩
  invFun g := ⟨⟨g.1, h g.2⟩, g.2⟩
  map_mul' _g _h := rfl

@[to_additive]
/--
lemma `subgroupOf_mono` / 引理 `subgroupOf_mono`

English:
lemma subgroupOf_mono
  given: {H₁ H₂ : Subgroup G} (H₃ : Subgroup G) (h : H₁ <= H₂)
  proof: comap_mono h

@[to_additive (attr := simp)]

中文:
引理 subgroupOf_mono
  条件: {H₁ H₂ : Subgroup G} (H₃ : Subgroup G) (h : H₁ <= H₂)
  证明: comap_mono h

@[to_additive (attr := simp)]

Depends on / 依赖: comap_mono
-/
lemma subgroupOf_mono {H₁ H₂ : Subgroup G} (H₃ : Subgroup G) (h : H₁ <= H₂) :
    H₁.subgroupOf H₃ <= H₂.subgroupOf H₃ :=
  comap_mono h

@[to_additive (attr := simp)]
/--
theorem `comap_subtype` / 定理 `comap_subtype`

English:
theorem comap_subtype
  given: (H K : Subgroup G)
  statement: H.comap K.subtype = H.subgroupOf K
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 comap_subtype
  条件: (H K : Subgroup G)
  结论: H.comap K.subtype = H.subgroupOf K
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem comap_subtype (H K : Subgroup G) : H.comap K.subtype = H.subgroupOf K :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `comap_inclusion_subgroupOf` / 定理 `comap_inclusion_subgroupOf`

English:
theorem comap_inclusion_subgroupOf
  given: {K₁ K₂ : Subgroup G} (h : K₁ <= K₂) (H : Subgroup G)
  proof: rfl

@[to_additive]

中文:
定理 comap_inclusion_subgroupOf
  条件: {K₁ K₂ : Subgroup G} (h : K₁ <= K₂) (H : Subgroup G)
  证明: rfl

@[to_additive]
-/
theorem comap_inclusion_subgroupOf {K₁ K₂ : Subgroup G} (h : K₁ <= K₂) (H : Subgroup G) :
    (H.subgroupOf K₂).comap (inclusion h) = H.subgroupOf K₁ :=
  rfl

@[to_additive]
/--
theorem `coe_subgroupOf` / 定理 `coe_subgroupOf`

English:
theorem coe_subgroupOf
  given: (H K : Subgroup G)
  statement: (H.subgroupOf K : Set K) = K.subtype ⁻¹' H
  proof: rfl

@[to_additive]

中文:
定理 coe_subgroupOf
  条件: (H K : Subgroup G)
  结论: (H.subgroupOf K : Set K) = K.subtype ⁻¹' H
  证明: rfl

@[to_additive]
-/
theorem coe_subgroupOf (H K : Subgroup G) : (H.subgroupOf K : Set K) = K.subtype ⁻¹' H :=
  rfl

@[to_additive]
/--
theorem `mem_subgroupOf` / 定理 `mem_subgroupOf`

English:
theorem mem_subgroupOf
  given: {H K : Subgroup G} {h : K}
  statement: h in H.subgroupOf K ↔ (h : G) in H
  proof: Iff.rfl

中文:
定理 mem_subgroupOf
  条件: {H K : Subgroup G} {h : K}
  结论: h in H.subgroupOf K ↔ (h : G) in H
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_subgroupOf {H K : Subgroup G} {h : K} : h in H.subgroupOf K ↔ (h : G) in H :=
  Iff.rfl

-- TODO(kmill): use `K ⊓ H` order for RHS to match `Subtype.image_preimage_coe`
@[to_additive (attr := simp)]
/--
theorem `subgroupOf_map_subtype` / 定理 `subgroupOf_map_subtype`

English:
theorem subgroupOf_map_subtype
  given: (H K : Subgroup G)
  statement: (H.subgroupOf K).map K.subtype = H ⊓ K
  proof: SetLike.ext' .trans ?_; apply Set.inter_comm by refine Subtype.image_preimage_coe _ _

@[to_additive]

中文:
定理 subgroupOf_map_subtype
  条件: (H K : Subgroup G)
  结论: (H.subgroupOf K).map K.subtype = H ⊓ K
  证明: SetLike.ext' .trans ?_; apply Set.inter_comm by refine Subtype.image_preimage_coe _ _

@[to_additive]

Depends on / 依赖: Set.inter_comm, SetLike, SetLike.ext, Subtype, Subtype.image_preimage_coe, image_preimage_coe, inter_comm
-/
theorem subgroupOf_map_subtype (H K : Subgroup G) : (H.subgroupOf K).map K.subtype = H ⊓ K :=
SetLike.ext' .trans ?_; apply Set.inter_comm by refine Subtype.image_preimage_coe _ _

@[to_additive]
/--
theorem `map_subgroupOf_eq_of_le` / 定理 `map_subgroupOf_eq_of_le`

English:
theorem map_subgroupOf_eq_of_le
  given: {H K : Subgroup G} (h : H <= K)
  proof: by
  rwa [subgroupOf_map_subtype, inf_eq_left]

@[to_additive (attr := simp)]

中文:
定理 map_subgroupOf_eq_of_le
  条件: {H K : Subgroup G} (h : H <= K)
  证明: by
  rwa [subgroupOf_map_subtype, inf_eq_left]

@[to_additive (attr := simp)]

Depends on / 依赖: inf_eq_left, subgroupOf_map_subtype
-/
theorem map_subgroupOf_eq_of_le {H K : Subgroup G} (h : H <= K) :
    (H.subgroupOf K).map K.subtype = H := by
  rwa [subgroupOf_map_subtype, inf_eq_left]

@[to_additive (attr := simp)]
/--
theorem `bot_subgroupOf` / 定理 `bot_subgroupOf`

English:
theorem bot_subgroupOf
  statement: (⊥ : Subgroup G).subgroupOf H = ⊥
  proof: Eq.symm (Subgroup.ext fun _g => Subtype.ext_iff)

@[to_additive (attr := simp)]

中文:
定理 bot_subgroupOf
  结论: (⊥ : Subgroup G).subgroupOf H = ⊥
  证明: Eq.symm (Subgroup.ext fun _g => Subtype.ext_iff)

@[to_additive (attr := simp)]

Depends on / 依赖: Eq.symm, Subgroup, Subgroup.ext, Subtype, Subtype.ext_iff, ext_iff
-/
theorem bot_subgroupOf : (⊥ : Subgroup G).subgroupOf H = ⊥ :=
  Eq.symm (Subgroup.ext fun _g => Subtype.ext_iff)

@[to_additive (attr := simp)]
/--
theorem `top_subgroupOf` / 定理 `top_subgroupOf`

English:
theorem top_subgroupOf
  statement: (⊤ : Subgroup G).subgroupOf H = ⊤
  proof: rfl

@[to_additive]

中文:
定理 top_subgroupOf
  结论: (⊤ : Subgroup G).subgroupOf H = ⊤
  证明: rfl

@[to_additive]
-/
theorem top_subgroupOf : (⊤ : Subgroup G).subgroupOf H = ⊤ :=
  rfl

@[to_additive]
/--
theorem `subgroupOf_bot_eq_bot` / 定理 `subgroupOf_bot_eq_bot`

English:
theorem subgroupOf_bot_eq_bot
  statement: H.subgroupOf ⊥ = ⊥
  proof: Subsingleton.elim _ _

@[to_additive]

中文:
定理 subgroupOf_bot_eq_bot
  结论: H.subgroupOf ⊥ = ⊥
  证明: Subsingleton.elim _ _

@[to_additive]

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem subgroupOf_bot_eq_bot : H.subgroupOf ⊥ = ⊥ :=
  Subsingleton.elim _ _

@[to_additive]
/--
theorem `subgroupOf_bot_eq_top` / 定理 `subgroupOf_bot_eq_top`

English:
theorem subgroupOf_bot_eq_top
  statement: H.subgroupOf ⊥ = ⊤
  proof: Subsingleton.elim _ _

@[to_additive (attr := simp)]

中文:
定理 subgroupOf_bot_eq_top
  结论: H.subgroupOf ⊥ = ⊤
  证明: Subsingleton.elim _ _

@[to_additive (attr := simp)]

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem subgroupOf_bot_eq_top : H.subgroupOf ⊥ = ⊤ :=
  Subsingleton.elim _ _

@[to_additive (attr := simp)]
/--
theorem `subgroupOf_self` / 定理 `subgroupOf_self`

English:
theorem subgroupOf_self
  statement: H.subgroupOf H = ⊤
  proof: top_unique fun g _hg => g.2

@[to_additive (attr := simp)]

中文:
定理 subgroupOf_self
  结论: H.subgroupOf H = ⊤
  证明: top_unique fun g _hg => g.2

@[to_additive (attr := simp)]

Depends on / 依赖: top_unique
-/
theorem subgroupOf_self : H.subgroupOf H = ⊤ :=
  top_unique fun g _hg => g.2

@[to_additive (attr := simp)]
/--
theorem `subgroupOf_inj` / 定理 `subgroupOf_inj`

English:
theorem subgroupOf_inj
  given: {H₁ H₂ K : Subgroup G}
  proof: by
  simpa only [SetLike.ext_iff, mem_inf, mem_subgroupOf, and_congr_left_iff] using Subtype.forall

@[to_additive (attr := simp)]

中文:
定理 subgroupOf_inj
  条件: {H₁ H₂ K : Subgroup G}
  证明: by
  simpa only [SetLike.ext_iff, mem_inf, mem_subgroupOf, and_congr_left_iff] using Subtype.forall

@[to_additive (attr := simp)]

Depends on / 依赖: SetLike, SetLike.ext_iff, Subtype, Subtype.forall, and_congr_left_iff, ext_iff, mem_inf, mem_subgroupOf
-/
theorem subgroupOf_inj {H₁ H₂ K : Subgroup G} :
    H₁.subgroupOf K = H₂.subgroupOf K ↔ H₁ ⊓ K = H₂ ⊓ K := by
  simpa only [SetLike.ext_iff, mem_inf, mem_subgroupOf, and_congr_left_iff] using Subtype.forall

@[to_additive (attr := simp)]
/--
theorem `inf_subgroupOf_right` / 定理 `inf_subgroupOf_right`

English:
theorem inf_subgroupOf_right
  given: (H K : Subgroup G)
  statement: (H ⊓ K).subgroupOf K = H.subgroupOf K
  proof: subgroupOf_inj.2 (inf_right_idem _ _)

@[to_additive (attr := simp)]

中文:
定理 inf_subgroupOf_right
  条件: (H K : Subgroup G)
  结论: (H ⊓ K).subgroupOf K = H.subgroupOf K
  证明: subgroupOf_inj.2 (inf_right_idem _ _)

@[to_additive (attr := simp)]

Depends on / 依赖: inf_right_idem, subgroupOf_inj
-/
theorem inf_subgroupOf_right (H K : Subgroup G) : (H ⊓ K).subgroupOf K = H.subgroupOf K :=
  subgroupOf_inj.2 (inf_right_idem _ _)

@[to_additive (attr := simp)]
/--
theorem `inf_subgroupOf_left` / 定理 `inf_subgroupOf_left`

English:
theorem inf_subgroupOf_left
  given: (H K : Subgroup G)
  statement: (K ⊓ H).subgroupOf K = H.subgroupOf K
  proof: by
  rw [inf_comm]; rw [inf_subgroupOf_right]

@[to_additive (attr := simp)]

中文:
定理 inf_subgroupOf_left
  条件: (H K : Subgroup G)
  结论: (K ⊓ H).subgroupOf K = H.subgroupOf K
  证明: by
  rw [inf_comm]; rw [inf_subgroupOf_right]

@[to_additive (attr := simp)]

Depends on / 依赖: inf_comm, inf_subgroupOf_right
-/
theorem inf_subgroupOf_left (H K : Subgroup G) : (K ⊓ H).subgroupOf K = H.subgroupOf K := by
  rw [inf_comm]; rw [inf_subgroupOf_right]

@[to_additive (attr := simp)]
/--
theorem `subgroupOf_eq_bot` / 定理 `subgroupOf_eq_bot`

English:
theorem subgroupOf_eq_bot
  given: {H K : Subgroup G}
  statement: H.subgroupOf K = ⊥ ↔ Disjoint H K
  proof: by
  rw [disjoint_iff]; rw [← bot_subgroupOf]; rw [subgroupOf_inj]; rw [bot_inf_eq]

@[to_additive (attr := simp)]

中文:
定理 subgroupOf_eq_bot
  条件: {H K : Subgroup G}
  结论: H.subgroupOf K = ⊥ ↔ Disjoint H K
  证明: by
  rw [disjoint_iff]; rw [← bot_subgroupOf]; rw [subgroupOf_inj]; rw [bot_inf_eq]

@[to_additive (attr := simp)]

Depends on / 依赖: bot_inf_eq, bot_subgroupOf, disjoint_iff, subgroupOf_inj
-/
theorem subgroupOf_eq_bot {H K : Subgroup G} : H.subgroupOf K = ⊥ ↔ Disjoint H K := by
  rw [disjoint_iff]; rw [← bot_subgroupOf]; rw [subgroupOf_inj]; rw [bot_inf_eq]

@[to_additive (attr := simp)]
/--
theorem `subgroupOf_eq_top` / 定理 `subgroupOf_eq_top`

English:
theorem subgroupOf_eq_top
  given: {H K : Subgroup G}
  statement: H.subgroupOf K = ⊤ ↔ K <= H
  proof: by
  rw [← top_subgroupOf]; rw [subgroupOf_inj]; rw [top_inf_eq]; rw [inf_eq_right]

中文:
定理 subgroupOf_eq_top
  条件: {H K : Subgroup G}
  结论: H.subgroupOf K = ⊤ ↔ K <= H
  证明: by
  rw [← top_subgroupOf]; rw [subgroupOf_inj]; rw [top_inf_eq]; rw [inf_eq_right]

Depends on / 依赖: inf_eq_right, subgroupOf_inj, top_inf_eq, top_subgroupOf
-/
theorem subgroupOf_eq_top {H K : Subgroup G} : H.subgroupOf K = ⊤ ↔ K <= H := by
  rw [← top_subgroupOf]; rw [subgroupOf_inj]; rw [top_inf_eq]; rw [inf_eq_right]

variable (H : Subgroup G)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsMulCommutative
  signature: G] : IsMulCommutative H
  body: IsMulCommutative.of_setLike_mul_comm fun a _ b _ => mul_comm' a b

@[to_additive]

中文:
实例 [IsMulCommutative
  签名: G] : IsMulCommutative H
  定义体: IsMulCommutative.of_setLike_mul_comm fun a _ b _ => mul_comm' a b

@[to_additive]

Depends on / 依赖: IsMulCommutative, IsMulCommutative.of_setLike_mul_comm, mul_comm, of_setLike_mul_comm
-/
instance [IsMulCommutative G] : IsMulCommutative H :=
  IsMulCommutative.of_setLike_mul_comm fun a _ b _ => mul_comm' a b

@[to_additive]
/--
Instance `map_isMulCommutative` / 实例 `map_isMulCommutative`

English:
instance map_isMulCommutative
  signature: (f : G ->* G') [IsMulCommutative H]
  body: by
  refine .of_setLike_mul_comm ?_
  rintro - ⟨a, ha, rfl⟩ - ⟨b, hb, rfl⟩
  simpa [map_mul] using congr(f $(setLike_mul_comm ha hb))

@[to_additive]

中文:
实例 map_isMulCommutative
  签名: (f : G ->* G') [IsMulCommutative H]
  定义体: by
  refine .of_setLike_mul_comm ?_
  rintro - ⟨a, ha, rfl⟩ - ⟨b, hb, rfl⟩
  simpa [map_mul] using congr(f $(setLike_mul_comm ha hb))

@[to_additive]

Depends on / 依赖: map_mul, of_setLike_mul_comm, setLike_mul_comm
-/
instance map_isMulCommutative (f : G ->* G') [IsMulCommutative H] : IsMulCommutative (H.map f) := by
  refine .of_setLike_mul_comm ?_
  rintro - ⟨a, ha, rfl⟩ - ⟨b, hb, rfl⟩
  simpa [map_mul] using congr(f $(setLike_mul_comm ha hb))

@[to_additive]
/--
theorem `comap_injective_isMulCommutative` / 定理 `comap_injective_isMulCommutative`

English:
theorem comap_injective_isMulCommutative
  given: {f : G' ->* G} (hf : Injective f) [IsMulCommutative H]
  proof: .of_setLike_mul_comm fun a (ha : f a in H) b (hb : f b in H) => hf by
    simpa using setLike_mul_comm ha hb

@[to_additive]

中文:
定理 comap_injective_isMulCommutative
  条件: {f : G' ->* G} (hf : Injective f) [IsMulCommutative H]
  证明: .of_setLike_mul_comm fun a (ha : f a in H) b (hb : f b in H) => hf by
    simpa using setLike_mul_comm ha hb

@[to_additive]

Depends on / 依赖: of_setLike_mul_comm, setLike_mul_comm
-/
theorem comap_injective_isMulCommutative {f : G' ->* G} (hf : Injective f) [IsMulCommutative H] :
    IsMulCommutative (H.comap f) :=
.of_setLike_mul_comm fun a (ha : f a in H) b (hb : f b in H) => hf by
    simpa using setLike_mul_comm ha hb

@[to_additive]
/--
Instance `subgroupOf_isMulCommutative` / 实例 `subgroupOf_isMulCommutative`

English:
instance subgroupOf_isMulCommutative
  signature: [IsMulCommutative H]
  body: H.comap_injective_isMulCommutative Subtype.coe_injective

中文:
实例 subgroupOf_isMulCommutative
  签名: [IsMulCommutative H]
  定义体: H.comap_injective_isMulCommutative Subtype.coe_injective

Depends on / 依赖: H.comap_injective_isMulCommutative, Subtype, Subtype.coe_injective, coe_injective, comap_injective_isMulCommutative
-/
instance subgroupOf_isMulCommutative [IsMulCommutative H] : IsMulCommutative (H.subgroupOf K) :=
  H.comap_injective_isMulCommutative Subtype.coe_injective

end Subgroup

namespace MulEquiv
variable {H : Type*} [Group H]

set_option backward.isDefEq.respectTransparency false in
/--
An isomorphism of groups gives an order isomorphism between the lattices of subgroups,
defined by sending subgroups to their inverse images.

See also `MulEquiv.mapSubgroup` which maps subgroups to their forward images.
-/
@[to_additive (attr := simps)
/-- An isomorphism of groups gives an order isomorphism between the lattices of subgroups,
defined by sending subgroups to their inverse images.

See also `AddEquiv.mapAddSubgroup` which maps subgroups to their forward images. -/]
/--
Definition of `comapSubgroup` / `comapSubgroup` 的定义

English:
definition comapSubgroup
  signature: (f : G ≃* H)
  body: Subgroup.comap f
  invFun := Subgroup.comap f.symm
  left_inv sg := by simp [Subgroup.comap_comap]
  right_inv sh := by simp [Subgroup.comap_comap]
  map_rel_iff' {sg1 sg2} :=
    ⟨fun h => by simpa [Subgroup.comap_comap] using
      Subgroup.comap_mono (f := (f.symm : H ->* G)) h, Subgroup.comap_mo

中文:
定义 comapSubgroup
  签名: (f : G ≃* H)
  定义体: Subgroup.comap f
  invFun := Subgroup.comap f.symm
  left_inv sg := by simp [Subgroup.comap_comap]
  right_inv sh := by simp [Subgroup.comap_comap]
  map_rel_iff' {sg1 sg2} :=
    ⟨fun h => by simpa [Subgroup.comap_comap] using
      Subgroup.comap_mono (f := (f.symm : H ->* G)) h, Subgroup.comap_mo

Depends on / 依赖: Subgroup, Subgroup.comap
-/
def comapSubgroup (f : G ≃* H) : Subgroup H ≃o Subgroup G where
  toFun := Subgroup.comap f
  invFun := Subgroup.comap f.symm
  left_inv sg := by simp [Subgroup.comap_comap]
  right_inv sh := by simp [Subgroup.comap_comap]
  map_rel_iff' {sg1 sg2} :=
    ⟨fun h => by simpa [Subgroup.comap_comap] using
      Subgroup.comap_mono (f := (f.symm : H ->* G)) h, Subgroup.comap_mono⟩

@[to_additive (attr := simp, norm_cast)]
/--
lemma `coe_comapSubgroup` / 引理 `coe_comapSubgroup`

English:
lemma coe_comapSubgroup
  given: (e : G ≃* H)
  statement: comapSubgroup e = Subgroup.comap e.toMonoidHom
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 coe_comapSubgroup
  条件: (e : G ≃* H)
  结论: comapSubgroup e = Subgroup.comap e.toMonoidHom
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma coe_comapSubgroup (e : G ≃* H) : comapSubgroup e = Subgroup.comap e.toMonoidHom := rfl

@[to_additive (attr := simp)]
/--
lemma `symm_comapSubgroup` / 引理 `symm_comapSubgroup`

English:
lemma symm_comapSubgroup
  given: (e : G ≃* H)
  statement: (comapSubgroup e).symm = comapSubgroup e.symm
  proof: rfl

中文:
引理 symm_comapSubgroup
  条件: (e : G ≃* H)
  结论: (comapSubgroup e).symm = comapSubgroup e.symm
  证明: rfl
-/
lemma symm_comapSubgroup (e : G ≃* H) : (comapSubgroup e).symm = comapSubgroup e.symm := rfl

set_option backward.isDefEq.respectTransparency false in
/--
An isomorphism of groups gives an order isomorphism between the lattices of subgroups,
defined by sending subgroups to their forward images.

See also `MulEquiv.comapSubgroup` which maps subgroups to their inverse images.
-/
@[to_additive (attr := simps)
/-- An isomorphism of groups gives an order isomorphism between the lattices of subgroups,
defined by sending subgroups to their forward images.

See also `AddEquiv.comapAddSubgroup` which maps subgroups to their inverse images. -/]
/--
Definition of `mapSubgroup` / `mapSubgroup` 的定义

English:
definition mapSubgroup
  signature: {H : Type*} [Group H] (f : G ≃* H)
  body: Subgroup.map f
  invFun := Subgroup.map f.symm
  left_inv sg := by simp [Subgroup.map_map]
  right_inv sh := by simp [Subgroup.map_map]
  map_rel_iff' {sg1 sg2} :=
    ⟨fun h => by simpa [Subgroup.map_map] using
      Subgroup.map_mono (f := (f.symm : H ->* G)) h, Subgroup.map_mono⟩

@[to_additive (

中文:
定义 mapSubgroup
  签名: {H : 类型} [Group H] (f : G ≃* H)
  定义体: Subgroup.map f
  invFun := Subgroup.map f.symm
  left_inv sg := by simp [Subgroup.map_map]
  right_inv sh := by simp [Subgroup.map_map]
  map_rel_iff' {sg1 sg2} :=
    ⟨fun h => by simpa [Subgroup.map_map] using
      Subgroup.map_mono (f := (f.symm : H ->* G)) h, Subgroup.map_mono⟩

@[to_additive (

Depends on / 依赖: Subgroup, Subgroup.map
-/
def mapSubgroup {H : Type*} [Group H] (f : G ≃* H) : Subgroup G ≃o Subgroup H where
  toFun := Subgroup.map f
  invFun := Subgroup.map f.symm
  left_inv sg := by simp [Subgroup.map_map]
  right_inv sh := by simp [Subgroup.map_map]
  map_rel_iff' {sg1 sg2} :=
    ⟨fun h => by simpa [Subgroup.map_map] using
      Subgroup.map_mono (f := (f.symm : H ->* G)) h, Subgroup.map_mono⟩

@[to_additive (attr := simp, norm_cast)]
/--
lemma `coe_mapSubgroup` / 引理 `coe_mapSubgroup`

English:
lemma coe_mapSubgroup
  given: (e : G ≃* H)
  statement: mapSubgroup e = Subgroup.map e.toMonoidHom
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 coe_mapSubgroup
  条件: (e : G ≃* H)
  结论: mapSubgroup e = Subgroup.map e.toMonoidHom
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma coe_mapSubgroup (e : G ≃* H) : mapSubgroup e = Subgroup.map e.toMonoidHom := rfl

@[to_additive (attr := simp)]
/--
lemma `symm_mapSubgroup` / 引理 `symm_mapSubgroup`

English:
lemma symm_mapSubgroup
  given: (e : G ≃* H)
  statement: (mapSubgroup e).symm = mapSubgroup e.symm
  proof: rfl

中文:
引理 symm_mapSubgroup
  条件: (e : G ≃* H)
  结论: (mapSubgroup e).symm = mapSubgroup e.symm
  证明: rfl
-/
lemma symm_mapSubgroup (e : G ≃* H) : (mapSubgroup e).symm = mapSubgroup e.symm := rfl

end MulEquiv

namespace Subgroup

open MonoidHom

variable {N : Type*} [Group N] (f : G ->* N)

@[to_additive (attr := simp, norm_cast)]
/--
lemma `comap_toSubmonoid` / 引理 `comap_toSubmonoid`

English:
lemma comap_toSubmonoid
  given: (e : G ≃* N) (s : Subgroup N)
  proof: rfl

@[to_additive]

中文:
引理 comap_toSubmonoid
  条件: (e : G ≃* N) (s : Subgroup N)
  证明: rfl

@[to_additive]
-/
lemma comap_toSubmonoid (e : G ≃* N) (s : Subgroup N) :
    (s.comap e).toSubmonoid = s.toSubmonoid.comap e.toMonoidHom := rfl

@[to_additive]
/--
theorem `map_comap_le` / 定理 `map_comap_le`

English:
theorem map_comap_le
  given: (H : Subgroup N)
  statement: map f (comap f H) <= H
  proof: (gc_map_comap f).l_u_le _

@[to_additive]

中文:
定理 map_comap_le
  条件: (H : Subgroup N)
  结论: map f (comap f H) <= H
  证明: (gc_map_comap f).l_u_le _

@[to_additive]

Depends on / 依赖: gc_map_comap, l_u_le
-/
theorem map_comap_le (H : Subgroup N) : map f (comap f H) <= H :=
  (gc_map_comap f).l_u_le _

@[to_additive]
/--
theorem `le_comap_map` / 定理 `le_comap_map`

English:
theorem le_comap_map
  given: (H : Subgroup G)
  statement: H <= comap f (map f H)
  proof: (gc_map_comap f).le_u_l _

@[to_additive]

中文:
定理 le_comap_map
  条件: (H : Subgroup G)
  结论: H <= comap f (map f H)
  证明: (gc_map_comap f).le_u_l _

@[to_additive]

Depends on / 依赖: gc_map_comap, le_u_l
-/
theorem le_comap_map (H : Subgroup G) : H <= comap f (map f H) :=
  (gc_map_comap f).le_u_l _

@[to_additive]
/--
theorem `map_eq_comap_of_inverse` / 定理 `map_eq_comap_of_inverse`

English:
theorem map_eq_comap_of_inverse
  statement: {f : G ->* N} {g : N ->* G} (hl : Function.LeftInverse g f)
  proof: SetLike.ext' by rw [coe_map, coe_comap, Set.image_eq_preimage_of_inverse hl hr]

中文:
定理 map_eq_comap_of_inverse
  结论: {f : G ->* N} {g : N ->* G} (hl : Function.LeftInverse g f)
  证明: SetLike.ext' by rw [coe_map, coe_comap, Set.image_eq_preimage_of_inverse hl hr]

Depends on / 依赖: Set.image_eq_preimage_of_inverse, SetLike, SetLike.ext, coe_comap, coe_map, image_eq_preimage_of_inverse
-/
theorem map_eq_comap_of_inverse {f : G ->* N} {g : N ->* G} (hl : Function.LeftInverse g f)
    (hr : Function.RightInverse g f) (H : Subgroup G) : map f H = comap g H :=
SetLike.ext' by rw [coe_map, coe_comap, Set.image_eq_preimage_of_inverse hl hr]

/-- A subgroup is isomorphic to its image under an injective function. If you have an isomorphism,
use `MulEquiv.subgroupMap` for better definitional equalities. -/
@[to_additive
      /-- An additive subgroup is isomorphic to its image under an injective function. If you
      have an isomorphism, use `AddEquiv.addSubgroupMap` for better definitional equalities. -/]
/--
Definition of `equivMapOfInjective` / `equivMapOfInjective` 的定义

English:
definition equivMapOfInjective
  signature: (H : Subgroup G) (f : G ->* N) (hf : Function.Injective f)
  body: { Equiv.Set.image f H hf with map_mul' := fun _ _ => Subtype.ext (f.map_mul _ _) }

@[to_additive (attr := simp)]

中文:
定义 equivMapOfInjective
  签名: (H : Subgroup G) (f : G ->* N) (hf : Function.Injective f)
  定义体: { Equiv.Set.image f H hf with map_mul' := fun _ _ => Subtype.ext (f.map_mul _ _) }

@[to_additive (attr := simp)]

Depends on / 依赖: Equiv.Set.image, Subtype, Subtype.ext, f.map_mul, map_mul
-/
noncomputable def equivMapOfInjective (H : Subgroup G) (f : G ->* N) (hf : Function.Injective f) :
    H ≃* H.map f :=
  { Equiv.Set.image f H hf with map_mul' := fun _ _ => Subtype.ext (f.map_mul _ _) }

@[to_additive (attr := simp)]
/--
theorem `coe_equivMapOfInjective_apply` / 定理 `coe_equivMapOfInjective_apply`

English:
theorem coe_equivMapOfInjective_apply
  statement: (H : Subgroup G) (f : G ->* N) (hf : Function.Injective f)
  proof: rfl

中文:
定理 coe_equivMapOfInjective_apply
  结论: (H : Subgroup G) (f : G ->* N) (hf : Function.Injective f)
  证明: rfl
-/
theorem coe_equivMapOfInjective_apply (H : Subgroup G) (f : G ->* N) (hf : Function.Injective f)
    (h : H) : (equivMapOfInjective H f hf h : N) = f h :=
  rfl

end Subgroup

variable {N : Type*} [Group N]

namespace MonoidHom

/-- The `MonoidHom` from the preimage of a subgroup to itself. -/
@[to_additive (attr := simps!) /-- the `AddMonoidHom` from the preimage of an
additive subgroup to itself. -/]
/--
Definition of `subgroupComap` / `subgroupComap` 的定义

English:
definition subgroupComap
  signature: (f : G ->* G') (H' : Subgroup G')
  body: f.submonoidComap H'.toSubmonoid

@[to_additive]

中文:
定义 subgroupComap
  签名: (f : G ->* G') (H' : Subgroup G')
  定义体: f.submonoidComap H'.toSubmonoid

@[to_additive]

Depends on / 依赖: f.submonoidComap, submonoidComap, toSubmonoid
-/
def subgroupComap (f : G ->* G') (H' : Subgroup G') : H'.comap f ->* H' :=
  f.submonoidComap H'.toSubmonoid

@[to_additive]
/--
lemma `subgroupComap_surjective_of_surjective` / 引理 `subgroupComap_surjective_of_surjective`

English:
lemma subgroupComap_surjective_of_surjective
  given: (f : G ->* G') (H' : Subgroup G') (hf : Surjective f)
  proof: f.submonoidComap_surjective_of_surjective H'.toSubmonoid hf

中文:
引理 subgroupComap_surjective_of_surjective
  条件: (f : G ->* G') (H' : Subgroup G') (hf : Surjective f)
  证明: f.submonoidComap_surjective_of_surjective H'.toSubmonoid hf

Depends on / 依赖: f.submonoidComap_surjective_of_surjective, submonoidComap_surjective_of_surjective, toSubmonoid
-/
lemma subgroupComap_surjective_of_surjective (f : G ->* G') (H' : Subgroup G') (hf : Surjective f) :
    Surjective (f.subgroupComap H') :=
  f.submonoidComap_surjective_of_surjective H'.toSubmonoid hf

/-- The `MonoidHom` from a subgroup to its image. -/
@[to_additive (attr := simps!) /-- the `AddMonoidHom` from an additive subgroup to its image -/]
/--
Definition of `subgroupMap` / `subgroupMap` 的定义

English:
definition subgroupMap
  signature: (f : G ->* G') (H : Subgroup G)
  body: f.submonoidMap H.toSubmonoid

@[to_additive]

中文:
定义 subgroupMap
  签名: (f : G ->* G') (H : Subgroup G)
  定义体: f.submonoidMap H.toSubmonoid

@[to_additive]

Depends on / 依赖: H.toSubmonoid, f.submonoidMap, submonoidMap, toSubmonoid
-/
def subgroupMap (f : G ->* G') (H : Subgroup G) : H ->* H.map f :=
  f.submonoidMap H.toSubmonoid

@[to_additive]
/--
theorem `subgroupMap_surjective` / 定理 `subgroupMap_surjective`

English:
theorem subgroupMap_surjective
  given: (f : G ->* G') (H : Subgroup G)
  proof: f.submonoidMap_surjective H.toSubmonoid

中文:
定理 subgroupMap_surjective
  条件: (f : G ->* G') (H : Subgroup G)
  证明: f.submonoidMap_surjective H.toSubmonoid

Depends on / 依赖: H.toSubmonoid, f.submonoidMap_surjective, submonoidMap_surjective, toSubmonoid
-/
theorem subgroupMap_surjective (f : G ->* G') (H : Subgroup G) :
    Function.Surjective (f.subgroupMap H) :=
  f.submonoidMap_surjective H.toSubmonoid

end MonoidHom

namespace MulEquiv

variable {H K : Subgroup G}

/-- Makes the identity isomorphism from a proof two subgroups of a multiplicative
group are equal. -/
@[to_additive
      /-- Makes the identity additive isomorphism from a proof
      two subgroups of an additive group are equal. -/]
/--
Definition of `subgroupCongr` / `subgroupCongr` 的定义

English:
definition subgroupCongr
  signature: (h : H = K)
  body: { Equiv.setCongr <| congr_arg _ h with map_mul' := fun _ _ => rfl }

@[to_additive (attr := simp)]

中文:
定义 subgroupCongr
  签名: (h : H = K)
  定义体: { Equiv.setCongr <| congr_arg _ h with map_mul' := fun _ _ => rfl }

@[to_additive (attr := simp)]

Depends on / 依赖: Equiv.setCongr, congr_arg, map_mul, setCongr
-/
def subgroupCongr (h : H = K) : H ≃* K :=
  { Equiv.setCongr <| congr_arg _ h with map_mul' := fun _ _ => rfl }

@[to_additive (attr := simp)]
/--
lemma `subgroupCongr_apply` / 引理 `subgroupCongr_apply`

English:
lemma subgroupCongr_apply
  given: (h : H = K) (x)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 subgroupCongr_apply
  条件: (h : H = K) (x)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma subgroupCongr_apply (h : H = K) (x) :
    (MulEquiv.subgroupCongr h x : G) = x := rfl

@[to_additive (attr := simp)]
/--
lemma `subgroupCongr_symm_apply` / 引理 `subgroupCongr_symm_apply`

English:
lemma subgroupCongr_symm_apply
  given: (h : H = K) (x)
  proof: rfl

中文:
引理 subgroupCongr_symm_apply
  条件: (h : H = K) (x)
  证明: rfl
-/
lemma subgroupCongr_symm_apply (h : H = K) (x) :
    ((MulEquiv.subgroupCongr h).symm x : G) = x := rfl

/-- A subgroup is isomorphic to its image under an isomorphism. If you only have an injective map,
use `Subgroup.equivMapOfInjective`. -/
@[to_additive
      /-- An additive subgroup is isomorphic to its image under an isomorphism. If you only
      have an injective map, use `AddSubgroup.equivMapOfInjective`. -/]
/--
Definition of `subgroupMap` / `subgroupMap` 的定义

English:
definition subgroupMap
  signature: (e : G ≃* G') (H : Subgroup G)
  body: MulEquiv.submonoidMap (e : G ≃* G') H.toSubmonoid

@[to_additive (attr := simp)]

中文:
定义 subgroupMap
  签名: (e : G ≃* G') (H : Subgroup G)
  定义体: MulEquiv.submonoidMap (e : G ≃* G') H.toSubmonoid

@[to_additive (attr := simp)]

Depends on / 依赖: H.toSubmonoid, MulEquiv, MulEquiv.submonoidMap, submonoidMap, toSubmonoid
-/
def subgroupMap (e : G ≃* G') (H : Subgroup G) : H ≃* H.map (e : G ->* G') :=
  MulEquiv.submonoidMap (e : G ≃* G') H.toSubmonoid

@[to_additive (attr := simp)]
/--
theorem `coe_subgroupMap_apply` / 定理 `coe_subgroupMap_apply`

English:
theorem coe_subgroupMap_apply
  given: (e : G ≃* G') (H : Subgroup G) (g : H)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_subgroupMap_apply
  条件: (e : G ≃* G') (H : Subgroup G) (g : H)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_subgroupMap_apply (e : G ≃* G') (H : Subgroup G) (g : H) :
    ((subgroupMap e H g : H.map (e : G ->* G')) : G') = e g :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `subgroupMap_symm_apply` / 定理 `subgroupMap_symm_apply`

English:
theorem subgroupMap_symm_apply
  given: (e : G ≃* G') (H : Subgroup G) (g : H.map (e : G ->* G'))
  proof: rfl

中文:
定理 subgroupMap_symm_apply
  条件: (e : G ≃* G') (H : Subgroup G) (g : H.map (e : G ->* G'))
  证明: rfl
-/
theorem subgroupMap_symm_apply (e : G ≃* G') (H : Subgroup G) (g : H.map (e : G ->* G')) :
(e.subgroupMap H).symm g = ⟨e.symm g, SetLike.mem_coe.1 Set.mem_image_equiv.1 g.2⟩ :=
  rfl

end MulEquiv

namespace MonoidHom

open Subgroup

@[to_additive]
/--
theorem `closure_preimage_le` / 定理 `closure_preimage_le`

English:
theorem closure_preimage_le
  given: (f : G ->* N) (s : Set N)
  statement: closure (f ⁻¹' s) <= (closure s).comap f
  proof: (closure_le _).2 fun x hx => by rw [SetLike.mem_coe, mem_comap]; exact subset_closure hx

中文:
定理 closure_preimage_le
  条件: (f : G ->* N) (s : Set N)
  结论: closure (f ⁻¹' s) <= (closure s).comap f
  证明: (closure_le _).2 fun x hx => by rw [SetLike.mem_coe, mem_comap]; exact subset_closure hx

Depends on / 依赖: SetLike, SetLike.mem_coe, closure_le, mem_coe, mem_comap, subset_closure
-/
theorem closure_preimage_le (f : G ->* N) (s : Set N) : closure (f ⁻¹' s) <= (closure s).comap f :=
  (closure_le _).2 fun x hx => by rw [SetLike.mem_coe, mem_comap]; exact subset_closure hx

/-- The image under a monoid homomorphism of the subgroup generated by a set equals the subgroup
generated by the image of the set. -/
@[to_additive
      /-- The image under an `AddMonoid` hom of the `AddSubgroup` generated by a set equals
      the `AddSubgroup` generated by the image of the set. -/]
/--
theorem `map_closure` / 定理 `map_closure`

English:
theorem map_closure
  given: (f : G ->* N) (s : Set G)
  statement: (closure s).map f = closure (f '' s)
  proof: Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (Subgroup.gi N).gc (Subgroup.gi G).gc
    fun _ => rfl

中文:
定理 map_closure
  条件: (f : G ->* N) (s : Set G)
  结论: (closure s).map f = closure (f '' s)
  证明: Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (Subgroup.gi N).gc (Subgroup.gi G).gc
    fun _ => rfl

Depends on / 依赖: Set.image_preimage.l_comm_of_u_comm, Subgroup, Subgroup.gi, gc_map_comap, image_preimage, l_comm_of_u_comm
-/
theorem map_closure (f : G ->* N) (s : Set G) : (closure s).map f = closure (f '' s) :=
  Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (Subgroup.gi N).gc (Subgroup.gi G).gc
    fun _ => rfl

end MonoidHom

namespace Subgroup

@[to_additive]
/--
lemma `surjOn_iff_le_map` / 引理 `surjOn_iff_le_map`

English:
lemma surjOn_iff_le_map
  given: {f : G ->* N} {H : Subgroup G} {K : Subgroup N}
  proof: Iff.rfl

@[to_additive (attr := simp)]

中文:
引理 surjOn_iff_le_map
  条件: {f : G ->* N} {H : Subgroup G} {K : Subgroup N}
  证明: Iff.rfl

@[to_additive (attr := simp)]

Depends on / 依赖: Iff.rfl, f.isUnit_eqLocusM_mk_iff, isUnit_eqLocusM_mk_iff, r.prop
-/
lemma surjOn_iff_le_map {f : G ->* N} {H : Subgroup G} {K : Subgroup N} :
    Set.SurjOn f H K ↔ K <= H.map f :=
  Iff.rfl

@[to_additive (attr := simp)]
/--
theorem `equivMapOfInjective_coe_mulEquiv` / 定理 `equivMapOfInjective_coe_mulEquiv`

English:
theorem equivMapOfInjective_coe_mulEquiv
  given: (H : Subgroup G) (e : G ≃* G')
  proof: by
  ext
  rfl

中文:
定理 equivMapOfInjective_coe_mulEquiv
  条件: (H : Subgroup G) (e : G ≃* G')
  证明: by
  ext
  rfl
-/
theorem equivMapOfInjective_coe_mulEquiv (H : Subgroup G) (e : G ≃* G') :
    H.equivMapOfInjective (e : G ->* G') (EquivLike.injective e) = e.subgroupMap H := by
  ext
  rfl

end Subgroup
