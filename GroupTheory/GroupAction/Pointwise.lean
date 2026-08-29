/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth, Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Data.Set.Function
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.Algebra.Group.Units.Hom

/-!
# Pointwise actions of equivariant maps

- `image_smul_setₛₗ` : under a `σ`-equivariant map,
  one has `f '' (c • s) = (σ c) • f '' s`.

- `preimage_smul_setₛₗ'` is a general version of the equality
  `f ⁻¹' (σ c • s) = c • f⁻¹' s`.
  It requires that `c` acts surjectively and `σ c` acts injectively and
  is provided with specific versions:
  - `preimage_smul_setₛₗ_of_isUnit_isUnit` when `c` and `σ c` are units
  - `IsUnit.preimage_smul_setₛₗ` when `σ` belongs to a `MonoidHomClass` and `c` is a unit
  - `MonoidHom.preimage_smul_setₛₗ` when `σ` is a `MonoidHom` and `c` is a unit
  - `Group.preimage_smul_setₛₗ` : when the types of `c` and `σ c` are groups.

- `image_smul_set`, `preimage_smul_set` and `Group.preimage_smul_set` are
  the variants when `σ` is the identity.

-/

public section

open Function Set Pointwise


section MulActionSemiHomClass

section SMul

variable {M N F : Type*} {α β : Type*} {σ : M -> N} [SMul M α] [SMul N β] [FunLike F α β]
  [MulActionSemiHomClass F σ α β] {f : F} {s : Set α} {t : Set β}

@[to_additive (attr := simp)]
/--
theorem `image_smul_setₛₗ` / 定理 `image_smul_setₛₗ`

English:
theorem image_smul_setₛₗ
  given: (f : F) (c : M) (s : Set α)
  proof: Semiconj.set_image (map_smulₛₗ f c) s

@[to_additive]

中文:
定理 image_smul_setₛₗ
  条件: (f : F) (c : M) (s : 集合 α)
  证明: Semiconj.set_image (map_smulₛₗ f c) s

@[to_additive]

Depends on / 依赖: Semiconj, Semiconj.set_image, set_image
-/
theorem image_smul_setₛₗ (f : F) (c : M) (s : Set α) :
    f '' (c • s) = σ c • f '' s :=
  Semiconj.set_image (map_smulₛₗ f c) s

@[to_additive]
/--
theorem `Set.MapsTo.smul_setₛₗ` / 定理 `Set.MapsTo.smul_setₛₗ`

English:
theorem Set.MapsTo.smul_setₛₗ
  given: (hst : MapsTo f s t) (c : M)
  statement: MapsTo f (c • s) (σ c • t)
  proof: Function.Semiconj.mapsTo_image_right (map_smulₛₗ _ _) hst

中文:
定理 集合.映射到.smul_setₛₗ
  条件: (hst : 映射到 f s t) (c : M)
  结论: 映射到 f (c • s) (σ c • t)
  证明: Function.Semiconj.mapsTo_image_right (map_smulₛₗ _ _) hst

Depends on / 依赖: Function, Function.Semiconj.mapsTo_image_right, Semiconj, mapsTo_image_right
-/
theorem Set.MapsTo.smul_setₛₗ (hst : MapsTo f s t) (c : M) : MapsTo f (c • s) (σ c • t) :=
  Function.Semiconj.mapsTo_image_right (map_smulₛₗ _ _) hst

/-- Translation of preimage is contained in preimage of translation -/
@[to_additive]
/--
theorem `smul_preimage_set_subsetₛₗ` / 定理 `smul_preimage_set_subsetₛₗ`

English:
theorem smul_preimage_set_subsetₛₗ
  given: (f : F) (c : M) (t : Set β)
  statement: c • f ⁻¹' t subseteq f ⁻¹' (σ c • t)
  proof: ((mapsTo_preimage f t).smul_setₛₗ c).subset_preimage

中文:
定理 smul_preimage_set_subsetₛₗ
  条件: (f : F) (c : M) (t : 集合 β)
  结论: c • f ⁻¹' t subseteq f ⁻¹' (σ c • t)
  证明: ((mapsTo_preimage f t).smul_setₛₗ c).subset_preimage

Depends on / 依赖: mapsTo_preimage, subset_preimage
-/
theorem smul_preimage_set_subsetₛₗ (f : F) (c : M) (t : Set β) : c • f ⁻¹' t subseteq f ⁻¹' (σ c • t) :=
  ((mapsTo_preimage f t).smul_setₛₗ c).subset_preimage

/-- General version of `preimage_smul_setₛₗ`.
This version assumes that the scalar multiplication by `c` is surjective
while the scalar multiplication by `σ c` is injective. -/
@[to_additive /-- General version of `preimage_vadd_setₛₗ`.
This version assumes that the vector addition of `c` is surjective
while the vector addition of `σ c` is injective. -/]
/--
theorem `preimage_smul_setₛₗ'` / 定理 `preimage_smul_setₛₗ'`

English:
theorem preimage_smul_setₛₗ'
  statement: {c : M}
  proof: by
  refine Subset.antisymm ?_ (smul_preimage_set_subsetₛₗ f c t)
  rw [subset_def]; rw [hc.forall]
  rintro x ⟨y, hy, hxy⟩
  rw [map_smulₛₗ]; rw [hc'.eq_iff] at hxy
  subst y
  exact smul_mem_smul_set hy

中文:
定理 preimage_smul_setₛₗ'
  结论: {c : M}
  证明: by
  refine Subset.antisymm ?_ (smul_preimage_set_subsetₛₗ f c t)
  rw [subset_def]; rw [hc.forall]
  rintro x ⟨y, hy, hxy⟩
  rw [map_smulₛₗ]; rw [hc'.eq_iff] at hxy
  subst y
  exact smul_mem_smul_set hy

Depends on / 依赖: Subset, Subset.antisymm, antisymm, eq_iff, hc.forall, smul_mem_smul_set, subset_def
-/
theorem preimage_smul_setₛₗ' {c : M}
    (hc : Function.Surjective (fun (m : α) => c • m))
    (hc' : Function.Injective (fun (n : β) => σ c • n)) :
    f ⁻¹' (σ c • t) = c • f ⁻¹' t := by
  refine Subset.antisymm ?_ (smul_preimage_set_subsetₛₗ f c t)
  rw [subset_def]; rw [hc.forall]
  rintro x ⟨y, hy, hxy⟩
  rw [map_smulₛₗ]; rw [hc'.eq_iff] at hxy
  subst y
  exact smul_mem_smul_set hy

end SMul

section Monoid

variable {M N F : Type*} {α β : Type*} {σ : M -> N} [Monoid M] [Monoid N]
  [MulAction M α] [MulAction N β] [FunLike F α β] [MulActionSemiHomClass F σ α β]
  {f : F} {s : Set α} {t : Set β} {c : M}

/-- `preimage_smul_setₛₗ` when both scalars act by unit -/
@[to_additive]
/--
theorem `preimage_smul_setₛₗ_of_isUnit_isUnit` / 定理 `preimage_smul_setₛₗ_of_isUnit_isUnit`

English:
theorem preimage_smul_setₛₗ_of_isUnit_isUnit
  statement: (f : F)
  proof: preimage_smul_setₛₗ' hc.smul_bijective.surjective hc'.smul_bijective.injective

中文:
定理 preimage_smul_setₛₗ_of_isUnit_isUnit
  结论: (f : F)
  证明: preimage_smul_setₛₗ' hc.smul_bijective.surjective hc'.smul_bijective.injective

Depends on / 依赖: hc.smul_bijective.surjective, injective, smul_bijective, smul_bijective.injective, surjective
-/
theorem preimage_smul_setₛₗ_of_isUnit_isUnit (f : F)
    (hc : IsUnit c) (hc' : IsUnit (σ c)) (t : Set β) : f ⁻¹' (σ c • t) = c • f ⁻¹' t :=
  preimage_smul_setₛₗ' hc.smul_bijective.surjective hc'.smul_bijective.injective

/-- `preimage_smul_setₛₗ` when `c` is a unit and `σ` is a monoid homomorphism. -/
@[to_additive]
/--
theorem `IsUnit.preimage_smul_setₛₗ` / 定理 `IsUnit.preimage_smul_setₛₗ`

English:
theorem IsUnit.preimage_smul_setₛₗ
  statement: {F G : Type*} [FunLike G M N] [MonoidHomClass G M N]
  proof: preimage_smul_setₛₗ_of_isUnit_isUnit _ hc (hc.map _) _

中文:
定理 是单位.preimage_smul_setₛₗ
  结论: {F G : 类型} [函数状 G M N] [幺半群态射类 G M N]
  证明: preimage_smul_setₛₗ_of_isUnit_isUnit _ hc (hc.map _) _

Depends on / 依赖: hc.map
-/
theorem IsUnit.preimage_smul_setₛₗ {F G : Type*} [FunLike G M N] [MonoidHomClass G M N]
    (σ : G) [FunLike F α β] [MulActionSemiHomClass F σ α β] (f : F) (hc : IsUnit c) (t : Set β) :
    f ⁻¹' (σ c • t) = c • f ⁻¹' t :=
  preimage_smul_setₛₗ_of_isUnit_isUnit _ hc (hc.map _) _

-- TODO: when you remove the next 2 aliases,
-- please move the group version below out of the `Group` namespace.
/-- `preimage_smul_setₛₗ` when `c` is a unit and `σ` is a monoid homomorphism. -/
@[to_additive]
/--
theorem `MonoidHom.preimage_smul_setₛₗ` / 定理 `MonoidHom.preimage_smul_setₛₗ`

English:
theorem MonoidHom.preimage_smul_setₛₗ
  statement: {F : Type*} (σ : M ->* N) [FunLike F α β]
  proof: hc.preimage_smul_setₛₗ σ f t

中文:
定理 幺半群态射.preimage_smul_setₛₗ
  结论: {F : 类型} (σ : M ->* N) [函数状 F α β]
  证明: hc.preimage_smul_setₛₗ σ f t
-/
protected theorem MonoidHom.preimage_smul_setₛₗ {F : Type*} (σ : M ->* N) [FunLike F α β]
    [MulActionSemiHomClass F σ α β] (f : F) (hc : IsUnit c) (t : Set β) :
    f ⁻¹' (σ c • t) = c • f ⁻¹' t :=
  hc.preimage_smul_setₛₗ σ f t

end Monoid

/-- `preimage_smul_setₛₗ` in the context of groups -/
@[to_additive]
/--
theorem `Group.preimage_smul_setₛₗ` / 定理 `Group.preimage_smul_setₛₗ`

English:
theorem Group.preimage_smul_setₛₗ
  statement: {G H α β : Type*} [Group G] [Group H] (σ : G -> H)
  proof: preimage_smul_setₛₗ_of_isUnit_isUnit _ (Group.isUnit _) (Group.isUnit _) _

中文:
定理 群.preimage_smul_setₛₗ
  结论: {G H α β : 类型} [群 G] [群 H] (σ : G -> H)
  证明: preimage_smul_setₛₗ_of_isUnit_isUnit _ (Group.isUnit _) (Group.isUnit _) _

Depends on / 依赖: Group.isUnit, isUnit
-/
theorem Group.preimage_smul_setₛₗ {G H α β : Type*} [Group G] [Group H] (σ : G -> H)
    [MulAction G α] [MulAction H β]
    {F : Type*} [FunLike F α β] [MulActionSemiHomClass F σ α β] (f : F) (c : G) (t : Set β) :
    f ⁻¹' (σ c • t) = c • f ⁻¹' t :=
  preimage_smul_setₛₗ_of_isUnit_isUnit _ (Group.isUnit _) (Group.isUnit _) _

end MulActionSemiHomClass

section MulActionHomClass

section SMul

variable {M α β F : Type*} [SMul M α] [SMul M β] [FunLike F α β] [MulActionHomClass F M α β]

@[to_additive]
/--
theorem `image_smul_set` / 定理 `image_smul_set`

English:
theorem image_smul_set
  given: (f : F) (c : M) (s : Set α)
  statement: f '' (c • s) = c • f '' s
  proof: image_smul_setₛₗ f c s

@[to_additive]

中文:
定理 image_smul_set
  条件: (f : F) (c : M) (s : 集合 α)
  结论: f '' (c • s) = c • f '' s
  证明: image_smul_setₛₗ f c s

@[to_additive]
-/
theorem image_smul_set (f : F) (c : M) (s : Set α) : f '' (c • s) = c • f '' s :=
  image_smul_setₛₗ f c s

@[to_additive]
/--
theorem `smul_preimage_set_subset` / 定理 `smul_preimage_set_subset`

English:
theorem smul_preimage_set_subset
  given: (f : F) (c : M) (t : Set β)
  statement: c • f ⁻¹' t subseteq f ⁻¹' (c • t)
  proof: smul_preimage_set_subsetₛₗ f c t

@[to_additive]

中文:
定理 smul_preimage_set_subset
  条件: (f : F) (c : M) (t : 集合 β)
  结论: c • f ⁻¹' t subseteq f ⁻¹' (c • t)
  证明: smul_preimage_set_subsetₛₗ f c t

@[to_additive]
-/
theorem smul_preimage_set_subset (f : F) (c : M) (t : Set β) : c • f ⁻¹' t subseteq f ⁻¹' (c • t) :=
  smul_preimage_set_subsetₛₗ f c t

@[to_additive]
/--
theorem `Set.MapsTo.smul_set` / 定理 `Set.MapsTo.smul_set`

English:
theorem Set.MapsTo.smul_set
  given: {f : F} {s : Set α} {t : Set β} (hst : MapsTo f s t) (c : M)
  proof: hst.smul_setₛₗ c

中文:
定理 集合.映射到.smul_set
  条件: {f : F} {s : 集合 α} {t : 集合 β} (hst : 映射到 f s t) (c : M)
  证明: hst.smul_setₛₗ c

Depends on / 依赖: hst.smul_set
-/
theorem Set.MapsTo.smul_set {f : F} {s : Set α} {t : Set β} (hst : MapsTo f s t) (c : M) :
    MapsTo f (c • s) (c • t) :=
  hst.smul_setₛₗ c

end SMul

@[to_additive]
/--
theorem `IsUnit.preimage_smul_set` / 定理 `IsUnit.preimage_smul_set`

English:
theorem IsUnit.preimage_smul_set
  statement: {M α β F : Type*} [Monoid M] [MulAction M α] [MulAction M β]
  proof: preimage_smul_setₛₗ_of_isUnit_isUnit f hc hc t

中文:
定理 是单位.preimage_smul_set
  结论: {M α β F : 类型} [幺半群 M] [乘法作用 M α] [乘法作用 M β]
  证明: preimage_smul_setₛₗ_of_isUnit_isUnit f hc hc t
-/
theorem IsUnit.preimage_smul_set {M α β F : Type*} [Monoid M] [MulAction M α] [MulAction M β]
    [FunLike F α β] [MulActionHomClass F M α β] (f : F) {c : M} (hc : IsUnit c) (t : Set β) :
    f ⁻¹' (c • t) = c • f ⁻¹' t :=
  preimage_smul_setₛₗ_of_isUnit_isUnit f hc hc t

-- TODO: when you remove the next 2 aliases,
-- please move the `Group` version to the root namespace.
@[to_additive]
/--
theorem `Group.preimage_smul_set` / 定理 `Group.preimage_smul_set`

English:
theorem Group.preimage_smul_set
  statement: {G : Type*} [Group G] {α β : Type*} [MulAction G α] [MulAction G β]
  proof: (Group.isUnit c).preimage_smul_set f t

中文:
定理 群.preimage_smul_set
  结论: {G : 类型} [群 G] {α β : 类型} [乘法作用 G α] [乘法作用 G β]
  证明: (Group.isUnit c).preimage_smul_set f t

Depends on / 依赖: Group.isUnit, isUnit, preimage_smul_set
-/
theorem Group.preimage_smul_set {G : Type*} [Group G] {α β : Type*} [MulAction G α] [MulAction G β]
    {F : Type*} [FunLike F α β] [MulActionHomClass F G α β] (f : F) (c : G) (t : Set β) :
    f ⁻¹' (c • t) = c • f ⁻¹' t :=
  (Group.isUnit c).preimage_smul_set f t

end MulActionHomClass
