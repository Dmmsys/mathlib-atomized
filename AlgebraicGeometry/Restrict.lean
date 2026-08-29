/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Over

/-!
# Restriction of Schemes and Morphisms

## Main definition
- `AlgebraicGeometry.Scheme.restrict`: The restriction of a scheme along an open embedding.
  The map `X.restrict f ⟶ X` is `AlgebraicGeometry.Scheme.ofRestrict`.
  `U : X.Opens` has a coercion to `Scheme` and `U.ι` is a shorthand
  for `X.restrict U.open_embedding : U ⟶ X`.
- `AlgebraicGeometry.morphismRestrict`: The restriction of `X ⟶ Y` to `X ∣_ᵤ f ⁻¹ᵁ U ⟶ Y ∣_ᵤ U`.

-/

@[expose] public section

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737


noncomputable section

open TopologicalSpace CategoryTheory Opposite CategoryTheory.Limits

namespace AlgebraicGeometry

universe v v₁ v₂ u u₁

variable {C : Type u₁} [Category.{v} C]

section

variable {X : Scheme.{u}} (U : X.Opens)

namespace Scheme.Opens

/-- Open subset of a scheme as a scheme. -/
@[coe]
/--
Definition of `toScheme` / `toScheme` 的定义

English:
definition toScheme
  signature: {X : Scheme.{u}} (U : X.Opens)
  body: X.restrict U.isOpenEmbedding

中文:
定义 toScheme
  签名: {X : 概形.{u}} (U : X.Opens)
  定义体: X.restrict U.isOpenEmbedding

Depends on / 依赖: U.isOpenEmbedding, X.restrict, isOpenEmbedding, restrict
-/
def toScheme {X : Scheme.{u}} (U : X.Opens) : Scheme.{u} :=
  X.restrict U.isOpenEmbedding

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeOut X.Opens Scheme
  body: ⟨toScheme⟩

中文:
实例 :
  签名: CoeOut X.Opens 概形
  定义体: ⟨toScheme⟩

Depends on / 依赖: toScheme
-/
instance : CoeOut X.Opens Scheme := ⟨toScheme⟩

/--
Definition of `ι` / `ι` 的定义

English:
definition ι
  signature: : ↑U ⟶ X
  body: X.ofRestrict _

@[simp]

中文:
定义 ι
  签名: : ↑U ⟶ X
  定义体: X.ofRestrict _

@[simp]

Depends on / 依赖: X.ofRestrict, ofRestrict
-/
def ι : ↑U ⟶ X := X.ofRestrict _

@[simp]
/--
lemma `ι_apply` / 引理 `ι_apply`

English:
lemma ι_apply
  given: (x : U)
  statement: U.ι x = x.val
  proof: rfl

中文:
引理 ι_apply
  条件: (x : U)
  结论: U.ι x = x.val
  证明: rfl
-/
lemma ι_apply (x : U) : U.ι x = x.val := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOpenImmersion U.ι
  body: inferInstanceAs (IsOpenImmersion (X.ofRestrict _))

中文:
实例 :
  签名: 是开浸入 U.ι
  定义体: inferInstanceAs (IsOpenImmersion (X.ofRestrict _))

Depends on / 依赖: IsOpenImmersion, X.ofRestrict, ofRestrict
-/
instance : IsOpenImmersion U.ι := inferInstanceAs (IsOpenImmersion (X.ofRestrict _))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: U.toScheme.CanonicallyOver X
  body: U.ι

中文:
实例 :
  签名: U.toScheme.CanonicallyOver X
  定义体: U.ι
-/
@[simps! over] instance : U.toScheme.CanonicallyOver X where
  hom := U.ι

/--
lemma `ι_comp_over` / 引理 `ι_comp_over`

English:
lemma ι_comp_over
  given: (S : Scheme.{u}) [X.Over S]
  statement: U.ι ≫ X ↘ S = U.toScheme ↘ S
  proof: rfl

中文:
引理 ι_comp_over
  条件: (S : 概形.{u}) [X.Over S]
  结论: U.ι ≫ X ↘ S = U.toScheme ↘ S
  证明: rfl
-/
lemma ι_comp_over (S : Scheme.{u}) [X.Over S] : U.ι ≫ X ↘ S = U.toScheme ↘ S := rfl

instance (U : X.Opens) : U.ι.IsOver X where

/--
lemma `toScheme_carrier` / 引理 `toScheme_carrier`

English:
lemma toScheme_carrier
  statement: (U : Type u) = (U : Set X)
  proof: rfl

中文:
引理 toScheme_carrier
  结论: (U : 类型u) = (U : 集合 X)
  证明: rfl
-/
lemma toScheme_carrier : (U : Type u) = (U : Set X) := rfl

/--
lemma `toScheme_presheaf_obj` / 引理 `toScheme_presheaf_obj`

English:
lemma toScheme_presheaf_obj
  given: (V)
  statement: Γ(U, V) = Γ(X, U.ι ''ᵁ V)
  proof: rfl

中文:
引理 toScheme_presheaf_obj
  条件: (V)
  结论: Γ(U, V) = Γ(X, U.ι ''ᵁ V)
  证明: rfl
-/
lemma toScheme_presheaf_obj (V) : Γ(U, V) = Γ(X, U.ι ''ᵁ V) := rfl

/--
lemma `forall_toScheme` / 引理 `forall_toScheme`

English:
lemma forall_toScheme
  given: {U : X.Opens} {P : U.toScheme -> Prop}
  proof: Subtype.forall

中文:
引理 对任意_toScheme
  条件: {U : X.Opens} {P : U.toScheme -> 命题}
  证明: Subtype.forall

Depends on / 依赖: Subtype, Subtype.forall
-/
lemma forall_toScheme {U : X.Opens} {P : U.toScheme -> Prop} :
    (forall x, P x) ↔ forall (x : X) (hx : x in U), P ⟨x, hx⟩ := Subtype.forall

/--
lemma `exists_toScheme` / 引理 `exists_toScheme`

English:
lemma exists_toScheme
  given: {U : X.Opens} {P : U.toScheme -> Prop}
  proof: Subtype.exists

@[simp]

中文:
引理 存在_toScheme
  条件: {U : X.Opens} {P : U.toScheme -> 命题}
  证明: Subtype.exists

@[simp]

Depends on / 依赖: Subtype, Subtype.exists
-/
lemma exists_toScheme {U : X.Opens} {P : U.toScheme -> Prop} :
    (exists x, P x) ↔ exists (x : X) (hx : x in U), P ⟨x, hx⟩ := Subtype.exists

@[simp]
/--
lemma `toScheme_presheaf_map` / 引理 `toScheme_presheaf_map`

English:
lemma toScheme_presheaf_map
  given: {V W} (i : V ⟶ W)
  proof: rfl

@[simp]

中文:
引理 toScheme_presheaf_map
  条件: {V W} (i : V ⟶ W)
  证明: rfl

@[simp]
-/
lemma toScheme_presheaf_map {V W} (i : V ⟶ W) :
    U.toScheme.presheaf.map i = X.presheaf.map (U.ι.opensFunctor.map i.unop).op := rfl

@[simp]
/--
lemma `ι_app` / 引理 `ι_app`

English:
lemma ι_app
  given: (V)
  statement: U.ι.app V = X.presheaf.map
  proof: rfl

@[simp]

中文:
引理 ι_app
  条件: (V)
  结论: U.ι.app V = X.presheaf.map
  证明: rfl

@[simp]

Depends on / 依赖: Set.image_preimage_subset, image_preimage_subset
-/
lemma ι_app (V) : U.ι.app V = X.presheaf.map
    (homOfLE (x := U.ι ''ᵁ U.ι ⁻¹ᵁ V) (Set.image_preimage_subset _ _)).op :=
  rfl

@[simp]
/--
lemma `ι_appTop` / 引理 `ι_appTop`

English:
lemma ι_appTop
  proof: rfl

中文:
引理 ι_appTop
  证明: rfl

Depends on / 依赖: le_top
-/
lemma ι_appTop :
    U.ι.appTop = X.presheaf.map (homOfLE (x := U.ι ''ᵁ ⊤) le_top).op :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `ι_appLE` / 引理 `ι_appLE`

English:
lemma ι_appLE
  given: (V W e)
  proof: by
  simp only [Hom.appLE, ι_app, toScheme_presheaf_map, Quiver.Hom.unop_op,
    Hom.opensFunctor_map_homOfLE, ← Functor.map_comp]
  rfl

@[simp]

中文:
引理 ι_appLE
  条件: (V W e)
  证明: by
  simp only [Hom.appLE, ι_app, toScheme_presheaf_map, Quiver.Hom.unop_op,
    Hom.opensFunctor_map_homOfLE, ← Functor.map_comp]
  rfl

@[simp]

Depends on / 依赖: Functor, Functor.map_comp, Hom.appLE, Hom.opensFunctor_map_homOfLE, Quiver, Quiver.Hom.unop_op, Set.image_subset_iff.mpr, image_subset_iff, map_comp, opensFunctor_map_homOfLE, toScheme_presheaf_map, unop_op
-/
lemma ι_appLE (V W e) :
    U.ι.appLE V W e =
      X.presheaf.map (homOfLE (x := U.ι ''ᵁ W) (Set.image_subset_iff.mpr ‹_›)).op := by
  simp only [Hom.appLE, ι_app, toScheme_presheaf_map, Quiver.Hom.unop_op,
    Hom.opensFunctor_map_homOfLE, ← Functor.map_comp]
  rfl

@[simp]
/--
lemma `ι_appIso` / 引理 `ι_appIso`

English:
lemma ι_appIso
  given: (V)
  statement: U.ι.appIso V = Iso.refl _
  proof: X.ofRestrict_appIso _ _

@[simp]

中文:
引理 ι_appIso
  条件: (V)
  结论: U.ι.appIso V = 同构.refl _
  证明: X.ofRestrict_appIso _ _

@[simp]

Depends on / 依赖: X.ofRestrict_appIso, ofRestrict_appIso
-/
lemma ι_appIso (V) : U.ι.appIso V = Iso.refl _ :=
  X.ofRestrict_appIso _ _

@[simp]
/--
lemma `opensRange_ι` / 引理 `opensRange_ι`

English:
lemma opensRange_ι
  statement: U.ι.opensRange = U
  proof: Opens.ext Subtype.range_val

@[simp]

中文:
引理 opensRange_ι
  结论: U.ι.opensRange = U
  证明: Opens.ext Subtype.range_val

@[simp]

Depends on / 依赖: Opens.ext, Subtype, Subtype.range_val, range_val
-/
lemma opensRange_ι : U.ι.opensRange = U :=
  Opens.ext Subtype.range_val

@[simp]
/--
lemma `range_ι` / 引理 `range_ι`

English:
lemma range_ι
  statement: Set.range U.ι = U
  proof: Subtype.range_val

中文:
引理 range_ι
  结论: 集合.range U.ι = U
  证明: Subtype.range_val

Depends on / 依赖: Subtype, Subtype.range_val, range_val
-/
lemma range_ι : Set.range U.ι = U :=
  Subtype.range_val

/--
lemma `ι_image_top` / 引理 `ι_image_top`

English:
lemma ι_image_top
  statement: U.ι ''ᵁ ⊤ = U
  proof: U.isOpenEmbedding_obj_top

中文:
引理 ι_image_top
  结论: U.ι ''ᵁ ⊤ = U
  证明: U.isOpenEmbedding_obj_top

Depends on / 依赖: U.isOpenEmbedding_obj_top, isOpenEmbedding_obj_top
-/
lemma ι_image_top : U.ι ''ᵁ ⊤ = U :=
  U.isOpenEmbedding_obj_top

/--
lemma `ι_image_le` / 引理 `ι_image_le`

English:
lemma ι_image_le
  given: (W : U.toScheme.Opens)
  statement: U.ι ''ᵁ W <= U
  proof: by
  simp_rw [← U.ι_image_top]
  exact U.ι.image_mono le_top

@[simp]

中文:
引理 ι_image_le
  条件: (W : U.toScheme.Opens)
  结论: U.ι ''ᵁ W <= U
  证明: by
  simp_rw [← U.ι_image_top]
  exact U.ι.image_mono le_top

@[simp]

Depends on / 依赖: image_mono, le_top, simp_rw
-/
lemma ι_image_le (W : U.toScheme.Opens) : U.ι ''ᵁ W <= U := by
  simp_rw [← U.ι_image_top]
  exact U.ι.image_mono le_top

@[simp]
/--
lemma `ι_preimage_self` / 引理 `ι_preimage_self`

English:
lemma ι_preimage_self
  statement: U.ι ⁻¹ᵁ U = ⊤
  proof: Opens.inclusion'_map_eq_top _

@[simp]

中文:
引理 ι_preimage_self
  结论: U.ι ⁻¹ᵁ U = ⊤
  证明: Opens.inclusion'_map_eq_top _

@[simp]

Depends on / 依赖: Opens.inclusion, _map_eq_top, inclusion
-/
lemma ι_preimage_self : U.ι ⁻¹ᵁ U = ⊤ :=
  Opens.inclusion'_map_eq_top _

@[simp]
/--
lemma `mem_ι_image_iff` / 引理 `mem_ι_image_iff`

English:
lemma mem_ι_image_iff
  given: {x : U} {V : Opens U}
  statement: (x : X) in U.ι ''ᵁ V ↔ x in V
  proof: U.ι.apply_mem_image_iff

中文:
引理 mem_ι_image_iff
  条件: {x : U} {V : Opens U}
  结论: (x : X) in U.ι ''ᵁ V ↔ x in V
  证明: U.ι.apply_mem_image_iff

Depends on / 依赖: apply_mem_image_iff
-/
lemma mem_ι_image_iff {x : U} {V : Opens U} : (x : X) in U.ι ''ᵁ V ↔ x in V :=
  U.ι.apply_mem_image_iff

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (U.ι.appLE U ⊤ U.ι_preimage_self.ge)
  body: by
  simp only [ι, ofRestrict_appLE]
  change IsIso (X.presheaf.map (eqToIso U.ι_image_top).hom.op)
  infer_instance

中文:
实例 :
  签名: 是同构 (U.ι.appLE U ⊤ U.ι_preimage_self.ge)
  定义体: by
  simp only [ι, ofRestrict_appLE]
  change IsIso (X.presheaf.map (eqToIso U.ι_image_top).hom.op)
  infer_instance

Depends on / 依赖: X.presheaf.map, eqToIso, hom.op, infer_instance, ofRestrict_appLE, presheaf
-/
instance : IsIso (U.ι.appLE U ⊤ U.ι_preimage_self.ge) := by
  simp only [ι, ofRestrict_appLE]
  change IsIso (X.presheaf.map (eqToIso U.ι_image_top).hom.op)
  infer_instance

/--
lemma `ι_app_self` / 引理 `ι_app_self`

English:
lemma ι_app_self
  statement: U.ι.app U = X.presheaf.map (eqToHom (X := U.ι ''ᵁ _) (by simp)).op
  proof: rfl

中文:
引理 ι_app_self
  结论: U.ι.app U = X.presheaf.map (eqToHom (X := U.ι ''ᵁ _) (by simp)).op
  证明: rfl
-/
lemma ι_app_self : U.ι.app U = X.presheaf.map (eqToHom (X := U.ι ''ᵁ _) (by simp)).op := rfl

/--
lemma `eq_presheaf_map_eqToHom` / 引理 `eq_presheaf_map_eqToHom`

English:
lemma eq_presheaf_map_eqToHom
  given: {V W : Opens U} (e : U.ι ''ᵁ V = U.ι ''ᵁ W)
  proof: rfl

@[simp]

中文:
引理 eq_presheaf_map_eqToHom
  条件: {V W : Opens U} (e : U.ι ''ᵁ V = U.ι ''ᵁ W)
  证明: rfl

@[simp]
-/
lemma eq_presheaf_map_eqToHom {V W : Opens U} (e : U.ι ''ᵁ V = U.ι ''ᵁ W) :
    X.presheaf.map (eqToHom e).op =
      U.toScheme.presheaf.map (eqToHom <| U.isOpenEmbedding.functor_obj_injective e).op := rfl

@[simp]
/--
lemma `nonempty_iff` / 引理 `nonempty_iff`

English:
lemma nonempty_iff
  statement: Nonempty U.toScheme ↔ (U : Set X).Nonempty
  proof: by
  simp only [toScheme_carrier, SetLike.coe_sort_coe, nonempty_subtype]
  rfl

中文:
引理 nonempty_iff
  结论: 非空 U.toScheme ↔ (U : 集合 X).非空
  证明: by
  simp only [toScheme_carrier, SetLike.coe_sort_coe, nonempty_subtype]
  rfl

Depends on / 依赖: SetLike, SetLike.coe_sort_coe, coe_sort_coe, nonempty_subtype, toScheme_carrier
-/
lemma nonempty_iff : Nonempty U.toScheme ↔ (U : Set X).Nonempty := by
  simp only [toScheme_carrier, SetLike.coe_sort_coe, nonempty_subtype]
  rfl

attribute [-simp] eqToHom_op in
/-- The global sections of the restriction is isomorphic to the sections on the open set. -/
@[simps!]
/--
Definition of `topIso` / `topIso` 的定义

English:
definition topIso
  signature: : Γ(U, ⊤) ≅ Γ(X, U)
  body: X.presheaf.mapIso (eqToIso U.ι_image_top.symm).op

中文:
定义 topIso
  签名: : Γ(U, ⊤) ≅ Γ(X, U)
  定义体: X.presheaf.mapIso (eqToIso U.ι_image_top.symm).op

Depends on / 依赖: X.presheaf.mapIso, _image_top.symm, eqToIso, mapIso, presheaf
-/
def topIso : Γ(U, ⊤) ≅ Γ(X, U) :=
  X.presheaf.mapIso (eqToIso U.ι_image_top.symm).op

/--
Definition of `stalkIso` / `stalkIso` 的定义

English:
definition stalkIso
  signature: {X : Scheme.{u}} (U : X.Opens) (x : U)
  body: X.restrictStalkIso (Opens.isOpenEmbedding _) _

@[reassoc (attr := simp)]

中文:
定义 stalkIso
  签名: {X : 概形.{u}} (U : X.Opens) (x : U)
  定义体: X.restrictStalkIso (Opens.isOpenEmbedding _) _

@[reassoc (attr := simp)]

Depends on / 依赖: Opens.isOpenEmbedding, X.restrictStalkIso, isOpenEmbedding, restrictStalkIso
-/
def stalkIso {X : Scheme.{u}} (U : X.Opens) (x : U) :
    U.toScheme.presheaf.stalk x ≅ X.presheaf.stalk x.1 :=
  X.restrictStalkIso (Opens.isOpenEmbedding _) _

@[reassoc (attr := simp)]
/--
lemma `germ_stalkIso_hom` / 引理 `germ_stalkIso_hom`

English:
lemma germ_stalkIso_hom
  statement: {X : Scheme.{u}} (U : X.Opens)
  proof: PresheafedSpace.restrictStalkIso_hom_eq_germ _ U.isOpenEmbedding _ _ _

@[reassoc]

中文:
引理 germ_stalkIso_hom
  结论: {X : 概形.{u}} (U : X.Opens)
  证明: PresheafedSpace.restrictStalkIso_hom_eq_germ _ U.isOpenEmbedding _ _ _

@[reassoc]

Depends on / 依赖: PresheafedSpace, PresheafedSpace.restrictStalkIso_hom_eq_germ, U.isOpenEmbedding, isOpenEmbedding, restrictStalkIso_hom_eq_germ
-/
lemma germ_stalkIso_hom {X : Scheme.{u}} (U : X.Opens)
    {V : U.toScheme.Opens} (x : U) (hx : x in V) :
      U.toScheme.presheaf.germ V x hx ≫ (U.stalkIso x).hom =
        X.presheaf.germ (U.ι ''ᵁ V) x.1 ⟨x, hx, rfl⟩ :=
    PresheafedSpace.restrictStalkIso_hom_eq_germ _ U.isOpenEmbedding _ _ _

@[reassoc]
/--
lemma `germ_stalkIso_inv` / 引理 `germ_stalkIso_inv`

English:
lemma germ_stalkIso_inv
  statement: {X : Scheme.{u}} (U : X.Opens) (V : U.toScheme.Opens) (x : U)
  proof: PresheafedSpace.restrictStalkIso_inv_eq_germ X.toPresheafedSpace U.isOpenEmbedding V x hx

中文:
引理 germ_stalkIso_inv
  结论: {X : 概形.{u}} (U : X.Opens) (V : U.toScheme.Opens) (x : U)
  证明: PresheafedSpace.restrictStalkIso_inv_eq_germ X.toPresheafedSpace U.isOpenEmbedding V x hx

Depends on / 依赖: PresheafedSpace, PresheafedSpace.restrictStalkIso_inv_eq_germ, U.isOpenEmbedding, X.toPresheafedSpace, isOpenEmbedding, restrictStalkIso_inv_eq_germ, toPresheafedSpace
-/
lemma germ_stalkIso_inv {X : Scheme.{u}} (U : X.Opens) (V : U.toScheme.Opens) (x : U)
    (hx : x in V) : X.presheaf.germ (U.ι ''ᵁ V) x ⟨x, hx, rfl⟩ ≫
      (U.stalkIso x).inv = U.toScheme.presheaf.germ V x hx :=
  PresheafedSpace.restrictStalkIso_inv_eq_germ X.toPresheafedSpace U.isOpenEmbedding V x hx

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `stalkIso_inv` / 引理 `stalkIso_inv`

English:
lemma stalkIso_inv
  given: {X : Scheme.{u}} (U : X.Opens) (x : U)
  proof: by
  rw [← Category.comp_id (U.stalkIso x).inv]; rw [Iso.inv_comp_eq]
  apply TopCat.Presheaf.stalk_hom_ext
  intro W hxW
  simp only [Category.comp_id, U.germ_stalkIso_hom_assoc]
  convert! (Scheme.Hom.germ_stalkMap U.ι (U.ι ''ᵁ W) x ⟨_, hxW, rfl⟩).symm
  refine (U.toScheme.presheaf.germ_res (homOf

中文:
引理 stalkIso_inv
  条件: {X : 概形.{u}} (U : X.Opens) (x : U)
  证明: by
  rw [← Category.comp_id (U.stalkIso x).inv]; rw [Iso.inv_comp_eq]
  apply TopCat.Presheaf.stalk_hom_ext
  intro W hxW
  simp only [Category.comp_id, U.germ_stalkIso_hom_assoc]
  convert! (Scheme.Hom.germ_stalkMap U.ι (U.ι ''ᵁ W) x ⟨_, hxW, rfl⟩).symm
  refine (U.toScheme.presheaf.germ_res (homOf

Depends on / 依赖: Category, Category.comp_id, Iso.inv_comp_eq, Presheaf, Scheme, Scheme.Hom.germ_stalkMap, Set.preimage_image_eq, Subtype, Subtype.val_injective, TopCat, TopCat.Presheaf.stalk_hom_ext, U.germ_stalkIso_hom_assoc, U.stalkIso, U.toScheme.presheaf.germ_res, comp_id, convert, germ_res, germ_stalkIso_hom_assoc, germ_stalkMap, homOfLE
-/
lemma stalkIso_inv {X : Scheme.{u}} (U : X.Opens) (x : U) :
    (U.stalkIso x).inv = U.ι.stalkMap x := by
  rw [← Category.comp_id (U.stalkIso x).inv]; rw [Iso.inv_comp_eq]
  apply TopCat.Presheaf.stalk_hom_ext
  intro W hxW
  simp only [Category.comp_id, U.germ_stalkIso_hom_assoc]
  convert! (Scheme.Hom.germ_stalkMap U.ι (U.ι ''ᵁ W) x ⟨_, hxW, rfl⟩).symm
  refine (U.toScheme.presheaf.germ_res (homOfLE ?_) _ _).symm
  exact (Set.preimage_image_eq _ Subtype.val_injective).le

end Scheme.Opens

/-- If `U` is a family of open sets that covers `X`, then `X.restrict U` forms an `X.open_cover`. -/
@[simps! I₀ X f]
/--
Definition of `Scheme.openCoverOfIsOpenCover` / `Scheme.openCoverOfIsOpenCover` 的定义

English:
definition Scheme.openCoverOfIsOpenCover
  signature: {s : Type*} (X : Scheme.{u}) (U : s -> X.Opens)
  body: s
  X i := U i
  f i := (U i).ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    have hx : x in ⨆ i, U i := hU.symm ▸ show x in (⊤ : X.Opens) by trivial
    rw [Opens.mem_iSup] at hx
    obtain ⟨i, hi⟩ := hx
    use i
    simpa

#adaptation_note

中文:
定义 概形.openCoverOfIsOpenCover
  签名: {s : 类型} (X : 概形.{u}) (U : s -> X.Opens)
  定义体: s
  X i := U i
  f i := (U i).ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    have hx : x in ⨆ i, U i := hU.symm ▸ show x in (⊤ : X.Opens) by trivial
    rw [Opens.mem_iSup] at hx
    obtain ⟨i, hi⟩ := hx
    use i
    simpa

#adaptation_note
-/
def Scheme.openCoverOfIsOpenCover {s : Type*} (X : Scheme.{u}) (U : s -> X.Opens)
    (hU : IsOpenCover U) : X.OpenCover where
  I₀ := s
  X i := U i
  f i := (U i).ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    have hx : x in ⨆ i, U i := hU.symm ▸ show x in (⊤ : X.Opens) by trivial
    rw [Opens.mem_iSup] at hx
    obtain ⟨i, hi⟩ := hx
    use i
    simpa

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The open sets of an open subscheme corresponds to the open sets containing in the subset. -/
@[simps!]
/--
Definition of `opensRestrict` / `opensRestrict` 的定义

English:
definition opensRestrict
  signature: :
  body: (IsOpenImmersion.opensEquiv (U.ι)).trans (Equiv.subtypeEquivProp (by simp))

中文:
定义 opensRestrict
  签名: :
  定义体: (IsOpenImmersion.opensEquiv (U.ι)).trans (Equiv.subtypeEquivProp (by simp))

Depends on / 依赖: Equiv.subtypeEquivProp, IsOpenImmersion, IsOpenImmersion.opensEquiv, opensEquiv, subtypeEquivProp
-/
def opensRestrict :
    Scheme.Opens U ≃ { V : X.Opens // V <= U } :=
  (IsOpenImmersion.opensEquiv (U.ι)).trans (Equiv.subtypeEquivProp (by simp))

/--
Instance `ΓRestrictAlgebra` / 实例 `ΓRestrictAlgebra`

English:
instance ΓRestrictAlgebra
  signature: {X : Scheme.{u}} (U : X.Opens)
  body: U.ι.appTop.hom.toAlgebra

中文:
实例 ΓRestrictAlgebra
  签名: {X : 概形.{u}} (U : X.Opens)
  定义体: U.ι.appTop.hom.toAlgebra

Depends on / 依赖: appTop, appTop.hom.toAlgebra, toAlgebra
-/
instance ΓRestrictAlgebra {X : Scheme.{u}} (U : X.Opens) :
    Algebra Γ(X, ⊤) Γ(U, ⊤) :=
  U.ι.appTop.hom.toAlgebra

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Scheme.Opens.ι_image_basicOpen'` / 引理 `Scheme.Opens.ι_image_basicOpen'`

English:
lemma Scheme.Opens.ι_image_basicOpen'
  given: (r : Γ(U, ⊤))
  proof: by
  refine (Scheme.image_basicOpen (X.ofRestrict U.isOpenEmbedding) r).trans ?_
  rw [← Scheme.basicOpen_res_eq _ _ (eqToHom U.isOpenEmbedding_obj_top).op]
  rw [← CommRingCat.comp_apply]; rw [← CategoryTheory.Functor.map_comp]; rw [← op_comp]; rw [eqToHom_trans]; rw [eqToHom_refl]; rw [op_id]
  co

中文:
引理 概形.Opens.ι_image_basicOpen'
  条件: (r : Γ(U, ⊤))
  证明: by
  refine (Scheme.image_basicOpen (X.ofRestrict U.isOpenEmbedding) r).trans ?_
  rw [← Scheme.basicOpen_res_eq _ _ (eqToHom U.isOpenEmbedding_obj_top).op]
  rw [← CommRingCat.comp_apply]; rw [← CategoryTheory.Functor.map_comp]; rw [← op_comp]; rw [eqToHom_trans]; rw [eqToHom_refl]; rw [op_id]
  co

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id, CommRingCat, CommRingCat.comp_apply, Functor, IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.ofRestrict_invApp, Scheme, Scheme.basicOpen_res_eq, Scheme.image_basicOpen, U.isOpenEmbedding, U.isOpenEmbedding_obj_top, X.ofRestrict, basicOpen_res_eq, comp_apply, eqToHom, eqToHom_refl, eqToHom_trans
-/
lemma Scheme.Opens.ι_image_basicOpen' (r : Γ(U, ⊤)) :
    U.ι ''ᵁ U.toScheme.basicOpen r = X.basicOpen
      (X.presheaf.map (eqToHom U.ι_image_top.symm).op r) := by
  refine (Scheme.image_basicOpen (X.ofRestrict U.isOpenEmbedding) r).trans ?_
  rw [← Scheme.basicOpen_res_eq _ _ (eqToHom U.isOpenEmbedding_obj_top).op]
  rw [← CommRingCat.comp_apply]; rw [← CategoryTheory.Functor.map_comp]; rw [← op_comp]; rw [eqToHom_trans]; rw [eqToHom_refl]; rw [op_id]
  congr
  exact (PresheafedSpace.IsOpenImmersion.ofRestrict_invApp _ _ _).trans
    (CategoryTheory.Functor.map_id _ _).symm

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Scheme.Opens.ι_image_basicOpen` / 引理 `Scheme.Opens.ι_image_basicOpen`

English:
lemma Scheme.Opens.ι_image_basicOpen
  given: (r : Γ(U, ⊤))
  proof: by
  rw [Scheme.Opens.ι_image_basicOpen']; rw [Scheme.basicOpen_res_eq]

中文:
引理 概形.Opens.ι_image_basicOpen
  条件: (r : Γ(U, ⊤))
  证明: by
  rw [Scheme.Opens.ι_image_basicOpen']; rw [Scheme.basicOpen_res_eq]

Depends on / 依赖: Scheme, Scheme.Opens, Scheme.basicOpen_res_eq, basicOpen_res_eq
-/
lemma Scheme.Opens.ι_image_basicOpen (r : Γ(U, ⊤)) :
    U.ι ''ᵁ U.toScheme.basicOpen r = X.basicOpen r := by
  rw [Scheme.Opens.ι_image_basicOpen']; rw [Scheme.basicOpen_res_eq]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Scheme.Opens.ι_image_basicOpen_topIso_inv` / 引理 `Scheme.Opens.ι_image_basicOpen_topIso_inv`

English:
lemma Scheme.Opens.ι_image_basicOpen_topIso_inv
  given: (r : Γ(X, U))
  proof: by
  simp only [Scheme.Opens.toScheme_presheaf_obj]
  rw [ι_image_basicOpen']; rw [basicOpen_res_eq]; rw [topIso_inv]; rw [basicOpen_res_eq X]

@[simp]

中文:
引理 概形.Opens.ι_image_basicOpen_topIso_inv
  条件: (r : Γ(X, U))
  证明: by
  simp only [Scheme.Opens.toScheme_presheaf_obj]
  rw [ι_image_basicOpen']; rw [basicOpen_res_eq]; rw [topIso_inv]; rw [basicOpen_res_eq X]

@[simp]

Depends on / 依赖: Scheme, Scheme.Opens.toScheme_presheaf_obj, basicOpen_res_eq, toScheme_presheaf_obj, topIso_inv
-/
lemma Scheme.Opens.ι_image_basicOpen_topIso_inv (r : Γ(X, U)) :
    U.ι ''ᵁ U.toScheme.basicOpen (U.topIso.inv r) = X.basicOpen r := by
  simp only [Scheme.Opens.toScheme_presheaf_obj]
  rw [ι_image_basicOpen']; rw [basicOpen_res_eq]; rw [topIso_inv]; rw [basicOpen_res_eq X]

@[simp]
/--
lemma `Scheme.Opens.mem_basicOpen_toScheme` / 引理 `Scheme.Opens.mem_basicOpen_toScheme`

English:
lemma Scheme.Opens.mem_basicOpen_toScheme
  given: {U : X.Opens} {V : Scheme.Opens U} {r : Γ(U, V)} {x : U}
  proof: by
  rw [← U.toScheme.basicOpen_res_eq _ (eqToHom (U.ι.preimage_image_eq V)).op]
  exact congr(x in $(U.ι.preimage_basicOpen r)).to_iff.symm

中文:
引理 概形.Opens.mem_basicOpen_toScheme
  条件: {U : X.Opens} {V : 概形.Opens U} {r : Γ(U, V)} {x : U}
  证明: by
  rw [← U.toScheme.basicOpen_res_eq _ (eqToHom (U.ι.preimage_image_eq V)).op]
  exact congr(x in $(U.ι.preimage_basicOpen r)).to_iff.symm

Depends on / 依赖: U.toScheme.basicOpen_res_eq, basicOpen_res_eq, eqToHom, preimage_basicOpen, preimage_image_eq, toScheme, to_iff, to_iff.symm
-/
lemma Scheme.Opens.mem_basicOpen_toScheme {U : X.Opens} {V : Scheme.Opens U} {r : Γ(U, V)} {x : U} :
    x in U.toScheme.basicOpen r ↔ (x : X) in X.basicOpen r := by
  rw [← U.toScheme.basicOpen_res_eq _ (eqToHom (U.ι.preimage_image_eq V)).op]
  exact congr(x in $(U.ι.preimage_basicOpen r)).to_iff.symm

/-- If `U ≤ V`, then `U` is also a subscheme of `V`. -/
protected noncomputable
/--
Definition of `Scheme.homOfLE` / `Scheme.homOfLE` 的定义

English:
definition Scheme.homOfLE
  signature: (X : Scheme.{u}) {U V : X.Opens} (e : U <= V)
  body: IsOpenImmersion.lift V.ι U.ι (by simpa using e)

@[reassoc (attr := simp)]

中文:
定义 概形.homOfLE
  签名: (X : 概形.{u}) {U V : X.Opens} (e : U <= V)
  定义体: IsOpenImmersion.lift V.ι U.ι (by simpa using e)

@[reassoc (attr := simp)]

Depends on / 依赖: IsOpenImmersion, IsOpenImmersion.lift
-/
def Scheme.homOfLE (X : Scheme.{u}) {U V : X.Opens} (e : U <= V) : (U : Scheme.{u}) ⟶ V :=
  IsOpenImmersion.lift V.ι U.ι (by simpa using e)

@[reassoc (attr := simp)]
/--
lemma `Scheme.homOfLE_ι` / 引理 `Scheme.homOfLE_ι`

English:
lemma Scheme.homOfLE_ι
  given: (X : Scheme.{u}) {U V : X.Opens} (e : U <= V)
  proof: IsOpenImmersion.lift_fac _ _ _

中文:
引理 概形.homOfLE_ι
  条件: (X : 概形.{u}) {U V : X.Opens} (e : U <= V)
  证明: IsOpenImmersion.lift_fac _ _ _

Depends on / 依赖: IsOpenImmersion, IsOpenImmersion.lift_fac, lift_fac
-/
lemma Scheme.homOfLE_ι (X : Scheme.{u}) {U V : X.Opens} (e : U <= V) :
    X.homOfLE e ≫ V.ι = U.ι :=
  IsOpenImmersion.lift_fac _ _ _

instance {U V : X.Opens} (h : U <= V) : (X.homOfLE h).IsOver X where

@[simp]
/--
lemma `Scheme.homOfLE_rfl` / 引理 `Scheme.homOfLE_rfl`

English:
lemma Scheme.homOfLE_rfl
  given: (X : Scheme.{u}) (U : X.Opens)
  statement: X.homOfLE (refl U) = 𝟙 _
  proof: by
  rw [← cancel_mono U.ι]; rw [Scheme.homOfLE_ι]; rw [Category.id_comp]

@[reassoc (attr := simp)]

中文:
引理 概形.homOfLE_rfl
  条件: (X : 概形.{u}) (U : X.Opens)
  结论: X.homOfLE (refl U) = 𝟙 _
  证明: by
  rw [← cancel_mono U.ι]; rw [Scheme.homOfLE_ι]; rw [Category.id_comp]

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.id_comp, Scheme, Scheme.homOfLE_, cancel_mono, id_comp
-/
lemma Scheme.homOfLE_rfl (X : Scheme.{u}) (U : X.Opens) : X.homOfLE (refl U) = 𝟙 _ := by
  rw [← cancel_mono U.ι]; rw [Scheme.homOfLE_ι]; rw [Category.id_comp]

@[reassoc (attr := simp)]
/--
lemma `Scheme.homOfLE_homOfLE` / 引理 `Scheme.homOfLE_homOfLE`

English:
lemma Scheme.homOfLE_homOfLE
  given: (X : Scheme.{u}) {U V W : X.Opens} (e₁ : U <= V) (e₂ : V <= W)
  proof: by
  rw [← cancel_mono W.ι]; rw [Category.assoc]; rw [Scheme.homOfLE_ι]; rw [Scheme.homOfLE_ι]; rw [Scheme.homOfLE_ι]

中文:
引理 概形.homOfLE_homOfLE
  条件: (X : 概形.{u}) {U V W : X.Opens} (e₁ : U <= V) (e₂ : V <= W)
  证明: by
  rw [← cancel_mono W.ι]; rw [Category.assoc]; rw [Scheme.homOfLE_ι]; rw [Scheme.homOfLE_ι]; rw [Scheme.homOfLE_ι]

Depends on / 依赖: Category, Category.assoc, Scheme, Scheme.homOfLE_, cancel_mono
-/
lemma Scheme.homOfLE_homOfLE (X : Scheme.{u}) {U V W : X.Opens} (e₁ : U <= V) (e₂ : V <= W) :
    X.homOfLE e₁ ≫ X.homOfLE e₂ = X.homOfLE (e₁.trans e₂) := by
  rw [← cancel_mono W.ι]; rw [Category.assoc]; rw [Scheme.homOfLE_ι]; rw [Scheme.homOfLE_ι]; rw [Scheme.homOfLE_ι]

/--
theorem `Scheme.homOfLE_base` / 定理 `Scheme.homOfLE_base`

English:
theorem Scheme.homOfLE_base
  given: {U V : X.Opens} (e : U <= V)
  proof: by
  ext a; refine Subtype.ext ?_ -- Porting note: `ext` did not pick up `Subtype.ext`
  exact congr($(X.homOfLE_ι e) a)

中文:
定理 概形.homOfLE_base
  条件: {U V : X.Opens} (e : U <= V)
  证明: by
  ext a; refine Subtype.ext ?_ -- Porting note: `ext` did not pick up `Subtype.ext`
  exact congr($(X.homOfLE_ι e) a)

Depends on / 依赖: Porting, Subtype, Subtype.ext, X.homOfLE_
-/
theorem Scheme.homOfLE_base {U V : X.Opens} (e : U <= V) :
    (X.homOfLE e).base = (Opens.toTopCat _).map (homOfLE e) := by
  ext a; refine Subtype.ext ?_ -- Porting note: `ext` did not pick up `Subtype.ext`
  exact congr($(X.homOfLE_ι e) a)

/--
theorem `Scheme.homOfLE_apply'` / 定理 `Scheme.homOfLE_apply'`

English:
theorem Scheme.homOfLE_apply'
  given: {U V : X.Opens} (e : U <= V) (x : X) (hx : x in U)
  proof: by
  rw [homOfLE_base]
  rfl

@[simp]

中文:
定理 概形.homOfLE_apply'
  条件: {U V : X.Opens} (e : U <= V) (x : X) (hx : x in U)
  证明: by
  rw [homOfLE_base]
  rfl

@[simp]

Depends on / 依赖: homOfLE_base
-/
theorem Scheme.homOfLE_apply' {U V : X.Opens} (e : U <= V) (x : X) (hx : x in U) :
    X.homOfLE e ⟨x, hx⟩ = ⟨x, e hx⟩ := by
  rw [homOfLE_base]
  rfl

@[simp]
/--
theorem `Scheme.homOfLE_apply` / 定理 `Scheme.homOfLE_apply`

English:
theorem Scheme.homOfLE_apply
  given: {U V : X.Opens} (e : U <= V) (x : U)
  proof: by
  rw [Scheme.homOfLE_apply']

中文:
定理 概形.homOfLE_apply
  条件: {U V : X.Opens} (e : U <= V) (x : U)
  证明: by
  rw [Scheme.homOfLE_apply']

Depends on / 依赖: Scheme, Scheme.homOfLE_apply, homOfLE_apply
-/
theorem Scheme.homOfLE_apply {U V : X.Opens} (e : U <= V) (x : U) :
    (X.homOfLE e x).1 = x := by
  rw [Scheme.homOfLE_apply']

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `Scheme.ι_image_homOfLE_eq_ι_image_inf` / 定理 `Scheme.ι_image_homOfLE_eq_ι_image_inf`

English:
theorem Scheme.ι_image_homOfLE_eq_ι_image_inf
  given: {U V : X.Opens} (e : U <= V) (W : Opens V)
  proof: by
  ext x
  constructor
  · rintro ⟨⟨y, hyU⟩, hyW, rfl⟩
    exact ⟨⟨⟨y, e hyU⟩, by simpa [homOfLE_apply'] using hyW, rfl⟩, hyU⟩
  · rintro ⟨⟨y, hyW, rfl⟩, hyU⟩
    exact ⟨⟨y.1, hyU⟩, by simpa [homOfLE_apply'] using hyW, rfl⟩

中文:
定理 概形.ι_image_homOfLE_eq_ι_image_inf
  条件: {U V : X.Opens} (e : U <= V) (W : Opens V)
  证明: by
  ext x
  constructor
  · rintro ⟨⟨y, hyU⟩, hyW, rfl⟩
    exact ⟨⟨⟨y, e hyU⟩, by simpa [homOfLE_apply'] using hyW, rfl⟩, hyU⟩
  · rintro ⟨⟨y, hyW, rfl⟩, hyU⟩
    exact ⟨⟨y.1, hyU⟩, by simpa [homOfLE_apply'] using hyW, rfl⟩

Depends on / 依赖: homOfLE_apply
-/
theorem Scheme.ι_image_homOfLE_eq_ι_image_inf {U V : X.Opens} (e : U <= V) (W : Opens V) :
    U.ι ''ᵁ X.homOfLE e ⁻¹ᵁ W = V.ι ''ᵁ W ⊓ U := by
  ext x
  constructor
  · rintro ⟨⟨y, hyU⟩, hyW, rfl⟩
    exact ⟨⟨⟨y, e hyU⟩, by simpa [homOfLE_apply'] using hyW, rfl⟩, hyU⟩
  · rintro ⟨⟨y, hyW, rfl⟩, hyU⟩
    exact ⟨⟨y.1, hyU⟩, by simpa [homOfLE_apply'] using hyW, rfl⟩

/--
theorem `Scheme.ι_image_homOfLE_le_ι_image` / 定理 `Scheme.ι_image_homOfLE_le_ι_image`

English:
theorem Scheme.ι_image_homOfLE_le_ι_image
  given: {U V : X.Opens} (e : U <= V) (W : Opens V)
  proof: by
  simp [Scheme.ι_image_homOfLE_eq_ι_image_inf]

中文:
定理 概形.ι_image_homOfLE_le_ι_image
  条件: {U V : X.Opens} (e : U <= V) (W : Opens V)
  证明: by
  simp [Scheme.ι_image_homOfLE_eq_ι_image_inf]

Depends on / 依赖: Scheme
-/
theorem Scheme.ι_image_homOfLE_le_ι_image {U V : X.Opens} (e : U <= V) (W : Opens V) :
    U.ι ''ᵁ X.homOfLE e ⁻¹ᵁ W <= V.ι ''ᵁ W := by
  simp [Scheme.ι_image_homOfLE_eq_ι_image_inf]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `Scheme.homOfLE_app` / 定理 `Scheme.homOfLE_app`

English:
theorem Scheme.homOfLE_app
  given: {U V : X.Opens} (e : U <= V) (W : Opens V)
  proof: by
  have e₁ := Scheme.Hom.congr_app (X.homOfLE_ι e) (V.ι ''ᵁ W)
  have : V.ι ⁻¹ᵁ V.ι ''ᵁ W = W := W.map_functor_eq (U := V)
  have e₂ := (X.homOfLE e).naturality (eqToIso this).hom.op
  have e₃ := e₂.symm.trans e₁
  dsimp at e₃ ⊢
  rw [← IsIso.eq_comp_inv]; rw [← Functor.map_inv]; rw [← Functor.map

中文:
定理 概形.homOfLE_app
  条件: {U V : X.Opens} (e : U <= V) (W : Opens V)
  证明: by
  have e₁ := Scheme.Hom.congr_app (X.homOfLE_ι e) (V.ι ''ᵁ W)
  have : V.ι ⁻¹ᵁ V.ι ''ᵁ W = W := W.map_functor_eq (U := V)
  have e₂ := (X.homOfLE e).naturality (eqToIso this).hom.op
  have e₃ := e₂.symm.trans e₁
  dsimp at e₃ ⊢
  rw [← IsIso.eq_comp_inv]; rw [← Functor.map_inv]; rw [← Functor.map

Depends on / 依赖: Functor, Functor.map_comp, Functor.map_inv, IsIso.eq_comp_inv, Scheme, Scheme.Hom.congr_app, W.map_functor_eq, X.homOfLE, X.homOfLE_, congr_app, eqToIso, eq_comp_inv, hom.op, homOfLE, map_comp, map_functor_eq, map_inv, naturality, symm.trans
-/
theorem Scheme.homOfLE_app {U V : X.Opens} (e : U <= V) (W : Opens V) :
    (X.homOfLE e).app W = X.presheaf.map (homOfLE <| X.ι_image_homOfLE_le_ι_image e W).op := by
  have e₁ := Scheme.Hom.congr_app (X.homOfLE_ι e) (V.ι ''ᵁ W)
  have : V.ι ⁻¹ᵁ V.ι ''ᵁ W = W := W.map_functor_eq (U := V)
  have e₂ := (X.homOfLE e).naturality (eqToIso this).hom.op
  have e₃ := e₂.symm.trans e₁
  dsimp at e₃ ⊢
  rw [← IsIso.eq_comp_inv]; rw [← Functor.map_inv]; rw [← Functor.map_comp] at e₃
  rw [e₃]; rw [← Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `Scheme.homOfLE_appLE` / 定理 `Scheme.homOfLE_appLE`

English:
theorem Scheme.homOfLE_appLE
  given: {U V : X.Opens} (e : U <= V) (W : Opens V) (W' : Opens U) (e')
  proof: by
  simp [Scheme.Hom.appLE, Scheme.homOfLE_app, ← Functor.map_comp, ← op_comp]

中文:
定理 概形.homOfLE_appLE
  条件: {U V : X.Opens} (e : U <= V) (W : Opens V) (W' : Opens U) (e')
  证明: by
  simp [Scheme.Hom.appLE, Scheme.homOfLE_app, ← Functor.map_comp, ← op_comp]

Depends on / 依赖: Functor, Functor.map_comp, Scheme, Scheme.Hom.appLE, Scheme.homOfLE_app, homOfLE_app, map_comp, op_comp
-/
theorem Scheme.homOfLE_appLE {U V : X.Opens} (e : U <= V) (W : Opens V) (W' : Opens U) (e') :
    (X.homOfLE e).appLE W W' e' = X.presheaf.map
      (homOfLE ((U.ι.image_mono e').trans (Scheme.ι_image_homOfLE_le_ι_image ..))).op := by
  simp [Scheme.Hom.appLE, Scheme.homOfLE_app, ← Functor.map_comp, ← op_comp]

/--
theorem `Scheme.homOfLE_appTop` / 定理 `Scheme.homOfLE_appTop`

English:
theorem Scheme.homOfLE_appTop
  given: {U V : X.Opens} (e : U <= V)
  proof: homOfLE_app ..

中文:
定理 概形.homOfLE_appTop
  条件: {U V : X.Opens} (e : U <= V)
  证明: homOfLE_app ..

Depends on / 依赖: homOfLE_app
-/
theorem Scheme.homOfLE_appTop {U V : X.Opens} (e : U <= V) :
    (X.homOfLE e).appTop = X.presheaf.map (homOfLE <| X.ι_image_homOfLE_le_ι_image e ⊤).op :=
  homOfLE_app ..

instance (X : Scheme.{u}) {U V : X.Opens} (e : U <= V) : IsOpenImmersion (X.homOfLE e) := by
  delta Scheme.homOfLE
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Scheme.Hom.appIso_homOfLE_inv` / 引理 `Scheme.Hom.appIso_homOfLE_inv`

English:
lemma Scheme.Hom.appIso_homOfLE_inv
  statement: {X : Scheme.{u}} {U V : X.Opens} (h : U <= V)
  proof: by
  rw [eq_comm]; rw [← Iso.hom_comp_eq_id]
  dsimp
  simp only [appIso_hom, homOfLE_app, homOfLE_leOfHom, eqToHom_op, Opens.toScheme_presheaf_map,
    eqToHom_unop, ← X.presheaf.map_comp, Category.assoc, ← X.presheaf.map_id]
  rfl

@[simp]

中文:
引理 概形.态射.appIso_homOfLE_inv
  结论: {X : 概形.{u}} {U V : X.Opens} (h : U <= V)
  证明: by
  rw [eq_comm]; rw [← Iso.hom_comp_eq_id]
  dsimp
  simp only [appIso_hom, homOfLE_app, homOfLE_leOfHom, eqToHom_op, Opens.toScheme_presheaf_map,
    eqToHom_unop, ← X.presheaf.map_comp, Category.assoc, ← X.presheaf.map_id]
  rfl

@[simp]

Depends on / 依赖: Category, Category.assoc, Iso.hom_comp_eq_id, Opens.toScheme_presheaf_map, X.presheaf.map_comp, X.presheaf.map_id, appIso_hom, eqToHom_op, eqToHom_unop, eq_comm, homOfLE_app, homOfLE_leOfHom, hom_comp_eq_id, map_comp, map_id, presheaf, toScheme_presheaf_map
-/
lemma Scheme.Hom.appIso_homOfLE_inv {X : Scheme.{u}} {U V : X.Opens} (h : U <= V)
    (W : (U : Scheme.{u}).Opens) :
    ((X.homOfLE h).appIso W).inv =
      X.presheaf.map (.op <| homOfLE <| by
        suffices V.ι ''ᵁ _ <= U.ι ''ᵁ W by simpa
        simp [← Scheme.Hom.comp_image]) := by
  rw [eq_comm]; rw [← Iso.hom_comp_eq_id]
  dsimp
  simp only [appIso_hom, homOfLE_app, homOfLE_leOfHom, eqToHom_op, Opens.toScheme_presheaf_map,
    eqToHom_unop, ← X.presheaf.map_comp, Category.assoc, ← X.presheaf.map_id]
  rfl

@[simp]
/--
lemma `Scheme.opensRange_homOfLE` / 引理 `Scheme.opensRange_homOfLE`

English:
lemma Scheme.opensRange_homOfLE
  given: {U V : X.Opens} (e : U <= V)
  proof: V.ι.image_injective (by simp [← Hom.opensRange_comp, Hom.image_preimage_eq_opensRange_inf, e])

中文:
引理 概形.opensRange_homOfLE
  条件: {U V : X.Opens} (e : U <= V)
  证明: V.ι.image_injective (by simp [← Hom.opensRange_comp, Hom.image_preimage_eq_opensRange_inf, e])

Depends on / 依赖: Hom.image_preimage_eq_opensRange_inf, Hom.opensRange_comp, image_injective, image_preimage_eq_opensRange_inf, opensRange_comp
-/
lemma Scheme.opensRange_homOfLE {U V : X.Opens} (e : U <= V) :
    (X.homOfLE e).opensRange = V.ι ⁻¹ᵁ U :=
  V.ι.image_injective (by simp [← Hom.opensRange_comp, Hom.image_preimage_eq_opensRange_inf, e])

/--
Definition of `Scheme.Opens.iSupOpenCover` / `Scheme.Opens.iSupOpenCover` 的定义

English:
definition Scheme.Opens.iSupOpenCover
  signature: {J : Type*} {X : Scheme} (U : J -> X.Opens)
  body: J
  X i := U i
  f j := X.homOfLE (le_iSup _ _)
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp x.2
    use i, ⟨x.1, hi⟩
    apply Subtype.ext
    simp

中文:
定义 概形.Opens.iSupOpenCover
  签名: {J : 类型} {X : 概形} (U : J -> X.Opens)
  定义体: J
  X i := U i
  f j := X.homOfLE (le_iSup _ _)
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp x.2
    use i, ⟨x.1, hi⟩
    apply Subtype.ext
    simp
-/
def Scheme.Opens.iSupOpenCover {J : Type*} {X : Scheme} (U : J -> X.Opens) :
    (⨆ i, U i).toScheme.OpenCover where
  I₀ := J
  X i := U i
  f j := X.homOfLE (le_iSup _ _)
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp x.2
    use i, ⟨x.1, hi⟩
    apply Subtype.ext
    simp

set_option backward.defeqAttrib.useBackward true in
variable (X) in
/-- The functor taking open subsets of `X` to open subschemes of `X`. -/
@[simps! obj_left obj_hom map_left]
/--
Definition of `Scheme.restrictFunctor` / `Scheme.restrictFunctor` 的定义

English:
definition Scheme.restrictFunctor
  signature: : X.Opens ⥤ Over X where
  body: Over.mk U.ι
  map {U V} i := Over.homMk (X.homOfLE i.le) (by simp)
  map_id U := by
    ext1
    exact Scheme.homOfLE_rfl _ _
  map_comp {U V W} i j := by
    ext1
    exact (X.homOfLE_homOfLE i.le j.le).symm

中文:
定义 概形.restrictFunctor
  签名: : X.Opens ⥤ Over X where
  定义体: Over.mk U.ι
  map {U V} i := Over.homMk (X.homOfLE i.le) (by simp)
  map_id U := by
    ext1
    exact Scheme.homOfLE_rfl _ _
  map_comp {U V W} i j := by
    ext1
    exact (X.homOfLE_homOfLE i.le j.le).symm

Depends on / 依赖: Over.mk
-/
def Scheme.restrictFunctor : X.Opens ⥤ Over X where
  obj U := Over.mk U.ι
  map {U V} i := Over.homMk (X.homOfLE i.le) (by simp)
  map_id U := by
    ext1
    exact Scheme.homOfLE_rfl _ _
  map_comp {U V W} i j := by
    ext1
    exact (X.homOfLE_homOfLE i.le j.le).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The functor that restricts to open subschemes and then takes global section is
isomorphic to the structure sheaf. -/
@[simps!]
/--
Definition of `Scheme.restrictFunctorΓ` / `Scheme.restrictFunctorΓ` 的定义

English:
definition Scheme.restrictFunctorΓ
  signature: : X.restrictFunctor.op ⋙ (Over.forget X).op ⋙ Scheme.Γ ≅ X.presheaf
  body: NatIso.ofComponents
    (fun U => X.presheaf.mapIso ((eqToIso (unop U).isOpenEmbedding_obj_top).symm.op :))
    (by
      intro U V i
      dsimp
      rw [X.homOfLE_appTop]; rw [← Functor.map_comp]; rw [← Functor.map_comp]
      congr 1)

中文:
定义 概形.restrictFunctorΓ
  签名: : X.restrictFunctor.op ⋙ (Over.forget X).op ⋙ 概形.Γ ≅ X.presheaf
  定义体: NatIso.ofComponents
    (fun U => X.presheaf.mapIso ((eqToIso (unop U).isOpenEmbedding_obj_top).symm.op :))
    (by
      intro U V i
      dsimp
      rw [X.homOfLE_appTop]; rw [← Functor.map_comp]; rw [← Functor.map_comp]
      congr 1)

Depends on / 依赖: Functor, Functor.map_comp, NatIso, NatIso.ofComponents, X.homOfLE_appTop, X.presheaf.mapIso, eqToIso, homOfLE_appTop, isOpenEmbedding_obj_top, mapIso, map_comp, ofComponents, presheaf, symm.op
-/
def Scheme.restrictFunctorΓ : X.restrictFunctor.op ⋙ (Over.forget X).op ⋙ Scheme.Γ ≅ X.presheaf :=
  NatIso.ofComponents
    (fun U => X.presheaf.mapIso ((eqToIso (unop U).isOpenEmbedding_obj_top).symm.op :))
    (by
      intro U V i
      dsimp
      rw [X.homOfLE_appTop]; rw [← Functor.map_comp]; rw [← Functor.map_comp]
      congr 1)

/-- `X ∣_ U ∣_ V` is isomorphic to `X ∣_ V ∣_ U` -/
noncomputable
/--
Definition of `Scheme.restrictRestrictComm` / `Scheme.restrictRestrictComm` 的定义

English:
definition Scheme.restrictRestrictComm
  signature: (X : Scheme.{u}) (U V : X.Opens)
  body: IsOpenImmersion.isoOfRangeEq (Opens.ι _ ≫ U.ι) (Opens.ι _ ≫ V.ι) by
    simp only [Hom.comp_base, TopCat.coe_comp, Set.range_comp, Opens.range_ι, Opens.map_coe,
      Set.image_preimage_eq_inter_range, Set.inter_comm (U : Set X)]

中文:
定义 概形.restrictRestrictComm
  签名: (X : 概形.{u}) (U V : X.Opens)
  定义体: IsOpenImmersion.isoOfRangeEq (Opens.ι _ ≫ U.ι) (Opens.ι _ ≫ V.ι) by
    simp only [Hom.comp_base, TopCat.coe_comp, Set.range_comp, Opens.range_ι, Opens.map_coe,
      Set.image_preimage_eq_inter_range, Set.inter_comm (U : Set X)]

Depends on / 依赖: Hom.comp_base, IsOpenImmersion, IsOpenImmersion.isoOfRangeEq, Opens.map_coe, Opens.range_, Set.image_preimage_eq_inter_range, Set.inter_comm, Set.range_comp, TopCat, TopCat.coe_comp, coe_comp, comp_base, image_preimage_eq_inter_range, inter_comm, isoOfRangeEq, map_coe, range_comp
-/
def Scheme.restrictRestrictComm (X : Scheme.{u}) (U V : X.Opens) :
    (U.ι ⁻¹ᵁ V).toScheme ≅ V.ι ⁻¹ᵁ U :=
IsOpenImmersion.isoOfRangeEq (Opens.ι _ ≫ U.ι) (Opens.ι _ ≫ V.ι) by
    simp only [Hom.comp_base, TopCat.coe_comp, Set.range_comp, Opens.range_ι, Opens.map_coe,
      Set.image_preimage_eq_inter_range, Set.inter_comm (U : Set X)]

/-- If `f : X ⟶ Y` is an open immersion, then for any `U : X.Opens`,
we have the isomorphism `U ≅ f ''ᵁ U`. -/
noncomputable
/--
Definition of `Scheme.Hom.isoImage` / `Scheme.Hom.isoImage` 的定义

English:
definition Scheme.Hom.isoImage
  body: IsOpenImmersion.isoOfRangeEq (Opens.ι _ ≫ f) (Opens.ι _) (by simp [Set.range_comp])

@[reassoc (attr := simp)]

中文:
定义 概形.态射.isoImage
  定义体: IsOpenImmersion.isoOfRangeEq (Opens.ι _ ≫ f) (Opens.ι _) (by simp [Set.range_comp])

@[reassoc (attr := simp)]

Depends on / 依赖: IsOpenImmersion, IsOpenImmersion.isoOfRangeEq, Set.range_comp, isoOfRangeEq, range_comp
-/
def Scheme.Hom.isoImage
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : X.Opens) :
    U.toScheme ≅ f ''ᵁ U :=
  IsOpenImmersion.isoOfRangeEq (Opens.ι _ ≫ f) (Opens.ι _) (by simp [Set.range_comp])

@[reassoc (attr := simp)]
/--
lemma `Scheme.Hom.isoImage_hom_ι` / 引理 `Scheme.Hom.isoImage_hom_ι`

English:
lemma Scheme.Hom.isoImage_hom_ι
  proof: IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)]

中文:
引理 概形.态射.isoImage_hom_ι
  证明: IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: IsOpenImmersion, IsOpenImmersion.isoOfRangeEq_hom_fac, isoOfRangeEq_hom_fac
-/
lemma Scheme.Hom.isoImage_hom_ι
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : X.Opens) :
    (f.isoImage U).hom ≫ (f ''ᵁ U).ι = U.ι ≫ f :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)]
/--
lemma `Scheme.Hom.isoImage_inv_ι` / 引理 `Scheme.Hom.isoImage_inv_ι`

English:
lemma Scheme.Hom.isoImage_inv_ι
  proof: IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

@[reassoc]

中文:
引理 概形.态射.isoImage_inv_ι
  证明: IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

@[reassoc]

Depends on / 依赖: IsOpenImmersion, IsOpenImmersion.isoOfRangeEq_inv_fac, isoOfRangeEq_inv_fac
-/
lemma Scheme.Hom.isoImage_inv_ι
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : X.Opens) :
    (f.isoImage U).inv ≫ U.ι ≫ f = (f ''ᵁ U).ι :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

@[reassoc]
/--
lemma `Scheme.Hom.isoImage_hom_homOfLE` / 引理 `Scheme.Hom.isoImage_hom_homOfLE`

English:
lemma Scheme.Hom.isoImage_hom_homOfLE
  proof: by
  simp [← cancel_mono (f ''ᵁ V).ι]

@[reassoc]

中文:
引理 概形.态射.isoImage_hom_homOfLE
  证明: by
  simp [← cancel_mono (f ''ᵁ V).ι]

@[reassoc]

Depends on / 依赖: cancel_mono
-/
lemma Scheme.Hom.isoImage_hom_homOfLE
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U V : Opens X) (e : U <= V) :
    (f.isoImage U).hom ≫ Y.homOfLE (f.image_mono e) = X.homOfLE e ≫ (f.isoImage V).hom := by
  simp [← cancel_mono (f ''ᵁ V).ι]

@[reassoc]
/--
lemma `Scheme.Hom.isoImage_inv_homOfLE` / 引理 `Scheme.Hom.isoImage_inv_homOfLE`

English:
lemma Scheme.Hom.isoImage_inv_homOfLE
  proof: by
  simp [← cancel_mono (f.isoImage V).hom, ← f.isoImage_hom_homOfLE]

@[reassoc (attr := simp)]

中文:
引理 概形.态射.isoImage_inv_homOfLE
  证明: by
  simp [← cancel_mono (f.isoImage V).hom, ← f.isoImage_hom_homOfLE]

@[reassoc (attr := simp)]

Depends on / 依赖: cancel_mono, f.isoImage, f.isoImage_hom_homOfLE, isoImage, isoImage_hom_homOfLE
-/
lemma Scheme.Hom.isoImage_inv_homOfLE
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U V : Opens X) (e : U <= V) :
    (f.isoImage U).inv ≫ X.homOfLE e = Y.homOfLE (f.image_mono e) ≫ (f.isoImage V).inv := by
  simp [← cancel_mono (f.isoImage V).hom, ← f.isoImage_hom_homOfLE]

@[reassoc (attr := simp)]
/--
lemma `Scheme.Opens.isoImage_ι_inv_ι` / 引理 `Scheme.Opens.isoImage_ι_inv_ι`

English:
lemma Scheme.Opens.isoImage_ι_inv_ι
  given: {X : Scheme.{u}} (U : Opens X) (V : Opens U)
  proof: by
  simp [← cancel_mono U.ι]

中文:
引理 概形.Opens.isoImage_ι_inv_ι
  条件: {X : 概形.{u}} (U : Opens X) (V : Opens U)
  证明: by
  simp [← cancel_mono U.ι]

Depends on / 依赖: cancel_mono
-/
lemma Scheme.Opens.isoImage_ι_inv_ι {X : Scheme.{u}} (U : Opens X) (V : Opens U) :
    (U.ι.isoImage V).inv ≫ V.ι = X.homOfLE (U.ι_image_le V) := by
  simp [← cancel_mono U.ι]

/--
Definition of `Scheme.Hom.isoOpensRange` / `Scheme.Hom.isoOpensRange` 的定义

English:
definition Scheme.Hom.isoOpensRange
  signature: {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
  body: IsOpenImmersion.isoOfRangeEq f f.opensRange.ι (by simp)

@[reassoc (attr := simp)]

中文:
定义 概形.态射.isoOpensRange
  签名: {X Y : 概形.{u}} (f : X ⟶ Y) [是开浸入 f]
  定义体: IsOpenImmersion.isoOfRangeEq f f.opensRange.ι (by simp)

@[reassoc (attr := simp)]

Depends on / 依赖: IsOpenImmersion, IsOpenImmersion.isoOfRangeEq, f.opensRange, isoOfRangeEq, opensRange
-/
def Scheme.Hom.isoOpensRange {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    X ≅ f.opensRange :=
  IsOpenImmersion.isoOfRangeEq f f.opensRange.ι (by simp)

@[reassoc (attr := simp)]
/--
lemma `Scheme.Hom.isoOpensRange_hom_ι` / 引理 `Scheme.Hom.isoOpensRange_hom_ι`

English:
lemma Scheme.Hom.isoOpensRange_hom_ι
  given: {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
  proof: by
  simp [isoOpensRange]

@[reassoc (attr := simp)]

中文:
引理 概形.态射.isoOpensRange_hom_ι
  条件: {X Y : 概形.{u}} (f : X ⟶ Y) [是开浸入 f]
  证明: by
  simp [isoOpensRange]

@[reassoc (attr := simp)]

Depends on / 依赖: isoOpensRange
-/
lemma Scheme.Hom.isoOpensRange_hom_ι {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    f.isoOpensRange.hom ≫ f.opensRange.ι = f := by
  simp [isoOpensRange]

@[reassoc (attr := simp)]
/--
lemma `Scheme.Hom.isoOpensRange_inv_comp` / 引理 `Scheme.Hom.isoOpensRange_inv_comp`

English:
lemma Scheme.Hom.isoOpensRange_inv_comp
  given: {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
  proof: by
  simp [isoOpensRange]

中文:
引理 概形.态射.isoOpensRange_inv_comp
  条件: {X Y : 概形.{u}} (f : X ⟶ Y) [是开浸入 f]
  证明: by
  simp [isoOpensRange]

Depends on / 依赖: isoOpensRange
-/
lemma Scheme.Hom.isoOpensRange_inv_comp {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    f.isoOpensRange.inv ≫ f = f.opensRange.ι := by
  simp [isoOpensRange]

/-- `(⊤ : X.Opens)` as a scheme is isomorphic to `X`. -/
@[simps hom]
/--
Definition of `Scheme.topIso` / `Scheme.topIso` 的定义

English:
definition Scheme.topIso
  signature: (X : Scheme)
  body: Scheme.Opens.ι _
  inv := ⟨X.restrictTopIso.inv⟩
  hom_inv_id := Hom.ext' X.restrictTopIso.hom_inv_id
  inv_hom_id := Hom.ext' X.restrictTopIso.inv_hom_id

@[reassoc (attr := simp)]

中文:
定义 概形.topIso
  签名: (X : 概形)
  定义体: Scheme.Opens.ι _
  inv := ⟨X.restrictTopIso.inv⟩
  hom_inv_id := Hom.ext' X.restrictTopIso.hom_inv_id
  inv_hom_id := Hom.ext' X.restrictTopIso.inv_hom_id

@[reassoc (attr := simp)]

Depends on / 依赖: Scheme, Scheme.Opens
-/
def Scheme.topIso (X : Scheme) : ↑(⊤ : X.Opens) ≅ X where
  hom := Scheme.Opens.ι _
  inv := ⟨X.restrictTopIso.inv⟩
  hom_inv_id := Hom.ext' X.restrictTopIso.hom_inv_id
  inv_hom_id := Hom.ext' X.restrictTopIso.inv_hom_id

@[reassoc (attr := simp)]
/--
lemma `Scheme.toIso_inv_ι` / 引理 `Scheme.toIso_inv_ι`

English:
lemma Scheme.toIso_inv_ι
  given: (X : Scheme.{u})
  statement: X.topIso.inv ≫ Opens.ι _ = 𝟙 _
  proof: X.topIso.inv_hom_id

@[reassoc (attr := simp)]

中文:
引理 概形.toIso_inv_ι
  条件: (X : 概形.{u})
  结论: X.topIso.inv ≫ Opens.ι _ = 𝟙 _
  证明: X.topIso.inv_hom_id

@[reassoc (attr := simp)]

Depends on / 依赖: X.topIso.inv_hom_id, inv_hom_id, topIso
-/
lemma Scheme.toIso_inv_ι (X : Scheme.{u}) : X.topIso.inv ≫ Opens.ι _ = 𝟙 _ :=
  X.topIso.inv_hom_id

@[reassoc (attr := simp)]
/--
lemma `Scheme.ι_toIso_inv` / 引理 `Scheme.ι_toIso_inv`

English:
lemma Scheme.ι_toIso_inv
  given: (X : Scheme.{u})
  statement: Opens.ι _ ≫ X.topIso.inv = 𝟙 _
  proof: X.topIso.hom_inv_id

中文:
引理 概形.ι_toIso_inv
  条件: (X : 概形.{u})
  结论: Opens.ι _ ≫ X.topIso.inv = 𝟙 _
  证明: X.topIso.hom_inv_id

Depends on / 依赖: X.topIso.hom_inv_id, hom_inv_id, topIso
-/
lemma Scheme.ι_toIso_inv (X : Scheme.{u}) : Opens.ι _ ≫ X.topIso.inv = 𝟙 _ :=
  X.topIso.hom_inv_id

/-- If `U = V`, then `X ∣_ U` is isomorphic to `X ∣_ V`. -/
noncomputable
/--
Definition of `Scheme.isoOfEq` / `Scheme.isoOfEq` 的定义

English:
definition Scheme.isoOfEq
  signature: (X : Scheme.{u}) {U V : X.Opens} (e : U = V)
  body: IsOpenImmersion.isoOfRangeEq U.ι V.ι (by rw [e])

@[reassoc (attr := simp)]

中文:
定义 概形.isoOfEq
  签名: (X : 概形.{u}) {U V : X.Opens} (e : U = V)
  定义体: IsOpenImmersion.isoOfRangeEq U.ι V.ι (by rw [e])

@[reassoc (attr := simp)]

Depends on / 依赖: IsOpenImmersion, IsOpenImmersion.isoOfRangeEq, isoOfRangeEq
-/
def Scheme.isoOfEq (X : Scheme.{u}) {U V : X.Opens} (e : U = V) :
    (U : Scheme.{u}) ≅ V :=
  IsOpenImmersion.isoOfRangeEq U.ι V.ι (by rw [e])

@[reassoc (attr := simp)]
/--
lemma `Scheme.isoOfEq_hom_ι` / 引理 `Scheme.isoOfEq_hom_ι`

English:
lemma Scheme.isoOfEq_hom_ι
  given: (X : Scheme.{u}) {U V : X.Opens} (e : U = V)
  proof: IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)]

中文:
引理 概形.isoOfEq_hom_ι
  条件: (X : 概形.{u}) {U V : X.Opens} (e : U = V)
  证明: IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: IsOpenImmersion, IsOpenImmersion.isoOfRangeEq_hom_fac, isoOfRangeEq_hom_fac
-/
lemma Scheme.isoOfEq_hom_ι (X : Scheme.{u}) {U V : X.Opens} (e : U = V) :
    (X.isoOfEq e).hom ≫ V.ι = U.ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)]
/--
lemma `Scheme.isoOfEq_inv_ι` / 引理 `Scheme.isoOfEq_inv_ι`

English:
lemma Scheme.isoOfEq_inv_ι
  given: (X : Scheme.{u}) {U V : X.Opens} (e : U = V)
  proof: IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

中文:
引理 概形.isoOfEq_inv_ι
  条件: (X : 概形.{u}) {U V : X.Opens} (e : U = V)
  证明: IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

Depends on / 依赖: IsOpenImmersion, IsOpenImmersion.isoOfRangeEq_inv_fac, isoOfRangeEq_inv_fac
-/
lemma Scheme.isoOfEq_inv_ι (X : Scheme.{u}) {U V : X.Opens} (e : U = V) :
    (X.isoOfEq e).inv ≫ U.ι = V.ι :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

/--
lemma `Scheme.isoOfEq_hom` / 引理 `Scheme.isoOfEq_hom`

English:
lemma Scheme.isoOfEq_hom
  given: (X : Scheme.{u}) {U V : X.Opens} (e : U = V)
  proof: rfl

中文:
引理 概形.isoOfEq_hom
  条件: (X : 概形.{u}) {U V : X.Opens} (e : U = V)
  证明: rfl
-/
lemma Scheme.isoOfEq_hom (X : Scheme.{u}) {U V : X.Opens} (e : U = V) :
    (X.isoOfEq e).hom = X.homOfLE e.le := rfl

/--
lemma `Scheme.isoOfEq_inv` / 引理 `Scheme.isoOfEq_inv`

English:
lemma Scheme.isoOfEq_inv
  given: (X : Scheme.{u}) {U V : X.Opens} (e : U = V)
  proof: rfl

@[simp]

中文:
引理 概形.isoOfEq_inv
  条件: (X : 概形.{u}) {U V : X.Opens} (e : U = V)
  证明: rfl

@[simp]
-/
lemma Scheme.isoOfEq_inv (X : Scheme.{u}) {U V : X.Opens} (e : U = V) :
    (X.isoOfEq e).inv = X.homOfLE e.ge := rfl

@[simp]
/--
lemma `Scheme.isoOfEq_rfl` / 引理 `Scheme.isoOfEq_rfl`

English:
lemma Scheme.isoOfEq_rfl
  given: (X : Scheme.{u}) (U : X.Opens)
  statement: X.isoOfEq (refl U) = Iso.refl _
  proof: by
  ext1
  rw [← cancel_mono U.ι]; rw [Scheme.isoOfEq_hom_ι]; rw [Iso.refl_hom]; rw [Category.id_comp]

中文:
引理 概形.isoOfEq_rfl
  条件: (X : 概形.{u}) (U : X.Opens)
  结论: X.isoOfEq (refl U) = 同构.refl _
  证明: by
  ext1
  rw [← cancel_mono U.ι]; rw [Scheme.isoOfEq_hom_ι]; rw [Iso.refl_hom]; rw [Category.id_comp]

Depends on / 依赖: Category, Category.id_comp, Iso.refl_hom, Scheme, Scheme.isoOfEq_hom_, cancel_mono, id_comp, refl_hom
-/
lemma Scheme.isoOfEq_rfl (X : Scheme.{u}) (U : X.Opens) : X.isoOfEq (refl U) = Iso.refl _ := by
  ext1
  rw [← cancel_mono U.ι]; rw [Scheme.isoOfEq_hom_ι]; rw [Iso.refl_hom]; rw [Category.id_comp]

end

/--
Definition of `Scheme.Hom.preimageIso` / `Scheme.Hom.preimageIso` 的定义

English:
definition Scheme.Hom.preimageIso
  signature: {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso (C := Scheme) f]
  body: by
  apply IsOpenImmersion.isoOfRangeEq (f := (f ⁻¹ᵁ U).ι ≫ f) U.ι _
  dsimp
  rw [Set.range_comp]; rw [Opens.range_ι]; rw [Opens.range_ι]
  refine @Set.image_preimage_eq _ _ f U.1 f.homeomorph.surjective

@[reassoc (attr := simp)]

中文:
定义 概形.态射.preimageIso
  签名: {X Y : 概形.{u}} (f : X ⟶ Y) [是同构 (C := 概形) f]
  定义体: by
  apply IsOpenImmersion.isoOfRangeEq (f := (f ⁻¹ᵁ U).ι ≫ f) U.ι _
  dsimp
  rw [Set.range_comp]; rw [Opens.range_ι]; rw [Opens.range_ι]
  refine @Set.image_preimage_eq _ _ f U.1 f.homeomorph.surjective

@[reassoc (attr := simp)]

Depends on / 依赖: Scheme
-/
noncomputable def Scheme.Hom.preimageIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso (C := Scheme) f]
    (U : Y.Opens) : (f ⁻¹ᵁ U).toScheme ≅ U := by
  apply IsOpenImmersion.isoOfRangeEq (f := (f ⁻¹ᵁ U).ι ≫ f) U.ι _
  dsimp
  rw [Set.range_comp]; rw [Opens.range_ι]; rw [Opens.range_ι]
  refine @Set.image_preimage_eq _ _ f U.1 f.homeomorph.surjective

@[reassoc (attr := simp)]
/--
lemma `Scheme.Hom.preimageIso_hom_ι` / 引理 `Scheme.Hom.preimageIso_hom_ι`

English:
lemma Scheme.Hom.preimageIso_hom_ι
  statement: {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso (C := Scheme) f]
  proof: IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)]

中文:
引理 概形.态射.preimageIso_hom_ι
  结论: {X Y : 概形.{u}} (f : X ⟶ Y) [是同构 (C := 概形) f]
  证明: IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: Scheme
-/
lemma Scheme.Hom.preimageIso_hom_ι {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso (C := Scheme) f]
    (U : Y.Opens) : (f.preimageIso U).hom ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)]
/--
lemma `Scheme.Hom.preimageIso_inv_ι` / 引理 `Scheme.Hom.preimageIso_inv_ι`

English:
lemma Scheme.Hom.preimageIso_inv_ι
  statement: {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso (C := Scheme) f]
  proof: IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

中文:
引理 概形.态射.preimageIso_inv_ι
  结论: {X Y : 概形.{u}} (f : X ⟶ Y) [是同构 (C := 概形) f]
  证明: IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

Depends on / 依赖: Scheme
-/
lemma Scheme.Hom.preimageIso_inv_ι {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso (C := Scheme) f]
    (U : Y.Opens) : (f.preimageIso U).inv ≫ (f ⁻¹ᵁ U).ι ≫ f = U.ι :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

/--
Definition of `Scheme.Opens.isoOfLE` / `Scheme.Opens.isoOfLE` 的定义

English:
definition Scheme.Opens.isoOfLE
  signature: {X : Scheme.{u}} {U V : X.Opens} (hUV : U <= V)
  body: IsOpenImmersion.isoOfRangeEq ((V.ι ⁻¹ᵁ U).ι ≫ V.ι) U.ι by
    have : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U := by simpa [Scheme.Hom.image_preimage_eq_opensRange_inf]
    rw [Scheme.Hom.comp_base]; rw [TopCat.coe_comp]; rw [Scheme.Opens.range_ι]; rw [Set.range_comp]; rw [← this]
    simp

@[reassoc (attr := simp)]

中文:
定义 概形.Opens.isoOfLE
  签名: {X : 概形.{u}} {U V : X.Opens} (hUV : U <= V)
  定义体: IsOpenImmersion.isoOfRangeEq ((V.ι ⁻¹ᵁ U).ι ≫ V.ι) U.ι by
    have : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U := by simpa [Scheme.Hom.image_preimage_eq_opensRange_inf]
    rw [Scheme.Hom.comp_base]; rw [TopCat.coe_comp]; rw [Scheme.Opens.range_ι]; rw [Set.range_comp]; rw [← this]
    simp

@[reassoc (attr := simp)]

Depends on / 依赖: IsOpenImmersion, IsOpenImmersion.isoOfRangeEq, Scheme, Scheme.Hom.comp_base, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.range_, Set.range_comp, TopCat, TopCat.coe_comp, coe_comp, comp_base, image_preimage_eq_opensRange_inf, isoOfRangeEq, range_comp
-/
noncomputable def Scheme.Opens.isoOfLE {X : Scheme.{u}} {U V : X.Opens} (hUV : U <= V) :
    (V.ι ⁻¹ᵁ U).toScheme ≅ U :=
IsOpenImmersion.isoOfRangeEq ((V.ι ⁻¹ᵁ U).ι ≫ V.ι) U.ι by
    have : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U := by simpa [Scheme.Hom.image_preimage_eq_opensRange_inf]
    rw [Scheme.Hom.comp_base]; rw [TopCat.coe_comp]; rw [Scheme.Opens.range_ι]; rw [Set.range_comp]; rw [← this]
    simp

@[reassoc (attr := simp)]
/--
lemma `Scheme.Opens.isoOfLE_hom_ι` / 引理 `Scheme.Opens.isoOfLE_hom_ι`

English:
lemma Scheme.Opens.isoOfLE_hom_ι
  given: {X : Scheme.{u}} {U V : X.Opens} (hUV : U <= V)
  proof: by
  simp [isoOfLE]

@[reassoc (attr := simp)]

中文:
引理 概形.Opens.isoOfLE_hom_ι
  条件: {X : 概形.{u}} {U V : X.Opens} (hUV : U <= V)
  证明: by
  simp [isoOfLE]

@[reassoc (attr := simp)]

Depends on / 依赖: isoOfLE
-/
lemma Scheme.Opens.isoOfLE_hom_ι {X : Scheme.{u}} {U V : X.Opens} (hUV : U <= V) :
    (isoOfLE hUV).hom ≫ U.ι = (V.ι ⁻¹ᵁ U).ι ≫ V.ι := by
  simp [isoOfLE]

@[reassoc (attr := simp)]
/--
lemma `Scheme.Opens.isoOfLE_inv_ι` / 引理 `Scheme.Opens.isoOfLE_inv_ι`

English:
lemma Scheme.Opens.isoOfLE_inv_ι
  given: {X : Scheme.{u}} {U V : X.Opens} (hUV : U <= V)
  proof: by
  simp [isoOfLE]

中文:
引理 概形.Opens.isoOfLE_inv_ι
  条件: {X : 概形.{u}} {U V : X.Opens} (hUV : U <= V)
  证明: by
  simp [isoOfLE]

Depends on / 依赖: isoOfLE
-/
lemma Scheme.Opens.isoOfLE_inv_ι {X : Scheme.{u}} {U V : X.Opens} (hUV : U <= V) :
    (isoOfLE hUV).inv ≫ (V.ι ⁻¹ᵁ U).ι ≫ V.ι = U.ι := by
  simp [isoOfLE]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `basicOpenIsoSpecAway` / `basicOpenIsoSpecAway` 的定义

English:
definition basicOpenIsoSpecAway
  signature: {R : CommRingCat.{u}} (f : R)
  body: IsOpenImmersion.isoOfRangeEq (Scheme.Opens.ι _) (Spec.map (CommRingCat.ofHom (algebraMap _ _)))
    (by
      simp only [Scheme.Opens.range_ι]
      exact (PrimeSpectrum.localization_away_comap_range _ _).symm)

@[reassoc (attr := simp)]

中文:
定义 basicOpenIsoSpecAway
  签名: {R : 交换环范畴.{u}} (f : R)
  定义体: IsOpenImmersion.isoOfRangeEq (Scheme.Opens.ι _) (Spec.map (CommRingCat.ofHom (algebraMap _ _)))
    (by
      simp only [Scheme.Opens.range_ι]
      exact (PrimeSpectrum.localization_away_comap_range _ _).symm)

@[reassoc (attr := simp)]

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.basicOpen, basicOpen
-/
def basicOpenIsoSpecAway {R : CommRingCat.{u}} (f : R) :
    Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f) ≅
      Spec (.of <| Localization.Away f) :=
  IsOpenImmersion.isoOfRangeEq (Scheme.Opens.ι _) (Spec.map (CommRingCat.ofHom (algebraMap _ _)))
    (by
      simp only [Scheme.Opens.range_ι]
      exact (PrimeSpectrum.localization_away_comap_range _ _).symm)

@[reassoc (attr := simp)]
/--
lemma `basicOpenIsoSpecAway_hom_SpecMap` / 引理 `basicOpenIsoSpecAway_hom_SpecMap`

English:
lemma basicOpenIsoSpecAway_hom_SpecMap
  given: {R : CommRingCat.{u}} (f : R)
  proof: by
  simp [basicOpenIsoSpecAway]

中文:
引理 basicOpenIsoSpecAway_hom_SpecMap
  条件: {R : 交换环范畴.{u}} (f : R)
  证明: by
  simp [basicOpenIsoSpecAway]

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.basicOpen, basicOpen, basicOpenIsoSpecAway
-/
lemma basicOpenIsoSpecAway_hom_SpecMap {R : CommRingCat.{u}} (f : R) :
    (basicOpenIsoSpecAway f).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R _)) =
        Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f) := by
  simp [basicOpenIsoSpecAway]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `basicOpenIsoSpecAway_inv_homOfLE` / 引理 `basicOpenIsoSpecAway_inv_homOfLE`

English:
lemma basicOpenIsoSpecAway_inv_homOfLE
  given: {R : CommRingCat.{u}} (f g x : R) (hx : x = f * g)
  proof: by rw [hx]; infer_instance
    (basicOpenIsoSpecAway x).inv ≫ (Spec R).homOfLE (by simp [hx, PrimeSpectrum.basicOpen_mul]) =
      Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayRight f g)) ≫
        (basicOpenIsoSpecAway f).inv := by
  subst hx
  rw [← cancel_mono (Scheme.Opens.ι _)]
  

中文:
引理 basicOpenIsoSpecAway_inv_homOfLE
  条件: {R : 交换环范畴.{u}} (f g x : R) (hx : x = f * g)
  证明: by rw [hx]; infer_instance
    (basicOpenIsoSpecAway x).inv ≫ (Spec R).homOfLE (by simp [hx, PrimeSpectrum.basicOpen_mul]) =
      Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayRight f g)) ≫
        (basicOpenIsoSpecAway f).inv := by
  subst hx
  rw [← cancel_mono (Scheme.Opens.ι _)]
  

Depends on / 依赖: Category, Category.assoc, CommRingCat, CommRingCat.ofHom, CommRingCat.ofHom_comp, IsLocalization, IsLocalization.Away.awayToAwayRight, IsLocalization.Away.awayToAwayRight_eq, IsOpenImmersion, IsOpenImmersion.isoOfRangeEq_inv_fac, PrimeSpectrum, PrimeSpectrum.basicOpen_mul, Scheme, Scheme.Opens, Scheme.homOfLE_, Spec.map, Spec.map_comp, awayToAwayRight, awayToAwayRight_eq, basicOpenIsoSpecAway
-/
lemma basicOpenIsoSpecAway_inv_homOfLE {R : CommRingCat.{u}} (f g x : R) (hx : x = f * g) :
    haveI : IsLocalization.Away (f * g) (Localization.Away x) := by rw [hx]; infer_instance
    (basicOpenIsoSpecAway x).inv ≫ (Spec R).homOfLE (by simp [hx, PrimeSpectrum.basicOpen_mul]) =
      Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayRight f g)) ≫
        (basicOpenIsoSpecAway f).inv := by
  subst hx
  rw [← cancel_mono (Scheme.Opens.ι _)]
  simp only [basicOpenIsoSpecAway, Category.assoc, Scheme.homOfLE_ι,
    IsOpenImmersion.isoOfRangeEq_inv_fac]
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr
  ext x
  exact (IsLocalization.Away.awayToAwayRight_eq f g x (S := Localization.Away f)).symm

section MorphismRestrict

/--
Definition of `pullbackRestrictIsoRestrict` / `pullbackRestrictIsoRestrict` 的定义

English:
definition pullbackRestrictIsoRestrict
  signature: {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
  body: by
  refine IsOpenImmersion.isoOfRangeEq (pullback.fst f _) (Scheme.Opens.ι _) ?_
  simp [IsOpenImmersion.range_pullbackFst]

@[simp, reassoc]

中文:
定义 pullbackRestrictIsoRestrict
  签名: {X Y : 概形.{u}} (f : X ⟶ Y) (U : Y.Opens)
  定义体: by
  refine IsOpenImmersion.isoOfRangeEq (pullback.fst f _) (Scheme.Opens.ι _) ?_
  simp [IsOpenImmersion.range_pullbackFst]

@[simp, reassoc]

Depends on / 依赖: IsOpenImmersion, IsOpenImmersion.isoOfRangeEq, IsOpenImmersion.range_pullbackFst, Scheme, Scheme.Opens, isoOfRangeEq, pullback, pullback.fst, range_pullbackFst
-/
def pullbackRestrictIsoRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    pullback f U.ι ≅ f ⁻¹ᵁ U := by
  refine IsOpenImmersion.isoOfRangeEq (pullback.fst f _) (Scheme.Opens.ι _) ?_
  simp [IsOpenImmersion.range_pullbackFst]

@[simp, reassoc]
/--
theorem `pullbackRestrictIsoRestrict_inv_fst` / 定理 `pullbackRestrictIsoRestrict_inv_fst`

English:
theorem pullbackRestrictIsoRestrict_inv_fst
  given: {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
  proof: by
  delta pullbackRestrictIsoRestrict; simp

@[reassoc (attr := simp)]

中文:
定理 pullbackRestrictIsoRestrict_inv_fst
  条件: {X Y : 概形.{u}} (f : X ⟶ Y) (U : Y.Opens)
  证明: by
  delta pullbackRestrictIsoRestrict; simp

@[reassoc (attr := simp)]

Depends on / 依赖: pullbackRestrictIsoRestrict
-/
theorem pullbackRestrictIsoRestrict_inv_fst {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    (pullbackRestrictIsoRestrict f U).inv ≫ pullback.fst f _ = (f ⁻¹ᵁ U).ι := by
  delta pullbackRestrictIsoRestrict; simp

@[reassoc (attr := simp)]
/--
theorem `pullbackRestrictIsoRestrict_hom_ι` / 定理 `pullbackRestrictIsoRestrict_hom_ι`

English:
theorem pullbackRestrictIsoRestrict_hom_ι
  given: {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
  proof: by
  delta pullbackRestrictIsoRestrict; simp

中文:
定理 pullbackRestrictIsoRestrict_hom_ι
  条件: {X Y : 概形.{u}} (f : X ⟶ Y) (U : Y.Opens)
  证明: by
  delta pullbackRestrictIsoRestrict; simp

Depends on / 依赖: pullbackRestrictIsoRestrict
-/
theorem pullbackRestrictIsoRestrict_hom_ι {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    (pullbackRestrictIsoRestrict f U).hom ≫ (f ⁻¹ᵁ U).ι = pullback.fst f _ := by
  delta pullbackRestrictIsoRestrict; simp

/--
Definition of `morphismRestrict` / `morphismRestrict` 的定义

English:
definition morphismRestrict
  signature: {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
  body: (pullbackRestrictIsoRestrict f U).inv ≫ pullback.snd _ _

中文:
定义 morphismRestrict
  签名: {X Y : 概形.{u}} (f : X ⟶ Y) (U : Y.Opens)
  定义体: (pullbackRestrictIsoRestrict f U).inv ≫ pullback.snd _ _

Depends on / 依赖: pullback, pullback.snd, pullbackRestrictIsoRestrict
-/
def morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) : (f ⁻¹ᵁ U).toScheme ⟶ U :=
  (pullbackRestrictIsoRestrict f U).inv ≫ pullback.snd _ _

/-- the notation for restricting a morphism of scheme to an open subset of the target scheme -/
infixl:85 " ∣_ " => morphismRestrict

@[reassoc (attr := simp)]
/--
theorem `pullbackRestrictIsoRestrict_hom_morphismRestrict` / 定理 `pullbackRestrictIsoRestrict_hom_morphismRestrict`

English:
theorem pullbackRestrictIsoRestrict_hom_morphismRestrict
  statement: {X Y : Scheme.{u}} (f : X ⟶ Y)
  proof: Iso.hom_inv_id_assoc _ _

@[reassoc (attr := simp)]

中文:
定理 pullbackRestrictIsoRestrict_hom_morphismRestrict
  结论: {X Y : 概形.{u}} (f : X ⟶ Y)
  证明: Iso.hom_inv_id_assoc _ _

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.hom_inv_id_assoc, hom_inv_id_assoc
-/
theorem pullbackRestrictIsoRestrict_hom_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) : (pullbackRestrictIsoRestrict f U).hom ≫ f ∣_ U = pullback.snd _ _ :=
  Iso.hom_inv_id_assoc _ _

@[reassoc (attr := simp)]
/--
theorem `morphismRestrict_ι` / 定理 `morphismRestrict_ι`

English:
theorem morphismRestrict_ι
  given: {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
  proof: by
  delta morphismRestrict
  rw [Category.assoc]; rw [pullback.condition.symm]; rw [pullbackRestrictIsoRestrict_inv_fst_assoc]

中文:
定理 morphismRestrict_ι
  条件: {X Y : 概形.{u}} (f : X ⟶ Y) (U : Y.Opens)
  证明: by
  delta morphismRestrict
  rw [Category.assoc]; rw [pullback.condition.symm]; rw [pullbackRestrictIsoRestrict_inv_fst_assoc]

Depends on / 依赖: Category, Category.assoc, condition, morphismRestrict, pullback, pullback.condition.symm, pullbackRestrictIsoRestrict_inv_fst_assoc
-/
theorem morphismRestrict_ι {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    f ∣_ U ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f := by
  delta morphismRestrict
  rw [Category.assoc]; rw [pullback.condition.symm]; rw [pullbackRestrictIsoRestrict_inv_fst_assoc]

/--
theorem `isPullback_morphismRestrict` / 定理 `isPullback_morphismRestrict`

English:
theorem isPullback_morphismRestrict
  given: {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
  proof: by
  apply IsOpenImmersion.isPullback <;>
  simp

中文:
定理 isPullback_morphismRestrict
  条件: {X Y : 概形.{u}} (f : X ⟶ Y) (U : Y.Opens)
  证明: by
  apply IsOpenImmersion.isPullback <;>
  simp

Depends on / 依赖: IsOpenImmersion, IsOpenImmersion.isPullback, isPullback
-/
theorem isPullback_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    IsPullback (f ∣_ U) (f ⁻¹ᵁ U).ι U.ι f := by
  apply IsOpenImmersion.isPullback <;>
  simp

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isPullback_opens_inf_le` / 引理 `isPullback_opens_inf_le`

English:
lemma isPullback_opens_inf_le
  given: {X : Scheme} {U V W : X.Opens} (hU : U <= W) (hV : V <= W)
  proof: by
  refine (isPullback_morphismRestrict (X.homOfLE hV) (W.ι ⁻¹ᵁ U)).of_iso (V.ι.isoImage _ ≪≫
    X.isoOfEq ?_) (W.ι.isoImage _ ≪≫ X.isoOfEq ?_) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [← TopologicalSpace.Opens.map_comp_obj, ← Scheme.Hom.comp_base, Scheme.homOfLE_ι]
    exact V.functor_map_eq_

中文:
引理 isPullback_opens_inf_le
  条件: {X : 概形} {U V W : X.Opens} (hU : U <= W) (hV : V <= W)
  证明: by
  refine (isPullback_morphismRestrict (X.homOfLE hV) (W.ι ⁻¹ᵁ U)).of_iso (V.ι.isoImage _ ≪≫
    X.isoOfEq ?_) (W.ι.isoImage _ ≪≫ X.isoOfEq ?_) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [← TopologicalSpace.Opens.map_comp_obj, ← Scheme.Hom.comp_base, Scheme.homOfLE_ι]
    exact V.functor_map_eq_

Depends on / 依赖: Iso.refl, Scheme, Scheme.Hom.comp_base, Scheme.Opens, Scheme.homOfLE_, TopologicalSpace, TopologicalSpace.Opens.map_comp_obj, V.functor_map_eq_inf, W.functor_map_eq_inf, X.homOfLE, X.isoOfEq, all_goals, cancel_mono, comp_base, functor_map_eq_inf, homOfLE, isPullback_morphismRestrict, isoImage, isoOfEq, map_comp_obj
-/
lemma isPullback_opens_inf_le {X : Scheme} {U V W : X.Opens} (hU : U <= W) (hV : V <= W) :
    IsPullback (X.homOfLE inf_le_left) (X.homOfLE inf_le_right) (X.homOfLE hU) (X.homOfLE hV) := by
  refine (isPullback_morphismRestrict (X.homOfLE hV) (W.ι ⁻¹ᵁ U)).of_iso (V.ι.isoImage _ ≪≫
    X.isoOfEq ?_) (W.ι.isoImage _ ≪≫ X.isoOfEq ?_) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [← TopologicalSpace.Opens.map_comp_obj, ← Scheme.Hom.comp_base, Scheme.homOfLE_ι]
    exact V.functor_map_eq_inf U
  · exact (W.functor_map_eq_inf U).trans (by simpa)
  all_goals { simp [← cancel_mono (Scheme.Opens.ι _)] }

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isPullback_opens_inf` / 引理 `isPullback_opens_inf`

English:
lemma isPullback_opens_inf
  given: {X : Scheme} (U V : X.Opens)
  proof: (isPullback_morphismRestrict V.ι U).of_iso (V.ι.isoImage _ ≪≫ X.isoOfEq
    (V.functor_map_eq_inf U)) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [← cancel_mono U.ι])
    (by simp [← cancel_mono V.ι]) (by simp) (by simp)

中文:
引理 isPullback_opens_inf
  条件: {X : 概形} (U V : X.Opens)
  证明: (isPullback_morphismRestrict V.ι U).of_iso (V.ι.isoImage _ ≪≫ X.isoOfEq
    (V.functor_map_eq_inf U)) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [← cancel_mono U.ι])
    (by simp [← cancel_mono V.ι]) (by simp) (by simp)

Depends on / 依赖: Iso.refl, V.functor_map_eq_inf, X.isoOfEq, cancel_mono, functor_map_eq_inf, isPullback_morphismRestrict, isoImage, isoOfEq, of_iso
-/
lemma isPullback_opens_inf {X : Scheme} (U V : X.Opens) :
    IsPullback (X.homOfLE inf_le_left) (X.homOfLE inf_le_right) U.ι V.ι :=
  (isPullback_morphismRestrict V.ι U).of_iso (V.ι.isoImage _ ≪≫ X.isoOfEq
    (V.functor_map_eq_inf U)) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [← cancel_mono U.ι])
    (by simp [← cancel_mono V.ι]) (by simp) (by simp)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `morphismRestrict_id` / 引理 `morphismRestrict_id`

English:
lemma morphismRestrict_id
  given: {X : Scheme.{u}} (U : X.Opens)
  statement: 𝟙 X ∣_ U = 𝟙 _
  proof: by
  rw [← cancel_mono U.ι]; rw [morphismRestrict_ι]; rw [Category.comp_id]; rw [Category.id_comp]
  rfl

中文:
引理 morphismRestrict_id
  条件: {X : 概形.{u}} (U : X.Opens)
  结论: 𝟙 X ∣_ U = 𝟙 _
  证明: by
  rw [← cancel_mono U.ι]; rw [morphismRestrict_ι]; rw [Category.comp_id]; rw [Category.id_comp]
  rfl

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, cancel_mono, comp_id, id_comp
-/
lemma morphismRestrict_id {X : Scheme.{u}} (U : X.Opens) : 𝟙 X ∣_ U = 𝟙 _ := by
  rw [← cancel_mono U.ι]; rw [morphismRestrict_ι]; rw [Category.comp_id]; rw [Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `morphismRestrict_comp` / 定理 `morphismRestrict_comp`

English:
theorem morphismRestrict_comp
  given: {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Opens Z)
  proof: by
  delta morphismRestrict
  rw [← pullbackRightPullbackFstIso_inv_snd_snd]
  simp_rw [← Category.assoc]
  congr 1
  rw [← cancel_mono (pullback.fst _ _)]
  simp_rw [Category.assoc]
  rw [pullbackRestrictIsoRestrict_inv_fst]; rw [pullbackRightPullbackFstIso_inv_snd_fst]; rw [←
    pullback.conditio

中文:
定理 morphismRestrict_comp
  条件: {X Y Z : 概形.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Opens Z)
  证明: by
  delta morphismRestrict
  rw [← pullbackRightPullbackFstIso_inv_snd_snd]
  simp_rw [← Category.assoc]
  congr 1
  rw [← cancel_mono (pullback.fst _ _)]
  simp_rw [Category.assoc]
  rw [pullbackRestrictIsoRestrict_inv_fst]; rw [pullbackRightPullbackFstIso_inv_snd_fst]; rw [←
    pullback.conditio

Depends on / 依赖: Category, Category.assoc, cancel_mono, condition, morphismRestrict, pullback, pullback.condition, pullback.fst, pullbackRestrictIsoRestrict_inv_fst, pullbackRestrictIsoRestrict_inv_fst_assoc, pullbackRightPullbackFstIso_inv_snd_fst, pullbackRightPullbackFstIso_inv_snd_snd, simp_rw
-/
theorem morphismRestrict_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Opens Z) :
    (f ≫ g) ∣_ U = f ∣_ g ⁻¹ᵁ U ≫ g ∣_ U := by
  delta morphismRestrict
  rw [← pullbackRightPullbackFstIso_inv_snd_snd]
  simp_rw [← Category.assoc]
  congr 1
  rw [← cancel_mono (pullback.fst _ _)]
  simp_rw [Category.assoc]
  rw [pullbackRestrictIsoRestrict_inv_fst]; rw [pullbackRightPullbackFstIso_inv_snd_fst]; rw [←
    pullback.condition]; rw [pullbackRestrictIsoRestrict_inv_fst_assoc]; rw [pullbackRestrictIsoRestrict_inv_fst_assoc]
  rfl

@[reassoc]
/--
theorem `morphismRestrict_homOfLE` / 定理 `morphismRestrict_homOfLE`

English:
theorem morphismRestrict_homOfLE
  given: {X Y : Scheme.{u}} (f : X ⟶ Y) (U V : Y.Opens) (e : U <= V)
  proof: by
  simp [← cancel_mono V.ι]

@[reassoc (attr := simp)]

中文:
定理 morphismRestrict_homOfLE
  条件: {X Y : 概形.{u}} (f : X ⟶ Y) (U V : Y.Opens) (e : U <= V)
  证明: by
  simp [← cancel_mono V.ι]

@[reassoc (attr := simp)]

Depends on / 依赖: cancel_mono
-/
theorem morphismRestrict_homOfLE {X Y : Scheme.{u}} (f : X ⟶ Y) (U V : Y.Opens) (e : U <= V) :
    (f ∣_ U) ≫ Y.homOfLE e = X.homOfLE (f.preimage_mono e) ≫ (f ∣_ V) := by
  simp [← cancel_mono V.ι]

@[reassoc (attr := simp)]
/--
lemma `Scheme.Hom.isoImage_preimage_hom_homOfLE` / 引理 `Scheme.Hom.isoImage_preimage_hom_homOfLE`

English:
lemma Scheme.Hom.isoImage_preimage_hom_homOfLE
  statement: {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
  proof: by
  simp [← cancel_mono U.ι]

中文:
引理 概形.态射.isoImage_preimage_hom_homOfLE
  结论: {X Y : 概形.{u}} (f : X ⟶ Y) [是开浸入 f]
  证明: by
  simp [← cancel_mono U.ι]

Depends on / 依赖: cancel_mono
-/
lemma Scheme.Hom.isoImage_preimage_hom_homOfLE {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (U : Y.Opens) :
    (f.isoImage (f ⁻¹ᵁ U)).hom ≫ Y.homOfLE (f.image_preimage_le U) = f ∣_ U := by
  simp [← cancel_mono U.ι]

instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (U : Y.Opens) : IsIso (f ∣_ U) := by
  delta morphismRestrict; infer_instance

@[simp]
/--
theorem `morphismRestrict_base_coe` / 定理 `morphismRestrict_base_coe`

English:
theorem morphismRestrict_base_coe
  given: {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (x)
  proof: congr_arg (fun f => (Scheme.Hom.toLRSHom f).base x)
    (morphismRestrict_ι f U)

中文:
定理 morphismRestrict_base_coe
  条件: {X Y : 概形.{u}} (f : X ⟶ Y) (U : Y.Opens) (x)
  证明: congr_arg (fun f => (Scheme.Hom.toLRSHom f).base x)
    (morphismRestrict_ι f U)

Depends on / 依赖: Scheme, Scheme.Hom.toLRSHom, congr_arg, toLRSHom
-/
theorem morphismRestrict_base_coe {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (x) :
    ((f ∣_ U) x).1 = f x.1 :=
  congr_arg (fun f => (Scheme.Hom.toLRSHom f).base x)
    (morphismRestrict_ι f U)

/--
theorem `morphismRestrict_base` / 定理 `morphismRestrict_base`

English:
theorem morphismRestrict_base
  given: {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
  proof: funext fun x => Subtype.ext (morphismRestrict_base_coe f U x)

中文:
定理 morphismRestrict_base
  条件: {X Y : 概形.{u}} (f : X ⟶ Y) (U : Y.Opens)
  证明: funext fun x => Subtype.ext (morphismRestrict_base_coe f U x)

Depends on / 依赖: Subtype, Subtype.ext, morphismRestrict_base_coe
-/
theorem morphismRestrict_base {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    ⇑(f ∣_ U) = U.1.restrictPreimage f :=
  funext fun x => Subtype.ext (morphismRestrict_base_coe f U x)

/--
theorem `image_morphismRestrict_preimage` / 定理 `image_morphismRestrict_preimage`

English:
theorem image_morphismRestrict_preimage
  given: {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U)
  proof: IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback (isPullback_morphismRestrict f U) V

中文:
定理 image_morphismRestrict_preimage
  条件: {X Y : 概形.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U)
  证明: IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback (isPullback_morphismRestrict f U) V

Depends on / 依赖: IsOpenImmersion, IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback, image_preimage_eq_preimage_image_of_isPullback, isPullback_morphismRestrict
-/
theorem image_morphismRestrict_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U) :
    (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V) = f ⁻¹ᵁ (U.ι ''ᵁ V) :=
  IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback (isPullback_morphismRestrict f U) V

set_option backward.isDefEq.respectTransparency false in
open Scheme in
/--
theorem `morphismRestrict_app` / 定理 `morphismRestrict_app`

English:
theorem morphismRestrict_app
  given: {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : U.toScheme.Opens)
  proof: by
  obtain ⟨V, rfl⟩ : exists V', U.ι ⁻¹ᵁ U.ι ''ᵁ V' = V := ⟨_, U.ι.preimage_image_eq V⟩
  simpa [← Functor.map_comp_assoc, ← Functor.map_comp] using!
    congr(Y.presheaf.map (eqToHom (congr_arg (U.ι ''ᵁ ·) (U.ι.preimage_image_eq V).symm)).op ≫
 (Scheme.Hom.congr_app (morphismRestrict_ι f U) (U.ι '

中文:
定理 morphismRestrict_app
  条件: {X Y : 概形.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : U.toScheme.Opens)
  证明: by
  obtain ⟨V, rfl⟩ : exists V', U.ι ⁻¹ᵁ U.ι ''ᵁ V' = V := ⟨_, U.ι.preimage_image_eq V⟩
  simpa [← Functor.map_comp_assoc, ← Functor.map_comp] using!
    congr(Y.presheaf.map (eqToHom (congr_arg (U.ι ''ᵁ ·) (U.ι.preimage_image_eq V).symm)).op ≫
 (Scheme.Hom.congr_app (morphismRestrict_ι f U) (U.ι '

Depends on / 依赖: Functor, Functor.map_comp, Functor.map_comp_assoc, Scheme, Scheme.Hom.congr_app, Y.presheaf.map, congr_app, congr_arg, eqToHom, map_comp, map_comp_assoc, preimage_image_eq, presheaf
-/
theorem morphismRestrict_app {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : U.toScheme.Opens) :
    (f ∣_ U).app V = f.app (U.ι ''ᵁ V) ≫
        X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op := by
  obtain ⟨V, rfl⟩ : exists V', U.ι ⁻¹ᵁ U.ι ''ᵁ V' = V := ⟨_, U.ι.preimage_image_eq V⟩
  simpa [← Functor.map_comp_assoc, ← Functor.map_comp] using!
    congr(Y.presheaf.map (eqToHom (congr_arg (U.ι ''ᵁ ·) (U.ι.preimage_image_eq V).symm)).op ≫
 (Scheme.Hom.congr_app (morphismRestrict_ι f U) (U.ι ''ᵁ V)))

/--
theorem `morphismRestrict_appTop` / 定理 `morphismRestrict_appTop`

English:
theorem morphismRestrict_appTop
  given: {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
  proof: morphismRestrict_app ..

@[simp]

中文:
定理 morphismRestrict_appTop
  条件: {X Y : 概形.{u}} (f : X ⟶ Y) (U : Y.Opens)
  证明: morphismRestrict_app ..

@[simp]

Depends on / 依赖: morphismRestrict_app
-/
theorem morphismRestrict_appTop {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    (f ∣_ U).appTop = f.app (U.ι ''ᵁ ⊤) ≫
        X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op :=
  morphismRestrict_app ..

@[simp]
/--
theorem `morphismRestrict_app'` / 定理 `morphismRestrict_app'`

English:
theorem morphismRestrict_app'
  given: {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U)
  proof: morphismRestrict_app f U V

中文:
定理 morphismRestrict_app'
  条件: {X Y : 概形.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U)
  证明: morphismRestrict_app f U V

Depends on / 依赖: morphismRestrict_app
-/
theorem morphismRestrict_app' {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U) :
    (f ∣_ U).app V = f.appLE _ _ (image_morphismRestrict_preimage f U V).le :=
  morphismRestrict_app f U V

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `morphismRestrict_appLE` / 定理 `morphismRestrict_appLE`

English:
theorem morphismRestrict_appLE
  given: {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V W e)
  proof: by
  rw [Scheme.Hom.appLE]; rw [morphismRestrict_app']; rw [Scheme.Opens.toScheme_presheaf_map]; rw [Scheme.Hom.appLE_map]

@[reassoc]

中文:
定理 morphismRestrict_appLE
  条件: {X Y : 概形.{u}} (f : X ⟶ Y) (U : Y.Opens) (V W e)
  证明: by
  rw [Scheme.Hom.appLE]; rw [morphismRestrict_app']; rw [Scheme.Opens.toScheme_presheaf_map]; rw [Scheme.Hom.appLE_map]

@[reassoc]

Depends on / 依赖: Scheme, Scheme.Hom.appLE, Scheme.Hom.appLE_map, Scheme.Opens.toScheme_presheaf_map, appLE_map, morphismRestrict_app, toScheme_presheaf_map
-/
theorem morphismRestrict_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V W e) :
    (f ∣_ U).appLE V W e = f.appLE (U.ι ''ᵁ V) ((f ⁻¹ᵁ U).ι ''ᵁ W)
      ((Set.image_mono e).trans (image_morphismRestrict_preimage f U V).le) := by
  rw [Scheme.Hom.appLE]; rw [morphismRestrict_app']; rw [Scheme.Opens.toScheme_presheaf_map]; rw [Scheme.Hom.appLE_map]

@[reassoc]
/--
theorem `morphismRestrict_homOfLE_isoImage_ι_hom` / 定理 `morphismRestrict_homOfLE_isoImage_ι_hom`

English:
theorem morphismRestrict_homOfLE_isoImage_ι_hom
  proof: by
  simp [← cancel_mono (V.ι ''ᵁ W).ι]

@[reassoc]

中文:
定理 morphismRestrict_homOfLE_isoImage_ι_hom
  证明: by
  simp [← cancel_mono (V.ι ''ᵁ W).ι]

@[reassoc]

Depends on / 依赖: cancel_mono
-/
theorem morphismRestrict_homOfLE_isoImage_ι_hom
    {X : Scheme.{u}} {U V : X.Opens} (e : U <= V) (W : Opens V) :
    X.homOfLE e ∣_ W ≫ (V.ι.isoImage W).hom =
      (U.ι.isoImage (X.homOfLE e ⁻¹ᵁ W)).hom ≫ X.homOfLE (X.ι_image_homOfLE_le_ι_image e W) := by
  simp [← cancel_mono (V.ι ''ᵁ W).ι]

@[reassoc]
/--
theorem `isoImage_ι_inv_morphismRestrict_homOfLE` / 定理 `isoImage_ι_inv_morphismRestrict_homOfLE`

English:
theorem isoImage_ι_inv_morphismRestrict_homOfLE
  statement: {X : Scheme.{u}} {U V : X.Opens}
  proof: by
  simp [← cancel_mono (V.ι.isoImage W).hom, morphismRestrict_homOfLE_isoImage_ι_hom]

中文:
定理 isoImage_ι_inv_morphismRestrict_homOfLE
  结论: {X : 概形.{u}} {U V : X.Opens}
  证明: by
  simp [← cancel_mono (V.ι.isoImage W).hom, morphismRestrict_homOfLE_isoImage_ι_hom]

Depends on / 依赖: cancel_mono, isoImage
-/
theorem isoImage_ι_inv_morphismRestrict_homOfLE {X : Scheme.{u}} {U V : X.Opens}
    (e : U <= V) (W : Opens V) :
    (U.ι.isoImage (X.homOfLE e ⁻¹ᵁ W)).inv ≫ X.homOfLE e ∣_ W =
      X.homOfLE (X.ι_image_homOfLE_le_ι_image e W) ≫ (V.ι.isoImage W).inv := by
  simp [← cancel_mono (V.ι.isoImage W).hom, morphismRestrict_homOfLE_isoImage_ι_hom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `morphismRestrictOpensRange` / `morphismRestrictOpensRange` 的定义

English:
definition morphismRestrictOpensRange
  signature: {X Y U : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ Y) [IsOpenImmersion g]
  body: by
  let V : Y.Opens := g.opensRange
  let e :=
    IsOpenImmersion.isoOfRangeEq g V.ι Subtype.range_coe.symm
  let t : pullback f g ⟶ pullback f V.ι :=
    pullback.map _ _ _ _ (𝟙 _) e.hom (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
      (by rw [Category.comp_id, IsOpenImmersion.isoOfRangeE

中文:
定义 morphismRestrictOpensRange
  签名: {X Y U : 概形.{u}} (f : X ⟶ Y) (g : U ⟶ Y) [是开浸入 g]
  定义体: by
  let V : Y.Opens := g.opensRange
  let e :=
    IsOpenImmersion.isoOfRangeEq g V.ι Subtype.range_coe.symm
  let t : pullback f g ⟶ pullback f V.ι :=
    pullback.map _ _ _ _ (𝟙 _) e.hom (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
      (by rw [Category.comp_id, IsOpenImmersion.isoOfRangeE

Depends on / 依赖: Arrow.isoMk, Category, Category.assoc, Category.comp_id, Category.id_comp, IsOpenImmersion, IsOpenImmersion.isoOfRangeEq, IsOpenImmersion.isoOfRangeEq_hom_fac, Iso.comp_inv_eq, Iso.trans_hom, Subtype, Subtype.range_coe.symm, Y.Opens, asIso_hom, cancel_mono, comp_id, comp_inv_eq, e.hom, g.opensRange, id_comp
-/
def morphismRestrictOpensRange {X Y U : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ Y) [IsOpenImmersion g] :
    Arrow.mk (f ∣_ g.opensRange) ≅ Arrow.mk (pullback.snd f g) := by
  let V : Y.Opens := g.opensRange
  let e :=
    IsOpenImmersion.isoOfRangeEq g V.ι Subtype.range_coe.symm
  let t : pullback f g ⟶ pullback f V.ι :=
    pullback.map _ _ _ _ (𝟙 _) e.hom (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
      (by rw [Category.comp_id, IsOpenImmersion.isoOfRangeEq_hom_fac])
  symm
  refine Arrow.isoMk (asIso t ≪≫ pullbackRestrictIsoRestrict f V) e ?_
  rw [Iso.trans_hom]; rw [asIso_hom]; rw [← Iso.comp_inv_eq]; rw [← cancel_mono g]
  dsimp
  rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [IsOpenImmersion.isoOfRangeEq_inv_fac]; rw [← pullback.condition]; rw [morphismRestrict_ι]; rw [pullbackRestrictIsoRestrict_hom_ι_assoc]; rw [pullback.lift_fst_assoc]; rw [Category.comp_id]

/--
Definition of `morphismRestrictEq` / `morphismRestrictEq` 的定义

English:
definition morphismRestrictEq
  signature: {X Y : Scheme.{u}} (f : X ⟶ Y) {U V : Y.Opens} (e : U = V)
  body: eqToIso (by subst e; rfl)

@[reassoc]

中文:
定义 morphismRestrictEq
  签名: {X Y : 概形.{u}} (f : X ⟶ Y) {U V : Y.Opens} (e : U = V)
  定义体: eqToIso (by subst e; rfl)

@[reassoc]

Depends on / 依赖: eqToIso
-/
def morphismRestrictEq {X Y : Scheme.{u}} (f : X ⟶ Y) {U V : Y.Opens} (e : U = V) :
    Arrow.mk (f ∣_ U) ≅ Arrow.mk (f ∣_ V) :=
  eqToIso (by subst e; rfl)

@[reassoc]
/--
lemma `morphismRestrict_ι_image_ι_isoImage_inv` / 引理 `morphismRestrict_ι_image_ι_isoImage_inv`

English:
lemma morphismRestrict_ι_image_ι_isoImage_inv
  proof: by
  simp [← cancel_mono (Scheme.Opens.ι _)]

@[reassoc]

中文:
引理 morphismRestrict_ι_image_ι_isoImage_inv
  证明: by
  simp [← cancel_mono (Scheme.Opens.ι _)]

@[reassoc]

Depends on / 依赖: Scheme, Scheme.Opens, cancel_mono
-/
lemma morphismRestrict_ι_image_ι_isoImage_inv
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : U.toScheme.Opens) :
    f ∣_ U.ι ''ᵁ V ≫ (U.ι.isoImage V).inv = (X.homOfLE (image_morphismRestrict_preimage f U V).ge ≫
      ((f ⁻¹ᵁ U).ι.isoImage ((f ∣_ U) ⁻¹ᵁ V)).inv) ≫ f ∣_ U ∣_ V := by
  simp [← cancel_mono (Scheme.Opens.ι _)]

@[reassoc]
/--
lemma `morphismRestrict_morphismRestrict_ι_isoImage_hom` / 引理 `morphismRestrict_morphismRestrict_ι_isoImage_hom`

English:
lemma morphismRestrict_morphismRestrict_ι_isoImage_hom
  proof: by
  simp [← cancel_mono (Scheme.Opens.ι _)]

中文:
引理 morphismRestrict_morphismRestrict_ι_isoImage_hom
  证明: by
  simp [← cancel_mono (Scheme.Opens.ι _)]

Depends on / 依赖: Scheme, Scheme.Opens, cancel_mono
-/
lemma morphismRestrict_morphismRestrict_ι_isoImage_hom
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : U.toScheme.Opens) :
    f ∣_ U ∣_ V ≫ (U.ι.isoImage V).hom = (((f ⁻¹ᵁ U).ι.isoImage ((f ∣_ U) ⁻¹ᵁ V)).hom ≫
      X.homOfLE (image_morphismRestrict_preimage f U V).le) ≫ f ∣_ U.ι ''ᵁ V := by
  simp [← cancel_mono (Scheme.Opens.ι _)]

/--
Definition of `morphismRestrictRestrict` / `morphismRestrictRestrict` 的定义

English:
definition morphismRestrictRestrict
  signature: {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : U.toScheme.Opens)
  body: by
  refine Arrow.isoMk' _ _ ((Scheme.Opens.ι _).isoImage _ ≪≫ Scheme.isoOfEq _ ?_)
    ((Scheme.Opens.ι _).isoImage _) ?_
  · exact image_morphismRestrict_preimage f U V
  · simp [← cancel_mono (Scheme.Opens.ι _)]

中文:
定义 morphismRestrictRestrict
  签名: {X Y : 概形.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : U.toScheme.Opens)
  定义体: by
  refine Arrow.isoMk' _ _ ((Scheme.Opens.ι _).isoImage _ ≪≫ Scheme.isoOfEq _ ?_)
    ((Scheme.Opens.ι _).isoImage _) ?_
  · exact image_morphismRestrict_preimage f U V
  · simp [← cancel_mono (Scheme.Opens.ι _)]

Depends on / 依赖: Arrow.isoMk, Scheme, Scheme.Opens, Scheme.isoOfEq, cancel_mono, image_morphismRestrict_preimage, isoImage, isoOfEq
-/
def morphismRestrictRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : U.toScheme.Opens) :
    Arrow.mk (f ∣_ U ∣_ V) ≅ Arrow.mk (f ∣_ U.ι ''ᵁ V) := by
  refine Arrow.isoMk' _ _ ((Scheme.Opens.ι _).isoImage _ ≪≫ Scheme.isoOfEq _ ?_)
    ((Scheme.Opens.ι _).isoImage _) ?_
  · exact image_morphismRestrict_preimage f U V
  · simp [← cancel_mono (Scheme.Opens.ι _)]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `morphismRestrictRestrictBasicOpen` / `morphismRestrictRestrictBasicOpen` 的定义

English:
definition morphismRestrictRestrictBasicOpen
  signature: {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (r : Γ(Y, U))
  body: by
  refine morphismRestrictRestrict _ _ _ ≪≫ morphismRestrictEq _ ?_
  simp [Scheme.Opens.ι_image_basicOpen]

中文:
定义 morphismRestrictRestrictBasicOpen
  签名: {X Y : 概形.{u}} (f : X ⟶ Y) (U : Y.Opens) (r : Γ(Y, U))
  定义体: by
  refine morphismRestrictRestrict _ _ _ ≪≫ morphismRestrictEq _ ?_
  simp [Scheme.Opens.ι_image_basicOpen]

Depends on / 依赖: Scheme, Scheme.Opens, morphismRestrictEq, morphismRestrictRestrict
-/
def morphismRestrictRestrictBasicOpen {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (r : Γ(Y, U)) :
    Arrow.mk (f ∣_ U ∣_
          U.toScheme.basicOpen (Y.presheaf.map (eqToHom U.isOpenEmbedding_obj_top).op r)) ≅
      Arrow.mk (f ∣_ Y.basicOpen r) := by
  refine morphismRestrictRestrict _ _ _ ≪≫ morphismRestrictEq _ ?_
  simp [Scheme.Opens.ι_image_basicOpen]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `morphismRestrictStalkMap` / `morphismRestrictStalkMap` 的定义

English:
definition morphismRestrictStalkMap
  signature: {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (x)
  body: Arrow.isoMk' _ _
  (U.stalkIso ((f ∣_ U) x) ≪≫
    (TopCat.Presheaf.stalkCongr _ <| Inseparable.of_eq <| morphismRestrict_base_coe f U x))
((f ⁻¹ᵁ U).stalkIso x) TopCat.Presheaf.stalk_hom_ext _ fun V hxV => by
    simp [Scheme.Hom.germ_stalkMap_assoc, Scheme.Hom.appLE]

中文:
定义 morphismRestrictStalkMap
  签名: {X Y : 概形.{u}} (f : X ⟶ Y) (U : Y.Opens) (x)
  定义体: Arrow.isoMk' _ _
  (U.stalkIso ((f ∣_ U) x) ≪≫
    (TopCat.Presheaf.stalkCongr _ <| Inseparable.of_eq <| morphismRestrict_base_coe f U x))
((f ⁻¹ᵁ U).stalkIso x) TopCat.Presheaf.stalk_hom_ext _ fun V hxV => by
    simp [Scheme.Hom.germ_stalkMap_assoc, Scheme.Hom.appLE]

Depends on / 依赖: Arrow.isoMk
-/
def morphismRestrictStalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (x) :
    Arrow.mk ((f ∣_ U).stalkMap x) ≅ Arrow.mk (f.stalkMap x.1) := Arrow.isoMk' _ _
  (U.stalkIso ((f ∣_ U) x) ≪≫
    (TopCat.Presheaf.stalkCongr _ <| Inseparable.of_eq <| morphismRestrict_base_coe f U x))
((f ⁻¹ᵁ U).stalkIso x) TopCat.Presheaf.stalk_hom_ext _ fun V hxV => by
    simp [Scheme.Hom.germ_stalkMap_assoc, Scheme.Hom.appLE]

instance {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) [IsOpenImmersion f] :
    IsOpenImmersion (f ∣_ U) := by
  delta morphismRestrict
  exact PresheafedSpace.IsOpenImmersion.comp _ _

variable {X Y : Scheme.{u}}

namespace Scheme.Hom

/--
Definition of `resLE` / `resLE` 的定义

English:
definition resLE
  signature: (f : Hom X Y) (U : Y.Opens) (V : X.Opens) (e : V <= f ⁻¹ᵁ U)
  body: X.homOfLE e ≫ f ∣_ U

中文:
定义 resLE
  签名: (f : 态射 X Y) (U : Y.Opens) (V : X.Opens) (e : V <= f ⁻¹ᵁ U)
  定义体: X.homOfLE e ≫ f ∣_ U

Depends on / 依赖: X.homOfLE, homOfLE
-/
def resLE (f : Hom X Y) (U : Y.Opens) (V : X.Opens) (e : V <= f ⁻¹ᵁ U) : V.toScheme ⟶ U.toScheme :=
  X.homOfLE e ≫ f ∣_ U

variable (f : X ⟶ Y) {U U' : Y.Opens} {V V' : X.Opens} (e : V <= f ⁻¹ᵁ U)

/--
lemma `resLE_eq_morphismRestrict` / 引理 `resLE_eq_morphismRestrict`

English:
lemma resLE_eq_morphismRestrict
  statement: f.resLE U (f ⁻¹ᵁ U) le_rfl = f ∣_ U
  proof: by
  simp [resLE]

@[simp]

中文:
引理 resLE_eq_morphismRestrict
  结论: f.resLE U (f ⁻¹ᵁ U) le_rfl = f ∣_ U
  证明: by
  simp [resLE]

@[simp]
-/
lemma resLE_eq_morphismRestrict : f.resLE U (f ⁻¹ᵁ U) le_rfl = f ∣_ U := by
  simp [resLE]

@[simp]
/--
lemma `resLE_id` / 引理 `resLE_id`

English:
lemma resLE_id
  given: (i : V <= V')
  statement: resLE (𝟙 X) V' V i = X.homOfLE i
  proof: by
  simp only [resLE, morphismRestrict_id]
  rfl

@[reassoc (attr := simp)]

中文:
引理 resLE_id
  条件: (i : V <= V')
  结论: resLE (𝟙 X) V' V i = X.homOfLE i
  证明: by
  simp only [resLE, morphismRestrict_id]
  rfl

@[reassoc (attr := simp)]

Depends on / 依赖: morphismRestrict_id
-/
lemma resLE_id (i : V <= V') : resLE (𝟙 X) V' V i = X.homOfLE i := by
  simp only [resLE, morphismRestrict_id]
  rfl

@[reassoc (attr := simp)]
/--
lemma `resLE_comp_ι` / 引理 `resLE_comp_ι`

English:
lemma resLE_comp_ι
  statement: f.resLE U V e ≫ U.ι = V.ι ≫ f
  proof: by
  simp [resLE]

@[reassoc]

中文:
引理 resLE_comp_ι
  结论: f.resLE U V e ≫ U.ι = V.ι ≫ f
  证明: by
  simp [resLE]

@[reassoc]
-/
lemma resLE_comp_ι : f.resLE U V e ≫ U.ι = V.ι ≫ f := by
  simp [resLE]

@[reassoc]
/--
lemma `resLE_comp_resLE` / 引理 `resLE_comp_resLE`

English:
lemma resLE_comp_resLE
  given: {Z : Scheme.{u}} (g : Y ⟶ Z) {W : Z.Opens} (e')
  proof: by
  simp [← cancel_mono W.ι]

中文:
引理 resLE_comp_resLE
  条件: {Z : 概形.{u}} (g : Y ⟶ Z) {W : Z.Opens} (e')
  证明: by
  simp [← cancel_mono W.ι]

Depends on / 依赖: cancel_mono
-/
lemma resLE_comp_resLE {Z : Scheme.{u}} (g : Y ⟶ Z) {W : Z.Opens} (e') :
    f.resLE U V e ≫ g.resLE W U e' = (f ≫ g).resLE W V
      (e.trans ((Opens.map f.base).map (homOfLE e')).le) := by
  simp [← cancel_mono W.ι]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `map_resLE` / 引理 `map_resLE`

English:
lemma map_resLE
  given: (i : V' <= V)
  proof: by
  simp_rw [← resLE_id, resLE_comp_resLE, Category.id_comp]

中文:
引理 map_resLE
  条件: (i : V' <= V)
  证明: by
  simp_rw [← resLE_id, resLE_comp_resLE, Category.id_comp]

Depends on / 依赖: Category, Category.id_comp, id_comp, resLE_comp_resLE, resLE_id, simp_rw
-/
lemma map_resLE (i : V' <= V) :
    X.homOfLE i ≫ f.resLE U V e = f.resLE U V' (i.trans e) := by
  simp_rw [← resLE_id, resLE_comp_resLE, Category.id_comp]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `resLE_map` / 引理 `resLE_map`

English:
lemma resLE_map
  given: (i : U <= U')
  proof: by
  simp_rw [← resLE_id, resLE_comp_resLE, Category.comp_id]

中文:
引理 resLE_map
  条件: (i : U <= U')
  证明: by
  simp_rw [← resLE_id, resLE_comp_resLE, Category.comp_id]

Depends on / 依赖: Category, Category.comp_id, comp_id, resLE_comp_resLE, resLE_id, simp_rw
-/
lemma resLE_map (i : U <= U') :
    f.resLE U V e ≫ Y.homOfLE i =
      f.resLE U' V (e.trans ((Opens.map f.base).map i.hom).le) := by
  simp_rw [← resLE_id, resLE_comp_resLE, Category.comp_id]

/--
lemma `resLE_congr` / 引理 `resLE_congr`

English:
lemma resLE_congr
  given: (e₁ : U = U') (e₂ : V = V') (P : MorphismProperty Scheme.{u})
  proof: by
  subst e₁; subst e₂; rfl

中文:
引理 resLE_congr
  条件: (e₁ : U = U') (e₂ : V = V') (P : MorphismProperty 概形.{u})
  证明: by
  subst e₁; subst e₂; rfl
-/
lemma resLE_congr (e₁ : U = U') (e₂ : V = V') (P : MorphismProperty Scheme.{u}) :
    P (f.resLE U V e) ↔ P (f.resLE U' V' (e₁ ▸ e₂ ▸ e)) := by
  subst e₁; subst e₂; rfl

/--
lemma `resLE_preimage` / 引理 `resLE_preimage`

English:
lemma resLE_preimage
  statement: (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens} (e : V <= f ⁻¹ᵁ U)
  proof: by
  rw [← comp_preimage]; rw [← resLE_comp_ι f e]; rw [comp_preimage]; rw [preimage_image_eq]

中文:
引理 resLE_preimage
  结论: (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens} (e : V <= f ⁻¹ᵁ U)
  证明: by
  rw [← comp_preimage]; rw [← resLE_comp_ι f e]; rw [comp_preimage]; rw [preimage_image_eq]

Depends on / 依赖: comp_preimage, preimage_image_eq
-/
lemma resLE_preimage (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens} (e : V <= f ⁻¹ᵁ U)
    (O : U.toScheme.Opens) :
    f.resLE U V e ⁻¹ᵁ O = V.ι ⁻¹ᵁ (f ⁻¹ᵁ U.ι ''ᵁ O) := by
  rw [← comp_preimage]; rw [← resLE_comp_ι f e]; rw [comp_preimage]; rw [preimage_image_eq]

/--
lemma `le_resLE_preimage_iff` / 引理 `le_resLE_preimage_iff`

English:
lemma le_resLE_preimage_iff
  statement: {U : Y.Opens} {V : X.Opens} (e : V <= f ⁻¹ᵁ U)
  proof: by
  simp [resLE_preimage, ← image_le_image_iff V.ι, image_preimage_eq_opensRange_inf, V.ι_image_le]

中文:
引理 le_resLE_preimage_iff
  结论: {U : Y.Opens} {V : X.Opens} (e : V <= f ⁻¹ᵁ U)
  证明: by
  simp [resLE_preimage, ← image_le_image_iff V.ι, image_preimage_eq_opensRange_inf, V.ι_image_le]

Depends on / 依赖: image_le_image_iff, image_preimage_eq_opensRange_inf, resLE_preimage
-/
lemma le_resLE_preimage_iff {U : Y.Opens} {V : X.Opens} (e : V <= f ⁻¹ᵁ U)
    (O : U.toScheme.Opens) (W : V.toScheme.Opens) :
    W <= (f.resLE U V e) ⁻¹ᵁ O ↔ V.ι ''ᵁ W <= f ⁻¹ᵁ U.ι ''ᵁ O := by
  simp [resLE_preimage, ← image_le_image_iff V.ι, image_preimage_eq_opensRange_inf, V.ι_image_le]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `resLE_app_top` / 引理 `resLE_app_top`

English:
lemma resLE_app_top
  statement: (f.resLE U V e).app ⊤ =
  proof: by simp [Scheme.Hom.resLE]

中文:
引理 resLE_app_top
  结论: (f.resLE U V e).app ⊤ =
  证明: by simp [Scheme.Hom.resLE]
-/
@[simp] lemma resLE_app_top : (f.resLE U V e).app ⊤ =
    U.topIso.hom ≫ f.appLE U V e ≫ V.topIso.inv := by simp [Scheme.Hom.resLE]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `resLE_appLE` / 引理 `resLE_appLE`

English:
lemma resLE_appLE
  statement: {U : Y.Opens} {V : X.Opens} (e : V <= f ⁻¹ᵁ U)
  proof: by
  dsimp [appLE, resLE]
  simp only [morphismRestrict_app', appLE, homOfLE_leOfHom, homOfLE_app, Category.assoc]
  rw [← X.presheaf.map_comp]; rw [← X.presheaf.map_comp]
  rfl

中文:
引理 resLE_appLE
  结论: {U : Y.Opens} {V : X.Opens} (e : V <= f ⁻¹ᵁ U)
  证明: by
  dsimp [appLE, resLE]
  simp only [morphismRestrict_app', appLE, homOfLE_leOfHom, homOfLE_app, Category.assoc]
  rw [← X.presheaf.map_comp]; rw [← X.presheaf.map_comp]
  rfl

Depends on / 依赖: Category, Category.assoc, X.presheaf.map_comp, homOfLE_app, homOfLE_leOfHom, map_comp, morphismRestrict_app, presheaf
-/
lemma resLE_appLE {U : Y.Opens} {V : X.Opens} (e : V <= f ⁻¹ᵁ U)
    (O : U.toScheme.Opens) (W : V.toScheme.Opens) (e' : W <= resLE f U V e ⁻¹ᵁ O) :
    (f.resLE U V e).appLE O W e' =
      f.appLE (U.ι ''ᵁ O) (V.ι ''ᵁ W) ((le_resLE_preimage_iff f e O W).mp e') := by
  dsimp [appLE, resLE]
  simp only [morphismRestrict_app', appLE, homOfLE_leOfHom, homOfLE_app, Category.assoc]
  rw [← X.presheaf.map_comp]; rw [← X.presheaf.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `coe_resLE_apply` / 引理 `coe_resLE_apply`

English:
lemma coe_resLE_apply
  given: (x : V)
  statement: (f.resLE U V e x).1 = f x
  proof: by
  simp [resLE, morphismRestrict_base]

中文:
引理 coe_resLE_apply
  条件: (x : V)
  结论: (f.resLE U V e x).1 = f x
  证明: by
  simp [resLE, morphismRestrict_base]

Depends on / 依赖: morphismRestrict_base
-/
lemma coe_resLE_apply (x : V) : (f.resLE U V e x).1 = f x := by
  simp [resLE, morphismRestrict_base]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `resLEStalkMap` / `resLEStalkMap` 的定义

English:
definition resLEStalkMap
  signature: (x : V)
  body: Arrow.isoMk (U.stalkIso _ ≪≫
      (Y.presheaf.stalkCongr <| Inseparable.of_eq <| by simp)) (V.stalkIso x) <| by
    dsimp
    rw [Category.assoc]; rw [← Iso.eq_inv_comp]; rw [← Category.assoc]; rw [← Iso.comp_inv_eq]; rw [Opens.stalkIso_inv]; rw [Opens.stalkIso_inv]; rw [← stalkMap_comp]; rw [stalk

中文:
定义 resLEStalkMap
  签名: (x : V)
  定义体: Arrow.isoMk (U.stalkIso _ ≪≫
      (Y.presheaf.stalkCongr <| Inseparable.of_eq <| by simp)) (V.stalkIso x) <| by
    dsimp
    rw [Category.assoc]; rw [← Iso.eq_inv_comp]; rw [← Category.assoc]; rw [← Iso.comp_inv_eq]; rw [Opens.stalkIso_inv]; rw [Opens.stalkIso_inv]; rw [← stalkMap_comp]; rw [stalk

Depends on / 依赖: Arrow.isoMk, Category, Category.assoc, Inseparable, Inseparable.of_eq, Iso.comp_inv_eq, Iso.eq_inv_comp, Opens.stalkIso_inv, U.stalkIso, V.stalkIso, Y.presheaf.stalkCongr, comp_inv_eq, eq_inv_comp, of_eq, presheaf, stalkCongr, stalkIso, stalkIso_inv, stalkMap_comp, stalkMap_congr_hom
-/
def resLEStalkMap (x : V) :
    Arrow.mk ((f.resLE U V e).stalkMap x) ≅ Arrow.mk (f.stalkMap x) :=
  Arrow.isoMk (U.stalkIso _ ≪≫
      (Y.presheaf.stalkCongr <| Inseparable.of_eq <| by simp)) (V.stalkIso x) <| by
    dsimp
    rw [Category.assoc]; rw [← Iso.eq_inv_comp]; rw [← Category.assoc]; rw [← Iso.comp_inv_eq]; rw [Opens.stalkIso_inv]; rw [Opens.stalkIso_inv]; rw [← stalkMap_comp]; rw [stalkMap_congr_hom _ _ (resLE_comp_ι f e)]; rw [stalkMap_comp]
    simp

end Scheme.Hom

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `arrowResLEAppIso` / `arrowResLEAppIso` 的定义

English:
definition arrowResLEAppIso
  signature: (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (e : V <= f ⁻¹ᵁ U)
  body: Arrow.isoMk U.topIso V.topIso by
  simp only [Scheme.Opens.topIso_hom, eqToHom_op, Arrow.mk_hom, Scheme.Hom.map_appLE]
  rw [Scheme.Hom.appTop]; rw [← Scheme.Hom.appLE_eq_app]; rw [Scheme.Hom.resLE_appLE]; rw [Scheme.Hom.appLE_map]

中文:
定义 arrowResLEAppIso
  签名: (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (e : V <= f ⁻¹ᵁ U)
  定义体: Arrow.isoMk U.topIso V.topIso by
  simp only [Scheme.Opens.topIso_hom, eqToHom_op, Arrow.mk_hom, Scheme.Hom.map_appLE]
  rw [Scheme.Hom.appTop]; rw [← Scheme.Hom.appLE_eq_app]; rw [Scheme.Hom.resLE_appLE]; rw [Scheme.Hom.appLE_map]

Depends on / 依赖: Arrow.isoMk, Arrow.mk_hom, Scheme, Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_map, Scheme.Hom.appTop, Scheme.Hom.map_appLE, Scheme.Hom.resLE_appLE, Scheme.Opens.topIso_hom, U.topIso, V.topIso, appLE_eq_app, appLE_map, appTop, eqToHom_op, map_appLE, mk_hom, resLE_appLE, topIso, topIso_hom
-/
noncomputable def arrowResLEAppIso (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (e : V <= f ⁻¹ᵁ U) :
    Arrow.mk ((f.resLE U V e).appTop) ≅ Arrow.mk (f.appLE U V e) :=
Arrow.isoMk U.topIso V.topIso by
  simp only [Scheme.Opens.topIso_hom, eqToHom_op, Arrow.mk_hom, Scheme.Hom.map_appLE]
  rw [Scheme.Hom.appTop]; rw [← Scheme.Hom.appLE_eq_app]; rw [Scheme.Hom.resLE_appLE]; rw [Scheme.Hom.appLE_map]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `Scheme.Hom.isPullback_resLE` / 引理 `Scheme.Hom.isPullback_resLE`

English:
lemma Scheme.Hom.isPullback_resLE
  proof: by
  refine .paste_horiz (v₁₂ := iY.resLE _ _
    ((g.preimage_mono hUSX).trans_eq congr(($H.w) ⁻¹ᵁ US) :)) ?_ ?_
  · refine (IsOpenImmersion.isPullback _ _ _ _ (by simp) ?_).flip
    simp only [Scheme.opensRange_homOfLE, ← Scheme.Hom.comp_preimage, Scheme.Hom.resLE_comp_ι]
    rw [Scheme.Hom.comp_p

中文:
引理 概形.态射.isPullback_resLE
  证明: by
  refine .paste_horiz (v₁₂ := iY.resLE _ _
    ((g.preimage_mono hUSX).trans_eq congr(($H.w) ⁻¹ᵁ US) :)) ?_ ?_
  · refine (IsOpenImmersion.isPullback _ _ _ _ (by simp) ?_).flip
    simp only [Scheme.opensRange_homOfLE, ← Scheme.Hom.comp_preimage, Scheme.Hom.resLE_comp_ι]
    rw [Scheme.Hom.comp_p

Depends on / 依赖: IsOpenImmersion, IsOpenImmersion.isPullback, Scheme, Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.resLE_comp_, Scheme.Opens.opensRange_, Scheme.opensRange_homOfLE, comp_preimage, eq_iff, g.preimage_mono, iY.resLE, image_injective, image_injective.eq_iff, image_preimage_eq_opensRange_inf, isPullback, isPullback_morphismRestrict, of_bot, opensRange_homOfLE, paste_horiz
-/
lemma Scheme.Hom.isPullback_resLE
    {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {iX : X ⟶ S} {iY : Y ⟶ T}
    (H : IsPullback g iY iX f)
    {US : S.Opens} {UT : T.Opens}
    {UX : X.Opens} (hUST : UT <= f ⁻¹ᵁ US) (hUSX : UX <= iX ⁻¹ᵁ US)
    {UY : Y.Opens} (hUY : UY = g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) :
    IsPullback (g.resLE UX UY (by simp [*])) (iY.resLE UT UY (by simp [*]))
      (iX.resLE US UX hUSX) (f.resLE US UT hUST) := by
  refine .paste_horiz (v₁₂ := iY.resLE _ _
    ((g.preimage_mono hUSX).trans_eq congr(($H.w) ⁻¹ᵁ US) :)) ?_ ?_
  · refine (IsOpenImmersion.isPullback _ _ _ _ (by simp) ?_).flip
    simp only [Scheme.opensRange_homOfLE, ← Scheme.Hom.comp_preimage, Scheme.Hom.resLE_comp_ι]
    rw [Scheme.Hom.comp_preimage]; rw [← (g ⁻¹ᵁ UX).ι.image_injective.eq_iff]
    simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    simp [hUY]
  · refine .of_bot ?_ ?_ (isPullback_morphismRestrict f US)
    · simpa using (isPullback_morphismRestrict g UX).paste_vert H
    · simp [← cancel_mono US.ι, H.w]

end MorphismRestrict

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The restriction of an open cover to an open subset. -/
@[simps! I₀ X f]
noncomputable
/--
Definition of `Scheme.OpenCover.restrict` / `Scheme.OpenCover.restrict` 的定义

English:
definition Scheme.OpenCover.restrict
  signature: {X : Scheme.{u}} (𝒰 : Scheme.OpenCover.{v} X) (U : Opens X)
  body: by
  refine Cover.copy (𝒰.pullback₁ U.ι) 𝒰.I₀ _ (𝒰.f · ∣_ U) (Equiv.refl _)
    (fun i => IsOpenImmersion.isoOfRangeEq (Opens.ι _) (pullback.snd _ _) ?_) ?_
  · dsimp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
      PreZeroHypercover.pullback₁_I₀, Equiv.refl_apply, PreZeroHyperc

中文:
定义 概形.OpenCover.restrict
  签名: {X : 概形.{u}} (𝒰 : 概形.OpenCover.{v} X) (U : Opens X)
  定义体: by
  refine Cover.copy (𝒰.pullback₁ U.ι) 𝒰.I₀ _ (𝒰.f · ∣_ U) (Equiv.refl _)
    (fun i => IsOpenImmersion.isoOfRangeEq (Opens.ι _) (pullback.snd _ _) ?_) ?_
  · dsimp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
      PreZeroHypercover.pullback₁_I₀, Equiv.refl_apply, PreZeroHyperc

Depends on / 依赖: Category, Category.assoc, Cover.copy, Equiv.refl, Equiv.refl_apply, IsOpenImmersion, IsOpenImmersion.isoOfRangeEq, IsOpenImmersion.range_pullbackSnd, Opens.opensRange_, PreZeroHypercover, PreZeroHypercover.pullback, Precoverage, Precoverage.ZeroHypercover.pullback, Subtype, Subtype.range_val, ZeroHypercover, cancel_mono, isoOfRangeEq, pullback, pullback.snd
-/
def Scheme.OpenCover.restrict {X : Scheme.{u}} (𝒰 : Scheme.OpenCover.{v} X) (U : Opens X) :
    U.toScheme.OpenCover := by
  refine Cover.copy (𝒰.pullback₁ U.ι) 𝒰.I₀ _ (𝒰.f · ∣_ U) (Equiv.refl _)
    (fun i => IsOpenImmersion.isoOfRangeEq (Opens.ι _) (pullback.snd _ _) ?_) ?_
  · dsimp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
      PreZeroHypercover.pullback₁_I₀, Equiv.refl_apply, PreZeroHypercover.pullback₁_X]
    rw [IsOpenImmersion.range_pullbackSnd U.ι (𝒰.f i)]; rw [Opens.opensRange_ι]
    exact Subtype.range_val
  · intro i
    rw [← cancel_mono U.ι]
    simp [morphismRestrict_ι, Equiv.refl_apply, Category.assoc, pullback.condition]

end AlgebraicGeometry
