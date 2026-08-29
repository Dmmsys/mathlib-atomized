/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

/-!
# Open immersions of structured spaces

We say that a morphism of presheafed spaces `f : X ⟶ Y` is an open immersion if
the underlying map of spaces is an open embedding `f : X ⟶ U ⊆ Y`,
and the sheaf map `Y(V) ⟶ f _* X(V)` is an iso for each `V ⊆ U`.

Abbreviations are also provided for `SheafedSpace`, `LocallyRingedSpace` and `Scheme`.

## Main definitions

* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`: the `Prop`-valued typeclass asserting
  that a PresheafedSpace hom `f` is an open immersion.
* `AlgebraicGeometry.IsOpenImmersion`: the `Prop`-valued typeclass asserting
  that a Scheme morphism `f` is an open immersion.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoRestrict`: The source of an
  open immersion is isomorphic to the restriction of the target onto the image.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift`: Any morphism whose range is
  contained in an open immersion factors through the open immersion.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSheafedSpace`: If `f : X ⟶ Y` is an
  open immersion of presheafed spaces, and `Y` is a sheafed space, then `X` is also a sheafed
  space. The morphism as morphisms of sheafed spaces is given by `toSheafedSpaceHom`.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toLocallyRingedSpace`: If `f : X ⟶ Y` is
  an open immersion of presheafed spaces, and `Y` is a locally ringed space, then `X` is also a
  locally ringed space. The morphism as morphisms of locally ringed spaces is given by
  `toLocallyRingedSpaceHom`.

## Main results

* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.comp`: The composition of two open
  immersions is an open immersion.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofIso`: An iso is an open immersion.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.to_iso`:
  A surjective open immersion is an isomorphism.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.stalk_iso`: An open immersion induces
  an isomorphism on stalks.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.hasPullback_of_left`: If `f` is an open
  immersion, then the pullback `(f, g)` exists (and the forgetful functor to `TopCat` preserves it).
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackSndOfLeft`: Open immersions
  are stable under pullbacks.
* `AlgebraicGeometry.SheafedSpace.IsOpenImmersion.of_stalk_iso`: A (topological) open embedding
  between two sheafed spaces is an open immersion if all the stalk maps are isomorphisms.

-/

@[expose] public section


open TopologicalSpace CategoryTheory Opposite Topology

open CategoryTheory.Limits

namespace AlgebraicGeometry

universe w v v₁ v₂ u

variable {C : Type u} [Category.{v} C]

/--
Definition of `PresheafedSpace.IsOpenImmersion` / `PresheafedSpace.IsOpenImmersion` 的定义

English:
class PresheafedSpace.IsOpenImmersion
  parameters: {X Y : PresheafedSpace C} (f : X ⟶ Y)
  axioms and operations (2):
    - base_open : IsOpenEmbedding f.base
    - c_iso : forall U : Opens X, IsIso (f.c.app (op (base_open.functor.obj U)))

中文:
类 Presheafed空间.是开浸入
  参数: {X Y : Presheafed空间 C} (f : X ⟶ Y)
  公理与运算 (2 个):
    - base_open : 是开嵌入 f.base
    - c_iso : 对任意 U : Opens X, 是同构 (f.c.app (op (base_open.functor.obj U)))
-/
class PresheafedSpace.IsOpenImmersion {X Y : PresheafedSpace C} (f : X ⟶ Y) : Prop where
  /-- the underlying continuous map of underlying spaces from the source to an open subset of the
  target. -/
  base_open : IsOpenEmbedding f.base
  /-- the underlying sheaf morphism is an isomorphism on each open subset -/
  c_iso : forall U : Opens X, IsIso (f.c.app (op (base_open.functor.obj U)))

/--
Definition of `SheafedSpace.IsOpenImmersion` / `SheafedSpace.IsOpenImmersion` 的定义

English:
abbreviation SheafedSpace.IsOpenImmersion
  signature: {X Y : SheafedSpace C} (f : X ⟶ Y)
  body: PresheafedSpace.IsOpenImmersion f.hom

中文:
缩写 Sheafed空间.是开浸入
  签名: {X Y : Sheafed空间 C} (f : X ⟶ Y)
  定义体: PresheafedSpace.IsOpenImmersion f.hom

Depends on / 依赖: IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion, f.hom
-/
abbrev SheafedSpace.IsOpenImmersion {X Y : SheafedSpace C} (f : X ⟶ Y) : Prop :=
  PresheafedSpace.IsOpenImmersion f.hom

/--
lemma `SheafedSpace.isOpenImmersion_iff_hom` / 引理 `SheafedSpace.isOpenImmersion_iff_hom`

English:
lemma SheafedSpace.isOpenImmersion_iff_hom
  given: {X Y : SheafedSpace C} (f : X ⟶ Y)
  proof: Iff.rfl

中文:
引理 Sheafed空间.isOpenImmersion_iff_hom
  条件: {X Y : Sheafed空间 C} (f : X ⟶ Y)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma SheafedSpace.isOpenImmersion_iff_hom {X Y : SheafedSpace C} (f : X ⟶ Y) :
    SheafedSpace.IsOpenImmersion f ↔ PresheafedSpace.IsOpenImmersion f.hom := Iff.rfl

/--
Definition of `LocallyRingedSpace.IsOpenImmersion` / `LocallyRingedSpace.IsOpenImmersion` 的定义

English:
abbreviation LocallyRingedSpace.IsOpenImmersion
  signature: {X Y : LocallyRingedSpace} (f : X ⟶ Y)
  body: SheafedSpace.IsOpenImmersion f.toShHom

中文:
缩写 LocallyRinged空间.是开浸入
  签名: {X Y : LocallyRinged空间} (f : X ⟶ Y)
  定义体: SheafedSpace.IsOpenImmersion f.toShHom

Depends on / 依赖: IsOpenImmersion, SheafedSpace, SheafedSpace.IsOpenImmersion, f.toShHom, toShHom
-/
abbrev LocallyRingedSpace.IsOpenImmersion {X Y : LocallyRingedSpace} (f : X ⟶ Y) : Prop :=
  SheafedSpace.IsOpenImmersion f.toShHom

instance {X Y : LocallyRingedSpace} (f : X ⟶ Y) [LocallyRingedSpace.IsOpenImmersion f] :
    PresheafedSpace.IsOpenImmersion f.toHom := by assumption

namespace PresheafedSpace.IsOpenImmersion

open PresheafedSpace

local notation "IsOpenImmersion" => PresheafedSpace.IsOpenImmersion

attribute [instance] IsOpenImmersion.c_iso

section

variable {X Y : PresheafedSpace C} (f : X ⟶ Y) [H : IsOpenImmersion f]

/--
Definition of `opensFunctor` / `opensFunctor` 的定义

English:
abbreviation opensFunctor
  body: H.base_open.functor

中文:
缩写 opensFunctor
  定义体: H.base_open.functor

Depends on / 依赖: H.base_open.functor, base_open, functor
-/
abbrev opensFunctor :=
  H.base_open.functor

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An open immersion `f : X ⟶ Y` induces an isomorphism `X ≅ Y|_{f(X)}`. -/
@[simps! hom_c_app]
/--
Definition of `isoRestrict` / `isoRestrict` 的定义

English:
definition isoRestrict
  signature: : X ≅ Y.restrict H.base_open
  body: PresheafedSpace.isoOfComponents (Iso.refl _) by
    symm
    fapply NatIso.ofComponents
    · intro U
      refine asIso (f.c.app (op (opensFunctor f |>.obj (unop U)))) ≪≫ X.presheaf.mapIso (eqToIso ?_)
      induction U with | op U => ?_
      cases U
      dsimp only [IsOpenMap.functor, Functor.op

中文:
定义 isoRestrict
  签名: : X ≅ Y.restrict H.base_open
  定义体: PresheafedSpace.isoOfComponents (Iso.refl _) by
    symm
    fapply NatIso.ofComponents
    · intro U
      refine asIso (f.c.app (op (opensFunctor f |>.obj (unop U)))) ≪≫ X.presheaf.mapIso (eqToIso ?_)
      induction U with | op U => ?_
      cases U
      dsimp only [IsOpenMap.functor, Functor.op

Depends on / 依赖: Functor, Functor.op, H.base_open.injective, IsOpenMap, IsOpenMap.functor, Iso.refl, NatIso, NatIso.ofComponents, NatTrans, NatTrans.naturality_assoc, Opens.map_def, Presheaf, PresheafedSpace, PresheafedSpace.isoOfComponents, Quiver, Quiver.Hom.unop_op, Set.preimage_image_eq, TopCat, TopCat.Presheaf.pushforward_obj_map, TopCat.Presheaf.pushforward_obj_obj
-/
noncomputable def isoRestrict : X ≅ Y.restrict H.base_open :=
PresheafedSpace.isoOfComponents (Iso.refl _) by
    symm
    fapply NatIso.ofComponents
    · intro U
      refine asIso (f.c.app (op (opensFunctor f |>.obj (unop U)))) ≪≫ X.presheaf.mapIso (eqToIso ?_)
      induction U with | op U => ?_
      cases U
      dsimp only [IsOpenMap.functor, Functor.op, Opens.map_def]
      congr 2
      erw [Set.preimage_image_eq _ H.base_open.injective]
      rfl
    · intro U V i
      dsimp
      simp only [NatTrans.naturality_assoc, TopCat.Presheaf.pushforward_obj_obj,
        TopCat.Presheaf.pushforward_obj_map, Quiver.Hom.unop_op, Category.assoc]
      rw [← X.presheaf.map_comp]; rw [← X.presheaf.map_comp]
      congr 1

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `isoRestrict_hom_ofRestrict` / 定理 `isoRestrict_hom_ofRestrict`

English:
theorem isoRestrict_hom_ofRestrict
  statement: (isoRestrict f).hom ≫ Y.ofRestrict _ = f
  proof: by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` did not pick up `NatTrans.ext`
refine PresheafedSpace.Hom.ext _ _ rfl NatTrans.ext funext fun x => ?_
  simp only [eqToHom_refl,
    Functor.whiskerRight_id']
  erw [Category.comp_id, comp_c_app, f.c.naturali

中文:
定理 isoRestrict_hom_ofRestrict
  结论: (isoRestrict f).hom ≫ Y.ofRestrict _ = f
  证明: by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` did not pick up `NatTrans.ext`
refine PresheafedSpace.Hom.ext _ _ rfl NatTrans.ext funext fun x => ?_
  simp only [eqToHom_refl,
    Functor.whiskerRight_id']
  erw [Category.comp_id, comp_c_app, f.c.naturali
-/
theorem isoRestrict_hom_ofRestrict : (isoRestrict f).hom ≫ Y.ofRestrict _ = f := by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` did not pick up `NatTrans.ext`
refine PresheafedSpace.Hom.ext _ _ rfl NatTrans.ext funext fun x => ?_
  simp only [eqToHom_refl,
    Functor.whiskerRight_id']
  erw [Category.comp_id, comp_c_app, f.c.naturality_assoc, ← X.presheaf.map_comp]
  trans f.c.app x ≫ X.presheaf.map (𝟙 _)
  · congr 1
  · simp

@[reassoc (attr := simp)]
/--
theorem `isoRestrict_inv_ofRestrict` / 定理 `isoRestrict_inv_ofRestrict`

English:
theorem isoRestrict_inv_ofRestrict
  statement: (isoRestrict f).inv ≫ f = Y.ofRestrict _
  proof: by
  rw [Iso.inv_comp_eq]; rw [isoRestrict_hom_ofRestrict]

中文:
定理 isoRestrict_inv_ofRestrict
  结论: (isoRestrict f).inv ≫ f = Y.ofRestrict _
  证明: by
  rw [Iso.inv_comp_eq]; rw [isoRestrict_hom_ofRestrict]

Depends on / 依赖: Iso.inv_comp_eq, inv_comp_eq, isoRestrict_hom_ofRestrict
-/
theorem isoRestrict_inv_ofRestrict : (isoRestrict f).inv ≫ f = Y.ofRestrict _ := by
  rw [Iso.inv_comp_eq]; rw [isoRestrict_hom_ofRestrict]

/--
Instance `mono` / 实例 `mono`

English:
instance mono
  signature: : Mono f
  body: by
  rw [← H.isoRestrict_hom_ofRestrict]; apply mono_comp

中文:
实例 mono
  签名: : 单态射 f
  定义体: by
  rw [← H.isoRestrict_hom_ofRestrict]; apply mono_comp

Depends on / 依赖: H.isoRestrict_hom_ofRestrict, isoRestrict_hom_ofRestrict, mono_comp
-/
instance mono : Mono f := by
  rw [← H.isoRestrict_hom_ofRestrict]; apply mono_comp

/--
lemma `c_iso'` / 引理 `c_iso'`

English:
lemma c_iso'
  given: {V : Opens Y} (U : Opens X) (h : V = (opensFunctor f).obj U)
  proof: by
  subst h
  infer_instance

中文:
引理 c_iso'
  条件: {V : Opens Y} (U : Opens X) (h : V = (opensFunctor f).obj U)
  证明: by
  subst h
  infer_instance

Depends on / 依赖: infer_instance
-/
lemma c_iso' {V : Opens Y} (U : Opens X) (h : V = (opensFunctor f).obj U) :
    IsIso (f.c.app (Opposite.op V)) := by
  subst h
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/--
Instance `comp` / 实例 `comp`

English:
instance comp
  signature: {Z : PresheafedSpace C} (g : Y ⟶ Z) [hg : IsOpenImmersion g]
  body: hg.base_open.comp H.base_open
  c_iso U := by
    generalize_proofs h
    dsimp only [AlgebraicGeometry.PresheafedSpace.comp_c_app, unop_op, Functor.op, comp_base,
      Opens.map_comp_obj]
    apply IsIso.comp_isIso'
    · exact c_iso' g ((opensFunctor f).obj U) (by ext; simp)
    · apply c_iso' f 

中文:
实例 comp
  签名: {Z : Presheafed空间 C} (g : Y ⟶ Z) [hg : 是开浸入 g]
  定义体: hg.base_open.comp H.base_open
  c_iso U := by
    generalize_proofs h
    dsimp only [AlgebraicGeometry.PresheafedSpace.comp_c_app, unop_op, Functor.op, comp_base,
      Opens.map_comp_obj]
    apply IsIso.comp_isIso'
    · exact c_iso' g ((opensFunctor f).obj U) (by ext; simp)
    · apply c_iso' f 

Depends on / 依赖: H.base_open, base_open, hg.base_open.comp
-/
instance comp {Z : PresheafedSpace C} (g : Y ⟶ Z) [hg : IsOpenImmersion g] :
    IsOpenImmersion (f ≫ g) where
  base_open := hg.base_open.comp H.base_open
  c_iso U := by
    generalize_proofs h
    dsimp only [AlgebraicGeometry.PresheafedSpace.comp_c_app, unop_op, Functor.op, comp_base,
      Opens.map_comp_obj]
    apply IsIso.comp_isIso'
    · exact c_iso' g ((opensFunctor f).obj U) (by ext; simp)
    · apply c_iso' f U
      ext1
      dsimp only [Opens.map_coe, IsOpenMap.coe_functor_obj, comp_base, TopCat.coe_comp]
      rw [Set.image_comp]; rw [Set.preimage_image_eq _ hg.base_open.injective]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `invApp` / `invApp` 的定义

English:
definition invApp
  signature: (U : Opens X)
  body: X.presheaf.map (eqToHom (by simp [Opens.map_def, Set.preimage_image_eq _ H.base_open.injective]))
    ≫ inv (f.c.app (op (opensFunctor f |>.obj U)))

中文:
定义 invApp
  签名: (U : Opens X)
  定义体: X.presheaf.map (eqToHom (by simp [Opens.map_def, Set.preimage_image_eq _ H.base_open.injective]))
    ≫ inv (f.c.app (op (opensFunctor f |>.obj U)))

Depends on / 依赖: H.base_open.injective, Opens.map_def, Set.preimage_image_eq, X.presheaf.map, base_open, eqToHom, f.c.app, injective, map_def, opensFunctor, preimage_image_eq, presheaf
-/
noncomputable def invApp (U : Opens X) :
    X.presheaf.obj (op U) ⟶ Y.presheaf.obj (op (opensFunctor f |>.obj U)) :=
  X.presheaf.map (eqToHom (by simp [Opens.map_def, Set.preimage_image_eq _ H.base_open.injective]))
    ≫ inv (f.c.app (op (opensFunctor f |>.obj U)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/--
theorem `inv_naturality` / 定理 `inv_naturality`

English:
theorem inv_naturality
  given: {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
  proof: by
  simp only [invApp, ← Category.assoc]
  rw [IsIso.comp_inv_eq]
  simp only [Functor.op_obj, op_unop, ← X.presheaf.map_comp, Functor.op_map, Category.assoc,
    NatTrans.naturality, Quiver.Hom.unop_op, IsIso.inv_hom_id_assoc,
    TopCat.Presheaf.pushforward_obj_map]
  congr 1

中文:
定理 inv_naturality
  条件: {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
  证明: by
  simp only [invApp, ← Category.assoc]
  rw [IsIso.comp_inv_eq]
  simp only [Functor.op_obj, op_unop, ← X.presheaf.map_comp, Functor.op_map, Category.assoc,
    NatTrans.naturality, Quiver.Hom.unop_op, IsIso.inv_hom_id_assoc,
    TopCat.Presheaf.pushforward_obj_map]
  congr 1

Depends on / 依赖: Category, Category.assoc, Functor, Functor.op_map, Functor.op_obj, IsIso.comp_inv_eq, IsIso.inv_hom_id_assoc, NatTrans, NatTrans.naturality, Presheaf, Quiver, Quiver.Hom.unop_op, TopCat, TopCat.Presheaf.pushforward_obj_map, X.presheaf.map_comp, comp_inv_eq, invApp, inv_hom_id_assoc, map_comp, naturality
-/
theorem inv_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    X.presheaf.map i ≫ H.invApp _ (unop V) =
      invApp f (unop U) ≫ Y.presheaf.map (opensFunctor f |>.op.map i) := by
  simp only [invApp, ← Category.assoc]
  rw [IsIso.comp_inv_eq]
  simp only [Functor.op_obj, op_unop, ← X.presheaf.map_comp, Functor.op_map, Category.assoc,
    NatTrans.naturality, Quiver.Hom.unop_op, IsIso.inv_hom_id_assoc,
    TopCat.Presheaf.pushforward_obj_map]
  congr 1

set_option backward.isDefEq.respectTransparency.types false in
instance (U : Opens X) : IsIso (invApp f U) := by delta invApp; infer_instance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `inv_invApp` / 定理 `inv_invApp`

English:
theorem inv_invApp
  given: (U : Opens X)
  proof: by
  rw [← cancel_epi (H.invApp _ U)]; rw [IsIso.hom_inv_id]
  delta invApp
  simp [← Functor.map_comp]

中文:
定理 inv_invApp
  条件: (U : Opens X)
  证明: by
  rw [← cancel_epi (H.invApp _ U)]; rw [IsIso.hom_inv_id]
  delta invApp
  simp [← Functor.map_comp]

Depends on / 依赖: Functor, Functor.map_comp, H.invApp, IsIso.hom_inv_id, cancel_epi, hom_inv_id, invApp, map_comp
-/
theorem inv_invApp (U : Opens X) :
    inv (H.invApp _ U) =
      f.c.app (op (opensFunctor f |>.obj U)) ≫
        X.presheaf.map
          (eqToHom (by simp [Opens.map_def, Set.preimage_image_eq _ H.base_open.injective])) := by
  rw [← cancel_epi (H.invApp _ U)]; rw [IsIso.hom_inv_id]
  delta invApp
  simp [← Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc, elementwise]
/--
theorem `invApp_app` / 定理 `invApp_app`

English:
theorem invApp_app
  given: (U : Opens X)
  proof: by
  rw [invApp]; rw [Category.assoc]; rw [IsIso.inv_hom_id]; rw [Category.comp_id]

中文:
定理 invApp_app
  条件: (U : Opens X)
  证明: by
  rw [invApp]; rw [Category.assoc]; rw [IsIso.inv_hom_id]; rw [Category.comp_id]

Depends on / 依赖: Category, Category.assoc, Category.comp_id, IsIso.inv_hom_id, comp_id, invApp, inv_hom_id
-/
theorem invApp_app (U : Opens X) :
    invApp f U ≫ f.c.app (op (opensFunctor f |>.obj U)) = X.presheaf.map
      (eqToHom (by simp [Opens.map_def, Set.preimage_image_eq _ H.base_open.injective])) := by
  rw [invApp]; rw [Category.assoc]; rw [IsIso.inv_hom_id]; rw [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/--
theorem `app_invApp` / 定理 `app_invApp`

English:
theorem app_invApp
  given: (U : Opens Y)
  proof: by
  rw [invApp]; rw [← Category.assoc]; rw [IsIso.comp_inv_eq]; rw [f.c.naturality]
  congr

中文:
定理 app_invApp
  条件: (U : Opens Y)
  证明: by
  rw [invApp]; rw [← Category.assoc]; rw [IsIso.comp_inv_eq]; rw [f.c.naturality]
  congr

Depends on / 依赖: Category, Category.assoc, IsIso.comp_inv_eq, comp_inv_eq, f.c.naturality, invApp, naturality
-/
theorem app_invApp (U : Opens Y) :
    f.c.app (op U) ≫ H.invApp _ ((Opens.map f.base).obj U) =
      Y.presheaf.map
        ((homOfLE (Set.image_preimage_subset f.base U.1)).op :
          op U ⟶ op (opensFunctor f |>.obj ((Opens.map f.base).obj U))) := by
  rw [invApp]; rw [← Category.assoc]; rw [IsIso.comp_inv_eq]; rw [f.c.naturality]
  congr

/-- A variant of `app_inv_app` that gives an `eqToHom` instead of `homOfLe`. -/
@[reassoc]
/--
theorem `app_inv_app'` / 定理 `app_inv_app'`

English:
theorem app_inv_app'
  given: (U : Opens Y) (hU : (U : Set Y) subseteq Set.range f.base)
  proof: by
  simp only [app_invApp, Opens.carrier_eq_coe,
    homOfLE_leOfHom, eqToHom_op]
  tauto

中文:
定理 app_inv_app'
  条件: (U : Opens Y) (hU : (U : 集合 Y) subseteq 集合.range f.base)
  证明: by
  simp only [app_invApp, Opens.carrier_eq_coe,
    homOfLE_leOfHom, eqToHom_op]
  tauto

Depends on / 依赖: f.base
-/
theorem app_inv_app' (U : Opens Y) (hU : (U : Set Y) subseteq Set.range f.base) :
    f.c.app (op U) ≫ invApp f ((Opens.map f.base).obj U) =
      Y.presheaf.map
        (eqToHom
            (le_antisymm (Set.image_preimage_subset f.base U.1) <|
              (Set.image_preimage_eq_inter_range (f := f.base) (t := U.1)).symm ▸
                Set.subset_inter_iff.mpr ⟨fun _ h => h, hU⟩)).op := by
  simp only [app_invApp, Opens.carrier_eq_coe,
    homOfLE_leOfHom, eqToHom_op]
  tauto

set_option backward.isDefEq.respectTransparency false in
/--
Instance `ofIso` / 实例 `ofIso`

English:
instance ofIso
  signature: {X Y : PresheafedSpace C} (H : X ≅ Y)
  body: (TopCat.homeoOfIso ((forget C).mapIso H)).isOpenEmbedding
  -- Porting note: `inferInstance` will fail if Lean is not told that `H.hom.c` is iso
  c_iso _ := letI : IsIso H.hom.c := inferInstance;
    inferInstance

中文:
实例 ofIso
  签名: {X Y : Presheafed空间 C} (H : X ≅ Y)
  定义体: (TopCat.homeoOfIso ((forget C).mapIso H)).isOpenEmbedding
  -- Porting note: `inferInstance` will fail if Lean is not told that `H.hom.c` is iso
  c_iso _ := letI : IsIso H.hom.c := inferInstance;
    inferInstance

Depends on / 依赖: TopCat, TopCat.homeoOfIso, forget, homeoOfIso, isOpenEmbedding, mapIso
-/
instance ofIso {X Y : PresheafedSpace C} (H : X ≅ Y) : IsOpenImmersion H.hom where
  base_open := (TopCat.homeoOfIso ((forget C).mapIso H)).isOpenEmbedding
  -- Porting note: `inferInstance` will fail if Lean is not told that `H.hom.c` is iso
  c_iso _ := letI : IsIso H.hom.c := inferInstance;
    inferInstance

instance (priority := 100) ofIsIso {X Y : PresheafedSpace C} (f : X ⟶ Y) [IsIso f] :
    IsOpenImmersion f :=
  AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofIso (asIso f)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `ofRestrict` / 实例 `ofRestrict`

English:
instance ofRestrict
  signature: {X : TopCat} (Y : PresheafedSpace C) {f : X ⟶ Y.carrier}
  body: hf
  c_iso U := by
    dsimp
    have : (Opens.map f).obj (hf.functor.obj U) = U := by
      ext1
      exact Set.preimage_image_eq _ hf.injective
    convert_to IsIso (Y.presheaf.map (𝟙 _))
    · congr
    · -- Porting note: was `apply Subsingleton.helim; rw [this]`
      -- See https://github.com/

中文:
实例 ofRestrict
  签名: {X : 顶元素范畴} (Y : Presheafed空间 C) {f : X ⟶ Y.carrier}
  定义体: hf
  c_iso U := by
    dsimp
    have : (Opens.map f).obj (hf.functor.obj U) = U := by
      ext1
      exact Set.preimage_image_eq _ hf.injective
    convert_to IsIso (Y.presheaf.map (𝟙 _))
    · congr
    · -- Porting note: was `apply Subsingleton.helim; rw [this]`
      -- See https://github.com/

Depends on / 依赖: IsStablyFiniteRing, OrzechProperty
-/
instance ofRestrict {X : TopCat} (Y : PresheafedSpace C) {f : X ⟶ Y.carrier}
    (hf : IsOpenEmbedding f) : IsOpenImmersion (Y.ofRestrict hf) where
  base_open := hf
  c_iso U := by
    dsimp
    have : (Opens.map f).obj (hf.functor.obj U) = U := by
      ext1
      exact Set.preimage_image_eq _ hf.injective
    convert_to IsIso (Y.presheaf.map (𝟙 _))
    · congr
    · -- Porting note: was `apply Subsingleton.helim; rw [this]`
      -- See https://github.com/leanprover/lean4/issues/2273
      congr
      · simp only
        congr
      apply Subsingleton.helim
      rw [this]
    · infer_instance

set_option backward.isDefEq.respectTransparency false in
@[elementwise, simp]
/--
theorem `ofRestrict_invApp` / 定理 `ofRestrict_invApp`

English:
theorem ofRestrict_invApp
  statement: {C : Type*} [Category* C] (X : PresheafedSpace C) {Y : TopCat.{w}}
  proof: by
  delta invApp
  rw [IsIso.comp_inv_eq]; rw [Category.id_comp]
  change X.presheaf.map _ = X.presheaf.map _
  congr 1

中文:
定理 ofRestrict_invApp
  结论: {C : 类型} [范畴* C] (X : Presheafed空间 C) {Y : 顶元素范畴.{w}}
  证明: by
  delta invApp
  rw [IsIso.comp_inv_eq]; rw [Category.id_comp]
  change X.presheaf.map _ = X.presheaf.map _
  congr 1

Depends on / 依赖: Category, Category.id_comp, IsIso.comp_inv_eq, IsStablyFiniteRing, Nontrivial, RankCondition, X.presheaf.map, comp_inv_eq, id_comp, invApp, presheaf
-/
theorem ofRestrict_invApp {C : Type*} [Category* C] (X : PresheafedSpace C) {Y : TopCat.{w}}
    {f : Y ⟶ TopCat.of X.carrier} (h : IsOpenEmbedding f) (U : Opens (X.restrict h).carrier) :
    (PresheafedSpace.IsOpenImmersion.ofRestrict X h).invApp _ U = 𝟙 _ := by
  delta invApp
  rw [IsIso.comp_inv_eq]; rw [Category.id_comp]
  change X.presheaf.map _ = X.presheaf.map _
  congr 1

/--
theorem `to_iso` / 定理 `to_iso`

English:
theorem to_iso
  given: [h' : Epi f.base]
  statement: IsIso f
  proof: by
  have : forall (U : (Opens Y)ᵒᵖ), IsIso (f.c.app U) := by
    intro U
    have : U = op (opensFunctor f |>.obj ((Opens.map f.base).obj (unop U))) := by
      induction U with | op U => ?_
      cases U
      dsimp only [Functor.op, Opens.map]
      congr
      exact (Set.image_preimage_eq _ ((To

中文:
定理 to_iso
  条件: [h' : 满态射 f.base]
  结论: 是同构 f
  证明: by
  have : forall (U : (Opens Y)ᵒᵖ), IsIso (f.c.app U) := by
    intro U
    have : U = op (opensFunctor f |>.obj ((Opens.map f.base).obj (unop U))) := by
      induction U with | op U => ?_
      cases U
      dsimp only [Functor.op, Opens.map]
      congr
      exact (Set.image_preimage_eq _ ((To

Depends on / 依赖: Functor, Functor.op, H.base_open.isEmbedding.toHomeomorp, H.c_iso, NatIso, NatIso.isIso_of_isIso_app, Opens.map, Set.image_preimage_eq, TopCat, TopCat.epi_iff_surjective, allowSynthFailures, base_open, c_iso, convert, epi_iff_surjective, f.base, f.c.app, image_preimage_eq, isEmbedding, isIso_of_components
-/
theorem to_iso [h' : Epi f.base] : IsIso f := by
  have : forall (U : (Opens Y)ᵒᵖ), IsIso (f.c.app U) := by
    intro U
    have : U = op (opensFunctor f |>.obj ((Opens.map f.base).obj (unop U))) := by
      induction U with | op U => ?_
      cases U
      dsimp only [Functor.op, Opens.map]
      congr
      exact (Set.image_preimage_eq _ ((TopCat.epi_iff_surjective _).mp h')).symm
    convert! H.c_iso (Opens.map f.base |>.obj <| unop U)
  have : IsIso f.c := NatIso.isIso_of_isIso_app _
  apply +allowSynthFailures isIso_of_components
  let t : X ≃ₜ Y := H.base_open.isEmbedding.toHomeomorph.trans
    { toFun := Subtype.val
      invFun := fun x =>
        ⟨x, by rw [Set.range_eq_univ.mpr ((TopCat.epi_iff_surjective _).mp h')]; trivial⟩ }
  exact (TopCat.isoOfHomeo t).isIso_hom

set_option backward.isDefEq.respectTransparency false in
/--
Instance `stalk_iso` / 实例 `stalk_iso`

English:
instance stalk_iso
  signature: [HasColimits C] (x : X)
  body: by
  rw [← H.isoRestrict_hom_ofRestrict]; rw [PresheafedSpace.stalkMap.comp]
  infer_instance

中文:
实例 stalk_iso
  签名: [有余极限 C] (x : X)
  定义体: by
  rw [← H.isoRestrict_hom_ofRestrict]; rw [PresheafedSpace.stalkMap.comp]
  infer_instance

Depends on / 依赖: H.isoRestrict_hom_ofRestrict, PresheafedSpace, PresheafedSpace.stalkMap.comp, infer_instance, isoRestrict_hom_ofRestrict, stalkMap
-/
instance stalk_iso [HasColimits C] (x : X) : IsIso (f.stalkMap x) := by
  rw [← H.isoRestrict_hom_ofRestrict]; rw [PresheafedSpace.stalkMap.comp]
  infer_instance

end

noncomputable section Pullback

variable {X Y Z : PresheafedSpace C} (f : X ⟶ Z) [hf : IsOpenImmersion f] (g : Y ⟶ Z)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `pullbackConeOfLeftFst` / `pullbackConeOfLeftFst` 的定义

English:
definition pullbackConeOfLeftFst
  signature: :
  body: pullback.fst _ _
  c :=
    { app := fun U =>
        hf.invApp _ (unop U) ≫
          g.c.app (op (hf.base_open.functor.obj (unop U))) ≫
            Y.presheaf.map
              (eqToHom
                (by
                  simp only [IsOpenMap.functor, op_inj_iff, Opens.map,
                    F

中文:
定义 pullbackConeOfLeftFst
  签名: :
  定义体: pullback.fst _ _
  c :=
    { app := fun U =>
        hf.invApp _ (unop U) ≫
          g.c.app (op (hf.base_open.functor.obj (unop U))) ≫
            Y.presheaf.map
              (eqToHom
                (by
                  simp only [IsOpenMap.functor, op_inj_iff, Opens.map,
                    F

Depends on / 依赖: pullback, pullback.fst
-/
def pullbackConeOfLeftFst :
    Y.restrict (TopCat.snd_isOpenEmbedding_of_left hf.base_open g.base) ⟶ X where
  base := pullback.fst _ _
  c :=
    { app := fun U =>
        hf.invApp _ (unop U) ≫
          g.c.app (op (hf.base_open.functor.obj (unop U))) ≫
            Y.presheaf.map
              (eqToHom
                (by
                  simp only [IsOpenMap.functor, op_inj_iff, Opens.map,
                    Functor.op_obj]
                  apply LE.le.antisymm
                  · rintro _ ⟨_, h₁, h₂⟩
                    use (TopCat.pullbackIsoProdSubtype _ _).inv ⟨⟨_, _⟩, h₂⟩
                    simpa [(TopCat.pullbackIsoProdSubtype_inv_fst_apply),
                      (TopCat.pullbackIsoProdSubtype_inv_snd_apply)]
                  · rintro _ ⟨x, h₁, rfl⟩
                    exact ⟨_, h₁, CategoryTheory.congr_fun pullback.condition x⟩))
      naturality := by
        intro U V i
        induction U
        induction V
        simp only [(inv_naturality_assoc), restrict_carrier, restrict_presheaf,
          TopCat.Presheaf.pushforward_obj_obj, Functor.comp_obj, Functor.op_obj,
          TopCat.Presheaf.pushforward_obj_map, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op,
          NatTrans.naturality_assoc, TopCat.Presheaf.pushforward_obj_map, Quiver.Hom.unop_op,
          ← Functor.map_comp, Category.assoc]
        rfl }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `pullback_cone_of_left_condition` / 定理 `pullback_cone_of_left_condition`

English:
theorem pullback_cone_of_left_condition
  statement: pullbackConeOfLeftFst f g ≫ f = Y.ofRestrict _ ≫ g
  proof: by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` did not pick up `NatTrans.ext`
refine PresheafedSpace.Hom.ext _ _ ?_ NatTrans.ext funext fun U => ?_
  · simpa using! pullback.condition
  · induction U
    simp only [(NatTrans.comp_app), comp_c_app, unop_op

中文:
定理 pullback_cone_of_left_condition
  结论: pullbackConeOfLeftFst f g ≫ f = Y.ofRestrict _ ≫ g
  证明: by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` did not pick up `NatTrans.ext`
refine PresheafedSpace.Hom.ext _ _ ?_ NatTrans.ext funext fun U => ?_
  · simpa using! pullback.condition
  · induction U
    simp only [(NatTrans.comp_app), comp_c_app, unop_op
-/
theorem pullback_cone_of_left_condition : pullbackConeOfLeftFst f g ≫ f = Y.ofRestrict _ ≫ g := by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` did not pick up `NatTrans.ext`
refine PresheafedSpace.Hom.ext _ _ ?_ NatTrans.ext funext fun U => ?_
  · simpa using! pullback.condition
  · induction U
    simp only [(NatTrans.comp_app), comp_c_app, unop_op, Functor.whiskerRight_app,
      pullbackConeOfLeftFst, app_invApp_assoc, eqToHom_app, Category.assoc,
      NatTrans.naturality_assoc, restrict_carrier, comp_base, ofRestrict_base, restrict_presheaf,
      Functor.comp_obj, Functor.op_obj, Opens.map_comp_obj, TopCat.Presheaf.pushforward_obj_obj,
      Opens.carrier_eq_coe, homOfLE_leOfHom, TopCat.Presheaf.pushforward_obj_map, Functor.comp_map,
      Functor.op_map, eqToHom_unop, ofRestrict_c_app, Functor.id_obj]
    rw [← Y.presheaf.map_comp]; rw [← Y.presheaf.map_comp]
    congr 1

/--
Definition of `pullbackConeOfLeft` / `pullbackConeOfLeft` 的定义

English:
definition pullbackConeOfLeft
  signature: : PullbackCone f g
  body: PullbackCone.mk (pullbackConeOfLeftFst f g) (Y.ofRestrict _)
    (pullback_cone_of_left_condition f g)

中文:
定义 pullbackConeOfLeft
  签名: : PullbackCone f g
  定义体: PullbackCone.mk (pullbackConeOfLeftFst f g) (Y.ofRestrict _)
    (pullback_cone_of_left_condition f g)

Depends on / 依赖: PullbackCone, PullbackCone.mk, Y.ofRestrict, ofRestrict, pullbackConeOfLeftFst, pullback_cone_of_left_condition
-/
def pullbackConeOfLeft : PullbackCone f g :=
  PullbackCone.mk (pullbackConeOfLeftFst f g) (Y.ofRestrict _)
    (pullback_cone_of_left_condition f g)

variable (s : PullbackCone f g)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `pullbackConeOfLeftLift` / `pullbackConeOfLeftLift` 的定义

English:
definition pullbackConeOfLeftLift
  signature: : s.pt ⟶ (pullbackConeOfLeft f g).pt where
  body: pullback.lift s.fst.base s.snd.base
      (congr_arg (fun x => PresheafedSpace.Hom.base x) s.condition)
  c :=
    { app := fun U =>
        s.snd.c.app _ ≫
          s.pt.presheaf.map
            (eqToHom
              (by
                dsimp only [Opens.map_def, IsOpenMap.functor, Functor.op]
  

中文:
定义 pullbackConeOfLeftLift
  签名: : s.pt ⟶ (pullbackConeOfLeft f g).pt where
  定义体: pullback.lift s.fst.base s.snd.base
      (congr_arg (fun x => PresheafedSpace.Hom.base x) s.condition)
  c :=
    { app := fun U =>
        s.snd.c.app _ ≫
          s.pt.presheaf.map
            (eqToHom
              (by
                dsimp only [Opens.map_def, IsOpenMap.functor, Functor.op]
  

Depends on / 依赖: Function, Function.comp_def, Functor, Functor.op, Hom.base, IsOpenMap, IsOpenMap.functor, Opens.map_def, PresheafedSpace, PresheafedSpace.Hom.base, PullbackCone, PullbackCone.mk, Set.preimage_preimage, WalkingCospan, WalkingCospan.right, comp_def, condition, congr_arg, conv_lhs, eqToHom
-/
def pullbackConeOfLeftLift : s.pt ⟶ (pullbackConeOfLeft f g).pt where
  base :=
    pullback.lift s.fst.base s.snd.base
      (congr_arg (fun x => PresheafedSpace.Hom.base x) s.condition)
  c :=
    { app := fun U =>
        s.snd.c.app _ ≫
          s.pt.presheaf.map
            (eqToHom
              (by
                dsimp only [Opens.map_def, IsOpenMap.functor, Functor.op]
                congr 2
                let s' : PullbackCone f.base g.base :=
                  PullbackCone.mk s.fst.base s.snd.base (congr_arg Hom.base s.condition)
                have : _ = s.snd.base := limit.lift_π s' WalkingCospan.right
                conv_lhs =>
                  rw [← this]
                  dsimp [s']
                  rw [Function.comp_def]; rw [← Set.preimage_preimage]
                rw [Set.preimage_image_eq _
                    (TopCat.snd_isOpenEmbedding_of_left hf.base_open g.base).injective]
                rfl))
      naturality := fun U V i => by
        erw [s.snd.c.naturality_assoc]
        rw [Category.assoc]
        erw [← s.pt.presheaf.map_comp, ← s.pt.presheaf.map_comp]
        congr 1 }

set_option backward.isDefEq.respectTransparency false in
-- this lemma is not a `simp` lemma, because it is an implementation detail
/--
theorem `pullbackConeOfLeftLift_fst` / 定理 `pullbackConeOfLeftLift_fst`

English:
theorem pullbackConeOfLeftLift_fst
  proof: by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` did not pick up `NatTrans.ext`
refine PresheafedSpace.Hom.ext _ _ ?_ NatTrans.ext funext fun x => ?_
  · change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
    simp
  · induction x with | op x => ?_
    change

中文:
定理 pullbackConeOfLeftLift_fst
  证明: by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` did not pick up `NatTrans.ext`
refine PresheafedSpace.Hom.ext _ _ ?_ NatTrans.ext funext fun x => ?_
  · change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
    simp
  · induction x with | op x => ?_
    change

Depends on / 依赖: rankCondition_of_nontrivial_of_commSemiring
-/
theorem pullbackConeOfLeftLift_fst :
    pullbackConeOfLeftLift f g s ≫ (pullbackConeOfLeft f g).fst = s.fst := by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` did not pick up `NatTrans.ext`
refine PresheafedSpace.Hom.ext _ _ ?_ NatTrans.ext funext fun x => ?_
  · change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
    simp
  · induction x with | op x => ?_
    change ((_ ≫ _) ≫ _ ≫ _) ≫ _ = _
    simp_rw [Category.assoc]
    erw [← s.pt.presheaf.map_comp]
    erw [s.snd.c.naturality_assoc]
    have := congr_app s.condition (op (opensFunctor f |>.obj x))
    dsimp only [comp_c_app, unop_op] at this
    rw [← IsIso.comp_inv_eq] at this
    replace this := reassoc_of% this
    erw [← this, hf.invApp_app_assoc, s.fst.c.naturality_assoc]
    simp [eqToHom_map]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- this lemma is not a `simp` lemma, because it is an implementation detail
/--
theorem `pullbackConeOfLeftLift_snd` / 定理 `pullbackConeOfLeftLift_snd`

English:
theorem pullbackConeOfLeftLift_snd
  proof: by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` did not pick up `NatTrans.ext`
refine PresheafedSpace.Hom.ext _ _ ?_ NatTrans.ext funext fun x => ?_
  · change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
    simp
  · change (_ ≫ _ ≫ _) ≫ _ = _
    simp_rw [

中文:
定理 pullbackConeOfLeftLift_snd
  证明: by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` did not pick up `NatTrans.ext`
refine PresheafedSpace.Hom.ext _ _ ?_ NatTrans.ext funext fun x => ?_
  · change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
    simp
  · change (_ ≫ _ ≫ _) ≫ _ = _
    simp_rw [
-/
theorem pullbackConeOfLeftLift_snd :
    pullbackConeOfLeftLift f g s ≫ (pullbackConeOfLeft f g).snd = s.snd := by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` did not pick up `NatTrans.ext`
refine PresheafedSpace.Hom.ext _ _ ?_ NatTrans.ext funext fun x => ?_
  · change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
    simp
  · change (_ ≫ _ ≫ _) ≫ _ = _
    simp_rw [Category.assoc]
    erw [s.snd.c.naturality_assoc]
    erw [← s.pt.presheaf.map_comp, ← s.pt.presheaf.map_comp]
    trans s.snd.c.app x ≫ s.pt.presheaf.map (𝟙 _)
    · congr 1
    · simp

set_option backward.isDefEq.respectTransparency false in
/--
Instance `pullbackConeSndIsOpenImmersion` / 实例 `pullbackConeSndIsOpenImmersion`

English:
instance pullbackConeSndIsOpenImmersion
  signature: : IsOpenImmersion (pullbackConeOfLeft f g).snd
  body: by
  erw [CategoryTheory.Limits.PullbackCone.mk_snd]
  infer_instance

中文:
实例 pullbackConeSndIsOpenImmersion
  签名: : 是开浸入 (pullbackConeOfLeft f g).snd
  定义体: by
  erw [CategoryTheory.Limits.PullbackCone.mk_snd]
  infer_instance

Depends on / 依赖: CategoryTheory, CategoryTheory.Limits.PullbackCone.mk_snd, Limits, PullbackCone, infer_instance, mk_snd
-/
instance pullbackConeSndIsOpenImmersion : IsOpenImmersion (pullbackConeOfLeft f g).snd := by
  erw [CategoryTheory.Limits.PullbackCone.mk_snd]
  infer_instance

/--
Definition of `pullbackConeOfLeftIsLimit` / `pullbackConeOfLeftIsLimit` 的定义

English:
definition pullbackConeOfLeftIsLimit
  signature: : IsLimit (pullbackConeOfLeft f g)
  body: by
  apply PullbackCone.isLimitAux'
  intro s
  use pullbackConeOfLeftLift f g s
  use pullbackConeOfLeftLift_fst f g s
  use pullbackConeOfLeftLift_snd f g s
  intro m _ h₂
  rw [← cancel_mono (pullbackConeOfLeft f g).snd]
  exact h₂.trans (pullbackConeOfLeftLift_snd f g s).symm

中文:
定义 pullbackConeOfLeftIsLimit
  签名: : 是极限 (pullbackConeOfLeft f g)
  定义体: by
  apply PullbackCone.isLimitAux'
  intro s
  use pullbackConeOfLeftLift f g s
  use pullbackConeOfLeftLift_fst f g s
  use pullbackConeOfLeftLift_snd f g s
  intro m _ h₂
  rw [← cancel_mono (pullbackConeOfLeft f g).snd]
  exact h₂.trans (pullbackConeOfLeftLift_snd f g s).symm

Depends on / 依赖: PullbackCone, PullbackCone.isLimitAux, cancel_mono, isLimitAux, pullbackConeOfLeft, pullbackConeOfLeftLift, pullbackConeOfLeftLift_fst, pullbackConeOfLeftLift_snd
-/
def pullbackConeOfLeftIsLimit : IsLimit (pullbackConeOfLeft f g) := by
  apply PullbackCone.isLimitAux'
  intro s
  use pullbackConeOfLeftLift f g s
  use pullbackConeOfLeftLift_fst f g s
  use pullbackConeOfLeftLift_snd f g s
  intro m _ h₂
  rw [← cancel_mono (pullbackConeOfLeft f g).snd]
  exact h₂.trans (pullbackConeOfLeftLift_snd f g s).symm

/--
Instance `hasPullback_of_left` / 实例 `hasPullback_of_left`

English:
instance hasPullback_of_left
  signature: : HasPullback f g
  body: ⟨⟨⟨_, pullbackConeOfLeftIsLimit f g⟩⟩⟩

中文:
实例 hasPullback_of_left
  签名: : HasPullback f g
  定义体: ⟨⟨⟨_, pullbackConeOfLeftIsLimit f g⟩⟩⟩

Depends on / 依赖: pullbackConeOfLeftIsLimit
-/
instance hasPullback_of_left : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfLeftIsLimit f g⟩⟩⟩

/--
Instance `hasPullback_of_right` / 实例 `hasPullback_of_right`

English:
instance hasPullback_of_right
  signature: : HasPullback g f
  body: hasPullback_symmetry f g

中文:
实例 hasPullback_of_right
  签名: : HasPullback g f
  定义体: hasPullback_symmetry f g

Depends on / 依赖: hasPullback_symmetry
-/
instance hasPullback_of_right : HasPullback g f :=
  hasPullback_symmetry f g

set_option backward.isDefEq.respectTransparency false in
/--
Instance `pullbackSndOfLeft` / 实例 `pullbackSndOfLeft`

English:
instance pullbackSndOfLeft
  signature: : IsOpenImmersion (pullback.snd f g)
  body: by
  delta pullback.snd
  rw [← limit.isoLimitCone_hom_π ⟨_]; rw [pullbackConeOfLeftIsLimit f g⟩ WalkingCospan.right]
  infer_instance

中文:
实例 pullbackSndOfLeft
  签名: : 是开浸入 (pullback.snd f g)
  定义体: by
  delta pullback.snd
  rw [← limit.isoLimitCone_hom_π ⟨_]; rw [pullbackConeOfLeftIsLimit f g⟩ WalkingCospan.right]
  infer_instance

Depends on / 依赖: WalkingCospan, WalkingCospan.right, infer_instance, limit.isoLimitCone_hom_, pullback, pullback.snd, pullbackConeOfLeftIsLimit
-/
instance pullbackSndOfLeft : IsOpenImmersion (pullback.snd f g) := by
  delta pullback.snd
  rw [← limit.isoLimitCone_hom_π ⟨_]; rw [pullbackConeOfLeftIsLimit f g⟩ WalkingCospan.right]
  infer_instance

/--
Instance `pullbackFstOfRight` / 实例 `pullbackFstOfRight`

English:
instance pullbackFstOfRight
  signature: : IsOpenImmersion (pullback.fst g f)
  body: by
  rw [← pullbackSymmetry_hom_comp_snd]
  infer_instance

中文:
实例 pullbackFstOfRight
  签名: : 是开浸入 (pullback.fst g f)
  定义体: by
  rw [← pullbackSymmetry_hom_comp_snd]
  infer_instance

Depends on / 依赖: infer_instance, pullbackSymmetry_hom_comp_snd
-/
instance pullbackFstOfRight : IsOpenImmersion (pullback.fst g f) := by
  rw [← pullbackSymmetry_hom_comp_snd]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Instance `pullbackToBaseIsOpenImmersion` / 实例 `pullbackToBaseIsOpenImmersion`

English:
instance pullbackToBaseIsOpenImmersion
  signature: [IsOpenImmersion g]
  body: by
  rw [← limit.w (cospan f g) WalkingCospan.Hom.inl]; rw [cospan_map_inl]
  infer_instance

中文:
实例 pullbackToBaseIsOpenImmersion
  签名: [是开浸入 g]
  定义体: by
  rw [← limit.w (cospan f g) WalkingCospan.Hom.inl]; rw [cospan_map_inl]
  infer_instance

Depends on / 依赖: WalkingCospan, WalkingCospan.Hom.inl, cospan, cospan_map_inl, infer_instance, limit.w
-/
instance pullbackToBaseIsOpenImmersion [IsOpenImmersion g] :
    IsOpenImmersion (limit.π (cospan f g) WalkingCospan.one) := by
  rw [← limit.w (cospan f g) WalkingCospan.Hom.inl]; rw [cospan_map_inl]
  infer_instance

/--
Instance `forget_preservesLimitsOfLeft` / 实例 `forget_preservesLimitsOfLeft`

English:
instance forget_preservesLimitsOfLeft
  signature: : PreservesLimit (cospan f g) (forget C)
  body: preservesLimit_of_preserves_limit_cone (pullbackConeOfLeftIsLimit f g)
    (by
      apply (IsLimit.postcomposeHomEquiv (diagramIsoCospan _) _).toFun
      refine (IsLimit.equivIsoLimit ?_).toFun (limit.isLimit (cospan f.base g.base))
      fapply Cone.ext
      · exact Iso.refl _
      change foral

中文:
实例 forget_preservesLimitsOfLeft
  签名: : 保持极限 (cospan f g) (forget C)
  定义体: preservesLimit_of_preserves_limit_cone (pullbackConeOfLeftIsLimit f g)
    (by
      apply (IsLimit.postcomposeHomEquiv (diagramIsoCospan _) _).toFun
      refine (IsLimit.equivIsoLimit ?_).toFun (limit.isLimit (cospan f.base g.base))
      fapply Cone.ext
      · exact Iso.refl _
      change foral

Depends on / 依赖: Category, Category.id_comp, Cone.ext, Functor, Functor.comp_map, Functor.mapCone_, IsLimit, IsLimit.equivIsoLimit, IsLimit.postcomposeHomEquiv, Iso.refl, PullbackCone, PullbackCone.condition_one, comp_base, comp_map, condition_one, cone_x, cospan, cospan_left, cospan_one, cospan_right
-/
instance forget_preservesLimitsOfLeft : PreservesLimit (cospan f g) (forget C) :=
  preservesLimit_of_preserves_limit_cone (pullbackConeOfLeftIsLimit f g)
    (by
      apply (IsLimit.postcomposeHomEquiv (diagramIsoCospan _) _).toFun
      refine (IsLimit.equivIsoLimit ?_).toFun (limit.isLimit (cospan f.base g.base))
      fapply Cone.ext
      · exact Iso.refl _
      change forall j, _ = 𝟙 _ ≫ _ ≫ _
      simp_rw [Category.id_comp]
      rintro (_ | _ | _) <;> symm
      · simp only [limit.cone_x, cospan_one, Functor.mapCone_π_app, PullbackCone.condition_one,
        forget_map,
          comp_base, cospan_left, cospan_right, Functor.comp_map, cospan_map_inl, cospan_map_inr,
          diagramIsoCospan_hom_app, PullbackCone.fst_limit_cone]
        tauto
      · exact Category.comp_id _
      · exact Category.comp_id _)

/--
Instance `forget_preservesLimitsOfRight` / 实例 `forget_preservesLimitsOfRight`

English:
instance forget_preservesLimitsOfRight
  signature: : PreservesLimit (cospan g f) (forget C)
  body: preservesPullback_symmetry (forget C) f g

中文:
实例 forget_preservesLimitsOfRight
  签名: : 保持极限 (cospan g f) (forget C)
  定义体: preservesPullback_symmetry (forget C) f g

Depends on / 依赖: forget, preservesPullback_symmetry
-/
instance forget_preservesLimitsOfRight : PreservesLimit (cospan g f) (forget C) :=
  preservesPullback_symmetry (forget C) f g

set_option backward.isDefEq.respectTransparency false in
/--
theorem `pullback_snd_isIso_of_range_subset` / 定理 `pullback_snd_isIso_of_range_subset`

English:
theorem pullback_snd_isIso_of_range_subset
  given: (H : Set.range g.base subseteq Set.range f.base)
  proof: by
  have := TopCat.snd_iso_of_left_embedding_range_subset hf.base_open.isEmbedding g.base H
  have : IsIso (pullback.snd f g).base := by
    delta pullback.snd
    rw [← limit.isoLimitCone_hom_π ⟨_]; rw [pullbackConeOfLeftIsLimit f g⟩ WalkingCospan.right]
    change IsIso (_ ≫ pullback.snd _ _)
   

中文:
定理 pullback_snd_isIso_of_range_subset
  条件: (H : 集合.range g.base subseteq 集合.range f.base)
  证明: by
  have := TopCat.snd_iso_of_left_embedding_range_subset hf.base_open.isEmbedding g.base H
  have : IsIso (pullback.snd f g).base := by
    delta pullback.snd
    rw [← limit.isoLimitCone_hom_π ⟨_]; rw [pullbackConeOfLeftIsLimit f g⟩ WalkingCospan.right]
    change IsIso (_ ≫ pullback.snd _ _)
   

Depends on / 依赖: TopCat, TopCat.snd_iso_of_left_embedding_range_subset, WalkingCospan, WalkingCospan.right, base_open, g.base, hf.base_open.isEmbedding, infer_instance, isEmbedding, limit.isoLimitCone_hom_, pullback, pullback.snd, pullbackConeOfLeftIsLimit, snd_iso_of_left_embedding_range_subset, to_iso
-/
theorem pullback_snd_isIso_of_range_subset (H : Set.range g.base subseteq Set.range f.base) :
    IsIso (pullback.snd f g) := by
  have := TopCat.snd_iso_of_left_embedding_range_subset hf.base_open.isEmbedding g.base H
  have : IsIso (pullback.snd f g).base := by
    delta pullback.snd
    rw [← limit.isoLimitCone_hom_π ⟨_]; rw [pullbackConeOfLeftIsLimit f g⟩ WalkingCospan.right]
    change IsIso (_ ≫ pullback.snd _ _)
    infer_instance
  apply to_iso

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (H : Set.range g.base subseteq Set.range f.base)
  body: haveI := pullback_snd_isIso_of_range_subset f g H
  inv (pullback.snd f g) ≫ pullback.fst _ _

@[simp, reassoc]

中文:
定义 lift
  签名: (H : 集合.range g.base subseteq 集合.range f.base)
  定义体: haveI := pullback_snd_isIso_of_range_subset f g H
  inv (pullback.snd f g) ≫ pullback.fst _ _

@[simp, reassoc]

Depends on / 依赖: pullback, pullback.fst, pullback.snd, pullback_snd_isIso_of_range_subset
-/
def lift (H : Set.range g.base subseteq Set.range f.base) : Y ⟶ X :=
  haveI := pullback_snd_isIso_of_range_subset f g H
  inv (pullback.snd f g) ≫ pullback.fst _ _

@[simp, reassoc]
/--
theorem `lift_fac` / 定理 `lift_fac`

English:
theorem lift_fac
  given: (H : Set.range g.base subseteq Set.range f.base)
  statement: lift f g H ≫ f = g
  proof: by
  simp [AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift,
    CategoryTheory.Limits.pullback.condition]

中文:
定理 lift_fac
  条件: (H : 集合.range g.base subseteq 集合.range f.base)
  结论: lift f g H ≫ f = g
  证明: by
  simp [AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift,
    CategoryTheory.Limits.pullback.condition]

Depends on / 依赖: AlgebraicGeometry, AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift, CategoryTheory, CategoryTheory.Limits.pullback.condition, IsOpenImmersion, Limits, PresheafedSpace, condition, pullback
-/
theorem lift_fac (H : Set.range g.base subseteq Set.range f.base) : lift f g H ≫ f = g := by
  simp [AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift,
    CategoryTheory.Limits.pullback.condition]

/--
theorem `lift_uniq` / 定理 `lift_uniq`

English:
theorem lift_uniq
  given: (H : Set.range g.base subseteq Set.range f.base) (l : Y ⟶ X) (hl : l ≫ f = g)
  proof: by rw [← cancel_mono f, hl, lift_fac]

中文:
定理 lift_uniq
  条件: (H : 集合.range g.base subseteq 集合.range f.base) (l : Y ⟶ X) (hl : l ≫ f = g)
  证明: by rw [← cancel_mono f, hl, lift_fac]

Depends on / 依赖: cancel_mono, lift_fac
-/
theorem lift_uniq (H : Set.range g.base subseteq Set.range f.base) (l : Y ⟶ X) (hl : l ≫ f = g) :
    l = lift f g H := by rw [← cancel_mono f, hl, lift_fac]

/-- Two open immersions with equal range is isomorphic. -/
@[simps]
/--
Definition of `isoOfRangeEq` / `isoOfRangeEq` 的定义

English:
definition isoOfRangeEq
  signature: [IsOpenImmersion g] (e : Set.range f.base = Set.range g.base)
  body: lift g f (le_of_eq e)
  inv := lift f g (le_of_eq e.symm)
  hom_inv_id := by rw [← cancel_mono f]; simp
  inv_hom_id := by rw [← cancel_mono g]; simp

中文:
定义 isoOfRangeEq
  签名: [是开浸入 g] (e : 集合.range f.base = 集合.range g.base)
  定义体: lift g f (le_of_eq e)
  inv := lift f g (le_of_eq e.symm)
  hom_inv_id := by rw [← cancel_mono f]; simp
  inv_hom_id := by rw [← cancel_mono g]; simp

Depends on / 依赖: le_of_eq
-/
def isoOfRangeEq [IsOpenImmersion g] (e : Set.range f.base = Set.range g.base) : X ≅ Y where
  hom := lift g f (le_of_eq e)
  inv := lift f g (le_of_eq e.symm)
  hom_inv_id := by rw [← cancel_mono f]; simp
  inv_hom_id := by rw [← cancel_mono g]; simp

end Pullback

open CategoryTheory.Limits.WalkingCospan

section ToSheafedSpace

variable {X : PresheafedSpace C} (Y : SheafedSpace C)

/--
Definition of `toSheafedSpace` / `toSheafedSpace` 的定义

English:
definition toSheafedSpace
  signature: (f : X ⟶ Y.toPresheafedSpace) [H : IsOpenImmersion f]
  body: by
    apply TopCat.Presheaf.isSheaf_of_iso (sheafIsoOfIso (isoRestrict f).symm).symm
    apply TopCat.Sheaf.pushforward_sheaf_of_sheaf
    exact (Y.restrict H.base_open).IsSheaf
  toPresheafedSpace := X

中文:
定义 toSheafedSpace
  签名: (f : X ⟶ Y.toPresheafedSpace) [H : 是开浸入 f]
  定义体: by
    apply TopCat.Presheaf.isSheaf_of_iso (sheafIsoOfIso (isoRestrict f).symm).symm
    apply TopCat.Sheaf.pushforward_sheaf_of_sheaf
    exact (Y.restrict H.base_open).IsSheaf
  toPresheafedSpace := X

Depends on / 依赖: H.base_open, IsSheaf, Presheaf, TopCat, TopCat.Presheaf.isSheaf_of_iso, TopCat.Sheaf.pushforward_sheaf_of_sheaf, Y.restrict, base_open, isSheaf_of_iso, isoRestrict, pushforward_sheaf_of_sheaf, restrict, sheafIsoOfIso, toPresheafedSpace
-/
def toSheafedSpace (f : X ⟶ Y.toPresheafedSpace) [H : IsOpenImmersion f] : SheafedSpace C where
  IsSheaf := by
    apply TopCat.Presheaf.isSheaf_of_iso (sheafIsoOfIso (isoRestrict f).symm).symm
    apply TopCat.Sheaf.pushforward_sheaf_of_sheaf
    exact (Y.restrict H.base_open).IsSheaf
  toPresheafedSpace := X

variable (f : X ⟶ Y.toPresheafedSpace) [H : IsOpenImmersion f]

@[simp]
/--
theorem `toSheafedSpace_toPresheafedSpace` / 定理 `toSheafedSpace_toPresheafedSpace`

English:
theorem toSheafedSpace_toPresheafedSpace
  statement: (toSheafedSpace Y f).toPresheafedSpace = X
  proof: rfl

中文:
定理 toSheafedSpace_toPresheafedSpace
  结论: (toSheafedSpace Y f).toPresheafedSpace = X
  证明: rfl
-/
theorem toSheafedSpace_toPresheafedSpace : (toSheafedSpace Y f).toPresheafedSpace = X :=
  rfl

/--
Definition of `toSheafedSpaceHom` / `toSheafedSpaceHom` 的定义

English:
definition toSheafedSpaceHom
  signature: : toSheafedSpace Y f ⟶ Y
  body: InducedCategory.homMk f

@[simp]

中文:
定义 toSheafedSpaceHom
  签名: : toSheafedSpace Y f ⟶ Y
  定义体: InducedCategory.homMk f

@[simp]

Depends on / 依赖: InducedCategory, InducedCategory.homMk
-/
def toSheafedSpaceHom : toSheafedSpace Y f ⟶ Y :=
  InducedCategory.homMk f

@[simp]
/--
theorem `toSheafedSpaceHom_hom_base` / 定理 `toSheafedSpaceHom_hom_base`

English:
theorem toSheafedSpaceHom_hom_base
  statement: (toSheafedSpaceHom Y f).hom.base = f.base
  proof: rfl

@[simp]

中文:
定理 toSheafedSpaceHom_hom_base
  结论: (toSheafedSpaceHom Y f).hom.base = f.base
  证明: rfl

@[simp]
-/
theorem toSheafedSpaceHom_hom_base : (toSheafedSpaceHom Y f).hom.base = f.base :=
  rfl

@[simp]
/--
theorem `toSheafedSpaceHom_hom_c` / 定理 `toSheafedSpaceHom_hom_c`

English:
theorem toSheafedSpaceHom_hom_c
  statement: (toSheafedSpaceHom Y f).hom.c = f.c
  proof: rfl

中文:
定理 toSheafedSpaceHom_hom_c
  结论: (toSheafedSpaceHom Y f).hom.c = f.c
  证明: rfl
-/
theorem toSheafedSpaceHom_hom_c : (toSheafedSpaceHom Y f).hom.c = f.c :=
  rfl

/--
Instance `toSheafedSpace_isOpenImmersion` / 实例 `toSheafedSpace_isOpenImmersion`

English:
instance toSheafedSpace_isOpenImmersion
  signature: : SheafedSpace.IsOpenImmersion (toSheafedSpaceHom Y f)
  body: H

@[simp]

中文:
实例 toSheafedSpace_isOpenImmersion
  签名: : Sheafed空间.是开浸入 (toSheafedSpaceHom Y f)
  定义体: H

@[simp]
-/
instance toSheafedSpace_isOpenImmersion : SheafedSpace.IsOpenImmersion (toSheafedSpaceHom Y f) :=
  H

@[simp]
/--
theorem `sheafedSpace_toSheafedSpace` / 定理 `sheafedSpace_toSheafedSpace`

English:
theorem sheafedSpace_toSheafedSpace
  statement: {X Y : SheafedSpace C} (f : X ⟶ Y)
  proof: by cases X; rfl

中文:
定理 sheafedSpace_toSheafedSpace
  结论: {X Y : Sheafed空间 C} (f : X ⟶ Y)
  证明: by cases X; rfl
-/
theorem sheafedSpace_toSheafedSpace {X Y : SheafedSpace C} (f : X ⟶ Y)
    [SheafedSpace.IsOpenImmersion f] :
    toSheafedSpace Y f.hom = X := by cases X; rfl

end ToSheafedSpace

section ToLocallyRingedSpace

variable {X : PresheafedSpace CommRingCat} (Y : LocallyRingedSpace)
variable (f : X ⟶ Y.toPresheafedSpace) [H : IsOpenImmersion f]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `toLocallyRingedSpace` / `toLocallyRingedSpace` 的定义

English:
definition toLocallyRingedSpace
  signature: : LocallyRingedSpace where
  body: toSheafedSpace Y.toSheafedSpace f
  isLocalRing x :=
    haveI : IsLocalRing (Y.presheaf.stalk (f.base x)) := Y.isLocalRing _
    (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.isLocalRing

@[simp]

中文:
定义 toLocallyRingedSpace
  签名: : LocallyRinged空间 where
  定义体: toSheafedSpace Y.toSheafedSpace f
  isLocalRing x :=
    haveI : IsLocalRing (Y.presheaf.stalk (f.base x)) := Y.isLocalRing _
    (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.isLocalRing

@[simp]

Depends on / 依赖: Y.toSheafedSpace, toSheafedSpace
-/
def toLocallyRingedSpace : LocallyRingedSpace where
  toSheafedSpace := toSheafedSpace Y.toSheafedSpace f
  isLocalRing x :=
    haveI : IsLocalRing (Y.presheaf.stalk (f.base x)) := Y.isLocalRing _
    (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.isLocalRing

@[simp]
/--
theorem `toLocallyRingedSpace_toSheafedSpace` / 定理 `toLocallyRingedSpace_toSheafedSpace`

English:
theorem toLocallyRingedSpace_toSheafedSpace
  proof: rfl

中文:
定理 toLocallyRingedSpace_toSheafedSpace
  证明: rfl
-/
theorem toLocallyRingedSpace_toSheafedSpace :
    (toLocallyRingedSpace Y f).toSheafedSpace = toSheafedSpace Y.1 f :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `toLocallyRingedSpaceHom` / `toLocallyRingedSpaceHom` 的定义

English:
definition toLocallyRingedSpaceHom
  signature: : toLocallyRingedSpace Y f ⟶ Y
  body: ⟨f, fun _ => inferInstance⟩

@[simp]

中文:
定义 toLocallyRingedSpaceHom
  签名: : toLocallyRingedSpace Y f ⟶ Y
  定义体: ⟨f, fun _ => inferInstance⟩

@[simp]
-/
def toLocallyRingedSpaceHom : toLocallyRingedSpace Y f ⟶ Y :=
  ⟨f, fun _ => inferInstance⟩

@[simp]
/--
theorem `toLocallyRingedSpaceHom_val` / 定理 `toLocallyRingedSpaceHom_val`

English:
theorem toLocallyRingedSpaceHom_val
  proof: rfl

中文:
定理 toLocallyRingedSpaceHom_val
  证明: rfl
-/
theorem toLocallyRingedSpaceHom_val :
    (toLocallyRingedSpaceHom Y f).toShHom = InducedCategory.homMk f :=
  rfl

/--
Instance `toLocallyRingedSpace_isOpenImmersion` / 实例 `toLocallyRingedSpace_isOpenImmersion`

English:
instance toLocallyRingedSpace_isOpenImmersion
  signature: :
  body: H

@[simp]

中文:
实例 toLocallyRingedSpace_isOpenImmersion
  签名: :
  定义体: H

@[simp]
-/
instance toLocallyRingedSpace_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (toLocallyRingedSpaceHom Y f) :=
  H

@[simp]
/--
theorem `locallyRingedSpace_toLocallyRingedSpace` / 定理 `locallyRingedSpace_toLocallyRingedSpace`

English:
theorem locallyRingedSpace_toLocallyRingedSpace
  statement: {X Y : LocallyRingedSpace} (f : X ⟶ Y)
  proof: rfl

中文:
定理 locallyRingedSpace_toLocallyRingedSpace
  结论: {X Y : LocallyRinged空间} (f : X ⟶ Y)
  证明: rfl
-/
theorem locallyRingedSpace_toLocallyRingedSpace {X Y : LocallyRingedSpace} (f : X ⟶ Y)
    [LocallyRingedSpace.IsOpenImmersion f] : toLocallyRingedSpace Y f.toHom = X :=
  rfl

end ToLocallyRingedSpace

/--
theorem `isIso_of_subset` / 定理 `isIso_of_subset`

English:
theorem isIso_of_subset
  statement: {X Y : PresheafedSpace C} (f : X ⟶ Y)
  proof: by
  have : U = H.base_open.functor.obj ((Opens.map f.base).obj U) := by
    ext1
    exact (Set.inter_eq_left.mpr hU).symm.trans Set.image_preimage_eq_inter_range.symm
  convert! H.c_iso ((Opens.map f.base).obj U)

中文:
定理 isIso_of_subset
  结论: {X Y : Presheafed空间 C} (f : X ⟶ Y)
  证明: by
  have : U = H.base_open.functor.obj ((Opens.map f.base).obj U) := by
    ext1
    exact (Set.inter_eq_left.mpr hU).symm.trans Set.image_preimage_eq_inter_range.symm
  convert! H.c_iso ((Opens.map f.base).obj U)

Depends on / 依赖: H.base_open.functor.obj, H.c_iso, Opens.map, Set.image_preimage_eq_inter_range.symm, Set.inter_eq_left.mpr, base_open, c_iso, convert, f.base, functor, image_preimage_eq_inter_range, inter_eq_left, symm.trans
-/
theorem isIso_of_subset {X Y : PresheafedSpace C} (f : X ⟶ Y)
    [H : PresheafedSpace.IsOpenImmersion f] (U : Opens Y.carrier)
    (hU : (U : Set Y.carrier) subseteq Set.range f.base) : IsIso (f.c.app <| op U) := by
  have : U = H.base_open.functor.obj ((Opens.map f.base).obj U) := by
    ext1
    exact (Set.inter_eq_left.mpr hU).symm.trans Set.image_preimage_eq_inter_range.symm
  convert! H.c_iso ((Opens.map f.base).obj U)

end PresheafedSpace.IsOpenImmersion

namespace SheafedSpace.IsOpenImmersion

instance (priority := 100) of_isIso {X Y : SheafedSpace C} (f : X ⟶ Y) [IsIso f] :
    SheafedSpace.IsOpenImmersion f :=
  @PresheafedSpace.IsOpenImmersion.ofIsIso _ _ _ _ f.hom
    (SheafedSpace.forgetToPresheafedSpace.map_isIso _)

/--
Instance `comp` / 实例 `comp`

English:
instance comp
  signature: {X Y Z : SheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) [SheafedSpace.IsOpenImmersion f]
  body: PresheafedSpace.IsOpenImmersion.comp f.hom g.hom

noncomputable section Pullback

中文:
实例 comp
  签名: {X Y Z : Sheafed空间 C} (f : X ⟶ Y) (g : Y ⟶ Z) [Sheafed空间.是开浸入 f]
  定义体: PresheafedSpace.IsOpenImmersion.comp f.hom g.hom

noncomputable section Pullback

Depends on / 依赖: IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.comp, f.hom, g.hom
-/
instance comp {X Y Z : SheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) [SheafedSpace.IsOpenImmersion f]
    [SheafedSpace.IsOpenImmersion g] : SheafedSpace.IsOpenImmersion (f ≫ g) :=
  PresheafedSpace.IsOpenImmersion.comp f.hom g.hom

noncomputable section Pullback

variable {X Y Z : SheafedSpace C} (f : X ⟶ Z) (g : Y ⟶ Z)
variable [H : SheafedSpace.IsOpenImmersion f]

/-- This is often wrapped in parentheses to distinguish with the forgetful functor. -/
local notation "forget" => SheafedSpace.forgetToPresheafedSpace

open CategoryTheory.Limits.WalkingCospan

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono f
  body: (forget).mono_of_mono_map (show @Mono (PresheafedSpace C) _ _ _ f.hom by infer_instance)

中文:
实例 :
  签名: 单态射 f
  定义体: (forget).mono_of_mono_map (show @Mono (PresheafedSpace C) _ _ _ f.hom by infer_instance)

Depends on / 依赖: PresheafedSpace, f.hom, forget, infer_instance, mono_of_mono_map
-/
instance : Mono f :=
  (forget).mono_of_mono_map (show @Mono (PresheafedSpace C) _ _ _ f.hom by infer_instance)

/--
Instance `forgetMapIsOpenImmersion` / 实例 `forgetMapIsOpenImmersion`

English:
instance forgetMapIsOpenImmersion
  signature: : PresheafedSpace.IsOpenImmersion ((forget).map f)
  body: ⟨H.base_open, H.c_iso⟩

中文:
实例 forgetMapIsOpenImmersion
  签名: : Presheafed空间.是开浸入 ((forget).map f)
  定义体: ⟨H.base_open, H.c_iso⟩

Depends on / 依赖: H.base_open, H.c_iso, base_open, c_iso
-/
instance forgetMapIsOpenImmersion : PresheafedSpace.IsOpenImmersion ((forget).map f) :=
  ⟨H.base_open, H.c_iso⟩

/--
Instance `hasLimit_cospan_forget_of_left` / 实例 `hasLimit_cospan_forget_of_left`

English:
instance hasLimit_cospan_forget_of_left
  signature: : HasLimit (cospan f g ⋙ forget)
  body: by
  have : HasLimit (cospan ((cospan f g ⋙ forget).map Hom.inl)
      ((cospan f g ⋙ forget).map Hom.inr)) := by
    change HasLimit (cospan ((forget).map f) ((forget).map g))
    infer_instance
  apply hasLimit_of_iso (diagramIsoCospan _).symm

中文:
实例 hasLimit_cospan_forget_of_left
  签名: : 有极限 (cospan f g ⋙ forget)
  定义体: by
  have : HasLimit (cospan ((cospan f g ⋙ forget).map Hom.inl)
      ((cospan f g ⋙ forget).map Hom.inr)) := by
    change HasLimit (cospan ((forget).map f) ((forget).map g))
    infer_instance
  apply hasLimit_of_iso (diagramIsoCospan _).symm

Depends on / 依赖: HasLimit, Hom.inl, Hom.inr, cospan, diagramIsoCospan, forget, hasLimit_of_iso, infer_instance
-/
instance hasLimit_cospan_forget_of_left : HasLimit (cospan f g ⋙ forget) := by
  have : HasLimit (cospan ((cospan f g ⋙ forget).map Hom.inl)
      ((cospan f g ⋙ forget).map Hom.inr)) := by
    change HasLimit (cospan ((forget).map f) ((forget).map g))
    infer_instance
  apply hasLimit_of_iso (diagramIsoCospan _).symm

/--
Instance `hasLimit_cospan_forget_of_left'` / 实例 `hasLimit_cospan_forget_of_left'`

English:
instance hasLimit_cospan_forget_of_left'
  signature: :
  body: show HasLimit (cospan ((forget).map f) ((forget).map g)) from inferInstance

中文:
实例 hasLimit_cospan_forget_of_left'
  签名: :
  定义体: show HasLimit (cospan ((forget).map f) ((forget).map g)) from inferInstance

Depends on / 依赖: HasLimit, cospan, forget
-/
instance hasLimit_cospan_forget_of_left' :
    HasLimit (cospan ((cospan f g ⋙ forget).map Hom.inl) ((cospan f g ⋙ forget).map Hom.inr)) :=
  show HasLimit (cospan ((forget).map f) ((forget).map g)) from inferInstance

/--
Instance `hasLimit_cospan_forget_of_right` / 实例 `hasLimit_cospan_forget_of_right`

English:
instance hasLimit_cospan_forget_of_right
  signature: : HasLimit (cospan g f ⋙ forget)
  body: by
  have : HasLimit (cospan ((cospan g f ⋙ forget).map Hom.inl)
      ((cospan g f ⋙ forget).map Hom.inr)) := by
    change HasLimit (cospan ((forget).map g) ((forget).map f))
    infer_instance
  apply hasLimit_of_iso (diagramIsoCospan _).symm

中文:
实例 hasLimit_cospan_forget_of_right
  签名: : 有极限 (cospan g f ⋙ forget)
  定义体: by
  have : HasLimit (cospan ((cospan g f ⋙ forget).map Hom.inl)
      ((cospan g f ⋙ forget).map Hom.inr)) := by
    change HasLimit (cospan ((forget).map g) ((forget).map f))
    infer_instance
  apply hasLimit_of_iso (diagramIsoCospan _).symm

Depends on / 依赖: HasLimit, Hom.inl, Hom.inr, cospan, diagramIsoCospan, forget, hasLimit_of_iso, infer_instance
-/
instance hasLimit_cospan_forget_of_right : HasLimit (cospan g f ⋙ forget) := by
  have : HasLimit (cospan ((cospan g f ⋙ forget).map Hom.inl)
      ((cospan g f ⋙ forget).map Hom.inr)) := by
    change HasLimit (cospan ((forget).map g) ((forget).map f))
    infer_instance
  apply hasLimit_of_iso (diagramIsoCospan _).symm

/--
Instance `hasLimit_cospan_forget_of_right'` / 实例 `hasLimit_cospan_forget_of_right'`

English:
instance hasLimit_cospan_forget_of_right'
  signature: :
  body: show HasLimit (cospan ((forget).map g) ((forget).map f)) from inferInstance

中文:
实例 hasLimit_cospan_forget_of_right'
  签名: :
  定义体: show HasLimit (cospan ((forget).map g) ((forget).map f)) from inferInstance

Depends on / 依赖: HasLimit, cospan, forget
-/
instance hasLimit_cospan_forget_of_right' :
    HasLimit (cospan ((cospan g f ⋙ forget).map Hom.inl) ((cospan g f ⋙ forget).map Hom.inr)) :=
  show HasLimit (cospan ((forget).map g) ((forget).map f)) from inferInstance

/--
Instance `forgetCreatesPullbackOfLeft` / 实例 `forgetCreatesPullbackOfLeft`

English:
instance forgetCreatesPullbackOfLeft
  signature: : CreatesLimit (cospan f g) forget
  body: createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toSheafedSpace Y
      (@pullback.snd (PresheafedSpace C) _ _ _ _ f.hom g.hom _))
    (eqToIso (show pullback _ _ = pullback _ _ by congr) ≪≫
      HasLimit.isoOfNatIso (diagramIsoCospan _).symm)

中文:
实例 forgetCreatesPullbackOfLeft
  签名: : 创造极限 (cospan f g) forget
  定义体: createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toSheafedSpace Y
      (@pullback.snd (PresheafedSpace C) _ _ _ _ f.hom g.hom _))
    (eqToIso (show pullback _ _ = pullback _ _ by congr) ≪≫
      HasLimit.isoOfNatIso (diagramIsoCospan _).symm)

Depends on / 依赖: HasLimit, HasLimit.isoOfNatIso, IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.toSheafedSpace, createsLimitOfFullyFaithfulOfIso, diagramIsoCospan, eqToIso, f.hom, g.hom, isoOfNatIso, pullback, pullback.snd, toSheafedSpace
-/
instance forgetCreatesPullbackOfLeft : CreatesLimit (cospan f g) forget :=
  createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toSheafedSpace Y
      (@pullback.snd (PresheafedSpace C) _ _ _ _ f.hom g.hom _))
    (eqToIso (show pullback _ _ = pullback _ _ by congr) ≪≫
      HasLimit.isoOfNatIso (diagramIsoCospan _).symm)

/--
Instance `forgetCreatesPullbackOfRight` / 实例 `forgetCreatesPullbackOfRight`

English:
instance forgetCreatesPullbackOfRight
  signature: : CreatesLimit (cospan g f) forget
  body: createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toSheafedSpace Y
      (@pullback.fst (PresheafedSpace C) _ _ _ _ g.hom f.hom _))
    (eqToIso (show pullback _ _ = pullback _ _ by congr) ≪≫
      HasLimit.isoOfNatIso (diagramIsoCospan _).symm)

中文:
实例 forgetCreatesPullbackOfRight
  签名: : 创造极限 (cospan g f) forget
  定义体: createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toSheafedSpace Y
      (@pullback.fst (PresheafedSpace C) _ _ _ _ g.hom f.hom _))
    (eqToIso (show pullback _ _ = pullback _ _ by congr) ≪≫
      HasLimit.isoOfNatIso (diagramIsoCospan _).symm)

Depends on / 依赖: HasLimit, HasLimit.isoOfNatIso, IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.toSheafedSpace, createsLimitOfFullyFaithfulOfIso, diagramIsoCospan, eqToIso, f.hom, g.hom, isoOfNatIso, pullback, pullback.fst, toSheafedSpace
-/
instance forgetCreatesPullbackOfRight : CreatesLimit (cospan g f) forget :=
  createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toSheafedSpace Y
      (@pullback.fst (PresheafedSpace C) _ _ _ _ g.hom f.hom _))
    (eqToIso (show pullback _ _ = pullback _ _ by congr) ≪≫
      HasLimit.isoOfNatIso (diagramIsoCospan _).symm)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `sheafedSpace_forgetPreserves_of_left` / 实例 `sheafedSpace_forgetPreserves_of_left`

English:
instance sheafedSpace_forgetPreserves_of_left
  signature: :
  body: @Limits.comp_preservesLimit _ _ _ _ _ _ (cospan f g) _ _ forget (PresheafedSpace.forget C)
inferInstance by
      have : PreservesLimit
        (cospan ((cospan f g ⋙ forget).map Hom.inl)
          ((cospan f g ⋙ forget).map Hom.inr)) (PresheafedSpace.forget C) := by
        dsimp
        infer_inst

中文:
实例 sheafedSpace_forgetPreserves_of_left
  签名: :
  定义体: @Limits.comp_preservesLimit _ _ _ _ _ _ (cospan f g) _ _ forget (PresheafedSpace.forget C)
inferInstance by
      have : PreservesLimit
        (cospan ((cospan f g ⋙ forget).map Hom.inl)
          ((cospan f g ⋙ forget).map Hom.inr)) (PresheafedSpace.forget C) := by
        dsimp
        infer_inst

Depends on / 依赖: Hom.inl, Hom.inr, Limits, Limits.comp_preservesLimit, PreservesLimit, PresheafedSpace, PresheafedSpace.forget, comp_preservesLimit, cospan, diagramIsoCospan, forget, infer_instance, preservesLimit_of_iso_diagram
-/
instance sheafedSpace_forgetPreserves_of_left :
    PreservesLimit (cospan f g) (SheafedSpace.forget C) :=
  @Limits.comp_preservesLimit _ _ _ _ _ _ (cospan f g) _ _ forget (PresheafedSpace.forget C)
inferInstance by
      have : PreservesLimit
        (cospan ((cospan f g ⋙ forget).map Hom.inl)
          ((cospan f g ⋙ forget).map Hom.inr)) (PresheafedSpace.forget C) := by
        dsimp
        infer_instance
      apply preservesLimit_of_iso_diagram _ (diagramIsoCospan _).symm

/--
Instance `sheafedSpace_forgetPreserves_of_right` / 实例 `sheafedSpace_forgetPreserves_of_right`

English:
instance sheafedSpace_forgetPreserves_of_right
  signature: :
  body: preservesPullback_symmetry _ _ _

中文:
实例 sheafedSpace_forgetPreserves_of_right
  签名: :
  定义体: preservesPullback_symmetry _ _ _

Depends on / 依赖: preservesPullback_symmetry
-/
instance sheafedSpace_forgetPreserves_of_right :
    PreservesLimit (cospan g f) (SheafedSpace.forget C) :=
  preservesPullback_symmetry _ _ _

/--
Instance `sheafedSpace_hasPullback_of_left` / 实例 `sheafedSpace_hasPullback_of_left`

English:
instance sheafedSpace_hasPullback_of_left
  signature: : HasPullback f g
  body: hasLimit_of_created (cospan f g) forget

中文:
实例 sheafedSpace_hasPullback_of_left
  签名: : HasPullback f g
  定义体: hasLimit_of_created (cospan f g) forget

Depends on / 依赖: cospan, forget, hasLimit_of_created
-/
instance sheafedSpace_hasPullback_of_left : HasPullback f g :=
  hasLimit_of_created (cospan f g) forget

/--
Instance `sheafedSpace_hasPullback_of_right` / 实例 `sheafedSpace_hasPullback_of_right`

English:
instance sheafedSpace_hasPullback_of_right
  signature: : HasPullback g f
  body: hasLimit_of_created (cospan g f) forget

中文:
实例 sheafedSpace_hasPullback_of_right
  签名: : HasPullback g f
  定义体: hasLimit_of_created (cospan g f) forget

Depends on / 依赖: cospan, forget, hasLimit_of_created
-/
instance sheafedSpace_hasPullback_of_right : HasPullback g f :=
  hasLimit_of_created (cospan g f) forget

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `sheafedSpace_pullback_snd_of_left` / 实例 `sheafedSpace_pullback_snd_of_left`

English:
instance sheafedSpace_pullback_snd_of_left
  signature: :
  body: by
  rw [SheafedSpace.isOpenImmersion_iff_hom]
  have : _ = (pullback.snd f g).hom := preservesLimitIso_hom_π forget (cospan f g) right
  rw [← this]
  have := HasLimit.isoOfNatIso_hom_π (diagramIsoCospan (cospan f g ⋙ forget)) right
  dsimp at this
  rw [Category.comp_id] at this
  rw [← this]
  in

中文:
实例 sheafedSpace_pullback_snd_of_left
  签名: :
  定义体: by
  rw [SheafedSpace.isOpenImmersion_iff_hom]
  have : _ = (pullback.snd f g).hom := preservesLimitIso_hom_π forget (cospan f g) right
  rw [← this]
  have := HasLimit.isoOfNatIso_hom_π (diagramIsoCospan (cospan f g ⋙ forget)) right
  dsimp at this
  rw [Category.comp_id] at this
  rw [← this]
  in

Depends on / 依赖: Category, Category.comp_id, HasLimit, HasLimit.isoOfNatIso_hom_, SheafedSpace, SheafedSpace.isOpenImmersion_iff_hom, comp_id, cospan, diagramIsoCospan, forget, infer_instance, isOpenImmersion_iff_hom, pullback, pullback.snd
-/
instance sheafedSpace_pullback_snd_of_left :
    SheafedSpace.IsOpenImmersion (pullback.snd f g) := by
  rw [SheafedSpace.isOpenImmersion_iff_hom]
  have : _ = (pullback.snd f g).hom := preservesLimitIso_hom_π forget (cospan f g) right
  rw [← this]
  have := HasLimit.isoOfNatIso_hom_π (diagramIsoCospan (cospan f g ⋙ forget)) right
  dsimp at this
  rw [Category.comp_id] at this
  rw [← this]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `sheafedSpace_pullback_fst_of_right` / 实例 `sheafedSpace_pullback_fst_of_right`

English:
instance sheafedSpace_pullback_fst_of_right
  signature: :
  body: by
  rw [SheafedSpace.isOpenImmersion_iff_hom]
  have : _ = (pullback.fst g f).hom := preservesLimitIso_hom_π forget (cospan g f) left
  rw [← this]
  have := HasLimit.isoOfNatIso_hom_π (diagramIsoCospan (cospan g f ⋙ forget)) left
  dsimp at this
  rw [Category.comp_id] at this
  rw [← this]
  infe

中文:
实例 sheafedSpace_pullback_fst_of_right
  签名: :
  定义体: by
  rw [SheafedSpace.isOpenImmersion_iff_hom]
  have : _ = (pullback.fst g f).hom := preservesLimitIso_hom_π forget (cospan g f) left
  rw [← this]
  have := HasLimit.isoOfNatIso_hom_π (diagramIsoCospan (cospan g f ⋙ forget)) left
  dsimp at this
  rw [Category.comp_id] at this
  rw [← this]
  infe

Depends on / 依赖: Category, Category.comp_id, HasLimit, HasLimit.isoOfNatIso_hom_, SheafedSpace, SheafedSpace.isOpenImmersion_iff_hom, comp_id, cospan, diagramIsoCospan, forget, infer_instance, isOpenImmersion_iff_hom, pullback, pullback.fst
-/
instance sheafedSpace_pullback_fst_of_right :
    SheafedSpace.IsOpenImmersion (pullback.fst g f) := by
  rw [SheafedSpace.isOpenImmersion_iff_hom]
  have : _ = (pullback.fst g f).hom := preservesLimitIso_hom_π forget (cospan g f) left
  rw [← this]
  have := HasLimit.isoOfNatIso_hom_π (diagramIsoCospan (cospan g f ⋙ forget)) left
  dsimp at this
  rw [Category.comp_id] at this
  rw [← this]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Instance `sheafedSpace_pullback_to_base_isOpenImmersion` / 实例 `sheafedSpace_pullback_to_base_isOpenImmersion`

English:
instance sheafedSpace_pullback_to_base_isOpenImmersion
  signature: [SheafedSpace.IsOpenImmersion g]
  body: by
  rw [← limit.w (cospan f g) Hom.inl]; rw [cospan_map_inl]
  infer_instance

中文:
实例 sheafedSpace_pullback_to_base_isOpenImmersion
  签名: [Sheafed空间.是开浸入 g]
  定义体: by
  rw [← limit.w (cospan f g) Hom.inl]; rw [cospan_map_inl]
  infer_instance

Depends on / 依赖: Hom.inl, cospan, cospan_map_inl, infer_instance, limit.w
-/
instance sheafedSpace_pullback_to_base_isOpenImmersion [SheafedSpace.IsOpenImmersion g] :
    SheafedSpace.IsOpenImmersion (limit.π (cospan f g) one : pullback f g ⟶ Z) := by
  rw [← limit.w (cospan f g) Hom.inl]; rw [cospan_map_inl]
  infer_instance

end Pullback

section OfStalkIso

variable [HasLimits C] [HasColimits C] {FC : C -> C -> Type*} {CC : C -> Type v}
variable [forall X Y, FunLike (FC X Y) (CC X) (CC Y)] [instCC : ConcreteCategory.{v} C FC]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]
  [PreservesLimits (CategoryTheory.forget C)]

variable [PreservesFilteredColimits (CategoryTheory.forget C)]

set_option backward.isDefEq.respectTransparency false in
include instCC in
/--
theorem `of_stalk_iso` / 定理 `of_stalk_iso`

English:
theorem of_stalk_iso
  statement: {X Y : SheafedSpace C} (f : X ⟶ Y) (hf : IsOpenEmbedding f.hom.base)
  proof: { base_open := hf
    c_iso := fun U => by
      apply +allowSynthFailures TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso
          (show Y.sheaf ⟶ (TopCat.Sheaf.pushforward _ f.hom.base).obj X.sheaf from ⟨f.hom.c⟩)
      rintro ⟨_, y, hy, rfl⟩
      specialize H y
      delta PresheafedSpace.Hom

中文:
定理 of_stalk_iso
  结论: {X Y : Sheafed空间 C} (f : X ⟶ Y) (hf : 是开嵌入 f.hom.base)
  证明: { base_open := hf
    c_iso := fun U => by
      apply +allowSynthFailures TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso
          (show Y.sheaf ⟶ (TopCat.Sheaf.pushforward _ f.hom.base).obj X.sheaf from ⟨f.hom.c⟩)
      rintro ⟨_, y, hy, rfl⟩
      specialize H y
      delta PresheafedSpace.Hom

Depends on / 依赖: Category, Category.assoc, Category.comp_, IsIso.comp_isIso, IsIso.hom_inv_id, IsIso.inv_isIso, Presheaf, PresheafedSpace, PresheafedSpace.Hom.stalkMap, TopCat, TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso, TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing, TopCat.Sheaf.pushforward, X.presheaf, X.sheaf, Y.sheaf, allowSynthFailures, app_isIso_of_stalkFunctor_map_iso, base_open, c_iso
-/
theorem of_stalk_iso {X Y : SheafedSpace C} (f : X ⟶ Y) (hf : IsOpenEmbedding f.hom.base)
    [H : forall x : X.1, IsIso (f.hom.stalkMap x)] : SheafedSpace.IsOpenImmersion f :=
  { base_open := hf
    c_iso := fun U => by
      apply +allowSynthFailures TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso
          (show Y.sheaf ⟶ (TopCat.Sheaf.pushforward _ f.hom.base).obj X.sheaf from ⟨f.hom.c⟩)
      rintro ⟨_, y, hy, rfl⟩
      specialize H y
      delta PresheafedSpace.Hom.stalkMap at H
      have H' := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing C
        hf.toIsInducing X.presheaf y
      have := IsIso.comp_isIso' H (@IsIso.inv_isIso _ _ _ _ _ H')
      rwa [Category.assoc, IsIso.hom_inv_id, Category.comp_id] at this }

end OfStalkIso

section

variable {X Y : SheafedSpace C} (f : X ⟶ Y) [H : IsOpenImmersion f]

/--
Definition of `opensFunctor` / `opensFunctor` 的定义

English:
abbreviation opensFunctor
  signature: : Opens X ⥤ Opens Y
  body: H.base_open.functor

#adaptation_note

中文:
缩写 opensFunctor
  签名: : Opens X ⥤ Opens Y
  定义体: H.base_open.functor

#adaptation_note

Depends on / 依赖: H.base_open.functor, base_open, functor
-/
abbrev opensFunctor : Opens X ⥤ Opens Y :=
  H.base_open.functor

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- An open immersion `f : X ⟶ Y` induces an isomorphism `X ≅ Y|_{f(X)}`. -/
@[simps! hom_hom_c_app]
/--
Definition of `isoRestrict` / `isoRestrict` 的定义

English:
definition isoRestrict
  signature: : X ≅ Y.restrict H.base_open
  body: SheafedSpace.isoMk PresheafedSpace.IsOpenImmersion.isoRestrict f.hom

@[reassoc (attr := simp)]

中文:
定义 isoRestrict
  签名: : X ≅ Y.restrict H.base_open
  定义体: SheafedSpace.isoMk PresheafedSpace.IsOpenImmersion.isoRestrict f.hom

@[reassoc (attr := simp)]

Depends on / 依赖: IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.isoRestrict, SheafedSpace, SheafedSpace.isoMk, f.hom, isoRestrict
-/
noncomputable def isoRestrict : X ≅ Y.restrict H.base_open :=
SheafedSpace.isoMk PresheafedSpace.IsOpenImmersion.isoRestrict f.hom

@[reassoc (attr := simp)]
/--
theorem `isoRestrict_hom_ofRestrict` / 定理 `isoRestrict_hom_ofRestrict`

English:
theorem isoRestrict_hom_ofRestrict
  statement: (isoRestrict f).hom ≫ Y.ofRestrict _ = f
  proof: InducedCategory.hom_ext
    (PresheafedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict f.hom)

@[reassoc (attr := simp)]

中文:
定理 isoRestrict_hom_ofRestrict
  结论: (isoRestrict f).hom ≫ Y.ofRestrict _ = f
  证明: InducedCategory.hom_ext
    (PresheafedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict f.hom)

@[reassoc (attr := simp)]

Depends on / 依赖: InducedCategory, InducedCategory.hom_ext, IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict, f.hom, hom_ext, isoRestrict_hom_ofRestrict
-/
theorem isoRestrict_hom_ofRestrict : (isoRestrict f).hom ≫ Y.ofRestrict _ = f :=
  InducedCategory.hom_ext
    (PresheafedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict f.hom)

@[reassoc (attr := simp)]
/--
theorem `isoRestrict_inv_ofRestrict` / 定理 `isoRestrict_inv_ofRestrict`

English:
theorem isoRestrict_inv_ofRestrict
  statement: (isoRestrict f).inv ≫ f = Y.ofRestrict _
  proof: InducedCategory.hom_ext
    (PresheafedSpace.IsOpenImmersion.isoRestrict_inv_ofRestrict f.hom)

中文:
定理 isoRestrict_inv_ofRestrict
  结论: (isoRestrict f).inv ≫ f = Y.ofRestrict _
  证明: InducedCategory.hom_ext
    (PresheafedSpace.IsOpenImmersion.isoRestrict_inv_ofRestrict f.hom)

Depends on / 依赖: InducedCategory, InducedCategory.hom_ext, IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.isoRestrict_inv_ofRestrict, f.hom, hom_ext, isoRestrict_inv_ofRestrict
-/
theorem isoRestrict_inv_ofRestrict : (isoRestrict f).inv ≫ f = Y.ofRestrict _ :=
  InducedCategory.hom_ext
    (PresheafedSpace.IsOpenImmersion.isoRestrict_inv_ofRestrict f.hom)

/--
Definition of `invApp` / `invApp` 的定义

English:
definition invApp
  signature: (U : Opens X)
  body: PresheafedSpace.IsOpenImmersion.invApp f.hom U

#adaptation_note

中文:
定义 invApp
  签名: (U : Opens X)
  定义体: PresheafedSpace.IsOpenImmersion.invApp f.hom U

#adaptation_note

Depends on / 依赖: IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.invApp, f.hom, invApp
-/
noncomputable def invApp (U : Opens X) :
    X.presheaf.obj (op U) ⟶ Y.presheaf.obj (op (opensFunctor f |>.obj U)) :=
  PresheafedSpace.IsOpenImmersion.invApp f.hom U

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
theorem `inv_naturality` / 定理 `inv_naturality`

English:
theorem inv_naturality
  given: {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
  proof: PresheafedSpace.IsOpenImmersion.inv_naturality f.hom i

中文:
定理 inv_naturality
  条件: {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
  证明: PresheafedSpace.IsOpenImmersion.inv_naturality f.hom i

Depends on / 依赖: IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.inv_naturality, f.hom, inv_naturality
-/
theorem inv_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    X.presheaf.map i ≫ H.invApp _ (unop V) =
      H.invApp _ (unop U) ≫ Y.presheaf.map (opensFunctor f |>.op.map i) :=
  PresheafedSpace.IsOpenImmersion.inv_naturality f.hom i

instance (U : Opens X) : IsIso (H.invApp _ U) := by delta invApp; infer_instance

/--
theorem `inv_invApp` / 定理 `inv_invApp`

English:
theorem inv_invApp
  given: (U : Opens X)
  proof: PresheafedSpace.IsOpenImmersion.inv_invApp f.hom U

@[reassoc (attr := simp)]

中文:
定理 inv_invApp
  条件: (U : Opens X)
  证明: PresheafedSpace.IsOpenImmersion.inv_invApp f.hom U

@[reassoc (attr := simp)]

Depends on / 依赖: IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.inv_invApp, f.hom, inv_invApp
-/
theorem inv_invApp (U : Opens X) :
    inv (H.invApp _ U) =
      f.hom.c.app (op (opensFunctor f |>.obj U)) ≫ X.presheaf.map
        (eqToHom (by simp [Opens.map_def, Set.preimage_image_eq _ H.base_open.injective])) :=
  PresheafedSpace.IsOpenImmersion.inv_invApp f.hom U

@[reassoc (attr := simp)]
/--
theorem `invApp_app` / 定理 `invApp_app`

English:
theorem invApp_app
  given: (U : Opens X)
  proof: PresheafedSpace.IsOpenImmersion.invApp_app f.hom U

中文:
定理 invApp_app
  条件: (U : Opens X)
  证明: PresheafedSpace.IsOpenImmersion.invApp_app f.hom U

Depends on / 依赖: IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.invApp_app, f.hom, invApp_app
-/
theorem invApp_app (U : Opens X) :
    H.invApp _ U ≫ f.hom.c.app (op (opensFunctor f |>.obj U)) = X.presheaf.map
      (eqToHom (by simp [Opens.map_def, Set.preimage_image_eq _ H.base_open.injective])) :=
  PresheafedSpace.IsOpenImmersion.invApp_app f.hom U

attribute [elementwise] invApp_app

@[reassoc (attr := simp)]
/--
theorem `app_invApp` / 定理 `app_invApp`

English:
theorem app_invApp
  given: (U : Opens Y)
  proof: PresheafedSpace.IsOpenImmersion.app_invApp f.hom U

中文:
定理 app_invApp
  条件: (U : Opens Y)
  证明: PresheafedSpace.IsOpenImmersion.app_invApp f.hom U

Depends on / 依赖: IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.app_invApp, app_invApp, f.hom
-/
theorem app_invApp (U : Opens Y) :
    f.hom.c.app (op U) ≫ H.invApp _ ((Opens.map f.hom.base).obj U) =
      Y.presheaf.map
        ((homOfLE (Set.image_preimage_subset f.hom.base U.1)).op :
          op U ⟶ op (opensFunctor f |>.obj ((Opens.map f.hom.base).obj U))) :=
  PresheafedSpace.IsOpenImmersion.app_invApp f.hom U

/-- A variant of `app_inv_app` that gives an `eqToHom` instead of `homOfLe`. -/
@[reassoc]
/--
theorem `app_inv_app'` / 定理 `app_inv_app'`

English:
theorem app_inv_app'
  given: (U : Opens Y) (hU : (U : Set Y) subseteq Set.range f.hom.base)
  proof: PresheafedSpace.IsOpenImmersion.app_invApp f.hom U

中文:
定理 app_inv_app'
  条件: (U : Opens Y) (hU : (U : 集合 Y) subseteq 集合.range f.hom.base)
  证明: PresheafedSpace.IsOpenImmersion.app_invApp f.hom U

Depends on / 依赖: f.hom.base
-/
theorem app_inv_app' (U : Opens Y) (hU : (U : Set Y) subseteq Set.range f.hom.base) :
    f.hom.c.app (op U) ≫ invApp f ((Opens.map f.hom.base).obj U) =
      Y.presheaf.map
        (eqToHom <|
le_antisymm (Set.image_preimage_subset f.hom.base U.1)
              (Set.image_preimage_eq_inter_range (f := f.hom.base) (t := U.1)).symm ▸
                Set.subset_inter_iff.mpr ⟨fun _ h => h, hU⟩).op :=
  PresheafedSpace.IsOpenImmersion.app_invApp f.hom U

/--
Instance `ofRestrict` / 实例 `ofRestrict`

English:
instance ofRestrict
  signature: {X : TopCat.{w}} (Y : SheafedSpace C) {f : X ⟶ Y.carrier}
  body: PresheafedSpace.IsOpenImmersion.ofRestrict _ hf

@[elementwise, simp]

中文:
实例 ofRestrict
  签名: {X : 顶元素范畴.{w}} (Y : Sheafed空间 C) {f : X ⟶ Y.carrier}
  定义体: PresheafedSpace.IsOpenImmersion.ofRestrict _ hf

@[elementwise, simp]

Depends on / 依赖: IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.ofRestrict, ofRestrict
-/
instance ofRestrict {X : TopCat.{w}} (Y : SheafedSpace C) {f : X ⟶ Y.carrier}
    (hf : IsOpenEmbedding f) : IsOpenImmersion (Y.ofRestrict hf) :=
  PresheafedSpace.IsOpenImmersion.ofRestrict _ hf

@[elementwise, simp]
/--
theorem `ofRestrict_invApp` / 定理 `ofRestrict_invApp`

English:
theorem ofRestrict_invApp
  statement: {C : Type*} [Category* C] (X : SheafedSpace C) {Y : TopCat.{w}}
  proof: PresheafedSpace.IsOpenImmersion.ofRestrict_invApp _ h U

中文:
定理 ofRestrict_invApp
  结论: {C : 类型} [范畴* C] (X : Sheafed空间 C) {Y : 顶元素范畴.{w}}
  证明: PresheafedSpace.IsOpenImmersion.ofRestrict_invApp _ h U

Depends on / 依赖: IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.ofRestrict_invApp, ofRestrict_invApp
-/
theorem ofRestrict_invApp {C : Type*} [Category* C] (X : SheafedSpace C) {Y : TopCat.{w}}
    {f : Y ⟶ TopCat.of X.carrier} (h : IsOpenEmbedding f) (U : Opens (X.restrict h).carrier) :
    (SheafedSpace.IsOpenImmersion.ofRestrict X h).invApp _ U = 𝟙 _ :=
  PresheafedSpace.IsOpenImmersion.ofRestrict_invApp _ h U

/--
theorem `to_iso` / 定理 `to_iso`

English:
theorem to_iso
  given: [h' : Epi f.hom.base]
  statement: IsIso f
  proof: by
  have : IsIso (forgetToPresheafedSpace.map f) := PresheafedSpace.IsOpenImmersion.to_iso f.hom
  apply isIso_of_reflects_iso _ (SheafedSpace.forgetToPresheafedSpace)

中文:
定理 to_iso
  条件: [h' : 满态射 f.hom.base]
  结论: 是同构 f
  证明: by
  have : IsIso (forgetToPresheafedSpace.map f) := PresheafedSpace.IsOpenImmersion.to_iso f.hom
  apply isIso_of_reflects_iso _ (SheafedSpace.forgetToPresheafedSpace)

Depends on / 依赖: IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.to_iso, SheafedSpace, SheafedSpace.forgetToPresheafedSpace, f.hom, forgetToPresheafedSpace, forgetToPresheafedSpace.map, isIso_of_reflects_iso, to_iso
-/
theorem to_iso [h' : Epi f.hom.base] : IsIso f := by
  have : IsIso (forgetToPresheafedSpace.map f) := PresheafedSpace.IsOpenImmersion.to_iso f.hom
  apply isIso_of_reflects_iso _ (SheafedSpace.forgetToPresheafedSpace)

/--
Instance `stalk_iso` / 实例 `stalk_iso`

English:
instance stalk_iso
  signature: [HasColimits C] (x : X)
  body: PresheafedSpace.IsOpenImmersion.stalk_iso f.hom x

中文:
实例 stalk_iso
  签名: [有余极限 C] (x : X)
  定义体: PresheafedSpace.IsOpenImmersion.stalk_iso f.hom x

Depends on / 依赖: IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.stalk_iso, f.hom, stalk_iso
-/
instance stalk_iso [HasColimits C] (x : X) :
    IsIso (f.hom.stalkMap x) :=
  PresheafedSpace.IsOpenImmersion.stalk_iso f.hom x

end

section Prod

-- here `ι` should have same universe level as morphism of `C`, so needs explicit universe level
variable [HasLimits C] {ι : Type v} (F : Discrete ι ⥤ SheafedSpace.{_, v, v} C) [HasColimit F]
  (i : Discrete ι)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `sigma_ι_isOpenEmbedding` / 定理 `sigma_ι_isOpenEmbedding`

English:
theorem sigma_ι_isOpenEmbedding
  statement: IsOpenEmbedding (colimit.ι F i).hom.base
  proof: by
  rw [← show _ = (colimit.ι F i).hom.base from
    ι_preservesColimitIso_inv (SheafedSpace.forget C) F i]
  have : _ = _ ≫ colimit.ι (Discrete.functor ((F ⋙ SheafedSpace.forget C).obj ∘ Discrete.mk)) i :=
    HasColimit.isoOfNatIso_ι_hom Discrete.natIsoFunctor i
  rw [← Iso.eq_comp_inv] at this
 

中文:
定理 sigma_ι_isOpenEmbedding
  结论: 是开嵌入 (colimit.ι F i).hom.base
  证明: by
  rw [← show _ = (colimit.ι F i).hom.base from
    ι_preservesColimitIso_inv (SheafedSpace.forget C) F i]
  have : _ = _ ≫ colimit.ι (Discrete.functor ((F ⋙ SheafedSpace.forget C).obj ∘ Discrete.mk)) i :=
    HasColimit.isoOfNatIso_ι_hom Discrete.natIsoFunctor i
  rw [← Iso.eq_comp_inv] at this
 

Depends on / 依赖: Category, Category.assoc, Discrete, Discrete.functor, Discrete.mk, Discrete.natIsoFunctor, HasColimit, HasColimit.isoOfNatIso_, Iso.eq_comp_inv, SheafedSpace, SheafedSpace.forget, TopCat, TopCat.sigmaIsoSigma_hom_, colimit, eq_comp_inv, forget, functor, hom.base, i.as, natIsoFunctor
-/
theorem sigma_ι_isOpenEmbedding : IsOpenEmbedding (colimit.ι F i).hom.base := by
  rw [← show _ = (colimit.ι F i).hom.base from
    ι_preservesColimitIso_inv (SheafedSpace.forget C) F i]
  have : _ = _ ≫ colimit.ι (Discrete.functor ((F ⋙ SheafedSpace.forget C).obj ∘ Discrete.mk)) i :=
    HasColimit.isoOfNatIso_ι_hom Discrete.natIsoFunctor i
  rw [← Iso.eq_comp_inv] at this
  rw [this]
  have : colimit.ι _ _ ≫ _ = _ :=
    TopCat.sigmaIsoSigma_hom_ι.{v, v} ((F ⋙ SheafedSpace.forget C).obj ∘ Discrete.mk) i.as
  rw [← Iso.eq_comp_inv] at this
  cases i
  rw [this]; rw [← Category.assoc]
  simp_rw [TopCat.isOpenEmbedding_iff_comp_isIso, (TopCat.isOpenEmbedding_iff_isIso_comp)]
  exact .sigmaMk

set_option backward.isDefEq.respectTransparency false in
/--
theorem `image_preimage_is_empty` / 定理 `image_preimage_is_empty`

English:
theorem image_preimage_is_empty
  given: (j : Discrete ι) (h : i != j) (U : Opens (F.obj i))
  proof: by
  ext x
  apply iff_false_intro
  rintro ⟨y, hy, eq⟩
  replace eq := ConcreteCategory.congr_arg (preservesColimitIso (SheafedSpace.forget C) F ≪≫
    HasColimit.isoOfNatIso Discrete.natIsoFunctor ≪≫ TopCat.sigmaIsoSigma.{v, v} _).hom eq
  simp_rw [CategoryTheory.Iso.trans_hom, ← TopCat.comp_app, 

中文:
定理 image_preimage_is_empty
  条件: (j : 离散 ι) (h : i != j) (U : Opens (F.obj i))
  证明: by
  ext x
  apply iff_false_intro
  rintro ⟨y, hy, eq⟩
  replace eq := ConcreteCategory.congr_arg (preservesColimitIso (SheafedSpace.forget C) F ≪≫
    HasColimit.isoOfNatIso Discrete.natIsoFunctor ≪≫ TopCat.sigmaIsoSigma.{v, v} _).hom eq
  simp_rw [CategoryTheory.Iso.trans_hom, ← TopCat.comp_app, 

Depends on / 依赖: CategoryTheory, CategoryTheory.Iso.trans_hom, ConcreteCategory, ConcreteCategory.congr_arg, Discrete, Discrete.natIsoFunctor, HasColimit, HasColimit.isoOfNatIso, PresheafedSpace, PresheafedSpace.comp_base, SheafedSpace, SheafedSpace.forget, TopCat, TopCat.comp_app, TopCat.sigmaIsoSigma, colimit, comp_app, comp_base, congr_arg, forget
-/
theorem image_preimage_is_empty (j : Discrete ι) (h : i != j) (U : Opens (F.obj i)) :
    (Opens.map (colimit.ι (F ⋙ SheafedSpace.forgetToPresheafedSpace) j).base).obj
        ((Opens.map (preservesColimitIso SheafedSpace.forgetToPresheafedSpace F).inv.base).obj
          ((sigma_ι_isOpenEmbedding F i).functor.obj U)) =
      ⊥ := by
  ext x
  apply iff_false_intro
  rintro ⟨y, hy, eq⟩
  replace eq := ConcreteCategory.congr_arg (preservesColimitIso (SheafedSpace.forget C) F ≪≫
    HasColimit.isoOfNatIso Discrete.natIsoFunctor ≪≫ TopCat.sigmaIsoSigma.{v, v} _).hom eq
  simp_rw [CategoryTheory.Iso.trans_hom, ← TopCat.comp_app, ← PresheafedSpace.comp_base] at eq
  rw [ι_preservesColimitIso_inv] at eq
  change
    ((SheafedSpace.forget C).map (colimit.ι F i) ≫ (preservesColimitIso (forget C) F).hom ≫
          (HasColimit.isoOfNatIso Discrete.natIsoFunctor).hom ≫
            (TopCat.sigmaIsoSigma ((F ⋙ forget C).obj ∘ Discrete.mk)).hom) y =
      ((SheafedSpace.forget C).map (colimit.ι F j) ≫ (preservesColimitIso (forget C) F).hom ≫
          (HasColimit.isoOfNatIso Discrete.natIsoFunctor).hom ≫
            (TopCat.sigmaIsoSigma ((F ⋙ forget C).obj ∘ Discrete.mk)).hom) x at eq
  cases i; cases j
  rw [ι_preservesColimitIso_hom_assoc]; rw [ι_preservesColimitIso_hom_assoc]; rw [HasColimit.isoOfNatIso_ι_hom_assoc]; rw [HasColimit.isoOfNatIso_ι_hom_assoc]; rw [TopCat.sigmaIsoSigma_hom_ι]; rw [TopCat.sigmaIsoSigma_hom_ι] at eq
  convert! h (congr_arg Discrete.mk (congr_arg Sigma.fst eq))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `sigma_ι_isOpenImmersion_aux` / 实例 `sigma_ι_isOpenImmersion_aux`

English:
instance sigma_ι_isOpenImmersion_aux
  signature: [HasStrictTerminalObjects C]
  body: sigma_ι_isOpenEmbedding F i
  c_iso U := by
    have h₁ := ι_preservesColimitIso_inv SheafedSpace.forgetToPresheafedSpace F i
    have h₂ : colimit.ι F i =
      { hom := (colimit.ι (F ⋙ forgetToPresheafedSpace) i ≫
        (preservesColimitIso _ F).inv) } :=
      InducedCategory.hom_ext h₁.symm
  

中文:
实例 sigma_ι_isOpenImmersion_aux
  签名: [有StrictTerminalObjects C]
  定义体: sigma_ι_isOpenEmbedding F i
  c_iso U := by
    have h₁ := ι_preservesColimitIso_inv SheafedSpace.forgetToPresheafedSpace F i
    have h₂ : colimit.ι F i =
      { hom := (colimit.ι (F ⋙ forgetToPresheafedSpace) i ≫
        (preservesColimitIso _ F).inv) } :=
      InducedCategory.hom_ext h₁.symm
  
-/
instance sigma_ι_isOpenImmersion_aux [HasStrictTerminalObjects C] :
    SheafedSpace.IsOpenImmersion (colimit.ι F i) where
  base_open := sigma_ι_isOpenEmbedding F i
  c_iso U := by
    have h₁ := ι_preservesColimitIso_inv SheafedSpace.forgetToPresheafedSpace F i
    have h₂ : colimit.ι F i =
      { hom := (colimit.ι (F ⋙ forgetToPresheafedSpace) i ≫
        (preservesColimitIso _ F).inv) } :=
      InducedCategory.hom_ext h₁.symm
    have H :
      IsOpenEmbedding
        (colimit.ι (F ⋙ SheafedSpace.forgetToPresheafedSpace) i ≫
            (preservesColimitIso SheafedSpace.forgetToPresheafedSpace F).inv).base := by
      have := h₁.symm
      convert! sigma_ι_isOpenEmbedding F i
suffices IsIso (colimit.ι (F ⋙ SheafedSpace.forgetToPresheafedSpace) i ≫
        (preservesColimitIso SheafedSpace.forgetToPresheafedSpace F).inv).c.app <|
      op (H.functor.obj U) by
      convert! this
    rw [PresheafedSpace.comp_c_app]; rw [← PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_hom_π]
    -- Porting note: this instance created manually to make the `inferInstance` below work
    have : IsIso (preservesColimitIso forgetToPresheafedSpace F).inv.c := inferInstance
    suffices IsIso (limit.π (PresheafedSpace.componentwiseDiagram
      (F ⋙ SheafedSpace.forgetToPresheafedSpace) ((Opens.map
        (preservesColimitIso SheafedSpace.forgetToPresheafedSpace F).inv.base).obj
          (H.functor.obj U))) (op i)) from inferInstance
    apply limit_π_isIso_of_is_strict_terminal
    rintro ⟨j⟩ hj
    dsimp
    convert! (F.obj j).sheaf.isTerminalOfEmpty using 3
    convert! image_preimage_is_empty F i j (fun h => hj (congr_arg op h.symm)) U using 6
    exact congr_arg PresheafedSpace.Hom.base h₁

set_option backward.defeqAttrib.useBackward true in
/--
Instance `sigma_ι_isOpenImmersion` / 实例 `sigma_ι_isOpenImmersion`

English:
instance sigma_ι_isOpenImmersion
  signature: {ι : Type w} [Small.{v} ι]
  body: by
  obtain ⟨ι', ⟨e⟩⟩ := Small.equiv_small (α := ι)
  let f : Discrete ι' ≌ Discrete ι := Discrete.equivalence e.symm
  have : colimit.ι F i = (colimit.ι F i ≫ (HasColimit.isoOfEquivalence f (Iso.refl _)).inv) ≫
      (HasColimit.isoOfEquivalence f (Iso.refl _)).hom := by
    simp
  rw [this]; rw [H

中文:
实例 sigma_ι_isOpenImmersion
  签名: {ι : 类型 w} [Small.{v} ι]
  定义体: by
  obtain ⟨ι', ⟨e⟩⟩ := Small.equiv_small (α := ι)
  let f : Discrete ι' ≌ Discrete ι := Discrete.equivalence e.symm
  have : colimit.ι F i = (colimit.ι F i ≫ (HasColimit.isoOfEquivalence f (Iso.refl _)).inv) ≫
      (HasColimit.isoOfEquivalence f (Iso.refl _)).hom := by
    simp
  rw [this]; rw [H

Depends on / 依赖: Discrete, Discrete.equivalence, HasColimit, HasColimit.isoOfEquivalence, Iso.refl, Small.equiv_small, colimit, e.symm, equiv_small, equivalence, infer_instance, isoOfEquivalence
-/
instance sigma_ι_isOpenImmersion {ι : Type w} [Small.{v} ι]
    (F : Discrete ι ⥤ SheafedSpace.{_, v, v} C) [HasColimit F] (i : Discrete ι)
    [HasStrictTerminalObjects C] :
    SheafedSpace.IsOpenImmersion (colimit.ι F i) := by
  obtain ⟨ι', ⟨e⟩⟩ := Small.equiv_small (α := ι)
  let f : Discrete ι' ≌ Discrete ι := Discrete.equivalence e.symm
  have : colimit.ι F i = (colimit.ι F i ≫ (HasColimit.isoOfEquivalence f (Iso.refl _)).inv) ≫
      (HasColimit.isoOfEquivalence f (Iso.refl _)).hom := by
    simp
  rw [this]; rw [HasColimit.ι_isoOfEquivalence_inv]
  infer_instance

end Prod

end SheafedSpace.IsOpenImmersion

namespace LocallyRingedSpace.IsOpenImmersion

instance (X : LocallyRingedSpace) {U : TopCat.{w}} (f : U ⟶ X.toTopCat) (hf : IsOpenEmbedding f) :
    LocallyRingedSpace.IsOpenImmersion (X.ofRestrict hf) :=
  PresheafedSpace.IsOpenImmersion.ofRestrict X.toPresheafedSpace hf

noncomputable section Pullback

variable {X Y Z : LocallyRingedSpace} (f : X ⟶ Z) (g : Y ⟶ Z)
variable [H : LocallyRingedSpace.IsOpenImmersion f]

instance (priority := 100) of_isIso [IsIso g] : LocallyRingedSpace.IsOpenImmersion g := by
  infer_instance

/--
Instance `comp` / 实例 `comp`

English:
instance comp
  signature: (g : Z ⟶ Y) [LocallyRingedSpace.IsOpenImmersion g]
  body: PresheafedSpace.IsOpenImmersion.comp f.1 g.1

中文:
实例 comp
  签名: (g : Z ⟶ Y) [LocallyRinged空间.是开浸入 g]
  定义体: PresheafedSpace.IsOpenImmersion.comp f.1 g.1

Depends on / 依赖: IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.comp
-/
instance comp (g : Z ⟶ Y) [LocallyRingedSpace.IsOpenImmersion g] :
    LocallyRingedSpace.IsOpenImmersion (f ≫ g) :=
  PresheafedSpace.IsOpenImmersion.comp f.1 g.1

/--
Instance `mono` / 实例 `mono`

English:
instance mono
  signature: : Mono f
  body: LocallyRingedSpace.forgetToSheafedSpace.mono_of_mono_map (show Mono f.toShHom by infer_instance)

中文:
实例 mono
  签名: : 单态射 f
  定义体: LocallyRingedSpace.forgetToSheafedSpace.mono_of_mono_map (show Mono f.toShHom by infer_instance)

Depends on / 依赖: LocallyRingedSpace, LocallyRingedSpace.forgetToSheafedSpace.mono_of_mono_map, f.toShHom, forgetToSheafedSpace, infer_instance, mono_of_mono_map, toShHom
-/
instance mono : Mono f :=
  LocallyRingedSpace.forgetToSheafedSpace.mono_of_mono_map (show Mono f.toShHom by infer_instance)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SheafedSpace.IsOpenImmersion (LocallyRingedSpace.forgetToSheafedSpace.map f)
  body: H

中文:
实例 :
  签名: Sheafed空间.是开浸入 (LocallyRinged空间.forgetToSheafedSpace.map f)
  定义体: H
-/
instance : SheafedSpace.IsOpenImmersion (LocallyRingedSpace.forgetToSheafedSpace.map f) :=
  H

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `pullbackConeOfLeft` / `pullbackConeOfLeft` 的定义

English:
definition pullbackConeOfLeft
  signature: : PullbackCone f g
  body: by
  refine PullbackCone.mk ?_
      (Y.ofRestrict (TopCat.snd_isOpenEmbedding_of_left H.base_open g.base)) ?_
  · use PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftFst f.1 g.1
    intro x
    have := PresheafedSpace.stalkMap.congr_hom _ _
        (PresheafedSpace.IsOpenImmersion.pullback_cone_o

中文:
定义 pullbackConeOfLeft
  签名: : PullbackCone f g
  定义体: by
  refine PullbackCone.mk ?_
      (Y.ofRestrict (TopCat.snd_isOpenEmbedding_of_left H.base_open g.base)) ?_
  · use PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftFst f.1 g.1
    intro x
    have := PresheafedSpace.stalkMap.congr_hom _ _
        (PresheafedSpace.IsOpenImmersion.pullback_cone_o

Depends on / 依赖: H.base_open, IsIso.eq_inv_comp, IsOpenImmersion, LocallyRingedSpace, LocallyRingedSpace.Hom.ext, PresheafedSpace, PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftFst, PresheafedSpace.IsOpenImmersion.pullback_cone_of_left_condition, PresheafedSpace.stalkMap.comp, PresheafedSpace.stalkMap.congr_hom, PullbackCone, PullbackCone.mk, RingHom, RingHom.isLocalHom_comp, TopCat, TopCat.snd_isOpenEmbedding_of_left, Y.ofRestrict, base_open, congr_hom, eq_inv_comp
-/
def pullbackConeOfLeft : PullbackCone f g := by
  refine PullbackCone.mk ?_
      (Y.ofRestrict (TopCat.snd_isOpenEmbedding_of_left H.base_open g.base)) ?_
  · use PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftFst f.1 g.1
    intro x
    have := PresheafedSpace.stalkMap.congr_hom _ _
        (PresheafedSpace.IsOpenImmersion.pullback_cone_of_left_condition f.1 g.1) x
    rw [PresheafedSpace.stalkMap.comp]; rw [PresheafedSpace.stalkMap.comp] at this
    rw [← IsIso.eq_inv_comp] at this
    rw [this]
    dsimp
    apply RingHom.isLocalHom_comp
  · exact LocallyRingedSpace.Hom.ext'
        (PresheafedSpace.IsOpenImmersion.pullback_cone_of_left_condition _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LocallyRingedSpace.IsOpenImmersion (pullbackConeOfLeft f g).snd
  body: show PresheafedSpace.IsOpenImmersion (Y.toPresheafedSpace.ofRestrict _) by infer_instance

中文:
实例 :
  签名: LocallyRinged空间.是开浸入 (pullbackConeOfLeft f g).snd
  定义体: show PresheafedSpace.IsOpenImmersion (Y.toPresheafedSpace.ofRestrict _) by infer_instance

Depends on / 依赖: IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion, Y.toPresheafedSpace.ofRestrict, infer_instance, ofRestrict, toPresheafedSpace
-/
instance : LocallyRingedSpace.IsOpenImmersion (pullbackConeOfLeft f g).snd :=
  show PresheafedSpace.IsOpenImmersion (Y.toPresheafedSpace.ofRestrict _) by infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `pullbackConeOfLeftIsLimit` / `pullbackConeOfLeftIsLimit` 的定义

English:
definition pullbackConeOfLeftIsLimit
  signature: : IsLimit (pullbackConeOfLeft f g)
  body: PullbackCone.isLimitAux' _ fun s => by
    refine ⟨LocallyRingedSpace.Hom.mk (PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift
        f.1 g.1 (PullbackCone.mk _ _ (congr_arg LocallyRingedSpace.Hom.toHom s.condition))) ?_,
      LocallyRingedSpace.Hom.ext'
        (PresheafedSpace.IsOpenImmers

中文:
定义 pullbackConeOfLeftIsLimit
  签名: : 是极限 (pullbackConeOfLeft f g)
  定义体: PullbackCone.isLimitAux' _ fun s => by
    refine ⟨LocallyRingedSpace.Hom.mk (PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift
        f.1 g.1 (PullbackCone.mk _ _ (congr_arg LocallyRingedSpace.Hom.toHom s.condition))) ?_,
      LocallyRingedSpace.Hom.ext'
        (PresheafedSpace.IsOpenImmers

Depends on / 依赖: IsOpenImmersion, LocallyRingedSpace, LocallyRingedSpace.Hom.ext, LocallyRingedSpace.Hom.mk, LocallyRingedSpace.Hom.toHom, PresheafedSpace, PresheafedSpace.IsOpe, PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift, PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_fst, PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_snd, PresheafedSpace.stalkMap.congr_hom, PullbackCone, PullbackCone.isLimitAux, PullbackCone.mk, condition, congr_arg, congr_hom, isLimitAux, pullbackConeOfLeftLift, pullbackConeOfLeftLift_fst
-/
def pullbackConeOfLeftIsLimit : IsLimit (pullbackConeOfLeft f g) :=
  PullbackCone.isLimitAux' _ fun s => by
    refine ⟨LocallyRingedSpace.Hom.mk (PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift
        f.1 g.1 (PullbackCone.mk _ _ (congr_arg LocallyRingedSpace.Hom.toHom s.condition))) ?_,
      LocallyRingedSpace.Hom.ext'
        (PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_fst f.1 g.1 _),
      LocallyRingedSpace.Hom.ext'
          (PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_snd f.1 g.1 _), ?_⟩
    · intro x
      have :=
        PresheafedSpace.stalkMap.congr_hom _ _
          (PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_snd f.1 g.1
            (PullbackCone.mk s.fst.1 s.snd.1
              (congr_arg LocallyRingedSpace.Hom.toHom s.condition)))
          x
      change _ = _ ≫ s.snd.1.stalkMap x at this
      rw [PresheafedSpace.stalkMap.comp]; rw [← IsIso.eq_inv_comp] at this
      rw [this]
      infer_instance
    · intro m _ h₂
      rw [← cancel_mono (pullbackConeOfLeft f g).snd]
exact h₂.trans LocallyRingedSpace.Hom.ext'
        (PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_snd f.1 g.1 <|
PullbackCone.mk s.fst.1 s.snd.1 congr_arg
            LocallyRingedSpace.Hom.toHom s.condition).symm

/--
Instance `hasPullback_of_left` / 实例 `hasPullback_of_left`

English:
instance hasPullback_of_left
  signature: : HasPullback f g
  body: ⟨⟨⟨_, pullbackConeOfLeftIsLimit f g⟩⟩⟩

中文:
实例 hasPullback_of_left
  签名: : HasPullback f g
  定义体: ⟨⟨⟨_, pullbackConeOfLeftIsLimit f g⟩⟩⟩

Depends on / 依赖: pullbackConeOfLeftIsLimit
-/
instance hasPullback_of_left : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfLeftIsLimit f g⟩⟩⟩

/--
Instance `hasPullback_of_right` / 实例 `hasPullback_of_right`

English:
instance hasPullback_of_right
  signature: : HasPullback g f
  body: hasPullback_symmetry f g

中文:
实例 hasPullback_of_right
  签名: : HasPullback g f
  定义体: hasPullback_symmetry f g

Depends on / 依赖: hasPullback_symmetry
-/
instance hasPullback_of_right : HasPullback g f :=
  hasPullback_symmetry f g

set_option backward.isDefEq.respectTransparency false in
/--
Instance `pullback_snd_of_left` / 实例 `pullback_snd_of_left`

English:
instance pullback_snd_of_left
  signature: :
  body: by
  delta pullback.snd
  rw [← limit.isoLimitCone_hom_π ⟨_]; rw [pullbackConeOfLeftIsLimit f g⟩ WalkingCospan.right]
  infer_instance

中文:
实例 pullback_snd_of_left
  签名: :
  定义体: by
  delta pullback.snd
  rw [← limit.isoLimitCone_hom_π ⟨_]; rw [pullbackConeOfLeftIsLimit f g⟩ WalkingCospan.right]
  infer_instance

Depends on / 依赖: WalkingCospan, WalkingCospan.right, infer_instance, limit.isoLimitCone_hom_, pullback, pullback.snd, pullbackConeOfLeftIsLimit
-/
instance pullback_snd_of_left :
    LocallyRingedSpace.IsOpenImmersion (pullback.snd f g) := by
  delta pullback.snd
  rw [← limit.isoLimitCone_hom_π ⟨_]; rw [pullbackConeOfLeftIsLimit f g⟩ WalkingCospan.right]
  infer_instance

/--
Instance `pullback_fst_of_right` / 实例 `pullback_fst_of_right`

English:
instance pullback_fst_of_right
  signature: :
  body: by
  rw [← pullbackSymmetry_hom_comp_snd]
  infer_instance

中文:
实例 pullback_fst_of_right
  签名: :
  定义体: by
  rw [← pullbackSymmetry_hom_comp_snd]
  infer_instance

Depends on / 依赖: infer_instance, pullbackSymmetry_hom_comp_snd
-/
instance pullback_fst_of_right :
    LocallyRingedSpace.IsOpenImmersion (pullback.fst g f) := by
  rw [← pullbackSymmetry_hom_comp_snd]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Instance `pullback_to_base_isOpenImmersion` / 实例 `pullback_to_base_isOpenImmersion`

English:
instance pullback_to_base_isOpenImmersion
  signature: [LocallyRingedSpace.IsOpenImmersion g]
  body: by
  rw [← limit.w (cospan f g) WalkingCospan.Hom.inl]; rw [cospan_map_inl]
  infer_instance

中文:
实例 pullback_to_base_isOpenImmersion
  签名: [LocallyRinged空间.是开浸入 g]
  定义体: by
  rw [← limit.w (cospan f g) WalkingCospan.Hom.inl]; rw [cospan_map_inl]
  infer_instance

Depends on / 依赖: WalkingCospan, WalkingCospan.Hom.inl, cospan, cospan_map_inl, infer_instance, limit.w
-/
instance pullback_to_base_isOpenImmersion [LocallyRingedSpace.IsOpenImmersion g] :
    LocallyRingedSpace.IsOpenImmersion (limit.π (cospan f g) WalkingCospan.one) := by
  rw [← limit.w (cospan f g) WalkingCospan.Hom.inl]; rw [cospan_map_inl]
  infer_instance

/--
Instance `forget_preservesPullbackOfLeft` / 实例 `forget_preservesPullbackOfLeft`

English:
instance forget_preservesPullbackOfLeft
  signature: :
  body: preservesLimit_of_preserves_limit_cone (pullbackConeOfLeftIsLimit f g) by
    apply (isLimitMapConePullbackConeEquiv _ _).symm.toFun
    apply isLimitOfIsLimitPullbackConeMap SheafedSpace.forgetToPresheafedSpace
    exact PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit f.1 g.1

中文:
实例 forget_preservesPullbackOfLeft
  签名: :
  定义体: preservesLimit_of_preserves_limit_cone (pullbackConeOfLeftIsLimit f g) by
    apply (isLimitMapConePullbackConeEquiv _ _).symm.toFun
    apply isLimitOfIsLimitPullbackConeMap SheafedSpace.forgetToPresheafedSpace
    exact PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit f.1 g.1

Depends on / 依赖: IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit, SheafedSpace, SheafedSpace.forgetToPresheafedSpace, forgetToPresheafedSpace, isLimitMapConePullbackConeEquiv, isLimitOfIsLimitPullbackConeMap, preservesLimit_of_preserves_limit_cone, pullbackConeOfLeftIsLimit, symm.toFun
-/
instance forget_preservesPullbackOfLeft :
    PreservesLimit (cospan f g) LocallyRingedSpace.forgetToSheafedSpace :=
preservesLimit_of_preserves_limit_cone (pullbackConeOfLeftIsLimit f g) by
    apply (isLimitMapConePullbackConeEquiv _ _).symm.toFun
    apply isLimitOfIsLimitPullbackConeMap SheafedSpace.forgetToPresheafedSpace
    exact PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit f.1 g.1

/--
Instance `forgetToPresheafedSpace_preservesPullback_of_left` / 实例 `forgetToPresheafedSpace_preservesPullback_of_left`

English:
instance forgetToPresheafedSpace_preservesPullback_of_left
  signature: :
  body: preservesLimit_of_preserves_limit_cone (pullbackConeOfLeftIsLimit f g) by
    apply (isLimitMapConePullbackConeEquiv _ _).symm.toFun
    exact PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit f.1 g.1

中文:
实例 forgetToPresheafedSpace_preservesPullback_of_left
  签名: :
  定义体: preservesLimit_of_preserves_limit_cone (pullbackConeOfLeftIsLimit f g) by
    apply (isLimitMapConePullbackConeEquiv _ _).symm.toFun
    exact PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit f.1 g.1

Depends on / 依赖: IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit, isLimitMapConePullbackConeEquiv, preservesLimit_of_preserves_limit_cone, pullbackConeOfLeftIsLimit, symm.toFun
-/
instance forgetToPresheafedSpace_preservesPullback_of_left :
    PreservesLimit (cospan f g)
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) :=
preservesLimit_of_preserves_limit_cone (pullbackConeOfLeftIsLimit f g) by
    apply (isLimitMapConePullbackConeEquiv _ _).symm.toFun
    exact PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit f.1 g.1

/--
Instance `forgetToPresheafedSpacePreservesOpenImmersion` / 实例 `forgetToPresheafedSpacePreservesOpenImmersion`

English:
instance forgetToPresheafedSpacePreservesOpenImmersion
  signature: :
  body: H

中文:
实例 forgetToPresheafedSpacePreservesOpenImmersion
  签名: :
  定义体: H
-/
instance forgetToPresheafedSpacePreservesOpenImmersion :
    PresheafedSpace.IsOpenImmersion
      ((LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace).map f) :=
  H

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `forgetToTop_preservesPullback_of_left` / 实例 `forgetToTop_preservesPullback_of_left`

English:
instance forgetToTop_preservesPullback_of_left
  signature: :
  body: by
change PreservesLimit _
    (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) ⋙
    PresheafedSpace.forget _
  apply +allowSynthFailures Limits.comp_preservesLimit
  apply +allowSynthFailures preservesLimit_of_iso_diagram
  · exact (diagramIsoCospan _).symm
  dsimp


中文:
实例 forgetToTop_preservesPullback_of_left
  签名: :
  定义体: by
change PreservesLimit _
    (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) ⋙
    PresheafedSpace.forget _
  apply +allowSynthFailures Limits.comp_preservesLimit
  apply +allowSynthFailures preservesLimit_of_iso_diagram
  · exact (diagramIsoCospan _).symm
  dsimp


Depends on / 依赖: Limits, Limits.comp_preservesLimit, LocallyRingedSpace, LocallyRingedSpace.forgetToSheafedSpace, PreservesLimit, PresheafedSpace, PresheafedSpace.forget, SheafedSpace, SheafedSpace.forgetToPresheafedSpace, allowSynthFailures, comp_preservesLimit, diagramIsoCospan, forget, forgetToPresheafedSpace, forgetToSheafedSpace, infer_instance, preservesLimit_of_iso_diagram
-/
instance forgetToTop_preservesPullback_of_left :
    PreservesLimit (cospan f g)
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget _) := by
change PreservesLimit _
    (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) ⋙
    PresheafedSpace.forget _
  apply +allowSynthFailures Limits.comp_preservesLimit
  apply +allowSynthFailures preservesLimit_of_iso_diagram
  · exact (diagramIsoCospan _).symm
  dsimp
  infer_instance

/--
Instance `forget_reflectsPullback_of_left` / 实例 `forget_reflectsPullback_of_left`

English:
instance forget_reflectsPullback_of_left
  signature: :
  body: reflectsLimit_of_reflectsIsomorphisms _ _

中文:
实例 forget_reflectsPullback_of_left
  签名: :
  定义体: reflectsLimit_of_reflectsIsomorphisms _ _

Depends on / 依赖: reflectsLimit_of_reflectsIsomorphisms
-/
instance forget_reflectsPullback_of_left :
    ReflectsLimit (cospan f g) LocallyRingedSpace.forgetToSheafedSpace :=
  reflectsLimit_of_reflectsIsomorphisms _ _

/--
Instance `forget_preservesPullback_of_right` / 实例 `forget_preservesPullback_of_right`

English:
instance forget_preservesPullback_of_right
  signature: :
  body: preservesPullback_symmetry _ _ _

中文:
实例 forget_preservesPullback_of_right
  签名: :
  定义体: preservesPullback_symmetry _ _ _

Depends on / 依赖: preservesPullback_symmetry
-/
instance forget_preservesPullback_of_right :
    PreservesLimit (cospan g f) LocallyRingedSpace.forgetToSheafedSpace :=
  preservesPullback_symmetry _ _ _

/--
Instance `forgetToPresheafedSpace_preservesPullback_of_right` / 实例 `forgetToPresheafedSpace_preservesPullback_of_right`

English:
instance forgetToPresheafedSpace_preservesPullback_of_right
  signature: :
  body: preservesPullback_symmetry _ _ _

中文:
实例 forgetToPresheafedSpace_preservesPullback_of_right
  签名: :
  定义体: preservesPullback_symmetry _ _ _

Depends on / 依赖: preservesPullback_symmetry
-/
instance forgetToPresheafedSpace_preservesPullback_of_right :
    PreservesLimit (cospan g f)
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) :=
  preservesPullback_symmetry _ _ _

/--
Instance `forget_reflectsPullback_of_right` / 实例 `forget_reflectsPullback_of_right`

English:
instance forget_reflectsPullback_of_right
  signature: :
  body: reflectsLimit_of_reflectsIsomorphisms _ _

中文:
实例 forget_reflectsPullback_of_right
  签名: :
  定义体: reflectsLimit_of_reflectsIsomorphisms _ _

Depends on / 依赖: reflectsLimit_of_reflectsIsomorphisms
-/
instance forget_reflectsPullback_of_right :
    ReflectsLimit (cospan g f) LocallyRingedSpace.forgetToSheafedSpace :=
  reflectsLimit_of_reflectsIsomorphisms _ _

/--
Instance `forgetToPresheafedSpace_reflectsPullback_of_left` / 实例 `forgetToPresheafedSpace_reflectsPullback_of_left`

English:
instance forgetToPresheafedSpace_reflectsPullback_of_left
  signature: :
  body: reflectsLimit_of_reflectsIsomorphisms _ _

中文:
实例 forgetToPresheafedSpace_reflectsPullback_of_left
  签名: :
  定义体: reflectsLimit_of_reflectsIsomorphisms _ _

Depends on / 依赖: reflectsLimit_of_reflectsIsomorphisms
-/
instance forgetToPresheafedSpace_reflectsPullback_of_left :
    ReflectsLimit (cospan f g)
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) :=
  reflectsLimit_of_reflectsIsomorphisms _ _

/--
Instance `forgetToPresheafedSpace_reflectsPullback_of_right` / 实例 `forgetToPresheafedSpace_reflectsPullback_of_right`

English:
instance forgetToPresheafedSpace_reflectsPullback_of_right
  signature: :
  body: reflectsLimit_of_reflectsIsomorphisms _ _

中文:
实例 forgetToPresheafedSpace_reflectsPullback_of_right
  签名: :
  定义体: reflectsLimit_of_reflectsIsomorphisms _ _

Depends on / 依赖: reflectsLimit_of_reflectsIsomorphisms
-/
instance forgetToPresheafedSpace_reflectsPullback_of_right :
    ReflectsLimit (cospan g f)
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) :=
  reflectsLimit_of_reflectsIsomorphisms _ _

/--
theorem `pullback_snd_isIso_of_range_subset` / 定理 `pullback_snd_isIso_of_range_subset`

English:
theorem pullback_snd_isIso_of_range_subset
  given: (H' : Set.range g.base subseteq Set.range f.base)
  proof: by
  apply +allowSynthFailures Functor.ReflectsIsomorphisms.reflects
    (F := LocallyRingedSpace.forgetToSheafedSpace)
  apply +allowSynthFailures Functor.ReflectsIsomorphisms.reflects
    (F := SheafedSpace.forgetToPresheafedSpace)
  erw [← PreservesPullback.iso_hom_snd
      (LocallyRingedSpace.f

中文:
定理 pullback_snd_isIso_of_range_subset
  条件: (H' : 集合.range g.base subseteq 集合.range f.base)
  证明: by
  apply +allowSynthFailures Functor.ReflectsIsomorphisms.reflects
    (F := LocallyRingedSpace.forgetToSheafedSpace)
  apply +allowSynthFailures Functor.ReflectsIsomorphisms.reflects
    (F := SheafedSpace.forgetToPresheafedSpace)
  erw [← PreservesPullback.iso_hom_snd
      (LocallyRingedSpace.f

Depends on / 依赖: Functor, Functor.ReflectsIsomorphisms.reflects, LocallyRingedSpace, LocallyRingedSpace.forgetToSheafedSpace, PreservesPullback, PreservesPullback.iso_hom_snd, ReflectsIsomorphisms, SheafedSpace, SheafedSpace.forgetToPresheafedSpace, allowSynthFailures, forgetToPresheafedSpace, forgetToSheafedSpace, iso_hom_snd, reflects
-/
theorem pullback_snd_isIso_of_range_subset (H' : Set.range g.base subseteq Set.range f.base) :
    IsIso (pullback.snd f g) := by
  apply +allowSynthFailures Functor.ReflectsIsomorphisms.reflects
    (F := LocallyRingedSpace.forgetToSheafedSpace)
  apply +allowSynthFailures Functor.ReflectsIsomorphisms.reflects
    (F := SheafedSpace.forgetToPresheafedSpace)
  erw [← PreservesPullback.iso_hom_snd
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) f g]
  -- Porting note: was `inferInstance`
exact IsIso.comp_isIso' inferInstance
    PresheafedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset _ _ H'

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (H' : Set.range g.base subseteq Set.range f.base)
  body: have := pullback_snd_isIso_of_range_subset f g H'
  inv (pullback.snd f g) ≫ pullback.fst _ _

@[simp, reassoc]

中文:
定义 lift
  签名: (H' : 集合.range g.base subseteq 集合.range f.base)
  定义体: have := pullback_snd_isIso_of_range_subset f g H'
  inv (pullback.snd f g) ≫ pullback.fst _ _

@[simp, reassoc]

Depends on / 依赖: pullback, pullback.fst, pullback.snd, pullback_snd_isIso_of_range_subset
-/
def lift (H' : Set.range g.base subseteq Set.range f.base) : Y ⟶ X :=
  have := pullback_snd_isIso_of_range_subset f g H'
  inv (pullback.snd f g) ≫ pullback.fst _ _

@[simp, reassoc]
/--
theorem `lift_fac` / 定理 `lift_fac`

English:
theorem lift_fac
  given: (H' : Set.range g.base subseteq Set.range f.base)
  statement: lift f g H' ≫ f = g
  proof: by
  simp [lift, pullback.condition]

中文:
定理 lift_fac
  条件: (H' : 集合.range g.base subseteq 集合.range f.base)
  结论: lift f g H' ≫ f = g
  证明: by
  simp [lift, pullback.condition]

Depends on / 依赖: condition, pullback, pullback.condition
-/
theorem lift_fac (H' : Set.range g.base subseteq Set.range f.base) : lift f g H' ≫ f = g := by
  simp [lift, pullback.condition]

/--
theorem `lift_uniq` / 定理 `lift_uniq`

English:
theorem lift_uniq
  given: (H' : Set.range g.base subseteq Set.range f.base) (l : Y ⟶ X) (hl : l ≫ f = g)
  proof: by rw [← cancel_mono f, hl, lift_fac]

中文:
定理 lift_uniq
  条件: (H' : 集合.range g.base subseteq 集合.range f.base) (l : Y ⟶ X) (hl : l ≫ f = g)
  证明: by rw [← cancel_mono f, hl, lift_fac]

Depends on / 依赖: cancel_mono, lift_fac
-/
theorem lift_uniq (H' : Set.range g.base subseteq Set.range f.base) (l : Y ⟶ X) (hl : l ≫ f = g) :
    l = lift f g H' := by rw [← cancel_mono f, hl, lift_fac]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lift_range` / 定理 `lift_range`

English:
theorem lift_range
  given: (H' : Set.range g.base subseteq Set.range f.base)
  proof: by
  have := pullback_snd_isIso_of_range_subset f g H'
  dsimp only [lift]
  have : _ = (pullback.fst f g).base :=
    PreservesPullback.iso_hom_fst
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget _) f g
  rw [LocallyRingedSpace.comp_base]; rw [← this]; rw [← Category.assoc]; rw

中文:
定理 lift_range
  条件: (H' : 集合.range g.base subseteq 集合.range f.base)
  证明: by
  have := pullback_snd_isIso_of_range_subset f g H'
  dsimp only [lift]
  have : _ = (pullback.fst f g).base :=
    PreservesPullback.iso_hom_fst
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget _) f g
  rw [LocallyRingedSpace.comp_base]; rw [← this]; rw [← Category.assoc]; rw

Depends on / 依赖: Category, Category.assoc, LocallyRingedSpace, LocallyRingedSpace.comp_base, LocallyRingedSpace.forgetToSheafedSpace, PreservesPullback, PreservesPullback.iso_hom_fst, Set.image_univ, Set.range_comp, Set.range_eq_univ.mpr, SheafedSpace, SheafedSpace.forget, TopCat, TopCat.coe_comp, TopCat.pullback_fst_range, coe_comp, comp_base, eq.symm, forget, forgetToSheafedSpace
-/
theorem lift_range (H' : Set.range g.base subseteq Set.range f.base) :
    Set.range (lift f g H').base = f.base ⁻¹' Set.range g.base := by
  have := pullback_snd_isIso_of_range_subset f g H'
  dsimp only [lift]
  have : _ = (pullback.fst f g).base :=
    PreservesPullback.iso_hom_fst
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget _) f g
  rw [LocallyRingedSpace.comp_base]; rw [← this]; rw [← Category.assoc]; rw [TopCat.coe_comp]; rw [Set.range_comp]; rw [Set.range_eq_univ.mpr]; rw [Set.image_univ]
  · rw [TopCat.pullback_fst_range]
    ext
    constructor
    · rintro ⟨y, eq⟩; exact ⟨y, eq.symm⟩
    · rintro ⟨y, eq⟩; exact ⟨y, eq.symm⟩
  · rw [← TopCat.epi_iff_surjective, show (inv (pullback.snd f g)).base = _ from
        (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget _).map_inv _]
    infer_instance

end Pullback

/--
Definition of `isoRestrict` / `isoRestrict` 的定义

English:
definition isoRestrict
  signature: {X Y : LocallyRingedSpace} (f : X ⟶ Y)
  body: LocallyRingedSpace.isoOfSheafedSpaceIso
    SheafedSpace.fullyFaithfulForgetToPresheafedSpace.preimageIso
      (PresheafedSpace.IsOpenImmersion.isoRestrict f.1)

中文:
定义 isoRestrict
  签名: {X Y : LocallyRinged空间} (f : X ⟶ Y)
  定义体: LocallyRingedSpace.isoOfSheafedSpaceIso
    SheafedSpace.fullyFaithfulForgetToPresheafedSpace.preimageIso
      (PresheafedSpace.IsOpenImmersion.isoRestrict f.1)

Depends on / 依赖: IsOpenImmersion, LocallyRingedSpace, LocallyRingedSpace.isoOfSheafedSpaceIso, PresheafedSpace, PresheafedSpace.IsOpenImmersion.isoRestrict, SheafedSpace, SheafedSpace.fullyFaithfulForgetToPresheafedSpace.preimageIso, fullyFaithfulForgetToPresheafedSpace, isoOfSheafedSpaceIso, isoRestrict, preimageIso
-/
noncomputable def isoRestrict {X Y : LocallyRingedSpace} (f : X ⟶ Y)
    [H : LocallyRingedSpace.IsOpenImmersion f] :
    X ≅ Y.restrict H.base_open :=
LocallyRingedSpace.isoOfSheafedSpaceIso
    SheafedSpace.fullyFaithfulForgetToPresheafedSpace.preimageIso
      (PresheafedSpace.IsOpenImmersion.isoRestrict f.1)

/--
Definition of `opensFunctor` / `opensFunctor` 的定义

English:
abbreviation opensFunctor
  signature: {X Y : LocallyRingedSpace} (f : X ⟶ Y)
  body: H.base_open.functor

中文:
缩写 opensFunctor
  签名: {X Y : LocallyRinged空间} (f : X ⟶ Y)
  定义体: H.base_open.functor

Depends on / 依赖: H.base_open.functor, base_open, functor
-/
abbrev opensFunctor {X Y : LocallyRingedSpace} (f : X ⟶ Y)
    [H : LocallyRingedSpace.IsOpenImmersion f] : Opens X ⥤ Opens Y :=
  H.base_open.functor

section OfStalkIso

/--
theorem `of_stalk_iso` / 定理 `of_stalk_iso`

English:
theorem of_stalk_iso
  statement: {X Y : LocallyRingedSpace} (f : X ⟶ Y) (hf : IsOpenEmbedding f.base)
  proof: SheafedSpace.IsOpenImmersion.of_stalk_iso _ hf (H := stalk_iso)

中文:
定理 of_stalk_iso
  结论: {X Y : LocallyRinged空间} (f : X ⟶ Y) (hf : 是开嵌入 f.base)
  证明: SheafedSpace.IsOpenImmersion.of_stalk_iso _ hf (H := stalk_iso)

Depends on / 依赖: IsOpenImmersion, SheafedSpace, SheafedSpace.IsOpenImmersion.of_stalk_iso, of_stalk_iso, stalk_iso
-/
theorem of_stalk_iso {X Y : LocallyRingedSpace} (f : X ⟶ Y) (hf : IsOpenEmbedding f.base)
    [stalk_iso : forall x : X.1, IsIso (f.stalkMap x)] :
    LocallyRingedSpace.IsOpenImmersion f :=
  SheafedSpace.IsOpenImmersion.of_stalk_iso _ hf (H := stalk_iso)

end OfStalkIso

section

variable {X Y : LocallyRingedSpace} (f : X ⟶ Y) [H : IsOpenImmersion f]

@[reassoc (attr := simp)]
/--
theorem `isoRestrict_hom_ofRestrict` / 定理 `isoRestrict_hom_ofRestrict`

English:
theorem isoRestrict_hom_ofRestrict
  statement: (isoRestrict f).hom ≫ Y.ofRestrict _ = f
  proof: by
  apply LocallyRingedSpace.forgetToSheafedSpace.map_injective
  exact SheafedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict f.toShHom

@[reassoc (attr := simp)]

中文:
定理 isoRestrict_hom_ofRestrict
  结论: (isoRestrict f).hom ≫ Y.ofRestrict _ = f
  证明: by
  apply LocallyRingedSpace.forgetToSheafedSpace.map_injective
  exact SheafedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict f.toShHom

@[reassoc (attr := simp)]

Depends on / 依赖: IsOpenImmersion, LocallyRingedSpace, LocallyRingedSpace.forgetToSheafedSpace.map_injective, SheafedSpace, SheafedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict, f.toShHom, forgetToSheafedSpace, isoRestrict_hom_ofRestrict, map_injective, toShHom
-/
theorem isoRestrict_hom_ofRestrict : (isoRestrict f).hom ≫ Y.ofRestrict _ = f := by
  apply LocallyRingedSpace.forgetToSheafedSpace.map_injective
  exact SheafedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict f.toShHom

@[reassoc (attr := simp)]
/--
theorem `isoRestrict_inv_ofRestrict` / 定理 `isoRestrict_inv_ofRestrict`

English:
theorem isoRestrict_inv_ofRestrict
  statement: (isoRestrict f).inv ≫ f = Y.ofRestrict _
  proof: by
  simp only [← isoRestrict_hom_ofRestrict f, Iso.inv_hom_id_assoc]

中文:
定理 isoRestrict_inv_ofRestrict
  结论: (isoRestrict f).inv ≫ f = Y.ofRestrict _
  证明: by
  simp only [← isoRestrict_hom_ofRestrict f, Iso.inv_hom_id_assoc]

Depends on / 依赖: Iso.inv_hom_id_assoc, inv_hom_id_assoc, isoRestrict_hom_ofRestrict
-/
theorem isoRestrict_inv_ofRestrict : (isoRestrict f).inv ≫ f = Y.ofRestrict _ := by
  simp only [← isoRestrict_hom_ofRestrict f, Iso.inv_hom_id_assoc]
/--
Definition of `invApp` / `invApp` 的定义

English:
definition invApp
  signature: (U : Opens X)
  body: PresheafedSpace.IsOpenImmersion.invApp f.1 U

#adaptation_note

中文:
定义 invApp
  签名: (U : Opens X)
  定义体: PresheafedSpace.IsOpenImmersion.invApp f.1 U

#adaptation_note

Depends on / 依赖: IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.invApp, invApp
-/
noncomputable def invApp (U : Opens X) :
    X.presheaf.obj (op U) ⟶ Y.presheaf.obj (op (opensFunctor f |>.obj U)) :=
  PresheafedSpace.IsOpenImmersion.invApp f.1 U

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
theorem `inv_naturality` / 定理 `inv_naturality`

English:
theorem inv_naturality
  given: {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
  proof: PresheafedSpace.IsOpenImmersion.inv_naturality f.1 i

中文:
定理 inv_naturality
  条件: {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
  证明: PresheafedSpace.IsOpenImmersion.inv_naturality f.1 i

Depends on / 依赖: IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.inv_naturality, inv_naturality
-/
theorem inv_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    X.presheaf.map i ≫ H.invApp _ (unop V) =
      H.invApp _ (unop U) ≫ Y.presheaf.map (opensFunctor f |>.op.map i) :=
  PresheafedSpace.IsOpenImmersion.inv_naturality f.1 i

set_option backward.isDefEq.respectTransparency false in
instance (U : Opens X) : IsIso (H.invApp _ U) := by delta invApp; infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `inv_invApp` / 定理 `inv_invApp`

English:
theorem inv_invApp
  given: (U : Opens X)
  proof: PresheafedSpace.IsOpenImmersion.inv_invApp f.1 U

中文:
定理 inv_invApp
  条件: (U : Opens X)
  证明: PresheafedSpace.IsOpenImmersion.inv_invApp f.1 U

Depends on / 依赖: H.base_open.injective, Set.preimage_image_eq, base_open, injective, preimage_image_eq
-/
theorem inv_invApp (U : Opens X) :
    inv (H.invApp _ U) =
      f.c.app (op (opensFunctor f |>.obj U)) ≫ X.presheaf.map
        (eqToHom (by
          have := Set.preimage_image_eq U.1 H.base_open.injective
          dsimp at this
          simp [Opens.map_def, this])) :=
  PresheafedSpace.IsOpenImmersion.inv_invApp f.1 U

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `invApp_app` / 定理 `invApp_app`

English:
theorem invApp_app
  given: (U : Opens X)
  proof: PresheafedSpace.IsOpenImmersion.invApp_app f.1 U

中文:
定理 invApp_app
  条件: (U : Opens X)
  证明: PresheafedSpace.IsOpenImmersion.invApp_app f.1 U

Depends on / 依赖: H.base_open.injective, Set.preimage_image_eq, base_open, injective, preimage_image_eq
-/
theorem invApp_app (U : Opens X) :
    H.invApp _ U ≫ f.c.app (op (opensFunctor f |>.obj U)) = X.presheaf.map
      (eqToHom (by
        have := Set.preimage_image_eq U.1 H.base_open.injective
        dsimp at this
        simp [Opens.map_def, this])) :=
  PresheafedSpace.IsOpenImmersion.invApp_app f.1 U

attribute [elementwise nosimp] invApp_app

@[reassoc (attr := simp)]
/--
theorem `app_invApp` / 定理 `app_invApp`

English:
theorem app_invApp
  given: (U : Opens Y)
  proof: PresheafedSpace.IsOpenImmersion.app_invApp f.1 U

中文:
定理 app_invApp
  条件: (U : Opens Y)
  证明: PresheafedSpace.IsOpenImmersion.app_invApp f.1 U

Depends on / 依赖: IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.app_invApp, app_invApp
-/
theorem app_invApp (U : Opens Y) :
    f.c.app (op U) ≫ H.invApp _ ((Opens.map f.base).obj U) =
      Y.presheaf.map
        ((homOfLE (Set.image_preimage_subset f.base U.1)).op :
          op U ⟶ op (opensFunctor f |>.obj ((Opens.map f.base).obj U))) :=
  PresheafedSpace.IsOpenImmersion.app_invApp f.1 U

/-- A variant of `app_inv_app` that gives an `eqToHom` instead of `homOfLe`. -/
@[reassoc]
/--
theorem `app_inv_app'` / 定理 `app_inv_app'`

English:
theorem app_inv_app'
  given: (U : Opens Y) (hU : (U : Set Y) subseteq Set.range f.base)
  proof: PresheafedSpace.IsOpenImmersion.app_invApp f.1 U

中文:
定理 app_inv_app'
  条件: (U : Opens Y) (hU : (U : 集合 Y) subseteq 集合.range f.base)
  证明: PresheafedSpace.IsOpenImmersion.app_invApp f.1 U

Depends on / 依赖: f.base
-/
theorem app_inv_app' (U : Opens Y) (hU : (U : Set Y) subseteq Set.range f.base) :
    f.c.app (op U) ≫ H.invApp _ ((Opens.map f.base).obj U) =
      Y.presheaf.map
        (eqToHom <|
le_antisymm (Set.image_preimage_subset f.base U.1)
              (Set.image_preimage_eq_inter_range (f := f.base) (t := U.1)).symm ▸
                Set.subset_inter_iff.mpr ⟨fun _ h => h, hU⟩).op :=
  PresheafedSpace.IsOpenImmersion.app_invApp f.1 U

/--
Instance `ofRestrict` / 实例 `ofRestrict`

English:
instance ofRestrict
  signature: {X : TopCat.{w}} (Y : LocallyRingedSpace) {f : X ⟶ Y.carrier}
  body: PresheafedSpace.IsOpenImmersion.ofRestrict _ hf

@[elementwise, simp]

中文:
实例 ofRestrict
  签名: {X : 顶元素范畴.{w}} (Y : LocallyRinged空间) {f : X ⟶ Y.carrier}
  定义体: PresheafedSpace.IsOpenImmersion.ofRestrict _ hf

@[elementwise, simp]

Depends on / 依赖: IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.ofRestrict, ofRestrict
-/
instance ofRestrict {X : TopCat.{w}} (Y : LocallyRingedSpace) {f : X ⟶ Y.carrier}
    (hf : IsOpenEmbedding f) : IsOpenImmersion (Y.ofRestrict hf) :=
  PresheafedSpace.IsOpenImmersion.ofRestrict _ hf

@[elementwise, simp]
/--
theorem `ofRestrict_invApp` / 定理 `ofRestrict_invApp`

English:
theorem ofRestrict_invApp
  statement: (X : LocallyRingedSpace) {Y : TopCat.{w}}
  proof: PresheafedSpace.IsOpenImmersion.ofRestrict_invApp _ h U

中文:
定理 ofRestrict_invApp
  结论: (X : LocallyRinged空间) {Y : 顶元素范畴.{w}}
  证明: PresheafedSpace.IsOpenImmersion.ofRestrict_invApp _ h U

Depends on / 依赖: IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.ofRestrict_invApp, ofRestrict_invApp
-/
theorem ofRestrict_invApp (X : LocallyRingedSpace) {Y : TopCat.{w}}
    {f : Y ⟶ TopCat.of X.carrier} (h : IsOpenEmbedding f) (U : Opens (X.restrict h).carrier) :
    (LocallyRingedSpace.IsOpenImmersion.ofRestrict X h).invApp _ U = 𝟙 _ :=
  PresheafedSpace.IsOpenImmersion.ofRestrict_invApp _ h U

/--
Instance `stalk_iso` / 实例 `stalk_iso`

English:
instance stalk_iso
  signature: (x : X)
  body: PresheafedSpace.IsOpenImmersion.stalk_iso f.1 x

中文:
实例 stalk_iso
  签名: (x : X)
  定义体: PresheafedSpace.IsOpenImmersion.stalk_iso f.1 x

Depends on / 依赖: IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.stalk_iso, stalk_iso
-/
instance stalk_iso (x : X) : IsIso (f.stalkMap x) :=
  PresheafedSpace.IsOpenImmersion.stalk_iso f.1 x

/--
theorem `to_iso` / 定理 `to_iso`

English:
theorem to_iso
  given: [Epi f.base]
  statement: IsIso f
  proof: by
  rw [← isIso_iff_of_reflects_iso _ LocallyRingedSpace.forgetToSheafedSpace]
  have : Epi (forgetToSheafedSpace.map f).hom.base := by assumption
  apply SheafedSpace.IsOpenImmersion.to_iso

中文:
定理 to_iso
  条件: [满态射 f.base]
  结论: 是同构 f
  证明: by
  rw [← isIso_iff_of_reflects_iso _ LocallyRingedSpace.forgetToSheafedSpace]
  have : Epi (forgetToSheafedSpace.map f).hom.base := by assumption
  apply SheafedSpace.IsOpenImmersion.to_iso

Depends on / 依赖: IsOpenImmersion, LocallyRingedSpace, LocallyRingedSpace.forgetToSheafedSpace, SheafedSpace, SheafedSpace.IsOpenImmersion.to_iso, forgetToSheafedSpace, forgetToSheafedSpace.map, hom.base, isIso_iff_of_reflects_iso, to_iso
-/
theorem to_iso [Epi f.base] : IsIso f := by
  rw [← isIso_iff_of_reflects_iso _ LocallyRingedSpace.forgetToSheafedSpace]
  have : Epi (forgetToSheafedSpace.map f).hom.base := by assumption
  apply SheafedSpace.IsOpenImmersion.to_iso

end

end LocallyRingedSpace.IsOpenImmersion

end AlgebraicGeometry
