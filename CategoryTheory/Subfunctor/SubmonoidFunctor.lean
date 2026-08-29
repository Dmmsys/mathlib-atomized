/-
Copyright (c) 2026 John Rozmarynowycz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Rozmarynowycz
-/
module

public import Mathlib.Algebra.Category.MonCat.Basic
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Functors of submonoids

Given a functor `M : C ⥤ MonCat`, we define a functor of submonoids `S` to be a
family `Submonoid (M.obj U)` for all `U : C` that are compatible with the maps induced by `M`.

We provide the complete lattice structure and the basic functoriality properties.

## TODO

- Show the Galois connection between `SubmonoidFunctor.image` and `SubmonoidFunctor.comap`
  and provide the related API.
-/

@[expose] public section

universe w v u

open Opposite CategoryTheory ConcreteCategory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {M : C ⥤ MonCat.{w}}

variable (M) in
/-- A submonoid functor consists of a submonoid of `M.obj U` for every `U`,
compatible with the restriction maps `M.map i`. -/
@[ext]
/--
Definition of `SubmonoidFunctor` / `SubmonoidFunctor` 的定义

English:
structure SubmonoidFunctor
  parameters: where
  axioms and operations (2):
    - obj((U : C)) : Submonoid (M.obj U)
    - map({U V : C} (i : U ⟶ V)) : obj U <= (obj V).comap (M.map i).hom  [default: by cat_disch]

中文:
结构 子幺半群函子
  参数: where
  公理与运算 (2 个):
    - obj((U : C)) : 子幺半群 (M.obj U)
    - map({U V : C} (i : U ⟶ V)) : obj U <= (obj V).comap (M.map i).hom  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure SubmonoidFunctor where
  /-- A submonoid of `M.obj U` for all `U : C`. -/
  obj (U : C) : Submonoid (M.obj U)
  /-- For any `i : U ⟶ V`, `M.map i` maps the submonoid `obj U` into the submonoid `obj V`. -/
  map {U V : C} (i : U ⟶ V) : obj U <= (obj V).comap (M.map i).hom := by cat_disch

namespace SubmonoidFunctor

variable (S : SubmonoidFunctor M)

/--
lemma `map_le` / 引理 `map_le`

English:
lemma map_le
  given: {U V : C} (f : U ⟶ V)
  statement: (S.obj U).map (M.map f).hom <= S.obj V
  proof: by
  grw [Submonoid.map_le_iff_le_comap, S.map f]

中文:
引理 map_le
  条件: {U V : C} (f : U ⟶ V)
  结论: (S.obj U).map (M.map f).hom <= S.obj V
  证明: by
  grw [Submonoid.map_le_iff_le_comap, S.map f]

Depends on / 依赖: S.map, Submonoid, Submonoid.map_le_iff_le_comap, map_le_iff_le_comap
-/
lemma map_le {U V : C} (f : U ⟶ V) : (S.obj U).map (M.map f).hom <= S.obj V := by
  grw [Submonoid.map_le_iff_le_comap, S.map f]

/-- The functor of monoids associated to a functor of submonoids. -/
@[simps obj map]
/--
Definition of `toFunctor` / `toFunctor` 的定义

English:
definition toFunctor
  signature: : C ⥤ MonCat.{w} where
  body: MonCat.of (S.obj _)
  map i :=
MonCat.ofHom ((M.map i).hom.submonoidComap (S.obj _)).comp Submonoid.inclusion (S.map i)

中文:
定义 toFunctor
  签名: : C ⥤ 幺半群范畴.{w} where
  定义体: MonCat.of (S.obj _)
  map i :=
MonCat.ofHom ((M.map i).hom.submonoidComap (S.obj _)).comp Submonoid.inclusion (S.map i)

Depends on / 依赖: MonCat, MonCat.of, S.obj
-/
def toFunctor : C ⥤ MonCat.{w} where
  obj _ := MonCat.of (S.obj _)
  map i :=
MonCat.ofHom ((M.map i).hom.submonoidComap (S.obj _)).comp Submonoid.inclusion (S.map i)

/-- The subfunctor associated to a functor of submonoids. -/
@[simps obj]
/--
Definition of `toSubfunctor` / `toSubfunctor` 的定义

English:
definition toSubfunctor
  signature: : Subfunctor (M ⋙ forget MonCat) where
  body: (S.obj _).carrier
  map := S.map

中文:
定义 toSubfunctor
  签名: : 子函子 (M ⋙ forget 幺半群范畴) where
  定义体: (S.obj _).carrier
  map := S.map

Depends on / 依赖: S.obj, carrier
-/
def toSubfunctor : Subfunctor (M ⋙ forget MonCat) where
  obj _ := (S.obj _).carrier
  map := S.map

variable {M M' M'' : C ⥤ MonCat.{w}} (S : SubmonoidFunctor M) (S' : SubmonoidFunctor M')

instance {U : C} : CoeHead (S.toFunctor.obj U) (M.obj U) where
  coe := Subtype.val

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (SubmonoidFunctor M)
  body: PartialOrder.lift SubmonoidFunctor.obj fun _ _ => SubmonoidFunctor.ext

@[simps! top_obj bot_obj sup_obj inf_obj sInf_obj sSup_obj]

中文:
实例 :
  签名: 偏序 (子幺半群函子 M)
  定义体: PartialOrder.lift SubmonoidFunctor.obj fun _ _ => SubmonoidFunctor.ext

@[simps! top_obj bot_obj sup_obj inf_obj sInf_obj sSup_obj]

Depends on / 依赖: PartialOrder, PartialOrder.lift, SubmonoidFunctor, SubmonoidFunctor.ext, SubmonoidFunctor.obj
-/
instance : PartialOrder (SubmonoidFunctor M) :=
  PartialOrder.lift SubmonoidFunctor.obj fun _ _ => SubmonoidFunctor.ext

@[simps! top_obj bot_obj sup_obj inf_obj sInf_obj sSup_obj]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (SubmonoidFunctor M)
  body: { obj _ := F.obj _ ⊔ G.obj _
      map i := by grw [F.map i, G.map i, (Submonoid.monotone_comap).le_map_sup] }
  le_sup_left _ _ _ := by simp
  le_sup_right _ _ _ := by simp
  sup_le F G H h₁ h₂ U := by simp [h₁ U, h₂ U]
  inf S T :=
    { obj _ := S.obj _ ⊓ T.obj _
      map _ _ h := ⟨S.map _ h.1, 

中文:
实例 :
  签名: 完备格 (子幺半群函子 M)
  定义体: { obj _ := F.obj _ ⊔ G.obj _
      map i := by grw [F.map i, G.map i, (Submonoid.monotone_comap).le_map_sup] }
  le_sup_left _ _ _ := by simp
  le_sup_right _ _ _ := by simp
  sup_le F G H h₁ h₂ U := by simp [h₁ U, h₂ U]
  inf S T :=
    { obj _ := S.obj _ ⊓ T.obj _
      map _ _ h := ⟨S.map _ h.1, 

Depends on / 依赖: F.map, F.obj, G.map, G.obj, S.map, S.obj, Submonoid, Submonoid.monotone_comap, Submonoid.monotone_comap.le_map_iSup, T.map, T.obj, inf_le_left, inf_le_right, le_inf, le_map_sup, le_sup_left, le_sup_right, monotone_comap, sup_le
-/
instance : CompleteLattice (SubmonoidFunctor M) where
  sup F G :=
    { obj _ := F.obj _ ⊔ G.obj _
      map i := by grw [F.map i, G.map i, (Submonoid.monotone_comap).le_map_sup] }
  le_sup_left _ _ _ := by simp
  le_sup_right _ _ _ := by simp
  sup_le F G H h₁ h₂ U := by simp [h₁ U, h₂ U]
  inf S T :=
    { obj _ := S.obj _ ⊓ T.obj _
      map _ _ h := ⟨S.map _ h.1, T.map _ h.2⟩ }
  inf_le_left _ _ _ _ h := h.1
  inf_le_right _ _ _ _ h := h.2
  le_inf _ _ _ h₁ h₂ _ _ h := ⟨h₁ _ h, h₂ _ h⟩
  sSup S :=
    { obj _ := ⨆ F in S, F.obj _
      map {U V} f := by
        grw [← Submonoid.monotone_comap.le_map_iSup₂]
        exact iSup₂_mono fun F _ => F.map f }
  isLUB_sSup _ := ⟨fun a ha U => le_iSup₂_of_le a ha le_rfl, fun _ _ _ => by aesop⟩
  sInf S :=
    { obj _ := ⨅ F in S, F.obj _
      map f := by
        rw [(Submonoid.gc_map_comap (M.map f).hom).u_iInf₂]
        exact iInf₂_mono fun F _ => F.map f }
  isGLB_sInf _ := ⟨fun _ _ _ _ => by aesop, fun _ _ _ => by aesop⟩
  bot := { obj _ := ⊥ }
  bot_le _ _ := bot_le
  top := { obj _ := ⊤ }
  le_top _ _ := le_top

/-- The inclusion of a submonoid functor `S` to the original functor of monoids `M`. -/
@[simps]
/--
Definition of `ι` / `ι` 的定义

English:
definition ι
  signature: : S.toFunctor ⟶ M where
  body: MonCat.ofHom (Submonoid.subtype _)

中文:
定义 ι
  签名: : S.toFunctor ⟶ M where
  定义体: MonCat.ofHom (Submonoid.subtype _)

Depends on / 依赖: MonCat, MonCat.ofHom, Submonoid, Submonoid.subtype, subtype
-/
def ι : S.toFunctor ⟶ M where
  app _ := MonCat.ofHom (Submonoid.subtype _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono S.ι
  body: by
  suffices forall (X : C), Mono (S.ι.app X) from NatTrans.mono_of_mono_app _
  intro X
  exact ConcreteCategory.mono_of_injective _ Subtype.val_injective

中文:
实例 :
  签名: 单态射 S.ι
  定义体: by
  suffices forall (X : C), Mono (S.ι.app X) from NatTrans.mono_of_mono_app _
  intro X
  exact ConcreteCategory.mono_of_injective _ Subtype.val_injective

Depends on / 依赖: ConcreteCategory, ConcreteCategory.mono_of_injective, NatTrans, NatTrans.mono_of_mono_app, Subtype, Subtype.val_injective, mono_of_injective, mono_of_mono_app, val_injective
-/
instance : Mono S.ι := by
  suffices forall (X : C), Mono (S.ι.app X) from NatTrans.mono_of_mono_app _
  intro X
  exact ConcreteCategory.mono_of_injective _ Subtype.val_injective

section image

variable (p : M ⟶ M')

/-- The submonoid functor defined by the image along a morphism of functors of monoids. -/
@[simps]
/--
Definition of `image` / `image` 的定义

English:
definition image
  signature: (S : SubmonoidFunctor M)
  body: Submonoid.map (MonCat.Hom.hom (p.app _)) (S.obj _)
  map i := by
    rw [← Submonoid.map_le_iff_le_comap]; rw [Submonoid.map_map]; rw [← MonCat.hom_comp]; rw [← p.naturality]; rw [MonCat.hom_comp]; rw [← Submonoid.map_map]
    grw [S.map_le]

中文:
定义 像
  签名: (S : 子幺半群函子 M)
  定义体: Submonoid.map (MonCat.Hom.hom (p.app _)) (S.obj _)
  map i := by
    rw [← Submonoid.map_le_iff_le_comap]; rw [Submonoid.map_map]; rw [← MonCat.hom_comp]; rw [← p.naturality]; rw [MonCat.hom_comp]; rw [← Submonoid.map_map]
    grw [S.map_le]

Depends on / 依赖: MonCat, MonCat.Hom.hom, S.obj, Submonoid, Submonoid.map, p.app
-/
def image (S : SubmonoidFunctor M) : SubmonoidFunctor M' where
  obj _ := Submonoid.map (MonCat.Hom.hom (p.app _)) (S.obj _)
  map i := by
    rw [← Submonoid.map_le_iff_le_comap]; rw [Submonoid.map_map]; rw [← MonCat.hom_comp]; rw [← p.naturality]; rw [MonCat.hom_comp]; rw [← Submonoid.map_map]
    grw [S.map_le]

variable (M) in
@[simp]
/--
lemma `image_id` / 引理 `image_id`

English:
lemma image_id
  statement: image (𝟙 M) ⊤ = ⊤
  proof: by aesop

@[simp]

中文:
引理 image_id
  结论: 像 (𝟙 M) ⊤ = ⊤
  证明: by aesop

@[simp]
-/
lemma image_id : image (𝟙 M) ⊤ = ⊤ := by aesop

@[simp]
/--
lemma `image_comp` / 引理 `image_comp`

English:
lemma image_comp
  given: (p' : M' ⟶ M'')
  statement: S.image (p ≫ p') = (S.image p).image p'
  proof: by cat_disch

中文:
引理 image_comp
  条件: (p' : M' ⟶ M'')
  结论: S.像 (p ≫ p') = (S.像 p).像 p'
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
lemma image_comp (p' : M' ⟶ M'') : S.image (p ≫ p') = (S.image p).image p' := by cat_disch

end image

section comap

variable (p : M ⟶ M') (S'' : SubmonoidFunctor M'')

/-- The submonoid functor defined by the preimage along a morphism of functors of monoids. -/
@[simps]
/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (S' : SubmonoidFunctor M')
  body: Submonoid.comap (MonCat.Hom.hom (p.app _)) (S'.obj _)
  map _ _ h := by
    simp_rw [Submonoid.mem_comap, NatTrans.naturality_apply]
    exact Submonoid.mem_comap.mp (Set.mem_of_mem_of_subset h (S'.map _))

中文:
定义 comap
  签名: (S' : 子幺半群函子 M')
  定义体: Submonoid.comap (MonCat.Hom.hom (p.app _)) (S'.obj _)
  map _ _ h := by
    simp_rw [Submonoid.mem_comap, NatTrans.naturality_apply]
    exact Submonoid.mem_comap.mp (Set.mem_of_mem_of_subset h (S'.map _))

Depends on / 依赖: MonCat, MonCat.Hom.hom, Submonoid, Submonoid.comap, p.app
-/
def comap (S' : SubmonoidFunctor M') : SubmonoidFunctor M where
  obj _ := Submonoid.comap (MonCat.Hom.hom (p.app _)) (S'.obj _)
  map _ _ h := by
    simp_rw [Submonoid.mem_comap, NatTrans.naturality_apply]
    exact Submonoid.mem_comap.mp (Set.mem_of_mem_of_subset h (S'.map _))

variable (M) in
@[simp]
/--
lemma `comap_id` / 引理 `comap_id`

English:
lemma comap_id
  statement: comap (𝟙 M) ⊤ = ⊤
  proof: rfl

@[simp]

中文:
引理 comap_id
  结论: comap (𝟙 M) ⊤ = ⊤
  证明: rfl

@[simp]
-/
lemma comap_id : comap (𝟙 M) ⊤ = ⊤ := rfl

@[simp]
/--
lemma `comap_comp` / 引理 `comap_comp`

English:
lemma comap_comp
  given: (p' : M' ⟶ M'')
  statement: S''.comap (p ≫ p') = (S''.comap p').comap p
  proof: by rfl

中文:
引理 comap_comp
  条件: (p' : M' ⟶ M'')
  结论: S''.comap (p ≫ p') = (S''.comap p').comap p
  证明: by rfl
-/
lemma comap_comp (p' : M' ⟶ M'') : S''.comap (p ≫ p') = (S''.comap p').comap p := by rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `image_comap_ι` / 引理 `image_comap_ι`

English:
lemma image_comap_ι
  statement: image S.ι (comap S.ι S) = S
  proof: by aesop

中文:
引理 image_comap_ι
  结论: 像 S.ι (comap S.ι S) = S
  证明: by aesop
-/
lemma image_comap_ι : image S.ι (comap S.ι S) = S := by aesop

end comap

section lift

variable (p : M ⟶ M') (S : SubmonoidFunctor M) (S' : SubmonoidFunctor M')
  (hp : image p ⊤ <= S')

set_option backward.defeqAttrib.useBackward true in
/-- If the image of morphism `M' ⟶ M` lands in a submonoid functor `S`,
then the morphism factors through it. -/
@[simps! app]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : M ⟶ S'.toFunctor where
  body: MonCat.ofHom MonoidHom.codRestrict (p.app U).hom _ fun x => hp _ (by simp)

@[reassoc (attr := simp)]

中文:
定义 lift
  签名: : M ⟶ S'.toFunctor where
  定义体: MonCat.ofHom MonoidHom.codRestrict (p.app U).hom _ fun x => hp _ (by simp)

@[reassoc (attr := simp)]

Depends on / 依赖: MonCat, MonCat.ofHom, MonoidHom, MonoidHom.codRestrict, codRestrict, p.app
-/
def lift : M ⟶ S'.toFunctor where
app U := MonCat.ofHom MonoidHom.codRestrict (p.app U).hom _ fun x => hp _ (by simp)

@[reassoc (attr := simp)]
/--
theorem `lift_ι` / 定理 `lift_ι`

English:
theorem lift_ι
  statement: lift p S' hp ≫ S'.ι = p
  proof: rfl

中文:
定理 lift_ι
  结论: lift p S' hp ≫ S'.ι = p
  证明: rfl
-/
theorem lift_ι : lift p S' hp ≫ S'.ι = p := rfl

end lift

end SubmonoidFunctor

end CategoryTheory
