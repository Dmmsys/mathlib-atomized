/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Tactic.CategoryTheory.IsoReassoc
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Whiskering

Given a functor `F : C ⥤ D` and functors `G H : D ⥤ E` and a natural transformation `α : G ⟶ H`,
we can construct a new natural transformation `F ⋙ G ⟶ F ⋙ H`,
called `whiskerLeft F α`. This is the same as the horizontal composition of `𝟙 F` with `α`.

This operation is functorial in `F`, and we package this as `whiskeringLeft`. Here
`(whiskeringLeft.obj F).obj G` is `F ⋙ G`, and
`(whiskeringLeft.obj F).map α` is `whiskerLeft F α`.
(That is, we might have alternatively named this as the "left composition functor".)

We also provide analogues for composition on the right, and for these operations on isomorphisms.

We show the associator and unitor natural isomorphisms satisfy the triangle and pentagon
identities.
-/

@[expose] public section


namespace CategoryTheory

namespace Functor

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃}
  [Category.{v₃} E]

/-- If `α : G ⟶ H` then `whiskerLeft F α : F ⋙ G ⟶ F ⋙ H` has components `α.app (F.obj X)`. -/
@[implicit_reducible, to_dual self, simps (attr := to_dual self)]
/--
Definition of `whiskerLeft` / `whiskerLeft` 的定义

English:
definition whiskerLeft
  signature: (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H)
  body: α.app (F.obj X)
  naturality X Y f := by rw [Functor.comp_map, Functor.comp_map, α.naturality]

@[simp, to_dual self]

中文:
定义 whiskerLeft
  签名: (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H)
  定义体: α.app (F.obj X)
  naturality X Y f := by rw [Functor.comp_map, Functor.comp_map, α.naturality]

@[simp, to_dual self]

Depends on / 依赖: F.obj
-/
def whiskerLeft (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) :
    F ⋙ G ⟶ F ⋙ H where
  app X := α.app (F.obj X)
  naturality X Y f := by rw [Functor.comp_map, Functor.comp_map, α.naturality]

@[simp, to_dual self]
/--
lemma `id_hcomp` / 引理 `id_hcomp`

English:
lemma id_hcomp
  given: (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H)
  statement: 𝟙 F ◫ α = whiskerLeft F α
  proof: by
  ext
  simp

中文:
引理 id_hcomp
  条件: (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H)
  结论: 𝟙 F ◫ α = whiskerLeft F α
  证明: by
  ext
  simp
-/
lemma id_hcomp (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) : 𝟙 F ◫ α = whiskerLeft F α := by
  ext
  simp

/-- If `α : G ⟶ H` then `whiskerRight α F : G ⋙ F ⟶ H ⋙ F` has components `F.map (α.app X)`. -/
@[implicit_reducible, to_dual self, simps (attr := to_dual self)]
/--
Definition of `whiskerRight` / `whiskerRight` 的定义

English:
definition whiskerRight
  signature: {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E)
  body: F.map (α.app X)
  naturality X Y f := by
    rw [Functor.comp_map]; rw [Functor.comp_map]; rw [← F.map_comp]; rw [← F.map_comp]; rw [α.naturality]

@[simp, to_dual self]

中文:
定义 whiskerRight
  签名: {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E)
  定义体: F.map (α.app X)
  naturality X Y f := by
    rw [Functor.comp_map]; rw [Functor.comp_map]; rw [← F.map_comp]; rw [← F.map_comp]; rw [α.naturality]

@[simp, to_dual self]

Depends on / 依赖: F.map
-/
def whiskerRight {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) :
    G ⋙ F ⟶ H ⋙ F where
  app X := F.map (α.app X)
  naturality X Y f := by
    rw [Functor.comp_map]; rw [Functor.comp_map]; rw [← F.map_comp]; rw [← F.map_comp]; rw [α.naturality]

@[simp, to_dual self]
/--
lemma `hcomp_id` / 引理 `hcomp_id`

English:
lemma hcomp_id
  given: {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E)
  statement: α ◫ 𝟙 F = whiskerRight α F
  proof: by
  ext
  simp

中文:
引理 hcomp_id
  条件: {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E)
  结论: α ◫ 𝟙 F = whiskerRight α F
  证明: by
  ext
  simp
-/
lemma hcomp_id {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) : α ◫ 𝟙 F = whiskerRight α F := by
  ext
  simp

variable (C D E)

set_option backward.defeqAttrib.useBackward true in
/-- Left-composition gives a functor `(C ⥤ D) ⥤ ((D ⥤ E) ⥤ (C ⥤ E))`.

`(whiskeringLeft.obj F).obj G` is `F ⋙ G`, and
`(whiskeringLeft.obj F).map α` is `whiskerLeft F α`.
-/
@[simps, implicit_reducible]
/--
Definition of `whiskeringLeft` / `whiskeringLeft` 的定义

English:
definition whiskeringLeft
  signature: : (C ⥤ D) ⥤ (D ⥤ E) ⥤ C ⥤ E where
  body: { obj := fun G => F ⋙ G
      map := fun α => whiskerLeft F α }
  map τ :=
    { app := fun H =>
        { app := fun c => H.map (τ.app c)
          naturality := fun X Y f => by dsimp; rw [← H.map_comp, ← H.map_comp, ← τ.naturality] }
      naturality := fun X Y f => by ext; dsimp; rw [f.naturality] }

中文:
定义 whiskeringLeft
  签名: : (C ⥤ D) ⥤ (D ⥤ E) ⥤ C ⥤ E where
  定义体: { obj := fun G => F ⋙ G
      map := fun α => whiskerLeft F α }
  map τ :=
    { app := fun H =>
        { app := fun c => H.map (τ.app c)
          naturality := fun X Y f => by dsimp; rw [← H.map_comp, ← H.map_comp, ← τ.naturality] }
      naturality := fun X Y f => by ext; dsimp; rw [f.naturality] }

Depends on / 依赖: H.map, H.map_comp, f.naturality, map_comp, naturality, whiskerLeft
-/
def whiskeringLeft : (C ⥤ D) ⥤ (D ⥤ E) ⥤ C ⥤ E where
  obj F :=
    { obj := fun G => F ⋙ G
      map := fun α => whiskerLeft F α }
  map τ :=
    { app := fun H =>
        { app := fun c => H.map (τ.app c)
          naturality := fun X Y f => by dsimp; rw [← H.map_comp, ← H.map_comp, ← τ.naturality] }
      naturality := fun X Y f => by ext; dsimp; rw [f.naturality] }

set_option backward.defeqAttrib.useBackward true in
/-- Right-composition gives a functor `(D ⥤ E) ⥤ ((C ⥤ D) ⥤ (C ⥤ E))`.

`(whiskeringRight.obj H).obj F` is `F ⋙ H`, and
`(whiskeringRight.obj H).map α` is `whiskerRight α H`.
-/
@[simps, implicit_reducible]
/--
Definition of `whiskeringRight` / `whiskeringRight` 的定义

English:
definition whiskeringRight
  signature: : (D ⥤ E) ⥤ (C ⥤ D) ⥤ C ⥤ E where
  body: { obj := fun F => F ⋙ H
      map := fun α => whiskerRight α H }
  map τ :=
    { app := fun F =>
        { app := fun c => τ.app (F.obj c)
          naturality := fun X Y f => by dsimp; rw [τ.naturality] }
      naturality := fun X Y f => by ext; dsimp; rw [← NatTrans.naturality] }

中文:
定义 whiskeringRight
  签名: : (D ⥤ E) ⥤ (C ⥤ D) ⥤ C ⥤ E where
  定义体: { obj := fun F => F ⋙ H
      map := fun α => whiskerRight α H }
  map τ :=
    { app := fun F =>
        { app := fun c => τ.app (F.obj c)
          naturality := fun X Y f => by dsimp; rw [τ.naturality] }
      naturality := fun X Y f => by ext; dsimp; rw [← NatTrans.naturality] }

Depends on / 依赖: F.obj, NatTrans, NatTrans.naturality, naturality, whiskerRight
-/
def whiskeringRight : (D ⥤ E) ⥤ (C ⥤ D) ⥤ C ⥤ E where
  obj H :=
    { obj := fun F => F ⋙ H
      map := fun α => whiskerRight α H }
  map τ :=
    { app := fun F =>
        { app := fun c => τ.app (F.obj c)
          naturality := fun X Y f => by dsimp; rw [τ.naturality] }
      naturality := fun X Y f => by ext; dsimp; rw [← NatTrans.naturality] }

variable {C} {D} {E}

/--
Instance `faithful_whiskeringRight_obj` / 实例 `faithful_whiskeringRight_obj`

English:
instance faithful_whiskeringRight_obj
  signature: {F : D ⥤ E} [F.Faithful]
  body: by
    ext X
exact F.map_injective congr_fun (congr_arg NatTrans.app hαβ) X

中文:
实例 faithful_whiskeringRight_obj
  签名: {F : D ⥤ E} [F.忠实]
  定义体: by
    ext X
exact F.map_injective congr_fun (congr_arg NatTrans.app hαβ) X

Depends on / 依赖: F.map_injective, NatTrans, NatTrans.app, congr_arg, congr_fun, map_injective
-/
instance faithful_whiskeringRight_obj {F : D ⥤ E} [F.Faithful] :
    ((whiskeringRight C D E).obj F).Faithful where
  map_injective hαβ := by
    ext X
exact F.map_injective congr_fun (congr_arg NatTrans.app hαβ) X

/-- If `F : D ⥤ E` is fully faithful, then so is
`(whiskeringRight C D E).obj F : (C ⥤ D) ⥤ C ⥤ E`. -/
@[simps]
/--
Definition of `FullyFaithful.whiskeringRight` / `FullyFaithful.whiskeringRight` 的定义

English:
definition FullyFaithful.whiskeringRight
  signature: {F : D ⥤ E} (hF : F.FullyFaithful)
  body: { app := fun X => hF.preimage (f.app X)
      naturality := fun _ _ g => by
        apply hF.map_injective
        simp only [map_comp, map_preimage]
        apply f.naturality }

中文:
定义 满忠实.whiskeringRight
  签名: {F : D ⥤ E} (hF : F.满忠实)
  定义体: { app := fun X => hF.preimage (f.app X)
      naturality := fun _ _ g => by
        apply hF.map_injective
        simp only [map_comp, map_preimage]
        apply f.naturality }

Depends on / 依赖: f.app, f.naturality, hF.map_injective, hF.preimage, map_comp, map_injective, map_preimage, naturality, preimage
-/
def FullyFaithful.whiskeringRight {F : D ⥤ E} (hF : F.FullyFaithful)
    (C : Type*) [Category* C] :
    ((whiskeringRight C D E).obj F).FullyFaithful where
  preimage f :=
    { app := fun X => hF.preimage (f.app X)
      naturality := fun _ _ g => by
        apply hF.map_injective
        simp only [map_comp, map_preimage]
        apply f.naturality }

/--
theorem `whiskeringLeft_obj_id` / 定理 `whiskeringLeft_obj_id`

English:
theorem whiskeringLeft_obj_id
  statement: (whiskeringLeft C C E).obj (𝟭 _) = 𝟭 _
  proof: rfl

中文:
定理 whiskeringLeft_obj_id
  结论: (whiskeringLeft C C E).obj (𝟭 _) = 𝟭 _
  证明: rfl
-/
theorem whiskeringLeft_obj_id : (whiskeringLeft C C E).obj (𝟭 _) = 𝟭 _ :=
  rfl

/-- The isomorphism between left-whiskering on the identity functor and the identity of the functor
between the resulting functor categories. -/
@[simps!]
/--
Definition of `whiskeringLeftObjIdIso` / `whiskeringLeftObjIdIso` 的定义

English:
definition whiskeringLeftObjIdIso
  signature: : (whiskeringLeft C C E).obj (𝟭 _) ≅ 𝟭 _
  body: Iso.refl _

中文:
定义 whiskeringLeftObjIdIso
  签名: : (whiskeringLeft C C E).obj (𝟭 _) ≅ 𝟭 _
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def whiskeringLeftObjIdIso : (whiskeringLeft C C E).obj (𝟭 _) ≅ 𝟭 _ :=
  Iso.refl _

/--
theorem `whiskeringLeft_obj_comp` / 定理 `whiskeringLeft_obj_comp`

English:
theorem whiskeringLeft_obj_comp
  given: {D' : Type u₄} [Category.{v₄} D'] (F : C ⥤ D) (G : D ⥤ D')
  proof: rfl

中文:
定理 whiskeringLeft_obj_comp
  条件: {D' : 类型u₄} [范畴.{v₄} D'] (F : C ⥤ D) (G : D ⥤ D')
  证明: rfl
-/
theorem whiskeringLeft_obj_comp {D' : Type u₄} [Category.{v₄} D'] (F : C ⥤ D) (G : D ⥤ D') :
    (whiskeringLeft C D' E).obj (F ⋙ G) =
    (whiskeringLeft D D' E).obj G ⋙ (whiskeringLeft C D E).obj F :=
  rfl

/-- The isomorphism between left-whiskering on the composition of functors and the composition
of two left-whiskering applications. -/
@[simps!]
/--
Definition of `whiskeringLeftObjCompIso` / `whiskeringLeftObjCompIso` 的定义

English:
definition whiskeringLeftObjCompIso
  signature: {D' : Type u₄} [Category.{v₄} D'] (F : C ⥤ D) (G : D ⥤ D')
  body: Iso.refl _

中文:
定义 whiskeringLeftObjCompIso
  签名: {D' : 类型u₄} [范畴.{v₄} D'] (F : C ⥤ D) (G : D ⥤ D')
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def whiskeringLeftObjCompIso {D' : Type u₄} [Category.{v₄} D'] (F : C ⥤ D) (G : D ⥤ D') :
    (whiskeringLeft C D' E).obj (F ⋙ G) ≅
    (whiskeringLeft D D' E).obj G ⋙ (whiskeringLeft C D E).obj F :=
  Iso.refl _

/--
theorem `whiskeringRight_obj_id` / 定理 `whiskeringRight_obj_id`

English:
theorem whiskeringRight_obj_id
  statement: (whiskeringRight E C C).obj (𝟭 _) = 𝟭 _
  proof: rfl

中文:
定理 whiskeringRight_obj_id
  结论: (whiskeringRight E C C).obj (𝟭 _) = 𝟭 _
  证明: rfl
-/
theorem whiskeringRight_obj_id : (whiskeringRight E C C).obj (𝟭 _) = 𝟭 _ :=
  rfl

/-- The isomorphism between right-whiskering on the identity functor and the identity of the functor
between the resulting functor categories. -/
@[simps!]
/--
Definition of `whiskeringRightObjIdIso` / `whiskeringRightObjIdIso` 的定义

English:
definition whiskeringRightObjIdIso
  signature: : (whiskeringRight E C C).obj (𝟭 _) ≅ 𝟭 _
  body: Iso.refl _

中文:
定义 whiskeringRightObjIdIso
  签名: : (whiskeringRight E C C).obj (𝟭 _) ≅ 𝟭 _
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def whiskeringRightObjIdIso : (whiskeringRight E C C).obj (𝟭 _) ≅ 𝟭 _ :=
  Iso.refl _

/--
theorem `whiskeringRight_obj_comp` / 定理 `whiskeringRight_obj_comp`

English:
theorem whiskeringRight_obj_comp
  given: {D' : Type u₄} [Category.{v₄} D'] (F : C ⥤ D) (G : D ⥤ D')
  proof: rfl

中文:
定理 whiskeringRight_obj_comp
  条件: {D' : 类型u₄} [范畴.{v₄} D'] (F : C ⥤ D) (G : D ⥤ D')
  证明: rfl
-/
theorem whiskeringRight_obj_comp {D' : Type u₄} [Category.{v₄} D'] (F : C ⥤ D) (G : D ⥤ D') :
    (whiskeringRight E C D).obj F ⋙ (whiskeringRight E D D').obj G =
    (whiskeringRight E C D').obj (F ⋙ G) :=
  rfl

/-- The isomorphism between right-whiskering on the composition of functors and the composition
of two right-whiskering applications. -/
@[simps!]
/--
Definition of `whiskeringRightObjCompIso` / `whiskeringRightObjCompIso` 的定义

English:
definition whiskeringRightObjCompIso
  signature: {D' : Type u₄} [Category.{v₄} D'] (F : C ⥤ D) (G : D ⥤ D')
  body: Iso.refl _

中文:
定义 whiskeringRightObjCompIso
  签名: {D' : 类型u₄} [范畴.{v₄} D'] (F : C ⥤ D) (G : D ⥤ D')
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def whiskeringRightObjCompIso {D' : Type u₄} [Category.{v₄} D'] (F : C ⥤ D) (G : D ⥤ D') :
    (whiskeringRight E C D).obj F ⋙ (whiskeringRight E D D').obj G ≅
    (whiskeringRight E C D').obj (F ⋙ G) :=
  Iso.refl _

/--
Instance `full_whiskeringRight_obj` / 实例 `full_whiskeringRight_obj`

English:
instance full_whiskeringRight_obj
  signature: {F : D ⥤ E} [F.Faithful] [F.Full]
  body: ((Functor.FullyFaithful.ofFullyFaithful F).whiskeringRight C).full

@[simp]

中文:
实例 full_whiskeringRight_obj
  签名: {F : D ⥤ E} [F.忠实] [F.满]
  定义体: ((Functor.FullyFaithful.ofFullyFaithful F).whiskeringRight C).full

@[simp]

Depends on / 依赖: FullyFaithful, Functor, Functor.FullyFaithful.ofFullyFaithful, ofFullyFaithful, whiskeringRight
-/
instance full_whiskeringRight_obj {F : D ⥤ E} [F.Faithful] [F.Full] :
    ((whiskeringRight C D E).obj F).Full :=
  ((Functor.FullyFaithful.ofFullyFaithful F).whiskeringRight C).full

@[simp]
/--
theorem `whiskerLeft_id` / 定理 `whiskerLeft_id`

English:
theorem whiskerLeft_id
  given: (F : C ⥤ D) {G : D ⥤ E}
  proof: rfl

@[simp]

中文:
定理 whiskerLeft_id
  条件: (F : C ⥤ D) {G : D ⥤ E}
  证明: rfl

@[simp]
-/
theorem whiskerLeft_id (F : C ⥤ D) {G : D ⥤ E} :
    whiskerLeft F (NatTrans.id G) = NatTrans.id (F.comp G) :=
  rfl

@[simp]
/--
theorem `whiskerLeft_id'` / 定理 `whiskerLeft_id'`

English:
theorem whiskerLeft_id'
  given: (F : C ⥤ D) {G : D ⥤ E}
  statement: whiskerLeft F (𝟙 G) = 𝟙 (F.comp G)
  proof: rfl

@[simp]

中文:
定理 whiskerLeft_id'
  条件: (F : C ⥤ D) {G : D ⥤ E}
  结论: whiskerLeft F (𝟙 G) = 𝟙 (F.comp G)
  证明: rfl

@[simp]
-/
theorem whiskerLeft_id' (F : C ⥤ D) {G : D ⥤ E} : whiskerLeft F (𝟙 G) = 𝟙 (F.comp G) :=
  rfl

@[simp]
/--
theorem `whiskerRight_id` / 定理 `whiskerRight_id`

English:
theorem whiskerRight_id
  given: {G : C ⥤ D} (F : D ⥤ E)
  proof: ((whiskeringRight C D E).obj F).map_id _

@[simp]

中文:
定理 whiskerRight_id
  条件: {G : C ⥤ D} (F : D ⥤ E)
  证明: ((whiskeringRight C D E).obj F).map_id _

@[simp]

Depends on / 依赖: map_id, whiskeringRight
-/
theorem whiskerRight_id {G : C ⥤ D} (F : D ⥤ E) :
    whiskerRight (NatTrans.id G) F = NatTrans.id (G.comp F) :=
  ((whiskeringRight C D E).obj F).map_id _

@[simp]
/--
theorem `whiskerRight_id'` / 定理 `whiskerRight_id'`

English:
theorem whiskerRight_id'
  given: {G : C ⥤ D} (F : D ⥤ E)
  statement: whiskerRight (𝟙 G) F = 𝟙 (G.comp F)
  proof: ((whiskeringRight C D E).obj F).map_id _

@[simp, to_dual self, reassoc]

中文:
定理 whiskerRight_id'
  条件: {G : C ⥤ D} (F : D ⥤ E)
  结论: whiskerRight (𝟙 G) F = 𝟙 (G.comp F)
  证明: ((whiskeringRight C D E).obj F).map_id _

@[simp, to_dual self, reassoc]

Depends on / 依赖: map_id, whiskeringRight
-/
theorem whiskerRight_id' {G : C ⥤ D} (F : D ⥤ E) : whiskerRight (𝟙 G) F = 𝟙 (G.comp F) :=
  ((whiskeringRight C D E).obj F).map_id _

@[simp, to_dual self, reassoc]
/--
theorem `whiskerLeft_comp` / 定理 `whiskerLeft_comp`

English:
theorem whiskerLeft_comp
  given: (F : C ⥤ D) {G H K : D ⥤ E} (α : G ⟶ H) (β : H ⟶ K)
  proof: rfl

@[simp, to_dual self, reassoc]

中文:
定理 whiskerLeft_comp
  条件: (F : C ⥤ D) {G H K : D ⥤ E} (α : G ⟶ H) (β : H ⟶ K)
  证明: rfl

@[simp, to_dual self, reassoc]
-/
theorem whiskerLeft_comp (F : C ⥤ D) {G H K : D ⥤ E} (α : G ⟶ H) (β : H ⟶ K) :
    whiskerLeft F (α ≫ β) = whiskerLeft F α ≫ whiskerLeft F β :=
  rfl

@[simp, to_dual self, reassoc]
/--
theorem `whiskerRight_comp` / 定理 `whiskerRight_comp`

English:
theorem whiskerRight_comp
  given: {G H K : C ⥤ D} (α : G ⟶ H) (β : H ⟶ K) (F : D ⥤ E)
  proof: ((whiskeringRight C D E).obj F).map_comp α β

@[to_dual none, reassoc]

中文:
定理 whiskerRight_comp
  条件: {G H K : C ⥤ D} (α : G ⟶ H) (β : H ⟶ K) (F : D ⥤ E)
  证明: ((whiskeringRight C D E).obj F).map_comp α β

@[to_dual none, reassoc]

Depends on / 依赖: map_comp, whiskeringRight
-/
theorem whiskerRight_comp {G H K : C ⥤ D} (α : G ⟶ H) (β : H ⟶ K) (F : D ⥤ E) :
    whiskerRight (α ≫ β) F = whiskerRight α F ≫ whiskerRight β F :=
  ((whiskeringRight C D E).obj F).map_comp α β

@[to_dual none, reassoc]
/--
theorem `whiskerLeft_comp_whiskerRight` / 定理 `whiskerLeft_comp_whiskerRight`

English:
theorem whiskerLeft_comp_whiskerRight
  given: {F G : C ⥤ D} {H K : D ⥤ E} (α : F ⟶ G) (β : H ⟶ K)
  proof: by
  ext
  simp

中文:
定理 whiskerLeft_comp_whiskerRight
  条件: {F G : C ⥤ D} {H K : D ⥤ E} (α : F ⟶ G) (β : H ⟶ K)
  证明: by
  ext
  simp
-/
theorem whiskerLeft_comp_whiskerRight {F G : C ⥤ D} {H K : D ⥤ E} (α : F ⟶ G) (β : H ⟶ K) :
    whiskerLeft F β ≫ whiskerRight α K = whiskerRight α H ≫ whiskerLeft G β := by
  ext
  simp

set_option backward.defeqAttrib.useBackward true in
@[to_dual hcomp_eq_whiskerRight_comp_whiskerLeft]
/--
lemma `NatTrans.hcomp_eq_whiskerLeft_comp_whiskerRight` / 引理 `NatTrans.hcomp_eq_whiskerLeft_comp_whiskerRight`

English:
lemma NatTrans.hcomp_eq_whiskerLeft_comp_whiskerRight
  statement: {F G : C ⥤ D} {H K : D ⥤ E}
  proof: by
  ext
  simp

中文:
引理 自然变换.hcomp_eq_whiskerLeft_comp_whiskerRight
  结论: {F G : C ⥤ D} {H K : D ⥤ E}
  证明: by
  ext
  simp
-/
lemma NatTrans.hcomp_eq_whiskerLeft_comp_whiskerRight {F G : C ⥤ D} {H K : D ⥤ E}
    (α : F ⟶ G) (β : H ⟶ K) : α ◫ β = whiskerLeft F β ≫ whiskerRight α K := by
  ext
  simp

/--
Definition of `isoWhiskerLeft` / `isoWhiskerLeft` 的定义

English:
definition isoWhiskerLeft
  signature: (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H)
  body: ((whiskeringLeft C D E).obj F).mapIso α

@[simp]

中文:
定义 isoWhiskerLeft
  签名: (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H)
  定义体: ((whiskeringLeft C D E).obj F).mapIso α

@[simp]

Depends on / 依赖: mapIso, whiskeringLeft
-/
def isoWhiskerLeft (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) : F ⋙ G ≅ F ⋙ H :=
  ((whiskeringLeft C D E).obj F).mapIso α

@[simp]
/--
theorem `isoWhiskerLeft_hom` / 定理 `isoWhiskerLeft_hom`

English:
theorem isoWhiskerLeft_hom
  given: (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H)
  proof: rfl

@[simp]

中文:
定理 isoWhiskerLeft_hom
  条件: (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H)
  证明: rfl

@[simp]
-/
theorem isoWhiskerLeft_hom (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) :
    (isoWhiskerLeft F α).hom = whiskerLeft F α.hom :=
  rfl

@[simp]
/--
theorem `isoWhiskerLeft_inv` / 定理 `isoWhiskerLeft_inv`

English:
theorem isoWhiskerLeft_inv
  given: (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H)
  proof: rfl

中文:
定理 isoWhiskerLeft_inv
  条件: (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H)
  证明: rfl
-/
theorem isoWhiskerLeft_inv (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) :
    (isoWhiskerLeft F α).inv = whiskerLeft F α.inv :=
  rfl

/--
lemma `isoWhiskerLeft_symm` / 引理 `isoWhiskerLeft_symm`

English:
lemma isoWhiskerLeft_symm
  given: (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H)
  proof: rfl

@[simp]

中文:
引理 isoWhiskerLeft_symm
  条件: (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H)
  证明: rfl

@[simp]
-/
lemma isoWhiskerLeft_symm (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) :
    (isoWhiskerLeft F α).symm = isoWhiskerLeft F α.symm :=
  rfl

@[simp]
/--
lemma `isoWhiskerLeft_refl` / 引理 `isoWhiskerLeft_refl`

English:
lemma isoWhiskerLeft_refl
  given: (F : C ⥤ D) (G : D ⥤ E)
  proof: rfl

中文:
引理 isoWhiskerLeft_refl
  条件: (F : C ⥤ D) (G : D ⥤ E)
  证明: rfl
-/
lemma isoWhiskerLeft_refl (F : C ⥤ D) (G : D ⥤ E) :
    isoWhiskerLeft F (Iso.refl G) = Iso.refl _ :=
  rfl

/--
Definition of `isoWhiskerRight` / `isoWhiskerRight` 的定义

English:
definition isoWhiskerRight
  signature: {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E)
  body: ((whiskeringRight C D E).obj F).mapIso α

@[simp]

中文:
定义 isoWhiskerRight
  签名: {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E)
  定义体: ((whiskeringRight C D E).obj F).mapIso α

@[simp]

Depends on / 依赖: mapIso, whiskeringRight
-/
def isoWhiskerRight {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) : G ⋙ F ≅ H ⋙ F :=
  ((whiskeringRight C D E).obj F).mapIso α

@[simp]
/--
theorem `isoWhiskerRight_hom` / 定理 `isoWhiskerRight_hom`

English:
theorem isoWhiskerRight_hom
  given: {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E)
  proof: rfl

@[simp]

中文:
定理 isoWhiskerRight_hom
  条件: {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E)
  证明: rfl

@[simp]
-/
theorem isoWhiskerRight_hom {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) :
    (isoWhiskerRight α F).hom = whiskerRight α.hom F :=
  rfl

@[simp]
/--
theorem `isoWhiskerRight_inv` / 定理 `isoWhiskerRight_inv`

English:
theorem isoWhiskerRight_inv
  given: {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E)
  proof: rfl

中文:
定理 isoWhiskerRight_inv
  条件: {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E)
  证明: rfl
-/
theorem isoWhiskerRight_inv {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) :
    (isoWhiskerRight α F).inv = whiskerRight α.inv F :=
  rfl

/--
lemma `isoWhiskerRight_symm` / 引理 `isoWhiskerRight_symm`

English:
lemma isoWhiskerRight_symm
  given: {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E)
  proof: rfl

@[simp]

中文:
引理 isoWhiskerRight_symm
  条件: {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E)
  证明: rfl

@[simp]
-/
lemma isoWhiskerRight_symm {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) :
    (isoWhiskerRight α F).symm = isoWhiskerRight α.symm F :=
  rfl

@[simp]
/--
lemma `isoWhiskerRight_refl` / 引理 `isoWhiskerRight_refl`

English:
lemma isoWhiskerRight_refl
  given: (F : C ⥤ D) (G : D ⥤ E)
  proof: by
  cat_disch

@[to_dual self]

中文:
引理 isoWhiskerRight_refl
  条件: (F : C ⥤ D) (G : D ⥤ E)
  证明: by
  cat_disch

@[to_dual self]

Depends on / 依赖: cat_disch
-/
lemma isoWhiskerRight_refl (F : C ⥤ D) (G : D ⥤ E) :
    isoWhiskerRight (Iso.refl F) G = Iso.refl _ := by
  cat_disch

@[to_dual self]
/--
Instance `isIso_whiskerLeft` / 实例 `isIso_whiskerLeft`

English:
instance isIso_whiskerLeft
  signature: (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) [IsIso α]
  body: (isoWhiskerLeft F (asIso α)).isIso_hom

@[to_dual self]

中文:
实例 isIso_whiskerLeft
  签名: (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) [是同构 α]
  定义体: (isoWhiskerLeft F (asIso α)).isIso_hom

@[to_dual self]

Depends on / 依赖: isIso_hom, isoWhiskerLeft
-/
instance isIso_whiskerLeft (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) [IsIso α] :
    IsIso (whiskerLeft F α) :=
  (isoWhiskerLeft F (asIso α)).isIso_hom

@[to_dual self]
/--
Instance `isIso_whiskerRight` / 实例 `isIso_whiskerRight`

English:
instance isIso_whiskerRight
  signature: {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) [IsIso α]
  body: (isoWhiskerRight (asIso α) F).isIso_hom

@[simp, to_dual self]

中文:
实例 isIso_whiskerRight
  签名: {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) [是同构 α]
  定义体: (isoWhiskerRight (asIso α) F).isIso_hom

@[simp, to_dual self]

Depends on / 依赖: isIso_hom, isoWhiskerRight
-/
instance isIso_whiskerRight {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) [IsIso α] :
    IsIso (whiskerRight α F) :=
  (isoWhiskerRight (asIso α) F).isIso_hom

@[simp, to_dual self]
/--
theorem `inv_whiskerRight` / 定理 `inv_whiskerRight`

English:
theorem inv_whiskerRight
  given: {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) [IsIso α]
  proof: by
  symm
  apply IsIso.eq_inv_of_inv_hom_id
  simp [← whiskerRight_comp]

@[simp, to_dual self]

中文:
定理 inv_whiskerRight
  条件: {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) [是同构 α]
  证明: by
  symm
  apply IsIso.eq_inv_of_inv_hom_id
  simp [← whiskerRight_comp]

@[simp, to_dual self]

Depends on / 依赖: IsIso.eq_inv_of_inv_hom_id, eq_inv_of_inv_hom_id, whiskerRight_comp
-/
theorem inv_whiskerRight {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) [IsIso α] :
    inv (whiskerRight α F) = whiskerRight (inv α) F := by
  symm
  apply IsIso.eq_inv_of_inv_hom_id
  simp [← whiskerRight_comp]

@[simp, to_dual self]
/--
theorem `inv_whiskerLeft` / 定理 `inv_whiskerLeft`

English:
theorem inv_whiskerLeft
  given: (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) [IsIso α]
  proof: by
  symm
  apply IsIso.eq_inv_of_inv_hom_id
  simp [← whiskerLeft_comp]

@[simp, reassoc]

中文:
定理 inv_whiskerLeft
  条件: (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) [是同构 α]
  证明: by
  symm
  apply IsIso.eq_inv_of_inv_hom_id
  simp [← whiskerLeft_comp]

@[simp, reassoc]

Depends on / 依赖: IsIso.eq_inv_of_inv_hom_id, eq_inv_of_inv_hom_id, whiskerLeft_comp
-/
theorem inv_whiskerLeft (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) [IsIso α] :
    inv (whiskerLeft F α) = whiskerLeft F (inv α) := by
  symm
  apply IsIso.eq_inv_of_inv_hom_id
  simp [← whiskerLeft_comp]

@[simp, reassoc]
/--
theorem `isoWhiskerLeft_trans` / 定理 `isoWhiskerLeft_trans`

English:
theorem isoWhiskerLeft_trans
  given: (F : C ⥤ D) {G H K : D ⥤ E} (α : G ≅ H) (β : H ≅ K)
  proof: rfl

@[simp, reassoc]

中文:
定理 isoWhiskerLeft_trans
  条件: (F : C ⥤ D) {G H K : D ⥤ E} (α : G ≅ H) (β : H ≅ K)
  证明: rfl

@[simp, reassoc]
-/
theorem isoWhiskerLeft_trans (F : C ⥤ D) {G H K : D ⥤ E} (α : G ≅ H) (β : H ≅ K) :
    isoWhiskerLeft F (α ≪≫ β) = isoWhiskerLeft F α ≪≫ isoWhiskerLeft F β :=
  rfl

@[simp, reassoc]
/--
theorem `isoWhiskerRight_trans` / 定理 `isoWhiskerRight_trans`

English:
theorem isoWhiskerRight_trans
  given: {G H K : C ⥤ D} (α : G ≅ H) (β : H ≅ K) (F : D ⥤ E)
  proof: ((whiskeringRight C D E).obj F).mapIso_trans α β

@[reassoc]

中文:
定理 isoWhiskerRight_trans
  条件: {G H K : C ⥤ D} (α : G ≅ H) (β : H ≅ K) (F : D ⥤ E)
  证明: ((whiskeringRight C D E).obj F).mapIso_trans α β

@[reassoc]

Depends on / 依赖: mapIso_trans, whiskeringRight
-/
theorem isoWhiskerRight_trans {G H K : C ⥤ D} (α : G ≅ H) (β : H ≅ K) (F : D ⥤ E) :
    isoWhiskerRight (α ≪≫ β) F = isoWhiskerRight α F ≪≫ isoWhiskerRight β F :=
  ((whiskeringRight C D E).obj F).mapIso_trans α β

@[reassoc]
/--
theorem `isoWhiskerLeft_trans_isoWhiskerRight` / 定理 `isoWhiskerLeft_trans_isoWhiskerRight`

English:
theorem isoWhiskerLeft_trans_isoWhiskerRight
  given: {F G : C ⥤ D} {H K : D ⥤ E} (α : F ≅ G) (β : H ≅ K)
  proof: by
  ext
  simp

中文:
定理 isoWhiskerLeft_trans_isoWhiskerRight
  条件: {F G : C ⥤ D} {H K : D ⥤ E} (α : F ≅ G) (β : H ≅ K)
  证明: by
  ext
  simp
-/
theorem isoWhiskerLeft_trans_isoWhiskerRight {F G : C ⥤ D} {H K : D ⥤ E} (α : F ≅ G) (β : H ≅ K) :
    isoWhiskerLeft F β ≪≫ isoWhiskerRight α K = isoWhiskerRight α H ≪≫ isoWhiskerLeft G β := by
  ext
  simp

variable {B : Type u₄} [Category.{v₄} B]

@[simp, to_dual none]
/--
theorem `whiskerLeft_twice` / 定理 `whiskerLeft_twice`

English:
theorem whiskerLeft_twice
  given: (F : B ⥤ C) (G : C ⥤ D) {H K : D ⥤ E} (α : H ⟶ K)
  proof: by
  cat_disch

@[simp, to_dual none]

中文:
定理 whiskerLeft_twice
  条件: (F : B ⥤ C) (G : C ⥤ D) {H K : D ⥤ E} (α : H ⟶ K)
  证明: by
  cat_disch

@[simp, to_dual none]

Depends on / 依赖: cat_disch
-/
theorem whiskerLeft_twice (F : B ⥤ C) (G : C ⥤ D) {H K : D ⥤ E} (α : H ⟶ K) :
    whiskerLeft F (whiskerLeft G α) =
    (Functor.associator _ _ _).inv ≫ whiskerLeft (F ⋙ G) α ≫ (Functor.associator _ _ _).hom := by
  cat_disch

@[simp, to_dual none]
/--
theorem `whiskerRight_twice` / 定理 `whiskerRight_twice`

English:
theorem whiskerRight_twice
  given: {H K : B ⥤ C} (F : C ⥤ D) (G : D ⥤ E) (α : H ⟶ K)
  proof: by
  cat_disch

@[to_dual none]

中文:
定理 whiskerRight_twice
  条件: {H K : B ⥤ C} (F : C ⥤ D) (G : D ⥤ E) (α : H ⟶ K)
  证明: by
  cat_disch

@[to_dual none]

Depends on / 依赖: cat_disch
-/
theorem whiskerRight_twice {H K : B ⥤ C} (F : C ⥤ D) (G : D ⥤ E) (α : H ⟶ K) :
    whiskerRight (whiskerRight α F) G =
    (Functor.associator _ _ _).hom ≫ whiskerRight α (F ⋙ G) ≫ (Functor.associator _ _ _).inv := by
  cat_disch

@[to_dual none]
/--
theorem `whiskerRight_left` / 定理 `whiskerRight_left`

English:
theorem whiskerRight_left
  given: (F : B ⥤ C) {G H : C ⥤ D} (α : G ⟶ H) (K : D ⥤ E)
  proof: by
  cat_disch

@[simp]

中文:
定理 whiskerRight_left
  条件: (F : B ⥤ C) {G H : C ⥤ D} (α : G ⟶ H) (K : D ⥤ E)
  证明: by
  cat_disch

@[simp]

Depends on / 依赖: cat_disch
-/
theorem whiskerRight_left (F : B ⥤ C) {G H : C ⥤ D} (α : G ⟶ H) (K : D ⥤ E) :
    whiskerRight (whiskerLeft F α) K =
    (Functor.associator _ _ _).hom ≫ whiskerLeft F (whiskerRight α K) ≫
      (Functor.associator _ _ _).inv := by
  cat_disch

@[simp]
/--
theorem `isoWhiskerLeft_twice` / 定理 `isoWhiskerLeft_twice`

English:
theorem isoWhiskerLeft_twice
  given: (F : B ⥤ C) (G : C ⥤ D) {H K : D ⥤ E} (α : H ≅ K)
  proof: by
  cat_disch

@[simp, reassoc]

中文:
定理 isoWhiskerLeft_twice
  条件: (F : B ⥤ C) (G : C ⥤ D) {H K : D ⥤ E} (α : H ≅ K)
  证明: by
  cat_disch

@[simp, reassoc]

Depends on / 依赖: cat_disch
-/
theorem isoWhiskerLeft_twice (F : B ⥤ C) (G : C ⥤ D) {H K : D ⥤ E} (α : H ≅ K) :
    isoWhiskerLeft F (isoWhiskerLeft G α) =
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerLeft (F ⋙ G) α ≪≫ Functor.associator _ _ _ := by
  cat_disch

@[simp, reassoc]
/--
theorem `isoWhiskerRight_twice` / 定理 `isoWhiskerRight_twice`

English:
theorem isoWhiskerRight_twice
  given: {H K : B ⥤ C} (F : C ⥤ D) (G : D ⥤ E) (α : H ≅ K)
  proof: by
  cat_disch

@[reassoc]

中文:
定理 isoWhiskerRight_twice
  条件: {H K : B ⥤ C} (F : C ⥤ D) (G : D ⥤ E) (α : H ≅ K)
  证明: by
  cat_disch

@[reassoc]

Depends on / 依赖: cat_disch
-/
theorem isoWhiskerRight_twice {H K : B ⥤ C} (F : C ⥤ D) (G : D ⥤ E) (α : H ≅ K) :
    isoWhiskerRight (isoWhiskerRight α F) G =
    Functor.associator _ _ _ ≪≫ isoWhiskerRight α (F ⋙ G) ≪≫ (Functor.associator _ _ _).symm := by
  cat_disch

@[reassoc]
/--
theorem `isoWhiskerRight_left` / 定理 `isoWhiskerRight_left`

English:
theorem isoWhiskerRight_left
  given: (F : B ⥤ C) {G H : C ⥤ D} (α : G ≅ H) (K : D ⥤ E)
  proof: by
  cat_disch

@[reassoc]

中文:
定理 isoWhiskerRight_left
  条件: (F : B ⥤ C) {G H : C ⥤ D} (α : G ≅ H) (K : D ⥤ E)
  证明: by
  cat_disch

@[reassoc]

Depends on / 依赖: cat_disch
-/
theorem isoWhiskerRight_left (F : B ⥤ C) {G H : C ⥤ D} (α : G ≅ H) (K : D ⥤ E) :
    isoWhiskerRight (isoWhiskerLeft F α) K =
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft F (isoWhiskerRight α K) ≪≫
      (Functor.associator _ _ _).symm := by
  cat_disch

@[reassoc]
/--
theorem `isoWhiskerLeft_right` / 定理 `isoWhiskerLeft_right`

English:
theorem isoWhiskerLeft_right
  given: (F : B ⥤ C) {G H : C ⥤ D} (α : G ≅ H) (K : D ⥤ E)
  proof: by
  cat_disch

中文:
定理 isoWhiskerLeft_right
  条件: (F : B ⥤ C) {G H : C ⥤ D} (α : G ≅ H) (K : D ⥤ E)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
theorem isoWhiskerLeft_right (F : B ⥤ C) {G H : C ⥤ D} (α : G ≅ H) (K : D ⥤ E) :
    isoWhiskerLeft F (isoWhiskerRight α K) =
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (isoWhiskerLeft F α) K ≪≫
      Functor.associator _ _ _ := by
  cat_disch

end

universe u₅ v₅

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {C : Type u₃} [Category.{v₃} C] {D : Type u₄} [Category.{v₄} D] {E : Type u₅} [Category.{v₅} E]
  (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) (K : D ⥤ E)

@[reassoc]
/--
theorem `triangleIso` / 定理 `triangleIso`

English:
theorem triangleIso
  proof: by cat_disch

@[reassoc]

中文:
定理 triangleIso
  证明: by cat_disch

@[reassoc]

Depends on / 依赖: cat_disch
-/
theorem triangleIso :
    associator F (𝟭 B) G ≪≫ isoWhiskerLeft F (leftUnitor G) =
      isoWhiskerRight (rightUnitor F) G := by cat_disch

@[reassoc]
/--
theorem `pentagonIso` / 定理 `pentagonIso`

English:
theorem pentagonIso
  proof: by cat_disch

中文:
定理 pentagonIso
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
theorem pentagonIso :
    isoWhiskerRight (associator F G H) K ≪≫
        associator F (G ⋙ H) K ≪≫ isoWhiskerLeft F (associator G H K) =
      associator (F ⋙ G) H K ≪≫ associator F G (H ⋙ K) := by cat_disch

/--
theorem `triangle` / 定理 `triangle`

English:
theorem triangle
  proof: by cat_disch

中文:
定理 triangle
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
theorem triangle :
    (associator F (𝟭 B) G).hom ≫ whiskerLeft F (leftUnitor G).hom =
      whiskerRight (rightUnitor F).hom G := by cat_disch

/--
theorem `pentagon` / 定理 `pentagon`

English:
theorem pentagon
  proof: by cat_disch

中文:
定理 pentagon
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
theorem pentagon :
    whiskerRight (associator F G H).hom K ≫
        (associator F (G ⋙ H) K).hom ≫ whiskerLeft F (associator G H K).hom =
      (associator (F ⋙ G) H K).hom ≫ (associator F G (H ⋙ K)).hom := by cat_disch

variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* D₁] [Category* D₂] [Category* D₃] (E : Type*) [Category* E]

/-- The obvious functor `(C₁ ⥤ D₁) ⥤ (C₂ ⥤ D₂) ⥤ (D₁ ⥤ D₂ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ E)`. -/
@[simps!, implicit_reducible]
/--
Definition of `whiskeringLeft₂` / `whiskeringLeft₂` 的定义

English:
definition whiskeringLeft₂
  signature: :
  body: { obj := fun F₂ =>
        (whiskeringRight D₁ (D₂ ⥤ E) (C₂ ⥤ E)).obj ((whiskeringLeft C₂ D₂ E).obj F₂) ⋙
          (whiskeringLeft C₁ D₁ (C₂ ⥤ E)).obj F₁
      map := fun φ => whiskerRight
        ((whiskeringRight D₁ (D₂ ⥤ E) (C₂ ⥤ E)).map ((whiskeringLeft C₂ D₂ E).map φ)) _ }
  map ψ :=
    { app := fun F₂ => whiskerLeft _ ((whiskeringLeft C₁ D₁ (C₂ ⥤ E)).map ψ) }

中文:
定义 whiskeringLeft₂
  签名: :
  定义体: { obj := fun F₂ =>
        (whiskeringRight D₁ (D₂ ⥤ E) (C₂ ⥤ E)).obj ((whiskeringLeft C₂ D₂ E).obj F₂) ⋙
          (whiskeringLeft C₁ D₁ (C₂ ⥤ E)).obj F₁
      map := fun φ => whiskerRight
        ((whiskeringRight D₁ (D₂ ⥤ E) (C₂ ⥤ E)).map ((whiskeringLeft C₂ D₂ E).map φ)) _ }
  map ψ :=
    { app := fun F₂ => whiskerLeft _ ((whiskeringLeft C₁ D₁ (C₂ ⥤ E)).map ψ) }

Depends on / 依赖: whiskerLeft, whiskerRight, whiskeringLeft, whiskeringRight
-/
def whiskeringLeft₂ :
    (C₁ ⥤ D₁) ⥤ (C₂ ⥤ D₂) ⥤ (D₁ ⥤ D₂ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ E) where
  obj F₁ :=
    { obj := fun F₂ =>
        (whiskeringRight D₁ (D₂ ⥤ E) (C₂ ⥤ E)).obj ((whiskeringLeft C₂ D₂ E).obj F₂) ⋙
          (whiskeringLeft C₁ D₁ (C₂ ⥤ E)).obj F₁
      map := fun φ => whiskerRight
        ((whiskeringRight D₁ (D₂ ⥤ E) (C₂ ⥤ E)).map ((whiskeringLeft C₂ D₂ E).map φ)) _ }
  map ψ :=
    { app := fun F₂ => whiskerLeft _ ((whiskeringLeft C₁ D₁ (C₂ ⥤ E)).map ψ) }

/-- Auxiliary definition for `whiskeringLeft₃`. -/
@[implicit_reducible, simps!]
/--
Definition of `whiskeringLeft₃ObjObjObj` / `whiskeringLeft₃ObjObjObj` 的定义

English:
definition whiskeringLeft₃ObjObjObj
  signature: (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (F₃ : C₃ ⥤ D₃)
  body: (whiskeringRight _ _ _).obj (((whiskeringLeft₂ E).obj F₂).obj F₃) ⋙
    (whiskeringLeft C₁ D₁ _).obj F₁

中文:
定义 whiskeringLeft₃ObjObjObj
  签名: (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (F₃ : C₃ ⥤ D₃)
  定义体: (whiskeringRight _ _ _).obj (((whiskeringLeft₂ E).obj F₂).obj F₃) ⋙
    (whiskeringLeft C₁ D₁ _).obj F₁

Depends on / 依赖: whiskeringLeft, whiskeringRight
-/
def whiskeringLeft₃ObjObjObj (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (F₃ : C₃ ⥤ D₃) :
    (D₁ ⥤ D₂ ⥤ D₃ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ E :=
  (whiskeringRight _ _ _).obj (((whiskeringLeft₂ E).obj F₂).obj F₃) ⋙
    (whiskeringLeft C₁ D₁ _).obj F₁

/-- Auxiliary definition for `whiskeringLeft₃`. -/
@[implicit_reducible, simps]
/--
Definition of `whiskeringLeft₃ObjObjMap` / `whiskeringLeft₃ObjObjMap` 的定义

English:
definition whiskeringLeft₃ObjObjMap
  signature: (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) {F₃ F₃' : C₃ ⥤ D₃} (τ₃ : F₃ ⟶ F₃')
  body: whiskerLeft _ (whiskerLeft _ (((whiskeringLeft₂ E).obj F₂).map τ₃))

中文:
定义 whiskeringLeft₃ObjObjMap
  签名: (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) {F₃ F₃' : C₃ ⥤ D₃} (τ₃ : F₃ ⟶ F₃')
  定义体: whiskerLeft _ (whiskerLeft _ (((whiskeringLeft₂ E).obj F₂).map τ₃))

Depends on / 依赖: whiskerLeft
-/
def whiskeringLeft₃ObjObjMap (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) {F₃ F₃' : C₃ ⥤ D₃} (τ₃ : F₃ ⟶ F₃') :
    whiskeringLeft₃ObjObjObj E F₁ F₂ F₃ ⟶
      whiskeringLeft₃ObjObjObj E F₁ F₂ F₃' where
  app F := whiskerLeft _ (whiskerLeft _ (((whiskeringLeft₂ E).obj F₂).map τ₃))

variable (C₃ D₃) in
/-- Auxiliary definition for `whiskeringLeft₃`. -/
@[implicit_reducible, simps]
/--
Definition of `whiskeringLeft₃ObjObj` / `whiskeringLeft₃ObjObj` 的定义

English:
definition whiskeringLeft₃ObjObj
  signature: (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂)
  body: whiskeringLeft₃ObjObjObj E F₁ F₂ F₃
  map τ₃ := whiskeringLeft₃ObjObjMap E F₁ F₂ τ₃

中文:
定义 whiskeringLeft₃ObjObj
  签名: (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂)
  定义体: whiskeringLeft₃ObjObjObj E F₁ F₂ F₃
  map τ₃ := whiskeringLeft₃ObjObjMap E F₁ F₂ τ₃
-/
def whiskeringLeft₃ObjObj (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) :
    (C₃ ⥤ D₃) ⥤ (D₁ ⥤ D₂ ⥤ D₃ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) where
  obj F₃ := whiskeringLeft₃ObjObjObj E F₁ F₂ F₃
  map τ₃ := whiskeringLeft₃ObjObjMap E F₁ F₂ τ₃

variable (C₃ D₃) in
/-- Auxiliary definition for `whiskeringLeft₃`. -/
@[implicit_reducible, simps]
/--
Definition of `whiskeringLeft₃ObjMap` / `whiskeringLeft₃ObjMap` 的定义

English:
definition whiskeringLeft₃ObjMap
  signature: (F₁ : C₁ ⥤ D₁) {F₂ F₂' : C₂ ⥤ D₂} (τ₂ : F₂ ⟶ F₂')
  body: whiskerRight ((whiskeringRight _ _ _).map (((whiskeringLeft₂ E).map τ₂).app F₃)) _

中文:
定义 whiskeringLeft₃ObjMap
  签名: (F₁ : C₁ ⥤ D₁) {F₂ F₂' : C₂ ⥤ D₂} (τ₂ : F₂ ⟶ F₂')
  定义体: whiskerRight ((whiskeringRight _ _ _).map (((whiskeringLeft₂ E).map τ₂).app F₃)) _

Depends on / 依赖: whiskerRight, whiskeringRight
-/
def whiskeringLeft₃ObjMap (F₁ : C₁ ⥤ D₁) {F₂ F₂' : C₂ ⥤ D₂} (τ₂ : F₂ ⟶ F₂') :
    whiskeringLeft₃ObjObj C₃ D₃ E F₁ F₂ ⟶ whiskeringLeft₃ObjObj C₃ D₃ E F₁ F₂' where
  app F₃ := whiskerRight ((whiskeringRight _ _ _).map (((whiskeringLeft₂ E).map τ₂).app F₃)) _

variable (C₂ C₃ D₂ D₃) in
/-- Auxiliary definition for `whiskeringLeft₃`. -/
@[implicit_reducible, simps]
/--
Definition of `whiskeringLeft₃Obj` / `whiskeringLeft₃Obj` 的定义

English:
definition whiskeringLeft₃Obj
  signature: (F₁ : C₁ ⥤ D₁)
  body: whiskeringLeft₃ObjObj C₃ D₃ E F₁ F₂
  map τ₂ := whiskeringLeft₃ObjMap C₃ D₃ E F₁ τ₂

中文:
定义 whiskeringLeft₃Obj
  签名: (F₁ : C₁ ⥤ D₁)
  定义体: whiskeringLeft₃ObjObj C₃ D₃ E F₁ F₂
  map τ₂ := whiskeringLeft₃ObjMap C₃ D₃ E F₁ τ₂
-/
def whiskeringLeft₃Obj (F₁ : C₁ ⥤ D₁) :
    (C₂ ⥤ D₂) ⥤ (C₃ ⥤ D₃) ⥤ (D₁ ⥤ D₂ ⥤ D₃ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) where
  obj F₂ := whiskeringLeft₃ObjObj C₃ D₃ E F₁ F₂
  map τ₂ := whiskeringLeft₃ObjMap C₃ D₃ E F₁ τ₂

variable (C₂ C₃ D₂ D₃) in
/-- Auxiliary definition for `whiskeringLeft₃`. -/
@[implicit_reducible, simps]
/--
Definition of `whiskeringLeft₃Map` / `whiskeringLeft₃Map` 的定义

English:
definition whiskeringLeft₃Map
  signature: {F₁ F₁' : C₁ ⥤ D₁} (τ₁ : F₁ ⟶ F₁')
  body: { app F₃ := whiskerLeft _ ((whiskeringLeft _ _ _).map τ₁) }

中文:
定义 whiskeringLeft₃Map
  签名: {F₁ F₁' : C₁ ⥤ D₁} (τ₁ : F₁ ⟶ F₁')
  定义体: { app F₃ := whiskerLeft _ ((whiskeringLeft _ _ _).map τ₁) }

Depends on / 依赖: whiskerLeft, whiskeringLeft
-/
def whiskeringLeft₃Map {F₁ F₁' : C₁ ⥤ D₁} (τ₁ : F₁ ⟶ F₁') :
    whiskeringLeft₃Obj C₂ C₃ D₂ D₃ E F₁ ⟶ whiskeringLeft₃Obj C₂ C₃ D₂ D₃ E F₁' where
  app F₂ := { app F₃ := whiskerLeft _ ((whiskeringLeft _ _ _).map τ₁) }

/-- The obvious functor
`(C₁ ⥤ D₁) ⥤ (C₂ ⥤ D₂) ⥤ (C₃ ⥤ D₃) ⥤ (D₁ ⥤ D₂ ⥤ D₃ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ E)`. -/
@[simps!, implicit_reducible]
/--
Definition of `whiskeringLeft₃` / `whiskeringLeft₃` 的定义

English:
definition whiskeringLeft₃
  signature: :
  body: whiskeringLeft₃Obj C₂ C₃ D₂ D₃ E F₁
  map τ₁ := whiskeringLeft₃Map C₂ C₃ D₂ D₃ E τ₁

中文:
定义 whiskeringLeft₃
  签名: :
  定义体: whiskeringLeft₃Obj C₂ C₃ D₂ D₃ E F₁
  map τ₁ := whiskeringLeft₃Map C₂ C₃ D₂ D₃ E τ₁
-/
def whiskeringLeft₃ :
    (C₁ ⥤ D₁) ⥤ (C₂ ⥤ D₂) ⥤ (C₃ ⥤ D₃) ⥤ (D₁ ⥤ D₂ ⥤ D₃ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) where
  obj F₁ := whiskeringLeft₃Obj C₂ C₃ D₂ D₃ E F₁
  map τ₁ := whiskeringLeft₃Map C₂ C₃ D₂ D₃ E τ₁

variable {E}

/-- The "postcomposition" with a functor `E ⥤ E'` gives a functor
`(E ⥤ E') ⥤ (C₁ ⥤ C₂ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ E'`. -/
@[simps!, implicit_reducible]
/--
Definition of `postcompose₂` / `postcompose₂` 的定义

English:
definition postcompose₂
  signature: {E' : Type*} [Category* E']
  body: whiskeringRight C₂ _ _ ⋙ whiskeringRight C₁ _ _

中文:
定义 postcompose₂
  签名: {E' : 类型} [范畴* E']
  定义体: whiskeringRight C₂ _ _ ⋙ whiskeringRight C₁ _ _

Depends on / 依赖: whiskeringRight
-/
def postcompose₂ {E' : Type*} [Category* E'] :
    (E ⥤ E') ⥤ (C₁ ⥤ C₂ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ E' :=
  whiskeringRight C₂ _ _ ⋙ whiskeringRight C₁ _ _

/-- The "postcomposition" with a functor `E ⥤ E'` gives a functor
`(E ⥤ E') ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ E'`. -/
@[simps!, implicit_reducible]
/--
Definition of `postcompose₃` / `postcompose₃` 的定义

English:
definition postcompose₃
  signature: {E' : Type*} [Category* E']
  body: whiskeringRight C₃ _ _ ⋙ whiskeringRight C₂ _ _ ⋙ whiskeringRight C₁ _ _

中文:
定义 postcompose₃
  签名: {E' : 类型} [范畴* E']
  定义体: whiskeringRight C₃ _ _ ⋙ whiskeringRight C₂ _ _ ⋙ whiskeringRight C₁ _ _

Depends on / 依赖: whiskeringRight
-/
def postcompose₃ {E' : Type*} [Category* E'] :
    (E ⥤ E') ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ E' :=
  whiskeringRight C₃ _ _ ⋙ whiskeringRight C₂ _ _ ⋙ whiskeringRight C₁ _ _

end Functor

end CategoryTheory
