/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Products.Bifunctor

/-!
# A Fubini theorem for categorical (co)limits

We prove that $lim_{J × K} G = lim_J (lim_K G(j, -))$ for a functor `G : J × K ⥤ C`,
when all the appropriate limits exist.

We begin working with a functor `F : J ⥤ K ⥤ C`. We'll write `G : J × K ⥤ C` for the associated
"uncurried" functor.

In the first part, given a coherent family `D` of limit cones over the functors `F.obj j`,
and a cone `c` over `G`, we construct a cone over the cone points of `D`.
We then show that if `c` is a limit cone, the constructed cone is also a limit cone.

In the second part, we state the Fubini theorem in the setting where limits are
provided by suitable `HasLimit` classes.

We construct
`limitUncurryIsoLimitCompLim F : limit (uncurry.obj F) ≅ limit (F ⋙ lim)`
and give simp lemmas characterising it.
For convenience, we also provide
`limitIsoLimitCurryCompLim G : limit G ≅ limit ((curry.obj G) ⋙ lim)`
in terms of the uncurried functor.

All statements have their counterpart for colimits.
-/

@[expose] public section


open CategoryTheory Functor

namespace CategoryTheory.Limits

variable {J K : Type*} [Category* J] [Category* K]
variable {C : Type*} [Category* C]
variable (F : J ⥤ K ⥤ C) (G : J × K ⥤ C)

-- We could try introducing a "dependent functor type" to handle this?
/--
Definition of `DiagramOfCones` / `DiagramOfCones` 的定义

English:
structure DiagramOfCones
  parameters: where
  axioms and operations (4):
    - obj : forall j : J, Cone (F.obj j)
    - map : forall {j j' : J} (f : j ⟶ j'), (Cone.postcompose (F.map f)).obj (obj j) ⟶ obj j'
    - id : forall j : J, (map (𝟙 j)).hom = 𝟙 _  [default: by cat_disch]
    - comp : forall {j₁ j₂ j₃ : J} (f : j₁ ⟶ j₂) (g : j₂ ⟶ j₃), (map (f ≫ g)).hom = (map f).hom ≫ (map g).hom  [default: by cat_disch]

中文:
结构 DiagramOfCones
  参数: where
  公理与运算 (4 个):
    - obj : 对任意 j : J, 锥 (F.obj j)
    - map : 对任意 {j j' : J} (f : j ⟶ j'), (锥.postcompose (F.map f)).obj (obj j) ⟶ obj j'
    - id : 对任意 j : J, (map (𝟙 j)).hom = 𝟙 _  [默认: by cat_disch]
    - comp : 对任意 {j₁ j₂ j₃ : J} (f : j₁ ⟶ j₂) (g : j₂ ⟶ j₃), (map (f ≫ g)).hom = (map f).hom ≫ (map g).hom  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure DiagramOfCones where
  /-- For each object, a cone. -/
  obj : forall j : J, Cone (F.obj j)
  /-- For each map, a map of cones. -/
  map : forall {j j' : J} (f : j ⟶ j'), (Cone.postcompose (F.map f)).obj (obj j) ⟶ obj j'
  id : forall j : J, (map (𝟙 j)).hom = 𝟙 _ := by cat_disch
  comp : forall {j₁ j₂ j₃ : J} (f : j₁ ⟶ j₂) (g : j₂ ⟶ j₃),
    (map (f ≫ g)).hom = (map f).hom ≫ (map g).hom := by cat_disch

/--
Definition of `DiagramOfCocones` / `DiagramOfCocones` 的定义

English:
structure DiagramOfCocones
  parameters: where
  axioms and operations (4):
    - obj : forall j : J, Cocone (F.obj j)
    - map : forall {j j' : J} (f : j ⟶ j'), (obj j) ⟶ (Cocone.precompose (F.map f)).obj (obj j')
    - id : forall j : J, (map (𝟙 j)).hom = 𝟙 _  [default: by cat_disch]
    - comp : forall {j₁ j₂ j₃ : J} (f : j₁ ⟶ j₂) (g : j₂ ⟶ j₃), (map (f ≫ g)).hom = (map f).hom ≫ (map g).hom  [default: by cat_disch]

中文:
结构 DiagramOfCocones
  参数: where
  公理与运算 (4 个):
    - obj : 对任意 j : J, 余锥 (F.obj j)
    - map : 对任意 {j j' : J} (f : j ⟶ j'), (obj j) ⟶ (余锥.precompose (F.map f)).obj (obj j')
    - id : 对任意 j : J, (map (𝟙 j)).hom = 𝟙 _  [默认: by cat_disch]
    - comp : 对任意 {j₁ j₂ j₃ : J} (f : j₁ ⟶ j₂) (g : j₂ ⟶ j₃), (map (f ≫ g)).hom = (map f).hom ≫ (map g).hom  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure DiagramOfCocones where
  /-- For each object, a cocone. -/
  obj : forall j : J, Cocone (F.obj j)
  /-- For each map, a map of cocones. -/
  map : forall {j j' : J} (f : j ⟶ j'), (obj j) ⟶ (Cocone.precompose (F.map f)).obj (obj j')
  id : forall j : J, (map (𝟙 j)).hom = 𝟙 _ := by cat_disch
  comp : forall {j₁ j₂ j₃ : J} (f : j₁ ⟶ j₂) (g : j₂ ⟶ j₃),
    (map (f ≫ g)).hom = (map f).hom ≫ (map g).hom := by cat_disch

variable {F}

/-- Extract the functor `J ⥤ C` consisting of the cone points and the maps between them,
from a `DiagramOfCones`.
-/
@[simps]
/--
Definition of `DiagramOfCones.conePoints` / `DiagramOfCones.conePoints` 的定义

English:
definition DiagramOfCones.conePoints
  signature: (D : DiagramOfCones F)
  body: (D.obj j).pt
  map f := (D.map f).hom
  map_id j := D.id j
  map_comp f g := D.comp f g

中文:
定义 DiagramOfCones.conePoints
  签名: (D : DiagramOfCones F)
  定义体: (D.obj j).pt
  map f := (D.map f).hom
  map_id j := D.id j
  map_comp f g := D.comp f g

Depends on / 依赖: D.obj
-/
def DiagramOfCones.conePoints (D : DiagramOfCones F) : J ⥤ C where
  obj j := (D.obj j).pt
  map f := (D.map f).hom
  map_id j := D.id j
  map_comp f g := D.comp f g

/-- Extract the functor `J ⥤ C` consisting of the cocone points and the maps between them,
from a `DiagramOfCocones`.
-/
@[simps]
/--
Definition of `DiagramOfCocones.coconePoints` / `DiagramOfCocones.coconePoints` 的定义

English:
definition DiagramOfCocones.coconePoints
  signature: (D : DiagramOfCocones F)
  body: (D.obj j).pt
  map f := (D.map f).hom
  map_id j := D.id j
  map_comp f g := D.comp f g

中文:
定义 DiagramOfCocones.coconePoints
  签名: (D : DiagramOfCocones F)
  定义体: (D.obj j).pt
  map f := (D.map f).hom
  map_id j := D.id j
  map_comp f g := D.comp f g

Depends on / 依赖: D.obj
-/
def DiagramOfCocones.coconePoints (D : DiagramOfCocones F) : J ⥤ C where
  obj j := (D.obj j).pt
  map f := (D.map f).hom
  map_id j := D.id j
  map_comp f g := D.comp f g

set_option backward.isDefEq.respectTransparency false in
/-- Given a diagram `D` of limit cones over the `F.obj j`, and a cone over `uncurry.obj F`,
we can construct a cone over the diagram consisting of the cone points from `D`.
-/
@[simps]
/--
Definition of `coneOfConeUncurry` / `coneOfConeUncurry` 的定义

English:
definition coneOfConeUncurry
  signature: {D : DiagramOfCones F} (Q : forall j, IsLimit (D.obj j))
  body: c.pt
  π :=
    { app := fun j =>
        (Q j).lift
          { pt := c.pt
            π :=
              { app := fun k => c.π.app (j, k)
                naturality := fun k k' f => by
                  simpa using @NatTrans.naturality _ _ _ _ _ _ c.π (j, k) (j, k') (𝟙 j, f) } }
      naturality :

中文:
定义 coneOfConeUncurry
  签名: {D : DiagramOfCones F} (Q : 对任意 j, 是极限 (D.obj j))
  定义体: c.pt
  π :=
    { app := fun j =>
        (Q j).lift
          { pt := c.pt
            π :=
              { app := fun k => c.π.app (j, k)
                naturality := fun k k' f => by
                  simpa using @NatTrans.naturality _ _ _ _ _ _ c.π (j, k) (j, k') (𝟙 j, f) } }
      naturality :

Depends on / 依赖: Localization, Localization.inverts, c.pt, inverts, z.hs
-/
def coneOfConeUncurry {D : DiagramOfCones F} (Q : forall j, IsLimit (D.obj j))
    (c : Cone (uncurry.obj F)) : Cone D.conePoints where
  pt := c.pt
  π :=
    { app := fun j =>
        (Q j).lift
          { pt := c.pt
            π :=
              { app := fun k => c.π.app (j, k)
                naturality := fun k k' f => by
                  simpa using @NatTrans.naturality _ _ _ _ _ _ c.π (j, k) (j, k') (𝟙 j, f) } }
      naturality := fun j j' f =>
        (Q j').hom_ext
          (fun k => by simpa using @NatTrans.naturality _ _ _ _ _ _ c.π (j, k) (j', k) (f, 𝟙 k)) }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a diagram `D` of limit cones over the `curry.obj G j`, and a cone over `G`,
we can construct a cone over the diagram consisting of the cone points from `D`.
-/
@[simps]
/--
Definition of `coneOfConeCurry` / `coneOfConeCurry` 的定义

English:
definition coneOfConeCurry
  signature: {D : DiagramOfCones (curry.obj G)} (Q : forall j, IsLimit (D.obj j))
  body: c.pt
  π :=
    { app j := (Q j).lift
        { pt := c.pt
          π := { app k := c.π.app (j, k) } }
      naturality {_ j'} _ := (Q j').hom_ext (by simp) }

中文:
定义 coneOfConeCurry
  签名: {D : DiagramOfCones (curry.obj G)} (Q : 对任意 j, 是极限 (D.obj j))
  定义体: c.pt
  π :=
    { app j := (Q j).lift
        { pt := c.pt
          π := { app k := c.π.app (j, k) } }
      naturality {_ j'} _ := (Q j').hom_ext (by simp) }

Depends on / 依赖: c.pt
-/
def coneOfConeCurry {D : DiagramOfCones (curry.obj G)} (Q : forall j, IsLimit (D.obj j))
    (c : Cone G) : Cone D.conePoints where
  pt := c.pt
  π :=
    { app j := (Q j).lift
        { pt := c.pt
          π := { app k := c.π.app (j, k) } }
      naturality {_ j'} _ := (Q j').hom_ext (by simp) }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open scoped CategoryTheory.Prod in
/-- Given a diagram `D` of colimit cocones over the `F.obj j`, and a cocone over `uncurry.obj F`,
we can construct a cocone over the diagram consisting of the cocone points from `D`.
-/
@[simps]
/--
Definition of `coconeOfCoconeUncurry` / `coconeOfCoconeUncurry` 的定义

English:
definition coconeOfCoconeUncurry
  signature: {D : DiagramOfCocones F} (Q : forall j, IsColimit (D.obj j))
  body: c.pt
  ι :=
    { app := fun j =>
        (Q j).desc
          { pt := c.pt
            ι :=
              { app := fun k => c.ι.app (j, k)
                naturality := fun k k' f => by
                  dsimp; simp only [Category.comp_id]
                  conv_lhs =>
                    arg 1; eq

中文:
定义 coconeOfCoconeUncurry
  签名: {D : DiagramOfCocones F} (Q : 对任意 j, 是余极限 (D.obj j))
  定义体: c.pt
  ι :=
    { app := fun j =>
        (Q j).desc
          { pt := c.pt
            ι :=
              { app := fun k => c.ι.app (j, k)
                naturality := fun k k' f => by
                  dsimp; simp only [Category.comp_id]
                  conv_lhs =>
                    arg 1; eq

Depends on / 依赖: c.pt
-/
def coconeOfCoconeUncurry {D : DiagramOfCocones F} (Q : forall j, IsColimit (D.obj j))
    (c : Cocone (uncurry.obj F)) : Cocone D.coconePoints where
  pt := c.pt
  ι :=
    { app := fun j =>
        (Q j).desc
          { pt := c.pt
            ι :=
              { app := fun k => c.ι.app (j, k)
                naturality := fun k k' f => by
                  dsimp; simp only [Category.comp_id]
                  conv_lhs =>
                    arg 1; equals (F.map (𝟙 _)).app _ ≫ (F.obj j).map f =>
                      simp
                  conv_lhs => arg 1; rw [← uncurry_obj_map F (𝟙 j ×ₘ f)]
                  rw [c.w] } }
      naturality := fun j j' f =>
        (Q j).hom_ext
          (by
            dsimp
            intro k
            simp only [Limits.CoconeMorphism.w_assoc, Limits.Cocone.precompose_obj_ι,
              Limits.IsColimit.fac, NatTrans.comp_app, Category.comp_id,
              Category.assoc]
            have := @NatTrans.naturality _ _ _ _ _ _ c.ι (j, k) (j', k) (f, 𝟙 k)
            dsimp at this
            simp only [Category.comp_id, CategoryTheory.Functor.map_id] at this
            exact this) }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a diagram `D` of colimit cocones under the `curry.obj G j`, and a cocone under `G`,
we can construct a cocone under the diagram consisting of the cocone points from `D`.
-/
@[simps]
/--
Definition of `coconeOfCoconeCurry` / `coconeOfCoconeCurry` 的定义

English:
definition coconeOfCoconeCurry
  signature: {D : DiagramOfCocones (curry.obj G)} (Q : forall j, IsColimit (D.obj j))
  body: c.pt
  ι :=
    { app j := (Q j).desc
        { pt := c.pt
          ι := { app k := c.ι.app (j, k) } }
      naturality {j _} _ := (Q j).hom_ext (by simp) }

中文:
定义 coconeOfCoconeCurry
  签名: {D : DiagramOfCocones (curry.obj G)} (Q : 对任意 j, 是余极限 (D.obj j))
  定义体: c.pt
  ι :=
    { app j := (Q j).desc
        { pt := c.pt
          ι := { app k := c.ι.app (j, k) } }
      naturality {j _} _ := (Q j).hom_ext (by simp) }

Depends on / 依赖: c.pt
-/
def coconeOfCoconeCurry {D : DiagramOfCocones (curry.obj G)} (Q : forall j, IsColimit (D.obj j))
    (c : Cocone G) : Cocone D.coconePoints where
  pt := c.pt
  ι :=
    { app j := (Q j).desc
        { pt := c.pt
          ι := { app k := c.ι.app (j, k) } }
      naturality {j _} _ := (Q j).hom_ext (by simp) }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `coneOfConeUncurryIsLimit` / `coneOfConeUncurryIsLimit` 的定义

English:
definition coneOfConeUncurryIsLimit
  signature: {D : DiagramOfCones F} (Q : forall j, IsLimit (D.obj j))
  body: P.lift
      { pt := s.pt
        π :=
          { app := fun p => s.π.app p.1 ≫ (D.obj p.1).π.app p.2
            naturality := fun p p' f => by
              dsimp; simp only [Category.id_comp, Category.assoc]
              rcases p with ⟨j, k⟩
              rcases p' with ⟨j', k'⟩
              r

中文:
定义 coneOfConeUncurryIsLimit
  签名: {D : DiagramOfCones F} (Q : 对任意 j, 是极限 (D.obj j))
  定义体: P.lift
      { pt := s.pt
        π :=
          { app := fun p => s.π.app p.1 ≫ (D.obj p.1).π.app p.2
            naturality := fun p p' f => by
              dsimp; simp only [Category.id_comp, Category.assoc]
              rcases p with ⟨j, k⟩
              rcases p' with ⟨j', k'⟩
              r

Depends on / 依赖: Category, Category.assoc, Category.id_comp, D.map, D.obj, Functor, Functor.const_obj_map, NatTrans, NatTrans.naturality, P.lift, const_obj_map, id_comp, naturality, s.pt, slice_rhs
-/
def coneOfConeUncurryIsLimit {D : DiagramOfCones F} (Q : forall j, IsLimit (D.obj j))
    {c : Cone (uncurry.obj F)} (P : IsLimit c) : IsLimit (coneOfConeUncurry Q c) where
  lift s :=
    P.lift
      { pt := s.pt
        π :=
          { app := fun p => s.π.app p.1 ≫ (D.obj p.1).π.app p.2
            naturality := fun p p' f => by
              dsimp; simp only [Category.id_comp, Category.assoc]
              rcases p with ⟨j, k⟩
              rcases p' with ⟨j', k'⟩
              rcases f with ⟨fj, fk⟩
              dsimp
              slice_rhs 3 4 => rw [← NatTrans.naturality]
              slice_rhs 2 3 => rw [← (D.obj j).π.naturality]
              simp only [Functor.const_obj_map, Category.id_comp, Category.assoc]
              have w := (D.map fj).w k'
              dsimp at w
              rw [← w]
              have n := s.π.naturality fj
              dsimp at n
              simp only [Category.id_comp] at n
              rw [n]
              simp } }
  fac s j := by
    apply (Q j).hom_ext
    intro k
    simp
  uniq s m w := by
    refine P.uniq
      { pt := s.pt
        π := _ } m ?_
    rintro ⟨j, k⟩
    dsimp
    rw [← w j]
    simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `IsLimit.ofConeOfConeUncurry` / `IsLimit.ofConeOfConeUncurry` 的定义

English:
definition IsLimit.ofConeOfConeUncurry
  signature: {D : DiagramOfCones F} (Q : forall j, IsLimit (D.obj j))
  body: -- These constructions are used in various fields of the proof so we abstract them here.
  letI E (j : J) : Prod.sectR j K ⋙ uncurry.obj F ≅ F.obj j :=
    NatIso.ofComponents (fun _ => Iso.refl _)
  letI S (s : Cone (uncurry.obj F)) : Cone D.conePoints :=
    { pt := s.pt
      π :=
        { app j

中文:
定义 是极限.ofConeOfConeUncurry
  签名: {D : DiagramOfCones F} (Q : 对任意 j, 是极限 (D.obj j))
  定义体: -- These constructions are used in various fields of the proof so we abstract them here.
  letI E (j : J) : Prod.sectR j K ⋙ uncurry.obj F ≅ F.obj j :=
    NatIso.ofComponents (fun _ => Iso.refl _)
  letI S (s : Cone (uncurry.obj F)) : Cone D.conePoints :=
    { pt := s.pt
      π :=
        { app j
-/
def IsLimit.ofConeOfConeUncurry {D : DiagramOfCones F} (Q : forall j, IsLimit (D.obj j))
    {c : Cone (uncurry.obj F)} (P : IsLimit (coneOfConeUncurry Q c)) : IsLimit c :=
  -- These constructions are used in various fields of the proof so we abstract them here.
  letI E (j : J) : Prod.sectR j K ⋙ uncurry.obj F ≅ F.obj j :=
    NatIso.ofComponents (fun _ => Iso.refl _)
  letI S (s : Cone (uncurry.obj F)) : Cone D.conePoints :=
    { pt := s.pt
      π :=
        { app j := (Q j).lift <|
(Cone.postcompose (E j).hom).obj s.whisker (Prod.sectR j K)
naturality {j' j} f := (Q j).hom_ext
            fun k => by simpa [E] using s.π.naturality ((Prod.sectL J k).map f) } }
  { lift s := P.lift (S s)
    fac s p := by
      have h1 := (Q p.1).fac ((Cone.postcompose (E p.1).hom).obj <|
        s.whisker (Prod.sectR p.1 K)) p.2
      simp only [Functor.comp_obj, Prod.sectR_obj, uncurry_obj_obj,
        Cone.postcompose_obj_pt, Cone.whisker_pt, Cone.postcompose_obj_π,
        Cone.whisker_π, NatTrans.comp_app, Functor.const_obj_obj, whiskerLeft_app,
        NatIso.ofComponents_hom_app, Iso.refl_hom, Category.comp_id, E] at h1
      have h2 := (P.fac (S s) p.1)
      dsimp only [Functor.comp_obj, Prod.sectR_obj, uncurry_obj_obj, NatTrans.id_app,
        Functor.const_obj_obj, DiagramOfCones.conePoints_obj, DiagramOfCones.conePoints_map,
        Functor.const_obj_map, id_eq, Cone.postcompose_obj_pt, Cone.whisker_pt,
        Cone.postcompose_obj_π, Cone.whisker_π, NatTrans.comp_app, whiskerLeft_app,
        NatIso.ofComponents_hom_app, Iso.refl_hom, Prod.sectL_obj, Prod.sectL_map, eq_mp_eq_cast,
        eq_mpr_eq_cast, coneOfConeUncurry_pt, coneOfConeUncurry_π_app, S, E] at h2 ⊢
      simp [← h1, ← h2]
uniq s f hf := P.uniq (s := S s) _
fun j => (Q j).hom_ext fun k => by simpa [S, E] using hf (j, k) }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `coconeOfCoconeUncurryIsColimit` / `coconeOfCoconeUncurryIsColimit` 的定义

English:
definition coconeOfCoconeUncurryIsColimit
  signature: {D : DiagramOfCocones F} (Q : forall j, IsColimit (D.obj j))
  body: P.desc
      { pt := s.pt
        ι :=
          { app := fun p => (D.obj p.1).ι.app p.2 ≫ s.ι.app p.1
            naturality := fun p p' f => by
              dsimp; simp only [Category.assoc]
              rcases p with ⟨j, k⟩
              rcases p' with ⟨j', k'⟩
              rcases f with ⟨fj, 

中文:
定义 coconeOfCoconeUncurryIsColimit
  签名: {D : DiagramOfCocones F} (Q : 对任意 j, 是余极限 (D.obj j))
  定义体: P.desc
      { pt := s.pt
        ι :=
          { app := fun p => (D.obj p.1).ι.app p.2 ≫ s.ι.app p.1
            naturality := fun p p' f => by
              dsimp; simp only [Category.assoc]
              rcases p with ⟨j, k⟩
              rcases p' with ⟨j', k'⟩
              rcases f with ⟨fj, 

Depends on / 依赖: Category, Category.assoc, Category.comp_id, D.map, D.obj, Functor, Functor.const_obj_map, P.desc, comp_id, const_obj_map, hom_ext, naturality, s.pt, slice_lhs
-/
def coconeOfCoconeUncurryIsColimit {D : DiagramOfCocones F} (Q : forall j, IsColimit (D.obj j))
    {c : Cocone (uncurry.obj F)} (P : IsColimit c) : IsColimit (coconeOfCoconeUncurry Q c) where
  desc s :=
    P.desc
      { pt := s.pt
        ι :=
          { app := fun p => (D.obj p.1).ι.app p.2 ≫ s.ι.app p.1
            naturality := fun p p' f => by
              dsimp; simp only [Category.assoc]
              rcases p with ⟨j, k⟩
              rcases p' with ⟨j', k'⟩
              rcases f with ⟨fj, fk⟩
              dsimp
              slice_lhs 2 3 => rw [(D.obj j').ι.naturality]
              simp only [Functor.const_obj_map, Category.assoc]
              have w := (D.map fj).w k
              dsimp at w
              slice_lhs 1 2 => rw [← w]
              have n := s.ι.naturality fj
              dsimp at n
              simp only [Category.comp_id] at n
              rw [← n]
              simp } }
  fac s j := by
    apply (Q j).hom_ext
    intro k
    simp
  uniq s m w := by
    refine P.uniq
      { pt := s.pt
        ι := _ } m ?_
    rintro ⟨j, k⟩
    dsimp
    rw [← w j]
    simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `IsColimit.ofCoconeUncurry` / `IsColimit.ofCoconeUncurry` 的定义

English:
definition IsColimit.ofCoconeUncurry
  signature: {D : DiagramOfCocones F}
  body: -- These constructions are used in various fields of the proof so we abstract them here.
  letI E (j : J) : (Prod.sectR j K ⋙ uncurry.obj F ≅ F.obj j) :=
    NatIso.ofComponents (fun _ => Iso.refl _)
  letI S (s : Cocone (uncurry.obj F)) : Cocone D.coconePoints :=
    { pt := s.pt
      ι :=
       

中文:
定义 是余极限.ofCoconeUncurry
  签名: {D : DiagramOfCocones F}
  定义体: -- These constructions are used in various fields of the proof so we abstract them here.
  letI E (j : J) : (Prod.sectR j K ⋙ uncurry.obj F ≅ F.obj j) :=
    NatIso.ofComponents (fun _ => Iso.refl _)
  letI S (s : Cocone (uncurry.obj F)) : Cocone D.coconePoints :=
    { pt := s.pt
      ι :=
       
-/
def IsColimit.ofCoconeUncurry {D : DiagramOfCocones F}
    (Q : forall j, IsColimit (D.obj j)) {c : Cocone (uncurry.obj F)}
    (P : IsColimit (coconeOfCoconeUncurry Q c)) : IsColimit c :=
  -- These constructions are used in various fields of the proof so we abstract them here.
  letI E (j : J) : (Prod.sectR j K ⋙ uncurry.obj F ≅ F.obj j) :=
    NatIso.ofComponents (fun _ => Iso.refl _)
  letI S (s : Cocone (uncurry.obj F)) : Cocone D.coconePoints :=
    { pt := s.pt
      ι :=
        { app j := (Q j).desc <|
(Cocone.precompose (E j).inv).obj s.whisker (Prod.sectR j K)
naturality {j j'} f := (Q j).hom_ext
            fun k => by simpa [E] using s.ι.naturality ((Prod.sectL J k).map f) } }
  { desc s := P.desc (S s)
    fac s p := by
      have h1 := (Q p.1).fac ((Cocone.precompose (E p.1).inv).obj <|
        s.whisker (Prod.sectR p.1 K)) p.2
      simp only [Functor.comp_obj, Prod.sectR_obj, uncurry_obj_obj,
        Cocone.precompose_obj_pt, Cocone.whisker_pt, Functor.const_obj_obj,
        Cocone.precompose_obj_ι, Cocone.whisker_ι, NatTrans.comp_app, NatIso.ofComponents_inv_app,
        Iso.refl_inv, whiskerLeft_app, Category.id_comp, E] at h1
      have h2 := (P.fac (S s) p.1)
      dsimp only [DiagramOfCocones.coconePoints_obj, Functor.comp_obj, Prod.sectR_obj,
        uncurry_obj_obj, NatTrans.id_app, Functor.const_obj_obj, DiagramOfCocones.coconePoints_map,
        Functor.const_obj_map, id_eq, Cocone.precompose_obj_pt, Cocone.whisker_pt,
        Cocone.precompose_obj_ι, Cocone.whisker_ι, NatTrans.comp_app, NatIso.ofComponents_inv_app,
        Iso.refl_inv, whiskerLeft_app, Prod.sectL_obj, Prod.sectL_map, eq_mp_eq_cast,
        eq_mpr_eq_cast, coconeOfCoconeUncurry_pt, coconeOfCoconeUncurry_ι_app, S, E] at h2 ⊢
      simp [← h1, ← h2]
uniq s f hf := P.uniq (s := S s) _
fun j => (Q j).hom_ext fun k => by simpa [S, E] using hf (j, k) }

section

variable (F)
variable [HasLimitsOfShape K C]

set_option backward.defeqAttrib.useBackward true in
/-- Given a functor `F : J ⥤ K ⥤ C`, with all needed limits,
we can construct a diagram consisting of the limit cone over each functor `F.obj j`,
and the universal cone morphisms between these.
-/
@[simps]
/--
Definition of `DiagramOfCones.mkOfHasLimits` / `DiagramOfCones.mkOfHasLimits` 的定义

English:
definition DiagramOfCones.mkOfHasLimits
  signature: : DiagramOfCones F where
  body: limit.cone (F.obj j)
  map f := { hom := lim.map (F.map f) }

中文:
定义 DiagramOfCones.mkOfHasLimits
  签名: : DiagramOfCones F where
  定义体: limit.cone (F.obj j)
  map f := { hom := lim.map (F.map f) }

Depends on / 依赖: F.obj, limit.cone
-/
noncomputable def DiagramOfCones.mkOfHasLimits : DiagramOfCones F where
  obj j := limit.cone (F.obj j)
  map f := { hom := lim.map (F.map f) }

-- Satisfying the inhabited linter.
/--
Instance `diagramOfConesInhabited` / 实例 `diagramOfConesInhabited`

English:
instance diagramOfConesInhabited
  signature: : Inhabited (DiagramOfCones F)
  body: ⟨DiagramOfCones.mkOfHasLimits F⟩

@[simp]

中文:
实例 diagramOfConesInhabited
  签名: : 可居 (DiagramOfCones F)
  定义体: ⟨DiagramOfCones.mkOfHasLimits F⟩

@[simp]

Depends on / 依赖: DiagramOfCones, DiagramOfCones.mkOfHasLimits, mkOfHasLimits
-/
noncomputable instance diagramOfConesInhabited : Inhabited (DiagramOfCones F) :=
  ⟨DiagramOfCones.mkOfHasLimits F⟩

@[simp]
/--
theorem `DiagramOfCones.mkOfHasLimits_conePoints` / 定理 `DiagramOfCones.mkOfHasLimits_conePoints`

English:
theorem DiagramOfCones.mkOfHasLimits_conePoints
  proof: rfl

中文:
定理 DiagramOfCones.mkOfHasLimits_conePoints
  证明: rfl
-/
theorem DiagramOfCones.mkOfHasLimits_conePoints :
    (DiagramOfCones.mkOfHasLimits F).conePoints = F ⋙ lim :=
  rfl

section

variable [HasLimit (curry.obj G ⋙ lim)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `coneOfHasLimitCurryCompLim` / `coneOfHasLimitCurryCompLim` 的定义

English:
definition coneOfHasLimitCurryCompLim
  signature: : Cone G
  body: let Q : DiagramOfCones (curry.obj G) := .mkOfHasLimits _
  { pt := limit (curry.obj G ⋙ lim),
    π :=
    { app x := limit.π (curry.obj G ⋙ lim) x.fst ≫ (Q.obj x.fst).π.app x.snd
      naturality {x y} := fun ⟨f₁, f₂⟩ => by
        have := (Q.obj x.1).w f₂
        dsimp [Q] at this ⊢
        rw [← 

中文:
定义 coneOfHasLimitCurryCompLim
  签名: : 锥 G
  定义体: let Q : DiagramOfCones (curry.obj G) := .mkOfHasLimits _
  { pt := limit (curry.obj G ⋙ lim),
    π :=
    { app x := limit.π (curry.obj G ⋙ lim) x.fst ≫ (Q.obj x.fst).π.app x.snd
      naturality {x y} := fun ⟨f₁, f₂⟩ => by
        have := (Q.obj x.1).w f₂
        dsimp [Q] at this ⊢
        rw [← 

Depends on / 依赖: Category, Category.assoc, Category.id_comp, DiagramOfCones, G.map_comp, Prod.fac, Q.obj, curry.obj, curry_obj_map_app, id_comp, limit.w, map_comp, mkOfHasLimits, naturality, reassoc_of, x.fst, x.snd
-/
noncomputable def coneOfHasLimitCurryCompLim : Cone G :=
  let Q : DiagramOfCones (curry.obj G) := .mkOfHasLimits _
  { pt := limit (curry.obj G ⋙ lim),
    π :=
    { app x := limit.π (curry.obj G ⋙ lim) x.fst ≫ (Q.obj x.fst).π.app x.snd
      naturality {x y} := fun ⟨f₁, f₂⟩ => by
        have := (Q.obj x.1).w f₂
        dsimp [Q] at this ⊢
        rw [← limit.w (F := curry.obj G ⋙ lim) (f := f₁)]
        dsimp
        simp only [Category.assoc, Category.id_comp, Prod.fac (f₁, f₂),
          G.map_comp, limMap_π, curry_obj_map_app, reassoc_of% this] } }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isLimitConeOfHasLimitCurryCompLim` / `isLimitConeOfHasLimitCurryCompLim` 的定义

English:
definition isLimitConeOfHasLimitCurryCompLim
  signature: : IsLimit (coneOfHasLimitCurryCompLim G)
  body: let Q : DiagramOfCones (curry.obj G) := .mkOfHasLimits _
  let Q' : forall j, IsLimit (Q.obj j) := fun j => limit.isLimit _
  { lift c' := limit.lift (F := curry.obj G ⋙ lim) (coneOfConeCurry G Q' c')
    fac c' f := by simp [coneOfHasLimitCurryCompLim, Q, Q']
    uniq c' f h := by
      dsimp [cone

中文:
定义 isLimitConeOfHasLimitCurryCompLim
  签名: : 是极限 (coneOfHasLimitCurryCompLim G)
  定义体: let Q : DiagramOfCones (curry.obj G) := .mkOfHasLimits _
  let Q' : forall j, IsLimit (Q.obj j) := fun j => limit.isLimit _
  { lift c' := limit.lift (F := curry.obj G ⋙ lim) (coneOfConeCurry G Q' c')
    fac c' f := by simp [coneOfHasLimitCurryCompLim, Q, Q']
    uniq c' f h := by
      dsimp [cone

Depends on / 依赖: DiagramOfCones, IsLimit, Q.obj, coneOfConeCurry, coneOfHasLimitCurryCompLim, curry.obj, hom_ext, isLimit, limit.hom_ext, limit.isLimit, limit.lift, mkOfHasLimits
-/
noncomputable def isLimitConeOfHasLimitCurryCompLim : IsLimit (coneOfHasLimitCurryCompLim G) :=
  let Q : DiagramOfCones (curry.obj G) := .mkOfHasLimits _
  let Q' : forall j, IsLimit (Q.obj j) := fun j => limit.isLimit _
  { lift c' := limit.lift (F := curry.obj G ⋙ lim) (coneOfConeCurry G Q' c')
    fac c' f := by simp [coneOfHasLimitCurryCompLim, Q, Q']
    uniq c' f h := by
      dsimp [coneOfHasLimitCurryCompLim] at f h ⊢
      refine limit.hom_ext (F := curry.obj G ⋙ lim) (fun j => limit.hom_ext (fun k => ?_))
      simp [h ⟨j, k⟩, Q'] }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasLimit G
  body: ⟨ { cone := coneOfHasLimitCurryCompLim G
        isLimit := isLimitConeOfHasLimitCurryCompLim G }⟩

中文:
实例 :
  签名: 有极限 G
  定义体: ⟨ { cone := coneOfHasLimitCurryCompLim G
        isLimit := isLimitConeOfHasLimitCurryCompLim G }⟩

Depends on / 依赖: coneOfHasLimitCurryCompLim, isLimit, isLimitConeOfHasLimitCurryCompLim
-/
instance : HasLimit G where
  exists_limit :=
    ⟨ { cone := coneOfHasLimitCurryCompLim G
        isLimit := isLimitConeOfHasLimitCurryCompLim G }⟩

end

variable [HasLimit (uncurry.obj F)] [HasLimit (F ⋙ lim)]

/--
Definition of `limitUncurryIsoLimitCompLim` / `limitUncurryIsoLimitCompLim` 的定义

English:
definition limitUncurryIsoLimitCompLim
  signature: : limit (uncurry.obj F) ≅ limit (F ⋙ lim)
  body: by
  let c := limit.cone (uncurry.obj F)
  let P : IsLimit c := limit.isLimit _
  let G := DiagramOfCones.mkOfHasLimits F
  let Q : forall j, IsLimit (G.obj j) := fun j => limit.isLimit _
  have Q' := coneOfConeUncurryIsLimit Q P
  have Q'' := limit.isLimit (F ⋙ lim)
  exact IsLimit.conePointUniqueU

中文:
定义 limitUncurryIsoLimitCompLim
  签名: : limit (uncurry.obj F) ≅ limit (F ⋙ lim)
  定义体: by
  let c := limit.cone (uncurry.obj F)
  let P : IsLimit c := limit.isLimit _
  let G := DiagramOfCones.mkOfHasLimits F
  let Q : forall j, IsLimit (G.obj j) := fun j => limit.isLimit _
  have Q' := coneOfConeUncurryIsLimit Q P
  have Q'' := limit.isLimit (F ⋙ lim)
  exact IsLimit.conePointUniqueU

Depends on / 依赖: DiagramOfCones, DiagramOfCones.mkOfHasLimits, G.obj, IsLimit, IsLimit.conePointUniqueUpToIso, coneOfConeUncurryIsLimit, conePointUniqueUpToIso, isLimit, limit.cone, limit.isLimit, mkOfHasLimits, uncurry, uncurry.obj
-/
noncomputable def limitUncurryIsoLimitCompLim : limit (uncurry.obj F) ≅ limit (F ⋙ lim) := by
  let c := limit.cone (uncurry.obj F)
  let P : IsLimit c := limit.isLimit _
  let G := DiagramOfCones.mkOfHasLimits F
  let Q : forall j, IsLimit (G.obj j) := fun j => limit.isLimit _
  have Q' := coneOfConeUncurryIsLimit Q P
  have Q'' := limit.isLimit (F ⋙ lim)
  exact IsLimit.conePointUniqueUpToIso Q' Q''

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/--
theorem `limitUncurryIsoLimitCompLim_hom_π_π` / 定理 `limitUncurryIsoLimitCompLim_hom_π_π`

English:
theorem limitUncurryIsoLimitCompLim_hom_π_π
  given: {j} {k}
  proof: by
  dsimp [limitUncurryIsoLimitCompLim, IsLimit.conePointUniqueUpToIso, IsLimit.uniqueUpToIso]
  simp

中文:
定理 limitUncurryIsoLimitCompLim_hom_π_π
  条件: {j} {k}
  证明: by
  dsimp [limitUncurryIsoLimitCompLim, IsLimit.conePointUniqueUpToIso, IsLimit.uniqueUpToIso]
  simp

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, IsLimit.uniqueUpToIso, conePointUniqueUpToIso, limitUncurryIsoLimitCompLim, uniqueUpToIso
-/
theorem limitUncurryIsoLimitCompLim_hom_π_π {j} {k} :
    (limitUncurryIsoLimitCompLim F).hom ≫ limit.π _ j ≫ limit.π _ k = limit.π _ (j, k) := by
  dsimp [limitUncurryIsoLimitCompLim, IsLimit.conePointUniqueUpToIso, IsLimit.uniqueUpToIso]
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/--
theorem `limitUncurryIsoLimitCompLim_inv_π` / 定理 `limitUncurryIsoLimitCompLim_inv_π`

English:
theorem limitUncurryIsoLimitCompLim_inv_π
  given: {j} {k}
  proof: by
  rw [← cancel_epi (limitUncurryIsoLimitCompLim F).hom]
  simp

中文:
定理 limitUncurryIsoLimitCompLim_inv_π
  条件: {j} {k}
  证明: by
  rw [← cancel_epi (limitUncurryIsoLimitCompLim F).hom]
  simp

Depends on / 依赖: cancel_epi, limitUncurryIsoLimitCompLim
-/
theorem limitUncurryIsoLimitCompLim_inv_π {j} {k} :
    (limitUncurryIsoLimitCompLim F).inv ≫ limit.π _ (j, k) =
      (limit.π _ j ≫ limit.π _ k) := by
  rw [← cancel_epi (limitUncurryIsoLimitCompLim F).hom]
  simp

end

section

variable (F)
variable [HasColimitsOfShape K C]

set_option backward.defeqAttrib.useBackward true in
/-- Given a functor `F : J ⥤ K ⥤ C`, with all needed colimits,
we can construct a diagram consisting of the colimit cocone over each functor `F.obj j`,
and the universal cocone morphisms between these.
-/
@[simps]
/--
Definition of `DiagramOfCocones.mkOfHasColimits` / `DiagramOfCocones.mkOfHasColimits` 的定义

English:
definition DiagramOfCocones.mkOfHasColimits
  signature: : DiagramOfCocones F where
  body: colimit.cocone (F.obj j)
  map f := { hom := colim.map (F.map f) }

中文:
定义 DiagramOfCocones.mkOfHasColimits
  签名: : DiagramOfCocones F where
  定义体: colimit.cocone (F.obj j)
  map f := { hom := colim.map (F.map f) }

Depends on / 依赖: F.obj, cocone, colimit, colimit.cocone
-/
noncomputable def DiagramOfCocones.mkOfHasColimits : DiagramOfCocones F where
  obj j := colimit.cocone (F.obj j)
  map f := { hom := colim.map (F.map f) }

-- Satisfying the inhabited linter.
/--
Instance `diagramOfCoconesInhabited` / 实例 `diagramOfCoconesInhabited`

English:
instance diagramOfCoconesInhabited
  signature: : Inhabited (DiagramOfCocones F)
  body: ⟨DiagramOfCocones.mkOfHasColimits F⟩

@[simp]

中文:
实例 diagramOfCoconesInhabited
  签名: : 可居 (DiagramOfCocones F)
  定义体: ⟨DiagramOfCocones.mkOfHasColimits F⟩

@[simp]

Depends on / 依赖: DiagramOfCocones, DiagramOfCocones.mkOfHasColimits, mkOfHasColimits
-/
noncomputable instance diagramOfCoconesInhabited : Inhabited (DiagramOfCocones F) :=
  ⟨DiagramOfCocones.mkOfHasColimits F⟩

@[simp]
/--
theorem `DiagramOfCocones.mkOfHasColimits_coconePoints` / 定理 `DiagramOfCocones.mkOfHasColimits_coconePoints`

English:
theorem DiagramOfCocones.mkOfHasColimits_coconePoints
  proof: rfl

中文:
定理 DiagramOfCocones.mkOfHasColimits_coconePoints
  证明: rfl
-/
theorem DiagramOfCocones.mkOfHasColimits_coconePoints :
    (DiagramOfCocones.mkOfHasColimits F).coconePoints = F ⋙ colim :=
  rfl

section

variable [HasColimit (curry.obj G ⋙ colim)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `coconeOfHasColimitCurryCompColim` / `coconeOfHasColimitCurryCompColim` 的定义

English:
definition coconeOfHasColimitCurryCompColim
  signature: : Cocone G
  body: let Q : DiagramOfCocones (curry.obj G) := .mkOfHasColimits _
  { pt := colimit (curry.obj G ⋙ colim),
    ι :=
    { app x := (Q.obj x.fst).ι.app x.snd ≫ colimit.ι (curry.obj G ⋙ colim) x.fst
      naturality {x y} := fun ⟨f₁, f₂⟩ => by
        have := (Q.obj y.1).w f₂
        dsimp [Q] at this ⊢
  

中文:
定义 coconeOfHasColimitCurryCompColim
  签名: : 余锥 G
  定义体: let Q : DiagramOfCocones (curry.obj G) := .mkOfHasColimits _
  { pt := colimit (curry.obj G ⋙ colim),
    ι :=
    { app x := (Q.obj x.fst).ι.app x.snd ≫ colimit.ι (curry.obj G ⋙ colim) x.fst
      naturality {x y} := fun ⟨f₁, f₂⟩ => by
        have := (Q.obj y.1).w f₂
        dsimp [Q] at this ⊢
  

Depends on / 依赖: Category, Category.assoc, Category.comp_id, DiagramOfCocones, G.map_comp_assoc, Prod.fac, Q.obj, colimit, colimit.w, comp_id, curry.obj, curry_obj_map_app, curry_obj_obj_map, map_comp_assoc, mkOfHasColimits, naturality, x.fst, x.snd
-/
noncomputable def coconeOfHasColimitCurryCompColim : Cocone G :=
  let Q : DiagramOfCocones (curry.obj G) := .mkOfHasColimits _
  { pt := colimit (curry.obj G ⋙ colim),
    ι :=
    { app x := (Q.obj x.fst).ι.app x.snd ≫ colimit.ι (curry.obj G ⋙ colim) x.fst
      naturality {x y} := fun ⟨f₁, f₂⟩ => by
        have := (Q.obj y.1).w f₂
        dsimp [Q] at this ⊢
        rw [← colimit.w (F := curry.obj G ⋙ colim) (f := f₁)]; rw [Category.assoc]; rw [Category.comp_id]; rw [Prod.fac' (f₁]; rw [f₂)]; rw [G.map_comp_assoc]; rw [← curry_obj_map_app]; rw [← curry_obj_obj_map]
        dsimp
        simp [ι_colimMap_assoc, curry_obj_map_app, reassoc_of% this] } }


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimitCoconeOfHasColimitCurryCompColim` / `isColimitCoconeOfHasColimitCurryCompColim` 的定义

English:
definition isColimitCoconeOfHasColimitCurryCompColim
  signature: :
  body: let Q : DiagramOfCocones (curry.obj G) := .mkOfHasColimits _
  let Q' : forall j, IsColimit (Q.obj j) := fun j => colimit.isColimit _
  { desc c' := colimit.desc (F := curry.obj G ⋙ colim) (coconeOfCoconeCurry G Q' c')
    fac c' f := by simp [coconeOfHasColimitCurryCompColim, Q, Q']
    uniq c' f h

中文:
定义 isColimitCoconeOfHasColimitCurryCompColim
  签名: :
  定义体: let Q : DiagramOfCocones (curry.obj G) := .mkOfHasColimits _
  let Q' : forall j, IsColimit (Q.obj j) := fun j => colimit.isColimit _
  { desc c' := colimit.desc (F := curry.obj G ⋙ colim) (coconeOfCoconeCurry G Q' c')
    fac c' f := by simp [coconeOfHasColimitCurryCompColim, Q, Q']
    uniq c' f h

Depends on / 依赖: DiagramOfCocones, IsColimit, Q.obj, coconeOfCoconeCurry, coconeOfHasColimitCurryCompColim, colimit, colimit.desc, colimit.hom_ext, colimit.isColimit, curry.obj, hom_ext, isColimit, mkOfHasColimits
-/
noncomputable def isColimitCoconeOfHasColimitCurryCompColim :
    IsColimit (coconeOfHasColimitCurryCompColim G) :=
  let Q : DiagramOfCocones (curry.obj G) := .mkOfHasColimits _
  let Q' : forall j, IsColimit (Q.obj j) := fun j => colimit.isColimit _
  { desc c' := colimit.desc (F := curry.obj G ⋙ colim) (coconeOfCoconeCurry G Q' c')
    fac c' f := by simp [coconeOfHasColimitCurryCompColim, Q, Q']
    uniq c' f h := by
      dsimp [coconeOfHasColimitCurryCompColim] at f h ⊢
      refine colimit.hom_ext (F := curry.obj G ⋙ colim) (fun j => colimit.hom_ext (fun k => ?_))
      simp [← h ⟨j, k⟩, Q'] }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasColimit G
  body: ⟨ { cocone := coconeOfHasColimitCurryCompColim G
        isColimit := isColimitCoconeOfHasColimitCurryCompColim G }⟩

中文:
实例 :
  签名: 有余极限 G
  定义体: ⟨ { cocone := coconeOfHasColimitCurryCompColim G
        isColimit := isColimitCoconeOfHasColimitCurryCompColim G }⟩

Depends on / 依赖: cocone, coconeOfHasColimitCurryCompColim, isColimit, isColimitCoconeOfHasColimitCurryCompColim
-/
instance : HasColimit G where
  exists_colimit :=
    ⟨ { cocone := coconeOfHasColimitCurryCompColim G
        isColimit := isColimitCoconeOfHasColimitCurryCompColim G }⟩

end

variable [HasColimit (uncurry.obj F)] [HasColimit (F ⋙ colim)]

/--
Definition of `colimitUncurryIsoColimitCompColim` / `colimitUncurryIsoColimitCompColim` 的定义

English:
definition colimitUncurryIsoColimitCompColim
  signature: :
  body: by
  let c := colimit.cocone (uncurry.obj F)
  let P : IsColimit c := colimit.isColimit _
  let G := DiagramOfCocones.mkOfHasColimits F
  let Q : forall j, IsColimit (G.obj j) := fun j => colimit.isColimit _
  have Q' := coconeOfCoconeUncurryIsColimit Q P
  have Q'' := colimit.isColimit (F ⋙ colim)


中文:
定义 colimitUncurryIsoColimitCompColim
  签名: :
  定义体: by
  let c := colimit.cocone (uncurry.obj F)
  let P : IsColimit c := colimit.isColimit _
  let G := DiagramOfCocones.mkOfHasColimits F
  let Q : forall j, IsColimit (G.obj j) := fun j => colimit.isColimit _
  have Q' := coconeOfCoconeUncurryIsColimit Q P
  have Q'' := colimit.isColimit (F ⋙ colim)


Depends on / 依赖: DiagramOfCocones, DiagramOfCocones.mkOfHasColimits, G.obj, IsColimit, IsColimit.coconePointUniqueUpToIso, cocone, coconeOfCoconeUncurryIsColimit, coconePointUniqueUpToIso, colimit, colimit.cocone, colimit.isColimit, isColimit, mkOfHasColimits, uncurry, uncurry.obj
-/
noncomputable def colimitUncurryIsoColimitCompColim :
    colimit (uncurry.obj F) ≅ colimit (F ⋙ colim) := by
  let c := colimit.cocone (uncurry.obj F)
  let P : IsColimit c := colimit.isColimit _
  let G := DiagramOfCocones.mkOfHasColimits F
  let Q : forall j, IsColimit (G.obj j) := fun j => colimit.isColimit _
  have Q' := coconeOfCoconeUncurryIsColimit Q P
  have Q'' := colimit.isColimit (F ⋙ colim)
  exact IsColimit.coconePointUniqueUpToIso Q' Q''

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/--
theorem `colimitUncurryIsoColimitCompColim_ι_ι_inv` / 定理 `colimitUncurryIsoColimitCompColim_ι_ι_inv`

English:
theorem colimitUncurryIsoColimitCompColim_ι_ι_inv
  given: {j} {k}
  proof: by
  dsimp [colimitUncurryIsoColimitCompColim, IsColimit.coconePointUniqueUpToIso,
    IsColimit.uniqueUpToIso]
  simp

中文:
定理 colimitUncurryIsoColimitCompColim_ι_ι_inv
  条件: {j} {k}
  证明: by
  dsimp [colimitUncurryIsoColimitCompColim, IsColimit.coconePointUniqueUpToIso,
    IsColimit.uniqueUpToIso]
  simp

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, IsColimit.uniqueUpToIso, coconePointUniqueUpToIso, colimitUncurryIsoColimitCompColim, uniqueUpToIso
-/
theorem colimitUncurryIsoColimitCompColim_ι_ι_inv {j} {k} :
    colimit.ι (F.obj j) k ≫ colimit.ι (F ⋙ colim) j ≫ (colimitUncurryIsoColimitCompColim F).inv =
      colimit.ι (uncurry.obj F) (j, k) := by
  dsimp [colimitUncurryIsoColimitCompColim, IsColimit.coconePointUniqueUpToIso,
    IsColimit.uniqueUpToIso]
  simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp, reassoc]
/--
theorem `colimitUncurryIsoColimitCompColim_ι_hom` / 定理 `colimitUncurryIsoColimitCompColim_ι_hom`

English:
theorem colimitUncurryIsoColimitCompColim_ι_hom
  given: {j} {k}
  proof: by
  rw [← cancel_mono (colimitUncurryIsoColimitCompColim F).inv]
  simp

中文:
定理 colimitUncurryIsoColimitCompColim_ι_hom
  条件: {j} {k}
  证明: by
  rw [← cancel_mono (colimitUncurryIsoColimitCompColim F).inv]
  simp

Depends on / 依赖: Quot.lift, RightFraction, RightFraction.mk, a.comp, a.hs, cancel_mono, colimitUncurryIsoColimitCompColim, exists_leftFraction
-/
theorem colimitUncurryIsoColimitCompColim_ι_hom {j} {k} :
    colimit.ι _ (j, k) ≫ (colimitUncurryIsoColimitCompColim F).hom =
      (colimit.ι _ k ≫ colimit.ι (F ⋙ colim) j : _ ⟶ (colimit (F ⋙ colim))) := by
  rw [← cancel_mono (colimitUncurryIsoColimitCompColim F).inv]
  simp

end

section

variable (F) [HasLimitsOfShape J C] [HasLimitsOfShape K C]

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `limitFlipCompLimIsoLimitCompLim` / `limitFlipCompLimIsoLimitCompLim` 的定义

English:
definition limitFlipCompLimIsoLimitCompLim
  signature: : limit (F.flip ⋙ lim) ≅ limit (F ⋙ lim)
  body: (limitUncurryIsoLimitCompLim _).symm ≪≫
    HasLimit.isoOfNatIso (uncurryObjFlip _) ≪≫
      HasLimit.isoOfEquivalence (Prod.braiding _ _)
          (NatIso.ofComponents fun _ => by rfl) ≪≫
        limitUncurryIsoLimitCompLim _

中文:
定义 limitFlipCompLimIsoLimitCompLim
  签名: : limit (F.flip ⋙ lim) ≅ limit (F ⋙ lim)
  定义体: (limitUncurryIsoLimitCompLim _).symm ≪≫
    HasLimit.isoOfNatIso (uncurryObjFlip _) ≪≫
      HasLimit.isoOfEquivalence (Prod.braiding _ _)
          (NatIso.ofComponents fun _ => by rfl) ≪≫
        limitUncurryIsoLimitCompLim _

Depends on / 依赖: HasLimit, HasLimit.isoOfEquivalence, HasLimit.isoOfNatIso, NatIso, NatIso.ofComponents, Prod.braiding, braiding, isoOfEquivalence, isoOfNatIso, limitUncurryIsoLimitCompLim, ofComponents, uncurryObjFlip
-/
noncomputable def limitFlipCompLimIsoLimitCompLim : limit (F.flip ⋙ lim) ≅ limit (F ⋙ lim) :=
  (limitUncurryIsoLimitCompLim _).symm ≪≫
    HasLimit.isoOfNatIso (uncurryObjFlip _) ≪≫
      HasLimit.isoOfEquivalence (Prod.braiding _ _)
          (NatIso.ofComponents fun _ => by rfl) ≪≫
        limitUncurryIsoLimitCompLim _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/--
theorem `limitFlipCompLimIsoLimitCompLim_hom_π_π` / 定理 `limitFlipCompLimIsoLimitCompLim_hom_π_π`

English:
theorem limitFlipCompLimIsoLimitCompLim_hom_π_π
  given: (j) (k)
  proof: by
  dsimp [limitFlipCompLimIsoLimitCompLim]
  simp [Equivalence.counit]

中文:
定理 limitFlipCompLimIsoLimitCompLim_hom_π_π
  条件: (j) (k)
  证明: by
  dsimp [limitFlipCompLimIsoLimitCompLim]
  simp [Equivalence.counit]

Depends on / 依赖: Equivalence, Equivalence.counit, counit, limitFlipCompLimIsoLimitCompLim
-/
theorem limitFlipCompLimIsoLimitCompLim_hom_π_π (j) (k) :
    (limitFlipCompLimIsoLimitCompLim F).hom ≫ limit.π _ j ≫ limit.π _ k =
      (limit.π _ k ≫ limit.π _ j) := by
  dsimp [limitFlipCompLimIsoLimitCompLim]
  simp [Equivalence.counit]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/--
theorem `limitFlipCompLimIsoLimitCompLim_inv_π_π` / 定理 `limitFlipCompLimIsoLimitCompLim_inv_π_π`

English:
theorem limitFlipCompLimIsoLimitCompLim_inv_π_π
  given: (k) (j)
  proof: by
  simp [limitFlipCompLimIsoLimitCompLim]

中文:
定理 limitFlipCompLimIsoLimitCompLim_inv_π_π
  条件: (k) (j)
  证明: by
  simp [limitFlipCompLimIsoLimitCompLim]

Depends on / 依赖: limitFlipCompLimIsoLimitCompLim
-/
theorem limitFlipCompLimIsoLimitCompLim_inv_π_π (k) (j) :
    (limitFlipCompLimIsoLimitCompLim F).inv ≫ limit.π _ k ≫ limit.π _ j =
      (limit.π _ j ≫ limit.π _ k) := by
  simp [limitFlipCompLimIsoLimitCompLim]

end

section

variable (F) [HasColimitsOfShape J C] [HasColimitsOfShape K C]

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `colimitFlipCompColimIsoColimitCompColim` / `colimitFlipCompColimIsoColimitCompColim` 的定义

English:
definition colimitFlipCompColimIsoColimitCompColim
  signature: :
  body: (colimitUncurryIsoColimitCompColim _).symm ≪≫
    HasColimit.isoOfNatIso (uncurryObjFlip _) ≪≫
      HasColimit.isoOfEquivalence (Prod.braiding _ _)
          (NatIso.ofComponents fun _ => by rfl) ≪≫
        colimitUncurryIsoColimitCompColim _

中文:
定义 colimitFlipCompColimIsoColimitCompColim
  签名: :
  定义体: (colimitUncurryIsoColimitCompColim _).symm ≪≫
    HasColimit.isoOfNatIso (uncurryObjFlip _) ≪≫
      HasColimit.isoOfEquivalence (Prod.braiding _ _)
          (NatIso.ofComponents fun _ => by rfl) ≪≫
        colimitUncurryIsoColimitCompColim _

Depends on / 依赖: HasColimit, HasColimit.isoOfEquivalence, HasColimit.isoOfNatIso, NatIso, NatIso.ofComponents, Prod.braiding, braiding, colimitUncurryIsoColimitCompColim, isoOfEquivalence, isoOfNatIso, ofComponents, uncurryObjFlip
-/
noncomputable def colimitFlipCompColimIsoColimitCompColim :
    colimit (F.flip ⋙ colim) ≅ colimit (F ⋙ colim) :=
  (colimitUncurryIsoColimitCompColim _).symm ≪≫
    HasColimit.isoOfNatIso (uncurryObjFlip _) ≪≫
      HasColimit.isoOfEquivalence (Prod.braiding _ _)
          (NatIso.ofComponents fun _ => by rfl) ≪≫
        colimitUncurryIsoColimitCompColim _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/--
theorem `colimitFlipCompColimIsoColimitCompColim_ι_ι_hom` / 定理 `colimitFlipCompColimIsoColimitCompColim_ι_ι_hom`

English:
theorem colimitFlipCompColimIsoColimitCompColim_ι_ι_hom
  given: (j) (k)
  proof: by
  dsimp [colimitFlipCompColimIsoColimitCompColim]
  conv_lhs => slice 1 3
  simp [Equivalence.unit]

中文:
定理 colimitFlipCompColimIsoColimitCompColim_ι_ι_hom
  条件: (j) (k)
  证明: by
  dsimp [colimitFlipCompColimIsoColimitCompColim]
  conv_lhs => slice 1 3
  simp [Equivalence.unit]

Depends on / 依赖: Equivalence, Equivalence.unit, colimitFlipCompColimIsoColimitCompColim, conv_lhs
-/
theorem colimitFlipCompColimIsoColimitCompColim_ι_ι_hom (j) (k) :
    colimit.ι (F.flip.obj k) j ≫ colimit.ι (F.flip ⋙ colim) k ≫
      (colimitFlipCompColimIsoColimitCompColim F).hom =
        (colimit.ι _ k ≫ colimit.ι (F ⋙ colim) j : _ ⟶ colimit (F ⋙ colim)) := by
  dsimp [colimitFlipCompColimIsoColimitCompColim]
  conv_lhs => slice 1 3
  simp [Equivalence.unit]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/--
theorem `colimitFlipCompColimIsoColimitCompColim_ι_ι_inv` / 定理 `colimitFlipCompColimIsoColimitCompColim_ι_ι_inv`

English:
theorem colimitFlipCompColimIsoColimitCompColim_ι_ι_inv
  given: (k) (j)
  proof: by
  dsimp [colimitFlipCompColimIsoColimitCompColim]
  conv_lhs => slice 1 3
  simp [Equivalence.counitInv]

中文:
定理 colimitFlipCompColimIsoColimitCompColim_ι_ι_inv
  条件: (k) (j)
  证明: by
  dsimp [colimitFlipCompColimIsoColimitCompColim]
  conv_lhs => slice 1 3
  simp [Equivalence.counitInv]

Depends on / 依赖: Equivalence, Equivalence.counitInv, colimitFlipCompColimIsoColimitCompColim, conv_lhs, counitInv
-/
theorem colimitFlipCompColimIsoColimitCompColim_ι_ι_inv (k) (j) :
    colimit.ι (F.obj j) k ≫ colimit.ι (F ⋙ colim) j ≫
      (colimitFlipCompColimIsoColimitCompColim F).inv =
        (colimit.ι _ j ≫ colimit.ι (F.flip ⋙ colim) k : _ ⟶ colimit (F.flip ⋙ colim)) := by
  dsimp [colimitFlipCompColimIsoColimitCompColim]
  conv_lhs => slice 1 3
  simp [Equivalence.counitInv]

end

section

variable [HasLimitsOfShape K C] [HasLimit (curry.obj G ⋙ lim)]

/--
Definition of `limitIsoLimitCurryCompLim` / `limitIsoLimitCurryCompLim` 的定义

English:
definition limitIsoLimitCurryCompLim
  signature: : limit G ≅ limit (curry.obj G ⋙ lim)
  body: by
  have i : G ≅ uncurry.obj ((@curry J _ K _ C _).obj G) := currying.symm.unitIso.app G
  haveI : Limits.HasLimit (uncurry.obj ((@curry J _ K _ C _).obj G)) := hasLimit_of_iso i
  trans limit (uncurry.obj ((@curry J _ K _ C _).obj G))
  · apply HasLimit.isoOfNatIso i
  · exact limitUncurryIsoLimit

中文:
定义 limitIsoLimitCurryCompLim
  签名: : limit G ≅ limit (curry.obj G ⋙ lim)
  定义体: by
  have i : G ≅ uncurry.obj ((@curry J _ K _ C _).obj G) := currying.symm.unitIso.app G
  haveI : Limits.HasLimit (uncurry.obj ((@curry J _ K _ C _).obj G)) := hasLimit_of_iso i
  trans limit (uncurry.obj ((@curry J _ K _ C _).obj G))
  · apply HasLimit.isoOfNatIso i
  · exact limitUncurryIsoLimit

Depends on / 依赖: HasLimit, HasLimit.isoOfNatIso, Limits, Limits.HasLimit, currying, currying.symm.unitIso.app, hasLimit_of_iso, isoOfNatIso, limitUncurryIsoLimitCompLim, uncurry, uncurry.obj, unitIso
-/
noncomputable def limitIsoLimitCurryCompLim : limit G ≅ limit (curry.obj G ⋙ lim) := by
  have i : G ≅ uncurry.obj ((@curry J _ K _ C _).obj G) := currying.symm.unitIso.app G
  haveI : Limits.HasLimit (uncurry.obj ((@curry J _ K _ C _).obj G)) := hasLimit_of_iso i
  trans limit (uncurry.obj ((@curry J _ K _ C _).obj G))
  · apply HasLimit.isoOfNatIso i
  · exact limitUncurryIsoLimitCompLim ((@curry J _ K _ C _).obj G)

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/--
theorem `limitIsoLimitCurryCompLim_hom_π_π` / 定理 `limitIsoLimitCurryCompLim_hom_π_π`

English:
theorem limitIsoLimitCurryCompLim_hom_π_π
  given: {j} {k}
  proof: by
  simp [limitIsoLimitCurryCompLim, Trans.simple]

中文:
定理 limitIsoLimitCurryCompLim_hom_π_π
  条件: {j} {k}
  证明: by
  simp [limitIsoLimitCurryCompLim, Trans.simple]

Depends on / 依赖: Trans.simple, limitIsoLimitCurryCompLim, simple
-/
theorem limitIsoLimitCurryCompLim_hom_π_π {j} {k} :
    (limitIsoLimitCurryCompLim G).hom ≫ limit.π _ j ≫ limit.π _ k = limit.π _ (j, k) := by
  simp [limitIsoLimitCurryCompLim, Trans.simple]

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/--
theorem `limitIsoLimitCurryCompLim_inv_π` / 定理 `limitIsoLimitCurryCompLim_inv_π`

English:
theorem limitIsoLimitCurryCompLim_inv_π
  given: {j} {k}
  proof: by
  rw [← cancel_epi (limitIsoLimitCurryCompLim G).hom]
  simp

中文:
定理 limitIsoLimitCurryCompLim_inv_π
  条件: {j} {k}
  证明: by
  rw [← cancel_epi (limitIsoLimitCurryCompLim G).hom]
  simp

Depends on / 依赖: cancel_epi, limitIsoLimitCurryCompLim
-/
theorem limitIsoLimitCurryCompLim_inv_π {j} {k} :
    (limitIsoLimitCurryCompLim G).inv ≫ limit.π _ (j, k) =
      (limit.π _ j ≫ limit.π _ k) := by
  rw [← cancel_epi (limitIsoLimitCurryCompLim G).hom]
  simp

end

section

variable [HasColimitsOfShape K C] [HasColimit (curry.obj G ⋙ colim)]

/--
Definition of `colimitIsoColimitCurryCompColim` / `colimitIsoColimitCurryCompColim` 的定义

English:
definition colimitIsoColimitCurryCompColim
  signature: : colimit G ≅ colimit (curry.obj G ⋙ colim)
  body: by
  have i : G ≅ uncurry.obj ((@curry J _ K _ C _).obj G) := currying.symm.unitIso.app G
  haveI : Limits.HasColimit (uncurry.obj ((@curry J _ K _ C _).obj G)) := hasColimit_of_iso i.symm
  trans colimit (uncurry.obj ((@curry J _ K _ C _).obj G))
  · apply HasColimit.isoOfNatIso i
  · exact colimit

中文:
定义 colimitIsoColimitCurryCompColim
  签名: : colimit G ≅ colimit (curry.obj G ⋙ colim)
  定义体: by
  have i : G ≅ uncurry.obj ((@curry J _ K _ C _).obj G) := currying.symm.unitIso.app G
  haveI : Limits.HasColimit (uncurry.obj ((@curry J _ K _ C _).obj G)) := hasColimit_of_iso i.symm
  trans colimit (uncurry.obj ((@curry J _ K _ C _).obj G))
  · apply HasColimit.isoOfNatIso i
  · exact colimit

Depends on / 依赖: HasColimit, HasColimit.isoOfNatIso, Limits, Limits.HasColimit, colimit, colimitUncurryIsoColimitCompColim, currying, currying.symm.unitIso.app, hasColimit_of_iso, i.symm, isoOfNatIso, uncurry, uncurry.obj, unitIso
-/
noncomputable def colimitIsoColimitCurryCompColim : colimit G ≅ colimit (curry.obj G ⋙ colim) := by
  have i : G ≅ uncurry.obj ((@curry J _ K _ C _).obj G) := currying.symm.unitIso.app G
  haveI : Limits.HasColimit (uncurry.obj ((@curry J _ K _ C _).obj G)) := hasColimit_of_iso i.symm
  trans colimit (uncurry.obj ((@curry J _ K _ C _).obj G))
  · apply HasColimit.isoOfNatIso i
  · exact colimitUncurryIsoColimitCompColim ((@curry J _ K _ C _).obj G)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/--
theorem `colimitIsoColimitCurryCompColim_ι_ι_inv` / 定理 `colimitIsoColimitCurryCompColim_ι_ι_inv`

English:
theorem colimitIsoColimitCurryCompColim_ι_ι_inv
  given: {j} {k}
  proof: by
  simp [colimitIsoColimitCurryCompColim, Trans.simple, colimitUncurryIsoColimitCompColim]

中文:
定理 colimitIsoColimitCurryCompColim_ι_ι_inv
  条件: {j} {k}
  证明: by
  simp [colimitIsoColimitCurryCompColim, Trans.simple, colimitUncurryIsoColimitCompColim]

Depends on / 依赖: Trans.simple, colimitIsoColimitCurryCompColim, colimitUncurryIsoColimitCompColim, simple
-/
theorem colimitIsoColimitCurryCompColim_ι_ι_inv {j} {k} :
    colimit.ι ((curry.obj G).obj j) k ≫ colimit.ι (curry.obj G ⋙ colim) j ≫
      (colimitIsoColimitCurryCompColim G).inv = colimit.ι _ (j, k) := by
  simp [colimitIsoColimitCurryCompColim, Trans.simple, colimitUncurryIsoColimitCompColim]

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/--
theorem `colimitIsoColimitCurryCompColim_ι_hom` / 定理 `colimitIsoColimitCurryCompColim_ι_hom`

English:
theorem colimitIsoColimitCurryCompColim_ι_hom
  given: {j} {k}
  proof: by
  rw [← cancel_mono (colimitIsoColimitCurryCompColim G).inv]
  simp

中文:
定理 colimitIsoColimitCurryCompColim_ι_hom
  条件: {j} {k}
  证明: by
  rw [← cancel_mono (colimitIsoColimitCurryCompColim G).inv]
  simp

Depends on / 依赖: cancel_mono, colimitIsoColimitCurryCompColim
-/
theorem colimitIsoColimitCurryCompColim_ι_hom {j} {k} :
    colimit.ι _ (j, k) ≫ (colimitIsoColimitCurryCompColim G).hom =
      (colimit.ι (_) k ≫ colimit.ι (curry.obj G ⋙ colim) j : _ ⟶ colimit (_ ⋙ colim)) := by
  rw [← cancel_mono (colimitIsoColimitCurryCompColim G).inv]
  simp

end

section

variable [HasLimitsOfShape K C] [HasLimitsOfShape J C] [HasLimit (curry.obj G ⋙ lim)]

open CategoryTheory.prod

/--
Definition of `limitCurrySwapCompLimIsoLimitCurryCompLim` / `limitCurrySwapCompLimIsoLimitCurryCompLim` 的定义

English:
definition limitCurrySwapCompLimIsoLimitCurryCompLim
  signature: :
  body: calc
    limit (curry.obj (Prod.swap K J ⋙ G) ⋙ lim) ≅ limit (Prod.swap K J ⋙ G) :=
      (limitIsoLimitCurryCompLim _).symm
    _ ≅ limit G := HasLimit.isoOfEquivalence (Prod.braiding K J) (Iso.refl _)
    _ ≅ limit (curry.obj G ⋙ lim) := limitIsoLimitCurryCompLim _

中文:
定义 limitCurrySwapCompLimIsoLimitCurryCompLim
  签名: :
  定义体: calc
    limit (curry.obj (Prod.swap K J ⋙ G) ⋙ lim) ≅ limit (Prod.swap K J ⋙ G) :=
      (limitIsoLimitCurryCompLim _).symm
    _ ≅ limit G := HasLimit.isoOfEquivalence (Prod.braiding K J) (Iso.refl _)
    _ ≅ limit (curry.obj G ⋙ lim) := limitIsoLimitCurryCompLim _

Depends on / 依赖: HasLimit, HasLimit.isoOfEquivalence, Iso.refl, Prod.braiding, Prod.swap, braiding, curry.obj, isoOfEquivalence, limitIsoLimitCurryCompLim
-/
noncomputable def limitCurrySwapCompLimIsoLimitCurryCompLim :
    limit (curry.obj (Prod.swap K J ⋙ G) ⋙ lim) ≅ limit (curry.obj G ⋙ lim) :=
  calc
    limit (curry.obj (Prod.swap K J ⋙ G) ⋙ lim) ≅ limit (Prod.swap K J ⋙ G) :=
      (limitIsoLimitCurryCompLim _).symm
    _ ≅ limit G := HasLimit.isoOfEquivalence (Prod.braiding K J) (Iso.refl _)
    _ ≅ limit (curry.obj G ⋙ lim) := limitIsoLimitCurryCompLim _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `limitCurrySwapCompLimIsoLimitCurryCompLim_hom_π_π` / 定理 `limitCurrySwapCompLimIsoLimitCurryCompLim_hom_π_π`

English:
theorem limitCurrySwapCompLimIsoLimitCurryCompLim_hom_π_π
  given: {j} {k}
  proof: by
  dsimp [limitCurrySwapCompLimIsoLimitCurryCompLim, Equivalence.counit]
  rw [Category.assoc]; rw [Category.assoc]; rw [limitIsoLimitCurryCompLim_hom_π_π]; rw [HasLimit.isoOfEquivalence_hom_π]
  dsimp [Equivalence.counit]
  rw [← prod_id]; rw [G.map_id]
  simp

中文:
定理 limitCurrySwapCompLimIsoLimitCurryCompLim_hom_π_π
  条件: {j} {k}
  证明: by
  dsimp [limitCurrySwapCompLimIsoLimitCurryCompLim, Equivalence.counit]
  rw [Category.assoc]; rw [Category.assoc]; rw [limitIsoLimitCurryCompLim_hom_π_π]; rw [HasLimit.isoOfEquivalence_hom_π]
  dsimp [Equivalence.counit]
  rw [← prod_id]; rw [G.map_id]
  simp

Depends on / 依赖: Category, Category.assoc, Equivalence, Equivalence.counit, G.map_id, HasLimit, HasLimit.isoOfEquivalence_hom_, counit, limitCurrySwapCompLimIsoLimitCurryCompLim, map_id, prod_id
-/
theorem limitCurrySwapCompLimIsoLimitCurryCompLim_hom_π_π {j} {k} :
    (limitCurrySwapCompLimIsoLimitCurryCompLim G).hom ≫ limit.π _ j ≫ limit.π _ k =
      (limit.π _ k ≫ limit.π _ j) := by
  dsimp [limitCurrySwapCompLimIsoLimitCurryCompLim, Equivalence.counit]
  rw [Category.assoc]; rw [Category.assoc]; rw [limitIsoLimitCurryCompLim_hom_π_π]; rw [HasLimit.isoOfEquivalence_hom_π]
  dsimp [Equivalence.counit]
  rw [← prod_id]; rw [G.map_id]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `limitCurrySwapCompLimIsoLimitCurryCompLim_inv_π_π` / 定理 `limitCurrySwapCompLimIsoLimitCurryCompLim_inv_π_π`

English:
theorem limitCurrySwapCompLimIsoLimitCurryCompLim_inv_π_π
  given: {j} {k}
  proof: by
  simp [limitCurrySwapCompLimIsoLimitCurryCompLim]

中文:
定理 limitCurrySwapCompLimIsoLimitCurryCompLim_inv_π_π
  条件: {j} {k}
  证明: by
  simp [limitCurrySwapCompLimIsoLimitCurryCompLim]

Depends on / 依赖: limitCurrySwapCompLimIsoLimitCurryCompLim
-/
theorem limitCurrySwapCompLimIsoLimitCurryCompLim_inv_π_π {j} {k} :
    (limitCurrySwapCompLimIsoLimitCurryCompLim G).inv ≫ limit.π _ k ≫ limit.π _ j =
      (limit.π _ j ≫ limit.π _ k) := by
  simp [limitCurrySwapCompLimIsoLimitCurryCompLim]

end

section

variable [HasColimitsOfShape K C] [HasColimitsOfShape J C] [HasColimit (curry.obj G ⋙ colim)]

open CategoryTheory.prod

/--
Definition of `colimitCurrySwapCompColimIsoColimitCurryCompColim` / `colimitCurrySwapCompColimIsoColimitCurryCompColim` 的定义

English:
definition colimitCurrySwapCompColimIsoColimitCurryCompColim
  signature: :
  body: calc
    colimit (curry.obj (Prod.swap K J ⋙ G) ⋙ colim) ≅ colimit (Prod.swap K J ⋙ G) :=
      (colimitIsoColimitCurryCompColim _).symm
    _ ≅ colimit G := HasColimit.isoOfEquivalence (Prod.braiding K J) (Iso.refl _)
    _ ≅ colimit (curry.obj G ⋙ colim) := colimitIsoColimitCurryCompColim _

中文:
定义 colimitCurrySwapCompColimIsoColimitCurryCompColim
  签名: :
  定义体: calc
    colimit (curry.obj (Prod.swap K J ⋙ G) ⋙ colim) ≅ colimit (Prod.swap K J ⋙ G) :=
      (colimitIsoColimitCurryCompColim _).symm
    _ ≅ colimit G := HasColimit.isoOfEquivalence (Prod.braiding K J) (Iso.refl _)
    _ ≅ colimit (curry.obj G ⋙ colim) := colimitIsoColimitCurryCompColim _

Depends on / 依赖: HasColimit, HasColimit.isoOfEquivalence, Iso.refl, Prod.braiding, Prod.swap, braiding, colimit, colimitIsoColimitCurryCompColim, curry.obj, isoOfEquivalence
-/
noncomputable def colimitCurrySwapCompColimIsoColimitCurryCompColim :
    colimit (curry.obj (Prod.swap K J ⋙ G) ⋙ colim) ≅ colimit (curry.obj G ⋙ colim) :=
  calc
    colimit (curry.obj (Prod.swap K J ⋙ G) ⋙ colim) ≅ colimit (Prod.swap K J ⋙ G) :=
      (colimitIsoColimitCurryCompColim _).symm
    _ ≅ colimit G := HasColimit.isoOfEquivalence (Prod.braiding K J) (Iso.refl _)
    _ ≅ colimit (curry.obj G ⋙ colim) := colimitIsoColimitCurryCompColim _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `colimitCurrySwapCompColimIsoColimitCurryCompColim_ι_ι_hom` / 定理 `colimitCurrySwapCompColimIsoColimitCurryCompColim_ι_ι_hom`

English:
theorem colimitCurrySwapCompColimIsoColimitCurryCompColim_ι_ι_hom
  given: {j} {k}
  proof: by
  dsimp [colimitCurrySwapCompColimIsoColimitCurryCompColim]
  conv_lhs => slice 1 3
  simp

中文:
定理 colimitCurrySwapCompColimIsoColimitCurryCompColim_ι_ι_hom
  条件: {j} {k}
  证明: by
  dsimp [colimitCurrySwapCompColimIsoColimitCurryCompColim]
  conv_lhs => slice 1 3
  simp

Depends on / 依赖: colimitCurrySwapCompColimIsoColimitCurryCompColim, conv_lhs
-/
theorem colimitCurrySwapCompColimIsoColimitCurryCompColim_ι_ι_hom {j} {k} :
    colimit.ι _ j ≫ colimit.ι (curry.obj (Prod.swap K J ⋙ G) ⋙ colim) k ≫
      (colimitCurrySwapCompColimIsoColimitCurryCompColim G).hom =
        (colimit.ι _ k ≫ colimit.ι (curry.obj G ⋙ colim) j :
          _ ⟶ colimit (curry.obj G ⋙ colim)) := by
  dsimp [colimitCurrySwapCompColimIsoColimitCurryCompColim]
  conv_lhs => slice 1 3
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `colimitCurrySwapCompColimIsoColimitCurryCompColim_ι_ι_inv` / 定理 `colimitCurrySwapCompColimIsoColimitCurryCompColim_ι_ι_inv`

English:
theorem colimitCurrySwapCompColimIsoColimitCurryCompColim_ι_ι_inv
  given: {j} {k}
  proof: by
  dsimp [colimitCurrySwapCompColimIsoColimitCurryCompColim]
  conv_lhs => slice 1 3
  rw [colimitIsoColimitCurryCompColim_ι_ι_inv]; rw [HasColimit.ι_isoOfEquivalence_inv]
  dsimp [Equivalence.counitInv]
  rw [CategoryTheory.Bifunctor.map_id]
  simp

中文:
定理 colimitCurrySwapCompColimIsoColimitCurryCompColim_ι_ι_inv
  条件: {j} {k}
  证明: by
  dsimp [colimitCurrySwapCompColimIsoColimitCurryCompColim]
  conv_lhs => slice 1 3
  rw [colimitIsoColimitCurryCompColim_ι_ι_inv]; rw [HasColimit.ι_isoOfEquivalence_inv]
  dsimp [Equivalence.counitInv]
  rw [CategoryTheory.Bifunctor.map_id]
  simp

Depends on / 依赖: Bifunctor, CategoryTheory, CategoryTheory.Bifunctor.map_id, Equivalence, Equivalence.counitInv, HasColimit, colimitCurrySwapCompColimIsoColimitCurryCompColim, conv_lhs, counitInv, map_id
-/
theorem colimitCurrySwapCompColimIsoColimitCurryCompColim_ι_ι_inv {j} {k} :
    colimit.ι _ k ≫ colimit.ι (curry.obj G ⋙ colim) j ≫
      (colimitCurrySwapCompColimIsoColimitCurryCompColim G).inv =
        (colimit.ι _ j ≫
          colimit.ι (curry.obj _ ⋙ colim) k :
            _ ⟶ colimit (curry.obj (Prod.swap K J ⋙ G) ⋙ colim)) := by
  dsimp [colimitCurrySwapCompColimIsoColimitCurryCompColim]
  conv_lhs => slice 1 3
  rw [colimitIsoColimitCurryCompColim_ι_ι_inv]; rw [HasColimit.ι_isoOfEquivalence_inv]
  dsimp [Equivalence.counitInv]
  rw [CategoryTheory.Bifunctor.map_id]
  simp

end

end CategoryTheory.Limits
