/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Products.Basic

/-!
# Joins of categories

Given categories `C, D`, this file constructs a category `C ⋆ D`. Its objects are either
objects of `C` or objects of `D`, morphisms between objects of `C` are morphisms in `C`,
morphisms between objects of `D` are morphisms in `D`, and finally, given `c : C` and `d : D`,
there is a unique morphism `c ⟶ d` in `C ⋆ D`.

## Main constructions

* `Join.edge c d`: the unique map from `c` to `d`.
* `Join.inclLeft : C ⥤ C ⋆ D`, the left inclusion. Its action on morphisms is the main entry point
  to construct maps in `C ⋆ D` between objects coming from `C`.
* `Join.inclRight : D ⥤ C ⋆ D`, the right inclusion. Its action on morphisms is the main entry point
  to construct maps in `C ⋆ D` between objects coming from `D`.
* `Join.mkFunctor`, A constructor for functors out of a join of categories.
* `Join.mkNatTrans`, A constructor for natural transformations between functors out of a join
  of categories.
* `Join.mkNatIso`, A constructor for natural isomorphisms between functors out of a join
  of categories.

## References

* [Kerodon: section 1.4.3.2](https://kerodon.net/tag/0160)

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

namespace CategoryTheory

open CategoryTheory.Functor

-- Impl. : We are not defining it as a type alias for `C ⊕ D` so that we can have
-- aesop to call cases on `Join C D`
/--
Inductive type `Join` / 归纳类型 `Join`

English:
inductive Join
  parameters: (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]
  constructors (2):
    - left: C -> Join C D
    - right: D -> Join C D

中文:
归纳类型 Join
  参数: (C : 类型u₁) [Category.{v₁} C] (D : 类型u₂) [Category.{v₂} D]
  构造子 (2 个):
    - left: C -> Join C D
    - right: D -> Join C D

Depends on / 依赖: CategoryTheory
-/
inductive Join (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D] : Type (max u₁ u₂)
  | left : C -> Join C D
  | right : D -> Join C D

attribute [aesop safe cases (rule_sets := [CategoryTheory])] Join

namespace Join

@[inherit_doc] scoped infixr:30 " ⋆ " => Join

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

section CategoryStructure

variable {C D}

/--
Definition of `Hom` / `Hom` 的定义

English:
definition Hom
  signature: : C ⋆ D -> C ⋆ D -> Type (max v₁ v₂)

中文:
定义 Hom
  签名: : C ⋆ D -> C ⋆ D -> Type (max v₁ v₂)
-/
def Hom : C ⋆ D -> C ⋆ D -> Type (max v₁ v₂)
  | .left x, .left y => ULift (x ⟶ y)
  | .right x, .right y => ULift (x ⟶ y)
  | .left _, .right _ => PUnit
  | .right _, .left _ => PEmpty

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : forall X : C ⋆ D, Hom X X

中文:
定义 id
  签名: : 对任意 X : C ⋆ D, Hom X X
-/
def id : forall X : C ⋆ D, Hom X X
  | .left x => ULift.up (𝟙 x)
  | .right x => ULift.up (𝟙 x)

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: : forall {x y z : C ⋆ D}, Hom x y -> Hom y z -> Hom x z

中文:
定义 comp
  签名: : 对任意 {x y z : C ⋆ D}, Hom x y -> Hom y z -> Hom x z
-/
def comp : forall {x y z : C ⋆ D}, Hom x y -> Hom y z -> Hom x z
  | .left _x, .left _y, .left _z, f, g => ULift.up (ULift.down f ≫ ULift.down g)
  | .left _x, .left _y, .right _z, _, _ => PUnit.unit
  | .left _x, .right _y, .right _z, _, _ => PUnit.unit
  | .right _x, .right _y, .right _z, f, g => ULift.up (ULift.down f ≫ ULift.down g)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category.{max v₁ v₂} (C ⋆ D)
  body: Hom X Y
  id _ := id _
  comp := comp
  assoc {a b c d} f g h := by
    cases a <;>
    cases b <;>
    cases c <;>
    cases d <;>
    simp only [Hom, comp, Category.assoc] <;>
    tauto
  id_comp {x y} f := by
    cases x <;> cases y <;> simp only [Hom, id, comp, Category.id_comp] <;> tauto
  comp

中文:
实例 :
  签名: Category.{max v₁ v₂} (C ⋆ D)
  定义体: Hom X Y
  id _ := id _
  comp := comp
  assoc {a b c d} f g h := by
    cases a <;>
    cases b <;>
    cases c <;>
    cases d <;>
    simp only [Hom, comp, Category.assoc] <;>
    tauto
  id_comp {x y} f := by
    cases x <;> cases y <;> simp only [Hom, id, comp, Category.id_comp] <;> tauto
  comp
-/
instance : Category.{max v₁ v₂} (C ⋆ D) where
  Hom X Y := Hom X Y
  id _ := id _
  comp := comp
  assoc {a b c d} f g h := by
    cases a <;>
    cases b <;>
    cases c <;>
    cases d <;>
    simp only [Hom, comp, Category.assoc] <;>
    tauto
  id_comp {x y} f := by
    cases x <;> cases y <;> simp only [Hom, id, comp, Category.id_comp] <;> tauto
  comp_id {x y} f := by
    cases x <;> cases y <;> simp only [Hom, id, comp, Category.comp_id] <;> tauto

@[aesop safe destruct (rule_sets := [CategoryTheory])]
/--
lemma `false_of_right_to_left` / 引理 `false_of_right_to_left`

English:
lemma false_of_right_to_left
  given: {X : D} {Y : C} (f : right X ⟶ left Y)
  statement: False
  proof: (f : PEmpty).elim

中文:
引理 false_of_right_to_left
  条件: {X : D} {Y : C} (f : right X ⟶ left Y)
  结论: False
  证明: (f : PEmpty).elim

Depends on / 依赖: PEmpty
-/
lemma false_of_right_to_left {X : D} {Y : C} (f : right X ⟶ left Y) : False := (f : PEmpty).elim

instance {X : C} {Y : D} : Unique (left X ⟶ right Y) := inferInstanceAs (Unique PUnit)

/--
Definition of `edge` / `edge` 的定义

English:
definition edge
  signature: (c : C) (d : D)
  body: default

中文:
定义 edge
  签名: (c : C) (d : D)
  定义体: default
-/
def edge (c : C) (d : D) : left c ⟶ right d := default

end CategoryStructure

section Inclusions

/-- The canonical inclusion from C to `C ⋆ D`.
Terms of the form `(inclLeft C D).map f` should be treated as primitive when working with joins
and one should avoid trying to reduce them. For this reason, there is no `inclLeft_map` simp
lemma. -/
@[simps! obj]
/--
Definition of `inclLeft` / `inclLeft` 的定义

English:
definition inclLeft
  signature: : C ⥤ C ⋆ D where
  body: left
  map := ULift.up

中文:
定义 inclLeft
  签名: : C ⥤ C ⋆ D where
  定义体: left
  map := ULift.up
-/
def inclLeft : C ⥤ C ⋆ D where
  obj := left
  map := ULift.up

/-- The canonical inclusion from D to `C ⋆ D`.
Terms of the form `(inclRight C D).map f` should be treated as primitive when working with joins
and one should avoid trying to reduce them. For this reason, there is no `inclRight_map` simp
lemma. -/
@[simps! obj]
/--
Definition of `inclRight` / `inclRight` 的定义

English:
definition inclRight
  signature: : D ⥤ C ⋆ D where
  body: right
  map := ULift.up

中文:
定义 inclRight
  签名: : D ⥤ C ⋆ D where
  定义体: right
  map := ULift.up
-/
def inclRight : D ⥤ C ⋆ D where
  obj := right
  map := ULift.up

variable {C D}

/-- An induction principle for morphisms in a join of categories: a morphism is either of the form
`(inclLeft _ _).map _`, `(inclRight _ _).map _`, or is `edge _ _`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/--
Definition of `homInduction` / `homInduction` 的定义

English:
definition homInduction
  signature: {P : {x y : C ⋆ D} -> (x ⟶ y) -> Sort*}
  body: match x, y, f with
  | .left x, .left y, .up f => left x y f
  | .right x, .right y, .up f => right x y f
  | .left x, .right y, _ => edge x y

@[simp]

中文:
定义 homInduction
  签名: {P : {x y : C ⋆ D} -> (x ⟶ y) -> Sort*}
  定义体: match x, y, f with
  | .left x, .left y, .up f => left x y f
  | .right x, .right y, .up f => right x y f
  | .left x, .right y, _ => edge x y

@[simp]
-/
def homInduction {P : {x y : C ⋆ D} -> (x ⟶ y) -> Sort*}
    (left : forall x y : C, (f : x ⟶ y) -> P ((inclLeft C D).map f))
    (right : forall x y : D, (f : x ⟶ y) -> P ((inclRight C D).map f))
    (edge : forall (c : C) (d : D), P (edge c d))
    {x y : C ⋆ D} (f : x ⟶ y) : P f :=
  match x, y, f with
  | .left x, .left y, .up f => left x y f
  | .right x, .right y, .up f => right x y f
  | .left x, .right y, _ => edge x y

@[simp]
/--
lemma `homInduction_left` / 引理 `homInduction_left`

English:
lemma homInduction_left
  statement: {P : {x y : C ⋆ D} -> (x ⟶ y) -> Sort*}
  proof: rfl

@[simp]

中文:
引理 homInduction_left
  结论: {P : {x y : C ⋆ D} -> (x ⟶ y) -> Sort*}
  证明: rfl

@[simp]
-/
lemma homInduction_left {P : {x y : C ⋆ D} -> (x ⟶ y) -> Sort*}
    (left : forall x y : C, (f : x ⟶ y) -> P ((inclLeft C D).map f))
    (right : forall x y : D, (f : x ⟶ y) -> P ((inclRight C D).map f))
    (edge : forall (c : C) (d : D), P (edge c d))
    {x y : C} (f : x ⟶ y) : homInduction left right edge ((inclLeft C D).map f) = left x y f :=
  rfl

@[simp]
/--
lemma `homInduction_right` / 引理 `homInduction_right`

English:
lemma homInduction_right
  statement: {P : {x y : C ⋆ D} -> (x ⟶ y) -> Sort*}
  proof: rfl

@[simp]

中文:
引理 homInduction_right
  结论: {P : {x y : C ⋆ D} -> (x ⟶ y) -> Sort*}
  证明: rfl

@[simp]
-/
lemma homInduction_right {P : {x y : C ⋆ D} -> (x ⟶ y) -> Sort*}
    (left : forall x y : C, (f : x ⟶ y) -> P ((inclLeft C D).map f))
    (right : forall x y : D, (f : x ⟶ y) -> P ((inclRight C D).map f))
    (edge : forall (c : C) (d : D), P (edge c d))
    {x y : D} (f : x ⟶ y) : homInduction left right edge ((inclRight C D).map f) = right x y f :=
  rfl

@[simp]
/--
lemma `homInduction_edge` / 引理 `homInduction_edge`

English:
lemma homInduction_edge
  statement: {P : {x y : C ⋆ D} -> (x ⟶ y) -> Sort*}
  proof: rfl

中文:
引理 homInduction_edge
  结论: {P : {x y : C ⋆ D} -> (x ⟶ y) -> Sort*}
  证明: rfl
-/
lemma homInduction_edge {P : {x y : C ⋆ D} -> (x ⟶ y) -> Sort*}
    (left : forall x y : C, (f : x ⟶ y) -> P ((inclLeft C D).map f))
    (right : forall x y : D, (f : x ⟶ y) -> P ((inclRight C D).map f))
    (edge : forall (c : C) (d : D), P (edge c d))
    {c : C} {d : D} : homInduction left right edge (Join.edge c d) = edge c d :=
  rfl

variable (C D)

/--
Definition of `inclLeftFullyFaithful` / `inclLeftFullyFaithful` 的定义

English:
definition inclLeftFullyFaithful
  signature: : (inclLeft C D).FullyFaithful where
  body: f.down

中文:
定义 inclLeftFullyFaithful
  签名: : (inclLeft C D).FullyFaithful where
  定义体: f.down

Depends on / 依赖: f.down
-/
def inclLeftFullyFaithful : (inclLeft C D).FullyFaithful where
  preimage f := f.down

/--
Definition of `inclRightFullyFaithful` / `inclRightFullyFaithful` 的定义

English:
definition inclRightFullyFaithful
  signature: : (inclRight C D).FullyFaithful where
  body: f.down

.full instance inclLeftFull : (inclLeft C D).Full := inclLeftFullyFaithful C D

.full instance inclRightFull : (inclRight C D).Full := inclRightFullyFaithful C D

.faithful instance inclLeftFaithful : (inclLeft C D).Faithful := inclLeftFullyFaithful C D

.faithful instance inclRightFaithful 

中文:
定义 inclRightFullyFaithful
  签名: : (inclRight C D).FullyFaithful where
  定义体: f.down

.full instance inclLeftFull : (inclLeft C D).Full := inclLeftFullyFaithful C D

.full instance inclRightFull : (inclRight C D).Full := inclRightFullyFaithful C D

.faithful instance inclLeftFaithful : (inclLeft C D).Faithful := inclLeftFullyFaithful C D

.faithful instance inclRightFaithful 

Depends on / 依赖: f.down
-/
def inclRightFullyFaithful : (inclRight C D).FullyFaithful where
  preimage f := f.down

.full instance inclLeftFull : (inclLeft C D).Full := inclLeftFullyFaithful C D

.full instance inclRightFull : (inclRight C D).Full := inclRightFullyFaithful C D

.faithful instance inclLeftFaithful : (inclLeft C D).Faithful := inclLeftFullyFaithful C D

.faithful instance inclRightFaithful : (inclRight C D).Faithful := inclRightFullyFaithful C D

variable {C} in
/--
lemma `id_left` / 引理 `id_left`

English:
lemma id_left
  given: (c : C)
  statement: 𝟙 (left c) = (inclLeft C D).map (𝟙 c)
  proof: rfl

中文:
引理 id_left
  条件: (c : C)
  结论: 𝟙 (left c) = (inclLeft C D).map (𝟙 c)
  证明: rfl
-/
lemma id_left (c : C) : 𝟙 (left c) = (inclLeft C D).map (𝟙 c) := rfl

variable {D} in
/--
lemma `id_right` / 引理 `id_right`

English:
lemma id_right
  given: (d : D)
  statement: 𝟙 (right d) = (inclRight C D).map (𝟙 d)
  proof: rfl

中文:
引理 id_right
  条件: (d : D)
  结论: 𝟙 (right d) = (inclRight C D).map (𝟙 d)
  证明: rfl
-/
lemma id_right (d : D) : 𝟙 (right d) = (inclRight C D).map (𝟙 d) := rfl

/-- The "canonical" natural transformation from `(Prod.fst C D) ⋙ inclLeft C D` to
`(Prod.snd C D) ⋙ inclRight C D`. This is bundling together all the edge morphisms
into the data of a natural transformation. -/
@[simps!]
/--
Definition of `edgeTransform` / `edgeTransform` 的定义

English:
definition edgeTransform
  signature: :
  body: fun (c, d) => edge c d

中文:
定义 edgeTransform
  签名: :
  定义体: fun (c, d) => edge c d
-/
def edgeTransform :
    Prod.fst C D ⋙ inclLeft C D ⟶ Prod.snd C D ⋙ inclRight C D where
  app := fun (c, d) => edge c d

end Inclusions

section Functoriality

variable {C D} {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `mkFunctor` / `mkFunctor` 的定义

English:
definition mkFunctor
  signature: (F : C ⥤ E) (G : D ⥤ E) (α : Prod.fst C D ⋙ F ⟶ Prod.snd C D ⋙ G)
  body: match X with
    | .left x => F.obj x
    | .right x => G.obj x
  map f :=
    homInduction
      (left := fun _ _ f => F.map f)
      (right := fun _ _ g => G.map g)
      (edge := fun c d => α.app (c, d))
      f
  map_id x := by
    cases x
    · dsimp only [id_left, homInduction_left]
      simp

中文:
定义 mkFunctor
  签名: (F : C ⥤ E) (G : D ⥤ E) (α : Prod.fst C D ⋙ F ⟶ Prod.snd C D ⋙ G)
  定义体: match X with
    | .left x => F.obj x
    | .right x => G.obj x
  map f :=
    homInduction
      (left := fun _ _ f => F.map f)
      (right := fun _ _ g => G.map g)
      (edge := fun c d => α.app (c, d))
      f
  map_id x := by
    cases x
    · dsimp only [id_left, homInduction_left]
      simp

Depends on / 依赖: F.map, F.obj, Functor, Functor.map_comp, G.map, G.obj, Prod.sectL, edge.right, homInduction, homInduction_left, homInduction_right, id_left, id_right, left.edge, map_comp, map_id, naturality
-/
def mkFunctor (F : C ⥤ E) (G : D ⥤ E) (α : Prod.fst C D ⋙ F ⟶ Prod.snd C D ⋙ G) :
    C ⋆ D ⥤ E where
  obj X :=
    match X with
    | .left x => F.obj x
    | .right x => G.obj x
  map f :=
    homInduction
      (left := fun _ _ f => F.map f)
      (right := fun _ _ g => G.map g)
      (edge := fun c d => α.app (c, d))
      f
  map_id x := by
    cases x
    · dsimp only [id_left, homInduction_left]
      simp
    · dsimp only [id_right, homInduction_right]
      simp
  map_comp {x y z} f g := by
    cases f <;> cases g
    · simp [← Functor.map_comp]
    · case left.edge f d => simpa using! (α.naturality <| (Prod.sectL _ d).map f).symm
    · simp [← Functor.map_comp]
· case edge.right c _ _ f => simpa using! α.naturality (Prod.sectR c _).map f

section

variable (F : C ⥤ E) (G : D ⥤ E) (α : Prod.fst C D ⋙ F ⟶ Prod.snd C D ⋙ G)

-- As these equalities of objects are definitional, they should be fine.
@[simp]
/--
lemma `mkFunctor_obj_left` / 引理 `mkFunctor_obj_left`

English:
lemma mkFunctor_obj_left
  given: (c : C)
  statement: (mkFunctor F G α).obj (left c) = F.obj c
  proof: rfl

@[simp]

中文:
引理 mkFunctor_obj_left
  条件: (c : C)
  结论: (mkFunctor F G α).obj (left c) = F.obj c
  证明: rfl

@[simp]
-/
lemma mkFunctor_obj_left (c : C) : (mkFunctor F G α).obj (left c) = F.obj c := rfl

@[simp]
/--
lemma `mkFunctor_obj_right` / 引理 `mkFunctor_obj_right`

English:
lemma mkFunctor_obj_right
  given: (d : D)
  statement: (mkFunctor F G α).obj (right d) = G.obj d
  proof: rfl

@[simp]

中文:
引理 mkFunctor_obj_right
  条件: (d : D)
  结论: (mkFunctor F G α).obj (right d) = G.obj d
  证明: rfl

@[simp]
-/
lemma mkFunctor_obj_right (d : D) : (mkFunctor F G α).obj (right d) = G.obj d := rfl

@[simp]
/--
lemma `mkFunctor_map_inclLeft` / 引理 `mkFunctor_map_inclLeft`

English:
lemma mkFunctor_map_inclLeft
  given: {c c' : C} (f : c ⟶ c')
  proof: rfl

中文:
引理 mkFunctor_map_inclLeft
  条件: {c c' : C} (f : c ⟶ c')
  证明: rfl
-/
lemma mkFunctor_map_inclLeft {c c' : C} (f : c ⟶ c') :
    (mkFunctor F G α).map ((inclLeft C D).map f) = F.map f :=
  rfl

/-- Precomposing `mkFunctor F G α` with the left inclusion gives back `F`. -/
@[simps!]
/--
Definition of `mkFunctorLeft` / `mkFunctorLeft` 的定义

English:
definition mkFunctorLeft
  signature: : inclLeft C D ⋙ mkFunctor F G α ≅ F
  body: Iso.refl _

中文:
定义 mkFunctorLeft
  签名: : inclLeft C D ⋙ mkFunctor F G α ≅ F
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def mkFunctorLeft : inclLeft C D ⋙ mkFunctor F G α ≅ F := Iso.refl _

/-- Precomposing `mkFunctor F G α` with the right inclusion gives back `G`. -/
@[simps!]
/--
Definition of `mkFunctorRight` / `mkFunctorRight` 的定义

English:
definition mkFunctorRight
  signature: : inclRight C D ⋙ mkFunctor F G α ≅ G
  body: Iso.refl _

@[simp]

中文:
定义 mkFunctorRight
  签名: : inclRight C D ⋙ mkFunctor F G α ≅ G
  定义体: Iso.refl _

@[simp]

Depends on / 依赖: Iso.refl
-/
def mkFunctorRight : inclRight C D ⋙ mkFunctor F G α ≅ G := Iso.refl _

@[simp]
/--
lemma `mkFunctor_map_inclRight` / 引理 `mkFunctor_map_inclRight`

English:
lemma mkFunctor_map_inclRight
  given: {d d' : D} (f : d ⟶ d')
  proof: rfl

中文:
引理 mkFunctor_map_inclRight
  条件: {d d' : D} (f : d ⟶ d')
  证明: rfl
-/
lemma mkFunctor_map_inclRight {d d' : D} (f : d ⟶ d') :
    (mkFunctor F G α).map ((inclRight C D).map f) = G.map f :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Whiskering `mkFunctor F G α` with the universal transformation gives back `α`. -/
@[simp]
/--
lemma `mkFunctor_edgeTransform` / 引理 `mkFunctor_edgeTransform`

English:
lemma mkFunctor_edgeTransform
  proof: by
  ext x
  simp [mkFunctor]

@[simp]

中文:
引理 mkFunctor_edgeTransform
  证明: by
  ext x
  simp [mkFunctor]

@[simp]

Depends on / 依赖: mkFunctor
-/
lemma mkFunctor_edgeTransform :
    whiskerRight (edgeTransform C D) (mkFunctor F G α) = α := by
  ext x
  simp [mkFunctor]

@[simp]
/--
lemma `mkFunctor_map_edge` / 引理 `mkFunctor_map_edge`

English:
lemma mkFunctor_map_edge
  given: (c : C) (d : D)
  proof: rfl

中文:
引理 mkFunctor_map_edge
  条件: (c : C) (d : D)
  证明: rfl
-/
lemma mkFunctor_map_edge (c : C) (d : D) :
    (mkFunctor F G α).map (edge c d) = α.app (c, d) :=
  rfl

end

/--
Definition of `mkNatTrans` / `mkNatTrans` 的定义

English:
definition mkNatTrans
  signature: {F : C ⋆ D ⥤ E} {F' : C ⋆ D ⥤ E}
  body: match x with
    | left x => αₗ.app x
    | right x => αᵣ.app x
  naturality {x y} f := by
    cases f with
    | @left x y f => simpa using! αₗ.naturality f
    | @right x y f => simpa using! αᵣ.naturality f
    | @edge c d => exact funext_iff.mp (NatTrans.ext_iff.mp h) (c, d)

中文:
定义 mkNatTrans
  签名: {F : C ⋆ D ⥤ E} {F' : C ⋆ D ⥤ E}
  定义体: match x with
    | left x => αₗ.app x
    | right x => αᵣ.app x
  naturality {x y} f := by
    cases f with
    | @left x y f => simpa using! αₗ.naturality f
    | @right x y f => simpa using! αᵣ.naturality f
    | @edge c d => exact funext_iff.mp (NatTrans.ext_iff.mp h) (c, d)

Depends on / 依赖: NatTrans, NatTrans.ext_iff.mp, cat_disch, ext_iff, funext_iff, funext_iff.mp, naturality
-/
def mkNatTrans {F : C ⋆ D ⥤ E} {F' : C ⋆ D ⥤ E}
    (αₗ : inclLeft C D ⋙ F ⟶ inclLeft C D ⋙ F') (αᵣ : inclRight C D ⋙ F ⟶ inclRight C D ⋙ F')
    (h : whiskerRight (edgeTransform C D) F ≫ whiskerLeft (Prod.snd C D) αᵣ =
      whiskerLeft (Prod.fst C D) αₗ ≫ whiskerRight (edgeTransform C D) F' := by cat_disch) :
    F ⟶ F' where
  app x := match x with
    | left x => αₗ.app x
    | right x => αᵣ.app x
  naturality {x y} f := by
    cases f with
    | @left x y f => simpa using! αₗ.naturality f
    | @right x y f => simpa using! αᵣ.naturality f
    | @edge c d => exact funext_iff.mp (NatTrans.ext_iff.mp h) (c, d)

section

variable {F : C ⋆ D ⥤ E} {F' : C ⋆ D ⥤ E}
    (αₗ : inclLeft C D ⋙ F ⟶ inclLeft C D ⋙ F') (αᵣ : inclRight C D ⋙ F ⟶ inclRight C D ⋙ F')
    (h : whiskerRight (edgeTransform C D) F ≫ whiskerLeft (Prod.snd C D) αᵣ =
      whiskerLeft (Prod.fst C D) αₗ ≫ whiskerRight (edgeTransform C D) F' := by cat_disch)

set_option backward.privateInPublic true in
@[simp]
/--
lemma `mkNatTrans_app_left` / 引理 `mkNatTrans_app_left`

English:
lemma mkNatTrans_app_left
  given: (c : C)
  statement: (mkNatTrans αₗ αᵣ h).app (left c) = αₗ.app c
  proof: rfl

中文:
引理 mkNatTrans_app_left
  条件: (c : C)
  结论: (mk自然数Trans αₗ αᵣ h).app (left c) = αₗ.app c
  证明: rfl
-/
lemma mkNatTrans_app_left (c : C) : (mkNatTrans αₗ αᵣ h).app (left c) = αₗ.app c := rfl

set_option backward.privateInPublic true in
@[simp]
/--
lemma `mkNatTrans_app_right` / 引理 `mkNatTrans_app_right`

English:
lemma mkNatTrans_app_right
  given: (d : D)
  statement: (mkNatTrans αₗ αᵣ h).app (right d) = αᵣ.app d
  proof: rfl

中文:
引理 mkNatTrans_app_right
  条件: (d : D)
  结论: (mk自然数Trans αₗ αᵣ h).app (right d) = αᵣ.app d
  证明: rfl
-/
lemma mkNatTrans_app_right (d : D) : (mkNatTrans αₗ αᵣ h).app (right d) = αᵣ.app d := rfl

set_option backward.privateInPublic true in
@[simp]
/--
lemma `whiskerLeft_inclLeft_mkNatTrans` / 引理 `whiskerLeft_inclLeft_mkNatTrans`

English:
lemma whiskerLeft_inclLeft_mkNatTrans
  statement: whiskerLeft (inclLeft C D) (mkNatTrans αₗ αᵣ h) = αₗ
  proof: rfl

中文:
引理 whiskerLeft_inclLeft_mkNatTrans
  结论: whiskerLeft (inclLeft C D) (mk自然数Trans αₗ αᵣ h) = αₗ
  证明: rfl
-/
lemma whiskerLeft_inclLeft_mkNatTrans : whiskerLeft (inclLeft C D) (mkNatTrans αₗ αᵣ h) = αₗ := rfl

set_option backward.privateInPublic true in
@[simp]
/--
lemma `whiskerLeft_inclRight_mkNatTrans` / 引理 `whiskerLeft_inclRight_mkNatTrans`

English:
lemma whiskerLeft_inclRight_mkNatTrans
  proof: rfl

中文:
引理 whiskerLeft_inclRight_mkNatTrans
  证明: rfl
-/
lemma whiskerLeft_inclRight_mkNatTrans :
    whiskerLeft (inclRight C D) (mkNatTrans αₗ αᵣ h) = αᵣ := rfl

end

/--
lemma `natTrans_ext` / 引理 `natTrans_ext`

English:
lemma natTrans_ext
  statement: {F F' : C ⋆ D ⥤ E} {α β : F ⟶ F'}
  proof: by
  ext t
  cases t with
  | left t => exact congrArg (fun x => x.app t) h₁
  | right t => exact congrArg (fun x => x.app t) h₂

中文:
引理 natTrans_ext
  结论: {F F' : C ⋆ D ⥤ E} {α β : F ⟶ F'}
  证明: by
  ext t
  cases t with
  | left t => exact congrArg (fun x => x.app t) h₁
  | right t => exact congrArg (fun x => x.app t) h₂

Depends on / 依赖: x.app
-/
lemma natTrans_ext {F F' : C ⋆ D ⥤ E} {α β : F ⟶ F'}
    (h₁ : whiskerLeft (inclLeft C D) α = whiskerLeft (inclLeft C D) β)
    (h₂ : whiskerLeft (inclRight C D) α = whiskerLeft (inclRight C D) β) :
    α = β := by
  ext t
  cases t with
  | left t => exact congrArg (fun x => x.app t) h₁
  | right t => exact congrArg (fun x => x.app t) h₂

set_option backward.defeqAttrib.useBackward true in
/--
lemma `eq_mkNatTrans` / 引理 `eq_mkNatTrans`

English:
lemma eq_mkNatTrans
  given: {F F' : C ⋆ D ⥤ E} (α : F ⟶ F')
  proof: by
  apply natTrans_ext <;> simp

中文:
引理 eq_mkNatTrans
  条件: {F F' : C ⋆ D ⥤ E} (α : F ⟶ F')
  证明: by
  apply natTrans_ext <;> simp

Depends on / 依赖: natTrans_ext
-/
lemma eq_mkNatTrans {F F' : C ⋆ D ⥤ E} (α : F ⟶ F') :
    mkNatTrans (whiskerLeft (inclLeft C D) α) (whiskerLeft (inclRight C D) α) = α := by
  apply natTrans_ext <;> simp

section

/--
lemma `mkNatTransComp` / 引理 `mkNatTransComp`

English:
lemma mkNatTransComp
  proof: by
  apply natTrans_ext <;> cat_disch

中文:
引理 mkNatTransComp
  证明: by
  apply natTrans_ext <;> cat_disch

Depends on / 依赖: Prod.fst, Prod.snd, cat_disch, edgeTransform, mkNatTrans, natTrans_ext, reassoc_of, whiskerLeft, whiskerRight
-/
lemma mkNatTransComp
    {F F' F'' : C ⋆ D ⥤ E}
    (αₗ : inclLeft C D ⋙ F ⟶ inclLeft C D ⋙ F')
    (αᵣ : inclRight C D ⋙ F ⟶ inclRight C D ⋙ F')
    (βₗ : inclLeft C D ⋙ F' ⟶ inclLeft C D ⋙ F'')
    (βᵣ : inclRight C D ⋙ F' ⟶ inclRight C D ⋙ F'')
    (h : whiskerRight (edgeTransform C D) F ≫ whiskerLeft (Prod.snd C D) αᵣ =
      whiskerLeft (Prod.fst C D) αₗ ≫ whiskerRight (edgeTransform C D) F' := by cat_disch)
    (h' : whiskerRight (edgeTransform C D) F' ≫ whiskerLeft (Prod.snd C D) βᵣ =
      whiskerLeft (Prod.fst C D) βₗ ≫ whiskerRight (edgeTransform C D) F'' := by cat_disch) :
    mkNatTrans (αₗ ≫ βₗ) (αᵣ ≫ βᵣ) (by simp [← h', reassoc_of% h]) =
    mkNatTrans αₗ αᵣ h ≫ mkNatTrans βₗ βᵣ h' := by
  apply natTrans_ext <;> cat_disch

end

set_option backward.isDefEq.respectTransparency false in
/-- Two functors out of a join of categories are naturally isomorphic if their
compositions with the inclusions are isomorphic and the whiskering with the canonical
transformation is respected through these isomorphisms. -/
@[simps]
/--
Definition of `mkNatIso` / `mkNatIso` 的定义

English:
definition mkNatIso
  signature: {F : C ⋆ D ⥤ E} {G : C ⋆ D ⥤ E}
  body: mkNatTrans eₗ.hom eᵣ.hom (by simpa using h)
  inv := mkNatTrans eₗ.inv eᵣ.inv (by rw [Eq.comm, ← isoWhiskerLeft_inv, ← isoWhiskerLeft_inv,
    Iso.inv_comp_eq, ← Category.assoc, Eq.comm, Iso.comp_inv_eq, h])

中文:
定义 mkNatIso
  签名: {F : C ⋆ D ⥤ E} {G : C ⋆ D ⥤ E}
  定义体: mkNatTrans eₗ.hom eᵣ.hom (by simpa using h)
  inv := mkNatTrans eₗ.inv eᵣ.inv (by rw [Eq.comm, ← isoWhiskerLeft_inv, ← isoWhiskerLeft_inv,
    Iso.inv_comp_eq, ← Category.assoc, Eq.comm, Iso.comp_inv_eq, h])

Depends on / 依赖: Category, Category.assoc, Eq.comm, Iso.comp_inv_eq, Iso.inv_comp_eq, cat_disch, comp_inv_eq, inv_comp_eq, isoWhiskerLeft_inv, mkNatTrans
-/
def mkNatIso {F : C ⋆ D ⥤ E} {G : C ⋆ D ⥤ E}
    (eₗ : inclLeft C D ⋙ F ≅ inclLeft C D ⋙ G)
    (eᵣ : inclRight C D ⋙ F ≅ inclRight C D ⋙ G)
    (h : whiskerRight (edgeTransform C D) F ≫ (isoWhiskerLeft (Prod.snd C D) eᵣ).hom =
      (isoWhiskerLeft (Prod.fst C D) eₗ).hom ≫ whiskerRight (edgeTransform C D) G := by cat_disch) :
    F ≅ G where
  hom := mkNatTrans eₗ.hom eᵣ.hom (by simpa using h)
  inv := mkNatTrans eₗ.inv eᵣ.inv (by rw [Eq.comm, ← isoWhiskerLeft_inv, ← isoWhiskerLeft_inv,
    Iso.inv_comp_eq, ← Category.assoc, Eq.comm, Iso.comp_inv_eq, h])

/--
Definition of `mapPair` / `mapPair` 的定义

English:
definition mapPair
  signature: (Fₗ : C ⥤ E) (Fᵣ : D ⥤ E')
  body: mkFunctor (Fₗ ⋙ inclLeft _ _) (Fᵣ ⋙ inclRight _ _) { app := fun _ => edge _ _ }

中文:
定义 mapPair
  签名: (Fₗ : C ⥤ E) (Fᵣ : D ⥤ E')
  定义体: mkFunctor (Fₗ ⋙ inclLeft _ _) (Fᵣ ⋙ inclRight _ _) { app := fun _ => edge _ _ }

Depends on / 依赖: inclLeft, inclRight, mkFunctor
-/
def mapPair (Fₗ : C ⥤ E) (Fᵣ : D ⥤ E') : C ⋆ D ⥤ E ⋆ E' :=
  mkFunctor (Fₗ ⋙ inclLeft _ _) (Fᵣ ⋙ inclRight _ _) { app := fun _ => edge _ _ }

section mapPair

variable (Fₗ : C ⥤ E) (Fᵣ : D ⥤ E')

@[simp]
/--
lemma `mapPair_obj_left` / 引理 `mapPair_obj_left`

English:
lemma mapPair_obj_left
  given: (c : C)
  statement: (mapPair Fₗ Fᵣ).obj (left c) = left (Fₗ.obj c)
  proof: rfl

@[simp]

中文:
引理 mapPair_obj_left
  条件: (c : C)
  结论: (mapPair Fₗ Fᵣ).obj (left c) = left (Fₗ.obj c)
  证明: rfl

@[simp]
-/
lemma mapPair_obj_left (c : C) : (mapPair Fₗ Fᵣ).obj (left c) = left (Fₗ.obj c) := rfl

@[simp]
/--
lemma `mapPair_obj_right` / 引理 `mapPair_obj_right`

English:
lemma mapPair_obj_right
  given: (d : D)
  statement: (mapPair Fₗ Fᵣ).obj (right d) = right (Fᵣ.obj d)
  proof: rfl

@[simp]

中文:
引理 mapPair_obj_right
  条件: (d : D)
  结论: (mapPair Fₗ Fᵣ).obj (right d) = right (Fᵣ.obj d)
  证明: rfl

@[simp]
-/
lemma mapPair_obj_right (d : D) : (mapPair Fₗ Fᵣ).obj (right d) = right (Fᵣ.obj d) := rfl

@[simp]
/--
lemma `mapPair_map_inclLeft` / 引理 `mapPair_map_inclLeft`

English:
lemma mapPair_map_inclLeft
  given: {c c' : C} (f : c ⟶ c')
  proof: rfl

@[simp]

中文:
引理 mapPair_map_inclLeft
  条件: {c c' : C} (f : c ⟶ c')
  证明: rfl

@[simp]
-/
lemma mapPair_map_inclLeft {c c' : C} (f : c ⟶ c') :
    (mapPair Fₗ Fᵣ).map ((inclLeft C D).map f) = (inclLeft E E').map (Fₗ.map f) := rfl

@[simp]
/--
lemma `mapPair_map_inclRight` / 引理 `mapPair_map_inclRight`

English:
lemma mapPair_map_inclRight
  given: {d d' : D} (f : d ⟶ d')
  proof: rfl

中文:
引理 mapPair_map_inclRight
  条件: {d d' : D} (f : d ⟶ d')
  证明: rfl
-/
lemma mapPair_map_inclRight {d d' : D} (f : d ⟶ d') :
    (mapPair Fₗ Fᵣ).map ((inclRight C D).map f) = (inclRight E E').map (Fᵣ.map f) := rfl

/-- Characterizing `mapPair` on left morphisms. -/
@[simps! hom_app inv_app]
/--
Definition of `mapPairLeft` / `mapPairLeft` 的定义

English:
definition mapPairLeft
  signature: : inclLeft _ _ ⋙ mapPair Fₗ Fᵣ ≅ Fₗ ⋙ inclLeft _ _
  body: mkFunctorLeft _ _ _

中文:
定义 mapPairLeft
  签名: : inclLeft _ _ ⋙ mapPair Fₗ Fᵣ ≅ Fₗ ⋙ inclLeft _ _
  定义体: mkFunctorLeft _ _ _

Depends on / 依赖: mkFunctorLeft
-/
def mapPairLeft : inclLeft _ _ ⋙ mapPair Fₗ Fᵣ ≅ Fₗ ⋙ inclLeft _ _ := mkFunctorLeft _ _ _

/-- Characterizing `mapPair` on right morphisms. -/
@[simps! hom_app inv_app]
/--
Definition of `mapPairRight` / `mapPairRight` 的定义

English:
definition mapPairRight
  signature: : inclRight _ _ ⋙ mapPair Fₗ Fᵣ ≅ Fᵣ ⋙ inclRight _ _
  body: mkFunctorRight _ _ _

中文:
定义 mapPairRight
  签名: : inclRight _ _ ⋙ mapPair Fₗ Fᵣ ≅ Fᵣ ⋙ inclRight _ _
  定义体: mkFunctorRight _ _ _

Depends on / 依赖: mkFunctorRight
-/
def mapPairRight : inclRight _ _ ⋙ mapPair Fₗ Fᵣ ≅ Fᵣ ⋙ inclRight _ _ := mkFunctorRight _ _ _

end mapPair

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Any functor out of a join is naturally isomorphic to a functor of the form `mkFunctor F G α`. -/
@[simps!]
/--
Definition of `isoMkFunctor` / `isoMkFunctor` 的定义

English:
definition isoMkFunctor
  signature: (F : C ⋆ D ⥤ E)
  body: mkNatIso (mkFunctorLeft _ _ _).symm (mkFunctorRight _ _ _).symm

中文:
定义 isoMkFunctor
  签名: (F : C ⋆ D ⥤ E)
  定义体: mkNatIso (mkFunctorLeft _ _ _).symm (mkFunctorRight _ _ _).symm

Depends on / 依赖: mkFunctorLeft, mkFunctorRight, mkNatIso
-/
def isoMkFunctor (F : C ⋆ D ⥤ E) :
    F ≅ mkFunctor (inclLeft C D ⋙ F) (inclRight C D ⋙ F) (whiskerRight (edgeTransform C D) F) :=
  mkNatIso (mkFunctorLeft _ _ _).symm (mkFunctorRight _ _ _).symm

/-- `mapPair` respects identities -/
@[simps!]
/--
Definition of `mapPairId` / `mapPairId` 的定义

English:
definition mapPairId
  signature: : mapPair (𝟭 C) (𝟭 D) ≅ 𝟭 (C ⋆ D)
  body: mkNatIso
    (mapPairLeft _ _ ≪≫ Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm)
    (mapPairRight _ _ ≪≫ Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm)

中文:
定义 mapPairId
  签名: : mapPair (𝟭 C) (𝟭 D) ≅ 𝟭 (C ⋆ D)
  定义体: mkNatIso
    (mapPairLeft _ _ ≪≫ Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm)
    (mapPairRight _ _ ≪≫ Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm)

Depends on / 依赖: Functor, Functor.leftUnitor, Functor.rightUnitor, leftUnitor, mapPairLeft, mapPairRight, mkNatIso, rightUnitor
-/
def mapPairId : mapPair (𝟭 C) (𝟭 D) ≅ 𝟭 (C ⋆ D) :=
  mkNatIso
    (mapPairLeft _ _ ≪≫ Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm)
    (mapPairRight _ _ ≪≫ Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm)

variable {J : Type u₅} [Category.{v₅} J]
  {K : Type u₆} [Category.{v₆} K]

-- @[simps!] times out here
/--
Definition of `mapPairComp` / `mapPairComp` 的定义

English:
definition mapPairComp
  signature: (Fₗ : C ⥤ E) (Fᵣ : D ⥤ E') (Gₗ : E ⥤ J) (Gᵣ : E' ⥤ K)
  body: mkNatIso
    (mapPairLeft (Fₗ ⋙ Gₗ) (Fᵣ ⋙ Gᵣ) ≪≫
      Functor.associator Fₗ Gₗ (inclLeft J K) ≪≫
      (isoWhiskerLeft Fₗ (mapPairLeft Gₗ Gᵣ).symm) ≪≫
      (Functor.associator Fₗ (inclLeft E E') (mapPair Gₗ Gᵣ)).symm ≪≫
      isoWhiskerRight (mapPairLeft Fₗ Fᵣ).symm (mapPair Gₗ Gᵣ))
    (mapPairRi

中文:
定义 mapPairComp
  签名: (Fₗ : C ⥤ E) (Fᵣ : D ⥤ E') (Gₗ : E ⥤ J) (Gᵣ : E' ⥤ K)
  定义体: mkNatIso
    (mapPairLeft (Fₗ ⋙ Gₗ) (Fᵣ ⋙ Gᵣ) ≪≫
      Functor.associator Fₗ Gₗ (inclLeft J K) ≪≫
      (isoWhiskerLeft Fₗ (mapPairLeft Gₗ Gᵣ).symm) ≪≫
      (Functor.associator Fₗ (inclLeft E E') (mapPair Gₗ Gᵣ)).symm ≪≫
      isoWhiskerRight (mapPairLeft Fₗ Fᵣ).symm (mapPair Gₗ Gᵣ))
    (mapPairRi

Depends on / 依赖: Functor, Functor.associator, associator, inclLeft, inclRight, isoWhiskerLeft, isoWhiskerRight, mapPair, mapPairLeft, mapPairRight, mkNatIso
-/
def mapPairComp (Fₗ : C ⥤ E) (Fᵣ : D ⥤ E') (Gₗ : E ⥤ J) (Gᵣ : E' ⥤ K) :
    mapPair (Fₗ ⋙ Gₗ) (Fᵣ ⋙ Gᵣ) ≅ mapPair Fₗ Fᵣ ⋙ mapPair Gₗ Gᵣ :=
  mkNatIso
    (mapPairLeft (Fₗ ⋙ Gₗ) (Fᵣ ⋙ Gᵣ) ≪≫
      Functor.associator Fₗ Gₗ (inclLeft J K) ≪≫
      (isoWhiskerLeft Fₗ (mapPairLeft Gₗ Gᵣ).symm) ≪≫
      (Functor.associator Fₗ (inclLeft E E') (mapPair Gₗ Gᵣ)).symm ≪≫
      isoWhiskerRight (mapPairLeft Fₗ Fᵣ).symm (mapPair Gₗ Gᵣ))
    (mapPairRight (Fₗ ⋙ Gₗ) (Fᵣ ⋙ Gᵣ) ≪≫
      Functor.associator Fᵣ Gᵣ (inclRight J K) ≪≫
      (isoWhiskerLeft Fᵣ (mapPairRight Gₗ Gᵣ).symm) ≪≫
      (Functor.associator Fᵣ (inclRight E E') (mapPair Gₗ Gᵣ)).symm ≪≫
      isoWhiskerRight (mapPairRight Fₗ Fᵣ).symm (mapPair Gₗ Gᵣ))

section mapPairComp

variable (Fₗ : C ⥤ E) (Fᵣ : D ⥤ E') (Gₗ : E ⥤ J) (Gᵣ : E' ⥤ K)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `mapPairComp_hom_app_left` / 引理 `mapPairComp_hom_app_left`

English:
lemma mapPairComp_hom_app_left
  given: (c : C)
  proof: by
  dsimp [mapPairComp]
  simp

中文:
引理 mapPairComp_hom_app_left
  条件: (c : C)
  证明: by
  dsimp [mapPairComp]
  simp

Depends on / 依赖: mapPairComp
-/
lemma mapPairComp_hom_app_left (c : C) :
    (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).hom.app (left c) = 𝟙 (left (Gₗ.obj (Fₗ.obj c))) := by
  dsimp [mapPairComp]
  simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `mapPairComp_hom_app_right` / 引理 `mapPairComp_hom_app_right`

English:
lemma mapPairComp_hom_app_right
  given: (d : D)
  proof: by
  dsimp [mapPairComp]
  simp

中文:
引理 mapPairComp_hom_app_right
  条件: (d : D)
  证明: by
  dsimp [mapPairComp]
  simp

Depends on / 依赖: mapPairComp
-/
lemma mapPairComp_hom_app_right (d : D) :
    (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).hom.app (right d) = 𝟙 (right (Gᵣ.obj (Fᵣ.obj d))) := by
  dsimp [mapPairComp]
  simp

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `mapPairComp_inv_app_left` / 引理 `mapPairComp_inv_app_left`

English:
lemma mapPairComp_inv_app_left
  given: (c : C)
  proof: by
  dsimp [mapPairComp]
  simp

中文:
引理 mapPairComp_inv_app_left
  条件: (c : C)
  证明: by
  dsimp [mapPairComp]
  simp

Depends on / 依赖: mapPairComp
-/
lemma mapPairComp_inv_app_left (c : C) :
    (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).inv.app (left c) = 𝟙 (left (Gₗ.obj (Fₗ.obj c))) := by
  dsimp [mapPairComp]
  simp

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `mapPairComp_inv_app_right` / 引理 `mapPairComp_inv_app_right`

English:
lemma mapPairComp_inv_app_right
  given: (d : D)
  proof: by
  dsimp [mapPairComp]
  simp

中文:
引理 mapPairComp_inv_app_right
  条件: (d : D)
  证明: by
  dsimp [mapPairComp]
  simp

Depends on / 依赖: mapPairComp
-/
lemma mapPairComp_inv_app_right (d : D) :
    (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).inv.app (right d) = 𝟙 (right (Gᵣ.obj (Fᵣ.obj d))) := by
  dsimp [mapPairComp]
  simp

end mapPairComp

end Functoriality

section NaturalTransforms

variable {E : Type u₃} [Category.{v₃} E]
  {E' : Type u₄} [Category.{v₄} E']

variable {C D}

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- A natural transformation `Fₗ ⟶ Gₗ` induces a natural transformation
  `mapPair Fₗ H ⟶ mapPair Gₗ H` for every `H : D ⥤ E'`. -/
@[simps!]
/--
Definition of `mapWhiskerRight` / `mapWhiskerRight` 的定义

English:
definition mapWhiskerRight
  signature: {Fₗ : C ⥤ E} {Gₗ : C ⥤ E} (α : Fₗ ⟶ Gₗ) (H : D ⥤ E')
  body: mkNatTrans
    ((mapPairLeft Fₗ H).hom ≫ whiskerRight α (inclLeft E E') ≫ (mapPairLeft Gₗ H).inv)
    ((mapPairRight Fₗ H).hom ≫ whiskerRight (𝟙 H) (inclRight E E') ≫ (mapPairRight Gₗ H).inv)

中文:
定义 mapWhiskerRight
  签名: {Fₗ : C ⥤ E} {Gₗ : C ⥤ E} (α : Fₗ ⟶ Gₗ) (H : D ⥤ E')
  定义体: mkNatTrans
    ((mapPairLeft Fₗ H).hom ≫ whiskerRight α (inclLeft E E') ≫ (mapPairLeft Gₗ H).inv)
    ((mapPairRight Fₗ H).hom ≫ whiskerRight (𝟙 H) (inclRight E E') ≫ (mapPairRight Gₗ H).inv)

Depends on / 依赖: inclLeft, inclRight, mapPairLeft, mapPairRight, mkNatTrans, whiskerRight
-/
def mapWhiskerRight {Fₗ : C ⥤ E} {Gₗ : C ⥤ E} (α : Fₗ ⟶ Gₗ) (H : D ⥤ E') :
    mapPair Fₗ H ⟶ mapPair Gₗ H :=
  mkNatTrans
    ((mapPairLeft Fₗ H).hom ≫ whiskerRight α (inclLeft E E') ≫ (mapPairLeft Gₗ H).inv)
    ((mapPairRight Fₗ H).hom ≫ whiskerRight (𝟙 H) (inclRight E E') ≫ (mapPairRight Gₗ H).inv)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `mapWhiskerRight_comp` / 引理 `mapWhiskerRight_comp`

English:
lemma mapWhiskerRight_comp
  statement: {Fₗ : C ⥤ E} {Gₗ : C ⥤ E} {Hₗ : C ⥤ E}
  proof: by
  cat_disch

中文:
引理 mapWhiskerRight_comp
  结论: {Fₗ : C ⥤ E} {Gₗ : C ⥤ E} {Hₗ : C ⥤ E}
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma mapWhiskerRight_comp {Fₗ : C ⥤ E} {Gₗ : C ⥤ E} {Hₗ : C ⥤ E}
    (α : Fₗ ⟶ Gₗ) (β : Gₗ ⟶ Hₗ) (H : D ⥤ E') :
    mapWhiskerRight (α ≫ β) H = mapWhiskerRight α H ≫ mapWhiskerRight β H := by
  cat_disch

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `mapWhiskerRight_id` / 引理 `mapWhiskerRight_id`

English:
lemma mapWhiskerRight_id
  given: (Fₗ : C ⥤ E) (H : D ⥤ E')
  proof: by
  cat_disch

#adaptation_note

中文:
引理 mapWhiskerRight_id
  条件: (Fₗ : C ⥤ E) (H : D ⥤ E')
  证明: by
  cat_disch

#adaptation_note

Depends on / 依赖: cat_disch
-/
lemma mapWhiskerRight_id (Fₗ : C ⥤ E) (H : D ⥤ E') :
    mapWhiskerRight (𝟙 Fₗ) H = 𝟙 _ := by
  cat_disch

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- A natural transformation `Fᵣ ⟶ Gᵣ` induces a natural transformation
  `mapPair H Fᵣ ⟶ mapPair H Gᵣ` for every `H : C ⥤ E`. -/
@[simps!]
/--
Definition of `mapWhiskerLeft` / `mapWhiskerLeft` 的定义

English:
definition mapWhiskerLeft
  signature: (H : C ⥤ E) {Fᵣ : D ⥤ E'} {Gᵣ : D ⥤ E'} (α : Fᵣ ⟶ Gᵣ)
  body: mkNatTrans
    ((mapPairLeft H Fᵣ).hom ≫ whiskerRight (𝟙 H) (inclLeft E E') ≫ (mapPairLeft H Gᵣ).inv)
    ((mapPairRight H Fᵣ).hom ≫ whiskerRight α (inclRight E E') ≫ (mapPairRight H Gᵣ).inv)

中文:
定义 mapWhiskerLeft
  签名: (H : C ⥤ E) {Fᵣ : D ⥤ E'} {Gᵣ : D ⥤ E'} (α : Fᵣ ⟶ Gᵣ)
  定义体: mkNatTrans
    ((mapPairLeft H Fᵣ).hom ≫ whiskerRight (𝟙 H) (inclLeft E E') ≫ (mapPairLeft H Gᵣ).inv)
    ((mapPairRight H Fᵣ).hom ≫ whiskerRight α (inclRight E E') ≫ (mapPairRight H Gᵣ).inv)

Depends on / 依赖: inclLeft, inclRight, mapPairLeft, mapPairRight, mkNatTrans, whiskerRight
-/
def mapWhiskerLeft (H : C ⥤ E) {Fᵣ : D ⥤ E'} {Gᵣ : D ⥤ E'} (α : Fᵣ ⟶ Gᵣ) :
    mapPair H Fᵣ ⟶ mapPair H Gᵣ :=
  mkNatTrans
    ((mapPairLeft H Fᵣ).hom ≫ whiskerRight (𝟙 H) (inclLeft E E') ≫ (mapPairLeft H Gᵣ).inv)
    ((mapPairRight H Fᵣ).hom ≫ whiskerRight α (inclRight E E') ≫ (mapPairRight H Gᵣ).inv)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `mapWhiskerLeft_comp` / 引理 `mapWhiskerLeft_comp`

English:
lemma mapWhiskerLeft_comp
  statement: {Fᵣ : D ⥤ E'} {Gᵣ : D ⥤ E'} {Hᵣ : D ⥤ E'}
  proof: by
  cat_disch

中文:
引理 mapWhiskerLeft_comp
  结论: {Fᵣ : D ⥤ E'} {Gᵣ : D ⥤ E'} {Hᵣ : D ⥤ E'}
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma mapWhiskerLeft_comp {Fᵣ : D ⥤ E'} {Gᵣ : D ⥤ E'} {Hᵣ : D ⥤ E'}
    (H : C ⥤ E) (α : Fᵣ ⟶ Gᵣ) (β : Gᵣ ⟶ Hᵣ) :
    mapWhiskerLeft H (α ≫ β) = mapWhiskerLeft H α ≫ mapWhiskerLeft H β := by
  cat_disch

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `mapWhiskerLeft_id` / 引理 `mapWhiskerLeft_id`

English:
lemma mapWhiskerLeft_id
  given: (H : C ⥤ E) (Fᵣ : D ⥤ E')
  proof: by
  cat_disch

#adaptation_note

中文:
引理 mapWhiskerLeft_id
  条件: (H : C ⥤ E) (Fᵣ : D ⥤ E')
  证明: by
  cat_disch

#adaptation_note

Depends on / 依赖: cat_disch
-/
lemma mapWhiskerLeft_id (H : C ⥤ E) (Fᵣ : D ⥤ E') :
    mapWhiskerLeft H (𝟙 Fᵣ) = 𝟙 _ := by
  cat_disch

#adaptation_note
/--
The statement of `mapWhiskerLeft_app` and `mapWhiskerRight_app` was determined using `simp` with
`respectTransparency.types false`. In order to apply these, we need a matching normal form.
We achieve this using `respectTransparency.types false` on this lemma, too.
Probable fix: Figure out what the intended statement of `mapWhiskerLeft_app` and
`mapWhiskerRight_app` is, and only then fix this lemma.
-/
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `mapWhisker_exchange` / 引理 `mapWhisker_exchange`

English:
lemma mapWhisker_exchange
  statement: (Fₗ : C ⥤ E) (Gₗ : C ⥤ E) (Fᵣ : D ⥤ E') (Gᵣ : D ⥤ E')
  proof: by
  ext
  cat_disch

#adaptation_note

中文:
引理 mapWhisker_exchange
  结论: (Fₗ : C ⥤ E) (Gₗ : C ⥤ E) (Fᵣ : D ⥤ E') (Gᵣ : D ⥤ E')
  证明: by
  ext
  cat_disch

#adaptation_note

Depends on / 依赖: cat_disch
-/
lemma mapWhisker_exchange (Fₗ : C ⥤ E) (Gₗ : C ⥤ E) (Fᵣ : D ⥤ E') (Gᵣ : D ⥤ E')
    (αₗ : Fₗ ⟶ Gₗ) (αᵣ : Fᵣ ⟶ Gᵣ) :
    mapWhiskerLeft Fₗ αᵣ ≫ mapWhiskerRight αₗ Gᵣ =
      mapWhiskerRight αₗ Fᵣ ≫ mapWhiskerLeft Gₗ αᵣ := by
  ext
  cat_disch

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- A natural isomorphism `Fᵣ ≅ Gᵣ` induces a natural isomorphism
  `mapPair H Fᵣ ≅ mapPair H Gᵣ` for every `H : C ⥤ E`. -/
@[simps!]
/--
Definition of `mapIsoWhiskerLeft` / `mapIsoWhiskerLeft` 的定义

English:
definition mapIsoWhiskerLeft
  signature: (H : C ⥤ E) {Fᵣ : D ⥤ E'} {Gᵣ : D ⥤ E'} (α : Fᵣ ≅ Gᵣ)
  body: mkNatIso
    (mapPairLeft H Fᵣ ≪≫ isoWhiskerRight (Iso.refl H) (inclLeft _ _) ≪≫ (mapPairLeft H Gᵣ).symm)
    (mapPairRight H Fᵣ ≪≫ isoWhiskerRight α (inclRight E E') ≪≫ (mapPairRight H Gᵣ).symm)

#adaptation_note

中文:
定义 mapIsoWhiskerLeft
  签名: (H : C ⥤ E) {Fᵣ : D ⥤ E'} {Gᵣ : D ⥤ E'} (α : Fᵣ ≅ Gᵣ)
  定义体: mkNatIso
    (mapPairLeft H Fᵣ ≪≫ isoWhiskerRight (Iso.refl H) (inclLeft _ _) ≪≫ (mapPairLeft H Gᵣ).symm)
    (mapPairRight H Fᵣ ≪≫ isoWhiskerRight α (inclRight E E') ≪≫ (mapPairRight H Gᵣ).symm)

#adaptation_note

Depends on / 依赖: Iso.refl, inclLeft, inclRight, isoWhiskerRight, mapPairLeft, mapPairRight, mkNatIso
-/
def mapIsoWhiskerLeft (H : C ⥤ E) {Fᵣ : D ⥤ E'} {Gᵣ : D ⥤ E'} (α : Fᵣ ≅ Gᵣ) :
    mapPair H Fᵣ ≅ mapPair H Gᵣ :=
  mkNatIso
    (mapPairLeft H Fᵣ ≪≫ isoWhiskerRight (Iso.refl H) (inclLeft _ _) ≪≫ (mapPairLeft H Gᵣ).symm)
    (mapPairRight H Fᵣ ≪≫ isoWhiskerRight α (inclRight E E') ≪≫ (mapPairRight H Gᵣ).symm)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- A natural isomorphism `Fᵣ ≅ Gᵣ` induces a natural isomorphism
  `mapPair Fₗ H ≅ mapPair Gₗ H` for every `H : C ⥤ E`. -/
@[simps!]
/--
Definition of `mapIsoWhiskerRight` / `mapIsoWhiskerRight` 的定义

English:
definition mapIsoWhiskerRight
  signature: {Fₗ : C ⥤ E} {Gₗ : C ⥤ E} (α : Fₗ ≅ Gₗ) (H : D ⥤ E')
  body: mkNatIso
    (mapPairLeft Fₗ H ≪≫ isoWhiskerRight α (inclLeft E E') ≪≫ (mapPairLeft Gₗ H).symm)
    (mapPairRight Fₗ H ≪≫ isoWhiskerRight (Iso.refl H) (inclRight E E') ≪≫ (mapPairRight Gₗ H).symm)

中文:
定义 mapIsoWhiskerRight
  签名: {Fₗ : C ⥤ E} {Gₗ : C ⥤ E} (α : Fₗ ≅ Gₗ) (H : D ⥤ E')
  定义体: mkNatIso
    (mapPairLeft Fₗ H ≪≫ isoWhiskerRight α (inclLeft E E') ≪≫ (mapPairLeft Gₗ H).symm)
    (mapPairRight Fₗ H ≪≫ isoWhiskerRight (Iso.refl H) (inclRight E E') ≪≫ (mapPairRight Gₗ H).symm)

Depends on / 依赖: Iso.refl, inclLeft, inclRight, isoWhiskerRight, mapPairLeft, mapPairRight, mkNatIso
-/
def mapIsoWhiskerRight {Fₗ : C ⥤ E} {Gₗ : C ⥤ E} (α : Fₗ ≅ Gₗ) (H : D ⥤ E') :
    mapPair Fₗ H ≅ mapPair Gₗ H :=
  mkNatIso
    (mapPairLeft Fₗ H ≪≫ isoWhiskerRight α (inclLeft E E') ≪≫ (mapPairLeft Gₗ H).symm)
    (mapPairRight Fₗ H ≪≫ isoWhiskerRight (Iso.refl H) (inclRight E E') ≪≫ (mapPairRight Gₗ H).symm)

/--
lemma `mapIsoWhiskerRight_hom` / 引理 `mapIsoWhiskerRight_hom`

English:
lemma mapIsoWhiskerRight_hom
  given: {Fₗ : C ⥤ E} {Gₗ : C ⥤ E} (α : Fₗ ≅ Gₗ) (H : D ⥤ E')
  proof: rfl

#adaptation_note

中文:
引理 mapIsoWhiskerRight_hom
  条件: {Fₗ : C ⥤ E} {Gₗ : C ⥤ E} (α : Fₗ ≅ Gₗ) (H : D ⥤ E')
  证明: rfl

#adaptation_note
-/
lemma mapIsoWhiskerRight_hom {Fₗ : C ⥤ E} {Gₗ : C ⥤ E} (α : Fₗ ≅ Gₗ) (H : D ⥤ E') :
    (mapIsoWhiskerRight α H).hom = mapWhiskerRight α.hom H := rfl

#adaptation_note
/--
The statement of `mapWhiskerLeft_app` and `mapWhiskerRight_app` was determined using `simp` with
`respectTransparency.types false`. In order to apply these, we need a matching normal form.
We achieve this using `respectTransparency.types false` on this lemma, too.
Probable fix: Figure out what the intended statement of `mapWhiskerLeft_app` and
`mapWhiskerRight_app` is, and only then fix this lemma.
-/
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `mapIsoWhiskerRight_inv` / 引理 `mapIsoWhiskerRight_inv`

English:
lemma mapIsoWhiskerRight_inv
  given: {Fₗ : C ⥤ E} {Gₗ : C ⥤ E} (α : Fₗ ≅ Gₗ) (H : D ⥤ E')
  proof: by
  ext x
  cases x <;> simp [mapIsoWhiskerRight]

中文:
引理 mapIsoWhiskerRight_inv
  条件: {Fₗ : C ⥤ E} {Gₗ : C ⥤ E} (α : Fₗ ≅ Gₗ) (H : D ⥤ E')
  证明: by
  ext x
  cases x <;> simp [mapIsoWhiskerRight]

Depends on / 依赖: mapIsoWhiskerRight
-/
lemma mapIsoWhiskerRight_inv {Fₗ : C ⥤ E} {Gₗ : C ⥤ E} (α : Fₗ ≅ Gₗ) (H : D ⥤ E') :
    (mapIsoWhiskerRight α H).inv = mapWhiskerRight α.inv H := by
  ext x
  cases x <;> simp [mapIsoWhiskerRight]

/--
lemma `mapIsoWhiskerLeft_hom` / 引理 `mapIsoWhiskerLeft_hom`

English:
lemma mapIsoWhiskerLeft_hom
  given: (H : C ⥤ E) {Fᵣ : D ⥤ E'} {Gᵣ : D ⥤ E'} (α : Fᵣ ≅ Gᵣ)
  proof: rfl

#adaptation_note

中文:
引理 mapIsoWhiskerLeft_hom
  条件: (H : C ⥤ E) {Fᵣ : D ⥤ E'} {Gᵣ : D ⥤ E'} (α : Fᵣ ≅ Gᵣ)
  证明: rfl

#adaptation_note
-/
lemma mapIsoWhiskerLeft_hom (H : C ⥤ E) {Fᵣ : D ⥤ E'} {Gᵣ : D ⥤ E'} (α : Fᵣ ≅ Gᵣ) :
    (mapIsoWhiskerLeft H α).hom = mapWhiskerLeft H α.hom := rfl

#adaptation_note
/--
The statement of `mapWhiskerLeft_app` and `mapWhiskerRight_app` was determined using `simp` with
`respectTransparency.types false`. In order to apply these, we need a matching normal form.
We achieve this using `respectTransparency.types false` on this lemma, too.
Probable fix: Figure out what the intended statement of `mapWhiskerLeft_app` and
`mapWhiskerRight_app` is, and only then fix this lemma.
-/
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `mapIsoWhiskerLeft_inv` / 引理 `mapIsoWhiskerLeft_inv`

English:
lemma mapIsoWhiskerLeft_inv
  given: (H : C ⥤ E) {Fᵣ : D ⥤ E'} {Gᵣ : D ⥤ E'} (α : Fᵣ ≅ Gᵣ)
  proof: by
  ext x
  cases x <;> simp [mapIsoWhiskerLeft]

中文:
引理 mapIsoWhiskerLeft_inv
  条件: (H : C ⥤ E) {Fᵣ : D ⥤ E'} {Gᵣ : D ⥤ E'} (α : Fᵣ ≅ Gᵣ)
  证明: by
  ext x
  cases x <;> simp [mapIsoWhiskerLeft]

Depends on / 依赖: mapIsoWhiskerLeft
-/
lemma mapIsoWhiskerLeft_inv (H : C ⥤ E) {Fᵣ : D ⥤ E'} {Gᵣ : D ⥤ E'} (α : Fᵣ ≅ Gᵣ) :
    (mapIsoWhiskerLeft H α).inv = mapWhiskerLeft H α.inv := by
  ext x
  cases x <;> simp [mapIsoWhiskerLeft]

end NaturalTransforms

section mapPairEquiv

variable {C' : Type u₃} [Category.{v₃} C']
  {D' : Type u₄} [Category.{v₄} D']

variable {C D}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Equivalent categories have equivalent joins. -/
@[simps]
/--
Definition of `mapPairEquiv` / `mapPairEquiv` 的定义

English:
definition mapPairEquiv
  signature: (e : C ≌ C') (e' : D ≌ D')
  body: mapPair e.functor e'.functor
  inverse := mapPair e.inverse e'.inverse
  unitIso :=
    mapPairId.symm ≪≫
      mapIsoWhiskerRight e.unitIso _ ≪≫
      mapIsoWhiskerLeft _ e'.unitIso ≪≫
      mapPairComp _ _ _ _
  counitIso :=
    (mapPairComp _ _ _ _).symm ≪≫
      mapIsoWhiskerRight e.counitIso _ 

中文:
定义 mapPairEquiv
  签名: (e : C ≌ C') (e' : D ≌ D')
  定义体: mapPair e.functor e'.functor
  inverse := mapPair e.inverse e'.inverse
  unitIso :=
    mapPairId.symm ≪≫
      mapIsoWhiskerRight e.unitIso _ ≪≫
      mapIsoWhiskerLeft _ e'.unitIso ≪≫
      mapPairComp _ _ _ _
  counitIso :=
    (mapPairComp _ _ _ _).symm ≪≫
      mapIsoWhiskerRight e.counitIso _ 

Depends on / 依赖: e.functor, functor, mapPair
-/
def mapPairEquiv (e : C ≌ C') (e' : D ≌ D') : C ⋆ D ≌ C' ⋆ D' where
  functor := mapPair e.functor e'.functor
  inverse := mapPair e.inverse e'.inverse
  unitIso :=
    mapPairId.symm ≪≫
      mapIsoWhiskerRight e.unitIso _ ≪≫
      mapIsoWhiskerLeft _ e'.unitIso ≪≫
      mapPairComp _ _ _ _
  counitIso :=
    (mapPairComp _ _ _ _).symm ≪≫
      mapIsoWhiskerRight e.counitIso _ ≪≫
      mapIsoWhiskerLeft _ e'.counitIso ≪≫
      mapPairId
  functor_unitIso_comp x := by
    cases x <;>
    simp [← (inclLeft C' D').map_comp, ← (inclRight C' D').map_comp]

/--
Instance `isEquivalenceMapPair` / 实例 `isEquivalenceMapPair`

English:
instance isEquivalenceMapPair
  signature: {F : C ⥤ C'} {F' : D ⥤ D'} [F.IsEquivalence] [F'.IsEquivalence]
  body: inferInstanceAs (mapPairEquiv F.asEquivalence F'.asEquivalence).functor.IsEquivalence

中文:
实例 isEquivalenceMapPair
  签名: {F : C ⥤ C'} {F' : D ⥤ D'} [F.IsEquivalence] [F'.IsEquivalence]
  定义体: inferInstanceAs (mapPairEquiv F.asEquivalence F'.asEquivalence).functor.IsEquivalence

Depends on / 依赖: F.asEquivalence, IsEquivalence, asEquivalence, functor, functor.IsEquivalence, mapPairEquiv
-/
instance isEquivalenceMapPair {F : C ⥤ C'} {F' : D ⥤ D'} [F.IsEquivalence] [F'.IsEquivalence] :
    (mapPair F F').IsEquivalence :=
  inferInstanceAs (mapPairEquiv F.asEquivalence F'.asEquivalence).functor.IsEquivalence

end mapPairEquiv

end Join

end CategoryTheory
