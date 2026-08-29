/-
Copyright (c) 2024 Mario Carneiro and Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl
-/
module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Category.Quiv

/-!
# The category of refl quivers

The category `ReflQuiv` of (bundled) reflexive quivers, and the free/forgetful adjunction between
`Cat` and `ReflQuiv`.
-/

@[expose] public section

namespace CategoryTheory
universe v u v₁ v₂ u₁ u₂

set_option linter.checkUnivs false in
/--
Definition of `ReflQuiv` / `ReflQuiv` 的定义

English:
definition ReflQuiv
  body: Bundled ReflQuiver.{v, u}

中文:
定义 ReflQuiv
  定义体: Bundled ReflQuiver.{v, u}

Depends on / 依赖: Bundled, ReflQuiver
-/
def ReflQuiv :=
  Bundled ReflQuiver.{v, u}

namespace ReflQuiv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort ReflQuiv (Type u)
  body: Bundled.α

中文:
实例 :
  签名: CoeSort ReflQuiv (类型u)
  定义体: Bundled.α

Depends on / 依赖: Bundled, binaryCofan_inl, colimit, colimit.isColimit, isColimit
-/
instance : CoeSort ReflQuiv (Type u) where coe := Bundled.α

instance (C : ReflQuiv.{v, u}) : ReflQuiver.{v, u} C := C.str

/--
Definition of `toQuiv` / `toQuiv` 的定义

English:
definition toQuiv
  signature: (C : ReflQuiv.{v, u})
  body: Quiv.of C.α

中文:
定义 toQuiv
  签名: (C : ReflQuiv.{v, u})
  定义体: Quiv.of C.α

Depends on / 依赖: Quiv.of, binaryCofan_inr, colimit, colimit.isColimit, isColimit
-/
def toQuiv (C : ReflQuiv.{v, u}) : Quiv.{v, u} := Quiv.of C.α

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (C : Type u) [ReflQuiver.{v} C]
  body: Bundled.of C

中文:
定义 of
  签名: (C : 类型u) [ReflQuiver.{v} C]
  定义体: Bundled.of C

Depends on / 依赖: Bundled, Bundled.of
-/
def of (C : Type u) [ReflQuiver.{v} C] : ReflQuiv.{v, u} := Bundled.of C

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited ReflQuiv
  body: ⟨ReflQuiv.of (Discrete default)⟩

中文:
实例 :
  签名: Inhabited ReflQuiv
  定义体: ⟨ReflQuiv.of (Discrete default)⟩

Depends on / 依赖: Discrete, ReflQuiv, ReflQuiv.of
-/
instance : Inhabited ReflQuiv := ⟨ReflQuiv.of (Discrete default)⟩

/--
theorem `of_val` / 定理 `of_val`

English:
theorem of_val
  given: (C : Type u) [ReflQuiver C]
  statement: (ReflQuiv.of C) = C
  proof: rfl

中文:
定理 of_val
  条件: (C : 类型u) [ReflQuiver C]
  结论: (ReflQuiv.of C) = C
  证明: rfl
-/
@[simp] theorem of_val (C : Type u) [ReflQuiver C] : (ReflQuiv.of C) = C := rfl

/--
Instance `category` / 实例 `category`

English:
instance category
  signature: : LargeCategory.{max v u} ReflQuiv.{v, u} where
  body: ReflPrefunctor C D
  id C := ReflPrefunctor.id C
  comp F G := ReflPrefunctor.comp F G

中文:
实例 category
  签名: : LargeCategory.{max v u} ReflQuiv.{v, u} where
  定义体: ReflPrefunctor C D
  id C := ReflPrefunctor.id C
  comp F G := ReflPrefunctor.comp F G

Depends on / 依赖: ReflPrefunctor
-/
instance category : LargeCategory.{max v u} ReflQuiv.{v, u} where
  Hom C D := ReflPrefunctor C D
  id C := ReflPrefunctor.id C
  comp F G := ReflPrefunctor.comp F G

/--
theorem `id_eq_id` / 定理 `id_eq_id`

English:
theorem id_eq_id
  given: (X : ReflQuiv)
  statement: 𝟙 X = 𝟭rq X
  proof: rfl

中文:
定理 id_eq_id
  条件: (X : ReflQuiv)
  结论: 𝟙 X = 𝟭rq X
  证明: rfl
-/
theorem id_eq_id (X : ReflQuiv) : 𝟙 X = 𝟭rq X := rfl
/--
theorem `comp_eq_comp` / 定理 `comp_eq_comp`

English:
theorem comp_eq_comp
  given: {X Y Z : ReflQuiv} (F : X ⟶ Y) (G : Y ⟶ Z)
  statement: F ≫ G = F ⋙rq G
  proof: rfl

@[simp]

中文:
定理 comp_eq_comp
  条件: {X Y Z : ReflQuiv} (F : X ⟶ Y) (G : Y ⟶ Z)
  结论: F ≫ G = F ⋙rq G
  证明: rfl

@[simp]
-/
theorem comp_eq_comp {X Y Z : ReflQuiv} (F : X ⟶ Y) (G : Y ⟶ Z) : F ≫ G = F ⋙rq G := rfl

@[simp]
/--
lemma `id_obj` / 引理 `id_obj`

English:
lemma id_obj
  given: (X : ReflQuiv) (x : X)
  statement: (ReflPrefunctor.toPrefunctor (𝟙 X)).obj x = x
  proof: rfl

@[simp]

中文:
引理 id_obj
  条件: (X : ReflQuiv) (x : X)
  结论: (ReflPrefunctor.toPrefunctor (𝟙 X)).obj x = x
  证明: rfl

@[simp]
-/
lemma id_obj (X : ReflQuiv) (x : X) : (ReflPrefunctor.toPrefunctor (𝟙 X)).obj x = x := rfl

@[simp]
/--
lemma `id_map` / 引理 `id_map`

English:
lemma id_map
  given: {X : ReflQuiv} {x y : X} (f : x ⟶ y)
  proof: rfl

@[simp]

中文:
引理 id_map
  条件: {X : ReflQuiv} {x y : X} (f : x ⟶ y)
  证明: rfl

@[simp]
-/
lemma id_map {X : ReflQuiv} {x y : X} (f : x ⟶ y) :
    (ReflPrefunctor.toPrefunctor (𝟙 X)).map f = f := rfl

@[simp]
/--
lemma `comp_obj` / 引理 `comp_obj`

English:
lemma comp_obj
  given: {X Y Z : ReflQuiv} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  proof: rfl

@[simp]

中文:
引理 comp_obj
  条件: {X Y Z : ReflQuiv} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  证明: rfl

@[simp]
-/
lemma comp_obj {X Y Z : ReflQuiv} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).obj x = g.obj (f.obj x) := rfl

@[simp]
/--
lemma `comp_map` / 引理 `comp_map`

English:
lemma comp_map
  given: {X Y Z : ReflQuiv} (f : X ⟶ Y) (g : Y ⟶ Z) {x y : X} (a : x ⟶ y)
  proof: rfl

中文:
引理 comp_map
  条件: {X Y Z : ReflQuiv} (f : X ⟶ Y) (g : Y ⟶ Z) {x y : X} (a : x ⟶ y)
  证明: rfl
-/
lemma comp_map {X Y Z : ReflQuiv} (f : X ⟶ Y) (g : Y ⟶ Z) {x y : X} (a : x ⟶ y) :
    (f ≫ g).map a = g.map (f.map a) := rfl

/-- The forgetful functor from categories to quivers. -/
@[simps]
/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: : Cat.{v, u} ⥤ ReflQuiv.{v, u} where
  body: ReflQuiv.of C
  map F := F.toFunctor.toReflPrefunctor

中文:
定义 forget
  签名: : Cat.{v, u} ⥤ ReflQuiv.{v, u} where
  定义体: ReflQuiv.of C
  map F := F.toFunctor.toReflPrefunctor

Depends on / 依赖: ReflQuiv, ReflQuiv.of
-/
def forget : Cat.{v, u} ⥤ ReflQuiv.{v, u} where
  obj C := ReflQuiv.of C
  map F := F.toFunctor.toReflPrefunctor

/--
theorem `forget_faithful` / 定理 `forget_faithful`

English:
theorem forget_faithful
  statement: {C D : Cat.{v, u}} (F G : C ⥤ D)
  proof: by
  cases F; cases G; cases hyp; rfl

中文:
定理 forget_faithful
  结论: {C D : Cat.{v, u}} (F G : C ⥤ D)
  证明: by
  cases F; cases G; cases hyp; rfl
-/
theorem forget_faithful {C D : Cat.{v, u}} (F G : C ⥤ D)
    (hyp : forget.map F.toCatHom = forget.map G.toCatHom) : F = G := by
  cases F; cases G; cases hyp; rfl

/--
Instance `forget.Faithful` / 实例 `forget.Faithful`

English:
instance forget.Faithful
  signature: : Functor.Faithful (forget) where
  body: fun hyp => Cat.Hom.ext forget_faithful _ _ hyp

中文:
实例 forget.Faithful
  签名: : Functor.Faithful (forget) where
  定义体: fun hyp => Cat.Hom.ext forget_faithful _ _ hyp

Depends on / 依赖: Cat.Hom.ext, forget_faithful
-/
instance forget.Faithful : Functor.Faithful (forget) where
map_injective := fun hyp => Cat.Hom.ext forget_faithful _ _ hyp

/-- The forgetful functor from categories to quivers. -/
@[simps]
/--
Definition of `forgetToQuiv` / `forgetToQuiv` 的定义

English:
definition forgetToQuiv
  signature: : ReflQuiv.{v, u} ⥤ Quiv.{v, u} where
  body: Quiv.of V
  map F := F.toPrefunctor

中文:
定义 forgetToQuiv
  签名: : ReflQuiv.{v, u} ⥤ Quiv.{v, u} where
  定义体: Quiv.of V
  map F := F.toPrefunctor

Depends on / 依赖: Quiv.of
-/
def forgetToQuiv : ReflQuiv.{v, u} ⥤ Quiv.{v, u} where
  obj V := Quiv.of V
  map F := F.toPrefunctor

/--
theorem `forgetToQuiv_faithful` / 定理 `forgetToQuiv_faithful`

English:
theorem forgetToQuiv_faithful
  statement: {V W : ReflQuiv} (F G : V ⥤rq W)
  proof: by
  cases F; cases G; cases hyp; rfl

中文:
定理 forgetToQuiv_faithful
  结论: {V W : ReflQuiv} (F G : V ⥤rq W)
  证明: by
  cases F; cases G; cases hyp; rfl
-/
theorem forgetToQuiv_faithful {V W : ReflQuiv} (F G : V ⥤rq W)
    (hyp : forgetToQuiv.map F = forgetToQuiv.map G) : F = G := by
  cases F; cases G; cases hyp; rfl

/--
Instance `forgetToQuiv.Faithful` / 实例 `forgetToQuiv.Faithful`

English:
instance forgetToQuiv.Faithful
  signature: : Functor.Faithful forgetToQuiv where
  body: fun hyp => forgetToQuiv_faithful _ _ hyp

中文:
实例 forgetToQuiv.Faithful
  签名: : Functor.Faithful forgetToQuiv where
  定义体: fun hyp => forgetToQuiv_faithful _ _ hyp

Depends on / 依赖: forgetToQuiv_faithful
-/
instance forgetToQuiv.Faithful : Functor.Faithful forgetToQuiv where
  map_injective := fun hyp => forgetToQuiv_faithful _ _ hyp

/--
theorem `forget_forgetToQuiv` / 定理 `forget_forgetToQuiv`

English:
theorem forget_forgetToQuiv
  statement: forget ⋙ forgetToQuiv = Quiv.forget
  proof: rfl

中文:
定理 forget_forgetToQuiv
  结论: forget ⋙ forgetToQuiv = Quiv.forget
  证明: rfl

Depends on / 依赖: forget, monoCoprod_of_preservesCoprod_of_reflectsMono
-/
theorem forget_forgetToQuiv : forget ⋙ forgetToQuiv = Quiv.forget := rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isoOfQuivIso` / `isoOfQuivIso` 的定义

English:
definition isoOfQuivIso
  signature: {V W : Type u} [ReflQuiver V] [ReflQuiver W]
  body: ReflPrefunctor.mk e.hom h_id
  inv := ReflPrefunctor.mk e.inv
    (fun Y => (Quiv.homEquivOfIso e).injective (by simp [Quiv.hom_map_inv_map_of_iso, h_id]))
  hom_inv_id := by
    apply forgetToQuiv.map_injective
    exact e.hom_inv_id
  inv_hom_id := by
    apply forgetToQuiv.map_injective
    exact

中文:
定义 isoOfQuivIso
  签名: {V W : 类型u} [ReflQuiver V] [ReflQuiver W]
  定义体: ReflPrefunctor.mk e.hom h_id
  inv := ReflPrefunctor.mk e.inv
    (fun Y => (Quiv.homEquivOfIso e).injective (by simp [Quiv.hom_map_inv_map_of_iso, h_id]))
  hom_inv_id := by
    apply forgetToQuiv.map_injective
    exact e.hom_inv_id
  inv_hom_id := by
    apply forgetToQuiv.map_injective
    exact

Depends on / 依赖: MonoCoprod, MonoCoprod.mono_map, _of_injective, e.hom.obj, mono_iff_injective, mono_map
-/
def isoOfQuivIso {V W : Type u} [ReflQuiver V] [ReflQuiver W]
    (e : Quiv.of V ≅ Quiv.of W)
    (h_id : forall (X : V), e.hom.map (𝟙rq X) = ReflQuiver.id (obj := W) (e.hom.obj X)) :
    ReflQuiv.of V ≅ ReflQuiv.of W where
  hom := ReflPrefunctor.mk e.hom h_id
  inv := ReflPrefunctor.mk e.inv
    (fun Y => (Quiv.homEquivOfIso e).injective (by simp [Quiv.hom_map_inv_map_of_iso, h_id]))
  hom_inv_id := by
    apply forgetToQuiv.map_injective
    exact e.hom_inv_id
  inv_hom_id := by
    apply forgetToQuiv.map_injective
    exact e.inv_hom_id

/--
Definition of `isoOfEquiv` / `isoOfEquiv` 的定义

English:
definition isoOfEquiv
  signature: {V W : Type u} [ReflQuiver V] [ReflQuiver W] (e : V ≃ W)
  body: isoOfQuivIso (Quiv.isoOfEquiv e he) h_id

中文:
定义 isoOfEquiv
  签名: {V W : 类型u} [ReflQuiver V] [ReflQuiver W] (e : V ≃ W)
  定义体: isoOfQuivIso (Quiv.isoOfEquiv e he) h_id
-/
def isoOfEquiv {V W : Type u} [ReflQuiver V] [ReflQuiver W] (e : V ≃ W)
    (he : forall (X Y : V), (X ⟶ Y) ≃ (e X ⟶ e Y))
    (h_id : forall (X : V), he _ _ (𝟙rq X) = ReflQuiver.id (obj := W) (e X)) :
    ReflQuiv.of V ≅ ReflQuiv.of W := isoOfQuivIso (Quiv.isoOfEquiv e he) h_id

end ReflQuiv

namespace ReflPrefunctor

/--
Definition of `toFunctor` / `toFunctor` 的定义

English:
definition toFunctor
  signature: {C D : Cat} (F : (ReflQuiv.of C) ⟶ (ReflQuiv.of D))
  body: F.obj
  map := F.map
  map_id := F.map_id
  map_comp := hyp

中文:
定义 toFunctor
  签名: {C D : Cat} (F : (ReflQuiv.of C) ⟶ (ReflQuiv.of D))
  定义体: F.obj
  map := F.map
  map_id := F.map_id
  map_comp := hyp
-/
def toFunctor {C D : Cat} (F : (ReflQuiv.of C) ⟶ (ReflQuiv.of D))
    (hyp : forall {X Y Z : ↑C} (f : X ⟶ Y) (g : Y ⟶ Z),
      F.map (CategoryStruct.comp (obj := C) f g) =
        CategoryStruct.comp (obj := D) (F.map f) (F.map g)) : C ⥤ D where
  obj := F.obj
  map := F.map
  map_id := F.map_id
  map_comp := hyp

end ReflPrefunctor

namespace Cat

variable (V : Type*) [ReflQuiver V]

/--
Inductive type `FreeReflRel` / 归纳类型 `FreeReflRel`

English:
inductive FreeReflRel
  parameters: : (X Y : Paths V) -> (f g : X ⟶ Y) -> Prop
  constructors (1):
    - mk: {X : V} : FreeReflRel X X (Quiver.Hom.toPath (𝟙rq X)) .nil

中文:
归纳类型 FreeReflRel
  参数: : (X Y : Paths V) -> (f g : X ⟶ Y) -> 命题
  构造子 (1 个):
    - mk: {X : V} : FreeReflRel X X (Quiver.Hom.toPath (𝟙rq X)) .nil
-/
inductive FreeReflRel : (X Y : Paths V) -> (f g : X ⟶ Y) -> Prop
  | mk {X : V} : FreeReflRel X X (Quiver.Hom.toPath (𝟙rq X)) .nil

/--
Definition of `FreeRefl` / `FreeRefl` 的定义

English:
definition FreeRefl
  body: Quotient (C := Paths V) (FreeReflRel V)

中文:
定义 FreeRefl
  定义体: Quotient (C := Paths V) (FreeReflRel V)

Depends on / 依赖: FreeReflRel, Quotient
-/
def FreeRefl := Quotient (C := Paths V) (FreeReflRel V)

namespace FreeRefl

variable {V}

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (FreeRefl V)
  body: inferInstanceAs (Category (Quotient _))

中文:
实例 :
  签名: Category (FreeRefl V)
  定义体: inferInstanceAs (Category (Quotient _))

Depends on / 依赖: Category, Quotient
-/
instance : Category (FreeRefl V) :=
  inferInstanceAs (Category (Quotient _))

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (v : V)
  body: (Quotient.functor _).obj v

中文:
定义 mk
  签名: (v : V)
  定义体: (Quotient.functor _).obj v

Depends on / 依赖: Quotient, Quotient.functor, functor
-/
def mk (v : V) : FreeRefl V := (Quotient.functor _).obj v

/-- Induction principle for the objects of the free category on a reflexive quiver. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/--
Definition of `induction` / `induction` 的定义

English:
definition induction
  signature: {motive : FreeRefl V -> Sort*} (mk : forall v, motive (mk v)) (x : FreeRefl V)
  body: mk _

中文:
定义 induction
  签名: {motive : FreeRefl V -> Sort*} (mk : 对任意 v, motive (mk v)) (x : FreeRefl V)
  定义体: mk _
-/
def induction {motive : FreeRefl V -> Sort*} (mk : forall v, motive (mk v)) (x : FreeRefl V) :
    motive x :=
  mk _

variable (V) in
/--
Definition of `quotientFunctor` / `quotientFunctor` 的定义

English:
definition quotientFunctor
  signature: : Paths V ⥤ FreeRefl V
  body: Quotient.functor (C := Paths V) (FreeReflRel (V := V))

中文:
定义 quotientFunctor
  签名: : Paths V ⥤ FreeRefl V
  定义体: Quotient.functor (C := Paths V) (FreeReflRel (V := V))

Depends on / 依赖: FreeReflRel, Quotient, Quotient.functor, functor
-/
def quotientFunctor : Paths V ⥤ FreeRefl V :=
  Quotient.functor (C := Paths V) (FreeReflRel (V := V))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (FreeRefl.quotientFunctor V).Full
  body: Quotient.full_functor _

中文:
实例 :
  签名: (FreeRefl.quotientFunctor V).Full
  定义体: Quotient.full_functor _

Depends on / 依赖: Quotient, Quotient.full_functor, full_functor
-/
instance : (FreeRefl.quotientFunctor V).Full :=
  Quotient.full_functor _

/--
Definition of `homMk` / `homMk` 的定义

English:
definition homMk
  signature: {v w : V} (f : v ⟶ w)
  body: (quotientFunctor V).map f.toPath

@[simp]

中文:
定义 homMk
  签名: {v w : V} (f : v ⟶ w)
  定义体: (quotientFunctor V).map f.toPath

@[simp]

Depends on / 依赖: f.toPath, quotientFunctor, toPath
-/
def homMk {v w : V} (f : v ⟶ w) : mk v ⟶ mk w := (quotientFunctor V).map f.toPath

@[simp]
/--
lemma `homMk_id` / 引理 `homMk_id`

English:
lemma homMk_id
  given: (v : V)
  statement: homMk (𝟙rq v) = 𝟙 _
  proof: Quotient.sound _ ⟨⟩

@[simp]

中文:
引理 homMk_id
  条件: (v : V)
  结论: homMk (𝟙rq v) = 𝟙 _
  证明: Quotient.sound _ ⟨⟩

@[simp]

Depends on / 依赖: Quotient, Quotient.sound
-/
lemma homMk_id (v : V) : homMk (𝟙rq v) = 𝟙 _ :=
  Quotient.sound _ ⟨⟩

@[simp]
/--
lemma `quotientFunctor_map_nil` / 引理 `quotientFunctor_map_nil`

English:
lemma quotientFunctor_map_nil
  given: (x : Paths V)
  proof: Functor.map_id _ _

@[simp]

中文:
引理 quotientFunctor_map_nil
  条件: (x : Paths V)
  证明: Functor.map_id _ _

@[simp]

Depends on / 依赖: Functor, Functor.map_id, map_id
-/
lemma quotientFunctor_map_nil (x : Paths V) :
    (quotientFunctor V).map (.nil : x ⟶ x) = 𝟙 _ :=
  Functor.map_id _ _

@[simp]
/--
lemma `quotientFunctor_map_cons` / 引理 `quotientFunctor_map_cons`

English:
lemma quotientFunctor_map_cons
  statement: {x y z : Paths V}
  proof: rfl

中文:
引理 quotientFunctor_map_cons
  结论: {x y z : Paths V}
  证明: rfl
-/
lemma quotientFunctor_map_cons {x y z : Paths V}
    (p : x ⟶ y) (q : Quiver.Hom (V := V) y z) :
    (quotientFunctor V).map (p.cons q : x ⟶ z) =
      (quotientFunctor V).map p ≫ homMk q :=
  rfl

variable (V) in
/--
Definition of `morphismPropertyHomMk` / `morphismPropertyHomMk` 的定义

English:
definition morphismPropertyHomMk
  signature: : MorphismProperty (FreeRefl V)
  body: .ofHoms (fun (e : Σ (x y : V), x ⟶ y) => homMk e.2.2)

中文:
定义 morphismPropertyHomMk
  签名: : Morphism命题erty (FreeRefl V)
  定义体: .ofHoms (fun (e : Σ (x y : V), x ⟶ y) => homMk e.2.2)

Depends on / 依赖: ofHoms
-/
def morphismPropertyHomMk : MorphismProperty (FreeRefl V) :=
    .ofHoms (fun (e : Σ (x y : V), x ⟶ y) => homMk e.2.2)

/--
lemma `morphismPropertyHomMk_homMk` / 引理 `morphismPropertyHomMk_homMk`

English:
lemma morphismPropertyHomMk_homMk
  given: {x y : V} (e : x ⟶ y)
  proof: by
  dsimp only [morphismPropertyHomMk]
  rw [MorphismProperty.ofHoms_iff]
  exact ⟨⟨x, y, e⟩, rfl⟩

@[elab_as_elim, induction_eliminator]

中文:
引理 morphismPropertyHomMk_homMk
  条件: {x y : V} (e : x ⟶ y)
  证明: by
  dsimp only [morphismPropertyHomMk]
  rw [MorphismProperty.ofHoms_iff]
  exact ⟨⟨x, y, e⟩, rfl⟩

@[elab_as_elim, induction_eliminator]

Depends on / 依赖: MorphismProperty, MorphismProperty.ofHoms_iff, morphismPropertyHomMk, ofHoms_iff
-/
lemma morphismPropertyHomMk_homMk {x y : V} (e : x ⟶ y) :
    morphismPropertyHomMk V (homMk e) := by
  dsimp only [morphismPropertyHomMk]
  rw [MorphismProperty.ofHoms_iff]
  exact ⟨⟨x, y, e⟩, rfl⟩

@[elab_as_elim, induction_eliminator]
/--
lemma `hom_induction` / 引理 `hom_induction`

English:
lemma hom_induction
  statement: {motive : forall {x y : FreeRefl V} (_ : x ⟶ y), Prop}
  proof: by
    induction x using induction with | _ x
    induction y using induction with | _ y
    obtain ⟨f, rfl⟩ := (quotientFunctor _).map_surjective f
    induction f with
    | nil => simpa using! id x
    | cons _ f h => simpa using! comp_homMk _ f h

中文:
引理 hom_induction
  结论: {motive : 对任意 {x y : FreeRefl V} (_ : x ⟶ y), 命题}
  证明: by
    induction x using induction with | _ x
    induction y using induction with | _ y
    obtain ⟨f, rfl⟩ := (quotientFunctor _).map_surjective f
    induction f with
    | nil => simpa using! id x
    | cons _ f h => simpa using! comp_homMk _ f h

Depends on / 依赖: comp_homMk, map_surjective, quotientFunctor
-/
lemma hom_induction {motive : forall {x y : FreeRefl V} (_ : x ⟶ y), Prop}
    (id : forall (x : V), motive (homMk (𝟙rq x)))
    (comp_homMk : forall {x y z : V} (f : mk x ⟶ mk y) (g : y ⟶ z),
      motive f -> motive (f ≫ homMk g)) {x y : FreeRefl V} (f : x ⟶ y) :
  motive f := by
    induction x using induction with | _ x
    induction y using induction with | _ y
    obtain ⟨f, rfl⟩ := (quotientFunctor _).map_surjective f
    induction f with
    | nil => simpa using! id x
    | cons _ f h => simpa using! comp_homMk _ f h

open MorphismProperty in
/--
lemma `multiplicativeClosure_morphismPropertyHomMk` / 引理 `multiplicativeClosure_morphismPropertyHomMk`

English:
lemma multiplicativeClosure_morphismPropertyHomMk
  proof: le_antisymm (by simp) (by
    intro _ _ f hf
    clear hf
    induction f using hom_induction with
    | id => exact le_multiplicativeClosure _ _ (morphismPropertyHomMk_homMk _)
    | comp_homMk _ _ h =>
      exact comp_mem _ _ _ h (le_multiplicativeClosure _ _ (morphismPropertyHomMk_homMk _)))

中文:
引理 multiplicativeClosure_morphismPropertyHomMk
  证明: le_antisymm (by simp) (by
    intro _ _ f hf
    clear hf
    induction f using hom_induction with
    | id => exact le_multiplicativeClosure _ _ (morphismPropertyHomMk_homMk _)
    | comp_homMk _ _ h =>
      exact comp_mem _ _ _ h (le_multiplicativeClosure _ _ (morphismPropertyHomMk_homMk _)))

Depends on / 依赖: comp_homMk, comp_mem, hom_induction, le_antisymm, le_multiplicativeClosure, morphismPropertyHomMk_homMk
-/
lemma multiplicativeClosure_morphismPropertyHomMk :
    (morphismPropertyHomMk V).multiplicativeClosure = ⊤ :=
  le_antisymm (by simp) (by
    intro _ _ f hf
    clear hf
    induction f using hom_induction with
    | id => exact le_multiplicativeClosure _ _ (morphismPropertyHomMk_homMk _)
    | comp_homMk _ _ h =>
      exact comp_mem _ _ _ h (le_multiplicativeClosure _ _ (morphismPropertyHomMk_homMk _)))

/--
lemma `morphismProperty_eq_top` / 引理 `morphismProperty_eq_top`

English:
lemma morphismProperty_eq_top
  statement: {W : MorphismProperty (FreeRefl V)}
  proof: le_antisymm (by simp) (by
    rw [← multiplicativeClosure_morphismPropertyHomMk]; rw [MorphismProperty.multiplicativeClosure_le_iff]
    rintro _ _ _ ⟨h⟩
    apply hW)

中文:
引理 morphismProperty_eq_top
  结论: {W : Morphism命题erty (FreeRefl V)}
  证明: le_antisymm (by simp) (by
    rw [← multiplicativeClosure_morphismPropertyHomMk]; rw [MorphismProperty.multiplicativeClosure_le_iff]
    rintro _ _ _ ⟨h⟩
    apply hW)

Depends on / 依赖: MorphismProperty, MorphismProperty.multiplicativeClosure_le_iff, le_antisymm, multiplicativeClosure_le_iff, multiplicativeClosure_morphismPropertyHomMk
-/
lemma morphismProperty_eq_top {W : MorphismProperty (FreeRefl V)}
    [W.IsMultiplicative] (hW : forall {x y : V} (e : x ⟶ y), W (homMk e)) :
    W = ⊤ :=
  le_antisymm (by simp) (by
    rw [← multiplicativeClosure_morphismPropertyHomMk]; rw [MorphismProperty.multiplicativeClosure_le_iff]
    rintro _ _ _ ⟨h⟩
    apply hW)

section

variable {D : Type*} [Category* D] (F : V ⥤rq D)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : FreeRefl V ⥤ D
  body: Quotient.lift _ (Paths.lift F.toPrefunctor) (by
    rintro _ _ _ _ ⟨h⟩
    simp)

中文:
定义 lift
  签名: : FreeRefl V ⥤ D
  定义体: Quotient.lift _ (Paths.lift F.toPrefunctor) (by
    rintro _ _ _ _ ⟨h⟩
    simp)

Depends on / 依赖: F.toPrefunctor, Paths.lift, Quotient, Quotient.lift, toPrefunctor
-/
def lift : FreeRefl V ⥤ D :=
  Quotient.lift _ (Paths.lift F.toPrefunctor) (by
    rintro _ _ _ _ ⟨h⟩
    simp)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `lift_obj` / 引理 `lift_obj`

English:
lemma lift_obj
  given: (v : V)
  statement: (lift F).obj (mk v) = F.obj v
  proof: rfl

中文:
引理 lift_obj
  条件: (v : V)
  结论: (lift F).obj (mk v) = F.obj v
  证明: rfl
-/
lemma lift_obj (v : V) : (lift F).obj (mk v) = F.obj v := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `lift_map` / 引理 `lift_map`

English:
lemma lift_map
  given: {v w : V} (f : v ⟶ w)
  statement: (lift F).map (homMk f) = F.map f
  proof: Category.id_comp _

中文:
引理 lift_map
  条件: {v w : V} (f : v ⟶ w)
  结论: (lift F).map (homMk f) = F.map f
  证明: Category.id_comp _

Depends on / 依赖: Category, Category.id_comp, id_comp
-/
lemma lift_map {v w : V} (f : v ⟶ w) : (lift F).map (homMk f) = F.map f :=
  Category.id_comp _

end

section

variable {D : Type*} [Category* D]
  (obj : V -> D) (map : forall {v w : V}, (v ⟶ w) -> (obj v ⟶ obj w))
  (map_id : forall (v : V), map (𝟙rq v) = 𝟙 _)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `lift'` / `lift'` 的定义

English:
definition lift'
  signature: : FreeRefl V ⥤ D
  body: lift { obj := obj, map := map, map_id := map_id }

中文:
定义 lift'
  签名: : FreeRefl V ⥤ D
  定义体: lift { obj := obj, map := map, map_id := map_id }

Depends on / 依赖: map_id
-/
def lift' : FreeRefl V ⥤ D :=
  lift { obj := obj, map := map, map_id := map_id }

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `lift'_obj` / 引理 `lift'_obj`

English:
lemma lift'_obj
  given: (v : V)
  proof: rfl

中文:
引理 lift'_obj
  条件: (v : V)
  证明: rfl
-/
lemma lift'_obj (v : V) :
    (lift' obj map map_id).obj (mk v) = obj v := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `lift'_map` / 引理 `lift'_map`

English:
lemma lift'_map
  given: {v w : V} (f : v ⟶ w)
  proof: by
  simp [lift']

中文:
引理 lift'_map
  条件: {v w : V} (f : v ⟶ w)
  证明: by
  simp [lift']
-/
lemma lift'_map {v w : V} (f : v ⟶ w) :
    (lift' obj map map_id).map (homMk f) = map f := by
  simp [lift']

end

/--
theorem `lift_unique'` / 定理 `lift_unique'`

English:
theorem lift_unique'
  statement: {V} [ReflQuiver V] {D} [Category* D] (F₁ F₂ : FreeRefl V ⥤ D)
  proof: Quotient.lift_unique' (C := Cat.free.obj (Quiv.of V)) (FreeReflRel (V := V)) _ _ h

中文:
定理 lift_unique'
  结论: {V} [ReflQuiver V] {D} [Category* D] (F₁ F₂ : FreeRefl V ⥤ D)
  证明: Quotient.lift_unique' (C := Cat.free.obj (Quiv.of V)) (FreeReflRel (V := V)) _ _ h

Depends on / 依赖: Cat.free.obj, FreeReflRel, Quiv.of, Quotient, Quotient.lift_unique, lift_unique
-/
theorem lift_unique' {V} [ReflQuiver V] {D} [Category* D] (F₁ F₂ : FreeRefl V ⥤ D)
    (h : quotientFunctor V ⋙ F₁ = quotientFunctor V ⋙ F₂) :
    F₁ = F₂ :=
  Quotient.lift_unique' (C := Cat.free.obj (Quiv.of V)) (FreeReflRel (V := V)) _ _ h

/--
lemma `functor_ext` / 引理 `functor_ext`

English:
lemma functor_ext
  statement: {D : Type*} [Category* D]
  proof: lift_unique' _ _ (Paths.ext_functor (by ext; apply h₁) (fun _ _ _ => h₂ _))

@[simp]

中文:
引理 functor_ext
  结论: {D : 类型} [Category* D]
  证明: lift_unique' _ _ (Paths.ext_functor (by ext; apply h₁) (fun _ _ _ => h₂ _))

@[simp]

Depends on / 依赖: HasPullbacks, IsStableUnderComposition, P.IsStableUnderComposition, Paths.ext_functor, ext_functor, hasPullbacks, lift_unique
-/
lemma functor_ext {D : Type*} [Category* D]
    {F G : FreeRefl V ⥤ D} (h₁ : forall v, F.obj (mk v) = G.obj (mk v))
    (h₂ : forall {v w : V} (f : v ⟶ w), F.map (homMk f) =
      eqToHom (h₁ v) ≫ G.map (homMk f) ≫ eqToHom (h₁ w).symm) : F = G :=
  lift_unique' _ _ (Paths.ext_functor (by ext; apply h₁) (fun _ _ _ => h₂ _))

@[simp]
/--
lemma `quotientFunctor_map_id` / 引理 `quotientFunctor_map_id`

English:
lemma quotientFunctor_map_id
  given: (V) [ReflQuiver V] (X : V)
  proof: Quotient.sound _ .mk

中文:
引理 quotientFunctor_map_id
  条件: (V) [ReflQuiver V] (X : V)
  证明: Quotient.sound _ .mk

Depends on / 依赖: Quotient, Quotient.sound
-/
lemma quotientFunctor_map_id (V) [ReflQuiver V] (X : V) :
    (FreeRefl.quotientFunctor V).map (𝟙rq X).toPath = 𝟙 _ :=
  Quotient.sound _ .mk

set_option backward.isDefEq.respectTransparency.types false in
instance (V : Type*) [ReflQuiver V] [Unique V] : Unique (FreeRefl V) :=
  inferInstanceAs (Unique (Quotient _))

set_option backward.isDefEq.respectTransparency.types false in
instance (V : Type*) [ReflQuiver V] [Unique V]
    [forall (x y : V), Unique (x ⟶ y)] (x y : FreeRefl V) :
    Unique (x ⟶ y) where
  default := homMk default
  uniq f := by
    induction f using hom_induction with
    | id => congr; subsingleton
    | @comp_homMk x y z _ g h =>
      obtain rfl := Subsingleton.elim y z
      obtain rfl := Subsingleton.elim g (𝟙rq _)
      simp [h]

instance (V : Type*) [ReflQuiver V] [Unique V]
    [forall (x y : V), Subsingleton (x ⟶ y)] (x y : FreeRefl V) :
    Subsingleton (x ⟶ y) :=
  letI (x y : V) : Unique (x ⟶ y) := by
    obtain rfl : x = y := by subsingleton
    exact (unique_iff_subsingleton_and_nonempty _ |>.mpr ⟨inferInstance, ⟨𝟙rq _⟩⟩).some
  inferInstance

end FreeRefl

/-- Given a refl quiver `V`, this is the refl functor `V ⥤rq FreeRefl V` which
is the counit of the adjunction between reflexive quivers and categories. -/
@[simps]
/--
Definition of `toFreeRefl` / `toFreeRefl` 的定义

English:
definition toFreeRefl
  signature: : V ⥤rq FreeRefl V where
  body: .mk
  map := FreeRefl.homMk

中文:
定义 toFreeRefl
  签名: : V ⥤rq FreeRefl V where
  定义体: .mk
  map := FreeRefl.homMk
-/
def toFreeRefl : V ⥤rq FreeRefl V where
  obj := .mk
  map := FreeRefl.homMk

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
attribute [local simp] Functor.toReflPrefunctor in
variable {V} in
/--
lemma `FreeRefl.lift_spec` / 引理 `FreeRefl.lift_spec`

English:
lemma FreeRefl.lift_spec
  given: {D : Type*} [Category* D] (F : V ⥤rq D)
  proof: ReflPrefunctor.ext (fun v => by simp) (by simp)

中文:
引理 FreeRefl.lift_spec
  条件: {D : 类型} [Category* D] (F : V ⥤rq D)
  证明: ReflPrefunctor.ext (fun v => by simp) (by simp)

Depends on / 依赖: ReflPrefunctor, ReflPrefunctor.ext
-/
lemma FreeRefl.lift_spec {D : Type*} [Category* D] (F : V ⥤rq D) :
    Cat.toFreeRefl V ⋙rq (Cat.FreeRefl.lift F).toReflPrefunctor = F :=
  ReflPrefunctor.ext (fun v => by simp) (by simp)

variable {V} {W : Type*} [ReflQuiver W] (F : V ⥤rq W)
set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `freeReflMap` / `freeReflMap` 的定义

English:
definition freeReflMap
  signature: : FreeRefl V ⥤ FreeRefl W
  body: FreeRefl.lift' (fun v => .mk (F.obj v)) (fun f => FreeRefl.homMk (F.map f))
    (fun v => by simp)

中文:
定义 freeReflMap
  签名: : FreeRefl V ⥤ FreeRefl W
  定义体: FreeRefl.lift' (fun v => .mk (F.obj v)) (fun f => FreeRefl.homMk (F.map f))
    (fun v => by simp)

Depends on / 依赖: F.map, F.obj, FreeRefl, FreeRefl.homMk, FreeRefl.lift
-/
def freeReflMap : FreeRefl V ⥤ FreeRefl W :=
  FreeRefl.lift' (fun v => .mk (F.obj v)) (fun f => FreeRefl.homMk (F.map f))
    (fun v => by simp)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `freeReflMap_obj` / 引理 `freeReflMap_obj`

English:
lemma freeReflMap_obj
  given: (v : V)
  statement: (freeReflMap F).obj (.mk v) = .mk (F.obj v)
  proof: rfl

中文:
引理 freeReflMap_obj
  条件: (v : V)
  结论: (freeReflMap F).obj (.mk v) = .mk (F.obj v)
  证明: rfl

Depends on / 依赖: CategoryTheory, CategoryTheory.Over.pullback, MorphismProperty, MorphismProperty.Over.forget, MorphismProperty.Over.pullback, Over.forget, PreservesLimitsOfShape, forget, preservesLimitsOfShape_of_reflects_of_preserves, pullback
-/
lemma freeReflMap_obj (v : V) : (freeReflMap F).obj (.mk v) = .mk (F.obj v) := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `freeReflMap_map` / 引理 `freeReflMap_map`

English:
lemma freeReflMap_map
  given: {v w : V} (f : v ⟶ w)
  proof: rfl

中文:
引理 freeReflMap_map
  条件: {v w : V} (f : v ⟶ w)
  证明: rfl
-/
lemma freeReflMap_map {v w : V} (f : v ⟶ w) :
    (freeReflMap F).map (FreeRefl.homMk f) = FreeRefl.homMk (F.map f) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `freeReflMap_naturality` / 定理 `freeReflMap_naturality`

English:
theorem freeReflMap_naturality
  proof: Paths.ext_functor rfl (by cat_disch)

中文:
定理 freeReflMap_naturality
  证明: Paths.ext_functor rfl (by cat_disch)

Depends on / 依赖: Paths.ext_functor, cat_disch, ext_functor
-/
theorem freeReflMap_naturality
    {V W : Type*} [ReflQuiver.{v₁} V] [ReflQuiver.{v₂} W] (F : V ⥤rq W) :
    FreeRefl.quotientFunctor V ⋙ freeReflMap F =
    freeMap F.toPrefunctor ⋙ FreeRefl.quotientFunctor W :=
  Paths.ext_functor rfl (by cat_disch)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The functor sending a reflexive quiver to the free category it generates, a quotient of
its path category -/
@[simps]
/--
Definition of `freeRefl` / `freeRefl` 的定义

English:
definition freeRefl
  signature: : ReflQuiv.{v, u} ⥤ Cat.{max u v, u} where
  body: Cat.of (FreeRefl V)
  map F := (freeReflMap F).toCatHom
  map_id X := by ext1; exact FreeRefl.functor_ext (by simp) (by simp)
  map_comp {X Y Z} f g := by ext1; exact FreeRefl.functor_ext (by simp) (by simp)

中文:
定义 freeRefl
  签名: : ReflQuiv.{v, u} ⥤ Cat.{max u v, u} where
  定义体: Cat.of (FreeRefl V)
  map F := (freeReflMap F).toCatHom
  map_id X := by ext1; exact FreeRefl.functor_ext (by simp) (by simp)
  map_comp {X Y Z} f g := by ext1; exact FreeRefl.functor_ext (by simp) (by simp)

Depends on / 依赖: Cat.of, FreeRefl
-/
def freeRefl : ReflQuiv.{v, u} ⥤ Cat.{max u v, u} where
  obj V := Cat.of (FreeRefl V)
  map F := (freeReflMap F).toCatHom
  map_id X := by ext1; exact FreeRefl.functor_ext (by simp) (by simp)
  map_comp {X Y Z} f g := by ext1; exact FreeRefl.functor_ext (by simp) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `freeReflNatTrans` / `freeReflNatTrans` 的定义

English:
definition freeReflNatTrans
  signature: : ReflQuiv.forgetToQuiv ⋙ Cat.free ⟶ freeRefl where
  body: (FreeRefl.quotientFunctor V).toCatHom
  naturality v w f := by
    ext1; exact Paths.ext_functor (V := Quiv.of v) (by cat_disch) (by cat_disch)

中文:
定义 freeReflNatTrans
  签名: : ReflQuiv.forgetToQuiv ⋙ Cat.free ⟶ freeRefl where
  定义体: (FreeRefl.quotientFunctor V).toCatHom
  naturality v w f := by
    ext1; exact Paths.ext_functor (V := Quiv.of v) (by cat_disch) (by cat_disch)

Depends on / 依赖: FreeRefl, FreeRefl.quotientFunctor, quotientFunctor, toCatHom
-/
def freeReflNatTrans : ReflQuiv.forgetToQuiv ⋙ Cat.free ⟶ freeRefl where
  app V := (FreeRefl.quotientFunctor V).toCatHom
  naturality v w f := by
    ext1; exact Paths.ext_functor (V := Quiv.of v) (by cat_disch) (by cat_disch)

end Cat

namespace ReflQuiv
open Category

namespace adj

variable {V W : Type*} [ReflQuiver W] [ReflQuiver V]
  {C D : Type*} [Category* C] [Category* D]

set_option backward.isDefEq.respectTransparency false in
/-- Given a reflexive quiver `V` and a category `C`, this is the bijection
between functors `Cat.FreeRefl V ⥤ C` and refl functors `V ⥤rq C`. -/
@[simps]
/--
Definition of `homEquiv` / `homEquiv` 的定义

English:
definition homEquiv
  signature: : (Cat.FreeRefl V ⥤ C) ≃ V ⥤rq C where
  body: Cat.toFreeRefl V ⋙rq F.toReflPrefunctor
  invFun := Cat.FreeRefl.lift
  left_inv F := Cat.FreeRefl.functor_ext (by cat_disch) (by cat_disch)
  right_inv := Cat.FreeRefl.lift_spec

中文:
定义 homEquiv
  签名: : (Cat.FreeRefl V ⥤ C) ≃ V ⥤rq C where
  定义体: Cat.toFreeRefl V ⋙rq F.toReflPrefunctor
  invFun := Cat.FreeRefl.lift
  left_inv F := Cat.FreeRefl.functor_ext (by cat_disch) (by cat_disch)
  right_inv := Cat.FreeRefl.lift_spec

Depends on / 依赖: Cat.toFreeRefl, F.toReflPrefunctor, toFreeRefl, toReflPrefunctor
-/
def homEquiv : (Cat.FreeRefl V ⥤ C) ≃ V ⥤rq C where
  toFun F := Cat.toFreeRefl V ⋙rq F.toReflPrefunctor
  invFun := Cat.FreeRefl.lift
  left_inv F := Cat.FreeRefl.functor_ext (by cat_disch) (by cat_disch)
  right_inv := Cat.FreeRefl.lift_spec

set_option backward.defeqAttrib.useBackward true in
/--
lemma `homEquiv_naturality_left_symm` / 引理 `homEquiv_naturality_left_symm`

English:
lemma homEquiv_naturality_left_symm
  given: (F : V ⥤rq W) (G : W ⥤rq C)
  proof: Cat.FreeRefl.functor_ext (by simp) (by simp)

中文:
引理 homEquiv_naturality_left_symm
  条件: (F : V ⥤rq W) (G : W ⥤rq C)
  证明: Cat.FreeRefl.functor_ext (by simp) (by simp)

Depends on / 依赖: Cat.FreeRefl.functor_ext, FreeRefl, HasPushouts, IsStableUnderComposition, P.IsStableUnderComposition, functor_ext
-/
lemma homEquiv_naturality_left_symm (F : V ⥤rq W) (G : W ⥤rq C) :
    homEquiv.symm (F ⋙rq G) = Cat.freeReflMap F ⋙ homEquiv.symm G :=
  Cat.FreeRefl.functor_ext (by simp) (by simp)

/--
lemma `homEquiv_naturality_right` / 引理 `homEquiv_naturality_right`

English:
lemma homEquiv_naturality_right
  given: (F : Cat.FreeRefl V ⥤ C) (G : C ⥤ D)
  proof: rfl

中文:
引理 homEquiv_naturality_right
  条件: (F : Cat.FreeRefl V ⥤ C) (G : C ⥤ D)
  证明: rfl
-/
lemma homEquiv_naturality_right (F : Cat.FreeRefl V ⥤ C) (G : C ⥤ D) :
    homEquiv (F ⋙ G) = homEquiv F ⋙rq G.toReflPrefunctor := rfl

end adj

/--
Definition of `adj` / `adj` 的定义

English:
definition adj
  signature: : Cat.freeRefl.{max u v, u} ⊣ ReflQuiv.forget
  body: Adjunction.mkOfHomEquiv
    { homEquiv _ _ := (Cat.Hom.equivFunctor ..).trans adj.homEquiv
      homEquiv_naturality_left_symm _ _ := by ext1; exact adj.homEquiv_naturality_left_symm _ _
      homEquiv_naturality_right _ _ := adj.homEquiv_naturality_right _ _ }

@[simp]

中文:
定义 adj
  签名: : Cat.freeRefl.{max u v, u} ⊣ ReflQuiv.forget
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv _ _ := (Cat.Hom.equivFunctor ..).trans adj.homEquiv
      homEquiv_naturality_left_symm _ _ := by ext1; exact adj.homEquiv_naturality_left_symm _ _
      homEquiv_naturality_right _ _ := adj.homEquiv_naturality_right _ _ }

@[simp]

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, Cat.Hom.equivFunctor, adj.homEquiv, adj.homEquiv_naturality_left_symm, adj.homEquiv_naturality_right, equivFunctor, homEquiv, homEquiv_naturality_left_symm, homEquiv_naturality_right, mkOfHomEquiv
-/
def adj : Cat.freeRefl.{max u v, u} ⊣ ReflQuiv.forget :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ := (Cat.Hom.equivFunctor ..).trans adj.homEquiv
      homEquiv_naturality_left_symm _ _ := by ext1; exact adj.homEquiv_naturality_left_symm _ _
      homEquiv_naturality_right _ _ := adj.homEquiv_naturality_right _ _ }

@[simp]
/--
lemma `adj_unit_app` / 引理 `adj_unit_app`

English:
lemma adj_unit_app
  given: (V) [ReflQuiver V]
  proof: rfl

中文:
引理 adj_unit_app
  条件: (V) [ReflQuiver V]
  证明: rfl
-/
lemma adj_unit_app (V) [ReflQuiver V] :
    adj.unit.app (ReflQuiv.of V) = Cat.toFreeRefl V := rfl

/--
lemma `adj_counit_app` / 引理 `adj_counit_app`

English:
lemma adj_counit_app
  given: (D : Type u) [Category.{max u v} D]
  proof: rfl

中文:
引理 adj_counit_app
  条件: (D : 类型u) [Category.{max u v} D]
  证明: rfl
-/
lemma adj_counit_app (D : Type u) [Category.{max u v} D] :
    adj.counit.app (Cat.of D) = (Cat.FreeRefl.lift (𝟭rq D)).toCatHom := rfl

variable {V : Type*} [ReflQuiver V]
  {C : Type*} [Category* C]

/--
lemma `adj_homEquiv` / 引理 `adj_homEquiv`

English:
lemma adj_homEquiv
  given: (V : Type u) [ReflQuiver.{max u v} V] (C : Type u) [Category.{max u v} C]
  proof: by
  ext F
  apply Adjunction.homEquiv_unit

中文:
引理 adj_homEquiv
  条件: (V : 类型u) [ReflQuiver.{max u v} V] (C : 类型u) [Category.{max u v} C]
  证明: by
  ext F
  apply Adjunction.homEquiv_unit

Depends on / 依赖: Adjunction, Adjunction.homEquiv_unit, homEquiv_unit
-/
lemma adj_homEquiv (V : Type u) [ReflQuiver.{max u v} V] (C : Type u) [Category.{max u v} C] :
    (adj).homEquiv (.of V) (.of C) = (Cat.Hom.equivFunctor _ _).trans adj.homEquiv := by
  ext F
  apply Adjunction.homEquiv_unit

/--
lemma `adj.unit.map_app_eq` / 引理 `adj.unit.map_app_eq`

English:
lemma adj.unit.map_app_eq
  given: (V : Type u) [ReflQuiver.{max u v} V]
  proof: rfl

中文:
引理 adj.unit.map_app_eq
  条件: (V : 类型u) [ReflQuiver.{max u v} V]
  证明: rfl
-/
lemma adj.unit.map_app_eq (V : Type u) [ReflQuiver.{max u v} V] :
    (adj.unit.app (.of V)).toPrefunctor = Quiv.adj.unit.app (.of V) ⋙q
      (Cat.FreeRefl.quotientFunctor V).toPrefunctor := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `adj.counit.comp_app_eq` / 引理 `adj.counit.comp_app_eq`

English:
lemma adj.counit.comp_app_eq
  given: (C : Type u) [Category.{max u v} C]
  proof: Paths.ext_functor rfl (fun _ _ f => by
    dsimp
    simp only [adj_counit_app, composePath_toPath, comp_id, id_comp]
    apply Cat.FreeRefl.lift_map)

中文:
引理 adj.counit.comp_app_eq
  条件: (C : 类型u) [Category.{max u v} C]
  证明: Paths.ext_functor rfl (fun _ _ f => by
    dsimp
    simp only [adj_counit_app, composePath_toPath, comp_id, id_comp]
    apply Cat.FreeRefl.lift_map)

Depends on / 依赖: Cat.FreeRefl.lift_map, FreeRefl, Paths.ext_functor, adj_counit_app, comp_id, composePath_toPath, ext_functor, id_comp, lift_map
-/
lemma adj.counit.comp_app_eq (C : Type u) [Category.{max u v} C] :
    Cat.FreeRefl.quotientFunctor C ⋙ (adj.counit.app (.of C)).toFunctor =
      pathComposition _ :=
  Paths.ext_functor rfl (fun _ _ f => by
    dsimp
    simp only [adj_counit_app, composePath_toPath, comp_id, id_comp]
    apply Cat.FreeRefl.lift_map)

end ReflQuiv

end CategoryTheory
