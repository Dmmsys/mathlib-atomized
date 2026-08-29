/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Reid Barton, Joël Riou
-/
module

public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.ObjectProperty.Basic

/-!
# The full subcategory associated to a property of objects

Given a category `C` and `P : ObjectProperty C`, we define
a category structure on the type `P.FullSubcategory`
of objects in `C` satisfying `P`.

-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory

namespace ObjectProperty

variable {C : Type u} [Category.{v} C]

section

variable (P : ObjectProperty C)

/--
A subtype-like structure for full subcategories. Morphisms just ignore the property. We don't use
actual subtypes since the simp-normal form `↑X` of `X.val` does not work well for full
subcategories. -/
@[ext, stacks 001D "We do not define 'strictly full' subcategories."]
/--
Definition of `FullSubcategory` / `FullSubcategory` 的定义

English:
structure FullSubcategory
  parameters: where
  axioms and operations (2):
    - obj : C
    - property : P obj

中文:
结构 FullSubcategory
  参数: where
  公理与运算 (2 个):
    - obj : C
    - property : P obj
-/
structure FullSubcategory where
  /-- The category of which this is a full subcategory -/
  obj : C
  /-- The predicate satisfied by all objects in this subcategory -/
  property : P obj

/--
Instance `FullSubcategory.category` / 实例 `FullSubcategory.category`

English:
instance FullSubcategory.category
  signature: : Category.{v} P.FullSubcategory
  body: inferInstanceAs (Category (InducedCategory _ FullSubcategory.obj))

中文:
实例 FullSubcategory.category
  签名: : Category.{v} P.FullSubcategory
  定义体: inferInstanceAs (Category (InducedCategory _ FullSubcategory.obj))

Depends on / 依赖: Category, FullSubcategory, FullSubcategory.obj, InducedCategory
-/
instance FullSubcategory.category : Category.{v} P.FullSubcategory :=
  inferInstanceAs (Category (InducedCategory _ FullSubcategory.obj))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.Nonempty]
  signature: : Nonempty P.FullSubcategory
  body: Nonempty.intro ⟨P.arbitrary, P.prop_arbitrary⟩

@[ext]

中文:
实例 [P.Nonempty]
  签名: : Nonempty P.FullSubcategory
  定义体: Nonempty.intro ⟨P.arbitrary, P.prop_arbitrary⟩

@[ext]

Depends on / 依赖: Nonempty, Nonempty.intro, P.arbitrary, P.prop_arbitrary, arbitrary, prop_arbitrary
-/
instance [P.Nonempty] : Nonempty P.FullSubcategory :=
  Nonempty.intro ⟨P.arbitrary, P.prop_arbitrary⟩

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : P.FullSubcategory} {f g : X ⟶ Y} (h : f.hom = g.hom)
  statement: f = g
  proof: InducedCategory.hom_ext h

中文:
引理 hom_ext
  条件: {X Y : P.FullSubcategory} {f g : X ⟶ Y} (h : f.hom = g.hom)
  结论: f = g
  证明: InducedCategory.hom_ext h

Depends on / 依赖: InducedCategory, InducedCategory.hom_ext, hom_ext
-/
lemma hom_ext {X Y : P.FullSubcategory} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g :=
  InducedCategory.hom_ext h

/-- The forgetful functor from a full subcategory into the original category
("forgetting" the condition).
-/
@[implicit_reducible]
/--
Definition of `ι` / `ι` 的定义

English:
definition ι
  signature: : P.FullSubcategory ⥤ C
  body: inducedFunctor FullSubcategory.obj

@[simp]

中文:
定义 ι
  签名: : P.FullSubcategory ⥤ C
  定义体: inducedFunctor FullSubcategory.obj

@[simp]

Depends on / 依赖: FullSubcategory, FullSubcategory.obj, inducedFunctor
-/
def ι : P.FullSubcategory ⥤ C :=
  inducedFunctor FullSubcategory.obj

@[simp]
/--
theorem `ι_obj` / 定理 `ι_obj`

English:
theorem ι_obj
  given: {X}
  statement: P.ι.obj X = X.obj
  proof: rfl

@[simp]

中文:
定理 ι_obj
  条件: {X}
  结论: P.ι.obj X = X.obj
  证明: rfl

@[simp]
-/
theorem ι_obj {X} : P.ι.obj X = X.obj :=
  rfl

@[simp]
/--
theorem `ι_map` / 定理 `ι_map`

English:
theorem ι_map
  given: {X Y} {f : X ⟶ Y}
  statement: P.ι.map f = f.hom
  proof: rfl

中文:
定理 ι_map
  条件: {X Y} {f : X ⟶ Y}
  结论: P.ι.map f = f.hom
  证明: rfl
-/
theorem ι_map {X Y} {f : X ⟶ Y} : P.ι.map f = f.hom :=
  rfl

/--
lemma `prop_ι_obj` / 引理 `prop_ι_obj`

English:
lemma prop_ι_obj
  given: (X)
  statement: P (P.ι.obj X)
  proof: X.2

@[simp]

中文:
引理 prop_ι_obj
  条件: (X)
  结论: P (P.ι.obj X)
  证明: X.2

@[simp]
-/
lemma prop_ι_obj (X) : P (P.ι.obj X) := X.2

@[simp]
/--
lemma `FullSubcategory.id_hom` / 引理 `FullSubcategory.id_hom`

English:
lemma FullSubcategory.id_hom
  given: (X : P.FullSubcategory)
  proof: rfl

@[simp, reassoc]

中文:
引理 FullSubcategory.id_hom
  条件: (X : P.FullSubcategory)
  证明: rfl

@[simp, reassoc]
-/
lemma FullSubcategory.id_hom (X : P.FullSubcategory) :
    InducedCategory.Hom.hom (𝟙 X) = 𝟙 X.obj := rfl

@[simp, reassoc]
/--
lemma `FullSubcategory.comp_hom` / 引理 `FullSubcategory.comp_hom`

English:
lemma FullSubcategory.comp_hom
  given: {X Y Z : P.FullSubcategory} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
引理 FullSubcategory.comp_hom
  条件: {X Y Z : P.FullSubcategory} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
lemma FullSubcategory.comp_hom {X Y Z : P.FullSubcategory} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

variable {P} in
/-- Constructor for morphisms in a full subcategory. -/
@[simps, implicit_reducible]
/--
Definition of `homMk` / `homMk` 的定义

English:
definition homMk
  signature: {X Y : P.FullSubcategory} (f : X.obj ⟶ Y.obj)
  body: f

中文:
定义 homMk
  签名: {X Y : P.FullSubcategory} (f : X.obj ⟶ Y.obj)
  定义体: f
-/
def homMk {X Y : P.FullSubcategory} (f : X.obj ⟶ Y.obj) : X ⟶ Y where
  hom := f

variable {P} in
/--
lemma `homMk_surjective` / 引理 `homMk_surjective`

English:
lemma homMk_surjective
  given: {X Y : P.FullSubcategory}
  proof: fun f => ⟨f.hom, rfl⟩

中文:
引理 homMk_surjective
  条件: {X Y : P.FullSubcategory}
  证明: fun f => ⟨f.hom, rfl⟩

Depends on / 依赖: f.hom
-/
lemma homMk_surjective {X Y : P.FullSubcategory} :
    Function.Surjective (homMk : (X.obj ⟶ Y.obj) -> _) :=
  fun f => ⟨f.hom, rfl⟩

/--
Definition of `fullyFaithfulι` / `fullyFaithfulι` 的定义

English:
abbreviation fullyFaithfulι
  signature: :
  body: homMk _

中文:
缩写 fullyFaithfulι
  签名: :
  定义体: homMk _
-/
abbrev fullyFaithfulι :
    P.ι.FullyFaithful where
  preimage f := homMk _

/--
Instance `full_ι` / 实例 `full_ι`

English:
instance full_ι
  signature: : P.ι.Full
  body: P.fullyFaithfulι.full

中文:
实例 full_ι
  签名: : P.ι.Full
  定义体: P.fullyFaithfulι.full

Depends on / 依赖: P.fullyFaithful
-/
instance full_ι : P.ι.Full := P.fullyFaithfulι.full
/--
Instance `faithful_ι` / 实例 `faithful_ι`

English:
instance faithful_ι
  signature: : P.ι.Faithful
  body: P.fullyFaithfulι.faithful

中文:
实例 faithful_ι
  签名: : P.ι.Faithful
  定义体: P.fullyFaithfulι.faithful

Depends on / 依赖: P.fullyFaithful, faithful
-/
instance faithful_ι : P.ι.Faithful := P.fullyFaithfulι.faithful

/-- Constructor for isomorphisms in `P.FullSubcategory` when
`P : ObjectProperty C`. -/
@[simps]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {X Y : P.FullSubcategory} (e : X.obj ≅ Y.obj)
  body: homMk e.hom
  inv := homMk e.inv

中文:
定义 isoMk
  签名: {X Y : P.FullSubcategory} (e : X.obj ≅ Y.obj)
  定义体: homMk e.hom
  inv := homMk e.inv

Depends on / 依赖: e.hom
-/
def isoMk {X Y : P.FullSubcategory} (e : X.obj ≅ Y.obj) : X ≅ Y where
  hom := homMk e.hom
  inv := homMk e.inv

variable {P}

@[reassoc (attr := simp)]
/--
lemma `isoHom_inv_id_hom` / 引理 `isoHom_inv_id_hom`

English:
lemma isoHom_inv_id_hom
  given: {X Y : P.FullSubcategory} (e : X ≅ Y)
  proof: P.ι.congr_map e.hom_inv_id

@[reassoc (attr := simp)]

中文:
引理 isoHom_inv_id_hom
  条件: {X Y : P.FullSubcategory} (e : X ≅ Y)
  证明: P.ι.congr_map e.hom_inv_id

@[reassoc (attr := simp)]

Depends on / 依赖: congr_map, e.hom_inv_id, hom_inv_id
-/
lemma isoHom_inv_id_hom {X Y : P.FullSubcategory} (e : X ≅ Y) :
    e.hom.hom ≫ e.inv.hom = 𝟙 _ :=
  P.ι.congr_map e.hom_inv_id

@[reassoc (attr := simp)]
/--
lemma `isoInv_hom_id_hom` / 引理 `isoInv_hom_id_hom`

English:
lemma isoInv_hom_id_hom
  given: {X Y : P.FullSubcategory} (e : X ≅ Y)
  proof: P.ι.congr_map e.inv_hom_id

中文:
引理 isoInv_hom_id_hom
  条件: {X Y : P.FullSubcategory} (e : X ≅ Y)
  证明: P.ι.congr_map e.inv_hom_id

Depends on / 依赖: congr_map, e.inv_hom_id, inv_hom_id
-/
lemma isoInv_hom_id_hom {X Y : P.FullSubcategory} (e : X ≅ Y) :
    e.inv.hom ≫ e.hom.hom = 𝟙 _ :=
  P.ι.congr_map e.inv_hom_id

instance {X Y : P.FullSubcategory} (f : X ⟶ Y) [IsIso f] : IsIso f.hom :=
  P.ι.map_isIso f

@[simp, push ←]
/--
lemma `hom_inv` / 引理 `hom_inv`

English:
lemma hom_inv
  given: {X Y : P.FullSubcategory} (f : X ⟶ Y) [IsIso f]
  statement: (inv f).hom = inv f.hom
  proof: IsIso.eq_inv_of_hom_inv_id (P.ι.congr_map (asIso f).hom_inv_id)

中文:
引理 hom_inv
  条件: {X Y : P.FullSubcategory} (f : X ⟶ Y) [IsIso f]
  结论: (inv f).hom = inv f.hom
  证明: IsIso.eq_inv_of_hom_inv_id (P.ι.congr_map (asIso f).hom_inv_id)

Depends on / 依赖: IsIso.eq_inv_of_hom_inv_id, congr_map, eq_inv_of_hom_inv_id, hom_inv_id
-/
lemma hom_inv {X Y : P.FullSubcategory} (f : X ⟶ Y) [IsIso f] : (inv f).hom = inv f.hom :=
  IsIso.eq_inv_of_hom_inv_id (P.ι.congr_map (asIso f).hom_inv_id)

/--
lemma `isIso_hom_iff` / 引理 `isIso_hom_iff`

English:
lemma isIso_hom_iff
  given: {X Y : P.FullSubcategory} (f : X ⟶ Y)
  statement: IsIso f.hom ↔ IsIso f
  proof: ⟨fun _ => (P.isoMk (asIso f.hom)).isIso_hom, fun _ => inferInstance⟩

中文:
引理 isIso_hom_iff
  条件: {X Y : P.FullSubcategory} (f : X ⟶ Y)
  结论: IsIso f.hom ↔ IsIso f
  证明: ⟨fun _ => (P.isoMk (asIso f.hom)).isIso_hom, fun _ => inferInstance⟩

Depends on / 依赖: P.isoMk, f.hom, isIso_hom
-/
lemma isIso_hom_iff {X Y : P.FullSubcategory} (f : X ⟶ Y) : IsIso f.hom ↔ IsIso f :=
  ⟨fun _ => (P.isoMk (asIso f.hom)).isIso_hom, fun _ => inferInstance⟩

variable {P' : ObjectProperty C}

/-- If `P` and `P'` are properties of objects such that `P ≤ P'`, there is
an induced functor `P.FullSubcategory ⥤ P'.FullSubcategory`. -/
@[simps, implicit_reducible]
/--
Definition of `ιOfLE` / `ιOfLE` 的定义

English:
definition ιOfLE
  signature: (h : P <= P')
  body: ⟨X.1, h _ X.2⟩
  map f := homMk f.hom

中文:
定义 ιOfLE
  签名: (h : P <= P')
  定义体: ⟨X.1, h _ X.2⟩
  map f := homMk f.hom
-/
def ιOfLE (h : P <= P') : P.FullSubcategory ⥤ P'.FullSubcategory where
  obj X := ⟨X.1, h _ X.2⟩
  map f := homMk f.hom

/--
Definition of `fullyFaithfulιOfLE` / `fullyFaithfulιOfLE` 的定义

English:
definition fullyFaithfulιOfLE
  signature: (h : P <= P')
  body: homMk f.hom

中文:
定义 fullyFaithfulιOfLE
  签名: (h : P <= P')
  定义体: homMk f.hom

Depends on / 依赖: f.hom
-/
def fullyFaithfulιOfLE (h : P <= P') :
    (ιOfLE h).FullyFaithful where
  preimage f := homMk f.hom

/--
Instance `full_ιOfLE` / 实例 `full_ιOfLE`

English:
instance full_ιOfLE
  signature: (h : P <= P')
  body: (fullyFaithfulιOfLE h).full

中文:
实例 full_ιOfLE
  签名: (h : P <= P')
  定义体: (fullyFaithfulιOfLE h).full
-/
instance full_ιOfLE (h : P <= P') : (ιOfLE h).Full := (fullyFaithfulιOfLE h).full
/--
Instance `faithful_ιOfLE` / 实例 `faithful_ιOfLE`

English:
instance faithful_ιOfLE
  signature: (h : P <= P')
  body: (fullyFaithfulιOfLE h).faithful

中文:
实例 faithful_ιOfLE
  签名: (h : P <= P')
  定义体: (fullyFaithfulιOfLE h).faithful

Depends on / 依赖: faithful
-/
instance faithful_ιOfLE (h : P <= P') : (ιOfLE h).Faithful := (fullyFaithfulιOfLE h).faithful

/--
Definition of `ιOfLECompιIso` / `ιOfLECompιIso` 的定义

English:
definition ιOfLECompιIso
  signature: (h : P <= P')
  body: Iso.refl _

中文:
定义 ιOfLECompιIso
  签名: (h : P <= P')
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def ιOfLECompιIso (h : P <= P') : ιOfLE h ⋙ P'.ι ≅ P.ι := Iso.refl _

end

section lift

variable {D : Type u'} [Category.{v'} D] (P Q : ObjectProperty D)
  (F : C ⥤ D) (hF : forall X, P (F.obj X))

/-- A functor which maps objects to objects satisfying a certain property induces a lift through
    the full subcategory of objects satisfying that property. -/
@[simps, implicit_reducible]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : C ⥤ FullSubcategory P where
  body: ⟨F.obj X, hF X⟩
  map f := homMk (F.map f)

中文:
定义 lift
  签名: : C ⥤ FullSubcategory P where
  定义体: ⟨F.obj X, hF X⟩
  map f := homMk (F.map f)

Depends on / 依赖: F.obj
-/
def lift : C ⥤ FullSubcategory P where
  obj X := ⟨F.obj X, hF X⟩
  map f := homMk (F.map f)

/--
Definition of `liftCompιIso` / `liftCompιIso` 的定义

English:
definition liftCompιIso
  signature: : P.lift F hF ⋙ P.ι ≅ F
  body: Iso.refl _

中文:
定义 liftCompιIso
  签名: : P.lift F hF ⋙ P.ι ≅ F
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def liftCompιIso : P.lift F hF ⋙ P.ι ≅ F := Iso.refl _

/--
lemma `ι_obj_lift_obj` / 引理 `ι_obj_lift_obj`

English:
lemma ι_obj_lift_obj
  given: (X : C)
  proof: rfl

中文:
引理 ι_obj_lift_obj
  条件: (X : C)
  证明: rfl
-/
lemma ι_obj_lift_obj (X : C) :
    P.ι.obj ((P.lift F hF).obj X) = F.obj X := rfl

/--
lemma `ι_obj_lift_map` / 引理 `ι_obj_lift_map`

English:
lemma ι_obj_lift_map
  given: {X Y : C} (f : X ⟶ Y)
  proof: rfl

中文:
引理 ι_obj_lift_map
  条件: {X Y : C} (f : X ⟶ Y)
  证明: rfl
-/
lemma ι_obj_lift_map {X Y : C} (f : X ⟶ Y) :
    P.ι.map ((P.lift F hF).map f) = F.map f := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.Faithful]
  signature: : (P.lift F hF).Faithful
  body: Functor.Faithful.of_comp_iso (P.liftCompιIso F hF)

中文:
实例 [F.Faithful]
  签名: : (P.lift F hF).Faithful
  定义体: Functor.Faithful.of_comp_iso (P.liftCompιIso F hF)

Depends on / 依赖: Faithful, Functor, Functor.Faithful.of_comp_iso, P.liftComp, of_comp_iso
-/
instance [F.Faithful] : (P.lift F hF).Faithful :=
  Functor.Faithful.of_comp_iso (P.liftCompιIso F hF)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.Full]
  signature: : (P.lift F hF).Full
  body: Functor.Full.of_comp_faithful_iso (P.liftCompιIso F hF)

中文:
实例 [F.Full]
  签名: : (P.lift F hF).Full
  定义体: Functor.Full.of_comp_faithful_iso (P.liftCompιIso F hF)

Depends on / 依赖: Functor, Functor.Full.of_comp_faithful_iso, P.liftComp, of_comp_faithful_iso
-/
instance [F.Full] : (P.lift F hF).Full :=
  Functor.Full.of_comp_faithful_iso (P.liftCompιIso F hF)

variable {Q}

/--
Definition of `liftCompιOfLEIso` / `liftCompιOfLEIso` 的定义

English:
definition liftCompιOfLEIso
  signature: (h : P <= Q)
  body: Iso.refl _

中文:
定义 liftCompιOfLEIso
  签名: (h : P <= Q)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def liftCompιOfLEIso (h : P <= Q) :
    P.lift F hF ⋙ ιOfLE h ≅ Q.lift F (fun X => h _ (hF X)) := Iso.refl _

end lift

end ObjectProperty

end CategoryTheory
