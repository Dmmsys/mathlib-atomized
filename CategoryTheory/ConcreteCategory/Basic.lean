/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johannes Hölzl, Reid Barton, Sean Leather, Yury Kudryashov, Anne Baanen,
  Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Concrete categories

A concrete category is a category `C` where the objects and morphisms correspond with types and
(bundled) functions between these types. We define concrete categories using
`class ConcreteCategory`. To convert an object to a type, write `ToType`. To convert a morphism
to a (bundled) function, write `hom`.

Each concrete category `C` comes with a canonical faithful functor `forget C : C ⥤ Type*`,
see the file `Mathlib.CategoryTheory.ConcreteCategory.Forget`

## Implementation notes

We do not use `CoeSort` to convert objects in a concrete category to types, since this would lead
to elaboration mismatches between results taking a `[ConcreteCategory C]` instance and specific
types `C` that hold a `ConcreteCategory C` instance: the first gets a literal `CoeSort.coe` and
the second gets unfolded to the actual `coe` field.

`ToType` and `ToHom` are `abbrev`s so that we do not need to copy over instances such as `Ring`
or `RingHomClass` respectively.

## References

See [Ahrens and Lumsdaine, *Displayed Categories*][ahrens2017] for
related work.
-/

@[expose] public section


assert_not_exists CategoryTheory.CommSq CategoryTheory.Adjunction

universe w w' v v' v'' u u' u''

namespace CategoryTheory

section ConcreteCategory

/--
Definition of `ConcreteCategory` / `ConcreteCategory` 的定义

English:
class ConcreteCategory
  parameters: (C : Type u) [Category.{v} C]
  axioms and operations (6):
    - (hom : forall {X Y}, (X ⟶ Y) -> FC X Y)
    - (ofHom : forall {X Y}, FC X Y -> (X ⟶ Y))
    - (hom_ofHom : forall {X Y} (f : FC X Y), hom (ofHom f) = f  [default: by cat_disch)]
    - (ofHom_hom : forall {X Y} (f : X ⟶ Y), ofHom (hom f) = f  [default: by cat_disch)]
    - (id_apply : forall {X} (x : CC X), hom (𝟙 X) x = x  [default: by cat_disch)]
    - (comp_apply : forall {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) (x : CC X), hom (f ≫ g) x = hom g (hom f x)  [default: by cat_disch)]

中文:
类 ConcreteCategory
  参数: (C : 类型u) [Category.{v} C]
  公理与运算 (6 个):
    - (hom : 对任意 {X Y}, (X ⟶ Y) -> FC X Y)
    - (ofHom : 对任意 {X Y}, FC X Y -> (X ⟶ Y))
    - (hom_ofHom : 对任意 {X Y} (f : FC X Y), hom (ofHom f) = f  [默认: by cat_disch)]
    - (ofHom_hom : 对任意 {X Y} (f : X ⟶ Y), ofHom (hom f) = f  [默认: by cat_disch)]
    - (id_apply : 对任意 {X} (x : CC X), hom (𝟙 X) x = x  [默认: by cat_disch)]
    - (comp_apply : 对任意 {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) (x : CC X), hom (f ≫ g) x = hom g (hom f x)  [默认: by cat_disch)]

Depends on / 依赖: PreservesLimitsOfSize0, PreservesLimitsOfSize0.preservesFiniteLimits, cat_disch, comp_apply, id_apply, ofHom_hom, preservesFiniteLimits
-/
class ConcreteCategory (C : Type u) [Category.{v} C]
    (FC : outParam <| C -> C -> Type*) {CC : outParam <| C -> Type w}
    [outParam <| forall X Y, FunLike (FC X Y) (CC X) (CC Y)] where
  /-- Convert a morphism of `C` to a bundled function. -/
  (hom : forall {X Y}, (X ⟶ Y) -> FC X Y)
  /-- Convert a bundled function to a morphism of `C`. -/
  (ofHom : forall {X Y}, FC X Y -> (X ⟶ Y))
  (hom_ofHom : forall {X Y} (f : FC X Y), hom (ofHom f) = f := by cat_disch)
  (ofHom_hom : forall {X Y} (f : X ⟶ Y), ofHom (hom f) = f := by cat_disch)
  (id_apply : forall {X} (x : CC X), hom (𝟙 X) x = x := by cat_disch)
  (comp_apply : forall {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) (x : CC X),
    hom (f ≫ g) x = hom g (hom f x) := by cat_disch)

attribute [simp] ConcreteCategory.hom_ofHom ConcreteCategory.ofHom_hom

variable {C : Type u} [Category.{v} C] {FC : C -> C -> Type*} {CC : C -> Type w}
variable [forall X Y, FunLike (FC X Y) (CC X) (CC Y)]

/-- `ToType X` converts the object `X` of the concrete category `C` to a type.

This is an `abbrev` so that instances on `X` (e.g. `Ring`) do not need to be redeclared.
-/
@[nolint unusedArguments] -- Need the instance to trigger unification that finds `CC`.
/--
Definition of `ToType` / `ToType` 的定义

English:
abbreviation ToType
  signature: [ConcreteCategory C FC]
  body: CC

中文:
缩写 ToType
  签名: [ConcreteCategory C FC]
  定义体: CC

Depends on / 依赖: PreservesLimits, PreservesLimits.preservesFiniteLimits, preservesFiniteLimits
-/
abbrev ToType [ConcreteCategory C FC] := CC

/-- `ToHom X Y` is the type of (bundled) functions between objects `X Y : C`.

This is an `abbrev` so that instances (e.g. `RingHomClass`) do not need to be redeclared.
-/
@[nolint unusedArguments] -- Need the instance to trigger unification that finds `FC`.
/--
Definition of `ToHom` / `ToHom` 的定义

English:
abbreviation ToHom
  signature: [ConcreteCategory C FC]
  body: FC

中文:
缩写 ToHom
  签名: [ConcreteCategory C FC]
  定义体: FC
-/
abbrev ToHom [ConcreteCategory C FC] := FC

variable [ConcreteCategory C FC]

namespace ConcreteCategory

/-- We can apply morphisms of concrete categories by first casting them down
to the base functions.
-/
instance {X Y : C} : CoeFun (X ⟶ Y) (fun _ => ToType X -> ToType Y) where
  coe f := hom f

/-- A non-instance `FunLike` instance on `X ⟶ Y`. -/
@[deprecated "No replacement" (since := "2026-04-23")]
/--
Definition of `instFunLike` / `instFunLike` 的定义

English:
abbreviation instFunLike
  signature: {X Y : C}
  body: f
  coe_injective f g h := by
    rw [← ofHom_hom f]; rw [← ofHom_hom g]
    simp_all

@[deprecated (since := "2026-04-03")] alias _root_.CategoryTheory.HasForget.instFunLike :=
  instFunLike

中文:
缩写 instFunLike
  签名: {X Y : C}
  定义体: f
  coe_injective f g h := by
    rw [← ofHom_hom f]; rw [← ofHom_hom g]
    simp_all

@[deprecated (since := "2026-04-03")] alias _root_.CategoryTheory.HasForget.instFunLike :=
  instFunLike
-/
abbrev instFunLike {X Y : C} :
    FunLike (X ⟶ Y) (ToType X) (ToType Y) where
  coe f := f
  coe_injective f g h := by
    rw [← ofHom_hom f]; rw [← ofHom_hom g]
    simp_all

@[deprecated (since := "2026-04-03")] alias _root_.CategoryTheory.HasForget.instFunLike :=
  instFunLike

/--
Definition of `homEquiv` / `homEquiv` 的定义

English:
definition homEquiv
  signature: {X Y : C}
  body: hom
  invFun := ofHom
  left_inv := ofHom_hom
  right_inv := hom_ofHom

中文:
定义 homEquiv
  签名: {X Y : C}
  定义体: hom
  invFun := ofHom
  left_inv := ofHom_hom
  right_inv := hom_ofHom
-/
def homEquiv {X Y : C} : (X ⟶ Y) ≃ ToHom X Y where
  toFun := hom
  invFun := ofHom
  left_inv := ofHom_hom
  right_inv := hom_ofHom

/--
lemma `hom_bijective` / 引理 `hom_bijective`

English:
lemma hom_bijective
  given: {X Y : C}
  statement: Function.Bijective (hom : (X ⟶ Y) -> ToHom X Y)
  proof: homEquiv.bijective

中文:
引理 hom_bijective
  条件: {X Y : C}
  结论: Function.Bijective (hom : (X ⟶ Y) -> ToHom X Y)
  证明: homEquiv.bijective

Depends on / 依赖: Finite, bijective, homEquiv, homEquiv.bijective
-/
lemma hom_bijective {X Y : C} : Function.Bijective (hom : (X ⟶ Y) -> ToHom X Y) :=
  homEquiv.bijective

/--
lemma `hom_injective` / 引理 `hom_injective`

English:
lemma hom_injective
  given: {X Y : C}
  statement: Function.Injective (hom : (X ⟶ Y) -> ToHom X Y)
  proof: hom_bijective.injective

中文:
引理 hom_injective
  条件: {X Y : C}
  结论: Function.Injective (hom : (X ⟶ Y) -> ToHom X Y)
  证明: hom_bijective.injective

Depends on / 依赖: hom_bijective, hom_bijective.injective, injective
-/
lemma hom_injective {X Y : C} : Function.Injective (hom : (X ⟶ Y) -> ToHom X Y) :=
  hom_bijective.injective

/--
lemma `hom_surjective` / 引理 `hom_surjective`

English:
lemma hom_surjective
  given: {X Y : C}
  statement: Function.Surjective (hom : (X ⟶ Y) -> ToHom X Y)
  proof: hom_bijective.surjective

中文:
引理 hom_surjective
  条件: {X Y : C}
  结论: Function.Surjective (hom : (X ⟶ Y) -> ToHom X Y)
  证明: hom_bijective.surjective

Depends on / 依赖: hom_bijective, hom_bijective.surjective, surjective
-/
lemma hom_surjective {X Y : C} : Function.Surjective (hom : (X ⟶ Y) -> ToHom X Y) :=
  hom_bijective.surjective

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {X Y : C} {f g : X ⟶ Y} (h : hom f = hom g)
  statement: f = g
  proof: hom_injective h

中文:
引理 ext
  条件: {X Y : C} {f g : X ⟶ Y} (h : hom f = hom g)
  结论: f = g
  证明: hom_injective h
-/
@[ext] lemma ext {X Y : C} {f g : X ⟶ Y} (h : hom f = hom g) : f = g :=
  hom_injective h

/--
lemma `coe_ext` / 引理 `coe_ext`

English:
lemma coe_ext
  given: {X Y : C} {f g : X ⟶ Y} (h : ⇑(hom f) = ⇑(hom g))
  statement: f = g
  proof: ext (DFunLike.coe_injective h)

中文:
引理 coe_ext
  条件: {X Y : C} {f g : X ⟶ Y} (h : ⇑(hom f) = ⇑(hom g))
  结论: f = g
  证明: ext (DFunLike.coe_injective h)

Depends on / 依赖: DFunLike, DFunLike.coe_injective, Finite, ReflectsFiniteProducts, coe_injective
-/
lemma coe_ext {X Y : C} {f g : X ⟶ Y} (h : ⇑(hom f) = ⇑(hom g)) : f = g :=
  ext (DFunLike.coe_injective h)

/--
lemma `ext_apply` / 引理 `ext_apply`

English:
lemma ext_apply
  given: {X Y : C} {f g : X ⟶ Y} (h : forall x, f x = g x)
  statement: f = g
  proof: ext (DFunLike.ext _ _ h)

中文:
引理 ext_apply
  条件: {X Y : C} {f g : X ⟶ Y} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: ext (DFunLike.ext _ _ h)

Depends on / 依赖: DFunLike, DFunLike.ext
-/
lemma ext_apply {X Y : C} {f g : X ⟶ Y} (h : forall x, f x = g x) : f = g :=
  ext (DFunLike.ext _ _ h)

/-- In any concrete category, we can test equality of morphisms by pointwise evaluations. -/
@[ext low]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  given: {X Y : C} (f g : X ⟶ Y) (w : forall x, f x = g x)
  statement: f = g
  proof: ext (DFunLike.ext _ _ w)

中文:
定理 hom_ext
  条件: {X Y : C} (f g : X ⟶ Y) (w : 对任意 x, f x = g x)
  结论: f = g
  证明: ext (DFunLike.ext _ _ w)

Depends on / 依赖: DFunLike, DFunLike.ext, ReflectsLimitsOfSize
-/
theorem hom_ext {X Y : C} (f g : X ⟶ Y) (w : forall x, f x = g x) : f = g :=
  ext (DFunLike.ext _ _ w)

/--
theorem `congr_hom` / 定理 `congr_hom`

English:
theorem congr_hom
  given: {X Y : C} {f g : X ⟶ Y} (h : f = g) (x : ToType X)
  statement: f x = g x
  proof: congrFun (congrArg (fun k : X ⟶ Y => (k : ToType X -> ToType Y)) h) x

中文:
定理 congr_hom
  条件: {X Y : C} {f g : X ⟶ Y} (h : f = g) (x : ToType X)
  结论: f x = g x
  证明: congrFun (congrArg (fun k : X ⟶ Y => (k : ToType X -> ToType Y)) h) x

Depends on / 依赖: ToType
-/
theorem congr_hom {X Y : C} {f g : X ⟶ Y} (h : f = g) (x : ToType X) : f x = g x :=
  congrFun (congrArg (fun k : X ⟶ Y => (k : ToType X -> ToType Y)) h) x

/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  given: {X : C}
  statement: (𝟙 X : ToType X -> ToType X) = id
  proof: by
  ext
  simp [ConcreteCategory.id_apply]

中文:
定理 coe_id
  条件: {X : C}
  结论: (𝟙 X : ToType X -> ToType X) = id
  证明: by
  ext
  simp [ConcreteCategory.id_apply]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.id_apply, id_apply
-/
theorem coe_id {X : C} : (𝟙 X : ToType X -> ToType X) = id := by
  ext
  simp [ConcreteCategory.id_apply]

/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  statement: (f ≫ g : ToType X -> ToType Z) = g ∘ f
  proof: by
  ext
  simp [ConcreteCategory.comp_apply]

中文:
定理 coe_comp
  条件: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  结论: (f ≫ g : ToType X -> ToType Z) = g ∘ f
  证明: by
  ext
  simp [ConcreteCategory.comp_apply]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, comp_apply
-/
theorem coe_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : ToType X -> ToType Z) = g ∘ f := by
  ext
  simp [ConcreteCategory.comp_apply]

/--
theorem `_root_.CategoryTheory.id_apply` / 定理 `_root_.CategoryTheory.id_apply`

English:
theorem _root_.CategoryTheory.id_apply
  given: {X : C} (x : ToType X)
  proof: by
  simp [ConcreteCategory.id_apply _]

中文:
定理 _root_.CategoryTheory.id_apply
  条件: {X : C} (x : ToType X)
  证明: by
  simp [ConcreteCategory.id_apply _]
-/
@[simp] theorem _root_.CategoryTheory.id_apply {X : C} (x : ToType X) :
    𝟙 X x = x := by
  simp [ConcreteCategory.id_apply _]

/--
theorem `_root_.CategoryTheory.comp_apply` / 定理 `_root_.CategoryTheory.comp_apply`

English:
theorem _root_.CategoryTheory.comp_apply
  statement: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: by
  simp [ConcreteCategory.comp_apply]

@[deprecated (since := "2026-02-06")] alias _root_.CategoryTheory.comp_apply' :=
  _root_.CategoryTheory.comp_apply

中文:
定理 _root_.CategoryTheory.comp_apply
  结论: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: by
  simp [ConcreteCategory.comp_apply]

@[deprecated (since := "2026-02-06")] alias _root_.CategoryTheory.comp_apply' :=
  _root_.CategoryTheory.comp_apply
-/
@[simp] theorem _root_.CategoryTheory.comp_apply {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : ToType X) : (f ≫ g) x = g (f x) := by
  simp [ConcreteCategory.comp_apply]

@[deprecated (since := "2026-02-06")] alias _root_.CategoryTheory.comp_apply' :=
  _root_.CategoryTheory.comp_apply

/--
theorem `congr_arg` / 定理 `congr_arg`

English:
theorem congr_arg
  given: {X Y : C} (f : X ⟶ Y) {x x' : ToType X} (h : x = x')
  statement: f x = f x'
  proof: congrArg (f : ToType X -> ToType Y) h

中文:
定理 congr_arg
  条件: {X Y : C} (f : X ⟶ Y) {x x' : ToType X} (h : x = x')
  结论: f x = f x'
  证明: congrArg (f : ToType X -> ToType Y) h

Depends on / 依赖: ToType
-/
theorem congr_arg {X Y : C} (f : X ⟶ Y) {x x' : ToType X} (h : x = x') : f x = f x' :=
  congrArg (f : ToType X -> ToType Y) h

end ConcreteCategory

/--
theorem `hom_id` / 定理 `hom_id`

English:
theorem hom_id
  given: {X : C}
  statement: (𝟙 X : ToType X -> ToType X) = id
  proof: by
  ext
  simp

中文:
定理 hom_id
  条件: {X : C}
  结论: (𝟙 X : ToType X -> ToType X) = id
  证明: by
  ext
  simp
-/
theorem hom_id {X : C} : (𝟙 X : ToType X -> ToType X) = id := by
  ext
  simp

/--
theorem `hom_comp` / 定理 `hom_comp`

English:
theorem hom_comp
  given: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  statement: (f ≫ g : ToType X -> ToType Z) = g ∘ f
  proof: by
  ext
  simp

中文:
定理 hom_comp
  条件: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  结论: (f ≫ g : ToType X -> ToType Z) = g ∘ f
  证明: by
  ext
  simp
-/
theorem hom_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : ToType X -> ToType Z) = g ∘ f := by
  ext
  simp

open ConcreteCategory

set_option backward.isDefEq.respectTransparency false in
/--
Instance `InducedCategory.concreteCategory` / 实例 `InducedCategory.concreteCategory`

English:
instance InducedCategory.concreteCategory
  signature: {C : Type u} {D : Type u'} [Category.{v'} D]
  body: hom f.hom
  ofHom g := homMk (ofHom g)
  hom_ofHom _ := hom_ofHom _
  ofHom_hom _ := by ext; simp [ofHom_hom]
  comp_apply _ _ _ := ConcreteCategory.comp_apply _ _ _
  id_apply _ := ConcreteCategory.id_apply _

中文:
实例 InducedCategory.concreteCategory
  签名: {C : 类型u} {D : 类型u'} [Category.{v'} D]
  定义体: hom f.hom
  ofHom g := homMk (ofHom g)
  hom_ofHom _ := hom_ofHom _
  ofHom_hom _ := by ext; simp [ofHom_hom]
  comp_apply _ _ _ := ConcreteCategory.comp_apply _ _ _
  id_apply _ := ConcreteCategory.id_apply _

Depends on / 依赖: f.hom, preservesColimitsOfShapeOfPreservesFiniteColimits
-/
instance InducedCategory.concreteCategory {C : Type u} {D : Type u'} [Category.{v'} D]
    {FD : D -> D -> Type*} {CD : D -> Type w} [forall X Y, FunLike (FD X Y) (CD X) (CD Y)]
    [ConcreteCategory.{w} D FD] (f : C -> D) :
    ConcreteCategory (InducedCategory D f) (fun X Y => FD (f X) (f Y)) where
  hom f := hom f.hom
  ofHom g := homMk (ofHom g)
  hom_ofHom _ := hom_ofHom _
  ofHom_hom _ := by ext; simp [ofHom_hom]
  comp_apply _ _ _ := ConcreteCategory.comp_apply _ _ _
  id_apply _ := ConcreteCategory.id_apply _

/--
Instance `ObjectProperty.FullSubcategory.concreteCategory` / 实例 `ObjectProperty.FullSubcategory.concreteCategory`

English:
instance ObjectProperty.FullSubcategory.concreteCategory
  signature: {C : Type u} [Category.{v} C]
  body: hom f.hom
  ofHom g := homMk (ofHom g)
  hom_ofHom _ := hom_ofHom _
  ofHom_hom _ := by ext; simp [ofHom_hom]
  comp_apply _ _ _ := ConcreteCategory.comp_apply _ _ _
  id_apply _ := ConcreteCategory.id_apply _

@[deprecated (since := "2026-04-18")] alias FullSubcategory.concreteCategory :=
  ObjectP

中文:
实例 ObjectProperty.FullSubcategory.concreteCategory
  签名: {C : 类型u} [Category.{v} C]
  定义体: hom f.hom
  ofHom g := homMk (ofHom g)
  hom_ofHom _ := hom_ofHom _
  ofHom_hom _ := by ext; simp [ofHom_hom]
  comp_apply _ _ _ := ConcreteCategory.comp_apply _ _ _
  id_apply _ := ConcreteCategory.id_apply _

@[deprecated (since := "2026-04-18")] alias FullSubcategory.concreteCategory :=
  ObjectP

Depends on / 依赖: f.hom
-/
instance ObjectProperty.FullSubcategory.concreteCategory {C : Type u} [Category.{v} C]
    {FC : C -> C -> Type*} {CC : C -> Type w} [forall X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory.{w} C FC]
    (P : ObjectProperty C) : ConcreteCategory P.FullSubcategory (fun X Y => FC X.1 Y.1) where
  hom f := hom f.hom
  ofHom g := homMk (ofHom g)
  hom_ofHom _ := hom_ofHom _
  ofHom_hom _ := by ext; simp [ofHom_hom]
  comp_apply _ _ _ := ConcreteCategory.comp_apply _ _ _
  id_apply _ := ConcreteCategory.id_apply _

@[deprecated (since := "2026-04-18")] alias FullSubcategory.concreteCategory :=
  ObjectProperty.FullSubcategory.concreteCategory

end ConcreteCategory

variable {C : Type u} [Category.{v} C]
variable {D : Type*} [Category* D] {FD : outParam <| D -> D -> Type*}
    {CD : outParam <| D -> Type w}
    [outParam <| forall X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{w} D FD]

-- TODO: generate this lemma with the `elementwise` attribute.
@[simp]
/--
lemma `NatTrans.naturality_apply` / 引理 `NatTrans.naturality_apply`

English:
lemma NatTrans.naturality_apply
  statement: {F G : C ⥤ D} (φ : F ⟶ G) {X Y : C} (f : X ⟶ Y)
  proof: by
  simp [← CategoryTheory.comp_apply]

中文:
引理 NatTrans.naturality_apply
  结论: {F G : C ⥤ D} (φ : F ⟶ G) {X Y : C} (f : X ⟶ Y)
  证明: by
  simp [← CategoryTheory.comp_apply]

Depends on / 依赖: CategoryTheory, CategoryTheory.comp_apply, PreservesColimitsOfSize0, PreservesColimitsOfSize0.preservesFiniteColimits, comp_apply, preservesFiniteColimits
-/
lemma NatTrans.naturality_apply {F G : C ⥤ D} (φ : F ⟶ G) {X Y : C} (f : X ⟶ Y)
    (x : ToType (F.obj X)) :
    φ.app Y (F.map f x) = G.map f (φ.app X x) := by
  simp [← CategoryTheory.comp_apply]

end CategoryTheory
