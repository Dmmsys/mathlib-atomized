/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Adam Topaz
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Data.Finite.Prod

/-!
# The category of finite types.

We define the category of finite types, denoted `FintypeCat` as
the full subcategory of types with a `Finite` instance.

We also define `FintypeCat.Skeleton`, the standard skeleton of `FintypeCat` whose objects
are `Fin n` for `n : ℕ`. We prove that the obvious inclusion functor
`FintypeCat.Skeleton ⥤ FintypeCat` is an equivalence of categories in
`FintypeCat.Skeleton.equivalence`.
We prove that `FintypeCat.Skeleton` is a skeleton of `FintypeCat` in `FintypeCat.isSkeleton`.
-/

@[expose] public section

open CategoryTheory

/--
Definition of `FintypeCat` / `FintypeCat` 的定义

English:
abbreviation FintypeCat
  body: ObjectProperty.FullSubcategory (C := Type*) Finite

中文:
缩写 FintypeCat
  定义体: ObjectProperty.FullSubcategory (C := Type*) Finite

Depends on / 依赖: Finite, FullSubcategory, ObjectProperty, ObjectProperty.FullSubcategory
-/
abbrev FintypeCat := ObjectProperty.FullSubcategory (C := Type*) Finite

namespace FintypeCat

/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (X : Type*) [Finite X]
  body: ⟨X, inferInstance⟩

中文:
缩写 of
  签名: (X : 类型) [Finite X]
  定义体: ⟨X, inferInstance⟩
-/
abbrev of (X : Type*) [Finite X] : FintypeCat :=
  ⟨X, inferInstance⟩

/--
Instance `instCoeSort` / 实例 `instCoeSort`

English:
instance instCoeSort
  signature: : CoeSort FintypeCat Type*
  body: ⟨fun X => X.obj⟩

中文:
实例 instCoeSort
  签名: : CoeSort FintypeCat 类型
  定义体: ⟨fun X => X.obj⟩

Depends on / 依赖: X.obj
-/
instance instCoeSort : CoeSort FintypeCat Type* :=
  ⟨fun X => X.obj⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited FintypeCat
  body: ⟨of PEmpty⟩

中文:
实例 :
  签名: Inhabited FintypeCat
  定义体: ⟨of PEmpty⟩

Depends on / 依赖: PEmpty
-/
instance : Inhabited FintypeCat :=
  ⟨of PEmpty⟩

instance {X : FintypeCat} : Finite X :=
  X.property

/-- A `Fintype` instance on objects on `FintypeCat`, that should be turned on as needed.
Prefer the `Finite` instance if possible. -/
@[instance_reducible]
/--
Definition of `fintype` / `fintype` 的定义

English:
definition fintype
  signature: {X : FintypeCat}
  body: Fintype.ofFinite X.obj

中文:
定义 fintype
  签名: {X : FintypeCat}
  定义体: Fintype.ofFinite X.obj

Depends on / 依赖: Fintype, Fintype.ofFinite, X.obj, ofFinite
-/
noncomputable def fintype {X : FintypeCat} : Fintype X :=
  Fintype.ofFinite X.obj

/-- The fully faithful embedding of `FintypeCat` into the category of types. -/
@[simps!]
/--
Definition of `incl` / `incl` 的定义

English:
abbreviation incl
  signature: : FintypeCat ⥤ Type*
  body: ObjectProperty.ι _

中文:
缩写 incl
  签名: : FintypeCat ⥤ 类型
  定义体: ObjectProperty.ι _

Depends on / 依赖: ObjectProperty
-/
abbrev incl : FintypeCat ⥤ Type* := ObjectProperty.ι _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: incl.Full
  body: ObjectProperty.full_ι _

中文:
实例 :
  签名: incl.Full
  定义体: ObjectProperty.full_ι _

Depends on / 依赖: ObjectProperty, ObjectProperty.full_
-/
instance : incl.Full := ObjectProperty.full_ι _
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: incl.Faithful
  body: ObjectProperty.faithful_ι _

example : ConcreteCategory FintypeCat
    (fun X Y => TypeCat.Fun X.obj Y.obj) :=
  inferInstance

中文:
实例 :
  签名: incl.Faithful
  定义体: ObjectProperty.faithful_ι _

example : ConcreteCategory FintypeCat
    (fun X Y => TypeCat.Fun X.obj Y.obj) :=
  inferInstance

Depends on / 依赖: ObjectProperty, ObjectProperty.faithful_
-/
instance : incl.Faithful := ObjectProperty.faithful_ι _

example : ConcreteCategory FintypeCat
    (fun X Y => TypeCat.Fun X.obj Y.obj) :=
  inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget FintypeCat).Full
  body: inferInstanceAs FintypeCat.incl.Full

@[simp]

中文:
实例 :
  签名: (forget FintypeCat).Full
  定义体: inferInstanceAs FintypeCat.incl.Full

@[simp]

Depends on / 依赖: FintypeCat, FintypeCat.incl.Full
-/
instance : (forget FintypeCat).Full := inferInstanceAs FintypeCat.incl.Full

@[simp]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (X : FintypeCat) (x : X)
  statement: (𝟙 X : X -> X) x = x
  proof: rfl

@[simp]

中文:
定理 id_apply
  条件: (X : FintypeCat) (x : X)
  结论: (𝟙 X : X -> X) x = x
  证明: rfl

@[simp]
-/
theorem id_apply (X : FintypeCat) (x : X) : (𝟙 X : X -> X) x = x :=
  rfl

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: {X Y Z : FintypeCat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  statement: (f ≫ g) x = g (f x)
  proof: rfl

@[simp]

中文:
定理 comp_apply
  条件: {X Y Z : FintypeCat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  结论: (f ≫ g) x = g (f x)
  证明: rfl

@[simp]
-/
theorem comp_apply {X Y Z : FintypeCat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x) :=
  rfl

@[simp]
/--
lemma `hom_apply` / 引理 `hom_apply`

English:
lemma hom_apply
  given: {X Y : FintypeCat} (f : X ⟶ Y) (x : X)
  proof: rfl

中文:
引理 hom_apply
  条件: {X Y : FintypeCat} (f : X ⟶ Y) (x : X)
  证明: rfl
-/
lemma hom_apply {X Y : FintypeCat} (f : X ⟶ Y) (x : X) :
    f.hom x = f x := rfl

-- Isn't `@[simp]` because `simp` can prove it after importing `Mathlib.CategoryTheory.Elementwise`.
/--
lemma `hom_inv_id_apply` / 引理 `hom_inv_id_apply`

English:
lemma hom_inv_id_apply
  given: {X Y : FintypeCat} (f : X ≅ Y) (x : X)
  statement: f.inv (f.hom x) = x
  proof: ConcreteCategory.congr_hom f.hom_inv_id x

中文:
引理 hom_inv_id_apply
  条件: {X Y : FintypeCat} (f : X ≅ Y) (x : X)
  结论: f.inv (f.hom x) = x
  证明: ConcreteCategory.congr_hom f.hom_inv_id x

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, congr_hom, f.hom_inv_id, hom_inv_id
-/
lemma hom_inv_id_apply {X Y : FintypeCat} (f : X ≅ Y) (x : X) : f.inv (f.hom x) = x :=
  ConcreteCategory.congr_hom f.hom_inv_id x

-- Isn't `@[simp]` because `simp` can prove it after importing `Mathlib.CategoryTheory.Elementwise`.
/--
lemma `inv_hom_id_apply` / 引理 `inv_hom_id_apply`

English:
lemma inv_hom_id_apply
  given: {X Y : FintypeCat} (f : X ≅ Y) (y : Y)
  statement: f.hom (f.inv y) = y
  proof: ConcreteCategory.congr_hom f.inv_hom_id y

@[ext]

中文:
引理 inv_hom_id_apply
  条件: {X Y : FintypeCat} (f : X ≅ Y) (y : Y)
  结论: f.hom (f.inv y) = y
  证明: ConcreteCategory.congr_hom f.inv_hom_id y

@[ext]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, congr_hom, f.inv_hom_id, inv_hom_id
-/
lemma inv_hom_id_apply {X Y : FintypeCat} (f : X ≅ Y) (y : Y) : f.hom (f.inv y) = y :=
  ConcreteCategory.congr_hom f.inv_hom_id y

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : FintypeCat} (f g : X ⟶ Y) (h : forall x, f x = g x)
  statement: f = g
  proof: ConcreteCategory.hom_ext _ _ h

中文:
引理 hom_ext
  条件: {X Y : FintypeCat} (f g : X ⟶ Y) (h : 对任意 x, f x = g x)
  结论: f = g
  证明: ConcreteCategory.hom_ext _ _ h

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ext, hom_ext
-/
lemma hom_ext {X Y : FintypeCat} (f g : X ⟶ Y) (h : forall x, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ h

/--
Definition of `homMk` / `homMk` 的定义

English:
definition homMk
  signature: {X Y : FintypeCat} (f : X -> Y)
  body: ↾f

@[simp]

中文:
定义 homMk
  签名: {X Y : FintypeCat} (f : X -> Y)
  定义体: ↾f

@[simp]
-/
def homMk {X Y : FintypeCat} (f : X -> Y) : X ⟶ Y where
  hom := ↾f

@[simp]
/--
lemma `homMk_apply` / 引理 `homMk_apply`

English:
lemma homMk_apply
  given: {X Y : FintypeCat} (f : X -> Y) (x : X)
  proof: rfl

@[simp]

中文:
引理 homMk_apply
  条件: {X Y : FintypeCat} (f : X -> Y) (x : X)
  证明: rfl

@[simp]
-/
lemma homMk_apply {X Y : FintypeCat} (f : X -> Y) (x : X) :
    homMk f x = f x := rfl

@[simp]
/--
lemma `id_hom` / 引理 `id_hom`

English:
lemma id_hom
  given: (X : FintypeCat)
  statement: 𝟙 X.obj = ↾id
  proof: rfl

@[simp, reassoc]

中文:
引理 id_hom
  条件: (X : FintypeCat)
  结论: 𝟙 X.obj = ↾id
  证明: rfl

@[simp, reassoc]
-/
lemma id_hom (X : FintypeCat) : 𝟙 X.obj = ↾id := rfl

@[simp, reassoc]
/--
lemma `comp_hom` / 引理 `comp_hom`

English:
lemma comp_hom
  given: {X Y Z : FintypeCat} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

@[simp]

中文:
引理 comp_hom
  条件: {X Y Z : FintypeCat} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl

@[simp]
-/
lemma comp_hom {X Y Z : FintypeCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f.hom ≫ g.hom = ↾(g.hom ∘ f.hom) := rfl

@[simp]
/--
lemma `homMk_eq_id_iff` / 引理 `homMk_eq_id_iff`

English:
lemma homMk_eq_id_iff
  given: {X : FintypeCat} (f : X -> X)
  proof: by
  constructor
  · intro h
    ext x
    exact ConcreteCategory.congr_hom h x
  · rintro rfl
    rfl

@[simp]

中文:
引理 homMk_eq_id_iff
  条件: {X : FintypeCat} (f : X -> X)
  证明: by
  constructor
  · intro h
    ext x
    exact ConcreteCategory.congr_hom h x
  · rintro rfl
    rfl

@[simp]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, congr_hom
-/
lemma homMk_eq_id_iff {X : FintypeCat} (f : X -> X) :
    homMk f = 𝟙 X ↔ f = id := by
  constructor
  · intro h
    ext x
    exact ConcreteCategory.congr_hom h x
  · rintro rfl
    rfl

@[simp]
/--
lemma `homMk_eq_comp_iff` / 引理 `homMk_eq_comp_iff`

English:
lemma homMk_eq_comp_iff
  given: {X Y Z : FintypeCat} (f : X -> Y) (g : Y -> Z) (h : X -> Z)
  proof: by
  constructor
  · intro h
    ext x
    exact ConcreteCategory.congr_hom h x
  · rintro rfl
    rfl

中文:
引理 homMk_eq_comp_iff
  条件: {X Y Z : FintypeCat} (f : X -> Y) (g : Y -> Z) (h : X -> Z)
  证明: by
  constructor
  · intro h
    ext x
    exact ConcreteCategory.congr_hom h x
  · rintro rfl
    rfl

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, congr_hom
-/
lemma homMk_eq_comp_iff {X Y Z : FintypeCat} (f : X -> Y) (g : Y -> Z) (h : X -> Z) :
    homMk h = homMk f ≫ homMk g ↔ h = g ∘ f := by
  constructor
  · intro h
    ext x
    exact ConcreteCategory.congr_hom h x
  · rintro rfl
    rfl

-- See `equivEquivIso` in the root namespace for the analogue in `Type`.
/-- Equivalences between finite types are the same as isomorphisms in `FintypeCat`. -/
@[simps]
/--
Definition of `equivEquivIso` / `equivEquivIso` 的定义

English:
definition equivEquivIso
  signature: {A B : FintypeCat}
  body: { hom := homMk e
      inv := homMk e.symm }
  invFun i :=
    { toFun := i.hom
      invFun := i.inv
      left_inv := ConcreteCategory.congr_hom i.hom_inv_id
      right_inv := ConcreteCategory.congr_hom i.inv_hom_id }
  left_inv := by cat_disch
  right_inv := by cat_disch

中文:
定义 equivEquivIso
  签名: {A B : FintypeCat}
  定义体: { hom := homMk e
      inv := homMk e.symm }
  invFun i :=
    { toFun := i.hom
      invFun := i.inv
      left_inv := ConcreteCategory.congr_hom i.hom_inv_id
      right_inv := ConcreteCategory.congr_hom i.inv_hom_id }
  left_inv := by cat_disch
  right_inv := by cat_disch

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, cat_disch, congr_hom, e.symm, hom_inv_id, i.hom, i.hom_inv_id, i.inv, i.inv_hom_id, invFun, inv_hom_id, left_inv, right_inv
-/
def equivEquivIso {A B : FintypeCat} : A ≃ B ≃ (A ≅ B) where
  toFun e :=
    { hom := homMk e
      inv := homMk e.symm }
  invFun i :=
    { toFun := i.hom
      invFun := i.inv
      left_inv := ConcreteCategory.congr_hom i.hom_inv_id
      right_inv := ConcreteCategory.congr_hom i.inv_hom_id }
  left_inv := by cat_disch
  right_inv := by cat_disch

instance (X Y : FintypeCat) : Finite (X ⟶ Y) :=
  Finite.of_equiv _ (show (X ⟶ Y) ≃ (X -> Y) from
    InducedCategory.homEquiv.trans TypeCat.homEquiv).symm

instance (X Y : FintypeCat) : Finite (X ≅ Y) :=
  Finite.of_injective _ (fun _ _ h => Iso.ext h)

instance (X : FintypeCat) : Finite (Aut X) :=
inferInstanceAs Finite (X ≅ X)

universe u

/--
Definition of `Skeleton` / `Skeleton` 的定义

English:
definition Skeleton
  signature: : Type u
  body: ULift Nat

中文:
定义 Skeleton
  签名: : 类型u
  定义体: ULift Nat
-/
def Skeleton : Type u :=
  ULift Nat

namespace Skeleton

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: : Nat -> Skeleton
  body: ULift.up

中文:
定义 mk
  签名: : 自然数 -> Skeleton
  定义体: ULift.up

Depends on / 依赖: ULift.up
-/
def mk : Nat -> Skeleton :=
  ULift.up

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited Skeleton
  body: ⟨mk 0⟩

中文:
实例 :
  签名: Inhabited Skeleton
  定义体: ⟨mk 0⟩
-/
instance : Inhabited Skeleton :=
  ⟨mk 0⟩

/--
Definition of `len` / `len` 的定义

English:
definition len
  signature: : Skeleton -> Nat
  body: ULift.down

@[ext]

中文:
定义 len
  签名: : Skeleton -> 自然数
  定义体: ULift.down

@[ext]

Depends on / 依赖: ULift.down
-/
def len : Skeleton -> Nat :=
  ULift.down

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (X Y : Skeleton)
  statement: X.len = Y.len -> X = Y
  proof: ULift.ext _ _

中文:
定理 ext
  条件: (X Y : Skeleton)
  结论: X.len = Y.len -> X = Y
  证明: ULift.ext _ _

Depends on / 依赖: ULift.ext
-/
theorem ext (X Y : Skeleton) : X.len = Y.len -> X = Y :=
  ULift.ext _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SmallCategory Skeleton.{u}
  body: ULift.{u} (Fin X.len) -> ULift.{u} (Fin Y.len)
  id _ := id
  comp f g := g ∘ f

中文:
实例 :
  签名: SmallCategory Skeleton.{u}
  定义体: ULift.{u} (Fin X.len) -> ULift.{u} (Fin Y.len)
  id _ := id
  comp f g := g ∘ f

Depends on / 依赖: X.len, Y.len
-/
instance : SmallCategory Skeleton.{u} where
  Hom X Y := ULift.{u} (Fin X.len) -> ULift.{u} (Fin Y.len)
  id _ := id
  comp f g := g ∘ f

/--
theorem `is_skeletal` / 定理 `is_skeletal`

English:
theorem is_skeletal
  statement: Skeletal Skeleton.{u}
  proof: fun X Y ⟨h⟩ =>
ext _ _
Fin.equiv_iff_eq.mp
Nonempty.intro
        { toFun := fun x => (h.hom ⟨x⟩).down
          invFun := fun x => (h.inv ⟨x⟩).down
          left_inv := by
            intro a
            change ULift.down _ = _
            rw [ULift.up_down]
            change ((h.hom ≫ h.inv) _).

中文:
定理 is_skeletal
  结论: Skeletal Skeleton.{u}
  证明: fun X Y ⟨h⟩ =>
ext _ _
Fin.equiv_iff_eq.mp
Nonempty.intro
        { toFun := fun x => (h.hom ⟨x⟩).down
          invFun := fun x => (h.inv ⟨x⟩).down
          left_inv := by
            intro a
            change ULift.down _ = _
            rw [ULift.up_down]
            change ((h.hom ≫ h.inv) _).
-/
theorem is_skeletal : Skeletal Skeleton.{u} := fun X Y ⟨h⟩ =>
ext _ _
Fin.equiv_iff_eq.mp
Nonempty.intro
        { toFun := fun x => (h.hom ⟨x⟩).down
          invFun := fun x => (h.inv ⟨x⟩).down
          left_inv := by
            intro a
            change ULift.down _ = _
            rw [ULift.up_down]
            change ((h.hom ≫ h.inv) _).down = _
            simp
            rfl
          right_inv := by
            intro a
            change ULift.down _ = _
            rw [ULift.up_down]
            change ((h.inv ≫ h.hom) _).down = _
            simp
            rfl }

/--
Definition of `incl` / `incl` 的定义

English:
definition incl
  signature: : Skeleton.{u} ⥤ FintypeCat.{u} where
  body: FintypeCat.of (ULift (Fin X.len))
  map f := homMk f

中文:
定义 incl
  签名: : Skeleton.{u} ⥤ FintypeCat.{u} where
  定义体: FintypeCat.of (ULift (Fin X.len))
  map f := homMk f

Depends on / 依赖: FintypeCat, FintypeCat.of, X.len
-/
def incl : Skeleton.{u} ⥤ FintypeCat.{u} where
  obj X := FintypeCat.of (ULift (Fin X.len))
  map f := homMk f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: incl.Full
  body: ⟨_, rfl⟩

中文:
实例 :
  签名: incl.Full
  定义体: ⟨_, rfl⟩
-/
instance : incl.Full where map_surjective _ := ⟨_, rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: incl.Faithful
  body: by
    simpa using TypeCat.homEquiv.symm.injective (InducedCategory.homEquiv.symm.injective h)

中文:
实例 :
  签名: incl.Faithful
  定义体: by
    simpa using TypeCat.homEquiv.symm.injective (InducedCategory.homEquiv.symm.injective h)

Depends on / 依赖: InducedCategory, InducedCategory.homEquiv.symm.injective, TypeCat, TypeCat.homEquiv.symm.injective, homEquiv, injective
-/
instance : incl.Faithful where
  map_injective h := by
    simpa using TypeCat.homEquiv.symm.injective (InducedCategory.homEquiv.symm.injective h)

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: incl.EssSurj
  body: Functor.EssSurj.mk fun X =>
    letI := X.fintype
    let F := Fintype.equivFin X
    ⟨mk (Fintype.card X),
      Nonempty.intro
        { hom := homMk (F.symm ∘ ULift.down)
          inv := homMk (ULift.up ∘ F) }⟩

中文:
实例 :
  签名: incl.EssSurj
  定义体: Functor.EssSurj.mk fun X =>
    letI := X.fintype
    let F := Fintype.equivFin X
    ⟨mk (Fintype.card X),
      Nonempty.intro
        { hom := homMk (F.symm ∘ ULift.down)
          inv := homMk (ULift.up ∘ F) }⟩

Depends on / 依赖: EssSurj, F.symm, Fintype, Fintype.card, Fintype.equivFin, Functor, Functor.EssSurj.mk, Nonempty, Nonempty.intro, ULift.down, ULift.up, X.fintype, equivFin, fintype
-/
instance : incl.EssSurj :=
  Functor.EssSurj.mk fun X =>
    letI := X.fintype
    let F := Fintype.equivFin X
    ⟨mk (Fintype.card X),
      Nonempty.intro
        { hom := homMk (F.symm ∘ ULift.down)
          inv := homMk (ULift.up ∘ F) }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: incl.IsEquivalence

中文:
实例 :
  签名: incl.IsEquivalence
-/
noncomputable instance : incl.IsEquivalence where

/--
Definition of `equivalence` / `equivalence` 的定义

English:
definition equivalence
  signature: : Skeleton ≌ FintypeCat
  body: incl.asEquivalence

中文:
定义 equivalence
  签名: : Skeleton ≌ FintypeCat
  定义体: incl.asEquivalence

Depends on / 依赖: asEquivalence, incl.asEquivalence
-/
noncomputable def equivalence : Skeleton ≌ FintypeCat :=
  incl.asEquivalence

attribute [local instance] FintypeCat.fintype in
@[simp]
/--
theorem `incl_mk_nat_card` / 定理 `incl_mk_nat_card`

English:
theorem incl_mk_nat_card
  given: (n : Nat)
  proof: by
  convert! Finset.card_fin n
  dsimp [incl, mk, len]
  convert! (Fintype.ofEquiv_card Equiv.ulift).symm

中文:
定理 incl_mk_nat_card
  条件: (n : 自然数)
  证明: by
  convert! Finset.card_fin n
  dsimp [incl, mk, len]
  convert! (Fintype.ofEquiv_card Equiv.ulift).symm

Depends on / 依赖: Equiv.ulift, Finset, Finset.card_fin, Fintype, Fintype.ofEquiv_card, card_fin, convert, ofEquiv_card
-/
theorem incl_mk_nat_card (n : Nat) :
    Fintype.card (incl.obj (mk n)) = n := by
  convert! Finset.card_fin n
  dsimp [incl, mk, len]
  convert! (Fintype.ofEquiv_card Equiv.ulift).symm

end Skeleton

/--
lemma `isSkeleton` / 引理 `isSkeleton`

English:
lemma isSkeleton
  statement: IsSkeletonOf FintypeCat Skeleton Skeleton.incl where
  proof: Skeleton.is_skeletal
  eqv := by infer_instance

中文:
引理 isSkeleton
  结论: IsSkeletonOf FintypeCat Skeleton Skeleton.incl where
  证明: Skeleton.is_skeletal
  eqv := by infer_instance

Depends on / 依赖: Skeleton, Skeleton.is_skeletal, is_skeletal
-/
lemma isSkeleton : IsSkeletonOf FintypeCat Skeleton Skeleton.incl where
  skel := Skeleton.is_skeletal
  eqv := by infer_instance

section Universes

universe v

attribute [local instance] FintypeCat.fintype in
/--
Definition of `uSwitch` / `uSwitch` 的定义

English:
definition uSwitch
  signature: : FintypeCat.{u} ⥤ FintypeCat.{v} where
  body: FintypeCat.of ULift.{v} (Fin (Fintype.card X))
  map {X Y} f :=
    homMk (ULift.up ∘ Fintype.equivFin Y ∘ f.hom ∘ (Fintype.equivFin X).symm ∘ ULift.down)

中文:
定义 uSwitch
  签名: : FintypeCat.{u} ⥤ FintypeCat.{v} where
  定义体: FintypeCat.of ULift.{v} (Fin (Fintype.card X))
  map {X Y} f :=
    homMk (ULift.up ∘ Fintype.equivFin Y ∘ f.hom ∘ (Fintype.equivFin X).symm ∘ ULift.down)

Depends on / 依赖: Fintype, Fintype.card, FintypeCat, FintypeCat.of
-/
noncomputable def uSwitch : FintypeCat.{u} ⥤ FintypeCat.{v} where
obj X := FintypeCat.of ULift.{v} (Fin (Fintype.card X))
  map {X Y} f :=
    homMk (ULift.up ∘ Fintype.equivFin Y ∘ f.hom ∘ (Fintype.equivFin X).symm ∘ ULift.down)

attribute [local instance] FintypeCat.fintype in
/--
Definition of `uSwitchEquiv` / `uSwitchEquiv` 的定义

English:
definition uSwitchEquiv
  signature: (X : FintypeCat.{u})
  body: Equiv.ulift.trans (Fintype.equivFin X).symm

中文:
定义 uSwitchEquiv
  签名: (X : FintypeCat.{u})
  定义体: Equiv.ulift.trans (Fintype.equivFin X).symm

Depends on / 依赖: Equiv.ulift.trans, Fintype, Fintype.equivFin, equivFin
-/
noncomputable def uSwitchEquiv (X : FintypeCat.{u}) :
    uSwitch.{u, v}.obj X ≃ X :=
  Equiv.ulift.trans (Fintype.equivFin X).symm

set_option backward.isDefEq.respectTransparency false in
/--
lemma `uSwitchEquiv_naturality` / 引理 `uSwitchEquiv_naturality`

English:
lemma uSwitchEquiv_naturality
  statement: {X Y : FintypeCat.{u}} (f : X ⟶ Y)
  proof: by
  simp only [uSwitch, uSwitchEquiv, Equiv.trans_apply, Equiv.ulift_apply]
  rw [homMk_apply]
  aesop

中文:
引理 uSwitchEquiv_naturality
  结论: {X Y : FintypeCat.{u}} (f : X ⟶ Y)
  证明: by
  simp only [uSwitch, uSwitchEquiv, Equiv.trans_apply, Equiv.ulift_apply]
  rw [homMk_apply]
  aesop

Depends on / 依赖: Equiv.trans_apply, Equiv.ulift_apply, homMk_apply, trans_apply, uSwitch, uSwitchEquiv, ulift_apply
-/
lemma uSwitchEquiv_naturality {X Y : FintypeCat.{u}} (f : X ⟶ Y)
    (x : uSwitch.{u, v}.obj X) :
    f (X.uSwitchEquiv x) = Y.uSwitchEquiv (uSwitch.map f x) := by
  simp only [uSwitch, uSwitchEquiv, Equiv.trans_apply, Equiv.ulift_apply]
  rw [homMk_apply]
  aesop

/--
lemma `uSwitchEquiv_symm_naturality` / 引理 `uSwitchEquiv_symm_naturality`

English:
lemma uSwitchEquiv_symm_naturality
  given: {X Y : FintypeCat.{u}} (f : X ⟶ Y) (x : X)
  proof: by
  rw [Equiv.eq_symm_apply]; rw [← uSwitchEquiv_naturality f]; rw [Equiv.apply_symm_apply]

中文:
引理 uSwitchEquiv_symm_naturality
  条件: {X Y : FintypeCat.{u}} (f : X ⟶ Y) (x : X)
  证明: by
  rw [Equiv.eq_symm_apply]; rw [← uSwitchEquiv_naturality f]; rw [Equiv.apply_symm_apply]

Depends on / 依赖: Equiv.apply_symm_apply, Equiv.eq_symm_apply, apply_symm_apply, eq_symm_apply, uSwitchEquiv_naturality
-/
lemma uSwitchEquiv_symm_naturality {X Y : FintypeCat.{u}} (f : X ⟶ Y) (x : X) :
    uSwitch.map f (X.uSwitchEquiv.symm x) = Y.uSwitchEquiv.symm (f x) := by
  rw [Equiv.eq_symm_apply]; rw [← uSwitchEquiv_naturality f]; rw [Equiv.apply_symm_apply]

/--
lemma `uSwitch_map_uSwitch_map` / 引理 `uSwitch_map_uSwitch_map`

English:
lemma uSwitch_map_uSwitch_map
  given: {X Y : FintypeCat.{u}} (f : X ⟶ Y)
  proof: rfl

中文:
引理 uSwitch_map_uSwitch_map
  条件: {X Y : FintypeCat.{u}} (f : X ⟶ Y)
  证明: rfl
-/
lemma uSwitch_map_uSwitch_map {X Y : FintypeCat.{u}} (f : X ⟶ Y) :
    uSwitch.map (uSwitch.map f) =
    (equivEquivIso ((uSwitch.obj X).uSwitchEquiv.trans X.uSwitchEquiv)).hom ≫
      f ≫ (equivEquivIso ((uSwitch.obj Y).uSwitchEquiv.trans
      Y.uSwitchEquiv)).inv := rfl

set_option backward.defeqAttrib.useBackward true in
attribute [local simp] uSwitch_map_uSwitch_map in
/--
Definition of `uSwitchEquivalence` / `uSwitchEquivalence` 的定义

English:
definition uSwitchEquivalence
  signature: : FintypeCat.{u} ≌ FintypeCat.{v} where
  body: uSwitch
  inverse := uSwitch
  unitIso := NatIso.ofComponents (fun X => (equivEquivIso <|
    (uSwitch.obj X).uSwitchEquiv.trans X.uSwitchEquiv).symm)
  counitIso := NatIso.ofComponents (fun X => equivEquivIso <|
    (uSwitch.obj X).uSwitchEquiv.trans X.uSwitchEquiv)
  functor_unitIso_comp X := by
 

中文:
定义 uSwitchEquivalence
  签名: : FintypeCat.{u} ≌ FintypeCat.{v} where
  定义体: uSwitch
  inverse := uSwitch
  unitIso := NatIso.ofComponents (fun X => (equivEquivIso <|
    (uSwitch.obj X).uSwitchEquiv.trans X.uSwitchEquiv).symm)
  counitIso := NatIso.ofComponents (fun X => equivEquivIso <|
    (uSwitch.obj X).uSwitchEquiv.trans X.uSwitchEquiv)
  functor_unitIso_comp X := by
 

Depends on / 依赖: uSwitch
-/
noncomputable def uSwitchEquivalence : FintypeCat.{u} ≌ FintypeCat.{v} where
  functor := uSwitch
  inverse := uSwitch
  unitIso := NatIso.ofComponents (fun X => (equivEquivIso <|
    (uSwitch.obj X).uSwitchEquiv.trans X.uSwitchEquiv).symm)
  counitIso := NatIso.ofComponents (fun X => equivEquivIso <|
    (uSwitch.obj X).uSwitchEquiv.trans X.uSwitchEquiv)
  functor_unitIso_comp X := by
    ext x
    simp [← uSwitchEquiv_naturality]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: uSwitch.IsEquivalence
  body: uSwitchEquivalence.isEquivalence_functor

中文:
实例 :
  签名: uSwitch.IsEquivalence
  定义体: uSwitchEquivalence.isEquivalence_functor

Depends on / 依赖: isEquivalence_functor, uSwitchEquivalence, uSwitchEquivalence.isEquivalence_functor
-/
instance : uSwitch.IsEquivalence :=
  uSwitchEquivalence.isEquivalence_functor

end Universes

end FintypeCat

namespace FunctorToFintypeCat

universe u v w

variable {C : Type u} [Category.{v} C] (F G : C ⥤ FintypeCat.{w}) {X Y : C}

/--
lemma `naturality` / 引理 `naturality`

English:
lemma naturality
  given: (σ : F ⟶ G) (f : X ⟶ Y) (x : F.obj X)
  proof: (σ.naturality_apply f) x

中文:
引理 naturality
  条件: (σ : F ⟶ G) (f : X ⟶ Y) (x : F.obj X)
  证明: (σ.naturality_apply f) x

Depends on / 依赖: naturality_apply
-/
lemma naturality (σ : F ⟶ G) (f : X ⟶ Y) (x : F.obj X) :
    σ.app Y (F.map f x) = G.map f (σ.app X x) :=
  (σ.naturality_apply f) x

end FunctorToFintypeCat
