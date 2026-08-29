/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Algebra.Group.Invertible.Defs

/-!
# The category of groups in a Cartesian monoidal category

We define group objects in Cartesian monoidal categories.

We show that the associativity diagram of a group object is always Cartesian and deduce that
morphisms of group objects commute with taking inverses.

We show that a finite-product-preserving functor takes group objects to group objects.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃ u

open CategoryTheory Category Limits MonoidalCategory CartesianMonoidalCategory Mon MonObj

namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory.{v₁} C]

/--
Definition of `AddGrpObj` / `AddGrpObj` 的定义

English:
class AddGrpObj
  parameters: (X : C)
  extends: AddMonObj X
  axioms and operations (3):
    - neg : X ⟶ X
    - left_neg((X)) : lift neg (𝟙 X) ≫ add = toUnit _ ≫ zero  [default: by cat_disch]
    - right_neg((X)) : lift (𝟙 X) neg ≫ add = toUnit _ ≫ zero  [default: by cat_disch]

中文:
类 AddGrpObj
  参数: (X : C)
  继承: AddMonObj X
  公理与运算 (3 个):
    - neg : X ⟶ X
    - left_neg((X)) : lift neg (𝟙 X) ≫ add = toUnit _ ≫ zero  [默认: by cat_disch]
    - right_neg((X)) : lift (𝟙 X) neg ≫ add = toUnit _ ≫ zero  [默认: by cat_disch]

Depends on / 依赖: cat_disch, right_neg, toUnit
-/
class AddGrpObj (X : C) extends AddMonObj X where
  /-- The negation in a group object -/
  neg : X ⟶ X
  left_neg (X) : lift neg (𝟙 X) ≫ add = toUnit _ ≫ zero := by cat_disch
  right_neg (X) : lift (𝟙 X) neg ≫ add = toUnit _ ≫ zero := by cat_disch

/-- A group object internal to a cartesian monoidal category. Also see the bundled `Grp`. -/
@[to_additive]
/--
Definition of `GrpObj` / `GrpObj` 的定义

English:
class GrpObj
  parameters: (X : C)
  extends: MonObj X
  axioms and operations (3):
    - inv : X ⟶ X
    - left_inv((X)) : lift inv (𝟙 X) ≫ mul = toUnit _ ≫ one  [default: by cat_disch]
    - right_inv((X)) : lift (𝟙 X) inv ≫ mul = toUnit _ ≫ one  [default: by cat_disch]

中文:
类 GrpObj
  参数: (X : C)
  继承: MonObj X
  公理与运算 (3 个):
    - inv : X ⟶ X
    - left_inv((X)) : lift inv (𝟙 X) ≫ mul = toUnit _ ≫ one  [默认: by cat_disch]
    - right_inv((X)) : lift (𝟙 X) inv ≫ mul = toUnit _ ≫ one  [默认: by cat_disch]

Depends on / 依赖: cat_disch, right_inv, toUnit
-/
class GrpObj (X : C) extends MonObj X where
  /-- The inverse in a group object -/
  inv : X ⟶ X
  left_inv (X) : lift inv (𝟙 X) ≫ mul = toUnit _ ≫ one := by cat_disch
  right_inv (X) : lift (𝟙 X) inv ≫ mul = toUnit _ ≫ one := by cat_disch

namespace MonObj

@[inherit_doc] scoped notation "ι" => GrpObj.inv
@[inherit_doc] scoped notation "ι[" G "]" => GrpObj.inv (X := G)

end MonObj

namespace GrpObj

attribute [reassoc (attr := simp)] left_inv right_inv
attribute [reassoc (attr := simp)] AddGrpObj.left_neg AddGrpObj.right_neg
attribute [to_additive existing] left_inv_assoc right_inv_assoc

@[to_additive]
/--
Instance `instTensorUnit` / 实例 `instTensorUnit`

English:
instance instTensorUnit
  signature: : GrpObj (𝟙_ C) where
  body: 𝟙 (𝟙_ C)

中文:
实例 instTensorUnit
  签名: : GrpObj (𝟙_ C) where
  定义体: 𝟙 (𝟙_ C)
-/
instance instTensorUnit : GrpObj (𝟙_ C) where
  inv := 𝟙 (𝟙_ C)

attribute [simps inv] instTensorUnit
attribute [simps neg] AddGrpObj.instTensorAddUnit

end GrpObj

variable (C) in
/--
Definition of `AddGrp` / `AddGrp` 的定义

English:
structure AddGrp
  parameters: where
  axioms and operations (2):
    - X : C
    - [addGrp : AddGrpObj X]

中文:
结构 AddGrp
  参数: where
  公理与运算 (2 个):
    - X : C
    - [addGrp : AddGrpObj X]
-/
structure AddGrp where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [addGrp : AddGrpObj X]

variable (C) in
/-- A group object in a Cartesian monoidal category. -/
@[to_additive]
/--
Definition of `Grp` / `Grp` 的定义

English:
structure Grp
  parameters: where
  axioms and operations (2):
    - X : C
    - [grp : GrpObj X]

中文:
结构 Grp
  参数: where
  公理与运算 (2 个):
    - X : C
    - [grp : GrpObj X]
-/
structure Grp where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [grp : GrpObj X]

attribute [instance] Grp.grp AddGrp.addGrp

namespace Grp

/-- A group object is a monoid object. -/
@[to_additive (attr := simps -isSimp X) toAddMon
/-- An additive group object is an additive monoid object. -/]
/--
Definition of `toMon` / `toMon` 的定义

English:
abbreviation toMon
  signature: (A : Grp C)
  body: ⟨A.X⟩

中文:
缩写 toMon
  签名: (A : Grp C)
  定义体: ⟨A.X⟩
-/
abbrev toMon (A : Grp C) : Mon C := ⟨A.X⟩

variable (C) in
/-- The trivial group object. -/
@[to_additive (attr := simps!) /-- The trivial additive group object. -/]
/--
Definition of `trivial` / `trivial` 的定义

English:
definition trivial
  signature: : Grp C
  body: { Mon.trivial C with grp := GrpObj.instTensorUnit }

@[to_additive]

中文:
定义 trivial
  签名: : Grp C
  定义体: { Mon.trivial C with grp := GrpObj.instTensorUnit }

@[to_additive]

Depends on / 依赖: GrpObj, GrpObj.instTensorUnit, Mon.trivial, instTensorUnit
-/
def trivial : Grp C := { Mon.trivial C with grp := GrpObj.instTensorUnit }

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Grp C)
  body: trivial C

@[to_additive]

中文:
实例 :
  签名: Inhabited (Grp C)
  定义体: trivial C

@[to_additive]
-/
instance : Inhabited (Grp C) where
  default := trivial C

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (Grp C)
  body: inferInstanceAs (Category (InducedCategory _ Grp.toMon))

@[to_additive (attr := simp)]

中文:
实例 :
  签名: Category (Grp C)
  定义体: inferInstanceAs (Category (InducedCategory _ Grp.toMon))

@[to_additive (attr := simp)]

Depends on / 依赖: Category, Grp.toMon, InducedCategory
-/
instance : Category (Grp C) :=
  inferInstanceAs (Category (InducedCategory _ Grp.toMon))

@[to_additive (attr := simp)]
/--
theorem `id_hom_hom` / 定理 `id_hom_hom`

English:
theorem id_hom_hom
  given: (A : Grp C)
  statement: Mon.Hom.hom (InducedCategory.Hom.hom (𝟙 A)) = 𝟙 A.X
  proof: rfl

@[to_additive (attr := simp, reassoc)]

中文:
定理 id_hom_hom
  条件: (A : Grp C)
  结论: Mon.Hom.hom (InducedCategory.Hom.hom (𝟙 A)) = 𝟙 A.X
  证明: rfl

@[to_additive (attr := simp, reassoc)]
-/
theorem id_hom_hom (A : Grp C) : Mon.Hom.hom (InducedCategory.Hom.hom (𝟙 A)) = 𝟙 A.X :=
  rfl

@[to_additive (attr := simp, reassoc)]
/--
theorem `comp_hom_hom` / 定理 `comp_hom_hom`

English:
theorem comp_hom_hom
  given: {R S T : Grp C} (f : R ⟶ S) (g : S ⟶ T)
  proof: rfl

@[to_additive (attr := ext)]

中文:
定理 comp_hom_hom
  条件: {R S T : Grp C} (f : R ⟶ S) (g : S ⟶ T)
  证明: rfl

@[to_additive (attr := ext)]
-/
theorem comp_hom_hom {R S T : Grp C} (f : R ⟶ S) (g : S ⟶ T) :
    Mon.Hom.hom (f ≫ g).hom = f.hom.hom ≫ g.hom.hom :=
  rfl

@[to_additive (attr := ext)]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  given: {A B : Grp C} (f g : A ⟶ B) (h : f.hom.hom = g.hom.hom)
  statement: f = g
  proof: InducedCategory.hom_ext (Mon.Hom.ext h)

中文:
定理 hom_ext
  条件: {A B : Grp C} (f g : A ⟶ B) (h : f.hom.hom = g.hom.hom)
  结论: f = g
  证明: InducedCategory.hom_ext (Mon.Hom.ext h)

Depends on / 依赖: InducedCategory, InducedCategory.hom_ext, Mon.Hom.ext, hom_ext
-/
theorem hom_ext {A B : Grp C} (f g : A ⟶ B) (h : f.hom.hom = g.hom.hom) : f = g :=
  InducedCategory.hom_ext (Mon.Hom.ext h)

/-- Constructor for morphisms in `Grp C`. -/
@[to_additive (attr := simps) /-- Constructor for morphisms in `AddGrp C`. -/]
/--
Definition of `homMk'` / `homMk'` 的定义

English:
definition homMk'
  signature: {A B : Grp C} (f : A.toMon ⟶ B.toMon)
  body: f

中文:
定义 homMk'
  签名: {A B : Grp C} (f : A.toMon ⟶ B.toMon)
  定义体: f
-/
def homMk' {A B : Grp C} (f : A.toMon ⟶ B.toMon) : A ⟶ B where
  hom := f

/-- Construct a morphism `A ⟶ B` of `Grp C` from a map `f : A.X ⟶ A.X` and a `IsMonHom f`
instance. -/
@[to_additive (attr := simps!)
/-- Construct a morphism `A ⟶ B` of `AddGrp C` from a map `f : A.X ⟶ A.X` and a `IsAddMonHom f`
instance.-/]
/--
Definition of `homMk` / `homMk` 的定义

English:
definition homMk
  signature: {A B : Grp C} (f : A.X ⟶ B.X) [IsMonHom f]
  body: homMk' (.mk f)

中文:
定义 homMk
  签名: {A B : Grp C} (f : A.X ⟶ B.X) [IsMonHom f]
  定义体: homMk' (.mk f)
-/
def homMk {A B : Grp C} (f : A.X ⟶ B.X) [IsMonHom f] : A ⟶ B :=
  homMk' (.mk f)

/-- Construct a morphism `Grp.mk G ⟶ Grp.mk H` from a map `f : G ⟶ H` and a `IsMonHom f`
instance. -/
@[to_additive (attr := simps!)
/-- Construct a morphism `AddGrp.mk G ⟶ AddGrp.mk H` from a map `f : G ⟶ H` and a `IsAddMonHom f`
instance. -/]
/--
Definition of `ofHom` / `ofHom` 的定义

English:
definition ofHom
  signature: {A B : C} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
  body: Grp.homMk f

中文:
定义 ofHom
  签名: {A B : C} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
  定义体: Grp.homMk f

Depends on / 依赖: Grp.homMk
-/
def ofHom {A B : C} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] : Grp.mk A ⟶ Grp.mk B :=
  Grp.homMk f

/-- Constructor for morphisms in `Grp C`. -/
@[to_additive (attr := simps!) /-- Constructor for morphisms in `AddGrp C`. -/]
/--
Definition of `homMk''` / `homMk''` 的定义

English:
definition homMk''
  signature: {A B : Grp C} (f : A.X ⟶ B.X)
  body: haveI : IsMonHom f := ⟨one_f, mul_f⟩
  homMk f

@[to_additive (attr := simp)]

中文:
定义 homMk''
  签名: {A B : Grp C} (f : A.X ⟶ B.X)
  定义体: haveI : IsMonHom f := ⟨one_f, mul_f⟩
  homMk f

@[to_additive (attr := simp)]

Depends on / 依赖: IsMonHom, cat_disch, mul_f, one_f
-/
def homMk'' {A B : Grp C} (f : A.X ⟶ B.X)
    (one_f : η ≫ f = η := by cat_disch)
    (mul_f : μ ≫ f = (f otimesₘ f) ≫ μ := by cat_disch) : A ⟶ B :=
  haveI : IsMonHom f := ⟨one_f, mul_f⟩
  homMk f

@[to_additive (attr := simp)]
/--
lemma `id'` / 引理 `id'`

English:
lemma id'
  given: (A : Grp C)
  proof: rfl

@[to_additive (attr := simp, reassoc)]

中文:
引理 id'
  条件: (A : Grp C)
  证明: rfl

@[to_additive (attr := simp, reassoc)]
-/
lemma id' (A : Grp C) :
    (InducedCategory.Hom.hom (𝟙 A) : A.toMon ⟶ A.toMon) = 𝟙 (A.toMon) := rfl

@[to_additive (attr := simp, reassoc)]
/--
lemma `comp'` / 引理 `comp'`

English:
lemma comp'
  given: {A₁ A₂ A₃ : Grp C} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃)
  proof: rfl

中文:
引理 comp'
  条件: {A₁ A₂ A₃ : Grp C} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃)
  证明: rfl
-/
lemma comp' {A₁ A₂ A₃ : Grp C} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) :
    (InducedCategory.Hom.hom (f ≫ g : A₁ ⟶ A₃) : A₁.toMon ⟶ A₃.toMon) =
      f.hom ≫ g.hom := rfl

end Grp

namespace GrpObj
variable {G X : C} [GrpObj G]

variable {A : C} {B : C}

@[to_additive (attr := reassoc (attr := simp))]
/--
theorem `lift_comp_inv_right` / 定理 `lift_comp_inv_right`

English:
theorem lift_comp_inv_right
  given: [GrpObj B] (f : A ⟶ B)
  proof: by
  have := f ≫= right_inv B
  rwa [comp_lift_assoc, comp_id, reassoc_of% toUnit_unique (f ≫ toUnit B) (toUnit A)] at this

@[to_additive (attr := reassoc)]

中文:
定理 lift_comp_inv_right
  条件: [GrpObj B] (f : A ⟶ B)
  证明: by
  have := f ≫= right_inv B
  rwa [comp_lift_assoc, comp_id, reassoc_of% toUnit_unique (f ≫ toUnit B) (toUnit A)] at this

@[to_additive (attr := reassoc)]

Depends on / 依赖: comp_id, comp_lift_assoc, reassoc_of, right_inv, toUnit, toUnit_unique
-/
theorem lift_comp_inv_right [GrpObj B] (f : A ⟶ B) :
    lift f (f ≫ ι) ≫ μ = toUnit _ ≫ η := by
  have := f ≫= right_inv B
  rwa [comp_lift_assoc, comp_id, reassoc_of% toUnit_unique (f ≫ toUnit B) (toUnit A)] at this

@[to_additive (attr := reassoc)]
/--
theorem `lift_inv_comp_right` / 定理 `lift_inv_comp_right`

English:
theorem lift_inv_comp_right
  given: [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
  proof: by
  have := right_inv A =≫ f
  rwa [assoc, IsMonHom.mul_hom, assoc, IsMonHom.one_hom, lift_map_assoc, id_comp] at this

@[to_additive (attr := reassoc (attr := simp))]

中文:
定理 lift_inv_comp_right
  条件: [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
  证明: by
  have := right_inv A =≫ f
  rwa [assoc, IsMonHom.mul_hom, assoc, IsMonHom.one_hom, lift_map_assoc, id_comp] at this

@[to_additive (attr := reassoc (attr := simp))]

Depends on / 依赖: IsMonHom, IsMonHom.mul_hom, IsMonHom.one_hom, id_comp, lift_map_assoc, mul_hom, one_hom, right_inv
-/
theorem lift_inv_comp_right [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] :
    lift f (ι ≫ f) ≫ μ = toUnit _ ≫ η := by
  have := right_inv A =≫ f
  rwa [assoc, IsMonHom.mul_hom, assoc, IsMonHom.one_hom, lift_map_assoc, id_comp] at this

@[to_additive (attr := reassoc (attr := simp))]
/--
theorem `lift_comp_inv_left` / 定理 `lift_comp_inv_left`

English:
theorem lift_comp_inv_left
  given: [GrpObj B] (f : A ⟶ B)
  proof: by
  have := f ≫= left_inv B
  rwa [comp_lift_assoc, comp_id, reassoc_of% toUnit_unique (f ≫ toUnit B) (toUnit A)] at this

@[to_additive (attr := reassoc)]

中文:
定理 lift_comp_inv_left
  条件: [GrpObj B] (f : A ⟶ B)
  证明: by
  have := f ≫= left_inv B
  rwa [comp_lift_assoc, comp_id, reassoc_of% toUnit_unique (f ≫ toUnit B) (toUnit A)] at this

@[to_additive (attr := reassoc)]

Depends on / 依赖: comp_id, comp_lift_assoc, left_inv, reassoc_of, toUnit, toUnit_unique
-/
theorem lift_comp_inv_left [GrpObj B] (f : A ⟶ B) :
    lift (f ≫ ι) f ≫ μ = toUnit _ ≫ η := by
  have := f ≫= left_inv B
  rwa [comp_lift_assoc, comp_id, reassoc_of% toUnit_unique (f ≫ toUnit B) (toUnit A)] at this

@[to_additive (attr := reassoc)]
/--
theorem `lift_inv_comp_left` / 定理 `lift_inv_comp_left`

English:
theorem lift_inv_comp_left
  given: [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
  proof: by
  have := left_inv A =≫ f
  rwa [assoc, IsMonHom.mul_hom, assoc, IsMonHom.one_hom, lift_map_assoc, id_comp] at this

@[to_additive]

中文:
定理 lift_inv_comp_left
  条件: [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
  证明: by
  have := left_inv A =≫ f
  rwa [assoc, IsMonHom.mul_hom, assoc, IsMonHom.one_hom, lift_map_assoc, id_comp] at this

@[to_additive]

Depends on / 依赖: IsMonHom, IsMonHom.mul_hom, IsMonHom.one_hom, id_comp, left_inv, lift_map_assoc, mul_hom, one_hom
-/
theorem lift_inv_comp_left [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] :
    lift (ι ≫ f) f ≫ μ = toUnit _ ≫ η := by
  have := left_inv A =≫ f
  rwa [assoc, IsMonHom.mul_hom, assoc, IsMonHom.one_hom, lift_map_assoc, id_comp] at this

@[to_additive]
/--
theorem `eq_lift_inv_left` / 定理 `eq_lift_inv_left`

English:
theorem eq_lift_inv_left
  given: [GrpObj B] (f g h : A ⟶ B)
  proof: by
  refine ⟨?_, ?_⟩ <;> (rintro rfl; simp [← lift_lift_assoc])

@[to_additive]

中文:
定理 eq_lift_inv_left
  条件: [GrpObj B] (f g h : A ⟶ B)
  证明: by
  refine ⟨?_, ?_⟩ <;> (rintro rfl; simp [← lift_lift_assoc])

@[to_additive]

Depends on / 依赖: lift_lift_assoc
-/
theorem eq_lift_inv_left [GrpObj B] (f g h : A ⟶ B) :
    f = lift (g ≫ ι) h ≫ μ ↔ lift g f ≫ μ = h := by
  refine ⟨?_, ?_⟩ <;> (rintro rfl; simp [← lift_lift_assoc])

@[to_additive]
/--
theorem `lift_inv_left_eq` / 定理 `lift_inv_left_eq`

English:
theorem lift_inv_left_eq
  given: [GrpObj B] (f g h : A ⟶ B)
  proof: by
  rw [eq_comm]; rw [eq_lift_inv_left]; rw [eq_comm]

@[to_additive]

中文:
定理 lift_inv_left_eq
  条件: [GrpObj B] (f g h : A ⟶ B)
  证明: by
  rw [eq_comm]; rw [eq_lift_inv_left]; rw [eq_comm]

@[to_additive]

Depends on / 依赖: eq_comm, eq_lift_inv_left
-/
theorem lift_inv_left_eq [GrpObj B] (f g h : A ⟶ B) :
    lift (f ≫ ι) g ≫ μ = h ↔ g = lift f h ≫ μ := by
  rw [eq_comm]; rw [eq_lift_inv_left]; rw [eq_comm]

@[to_additive]
/--
theorem `eq_lift_inv_right` / 定理 `eq_lift_inv_right`

English:
theorem eq_lift_inv_right
  given: [GrpObj B] (f g h : A ⟶ B)
  proof: by
  refine ⟨?_, ?_⟩ <;> (rintro rfl; simp [lift_lift_assoc])

@[to_additive]

中文:
定理 eq_lift_inv_right
  条件: [GrpObj B] (f g h : A ⟶ B)
  证明: by
  refine ⟨?_, ?_⟩ <;> (rintro rfl; simp [lift_lift_assoc])

@[to_additive]

Depends on / 依赖: lift_lift_assoc
-/
theorem eq_lift_inv_right [GrpObj B] (f g h : A ⟶ B) :
    f = lift g (h ≫ ι) ≫ μ ↔ lift f h ≫ μ = g := by
  refine ⟨?_, ?_⟩ <;> (rintro rfl; simp [lift_lift_assoc])

@[to_additive]
/--
theorem `lift_inv_right_eq` / 定理 `lift_inv_right_eq`

English:
theorem lift_inv_right_eq
  given: [GrpObj B] (f g h : A ⟶ B)
  proof: by
  rw [eq_comm]; rw [eq_lift_inv_right]; rw [eq_comm]

@[to_additive]

中文:
定理 lift_inv_right_eq
  条件: [GrpObj B] (f g h : A ⟶ B)
  证明: by
  rw [eq_comm]; rw [eq_lift_inv_right]; rw [eq_comm]

@[to_additive]

Depends on / 依赖: eq_comm, eq_lift_inv_right
-/
theorem lift_inv_right_eq [GrpObj B] (f g h : A ⟶ B) :
    lift f (g ≫ ι) ≫ μ = h ↔ f = lift h g ≫ μ := by
  rw [eq_comm]; rw [eq_lift_inv_right]; rw [eq_comm]

@[to_additive]
/--
theorem `lift_left_mul_ext` / 定理 `lift_left_mul_ext`

English:
theorem lift_left_mul_ext
  statement: [GrpObj B] {f g : A ⟶ B} (i : A ⟶ B)
  proof: by
  rwa [← eq_lift_inv_right, lift_lift_assoc, lift_comp_inv_right, lift_comp_one_right] at h

@[to_additive (attr := reassoc (attr := simp))]

中文:
定理 lift_left_mul_ext
  结论: [GrpObj B] {f g : A ⟶ B} (i : A ⟶ B)
  证明: by
  rwa [← eq_lift_inv_right, lift_lift_assoc, lift_comp_inv_right, lift_comp_one_right] at h

@[to_additive (attr := reassoc (attr := simp))]

Depends on / 依赖: eq_lift_inv_right, lift_comp_inv_right, lift_comp_one_right, lift_lift_assoc
-/
theorem lift_left_mul_ext [GrpObj B] {f g : A ⟶ B} (i : A ⟶ B)
    (h : lift f i ≫ μ = lift g i ≫ μ) : f = g := by
  rwa [← eq_lift_inv_right, lift_lift_assoc, lift_comp_inv_right, lift_comp_one_right] at h

@[to_additive (attr := reassoc (attr := simp))]
/--
theorem `inv_comp_inv` / 定理 `inv_comp_inv`

English:
theorem inv_comp_inv
  given: (A : C) [GrpObj A]
  statement: ι ≫ ι = 𝟙 A
  proof: by
  apply lift_left_mul_ext ι[A]
  rw [right_inv]; rw [← comp_toUnit_assoc ι]; rw [← left_inv]; rw [comp_lift_assoc]; rw [Category.comp_id]

中文:
定理 inv_comp_inv
  条件: (A : C) [GrpObj A]
  结论: ι ≫ ι = 𝟙 A
  证明: by
  apply lift_left_mul_ext ι[A]
  rw [right_inv]; rw [← comp_toUnit_assoc ι]; rw [← left_inv]; rw [comp_lift_assoc]; rw [Category.comp_id]

Depends on / 依赖: Category, Category.comp_id, comp_id, comp_lift_assoc, comp_toUnit_assoc, left_inv, lift_left_mul_ext, right_inv
-/
theorem inv_comp_inv (A : C) [GrpObj A] : ι ≫ ι = 𝟙 A := by
  apply lift_left_mul_ext ι[A]
  rw [right_inv]; rw [← comp_toUnit_assoc ι]; rw [← left_inv]; rw [comp_lift_assoc]; rw [Category.comp_id]

/-- Transfer `AddGrpObj` along an isomorphism. -/
-- Note: The simps lemmas are not tagged simp because their `#discr_tree_simp_key` are too generic.
@[simps! -isSimp]
/--
Definition of `_root_.CategoryTheory.AddGrpObj.ofIso` / `_root_.CategoryTheory.AddGrpObj.ofIso` 的定义

English:
abbreviation _root_.CategoryTheory.AddGrpObj.ofIso
  signature: {G' X : C} [AddGrpObj G'] (e : G' ≅ X)
  body: AddMonObj.ofIso e
  neg := e.inv ≫ AddGrpObj.neg ≫ e.hom
  left_neg := by simp +instances [AddMonObj.ofIso]
  right_neg := by simp +instances [AddMonObj.ofIso]

中文:
缩写 _root_.CategoryTheory.AddGrpObj.ofIso
  签名: {G' X : C} [AddGrpObj G'] (e : G' ≅ X)
  定义体: AddMonObj.ofIso e
  neg := e.inv ≫ AddGrpObj.neg ≫ e.hom
  left_neg := by simp +instances [AddMonObj.ofIso]
  right_neg := by simp +instances [AddMonObj.ofIso]

Depends on / 依赖: AddMonObj, AddMonObj.ofIso
-/
abbrev _root_.CategoryTheory.AddGrpObj.ofIso {G' X : C} [AddGrpObj G'] (e : G' ≅ X) :
    AddGrpObj X where
  toAddMonObj := AddMonObj.ofIso e
  neg := e.inv ≫ AddGrpObj.neg ≫ e.hom
  left_neg := by simp +instances [AddMonObj.ofIso]
  right_neg := by simp +instances [AddMonObj.ofIso]

/-- Transfer `GrpObj` along an isomorphism. -/
-- Note: The simps lemmas are not tagged simp because their `#discr_tree_simp_key` are too generic.
@[simps! -isSimp]
/--
Definition of `ofIso` / `ofIso` 的定义

English:
abbreviation ofIso
  signature: (e : G ≅ X)
  body: .ofIso e
  inv := e.inv ≫ ι[G] ≫ e.hom
  left_inv := by simp +instances [MonObj.ofIso]
  right_inv := by simp +instances [MonObj.ofIso]

中文:
缩写 ofIso
  签名: (e : G ≅ X)
  定义体: .ofIso e
  inv := e.inv ≫ ι[G] ≫ e.hom
  left_inv := by simp +instances [MonObj.ofIso]
  right_inv := by simp +instances [MonObj.ofIso]
-/
abbrev ofIso (e : G ≅ X) : GrpObj X where
  toMonObj := .ofIso e
  inv := e.inv ≫ ι[G] ≫ e.hom
  left_inv := by simp +instances [MonObj.ofIso]
  right_inv := by simp +instances [MonObj.ofIso]

attribute [to_additive existing] ofIso

@[to_additive]
instance (A : C) [GrpObj A] : IsIso ι[A] := ⟨ι, by simp, by simp⟩

/-- For `inv ≫ inv = 𝟙` see `inv_comp_inv`. -/
@[to_additive (attr := simp) /-- For `neg ≫ neg = 𝟙` see `neg_comp_neg`. -/]
/--
theorem `inv_inv` / 定理 `inv_inv`

English:
theorem inv_inv
  given: (A : C) [GrpObj A]
  statement: CategoryTheory.inv ι = ι[A]
  proof: by
  rw [eq_comm]; rw [← CategoryTheory.inv_comp_eq_id]; rw [IsIso.inv_inv]; rw [inv_comp_inv]

@[to_additive (attr := reassoc)]

中文:
定理 inv_inv
  条件: (A : C) [GrpObj A]
  结论: CategoryTheory.inv ι = ι[A]
  证明: by
  rw [eq_comm]; rw [← CategoryTheory.inv_comp_eq_id]; rw [IsIso.inv_inv]; rw [inv_comp_inv]

@[to_additive (attr := reassoc)]

Depends on / 依赖: CategoryTheory, CategoryTheory.inv_comp_eq_id, IsIso.inv_inv, eq_comm, inv_comp_eq_id, inv_comp_inv, inv_inv
-/
theorem inv_inv (A : C) [GrpObj A] : CategoryTheory.inv ι = ι[A] := by
  rw [eq_comm]; rw [← CategoryTheory.inv_comp_eq_id]; rw [IsIso.inv_inv]; rw [inv_comp_inv]

@[to_additive (attr := reassoc)]
/--
theorem `mul_inv` / 定理 `mul_inv`

English:
theorem mul_inv
  given: [BraidedCategory C] (A : C) [GrpObj A]
  proof: by
  apply lift_left_mul_ext μ
  nth_rw 2 [← Category.comp_id μ]
  rw [← comp_lift]; rw [Category.assoc]; rw [left_inv]; rw [← Category.assoc (β_ A A).hom]; rw [← lift_snd_fst]; rw [lift_map]; rw [lift_lift_assoc]
  nth_rw 2 [← Category.id_comp μ]
  rw [← lift_fst_snd]; rw [← lift_lift_assoc (fst A 

中文:
定理 mul_inv
  条件: [BraidedCategory C] (A : C) [GrpObj A]
  证明: by
  apply lift_left_mul_ext μ
  nth_rw 2 [← Category.comp_id μ]
  rw [← comp_lift]; rw [Category.assoc]; rw [left_inv]; rw [← Category.assoc (β_ A A).hom]; rw [← lift_snd_fst]; rw [lift_map]; rw [lift_lift_assoc]
  nth_rw 2 [← Category.id_comp μ]
  rw [← lift_fst_snd]; rw [← lift_lift_assoc (fst A 

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Category.id_comp, comp_id, comp_lift, comp_toUnit_assoc, id_comp, left_inv, lift_comp_inv_left, lift_comp_one_left, lift_fst_snd, lift_left_mul_ext, lift_lift_assoc, lift_map, lift_snd_fst, nth_rw
-/
theorem mul_inv [BraidedCategory C] (A : C) [GrpObj A] :
    μ ≫ ι = (β_ A A).hom ≫ (ι otimesₘ ι) ≫ μ := by
  apply lift_left_mul_ext μ
  nth_rw 2 [← Category.comp_id μ]
  rw [← comp_lift]; rw [Category.assoc]; rw [left_inv]; rw [← Category.assoc (β_ A A).hom]; rw [← lift_snd_fst]; rw [lift_map]; rw [lift_lift_assoc]
  nth_rw 2 [← Category.id_comp μ]
  rw [← lift_fst_snd]; rw [← lift_lift_assoc (fst A A ≫ _)]; rw [lift_comp_inv_left]; rw [lift_comp_one_left]; rw [lift_comp_inv_left]; rw [comp_toUnit_assoc]

@[to_additive (attr := reassoc)]
/--
theorem `tensorHom_inv_inv_mul` / 定理 `tensorHom_inv_inv_mul`

English:
theorem tensorHom_inv_inv_mul
  given: [BraidedCategory C] (A : C) [GrpObj A]
  proof: by
  rw [mul_inv A]; rw [SymmetricCategory.symmetry_assoc]

@[to_additive (attr := reassoc)]

中文:
定理 tensorHom_inv_inv_mul
  条件: [BraidedCategory C] (A : C) [GrpObj A]
  证明: by
  rw [mul_inv A]; rw [SymmetricCategory.symmetry_assoc]

@[to_additive (attr := reassoc)]

Depends on / 依赖: SymmetricCategory, SymmetricCategory.symmetry_assoc, mul_inv, symmetry_assoc
-/
theorem tensorHom_inv_inv_mul [BraidedCategory C] (A : C) [GrpObj A] :
    (ι[A] otimesₘ ι[A]) ≫ μ = (β_ A A).hom ≫ μ ≫ ι := by
  rw [mul_inv A]; rw [SymmetricCategory.symmetry_assoc]

@[to_additive (attr := reassoc)]
/--
lemma `mul_inv_rev` / 引理 `mul_inv_rev`

English:
lemma mul_inv_rev
  given: [BraidedCategory C] (G : C) [GrpObj G]
  proof: by simp [tensorHom_inv_inv_mul]

中文:
引理 mul_inv_rev
  条件: [BraidedCategory C] (G : C) [GrpObj G]
  证明: by simp [tensorHom_inv_inv_mul]

Depends on / 依赖: tensorHom_inv_inv_mul
-/
lemma mul_inv_rev [BraidedCategory C] (G : C) [GrpObj G] :
    μ ≫ ι = (ι[G] otimesₘ ι) ≫ (β_ _ _).hom ≫ μ := by simp [tensorHom_inv_inv_mul]

/-- The map `(· * f)`. -/
@[to_additive (attr := simps) /-- The map `(· + f)`. -/]
/--
Definition of `mulRight` / `mulRight` 的定义

English:
definition mulRight
  signature: {A : C} [GrpObj A] (f : 𝟙_ C ⟶ A)
  body: lift (𝟙 _) (toUnit _ ≫ f) ≫ μ
  inv := lift (𝟙 _) (toUnit _ ≫ f ≫ ι) ≫ μ
  hom_inv_id := by simp [comp_lift_assoc, lift_lift_assoc, ← comp_lift]
  inv_hom_id := by simp [comp_lift_assoc, lift_lift_assoc, ← comp_lift]

@[to_additive (attr := simp)]

中文:
定义 mulRight
  签名: {A : C} [GrpObj A] (f : 𝟙_ C ⟶ A)
  定义体: lift (𝟙 _) (toUnit _ ≫ f) ≫ μ
  inv := lift (𝟙 _) (toUnit _ ≫ f ≫ ι) ≫ μ
  hom_inv_id := by simp [comp_lift_assoc, lift_lift_assoc, ← comp_lift]
  inv_hom_id := by simp [comp_lift_assoc, lift_lift_assoc, ← comp_lift]

@[to_additive (attr := simp)]

Depends on / 依赖: toUnit
-/
def mulRight {A : C} [GrpObj A] (f : 𝟙_ C ⟶ A) : A ≅ A where
  hom := lift (𝟙 _) (toUnit _ ≫ f) ≫ μ
  inv := lift (𝟙 _) (toUnit _ ≫ f ≫ ι) ≫ μ
  hom_inv_id := by simp [comp_lift_assoc, lift_lift_assoc, ← comp_lift]
  inv_hom_id := by simp [comp_lift_assoc, lift_lift_assoc, ← comp_lift]

@[to_additive (attr := simp)]
/--
lemma `mulRight_one` / 引理 `mulRight_one`

English:
lemma mulRight_one
  given: (A : C) [GrpObj A]
  statement: mulRight η[A] = Iso.refl A
  proof: by
  ext; simp

中文:
引理 mulRight_one
  条件: (A : C) [GrpObj A]
  结论: mulRight η[A] = Iso.refl A
  证明: by
  ext; simp
-/
lemma mulRight_one (A : C) [GrpObj A] : mulRight η[A] = Iso.refl A := by
  ext; simp

/-- The associativity diagram of a group object is Cartesian.

In fact, any monoid object whose associativity diagram is Cartesian can be made into a group object
(we do not prove this in this file), so we should expect that many properties of group objects
follow from this result. -/
@[to_additive /-- The associativity diagram of an additive group object is Cartesian.

In fact, any additive monoid object whose associativity diagram is Cartesian can be made into an
additive group object (we do not prove this in this file), so we should expect that many properties
of additive group objects follow from this result. -/]
/--
theorem `isPullback` / 定理 `isPullback`

English:
theorem isPullback
  given: (A : C) [GrpObj A]
  proof: by simp
isLimit' := Nonempty.intro PullbackCone.IsLimit.mk _
    (fun s => lift
      (lift
        (s.snd ≫ fst _ _)
        (lift (s.snd ≫ fst _ _ ≫ ι) (s.fst ≫ fst _ _) ≫ μ))
      (s.fst ≫ snd _ _))
    (by
      refine fun s => CartesianMonoidalCategory.hom_ext _ _ ?_ (by simp)
      simp only 

中文:
定理 isPullback
  条件: (A : C) [GrpObj A]
  证明: by simp
isLimit' := Nonempty.intro PullbackCone.IsLimit.mk _
    (fun s => lift
      (lift
        (s.snd ≫ fst _ _)
        (lift (s.snd ≫ fst _ _ ≫ ι) (s.fst ≫ fst _ _) ≫ μ))
      (s.fst ≫ snd _ _))
    (by
      refine fun s => CartesianMonoidalCategory.hom_ext _ _ ?_ (by simp)
      simp only 

Depends on / 依赖: CartesianMonoidalCategory, CartesianMonoidalCategory.hom_ext, IsLimit, Nonempty, Nonempty.intro, PullbackCone, PullbackCone.IsLimit.mk, hom_ext, isLimit, lift_comp_inv_right, lift_comp_one_left, lift_fst, lift_lift_assoc, lift_lift_associator_hom_assoc, lift_whiskerLef, lift_whiskerRight, s.fst, s.snd
-/
theorem isPullback (A : C) [GrpObj A] :
    IsPullback (μ ▷ A) ((α_ A A A).hom ≫ (A ◁ μ)) μ μ where
  w := by simp
isLimit' := Nonempty.intro PullbackCone.IsLimit.mk _
    (fun s => lift
      (lift
        (s.snd ≫ fst _ _)
        (lift (s.snd ≫ fst _ _ ≫ ι) (s.fst ≫ fst _ _) ≫ μ))
      (s.fst ≫ snd _ _))
    (by
      refine fun s => CartesianMonoidalCategory.hom_ext _ _ ?_ (by simp)
      simp only [lift_whiskerRight, lift_fst]
      rw [← lift_lift_assoc]; rw [← assoc]; rw [lift_comp_inv_right]; rw [lift_comp_one_left])
    (by
      refine fun s => CartesianMonoidalCategory.hom_ext _ _ (by simp) ?_
      simp only [lift_lift_associator_hom_assoc, lift_whiskerLeft, lift_snd]
      have : lift (s.snd ≫ fst _ _ ≫ ι) (s.fst ≫ fst _ _) ≫ μ =
          lift (s.snd ≫ snd _ _) (s.fst ≫ snd _ _ ≫ ι) ≫ μ := by
        rw [← assoc s.fst]; rw [eq_lift_inv_right]; rw [lift_lift_assoc]; rw [← assoc s.snd]; rw [lift_inv_left_eq]; rw [lift_comp_fst_snd]; rw [lift_comp_fst_snd]; rw [s.condition]
      rw [this]; rw [lift_lift_assoc]; rw [← assoc]; rw [lift_comp_inv_left]; rw [lift_comp_one_right])
    (by
      intro s m hm₁ hm₂
      refine CartesianMonoidalCategory.hom_ext _ _ (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_) ?_
      · simpa using hm₂ =≫ fst _ _
      · have h : m ≫ fst _ _ ≫ fst _ _ = s.snd ≫ fst _ _ := by simpa using hm₂ =≫ fst _ _
        have := hm₁ =≫ fst _ _
        simp only [assoc, whiskerRight_fst, lift_fst, lift_snd] at this ⊢
        rw [← assoc]; rw [← lift_comp_fst_snd (m ≫ _)]; rw [assoc]; rw [assoc]; rw [h] at this
        rwa [← assoc s.snd, eq_lift_inv_left]
      · simpa using hm₁ =≫ snd _ _)

/-- Morphisms of group objects preserve inverses. -/
@[to_additive (attr := reassoc (attr := simp))
/-- Morphisms of group objects preserve negations. -/]
/--
theorem `inv_hom` / 定理 `inv_hom`

English:
theorem inv_hom
  given: [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
  statement: ι ≫ f = f ≫ ι
  proof: by
  suffices lift (lift f (ι ≫ f)) f =
      lift (lift f (f ≫ ι)) f by simpa using (this =≫ fst _ _) =≫ snd _ _
  apply (isPullback B).hom_ext <;> apply CartesianMonoidalCategory.hom_ext <;>
    simp [lift_inv_comp_right, lift_inv_comp_left]

@[to_additive]

中文:
定理 inv_hom
  条件: [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
  结论: ι ≫ f = f ≫ ι
  证明: by
  suffices lift (lift f (ι ≫ f)) f =
      lift (lift f (f ≫ ι)) f by simpa using (this =≫ fst _ _) =≫ snd _ _
  apply (isPullback B).hom_ext <;> apply CartesianMonoidalCategory.hom_ext <;>
    simp [lift_inv_comp_right, lift_inv_comp_left]

@[to_additive]

Depends on / 依赖: CartesianMonoidalCategory, CartesianMonoidalCategory.hom_ext, hom_ext, isPullback, lift_inv_comp_left, lift_inv_comp_right
-/
theorem inv_hom [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] : ι ≫ f = f ≫ ι := by
  suffices lift (lift f (ι ≫ f)) f =
      lift (lift f (f ≫ ι)) f by simpa using (this =≫ fst _ _) =≫ snd _ _
  apply (isPullback B).hom_ext <;> apply CartesianMonoidalCategory.hom_ext <;>
    simp [lift_inv_comp_right, lift_inv_comp_left]

@[to_additive]
/--
lemma `toMonObj_injective` / 引理 `toMonObj_injective`

English:
lemma toMonObj_injective
  given: {X : C}
  proof: by
  intro h₁ h₂ e
  suffices h₁.inv = h₂.inv by cases h₁; congr!
  apply lift_left_mul_ext (𝟙 _)
  rw [left_inv]
  convert! @left_inv _ _ _ _ h₁ using 2
  exacts [congr(($e.symm).mul), congr(($e.symm).one)]

@[to_additive (attr := ext)]

中文:
引理 toMonObj_injective
  条件: {X : C}
  证明: by
  intro h₁ h₂ e
  suffices h₁.inv = h₂.inv by cases h₁; congr!
  apply lift_left_mul_ext (𝟙 _)
  rw [left_inv]
  convert! @left_inv _ _ _ _ h₁ using 2
  exacts [congr(($e.symm).mul), congr(($e.symm).one)]

@[to_additive (attr := ext)]

Depends on / 依赖: convert, e.symm, exacts, left_inv, lift_left_mul_ext
-/
lemma toMonObj_injective {X : C} :
    Function.Injective (@GrpObj.toMonObj C ‹_› ‹_› X) := by
  intro h₁ h₂ e
  suffices h₁.inv = h₂.inv by cases h₁; congr!
  apply lift_left_mul_ext (𝟙 _)
  rw [left_inv]
  convert! @left_inv _ _ _ _ h₁ using 2
  exacts [congr(($e.symm).mul), congr(($e.symm).one)]

@[to_additive (attr := ext)]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {X : C} (h₁ h₂ : GrpObj X) (H : h₁.toMonObj = h₂.toMonObj)
  statement: h₁ = h₂
  proof: GrpObj.toMonObj_injective H

中文:
引理 ext
  条件: {X : C} (h₁ h₂ : GrpObj X) (H : h₁.toMonObj = h₂.toMonObj)
  结论: h₁ = h₂
  证明: GrpObj.toMonObj_injective H

Depends on / 依赖: GrpObj, GrpObj.toMonObj_injective, toMonObj_injective
-/
lemma ext {X : C} (h₁ h₂ : GrpObj X) (H : h₁.toMonObj = h₂.toMonObj) : h₁ = h₂ :=
  GrpObj.toMonObj_injective H

-- Note: `Invertible` has no additive variant
/-- A monoid object with invertible homs is a group object. -/
@[instance_reducible]
/--
Definition of `ofInvertible` / `ofInvertible` 的定义

English:
definition ofInvertible
  signature: (G : C) [MonObj G] (h : forall X (f : X ⟶ G), Invertible f)
  body: Yoneda.fullyFaithful.preimage
    ⟨fun X => ↾fun f => (h X.unop f).invOf, fun X Y f => by
      ext g
      simp only [yoneda_obj_map, TypeCat.Fun.toFun_apply, comp_apply,
        ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk, invOf_eq_iff_left]
      rw [← comp_mul]; rw [invOf_mul_self]; rw [comp_

中文:
定义 ofInvertible
  签名: (G : C) [MonObj G] (h : 对任意 X (f : X ⟶ G), Invertible f)
  定义体: Yoneda.fullyFaithful.preimage
    ⟨fun X => ↾fun f => (h X.unop f).invOf, fun X Y f => by
      ext g
      simp only [yoneda_obj_map, TypeCat.Fun.toFun_apply, comp_apply,
        ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk, invOf_eq_iff_left]
      rw [← comp_mul]; rw [invOf_mul_self]; rw [comp_

Depends on / 依赖: Yoneda, Yoneda.fullyFaithful.preimage, fullyFaithful, preimage
-/
def ofInvertible (G : C) [MonObj G] (h : forall X (f : X ⟶ G), Invertible f) : GrpObj G where
  inv := Yoneda.fullyFaithful.preimage
    ⟨fun X => ↾fun f => (h X.unop f).invOf, fun X Y f => by
      ext g
      simp only [yoneda_obj_map, TypeCat.Fun.toFun_apply, comp_apply,
        ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk, invOf_eq_iff_left]
      rw [← comp_mul]; rw [invOf_mul_self]; rw [comp_one]⟩
  left_inv := by simp [Yoneda.fullyFaithful_preimage, ← Hom.mul_def, Hom.one_def]
  right_inv := by simp [Yoneda.fullyFaithful_preimage, ← Hom.mul_def, Hom.one_def]

namespace tensorObj
variable [BraidedCategory C] {G H : C} [GrpObj G] [GrpObj H]

@[to_additive]
/--
Instance `instTensorObj` / 实例 `instTensorObj`

English:
instance instTensorObj
  signature: : GrpObj (G otimes H) where
  body: ι otimesₘ ι

中文:
实例 instTensorObj
  签名: : GrpObj (G otimes H) where
  定义体: ι otimesₘ ι
-/
instance instTensorObj : GrpObj (G otimes H) where
  inv := ι otimesₘ ι

attribute [simps inv] instTensorObj
attribute [simps neg] AddGrpObj.tensorObj.instTensorObj

end GrpObj.tensorObj

namespace Grp

section

variable (C)

/-- The forgetful functor from group objects to monoid objects. -/
@[to_additive (attr := simps! obj_X)
/-- The forgetful functor from additive group objects to additive monoid objects. -/]
/--
Definition of `forget₂Mon` / `forget₂Mon` 的定义

English:
definition forget₂Mon
  signature: : Grp C ⥤ Mon C
  body: inducedFunctor Grp.toMon

中文:
定义 forget₂Mon
  签名: : Grp C ⥤ Mon C
  定义体: inducedFunctor Grp.toMon

Depends on / 依赖: Grp.toMon, inducedFunctor
-/
def forget₂Mon : Grp C ⥤ Mon C :=
  inducedFunctor Grp.toMon

/-- The forgetful functor from group objects to monoid objects is fully faithful. -/
@[to_additive
/-- The forgetful functor from additive group objects to additive monoid objects
is fully faithful. -/]
/--
Definition of `fullyFaithfulForget₂Mon` / `fullyFaithfulForget₂Mon` 的定义

English:
definition fullyFaithfulForget₂Mon
  signature: : (forget₂Mon C).FullyFaithful
  body: fullyFaithfulInducedFunctor _

中文:
定义 fullyFaithfulForget₂Mon
  签名: : (forget₂Mon C).FullyFaithful
  定义体: fullyFaithfulInducedFunctor _

Depends on / 依赖: fullyFaithfulInducedFunctor
-/
def fullyFaithfulForget₂Mon : (forget₂Mon C).FullyFaithful :=
  fullyFaithfulInducedFunctor _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂Mon C).Full
  body: InducedCategory.full _

中文:
实例 :
  签名: (forget₂Mon C).Full
  定义体: InducedCategory.full _
-/
@[to_additive] instance : (forget₂Mon C).Full := InducedCategory.full _
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂Mon C).Faithful
  body: InducedCategory.faithful _

中文:
实例 :
  签名: (forget₂Mon C).Faithful
  定义体: InducedCategory.faithful _
-/
@[to_additive] instance : (forget₂Mon C).Faithful := InducedCategory.faithful _

variable {C}

@[to_additive (attr := simp) forget₂AddMon_obj_zero]
/--
theorem `forget₂Mon_obj_one` / 定理 `forget₂Mon_obj_one`

English:
theorem forget₂Mon_obj_one
  given: (A : Grp C)
  statement: η[((forget₂Mon C).obj A).X] = η[A.X]
  proof: rfl

@[to_additive (attr := simp) forget₂AddMon_obj_add]

中文:
定理 forget₂Mon_obj_one
  条件: (A : Grp C)
  结论: η[((forget₂Mon C).obj A).X] = η[A.X]
  证明: rfl

@[to_additive (attr := simp) forget₂AddMon_obj_add]
-/
theorem forget₂Mon_obj_one (A : Grp C) : η[((forget₂Mon C).obj A).X] = η[A.X] :=
  rfl

@[to_additive (attr := simp) forget₂AddMon_obj_add]
/--
theorem `forget₂Mon_obj_mul` / 定理 `forget₂Mon_obj_mul`

English:
theorem forget₂Mon_obj_mul
  given: (A : Grp C)
  statement: μ[((forget₂Mon C).obj A).X] = μ[A.X]
  proof: rfl

@[to_additive (attr := simp) forget₂AddMon_map_hom]

中文:
定理 forget₂Mon_obj_mul
  条件: (A : Grp C)
  结论: μ[((forget₂Mon C).obj A).X] = μ[A.X]
  证明: rfl

@[to_additive (attr := simp) forget₂AddMon_map_hom]
-/
theorem forget₂Mon_obj_mul (A : Grp C) : μ[((forget₂Mon C).obj A).X] = μ[A.X] :=
  rfl

@[to_additive (attr := simp) forget₂AddMon_map_hom]
/--
theorem `forget₂Mon_map_hom` / 定理 `forget₂Mon_map_hom`

English:
theorem forget₂Mon_map_hom
  given: {A B : Grp C} (f : A ⟶ B)
  proof: rfl

中文:
定理 forget₂Mon_map_hom
  条件: {A B : Grp C} (f : A ⟶ B)
  证明: rfl
-/
theorem forget₂Mon_map_hom {A B : Grp C} (f : A ⟶ B) :
    ((forget₂Mon C).map f).hom = f.hom.hom :=
  rfl

variable (C)

/-- The forgetful functor from group objects to the ambient category. -/
@[to_additive (attr := simps!)
/-- The forgetful functor from additive group objects to the ambient category. -/]
/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: : Grp C ⥤ C
  body: forget₂Mon C ⋙ Mon.forget C

@[to_additive]

中文:
定义 forget
  签名: : Grp C ⥤ C
  定义体: forget₂Mon C ⋙ Mon.forget C

@[to_additive]

Depends on / 依赖: Mon.forget, forget
-/
def forget : Grp C ⥤ C :=
  forget₂Mon C ⋙ Mon.forget C

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget C).Faithful

中文:
实例 :
  签名: (forget C).Faithful
-/
instance : (forget C).Faithful where

@[to_additive (attr := simp) forget₂AddMon_comp_forget]
/--
theorem `forget₂Mon_comp_forget` / 定理 `forget₂Mon_comp_forget`

English:
theorem forget₂Mon_comp_forget
  statement: forget₂Mon C ⋙ Mon.forget C = forget C
  proof: rfl

@[to_additive]

中文:
定理 forget₂Mon_comp_forget
  结论: forget₂Mon C ⋙ Mon.forget C = forget C
  证明: rfl

@[to_additive]
-/
theorem forget₂Mon_comp_forget : forget₂Mon C ⋙ Mon.forget C = forget C := rfl

@[to_additive]
instance {G H : Grp C} {f : G ⟶ H} [IsIso f] : IsIso f.hom.hom :=
inferInstanceAs IsIso (forget C).map f

end

/-- Construct an isomorphism of group objects by giving a monoid isomorphism between the underlying
objects. -/
@[to_additive (attr := simps!)
/-- Construct an isomorphism of additive group objects by giving an additive monoid
isomorphism between the underlying objects. -/]
/--
Definition of `mkIso'` / `mkIso'` 的定义

English:
definition mkIso'
  signature: {G H : C} (e : G ≅ H) [GrpObj G] [GrpObj H] [IsMonHom e.hom]
  body: (fullyFaithfulForget₂Mon C).preimageIso (Mon.mkIso' e)

中文:
定义 mkIso'
  签名: {G H : C} (e : G ≅ H) [GrpObj G] [GrpObj H] [IsMonHom e.hom]
  定义体: (fullyFaithfulForget₂Mon C).preimageIso (Mon.mkIso' e)

Depends on / 依赖: Mon.mkIso, preimageIso
-/
def mkIso' {G H : C} (e : G ≅ H) [GrpObj G] [GrpObj H] [IsMonHom e.hom] : mk G ≅ mk H :=
  (fullyFaithfulForget₂Mon C).preimageIso (Mon.mkIso' e)

/-- Construct an isomorphism of group objects by giving an isomorphism between the underlying
objects and checking compatibility with unit and multiplication only in the forward direction. -/
@[to_additive (attr := simps! -isSimp)
/-- Construct an isomorphism of additive group objects by giving an isomorphism between
the underlying objects and checking compatibility with zero and addition only in the
forward direction. -/]
/--
Definition of `mkIso` / `mkIso` 的定义

English:
abbreviation mkIso
  signature: {G H : Grp C} (e : G.X ≅ H.X) (one_f : η[G.X] ≫ e.hom = η[H.X] := by cat_disch)
  body: have : IsMonHom e.hom := ⟨one_f, mul_f⟩
  mkIso' e

@[to_additive]

中文:
缩写 mkIso
  签名: {G H : Grp C} (e : G.X ≅ H.X) (one_f : η[G.X] ≫ e.hom = η[H.X] := by cat_disch)
  定义体: have : IsMonHom e.hom := ⟨one_f, mul_f⟩
  mkIso' e

@[to_additive]

Depends on / 依赖: IsMonHom, cat_disch, e.hom, mul_f, one_f
-/
abbrev mkIso {G H : Grp C} (e : G.X ≅ H.X) (one_f : η[G.X] ≫ e.hom = η[H.X] := by cat_disch)
    (mul_f : μ[G.X] ≫ e.hom = (e.hom otimesₘ e.hom) ≫ μ[H.X] := by cat_disch) : G ≅ H :=
  have : IsMonHom e.hom := ⟨one_f, mul_f⟩
  mkIso' e

@[to_additive]
/--
Instance `uniqueHomFromTrivial` / 实例 `uniqueHomFromTrivial`

English:
instance uniqueHomFromTrivial
  signature: (A : Grp C)
  body: (show _ ≃ (Mon.trivial C ⟶ A.toMon) from InducedCategory.homEquiv).unique

@[to_additive]

中文:
实例 uniqueHomFromTrivial
  签名: (A : Grp C)
  定义体: (show _ ≃ (Mon.trivial C ⟶ A.toMon) from InducedCategory.homEquiv).unique

@[to_additive]

Depends on / 依赖: A.toMon, InducedCategory, InducedCategory.homEquiv, Mon.trivial, homEquiv, unique
-/
instance uniqueHomFromTrivial (A : Grp C) : Unique (trivial C ⟶ A) :=
  (show _ ≃ (Mon.trivial C ⟶ A.toMon) from InducedCategory.homEquiv).unique

@[to_additive]
/--
Instance `uniqueHomToTrivial` / 实例 `uniqueHomToTrivial`

English:
instance uniqueHomToTrivial
  signature: (A : Grp C)
  body: (show _ ≃ (A.toMon ⟶ Mon.trivial C) from InducedCategory.homEquiv).unique

中文:
实例 uniqueHomToTrivial
  签名: (A : Grp C)
  定义体: (show _ ≃ (A.toMon ⟶ Mon.trivial C) from InducedCategory.homEquiv).unique

Depends on / 依赖: A.toMon, InducedCategory, InducedCategory.homEquiv, Mon.trivial, homEquiv, unique
-/
instance uniqueHomToTrivial (A : Grp C) : Unique (A ⟶ trivial C) :=
  (show _ ≃ (A.toMon ⟶ Mon.trivial C) from InducedCategory.homEquiv).unique

variable (C) in
@[to_additive]
/--
lemma `isZero_trivial` / 引理 `isZero_trivial`

English:
lemma isZero_trivial
  statement: IsZero (trivial C) where
  proof: nonempty_unique (trivial C ⟶ A)
  unique_from A := nonempty_unique (A ⟶ trivial C)

@[to_additive]

中文:
引理 isZero_trivial
  结论: IsZero (trivial C) where
  证明: nonempty_unique (trivial C ⟶ A)
  unique_from A := nonempty_unique (A ⟶ trivial C)

@[to_additive]

Depends on / 依赖: nonempty_unique
-/
lemma isZero_trivial : IsZero (trivial C) where
  unique_to A := nonempty_unique (trivial C ⟶ A)
  unique_from A := nonempty_unique (A ⟶ trivial C)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasZeroObject (Grp C)
  body: ⟨Grp.trivial C, isZero_trivial C⟩

@[to_additive]

中文:
实例 :
  签名: HasZeroObject (Grp C)
  定义体: ⟨Grp.trivial C, isZero_trivial C⟩

@[to_additive]

Depends on / 依赖: Grp.trivial, isZero_trivial
-/
instance : HasZeroObject (Grp C) where
  zero := ⟨Grp.trivial C, isZero_trivial C⟩

@[to_additive]
noncomputable instance (G H : Grp C) : Zero (G ⟶ H) where
  zero := Grp.homMk (toUnit _ ≫ η)

@[to_additive (attr := simp)]
/--
lemma `zero_hom` / 引理 `zero_hom`

English:
lemma zero_hom
  given: (G H : Grp C)
  statement: (0 : G ⟶ H).hom = 0
  proof: rfl

@[to_additive]

中文:
引理 zero_hom
  条件: (G H : Grp C)
  结论: (0 : G ⟶ H).hom = 0
  证明: rfl

@[to_additive]
-/
lemma zero_hom (G H : Grp C) : (0 : G ⟶ H).hom = 0 := rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasZeroMorphisms (Grp C)

中文:
实例 :
  签名: HasZeroMorphisms (Grp C)
-/
noncomputable instance : HasZeroMorphisms (Grp C) where

/-! ### `Grp C` is cartesian-monoidal -/

variable [BraidedCategory C] {G H H₁ H₂ : Grp C}

@[to_additive (attr := simps! tensorObj_X tensorHom_hom)]
/--
Instance `instMonoidalCategoryStruct` / 实例 `instMonoidalCategoryStruct`

English:
instance instMonoidalCategoryStruct
  signature: : MonoidalCategoryStruct (Grp C) where
  body: ⟨G.X otimes H.X⟩
  tensorHom f g := homMk' (tensorHom (C := Mon C) f.hom g.hom)
  whiskerRight f G := homMk' (whiskerRight (C := Mon C) f.hom G.toMon)
  whiskerLeft G _ _ f := homMk' (MonoidalCategoryStruct.whiskerLeft (C := Mon C) G.toMon f.hom)
  tensorUnit := ⟨𝟙_ C⟩
  associator X Y Z :=
    (Grp

中文:
实例 instMonoidalCategoryStruct
  签名: : MonoidalCategoryStruct (Grp C) where
  定义体: ⟨G.X otimes H.X⟩
  tensorHom f g := homMk' (tensorHom (C := Mon C) f.hom g.hom)
  whiskerRight f G := homMk' (whiskerRight (C := Mon C) f.hom G.toMon)
  whiskerLeft G _ _ f := homMk' (MonoidalCategoryStruct.whiskerLeft (C := Mon C) G.toMon f.hom)
  tensorUnit := ⟨𝟙_ C⟩
  associator X Y Z :=
    (Grp

Depends on / 依赖: otimes
-/
instance instMonoidalCategoryStruct : MonoidalCategoryStruct (Grp C) where
  tensorObj G H := ⟨G.X otimes H.X⟩
  tensorHom f g := homMk' (tensorHom (C := Mon C) f.hom g.hom)
  whiskerRight f G := homMk' (whiskerRight (C := Mon C) f.hom G.toMon)
  whiskerLeft G _ _ f := homMk' (MonoidalCategoryStruct.whiskerLeft (C := Mon C) G.toMon f.hom)
  tensorUnit := ⟨𝟙_ C⟩
  associator X Y Z :=
    (Grp.fullyFaithfulForget₂Mon C).preimageIso (associator X.toMon Y.toMon Z.toMon)
  leftUnitor G := (Grp.fullyFaithfulForget₂Mon C).preimageIso (leftUnitor G.toMon)
  rightUnitor G := (Grp.fullyFaithfulForget₂Mon C).preimageIso (rightUnitor G.toMon)

@[to_additive (attr := simp)]
/--
lemma `tensorUnit_X` / 引理 `tensorUnit_X`

English:
lemma tensorUnit_X
  statement: (𝟙_ (Grp C)).X = 𝟙_ C
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 tensorUnit_X
  结论: (𝟙_ (Grp C)).X = 𝟙_ C
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma tensorUnit_X : (𝟙_ (Grp C)).X = 𝟙_ C := rfl

@[to_additive (attr := simp)]
/--
lemma `tensorUnit_one` / 引理 `tensorUnit_one`

English:
lemma tensorUnit_one
  statement: η[(𝟙_ (Grp C)).X] = η[𝟙_ C]
  proof: rfl
@[to_additive (attr := simp)]

中文:
引理 tensorUnit_one
  结论: η[(𝟙_ (Grp C)).X] = η[𝟙_ C]
  证明: rfl
@[to_additive (attr := simp)]
-/
lemma tensorUnit_one : η[(𝟙_ (Grp C)).X] = η[𝟙_ C] := rfl
@[to_additive (attr := simp)]
/--
lemma `tensorUnit_mul` / 引理 `tensorUnit_mul`

English:
lemma tensorUnit_mul
  statement: μ[(𝟙_ (Grp C)).X] = μ[𝟙_ C]
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 tensorUnit_mul
  结论: μ[(𝟙_ (Grp C)).X] = μ[𝟙_ C]
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma tensorUnit_mul : μ[(𝟙_ (Grp C)).X] = μ[𝟙_ C] := rfl

@[to_additive (attr := simp)]
/--
lemma `tensorObj_one` / 引理 `tensorObj_one`

English:
lemma tensorObj_one
  given: (G H : Grp C)
  statement: η[(G otimes H).X] = η[G.X otimes H.X]
  proof: rfl
@[to_additive (attr := simp)]

中文:
引理 tensorObj_one
  条件: (G H : Grp C)
  结论: η[(G otimes H).X] = η[G.X otimes H.X]
  证明: rfl
@[to_additive (attr := simp)]
-/
lemma tensorObj_one (G H : Grp C) : η[(G otimes H).X] = η[G.X otimes H.X] := rfl
@[to_additive (attr := simp)]
/--
lemma `tensorObj_mul` / 引理 `tensorObj_mul`

English:
lemma tensorObj_mul
  given: (G H : Grp C)
  statement: μ[(G otimes H).X] = μ[G.X otimes H.X]
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 tensorObj_mul
  条件: (G H : Grp C)
  结论: μ[(G otimes H).X] = μ[G.X otimes H.X]
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma tensorObj_mul (G H : Grp C) : μ[(G otimes H).X] = μ[G.X otimes H.X] := rfl

@[to_additive (attr := simp)]
/--
lemma `whiskerLeft_hom_hom` / 引理 `whiskerLeft_hom_hom`

English:
lemma whiskerLeft_hom_hom
  given: {G H : Grp C} (f : G ⟶ H) (I : Grp C)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 whiskerLeft_hom_hom
  条件: {G H : Grp C} (f : G ⟶ H) (I : Grp C)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma whiskerLeft_hom_hom {G H : Grp C} (f : G ⟶ H) (I : Grp C) :
    (f ▷ I).hom.hom = f.hom.hom ▷ I.X := rfl

@[to_additive (attr := simp)]
/--
lemma `whiskerRight_hom_hom` / 引理 `whiskerRight_hom_hom`

English:
lemma whiskerRight_hom_hom
  given: (G : Grp C) {H I : Grp C} (f : H ⟶ I)
  proof: rfl


@[to_additive (attr := simp)]

中文:
引理 whiskerRight_hom_hom
  条件: (G : Grp C) {H I : Grp C} (f : H ⟶ I)
  证明: rfl


@[to_additive (attr := simp)]
-/
lemma whiskerRight_hom_hom (G : Grp C) {H I : Grp C} (f : H ⟶ I) :
    (G ◁ f).hom.hom = G.X ◁ f.hom.hom := rfl


@[to_additive (attr := simp)]
/--
lemma `leftUnitor_hom_hom_hom` / 引理 `leftUnitor_hom_hom_hom`

English:
lemma leftUnitor_hom_hom_hom
  given: (G : Grp C)
  statement: (fun_ G).hom.hom.hom = (fun_ G.X).hom
  proof: rfl
@[to_additive (attr := simp)]

中文:
引理 leftUnitor_hom_hom_hom
  条件: (G : Grp C)
  结论: (fun_ G).hom.hom.hom = (fun_ G.X).hom
  证明: rfl
@[to_additive (attr := simp)]
-/
lemma leftUnitor_hom_hom_hom (G : Grp C) : (fun_ G).hom.hom.hom = (fun_ G.X).hom := rfl
@[to_additive (attr := simp)]
/--
lemma `leftUnitor_inv_hom_hom` / 引理 `leftUnitor_inv_hom_hom`

English:
lemma leftUnitor_inv_hom_hom
  given: (G : Grp C)
  statement: (fun_ G).inv.hom.hom = (fun_ G.X).inv
  proof: rfl
@[to_additive (attr := simp)]

中文:
引理 leftUnitor_inv_hom_hom
  条件: (G : Grp C)
  结论: (fun_ G).inv.hom.hom = (fun_ G.X).inv
  证明: rfl
@[to_additive (attr := simp)]
-/
lemma leftUnitor_inv_hom_hom (G : Grp C) : (fun_ G).inv.hom.hom = (fun_ G.X).inv := rfl
@[to_additive (attr := simp)]
/--
lemma `rightUnitor_hom_hom_hom` / 引理 `rightUnitor_hom_hom_hom`

English:
lemma rightUnitor_hom_hom_hom
  given: (G : Grp C)
  statement: (ρ_ G).hom.hom.hom = (ρ_ G.X).hom
  proof: rfl
@[to_additive (attr := simp)]

中文:
引理 rightUnitor_hom_hom_hom
  条件: (G : Grp C)
  结论: (ρ_ G).hom.hom.hom = (ρ_ G.X).hom
  证明: rfl
@[to_additive (attr := simp)]
-/
lemma rightUnitor_hom_hom_hom (G : Grp C) : (ρ_ G).hom.hom.hom = (ρ_ G.X).hom := rfl
@[to_additive (attr := simp)]
/--
lemma `rightUnitor_inv_hom_hom` / 引理 `rightUnitor_inv_hom_hom`

English:
lemma rightUnitor_inv_hom_hom
  given: (G : Grp C)
  statement: (ρ_ G).inv.hom.hom = (ρ_ G.X).inv
  proof: rfl
@[to_additive (attr := simp)]

中文:
引理 rightUnitor_inv_hom_hom
  条件: (G : Grp C)
  结论: (ρ_ G).inv.hom.hom = (ρ_ G.X).inv
  证明: rfl
@[to_additive (attr := simp)]
-/
lemma rightUnitor_inv_hom_hom (G : Grp C) : (ρ_ G).inv.hom.hom = (ρ_ G.X).inv := rfl
@[to_additive (attr := simp)]
/--
lemma `associator_hom_hom_hom` / 引理 `associator_hom_hom_hom`

English:
lemma associator_hom_hom_hom
  given: (G H I : Grp C)
  proof: rfl
@[to_additive (attr := simp)]

中文:
引理 associator_hom_hom_hom
  条件: (G H I : Grp C)
  证明: rfl
@[to_additive (attr := simp)]
-/
lemma associator_hom_hom_hom (G H I : Grp C) :
    (α_ G H I).hom.hom.hom = (α_ G.X H.X I.X).hom := rfl
@[to_additive (attr := simp)]
/--
lemma `associator_inv_hom_hom` / 引理 `associator_inv_hom_hom`

English:
lemma associator_inv_hom_hom
  given: (G H I : Grp C)
  proof: rfl

@[to_additive]

中文:
引理 associator_inv_hom_hom
  条件: (G H I : Grp C)
  证明: rfl

@[to_additive]
-/
lemma associator_inv_hom_hom (G H I : Grp C) :
    (α_ G H I).inv.hom.hom = (α_ G.X H.X I.X).inv := rfl

@[to_additive]
/--
Instance `instMonoidalCategory` / 实例 `instMonoidalCategory`

English:
instance instMonoidalCategory
  signature: : MonoidalCategory (Grp C) where
  body: by intros; ext; simp [tensorHom_def]
  triangle _ _ := by ext; exact triangle _ _

中文:
实例 instMonoidalCategory
  签名: : MonoidalCategory (Grp C) where
  定义体: by intros; ext; simp [tensorHom_def]
  triangle _ _ := by ext; exact triangle _ _

Depends on / 依赖: intros, tensorHom_def, triangle
-/
instance instMonoidalCategory : MonoidalCategory (Grp C) where
  tensorHom_def := by intros; ext; simp [tensorHom_def]
  triangle _ _ := by ext; exact triangle _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[to_additive]
/--
Instance `instCartesianMonoidalCategory` / 实例 `instCartesianMonoidalCategory`

English:
instance instCartesianMonoidalCategory
  signature: : CartesianMonoidalCategory (Grp C) where
  body: .ofUniqueHom (fun G => homMk' (toUnit G.toMon)) fun G f => by ext; exact toUnit_unique ..
  fst G H := homMk' (fst G.toMon H.toMon)
  snd G H := homMk' (snd G.toMon H.toMon)
  tensorProductIsBinaryProduct G H :=
    BinaryFan.IsLimit.mk _ (fun {T} f g => .mk (lift f.hom g.hom))
      (by aesop_cat) 

中文:
实例 instCartesianMonoidalCategory
  签名: : CartesianMonoidalCategory (Grp C) where
  定义体: .ofUniqueHom (fun G => homMk' (toUnit G.toMon)) fun G f => by ext; exact toUnit_unique ..
  fst G H := homMk' (fst G.toMon H.toMon)
  snd G H := homMk' (snd G.toMon H.toMon)
  tensorProductIsBinaryProduct G H :=
    BinaryFan.IsLimit.mk _ (fun {T} f g => .mk (lift f.hom g.hom))
      (by aesop_cat) 

Depends on / 依赖: BinaryFan, BinaryFan.IsLimit.mk, G.toMon, H.toMon, IsLimit, aesop_cat, f.hom, fst_def, g.hom, ofUniqueHom, snd_def, tensorProductIsBinaryProduct, toUnit, toUnit_unique
-/
instance instCartesianMonoidalCategory : CartesianMonoidalCategory (Grp C) where
  isTerminalTensorUnit :=
    .ofUniqueHom (fun G => homMk' (toUnit G.toMon)) fun G f => by ext; exact toUnit_unique ..
  fst G H := homMk' (fst G.toMon H.toMon)
  snd G H := homMk' (snd G.toMon H.toMon)
  tensorProductIsBinaryProduct G H :=
    BinaryFan.IsLimit.mk _ (fun {T} f g => .mk (lift f.hom g.hom))
      (by aesop_cat) (by aesop_cat) (by aesop_cat)
  fst_def G H := by ext; apply fst_def
  snd_def G H := by ext; apply snd_def

@[to_additive (attr := simp)]
/--
lemma `lift_hom` / 引理 `lift_hom`

English:
lemma lift_hom
  given: (f : G ⟶ H₁) (g : G ⟶ H₂)
  statement: (lift f g).hom = (lift f.hom g.hom)
  proof: rfl
@[to_additive (attr := simp)]

中文:
引理 lift_hom
  条件: (f : G ⟶ H₁) (g : G ⟶ H₂)
  结论: (lift f g).hom = (lift f.hom g.hom)
  证明: rfl
@[to_additive (attr := simp)]
-/
lemma lift_hom (f : G ⟶ H₁) (g : G ⟶ H₂) : (lift f g).hom = (lift f.hom g.hom) := rfl
@[to_additive (attr := simp)]
/--
lemma `fst_hom_hom` / 引理 `fst_hom_hom`

English:
lemma fst_hom_hom
  given: (G H : Grp C)
  statement: (fst G H).hom.hom = fst G.X H.X
  proof: rfl
@[to_additive (attr := simp)]

中文:
引理 fst_hom_hom
  条件: (G H : Grp C)
  结论: (fst G H).hom.hom = fst G.X H.X
  证明: rfl
@[to_additive (attr := simp)]
-/
lemma fst_hom_hom (G H : Grp C) : (fst G H).hom.hom = fst G.X H.X := rfl
@[to_additive (attr := simp)]
/--
lemma `snd_hom_hom` / 引理 `snd_hom_hom`

English:
lemma snd_hom_hom
  given: (G H : Grp C)
  statement: (snd G H).hom.hom = snd G.X H.X
  proof: rfl

中文:
引理 snd_hom_hom
  条件: (G H : Grp C)
  结论: (snd G H).hom.hom = snd G.X H.X
  证明: rfl
-/
lemma snd_hom_hom (G H : Grp C) : (snd G H).hom.hom = snd G.X H.X := rfl

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simps)]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂Mon C).Monoidal
  body: 𝟙 _
  «μ» G H := 𝟙 _
  «η» := 𝟙 _
  δ G H := 𝟙 _

中文:
实例 :
  签名: (forget₂Mon C).Monoidal
  定义体: 𝟙 _
  «μ» G H := 𝟙 _
  «η» := 𝟙 _
  δ G H := 𝟙 _
-/
instance : (forget₂Mon C).Monoidal where
  ε := 𝟙 _
  «μ» G H := 𝟙 _
  «η» := 𝟙 _
  δ G H := 𝟙 _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
attribute [local simp] MonObj.tensorObj.mul_def mul_eq_mul comp_mul in
@[to_additive]
/--
Instance `instBraidedCategory` / 实例 `instBraidedCategory`

English:
instance instBraidedCategory
  signature: : BraidedCategory (Grp C)
  body: .ofFaithful (forget₂Mon C) fun G H => Grp.mkIso (β_ G.X H.X)

@[to_additive (attr := simp)]

中文:
实例 instBraidedCategory
  签名: : BraidedCategory (Grp C)
  定义体: .ofFaithful (forget₂Mon C) fun G H => Grp.mkIso (β_ G.X H.X)

@[to_additive (attr := simp)]

Depends on / 依赖: Grp.mkIso, ofFaithful
-/
instance instBraidedCategory : BraidedCategory (Grp C) :=
  .ofFaithful (forget₂Mon C) fun G H => Grp.mkIso (β_ G.X H.X)

@[to_additive (attr := simp)]
/--
lemma `braiding_hom_hom_hom` / 引理 `braiding_hom_hom_hom`

English:
lemma braiding_hom_hom_hom
  given: (G H : Grp C)
  statement: (β_ G H).hom.hom.hom = (β_ G.X H.X).hom
  proof: rfl
@[to_additive (attr := simp)]

中文:
引理 braiding_hom_hom_hom
  条件: (G H : Grp C)
  结论: (β_ G H).hom.hom.hom = (β_ G.X H.X).hom
  证明: rfl
@[to_additive (attr := simp)]
-/
lemma braiding_hom_hom_hom (G H : Grp C) : (β_ G H).hom.hom.hom = (β_ G.X H.X).hom := rfl
@[to_additive (attr := simp)]
/--
lemma `braiding_inv_hom_hom` / 引理 `braiding_inv_hom_hom`

English:
lemma braiding_inv_hom_hom
  given: (G H : Grp C)
  statement: (β_ G H).inv.hom.hom = (β_ G.X H.X).inv
  proof: rfl

中文:
引理 braiding_inv_hom_hom
  条件: (G H : Grp C)
  结论: (β_ G H).inv.hom.hom = (β_ G.X H.X).inv
  证明: rfl
-/
lemma braiding_inv_hom_hom (G H : Grp C) : (β_ G H).inv.hom.hom = (β_ G.X H.X).inv := rfl

end Grp

variable
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [CartesianMonoidalCategory E]

namespace Functor
variable {F F' : C ⥤ D} {G : D ⥤ E}

section Monoidal
variable [F.Monoidal] [F'.Monoidal] [G.Monoidal]

open scoped Obj

/-- The image of a group object under a monoidal functor is a group object. -/
@[to_additive (attr := simp)
/-- The image of an additive group object under a monoidal functor is an additive group object. -/]
/--
Definition of `grpObjObj` / `grpObjObj` 的定义

English:
abbreviation grpObjObj
  signature: {G : C} [GrpObj G]
  body: F.map ι
  left_inv := by
    simp [← Functor.map_id, Functor.Monoidal.lift_μ_assoc,
      Functor.Monoidal.toUnit_ε_assoc, ← Functor.map_comp]
  right_inv := by
    simp [← Functor.map_id, Functor.Monoidal.lift_μ_assoc,
      Functor.Monoidal.toUnit_ε_assoc, ← Functor.map_comp]

scoped[CategoryTheor

中文:
缩写 grpObjObj
  签名: {G : C} [GrpObj G]
  定义体: F.map ι
  left_inv := by
    simp [← Functor.map_id, Functor.Monoidal.lift_μ_assoc,
      Functor.Monoidal.toUnit_ε_assoc, ← Functor.map_comp]
  right_inv := by
    simp [← Functor.map_id, Functor.Monoidal.lift_μ_assoc,
      Functor.Monoidal.toUnit_ε_assoc, ← Functor.map_comp]

scoped[CategoryTheor

Depends on / 依赖: F.map
-/
abbrev grpObjObj {G : C} [GrpObj G] : GrpObj (F.obj G) where
  inv := F.map ι
  left_inv := by
    simp [← Functor.map_id, Functor.Monoidal.lift_μ_assoc,
      Functor.Monoidal.toUnit_ε_assoc, ← Functor.map_comp]
  right_inv := by
    simp [← Functor.map_id, Functor.Monoidal.lift_μ_assoc,
      Functor.Monoidal.toUnit_ε_assoc, ← Functor.map_comp]

scoped[CategoryTheory.Obj] attribute [instance] CategoryTheory.Functor.grpObjObj
  CategoryTheory.Functor.addGrpObjObj

@[to_additive (attr := reassoc, simp) neg_def]
/--
lemma `obj.ι_def` / 引理 `obj.ι_def`

English:
lemma obj.ι_def
  given: {G : C} [GrpObj G]
  statement: ι[F.obj G] = F.map ι
  proof: rfl

中文:
引理 obj.ι_def
  条件: {G : C} [GrpObj G]
  结论: ι[F.obj G] = F.map ι
  证明: rfl
-/
lemma obj.ι_def {G : C} [GrpObj G] : ι[F.obj G] = F.map ι := rfl

open Monoidal

variable (F) in
/-- A finite-product-preserving functor takes group objects to group objects. -/
@[to_additive (attr := simps!)
/-- A finite-product-preserving functor takes additive group objects to additive group objects. -/]
/--
Definition of `mapGrp` / `mapGrp` 的定义

English:
definition mapGrp
  signature: : Grp C ⥤ Grp D where
  body: .mk (F.obj A.X)
  map f := Grp.homMk' (F.mapMon.map f.hom)

@[to_additive]

中文:
定义 mapGrp
  签名: : Grp C ⥤ Grp D where
  定义体: .mk (F.obj A.X)
  map f := Grp.homMk' (F.mapMon.map f.hom)

@[to_additive]

Depends on / 依赖: F.obj
-/
def mapGrp : Grp C ⥤ Grp D where
  obj A := .mk (F.obj A.X)
  map f := Grp.homMk' (F.mapMon.map f.hom)

@[to_additive]
/--
Instance `Faithful.mapGrp` / 实例 `Faithful.mapGrp`

English:
instance Faithful.mapGrp
  signature: [F.Faithful]
  body: (Grp.forget₂Mon _).map_injective
      (F.mapMon.map_injective ((Grp.forget₂Mon _).congr_map hfg))

中文:
实例 Faithful.mapGrp
  签名: [F.Faithful]
  定义体: (Grp.forget₂Mon _).map_injective
      (F.mapMon.map_injective ((Grp.forget₂Mon _).congr_map hfg))
-/
protected instance Faithful.mapGrp [F.Faithful] : F.mapGrp.Faithful where
  map_injective hfg :=
    (Grp.forget₂Mon _).map_injective
      (F.mapMon.map_injective ((Grp.forget₂Mon _).congr_map hfg))

set_option backward.isDefEq.respectTransparency.types false in
/-- If `F : C ⥤ D` is a fully faithful monoidal functor, then
`F.mapGrp : Grp C ⥤ Grp D` is fully faithful too. -/
@[to_additive /-- If `F : C ⥤ D` is a fully faithful monoidal functor, then
`F.mapAddGrp : AddGrp C ⥤ AddGrp D` is fully faithful too. -/]
/--
Definition of `FullyFaithful.mapGrp` / `FullyFaithful.mapGrp` 的定义

English:
definition FullyFaithful.mapGrp
  signature: (hF : F.FullyFaithful)
  body: Grp.homMk' (hF.mapMon.preimage f.hom)

中文:
定义 FullyFaithful.mapGrp
  签名: (hF : F.FullyFaithful)
  定义体: Grp.homMk' (hF.mapMon.preimage f.hom)
-/
protected def FullyFaithful.mapGrp (hF : F.FullyFaithful) : F.mapGrp.FullyFaithful where
  preimage f := Grp.homMk' (hF.mapMon.preimage f.hom)

set_option backward.isDefEq.respectTransparency.types false in
@[to_additive]
/--
Instance `Full.mapGrp` / 实例 `Full.mapGrp`

English:
instance Full.mapGrp
  signature: [F.Full] [F.Faithful]
  body: ((FullyFaithful.ofFullyFaithful F).mapGrp).full

@[to_additive (attr := simp)]

中文:
实例 Full.mapGrp
  签名: [F.Full] [F.Faithful]
  定义体: ((FullyFaithful.ofFullyFaithful F).mapGrp).full

@[to_additive (attr := simp)]
-/
protected instance Full.mapGrp [F.Full] [F.Faithful] : F.mapGrp.Full :=
  ((FullyFaithful.ofFullyFaithful F).mapGrp).full

@[to_additive (attr := simp)]
/--
theorem `mapGrp_id_one` / 定理 `mapGrp_id_one`

English:
theorem mapGrp_id_one
  given: (A : Grp C)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 mapGrp_id_one
  条件: (A : Grp C)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem mapGrp_id_one (A : Grp C) :
    η[((𝟭 C).mapGrp.obj A).X] = 𝟙 _ ≫ η[A.X] :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mapGrp_id_mul` / 定理 `mapGrp_id_mul`

English:
theorem mapGrp_id_mul
  given: (A : Grp C)
  proof: rfl

@[to_additive (attr := simp, reassoc)]

中文:
定理 mapGrp_id_mul
  条件: (A : Grp C)
  证明: rfl

@[to_additive (attr := simp, reassoc)]
-/
theorem mapGrp_id_mul (A : Grp C) :
    μ[((𝟭 C).mapGrp.obj A).X] = 𝟙 _ ≫ μ[A.X] :=
  rfl

@[to_additive (attr := simp, reassoc)]
/--
theorem `comp_mapGrp_one` / 定理 `comp_mapGrp_one`

English:
theorem comp_mapGrp_one
  given: (A : Grp C)
  proof: rfl

@[to_additive (attr := simp, reassoc)]

中文:
定理 comp_mapGrp_one
  条件: (A : Grp C)
  证明: rfl

@[to_additive (attr := simp, reassoc)]
-/
theorem comp_mapGrp_one (A : Grp C) :
    η[((F ⋙ G).mapGrp.obj A).X] = LaxMonoidal.ε (F ⋙ G) ≫ (F ⋙ G).map η[A.X] :=
  rfl

@[to_additive (attr := simp, reassoc)]
/--
theorem `comp_mapGrp_mul` / 定理 `comp_mapGrp_mul`

English:
theorem comp_mapGrp_mul
  given: (A : Grp C)
  proof: rfl

中文:
定理 comp_mapGrp_mul
  条件: (A : Grp C)
  证明: rfl
-/
theorem comp_mapGrp_mul (A : Grp C) :
    μ[((F ⋙ G).mapGrp.obj A).X] = LaxMonoidal.μ (F ⋙ G) _ _ ≫ (F ⋙ G).map μ[A.X] :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The identity functor is also the identity on group objects. -/
@[to_additive (attr := simps!)
/-- The identity functor is also the identity on additive group objects. -/]
/--
Definition of `mapGrpIdIso` / `mapGrpIdIso` 的定义

English:
definition mapGrpIdIso
  signature: : mapGrp (𝟭 C) ≅ 𝟭 (Grp C)
  body: NatIso.ofComponents fun X => Grp.mkIso (.refl _)

中文:
定义 mapGrpIdIso
  签名: : mapGrp (𝟭 C) ≅ 𝟭 (Grp C)
  定义体: NatIso.ofComponents fun X => Grp.mkIso (.refl _)

Depends on / 依赖: Grp.mkIso, NatIso, NatIso.ofComponents, ofComponents
-/
def mapGrpIdIso : mapGrp (𝟭 C) ≅ 𝟭 (Grp C) :=
  NatIso.ofComponents fun X => Grp.mkIso (.refl _)

set_option backward.isDefEq.respectTransparency false in
/-- The composition functor is also the composition on group objects. -/
@[to_additive (attr := simps!)
/-- The composition functor is also the composition on additive group objects. -/]
/--
Definition of `mapGrpCompIso` / `mapGrpCompIso` 的定义

English:
definition mapGrpCompIso
  signature: : (F ⋙ G).mapGrp ≅ F.mapGrp ⋙ G.mapGrp
  body: NatIso.ofComponents fun X => Grp.mkIso (.refl _)

中文:
定义 mapGrpCompIso
  签名: : (F ⋙ G).mapGrp ≅ F.mapGrp ⋙ G.mapGrp
  定义体: NatIso.ofComponents fun X => Grp.mkIso (.refl _)

Depends on / 依赖: Grp.mkIso, NatIso, NatIso.ofComponents, ofComponents
-/
def mapGrpCompIso : (F ⋙ G).mapGrp ≅ F.mapGrp ⋙ G.mapGrp :=
  NatIso.ofComponents fun X => Grp.mkIso (.refl _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Natural transformations between functors lift to group objects. -/
@[to_additive (attr := simps!)
/-- Natural transformations between functors lift to additive group objects. -/]
/--
Definition of `mapGrpNatTrans` / `mapGrpNatTrans` 的定义

English:
definition mapGrpNatTrans
  signature: (f : F ⟶ F')
  body: Grp.homMk' ((mapMonNatTrans f).app X.toMon)

中文:
定义 mapGrpNatTrans
  签名: (f : F ⟶ F')
  定义体: Grp.homMk' ((mapMonNatTrans f).app X.toMon)

Depends on / 依赖: Grp.homMk, X.toMon, mapMonNatTrans
-/
def mapGrpNatTrans (f : F ⟶ F') : F.mapGrp ⟶ F'.mapGrp where
  app X := Grp.homMk' ((mapMonNatTrans f).app X.toMon)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Natural isomorphisms between functors lift to group objects. -/
@[to_additive (attr := simps!)
/-- Natural isomorphisms between functors lift to additive group objects. -/]
/--
Definition of `mapGrpNatIso` / `mapGrpNatIso` 的定义

English:
definition mapGrpNatIso
  signature: (e : F ≅ F')
  body: NatIso.ofComponents fun X => Grp.mkIso (e.app _)

中文:
定义 mapGrpNatIso
  签名: (e : F ≅ F')
  定义体: NatIso.ofComponents fun X => Grp.mkIso (e.app _)

Depends on / 依赖: Grp.mkIso, NatIso, NatIso.ofComponents, e.app, ofComponents
-/
def mapGrpNatIso (e : F ≅ F') : F.mapGrp ≅ F'.mapGrp :=
  NatIso.ofComponents fun X => Grp.mkIso (e.app _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
attribute [local instance] Monoidal.ofChosenFiniteProducts in
/-- `mapGrp` is functorial in the left-exact functor. -/
@[to_additive (attr := simps)
/-- `mapAddGrp` is functorial in the left-exact functor. -/]
/--
Definition of `mapGrpFunctor` / `mapGrpFunctor` 的定义

English:
definition mapGrpFunctor
  signature: : (C ⥤ₗ D) ⥤ Grp C ⥤ Grp D where
  body: F.1.mapGrp
  map {F G} α := { app A := Grp.homMk'' (α.hom.app A.X) }

中文:
定义 mapGrpFunctor
  签名: : (C ⥤ₗ D) ⥤ Grp C ⥤ Grp D where
  定义体: F.1.mapGrp
  map {F G} α := { app A := Grp.homMk'' (α.hom.app A.X) }

Depends on / 依赖: mapGrp
-/
noncomputable def mapGrpFunctor : (C ⥤ₗ D) ⥤ Grp C ⥤ Grp D where
  obj F := F.1.mapGrp
  map {F G} α := { app A := Grp.homMk'' (α.hom.app A.X) }

/-- Pullback a group object along a fully faithful monoidal functor. -/
@[to_additive (attr := simps)
/-- Pullback an additive group object along a fully faithful monoidal functor. -/]
/--
Definition of `FullyFaithful.grpObj` / `FullyFaithful.grpObj` 的定义

English:
abbreviation FullyFaithful.grpObj
  signature: (hF : F.FullyFaithful) (X : C) [GrpObj (F.obj X)]
  body: hF.monObj X
  inv := hF.preimage ι[F.obj X]
left_inv := hF.map_injective by
    simp [OplaxMonoidal.η_of_cartesianMonoidalCategory]
right_inv := hF.map_injective by
    simp [OplaxMonoidal.η_of_cartesianMonoidalCategory]

中文:
缩写 FullyFaithful.grpObj
  签名: (hF : F.FullyFaithful) (X : C) [GrpObj (F.obj X)]
  定义体: hF.monObj X
  inv := hF.preimage ι[F.obj X]
left_inv := hF.map_injective by
    simp [OplaxMonoidal.η_of_cartesianMonoidalCategory]
right_inv := hF.map_injective by
    simp [OplaxMonoidal.η_of_cartesianMonoidalCategory]

Depends on / 依赖: hF.monObj, monObj
-/
abbrev FullyFaithful.grpObj (hF : F.FullyFaithful) (X : C) [GrpObj (F.obj X)] :
    GrpObj X where
  __ := hF.monObj X
  inv := hF.preimage ι[F.obj X]
left_inv := hF.map_injective by
    simp [OplaxMonoidal.η_of_cartesianMonoidalCategory]
right_inv := hF.map_injective by
    simp [OplaxMonoidal.η_of_cartesianMonoidalCategory]

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] MonObj.ofIso_one MonObj.ofIso_mul in
/-- The essential image of a full and faithful functor between cartesian-monoidal categories is the
same on group objects as on objects. -/
@[to_additive (attr := simp)
/-- The essential image of a full and faithful functor between cartesian-monoidal categories is the
same on additive group objects as on objects. -/]
/--
lemma `essImage_mapGrp` / 引理 `essImage_mapGrp`

English:
lemma essImage_mapGrp
  given: [F.Full] [F.Faithful] {G : Grp D}
  proof: by rintro ⟨H, ⟨e⟩⟩; exact ⟨H.X, ⟨(Grp.forget _).mapIso e⟩⟩
  mpr := by
    rintro ⟨H, ⟨e⟩⟩
    let : GrpObj (F.obj H) := .ofIso e.symm
    let : GrpObj H := (FullyFaithful.ofFullyFaithful F).grpObj H
    refine ⟨⟨H⟩, ⟨Grp.mkIso e ?_ ?_⟩⟩ <;> simp

中文:
引理 essImage_mapGrp
  条件: [F.Full] [F.Faithful] {G : Grp D}
  证明: by rintro ⟨H, ⟨e⟩⟩; exact ⟨H.X, ⟨(Grp.forget _).mapIso e⟩⟩
  mpr := by
    rintro ⟨H, ⟨e⟩⟩
    let : GrpObj (F.obj H) := .ofIso e.symm
    let : GrpObj H := (FullyFaithful.ofFullyFaithful F).grpObj H
    refine ⟨⟨H⟩, ⟨Grp.mkIso e ?_ ?_⟩⟩ <;> simp

Depends on / 依赖: F.obj, FullyFaithful, FullyFaithful.ofFullyFaithful, Grp.forget, Grp.mkIso, GrpObj, e.symm, forget, grpObj, mapIso, ofFullyFaithful
-/
lemma essImage_mapGrp [F.Full] [F.Faithful] {G : Grp D} :
    F.mapGrp.essImage G ↔ F.essImage G.X where
  mp := by rintro ⟨H, ⟨e⟩⟩; exact ⟨H.X, ⟨(Grp.forget _).mapIso e⟩⟩
  mpr := by
    rintro ⟨H, ⟨e⟩⟩
    let : GrpObj (F.obj H) := .ofIso e.symm
    let : GrpObj H := (FullyFaithful.ofFullyFaithful F).grpObj H
    refine ⟨⟨H⟩, ⟨Grp.mkIso e ?_ ?_⟩⟩ <;> simp

end Monoidal

section Braided
variable [BraidedCategory C] [BraidedCategory D] (F : C ⥤ D) [F.Braided]

open Monoidal LaxMonoidal

@[to_additive]
/--
Instance `mapGrp.instMonoidal` / 实例 `mapGrp.instMonoidal`

English:
instance mapGrp.instMonoidal
  signature: : F.mapGrp.Monoidal
  body: Functor.CoreMonoidal.toMonoidal
  { εIso := (Grp.fullyFaithfulForget₂Mon _).preimageIso (εIso F.mapMon)
    μIso X Y := (Grp.fullyFaithfulForget₂Mon _).preimageIso (μIso F.mapMon X.toMon Y.toMon)
    μIso_hom_natural_left f Z :=
      (Grp.forget₂Mon _).map_injective (μ_natural_left F.mapMon f.hom Z

中文:
实例 mapGrp.instMonoidal
  签名: : F.mapGrp.Monoidal
  定义体: Functor.CoreMonoidal.toMonoidal
  { εIso := (Grp.fullyFaithfulForget₂Mon _).preimageIso (εIso F.mapMon)
    μIso X Y := (Grp.fullyFaithfulForget₂Mon _).preimageIso (μIso F.mapMon X.toMon Y.toMon)
    μIso_hom_natural_left f Z :=
      (Grp.forget₂Mon _).map_injective (μ_natural_left F.mapMon f.hom Z

Depends on / 依赖: CoreMonoidal, F.mapMon, Functor, Functor.CoreMonoidal.toMonoidal, Grp.forget, Grp.fullyFaithfulForget, X.toMon, Y.toMon, Z.toMon, associativity, f.hom, mapMon, map_injective, preimageIso, toMonoidal
-/
noncomputable instance mapGrp.instMonoidal : F.mapGrp.Monoidal :=
  Functor.CoreMonoidal.toMonoidal
  { εIso := (Grp.fullyFaithfulForget₂Mon _).preimageIso (εIso F.mapMon)
    μIso X Y := (Grp.fullyFaithfulForget₂Mon _).preimageIso (μIso F.mapMon X.toMon Y.toMon)
    μIso_hom_natural_left f Z :=
      (Grp.forget₂Mon _).map_injective (μ_natural_left F.mapMon f.hom Z.toMon)
    μIso_hom_natural_right Z f :=
      (Grp.forget₂Mon _).map_injective (μ_natural_right F.mapMon Z.toMon f.hom)
    associativity X Y Z :=
      (Grp.forget₂Mon _).map_injective (associativity F.mapMon X.toMon Y.toMon Z.toMon)
    left_unitality X :=
      (Grp.forget₂Mon _).map_injective (left_unitality F.mapMon X.toMon)
    right_unitality X :=
      (Grp.forget₂Mon _).map_injective (right_unitality F.mapMon X.toMon) }

@[to_additive]
/--
Instance `mapGrp.instBraided` / 实例 `mapGrp.instBraided`

English:
instance mapGrp.instBraided
  signature: : F.mapGrp.Braided where
  body: (Grp.forget₂Mon _).map_injective (Braided.braided X.toMon Y.toMon)

中文:
实例 mapGrp.instBraided
  签名: : F.mapGrp.Braided where
  定义体: (Grp.forget₂Mon _).map_injective (Braided.braided X.toMon Y.toMon)

Depends on / 依赖: Braided, Braided.braided, Grp.forget, X.toMon, Y.toMon, braided, map_injective
-/
noncomputable instance mapGrp.instBraided : F.mapGrp.Braided where
  braided X Y :=
    (Grp.forget₂Mon _).map_injective (Braided.braided X.toMon Y.toMon)

end Braided
end Functor

open CategoryTheory.Functor

namespace Adjunction
variable {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) [F.Monoidal] [G.Monoidal]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An adjunction of monoidal functors lifts to an adjunction of their lifts to group objects. -/
@[to_additive (attr := simps)
/-- An adjunction of monoidal functors lifts to an adjunction of their lifts
to additive group objects. -/]
/--
Definition of `mapGrp` / `mapGrp` 的定义

English:
definition mapGrp
  signature: : F.mapGrp ⊣ G.mapGrp where
  body: mapGrpIdIso.inv ≫ mapGrpNatTrans a.unit ≫ mapGrpCompIso.hom
  counit := mapGrpCompIso.inv ≫ mapGrpNatTrans a.counit ≫ mapGrpIdIso.hom

中文:
定义 mapGrp
  签名: : F.mapGrp ⊣ G.mapGrp where
  定义体: mapGrpIdIso.inv ≫ mapGrpNatTrans a.unit ≫ mapGrpCompIso.hom
  counit := mapGrpCompIso.inv ≫ mapGrpNatTrans a.counit ≫ mapGrpIdIso.hom

Depends on / 依赖: a.unit, mapGrpCompIso, mapGrpCompIso.hom, mapGrpIdIso, mapGrpIdIso.inv, mapGrpNatTrans
-/
def mapGrp : F.mapGrp ⊣ G.mapGrp where
  unit := mapGrpIdIso.inv ≫ mapGrpNatTrans a.unit ≫ mapGrpCompIso.hom
  counit := mapGrpCompIso.inv ≫ mapGrpNatTrans a.counit ≫ mapGrpIdIso.hom

end Adjunction

namespace Equivalence
variable (e : C ≌ D) [e.functor.Monoidal] [e.inverse.Monoidal]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An equivalence of categories lifts to an equivalence of their group objects. -/
@[to_additive (attr := simps)
/-- An equivalence of categories lifts to an equivalence of their additive group objects. -/]
/--
Definition of `mapGrp` / `mapGrp` 的定义

English:
definition mapGrp
  signature: : Grp C ≌ Grp D where
  body: e.functor.mapGrp
  inverse := e.inverse.mapGrp
  unitIso := mapGrpIdIso.symm ≪≫ mapGrpNatIso e.unitIso ≪≫ mapGrpCompIso
  counitIso := mapGrpCompIso.symm ≪≫ mapGrpNatIso e.counitIso ≪≫ mapGrpIdIso

中文:
定义 mapGrp
  签名: : Grp C ≌ Grp D where
  定义体: e.functor.mapGrp
  inverse := e.inverse.mapGrp
  unitIso := mapGrpIdIso.symm ≪≫ mapGrpNatIso e.unitIso ≪≫ mapGrpCompIso
  counitIso := mapGrpCompIso.symm ≪≫ mapGrpNatIso e.counitIso ≪≫ mapGrpIdIso

Depends on / 依赖: e.functor.mapGrp, functor, mapGrp
-/
def mapGrp : Grp C ≌ Grp D where
  functor := e.functor.mapGrp
  inverse := e.inverse.mapGrp
  unitIso := mapGrpIdIso.symm ≪≫ mapGrpNatIso e.unitIso ≪≫ mapGrpCompIso
  counitIso := mapGrpCompIso.symm ≪≫ mapGrpNatIso e.counitIso ≪≫ mapGrpIdIso

end CategoryTheory.Equivalence
