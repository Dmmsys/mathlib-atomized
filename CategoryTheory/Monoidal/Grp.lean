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

/-- An additive group object internal to a cartesian monoidal category.
Also see the bundled `AddGrp`. -/
/-
**CategoryTheory.AddGrpObj** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：AddGrpObj (X : C) extends AddMonObj X where /-- The negation in a group ob
ject -/ neg : X ⟶ X left_neg (X) : lift neg (𝟙 X) ≫ add = toUnit _ ≫ zero
参数：X : C。
继承自：AddMonObj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive group object internal to a cartesian monoidal category.
Also see the bundled `AddGrp`.
-/
class AddGrpObj (X : C) extends AddMonObj X where
  /-- The negation in a group object -/
  neg : X ⟶ X
  left_neg (X) : lift neg (𝟙 X) ≫ add = toUnit _ ≫ zero := by cat_disch
  right_neg (X) : lift (𝟙 X) neg ≫ add = toUnit _ ≫ zero := by cat_disch

/-- A group object internal to a cartesian monoidal category. Also see the bundled `Grp`. -/
@[to_additive]
/-
**CategoryTheory.GrpObj** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：GrpObj (X : C) extends MonObj X where /-- The inverse in a group object -/
 inv : X ⟶ X left_inv (X) : lift inv (𝟙 X) ≫ mul = toUnit _ ≫ one
参数：X : C。
继承自：MonObj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A group object internal to a cartesian monoidal category. Also see the bundled `
Grp`.
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
/-
**CategoryTheory.GrpObj.instTensorUnit** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.GrpObj`。
形式化陈述：instTensorUnit : GrpObj (𝟙_ C) where inv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instTensorUnit : GrpObj (𝟙_ C) where
  inv := 𝟙 (𝟙_ C)

attribute [simps inv] instTensorUnit
attribute [simps neg] AddGrpObj.instTensorAddUnit

end GrpObj

variable (C) in
/-- An additive group object in a Cartesian monoidal category. -/
/-
**CategoryTheory.AddGrp** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] → [CategoryT
heory.CartesianMonoidalCategory C] → Type (max u₁ v₁)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive group object in a Cartesian monoidal category.
-/
structure AddGrp where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [addGrp : AddGrpObj X]

variable (C) in
/-- A group object in a Cartesian monoidal category. -/
@[to_additive]
/-
**CategoryTheory.Grp** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] → [CategoryT
heory.CartesianMonoidalCategory C] → Type (max u₁ v₁)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A group object in a Cartesian monoidal category.
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
/-
**CategoryTheory.Grp.toMon** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Grp`。
形式化陈述：toMon (A : Grp C) : Mon C
参数：A : Grp C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev toMon (A : Grp C) : Mon C := ⟨A.X⟩

variable (C) in
/-- The trivial group object. -/
@[to_additive (attr := simps!) /-- The trivial additive group object. -/]
/-
**CategoryTheory.Grp.trivial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Grp`。
形式化陈述：trivial : Grp C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial group object.
-/
def trivial : Grp C := { Mon.trivial C with grp := GrpObj.instTensorUnit }

@[to_additive]
/-
**CategoryTheory.Grp.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Grp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Grp C) where
  default := trivial C

@[to_additive]
/-
**CategoryTheory.Grp.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Grp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (Grp C) :=
  inferInstanceAs (Category (InducedCategory _ Grp.toMon))

@[to_additive (attr := simp)]
/-
**CategoryTheory.Grp.id_hom_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Grp`。
形式化陈述：id_hom_hom (A : Grp C) : Mon.Hom.hom (InducedCategory.Hom.hom (𝟙 A)) = 𝟙 A
.X
参数：A : Grp C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_hom_hom (A : Grp C) : Mon.Hom.hom (InducedCategory.Hom.hom (𝟙 A)) = 𝟙 A.X :=
  rfl

@[to_additive (attr := simp, reassoc)]
/-
**CategoryTheory.Grp.comp_hom_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Grp`
。
形式化陈述：comp_hom_hom {R S T : Grp C} (f : R ⟶ S) (g : S ⟶ T) : Mon.Hom.hom (f ≫ g)
.hom = f.hom.hom ≫ g.hom.hom
参数：f : R ⟶ S；g : S ⟶ T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_hom_hom {R S T : Grp C} (f : R ⟶ S) (g : S ⟶ T) :
    Mon.Hom.hom (f ≫ g).hom = f.hom.hom ≫ g.hom.hom :=
  rfl

@[to_additive (attr := ext)]
/-
**CategoryTheory.Grp.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Grp`。
形式化陈述：hom_ext {A B : Grp C} (f g : A ⟶ B) (h : f.hom.hom = g.hom.hom) : f = g
参数：f g : A ⟶ B；h : f.hom.hom = g.hom.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.InducedCategory.hom_ext`：hom_ext {X Y : InducedCategory D
 F} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用定理 `CategoryTheory.Mon.Hom.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Categ
ory.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C}   {M N : CategoryTh
eory.Mon C} {x y…
-/
theorem hom_ext {A B : Grp C} (f g : A ⟶ B) (h : f.hom.hom = g.hom.hom) : f = g :=
  InducedCategory.hom_ext (Mon.Hom.ext h)

/-- Constructor for morphisms in `Grp C`. -/
@[to_additive (attr := simps) /-- Constructor for morphisms in `AddGrp C`. -/]
/-
**CategoryTheory.Grp.homMk'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Grp`。
形式化陈述：homMk' {A B : Grp C} (f : A.toMon ⟶ B.toMon) : A ⟶ B where hom
参数：f : A.toMon ⟶ B.toMon。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms in `Grp C`.
-/
def homMk' {A B : Grp C} (f : A.toMon ⟶ B.toMon) : A ⟶ B where
  hom := f

/-- Construct a morphism `A ⟶ B` of `Grp C` from a map `f : A.X ⟶ A.X` and a `IsMonHom f`
instance. -/
@[to_additive (attr := simps!)
/-- Construct a morphism `A ⟶ B` of `AddGrp C` from a map `f : A.X ⟶ A.X` and a `IsAddMonHom f`
instance.-/]
/-
**CategoryTheory.Grp.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Grp`。
形式化陈述：homMk {A B : Grp C} (f : A.X ⟶ B.X) [IsMonHom f] : A ⟶ B
参数：f : A.X ⟶ B.X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def homMk {A B : Grp C} (f : A.X ⟶ B.X) [IsMonHom f] : A ⟶ B :=
  homMk' (.mk f)

/-- Construct a morphism `Grp.mk G ⟶ Grp.mk H` from a  map `f : G ⟶ H` and a `IsMonHom f`
instance. -/
@[to_additive (attr := simps!)
/-- Construct a morphism `AddGrp.mk G ⟶ AddGrp.mk H` from a  map `f : G ⟶ H` and a `IsAddMonHom f`
instance. -/]
/-
**CategoryTheory.Grp.ofHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Grp`。
形式化陈述：ofHom {A B : C} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] : Grp.mk A 
⟶ Grp.mk B
参数：f : A ⟶ B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofHom {A B : C} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] : Grp.mk A ⟶ Grp.mk B :=
  Grp.homMk f

/-- Constructor for morphisms in `Grp C`. -/
@[to_additive (attr := simps!) /-- Constructor for morphisms in `AddGrp C`. -/]
/-
**CategoryTheory.Grp.homMk''** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Grp`。
形式化陈述：homMk'' {A B : Grp C} (f : A.X ⟶ B.X) (one_f : η ≫ f = η
参数：f : A.X ⟶ B.X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms in `Grp C`.
-/
def homMk'' {A B : Grp C} (f : A.X ⟶ B.X)
    (one_f : η ≫ f = η := by cat_disch)
    (mul_f : μ ≫ f = (f ⊗ₘ f) ≫ μ := by cat_disch) : A ⟶ B :=
  haveI : IsMonHom f := ⟨one_f, mul_f⟩
  homMk f

@[to_additive (attr := simp)]
/-
**CategoryTheory.Grp.id'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Grp`。
形式化陈述：id' (A : Grp C) : (InducedCategory.Hom.hom (𝟙 A) : A.toMon ⟶ A.toMon) = 𝟙 
(A.toMon)
参数：A : Grp C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id' (A : Grp C) :
    (InducedCategory.Hom.hom (𝟙 A) : A.toMon ⟶ A.toMon) = 𝟙 (A.toMon) := rfl

@[to_additive (attr := simp, reassoc)]
/-
**CategoryTheory.Grp.comp'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Grp`。
形式化陈述：comp' {A₁ A₂ A₃ : Grp C} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) : (InducedCategory.Ho
m.hom (f ≫ g : A₁ ⟶ A₃) : A₁.toMon ⟶ A₃.toMon) = f.hom ≫ g.hom
参数：f : A₁ ⟶ A₂；g : A₂ ⟶ A₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp' {A₁ A₂ A₃ : Grp C} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) :
    (InducedCategory.Hom.hom (f ≫ g : A₁ ⟶ A₃) : A₁.toMon ⟶ A₃.toMon) =
      f.hom ≫ g.hom := rfl

end Grp

namespace GrpObj
variable {G X : C} [GrpObj G]

variable {A : C} {B : C}

@[to_additive (attr := reassoc (attr := simp))]
/-
**CategoryTheory.GrpObj.lift_comp_inv_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.GrpObj`。
形式化陈述：lift_comp_inv_right [GrpObj B] (f : A ⟶ B) : lift f (f ≫ ι) ≫ μ = toUnit _
 ≫ η
参数：f : A ⟶ B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…
· 使用定理 `CategoryTheory.GrpObj.right_inv`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {inst_1 : CategoryTheory.CartesianMonoidalCategory C}   (X 
: C) [self : Category…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用引理 `CategoryTheory.SemiCartesianMonoidalCategory.toUnit_unique`：toUnit_uniqu
e {X : C} (f g : X ⟶ 𝟙_ _) : f = g
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.comp_lift_assoc`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.CartesianMon
oidalCategory C]   {V W X Y : C} (f : V ⟶ W) (…
-/
theorem lift_comp_inv_right [GrpObj B] (f : A ⟶ B) :
    lift f (f ≫ ι) ≫ μ = toUnit _ ≫ η := by
  have := f ≫= right_inv B
  rwa [comp_lift_assoc, comp_id, reassoc_of% toUnit_unique (f ≫ toUnit B) (toUnit A)] at this

@[to_additive (attr := reassoc)]
/-
**CategoryTheory.GrpObj.lift_inv_comp_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.GrpObj`。
形式化陈述：lift_inv_comp_right [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] : lift 
f (ι ≫ f) ≫ μ = toUnit _ ≫ η
参数：f : A ⟶ B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.GrpObj.right_inv`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {inst_1 : CategoryTheory.CartesianMonoidalCategory C}   (X 
: C) [self : Category…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.lift_map_assoc`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.CartesianMono
idalCategory C]   {V W X Y Z : C} (f : V ⟶ W)…
· 使用定理 `CategoryTheory.IsMonHom.one_hom`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M N : C}   {i
nst_2 : CategoryTheor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsMonHom.mul_hom`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M N : C}   {i
nst_2 : CategoryTheor…
-/
theorem lift_inv_comp_right [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] :
    lift f (ι ≫ f) ≫ μ = toUnit _ ≫ η := by
  have := right_inv A =≫ f
  rwa [assoc, IsMonHom.mul_hom, assoc, IsMonHom.one_hom, lift_map_assoc, id_comp] at this

@[to_additive (attr := reassoc (attr := simp))]
/-
**CategoryTheory.GrpObj.lift_comp_inv_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.GrpObj`。
形式化陈述：lift_comp_inv_left [GrpObj B] (f : A ⟶ B) : lift (f ≫ ι) f ≫ μ = toUnit _ 
≫ η
参数：f : A ⟶ B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…
· 使用定理 `CategoryTheory.GrpObj.left_inv`：∀ {C : Type u₁} {inst : CategoryTheory.C
ategory.{v₁, u₁} C} {inst_1 : CategoryTheory.CartesianMonoidalCategory C}   (X :
 C) [self : Category…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用引理 `CategoryTheory.SemiCartesianMonoidalCategory.toUnit_unique`：toUnit_uniqu
e {X : C} (f g : X ⟶ 𝟙_ _) : f = g
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.comp_lift_assoc`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.CartesianMon
oidalCategory C]   {V W X Y : C} (f : V ⟶ W) (…
-/
theorem lift_comp_inv_left [GrpObj B] (f : A ⟶ B) :
    lift (f ≫ ι) f ≫ μ = toUnit _ ≫ η := by
  have := f ≫= left_inv B
  rwa [comp_lift_assoc, comp_id, reassoc_of% toUnit_unique (f ≫ toUnit B) (toUnit A)] at this

@[to_additive (attr := reassoc)]
/-
**CategoryTheory.GrpObj.lift_inv_comp_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.GrpObj`。
形式化陈述：lift_inv_comp_left [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] : lift (
ι ≫ f) f ≫ μ = toUnit _ ≫ η
参数：f : A ⟶ B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.GrpObj.left_inv`：∀ {C : Type u₁} {inst : CategoryTheory.C
ategory.{v₁, u₁} C} {inst_1 : CategoryTheory.CartesianMonoidalCategory C}   (X :
 C) [self : Category…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.lift_map_assoc`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.CartesianMono
idalCategory C]   {V W X Y Z : C} (f : V ⟶ W)…
· 使用定理 `CategoryTheory.IsMonHom.one_hom`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M N : C}   {i
nst_2 : CategoryTheor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsMonHom.mul_hom`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M N : C}   {i
nst_2 : CategoryTheor…
-/
theorem lift_inv_comp_left [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] :
    lift (ι ≫ f) f ≫ μ = toUnit _ ≫ η := by
  have := left_inv A =≫ f
  rwa [assoc, IsMonHom.mul_hom, assoc, IsMonHom.one_hom, lift_map_assoc, id_comp] at this

@[to_additive]
/-
**CategoryTheory.GrpObj.eq_lift_inv_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.GrpObj`。
形式化陈述：eq_lift_inv_left [GrpObj B] (f g h : A ⟶ B) : f = lift (g ≫ ι) h ≫ μ ↔ lif
t g f ≫ μ = h
参数：f g h : A ⟶ B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrpObj.lift_comp_inv_right`：lift_comp_inv_right [GrpObj B
] (f : A ⟶ B) : lift f (f ≫ ι) ≫ μ = toUnit _ ≫ η
· 使用定理 `CategoryTheory.MonObj.lift_comp_one_left`：lift_comp_one_left {A : C} {B 
: C} [MonObj B] (f : A ⟶ 𝟙_ C) (g : A ⟶ B) : lift (f ≫ η) g ≫ μ = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.GrpObj.lift_comp_inv_left`：lift_comp_inv_left [GrpObj B] 
(f : A ⟶ B) : lift (f ≫ ι) f ≫ μ = toUnit _ ≫ η
-/
theorem eq_lift_inv_left [GrpObj B] (f g h : A ⟶ B) :
    f = lift (g ≫ ι) h ≫ μ ↔ lift g f ≫ μ = h := by
  refine ⟨?_, ?_⟩ <;> (rintro rfl; simp [← lift_lift_assoc])

@[to_additive]
/-
**CategoryTheory.GrpObj.lift_inv_left_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.GrpObj`。
形式化陈述：lift_inv_left_eq [GrpObj B] (f g h : A ⟶ B) : lift (f ≫ ι) g ≫ μ = h ↔ g =
 lift f h ≫ μ
参数：f g h : A ⟶ B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `CategoryTheory.GrpObj.eq_lift_inv_left`：eq_lift_inv_left [GrpObj B] (f g
 h : A ⟶ B) : f = lift (g ≫ ι) h ≫ μ ↔ lift g f ≫ μ = h
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lift_inv_left_eq [GrpObj B] (f g h : A ⟶ B) :
    lift (f ≫ ι) g ≫ μ = h ↔ g = lift f h ≫ μ := by
  rw [eq_comm, eq_lift_inv_left, eq_comm]

@[to_additive]
/-
**CategoryTheory.GrpObj.eq_lift_inv_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.GrpObj`。
形式化陈述：eq_lift_inv_right [GrpObj B] (f g h : A ⟶ B) : f = lift g (h ≫ ι) ≫ μ ↔ li
ft f h ≫ μ = g
参数：f g h : A ⟶ B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonObj.lift_lift_assoc`：lift_lift_assoc {A : C} {B : C} [
MonObj B] (f g h : A ⟶ B) : lift (lift f g ≫ μ) h ≫ μ = lift f (lift g h ≫ μ) ≫ 
μ
· 使用定理 `CategoryTheory.GrpObj.lift_comp_inv_left`：lift_comp_inv_left [GrpObj B] 
(f : A ⟶ B) : lift (f ≫ ι) f ≫ μ = toUnit _ ≫ η
· 使用定理 `CategoryTheory.MonObj.lift_comp_one_right`：lift_comp_one_right {A : C} {
B : C} [MonObj B] (f : A ⟶ B) (g : A ⟶ 𝟙_ C) : lift f (g ≫ η) ≫ μ = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.GrpObj.lift_comp_inv_right`：lift_comp_inv_right [GrpObj B
] (f : A ⟶ B) : lift f (f ≫ ι) ≫ μ = toUnit _ ≫ η
-/
theorem eq_lift_inv_right [GrpObj B] (f g h : A ⟶ B) :
    f = lift g (h ≫ ι) ≫ μ ↔ lift f h ≫ μ = g := by
  refine ⟨?_, ?_⟩ <;> (rintro rfl; simp [lift_lift_assoc])

@[to_additive]
/-
**CategoryTheory.GrpObj.lift_inv_right_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.GrpObj`。
形式化陈述：lift_inv_right_eq [GrpObj B] (f g h : A ⟶ B) : lift f (g ≫ ι) ≫ μ = h ↔ f 
= lift h g ≫ μ
参数：f g h : A ⟶ B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `CategoryTheory.GrpObj.eq_lift_inv_right`：eq_lift_inv_right [GrpObj B] (f
 g h : A ⟶ B) : f = lift g (h ≫ ι) ≫ μ ↔ lift f h ≫ μ = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lift_inv_right_eq [GrpObj B] (f g h : A ⟶ B) :
    lift f (g ≫ ι) ≫ μ = h ↔ f = lift h g ≫ μ := by
  rw [eq_comm, eq_lift_inv_right, eq_comm]

@[to_additive]
/-
**CategoryTheory.GrpObj.lift_left_mul_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.GrpObj`。
形式化陈述：lift_left_mul_ext [GrpObj B] {f g : A ⟶ B} (i : A ⟶ B) (h : lift f i ≫ μ =
 lift g i ≫ μ) : f = g
参数：i : A ⟶ B；h : lift f i ≫ μ = lift g i ≫ μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonObj.lift_comp_one_right`：lift_comp_one_right {A : C} {
B : C} [MonObj B] (f : A ⟶ B) (g : A ⟶ 𝟙_ C) : lift f (g ≫ η) ≫ μ = f
· 使用定理 `CategoryTheory.GrpObj.lift_comp_inv_right`：lift_comp_inv_right [GrpObj B
] (f : A ⟶ B) : lift f (f ≫ ι) ≫ μ = toUnit _ ≫ η
· 使用定理 `CategoryTheory.MonObj.lift_lift_assoc`：lift_lift_assoc {A : C} {B : C} [
MonObj B] (f g h : A ⟶ B) : lift (lift f g ≫ μ) h ≫ μ = lift f (lift g h ≫ μ) ≫ 
μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.GrpObj.eq_lift_inv_right`：eq_lift_inv_right [GrpObj B] (f
 g h : A ⟶ B) : f = lift g (h ≫ ι) ≫ μ ↔ lift f h ≫ μ = g
-/
theorem lift_left_mul_ext [GrpObj B] {f g : A ⟶ B} (i : A ⟶ B)
    (h : lift f i ≫ μ = lift g i ≫ μ) : f = g := by
  rwa [← eq_lift_inv_right, lift_lift_assoc, lift_comp_inv_right, lift_comp_one_right] at h

@[to_additive (attr := reassoc (attr := simp))]
/-
**CategoryTheory.GrpObj.inv_comp_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.G
rpObj`。
形式化陈述：inv_comp_inv (A : C) [GrpObj A] : ι ≫ ι = 𝟙 A
参数：A : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrpObj.lift_left_mul_ext`：lift_left_mul_ext [GrpObj B] {f
 g : A ⟶ B} (i : A ⟶ B) (h : lift f i ≫ μ = lift g i ≫ μ) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrpObj.right_inv`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {inst_1 : CategoryTheory.CartesianMonoidalCategory C}   (X 
: C) [self : Category…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.SemiCartesianMonoidalCategory.comp_toUnit_assoc`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.SemiCa
rtesianMonoidalCategory C]   {X Y : C} (f : X ⟶ Y) {…
· 使用定理 `CategoryTheory.GrpObj.left_inv`：∀ {C : Type u₁} {inst : CategoryTheory.C
ategory.{v₁, u₁} C} {inst_1 : CategoryTheory.CartesianMonoidalCategory C}   (X :
 C) [self : Category…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.comp_lift_assoc`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.CartesianMon
oidalCategory C]   {V W X Y : C} (f : V ⟶ W) (…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem inv_comp_inv (A : C) [GrpObj A] : ι ≫ ι = 𝟙 A := by
  apply lift_left_mul_ext ι[A]
  rw [right_inv, ← comp_toUnit_assoc ι, ← left_inv, comp_lift_assoc, Category.comp_id]

/-- Transfer `AddGrpObj` along an isomorphism. -/
-- Note: The simps lemmas are not tagged simp because their `#discr_tree_simp_key` are too generic.
@[simps! -isSimp]
/-
**CategoryTheory.GrpObj._root_.CategoryTheory.AddGrpObj.ofIso** 是 Mathlib 中的一个缩写
定义，位于命名空间 `CategoryTheory.GrpObj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.GrpObj.ofIso** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.GrpObj
`。
形式化陈述：ofIso (e : G ≅ X) : GrpObj X where toMonObj
参数：e : G ≅ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev ofIso (e : G ≅ X) : GrpObj X where
  toMonObj := .ofIso e
  inv := e.inv ≫ ι[G] ≫ e.hom
  left_inv := by simp +instances [MonObj.ofIso]
  right_inv := by simp +instances [MonObj.ofIso]

attribute [to_additive existing] ofIso

@[to_additive]
/-
**CategoryTheory.GrpObj.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.GrpObj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : C) [GrpObj A] : IsIso ι[A] := ⟨ι, by simp, by simp⟩

/-- For `inv ≫ inv = 𝟙` see `inv_comp_inv`. -/
@[to_additive (attr := simp) /-- For `neg ≫ neg = 𝟙` see `neg_comp_neg`. -/]
/-
**CategoryTheory.GrpObj.inv_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.GrpObj
`。
形式化陈述：inv_inv (A : C) [GrpObj A] : CategoryTheory.inv ι = ι[A]
参数：A : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrpObj.instIsIsoInv`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C]   
(A : C) [inst_2 : Catego…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.inv_comp_eq_id`：inv_comp_eq_id (g : X ⟶ Y) [IsIso g] {f :
 X ⟶ Y} : inv g ≫ f = 𝟙 Y ↔ f = g
· 使用定理 `CategoryTheory.IsIso.inv_inv`：inv_inv [IsIso f] : inv (inv f) = f
· 使用定理 `CategoryTheory.GrpObj.inv_comp_inv`：inv_comp_inv (A : C) [GrpObj A] : ι 
≫ ι = 𝟙 A

--- 原说明 ---
For `inv ≫ inv = 𝟙` see `inv_comp_inv`.
-/
theorem inv_inv (A : C) [GrpObj A] : CategoryTheory.inv ι = ι[A] := by
  rw [eq_comm, ← CategoryTheory.inv_comp_eq_id, IsIso.inv_inv, inv_comp_inv]

@[to_additive (attr := reassoc)]
/-
**CategoryTheory.GrpObj.mul_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.GrpObj
`。
形式化陈述：mul_inv [BraidedCategory C] (A : C) [GrpObj A] : μ ≫ ι = (β_ A A).hom ≫ (ι
 otimesₘ ι) ≫ μ
参数：A : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrpObj.lift_left_mul_ext`：lift_left_mul_ext [GrpObj B] {f
 g : A ⟶ B} (i : A ⟶ B) (h : lift f i ≫ μ = lift g i ≫ μ) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.comp_lift`：comp_lift {V W X Y :
 C} (f : V ⟶ W) (g : W ⟶ X) (h : W ⟶ Y) : f ≫ lift g h = lift (f ≫ g) (f ≫ h)
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.GrpObj.left_inv`：∀ {C : Type u₁} {inst : CategoryTheory.C
ategory.{v₁, u₁} C} {inst_1 : CategoryTheory.CartesianMonoidalCategory C}   (X :
 C) [self : Category…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.lift_snd_fst`：lift_snd_fst {X Y
 : C} : lift (snd X Y) (fst X Y) = (β_ X Y).hom
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_map`：lift_map {V W X Y Z :
 C} (f : V ⟶ W) (g : V ⟶ X) (h : W ⟶ Y) (k : X ⟶ Z) : lift f g ≫ (h otimesₘ k) =
 lift (f ≫ h) (g ≫ k)
· 使用定理 `CategoryTheory.MonObj.lift_lift_assoc`：lift_lift_assoc {A : C} {B : C} [
MonObj B] (f g h : A ⟶ B) : lift (lift f g ≫ μ) h ≫ μ = lift f (lift g h ≫ μ) ≫ 
μ
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst_snd`：lift_fst_snd {X Y
 : C} : lift (fst X Y) (snd X Y) = 𝟙 (X otimes Y)
· 使用定理 `CategoryTheory.GrpObj.lift_comp_inv_left`：lift_comp_inv_left [GrpObj B] 
(f : A ⟶ B) : lift (f ≫ ι) f ≫ μ = toUnit _ ≫ η
· 使用定理 `CategoryTheory.MonObj.lift_comp_one_left`：lift_comp_one_left {A : C} {B 
: C} [MonObj B] (f : A ⟶ 𝟙_ C) (g : A ⟶ B) : lift (f ≫ η) g ≫ μ = g
· 使用定理 `CategoryTheory.SemiCartesianMonoidalCategory.comp_toUnit_assoc`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.SemiCa
rtesianMonoidalCategory C]   {X Y : C} (f : X ⟶ Y) {…
-/
theorem mul_inv [BraidedCategory C] (A : C) [GrpObj A] :
    μ ≫ ι = (β_ A A).hom ≫ (ι ⊗ₘ ι) ≫ μ := by
  apply lift_left_mul_ext μ
  nth_rw 2 [← Category.comp_id μ]
  rw [← comp_lift, Category.assoc, left_inv, ← Category.assoc (β_ A A).hom,
    ← lift_snd_fst, lift_map, lift_lift_assoc]
  nth_rw 2 [← Category.id_comp μ]
  rw [← lift_fst_snd, ← lift_lift_assoc (fst A A ≫ _), lift_comp_inv_left, lift_comp_one_left,
    lift_comp_inv_left, comp_toUnit_assoc]

@[to_additive (attr := reassoc)]
/-
**CategoryTheory.GrpObj.tensorHom_inv_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.GrpObj`。
形式化陈述：tensorHom_inv_inv_mul [BraidedCategory C] (A : C) [GrpObj A] : (ι[A] otime
sₘ ι[A]) ≫ μ = (β_ A A).hom ≫ μ ≫ ι
参数：A : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrpObj.mul_inv`：mul_inv [BraidedCategory C] (A : C) [GrpO
bj A] : μ ≫ ι = (β_ A A).hom ≫ (ι otimesₘ ι) ≫ μ
· 使用定理 `CategoryTheory.SymmetricCategory.symmetry_assoc`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.MonoidalCategory C}  
 [self : CategoryTheory.SymmetricCate…
-/
theorem tensorHom_inv_inv_mul [BraidedCategory C] (A : C) [GrpObj A] :
    (ι[A] ⊗ₘ ι[A]) ≫ μ = (β_ A A).hom ≫ μ ≫ ι := by
  rw [mul_inv A, SymmetricCategory.symmetry_assoc]

@[to_additive (attr := reassoc)]
/-
**CategoryTheory.GrpObj.mul_inv_rev** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Gr
pObj`。
形式化陈述：mul_inv_rev [BraidedCategory C] (G : C) [GrpObj G] : μ ≫ ι = (ι[G] otimesₘ
 ι) ≫ (β_ _ _).hom ≫ μ
参数：G : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.BraidedCategory.braiding_naturality_assoc`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCate
gory C]   [inst_2 : CategoryTheory.BraidedCate…
· 使用定理 `CategoryTheory.GrpObj.tensorHom_inv_inv_mul`：tensorHom_inv_inv_mul [Brai
dedCategory C] (A : C) [GrpObj A] : (ι[A] otimesₘ ι[A]) ≫ μ = (β_ A A).hom ≫ μ ≫
 ι
· 使用定理 `CategoryTheory.SymmetricCategory.symmetry_assoc`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.MonoidalCategory C}  
 [self : CategoryTheory.SymmetricCate…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mul_inv_rev [BraidedCategory C] (G : C) [GrpObj G] :
    μ ≫ ι = (ι[G] ⊗ₘ ι) ≫ (β_ _ _).hom ≫ μ := by simp [tensorHom_inv_inv_mul]

/-- The map `(· * f)`. -/
@[to_additive (attr := simps) /-- The map `(· + f)`. -/]
/-
**CategoryTheory.GrpObj.mulRight** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.GrpOb
j`。
形式化陈述：mulRight {A : C} [GrpObj A] (f : 𝟙_ C ⟶ A) : A ≅ A where hom
参数：f : 𝟙_ C ⟶ A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `(· * f)`.
-/
def mulRight {A : C} [GrpObj A] (f : 𝟙_ C ⟶ A) : A ≅ A where
  hom := lift (𝟙 _) (toUnit _ ≫ f) ≫ μ
  inv := lift (𝟙 _) (toUnit _ ≫ f ≫ ι) ≫ μ
  hom_inv_id := by simp [comp_lift_assoc, lift_lift_assoc, ← comp_lift]
  inv_hom_id := by simp [comp_lift_assoc, lift_lift_assoc, ← comp_lift]

@[to_additive (attr := simp)]
/-
**CategoryTheory.GrpObj.mulRight_one** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.G
rpObj`。
形式化陈述：mulRight_one (A : C) [GrpObj A] : mulRight η[A] = Iso.refl A
参数：A : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrpObj.mulRight_hom`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C]   
{A : C} [inst_2 : Catego…
· 使用定理 `CategoryTheory.MonObj.lift_comp_one_right`：lift_comp_one_right {A : C} {
B : C} [MonObj B] (f : A ⟶ B) (g : A ⟶ 𝟙_ C) : lift f (g ≫ η) ≫ μ = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
/-
**CategoryTheory.GrpObj.isPullback** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Grp
Obj`。
形式化陈述：isPullback (A : C) [GrpObj A] : IsPullback (μ ▷ A) ((α_ A A A).hom ≫ (A ◁ 
μ)) μ μ where w
参数：A : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonObj.mul_assoc`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} (X : C)   [sel
f : CategoryTheory.Mo…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_whiskerRight`：lift_whisker
Right {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : Y ⟶ W) : lift f g ≫ (h ▷ Z) = l
ift (f ≫ h) g
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst`：lift_fst {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonObj.lift_lift_assoc`：lift_lift_assoc {A : C} {B : C} [
MonObj B] (f g h : A ⟶ B) : lift (lift f g ≫ μ) h ≫ μ = lift f (lift g h ≫ μ) ≫ 
μ
· 使用定理 `CategoryTheory.GrpObj.lift_comp_inv_right`：lift_comp_inv_right [GrpObj B
] (f : A ⟶ B) : lift f (f ≫ ι) ≫ μ = toUnit _ ≫ η
· 使用定理 `CategoryTheory.MonObj.lift_comp_one_left`：lift_comp_one_left {A : C} {B 
: C} [MonObj B] (f : A ⟶ 𝟙_ C) (g : A ⟶ B) : lift (f ≫ η) g ≫ μ = g
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.lift_lift_associator_hom_assoc`
：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheo
ry.CartesianMonoidalCategory C]   {X Y Z W : C} (f : X ⟶ Y) (…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_whiskerLeft`：lift_whiskerL
eft {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : Z ⟶ W) : lift f g ≫ (Y ◁ h) = lif
t f (g ≫ h)
· 使用定理 `CategoryTheory.GrpObj.eq_lift_inv_right`：eq_lift_inv_right [GrpObj B] (f
 g h : A ⟶ B) : f = lift g (h ≫ ι) ≫ μ ↔ lift f h ≫ μ = g
· 使用定理 `CategoryTheory.GrpObj.lift_inv_left_eq`：lift_inv_left_eq [GrpObj B] (f g
 h : A ⟶ B) : lift (f ≫ ι) g ≫ μ = h ↔ g = lift f h ≫ μ
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_comp_fst_snd`：lift_comp_fs
t_snd {X Y Z : C} (f : X ⟶ Y otimes Z) : lift (f ≫ fst _ _) (f ≫ snd _ _) = f
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
· 使用定理 `CategoryTheory.GrpObj.lift_comp_inv_left`：lift_comp_inv_left [GrpObj B] 
(f : A ⟶ B) : lift (f ≫ ι) f ≫ μ = toUnit _ ≫ η
· 使用定理 `CategoryTheory.MonObj.lift_comp_one_right`：lift_comp_one_right {A : C} {
B : C} [MonObj B] (f : A ⟶ B) (g : A ⟶ 𝟙_ C) : lift f (g ≫ η) ≫ μ = f
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerLeft_fst`：whiskerLeft_fs
t (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f ≫ fst _ _ = fst _ _
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.associator_hom_fst`：associator_
hom_fst (X Y Z : C) : (α_ X Y Z).hom ≫ fst _ _ = fst _ _ ≫ fst _ _
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.GrpObj.eq_lift_inv_left`：eq_lift_inv_left [GrpObj B] (f g
 h : A ⟶ B) : f = lift (g ≫ ι) h ≫ μ ↔ lift g f ≫ μ = h
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerRight_fst`：whiskerRight_
fst {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z ≫ fst _ _ = fst _ _ ≫ f
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerRight_snd`：whiskerRight_
snd {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z ≫ snd _ _ = snd _ _
-/
theorem isPullback (A : C) [GrpObj A] :
    IsPullback (μ ▷ A) ((α_ A A A).hom ≫ (A ◁ μ)) μ μ where
  w := by simp
  isLimit' := Nonempty.intro <| PullbackCone.IsLimit.mk _
    (fun s => lift
      (lift
        (s.snd ≫ fst _ _)
        (lift (s.snd ≫ fst _ _ ≫ ι) (s.fst ≫ fst _ _) ≫ μ))
      (s.fst ≫ snd _ _))
    (by
      refine fun s => CartesianMonoidalCategory.hom_ext _ _ ?_ (by simp)
      simp only [lift_whiskerRight, lift_fst]
      rw [← lift_lift_assoc, ← assoc, lift_comp_inv_right, lift_comp_one_left])
    (by
      refine fun s => CartesianMonoidalCategory.hom_ext _ _ (by simp) ?_
      simp only [lift_lift_associator_hom_assoc, lift_whiskerLeft, lift_snd]
      have : lift (s.snd ≫ fst _ _ ≫ ι) (s.fst ≫ fst _ _) ≫ μ =
          lift (s.snd ≫ snd _ _) (s.fst ≫ snd _ _ ≫ ι) ≫ μ := by
        rw [← assoc s.fst, eq_lift_inv_right, lift_lift_assoc, ← assoc s.snd, lift_inv_left_eq,
          lift_comp_fst_snd, lift_comp_fst_snd, s.condition]
      rw [this, lift_lift_assoc, ← assoc, lift_comp_inv_left, lift_comp_one_right])
    (by
      intro s m hm₁ hm₂
      refine CartesianMonoidalCategory.hom_ext _ _ (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_) ?_
      · simpa using hm₂ =≫ fst _ _
      · have h : m ≫ fst _ _ ≫ fst _ _ = s.snd ≫ fst _ _ := by simpa using hm₂ =≫ fst _ _
        have := hm₁ =≫ fst _ _
        simp only [assoc, whiskerRight_fst, lift_fst, lift_snd] at this ⊢
        rw [← assoc, ← lift_comp_fst_snd (m ≫ _), assoc, assoc, h] at this
        rwa [← assoc s.snd, eq_lift_inv_left]
      · simpa using hm₁ =≫ snd _ _)

/-- Morphisms of group objects preserve inverses. -/
@[to_additive (attr := reassoc (attr := simp))
/-- Morphisms of group objects preserve negations. -/]
/-
**CategoryTheory.GrpObj.inv_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.GrpObj
`。
形式化陈述：inv_hom [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] : ι ≫ f = f ≫ ι
参数：f : A ⟶ B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPullback.hom_ext`：hom_ext (hP : IsPullback fst snd f g)
 {W : C} {k l : W ⟶ P} (h₀ : k ≫ fst = l ≫ fst) (h₁ : k ≫ snd = l ≫ snd) : k = l
· 使用定理 `CategoryTheory.GrpObj.isPullback`：isPullback (A : C) [GrpObj A] : IsPull
back (μ ▷ A) ((α_ A A A).hom ≫ (A ◁ μ)) μ μ where w
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_whiskerRight`：lift_whisker
Right {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : Y ⟶ W) : lift f g ≫ (h ▷ Z) = l
ift (f ≫ h) g
· 使用定理 `CategoryTheory.GrpObj.lift_inv_comp_right`：lift_inv_comp_right [GrpObj A
] [GrpObj B] (f : A ⟶ B) [IsMonHom f] : lift f (ι ≫ f) ≫ μ = toUnit _ ≫ η
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst`：lift_fst {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f
· 使用定理 `CategoryTheory.GrpObj.lift_comp_inv_right`：lift_comp_inv_right [GrpObj B
] (f : A ⟶ B) : lift f (f ≫ ι) ≫ μ = toUnit _ ≫ η
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.lift_lift_associator_hom_assoc`
：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheo
ry.CartesianMonoidalCategory C]   {X Y Z W : C} (f : X ⟶ Y) (…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_whiskerLeft`：lift_whiskerL
eft {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : Z ⟶ W) : lift f g ≫ (Y ◁ h) = lif
t f (g ≫ h)
· 使用定理 `CategoryTheory.GrpObj.lift_inv_comp_left`：lift_inv_comp_left [GrpObj A] 
[GrpObj B] (f : A ⟶ B) [IsMonHom f] : lift (ι ≫ f) f ≫ μ = toUnit _ ≫ η
· 使用定理 `CategoryTheory.GrpObj.lift_comp_inv_left`：lift_comp_inv_left [GrpObj B] 
(f : A ⟶ B) : lift (f ≫ ι) f ≫ μ = toUnit _ ≫ η
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
-/
theorem inv_hom [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] : ι ≫ f = f ≫ ι := by
  suffices lift (lift f (ι ≫ f)) f =
      lift (lift f (f ≫ ι)) f by simpa using (this =≫ fst _ _) =≫ snd _ _
  apply (isPullback B).hom_ext <;> apply CartesianMonoidalCategory.hom_ext <;>
    simp [lift_inv_comp_right, lift_inv_comp_left]

@[to_additive]
/-
**CategoryTheory.GrpObj.toMonObj_injective** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.GrpObj`。
形式化陈述：toMonObj_injective {X : C} : Function.Injective (@GrpObj.toMonObj C ‹_› ‹_
› X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrpObj.lift_left_mul_ext`：lift_left_mul_ext [GrpObj B] {f
 g : A ⟶ B} (i : A ⟶ B) (h : lift f i ≫ μ = lift g i ≫ μ) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrpObj.left_inv`：∀ {C : Type u₁} {inst : CategoryTheory.C
ategory.{v₁, u₁} C} {inst_1 : CategoryTheory.CartesianMonoidalCategory C}   (X :
 C) [self : Category…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.GrpObj.right_inv`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {inst_1 : CategoryTheory.CartesianMonoidalCategory C}   (X 
: C) [self : Category…
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
/-
**CategoryTheory.GrpObj.ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrpObj`。
形式化陈述：ext {X : C} (h₁ h₂ : GrpObj X) (H : h₁.toMonObj = h₂.toMonObj) : h₁ = h₂
参数：h₁ h₂ : GrpObj X；H : h₁.toMonObj = h₂.toMonObj。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GrpObj.toMonObj_injective`：toMonObj_injective {X : C} : F
unction.Injective (@GrpObj.toMonObj C ‹_› ‹_› X)
-/
lemma ext {X : C} (h₁ h₂ : GrpObj X) (H : h₁.toMonObj = h₂.toMonObj) : h₁ = h₂ :=
  GrpObj.toMonObj_injective H

-- Note: `Invertible` has no additive variant
/-- A monoid object with invertible homs is a group object. -/
@[instance_reducible]
/-
**CategoryTheory.GrpObj.ofInvertible** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.G
rpObj`。
形式化陈述：ofInvertible (G : C) [MonObj G] (h : forall X (f : X ⟶ G), Invertible f) :
 GrpObj G where inv
参数：G : C；h : forall X (f : X ⟶ G), Invertible f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A monoid object with invertible homs is a group object.
-/
def ofInvertible (G : C) [MonObj G] (h : ∀ X (f : X ⟶ G), Invertible f) : GrpObj G where
  inv := Yoneda.fullyFaithful.preimage
    ⟨fun X ↦ ↾fun f ↦ (h X.unop f).invOf, fun X Y f ↦ by
      ext g
      simp only [yoneda_obj_map, TypeCat.Fun.toFun_apply, comp_apply,
        ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk, invOf_eq_iff_left]
      rw [← comp_mul, invOf_mul_self, comp_one]⟩
  left_inv := by simp [Yoneda.fullyFaithful_preimage, ← Hom.mul_def, Hom.one_def]
  right_inv := by simp [Yoneda.fullyFaithful_preimage, ← Hom.mul_def, Hom.one_def]

namespace tensorObj
variable [BraidedCategory C] {G H : C} [GrpObj G] [GrpObj H]

@[to_additive]
/-
**CategoryTheory.GrpObj.tensorObj.instTensorObj** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.GrpObj.tensorObj`。
形式化陈述：instTensorObj : GrpObj (G otimes H) where inv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instTensorObj : GrpObj (G ⊗ H) where
  inv := ι ⊗ₘ ι

attribute [simps inv] instTensorObj
attribute [simps neg] AddGrpObj.tensorObj.instTensorObj

end GrpObj.tensorObj

namespace Grp

section

variable (C)

/-- The forgetful functor from group objects to monoid objects. -/
@[to_additive (attr := simps! obj_X)
/-- The forgetful functor from additive group objects to additive monoid objects. -/]
/-
**CategoryTheory.Grp.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Grp`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] → CategoryTheory.Functor (Catego
ryTheory.Grp C) C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def forget₂Mon : Grp C ⥤ Mon C :=
  inducedFunctor Grp.toMon

/-- The forgetful functor from group objects to monoid objects is fully faithful. -/
@[to_additive
/-- The forgetful functor from additive group objects to additive monoid objects
is fully faithful. -/]
/-
**CategoryTheory.Grp.fullyFaithfulForget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Grp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def fullyFaithfulForget₂Mon : (forget₂Mon C).FullyFaithful :=
  fullyFaithfulInducedFunctor _
/-
**CategoryTheory.Grp.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Grp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance : (forget₂Mon C).Full := InducedCategory.full _
/-
**CategoryTheory.Grp.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Grp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance : (forget₂Mon C).Faithful := InducedCategory.faithful _

variable {C}

@[to_additive (attr := simp) forget₂AddMon_obj_zero]
/-
**CategoryTheory.Grp.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Grp`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] → CategoryTheory.Functor (Catego
ryTheory.Grp C) C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂Mon_obj_one (A : Grp C) : η[((forget₂Mon C).obj A).X] = η[A.X] :=
  rfl

@[to_additive (attr := simp) forget₂AddMon_obj_add]
/-
**CategoryTheory.Grp.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Grp`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] → CategoryTheory.Functor (Catego
ryTheory.Grp C) C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂Mon_obj_mul (A : Grp C) : μ[((forget₂Mon C).obj A).X] = μ[A.X] :=
  rfl

@[to_additive (attr := simp) forget₂AddMon_map_hom]
/-
**CategoryTheory.Grp.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Grp`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] → CategoryTheory.Functor (Catego
ryTheory.Grp C) C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂Mon_map_hom {A B : Grp C} (f : A ⟶ B) :
    ((forget₂Mon C).map f).hom = f.hom.hom :=
  rfl

variable (C)

/-- The forgetful functor from group objects to the ambient category. -/
@[to_additive (attr := simps!)
/-- The forgetful functor from additive group objects to the ambient category. -/]
/-
**CategoryTheory.Grp.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Grp`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] → CategoryTheory.Functor (Catego
ryTheory.Grp C) C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def forget : Grp C ⥤ C :=
  forget₂Mon C ⋙ Mon.forget C

@[to_additive]
/-
**CategoryTheory.Grp.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Grp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget C).Faithful where

@[to_additive (attr := simp) forget₂AddMon_comp_forget]
/-
**CategoryTheory.Grp.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Grp`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] → CategoryTheory.Functor (Catego
ryTheory.Grp C) C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂Mon_comp_forget : forget₂Mon C ⋙ Mon.forget C = forget C := rfl

@[to_additive]
/-
**CategoryTheory.Grp.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Grp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {G H : Grp C} {f : G ⟶ H} [IsIso f] : IsIso f.hom.hom :=
  inferInstanceAs <| IsIso <| (forget C).map f

end

/-- Construct an isomorphism of group objects by giving a monoid isomorphism between the underlying
objects. -/
@[to_additive (attr := simps!)
/-- Construct an isomorphism of additive group objects by giving an additive monoid
isomorphism between the underlying objects. -/]
/-
**CategoryTheory.Grp.mkIso'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Grp`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] →       {G H : C} →         (e :
 G ≅ H) →           [inst_2 : CategoryTheory.GrpObj G] →             [inst_3 : C
ategoryTheory.GrpObj H] →               [CategoryTheory.IsMonHom e.hom] → { X :=
 G, grp := inst_2 } ≅ { X := H, grp := inst_3 }
参数：e : G ≅ H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mkIso' {G H : C} (e : G ≅ H) [GrpObj G] [GrpObj H] [IsMonHom e.hom] : mk G ≅ mk H :=
  (fullyFaithfulForget₂Mon C).preimageIso (Mon.mkIso' e)

/-- Construct an isomorphism of group objects by giving an isomorphism between the underlying
objects and checking compatibility with unit and multiplication only in the forward direction. -/
@[to_additive (attr := simps! -isSimp)
/-- Construct an isomorphism of additive group objects by giving an isomorphism between
the underlying objects and checking compatibility with zero and addition only in the
forward direction. -/]
/-
**CategoryTheory.Grp.mkIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Grp`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] →       {G H : CategoryTheory.Gr
p C} →         (e : G.X ≅ H.X) →           autoParam (CategoryTheory.CategoryStr
uct.comp CategoryTheory.MonObj.one e.hom = CategoryTheory.MonObj.one)           
    CategoryTheory.Grp.mkIso._auto_1 →             autoParam                 (Ca
tegoryTheory.CategoryStruct.comp CategoryTheory.MonObj.mul e.hom =              
     CategoryTheory.CategoryStruct.comp (CategoryTheory.MonoidalCategoryStruct.t
ensorHom e.hom e.hom)                     CategoryTheory.MonObj.mul)            
     CategoryTheory.Grp.mkIso._auto_3 →               (G ≅ H)
参数：e : G.X ≅ H.X；CategoryTheory.CategoryStruct.comp CategoryTheory.MonObj.one e.
hom = CategoryTheory.MonObj.one；CategoryTheory.CategoryStruct.comp CategoryTheor
y.MonObj.mul e.hom =                   CategoryTheory.CategoryStruct.comp (Categ
oryTheory.MonoidalCategoryStruct.tensorHom e.hom e.hom)                     Cate
goryTheory.MonObj.mul；G ≅ H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev mkIso {G H : Grp C} (e : G.X ≅ H.X) (one_f : η[G.X] ≫ e.hom = η[H.X] := by cat_disch)
    (mul_f : μ[G.X] ≫ e.hom = (e.hom ⊗ₘ e.hom) ≫ μ[H.X] := by cat_disch) : G ≅ H :=
  have : IsMonHom e.hom := ⟨one_f, mul_f⟩
  mkIso' e

@[to_additive]
/-
**CategoryTheory.Grp.uniqueHomFromTrivial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Grp`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] →       (A : CategoryTheory.Grp 
C) → Unique (CategoryTheory.Grp.trivial C ⟶ A)
参数：A : CategoryTheory.Grp C；CategoryTheory.Grp.trivial C ⟶ A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniqueHomFromTrivial (A : Grp C) : Unique (trivial C ⟶ A) :=
  (show _ ≃ (Mon.trivial C ⟶ A.toMon) from InducedCategory.homEquiv).unique

@[to_additive]
/-
**CategoryTheory.Grp.uniqueHomToTrivial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Grp`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] →       (A : CategoryTheory.Grp 
C) → Unique (A ⟶ CategoryTheory.Grp.trivial C)
参数：A : CategoryTheory.Grp C；A ⟶ CategoryTheory.Grp.trivial C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniqueHomToTrivial (A : Grp C) : Unique (A ⟶ trivial C) :=
  (show _ ≃ (A.toMon ⟶ Mon.trivial C) from InducedCategory.homEquiv).unique

variable (C) in
@[to_additive]
/-
**CategoryTheory.Grp.isZero_trivial** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Gr
p`。
形式化陈述：∀ (C : Type u₁) [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C],   CategoryTheory.Limits.IsZero (Categor
yTheory.Grp.trivial C)
参数：C : Type u₁；CategoryTheory.Grp.trivial C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_unique`：nonempty_unique (α : Sort u) [Subsingleton α] [Nonempty
 α] : Nonempty (Unique α)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma isZero_trivial : IsZero (trivial C) where
  unique_to A := nonempty_unique (trivial C ⟶ A)
  unique_from A := nonempty_unique (A ⟶ trivial C)

@[to_additive]
/-
**CategoryTheory.Grp.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Grp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasZeroObject (Grp C) where
  zero := ⟨Grp.trivial C, isZero_trivial C⟩

@[to_additive]
/-
**CategoryTheory.Grp.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Grp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (G H : Grp C) : Zero (G ⟶ H) where
  zero := Grp.homMk (toUnit _ ≫ η)

@[to_additive (attr := simp)]
/-
**CategoryTheory.Grp.zero_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Grp`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   (G H : CategoryTheory.Grp C), Category
Theory.InducedCategory.Hom.hom 0 = 0
参数：G H : CategoryTheory.Grp C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zero_hom (G H : Grp C) : (0 : G ⟶ H).hom = 0 := rfl

@[to_additive]
/-
**CategoryTheory.Grp.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Grp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : HasZeroMorphisms (Grp C) where

/-! ### `Grp C` is cartesian-monoidal -/

variable [BraidedCategory C] {G H H₁ H₂ : Grp C}

@[to_additive (attr := simps! tensorObj_X tensorHom_hom)]
/-
**CategoryTheory.Grp.instMonoidalCategoryStruct** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Grp`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] →       [CategoryTheory.BraidedC
ategory C] → CategoryTheory.MonoidalCategoryStruct (CategoryTheory.Grp C)
参数：CategoryTheory.Grp C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoidalCategoryStruct : MonoidalCategoryStruct (Grp C) where
  tensorObj G H := ⟨G.X ⊗ H.X⟩
  tensorHom f g := homMk' (tensorHom (C := Mon C) f.hom g.hom)
  whiskerRight f G := homMk' (whiskerRight (C := Mon C) f.hom G.toMon)
  whiskerLeft G _ _ f := homMk' (MonoidalCategoryStruct.whiskerLeft (C := Mon C) G.toMon f.hom)
  tensorUnit := ⟨𝟙_ C⟩
  associator X Y Z :=
    (Grp.fullyFaithfulForget₂Mon C).preimageIso (associator X.toMon Y.toMon Z.toMon)
  leftUnitor G := (Grp.fullyFaithfulForget₂Mon C).preimageIso (leftUnitor G.toMon)
  rightUnitor G := (Grp.fullyFaithfulForget₂Mon C).preimageIso (rightUnitor G.toMon)

@[to_additive (attr := simp)]
/-
**CategoryTheory.Grp.tensorUnit_X** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Grp`
。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCatego
ry C],   (CategoryTheory.MonoidalCategoryStruct.tensorUnit (CategoryTheory.Grp C
)).X =     CategoryTheory.MonoidalCategoryStruct.tensorUnit C
参数：CategoryTheory.MonoidalCategoryStruct.tensorUnit (CategoryTheory.Grp C)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorUnit_X : (𝟙_ (Grp C)).X = 𝟙_ C := rfl

@[to_additive (attr := simp)]
/-
**CategoryTheory.Grp.tensorUnit_one** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Gr
p`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCatego
ry C], CategoryTheory.MonObj.one = CategoryTheory.MonObj.one
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorUnit_one : η[(𝟙_ (Grp C)).X] = η[𝟙_ C] := rfl
@[to_additive (attr := simp)]
/-
**CategoryTheory.Grp.tensorUnit_mul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Gr
p`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCatego
ry C], CategoryTheory.MonObj.mul = CategoryTheory.MonObj.mul
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorUnit_mul : μ[(𝟙_ (Grp C)).X] = μ[𝟙_ C] := rfl

@[to_additive (attr := simp)]
/-
**CategoryTheory.Grp.tensorObj_one** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Grp
`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCatego
ry C] (G H : CategoryTheory.Grp C),   CategoryTheory.MonObj.one = CategoryTheory
.MonObj.one
参数：G H : CategoryTheory.Grp C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorObj_one (G H : Grp C) : η[(G ⊗ H).X] = η[G.X ⊗ H.X] := rfl
@[to_additive (attr := simp)]
/-
**CategoryTheory.Grp.tensorObj_mul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Grp
`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCatego
ry C] (G H : CategoryTheory.Grp C),   CategoryTheory.MonObj.mul = CategoryTheory
.MonObj.mul
参数：G H : CategoryTheory.Grp C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorObj_mul (G H : Grp C) : μ[(G ⊗ H).X] = μ[G.X ⊗ H.X] := rfl

@[to_additive (attr := simp)]
/-
**CategoryTheory.Grp.whiskerLeft_hom_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Grp`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCatego
ry C] {G H : CategoryTheory.Grp C} (f : G ⟶ H) (I : CategoryTheory.Grp C),   (Ca
tegoryTheory.MonoidalCategoryStruct.whiskerRight f I).hom.hom =     CategoryTheo
ry.MonoidalCategoryStruct.whiskerRight f.hom.hom I.X
参数：f : G ⟶ H；I : CategoryTheory.Grp C；CategoryTheory.MonoidalCategoryStruct.whis
kerRight f I。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerLeft_hom_hom {G H : Grp C} (f : G ⟶ H) (I : Grp C) :
    (f ▷ I).hom.hom = f.hom.hom ▷ I.X := rfl

@[to_additive (attr := simp)]
/-
**CategoryTheory.Grp.whiskerRight_hom_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Grp`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCatego
ry C] (G : CategoryTheory.Grp C) {H I : CategoryTheory.Grp C} (f : H ⟶ I),   (Ca
tegoryTheory.MonoidalCategoryStruct.whiskerLeft G f).hom.hom =     CategoryTheor
y.MonoidalCategoryStruct.whiskerLeft G.X f.hom.hom
参数：G : CategoryTheory.Grp C；f : H ⟶ I；CategoryTheory.MonoidalCategoryStruct.whis
kerLeft G f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerRight_hom_hom (G : Grp C) {H I : Grp C} (f : H ⟶ I) :
    (G ◁ f).hom.hom = G.X ◁ f.hom.hom := rfl


@[to_additive (attr := simp)]
/-
**CategoryTheory.Grp.leftUnitor_hom_hom_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Grp`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCatego
ry C] (G : CategoryTheory.Grp C),   (CategoryTheory.MonoidalCategoryStruct.leftU
nitor G).hom.hom.hom =     (CategoryTheory.MonoidalCategoryStruct.leftUnitor G.X
).hom
参数：G : CategoryTheory.Grp C；CategoryTheory.MonoidalCategoryStruct.leftUnitor G；C
ategoryTheory.MonoidalCategoryStruct.leftUnitor G.X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma leftUnitor_hom_hom_hom (G : Grp C) : (λ_ G).hom.hom.hom = (λ_ G.X).hom := rfl
@[to_additive (attr := simp)]
/-
**CategoryTheory.Grp.leftUnitor_inv_hom_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Grp`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCatego
ry C] (G : CategoryTheory.Grp C),   (CategoryTheory.MonoidalCategoryStruct.leftU
nitor G).inv.hom.hom =     (CategoryTheory.MonoidalCategoryStruct.leftUnitor G.X
).inv
参数：G : CategoryTheory.Grp C；CategoryTheory.MonoidalCategoryStruct.leftUnitor G；C
ategoryTheory.MonoidalCategoryStruct.leftUnitor G.X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma leftUnitor_inv_hom_hom (G : Grp C) : (λ_ G).inv.hom.hom = (λ_ G.X).inv := rfl
@[to_additive (attr := simp)]
/-
**CategoryTheory.Grp.rightUnitor_hom_hom_hom** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Grp`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCatego
ry C] (G : CategoryTheory.Grp C),   (CategoryTheory.MonoidalCategoryStruct.right
Unitor G).hom.hom.hom =     (CategoryTheory.MonoidalCategoryStruct.rightUnitor G
.X).hom
参数：G : CategoryTheory.Grp C；CategoryTheory.MonoidalCategoryStruct.rightUnitor G；
CategoryTheory.MonoidalCategoryStruct.rightUnitor G.X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rightUnitor_hom_hom_hom (G : Grp C) : (ρ_ G).hom.hom.hom = (ρ_ G.X).hom := rfl
@[to_additive (attr := simp)]
/-
**CategoryTheory.Grp.rightUnitor_inv_hom_hom** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Grp`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCatego
ry C] (G : CategoryTheory.Grp C),   (CategoryTheory.MonoidalCategoryStruct.right
Unitor G).inv.hom.hom =     (CategoryTheory.MonoidalCategoryStruct.rightUnitor G
.X).inv
参数：G : CategoryTheory.Grp C；CategoryTheory.MonoidalCategoryStruct.rightUnitor G；
CategoryTheory.MonoidalCategoryStruct.rightUnitor G.X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rightUnitor_inv_hom_hom (G : Grp C) : (ρ_ G).inv.hom.hom = (ρ_ G.X).inv := rfl
@[to_additive (attr := simp)]
/-
**CategoryTheory.Grp.associator_hom_hom_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Grp`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCatego
ry C] (G H I : CategoryTheory.Grp C),   (CategoryTheory.MonoidalCategoryStruct.a
ssociator G H I).hom.hom.hom =     (CategoryTheory.MonoidalCategoryStruct.associ
ator G.X H.X I.X).hom
参数：G H I : CategoryTheory.Grp C；CategoryTheory.MonoidalCategoryStruct.associator
 G H I；CategoryTheory.MonoidalCategoryStruct.associator G.X H.X I.X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma associator_hom_hom_hom (G H I : Grp C) :
    (α_ G H I).hom.hom.hom = (α_ G.X H.X I.X).hom := rfl
@[to_additive (attr := simp)]
/-
**CategoryTheory.Grp.associator_inv_hom_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Grp`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCatego
ry C] (G H I : CategoryTheory.Grp C),   (CategoryTheory.MonoidalCategoryStruct.a
ssociator G H I).inv.hom.hom =     (CategoryTheory.MonoidalCategoryStruct.associ
ator G.X H.X I.X).inv
参数：G H I : CategoryTheory.Grp C；CategoryTheory.MonoidalCategoryStruct.associator
 G H I；CategoryTheory.MonoidalCategoryStruct.associator G.X H.X I.X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma associator_inv_hom_hom (G H I : Grp C) :
    (α_ G H I).inv.hom.hom = (α_ G.X H.X I.X).inv := rfl

@[to_additive]
/-
**CategoryTheory.Grp.instMonoidalCategory** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Grp`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] →       [CategoryTheory.BraidedC
ategory C] → CategoryTheory.MonoidalCategory (CategoryTheory.Grp C)
参数：CategoryTheory.Grp C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoidalCategory : MonoidalCategory (Grp C) where
  tensorHom_def := by intros; ext; simp [tensorHom_def]
  triangle _ _ := by ext; exact triangle _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[to_additive]
/-
**CategoryTheory.Grp.instCartesianMonoidalCategory** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Grp`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] →       [CategoryTheory.BraidedC
ategory C] → CategoryTheory.CartesianMonoidalCategory (CategoryTheory.Grp C)
参数：CategoryTheory.Grp C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCartesianMonoidalCategory : CartesianMonoidalCategory (Grp C) where
  isTerminalTensorUnit :=
    .ofUniqueHom (fun G ↦ homMk' (toUnit G.toMon)) fun G f ↦ by ext; exact toUnit_unique ..
  fst G H := homMk' (fst G.toMon H.toMon)
  snd G H := homMk' (snd G.toMon H.toMon)
  tensorProductIsBinaryProduct G H :=
    BinaryFan.IsLimit.mk _ (fun {T} f g ↦ .mk (lift f.hom g.hom))
      (by aesop_cat) (by aesop_cat) (by aesop_cat)
  fst_def G H := by ext; apply fst_def
  snd_def G H := by ext; apply snd_def

@[to_additive (attr := simp)]
/-
**CategoryTheory.Grp.lift_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Grp`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCatego
ry C] {G H₁ H₂ : CategoryTheory.Grp C} (f : G ⟶ H₁) (g : G ⟶ H₂),   (CategoryThe
ory.CartesianMonoidalCategory.lift f g).hom = CategoryTheory.CartesianMonoidalCa
tegory.lift f.hom g.hom
参数：f : G ⟶ H₁；g : G ⟶ H₂；CategoryTheory.CartesianMonoidalCategory.lift f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lift_hom (f : G ⟶ H₁) (g : G ⟶ H₂) : (lift f g).hom = (lift f.hom g.hom) := rfl
@[to_additive (attr := simp)]
/-
**CategoryTheory.Grp.fst_hom_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Grp`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCatego
ry C] (G H : CategoryTheory.Grp C),   (CategoryTheory.SemiCartesianMonoidalCateg
ory.fst G H).hom.hom =     CategoryTheory.SemiCartesianMonoidalCategory.fst G.X 
H.X
参数：G H : CategoryTheory.Grp C；CategoryTheory.SemiCartesianMonoidalCategory.fst G
 H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fst_hom_hom (G H : Grp C) : (fst G H).hom.hom = fst G.X H.X := rfl
@[to_additive (attr := simp)]
/-
**CategoryTheory.Grp.snd_hom_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Grp`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCatego
ry C] (G H : CategoryTheory.Grp C),   (CategoryTheory.SemiCartesianMonoidalCateg
ory.snd G H).hom.hom =     CategoryTheory.SemiCartesianMonoidalCategory.snd G.X 
H.X
参数：G H : CategoryTheory.Grp C；CategoryTheory.SemiCartesianMonoidalCategory.snd G
 H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma snd_hom_hom (G H : Grp C) : (snd G H).hom.hom = snd G.X H.X := rfl

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simps)]
/-
**CategoryTheory.Grp.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Grp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.Grp.instBraidedCategory** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Grp`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] →       [inst_2 : CategoryTheory
.BraidedCategory C] → CategoryTheory.BraidedCategory (CategoryTheory.Grp C)
参数：CategoryTheory.Grp C。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Grp.instFaithfulMonForget₂Mon`：∀ (C : Type u₁) [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.CartesianMonoidalCate
gory C],   (CategoryTheory.Grp.for…
-/
instance instBraidedCategory : BraidedCategory (Grp C) :=
  .ofFaithful (forget₂Mon C) fun G H ↦ Grp.mkIso (β_ G.X H.X)

@[to_additive (attr := simp)]
/-
**CategoryTheory.Grp.braiding_hom_hom_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Grp`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCatego
ry C] (G H : CategoryTheory.Grp C), (β_ G H).hom.hom.hom = (β_ G.X H.X).hom
参数：G H : CategoryTheory.Grp C；β_ G H；β_ G.X H.X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma braiding_hom_hom_hom (G H : Grp C) : (β_ G H).hom.hom.hom = (β_ G.X H.X).hom := rfl
@[to_additive (attr := simp)]
/-
**CategoryTheory.Grp.braiding_inv_hom_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Grp`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCatego
ry C] (G H : CategoryTheory.Grp C), (β_ G H).inv.hom.hom = (β_ G.X H.X).inv
参数：G H : CategoryTheory.Grp C；β_ G H；β_ G.X H.X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.Functor.grpObjObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fun
ctor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] →       {D : Type u₂} →         
[inst_2 : CategoryTheory.Category.{v₂, u₂} D] →           [inst_3 : CategoryTheo
ry.CartesianMonoidalCategory D] →             {F : CategoryTheory.Functor C D} →
               [F.Monoidal] → {G : C} → [CategoryTheory.GrpObj G] → CategoryTheo
ry.GrpObj (F.obj G)
参数：F.obj G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.Functor.obj.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma obj.ι_def {G : C} [GrpObj G] : ι[F.obj G] = F.map ι := rfl

open Monoidal

variable (F) in
/-- A finite-product-preserving functor takes group objects to group objects. -/
@[to_additive (attr := simps!)
/-- A finite-product-preserving functor takes additive group objects to additive group objects. -/]
/-
**CategoryTheory.Functor.mapGrp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functo
r`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] →       {D : Type u₂} →         
[inst_2 : CategoryTheory.Category.{v₂, u₂} D] →           [inst_3 : CategoryTheo
ry.CartesianMonoidalCategory D] →             (F : CategoryTheory.Functor C D) →
               [F.Monoidal] → CategoryTheory.Functor (CategoryTheory.Grp C) (Cat
egoryTheory.Grp D)
参数：F : CategoryTheory.Functor C D；CategoryTheory.Grp C；CategoryTheory.Grp D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapGrp : Grp C ⥤ Grp D where
  obj A := .mk (F.obj A.X)
  map f := Grp.homMk' (F.mapMon.map f.hom)

@[to_additive]
/-
**CategoryTheory.Functor.Faithful.mapGrp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Functor.Faithful`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   {D : Type u₂} [inst_2 : CategoryTheory
.Category.{v₂, u₂} D] [inst_3 : CategoryTheory.CartesianMonoidalCategory D]   {F
 : CategoryTheory.Functor C D} [inst_4 : F.Monoidal] [F.Faithful], F.mapGrp.Fait
hful
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `CategoryTheory.Grp.instFaithfulMonForget₂Mon`：∀ (C : Type u₁) [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.CartesianMonoidalCate
gory C],   (CategoryTheory.Grp.for…
· 使用定理 `CategoryTheory.Functor.Faithful.mapMon`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {D : Ty
pe u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
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
/-
**CategoryTheory.Functor.FullyFaithful.mapGrp** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Functor.FullyFaithful`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] →       {D : Type u₂} →         
[inst_2 : CategoryTheory.Category.{v₂, u₂} D] →           [inst_3 : CategoryTheo
ry.CartesianMonoidalCategory D] →             {F : CategoryTheory.Functor C D} →
 [inst_4 : F.Monoidal] → F.FullyFaithful → F.mapGrp.FullyFaithful
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def FullyFaithful.mapGrp (hF : F.FullyFaithful) : F.mapGrp.FullyFaithful where
  preimage f := Grp.homMk' (hF.mapMon.preimage f.hom)

set_option backward.isDefEq.respectTransparency.types false in
@[to_additive]
/-
**CategoryTheory.Functor.Full.mapGrp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.F
unctor.Full`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   {D : Type u₂} [inst_2 : CategoryTheory
.Category.{v₂, u₂} D] [inst_3 : CategoryTheory.CartesianMonoidalCategory D]   {F
 : CategoryTheory.Functor C D} [inst_4 : F.Monoidal] [F.Full] [F.Faithful], F.ma
pGrp.Full
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.full`：full : F.Full where map_surje
ctive
-/
protected instance Full.mapGrp [F.Full] [F.Faithful] : F.mapGrp.Full :=
  ((FullyFaithful.ofFullyFaithful F).mapGrp).full

@[to_additive (attr := simp)]
/-
**CategoryTheory.Functor.mapGrp_id_one** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   (A : CategoryTheory.Grp C),   Category
Theory.MonObj.one =     CategoryTheory.CategoryStruct.comp       (CategoryTheory
.CategoryStruct.id (CategoryTheory.MonoidalCategoryStruct.tensorUnit C)) Categor
yTheory.MonObj.one
参数：A : CategoryTheory.Grp C；CategoryTheory.CategoryStruct.id (CategoryTheory.Mon
oidalCategoryStruct.tensorUnit C)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapGrp_id_one (A : Grp C) :
    η[((𝟭 C).mapGrp.obj A).X] = 𝟙 _ ≫ η[A.X] :=
  rfl

@[to_additive (attr := simp)]
/-
**CategoryTheory.Functor.mapGrp_id_mul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   (A : CategoryTheory.Grp C),   Category
Theory.MonObj.mul =     CategoryTheory.CategoryStruct.comp       (CategoryTheory
.CategoryStruct.id (CategoryTheory.MonoidalCategoryStruct.tensorObj A.X A.X))   
    CategoryTheory.MonObj.mul
参数：A : CategoryTheory.Grp C；CategoryTheory.CategoryStruct.id (CategoryTheory.Mon
oidalCategoryStruct.tensorObj A.X A.X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapGrp_id_mul (A : Grp C) :
    μ[((𝟭 C).mapGrp.obj A).X] = 𝟙 _ ≫ μ[A.X] :=
  rfl

@[to_additive (attr := simp, reassoc)]
/-
**CategoryTheory.Functor.comp_mapGrp_one** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   {D : Type u₂} [inst_2 : CategoryTheory
.Category.{v₂, u₂} D] [inst_3 : CategoryTheory.CartesianMonoidalCategory D]   {E
 : Type u₃} [inst_4 : CategoryTheory.Category.{v₃, u₃} E] [inst_5 : CategoryTheo
ry.CartesianMonoidalCategory E]   {F : CategoryTheory.Functor C D} {G : Category
Theory.Functor D E} [inst_6 : F.Monoidal] [inst_7 : G.Monoidal]   (A : CategoryT
heory.Grp C),   CategoryTheory.MonObj.one =     CategoryTheory.CategoryStruct.co
mp (CategoryTheory.Functor.LaxMonoidal.ε (F.comp G))       ((F.comp G).map Categ
oryTheory.MonObj.one)
参数：A : CategoryTheory.Grp C；CategoryTheory.Functor.LaxMonoidal.ε (F.comp G)；(F.c
omp G).map CategoryTheory.MonObj.one。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_mapGrp_one (A : Grp C) :
    η[((F ⋙ G).mapGrp.obj A).X] = LaxMonoidal.ε (F ⋙ G) ≫ (F ⋙ G).map η[A.X] :=
  rfl

@[to_additive (attr := simp, reassoc)]
/-
**CategoryTheory.Functor.comp_mapGrp_mul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   {D : Type u₂} [inst_2 : CategoryTheory
.Category.{v₂, u₂} D] [inst_3 : CategoryTheory.CartesianMonoidalCategory D]   {E
 : Type u₃} [inst_4 : CategoryTheory.Category.{v₃, u₃} E] [inst_5 : CategoryTheo
ry.CartesianMonoidalCategory E]   {F : CategoryTheory.Functor C D} {G : Category
Theory.Functor D E} [inst_6 : F.Monoidal] [inst_7 : G.Monoidal]   (A : CategoryT
heory.Grp C),   CategoryTheory.MonObj.mul =     CategoryTheory.CategoryStruct.co
mp (CategoryTheory.Functor.LaxMonoidal.μ (F.comp G) A.X A.X)       ((F.comp G).m
ap CategoryTheory.MonObj.mul)
参数：A : CategoryTheory.Grp C；CategoryTheory.Functor.LaxMonoidal.μ (F.comp G) A.X 
A.X；(F.comp G).map CategoryTheory.MonObj.mul。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_mapGrp_mul (A : Grp C) :
    μ[((F ⋙ G).mapGrp.obj A).X] = LaxMonoidal.μ (F ⋙ G) _ _ ≫ (F ⋙ G).map μ[A.X] :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The identity functor is also the identity on group objects. -/
@[to_additive (attr := simps!)
/-- The identity functor is also the identity on additive group objects. -/]
/-
**CategoryTheory.Functor.mapGrpIdIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] →       (CategoryTheory.Functor.
id C).mapGrp ≅ CategoryTheory.Functor.id (CategoryTheory.Grp C)
参数：CategoryTheory.Functor.id C；CategoryTheory.Grp C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapGrpIdIso : mapGrp (𝟭 C) ≅ 𝟭 (Grp C) :=
  NatIso.ofComponents fun X ↦ Grp.mkIso (.refl _)

set_option backward.isDefEq.respectTransparency false in
/-- The composition functor is also the composition on group objects. -/
@[to_additive (attr := simps!)
/-- The composition functor is also the composition on additive group objects. -/]
/-
**CategoryTheory.Functor.mapGrpCompIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] →       {D : Type u₂} →         
[inst_2 : CategoryTheory.Category.{v₂, u₂} D] →           [inst_3 : CategoryTheo
ry.CartesianMonoidalCategory D] →             {E : Type u₃} →               [ins
t_4 : CategoryTheory.Category.{v₃, u₃} E] →                 [inst_5 : CategoryTh
eory.CartesianMonoidalCategory E] →                   {F : CategoryTheory.Functo
r C D} →                     {G : CategoryTheory.Functor D E} →                 
      [inst_6 : F.Monoidal] → [inst_7 : G.Monoidal] → (F.comp G).mapGrp ≅ F.mapG
rp.comp G.mapGrp
参数：F.comp G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapGrpCompIso : (F ⋙ G).mapGrp ≅ F.mapGrp ⋙ G.mapGrp :=
  NatIso.ofComponents fun X ↦ Grp.mkIso (.refl _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Natural transformations between functors lift to group objects. -/
@[to_additive (attr := simps!)
/-- Natural transformations between functors lift to additive group objects. -/]
/-
**CategoryTheory.Functor.mapGrpNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] →       {D : Type u₂} →         
[inst_2 : CategoryTheory.Category.{v₂, u₂} D] →           [inst_3 : CategoryTheo
ry.CartesianMonoidalCategory D] →             {F F' : CategoryTheory.Functor C D
} →               [inst_4 : F.Monoidal] → [inst_5 : F'.Monoidal] → (F ⟶ F') → (F
.mapGrp ⟶ F'.mapGrp)
参数：F ⟶ F'；F.mapGrp ⟶ F'.mapGrp。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.IsMonoidal.of_cartesianMonoidalCategory`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Ca
rtesianMonoidalCategory C]   {D : Type u₂} [inst_2 : …
-/
def mapGrpNatTrans (f : F ⟶ F') : F.mapGrp ⟶ F'.mapGrp where
  app X := Grp.homMk' ((mapMonNatTrans f).app X.toMon)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Natural isomorphisms between functors lift to group objects. -/
@[to_additive (attr := simps!)
/-- Natural isomorphisms between functors lift to additive group objects. -/]
/-
**CategoryTheory.Functor.mapGrpNatIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] →       {D : Type u₂} →         
[inst_2 : CategoryTheory.Category.{v₂, u₂} D] →           [inst_3 : CategoryTheo
ry.CartesianMonoidalCategory D] →             {F F' : CategoryTheory.Functor C D
} →               [inst_4 : F.Monoidal] → [inst_5 : F'.Monoidal] → (F ≅ F') → (F
.mapGrp ≅ F'.mapGrp)
参数：F ≅ F'；F.mapGrp ≅ F'.mapGrp。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapGrpNatIso (e : F ≅ F') : F.mapGrp ≅ F'.mapGrp :=
  NatIso.ofComponents fun X ↦ Grp.mkIso (e.app _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
attribute [local instance] Monoidal.ofChosenFiniteProducts in
/-- `mapGrp` is functorial in the left-exact functor. -/
@[to_additive (attr := simps)
/-- `mapAddGrp` is functorial in the left-exact functor. -/]
/-
**CategoryTheory.Functor.mapGrpFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] →       {D : Type u₂} →         
[inst_2 : CategoryTheory.Category.{v₂, u₂} D] →           [inst_3 : CategoryTheo
ry.CartesianMonoidalCategory D] →             CategoryTheory.Functor (C ⥤ₗ D) (C
ategoryTheory.Functor (CategoryTheory.Grp C) (CategoryTheory.Grp D))
参数：C ⥤ₗ D；CategoryTheory.Functor (CategoryTheory.Grp C) (CategoryTheory.Grp D)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def mapGrpFunctor : (C ⥤ₗ D) ⥤ Grp C ⥤ Grp D where
  obj F := F.1.mapGrp
  map {F G} α := { app A := Grp.homMk'' (α.hom.app A.X) }

/-- Pullback a group object along a fully faithful monoidal functor. -/
@[to_additive (attr := simps)
/-- Pullback an additive group object along a fully faithful monoidal functor. -/]
/-
**CategoryTheory.Functor.FullyFaithful.grpObj** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Functor.FullyFaithful`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] →       {D : Type u₂} →         
[inst_2 : CategoryTheory.Category.{v₂, u₂} D] →           [inst_3 : CategoryTheo
ry.CartesianMonoidalCategory D] →             {F : CategoryTheory.Functor C D} →
               [F.Monoidal] → F.FullyFaithful → (X : C) → [CategoryTheory.GrpObj
 (F.obj X)] → CategoryTheory.GrpObj X
参数：X : C；F.obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev FullyFaithful.grpObj (hF : F.FullyFaithful) (X : C) [GrpObj (F.obj X)] :
    GrpObj X where
  __ := hF.monObj X
  inv := hF.preimage ι[F.obj X]
  left_inv := hF.map_injective <| by
    simp [OplaxMonoidal.η_of_cartesianMonoidalCategory]
  right_inv := hF.map_injective <| by
    simp [OplaxMonoidal.η_of_cartesianMonoidalCategory]

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] MonObj.ofIso_one MonObj.ofIso_mul in
/-- The essential image of a full and faithful functor between cartesian-monoidal categories is the
same on group objects as on objects. -/
@[to_additive (attr := simp)
/-- The essential image of a full and faithful functor between cartesian-monoidal categories is the
same on additive group objects as on objects. -/]
/-
**CategoryTheory.Functor.essImage_mapGrp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   {D : Type u₂} [inst_2 : CategoryTheory
.Category.{v₂, u₂} D] [inst_3 : CategoryTheory.CartesianMonoidalCategory D]   {F
 : CategoryTheory.Functor C D} [inst_4 : F.Monoidal] [F.Full] [F.Faithful] {G : 
CategoryTheory.Grp D},   F.mapGrp.essImage G ↔ F.essImage G.X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonObj.ofIso_one`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {M X : C}   [i
nst_2 : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.FullyFaithful.map_preimage`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.Monoidal.ε_η_assoc`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D :
 Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.MonObj.ofIso_mul`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {M X : C}   [i
nst_2 : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.Monoidal.μ_δ_assoc`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D :
 Type u₂}   {inst_2 : CategoryT…
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
/-
**CategoryTheory.Functor.mapGrp.instMonoidal** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Functor.mapGrp`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] →       {D : Type u₂} →         
[inst_2 : CategoryTheory.Category.{v₂, u₂} D] →           [inst_3 : CategoryTheo
ry.CartesianMonoidalCategory D] →             [inst_4 : CategoryTheory.BraidedCa
tegory C] →               [inst_5 : CategoryTheory.BraidedCategory D] →         
        (F : CategoryTheory.Functor C D) → [inst_6 : F.Braided] → F.mapGrp.Monoi
dal
参数：F : CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.Functor.mapGrp.instBraided** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Functor.mapGrp`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] →       {D : Type u₂} →         
[inst_2 : CategoryTheory.Category.{v₂, u₂} D] →           [inst_3 : CategoryTheo
ry.CartesianMonoidalCategory D] →             [inst_4 : CategoryTheory.BraidedCa
tegory C] →               [inst_5 : CategoryTheory.BraidedCategory D] →         
        (F : CategoryTheory.Functor C D) → [inst_6 : F.Braided] → F.mapGrp.Braid
ed
参数：F : CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.Adjunction.mapGrp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Adj
unction`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] →       {D : Type u₂} →         
[inst_2 : CategoryTheory.Category.{v₂, u₂} D] →           [inst_3 : CategoryTheo
ry.CartesianMonoidalCategory D] →             {F : CategoryTheory.Functor C D} →
               {G : CategoryTheory.Functor D C} →                 (F ⊣ G) → [ins
t_4 : F.Monoidal] → [inst_5 : G.Monoidal] → F.mapGrp ⊣ G.mapGrp
参数：F ⊣ G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.Equivalence.mapGrp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Eq
uivalence`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] →       {D : Type u₂} →         
[inst_2 : CategoryTheory.Category.{v₂, u₂} D] →           [inst_3 : CategoryTheo
ry.CartesianMonoidalCategory D] →             (e : C ≌ D) → [e.functor.Monoidal]
 → [e.inverse.Monoidal] → CategoryTheory.Grp C ≌ CategoryTheory.Grp D
参数：e : C ≌ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapGrp : Grp C ≌ Grp D where
  functor := e.functor.mapGrp
  inverse := e.inverse.mapGrp
  unitIso := mapGrpIdIso.symm ≪≫ mapGrpNatIso e.unitIso ≪≫ mapGrpCompIso
  counitIso := mapGrpCompIso.symm ≪≫ mapGrpNatIso e.counitIso ≪≫ mapGrpIdIso

end CategoryTheory.Equivalence

