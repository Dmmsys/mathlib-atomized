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
/-
**CategoryTheory.ObjectProperty.FullSubcategory** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cat
egoryTheory.ObjectProperty`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
ObjectProperty C → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subtype-like structure for full subcategories. Morphisms just ignore the prope
rty. We don't use
actual subtypes since the simp-normal form `↑X` of `X.val` does not work well fo
r full
subcategories.
-/
structure FullSubcategory where
  /-- The category of which this is a full subcategory -/
  obj : C
  /-- The predicate satisfied by all objects in this subcategory -/
  property : P obj
/-
**CategoryTheory.ObjectProperty.FullSubcategory.category** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.ObjectProperty.FullSubcategory`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (P : Cate
goryTheory.ObjectProperty C) → CategoryTheory.Category.{v, u} P.FullSubcategory
参数：P : CategoryTheory.ObjectProperty C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance FullSubcategory.category : Category.{v} P.FullSubcategory :=
  inferInstanceAs (Category (InducedCategory _ FullSubcategory.obj))
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.Nonempty] : Nonempty P.FullSubcategory :=
  Nonempty.intro ⟨P.arbitrary, P.prop_arbitrary⟩

@[ext]
/-
**CategoryTheory.ObjectProperty.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.ObjectProperty`。
形式化陈述：hom_ext {X Y : P.FullSubcategory} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = 
g
参数：h : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.InducedCategory.hom_ext`：hom_ext {X Y : InducedCategory D
 F} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
-/
lemma hom_ext {X Y : P.FullSubcategory} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g :=
  InducedCategory.hom_ext h

/-- The forgetful functor from a full subcategory into the original category
("forgetting" the condition).
-/
@[implicit_reducible]
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from a full subcategory into the original category
("forgetting" the condition).
-/
def ι : P.FullSubcategory ⥤ C :=
  inducedFunctor FullSubcategory.obj

@[simp]
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_obj {X} : P.ι.obj X = X.obj :=
  rfl

@[simp]
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_map {X Y} {f : X ⟶ Y} : P.ι.map f = f.hom :=
  rfl
/-
**CategoryTheory.ObjectProperty.prop_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
ObjectProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prop_ι_obj (X) : P (P.ι.obj X) := X.2

@[simp]
/-
**CategoryTheory.ObjectProperty.FullSubcategory.id_hom** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.ObjectProperty.FullSubcategory`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheo
ry.ObjectProperty C) (X : P.FullSubcategory),   (CategoryTheory.CategoryStruct.i
d X).hom = CategoryTheory.CategoryStruct.id X.obj
参数：P : CategoryTheory.ObjectProperty C；X : P.FullSubcategory；CategoryTheory.Cate
goryStruct.id X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma FullSubcategory.id_hom (X : P.FullSubcategory) :
    InducedCategory.Hom.hom (𝟙 X) = 𝟙 X.obj := rfl

@[simp, reassoc]
/-
**CategoryTheory.ObjectProperty.FullSubcategory.comp_hom** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.ObjectProperty.FullSubcategory`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheo
ry.ObjectProperty C)   {X Y Z : P.FullSubcategory} (f : X ⟶ Y) (g : Y ⟶ Z),   (C
ategoryTheory.CategoryStruct.comp f g).hom = CategoryTheory.CategoryStruct.comp 
f.hom g.hom
参数：P : CategoryTheory.ObjectProperty C；f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.Catego
ryStruct.comp f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma FullSubcategory.comp_hom {X Y Z : P.FullSubcategory} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

variable {P} in
/-- Constructor for morphisms in a full subcategory. -/
@[simps, implicit_reducible]
/-
**CategoryTheory.ObjectProperty.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
ObjectProperty`。
形式化陈述：homMk {X Y : P.FullSubcategory} (f : X.obj ⟶ Y.obj) : X ⟶ Y where hom
参数：f : X.obj ⟶ Y.obj。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms in a full subcategory.
-/
def homMk {X Y : P.FullSubcategory} (f : X.obj ⟶ Y.obj) : X ⟶ Y where
  hom := f

variable {P} in
/-
**CategoryTheory.ObjectProperty.homMk_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.ObjectProperty`。
形式化陈述：homMk_surjective {X Y : P.FullSubcategory} : Function.Surjective (homMk : 
(X.obj ⟶ Y.obj) -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk_surjective {X Y : P.FullSubcategory} :
    Function.Surjective (homMk : (X.obj ⟶ Y.obj) → _) :=
  fun f ↦ ⟨f.hom, rfl⟩

/-- The inclusion of a full subcategory is fully faithful. -/
/-
**CategoryTheory.ObjectProperty.fullyFaithful** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categ
oryTheory.ObjectProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of a full subcategory is fully faithful.
-/
abbrev fullyFaithfulι :
    P.ι.FullyFaithful where
  preimage f := homMk _
/-
**CategoryTheory.ObjectProperty.full_** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
ObjectProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance full_ι : P.ι.Full := P.fullyFaithfulι.full
/-
**CategoryTheory.ObjectProperty.faithful_** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.ObjectProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance faithful_ι : P.ι.Faithful := P.fullyFaithfulι.faithful

/-- Constructor for isomorphisms in `P.FullSubcategory` when
`P : ObjectProperty C`. -/
@[simps]
/-
**CategoryTheory.ObjectProperty.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
ObjectProperty`。
形式化陈述：isoMk {X Y : P.FullSubcategory} (e : X.obj ≅ Y.obj) : X ≅ Y where hom
参数：e : X.obj ≅ Y.obj。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for isomorphisms in `P.FullSubcategory` when
`P : ObjectProperty C`.
-/
def isoMk {X Y : P.FullSubcategory} (e : X.obj ≅ Y.obj) : X ≅ Y where
  hom := homMk e.hom
  inv := homMk e.inv

variable {P}

@[reassoc (attr := simp)]
/-
**CategoryTheory.ObjectProperty.isoHom_inv_id_hom** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.ObjectProperty`。
形式化陈述：isoHom_inv_id_hom {X Y : P.FullSubcategory} (e : X ≅ Y) : e.hom.hom ≫ e.in
v.hom = 𝟙 _
参数：e : X ≅ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
-/
lemma isoHom_inv_id_hom {X Y : P.FullSubcategory} (e : X ≅ Y) :
    e.hom.hom ≫ e.inv.hom = 𝟙 _ :=
  P.ι.congr_map e.hom_inv_id

@[reassoc (attr := simp)]
/-
**CategoryTheory.ObjectProperty.isoInv_hom_id_hom** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.ObjectProperty`。
形式化陈述：isoInv_hom_id_hom {X Y : P.FullSubcategory} (e : X ≅ Y) : e.inv.hom ≫ e.ho
m.hom = 𝟙 _
参数：e : X ≅ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
-/
lemma isoInv_hom_id_hom {X Y : P.FullSubcategory} (e : X ≅ Y) :
    e.inv.hom ≫ e.hom.hom = 𝟙 _ :=
  P.ι.congr_map e.inv_hom_id
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : P.FullSubcategory} (f : X ⟶ Y) [IsIso f] : IsIso f.hom :=
  P.ι.map_isIso f

@[simp, push ←]
/-
**CategoryTheory.ObjectProperty.hom_inv** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.ObjectProperty`。
形式化陈述：hom_inv {X Y : P.FullSubcategory} (f : X ⟶ Y) [IsIso f] : (inv f).hom = in
v f.hom
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.eq_inv_of_hom_inv_id`：eq_inv_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : g = inv f
· 使用定理 `CategoryTheory.ObjectProperty.instIsIsoHomFullSubcategory`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C
} {X Y : P.FullSubcategory}   (f : X ⟶ Y) [Cate…
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
-/
lemma hom_inv {X Y : P.FullSubcategory} (f : X ⟶ Y) [IsIso f] : (inv f).hom = inv f.hom :=
  IsIso.eq_inv_of_hom_inv_id (P.ι.congr_map (asIso f).hom_inv_id)
/-
**CategoryTheory.ObjectProperty.isIso_hom_iff** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.ObjectProperty`。
形式化陈述：isIso_hom_iff {X Y : P.FullSubcategory} (f : X ⟶ Y) : IsIso f.hom ↔ IsIso 
f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.ObjectProperty.instIsIsoHomFullSubcategory`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C
} {X Y : P.FullSubcategory}   (f : X ⟶ Y) [Cate…
-/
lemma isIso_hom_iff {X Y : P.FullSubcategory} (f : X ⟶ Y) : IsIso f.hom ↔ IsIso f :=
  ⟨fun _ ↦ (P.isoMk (asIso f.hom)).isIso_hom, fun _ ↦ inferInstance⟩

variable {P' : ObjectProperty C}

/-- If `P` and `P'` are properties of objects such that `P ≤ P'`, there is
an induced functor `P.FullSubcategory ⥤ P'.FullSubcategory`. -/
@[simps, implicit_reducible]
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `P` and `P'` are properties of objects such that `P ≤ P'`, there is
an induced functor `P.FullSubcategory ⥤ P'.FullSubcategory`.
-/
def ιOfLE (h : P ≤ P') : P.FullSubcategory ⥤ P'.FullSubcategory where
  obj X := ⟨X.1, h _ X.2⟩
  map f := homMk f.hom

/-- If `h : P ≤ P'`, then `ιOfLE h` is fully faithful. -/
/-
**CategoryTheory.ObjectProperty.fullyFaithful** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.ObjectProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `h : P ≤ P'`, then `ιOfLE h` is fully faithful.
-/
def fullyFaithfulιOfLE (h : P ≤ P') :
    (ιOfLE h).FullyFaithful where
  preimage f := homMk f.hom
/-
**CategoryTheory.ObjectProperty.full_** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
ObjectProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance full_ιOfLE (h : P ≤ P') : (ιOfLE h).Full := (fullyFaithfulιOfLE h).full
/-
**CategoryTheory.ObjectProperty.faithful_** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.ObjectProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance faithful_ιOfLE (h : P ≤ P') : (ιOfLE h).Faithful := (fullyFaithfulιOfLE h).faithful

/-- If `h : P ≤ P'` is an inequality of properties of objects,
this is the obvious isomorphism `ιOfLE h ⋙ P'.ι ≅ P.ι`. -/
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `h : P ≤ P'` is an inequality of properties of objects,
this is the obvious isomorphism `ιOfLE h ⋙ P'.ι ≅ P.ι`.
-/
def ιOfLECompιIso (h : P ≤ P') : ιOfLE h ⋙ P'.ι ≅ P.ι := Iso.refl _

end

section lift

variable {D : Type u'} [Category.{v'} D] (P Q : ObjectProperty D)
  (F : C ⥤ D) (hF : ∀ X, P (F.obj X))

/-- A functor which maps objects to objects satisfying a certain property induces a lift through
    the full subcategory of objects satisfying that property. -/
@[simps, implicit_reducible]
/-
**CategoryTheory.ObjectProperty.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.O
bjectProperty`。
形式化陈述：lift : C ⥤ FullSubcategory P where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor which maps objects to objects satisfying a certain property induces a 
lift through
    the full subcategory of objects satisfying that property.
-/
def lift : C ⥤ FullSubcategory P where
  obj X := ⟨F.obj X, hF X⟩
  map f := homMk (F.map f)

/-- Composing the lift of a functor through a full subcategory with the inclusion yields the
    original functor. This is actually true definitionally. -/
/-
**CategoryTheory.ObjectProperty.liftComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.ObjectProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing the lift of a functor through a full subcategory with the inclusion yi
elds the
    original functor. This is actually true definitionally.
-/
def liftCompιIso : P.lift F hF ⋙ P.ι ≅ F := Iso.refl _
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_obj_lift_obj (X : C) :
    P.ι.obj ((P.lift F hF).obj X) = F.obj X := rfl
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_obj_lift_map {X Y : C} (f : X ⟶ Y) :
    P.ι.map ((P.lift F hF).map f) = F.map f := rfl
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.Faithful] : (P.lift F hF).Faithful :=
  Functor.Faithful.of_comp_iso (P.liftCompιIso F hF)
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.Full] : (P.lift F hF).Full :=
  Functor.Full.of_comp_faithful_iso (P.liftCompιIso F hF)

variable {Q}

/-- When `h : P ≤ Q`, this is the canonical isomorphism
`P.lift F hF ⋙ ιOfLE h ≅ Q.lift F _`. -/
/-
**CategoryTheory.ObjectProperty.liftComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.ObjectProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `h : P ≤ Q`, this is the canonical isomorphism
`P.lift F hF ⋙ ιOfLE h ≅ Q.lift F _`.
-/
def liftCompιOfLEIso (h : P ≤ Q) :
    P.lift F hF ⋙ ιOfLE h ≅ Q.lift F (fun X ↦ h _ (hF X)) := Iso.refl _

end lift

end ObjectProperty

end CategoryTheory

