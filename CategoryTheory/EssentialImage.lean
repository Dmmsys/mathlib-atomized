/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Order.BooleanAlgebra.Defs

/-!
# Essential image of a functor

The essential image `essImage` of a functor consists of the objects in the target category which
are isomorphic to an object in the image of the object function.
This, for instance, allows us to talk about objects belonging to a subcategory expressed as a
functor rather than a subtype, preserving the principle of equivalence. For example this lets us
define exponential ideals.

The essential image can also be seen as a subcategory of the target category, and witnesses that
a functor decomposes into an essentially surjective functor and a fully faithful functor.
(TODO: show that this decomposition forms an orthogonal factorisation system).
-/

@[expose] public section


universe v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] {F : C ⥤ D} {G : D ⥤ E}

namespace Functor

/-- The essential image of a functor `F` consists of those objects in the target category which are
isomorphic to an object in the image of the function `F.obj`. In other words, this is the closure
under isomorphism of the function `F.obj`.
This is the "non-evil" way of describing the image of a functor.
-/
/-
**CategoryTheory.Functor.essImage** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Func
tor`。
形式化陈述：essImage (F : C ⥤ D) : ObjectProperty D
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The essential image of a functor `F` consists of those objects in the target cat
egory which are
isomorphic to an object in the image of the function `F.obj`. In other words, th
is is the closure
under isomorphism of the function `F.obj`.
This is the "non-evil" way of describing the image of a functor.
-/
def essImage (F : C ⥤ D) : ObjectProperty D := fun Y => ∃ X : C, Nonempty (F.obj X ≅ Y)

/-- Get the witnessing object that `Y` is in the subcategory given by `F`. -/
/-
**CategoryTheory.Functor.essImage.witness** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor.essImage`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → {F : CategoryThe
ory.Functor C D} → {Y : D} → F.essImage Y → C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Get the witnessing object that `Y` is in the subcategory given by `F`.
-/
def essImage.witness {Y : D} (h : F.essImage Y) : C :=
  h.choose
/-
**CategoryTheory.Functor.isoClosure_eq_essImage** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Functor`。
形式化陈述：isoClosure_eq_essImage : ObjectProperty.isoClosure (· in Set.range F.obj) 
= F.essImage
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma isoClosure_eq_essImage : ObjectProperty.isoClosure (· ∈ Set.range F.obj) = F.essImage := by
  ext
  exact ⟨fun ⟨_, ⟨Z, rfl⟩, ⟨e⟩⟩ ↦ ⟨Z, ⟨e.symm⟩⟩, fun ⟨Z, ⟨e⟩⟩ ↦ ⟨F.obj Z, ⟨Z, rfl⟩, ⟨e.symm⟩⟩⟩

/-- Extract the isomorphism between `F.obj h.witness` and `Y` itself. -/
/-
**CategoryTheory.Functor.essImage.getIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Functor.essImage`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {F : Cat
egoryTheory.Functor C D} → {Y : D} → (h : F.essImage Y) → F.obj h.witness ≅ Y
参数：h : F.essImage Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract the isomorphism between `F.obj h.witness` and `Y` itself.
-/
def essImage.getIso {Y : D} (h : F.essImage Y) : F.obj h.witness ≅ Y :=
  Classical.choice h.choose_spec

/-- Being in the essential image is a "hygienic" property: it is preserved under isomorphism. -/
/-
**CategoryTheory.Functor.essImage.ofIso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Functor.essImage`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor C D}
 {Y Y' : D} (h : Y ≅ Y'), F.essImage Y → F.essImage Y'
参数：h : Y ≅ Y'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…

--- 原说明 ---
Being in the essential image is a "hygienic" property: it is preserved under iso
morphism.
-/
theorem essImage.ofIso {Y Y' : D} (h : Y ≅ Y') (hY : essImage F Y) : essImage F Y' :=
  hY.imp fun _ => Nonempty.map (· ≪≫ h)
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : F.essImage.IsClosedUnderIsomorphisms where
  of_iso e h := essImage.ofIso e h

/-- If `Y` is in the essential image of `F` then it is in the essential image of `F'` as long as
`F ≅ F'`.
-/
/-
**CategoryTheory.Functor.essImage.ofNatIso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Functor.essImage`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F F' : CategoryTheory.Functor C
 D} (h : F ≅ F') {Y : D}, F.essImage Y → F'.essImage Y
参数：h : F ≅ F'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…

--- 原说明 ---
If `Y` is in the essential image of `F` then it is in the essential image of `F'
` as long as
`F ≅ F'`.
-/
theorem essImage.ofNatIso {F' : C ⥤ D} (h : F ≅ F') {Y : D} (hY : essImage F Y) :
    essImage F' Y :=
  hY.imp fun X => Nonempty.map fun t => h.symm.app X ≪≫ t

/-- Isomorphic functors have equal essential images. -/
/-
**CategoryTheory.Functor.essImage_eq_of_natIso** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：essImage_eq_of_natIso {F' : C ⥤ D} (h : F ≅ F') : essImage F = essImage F'
参数：h : F ≅ F'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Functor.essImage.ofNatIso`：∀ {C : Type u₁} {D : Type u₂} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F F' : CategoryTh…

--- 原说明 ---
Isomorphic functors have equal essential images.
-/
theorem essImage_eq_of_natIso {F' : C ⥤ D} (h : F ≅ F') : essImage F = essImage F' :=
  funext fun _ => propext ⟨essImage.ofNatIso h, essImage.ofNatIso h.symm⟩

/-- An object in the image is in the essential image. -/
/-
**CategoryTheory.Functor.obj_mem_essImage** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：obj_mem_essImage (F : D ⥤ C) (Y : D) : essImage F (F.obj Y)
参数：F : D ⥤ C；Y : D。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object in the image is in the essential image.
-/
theorem obj_mem_essImage (F : D ⥤ C) (Y : D) : essImage F (F.obj Y) :=
  ⟨Y, ⟨Iso.refl _⟩⟩

/-- The essential image of a functor, interpreted as a full subcategory of the target category. -/
/-
**CategoryTheory.Functor.EssImageSubcategory** 是 Mathlib 中的一个缩写定义，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：EssImageSubcategory (F : C ⥤ D)
参数：F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The essential image of a functor, interpreted as a full subcategory of the targe
t category.
-/
abbrev EssImageSubcategory (F : C ⥤ D) := F.essImage.FullSubcategory
/-
**CategoryTheory.Functor.essImage_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：essImage_ext (F : C ⥤ D) {X Y : F.EssImageSubcategory} (f g : X ⟶ Y) (h : 
F.essImage.ι.map f = F.essImage.ι.map g) : f = g
参数：F : C ⥤ D；f g : X ⟶ Y；h : F.essImage.ι.map f = F.essImage.ι.map g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
-/
lemma essImage_ext (F : C ⥤ D) {X Y : F.EssImageSubcategory} (f g : X ⟶ Y)
    (h : F.essImage.ι.map f = F.essImage.ι.map g) : f = g :=
  F.essImage.ι.map_injective h

/--
Given a functor `F : C ⥤ D`, we have an (essentially surjective) functor from `C` to the essential
image of `F`.
-/
@[implicit_reducible, simps!]
/-
**CategoryTheory.Functor.toEssImage** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：toEssImage (F : C ⥤ D) : C ⥤ F.EssImageSubcategory
参数：F : C ⥤ D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.obj_mem_essImage`：obj_mem_essImage (F : D ⥤ C) (Y
 : D) : essImage F (F.obj Y)

--- 原说明 ---
Given a functor `F : C ⥤ D`, we have an (essentially surjective) functor from `C
` to the essential
image of `F`.
-/
def toEssImage (F : C ⥤ D) : C ⥤ F.EssImageSubcategory :=
  F.essImage.lift F (obj_mem_essImage _)

/-- The functor `F` factorises through its essential image, where the first functor is essentially
surjective and the second is fully faithful.
-/
@[simps!]
/-
**CategoryTheory.Functor.toEssImageComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `F` factorises through its essential image, where the first functor 
is essentially
surjective and the second is fully faithful.
-/
def toEssImageCompι (F : C ⥤ D) : F.toEssImage ⋙ F.essImage.ι ≅ F :=
  ObjectProperty.liftCompιIso _ _ _

/-- A functor `F : C ⥤ D` is essentially surjective if every object of `D` is in the essential
image of `F`. In other words, for every `Y : D`, there is some `X : C` with `F.obj X ≅ Y`. -/
@[stacks 001C]
/-
**CategoryTheory.Functor.EssSurj** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Fun
ctor`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.F
unctor C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : C ⥤ D` is essentially surjective if every object of `D` is in the
 essential
image of `F`. In other words, for every `Y : D`, there is some `X : C` with `F.o
bj X ≅ Y`.
-/
class EssSurj (F : C ⥤ D) : Prop where
  /-- All the objects of the target category are in the essential image. -/
  mem_essImage (F) (Y : D) : F.essImage Y
/-
**CategoryTheory.Functor.EssSurj.toEssImage** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Functor.EssSurj`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor C D}
, F.toEssImage.EssSurj
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance EssSurj.toEssImage : EssSurj F.toEssImage where
  mem_essImage := fun ⟨_, hY⟩ => ⟨hY.witness, ⟨F.essImage.isoMk hY.getIso⟩⟩
/-
**CategoryTheory.Functor.essSurj_of_surj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：essSurj_of_surj (h : Function.Surjective F.obj) : EssSurj F where mem_essI
mage Y
参数：h : Function.Surjective F.obj。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.obj_mem_essImage`：obj_mem_essImage (F : D ⥤ C) (Y
 : D) : essImage F (F.obj Y)
-/
theorem essSurj_of_surj (h : Function.Surjective F.obj) : EssSurj F where
  mem_essImage Y := by
    obtain ⟨X, rfl⟩ := h Y
    apply obj_mem_essImage

section EssSurj
variable (F)
variable [F.EssSurj]

/-- Given an essentially surjective functor, we can find a preimage for every object `Y` in the
    codomain. Applying the functor to this preimage will yield an object isomorphic to `Y`, see
    `obj_obj_preimage_iso`. -/
/-
**CategoryTheory.Functor.objPreimage** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：objPreimage (Y : D) : C
参数：Y : D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.EssSurj.mem_essImage`：∀ {C : Type u₁} {D : Type u
₂} {inst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   (F : CategoryTheor…

--- 原说明 ---
Given an essentially surjective functor, we can find a preimage for every object
 `Y` in the
    codomain. Applying the functor to this preimage will yield an object isomorp
hic to `Y`, see
    `obj_obj_preimage_iso`.
-/
def objPreimage (Y : D) : C :=
  essImage.witness (EssSurj.mem_essImage F Y)

/-- Applying an essentially surjective functor to a preimage of `Y` yields an object that is
    isomorphic to `Y`. -/
/-
**CategoryTheory.Functor.objObjPreimageIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：objObjPreimageIso (Y : D) : F.obj (F.objPreimage Y) ≅ Y
参数：Y : D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.EssSurj.mem_essImage`：∀ {C : Type u₁} {D : Type u
₂} {inst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   (F : CategoryTheor…

--- 原说明 ---
Applying an essentially surjective functor to a preimage of `Y` yields an object
 that is
    isomorphic to `Y`.
-/
def objObjPreimageIso (Y : D) : F.obj (F.objPreimage Y) ≅ Y :=
  Functor.essImage.getIso _

/-- The induced functor of a faithful functor is faithful. -/
/-
**CategoryTheory.Functor.Faithful.toEssImage** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Functor.Faithful`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [F.Faithful], F.toEssImage.Faithful
参数：F : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.obj_mem_essImage`：obj_mem_essImage (F : D ⥤ C) (Y
 : D) : essImage F (F.obj Y)
· 使用定理 `CategoryTheory.ObjectProperty.instFaithfulFullSubcategoryLift`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : Category
Theory.Category.{v', u'} D]   (P : CategoryTheory.O…

--- 原说明 ---
The induced functor of a faithful functor is faithful.
-/
instance Faithful.toEssImage (F : C ⥤ D) [Faithful F] : Faithful F.toEssImage := by
  dsimp only [Functor.toEssImage]
  infer_instance

/-- The induced functor of a full functor is full. -/
/-
**CategoryTheory.Functor.Full.toEssImage** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Functor.Full`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [F.Full], F.toEssImage.Full
参数：F : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.obj_mem_essImage`：obj_mem_essImage (F : D ⥤ C) (Y
 : D) : essImage F (F.obj Y)
· 使用定理 `CategoryTheory.ObjectProperty.instFullFullSubcategoryLift`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheo
ry.Category.{v', u'} D]   (P : CategoryTheory.O…

--- 原说明 ---
The induced functor of a full functor is full.
-/
instance Full.toEssImage (F : C ⥤ D) [Full F] : Full F.toEssImage := by
  dsimp only [Functor.toEssImage]
  infer_instance
/-
**CategoryTheory.Functor.instEssSurjId** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：instEssSurjId : EssSurj (𝟭 C) where mem_essImage Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instEssSurjId : EssSurj (𝟭 C) where
  mem_essImage Y := ⟨Y, ⟨Iso.refl _⟩⟩
/-
**CategoryTheory.Functor.essSurj_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：essSurj_of_iso {F G : C ⥤ D} [EssSurj F] (α : F ≅ G) : EssSurj G where mem
_essImage Y
参数：α : F ≅ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.essImage.ofNatIso`：∀ {C : Type u₁} {D : Type u₂} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F F' : CategoryTh…
· 使用定理 `CategoryTheory.Functor.EssSurj.mem_essImage`：∀ {C : Type u₁} {D : Type u
₂} {inst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   (F : CategoryTheor…
-/
lemma essSurj_of_iso {F G : C ⥤ D} [EssSurj F] (α : F ≅ G) : EssSurj G where
  mem_essImage Y := Functor.essImage.ofNatIso α (EssSurj.mem_essImage F Y)
/-
**CategoryTheory.Functor.essSurj_comp** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：essSurj_comp (F : C ⥤ D) (G : D ⥤ E) [F.EssSurj] [G.EssSurj] : (F ⋙ G).Ess
Surj where mem_essImage Z
参数：F : C ⥤ D；G : D ⥤ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance essSurj_comp (F : C ⥤ D) (G : D ⥤ E) [F.EssSurj] [G.EssSurj] :
    (F ⋙ G).EssSurj where
  mem_essImage Z := ⟨_, ⟨G.mapIso (F.objObjPreimageIso _) ≪≫ G.objObjPreimageIso Z⟩⟩
/-
**CategoryTheory.Functor.essSurj_of_comp_fully_faithful** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Functor`。
形式化陈述：essSurj_of_comp_fully_faithful (F : C ⥤ D) (G : D ⥤ E) [(F ⋙ G).EssSurj] [
G.Faithful] [G.Full] : F.EssSurj where mem_essImage X
参数：F : C ⥤ D；G : D ⥤ E；F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma essSurj_of_comp_fully_faithful (F : C ⥤ D) (G : D ⥤ E) [(F ⋙ G).EssSurj]
    [G.Faithful] [G.Full] : F.EssSurj where
  mem_essImage X := ⟨_, ⟨G.preimageIso ((F ⋙ G).objObjPreimageIso (G.obj X))⟩⟩

variable {F} {X : E}

/-- Pre-composing by an essentially surjective functor doesn't change the essential image. -/
/-
**CategoryTheory.Functor.essImage_comp_apply_of_essSurj** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Functor`。
形式化陈述：essImage_comp_apply_of_essSurj : (F ⋙ G).essImage X ↔ G.essImage X where m
p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.EssSurj.mem_essImage`：∀ {C : Type u₁} {D : Type u
₂} {inst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   (F : CategoryTheor…

--- 原说明 ---
Pre-composing by an essentially surjective functor doesn't change the essential 
image.
-/
lemma essImage_comp_apply_of_essSurj : (F ⋙ G).essImage X ↔ G.essImage X where
  mp := fun ⟨Y, ⟨e⟩⟩ ↦ ⟨F.obj Y, ⟨e⟩⟩
  mpr := fun ⟨Y, ⟨e⟩⟩ ↦
    let ⟨Z, ⟨e'⟩⟩ := Functor.EssSurj.mem_essImage F Y; ⟨Z, ⟨(G.mapIso e').trans e⟩⟩

/-- Pre-composing by an essentially surjective functor doesn't change the essential image. -/
/-
**CategoryTheory.Functor.essImage_comp_of_essSurj** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} {E : Type u₃} [inst : CategoryTheory.Categor
y.{v₁, u₁} C]   [inst_1 : CategoryTheory.Category.{v₂, u₂} D] [inst_2 : Category
Theory.Category.{v₃, u₃} E]   {F : CategoryTheory.Functor C D} {G : CategoryTheo
ry.Functor D E} [F.EssSurj], (F.comp G).essImage = G.essImage
参数：F.comp G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.Functor.essImage_comp_apply_of_essSurj`：essImage_comp_app
ly_of_essSurj : (F ⋙ G).essImage X ↔ G.essImage X where mp

--- 原说明 ---
Pre-composing by an essentially surjective functor doesn't change the essential 
image.
-/
@[simp] lemma essImage_comp_of_essSurj : (F ⋙ G).essImage = G.essImage :=
  funext fun _X ↦ propext essImage_comp_apply_of_essSurj

end EssSurj

section

variable {J C D : Type*} [Category* J] [Category* C] [Category* D]
  (G : J ⥤ D) (F : C ⥤ D) [F.Full] [F.Faithful] (hG : ∀ j, F.essImage (G.obj j))

/-- Lift a functor `G : J ⥤ D` to the essential image of a fully faithful functor `F : C ⥤ D` to a
functor `G' : J ⥤ C` such that `G' ⋙ F ≅ G`. See `essImage.liftFunctorCompIso`. -/
@[implicit_reducible, simps]
/-
**CategoryTheory.Functor.essImage.liftFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Functor.essImage`。
形式化陈述：{J : Type u_1} →   {C : Type u_2} →     {D : Type u_3} →       [inst : Cat
egoryTheory.Category.{v_1, u_1} J] →         [inst_1 : CategoryTheory.Category.{
v_2, u_2} C] →           [inst_2 : CategoryTheory.Category.{v_3, u_3} D] →      
       (G : CategoryTheory.Functor J D) →               (F : CategoryTheory.Func
tor C D) →                 [F.Full] → [F.Faithful] → (∀ (j : J), F.essImage (G.o
bj j)) → CategoryTheory.Functor J C
参数：G : CategoryTheory.Functor J D；F : CategoryTheory.Functor C D；∀ (j : J), F.es
sImage (G.obj j)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.EssSurj.toEssImage`：∀ {C : Type u₁} {D : Type u₂}
 [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…

--- 原说明 ---
Lift a functor `G : J ⥤ D` to the essential image of a fully faithful functor `F
 : C ⥤ D` to a
functor `G' : J ⥤ C` such that `G' ⋙ F ≅ G`. See `essImage.liftFunctorCompIso`.
-/
def essImage.liftFunctor : J ⥤ C where
  obj j := F.toEssImage.objPreimage ⟨G.obj j, hG j⟩
  map {i j} f :=
    F.preimage <|
    (F.toEssImage.objObjPreimageIso ⟨G.obj i, hG i⟩).hom.hom ≫ G.map f ≫
      (F.toEssImage.objObjPreimageIso ⟨G.obj j, hG j⟩).inv.hom
  map_id _ := F.map_injective (by simp)
  map_comp _ _ := F.map_injective (by simp)

/-- A functor `G : J ⥤ D` to the essential image of a fully faithful functor `F : C ⥤ D` does
factor through `essImage.liftFunctor G F hG`. -/
/-
**CategoryTheory.Functor.essImage.liftFunctorCompIso** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Functor.essImage`。
形式化陈述：{J : Type u_1} →   {C : Type u_2} →     {D : Type u_3} →       [inst : Cat
egoryTheory.Category.{v_1, u_1} J] →         [inst_1 : CategoryTheory.Category.{
v_2, u_2} C] →           [inst_2 : CategoryTheory.Category.{v_3, u_3} D] →      
       (G : CategoryTheory.Functor J D) →               (F : CategoryTheory.Func
tor C D) →                 [inst_3 : F.Full] →                   [inst_4 : F.Fai
thful] →                     (hG : ∀ (j : J), F.essImage (G.obj j)) →           
            (CategoryTheory.Functor.essImage.liftFunctor G F hG).comp F ≅ G
参数：G : CategoryTheory.Functor J D；F : CategoryTheory.Functor C D；hG : ∀ (j : J),
 F.essImage (G.obj j)；CategoryTheory.Functor.essImage.liftFunctor G F hG。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.EssSurj.toEssImage`：∀ {C : Type u₁} {D : Type u₂}
 [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…

--- 原说明 ---
A functor `G : J ⥤ D` to the essential image of a fully faithful functor `F : C 
⥤ D` does
factor through `essImage.liftFunctor G F hG`.
-/
@[simps!] def essImage.liftFunctorCompIso : essImage.liftFunctor G F hG ⋙ F ≅ G :=
  NatIso.ofComponents
    (fun i ↦ F.essImage.ι.mapIso (F.toEssImage.objObjPreimageIso ⟨G.obj i, hG _⟩))

end

/-
**CategoryTheory.Functor.essImage_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Fun
ctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma essImage_ι_comp (F : C ⥤ D) (P : ObjectProperty C) :
    (P.ι ⋙ F).essImage = P.map F := by
  ext Y
  constructor
  · rintro ⟨X, ⟨e⟩⟩
    exact ⟨X.1, X.2, ⟨e⟩⟩
  · rintro ⟨X, hX, ⟨e⟩⟩
    exact ⟨⟨X, hX⟩, ⟨e⟩⟩
/-
**CategoryTheory.Functor.full_of_comp_essSurj** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：full_of_comp_essSurj (F : D ⥤ E) (L : C ⥤ D) [EssSurj L] (h : forall ⦃X₁ X
₂ : C⦄ (φ : F.obj (L.obj X₁) ⟶ F.obj (L.obj X₂)), exists (f : L.obj X₁ ⟶ L.obj X
₂), F.map f = φ) : F.Full
参数：F : D ⥤ E；L : C ⥤ D；h : forall ⦃X₁ X₂ : C⦄ (φ : F.obj (L.obj X₁) ⟶ F.obj (L.o
bj X₂)), exists (f : L.obj X₁ ⟶ L.obj X₂), F.map f = φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Iso.map_inv_hom_id`：map_inv_hom_id (F : C ⥤ D) : F.map e.
inv ≫ F.map e.hom = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.map_inv_hom_id_assoc`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1,
 u_1} D]   {X Y : C} (e : X ≅…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma full_of_comp_essSurj (F : D ⥤ E) (L : C ⥤ D) [EssSurj L]
    (h : ∀ ⦃X₁ X₂ : C⦄ (φ : F.obj (L.obj X₁) ⟶ F.obj (L.obj X₂)),
      ∃ (f : L.obj X₁ ⟶ L.obj X₂), F.map f = φ) :
    F.Full := ⟨by
  intro X₁ X₂ ψ
  obtain ⟨f, hf⟩ := h (F.map (L.objObjPreimageIso X₁).hom ≫ ψ ≫
    F.map (L.objObjPreimageIso X₂).inv)
  exact ⟨(L.objObjPreimageIso X₁).inv ≫ f ≫ (L.objObjPreimageIso X₂).hom, by simp [hf]⟩⟩
/-
**CategoryTheory.Functor.faithful_of_comp_essSurj** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：faithful_of_comp_essSurj (F : D ⥤ E) (L : C ⥤ D) [EssSurj L] (h : forall ⦃
X₁ X₂ : C⦄ (f g : L.obj X₁ ⟶ L.obj X₂), F.map f = F.map g -> f = g) : F.Faithful
 where map_injective hfg
参数：F : D ⥤ E；L : C ⥤ D；h : forall ⦃X₁ X₂ : C⦄ (f g : L.obj X₁ ⟶ L.obj X₂), F.map
 f = F.map g -> f = g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.IsIso.mono_of_iso`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   CategoryThe
ory.Mono f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.IsIso.epi_of_iso`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   CategoryTheo
ry.Epi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma faithful_of_comp_essSurj (F : D ⥤ E) (L : C ⥤ D) [EssSurj L]
    (h : ∀ ⦃X₁ X₂ : C⦄ (f g : L.obj X₁ ⟶ L.obj X₂), F.map f = F.map g → f = g) :
    F.Faithful where
  map_injective hfg := by
    rw [← cancel_mono (L.objObjPreimageIso _).inv, ← cancel_epi (L.objObjPreimageIso _).hom]
    exact h _ _ (by simp [hfg])

end Functor

/-
**CategoryTheory.ObjectProperty.map_top** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.ObjectProperty`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
, ⊤.map F = F.essImage
参数：F : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma ObjectProperty.map_top (F : C ⥤ D) :
    (⊤ : ObjectProperty C).map F = F.essImage := by
  ext Y
  refine ⟨?_, ?_⟩
  · rintro ⟨X, _, ⟨e⟩⟩
    exact ⟨X, ⟨e⟩⟩
  · rintro ⟨X, ⟨e⟩⟩
    exact ⟨X, by simp, ⟨e⟩⟩

end CategoryTheory

