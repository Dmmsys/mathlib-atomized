/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Yoneda

/-!
# Domain of definition of the partial left adjoint

Given a functor `F : D ⥤ C`, we define a functor
`F.partialLeftAdjoint : F.PartialLeftAdjointSource ⥤ D` which is
defined on the full subcategory of `C` consisting of those objects `X : C`
such that `F ⋙ coyoneda.obj (op X) : D ⥤ Type _` is corepresentable.
For `X : F.PartialLeftAdjointSource` and `Y : D`, we have a natural bijection
`(F.partialLeftAdjoint.obj X ⟶ Y) ≃ (X.obj ⟶ F.obj Y)`
that is similar to what we would expect for the image of the object `X`
by the left adjoint of `F`, if such an adjoint existed.

Indeed, if the predicate `F.leftAdjointObjIsDefined` which defines
the `F.PartialLeftAdjointSource` holds for all
objects `X : C`, then `F` has a left adjoint.

When colimits indexed by a category `J` exist in `D`, we show that
the predicate `F.leftAdjointObjIsDefined` is stable under colimits indexed by `J`.

## TODO
* consider dualizing the results to right adjoints

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

open Category Opposite Limits

section partialLeftAdjoint

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : D ⥤ C)

/-- Given a functor `F : D ⥤ C`, this is a predicate on objects `X : C` corresponding
to the domain of definition of the (partial) left adjoint of `F`. -/
/-
**CategoryTheory.Functor.leftAdjointObjIsDefined** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：leftAdjointObjIsDefined : ObjectProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : D ⥤ C`, this is a predicate on objects `X : C` correspondin
g
to the domain of definition of the (partial) left adjoint of `F`.
-/
def leftAdjointObjIsDefined : ObjectProperty C :=
  fun X ↦ IsCorepresentable (F ⋙ coyoneda.obj (op X))
/-
**CategoryTheory.Functor.leftAdjointObjIsDefined_iff** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Functor`。
形式化陈述：leftAdjointObjIsDefined_iff (X : C) : F.leftAdjointObjIsDefined X ↔ IsCore
presentable (F ⋙ coyoneda.obj (op X))
参数：X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma leftAdjointObjIsDefined_iff (X : C) :
    F.leftAdjointObjIsDefined X ↔ IsCorepresentable (F ⋙ coyoneda.obj (op X)) := by rfl

variable {F} in
/-
**CategoryTheory.Functor.leftAdjointObjIsDefined_of_adjunction** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：leftAdjointObjIsDefined_of_adjunction {G : C ⥤ D} (adj : G ⊣ F) (X : C) : 
F.leftAdjointObjIsDefined X
参数：adj : G ⊣ F；X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.CorepresentableBy.isCorepresentable`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor C (T
ype v)} {X : C}   (e : F.CorepresentableBy X), F…
-/
lemma leftAdjointObjIsDefined_of_adjunction {G : C ⥤ D} (adj : G ⊣ F) (X : C) :
    F.leftAdjointObjIsDefined X :=
  (adj.corepresentableBy X).isCorepresentable

/-- The full subcategory where `F.partialLeftAdjoint` shall be defined. -/
/-
**CategoryTheory.Functor.PartialLeftAdjointSource** 是 Mathlib 中的一个缩写定义，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：PartialLeftAdjointSource
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The full subcategory where `F.partialLeftAdjoint` shall be defined.
-/
abbrev PartialLeftAdjointSource := F.leftAdjointObjIsDefined.FullSubcategory
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : F.PartialLeftAdjointSource) :
    IsCorepresentable (F ⋙ coyoneda.obj (op X.obj)) := X.property

/-- Given `F : D ⥤ C`, this is `F.partialLeftAdjoint` on objects: it sends
`X : C` such that `F.leftAdjointObjIsDefined X` holds to an object of `D`
which represents the functor `F ⋙ coyoneda.obj (op X.obj)`. -/
/-
**CategoryTheory.Functor.partialLeftAdjointObj** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：partialLeftAdjointObj (X : F.PartialLeftAdjointSource) : D
参数：X : F.PartialLeftAdjointSource。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instIsCorepresentableCompObjOppositeTypeCoyonedaO
pObjLeftAdjointObjIsDefined`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁
, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : Cate
goryTheor…

--- 原说明 ---
Given `F : D ⥤ C`, this is `F.partialLeftAdjoint` on objects: it sends
`X : C` such that `F.leftAdjointObjIsDefined X` holds to an object of `D`
which represents the functor `F ⋙ coyoneda.obj (op X.obj)`.
-/
noncomputable def partialLeftAdjointObj (X : F.PartialLeftAdjointSource) : D :=
  (F ⋙ coyoneda.obj (op X.obj)).coreprX

/-- Given `F : D ⥤ C`, this is the canonical bijection
`(F.partialLeftAdjointObj X ⟶ Y) ≃ (X.obj ⟶ F.obj Y)`
for all `X : F.PartialLeftAdjointSource` and `Y : D`. -/
/-
**CategoryTheory.Functor.partialLeftAdjointHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：partialLeftAdjointHomEquiv {X : F.PartialLeftAdjointSource} {Y : D} : (F.p
artialLeftAdjointObj X ⟶ Y) ≃ (X.obj ⟶ F.obj Y)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instIsCorepresentableCompObjOppositeTypeCoyonedaO
pObjLeftAdjointObjIsDefined`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁
, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : Cate
goryTheor…

--- 原说明 ---
Given `F : D ⥤ C`, this is the canonical bijection
`(F.partialLeftAdjointObj X ⟶ Y) ≃ (X.obj ⟶ F.obj Y)`
for all `X : F.PartialLeftAdjointSource` and `Y : D`.
-/
noncomputable def partialLeftAdjointHomEquiv {X : F.PartialLeftAdjointSource} {Y : D} :
    (F.partialLeftAdjointObj X ⟶ Y) ≃ (X.obj ⟶ F.obj Y) :=
  (F ⋙ coyoneda.obj (op X.obj)).corepresentableBy.homEquiv
/-
**CategoryTheory.Functor.partialLeftAdjointHomEquiv_comp** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Functor`。
形式化陈述：partialLeftAdjointHomEquiv_comp {X : F.PartialLeftAdjointSource} {Y Y' : D
} (f : F.partialLeftAdjointObj X ⟶ Y) (g : Y ⟶ Y') : F.partialLeftAdjointHomEqui
v (f ≫ g) = F.partialLeftAdjointHomEquiv f ≫ F.map g
参数：f : F.partialLeftAdjointObj X ⟶ Y；g : Y ⟶ Y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.CorepresentableBy.homEquiv_comp`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor C (Type 
v)} {X : C}   (self : F.CorepresentableBy X)…
· 使用定理 `CategoryTheory.Functor.instIsCorepresentableCompObjOppositeTypeCoyonedaO
pObjLeftAdjointObjIsDefined`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁
, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : Cate
goryTheor…
-/
lemma partialLeftAdjointHomEquiv_comp {X : F.PartialLeftAdjointSource} {Y Y' : D}
    (f : F.partialLeftAdjointObj X ⟶ Y) (g : Y ⟶ Y') :
    F.partialLeftAdjointHomEquiv (f ≫ g) =
      F.partialLeftAdjointHomEquiv f ≫ F.map g := by
  apply CorepresentableBy.homEquiv_comp

/-- Given `F : D ⥤ C`, this is `F.partialLeftAdjoint` on morphisms. -/
/-
**CategoryTheory.Functor.partialLeftAdjointMap** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：partialLeftAdjointMap {X Y : F.PartialLeftAdjointSource} (f : X ⟶ Y) : F.p
artialLeftAdjointObj X ⟶ F.partialLeftAdjointObj Y
参数：f : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given `F : D ⥤ C`, this is `F.partialLeftAdjoint` on morphisms.
-/
noncomputable def partialLeftAdjointMap {X Y : F.PartialLeftAdjointSource}
    (f : X ⟶ Y) : F.partialLeftAdjointObj X ⟶ F.partialLeftAdjointObj Y :=
    F.partialLeftAdjointHomEquiv.symm (f.hom ≫ F.partialLeftAdjointHomEquiv (𝟙 _))

@[simp]
/-
**CategoryTheory.Functor.partialLeftAdjointHomEquiv_map** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Functor`。
形式化陈述：partialLeftAdjointHomEquiv_map {X Y : F.PartialLeftAdjointSource} (f : X ⟶
 Y) : F.partialLeftAdjointHomEquiv (F.partialLeftAdjointMap f) = f.hom ≫ F.parti
alLeftAdjointHomEquiv (𝟙 _)
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma partialLeftAdjointHomEquiv_map {X Y : F.PartialLeftAdjointSource}
    (f : X ⟶ Y) :
    F.partialLeftAdjointHomEquiv (F.partialLeftAdjointMap f) =
      f.hom ≫ F.partialLeftAdjointHomEquiv (𝟙 _) := by
  simp [partialLeftAdjointMap]
/-
**CategoryTheory.Functor.partialLeftAdjointHomEquiv_map_comp** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Functor`。
形式化陈述：partialLeftAdjointHomEquiv_map_comp {X X' : F.PartialLeftAdjointSource} {Y
 : D} (f : X ⟶ X') (g : F.partialLeftAdjointObj X' ⟶ Y) : F.partialLeftAdjointHo
mEquiv (F.partialLeftAdjointMap f ≫ g) = f.hom ≫ F.partialLeftAdjointHomEquiv g
参数：f : X ⟶ X'；g : F.partialLeftAdjointObj X' ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.partialLeftAdjointHomEquiv_comp`：partialLeftAdjoi
ntHomEquiv_comp {X : F.PartialLeftAdjointSource} {Y Y' : D} (f : F.partialLeftAd
jointObj X ⟶ Y) (g : Y ⟶ Y') : F.partialLeft…
· 使用引理 `CategoryTheory.Functor.partialLeftAdjointHomEquiv_map`：partialLeftAdjoin
tHomEquiv_map {X Y : F.PartialLeftAdjointSource} (f : X ⟶ Y) : F.partialLeftAdjo
intHomEquiv (F.partialLeftAdjointMap f) = f…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma partialLeftAdjointHomEquiv_map_comp {X X' : F.PartialLeftAdjointSource} {Y : D}
    (f : X ⟶ X') (g : F.partialLeftAdjointObj X' ⟶ Y) :
    F.partialLeftAdjointHomEquiv (F.partialLeftAdjointMap f ≫ g) =
      f.hom ≫ F.partialLeftAdjointHomEquiv g := by
  rw [partialLeftAdjointHomEquiv_comp, partialLeftAdjointHomEquiv_map, assoc,
    ← partialLeftAdjointHomEquiv_comp, id_comp]

@[reassoc]
/-
**CategoryTheory.Functor.partialLeftAdjointHomEquiv_symm_comp** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：partialLeftAdjointHomEquiv_symm_comp {X : F.PartialLeftAdjointSource} {Y Y
' : D} (f : X.obj ⟶ F.obj Y) (g : Y ⟶ Y') : F.partialLeftAdjointHomEquiv.symm f 
≫ g = F.partialLeftAdjointHomEquiv.symm (f ≫ F.map g)
参数：f : X.obj ⟶ F.obj Y；g : Y ⟶ Y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.CorepresentableBy.homEquiv_symm_comp`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor C (
Type v)} {X : C}   (e : F.CorepresentableBy X) {Y…
· 使用定理 `CategoryTheory.Functor.instIsCorepresentableCompObjOppositeTypeCoyonedaO
pObjLeftAdjointObjIsDefined`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁
, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : Cate
goryTheor…
-/
lemma partialLeftAdjointHomEquiv_symm_comp {X : F.PartialLeftAdjointSource} {Y Y' : D}
    (f : X.obj ⟶ F.obj Y) (g : Y ⟶ Y') :
    F.partialLeftAdjointHomEquiv.symm f ≫ g = F.partialLeftAdjointHomEquiv.symm (f ≫ F.map g) :=
  CorepresentableBy.homEquiv_symm_comp ..

@[reassoc]
/-
**CategoryTheory.Functor.partialLeftAdjointHomEquiv_comp_symm** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：partialLeftAdjointHomEquiv_comp_symm {X X' : F.PartialLeftAdjointSource} {
Y : D} (f : X'.obj ⟶ F.obj Y) (g : X ⟶ X') : F.partialLeftAdjointMap g ≫ F.parti
alLeftAdjointHomEquiv.symm f = F.partialLeftAdjointHomEquiv.symm (g.hom ≫ f)
参数：f : X'.obj ⟶ F.obj Y；g : X ⟶ X'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用引理 `CategoryTheory.Functor.partialLeftAdjointHomEquiv_comp`：partialLeftAdjoi
ntHomEquiv_comp {X : F.PartialLeftAdjointSource} {Y Y' : D} (f : F.partialLeftAd
jointObj X ⟶ Y) (g : Y ⟶ Y') : F.partialLeft…
· 使用引理 `CategoryTheory.Functor.partialLeftAdjointHomEquiv_map`：partialLeftAdjoin
tHomEquiv_map {X Y : F.PartialLeftAdjointSource} (f : X ⟶ Y) : F.partialLeftAdjo
intHomEquiv (F.partialLeftAdjointMap f) = f…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
lemma partialLeftAdjointHomEquiv_comp_symm {X X' : F.PartialLeftAdjointSource} {Y : D}
    (f : X'.obj ⟶ F.obj Y) (g : X ⟶ X') :
    F.partialLeftAdjointMap g ≫ F.partialLeftAdjointHomEquiv.symm f =
    F.partialLeftAdjointHomEquiv.symm (g.hom ≫ f) := by
  rw [Equiv.eq_symm_apply, partialLeftAdjointHomEquiv_comp, partialLeftAdjointHomEquiv_map,
    assoc, ← partialLeftAdjointHomEquiv_comp, id_comp, Equiv.apply_symm_apply]

/-- Given `F : D ⥤ C`, this is the partial adjoint functor `F.PartialLeftAdjointSource ⥤ D`. -/
@[simps]
/-
**CategoryTheory.Functor.partialLeftAdjoint** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：partialLeftAdjoint : F.PartialLeftAdjointSource ⥤ D where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : D ⥤ C`, this is the partial adjoint functor `F.PartialLeftAdjointSour
ce ⥤ D`.
-/
noncomputable def partialLeftAdjoint : F.PartialLeftAdjointSource ⥤ D where
  obj := F.partialLeftAdjointObj
  map := F.partialLeftAdjointMap
  map_id X := by
    apply F.partialLeftAdjointHomEquiv.injective
    simp [partialLeftAdjointHomEquiv_map]
  map_comp {X Y Z} f g := by
    apply F.partialLeftAdjointHomEquiv.injective
    simp [partialLeftAdjointHomEquiv_comp, ← F.partialLeftAdjointHomEquiv_comp]

variable {F}
/-
**CategoryTheory.Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isRightAdjoint_of_leftAdjointObjIsDefined_eq_top (h : F.leftAdjointObjIsDe
fined = ⊤) : F.IsRightAdjoint
参数：h : F.leftAdjointObjIsDefined = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Adjunction.isRightAdjoint`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.CorepresentableBy.homEquiv_comp`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor C (Type 
v)} {X : C}   (self : F.CorepresentableBy X)…
-/
lemma isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (h : F.leftAdjointObjIsDefined = ⊤) : F.IsRightAdjoint := by
  replace h : ∀ X, IsCorepresentable (F ⋙ coyoneda.obj (op X)) := fun X ↦ by
    simp only [← leftAdjointObjIsDefined_iff, h, Pi.top_apply, Prop.top_eq_true]
  exact (Adjunction.adjunctionOfEquivLeft
    (fun X Y ↦ (F ⋙ coyoneda.obj (op X)).corepresentableBy.homEquiv)
    (fun X Y Y' g f ↦ by apply CorepresentableBy.homEquiv_comp)).isRightAdjoint

variable (F) in
/-
**CategoryTheory.Functor.isRightAdjoint_iff_leftAdjointObjIsDefined_eq_top** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isRightAdjoint_iff_leftAdjointObjIsDefined_eq_top : F.IsRightAdjoint ↔ F.l
eftAdjointObjIsDefined = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用引理 `CategoryTheory.Functor.leftAdjointObjIsDefined_of_adjunction`：leftAdjoin
tObjIsDefined_of_adjunction {G : C ⥤ D} (adj : G ⊣ F) (X : C) : F.leftAdjointObj
IsDefined X
· 使用引理 `CategoryTheory.Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top`
：isRightAdjoint_of_leftAdjointObjIsDefined_eq_top (h : F.leftAdjointObjIsDefined
 = ⊤) : F.IsRightAdjoint
-/
lemma isRightAdjoint_iff_leftAdjointObjIsDefined_eq_top :
    F.IsRightAdjoint ↔ F.leftAdjointObjIsDefined = ⊤ := by
  refine ⟨fun h ↦ ?_, isRightAdjoint_of_leftAdjointObjIsDefined_eq_top⟩
  ext X
  simpa only [Pi.top_apply, Prop.top_eq_true, iff_true]
    using leftAdjointObjIsDefined_of_adjunction (Adjunction.ofIsRightAdjoint F) X

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `leftAdjointObjIsDefined_of_isColimit`. -/
/-
**CategoryTheory.Functor.corepresentableByCompCoyonedaObjOfIsColimit** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：corepresentableByCompCoyonedaObjOfIsColimit {J : Type*} [Category* J] {R :
 J ⥤ F.PartialLeftAdjointSource} {c : Cocone (R ⋙ ObjectProperty.ι _)} (hc : IsC
olimit c) {c' : Cocone (R ⋙ F.partialLeftAdjoint)} (hc' : IsColimit c') : (F ⋙ c
oyoneda.obj (op c.pt)).CorepresentableBy c'.pt where homEquiv {Y}
参数：R ⋙ ObjectProperty.ι _；hc : IsColimit c；R ⋙ F.partialLeftAdjoint；hc' : IsColi
mit c'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Auxiliary definition for `leftAdjointObjIsDefined_of_isColimit`.
-/
noncomputable def corepresentableByCompCoyonedaObjOfIsColimit {J : Type*} [Category* J]
    {R : J ⥤ F.PartialLeftAdjointSource}
    {c : Cocone (R ⋙ ObjectProperty.ι _)} (hc : IsColimit c)
    {c' : Cocone (R ⋙ F.partialLeftAdjoint)} (hc' : IsColimit c') :
    (F ⋙ coyoneda.obj (op c.pt)).CorepresentableBy c'.pt where
  homEquiv {Y} :=
    { toFun := fun f ↦ hc.desc (Cocone.mk _
        { app := fun j ↦ F.partialLeftAdjointHomEquiv (c'.ι.app j ≫ f)
          naturality := fun j j' φ ↦ by
            dsimp
            rw [comp_id, ← c'.w φ, ← partialLeftAdjointHomEquiv_map_comp, assoc]
            dsimp })
      invFun := fun g ↦ hc'.desc (Cocone.mk _
        { app := fun j ↦ F.partialLeftAdjointHomEquiv.symm (c.ι.app j ≫ g)
          naturality := fun j j' φ ↦ by
            apply F.partialLeftAdjointHomEquiv.injective
            have := c.w φ
            dsimp at this ⊢
            rw [comp_id, Equiv.apply_symm_apply, partialLeftAdjointHomEquiv_map_comp,
              Equiv.apply_symm_apply, reassoc_of% this] })
      left_inv := fun f ↦ hc'.hom_ext (fun j ↦ by simp)
      right_inv := fun g ↦ hc.hom_ext (fun j ↦ by simp) }
  homEquiv_comp {Y Y'} g f := hc.hom_ext (fun j ↦ by
    dsimp
    simp only [IsColimit.fac, IsColimit.fac_assoc, partialLeftAdjointHomEquiv_comp,
      F.map_comp, assoc])
/-
**CategoryTheory.Functor.leftAdjointObjIsDefined_of_isColimit** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：leftAdjointObjIsDefined_of_isColimit {J : Type*} [Category* J] {R : J ⥤ C}
 {c : Cocone R} (hc : IsColimit c) [HasColimitsOfShape J D] (h : forall (j : J),
 F.leftAdjointObjIsDefined (R.obj j)) : F.leftAdjointObjIsDefined c.pt
参数：hc : IsColimit c；h : forall (j : J), F.leftAdjointObjIsDefined (R.obj j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.CorepresentableBy.isCorepresentable`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor C (T
ype v)} {X : C}   (e : F.CorepresentableBy X), F…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
lemma leftAdjointObjIsDefined_of_isColimit {J : Type*} [Category* J] {R : J ⥤ C} {c : Cocone R}
    (hc : IsColimit c) [HasColimitsOfShape J D]
    (h : ∀ (j : J), F.leftAdjointObjIsDefined (R.obj j)) :
    F.leftAdjointObjIsDefined c.pt :=
  (corepresentableByCompCoyonedaObjOfIsColimit
    (R := ObjectProperty.lift _ R h) hc (colimit.isColimit _)).isCorepresentable
/-
**CategoryTheory.Functor.leftAdjointObjIsDefined_colimit** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Functor`。
形式化陈述：leftAdjointObjIsDefined_colimit {J : Type*} [Category* J] (R : J ⥤ C) [Has
Colimit R] [HasColimitsOfShape J D] (h : forall (j : J), F.leftAdjointObjIsDefin
ed (R.obj j)) : F.leftAdjointObjIsDefined (colimit R)
参数：R : J ⥤ C；h : forall (j : J), F.leftAdjointObjIsDefined (R.obj j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.leftAdjointObjIsDefined_of_isColimit`：leftAdjoint
ObjIsDefined_of_isColimit {J : Type*} [Category* J] {R : J ⥤ C} {c : Cocone R} (
hc : IsColimit c) [HasColimitsOfShape J D] (h : f…
-/
lemma leftAdjointObjIsDefined_colimit {J : Type*} [Category* J] (R : J ⥤ C)
    [HasColimit R] [HasColimitsOfShape J D]
    (h : ∀ (j : J), F.leftAdjointObjIsDefined (R.obj j)) :
    F.leftAdjointObjIsDefined (colimit R) :=
  leftAdjointObjIsDefined_of_isColimit (colimit.isColimit R) h

end partialLeftAdjoint

section partialRightAdjoint

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

/-- Given a functor `F : C ⥤ D`, this is a predicate on objects `X : D` corresponding
to the domain of definition of the (partial) right adjoint of `F`. -/
/-
**CategoryTheory.Functor.rightAdjointObjIsDefined** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：rightAdjointObjIsDefined : ObjectProperty D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : C ⥤ D`, this is a predicate on objects `X : D` correspondin
g
to the domain of definition of the (partial) right adjoint of `F`.
-/
def rightAdjointObjIsDefined : ObjectProperty D :=
  fun Y ↦ IsRepresentable (F.op ⋙ yoneda.obj Y)
/-
**CategoryTheory.Functor.rightAdjointObjIsDefined_iff** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Functor`。
形式化陈述：rightAdjointObjIsDefined_iff (Y : D) : F.rightAdjointObjIsDefined Y ↔ IsRe
presentable (F.op ⋙ yoneda.obj Y)
参数：Y : D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma rightAdjointObjIsDefined_iff (Y : D) :
    F.rightAdjointObjIsDefined Y ↔ IsRepresentable (F.op ⋙ yoneda.obj Y) := by rfl

variable {F} in
/-
**CategoryTheory.Functor.rightAdjointObjIsDefined_of_adjunction** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：rightAdjointObjIsDefined_of_adjunction {G : D ⥤ C} (adj : F ⊣ G) (Y : D) :
 F.rightAdjointObjIsDefined Y
参数：adj : F ⊣ G；Y : D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.RepresentableBy.isRepresentable`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor Cᵒᵖ (Typ
e v)} {Y : C}   (e : F.RepresentableBy Y), F…
-/
lemma rightAdjointObjIsDefined_of_adjunction {G : D ⥤ C} (adj : F ⊣ G) (Y : D) :
    F.rightAdjointObjIsDefined Y :=
  (adj.representableBy Y).isRepresentable

/-- The full subcategory where `F.partialRightAdjoint` shall be defined. -/
/-
**CategoryTheory.Functor.PartialRightAdjointSource** 是 Mathlib 中的一个缩写定义，位于命名空间 `
CategoryTheory.Functor`。
形式化陈述：PartialRightAdjointSource
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The full subcategory where `F.partialRightAdjoint` shall be defined.
-/
abbrev PartialRightAdjointSource := F.rightAdjointObjIsDefined.FullSubcategory
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (Y : F.PartialRightAdjointSource) :
    IsRepresentable (F.op ⋙ yoneda.obj Y.obj) := Y.property

/-- Given `F : C ⥤ D`, this is `F.partialRightAdjoint` on objects: it sends
`X : D` such that `F.rightAdjointObjIsDefined X` holds to an object of `C`
which represents the functor `F.op ⋙ yoneda.obj X.obj`. -/
/-
**CategoryTheory.Functor.partialRightAdjointObj** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Functor`。
形式化陈述：partialRightAdjointObj (Y : F.PartialRightAdjointSource) : C
参数：Y : F.PartialRightAdjointSource。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instIsRepresentableCompOppositeOpObjTypeYonedaObj
RightAdjointObjIsDefined`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u
₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : Categor
yTheor…

--- 原说明 ---
Given `F : C ⥤ D`, this is `F.partialRightAdjoint` on objects: it sends
`X : D` such that `F.rightAdjointObjIsDefined X` holds to an object of `C`
which represents the functor `F.op ⋙ yoneda.obj X.obj`.
-/
noncomputable def partialRightAdjointObj (Y : F.PartialRightAdjointSource) : C :=
  (F.op ⋙ yoneda.obj Y.obj).reprX

/-- Given `F : C ⥤ D`, this is the canonical bijection
`(X ⟶ F.partialRightAdjointObj Y) ≃ (F.obj X ⟶ Y.obj)`
for all `X : C` and `Y : F.PartialRightAdjointSource`. -/
/-
**CategoryTheory.Functor.partialRightAdjointHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Functor`。
形式化陈述：partialRightAdjointHomEquiv {X : C} {Y : F.PartialRightAdjointSource} : (X
 ⟶ F.partialRightAdjointObj Y) ≃ (F.obj X ⟶ Y.obj)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instIsRepresentableCompOppositeOpObjTypeYonedaObj
RightAdjointObjIsDefined`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u
₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : Categor
yTheor…

--- 原说明 ---
Given `F : C ⥤ D`, this is the canonical bijection
`(X ⟶ F.partialRightAdjointObj Y) ≃ (F.obj X ⟶ Y.obj)`
for all `X : C` and `Y : F.PartialRightAdjointSource`.
-/
noncomputable def partialRightAdjointHomEquiv {X : C} {Y : F.PartialRightAdjointSource} :
    (X ⟶ F.partialRightAdjointObj Y) ≃ (F.obj X ⟶ Y.obj) :=
  (F.op ⋙ yoneda.obj Y.obj).representableBy.homEquiv
/-
**CategoryTheory.Functor.partialRightAdjointHomEquiv_comp** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Functor`。
形式化陈述：partialRightAdjointHomEquiv_comp {X X' : C} {Y : F.PartialRightAdjointSour
ce} (f : X' ⟶ F.partialRightAdjointObj Y) (g : X ⟶ X') : F.partialRightAdjointHo
mEquiv (g ≫ f) = F.map g ≫ F.partialRightAdjointHomEquiv f
参数：f : X' ⟶ F.partialRightAdjointObj Y；g : X ⟶ X'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.RepresentableBy.homEquiv_comp`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor Cᵒᵖ (Type 
v)} {Y : C}   (self : F.RepresentableBy Y)…
· 使用定理 `CategoryTheory.Functor.instIsRepresentableCompOppositeOpObjTypeYonedaObj
RightAdjointObjIsDefined`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u
₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : Categor
yTheor…
-/
lemma partialRightAdjointHomEquiv_comp {X X' : C} {Y : F.PartialRightAdjointSource}
    (f : X' ⟶ F.partialRightAdjointObj Y) (g : X ⟶ X') :
    F.partialRightAdjointHomEquiv (g ≫ f) =
      F.map g ≫ F.partialRightAdjointHomEquiv f :=
  RepresentableBy.homEquiv_comp ..

/-- Given `F : C ⥤ D`, this is `F.partialRightAdjoint` on morphisms. -/
/-
**CategoryTheory.Functor.partialRightAdjointMap** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Functor`。
形式化陈述：partialRightAdjointMap {X Y : F.PartialRightAdjointSource} (f : X ⟶ Y) : F
.partialRightAdjointObj X ⟶ F.partialRightAdjointObj Y
参数：f : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given `F : C ⥤ D`, this is `F.partialRightAdjoint` on morphisms.
-/
noncomputable def partialRightAdjointMap {X Y : F.PartialRightAdjointSource}
    (f : X ⟶ Y) : F.partialRightAdjointObj X ⟶ F.partialRightAdjointObj Y :=
    F.partialRightAdjointHomEquiv.symm (F.partialRightAdjointHomEquiv (𝟙 _) ≫ f.hom)

@[simp]
/-
**CategoryTheory.Functor.partialRightAdjointHomEquiv_map** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Functor`。
形式化陈述：partialRightAdjointHomEquiv_map {X Y : F.PartialRightAdjointSource} (f : X
 ⟶ Y) : F.partialRightAdjointHomEquiv (F.partialRightAdjointMap f) = F.partialRi
ghtAdjointHomEquiv (𝟙 _) ≫ f.hom
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma partialRightAdjointHomEquiv_map {X Y : F.PartialRightAdjointSource}
    (f : X ⟶ Y) :
    F.partialRightAdjointHomEquiv (F.partialRightAdjointMap f) =
      F.partialRightAdjointHomEquiv (𝟙 _) ≫ f.hom := by
  simp [partialRightAdjointMap]
/-
**CategoryTheory.Functor.partialRightAdjointHomEquiv_map_comp** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：partialRightAdjointHomEquiv_map_comp {X : C} {Y Y' : F.PartialRightAdjoint
Source} (f : X ⟶ F.partialRightAdjointObj Y) (g : Y ⟶ Y') : F.partialRightAdjoin
tHomEquiv (f ≫ F.partialRightAdjointMap g) = F.partialRightAdjointHomEquiv f ≫ g
.hom
参数：f : X ⟶ F.partialRightAdjointObj Y；g : Y ⟶ Y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.partialRightAdjointHomEquiv_comp`：partialRightAdj
ointHomEquiv_comp {X X' : C} {Y : F.PartialRightAdjointSource} (f : X' ⟶ F.parti
alRightAdjointObj Y) (g : X ⟶ X') : F.partial…
· 使用引理 `CategoryTheory.Functor.partialRightAdjointHomEquiv_map`：partialRightAdjo
intHomEquiv_map {X Y : F.PartialRightAdjointSource} (f : X ⟶ Y) : F.partialRight
AdjointHomEquiv (F.partialRightAdjointMap f)…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma partialRightAdjointHomEquiv_map_comp {X : C} {Y Y' : F.PartialRightAdjointSource}
    (f : X ⟶ F.partialRightAdjointObj Y) (g : Y ⟶ Y') :
    F.partialRightAdjointHomEquiv (f ≫ F.partialRightAdjointMap g) =
      F.partialRightAdjointHomEquiv f ≫ g.hom := by
  rw [partialRightAdjointHomEquiv_comp, partialRightAdjointHomEquiv_map,
    ← assoc, ← partialRightAdjointHomEquiv_comp, comp_id]

@[reassoc]
/-
**CategoryTheory.Functor.partialRightAdjointHomEquiv_comp_symm** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：partialRightAdjointHomEquiv_comp_symm {X X' : C} {Y : F.PartialRightAdjoin
tSource} (f : F.obj X' ⟶ Y.obj) (g : X ⟶ X') : g ≫ F.partialRightAdjointHomEquiv
.symm f = F.partialRightAdjointHomEquiv.symm (F.map g ≫ f)
参数：f : F.obj X' ⟶ Y.obj；g : X ⟶ X'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.RepresentableBy.comp_homEquiv_symm`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor Cᵒᵖ (
Type v)} {Y : C}   (e : F.RepresentableBy Y) {X…
· 使用定理 `CategoryTheory.Functor.instIsRepresentableCompOppositeOpObjTypeYonedaObj
RightAdjointObjIsDefined`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u
₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : Categor
yTheor…
-/
lemma partialRightAdjointHomEquiv_comp_symm {X X' : C} {Y : F.PartialRightAdjointSource}
    (f : F.obj X' ⟶ Y.obj) (g : X ⟶ X') :
    g ≫ F.partialRightAdjointHomEquiv.symm f =
      F.partialRightAdjointHomEquiv.symm (F.map g ≫ f) :=
  RepresentableBy.comp_homEquiv_symm ..

@[reassoc]
/-
**CategoryTheory.Functor.partialRightAdjointHomEquiv_symm_comp** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：partialRightAdjointHomEquiv_symm_comp {X : C} {Y Y' : F.PartialRightAdjoin
tSource} (f : F.obj X ⟶ Y.obj) (g : Y ⟶ Y') : F.partialRightAdjointHomEquiv.symm
 f ≫ F.partialRightAdjointMap g = F.partialRightAdjointHomEquiv.symm (f ≫ g.hom)
参数：f : F.obj X ⟶ Y.obj；g : Y ⟶ Y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.partialRightAdjointHomEquiv_map_comp`：partialRigh
tAdjointHomEquiv_map_comp {X : C} {Y Y' : F.PartialRightAdjointSource} (f : X ⟶ 
F.partialRightAdjointObj Y) (g : Y ⟶ Y') : F.part…
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma partialRightAdjointHomEquiv_symm_comp {X : C} {Y Y' : F.PartialRightAdjointSource}
    (f : F.obj X ⟶ Y.obj) (g : Y ⟶ Y') :
    F.partialRightAdjointHomEquiv.symm f ≫ F.partialRightAdjointMap g =
      F.partialRightAdjointHomEquiv.symm (f ≫ g.hom) := by
  simp [Equiv.eq_symm_apply, partialRightAdjointHomEquiv_map_comp]

/-- Given `F : C ⥤ D`, this is the partial adjoint functor `F.PartialRightAdjointSource ⥤ C`. -/
@[simps]
/-
**CategoryTheory.Functor.partialRightAdjoint** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Functor`。
形式化陈述：partialRightAdjoint : F.PartialRightAdjointSource ⥤ C where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : C ⥤ D`, this is the partial adjoint functor `F.PartialRightAdjointSou
rce ⥤ C`.
-/
noncomputable def partialRightAdjoint : F.PartialRightAdjointSource ⥤ C where
  obj := F.partialRightAdjointObj
  map := F.partialRightAdjointMap
  map_id X := by
    apply F.partialRightAdjointHomEquiv.injective
    simp [partialRightAdjointHomEquiv_map]
  map_comp {X Y Z} f g := by
    apply F.partialRightAdjointHomEquiv.injective
    simp [partialRightAdjointHomEquiv_comp, ← assoc, ← F.partialRightAdjointHomEquiv_comp]

variable {F}
/-
**CategoryTheory.Functor.isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top (h : F.rightAdjointObjIsD
efined = ⊤) : F.IsLeftAdjoint
参数：h : F.rightAdjointObjIsDefined = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.Adjunction.isLeftAdjoint`：isLeftAdjoint (adj : F ⊣ G) : F
.IsLeftAdjoint
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.RepresentableBy.comp_homEquiv_symm`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor Cᵒᵖ (
Type v)} {Y : C}   (e : F.RepresentableBy Y) {X…
-/
lemma isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top
    (h : F.rightAdjointObjIsDefined = ⊤) : F.IsLeftAdjoint := by
  replace h : ∀ X, IsRepresentable (F.op ⋙ yoneda.obj X) := fun X ↦ by
    simp only [← rightAdjointObjIsDefined_iff, h, Pi.top_apply, Prop.top_eq_true]
  exact (Adjunction.adjunctionOfEquivRight
    (fun X Y ↦ (F.op ⋙ yoneda.obj Y).representableBy.homEquiv.symm)
    (fun X Y Y' g f ↦ (RepresentableBy.comp_homEquiv_symm ..).symm)).isLeftAdjoint

variable (F) in
/-
**CategoryTheory.Functor.isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top : F.IsLeftAdjoint ↔ F.ri
ghtAdjointObjIsDefined = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用引理 `CategoryTheory.Functor.rightAdjointObjIsDefined_of_adjunction`：rightAdjo
intObjIsDefined_of_adjunction {G : D ⥤ C} (adj : F ⊣ G) (Y : D) : F.rightAdjoint
ObjIsDefined Y
· 使用引理 `CategoryTheory.Functor.isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top`
：isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top (h : F.rightAdjointObjIsDefine
d = ⊤) : F.IsLeftAdjoint
-/
lemma isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top :
    F.IsLeftAdjoint ↔ F.rightAdjointObjIsDefined = ⊤ := by
  refine ⟨fun h ↦ ?_, isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top⟩
  ext X
  simpa only [Pi.top_apply, Prop.top_eq_true, iff_true]
    using rightAdjointObjIsDefined_of_adjunction (Adjunction.ofIsLeftAdjoint F) X

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `rightAdjointObjIsDefined_of_isLimit`. -/
/-
**CategoryTheory.Functor.representableByCompYonedaObjOfIsLimit** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：representableByCompYonedaObjOfIsLimit {J : Type*} [Category* J] {R : J ⥤ F
.PartialRightAdjointSource} {c : Cone (R ⋙ ObjectProperty.ι _)} (hc : IsLimit c)
 {c' : Cone (R ⋙ F.partialRightAdjoint)} (hc' : IsLimit c') : (F.op ⋙ yoneda.obj
 c.pt).RepresentableBy c'.pt where homEquiv {Y}
参数：R ⋙ ObjectProperty.ι _；hc : IsLimit c；R ⋙ F.partialRightAdjoint；hc' : IsLimit
 c'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Auxiliary definition for `rightAdjointObjIsDefined_of_isLimit`.
-/
noncomputable def representableByCompYonedaObjOfIsLimit {J : Type*} [Category* J]
    {R : J ⥤ F.PartialRightAdjointSource}
    {c : Cone (R ⋙ ObjectProperty.ι _)} (hc : IsLimit c)
    {c' : Cone (R ⋙ F.partialRightAdjoint)} (hc' : IsLimit c') :
    (F.op ⋙ yoneda.obj c.pt).RepresentableBy c'.pt where
  homEquiv {Y} :=
    { toFun := fun f ↦ hc.lift (Cone.mk _
        { app := fun j ↦ F.partialRightAdjointHomEquiv (f ≫ c'.π.app j)
          naturality := fun j j' φ ↦ by
            dsimp
            rw [id_comp, ← c'.w φ, ← partialRightAdjointHomEquiv_map_comp,
              ← assoc]
            dsimp })
      invFun := fun g ↦ hc'.lift (Cone.mk _
        { app := fun j ↦ F.partialRightAdjointHomEquiv.symm (g ≫ c.π.app j)
          naturality := fun j j' φ ↦ by
            apply F.partialRightAdjointHomEquiv.injective
            have := c.w φ
            dsimp at this ⊢
            rw [id_comp, Equiv.apply_symm_apply, partialRightAdjointHomEquiv_map_comp,
              Equiv.apply_symm_apply, assoc, this] })
      left_inv := fun f ↦ hc'.hom_ext (fun j ↦ by simp)
      right_inv := fun g ↦ hc.hom_ext (fun j ↦ by simp) }
  homEquiv_comp {Y Y'} g f := hc.hom_ext (fun j ↦ by
    dsimp
    simp only [IsLimit.fac, partialRightAdjointHomEquiv_comp, assoc])
/-
**CategoryTheory.Functor.rightAdjointObjIsDefined_of_isLimit** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Functor`。
形式化陈述：rightAdjointObjIsDefined_of_isLimit {J : Type*} [Category* J] {R : J ⥤ D} 
{c : Cone R} (hc : IsLimit c) [HasLimitsOfShape J C] (h : forall (j : J), F.righ
tAdjointObjIsDefined (R.obj j)) : F.rightAdjointObjIsDefined c.pt
参数：hc : IsLimit c；h : forall (j : J), F.rightAdjointObjIsDefined (R.obj j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.RepresentableBy.isRepresentable`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor Cᵒᵖ (Typ
e v)} {Y : C}   (e : F.RepresentableBy Y), F…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
lemma rightAdjointObjIsDefined_of_isLimit {J : Type*} [Category* J] {R : J ⥤ D} {c : Cone R}
    (hc : IsLimit c) [HasLimitsOfShape J C]
    (h : ∀ (j : J), F.rightAdjointObjIsDefined (R.obj j)) :
    F.rightAdjointObjIsDefined c.pt :=
  (representableByCompYonedaObjOfIsLimit
    (R := ObjectProperty.lift _ R h) hc (limit.isLimit _)).isRepresentable
/-
**CategoryTheory.Functor.rightAdjointObjIsDefined_limit** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Functor`。
形式化陈述：rightAdjointObjIsDefined_limit {J : Type*} [Category* J] (R : J ⥤ D) [HasL
imit R] [HasLimitsOfShape J C] (h : forall (j : J), F.rightAdjointObjIsDefined (
R.obj j)) : F.rightAdjointObjIsDefined (limit R)
参数：R : J ⥤ D；h : forall (j : J), F.rightAdjointObjIsDefined (R.obj j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.rightAdjointObjIsDefined_of_isLimit`：rightAdjoint
ObjIsDefined_of_isLimit {J : Type*} [Category* J] {R : J ⥤ D} {c : Cone R} (hc :
 IsLimit c) [HasLimitsOfShape J C] (h : forall (…
-/
lemma rightAdjointObjIsDefined_limit {J : Type*} [Category* J] (R : J ⥤ D)
    [HasLimit R] [HasLimitsOfShape J C]
    (h : ∀ (j : J), F.rightAdjointObjIsDefined (R.obj j)) :
    F.rightAdjointObjIsDefined (limit R) :=
  rightAdjointObjIsDefined_of_isLimit (limit.isLimit R) h

end partialRightAdjoint

end Functor

end CategoryTheory

