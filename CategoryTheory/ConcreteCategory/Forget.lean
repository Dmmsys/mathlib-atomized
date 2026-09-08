/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johannes Hölzl, Reid Barton, Sean Leather, Yury Kudryashov, Anne Baanen,
  Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Types.Basic
/-!
# Forgetful functors

A concrete category is a category `C` where the objects and morphisms correspond with types and
(bundled) functions between these types, see the file
`Mathlib.CategoryTheory.ConcreteCategory.Basic`

Each concrete category `C` comes with a canonical faithful functor `forget C : C ⥤ Type*`.
We impose no restrictions on the category `C`, so `Type` has the identity forgetful functor.

We say that a concrete category `C` admits a *forgetful functor* to a concrete category `D`, if it
has a functor `forget₂ C D : C ⥤ D` such that `(forget₂ C D) ⋙ (forget D) = forget C`, see
`class HasForget₂`.  Due to `Faithful.div_comp`, it suffices to verify that `forget₂.obj` and
`forget₂.map` agree with the equality above; then `forget₂` will satisfy the functor laws
automatically, see `HasForget₂.mk'`.

We say that a concrete category `C` admits a *forgetful functor* to a concrete category `D`, if it
has a functor `forget₂ C D : C ⥤ D` such that `(forget₂ C D) ⋙ (forget D) = forget C`, see
`class HasForget₂`.  Due to `Faithful.div_comp`, it suffices to verify that `forget₂.obj` and
`forget₂.map` agree with the equality above; then `forget₂` will satisfy the functor laws
automatically, see `HasForget₂.mk'`.

## References

See [Ahrens and Lumsdaine, *Displayed Categories*][ahrens2017] for
related work.
-/

@[expose] public section

namespace CategoryTheory

universe w u

variable (C : Type*) [Category* C] {FC : outParam <| C → C → Type*} {CC : outParam <| C → Type w}
    [outParam <| ∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} C FC]

/-- The forgetful functor from a concrete category to the category of types. -/
/-
**CategoryTheory.forget** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：forget : C ⥤ Type w where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from a concrete category to the category of types.
-/
abbrev forget : C ⥤ Type w where
  obj X := ToType X
  map f := ↾f
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget C).Faithful where
  map_injective h := ConcreteCategory.hom_ext _ _ fun x ↦ ConcreteCategory.congr_hom h x

variable {C}

@[simp]
/-
**CategoryTheory.ConcreteCategory.forget_map_eq_ofHom** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.ConcreteCategory`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {FC : outPa
ram (C → C → Type u_2)}   {CC : outParam (C → Type w)} [inst_1 : outParam ((X Y 
: C) → FunLike (FC X Y) (CC X) (CC Y))]   [inst_2 : CategoryTheory.ConcreteCateg
ory C FC] {X Y : C} (f : X ⟶ Y),   (CategoryTheory.forget C).map f = TypeCat.ofH
om ⇑(CategoryTheory.ConcreteCategory.hom f)
参数：C → C → Type u_2；C → Type w；(X Y : C) → FunLike (FC X Y) (CC X) (CC Y)；f : X 
⟶ Y；CategoryTheory.forget C；CategoryTheory.ConcreteCategory.hom f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ConcreteCategory.forget_map_eq_ofHom {X Y : C} (f : X ⟶ Y) :
    (forget C).map f = ↾f :=
  rfl

@[deprecated (since := "2026-04-11")] alias ConcreteCategory.forget_map_eq_coe :=
  ConcreteCategory.forget_map_eq_ofHom
/-
**CategoryTheory.forget_obj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：forget_obj (X : C) : (forget C).obj X = ToType X
参数：X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget_obj (X : C) : (forget C).obj X = ToType X := rfl

/-- Analogue of `congr_fun h x`,
when `h : f = g` is an equality between morphisms in a concrete category.
-/
/-
**CategoryTheory.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {FC : outPa
ram (C → C → Type u_2)}   {CC : outParam (C → Type w)} [inst_1 : outParam ((X Y 
: C) → FunLike (FC X Y) (CC X) (CC Y))]   [inst_2 : CategoryTheory.ConcreteCateg
ory C FC] {X Y : C} {f g : X ⟶ Y},   f = g →     ∀ (x : CategoryTheory.ToType X)
,       (CategoryTheory.ConcreteCategory.hom f) x = (CategoryTheory.ConcreteCate
gory.hom g) x
参数：C → C → Type u_2；C → Type w；(X Y : C) → FunLike (FC X Y) (CC X) (CC Y)；x : Ca
tegoryTheory.ToType X；CategoryTheory.ConcreteCategory.hom f；CategoryTheory.Concr
eteCategory.hom g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
Analogue of `congr_fun h x`,
when `h : f = g` is an equality between morphisms in a concrete category.
-/
protected theorem congr_fun {X Y : C} {f g : X ⟶ Y} (h : f = g) (x : ToType X) : f x = g x :=
  congrFun (congrArg (fun k : X ⟶ Y => (k : ToType X → ToType Y)) h) x

/-- Analogue of `congr_arg f h`,
when `h : x = x'` is an equality between elements of objects in a concrete category.
-/
/-
**CategoryTheory.congr_arg** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {FC : outPa
ram (C → C → Type u_2)}   {CC : outParam (C → Type w)} [inst_1 : outParam ((X Y 
: C) → FunLike (FC X Y) (CC X) (CC Y))]   [inst_2 : CategoryTheory.ConcreteCateg
ory C FC] {X Y : C} (f : X ⟶ Y) {x x' : CategoryTheory.ToType X},   x = x' → (Ca
tegoryTheory.ConcreteCategory.hom f) x = (CategoryTheory.ConcreteCategory.hom f)
 x'
参数：C → C → Type u_2；C → Type w；(X Y : C) → FunLike (FC X Y) (CC X) (CC Y)；f : X 
⟶ Y；CategoryTheory.ConcreteCategory.hom f；CategoryTheory.ConcreteCategory.hom f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
Analogue of `congr_arg f h`,
when `h : x = x'` is an equality between elements of objects in a concrete categ
ory.
-/
protected theorem congr_arg {X Y : C} (f : X ⟶ Y) {x x' : ToType X} (h : x = x') : f x = f x' :=
  congrArg (f : ToType X → ToType Y) h

variable (C)

variable (D : Type*) [Category* D] {FD : outParam <| D → D → Type*}
    {CD : outParam <| D → Type w}
    [outParam <| ∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{w} D FD]

/-- `HasForget₂ C D`, where `C` and `D` are both concrete categories, provides a functor
`forget₂ C D : C ⥤ D` and a proof that `forget₂ ⋙ (forget D) = forget C`.
-/
/-
**CategoryTheory.HasForget** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HasForget₂ C D`, where `C` and `D` are both concrete categories, provides a fun
ctor
`forget₂ C D : C ⥤ D` and a proof that `forget₂ ⋙ (forget D) = forget C`.
-/
class HasForget₂ where
  /-- A functor from `C` to `D` -/
  forget₂ : C ⥤ D
  /-- It covers the `forget` for `C` and `D` -/
  forget_comp : forget₂ ⋙ forget D = forget C := by aesop

/-- The forgetful functor `C ⥤ D` between concrete categories for which we have an instance
`HasForget₂ C`. -/
/-
**CategoryTheory.forget** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：forget : C ⥤ Type w where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor `C ⥤ D` between concrete categories for which we have an i
nstance
`HasForget₂ C`.
-/
abbrev forget₂ [HasForget₂ C D] : C ⥤ D :=
  HasForget₂.forget₂

variable {C D}
/-
**CategoryTheory.forget** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：forget : C ⥤ Type w where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget₂_comp_apply [HasForget₂ C D] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : ToType <| (forget₂ C D).obj X) :
    ((forget₂ C D).map (f ≫ g) x) = (forget₂ C D).map g ((forget₂ C D).map f x) := by
  rw [Functor.map_comp, CategoryTheory.comp_apply]
/-
**CategoryTheory.forget** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：forget : C ⥤ Type w where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forget₂_faithful [HasForget₂ C D] : (forget₂ C D).Faithful :=
  HasForget₂.forget_comp.faithful_of_comp

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.InducedCategory.hasForget** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance InducedCategory.hasForget₂ (f : C → D) : HasForget₂ (InducedCategory D f) D where
  forget₂ := inducedFunctor f
  forget_comp := rfl
/-
**CategoryTheory.ObjectProperty.FullSubcategory.hasForget** 是 Mathlib 中的一个实例，位于命
名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ObjectProperty.FullSubcategory.hasForget₂ (P : ObjectProperty C) :
    HasForget₂ P.FullSubcategory C where
  forget₂ := P.ι
  forget_comp := rfl

@[deprecated (since := "2026-04-18")] alias FullSubcategory.hasForget₂ :=
  ObjectProperty.FullSubcategory.hasForget₂

/-- In order to construct a “partially forgetting” functor, we do not need to verify functor laws;
it suffices to ensure that compositions agree with `forget₂ C D ⋙ forget D = forget C`.
-/
@[instance_reducible]
/-
**CategoryTheory.HasForget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In order to construct a “partially forgetting” functor, we do not need to verify
 functor laws;
it suffices to ensure that compositions agree with `forget₂ C D ⋙ forget D = for
get C`.
-/
def HasForget₂.mk' (obj : C → D) (h_obj : ∀ X, (forget D).obj (obj X) = (forget C).obj X)
    (map : ∀ {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y))
    (h_map : ∀ {X Y} {f : X ⟶ Y}, (forget D).map (map f) ≍ (forget C).map f) :
    HasForget₂ C D where
  forget₂ := Functor.Faithful.div _ _ _ @h_obj _ @h_map
  forget_comp := by apply Functor.Faithful.div_comp


variable (C D) in
/-- Composition of `HasForget₂` instances. -/
@[reducible]
/-
**CategoryTheory.HasForget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of `HasForget₂` instances.
-/
def HasForget₂.trans (E : Type*) [Category* E] {FE : outParam <| E → E → Type*}
    {CE : outParam <| E → Type w}
    [outParam <| ∀ X Y, FunLike (FE X Y) (CE X) (CE Y)] [ConcreteCategory.{w} E FE]
    [HasForget₂ C D] [HasForget₂ D E] : HasForget₂ C E where
  forget₂ := CategoryTheory.forget₂ C D ⋙ CategoryTheory.forget₂ D E
  forget_comp := by
    change (CategoryTheory.forget₂ _ D) ⋙ (CategoryTheory.forget₂ D E ⋙ CategoryTheory.forget E) = _
    simp only [HasForget₂.forget_comp]
/-
**CategoryTheory.ConcreteCategory.forget** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ConcreteCategory.forget₂_comp_apply [HasForget₂ C D] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : ToType ((forget₂ C D).obj X)) :
    ((forget₂ C D).map (f ≫ g) x) =
      (forget₂ C D).map g ((forget₂ C D).map f x) := by
  rw [Functor.map_comp, CategoryTheory.comp_apply]
/-
**CategoryTheory.hom_isIso** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：hom_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : IsIso (C
参数：f : X ⟶ Y。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance hom_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] :
    IsIso (C := Type _) (↾(ConcreteCategory.hom f)) :=
  ((forget C).mapIso (asIso f)).isIso_hom

end CategoryTheory

