/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Preservation of injective objects

We define a typeclass `Functor.PreservesInjectiveObjects`.

We restate the existing result that if `F ⊣ G` is an adjunction and `F` preserves monomorphisms,
then `G` preserves injective objects. We show that the converse is true if the codomain of `F` has
enough injectives.
-/

public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

/-- A functor preserves injective objects if it maps injective objects to injective objects. -/
/-
**CategoryTheory.Functor.PreservesInjectiveObjects** 是 Mathlib 中的一个归纳类型，位于命名空间 `
CategoryTheory.Functor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} → [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.Functor
 C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor preserves injective objects if it maps injective objects to injective 
objects.
-/
class Functor.PreservesInjectiveObjects (F : C ⥤ D) : Prop where
  injective_obj {X : C} : Injective X → Injective (F.obj X)

/-- See `Functor.injective_obj_of_injective` for a variant taking `Injective X` as an explicit
argument. -/
/-
**CategoryTheory.Functor.injective_obj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [F.PreservesInjectiveObjects] (X : C) [CategoryTheory.Injective X],   CategoryT
heory.Injective (F.obj X)
参数：F : CategoryTheory.Functor C D；X : C；F.obj X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.PreservesInjectiveObjects.injective_obj`：∀ {C : T
ype u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cate
goryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
See `Functor.injective_obj_of_injective` for a variant taking `Injective X` as a
n explicit
argument.
-/
instance Functor.injective_obj (F : C ⥤ D) [F.PreservesInjectiveObjects] (X : C) [Injective X] :
    Injective (F.obj X) :=
  Functor.PreservesInjectiveObjects.injective_obj inferInstance

/-- See `Functor.injective_obj` for a variant taking `Injective X` as a typeclass argument. -/
/-
**CategoryTheory.Functor.injective_obj_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [F.PreservesInjectiveObjects] {X : C},   CategoryTheory.Injective X → CategoryT
heory.Injective (F.obj X)
参数：F : CategoryTheory.Functor C D；F.obj X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.PreservesInjectiveObjects.injective_obj`：∀ {C : T
ype u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cate
goryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
See `Functor.injective_obj` for a variant taking `Injective X` as a typeclass ar
gument.
-/
theorem Functor.injective_obj_of_injective (F : C ⥤ D) [F.PreservesInjectiveObjects] {X : C}
    (h : Injective X) : Injective (F.obj X) :=
  Functor.PreservesInjectiveObjects.injective_obj h
/-
**CategoryTheory.Functor.preservesInjectiveObjects_comp** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} E] (F : CategoryTheory.Functor C D)   (G : CategoryTheo
ry.Functor D E) [F.PreservesInjectiveObjects] [G.PreservesInjectiveObjects],   (
F.comp G).PreservesInjectiveObjects
参数：F : CategoryTheory.Functor C D；G : CategoryTheory.Functor D E；F.comp G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.injective_obj_of_injective`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   (F : CategoryTheor…
-/
instance Functor.preservesInjectiveObjects_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.PreservesInjectiveObjects] [G.PreservesInjectiveObjects] :
    (F ⋙ G).PreservesInjectiveObjects where
  injective_obj := G.injective_obj_of_injective ∘ F.injective_obj_of_injective
/-
**CategoryTheory.Functor.preservesInjectiveObjects_of_adjunction_of_preservesMon
omorphisms** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor C D}
 {G : CategoryTheory.Functor D C} (adj : F ⊣ G) [F.PreservesMonomorphisms],   G.
PreservesInjectiveObjects
参数：adj : F ⊣ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.map_injective`：map_injective (adj : F ⊣ G) [F.
PreservesMonomorphisms] (I : D) (hI : Injective I) : Injective (G.obj I)
-/
theorem Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.PreservesMonomorphisms] :
    G.PreservesInjectiveObjects where
  injective_obj h := adj.map_injective _ h
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) Functor.preservesInjectiveObjects_of_isEquivalence {F : C ⥤ D}
    [IsEquivalence F] : F.PreservesInjectiveObjects :=
  preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    F.asEquivalence.symm.toAdjunction
/-
**CategoryTheory.Functor.preservesMonomorphisms_of_adjunction_of_preservesInject
iveObjects** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.EnoughInjectives
 D] {F : CategoryTheory.Functor C D} {G : CategoryTheory.Functor D C} (adj : F ⊣
 G)   [G.PreservesInjectiveObjects], F.PreservesMonomorphisms
参数：adj : F ⊣ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.injective_obj`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u
₂} D]   (F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Injective.comp_factorThru`：comp_factorThru {J X Y : C} [I
njective J] (g : X ⟶ J) (f : X ⟶ Y) [Mono f] : f ≫ factorThru g f = g
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Adjunction.counit_naturality`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components_assoc`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.mono_of_mono_fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y Z : C} {f : Y ⟶ X} {g : Z ⟶ Y} {h : Z ⟶ X}   [CategoryThe
ory.Mono h], Category…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem Functor.preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects
    [EnoughInjectives D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [G.PreservesInjectiveObjects] :
    F.PreservesMonomorphisms where
  preserves {X Y} f _ := by
    suffices ∃ h, F.map f ≫ h = Injective.ι (F.obj X) from mono_of_mono_fac this.choose_spec
    exact ⟨F.map (Injective.factorThru (adj.unit.app X ≫ G.map (Injective.ι _)) f) ≫
      adj.counit.app (Injective.under (F.obj X)), by simp [← Functor.map_comp_assoc]⟩

end CategoryTheory

