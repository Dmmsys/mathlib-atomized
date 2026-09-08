/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Preservation of projective objects

We define a typeclass `Functor.PreservesProjectiveObjects`.

We restate the existing result that if `F ⊣ G` is an adjunction and `G` preserves epimorphisms,
then `F` preserves projective objects. We show that the converse is true if the domain of `F` has
enough projectives.
-/

public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

/-- A functor preserves projective objects if it maps projective objects to projective objects. -/
/-
**CategoryTheory.Functor.PreservesProjectiveObjects** 是 Mathlib 中的一个归纳类型，位于命名空间 
`CategoryTheory.Functor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} → [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.Functor
 C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor preserves projective objects if it maps projective objects to projecti
ve objects.
-/
class Functor.PreservesProjectiveObjects (F : C ⥤ D) : Prop where
  projective_obj {X : C} : Projective X → Projective (F.obj X)

/-- See `Functor.projective_obj_of_projective` for a variant taking `Projective X` as an explicit
argument. -/
/-
**CategoryTheory.Functor.projective_obj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [F.PreservesProjectiveObjects] (X : C) [CategoryTheory.Projective X],   Categor
yTheory.Projective (F.obj X)
参数：F : CategoryTheory.Functor C D；X : C；F.obj X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.PreservesProjectiveObjects.projective_obj`：∀ {C :
 Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
See `Functor.projective_obj_of_projective` for a variant taking `Projective X` a
s an explicit
argument.
-/
instance Functor.projective_obj (F : C ⥤ D) [F.PreservesProjectiveObjects] (X : C) [Projective X] :
    Projective (F.obj X) :=
  Functor.PreservesProjectiveObjects.projective_obj inferInstance

/-- See `Functor.projective_obj` for a variant taking `Projective X` as a typeclass argument. -/
/-
**CategoryTheory.Functor.projective_obj_of_projective** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [F.PreservesProjectiveObjects] {X : C},   CategoryTheory.Projective X → Categor
yTheory.Projective (F.obj X)
参数：F : CategoryTheory.Functor C D；F.obj X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.PreservesProjectiveObjects.projective_obj`：∀ {C :
 Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
See `Functor.projective_obj` for a variant taking `Projective X` as a typeclass 
argument.
-/
theorem Functor.projective_obj_of_projective (F : C ⥤ D) [F.PreservesProjectiveObjects] {X : C}
    (h : Projective X) : Projective (F.obj X) :=
  Functor.PreservesProjectiveObjects.projective_obj h
/-
**CategoryTheory.Functor.preservesProjectiveObjects_comp** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} E] (F : CategoryTheory.Functor C D)   (G : CategoryTheo
ry.Functor D E) [F.PreservesProjectiveObjects] [G.PreservesProjectiveObjects],  
 (F.comp G).PreservesProjectiveObjects
参数：F : CategoryTheory.Functor C D；G : CategoryTheory.Functor D E；F.comp G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.projective_obj_of_projective`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   (F : CategoryTheor…
-/
instance Functor.preservesProjectiveObjects_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.PreservesProjectiveObjects] [G.PreservesProjectiveObjects] :
    (F ⋙ G).PreservesProjectiveObjects where
  projective_obj := G.projective_obj_of_projective ∘ F.projective_obj_of_projective
/-
**CategoryTheory.Functor.preservesProjectiveObjects_of_adjunction_of_preservesEp
imorphisms** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor C D}
 {G : CategoryTheory.Functor D C} (adj : F ⊣ G) [G.PreservesEpimorphisms],   F.P
reservesProjectiveObjects
参数：adj : F ⊣ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.map_projective`：map_projective (adj : F ⊣ G) [
G.PreservesEpimorphisms] (P : C) (hP : Projective P) : Projective (F.obj P) wher
e factors f g _
-/
theorem Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [G.PreservesEpimorphisms] :
    F.PreservesProjectiveObjects where
  projective_obj h := adj.map_projective _ h
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) Functor.preservesProjectiveObjects_of_isEquivalence {F : C ⥤ D}
    [IsEquivalence F] : F.PreservesProjectiveObjects :=
  preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms F.asEquivalence.toAdjunction
/-
**CategoryTheory.Functor.preservesEpimorphisms_of_adjunction_of_preservesProject
iveObjects** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.EnoughProjective
s C] {F : CategoryTheory.Functor C D} {G : CategoryTheory.Functor D C} (adj : F 
⊣ G)   [F.PreservesProjectiveObjects], G.PreservesEpimorphisms
参数：adj : F ⊣ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.projective_obj`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   (F : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Projective.factorThru_comp`：factorThru_comp {P X E : C} [
Projective P] (f : P ⟶ X) (e : E ⟶ X) [Epi e] : factorThru f e ≫ e = f
· 使用定理 `CategoryTheory.Adjunction.unit_naturality_assoc`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.epi_of_epi_fac`：epi_of_epi_fac {f : X ⟶ Y} {g : Y ⟶ Z} {h
 : X ⟶ Z} [Epi h] (w : f ≫ g = h) : Epi g
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem Functor.preservesEpimorphisms_of_adjunction_of_preservesProjectiveObjects
    [EnoughProjectives C] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.PreservesProjectiveObjects] :
    G.PreservesEpimorphisms where
  preserves {X Y} f _ := by
    suffices ∃ h, h ≫ G.map f = Projective.π (G.obj Y) from epi_of_epi_fac this.choose_spec
    refine ⟨adj.unit.app (Projective.over (G.obj Y)) ≫
      G.map (Projective.factorThru (F.map (Projective.π _) ≫ adj.counit.app Y) f), ?_⟩
    rw [Category.assoc, ← Functor.map_comp]
    simp

end CategoryTheory

