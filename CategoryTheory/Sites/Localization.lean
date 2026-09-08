/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.Bousfield
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# The sheaf category as a localized category

In this file, it is shown that the category of sheaves `Sheaf J A` is a localization
of the category `Presheaf J A` with respect to the class `J.W` of morphisms
of presheaves which become isomorphisms after applying the sheafification functor.

-/

universe w

public section

namespace CategoryTheory

open Localization

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) {A : Type*} [Category* A]

namespace GrothendieckTopology

/-- The class of morphisms of presheaves which become isomorphisms after sheafification.
(See `GrothendieckTopology.W_iff`.) -/
/-
**CategoryTheory.GrothendieckTopology.W** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryThe
ory.GrothendieckTopology`。
形式化陈述：W : MorphismProperty (Cᵒᵖ ⥤ A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of morphisms of presheaves which become isomorphisms after sheafificat
ion.
(See `GrothendieckTopology.W_iff`.)
-/
abbrev W : MorphismProperty (Cᵒᵖ ⥤ A) := ObjectProperty.isLocal (Presheaf.IsSheaf J)

variable (A) in
/-
**CategoryTheory.GrothendieckTopology.W_eq_isLocal_range_sheafToPresheaf_obj** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：W_eq_isLocal_range_sheafToPresheaf_obj : J.W = ObjectProperty.isLocal (· i
n Set.range (sheafToPresheaf J A).obj)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
-/
lemma W_eq_isLocal_range_sheafToPresheaf_obj :
    J.W = ObjectProperty.isLocal (· ∈ Set.range (sheafToPresheaf J A).obj) := by
  apply congr_arg
  ext P
  constructor
  · intro hP
    exact ⟨⟨P, hP⟩, rfl⟩
  · rintro ⟨F, rfl⟩
    exact F.property
/-
**CategoryTheory.GrothendieckTopology.W_sheafToPresheaf_map_iff_isIso** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：W_sheafToPresheaf_map_iff_isIso {F₁ F₂ : Sheaf J A} (φ : F₁ ⟶ F₂) : J.W ((
sheafToPresheaf J A).map φ) ↔ IsIso φ
参数：φ : F₁ ⟶ F₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GrothendieckTopology.W_eq_isLocal_range_sheafToPresheaf_o
bj`：W_eq_isLocal_range_sheafToPresheaf_obj : J.W = ObjectProperty.isLocal (· in 
Set.range (sheafToPresheaf J A).obj)
· 使用引理 `CategoryTheory.ObjectProperty.isLocal_iff_isIso`：isLocal_iff_isIso {X Y 
: C} (f : X ⟶ Y) (hX : P X) (hY : P Y) : P.isLocal f ↔ IsIso f
· 使用引理 `CategoryTheory.isIso_iff_of_reflects_iso`：isIso_iff_of_reflects_iso {A B
 : C} (f : A ⟶ B) (F : C ⥤ D) [F.ReflectsIsomorphisms] : IsIso (F.map f) ↔ IsIso
 f
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_full_and_faithful`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma W_sheafToPresheaf_map_iff_isIso {F₁ F₂ : Sheaf J A} (φ : F₁ ⟶ F₂) :
    J.W ((sheafToPresheaf J A).map φ) ↔ IsIso φ := by
  rw [W_eq_isLocal_range_sheafToPresheaf_obj,
    ObjectProperty.isLocal_iff_isIso _ _ ⟨_, rfl⟩ ⟨_, rfl⟩, isIso_iff_of_reflects_iso]

section Adjunction

variable {G : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A}

/-
**CategoryTheory.GrothendieckTopology.W_adj_unit_app** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.GrothendieckTopology`。
形式化陈述：W_adj_unit_app (adj : G ⊣ sheafToPresheaf J A) (P : Cᵒᵖ ⥤ A) : J.W (adj.un
it.app P)
参数：adj : G ⊣ sheafToPresheaf J A；P : Cᵒᵖ ⥤ A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GrothendieckTopology.W_eq_isLocal_range_sheafToPresheaf_o
bj`：W_eq_isLocal_range_sheafToPresheaf_obj : J.W = ObjectProperty.isLocal (· in 
Set.range (sheafToPresheaf J A).obj)
· 使用引理 `CategoryTheory.ObjectProperty.isLocal_adj_unit_app`：isLocal_adj_unit_app
 (X : D) : isLocal (· in Set.range F.obj) (adj.unit.app X)
-/
lemma W_adj_unit_app (adj : G ⊣ sheafToPresheaf J A) (P : Cᵒᵖ ⥤ A) : J.W (adj.unit.app P) := by
  rw [W_eq_isLocal_range_sheafToPresheaf_obj]
  exact ObjectProperty.isLocal_adj_unit_app adj P
/-
**CategoryTheory.GrothendieckTopology.W_iff_isIso_map_of_adjunction** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：W_iff_isIso_map_of_adjunction (adj : G ⊣ sheafToPresheaf J A) {P₁ P₂ : Cᵒᵖ
 ⥤ A} (f : P₁ ⟶ P₂) : J.W f ↔ IsIso (G.map f)
参数：adj : G ⊣ sheafToPresheaf J A；f : P₁ ⟶ P₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GrothendieckTopology.W_eq_isLocal_range_sheafToPresheaf_o
bj`：W_eq_isLocal_range_sheafToPresheaf_obj : J.W = ObjectProperty.isLocal (· in 
Set.range (sheafToPresheaf J A).obj)
· 使用引理 `CategoryTheory.ObjectProperty.isLocal_iff_isIso_map`：isLocal_iff_isIso_m
ap {X Y : D} (f : X ⟶ Y) : isLocal (· in Set.range F.obj) f ↔ IsIso (G.map f)
-/
lemma W_iff_isIso_map_of_adjunction (adj : G ⊣ sheafToPresheaf J A)
    {P₁ P₂ : Cᵒᵖ ⥤ A} (f : P₁ ⟶ P₂) :
    J.W f ↔ IsIso (G.map f) := by
  rw [W_eq_isLocal_range_sheafToPresheaf_obj]
  exact ObjectProperty.isLocal_iff_isIso_map adj f
/-
**CategoryTheory.GrothendieckTopology.W_eq_inverseImage_isomorphisms_of_adjuncti
on** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：W_eq_inverseImage_isomorphisms_of_adjunction (adj : G ⊣ sheafToPresheaf J 
A) : J.W = (MorphismProperty.isomorphisms _).inverseImage G
参数：adj : G ⊣ sheafToPresheaf J A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GrothendieckTopology.W_eq_isLocal_range_sheafToPresheaf_o
bj`：W_eq_isLocal_range_sheafToPresheaf_obj : J.W = ObjectProperty.isLocal (· in 
Set.range (sheafToPresheaf J A).obj)
· 使用引理 `CategoryTheory.ObjectProperty.isLocal_eq_inverseImage_isomorphisms`：isLo
cal_eq_inverseImage_isomorphisms : isLocal (· in Set.range F.obj) = (MorphismPro
perty.isomorphisms _).inverseImage G
-/
lemma W_eq_inverseImage_isomorphisms_of_adjunction (adj : G ⊣ sheafToPresheaf J A) :
    J.W = (MorphismProperty.isomorphisms _).inverseImage G := by
  rw [W_eq_isLocal_range_sheafToPresheaf_obj,
    ObjectProperty.isLocal_eq_inverseImage_isomorphisms adj]

end Adjunction

section HasWeakSheafify

variable [HasWeakSheafify J A]

/-
**CategoryTheory.GrothendieckTopology.W_toSheafify** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.GrothendieckTopology`。
形式化陈述：W_toSheafify (P : Cᵒᵖ ⥤ A) : J.W (toSheafify J P)
参数：P : Cᵒᵖ ⥤ A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GrothendieckTopology.W_adj_unit_app`：W_adj_unit_app (adj 
: G ⊣ sheafToPresheaf J A) (P : Cᵒᵖ ⥤ A) : J.W (adj.unit.app P)
-/
lemma W_toSheafify (P : Cᵒᵖ ⥤ A) : J.W (toSheafify J P) :=
  J.W_adj_unit_app (sheafificationAdjunction J A) P
/-
**CategoryTheory.GrothendieckTopology.W_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.GrothendieckTopology`。
形式化陈述：W_iff {P₁ P₂ : Cᵒᵖ ⥤ A} (f : P₁ ⟶ P₂) : J.W f ↔ IsIso ((presheafToSheaf J 
A).map f)
参数：f : P₁ ⟶ P₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GrothendieckTopology.W_iff_isIso_map_of_adjunction`：W_iff
_isIso_map_of_adjunction (adj : G ⊣ sheafToPresheaf J A) {P₁ P₂ : Cᵒᵖ ⥤ A} (f : 
P₁ ⟶ P₂) : J.W f ↔ IsIso (G.map f)
-/
lemma W_iff {P₁ P₂ : Cᵒᵖ ⥤ A} (f : P₁ ⟶ P₂) :
    J.W f ↔ IsIso ((presheafToSheaf J A).map f) :=
  J.W_iff_isIso_map_of_adjunction (sheafificationAdjunction J A) f

variable (A) in
/-
**CategoryTheory.GrothendieckTopology.W_eq_inverseImage_isomorphisms** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：W_eq_inverseImage_isomorphisms : J.W = (MorphismProperty.isomorphisms _).i
nverseImage (presheafToSheaf J A)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GrothendieckTopology.W_eq_inverseImage_isomorphisms_of_ad
junction`：W_eq_inverseImage_isomorphisms_of_adjunction (adj : G ⊣ sheafToPreshea
f J A) : J.W = (MorphismProperty.isomorphisms _).inverseImage G
-/
lemma W_eq_inverseImage_isomorphisms :
    J.W = (MorphismProperty.isomorphisms _).inverseImage (presheafToSheaf J A) :=
  J.W_eq_inverseImage_isomorphisms_of_adjunction (sheafificationAdjunction J A)
/-
**CategoryTheory.GrothendieckTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (presheafToSheaf J A).IsLocalization J.W := by
  rw [W_eq_inverseImage_isomorphisms]
  exact (sheafificationAdjunction J A).isLocalization

end HasWeakSheafify

end GrothendieckTopology

/-
**CategoryTheory.Sieve.W_shrinkFunctor_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Sieve.W_shrinkFunctor_ι_of_mem [LocallySmall.{w} C] {X : C} (S : Sieve X) (hS : S ∈ J X) :
    J.W (Sieve.shrinkFunctor.{w} S).ι := by
  intro Z hZ
  rw [isSheaf_iff_isSheaf_of_type] at hZ
  rw [← Presieve.isSheafFor_iff_bijective_shrinkFunctor_ι_comp]
  exact hZ _ hS

variable {D : Type*} [Category* D] {K : GrothendieckTopology D}

/-- SGA 4 III 1.2 (ii) => (i) -/
/-
**CategoryTheory.Presieve.IsSheaf.comp_of_W_map_of_adjunction** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Presieve.IsSheaf`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (J : Catego
ryTheory.GrothendieckTopology C)   {D : Type u_3} [inst_1 : CategoryTheory.Categ
ory.{v_3, u_3} D] {K : CategoryTheory.GrothendieckTopology D}   [inst_2 : Catego
ryTheory.LocallySmall.{w, v_1, u_1} C] {F : CategoryTheory.Functor C D}   {H : C
ategoryTheory.Functor (CategoryTheory.Functor Cᵒᵖ (Type w)) (CategoryTheory.Func
tor Dᵒᵖ (Type w))}   (adj : H ⊣ (CategoryTheory.Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (
Type w)).obj F.op),   (∀ ⦃X : C⦄ ⦃S : CategoryTheory.Sieve X⦄,       S ∈ J X → K
.W (H.map (CategoryTheory.Sieve.shrinkFunctor.{w, v_1, u_1} S).ι)) →     ∀ (G : 
CategoryTheory.Functor Dᵒᵖ (Type w)),       CategoryTheory.Presieve.IsSheaf K G 
→ CategoryTheory.Presieve.IsSheaf J (F.op.comp G)
参数：J : CategoryTheory.GrothendieckTopology C；CategoryTheory.Functor Cᵒᵖ (Type w)
；CategoryTheory.Functor Dᵒᵖ (Type w)；adj : H ⊣ (CategoryTheory.Functor.whiskerin
gLeft Cᵒᵖ Dᵒᵖ (Type w)).obj F.op；∀ ⦃X : C⦄ ⦃S : CategoryTheory.Sieve X⦄,       S
 ∈ J X → K.W (H.map (CategoryTheory.Sieve.shrinkFunctor.{w, v_1, u_1} S).ι)；G : 
CategoryTheory.Functor Dᵒᵖ (Type w)；F.op.comp G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Presieve.isSheafFor_iff_bijective_shrinkFunctor_ι_comp`：i
sSheafFor_iff_bijective_shrinkFunctor_ι_comp [LocallySmall.{w} C] {X : C} (S : S
ieve X) (F : Cᵒᵖ ⥤ Type w) : IsSheafFor F S.arrows ↔ Functi…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.whiskeringLeft_obj_obj`：∀ (C : Type u₁) [inst : C
ategoryTheory.Category.{v₁, u₁} C] (D : Type u₂) [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   (E : Type u₃) [ins…
· 使用引理 `CategoryTheory.Adjunction.map_comp_bijective_iff`：map_comp_bijective_iff
 (adj : F ⊣ G) {X Y : C} (f : X ⟶ Y) (Z : D) : Function.Bijective (fun (g : F.ob
j Y ⟶ Z) => F.map f ≫ g) ↔ Function.Bi…
· 使用定理 `CategoryTheory.isSheaf_iff_isSheaf_of_type`：isSheaf_iff_isSheaf_of_type 
(P : Cᵒᵖ ⥤ Type w) : Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P

--- 原说明 ---
SGA 4 III 1.2 (ii) => (i)
-/
lemma Presieve.IsSheaf.comp_of_W_map_of_adjunction
    [LocallySmall.{w} C] {F : C ⥤ D} {H : (Cᵒᵖ ⥤ Type w) ⥤ (Dᵒᵖ ⥤ Type w)}
    (adj : H ⊣ (Functor.whiskeringLeft _ _ _).obj F.op)
    (h : ∀ ⦃X : C⦄ ⦃S : Sieve X⦄, S ∈ J X → K.W (H.map <| (Sieve.shrinkFunctor.{w} S).ι))
    (G : Dᵒᵖ ⥤ Type w) (hG : Presieve.IsSheaf K G) :
    Presieve.IsSheaf J (F.op ⋙ G) := by
  intro X S hS
  rw [Presieve.isSheafFor_iff_bijective_shrinkFunctor_ι_comp, ← Functor.whiskeringLeft_obj_obj,
    ← adj.map_comp_bijective_iff]
  refine h hS _ ?_
  rwa [isSheaf_iff_isSheaf_of_type]

end CategoryTheory

