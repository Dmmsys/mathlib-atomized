/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Preservation of zero objects and zero morphisms

We define the class `PreservesZeroMorphisms` and show basic properties.

## Main results

We provide the following results:
* Left adjoints and right adjoints preserve zero morphisms;
* full functors preserve zero morphisms;
* if both categories involved have a zero object, then a functor preserves zero morphisms if and
  only if it preserves the zero object;
* functors which preserve initial or terminal objects preserve zero morphisms.

-/

@[expose] public section


universe v u v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E]

section ZeroMorphisms

variable [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]

/-- A functor preserves zero morphisms if it sends zero morphisms to zero morphisms. -/
/-
**CategoryTheory.Functor.PreservesZeroMorphisms** 是 Mathlib 中的一个类，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：PreservesZeroMorphisms (F : C ⥤ D) : Prop where /-- For any pair objects `
F (0: X ⟶ Y) = (0 : F X ⟶ F Y)` -/ map_zero : forall X Y : C, F.map (0 : X ⟶ Y) 
= 0
参数：F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor preserves zero morphisms if it sends zero morphisms to zero morphisms.
-/
class PreservesZeroMorphisms (F : C ⥤ D) : Prop where
  /-- For any pair objects `F (0: X ⟶ Y) = (0 : F X ⟶ F Y)` -/
  map_zero : ∀ X Y : C, F.map (0 : X ⟶ Y) = 0 := by aesop

@[simp]
/-
**CategoryTheory.Functor.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Func
tor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [inst_2 : CategoryTheory.Limits.
HasZeroMorphisms C] [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D]   (F : C
ategoryTheory.Functor C D) [F.PreservesZeroMorphisms] (X Y : C), F.map 0 = 0
参数：F : CategoryTheory.Functor C D；X Y : C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.PreservesZeroMorphisms.map_zero`：∀ {C : Type u₁} 
{inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D}   {inst_2 : Category…
-/
protected theorem map_zero (F : C ⥤ D) [PreservesZeroMorphisms F] (X Y : C) :
    F.map (0 : X ⟶ Y) = 0 :=
  PreservesZeroMorphisms.map_zero _ _
/-
**CategoryTheory.Functor.map_isZero** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：map_isZero (F : C ⥤ D) [PreservesZeroMorphisms F] {X : C} (hX : IsZero X) 
: IsZero (F.obj X)
参数：F : C ⥤ D；hX : IsZero X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
-/
lemma map_isZero (F : C ⥤ D) [PreservesZeroMorphisms F] {X : C} (hX : IsZero X) :
    IsZero (F.obj X) := by
  simp only [IsZero.iff_id_eq_zero] at hX ⊢
  rw [← F.map_id, hX, F.map_zero]
/-
**CategoryTheory.Functor.zero_of_map_zero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：zero_of_map_zero (F : C ⥤ D) [PreservesZeroMorphisms F] [Faithful F] {X Y 
: C} (f : X ⟶ Y) (h : F.map f = 0) : f = 0
参数：F : C ⥤ D；f : X ⟶ Y；h : F.map f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
-/
theorem zero_of_map_zero (F : C ⥤ D) [PreservesZeroMorphisms F] [Faithful F] {X Y : C} (f : X ⟶ Y)
    (h : F.map f = 0) : f = 0 :=
  F.map_injective <| h.trans <| Eq.symm <| F.map_zero _ _
/-
**CategoryTheory.Functor.map_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：map_eq_zero_iff (F : C ⥤ D) [PreservesZeroMorphisms F] [Faithful F] {X Y :
 C} {f : X ⟶ Y} : F.map f = 0 ↔ f = 0
参数：F : C ⥤ D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.zero_of_map_zero`：zero_of_map_zero (F : C ⥤ D) [P
reservesZeroMorphisms F] [Faithful F] {X Y : C} (f : X ⟶ Y) (h : F.map f = 0) : 
f = 0
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem map_eq_zero_iff (F : C ⥤ D) [PreservesZeroMorphisms F] [Faithful F] {X Y : C} {f : X ⟶ Y} :
    F.map f = 0 ↔ f = 0 :=
  ⟨F.zero_of_map_zero _, by
    rintro rfl
    exact F.map_zero _ _⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) preservesZeroMorphisms_of_isLeftAdjoint (F : C ⥤ D) [IsLeftAdjoint F] :
    PreservesZeroMorphisms F where
  map_zero X Y := by
    let adj := Adjunction.ofIsLeftAdjoint F
    calc
      dsimp% F.map (0 : X ⟶ Y) = F.map 0 ≫ F.map (adj.unit.app Y) ≫ adj.counit.app (F.obj Y) := ?_
      _ = F.map 0 ≫ F.map ((rightAdjoint F).map (0 : F.obj X ⟶ _)) ≫ adj.counit.app (F.obj Y) := ?_
      _ = 0 := ?_
    · rw [Adjunction.left_triangle_components]
      exact (Category.comp_id _).symm
    · simp only [← Category.assoc, ← F.map_comp, zero_comp]
    · simp

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) preservesZeroMorphisms_of_isRightAdjoint (G : C ⥤ D) [IsRightAdjoint G] :
    PreservesZeroMorphisms G where
  map_zero X Y := by
    let adj := Adjunction.ofIsRightAdjoint G
    calc
      G.map (0 : X ⟶ Y) = adj.unit.app (G.obj X) ≫ G.map (adj.counit.app X) ≫ G.map 0 := ?_
      _ = adj.unit.app (G.obj X) ≫ G.map ((leftAdjoint G).map (0 : _ ⟶ G.obj X)) ≫ G.map 0 := ?_
      _ = 0 := ?_
    · rw [Adjunction.right_triangle_components_assoc]
    · simp only [← G.map_comp, comp_zero]
    · simp only [id_obj, Adjunction.unit_naturality_assoc, zero_comp]
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) preservesZeroMorphisms_of_full (F : C ⥤ D) [Full F] :
    PreservesZeroMorphisms F where
  map_zero X Y :=
    calc
      F.map (0 : X ⟶ Y) = F.map (0 ≫ F.preimage (0 : F.obj Y ⟶ F.obj Y)) := by rw [zero_comp]
      _ = 0 := by rw [F.map_comp, F.map_preimage, comp_zero]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.preservesZeroMorphisms_comp** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.Functor`。
形式化陈述：preservesZeroMorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [F.PreservesZeroMorphi
sms] [G.PreservesZeroMorphisms] : (F ⋙ G).PreservesZeroMorphisms
参数：F : C ⥤ D；G : D ⥤ E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance preservesZeroMorphisms_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] :
    (F ⋙ G).PreservesZeroMorphisms := ⟨by simp⟩
/-
**CategoryTheory.Functor.preservesZeroMorphisms_of_iso** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：preservesZeroMorphisms_of_iso {F₁ F₂ : C ⥤ D} [F₁.PreservesZeroMorphisms] 
(e : F₁ ≅ F₂) : F₂.PreservesZeroMorphisms where map_zero X Y
参数：e : F₁ ≅ F₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preservesZeroMorphisms_of_iso {F₁ F₂ : C ⥤ D} [F₁.PreservesZeroMorphisms] (e : F₁ ≅ F₂) :
    F₂.PreservesZeroMorphisms where
  map_zero X Y := by simp only [← cancel_epi (e.hom.app X), ← e.hom.naturality,
    F₁.map_zero, zero_comp, comp_zero]
/-
**CategoryTheory.Functor.preservesZeroMorphisms_evaluation_obj** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [inst_2 : CategoryTheory.Limits.
HasZeroMorphisms C] (j : D),   ((CategoryTheory.evaluation D C).obj j).Preserves
ZeroMorphisms
参数：j : D；(CategoryTheory.evaluation D C).obj j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance preservesZeroMorphisms_evaluation_obj (j : D) :
    PreservesZeroMorphisms ((evaluation D C).obj j) where
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D ⥤ E) [∀ X, (F.obj X).PreservesZeroMorphisms] :
    F.flip.PreservesZeroMorphisms where
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D ⥤ E) [F.PreservesZeroMorphisms] (Y : D) :
    (F.flip.obj Y).PreservesZeroMorphisms where

omit [HasZeroMorphisms C] in
/-
**CategoryTheory.Functor.whiskerRight_zero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} E] [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
  [inst_4 : CategoryTheory.Limits.HasZeroMorphisms E] {F G : CategoryTheory.Func
tor C D}   (H : CategoryTheory.Functor D E) [H.PreservesZeroMorphisms], Category
Theory.Functor.whiskerRight 0 H = 0
参数：H : CategoryTheory.Functor D E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma whiskerRight_zero {F G : C ⥤ D} (H : D ⥤ E) [H.PreservesZeroMorphisms] :
    whiskerRight (0 : F ⟶ G) H = 0 := by cat_disch

omit [HasZeroMorphisms C] in
/-
**CategoryTheory.Functor.FullyFaithful.preservesZeroMorphisms** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Functor.FullyFaithful`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [inst_2 : CategoryTheory.Limits.
HasZeroMorphisms D] (F : CategoryTheory.Functor C D) (hF : F.FullyFaithful),   F
.PreservesZeroMorphisms
参数：F : CategoryTheory.Functor C D；hF : F.FullyFaithful。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.FullyFaithful.map_preimage`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
-/
lemma FullyFaithful.preservesZeroMorphisms (F : C ⥤ D) (hF : F.FullyFaithful) :
    letI : HasZeroMorphisms C := hF.hasZeroMorphisms
    F.PreservesZeroMorphisms :=
  letI : HasZeroMorphisms C := hF.hasZeroMorphisms
  ⟨fun _ _ ↦ hF.map_preimage _⟩

end ZeroMorphisms

section ZeroObject

variable [HasZeroObject C] [HasZeroObject D]

open ZeroObject

variable [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D)

/-- A functor that preserves zero morphisms also preserves the zero object. -/
@[simps]
/-
**CategoryTheory.Functor.mapZeroObject** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：mapZeroObject [PreservesZeroMorphisms F] : F.obj 0 ≅ 0 where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor that preserves zero morphisms also preserves the zero object.
-/
def mapZeroObject [PreservesZeroMorphisms F] : F.obj 0 ≅ 0 where
  hom := 0
  inv := 0
  hom_inv_id := by rw [← F.map_id, id_zero, F.map_zero, zero_comp]
  inv_hom_id := by rw [id_zero, comp_zero]

variable {F}
/-
**CategoryTheory.Functor.preservesZeroMorphisms_of_map_zero_object** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesZeroMorphisms_of_map_zero_object (i : F.obj 0 ≅ 0) : PreservesZer
oMorphisms F where map_zero X Y
参数：i : F.obj 0 ≅ 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.zero_of_to_zero`：zero_of_to_zero {X : C} (f : X ⟶ 
0) : f = 0
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preservesZeroMorphisms_of_map_zero_object (i : F.obj 0 ≅ 0) : PreservesZeroMorphisms F where
  map_zero X Y :=
    calc
      F.map (0 : X ⟶ Y) = F.map (0 : X ⟶ 0) ≫ F.map 0 := by rw [← Functor.map_comp, comp_zero]
      _ = F.map 0 ≫ (i.hom ≫ i.inv) ≫ F.map 0 := by rw [Iso.hom_inv_id, Category.id_comp]
      _ = 0 := by simp only [zero_of_to_zero i.hom, zero_comp, comp_zero]
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) preservesZeroMorphisms_of_preserves_initial_object
    [PreservesColimit (Functor.empty.{0} C) F] : PreservesZeroMorphisms F :=
  preservesZeroMorphisms_of_map_zero_object <|
    F.mapIso HasZeroObject.zeroIsoInitial ≪≫
      PreservesInitial.iso F ≪≫ HasZeroObject.zeroIsoInitial.symm
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) preservesZeroMorphisms_of_preserves_terminal_object
    [PreservesLimit (Functor.empty.{0} C) F] : PreservesZeroMorphisms F :=
  preservesZeroMorphisms_of_map_zero_object <|
    F.mapIso HasZeroObject.zeroIsoTerminal ≪≫
      PreservesTerminal.iso F ≪≫ HasZeroObject.zeroIsoTerminal.symm

variable (F)

/-- Preserving zero morphisms implies preserving terminal objects. -/
/-
**CategoryTheory.Functor.preservesTerminalObject_of_preservesZeroMorphisms** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesTerminalObject_of_preservesZeroMorphisms [PreservesZeroMorphisms 
F] : PreservesLimit (Functor.empty.{0} C) F
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesTerminal_of_iso`：preservesTerminal_of_iso
 (f : G.obj (⊤_ C) ≅ ⊤_ D) : PreservesLimit (Functor.empty.{0} C) G
· 使用定理 `CategoryTheory.Limits.HasZeroObject.hasTerminal`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C],   Cat
egoryTheory.Limits.HasTerminal C

--- 原说明 ---
Preserving zero morphisms implies preserving terminal objects.
-/
lemma preservesTerminalObject_of_preservesZeroMorphisms [PreservesZeroMorphisms F] :
    PreservesLimit (Functor.empty.{0} C) F :=
  preservesTerminal_of_iso F <|
    F.mapIso HasZeroObject.zeroIsoTerminal.symm ≪≫ mapZeroObject F ≪≫ HasZeroObject.zeroIsoTerminal

/-- Preserving zero morphisms implies preserving terminal objects. -/
/-
**CategoryTheory.Functor.preservesInitialObject_of_preservesZeroMorphisms** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesInitialObject_of_preservesZeroMorphisms [PreservesZeroMorphisms F
] : PreservesColimit (Functor.empty.{0} C) F
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesInitial_of_iso`：preservesInitial_of_iso (
f : ⊥_ D ≅ G.obj (⊥_ C)) : PreservesColimit (Functor.empty.{0} C) G
· 使用定理 `CategoryTheory.Limits.HasZeroObject.hasInitial`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C],   Cate
goryTheory.Limits.HasInitial C

--- 原说明 ---
Preserving zero morphisms implies preserving terminal objects.
-/
lemma preservesInitialObject_of_preservesZeroMorphisms [PreservesZeroMorphisms F] :
    PreservesColimit (Functor.empty.{0} C) F :=
  preservesInitial_of_iso F <|
    HasZeroObject.zeroIsoInitial.symm ≪≫
      (mapZeroObject F).symm ≪≫ (F.mapIso HasZeroObject.zeroIsoInitial.symm).symm

end ZeroObject

section

variable [HasZeroObject D] [HasZeroMorphisms D]
  (G : C ⥤ D) (hG : IsZero G) (J : Type*) [Category* J]

include hG

/-- A zero functor preserves limits. -/
/-
**CategoryTheory.Functor.preservesLimitsOfShape_of_isZero** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Functor`。
形式化陈述：preservesLimitsOfShape_of_isZero : PreservesLimitsOfShape J G where preser
vesLimit {K}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.isZero`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} D]   (F
 : CategoryTheory.F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.isZero_iff`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} D] 
  [CategoryTheory.Limit…

--- 原说明 ---
A zero functor preserves limits.
-/
lemma preservesLimitsOfShape_of_isZero : PreservesLimitsOfShape J G where
  preservesLimit {K} := ⟨fun _ => ⟨by
    rw [Functor.isZero_iff] at hG
    exact IsLimit.ofIsZero _ ((K ⋙ G).isZero (fun X ↦ hG _)) (hG _)⟩⟩

/-- A zero functor preserves colimits. -/
/-
**CategoryTheory.Functor.preservesColimitsOfShape_of_isZero** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesColimitsOfShape_of_isZero : PreservesColimitsOfShape J G where pr
eservesColimit {K}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.isZero`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} D]   (F
 : CategoryTheory.F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.isZero_iff`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} D] 
  [CategoryTheory.Limit…

--- 原说明 ---
A zero functor preserves colimits.
-/
lemma preservesColimitsOfShape_of_isZero : PreservesColimitsOfShape J G where
  preservesColimit {K} := ⟨fun _ => ⟨by
    rw [Functor.isZero_iff] at hG
    exact IsColimit.ofIsZero _ ((K ⋙ G).isZero (fun X ↦ hG _)) (hG _)⟩⟩

/-- A zero functor preserves limits. -/
/-
**CategoryTheory.Functor.preservesLimitsOfSize_of_isZero** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Functor`。
形式化陈述：preservesLimitsOfSize_of_isZero : PreservesLimitsOfSize.{v, u} G where pre
servesLimitsOfShape
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.preservesLimitsOfShape_of_isZero`：preservesLimits
OfShape_of_isZero : PreservesLimitsOfShape J G where preservesLimit {K}

--- 原说明 ---
A zero functor preserves limits.
-/
lemma preservesLimitsOfSize_of_isZero : PreservesLimitsOfSize.{v, u} G where
  preservesLimitsOfShape := G.preservesLimitsOfShape_of_isZero hG _

/-- A zero functor preserves colimits. -/
/-
**CategoryTheory.Functor.preservesColimitsOfSize_of_isZero** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesColimitsOfSize_of_isZero : PreservesColimitsOfSize.{v, u} G where
 preservesColimitsOfShape
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.preservesColimitsOfShape_of_isZero`：preservesColi
mitsOfShape_of_isZero : PreservesColimitsOfShape J G where preservesColimit {K}

--- 原说明 ---
A zero functor preserves colimits.
-/
lemma preservesColimitsOfSize_of_isZero : PreservesColimitsOfSize.{v, u} G where
  preservesColimitsOfShape := G.preservesColimitsOfShape_of_isZero hG _

end

end CategoryTheory.Functor

