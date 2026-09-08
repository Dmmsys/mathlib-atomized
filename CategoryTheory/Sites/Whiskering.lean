/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.ConcreteCategory.Forget

/-!

In this file we construct the functor `Sheaf J A ⥤ Sheaf J B` between sheaf categories
obtained by composition with a functor `F : A ⥤ B`.

In order for the sheaf condition to be preserved, `F` must preserve the correct limits.
The lemma `Presheaf.IsSheaf.comp` says that composition with such an `F` indeed preserves the
sheaf condition.

The functor between sheaf categories is called `sheafCompose J F`.
Given a natural transformation `η : F ⟶ G`, we obtain a natural transformation
`sheafCompose J F ⟶ sheafCompose J G`, which we call `sheafCompose_map J η`.

-/

@[expose] public section


namespace CategoryTheory

open CategoryTheory.Limits CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {A : Type u₂} [Category.{v₂} A]
variable {B : Type u₃} [Category.{v₃} B]
variable (J : GrothendieckTopology C)
variable {U : C} (R : Presieve U)
variable (F G H : A ⥤ B) (η : F ⟶ G) (γ : G ⟶ H)

/-- Describes the property of a functor to "preserve sheaves". -/
/-
**CategoryTheory.GrothendieckTopology.HasSheafCompose** 是 Mathlib 中的一个归纳类型，位于命名空
间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {A : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} A] →         {B : Typ
e u₃} →           [inst_2 : CategoryTheory.Category.{v₃, u₃} B] →             Ca
tegoryTheory.GrothendieckTopology C → CategoryTheory.Functor A B → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Describes the property of a functor to "preserve sheaves".
-/
class GrothendieckTopology.HasSheafCompose : Prop where
  /-- For every sheaf `P`, `P ⋙ F` is a sheaf. -/
  isSheaf (P : Cᵒᵖ ⥤ A) (hP : Presheaf.IsSheaf J P) : Presheaf.IsSheaf J (P ⋙ F)

variable [J.HasSheafCompose F] [J.HasSheafCompose G] [J.HasSheafCompose H]

/-- Composing a functor which `HasSheafCompose`, yields a functor between sheaf categories. -/
@[simps! obj_obj map_hom]
/-
**CategoryTheory.sheafCompose** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：sheafCompose : Sheaf J A ⥤ Sheaf J B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing a functor which `HasSheafCompose`, yields a functor between sheaf cate
gories.
-/
def sheafCompose : Sheaf J A ⥤ Sheaf J B :=
  ObjectProperty.lift _
    (sheafToPresheaf _ _ ⋙ (Functor.whiskeringRight _ _ _).obj F)
      (fun P ↦ GrothendieckTopology.HasSheafCompose.isSheaf _ P.property)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.Faithful] : (sheafCompose J F ⋙ sheafToPresheaf _ _).Faithful :=
  show (sheafToPresheaf _ _ ⋙ (whiskeringRight Cᵒᵖ A B).obj F).Faithful from inferInstance
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.Faithful] [F.Full] : (sheafCompose J F ⋙ sheafToPresheaf _ _).Full :=
  show (sheafToPresheaf _ _ ⋙ (whiskeringRight Cᵒᵖ A B).obj F).Full from inferInstance

variable {F} in
/-- If `F : A ⥤ B` is fully faithful, then `sheafCompose J F ⋙ sheafToPresheaf J B` is fully
faithful. -/
/-
**CategoryTheory.fullyFaithfulSheafComposeCompSheafToPresheaf** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory`。
形式化陈述：fullyFaithfulSheafComposeCompSheafToPresheaf (hF : F.FullyFaithful) : (she
afCompose J F ⋙ sheafToPresheaf J B).FullyFaithful
参数：hF : F.FullyFaithful。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : A ⥤ B` is fully faithful, then `sheafCompose J F ⋙ sheafToPresheaf J B` 
is fully
faithful.
-/
def fullyFaithfulSheafComposeCompSheafToPresheaf (hF : F.FullyFaithful) :
    (sheafCompose J F ⋙ sheafToPresheaf J B).FullyFaithful :=
  (fullyFaithfulSheafToPresheaf J A).comp (hF.whiskeringRight Cᵒᵖ)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.Faithful] : (sheafCompose J F).Faithful :=
  Functor.Faithful.of_comp (sheafCompose J F) (sheafToPresheaf _ _)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.Full] [F.Faithful] : (sheafCompose J F).Full :=
  Functor.Full.of_comp_faithful (sheafCompose J F) (sheafToPresheaf _ _)

variable {F} in
/-- If `F : A ⥤ B` is fully faithful, then `sheafCompose J F` is fully faithful. -/
/-
**CategoryTheory.fullyFaithfulSheafCompose** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory`。
形式化陈述：fullyFaithfulSheafCompose (hF : F.FullyFaithful) : (sheafCompose J F).Full
yFaithful
参数：hF : F.FullyFaithful。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : A ⥤ B` is fully faithful, then `sheafCompose J F` is fully faithful.
-/
def fullyFaithfulSheafCompose (hF : F.FullyFaithful) :
    (sheafCompose J F).FullyFaithful :=
  (fullyFaithfulSheafComposeCompSheafToPresheaf J hF).ofCompFaithful
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.ReflectsIsomorphisms] : (sheafCompose J F).ReflectsIsomorphisms where
  reflects {G₁ G₂} f _ := by
    rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _),
      ← isIso_iff_of_reflects_iso _ ((whiskeringRight Cᵒᵖ A B).obj F)]
    change IsIso ((sheafToPresheaf _ _).map ((sheafCompose J F).map f))
    infer_instance

variable {F G}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
If `η : F ⟶ G` is a natural transformation then we obtain a morphism of functors
`sheafCompose J F ⟶ sheafCompose J G` by whiskering with `η` on the level of presheaves.
-/
/-
**CategoryTheory.sheafCompose_map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：sheafCompose_map : sheafCompose J F ⟶ sheafCompose J G where app
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `η : F ⟶ G` is a natural transformation then we obtain a morphism of functors
`sheafCompose J F ⟶ sheafCompose J G` by whiskering with `η` on the level of pre
sheaves.
-/
def sheafCompose_map : sheafCompose J F ⟶ sheafCompose J G where
  app := fun _ => .mk <| whiskerLeft _ η

@[simp]
/-
**CategoryTheory.sheafCompose_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：sheafCompose_id : sheafCompose_map (F
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sheafCompose_id : sheafCompose_map (F := F) J (𝟙 _) = 𝟙 _ := rfl

@[simp]
/-
**CategoryTheory.sheafCompose_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：sheafCompose_comp : sheafCompose_map J (η ≫ γ) = sheafCompose_map J η ≫ sh
eafCompose_map J γ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sheafCompose_comp :
    sheafCompose_map J (η ≫ γ) = sheafCompose_map J η ≫ sheafCompose_map J γ := rfl

namespace GrothendieckTopology.Cover

variable (F G) {J}
variable (P : Cᵒᵖ ⥤ A) {X : C} (S : J.Cover X)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The multicospan associated to a cover `S : J.Cover X` and a presheaf of the form `P ⋙ F`
is isomorphic to the composition of the multicospan associated to `S` and `P`,
composed with `F`. -/
@[simps!]
/-
**CategoryTheory.GrothendieckTopology.Cover.multicospanComp** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.GrothendieckTopology.Cover`。
形式化陈述：multicospanComp : (S.index (P ⋙ F)).multicospan ≅ (S.index P).multicospan 
⋙ F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multicospan associated to a cover `S : J.Cover X` and a presheaf of the form
 `P ⋙ F`
is isomorphic to the composition of the multicospan associated to `S` and `P`,
composed with `F`.
-/
def multicospanComp : (S.index (P ⋙ F)).multicospan ≅ (S.index P).multicospan ⋙ F :=
  NatIso.ofComponents
    (fun t =>
      match t with
      | WalkingMulticospan.left _ => Iso.refl _
      | WalkingMulticospan.right _ => Iso.refl _)
    (by
      rintro (a | b) (a | b) (f | f | f)
      all_goals cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Mapping the multifork associated to a cover `S : J.Cover X` and a presheaf `P` with
respect to a functor `F` is isomorphic (upto a natural isomorphism of the underlying functors)
to the multifork associated to `S` and `P ⋙ F`. -/
/-
**CategoryTheory.GrothendieckTopology.Cover.mapMultifork** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.GrothendieckTopology.Cover`。
形式化陈述：mapMultifork : F.mapCone (S.multifork P) ≅ (Limits.Cone.postcompose (S.mul
ticospanComp F P).hom).obj (S.multifork (P ⋙ F))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Mapping the multifork associated to a cover `S : J.Cover X` and a presheaf `P` w
ith
respect to a functor `F` is isomorphic (upto a natural isomorphism of the underl
ying functors)
to the multifork associated to `S` and `P ⋙ F`.
-/
def mapMultifork :
    F.mapCone (S.multifork P) ≅
      (Limits.Cone.postcompose (S.multicospanComp F P).hom).obj (S.multifork (P ⋙ F)) :=
  Cone.ext (Iso.refl _)

end GrothendieckTopology.Cover

/--
Composing a sheaf with a functor preserving the limit of `(S.index P).multicospan` yields a functor
between sheaf categories.
-/
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing a sheaf with a functor preserving the limit of `(S.index P).multicospa
n` yields a functor
between sheaf categories.
-/
instance (priority := high) hasSheafCompose_of_preservesMulticospan (F : A ⥤ B)
    [∀ (X : C) (S : J.Cover X) (P : Cᵒᵖ ⥤ A), PreservesLimit (S.index P).multicospan F] :
    J.HasSheafCompose F where
  isSheaf P hP := by
    rw [Presheaf.isSheaf_iff_multifork] at hP ⊢
    intro X S
    obtain ⟨h⟩ := hP X S
    replace h := isLimitOfPreserves F h
    replace h := Limits.IsLimit.ofIsoLimit h (S.mapMultifork F P)
    exact ⟨Limits.IsLimit.postcomposeHomEquiv (S.multicospanComp F P) _ h⟩

/--
Composing a sheaf with a functor preserving limits of the same size as the hom sets in `C` yields a
functor between sheaf categories.

Note: the size of the limit that `F` is required to preserve in
`hasSheafCompose_of_preservesMulticospan` is in general larger than this.
-/
/-
**CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize** 是 Mathlib 中的一个实例，位于命
名空间 `CategoryTheory`。
形式化陈述：hasSheafCompose_of_preservesLimitsOfSize [PreservesLimitsOfSize.{v₁, max u
₁ v₁} F] : J.HasSheafCompose F where isSheaf _ hP
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf`：isSheaf_comp_of_isSheaf
 (s : A ⥤ B) [PreservesLimitsOfSize.{v₁, max v₁ u₁} s] (h : IsSheaf J P) : IsShe
af J (P ⋙ s)

--- 原说明 ---
Composing a sheaf with a functor preserving limits of the same size as the hom s
ets in `C` yields a
functor between sheaf categories.

Note: the size of the limit that `F` is required to preserve in
`hasSheafCompose_of_preservesMulticospan` is in general larger than this.
-/
instance hasSheafCompose_of_preservesLimitsOfSize [PreservesLimitsOfSize.{v₁, max u₁ v₁} F] :
    J.HasSheafCompose F where
  isSheaf _ hP := Presheaf.isSheaf_comp_of_isSheaf J _ F hP

variable {J}
/-
**CategoryTheory.Sheaf.isSeparated** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.She
af`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} A]   {J : CategoryTheory.Grothendieck
Topology C} {FA : A → A → Type u_1} {CA : A → Type u_2}   [inst_2 : (X Y : A) → 
FunLike (FA X Y) (CA X) (CA Y)] [inst_3 : CategoryTheory.ConcreteCategory A FA] 
  [J.HasSheafCompose (CategoryTheory.forget A)] (F : CategoryTheory.Sheaf J A), 
  CategoryTheory.Presheaf.IsSeparated J F.obj
参数：X Y : A；FA X Y；CA X；CA Y；CategoryTheory.forget A；F : CategoryTheory.Sheaf J A
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.IsSeparatedFor.ext`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X : C
}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Presieve.IsSheaf.isSeparated`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C}   {P :
 CategoryTheory.Functor Cᵒᵖ (Type…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.isSheaf_iff_isSheaf_of_type`：isSheaf_iff_isSheaf_of_type 
(P : Cᵒᵖ ⥤ Type w) : Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
-/
lemma Sheaf.isSeparated {FA : A → A → Type*} {CA : A → Type*}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA] [J.HasSheafCompose (forget A)]
    (F : Sheaf J A) : Presheaf.IsSeparated J F.obj := by
  rintro X S hS x y h
  exact (((isSheaf_iff_isSheaf_of_type _ _).1
    ((sheafCompose J (forget A)).obj F).2).isSeparated S hS).ext (fun _ _ hf => h _ _ hf)
/-
**CategoryTheory.Presheaf.IsSheaf.isSeparated** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Presheaf.IsSheaf`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} A]   {J : CategoryTheory.Grothendieck
Topology C} {F : CategoryTheory.Functor Cᵒᵖ A} {FA : A → A → Type u_1}   {CA : A
 → Type u_2} [inst_2 : (X Y : A) → FunLike (FA X Y) (CA X) (CA Y)]   [inst_3 : C
ategoryTheory.ConcreteCategory A FA] [J.HasSheafCompose (CategoryTheory.forget A
)],   CategoryTheory.Presheaf.IsSheaf J F → CategoryTheory.Presheaf.IsSeparated 
J F
参数：X Y : A；FA X Y；CA X；CA Y；CategoryTheory.forget A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sheaf.isSeparated`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} A
]   {J : CategoryTheor…
-/
lemma Presheaf.IsSheaf.isSeparated {F : Cᵒᵖ ⥤ A} {FA : A → A → Type*} {CA : A → Type*}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
    [J.HasSheafCompose (forget A)] (hF : Presheaf.IsSheaf J F) :
    Presheaf.IsSeparated J F :=
  Sheaf.isSeparated ⟨F, hF⟩

end CategoryTheory

