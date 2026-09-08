/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-!

In this file, we show that an adjunction `G ⊣ F` induces an adjunction between
categories of sheaves. We also show that `G` preserves sheafification.

-/

@[expose] public section


namespace CategoryTheory

open GrothendieckTopology Limits Opposite CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type*} [Category* E]
variable {F : D ⥤ E} {G : E ⥤ D}

/-- The forgetful functor from `Sheaf J D` to sheaves of types, for a concrete category `D`
whose forgetful functor preserves the correct limits. -/
/-
**CategoryTheory.sheafForget** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：sheafForget {FD : D -> D -> Type*} {CD : D -> Type*} [forall X Y, FunLike 
(FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD] [HasSheafCompose J (forget D)] :
 Sheaf J D ⥤ Sheaf J (Type _)
参数：FD X Y；CD X；CD Y；forget D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from `Sheaf J D` to sheaves of types, for a concrete categ
ory `D`
whose forgetful functor preserves the correct limits.
-/
abbrev sheafForget {FD : D → D → Type*} {CD : D → Type*}
    [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD]
    [HasSheafCompose J (forget D)] : Sheaf J D ⥤ Sheaf J (Type _) :=
  sheafCompose J (forget D)

namespace Sheaf

noncomputable section

/-- An adjunction `adj : G ⊣ F` with `F : D ⥤ E` and `G : E ⥤ D` induces an adjunction
between `Sheaf J D` and `Sheaf J E`, in contexts where one can sheafify `D`-valued presheaves,
and postcomposing with `F` preserves the property of being a sheaf. -/
/-
**CategoryTheory.Sheaf.adjunction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Shea
f`。
形式化陈述：adjunction [HasWeakSheafify J D] [HasSheafCompose J F] (adj : G ⊣ F) : com
poseAndSheafify J G ⊣ sheafCompose J F
参数：adj : G ⊣ F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An adjunction `adj : G ⊣ F` with `F : D ⥤ E` and `G : E ⥤ D` induces an adjuncti
on
between `Sheaf J D` and `Sheaf J E`, in contexts where one can sheafify `D`-valu
ed presheaves,
and postcomposing with `F` preserves the property of being a sheaf.
-/
def adjunction [HasWeakSheafify J D] [HasSheafCompose J F] (adj : G ⊣ F) :
    composeAndSheafify J G ⊣ sheafCompose J F :=
  Adjunction.restrictFullyFaithful ((adj.whiskerRight Cᵒᵖ).comp (sheafificationAdjunction J D))
    (fullyFaithfulSheafToPresheaf J E) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Sheaf.adjunction_unit_app_hom** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Sheaf`。
形式化陈述：adjunction_unit_app_hom [HasWeakSheafify J D] [HasSheafCompose J F] (adj :
 G ⊣ F) (X : Sheaf J E) : ((adjunction J adj).unit.app X).hom = (adj.whiskerRigh
t Cᵒᵖ).unit.app _ ≫ whiskerRight (toSheafify J (X.obj ⋙ G)) F
参数：adj : G ⊣ F；X : Sheaf J E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.Adjunction.map_restrictFullyFaithful_unit_app`：map_restri
ctFullyFaithful_unit_app (X : C) : iC.map ((adj.restrictFullyFaithful hiC hiD co
mm1 comm2).unit.app X) = adj.unit.app (iC.obj X) ≫…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.Adjunction.comp_unit_app`：comp_unit_app (X : C) : dsimp% 
(adj₁.comp adj₂).unit.app X = adj₁.unit.app X ≫ G.map (adj₂.unit.app (F.obj X))
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.whiskerRight_id'`：whiskerRight_id' {G : C ⥤ D} (F
 : D ⥤ E) : whiskerRight (𝟙 G) F = 𝟙 (G.comp F)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma adjunction_unit_app_hom [HasWeakSheafify J D] [HasSheafCompose J F] (adj : G ⊣ F)
    (X : Sheaf J E) : ((adjunction J adj).unit.app X).hom =
      (adj.whiskerRight Cᵒᵖ).unit.app _ ≫ whiskerRight (toSheafify J (X.obj ⋙ G)) F := by
  change (sheafToPresheaf _ _).map ((adjunction J adj).unit.app X) = _
  simp only [Functor.id_obj, Functor.comp_obj, whiskeringRight_obj_obj, adjunction,
    Adjunction.map_restrictFullyFaithful_unit_app, Adjunction.comp_unit_app,
    sheafificationAdjunction_unit_app, whiskeringRight_obj_map, Iso.refl_hom, NatTrans.id_app,
    Functor.comp_map, Functor.map_id, whiskerRight_id', Category.comp_id]
  rfl

@[deprecated (since := "2026-03-05")]
alias adjunction_unit_app_val := adjunction_unit_app_hom

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Sheaf.adjunction_counit_app_hom** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Sheaf`。
形式化陈述：adjunction_counit_app_hom [HasWeakSheafify J D] [HasSheafCompose J F] (adj
 : G ⊣ F) (Y : Sheaf J D) : ((adjunction J adj).counit.app Y).hom = sheafifyLift
 J (((adj.whiskerRight Cᵒᵖ).counit.app Y.obj)) Y.property
参数：adj : G ⊣ F；Y : Sheaf J D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用引理 `CategoryTheory.Adjunction.map_restrictFullyFaithful_counit_app`：map_rest
rictFullyFaithful_counit_app (X : D) : iD.map ((adj.restrictFullyFaithful hiC hi
D comm1 comm2).counit.app X) = comm1.inv.app (R.obj …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.whiskerRight_id'`：whiskerRight_id' {G : C ⥤ D} (F
 : D ⥤ E) : whiskerRight (𝟙 G) F = 𝟙 (G.comp F)
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用引理 `CategoryTheory.Adjunction.comp_counit_app`：comp_counit_app (X : E) : dsi
mp% (adj₁.comp adj₂).counit.app X = H.map (adj₁.counit.app (I.obj X)) ≫ adj₂.cou
nit.app X
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.sheafificationAdjunction_counit_app_val`：sheafificationAd
junction_counit_app_val (P : Sheaf J D) : ((sheafificationAdjunction J D).counit
.app P).hom = sheafifyLift J (𝟙 P.obj) P.pro…
· 使用定理 `CategoryTheory.sheafifyMap_sheafifyLift`：sheafifyMap_sheafifyLift {P Q R
 : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) (hR : Presheaf.IsSheaf J R) : sheafifyMap J 
η ≫ sheafifyLift J γ hR = she…
· 使用定理 `CategoryTheory.sheafifyLift.congr_simp`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C) {D : Typ
e u_1}   [inst_1 : CategoryT…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma adjunction_counit_app_hom [HasWeakSheafify J D] [HasSheafCompose J F] (adj : G ⊣ F)
    (Y : Sheaf J D) : ((adjunction J adj).counit.app Y).hom =
      sheafifyLift J (((adj.whiskerRight Cᵒᵖ).counit.app Y.obj)) Y.property :=
  ((sheafToPresheaf _ _).congr_map
    (Adjunction.map_restrictFullyFaithful_counit_app _ _ (Functor.FullyFaithful.id _)
      (L := composeAndSheafify J G) (R := sheafCompose J F) _ _ Y)).trans (by cat_disch)

@[deprecated (since := "2026-03-05")]
alias adjunction_counit_app_val := adjunction_counit_app_hom
/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasWeakSheafify J D] [F.IsRightAdjoint] : (sheafCompose J F).IsRightAdjoint :=
  (adjunction J (Adjunction.ofIsRightAdjoint F)).isRightAdjoint
/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasWeakSheafify J D] [G.IsLeftAdjoint] : (composeAndSheafify J G).IsLeftAdjoint :=
  (adjunction J (Adjunction.ofIsLeftAdjoint G)).isLeftAdjoint

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Sheaf.preservesSheafification_of_adjunction** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Sheaf`。
形式化陈述：preservesSheafification_of_adjunction (adj : G ⊣ F) : J.PreservesSheafific
ation G where le P Q f hf
参数：adj : G ⊣ F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.isRightAdjoint`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.inverseImage_iff`：inverseImage_iff (P : 
MorphismProperty D) (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) : P.inverseImage F f ↔ P (
F.map f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.comp_bijective`：comp_bijective (f : α -> β) (e : β ≃ γ) : Bijectiv
e (e ∘ f) ↔ Bijective f
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `CategoryTheory.hasSheafCompose_of_preservesMulticospan`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} A]   {B : Type u₃} [ins…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `CategoryTheory.NatTrans.comp_app`：comp_app {F G H : C ⥤ D} (α : F ⟶ G) (
β : G ⟶ H) (X : C) : (α ≫ β).app X = α.app X ≫ β.app X
· 使用定理 `CategoryTheory.Adjunction.homEquiv_naturality_left`：homEquiv_naturality_
left (f : X' ⟶ X) (g : F.obj X ⟶ Y) : (adj.homEquiv X' Y) (F.map f ≫ g) = f ≫ (a
dj.homEquiv X Y) g
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
lemma preservesSheafification_of_adjunction (adj : G ⊣ F) :
    J.PreservesSheafification G where
  le P Q f hf := by
    have := adj.isRightAdjoint
    rw [MorphismProperty.inverseImage_iff]
    dsimp
    intro R hR
    rw [← ((adj.whiskerRight Cᵒᵖ).homEquiv P R).comp_bijective]
    convert!
      (((adj.whiskerRight Cᵒᵖ).homEquiv Q R).trans
          (hf.homEquiv (R ⋙ F) ((sheafCompose J F).obj ⟨R, hR⟩).property)).bijective
    ext g X
    -- The rest of this proof was
    -- `dsimp [Adjunction.whiskerRight, Adjunction.mkOfUnitCounit]; simp` before https://github.com/leanprover-community/mathlib4/pull/16317.
    dsimp
    rw [← NatTrans.comp_app]
    congr
    exact Adjunction.homEquiv_naturality_left _ _ _
/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [G.IsLeftAdjoint] : J.PreservesSheafification G :=
  preservesSheafification_of_adjunction J (Adjunction.ofIsLeftAdjoint G)

section ForgetToType

variable [HasWeakSheafify J D] {FD : D → D → Type*} {CD : D → Type (max u₁ v₁)}
    [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD] [HasSheafCompose J (forget D)]

/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [(forget D).IsRightAdjoint] :
    (sheafForget.{_, _, _, _, _, max u₁ v₁} (D := D) J).IsRightAdjoint := by infer_instance

end ForgetToType

end

end Sheaf

end CategoryTheory

