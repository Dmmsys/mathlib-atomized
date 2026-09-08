/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.FullSubcategory

/-!

# Limits and colimits of sheaves

## Limits

We prove that the forgetful functor from `Sheaf J D` to presheaves creates limits.
If the target category `D` has limits (of a certain shape),
this then implies that `Sheaf J D` has limits of the same shape and that the forgetful
functor preserves these limits.

## Colimits

Given a diagram `F : K ⥤ Sheaf J D` of sheaves, and a colimit cocone on the level of presheaves,
we show that the cocone obtained by sheafifying the cocone point is a colimit cocone of sheaves.

This allows us to show that `Sheaf J D` has colimits (of a certain shape) as soon as `D` does.

-/

@[expose] public section


namespace CategoryTheory

namespace Sheaf

open CategoryTheory.Limits

open Opposite

universe w w' v u z z' u₁ u₂

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {D : Type w} [Category.{w'} D]
variable {K : Type z} [Category.{z'} K]

section Limits

noncomputable section

section

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An auxiliary definition to be used below.

Whenever `E` is a cone of shape `K` of sheaves, and `S` is the multifork associated to a
covering `W` of an object `X`, with respect to the cone point `E.X`, this provides a cone of
shape `K` of objects in `D`, with cone point `S.X`.

See `isLimitMultiforkOfIsLimit` for more on how this definition is used.
-/
/-
**CategoryTheory.Sheaf.multiforkEvaluationCone** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Sheaf`。
形式化陈述：multiforkEvaluationCone (F : K ⥤ Sheaf J D) (E : Cone (F ⋙ sheafToPresheaf
 J D)) (X : C) (W : J.Cover X) (S : Multifork (W.index E.pt)) : Cone (F ⋙ sheafT
oPresheaf J D ⋙ (evaluation Cᵒᵖ D).obj (op X)) where pt
参数：F : K ⥤ Sheaf J D；E : Cone (F ⋙ sheafToPresheaf J D)；X : C；W : J.Cover X；S : 
Multifork (W.index E.pt)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary definition to be used below.

Whenever `E` is a cone of shape `K` of sheaves, and `S` is the multifork associa
ted to a
covering `W` of an object `X`, with respect to the cone point `E.X`, this provid
es a cone of
shape `K` of objects in `D`, with cone point `S.X`.

See `isLimitMultiforkOfIsLimit` for more on how this definition is used.
-/
def multiforkEvaluationCone (F : K ⥤ Sheaf J D) (E : Cone (F ⋙ sheafToPresheaf J D)) (X : C)
    (W : J.Cover X) (S : Multifork (W.index E.pt)) :
    Cone (F ⋙ sheafToPresheaf J D ⋙ (evaluation Cᵒᵖ D).obj (op X)) where
  pt := S.pt
  π :=
    { app := fun k => (Presheaf.isLimitOfIsSheaf J (F.obj k).1 W (F.obj k).2).lift <|
        Multifork.ofι _ S.pt (fun i => S.ι i ≫ (E.π.app k).app (op i.Y))
          (by
            intro i
            simp only [Category.assoc]
            erw [← (E.π.app k).naturality, ← (E.π.app k).naturality]
            dsimp
            simp only [← Category.assoc]
            congr 1
            apply S.condition)
      naturality := by
        intro i j f
        dsimp [Presheaf.isLimitOfIsSheaf]
        rw [Category.id_comp]
        apply Presheaf.IsSheaf.hom_ext (F.obj j).2 W
        intro ii
        rw [Presheaf.IsSheaf.amalgamate_map, Category.assoc, ← (F.map f).hom.naturality, ←
          Category.assoc, Presheaf.IsSheaf.amalgamate_map]
        erw [Category.assoc, ← E.w f]
        cat_disch }

variable [HasLimitsOfShape K D]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `E` is a cone of shape `K` of sheaves, which is a limit on the level of presheaves,
this definition shows that the limit presheaf satisfies the multifork variant of the sheaf
condition, at a given covering `W`.

This is used below in `isSheaf_of_isLimit` to show that the limit presheaf is indeed a sheaf.
-/
/-
**CategoryTheory.Sheaf.isLimitMultiforkOfIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Sheaf`。
形式化陈述：isLimitMultiforkOfIsLimit (F : K ⥤ Sheaf J D) (E : Cone (F ⋙ sheafToPreshe
af J D)) (hE : IsLimit E) (X : C) (W : J.Cover X) : IsLimit (W.multifork E.pt)
参数：F : K ⥤ Sheaf J D；E : Cone (F ⋙ sheafToPresheaf J D)；hE : IsLimit E；X : C；W :
 J.Cover X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `E` is a cone of shape `K` of sheaves, which is a limit on the level of presh
eaves,
this definition shows that the limit presheaf satisfies the multifork variant of
 the sheaf
condition, at a given covering `W`.

This is used below in `isSheaf_of_isLimit` to show that the limit presheaf is in
deed a sheaf.
-/
def isLimitMultiforkOfIsLimit (F : K ⥤ Sheaf J D) (E : Cone (F ⋙ sheafToPresheaf J D))
    (hE : IsLimit E) (X : C) (W : J.Cover X) : IsLimit (W.multifork E.pt) :=
  Multifork.IsLimit.mk _
    (fun S => (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X)) hE).lift <|
      multiforkEvaluationCone F E X W S)
    (by
      intro S i
      apply (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op i.Y)) hE).hom_ext
      intro k
      dsimp [Multifork.ofι]
      erw [Category.assoc, (E.π.app k).naturality]
      dsimp
      rw [← Category.assoc]
      erw [(isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X)) hE).fac
        (multiforkEvaluationCone F E X W S)]
      dsimp [multiforkEvaluationCone, Presheaf.isLimitOfIsSheaf]
      rw [Presheaf.IsSheaf.amalgamate_map])
    (by
      intro S m hm
      apply (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X)) hE).hom_ext
      intro k
      dsimp
      erw [(isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X)) hE).fac]
      apply Presheaf.IsSheaf.hom_ext (F.obj k).2 W
      intro i
      dsimp only [multiforkEvaluationCone, Presheaf.isLimitOfIsSheaf]
      rw [(F.obj k).property.amalgamate_map]
      dsimp [Multifork.ofι]
      change _ = S.ι i ≫ _
      erw [← hm, Category.assoc, ← (E.π.app k).naturality, Category.assoc]
      rfl)

/-- If `E` is a cone which is a limit on the level of presheaves,
then the limit presheaf is again a sheaf.

This is used to show that the forgetful functor from sheaves to presheaves creates limits.
-/
/-
**CategoryTheory.Sheaf.isSheaf_of_isLimit** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Sheaf`。
形式化陈述：isSheaf_of_isLimit (F : K ⥤ Sheaf J D) (E : Cone (F ⋙ sheafToPresheaf J D)
) (hE : IsLimit E) : Presheaf.IsSheaf J E.pt
参数：F : K ⥤ Sheaf J D；E : Cone (F ⋙ sheafToPresheaf J D)；hE : IsLimit E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presheaf.isSheaf_iff_multifork`：isSheaf_iff_multifork : I
sSheaf J P ↔ forall (X : C) (S : J.Cover X), Nonempty (IsLimit (S.multifork P))

--- 原说明 ---
If `E` is a cone which is a limit on the level of presheaves,
then the limit presheaf is again a sheaf.

This is used to show that the forgetful functor from sheaves to presheaves creat
es limits.
-/
theorem isSheaf_of_isLimit (F : K ⥤ Sheaf J D) (E : Cone (F ⋙ sheafToPresheaf J D))
    (hE : IsLimit E) : Presheaf.IsSheaf J E.pt := by
  rw [Presheaf.isSheaf_iff_multifork]
  intro X S
  exact ⟨isLimitMultiforkOfIsLimit _ _ hE _ _⟩
/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ObjectProperty.IsClosedUnderLimitsOfShape (Presheaf.IsSheaf J (A := D)) K where
  limitsOfShape_le := by
    rintro P ⟨h⟩
    let F : K ⥤ Sheaf J D := ObjectProperty.lift _ h.diag h.prop_diag_obj
    exact isSheaf_of_isLimit F _ h.isLimit
/-
**CategoryTheory.Sheaf.createsLimitsOfShape** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Sheaf`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Cate
goryTheory.GrothendieckTopology C} →       {D : Type w} →         [inst_1 : Cate
goryTheory.Category.{w', w} D] →           {K : Type z} →             [inst_2 : 
CategoryTheory.Category.{z', z} K] →               [CategoryTheory.Limits.HasLim
itsOfShape K D] →                 CategoryTheory.CreatesLimitsOfShape K (Categor
yTheory.sheafToPresheaf J D)
参数：CategoryTheory.sheafToPresheaf J D。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sheaf.instIsClosedUnderLimitsOfShapeFunctorOppositeIsShea
f`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.
GrothendieckTopology C} {D : Type w}   [inst_1 : CategoryTheory…
-/
instance createsLimitsOfShape : CreatesLimitsOfShape K (sheafToPresheaf J D) where
/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasLimitsOfShape K (Sheaf J D) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (sheafToPresheaf J D)
/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteProducts D] : HasFiniteProducts (Sheaf J D) :=
  ⟨inferInstance⟩
/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteLimits D] : HasFiniteLimits (Sheaf J D) :=
  ⟨fun _ ↦ inferInstance⟩

end

/-
**CategoryTheory.Sheaf.createsLimits** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.S
heaf`。
形式化陈述：createsLimits [HasLimitsOfSize.{u₁, u₂} D] : CreatesLimitsOfSize.{u₁, u₂} 
(sheafToPresheaf J D)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance createsLimits [HasLimitsOfSize.{u₁, u₂} D] :
    CreatesLimitsOfSize.{u₁, u₂} (sheafToPresheaf J D) :=
  ⟨createsLimitsOfShape⟩
/-
**CategoryTheory.Sheaf.hasLimitsOfSize** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.Sheaf`。
形式化陈述：hasLimitsOfSize [HasLimitsOfSize.{u₁, u₂} D] : HasLimitsOfSize.{u₁, u₂} (S
heaf J D)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasLimits_of_hasLimits_createsLimits`：hasLimits_of_hasLim
its_createsLimits (F : C ⥤ D) [HasLimitsOfSize.{w, w'} D] [CreatesLimitsOfSize.{
w, w'} F] : HasLimitsOfSize.{w, w'} C
-/
instance hasLimitsOfSize [HasLimitsOfSize.{u₁, u₂} D] : HasLimitsOfSize.{u₁, u₂} (Sheaf J D) :=
  hasLimits_of_hasLimits_createsLimits (sheafToPresheaf J D)
/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteLimits D] :
    PreservesFiniteLimits (sheafToPresheaf J D) where
  preservesFiniteLimits _ _ _ := inferInstance
/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {D : Type w} [Category.{max v u} D] [HasLimits D] :
    HasLimits (Sheaf J D) := inferInstance

end

end Limits

section Colimits

variable [HasWeakSheafify J D]

/-- Construct a cocone by sheafifying a cocone point of a cocone `E` of presheaves
over a functor which factors through sheaves.
In `isColimitSheafifyCocone`, we show that this is a colimit cocone when `E` is a colimit. -/
/-
**CategoryTheory.Sheaf.sheafifyCocone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Sheaf`。
形式化陈述：sheafifyCocone {F : K ⥤ Sheaf J D} (E : Cocone (F ⋙ sheafToPresheaf J D)) 
: Cocone F
参数：E : Cocone (F ⋙ sheafToPresheaf J D)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a cocone by sheafifying a cocone point of a cocone `E` of presheaves
over a functor which factors through sheaves.
In `isColimitSheafifyCocone`, we show that this is a colimit cocone when `E` is 
a colimit.
-/
noncomputable def sheafifyCocone {F : K ⥤ Sheaf J D}
    (E : Cocone (F ⋙ sheafToPresheaf J D)) : Cocone F :=
  (Cocone.precompose
    (Functor.isoWhiskerLeft F (asIso (sheafificationAdjunction J D).counit).symm).hom).obj
    ((presheafToSheaf J D).mapCocone E)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Sheaf.sheafifyCocone_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sheafifyCocone_ι_app_val
    {F : K ⥤ Sheaf J D} (E : Cocone (F ⋙ sheafToPresheaf J D)) (k : K) :
    ((Sheaf.sheafifyCocone E).ι.app k).hom =
      E.ι.app k ≫ CategoryTheory.toSheafify J E.pt := by
  rw [← cancel_epi ((sheafToPresheaf _ _).map
    ((sheafificationAdjunction J D).counit.app (F.obj k)))]
  dsimp [sheafifyCocone]
  rw [← ObjectProperty.FullSubcategory.comp_hom_assoc,
    ← NatTrans.comp_app, IsIso.hom_inv_id, NatTrans.id_app]
  dsimp
  rw [Category.id_comp, toSheafify_naturality, sheafificationAdjunction_counit_app_val,
    sheafifyLift_id_toSheafify_assoc]

/-- If `E` is a colimit cocone of presheaves, over a diagram factoring through sheaves,
then `sheafifyCocone E` is a colimit cocone. -/
/-
**CategoryTheory.Sheaf.isColimitSheafifyCocone** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Sheaf`。
形式化陈述：isColimitSheafifyCocone {F : K ⥤ Sheaf J D} (E : Cocone (F ⋙ sheafToPreshe
af J D)) (hE : IsColimit E) : IsColimit (sheafifyCocone E)
参数：E : Cocone (F ⋙ sheafToPresheaf J D)；hE : IsColimit E。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `E` is a colimit cocone of presheaves, over a diagram factoring through sheav
es,
then `sheafifyCocone E` is a colimit cocone.
-/
noncomputable def isColimitSheafifyCocone {F : K ⥤ Sheaf J D}
    (E : Cocone (F ⋙ sheafToPresheaf J D)) (hE : IsColimit E) : IsColimit (sheafifyCocone E) :=
  (IsColimit.precomposeHomEquiv _ ((presheafToSheaf J D).mapCocone E)).symm
    (isColimitOfPreserves _ hE)
/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasColimitsOfShape K D] : HasColimitsOfShape K (Sheaf J D) :=
  ⟨fun _ => HasColimit.mk
    ⟨sheafifyCocone (colimit.cocone _), isColimitSheafifyCocone _ (colimit.isColimit _)⟩⟩
/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteCoproducts D] : HasFiniteCoproducts (Sheaf J D) :=
  ⟨inferInstance⟩
/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteColimits D] : HasFiniteColimits (Sheaf J D) :=
  ⟨fun _ ↦ inferInstance⟩
/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasColimitsOfSize.{u₁, u₂} D] : HasColimitsOfSize.{u₁, u₂} (Sheaf J D) :=
  ⟨inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/--
If every cocone on a diagram of sheaves which is a colimit on the level of presheaves satisfies
the condition that the cocone point is a sheaf, then the functor from sheaves to presheaves
creates colimits of the diagram.
Note: this almost never holds in sheaf categories in general, but it does for the extensive
topology (see `Mathlib/CategoryTheory/Sites/Coherent/ExtensiveColimits.lean`).
-/
@[instance_reducible]
/-
**CategoryTheory.Sheaf.createsColimitOfIsSheaf** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Sheaf`。
形式化陈述：createsColimitOfIsSheaf (F : K ⥤ Sheaf J D) (h : forall (c : Cocone (F ⋙ s
heafToPresheaf J D)) (_ : IsColimit c), Presheaf.IsSheaf J c.pt) : CreatesColimi
t F (sheafToPresheaf J D)
参数：F : K ⥤ Sheaf J D；h : forall (c : Cocone (F ⋙ sheafToPresheaf J D)) (_ : IsCo
limit c), Presheaf.IsSheaf J c.pt。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If every cocone on a diagram of sheaves which is a colimit on the level of presh
eaves satisfies
the condition that the cocone point is a sheaf, then the functor from sheaves to
 presheaves
creates colimits of the diagram.
Note: this almost never holds in sheaf categories in general, but it does for th
e extensive
topology (see `Mathlib/CategoryTheory/Sites/Coherent/ExtensiveColimits.lean`).
-/
def createsColimitOfIsSheaf (F : K ⥤ Sheaf J D)
    (h : ∀ (c : Cocone (F ⋙ sheafToPresheaf J D)) (_ : IsColimit c), Presheaf.IsSheaf J c.pt) :
    CreatesColimit F (sheafToPresheaf J D) :=
  createsColimitOfReflectsIso fun E hE =>
    { liftedCocone := ⟨⟨E.pt, h _ hE⟩,
        ⟨fun _ => ⟨E.ι.app _⟩, fun _ _ _ => Sheaf.hom_ext <| E.ι.naturality _⟩⟩
      validLift := Cocone.ext (eqToIso rfl) fun j => by simp
      makesColimit :=
        { desc := fun S => ⟨hE.desc ((sheafToPresheaf J D).mapCocone S)⟩
          fac := fun S j => by ext1; dsimp; rw [hE.fac]; rfl
          uniq := fun S m hm => by
            ext1
            exact hE.uniq ((sheafToPresheaf J D).mapCocone S) m.hom fun j =>
              (ObjectProperty.ι _).congr_map (hm j) } }

variable {D : Type w} [Category.{max v u} D]
/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [HasLimits D] : HasLimits (Sheaf J D) := inferInstance

end Colimits

end Sheaf

end CategoryTheory

