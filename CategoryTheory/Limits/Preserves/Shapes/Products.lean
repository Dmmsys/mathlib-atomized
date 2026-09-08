/-
Copyright (c) 2020 Kim Morrison, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Preserving products

Constructions to relate the notions of preserving products and reflecting products
to concrete fans.

In particular, we show that `piComparison G f` is an isomorphism iff `G` preserves
the limit of `f`.
-/

@[expose] public section


noncomputable section

universe w v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (G : C ⥤ D)

namespace CategoryTheory.Limits

variable {J : Type w} (f : J → C)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The map of a fan is a limit iff the fan consisting of the mapped morphisms is a limit. This
essentially lets us commute `Fan.mk` with `Functor.mapCone`.
-/
/-
**CategoryTheory.Limits.isLimitMapConeFanMkEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：isLimitMapConeFanMkEquiv {P : C} (g : forall j, P ⟶ f j) : IsLimit (Functo
r.mapCone G (Fan.mk P g)) ≃ IsLimit (Fan.mk _ fun j => G.map (g j) : Fan fun j =
> G.obj (f j))
参数：g : forall j, P ⟶ f j。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The map of a fan is a limit iff the fan consisting of the mapped morphisms is a 
limit. This
essentially lets us commute `Fan.mk` with `Functor.mapCone`.
-/
def isLimitMapConeFanMkEquiv {P : C} (g : ∀ j, P ⟶ f j) :
    IsLimit (Functor.mapCone G (Fan.mk P g)) ≃
      IsLimit (Fan.mk _ fun j => G.map (g j) : Fan fun j => G.obj (f j)) := by
  refine (IsLimit.postcomposeHomEquiv ?_ _).symm.trans (IsLimit.equivIsoLimit ?_)
  · exact Discrete.natIso fun j => Iso.refl (G.obj (f j.as))
  exact Cone.ext (Iso.refl _) fun j ↦ by dsimp; cases j; simp

/-- The property of preserving products expressed in terms of fans. -/
/-
**CategoryTheory.Limits.isLimitFanMkObjOfIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：isLimitFanMkObjOfIsLimit [PreservesLimit (Discrete.functor f) G] {P : C} (
g : forall j, P ⟶ f j) (t : IsLimit (Fan.mk _ g)) : IsLimit (Fan.mk (G.obj P) fu
n j => G.map (g j) : Fan fun j => G.obj (f j))
参数：Discrete.functor f；g : forall j, P ⟶ f j；t : IsLimit (Fan.mk _ g)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of preserving products expressed in terms of fans.
-/
def isLimitFanMkObjOfIsLimit [PreservesLimit (Discrete.functor f) G] {P : C} (g : ∀ j, P ⟶ f j)
    (t : IsLimit (Fan.mk _ g)) :
    IsLimit (Fan.mk (G.obj P) fun j => G.map (g j) : Fan fun j => G.obj (f j)) :=
  isLimitMapConeFanMkEquiv _ _ _ (isLimitOfPreserves G t)

/-- The property of reflecting products expressed in terms of fans. -/
/-
**CategoryTheory.Limits.isLimitOfIsLimitFanMkObj** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：isLimitOfIsLimitFanMkObj [ReflectsLimit (Discrete.functor f) G] {P : C} (g
 : forall j, P ⟶ f j) (t : IsLimit (Fan.mk _ fun j => G.map (g j) : Fan fun j =>
 G.obj (f j))) : IsLimit (Fan.mk P g)
参数：Discrete.functor f；g : forall j, P ⟶ f j；t : IsLimit (Fan.mk _ fun j => G.map
 (g j) : Fan fun j => G.obj (f j))。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The property of reflecting products expressed in terms of fans.
-/
def isLimitOfIsLimitFanMkObj [ReflectsLimit (Discrete.functor f) G] {P : C} (g : ∀ j, P ⟶ f j)
    (t : IsLimit (Fan.mk _ fun j => G.map (g j) : Fan fun j => G.obj (f j))) :
    IsLimit (Fan.mk P g) :=
  isLimitOfReflects G ((isLimitMapConeFanMkEquiv _ _ _).symm t)

section

variable [HasProduct f]

/--
If `G` preserves products and `C` has them, then the fan constructed of the mapped projection of a
product is a limit.
-/
/-
**CategoryTheory.Limits.isLimitOfHasProductOfPreservesLimit** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Limits`。
形式化陈述：isLimitOfHasProductOfPreservesLimit [PreservesLimit (Discrete.functor f) G
] : IsLimit (Fan.mk _ fun j : J => G.map (Pi.π f j) : Fan fun j => G.obj (f j))
参数：Discrete.functor f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` preserves products and `C` has them, then the fan constructed of the mapp
ed projection of a
product is a limit.
-/
def isLimitOfHasProductOfPreservesLimit [PreservesLimit (Discrete.functor f) G] :
    IsLimit (Fan.mk _ fun j : J => G.map (Pi.π f j) : Fan fun j => G.obj (f j)) :=
  isLimitFanMkObjOfIsLimit G f _ (productIsProduct _)

variable [HasProduct fun j : J => G.obj (f j)]

/-- If `pi_comparison G f` is an isomorphism, then `G` preserves the limit of `f`. -/
/-
**CategoryTheory.Limits.PreservesProduct.of_iso_comparison** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits.PreservesProduct`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheory.Functor C D)
 {J : Type w} (f : J → C) [inst_2 : CategoryTheory.Limits.HasProduct f]   [inst_
3 : CategoryTheory.Limits.HasProduct fun j => G.obj (f j)]   [i : CategoryTheory
.IsIso (CategoryTheory.Limits.piComparison G f)],   CategoryTheory.Limits.Preser
vesLimit (CategoryTheory.Discrete.functor f) G
参数：G : CategoryTheory.Functor C D；f : J → C；f j；CategoryTheory.Limits.piComparis
on G f；CategoryTheory.Discrete.functor f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `pi_comparison G f` is an isomorphism, then `G` preserves the limit of `f`.
-/
lemma PreservesProduct.of_iso_comparison [i : IsIso (piComparison G f)] :
    PreservesLimit (Discrete.functor f) G := by
  apply preservesLimit_of_preserves_limit_cone (productIsProduct f)
  apply (isLimitMapConeFanMkEquiv _ _ _).symm _
  exact @IsLimit.ofPointIso _ _ _ _ _ _ _
    (limit.isLimit (Discrete.functor fun j : J => G.obj (f j))) i

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.inv_piComparison_comp_map_** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_piComparison_comp_map_π [IsIso (piComparison G f)] (j : J) :
     inv (piComparison G f) ≫ G.map (Pi.π _ j) =
      Pi.π (fun x ↦ (G.obj (f x))) j := by
  simp only [IsIso.inv_comp_eq, piComparison_comp_π]

variable [PreservesLimit (Discrete.functor f) G]

/--
If `G` preserves limits, we have an isomorphism from the image of a product to the product of the
images.
-/
/-
**CategoryTheory.Limits.PreservesProduct.iso** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.PreservesProduct`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (G : Cat
egoryTheory.Functor C D) →           {J : Type w} →             (f : J → C) →   
            [inst_2 : CategoryTheory.Limits.HasProduct f] →                 [ins
t_3 : CategoryTheory.Limits.HasProduct fun j => G.obj (f j)] →                  
 [CategoryTheory.Limits.PreservesLimit (CategoryTheory.Discrete.functor f) G] → 
                    G.obj (∏ᶜ f) ≅ ∏ᶜ fun j => G.obj (f j)
参数：G : CategoryTheory.Functor C D；f : J → C；f j；CategoryTheory.Discrete.functor 
f；∏ᶜ f；f j。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` preserves limits, we have an isomorphism from the image of a product to t
he product of the
images.
-/
def PreservesProduct.iso : G.obj (∏ᶜ f) ≅ ∏ᶜ fun j => G.obj (f j) :=
  IsLimit.conePointUniqueUpToIso (isLimitOfHasProductOfPreservesLimit G f) (limit.isLimit _)

@[simp]
/-
**CategoryTheory.Limits.PreservesProduct.iso_hom** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits.PreservesProduct`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheory.Functor C D)
 {J : Type w} (f : J → C) [inst_2 : CategoryTheory.Limits.HasProduct f]   [inst_
3 : CategoryTheory.Limits.HasProduct fun j => G.obj (f j)]   [inst_4 : CategoryT
heory.Limits.PreservesLimit (CategoryTheory.Discrete.functor f) G],   (CategoryT
heory.Limits.PreservesProduct.iso G f).hom = CategoryTheory.Limits.piComparison 
G f
参数：G : CategoryTheory.Functor C D；f : J → C；f j；CategoryTheory.Discrete.functor 
f；CategoryTheory.Limits.PreservesProduct.iso G f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PreservesProduct.iso_hom : (PreservesProduct.iso G f).hom = piComparison G f :=
  rfl
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (piComparison G f) := by
  rw [← PreservesProduct.iso_hom]
  infer_instance
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {I : Type*} [Category* I] [IsGroupoid I] (F : C ⥤ D) [PreservesLimitsOfShape I F] :
    PreservesLimitsOfShape Iᵒᵖ F :=
  letI : Groupoid I := Groupoid.ofIsGroupoid
  preservesLimitsOfShape_of_equiv (Groupoid.invEquivalence I) F

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The map of a cofan is a colimit iff the cofan consisting of the mapped morphisms is a colimit.
This essentially lets us commute `Cofan.mk` with `Functor.mapCocone`.
-/
/-
**CategoryTheory.Limits.isColimitMapCoconeCofanMkEquiv** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：isColimitMapCoconeCofanMkEquiv {P : C} (g : forall j, f j ⟶ P) : IsColimit
 (Functor.mapCocone G (Cofan.mk P g)) ≃ IsColimit (Cofan.mk _ fun j => G.map (g 
j) : Cofan fun j => G.obj (f j))
参数：g : forall j, f j ⟶ P。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The map of a cofan is a colimit iff the cofan consisting of the mapped morphisms
 is a colimit.
This essentially lets us commute `Cofan.mk` with `Functor.mapCocone`.
-/
def isColimitMapCoconeCofanMkEquiv {P : C} (g : ∀ j, f j ⟶ P) :
    IsColimit (Functor.mapCocone G (Cofan.mk P g)) ≃
      IsColimit (Cofan.mk _ fun j => G.map (g j) : Cofan fun j => G.obj (f j)) := by
  refine (IsColimit.precomposeHomEquiv ?_ _).symm.trans (IsColimit.equivIsoColimit ?_)
  · refine Discrete.natIso fun j => Iso.refl (G.obj (f j.as))
  refine Cocone.ext (Iso.refl _) fun j => by dsimp; cases j; simp

/-- The property of preserving coproducts expressed in terms of cofans. -/
/-
**CategoryTheory.Limits.isColimitCofanMkObjOfIsColimit** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：isColimitCofanMkObjOfIsColimit [PreservesColimit (Discrete.functor f) G] {
P : C} (g : forall j, f j ⟶ P) (t : IsColimit (Cofan.mk _ g)) : IsColimit (Cofan
.mk (G.obj P) fun j => G.map (g j) : Cofan fun j => G.obj (f j))
参数：Discrete.functor f；g : forall j, f j ⟶ P；t : IsColimit (Cofan.mk _ g)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of preserving coproducts expressed in terms of cofans.
-/
def isColimitCofanMkObjOfIsColimit [PreservesColimit (Discrete.functor f) G] {P : C}
    (g : ∀ j, f j ⟶ P) (t : IsColimit (Cofan.mk _ g)) :
    IsColimit (Cofan.mk (G.obj P) fun j => G.map (g j) : Cofan fun j => G.obj (f j)) :=
  isColimitMapCoconeCofanMkEquiv _ _ _ (isColimitOfPreserves G t)

/-- The property of reflecting coproducts expressed in terms of cofans. -/
/-
**CategoryTheory.Limits.isColimitOfIsColimitCofanMkObj** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：isColimitOfIsColimitCofanMkObj [ReflectsColimit (Discrete.functor f) G] {P
 : C} (g : forall j, f j ⟶ P) (t : IsColimit (Cofan.mk _ fun j => G.map (g j) : 
Cofan fun j => G.obj (f j))) : IsColimit (Cofan.mk P g)
参数：Discrete.functor f；g : forall j, f j ⟶ P；t : IsColimit (Cofan.mk _ fun j => G
.map (g j) : Cofan fun j => G.obj (f j))。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The property of reflecting coproducts expressed in terms of cofans.
-/
def isColimitOfIsColimitCofanMkObj [ReflectsColimit (Discrete.functor f) G] {P : C}
    (g : ∀ j, f j ⟶ P)
    (t : IsColimit (Cofan.mk _ fun j => G.map (g j) : Cofan fun j => G.obj (f j))) :
    IsColimit (Cofan.mk P g) :=
  isColimitOfReflects G ((isColimitMapCoconeCofanMkEquiv _ _ _).symm t)

section

variable [HasCoproduct f]

/-- If `G` preserves coproducts and `C` has them,
then the cofan constructed of the mapped inclusion of a coproduct is a colimit.
-/
/-
**CategoryTheory.Limits.isColimitOfHasCoproductOfPreservesColimit** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：isColimitOfHasCoproductOfPreservesColimit [PreservesColimit (Discrete.func
tor f) G] : IsColimit (Cofan.mk _ fun j : J => G.map (Sigma.ι f j) : Cofan fun j
 => G.obj (f j))
参数：Discrete.functor f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` preserves coproducts and `C` has them,
then the cofan constructed of the mapped inclusion of a coproduct is a colimit.
-/
def isColimitOfHasCoproductOfPreservesColimit [PreservesColimit (Discrete.functor f) G] :
    IsColimit (Cofan.mk _ fun j : J => G.map (Sigma.ι f j) : Cofan fun j => G.obj (f j)) :=
  isColimitCofanMkObjOfIsColimit G f _ (coproductIsCoproduct _)

variable [HasCoproduct fun j : J => G.obj (f j)]

/-- If `sigma_comparison G f` is an isomorphism, then `G` preserves the colimit of `f`. -/
/-
**CategoryTheory.Limits.PreservesCoproduct.of_iso_comparison** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits.PreservesCoproduct`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheory.Functor C D)
 {J : Type w} (f : J → C) [inst_2 : CategoryTheory.Limits.HasCoproduct f]   [ins
t_3 : CategoryTheory.Limits.HasCoproduct fun j => G.obj (f j)]   [i : CategoryTh
eory.IsIso (CategoryTheory.Limits.sigmaComparison G f)],   CategoryTheory.Limits
.PreservesColimit (CategoryTheory.Discrete.functor f) G
参数：G : CategoryTheory.Functor C D；f : J → C；f j；CategoryTheory.Limits.sigmaCompa
rison G f；CategoryTheory.Discrete.functor f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone`：pres
ervesColimit_of_preserves_colimit_cocone {F : C ⥤ D} {t : Cocone K} (h : IsColim
it t) (hF : IsColimit (F.mapCocone t)) : PreservesColimi…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `sigma_comparison G f` is an isomorphism, then `G` preserves the colimit of `
f`.
-/
lemma PreservesCoproduct.of_iso_comparison [i : IsIso (sigmaComparison G f)] :
    PreservesColimit (Discrete.functor f) G := by
  apply preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct f)
  apply (isColimitMapCoconeCofanMkEquiv _ _ _).symm _
  exact @IsColimit.ofPointIso _ _ _ _ _ _ _
    (colimit.isColimit (Discrete.functor fun j : J => G.obj (f j))) i

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.map_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_ι_comp_inv_sigmaComparison [IsIso (sigmaComparison G f)] (j : J) :
    G.map (Sigma.ι _ j) ≫ inv (sigmaComparison G f) =
      Sigma.ι (fun x ↦ (G.obj (f x))) j := by
  simp

variable [PreservesColimit (Discrete.functor f) G]

/-- If `G` preserves colimits,
we have an isomorphism from the image of a coproduct to the coproduct of the images.
-/
/-
**CategoryTheory.Limits.PreservesCoproduct.iso** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.PreservesCoproduct`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (G : Cat
egoryTheory.Functor C D) →           {J : Type w} →             (f : J → C) →   
            [inst_2 : CategoryTheory.Limits.HasCoproduct f] →                 [i
nst_3 : CategoryTheory.Limits.HasCoproduct fun j => G.obj (f j)] →              
     [CategoryTheory.Limits.PreservesColimit (CategoryTheory.Discrete.functor f)
 G] →                     G.obj (∐ f) ≅ ∐ fun j => G.obj (f j)
参数：G : CategoryTheory.Functor C D；f : J → C；f j；CategoryTheory.Discrete.functor 
f；∐ f；f j。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` preserves colimits,
we have an isomorphism from the image of a coproduct to the coproduct of the ima
ges.
-/
def PreservesCoproduct.iso : G.obj (∐ f) ≅ ∐ fun j => G.obj (f j) :=
  IsColimit.coconePointUniqueUpToIso (isColimitOfHasCoproductOfPreservesColimit G f)
    (colimit.isColimit _)

@[simp]
/-
**CategoryTheory.Limits.PreservesCoproduct.inv_hom** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.PreservesCoproduct`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheory.Functor C D)
 {J : Type w} (f : J → C) [inst_2 : CategoryTheory.Limits.HasCoproduct f]   [ins
t_3 : CategoryTheory.Limits.HasCoproduct fun j => G.obj (f j)]   [inst_4 : Categ
oryTheory.Limits.PreservesColimit (CategoryTheory.Discrete.functor f) G],   (Cat
egoryTheory.Limits.PreservesCoproduct.iso G f).inv = CategoryTheory.Limits.sigma
Comparison G f
参数：G : CategoryTheory.Functor C D；f : J → C；f j；CategoryTheory.Discrete.functor 
f；CategoryTheory.Limits.PreservesCoproduct.iso G f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PreservesCoproduct.inv_hom : (PreservesCoproduct.iso G f).inv = sigmaComparison G f := rfl
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (sigmaComparison G f) := by
  rw [← PreservesCoproduct.inv_hom]
  infer_instance

end

/-- If `F` preserves the limit of every `Discrete.functor f`, it preserves all limits of shape
`Discrete J`. -/
/-
**CategoryTheory.Limits.preservesLimitsOfShape_of_discrete** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesLimitsOfShape_of_discrete (F : C ⥤ D) [forall (f : J -> C), Prese
rvesLimit (Discrete.functor f) F] : PreservesLimitsOfShape (Discrete J) F where 
preservesLimit
参数：F : C ⥤ D；f : J -> C；Discrete.functor f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_iso_diagram`：preservesLimit_of_i
so_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesLimit K₁ F] : Pre
servesLimit K₂ F where preserves {c} t

--- 原说明 ---
If `F` preserves the limit of every `Discrete.functor f`, it preserves all limit
s of shape
`Discrete J`.
-/
lemma preservesLimitsOfShape_of_discrete (F : C ⥤ D)
    [∀ (f : J → C), PreservesLimit (Discrete.functor f) F] :
    PreservesLimitsOfShape (Discrete J) F where
  preservesLimit := preservesLimit_of_iso_diagram F (Discrete.natIsoFunctor).symm

/-- If `F` preserves the colimit of every `Discrete.functor f`, it preserves all colimits of shape
`Discrete J`. -/
/-
**CategoryTheory.Limits.preservesColimitsOfShape_of_discrete** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesColimitsOfShape_of_discrete (F : C ⥤ D) [forall (f : J -> C), Pre
servesColimit (Discrete.functor f) F] : PreservesColimitsOfShape (Discrete J) F 
where preservesColimit
参数：F : C ⥤ D；f : J -> C；Discrete.functor f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_iso_diagram`：preservesColimit_
of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesColimit K₁ F]
 : PreservesColimit K₂ F where preserves {c…

--- 原说明 ---
If `F` preserves the colimit of every `Discrete.functor f`, it preserves all col
imits of shape
`Discrete J`.
-/
lemma preservesColimitsOfShape_of_discrete (F : C ⥤ D)
    [∀ (f : J → C), PreservesColimit (Discrete.functor f) F] :
    PreservesColimitsOfShape (Discrete J) F where
  preservesColimit := preservesColimit_of_iso_diagram F (Discrete.natIsoFunctor).symm
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {I : Type w} (F : C ⥤ D) [PreservesColimitsOfShape (Discrete I) F] :
    PreservesColimitsOfShape (Discrete I)ᵒᵖ F :=
  preservesColimitsOfShape_of_equiv (Discrete.opposite I).symm F

end CategoryTheory.Limits

