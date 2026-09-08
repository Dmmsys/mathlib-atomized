/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct
public import Mathlib.CategoryTheory.Limits.Indization.FilteredColimits

/-!
# Ind-objects are closed under products

We show that if `C` admits products indexed by `α`, then `IsIndObject` is closed under taking
products in `Cᵒᵖ ⥤ Type v` indexed by `α`. This will imply that the functor `Ind C ⥤ Cᵒᵖ ⥤ Type v`
creates products indexed by `α` and that the functor `C ⥤ Ind C` preserves them.

## References
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Prop. 6.1.16(ii)
-/

public section

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {α : Type v}

/-
**CategoryTheory.Limits.isIndObject_pi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：isIndObject_pi (h : forall (g : α -> C), IsIndObject (∏ᶜ yoneda.obj ∘ g)) 
(f : α -> Cᵒᵖ ⥤ Type v) (hf : forall a, IsIndObject (f a)) : IsIndObject (∏ᶜ f)
参数：h : forall (g : α -> C), IsIndObject (∏ᶜ yoneda.obj ∘ g)；f : α -> Cᵒᵖ ⥤ Type 
v；hf : forall a, IsIndObject (f a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.Types.instHasProductsType`：CategoryTheory.Limits.H
asProducts (Type v)
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instIsIsoColimitPointwiseProductToProductColimitOf
IsIPCOfShapeOfIsFiltered`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1,
 u_1} C] {ι : Type u_2}   [inst_1 : CategoryTheory.Limits.HasProductsOfShape ι C
] [Cat…
· 使用定理 `CategoryTheory.Limits.instIsIPCOfShapeFunctorOfHasFilteredColimitsOfSize
`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (ι : Type u_1)   [ins
t_1 : CategoryTheory.Limits.HasProductsOfShape ι C] [CategoryT…
· 使用定理 `CategoryTheory.Limits.instIsIPCOfShapeOfIsIPCOfSmall`：∀ {C : Type u_1} [
inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.Has
Products C]   [inst_2 : CategoryTheory.Lim…
· 使用定理 `CategoryTheory.Limits.hasFilteredColimitsOfSize_of_hasColimitsOfSize`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.Ha
sColimitsOfSize.{w', w, v, u} C],   CategoryTheory.Limits.…
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfSize`：∀ [UnivLE.{v, u}], Catego
ryTheory.Limits.HasColimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `CategoryTheory.Limits.instIsIPCType`：CategoryTheory.Limits.IsIPC (Type u
)
· 使用定理 `CategoryTheory.Limits.IndObjectPresentation.instIsFilteredI`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {A : CategoryTheory.Functor Cᵒᵖ (T
ype v)}   (P : CategoryTheory.Limits.IndObjectPre…
· 使用定理 `CategoryTheory.Limits.IsIndObject.map`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {A B : CategoryTheory.Functor Cᵒᵖ (Type v)} (η : A ⟶ B) 
  [CategoryTheory.IsIso η],…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Limits.isIndObject_colimit`：isIndObject_colimit (I : Type
 v) [SmallCategory I] [IsFiltered I] (F : I ⥤ Cᵒᵖ ⥤ Type v) (hF : forall i, IsIn
dObject (F.obj i)) : IsIndObjec…
· 使用定理 `CategoryTheory.instIsFilteredForall`：∀ {α : Type w} {I : α → Type u₁} [i
nst : (i : α) → CategoryTheory.Category.{v₁, u₁} (I i)]   [∀ (i : α), CategoryTh
eory.IsFiltered (I i)], C…
-/
theorem isIndObject_pi (h : ∀ (g : α → C), IsIndObject (∏ᶜ yoneda.obj ∘ g))
    (f : α → Cᵒᵖ ⥤ Type v) (hf : ∀ a, IsIndObject (f a)) : IsIndObject (∏ᶜ f) := by
  let F := fun a => (hf a).presentation.F ⋙ yoneda
  suffices (∏ᶜ f ≅ colimit (pointwiseProduct F)) from
    (isIndObject_colimit _ _ (fun i => h _)).map this.inv
  refine Pi.mapIso (fun s => ?_) ≪≫ (asIso (colimitPointwiseProductToProductColimit F)).symm
  exact IsColimit.coconePointUniqueUpToIso (hf s).presentation.isColimit (colimit.isColimit _)
/-
**CategoryTheory.Limits.isIndObject_limit_of_discrete** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：isIndObject_limit_of_discrete (h : forall (g : α -> C), IsIndObject (∏ᶜ yo
neda.obj ∘ g)) (F : Discrete α ⥤ Cᵒᵖ ⥤ Type v) (hF : forall a, IsIndObject (F.ob
j a)) : IsIndObject (limit F)
参数：h : forall (g : α -> C), IsIndObject (∏ᶜ yoneda.obj ∘ g)；F : Discrete α ⥤ Cᵒᵖ
 ⥤ Type v；hF : forall a, IsIndObject (F.obj a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.IsIndObject.map`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {A B : CategoryTheory.Functor Cᵒᵖ (Type v)} (η : A ⟶ B) 
  [CategoryTheory.IsIso η],…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Limits.isIndObject_pi`：isIndObject_pi (h : forall (g : α 
-> C), IsIndObject (∏ᶜ yoneda.obj ∘ g)) (f : α -> Cᵒᵖ ⥤ Type v) (hf : forall a, 
IsIndObject (f a)) : IsInd…
-/
theorem isIndObject_limit_of_discrete (h : ∀ (g : α → C), IsIndObject (∏ᶜ yoneda.obj ∘ g))
    (F : Discrete α ⥤ Cᵒᵖ ⥤ Type v) (hF : ∀ a, IsIndObject (F.obj a)) : IsIndObject (limit F) :=
  IsIndObject.map (Pi.isoLimit _).hom (isIndObject_pi h _ (fun a => hF ⟨a⟩))
/-
**CategoryTheory.Limits.isIndObject_limit_of_discrete_of_hasLimitsOfShape** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：isIndObject_limit_of_discrete_of_hasLimitsOfShape [HasLimitsOfShape (Discr
ete α) C] (F : Discrete α ⥤ Cᵒᵖ ⥤ Type v) (hF : forall a, IsIndObject (F.obj a))
 : IsIndObject (limit F)
参数：Discrete α；F : Discrete α ⥤ Cᵒᵖ ⥤ Type v；hF : forall a, IsIndObject (F.obj a)
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.isIndObject_limit_of_discrete`：isIndObject_limit_o
f_discrete (h : forall (g : α -> C), IsIndObject (∏ᶜ yoneda.obj ∘ g)) (F : Discr
ete α ⥤ Cᵒᵖ ⥤ Type v) (hF : forall a, IsI…
· 使用定理 `CategoryTheory.Limits.IsIndObject.map`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {A B : CategoryTheory.Functor Cᵒᵖ (Type v)} (η : A ⟶ B) 
  [CategoryTheory.IsIso η],…
· 使用定理 `CategoryTheory.Limits.instHasLimitCompOfPreservesLimit`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Limits.isIndObject_limit_comp_yoneda`：isIndObject_limit_c
omp_yoneda {J : Type u'} [Category.{v'} J] (F : J ⥤ C) [HasLimit F] : IsIndObjec
t (limit (F ⋙ yoneda))
-/
theorem isIndObject_limit_of_discrete_of_hasLimitsOfShape [HasLimitsOfShape (Discrete α) C]
    (F : Discrete α ⥤ Cᵒᵖ ⥤ Type v) (hF : ∀ a, IsIndObject (F.obj a)) : IsIndObject (limit F) :=
  isIndObject_limit_of_discrete (fun g => (isIndObject_limit_comp_yoneda (Discrete.functor g)).map
      (HasLimit.isoOfNatIso (Discrete.compNatIsoDiscrete g yoneda)).hom) F hF

end CategoryTheory.Limits

