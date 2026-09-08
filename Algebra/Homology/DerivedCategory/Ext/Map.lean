/-
Copyright (c) 2025 Nailin Guan, Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Jingting Wang
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Map between Ext groups induced by an exact functor

In this file, we define the map `Ext^k (M, N) → Ext^k (F(M), F(N))`,
where `F` is an exact functor between abelian categories.

# Main Definition and results

* `CategoryTheory.Abelian.Ext.mapExactFunctor` : The map between `Ext` induced by
  `CategoryTheory.LocalizerMorphism.smallShiftedHomMap`.

* `CategoryTheory.Functor.mapExtAddHom` : Upgraded of `CategoryTheory.Abelian.Ext.mapExactFunctor`
  into an additive homomorphism.

* `CategoryTheory.Functor.mapExtLinearMap` : Upgrade of `F.mapExtAddHom` assuming `F` is linear.

* `Ext.mapExactFunctor_mk₀` : `Ext.mapExactFunctor` commutes with `Ext.mk₀`

* `Ext.mapExactFunctor_comp` : `Ext.mapExactFunctor` preserves `Ext.comp`

* `mapExactFunctor_extClass` :
  `Ext.mapExactFunctor` commutes with `ShortComplex.ShortExact.extClass`

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe t t' w w' u u' v v'

namespace CategoryTheory

open Limits Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

section

open DerivedCategory

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.DerivedCategory.map_triangleOfSES** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma DerivedCategory.map_triangleOfSESδ [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) :
    dsimp% F.mapDerivedCategory.map (triangleOfSESδ hS) =
    (F.mapDerivedCategoryFactors.hom.app S.X₃) ≫
      triangleOfSESδ (hS.map_of_exact (F.mapHomologicalComplex _)) ≫
        (F.mapDerivedCategoryFactors.inv.app S.X₁)⟦1⟧' ≫
          (F.mapDerivedCategory.commShiftIso (1 : ℤ)).inv.app (Q.obj S.X₁) := by
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  rw [← cancel_epi (F.mapDerivedCategory.map
    (Q.map (CochainComplex.mappingCone.descShortComplex S))), ← Functor.map_comp,
    descShortComplex_triangleOfSESδ, F.mapDerivedCategoryFactors_hom_naturality_assoc,
    ← CochainComplex.mappingCone.mapHomologicalComplexIso_hom_descShortComplex,
    Functor.map_comp_assoc, descShortComplex_triangleOfSESδ_assoc]
  dsimp
  rw  [← Functor.map_comp_assoc]
  rw [← CochainComplex.mappingCone.map_δ, Functor.map_comp_assoc,
    ← F.mapDerivedCategoryFactors_hom_naturality_assoc, Functor.map_comp]
  simp [NatTrans.shift_app, Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_inv_app,
    ← Functor.map_comp_assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.ShortComplex.ShortExact.mapShiftedHom_single** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ShortComplex.ShortExact.mapShiftedHom_singleδ'
    [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]
    {S : ShortComplex C} (hS : S.ShortExact) (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (F.mapDerivedCategorySingleFunctor 0).inv.app S.X₃ ≫
      ShiftedHom.map hS.singleδ F.mapDerivedCategory ≫
        ((F.mapDerivedCategorySingleFunctor 0).hom.app S.X₁)⟦1⟧' =
    (hS.map_of_exact F).singleδ := by
  dsimp [ShiftedHom.map, ShortComplex.ShortExact.singleδ]
  simp only [Functor.map_comp, Category.assoc, Functor.commShiftIso_hom_naturality,
    DerivedCategory.map_triangleOfSESδ, singleFunctorsPostcompQIso_hom_hom,
    singleFunctorsPostcompQIso_inv_hom]
  generalize_proofs _ _ _ _ _ _ h1 _ _ h2
  dsimp [CochainComplex.singleFunctors]
  rw [Functor.map_id, Category.id_comp,
    Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app_assoc,
    Iso.inv_hom_id_app_assoc, Functor.map_id, Functor.map_id, Category.id_comp,
    ← Functor.map_comp,
    F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app,
    dsimp% triangleOfSESδ_naturality h1 h2
      (S.mapNatTrans (F.mapCochainComplexSingleFunctor 0).hom),
    ← Functor.map_comp_assoc]
  simp

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**CategoryTheory.ShortComplex.ShortExact.mapShiftedHom_single** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma ShortComplex.ShortExact.mapShiftedHom_singleδ
    [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]
    {S : ShortComplex C} (hS : S.ShortExact) (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    ShiftedHom.map hS.singleδ F.mapDerivedCategory =
      (F.mapDerivedCategorySingleFunctor 0).hom.app S.X₃ ≫
        (hS.map_of_exact F).singleδ ≫ ((F.mapDerivedCategorySingleFunctor 0).inv.app S.X₁)⟦1⟧' := by
  simp [← hS.mapShiftedHom_singleδ'_assoc, ← Functor.map_comp]

end

section Ext

open Localization

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : HasExt.{w'} D] (X Y : C) : HasSmallLocalizedShiftedHom.{w'}
    (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) ℤ
    ((F ⋙ CochainComplex.singleFunctor D 0).obj X)
    ((F ⋙ CochainComplex.singleFunctor D 0).obj Y) :=
  h (F.obj X) (F.obj Y)

/-- The map between `Ext` induced by `LocalizerMorphism.smallShiftedHomMap`. -/
/-
**CategoryTheory.Abelian.Ext.mapExactFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Abelian.Ext`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Abelian C] →       {D : Type u'} →         [inst_2 : CategoryThe
ory.Category.{v', u'} D] →           [inst_3 : CategoryTheory.Abelian D] →      
       (F : CategoryTheory.Functor C D) →               [F.Additive] →          
       [CategoryTheory.Limits.PreservesFiniteLimits F] →                   [Cate
goryTheory.Limits.PreservesFiniteColimits F] →                     [inst_7 : Cat
egoryTheory.HasExt C] →                       [inst_8 : CategoryTheory.HasExt D]
 →                         {X Y : C} →                           {n : ℕ} → Categ
oryTheory.Abelian.Ext X Y n → CategoryTheory.Abelian.Ext (F.obj X) (F.obj Y) n
参数：F : CategoryTheory.Functor C D；F.obj X；F.obj Y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.instHasSmallLocalizedShiftedHomHomologicalComplexIntUpQua
siIsoObjCochainComplexCompSingleFunctorOfNatOfHasExt`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{
v', u'} D]   [inst_2 : CategoryThe…

--- 原说明 ---
The map between `Ext` induced by `LocalizerMorphism.smallShiftedHomMap`.
-/
noncomputable def Abelian.Ext.mapExactFunctor [HasExt.{w} C] [HasExt.{w'} D] {X Y : C} {n : ℕ}
    (f : Ext.{w} X Y n) : Ext.{w'} (F.obj X) (F.obj Y) n :=
  (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)).smallShiftedHomMap
    ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y) f

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.Ext.mapExactFunctor_hom** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Abelian.Ext`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C] {D : Type u'}   [inst_2 : CategoryTheory.Category.{v', u'} D]
 [inst_3 : CategoryTheory.Abelian D] (F : CategoryTheory.Functor C D)   [inst_4 
: F.Additive] [inst_5 : CategoryTheory.Limits.PreservesFiniteLimits F]   [inst_6
 : CategoryTheory.Limits.PreservesFiniteColimits F] [inst_7 : HasDerivedCategory
 C]   [inst_8 : HasDerivedCategory D] [inst_9 : CategoryTheory.HasExt C] [inst_1
0 : CategoryTheory.HasExt D] {X Y : C}   {n : ℕ} (e : CategoryTheory.Abelian.Ext
 X Y n),   (CategoryTheory.Abelian.Ext.mapExactFunctor F e).hom =     CategoryTh
eory.CategoryStruct.comp ((F.mapDerivedCategorySingleFunctor 0).inv.app X)      
 (CategoryTheory.CategoryStruct.comp (e.hom.map F.mapDerivedCategory)         ((
CategoryTheory.shiftFunctor (DerivedCategory D) ↑n).map ((F.mapDerivedCategorySi
ngleFunctor 0).hom.app Y)))
参数：F : CategoryTheory.Functor C D；e : CategoryTheory.Abelian.Ext X Y n；CategoryT
heory.Abelian.Ext.mapExactFunctor F e；(F.mapDerivedCategorySingleFunctor 0).inv.
app X；CategoryTheory.CategoryStruct.comp (e.hom.map F.mapDerivedCategory)       
  ((CategoryTheory.shiftFunctor (DerivedCategory D) ↑n).map ((F.mapDerivedCatego
rySingleFunctor 0).hom.app Y))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Functor.preservesHomologyOfExact`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelia
n C]   [inst_2 : HasDerivedCategory C], DerivedCateg…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CategoryTheory.LocalizerMorphism.equiv_smallShiftedHomMap`：equiv_smallSh
iftedHomMap (G : D₁ ⥤ D₂) [G.CommShift M] (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G) [NatTran
s.CommShift e.hom M] {m : M} (f : SmallShiftedH…
· 使用定理 `CategoryTheory.instHasSmallLocalizedShiftedHomHomologicalComplexIntUpQua
siIsoObjCochainComplexCompSingleFunctorOfNatOfHasExt`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{
v', u'} D]   [inst_2 : CategoryThe…
· 使用定理 `CategoryTheory.Functor.instCommShiftCochainComplexIntDerivedCategoryHomM
apDerivedCategoryFactors`：∀ {C₁ : Type u₁} [inst : CategoryTheory.Category.{v₁, 
u₁} C₁] [inst_1 : CategoryTheory.Abelian C₁]   [inst_2 : HasDerivedCategory C₁] 
{C₂ : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ShiftedHom.comp_mk₀`：comp_mk₀ {a : M} (f : ShiftedHom X Y
 a) (m₀ : M) (hm₀ : m₀ = 0) (g : Y ⟶ Z) : f.comp (mk₀ m₀ hm₀ g) (by rw [hm₀, zer
o_add]) = f ≫ g⟦a⟧'
· 使用引理 `CategoryTheory.ShiftedHom.mk₀_comp`：mk₀_comp (m₀ : M) (hm₀ : m₀ = 0) (f 
: X ⟶ Y) {a : M} (g : ShiftedHom Y Z a) : (mk₀ m₀ hm₀ f).comp g (by rw [hm₀, add
_zero]) = f ≫ g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerive
dCategoryFactors_hom_app_assoc`：∀ {C₁ : Type u₁} [inst : CategoryTheory.Category
.{v₁, u₁} C₁] [inst_1 : CategoryTheory.Abelian C₁]   [inst_2 : HasDerivedCategor
y C₁] {C₂ : …
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.ShiftedHom.mk₀.congr_simp`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_2
 : CategoryTheory.HasShift C M…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
-/
lemma Abelian.Ext.mapExactFunctor_hom
    [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]
    [HasExt.{w} C] [HasExt.{w'} D] {X Y : C} {n : ℕ} (e : Ext X Y n) :
    (e.mapExactFunctor F).hom =
    (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫ e.hom.map F.mapDerivedCategory ≫
    ((F.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦(n : ℤ)⟧' := by
  have : (e.mapExactFunctor F).hom = _ :=
    ((F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).equiv_smallShiftedHomMap DerivedCategory.Q DerivedCategory.Q
        ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y)
          F.mapDerivedCategory F.mapDerivedCategoryFactors.symm e)
  rw [this, ← ShiftedHom.comp_mk₀ _ 0 rfl, ← ShiftedHom.mk₀_comp 0 rfl]
  congr 2
  · simp [← F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app_assoc,
      CochainComplex.singleFunctor, CochainComplex.singleFunctors]
  · simp [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      ← Functor.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app]

section

attribute [local simp] Abelian.Ext.mapExactFunctor_hom
attribute [local instance] HasDerivedCategory.standard

variable [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ)

@[simp]
/-
**CategoryTheory.Abelian.Ext.mapExactFunctor_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Abelian.Ext`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C] {D : Type u'}   [inst_2 : CategoryTheory.Category.{v', u'} D]
 [inst_3 : CategoryTheory.Abelian D] (F : CategoryTheory.Functor C D)   [inst_4 
: F.Additive] [inst_5 : CategoryTheory.Limits.PreservesFiniteLimits F]   [inst_6
 : CategoryTheory.Limits.PreservesFiniteColimits F] [inst_7 : CategoryTheory.Has
Ext C]   [inst_8 : CategoryTheory.HasExt D] (X Y : C) (n : ℕ), CategoryTheory.Ab
elian.Ext.mapExactFunctor F 0 = 0
参数：F : CategoryTheory.Functor C D；X Y : C；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.Ext.ext`：ext {n : Nat} {α β : Ext X Y n} (h : α.h
om = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Abelian.Ext.mapExactFunctor_hom`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C] {D : Type u
'}   [inst_2 : CategoryTheory.Catego…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.Abelian.Ext.zero_hom`：zero_hom : (0 : Ext X Y n).hom = 0
· 使用引理 `CategoryTheory.ShiftedHom.map_zero`：map_zero {a : M} (F : C ⥤ D) [F.Comm
Shift M] [F.Additive] : (0 : ShiftedHom X Y a).map F = 0
· 使用定理 `CategoryTheory.Functor.IsTriangulated.instAdditive`：∀ {C : Type u_1} {D 
: Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTh
eory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…
· 使用定理 `CategoryTheory.Functor.instIsTriangulatedDerivedCategoryMapDerivedCatego
ry`：∀ {C₁ : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C₁] [inst_1 : Cate
goryTheory.Abelian C₁]   [inst_2 : HasDerivedCategory C₁] {C₂ : …
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Abelian.Ext.mapExactFunctor_zero : (0 : Ext X Y n).mapExactFunctor F = 0 := by
  aesop

@[simp]
/-
**CategoryTheory.Abelian.Ext.mapExactFunctor_add** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Abelian.Ext`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C] {D : Type u'}   [inst_2 : CategoryTheory.Category.{v', u'} D]
 [inst_3 : CategoryTheory.Abelian D] (F : CategoryTheory.Functor C D)   [inst_4 
: F.Additive] [inst_5 : CategoryTheory.Limits.PreservesFiniteLimits F]   [inst_6
 : CategoryTheory.Limits.PreservesFiniteColimits F] [inst_7 : CategoryTheory.Has
Ext C]   [inst_8 : CategoryTheory.HasExt D] (X Y : C) (n : ℕ) (f g : CategoryThe
ory.Abelian.Ext X Y n),   CategoryTheory.Abelian.Ext.mapExactFunctor F (f + g) =
     CategoryTheory.Abelian.Ext.mapExactFunctor F f + CategoryTheory.Abelian.Ext
.mapExactFunctor F g
参数：F : CategoryTheory.Functor C D；X Y : C；n : ℕ；f g : CategoryTheory.Abelian.Ext
 X Y n；f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.Ext.ext`：ext {n : Nat} {α β : Ext X Y n} (h : α.h
om = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Abelian.Ext.mapExactFunctor_hom`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C] {D : Type u
'}   [inst_2 : CategoryTheory.Catego…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.Abelian.Ext.add_hom`：add_hom (α β : Ext X Y n) : (α + β).
hom = α.hom + β.hom
· 使用引理 `CategoryTheory.ShiftedHom.map_add`：map_add {a : M} (α₁ α₂ : ShiftedHom X
 Y a) (F : C ⥤ D) [F.CommShift M] [F.Additive] : (α₁ + α₂).map F = α₁.map F + α₂
.map F
· 使用定理 `CategoryTheory.Functor.IsTriangulated.instAdditive`：∀ {C : Type u_1} {D 
: Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTh
eory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…
· 使用定理 `CategoryTheory.Functor.instIsTriangulatedDerivedCategoryMapDerivedCatego
ry`：∀ {C₁ : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C₁] [inst_1 : Cate
goryTheory.Abelian C₁]   [inst_2 : HasDerivedCategory C₁] {C₂ : …
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Abelian.Ext.mapExactFunctor_add (f g : Ext.{w} X Y n) :
    (f + g).mapExactFunctor F = f.mapExactFunctor F + g.mapExactFunctor F := by
  aesop

/-- Upgraded of `CategoryTheory.Abelian.Ext.mapExactFunctor` into an additive homomorphism. -/
/-
**CategoryTheory.Functor.mapExtAddHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Abelian C] →       {D : Type u'} →         [inst_2 : CategoryThe
ory.Category.{v', u'} D] →           [inst_3 : CategoryTheory.Abelian D] →      
       (F : CategoryTheory.Functor C D) →               [F.Additive] →          
       [CategoryTheory.Limits.PreservesFiniteLimits F] →                   [Cate
goryTheory.Limits.PreservesFiniteColimits F] →                     [inst_7 : Cat
egoryTheory.HasExt C] →                       [inst_8 : CategoryTheory.HasExt D]
 →                         (X Y : C) →                           (n : ℕ) → Categ
oryTheory.Abelian.Ext X Y n →+ CategoryTheory.Abelian.Ext (F.obj X) (F.obj Y) n
参数：F : CategoryTheory.Functor C D；X Y : C；n : ℕ；F.obj X；F.obj Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Upgraded of `CategoryTheory.Abelian.Ext.mapExactFunctor` into an additive homomo
rphism.
-/
noncomputable def Functor.mapExtAddHom (X Y : C) (n : ℕ) :
    Ext.{w} X Y n →+ Ext.{w'} (F.obj X) (F.obj Y) n where
  toFun e := e.mapExactFunctor F
  map_zero' := by simp
  map_add' := by simp

@[simp]
/-
**CategoryTheory.Functor.mapExtAddHom_coe** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C] {D : Type u'}   [inst_2 : CategoryTheory.Category.{v', u'} D]
 [inst_3 : CategoryTheory.Abelian D] (F : CategoryTheory.Functor C D)   [inst_4 
: F.Additive] [inst_5 : CategoryTheory.Limits.PreservesFiniteLimits F]   [inst_6
 : CategoryTheory.Limits.PreservesFiniteColimits F] [inst_7 : CategoryTheory.Has
Ext C]   [inst_8 : CategoryTheory.HasExt D] (X Y : C) (n : ℕ),   ⇑(F.mapExtAddHo
m X Y n) = CategoryTheory.Abelian.Ext.mapExactFunctor F
参数：F : CategoryTheory.Functor C D；X Y : C；n : ℕ；F.mapExtAddHom X Y n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Functor.mapExtAddHom_coe : ⇑(F.mapExtAddHom X Y n) = Ext.mapExactFunctor F := rfl
/-
**CategoryTheory.Functor.mapExtAddHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C] {D : Type u'}   [inst_2 : CategoryTheory.Category.{v', u'} D]
 [inst_3 : CategoryTheory.Abelian D] (F : CategoryTheory.Functor C D)   [inst_4 
: F.Additive] [inst_5 : CategoryTheory.Limits.PreservesFiniteLimits F]   [inst_6
 : CategoryTheory.Limits.PreservesFiniteColimits F] [inst_7 : CategoryTheory.Has
Ext C]   [inst_8 : CategoryTheory.HasExt D] (X Y : C) (n : ℕ) (e : CategoryTheor
y.Abelian.Ext X Y n),   (F.mapExtAddHom X Y n) e = CategoryTheory.Abelian.Ext.ma
pExactFunctor F e
参数：F : CategoryTheory.Functor C D；X Y : C；n : ℕ；e : CategoryTheory.Abelian.Ext X
 Y n；F.mapExtAddHom X Y n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Functor.mapExtAddHom_apply (e : Ext X Y n) : F.mapExtAddHom X Y n e = e.mapExactFunctor F :=
  rfl

variable (R : Type*) [Ring R] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D] [F.Linear R]

@[simp]
/-
**CategoryTheory.Functor.mapExactFunctor_smul** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C] {D : Type u'}   [inst_2 : CategoryTheory.Category.{v', u'} D]
 [inst_3 : CategoryTheory.Abelian D] (F : CategoryTheory.Functor C D)   [inst_4 
: F.Additive] [inst_5 : CategoryTheory.Limits.PreservesFiniteLimits F]   [inst_6
 : CategoryTheory.Limits.PreservesFiniteColimits F] [inst_7 : CategoryTheory.Has
Ext C]   [inst_8 : CategoryTheory.HasExt D] (X Y : C) (n : ℕ) (R : Type u_1) [in
st_9 : Ring R]   [inst_10 : CategoryTheory.Linear R C] [inst_11 : CategoryTheory
.Linear R D] [CategoryTheory.Functor.Linear R F]   (r : R) (f : CategoryTheory.A
belian.Ext X Y n),   CategoryTheory.Abelian.Ext.mapExactFunctor F (r • f) = r • 
CategoryTheory.Abelian.Ext.mapExactFunctor F f
参数：F : CategoryTheory.Functor C D；X Y : C；n : ℕ；R : Type u_1；r : R；f : CategoryT
heory.Abelian.Ext X Y n；r • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.Ext.ext`：ext {n : Nat} {α β : Ext X Y n} (h : α.h
om = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Abelian.Ext.mapExactFunctor_hom`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C] {D : Type u
'}   [inst_2 : CategoryTheory.Catego…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.Abelian.Ext.smul_hom`：smul_hom (x : Ext X Y n) (r : R) [H
asDerivedCategory C] : (r • x).hom = r • x.hom
· 使用引理 `CategoryTheory.ShiftedHom.map_smul`：map_smul (r : R) {a : M} (α : Shifte
dHom X Y a) (F : C ⥤ D) [F.CommShift M] [F.Linear R] : (r • α).map F = r • (α.ma
p F)
· 使用定理 `CategoryTheory.Functor.instLinearDerivedCategoryMapDerivedCategory`：∀ {C
₁ : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C₁] [inst_1 : CategoryTheo
ry.Abelian C₁]   [inst_2 : HasDerivedCategory C₁] {C₂ : …
· 使用定理 `CategoryTheory.Linear.smul_comp`：∀ {R : Type w} {inst : Semiring R} {C :
 Type u} {inst_1 : CategoryTheory.Category.{v, u} C}   {inst_2 : CategoryTheory.
Preadditive C} [self …
· 使用定理 `CategoryTheory.Linear.comp_smul`：∀ {R : Type w} {inst : Semiring R} {C :
 Type u} {inst_1 : CategoryTheory.Category.{v, u} C}   {inst_2 : CategoryTheory.
Preadditive C} [self …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Functor.mapExactFunctor_smul (r : R) (f : Ext.{w} X Y n) :
    (r • f).mapExactFunctor F = r • (f.mapExactFunctor F) := by
  aesop

/-- Upgrade of `F.mapExtAddHom` assuming `F` is linear. -/
/-
**CategoryTheory.Functor.mapExtLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Abelian C] →       {D : Type u'} →         [inst_2 : CategoryThe
ory.Category.{v', u'} D] →           [inst_3 : CategoryTheory.Abelian D] →      
       (F : CategoryTheory.Functor C D) →               [F.Additive] →          
       [CategoryTheory.Limits.PreservesFiniteLimits F] →                   [Cate
goryTheory.Limits.PreservesFiniteColimits F] →                     [inst_7 : Cat
egoryTheory.HasExt C] →                       [inst_8 : CategoryTheory.HasExt D]
 →                         (R : Type u_1) →                           [inst_9 : 
Ring R] →                             [inst_10 : CategoryTheory.Linear R C] →   
                            [inst_11 : CategoryTheory.Linear R D] →             
                    [CategoryTheory.Functor.Linear R F] →                       
            (X Y : C) →                                     (n : ℕ) →           
                            CategoryTheory.Abelian.Ext X Y n →ₗ[R]              
                           CategoryTheory.Abelian.Ext (F.obj X) (F.obj Y) n
参数：F : CategoryTheory.Functor C D；R : Type u_1；X Y : C；n : ℕ；F.obj X；F.obj Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Upgrade of `F.mapExtAddHom` assuming `F` is linear.
-/
noncomputable def Functor.mapExtLinearMap (X Y : C) (n : ℕ) :
    Ext.{w} X Y n →ₗ[R] Ext.{w'} (F.obj X) (F.obj Y) n where
  __ := F.mapExtAddHom X Y n
  map_smul' := by simp

@[simp]
/-
**CategoryTheory.Functor.mapExtLinearMap_toAddMonoidHom** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C] {D : Type u'}   [inst_2 : CategoryTheory.Category.{v', u'} D]
 [inst_3 : CategoryTheory.Abelian D] (F : CategoryTheory.Functor C D)   [inst_4 
: F.Additive] [inst_5 : CategoryTheory.Limits.PreservesFiniteLimits F]   [inst_6
 : CategoryTheory.Limits.PreservesFiniteColimits F] [inst_7 : CategoryTheory.Has
Ext C]   [inst_8 : CategoryTheory.HasExt D] (X Y : C) (n : ℕ) (R : Type u_1) [in
st_9 : Ring R]   [inst_10 : CategoryTheory.Linear R C] [inst_11 : CategoryTheory
.Linear R D]   [inst_12 : CategoryTheory.Functor.Linear R F], ↑(F.mapExtLinearMa
p R X Y n) = F.mapExtAddHom X Y n
参数：F : CategoryTheory.Functor C D；X Y : C；n : ℕ；R : Type u_1；F.mapExtLinearMap R
 X Y n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
lemma Functor.mapExtLinearMap_toAddMonoidHom : F.mapExtLinearMap R X Y n = F.mapExtAddHom X Y n :=
  rfl
/-
**CategoryTheory.Functor.mapExtLinearMap_coe** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Functor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C] {D : Type u'}   [inst_2 : CategoryTheory.Category.{v', u'} D]
 [inst_3 : CategoryTheory.Abelian D] (F : CategoryTheory.Functor C D)   [inst_4 
: F.Additive] [inst_5 : CategoryTheory.Limits.PreservesFiniteLimits F]   [inst_6
 : CategoryTheory.Limits.PreservesFiniteColimits F] [inst_7 : CategoryTheory.Has
Ext C]   [inst_8 : CategoryTheory.HasExt D] (X Y : C) (n : ℕ) (R : Type u_1) [in
st_9 : Ring R]   [inst_10 : CategoryTheory.Linear R C] [inst_11 : CategoryTheory
.Linear R D]   [inst_12 : CategoryTheory.Functor.Linear R F],   ⇑(F.mapExtLinear
Map R X Y n) = CategoryTheory.Abelian.Ext.mapExactFunctor F
参数：F : CategoryTheory.Functor C D；X Y : C；n : ℕ；R : Type u_1；F.mapExtLinearMap R
 X Y n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Functor.mapExtLinearMap_coe : ⇑(F.mapExtLinearMap R X Y n) = Ext.mapExactFunctor F := rfl
/-
**CategoryTheory.Functor.mapExtLinearMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C] {D : Type u'}   [inst_2 : CategoryTheory.Category.{v', u'} D]
 [inst_3 : CategoryTheory.Abelian D] (F : CategoryTheory.Functor C D)   [inst_4 
: F.Additive] [inst_5 : CategoryTheory.Limits.PreservesFiniteLimits F]   [inst_6
 : CategoryTheory.Limits.PreservesFiniteColimits F] [inst_7 : CategoryTheory.Has
Ext C]   [inst_8 : CategoryTheory.HasExt D] (X Y : C) (n : ℕ) (R : Type u_1) [in
st_9 : Ring R]   [inst_10 : CategoryTheory.Linear R C] [inst_11 : CategoryTheory
.Linear R D]   [inst_12 : CategoryTheory.Functor.Linear R F] (e : CategoryTheory
.Abelian.Ext X Y n),   (F.mapExtLinearMap R X Y n) e = CategoryTheory.Abelian.Ex
t.mapExactFunctor F e
参数：F : CategoryTheory.Functor C D；X Y : C；n : ℕ；R : Type u_1；e : CategoryTheory.
Abelian.Ext X Y n；F.mapExtLinearMap R X Y n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Functor.mapExtLinearMap_apply (e : Ext X Y n) :
    F.mapExtLinearMap R X Y n e = e.mapExactFunctor F := rfl

end

namespace Abelian.Ext

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Abelian.Ext.mapExactFunctor_mk** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Abelian.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapExactFunctor_mk₀ [HasExt.{w} C] [HasExt.{w'} D] {X Y : C} (f : X ⟶ Y) :
    (mk₀ f).mapExactFunctor F = mk₀ (F.map f) := by
  dsimp [Ext.mapExactFunctor, mk₀]
  rw [(F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (.up ℤ)).smallShiftedHomMap_mk₀
    ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y)
    (0 : ℤ) rfl]
  congr
  simpa only [Functor.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism_functor,
    Functor.mapCochainComplexSingleFunctor, Iso.app_inv, Iso.app_hom] using! NatIso.naturality_1 _ f
/-
**CategoryTheory.Abelian.Ext.mapExactFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Abelian.Ext`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Abelian C] →       {D : Type u'} →         [inst_2 : CategoryThe
ory.Category.{v', u'} D] →           [inst_3 : CategoryTheory.Abelian D] →      
       (F : CategoryTheory.Functor C D) →               [F.Additive] →          
       [CategoryTheory.Limits.PreservesFiniteLimits F] →                   [Cate
goryTheory.Limits.PreservesFiniteColimits F] →                     [inst_7 : Cat
egoryTheory.HasExt C] →                       [inst_8 : CategoryTheory.HasExt D]
 →                         {X Y : C} →                           {n : ℕ} → Categ
oryTheory.Abelian.Ext X Y n → CategoryTheory.Abelian.Ext (F.obj X) (F.obj Y) n
参数：F : CategoryTheory.Functor C D；F.obj X；F.obj Y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.instHasSmallLocalizedShiftedHomHomologicalComplexIntUpQua
siIsoObjCochainComplexCompSingleFunctorOfNatOfHasExt`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{
v', u'} D]   [inst_2 : CategoryThe…
-/
lemma mapExactFunctor₀ [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) :
    Ext.mapExactFunctor F (X := X) (Y := Y) = Ext.homEquiv₀.symm ∘ F.map ∘ Ext.homEquiv₀ := by
  ext x
  rcases (Ext.mk₀_bijective X Y).2 x with ⟨y, hy⟩
  simp [← hy, Ext.mapExactFunctor_mk₀, Ext.homEquiv₀]
/-
**CategoryTheory.Abelian.Ext.mapExactFunctor_comp** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Abelian.Ext`。
形式化陈述：mapExactFunctor_comp [HasExt.{w} C] [HasExt.{w'} D] {X Y Z : C} {a b : Nat
} (α : Ext X Y a) (β : Ext Y Z b) {c : Nat} (h : a + b = c) : (α.comp β h).mapEx
actFunctor F = (α.mapExactFunctor F).comp (β.mapExactFunctor F) h
参数：α : Ext X Y a；β : Ext Y Z b；h : a + b = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.LocalizerMorphism.smallShiftedHomMap_comp`：smallShiftedHo
mMap_comp [HasSmallLocalizedShiftedHom.{w} W₁ M Y₁ Z₁] [HasSmallLocalizedShifted
Hom.{w''} W₂ M Z₂ Z₂] [HasSmallLocalizedShifte…
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Functor.preservesHomologyOfExact`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.instHasSmallLocalizedShiftedHomHomologicalComplexIntUpQua
siIsoObjCochainComplexCompSingleFunctorOfNatOfHasExt`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{
v', u'} D]   [inst_2 : CategoryThe…
· 使用定理 `CochainComplex.instIsCompatibleWithShiftHomologicalComplexIntUpQuasiIso`
：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Catego
ryTheory.Preadditive C]   [inst_2 : CategoryTheory.CategoryWi…
-/
lemma mapExactFunctor_comp [HasExt.{w} C] [HasExt.{w'} D] {X Y Z : C} {a b : ℕ}
    (α : Ext X Y a) (β : Ext Y Z b) {c : ℕ} (h : a + b = c) :
    (α.comp β h).mapExactFunctor F = (α.mapExactFunctor F).comp (β.mapExactFunctor F) h :=
  (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (.up ℤ)).smallShiftedHomMap_comp _
    ((F.mapCochainComplexSingleFunctor 0).app Y) _ α β (show b + a = (c : ℤ) by grind)

attribute [local instance] HasDerivedCategory.standard in
/-
**CategoryTheory.Abelian.Ext.mapExactFunctor_extClass** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Abelian.Ext`。
形式化陈述：mapExactFunctor_extClass [HasExt.{w} C] [HasExt.{w'} D] {S : ShortComplex 
C} (hS : S.ShortExact) : hS.extClass.mapExactFunctor F = (hS.map_of_exact F).ext
Class
参数：hS : S.ShortExact。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.Ext.ext`：ext {n : Nat} {α β : Ext X Y n} (h : α.h
om = β.hom) : α = β
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.map_of_exact`：∀ {C : Type u_1} {D
 : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryT
heory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Abelian.Ext.mapExactFunctor_hom`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C] {D : Type u
'}   [inst_2 : CategoryTheory.Catego…
· 使用引理 `CategoryTheory.ShortComplex.ShortExact.extClass_hom`：extClass_hom [HasDe
rivedCategory.{w'} C] : hS.extClass.hom = hS.singleδ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.mapShiftedHom_singleδ'`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian
 C] {D : Type u'}   [inst_2 : CategoryTheory.Catego…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma mapExactFunctor_extClass [HasExt.{w} C] [HasExt.{w'} D] {S : ShortComplex C}
    (hS : S.ShortExact) : hS.extClass.mapExactFunctor F = (hS.map_of_exact F).extClass := by
  ext
  rw [Ext.mapExactFunctor_hom, hS.extClass_hom]
  exact (hS.mapShiftedHom_singleδ' F).trans (hS.map_of_exact F).extClass_hom.symm

end Abelian.Ext

end Ext

end CategoryTheory

