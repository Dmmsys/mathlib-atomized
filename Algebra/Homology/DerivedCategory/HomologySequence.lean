/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Shift.ShiftedHom

/-!
# The homology sequence

In this file, we construct `homologyFunctor C n : DerivedCategory C ⥤ C` for all `n : ℤ`,
show that they are homological functors which form a shift sequence, and construct
the long exact homology sequences associated to distinguished triangles in the
derived category.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

universe w v u

open CategoryTheory Pretriangulated

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

namespace DerivedCategory

/-- The homology functor `DerivedCategory C ⥤ C` in degree `n : ℤ`. -/
/-
**DerivedCategory.homologyFunctor** 是 Mathlib 中的一个定义，位于命名空间 `DerivedCategory`。
形式化陈述：homologyFunctor (n : Int) : DerivedCategory C ⥤ C
参数：n : Int。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C

--- 原说明 ---
The homology functor `DerivedCategory C ⥤ C` in degree `n : ℤ`.
-/
noncomputable def homologyFunctor (n : ℤ) : DerivedCategory C ⥤ C :=
  HomologicalComplexUpToQuasiIso.homologyFunctor C (ComplexShape.up ℤ) n

/-- The homology functor on the derived category is induced by the homology
functor on the category of cochain complexes. -/
/-
**DerivedCategory.homologyFunctorFactors** 是 Mathlib 中的一个定义，位于命名空间 `DerivedCateg
ory`。
形式化陈述：homologyFunctorFactors (n : Int) : Q ⋙ homologyFunctor C n ≅ HomologicalCo
mplex.homologyFunctor _ _ n
参数：n : Int。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C

--- 原说明 ---
The homology functor on the derived category is induced by the homology
functor on the category of cochain complexes.
-/
noncomputable def homologyFunctorFactors (n : ℤ) : Q ⋙ homologyFunctor C n ≅
    HomologicalComplex.homologyFunctor _ _ n :=
  HomologicalComplexUpToQuasiIso.homologyFunctorFactors C (ComplexShape.up ℤ) n

-- needed in `homologyMap_comp_eq_zero_of_distTriang`
set_option backward.isDefEq.respectTransparency false in
variable {C} in
@[reassoc (attr := simp)]
/-
**DerivedCategory.homologyFunctorFactors_hom_naturality** 是 Mathlib 中的一个引理，位于命名空
间 `DerivedCategory`。
形式化陈述：homologyFunctorFactors_hom_naturality {K L : CochainComplex C Int} (f : K 
⟶ L) (n : Int) : (homologyFunctor C n).map (Q.map f) ≫ (homologyFunctorFactors C
 n).hom.app L = (homologyFunctorFactors C n).hom.app K ≫ HomologicalComplex.homo
logyMap f n
参数：f : K ⟶ L；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
-/
lemma homologyFunctorFactors_hom_naturality
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℤ) :
    (homologyFunctor C n).map (Q.map f) ≫ (homologyFunctorFactors C n).hom.app L =
    (homologyFunctorFactors C n).hom.app K ≫ HomologicalComplex.homologyMap f n :=
  (homologyFunctorFactors C n).hom.naturality f

/-- The homology functor on the derived category is induced by the homology
functor on the homotopy category of cochain complexes. -/
/-
**DerivedCategory.homologyFunctorFactorsh** 是 Mathlib 中的一个定义，位于命名空间 `DerivedCate
gory`。
形式化陈述：homologyFunctorFactorsh (n : Int) : Qh ⋙ homologyFunctor C n ≅ HomotopyCat
egory.homologyFunctor _ _ n
参数：n : Int。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C

--- 原说明 ---
The homology functor on the derived category is induced by the homology
functor on the homotopy category of cochain complexes.
-/
noncomputable def homologyFunctorFactorsh (n : ℤ) : Qh ⋙ homologyFunctor C n ≅
    HomotopyCategory.homologyFunctor _ _ n :=
  HomologicalComplexUpToQuasiIso.homologyFunctorFactorsh C (ComplexShape.up ℤ) n

@[reassoc]
/-
**DerivedCategory.homologyFunctorFactorsh_hom_app_quotient_obj** 是 Mathlib 中的一个引
理，位于命名空间 `DerivedCategory`。
形式化陈述：homologyFunctorFactorsh_hom_app_quotient_obj (K : CochainComplex C Int) (n
 : Int) : (homologyFunctorFactorsh C n).hom.app ((HomotopyCategory.quotient _ _)
.obj K) = (homologyFunctor C n).map ((quotientCompQhIso C).hom.app K) ≫ (homolog
yFunctorFactors C n).hom.app K ≫ (HomotopyCategory.homologyFunctorFactors C (.up
 Int) n).inv.app _
参数：K : CochainComplex C Int；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplexUpToQuasiIso.homologyFunctorFactorsh_hom_app_quotient_
obj`：homologyFunctorFactorsh_hom_app_quotient_obj (K : HomologicalComplex C c) (
i : ι) : (homologyFunctorFactorsh C c i).hom.app ((HomotopyCatego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
-/
lemma homologyFunctorFactorsh_hom_app_quotient_obj (K : CochainComplex C ℤ) (n : ℤ) :
    (homologyFunctorFactorsh C n).hom.app ((HomotopyCategory.quotient _ _).obj K) =
    (homologyFunctor C n).map ((quotientCompQhIso C).hom.app K) ≫
      (homologyFunctorFactors C n).hom.app K ≫
        (HomotopyCategory.homologyFunctorFactors C (.up ℤ) n).inv.app _ :=
  HomologicalComplexUpToQuasiIso.homologyFunctorFactorsh_hom_app_quotient_obj ..

@[reassoc]
/-
**DerivedCategory.homologyFunctorFactorsh_inv_app_quotient_obj** 是 Mathlib 中的一个引
理，位于命名空间 `DerivedCategory`。
形式化陈述：homologyFunctorFactorsh_inv_app_quotient_obj (K : CochainComplex C Int) (n
 : Int) : (homologyFunctorFactorsh C n).inv.app ((HomotopyCategory.quotient _ _)
.obj K) = (HomotopyCategory.homologyFunctorFactors C (.up Int) n).hom.app _ ≫ (h
omologyFunctorFactors C n).inv.app K ≫ (homologyFunctor C n).map ((quotientCompQ
hIso C).inv.app K)
参数：K : CochainComplex C Int；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplexUpToQuasiIso.homologyFunctorFactorsh_inv_app_quotient_
obj`：homologyFunctorFactorsh_inv_app_quotient_obj (K : HomologicalComplex C c) (
i : ι) : (homologyFunctorFactorsh C c i).inv.app ((HomotopyCatego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
-/
lemma homologyFunctorFactorsh_inv_app_quotient_obj (K : CochainComplex C ℤ) (n : ℤ) :
    (homologyFunctorFactorsh C n).inv.app ((HomotopyCategory.quotient _ _).obj K) =
    (HomotopyCategory.homologyFunctorFactors C (.up ℤ) n).hom.app _ ≫
      (homologyFunctorFactors C n).inv.app K ≫
        (homologyFunctor C n).map ((quotientCompQhIso C).inv.app K) :=
  HomologicalComplexUpToQuasiIso.homologyFunctorFactorsh_inv_app_quotient_obj ..

set_option backward.defeqAttrib.useBackward true in
variable {C} in
/-
**DerivedCategory.isIso_Qh_map_iff** 是 Mathlib 中的一个引理，位于命名空间 `DerivedCategory`。
形式化陈述：isIso_Qh_map_iff {X Y : HomotopyCategory C (ComplexShape.up Int)} (f : X ⟶
 Y) : IsIso (Qh.map f) ↔ HomotopyCategory.quasiIso C _ f
参数：ComplexShape.up Int；f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
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
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomotopyCategory.mem_quasiIso_iff`：mem_quasiIso_iff {X Y : HomotopyCateg
ory C c} (f : X ⟶ Y) : quasiIso C c f ↔ forall (n : ι), IsIso ((homologyFunctor 
_ _ n).map f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatIso.isIso_map_iff`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F₁ F₂ : CategoryT…
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `DerivedCategory.instIsLocalizationHomotopyCategoryIntUpQhQuasiIso`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abe
lian C]   [inst_2 : HasDerivedCategory C], DerivedCateg…
-/
lemma isIso_Qh_map_iff {X Y : HomotopyCategory C (ComplexShape.up ℤ)} (f : X ⟶ Y) :
    IsIso (Qh.map f) ↔ HomotopyCategory.quasiIso C _ f := by
  constructor
  · intro hf
    rw [HomotopyCategory.mem_quasiIso_iff]
    intro n
    rw [← NatIso.isIso_map_iff (homologyFunctorFactorsh C n) f]
    dsimp
    infer_instance
  · exact Localization.inverts Qh (HomotopyCategory.quasiIso _ _) _
/-
**DerivedCategory.isIso_iff** 是 Mathlib 中的一个引理，位于命名空间 `DerivedCategory`。
形式化陈述：isIso_iff {K L : DerivedCategory C} (f : K ⟶ L) : IsIso f ↔ forall (n : In
t), IsIso ((homologyFunctor C n).map f)
参数：f : K ⟶ L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `DerivedCategory.instEssSurjArrowHomotopyCategoryIntUpMapArrowQh`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abeli
an C]   [inst_2 : HasDerivedCategory C], DerivedCateg…
· 使用定理 `CategoryTheory.MorphismProperty.arrow_iso_iff`：arrow_iso_iff (P : Morphi
smProperty C) [RespectsIso P] {f g : Arrow C} (e : f ≅ g) : P f.hom ↔ P g.hom
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.isomorphisms`：∀ (C : Type u)
 [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.iso
morphisms C).RespectsIso
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `DerivedCategory.isIso_Qh_map_iff`：isIso_Qh_map_iff {X Y : HomotopyCatego
ry C (ComplexShape.up Int)} (f : X ⟶ Y) : IsIso (Qh.map f) ↔ HomotopyCategory.qu
asiIso C _ f
· 使用引理 `HomotopyCategory.mem_quasiIso_iff`：mem_quasiIso_iff {X Y : HomotopyCateg
ory C c} (f : X ⟶ Y) : quasiIso C c f ↔ forall (n : ι), IsIso ((homologyFunctor 
_ _ n).map f)
-/
lemma isIso_iff {K L : DerivedCategory C} (f : K ⟶ L) :
    IsIso f ↔ ∀ (n : ℤ), IsIso ((homologyFunctor C n).map f) := by
  refine ⟨fun hf n ↦ inferInstance, fun hf ↦ ?_⟩
  refine ((MorphismProperty.isomorphisms (DerivedCategory C)).arrow_iso_iff
    (Qh.mapArrow.objObjPreimageIso (Arrow.mk f))).1 ?_
  let g := Qh.mapArrow.objPreimage (Arrow.mk f)
  change IsIso (Qh.map g.hom)
  rw [isIso_Qh_map_iff, HomotopyCategory.mem_quasiIso_iff]
  intro n
  have e : Arrow.mk ((homologyFunctor C n).map f) ≅
      Arrow.mk ((HomotopyCategory.homologyFunctor _ _ n).map g.hom) :=
    ((homologyFunctor C n).mapArrow.mapIso
      ((Qh.mapArrow.objObjPreimageIso (Arrow.mk f)).symm)) ≪≫
      ((Functor.mapArrowFunctor _ _).mapIso (homologyFunctorFactorsh C n)).app (Arrow.mk g.hom)
  exact ((MorphismProperty.isomorphisms C).arrow_iso_iff e).1 (hf n)
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : (homologyFunctor C n).IsHomological :=
  Functor.isHomological_of_localization Qh
    (homologyFunctor C n) _ (homologyFunctorFactorsh C n)

/-- The functors `homologyFunctor C n : DerivedCategory C ⥤ C` for all `n : ℤ` are part
of a "shift sequence", i.e. they satisfy compatibilities with shifts. -/
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functors `homologyFunctor C n : DerivedCategory C ⥤ C` for all `n : ℤ` are p
art
of a "shift sequence", i.e. they satisfy compatibilities with shifts.
-/
noncomputable instance : (homologyFunctor C 0).ShiftSequence ℤ :=
  Functor.ShiftSequence.induced (homologyFunctorFactorsh C 0) ℤ
    (homologyFunctor C) (homologyFunctorFactorsh C)
/-
**DerivedCategory.shift_homologyFunctor** 是 Mathlib 中的一个引理，位于命名空间 `DerivedCatego
ry`。
形式化陈述：shift_homologyFunctor (n : Int) : (homologyFunctor C 0).shift n = homology
Functor C n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma shift_homologyFunctor (n : ℤ) :
    (homologyFunctor C 0).shift n = homologyFunctor C n := rfl

variable {C}

@[reassoc]
/-
**DerivedCategory.shiftMap_homologyFunctor_map_Qh** 是 Mathlib 中的一个引理，位于命名空间 `Der
ivedCategory`。
形式化陈述：shiftMap_homologyFunctor_map_Qh {K L : HomotopyCategory C (.up Int)} {n : 
Int} (f : K ⟶ L⟦n⟧) (a a' : Int) (h : n + a = a'
参数：.up Int；f : K ⟶ L⟦n⟧；a a' : Int。
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
· 使用引理 `CategoryTheory.Functor.ShiftSequence.induced_shiftMap`：induced_shiftMap 
{n : M} {X Y : C} (f : X ⟶ Y⟦n⟧) (a a' : M) (h : n + a = a') : letI
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `DerivedCategory.instFullFunctorHomotopyCategoryIntUpObjWhiskeringLeftQh`
：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheo
ry.Abelian C]   [inst_2 : HasDerivedCategory C] {D : Type u_1…
· 使用定理 `DerivedCategory.instFaithfulFunctorHomotopyCategoryIntUpObjWhiskeringLef
tQh`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Category
Theory.Abelian C]   [inst_2 : HasDerivedCategory C] {D : Type u_1…
-/
lemma shiftMap_homologyFunctor_map_Qh
    {K L : HomotopyCategory C (.up ℤ)} {n : ℤ} (f : K ⟶ L⟦n⟧)
    (a a' : ℤ) (h : n + a = a' := by lia) :
    (homologyFunctor C 0).shiftMap (ShiftedHom.map f Qh) a a' h =
    (homologyFunctorFactorsh C a).hom.app _ ≫
      (HomotopyCategory.homologyFunctor C (.up ℤ) 0).shiftMap f a a' h ≫
        (homologyFunctorFactorsh C a').inv.app _ :=
  Functor.ShiftSequence.induced_shiftMap ..

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**DerivedCategory.shiftMap_homologyFunctor_map_Q** 是 Mathlib 中的一个引理，位于命名空间 `Deri
vedCategory`。
形式化陈述：shiftMap_homologyFunctor_map_Q {K L : CochainComplex C Int} {n : Int} (f :
 K ⟶ L⟦n⟧) (a a' : Int) (h : n + a = a'
参数：f : K ⟶ L⟦n⟧；a a' : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ShiftedHom.map_naturality_1`：map_naturality_1 {a : M} (f 
: ShiftedHom X Y a) {F G : C ⥤ D} (e : F ≅ G) [F.CommShift M] [G.CommShift M] [N
atTrans.CommShift e.hom M] : (mk…
· 使用定理 `DerivedCategory.instCommShiftHomologicalComplexIntUpHomFunctorQuotientCo
mpQhIso`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Cate
goryTheory.Abelian C]   [inst_2 : HasDerivedCategory C], CategoryTheo…
· 使用引理 `CategoryTheory.ShiftedHom.mk₀_comp`：mk₀_comp (m₀ : M) (hm₀ : m₀ = 0) (f 
: X ⟶ Y) {a : M} (g : ShiftedHom Y Z a) : (mk₀ m₀ hm₀ f).comp g (by rw [hm₀, add
_zero]) = f ≫ g
· 使用引理 `CategoryTheory.ShiftedHom.comp_mk₀`：comp_mk₀ {a : M} (f : ShiftedHom X Y
 a) (m₀ : M) (hm₀ : m₀ = 0) (g : Y ⟶ Z) : f.comp (mk₀ m₀ hm₀ g) (by rw [hm₀, zer
o_add]) = f ≫ g⟦a⟧'
· 使用引理 `CategoryTheory.Functor.shiftMap_comp'`：shiftMap_comp' {X Y Z : C} {n : M
} (f : X ⟶ Y) (g : Y ⟶ Z⟦n⟧) (a a' : M) (ha' : n + a = a') : F.shiftMap (f ≫ g) 
a a' ha' = (F.shift a).map …
· 使用引理 `CategoryTheory.Functor.shiftMap_comp`：shiftMap_comp {X Y Z : C} {n : M} 
(f : X ⟶ Y⟦n⟧) (g : Y ⟶ Z) (a a' : M) (ha' : n + a = a') : F.shiftMap (f ≫ g⟦n⟧'
) a a' ha' = F.shiftMap f …
· 使用引理 `CategoryTheory.ShiftedHom.comp_map`：comp_map {a : M} (f : ShiftedHom X Y
 a) (F : C ⥤ D) [F.CommShift M] (G : D ⥤ E) [G.CommShift M] : f.map (F ⋙ G) = (f
.map F).map G
· 使用引理 `DerivedCategory.shiftMap_homologyFunctor_map_Qh`：shiftMap_homologyFuncto
r_map_Qh {K L : HomotopyCategory C (.up Int)} {n : Int} (f : K ⟶ L⟦n⟧) (a a' : I
nt) (h : n + a = a'
· 使用引理 `DerivedCategory.homologyFunctorFactorsh_hom_app_quotient_obj`：homologyFu
nctorFactorsh_hom_app_quotient_obj (K : CochainComplex C Int) (n : Int) : (homol
ogyFunctorFactorsh C n).hom.app ((HomotopyCategory…
· 使用引理 `DerivedCategory.homologyFunctorFactorsh_inv_app_quotient_obj`：homologyFu
nctorFactorsh_inv_app_quotient_obj (K : CochainComplex C Int) (n : Int) : (homol
ogyFunctorFactorsh C n).inv.app ((HomotopyCategory…
· 使用引理 `HomotopyCategory.homologyFunctor_shiftMap`：homologyFunctor_shiftMap {K L
 : CochainComplex C Int} {n : Int} (f : K ⟶ L⟦n⟧) (a a' : Int) (h : n + a = a') 
: (homologyFunctor C (ComplexSh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
（共 31 条，此处仅展示前 30 条）
-/
lemma shiftMap_homologyFunctor_map_Q
    {K L : CochainComplex C ℤ} {n : ℤ} (f : K ⟶ L⟦n⟧)
    (a a' : ℤ) (h : n + a = a' := by lia) :
    (homologyFunctor C 0).shiftMap (ShiftedHom.map f Q) a a' h =
    (homologyFunctorFactors C a).hom.app _ ≫
      (HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftMap f a a' h ≫
        (homologyFunctorFactors C a').inv.app _ := by
  rw [← ShiftedHom.map_naturality_1 f (quotientCompQhIso C),
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀,
    Functor.shiftMap_comp', Functor.shiftMap_comp,
    ShiftedHom.comp_map, shiftMap_homologyFunctor_map_Qh ..,
    homologyFunctorFactorsh_hom_app_quotient_obj,
    homologyFunctorFactorsh_inv_app_quotient_obj,
    HomotopyCategory.homologyFunctor_shiftMap]
  simp [shift_homologyFunctor, ← Functor.map_comp, ← Functor.map_comp_assoc]

namespace HomologySequence

/-- The connecting homomorphism on the homology sequence attached to a distinguished
triangle in the derived category. -/
/-
**DerivedCategory.HomologySequence.** 是 Mathlib 中的一个定义，位于命名空间 `DerivedCategory.H
omologySequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The connecting homomorphism on the homology sequence attached to a distinguished
triangle in the derived category.
-/
noncomputable def δ (T : Triangle (DerivedCategory C))
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁ := by lia) :
    (homologyFunctor C n₀).obj T.obj₃ ⟶ (homologyFunctor C n₁).obj T.obj₁ :=
  (homologyFunctor C 0).shiftMap T.mor₃ n₀ n₁ (by rw [add_comm 1, h])

variable (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _) (n₀ n₁ : ℤ)

include hT

@[reassoc (attr := simp)]
/-
**DerivedCategory.HomologySequence.comp_** 是 Mathlib 中的一个引理，位于命名空间 `DerivedCateg
ory.HomologySequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_δ (h : n₀ + 1 = n₁ := by lia) :
    (homologyFunctor C n₀).map T.mor₂ ≫ δ T n₀ n₁ h = 0 :=
  (homologyFunctor C 0).comp_homologySequenceδ _ hT _ _ h

@[reassoc (attr := simp)]
/-
**DerivedCategory.HomologySequence.** 是 Mathlib 中的一个引理，位于命名空间 `DerivedCategory.H
omologySequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_comp (h : n₀ + 1 = n₁ := by lia) :
    δ T n₀ n₁ h ≫ (homologyFunctor C n₁).map T.mor₁ = 0 :=
  (homologyFunctor C 0).homologySequenceδ_comp _ hT _ _ h
/-
**DerivedCategory.HomologySequence.exact** 是 Mathlib 中的一个引理，位于命名空间 `DerivedCateg
ory.HomologySequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exact₂ :
    (ShortComplex.mk ((homologyFunctor C n₀).map T.mor₁) ((homologyFunctor C n₀).map T.mor₂)
      (by simp only [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT,
        Functor.map_zero])).Exact :=
  (homologyFunctor C 0).homologySequence_exact₂ _ hT _
/-
**DerivedCategory.HomologySequence.exact** 是 Mathlib 中的一个引理，位于命名空间 `DerivedCateg
ory.HomologySequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exact₃ (h : n₀ + 1 = n₁ := by lia) :
    (ShortComplex.mk _ _ (comp_δ T hT n₀ n₁ h)).Exact :=
  (homologyFunctor C 0).homologySequence_exact₃ _ hT _ _ h
/-
**DerivedCategory.HomologySequence.exact** 是 Mathlib 中的一个引理，位于命名空间 `DerivedCateg
ory.HomologySequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exact₁ (h : n₀ + 1 = n₁ := by lia) :
    (ShortComplex.mk _ _ (δ_comp T hT n₀ n₁ h)).Exact :=
  (homologyFunctor C 0).homologySequence_exact₁ _ hT _ _ h
/-
**DerivedCategory.HomologySequence.epi_homologyMap_mor** 是 Mathlib 中的一个引理，位于命名空间
 `DerivedCategory.HomologySequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma epi_homologyMap_mor₁_iff :
    Epi ((homologyFunctor C n₀).map T.mor₁) ↔ (homologyFunctor C n₀).map T.mor₂ = 0 :=
  (homologyFunctor C 0).homologySequence_epi_shift_map_mor₁_iff _ hT _
/-
**DerivedCategory.HomologySequence.mono_homologyMap_mor** 是 Mathlib 中的一个引理，位于命名空
间 `DerivedCategory.HomologySequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mono_homologyMap_mor₁_iff (h : n₀ + 1 = n₁ := by lia) :
    Mono ((homologyFunctor C n₁).map T.mor₁) ↔ δ T n₀ n₁ h = 0 :=
  (homologyFunctor C 0).homologySequence_mono_shift_map_mor₁_iff _ hT _ _ h
/-
**DerivedCategory.HomologySequence.epi_homologyMap_mor** 是 Mathlib 中的一个引理，位于命名空间
 `DerivedCategory.HomologySequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma epi_homologyMap_mor₂_iff (h : n₀ + 1 = n₁ := by lia) :
    Epi ((homologyFunctor C n₀).map T.mor₂) ↔ δ T n₀ n₁ h = 0 :=
  (homologyFunctor C 0).homologySequence_epi_shift_map_mor₂_iff _ hT _ _ h
/-
**DerivedCategory.HomologySequence.mono_homologyMap_mor** 是 Mathlib 中的一个引理，位于命名空
间 `DerivedCategory.HomologySequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mono_homologyMap_mor₂_iff :
    Mono ((homologyFunctor C n₀).map T.mor₂) ↔ (homologyFunctor C n₀).map T.mor₁ = 0 :=
  (homologyFunctor C 0).homologySequence_mono_shift_map_mor₂_iff _ hT n₀

end HomologySequence

end DerivedCategory

namespace CochainComplex

open HomologicalComplex

variable {C} (T : Triangle (CochainComplex C ℤ))

/-- If `T` is a triangle in `CochainComplex C ℤ`, this is the connecting homomorphism
`T.obj₃.homology n₀ ⟶ T.obj₁.homology n₁` in homology when `n₀ + 1 = n₁`. -/
/-
**CochainComplex.homology** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `T` is a triangle in `CochainComplex C ℤ`, this is the connecting homomorphis
m
`T.obj₃.homology n₀ ⟶ T.obj₁.homology n₁` in homology when `n₀ + 1 = n₁`.
-/
noncomputable def homologyδOfTriangle (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁ := by lia) :
    T.obj₃.homology n₀ ⟶ T.obj₁.homology n₁ :=
  homologyMap T.mor₃ n₀ ≫
    ((homologyFunctor C (.up ℤ) 0).shiftIso 1 n₀ n₁ (by lia)).hom.app _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CochainComplex.homologyFunctorFactors_hom_app_homology** 是 Mathlib 中的一个引理，位于命名
空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologyFunctorFactors_hom_app_homologyδOfTriangle
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁ := by lia) :
    (DerivedCategory.homologyFunctorFactors C n₀).hom.app T.obj₃ ≫
      homologyδOfTriangle T n₀ n₁ h =
    DerivedCategory.HomologySequence.δ
      (DerivedCategory.Q.mapTriangle.obj T) n₀ n₁ h ≫
        (DerivedCategory.homologyFunctorFactors C n₁).hom.app T.obj₁ := by
  dsimp [DerivedCategory.HomologySequence.δ]
  rw [dsimp% [ShiftedHom.map]
      DerivedCategory.shiftMap_homologyFunctor_map_Q T.mor₃ n₀ n₁ (by lia)]
  simp [Functor.shiftMap, homologyFunctor_shift, homologyδOfTriangle]

variable (hT : DerivedCategory.Q.mapTriangle.obj T ∈ distTriang _)

include hT

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CochainComplex.homologyMap_comp_eq_zero_of_distTriang** 是 Mathlib 中的一个引理，位于命名空
间 `CochainComplex`。
形式化陈述：homologyMap_comp_eq_zero_of_distTriang (n : Int) : homologyMap T.mor₁ n ≫ 
homologyMap T.mor₂ n = 0
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `DerivedCategory.homologyFunctorFactors_hom_naturality_assoc`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C
]   [inst_2 : HasDerivedCategory C] {K L : Cochai…
· 使用引理 `DerivedCategory.homologyFunctorFactors_hom_naturality`：homologyFunctorFa
ctors_hom_naturality {K L : CochainComplex C Int} (f : K ⟶ L) (n : Int) : (homol
ogyFunctor C n).map (Q.map f) ≫ (homologyFu…
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `CategoryTheory.Pretriangulated.comp_distTriang_mor_zero₁₂`：comp_distTria
ng_mor_zero₁₂ (T) (H : T in distTriang C) : T.mor₁ ≫ T.mor₂ = 0
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.IsHomological.toPreservesZeroMorphisms`：∀ {C : Ty
pe u_1} {A : Type u_3} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : C
ategoryTheory.HasShift C ℤ}   {inst_2 : CategoryThe…
· 使用定理 `DerivedCategory.instIsHomologicalHomologyFunctor`：∀ (C : Type u) [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2
 : HasDerivedCategory C] (n : ℤ), (Der…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
lemma homologyMap_comp_eq_zero_of_distTriang (n : ℤ) :
    homologyMap T.mor₁ n ≫ homologyMap T.mor₂ n = 0 := by
  rw [← cancel_epi ((DerivedCategory.homologyFunctorFactors _ _).hom.app _),
    ← DerivedCategory.homologyFunctorFactors_hom_naturality_assoc,
    ← DerivedCategory.homologyFunctorFactors_hom_naturality,
    ← Functor.map_comp_assoc, dsimp% comp_distTriang_mor_zero₁₂ _ hT, Functor.map_zero,
    Limits.zero_comp, Limits.comp_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CochainComplex.homology** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologyδOfTriangle_homologyMap (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁ := by lia) :
    homologyδOfTriangle T n₀ n₁ h ≫ homologyMap T.mor₁ n₁ = 0 := by
  rw [← cancel_epi ((DerivedCategory.homologyFunctorFactors _ _).hom.app _),
    homologyFunctorFactors_hom_app_homologyδOfTriangle_assoc ..,
    ← DerivedCategory.homologyFunctorFactors_hom_naturality]
  dsimp
  rw [reassoc_of% dsimp% DerivedCategory.HomologySequence.δ_comp _ hT n₀ n₁ h]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CochainComplex.homologyMap_homology** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologyMap_homologyδOfTriangle (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁ := by lia) :
    homologyMap T.mor₂ n₀ ≫ homologyδOfTriangle T n₀ n₁ h = 0 := by
  simp [← cancel_epi ((DerivedCategory.homologyFunctorFactors _ _).hom.app _),
    ← DerivedCategory.homologyFunctorFactors_hom_naturality_assoc,
    reassoc_of% dsimp% DerivedCategory.HomologySequence.comp_δ _ hT n₀ n₁ h]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.homologyMap_exact** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologyMap_exact₁_of_distTriang (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁ := by lia) :
    (ShortComplex.mk _ _ (homologyδOfTriangle_homologyMap T hT n₀ n₁ h)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (DerivedCategory.HomologySequence.exact₁ _ hT n₀ n₁ h)
  exact ShortComplex.isoMk
    ((DerivedCategory.homologyFunctorFactors _ _).app _)
    ((DerivedCategory.homologyFunctorFactors _ _).app _)
    ((DerivedCategory.homologyFunctorFactors _ _).app _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.homologyMap_exact** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologyMap_exact₂_of_distTriang (n : ℤ) :
    (ShortComplex.mk _ _ (homologyMap_comp_eq_zero_of_distTriang T hT n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (DerivedCategory.HomologySequence.exact₂ _ hT n)
  exact ShortComplex.isoMk
    ((DerivedCategory.homologyFunctorFactors _ _).app _)
    ((DerivedCategory.homologyFunctorFactors _ _).app _)
    ((DerivedCategory.homologyFunctorFactors _ _).app _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.homologyMap_exact** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologyMap_exact₃_of_distTriang (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁ := by lia) :
    (ShortComplex.mk _ _ (homologyMap_homologyδOfTriangle T hT n₀ n₁ h)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (DerivedCategory.HomologySequence.exact₃ _ hT n₀ n₁ h)
  exact ShortComplex.isoMk
    ((DerivedCategory.homologyFunctorFactors _ _).app _)
    ((DerivedCategory.homologyFunctorFactors _ _).app _)
    ((DerivedCategory.homologyFunctorFactors _ _).app _)

end CochainComplex

