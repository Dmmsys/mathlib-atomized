/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Smallness of Ext-groups from the existence of enough projectives

Let `C : Type u` be an abelian category (`Category.{v} C`) that has enough projectives.
If `C` is locally `w`-small, i.e. the type of morphisms in `C` are `Small.{w}`,
then we show that the condition `HasExt.{w}` holds, which means that for `X` and `Y` in `C`,
and `n : ℕ`, we may define `Ext X Y n : Type w`. In particular, this holds for `w = v`.

However, the main lemma `hasExt_of_enoughProjectives` is not made an instance:
for a given category `C`, there may be different reasonable choices for the universe `w`,
and if we have two `HasExt.{w₁}` and `HasExt.{w₂}` instances, we would have
to specify the universe explicitly almost everywhere, which would be an inconvenience.
So we must be very selective regarding `HasExt` instances.

-/

public section

universe w v u

open CategoryTheory Category

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace CochainComplex

open HomologicalComplex

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.isSplitEpi_to_singleFunctor_obj_of_projective** 是 Mathlib 中的一个引
理，位于命名空间 `CochainComplex`。
形式化陈述：isSplitEpi_to_singleFunctor_obj_of_projective {P : C} [Projective P] {K : 
CochainComplex C Int} {i : Int} (π : K ⟶ (CochainComplex.singleFunctor C i).obj 
P) [K.IsStrictlyLE i] [QuasiIsoAt π i] : IsSplitEpi π
参数：π : K ⟶ (CochainComplex.singleFunctor C i).obj P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.next`：next (α : Type*) [AddRightCancelSemigroup α] [One α
] (i : α) : (ComplexShape.up α).next i = i + 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_tgt`：eq_of_tgt (hX : IsZero X) (f g :
 Y ⟶ X) : f = g
· 使用引理 `CochainComplex.isZero_of_isStrictlyLE`：isZero_of_isStrictlyLE (n i : Int
) (hi : n < i
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `HomologicalComplex.instHasHomologyObjSingle`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   [inst_2 : CategoryTheory.Limi…
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `HomologicalComplex.iCyclesIso_hom_inv_id_assoc`：∀ {C : Type u_1} [inst :
 CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {ι : Type u_2} {c : Com…
· 使用定理 `HomologicalComplex.homologyπ_naturality_assoc`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {ι : Type u_2} {c : Com…
· 使用定理 `HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limit
s.HasZeroMorphisms C]   [inst_2 : CategoryTheory.Limi…
（共 43 条，此处仅展示前 30 条）
-/
lemma isSplitEpi_to_singleFunctor_obj_of_projective
    {P : C} [Projective P] {K : CochainComplex C ℤ} {i : ℤ}
    (π : K ⟶ (CochainComplex.singleFunctor C i).obj P) [K.IsStrictlyLE i] [QuasiIsoAt π i] :
    IsSplitEpi π := by
  let e := K.iCyclesIso i (i + 1) (by simp)
    ((K.isZero_of_isStrictlyLE i (i + 1) (by simp)).eq_of_tgt _ _)
  let α := e.inv ≫ K.homologyπ i ≫ homologyMap π i ≫ (singleObjHomologySelfIso _ _ _).hom
  have : π.f i = α ≫ (singleObjXSelf (ComplexShape.up ℤ) i P).inv := by
    rw [← cancel_epi e.hom]
    dsimp [α, e]
    rw [assoc, assoc, assoc, iCyclesIso_hom_inv_id_assoc,
      homologyπ_naturality_assoc]
    dsimp [singleFunctor, singleFunctors]
    rw [homologyπ_singleObjHomologySelfIso_hom_assoc,
      ← singleObjCyclesSelfIso_inv_iCycles, Iso.hom_inv_id_assoc, ← cyclesMap_i]
  exact ⟨⟨{
    section_ := mkHomFromSingle (Projective.factorThru (𝟙 P) α) (by
      rintro _ rfl
      apply (K.isZero_of_isStrictlyLE i (i + 1) (by simp)).eq_of_tgt)
    id := by
      apply HomologicalComplex.from_single_hom_ext
      rw [comp_f, mkHomFromSingle_f, assoc, id_f, this, Projective.factorThru_comp_assoc,
        id_comp, Iso.hom_inv_id]
      rfl }⟩⟩

end CochainComplex

namespace DerivedCategory

variable [HasDerivedCategory.{w} C]

/-
**DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective** 是 Mathlib 中的一个定
理，位于命名空间 `DerivedCategory`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C]   [inst_2 : HasDerivedCategory C] {P : C} [CategoryTheory.Pro
jective P] {L : CochainComplex C ℤ} {i : ℤ}   (φ : DerivedCategory.Q.obj ((Cocha
inComplex.singleFunctor C i).obj P) ⟶ DerivedCategory.Q.obj L),   ∀ n < i, ∀ [L.
IsStrictlyLE n], φ = 0
参数：φ : DerivedCategory.Q.obj ((CochainComplex.singleFunctor C i).obj P) ⟶ Derive
dCategory.Q.obj L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用引理 `DerivedCategory.right_fac_of_isStrictlyLE`：right_fac_of_isStrictlyLE {X 
Y : CochainComplex C Int} (f : Q.obj X ⟶ Q.obj Y) (n : Int) [X.IsStrictlyLE n] :
 exists (X' : CochainComplex C …
· 使用定理 `CochainComplex.instIsStrictlyLEObjIntSingleFunctor`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive 
C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用引理 `CochainComplex.isSplitEpi_to_singleFunctor_obj_of_projective`：isSplitEpi
_to_singleFunctor_obj_of_projective {P : C} [Projective P] {K : CochainComplex C
 Int} {i : Int} (π : K ⟶ (CochainComplex.singleFun…
· 使用定理 `QuasiIso.quasiIsoAt`：∀ {ι : Type u_1} {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C}   {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C} {c : 
ComplexSh…
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `DerivedCategory.isIso_Q_map_iff_quasiIso`：isIso_Q_map_iff_quasiIso {K L 
: CochainComplex C Int} (φ : K ⟶ L) : IsIso (Q.map φ) ↔ QuasiIso φ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.IsSplitEpi.id`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   Ca
tegoryTheory.Categ…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用引理 `HomologicalComplex.from_single_hom_ext`：from_single_hom_ext {K : Homolog
icalComplex V c} {j : ι} {A : V} {f g : (single V c j).obj A ⟶ K} (hfg : f.f j =
 g.f j) : f = g
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_tgt`：eq_of_tgt (hX : IsZero X) (f g :
 Y ⟶ X) : f = g
· 使用引理 `CochainComplex.isZero_of_isStrictlyLE`：isZero_of_isStrictlyLE (n i : Int
) (hi : n < i
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `DerivedCategory.instAdditiveCochainComplexIntQ`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 :
 HasDerivedCategory C], DerivedCateg…
-/
lemma from_singleFunctor_obj_eq_zero_of_projective {P : C} [Projective P]
    {L : CochainComplex C ℤ} {i : ℤ}
    (φ : Q.obj ((CochainComplex.singleFunctor C i).obj P) ⟶ Q.obj L)
    (n : ℤ) (hn : n < i) [L.IsStrictlyLE n] :
    φ = 0 := by
  obtain ⟨K, _, π, h, g, rfl⟩ := right_fac_of_isStrictlyLE φ i
  have hπ : IsSplitEpi π := by
    rw [isIso_Q_map_iff_quasiIso] at h
    exact CochainComplex.isSplitEpi_to_singleFunctor_obj_of_projective π
  have h₁ : inv (Q.map π) = Q.map (section_ π) := by
    rw [← cancel_mono (Q.map π), IsIso.inv_hom_id, ← Q.map_comp, IsSplitEpi.id, Q.map_id]
  have h₂ : section_ π ≫ g = 0 := by
    apply HomologicalComplex.from_single_hom_ext
    apply (L.isZero_of_isStrictlyLE n i hn).eq_of_tgt
  rw [h₁, ← Q.map_comp, h₂, Q.map_zero]

end DerivedCategory

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Abelian.Ext

open DerivedCategory

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.Ext.eq_zero_of_projective** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Abelian.Ext`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C]   [inst_2 : CategoryTheory.HasExt C] {P Y : C} {n : ℕ} [Categ
oryTheory.Projective P]   (e : CategoryTheory.Abelian.Ext P Y (n + 1)), e = 0
参数：e : CategoryTheory.Abelian.Ext P Y (n + 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.Ext.zero_hom`：zero_hom : (0 : Ext X Y n).hom = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.Functor.instIsSplitMonoApp`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian 
C]   [inst_2 : HasDerivedCategory C] {P : C} [Cate…
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CochainComplex.instIsStrictlyLEObjIntSingleFunctor`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive 
C]   [inst_2 : CategoryTheory.Limits.Has…
-/
lemma eq_zero_of_projective [HasExt.{w} C] {P Y : C} {n : ℕ} [Projective P]
    (e : Ext P Y (n + 1)) : e = 0 := by
  let := HasDerivedCategory.standard C
  apply homEquiv.injective
  simp only [← cancel_mono (((singleFunctors C).shiftIso (n + 1) (-(n + 1)) 0
    (by lia)).hom.app _), zero_hom, Limits.zero_comp]
  apply from_singleFunctor_obj_eq_zero_of_projective
    (L := (CochainComplex.singleFunctor C (-(n + 1))).obj Y) (n := -(n + 1)) _ (by lia)
/-
**CategoryTheory.Abelian.Ext.subsingleton_of_projective** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Abelian.Ext`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C]   [inst_2 : CategoryTheory.HasExt C] (P Y : C) [CategoryTheor
y.Projective P] (n : ℕ),   Subsingleton (CategoryTheory.Abelian.Ext P Y (n + 1))
参数：P Y : C；n : ℕ；CategoryTheory.Abelian.Ext P Y (n + 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_of_forall_eq`：∀ {α : Sort u_1} (x : α), (∀ (y : α), y = x) 
→ Subsingleton α
· 使用定理 `CategoryTheory.Abelian.Ext.eq_zero_of_projective`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2
 : CategoryTheory.HasExt C] {P Y : C} …
-/
lemma subsingleton_of_projective [HasExt.{w} C]
    (P Y : C) [Projective P] (n : ℕ) : Subsingleton (Ext.{w} P Y (n + 1)) :=
  subsingleton_of_forall_eq 0 Ext.eq_zero_of_projective

end Abelian.Ext

variable (C)

open Abelian

/-- If `C` is a locally `w`-small abelian category with enough projectives,
then `HasExt.{w} C` holds. We do not make this an instance though:
for a given category `C`, there may be different reasonable choices for
the universe `w`, and if we have two `HasExt.{w₁} C` and `HasExt.{w₂} C`
instances, we would have to specify the universe explicitly almost
everywhere, which would be an inconvenience. Then, we must be
very selective regarding `HasExt` instances. -/
/-
**CategoryTheory.hasExt_of_enoughProjectives** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C]   [CategoryTheory.LocallySmall.{w, v, u} C] [CategoryTheory.E
noughProjectives C], CategoryTheory.HasExt C
参数：C : Type u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.hasExt_of_hasDerivedCategory`：hasExt_of_hasDerivedCategor
y [HasDerivedCategory.{w} C] : HasExt.{w} C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.hasExt_iff_small_ext`：hasExt_iff_small_ext : HasExt.{w'} 
C ↔ forall (X Y : C) (n : Nat), Small.{w'} (Ext.{w} X Y n)
· 使用定理 `small_congr`：small_congr {α : Type*} {β : Type*} (e : α ≃ β) : Small.{w}
 α ↔ Small.{w} β
· 使用定理 `CategoryTheory.instSmallHomOfLocallySmall`：∀ (C : Type u) [inst : Catego
ryTheory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C] (X Y : C),
   Small.{w, v} (X ⟶ Y)
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用引理 `CategoryTheory.ShortComplex.exact_of_f_is_kernel`：exact_of_f_is_kernel (
hS : IsLimit (KernelFork.ofι S.f S.zero)) [S.HasHomology] : S.Exact
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃`：contravariant_
sequence_exact₃ {n₁ : Nat} (x₃ : Ext S.X₃ Y n₁) (hx₃ : (mk₀ S.g).comp x₃ (zero_a
dd n₁) = 0) {n₀ : Nat} (hn₀ : 1 + n₀ = n₁) : e…
· 使用定理 `CategoryTheory.Abelian.Ext.eq_zero_of_projective`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2
 : CategoryTheory.HasExt C] {P Y : C} …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `small_of_surjective`：small_of_surjective {α : Type v} {β : Type w} [Smal
l.{u} α] {f : α -> β} (hf : Function.Surjective f) : Small.{u} β

--- 原说明 ---
If `C` is a locally `w`-small abelian category with enough projectives,
then `HasExt.{w} C` holds. We do not make this an instance though:
for a given category `C`, there may be different reasonable choices for
the universe `w`, and if we have two `HasExt.{w₁} C` and `HasExt.{w₂} C`
instances, we would have to specify the universe explicitly almost
everywhere, which would be an inconvenience. Then, we must be
very selective regarding `HasExt` instances.
-/
lemma hasExt_of_enoughProjectives [LocallySmall.{w} C] [EnoughProjectives C] : HasExt.{w} C := by
  let := HasDerivedCategory.standard C
  have := hasExt_of_hasDerivedCategory C
  rw [hasExt_iff_small_ext.{w}]
  intro X Y n
  induction n generalizing X Y with
  | zero =>
    rw [small_congr Ext.homEquiv₀]
    infer_instance
  | succ n hn =>
    let S := ShortComplex.mk _ _ (kernel.condition (Projective.π X))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel S.g) }
    have : Function.Surjective (Ext.precomp hS.extClass Y (add_comm 1 n)) := fun x₃ ↦
      Ext.contravariant_sequence_exact₃ hS Y x₃
        (Ext.eq_zero_of_projective _) (by lia)
    exact small_of_surjective.{w} this

end CategoryTheory

