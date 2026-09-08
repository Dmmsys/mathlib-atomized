/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.SmallShiftedHom
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-!
# Morphisms to K-injective complexes in the derived category

In this file, we show that if `L : CochainComplex C ℤ` is K-injective,
then for any `K : HomotopyCategory C (.up ℤ)`, the functor `DerivedCategory.Qh`
induces a bijection from the type of morphisms `K ⟶ (HomotopyCategory.quotient _ _).obj L)`
(i.e. homotopy classes of morphisms of cochain complexes) to the type of
morphisms in the derived category.
We obtain that a morphism between `K`-injective cochain complexes is a quasi-isomorphism
iff it is a homotopy equivalence. In particular, a morphism between cochain complexes
indexed by `ℕ` which consist of injective objects is a quasi-isomorphism iff
it is a homotopy equivalence.

-/

@[expose] public section

universe w v u

open CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

open CategoryTheory Localization DerivedCategory

namespace CochainComplex

namespace IsKInjective

/-
**CochainComplex.IsKInjective.Qh_map_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Cochai
nComplex.IsKInjective`。
形式化陈述：Qh_map_bijective [HasDerivedCategory C] (K : HomotopyCategory C (ComplexSh
ape.up Int)) (L : CochainComplex C Int) [L.IsKInjective] : Function.Bijective (D
erivedCategory.Qh.map : (K ⟶ (HomotopyCategory.quotient _ _).obj L) -> _)
参数：K : HomotopyCategory C (ComplexShape.up Int)；L : CochainComplex C Int。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `CategoryTheory.ObjectProperty.rightOrthogonal.map_bijective_of_isTriangu
lated`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [i
nst_1 : CategoryTheory.Category.{v', u'} D]   {P : CategoryTheory.O…
· 使用定理 `HomotopyCategory.instHasZeroObject`：∀ {ι : Type u_2} (V : Type u) [inst 
: CategoryTheory.Category.{v, u} V] [inst_1 : CategoryTheory.Preadditive V]   (c
 : ComplexShape ι) [Cate…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `HomotopyCategory.instAdditiveIntUpShiftFunctor`：∀ (C : Type u) [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] (n : ℤ)
,   (CategoryTheory.shiftFunctor (Ho…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `HomotopyCategory.instIsTriangulatedIntUpSubcategoryAcyclic`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]
,   (HomotopyCategory.subcategoryAcyclic C).IsTr…
· 使用定理 `HomotopyCategory.instIsTriangulatedIntUp`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   [inst_2
 : CategoryTheory.Limits.HasBi…
· 使用定理 `CochainComplex.IsKInjective.rightOrthogonal`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abelian C]   (L : C
ochainComplex C ℤ) [L.IsKInjectiv…
· 使用定理 `DerivedCategory.instIsLocalizationHomotopyCategoryIntUpQhTrWSubcategoryA
cyclic`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categ
oryTheory.Abelian C]   [inst_2 : HasDerivedCategory C], DerivedCateg…
-/
lemma Qh_map_bijective [HasDerivedCategory C]
    (K : HomotopyCategory C (ComplexShape.up ℤ))
    (L : CochainComplex C ℤ) [L.IsKInjective] :
    Function.Bijective (DerivedCategory.Qh.map :
      (K ⟶ (HomotopyCategory.quotient _ _).obj L) → _) :=
  (CochainComplex.IsKInjective.rightOrthogonal L).map_bijective_of_isTriangulated _ _

open HomologicalComplex in
attribute [local instance] HasDerivedCategory.standard in
/-
**CochainComplex.IsKInjective.quasiIso_iff** 是 Mathlib 中的一个引理，位于命名空间 `CochainCom
plex.IsKInjective`。
形式化陈述：quasiIso_iff {K L : CochainComplex C Int} [K.IsKInjective] [L.IsKInjective
] (f : K ⟶ L) : QuasiIso f ↔ homotopyEquivalences C (.up Int) f
参数：f : K ⟶ L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomotopyCategory.inverseImage_quotient_isomorphisms`：inverseImage_quotie
nt_isomorphisms : (MorphismProperty.isomorphisms _).inverseImage (HomotopyCatego
ry.quotient V c) = homotopyEquivalences V…
· 使用引理 `CategoryTheory.MorphismProperty.inverseImage_iff`：inverseImage_iff (P : 
MorphismProperty D) (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) : P.inverseImage F f ↔ P (
F.map f)
· 使用定理 `CategoryTheory.MorphismProperty.isomorphisms.iff`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y),   CategoryTheory.Morph
ismProperty.isomorphisms C f ↔ Categor…
· 使用定理 `DerivedCategory.instIsIsoMapCochainComplexIntQOfQuasiIso`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]  
 [inst_2 : HasDerivedCategory C] {K L : Cochai…
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用引理 `CochainComplex.IsKInjective.Qh_map_bijective`：Qh_map_bijective [HasDeriv
edCategory C] (K : HomotopyCategory C (ComplexShape.up Int)) (L : CochainComplex
 C Int) [L.IsKInjective] : Functio…
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `DerivedCategory.quotientCompQhIso_hom_naturality_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [
inst_2 : HasDerivedCategory C] {K L : Cochai…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : X ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用引理 `homotopyEquivalences_le_quasiIso`：homotopyEquivalences_le_quasiIso {ι : 
Type*} (C : Type u) [Category.{v} C] [Preadditive C] (c : ComplexShape ι) [Categ
oryWithHomology C] : h…
-/
lemma quasiIso_iff {K L : CochainComplex C ℤ} [K.IsKInjective] [L.IsKInjective] (f : K ⟶ L) :
    QuasiIso f ↔ homotopyEquivalences C (.up ℤ) f := by
  refine ⟨fun _ ↦ ?_, fun hf ↦ homotopyEquivalences_le_quasiIso _ _ _ hf⟩
  rw [← HomotopyCategory.inverseImage_quotient_isomorphisms,
    MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff]
  obtain ⟨g, hg⟩ := (Qh_map_bijective _ _).surjective
    ((quotientCompQhIso C).hom.app L ≫ inv (Q.map f) ≫ (quotientCompQhIso C).inv.app K)
  refine ⟨g, (Qh_map_bijective _ _).injective ?_, (Qh_map_bijective _ _).injective ?_⟩
  · simp [hg]
  · simp [hg, ← quotientCompQhIso_inv_naturality, -NatTrans.naturality]

end IsKInjective

namespace HomComplex.CohomologyClass

variable (K L : CochainComplex C ℤ) (n : ℤ)
  [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) ℤ K L]

/-
**CochainComplex.HomComplex.CohomologyClass.bijective_toSmallShiftedHom_of_isKIn
jective** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.HomComplex.CohomologyClass`。
形式化陈述：bijective_toSmallShiftedHom_of_isKInjective [L.IsKInjective] : Function.Bi
jective (toSmallShiftedHom.{w} (K
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelia
n C]   [inst_2 : HasDerivedCategory C], DerivedCateg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Bijective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Bijective f → ∀ (g : γ → α), Function.Bijective 
(f ∘ g) ↔ Function.Bi…
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CochainComplex.HomComplex.CohomologyClass.mk_surjective`：mk_surjective :
 Function.Surjective (mk : Cocycle K L n -> _)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CochainComplex.HomComplex.CohomologyClass.equiv_toSmallShiftedHom_mk`：eq
uiv_toSmallShiftedHom_mk [HasDerivedCategory C] (x : Cocycle K L n) : SmallShift
edHom.equiv _ DerivedCategory.Q (mk x).toSmallShiftedHom =…
· 使用定理 `CategoryTheory.Iso.homCongr_apply`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) (f : X ⟶ Y),   (α.
homCongr β) f = Categor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.Bijective.comp`：∀ {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {g 
: β → φ} {f : α → β},   Function.Bijective g → Function.Bijective f → Function.B
ijective (g ∘…
· 使用引理 `CochainComplex.IsKInjective.Qh_map_bijective`：Qh_map_bijective [HasDeriv
edCategory C] (K : HomotopyCategory C (ComplexShape.up Int)) (L : CochainComplex
 C Int) [L.IsKInjective] : Functio…
· 使用定理 `CochainComplex.instIsKInjectiveObjIntShiftFunctor`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abelian C]   
(L : CochainComplex C ℤ) [hL : L.IsKInj…
· 使用引理 `CochainComplex.HomComplex.CohomologyClass.toHom_bijective`：toHom_bijecti
ve : Function.Bijective (toHom : CohomologyClass K L n -> _)
-/
lemma bijective_toSmallShiftedHom_of_isKInjective [L.IsKInjective] :
    Function.Bijective (toSmallShiftedHom.{w} (K := K) (L := L) (n := n)) := by
  let := HasDerivedCategory.standard C
  rw [← Function.Bijective.of_comp_iff'
      (SmallShiftedHom.equiv _ DerivedCategory.Q).bijective,
    ← Function.Bijective.of_comp_iff' (Iso.homCongr ((quotientCompQhIso C).symm.app K)
      ((Q.commShiftIso n).symm.app L ≪≫ (quotientCompQhIso C).symm.app (L⟦n⟧))).bijective]
  convert! (CochainComplex.IsKInjective.Qh_map_bijective _ _).comp (toHom_bijective K L n)
  ext x
  obtain ⟨x, rfl⟩ := x.mk_surjective
  simp [toHom_mk, ShiftedHom.map]

variable {K L n} in
/-- When `L` is a K-injective cochain complex, cohomology classes
in `CohomologyClass K L n` identify to elements in a type `SmallShiftedHom` relatively
to quasi-isomorphisms. -/
@[simps! -isSimp]
/-
**CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective** 是 Mathlib 中的一个
定义，位于命名空间 `CochainComplex.HomComplex.CohomologyClass`。
形式化陈述：equivOfIsKInjective [L.IsKInjective] : CohomologyClass K L n ≃ SmallShifte
dHom.{w} (HomologicalComplex.quasiIso C (.up Int)) K L n
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用引理 `CochainComplex.HomComplex.CohomologyClass.bijective_toSmallShiftedHom_of
_isKInjective`：bijective_toSmallShiftedHom_of_isKInjective [L.IsKInjective] : Fu
nction.Bijective (toSmallShiftedHom.{w} (K

--- 原说明 ---
When `L` is a K-injective cochain complex, cohomology classes
in `CohomologyClass K L n` identify to elements in a type `SmallShiftedHom` rela
tively
to quasi-isomorphisms.
-/
noncomputable def equivOfIsKInjective [L.IsKInjective] :
    CohomologyClass K L n ≃
      SmallShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) K L n :=
  Equiv.ofBijective _ (bijective_toSmallShiftedHom_of_isKInjective _ _ _)

end HomComplex.CohomologyClass

open HomologicalComplex

/-
**CochainComplex.quasiIso_iff_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `CochainCom
plex`。
形式化陈述：quasiIso_iff_of_injective {K L : CochainComplex C Nat} [forall n, Injectiv
e (K.X n)] [forall n, Injective (L.X n)] (f : K ⟶ L) : QuasiIso f ↔ homotopyEqui
valences C (.up Nat) f
参数：K.X n；L.X n；f : K ⟶ L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
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
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `HomologicalComplex.extend.instHasHomology`：∀ {ι : Type u_1} {ι' : Type u
_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : Categor
yTheory.Category.{v_1, u_3} C] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomologicalComplex.quasiIso_extendMap_iff`：quasiIso_extendMap_iff [foral
l j, K.HasHomology j] [forall j, L.HasHomology j] : QuasiIso (extendMap φ e) ↔ Q
uasiIso φ
· 使用引理 `CochainComplex.IsKInjective.quasiIso_iff`：quasiIso_iff {K L : CochainCom
plex C Int} [K.IsKInjective] [L.IsKInjective] (f : K ⟶ L) : QuasiIso f ↔ homotop
yEquivalences C (.up Int) f
· 使用定理 `CochainComplex.instIsKInjectiveExtendNatIntEmbeddingUpNatOfInjectiveX`：∀
 {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Category
Theory.Abelian C]   (K : CochainComplex C ℕ) [∀ (n : ℕ), Ca…
· 使用引理 `HomologicalComplex.homotopyEquivalences_extendMap_iff`：HomologicalComple
x.homotopyEquivalences_extendMap_iff {C : Type*} [Category* C] [HasZeroObject C]
 [Preadditive C] {K L : HomologicalComplex …
· 使用定理 `ComplexShape.instIsRelIffNatIntEmbeddingUpNat`：ComplexShape.embeddingUpN
at.IsRelIff
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma quasiIso_iff_of_injective {K L : CochainComplex C ℕ}
    [∀ n, Injective (K.X n)] [∀ n, Injective (L.X n)]
    (f : K ⟶ L) :
    QuasiIso f ↔ homotopyEquivalences C (.up ℕ) f := by
  rw [← quasiIso_extendMap_iff _ ComplexShape.embeddingUpNat,
    CochainComplex.IsKInjective.quasiIso_iff,
    homotopyEquivalences_extendMap_iff]

end CochainComplex

