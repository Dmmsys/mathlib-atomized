/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # Calculus of fractions in the derived category

We obtain various consequences of the calculus of left and right fractions
for `HomotopyCategory.quasiIso C (ComplexShape.up ℤ)` as lemmas about
factorizations of morphisms `f : Q.obj X ⟶ Q.obj Y` (where `X` and `Y`
are cochain complexes). These `f` can be factored as
a right fraction `inv (Q.map s) ≫ Q.map g` or as a left fraction
`Q.map g ≫ inv (Q.map s)`, with `s` a quasi-isomorphism (to `X` or from `Y`).
When strict bounds are known on `X` or `Y`, certain bounds may also be ensured
on the auxiliary object appearing in the fraction.

-/

public section

universe w v u

open CategoryTheory Category Limits

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).HasLeftCalculusOfFractions := by
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  infer_instance
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).HasRightCalculusOfFractions := by
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-- Any morphism `f : Q.obj X ⟶ Q.obj Y` in the derived category can be written
as `f = inv (Q.map s) ≫ Q.map g` with `s : X' ⟶ X` a quasi-isomorphism and `g : X' ⟶ Y`. -/
/-
**DerivedCategory.right_fac** 是 Mathlib 中的一个引理，位于命名空间 `DerivedCategory`。
形式化陈述：right_fac {X Y : CochainComplex C Int} (f : Q.obj X ⟶ Q.obj Y) : exists (X
' : CochainComplex C Int) (s : X' ⟶ X) (_ : IsIso (Q.map s)) (g : X' ⟶ Y), f = i
nv (Q.map s) ≫ Q.map g
参数：f : Q.obj X ⟶ Q.obj Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
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
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `DerivedCategory.instIsLocalizationHomotopyCategoryIntUpQhQuasiIso`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abe
lian C]   [inst_2 : HasDerivedCategory C], DerivedCateg…
· 使用定理 `CategoryTheory.Localization.exists_rightFraction`：∀ {C : Type u_1} {D : 
Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheo
ry.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `DerivedCategory.instHasRightCalculusOfFractionsHomotopyCategoryIntUpQuas
iIso`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C],   (HomotopyCategory.quasiIso C (ComplexShape.u…
· 使用引理 `CategoryTheory.MorphismProperty.RightFraction.cases`：cases (α : W.RightF
raction X Y) : exists (X' : C) (s : X' ⟶ X) (hs : W s) (f : X' ⟶ Y), α = RightFr
action.mk s hs f
· 使用引理 `HomotopyCategory.quotient_obj_surjective`：quotient_obj_surjective (X : H
omotopyCategory V c) : exists (K : HomologicalComplex V c), (quotient _ _).obj K
 = X
· 使用定理 `CategoryTheory.Functor.map_surjective`：map_surjective (F : C ⥤ D) [Full 
F] : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `HomotopyCategory.instFullHomologicalComplexQuotient`：∀ {ι : Type u_2} (V
 : Type u) [inst : CategoryTheory.Category.{v, u} V] [inst_1 : CategoryTheory.Pr
eadditive V]   (c : ComplexShape ι), (Hom…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `DerivedCategory.isIso_Qh_map_iff`：isIso_Qh_map_iff {X Y : HomotopyCatego
ry C (ComplexShape.up Int)} (f : X ⟶ Y) : IsIso (Qh.map f) ↔ HomotopyCategory.qu
asiIso C _ f

--- 原说明 ---
Any morphism `f : Q.obj X ⟶ Q.obj Y` in the derived category can be written
as `f = inv (Q.map s) ≫ Q.map g` with `s : X' ⟶ X` a quasi-isomorphism and `g : 
X' ⟶ Y`.
-/
lemma right_fac {X Y : CochainComplex C ℤ} (f : Q.obj X ⟶ Q.obj Y) :
    ∃ (X' : CochainComplex C ℤ) (s : X' ⟶ X) (_ : IsIso (Q.map s)) (g : X' ⟶ Y),
      f = inv (Q.map s) ≫ Q.map g := by
  have ⟨φ, hφ⟩ := Localization.exists_rightFraction Qh (HomotopyCategory.quasiIso C _) f
  obtain ⟨X', s, hs, g, rfl⟩ := φ.cases
  obtain ⟨X', rfl⟩ := HomotopyCategory.quotient_obj_surjective X'
  obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  rw [← isIso_Qh_map_iff] at hs
  exact ⟨X', s, hs, g, hφ⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Any morphism `f : Q.obj X ⟶ Q.obj Y` in the derived category can be written
as `f = Q.map g ≫ inv (Q.map s)` with `g : X ⟶ Y'` and `s : Y ⟶ Y'` a quasi-isomorphism. -/
/-
**DerivedCategory.left_fac** 是 Mathlib 中的一个引理，位于命名空间 `DerivedCategory`。
形式化陈述：left_fac {X Y : CochainComplex C Int} (f : Q.obj X ⟶ Q.obj Y) : exists (Y'
 : CochainComplex C Int) (g : X ⟶ Y') (s : Y ⟶ Y') (_ : IsIso (Q.map s)), f = Q.
map g ≫ inv (Q.map s)
参数：f : Q.obj X ⟶ Q.obj Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
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
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `DerivedCategory.instIsLocalizationHomotopyCategoryIntUpQhQuasiIso`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abe
lian C]   [inst_2 : HasDerivedCategory C], DerivedCateg…
· 使用定理 `CategoryTheory.Localization.exists_leftFraction`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `DerivedCategory.instHasLeftCalculusOfFractionsHomotopyCategoryIntUpQuasi
Iso`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Category
Theory.Abelian C],   (HomotopyCategory.quasiIso C (ComplexShape.u…
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.cases`：cases (α : W.LeftFra
ction X Y) : exists (Y' : C) (f : X ⟶ Y') (s : Y ⟶ Y') (hs : W s), α = LeftFract
ion.mk f s hs
· 使用引理 `HomotopyCategory.quotient_obj_surjective`：quotient_obj_surjective (X : H
omotopyCategory V c) : exists (K : HomologicalComplex V c), (quotient _ _).obj K
 = X
· 使用定理 `CategoryTheory.Functor.map_surjective`：map_surjective (F : C ⥤ D) [Full 
F] : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `HomotopyCategory.instFullHomologicalComplexQuotient`：∀ {ι : Type u_2} (V
 : Type u) [inst : CategoryTheory.Category.{v, u} V] [inst_1 : CategoryTheory.Pr
eadditive V]   (c : ComplexShape ι), (Hom…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `DerivedCategory.isIso_Qh_map_iff`：isIso_Qh_map_iff {X Y : HomotopyCatego
ry C (ComplexShape.up Int)} (f : X ⟶ Y) : IsIso (Qh.map f) ↔ HomotopyCategory.qu
asiIso C _ f

--- 原说明 ---
Any morphism `f : Q.obj X ⟶ Q.obj Y` in the derived category can be written
as `f = Q.map g ≫ inv (Q.map s)` with `g : X ⟶ Y'` and `s : Y ⟶ Y'` a quasi-isom
orphism.
-/
lemma left_fac {X Y : CochainComplex C ℤ} (f : Q.obj X ⟶ Q.obj Y) :
    ∃ (Y' : CochainComplex C ℤ) (g : X ⟶ Y') (s : Y ⟶ Y') (_ : IsIso (Q.map s)),
      f = Q.map g ≫ inv (Q.map s) := by
  have ⟨φ, hφ⟩ := Localization.exists_leftFraction Qh (HomotopyCategory.quasiIso C _) f
  obtain ⟨X', g, s, hs, rfl⟩ := φ.cases
  obtain ⟨X', rfl⟩ := HomotopyCategory.quotient_obj_surjective X'
  obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  rw [← isIso_Qh_map_iff] at hs
  exact ⟨X', g, s, hs, hφ⟩

/-- Any morphism `f : Q.obj X ⟶ Q.obj Y` in the derived category with `X` strictly `≤ n`
can be written as `f = inv (Q.map s) ≫ Q.map g` with `s : X' ⟶ X` a quasi-isomorphism with
`X'` strictly `≤ n` and `g : X' ⟶ Y`. -/
/-
**DerivedCategory.right_fac_of_isStrictlyLE** 是 Mathlib 中的一个引理，位于命名空间 `DerivedCa
tegory`。
形式化陈述：right_fac_of_isStrictlyLE {X Y : CochainComplex C Int} (f : Q.obj X ⟶ Q.ob
j Y) (n : Int) [X.IsStrictlyLE n] : exists (X' : CochainComplex C Int) (_ : X'.I
sStrictlyLE n) (s : X' ⟶ X) (_ : IsIso (Q.map s)) (g : X' ⟶ Y), f = inv (Q.map s
) ≫ Q.map g
参数：f : Q.obj X ⟶ Q.obj Y；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `DerivedCategory.right_fac`：right_fac {X Y : CochainComplex C Int} (f : Q
.obj X ⟶ Q.obj Y) : exists (X' : CochainComplex C Int) (s : X' ⟶ X) (_ : IsIso (
Q.map s)) (g : …
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
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
· 使用定理 `HomologicalComplex.instHasHomologyTruncLE`：∀ {ι : Type u_1} {ι' : Type u
_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : Categor
yTheory.Category.{v_1, u_3} C] …
· 使用定理 `ComplexShape.instIsTruncLENatIntEmbeddingUpIntLE`：∀ (p : ℤ), (ComplexSha
pe.embeddingUpIntLE p).IsTruncLE
· 使用引理 `CochainComplex.quasiIso_truncLEMap_iff`：quasiIso_truncLEMap_iff : QuasiI
so (truncLEMap φ n) ↔ forall (i : Int) (_ : i <= n), QuasiIsoAt φ i
· 使用定理 `QuasiIso.quasiIsoAt`：∀ {ι : Type u_1} {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C}   {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C} {c : 
ComplexSh…
· 使用定理 `HomologicalComplex.instIsStrictlySupportedTruncLE`：∀ {ι : Type u_1} {ι' 
: Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst :
 CategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `DerivedCategory.instIsIsoMapCochainComplexIntQOfQuasiIso`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]  
 [inst_2 : HasDerivedCategory C] {K L : Cochai…
· 使用定理 `CochainComplex.instQuasiIsoIntιTruncLEOfIsLE`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   (K : CochainComplex C ℤ…
· 使用定理 `HomologicalComplex.instIsSupportedOfIsStrictlySupported`：∀ {ι : Type u_1
} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [
inst : CategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CochainComplex.ιTruncLE_naturality`：ιTruncLE_naturality (n : Int) : trun
cLEMap φ n ≫ L.ιTruncLE n = K.ιTruncLE n ≫ φ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.inv.congr_simp`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (f f_1 : X ⟶ Y) (e_f : f = f_1)   [I : CategoryTheory.
IsIso f], CategoryT…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : X ⟶ Z), CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Any morphism `f : Q.obj X ⟶ Q.obj Y` in the derived category with `X` strictly `
≤ n`
can be written as `f = inv (Q.map s) ≫ Q.map g` with `s : X' ⟶ X` a quasi-isomor
phism with
`X'` strictly `≤ n` and `g : X' ⟶ Y`.
-/
lemma right_fac_of_isStrictlyLE {X Y : CochainComplex C ℤ} (f : Q.obj X ⟶ Q.obj Y) (n : ℤ)
    [X.IsStrictlyLE n] :
    ∃ (X' : CochainComplex C ℤ) (_ : X'.IsStrictlyLE n) (s : X' ⟶ X) (_ : IsIso (Q.map s))
      (g : X' ⟶ Y), f = inv (Q.map s) ≫ Q.map g := by
  obtain ⟨X', s, hs, g, rfl⟩ := right_fac f
  have : IsIso (Q.map (CochainComplex.truncLEMap s n)) := by
    rw [isIso_Q_map_iff_quasiIso, CochainComplex.quasiIso_truncLEMap_iff]
    rw [isIso_Q_map_iff_quasiIso] at hs
    infer_instance
  refine ⟨X'.truncLE n, inferInstance, CochainComplex.truncLEMap s n ≫ X.ιTruncLE n, ?_,
      CochainComplex.truncLEMap g n ≫ Y.ιTruncLE n, ?_⟩
  · rw [Q.map_comp]
    infer_instance
  · simp

/-- Any morphism `f : Q.obj X ⟶ Q.obj Y` in the derived category with `Y` strictly `≥ n`
can be written as `f = Q.map g ≫ inv (Q.map s)` with `g : X ⟶ Y'` and `s : Y ⟶ Y'`
a quasi-isomorphism with `Y'` strictly `≥ n`. -/
/-
**DerivedCategory.left_fac_of_isStrictlyGE** 是 Mathlib 中的一个引理，位于命名空间 `DerivedCat
egory`。
形式化陈述：left_fac_of_isStrictlyGE {X Y : CochainComplex C Int} (f : Q.obj X ⟶ Q.obj
 Y) (n : Int) [Y.IsStrictlyGE n] : exists (Y' : CochainComplex C Int) (_ : Y'.Is
StrictlyGE n) (g : X ⟶ Y') (s : Y ⟶ Y') (_ : IsIso (Q.map s)), f = Q.map g ≫ inv
 (Q.map s)
参数：f : Q.obj X ⟶ Q.obj Y；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `DerivedCategory.left_fac`：left_fac {X Y : CochainComplex C Int} (f : Q.o
bj X ⟶ Q.obj Y) : exists (Y' : CochainComplex C Int) (g : X ⟶ Y') (s : Y ⟶ Y') (
_ : IsIso (Q.m…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
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
· 使用定理 `HomologicalComplex.truncGE.instHasHomology`：∀ {ι : Type u_1} {ι' : Type 
u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : Catego
ryTheory.Category.{v_1, u_3} C] …
· 使用定理 `ComplexShape.instIsTruncGENatIntEmbeddingUpIntGE`：∀ (p : ℤ), (ComplexSha
pe.embeddingUpIntGE p).IsTruncGE
· 使用引理 `CochainComplex.quasiIso_truncGEMap_iff`：quasiIso_truncGEMap_iff : QuasiI
so (truncGEMap φ n) ↔ forall (i : Int) (_ : n <= i), QuasiIsoAt φ i
· 使用定理 `QuasiIso.quasiIsoAt`：∀ {ι : Type u_1} {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C}   {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C} {c : 
ComplexSh…
· 使用定理 `HomologicalComplex.instIsStrictlySupportedTruncGE`：∀ {ι : Type u_1} {ι' 
: Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst :
 CategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `DerivedCategory.instIsIsoMapCochainComplexIntQOfQuasiIso`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]  
 [inst_2 : HasDerivedCategory C] {K L : Cochai…
· 使用定理 `CochainComplex.instQuasiIsoIntπTruncGEOfIsGE`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   (K : CochainComplex C ℤ…
· 使用定理 `HomologicalComplex.instIsSupportedOfIsStrictlySupported`：∀ {ι : Type u_1
} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [
inst : CategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用引理 `CochainComplex.πTruncGE_naturality`：πTruncGE_naturality (n : Int) : K.πT
runcGE n ≫ truncGEMap φ n = φ ≫ L.πTruncGE n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.inv.congr_simp`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (f f_1 : X ⟶ Y) (e_f : f = f_1)   [I : CategoryTheory.
IsIso f], CategoryT…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.instIsSplitMonoMap`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {X Y : C} (f : Y ⟶…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
Any morphism `f : Q.obj X ⟶ Q.obj Y` in the derived category with `Y` strictly `
≥ n`
can be written as `f = Q.map g ≫ inv (Q.map s)` with `g : X ⟶ Y'` and `s : Y ⟶ Y
'`
a quasi-isomorphism with `Y'` strictly `≥ n`.
-/
lemma left_fac_of_isStrictlyGE {X Y : CochainComplex C ℤ} (f : Q.obj X ⟶ Q.obj Y) (n : ℤ)
    [Y.IsStrictlyGE n] :
    ∃ (Y' : CochainComplex C ℤ) (_ : Y'.IsStrictlyGE n) (g : X ⟶ Y') (s : Y ⟶ Y')
      (_ : IsIso (Q.map s)), f = Q.map g ≫ inv (Q.map s) := by
  obtain ⟨Y', g, s, hs, rfl⟩ := left_fac f
  have : IsIso (Q.map (CochainComplex.truncGEMap s n)) := by
    rw [isIso_Q_map_iff_quasiIso, CochainComplex.quasiIso_truncGEMap_iff]
    rw [isIso_Q_map_iff_quasiIso] at hs
    infer_instance
  refine ⟨Y'.truncGE n, inferInstance, X.πTruncGE n ≫ CochainComplex.truncGEMap g n,
    Y.πTruncGE n ≫ CochainComplex.truncGEMap s n, ?_, ?_⟩
  · rw [Q.map_comp]
    infer_instance
  · have eq := Q.congr_map (CochainComplex.πTruncGE_naturality s n)
    have eq' := Q.congr_map (CochainComplex.πTruncGE_naturality g n)
    simp only [Functor.map_comp] at eq eq'
    simp only [Functor.map_comp, ← cancel_mono (Q.map (CochainComplex.πTruncGE Y n)
      ≫ Q.map (CochainComplex.truncGEMap s n)), assoc, IsIso.inv_hom_id, comp_id]
    simp only [eq, IsIso.inv_hom_id_assoc, eq']

/-- Any morphism `f : Q.obj X ⟶ Q.obj Y` in the derived category
with `X` strictly `≥ a` and `≤ b`, and `Y` strictly `≥ a`
can be written as `f = inv (Q.map s) ≫ Q.map g` with `s : X' ⟶ X`
a quasi-isomorphism with `X'` strictly `≥ a` and `≤ b`, and `g : X' ⟶ Y`. -/
/-
**DerivedCategory.right_fac_of_isStrictlyLE_of_isStrictlyGE** 是 Mathlib 中的一个引理，位
于命名空间 `DerivedCategory`。
形式化陈述：right_fac_of_isStrictlyLE_of_isStrictlyGE {X Y : CochainComplex C Int} (a 
b : Int) [X.IsStrictlyGE a] [X.IsStrictlyLE b] [Y.IsStrictlyGE a] (f : Q.obj X ⟶
 Q.obj Y) : exists (X' : CochainComplex C Int) (_ : X'.IsStrictlyGE a) (_ : X'.I
sStrictlyLE b) (s : X' ⟶ X) (_ : IsIso (Q.map s)) (g : X' ⟶ Y), f = inv (Q.map s
) ≫ Q.map g
参数：a b : Int；f : Q.obj X ⟶ Q.obj Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `DerivedCategory.right_fac_of_isStrictlyLE`：right_fac_of_isStrictlyLE {X 
Y : CochainComplex C Int} (f : Q.obj X ⟶ Q.obj Y) (n : Int) [X.IsStrictlyLE n] :
 exists (X' : CochainComplex C …
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
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
· 使用定理 `HomologicalComplex.truncGE.instHasHomology`：∀ {ι : Type u_1} {ι' : Type 
u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : Catego
ryTheory.Category.{v_1, u_3} C] …
· 使用定理 `ComplexShape.instIsTruncGENatIntEmbeddingUpIntGE`：∀ (p : ℤ), (ComplexSha
pe.embeddingUpIntGE p).IsTruncGE
· 使用引理 `CochainComplex.quasiIso_truncGEMap_iff`：quasiIso_truncGEMap_iff : QuasiI
so (truncGEMap φ n) ↔ forall (i : Int) (_ : n <= i), QuasiIsoAt φ i
· 使用定理 `QuasiIso.quasiIsoAt`：∀ {ι : Type u_1} {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C}   {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C} {c : 
ComplexSh…
· 使用定理 `HomologicalComplex.instIsStrictlySupportedTruncGE`：∀ {ι : Type u_1} {ι' 
: Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst :
 CategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `HomologicalComplex.instIsStrictlySupportedTruncGE_1`：∀ {ι : Type u_1} {ι
' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst
 : CategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `CochainComplex.instIsIsoIntπTruncGEOfIsStrictlyGE`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   (K : CochainComplex C ℤ…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `DerivedCategory.instIsIsoMapCochainComplexIntQOfQuasiIso`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]  
 [inst_2 : HasDerivedCategory C] {K L : Cochai…
· 使用定理 `quasiIso_of_isIso`：∀ {ι : Type u_1} {C : Type u} [inst : CategoryTheory.
Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {c : Co
mplexSh…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
· 使用定理 `CategoryTheory.inv.congr_simp`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (f f_1 : X ⟶ Y) (e_f : f = f_1)   [I : CategoryTheory.
IsIso f], CategoryT…
· 使用定理 `CategoryTheory.IsIso.inv_comp`：inv_comp [IsIso f] [IsIso h] : inv (f ≫ h
) = inv h ≫ inv f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.IsIso.inv_inv`：inv_inv [IsIso f] : inv (inv f) = f
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : X ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Any morphism `f : Q.obj X ⟶ Q.obj Y` in the derived category
with `X` strictly `≥ a` and `≤ b`, and `Y` strictly `≥ a`
can be written as `f = inv (Q.map s) ≫ Q.map g` with `s : X' ⟶ X`
a quasi-isomorphism with `X'` strictly `≥ a` and `≤ b`, and `g : X' ⟶ Y`.
-/
lemma right_fac_of_isStrictlyLE_of_isStrictlyGE
    {X Y : CochainComplex C ℤ} (a b : ℤ) [X.IsStrictlyGE a] [X.IsStrictlyLE b]
    [Y.IsStrictlyGE a] (f : Q.obj X ⟶ Q.obj Y) :
    ∃ (X' : CochainComplex C ℤ) (_ : X'.IsStrictlyGE a) (_ : X'.IsStrictlyLE b)
    (s : X' ⟶ X) (_ : IsIso (Q.map s)) (g : X' ⟶ Y), f = inv (Q.map s) ≫ Q.map g := by
  obtain ⟨X', hX', s, hs, g, fac⟩ := right_fac_of_isStrictlyLE f b
  have : IsIso (Q.map (CochainComplex.truncGEMap s a)) := by
    rw [isIso_Q_map_iff_quasiIso] at hs
    rw [isIso_Q_map_iff_quasiIso, CochainComplex.quasiIso_truncGEMap_iff]
    infer_instance
  refine ⟨X'.truncGE a, inferInstance, inferInstance,
    CochainComplex.truncGEMap s a ≫ inv (X.πTruncGE a), ?_,
      CochainComplex.truncGEMap g a ≫ inv (Y.πTruncGE a), ?_⟩
  · rw [Q.map_comp]
    infer_instance
  · simp only [Functor.map_comp, Functor.map_inv, IsIso.inv_comp, IsIso.inv_inv, assoc, fac,
      ← cancel_epi (Q.map s), IsIso.hom_inv_id_assoc]
    rw [← Functor.map_comp_assoc, ← CochainComplex.πTruncGE_naturality s a,
      Functor.map_comp, assoc, IsIso.hom_inv_id_assoc,
      ← Functor.map_comp_assoc, CochainComplex.πTruncGE_naturality g a,
      Functor.map_comp, assoc, IsIso.hom_inv_id, comp_id]

/-- Any morphism `f : Q.obj X ⟶ Q.obj Y` in the derived category
with `X` strictly `≤ b`, and `Y` strictly `≥ a` and `≤ b`
can be written as `f = Q.map g ≫ inv (Q.map s)` with `g : X ⟶ Y'` and
`s : Y ⟶ Y'` a quasi-isomorphism with `Y'` strictly `≥ a` and `≤ b`. -/
/-
**DerivedCategory.left_fac_of_isStrictlyLE_of_isStrictlyGE** 是 Mathlib 中的一个引理，位于
命名空间 `DerivedCategory`。
形式化陈述：left_fac_of_isStrictlyLE_of_isStrictlyGE {X Y : CochainComplex C Int} (a b
 : Int) [X.IsStrictlyLE b] [Y.IsStrictlyGE a] [Y.IsStrictlyLE b] (f : Q.obj X ⟶ 
Q.obj Y) : exists (Y' : CochainComplex C Int) (_ : Y'.IsStrictlyGE a) (_ : Y'.Is
StrictlyLE b) (g : X ⟶ Y') (s : Y ⟶ Y') (_ : IsIso (Q.map s)), f = Q.map g ≫ inv
 (Q.map s)
参数：a b : Int；f : Q.obj X ⟶ Q.obj Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `DerivedCategory.left_fac_of_isStrictlyGE`：left_fac_of_isStrictlyGE {X Y 
: CochainComplex C Int} (f : Q.obj X ⟶ Q.obj Y) (n : Int) [Y.IsStrictlyGE n] : e
xists (Y' : CochainComplex C I…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
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
· 使用定理 `HomologicalComplex.instHasHomologyTruncLE`：∀ {ι : Type u_1} {ι' : Type u
_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : Categor
yTheory.Category.{v_1, u_3} C] …
· 使用定理 `ComplexShape.instIsTruncLENatIntEmbeddingUpIntLE`：∀ (p : ℤ), (ComplexSha
pe.embeddingUpIntLE p).IsTruncLE
· 使用引理 `CochainComplex.quasiIso_truncLEMap_iff`：quasiIso_truncLEMap_iff : QuasiI
so (truncLEMap φ n) ↔ forall (i : Int) (_ : i <= n), QuasiIsoAt φ i
· 使用定理 `QuasiIso.quasiIsoAt`：∀ {ι : Type u_1} {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C}   {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C} {c : 
ComplexSh…
· 使用定理 `HomologicalComplex.instIsStrictlySupportedTruncLE_1`：∀ {ι : Type u_1} {ι
' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst
 : CategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `HomologicalComplex.instIsStrictlySupportedTruncLE`：∀ {ι : Type u_1} {ι' 
: Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst :
 CategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `CochainComplex.instIsIsoIntιTruncLEOfIsStrictlyLE`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   (K : CochainComplex C ℤ…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `DerivedCategory.instIsIsoMapCochainComplexIntQOfQuasiIso`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]  
 [inst_2 : HasDerivedCategory C] {K L : Cochai…
· 使用定理 `quasiIso_of_isIso`：∀ {ι : Type u_1} {C : Type u} [inst : CategoryTheory.
Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {c : Co
mplexSh…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
· 使用定理 `CategoryTheory.inv.congr_simp`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (f f_1 : X ⟶ Y) (e_f : f = f_1)   [I : CategoryTheory.
IsIso f], CategoryT…
· 使用定理 `CategoryTheory.IsIso.inv_comp`：inv_comp [IsIso f] [IsIso h] : inv (f ≫ h
) = inv h ≫ inv f
· 使用定理 `CategoryTheory.IsIso.inv_inv`：inv_inv [IsIso f] : inv (inv f) = f
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
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
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
Any morphism `f : Q.obj X ⟶ Q.obj Y` in the derived category
with `X` strictly `≤ b`, and `Y` strictly `≥ a` and `≤ b`
can be written as `f = Q.map g ≫ inv (Q.map s)` with `g : X ⟶ Y'` and
`s : Y ⟶ Y'` a quasi-isomorphism with `Y'` strictly `≥ a` and `≤ b`.
-/
lemma left_fac_of_isStrictlyLE_of_isStrictlyGE
    {X Y : CochainComplex C ℤ} (a b : ℤ)
    [X.IsStrictlyLE b] [Y.IsStrictlyGE a] [Y.IsStrictlyLE b] (f : Q.obj X ⟶ Q.obj Y) :
    ∃ (Y' : CochainComplex C ℤ) (_ : Y'.IsStrictlyGE a) (_ : Y'.IsStrictlyLE b)
    (g : X ⟶ Y') (s : Y ⟶ Y') (_ : IsIso (Q.map s)), f = Q.map g ≫ inv (Q.map s) := by
  obtain ⟨Y', hY', g, s, hs, fac⟩ := left_fac_of_isStrictlyGE f a
  have : IsIso (Q.map (CochainComplex.truncLEMap s b)) := by
    rw [isIso_Q_map_iff_quasiIso] at hs
    rw [isIso_Q_map_iff_quasiIso, CochainComplex.quasiIso_truncLEMap_iff]
    infer_instance
  refine ⟨Y'.truncLE b, inferInstance, inferInstance,
    inv (X.ιTruncLE b) ≫ CochainComplex.truncLEMap g b,
    inv (Y.ιTruncLE b) ≫ CochainComplex.truncLEMap s b, ?_, ?_⟩
  · rw [Q.map_comp]
    infer_instance
  · simp only [Functor.map_comp, Functor.map_inv, IsIso.inv_comp, IsIso.inv_inv, assoc, fac,
      ← cancel_mono (Q.map s), IsIso.inv_hom_id, comp_id]
    rw [← Functor.map_comp, ← CochainComplex.ιTruncLE_naturality s b,
      Functor.map_comp, IsIso.inv_hom_id_assoc,
      ← Functor.map_comp, CochainComplex.ιTruncLE_naturality g b,
      Functor.map_comp, IsIso.inv_hom_id_assoc]
/-
**DerivedCategory.subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE** 是 Mathlib 中
的一个引理，位于命名空间 `DerivedCategory`。
形式化陈述：subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE (X Y : CochainComplex C I
nt) (a b : Int) (h : a < b) [X.IsStrictlyLE a] [Y.IsStrictlyGE b] : Subsingleton
 (Q.obj X ⟶ Q.obj Y)
参数：X Y : CochainComplex C Int；a b : Int；h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `DerivedCategory.right_fac_of_isStrictlyLE`：right_fac_of_isStrictlyLE {X 
Y : CochainComplex C Int} (f : Q.obj X ⟶ Q.obj Y) (n : Int) [X.IsStrictlyLE n] :
 exists (X' : CochainComplex C …
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
· 使用引理 `CochainComplex.isZero_of_isStrictlyLE`：isZero_of_isStrictlyLE (n i : Int
) (hi : n < i
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_tgt`：eq_of_tgt (hX : IsZero X) (f g :
 Y ⟶ X) : f = g
· 使用引理 `CochainComplex.isZero_of_isStrictlyGE`：isZero_of_isStrictlyGE (n i : Int
) (hi : i < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `DerivedCategory.instAdditiveCochainComplexIntQ`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 :
 HasDerivedCategory C], DerivedCateg…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE (X Y : CochainComplex C ℤ)
    (a b : ℤ) (h : a < b) [X.IsStrictlyLE a] [Y.IsStrictlyGE b] :
    Subsingleton (Q.obj X ⟶ Q.obj Y) := by
  suffices ∀ (f : Q.obj X ⟶ Q.obj Y), f = 0 from ⟨by simp [this]⟩
  intro f
  obtain ⟨X', _, s, _, g, rfl⟩ := right_fac_of_isStrictlyLE f a
  have : g = 0 := by
    ext i
    by_cases hi : a < i
    · apply (X'.isZero_of_isStrictlyLE a i hi).eq_of_src
    · apply (Y.isZero_of_isStrictlyGE b i (by lia)).eq_of_tgt
  rw [this, Q.map_zero, comp_zero]

end DerivedCategory

