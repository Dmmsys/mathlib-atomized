/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.FunctorN

/-!

# Comparison with the normalized Moore complex functor

In this file, we show that when the category `A` is abelian,
there is an isomorphism `N₁_iso_normalizedMooreComplex_comp_toKaroubi` between
the functor `N₁ : SimplicialObject A ⥤ Karoubi (ChainComplex A ℕ)`
defined in `FunctorN.lean` and the composition of
`normalizedMooreComplex A` with the inclusion
`ChainComplex A ℕ ⥤ Karoubi (ChainComplex A ℕ)`.

This isomorphism shall be used in `Equivalence.lean` in order to obtain
the Dold-Kan equivalence
`CategoryTheory.Abelian.DoldKan.equivalence : SimplicialObject A ≌ ChainComplex A ℕ`
with a functor (definitionally) equal to `normalizedMooreComplex A`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

@[expose] public section


open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Subobject CategoryTheory.Idempotents DoldKan

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

universe v

variable {A : Type*} [Category* A] [Abelian A] {X : SimplicialObject A}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicTopology.DoldKan.HigherFacesVanish.inclusionOfMooreComplexMap** 是 Mat
hlib 中的一个定理，位于命名空间 `AlgebraicTopology.DoldKan.HigherFacesVanish`。
形式化陈述：∀ {A : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} A] [inst_1 : C
ategoryTheory.Abelian A]   {X : CategoryTheory.SimplicialObject A} (n : ℕ),   Al
gebraicTopology.DoldKan.HigherFacesVanish (n + 1) ((AlgebraicTopology.inclusionO
fMooreComplexMap X).f (n + 1))
参数：n : ℕ；n + 1；(AlgebraicTopology.inclusionOfMooreComplexMap X).f (n + 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Abelian.hasPullbacks`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasPul
lbacks C
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.Subobject.finset_inf_arrow_factors`：finset_inf_arrow_fact
ors {I : Type*} {B : C} (s : Finset I) (P : I -> Subobject B) (i : I) (m : i in 
s) : (P i).Factors (s.inf P).arrow
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow`：factorThru_arrow {X Y : C} (P
 : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : P.factorThru f h ≫ P.arrow = f
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.kernelSubobject_arrow_comp`：kernelSubobject_arrow_
comp : (kernelSubobject f).arrow ≫ f = 0
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
theorem HigherFacesVanish.inclusionOfMooreComplexMap (n : ℕ) :
    HigherFacesVanish (n + 1) ((inclusionOfMooreComplexMap X).f (n + 1)) := fun j _ => by
  dsimp [AlgebraicTopology.inclusionOfMooreComplexMap, NormalizedMooreComplex.objX]
  rw [← factorThru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ j
    (by simp)), assoc, kernelSubobject_arrow_comp, comp_zero]
/-
**AlgebraicTopology.DoldKan.factors_normalizedMooreComplex_PInfty** 是 Mathlib 中的
一个定理，位于命名空间 `AlgebraicTopology.DoldKan`。
形式化陈述：factors_normalizedMooreComplex_PInfty (n : Nat) : Subobject.Factors (Norma
lizedMooreComplex.objX X n) (PInfty.f n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Subobject.top_factors`：top_factors {A B : C} (f : A ⟶ B) 
: (⊤ : Subobject B).Factors f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicTopology.DoldKan.PInfty_f`：PInfty_f (n : Nat) : (PInfty.f n : X
 _⦋n⦌ ⟶ X _⦋n⦌) = (P n).f n
· 使用定理 `CategoryTheory.Abelian.hasPullbacks`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasPul
lbacks C
· 使用定理 `AlgebraicTopology.NormalizedMooreComplex.objX.eq_2`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abelian C]  
 (X : CategoryTheory.SimplicialObject C)…
· 使用定理 `CategoryTheory.Subobject.finset_inf_factors`：finset_inf_factors {I : Typ
e*} {A B : C} {s : Finset I} {P : I -> Subobject B} (f : A ⟶ B) : (s.inf P).Fact
ors f ↔ forall i in s, (P i).Fact…
· 使用定理 `CategoryTheory.Limits.kernelSubobject_factors`：kernelSubobject_factors {
W : C} (h : W ⟶ X) (w : h ≫ f = 0) : (kernelSubobject f).Factors h
· 使用定理 `AlgebraicTopology.DoldKan.HigherFacesVanish.of_P`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]
   {X : CategoryTheory.SimplicialObjec…
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
-/
theorem factors_normalizedMooreComplex_PInfty (n : ℕ) :
    Subobject.Factors (NormalizedMooreComplex.objX X n) (PInfty.f n) := by
  rcases n with _ | n
  · apply top_factors
  · rw [PInfty_f, NormalizedMooreComplex.objX, finset_inf_factors]
    intro i _
    apply kernelSubobject_factors
    exact (HigherFacesVanish.of_P (n + 1) n) i le_add_self

set_option backward.isDefEq.respectTransparency false in
/-- `PInfty` factors through the normalized Moore complex -/
@[simps!]
/-
**AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex** 是 Mathlib 中的一个定义，位于
命名空间 `AlgebraicTopology.DoldKan`。
形式化陈述：PInftyToNormalizedMooreComplex (X : SimplicialObject A) : K[X] ⟶ N[X]
参数：X : SimplicialObject A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicTopology.DoldKan.factors_normalizedMooreComplex_PInfty`：factors
_normalizedMooreComplex_PInfty (n : Nat) : Subobject.Factors (NormalizedMooreCom
plex.objX X n) (PInfty.f n)

--- 原说明 ---
`PInfty` factors through the normalized Moore complex
-/
def PInftyToNormalizedMooreComplex (X : SimplicialObject A) : K[X] ⟶ N[X] :=
  ChainComplex.ofHom
    (fun n => factorThru _ _ (factors_normalizedMooreComplex_PInfty n)) fun n => by
    rw [← cancel_mono (NormalizedMooreComplex.objX X n).arrow, assoc, assoc, factorThru_arrow,
      ← inclusionOfMooreComplexMap_f, NormalizedMooreComplex.obj_d, ChainComplex.of_d,
      ← normalizedMooreComplex_objD, ← (inclusionOfMooreComplexMap X).comm (n + 1) n,
      inclusionOfMooreComplexMap_f, factorThru_arrow_assoc, alternatingFaceMapComplex_obj_d,
      ← alternatingFaceMapComplex_obj_d]
    exact PInfty.comm (n + 1) n

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex_comp_inclusionOfMoore
ComplexMap** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicTopology.DoldKan`。
形式化陈述：PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap (X : Simpli
cialObject A) : PInftyToNormalizedMooreComplex X ≫ inclusionOfMooreComplexMap X 
= PInfty
参数：X : SimplicialObject A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicTopology.DoldKan.factors_normalizedMooreComplex_PInfty`：factors
_normalizedMooreComplex_PInfty (n : Nat) : Subobject.Factors (NormalizedMooreCom
plex.objX X n) (PInfty.f n)
· 使用定理 `AlgebraicTopology.inclusionOfMooreComplexMap_f`：inclusionOfMooreComplexM
ap_f (X : SimplicialObject A) (n : Nat) : (inclusionOfMooreComplexMap X).f n = (
NormalizedMooreComplex.objX X n).arr…
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow`：factorThru_arrow {X Y : C} (P
 : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : P.factorThru f h ≫ P.arrow = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap (X : SimplicialObject A) :
    PInftyToNormalizedMooreComplex X ≫ inclusionOfMooreComplexMap X = PInfty := by cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex_naturality** 是 Mathli
b 中的一个定理，位于命名空间 `AlgebraicTopology.DoldKan`。
形式化陈述：PInftyToNormalizedMooreComplex_naturality {X Y : SimplicialObject A} (f : 
X ⟶ Y) : AlternatingFaceMapComplex.map f ≫ PInftyToNormalizedMooreComplex Y = PI
nftyToNormalizedMooreComplex X ≫ NormalizedMooreComplex.map f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Subobject.eq_of_comp_arrow_eq`：eq_of_comp_arrow_eq {X Y :
 C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g
· 使用定理 `AlgebraicTopology.DoldKan.factors_normalizedMooreComplex_PInfty`：factors
_normalizedMooreComplex_PInfty (n : Nat) : Subobject.Factors (NormalizedMooreCom
plex.objX X n) (PInfty.f n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow`：factorThru_arrow {X Y : C} (P
 : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : P.factorThru f h ≫ P.arrow = f
· 使用定理 `AlgebraicTopology.DoldKan.PInfty_f_naturality`：PInfty_f_naturality (n : 
Nat) {X Y : SimplicialObject C} (f : X ⟶ Y) : f.app (op ⦋n⦌) ≫ PInfty.f n = PInf
ty.f n ≫ f.app (op ⦋n⦌)
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow_assoc`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (P : CategoryTheory.Subobject Y) 
(f : X ⟶ Y)   (h : P.Factors f) {Z : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem PInftyToNormalizedMooreComplex_naturality {X Y : SimplicialObject A} (f : X ⟶ Y) :
    AlternatingFaceMapComplex.map f ≫ PInftyToNormalizedMooreComplex Y =
      PInftyToNormalizedMooreComplex X ≫ NormalizedMooreComplex.map f := by
  cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**AlgebraicTopology.DoldKan.PInfty_comp_PInftyToNormalizedMooreComplex** 是 Mathl
ib 中的一个定理，位于命名空间 `AlgebraicTopology.DoldKan`。
形式化陈述：PInfty_comp_PInftyToNormalizedMooreComplex (X : SimplicialObject A) : PInf
ty ≫ PInftyToNormalizedMooreComplex X = PInftyToNormalizedMooreComplex X
参数：X : SimplicialObject A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Subobject.eq_of_comp_arrow_eq`：eq_of_comp_arrow_eq {X Y :
 C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g
· 使用定理 `AlgebraicTopology.DoldKan.factors_normalizedMooreComplex_PInfty`：factors
_normalizedMooreComplex_PInfty (n : Nat) : Subobject.Factors (NormalizedMooreCom
plex.objX X n) (PInfty.f n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow`：factorThru_arrow {X Y : C} (P
 : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : P.factorThru f h ≫ P.arrow = f
· 使用定理 `AlgebraicTopology.DoldKan.PInfty_f_idem`：PInfty_f_idem (n : Nat) : (PInf
ty.f n : X _⦋n⦌ ⟶ _) ≫ PInfty.f n = PInfty.f n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem PInfty_comp_PInftyToNormalizedMooreComplex (X : SimplicialObject A) :
    PInfty ≫ PInftyToNormalizedMooreComplex X = PInftyToNormalizedMooreComplex X := by cat_disch

@[reassoc (attr := simp)]
/-
**AlgebraicTopology.DoldKan.inclusionOfMooreComplexMap_comp_PInfty** 是 Mathlib 中
的一个定理，位于命名空间 `AlgebraicTopology.DoldKan`。
形式化陈述：inclusionOfMooreComplexMap_comp_PInfty (X : SimplicialObject A) : inclusio
nOfMooreComplexMap X ≫ PInfty = inclusionOfMooreComplexMap X
参数：X : SimplicialObject A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicTopology.DoldKan.HigherFacesVanish.comp_P_eq_self`：comp_P_eq_se
lf {Y : C} {n q : Nat} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ) : φ ≫ (P
 q).f (n + 1) = φ
· 使用定理 `AlgebraicTopology.DoldKan.HigherFacesVanish.inclusionOfMooreComplexMap`：
∀ {A : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} A] [inst_1 : Categor
yTheory.Abelian A]   {X : CategoryTheory.SimplicialObject A}…
-/
theorem inclusionOfMooreComplexMap_comp_PInfty (X : SimplicialObject A) :
    inclusionOfMooreComplexMap X ≫ PInfty = inclusionOfMooreComplexMap X := by
  ext (_ | n)
  · dsimp
    simp only [comp_id]
  · exact (HigherFacesVanish.inclusionOfMooreComplexMap n).comp_P_eq_self

set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicTopology.DoldKan.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicTopology.DoldKa
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mono (inclusionOfMooreComplexMap X) :=
  ⟨fun _ _ hf => by
    ext n
    dsimp
    ext
    exact HomologicalComplex.congr_hom hf n⟩

set_option backward.isDefEq.respectTransparency false in
/-- `inclusionOfMooreComplexMap X` is a split mono. -/
/-
**AlgebraicTopology.DoldKan.splitMonoInclusionOfMooreComplexMap** 是 Mathlib 中的一个
定义，位于命名空间 `AlgebraicTopology.DoldKan`。
形式化陈述：splitMonoInclusionOfMooreComplexMap (X : SimplicialObject A) : SplitMono (
inclusionOfMooreComplexMap X) where retraction
参数：X : SimplicialObject A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`inclusionOfMooreComplexMap X` is a split mono.
-/
def splitMonoInclusionOfMooreComplexMap (X : SimplicialObject A) :
    SplitMono (inclusionOfMooreComplexMap X) where
  retraction := PInftyToNormalizedMooreComplex X
  id := by
    simp only [← cancel_mono (inclusionOfMooreComplexMap X), assoc, id_comp,
      PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap,
      inclusionOfMooreComplexMap_comp_PInfty]

variable (A)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- When the category `A` is abelian,
the functor `N₁ : SimplicialObject A ⥤ Karoubi (ChainComplex A ℕ)` defined
using `PInfty` identifies to the composition of the normalized Moore complex functor
and the inclusion in the Karoubi envelope. -/
/-
**AlgebraicTopology.DoldKan.N** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicTopology.DoldK
an`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When the category `A` is abelian,
the functor `N₁ : SimplicialObject A ⥤ Karoubi (ChainComplex A ℕ)` defined
using `PInfty` identifies to the composition of the normalized Moore complex fun
ctor
and the inclusion in the Karoubi envelope.
-/
def N₁_iso_normalizedMooreComplex_comp_toKaroubi : N₁ ≅ normalizedMooreComplex A ⋙ toKaroubi _ where
  hom :=
    { app := fun X => { f := PInftyToNormalizedMooreComplex X } }
  inv :=
    { app := fun X => { f := inclusionOfMooreComplexMap X } }
  hom_inv_id := by
    ext X : 3
    simp only [PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap,
      NatTrans.comp_app, Karoubi.comp_f, N₁_obj_p, NatTrans.id_app, Karoubi.id_f]
  inv_hom_id := by
    ext X : 3
    rw [← cancel_mono (inclusionOfMooreComplexMap X)]
    simp only [NatTrans.comp_app, Karoubi.comp_f, assoc, NatTrans.id_app, Karoubi.id_f,
      PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap,
      inclusionOfMooreComplexMap_comp_PInfty]
    dsimp only [Functor.comp_obj, toKaroubi]
    rw [id_comp]

end DoldKan

end AlgebraicTopology

