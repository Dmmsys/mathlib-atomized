/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-! # The triangulated structure on the homotopy category of complexes

In this file, we show that for any additive category `C`,
the pretriangulated category `HomotopyCategory C (ComplexShape.up ℤ)` is triangulated.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits Pretriangulated ComposableArrows

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737

universe v

variable {C : Type*} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {X₁ X₂ X₃ : CochainComplex C ℤ} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)

namespace CochainComplex

open HomComplex mappingCone

/-- Given two composable morphisms `f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` in the category
of cochain complexes, this is the canonical triangle
`mappingCone f ⟶ mappingCone (f ≫ g) ⟶ mappingCone g ⟶ (mappingCone f)⟦1⟧`. -/
@[simps! mor₁ mor₂ mor₃ obj₁ obj₂ obj₃]
/-
**CochainComplex.mappingConeCompTriangle** 是 Mathlib 中的一个定义，位于命名空间 `CochainCompl
ex`。
形式化陈述：mappingConeCompTriangle : Triangle (CochainComplex C Int)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two composable morphisms `f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` in the category
of cochain complexes, this is the canonical triangle
`mappingCone f ⟶ mappingCone (f ≫ g) ⟶ mappingCone g ⟶ (mappingCone f)⟦1⟧`.
-/
noncomputable def mappingConeCompTriangle : Triangle (CochainComplex C ℤ) :=
  Triangle.mk (map f (f ≫ g) (𝟙 X₁) g (by rw [id_comp]))
    (map (f ≫ g) g f (𝟙 X₃) (by rw [comp_id]))
    ((triangle g).mor₃ ≫ (inr f)⟦1⟧')

/-- Given two composable morphisms `f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` in the category
of cochain complexes, this is the canonical triangle
`mappingCone f ⟶ mappingCone (f ≫ g) ⟶ mappingCone g ⟶ (mappingCone f)⟦1⟧`
in the homotopy category. It is a distinguished triangle,
see `HomotopyCategory.mappingConeCompTriangleh_distinguished`. -/
/-
**CochainComplex.mappingConeCompTriangleh** 是 Mathlib 中的一个定义，位于命名空间 `CochainComp
lex`。
形式化陈述：mappingConeCompTriangleh : Triangle (HomotopyCategory C (ComplexShape.up I
nt))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two composable morphisms `f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` in the category
of cochain complexes, this is the canonical triangle
`mappingCone f ⟶ mappingCone (f ≫ g) ⟶ mappingCone g ⟶ (mappingCone f)⟦1⟧`
in the homotopy category. It is a distinguished triangle,
see `HomotopyCategory.mappingConeCompTriangleh_distinguished`.
-/
noncomputable def mappingConeCompTriangleh :
    Triangle (HomotopyCategory C (ComplexShape.up ℤ)) :=
  (HomotopyCategory.quotient _ _).mapTriangle.obj (mappingConeCompTriangle f g)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CochainComplex.mappingConeCompTriangle_mor** 是 Mathlib 中的一个引理，位于命名空间 `CochainC
omplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mappingConeCompTriangle_mor₃_naturality {Y₁ Y₂ Y₃ : CochainComplex C ℤ} (f' : Y₁ ⟶ Y₂)
    (g' : Y₂ ⟶ Y₃) (φ : mk₂ f g ⟶ mk₂ f' g') :
    map g g' (φ.app 1) (φ.app 2) (naturality' φ 1 2) ≫ (mappingConeCompTriangle f' g').mor₃ =
      (mappingConeCompTriangle f g).mor₃ ≫
        (map f f' (φ.app 0) (φ.app 1) (naturality' φ 0 1))⟦1⟧' := by
  ext n
  dsimp [map]
  -- the following list of lemmas was obtained by doing simp? [ext_from_iff _ (n + 1) _ rfl]
  simp only [Int.reduceNeg, Fin.isValue, assoc, inr_f_desc_f, HomologicalComplex.comp_f,
    ext_from_iff _ (n + 1) _ rfl, inl_v_desc_f_assoc, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    inl_v_triangle_mor₃_f_assoc, triangle_obj₁, shiftFunctor_obj_X', shiftFunctor_obj_X,
    shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, Preadditive.neg_comp,
    id_comp, Preadditive.comp_neg, inr_f_desc_f_assoc, inr_f_triangle_mor₃_f_assoc, zero_comp,
    comp_zero, and_self]

namespace MappingConeCompHomotopyEquiv

set_option backward.isDefEq.respectTransparency false in
/-- Given two composable morphisms `f` and `g` in the category of cochain complexes, this
is the canonical morphism (which is a homotopy equivalence) from `mappingCone g` to
the mapping cone of the morphism `mappingCone f ⟶ mappingCone (f ≫ g)`. -/
/-
**CochainComplex.MappingConeCompHomotopyEquiv.hom** 是 Mathlib 中的一个定义，位于命名空间 `Coc
hainComplex.MappingConeCompHomotopyEquiv`。
形式化陈述：hom : mappingCone g ⟶ mappingCone (mappingConeCompTriangle f g).mor₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two composable morphisms `f` and `g` in the category of cochain complexes,
 this
is the canonical morphism (which is a homotopy equivalence) from `mappingCone g`
 to
the mapping cone of the morphism `mappingCone f ⟶ mappingCone (f ≫ g)`.
-/
noncomputable def hom :
    mappingCone g ⟶ mappingCone (mappingConeCompTriangle f g).mor₁ :=
  lift _ (descCocycle g (Cochain.ofHom (inr f)) 0 (zero_add 1) (by simp))
    (descCochain _ 0 (Cochain.ofHom (inr (f ≫ g))) (neg_add_cancel 1)) (by
      ext p _ rfl
      dsimp [mappingConeCompTriangle, map]
      simp [ext_from_iff _ _ _ rfl, inl_v_d_assoc _ (p + 1) p (p + 2) (by lia) (by lia)])

set_option backward.isDefEq.respectTransparency false in
/-- Given two composable morphisms `f` and `g` in the category of cochain complexes, this
is the canonical morphism (which is a homotopy equivalence) from the mapping cone of
the morphism `mappingCone f ⟶ mappingCone (f ≫ g)` to `mappingCone g`. -/
/-
**CochainComplex.MappingConeCompHomotopyEquiv.inv** 是 Mathlib 中的一个定义，位于命名空间 `Coc
hainComplex.MappingConeCompHomotopyEquiv`。
形式化陈述：inv : mappingCone (mappingConeCompTriangle f g).mor₁ ⟶ mappingCone g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two composable morphisms `f` and `g` in the category of cochain complexes,
 this
is the canonical morphism (which is a homotopy equivalence) from the mapping con
e of
the morphism `mappingCone f ⟶ mappingCone (f ≫ g)` to `mappingCone g`.
-/
noncomputable def inv : mappingCone (mappingConeCompTriangle f g).mor₁ ⟶ mappingCone g :=
  desc _ ((snd f).comp (inl g) (zero_add (-1)))
    (desc _ ((Cochain.ofHom f).comp (inl g) (zero_add (-1))) (inr g) (by simp)) (by
      ext p
      rw [ext_from_iff _ (p + 1) _ rfl, ext_to_iff _ _ (p + 1) rfl]
      simp [map, δ_zero_cochain_comp,
        Cochain.comp_v _ _ (add_neg_cancel 1) p (p + 1) p (by lia) (by lia)])

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CochainComplex.MappingConeCompHomotopyEquiv.hom_inv_id** 是 Mathlib 中的一个引理，位于命名
空间 `CochainComplex.MappingConeCompHomotopyEquiv`。
形式化陈述：hom_inv_id : hom f g ≫ inv f g = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `CochainComplex.instHasHomotopyCofiberOfHasBinaryBiproductXHAddOfNat`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheo
ry.Preadditive C] {ι : Type u_3}   [inst_2 : AddRightCanc…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.mappingCone.lift_desc_f`：lift_desc_f {K L : CochainComple
x C Int} (α : Cocycle K F 1) (β : Cochain K G 0) (eq : δ 0 1 β + α.1.comp (Cocha
in.ofHom φ) (add_zero 1) = 0…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CochainComplex.HomComplex.Cochain.v.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} {n : ℤ} (γ γ_1…
· 使用定理 `CochainComplex.mappingCone.descCocycle_coe`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} (φ : F ⟶ G…
· 使用引理 `CochainComplex.HomComplex.Cochain.zero_cochain_comp_v`：zero_cochain_comp
_v (z₁ : Cochain F G 0) (z₂ : Cochain G K n) (p q : Int) (hpq : p + n = q) : (z₁
.comp z₂ (zero_add n)).v p q hpq = z₁.v p p…
· 使用引理 `CochainComplex.mappingCone.ext_from_iff`：ext_from_iff (i j : Int) (hij :
 j + 1 = i) {A : C} (f g : (mappingCone φ).X j ⟶ A) : f = g ↔ (inl φ).v i j (by 
lia) ≫ f = (inl φ).v i j (by …
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `CochainComplex.mappingCone.inl_v_descCochain_v_assoc`：∀ {C : Type u_1} [
inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive 
C]   {F G : CochainComplex C ℤ} (φ : F ⟶ G…
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用定理 `CochainComplex.mappingCone.inr_f_snd_v_assoc`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {F 
G : CochainComplex C ℤ} (φ : F ⟶ G…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CochainComplex.mappingCone.inr_f_descCochain_v_assoc`：∀ {C : Type u_1} [
inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive 
C]   {F G : CochainComplex C ℤ} (φ : F ⟶ G…
· 使用引理 `CochainComplex.mappingCone.inr_f_desc_f`：inr_f_desc_f (p : Int) : (inr φ
).f p ≫ (desc φ α β eq).f p = β.f p
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma hom_inv_id : hom f g ≫ inv f g = 𝟙 _ := by
  ext n
  simp [hom, inv, lift_desc_f _ _ _ _ _ _ _ n (n + 1) rfl, ext_from_iff _ (n + 1) _ rfl]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given two composable morphisms `f` and `g` in the category of cochain complexes,
this is the `homotopyInvHomId` field of the homotopy equivalence
`mappingConeCompHomotopyEquiv f g` between `mappingCone g` and the mapping cone of
the morphism `mappingCone f ⟶ mappingCone (f ≫ g)`. -/
/-
**CochainComplex.MappingConeCompHomotopyEquiv.homotopyInvHomId** 是 Mathlib 中的一个定
义，位于命名空间 `CochainComplex.MappingConeCompHomotopyEquiv`。
形式化陈述：homotopyInvHomId : Homotopy (inv f g ≫ hom f g) (𝟙 _)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given two composable morphisms `f` and `g` in the category of cochain complexes,
this is the `homotopyInvHomId` field of the homotopy equivalence
`mappingConeCompHomotopyEquiv f g` between `mappingCone g` and the mapping cone 
of
the morphism `mappingCone f ⟶ mappingCone (f ≫ g)`.
-/
noncomputable def homotopyInvHomId : Homotopy (inv f g ≫ hom f g) (𝟙 _) :=
  (Cochain.equivHomotopy _ _).symm ⟨-((snd _).comp ((fst (f ≫ g)).1.comp
    ((inl f).comp (inl _) (by decide)) (show 1 + (-2) = -1 by decide)) (zero_add (-1))), by
      rw [δ_neg, δ_zero_cochain_comp _ _ _ (neg_add_cancel 1),
        Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul,
        δ_comp _ _ (show 1 + (-2) = -1 by decide) 2 (-1) 0 (by decide)
          (by decide) (by decide),
        δ_comp _ _ (show (-1) + (-1) = -2 by decide) 0 0 (-1) (by decide)
          (by decide) (by decide), Int.negOnePow_neg, Int.negOnePow_neg,
        Int.negOnePow_even 2 ⟨1, by decide⟩, Int.negOnePow_one, Units.neg_smul,
        one_smul, one_smul, δ_inl, δ_inl, δ_snd, Cocycle.δ_eq_zero, Cochain.zero_comp, add_zero,
        Cochain.neg_comp, neg_neg]
      ext n
      rw [ext_from_iff _ (n + 1) n rfl, ext_from_iff _ (n + 1) n rfl,
        ext_from_iff _ (n + 2) (n + 1) (by lia)]
      dsimp [hom, inv]
      simp [ext_to_iff _ n (n + 1) rfl, map, Cochain.comp_v _ _
          (add_neg_cancel 1) n (n + 1) n (by lia) (by lia),
        Cochain.comp_v _ _ (show 1 + -2 = -1 by decide) (n + 1) (n + 2) n
          (by lia) (by lia),
        Cochain.comp_v _ _ (show (-1) + -1 = -2 by decide) (n + 2) (n + 1) n
          (by lia) (by lia)]⟩

end MappingConeCompHomotopyEquiv

/-- Given two composable morphisms `f` and `g` in the category of cochain complexes,
this is the homotopy equivalence `mappingConeCompHomotopyEquiv f g`
between `mappingCone g` and the mapping cone of
the morphism `mappingCone f ⟶ mappingCone (f ≫ g)`. -/
/-
**CochainComplex.mappingConeCompHomotopyEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Cochain
Complex`。
形式化陈述：mappingConeCompHomotopyEquiv : HomotopyEquiv (mappingCone g) (mappingCone 
(mappingConeCompTriangle f g).mor₁) where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two composable morphisms `f` and `g` in the category of cochain complexes,
this is the homotopy equivalence `mappingConeCompHomotopyEquiv f g`
between `mappingCone g` and the mapping cone of
the morphism `mappingCone f ⟶ mappingCone (f ≫ g)`.
-/
noncomputable def mappingConeCompHomotopyEquiv : HomotopyEquiv (mappingCone g)
    (mappingCone (mappingConeCompTriangle f g).mor₁) where
  hom := MappingConeCompHomotopyEquiv.hom f g
  inv := MappingConeCompHomotopyEquiv.inv f g
  homotopyHomInvId := Homotopy.ofEq (by simp)
  homotopyInvHomId := MappingConeCompHomotopyEquiv.homotopyInvHomId f g

@[reassoc (attr := simp)]
/-
**CochainComplex.mappingConeCompHomotopyEquiv_hom_inv_id** 是 Mathlib 中的一个引理，位于命名
空间 `CochainComplex`。
形式化陈述：mappingConeCompHomotopyEquiv_hom_inv_id : (mappingConeCompHomotopyEquiv f 
g).hom ≫ (mappingConeCompHomotopyEquiv f g).inv = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CochainComplex.instHasHomotopyCofiberOfHasBinaryBiproductXHAddOfNat`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheo
ry.Preadditive C] {ι : Type u_3}   [inst_2 : AddRightCanc…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.MappingConeCompHomotopyEquiv.hom_inv_id`：hom_inv_id : hom
 f g ≫ inv f g = 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mappingConeCompHomotopyEquiv_hom_inv_id :
    (mappingConeCompHomotopyEquiv f g).hom ≫
      (mappingConeCompHomotopyEquiv f g).inv = 𝟙 _ := by
  simp [mappingConeCompHomotopyEquiv]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CochainComplex.mappingConeCompHomotopyEquiv_comm** 是 Mathlib 中的一个引理，位于命名空间 `Co
chainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mappingConeCompHomotopyEquiv_comm₁ :
    inr (map f (f ≫ g) (𝟙 X₁) g (by rw [id_comp])) ≫
      (mappingConeCompHomotopyEquiv f g).inv = (mappingConeCompTriangle f g).mor₂ := by
  simp [map, mappingConeCompHomotopyEquiv, MappingConeCompHomotopyEquiv.inv]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CochainComplex.mappingConeCompHomotopyEquiv_comm** 是 Mathlib 中的一个引理，位于命名空间 `Co
chainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mappingConeCompHomotopyEquiv_comm₂ :
    (mappingConeCompHomotopyEquiv f g).hom ≫
      (triangle (mappingConeCompTriangle f g).mor₁).mor₃ =
      (mappingConeCompTriangle f g).mor₃ := by
  ext n
  simp [mappingConeCompHomotopyEquiv, MappingConeCompHomotopyEquiv.hom,
    lift_f _ _ _ _ _ (n + 1) rfl, ext_from_iff _ (n + 1) _ rfl]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CochainComplex.mappingConeCompTriangleh_comm** 是 Mathlib 中的一个引理，位于命名空间 `Cochai
nComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mappingConeCompTriangleh_comm₁ :
    (mappingConeCompTriangleh f g).mor₂ ≫
      (HomotopyCategory.quotient _ _).map (mappingConeCompHomotopyEquiv f g).hom =
    (HomotopyCategory.quotient _ _).map (mappingCone.inr _) := by
  rw [← cancel_mono (HomotopyCategory.isoOfHomotopyEquiv
      (mappingConeCompHomotopyEquiv f g)).inv, assoc]
  dsimp [mappingConeCompTriangleh]
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    mappingConeCompHomotopyEquiv_hom_inv_id, comp_id,
    mappingConeCompHomotopyEquiv_comm₁ f g,
    mappingConeCompTriangle_mor₂]

end CochainComplex

namespace HomotopyCategory

open CochainComplex

variable [HasZeroObject C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**HomotopyCategory.mappingConeCompTriangleh_distinguished** 是 Mathlib 中的一个引理，位于命
名空间 `HomotopyCategory`。
形式化陈述：mappingConeCompTriangleh_distinguished : (mappingConeCompTriangleh f g) in
 distTriang (HomotopyCategory C (ComplexShape.up Int))
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CochainComplex.instHasHomotopyCofiberOfHasBinaryBiproductXHAddOfNat`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheo
ry.Preadditive C] {ι : Type u_3}   [inst_2 : AddRightCanc…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用引理 `CochainComplex.mappingConeCompTriangleh_comm₁`：mappingConeCompTriangleh_
comm₁ : (mappingConeCompTriangleh f g).mor₂ ≫ (HomotopyCategory.quotient _ _).ma
p (mappingConeCompHomotopyEquiv f g…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用引理 `CochainComplex.mappingConeCompHomotopyEquiv_comm₂`：mappingConeCompHomoto
pyEquiv_comm₂ : (mappingConeCompHomotopyEquiv f g).hom ≫ (triangle (mappingConeC
ompTriangle f g).mor₁).mor₃ = (mappingC…
-/
lemma mappingConeCompTriangleh_distinguished :
    (mappingConeCompTriangleh f g) ∈
      distTriang (HomotopyCategory C (ComplexShape.up ℤ)) := by
  refine ⟨_, _, (mappingConeCompTriangle f g).mor₁, ⟨?_⟩⟩
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (isoOfHomotopyEquiv
    (mappingConeCompHomotopyEquiv f g)) (by cat_disch) (by simp) ?_
  dsimp [mappingConeCompTriangleh]
  rw [CategoryTheory.Functor.map_id, comp_id, ← Functor.map_comp_assoc]
  congr 2
  exact (mappingConeCompHomotopyEquiv_comm₂ f g).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : IsTriangulated (HomotopyCategory C (ComplexShape.up ℤ)) :=
  IsTriangulated.mk' (by
    rintro ⟨X₁ : CochainComplex C ℤ⟩ ⟨X₂ : CochainComplex C ℤ⟩ ⟨X₃ : CochainComplex C ℤ⟩ u₁₂' u₂₃'
    obtain ⟨u₁₂, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective u₁₂'
    obtain ⟨u₂₃, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective u₂₃'
    refine ⟨_, _, _, _, _, _, _, _, Iso.refl _, Iso.refl _, Iso.refl _, by simp, by simp,
        _, _, mappingCone_triangleh_distinguished u₁₂,
        _, _, mappingCone_triangleh_distinguished u₂₃,
        _, _, mappingCone_triangleh_distinguished (u₁₂ ≫ u₂₃), ⟨?_⟩⟩
    let α := mappingCone.triangleMap u₁₂ (u₁₂ ≫ u₂₃) (𝟙 X₁) u₂₃ (by rw [id_comp])
    let β := mappingCone.triangleMap (u₁₂ ≫ u₂₃) u₂₃ u₁₂ (𝟙 X₃) (by rw [comp_id])
    refine Triangulated.Octahedron.mk ((HomotopyCategory.quotient _ _).map α.hom₃)
      ((HomotopyCategory.quotient _ _).map β.hom₃) ?_ ?_ ?_ ?_ ?_
    · exact ((quotient _ _).mapTriangle.map α).comm₂
    · exact ((quotient _ _).mapTriangle.map α).comm₃.symm.trans (by dsimp [α]; simp)
    · exact ((quotient _ _).mapTriangle.map β).comm₂.trans (by dsimp [β]; simp)
    · exact ((quotient _ _).mapTriangle.map β).comm₃
    · refine isomorphic_distinguished _ (mappingConeCompTriangleh_distinguished u₁₂ u₂₃) _ ?_
      exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by dsimp [α, mappingConeCompTriangleh]; simp)
        (by dsimp [β, mappingConeCompTriangleh]; simp)
        (by dsimp [mappingConeCompTriangleh]; simp))

end HomotopyCategory

