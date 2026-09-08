/-
Copyright (c) 2025 Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# The co-Cartesian monoidal category structure on commutative `R`-algebras

This file provides the co-Cartesian-monoidal category structure on `CommAlgCat R` constructed
explicitly using the tensor product.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Limits TensorProduct Opposite
open Algebra.TensorProduct
open Algebra.TensorProduct (lid rid assoc comm)

noncomputable section

namespace CommAlgCat
universe u v
variable {R : Type u} [CommRing R] {A B C D : CommAlgCat.{u} R}

variable (A B)

/-- The explicit cocone with tensor products as the fibered coproduct in `CommAlgCat`. -/
/-
**CommAlgCat.binaryCofan** 是 Mathlib 中的一个定义，位于命名空间 `CommAlgCat`。
形式化陈述：binaryCofan : BinaryCofan A B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The explicit cocone with tensor products as the fibered coproduct in `CommAlgCat
`.
-/
def binaryCofan : BinaryCofan A B := .mk (ofHom includeLeft) (ofHom <| includeRight (A := A))
/-
**CommAlgCat.binaryCofan_inl** 是 Mathlib 中的一个定理，位于命名空间 `CommAlgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] (A B : CommAlgCat R),   (A.binaryCofan 
B).inl = CommAlgCat.ofHom Algebra.TensorProduct.includeLeft
参数：A B : CommAlgCat R；A.binaryCofan B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma binaryCofan_inl : (binaryCofan A B).inl = ofHom includeLeft := rfl
/-
**CommAlgCat.binaryCofan_inr** 是 Mathlib 中的一个定理，位于命名空间 `CommAlgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] (A B : CommAlgCat R),   (A.binaryCofan 
B).inr = CommAlgCat.ofHom Algebra.TensorProduct.includeRight
参数：A B : CommAlgCat R；A.binaryCofan B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma binaryCofan_inr : (binaryCofan A B).inr = ofHom includeRight := rfl
/-
**CommAlgCat.binaryCofan_pt** 是 Mathlib 中的一个定理，位于命名空间 `CommAlgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] (A B : CommAlgCat R), (A.binaryCofan B)
.pt = CommAlgCat.of R (TensorProduct R ↑A ↑B)
参数：A B : CommAlgCat R；A.binaryCofan B；TensorProduct R ↑A ↑B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma binaryCofan_pt : (binaryCofan A B).pt = .of R (A ⊗[R] B) := rfl

/-- Verify that the pushout cocone is indeed the colimit. -/
/-
**CommAlgCat.binaryCofanIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `CommAlgCat`。
形式化陈述：binaryCofanIsColimit : IsColimit (binaryCofan A B)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Verify that the pushout cocone is indeed the colimit.
-/
def binaryCofanIsColimit : IsColimit (binaryCofan A B) :=
  BinaryCofan.IsColimit.mk _
    (fun f g ↦ ofHom (lift f.hom g.hom fun _ _ ↦ .all _ _))
    (fun f g ↦ by ext1; exact lift_comp_includeLeft _ _ fun _ _ ↦ .all _ _)
    (fun f g ↦ by ext1; exact lift_comp_includeRight _ _ fun _ _ ↦ .all _ _)
    (fun f g m hm₁ hm₂ ↦ by
      ext1
      refine liftEquiv.symm_apply_eq (y := ⟨⟨_, _⟩, fun _ _ ↦ .all _ _⟩).mp ?_
      exact Subtype.ext (Prod.ext congr(($hm₁).hom) congr(($hm₂).hom)))

/-- The initial object of `CommAlgCat R` is `R` as an algebra over itself. -/
/-
**CommAlgCat.isInitialSelf** 是 Mathlib 中的一个定义，位于命名空间 `CommAlgCat`。
形式化陈述：isInitialSelf : IsInitial (of R R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The initial object of `CommAlgCat R` is `R` as an algebra over itself.
-/
def isInitialSelf : IsInitial (of R R) :=
  .ofUniqueHom (fun A ↦ ofHom (Algebra.ofId R A)) fun _ _ ↦ hom_ext (Algebra.ext_id _ _ _)

attribute [local simp] one_def in
/-
**CommAlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonoidalCategory (CommAlgCat.{u} R) where
  tensorObj S T := of R (S ⊗[R] T)
  whiskerLeft _ {_ _} f := ofHom (map (.id _ _) f.hom)
  whiskerRight f T := ofHom (map f.hom (.id _ _))
  tensorHom f g := ofHom (map f.hom g.hom)
  tensorUnit := .of R R
  associator _ _ _ := isoMk (assoc R R R _ _ _)
  leftUnitor _ := isoMk (lid R _)
  rightUnitor _ := isoMk (rid R R _)
/-
**CommAlgCat.coe_tensorUnit** 是 Mathlib 中的一个定理，位于命名空间 `CommAlgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R], ↑(CategoryTheory.MonoidalCategoryStruc
t.tensorUnit (CommAlgCat R)) = R
参数：CategoryTheory.MonoidalCategoryStruct.tensorUnit (CommAlgCat R)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_tensorUnit : 𝟙_ (CommAlgCat.{u} R) = R := rfl
/-
**CommAlgCat.coe_tensorObj** 是 Mathlib 中的一个定理，位于命名空间 `CommAlgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] (A B : CommAlgCat R),   ↑(CategoryTheor
y.MonoidalCategoryStruct.tensorObj A B) = TensorProduct R ↑A ↑B
参数：A B : CommAlgCat R；CategoryTheory.MonoidalCategoryStruct.tensorObj A B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_tensorObj : A ⊗ B = A ⊗[R] B := rfl

variable {A B}
/-
**CommAlgCat.tensorHom_hom** 是 Mathlib 中的一个定理，位于命名空间 `CommAlgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {A B C D : CommAlgCat R} (f : A ⟶ C) (g
 : B ⟶ D),   CommAlgCat.Hom.hom (CategoryTheory.MonoidalCategoryStruct.tensorHom
 f g) =     Algebra.TensorProduct.map (CommAlgCat.Hom.hom f) (CommAlgCat.Hom.hom
 g)
参数：f : A ⟶ C；g : B ⟶ D；CategoryTheory.MonoidalCategoryStruct.tensorHom f g；CommA
lgCat.Hom.hom f；CommAlgCat.Hom.hom g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma tensorHom_hom (f : A ⟶ C) (g : B ⟶ D) : (f ⊗ₘ g).hom = map f.hom g.hom := rfl

variable (C) in
/-
**CommAlgCat.whiskerRight_hom** 是 Mathlib 中的一个定理，位于命名空间 `CommAlgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {A B : CommAlgCat R} (C : CommAlgCat R)
 (f : A ⟶ B),   CommAlgCat.Hom.hom (CategoryTheory.MonoidalCategoryStruct.whiske
rRight f C) =     Algebra.TensorProduct.map (CommAlgCat.Hom.hom f) (AlgHom.id R 
↑C)
参数：C : CommAlgCat R；f : A ⟶ B；CategoryTheory.MonoidalCategoryStruct.whiskerRight
 f C；CommAlgCat.Hom.hom f；AlgHom.id R ↑C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma whiskerRight_hom (f : A ⟶ B) : (f ▷ C).hom = map f.hom (.id _ _) := rfl

variable (C) in
/-
**CommAlgCat.whiskerLeft_hom** 是 Mathlib 中的一个定理，位于命名空间 `CommAlgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {A B : CommAlgCat R} (C : CommAlgCat R)
 (f : A ⟶ B),   CommAlgCat.Hom.hom (CategoryTheory.MonoidalCategoryStruct.whiske
rLeft C f) =     Algebra.TensorProduct.map (AlgHom.id R ↑C) (CommAlgCat.Hom.hom 
f)
参数：C : CommAlgCat R；f : A ⟶ B；CategoryTheory.MonoidalCategoryStruct.whiskerLeft 
C f；AlgHom.id R ↑C；CommAlgCat.Hom.hom f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma whiskerLeft_hom (f : A ⟶ B) : (C ◁ f).hom = map (.id _ _) f.hom := rfl

variable (A B C) in
/-
**CommAlgCat.associator_hom_hom** 是 Mathlib 中的一个定理，位于命名空间 `CommAlgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] (A B C : CommAlgCat R),   CommAlgCat.Ho
m.hom (CategoryTheory.MonoidalCategoryStruct.associator A B C).hom =     ↑(Algeb
ra.TensorProduct.assoc R R R ↑A ↑B ↑C)
参数：A B C : CommAlgCat R；CategoryTheory.MonoidalCategoryStruct.associator A B C；A
lgebra.TensorProduct.assoc R R R ↑A ↑B ↑C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma associator_hom_hom : (α_ A B C).hom.hom = (assoc R R R A B C).toAlgHom := rfl

variable (A B C) in
/-
**CommAlgCat.associator_inv_hom** 是 Mathlib 中的一个定理，位于命名空间 `CommAlgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] (A B C : CommAlgCat R),   CommAlgCat.Ho
m.hom (CategoryTheory.MonoidalCategoryStruct.associator A B C).inv =     ↑(Algeb
ra.TensorProduct.assoc R R R ↑A ↑B ↑C).symm
参数：A B C : CommAlgCat R；CategoryTheory.MonoidalCategoryStruct.associator A B C；A
lgebra.TensorProduct.assoc R R R ↑A ↑B ↑C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma associator_inv_hom : (α_ A B C).inv.hom = (assoc R R R A B C).symm.toAlgHom := rfl
/-
**CommAlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BraidedCategory (CommAlgCat.{u} R) where
  braiding S T := isoMk (comm R _ _)
  braiding_naturality_right := by intros; ext : 1; dsimp; ext <;> rfl
  braiding_naturality_left := by intros; ext : 1; dsimp; ext <;> rfl
  hexagon_forward S T U := by ext : 1; dsimp; ext <;> rfl
  hexagon_reverse S T U := by ext : 1; dsimp; ext <;> rfl

variable (A B) in
/-
**CommAlgCat.braiding_hom_hom** 是 Mathlib 中的一个定理，位于命名空间 `CommAlgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] (A B : CommAlgCat R),   CommAlgCat.Hom.
hom (β_ A B).hom = ↑(Algebra.TensorProduct.comm R ↑A ↑B)
参数：A B : CommAlgCat R；β_ A B；Algebra.TensorProduct.comm R ↑A ↑B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma braiding_hom_hom : (β_ A B).hom.hom = (comm R A B).toAlgHom := rfl

variable (A B) in
/-
**CommAlgCat.braiding_inv_hom** 是 Mathlib 中的一个定理，位于命名空间 `CommAlgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] (A B : CommAlgCat R),   CommAlgCat.Hom.
hom (β_ A B).inv = ↑(Algebra.TensorProduct.comm R ↑B ↑A)
参数：A B : CommAlgCat R；β_ A B；Algebra.TensorProduct.comm R ↑B ↑A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma braiding_inv_hom : (β_ A B).inv.hom = (comm R B A).toAlgHom := rfl

attribute [local ext] Quiver.Hom.unop_inj in
/-
**CommAlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CartesianMonoidalCategory (CommAlgCat.{u} R)ᵒᵖ where
  isTerminalTensorUnit := terminalOpOfInitial isInitialSelf
  fst := _
  snd := _
  tensorProductIsBinaryProduct S T := BinaryCofan.IsColimit.op <| binaryCofanIsColimit S.unop T.unop
  fst_def S T := by ext x; change x ⊗ₜ 1 = x ⊗ₜ algebraMap R T.unop 1; simp
  snd_def S T := by ext x; change 1 ⊗ₜ x = algebraMap R S.unop 1 ⊗ₜ x; simp

variable {A B C D : (CommAlgCat.{u} R)ᵒᵖ}
/-
**CommAlgCat.fst_unop_hom** 是 Mathlib 中的一个定理，位于命名空间 `CommAlgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] (A B : (CommAlgCat R)ᵒᵖ),   CommAlgCat.
Hom.hom (CategoryTheory.SemiCartesianMonoidalCategory.fst A B).unop = Algebra.Te
nsorProduct.includeLeft
参数：A B : (CommAlgCat R)ᵒᵖ；CategoryTheory.SemiCartesianMonoidalCategory.fst A B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma fst_unop_hom (A B : (CommAlgCat.{u} R)ᵒᵖ) : (fst A B).unop.hom = includeLeft := rfl
/-
**CommAlgCat.snd_unop_hom** 是 Mathlib 中的一个定理，位于命名空间 `CommAlgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] (A B : (CommAlgCat R)ᵒᵖ),   CommAlgCat.
Hom.hom (CategoryTheory.SemiCartesianMonoidalCategory.snd A B).unop = Algebra.Te
nsorProduct.includeRight
参数：A B : (CommAlgCat R)ᵒᵖ；CategoryTheory.SemiCartesianMonoidalCategory.snd A B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma snd_unop_hom (A B : (CommAlgCat.{u} R)ᵒᵖ) : (snd A B).unop.hom = includeRight := rfl

variable (A B) in
/-
**CommAlgCat.toUnit_unop_hom** 是 Mathlib 中的一个定理，位于命名空间 `CommAlgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] (A : (CommAlgCat R)ᵒᵖ),   CommAlgCat.Ho
m.hom (CategoryTheory.SemiCartesianMonoidalCategory.toUnit A).unop = Algebra.ofI
d R ↑(Opposite.unop A)
参数：A : (CommAlgCat R)ᵒᵖ；CategoryTheory.SemiCartesianMonoidalCategory.toUnit A；Op
posite.unop A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toUnit_unop_hom : (toUnit A).unop.hom = Algebra.ofId R A.unop := rfl
/-
**CommAlgCat.lift_unop_hom** 是 Mathlib 中的一个定理，位于命名空间 `CommAlgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {A B C : (CommAlgCat R)ᵒᵖ} (f : C ⟶ A) 
(g : C ⟶ B),   CommAlgCat.Hom.hom (CategoryTheory.CartesianMonoidalCategory.lift
 f g).unop =     Algebra.TensorProduct.lift (CommAlgCat.Hom.hom f.unop) (CommAlg
Cat.Hom.hom g.unop) ⋯
参数：CommAlgCat R；f : C ⟶ A；g : C ⟶ B；CategoryTheory.CartesianMonoidalCategory.lif
t f g；CommAlgCat.Hom.hom f.unop；CommAlgCat.Hom.hom g.unop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma lift_unop_hom (f : C ⟶ A) (g : C ⟶ B) :
    (lift f g).unop.hom = lift f.unop.hom g.unop.hom fun _ _ ↦ .all _ _ := rfl

end CommAlgCat

