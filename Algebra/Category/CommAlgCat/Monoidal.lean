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

/--
Definition of `binaryCofan` / `binaryCofan` 的定义

English:
definition binaryCofan
  signature: : BinaryCofan A B
  body: .mk (ofHom includeLeft) (ofHom <| includeRight (A := A))

中文:
定义 binaryCofan
  签名: : BinaryCofan A B
  定义体: .mk (ofHom includeLeft) (ofHom <| includeRight (A := A))

Depends on / 依赖: includeLeft, includeRight
-/
def binaryCofan : BinaryCofan A B := .mk (ofHom includeLeft) (ofHom <| includeRight (A := A))

/--
lemma `binaryCofan_inl` / 引理 `binaryCofan_inl`

English:
lemma binaryCofan_inl
  statement: (binaryCofan A B).inl = ofHom includeLeft
  proof: rfl

中文:
引理 binaryCofan_inl
  结论: (binaryCofan A B).inl = ofHom includeLeft
  证明: rfl
-/
@[simp] lemma binaryCofan_inl : (binaryCofan A B).inl = ofHom includeLeft := rfl
/--
lemma `binaryCofan_inr` / 引理 `binaryCofan_inr`

English:
lemma binaryCofan_inr
  statement: (binaryCofan A B).inr = ofHom includeRight
  proof: rfl

中文:
引理 binaryCofan_inr
  结论: (binaryCofan A B).inr = ofHom includeRight
  证明: rfl
-/
@[simp] lemma binaryCofan_inr : (binaryCofan A B).inr = ofHom includeRight := rfl
/--
lemma `binaryCofan_pt` / 引理 `binaryCofan_pt`

English:
lemma binaryCofan_pt
  statement: (binaryCofan A B).pt = .of R (A otimes[R] B)
  proof: rfl

中文:
引理 binaryCofan_pt
  结论: (binaryCofan A B).pt = .of R (A otimes[R] B)
  证明: rfl
-/
@[simp] lemma binaryCofan_pt : (binaryCofan A B).pt = .of R (A otimes[R] B) := rfl

/--
Definition of `binaryCofanIsColimit` / `binaryCofanIsColimit` 的定义

English:
definition binaryCofanIsColimit
  signature: : IsColimit (binaryCofan A B)
  body: BinaryCofan.IsColimit.mk _
    (fun f g => ofHom (lift f.hom g.hom fun _ _ => .all _ _))
    (fun f g => by ext1; exact lift_comp_includeLeft _ _ fun _ _ => .all _ _)
    (fun f g => by ext1; exact lift_comp_includeRight _ _ fun _ _ => .all _ _)
    (fun f g m hm₁ hm₂ => by
      ext1
      refine l

中文:
定义 binaryCofanIsColimit
  签名: : IsColimit (binaryCofan A B)
  定义体: BinaryCofan.IsColimit.mk _
    (fun f g => ofHom (lift f.hom g.hom fun _ _ => .all _ _))
    (fun f g => by ext1; exact lift_comp_includeLeft _ _ fun _ _ => .all _ _)
    (fun f g => by ext1; exact lift_comp_includeRight _ _ fun _ _ => .all _ _)
    (fun f g m hm₁ hm₂ => by
      ext1
      refine l

Depends on / 依赖: BinaryCofan, BinaryCofan.IsColimit.mk, IsColimit, Prod.ext, Subtype, Subtype.ext, f.hom, g.hom, liftEquiv, liftEquiv.symm_apply_eq, lift_comp_includeLeft, lift_comp_includeRight, symm_apply_eq
-/
def binaryCofanIsColimit : IsColimit (binaryCofan A B) :=
  BinaryCofan.IsColimit.mk _
    (fun f g => ofHom (lift f.hom g.hom fun _ _ => .all _ _))
    (fun f g => by ext1; exact lift_comp_includeLeft _ _ fun _ _ => .all _ _)
    (fun f g => by ext1; exact lift_comp_includeRight _ _ fun _ _ => .all _ _)
    (fun f g m hm₁ hm₂ => by
      ext1
      refine liftEquiv.symm_apply_eq (y := ⟨⟨_, _⟩, fun _ _ => .all _ _⟩).mp ?_
      exact Subtype.ext (Prod.ext congr(($hm₁).hom) congr(($hm₂).hom)))

/--
Definition of `isInitialSelf` / `isInitialSelf` 的定义

English:
definition isInitialSelf
  signature: : IsInitial (of R R)
  body: .ofUniqueHom (fun A => ofHom (Algebra.ofId R A)) fun _ _ => hom_ext (Algebra.ext_id _ _ _)

中文:
定义 isInitialSelf
  签名: : IsInitial (of R R)
  定义体: .ofUniqueHom (fun A => ofHom (Algebra.ofId R A)) fun _ _ => hom_ext (Algebra.ext_id _ _ _)

Depends on / 依赖: Algebra, Algebra.ext_id, Algebra.ofId, ext_id, hom_ext, ofUniqueHom
-/
def isInitialSelf : IsInitial (of R R) :=
  .ofUniqueHom (fun A => ofHom (Algebra.ofId R A)) fun _ _ => hom_ext (Algebra.ext_id _ _ _)

attribute [local simp] one_def in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidalCategory (CommAlgCat.{u} R)
  body: of R (S otimes[R] T)
  whiskerLeft _ {_ _} f := ofHom (map (.id _ _) f.hom)
  whiskerRight f T := ofHom (map f.hom (.id _ _))
  tensorHom f g := ofHom (map f.hom g.hom)
  tensorUnit := .of R R
  associator _ _ _ := isoMk (assoc R R R _ _ _)
  leftUnitor _ := isoMk (lid R _)
  rightUnitor _ := isoMk 

中文:
实例 :
  签名: MonoidalCategory (CommAlgCat.{u} R)
  定义体: of R (S otimes[R] T)
  whiskerLeft _ {_ _} f := ofHom (map (.id _ _) f.hom)
  whiskerRight f T := ofHom (map f.hom (.id _ _))
  tensorHom f g := ofHom (map f.hom g.hom)
  tensorUnit := .of R R
  associator _ _ _ := isoMk (assoc R R R _ _ _)
  leftUnitor _ := isoMk (lid R _)
  rightUnitor _ := isoMk 

Depends on / 依赖: otimes
-/
instance : MonoidalCategory (CommAlgCat.{u} R) where
  tensorObj S T := of R (S otimes[R] T)
  whiskerLeft _ {_ _} f := ofHom (map (.id _ _) f.hom)
  whiskerRight f T := ofHom (map f.hom (.id _ _))
  tensorHom f g := ofHom (map f.hom g.hom)
  tensorUnit := .of R R
  associator _ _ _ := isoMk (assoc R R R _ _ _)
  leftUnitor _ := isoMk (lid R _)
  rightUnitor _ := isoMk (rid R R _)

/--
lemma `coe_tensorUnit` / 引理 `coe_tensorUnit`

English:
lemma coe_tensorUnit
  statement: 𝟙_ (CommAlgCat.{u} R) = R
  proof: rfl

中文:
引理 coe_tensorUnit
  结论: 𝟙_ (CommAlgCat.{u} R) = R
  证明: rfl
-/
@[simp] lemma coe_tensorUnit : 𝟙_ (CommAlgCat.{u} R) = R := rfl

/--
lemma `coe_tensorObj` / 引理 `coe_tensorObj`

English:
lemma coe_tensorObj
  statement: A otimes B = A otimes[R] B
  proof: rfl

中文:
引理 coe_tensorObj
  结论: A otimes B = A otimes[R] B
  证明: rfl
-/
@[simp] lemma coe_tensorObj : A otimes B = A otimes[R] B := rfl

variable {A B}

/--
lemma `tensorHom_hom` / 引理 `tensorHom_hom`

English:
lemma tensorHom_hom
  given: (f : A ⟶ C) (g : B ⟶ D)
  statement: (f otimesₘ g).hom = map f.hom g.hom
  proof: rfl

中文:
引理 tensorHom_hom
  条件: (f : A ⟶ C) (g : B ⟶ D)
  结论: (f otimesₘ g).hom = map f.hom g.hom
  证明: rfl
-/
@[simp] lemma tensorHom_hom (f : A ⟶ C) (g : B ⟶ D) : (f otimesₘ g).hom = map f.hom g.hom := rfl

variable (C) in
/--
lemma `whiskerRight_hom` / 引理 `whiskerRight_hom`

English:
lemma whiskerRight_hom
  given: (f : A ⟶ B)
  statement: (f ▷ C).hom = map f.hom (.id _ _)
  proof: rfl

中文:
引理 whiskerRight_hom
  条件: (f : A ⟶ B)
  结论: (f ▷ C).hom = map f.hom (.id _ _)
  证明: rfl
-/
@[simp] lemma whiskerRight_hom (f : A ⟶ B) : (f ▷ C).hom = map f.hom (.id _ _) := rfl

variable (C) in
/--
lemma `whiskerLeft_hom` / 引理 `whiskerLeft_hom`

English:
lemma whiskerLeft_hom
  given: (f : A ⟶ B)
  statement: (C ◁ f).hom = map (.id _ _) f.hom
  proof: rfl

中文:
引理 whiskerLeft_hom
  条件: (f : A ⟶ B)
  结论: (C ◁ f).hom = map (.id _ _) f.hom
  证明: rfl
-/
@[simp] lemma whiskerLeft_hom (f : A ⟶ B) : (C ◁ f).hom = map (.id _ _) f.hom := rfl

variable (A B C) in
/--
lemma `associator_hom_hom` / 引理 `associator_hom_hom`

English:
lemma associator_hom_hom
  statement: (α_ A B C).hom.hom = (assoc R R R A B C).toAlgHom
  proof: rfl

中文:
引理 associator_hom_hom
  结论: (α_ A B C).hom.hom = (assoc R R R A B C).toAlgHom
  证明: rfl
-/
@[simp] lemma associator_hom_hom : (α_ A B C).hom.hom = (assoc R R R A B C).toAlgHom := rfl

variable (A B C) in
/--
lemma `associator_inv_hom` / 引理 `associator_inv_hom`

English:
lemma associator_inv_hom
  statement: (α_ A B C).inv.hom = (assoc R R R A B C).symm.toAlgHom
  proof: rfl

中文:
引理 associator_inv_hom
  结论: (α_ A B C).inv.hom = (assoc R R R A B C).symm.toAlgHom
  证明: rfl
-/
@[simp] lemma associator_inv_hom : (α_ A B C).inv.hom = (assoc R R R A B C).symm.toAlgHom := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BraidedCategory (CommAlgCat.{u} R)
  body: isoMk (comm R _ _)
  braiding_naturality_right := by intros; ext : 1; dsimp; ext <;> rfl
  braiding_naturality_left := by intros; ext : 1; dsimp; ext <;> rfl
  hexagon_forward S T U := by ext : 1; dsimp; ext <;> rfl
  hexagon_reverse S T U := by ext : 1; dsimp; ext <;> rfl

中文:
实例 :
  签名: BraidedCategory (CommAlgCat.{u} R)
  定义体: isoMk (comm R _ _)
  braiding_naturality_right := by intros; ext : 1; dsimp; ext <;> rfl
  braiding_naturality_left := by intros; ext : 1; dsimp; ext <;> rfl
  hexagon_forward S T U := by ext : 1; dsimp; ext <;> rfl
  hexagon_reverse S T U := by ext : 1; dsimp; ext <;> rfl
-/
instance : BraidedCategory (CommAlgCat.{u} R) where
  braiding S T := isoMk (comm R _ _)
  braiding_naturality_right := by intros; ext : 1; dsimp; ext <;> rfl
  braiding_naturality_left := by intros; ext : 1; dsimp; ext <;> rfl
  hexagon_forward S T U := by ext : 1; dsimp; ext <;> rfl
  hexagon_reverse S T U := by ext : 1; dsimp; ext <;> rfl

variable (A B) in
/--
lemma `braiding_hom_hom` / 引理 `braiding_hom_hom`

English:
lemma braiding_hom_hom
  statement: (β_ A B).hom.hom = (comm R A B).toAlgHom
  proof: rfl

中文:
引理 braiding_hom_hom
  结论: (β_ A B).hom.hom = (comm R A B).toAlgHom
  证明: rfl
-/
@[simp] lemma braiding_hom_hom : (β_ A B).hom.hom = (comm R A B).toAlgHom := rfl

variable (A B) in
/--
lemma `braiding_inv_hom` / 引理 `braiding_inv_hom`

English:
lemma braiding_inv_hom
  statement: (β_ A B).inv.hom = (comm R B A).toAlgHom
  proof: rfl

中文:
引理 braiding_inv_hom
  结论: (β_ A B).inv.hom = (comm R B A).toAlgHom
  证明: rfl
-/
@[simp] lemma braiding_inv_hom : (β_ A B).inv.hom = (comm R B A).toAlgHom := rfl

attribute [local ext] Quiver.Hom.unop_inj in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CartesianMonoidalCategory (CommAlgCat.{u} R)ᵒᵖ
  body: terminalOpOfInitial isInitialSelf
  fst := _
  snd := _
tensorProductIsBinaryProduct S T := BinaryCofan.IsColimit.op binaryCofanIsColimit S.unop T.unop
  fst_def S T := by ext x; change x otimesₜ 1 = x otimesₜ algebraMap R T.unop 1; simp
  snd_def S T := by ext x; change 1 otimesₜ x = algebraMap R S

中文:
实例 :
  签名: CartesianMonoidalCategory (CommAlgCat.{u} R)ᵒᵖ
  定义体: terminalOpOfInitial isInitialSelf
  fst := _
  snd := _
tensorProductIsBinaryProduct S T := BinaryCofan.IsColimit.op binaryCofanIsColimit S.unop T.unop
  fst_def S T := by ext x; change x otimesₜ 1 = x otimesₜ algebraMap R T.unop 1; simp
  snd_def S T := by ext x; change 1 otimesₜ x = algebraMap R S

Depends on / 依赖: isInitialSelf, terminalOpOfInitial
-/
instance : CartesianMonoidalCategory (CommAlgCat.{u} R)ᵒᵖ where
  isTerminalTensorUnit := terminalOpOfInitial isInitialSelf
  fst := _
  snd := _
tensorProductIsBinaryProduct S T := BinaryCofan.IsColimit.op binaryCofanIsColimit S.unop T.unop
  fst_def S T := by ext x; change x otimesₜ 1 = x otimesₜ algebraMap R T.unop 1; simp
  snd_def S T := by ext x; change 1 otimesₜ x = algebraMap R S.unop 1 otimesₜ x; simp

variable {A B C D : (CommAlgCat.{u} R)ᵒᵖ}

/--
lemma `fst_unop_hom` / 引理 `fst_unop_hom`

English:
lemma fst_unop_hom
  given: (A B : (CommAlgCat.{u} R)ᵒᵖ)
  statement: (fst A B).unop.hom = includeLeft
  proof: rfl

中文:
引理 fst_unop_hom
  条件: (A B : (CommAlgCat.{u} R)ᵒᵖ)
  结论: (fst A B).unop.hom = includeLeft
  证明: rfl
-/
@[simp] lemma fst_unop_hom (A B : (CommAlgCat.{u} R)ᵒᵖ) : (fst A B).unop.hom = includeLeft := rfl
/--
lemma `snd_unop_hom` / 引理 `snd_unop_hom`

English:
lemma snd_unop_hom
  given: (A B : (CommAlgCat.{u} R)ᵒᵖ)
  statement: (snd A B).unop.hom = includeRight
  proof: rfl

中文:
引理 snd_unop_hom
  条件: (A B : (CommAlgCat.{u} R)ᵒᵖ)
  结论: (snd A B).unop.hom = includeRight
  证明: rfl
-/
@[simp] lemma snd_unop_hom (A B : (CommAlgCat.{u} R)ᵒᵖ) : (snd A B).unop.hom = includeRight := rfl

variable (A B) in
/--
lemma `toUnit_unop_hom` / 引理 `toUnit_unop_hom`

English:
lemma toUnit_unop_hom
  statement: (toUnit A).unop.hom = Algebra.ofId R A.unop
  proof: rfl

中文:
引理 toUnit_unop_hom
  结论: (toUnit A).unop.hom = Algebra.ofId R A.unop
  证明: rfl
-/
@[simp] lemma toUnit_unop_hom : (toUnit A).unop.hom = Algebra.ofId R A.unop := rfl

/--
lemma `lift_unop_hom` / 引理 `lift_unop_hom`

English:
lemma lift_unop_hom
  given: (f : C ⟶ A) (g : C ⟶ B)
  proof: rfl

中文:
引理 lift_unop_hom
  条件: (f : C ⟶ A) (g : C ⟶ B)
  证明: rfl
-/
@[simp] lemma lift_unop_hom (f : C ⟶ A) (g : C ⟶ B) :
    (lift f g).unop.hom = lift f.unop.hom g.unop.hom fun _ _ => .all _ _ := rfl

end CommAlgCat
