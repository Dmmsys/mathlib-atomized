/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Kim Morrison, Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# The symmetric monoidal structure on `Module R`.
-/

@[expose] public section

universe v w x u

open CategoryTheory MonoidalCategory

namespace SemimoduleCat

variable {R : Type u} [CommSemiring R]

/--
Definition of `braiding` / `braiding` 的定义

English:
definition braiding
  signature: (M N : SemimoduleCat.{u} R)
  body: LinearEquiv.toModuleIsoₛ (TensorProduct.comm R M N)

中文:
定义 braiding
  签名: (M N : SemimoduleCat.{u} R)
  定义体: LinearEquiv.toModuleIsoₛ (TensorProduct.comm R M N)

Depends on / 依赖: LinearEquiv, LinearEquiv.toModuleIso, TensorProduct, TensorProduct.comm
-/
def braiding (M N : SemimoduleCat.{u} R) : M otimes N ≅ N otimes M :=
  LinearEquiv.toModuleIsoₛ (TensorProduct.comm R M N)

namespace MonoidalCategory

@[simp]
/--
theorem `braiding_naturality` / 定理 `braiding_naturality`

English:
theorem braiding_naturality
  given: {X₁ X₂ Y₁ Y₂ : SemimoduleCat.{u} R} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
  proof: by
  ext : 1
  apply TensorProduct.ext'
  intro x y
  rfl

@[simp]

中文:
定理 braiding_naturality
  条件: {X₁ X₂ Y₁ Y₂ : SemimoduleCat.{u} R} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
  证明: by
  ext : 1
  apply TensorProduct.ext'
  intro x y
  rfl

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.ext
-/
theorem braiding_naturality {X₁ X₂ Y₁ Y₂ : SemimoduleCat.{u} R} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f otimesₘ g) ≫ (Y₁.braiding Y₂).hom = (X₁.braiding X₂).hom ≫ (g otimesₘ f) := by
  ext : 1
  apply TensorProduct.ext'
  intro x y
  rfl

@[simp]
/--
theorem `braiding_naturality_left` / 定理 `braiding_naturality_left`

English:
theorem braiding_naturality_left
  given: {X Y : SemimoduleCat R} (f : X ⟶ Y) (Z : SemimoduleCat R)
  proof: by
  simp_rw [← id_tensorHom]
  apply braiding_naturality

@[simp]

中文:
定理 braiding_naturality_left
  条件: {X Y : SemimoduleCat R} (f : X ⟶ Y) (Z : SemimoduleCat R)
  证明: by
  simp_rw [← id_tensorHom]
  apply braiding_naturality

@[simp]

Depends on / 依赖: braiding_naturality, id_tensorHom, simp_rw
-/
theorem braiding_naturality_left {X Y : SemimoduleCat R} (f : X ⟶ Y) (Z : SemimoduleCat R) :
    f ▷ Z ≫ (braiding Y Z).hom = (braiding X Z).hom ≫ Z ◁ f := by
  simp_rw [← id_tensorHom]
  apply braiding_naturality

@[simp]
/--
theorem `braiding_naturality_right` / 定理 `braiding_naturality_right`

English:
theorem braiding_naturality_right
  given: (X : SemimoduleCat R) {Y Z : SemimoduleCat R} (f : Y ⟶ Z)
  proof: by
  simp_rw [← id_tensorHom]
  apply braiding_naturality

@[simp]

中文:
定理 braiding_naturality_right
  条件: (X : SemimoduleCat R) {Y Z : SemimoduleCat R} (f : Y ⟶ Z)
  证明: by
  simp_rw [← id_tensorHom]
  apply braiding_naturality

@[simp]

Depends on / 依赖: braiding_naturality, id_tensorHom, simp_rw
-/
theorem braiding_naturality_right (X : SemimoduleCat R) {Y Z : SemimoduleCat R} (f : Y ⟶ Z) :
    X ◁ f ≫ (braiding X Z).hom = (braiding X Y).hom ≫ f ▷ X := by
  simp_rw [← id_tensorHom]
  apply braiding_naturality

@[simp]
/--
theorem `hexagon_forward` / 定理 `hexagon_forward`

English:
theorem hexagon_forward
  given: (X Y Z : SemimoduleCat.{u} R)
  proof: by
  ext : 1
  apply TensorProduct.ext_threefold
  intro x y z
  rfl

@[simp]

中文:
定理 hexagon_forward
  条件: (X Y Z : SemimoduleCat.{u} R)
  证明: by
  ext : 1
  apply TensorProduct.ext_threefold
  intro x y z
  rfl

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.ext_threefold, ext_threefold
-/
theorem hexagon_forward (X Y Z : SemimoduleCat.{u} R) :
    (α_ X Y Z).hom ≫ (braiding X _).hom ≫ (α_ Y Z X).hom =
      (braiding X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (braiding X Z).hom := by
  ext : 1
  apply TensorProduct.ext_threefold
  intro x y z
  rfl

@[simp]
/--
theorem `hexagon_reverse` / 定理 `hexagon_reverse`

English:
theorem hexagon_reverse
  given: (X Y Z : SemimoduleCat.{u} R)
  proof: by
  apply (cancel_epi (α_ X Y Z).hom).1
  ext : 1
  apply TensorProduct.ext_threefold
  intro x y z
  rfl

中文:
定理 hexagon_reverse
  条件: (X Y Z : SemimoduleCat.{u} R)
  证明: by
  apply (cancel_epi (α_ X Y Z).hom).1
  ext : 1
  apply TensorProduct.ext_threefold
  intro x y z
  rfl

Depends on / 依赖: TensorProduct, TensorProduct.ext_threefold, cancel_epi, ext_threefold
-/
theorem hexagon_reverse (X Y Z : SemimoduleCat.{u} R) :
    (α_ X Y Z).inv ≫ (braiding _ Z).hom ≫ (α_ Z X Y).inv =
      X ◁ (Y.braiding Z).hom ≫ (α_ X Z Y).inv ≫ (X.braiding Z).hom ▷ Y := by
  apply (cancel_epi (α_ X Y Z).hom).1
  ext : 1
  apply TensorProduct.ext_threefold
  intro x y z
  rfl

attribute [local ext] TensorProduct.ext

/--
Instance `symmetricCategory` / 实例 `symmetricCategory`

English:
instance symmetricCategory
  signature: : SymmetricCategory (SemimoduleCat.{u} R) where
  body: braiding
  braiding_naturality_left := braiding_naturality_left
  braiding_naturality_right := braiding_naturality_right
  hexagon_forward := hexagon_forward
  hexagon_reverse := hexagon_reverse
  -- Porting note: this proof was automatic in Lean3
  -- now `aesop` is applying `SemimoduleCat.ext` in 

中文:
实例 symmetricCategory
  签名: : SymmetricCategory (SemimoduleCat.{u} R) where
  定义体: braiding
  braiding_naturality_left := braiding_naturality_left
  braiding_naturality_right := braiding_naturality_right
  hexagon_forward := hexagon_forward
  hexagon_reverse := hexagon_reverse
  -- Porting note: this proof was automatic in Lean3
  -- now `aesop` is applying `SemimoduleCat.ext` in 

Depends on / 依赖: braiding
-/
instance symmetricCategory : SymmetricCategory (SemimoduleCat.{u} R) where
  braiding := braiding
  braiding_naturality_left := braiding_naturality_left
  braiding_naturality_right := braiding_naturality_right
  hexagon_forward := hexagon_forward
  hexagon_reverse := hexagon_reverse
  -- Porting note: this proof was automatic in Lean3
  -- now `aesop` is applying `SemimoduleCat.ext` in favour of `TensorProduct.ext`.
  symmetry _ _ := by
    ext : 1
    apply TensorProduct.ext'
    cat_disch

@[simp]
/--
theorem `braiding_hom_apply` / 定理 `braiding_hom_apply`

English:
theorem braiding_hom_apply
  given: {M N : SemimoduleCat.{u} R} (m : M) (n : N)
  proof: rfl

@[simp]

中文:
定理 braiding_hom_apply
  条件: {M N : SemimoduleCat.{u} R} (m : M) (n : N)
  证明: rfl

@[simp]
-/
theorem braiding_hom_apply {M N : SemimoduleCat.{u} R} (m : M) (n : N) :
    ((β_ M N).hom : M otimes N ⟶ N otimes M) (m otimesₜ n) = n otimesₜ m :=
  rfl

@[simp]
/--
theorem `braiding_inv_apply` / 定理 `braiding_inv_apply`

English:
theorem braiding_inv_apply
  given: {M N : SemimoduleCat.{u} R} (m : M) (n : N)
  proof: rfl

中文:
定理 braiding_inv_apply
  条件: {M N : SemimoduleCat.{u} R} (m : M) (n : N)
  证明: rfl
-/
theorem braiding_inv_apply {M N : SemimoduleCat.{u} R} (m : M) (n : N) :
    ((β_ M N).inv : N otimes M ⟶ M otimes N) (n otimesₜ m) = m otimesₜ n :=
  rfl

/--
theorem `tensorμ_eq_tensorTensorTensorComm` / 定理 `tensorμ_eq_tensorTensorTensorComm`

English:
theorem tensorμ_eq_tensorTensorTensorComm
  given: {A B C D : SemimoduleCat R}
  proof: SemimoduleCat.hom_ext TensorProduct.ext TensorProduct.ext LinearMap.ext₂ fun _ _ =>
TensorProduct.ext LinearMap.ext₂ fun _ _ => rfl

@[simp]

中文:
定理 tensorμ_eq_tensorTensorTensorComm
  条件: {A B C D : SemimoduleCat R}
  证明: SemimoduleCat.hom_ext TensorProduct.ext TensorProduct.ext LinearMap.ext₂ fun _ _ =>
TensorProduct.ext LinearMap.ext₂ fun _ _ => rfl

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext, SemimoduleCat, SemimoduleCat.hom_ext, TensorProduct, TensorProduct.ext, hom_ext
-/
theorem tensorμ_eq_tensorTensorTensorComm {A B C D : SemimoduleCat R} :
    tensorμ A B C D = ofHom (TensorProduct.tensorTensorTensorComm R A B C D).toLinearMap :=
SemimoduleCat.hom_ext TensorProduct.ext TensorProduct.ext LinearMap.ext₂ fun _ _ =>
TensorProduct.ext LinearMap.ext₂ fun _ _ => rfl

@[simp]
/--
theorem `tensorμ_apply` / 定理 `tensorμ_apply`

English:
theorem tensorμ_apply
  proof: rfl

中文:
定理 tensorμ_apply
  证明: rfl
-/
theorem tensorμ_apply
    {A B C D : SemimoduleCat R} (x : A) (y : B) (z : C) (w : D) :
    tensorμ A B C D ((x otimesₜ y) otimesₜ (z otimesₜ w)) = (x otimesₜ z) otimesₜ (y otimesₜ w) := rfl

end MonoidalCategory

end SemimoduleCat

namespace ModuleCat.MonoidalCategory

variable {R : Type u} [CommRing R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BraidedCategory (ModuleCat.{u} R)
  body: .ofFaithful equivalenceSemimoduleCat.functor (fun M N => (TensorProduct.comm R M N).toModuleIso)

中文:
实例 :
  签名: BraidedCategory (ModuleCat.{u} R)
  定义体: .ofFaithful equivalenceSemimoduleCat.functor (fun M N => (TensorProduct.comm R M N).toModuleIso)

Depends on / 依赖: TensorProduct, TensorProduct.comm, equivalenceSemimoduleCat, equivalenceSemimoduleCat.functor, functor, ofFaithful, toModuleIso
-/
instance : BraidedCategory (ModuleCat.{u} R) :=
  .ofFaithful equivalenceSemimoduleCat.functor (fun M N => (TensorProduct.comm R M N).toModuleIso)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: equivalenceSemimoduleCat (R := R).functor.Braided

中文:
实例 :
  签名: equivalenceSemimoduleCat (R := R).functor.Braided

Depends on / 依赖: Braided, functor, functor.Braided
-/
instance : equivalenceSemimoduleCat (R := R).functor.Braided where

/--
Instance `symmetricCategory` / 实例 `symmetricCategory`

English:
instance symmetricCategory
  signature: : SymmetricCategory (ModuleCat.{u} R)
  body: .ofFaithful equivalenceSemimoduleCat.functor

@[simp]

中文:
实例 symmetricCategory
  签名: : SymmetricCategory (ModuleCat.{u} R)
  定义体: .ofFaithful equivalenceSemimoduleCat.functor

@[simp]

Depends on / 依赖: equivalenceSemimoduleCat, equivalenceSemimoduleCat.functor, functor, ofFaithful
-/
instance symmetricCategory : SymmetricCategory (ModuleCat.{u} R) :=
  .ofFaithful equivalenceSemimoduleCat.functor

@[simp]
/--
theorem `braiding_hom_apply` / 定理 `braiding_hom_apply`

English:
theorem braiding_hom_apply
  given: {M N : ModuleCat.{u} R} (m : M) (n : N)
  proof: rfl

@[simp]

中文:
定理 braiding_hom_apply
  条件: {M N : ModuleCat.{u} R} (m : M) (n : N)
  证明: rfl

@[simp]
-/
theorem braiding_hom_apply {M N : ModuleCat.{u} R} (m : M) (n : N) :
    ((β_ M N).hom : M otimes N ⟶ N otimes M) (m otimesₜ n) = n otimesₜ m :=
  rfl

@[simp]
/--
theorem `braiding_inv_apply` / 定理 `braiding_inv_apply`

English:
theorem braiding_inv_apply
  given: {M N : ModuleCat.{u} R} (m : M) (n : N)
  proof: rfl

中文:
定理 braiding_inv_apply
  条件: {M N : ModuleCat.{u} R} (m : M) (n : N)
  证明: rfl
-/
theorem braiding_inv_apply {M N : ModuleCat.{u} R} (m : M) (n : N) :
    ((β_ M N).inv : N otimes M ⟶ M otimes N) (n otimesₜ m) = m otimesₜ n :=
  rfl

/--
theorem `tensorμ_eq_tensorTensorTensorComm` / 定理 `tensorμ_eq_tensorTensorTensorComm`

English:
theorem tensorμ_eq_tensorTensorTensorComm
  given: {A B C D : ModuleCat R}
  proof: ModuleCat.hom_ext TensorProduct.ext TensorProduct.ext LinearMap.ext₂ fun _ _ =>
TensorProduct.ext LinearMap.ext₂ fun _ _ => rfl

@[simp]

中文:
定理 tensorμ_eq_tensorTensorTensorComm
  条件: {A B C D : ModuleCat R}
  证明: ModuleCat.hom_ext TensorProduct.ext TensorProduct.ext LinearMap.ext₂ fun _ _ =>
TensorProduct.ext LinearMap.ext₂ fun _ _ => rfl

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext, ModuleCat, ModuleCat.hom_ext, TensorProduct, TensorProduct.ext, hom_ext
-/
theorem tensorμ_eq_tensorTensorTensorComm {A B C D : ModuleCat R} :
    tensorμ A B C D = ofHom (TensorProduct.tensorTensorTensorComm R A B C D).toLinearMap :=
ModuleCat.hom_ext TensorProduct.ext TensorProduct.ext LinearMap.ext₂ fun _ _ =>
TensorProduct.ext LinearMap.ext₂ fun _ _ => rfl

@[simp]
/--
theorem `tensorμ_apply` / 定理 `tensorμ_apply`

English:
theorem tensorμ_apply
  proof: rfl

中文:
定理 tensorμ_apply
  证明: rfl
-/
theorem tensorμ_apply
    {A B C D : ModuleCat R} (x : A) (y : B) (z : C) (w : D) :
    tensorμ A B C D ((x otimesₜ y) otimesₜ (z otimesₜ w)) = (x otimesₜ z) otimesₜ (y otimesₜ w) := rfl

end ModuleCat.MonoidalCategory
