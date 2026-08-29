/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Kim Morrison, Jakob von Raumer
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Monoidal.Transport

/-!
# The monoidal category structure on R-modules

Mostly this uses existing machinery in `LinearAlgebra.TensorProduct`.
We just need to provide a few small missing pieces to build the
`MonoidalCategory` instance.
The `SymmetricCategory` instance is in `Algebra.Category.ModuleCat.Monoidal.Symmetric`
to reduce imports.

Note the universe level of the modules must be at least the universe level of the ring,
so that we have a monoidal unit.
For now, we simplify by insisting both universe levels are the same.

We construct the monoidal closed structure on `ModuleCat R` in
`Algebra.Category.ModuleCat.Monoidal.Closed`.

If you're happy using the bundled `ModuleCat R`, it may be possible to mostly
use this as an interface and not need to interact much with the implementation details.
-/

@[expose] public section

universe v w x u

open CategoryTheory

namespace SemimoduleCat

variable {R : Type u} [CommSemiring R]

namespace MonoidalCategory

-- The definitions inside this namespace are essentially private.
-- After we build the `MonoidalCategory (Module R)` instance,
-- you should use that API.
open TensorProduct

attribute [local ext] TensorProduct.ext

/--
Definition of `tensorObj` / `tensorObj` 的定义

English:
definition tensorObj
  signature: (M N : SemimoduleCat R)
  body: SemimoduleCat.of R (M otimes[R] N)

中文:
定义 tensorObj
  签名: (M N : SemimoduleCat R)
  定义体: SemimoduleCat.of R (M otimes[R] N)

Depends on / 依赖: SemimoduleCat, SemimoduleCat.of, otimes
-/
def tensorObj (M N : SemimoduleCat R) : SemimoduleCat R :=
  SemimoduleCat.of R (M otimes[R] N)

/--
Definition of `tensorHom` / `tensorHom` 的定义

English:
definition tensorHom
  signature: {M N M' N' : SemimoduleCat R} (f : M ⟶ N) (g : M' ⟶ N')
  body: ofHom TensorProduct.map f.hom g.hom

中文:
定义 tensorHom
  签名: {M N M' N' : SemimoduleCat R} (f : M ⟶ N) (g : M' ⟶ N')
  定义体: ofHom TensorProduct.map f.hom g.hom

Depends on / 依赖: TensorProduct, TensorProduct.map, f.hom, g.hom
-/
def tensorHom {M N M' N' : SemimoduleCat R} (f : M ⟶ N) (g : M' ⟶ N') :
    tensorObj M M' ⟶ tensorObj N N' :=
ofHom TensorProduct.map f.hom g.hom

/--
Definition of `whiskerLeft` / `whiskerLeft` 的定义

English:
definition whiskerLeft
  signature: (M : SemimoduleCat R) {N₁ N₂ : SemimoduleCat R} (f : N₁ ⟶ N₂)
  body: ofHom f.hom.lTensor M

中文:
定义 whiskerLeft
  签名: (M : SemimoduleCat R) {N₁ N₂ : SemimoduleCat R} (f : N₁ ⟶ N₂)
  定义体: ofHom f.hom.lTensor M

Depends on / 依赖: f.hom.lTensor, lTensor
-/
def whiskerLeft (M : SemimoduleCat R) {N₁ N₂ : SemimoduleCat R} (f : N₁ ⟶ N₂) :
    tensorObj M N₁ ⟶ tensorObj M N₂ :=
ofHom f.hom.lTensor M

/--
Definition of `whiskerRight` / `whiskerRight` 的定义

English:
definition whiskerRight
  signature: {M₁ M₂ : SemimoduleCat R} (f : M₁ ⟶ M₂) (N : SemimoduleCat R)
  body: ofHom f.hom.rTensor N

中文:
定义 whiskerRight
  签名: {M₁ M₂ : SemimoduleCat R} (f : M₁ ⟶ M₂) (N : SemimoduleCat R)
  定义体: ofHom f.hom.rTensor N

Depends on / 依赖: f.hom.rTensor, rTensor
-/
def whiskerRight {M₁ M₂ : SemimoduleCat R} (f : M₁ ⟶ M₂) (N : SemimoduleCat R) :
    tensorObj M₁ N ⟶ tensorObj M₂ N :=
ofHom f.hom.rTensor N

/--
theorem `id_tensorHom_id` / 定理 `id_tensorHom_id`

English:
theorem id_tensorHom_id
  given: (M N : SemimoduleCat R)
  proof: by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): even with high priority `ext` fails to find this.
  apply TensorProduct.ext
  rfl

中文:
定理 id_tensorHom_id
  条件: (M N : SemimoduleCat R)
  证明: by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): even with high priority `ext` fails to find this.
  apply TensorProduct.ext
  rfl
-/
theorem id_tensorHom_id (M N : SemimoduleCat R) :
    tensorHom (𝟙 M) (𝟙 N) = 𝟙 (SemimoduleCat.of R (M otimes N)) := by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): even with high priority `ext` fails to find this.
  apply TensorProduct.ext
  rfl

/--
theorem `tensorHom_comp_tensorHom` / 定理 `tensorHom_comp_tensorHom`

English:
theorem tensorHom_comp_tensorHom
  statement: {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : SemimoduleCat R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
  proof: by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): even with high priority `ext` fails to find this.
  apply TensorProduct.ext
  rfl

中文:
定理 tensorHom_comp_tensorHom
  结论: {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : SemimoduleCat R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
  证明: by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): even with high priority `ext` fails to find this.
  apply TensorProduct.ext
  rfl
-/
theorem tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : SemimoduleCat R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ = tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) := by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): even with high priority `ext` fails to find this.
  apply TensorProduct.ext
  rfl

/--
Definition of `associator` / `associator` 的定义

English:
definition associator
  signature: (M : SemimoduleCat.{v} R) (N : SemimoduleCat.{w} R) (K : SemimoduleCat.{x} R)
  body: (TensorProduct.assoc R M N K).toModuleIsoₛ

中文:
定义 associator
  签名: (M : SemimoduleCat.{v} R) (N : SemimoduleCat.{w} R) (K : SemimoduleCat.{x} R)
  定义体: (TensorProduct.assoc R M N K).toModuleIsoₛ

Depends on / 依赖: TensorProduct, TensorProduct.assoc
-/
def associator (M : SemimoduleCat.{v} R) (N : SemimoduleCat.{w} R) (K : SemimoduleCat.{x} R) :
    tensorObj (tensorObj M N) K ≅ tensorObj M (tensorObj N K) :=
  (TensorProduct.assoc R M N K).toModuleIsoₛ

/--
Definition of `leftUnitor` / `leftUnitor` 的定义

English:
definition leftUnitor
  signature: (M : SemimoduleCat.{u} R)
  body: (TensorProduct.lid R M).toModuleIsoₛ

中文:
定义 leftUnitor
  签名: (M : SemimoduleCat.{u} R)
  定义体: (TensorProduct.lid R M).toModuleIsoₛ

Depends on / 依赖: TensorProduct, TensorProduct.lid
-/
def leftUnitor (M : SemimoduleCat.{u} R) : SemimoduleCat.of R (R otimes[R] M) ≅ M :=
  (TensorProduct.lid R M).toModuleIsoₛ

/--
Definition of `rightUnitor` / `rightUnitor` 的定义

English:
definition rightUnitor
  signature: (M : SemimoduleCat.{u} R)
  body: (TensorProduct.rid R M).toModuleIsoₛ

@[simps -isSimp]

中文:
定义 rightUnitor
  签名: (M : SemimoduleCat.{u} R)
  定义体: (TensorProduct.rid R M).toModuleIsoₛ

@[simps -isSimp]

Depends on / 依赖: TensorProduct, TensorProduct.rid
-/
def rightUnitor (M : SemimoduleCat.{u} R) : SemimoduleCat.of R (M otimes[R] R) ≅ M :=
  (TensorProduct.rid R M).toModuleIsoₛ

@[simps -isSimp]
/--
Instance `instMonoidalCategoryStruct` / 实例 `instMonoidalCategoryStruct`

English:
instance instMonoidalCategoryStruct
  signature: : MonoidalCategoryStruct (SemimoduleCat.{u} R) where
  body: tensorObj
  whiskerLeft := whiskerLeft
  whiskerRight := whiskerRight
  tensorHom := tensorHom
  tensorUnit := SemimoduleCat.of R R
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

中文:
实例 instMonoidalCategoryStruct
  签名: : MonoidalCategoryStruct (SemimoduleCat.{u} R) where
  定义体: tensorObj
  whiskerLeft := whiskerLeft
  whiskerRight := whiskerRight
  tensorHom := tensorHom
  tensorUnit := SemimoduleCat.of R R
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

Depends on / 依赖: AddCommGrpCat, PreservesLimitsOfShape, forget, inverseAux, inverseAux.obj, preservesLimitsOfShape_of_reflects_of_preserves, tensorObj
-/
instance instMonoidalCategoryStruct : MonoidalCategoryStruct (SemimoduleCat.{u} R) where
  tensorObj := tensorObj
  whiskerLeft := whiskerLeft
  whiskerRight := whiskerRight
  tensorHom := tensorHom
  tensorUnit := SemimoduleCat.of R R
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

/--
theorem `associator_naturality` / 定理 `associator_naturality`

English:
theorem associator_naturality
  statement: {X₁ X₂ X₃ Y₁ Y₂ Y₃ : SemimoduleCat R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
  proof: by
  ext : 1
  apply TensorProduct.ext_threefold
  intro x y z
  rfl

中文:
定理 associator_naturality
  结论: {X₁ X₂ X₃ Y₁ Y₂ Y₃ : SemimoduleCat R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
  证明: by
  ext : 1
  apply TensorProduct.ext_threefold
  intro x y z
  rfl

Depends on / 依赖: TensorProduct, TensorProduct.ext_threefold, ext_threefold
-/
theorem associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : SemimoduleCat R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (f₃ : X₃ ⟶ Y₃) :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom =
      (associator X₁ X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by
  ext : 1
  apply TensorProduct.ext_threefold
  intro x y z
  rfl

/--
theorem `pentagon` / 定理 `pentagon`

English:
theorem pentagon
  given: (W X Y Z : SemimoduleCat R)
  proof: by
  ext : 1
  apply TensorProduct.ext_fourfold
  intro w x y z
  rfl

中文:
定理 pentagon
  条件: (W X Y Z : SemimoduleCat R)
  证明: by
  ext : 1
  apply TensorProduct.ext_fourfold
  intro w x y z
  rfl

Depends on / 依赖: TensorProduct, TensorProduct.ext_fourfold, ext_fourfold
-/
theorem pentagon (W X Y Z : SemimoduleCat R) :
    whiskerRight (associator W X Y).hom Z ≫
        (associator W (tensorObj X Y) Z).hom ≫ whiskerLeft W (associator X Y Z).hom =
      (associator (tensorObj W X) Y Z).hom ≫ (associator W X (tensorObj Y Z)).hom := by
  ext : 1
  apply TensorProduct.ext_fourfold
  intro w x y z
  rfl

/--
theorem `leftUnitor_naturality` / 定理 `leftUnitor_naturality`

English:
theorem leftUnitor_naturality
  given: {M N : SemimoduleCat R} (f : M ⟶ N)
  proof: by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): broken ext
  apply TensorProduct.ext
  ext
  simp [tensorHom, tensorObj, leftUnitor]

中文:
定理 leftUnitor_naturality
  条件: {M N : SemimoduleCat R} (f : M ⟶ N)
  证明: by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): broken ext
  apply TensorProduct.ext
  ext
  simp [tensorHom, tensorObj, leftUnitor]
-/
theorem leftUnitor_naturality {M N : SemimoduleCat R} (f : M ⟶ N) :
    tensorHom (𝟙 (SemimoduleCat.of R R)) f ≫ (leftUnitor N).hom = (leftUnitor M).hom ≫ f := by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): broken ext
  apply TensorProduct.ext
  ext
  simp [tensorHom, tensorObj, leftUnitor]

/--
theorem `rightUnitor_naturality` / 定理 `rightUnitor_naturality`

English:
theorem rightUnitor_naturality
  given: {M N : SemimoduleCat R} (f : M ⟶ N)
  proof: by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): broken ext
  apply TensorProduct.ext
  ext
  simp [tensorHom, tensorObj, rightUnitor]

中文:
定理 rightUnitor_naturality
  条件: {M N : SemimoduleCat R} (f : M ⟶ N)
  证明: by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): broken ext
  apply TensorProduct.ext
  ext
  simp [tensorHom, tensorObj, rightUnitor]
-/
theorem rightUnitor_naturality {M N : SemimoduleCat R} (f : M ⟶ N) :
    tensorHom f (𝟙 (SemimoduleCat.of R R)) ≫ (rightUnitor N).hom = (rightUnitor M).hom ≫ f := by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): broken ext
  apply TensorProduct.ext
  ext
  simp [tensorHom, tensorObj, rightUnitor]

/--
theorem `triangle` / 定理 `triangle`

English:
theorem triangle
  given: (M N : SemimoduleCat.{u} R)
  proof: by
  ext : 1
  apply TensorProduct.ext_threefold
  intro x y
  exact TensorProduct.tmul_smul _ _

中文:
定理 triangle
  条件: (M N : SemimoduleCat.{u} R)
  证明: by
  ext : 1
  apply TensorProduct.ext_threefold
  intro x y
  exact TensorProduct.tmul_smul _ _

Depends on / 依赖: TensorProduct, TensorProduct.ext_threefold, TensorProduct.tmul_smul, ext_threefold, tmul_smul
-/
theorem triangle (M N : SemimoduleCat.{u} R) :
    (associator M (SemimoduleCat.of R R) N).hom ≫ tensorHom (𝟙 M) (leftUnitor N).hom =
      tensorHom (rightUnitor M).hom (𝟙 N) := by
  ext : 1
  apply TensorProduct.ext_threefold
  intro x y
  exact TensorProduct.tmul_smul _ _

end MonoidalCategory

open MonoidalCategory

/--
Instance `monoidalCategory` / 实例 `monoidalCategory`

English:
instance monoidalCategory
  signature: : MonoidalCategory (SemimoduleCat.{u} R)
  body: MonoidalCategory.ofTensorHom
  (id_tensorHom_id := fun M N => id_tensorHom_id M N)
  (tensorHom_comp_tensorHom := fun f g h => MonoidalCategory.tensorHom_comp_tensorHom f g h)
  (associator_naturality := fun f g h => MonoidalCategory.associator_naturality f g h)
  (leftUnitor_naturality := fun f => 

中文:
实例 monoidalCategory
  签名: : MonoidalCategory (SemimoduleCat.{u} R)
  定义体: MonoidalCategory.ofTensorHom
  (id_tensorHom_id := fun M N => id_tensorHom_id M N)
  (tensorHom_comp_tensorHom := fun f g h => MonoidalCategory.tensorHom_comp_tensorHom f g h)
  (associator_naturality := fun f g h => MonoidalCategory.associator_naturality f g h)
  (leftUnitor_naturality := fun f => 

Depends on / 依赖: MonoidalCategory, MonoidalCategory.ofTensorHom, ofTensorHom
-/
instance monoidalCategory : MonoidalCategory (SemimoduleCat.{u} R) := MonoidalCategory.ofTensorHom
  (id_tensorHom_id := fun M N => id_tensorHom_id M N)
  (tensorHom_comp_tensorHom := fun f g h => MonoidalCategory.tensorHom_comp_tensorHom f g h)
  (associator_naturality := fun f g h => MonoidalCategory.associator_naturality f g h)
  (leftUnitor_naturality := fun f => MonoidalCategory.leftUnitor_naturality f)
  (rightUnitor_naturality := fun f => rightUnitor_naturality f)
  (pentagon := fun M N K L => pentagon M N K L)
  (triangle := fun M N => triangle M N)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommSemiring ((𝟙_ (SemimoduleCat.{u} R) : SemimoduleCat.{u} R) : Type u)
  body: inferInstanceAs CommSemiring R

中文:
实例 :
  签名: CommSemiring ((𝟙_ (SemimoduleCat.{u} R) : SemimoduleCat.{u} R) : 类型u)
  定义体: inferInstanceAs CommSemiring R

Depends on / 依赖: CommSemiring
-/
instance : CommSemiring ((𝟙_ (SemimoduleCat.{u} R) : SemimoduleCat.{u} R) : Type u) :=
inferInstanceAs CommSemiring R

/--
theorem `hom_tensorHom` / 定理 `hom_tensorHom`

English:
theorem hom_tensorHom
  given: {K L M N : SemimoduleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N)
  proof: rfl

中文:
定理 hom_tensorHom
  条件: {K L M N : SemimoduleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N)
  证明: rfl
-/
theorem hom_tensorHom {K L M N : SemimoduleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) :
    (f otimesₘ g).hom = TensorProduct.map f.hom g.hom :=
  rfl

/--
theorem `hom_whiskerLeft` / 定理 `hom_whiskerLeft`

English:
theorem hom_whiskerLeft
  given: (L : SemimoduleCat.{u} R) {M N : SemimoduleCat.{u} R} (f : M ⟶ N)
  proof: rfl

中文:
定理 hom_whiskerLeft
  条件: (L : SemimoduleCat.{u} R) {M N : SemimoduleCat.{u} R} (f : M ⟶ N)
  证明: rfl
-/
theorem hom_whiskerLeft (L : SemimoduleCat.{u} R) {M N : SemimoduleCat.{u} R} (f : M ⟶ N) :
    (L ◁ f).hom = f.hom.lTensor L :=
  rfl

/--
theorem `hom_whiskerRight` / 定理 `hom_whiskerRight`

English:
theorem hom_whiskerRight
  given: {L M : SemimoduleCat.{u} R} (f : L ⟶ M) (N : SemimoduleCat.{u} R)
  proof: rfl

中文:
定理 hom_whiskerRight
  条件: {L M : SemimoduleCat.{u} R} (f : L ⟶ M) (N : SemimoduleCat.{u} R)
  证明: rfl
-/
theorem hom_whiskerRight {L M : SemimoduleCat.{u} R} (f : L ⟶ M) (N : SemimoduleCat.{u} R) :
    (f ▷ N).hom = f.hom.rTensor N :=
  rfl

/--
theorem `hom_hom_leftUnitor` / 定理 `hom_hom_leftUnitor`

English:
theorem hom_hom_leftUnitor
  given: {M : SemimoduleCat.{u} R}
  proof: rfl

中文:
定理 hom_hom_leftUnitor
  条件: {M : SemimoduleCat.{u} R}
  证明: rfl
-/
theorem hom_hom_leftUnitor {M : SemimoduleCat.{u} R} :
    (fun_ M).hom.hom = (TensorProduct.lid _ _).toLinearMap :=
  rfl

/--
theorem `hom_inv_leftUnitor` / 定理 `hom_inv_leftUnitor`

English:
theorem hom_inv_leftUnitor
  given: {M : SemimoduleCat.{u} R}
  proof: rfl

中文:
定理 hom_inv_leftUnitor
  条件: {M : SemimoduleCat.{u} R}
  证明: rfl
-/
theorem hom_inv_leftUnitor {M : SemimoduleCat.{u} R} :
    (fun_ M).inv.hom = (TensorProduct.lid _ _).symm.toLinearMap :=
  rfl

/--
theorem `hom_hom_rightUnitor` / 定理 `hom_hom_rightUnitor`

English:
theorem hom_hom_rightUnitor
  given: {M : SemimoduleCat.{u} R}
  proof: rfl

中文:
定理 hom_hom_rightUnitor
  条件: {M : SemimoduleCat.{u} R}
  证明: rfl
-/
theorem hom_hom_rightUnitor {M : SemimoduleCat.{u} R} :
    (ρ_ M).hom.hom = (TensorProduct.rid _ _).toLinearMap :=
  rfl

/--
theorem `hom_inv_rightUnitor` / 定理 `hom_inv_rightUnitor`

English:
theorem hom_inv_rightUnitor
  given: {M : SemimoduleCat.{u} R}
  proof: rfl

中文:
定理 hom_inv_rightUnitor
  条件: {M : SemimoduleCat.{u} R}
  证明: rfl
-/
theorem hom_inv_rightUnitor {M : SemimoduleCat.{u} R} :
    (ρ_ M).inv.hom = (TensorProduct.rid _ _).symm.toLinearMap :=
  rfl

/--
theorem `hom_hom_associator` / 定理 `hom_hom_associator`

English:
theorem hom_hom_associator
  given: {M N K : SemimoduleCat.{u} R}
  proof: rfl

中文:
定理 hom_hom_associator
  条件: {M N K : SemimoduleCat.{u} R}
  证明: rfl
-/
theorem hom_hom_associator {M N K : SemimoduleCat.{u} R} :
    (α_ M N K).hom.hom = (TensorProduct.assoc _ _ _ _).toLinearMap :=
  rfl

/--
theorem `hom_inv_associator` / 定理 `hom_inv_associator`

English:
theorem hom_inv_associator
  given: {M N K : SemimoduleCat.{u} R}
  proof: rfl

中文:
定理 hom_inv_associator
  条件: {M N K : SemimoduleCat.{u} R}
  证明: rfl
-/
theorem hom_inv_associator {M N K : SemimoduleCat.{u} R} :
    (α_ M N K).inv.hom = (TensorProduct.assoc _ _ _ _).symm.toLinearMap :=
  rfl

namespace MonoidalCategory

@[simp]
/--
theorem `tensorHom_tmul` / 定理 `tensorHom_tmul`

English:
theorem tensorHom_tmul
  given: {K L M N : SemimoduleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) (k : K) (m : M)
  proof: rfl

@[simp]

中文:
定理 tensorHom_tmul
  条件: {K L M N : SemimoduleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) (k : K) (m : M)
  证明: rfl

@[simp]
-/
theorem tensorHom_tmul {K L M N : SemimoduleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) (k : K) (m : M) :
    (f otimesₘ g) (k otimesₜ m) = f k otimesₜ g m :=
  rfl

@[simp]
/--
theorem `whiskerLeft_apply` / 定理 `whiskerLeft_apply`

English:
theorem whiskerLeft_apply
  statement: (L : SemimoduleCat.{u} R) {M N : SemimoduleCat.{u} R} (f : M ⟶ N)
  proof: rfl

@[simp]

中文:
定理 whiskerLeft_apply
  结论: (L : SemimoduleCat.{u} R) {M N : SemimoduleCat.{u} R} (f : M ⟶ N)
  证明: rfl

@[simp]
-/
theorem whiskerLeft_apply (L : SemimoduleCat.{u} R) {M N : SemimoduleCat.{u} R} (f : M ⟶ N)
    (l : L) (m : M) :
    (L ◁ f) (l otimesₜ m) = l otimesₜ f m :=
  rfl

@[simp]
/--
theorem `whiskerRight_apply` / 定理 `whiskerRight_apply`

English:
theorem whiskerRight_apply
  statement: {L M : SemimoduleCat.{u} R} (f : L ⟶ M) (N : SemimoduleCat.{u} R)
  proof: rfl

@[simp]

中文:
定理 whiskerRight_apply
  结论: {L M : SemimoduleCat.{u} R} (f : L ⟶ M) (N : SemimoduleCat.{u} R)
  证明: rfl

@[simp]
-/
theorem whiskerRight_apply {L M : SemimoduleCat.{u} R} (f : L ⟶ M) (N : SemimoduleCat.{u} R)
    (l : L) (n : N) :
    (f ▷ N) (l otimesₜ n) = f l otimesₜ n :=
  rfl

@[simp]
/--
theorem `leftUnitor_hom_apply` / 定理 `leftUnitor_hom_apply`

English:
theorem leftUnitor_hom_apply
  given: {M : SemimoduleCat.{u} R} (r : R) (m : M)
  proof: TensorProduct.lid_tmul m r

@[simp]

中文:
定理 leftUnitor_hom_apply
  条件: {M : SemimoduleCat.{u} R} (r : R) (m : M)
  证明: TensorProduct.lid_tmul m r

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.lid_tmul, lid_tmul
-/
theorem leftUnitor_hom_apply {M : SemimoduleCat.{u} R} (r : R) (m : M) :
    ((fun_ M).hom : 𝟙_ (SemimoduleCat R) otimes M ⟶ M) (r otimesₜ[R] m) = r • m :=
  TensorProduct.lid_tmul m r

@[simp]
/--
theorem `leftUnitor_inv_apply` / 定理 `leftUnitor_inv_apply`

English:
theorem leftUnitor_inv_apply
  given: {M : SemimoduleCat.{u} R} (m : M)
  proof: TensorProduct.lid_symm_apply m

@[simp]

中文:
定理 leftUnitor_inv_apply
  条件: {M : SemimoduleCat.{u} R} (m : M)
  证明: TensorProduct.lid_symm_apply m

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.lid_symm_apply, lid_symm_apply
-/
theorem leftUnitor_inv_apply {M : SemimoduleCat.{u} R} (m : M) :
    ((fun_ M).inv : M ⟶ 𝟙_ (SemimoduleCat.{u} R) otimes M) m = 1 otimesₜ[R] m :=
  TensorProduct.lid_symm_apply m

@[simp]
/--
theorem `rightUnitor_hom_apply` / 定理 `rightUnitor_hom_apply`

English:
theorem rightUnitor_hom_apply
  given: {M : SemimoduleCat.{u} R} (m : M) (r : R)
  proof: TensorProduct.rid_tmul m r

@[simp]

中文:
定理 rightUnitor_hom_apply
  条件: {M : SemimoduleCat.{u} R} (m : M) (r : R)
  证明: TensorProduct.rid_tmul m r

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.rid_tmul, rid_tmul
-/
theorem rightUnitor_hom_apply {M : SemimoduleCat.{u} R} (m : M) (r : R) :
    ((ρ_ M).hom : M otimes 𝟙_ (SemimoduleCat R) ⟶ M) (m otimesₜ r) = r • m :=
  TensorProduct.rid_tmul m r

@[simp]
/--
theorem `rightUnitor_inv_apply` / 定理 `rightUnitor_inv_apply`

English:
theorem rightUnitor_inv_apply
  given: {M : SemimoduleCat.{u} R} (m : M)
  proof: TensorProduct.rid_symm_apply m

@[simp]

中文:
定理 rightUnitor_inv_apply
  条件: {M : SemimoduleCat.{u} R} (m : M)
  证明: TensorProduct.rid_symm_apply m

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.rid_symm_apply, rid_symm_apply
-/
theorem rightUnitor_inv_apply {M : SemimoduleCat.{u} R} (m : M) :
    ((ρ_ M).inv : M ⟶ M otimes 𝟙_ (SemimoduleCat.{u} R)) m = m otimesₜ[R] 1 :=
  TensorProduct.rid_symm_apply m

@[simp]
/--
theorem `associator_hom_apply` / 定理 `associator_hom_apply`

English:
theorem associator_hom_apply
  given: {M N K : SemimoduleCat.{u} R} (m : M) (n : N) (k : K)
  proof: rfl

@[simp]

中文:
定理 associator_hom_apply
  条件: {M N K : SemimoduleCat.{u} R} (m : M) (n : N) (k : K)
  证明: rfl

@[simp]
-/
theorem associator_hom_apply {M N K : SemimoduleCat.{u} R} (m : M) (n : N) (k : K) :
    ((α_ M N K).hom : (M otimes N) otimes K ⟶ M otimes N otimes K) (m otimesₜ n otimesₜ k) = m otimesₜ (n otimesₜ k) :=
  rfl

@[simp]
/--
theorem `associator_inv_apply` / 定理 `associator_inv_apply`

English:
theorem associator_inv_apply
  given: {M N K : SemimoduleCat.{u} R} (m : M) (n : N) (k : K)
  proof: rfl

中文:
定理 associator_inv_apply
  条件: {M N K : SemimoduleCat.{u} R} (m : M) (n : N) (k : K)
  证明: rfl
-/
theorem associator_inv_apply {M N K : SemimoduleCat.{u} R} (m : M) (n : N) (k : K) :
    ((α_ M N K).inv : M otimes N otimes K ⟶ (M otimes N) otimes K) (m otimesₜ (n otimesₜ k)) = m otimesₜ n otimesₜ k :=
  rfl

variable {M₁ M₂ M₃ M₄ : SemimoduleCat.{u} R}

section

variable (f : M₁ -> M₂ -> M₃) (h₁ : forall m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
  (h₂ : forall (a : R) m n, f (a • m) n = a • f m n)
  (h₃ : forall m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
  (h₄ : forall (a : R) m n, f m (a • n) = a • f m n)

/--
Definition of `tensorLift` / `tensorLift` 的定义

English:
definition tensorLift
  signature: : M₁ otimes M₂ ⟶ M₃
  body: ofHom TensorProduct.lift (LinearMap.mk₂ R f h₁ h₂ h₃ h₄)

@[simp]

中文:
定义 tensorLift
  签名: : M₁ otimes M₂ ⟶ M₃
  定义体: ofHom TensorProduct.lift (LinearMap.mk₂ R f h₁ h₂ h₃ h₄)

@[simp]

Depends on / 依赖: LinearMap, LinearMap.mk, TensorProduct, TensorProduct.lift
-/
def tensorLift : M₁ otimes M₂ ⟶ M₃ :=
ofHom TensorProduct.lift (LinearMap.mk₂ R f h₁ h₂ h₃ h₄)

@[simp]
/--
lemma `tensorLift_tmul` / 引理 `tensorLift_tmul`

English:
lemma tensorLift_tmul
  given: (m : M₁) (n : M₂)
  proof: rfl

中文:
引理 tensorLift_tmul
  条件: (m : M₁) (n : M₂)
  证明: rfl
-/
lemma tensorLift_tmul (m : M₁) (n : M₂) :
    tensorLift f h₁ h₂ h₃ h₄ (m otimesₜ n) = f m n := rfl

end

/--
lemma `tensor_ext` / 引理 `tensor_ext`

English:
lemma tensor_ext
  given: {f g : M₁ otimes M₂ ⟶ M₃} (h : forall m n, f.hom (m otimesₜ n) = g.hom (m otimesₜ n))
  proof: hom_ext TensorProduct.ext (by ext; apply h)

中文:
引理 tensor_ext
  条件: {f g : M₁ otimes M₂ ⟶ M₃} (h : 对任意 m n, f.hom (m otimesₜ n) = g.hom (m otimesₜ n))
  证明: hom_ext TensorProduct.ext (by ext; apply h)

Depends on / 依赖: TensorProduct, TensorProduct.ext, hom_ext
-/
lemma tensor_ext {f g : M₁ otimes M₂ ⟶ M₃} (h : forall m n, f.hom (m otimesₜ n) = g.hom (m otimesₜ n)) :
    f = g :=
hom_ext TensorProduct.ext (by ext; apply h)

/--
lemma `tensor_ext₃'` / 引理 `tensor_ext₃'`

English:
lemma tensor_ext₃'
  statement: {f g : (M₁ otimes M₂) otimes M₃ ⟶ M₄}
  proof: hom_ext TensorProduct.ext_threefold h

中文:
引理 tensor_ext₃'
  结论: {f g : (M₁ otimes M₂) otimes M₃ ⟶ M₄}
  证明: hom_ext TensorProduct.ext_threefold h

Depends on / 依赖: TensorProduct, TensorProduct.ext_threefold, ext_threefold, hom_ext
-/
lemma tensor_ext₃' {f g : (M₁ otimes M₂) otimes M₃ ⟶ M₄}
    (h : forall m₁ m₂ m₃, f (m₁ otimesₜ m₂ otimesₜ m₃) = g (m₁ otimesₜ m₂ otimesₜ m₃)) :
    f = g :=
hom_ext TensorProduct.ext_threefold h

/--
lemma `tensor_ext₃` / 引理 `tensor_ext₃`

English:
lemma tensor_ext₃
  statement: {f g : M₁ otimes (M₂ otimes M₃) ⟶ M₄}
  proof: by
  rw [← cancel_epi (α_ _ _ _).hom]
  exact tensor_ext₃' h

中文:
引理 tensor_ext₃
  结论: {f g : M₁ otimes (M₂ otimes M₃) ⟶ M₄}
  证明: by
  rw [← cancel_epi (α_ _ _ _).hom]
  exact tensor_ext₃' h

Depends on / 依赖: CommGrpCat, CommGrpCat.of, Concrete, Concrete.small_sections_of_hasLimit, GrpCat, HasLimit, MonCat, Types.Small.limitCone, cancel_epi, createsLimitOfReflectsIso, forget, liftedCone, limitCone, sections, small_sections_of_hasLimit
-/
lemma tensor_ext₃ {f g : M₁ otimes (M₂ otimes M₃) ⟶ M₄}
    (h : forall m₁ m₂ m₃, f (m₁ otimesₜ (m₂ otimesₜ m₃)) = g (m₁ otimesₜ (m₂ otimesₜ m₃))) :
    f = g := by
  rw [← cancel_epi (α_ _ _ _).hom]
  exact tensor_ext₃' h

end MonoidalCategory

end SemimoduleCat

namespace ModuleCat

variable {R : Type u} [CommRing R]

@[simps -isSimp]
/--
Instance `MonoidalCategory.instMonoidalCategoryStruct` / 实例 `MonoidalCategory.instMonoidalCategoryStruct`

English:
instance MonoidalCategory.instMonoidalCategoryStruct
  signature: :
  body: of R (TensorProduct R M N)
whiskerLeft M _ _ f := ofHom f.hom.lTensor M
whiskerRight f M := ofHom f.hom.rTensor M
tensorHom f g := ofHom TensorProduct.map f.hom g.hom
  tensorUnit := of R R
  associator M N K := (TensorProduct.assoc R M N K).toModuleIso
  leftUnitor M := (TensorProduct.lid R M).toMo

中文:
实例 MonoidalCategory.instMonoidalCategoryStruct
  签名: :
  定义体: of R (TensorProduct R M N)
whiskerLeft M _ _ f := ofHom f.hom.lTensor M
whiskerRight f M := ofHom f.hom.rTensor M
tensorHom f g := ofHom TensorProduct.map f.hom g.hom
  tensorUnit := of R R
  associator M N K := (TensorProduct.assoc R M N K).toModuleIso
  leftUnitor M := (TensorProduct.lid R M).toMo

Depends on / 依赖: TensorProduct
-/
instance MonoidalCategory.instMonoidalCategoryStruct :
    MonoidalCategoryStruct (ModuleCat.{u} R) where
  tensorObj M N := of R (TensorProduct R M N)
whiskerLeft M _ _ f := ofHom f.hom.lTensor M
whiskerRight f M := ofHom f.hom.rTensor M
tensorHom f g := ofHom TensorProduct.map f.hom g.hom
  tensorUnit := of R R
  associator M N K := (TensorProduct.assoc R M N K).toModuleIso
  leftUnitor M := (TensorProduct.lid R M).toModuleIso
  rightUnitor M := (TensorProduct.rid R M).toModuleIso

/--
Instance `monoidalCategory` / 实例 `monoidalCategory`

English:
instance monoidalCategory
  signature: : MonoidalCategory (ModuleCat.{u} R)
  body: Monoidal.induced equivalenceSemimoduleCat.functor
  { μIso _ _ := .refl _
    εIso := .refl _
    associator_eq _ _ _ := by ext1; exact TensorProduct.ext (TensorProduct.ext rfl)
    leftUnitor_eq _ := by ext1; exact TensorProduct.ext rfl
    rightUnitor_eq _ := by ext1; exact TensorProduct.ext rfl }

中文:
实例 monoidalCategory
  签名: : MonoidalCategory (ModuleCat.{u} R)
  定义体: Monoidal.induced equivalenceSemimoduleCat.functor
  { μIso _ _ := .refl _
    εIso := .refl _
    associator_eq _ _ _ := by ext1; exact TensorProduct.ext (TensorProduct.ext rfl)
    leftUnitor_eq _ := by ext1; exact TensorProduct.ext rfl
    rightUnitor_eq _ := by ext1; exact TensorProduct.ext rfl }

Depends on / 依赖: Monoidal, Monoidal.induced, TensorProduct, TensorProduct.ext, associator_eq, equivalenceSemimoduleCat, equivalenceSemimoduleCat.functor, functor, induced, leftUnitor_eq, rightUnitor_eq
-/
instance monoidalCategory : MonoidalCategory (ModuleCat.{u} R) :=
  Monoidal.induced equivalenceSemimoduleCat.functor
  { μIso _ _ := .refl _
    εIso := .refl _
    associator_eq _ _ _ := by ext1; exact TensorProduct.ext (TensorProduct.ext rfl)
    leftUnitor_eq _ := by ext1; exact TensorProduct.ext rfl
    rightUnitor_eq _ := by ext1; exact TensorProduct.ext rfl }

open MonoidalCategory

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommRing ((𝟙_ (ModuleCat.{u} R) : ModuleCat.{u} R) : Type u)
  body: inferInstanceAs CommRing R

中文:
实例 :
  签名: CommRing ((𝟙_ (ModuleCat.{u} R) : ModuleCat.{u} R) : 类型u)
  定义体: inferInstanceAs CommRing R

Depends on / 依赖: CommRing
-/
instance : CommRing ((𝟙_ (ModuleCat.{u} R) : ModuleCat.{u} R) : Type u) :=
inferInstanceAs CommRing R

/--
theorem `hom_tensorHom` / 定理 `hom_tensorHom`

English:
theorem hom_tensorHom
  given: {K L M N : ModuleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N)
  proof: rfl

中文:
定理 hom_tensorHom
  条件: {K L M N : ModuleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N)
  证明: rfl
-/
theorem hom_tensorHom {K L M N : ModuleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) :
    (f otimesₘ g).hom = TensorProduct.map f.hom g.hom :=
  rfl

/--
theorem `hom_whiskerLeft` / 定理 `hom_whiskerLeft`

English:
theorem hom_whiskerLeft
  given: (L : ModuleCat.{u} R) {M N : ModuleCat.{u} R} (f : M ⟶ N)
  proof: rfl

中文:
定理 hom_whiskerLeft
  条件: (L : ModuleCat.{u} R) {M N : ModuleCat.{u} R} (f : M ⟶ N)
  证明: rfl
-/
theorem hom_whiskerLeft (L : ModuleCat.{u} R) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (L ◁ f).hom = f.hom.lTensor L :=
  rfl

/--
theorem `hom_whiskerRight` / 定理 `hom_whiskerRight`

English:
theorem hom_whiskerRight
  given: {L M : ModuleCat.{u} R} (f : L ⟶ M) (N : ModuleCat.{u} R)
  proof: rfl

中文:
定理 hom_whiskerRight
  条件: {L M : ModuleCat.{u} R} (f : L ⟶ M) (N : ModuleCat.{u} R)
  证明: rfl
-/
theorem hom_whiskerRight {L M : ModuleCat.{u} R} (f : L ⟶ M) (N : ModuleCat.{u} R) :
    (f ▷ N).hom = f.hom.rTensor N :=
  rfl

/--
theorem `hom_hom_leftUnitor` / 定理 `hom_hom_leftUnitor`

English:
theorem hom_hom_leftUnitor
  given: {M : ModuleCat.{u} R}
  proof: rfl

中文:
定理 hom_hom_leftUnitor
  条件: {M : ModuleCat.{u} R}
  证明: rfl
-/
theorem hom_hom_leftUnitor {M : ModuleCat.{u} R} :
    (fun_ M).hom.hom = (TensorProduct.lid _ _).toLinearMap :=
  rfl

/--
theorem `hom_inv_leftUnitor` / 定理 `hom_inv_leftUnitor`

English:
theorem hom_inv_leftUnitor
  given: {M : ModuleCat.{u} R}
  proof: rfl

中文:
定理 hom_inv_leftUnitor
  条件: {M : ModuleCat.{u} R}
  证明: rfl
-/
theorem hom_inv_leftUnitor {M : ModuleCat.{u} R} :
    (fun_ M).inv.hom = (TensorProduct.lid _ _).symm.toLinearMap :=
  rfl

/--
theorem `hom_hom_rightUnitor` / 定理 `hom_hom_rightUnitor`

English:
theorem hom_hom_rightUnitor
  given: {M : ModuleCat.{u} R}
  proof: rfl

中文:
定理 hom_hom_rightUnitor
  条件: {M : ModuleCat.{u} R}
  证明: rfl
-/
theorem hom_hom_rightUnitor {M : ModuleCat.{u} R} :
    (ρ_ M).hom.hom = (TensorProduct.rid _ _).toLinearMap :=
  rfl

/--
theorem `hom_inv_rightUnitor` / 定理 `hom_inv_rightUnitor`

English:
theorem hom_inv_rightUnitor
  given: {M : ModuleCat.{u} R}
  proof: rfl

中文:
定理 hom_inv_rightUnitor
  条件: {M : ModuleCat.{u} R}
  证明: rfl
-/
theorem hom_inv_rightUnitor {M : ModuleCat.{u} R} :
    (ρ_ M).inv.hom = (TensorProduct.rid _ _).symm.toLinearMap :=
  rfl

/--
theorem `hom_hom_associator` / 定理 `hom_hom_associator`

English:
theorem hom_hom_associator
  given: {M N K : ModuleCat.{u} R}
  proof: rfl

中文:
定理 hom_hom_associator
  条件: {M N K : ModuleCat.{u} R}
  证明: rfl
-/
theorem hom_hom_associator {M N K : ModuleCat.{u} R} :
    (α_ M N K).hom.hom = (TensorProduct.assoc _ _ _ _).toLinearMap :=
  rfl

/--
theorem `hom_inv_associator` / 定理 `hom_inv_associator`

English:
theorem hom_inv_associator
  given: {M N K : ModuleCat.{u} R}
  proof: rfl

中文:
定理 hom_inv_associator
  条件: {M N K : ModuleCat.{u} R}
  证明: rfl
-/
theorem hom_inv_associator {M N K : ModuleCat.{u} R} :
    (α_ M N K).inv.hom = (TensorProduct.assoc _ _ _ _).symm.toLinearMap :=
  rfl

namespace MonoidalCategory

@[simp]
/--
theorem `tensorHom_tmul` / 定理 `tensorHom_tmul`

English:
theorem tensorHom_tmul
  given: {K L M N : ModuleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) (k : K) (m : M)
  proof: rfl

@[simp]

中文:
定理 tensorHom_tmul
  条件: {K L M N : ModuleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) (k : K) (m : M)
  证明: rfl

@[simp]
-/
theorem tensorHom_tmul {K L M N : ModuleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) (k : K) (m : M) :
    (f otimesₘ g) (k otimesₜ m) = f k otimesₜ g m :=
  rfl

@[simp]
/--
theorem `whiskerLeft_apply` / 定理 `whiskerLeft_apply`

English:
theorem whiskerLeft_apply
  statement: (L : ModuleCat.{u} R) {M N : ModuleCat.{u} R} (f : M ⟶ N)
  proof: rfl

@[simp]

中文:
定理 whiskerLeft_apply
  结论: (L : ModuleCat.{u} R) {M N : ModuleCat.{u} R} (f : M ⟶ N)
  证明: rfl

@[simp]
-/
theorem whiskerLeft_apply (L : ModuleCat.{u} R) {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (l : L) (m : M) :
    (L ◁ f) (l otimesₜ m) = l otimesₜ f m :=
  rfl

@[simp]
/--
theorem `whiskerRight_apply` / 定理 `whiskerRight_apply`

English:
theorem whiskerRight_apply
  statement: {L M : ModuleCat.{u} R} (f : L ⟶ M) (N : ModuleCat.{u} R)
  proof: rfl

@[simp]

中文:
定理 whiskerRight_apply
  结论: {L M : ModuleCat.{u} R} (f : L ⟶ M) (N : ModuleCat.{u} R)
  证明: rfl

@[simp]
-/
theorem whiskerRight_apply {L M : ModuleCat.{u} R} (f : L ⟶ M) (N : ModuleCat.{u} R)
    (l : L) (n : N) :
    (f ▷ N) (l otimesₜ n) = f l otimesₜ n :=
  rfl

@[simp]
/--
theorem `leftUnitor_hom_apply` / 定理 `leftUnitor_hom_apply`

English:
theorem leftUnitor_hom_apply
  given: {M : ModuleCat.{u} R} (r : R) (m : M)
  proof: TensorProduct.lid_tmul m r

@[simp]

中文:
定理 leftUnitor_hom_apply
  条件: {M : ModuleCat.{u} R} (r : R) (m : M)
  证明: TensorProduct.lid_tmul m r

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.lid_tmul, lid_tmul
-/
theorem leftUnitor_hom_apply {M : ModuleCat.{u} R} (r : R) (m : M) :
    ((fun_ M).hom : 𝟙_ (ModuleCat R) otimes M ⟶ M) (r otimesₜ[R] m) = r • m :=
  TensorProduct.lid_tmul m r

@[simp]
/--
theorem `leftUnitor_inv_apply` / 定理 `leftUnitor_inv_apply`

English:
theorem leftUnitor_inv_apply
  given: {M : ModuleCat.{u} R} (m : M)
  proof: TensorProduct.lid_symm_apply m

@[simp]

中文:
定理 leftUnitor_inv_apply
  条件: {M : ModuleCat.{u} R} (m : M)
  证明: TensorProduct.lid_symm_apply m

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.lid_symm_apply, lid_symm_apply
-/
theorem leftUnitor_inv_apply {M : ModuleCat.{u} R} (m : M) :
    ((fun_ M).inv : M ⟶ 𝟙_ (ModuleCat.{u} R) otimes M) m = 1 otimesₜ[R] m :=
  TensorProduct.lid_symm_apply m

@[simp]
/--
theorem `rightUnitor_hom_apply` / 定理 `rightUnitor_hom_apply`

English:
theorem rightUnitor_hom_apply
  given: {M : ModuleCat.{u} R} (m : M) (r : R)
  proof: TensorProduct.rid_tmul m r

@[simp]

中文:
定理 rightUnitor_hom_apply
  条件: {M : ModuleCat.{u} R} (m : M) (r : R)
  证明: TensorProduct.rid_tmul m r

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.rid_tmul, rid_tmul
-/
theorem rightUnitor_hom_apply {M : ModuleCat.{u} R} (m : M) (r : R) :
    ((ρ_ M).hom : M otimes 𝟙_ (ModuleCat R) ⟶ M) (m otimesₜ r) = r • m :=
  TensorProduct.rid_tmul m r

@[simp]
/--
theorem `rightUnitor_inv_apply` / 定理 `rightUnitor_inv_apply`

English:
theorem rightUnitor_inv_apply
  given: {M : ModuleCat.{u} R} (m : M)
  proof: TensorProduct.rid_symm_apply m

@[simp]

中文:
定理 rightUnitor_inv_apply
  条件: {M : ModuleCat.{u} R} (m : M)
  证明: TensorProduct.rid_symm_apply m

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.rid_symm_apply, rid_symm_apply
-/
theorem rightUnitor_inv_apply {M : ModuleCat.{u} R} (m : M) :
    ((ρ_ M).inv : M ⟶ M otimes 𝟙_ (ModuleCat.{u} R)) m = m otimesₜ[R] 1 :=
  TensorProduct.rid_symm_apply m

@[simp]
/--
theorem `associator_hom_apply` / 定理 `associator_hom_apply`

English:
theorem associator_hom_apply
  given: {M N K : ModuleCat.{u} R} (m : M) (n : N) (k : K)
  proof: rfl

@[simp]

中文:
定理 associator_hom_apply
  条件: {M N K : ModuleCat.{u} R} (m : M) (n : N) (k : K)
  证明: rfl

@[simp]
-/
theorem associator_hom_apply {M N K : ModuleCat.{u} R} (m : M) (n : N) (k : K) :
    ((α_ M N K).hom : (M otimes N) otimes K ⟶ M otimes N otimes K) (m otimesₜ n otimesₜ k) = m otimesₜ (n otimesₜ k) :=
  rfl

@[simp]
/--
theorem `associator_inv_apply` / 定理 `associator_inv_apply`

English:
theorem associator_inv_apply
  given: {M N K : ModuleCat.{u} R} (m : M) (n : N) (k : K)
  proof: rfl

中文:
定理 associator_inv_apply
  条件: {M N K : ModuleCat.{u} R} (m : M) (n : N) (k : K)
  证明: rfl
-/
theorem associator_inv_apply {M N K : ModuleCat.{u} R} (m : M) (n : N) (k : K) :
    ((α_ M N K).inv : M otimes N otimes K ⟶ (M otimes N) otimes K) (m otimesₜ (n otimesₜ k)) = m otimesₜ n otimesₜ k :=
  rfl

variable {M₁ M₂ M₃ M₄ : ModuleCat.{u} R}

section

variable (f : M₁ -> M₂ -> M₃) (h₁ : forall m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
  (h₂ : forall (a : R) m n, f (a • m) n = a • f m n)
  (h₃ : forall m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
  (h₄ : forall (a : R) m n, f m (a • n) = a • f m n)

/--
Definition of `tensorLift` / `tensorLift` 的定义

English:
definition tensorLift
  signature: : M₁ otimes M₂ ⟶ M₃
  body: ofHom TensorProduct.lift (LinearMap.mk₂ R f h₁ h₂ h₃ h₄)

@[simp]

中文:
定义 tensorLift
  签名: : M₁ otimes M₂ ⟶ M₃
  定义体: ofHom TensorProduct.lift (LinearMap.mk₂ R f h₁ h₂ h₃ h₄)

@[simp]

Depends on / 依赖: LinearMap, LinearMap.mk, TensorProduct, TensorProduct.lift
-/
def tensorLift : M₁ otimes M₂ ⟶ M₃ :=
ofHom TensorProduct.lift (LinearMap.mk₂ R f h₁ h₂ h₃ h₄)

@[simp]
/--
lemma `tensorLift_tmul` / 引理 `tensorLift_tmul`

English:
lemma tensorLift_tmul
  given: (m : M₁) (n : M₂)
  proof: rfl

中文:
引理 tensorLift_tmul
  条件: (m : M₁) (n : M₂)
  证明: rfl
-/
lemma tensorLift_tmul (m : M₁) (n : M₂) :
    tensorLift f h₁ h₂ h₃ h₄ (m otimesₜ n) = f m n := rfl

end

/--
lemma `tensor_ext` / 引理 `tensor_ext`

English:
lemma tensor_ext
  given: {f g : M₁ otimes M₂ ⟶ M₃} (h : forall m n, f.hom (m otimesₜ n) = g.hom (m otimesₜ n))
  proof: hom_ext TensorProduct.ext (by ext; apply h)

中文:
引理 tensor_ext
  条件: {f g : M₁ otimes M₂ ⟶ M₃} (h : 对任意 m n, f.hom (m otimesₜ n) = g.hom (m otimesₜ n))
  证明: hom_ext TensorProduct.ext (by ext; apply h)

Depends on / 依赖: TensorProduct, TensorProduct.ext, hom_ext
-/
lemma tensor_ext {f g : M₁ otimes M₂ ⟶ M₃} (h : forall m n, f.hom (m otimesₜ n) = g.hom (m otimesₜ n)) :
    f = g :=
hom_ext TensorProduct.ext (by ext; apply h)

/--
lemma `tensor_ext₃'` / 引理 `tensor_ext₃'`

English:
lemma tensor_ext₃'
  statement: {f g : (M₁ otimes M₂) otimes M₃ ⟶ M₄}
  proof: hom_ext TensorProduct.ext_threefold h

中文:
引理 tensor_ext₃'
  结论: {f g : (M₁ otimes M₂) otimes M₃ ⟶ M₄}
  证明: hom_ext TensorProduct.ext_threefold h

Depends on / 依赖: TensorProduct, TensorProduct.ext_threefold, ext_threefold, hom_ext
-/
lemma tensor_ext₃' {f g : (M₁ otimes M₂) otimes M₃ ⟶ M₄}
    (h : forall m₁ m₂ m₃, f (m₁ otimesₜ m₂ otimesₜ m₃) = g (m₁ otimesₜ m₂ otimesₜ m₃)) :
    f = g :=
hom_ext TensorProduct.ext_threefold h

/--
lemma `tensor_ext₃` / 引理 `tensor_ext₃`

English:
lemma tensor_ext₃
  statement: {f g : M₁ otimes (M₂ otimes M₃) ⟶ M₄}
  proof: by
  rw [← cancel_epi (α_ _ _ _).hom]
  exact tensor_ext₃' h

中文:
引理 tensor_ext₃
  结论: {f g : M₁ otimes (M₂ otimes M₃) ⟶ M₄}
  证明: by
  rw [← cancel_epi (α_ _ _ _).hom]
  exact tensor_ext₃' h

Depends on / 依赖: cancel_epi
-/
lemma tensor_ext₃ {f g : M₁ otimes (M₂ otimes M₃) ⟶ M₄}
    (h : forall m₁ m₂ m₃, f (m₁ otimesₜ (m₂ otimesₜ m₃)) = g (m₁ otimesₜ (m₂ otimesₜ m₃))) :
    f = g := by
  rw [← cancel_epi (α_ _ _ _).hom]
  exact tensor_ext₃' h

end MonoidalCategory

open Opposite

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidalPreadditive (ModuleCat.{u} R)
  body: by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intros
    ext : 1
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp [ModuleCat.hom_whiskerLeft]
  · intros
    ext : 1
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp [ModuleCat.hom_whis

中文:
实例 :
  签名: MonoidalPreadditive (ModuleCat.{u} R)
  定义体: by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intros
    ext : 1
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp [ModuleCat.hom_whiskerLeft]
  · intros
    ext : 1
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp [ModuleCat.hom_whis

Depends on / 依赖: LinearMap, LinearMap.ext, ModuleCat, ModuleCat.hom_whiskerLeft, ModuleCat.hom_whiskerRight, TensorProduct, TensorProduct.ext, hom_whiskerLeft, hom_whiskerRight, intros
-/
instance : MonoidalPreadditive (ModuleCat.{u} R) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intros
    ext : 1
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp [ModuleCat.hom_whiskerLeft]
  · intros
    ext : 1
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp [ModuleCat.hom_whiskerRight]
  · intros
    ext : 1
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp [ModuleCat.hom_whiskerLeft]
  · intros
    ext : 1
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp [ModuleCat.hom_whiskerRight]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidalLinear R (ModuleCat.{u} R)
  body: by
  refine ⟨?_, ?_⟩
  · intros
    ext : 1
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp [ModuleCat.hom_whiskerLeft]
  · intros
    ext : 1
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp [ModuleCat.hom_whiskerRight

中文:
实例 :
  签名: MonoidalLinear R (ModuleCat.{u} R)
  定义体: by
  refine ⟨?_, ?_⟩
  · intros
    ext : 1
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp [ModuleCat.hom_whiskerLeft]
  · intros
    ext : 1
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp [ModuleCat.hom_whiskerRight

Depends on / 依赖: LinearMap, LinearMap.ext, ModuleCat, ModuleCat.hom_whiskerLeft, ModuleCat.hom_whiskerRight, TensorProduct, TensorProduct.ext, hom_whiskerLeft, hom_whiskerRight, intros
-/
instance : MonoidalLinear R (ModuleCat.{u} R) := by
  refine ⟨?_, ?_⟩
  · intros
    ext : 1
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp [ModuleCat.hom_whiskerLeft]
  · intros
    ext : 1
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp [ModuleCat.hom_whiskerRight]

/--
lemma `ofHom₂_compr₂` / 引理 `ofHom₂_compr₂`

English:
lemma ofHom₂_compr₂
  given: {M N P Q : ModuleCat.{u} R} (f : M ->ₗ[R] N ->ₗ[R] P) (g : P ->ₗ[R] Q)
  proof: rfl

中文:
引理 ofHom₂_compr₂
  条件: {M N P Q : ModuleCat.{u} R} (f : M ->ₗ[R] N ->ₗ[R] P) (g : P ->ₗ[R] Q)
  证明: rfl
-/
@[simp] lemma ofHom₂_compr₂ {M N P Q : ModuleCat.{u} R} (f : M ->ₗ[R] N ->ₗ[R] P) (g : P ->ₗ[R] Q) :
    ofHom₂ (f.compr₂ g) = ofHom₂ f ≫ ofHom (Linear.rightComp R _ (ofHom g)) := rfl

end ModuleCat
