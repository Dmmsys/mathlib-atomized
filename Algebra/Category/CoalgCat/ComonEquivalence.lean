/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Category.CoalgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Monoidal.Braided.Opposite
public import Mathlib.CategoryTheory.Monoidal.Comon_
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Coalgebra.TensorProduct
public import Mathlib.Tactic.SuppressCompilation

/-!
# The category equivalence between `R`-coalgebras and comonoid objects in `R-Mod`

Given a commutative ring `R`, this file defines the equivalence of categories between
`R`-coalgebras and comonoid objects in the category of `R`-modules.

We then use this to set up boilerplate for the `Coalgebra` instance on a tensor product of
coalgebras defined in `Mathlib/RingTheory/Coalgebra/TensorProduct.lean`.

## Implementation notes

We make the definition `CoalgCat.instMonoidalCategoryAux` in this file, which is the
monoidal structure on `CoalgCat` induced by the equivalence with `Comon(R-Mod)`. We
use this to show the comultiplication and counit on a tensor product of coalgebras satisfy
the coalgebra axioms, but our actual `MonoidalCategory` instance on `CoalgCat` is
constructed in `Mathlib/Algebra/Category/CoalgCat/Monoidal.lean` to have better
definitional equalities.

-/

@[expose] public section

suppress_compilation

universe v u

namespace CoalgCat

open CategoryTheory MonoidalCategory ComonObj

variable {R : Type u} [CommRing R]

@[simps counit comul]
noncomputable instance (X : CoalgCat R) : ComonObj (ModuleCat.of R X) where
  counit := ModuleCat.ofHom Coalgebra.counit
  comul := ModuleCat.ofHom Coalgebra.comul
counit_comul := ModuleCat.hom_ext by simpa using! Coalgebra.rTensor_counit_comp_comul
comul_counit := ModuleCat.hom_ext by simpa using! Coalgebra.lTensor_counit_comp_comul
comul_assoc := ModuleCat.hom_ext by simp_rw [ModuleCat.of_coe]; exact Coalgebra.coassoc.symm

/-- An `R`-coalgebra is a comonoid object in the category of `R`-modules. -/
@[simps X]
/--
Definition of `toComonObj` / `toComonObj` 的定义

English:
definition toComonObj
  signature: (X : CoalgCat R)
  body: ⟨ModuleCat.of R X⟩

中文:
定义 toComonObj
  签名: (X : CoalgCat R)
  定义体: ⟨ModuleCat.of R X⟩

Depends on / 依赖: ModuleCat, ModuleCat.of
-/
noncomputable def toComonObj (X : CoalgCat R) : Comon (ModuleCat R) := ⟨ModuleCat.of R X⟩

variable (R) in
/-- The natural functor from `R`-coalgebras to comonoid objects in the category of `R`-modules. -/
@[simps]
/--
Definition of `toComon` / `toComon` 的定义

English:
definition toComon
  signature: : CoalgCat R ⥤ Comon (ModuleCat R) where
  body: toComonObj X
  map f :=
    { hom := ModuleCat.ofHom f.1
      isComonHom_hom :=
        { hom_counit := ModuleCat.hom_ext f.1.counit_comp
          hom_comul := ModuleCat.hom_ext f.1.map_comp_comul.symm } }

中文:
定义 toComon
  签名: : CoalgCat R ⥤ Comon (ModuleCat R) where
  定义体: toComonObj X
  map f :=
    { hom := ModuleCat.ofHom f.1
      isComonHom_hom :=
        { hom_counit := ModuleCat.hom_ext f.1.counit_comp
          hom_comul := ModuleCat.hom_ext f.1.map_comp_comul.symm } }

Depends on / 依赖: toComonObj
-/
def toComon : CoalgCat R ⥤ Comon (ModuleCat R) where
  obj X := toComonObj X
  map f :=
    { hom := ModuleCat.ofHom f.1
      isComonHom_hom :=
        { hom_counit := ModuleCat.hom_ext f.1.counit_comp
          hom_comul := ModuleCat.hom_ext f.1.map_comp_comul.symm } }

/-- A comonoid object in the category of `R`-modules has a natural comultiplication
and counit. -/
@[simps]
/--
Instance `ofComonObjCoalgebraStruct` / 实例 `ofComonObjCoalgebraStruct`

English:
instance ofComonObjCoalgebraStruct
  signature: (X : ModuleCat R) [ComonObj X]
  body: Δ[X].hom
  counit := ε[X].hom

中文:
实例 ofComonObjCoalgebraStruct
  签名: (X : ModuleCat R) [ComonObj X]
  定义体: Δ[X].hom
  counit := ε[X].hom
-/
noncomputable instance ofComonObjCoalgebraStruct (X : ModuleCat R) [ComonObj X] :
    CoalgebraStruct R X where
  comul := Δ[X].hom
  counit := ε[X].hom

/--
Definition of `ofComonObj` / `ofComonObj` 的定义

English:
definition ofComonObj
  signature: (X : ModuleCat R) [ComonObj X]
  body: { ModuleCat.of R X with
    instCoalgebra :=
      { ofComonObjCoalgebraStruct X with
        coassoc := ModuleCat.hom_ext_iff.mp (comul_assoc X).symm
        rTensor_counit_comp_comul := ModuleCat.hom_ext_iff.mp (counit_comul X)
        lTensor_counit_comp_comul := ModuleCat.hom_ext_iff.mp (comul_c

中文:
定义 ofComonObj
  签名: (X : ModuleCat R) [ComonObj X]
  定义体: { ModuleCat.of R X with
    instCoalgebra :=
      { ofComonObjCoalgebraStruct X with
        coassoc := ModuleCat.hom_ext_iff.mp (comul_assoc X).symm
        rTensor_counit_comp_comul := ModuleCat.hom_ext_iff.mp (counit_comul X)
        lTensor_counit_comp_comul := ModuleCat.hom_ext_iff.mp (comul_c

Depends on / 依赖: ModuleCat, ModuleCat.hom_ext_iff.mp, ModuleCat.of, coassoc, comul_assoc, comul_counit, counit_comul, hom_ext_iff, instCoalgebra, lTensor_counit_comp_comul, ofComonObjCoalgebraStruct, rTensor_counit_comp_comul
-/
noncomputable def ofComonObj (X : ModuleCat R) [ComonObj X] : CoalgCat R :=
  { ModuleCat.of R X with
    instCoalgebra :=
      { ofComonObjCoalgebraStruct X with
        coassoc := ModuleCat.hom_ext_iff.mp (comul_assoc X).symm
        rTensor_counit_comp_comul := ModuleCat.hom_ext_iff.mp (counit_comul X)
        lTensor_counit_comp_comul := ModuleCat.hom_ext_iff.mp (comul_counit X) } }

variable (R)

/--
Definition of `ofComon` / `ofComon` 的定义

English:
definition ofComon
  signature: : Comon (ModuleCat R) ⥤ CoalgCat R where
  body: ofComonObj X.X
  map f :=
    { toCoalgHom' :=
      { f.hom.hom with
        counit_comp := ModuleCat.hom_ext_iff.mp (IsComonHom.hom_counit f.hom)
        map_comp_comul := ModuleCat.hom_ext_iff.mp ((IsComonHom.hom_comul f.hom).symm) } }

中文:
定义 ofComon
  签名: : Comon (ModuleCat R) ⥤ CoalgCat R where
  定义体: ofComonObj X.X
  map f :=
    { toCoalgHom' :=
      { f.hom.hom with
        counit_comp := ModuleCat.hom_ext_iff.mp (IsComonHom.hom_counit f.hom)
        map_comp_comul := ModuleCat.hom_ext_iff.mp ((IsComonHom.hom_comul f.hom).symm) } }

Depends on / 依赖: ofComonObj
-/
noncomputable def ofComon : Comon (ModuleCat R) ⥤ CoalgCat R where
  obj X := ofComonObj X.X
  map f :=
    { toCoalgHom' :=
      { f.hom.hom with
        counit_comp := ModuleCat.hom_ext_iff.mp (IsComonHom.hom_counit f.hom)
        map_comp_comul := ModuleCat.hom_ext_iff.mp ((IsComonHom.hom_comul f.hom).symm) } }

/-- The natural category equivalence between `R`-coalgebras and comonoid objects in the
category of `R`-modules. -/
@[simps]
/--
Definition of `comonEquivalence` / `comonEquivalence` 的定义

English:
definition comonEquivalence
  signature: : CoalgCat R ≌ Comon (ModuleCat R) where
  body: toComon R
  inverse := ofComon R
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) fun _ => by rfl
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) fun _ => by rfl

中文:
定义 comonEquivalence
  签名: : CoalgCat R ≌ Comon (ModuleCat R) where
  定义体: toComon R
  inverse := ofComon R
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) fun _ => by rfl
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) fun _ => by rfl

Depends on / 依赖: toComon
-/
def comonEquivalence : CoalgCat R ≌ Comon (ModuleCat R) where
  functor := toComon R
  inverse := ofComon R
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) fun _ => by rfl
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) fun _ => by rfl

variable {R}

/-- The monoidal category structure on the category of `R`-coalgebras induced by the
equivalence with `Comon(R-Mod)`. This is just an auxiliary definition; the `MonoidalCategory`
instance we make in `Mathlib/Algebra/Category/CoalgCat/Monoidal.lean` has better
definitional equalities. -/
@[instance_reducible]
/--
Definition of `instMonoidalCategoryAux` / `instMonoidalCategoryAux` 的定义

English:
definition instMonoidalCategoryAux
  signature: : MonoidalCategory (CoalgCat R)
  body: Monoidal.transport (comonEquivalence R).symm

中文:
定义 instMonoidalCategoryAux
  签名: : MonoidalCategory (CoalgCat R)
  定义体: Monoidal.transport (comonEquivalence R).symm

Depends on / 依赖: Monoidal, Monoidal.transport, comonEquivalence, transport
-/
noncomputable def instMonoidalCategoryAux : MonoidalCategory (CoalgCat R) :=
  Monoidal.transport (comonEquivalence R).symm

namespace MonoidalCategoryAux

variable {M N P Q : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module R M] [Module R N] [Module R P] [Module R Q] [Coalgebra R M] [Coalgebra R N]
    [Coalgebra R P] [Coalgebra R Q]

attribute [local instance] instMonoidalCategoryAux

open MonoidalCategory ModuleCat.MonoidalCategory

set_option backward.isDefEq.respectTransparency false in
/--
theorem `tensorObj_comul` / 定理 `tensorObj_comul`

English:
theorem tensorObj_comul
  given: (K L : CoalgCat R)
  proof: by
  rw [ofComonObjCoalgebraStruct_comul]
  simp only [Comon.monoidal_tensorObj_comon_comul,
    MonObj.tensorObj.mul_def, unop_comp, unop_tensorObj, unop_tensorHom,
    BraidedCategory.unop_tensorμ, tensorμ_eq_tensorTensorTensorComm, ModuleCat.hom_comp,
    ModuleCat.hom_ofHom]
  rfl

中文:
定理 tensorObj_comul
  条件: (K L : CoalgCat R)
  证明: by
  rw [ofComonObjCoalgebraStruct_comul]
  simp only [Comon.monoidal_tensorObj_comon_comul,
    MonObj.tensorObj.mul_def, unop_comp, unop_tensorObj, unop_tensorHom,
    BraidedCategory.unop_tensorμ, tensorμ_eq_tensorTensorTensorComm, ModuleCat.hom_comp,
    ModuleCat.hom_ofHom]
  rfl

Depends on / 依赖: CoalgCat, otimes
-/
theorem tensorObj_comul (K L : CoalgCat R) :
    Coalgebra.comul (R := R) (A := (K otimes L : CoalgCat R))
      = (TensorProduct.tensorTensorTensorComm R K K L L).toLinearMap
      ∘ₗ TensorProduct.map Coalgebra.comul Coalgebra.comul := by
  rw [ofComonObjCoalgebraStruct_comul]
  simp only [Comon.monoidal_tensorObj_comon_comul,
    MonObj.tensorObj.mul_def, unop_comp, unop_tensorObj, unop_tensorHom,
    BraidedCategory.unop_tensorμ, tensorμ_eq_tensorTensorTensorComm, ModuleCat.hom_comp,
    ModuleCat.hom_ofHom]
  rfl

/--
theorem `tensorHom_toLinearMap` / 定理 `tensorHom_toLinearMap`

English:
theorem tensorHom_toLinearMap
  given: (f : M ->ₗc[R] N) (g : P ->ₗc[R] Q)
  proof: rfl

中文:
定理 tensorHom_toLinearMap
  条件: (f : M ->ₗc[R] N) (g : P ->ₗc[R] Q)
  证明: rfl
-/
theorem tensorHom_toLinearMap (f : M ->ₗc[R] N) (g : P ->ₗc[R] Q) :
    (CoalgCat.ofHom f otimesₘ CoalgCat.ofHom g).1.toLinearMap
      = TensorProduct.map f.toLinearMap g.toLinearMap := rfl

/--
theorem `associator_hom_toLinearMap` / 定理 `associator_hom_toLinearMap`

English:
theorem associator_hom_toLinearMap
  proof: TensorProduct.ext TensorProduct.ext by ext; rfl

中文:
定理 associator_hom_toLinearMap
  证明: TensorProduct.ext TensorProduct.ext by ext; rfl

Depends on / 依赖: TensorProduct, TensorProduct.ext
-/
theorem associator_hom_toLinearMap :
    (α_ (CoalgCat.of R M) (CoalgCat.of R N) (CoalgCat.of R P)).hom.1.toLinearMap
      = (TensorProduct.assoc R M N P).toLinearMap :=
TensorProduct.ext TensorProduct.ext by ext; rfl

/--
theorem `leftUnitor_hom_toLinearMap` / 定理 `leftUnitor_hom_toLinearMap`

English:
theorem leftUnitor_hom_toLinearMap
  proof: TensorProduct.ext by ext; rfl

中文:
定理 leftUnitor_hom_toLinearMap
  证明: TensorProduct.ext by ext; rfl

Depends on / 依赖: TensorProduct, TensorProduct.ext
-/
theorem leftUnitor_hom_toLinearMap :
    (fun_ (CoalgCat.of R M)).hom.1.toLinearMap = (TensorProduct.lid R M).toLinearMap :=
TensorProduct.ext by ext; rfl

/--
theorem `rightUnitor_hom_toLinearMap` / 定理 `rightUnitor_hom_toLinearMap`

English:
theorem rightUnitor_hom_toLinearMap
  proof: TensorProduct.ext by ext; rfl

中文:
定理 rightUnitor_hom_toLinearMap
  证明: TensorProduct.ext by ext; rfl

Depends on / 依赖: TensorProduct, TensorProduct.ext
-/
theorem rightUnitor_hom_toLinearMap :
    (ρ_ (CoalgCat.of R M)).hom.1.toLinearMap = (TensorProduct.rid R M).toLinearMap :=
TensorProduct.ext by ext; rfl

open TensorProduct

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] MonObj.tensorObj.one_def MonObj.tensorObj.mul_def in
/--
theorem `comul_tensorObj` / 定理 `comul_tensorObj`

English:
theorem comul_tensorObj
  proof: by
  rw [ofComonObjCoalgebraStruct_comul]
  simp [tensorμ_eq_tensorTensorTensorComm, TensorProduct.comul_def,
    AlgebraTensorModule.tensorTensorTensorComm_eq]
  rfl

中文:
定理 comul_tensorObj
  证明: by
  rw [ofComonObjCoalgebraStruct_comul]
  simp [tensorμ_eq_tensorTensorTensorComm, TensorProduct.comul_def,
    AlgebraTensorModule.tensorTensorTensorComm_eq]
  rfl

Depends on / 依赖: CoalgCat, CoalgCat.of, otimes
-/
theorem comul_tensorObj :
    Coalgebra.comul (R := R) (A := (CoalgCat.of R M otimes CoalgCat.of R N : CoalgCat R))
      = Coalgebra.comul (A := M otimes[R] N) := by
  rw [ofComonObjCoalgebraStruct_comul]
  simp [tensorμ_eq_tensorTensorTensorComm, TensorProduct.comul_def,
    AlgebraTensorModule.tensorTensorTensorComm_eq]
  rfl

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] MonObj.tensorObj.one_def MonObj.tensorObj.mul_def in
/--
theorem `comul_tensorObj_tensorObj_right` / 定理 `comul_tensorObj_tensorObj_right`

English:
theorem comul_tensorObj_tensorObj_right
  proof: by
  rw [ofComonObjCoalgebraStruct_comul]
  simp only [Comon.monoidal_tensorObj_comon_comul]
  simp [tensorμ_eq_tensorTensorTensorComm, TensorProduct.comul_def,
    AlgebraTensorModule.tensorTensorTensorComm_eq]
  rfl

中文:
定理 comul_tensorObj_tensorObj_right
  证明: by
  rw [ofComonObjCoalgebraStruct_comul]
  simp only [Comon.monoidal_tensorObj_comon_comul]
  simp [tensorμ_eq_tensorTensorTensorComm, TensorProduct.comul_def,
    AlgebraTensorModule.tensorTensorTensorComm_eq]
  rfl

Depends on / 依赖: CoalgCat, CoalgCat.of, otimes
-/
theorem comul_tensorObj_tensorObj_right :
    Coalgebra.comul (R := R) (A := (CoalgCat.of R M otimes
      (CoalgCat.of R N otimes CoalgCat.of R P) : CoalgCat R))
      = Coalgebra.comul (A := M otimes[R] (N otimes[R] P)) := by
  rw [ofComonObjCoalgebraStruct_comul]
  simp only [Comon.monoidal_tensorObj_comon_comul]
  simp [tensorμ_eq_tensorTensorTensorComm, TensorProduct.comul_def,
    AlgebraTensorModule.tensorTensorTensorComm_eq]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
attribute [local simp] MonObj.tensorObj.one_def MonObj.tensorObj.mul_def in
/--
theorem `comul_tensorObj_tensorObj_left` / 定理 `comul_tensorObj_tensorObj_left`

English:
theorem comul_tensorObj_tensorObj_left
  proof: by
  rw [ofComonObjCoalgebraStruct_comul]
  simp [tensorμ_eq_tensorTensorTensorComm, TensorProduct.comul_def,
    AlgebraTensorModule.tensorTensorTensorComm_eq]
  rfl

中文:
定理 comul_tensorObj_tensorObj_left
  证明: by
  rw [ofComonObjCoalgebraStruct_comul]
  simp [tensorμ_eq_tensorTensorTensorComm, TensorProduct.comul_def,
    AlgebraTensorModule.tensorTensorTensorComm_eq]
  rfl
-/
theorem comul_tensorObj_tensorObj_left :
    Coalgebra.comul (R := R)
      (A := ((CoalgCat.of R M otimes CoalgCat.of R N) otimes CoalgCat.of R P : CoalgCat R))
      = Coalgebra.comul (A := M otimes[R] N otimes[R] P) := by
  rw [ofComonObjCoalgebraStruct_comul]
  simp [tensorμ_eq_tensorTensorTensorComm, TensorProduct.comul_def,
    AlgebraTensorModule.tensorTensorTensorComm_eq]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `counit_tensorObj` / 定理 `counit_tensorObj`

English:
theorem counit_tensorObj
  proof: by
  rw [ofComonObjCoalgebraStruct_counit]
  simp [TensorProduct.counit_def, TensorProduct.AlgebraTensorModule.rid_eq_rid, ← lid_eq_rid]
  rfl

中文:
定理 counit_tensorObj
  证明: by
  rw [ofComonObjCoalgebraStruct_counit]
  simp [TensorProduct.counit_def, TensorProduct.AlgebraTensorModule.rid_eq_rid, ← lid_eq_rid]
  rfl

Depends on / 依赖: CoalgCat, CoalgCat.of, otimes
-/
theorem counit_tensorObj :
    Coalgebra.counit (R := R) (A := (CoalgCat.of R M otimes CoalgCat.of R N : CoalgCat R))
      = Coalgebra.counit (A := M otimes[R] N) := by
  rw [ofComonObjCoalgebraStruct_counit]
  simp [TensorProduct.counit_def, TensorProduct.AlgebraTensorModule.rid_eq_rid, ← lid_eq_rid]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `counit_tensorObj_tensorObj_right` / 定理 `counit_tensorObj_tensorObj_right`

English:
theorem counit_tensorObj_tensorObj_right
  proof: by
  rw [ofComonObjCoalgebraStruct_counit]
  simp [TensorProduct.counit_def, TensorProduct.AlgebraTensorModule.rid_eq_rid, ← lid_eq_rid]
  rfl

中文:
定理 counit_tensorObj_tensorObj_right
  证明: by
  rw [ofComonObjCoalgebraStruct_counit]
  simp [TensorProduct.counit_def, TensorProduct.AlgebraTensorModule.rid_eq_rid, ← lid_eq_rid]
  rfl
-/
theorem counit_tensorObj_tensorObj_right :
    Coalgebra.counit (R := R)
      (A := (CoalgCat.of R M otimes (CoalgCat.of R N otimes CoalgCat.of R P) : CoalgCat R))
      = Coalgebra.counit (A := M otimes[R] (N otimes[R] P)) := by
  rw [ofComonObjCoalgebraStruct_counit]
  simp [TensorProduct.counit_def, TensorProduct.AlgebraTensorModule.rid_eq_rid, ← lid_eq_rid]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `counit_tensorObj_tensorObj_left` / 定理 `counit_tensorObj_tensorObj_left`

English:
theorem counit_tensorObj_tensorObj_left
  proof: by
  rw [ofComonObjCoalgebraStruct_counit]
  simp [TensorProduct.counit_def, TensorProduct.AlgebraTensorModule.rid_eq_rid, ← lid_eq_rid]
  rfl

中文:
定理 counit_tensorObj_tensorObj_left
  证明: by
  rw [ofComonObjCoalgebraStruct_counit]
  simp [TensorProduct.counit_def, TensorProduct.AlgebraTensorModule.rid_eq_rid, ← lid_eq_rid]
  rfl

Depends on / 依赖: Finsupp, Finsupp.equivFunOnFinite_symm_sum, equivFunOnFinite_symm_sum
-/
theorem counit_tensorObj_tensorObj_left :
    Coalgebra.counit (R := R)
      (A := ((CoalgCat.of R M otimes CoalgCat.of R N) otimes CoalgCat.of R P : CoalgCat R))
      = Coalgebra.counit (A := (M otimes[R] N) otimes[R] P) := by
  rw [ofComonObjCoalgebraStruct_counit]
  simp [TensorProduct.counit_def, TensorProduct.AlgebraTensorModule.rid_eq_rid, ← lid_eq_rid]
  rfl

end CoalgCat.MonoidalCategoryAux
