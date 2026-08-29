/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johan Commelin
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!
The functor of forming finitely supported functions on a type with values in a `[Ring R]`
is the left adjoint of
the forgetful functor from `R`-modules to types.
-/

@[expose] public noncomputable section

assert_not_exists Cardinal

open CategoryTheory
open scoped MonoidAlgebra

namespace ModuleCat

universe u

variable (R : Type u)

section

variable [Ring R]

/--
Definition of `free` / `free` 的定义

English:
definition free
  signature: : Type u ⥤ ModuleCat R where
  body: ModuleCat.of R (X ->₀ R)
map {_ _} f := ofHom Finsupp.lmapDomain _ _ (f : _ -> _)

中文:
定义 free
  签名: : 类型u ⥤ 模范畴 R where
  定义体: ModuleCat.of R (X ->₀ R)
map {_ _} f := ofHom Finsupp.lmapDomain _ _ (f : _ -> _)

Depends on / 依赖: ModuleCat, ModuleCat.of
-/
def free : Type u ⥤ ModuleCat R where
  obj X := ModuleCat.of R (X ->₀ R)
map {_ _} f := ofHom Finsupp.lmapDomain _ _ (f : _ -> _)

/-- The free functor `Type u ⥤ ModuleCat R` sending a type `X` to the
free `R`-module with generators `x : X`, implemented as the monoid algebra `R[X]`.
-/
@[simps]
/--
Definition of `monoidAlgebraFree` / `monoidAlgebraFree` 的定义

English:
definition monoidAlgebraFree
  signature: : Type u ⥤ ModuleCat.{u} R where
  body: .of R R[X]
  map f := ofHom (MonoidAlgebra.mapDomainLinearMap R R f)

中文:
定义 monoidAlgebraFree
  签名: : 类型u ⥤ 模范畴.{u} R where
  定义体: .of R R[X]
  map f := ofHom (MonoidAlgebra.mapDomainLinearMap R R f)
-/
def monoidAlgebraFree : Type u ⥤ ModuleCat.{u} R where
  obj X := .of R R[X]
  map f := ofHom (MonoidAlgebra.mapDomainLinearMap R R f)

variable {R}

/--
Definition of `freeMk` / `freeMk` 的定义

English:
definition freeMk
  signature: {X : Type u} (x : X)
  body: Finsupp.single x 1

@[ext 1200]

中文:
定义 freeMk
  签名: {X : 类型u} (x : X)
  定义体: Finsupp.single x 1

@[ext 1200]

Depends on / 依赖: AlgCat, Finsupp, Finsupp.single, Functor, Functor.isRightAdjoint_comp_iff_right, ModuleCat, ModuleCat.restrictScalarsEquivalenceOfRingEquiv, Shrink, Shrink.ringEquiv, e.inverse, infer_instance, inverse, isRightAdjoint, isRightAdjoint_comp_iff_right, restrictScalarsEquivalenceOfRingEquiv, ringEquiv, single, tensorAlgebraAdj
-/
noncomputable def freeMk {X : Type u} (x : X) : (free R).obj X := Finsupp.single x 1

@[ext 1200]
/--
lemma `free_hom_ext` / 引理 `free_hom_ext`

English:
lemma free_hom_ext
  statement: {X : Type u} {M : ModuleCat.{u} R} {f g : (free R).obj X ⟶ M}
  proof: ModuleCat.hom_ext (Finsupp.lhom_ext' (fun x => LinearMap.ext_ring (h x)))

中文:
引理 free_hom_ext
  结论: {X : 类型u} {M : 模范畴.{u} R} {f g : (free R).obj X ⟶ M}
  证明: ModuleCat.hom_ext (Finsupp.lhom_ext' (fun x => LinearMap.ext_ring (h x)))

Depends on / 依赖: Finsupp, Finsupp.lhom_ext, LinearMap, LinearMap.ext_ring, ModuleCat, ModuleCat.hom_ext, ext_ring, hom_ext, lhom_ext
-/
lemma free_hom_ext {X : Type u} {M : ModuleCat.{u} R} {f g : (free R).obj X ⟶ M}
    (h : forall (x : X), f (freeMk x) = g (freeMk x)) :
    f = g :=
  ModuleCat.hom_ext (Finsupp.lhom_ext' (fun x => LinearMap.ext_ring (h x)))

/--
Definition of `freeDesc` / `freeDesc` 的定义

English:
definition freeDesc
  signature: {X : Type u} {M : ModuleCat.{u} R} (f : X ⟶ M)
  body: ofHom Finsupp.lift M R X f

@[simp]

中文:
定义 freeDesc
  签名: {X : 类型u} {M : 模范畴.{u} R} (f : X ⟶ M)
  定义体: ofHom Finsupp.lift M R X f

@[simp]

Depends on / 依赖: Finsupp, Finsupp.lift
-/
noncomputable def freeDesc {X : Type u} {M : ModuleCat.{u} R} (f : X ⟶ M) :
    (free R).obj X ⟶ M :=
ofHom Finsupp.lift M R X f

@[simp]
/--
lemma `freeDesc_apply` / 引理 `freeDesc_apply`

English:
lemma freeDesc_apply
  given: {X : Type u} {M : ModuleCat.{u} R} (f : X ⟶ M) (x : X)
  proof: by
  dsimp [freeDesc]
  erw [Finsupp.lift_apply, Finsupp.sum_single_index]
  all_goals simp

@[simp]

中文:
引理 freeDesc_apply
  条件: {X : 类型u} {M : 模范畴.{u} R} (f : X ⟶ M) (x : X)
  证明: by
  dsimp [freeDesc]
  erw [Finsupp.lift_apply, Finsupp.sum_single_index]
  all_goals simp

@[simp]

Depends on / 依赖: Finsupp, Finsupp.lift_apply, Finsupp.sum_single_index, all_goals, freeDesc, lift_apply, sum_single_index
-/
lemma freeDesc_apply {X : Type u} {M : ModuleCat.{u} R} (f : X ⟶ M) (x : X) :
    freeDesc f (freeMk x) = f x := by
  dsimp [freeDesc]
  erw [Finsupp.lift_apply, Finsupp.sum_single_index]
  all_goals simp

@[simp]
/--
lemma `free_map_apply` / 引理 `free_map_apply`

English:
lemma free_map_apply
  given: {X Y : Type u} (f : X ⟶ Y) (x : X)
  proof: by
  apply Finsupp.mapDomain_single

中文:
引理 free_map_apply
  条件: {X Y : 类型u} (f : X ⟶ Y) (x : X)
  证明: by
  apply Finsupp.mapDomain_single

Depends on / 依赖: Finsupp, Finsupp.mapDomain_single, mapDomain_single
-/
lemma free_map_apply {X Y : Type u} (f : X ⟶ Y) (x : X) :
    (free R).map f (freeMk x) = freeMk (f x) := by
  apply Finsupp.mapDomain_single

/-- The bijection `((free R).obj X ⟶ M) ≃ (X → M)` when `X` is a type and `M` a module. -/
@[simps]
/--
Definition of `freeHomEquiv` / `freeHomEquiv` 的定义

English:
definition freeHomEquiv
  signature: {X : Type u} {M : ModuleCat.{u} R}
  body: ↾fun x => φ (freeMk x)
  invFun ψ := freeDesc (↾ψ)
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

中文:
定义 freeHomEquiv
  签名: {X : 类型u} {M : 模范畴.{u} R}
  定义体: ↾fun x => φ (freeMk x)
  invFun ψ := freeDesc (↾ψ)
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

Depends on / 依赖: freeMk
-/
def freeHomEquiv {X : Type u} {M : ModuleCat.{u} R} :
    ((free R).obj X ⟶ M) ≃ (X ⟶ M) where
  toFun φ := ↾fun x => φ (freeMk x)
  invFun ψ := freeDesc (↾ψ)
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

variable (R)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `adj` / `adj` 的定义

English:
definition adj
  signature: : free R ⊣ forget (ModuleCat.{u} R)
  body: Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ => freeHomEquiv
      homEquiv_naturality_left_symm := fun {X Y M} f g => by ext; simp [freeHomEquiv] }

@[simp]

中文:
定义 adj
  签名: : free R ⊣ forget (模范畴.{u} R)
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ => freeHomEquiv
      homEquiv_naturality_left_symm := fun {X Y M} f g => by ext; simp [freeHomEquiv] }

@[simp]

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, freeHomEquiv, homEquiv, homEquiv_naturality_left_symm, mkOfHomEquiv
-/
def adj : free R ⊣ forget (ModuleCat.{u} R) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ => freeHomEquiv
      homEquiv_naturality_left_symm := fun {X Y M} f g => by ext; simp [freeHomEquiv] }

@[simp]
/--
lemma `adj_homEquiv` / 引理 `adj_homEquiv`

English:
lemma adj_homEquiv
  given: (X : Type u) (M : ModuleCat.{u} R)
  proof: by
  simp only [adj, Adjunction.mkOfHomEquiv_homEquiv]

中文:
引理 adj_homEquiv
  条件: (X : 类型u) (M : 模范畴.{u} R)
  证明: by
  simp only [adj, Adjunction.mkOfHomEquiv_homEquiv]

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv_homEquiv, mkOfHomEquiv_homEquiv
-/
lemma adj_homEquiv (X : Type u) (M : ModuleCat.{u} R) :
    (adj R).homEquiv X M = freeHomEquiv := by
  simp only [adj, Adjunction.mkOfHomEquiv_homEquiv]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget (ModuleCat.{u} R)).IsRightAdjoint
  body: (adj R).isRightAdjoint

中文:
实例 :
  签名: (forget (模范畴.{u} R)).是右伴随
  定义体: (adj R).isRightAdjoint

Depends on / 依赖: isRightAdjoint
-/
instance : (forget (ModuleCat.{u} R)).IsRightAdjoint :=
  (adj R).isRightAdjoint

end

section Free

open MonoidalCategory

variable [CommRing R]

namespace FreeMonoidal

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `εIso` / `εIso` 的定义

English:
definition εIso
  signature: : 𝟙_ (ModuleCat R) ≅ (free R).obj (𝟙_ (Type u)) where
  body: ofHom Finsupp.lsingle PUnit.unit
inv := ofHom Finsupp.lapply PUnit.unit
  hom_inv_id := by
    ext
    simp [free]
  inv_hom_id := by
    ext ⟨⟩
    dsimp [freeMk]
    erw [Finsupp.lapply_apply, Finsupp.lsingle_apply]
    rw [Finsupp.single_eq_same]

中文:
定义 εIso
  签名: : 𝟙_ (模范畴 R) ≅ (free R).obj (𝟙_ (类型u)) where
  定义体: ofHom Finsupp.lsingle PUnit.unit
inv := ofHom Finsupp.lapply PUnit.unit
  hom_inv_id := by
    ext
    simp [free]
  inv_hom_id := by
    ext ⟨⟩
    dsimp [freeMk]
    erw [Finsupp.lapply_apply, Finsupp.lsingle_apply]
    rw [Finsupp.single_eq_same]

Depends on / 依赖: Finsupp, Finsupp.lsingle, PUnit.unit, lsingle
-/
def εIso : 𝟙_ (ModuleCat R) ≅ (free R).obj (𝟙_ (Type u)) where
hom := ofHom Finsupp.lsingle PUnit.unit
inv := ofHom Finsupp.lapply PUnit.unit
  hom_inv_id := by
    ext
    simp [free]
  inv_hom_id := by
    ext ⟨⟩
    dsimp [freeMk]
    erw [Finsupp.lapply_apply, Finsupp.lsingle_apply]
    rw [Finsupp.single_eq_same]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `εIso_hom_one` / 引理 `εIso_hom_one`

English:
lemma εIso_hom_one
  statement: (εIso R).hom 1 = freeMk PUnit.unit
  proof: rfl

中文:
引理 εIso_hom_one
  结论: (εIso R).hom 1 = freeMk 命题单元.unit
  证明: rfl
-/
lemma εIso_hom_one : (εIso R).hom 1 = freeMk PUnit.unit := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `εIso_inv_freeMk` / 引理 `εIso_inv_freeMk`

English:
lemma εIso_inv_freeMk
  given: (x : PUnit)
  statement: (εIso R).inv (freeMk x) = 1
  proof: by
  dsimp [εIso, freeMk]
  erw [Finsupp.lapply_apply]
  rw [Finsupp.single_eq_same]

中文:
引理 εIso_inv_freeMk
  条件: (x : 命题单元)
  结论: (εIso R).inv (freeMk x) = 1
  证明: by
  dsimp [εIso, freeMk]
  erw [Finsupp.lapply_apply]
  rw [Finsupp.single_eq_same]

Depends on / 依赖: Finsupp, Finsupp.lapply_apply, Finsupp.single_eq_same, freeMk, lapply_apply, single_eq_same
-/
lemma εIso_inv_freeMk (x : PUnit) : (εIso R).inv (freeMk x) = 1 := by
  dsimp [εIso, freeMk]
  erw [Finsupp.lapply_apply]
  rw [Finsupp.single_eq_same]

/--
Definition of `μIso` / `μIso` 的定义

English:
definition μIso
  signature: (X Y : Type u)
  body: (finsuppTensorFinsupp' R _ _).toModuleIso

@[simp]

中文:
定义 μIso
  签名: (X Y : 类型u)
  定义体: (finsuppTensorFinsupp' R _ _).toModuleIso

@[simp]

Depends on / 依赖: finsuppTensorFinsupp, toModuleIso
-/
def μIso (X Y : Type u) :
    (free R).obj X otimes (free R).obj Y ≅ (free R).obj (X otimes Y) :=
  (finsuppTensorFinsupp' R _ _).toModuleIso

@[simp]
/--
lemma `μIso_hom_freeMk_tmul_freeMk` / 引理 `μIso_hom_freeMk_tmul_freeMk`

English:
lemma μIso_hom_freeMk_tmul_freeMk
  given: {X Y : Type u} (x : X) (y : Y)
  proof: by
  dsimp [μIso, freeMk]
  erw [finsuppTensorFinsupp'_single_tmul_single]
  rw [mul_one]

中文:
引理 μIso_hom_freeMk_tmul_freeMk
  条件: {X Y : 类型u} (x : X) (y : Y)
  证明: by
  dsimp [μIso, freeMk]
  erw [finsuppTensorFinsupp'_single_tmul_single]
  rw [mul_one]

Depends on / 依赖: _single_tmul_single, finsuppTensorFinsupp, freeMk, mul_one
-/
lemma μIso_hom_freeMk_tmul_freeMk {X Y : Type u} (x : X) (y : Y) :
    (μIso R X Y).hom (freeMk x otimesₜ freeMk y) = freeMk (x, y) := by
  dsimp [μIso, freeMk]
  erw [finsuppTensorFinsupp'_single_tmul_single]
  rw [mul_one]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `μIso_inv_freeMk` / 引理 `μIso_inv_freeMk`

English:
lemma μIso_inv_freeMk
  given: {X Y : Type u} (z : X otimes Y)
  proof: by
  dsimp [μIso, freeMk]
  erw [finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]

中文:
引理 μIso_inv_freeMk
  条件: {X Y : 类型u} (z : X otimes Y)
  证明: by
  dsimp [μIso, freeMk]
  erw [finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]

Depends on / 依赖: _symm_single_eq_single_one_tmul, finsuppTensorFinsupp, freeMk
-/
lemma μIso_inv_freeMk {X Y : Type u} (z : X otimes Y) :
    (μIso R X Y).inv (freeMk z) = freeMk z.1 otimesₜ freeMk z.2 := by
  dsimp [μIso, freeMk]
  erw [finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]

end FreeMonoidal
set_option backward.isDefEq.respectTransparency.types false in
open FreeMonoidal in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (free R).Monoidal
  body: Functor.CoreMonoidal.toMonoidal
    { εIso := εIso R
      μIso := μIso R
      μIso_hom_natural_left := fun {X Y} f X' => by
        rw [← cancel_epi (μIso R X X').inv]
        aesop
      μIso_hom_natural_right := fun {X Y} X' f => by
        rw [← cancel_epi (μIso R X' X).inv]
        aesop
      associativity := fun X Y Z => by
        rw [← cancel_epi ((μIso R X Y).inv ▷ _)]; rw [← cancel_epi (μIso R _ _).inv]
        ext ⟨⟨x, y⟩, z⟩
        dsimp
        rw [μIso_inv_freeMk]; rw [MonoidalCategory.whiskerRight_apply]; rw [μIso_inv_freeMk]; rw [MonoidalCategory.whiskerRight_apply]; rw [μIso_hom_freeMk_tmul_freeMk]; rw [μIso_hom_freeMk_tmul_freeMk]; rw [free_map_apply]; rw [CategoryTheory.associator_hom_apply]; rw [MonoidalCategory.associator_hom_apply]; rw [MonoidalCategory.whiskerLeft_apply]; rw [μIso_hom_freeMk_tmul_freeMk]; rw [μIso_hom_freeMk_tmul_freeMk]
      left_unitality := fun X => by
        rw [← cancel_epi (fun_ _).inv]; rw [Iso.inv_hom_id]
        aesop
      right_unitality := fun X => by
        rw [← cancel_epi (ρ_ _).inv]; rw [Iso.inv_hom_id]
        aesop }

中文:
实例 :
  签名: (free R).幺半群
  定义体: Functor.CoreMonoidal.toMonoidal
    { εIso := εIso R
      μIso := μIso R
      μIso_hom_natural_left := fun {X Y} f X' => by
        rw [← cancel_epi (μIso R X X').inv]
        aesop
      μIso_hom_natural_right := fun {X Y} X' f => by
        rw [← cancel_epi (μIso R X' X).inv]
        aesop
      associativity := fun X Y Z => by
        rw [← cancel_epi ((μIso R X Y).inv ▷ _)]; rw [← cancel_epi (μIso R _ _).inv]
        ext ⟨⟨x, y⟩, z⟩
        dsimp
        rw [μIso_inv_freeMk]; rw [MonoidalCategory.whiskerRight_apply]; rw [μIso_inv_freeMk]; rw [MonoidalCategory.whiskerRight_apply]; rw [μIso_hom_freeMk_tmul_freeMk]; rw [μIso_hom_freeMk_tmul_freeMk]; rw [free_map_apply]; rw [CategoryTheory.associator_hom_apply]; rw [MonoidalCategory.associator_hom_apply]; rw [MonoidalCategory.whiskerLeft_apply]; rw [μIso_hom_freeMk_tmul_freeMk]; rw [μIso_hom_freeMk_tmul_freeMk]
      left_unitality := fun X => by
        rw [← cancel_epi (fun_ _).inv]; rw [Iso.inv_hom_id]
        aesop
      right_unitality := fun X => by
        rw [← cancel_epi (ρ_ _).inv]; rw [Iso.inv_hom_id]
        aesop }

Depends on / 依赖: CoreMonoidal, Functor, Functor.CoreMonoidal.toMonoidal, MonoidalCategory, MonoidalCategory.whiskerRight_apply, associativity, cancel_epi, toMonoidal, whiskerRight_apply
-/
instance : (free R).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := εIso R
      μIso := μIso R
      μIso_hom_natural_left := fun {X Y} f X' => by
        rw [← cancel_epi (μIso R X X').inv]
        aesop
      μIso_hom_natural_right := fun {X Y} X' f => by
        rw [← cancel_epi (μIso R X' X).inv]
        aesop
      associativity := fun X Y Z => by
        rw [← cancel_epi ((μIso R X Y).inv ▷ _)]; rw [← cancel_epi (μIso R _ _).inv]
        ext ⟨⟨x, y⟩, z⟩
        dsimp
        rw [μIso_inv_freeMk]; rw [MonoidalCategory.whiskerRight_apply]; rw [μIso_inv_freeMk]; rw [MonoidalCategory.whiskerRight_apply]; rw [μIso_hom_freeMk_tmul_freeMk]; rw [μIso_hom_freeMk_tmul_freeMk]; rw [free_map_apply]; rw [CategoryTheory.associator_hom_apply]; rw [MonoidalCategory.associator_hom_apply]; rw [MonoidalCategory.whiskerLeft_apply]; rw [μIso_hom_freeMk_tmul_freeMk]; rw [μIso_hom_freeMk_tmul_freeMk]
      left_unitality := fun X => by
        rw [← cancel_epi (fun_ _).inv]; rw [Iso.inv_hom_id]
        aesop
      right_unitality := fun X => by
        rw [← cancel_epi (ρ_ _).inv]; rw [Iso.inv_hom_id]
        aesop }

open Functor.LaxMonoidal Functor.OplaxMonoidal

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `free_ε_one` / 引理 `free_ε_one`

English:
lemma free_ε_one
  statement: ε (free R) 1 = freeMk PUnit.unit
  proof: rfl

中文:
引理 free_ε_one
  结论: ε (free R) 1 = freeMk 命题单元.unit
  证明: rfl
-/
lemma free_ε_one : ε (free R) 1 = freeMk PUnit.unit := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `free_η_freeMk` / 引理 `free_η_freeMk`

English:
lemma free_η_freeMk
  given: (x : PUnit)
  statement: η (free R) (freeMk x) = 1
  proof: by
  apply FreeMonoidal.εIso_inv_freeMk

@[simp]

中文:
引理 free_η_freeMk
  条件: (x : 命题单元)
  结论: η (free R) (freeMk x) = 1
  证明: by
  apply FreeMonoidal.εIso_inv_freeMk

@[simp]

Depends on / 依赖: FreeMonoidal
-/
lemma free_η_freeMk (x : PUnit) : η (free R) (freeMk x) = 1 := by
  apply FreeMonoidal.εIso_inv_freeMk

@[simp]
/--
lemma `free_μ_freeMk_tmul_freeMk` / 引理 `free_μ_freeMk_tmul_freeMk`

English:
lemma free_μ_freeMk_tmul_freeMk
  given: {X Y : Type u} (x : X) (y : Y)
  proof: by
  apply FreeMonoidal.μIso_hom_freeMk_tmul_freeMk

@[simp]

中文:
引理 free_μ_freeMk_tmul_freeMk
  条件: {X Y : 类型u} (x : X) (y : Y)
  证明: by
  apply FreeMonoidal.μIso_hom_freeMk_tmul_freeMk

@[simp]

Depends on / 依赖: FreeMonoidal
-/
lemma free_μ_freeMk_tmul_freeMk {X Y : Type u} (x : X) (y : Y) :
    μ (free R) _ _ (freeMk x otimesₜ freeMk y) = freeMk (x, y) := by
  apply FreeMonoidal.μIso_hom_freeMk_tmul_freeMk

@[simp]
/--
lemma `free_δ_freeMk` / 引理 `free_δ_freeMk`

English:
lemma free_δ_freeMk
  given: {X Y : Type u} (z : X otimes Y)
  proof: by
  apply FreeMonoidal.μIso_inv_freeMk

中文:
引理 free_δ_freeMk
  条件: {X Y : 类型u} (z : X otimes Y)
  证明: by
  apply FreeMonoidal.μIso_inv_freeMk

Depends on / 依赖: FreeMonoidal
-/
lemma free_δ_freeMk {X Y : Type u} (z : X otimes Y) :
    δ (free R) _ _ (freeMk z) = freeMk z.1 otimesₜ freeMk z.2 := by
  apply FreeMonoidal.μIso_inv_freeMk

end Free

end ModuleCat

namespace CategoryTheory

universe v u

/-- `Free R C` is a type synonym for `C`, which, given `[CommRing R]` and `[Category* C]`,
we will equip with a category structure where the morphisms are formal `R`-linear combinations
of the morphisms in `C`.
-/
@[nolint unusedArguments]
/--
Definition of `Free` / `Free` 的定义

English:
definition Free
  signature: (_ : Type*) (C : Type u)
  body: C

中文:
定义 自由
  签名: (_ : 类型) (C : 类型u)
  定义体: C
-/
def Free (_ : Type*) (C : Type u) :=
  C

/--
Definition of `Free.of` / `Free.of` 的定义

English:
definition Free.of
  signature: (R : Type*) {C : Type u} (X : C)
  body: X

中文:
定义 自由.of
  签名: (R : 类型) {C : 类型u} (X : C)
  定义体: X
-/
def Free.of (R : Type*) {C : Type u} (X : C) : Free R C :=
  X

variable (R : Type*) [CommRing R] (C : Type u) [Category.{v} C]

open Finsupp

-- Conceptually, it would be nice to construct this via "transport of enrichment",
-- using the fact that `ModuleCat.Free R : Type ⥤ ModuleCat R` and `ModuleCat.forget` are both lax
-- monoidal. This still seems difficult, so we just do it by hand.
set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `categoryFree` / 实例 `categoryFree`

English:
instance categoryFree
  signature: : Category (Free R C) where
  body: fun X Y : C => (X ⟶ Y) ->₀ R
  id := fun X : C => Finsupp.single (𝟙 X) 1
  comp {X _ Z : C} f g :=
    (f.sum (fun f' s => g.sum (fun g' t => Finsupp.single (f' ≫ g') (s * t))) : (X ⟶ Z) ->₀ R)
  assoc {W X Y Z} f g h := by
    -- This imitates the proof of associativity for `MonoidAlgebra`.
    simp [sum_sum_index, add_mul, mul_add, Category.assoc, mul_assoc]

中文:
实例 categoryFree
  签名: : 范畴 (自由 R C) where
  定义体: fun X Y : C => (X ⟶ Y) ->₀ R
  id := fun X : C => Finsupp.single (𝟙 X) 1
  comp {X _ Z : C} f g :=
    (f.sum (fun f' s => g.sum (fun g' t => Finsupp.single (f' ≫ g') (s * t))) : (X ⟶ Z) ->₀ R)
  assoc {W X Y Z} f g h := by
    -- This imitates the proof of associativity for `MonoidAlgebra`.
    simp [sum_sum_index, add_mul, mul_add, Category.assoc, mul_assoc]
-/
instance categoryFree : Category (Free R C) where
  Hom := fun X Y : C => (X ⟶ Y) ->₀ R
  id := fun X : C => Finsupp.single (𝟙 X) 1
  comp {X _ Z : C} f g :=
    (f.sum (fun f' s => g.sum (fun g' t => Finsupp.single (f' ≫ g') (s * t))) : (X ⟶ Z) ->₀ R)
  assoc {W X Y Z} f g h := by
    -- This imitates the proof of associativity for `MonoidAlgebra`.
    simp [sum_sum_index, add_mul, mul_add, Category.assoc, mul_assoc]

namespace Free

section

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preadditive (Free R C)
  body: Finsupp.instAddCommGroup
  add_comp X Y Z f f' g := by
    dsimp +instances [CategoryTheory.categoryFree]
    rw [Finsupp.sum_add_index'] <;> · simp [add_mul]
  comp_add X Y Z f g g' := by
    dsimp +instances [CategoryTheory.categoryFree]
    rw [← Finsupp.sum_add]
    congr; ext r h
    rw [Finsupp.sum_add_index'] <;> · simp [mul_add]

中文:
实例 :
  签名: 预加性 (自由 R C)
  定义体: Finsupp.instAddCommGroup
  add_comp X Y Z f f' g := by
    dsimp +instances [CategoryTheory.categoryFree]
    rw [Finsupp.sum_add_index'] <;> · simp [add_mul]
  comp_add X Y Z f g g' := by
    dsimp +instances [CategoryTheory.categoryFree]
    rw [← Finsupp.sum_add]
    congr; ext r h
    rw [Finsupp.sum_add_index'] <;> · simp [mul_add]

Depends on / 依赖: Finsupp, Finsupp.instAddCommGroup, instAddCommGroup
-/
instance : Preadditive (Free R C) where
  homGroup _ _ := Finsupp.instAddCommGroup
  add_comp X Y Z f f' g := by
    dsimp +instances [CategoryTheory.categoryFree]
    rw [Finsupp.sum_add_index'] <;> · simp [add_mul]
  comp_add X Y Z f g g' := by
    dsimp +instances [CategoryTheory.categoryFree]
    rw [← Finsupp.sum_add]
    congr; ext r h
    rw [Finsupp.sum_add_index'] <;> · simp [mul_add]

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Linear R (Free R C)
  body: Finsupp.module _ R
  smul_comp X Y Z r f g := by
    dsimp +instances [CategoryTheory.categoryFree]
    rw [Finsupp.sum_smul_index] <;> simp [Finsupp.smul_sum, mul_assoc]
  comp_smul X Y Z f r g := by
    dsimp +instances [CategoryTheory.categoryFree]
    simp_rw [Finsupp.smul_sum]
    congr; ext h s
    rw [Finsupp.sum_smul_index] <;> simp [mul_left_comm]

中文:
实例 :
  签名: 线性 R (自由 R C)
  定义体: Finsupp.module _ R
  smul_comp X Y Z r f g := by
    dsimp +instances [CategoryTheory.categoryFree]
    rw [Finsupp.sum_smul_index] <;> simp [Finsupp.smul_sum, mul_assoc]
  comp_smul X Y Z f r g := by
    dsimp +instances [CategoryTheory.categoryFree]
    simp_rw [Finsupp.smul_sum]
    congr; ext h s
    rw [Finsupp.sum_smul_index] <;> simp [mul_left_comm]

Depends on / 依赖: Finsupp, Finsupp.module, module
-/
instance : Linear R (Free R C) where
  homModule _ _ := Finsupp.module _ R
  smul_comp X Y Z r f g := by
    dsimp +instances [CategoryTheory.categoryFree]
    rw [Finsupp.sum_smul_index] <;> simp [Finsupp.smul_sum, mul_assoc]
  comp_smul X Y Z f r g := by
    dsimp +instances [CategoryTheory.categoryFree]
    simp_rw [Finsupp.smul_sum]
    congr; ext h s
    rw [Finsupp.sum_smul_index] <;> simp [mul_left_comm]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `single_comp_single` / 定理 `single_comp_single`

English:
theorem single_comp_single
  given: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (r s : R)
  proof: by
  dsimp +instances [CategoryTheory.categoryFree]
  simp

中文:
定理 single_comp_single
  条件: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (r s : R)
  证明: by
  dsimp +instances [CategoryTheory.categoryFree]
  simp

Depends on / 依赖: CategoryTheory, CategoryTheory.categoryFree, categoryFree, instances
-/
theorem single_comp_single {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (r s : R) :
    (single f r ≫ single g s : Free.of R X ⟶ Free.of R Z) = single (f ≫ g) (r * s) := by
  dsimp +instances [CategoryTheory.categoryFree]
  simp

end

attribute [local simp] single_comp_single

set_option backward.isDefEq.respectTransparency false in
/-- A category embeds into its `R`-linear completion.
-/
@[simps]
/--
Definition of `embedding` / `embedding` 的定义

English:
definition embedding
  signature: : C ⥤ Free R C where
  body: X
  map {_ _} f := Finsupp.single f 1
  map_id _ := rfl
  map_comp {X Y Z} f g := by
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10959): simp used to be able to close this goal
    rw [single_comp_single]; rw [one_mul]

中文:
定义 embedding
  签名: : C ⥤ 自由 R C where
  定义体: X
  map {_ _} f := Finsupp.single f 1
  map_id _ := rfl
  map_comp {X Y Z} f g := by
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10959): simp used to be able to close this goal
    rw [single_comp_single]; rw [one_mul]
-/
def embedding : C ⥤ Free R C where
  obj X := X
  map {_ _} f := Finsupp.single f 1
  map_id _ := rfl
  map_comp {X Y Z} f g := by
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10959): simp used to be able to close this goal
    rw [single_comp_single]; rw [one_mul]

variable {C} {D : Type u} [Category.{v} D] [Preadditive D] [Linear R D]

open Preadditive Linear

set_option backward.isDefEq.respectTransparency false in
/-- A functor to an `R`-linear category lifts to a functor from its `R`-linear completion.
-/
@[simps]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (F : C ⥤ D)
  body: F.obj X
  map {_ _} f := f.sum fun f' r => r • F.map f'
  map_id := by
    dsimp +instances [CategoryTheory.categoryFree]
    simp
  map_comp {X Y Z} f g := by
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f₁ f₂ w₁ w₂ =>
      rw [add_comp]
      rw [Finsupp.sum_add_index']; rw [Finsupp.sum_add_index']
      · simp only [w₁, w₂, add_comp]
      · intros; rw [zero_smul]
      · intros; simp only [add_smul]
      · intros; rw [zero_smul]
      · intros; simp only [add_smul]
    | single f' r =>
      induction g using Finsupp.induction_linear with
      | zero => simp
      | add f₁ f₂ w₁ w₂ =>
        rw [comp_add]
        rw [Finsupp.sum_add_index']; rw [Finsupp.sum_add_index']
        · simp only [w₁, w₂, comp_add]
        · intros; rw [zero_smul]
        · intros; simp only [add_smul]
        · intros; rw [zero_smul]
        · intros; simp only [add_smul]
      | single g' s =>
        rw [single_comp_single _ _ f' g' r s]
        simp [mul_comm r s, mul_smul]

中文:
定义 lift
  签名: (F : C ⥤ D)
  定义体: F.obj X
  map {_ _} f := f.sum fun f' r => r • F.map f'
  map_id := by
    dsimp +instances [CategoryTheory.categoryFree]
    simp
  map_comp {X Y Z} f g := by
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f₁ f₂ w₁ w₂ =>
      rw [add_comp]
      rw [Finsupp.sum_add_index']; rw [Finsupp.sum_add_index']
      · simp only [w₁, w₂, add_comp]
      · intros; rw [zero_smul]
      · intros; simp only [add_smul]
      · intros; rw [zero_smul]
      · intros; simp only [add_smul]
    | single f' r =>
      induction g using Finsupp.induction_linear with
      | zero => simp
      | add f₁ f₂ w₁ w₂ =>
        rw [comp_add]
        rw [Finsupp.sum_add_index']; rw [Finsupp.sum_add_index']
        · simp only [w₁, w₂, comp_add]
        · intros; rw [zero_smul]
        · intros; simp only [add_smul]
        · intros; rw [zero_smul]
        · intros; simp only [add_smul]
      | single g' s =>
        rw [single_comp_single _ _ f' g' r s]
        simp [mul_comm r s, mul_smul]

Depends on / 依赖: F.obj
-/
def lift (F : C ⥤ D) : Free R C ⥤ D where
  obj X := F.obj X
  map {_ _} f := f.sum fun f' r => r • F.map f'
  map_id := by
    dsimp +instances [CategoryTheory.categoryFree]
    simp
  map_comp {X Y Z} f g := by
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f₁ f₂ w₁ w₂ =>
      rw [add_comp]
      rw [Finsupp.sum_add_index']; rw [Finsupp.sum_add_index']
      · simp only [w₁, w₂, add_comp]
      · intros; rw [zero_smul]
      · intros; simp only [add_smul]
      · intros; rw [zero_smul]
      · intros; simp only [add_smul]
    | single f' r =>
      induction g using Finsupp.induction_linear with
      | zero => simp
      | add f₁ f₂ w₁ w₂ =>
        rw [comp_add]
        rw [Finsupp.sum_add_index']; rw [Finsupp.sum_add_index']
        · simp only [w₁, w₂, comp_add]
        · intros; rw [zero_smul]
        · intros; simp only [add_smul]
        · intros; rw [zero_smul]
        · intros; simp only [add_smul]
      | single g' s =>
        rw [single_comp_single _ _ f' g' r s]
        simp [mul_comm r s, mul_smul]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `lift_map_single` / 定理 `lift_map_single`

English:
theorem lift_map_single
  given: (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (r : R)
  proof: by simp

中文:
定理 lift_map_single
  条件: (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (r : R)
  证明: by simp
-/
theorem lift_map_single (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (r : R) :
    (lift R F).map (single f r) = r • F.map f := by simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `lift_additive` / 实例 `lift_additive`

English:
instance lift_additive
  signature: (F : C ⥤ D)
  body: by
    dsimp
    rw [Finsupp.sum_add_index'] <;> simp [add_smul]

中文:
实例 lift_additive
  签名: (F : C ⥤ D)
  定义体: by
    dsimp
    rw [Finsupp.sum_add_index'] <;> simp [add_smul]

Depends on / 依赖: Finsupp, Finsupp.sum_add_index, add_smul, sum_add_index
-/
instance lift_additive (F : C ⥤ D) : (lift R F).Additive where
  map_add {X Y} f g := by
    dsimp
    rw [Finsupp.sum_add_index'] <;> simp [add_smul]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `lift_linear` / 实例 `lift_linear`

English:
instance lift_linear
  signature: (F : C ⥤ D)
  body: by
    dsimp
    rw [Finsupp.sum_smul_index] <;> simp [Finsupp.smul_sum, mul_smul]

中文:
实例 lift_linear
  签名: (F : C ⥤ D)
  定义体: by
    dsimp
    rw [Finsupp.sum_smul_index] <;> simp [Finsupp.smul_sum, mul_smul]

Depends on / 依赖: Finsupp, Finsupp.smul_sum, Finsupp.sum_smul_index, mul_smul, smul_sum, sum_smul_index
-/
instance lift_linear (F : C ⥤ D) : (lift R F).Linear R where
  map_smul {X Y} f r := by
    dsimp
    rw [Finsupp.sum_smul_index] <;> simp [Finsupp.smul_sum, mul_smul]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `embeddingLiftIso` / `embeddingLiftIso` 的定义

English:
definition embeddingLiftIso
  signature: (F : C ⥤ D)
  body: NatIso.ofComponents fun _ => Iso.refl _

中文:
定义 embeddingLiftIso
  签名: (F : C ⥤ D)
  定义体: NatIso.ofComponents fun _ => Iso.refl _

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def embeddingLiftIso (F : C ⥤ D) : embedding R C ⋙ lift R F ≅ F :=
  NatIso.ofComponents fun _ => Iso.refl _

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `ext` / `ext` 的定义

English:
definition ext
  signature: {F G : Free R C ⥤ D} [F.Additive] [F.Linear R] [G.Additive] [G.Linear R]
  body: NatIso.ofComponents (fun X => α.app X)
    (by
      intro X Y f
      induction f using Finsupp.induction_linear with
      | zero => simp
      | add f₁ f₂ w₁ w₂ =>
        rw [Functor.map_add]; rw [add_comp]; rw [w₁]; rw [w₂]; rw [Functor.map_add]; rw [comp_add]
      | single f' r =>
        rw [Iso.app_hom]; rw [Iso.app_hom]; rw [← smul_single_one]; rw [F.map_smul]; rw [G.map_smul]; rw [smul_comp]; rw [comp_smul]
        change r • (embedding R C ⋙ F).map f' ≫ _ = r • _ ≫ (embedding R C ⋙ G).map f'
        rw [α.hom.naturality f'])

中文:
定义 ext
  签名: {F G : 自由 R C ⥤ D} [F.加性] [F.线性 R] [G.加性] [G.线性 R]
  定义体: NatIso.ofComponents (fun X => α.app X)
    (by
      intro X Y f
      induction f using Finsupp.induction_linear with
      | zero => simp
      | add f₁ f₂ w₁ w₂ =>
        rw [Functor.map_add]; rw [add_comp]; rw [w₁]; rw [w₂]; rw [Functor.map_add]; rw [comp_add]
      | single f' r =>
        rw [Iso.app_hom]; rw [Iso.app_hom]; rw [← smul_single_one]; rw [F.map_smul]; rw [G.map_smul]; rw [smul_comp]; rw [comp_smul]
        change r • (embedding R C ⋙ F).map f' ≫ _ = r • _ ≫ (embedding R C ⋙ G).map f'
        rw [α.hom.naturality f'])

Depends on / 依赖: F.map_smul, Finsupp, Finsupp.induction_linear, Functor, Functor.map_add, G.map_smul, Iso.app_hom, NatIso, NatIso.ofComponents, add_comp, app_hom, comp_add, comp_smul, embedding, hom.naturality, induction_linear, map_add, map_smul, naturality, ofComponents
-/
def ext {F G : Free R C ⥤ D} [F.Additive] [F.Linear R] [G.Additive] [G.Linear R]
    (α : embedding R C ⋙ F ≅ embedding R C ⋙ G) : F ≅ G :=
  NatIso.ofComponents (fun X => α.app X)
    (by
      intro X Y f
      induction f using Finsupp.induction_linear with
      | zero => simp
      | add f₁ f₂ w₁ w₂ =>
        rw [Functor.map_add]; rw [add_comp]; rw [w₁]; rw [w₂]; rw [Functor.map_add]; rw [comp_add]
      | single f' r =>
        rw [Iso.app_hom]; rw [Iso.app_hom]; rw [← smul_single_one]; rw [F.map_smul]; rw [G.map_smul]; rw [smul_comp]; rw [comp_smul]
        change r • (embedding R C ⋙ F).map f' ≫ _ = r • _ ≫ (embedding R C ⋙ G).map f'
        rw [α.hom.naturality f'])

/--
Definition of `liftUnique` / `liftUnique` 的定义

English:
definition liftUnique
  signature: (F : C ⥤ D) (L : Free R C ⥤ D) [L.Additive] [L.Linear R]
  body: ext R (α.trans (embeddingLiftIso R F).symm)

中文:
定义 liftUnique
  签名: (F : C ⥤ D) (L : 自由 R C ⥤ D) [L.加性] [L.线性 R]
  定义体: ext R (α.trans (embeddingLiftIso R F).symm)

Depends on / 依赖: embeddingLiftIso
-/
def liftUnique (F : C ⥤ D) (L : Free R C ⥤ D) [L.Additive] [L.Linear R]
    (α : embedding R C ⋙ L ≅ F) : L ≅ lift R F :=
  ext R (α.trans (embeddingLiftIso R F).symm)

end Free
end CategoryTheory
