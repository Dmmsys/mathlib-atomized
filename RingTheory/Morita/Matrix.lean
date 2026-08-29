/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang
-/
module

public import Mathlib.LinearAlgebra.Matrix.Module
public import Mathlib.RingTheory.Morita.Basic
/-!
# Morita Equivalence between `R` and `Mₙ(R)`

## Main definitions
- `ModuleCat.toMatrixModCat`: The functor from `Mod-R` to `Mod-Mₙ(R)` induced by
  `LinearMap.mapMatrixModule` and `Matrix.Module.matrixModule`.
- `MatrixModCat.toModuleCat`: The functor from `Mod-Mₙ(R)` to `Mod-R` induced by sending `M` to
  the image of `Eᵢᵢ • ·` where `Eᵢᵢ` is the elementary matrix.
- `ModuleCat.matrixEquivalence`: An equivalence of categories composed by
  `ModuleCat.toMatrixModCat R ι`.
  and `MatrixModCat.toModuleCat R i`.
- `moritaEquivalentToMatrix`: `moritaEquivalentToMatrix` is a `MoritaEquivalence`.

## Main results
- `IsMoritaEquivalent.matrix`: `R` and `Mₙ(R)` are Morita equivalent.

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe u v

variable (R : Type u) (ι : Type v) [Ring R] [Fintype ι] [DecidableEq ι]

open CategoryTheory Matrix.Module

/-- The functor from `Mod-R` to `Mod-Mₙ(R)` induced by `LinearMap.mapModule` and
  `Matrix.matrixModule`. -/
@[simps]
/--
Definition of `ModuleCat.toMatrixModCat` / `ModuleCat.toMatrixModCat` 的定义

English:
definition ModuleCat.toMatrixModCat
  signature: : ModuleCat R ⥤ ModuleCat (Matrix ι ι R) where
  body: ModuleCat.of (Matrix ι ι R) (ι -> M)
map f := ModuleCat.ofHom f.hom.mapMatrixModule ι
map_id _ := ModuleCat.hom_ext LinearMap.mapMatrixModule_id
  map_comp f g := ModuleCat.hom_ext (LinearMap.mapMatrixModule_comp f.hom g.hom)

中文:
定义 ModuleCat.toMatrixModCat
  签名: : ModuleCat R ⥤ ModuleCat (Matrix ι ι R) where
  定义体: ModuleCat.of (Matrix ι ι R) (ι -> M)
map f := ModuleCat.ofHom f.hom.mapMatrixModule ι
map_id _ := ModuleCat.hom_ext LinearMap.mapMatrixModule_id
  map_comp f g := ModuleCat.hom_ext (LinearMap.mapMatrixModule_comp f.hom g.hom)

Depends on / 依赖: Matrix, ModuleCat, ModuleCat.of
-/
def ModuleCat.toMatrixModCat : ModuleCat R ⥤ ModuleCat (Matrix ι ι R) where
  obj M := ModuleCat.of (Matrix ι ι R) (ι -> M)
map f := ModuleCat.ofHom f.hom.mapMatrixModule ι
map_id _ := ModuleCat.hom_ext LinearMap.mapMatrixModule_id
  map_comp f g := ModuleCat.hom_ext (LinearMap.mapMatrixModule_comp f.hom g.hom)

variable {ι}

namespace MatrixModCat

open Matrix

variable {M : Type*} [AddCommGroup M] [Module (Matrix ι ι R) M] [Module R M]
  [IsScalarTower R (Matrix ι ι R) M]

set_option backward.defeqAttrib.useBackward true in
variable (M) in
/--
Definition of `toModuleCatObj` / `toModuleCatObj` 的定义

English:
definition toModuleCatObj
  signature: (i : ι)
  body: LinearMap.range (τ₁₂ := .id _)
    { __ := DistribSMul.toAddMonoidHom M (single i i 1 : Matrix ι ι R)
      map_smul' r x := by
        dsimp
        have : Commute (diagonal fun x : ι => r) (single i i 1) := by
          ext; simp [Matrix.single]
        rw [← smul_assoc r]; rw [smul_eq_diagonal_mu

中文:
定义 toModuleCatObj
  签名: (i : ι)
  定义体: LinearMap.range (τ₁₂ := .id _)
    { __ := DistribSMul.toAddMonoidHom M (single i i 1 : Matrix ι ι R)
      map_smul' r x := by
        dsimp
        have : Commute (diagonal fun x : ι => r) (single i i 1) := by
          ext; simp [Matrix.single]
        rw [← smul_assoc r]; rw [smul_eq_diagonal_mu

Depends on / 依赖: Commute, DistribSMul, DistribSMul.toAddMonoidHom, LinearMap, LinearMap.range, Matrix, Matrix.single, diagonal, map_smul, mul_smul, nth_rw, one_smul, single, smul_assoc, smul_eq_diagonal_mul, smul_one_eq_diagonal, this.eq, toAddMonoidHom
-/
def toModuleCatObj (i : ι) : Submodule R M :=
LinearMap.range (τ₁₂ := .id _)
    { __ := DistribSMul.toAddMonoidHom M (single i i 1 : Matrix ι ι R)
      map_smul' r x := by
        dsimp
        have : Commute (diagonal fun x : ι => r) (single i i 1) := by
          ext; simp [Matrix.single]
        rw [← smul_assoc r]; rw [smul_eq_diagonal_mul]; rw [this.eq]; rw [mul_smul]; rw [← smul_one_eq_diagonal]
        nth_rw 1 [← one_smul (Matrix ι ι R) x]
        rw [smul_assoc] }

variable {R} in
@[simp]
/--
lemma `mem_toModuleCatObj` / 引理 `mem_toModuleCatObj`

English:
lemma mem_toModuleCatObj
  given: (i : ι) {x : M}
  proof: Iff.rfl

中文:
引理 mem_toModuleCatObj
  条件: (i : ι) {x : M}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_toModuleCatObj (i : ι) {x : M} :
    x in toModuleCatObj R M i ↔ exists y : M, single i i (1 : R) • y = x :=
  Iff.rfl

variable {R} in
/-- An `R`-linear map between `Eᵢᵢ • M` and `Eᵢᵢ • N` induced by an `Mₙ(R)`-linear map
  from `M` to `N`. -/
@[simps!]
/--
Definition of `fromMatrixLinear` / `fromMatrixLinear` 的定义

English:
definition fromMatrixLinear
  signature: {N : Type*} [AddCommGroup N] [Module (Matrix ι ι R) N] (i : ι)
  body: .restrict fun x hx => by f.restrictScalars R
.1 hx obtain ⟨y, rfl⟩ := mem_toModuleCatObj i
.symm⟩ exact ⟨f y, map_smul _ _ _

中文:
定义 fromMatrixLinear
  签名: {N : 类型} [AddCommGroup N] [Module (Matrix ι ι R) N] (i : ι)
  定义体: .restrict fun x hx => by f.restrictScalars R
.1 hx obtain ⟨y, rfl⟩ := mem_toModuleCatObj i
.symm⟩ exact ⟨f y, map_smul _ _ _

Depends on / 依赖: f.restrictScalars, map_smul, mem_toModuleCatObj, restrict, restrictScalars
-/
def fromMatrixLinear {N : Type*} [AddCommGroup N] [Module (Matrix ι ι R) N] (i : ι)
    [Module R N] [IsScalarTower R (Matrix ι ι R) N] (f : M ->ₗ[Matrix ι ι R] N) :
    toModuleCatObj R M i ->ₗ[R] toModuleCatObj R N i :=
.restrict fun x hx => by f.restrictScalars R
.1 hx obtain ⟨y, rfl⟩ := mem_toModuleCatObj i
.symm⟩ exact ⟨f y, map_smul _ _ _

end MatrixModCat

universe w

/--
lemma `MatrixModCat.isScalarTower_toModuleCat` / 引理 `MatrixModCat.isScalarTower_toModuleCat`

English:
lemma MatrixModCat.isScalarTower_toModuleCat
  given: (M : ModuleCat (Matrix ι ι R))
  proof: Module.compHom M (Matrix.scalar (α := R) ι)
    IsScalarTower R (Matrix ι ι R) M :=
  letI := Module.compHom M (Matrix.scalar (α := R) ι)
  { smul_assoc r m x := show _ = Matrix.scalar ι r • (m • x) by
      rw [← mul_smul]; rw [Matrix.scalar_apply]; rw [Matrix.smul_eq_diagonal_mul] }

中文:
引理 MatrixModCat.isScalarTower_toModuleCat
  条件: (M : ModuleCat (Matrix ι ι R))
  证明: Module.compHom M (Matrix.scalar (α := R) ι)
    IsScalarTower R (Matrix ι ι R) M :=
  letI := Module.compHom M (Matrix.scalar (α := R) ι)
  { smul_assoc r m x := show _ = Matrix.scalar ι r • (m • x) by
      rw [← mul_smul]; rw [Matrix.scalar_apply]; rw [Matrix.smul_eq_diagonal_mul] }

Depends on / 依赖: Matrix, Matrix.scalar, Module, Module.compHom, compHom, scalar
-/
lemma MatrixModCat.isScalarTower_toModuleCat (M : ModuleCat (Matrix ι ι R)) :
    letI := Module.compHom M (Matrix.scalar (α := R) ι)
    IsScalarTower R (Matrix ι ι R) M :=
  letI := Module.compHom M (Matrix.scalar (α := R) ι)
  { smul_assoc r m x := show _ = Matrix.scalar ι r • (m • x) by
      rw [← mul_smul]; rw [Matrix.scalar_apply]; rw [Matrix.smul_eq_diagonal_mul] }

/-- The functor from the category of modules over `Mₙ(R)` to the category of modules over `R`
  induced by sending `M` to the image of `Eᵢᵢ • ·` where `Eᵢᵢ` is the elementary matrix. -/
@[simps]
/--
Definition of `MatrixModCat.toModuleCat` / `MatrixModCat.toModuleCat` 的定义

English:
definition MatrixModCat.toModuleCat
  signature: (i : ι)
  body: letI (M : ModuleCat (Matrix ι ι R)) := Module.compHom M (Matrix.scalar (α := R) ι)
  haveI := MatrixModCat.isScalarTower_toModuleCat
  { obj M := ModuleCat.of R (MatrixModCat.toModuleCatObj R M i)
map f := ModuleCat.ofHom fromMatrixLinear i f.hom
    map_id _ := rfl
    map_comp _ _ := rfl }

中文:
定义 MatrixModCat.toModuleCat
  签名: (i : ι)
  定义体: letI (M : ModuleCat (Matrix ι ι R)) := Module.compHom M (Matrix.scalar (α := R) ι)
  haveI := MatrixModCat.isScalarTower_toModuleCat
  { obj M := ModuleCat.of R (MatrixModCat.toModuleCatObj R M i)
map f := ModuleCat.ofHom fromMatrixLinear i f.hom
    map_id _ := rfl
    map_comp _ _ := rfl }

Depends on / 依赖: Matrix, Matrix.scalar, MatrixModCat, MatrixModCat.isScalarTower_toModuleCat, MatrixModCat.toModuleCatObj, Module, Module.compHom, ModuleCat, ModuleCat.of, ModuleCat.ofHom, compHom, f.hom, fromMatrixLinear, isScalarTower_toModuleCat, map_comp, map_id, scalar, toModuleCatObj
-/
def MatrixModCat.toModuleCat (i : ι) : ModuleCat (Matrix ι ι R) ⥤ ModuleCat R :=
  letI (M : ModuleCat (Matrix ι ι R)) := Module.compHom M (Matrix.scalar (α := R) ι)
  haveI := MatrixModCat.isScalarTower_toModuleCat
  { obj M := ModuleCat.of R (MatrixModCat.toModuleCatObj R M i)
map f := ModuleCat.ofHom fromMatrixLinear i f.hom
    map_id _ := rfl
    map_comp _ _ := rfl }

open MatrixModCat Matrix

/--
Definition of `fromModuleCatToModuleCatLinearEquivtoModuleCatObj` / `fromModuleCatToModuleCatLinearEquivtoModuleCatObj` 的定义

English:
definition fromModuleCatToModuleCatLinearEquivtoModuleCatObj
  body: AddEquiv.refl _
map_smul' _ _ := Subtype.ext scalar_smul _ _

中文:
定义 fromModuleCatToModuleCatLinearEquivtoModuleCatObj
  定义体: AddEquiv.refl _
map_smul' _ _ := Subtype.ext scalar_smul _ _

Depends on / 依赖: AddEquiv, AddEquiv.refl
-/
def fromModuleCatToModuleCatLinearEquivtoModuleCatObj
    (M : Type*) [AddCommGroup M] [Module R M] (i : ι) :
    (ModuleCat.toMatrixModCat R ι ⋙ MatrixModCat.toModuleCat R i).obj (.of R M) ≃ₗ[R]
    MatrixModCat.toModuleCatObj R (ι -> M) i where
  __ := AddEquiv.refl _
map_smul' _ _ := Subtype.ext scalar_smul _ _

/-- Auxiliary isomorphism showing that compose two functors gives `id` on objects. -/
@[simps]
/--
Definition of `fromModuleCatToModuleCatLinearEquiv` / `fromModuleCatToModuleCatLinearEquiv` 的定义

English:
definition fromModuleCatToModuleCatLinearEquiv
  signature: (M : Type*) [AddCommGroup M] [Module R M] (i : ι)
  body: ∑ i : ι, x.1 i
  map_add' := by simp [Finset.sum_add_distrib]
  map_smul' r := fun ⟨x, hx⟩ => by simp [Finset.smul_sum]
  invFun x := ⟨Pi.single i x, Function.const ι x, by simp⟩
  left_inv := fun ⟨x, hx⟩ => by
.1 hx obtain ⟨y, hy⟩ := mem_toModuleCatObj i
    rw [single_smul] at hy
    simp [← hy]
 

中文:
定义 fromModuleCatToModuleCatLinearEquiv
  签名: (M : 类型) [AddCommGroup M] [Module R M] (i : ι)
  定义体: ∑ i : ι, x.1 i
  map_add' := by simp [Finset.sum_add_distrib]
  map_smul' r := fun ⟨x, hx⟩ => by simp [Finset.smul_sum]
  invFun x := ⟨Pi.single i x, Function.const ι x, by simp⟩
  left_inv := fun ⟨x, hx⟩ => by
.1 hx obtain ⟨y, hy⟩ := mem_toModuleCatObj i
    rw [single_smul] at hy
    simp [← hy]
 
-/
def fromModuleCatToModuleCatLinearEquiv (M : Type*) [AddCommGroup M] [Module R M] (i : ι) :
    MatrixModCat.toModuleCatObj R (ι -> M) i ≃ₗ[R] M where
  toFun x := ∑ i : ι, x.1 i
  map_add' := by simp [Finset.sum_add_distrib]
  map_smul' r := fun ⟨x, hx⟩ => by simp [Finset.smul_sum]
  invFun x := ⟨Pi.single i x, Function.const ι x, by simp⟩
  left_inv := fun ⟨x, hx⟩ => by
.1 hx obtain ⟨y, hy⟩ := mem_toModuleCatObj i
    rw [single_smul] at hy
    simp [← hy]
  right_inv x := by simp

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `MatrixModCat.unitIso` / `MatrixModCat.unitIso` 的定义

English:
definition MatrixModCat.unitIso
  signature: (i : ι)
  body: NatIso.ofComponents (fun X => (fromModuleCatToModuleCatLinearEquivtoModuleCatObj R X i ≪≫ₗ
    (fromModuleCatToModuleCatLinearEquiv R X i)).toModuleIso) <| by
    intros
    ext
    simp [fromModuleCatToModuleCatLinearEquivtoModuleCatObj]

中文:
定义 MatrixModCat.unitIso
  签名: (i : ι)
  定义体: NatIso.ofComponents (fun X => (fromModuleCatToModuleCatLinearEquivtoModuleCatObj R X i ≪≫ₗ
    (fromModuleCatToModuleCatLinearEquiv R X i)).toModuleIso) <| by
    intros
    ext
    simp [fromModuleCatToModuleCatLinearEquivtoModuleCatObj]

Depends on / 依赖: NatIso, NatIso.ofComponents, fromModuleCatToModuleCatLinearEquiv, fromModuleCatToModuleCatLinearEquivtoModuleCatObj, intros, ofComponents, toModuleIso
-/
def MatrixModCat.unitIso (i : ι) :
    ModuleCat.toMatrixModCat R ι ⋙ MatrixModCat.toModuleCat R i ≅ 𝟭 (ModuleCat R) :=
  NatIso.ofComponents (fun X => (fromModuleCatToModuleCatLinearEquivtoModuleCatObj R X i ≪≫ₗ
    (fromModuleCatToModuleCatLinearEquiv R X i)).toModuleIso) <| by
    intros
    ext
    simp [fromModuleCatToModuleCatLinearEquivtoModuleCatObj]

/--
Definition of `toModuleCatFromModuleCatLinearEquiv` / `toModuleCatFromModuleCatLinearEquiv` 的定义

English:
definition toModuleCatFromModuleCatLinearEquiv
  signature: (M : ModuleCat (Matrix ι ι R)) (j : ι)
  body: Module.compHom M (Matrix.scalar (α := R) ι)
    haveI := MatrixModCat.isScalarTower_toModuleCat
    M ≃ₗ[Matrix ι ι R] (ι -> MatrixModCat.toModuleCatObj R M j) where
  toFun m i := ⟨single j i (1 : R) • m, single j i (1 : R) • m, by
    simp [← mul_smul]⟩
  map_add' _ _ := by ext; simp
map_smul' x m

中文:
定义 toModuleCatFromModuleCatLinearEquiv
  签名: (M : ModuleCat (Matrix ι ι R)) (j : ι)
  定义体: Module.compHom M (Matrix.scalar (α := R) ι)
    haveI := MatrixModCat.isScalarTower_toModuleCat
    M ≃ₗ[Matrix ι ι R] (ι -> MatrixModCat.toModuleCatObj R M j) where
  toFun m i := ⟨single j i (1 : R) • m, single j i (1 : R) • m, by
    simp [← mul_smul]⟩
  map_add' _ _ := by ext; simp
map_smul' x m

Depends on / 依赖: IsScalarTower, Matrix, Matrix.scalar, Module, Module.compHom, compHom, scalar
-/
def toModuleCatFromModuleCatLinearEquiv (M : ModuleCat (Matrix ι ι R)) (j : ι) :
    letI := Module.compHom M (Matrix.scalar (α := R) ι)
    haveI := MatrixModCat.isScalarTower_toModuleCat
    M ≃ₗ[Matrix ι ι R] (ι -> MatrixModCat.toModuleCatObj R M j) where
  toFun m i := ⟨single j i (1 : R) • m, single j i (1 : R) • m, by
    simp [← mul_smul]⟩
  map_add' _ _ := by ext; simp
map_smul' x m := funext fun i => Subtype.ext by
    let := Module.compHom M (Matrix.scalar (α := R) ι)
    have := MatrixModCat.isScalarTower_toModuleCat R M
    simp only [← mul_smul, RingHom.id_apply, Module.smul_apply,
      AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, ← smul_assoc, ← Finset.sum_smul]
    congr
    ext i1 j1
    simp only [mul_apply, smul_single, smul_eq_mul, mul_one, sum_apply]
    rw [Finset.sum_eq_single_of_mem (a := i) (by simp) (fun b _ hb => by simp [single]; rw [Ne.symm hb])]
    simp only [single_apply, and_true, ite_mul, one_mul, zero_mul]
    split_ifs with h <;> simp [h]
  invFun m := ∑ i, single i j (1 : R) • m i
  left_inv m := by simp [← mul_smul, ← Finset.sum_smul, sum_single_one]
  right_inv v := by
    dsimp
    ext i
    simp only [Finset.smul_sum]
    rw [Finset.sum_eq_single i (fun b _ hb => by
      simp [← mul_smul]; rw [single_mul_single_of_ne _ _ _ _ hb.symm]) (by simp)]
    obtain ⟨y, hy⟩ := by simpa [-SetLike.coe_mem] using (v i).2
    simp [← mul_smul, ← hy]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `MatrixModCat.counitIso` / `MatrixModCat.counitIso` 的定义

English:
definition MatrixModCat.counitIso
  signature: (i : ι)
  body: NatIso.ofComponents (fun X => ((toModuleCatFromModuleCatLinearEquiv R X i).symm).toModuleIso) by
    intros
    ext
    simp [toModuleCatFromModuleCatLinearEquiv]

中文:
定义 MatrixModCat.counitIso
  签名: (i : ι)
  定义体: NatIso.ofComponents (fun X => ((toModuleCatFromModuleCatLinearEquiv R X i).symm).toModuleIso) by
    intros
    ext
    simp [toModuleCatFromModuleCatLinearEquiv]

Depends on / 依赖: IsScalarTower, NatIso, NatIso.ofComponents, intros, ofComponents, toModuleCatFromModuleCatLinearEquiv, toModuleIso
-/
def MatrixModCat.counitIso (i : ι) :
    MatrixModCat.toModuleCat R i ⋙ ModuleCat.toMatrixModCat R ι ≅ 𝟭 (ModuleCat (Matrix ι ι R)) :=
NatIso.ofComponents (fun X => ((toModuleCatFromModuleCatLinearEquiv R X i).symm).toModuleIso) by
    intros
    ext
    simp [toModuleCatFromModuleCatLinearEquiv]

set_option backward.isDefEq.respectTransparency false in
-- This declaration has been on the tipping point of timeout ever since nightly-2026-02-23.
/-- `ModuleCat.toMatrixModCat R ι` and `MatrixModCat.toModuleCat R i` together form
  an equivalence of categories. -/
@[simps, stacks 074D "(1)"]
/--
Definition of `ModuleCat.matrixEquivalence` / `ModuleCat.matrixEquivalence` 的定义

English:
definition ModuleCat.matrixEquivalence
  signature: (i : ι)
  body: ModuleCat.toMatrixModCat R ι
  inverse := MatrixModCat.toModuleCat R i
.symm unitIso := MatrixModCat.unitIso R i
  counitIso := MatrixModCat.counitIso R i
  functor_unitIso_comp X := by
    ext1
    suffices (toModuleCatFromModuleCatLinearEquiv R ((ModuleCat.toMatrixModCat R ι).obj X)
      i).symm.

中文:
定义 ModuleCat.matrixEquivalence
  签名: (i : ι)
  定义体: ModuleCat.toMatrixModCat R ι
  inverse := MatrixModCat.toModuleCat R i
.symm unitIso := MatrixModCat.unitIso R i
  counitIso := MatrixModCat.counitIso R i
  functor_unitIso_comp X := by
    ext1
    suffices (toModuleCatFromModuleCatLinearEquiv R ((ModuleCat.toMatrixModCat R ι).obj X)
      i).symm.

Depends on / 依赖: ModuleCat, ModuleCat.toMatrixModCat, SMulCommClass, toMatrixModCat
-/
def ModuleCat.matrixEquivalence (i : ι) : ModuleCat R ≌ ModuleCat (Matrix ι ι R) where
  functor := ModuleCat.toMatrixModCat R ι
  inverse := MatrixModCat.toModuleCat R i
.symm unitIso := MatrixModCat.unitIso R i
  counitIso := MatrixModCat.counitIso R i
  functor_unitIso_comp X := by
    ext1
    suffices (toModuleCatFromModuleCatLinearEquiv R ((ModuleCat.toMatrixModCat R ι).obj X)
      i).symm.toLinearMap ∘ₗ LinearMap.mapMatrixModule ι (ModuleCat.Hom.hom
      ((unitIso R i).inv.app X)) = LinearMap.id by simpa using! this
    ext x
    simp [unitIso, toModuleCatFromModuleCatLinearEquiv, fromModuleCatToModuleCatLinearEquiv,
      fromModuleCatToModuleCatLinearEquivtoModuleCatObj, Finset.univ_sum_single]

set_option backward.isDefEq.respectTransparency false in
open ModuleCat.Algebra in
/-- Moreover `ModuleCat.matrixEquivalence` is a `MoritaEquivalence`. -/
@[simps]
/--
Definition of `moritaEquivalenceMatrix` / `moritaEquivalenceMatrix` 的定义

English:
definition moritaEquivalenceMatrix
  signature: (R₀ : Type*) [CommRing R₀] [Algebra R₀ R] (i : ι)
  body: ModuleCat.matrixEquivalence R i
  linear.map_smul {X Y} f r := by
    ext (v : ι -> X)
    simp only [ModuleCat.matrixEquivalence_functor, ModuleCat.toMatrixModCat_obj_carrier,
      ModuleCat.toMatrixModCat_map, ModuleCat.hom_smul, ModuleCat.hom_ofHom, LinearMap.smul_apply]
    ext i
    simp only 

中文:
定义 moritaEquivalenceMatrix
  签名: (R₀ : 类型) [CommRing R₀] [Algebra R₀ R] (i : ι)
  定义体: ModuleCat.matrixEquivalence R i
  linear.map_smul {X Y} f r := by
    ext (v : ι -> X)
    simp only [ModuleCat.matrixEquivalence_functor, ModuleCat.toMatrixModCat_obj_carrier,
      ModuleCat.toMatrixModCat_map, ModuleCat.hom_smul, ModuleCat.hom_ofHom, LinearMap.smul_apply]
    ext i
    simp only 

Depends on / 依赖: ModuleCat, ModuleCat.matrixEquivalence, SMulCommClass, matrixEquivalence
-/
def moritaEquivalenceMatrix (R₀ : Type*) [CommRing R₀] [Algebra R₀ R] (i : ι) :
    MoritaEquivalence R₀ R (Matrix ι ι R) where
  eqv := ModuleCat.matrixEquivalence R i
  linear.map_smul {X Y} f r := by
    ext (v : ι -> X)
    simp only [ModuleCat.matrixEquivalence_functor, ModuleCat.toMatrixModCat_obj_carrier,
      ModuleCat.toMatrixModCat_map, ModuleCat.hom_smul, ModuleCat.hom_ofHom, LinearMap.smul_apply]
    ext i
    simp only [LinearMap.mapMatrixModule_apply, LinearMap.compLeft_apply, Function.comp_apply,
      LinearMap.smul_apply]
    change _ = ((algebraMap R₀ (Matrix ι ι R) r) • ((ModuleCat.Hom.hom f).mapMatrixModule ι v)) i
    simp [Matrix.algebraMap_matrix_apply]

/--
theorem `IsMoritaEquivalent.matrix` / 定理 `IsMoritaEquivalent.matrix`

English:
theorem IsMoritaEquivalent.matrix
  given: (R₀ : Type*) [CommRing R₀] [Algebra R₀ R] [Nonempty ι]
  proof: ⟨Nonempty.map (moritaEquivalenceMatrix R R₀) inferInstance⟩

中文:
定理 IsMoritaEquivalent.matrix
  条件: (R₀ : 类型) [CommRing R₀] [Algebra R₀ R] [Nonempty ι]
  证明: ⟨Nonempty.map (moritaEquivalenceMatrix R R₀) inferInstance⟩

Depends on / 依赖: MulAction, Nonempty, Nonempty.map, moritaEquivalenceMatrix
-/
theorem IsMoritaEquivalent.matrix (R₀ : Type*) [CommRing R₀] [Algebra R₀ R] [Nonempty ι] :
    IsMoritaEquivalent R₀ R (Matrix ι ι R) :=
  ⟨Nonempty.map (moritaEquivalenceMatrix R R₀) inferInstance⟩
