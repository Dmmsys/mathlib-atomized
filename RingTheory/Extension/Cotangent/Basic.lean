/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Extension.Presentation.Basic

/-!

# Naive cotangent complex associated to a presentation.

Given a presentation `0 → I → R[x₁,...,xₙ] → S → 0` (or equivalently a closed embedding `S ↪ Aⁿ`
defined by `I`), we may define the (naive) cotangent complex `I/I² → ⨁ᵢ S dxᵢ → Ω[S/R] → 0`.

## Main results
- `Algebra.Extension.Cotangent`: The conormal space `I/I²`. (Defined in `Generators/Basic`)
- `Algebra.Extension.CotangentSpace`: The cotangent space `⨁ᵢ S dxᵢ`.
- `Algebra.Generators.cotangentSpaceBasis`: The canonical basis on `⨁ᵢ S dxᵢ`.
- `Algebra.Extension.CotangentComplex`: The map `I/I² → ⨁ᵢ S dxᵢ`.
- `Algebra.Extension.toKaehler`: The projection `⨁ᵢ S dxᵢ → Ω[S/R]`.
- `Algebra.Extension.toKaehler_surjective`: The map `⨁ᵢ S dxᵢ → Ω[S/R]` is surjective.
- `Algebra.Extension.exact_cotangentComplex_toKaehler`: `I/I² → ⨁ᵢ S dxᵢ → Ω[S/R]` is exact.
- `Algebra.Extension.Hom.Sub`: If `f` and `g` are two maps between presentations, `f - g` induces
  a map `⨁ᵢ S dxᵢ → I/I²` that makes `f` and `g` homotopic.
- `Algebra.Extension.H1Cotangent`: The first homology of the (naive) cotangent complex
  of `S` over `R`, induced by a given presentation.
- `Algebra.H1Cotangent`: `H¹(L_{S/R})`,
  the first homology of the (naive) cotangent complex of `S` over `R`.

## Implementation detail
We actually develop these material for general extensions (i.e. surjection `P → S`) so that we can
apply them to infinitesimal smooth (or versal) extensions later.

-/

@[expose] public noncomputable section

open KaehlerDifferential Module MvPolynomial TensorProduct

namespace Algebra

universe w u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

namespace Extension

variable (P : Extension.{w} R S)

/--
Definition of `CotangentSpace` / `CotangentSpace` 的定义

English:
abbreviation CotangentSpace
  signature: : Type _
  body: S otimes[P.Ring] Ω[P.Ring⁄R]

中文:
缩写 CotangentSpace
  签名: : 类型 _
  定义体: S otimes[P.Ring] Ω[P.Ring⁄R]

Depends on / 依赖: P.Ring, otimes
-/
abbrev CotangentSpace : Type _ := S otimes[P.Ring] Ω[P.Ring⁄R]

/--
Definition of `cotangentComplex` / `cotangentComplex` 的定义

English:
definition cotangentComplex
  signature: : P.Cotangent ->ₗ[S] P.CotangentSpace
  body: letI f : P.Cotangent ≃ₗ[P.Ring] P.ker.Cotangent :=
    { __ := AddEquiv.refl _, map_smul' := Cotangent.val_smul' }
  (kerCotangentToTensor R P.Ring S ∘ₗ f).extendScalarsOfSurjective P.algebraMap_surjective

@[simp]

中文:
定义 cotangentComplex
  签名: : P.余切 ->ₗ[S] P.CotangentSpace
  定义体: letI f : P.Cotangent ≃ₗ[P.Ring] P.ker.Cotangent :=
    { __ := AddEquiv.refl _, map_smul' := Cotangent.val_smul' }
  (kerCotangentToTensor R P.Ring S ∘ₗ f).extendScalarsOfSurjective P.algebraMap_surjective

@[simp]

Depends on / 依赖: AddEquiv, AddEquiv.refl, Cotangent, Cotangent.val_smul, P.Cotangent, P.Ring, P.algebraMap_surjective, P.ker.Cotangent, algebraMap_surjective, extendScalarsOfSurjective, kerCotangentToTensor, map_smul, val_smul
-/
def cotangentComplex : P.Cotangent ->ₗ[S] P.CotangentSpace :=
  letI f : P.Cotangent ≃ₗ[P.Ring] P.ker.Cotangent :=
    { __ := AddEquiv.refl _, map_smul' := Cotangent.val_smul' }
  (kerCotangentToTensor R P.Ring S ∘ₗ f).extendScalarsOfSurjective P.algebraMap_surjective

@[simp]
/--
lemma `cotangentComplex_mk` / 引理 `cotangentComplex_mk`

English:
lemma cotangentComplex_mk
  given: (x)
  statement: P.cotangentComplex (.mk x) = 1 otimesₜ .D _ _ x
  proof: rfl

中文:
引理 cotangentComplex_mk
  条件: (x)
  结论: P.cotangentComplex (.mk x) = 1 otimesₜ .D _ _ x
  证明: rfl
-/
lemma cotangentComplex_mk (x) : P.cotangentComplex (.mk x) = 1 otimesₜ .D _ _ x :=
  rfl

/--
lemma `Cotangent.mk_C_mem_ker_cotangentComplex` / 引理 `Cotangent.mk_C_mem_ker_cotangentComplex`

English:
lemma Cotangent.mk_C_mem_ker_cotangentComplex
  statement: {σ : Type*} (G : Generators R S σ)
  proof: by
  have : D R G.toExtension.Ring (C r) = 0 := Derivation.map_algebraMap ..
  simp [this]

中文:
引理 余切.mk_C_mem_ker_cotangentComplex
  结论: {σ : 类型} (G : 生成元 R S σ)
  证明: by
  have : D R G.toExtension.Ring (C r) = 0 := Derivation.map_algebraMap ..
  simp [this]

Depends on / 依赖: Derivation, Derivation.map_algebraMap, G.toExtension.Ring, map_algebraMap, toExtension
-/
lemma Cotangent.mk_C_mem_ker_cotangentComplex {σ : Type*} (G : Generators R S σ)
    {r : R} (hr : C r in G.ker) :
    Extension.Cotangent.mk ⟨C r, hr⟩ in G.toExtension.cotangentComplex.ker := by
  have : D R G.toExtension.Ring (C r) = 0 := Derivation.map_algebraMap ..
  simp [this]

section baseChange

variable {A : Type*} [CommRing A] [Algebra S A] [Algebra P.Ring A] [IsScalarTower P.Ring S A]

variable (R S) in
/--
Definition of `_root_.KaehlerDifferential.cotangentComplexBaseChange` / `_root_.KaehlerDifferential.cotangentComplexBaseChange` 的定义

English:
definition _root_.KaehlerDifferential.cotangentComplexBaseChange
  body: LinearMap.liftBaseChange _ (KaehlerDifferential.kerToTensor _ _ _ ∘ₗ Submodule.inclusion
    (by rw [IsScalarTower.algebraMap_eq P S A]; intro; aesop))

omit [Algebra R S] in

中文:
定义 _root_.KaehlerDifferential.cotangentComplexBaseChange
  定义体: LinearMap.liftBaseChange _ (KaehlerDifferential.kerToTensor _ _ _ ∘ₗ Submodule.inclusion
    (by rw [IsScalarTower.algebraMap_eq P S A]; intro; aesop))

omit [Algebra R S] in

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_eq, KaehlerDifferential, KaehlerDifferential.kerToTensor, LinearMap, LinearMap.liftBaseChange, Submodule, Submodule.inclusion, algebraMap_eq, inclusion, kerToTensor, liftBaseChange
-/
def _root_.KaehlerDifferential.cotangentComplexBaseChange
    (P A : Type*) [CommRing P] [CommRing A] [Algebra P S] [Algebra P A]
    [Algebra R P] [Algebra S A] [IsScalarTower P S A] :
    A otimes[P] RingHom.ker (algebraMap P S) ->ₗ[A] A otimes[P] Ω[P⁄R] :=
  LinearMap.liftBaseChange _ (KaehlerDifferential.kerToTensor _ _ _ ∘ₗ Submodule.inclusion
    (by rw [IsScalarTower.algebraMap_eq P S A]; intro; aesop))

omit [Algebra R S] in
/--
lemma `_root_.KaehlerDifferential.cotangentComplexBaseChange_tmul` / 引理 `_root_.KaehlerDifferential.cotangentComplexBaseChange_tmul`

English:
lemma _root_.KaehlerDifferential.cotangentComplexBaseChange_tmul
  proof: rfl

中文:
引理 _root_.KaehlerDifferential.cotangentComplexBaseChange_tmul
  证明: rfl
-/
lemma _root_.KaehlerDifferential.cotangentComplexBaseChange_tmul
    {P A : Type*} [CommRing P] [CommRing A] [Algebra P S]
    [Algebra P A] [Algebra R P] [Algebra S A] [IsScalarTower P S A] (a b) :
  cotangentComplexBaseChange R S P A (a otimesₜ b) =
    a • kerToTensor R P A ⟨b.1, by rw [IsScalarTower.algebraMap_eq P S A]; aesop⟩ := rfl

variable (A) in
/--
lemma `cotangentComplexBaseChange_eq_lTensor_cotangentComplex` / 引理 `cotangentComplexBaseChange_eq_lTensor_cotangentComplex`

English:
lemma cotangentComplexBaseChange_eq_lTensor_cotangentComplex
  proof: by
  ext x
  simp [LinearEquiv.baseChange, cotangentComplexBaseChange_tmul]

中文:
引理 cotangentComplexBaseChange_eq_lTensor_cotangentComplex
  证明: by
  ext x
  simp [LinearEquiv.baseChange, cotangentComplexBaseChange_tmul]

Depends on / 依赖: LinearEquiv, LinearEquiv.baseChange, baseChange, cotangentComplexBaseChange_tmul
-/
lemma cotangentComplexBaseChange_eq_lTensor_cotangentComplex :
  cotangentComplexBaseChange R S P.Ring A =
    AlgebraTensorModule.cancelBaseChange P.Ring S A A Ω[P.Ring⁄R] ∘ₗ
      P.cotangentComplex.baseChange A ∘ₗ
      ((AlgebraTensorModule.cancelBaseChange P.Ring S A A P.ker).symm ≪≫ₗ
        P.cotangentEquiv.baseChange (A := A)) := by
  ext x
  simp [LinearEquiv.baseChange, cotangentComplexBaseChange_tmul]

variable (A) in
/--
lemma `lTensor_cotangentComplex_eq_cotangentComplexBaseChange` / 引理 `lTensor_cotangentComplex_eq_cotangentComplexBaseChange`

English:
lemma lTensor_cotangentComplex_eq_cotangentComplexBaseChange
  proof: by
  apply LinearMap.coe_injective
  dsimp
  rw [LinearEquiv.eq_symm_comp]; rw [← LinearEquiv.comp_symm_eq]
  exact congr(($(cotangentComplexBaseChange_eq_lTensor_cotangentComplex P A) : _ -> _)).symm

中文:
引理 lTensor_cotangentComplex_eq_cotangentComplexBaseChange
  证明: by
  apply LinearMap.coe_injective
  dsimp
  rw [LinearEquiv.eq_symm_comp]; rw [← LinearEquiv.comp_symm_eq]
  exact congr(($(cotangentComplexBaseChange_eq_lTensor_cotangentComplex P A) : _ -> _)).symm

Depends on / 依赖: LinearEquiv, LinearEquiv.comp_symm_eq, LinearEquiv.eq_symm_comp, LinearMap, LinearMap.coe_injective, coe_injective, comp_symm_eq, cotangentComplexBaseChange_eq_lTensor_cotangentComplex, eq_symm_comp
-/
lemma lTensor_cotangentComplex_eq_cotangentComplexBaseChange :
  P.cotangentComplex.baseChange A =
    (AlgebraTensorModule.cancelBaseChange P.Ring S A A Ω[P.Ring⁄R]).symm ∘ₗ
      cotangentComplexBaseChange R S P.Ring A ∘ₗ
      ((AlgebraTensorModule.cancelBaseChange P.Ring S A A P.ker).symm ≪≫ₗ
        P.cotangentEquiv.baseChange (A := A)).symm := by
  apply LinearMap.coe_injective
  dsimp
  rw [LinearEquiv.eq_symm_comp]; rw [← LinearEquiv.comp_symm_eq]
  exact congr(($(cotangentComplexBaseChange_eq_lTensor_cotangentComplex P A) : _ -> _)).symm

end baseChange

universe w' u' v'

variable {R' : Type u'} {S' : Type v'} [CommRing R'] [CommRing S'] [Algebra R' S']
variable (P' : Extension.{w'} R' S')
variable [Algebra R R'] [Algebra S S'] [Algebra R S'] [IsScalarTower R R' S']

attribute [local instance] SMulCommClass.of_commMonoid

variable {P P'}

universe w'' u'' v''

variable {R'' : Type u''} {S'' : Type v''} [CommRing R''] [CommRing S''] [Algebra R'' S'']
variable {P'' : Extension.{w''} R'' S''}
variable [Algebra R R''] [Algebra S S''] [Algebra R S'']
  [IsScalarTower R R'' S'']
variable [Algebra R' R''] [Algebra S' S''] [Algebra R' S'']
  [IsScalarTower R' R'' S'']
variable [IsScalarTower R R' R''] [IsScalarTower S S' S'']

namespace CotangentSpace

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : Hom P P')
  body: by
  letI := ((algebraMap S S').comp (algebraMap P.Ring S)).toAlgebra
  haveI : IsScalarTower P.Ring S S' := IsScalarTower.of_algebraMap_eq' rfl
  letI := f.toAlgHom.toAlgebra
  haveI : IsScalarTower P.Ring P'.Ring S' :=
    IsScalarTower.of_algebraMap_eq (fun x => (f.algebraMap_toRingHom x).symm)
  apply LinearMap.liftBaseChange
  refine (TensorProduct.mk _ _ _ 1).restrictScalars _ ∘ₗ KaehlerDifferential.map R R' P.Ring P'.Ring

中文:
定义 map
  签名: (f : 态射 P P')
  定义体: by
  letI := ((algebraMap S S').comp (algebraMap P.Ring S)).toAlgebra
  haveI : IsScalarTower P.Ring S S' := IsScalarTower.of_algebraMap_eq' rfl
  letI := f.toAlgHom.toAlgebra
  haveI : IsScalarTower P.Ring P'.Ring S' :=
    IsScalarTower.of_algebraMap_eq (fun x => (f.algebraMap_toRingHom x).symm)
  apply LinearMap.liftBaseChange
  refine (TensorProduct.mk _ _ _ 1).restrictScalars _ ∘ₗ KaehlerDifferential.map R R' P.Ring P'.Ring
-/
protected def map (f : Hom P P') : P.CotangentSpace ->ₗ[S] P'.CotangentSpace := by
  letI := ((algebraMap S S').comp (algebraMap P.Ring S)).toAlgebra
  haveI : IsScalarTower P.Ring S S' := IsScalarTower.of_algebraMap_eq' rfl
  letI := f.toAlgHom.toAlgebra
  haveI : IsScalarTower P.Ring P'.Ring S' :=
    IsScalarTower.of_algebraMap_eq (fun x => (f.algebraMap_toRingHom x).symm)
  apply LinearMap.liftBaseChange
  refine (TensorProduct.mk _ _ _ 1).restrictScalars _ ∘ₗ KaehlerDifferential.map R R' P.Ring P'.Ring

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `map_tmul` / 引理 `map_tmul`

English:
lemma map_tmul
  given: (f : Hom P P') (x y)
  proof: by
  simp only [CotangentSpace.map, AlgHom.toRingHom_eq_coe, LinearMap.liftBaseChange_tmul,
    LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply, map_D, mk_apply]
  rw [smul_tmul']; rw [← Algebra.algebraMap_eq_smul_one]
  rfl

中文:
引理 map_tmul
  条件: (f : 态射 P P') (x y)
  证明: by
  simp only [CotangentSpace.map, AlgHom.toRingHom_eq_coe, LinearMap.liftBaseChange_tmul,
    LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply, map_D, mk_apply]
  rw [smul_tmul']; rw [← Algebra.algebraMap_eq_smul_one]
  rfl

Depends on / 依赖: AlgHom, AlgHom.toRingHom_eq_coe, Algebra, Algebra.algebraMap_eq_smul_one, CotangentSpace, CotangentSpace.map, Function, Function.comp_apply, LinearMap, LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearMap.liftBaseChange_tmul, algebraMap_eq_smul_one, coe_comp, coe_restrictScalars, comp_apply, liftBaseChange_tmul, map_D, mk_apply, smul_tmul
-/
lemma map_tmul (f : Hom P P') (x y) :
    CotangentSpace.map f (x otimesₜ .D _ _ y) = (algebraMap _ _ x) otimesₜ .D _ _ (f.toAlgHom y) := by
  simp only [CotangentSpace.map, AlgHom.toRingHom_eq_coe, LinearMap.liftBaseChange_tmul,
    LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply, map_D, mk_apply]
  rw [smul_tmul']; rw [← Algebra.algebraMap_eq_smul_one]
  rfl

/--
lemma `map_tmul_eq_tmul_map` / 引理 `map_tmul_eq_tmul_map`

English:
lemma map_tmul_eq_tmul_map
  given: (f : P.Hom P') (x : S) (y : Ω[P.Ring⁄R])
  proof: f.toAlgHom.toAlgebra
    (CotangentSpace.map f) (x otimesₜ[P.Ring] y) =
      (algebraMap S S') x otimesₜ[P'.Ring] KaehlerDifferential.map _ _ _ _ y := by
  rw [CotangentSpace.map]; rw [LinearMap.liftBaseChange_tmul]; rw [LinearMap.coe_comp]; rw [Function.comp_apply]; rw [LinearMap.restrictScalars_apply]; rw [mk_apply]; rw [smul_tmul']; rw [Algebra.smul_def]; rw [mul_one]

@[simp]

中文:
引理 map_tmul_eq_tmul_map
  条件: (f : P.态射 P') (x : S) (y : Ω[P.环⁄R])
  证明: f.toAlgHom.toAlgebra
    (CotangentSpace.map f) (x otimesₜ[P.Ring] y) =
      (algebraMap S S') x otimesₜ[P'.Ring] KaehlerDifferential.map _ _ _ _ y := by
  rw [CotangentSpace.map]; rw [LinearMap.liftBaseChange_tmul]; rw [LinearMap.coe_comp]; rw [Function.comp_apply]; rw [LinearMap.restrictScalars_apply]; rw [mk_apply]; rw [smul_tmul']; rw [Algebra.smul_def]; rw [mul_one]

@[simp]

Depends on / 依赖: f.toAlgHom.toAlgebra, toAlgHom, toAlgebra
-/
lemma map_tmul_eq_tmul_map (f : P.Hom P') (x : S) (y : Ω[P.Ring⁄R]) :
    letI : Algebra P.Ring P'.Ring := f.toAlgHom.toAlgebra
    (CotangentSpace.map f) (x otimesₜ[P.Ring] y) =
      (algebraMap S S') x otimesₜ[P'.Ring] KaehlerDifferential.map _ _ _ _ y := by
  rw [CotangentSpace.map]; rw [LinearMap.liftBaseChange_tmul]; rw [LinearMap.coe_comp]; rw [Function.comp_apply]; rw [LinearMap.restrictScalars_apply]; rw [mk_apply]; rw [smul_tmul']; rw [Algebra.smul_def]; rw [mul_one]

@[simp]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  proof: by ext; simp

中文:
引理 map_id
  证明: by ext; simp
-/
lemma map_id :
    CotangentSpace.map (.id P) = LinearMap.id := by ext; simp

/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  given: (f : Hom P P') (g : Hom P' P'')
  proof: by
  ext x
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
  | add =>
    simp only [map_add, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply, *]
  | tmul x y =>
    obtain ⟨y, rfl⟩ := KaehlerDifferential.tensorProductTo_surjective _ _ y
    induction y with
    | zero => simp only [map_zero, tmul_zero]
    | add => simp only [map_add, tmul_add, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
      Function.comp_apply, *]
    | tmul => simp only [Derivation.tensorProductTo_tmul, tmul_smul, smul_tmul', map_tmul,
        Hom.toAlgHom_apply, Hom.comp_toRingHom, RingHom.coe_comp, Function.comp_apply,
        LinearMap.coe_comp, LinearMap.coe_restrictScalars,
        ← IsScalarTower.algebraMap_apply S S' S'']

中文:
引理 map_comp
  条件: (f : 态射 P P') (g : 态射 P' P'')
  证明: by
  ext x
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
  | add =>
    simp only [map_add, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply, *]
  | tmul x y =>
    obtain ⟨y, rfl⟩ := KaehlerDifferential.tensorProductTo_surjective _ _ y
    induction y with
    | zero => simp only [map_zero, tmul_zero]
    | add => simp only [map_add, tmul_add, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
      Function.comp_apply, *]
    | tmul => simp only [Derivation.tensorProductTo_tmul, tmul_smul, smul_tmul', map_tmul,
        Hom.toAlgHom_apply, Hom.comp_toRingHom, RingHom.coe_comp, Function.comp_apply,
        LinearMap.coe_comp, LinearMap.coe_restrictScalars,
        ← IsScalarTower.algebraMap_apply S S' S'']

Depends on / 依赖: Derivation, Derivation.tensorProductTo, Function, Function.comp_apply, KaehlerDifferential, KaehlerDifferential.tensorProductTo_surjective, LinearMap, LinearMap.coe_comp, LinearMap.coe_restrictScalars, TensorProduct, TensorProduct.induction_on, coe_comp, coe_restrictScalars, comp_apply, induction_on, map_add, map_zero, tensorProductTo, tensorProductTo_surjective, tmul_add
-/
lemma map_comp (f : Hom P P') (g : Hom P' P'') :
    CotangentSpace.map (g.comp f) =
      (CotangentSpace.map g).restrictScalars S ∘ₗ CotangentSpace.map f := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
  | add =>
    simp only [map_add, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply, *]
  | tmul x y =>
    obtain ⟨y, rfl⟩ := KaehlerDifferential.tensorProductTo_surjective _ _ y
    induction y with
    | zero => simp only [map_zero, tmul_zero]
    | add => simp only [map_add, tmul_add, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
      Function.comp_apply, *]
    | tmul => simp only [Derivation.tensorProductTo_tmul, tmul_smul, smul_tmul', map_tmul,
        Hom.toAlgHom_apply, Hom.comp_toRingHom, RingHom.coe_comp, Function.comp_apply,
        LinearMap.coe_comp, LinearMap.coe_restrictScalars,
        ← IsScalarTower.algebraMap_apply S S' S'']

/--
lemma `map_comp_apply` / 引理 `map_comp_apply`

English:
lemma map_comp_apply
  given: (f : Hom P P') (g : Hom P' P'') (x)
  proof: DFunLike.congr_fun (map_comp f g) x

中文:
引理 map_comp_apply
  条件: (f : 态射 P P') (g : 态射 P' P'') (x)
  证明: DFunLike.congr_fun (map_comp f g) x

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, map_comp
-/
lemma map_comp_apply (f : Hom P P') (g : Hom P' P'') (x) :
    CotangentSpace.map (g.comp f) x = .map g (.map f x) :=
  DFunLike.congr_fun (map_comp f g) x

/--
lemma `map_cotangentComplex` / 引理 `map_cotangentComplex`

English:
lemma map_cotangentComplex
  given: (f : Hom P P') (x)
  proof: by
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  rw [cotangentComplex_mk]; rw [map_tmul]; rw [map_one]; rw [Cotangent.map_mk]; rw [cotangentComplex_mk]

中文:
引理 map_cotangentComplex
  条件: (f : 态射 P P') (x)
  证明: by
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  rw [cotangentComplex_mk]; rw [map_tmul]; rw [map_one]; rw [Cotangent.map_mk]; rw [cotangentComplex_mk]

Depends on / 依赖: Cotangent, Cotangent.map_mk, Cotangent.mk_surjective, cotangentComplex_mk, map_mk, map_one, map_tmul, mk_surjective
-/
lemma map_cotangentComplex (f : Hom P P') (x) :
    CotangentSpace.map f (P.cotangentComplex x) = P'.cotangentComplex (.map f x) := by
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  rw [cotangentComplex_mk]; rw [map_tmul]; rw [map_one]; rw [Cotangent.map_mk]; rw [cotangentComplex_mk]

/--
lemma `map_comp_cotangentComplex` / 引理 `map_comp_cotangentComplex`

English:
lemma map_comp_cotangentComplex
  given: (f : Hom P P')
  proof: by
  ext x; exact map_cotangentComplex f x

中文:
引理 map_comp_cotangentComplex
  条件: (f : 态射 P P')
  证明: by
  ext x; exact map_cotangentComplex f x

Depends on / 依赖: map_cotangentComplex
-/
lemma map_comp_cotangentComplex (f : Hom P P') :
    CotangentSpace.map f ∘ₗ P.cotangentComplex =
      P'.cotangentComplex.restrictScalars S ∘ₗ Cotangent.map f := by
  ext x; exact map_cotangentComplex f x

end CotangentSpace

/--
lemma `Hom.sub_aux` / 引理 `Hom.sub_aux`

English:
lemma Hom.sub_aux
  given: (f g : Hom P P') (x y)
  proof: ((algebraMap S S').comp (algebraMap P.Ring S)).toAlgebra
    f.toAlgHom (x * y) - g.toAlgHom (x * y) -
        (P'.σ ((algebraMap P.Ring S') x) * (f.toAlgHom y - g.toAlgHom y) +
          P'.σ ((algebraMap P.Ring S') y) * (f.toAlgHom x - g.toAlgHom x)) in
      P'.ker ^ 2 := by
  let := ((algebraMap S S').comp (algebraMap P.Ring S)).toAlgebra
  have :
      (f.toAlgHom x - P'.σ (algebraMap P.Ring S' x)) * (f.toAlgHom y - g.toAlgHom y) +
      (g.toAlgHom y - P'.σ (algebraMap P.Ring S' y)) * (f.toAlgHom x - g.toAlgHom x)
        in P'.ker ^ 2 := by
    rw [pow_two]
    refine Ideal.add_mem _ (Ideal.mul_mem_mul ?_ ?_) (Ideal.mul_mem_mul ?_ ?_) <;>
      simp only [RingHom.algebraMap_toAlgebra, RingHom.coe_comp,
        Function.comp_apply,
        ker, RingHom.mem_ker, map_sub, algebraMap_toRingHom,
        algebraMap_σ, sub_self, toAlgHom_apply]
  convert! this using 1
  simp only [map_mul]
  ring

中文:
引理 态射.sub_aux
  条件: (f g : 态射 P P') (x y)
  证明: ((algebraMap S S').comp (algebraMap P.Ring S)).toAlgebra
    f.toAlgHom (x * y) - g.toAlgHom (x * y) -
        (P'.σ ((algebraMap P.Ring S') x) * (f.toAlgHom y - g.toAlgHom y) +
          P'.σ ((algebraMap P.Ring S') y) * (f.toAlgHom x - g.toAlgHom x)) in
      P'.ker ^ 2 := by
  let := ((algebraMap S S').comp (algebraMap P.Ring S)).toAlgebra
  have :
      (f.toAlgHom x - P'.σ (algebraMap P.Ring S' x)) * (f.toAlgHom y - g.toAlgHom y) +
      (g.toAlgHom y - P'.σ (algebraMap P.Ring S' y)) * (f.toAlgHom x - g.toAlgHom x)
        in P'.ker ^ 2 := by
    rw [pow_two]
    refine Ideal.add_mem _ (Ideal.mul_mem_mul ?_ ?_) (Ideal.mul_mem_mul ?_ ?_) <;>
      simp only [RingHom.algebraMap_toAlgebra, RingHom.coe_comp,
        Function.comp_apply,
        ker, RingHom.mem_ker, map_sub, algebraMap_toRingHom,
        algebraMap_σ, sub_self, toAlgHom_apply]
  convert! this using 1
  simp only [map_mul]
  ring

Depends on / 依赖: P.Ring, algebraMap, toAlgebra
-/
lemma Hom.sub_aux (f g : Hom P P') (x y) :
    letI := ((algebraMap S S').comp (algebraMap P.Ring S)).toAlgebra
    f.toAlgHom (x * y) - g.toAlgHom (x * y) -
        (P'.σ ((algebraMap P.Ring S') x) * (f.toAlgHom y - g.toAlgHom y) +
          P'.σ ((algebraMap P.Ring S') y) * (f.toAlgHom x - g.toAlgHom x)) in
      P'.ker ^ 2 := by
  let := ((algebraMap S S').comp (algebraMap P.Ring S)).toAlgebra
  have :
      (f.toAlgHom x - P'.σ (algebraMap P.Ring S' x)) * (f.toAlgHom y - g.toAlgHom y) +
      (g.toAlgHom y - P'.σ (algebraMap P.Ring S' y)) * (f.toAlgHom x - g.toAlgHom x)
        in P'.ker ^ 2 := by
    rw [pow_two]
    refine Ideal.add_mem _ (Ideal.mul_mem_mul ?_ ?_) (Ideal.mul_mem_mul ?_ ?_) <;>
      simp only [RingHom.algebraMap_toAlgebra, RingHom.coe_comp,
        Function.comp_apply,
        ker, RingHom.mem_ker, map_sub, algebraMap_toRingHom,
        algebraMap_σ, sub_self, toAlgHom_apply]
  convert! this using 1
  simp only [map_mul]
  ring

/--
If `f` and `g` are two maps `P → P'` between presentations,
then the image of `f - g` is in the kernel of `P' → S`.
-/
@[simps! apply_coe]
/--
Definition of `Hom.subToKer` / `Hom.subToKer` 的定义

English:
definition Hom.subToKer
  signature: (f g : Hom P P')
  body: by
  refine ((f.toAlgHom.toLinearMap - g.toAlgHom.toLinearMap).codRestrict
    (P'.ker.restrictScalars R) ?_)
  intro x
  simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply, ker,
    Submodule.restrictScalars_mem, RingHom.mem_ker, map_sub, algebraMap_toRingHom,
    sub_self, toAlgHom_apply]

中文:
定义 态射.subToKer
  签名: (f g : 态射 P P')
  定义体: by
  refine ((f.toAlgHom.toLinearMap - g.toAlgHom.toLinearMap).codRestrict
    (P'.ker.restrictScalars R) ?_)
  intro x
  simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply, ker,
    Submodule.restrictScalars_mem, RingHom.mem_ker, map_sub, algebraMap_toRingHom,
    sub_self, toAlgHom_apply]

Depends on / 依赖: AlgHom, AlgHom.toLinearMap_apply, LinearMap, LinearMap.sub_apply, RingHom, RingHom.mem_ker, Submodule, Submodule.restrictScalars_mem, algebraMap_toRingHom, codRestrict, f.toAlgHom.toLinearMap, g.toAlgHom.toLinearMap, ker.restrictScalars, map_sub, mem_ker, restrictScalars, restrictScalars_mem, sub_apply, sub_self, toAlgHom
-/
def Hom.subToKer (f g : Hom P P') : P.Ring ->ₗ[R] P'.ker := by
  refine ((f.toAlgHom.toLinearMap - g.toAlgHom.toLinearMap).codRestrict
    (P'.ker.restrictScalars R) ?_)
  intro x
  simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply, ker,
    Submodule.restrictScalars_mem, RingHom.mem_ker, map_sub, algebraMap_toRingHom,
    sub_self, toAlgHom_apply]

variable [IsScalarTower R S S'] in
/--
Definition of `Hom.sub` / `Hom.sub` 的定义

English:
definition Hom.sub
  signature: (f g : Hom P P')
  body: by
  letI := ((algebraMap S S').comp (algebraMap P.Ring S)).toAlgebra
  haveI : IsScalarTower P.Ring S S' := IsScalarTower.of_algebraMap_eq' rfl
  letI := f.toAlgHom.toAlgebra
  haveI : IsScalarTower P.Ring P'.Ring S' :=
    IsScalarTower.of_algebraMap_eq fun x => (f.algebraMap_toRingHom x).symm
  haveI : IsScalarTower R P.Ring S' :=
    IsScalarTower.of_algebraMap_eq fun x =>
      show algebraMap R S' x = algebraMap S S' (algebraMap P.Ring S (algebraMap R P.Ring x)) by
        rw [← IsScalarTower.algebraMap_apply R P.Ring S]; rw [← IsScalarTower.algebraMap_apply]
  refine (Derivation.liftKaehlerDifferential ?_).liftBaseChange S
  refine
  { __ := Cotangent.mk.restrictScalars R ∘ₗ f.subToKer g
    map_one_eq_zero' := ?_
    leibniz' := ?_ }
  · ext
    simp [Ideal.toCotangent_eq_zero]
  · intro x y
    ext
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
      Cotangent.val_mk, Cotangent.val_add, Cotangent.val_smul''', ← map_smul, ← map_add,
      Ideal.toCotangent_eq]
    exact Hom.sub_aux f g x y

中文:
定义 态射.sub
  签名: (f g : 态射 P P')
  定义体: by
  letI := ((algebraMap S S').comp (algebraMap P.Ring S)).toAlgebra
  haveI : IsScalarTower P.Ring S S' := IsScalarTower.of_algebraMap_eq' rfl
  letI := f.toAlgHom.toAlgebra
  haveI : IsScalarTower P.Ring P'.Ring S' :=
    IsScalarTower.of_algebraMap_eq fun x => (f.algebraMap_toRingHom x).symm
  haveI : IsScalarTower R P.Ring S' :=
    IsScalarTower.of_algebraMap_eq fun x =>
      show algebraMap R S' x = algebraMap S S' (algebraMap P.Ring S (algebraMap R P.Ring x)) by
        rw [← IsScalarTower.algebraMap_apply R P.Ring S]; rw [← IsScalarTower.algebraMap_apply]
  refine (Derivation.liftKaehlerDifferential ?_).liftBaseChange S
  refine
  { __ := Cotangent.mk.restrictScalars R ∘ₗ f.subToKer g
    map_one_eq_zero' := ?_
    leibniz' := ?_ }
  · ext
    simp [Ideal.toCotangent_eq_zero]
  · intro x y
    ext
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
      Cotangent.val_mk, Cotangent.val_add, Cotangent.val_smul''', ← map_smul, ← map_add,
      Ideal.toCotangent_eq]
    exact Hom.sub_aux f g x y
-/
def Hom.sub (f g : Hom P P') : P.CotangentSpace ->ₗ[S] P'.Cotangent := by
  letI := ((algebraMap S S').comp (algebraMap P.Ring S)).toAlgebra
  haveI : IsScalarTower P.Ring S S' := IsScalarTower.of_algebraMap_eq' rfl
  letI := f.toAlgHom.toAlgebra
  haveI : IsScalarTower P.Ring P'.Ring S' :=
    IsScalarTower.of_algebraMap_eq fun x => (f.algebraMap_toRingHom x).symm
  haveI : IsScalarTower R P.Ring S' :=
    IsScalarTower.of_algebraMap_eq fun x =>
      show algebraMap R S' x = algebraMap S S' (algebraMap P.Ring S (algebraMap R P.Ring x)) by
        rw [← IsScalarTower.algebraMap_apply R P.Ring S]; rw [← IsScalarTower.algebraMap_apply]
  refine (Derivation.liftKaehlerDifferential ?_).liftBaseChange S
  refine
  { __ := Cotangent.mk.restrictScalars R ∘ₗ f.subToKer g
    map_one_eq_zero' := ?_
    leibniz' := ?_ }
  · ext
    simp [Ideal.toCotangent_eq_zero]
  · intro x y
    ext
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
      Cotangent.val_mk, Cotangent.val_add, Cotangent.val_smul''', ← map_smul, ← map_add,
      Ideal.toCotangent_eq]
    exact Hom.sub_aux f g x y

variable [IsScalarTower R S S']

/--
lemma `Hom.sub_one_tmul` / 引理 `Hom.sub_one_tmul`

English:
lemma Hom.sub_one_tmul
  given: (f g : Hom P P') (x)
  proof: by
  simp only [sub, LinearMap.liftBaseChange_tmul, Derivation.liftKaehlerDifferential_comp_D,
    Derivation.mk_coe, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
    one_smul]

@[simp]

中文:
引理 态射.sub_one_tmul
  条件: (f g : 态射 P P') (x)
  证明: by
  simp only [sub, LinearMap.liftBaseChange_tmul, Derivation.liftKaehlerDifferential_comp_D,
    Derivation.mk_coe, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
    one_smul]

@[simp]

Depends on / 依赖: Derivation, Derivation.liftKaehlerDifferential_comp_D, Derivation.mk_coe, Function, Function.comp_apply, LinearMap, LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearMap.liftBaseChange_tmul, coe_comp, coe_restrictScalars, comp_apply, liftBaseChange_tmul, liftKaehlerDifferential_comp_D, mk_coe, one_smul
-/
lemma Hom.sub_one_tmul (f g : Hom P P') (x) :
    f.sub g (1 otimesₜ .D _ _ x) = Cotangent.mk (f.subToKer g x) := by
  simp only [sub, LinearMap.liftBaseChange_tmul, Derivation.liftKaehlerDifferential_comp_D,
    Derivation.mk_coe, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
    one_smul]

@[simp]
/--
lemma `Hom.sub_tmul` / 引理 `Hom.sub_tmul`

English:
lemma Hom.sub_tmul
  given: (f g : Hom P P') (r x)
  proof: by
  simp only [sub, LinearMap.liftBaseChange_tmul, Derivation.liftKaehlerDifferential_comp_D,
    Derivation.mk_coe, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply]

中文:
引理 态射.sub_tmul
  条件: (f g : 态射 P P') (r x)
  证明: by
  simp only [sub, LinearMap.liftBaseChange_tmul, Derivation.liftKaehlerDifferential_comp_D,
    Derivation.mk_coe, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply]

Depends on / 依赖: Derivation, Derivation.liftKaehlerDifferential_comp_D, Derivation.mk_coe, Function, Function.comp_apply, LinearMap, LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearMap.liftBaseChange_tmul, coe_comp, coe_restrictScalars, comp_apply, liftBaseChange_tmul, liftKaehlerDifferential_comp_D, mk_coe
-/
lemma Hom.sub_tmul (f g : Hom P P') (r x) :
    f.sub g (r otimesₜ .D _ _ x) = r • Cotangent.mk (f.subToKer g x) := by
  simp only [sub, LinearMap.liftBaseChange_tmul, Derivation.liftKaehlerDifferential_comp_D,
    Derivation.mk_coe, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply]

/--
lemma `CotangentSpace.map_sub_map` / 引理 `CotangentSpace.map_sub_map`

English:
lemma CotangentSpace.map_sub_map
  given: (f g : Hom P P')
  proof: by
  ext x
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
  | add =>
    simp only [map_add, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply, *]
  | tmul x y =>
    obtain ⟨y, rfl⟩ := KaehlerDifferential.tensorProductTo_surjective _ _ y
    induction y with
    | zero => simp only [map_zero, tmul_zero]
    | add => simp only [map_add, tmul_add, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
      Function.comp_apply, *]
    | tmul =>
      simp only [Derivation.tensorProductTo_tmul, tmul_smul, smul_tmul', LinearMap.sub_apply,
        map_tmul, Hom.toAlgHom_apply, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
        Function.comp_apply, Hom.sub_tmul, LinearMap.map_smul_of_tower, cotangentComplex_mk,
        Hom.subToKer_apply_coe, map_sub, ← algebraMap_eq_smul_one, tmul_sub, smul_sub]

中文:
引理 CotangentSpace.map_sub_map
  条件: (f g : 态射 P P')
  证明: by
  ext x
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
  | add =>
    simp only [map_add, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply, *]
  | tmul x y =>
    obtain ⟨y, rfl⟩ := KaehlerDifferential.tensorProductTo_surjective _ _ y
    induction y with
    | zero => simp only [map_zero, tmul_zero]
    | add => simp only [map_add, tmul_add, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
      Function.comp_apply, *]
    | tmul =>
      simp only [Derivation.tensorProductTo_tmul, tmul_smul, smul_tmul', LinearMap.sub_apply,
        map_tmul, Hom.toAlgHom_apply, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
        Function.comp_apply, Hom.sub_tmul, LinearMap.map_smul_of_tower, cotangentComplex_mk,
        Hom.subToKer_apply_coe, map_sub, ← algebraMap_eq_smul_one, tmul_sub, smul_sub]

Depends on / 依赖: Derivation, Derivation.tensorProductTo, Function, Function.comp_apply, KaehlerDifferential, KaehlerDifferential.tensorProductTo_surjective, LinearMap, LinearMap.coe_comp, LinearMap.coe_restrictScalars, TensorProduct, TensorProduct.induction_on, coe_comp, coe_restrictScalars, comp_apply, induction_on, map_add, map_zero, tensorProductTo, tensorProductTo_surjective, tmul_add
-/
lemma CotangentSpace.map_sub_map (f g : Hom P P') :
    CotangentSpace.map f - CotangentSpace.map g =
      P'.cotangentComplex.restrictScalars S ∘ₗ (f.sub g) := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
  | add =>
    simp only [map_add, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply, *]
  | tmul x y =>
    obtain ⟨y, rfl⟩ := KaehlerDifferential.tensorProductTo_surjective _ _ y
    induction y with
    | zero => simp only [map_zero, tmul_zero]
    | add => simp only [map_add, tmul_add, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
      Function.comp_apply, *]
    | tmul =>
      simp only [Derivation.tensorProductTo_tmul, tmul_smul, smul_tmul', LinearMap.sub_apply,
        map_tmul, Hom.toAlgHom_apply, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
        Function.comp_apply, Hom.sub_tmul, LinearMap.map_smul_of_tower, cotangentComplex_mk,
        Hom.subToKer_apply_coe, map_sub, ← algebraMap_eq_smul_one, tmul_sub, smul_sub]

/--
lemma `Cotangent.map_sub_map` / 引理 `Cotangent.map_sub_map`

English:
lemma Cotangent.map_sub_map
  given: (f g : Hom P P')
  proof: by
  ext x
  obtain ⟨x, rfl⟩ := mk_surjective x
  simp only [LinearMap.sub_apply, map_mk, LinearMap.coe_comp, Function.comp_apply,
    cotangentComplex_mk, Hom.sub_tmul, one_smul, val_mk]
  apply (Ideal.cotangentEquivIdeal _).injective
  ext
  simp only [val_sub, val_mk, map_sub, AddSubgroupClass.coe_sub, Ideal.cotangentEquivIdeal_apply,
    Ideal.toCotangent_to_quotient_square, Submodule.mkQ_apply, Ideal.Quotient.mk_eq_mk,
    Hom.subToKer_apply_coe, Hom.toAlgHom_apply]

中文:
引理 余切.map_sub_map
  条件: (f g : 态射 P P')
  证明: by
  ext x
  obtain ⟨x, rfl⟩ := mk_surjective x
  simp only [LinearMap.sub_apply, map_mk, LinearMap.coe_comp, Function.comp_apply,
    cotangentComplex_mk, Hom.sub_tmul, one_smul, val_mk]
  apply (Ideal.cotangentEquivIdeal _).injective
  ext
  simp only [val_sub, val_mk, map_sub, AddSubgroupClass.coe_sub, Ideal.cotangentEquivIdeal_apply,
    Ideal.toCotangent_to_quotient_square, Submodule.mkQ_apply, Ideal.Quotient.mk_eq_mk,
    Hom.subToKer_apply_coe, Hom.toAlgHom_apply]

Depends on / 依赖: AddSubgroupClass, AddSubgroupClass.coe_sub, Function, Function.comp_apply, Hom.subToKer_apply_coe, Hom.sub_tmul, Hom.toAlgHom_apply, Ideal.Quotient.mk_eq_mk, Ideal.cotangentEquivIdeal, Ideal.cotangentEquivIdeal_apply, Ideal.toCotangent_to_quotient_square, LinearMap, LinearMap.coe_comp, LinearMap.sub_apply, Quotient, Submodule, Submodule.mkQ_apply, coe_comp, coe_sub, comp_apply
-/
lemma Cotangent.map_sub_map (f g : Hom P P') :
    map f - map g = (f.sub g) ∘ₗ P.cotangentComplex := by
  ext x
  obtain ⟨x, rfl⟩ := mk_surjective x
  simp only [LinearMap.sub_apply, map_mk, LinearMap.coe_comp, Function.comp_apply,
    cotangentComplex_mk, Hom.sub_tmul, one_smul, val_mk]
  apply (Ideal.cotangentEquivIdeal _).injective
  ext
  simp only [val_sub, val_mk, map_sub, AddSubgroupClass.coe_sub, Ideal.cotangentEquivIdeal_apply,
    Ideal.toCotangent_to_quotient_square, Submodule.mkQ_apply, Ideal.Quotient.mk_eq_mk,
    Hom.subToKer_apply_coe, Hom.toAlgHom_apply]

variable (P) in
/--
Definition of `toKaehler` / `toKaehler` 的定义

English:
abbreviation toKaehler
  signature: : P.CotangentSpace ->ₗ[S] Ω[S⁄R]
  body: mapBaseChange _ _ _

中文:
缩写 toKaehler
  签名: : P.CotangentSpace ->ₗ[S] Ω[S⁄R]
  定义体: mapBaseChange _ _ _

Depends on / 依赖: mapBaseChange
-/
abbrev toKaehler : P.CotangentSpace ->ₗ[S] Ω[S⁄R] := mapBaseChange _ _ _

/--
lemma `toKaehler_surjective` / 引理 `toKaehler_surjective`

English:
lemma toKaehler_surjective
  statement: Function.Surjective P.toKaehler
  proof: mapBaseChange_surjective _ _ _ P.algebraMap_surjective

中文:
引理 toKaehler_surjective
  结论: 函数.满射 P.toKaehler
  证明: mapBaseChange_surjective _ _ _ P.algebraMap_surjective

Depends on / 依赖: P.algebraMap_surjective, algebraMap_surjective, mapBaseChange_surjective
-/
lemma toKaehler_surjective : Function.Surjective P.toKaehler :=
  mapBaseChange_surjective _ _ _ P.algebraMap_surjective

/--
lemma `exact_cotangentComplex_toKaehler` / 引理 `exact_cotangentComplex_toKaehler`

English:
lemma exact_cotangentComplex_toKaehler
  statement: Function.Exact P.cotangentComplex P.toKaehler
  proof: exact_kerCotangentToTensor_mapBaseChange _ _ _ P.algebraMap_surjective

中文:
引理 exact_cotangentComplex_toKaehler
  结论: 函数.正合 P.cotangentComplex P.toKaehler
  证明: exact_kerCotangentToTensor_mapBaseChange _ _ _ P.algebraMap_surjective

Depends on / 依赖: P.algebraMap_surjective, algebraMap_surjective, exact_kerCotangentToTensor_mapBaseChange
-/
lemma exact_cotangentComplex_toKaehler : Function.Exact P.cotangentComplex P.toKaehler :=
  exact_kerCotangentToTensor_mapBaseChange _ _ _ P.algebraMap_surjective

variable (P) in
/--
Definition of `H1Cotangent` / `H1Cotangent` 的定义

English:
definition H1Cotangent
  signature: : Type _
  body: LinearMap.ker P.cotangentComplex

中文:
定义 H1Cotangent
  签名: : 类型 _
  定义体: LinearMap.ker P.cotangentComplex
-/
protected def H1Cotangent : Type _ := LinearMap.ker P.cotangentComplex

-- The `SMul` instance exists to avoid a zsmul diamond.
variable {R₀} [CommRing R₀] [Algebra R₀ S] [Module R₀ P.Cotangent]
  [IsScalarTower R₀ S P.Cotangent] in
deriving instance SMul R₀, AddCommGroup, Module R₀ for (P).H1Cotangent

/--
lemma `H1Cotangent.val_add` / 引理 `H1Cotangent.val_add`

English:
lemma H1Cotangent.val_add
  given: (x y : P.H1Cotangent)
  statement: (x + y).1 = x.1 + y.1
  proof: rfl

中文:
引理 H1Cotangent.val_add
  条件: (x y : P.H1Cotangent)
  结论: (x + y).1 = x.1 + y.1
  证明: rfl
-/
@[simp] lemma H1Cotangent.val_add (x y : P.H1Cotangent) : (x + y).1 = x.1 + y.1 := rfl
/--
lemma `H1Cotangent.val_zero` / 引理 `H1Cotangent.val_zero`

English:
lemma H1Cotangent.val_zero
  statement: (0 : P.H1Cotangent).1 = 0
  proof: rfl

中文:
引理 H1Cotangent.val_zero
  结论: (0 : P.H1Cotangent).1 = 0
  证明: rfl
-/
@[simp] lemma H1Cotangent.val_zero : (0 : P.H1Cotangent).1 = 0 := rfl
/--
lemma `H1Cotangent.val_smul` / 引理 `H1Cotangent.val_smul`

English:
lemma H1Cotangent.val_smul
  statement: {R₀} [CommRing R₀] [Algebra R₀ S] [Module R₀ P.Cotangent]
  proof: rfl

中文:
引理 H1Cotangent.val_smul
  结论: {R₀} [交换环 R₀] [代数 R₀ S] [模 R₀ P.余切]
  证明: rfl
-/
@[simp] lemma H1Cotangent.val_smul {R₀} [CommRing R₀] [Algebra R₀ S] [Module R₀ P.Cotangent]
    [IsScalarTower R₀ S P.Cotangent] (r : R₀) (x : P.H1Cotangent) : (r • x).1 = r • x.1 := rfl

instance {R₁ R₂} [CommRing R₁] [CommRing R₂] [Algebra R₁ R₂]
    [Algebra R₁ S] [Algebra R₂ S]
    [Module R₁ P.Cotangent] [IsScalarTower R₁ S P.Cotangent]
    [Module R₂ P.Cotangent] [IsScalarTower R₂ S P.Cotangent]
    [IsScalarTower R₁ R₂ P.Cotangent] :
    IsScalarTower R₁ R₂ P.H1Cotangent :=
inferInstanceAs IsScalarTower R₁ R₂ (LinearMap.ker _)

/--
lemma `subsingleton_h1Cotangent` / 引理 `subsingleton_h1Cotangent`

English:
lemma subsingleton_h1Cotangent
  given: (P : Extension R S)
  proof: by
  delta Extension.H1Cotangent
  rw [← LinearMap.ker_eq_bot]; rw [Submodule.eq_bot_iff]; rw [subsingleton_iff_forall_eq 0]; rw [Subtype.forall']
  simp only [Subtype.ext_iff, Submodule.coe_zero]

中文:
引理 subsingleton_h1Cotangent
  条件: (P : 扩张 R S)
  证明: by
  delta Extension.H1Cotangent
  rw [← LinearMap.ker_eq_bot]; rw [Submodule.eq_bot_iff]; rw [subsingleton_iff_forall_eq 0]; rw [Subtype.forall']
  simp only [Subtype.ext_iff, Submodule.coe_zero]

Depends on / 依赖: Extension, Extension.H1Cotangent, H1Cotangent, LinearMap, LinearMap.ker_eq_bot, Submodule, Submodule.coe_zero, Submodule.eq_bot_iff, Subtype, Subtype.ext_iff, Subtype.forall, coe_zero, eq_bot_iff, ext_iff, ker_eq_bot, proxy_equiv, subsingleton_iff_forall_eq
-/
lemma subsingleton_h1Cotangent (P : Extension R S) :
    Subsingleton P.H1Cotangent ↔ Function.Injective P.cotangentComplex := by
  delta Extension.H1Cotangent
  rw [← LinearMap.ker_eq_bot]; rw [Submodule.eq_bot_iff]; rw [subsingleton_iff_forall_eq 0]; rw [Subtype.forall']
  simp only [Subtype.ext_iff, Submodule.coe_zero]

/--
Definition of `h1Cotangentι` / `h1Cotangentι` 的定义

English:
definition h1Cotangentι
  signature: : P.H1Cotangent ->ₗ[S] P.Cotangent
  body: Submodule.subtype _

中文:
定义 h1Cotangentι
  签名: : P.H1Cotangent ->ₗ[S] P.余切
  定义体: Submodule.subtype _
-/
@[simps!] noncomputable def h1Cotangentι : P.H1Cotangent ->ₗ[S] P.Cotangent := Submodule.subtype _

/--
lemma `h1Cotangentι_injective` / 引理 `h1Cotangentι_injective`

English:
lemma h1Cotangentι_injective
  statement: Function.Injective P.h1Cotangentι
  proof: Subtype.val_injective

中文:
引理 h1Cotangentι_injective
  结论: 函数.单射 P.h1Cotangentι
  证明: Subtype.val_injective

Depends on / 依赖: Subtype, Subtype.val_injective, val_injective
-/
lemma h1Cotangentι_injective : Function.Injective P.h1Cotangentι := Subtype.val_injective

/--
lemma `h1Cotangentι_ext` / 引理 `h1Cotangentι_ext`

English:
lemma h1Cotangentι_ext
  given: (x y : P.H1Cotangent) (e : x.1 = y.1)
  statement: x = y
  proof: Subtype.ext e

中文:
引理 h1Cotangentι_ext
  条件: (x y : P.H1Cotangent) (e : x.1 = y.1)
  结论: x = y
  证明: Subtype.ext e
-/
@[ext] lemma h1Cotangentι_ext (x y : P.H1Cotangent) (e : x.1 = y.1) : x = y := Subtype.ext e

/--
lemma `exact_hCotangentι_cotangentComplex` / 引理 `exact_hCotangentι_cotangentComplex`

English:
lemma exact_hCotangentι_cotangentComplex
  statement: Function.Exact h1Cotangentι P.cotangentComplex
  proof: by
  rw [LinearMap.exact_iff]
  exact (Submodule.range_subtype _).symm

中文:
引理 exact_hCotangentι_cotangentComplex
  结论: 函数.正合 h1Cotangentι P.cotangentComplex
  证明: by
  rw [LinearMap.exact_iff]
  exact (Submodule.range_subtype _).symm

Depends on / 依赖: LinearMap, LinearMap.exact_iff, Submodule, Submodule.range_subtype, exact_iff, range_subtype
-/
lemma exact_hCotangentι_cotangentComplex : Function.Exact h1Cotangentι P.cotangentComplex := by
  rw [LinearMap.exact_iff]
  exact (Submodule.range_subtype _).symm

/--
The induced map on the first homology of the (naive) cotangent complex.
-/
@[simps!]
/--
Definition of `H1Cotangent.map` / `H1Cotangent.map` 的定义

English:
definition H1Cotangent.map
  signature: (f : Hom P P')
  body: by
  refine (Cotangent.map f).restrict (p := LinearMap.ker P.cotangentComplex)
    (q := (LinearMap.ker P'.cotangentComplex).restrictScalars S) fun x hx => ?_
  simp only [LinearMap.mem_ker, Submodule.restrictScalars_mem] at hx ⊢
  apply_fun (CotangentSpace.map f) at hx
  rw [CotangentSpace.map_cotangentComplex] at hx
  rw [hx]
  exact LinearMap.map_zero _

中文:
定义 H1Cotangent.map
  签名: (f : 态射 P P')
  定义体: by
  refine (Cotangent.map f).restrict (p := LinearMap.ker P.cotangentComplex)
    (q := (LinearMap.ker P'.cotangentComplex).restrictScalars S) fun x hx => ?_
  simp only [LinearMap.mem_ker, Submodule.restrictScalars_mem] at hx ⊢
  apply_fun (CotangentSpace.map f) at hx
  rw [CotangentSpace.map_cotangentComplex] at hx
  rw [hx]
  exact LinearMap.map_zero _

Depends on / 依赖: Cotangent, Cotangent.map, CotangentSpace, CotangentSpace.map, CotangentSpace.map_cotangentComplex, LinearMap, LinearMap.ker, LinearMap.map_zero, LinearMap.mem_ker, P.cotangentComplex, Submodule, Submodule.restrictScalars_mem, apply_fun, cotangentComplex, map_cotangentComplex, map_zero, mem_ker, restrict, restrictScalars, restrictScalars_mem
-/
def H1Cotangent.map (f : Hom P P') : P.H1Cotangent ->ₗ[S] P'.H1Cotangent := by
  refine (Cotangent.map f).restrict (p := LinearMap.ker P.cotangentComplex)
    (q := (LinearMap.ker P'.cotangentComplex).restrictScalars S) fun x hx => ?_
  simp only [LinearMap.mem_ker, Submodule.restrictScalars_mem] at hx ⊢
  apply_fun (CotangentSpace.map f) at hx
  rw [CotangentSpace.map_cotangentComplex] at hx
  rw [hx]
  exact LinearMap.map_zero _

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `H1Cotangent.map_eq` / 引理 `H1Cotangent.map_eq`

English:
lemma H1Cotangent.map_eq
  given: (f g : Hom P P')
  statement: map f = map g
  proof: by
  ext x
  simp only [map_apply_coe]
  rw [← sub_eq_zero]; rw [← Cotangent.val_sub]; rw [← LinearMap.sub_apply]; rw [Cotangent.map_sub_map]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.map_coe_ker, map_zero,
    Cotangent.val_zero]

中文:
引理 H1Cotangent.map_eq
  条件: (f g : 态射 P P')
  结论: map f = map g
  证明: by
  ext x
  simp only [map_apply_coe]
  rw [← sub_eq_zero]; rw [← Cotangent.val_sub]; rw [← LinearMap.sub_apply]; rw [Cotangent.map_sub_map]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.map_coe_ker, map_zero,
    Cotangent.val_zero]

Depends on / 依赖: Cotangent, Cotangent.map_sub_map, Cotangent.val_sub, Cotangent.val_zero, Function, Function.comp_apply, LinearMap, LinearMap.coe_comp, LinearMap.map_coe_ker, LinearMap.sub_apply, coe_comp, comp_apply, map_apply_coe, map_coe_ker, map_sub_map, map_zero, sub_apply, sub_eq_zero, val_sub, val_zero
-/
lemma H1Cotangent.map_eq (f g : Hom P P') : map f = map g := by
  ext x
  simp only [map_apply_coe]
  rw [← sub_eq_zero]; rw [← Cotangent.val_sub]; rw [← LinearMap.sub_apply]; rw [Cotangent.map_sub_map]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.map_coe_ker, map_zero,
    Cotangent.val_zero]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `H1Cotangent.map_id` / 引理 `H1Cotangent.map_id`

English:
lemma H1Cotangent.map_id
  statement: map (.id P) = LinearMap.id
  proof: by ext; simp

中文:
引理 H1Cotangent.map_id
  结论: map (.id P) = 线性映射.id
  证明: by ext; simp
-/
@[simp] lemma H1Cotangent.map_id : map (.id P) = LinearMap.id := by ext; simp

set_option backward.isDefEq.respectTransparency.types false in
omit [IsScalarTower R S S'] in
/--
lemma `H1Cotangent.map_comp` / 引理 `H1Cotangent.map_comp`

English:
lemma H1Cotangent.map_comp
  proof: by
  ext; simp [Cotangent.map_comp]

omit [IsScalarTower R S S'] in
@[simp]

中文:
引理 H1Cotangent.map_comp
  证明: by
  ext; simp [Cotangent.map_comp]

omit [IsScalarTower R S S'] in
@[simp]

Depends on / 依赖: Cotangent, Cotangent.map_comp, map_comp
-/
lemma H1Cotangent.map_comp
    (f : Hom P P') (g : Hom P' P'') :
    map (g.comp f) = (map g).restrictScalars S ∘ₗ map f := by
  ext; simp [Cotangent.map_comp]

omit [IsScalarTower R S S'] in
@[simp]
/--
lemma `H1Cotangent.map_comp_apply` / 引理 `H1Cotangent.map_comp_apply`

English:
lemma H1Cotangent.map_comp_apply
  given: (f : Hom P P') (g : Hom P' P'') (x : P.H1Cotangent)
  proof: congr($(H1Cotangent.map_comp f g) x)

中文:
引理 H1Cotangent.map_comp_apply
  条件: (f : 态射 P P') (g : 态射 P' P'') (x : P.H1Cotangent)
  证明: congr($(H1Cotangent.map_comp f g) x)

Depends on / 依赖: H1Cotangent, H1Cotangent.map_comp, map_comp
-/
lemma H1Cotangent.map_comp_apply (f : Hom P P') (g : Hom P' P'') (x : P.H1Cotangent) :
    map (g.comp f) x = map g (map f x) :=
  congr($(H1Cotangent.map_comp f g) x)

/-- Maps `P₁ → P₂` and `P₂ → P₁` between extensions
induce an isomorphism between `H¹(L_P₁)` and `H¹(L_P₂)`. -/
@[simps! apply]
/--
Definition of `H1Cotangent.equiv` / `H1Cotangent.equiv` 的定义

English:
definition H1Cotangent.equiv
  signature: {P₁ P₂ : Extension R S} (f₁ : P₁.Hom P₂) (f₂ : P₂.Hom P₁)
  body: map f₁
  invFun := map f₂
  left_inv x :=
    show (map f₂ ∘ₗ map f₁) x = LinearMap.id (R := S) x by
    rw [← Extension.H1Cotangent.map_id]; rw [eq_comm]; rw [map_eq _ (f₂.comp f₁)]; rw [Extension.H1Cotangent.map_comp]; rfl
  right_inv x :=
    show (map f₁ ∘ₗ map f₂) x = LinearMap.id (R := S) x by
    rw [← Extension.H1Cotangent.map_id]; rw [eq_comm]; rw [map_eq _ (f₁.comp f₂)]; rw [Extension.H1Cotangent.map_comp]; rfl

omit [IsScalarTower R S S'] in

中文:
定义 H1Cotangent.equiv
  签名: {P₁ P₂ : 扩张 R S} (f₁ : P₁.态射 P₂) (f₂ : P₂.态射 P₁)
  定义体: map f₁
  invFun := map f₂
  left_inv x :=
    show (map f₂ ∘ₗ map f₁) x = LinearMap.id (R := S) x by
    rw [← Extension.H1Cotangent.map_id]; rw [eq_comm]; rw [map_eq _ (f₂.comp f₁)]; rw [Extension.H1Cotangent.map_comp]; rfl
  right_inv x :=
    show (map f₁ ∘ₗ map f₂) x = LinearMap.id (R := S) x by
    rw [← Extension.H1Cotangent.map_id]; rw [eq_comm]; rw [map_eq _ (f₁.comp f₂)]; rw [Extension.H1Cotangent.map_comp]; rfl

omit [IsScalarTower R S S'] in
-/
def H1Cotangent.equiv {P₁ P₂ : Extension R S} (f₁ : P₁.Hom P₂) (f₂ : P₂.Hom P₁) :
    P₁.H1Cotangent ≃ₗ[S] P₂.H1Cotangent where
  __ := map f₁
  invFun := map f₂
  left_inv x :=
    show (map f₂ ∘ₗ map f₁) x = LinearMap.id (R := S) x by
    rw [← Extension.H1Cotangent.map_id]; rw [eq_comm]; rw [map_eq _ (f₂.comp f₁)]; rw [Extension.H1Cotangent.map_comp]; rfl
  right_inv x :=
    show (map f₁ ∘ₗ map f₂) x = LinearMap.id (R := S) x by
    rw [← Extension.H1Cotangent.map_id]; rw [eq_comm]; rw [map_eq _ (f₁.comp f₂)]; rw [Extension.H1Cotangent.map_comp]; rfl

omit [IsScalarTower R S S'] in
/--
lemma `Cotangent.map_comp_h1Cotangentι` / 引理 `Cotangent.map_comp_h1Cotangentι`

English:
lemma Cotangent.map_comp_h1Cotangentι
  given: (f : P.Hom P')
  proof: rfl

中文:
引理 余切.map_comp_h1Cotangentι
  条件: (f : P.态射 P')
  证明: rfl
-/
lemma Cotangent.map_comp_h1Cotangentι (f : P.Hom P') :
    Cotangent.map f ∘ₗ P.h1Cotangentι =
      P'.h1Cotangentι.restrictScalars S ∘ₗ H1Cotangent.map f := rfl

end Extension

namespace Generators

variable {ι : Type w} (P : Generators R S ι)

/--
Definition of `cotangentSpaceBasis` / `cotangentSpaceBasis` 的定义

English:
definition cotangentSpaceBasis
  signature: : Basis ι S P.toExtension.CotangentSpace
  body: (mvPolynomialBasis _ _).baseChange (R := P.Ring) _

中文:
定义 cotangentSpaceBasis
  签名: : 基 ι S P.toExtension.CotangentSpace
  定义体: (mvPolynomialBasis _ _).baseChange (R := P.Ring) _

Depends on / 依赖: P.Ring, baseChange, mvPolynomialBasis
-/
def cotangentSpaceBasis : Basis ι S P.toExtension.CotangentSpace :=
  (mvPolynomialBasis _ _).baseChange (R := P.Ring) _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `cotangentSpaceBasis_repr_tmul` / 引理 `cotangentSpaceBasis_repr_tmul`

English:
lemma cotangentSpaceBasis_repr_tmul
  given: (r x i)
  proof: by
  simp only [cotangentSpaceBasis, Basis.baseChange_repr_tmul, mvPolynomialBasis_repr_apply,
    Algebra.smul_def, mul_comm r, algebraMap_apply, toExtension]

中文:
引理 cotangentSpaceBasis_repr_tmul
  条件: (r x i)
  证明: by
  simp only [cotangentSpaceBasis, Basis.baseChange_repr_tmul, mvPolynomialBasis_repr_apply,
    Algebra.smul_def, mul_comm r, algebraMap_apply, toExtension]

Depends on / 依赖: Algebra, Algebra.smul_def, Basis.baseChange_repr_tmul, algebraMap_apply, baseChange_repr_tmul, cotangentSpaceBasis, mul_comm, mvPolynomialBasis_repr_apply, smul_def, toExtension
-/
lemma cotangentSpaceBasis_repr_tmul (r x i) :
    P.cotangentSpaceBasis.repr (r otimesₜ[P.Ring] KaehlerDifferential.D R P.Ring x : _) i =
      r * aeval P.val (pderiv i x) := by
  simp only [cotangentSpaceBasis, Basis.baseChange_repr_tmul, mvPolynomialBasis_repr_apply,
    Algebra.smul_def, mul_comm r, algebraMap_apply, toExtension]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `cotangentSpaceBasis_repr_one_tmul` / 引理 `cotangentSpaceBasis_repr_one_tmul`

English:
lemma cotangentSpaceBasis_repr_one_tmul
  given: (x i)
  proof: by
  simp

中文:
引理 cotangentSpaceBasis_repr_one_tmul
  条件: (x i)
  证明: by
  simp
-/
lemma cotangentSpaceBasis_repr_one_tmul (x i) :
    P.cotangentSpaceBasis.repr (1 otimesₜ .D _ _ x) i = aeval P.val (pderiv i x) := by
  simp

set_option backward.isDefEq.respectTransparency false in
/--
lemma `cotangentSpaceBasis_apply` / 引理 `cotangentSpaceBasis_apply`

English:
lemma cotangentSpaceBasis_apply
  given: (i)
  proof: by
  simp [cotangentSpaceBasis, toExtension]

中文:
引理 cotangentSpaceBasis_apply
  条件: (i)
  证明: by
  simp [cotangentSpaceBasis, toExtension]

Depends on / 依赖: cotangentSpaceBasis, toExtension
-/
lemma cotangentSpaceBasis_apply (i) :
    P.cotangentSpaceBasis i = ((1 : S) otimesₜ[P.Ring] D R P.Ring (.X i) :) := by
  simp [cotangentSpaceBasis, toExtension]

instance (P : Generators R S ι) : Module.Free S P.toExtension.CotangentSpace :=
  .of_basis P.cotangentSpaceBasis

/--
Definition of `cotangentRestrict` / `cotangentRestrict` 的定义

English:
definition cotangentRestrict
  signature: {σ : Type*} {u : σ -> ι} (hu : Function.Injective u)
  body: Finsupp.lcomapDomain u hu ∘ₗ P.cotangentSpaceBasis.repr.toLinearMap ∘ₗ
    P.toExtension.cotangentComplex

中文:
定义 cotangentRestrict
  签名: {σ : 类型} {u : σ -> ι} (hu : 函数.单射 u)
  定义体: Finsupp.lcomapDomain u hu ∘ₗ P.cotangentSpaceBasis.repr.toLinearMap ∘ₗ
    P.toExtension.cotangentComplex

Depends on / 依赖: Finsupp, Finsupp.lcomapDomain, P.cotangentSpaceBasis.repr.toLinearMap, P.toExtension.cotangentComplex, cotangentComplex, cotangentSpaceBasis, lcomapDomain, toExtension, toLinearMap
-/
def cotangentRestrict {σ : Type*} {u : σ -> ι} (hu : Function.Injective u) :
    P.toExtension.Cotangent ->ₗ[S] (σ ->₀ S) :=
  Finsupp.lcomapDomain u hu ∘ₗ P.cotangentSpaceBasis.repr.toLinearMap ∘ₗ
    P.toExtension.cotangentComplex

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `cotangentRestrict_mk` / 引理 `cotangentRestrict_mk`

English:
lemma cotangentRestrict_mk
  given: {σ : Type*} {u : σ -> ι} (hu : Function.Injective u) (x : P.ker)
  proof: by
  ext j
  simp only [cotangentRestrict, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Finsupp.lcomapDomain_apply, Finsupp.comapDomain_apply, Extension.cotangentComplex_mk]
  simp only [toExtension_Ring, P.cotangentSpaceBasis_repr_tmul, one_mul]

universe w' u' v'

中文:
引理 cotangentRestrict_mk
  条件: {σ : 类型} {u : σ -> ι} (hu : 函数.单射 u) (x : P.ker)
  证明: by
  ext j
  simp only [cotangentRestrict, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Finsupp.lcomapDomain_apply, Finsupp.comapDomain_apply, Extension.cotangentComplex_mk]
  simp only [toExtension_Ring, P.cotangentSpaceBasis_repr_tmul, one_mul]

universe w' u' v'

Depends on / 依赖: Extension, Extension.cotangentComplex_mk, Finsupp, Finsupp.comapDomain_apply, Finsupp.lcomapDomain_apply, Function, Function.comp_apply, LinearEquiv, LinearEquiv.coe_coe, LinearMap, LinearMap.coe_comp, P.cotangentSpaceBasis_repr_tmul, coe_coe, coe_comp, comapDomain_apply, comp_apply, cotangentComplex_mk, cotangentRestrict, cotangentSpaceBasis_repr_tmul, lcomapDomain_apply
-/
lemma cotangentRestrict_mk {σ : Type*} {u : σ -> ι} (hu : Function.Injective u) (x : P.ker) :
    cotangentRestrict P hu (Extension.Cotangent.mk x) =
fun j => (aeval P.val) pderiv (u j) x.val := by
  ext j
  simp only [cotangentRestrict, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Finsupp.lcomapDomain_apply, Finsupp.comapDomain_apply, Extension.cotangentComplex_mk]
  simp only [toExtension_Ring, P.cotangentSpaceBasis_repr_tmul, one_mul]

universe w' u' v'

variable {R' : Type u'} {S' : Type v'} {ι' : Type w'} [CommRing R'] [CommRing S'] [Algebra R' S']
variable (P' : Generators R' S' ι')
variable [Algebra R R'] [Algebra S S'] [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']

attribute [local instance] SMulCommClass.of_commMonoid

variable {P P'}

universe w'' u'' v''

variable {R'' : Type u''} {S'' : Type v''} {ι'' : Type w''}
  [CommRing R''] [CommRing S''] [Algebra R'' S''] {P'' : Generators R'' S'' ι''}
variable [Algebra R R''] [Algebra S S''] [Algebra R S'']
  [IsScalarTower R R'' S''] [IsScalarTower R S S'']
variable [Algebra R' R''] [Algebra S' S''] [Algebra R' S'']
  [IsScalarTower R' R'' S''] [IsScalarTower R' S' S'']
variable [IsScalarTower S S' S'']

open Extension

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `repr_CotangentSpaceMap` / 引理 `repr_CotangentSpaceMap`

English:
lemma repr_CotangentSpaceMap
  given: (f : Hom P P') (i j)
  proof: by
  rw [cotangentSpaceBasis_apply]
  simp only [toExtension]
  rw [CotangentSpace.map_tmul]; rw [map_one]
  erw [cotangentSpaceBasis_repr_one_tmul, Hom.toAlgHom_X]

中文:
引理 repr_CotangentSpaceMap
  条件: (f : 态射 P P') (i j)
  证明: by
  rw [cotangentSpaceBasis_apply]
  simp only [toExtension]
  rw [CotangentSpace.map_tmul]; rw [map_one]
  erw [cotangentSpaceBasis_repr_one_tmul, Hom.toAlgHom_X]

Depends on / 依赖: CotangentSpace, CotangentSpace.map_tmul, Hom.toAlgHom_X, cotangentSpaceBasis_apply, cotangentSpaceBasis_repr_one_tmul, map_one, map_tmul, toAlgHom_X, toExtension
-/
lemma repr_CotangentSpaceMap (f : Hom P P') (i j) :
    P'.cotangentSpaceBasis.repr (CotangentSpace.map f.toExtensionHom (P.cotangentSpaceBasis i)) j =
      aeval P'.val (pderiv j (f.val i)) := by
  rw [cotangentSpaceBasis_apply]
  simp only [toExtension]
  rw [CotangentSpace.map_tmul]; rw [map_one]
  erw [cotangentSpaceBasis_repr_one_tmul, Hom.toAlgHom_X]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `toKaehler_tmul_D` / 引理 `toKaehler_tmul_D`

English:
lemma toKaehler_tmul_D
  given: (i)
  proof: (KaehlerDifferential.mapBaseChange_tmul ..).trans (by simp)

@[simp]

中文:
引理 toKaehler_tmul_D
  条件: (i)
  证明: (KaehlerDifferential.mapBaseChange_tmul ..).trans (by simp)

@[simp]

Depends on / 依赖: KaehlerDifferential, KaehlerDifferential.mapBaseChange_tmul, mapBaseChange_tmul
-/
lemma toKaehler_tmul_D (i) :
    P.toExtension.toKaehler (1 otimesₜ D R P.Ring (X i)) = D _ _ (P.val i) :=
  (KaehlerDifferential.mapBaseChange_tmul ..).trans (by simp)

@[simp]
/--
lemma `toKaehler_cotangentSpaceBasis` / 引理 `toKaehler_cotangentSpaceBasis`

English:
lemma toKaehler_cotangentSpaceBasis
  given: (i)
  proof: by
  rw [cotangentSpaceBasis_apply]
  exact toKaehler_tmul_D i

中文:
引理 toKaehler_cotangentSpaceBasis
  条件: (i)
  证明: by
  rw [cotangentSpaceBasis_apply]
  exact toKaehler_tmul_D i

Depends on / 依赖: cotangentSpaceBasis_apply, toKaehler_tmul_D
-/
lemma toKaehler_cotangentSpaceBasis (i) :
    P.toExtension.toKaehler (P.cotangentSpaceBasis i) = D R S (P.val i) := by
  rw [cotangentSpaceBasis_apply]
  exact toKaehler_tmul_D i

end Generators

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- TODO: should infer_instance be considered normalising?
set_option linter.flexible false in
-- TODO: generalize to essentially of finite presentation algebras
open KaehlerDifferential in
attribute [local instance] Module.finitePresentation_of_projective in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Algebra.FinitePresentation
  signature: R S] : Module.FinitePresentation S Ω[S⁄R]
  body: by
  let P := Algebra.Presentation.ofFinitePresentation R S
  have : Algebra.FiniteType R P.toExtension.Ring := by simp [P]; infer_instance
  refine Module.finitePresentation_of_surjective _ P.toExtension.toKaehler_surjective ?_
  rw [LinearMap.exact_iff.mp P.toExtension.exact_cotangentComplex_toKaehler]; rw [← Submodule.map_top]
  exact (Extension.Cotangent.finite P.fg_ker).1.map P.toExtension.cotangentComplex

中文:
实例 [代数.有限呈现
  签名: R S] : 模.有限呈现 S Ω[S⁄R]
  定义体: by
  let P := Algebra.Presentation.ofFinitePresentation R S
  have : Algebra.FiniteType R P.toExtension.Ring := by simp [P]; infer_instance
  refine Module.finitePresentation_of_surjective _ P.toExtension.toKaehler_surjective ?_
  rw [LinearMap.exact_iff.mp P.toExtension.exact_cotangentComplex_toKaehler]; rw [← Submodule.map_top]
  exact (Extension.Cotangent.finite P.fg_ker).1.map P.toExtension.cotangentComplex

Depends on / 依赖: Algebra, Algebra.FiniteType, Algebra.Presentation.ofFinitePresentation, Cotangent, Extension, Extension.Cotangent.finite, FiniteType, LinearMap, LinearMap.exact_iff.mp, Module, Module.finitePresentation_of_surjective, P.fg_ker, P.toExtension.Ring, P.toExtension.cotangentComplex, P.toExtension.exact_cotangentComplex_toKaehler, P.toExtension.toKaehler_surjective, Presentation, Submodule, Submodule.map_top, cotangentComplex
-/
instance [Algebra.FinitePresentation R S] : Module.FinitePresentation S Ω[S⁄R] := by
  let P := Algebra.Presentation.ofFinitePresentation R S
  have : Algebra.FiniteType R P.toExtension.Ring := by simp [P]; infer_instance
  refine Module.finitePresentation_of_surjective _ P.toExtension.toKaehler_surjective ?_
  rw [LinearMap.exact_iff.mp P.toExtension.exact_cotangentComplex_toKaehler]; rw [← Submodule.map_top]
  exact (Extension.Cotangent.finite P.fg_ker).1.map P.toExtension.cotangentComplex

variable {ι : Type w} {ι' : Type*} {P : Generators R S ι}

open Extension.H1Cotangent in
/-- `H¹(L_{S/R})` is independent of the presentation chosen. -/
@[simps! apply]
/--
Definition of `Generators.H1Cotangent.equiv` / `Generators.H1Cotangent.equiv` 的定义

English:
definition Generators.H1Cotangent.equiv
  signature: (P : Generators R S ι) (P' : Generators R S ι')
  body: Extension.H1Cotangent.equiv
    (Generators.defaultHom P P').toExtensionHom (Generators.defaultHom P' P).toExtensionHom

中文:
定义 生成元.H1Cotangent.equiv
  签名: (P : 生成元 R S ι) (P' : 生成元 R S ι')
  定义体: Extension.H1Cotangent.equiv
    (Generators.defaultHom P P').toExtensionHom (Generators.defaultHom P' P).toExtensionHom

Depends on / 依赖: Extension, Extension.H1Cotangent.equiv, Generators, Generators.defaultHom, H1Cotangent, defaultHom, toExtensionHom
-/
def Generators.H1Cotangent.equiv (P : Generators R S ι) (P' : Generators R S ι') :
    P.toExtension.H1Cotangent ≃ₗ[S] P'.toExtension.H1Cotangent :=
  Extension.H1Cotangent.equiv
    (Generators.defaultHom P P').toExtensionHom (Generators.defaultHom P' P).toExtensionHom

variable {S' : Type*} [CommRing S'] [Algebra R S']
variable {T : Type w} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable [Algebra S' T] [IsScalarTower R S' T]

variable (R S S' T)

/--
Definition of `H1Cotangent` / `H1Cotangent` 的定义

English:
abbreviation H1Cotangent
  signature: : Type _
  body: (Generators.self R S).toExtension.H1Cotangent

中文:
缩写 H1Cotangent
  签名: : 类型 _
  定义体: (Generators.self R S).toExtension.H1Cotangent

Depends on / 依赖: Generators, Generators.self, H1Cotangent, toExtension, toExtension.H1Cotangent
-/
abbrev H1Cotangent : Type _ := (Generators.self R S).toExtension.H1Cotangent

/--
Definition of `H1Cotangent.map` / `H1Cotangent.map` 的定义

English:
definition H1Cotangent.map
  signature: : H1Cotangent R S' ->ₗ[S'] H1Cotangent S T
  body: Extension.H1Cotangent.map (Generators.defaultHom _ _).toExtensionHom

中文:
定义 H1Cotangent.map
  签名: : H1Cotangent R S' ->ₗ[S'] H1Cotangent S T
  定义体: Extension.H1Cotangent.map (Generators.defaultHom _ _).toExtensionHom
-/
def H1Cotangent.map : H1Cotangent R S' ->ₗ[S'] H1Cotangent S T :=
  Extension.H1Cotangent.map (Generators.defaultHom _ _).toExtensionHom

/--
Definition of `H1Cotangent.mapEquiv` / `H1Cotangent.mapEquiv` 的定义

English:
definition H1Cotangent.mapEquiv
  signature: (e : S ≃ₐ[R] S')
  body: -- we are constructing data, so we do not use `algebraize`
  letI := e.toRingHom.toAlgebra
  letI := e.symm.toRingHom.toAlgebra
  have : IsScalarTower R S S' := .of_algebraMap_eq' e.toAlgHom.comp_algebraMap.symm
  have : IsScalarTower R S' S := .of_algebraMap_eq' e.symm.toAlgHom.comp_algebraMap.symm
  have : IsScalarTower S S' S := .of_algebraMap_eq fun _ => (e.symm_apply_apply _).symm
  have : IsScalarTower S' S S' := .of_algebraMap_eq fun _ => (e.apply_symm_apply _).symm
  { toFun := map R R S S'
    invFun := map R R S' S
    left_inv x := by
      change ((map R R S' S).restrictScalars S ∘ₗ map R R S S') x = x
      rw [map]; rw [map]; rw [← Extension.H1Cotangent.map_comp]; rw [Extension.H1Cotangent.map_eq]; rw [Extension.H1Cotangent.map_id]; rw [LinearMap.id_apply]
    right_inv x := by
      change ((map R R S S').restrictScalars S' ∘ₗ map R R S' S) x = x
      rw [map]; rw [map]; rw [← Extension.H1Cotangent.map_comp]; rw [Extension.H1Cotangent.map_eq]; rw [Extension.H1Cotangent.map_id]; rw [LinearMap.id_apply]
    map_add' := map_add (map R R S S')
    map_smul' := LinearMap.CompatibleSMul.map_smul (map R R S S') }

中文:
定义 H1Cotangent.mapEquiv
  签名: (e : S ≃ₐ[R] S')
  定义体: -- we are constructing data, so we do not use `algebraize`
  letI := e.toRingHom.toAlgebra
  letI := e.symm.toRingHom.toAlgebra
  have : IsScalarTower R S S' := .of_algebraMap_eq' e.toAlgHom.comp_algebraMap.symm
  have : IsScalarTower R S' S := .of_algebraMap_eq' e.symm.toAlgHom.comp_algebraMap.symm
  have : IsScalarTower S S' S := .of_algebraMap_eq fun _ => (e.symm_apply_apply _).symm
  have : IsScalarTower S' S S' := .of_algebraMap_eq fun _ => (e.apply_symm_apply _).symm
  { toFun := map R R S S'
    invFun := map R R S' S
    left_inv x := by
      change ((map R R S' S).restrictScalars S ∘ₗ map R R S S') x = x
      rw [map]; rw [map]; rw [← Extension.H1Cotangent.map_comp]; rw [Extension.H1Cotangent.map_eq]; rw [Extension.H1Cotangent.map_id]; rw [LinearMap.id_apply]
    right_inv x := by
      change ((map R R S S').restrictScalars S' ∘ₗ map R R S' S) x = x
      rw [map]; rw [map]; rw [← Extension.H1Cotangent.map_comp]; rw [Extension.H1Cotangent.map_eq]; rw [Extension.H1Cotangent.map_id]; rw [LinearMap.id_apply]
    map_add' := map_add (map R R S S')
    map_smul' := LinearMap.CompatibleSMul.map_smul (map R R S S') }
-/
def H1Cotangent.mapEquiv (e : S ≃ₐ[R] S') :
    H1Cotangent R S ≃ₗ[R] H1Cotangent R S' :=
  -- we are constructing data, so we do not use `algebraize`
  letI := e.toRingHom.toAlgebra
  letI := e.symm.toRingHom.toAlgebra
  have : IsScalarTower R S S' := .of_algebraMap_eq' e.toAlgHom.comp_algebraMap.symm
  have : IsScalarTower R S' S := .of_algebraMap_eq' e.symm.toAlgHom.comp_algebraMap.symm
  have : IsScalarTower S S' S := .of_algebraMap_eq fun _ => (e.symm_apply_apply _).symm
  have : IsScalarTower S' S S' := .of_algebraMap_eq fun _ => (e.apply_symm_apply _).symm
  { toFun := map R R S S'
    invFun := map R R S' S
    left_inv x := by
      change ((map R R S' S).restrictScalars S ∘ₗ map R R S S') x = x
      rw [map]; rw [map]; rw [← Extension.H1Cotangent.map_comp]; rw [Extension.H1Cotangent.map_eq]; rw [Extension.H1Cotangent.map_id]; rw [LinearMap.id_apply]
    right_inv x := by
      change ((map R R S S').restrictScalars S' ∘ₗ map R R S' S) x = x
      rw [map]; rw [map]; rw [← Extension.H1Cotangent.map_comp]; rw [Extension.H1Cotangent.map_eq]; rw [Extension.H1Cotangent.map_id]; rw [LinearMap.id_apply]
    map_add' := map_add (map R R S S')
    map_smul' := LinearMap.CompatibleSMul.map_smul (map R R S S') }

variable {R S S' T}

/--
Definition of `Generators.equivH1Cotangent` / `Generators.equivH1Cotangent` 的定义

English:
abbreviation Generators.equivH1Cotangent
  signature: (P : Generators R S ι)
  body: Generators.H1Cotangent.equiv _ _

中文:
缩写 生成元.equivH1Cotangent
  签名: (P : 生成元 R S ι)
  定义体: Generators.H1Cotangent.equiv _ _

Depends on / 依赖: Generators, Generators.H1Cotangent.equiv, H1Cotangent
-/
abbrev Generators.equivH1Cotangent (P : Generators R S ι) :
    P.toExtension.H1Cotangent ≃ₗ[S] H1Cotangent R S :=
  Generators.H1Cotangent.equiv _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- TODO: should infer_instance be considered normalising?
set_option linter.flexible false in
attribute [local instance] Module.finitePresentation_of_projective in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [FinitePresentation
  signature: R S] [Module.Projective S Ω[S⁄R]] :
  body: by
  let P := Algebra.Presentation.ofFinitePresentation R S
  have : Algebra.FiniteType R P.toExtension.Ring := by simp [P]; infer_instance
  suffices Module.Finite S P.toExtension.H1Cotangent from
    .of_surjective P.equivH1Cotangent.toLinearMap P.equivH1Cotangent.surjective
  rw [Module.finite_def]; rw [Submodule.fg_top]; rw [← LinearMap.ker_rangeRestrict]
  have := Extension.Cotangent.finite P.fg_ker
  have : Module.FinitePresentation S (LinearMap.range P.toExtension.cotangentComplex) := by
    rw [← LinearMap.exact_iff.mp P.toExtension.exact_cotangentComplex_toKaehler]
    exact Module.finitePresentation_of_projective_of_exact
      _ _ (Subtype.val_injective) P.toExtension.toKaehler_surjective
      (LinearMap.exact_subtype_ker_map _)
  exact Module.FinitePresentation.fg_ker (N := LinearMap.range P.toExtension.cotangentComplex)
    _ P.toExtension.cotangentComplex.surjective_rangeRestrict

中文:
实例 [有限呈现
  签名: R S] [模.投射 S Ω[S⁄R]] :
  定义体: by
  let P := Algebra.Presentation.ofFinitePresentation R S
  have : Algebra.FiniteType R P.toExtension.Ring := by simp [P]; infer_instance
  suffices Module.Finite S P.toExtension.H1Cotangent from
    .of_surjective P.equivH1Cotangent.toLinearMap P.equivH1Cotangent.surjective
  rw [Module.finite_def]; rw [Submodule.fg_top]; rw [← LinearMap.ker_rangeRestrict]
  have := Extension.Cotangent.finite P.fg_ker
  have : Module.FinitePresentation S (LinearMap.range P.toExtension.cotangentComplex) := by
    rw [← LinearMap.exact_iff.mp P.toExtension.exact_cotangentComplex_toKaehler]
    exact Module.finitePresentation_of_projective_of_exact
      _ _ (Subtype.val_injective) P.toExtension.toKaehler_surjective
      (LinearMap.exact_subtype_ker_map _)
  exact Module.FinitePresentation.fg_ker (N := LinearMap.range P.toExtension.cotangentComplex)
    _ P.toExtension.cotangentComplex.surjective_rangeRestrict

Depends on / 依赖: Algebra, Algebra.FiniteType, Algebra.Presentation.ofFinitePresentation, Cotangent, Extension, Extension.Cotangent.finite, Finite, FinitePresentation, FiniteType, H1Cotangent, LinearMap, LinearMap.ker_rangeRestrict, LinearMap.range, Module, Module.Finite, Module.FinitePresentation, Module.finite_def, P.equivH1Cotangent.surjective, P.equivH1Cotangent.toLinearMap, P.fg_ker
-/
instance [FinitePresentation R S] [Module.Projective S Ω[S⁄R]] :
    Module.Finite S (H1Cotangent R S) := by
  let P := Algebra.Presentation.ofFinitePresentation R S
  have : Algebra.FiniteType R P.toExtension.Ring := by simp [P]; infer_instance
  suffices Module.Finite S P.toExtension.H1Cotangent from
    .of_surjective P.equivH1Cotangent.toLinearMap P.equivH1Cotangent.surjective
  rw [Module.finite_def]; rw [Submodule.fg_top]; rw [← LinearMap.ker_rangeRestrict]
  have := Extension.Cotangent.finite P.fg_ker
  have : Module.FinitePresentation S (LinearMap.range P.toExtension.cotangentComplex) := by
    rw [← LinearMap.exact_iff.mp P.toExtension.exact_cotangentComplex_toKaehler]
    exact Module.finitePresentation_of_projective_of_exact
      _ _ (Subtype.val_injective) P.toExtension.toKaehler_surjective
      (LinearMap.exact_subtype_ker_map _)
  exact Module.FinitePresentation.fg_ker (N := LinearMap.range P.toExtension.cotangentComplex)
    _ P.toExtension.cotangentComplex.surjective_rangeRestrict

end Algebra
