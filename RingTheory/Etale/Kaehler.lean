/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Smooth.Kaehler
public import Mathlib.RingTheory.Flat.Localization

/-!
# The differential module and étale algebras

## Main results
- `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`:
  The canonical isomorphism `T ⊗[S] Ω[S⁄R] ≃ₗ[T] Ω[T⁄R]` for `T` a formally étale `S`-algebra.
- `Algebra.tensorH1CotangentOfIsLocalization`:
  The canonical isomorphism `T ⊗[S] H¹(L_{S⁄R}) ≃ₗ[T] H¹(L_{T⁄R})` for `T` a localization of `S`.
-/

@[expose] public section

universe u

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

open TensorProduct

/--
The canonical isomorphism `T ⊗[S] Ω[S⁄R] ≃ₗ[T] Ω[T⁄R]` for `T` a formally étale `S`-algebra.
Also see `S ⊗[R] Ω[A⁄R] ≃ₗ[S] Ω[S ⊗[R] A⁄S]` at `KaehlerDifferential.tensorKaehlerEquiv`.
-/
@[simps! apply] noncomputable
/--
Definition of `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale` / `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale` 的定义

English:
definition KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
  signature: [Algebra.FormallyEtale S T]
  body: by
  refine LinearEquiv.ofBijective (mapBaseChange R S T)
    ⟨?_, fun x => (KaehlerDifferential.exact_mapBaseChange_map R S T x).mp (Subsingleton.elim _ _)⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T x).mp hx
  rw [Subsingleto

中文:
定义 KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
  签名: [代数.形式平展 S T]
  定义体: by
  refine LinearEquiv.ofBijective (mapBaseChange R S T)
    ⟨?_, fun x => (KaehlerDifferential.exact_mapBaseChange_map R S T x).mp (Subsingleton.elim _ _)⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T x).mp hx
  rw [Subsingleto

Depends on / 依赖: Algebra, Algebra.H1Cotangent.exact_, H1Cotangent, KaehlerDifferential, KaehlerDifferential.exact_mapBaseChange_map, LinearEquiv, LinearEquiv.ofBijective, Subsingleton, Subsingleton.elim, exact_mapBaseChange_map, injective_iff_map_eq_zero, mapBaseChange, map_zero, ofBijective
-/
def KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale [Algebra.FormallyEtale S T] :
    T otimes[S] Ω[S⁄R] ≃ₗ[T] Ω[T⁄R] := by
  refine LinearEquiv.ofBijective (mapBaseChange R S T)
    ⟨?_, fun x => (KaehlerDifferential.exact_mapBaseChange_map R S T x).mp (Subsingleton.elim _ _)⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T x).mp hx
  rw [Subsingleton.elim x 0]; rw [map_zero]

/--
lemma `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap` / 引理 `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap`

English:
lemma KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap
  proof: by
  rw [LinearEquiv.symm_apply_eq]; rw [tensorKaehlerEquivOfFormallyEtale_apply]; rw [mapBaseChange_tmul]; rw [one_smul]; rw [map_D]

中文:
引理 KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap
  证明: by
  rw [LinearEquiv.symm_apply_eq]; rw [tensorKaehlerEquivOfFormallyEtale_apply]; rw [mapBaseChange_tmul]; rw [one_smul]; rw [map_D]

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_eq, mapBaseChange_tmul, map_D, one_smul, symm_apply_eq, tensorKaehlerEquivOfFormallyEtale_apply
-/
lemma KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap
    [Algebra.FormallyEtale S T] (s : S) :
    (tensorKaehlerEquivOfFormallyEtale R S T).symm (D R T (algebraMap S T s)) = 1 otimesₜ D R S s := by
  rw [LinearEquiv.symm_apply_eq]; rw [tensorKaehlerEquivOfFormallyEtale_apply]; rw [mapBaseChange_tmul]; rw [one_smul]; rw [map_D]

/--
lemma `KaehlerDifferential.isBaseChange_of_formallyEtale` / 引理 `KaehlerDifferential.isBaseChange_of_formallyEtale`

English:
lemma KaehlerDifferential.isBaseChange_of_formallyEtale
  given: [Algebra.FormallyEtale S T]
  proof: by
  change Function.Bijective _
  convert! (tensorKaehlerEquivOfFormallyEtale R S T).bijective using 1
  change _ = ((tensorKaehlerEquivOfFormallyEtale
    R S T).toLinearMap.restrictScalars S : T otimes[S] Ω[S⁄R] -> _)
  congr!
  ext
  simp

中文:
引理 KaehlerDifferential.isBaseChange_of_formallyEtale
  条件: [代数.形式平展 S T]
  证明: by
  change Function.Bijective _
  convert! (tensorKaehlerEquivOfFormallyEtale R S T).bijective using 1
  change _ = ((tensorKaehlerEquivOfFormallyEtale
    R S T).toLinearMap.restrictScalars S : T otimes[S] Ω[S⁄R] -> _)
  congr!
  ext
  simp

Depends on / 依赖: Bijective, Function, Function.Bijective, bijective, convert, otimes, restrictScalars, tensorKaehlerEquivOfFormallyEtale, toLinearMap, toLinearMap.restrictScalars
-/
lemma KaehlerDifferential.isBaseChange_of_formallyEtale [Algebra.FormallyEtale S T] :
    IsBaseChange T (map R R S T) := by
  change Function.Bijective _
  convert! (tensorKaehlerEquivOfFormallyEtale R S T).bijective using 1
  change _ = ((tensorKaehlerEquivOfFormallyEtale
    R S T).toLinearMap.restrictScalars S : T otimes[S] Ω[S⁄R] -> _)
  congr!
  ext
  simp

/--
Instance `KaehlerDifferential.isLocalizedModule_map` / 实例 `KaehlerDifferential.isLocalizedModule_map`

English:
instance KaehlerDifferential.isLocalizedModule_map
  signature: (M : Submonoid S) [IsLocalization M T]
  body: have := Algebra.FormallyEtale.of_isLocalization (Rₘ := T) M
  (isLocalizedModule_iff_isBaseChange M T _).mpr (isBaseChange_of_formallyEtale R S T)

中文:
实例 KaehlerDifferential.isLocalizedModule_map
  签名: (M : 子幺半群 S) [是Localization M T]
  定义体: have := Algebra.FormallyEtale.of_isLocalization (Rₘ := T) M
  (isLocalizedModule_iff_isBaseChange M T _).mpr (isBaseChange_of_formallyEtale R S T)

Depends on / 依赖: Algebra, Algebra.FormallyEtale.of_isLocalization, FormallyEtale, isBaseChange_of_formallyEtale, isLocalizedModule_iff_isBaseChange, of_isLocalization
-/
instance KaehlerDifferential.isLocalizedModule_map (M : Submonoid S) [IsLocalization M T] :
    IsLocalizedModule M (map R R S T) :=
  have := Algebra.FormallyEtale.of_isLocalization (Rₘ := T) M
  (isLocalizedModule_iff_isBaseChange M T _).mpr (isBaseChange_of_formallyEtale R S T)

/--
lemma `KaehlerDifferential.span_range_map_derivation_of_isLocalization` / 引理 `KaehlerDifferential.span_range_map_derivation_of_isLocalization`

English:
lemma KaehlerDifferential.span_range_map_derivation_of_isLocalization
  proof: by
  convert!
    span_eq_top_of_isLocalizedModule T M (map R R S T) (v := Set.range <| D R S)
      (span_range_derivation R S)
  rw [← Set.range_comp]; rw [Function.comp_def]

中文:
引理 KaehlerDifferential.span_range_map_derivation_of_isLocalization
  证明: by
  convert!
    span_eq_top_of_isLocalizedModule T M (map R R S T) (v := Set.range <| D R S)
      (span_range_derivation R S)
  rw [← Set.range_comp]; rw [Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, Set.range, Set.range_comp, comp_def, convert, range_comp, span_eq_top_of_isLocalizedModule, span_range_derivation
-/
lemma KaehlerDifferential.span_range_map_derivation_of_isLocalization
    (M : Submonoid S) [IsLocalization M T] :
    Submodule.span T (Set.range <| map R R S T ∘ D R S) = ⊤ := by
  convert!
    span_eq_top_of_isLocalizedModule T M (map R R S T) (v := Set.range <| D R S)
      (span_range_derivation R S)
  rw [← Set.range_comp]; rw [Function.comp_def]

namespace Algebra.Extension

open KaehlerDifferential

attribute [local instance] SMulCommClass.of_commMonoid

variable {R S T}

/-!
Suppose we have a morphism of extensions of `R`-algebras
```
0 → J → Q → T → 0
    ↑ ↑ ↑
0 → I → P → S → 0
```
-/
variable {P : Extension.{u} R S} {Q : Extension.{u} R T} (f : P.Hom Q)

set_option backward.defeqAttrib.useBackward true in
/-- If `P → Q` is formally étale, then `T ⊗ₛ (S ⊗ₚ Ω[P/R]) ≃ T ⊗_Q Ω[Q/R]`. -/
noncomputable
/--
Definition of `tensorCotangentSpaceOfFormallyEtale` / `tensorCotangentSpaceOfFormallyEtale` 的定义

English:
definition tensorCotangentSpaceOfFormallyEtale
  body: letI := f.toRingHom.toAlgebra
  haveI : IsScalarTower R P.Ring Q.Ring :=
    .of_algebraMap_eq fun r => (f.toRingHom_algebraMap r).symm
  letI := ((algebraMap S T).comp (algebraMap P.Ring S)).toAlgebra
  haveI : IsScalarTower P.Ring S T := .of_algebraMap_eq' rfl
  haveI : IsScalarTower P.Ring Q.Ring

中文:
定义 tensorCotangentSpaceOfFormallyEtale
  定义体: letI := f.toRingHom.toAlgebra
  haveI : IsScalarTower R P.Ring Q.Ring :=
    .of_algebraMap_eq fun r => (f.toRingHom_algebraMap r).symm
  letI := ((algebraMap S T).comp (algebraMap P.Ring S)).toAlgebra
  haveI : IsScalarTower P.Ring S T := .of_algebraMap_eq' rfl
  haveI : IsScalarTower P.Ring Q.Ring

Depends on / 依赖: CotangentSpace, CotangentSpace.map, FormallyEtale, IsScalarTower, LinearMa, LinearMap, LinearMap.liftBaseChange, P.Ring, Q.Ring, algebraMap, algebraMap_toRingHom, f.algebraMap_toRingHom, f.toRingHom.toAlgebra, f.toRingHom_algebraMap, invFun, liftBaseChange, of_algebraMap_eq, toAlgebra, toRingHom, toRingHom_algebraMap
-/
def tensorCotangentSpaceOfFormallyEtale
    (H : f.toRingHom.FormallyEtale) :
    T otimes[S] P.CotangentSpace ≃ₗ[T] Q.CotangentSpace :=
  letI := f.toRingHom.toAlgebra
  haveI : IsScalarTower R P.Ring Q.Ring :=
    .of_algebraMap_eq fun r => (f.toRingHom_algebraMap r).symm
  letI := ((algebraMap S T).comp (algebraMap P.Ring S)).toAlgebra
  haveI : IsScalarTower P.Ring S T := .of_algebraMap_eq' rfl
  haveI : IsScalarTower P.Ring Q.Ring T :=
    .of_algebraMap_eq fun r => (f.algebraMap_toRingHom r).symm
  haveI : FormallyEtale P.Ring Q.Ring := ‹_›
  { __ := (CotangentSpace.map f).liftBaseChange T
    invFun := LinearMap.liftBaseChange T (by
      refine LinearMap.liftBaseChange _ ?_ ∘ₗ
        (tensorKaehlerEquivOfFormallyEtale R P.Ring Q.Ring).symm.toLinearMap
      exact (TensorProduct.mk _ _ _ 1).restrictScalars P.Ring ∘ₗ
        (TensorProduct.mk _ _ _ 1).restrictScalars P.Ring)
    left_inv x := by
      change (LinearMap.liftBaseChange _ _ ∘ₗ LinearMap.liftBaseChange _ _) x =
        LinearMap.id (R := T) x
      congr 1
      ext : 4
      refine Derivation.liftKaehlerDifferential_unique
        (R := R) (S := P.Ring) (M := T otimes[S] P.CotangentSpace) _ _ ?_
      ext a
      have : (tensorKaehlerEquivOfFormallyEtale R P.Ring Q.Ring).symm
          ((D R Q.Ring) (f.toRingHom a)) = 1 otimesₜ D _ _ a :=
        tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap R P.Ring Q.Ring a
      simp [this]
    right_inv x := by
      change (LinearMap.liftBaseChange _ _ ∘ₗ LinearMap.liftBaseChange _ _) x =
        LinearMap.id (R := T) x
      congr 1
      ext a
      dsimp
      obtain ⟨x, hx⟩ := (tensorKaehlerEquivOfFormallyEtale R P.Ring _).surjective (D R Q.Ring a)
      simp only [one_smul, ← hx, LinearEquiv.symm_apply_apply]
      change (((CotangentSpace.map f).liftBaseChange T).restrictScalars Q.Ring ∘ₗ
        LinearMap.liftBaseChange _ _) x = ((TensorProduct.mk _ _ _ 1) ∘ₗ
          (tensorKaehlerEquivOfFormallyEtale R P.Ring Q.Ring).toLinearMap) x
      congr 1
      ext a
      simp; rfl }

/-- (Implementation)
If `J ≃ Q ⊗ₚ I` (e.g. when `T = Q ⊗ₚ S` and `P → Q` is flat), then `T ⊗ₛ I/I² ≃ J/J²`.
This is the inverse. -/
noncomputable
/--
Definition of `tensorCotangentInvFun` / `tensorCotangentInvFun` 的定义

English:
definition tensorCotangentInvFun
  body: letI := ((algebraMap S T).comp (algebraMap P.Ring S)).toAlgebra
  haveI : IsScalarTower P.Ring S T := .of_algebraMap_eq' rfl
  haveI : IsScalarTower P.Ring Q.Ring T :=
    .of_algebraMap_eq fun r => halg ▸ (f.algebraMap_toRingHom r).symm
  letI e := LinearEquiv.ofBijective _ H
  letI f' : Q.ker ->ₗ[

中文:
定义 tensorCotangentInvFun
  定义体: letI := ((algebraMap S T).comp (algebraMap P.Ring S)).toAlgebra
  haveI : IsScalarTower P.Ring S T := .of_algebraMap_eq' rfl
  haveI : IsScalarTower P.Ring Q.Ring T :=
    .of_algebraMap_eq fun r => halg ▸ (f.algebraMap_toRingHom r).symm
  letI e := LinearEquiv.ofBijective _ H
  letI f' : Q.ker ->ₗ[

Depends on / 依赖: Cotangent, Cotangent.mk, IsScalarTower, LinearEquiv, LinearEquiv.ofBijective, LinearMap, LinearMap.liftBaseChange, P.Cotangent, P.Ring, Q.Ring, Q.ker, QuotientAddGroup, QuotientAddGroup.lift, Submodule, Submodule.smul_, TensorProduct, TensorProduct.mk, algebraMap, algebraMap_toRingHom, e.symm.toLinearMap
-/
def tensorCotangentInvFun
    [alg : Algebra P.Ring Q.Ring] (halg : algebraMap P.Ring Q.Ring = f.toRingHom)
    (H : Function.Bijective ((f.mapKer halg).liftBaseChange Q.Ring)) :
    Q.Cotangent ->+ T otimes[S] P.Cotangent :=
  letI := ((algebraMap S T).comp (algebraMap P.Ring S)).toAlgebra
  haveI : IsScalarTower P.Ring S T := .of_algebraMap_eq' rfl
  haveI : IsScalarTower P.Ring Q.Ring T :=
    .of_algebraMap_eq fun r => halg ▸ (f.algebraMap_toRingHom r).symm
  letI e := LinearEquiv.ofBijective _ H
  letI f' : Q.ker ->ₗ[Q.Ring] T otimes[S] P.Cotangent :=
    (LinearMap.liftBaseChange _
      ((TensorProduct.mk _ _ _ 1).restrictScalars _ ∘ₗ Cotangent.mk)) ∘ₗ e.symm.toLinearMap
QuotientAddGroup.lift _ f' by
    intro x hx
    refine Submodule.smul_induction_on hx ?_ fun _ _ => add_mem
    clear x hx
    rintro a ha b -
    obtain ⟨x, hx⟩ := e.surjective ⟨a, ha⟩
    obtain rfl : (e x).1 = a := congr_arg Subtype.val hx
    obtain ⟨y, rfl⟩ := e.surjective b
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_coe, map_smul,
      LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply, f']
    clear hx ha
    induction x with
    | zero => simp only [map_zero, ZeroMemClass.coe_zero, zero_smul]
    | add x y _ _ =>
      simp only [map_add, Submodule.coe_add, add_smul, zero_add, *]
    | tmul a b =>
      induction y with
      | zero => simp only [map_zero, smul_zero]
      | add x y hx hy => simp only [LinearMap.map_add, smul_add, hx, hy, zero_add]
      | tmul c d =>
        simp only [LinearMap.liftBaseChange_tmul, LinearMap.coe_comp, SetLike.val_smul,
          LinearMap.coe_restrictScalars, Function.comp_apply, mk_apply, smul_eq_mul, e,
          LinearMap.liftBaseChange_tmul, LinearEquiv.ofBijective_apply]
        have h₂ : b.1 • Cotangent.mk d = 0 := by ext; simp [Cotangent.smul_eq_zero_of_mem _ b.2]
        rw [TensorProduct.smul_tmul']; rw [mul_smul]; rw [f.mapKer_apply_coe]; rw [← halg]; rw [algebraMap_smul]; rw [← TensorProduct.tmul_smul]; rw [h₂]; rw [tmul_zero]; rw [smul_zero]

omit [IsScalarTower R S T] in
/--
lemma `tensorCotangentInvFun_smul_mk` / 引理 `tensorCotangentInvFun_smul_mk`

English:
lemma tensorCotangentInvFun_smul_mk
  proof: by
  let := ((algebraMap S T).comp (algebraMap P.Ring S)).toAlgebra
  have : IsScalarTower P.Ring S T := .of_algebraMap_eq' rfl
  have : IsScalarTower P.Ring Q.Ring T :=
    .of_algebraMap_eq fun r => halg ▸ (f.algebraMap_toRingHom r).symm
  let e := LinearEquiv.ofBijective _ H
  trans tensorCotange

中文:
引理 tensorCotangentInvFun_smul_mk
  证明: by
  let := ((algebraMap S T).comp (algebraMap P.Ring S)).toAlgebra
  have : IsScalarTower P.Ring S T := .of_algebraMap_eq' rfl
  have : IsScalarTower P.Ring Q.Ring T :=
    .of_algebraMap_eq fun r => halg ▸ (f.algebraMap_toRingHom r).symm
  let e := LinearEquiv.ofBijective _ H
  trans tensorCotange

Depends on / 依赖: Cotangent, Cotangent.mk, IsScalarTower, LinearEquiv, LinearEquiv.ofBijective, P.Ring, Q.Ring, TensorProduct, TensorProduct.mk, algebraMap, algebraMap_toRingHom, e.symm, f.algebraMap_toRingHom, f.mapKer, liftBaseChange, mapKer, ofBijective, of_algebraMap_eq, restrictScalars, tensorCotangentInvFun
-/
lemma tensorCotangentInvFun_smul_mk
    [alg : Algebra P.Ring Q.Ring] (halg : algebraMap P.Ring Q.Ring = f.toRingHom)
    (H : Function.Bijective ((f.mapKer halg).liftBaseChange Q.Ring)) (x : Q.Ring) (y : P.ker) :
    tensorCotangentInvFun f halg H (x • .mk ⟨f.toRingHom y, (f.mapKer halg y).2⟩) =
      x • 1 otimesₜ .mk y := by
  let := ((algebraMap S T).comp (algebraMap P.Ring S)).toAlgebra
  have : IsScalarTower P.Ring S T := .of_algebraMap_eq' rfl
  have : IsScalarTower P.Ring Q.Ring T :=
    .of_algebraMap_eq fun r => halg ▸ (f.algebraMap_toRingHom r).symm
  let e := LinearEquiv.ofBijective _ H
  trans tensorCotangentInvFun f halg H (.mk ((f.mapKer halg).liftBaseChange Q.Ring (x otimesₜ y)))
  · simp; rfl
  change ((TensorProduct.mk _ _ _ 1).restrictScalars _ ∘ₗ Cotangent.mk).liftBaseChange _
    (e.symm (e (x otimesₜ y))) = _
  rw [e.symm_apply_apply]
  simp

/-- If `J ≃ Q ⊗ₚ I` (e.g. when `T = Q ⊗ₚ S` and `P → Q` is flat), then `T ⊗ₛ I/I² ≃ J/J²`. -/
noncomputable
/--
Definition of `tensorCotangent` / `tensorCotangent` 的定义

English:
definition tensorCotangent
  signature: [alg : Algebra P.Ring Q.Ring] (halg : algebraMap P.Ring Q.Ring = f.toRingHom)
  body: { __ := (Cotangent.map f).liftBaseChange T
    invFun := tensorCotangentInvFun f halg H
    left_inv x := by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
      induction x with
      | zero => simp only [map_zero]
      | add x y _ _ => simp only [map_add, *]
      | tmul a b =>
   

中文:
定义 tensorCotangent
  签名: [alg : 代数 P.环 Q.环] (halg : algebraMap P.环 Q.环 = f.toRingHom)
  定义体: { __ := (Cotangent.map f).liftBaseChange T
    invFun := tensorCotangentInvFun f halg H
    left_inv x := by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
      induction x with
      | zero => simp only [map_zero]
      | add x y _ _ => simp only [map_add, *]
      | tmul a b =>
   

Depends on / 依赖: AddHom, AddHom.toFun_eq_coe, Cotangent, Cotangent.map, Cotangent.map_mk, Cotangent.mk_surjective, Hom.toAlgHom_apply, LinearMap, LinearMap.coe_toAddHom, LinearMap.liftBaseChange_tmul, MyFunLike, MyFunLike.toFun, Q.algebraMap_surjective, algebraMap_smul, algebraMap_surjective, coe_toAddHom, invFun, left_inv, liftBaseChange, liftBaseChange_tmul
-/
def tensorCotangent [alg : Algebra P.Ring Q.Ring] (halg : algebraMap P.Ring Q.Ring = f.toRingHom)
    (H : Function.Bijective ((f.mapKer halg).liftBaseChange Q.Ring)) :
    T otimes[S] P.Cotangent ≃ₗ[T] Q.Cotangent :=
  { __ := (Cotangent.map f).liftBaseChange T
    invFun := tensorCotangentInvFun f halg H
    left_inv x := by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
      induction x with
      | zero => simp only [map_zero]
      | add x y _ _ => simp only [map_add, *]
      | tmul a b =>
        obtain ⟨b, rfl⟩ := Cotangent.mk_surjective b
        obtain ⟨a, rfl⟩ := Q.algebraMap_surjective a
        simp only [LinearMap.liftBaseChange_tmul, Cotangent.map_mk, Hom.toAlgHom_apply,
          algebraMap_smul]
        refine (tensorCotangentInvFun_smul_mk f halg H a b).trans ?_
        simp [algebraMap_eq_smul_one, TensorProduct.smul_tmul']
    right_inv x := by
      obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
      obtain ⟨x, rfl⟩ := H.surjective x
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
      induction x with
      | zero => simp only [map_zero]
      | add x y _ _ => simp only [map_add, *]
      | tmul a b =>
        simp only [LinearMap.liftBaseChange_tmul, map_smul]
        simp [Hom.mapKer, tensorCotangentInvFun_smul_mk] }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `J ≃ Q ⊗ₚ I`, `S → T` is flat and `P → Q` is formally étale, then `T ⊗ H¹(L_P) ≃ H¹(L_Q)`. -/
noncomputable
/--
Definition of `tensorH1CotangentOfFormallyEtale` / `tensorH1CotangentOfFormallyEtale` 的定义

English:
definition tensorH1CotangentOfFormallyEtale
  signature: [alg : Algebra P.Ring Q.Ring]
  body: by
  refine .ofBijective ((H1Cotangent.map f).liftBaseChange T) ?_
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    apply Module.Flat.lTensor_preserves_injective_linearMap _ h1Cotangentι_injective
    apply (Extension.tensorCotangent f halg H₂).injective
    simp only [map_zero]
 

中文:
定义 tensorH1CotangentOfFormallyEtale
  签名: [alg : 代数 P.环 Q.环]
  定义体: by
  refine .ofBijective ((H1Cotangent.map f).liftBaseChange T) ?_
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    apply Module.Flat.lTensor_preserves_injective_linearMap _ h1Cotangentι_injective
    apply (Extension.tensorCotangent f halg H₂).injective
    simp only [map_zero]
 

Depends on / 依赖: Cotangent, Cotangent.map, Extension, Extension.tensorCotangent, Function, Function.Exact, H1Cotangent, H1Cotangent.map, Module, Module.Flat.lTensor_preserves_injective_linearMap, P.co, baseChange, injective, injective_iff_map_eq_zero, lTensor_preserves_injective_linearMap, liftBaseChange, map_zero, ofBijective, tensorCotangent
-/
def tensorH1CotangentOfFormallyEtale [alg : Algebra P.Ring Q.Ring]
    (halg : algebraMap P.Ring Q.Ring = f.toRingHom) [Module.Flat S T]
    (H₁ : f.toRingHom.FormallyEtale)
    (H₂ : Function.Bijective ((f.mapKer halg).liftBaseChange Q.Ring)) :
    T otimes[S] P.H1Cotangent ≃ₗ[T] Q.H1Cotangent := by
  refine .ofBijective ((H1Cotangent.map f).liftBaseChange T) ?_
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    apply Module.Flat.lTensor_preserves_injective_linearMap _ h1Cotangentι_injective
    apply (Extension.tensorCotangent f halg H₂).injective
    simp only [map_zero]
    rw [← h1Cotangentι.map_zero]; rw [← hx]
    change ((Cotangent.map f).liftBaseChange T ∘ₗ h1Cotangentι.baseChange T) x =
      (h1Cotangentι ∘ₗ _) x
    congr 1
    ext x
    simp
  · intro x
    have : Function.Exact (h1Cotangentι.baseChange T) (P.cotangentComplex.baseChange T) :=
      Module.Flat.lTensor_exact T (LinearMap.exact_subtype_ker_map _)
    obtain ⟨a, ha⟩ := (this ((Extension.tensorCotangent f halg H₂).symm x.1)).mp (by
      apply (Extension.tensorCotangentSpaceOfFormallyEtale f H₁).injective
      rw [LinearEquiv.map_zero]; rw [← x.2]
      have : (CotangentSpace.map f).liftBaseChange T ∘ₗ P.cotangentComplex.baseChange T =
          Q.cotangentComplex ∘ₗ (Cotangent.map f).liftBaseChange T := by
        ext x; obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x; dsimp
        simp only [CotangentSpace.map_tmul,
          map_one, Hom.toAlgHom_apply, one_smul, cotangentComplex_mk]
      exact (DFunLike.congr_fun this _).trans (DFunLike.congr_arg Q.cotangentComplex
        ((tensorCotangent f halg H₂).apply_symm_apply x.1)))
    refine ⟨a, Subtype.ext (.trans ?_ ((LinearEquiv.eq_symm_apply _).mp ha))⟩
    change (h1Cotangentι ∘ₗ (H1Cotangent.map f).liftBaseChange T) _ =
      ((Cotangent.map f).liftBaseChange T ∘ₗ h1Cotangentι.baseChange T) _
    congr 1
    ext; dsimp

end Extension

variable {S}

set_option backward.isDefEq.respectTransparency false in
/-- let `p` be a submonoid of an `R`-algebra `S`. Then `Sₚ ⊗ H¹(L_{S/R}) ≃ H¹(L_{Sₚ/R})`. -/
noncomputable
/--
Definition of `tensorH1CotangentOfIsLocalization` / `tensorH1CotangentOfIsLocalization` 的定义

English:
definition tensorH1CotangentOfIsLocalization
  signature: (M : Submonoid S) [IsLocalization M T]
  body: by
  letI P : Extension R S := (Generators.self R S).toExtension
  letI M' := M.comap (algebraMap P.Ring S)
  letI fQ : Localization M' ->ₐ[R] T := IsLocalization.liftAlgHom (M := M')
    (f := (IsScalarTower.toAlgHom R S T).comp (IsScalarTower.toAlgHom R P.Ring S)) (fun ⟨y, hy⟩ =>
    by simpa usin

中文:
定义 tensorH1CotangentOfIsLocalization
  签名: (M : 子幺半群 S) [是Localization M T]
  定义体: by
  letI P : Extension R S := (Generators.self R S).toExtension
  letI M' := M.comap (algebraMap P.Ring S)
  letI fQ : Localization M' ->ₐ[R] T := IsLocalization.liftAlgHom (M := M')
    (f := (IsScalarTower.toAlgHom R S T).comp (IsScalarTower.toAlgHom R P.Ring S)) (fun ⟨y, hy⟩ =>
    by simpa usin

Depends on / 依赖: Extension, Generators, Generators.self, IsLocalization, IsLocalization.exists_mk, IsLocalization.liftAlgHom, IsLocalization.map_units, IsScalarTower, IsScalarTower.toAlgHom, Localization, M.comap, P.Ring, P.algebraMap_surjecti, algebraMap, algebraMap_surjecti, exists_mk, liftAlgHom, map_units, ofSurjective, toAlgHom
-/
def tensorH1CotangentOfIsLocalization (M : Submonoid S) [IsLocalization M T] :
    T otimes[S] H1Cotangent R S ≃ₗ[T] H1Cotangent R T := by
  letI P : Extension R S := (Generators.self R S).toExtension
  letI M' := M.comap (algebraMap P.Ring S)
  letI fQ : Localization M' ->ₐ[R] T := IsLocalization.liftAlgHom (M := M')
    (f := (IsScalarTower.toAlgHom R S T).comp (IsScalarTower.toAlgHom R P.Ring S)) (fun ⟨y, hy⟩ =>
    by simpa using IsLocalization.map_units T ⟨algebraMap P.Ring S y, hy⟩)
  letI Q : Extension R T := .ofSurjective fQ (by
    intro x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq M x
    obtain ⟨x, rfl⟩ := P.algebraMap_surjective x
    obtain ⟨s, rfl⟩ := P.algebraMap_surjective s
    refine ⟨IsLocalization.mk' _ x ⟨s, show s in M' from hs⟩, ?_⟩
    simp only [fQ, IsLocalization.coe_liftAlgHom, AlgHom.toRingHom_eq_coe]
    rw [IsLocalization.lift_mk'_spec]
    simp)
  letI f : P.Hom Q :=
  { toRingHom := algebraMap P.Ring (Localization M')
    toRingHom_algebraMap x := (IsScalarTower.algebraMap_apply R P.Ring (Localization M') _).symm
    algebraMap_toRingHom x := @IsLocalization.lift_eq .. }
  haveI : FormallySmooth R P.Ring := inferInstanceAs (FormallySmooth R (MvPolynomial _ _))
  haveI : FormallySmooth P.Ring (Localization M') := .of_isLocalization M'
  haveI : FormallySmooth R Q.Ring := .comp R P.Ring (Localization M')
  haveI : Module.Flat S T := IsLocalization.flat T M
  letI : Algebra P.Ring Q.Ring := (inferInstance : Algebra P.Ring (Localization M'))
  letI := ((algebraMap S T).comp (algebraMap P.Ring S)).toAlgebra
  letI := fQ.toRingHom.toAlgebra
  haveI : IsScalarTower P.Ring S T := .of_algebraMap_eq' rfl
  haveI : IsScalarTower P.Ring (Localization M') T :=
    .of_algebraMap_eq fun r => (f.algebraMap_toRingHom r).symm
  haveI : IsLocalizedModule M' (IsScalarTower.toAlgHom P.Ring S T).toLinearMap := by
    rw [isLocalizedModule_iff_isLocalization]
    convert! ‹IsLocalization M T› using 1
    exact Submonoid.map_comap_eq_of_surjective P.algebraMap_surjective _
  refine Extension.tensorH1CotangentOfFormallyEtale f rfl ?_ ?_ ≪≫ₗ
      Extension.equivH1CotangentOfFormallySmooth _
  · exact RingHom.formallyEtale_algebraMap.mpr
      (FormallyEtale.of_isLocalization (M := M') (Rₘ := Localization M'))
  · let F : P.ker ->ₗ[P.Ring] RingHom.ker fQ := f.mapKer rfl
    refine (isLocalizedModule_iff_isBaseChange M' (Localization M') F).mp ?_
    have : (LinearMap.ker <| Algebra.linearMap P.Ring S).localized' (Localization M') M'
        (Algebra.linearMap P.Ring (Localization M')) = RingHom.ker fQ := by
      rw [LinearMap.localized'_ker_eq_ker_localizedMap (Localization M') M'
        (Algebra.linearMap P.Ring (Localization M'))
        (f' := (IsScalarTower.toAlgHom P.Ring S T).toLinearMap)]
      ext x
      obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq M' x
      simp only [LinearMap.mem_ker, LinearMap.extendScalarsOfIsLocalization_apply', RingHom.mem_ker,
        IsLocalization.coe_liftAlgHom, AlgHom.toRingHom_eq_coe, IsLocalization.lift_mk'_spec,
        RingHom.coe_coe, AlgHom.coe_comp, IsScalarTower.coe_toAlgHom', Function.comp_apply,
        mul_zero, fQ]
      have : IsLocalization.mk' (Localization M') x ⟨s, hs⟩ =
          IsLocalizedModule.mk' (Algebra.linearMap P.Ring (Localization M')) x ⟨s, hs⟩ := by
        rw [IsLocalization.mk'_eq_iff_eq_mul]; rw [mul_comm]; rw [← Algebra.smul_def]; rw [← Submonoid.smul_def]; rw [IsLocalizedModule.mk'_cancel']
        rfl
      simp [this, ← IsScalarTower.algebraMap_apply]
    have : F = ((LinearEquiv.ofEq _ _ this).restrictScalars P.Ring).toLinearMap ∘ₗ
      P.ker.toLocalized' (Localization M') M' (Algebra.linearMap P.Ring (Localization M')) := by
      ext; rfl
    rw [this]
    exact IsLocalizedModule.of_linearEquiv _ _ _

set_option backward.isDefEq.respectTransparency false in
/--
lemma `tensorH1CotangentOfIsLocalization_toLinearMap` / 引理 `tensorH1CotangentOfIsLocalization_toLinearMap`

English:
lemma tensorH1CotangentOfIsLocalization_toLinearMap
  proof: by
  ext x : 3
  simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, LinearMap.liftBaseChange_tmul, one_smul]
  simp only [tensorH1CotangentOfIsLocalization,
    Extension.tensorH1CotangentOfFormallyEtale,
    LinearEquiv.ofBijective_apply

中文:
引理 tensorH1CotangentOfIsLocalization_toLinearMap
  证明: by
  ext x : 3
  simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, LinearMap.liftBaseChange_tmul, one_smul]
  simp only [tensorH1CotangentOfIsLocalization,
    Extension.tensorH1CotangentOfFormallyEtale,
    LinearEquiv.ofBijective_apply

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.curry_apply, Extension, Extension.equivH1CotangentOfFormallySmooth, Extension.tensorH1CotangentOfFormallyEtale, Generators, Generators.self, LinearEquiv, LinearEquiv.coe_coe, LinearEquiv.ofBijective_apply, LinearEquiv.trans_apply, LinearMap, LinearMap.coe_restrictScalars, LinearMap.liftBaseChange_tmul, M.comap, P.Ring, algebraMap, coe_coe, coe_restrictScalars, curry_apply
-/
lemma tensorH1CotangentOfIsLocalization_toLinearMap
    (M : Submonoid S) [IsLocalization M T] :
    (tensorH1CotangentOfIsLocalization R T M).toLinearMap =
      (Algebra.H1Cotangent.map R R S T).liftBaseChange T := by
  ext x : 3
  simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, LinearMap.liftBaseChange_tmul, one_smul]
  simp only [tensorH1CotangentOfIsLocalization,
    Extension.tensorH1CotangentOfFormallyEtale,
    LinearEquiv.ofBijective_apply, LinearMap.liftBaseChange_tmul, one_smul,
    Extension.equivH1CotangentOfFormallySmooth, LinearEquiv.trans_apply]
  let P : Extension R S := (Generators.self R S).toExtension
  let M' := M.comap (algebraMap P.Ring S)
  let fQ : Localization M' ->ₐ[R] T := IsLocalization.liftAlgHom (M := M')
    (f := (IsScalarTower.toAlgHom R S T).comp (IsScalarTower.toAlgHom R P.Ring S)) (fun ⟨y, hy⟩ =>
    by simpa using IsLocalization.map_units T ⟨algebraMap P.Ring S y, hy⟩)
  let Q : Extension R T := .ofSurjective fQ (by
    intro x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq M x
    obtain ⟨x, rfl⟩ := P.algebraMap_surjective x
    obtain ⟨s, rfl⟩ := P.algebraMap_surjective s
    refine ⟨IsLocalization.mk' _ x ⟨s, show s in M' from hs⟩, ?_⟩
    simp only [fQ, IsLocalization.coe_liftAlgHom, AlgHom.toRingHom_eq_coe]
    rw [IsLocalization.lift_mk'_spec]
    simp)
  let f : (Generators.self R T).toExtension.Hom Q :=
  { toRingHom := (MvPolynomial.aeval Q.σ).toRingHom
    toRingHom_algebraMap := (MvPolynomial.aeval Q.σ).commutes
    algebraMap_toRingHom := by
      have : (IsScalarTower.toAlgHom R Q.Ring T).comp (MvPolynomial.aeval Q.σ) =
          IsScalarTower.toAlgHom _ (Generators.self R T).toExtension.Ring _ := by
        ext i
        change _ = algebraMap (Generators.self R T).Ring _ (.X i)
        simp
      exact DFunLike.congr_fun this }
  rw [← Extension.H1Cotangent.equivOfFormallySmooth_symm]; rw [LinearEquiv.symm_apply_eq]; rw [@Extension.H1Cotangent.equivOfFormallySmooth_apply (f := f)]; rw [Algebra.H1Cotangent.map]; rw [← (Extension.H1Cotangent.map f).coe_restrictScalars S]; rw [← LinearMap.comp_apply]; rw [← Extension.H1Cotangent.map_comp]; rw [Extension.H1Cotangent.map_eq]

/--
Instance `H1Cotangent.isLocalizedModule` / 实例 `H1Cotangent.isLocalizedModule`

English:
instance H1Cotangent.isLocalizedModule
  signature: (M : Submonoid S) [IsLocalization M T]
  body: by
  rw [isLocalizedModule_iff_isBaseChange M T]
  change Function.Bijective ((Algebra.H1Cotangent.map R R S T).liftBaseChange T)
  rw [← tensorH1CotangentOfIsLocalization_toLinearMap R T M]
  exact (tensorH1CotangentOfIsLocalization R T M).bijective

中文:
实例 H1Cotangent.isLocalizedModule
  签名: (M : 子幺半群 S) [是Localization M T]
  定义体: by
  rw [isLocalizedModule_iff_isBaseChange M T]
  change Function.Bijective ((Algebra.H1Cotangent.map R R S T).liftBaseChange T)
  rw [← tensorH1CotangentOfIsLocalization_toLinearMap R T M]
  exact (tensorH1CotangentOfIsLocalization R T M).bijective

Depends on / 依赖: Algebra, Algebra.H1Cotangent.map, Bijective, Function, Function.Bijective, H1Cotangent, bijective, isLocalizedModule_iff_isBaseChange, liftBaseChange, tensorH1CotangentOfIsLocalization, tensorH1CotangentOfIsLocalization_toLinearMap
-/
instance H1Cotangent.isLocalizedModule (M : Submonoid S) [IsLocalization M T] :
    IsLocalizedModule M (Algebra.H1Cotangent.map R R S T) := by
  rw [isLocalizedModule_iff_isBaseChange M T]
  change Function.Bijective ((Algebra.H1Cotangent.map R R S T).liftBaseChange T)
  rw [← tensorH1CotangentOfIsLocalization_toLinearMap R T M]
  exact (tensorH1CotangentOfIsLocalization R T M).bijective

end Algebra
