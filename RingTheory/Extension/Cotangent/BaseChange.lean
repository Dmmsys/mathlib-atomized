/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Ideal.CotangentBaseChange
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.Algebra.FiveLemma
public import Mathlib.RingTheory.Kaehler.TensorProduct

/-!
# Base change for the naive cotangent complex

This file shows that the cotangent space and first homology of the naive cotangent complex
commute with base change.

## Main results

- `Algebra.Extension.tensorCotangentSpace`: If `T` is an `R`-algebra, there is a `T`-linear
  isomorphism `T ⊗[R] P.CotangentSpace ≃ₗ[T] (P.baseChange).CotangentSpace`.
- `Algebra.Extension.tensorCotangentOfFlat`: If `T` is flat over `R`, there is a `T`-linear
  isomorphism `T ⊗[R] P.Cotangent ≃ₗ[T] (P.baseChange).Cotangent`.
- `Algebra.Extension.tensorH1CotangentOfFlat`: If `T` is flat over `R`, there is a `T`-linear
  isomorphism `T ⊗[R] P.H1Cotangent ≃ₗ[T] (P.baseChange).H1Cotangent`.
- `Algebra.tensorH1CotangentOfFlat`: Flat base change commutes with `H1Cotangent`.

-/

public section

universe u

open TensorProduct

namespace Algebra

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

namespace Extension

variable {R S} (P : Extension.{u} R S)
variable (T : Type*) [CommRing T] [Algebra R T]

/-- The cotangent space of an extension commutes with base change. -/
noncomputable
/--
Definition of `tensorCotangentSpace` / `tensorCotangentSpace` 的定义

English:
definition tensorCotangentSpace
  signature: (P : Extension.{u} R S) (T : Type*) [CommRing T] [Algebra R T]
  body: letI := P.algebraBaseChange T
  letI : Algebra S (T otimes[R] S) := TensorProduct.rightAlgebra
  letI : Algebra P.Ring (T otimes[R] S) := Algebra.compHom _ (algebraMap P.Ring S)
  haveI : IsScalarTower R P.Ring (T otimes[R] S) :=
    .of_algebraMap_eq fun x => by
      rw [TensorProduct.algebraMap_a

中文:
定义 tensorCotangentSpace
  签名: (P : 扩张.{u} R S) (T : 类型) [交换环 T] [代数 R T]
  定义体: letI := P.algebraBaseChange T
  letI : Algebra S (T otimes[R] S) := TensorProduct.rightAlgebra
  letI : Algebra P.Ring (T otimes[R] S) := Algebra.compHom _ (algebraMap P.Ring S)
  haveI : IsScalarTower R P.Ring (T otimes[R] S) :=
    .of_algebraMap_eq fun x => by
      rw [TensorProduct.algebraMap_a

Depends on / 依赖: CotangentSpace
-/
def tensorCotangentSpace (P : Extension.{u} R S) (T : Type*) [CommRing T] [Algebra R T] :
    T otimes[R] P.CotangentSpace ≃ₗ[T] (P.baseChange (T := T)).CotangentSpace :=
  letI := P.algebraBaseChange T
  letI : Algebra S (T otimes[R] S) := TensorProduct.rightAlgebra
  letI : Algebra P.Ring (T otimes[R] S) := Algebra.compHom _ (algebraMap P.Ring S)
  haveI : IsScalarTower R P.Ring (T otimes[R] S) :=
    .of_algebraMap_eq fun x => by
      rw [TensorProduct.algebraMap_apply]; rw [RingHom.algebraMap_toAlgebra]; rw [Algebra.TensorProduct.tmul_one_eq_one_tmul]; rw [IsScalarTower.algebraMap_apply R P.Ring]
      rfl
  letI PT : Extension T (T otimes[R] S) := P.baseChange
  haveI : IsPushout R T P.Ring PT.Ring := by
    convert! TensorProduct.isPushout (R := R) (T := P.Ring) (S := T)
    exact Algebra.algebra_ext _ _ fun _ => rfl
  haveI : IsScalarTower P.Ring PT.Ring (T otimes[R] S) := .of_algebraMap_eq' rfl
  (IsTensorProduct.assocOfMapSMul (TensorProduct.mk R T S) (isTensorProduct _ _ _)
    (TensorProduct.mk _ _ _) (isTensorProduct _ _ _) (by simp [Algebra.smul_def])
    (by simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra])).symm ≪≫ₗ
  (AlgebraTensorModule.cancelBaseChange _ PT.Ring PT.Ring _ _).symm.restrictScalars T ≪≫ₗ
  (AlgebraTensorModule.congr (LinearEquiv.refl PT.Ring (T otimes[R] S))
    (KaehlerDifferential.tensorKaehlerEquiv R T P.Ring PT.Ring)).restrictScalars T

set_option backward.isDefEq.respectTransparency.types false in
attribute [local instance] algebraBaseChange in
/--
lemma `tensorCotangentSpace_tmul_tmul` / 引理 `tensorCotangentSpace_tmul_tmul`

English:
lemma tensorCotangentSpace_tmul_tmul
  given: (t : T) (s : S) (x : Ω[P.Ring⁄R])
  proof: by
  simp only [tensorCotangentSpace, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    ← mk_apply s x, IsTensorProduct.assocOfMapSMul_symm_tmul]
  simp only [mk_apply, AlgebraTensorModule.cancelBaseChange_symm_tmul,
    AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply]
  have : 

中文:
引理 tensorCotangentSpace_tmul_tmul
  条件: (t : T) (s : S) (x : Ω[P.环⁄R])
  证明: by
  simp only [tensorCotangentSpace, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    ← mk_apply s x, IsTensorProduct.assocOfMapSMul_symm_tmul]
  simp only [mk_apply, AlgebraTensorModule.cancelBaseChange_symm_tmul,
    AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply]
  have : 

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.cancelBaseChange_symm_tmul, AlgebraTensorModule.congr_tmul, IsTensorProduct, IsTensorProduct.assocOfMapSMul_symm_tmul, KaehlerDifferential, KaehlerDifferential.D, KaehlerDifferential.span_range_derivation, LinearEquiv, LinearEquiv.refl_apply, LinearEquiv.restrictScalars_apply, LinearEquiv.trans_apply, P.Ring, Set.range, Submodule, Submodule.span, Submodule.span_induction, assocOfMapSMul_symm_tmul, cancelBaseChange_symm_tmul, congr_tmul
-/
lemma tensorCotangentSpace_tmul_tmul (t : T) (s : S) (x : Ω[P.Ring⁄R]) :
    P.tensorCotangentSpace T (t otimesₜ (s otimesₜ x)) = t otimesₜ s otimesₜ KaehlerDifferential.map _ _ _ _ x := by
  simp only [tensorCotangentSpace, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    ← mk_apply s x, IsTensorProduct.assocOfMapSMul_symm_tmul]
  simp only [mk_apply, AlgebraTensorModule.cancelBaseChange_symm_tmul,
    AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply]
  have : x in Submodule.span P.Ring (Set.range (KaehlerDifferential.D R P.Ring)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction this using Submodule.span_induction with
  | zero => simp
  | add x y _ _ hx hy => simp [tmul_add, hx, hy]
  | mem y hy =>
    obtain ⟨y, rfl⟩ := hy
    simp
  | smul a x _ hx =>
    rw [tmul_smul]; rw [← algebraMap_smul (P.baseChange (T := T)).Ring a]; rw [LinearEquiv.map_smul]; rw [tmul_smul]; rw [hx]; rw [LinearMap.map_smul]; rw [← algebraMap_smul (P.baseChange (T := T)).Ring a]; rw [tmul_smul]

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
@[simp]
/--
lemma `tensorCotangentSpace_tmul` / 引理 `tensorCotangentSpace_tmul`

English:
lemma tensorCotangentSpace_tmul
  given: (t : T) (x : P.CotangentSpace)
  proof: by
  dsimp only [CotangentSpace] at x
  induction x with
  | zero => rw [tmul_zero, LinearEquiv.map_zero, LinearMap.map_zero, smul_zero]
  | add x y hx hy => rw [tmul_add, LinearEquiv.map_add, LinearMap.map_add, smul_add, hx, hy]
  | tmul s y =>
  simp [tensorCotangentSpace_tmul_tmul, CotangentSpace

中文:
引理 tensorCotangentSpace_tmul
  条件: (t : T) (x : P.CotangentSpace)
  证明: by
  dsimp only [CotangentSpace] at x
  induction x with
  | zero => rw [tmul_zero, LinearEquiv.map_zero, LinearMap.map_zero, smul_zero]
  | add x y hx hy => rw [tmul_add, LinearEquiv.map_add, LinearMap.map_add, smul_add, hx, hy]
  | tmul s y =>
  simp [tensorCotangentSpace_tmul_tmul, CotangentSpace

Depends on / 依赖: Algebra, Algebra.smul_def, CotangentSpace, CotangentSpace.map_tmul_eq_tmul_map, LinearEquiv, LinearEquiv.map_add, LinearEquiv.map_zero, LinearMap, LinearMap.map_add, LinearMap.map_zero, RingHom, RingHom.algebraMap_toAlgebra, algebraMap_toAlgebra, map_add, map_tmul_eq_tmul_map, map_zero, smul_add, smul_def, smul_tmul, smul_zero
-/
lemma tensorCotangentSpace_tmul (t : T) (x : P.CotangentSpace) :
    P.tensorCotangentSpace T (t otimesₜ x) = t • CotangentSpace.map (P.toBaseChange T) x := by
  dsimp only [CotangentSpace] at x
  induction x with
  | zero => rw [tmul_zero, LinearEquiv.map_zero, LinearMap.map_zero, smul_zero]
  | add x y hx hy => rw [tmul_add, LinearEquiv.map_add, LinearMap.map_add, smul_add, hx, hy]
  | tmul s y =>
  simp [tensorCotangentSpace_tmul_tmul, CotangentSpace.map_tmul_eq_tmul_map,
    smul_tmul', Algebra.smul_def, RingHom.algebraMap_toAlgebra]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `tensorCotangentOfFlat` / `tensorCotangentOfFlat` 的定义

English:
definition tensorCotangentOfFlat
  signature: [Module.Flat R T]
  body: AlgebraTensorModule.congr (.refl T T) (P.cotangentEquivCotangentKer.restrictScalars R) ≪≫ₗ
    P.ker.tensorCotangentEquiv R T ≪≫ₗ
    (Ideal.Cotangent.equivOfEq _ _ (P.ker_baseChange T).symm).restrictScalars T ≪≫ₗ
    (P.baseChange (T := T)).cotangentEquivCotangentKer.symm.restrictScalars T

中文:
定义 tensorCotangentOfFlat
  签名: [模.平坦 R T]
  定义体: AlgebraTensorModule.congr (.refl T T) (P.cotangentEquivCotangentKer.restrictScalars R) ≪≫ₗ
    P.ker.tensorCotangentEquiv R T ≪≫ₗ
    (Ideal.Cotangent.equivOfEq _ _ (P.ker_baseChange T).symm).restrictScalars T ≪≫ₗ
    (P.baseChange (T := T)).cotangentEquivCotangentKer.symm.restrictScalars T

Depends on / 依赖: Cotangent
-/
noncomputable def tensorCotangentOfFlat [Module.Flat R T] :
    T otimes[R] P.Cotangent ≃ₗ[T] (P.baseChange (T := T)).Cotangent :=
  AlgebraTensorModule.congr (.refl T T) (P.cotangentEquivCotangentKer.restrictScalars R) ≪≫ₗ
    P.ker.tensorCotangentEquiv R T ≪≫ₗ
    (Ideal.Cotangent.equivOfEq _ _ (P.ker_baseChange T).symm).restrictScalars T ≪≫ₗ
    (P.baseChange (T := T)).cotangentEquivCotangentKer.symm.restrictScalars T

set_option backward.isDefEq.respectTransparency.types false in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
@[simp]
/--
lemma `tensorCotangentOfFlat_tmul` / 引理 `tensorCotangentOfFlat_tmul`

English:
lemma tensorCotangentOfFlat_tmul
  given: [Module.Flat R T] (t : T) (x : P.Cotangent)
  proof: by
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  simp only [tensorCotangentOfFlat, LinearEquiv.trans_apply, AlgebraTensorModule.congr_tmul,
    LinearEquiv.refl_apply, LinearEquiv.restrictScalars_apply, cotangentEquivCotangentKer_apply,
    Cotangent.val_mk, Ideal.tensorCotangentEquiv_tmul, map_s

中文:
引理 tensorCotangentOfFlat_tmul
  条件: [模.平坦 R T] (t : T) (x : P.余切)
  证明: by
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  simp only [tensorCotangentOfFlat, LinearEquiv.trans_apply, AlgebraTensorModule.congr_tmul,
    LinearEquiv.refl_apply, LinearEquiv.restrictScalars_apply, cotangentEquivCotangentKer_apply,
    Cotangent.val_mk, Ideal.tensorCotangentEquiv_tmul, map_s

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.congr_tmul, Cotangent, Cotangent.map_mk, Cotangent.mk_surjective, Cotangent.val_mk, Hom.toAlgHom_apply, Ideal.Cotangent.equivOfEq_toCotangent, Ideal.tensorCotangentEquiv_tmul, LinearEquiv, LinearEquiv.refl_apply, LinearEquiv.restrictScalars_apply, LinearEquiv.trans_apply, congr_tmul, cotangentEquivCotangentKer_apply, equivOfEq_toCotangent, map_mk, map_smul, mk_surjective, refl_apply
-/
lemma tensorCotangentOfFlat_tmul [Module.Flat R T] (t : T) (x : P.Cotangent) :
    P.tensorCotangentOfFlat T (t otimesₜ x) = t • Cotangent.map (P.toBaseChange T) x := by
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  simp only [tensorCotangentOfFlat, LinearEquiv.trans_apply, AlgebraTensorModule.congr_tmul,
    LinearEquiv.refl_apply, LinearEquiv.restrictScalars_apply, cotangentEquivCotangentKer_apply,
    Cotangent.val_mk, Ideal.tensorCotangentEquiv_tmul, map_smul, Cotangent.map_mk,
    Hom.toAlgHom_apply, Ideal.Cotangent.equivOfEq_toCotangent]
  rfl

/-- The canonical map `T ⊗[R] P.H1Cotangent →ₗ[T] (P.baseChange).H1Cotangent`. -/
@[expose]
noncomputable
/--
Definition of `tensorToH1Cotangent` / `tensorToH1Cotangent` 的定义

English:
definition tensorToH1Cotangent
  signature: : T otimes[R] P.H1Cotangent ->ₗ[T] (P.baseChange (T := T)).H1Cotangent
  body: letI : Algebra S (T otimes[R] S) := Algebra.TensorProduct.rightAlgebra
LinearMap.liftBaseChange T
    (Extension.H1Cotangent.map (P.toBaseChange T)).restrictScalars R

中文:
定义 tensorToH1Cotangent
  签名: : T otimes[R] P.H1Cotangent ->ₗ[T] (P.baseChange (T := T)).H1Cotangent
  定义体: letI : Algebra S (T otimes[R] S) := Algebra.TensorProduct.rightAlgebra
LinearMap.liftBaseChange T
    (Extension.H1Cotangent.map (P.toBaseChange T)).restrictScalars R

Depends on / 依赖: H1Cotangent
-/
def tensorToH1Cotangent : T otimes[R] P.H1Cotangent ->ₗ[T] (P.baseChange (T := T)).H1Cotangent :=
  letI : Algebra S (T otimes[R] S) := Algebra.TensorProduct.rightAlgebra
LinearMap.liftBaseChange T
    (Extension.H1Cotangent.map (P.toBaseChange T)).restrictScalars R

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
@[simp]
/--
lemma `tensorToH1Cotangent_tmul` / 引理 `tensorToH1Cotangent_tmul`

English:
lemma tensorToH1Cotangent_tmul
  given: (t : T) (x : P.H1Cotangent)
  proof: rfl

中文:
引理 tensorToH1Cotangent_tmul
  条件: (t : T) (x : P.H1Cotangent)
  证明: rfl
-/
lemma tensorToH1Cotangent_tmul (t : T) (x : P.H1Cotangent) :
    (P.tensorToH1Cotangent T (t otimesₜ x)).val = t • Cotangent.map (P.toBaseChange T) x.val :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `tensorToH1Cotangent_bijective_of_flat` / 引理 `tensorToH1Cotangent_bijective_of_flat`

English:
lemma tensorToH1Cotangent_bijective_of_flat
  given: [Module.Flat R T]
  proof: by
  -- We apply the five lemma.
  apply LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective (M₁ := Unit)
      (N₁ := Unit) (M₂ := Unit) (N₂ := Unit)
    -- The row `0 → 0 → T ⊗ H¹(P) → T ⊗ P.Cotangent → T ⊗ P.CotangentSpace`.
    0 0
    ((P.h1Cotangentι.restrictScalars R).lTe

中文:
引理 tensorToH1Cotangent_bijective_of_flat
  条件: [模.平坦 R T]
  证明: by
  -- We apply the five lemma.
  apply LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective (M₁ := Unit)
      (N₁ := Unit) (M₂ := Unit) (N₂ := Unit)
    -- The row `0 → 0 → T ⊗ H¹(P) → T ⊗ P.Cotangent → T ⊗ P.CotangentSpace`.
    0 0
    ((P.h1Cotangentι.restrictScalars R).lTe
-/
lemma tensorToH1Cotangent_bijective_of_flat [Module.Flat R T] :
    Function.Bijective (P.tensorToH1Cotangent T) := by
  -- We apply the five lemma.
  apply LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective (M₁ := Unit)
      (N₁ := Unit) (M₂ := Unit) (N₂ := Unit)
    -- The row `0 → 0 → T ⊗ H¹(P) → T ⊗ P.Cotangent → T ⊗ P.CotangentSpace`.
    0 0
    ((P.h1Cotangentι.restrictScalars R).lTensor T)
    ((P.cotangentComplex.restrictScalars R).lTensor T)
    -- The row `0 → 0 → H¹(T ⊗ P) → (T ⊗ P).Cotangent → (T ⊗ P).CotangentSpace`.
    0 0
    (h1Cotangentι.restrictScalars R)
    ((P.baseChange (T := T)).cotangentComplex.restrictScalars R)
    -- The vertical maps induced by base change.
    0 0
    ((P.tensorToH1Cotangent T).restrictScalars R)
    ((P.tensorCotangentOfFlat T).restrictScalars R)
    ((P.tensorCotangentSpace T).restrictScalars R)
  · simp
  · simp
  · ext
    simp
  · ext
    simp [CotangentSpace.map_cotangentComplex]
  · tauto
  · simp only [LinearMap.exact_zero_iff_injective]
    apply Module.Flat.lTensor_preserves_injective_linearMap
    exact h1Cotangentι_injective
  · apply Module.Flat.lTensor_exact
    exact P.exact_hCotangentι_cotangentComplex
  · tauto
  · rw [LinearMap.exact_zero_iff_injective]
    simp only [LinearMap.coe_restrictScalars]
    exact h1Cotangentι_injective
  · apply exact_hCotangentι_cotangentComplex
  · tauto
  · simp
  · exact (P.tensorCotangentOfFlat T).bijective
  · exact (P.tensorCotangentSpace T).injective

/-- If `T` is flat over `R`, there is a `T`-linear isomorphism
`T ⊗[R] P.H1Cotangent ≃ₗ[T] (P.baseChange).H1Cotangent`. -/
@[expose]
/--
Definition of `tensorH1CotangentOfFlat` / `tensorH1CotangentOfFlat` 的定义

English:
definition tensorH1CotangentOfFlat
  signature: [Module.Flat R T]
  body: LinearEquiv.ofBijective (P.tensorToH1Cotangent T)
    (P.tensorToH1Cotangent_bijective_of_flat T)

中文:
定义 tensorH1CotangentOfFlat
  签名: [模.平坦 R T]
  定义体: LinearEquiv.ofBijective (P.tensorToH1Cotangent T)
    (P.tensorToH1Cotangent_bijective_of_flat T)

Depends on / 依赖: H1Cotangent
-/
noncomputable def tensorH1CotangentOfFlat [Module.Flat R T] :
    T otimes[R] P.H1Cotangent ≃ₗ[T] (P.baseChange (T := T)).H1Cotangent :=
  LinearEquiv.ofBijective (P.tensorToH1Cotangent T)
    (P.tensorToH1Cotangent_bijective_of_flat T)

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/--
lemma `tensorH1CotangentOfFlat_tmul` / 引理 `tensorH1CotangentOfFlat_tmul`

English:
lemma tensorH1CotangentOfFlat_tmul
  given: [Module.Flat R T] (t : T) (x : P.H1Cotangent)
  proof: rfl

中文:
引理 tensorH1CotangentOfFlat_tmul
  条件: [模.平坦 R T] (t : T) (x : P.H1Cotangent)
  证明: rfl
-/
lemma tensorH1CotangentOfFlat_tmul [Module.Flat R T] (t : T) (x : P.H1Cotangent) :
    P.tensorH1CotangentOfFlat T (t otimesₜ x) = t • H1Cotangent.map (P.toBaseChange T) x :=
  rfl

end Extension

/--
Definition of `tensorH1CotangentOfFlat` / `tensorH1CotangentOfFlat` 的定义

English:
definition tensorH1CotangentOfFlat
  signature: (T : Type*) [CommRing T] [Algebra R T] [Module.Flat R T]
  body: (Generators.self R S).toExtension.tensorH1CotangentOfFlat T ≪≫ₗ
    (Extension.H1Cotangent.equiv
      ((Generators.self R S).baseChangeFromBaseChange T)
      ((Generators.self R S).baseChangeToBaseChange T)).restrictScalars T ≪≫ₗ
    ((Generators.self R S).baseChange (T := T)).equivH1Cotangent.res

中文:
定义 tensorH1CotangentOfFlat
  签名: (T : 类型) [交换环 T] [代数 R T] [模.平坦 R T]
  定义体: (Generators.self R S).toExtension.tensorH1CotangentOfFlat T ≪≫ₗ
    (Extension.H1Cotangent.equiv
      ((Generators.self R S).baseChangeFromBaseChange T)
      ((Generators.self R S).baseChangeToBaseChange T)).restrictScalars T ≪≫ₗ
    ((Generators.self R S).baseChange (T := T)).equivH1Cotangent.res

Depends on / 依赖: Extension, Extension.H1Cotangent.equiv, Generators, Generators.self, H1Cotangent, baseChange, baseChangeFromBaseChange, baseChangeToBaseChange, equivH1Cotangent, equivH1Cotangent.restrictScalars, restrictScalars, tensorH1CotangentOfFlat, toExtension, toExtension.tensorH1CotangentOfFlat
-/
noncomputable def tensorH1CotangentOfFlat (T : Type*) [CommRing T] [Algebra R T] [Module.Flat R T] :
    T otimes[R] H1Cotangent R S ≃ₗ[T] H1Cotangent T (T otimes[R] S) :=
  (Generators.self R S).toExtension.tensorH1CotangentOfFlat T ≪≫ₗ
    (Extension.H1Cotangent.equiv
      ((Generators.self R S).baseChangeFromBaseChange T)
      ((Generators.self R S).baseChangeToBaseChange T)).restrictScalars T ≪≫ₗ
    ((Generators.self R S).baseChange (T := T)).equivH1Cotangent.restrictScalars T

set_option backward.isDefEq.respectTransparency.types false in
attribute [local instance] TensorProduct.rightAlgebra in
/--
lemma `tensorH1CotangentOfFlat_tmul` / 引理 `tensorH1CotangentOfFlat_tmul`

English:
lemma tensorH1CotangentOfFlat_tmul
  statement: (T : Type*) [CommRing T] [Algebra R T] [Module.Flat R T]
  proof: by
  simp only [tensorH1CotangentOfFlat, LinearEquiv.trans_apply,
    Extension.tensorH1CotangentOfFlat_tmul, map_smul, LinearEquiv.restrictScalars_apply,
    Extension.H1Cotangent.equiv, LinearEquiv.coe_mk, Generators.equivH1Cotangent,
    Generators.H1Cotangent.equiv]
  rw [← Extension.H1Cotangent

中文:
引理 tensorH1CotangentOfFlat_tmul
  结论: (T : 类型) [交换环 T] [代数 R T] [模.平坦 R T]
  证明: by
  simp only [tensorH1CotangentOfFlat, LinearEquiv.trans_apply,
    Extension.tensorH1CotangentOfFlat_tmul, map_smul, LinearEquiv.restrictScalars_apply,
    Extension.H1Cotangent.equiv, LinearEquiv.coe_mk, Generators.equivH1Cotangent,
    Generators.H1Cotangent.equiv]
  rw [← Extension.H1Cotangent

Depends on / 依赖: Extension, Extension.H1Cotangent.equiv, Extension.H1Cotangent.map_comp_apply, Extension.H1Cotangent.map_eq, Extension.tensorH1CotangentOfFlat_tmul, Generators, Generators.H1Cotangent.equiv, Generators.equivH1Cotangent, H1Cotangent, H1Cotangent.map, LinearEquiv, LinearEquiv.coe_mk, LinearEquiv.restrictScalars_apply, LinearEquiv.trans_apply, coe_mk, equivH1Cotangent, map_comp_apply, map_eq, map_smul, restrictScalars_apply
-/
lemma tensorH1CotangentOfFlat_tmul (T : Type*) [CommRing T] [Algebra R T] [Module.Flat R T]
    (t : T) (x : H1Cotangent R S) :
    tensorH1CotangentOfFlat R S T (t otimesₜ x) = t • H1Cotangent.map _ _ _ _ x := by
  simp only [tensorH1CotangentOfFlat, LinearEquiv.trans_apply,
    Extension.tensorH1CotangentOfFlat_tmul, map_smul, LinearEquiv.restrictScalars_apply,
    Extension.H1Cotangent.equiv, LinearEquiv.coe_mk, Generators.equivH1Cotangent,
    Generators.H1Cotangent.equiv]
  rw [← Extension.H1Cotangent.map_comp_apply]; rw [← Extension.H1Cotangent.map_comp_apply]; rw [H1Cotangent.map]; rw [Extension.H1Cotangent.map_eq]

end Algebra
