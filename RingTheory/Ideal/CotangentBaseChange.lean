/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Base change of cotangent spaces

Given an `R`-algebra `S`, an ideal `I` of `S` and a flat `R`-algebra `T`, we show that
the base change `T ⊗[R] I/I²` of the cotangent space of `I` is naturally isomorphic to the
cotangent space of the extended ideal `I · (T ⊗[R] S)`.

## Main definitions

- `Ideal.tensorCotangentHom`: The canonical map `T ⊗[R] I/I² → (I · (T ⊗[R] S))/(I · (T ⊗[R] S))²`.
- `Ideal.tensorCotangentEquiv`: When `T` is `R`-flat, `tensorCotangentHom` is an isomorphism.
-/

@[expose] public noncomputable section

universe u

open TensorProduct

namespace Ideal

variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (T : Type*) [CommRing T] [Algebra R T] (I : Ideal S)

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/--
Definition of `tensorCotangentHom` / `tensorCotangentHom` 的定义

English:
definition tensorCotangentHom
  signature: :
  body: LinearMap.liftBaseChange T
    Cotangent.lift
      ((map (algebraMap S (T otimes[R] S)) I).toCotangent.restrictScalars R ∘ₗ
        (Algebra.idealMap _ I).restrictScalars R) <| fun x y => by
    simp only [AlgHom.toRingHom_eq_coe, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
      Function.comp_apply, Algebra.idealMap_mul]
    simp only [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, LinearMap.coe_restrictScalars,
      toCotangent_eq_zero, sq, MulMemClass.coe_mul]
    exact mul_mem_mul ((Algebra.idealMap (T otimes[R] S) I) x).property
      ((Algebra.idealMap (T otimes[R] S) I) y).property

中文:
定义 tensorCotangentHom
  签名: :
  定义体: LinearMap.liftBaseChange T
    Cotangent.lift
      ((map (algebraMap S (T otimes[R] S)) I).toCotangent.restrictScalars R ∘ₗ
        (Algebra.idealMap _ I).restrictScalars R) <| fun x y => by
    simp only [AlgHom.toRingHom_eq_coe, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
      Function.comp_apply, Algebra.idealMap_mul]
    simp only [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, LinearMap.coe_restrictScalars,
      toCotangent_eq_zero, sq, MulMemClass.coe_mul]
    exact mul_mem_mul ((Algebra.idealMap (T otimes[R] S) I) x).property
      ((Algebra.idealMap (T otimes[R] S) I) y).property

Depends on / 依赖: AlgHom, AlgHom.toRingHom_eq_coe, Algebra, Algebra.idealMap, Algebra.idealMap_mul, Cotangent, Cotangent.lift, Function, Function.comp_apply, LinearMap, LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearMap.liftBaseChange, MulMemClass, MulMemClass.coe_mul, RingHom, RingHom.algebraMap_toAlgebra, algebraMap, algebraMap_toAlgebra, coe_comp
-/
def tensorCotangentHom :
    T otimes[R] I.Cotangent ->ₗ[T]
      (I.map <| (Algebra.TensorProduct.includeRight.toRingHom : S ->+* T otimes[R] S)).Cotangent :=
LinearMap.liftBaseChange T
    Cotangent.lift
      ((map (algebraMap S (T otimes[R] S)) I).toCotangent.restrictScalars R ∘ₗ
        (Algebra.idealMap _ I).restrictScalars R) <| fun x y => by
    simp only [AlgHom.toRingHom_eq_coe, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
      Function.comp_apply, Algebra.idealMap_mul]
    simp only [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, LinearMap.coe_restrictScalars,
      toCotangent_eq_zero, sq, MulMemClass.coe_mul]
    exact mul_mem_mul ((Algebra.idealMap (T otimes[R] S) I) x).property
      ((Algebra.idealMap (T otimes[R] S) I) y).property

-- TODO: make this @[simp] when `Ideal.map` is refactored to only take `RingHom`s
/--
lemma `tensorCotangentHom_tmul` / 引理 `tensorCotangentHom_tmul`

English:
lemma tensorCotangentHom_tmul
  given: (t : T) (x : I)
  proof: by
  rfl

中文:
引理 tensorCotangentHom_tmul
  条件: (t : T) (x : I)
  证明: by
  rfl
-/
lemma tensorCotangentHom_tmul (t : T) (x : I) :
    tensorCotangentHom R T I (t otimesₜ[R] I.toCotangent x) =
      t • (I.map (Algebra.TensorProduct.includeRight.toRingHom : S ->+* T otimes[R] S)).toCotangent
        ⟨1 otimesₜ x, Ideal.mem_map_of_mem _ x.2⟩ := by
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `tensorCotangentHom_surjective` / 引理 `tensorCotangentHom_surjective`

English:
lemma tensorCotangentHom_surjective
  proof: by
  let a : S ->+* T otimes[R] S := Algebra.TensorProduct.includeRight.toRingHom
  intro x
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ x
  obtain ⟨y, rfl⟩ := I.map_includeRight_eq.le hx
  obtain rfl : hx = I.map_includeRight_eq.ge ⟨y, rfl⟩ := rfl
  induction y with
  | zero => exact ⟨0, by simp only [map_zero]; exact (map_zero _).symm⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp only [map_add, ha, hb]; rfl⟩
  | tmul t x =>
    use t otimesₜ I.toCotangent x
    apply Ideal.cotangentToQuotientSquare_injective
    simp [-AlgHom.toRingHom_eq_coe, tensorCotangentHom_tmul, Algebra.smul_def,
      ← Ideal.Quotient.mk_algebraMap, ← map_mul]

中文:
引理 tensorCotangentHom_surjective
  证明: by
  let a : S ->+* T otimes[R] S := Algebra.TensorProduct.includeRight.toRingHom
  intro x
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ x
  obtain ⟨y, rfl⟩ := I.map_includeRight_eq.le hx
  obtain rfl : hx = I.map_includeRight_eq.ge ⟨y, rfl⟩ := rfl
  induction y with
  | zero => exact ⟨0, by simp only [map_zero]; exact (map_zero _).symm⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp only [map_add, ha, hb]; rfl⟩
  | tmul t x =>
    use t otimesₜ I.toCotangent x
    apply Ideal.cotangentToQuotientSquare_injective
    simp [-AlgHom.toRingHom_eq_coe, tensorCotangentHom_tmul, Algebra.smul_def,
      ← Ideal.Quotient.mk_algebraMap, ← map_mul]

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeRight.toRingHom, I.map_includeRight_eq.ge, I.map_includeRight_eq.le, I.toCotangent, Ideal.toCotangent_surjective, TensorProduct, includeRight, map_add, map_includeRight_eq, map_zero, otimes, toCotangent, toCotangent_surjective, toRingHom
-/
lemma tensorCotangentHom_surjective :
    Function.Surjective (I.tensorCotangentHom R T) := by
  let a : S ->+* T otimes[R] S := Algebra.TensorProduct.includeRight.toRingHom
  intro x
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ x
  obtain ⟨y, rfl⟩ := I.map_includeRight_eq.le hx
  obtain rfl : hx = I.map_includeRight_eq.ge ⟨y, rfl⟩ := rfl
  induction y with
  | zero => exact ⟨0, by simp only [map_zero]; exact (map_zero _).symm⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp only [map_add, ha, hb]; rfl⟩
  | tmul t x =>
    use t otimesₜ I.toCotangent x
    apply Ideal.cotangentToQuotientSquare_injective
    simp [-AlgHom.toRingHom_eq_coe, tensorCotangentHom_tmul, Algebra.smul_def,
      ← Ideal.Quotient.mk_algebraMap, ← map_mul]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `tensorCotangentHom_injective_of_flat` / 引理 `tensorCotangentHom_injective_of_flat`

English:
lemma tensorCotangentHom_injective_of_flat
  given: [Module.Flat R T]
  proof: by
  let a : S ->+* T otimes[R] S := Algebra.TensorProduct.includeRight.toRingHom
  let f : (I.map a).Cotangent ->ₗ[T] T otimes[R] S ⧸ (I.map a) ^ 2 :=
    (Ideal.cotangentToQuotientSquare _).restrictScalars T
  suffices h : Function.Injective (f ∘ₗ tensorCotangentHom R T I) from .of_comp h
  let g : T otimes[R] I.Cotangent ->ₗ[T] T otimes[R] (S ⧸ I ^ 2) :=
    AlgebraTensorModule.lTensor T T I.cotangentToQuotientSquare
  let hₐ : T otimes[R] (S ⧸ I ^ 2) ≃ₐ[T] T otimes[R] S ⧸ (I.map a) ^ 2 :=
    (Algebra.TensorProduct.tensorQuotientEquiv _ _ _ _).trans
      (Ideal.quotientEquivAlgOfEq T (Ideal.map_pow _ _ _))
  have : f ∘ₗ tensorCotangentHom R T I = hₐ.toLinearMap ∘ₗ g := by
    ext x
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    dsimp [f, g, hₐ]
    rw [tensorCotangentHom_tmul]; rw [one_smul]; rw [Ideal.toCotangent_to_quotient_square]
    simp
  rw [this]; rw [LinearMap.coe_comp]
  apply hₐ.injective.comp
  · apply Module.Flat.lTensor_preserves_injective_linearMap (M := T)
      (I.cotangentToQuotientSquare.restrictScalars R)
    apply cotangentToQuotientSquare_injective

中文:
引理 tensorCotangentHom_injective_of_flat
  条件: [模.平坦 R T]
  证明: by
  let a : S ->+* T otimes[R] S := Algebra.TensorProduct.includeRight.toRingHom
  let f : (I.map a).Cotangent ->ₗ[T] T otimes[R] S ⧸ (I.map a) ^ 2 :=
    (Ideal.cotangentToQuotientSquare _).restrictScalars T
  suffices h : Function.Injective (f ∘ₗ tensorCotangentHom R T I) from .of_comp h
  let g : T otimes[R] I.Cotangent ->ₗ[T] T otimes[R] (S ⧸ I ^ 2) :=
    AlgebraTensorModule.lTensor T T I.cotangentToQuotientSquare
  let hₐ : T otimes[R] (S ⧸ I ^ 2) ≃ₐ[T] T otimes[R] S ⧸ (I.map a) ^ 2 :=
    (Algebra.TensorProduct.tensorQuotientEquiv _ _ _ _).trans
      (Ideal.quotientEquivAlgOfEq T (Ideal.map_pow _ _ _))
  have : f ∘ₗ tensorCotangentHom R T I = hₐ.toLinearMap ∘ₗ g := by
    ext x
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    dsimp [f, g, hₐ]
    rw [tensorCotangentHom_tmul]; rw [one_smul]; rw [Ideal.toCotangent_to_quotient_square]
    simp
  rw [this]; rw [LinearMap.coe_comp]
  apply hₐ.injective.comp
  · apply Module.Flat.lTensor_preserves_injective_linearMap (M := T)
      (I.cotangentToQuotientSquare.restrictScalars R)
    apply cotangentToQuotientSquare_injective

Depends on / 依赖: Algebra, Algebra.TensorProdu, Algebra.TensorProduct.includeRight.toRingHom, AlgebraTensorModule, AlgebraTensorModule.lTensor, Cotangent, Function, Function.Injective, I.Cotangent, I.cotangentToQuotientSquare, I.map, Ideal.cotangentToQuotientSquare, Injective, TensorProdu, TensorProduct, cotangentToQuotientSquare, includeRight, lTensor, of_comp, otimes
-/
lemma tensorCotangentHom_injective_of_flat [Module.Flat R T] :
    Function.Injective (I.tensorCotangentHom R T) := by
  let a : S ->+* T otimes[R] S := Algebra.TensorProduct.includeRight.toRingHom
  let f : (I.map a).Cotangent ->ₗ[T] T otimes[R] S ⧸ (I.map a) ^ 2 :=
    (Ideal.cotangentToQuotientSquare _).restrictScalars T
  suffices h : Function.Injective (f ∘ₗ tensorCotangentHom R T I) from .of_comp h
  let g : T otimes[R] I.Cotangent ->ₗ[T] T otimes[R] (S ⧸ I ^ 2) :=
    AlgebraTensorModule.lTensor T T I.cotangentToQuotientSquare
  let hₐ : T otimes[R] (S ⧸ I ^ 2) ≃ₐ[T] T otimes[R] S ⧸ (I.map a) ^ 2 :=
    (Algebra.TensorProduct.tensorQuotientEquiv _ _ _ _).trans
      (Ideal.quotientEquivAlgOfEq T (Ideal.map_pow _ _ _))
  have : f ∘ₗ tensorCotangentHom R T I = hₐ.toLinearMap ∘ₗ g := by
    ext x
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    dsimp [f, g, hₐ]
    rw [tensorCotangentHom_tmul]; rw [one_smul]; rw [Ideal.toCotangent_to_quotient_square]
    simp
  rw [this]; rw [LinearMap.coe_comp]
  apply hₐ.injective.comp
  · apply Module.Flat.lTensor_preserves_injective_linearMap (M := T)
      (I.cotangentToQuotientSquare.restrictScalars R)
    apply cotangentToQuotientSquare_injective

/--
Definition of `tensorCotangentEquiv` / `tensorCotangentEquiv` 的定义

English:
definition tensorCotangentEquiv
  signature: [Module.Flat R T]
  body: LinearEquiv.ofBijective (I.tensorCotangentHom R T)
    ⟨I.tensorCotangentHom_injective_of_flat R T, I.tensorCotangentHom_surjective R T⟩

中文:
定义 tensorCotangentEquiv
  签名: [模.平坦 R T]
  定义体: LinearEquiv.ofBijective (I.tensorCotangentHom R T)
    ⟨I.tensorCotangentHom_injective_of_flat R T, I.tensorCotangentHom_surjective R T⟩

Depends on / 依赖: I.tensorCotangentHom, I.tensorCotangentHom_injective_of_flat, I.tensorCotangentHom_surjective, LinearEquiv, LinearEquiv.ofBijective, ofBijective, tensorCotangentHom, tensorCotangentHom_injective_of_flat, tensorCotangentHom_surjective
-/
def tensorCotangentEquiv [Module.Flat R T] :
    T otimes[R] I.Cotangent ≃ₗ[T]
      (I.map (Algebra.TensorProduct.includeRight.toRingHom : _ ->+* T otimes[R] S)).Cotangent :=
  LinearEquiv.ofBijective (I.tensorCotangentHom R T)
    ⟨I.tensorCotangentHom_injective_of_flat R T, I.tensorCotangentHom_surjective R T⟩

-- TODO: make this @[simp] when `Ideal.map` is refactored to only take `RingHom`s
/--
lemma `tensorCotangentEquiv_tmul` / 引理 `tensorCotangentEquiv_tmul`

English:
lemma tensorCotangentEquiv_tmul
  given: [Module.Flat R T] (t : T) (x : I)
  proof: rfl

中文:
引理 tensorCotangentEquiv_tmul
  条件: [模.平坦 R T] (t : T) (x : I)
  证明: rfl
-/
lemma tensorCotangentEquiv_tmul [Module.Flat R T] (t : T) (x : I) :
    I.tensorCotangentEquiv R T (t otimesₜ I.toCotangent x) =
      t • (I.map (Algebra.TensorProduct.includeRight.toRingHom : S ->+* T otimes[R] S)).toCotangent
        ⟨1 otimesₜ x, Ideal.mem_map_of_mem _ x.2⟩ :=
  rfl

end Ideal
