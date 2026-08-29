/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.SurjectiveOnStalks

/-!

# Lemmas regarding the prime spectrum of tensor products

## Main result
- `PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks`:
  If `R →+* T` is surjective on stalks (see `Mathlib/RingTheory/SurjectiveOnStalks.lean`),
  then `Spec(S ⊗[R] T) → Spec S × Spec T` is a topological embedding
  (where `Spec S × Spec T` is the Cartesian product with the product topology).
-/

@[expose] public section

variable (R S T : Type*) [CommRing R] [CommRing S] [Algebra R S]
variable [CommRing T] [Algebra R T]

open TensorProduct Topology

/-- The canonical map from `Spec(S ⊗[R] T)` to the Cartesian product `Spec S × Spec T`. -/
noncomputable
/--
Definition of `PrimeSpectrum.tensorProductTo` / `PrimeSpectrum.tensorProductTo` 的定义

English:
definition PrimeSpectrum.tensorProductTo
  signature: (x : PrimeSpectrum (S otimes[R] T))
  body: ⟨comap (algebraMap _ _) x, comap Algebra.TensorProduct.includeRight.toRingHom x⟩

@[fun_prop]

中文:
定义 素谱.tensorProductTo
  签名: (x : 素谱 (S otimes[R] T))
  定义体: ⟨comap (algebraMap _ _) x, comap Algebra.TensorProduct.includeRight.toRingHom x⟩

@[fun_prop]

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeRight.toRingHom, TensorProduct, algebraMap, includeRight, toRingHom
-/
def PrimeSpectrum.tensorProductTo (x : PrimeSpectrum (S otimes[R] T)) :
    PrimeSpectrum S × PrimeSpectrum T :=
  ⟨comap (algebraMap _ _) x, comap Algebra.TensorProduct.includeRight.toRingHom x⟩

@[fun_prop]
/--
lemma `PrimeSpectrum.continuous_tensorProductTo` / 引理 `PrimeSpectrum.continuous_tensorProductTo`

English:
lemma PrimeSpectrum.continuous_tensorProductTo
  statement: Continuous (tensorProductTo R S T)
  proof: (continuous_comap _).prodMk (continuous_comap _)

中文:
引理 素谱.continuous_tensorProductTo
  结论: 连续 (tensorProductTo R S T)
  证明: (continuous_comap _).prodMk (continuous_comap _)

Depends on / 依赖: continuous_comap, prodMk
-/
lemma PrimeSpectrum.continuous_tensorProductTo : Continuous (tensorProductTo R S T) :=
  (continuous_comap _).prodMk (continuous_comap _)

variable (hRT : (algebraMap R T).SurjectiveOnStalks)
include hRT

/--
lemma `PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks_aux` / 引理 `PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks_aux`

English:
lemma PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks_aux
  proof: by
  let g : T ->+* S otimes[R] T := Algebra.TensorProduct.includeRight.toRingHom
  intro x hxp₁
  by_contra hxp₂
  obtain ⟨t, r, a, ht, e⟩ := hRT.exists_mul_eq_tmul x
    (p₂.asIdeal.comap g) inferInstance
  have h₁ : a otimesₜ[R] t in p₁.asIdeal := e ▸ p₁.asIdeal.mul_mem_left (1 otimesₜ[R] (r • t)) hxp₁
  have h₂ : a otimesₜ[R] t ∉ p₂.asIdeal := e ▸ p₂.asIdeal.primeCompl.mul_mem ht hxp₂
  rw [← mul_one a]; rw [← one_mul t]; rw [← Algebra.TensorProduct.tmul_mul_tmul] at h₁ h₂
  have h₃ : t ∉ p₂.asIdeal.comap g := fun h => h₂ (Ideal.mul_mem_left _ _ h)
  have h₄ : a ∉ p₂.asIdeal.comap (algebraMap S (S otimes[R] T)) :=
    fun h => h₂ (Ideal.mul_mem_right _ _ h)
  replace h₃ : t ∉ p₁.asIdeal.comap g := by
    rwa [show p₁.asIdeal.comap g = p₂.asIdeal.comap g from congr($h.2.1)]
  replace h₄ : a ∉ p₁.asIdeal.comap (algebraMap S (S otimes[R] T)) := by
    rwa [show p₁.asIdeal.comap (algebraMap S (S otimes[R] T)) = p₂.asIdeal.comap _ from congr($h.1.1)]
  exact p₁.asIdeal.primeCompl.mul_mem h₄ h₃ h₁

中文:
引理 素谱.isEmbedding_tensorProductTo_of_surjectiveOnStalks_aux
  证明: by
  let g : T ->+* S otimes[R] T := Algebra.TensorProduct.includeRight.toRingHom
  intro x hxp₁
  by_contra hxp₂
  obtain ⟨t, r, a, ht, e⟩ := hRT.exists_mul_eq_tmul x
    (p₂.asIdeal.comap g) inferInstance
  have h₁ : a otimesₜ[R] t in p₁.asIdeal := e ▸ p₁.asIdeal.mul_mem_left (1 otimesₜ[R] (r • t)) hxp₁
  have h₂ : a otimesₜ[R] t ∉ p₂.asIdeal := e ▸ p₂.asIdeal.primeCompl.mul_mem ht hxp₂
  rw [← mul_one a]; rw [← one_mul t]; rw [← Algebra.TensorProduct.tmul_mul_tmul] at h₁ h₂
  have h₃ : t ∉ p₂.asIdeal.comap g := fun h => h₂ (Ideal.mul_mem_left _ _ h)
  have h₄ : a ∉ p₂.asIdeal.comap (algebraMap S (S otimes[R] T)) :=
    fun h => h₂ (Ideal.mul_mem_right _ _ h)
  replace h₃ : t ∉ p₁.asIdeal.comap g := by
    rwa [show p₁.asIdeal.comap g = p₂.asIdeal.comap g from congr($h.2.1)]
  replace h₄ : a ∉ p₁.asIdeal.comap (algebraMap S (S otimes[R] T)) := by
    rwa [show p₁.asIdeal.comap (algebraMap S (S otimes[R] T)) = p₂.asIdeal.comap _ from congr($h.1.1)]
  exact p₁.asIdeal.primeCompl.mul_mem h₄ h₃ h₁

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeRight.toRingHom, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct, asIdeal, asIdeal.comap, asIdeal.mul_mem_left, asIdeal.primeCompl.mul_mem, exists_mul_eq_tmul, hRT.exists_mul_eq_tmul, includeRight, mul_mem, mul_mem_left, mul_one, one_mul, otimes, primeCompl, tmul_mul_tmul, toRingHom
-/
lemma PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks_aux
    (p₁ p₂ : PrimeSpectrum (S otimes[R] T))
    (h : tensorProductTo R S T p₁ = tensorProductTo R S T p₂) :
    p₁ <= p₂ := by
  let g : T ->+* S otimes[R] T := Algebra.TensorProduct.includeRight.toRingHom
  intro x hxp₁
  by_contra hxp₂
  obtain ⟨t, r, a, ht, e⟩ := hRT.exists_mul_eq_tmul x
    (p₂.asIdeal.comap g) inferInstance
  have h₁ : a otimesₜ[R] t in p₁.asIdeal := e ▸ p₁.asIdeal.mul_mem_left (1 otimesₜ[R] (r • t)) hxp₁
  have h₂ : a otimesₜ[R] t ∉ p₂.asIdeal := e ▸ p₂.asIdeal.primeCompl.mul_mem ht hxp₂
  rw [← mul_one a]; rw [← one_mul t]; rw [← Algebra.TensorProduct.tmul_mul_tmul] at h₁ h₂
  have h₃ : t ∉ p₂.asIdeal.comap g := fun h => h₂ (Ideal.mul_mem_left _ _ h)
  have h₄ : a ∉ p₂.asIdeal.comap (algebraMap S (S otimes[R] T)) :=
    fun h => h₂ (Ideal.mul_mem_right _ _ h)
  replace h₃ : t ∉ p₁.asIdeal.comap g := by
    rwa [show p₁.asIdeal.comap g = p₂.asIdeal.comap g from congr($h.2.1)]
  replace h₄ : a ∉ p₁.asIdeal.comap (algebraMap S (S otimes[R] T)) := by
    rwa [show p₁.asIdeal.comap (algebraMap S (S otimes[R] T)) = p₂.asIdeal.comap _ from congr($h.1.1)]
  exact p₁.asIdeal.primeCompl.mul_mem h₄ h₃ h₁

/--
lemma `PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks` / 引理 `PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks`

English:
lemma PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks
  proof: by
  refine ⟨?_, fun p₁ p₂ e =>
    (isEmbedding_tensorProductTo_of_surjectiveOnStalks_aux R S T hRT p₁ p₂ e).antisymm
      (isEmbedding_tensorProductTo_of_surjectiveOnStalks_aux R S T hRT p₂ p₁ e.symm)⟩
  let g : T ->+* S otimes[R] T := Algebra.TensorProduct.includeRight.toRingHom
  refine ⟨(continuous_tensorProductTo ..).le_induced.antisymm (isBasis_basic_opens.le_iff.mpr ?_)⟩
  rintro _ ⟨f, rfl⟩
  rw [@isOpen_iff_forall_mem_open]
  rintro J (hJ : f ∉ J.asIdeal)
  obtain ⟨t, r, a, ht, e⟩ := hRT.exists_mul_eq_tmul f
    (J.asIdeal.comap g) inferInstance
  refine ⟨_, ?_, ⟨_, (basicOpen a).2.prod (basicOpen t).2, rfl⟩, ?_⟩
  · rintro x ⟨hx₁ : a otimesₜ[R] (1 : T) ∉ x.asIdeal, hx₂ : (1 : S) otimesₜ[R] t ∉ x.asIdeal⟩
      (hx₃ : f in x.asIdeal)
    apply x.asIdeal.primeCompl.mul_mem hx₁ hx₂
    rw [Algebra.TensorProduct.tmul_mul_tmul]; rw [mul_one]; rw [one_mul]; rw [← e]
    exact x.asIdeal.mul_mem_left _ hx₃
  · have : a otimesₜ[R] (1 : T) * (1 : S) otimesₜ[R] t ∉ J.asIdeal := by
      rw [Algebra.TensorProduct.tmul_mul_tmul]; rw [mul_one]; rw [one_mul]; rw [← e]
      exact J.asIdeal.primeCompl.mul_mem ht hJ
    rwa [J.isPrime.mul_mem_iff_mem_or_mem.not, not_or] at this

中文:
引理 素谱.isEmbedding_tensorProductTo_of_surjectiveOnStalks
  证明: by
  refine ⟨?_, fun p₁ p₂ e =>
    (isEmbedding_tensorProductTo_of_surjectiveOnStalks_aux R S T hRT p₁ p₂ e).antisymm
      (isEmbedding_tensorProductTo_of_surjectiveOnStalks_aux R S T hRT p₂ p₁ e.symm)⟩
  let g : T ->+* S otimes[R] T := Algebra.TensorProduct.includeRight.toRingHom
  refine ⟨(continuous_tensorProductTo ..).le_induced.antisymm (isBasis_basic_opens.le_iff.mpr ?_)⟩
  rintro _ ⟨f, rfl⟩
  rw [@isOpen_iff_forall_mem_open]
  rintro J (hJ : f ∉ J.asIdeal)
  obtain ⟨t, r, a, ht, e⟩ := hRT.exists_mul_eq_tmul f
    (J.asIdeal.comap g) inferInstance
  refine ⟨_, ?_, ⟨_, (basicOpen a).2.prod (basicOpen t).2, rfl⟩, ?_⟩
  · rintro x ⟨hx₁ : a otimesₜ[R] (1 : T) ∉ x.asIdeal, hx₂ : (1 : S) otimesₜ[R] t ∉ x.asIdeal⟩
      (hx₃ : f in x.asIdeal)
    apply x.asIdeal.primeCompl.mul_mem hx₁ hx₂
    rw [Algebra.TensorProduct.tmul_mul_tmul]; rw [mul_one]; rw [one_mul]; rw [← e]
    exact x.asIdeal.mul_mem_left _ hx₃
  · have : a otimesₜ[R] (1 : T) * (1 : S) otimesₜ[R] t ∉ J.asIdeal := by
      rw [Algebra.TensorProduct.tmul_mul_tmul]; rw [mul_one]; rw [one_mul]; rw [← e]
      exact J.asIdeal.primeCompl.mul_mem ht hJ
    rwa [J.isPrime.mul_mem_iff_mem_or_mem.not, not_or] at this

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeRight.toRingHom, J.asIdeal, TensorProduct, antisymm, asIdeal, continuous_tensorProductTo, e.symm, exists_mul_eq_tmul, hRT.exists_mul_eq_tmul, includeRight, isBasis_basic_opens, isBasis_basic_opens.le_iff.mpr, isEmbedding_tensorProductTo_of_surjectiveOnStalks_aux, isOpen_iff_forall_mem_open, le_iff, le_induced, le_induced.antisymm, otimes, toRingHom
-/
lemma PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks :
    IsEmbedding (tensorProductTo R S T) := by
  refine ⟨?_, fun p₁ p₂ e =>
    (isEmbedding_tensorProductTo_of_surjectiveOnStalks_aux R S T hRT p₁ p₂ e).antisymm
      (isEmbedding_tensorProductTo_of_surjectiveOnStalks_aux R S T hRT p₂ p₁ e.symm)⟩
  let g : T ->+* S otimes[R] T := Algebra.TensorProduct.includeRight.toRingHom
  refine ⟨(continuous_tensorProductTo ..).le_induced.antisymm (isBasis_basic_opens.le_iff.mpr ?_)⟩
  rintro _ ⟨f, rfl⟩
  rw [@isOpen_iff_forall_mem_open]
  rintro J (hJ : f ∉ J.asIdeal)
  obtain ⟨t, r, a, ht, e⟩ := hRT.exists_mul_eq_tmul f
    (J.asIdeal.comap g) inferInstance
  refine ⟨_, ?_, ⟨_, (basicOpen a).2.prod (basicOpen t).2, rfl⟩, ?_⟩
  · rintro x ⟨hx₁ : a otimesₜ[R] (1 : T) ∉ x.asIdeal, hx₂ : (1 : S) otimesₜ[R] t ∉ x.asIdeal⟩
      (hx₃ : f in x.asIdeal)
    apply x.asIdeal.primeCompl.mul_mem hx₁ hx₂
    rw [Algebra.TensorProduct.tmul_mul_tmul]; rw [mul_one]; rw [one_mul]; rw [← e]
    exact x.asIdeal.mul_mem_left _ hx₃
  · have : a otimesₜ[R] (1 : T) * (1 : S) otimesₜ[R] t ∉ J.asIdeal := by
      rw [Algebra.TensorProduct.tmul_mul_tmul]; rw [mul_one]; rw [one_mul]; rw [← e]
      exact J.asIdeal.primeCompl.mul_mem ht hJ
    rwa [J.isPrime.mul_mem_iff_mem_or_mem.not, not_or] at this
