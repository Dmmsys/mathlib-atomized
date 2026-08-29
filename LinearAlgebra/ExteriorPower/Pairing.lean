/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Sophie Morel
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.TensorPower.Pairing

/-!
# The pairing between the exterior power of the dual and the exterior power

We construct the pairing
`exteriorPower.pairingDual : ⋀[R]^n (Module.Dual R M) →ₗ[R] (Module.Dual R (⋀[R]^n M))`.

-/

@[expose] public section

namespace exteriorPower

open TensorProduct PiTensorProduct

variable (R : Type*) (M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/--
Definition of `toTensorPower` / `toTensorPower` 的定义

English:
definition toTensorPower
  signature: (n : Nat)
  body: alternatingMapLinearEquiv (MultilinearMap.alternatization (PiTensorProduct.tprod R))

中文:
定义 toTensorPower
  签名: (n : 自然数)
  定义体: alternatingMapLinearEquiv (MultilinearMap.alternatization (PiTensorProduct.tprod R))

Depends on / 依赖: MultilinearMap, MultilinearMap.alternatization, PiTensorProduct, PiTensorProduct.tprod, alternatingMapLinearEquiv, alternatization
-/
noncomputable def toTensorPower (n : Nat) : ⋀[R]^n M ->ₗ[R] ⨂[R]^n M :=
  alternatingMapLinearEquiv (MultilinearMap.alternatization (PiTensorProduct.tprod R))

variable {M} in
open Equiv in
@[simp]
/--
lemma `toTensorPower_apply_ιMulti` / 引理 `toTensorPower_apply_ιMulti`

English:
lemma toTensorPower_apply_ιMulti
  given: {n : Nat} (v : Fin n -> M)
  proof: by
  dsimp [toTensorPower]
  simp only [alternatingMapLinearEquiv_apply_ιMulti,
    MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply]

中文:
引理 toTensorPower_apply_ιMulti
  条件: {n : 自然数} (v : 有限集 n -> M)
  证明: by
  dsimp [toTensorPower]
  simp only [alternatingMapLinearEquiv_apply_ιMulti,
    MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply]

Depends on / 依赖: MultilinearMap, MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply, alternatization_apply, domDomCongr_apply, toTensorPower
-/
lemma toTensorPower_apply_ιMulti {n : Nat} (v : Fin n -> M) :
    toTensorPower R M n (ιMulti R n v) =
      ∑ σ : Perm (Fin n), Perm.sign σ • PiTensorProduct.tprod R (fun i => v (σ i)) := by
  dsimp [toTensorPower]
  simp only [alternatingMapLinearEquiv_apply_ιMulti,
    MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply]

/--
Definition of `alternatingMapToDual` / `alternatingMapToDual` 的定义

English:
definition alternatingMapToDual
  signature: (n : Nat)
  body: (toTensorPower R M n).dualMap.compMultilinearMap
    (TensorPower.multilinearMapToDual R M n)
  map_eq_zero_of_eq' f i j hf hij := by
    ext v
    suffices Matrix.det (n := Fin n) (.of (fun i j => f j (v i))) = 0 by
      simpa [Matrix.det_apply] using this
    exact Matrix.det_zero_of_column_eq hij (by simp [hf])

中文:
定义 alternatingMapToDual
  签名: (n : 自然数)
  定义体: (toTensorPower R M n).dualMap.compMultilinearMap
    (TensorPower.multilinearMapToDual R M n)
  map_eq_zero_of_eq' f i j hf hij := by
    ext v
    suffices Matrix.det (n := Fin n) (.of (fun i j => f j (v i))) = 0 by
      simpa [Matrix.det_apply] using this
    exact Matrix.det_zero_of_column_eq hij (by simp [hf])

Depends on / 依赖: compMultilinearMap, dualMap, dualMap.compMultilinearMap, toTensorPower
-/
noncomputable def alternatingMapToDual (n : Nat) :
    AlternatingMap R (Module.Dual R M) (Module.Dual R (⋀[R]^n M)) (Fin n) where
  toMultilinearMap := (toTensorPower R M n).dualMap.compMultilinearMap
    (TensorPower.multilinearMapToDual R M n)
  map_eq_zero_of_eq' f i j hf hij := by
    ext v
    suffices Matrix.det (n := Fin n) (.of (fun i j => f j (v i))) = 0 by
      simpa [Matrix.det_apply] using this
    exact Matrix.det_zero_of_column_eq hij (by simp [hf])

variable {R M} in
open Equiv in
@[simp]
/--
theorem `alternatingMapToDual_apply_ιMulti` / 定理 `alternatingMapToDual_apply_ιMulti`

English:
theorem alternatingMapToDual_apply_ιMulti
  statement: {n : Nat}
  proof: by
  simp [alternatingMapToDual, Matrix.det_apply]

中文:
定理 alternatingMapToDual_apply_ιMulti
  结论: {n : 自然数}
  证明: by
  simp [alternatingMapToDual, Matrix.det_apply]

Depends on / 依赖: Matrix, Matrix.det_apply, alternatingMapToDual, det_apply
-/
theorem alternatingMapToDual_apply_ιMulti {n : Nat}
    (f : (_ : Fin n) -> Module.Dual R M) (v : Fin n -> M) :
    alternatingMapToDual R M n f (ιMulti _ _ v) =
      Matrix.det (n := Fin n) (.of (fun i j => f j (v i))) := by
  simp [alternatingMapToDual, Matrix.det_apply]

/--
Definition of `pairingDual` / `pairingDual` 的定义

English:
definition pairingDual
  signature: (n : Nat)
  body: alternatingMapLinearEquiv (alternatingMapToDual R M n)

中文:
定义 pairingDual
  签名: (n : 自然数)
  定义体: alternatingMapLinearEquiv (alternatingMapToDual R M n)

Depends on / 依赖: alternatingMapLinearEquiv, alternatingMapToDual
-/
noncomputable def pairingDual (n : Nat) :
    ⋀[R]^n (Module.Dual R M) ->ₗ[R] Module.Dual R (⋀[R]^n M) :=
  alternatingMapLinearEquiv (alternatingMapToDual R M n)

variable {R M} in
open Equiv in
@[simp]
/--
lemma `pairingDual_ιMulti_ιMulti` / 引理 `pairingDual_ιMulti_ιMulti`

English:
lemma pairingDual_ιMulti_ιMulti
  given: {n : Nat} (f : (_ : Fin n) -> Module.Dual R M) (v : Fin n -> M)
  proof: by
  simp [pairingDual]

中文:
引理 pairingDual_ιMulti_ιMulti
  条件: {n : 自然数} (f : (_ : 有限集 n) -> 模.对偶 R M) (v : 有限集 n -> M)
  证明: by
  simp [pairingDual]

Depends on / 依赖: pairingDual
-/
lemma pairingDual_ιMulti_ιMulti {n : Nat} (f : (_ : Fin n) -> Module.Dual R M) (v : Fin n -> M) :
    pairingDual R M n (ιMulti _ _ f) (ιMulti _ _ v) =
      Matrix.det (n := Fin n) (.of (fun i j => f j (v i))) := by
  simp [pairingDual]


section

/-! If an `R`-module `M` has a family of vectors `x : ι → M` and linear maps `f : ι → M`
such that `f i (x j)` is `1` or `0` depending on `i = j` or `i ≠ j`, then if `ι` has
a linear order, then a similar property regarding `pairingDual R M n`
applies to the family of vectors indexed
by `Fin n ↪o ι` in `⋀[R]^n M` and in `⋀[R]^n (Module.Dual R M)` that are obtained
by taking exterior products of the `x i` and the `f j`. (This shall be used in order
to construct a basis of `⋀[R]^n M` when `M` is a free module.) -/

variable {R M} {ι : Type*} [LinearOrder ι]
  (x : ι -> M) (f : ι -> Module.Dual R M)
  (h₁ : forall i, f i (x i) = 1) (h₀ : forall ⦃i j⦄, i != j -> f i (x j) = 0) (n : Nat)

include h₁ h₀ in
/--
lemma `pairingDual_apply_apply_eq_one` / 引理 `pairingDual_apply_apply_eq_one`

English:
lemma pairingDual_apply_apply_eq_one
  given: (a : Fin n ↪o ι)
  proof: by
  simp only [pairingDual_ιMulti_ιMulti, Function.comp_apply]
  rw [← Matrix.det_one (n := Fin n)]
  congr
  ext i j
  dsimp
  by_cases hij : i = j
  · subst hij
    simp only [h₁, Matrix.one_apply_eq]
  · rw [h₀ (by simpa using Ne.symm hij), Matrix.one_apply_ne hij]

include h₀ in

中文:
引理 pairingDual_apply_apply_eq_one
  条件: (a : 有限集 n ↪o ι)
  证明: by
  simp only [pairingDual_ιMulti_ιMulti, Function.comp_apply]
  rw [← Matrix.det_one (n := Fin n)]
  congr
  ext i j
  dsimp
  by_cases hij : i = j
  · subst hij
    simp only [h₁, Matrix.one_apply_eq]
  · rw [h₀ (by simpa using Ne.symm hij), Matrix.one_apply_ne hij]

include h₀ in

Depends on / 依赖: Function, Function.comp_apply, Matrix, Matrix.det_one, Matrix.one_apply_eq, Matrix.one_apply_ne, Ne.symm, comp_apply, det_one, one_apply_eq, one_apply_ne
-/
lemma pairingDual_apply_apply_eq_one (a : Fin n ↪o ι) :
    pairingDual R M n (ιMulti _ _ (f ∘ a)) (ιMulti _ _ (x ∘ a)) = 1 := by
  simp only [pairingDual_ιMulti_ιMulti, Function.comp_apply]
  rw [← Matrix.det_one (n := Fin n)]
  congr
  ext i j
  dsimp
  by_cases hij : i = j
  · subst hij
    simp only [h₁, Matrix.one_apply_eq]
  · rw [h₀ (by simpa using Ne.symm hij), Matrix.one_apply_ne hij]

include h₀ in
/--
lemma `pairingDual_apply_apply_eq_one_zero` / 引理 `pairingDual_apply_apply_eq_one_zero`

English:
lemma pairingDual_apply_apply_eq_one_zero
  given: (a b : Fin n ↪o ι) (h : a != b)
  proof: by
  simp only [pairingDual_ιMulti_ιMulti, Function.comp_apply, Matrix.det_apply]
  refine Finset.sum_eq_zero (fun σ _ => ?_)
  simp only [Matrix.of_apply, smul_eq_iff_eq_inv_smul, smul_zero]
  by_contra h'
  apply h
  have : a = b ∘ σ := by
    ext i
    by_contra hi
    exact h' (Finset.prod_eq_zero (i := i) (by simp) (h₀ hi))
  have hσ : Monotone σ := fun i j hij => by
    have h'' := congr_fun this
    dsimp at h''
    rw [← a.map_rel_iff] at hij
    simpa only [← b.map_rel_iff, ← h'']
  have hσ' : Monotone σ.symm := fun i j hij => by
    obtain ⟨i, rfl⟩ := σ.surjective i
    obtain ⟨j, rfl⟩ := σ.surjective j
    simp only [Equiv.symm_apply_apply]
    by_contra! h
    obtain rfl : i = j := σ.injective (le_antisymm hij (hσ h.le))
    simp only [lt_self_iff_false] at h
  obtain rfl : σ = 1 := by
    ext i : 1
    exact DFunLike.congr_fun (Subsingleton.elim (σ.toOrderIso hσ hσ') (OrderIso.refl _)) i
  ext
  apply congr_fun this

中文:
引理 pairingDual_apply_apply_eq_one_zero
  条件: (a b : 有限集 n ↪o ι) (h : a != b)
  证明: by
  simp only [pairingDual_ιMulti_ιMulti, Function.comp_apply, Matrix.det_apply]
  refine Finset.sum_eq_zero (fun σ _ => ?_)
  simp only [Matrix.of_apply, smul_eq_iff_eq_inv_smul, smul_zero]
  by_contra h'
  apply h
  have : a = b ∘ σ := by
    ext i
    by_contra hi
    exact h' (Finset.prod_eq_zero (i := i) (by simp) (h₀ hi))
  have hσ : Monotone σ := fun i j hij => by
    have h'' := congr_fun this
    dsimp at h''
    rw [← a.map_rel_iff] at hij
    simpa only [← b.map_rel_iff, ← h'']
  have hσ' : Monotone σ.symm := fun i j hij => by
    obtain ⟨i, rfl⟩ := σ.surjective i
    obtain ⟨j, rfl⟩ := σ.surjective j
    simp only [Equiv.symm_apply_apply]
    by_contra! h
    obtain rfl : i = j := σ.injective (le_antisymm hij (hσ h.le))
    simp only [lt_self_iff_false] at h
  obtain rfl : σ = 1 := by
    ext i : 1
    exact DFunLike.congr_fun (Subsingleton.elim (σ.toOrderIso hσ hσ') (OrderIso.refl _)) i
  ext
  apply congr_fun this

Depends on / 依赖: Finset, Finset.prod_eq_zero, Finset.sum_eq_zero, Function, Function.comp_apply, Matrix, Matrix.det_apply, Matrix.of_apply, Monotone, a.map_rel_iff, b.map_rel_iff, comp_apply, congr_fun, det_apply, map_rel_iff, of_apply, prod_eq_zero, smul_eq_iff_eq_inv_smul, smul_zero, sum_eq_zero
-/
lemma pairingDual_apply_apply_eq_one_zero (a b : Fin n ↪o ι) (h : a != b) :
    pairingDual R M n (ιMulti _ _ (f ∘ a)) (ιMulti _ _ (x ∘ b)) = 0 := by
  simp only [pairingDual_ιMulti_ιMulti, Function.comp_apply, Matrix.det_apply]
  refine Finset.sum_eq_zero (fun σ _ => ?_)
  simp only [Matrix.of_apply, smul_eq_iff_eq_inv_smul, smul_zero]
  by_contra h'
  apply h
  have : a = b ∘ σ := by
    ext i
    by_contra hi
    exact h' (Finset.prod_eq_zero (i := i) (by simp) (h₀ hi))
  have hσ : Monotone σ := fun i j hij => by
    have h'' := congr_fun this
    dsimp at h''
    rw [← a.map_rel_iff] at hij
    simpa only [← b.map_rel_iff, ← h'']
  have hσ' : Monotone σ.symm := fun i j hij => by
    obtain ⟨i, rfl⟩ := σ.surjective i
    obtain ⟨j, rfl⟩ := σ.surjective j
    simp only [Equiv.symm_apply_apply]
    by_contra! h
    obtain rfl : i = j := σ.injective (le_antisymm hij (hσ h.le))
    simp only [lt_self_iff_false] at h
  obtain rfl : σ = 1 := by
    ext i : 1
    exact DFunLike.congr_fun (Subsingleton.elim (σ.toOrderIso hσ hσ') (OrderIso.refl _)) i
  ext
  apply congr_fun this

end

end exteriorPower
