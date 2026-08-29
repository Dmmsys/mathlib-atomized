/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Module version of Chinese remainder theorem
-/

public section

open Function

variable {R : Type*} [CommRing R] {ι : Type*}
variable (M : Type*) [AddCommGroup M] [Module R M]
variable (I : ι -> Ideal R) (hI : Pairwise (IsCoprime on I))

namespace Ideal

open TensorProduct LinearMap

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `pi_mkQ_rTensor` / 引理 `pi_mkQ_rTensor`

English:
lemma pi_mkQ_rTensor
  given: [Fintype ι] [DecidableEq ι]
  proof: by
  ext; simp [LinearMap.pi, LinearEquiv.piCongrRight]

中文:
引理 pi_mkQ_rTensor
  条件: [有限类型 ι] [DecidableEq ι]
  证明: by
  ext; simp [LinearMap.pi, LinearEquiv.piCongrRight]

Depends on / 依赖: LinearEquiv, LinearEquiv.piCongrRight, LinearMap, LinearMap.pi, piCongrRight
-/
lemma pi_mkQ_rTensor [Fintype ι] [DecidableEq ι] :
    (LinearMap.pi fun i => (I i).mkQ).rTensor M = (piLeft ..).symm.toLinearMap ∘ₗ
      .pi (fun i => TensorProduct.mk R (R ⧸ I i) M 1) ∘ₗ TensorProduct.lid R M := by
  ext; simp [LinearMap.pi, LinearEquiv.piCongrRight]

variable [Finite ι]
include hI

attribute [local instance] Fintype.ofFinite

/--
theorem `pi_tensorProductMk_quotient_surjective` / 定理 `pi_tensorProductMk_quotient_surjective`

English:
theorem pi_tensorProductMk_quotient_surjective
  proof: by
  have := rTensor_surjective M (pi_mkQ_surjective hI)
  classical rw [pi_mkQ_rTensor] at this
  simpa using this

中文:
定理 pi_tensorProductMk_quotient_surjective
  证明: by
  have := rTensor_surjective M (pi_mkQ_surjective hI)
  classical rw [pi_mkQ_rTensor] at this
  simpa using this

Depends on / 依赖: classical, pi_mkQ_rTensor, pi_mkQ_surjective, rTensor_surjective
-/
theorem pi_tensorProductMk_quotient_surjective :
    Surjective (LinearMap.pi fun i => TensorProduct.mk R (R ⧸ I i) M 1) := by
  have := rTensor_surjective M (pi_mkQ_surjective hI)
  classical rw [pi_mkQ_rTensor] at this
  simpa using this

/--
theorem `ker_tensorProductMk_quotient` / 定理 `ker_tensorProductMk_quotient`

English:
theorem ker_tensorProductMk_quotient
  proof: by
  have := rTensor_exact M (exact_subtype_ker_map _) (pi_mkQ_surjective hI)
  rw [← (TensorProduct.lid R M).conj_exact_iff_exact]; rw [exact_iff] at this
  convert! this
  · classical simp [pi_mkQ_rTensor, LinearMap.comp_assoc]
  refine le_antisymm (Submodule.smul_le.mpr fun r hr m _ => ⟨⟨r, ?_⟩ otimesₜ m, rfl⟩) ?_
  · simpa only [ker_pi, Submodule.ker_mkQ]
  rintro _ ⟨x, rfl⟩
  refine x.induction_on (by simp) (fun r m => Submodule.smul_mem_smul ?_ ⟨⟩) fun _ _ => ?_
  · simpa only [← (I _).ker_mkQ, ← ker_pi] using! Subtype.mem _
  · simpa using! add_mem

中文:
定理 ker_tensorProductMk_quotient
  证明: by
  have := rTensor_exact M (exact_subtype_ker_map _) (pi_mkQ_surjective hI)
  rw [← (TensorProduct.lid R M).conj_exact_iff_exact]; rw [exact_iff] at this
  convert! this
  · classical simp [pi_mkQ_rTensor, LinearMap.comp_assoc]
  refine le_antisymm (Submodule.smul_le.mpr fun r hr m _ => ⟨⟨r, ?_⟩ otimesₜ m, rfl⟩) ?_
  · simpa only [ker_pi, Submodule.ker_mkQ]
  rintro _ ⟨x, rfl⟩
  refine x.induction_on (by simp) (fun r m => Submodule.smul_mem_smul ?_ ⟨⟩) fun _ _ => ?_
  · simpa only [← (I _).ker_mkQ, ← ker_pi] using! Subtype.mem _
  · simpa using! add_mem

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, Submodule, Submodule.ker_mkQ, Submodule.smul_le.mpr, Submodule.smul_mem_smul, TensorProduct, TensorProduct.lid, classical, comp_assoc, conj_exact_iff_exact, convert, exact_iff, exact_subtype_ker_map, induction_on, ker_mkQ, ker_pi, le_antisymm, pi_mkQ_rTensor, pi_mkQ_surjective
-/
theorem ker_tensorProductMk_quotient :
    ker (LinearMap.pi fun i => TensorProduct.mk R (R ⧸ I i) M 1) =
      (⨅ i, I i) • (⊤ : Submodule R M) := by
  have := rTensor_exact M (exact_subtype_ker_map _) (pi_mkQ_surjective hI)
  rw [← (TensorProduct.lid R M).conj_exact_iff_exact]; rw [exact_iff] at this
  convert! this
  · classical simp [pi_mkQ_rTensor, LinearMap.comp_assoc]
  refine le_antisymm (Submodule.smul_le.mpr fun r hr m _ => ⟨⟨r, ?_⟩ otimesₜ m, rfl⟩) ?_
  · simpa only [ker_pi, Submodule.ker_mkQ]
  rintro _ ⟨x, rfl⟩
  refine x.induction_on (by simp) (fun r m => Submodule.smul_mem_smul ?_ ⟨⟩) fun _ _ => ?_
  · simpa only [← (I _).ker_mkQ, ← ker_pi] using! Subtype.mem _
  · simpa using! add_mem

end Ideal
