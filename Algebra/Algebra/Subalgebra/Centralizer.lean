/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Properties of centers and centralizers

This file contains theorems about the center and centralizer of a subalgebra.

## Main results

Let `R` be a commutative ring and `A` and `B` two `R`-algebras.
- `Subalgebra.centralizer_sup`: if `S` and `T` are subalgebras of `A`, then the centralizer of
  `S ⊔ T` is the intersection of the centralizer of `S` and the centralizer of `T`.
- `Subalgebra.centralizer_range_includeLeft_eq_center_tensorProduct`: if `B` is free as a module,
  then the centralizer of `A ⊗ 1` in `A ⊗ B` is `C(A) ⊗ B` where `C(A)` is the center of `A`.
- `Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct`: if `A` is free as a module,
  then the centralizer of `1 ⊗ B` in `A ⊗ B` is `A ⊗ C(B)` where `C(B)` is the center of `B`.
-/

public section

namespace Subalgebra

open Algebra.TensorProduct

section CommSemiring

variable {R : Type*} [CommSemiring R]
variable {A : Type*} [Semiring A] [Algebra R A]

/--
lemma `le_centralizer_iff` / 引理 `le_centralizer_iff`

English:
lemma le_centralizer_iff
  given: (S T : Subalgebra R A)
  statement: S <= centralizer R T ↔ T <= centralizer R S
  proof: ⟨fun h t ht _ hs => (h hs t ht).symm, fun h s hs _ ht => (h ht s hs).symm⟩

中文:
引理 le_centralizer_iff
  条件: (S T : 子代数 R A)
  结论: S <= centralizer R T ↔ T <= centralizer R S
  证明: ⟨fun h t ht _ hs => (h hs t ht).symm, fun h s hs _ ht => (h ht s hs).symm⟩
-/
lemma le_centralizer_iff (S T : Subalgebra R A) : S <= centralizer R T ↔ T <= centralizer R S :=
  ⟨fun h t ht _ hs => (h hs t ht).symm, fun h s hs _ ht => (h ht s hs).symm⟩

/--
lemma `centralizer_coe_sup` / 引理 `centralizer_coe_sup`

English:
lemma centralizer_coe_sup
  given: (S T : Subalgebra R A)
  proof: eq_of_forall_le_iff fun K => by
    simp_rw [le_centralizer_iff, sup_le_iff, le_inf_iff, K.le_centralizer_iff]

中文:
引理 centralizer_coe_sup
  条件: (S T : 子代数 R A)
  证明: eq_of_forall_le_iff fun K => by
    simp_rw [le_centralizer_iff, sup_le_iff, le_inf_iff, K.le_centralizer_iff]

Depends on / 依赖: K.le_centralizer_iff, eq_of_forall_le_iff, le_centralizer_iff, le_inf_iff, simp_rw, sup_le_iff
-/
lemma centralizer_coe_sup (S T : Subalgebra R A) :
    centralizer R ((S ⊔ T : Subalgebra R A) : Set A) = centralizer R S ⊓ centralizer R T :=
  eq_of_forall_le_iff fun K => by
    simp_rw [le_centralizer_iff, sup_le_iff, le_inf_iff, K.le_centralizer_iff]

/--
lemma `centralizer_coe_iSup` / 引理 `centralizer_coe_iSup`

English:
lemma centralizer_coe_iSup
  given: {ι : Sort*} (S : ι -> Subalgebra R A)
  proof: eq_of_forall_le_iff fun K => by
    simp_rw [le_centralizer_iff, iSup_le_iff, le_iInf_iff, K.le_centralizer_iff]

中文:
引理 centralizer_coe_iSup
  条件: {ι : 类型层*} (S : ι -> 子代数 R A)
  证明: eq_of_forall_le_iff fun K => by
    simp_rw [le_centralizer_iff, iSup_le_iff, le_iInf_iff, K.le_centralizer_iff]

Depends on / 依赖: K.le_centralizer_iff, eq_of_forall_le_iff, iSup_le_iff, le_centralizer_iff, le_iInf_iff, simp_rw
-/
lemma centralizer_coe_iSup {ι : Sort*} (S : ι -> Subalgebra R A) :
    centralizer R ((⨆ i, S i : Subalgebra R A) : Set A) = ⨅ i, centralizer R (S i) :=
  eq_of_forall_le_iff fun K => by
    simp_rw [le_centralizer_iff, iSup_le_iff, le_iInf_iff, K.le_centralizer_iff]

end CommSemiring

section Free

variable (R : Type*) [CommSemiring R]
variable (A : Type*) [Semiring A] [Algebra R A]
variable (B : Type*) [Semiring B] [Algebra R B]

open Finsupp TensorProduct

/--
lemma `centralizer_coe_image_includeLeft_eq_center_tensorProduct` / 引理 `centralizer_coe_image_includeLeft_eq_center_tensorProduct`

English:
lemma centralizer_coe_image_includeLeft_eq_center_tensorProduct
  proof: by
  ext w
  constructor
  · intro hw
    rw [mem_centralizer_iff] at hw
    let ℬ := Module.Free.chooseBasis R B
    obtain ⟨b, rfl⟩ := TensorProduct.eq_repr_basis_right ℬ w
    refine Subalgebra.sum_mem _ fun j hj => ⟨⟨b j, ?_⟩ otimesₜ[R] ℬ j, by simp⟩
    rw [Subalgebra.mem_centralizer_iff]
    intro x hx
    suffices x • b = b.mapRange (· * x) (by simp) from Finsupp.ext_iff.1 this j
    specialize hw (x otimesₜ[R] 1) ⟨x, hx, rfl⟩
    simp only [Finsupp.sum, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      Finset.sum_mul, mul_one] at hw
    refine TensorProduct.sum_tmul_basis_right_injective ℬ ?_
    simp only [Finsupp.coe_lsum]
    rw [sum_of_support_subset (s := b.support) (hs := Finsupp.support_smul) (h := by simp)]; rw [sum_of_support_subset (s := b.support) (hs := support_mapRange) (h := by simp)]
    simpa only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, LinearMap.flip_apply,
      TensorProduct.mk_apply, Finsupp.mapRange_apply] using hw
  · rintro ⟨w, rfl⟩
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul b c =>
      simp [Subalgebra.mem_centralizer_iff _ |>.1 b.2 x hx]
    | add y z hy hz => rw [map_add, mul_add, hy, hz, add_mul]

中文:
引理 centralizer_coe_image_includeLeft_eq_center_tensorProduct
  证明: by
  ext w
  constructor
  · intro hw
    rw [mem_centralizer_iff] at hw
    let ℬ := Module.Free.chooseBasis R B
    obtain ⟨b, rfl⟩ := TensorProduct.eq_repr_basis_right ℬ w
    refine Subalgebra.sum_mem _ fun j hj => ⟨⟨b j, ?_⟩ otimesₜ[R] ℬ j, by simp⟩
    rw [Subalgebra.mem_centralizer_iff]
    intro x hx
    suffices x • b = b.mapRange (· * x) (by simp) from Finsupp.ext_iff.1 this j
    specialize hw (x otimesₜ[R] 1) ⟨x, hx, rfl⟩
    simp only [Finsupp.sum, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      Finset.sum_mul, mul_one] at hw
    refine TensorProduct.sum_tmul_basis_right_injective ℬ ?_
    simp only [Finsupp.coe_lsum]
    rw [sum_of_support_subset (s := b.support) (hs := Finsupp.support_smul) (h := by simp)]; rw [sum_of_support_subset (s := b.support) (hs := support_mapRange) (h := by simp)]
    simpa only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, LinearMap.flip_apply,
      TensorProduct.mk_apply, Finsupp.mapRange_apply] using hw
  · rintro ⟨w, rfl⟩
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul b c =>
      simp [Subalgebra.mem_centralizer_iff _ |>.1 b.2 x hx]
    | add y z hy hz => rw [map_add, mul_add, hy, hz, add_mul]
-/
lemma centralizer_coe_image_includeLeft_eq_center_tensorProduct
    (S : Set A) [Module.Free R B] :
    Subalgebra.centralizer R
      (Algebra.TensorProduct.includeLeft (S := R) '' S) =
    (Algebra.TensorProduct.map (Subalgebra.centralizer R (S : Set A)).val
      (AlgHom.id R B)).range := by
  ext w
  constructor
  · intro hw
    rw [mem_centralizer_iff] at hw
    let ℬ := Module.Free.chooseBasis R B
    obtain ⟨b, rfl⟩ := TensorProduct.eq_repr_basis_right ℬ w
    refine Subalgebra.sum_mem _ fun j hj => ⟨⟨b j, ?_⟩ otimesₜ[R] ℬ j, by simp⟩
    rw [Subalgebra.mem_centralizer_iff]
    intro x hx
    suffices x • b = b.mapRange (· * x) (by simp) from Finsupp.ext_iff.1 this j
    specialize hw (x otimesₜ[R] 1) ⟨x, hx, rfl⟩
    simp only [Finsupp.sum, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      Finset.sum_mul, mul_one] at hw
    refine TensorProduct.sum_tmul_basis_right_injective ℬ ?_
    simp only [Finsupp.coe_lsum]
    rw [sum_of_support_subset (s := b.support) (hs := Finsupp.support_smul) (h := by simp)]; rw [sum_of_support_subset (s := b.support) (hs := support_mapRange) (h := by simp)]
    simpa only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, LinearMap.flip_apply,
      TensorProduct.mk_apply, Finsupp.mapRange_apply] using hw
  · rintro ⟨w, rfl⟩
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul b c =>
      simp [Subalgebra.mem_centralizer_iff _ |>.1 b.2 x hx]
    | add y z hy hz => rw [map_add, mul_add, hy, hz, add_mul]

/--
lemma `centralizer_coe_image_includeRight_eq_center_tensorProduct` / 引理 `centralizer_coe_image_includeRight_eq_center_tensorProduct`

English:
lemma centralizer_coe_image_includeRight_eq_center_tensorProduct
  proof: by
  have eq1 := centralizer_coe_image_includeLeft_eq_center_tensorProduct R B A S
  apply_fun Subalgebra.comap (Algebra.TensorProduct.comm R A B).toAlgHom at eq1
  convert! eq1
  · ext x
    simpa [mem_centralizer_iff] using
⟨fun h b hb => (Algebra.TensorProduct.comm R A B).symm.injective by aesop, fun h b hb =>
(Algebra.TensorProduct.comm R A B).injective by aesop⟩
  · ext x
    simp only [AlgHom.mem_range, mem_comap, AlgEquiv.coe_toAlgHom]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(Algebra.TensorProduct.comm R _ _) x,
        by rw [Algebra.TensorProduct.comm_comp_map_apply]⟩
    · rintro ⟨y, hy⟩
      refine ⟨(Algebra.TensorProduct.comm R _ _) y, (Algebra.TensorProduct.comm R A B).injective ?_⟩
      rw [← hy]; rw [comm_comp_map_apply]; rw [← Algebra.TensorProduct.comm_symm]; rw [AlgEquiv.symm_apply_apply]

中文:
引理 centralizer_coe_image_includeRight_eq_center_tensorProduct
  证明: by
  have eq1 := centralizer_coe_image_includeLeft_eq_center_tensorProduct R B A S
  apply_fun Subalgebra.comap (Algebra.TensorProduct.comm R A B).toAlgHom at eq1
  convert! eq1
  · ext x
    simpa [mem_centralizer_iff] using
⟨fun h b hb => (Algebra.TensorProduct.comm R A B).symm.injective by aesop, fun h b hb =>
(Algebra.TensorProduct.comm R A B).injective by aesop⟩
  · ext x
    simp only [AlgHom.mem_range, mem_comap, AlgEquiv.coe_toAlgHom]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(Algebra.TensorProduct.comm R _ _) x,
        by rw [Algebra.TensorProduct.comm_comp_map_apply]⟩
    · rintro ⟨y, hy⟩
      refine ⟨(Algebra.TensorProduct.comm R _ _) y, (Algebra.TensorProduct.comm R A B).injective ?_⟩
      rw [← hy]; rw [comm_comp_map_apply]; rw [← Algebra.TensorProduct.comm_symm]; rw [AlgEquiv.symm_apply_apply]

Depends on / 依赖: AlgEquiv, AlgEquiv.coe_toAlgHom, AlgHom, AlgHom.mem_range, Algebra, Algebra.TensorProduct.comm, Subalgebra, Subalgebra.comap, TensorProduct, apply_fun, centralizer_coe_image_includeLeft_eq_center_tensorProduct, coe_toAlgHom, convert, injective, mem_centralizer_iff, mem_comap, mem_range, symm.injective, toAlgHom
-/
lemma centralizer_coe_image_includeRight_eq_center_tensorProduct
    (S : Set B) [Module.Free R A] :
    Subalgebra.centralizer R
      (Algebra.TensorProduct.includeRight '' S) =
    (Algebra.TensorProduct.map (AlgHom.id R A)
      (Subalgebra.centralizer R (S : Set B)).val).range := by
  have eq1 := centralizer_coe_image_includeLeft_eq_center_tensorProduct R B A S
  apply_fun Subalgebra.comap (Algebra.TensorProduct.comm R A B).toAlgHom at eq1
  convert! eq1
  · ext x
    simpa [mem_centralizer_iff] using
⟨fun h b hb => (Algebra.TensorProduct.comm R A B).symm.injective by aesop, fun h b hb =>
(Algebra.TensorProduct.comm R A B).injective by aesop⟩
  · ext x
    simp only [AlgHom.mem_range, mem_comap, AlgEquiv.coe_toAlgHom]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(Algebra.TensorProduct.comm R _ _) x,
        by rw [Algebra.TensorProduct.comm_comp_map_apply]⟩
    · rintro ⟨y, hy⟩
      refine ⟨(Algebra.TensorProduct.comm R _ _) y, (Algebra.TensorProduct.comm R A B).injective ?_⟩
      rw [← hy]; rw [comm_comp_map_apply]; rw [← Algebra.TensorProduct.comm_symm]; rw [AlgEquiv.symm_apply_apply]

/--
lemma `centralizer_coe_map_includeLeft_eq_center_tensorProduct` / 引理 `centralizer_coe_map_includeLeft_eq_center_tensorProduct`

English:
lemma centralizer_coe_map_includeLeft_eq_center_tensorProduct
  proof: centralizer_coe_image_includeLeft_eq_center_tensorProduct R A B S

中文:
引理 centralizer_coe_map_includeLeft_eq_center_tensorProduct
  证明: centralizer_coe_image_includeLeft_eq_center_tensorProduct R A B S
-/
lemma centralizer_coe_map_includeLeft_eq_center_tensorProduct
    (S : Subalgebra R A) [Module.Free R B] :
    Subalgebra.centralizer R
      (S.map (Algebra.TensorProduct.includeLeft (R := R) (B := B))) =
    (Algebra.TensorProduct.map (Subalgebra.centralizer R (S : Set A)).val
      (AlgHom.id R B)).range :=
  centralizer_coe_image_includeLeft_eq_center_tensorProduct R A B S

/--
lemma `centralizer_coe_map_includeRight_eq_center_tensorProduct` / 引理 `centralizer_coe_map_includeRight_eq_center_tensorProduct`

English:
lemma centralizer_coe_map_includeRight_eq_center_tensorProduct
  proof: centralizer_coe_image_includeRight_eq_center_tensorProduct R A B S

中文:
引理 centralizer_coe_map_includeRight_eq_center_tensorProduct
  证明: centralizer_coe_image_includeRight_eq_center_tensorProduct R A B S
-/
lemma centralizer_coe_map_includeRight_eq_center_tensorProduct
    (S : Subalgebra R B) [Module.Free R A] :
    Subalgebra.centralizer R
      (S.map (Algebra.TensorProduct.includeRight (R := R) (A := A))) =
    (Algebra.TensorProduct.map (AlgHom.id R A)
      (Subalgebra.centralizer R (S : Set B)).val).range :=
  centralizer_coe_image_includeRight_eq_center_tensorProduct R A B S

/--
lemma `centralizer_coe_range_includeLeft_eq_center_tensorProduct` / 引理 `centralizer_coe_range_includeLeft_eq_center_tensorProduct`

English:
lemma centralizer_coe_range_includeLeft_eq_center_tensorProduct
  given: [Module.Free R B]
  proof: by
  rw [← centralizer_univ]; rw [← Algebra.coe_top (R := R) (A := A)]; rw [← centralizer_coe_map_includeLeft_eq_center_tensorProduct R A B ⊤]
  ext
  simp [includeLeft, includeLeftRingHom]

中文:
引理 centralizer_coe_range_includeLeft_eq_center_tensorProduct
  条件: [模.自由 R B]
  证明: by
  rw [← centralizer_univ]; rw [← Algebra.coe_top (R := R) (A := A)]; rw [← centralizer_coe_map_includeLeft_eq_center_tensorProduct R A B ⊤]
  ext
  simp [includeLeft, includeLeftRingHom]

Depends on / 依赖: Algebra, Algebra.coe_top, centralizer_coe_map_includeLeft_eq_center_tensorProduct, centralizer_univ, coe_top, includeLeft, includeLeftRingHom
-/
lemma centralizer_coe_range_includeLeft_eq_center_tensorProduct [Module.Free R B] :
    Subalgebra.centralizer R
      (Algebra.TensorProduct.includeLeft : A ->ₐ[R] A otimes[R] B).range =
    (Algebra.TensorProduct.map (Subalgebra.center R A).val (AlgHom.id R B)).range := by
  rw [← centralizer_univ]; rw [← Algebra.coe_top (R := R) (A := A)]; rw [← centralizer_coe_map_includeLeft_eq_center_tensorProduct R A B ⊤]
  ext
  simp [includeLeft, includeLeftRingHom]

/--
lemma `centralizer_range_includeRight_eq_center_tensorProduct` / 引理 `centralizer_range_includeRight_eq_center_tensorProduct`

English:
lemma centralizer_range_includeRight_eq_center_tensorProduct
  given: [Module.Free R A]
  proof: by
  rw [← centralizer_univ]; rw [← Algebra.coe_top (R := R) (A := B)]; rw [← centralizer_coe_map_includeRight_eq_center_tensorProduct R A B ⊤]
  ext
  simp [includeRight]

中文:
引理 centralizer_range_includeRight_eq_center_tensorProduct
  条件: [模.自由 R A]
  证明: by
  rw [← centralizer_univ]; rw [← Algebra.coe_top (R := R) (A := B)]; rw [← centralizer_coe_map_includeRight_eq_center_tensorProduct R A B ⊤]
  ext
  simp [includeRight]

Depends on / 依赖: Algebra, Algebra.coe_top, centralizer_coe_map_includeRight_eq_center_tensorProduct, centralizer_univ, coe_top, includeRight
-/
lemma centralizer_range_includeRight_eq_center_tensorProduct [Module.Free R A] :
    Subalgebra.centralizer R
      (Algebra.TensorProduct.includeRight : B ->ₐ[R] A otimes[R] B).range =
    (Algebra.TensorProduct.map (AlgHom.id R A) (center R B).val).range := by
  rw [← centralizer_univ]; rw [← Algebra.coe_top (R := R) (A := B)]; rw [← centralizer_coe_map_includeRight_eq_center_tensorProduct R A B ⊤]
  ext
  simp [includeRight]

/--
lemma `centralizer_tensorProduct_eq_center_tensorProduct_left` / 引理 `centralizer_tensorProduct_eq_center_tensorProduct_left`

English:
lemma centralizer_tensorProduct_eq_center_tensorProduct_left
  given: [Module.Free R B]
  proof: by
  rw [← centralizer_coe_range_includeLeft_eq_center_tensorProduct]
  simp [Algebra.TensorProduct.map_range]

中文:
引理 centralizer_tensorProduct_eq_center_tensorProduct_left
  条件: [模.自由 R B]
  证明: by
  rw [← centralizer_coe_range_includeLeft_eq_center_tensorProduct]
  simp [Algebra.TensorProduct.map_range]

Depends on / 依赖: Algebra, Algebra.TensorProduct.map_range, TensorProduct, centralizer_coe_range_includeLeft_eq_center_tensorProduct, map_range
-/
lemma centralizer_tensorProduct_eq_center_tensorProduct_left [Module.Free R B] :
    Subalgebra.centralizer R
      (Algebra.TensorProduct.map (AlgHom.id R A) (Algebra.ofId R B)).range =
    (Algebra.TensorProduct.map (Subalgebra.center R A).val (AlgHom.id R B)).range := by
  rw [← centralizer_coe_range_includeLeft_eq_center_tensorProduct]
  simp [Algebra.TensorProduct.map_range]

/--
lemma `centralizer_tensorProduct_eq_center_tensorProduct_right` / 引理 `centralizer_tensorProduct_eq_center_tensorProduct_right`

English:
lemma centralizer_tensorProduct_eq_center_tensorProduct_right
  given: [Module.Free R A]
  proof: by
  rw [← centralizer_range_includeRight_eq_center_tensorProduct]
  simp [Algebra.TensorProduct.map_range]

中文:
引理 centralizer_tensorProduct_eq_center_tensorProduct_right
  条件: [模.自由 R A]
  证明: by
  rw [← centralizer_range_includeRight_eq_center_tensorProduct]
  simp [Algebra.TensorProduct.map_range]

Depends on / 依赖: Algebra, Algebra.TensorProduct.map_range, TensorProduct, centralizer_range_includeRight_eq_center_tensorProduct, map_range
-/
lemma centralizer_tensorProduct_eq_center_tensorProduct_right [Module.Free R A] :
    Subalgebra.centralizer R
      (Algebra.TensorProduct.map (Algebra.ofId R A) (AlgHom.id R B)).range =
    (Algebra.TensorProduct.map (AlgHom.id R A) (center R B).val).range := by
  rw [← centralizer_range_includeRight_eq_center_tensorProduct]
  simp [Algebra.TensorProduct.map_range]

end Free

end Subalgebra
