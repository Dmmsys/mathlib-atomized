/-
Copyright (c) 2025 Yong-Gyu Choi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yong-Gyu Choi
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Exactness properties of the difference map on tensor products

For an `R`-algebra `S`, we collect some properties of the `R`-linear map `S →ₗ[R] S ⊗[R] S` given
by `s ↦ s ⊗ₜ 1 - 1 ⊗ₜ s`.

## Main definitions

* `includeLeftSubRight`: The `R`-linear map sending `s : S` to `s ⊗ₜ 1 - 1 ⊗ₜ s`.
* `IsEffective`: Exactness of the sequence `R → S → S ⊗[R] S` where the first map is
  `Algebra.linearMap R S` and the second map is `includeLeftSubRight`. When `R` and `S` are
  commutative rings, this is equivalent to the inclusion `im (algebraMap : R → S) → S` being an
  effective monomorphism in `CommRingCat`.

## Main results

* `IsEffective.of_faithfullyFlat`: `IsEffective R S` is true for any faithfully flat `R`-algebra `S`

-/

@[expose] public section

open scoped TensorProduct

namespace Algebra

variable {R : Type*} [CommSemiring R]
variable {S : Type*} [Ring S] [Algebra R S]

namespace TensorProduct

section IncludeLeftSubRight

variable (R S) in
/--
Definition of `includeLeftSubRight` / `includeLeftSubRight` 的定义

English:
definition includeLeftSubRight
  signature: : S ->ₗ[R] S otimes[R] S
  body: includeLeft.toLinearMap - includeRight.toLinearMap

@[simp]

中文:
定义 includeLeftSubRight
  签名: : S ->ₗ[R] S otimes[R] S
  定义体: includeLeft.toLinearMap - includeRight.toLinearMap

@[simp]

Depends on / 依赖: includeLeft, includeLeft.toLinearMap, includeRight, includeRight.toLinearMap, toLinearMap
-/
def includeLeftSubRight : S ->ₗ[R] S otimes[R] S :=
  includeLeft.toLinearMap - includeRight.toLinearMap

@[simp]
/--
lemma `includeLeftSubRight_apply` / 引理 `includeLeftSubRight_apply`

English:
lemma includeLeftSubRight_apply
  given: (s : S)
  statement: includeLeftSubRight R S s = s otimesₜ[R] 1 - 1 otimesₜ[R] s
  proof: rfl

中文:
引理 includeLeftSubRight_apply
  条件: (s : S)
  结论: includeLeftSubRight R S s = s otimesₜ[R] 1 - 1 otimesₜ[R] s
  证明: rfl
-/
lemma includeLeftSubRight_apply (s : S) : includeLeftSubRight R S s = s otimesₜ[R] 1 - 1 otimesₜ[R] s :=
  rfl

/--
lemma `includeLeftSubRight_zero_of_mem_range` / 引理 `includeLeftSubRight_zero_of_mem_range`

English:
lemma includeLeftSubRight_zero_of_mem_range
  given: {s : S} (hs : s in Set.range ⇑(algebraMap R S))
  proof: by
  obtain ⟨_, hr⟩ := Set.mem_range.mp hs
  simp [← hr, algebraMap_eq_smul_one]

中文:
引理 includeLeftSubRight_zero_of_mem_range
  条件: {s : S} (hs : s in 集合.range ⇑(algebraMap R S))
  证明: by
  obtain ⟨_, hr⟩ := Set.mem_range.mp hs
  simp [← hr, algebraMap_eq_smul_one]

Depends on / 依赖: Set.mem_range.mp, algebraMap_eq_smul_one, mem_range
-/
lemma includeLeftSubRight_zero_of_mem_range {s : S} (hs : s in Set.range ⇑(algebraMap R S)) :
    includeLeftSubRight R S s = 0 := by
  obtain ⟨_, hr⟩ := Set.mem_range.mp hs
  simp [← hr, algebraMap_eq_smul_one]

/--
lemma `includeLeftSubRight_algebraMap_zero` / 引理 `includeLeftSubRight_algebraMap_zero`

English:
lemma includeLeftSubRight_algebraMap_zero
  given: (r : R)
  proof: includeLeftSubRight_zero_of_mem_range (Set.mem_range.mp (exists_apply_eq_apply _ _))

中文:
引理 includeLeftSubRight_algebraMap_zero
  条件: (r : R)
  证明: includeLeftSubRight_zero_of_mem_range (Set.mem_range.mp (exists_apply_eq_apply _ _))

Depends on / 依赖: Set.mem_range.mp, exists_apply_eq_apply, includeLeftSubRight_zero_of_mem_range, mem_range
-/
lemma includeLeftSubRight_algebraMap_zero (r : R) :
    includeLeftSubRight R S (algebraMap R S r) = 0 :=
  includeLeftSubRight_zero_of_mem_range (Set.mem_range.mp (exists_apply_eq_apply _ _))

/--
lemma `distribBaseChange_comp_includeLeftSubRight` / 引理 `distribBaseChange_comp_includeLeftSubRight`

English:
lemma distribBaseChange_comp_includeLeftSubRight
  given: (T : Type*) [CommRing T] [Algebra R T]
  proof: by
  ext
  simp [TensorProduct.tmul_sub, TensorProduct.one_def, tmul_one_tmul_one_tmul]

@[simp]

中文:
引理 distribBaseChange_comp_includeLeftSubRight
  条件: (T : 类型) [交换环 T] [代数 R T]
  证明: by
  ext
  simp [TensorProduct.tmul_sub, TensorProduct.one_def, tmul_one_tmul_one_tmul]

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.one_def, TensorProduct.tmul_sub, one_def, tmul_one_tmul_one_tmul, tmul_sub
-/
lemma distribBaseChange_comp_includeLeftSubRight (T : Type*) [CommRing T] [Algebra R T] :
    ((TensorProduct.AlgebraTensorModule.distribBaseChange R T S S).restrictScalars R).toLinearMap ∘ₗ
      (includeLeftSubRight R S).lTensor T =
    (includeLeftSubRight T (T otimes[R] S)).restrictScalars R := by
  ext
  simp [TensorProduct.tmul_sub, TensorProduct.one_def, tmul_one_tmul_one_tmul]

@[simp]
/--
lemma `distribBaseChange_includeLeftSubRight_apply` / 引理 `distribBaseChange_includeLeftSubRight_apply`

English:
lemma distribBaseChange_includeLeftSubRight_apply
  statement: (T : Type*) [CommRing T] [Algebra R T]
  proof: congr($(distribBaseChange_comp_includeLeftSubRight _) x)

中文:
引理 distribBaseChange_includeLeftSubRight_apply
  结论: (T : 类型) [交换环 T] [代数 R T]
  证明: congr($(distribBaseChange_comp_includeLeftSubRight _) x)

Depends on / 依赖: distribBaseChange_comp_includeLeftSubRight
-/
lemma distribBaseChange_includeLeftSubRight_apply (T : Type*) [CommRing T] [Algebra R T]
    (x : T otimes[R] S) :
    TensorProduct.AlgebraTensorModule.distribBaseChange R T S S
      ((includeLeftSubRight R S).lTensor T x) =
    includeLeftSubRight T (T otimes[R] S) x :=
  congr($(distribBaseChange_comp_includeLeftSubRight _) x)

end IncludeLeftSubRight

end TensorProduct

variable (R S) in
/--
Definition of `IsEffective` / `IsEffective` 的定义

English:
definition IsEffective
  signature: : Prop
  body: Function.Exact (Algebra.linearMap R S) (TensorProduct.includeLeftSubRight R S)

中文:
定义 IsEffective
  签名: : 命题
  定义体: Function.Exact (Algebra.linearMap R S) (TensorProduct.includeLeftSubRight R S)

Depends on / 依赖: Algebra, Algebra.linearMap, Function, Function.Exact, TensorProduct, TensorProduct.includeLeftSubRight, includeLeftSubRight, linearMap
-/
def IsEffective : Prop :=
  Function.Exact (Algebra.linearMap R S) (TensorProduct.includeLeftSubRight R S)

namespace IsEffective

/--
lemma `eqLocus_includeLeft_includeRight` / 引理 `eqLocus_includeLeft_includeRight`

English:
lemma eqLocus_includeLeft_includeRight
  given: (h : IsEffective R S)
  proof: by
  ext s
  refine ⟨?_, fun ⟨_, hr⟩ => by simp [← hr]⟩
  intro hs
exact (h s).mp (TensorProduct.includeLeftSubRight_apply (R := R) s).symm ▸ sub_eq_zero.mpr hs

中文:
引理 eqLocus_includeLeft_includeRight
  条件: (h : IsEffective R S)
  证明: by
  ext s
  refine ⟨?_, fun ⟨_, hr⟩ => by simp [← hr]⟩
  intro hs
exact (h s).mp (TensorProduct.includeLeftSubRight_apply (R := R) s).symm ▸ sub_eq_zero.mpr hs

Depends on / 依赖: otimes
-/
lemma eqLocus_includeLeft_includeRight (h : IsEffective R S) :
    TensorProduct.includeLeftRingHom.eqLocus TensorProduct.includeRight.toRingHom (S := S otimes[R] S) =
      Set.range (algebraMap R S) := by
  ext s
  refine ⟨?_, fun ⟨_, hr⟩ => by simp [← hr]⟩
  intro hs
exact (h s).mp (TensorProduct.includeLeftSubRight_apply (R := R) s).symm ▸ sub_eq_zero.mpr hs

/--
lemma `of_section` / 引理 `of_section`

English:
lemma of_section
  given: (g : S ->ₐ[R] R)
  statement: IsEffective R S
  proof: by
  intro s
  refine ⟨?_, TensorProduct.includeLeftSubRight_zero_of_mem_range⟩
  intro hs
  use g s
  apply (TensorProduct.lid R S).symm.injective
  rw [TensorProduct.lid_symm_apply]; rw [TensorProduct.lid_symm_apply]; rw [← mul_one ((Algebra.linearMap R S) _)]; rw [Algebra.coe_linearMap]; rw [← Al

中文:
引理 of_section
  条件: (g : S ->ₐ[R] R)
  结论: IsEffective R S
  证明: by
  intro s
  refine ⟨?_, TensorProduct.includeLeftSubRight_zero_of_mem_range⟩
  intro hs
  use g s
  apply (TensorProduct.lid R S).symm.injective
  rw [TensorProduct.lid_symm_apply]; rw [TensorProduct.lid_symm_apply]; rw [← mul_one ((Algebra.linearMap R S) _)]; rw [Algebra.coe_linearMap]; rw [← Al

Depends on / 依赖: AlgHom, AlgHom.id_apply, Algebra, Algebra.coe_linearMap, Algebra.linearMap, Algebra.smul_def, TensorProduct, TensorProduct.includeLeftSubRight_appl, TensorProduct.includeLeftSubRight_zero_of_mem_range, TensorProduct.lid, TensorProduct.lid_symm_apply, TensorProduct.map_tmul, TensorProduct.smul_tmul, coe_linearMap, id_apply, includeLeftSubRight_appl, includeLeftSubRight_zero_of_mem_range, injective, lid_symm_apply, linearMap
-/
lemma of_section (g : S ->ₐ[R] R) : IsEffective R S := by
  intro s
  refine ⟨?_, TensorProduct.includeLeftSubRight_zero_of_mem_range⟩
  intro hs
  use g s
  apply (TensorProduct.lid R S).symm.injective
  rw [TensorProduct.lid_symm_apply]; rw [TensorProduct.lid_symm_apply]; rw [← mul_one ((Algebra.linearMap R S) _)]; rw [Algebra.coe_linearMap]; rw [← Algebra.smul_def]; rw [← TensorProduct.smul_tmul]; rw [smul_eq_mul]; rw [mul_one]; rw [← AlgHom.id_apply (R := R) (1 : S)]; rw [← TensorProduct.map_tmul]; rw [sub_eq_zero.mp ((TensorProduct.includeLeftSubRight_apply s).symm.trans hs)]; rw [TensorProduct.map_tmul]; rw [map_one]; rw [AlgHom.id_apply]

section FaithfullyFlat

variable (R : Type*) [CommRing R]
variable (S : Type*)
variable (T : Type*) [CommRing T] [Algebra R T]

/--
lemma `of_isEffective_tensorProduct_of_faithfullyFlat` / 引理 `of_isEffective_tensorProduct_of_faithfullyFlat`

English:
lemma of_isEffective_tensorProduct_of_faithfullyFlat
  proof: by
refine Module.FaithfullyFlat.lTensor_reflects_exact _ _ _ _
    AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
      ((Algebra.linearMap R S).lTensor T) ((TensorProduct.includeLeftSubRight R S).lTensor T)
      (Algebra.linearMap T (T otimes[R] S)) (TensorProduct.includeLeftSubRig

中文:
引理 of_isEffective_tensorProduct_of_faithfullyFlat
  证明: by
refine Module.FaithfullyFlat.lTensor_reflects_exact _ _ _ _
    AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
      ((Algebra.linearMap R S).lTensor T) ((TensorProduct.includeLeftSubRight R S).lTensor T)
      (Algebra.linearMap T (T otimes[R] S)) (TensorProduct.includeLeftSubRig

Depends on / 依赖: AddMonoidHom, AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective, AddMonoidHom.id, Algebra, Algebra.linearMap, AlgebraTensorModule, FaithfullyFlat, Module, Module.FaithfullyFlat.lTensor_reflects_exact, TensorProduct, TensorProduct.AlgebraTensorModule.distribBaseChange, TensorProduct.includeLeftSubRight, TensorProduct.rid, distribBaseChange, exact_iff_of_surjective_of_bijective_of_injective, includeLeftSubRight, lTensor, lTensor_reflects_exact, linearMap, otimes
-/
lemma of_isEffective_tensorProduct_of_faithfullyFlat
    [Ring S] [Algebra R S] [Module.FaithfullyFlat R T] (h : IsEffective T (T otimes[R] S)) :
    IsEffective R S := by
refine Module.FaithfullyFlat.lTensor_reflects_exact _ _ _ _
    AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
      ((Algebra.linearMap R S).lTensor T) ((TensorProduct.includeLeftSubRight R S).lTensor T)
      (Algebra.linearMap T (T otimes[R] S)) (TensorProduct.includeLeftSubRight T (T otimes[R] S))
      (TensorProduct.rid R R T).toAddMonoidHom (AddMonoidHom.id (T otimes[R] S))
      (TensorProduct.AlgebraTensorModule.distribBaseChange R T S S).toAddMonoidHom ?_ ?_
      (TensorProduct.rid R R T).surjective Function.bijective_id
.mpr ‹_› ((TensorProduct.AlgebraTensorModule.distribBaseChange R T S S).injective)
  · ext
    simp [← Algebra.TensorProduct.linearMap_comp_rid]
    -- The goal is TensorProduct.rid .. = TensorProduct.AlgebraTensorModule.rid ..
    -- TODO: merge both into one definition, and remove the rfl.
    rfl
  · ext
    simp

/--
lemma `of_faithfullyFlat` / 引理 `of_faithfullyFlat`

English:
lemma of_faithfullyFlat
  given: [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
  proof: of_isEffective_tensorProduct_of_faithfullyFlat _ _ _ (of_section (TensorProduct.lmul'' R))

中文:
引理 of_faithfullyFlat
  条件: [交换环 S] [代数 R S] [模.忠实平坦 R S]
  证明: of_isEffective_tensorProduct_of_faithfullyFlat _ _ _ (of_section (TensorProduct.lmul'' R))

Depends on / 依赖: TensorProduct, TensorProduct.lmul, of_isEffective_tensorProduct_of_faithfullyFlat, of_section
-/
lemma of_faithfullyFlat [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S] :
    IsEffective R S :=
  of_isEffective_tensorProduct_of_faithfullyFlat _ _ _ (of_section (TensorProduct.lmul'' R))

end FaithfullyFlat

end IsEffective

section CodRestrictEqLocusPushoutCocone

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `codRestrictEqLocusPushoutCocone` / `codRestrictEqLocusPushoutCocone` 的定义

English:
definition codRestrictEqLocusPushoutCocone
  signature: :
  body: RingHom.codRestrict (algebraMap R S)
    ((CommRingCat.pushoutCocone R S S).inl.hom.eqLocus (CommRingCat.pushoutCocone R S S).inr.hom)
    (by simp)

中文:
定义 codRestrictEqLocusPushoutCocone
  签名: :
  定义体: RingHom.codRestrict (algebraMap R S)
    ((CommRingCat.pushoutCocone R S S).inl.hom.eqLocus (CommRingCat.pushoutCocone R S S).inr.hom)
    (by simp)

Depends on / 依赖: CommRingCat, CommRingCat.pushoutCocone, RingHom, RingHom.codRestrict, algebraMap, codRestrict, eqLocus, inl.hom.eqLocus, inr.hom, pushoutCocone
-/
def codRestrictEqLocusPushoutCocone :
    R ->+* (CommRingCat.equalizerFork
      (CommRingCat.pushoutCocone R S S).inl (CommRingCat.pushoutCocone R S S).inr).pt :=
  RingHom.codRestrict (algebraMap R S)
    ((CommRingCat.pushoutCocone R S S).inl.hom.eqLocus (CommRingCat.pushoutCocone R S S).inr.hom)
    (by simp)

/--
lemma `codRestrictEqLocusPushoutCocone.injective_of_faithfulSMul` / 引理 `codRestrictEqLocusPushoutCocone.injective_of_faithfulSMul`

English:
lemma codRestrictEqLocusPushoutCocone.injective_of_faithfulSMul
  given: [FaithfulSMul R S]
  proof: RingHom.injective_codRestrict.mpr (FaithfulSMul.algebraMap_injective _ _)

中文:
引理 codRestrictEqLocusPushoutCocone.injective_of_faithfulSMul
  条件: [忠实标量乘法 R S]
  证明: RingHom.injective_codRestrict.mpr (FaithfulSMul.algebraMap_injective _ _)

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, RingHom, RingHom.injective_codRestrict.mpr, algebraMap_injective, injective_codRestrict
-/
lemma codRestrictEqLocusPushoutCocone.injective_of_faithfulSMul [FaithfulSMul R S] :
    Function.Injective (codRestrictEqLocusPushoutCocone R S) :=
  RingHom.injective_codRestrict.mpr (FaithfulSMul.algebraMap_injective _ _)

/--
lemma `codRestrictEqLocusPushoutCocone.surjective_of_isEffective` / 引理 `codRestrictEqLocusPushoutCocone.surjective_of_isEffective`

English:
lemma codRestrictEqLocusPushoutCocone.surjective_of_isEffective
  given: (hf : Algebra.IsEffective R S)
  proof: by
  intro ⟨s, hs⟩
obtain ⟨t, rfl⟩ := Set.mem_range.mp
    Algebra.IsEffective.eqLocus_includeLeft_includeRight hf ▸ SetLike.mem_coe.mpr hs
  exact ⟨t, rfl⟩

中文:
引理 codRestrictEqLocusPushoutCocone.surjective_of_isEffective
  条件: (hf : 代数.IsEffective R S)
  证明: by
  intro ⟨s, hs⟩
obtain ⟨t, rfl⟩ := Set.mem_range.mp
    Algebra.IsEffective.eqLocus_includeLeft_includeRight hf ▸ SetLike.mem_coe.mpr hs
  exact ⟨t, rfl⟩

Depends on / 依赖: Algebra, Algebra.IsEffective.eqLocus_includeLeft_includeRight, IsEffective, Set.mem_range.mp, SetLike, SetLike.mem_coe.mpr, eqLocus_includeLeft_includeRight, mem_coe, mem_range
-/
lemma codRestrictEqLocusPushoutCocone.surjective_of_isEffective (hf : Algebra.IsEffective R S) :
    Function.Surjective (codRestrictEqLocusPushoutCocone R S) := by
  intro ⟨s, hs⟩
obtain ⟨t, rfl⟩ := Set.mem_range.mp
    Algebra.IsEffective.eqLocus_includeLeft_includeRight hf ▸ SetLike.mem_coe.mpr hs
  exact ⟨t, rfl⟩

/--
lemma `codRestrictEqLocusPushoutCocone.bijective_of_faithfullyFlat` / 引理 `codRestrictEqLocusPushoutCocone.bijective_of_faithfullyFlat`

English:
lemma codRestrictEqLocusPushoutCocone.bijective_of_faithfullyFlat
  given: [Module.FaithfullyFlat R S]
  proof: by
  constructor
  · exact codRestrictEqLocusPushoutCocone.injective_of_faithfulSMul _ _
  · exact codRestrictEqLocusPushoutCocone.surjective_of_isEffective _ _ (.of_faithfullyFlat R S)

中文:
引理 codRestrictEqLocusPushoutCocone.bijective_of_faithfullyFlat
  条件: [模.忠实平坦 R S]
  证明: by
  constructor
  · exact codRestrictEqLocusPushoutCocone.injective_of_faithfulSMul _ _
  · exact codRestrictEqLocusPushoutCocone.surjective_of_isEffective _ _ (.of_faithfullyFlat R S)

Depends on / 依赖: codRestrictEqLocusPushoutCocone, codRestrictEqLocusPushoutCocone.injective_of_faithfulSMul, codRestrictEqLocusPushoutCocone.surjective_of_isEffective, injective_of_faithfulSMul, of_faithfullyFlat, surjective_of_isEffective
-/
lemma codRestrictEqLocusPushoutCocone.bijective_of_faithfullyFlat [Module.FaithfullyFlat R S] :
    Function.Bijective (codRestrictEqLocusPushoutCocone R S) := by
  constructor
  · exact codRestrictEqLocusPushoutCocone.injective_of_faithfulSMul _ _
  · exact codRestrictEqLocusPushoutCocone.surjective_of_isEffective _ _ (.of_faithfullyFlat R S)

end CodRestrictEqLocusPushoutCocone

end Algebra
