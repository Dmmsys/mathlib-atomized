/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients

/-!

# Decomposition and Inertia fields

In this file, we develop Hilbert Theory on the splitting of prime ideals in a Galois extension.

Let `L/K` be a Galois extension of fields. Let `A` and `B` be subrings of `K` `L` respectively with
`K` fraction field of `A`, `L` fraction field of `B` and `B` the integral closure of `A` in `L`.

For `P` a prime ideal of `B` lying over the prime ideal `p` of `A`, the decomposition field `D` of
`P` in `L/K` is the subfield of elements of `L` fixed by the stabilizer of `P` in `Gal(L/K)`, and
the inertia field `E` of `P` in `L/K` is the subfield of elements of `L` fixed by the inertia
group of `P` in `Gal(L/K)`.

Let `e` and `f` the ramification index and inertia degree of `P` over `p` and let `g`
be the number of prime ideals above `p` in `L`. Denote by `𝓟D`, resp. `𝓟E`, the prime ideal of `D`,
resp. `E`, below `P`. Then we have the following properties
```
degree ramif. index inertia deg.
        L P
  e | | e 1
        E 𝓟E
  f | | 1 f
        D 𝓟D
  g | | 1 1
        K p
```

-/

@[expose] public section

variable (A K L : Type*) {B : Type*} [Field K] [Field L] [Algebra K L] [CommRing A] [CommRing B]
  [Algebra A B] {p : Ideal A} (P : Ideal B) [P.LiesOver p]

open MulAction Pointwise Ideal

section basic

variable (D : Type*) [Field D] [Algebra D L]

/--
Let `L/K` be a Galois extension of fields and let `P` be a prime ideal of `B`. The predicate that
says that `D` is the decomposition field of `P` in `L/K`, that is the subfield fixed by the
decomposition subgroup of `P`, that is the stabilizer of `P` in `Gal(L/K)`.
-/
@[mk_iff]
/--
Definition of `IsDecompositionField` / `IsDecompositionField` 的定义

English:
class IsDecompositionField
  parameters: [MulSemiringAction Gal(L/K) B]
  (no additional axioms)

中文:
类 是DecompositionField
  参数: [MulSemiring作用 Gal(L/K) B]
  (无附加公理)
-/
class IsDecompositionField [MulSemiringAction Gal(L/K) B] extends
    IsGaloisGroup (stabilizer Gal(L/K) P) D L

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulSemiringAction
  signature: Gal(L/K) B] [h
  body: { toIsGaloisGroup := h }

中文:
实例 [MulSemiring作用
  签名: Gal(L/K) B] [h
  定义体: { toIsGaloisGroup := h }

Depends on / 依赖: toIsGaloisGroup
-/
instance [MulSemiringAction Gal(L/K) B] [h : IsGaloisGroup (stabilizer Gal(L/K) P) D L] :
    IsDecompositionField K L P D := { toIsGaloisGroup := h }

variable (E : Type*) [Field E] [Algebra E L]

/--
Let `L/K` be a Galois extension of fields and let `P` be a prime ideal of `B`. The predicate that
says that `E` is the inertia field of `P` in `L/K`, that is the subfield fixed by the inertia
subgroup of `P` in `Gal(L/K)`.
-/
@[mk_iff]
/--
Definition of `IsInertiaField` / `IsInertiaField` 的定义

English:
class IsInertiaField
  parameters: [MulSemiringAction Gal(L/K) B]
  (no additional axioms)

中文:
类 是InertiaField
  参数: [MulSemiring作用 Gal(L/K) B]
  (无附加公理)
-/
class IsInertiaField [MulSemiringAction Gal(L/K) B] extends
    IsGaloisGroup (inertia Gal(L/K) P) E L

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulSemiringAction
  signature: Gal(L/K) B] [h
  body: { toIsGaloisGroup := h }

中文:
实例 [MulSemiring作用
  签名: Gal(L/K) B] [h
  定义体: { toIsGaloisGroup := h }

Depends on / 依赖: toIsGaloisGroup
-/
instance [MulSemiringAction Gal(L/K) B] [h : IsGaloisGroup (inertia Gal(L/K) P) E L] :
    IsInertiaField K L P E := { toIsGaloisGroup := h }

variable [MulSemiringAction Gal(L/K) B]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsGalois
  signature: K L] : IsDecompositionField K L P
  body: IsGaloisGroup.subgroup Gal(L/K) K L (stabilizer Gal(L/K) P)

中文:
实例 [是Galois
  签名: K L] : 是DecompositionField K L P
  定义体: IsGaloisGroup.subgroup Gal(L/K) K L (stabilizer Gal(L/K) P)

Depends on / 依赖: IsGaloisGroup, IsGaloisGroup.subgroup, stabilizer, subgroup
-/
instance [IsGalois K L] : IsDecompositionField K L P
    (FixedPoints.intermediateField (stabilizer Gal(L/K) P) : IntermediateField K L) where
  toIsGaloisGroup := IsGaloisGroup.subgroup Gal(L/K) K L (stabilizer Gal(L/K) P)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsGalois
  signature: K L] : IsInertiaField K L P
  body: IsGaloisGroup.subgroup Gal(L/K) K L (inertia Gal(L/K) P)

中文:
实例 [是Galois
  签名: K L] : 是InertiaField K L P
  定义体: IsGaloisGroup.subgroup Gal(L/K) K L (inertia Gal(L/K) P)

Depends on / 依赖: IsGaloisGroup, IsGaloisGroup.subgroup, inertia, subgroup
-/
instance [IsGalois K L] : IsInertiaField K L P
    (FixedPoints.intermediateField (inertia Gal(L/K) P) : IntermediateField K L) where
  toIsGaloisGroup := IsGaloisGroup.subgroup Gal(L/K) K L (inertia Gal(L/K) P)

variable (G : Type*) [Group G] [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L]
  [MulSemiringAction G B]

section of_isGaloisGroup

variable [Algebra B L] [IsFractionRing B L] [SMulDistribClass Gal(L/K) B L] [SMulDistribClass G B L]

/--
theorem `IsDecompositionField.of_isGaloisGroup` / 定理 `IsDecompositionField.of_isGaloisGroup`

English:
theorem IsDecompositionField.of_isGaloisGroup
  given: [h : IsGaloisGroup (stabilizer G P) D L]
  proof: by
refine (isDecompositionField_iff K L P D).mpr .of_mulEquiv (hG := h) ?_ fun _ x => ?_
  · refine (stabilizerEquiv _ (IsGaloisGroup.mulEquivAlgEquiv G K L) fun _ _ => ?_).symm
    apply FaithfulSMul.algebraMap_injective B L
    simp [algebraMap.smul']
  · obtain ⟨y, z, _, rfl⟩ := IsFractionRing.di

中文:
定理 是DecompositionField.of_isGaloisGroup
  条件: [h : 是Galois群 (stabilizer G P) D L]
  证明: by
refine (isDecompositionField_iff K L P D).mpr .of_mulEquiv (hG := h) ?_ fun _ x => ?_
  · refine (stabilizerEquiv _ (IsGaloisGroup.mulEquivAlgEquiv G K L) fun _ _ => ?_).symm
    apply FaithfulSMul.algebraMap_injective B L
    simp [algebraMap.smul']
  · obtain ⟨y, z, _, rfl⟩ := IsFractionRing.di

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, IsFractionRing, IsFractionRing.div_surjective, IsGaloisGroup, IsGaloisGroup.mulEquivAlgEquiv, algebraMap, algebraMap.smul, algebraMap_injective, div_surjective, isDecompositionField_iff, mulEquivAlgEquiv, of_mulEquiv, simp_rw, stabilizerEquiv, stabilizerEquiv_symm_apply_smul, subgroup_smul_def
-/
theorem IsDecompositionField.of_isGaloisGroup [h : IsGaloisGroup (stabilizer G P) D L] :
    IsDecompositionField K L P D := by
refine (isDecompositionField_iff K L P D).mpr .of_mulEquiv (hG := h) ?_ fun _ x => ?_
  · refine (stabilizerEquiv _ (IsGaloisGroup.mulEquivAlgEquiv G K L) fun _ _ => ?_).symm
    apply FaithfulSMul.algebraMap_injective B L
    simp [algebraMap.smul']
  · obtain ⟨y, z, _, rfl⟩ := IsFractionRing.div_surjective B x
    simp_rw [smul_div₀', subgroup_smul_def, ← algebraMap.smul', ← subgroup_smul_def,
      stabilizerEquiv_symm_apply_smul]

/--
theorem `IsInertiaField.of_isGaloisGroup` / 定理 `IsInertiaField.of_isGaloisGroup`

English:
theorem IsInertiaField.of_isGaloisGroup
  given: [h : IsGaloisGroup (inertia G P) E L]
  proof: by
refine (isInertiaField_iff K L P E).mpr .of_mulEquiv (hG := h) ?_ fun _ x => ?_
  · refine (inertiaEquiv _ (IsGaloisGroup.mulEquivAlgEquiv G K L) fun _ _ => ?_).symm
    apply FaithfulSMul.algebraMap_injective B L
    simp [algebraMap.smul']
  · obtain ⟨y, z, _, rfl⟩ := IsFractionRing.div_surject

中文:
定理 是InertiaField.of_isGaloisGroup
  条件: [h : 是Galois群 (inertia G P) E L]
  证明: by
refine (isInertiaField_iff K L P E).mpr .of_mulEquiv (hG := h) ?_ fun _ x => ?_
  · refine (inertiaEquiv _ (IsGaloisGroup.mulEquivAlgEquiv G K L) fun _ _ => ?_).symm
    apply FaithfulSMul.algebraMap_injective B L
    simp [algebraMap.smul']
  · obtain ⟨y, z, _, rfl⟩ := IsFractionRing.div_surject

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, IsFractionRing, IsFractionRing.div_surjective, IsGaloisGroup, IsGaloisGroup.mulEquivAlgEquiv, algebraMap, algebraMap.smul, algebraMap_injective, div_surjective, inertiaEquiv, inertiaEquiv_symm_apply_smul, isInertiaField_iff, mulEquivAlgEquiv, of_mulEquiv, simp_rw, subgroup_smul_def
-/
theorem IsInertiaField.of_isGaloisGroup [h : IsGaloisGroup (inertia G P) E L] :
    IsInertiaField K L P E := by
refine (isInertiaField_iff K L P E).mpr .of_mulEquiv (hG := h) ?_ fun _ x => ?_
  · refine (inertiaEquiv _ (IsGaloisGroup.mulEquivAlgEquiv G K L) fun _ _ => ?_).symm
    apply FaithfulSMul.algebraMap_injective B L
    simp [algebraMap.smul']
  · obtain ⟨y, z, _, rfl⟩ := IsFractionRing.div_surjective B x
    simp_rw [smul_div₀', subgroup_smul_def, ← algebraMap.smul', ← subgroup_smul_def,
      inertiaEquiv_symm_apply_smul]

end of_isGaloisGroup

variable (D' : Type*) [Field D'] [Algebra D' L] (E' : Type*) [Field E'] [Algebra E' L]

/--
Definition of `IsDecompositionField.ringEquiv` / `IsDecompositionField.ringEquiv` 的定义

English:
definition IsDecompositionField.ringEquiv
  signature: [IsDecompositionField K L P D]
  body: IsGaloisGroup.ringEquiv (stabilizer Gal(L/K) P) D D' L

@[simp]

中文:
定义 是DecompositionField.ringEquiv
  签名: [是DecompositionField K L P D]
  定义体: IsGaloisGroup.ringEquiv (stabilizer Gal(L/K) P) D D' L

@[simp]

Depends on / 依赖: IsGaloisGroup, IsGaloisGroup.ringEquiv, ringEquiv, stabilizer
-/
noncomputable def IsDecompositionField.ringEquiv [IsDecompositionField K L P D]
    [IsDecompositionField K L P D'] :
    D ≃+* D' :=
  IsGaloisGroup.ringEquiv (stabilizer Gal(L/K) P) D D' L

@[simp]
/--
theorem `IsDecompositionField.algebraMap_ringEquiv_apply` / 定理 `IsDecompositionField.algebraMap_ringEquiv_apply`

English:
theorem IsDecompositionField.algebraMap_ringEquiv_apply
  statement: [IsDecompositionField K L P D]
  proof: by
  simp [IsDecompositionField.ringEquiv, IsGaloisGroup.ringEquiv]

@[simp]

中文:
定理 是DecompositionField.algebraMap_ringEquiv_apply
  结论: [是DecompositionField K L P D]
  证明: by
  simp [IsDecompositionField.ringEquiv, IsGaloisGroup.ringEquiv]

@[simp]

Depends on / 依赖: IndepFun, IsDecompositionField, IsDecompositionField.ringEquiv, IsGaloisGroup, IsGaloisGroup.ringEquiv, Kernel, Kernel.IndepFun.process_congr_left, process_congr_left, ringEquiv
-/
theorem IsDecompositionField.algebraMap_ringEquiv_apply [IsDecompositionField K L P D]
    [IsDecompositionField K L P D'] (x : D) :
    algebraMap D' L (IsDecompositionField.ringEquiv K L P D D' x) = algebraMap D L x := by
  simp [IsDecompositionField.ringEquiv, IsGaloisGroup.ringEquiv]

@[simp]
/--
theorem `IsDecompositionField.algebraMap_ringEquiv_symm_apply` / 定理 `IsDecompositionField.algebraMap_ringEquiv_symm_apply`

English:
theorem IsDecompositionField.algebraMap_ringEquiv_symm_apply
  statement: [IsDecompositionField K L P D]
  proof: by
  simp [IsDecompositionField.ringEquiv, IsGaloisGroup.ringEquiv]

中文:
定理 是DecompositionField.algebraMap_ringEquiv_symm_apply
  结论: [是DecompositionField K L P D]
  证明: by
  simp [IsDecompositionField.ringEquiv, IsGaloisGroup.ringEquiv]

Depends on / 依赖: IndepFun, IsDecompositionField, IsDecompositionField.ringEquiv, IsGaloisGroup, IsGaloisGroup.ringEquiv, Kernel, Kernel.IndepFun.process_congr_right, process_congr_right, ringEquiv
-/
theorem IsDecompositionField.algebraMap_ringEquiv_symm_apply [IsDecompositionField K L P D]
    [IsDecompositionField K L P D'] (x : D') :
    algebraMap D L ((IsDecompositionField.ringEquiv K L P D D').symm x) = algebraMap D' L x := by
  simp [IsDecompositionField.ringEquiv, IsGaloisGroup.ringEquiv]

/--
Definition of `IsInertiaField.ringEquiv` / `IsInertiaField.ringEquiv` 的定义

English:
definition IsInertiaField.ringEquiv
  signature: [IsInertiaField K L P E] [IsInertiaField K L P E']
  body: IsGaloisGroup.ringEquiv (inertia Gal(L/K) P) E E' L

@[simp]

中文:
定义 是InertiaField.ringEquiv
  签名: [是InertiaField K L P E] [是InertiaField K L P E']
  定义体: IsGaloisGroup.ringEquiv (inertia Gal(L/K) P) E E' L

@[simp]

Depends on / 依赖: IndepFun, IsGaloisGroup, IsGaloisGroup.ringEquiv, Kernel, Kernel.IndepFun.process_congr, inertia, process_congr, ringEquiv
-/
noncomputable def IsInertiaField.ringEquiv [IsInertiaField K L P E] [IsInertiaField K L P E'] :
    E ≃+* E' :=
  IsGaloisGroup.ringEquiv (inertia Gal(L/K) P) E E' L

@[simp]
/--
theorem `IsInertiaField.algebraMap_ringEquiv_apply` / 定理 `IsInertiaField.algebraMap_ringEquiv_apply`

English:
theorem IsInertiaField.algebraMap_ringEquiv_apply
  statement: [IsInertiaField K L P E]
  proof: by
  simp [IsInertiaField.ringEquiv, IsGaloisGroup.ringEquiv]

@[simp]

中文:
定理 是InertiaField.algebraMap_ringEquiv_apply
  结论: [是InertiaField K L P E]
  证明: by
  simp [IsInertiaField.ringEquiv, IsGaloisGroup.ringEquiv]

@[simp]

Depends on / 依赖: IndepFun, IsGaloisGroup, IsGaloisGroup.ringEquiv, IsInertiaField, IsInertiaField.ringEquiv, Kernel, Kernel.IndepFun.process_indepFun, process_indepFun, ringEquiv
-/
theorem IsInertiaField.algebraMap_ringEquiv_apply [IsInertiaField K L P E]
    [IsInertiaField K L P E'] (x : E) :
    algebraMap E' L (IsInertiaField.ringEquiv K L P E E' x) = algebraMap E L x := by
  simp [IsInertiaField.ringEquiv, IsGaloisGroup.ringEquiv]

@[simp]
/--
theorem `IsInertiaField.algebraMap_ringEquiv_symm_apply` / 定理 `IsInertiaField.algebraMap_ringEquiv_symm_apply`

English:
theorem IsInertiaField.algebraMap_ringEquiv_symm_apply
  statement: [IsInertiaField K L P E]
  proof: by
  simp [IsInertiaField.ringEquiv, IsGaloisGroup.ringEquiv]

中文:
定理 是InertiaField.algebraMap_ringEquiv_symm_apply
  结论: [是InertiaField K L P E]
  证明: by
  simp [IsInertiaField.ringEquiv, IsGaloisGroup.ringEquiv]

Depends on / 依赖: IndepFun, IsGaloisGroup, IsGaloisGroup.ringEquiv, IsInertiaField, IsInertiaField.ringEquiv, Kernel, Kernel.IndepFun.process_indepFun, ringEquiv
-/
theorem IsInertiaField.algebraMap_ringEquiv_symm_apply [IsInertiaField K L P E]
    [IsInertiaField K L P E'] (x : E') :
    algebraMap E L ((IsInertiaField.ringEquiv K L P E E').symm x) = algebraMap E' L x := by
  simp [IsInertiaField.ringEquiv, IsGaloisGroup.ringEquiv]

end basic

section rank

attribute [local instance] Ideal.Quotient.field

variable [FiniteDimensional K L] [MulSemiringAction Gal(L/K) B]
  [IsGaloisGroup Gal(L/K) A B] [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [Ring.HasFiniteQuotients A] [P.IsMaximal]

variable (D : Type*) [Field D] [Algebra D L] [IsDecompositionField K L P D]

include K P

/--
theorem `IsDecompositionField.rank_left` / 定理 `IsDecompositionField.rank_left`

English:
theorem IsDecompositionField.rank_left
  given: (hp : p != ⊥)
  proof: by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  rw [← IsGaloisGroup.card_eq_finrank (stabilizer Gal(L/K) P) D L]; rw [card_stabilizer_eq p]

中文:
定理 是DecompositionField.rank_left
  条件: (hp : p != ⊥)
  证明: by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  rw [← IsGaloisGroup.card_eq_finrank (stabilizer Gal(L/K) P) D L]; rw [card_stabilizer_eq p]

Depends on / 依赖: Finite, HasFiniteQuotients, Ideal.IsMaximal.under, IndepFun, IsGaloisGroup, IsGaloisGroup.card_eq_finrank, IsMaximal, Kernel, Kernel.IndepFun.indepFun_process, Ring.HasFiniteQuotients.finiteQuotient, card_eq_finrank, card_stabilizer_eq, finiteQuotient, indepFun_process, over_def, p.IsMaximal, stabilizer
-/
theorem IsDecompositionField.rank_left (hp : p != ⊥) :
    Module.finrank D L = p.ramificationIdxIn B * p.inertiaDegIn B := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  rw [← IsGaloisGroup.card_eq_finrank (stabilizer Gal(L/K) P) D L]; rw [card_stabilizer_eq p]

/--
theorem `IsDecompositionField.rank_right` / 定理 `IsDecompositionField.rank_right`

English:
theorem IsDecompositionField.rank_right
  statement: [IsGalois K L] [Algebra K D] [IsScalarTower K D L]
  proof: by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : FiniteDimensional D L := FiniteDimensional.right K D L
  refine mul_left_injective₀ (b := Module.finrank D L) Module.finrank_pos.ne' ?_
  dsimp only
  rw [Module.finrank_mul_finrank]; rw [rank_left A K L P D hp]; rw [ncard_

中文:
定理 是DecompositionField.rank_right
  结论: [是Galois K L] [代数 K D] [标量塔 K D L]
  证明: by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : FiniteDimensional D L := FiniteDimensional.right K D L
  refine mul_left_injective₀ (b := Module.finrank D L) Module.finrank_pos.ne' ?_
  dsimp only
  rw [Module.finrank_mul_finrank]; rw [rank_left A K L P D hp]; rw [ncard_

Depends on / 依赖: FiniteDimensional, FiniteDimensional.right, Ideal.IsMaximal.under, IndepFun, IsGaloisGroup, IsGaloisGroup.card_eq_finrank, IsMaximal, Kernel, Kernel.IndepFun.indepFun_process, Module, Module.finrank, Module.finrank_mul_finrank, Module.finrank_pos.ne, card_eq_finrank, finrank, finrank_mul_finrank, finrank_pos, ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn, over_def, p.IsMaximal
-/
theorem IsDecompositionField.rank_right [IsGalois K L] [Algebra K D] [IsScalarTower K D L]
    (hp : p != ⊥) :
    Module.finrank K D = (p.primesOver B).ncard := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : FiniteDimensional D L := FiniteDimensional.right K D L
  refine mul_left_injective₀ (b := Module.finrank D L) Module.finrank_pos.ne' ?_
  dsimp only
  rw [Module.finrank_mul_finrank]; rw [rank_left A K L P D hp]; rw [ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B Gal(L/K)]; rw [IsGaloisGroup.card_eq_finrank Gal(L/K) K L]

variable (E : Type*) [Field E] [Algebra E L] [IsInertiaField K L P E]

/--
theorem `IsInertiaField.rank_left` / 定理 `IsInertiaField.rank_left`

English:
theorem IsInertiaField.rank_left
  given: (hp : p != ⊥)
  proof: by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  rw [← IsGaloisGroup.card_eq_finrank (inertia Gal(L/K) P) E L]; rw [card_inertia_eq_ramificationIdxIn p]

中文:
定理 是InertiaField.rank_left
  条件: (hp : p != ⊥)
  证明: by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  rw [← IsGaloisGroup.card_eq_finrank (inertia Gal(L/K) P) E L]; rw [card_inertia_eq_ramificationIdxIn p]

Depends on / 依赖: Finite, HasFiniteQuotients, Ideal.IsMaximal.under, IndepFun, IsGaloisGroup, IsGaloisGroup.card_eq_finrank, IsMaximal, Kernel, Kernel.IndepFun.process_indepFun_process, Ring.HasFiniteQuotients.finiteQuotient, card_eq_finrank, card_inertia_eq_ramificationIdxIn, finiteQuotient, inertia, over_def, p.IsMaximal, process_indepFun_process
-/
theorem IsInertiaField.rank_left (hp : p != ⊥) :
    Module.finrank E L = p.ramificationIdxIn B := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  rw [← IsGaloisGroup.card_eq_finrank (inertia Gal(L/K) P) E L]; rw [card_inertia_eq_ramificationIdxIn p]

/--
theorem `IsInertiaField.rank_right` / 定理 `IsInertiaField.rank_right`

English:
theorem IsInertiaField.rank_right
  given: [IsGalois K L] [Algebra K E] [IsScalarTower K E L] (hp : p != ⊥)
  proof: by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : FiniteDimensional E L := FiniteDimensional.right K E L
  refine mul_left_injective₀ (b := Module.finrank E L) Module.finrank_pos.ne' ?_
  dsimp only
  rw [Module.finrank_mul_finrank]; rw [rank_left A K L P E hp]; rw [mul_as

中文:
定理 是InertiaField.rank_right
  条件: [是Galois K L] [代数 K E] [标量塔 K E L] (hp : p != ⊥)
  证明: by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : FiniteDimensional E L := FiniteDimensional.right K E L
  refine mul_left_injective₀ (b := Module.finrank E L) Module.finrank_pos.ne' ?_
  dsimp only
  rw [Module.finrank_mul_finrank]; rw [rank_left A K L P E hp]; rw [mul_as

Depends on / 依赖: FiniteDimensional, FiniteDimensional.right, Ideal.IsMaximal.under, IndepFun, IsGaloisGroup, IsGaloisGroup.card_eq_finrank, IsMaximal, Kernel, Kernel.IndepFun.process_indepFun_process, Module, Module.finrank, Module.finrank_mul_finrank, Module.finrank_pos.ne, card_eq_finrank, finrank, finrank_mul_finrank, finrank_pos, inertiaDegIn, mul_assoc, mul_comm
-/
theorem IsInertiaField.rank_right [IsGalois K L] [Algebra K E] [IsScalarTower K E L] (hp : p != ⊥) :
    Module.finrank K E = (p.primesOver B).ncard * p.inertiaDegIn B := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : FiniteDimensional E L := FiniteDimensional.right K E L
  refine mul_left_injective₀ (b := Module.finrank E L) Module.finrank_pos.ne' ?_
  dsimp only
  rw [Module.finrank_mul_finrank]; rw [rank_left A K L P E hp]; rw [mul_assoc]; rw [mul_comm (p.inertiaDegIn B)]; rw [ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B Gal(L/K)]; rw [IsGaloisGroup.card_eq_finrank Gal(L/K) K L]

/--
theorem `IsInertiaField.rank_decompositionField` / 定理 `IsInertiaField.rank_decompositionField`

English:
theorem IsInertiaField.rank_decompositionField
  statement: [IsGalois K L] [Algebra K D] [Algebra K E]
  proof: by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have := Module.finrank_mul_finrank K D E
  rwa [IsInertiaField.rank_right A K L P E hp, IsDecompositionField.rank_right A K L P D hp,
    mul_right_inj'] at this
  exact IsDedekindDomain.primesOver_ncard_ne_zero p B

中文:
定理 是InertiaField.rank_decompositionField
  结论: [是Galois K L] [代数 K D] [代数 K E]
  证明: by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have := Module.finrank_mul_finrank K D E
  rwa [IsInertiaField.rank_right A K L P E hp, IsDecompositionField.rank_right A K L P D hp,
    mul_right_inj'] at this
  exact IsDedekindDomain.primesOver_ncard_ne_zero p B

Depends on / 依赖: Ideal.IsMaximal.under, IsDecompositionField, IsDecompositionField.rank_right, IsDedekindDomain, IsDedekindDomain.primesOver_ncard_ne_zero, IsInertiaField, IsInertiaField.rank_right, IsMaximal, Kernel, Kernel.iIndepFun.process_congr, Module, Module.finrank_mul_finrank, finrank_mul_finrank, iIndepFun, mul_right_inj, over_def, p.IsMaximal, primesOver_ncard_ne_zero, process_congr, rank_right
-/
theorem IsInertiaField.rank_decompositionField [IsGalois K L] [Algebra K D] [Algebra K E]
    [Algebra D E] [IsScalarTower K D E] [IsScalarTower K E L] [IsScalarTower K D L] (hp : p != ⊥) :
    Module.finrank D E = p.inertiaDegIn B := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have := Module.finrank_mul_finrank K D E
  rwa [IsInertiaField.rank_right A K L P E hp, IsDecompositionField.rank_right A K L P D hp,
    mul_right_inj'] at this
  exact IsDedekindDomain.primesOver_ncard_ne_zero p B

end rank

section splitting

variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L] [Algebra B L]
  [IsScalarTower A B L] [IsFractionRing B L] [MulSemiringAction Gal(L/K) B]
  [SMulDistribClass Gal(L/K) B L]

namespace IsDecompositionField

variable (D 𝓞D : Type*) [Field D] [Algebra D L] [IsDecompositionField K L P D] [CommRing 𝓞D]
  [Algebra 𝓞D D] [IsFractionRing 𝓞D D] [Algebra 𝓞D B] [Algebra 𝓞D L] [IsScalarTower 𝓞D D L]
  [IsScalarTower 𝓞D B L] (𝓟D : Ideal 𝓞D) [hD : P.LiesOver 𝓟D]

include K L D in
/--
theorem `primesOver_eq_singleton` / 定理 `primesOver_eq_singleton`

English:
theorem primesOver_eq_singleton
  statement: [hP : P.IsPrime] [Finite (stabilizer Gal(L/K) P)]
  proof: by
  have := IsGaloisGroup.of_isFractionRing (stabilizer Gal(L/K) P) 𝓞D B D L
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨hP, hD⟩, ?_⟩
  rintro Q ⟨_, _⟩
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup 𝓟D P Q (stabilizer Gal(L/K) P)
  exact σ.prop

中文:
定理 primesOver_eq_singleton
  结论: [hP : P.是素] [有限 (stabilizer Gal(L/K) P)]
  证明: by
  have := IsGaloisGroup.of_isFractionRing (stabilizer Gal(L/K) P) 𝓞D B D L
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨hP, hD⟩, ?_⟩
  rintro Q ⟨_, _⟩
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup 𝓟D P Q (stabilizer Gal(L/K) P)
  exact σ.prop

Depends on / 依赖: IsGaloisGroup, IsGaloisGroup.of_isFractionRing, Kernel, Kernel.iIndepFun.iIndepFun_process, Set.eq_singleton_iff_unique_mem.mpr, eq_singleton_iff_unique_mem, exists_smul_eq_of_isGaloisGroup, iIndepFun, iIndepFun_process, of_isFractionRing, stabilizer
-/
theorem primesOver_eq_singleton [hP : P.IsPrime] [Finite (stabilizer Gal(L/K) P)]
    [IsIntegrallyClosed 𝓞D] [Algebra.IsIntegral 𝓞D B] :
    primesOver 𝓟D B = {P} := by
  have := IsGaloisGroup.of_isFractionRing (stabilizer Gal(L/K) P) 𝓞D B D L
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨hP, hD⟩, ?_⟩
  rintro Q ⟨_, _⟩
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup 𝓟D P Q (stabilizer Gal(L/K) P)
  exact σ.prop

variable [IsGalois K L] [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [Algebra A 𝓞D] [Module.Finite A 𝓞D] [IsScalarTower A 𝓞D B]
  [IsDedekindDomain 𝓞D] [𝓟D.LiesOver p]

omit [P.LiesOver p] hD in
include K L D P in
/--
lemma `instances` / 引理 `instances`

English:
lemma instances
  given: (hp : p != ⊥)
  proof: by
  have inst₁ : Module.Finite 𝓞D B := Module.Finite.right A 𝓞D B
  have inst₂ : Module.IsTorsionFree 𝓞D B := by
    rw [Module.isTorsionFree_iff_faithfulSMul]
    apply Algebra.IsAlgebraic.faithfulSMul_tower_top A
  have inst₃ : Module.IsTorsionFree A 𝓞D := Module.IsTorsionFree.of_faithfulSMul _ _

中文:
引理 instances
  条件: (hp : p != ⊥)
  证明: by
  have inst₁ : Module.Finite 𝓞D B := Module.Finite.right A 𝓞D B
  have inst₂ : Module.IsTorsionFree 𝓞D B := by
    rw [Module.isTorsionFree_iff_faithfulSMul]
    apply Algebra.IsAlgebraic.faithfulSMul_tower_top A
  have inst₃ : Module.IsTorsionFree A 𝓞D := Module.IsTorsionFree.of_faithfulSMul _ _

Depends on / 依赖: Kernel, Kernel.iIndepFun.iIndepFun_process, iIndepFun
-/
private lemma instances (hp : p != ⊥) :
    Module.Finite 𝓞D B ∧ Module.IsTorsionFree 𝓞D B ∧ Module.IsTorsionFree A 𝓞D ∧
      IsGaloisGroup Gal(L/K) A B ∧ IsGaloisGroup (stabilizer Gal(L/K) P) 𝓞D B ∧ 𝓟D != ⊥ := by
  have inst₁ : Module.Finite 𝓞D B := Module.Finite.right A 𝓞D B
  have inst₂ : Module.IsTorsionFree 𝓞D B := by
    rw [Module.isTorsionFree_iff_faithfulSMul]
    apply Algebra.IsAlgebraic.faithfulSMul_tower_top A
  have inst₃ : Module.IsTorsionFree A 𝓞D := Module.IsTorsionFree.of_faithfulSMul _ _ B
  have inst₄ : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  have inst₅ : IsGaloisGroup (stabilizer Gal(L/K) P) 𝓞D B := .of_isFractionRing _ _ _ D L
  exact ⟨inst₁, inst₂, inst₃, inst₄, inst₅, Ideal.ne_bot_of_liesOver_of_ne_bot hp 𝓟D⟩

variable [FiniteDimensional K L] [Ring.HasFiniteQuotients A] [𝓟D.IsMaximal] [P.IsMaximal]

include K L D P in
/--
lemma `ramificationIdxIn_eq_and_inertiaDegIn_eq` / 引理 `ramificationIdxIn_eq_and_inertiaDegIn_eq`

English:
lemma ramificationIdxIn_eq_and_inertiaDegIn_eq
  given: (hp : p != ⊥)
  proof: by
  obtain ⟨_, _, _, _, _, h𝓟⟩ := instances A K L P D 𝓞D 𝓟D hp
  refine eq_and_eq_of_pos_of_le_of_mul_le_mul ?_ ?_ ?_ ?_ ?_
· exact Nat.pos_of_ne_zero ramificationIdxIn_ne_zero (stabilizer Gal(L/K) P)
· exact Nat.pos_of_ne_zero inertiaDegIn_ne_zero (stabilizer Gal(L/K) P)
  · rw [ramificationIdxIn_

中文:
引理 ramificationIdxIn_eq_and_inertiaDegIn_eq
  条件: (hp : p != ⊥)
  证明: by
  obtain ⟨_, _, _, _, _, h𝓟⟩ := instances A K L P D 𝓞D 𝓟D hp
  refine eq_and_eq_of_pos_of_le_of_mul_le_mul ?_ ?_ ?_ ?_ ?_
· exact Nat.pos_of_ne_zero ramificationIdxIn_ne_zero (stabilizer Gal(L/K) P)
· exact Nat.pos_of_ne_zero inertiaDegIn_ne_zero (stabilizer Gal(L/K) P)
  · rw [ramificationIdxIn_
-/
private lemma ramificationIdxIn_eq_and_inertiaDegIn_eq (hp : p != ⊥) :
    ramificationIdxIn 𝓟D B = p.ramificationIdxIn B ∧ inertiaDegIn 𝓟D B = p.inertiaDegIn B := by
  obtain ⟨_, _, _, _, _, h𝓟⟩ := instances A K L P D 𝓞D 𝓟D hp
  refine eq_and_eq_of_pos_of_le_of_mul_le_mul ?_ ?_ ?_ ?_ ?_
· exact Nat.pos_of_ne_zero ramificationIdxIn_ne_zero (stabilizer Gal(L/K) P)
· exact Nat.pos_of_ne_zero inertiaDegIn_ne_zero (stabilizer Gal(L/K) P)
  · rw [ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
      ramificationIdxIn_eq_ramificationIdx _ P (stabilizer Gal(L/K) P)]
    exact 𝓟D.ramificationIdx_above_le P
  · rw [inertiaDegIn_eq_inertiaDeg p P Gal(L/K),
      inertiaDegIn_eq_inertiaDeg _ P (stabilizer Gal(L/K) P)]
    exact inertiaDeg_above_le 𝓟D P
  · have := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝓟D B (stabilizer Gal(L/K) P)
    rw [primesOver_eq_singleton K L P D 𝓞D]; rw [Set.ncard_singleton]; rw [one_mul] at this
    rw [this]; rw [IsGaloisGroup.card_eq_finrank (stabilizer Gal(L/K) P) D L]; rw [IsDecompositionField.rank_left A K L P D hp]

include K L D P in
/--
theorem `ramificationIdxIn_eq` / 定理 `ramificationIdxIn_eq`

English:
theorem ramificationIdxIn_eq
  given: (hp : p != ⊥)
  proof: (ramificationIdxIn_eq_and_inertiaDegIn_eq A K L P D 𝓞D 𝓟D hp).1

include K L D P in

中文:
定理 ramificationIdxIn_eq
  条件: (hp : p != ⊥)
  证明: (ramificationIdxIn_eq_and_inertiaDegIn_eq A K L P D 𝓞D 𝓟D hp).1

include K L D P in

Depends on / 依赖: ramificationIdxIn_eq_and_inertiaDegIn_eq
-/
theorem ramificationIdxIn_eq (hp : p != ⊥) :
    ramificationIdxIn 𝓟D B = p.ramificationIdxIn B :=
  (ramificationIdxIn_eq_and_inertiaDegIn_eq A K L P D 𝓞D 𝓟D hp).1

include K L D P in
/--
theorem `inertiaDegIn_eq` / 定理 `inertiaDegIn_eq`

English:
theorem inertiaDegIn_eq
  given: (hp : p != ⊥)
  proof: (ramificationIdxIn_eq_and_inertiaDegIn_eq A K L P D 𝓞D 𝓟D hp).2

include K L D P in

中文:
定理 inertiaDegIn_eq
  条件: (hp : p != ⊥)
  证明: (ramificationIdxIn_eq_and_inertiaDegIn_eq A K L P D 𝓞D 𝓟D hp).2

include K L D P in

Depends on / 依赖: ramificationIdxIn_eq_and_inertiaDegIn_eq
-/
theorem inertiaDegIn_eq (hp : p != ⊥) :
    inertiaDegIn 𝓟D B = p.inertiaDegIn B :=
  (ramificationIdxIn_eq_and_inertiaDegIn_eq A K L P D 𝓞D 𝓟D hp).2

include K L D P in
/--
theorem `ramificationIdx_eq` / 定理 `ramificationIdx_eq`

English:
theorem ramificationIdx_eq
  given: (hp : p != ⊥)
  proof: by
  obtain ⟨_, _, _, _, _, h𝓟⟩ := instances A K L P D 𝓞D 𝓟D hp
  have := ramificationIdx_tower (R := A) 𝓟D P
  rwa [← ramificationIdxIn_eq_ramificationIdx 𝓟D P (stabilizer Gal(L/K) P),
    ramificationIdxIn_eq A K L P D 𝓞D 𝓟D hp, ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
right_eq_mul₀ (ram

中文:
定理 ramificationIdx_eq
  条件: (hp : p != ⊥)
  证明: by
  obtain ⟨_, _, _, _, _, h𝓟⟩ := instances A K L P D 𝓞D 𝓟D hp
  have := ramificationIdx_tower (R := A) 𝓟D P
  rwa [← ramificationIdxIn_eq_ramificationIdx 𝓟D P (stabilizer Gal(L/K) P),
    ramificationIdxIn_eq A K L P D 𝓞D 𝓟D hp, ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
right_eq_mul₀ (ram

Depends on / 依赖: instances, ramificationIdxIn_eq, ramificationIdxIn_eq_ramificationIdx, ramificationIdx_pos, ramificationIdx_tower, stabilizer
-/
theorem ramificationIdx_eq (hp : p != ⊥) :
    𝓟D.ramificationIdx A = 1 := by
  obtain ⟨_, _, _, _, _, h𝓟⟩ := instances A K L P D 𝓞D 𝓟D hp
  have := ramificationIdx_tower (R := A) 𝓟D P
  rwa [← ramificationIdxIn_eq_ramificationIdx 𝓟D P (stabilizer Gal(L/K) P),
    ramificationIdxIn_eq A K L P D 𝓞D 𝓟D hp, ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
right_eq_mul₀ (ramificationIdx_pos P A).ne'] at this

include K L D P in
/--
theorem `inertiaDeg_eq` / 定理 `inertiaDeg_eq`

English:
theorem inertiaDeg_eq
  given: (hp : p != ⊥)
  proof: by
  obtain ⟨_, _, _, _, _, _⟩ := instances A K L P D 𝓞D 𝓟D hp
  have := inertiaDeg_tower (R := A) 𝓟D P
  rwa [← inertiaDegIn_eq_inertiaDeg p P Gal(L/K), ← inertiaDegIn_eq A K L P D 𝓞D 𝓟D hp,
    ← inertiaDegIn_eq_inertiaDeg 𝓟D P (stabilizer Gal(L/K) P),
right_eq_mul₀ inertiaDegIn_ne_zero (stabilize

中文:
定理 inertiaDeg_eq
  条件: (hp : p != ⊥)
  证明: by
  obtain ⟨_, _, _, _, _, _⟩ := instances A K L P D 𝓞D 𝓟D hp
  have := inertiaDeg_tower (R := A) 𝓟D P
  rwa [← inertiaDegIn_eq_inertiaDeg p P Gal(L/K), ← inertiaDegIn_eq A K L P D 𝓞D 𝓟D hp,
    ← inertiaDegIn_eq_inertiaDeg 𝓟D P (stabilizer Gal(L/K) P),
right_eq_mul₀ inertiaDegIn_ne_zero (stabilize

Depends on / 依赖: inertiaDegIn_eq, inertiaDegIn_eq_inertiaDeg, inertiaDegIn_ne_zero, inertiaDeg_tower, instances, stabilizer
-/
theorem inertiaDeg_eq (hp : p != ⊥) :
    𝓟D.inertiaDeg A = 1 := by
  obtain ⟨_, _, _, _, _, _⟩ := instances A K L P D 𝓞D 𝓟D hp
  have := inertiaDeg_tower (R := A) 𝓟D P
  rwa [← inertiaDegIn_eq_inertiaDeg p P Gal(L/K), ← inertiaDegIn_eq A K L P D 𝓞D 𝓟D hp,
    ← inertiaDegIn_eq_inertiaDeg 𝓟D P (stabilizer Gal(L/K) P),
right_eq_mul₀ inertiaDegIn_ne_zero (stabilizer Gal(L/K) P)] at this

end IsDecompositionField

end splitting
