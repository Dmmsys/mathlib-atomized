/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Basis.Basic
public import Mathlib.Algebra.Lie.Weights.RootSystem
public import Mathlib.LinearAlgebra.RootSystem.BaseExists
public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

/-!

# The root system base associated to a Lie algebra basis

-/

@[expose] public section

noncomputable section

namespace LieAlgebra.Basis

open AddSubmonoid Function IsKilling LieModule LieSubalgebra Matrix Set

variable {ι K L : Type*} [Fintype ι] [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] {H : LieSubalgebra K L} (b : Basis ι H)

/--
Definition of `baseSupp'` / `baseSupp'` 的定义

English:
definition baseSupp'
  signature: (i : ι)
  body: b.isCartanSubalgebra
    H.root := by
  let := b.isCartanSubalgebra
  refine ⟨⟨b.baseSupp i, ?_⟩, ?_⟩
  · simp only [LieSubmodule.eq_bot_iff, ne_eq, not_forall]
    exact ⟨b.e i, (mem_genWeightSpace _ _ _).mpr fun x => ⟨1, by simp⟩, (b.sl2 i).e_ne_zero⟩
  · simpa [Weight.IsNonZero, Weight.IsZero] us

中文:
定义 baseSupp'
  签名: (i : ι)
  定义体: b.isCartanSubalgebra
    H.root := by
  let := b.isCartanSubalgebra
  refine ⟨⟨b.baseSupp i, ?_⟩, ?_⟩
  · simp only [LieSubmodule.eq_bot_iff, ne_eq, not_forall]
    exact ⟨b.e i, (mem_genWeightSpace _ _ _).mpr fun x => ⟨1, by simp⟩, (b.sl2 i).e_ne_zero⟩
  · simpa [Weight.IsNonZero, Weight.IsZero] us

Depends on / 依赖: b.isCartanSubalgebra, isCartanSubalgebra
-/
def baseSupp' (i : ι) :
    letI := b.isCartanSubalgebra
    H.root := by
  let := b.isCartanSubalgebra
  refine ⟨⟨b.baseSupp i, ?_⟩, ?_⟩
  · simp only [LieSubmodule.eq_bot_iff, ne_eq, not_forall]
    exact ⟨b.e i, (mem_genWeightSpace _ _ _).mpr fun x => ⟨1, by simp⟩, (b.sl2 i).e_ne_zero⟩
  · simpa [Weight.IsNonZero, Weight.IsZero] using b.linearIndependent_baseSupp.ne_zero i

/--
lemma `coe_linearMap_baseSupp'` / 引理 `coe_linearMap_baseSupp'`

English:
lemma coe_linearMap_baseSupp'
  given: (i : ι)
  statement: b.baseSupp' i = b.baseSupp i
  proof: rfl

中文:
引理 coe_linearMap_baseSupp'
  条件: (i : ι)
  结论: b.baseSupp' i = b.baseSupp i
  证明: rfl
-/
@[simp] lemma coe_linearMap_baseSupp' (i : ι) : b.baseSupp' i = b.baseSupp i := rfl

variable [IsTriangularizable K H L] [IsKilling K L]

/--
lemma `linearIndepOn_root_baseSupp` / 引理 `linearIndepOn_root_baseSupp`

English:
lemma linearIndepOn_root_baseSupp
  proof: b.isCartanSubalgebra
    LinearIndepOn K (rootSystem H).root (range b.baseSupp') := by
let e : ι ≃ range b.baseSupp' := Equiv.ofInjective _ fun i j hij =>
b.linearIndependent_baseSupp.injective by simpa [baseSupp'] using hij
  rw [LinearIndepOn]; rw [← linearIndependent_equiv e]
  exact b.linearInde

中文:
引理 linearIndepOn_root_baseSupp
  证明: b.isCartanSubalgebra
    LinearIndepOn K (rootSystem H).root (range b.baseSupp') := by
let e : ι ≃ range b.baseSupp' := Equiv.ofInjective _ fun i j hij =>
b.linearIndependent_baseSupp.injective by simpa [baseSupp'] using hij
  rw [LinearIndepOn]; rw [← linearIndependent_equiv e]
  exact b.linearInde

Depends on / 依赖: b.isCartanSubalgebra, isCartanSubalgebra
-/
lemma linearIndepOn_root_baseSupp :
    letI := b.isCartanSubalgebra
    LinearIndepOn K (rootSystem H).root (range b.baseSupp') := by
let e : ι ≃ range b.baseSupp' := Equiv.ofInjective _ fun i j hij =>
b.linearIndependent_baseSupp.injective by simpa [baseSupp'] using hij
  rw [LinearIndepOn]; rw [← linearIndependent_equiv e]
  exact b.linearIndependent_baseSupp

/--
lemma `root_mem_or_mem_neg` / 引理 `root_mem_or_mem_neg`

English:
lemma root_mem_or_mem_neg
  given: (χ : letI := b.isCartanSubalgebra; H.root)
  proof: b.isCartanSubalgebra
    ( (rootSystem H).root χ in closure ((rootSystem H).root '' range b.baseSupp') ∨
     -(rootSystem H).root χ in closure ((rootSystem H).root '' range b.baseSupp')) := by
  let := b.isCartanSubalgebra
  have (n : ι -> Nat) :
      ∑ i, n i • b.baseSupp i in closure (⇑(rootSyst

中文:
引理 root_mem_or_mem_neg
  条件: (χ : letI := b.isCartanSubalgebra; H.root)
  证明: b.isCartanSubalgebra
    ( (rootSystem H).root χ in closure ((rootSystem H).root '' range b.baseSupp') ∨
     -(rootSystem H).root χ in closure ((rootSystem H).root '' range b.baseSupp')) := by
  let := b.isCartanSubalgebra
  have (n : ι -> Nat) :
      ∑ i, n i • b.baseSupp i in closure (⇑(rootSyst

Depends on / 依赖: H.root, b.isCartanSubalgebra, isCartanSubalgebra
-/
lemma root_mem_or_mem_neg (χ : letI := b.isCartanSubalgebra; H.root) :
    letI := b.isCartanSubalgebra
    ( (rootSystem H).root χ in closure ((rootSystem H).root '' range b.baseSupp') ∨
     -(rootSystem H).root χ in closure ((rootSystem H).root '' range b.baseSupp')) := by
  let := b.isCartanSubalgebra
  have (n : ι -> Nat) :
      ∑ i, n i • b.baseSupp i in closure (⇑(rootSystem H).root '' range b.baseSupp') := by
    simp_rw [← Submodule.span_nat_eq_addSubmonoidClosure, Submodule.mem_toAddSubmonoid]
exact Submodule.sum_smul_mem _ _ fun i _ => Submodule.subset_span by simp
  let s : Set (H -> K) := {0} union
    {f | exists n : ι -> Nat, n != 0 ∧ f = -∑ i, n i • b.baseSupp i} union
    {f | exists n : ι -> Nat, n != 0 ∧ f = ∑ i, n i • b.baseSupp i}
  have hs : ⨆ α in s, rootSpace H α = ⊤ := by
    have := b.iSup_cartan_borelLower_borelUpper_eq_top
    rw [borelLower_eq]; rw [borelUpper_eq]; rw [b.cartan_eq] at this
    rw [iSup_union]; rw [iSup_union]
    simpa [iSup_and, iSup_comm (ι := H -> K)] using this
  obtain ⟨χ, hχ⟩ := χ
  change χ.toLinear in _ ∨ -χ.toLinear in _
  replace hs : ⇑χ in s :=
    (iSupIndep_genWeightSpace K H L).mem_of_biSup_eq_top hs χ.genWeightSpace_ne_bot
  replace hs : (exists n : ι -> Nat, n != 0 ∧ χ.toLinear = -∑ i, n i • b.baseSupp i) ∨
               (exists n : ι -> Nat, n != 0 ∧ χ.toLinear = ∑ i, n i • b.baseSupp i) := by
    have hχ' : ¬ χ.IsZero := by simpa using hχ
    simp only [hχ', s, singleton_union, mem_union, mem_insert_iff, Weight.coe_eq_zero_iff,
      mem_ofPred_eq, false_or] at hs
    simpa only [← LinearMap.coe_neg, ← Weight.coe_coe, LinearMap.coe_injective.eq_iff] using hs
  refine hs.symm.imp (fun ⟨n, hn₀, hn⟩ => ?_) (fun ⟨n, hn₀, hn⟩ => ?_) <;> simpa [hn] using this n

/--
Definition of `base` / `base` 的定义

English:
definition base
  signature: :
  body: b.isCartanSubalgebra
    RootPairing.Base (rootSystem H) :=
  letI := b.isCartanSubalgebra
  .mk' (rootSystem H) (range b.baseSupp') b.linearIndepOn_root_baseSupp b.root_mem_or_mem_neg

中文:
定义 base
  签名: :
  定义体: b.isCartanSubalgebra
    RootPairing.Base (rootSystem H) :=
  letI := b.isCartanSubalgebra
  .mk' (rootSystem H) (range b.baseSupp') b.linearIndepOn_root_baseSupp b.root_mem_or_mem_neg

Depends on / 依赖: b.isCartanSubalgebra, isCartanSubalgebra
-/
def base :
    letI := b.isCartanSubalgebra
    RootPairing.Base (rootSystem H) :=
  letI := b.isCartanSubalgebra
  .mk' (rootSystem H) (range b.baseSupp') b.linearIndepOn_root_baseSupp b.root_mem_or_mem_neg

/--
Definition of `baseSupportEquiv` / `baseSupportEquiv` 的定义

English:
definition baseSupportEquiv
  signature: : ι ≃ b.base.support
  body: have : Injective b.baseSupp' :=
fun i j hij => b.linearIndependent_baseSupp.injective by simpa [baseSupp'] using hij
  (Equiv.ofInjective _ this).trans (Set.Finite.subtypeEquivToFinset _)

中文:
定义 baseSupportEquiv
  签名: : ι ≃ b.base.support
  定义体: have : Injective b.baseSupp' :=
fun i j hij => b.linearIndependent_baseSupp.injective by simpa [baseSupp'] using hij
  (Equiv.ofInjective _ this).trans (Set.Finite.subtypeEquivToFinset _)

Depends on / 依赖: Equiv.ofInjective, Finite, Injective, Set.Finite.subtypeEquivToFinset, b.baseSupp, b.linearIndependent_baseSupp.injective, baseSupp, injective, linearIndependent_baseSupp, ofInjective, subtypeEquivToFinset
-/
def baseSupportEquiv : ι ≃ b.base.support :=
  have : Injective b.baseSupp' :=
fun i j hij => b.linearIndependent_baseSupp.injective by simpa [baseSupp'] using hij
  (Equiv.ofInjective _ this).trans (Set.Finite.subtypeEquivToFinset _)

/--
lemma `coe_baseSupportEquiv_apply` / 引理 `coe_baseSupportEquiv_apply`

English:
lemma coe_baseSupportEquiv_apply
  given: (i : ι)
  statement: b.baseSupportEquiv i = b.baseSupp i
  proof: rfl

中文:
引理 coe_baseSupportEquiv_apply
  条件: (i : ι)
  结论: b.baseSupportEquiv i = b.baseSupp i
  证明: rfl
-/
@[simp] lemma coe_baseSupportEquiv_apply (i : ι) : b.baseSupportEquiv i = b.baseSupp i := rfl

/--
lemma `coroot_eq_h'` / 引理 `coroot_eq_h'`

English:
lemma coroot_eq_h'
  given: (i : ι)
  proof: b.isCartanSubalgebra
    coroot (b.baseSupportEquiv i) = b.h' i := by
  let := b.isCartanSubalgebra
  suffices b.h' i in corootSpace (b.baseSupp' i) by
    have _i : IsAddTorsionFree L := .of_isTorsionFree K L
    exact (eq_coroot_of_mem_corootSpace_of_two (b.baseSupp' i).val this (by simp [baseSupp

中文:
引理 coroot_eq_h'
  条件: (i : ι)
  证明: b.isCartanSubalgebra
    coroot (b.baseSupportEquiv i) = b.h' i := by
  let := b.isCartanSubalgebra
  suffices b.h' i in corootSpace (b.baseSupp' i) by
    have _i : IsAddTorsionFree L := .of_isTorsionFree K L
    exact (eq_coroot_of_mem_corootSpace_of_two (b.baseSupp' i).val this (by simp [baseSupp
-/
@[simp] lemma coroot_eq_h' (i : ι) :
    letI := b.isCartanSubalgebra
    coroot (b.baseSupportEquiv i) = b.h' i := by
  let := b.isCartanSubalgebra
  suffices b.h' i in corootSpace (b.baseSupp' i) by
    have _i : IsAddTorsionFree L := .of_isTorsionFree K L
    exact (eq_coroot_of_mem_corootSpace_of_two (b.baseSupp' i).val this (by simp [baseSupp'])).symm
  have h_mem : ⁅b.e i, b.f i⁆ in H := by
    nth_rw 1 [(b.sl2 i).lie_e_f, b.cartan_eq_lieSpan]
exact subset_lieSpan mem_range_self i
  have h_eq : b.h' i = ⟨⁅b.e i, b.f i⁆, h_mem⟩ := by simp [(b.sl2 i).lie_e_f, h']
  rw [h_eq]
  have he : b.e i in rootSpace H (b.baseSupp i) :=
    (mem_genWeightSpace _ _ _).mpr fun ⟨z, hz⟩ => ⟨1, by simp⟩
  have hf : b.f i in rootSpace H (-b.baseSupp i) :=
    (mem_genWeightSpace _ _ _).mpr fun ⟨z, hz⟩ => ⟨1, by simp [← eq_neg_iff_add_eq_zero]⟩
exact (mem_corootSpace _).mpr Submodule.subset_span ⟨b.e i, he, b.f i, hf, rfl⟩

/--
lemma `cartanMatrix_base_eq` / 引理 `cartanMatrix_base_eq`

English:
lemma cartanMatrix_base_eq
  proof: by
  suffices b.base.cartanMatrix.reindex b.baseSupportEquiv.symm b.baseSupportEquiv.symm = b.A by
    rwa [← (reindex b.baseSupportEquiv b.baseSupportEquiv).symm_apply_eq]
  ext i j
  apply FaithfulSMul.algebraMap_injective Int K
  rw [reindex_apply]; rw [submatrix_apply]; rw [RootPairing.Base.alge

中文:
引理 cartanMatrix_base_eq
  证明: by
  suffices b.base.cartanMatrix.reindex b.baseSupportEquiv.symm b.baseSupportEquiv.symm = b.A by
    rwa [← (reindex b.baseSupportEquiv b.baseSupportEquiv).symm_apply_eq]
  ext i j
  apply FaithfulSMul.algebraMap_injective Int K
  rw [reindex_apply]; rw [submatrix_apply]; rw [RootPairing.Base.alge

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, RootPairing, RootPairing.Base.algebraMap_cartanMatrixIn_apply, Weight, Weight.coe_coe, algebraMap_cartanMatrixIn_apply, algebraMap_injective, b.base.cartanMatrix.reindex, b.baseSupportEquiv, b.baseSupportEquiv.symm, baseSupportEquiv, cartanMatrix, coe_coe, reindex, reindex_apply, submatrix_apply, symm_apply_eq
-/
lemma cartanMatrix_base_eq :
    b.base.cartanMatrix = b.A.reindex b.baseSupportEquiv b.baseSupportEquiv := by
  suffices b.base.cartanMatrix.reindex b.baseSupportEquiv.symm b.baseSupportEquiv.symm = b.A by
    rwa [← (reindex b.baseSupportEquiv b.baseSupportEquiv).symm_apply_eq]
  ext i j
  apply FaithfulSMul.algebraMap_injective Int K
  rw [reindex_apply]; rw [submatrix_apply]; rw [RootPairing.Base.algebraMap_cartanMatrixIn_apply]
  simp [← Weight.coe_coe]

end LieAlgebra.Basis
