/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.RootSystem.BaseChange
public import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear

/-!
# Nondegeneracy of the polarization on a finite root pairing

We show that if the base ring of a finite root pairing is linearly ordered, then the canonical
bilinear form is root-positive and positive-definite on the span of roots.
From these facts, it is easy to show that Coxeter weights in a finite root pairing are bounded
above by 4. Thus, the pairings of roots and coroots in a root pairing are restricted to the
interval `[-4, 4]`. Furthermore, a linearly independent pair of roots cannot have Coxeter weight 4.
For the case of crystallographic root pairings, we are thus reduced to a finite set of possible
options for each pair.
Another application is to the faithfulness of the Weyl group action on roots, and finiteness of the
Weyl group.

## Main results:
* `RootPairing.IsAnisotropic`: We say a finite root pairing is anisotropic if there are no roots /
  coroots which have length zero w.r.t. the root / coroot forms.
* `RootPairing.rootForm_pos_of_nonzero`: `RootForm` is strictly positive on non-zero linear
  combinations of roots. This gives us a convenient way to eliminate certain Dynkin diagrams from
  the classification, since it suffices to produce a nonzero linear combination of simple roots with
  non-positive norm.
* `RootPairing.rootForm_restrict_nondegenerate_of_ordered`: The root form is non-degenerate if
  the coefficients are ordered.
* `RootPairing.rootForm_restrict_nondegenerate_of_isAnisotropic`: the root form is
  non-degenerate if the coefficients are a field and the pairing is crystallographic.

## References:
* [N. Bourbaki, *Lie groups and Lie algebras. Chapters 4--6*][bourbaki1968]
* [M. Demazure, *SGA III, Exposé XXI, Données Radicielles*][demazure1970]

## Todo
* Weyl-invariance of `RootForm` and `CorootForm`
* Faithfulness of Weyl group perm action, and finiteness of Weyl group, over ordered rings.
* Relation to Coxeter weight.
-/

@[expose] public section

noncomputable section

open Set Function
open Module hiding reflection
open Submodule (span)

namespace RootPairing

variable {ι R M N : Type*} [Fintype ι] [AddCommGroup M] [AddCommGroup N]

section CommRing

variable [CommRing R] [Module R M] [Module R N] (P : RootPairing ι R M N)

/--
Definition of `IsAnisotropic` / `IsAnisotropic` 的定义

English:
class IsAnisotropic
  parameters: : Prop where
  axioms and operations (2):
    - rootForm_root_ne_zero((i : ι)) : P.RootForm (P.root i) (P.root i) != 0
    - corootForm_coroot_ne_zero((i : ι)) : P.CorootForm (P.coroot i) (P.coroot i) != 0

中文:
类 是Anisotropic
  参数: : 命题 where
  公理与运算 (2 个):
    - rootForm_root_ne_zero((i : ι)) : P.RootForm (P.root i) (P.root i) != 0
    - corootForm_coroot_ne_zero((i : ι)) : P.CorootForm (P.coroot i) (P.coroot i) != 0
-/
class IsAnisotropic : Prop where
  rootForm_root_ne_zero (i : ι) : P.RootForm (P.root i) (P.root i) != 0
  corootForm_coroot_ne_zero (i : ι) : P.CorootForm (P.coroot i) (P.coroot i) != 0

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsAnisotropic]
  signature: : P.flip.IsAnisotropic where
  body: IsAnisotropic.corootForm_coroot_ne_zero
  corootForm_coroot_ne_zero := IsAnisotropic.rootForm_root_ne_zero (P := P)

中文:
实例 [P.是Anisotropic]
  签名: : P.flip.是Anisotropic where
  定义体: IsAnisotropic.corootForm_coroot_ne_zero
  corootForm_coroot_ne_zero := IsAnisotropic.rootForm_root_ne_zero (P := P)

Depends on / 依赖: IsAnisotropic, IsAnisotropic.corootForm_coroot_ne_zero, corootForm_coroot_ne_zero
-/
instance [P.IsAnisotropic] : P.flip.IsAnisotropic where
  rootForm_root_ne_zero := IsAnisotropic.corootForm_coroot_ne_zero
  corootForm_coroot_ne_zero := IsAnisotropic.rootForm_root_ne_zero (P := P)

/--
lemma `isAnisotropic_of_isValuedIn` / 引理 `isAnisotropic_of_isValuedIn`

English:
lemma isAnisotropic_of_isValuedIn
  statement: (S : Type*)
  proof: (P.posRootForm S).form_apply_root_ne_zero i
  corootForm_coroot_ne_zero i := (P.flip.posRootForm S).form_apply_root_ne_zero i

中文:
引理 isAnisotropic_of_isValuedIn
  结论: (S : 类型)
  证明: (P.posRootForm S).form_apply_root_ne_zero i
  corootForm_coroot_ne_zero i := (P.flip.posRootForm S).form_apply_root_ne_zero i

Depends on / 依赖: P.posRootForm, form_apply_root_ne_zero, posRootForm
-/
lemma isAnisotropic_of_isValuedIn (S : Type*)
    [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
    [Algebra S R] [FaithfulSMul S R] [P.IsValuedIn S] :
    IsAnisotropic P where
  rootForm_root_ne_zero i := (P.posRootForm S).form_apply_root_ne_zero i
  corootForm_coroot_ne_zero i := (P.flip.posRootForm S).form_apply_root_ne_zero i

/--
Instance `instIsAnisotropicOfIsCrystallographic` / 实例 `instIsAnisotropicOfIsCrystallographic`

English:
instance instIsAnisotropicOfIsCrystallographic
  signature: [CharZero R] [P.IsCrystallographic]
  body: P.isAnisotropic_of_isValuedIn Int

中文:
实例 instIsAnisotropicOfIsCrystallographic
  签名: [特征零 R] [P.IsCrystallographic]
  定义体: P.isAnisotropic_of_isValuedIn Int

Depends on / 依赖: P.isAnisotropic_of_isValuedIn, isAnisotropic_of_isValuedIn
-/
instance instIsAnisotropicOfIsCrystallographic [CharZero R] [P.IsCrystallographic] :
    IsAnisotropic P :=
  P.isAnisotropic_of_isValuedIn Int

/--
Definition of `toInvariantForm` / `toInvariantForm` 的定义

English:
definition toInvariantForm
  signature: [P.IsAnisotropic]
  body: P.RootForm
  symm := P.rootForm_symmetric
  ne_zero := IsAnisotropic.rootForm_root_ne_zero
  isOrthogonal_reflection := P.rootForm_reflection_reflection_apply

中文:
定义 toInvariantForm
  签名: [P.是Anisotropic]
  定义体: P.RootForm
  symm := P.rootForm_symmetric
  ne_zero := IsAnisotropic.rootForm_root_ne_zero
  isOrthogonal_reflection := P.rootForm_reflection_reflection_apply
-/
@[simps] def toInvariantForm [P.IsAnisotropic] : P.InvariantForm where
  form := P.RootForm
  symm := P.rootForm_symmetric
  ne_zero := IsAnisotropic.rootForm_root_ne_zero
  isOrthogonal_reflection := P.rootForm_reflection_reflection_apply

/--
lemma `smul_coroot_eq_of_root_add_root_eq` / 引理 `smul_coroot_eq_of_root_add_root_eq`

English:
lemma smul_coroot_eq_of_root_add_root_eq
  statement: [P.IsAnisotropic] [IsDomain R] [IsTorsionFree R N]
  proof: (m * m) * P.pairing i j + (m * n) * (P.pairing i j * P.pairing j i) + (n * n) * P.pairing j i
    Q • P.coroot k = m • P.pairing i j • P.coroot i + n • P.pairing j i • P.coroot j := by
  let B := P.toInvariantForm
  let lsq (i) : R := B.form (P.root i) (P.root i)
  have hlsq (i : ι) : lsq i = P.Root

中文:
引理 smul_coroot_eq_of_root_add_root_eq
  结论: [P.是Anisotropic] [是整环 R] [是无挠 R N]
  证明: (m * m) * P.pairing i j + (m * n) * (P.pairing i j * P.pairing j i) + (n * n) * P.pairing j i
    Q • P.coroot k = m • P.pairing i j • P.coroot i + n • P.pairing j i • P.coroot j := by
  let B := P.toInvariantForm
  let lsq (i) : R := B.form (P.root i) (P.root i)
  have hlsq (i : ι) : lsq i = P.Root

Depends on / 依赖: B.form, P.RootForm, P.coroot, P.pairing, P.root, P.rootForm_self_smul_coroot, P.toInvariantForm, RootForm, coroot, map_smul, pairing, rootForm_self_smul_coroot, smul_assoc, smul_comm, toInvariantForm
-/
lemma smul_coroot_eq_of_root_add_root_eq [P.IsAnisotropic] [IsDomain R] [IsTorsionFree R N]
    {i j k : ι} {m n : R} (hk : m • P.root i + n • P.root j = P.root k) :
    letI Q :=
      (m * m) * P.pairing i j + (m * n) * (P.pairing i j * P.pairing j i) + (n * n) * P.pairing j i
    Q • P.coroot k = m • P.pairing i j • P.coroot i + n • P.pairing j i • P.coroot j := by
  let B := P.toInvariantForm
  let lsq (i) : R := B.form (P.root i) (P.root i)
  have hlsq (i : ι) : lsq i = P.RootForm (P.root i) (P.root i) := rfl
  have h₁ : lsq k • P.coroot k = (m • lsq i) • P.coroot i + (n • lsq j) • P.coroot j := by
    simp only [hlsq, smul_assoc, P.rootForm_self_smul_coroot, smul_comm _ 2]
    rw [← map_smul _ m]; rw [← map_smul _ n]; rw [← nsmul_add]; rw [← map_add]; rw [hk]
  have h₂ :
      lsq k = (m * m) * lsq i + (m * n) * (2 * B.form (P.root i) (P.root j)) + (n * n) * lsq j := by
    have aux : P.RootForm (P.root j) (P.root i) = B.form (P.root i) (P.root j) :=
      P.rootForm_symmetric.eq (P.root j) (P.root i)
    simp [hlsq, ← hk, aux, B]
    ring
  have h₃ : 2 * B.form (P.root i) (P.root j) = P.pairing i j * lsq j :=
    B.two_mul_apply_root_root i j
  have h₄ : P.pairing j i * lsq i = P.pairing i j * lsq j := B.pairing_mul_eq_pairing_mul_swap i j
  replace h₁ :
      (m * m * (P.pairing j i * lsq i)) • P.coroot k +
      (m * n * (P.pairing j i * P.pairing i j * lsq j)) • P.coroot k +
      (n * n * (P.pairing j i * lsq j)) • P.coroot k =
        (m * (P.pairing j i * lsq i)) • P.coroot i +
        (n * (P.pairing j i * lsq j)) • P.coroot j := by
    rw [h₂]; rw [h₃] at h₁
    replace h₁ := congr_arg (fun n => P.pairing j i • n) h₁
    simp only [add_smul, smul_add, ← mul_smul, smul_eq_mul] at h₁
    convert! h₁ using 1
    · module
    · ring_nf
  simp only [h₄] at h₁
  apply smul_right_injective _ (r := lsq j) (RootPairing.IsAnisotropic.rootForm_root_ne_zero j)
  simp only
  convert! h₁ using 1
  · module
  · module

section DomainAlg

variable (S : Type*) [CommRing S] [IsDomain R] [IsDomain S] [Algebra S R] [FaithfulSMul S R]
  [P.IsValuedIn S] [Module S M] [IsScalarTower S R M] [Module S N] [IsScalarTower S R N]

/--
lemma `finrank_range_polarization_eq_finrank_span_coroot` / 引理 `finrank_range_polarization_eq_finrank_span_coroot`

English:
lemma finrank_range_polarization_eq_finrank_span_coroot
  given: [P.IsAnisotropic]
  proof: by
  apply (Submodule.finrank_mono (P.range_polarizationIn_le_span_coroot S)).antisymm
  have : IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  have : Module.IsTorsionFree S N := .trans_faithfulSMul S R N
  have h_ne : ∏ i, (P.RootFormIn S (P.rootSpanMem S i) (P.rootSpanMem S i)) != 0 := by
 

中文:
引理 finrank_range_polarization_eq_finrank_span_coroot
  条件: [P.是Anisotropic]
  证明: by
  apply (Submodule.finrank_mono (P.range_polarizationIn_le_span_coroot S)).antisymm
  have : IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  have : Module.IsTorsionFree S N := .trans_faithfulSMul S R N
  have h_ne : ∏ i, (P.RootFormIn S (P.rootSpanMem S i) (P.rootSpanMem S i)) != 0 := by
 

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_eq_zero_iff, Finset, Finset.prod_ne_zero_iff.mpr, IsAnisotropic, IsAnisotropic.rootForm_root_ne_zero, IsReflexive, IsTorsionFree, LinearMap, LinearMap.f, Module, Module.IsTorsionFree, P.RootFormIn, P.flip.toLinearMap, P.range_polarizationIn_le_span_coroot, P.rootSpanMem, RootFormIn, Submodule, Submodule.finrank_mono, algebraMap_eq_zero_iff
-/
lemma finrank_range_polarization_eq_finrank_span_coroot [P.IsAnisotropic] :
    finrank S (LinearMap.range (P.PolarizationIn S)) = finrank S (P.corootSpan S) := by
  apply (Submodule.finrank_mono (P.range_polarizationIn_le_span_coroot S)).antisymm
  have : IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  have : Module.IsTorsionFree S N := .trans_faithfulSMul S R N
  have h_ne : ∏ i, (P.RootFormIn S (P.rootSpanMem S i) (P.rootSpanMem S i)) != 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i _ h => ?_
    have := (FaithfulSMul.algebraMap_eq_zero_iff S R).mpr h
    rw [algebraMap_rootFormIn] at this
    apply IsAnisotropic.rootForm_root_ne_zero i this
  refine LinearMap.finrank_le_of_isSMulRegular (P.corootSpan S)
    (LinearMap.range (M₂ := N) (P.PolarizationIn S))
    (smul_right_injective N h_ne) ?_
  intro _ hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).mp hx
  rw [← hc]; rw [Finset.smul_sum]
  simp_rw [smul_smul, mul_comm, ← smul_smul]
  exact Submodule.sum_smul_mem (LinearMap.range (P.PolarizationIn S)) c
    fun j _ => prod_rootFormIn_smul_coroot_mem_range_PolarizationIn P S j

/--
lemma `finrank_corootSpan_le` / 引理 `finrank_corootSpan_le`

English:
lemma finrank_corootSpan_le
  given: [P.IsAnisotropic]
  proof: by
  rw [← finrank_range_polarization_eq_finrank_span_coroot]
  exact LinearMap.finrank_range_le (P.PolarizationIn S)

中文:
引理 finrank_corootSpan_le
  条件: [P.是Anisotropic]
  证明: by
  rw [← finrank_range_polarization_eq_finrank_span_coroot]
  exact LinearMap.finrank_range_le (P.PolarizationIn S)
-/
private lemma finrank_corootSpan_le [P.IsAnisotropic] :
    finrank S (P.corootSpan S) <= finrank S (P.rootSpan S) := by
  rw [← finrank_range_polarization_eq_finrank_span_coroot]
  exact LinearMap.finrank_range_le (P.PolarizationIn S)

/--
lemma `finrank_corootSpan_eq` / 引理 `finrank_corootSpan_eq`

English:
lemma finrank_corootSpan_eq
  given: [P.IsAnisotropic]
  proof: le_antisymm (P.finrank_corootSpan_le S) (P.flip.finrank_corootSpan_le S)

中文:
引理 finrank_corootSpan_eq
  条件: [P.是Anisotropic]
  证明: le_antisymm (P.finrank_corootSpan_le S) (P.flip.finrank_corootSpan_le S)

Depends on / 依赖: P.finrank_corootSpan_le, P.flip.finrank_corootSpan_le, finrank_corootSpan_le, le_antisymm
-/
lemma finrank_corootSpan_eq [P.IsAnisotropic] :
    finrank S (P.corootSpan S) = finrank S (P.rootSpan S) :=
  le_antisymm (P.finrank_corootSpan_le S) (P.flip.finrank_corootSpan_le S)

/--
lemma `polarizationIn_Injective` / 引理 `polarizationIn_Injective`

English:
lemma polarizationIn_Injective
  given: [P.IsAnisotropic]
  proof: by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : Module.IsTorsionFree S M := .trans_faithfulSMul S R M
  rw [← LinearMap.ker_eq_bot]; rw [← top_disjoint]
  refine Submodule.disjoint_ker_of_finrank_le (L := ⊤) (P.PolarizationIn S) ?_
  rw [finrank_top]; rw [← finrank_corootSpan_eq

中文:
引理 polarizationIn_Injective
  条件: [P.是Anisotropic]
  证明: by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : Module.IsTorsionFree S M := .trans_faithfulSMul S R M
  rw [← LinearMap.ker_eq_bot]; rw [← top_disjoint]
  refine Submodule.disjoint_ker_of_finrank_le (L := ⊤) (P.PolarizationIn S) ?_
  rw [finrank_top]; rw [← finrank_corootSpan_eq

Depends on / 依赖: IsReflexive, IsTorsionFree, LinearMap, LinearMap.ker_eq_bot, LinearMap.range_eq_map, Module, Module.IsTorsionFree, P.PolarizationIn, P.toLinearMap, PolarizationIn, Submodule, Submodule.disjoint_ker_of_finrank_le, Submodule.finrank_mono, disjoint_ker_of_finrank_le, finrank_corootSpan_eq, finrank_mono, finrank_range_polarization_eq_finrank_span_coroot, finrank_top, ker_eq_bot, le_of_eq
-/
lemma polarizationIn_Injective [P.IsAnisotropic] :
    Function.Injective (P.PolarizationIn S) := by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : Module.IsTorsionFree S M := .trans_faithfulSMul S R M
  rw [← LinearMap.ker_eq_bot]; rw [← top_disjoint]
  refine Submodule.disjoint_ker_of_finrank_le (L := ⊤) (P.PolarizationIn S) ?_
  rw [finrank_top]; rw [← finrank_corootSpan_eq]; rw [← finrank_range_polarization_eq_finrank_span_coroot]
exact Submodule.finrank_mono le_of_eq LinearMap.range_eq_map (P.PolarizationIn S)

/--
lemma `exists_coroot_ne` / 引理 `exists_coroot_ne`

English:
lemma exists_coroot_ne
  statement: [P.IsAnisotropic]
  proof: by
  have hI := P.polarizationIn_Injective S
  have h := (map_ne_zero_iff (P.PolarizationIn S) hI).mpr hx
  rw [PolarizationIn_apply] at h
  contrapose! h
  exact Fintype.sum_eq_zero (fun a => (P.coroot'In S a) x • P.coroot a) fun i => by simp [h i]

中文:
引理 存在_coroot_ne
  结论: [P.是Anisotropic]
  证明: by
  have hI := P.polarizationIn_Injective S
  have h := (map_ne_zero_iff (P.PolarizationIn S) hI).mpr hx
  rw [PolarizationIn_apply] at h
  contrapose! h
  exact Fintype.sum_eq_zero (fun a => (P.coroot'In S a) x • P.coroot a) fun i => by simp [h i]

Depends on / 依赖: Fintype, Fintype.sum_eq_zero, P.PolarizationIn, P.coroot, P.polarizationIn_Injective, PolarizationIn, PolarizationIn_apply, contrapose, coroot, map_ne_zero_iff, polarizationIn_Injective, sum_eq_zero
-/
lemma exists_coroot_ne [P.IsAnisotropic]
    {x : P.rootSpan S} (hx : x != 0) :
    exists i, P.coroot'In S i x != 0 := by
  have hI := P.polarizationIn_Injective S
  have h := (map_ne_zero_iff (P.PolarizationIn S) hI).mpr hx
  rw [PolarizationIn_apply] at h
  contrapose! h
  exact Fintype.sum_eq_zero (fun a => (P.coroot'In S a) x • P.coroot a) fun i => by simp [h i]

end DomainAlg

section LinearOrderedCommRingAlg

variable (S : Type*) [CommRing S] [LinearOrder S] [IsStrictOrderedRing S] [IsDomain R] [Algebra S R]
  [FaithfulSMul S R] [P.IsValuedIn S] [Module S M] [IsScalarTower S R M] [Module S N]
  [IsScalarTower S R N]

/--
theorem `posRootForm_posForm_pos_of_ne_zero` / 定理 `posRootForm_posForm_pos_of_ne_zero`

English:
theorem posRootForm_posForm_pos_of_ne_zero
  given: {x : P.rootSpan S} (hx : x != 0)
  proof: by
  rw [posRootForm_posForm_apply_apply]
  have := P.isAnisotropic_of_isValuedIn S
  have : exists i in Finset.univ, 0 < (P.coroot'In S i) x * (P.coroot'In S i) x := by
    obtain ⟨i, hi⟩ := P.exists_coroot_ne S hx
    use i
    exact ⟨Finset.mem_univ i, mul_self_pos.mpr hi⟩
  exact Finset.sum_pos'

中文:
定理 posRootForm_posForm_pos_of_ne_zero
  条件: {x : P.rootSpan S} (hx : x != 0)
  证明: by
  rw [posRootForm_posForm_apply_apply]
  have := P.isAnisotropic_of_isValuedIn S
  have : exists i in Finset.univ, 0 < (P.coroot'In S i) x * (P.coroot'In S i) x := by
    obtain ⟨i, hi⟩ := P.exists_coroot_ne S hx
    use i
    exact ⟨Finset.mem_univ i, mul_self_pos.mpr hi⟩
  exact Finset.sum_pos'

Depends on / 依赖: Finset, Finset.mem_univ, Finset.sum_pos, Finset.univ, P.coroot, P.exists_coroot_ne, P.isAnisotropic_of_isValuedIn, coroot, exists_coroot_ne, isAnisotropic_of_isValuedIn, mem_univ, mul_self_nonneg, mul_self_pos, mul_self_pos.mpr, posRootForm_posForm_apply_apply, sum_pos
-/
theorem posRootForm_posForm_pos_of_ne_zero {x : P.rootSpan S} (hx : x != 0) :
    0 < (P.posRootForm S).posForm x x := by
  rw [posRootForm_posForm_apply_apply]
  have := P.isAnisotropic_of_isValuedIn S
  have : exists i in Finset.univ, 0 < (P.coroot'In S i) x * (P.coroot'In S i) x := by
    obtain ⟨i, hi⟩ := P.exists_coroot_ne S hx
    use i
    exact ⟨Finset.mem_univ i, mul_self_pos.mpr hi⟩
  exact Finset.sum_pos' (fun i a => mul_self_nonneg ((P.coroot'In S i) x)) this

/--
lemma `posRootForm_rootFormIn_posDef` / 引理 `posRootForm_rootFormIn_posDef`

English:
lemma posRootForm_rootFormIn_posDef
  statement: (P.RootFormIn S).toQuadraticMap.PosDef
  proof: by
  intro x hx
  simpa using P.posRootForm_posForm_pos_of_ne_zero S hx

中文:
引理 posRootForm_rootFormIn_posDef
  结论: (P.RootFormIn S).toQuadraticMap.PosDef
  证明: by
  intro x hx
  simpa using P.posRootForm_posForm_pos_of_ne_zero S hx

Depends on / 依赖: P.posRootForm_posForm_pos_of_ne_zero, posRootForm_posForm_pos_of_ne_zero
-/
lemma posRootForm_rootFormIn_posDef : (P.RootFormIn S).toQuadraticMap.PosDef := by
  intro x hx
  simpa using P.posRootForm_posForm_pos_of_ne_zero S hx

/--
lemma `posRootForm_posForm_anisotropic` / 引理 `posRootForm_posForm_anisotropic`

English:
lemma posRootForm_posForm_anisotropic
  proof: fun _ hx => Classical.byContradiction fun h =>
    (ne_of_lt (posRootForm_posForm_pos_of_ne_zero P S h)).symm hx

中文:
引理 posRootForm_posForm_anisotropic
  证明: fun _ hx => Classical.byContradiction fun h =>
    (ne_of_lt (posRootForm_posForm_pos_of_ne_zero P S h)).symm hx

Depends on / 依赖: Classical, Classical.byContradiction, byContradiction, ne_of_lt, posRootForm_posForm_pos_of_ne_zero
-/
lemma posRootForm_posForm_anisotropic :
    (P.posRootForm S).posForm.toQuadraticMap.Anisotropic :=
  fun _ hx => Classical.byContradiction fun h =>
    (ne_of_lt (posRootForm_posForm_pos_of_ne_zero P S h)).symm hx

/--
lemma `posRootForm_posForm_nondegenerate` / 引理 `posRootForm_posForm_nondegenerate`

English:
lemma posRootForm_posForm_nondegenerate
  proof: by
  constructor <;>
  · intro x
    contrapose!
    exact fun hx => ⟨x, (posRootForm_posForm_pos_of_ne_zero P S hx).ne'⟩

中文:
引理 posRootForm_posForm_nondegenerate
  证明: by
  constructor <;>
  · intro x
    contrapose!
    exact fun hx => ⟨x, (posRootForm_posForm_pos_of_ne_zero P S hx).ne'⟩

Depends on / 依赖: contrapose, posRootForm_posForm_pos_of_ne_zero
-/
lemma posRootForm_posForm_nondegenerate :
    (P.posRootForm S).posForm.Nondegenerate := by
  constructor <;>
  · intro x
    contrapose!
    exact fun hx => ⟨x, (posRootForm_posForm_pos_of_ne_zero P S hx).ne'⟩

end LinearOrderedCommRingAlg

end CommRing

section IsDomain

variable [CommRing R] [IsDomain R] [Module R M] [Module R N] (P : RootPairing ι R M N)
  [P.IsAnisotropic]

@[simp]
/--
lemma `finrank_rootSpan_map_polarization_eq_finrank_corootSpan` / 引理 `finrank_rootSpan_map_polarization_eq_finrank_corootSpan`

English:
lemma finrank_rootSpan_map_polarization_eq_finrank_corootSpan
  proof: by
  rw [← P.finrank_range_polarization_eq_finrank_span_coroot R]; rw [range_polarizationIn]

中文:
引理 finrank_rootSpan_map_polarization_eq_finrank_corootSpan
  证明: by
  rw [← P.finrank_range_polarization_eq_finrank_span_coroot R]; rw [range_polarizationIn]

Depends on / 依赖: P.finrank_range_polarization_eq_finrank_span_coroot, finrank_range_polarization_eq_finrank_span_coroot, range_polarizationIn
-/
lemma finrank_rootSpan_map_polarization_eq_finrank_corootSpan :
    finrank R ((P.rootSpan R).map P.Polarization) = finrank R (P.corootSpan R) := by
  rw [← P.finrank_range_polarization_eq_finrank_span_coroot R]; rw [range_polarizationIn]

/--
lemma `finrank_corootSpan_le'` / 引理 `finrank_corootSpan_le'`

English:
lemma finrank_corootSpan_le'
  proof: by
  rw [← finrank_rootSpan_map_polarization_eq_finrank_corootSpan]
  exact Submodule.finrank_map_le P.Polarization (P.rootSpan R)

中文:
引理 finrank_corootSpan_le'
  证明: by
  rw [← finrank_rootSpan_map_polarization_eq_finrank_corootSpan]
  exact Submodule.finrank_map_le P.Polarization (P.rootSpan R)
-/
private lemma finrank_corootSpan_le' :
    finrank R (P.corootSpan R) <= finrank R (P.rootSpan R) := by
  rw [← finrank_rootSpan_map_polarization_eq_finrank_corootSpan]
  exact Submodule.finrank_map_le P.Polarization (P.rootSpan R)

/--
lemma `finrank_corootSpan_eq'` / 引理 `finrank_corootSpan_eq'`

English:
lemma finrank_corootSpan_eq'
  proof: le_antisymm P.finrank_corootSpan_le' P.flip.finrank_corootSpan_le'

中文:
引理 finrank_corootSpan_eq'
  证明: le_antisymm P.finrank_corootSpan_le' P.flip.finrank_corootSpan_le'

Depends on / 依赖: P.finrank_corootSpan_le, P.flip.finrank_corootSpan_le, finrank_corootSpan_le, le_antisymm, measure_lt_top
-/
lemma finrank_corootSpan_eq' :
    finrank R (P.corootSpan R) = finrank R (P.rootSpan R) :=
  le_antisymm P.finrank_corootSpan_le' P.flip.finrank_corootSpan_le'

/--
lemma `disjoint_rootSpan_ker_rootForm` / 引理 `disjoint_rootSpan_ker_rootForm`

English:
lemma disjoint_rootSpan_ker_rootForm
  proof: by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  rw [← P.ker_polarization_eq_ker_rootForm]
  refine Submodule.disjoint_ker_of_finrank_le (L := P.rootSpan R) P.Polarization ?_
  rw [P.finrank_rootSpan_map_polarization_eq_finrank_corootSpan]; rw [P.finrank_corootSpan_eq']

中文:
引理 disjoint_rootSpan_ker_rootForm
  证明: by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  rw [← P.ker_polarization_eq_ker_rootForm]
  refine Submodule.disjoint_ker_of_finrank_le (L := P.rootSpan R) P.Polarization ?_
  rw [P.finrank_rootSpan_map_polarization_eq_finrank_corootSpan]; rw [P.finrank_corootSpan_eq']

Depends on / 依赖: IsReflexive, P.Polarization, P.finrank_corootSpan_eq, P.finrank_rootSpan_map_polarization_eq_finrank_corootSpan, P.ker_polarization_eq_ker_rootForm, P.rootSpan, P.toLinearMap, Polarization, Submodule, Submodule.disjoint_ker_of_finrank_le, disjoint_ker_of_finrank_le, finrank_corootSpan_eq, finrank_rootSpan_map_polarization_eq_finrank_corootSpan, ker_polarization_eq_ker_rootForm, of_isPerfPair, rootSpan, toLinearMap
-/
lemma disjoint_rootSpan_ker_rootForm :
    Disjoint (P.rootSpan R) (LinearMap.ker P.RootForm) := by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  rw [← P.ker_polarization_eq_ker_rootForm]
  refine Submodule.disjoint_ker_of_finrank_le (L := P.rootSpan R) P.Polarization ?_
  rw [P.finrank_rootSpan_map_polarization_eq_finrank_corootSpan]; rw [P.finrank_corootSpan_eq']

/--
lemma `disjoint_corootSpan_ker_corootForm` / 引理 `disjoint_corootSpan_ker_corootForm`

English:
lemma disjoint_corootSpan_ker_corootForm
  proof: P.flip.disjoint_rootSpan_ker_rootForm

中文:
引理 disjoint_corootSpan_ker_corootForm
  证明: P.flip.disjoint_rootSpan_ker_rootForm

Depends on / 依赖: P.flip.disjoint_rootSpan_ker_rootForm, disjoint_rootSpan_ker_rootForm
-/
lemma disjoint_corootSpan_ker_corootForm :
    Disjoint (P.corootSpan R) (LinearMap.ker P.CorootForm) :=
  P.flip.disjoint_rootSpan_ker_rootForm

/--
lemma `rootForm_nondegenerate` / 引理 `rootForm_nondegenerate`

English:
lemma rootForm_nondegenerate
  given: [P.IsRootSystem]
  proof: by
  simpa [(rootForm_symmetric P).isRefl.nondegenerate_iff_separatingLeft,
    LinearMap.separatingLeft_iff_ker_eq_bot] using P.disjoint_rootSpan_ker_rootForm

中文:
引理 rootForm_nondegenerate
  条件: [P.是RootSystem]
  证明: by
  simpa [(rootForm_symmetric P).isRefl.nondegenerate_iff_separatingLeft,
    LinearMap.separatingLeft_iff_ker_eq_bot] using P.disjoint_rootSpan_ker_rootForm

Depends on / 依赖: LinearMap, LinearMap.separatingLeft_iff_ker_eq_bot, P.disjoint_rootSpan_ker_rootForm, disjoint_rootSpan_ker_rootForm, isRefl, isRefl.nondegenerate_iff_separatingLeft, nondegenerate_iff_separatingLeft, rootForm_symmetric, separatingLeft_iff_ker_eq_bot
-/
lemma rootForm_nondegenerate [P.IsRootSystem] :
    P.RootForm.Nondegenerate := by
  simpa [(rootForm_symmetric P).isRefl.nondegenerate_iff_separatingLeft,
    LinearMap.separatingLeft_iff_ker_eq_bot] using P.disjoint_rootSpan_ker_rootForm

end IsDomain

section Field

variable [Field R] [Module R M] [Module R N] (P : RootPairing ι R M N) [P.IsAnisotropic]

/--
lemma `isCompl_rootSpan_ker_rootForm` / 引理 `isCompl_rootSpan_ker_rootForm`

English:
lemma isCompl_rootSpan_ker_rootForm
  proof: by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  refine (Submodule.isCompl_iff_disjoint _ _ ?_).mpr P.disjoint_rootSpan_ker_rootForm
  have aux : finrank R M =
      finrank R (P.rootSpan R) + finrank R (P.corootSpan R).dualA

中文:
引理 isCompl_rootSpan_ker_rootForm
  证明: by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  refine (Submodule.isCompl_iff_disjoint _ _ ?_).mpr P.disjoint_rootSpan_ker_rootForm
  have aux : finrank R M =
      finrank R (P.rootSpan R) + finrank R (P.corootSpan R).dualA

Depends on / 依赖: IsReflexive, P.corootSpan, P.disjoint_rootSpan_ker_rootForm, P.finrank_corootSpan_eq, P.flip.toLinearMap, P.rootSpan, P.toLinearMap, P.toPerfPair.finrank_eq, Submodule, Submodule.isCompl_iff_disjoint, Subspace, Subspace.dual_finrank_eq, Subspace.finrank_add_finrank_dualAnnihilator_eq, add_le_add_iff_left, corootSpan, disjoint_rootSpan_ker_rootForm, dualAnnihilator, dual_finrank_eq, finrank, finrank_add_finrank_dualAnnihilator_eq
-/
lemma isCompl_rootSpan_ker_rootForm :
    IsCompl (P.rootSpan R) (LinearMap.ker P.RootForm) := by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  refine (Submodule.isCompl_iff_disjoint _ _ ?_).mpr P.disjoint_rootSpan_ker_rootForm
  have aux : finrank R M =
      finrank R (P.rootSpan R) + finrank R (P.corootSpan R).dualAnnihilator := by
    rw [P.toPerfPair.finrank_eq]; rw [← P.finrank_corootSpan_eq']; rw [Subspace.finrank_add_finrank_dualAnnihilator_eq (P.corootSpan R)]; rw [Subspace.dual_finrank_eq]
  rw [aux]; rw [add_le_add_iff_left]
  convert! Submodule.finrank_mono P.corootSpan_dualAnnihilator_le_ker_rootForm
  exact (LinearEquiv.finrank_map_eq _ _).symm

/--
lemma `isCompl_corootSpan_ker_corootForm` / 引理 `isCompl_corootSpan_ker_corootForm`

English:
lemma isCompl_corootSpan_ker_corootForm
  proof: P.flip.isCompl_rootSpan_ker_rootForm

中文:
引理 isCompl_corootSpan_ker_corootForm
  证明: P.flip.isCompl_rootSpan_ker_rootForm

Depends on / 依赖: P.flip.isCompl_rootSpan_ker_rootForm, isCompl_rootSpan_ker_rootForm
-/
lemma isCompl_corootSpan_ker_corootForm :
    IsCompl (P.corootSpan R) (LinearMap.ker P.CorootForm) :=
  P.flip.isCompl_rootSpan_ker_rootForm

/--
lemma `ker_rootForm_eq_dualAnnihilator` / 引理 `ker_rootForm_eq_dualAnnihilator`

English:
lemma ker_rootForm_eq_dualAnnihilator
  proof: by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  suffices finrank R (LinearMap.ker P.RootForm) = finrank R (P.corootSpan R).dualAnnihilator by
    refine (Submodule.eq_of_le_of_finrank_eq P.corootSpan_dualAnnihilator_le_ker_r

中文:
引理 ker_rootForm_eq_dualAnnihilator
  证明: by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  suffices finrank R (LinearMap.ker P.RootForm) = finrank R (P.corootSpan R).dualAnnihilator by
    refine (Submodule.eq_of_le_of_finrank_eq P.corootSpan_dualAnnihilator_le_ker_r

Depends on / 依赖: IsReflexive, LinearEquiv, LinearEquiv.finrank_map_eq, LinearMap, LinearMap.ker, P.RootForm, P.corootSpan, P.corootSpan_dualAnnihilator_le_ker_rootForm, P.flip.toLinearMap, P.isCompl_rootSpan_ker_, P.toLinearMap, RootForm, Submodule, Submodule.eq_of_le_of_finrank_eq, Submodule.finrank_add_eq_of_isCompl, Subspace, Subspace.finrank_add_finrank_dualAnnihilator_eq, corootSpan, corootSpan_dualAnnihilator_le_ker_rootForm, dualAnnihilator
-/
lemma ker_rootForm_eq_dualAnnihilator :
    P.RootForm.ker =
      (P.corootSpan R).dualAnnihilator.map (P.toPerfPair.symm : Dual R N ->ₗ[R] M) := by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  suffices finrank R (LinearMap.ker P.RootForm) = finrank R (P.corootSpan R).dualAnnihilator by
    refine (Submodule.eq_of_le_of_finrank_eq P.corootSpan_dualAnnihilator_le_ker_rootForm ?_).symm
    rw [this]
    apply LinearEquiv.finrank_map_eq
  have aux0 := Subspace.finrank_add_finrank_dualAnnihilator_eq (P.corootSpan R)
  have aux1 := Submodule.finrank_add_eq_of_isCompl P.isCompl_rootSpan_ker_rootForm
  rw [← P.finrank_corootSpan_eq']; rw [P.toPerfPair.finrank_eq]; rw [Subspace.dual_finrank_eq] at aux1
  lia

/--
lemma `ker_corootForm_eq_dualAnnihilator` / 引理 `ker_corootForm_eq_dualAnnihilator`

English:
lemma ker_corootForm_eq_dualAnnihilator
  proof: P.flip.ker_rootForm_eq_dualAnnihilator

中文:
引理 ker_corootForm_eq_dualAnnihilator
  证明: P.flip.ker_rootForm_eq_dualAnnihilator

Depends on / 依赖: P.flip.ker_rootForm_eq_dualAnnihilator, ker_rootForm_eq_dualAnnihilator
-/
lemma ker_corootForm_eq_dualAnnihilator :
    P.CorootForm.ker =
      (P.rootSpan R).dualAnnihilator.map (P.flip.toPerfPair.symm : Dual R M ->ₗ[R] N) :=
  P.flip.ker_rootForm_eq_dualAnnihilator

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.IsBalanced
  body: { isCompl_left := by
      simpa only [ker_rootForm_eq_dualAnnihilator] using! P.isCompl_rootSpan_ker_rootForm
    isCompl_right := by
      simpa only [ker_corootForm_eq_dualAnnihilator] using! P.isCompl_corootSpan_ker_corootForm }

中文:
实例 :
  签名: P.是Balanced
  定义体: { isCompl_left := by
      simpa only [ker_rootForm_eq_dualAnnihilator] using! P.isCompl_rootSpan_ker_rootForm
    isCompl_right := by
      simpa only [ker_corootForm_eq_dualAnnihilator] using! P.isCompl_corootSpan_ker_corootForm }

Depends on / 依赖: IsFiniteMeasure, IsFiniteMeasure.toIsLocallyFiniteMeasure, P.isCompl_corootSpan_ker_corootForm, P.isCompl_rootSpan_ker_rootForm, TopologicalSpace, isCompl_corootSpan_ker_corootForm, isCompl_left, isCompl_right, isCompl_rootSpan_ker_rootForm, ker_corootForm_eq_dualAnnihilator, ker_rootForm_eq_dualAnnihilator, toIsLocallyFiniteMeasure
-/
instance : P.IsBalanced where
    isPerfectCompl :=
  { isCompl_left := by
      simpa only [ker_rootForm_eq_dualAnnihilator] using! P.isCompl_rootSpan_ker_rootForm
    isCompl_right := by
      simpa only [ker_corootForm_eq_dualAnnihilator] using! P.isCompl_corootSpan_ker_corootForm }

/--
lemma `rootForm_restrict_nondegenerate_of_isAnisotropic` / 引理 `rootForm_restrict_nondegenerate_of_isAnisotropic`

English:
lemma rootForm_restrict_nondegenerate_of_isAnisotropic
  proof: P.rootForm_symmetric.nondegenerate_restrict_of_isCompl_ker P.isCompl_rootSpan_ker_rootForm

@[simp]

中文:
引理 rootForm_restrict_nondegenerate_of_isAnisotropic
  证明: P.rootForm_symmetric.nondegenerate_restrict_of_isCompl_ker P.isCompl_rootSpan_ker_rootForm

@[simp]

Depends on / 依赖: P.isCompl_rootSpan_ker_rootForm, P.rootForm_symmetric.nondegenerate_restrict_of_isCompl_ker, isCompl_rootSpan_ker_rootForm, nondegenerate_restrict_of_isCompl_ker, rootForm_symmetric
-/
lemma rootForm_restrict_nondegenerate_of_isAnisotropic :
    LinearMap.Nondegenerate (P.RootForm.restrict (P.rootSpan R)) :=
  P.rootForm_symmetric.nondegenerate_restrict_of_isCompl_ker P.isCompl_rootSpan_ker_rootForm

@[simp]
/--
lemma `orthogonal_rootSpan_eq` / 引理 `orthogonal_rootSpan_eq`

English:
lemma orthogonal_rootSpan_eq
  proof: by
  rw [← LinearMap.BilinForm.orthogonal_top_eq_ker P.rootForm_symmetric.isRefl]
  refine le_antisymm ?_ (by intro; simp_all)
  rintro x hx y -
  simp only [LinearMap.BilinForm.mem_orthogonal_iff] at hx ⊢
  obtain ⟨u, hu, v, hv, rfl⟩ : existsᵉ (u in P.rootSpan R) (v in LinearMap.ker P.RootForm), u 

中文:
引理 orthogonal_rootSpan_eq
  证明: by
  rw [← LinearMap.BilinForm.orthogonal_top_eq_ker P.rootForm_symmetric.isRefl]
  refine le_antisymm ?_ (by intro; simp_all)
  rintro x hx y -
  simp only [LinearMap.BilinForm.mem_orthogonal_iff] at hx ⊢
  obtain ⟨u, hu, v, hv, rfl⟩ : existsᵉ (u in P.rootSpan R) (v in LinearMap.ker P.RootForm), u 

Depends on / 依赖: BilinForm, LinearMap, LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.BilinForm.orthogonal_top_eq_ker, LinearMap.ker, LinearMap.mem_ker, P.RootForm, P.isCompl_rootSpan_ker_rootForm.sup_eq_top, P.rootForm_symmetric.isRefl, P.rootSpan, RootForm, Submodule, Submodule.mem_sup, Submodule.mem_top, isCompl_rootSpan_ker_rootForm, isRefl, le_antisymm, mem_ker, mem_orthogonal_iff, mem_sup
-/
lemma orthogonal_rootSpan_eq :
    P.RootForm.orthogonal (P.rootSpan R) = LinearMap.ker P.RootForm := by
  rw [← LinearMap.BilinForm.orthogonal_top_eq_ker P.rootForm_symmetric.isRefl]
  refine le_antisymm ?_ (by intro; simp_all)
  rintro x hx y -
  simp only [LinearMap.BilinForm.mem_orthogonal_iff] at hx ⊢
  obtain ⟨u, hu, v, hv, rfl⟩ : existsᵉ (u in P.rootSpan R) (v in LinearMap.ker P.RootForm), u + v = y := by
    rw [← Submodule.mem_sup]; rw [P.isCompl_rootSpan_ker_rootForm.sup_eq_top]; exact Submodule.mem_top
  simp only [LinearMap.mem_ker] at hv
  simp [hx _ hu, hv]

@[simp]
/--
lemma `orthogonal_corootSpan_eq` / 引理 `orthogonal_corootSpan_eq`

English:
lemma orthogonal_corootSpan_eq
  proof: P.flip.orthogonal_rootSpan_eq

中文:
引理 orthogonal_corootSpan_eq
  证明: P.flip.orthogonal_rootSpan_eq

Depends on / 依赖: P.flip.orthogonal_rootSpan_eq, orthogonal_rootSpan_eq
-/
lemma orthogonal_corootSpan_eq :
    P.CorootForm.orthogonal (P.corootSpan R) = LinearMap.ker P.CorootForm :=
  P.flip.orthogonal_rootSpan_eq

/--
lemma `rootSpan_eq_top_iff` / 引理 `rootSpan_eq_top_iff`

English:
lemma rootSpan_eq_top_iff
  proof: by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> apply Submodule.eq_top_of_finrank_eq
  · rw [P.finrank_corootSpan_eq', h, finrank_top, P.toPerfPair.finrank_eq, Subspace.dual_finrank_eq]


中文:
引理 rootSpan_eq_top_iff
  证明: by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> apply Submodule.eq_top_of_finrank_eq
  · rw [P.finrank_corootSpan_eq', h, finrank_top, P.toPerfPair.finrank_eq, Subspace.dual_finrank_eq]


Depends on / 依赖: IsReflexive, P.finrank_corootSpan_eq, P.flip.toLinearMap, P.toLinearMap, P.toPerfPair.finrank_eq, Submodule, Submodule.eq_top_of_finrank_eq, Subspace, Subspace.dual_finrank_eq, dual_finrank_eq, eq_top_of_finrank_eq, finrank_corootSpan_eq, finrank_eq, finrank_top, of_isPerfPair, toLinearMap, toPerfPair
-/
lemma rootSpan_eq_top_iff :
    P.rootSpan R = ⊤ ↔ P.corootSpan R = ⊤ := by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> apply Submodule.eq_top_of_finrank_eq
  · rw [P.finrank_corootSpan_eq', h, finrank_top, P.toPerfPair.finrank_eq, Subspace.dual_finrank_eq]
  · rw [← P.finrank_corootSpan_eq', h, finrank_top, P.toPerfPair.finrank_eq,
      Subspace.dual_finrank_eq]

section IsRootSystem

variable [P.IsRootSystem]

/--
Definition of `PolarizationEquiv` / `PolarizationEquiv` 的定义

English:
definition PolarizationEquiv
  signature: : M ≃ₗ[R] N
  body: have : IsReflexive R M := Module.IsReflexive.of_isPerfPair P.toLinearMap
  (P.toInvariantForm.form.toDual P.rootForm_nondegenerate).trans P.flip.toPerfPair.symm

@[simp]

中文:
定义 PolarizationEquiv
  签名: : M ≃ₗ[R] N
  定义体: have : IsReflexive R M := Module.IsReflexive.of_isPerfPair P.toLinearMap
  (P.toInvariantForm.form.toDual P.rootForm_nondegenerate).trans P.flip.toPerfPair.symm

@[simp]

Depends on / 依赖: IsReflexive, Module, Module.IsReflexive.of_isPerfPair, P.flip.toPerfPair.symm, P.rootForm_nondegenerate, P.toInvariantForm.form.toDual, P.toLinearMap, of_isPerfPair, rootForm_nondegenerate, toDual, toInvariantForm, toLinearMap, toPerfPair
-/
def PolarizationEquiv : M ≃ₗ[R] N :=
  have : IsReflexive R M := Module.IsReflexive.of_isPerfPair P.toLinearMap
  (P.toInvariantForm.form.toDual P.rootForm_nondegenerate).trans P.flip.toPerfPair.symm

@[simp]
/--
lemma `polarizationEquiv_toLinearMap` / 引理 `polarizationEquiv_toLinearMap`

English:
lemma polarizationEquiv_toLinearMap
  proof: by
  simp only [PolarizationEquiv, LinearMap.BilinForm.toDual, RootPairing.toInvariantForm_form,
    ← P.flip_comp_polarization_eq_rootForm, RootPairing.flip_toLinearMap]
  ext m
  let e := P.flip.toPerfPair
  change e.symm (e _) = _
  simp

中文:
引理 polarizationEquiv_toLinearMap
  证明: by
  simp only [PolarizationEquiv, LinearMap.BilinForm.toDual, RootPairing.toInvariantForm_form,
    ← P.flip_comp_polarization_eq_rootForm, RootPairing.flip_toLinearMap]
  ext m
  let e := P.flip.toPerfPair
  change e.symm (e _) = _
  simp

Depends on / 依赖: BilinForm, LinearMap, LinearMap.BilinForm.toDual, P.flip.toPerfPair, P.flip_comp_polarization_eq_rootForm, PolarizationEquiv, RootPairing, RootPairing.flip_toLinearMap, RootPairing.toInvariantForm_form, e.symm, flip_comp_polarization_eq_rootForm, flip_toLinearMap, toDual, toInvariantForm_form, toPerfPair
-/
lemma polarizationEquiv_toLinearMap :
    P.PolarizationEquiv.toLinearMap = P.Polarization := by
  simp only [PolarizationEquiv, LinearMap.BilinForm.toDual, RootPairing.toInvariantForm_form,
    ← P.flip_comp_polarization_eq_rootForm, RootPairing.flip_toLinearMap]
  ext m
  let e := P.flip.toPerfPair
  change e.symm (e _) = _
  simp

-- Not `simp` to avoid losing the information that we're applying an `Equiv`.
/--
lemma `polarizationEquiv_apply` / 引理 `polarizationEquiv_apply`

English:
lemma polarizationEquiv_apply
  given: (m : M)
  proof: congr($P.polarizationEquiv_toLinearMap m)

中文:
引理 polarizationEquiv_apply
  条件: (m : M)
  证明: congr($P.polarizationEquiv_toLinearMap m)

Depends on / 依赖: P.polarizationEquiv_toLinearMap, polarizationEquiv_toLinearMap
-/
lemma polarizationEquiv_apply (m : M) :
    P.PolarizationEquiv m = P.Polarization m :=
  congr($P.polarizationEquiv_toLinearMap m)

/--
lemma `coroot_eq_polarizationEquiv_apply_root` / 引理 `coroot_eq_polarizationEquiv_apply_root`

English:
lemma coroot_eq_polarizationEquiv_apply_root
  given: (i : ι)
  proof: by
  have h₀ := IsAnisotropic.rootForm_root_ne_zero (P := P) i
  rw [polarizationEquiv_apply]; rw [← (smul_right_injective N h₀).eq_iff]; rw [P.rootForm_self_smul_coroot i]; rw [smul_smul]; rw [mul_div_cancel₀ _ h₀]
  norm_cast

中文:
引理 coroot_eq_polarizationEquiv_apply_root
  条件: (i : ι)
  证明: by
  have h₀ := IsAnisotropic.rootForm_root_ne_zero (P := P) i
  rw [polarizationEquiv_apply]; rw [← (smul_right_injective N h₀).eq_iff]; rw [P.rootForm_self_smul_coroot i]; rw [smul_smul]; rw [mul_div_cancel₀ _ h₀]
  norm_cast

Depends on / 依赖: IsAnisotropic, IsAnisotropic.rootForm_root_ne_zero, P.rootForm_self_smul_coroot, eq_iff, polarizationEquiv_apply, rootForm_root_ne_zero, rootForm_self_smul_coroot, smul_right_injective, smul_smul
-/
lemma coroot_eq_polarizationEquiv_apply_root (i : ι) :
    P.coroot i = (2 / P.RootForm (P.root i) (P.root i)) • P.PolarizationEquiv (P.root i) := by
  have h₀ := IsAnisotropic.rootForm_root_ne_zero (P := P) i
  rw [polarizationEquiv_apply]; rw [← (smul_right_injective N h₀).eq_iff]; rw [P.rootForm_self_smul_coroot i]; rw [smul_smul]; rw [mul_div_cancel₀ _ h₀]
  norm_cast

/--
lemma `polarizationEquiv_symm_apply_coroot` / 引理 `polarizationEquiv_symm_apply_coroot`

English:
lemma polarizationEquiv_symm_apply_coroot
  given: {i : ι}
  proof: by
  simp [coroot_eq_polarizationEquiv_apply_root]

中文:
引理 polarizationEquiv_symm_apply_coroot
  条件: {i : ι}
  证明: by
  simp [coroot_eq_polarizationEquiv_apply_root]

Depends on / 依赖: coroot_eq_polarizationEquiv_apply_root
-/
lemma polarizationEquiv_symm_apply_coroot {i : ι} :
    P.PolarizationEquiv.symm (P.coroot i) = (2 / P.RootForm (P.root i) (P.root i)) • P.root i := by
  simp [coroot_eq_polarizationEquiv_apply_root]

variable [NeZero (2 : R)]

/--
lemma `linearIndepOn_coroot_iff_aux` / 引理 `linearIndepOn_coroot_iff_aux`

English:
lemma linearIndepOn_coroot_iff_aux
  given: {s : Set ι} (h : LinearIndepOn R P.root s)
  proof: by
  obtain ⟨f, hf⟩ : exists f : s -> Rˣ, forall i : s, P.coroot i = f i • P.PolarizationEquiv (P.root i) :=
    ⟨fun i => Units.mk0 (2 / P.RootForm (P.root i) (P.root i))
      (by simp [two_ne_zero, IsAnisotropic.rootForm_root_ne_zero]),
     fun i => by simp [coroot_eq_polarizationEquiv_apply_roo

中文:
引理 linearIndepOn_coroot_iff_aux
  条件: {s : 集合 ι} (h : LinearIndepOn R P.root s)
  证明: by
  obtain ⟨f, hf⟩ : exists f : s -> Rˣ, forall i : s, P.coroot i = f i • P.PolarizationEquiv (P.root i) :=
    ⟨fun i => Units.mk0 (2 / P.RootForm (P.root i) (P.root i))
      (by simp [two_ne_zero, IsAnisotropic.rootForm_root_ne_zero]),
     fun i => by simp [coroot_eq_polarizationEquiv_apply_roo
-/
private lemma linearIndepOn_coroot_iff_aux {s : Set ι} (h : LinearIndepOn R P.root s) :
    LinearIndepOn R P.coroot s := by
  obtain ⟨f, hf⟩ : exists f : s -> Rˣ, forall i : s, P.coroot i = f i • P.PolarizationEquiv (P.root i) :=
    ⟨fun i => Units.mk0 (2 / P.RootForm (P.root i) (P.root i))
      (by simp [two_ne_zero, IsAnisotropic.rootForm_root_ne_zero]),
     fun i => by simp [coroot_eq_polarizationEquiv_apply_root]⟩
  have : s.domRestrict P.coroot = P.PolarizationEquiv.toLinearMap ∘ (f • s.domRestrict P.root) := by
    ext; simp [hf, polarizationEquiv_apply]
  rw [← linearIndependent_restrict_iff]; rw [this]; rw [LinearMap.linearIndependent_iff_of_injOn _ P.PolarizationEquiv.injective.injOn]
  simpa

/--
lemma `linearIndepOn_coroot_iff` / 引理 `linearIndepOn_coroot_iff`

English:
lemma linearIndepOn_coroot_iff
  given: {s : Set ι}
  proof: ⟨P.flip.linearIndepOn_coroot_iff_aux, P.linearIndepOn_coroot_iff_aux⟩

中文:
引理 linearIndepOn_coroot_iff
  条件: {s : 集合 ι}
  证明: ⟨P.flip.linearIndepOn_coroot_iff_aux, P.linearIndepOn_coroot_iff_aux⟩
-/
@[simp] lemma linearIndepOn_coroot_iff {s : Set ι} :
    LinearIndepOn R P.coroot s ↔ LinearIndepOn R P.root s :=
  ⟨P.flip.linearIndepOn_coroot_iff_aux, P.linearIndepOn_coroot_iff_aux⟩

end IsRootSystem

end Field

section LinearOrderedCommRing

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [Module R M] [Module R N] (P : RootPairing ι R M N)

/--
Instance `instIsAnisotropicOfLinearOrderedCommRing` / 实例 `instIsAnisotropicOfLinearOrderedCommRing`

English:
instance instIsAnisotropicOfLinearOrderedCommRing
  signature: : IsAnisotropic P
  body: P.isAnisotropic_of_isValuedIn R

中文:
实例 instIsAnisotropicOfLinearOrderedCommRing
  签名: : 是Anisotropic P
  定义体: P.isAnisotropic_of_isValuedIn R

Depends on / 依赖: P.isAnisotropic_of_isValuedIn, isAnisotropic_of_isValuedIn
-/
instance instIsAnisotropicOfLinearOrderedCommRing : IsAnisotropic P :=
  P.isAnisotropic_of_isValuedIn R

/--
lemma `zero_le_rootForm` / 引理 `zero_le_rootForm`

English:
lemma zero_le_rootForm
  given: (x : M)
  proof: (P.rootForm_self_sum_of_squares x).nonneg

中文:
引理 zero_le_rootForm
  条件: (x : M)
  证明: (P.rootForm_self_sum_of_squares x).nonneg

Depends on / 依赖: P.rootForm_self_sum_of_squares, nonneg, rootForm_self_sum_of_squares
-/
lemma zero_le_rootForm (x : M) :
    0 <= P.RootForm x x :=
  (P.rootForm_self_sum_of_squares x).nonneg

/--
lemma `rootForm_restrict_nondegenerate_of_ordered` / 引理 `rootForm_restrict_nondegenerate_of_ordered`

English:
lemma rootForm_restrict_nondegenerate_of_ordered
  proof: (P.RootForm.nondegenerate_restrict_iff_disjoint_ker P.zero_le_rootForm
    P.rootForm_symmetric).mpr P.disjoint_rootSpan_ker_rootForm

中文:
引理 rootForm_restrict_nondegenerate_of_ordered
  证明: (P.RootForm.nondegenerate_restrict_iff_disjoint_ker P.zero_le_rootForm
    P.rootForm_symmetric).mpr P.disjoint_rootSpan_ker_rootForm

Depends on / 依赖: CompactSpace, CompactSpace.isFiniteMeasure, P.RootForm.nondegenerate_restrict_iff_disjoint_ker, P.disjoint_rootSpan_ker_rootForm, P.rootForm_symmetric, P.zero_le_rootForm, RootForm, TopologicalSpace, disjoint_rootSpan_ker_rootForm, isFiniteMeasure, nondegenerate_restrict_iff_disjoint_ker, rootForm_symmetric, zero_le_rootForm
-/
lemma rootForm_restrict_nondegenerate_of_ordered :
    LinearMap.Nondegenerate (P.RootForm.restrict (P.rootSpan R)) :=
  (P.RootForm.nondegenerate_restrict_iff_disjoint_ker P.zero_le_rootForm
    P.rootForm_symmetric).mpr P.disjoint_rootSpan_ker_rootForm

/--
lemma `rootForm_self_eq_zero_iff` / 引理 `rootForm_self_eq_zero_iff`

English:
lemma rootForm_self_eq_zero_iff
  given: {x : M}
  proof: P.RootForm.apply_apply_same_eq_zero_iff P.zero_le_rootForm P.rootForm_symmetric

中文:
引理 rootForm_self_eq_zero_iff
  条件: {x : M}
  证明: P.RootForm.apply_apply_same_eq_zero_iff P.zero_le_rootForm P.rootForm_symmetric

Depends on / 依赖: P.RootForm.apply_apply_same_eq_zero_iff, P.rootForm_symmetric, P.zero_le_rootForm, RootForm, TopologicalSpace, apply_apply_same_eq_zero_iff, isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts, rootForm_symmetric, zero_le_rootForm
-/
lemma rootForm_self_eq_zero_iff {x : M} :
    P.RootForm x x = 0 ↔ x in LinearMap.ker P.RootForm :=
  P.RootForm.apply_apply_same_eq_zero_iff P.zero_le_rootForm P.rootForm_symmetric

/--
lemma `eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero` / 引理 `eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero`

English:
lemma eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero
  statement: {x : M}
  proof: by
  have : x in P.rootSpan R ⊓ LinearMap.ker P.RootForm := ⟨hx, P.rootForm_self_eq_zero_iff.mp hx'⟩
  simpa [P.disjoint_rootSpan_ker_rootForm.eq_bot] using this

中文:
引理 eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero
  结论: {x : M}
  证明: by
  have : x in P.rootSpan R ⊓ LinearMap.ker P.RootForm := ⟨hx, P.rootForm_self_eq_zero_iff.mp hx'⟩
  simpa [P.disjoint_rootSpan_ker_rootForm.eq_bot] using this

Depends on / 依赖: LinearMap, LinearMap.ker, P.RootForm, P.disjoint_rootSpan_ker_rootForm.eq_bot, P.rootForm_self_eq_zero_iff.mp, P.rootSpan, RootForm, disjoint_rootSpan_ker_rootForm, eq_bot, rootForm_self_eq_zero_iff, rootSpan
-/
lemma eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero {x : M}
    (hx : x in P.rootSpan R) (hx' : P.RootForm x x = 0) :
    x = 0 := by
  have : x in P.rootSpan R ⊓ LinearMap.ker P.RootForm := ⟨hx, P.rootForm_self_eq_zero_iff.mp hx'⟩
  simpa [P.disjoint_rootSpan_ker_rootForm.eq_bot] using this

/--
lemma `rootForm_pos_of_ne_zero` / 引理 `rootForm_pos_of_ne_zero`

English:
lemma rootForm_pos_of_ne_zero
  given: {x : M} (hx : x in P.rootSpan R) (h : x != 0)
  proof: by
  apply (P.zero_le_rootForm x).lt_of_ne
  contrapose h
  exact P.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero hx h.symm

中文:
引理 rootForm_pos_of_ne_zero
  条件: {x : M} (hx : x in P.rootSpan R) (h : x != 0)
  证明: by
  apply (P.zero_le_rootForm x).lt_of_ne
  contrapose h
  exact P.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero hx h.symm

Depends on / 依赖: P.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero, P.zero_le_rootForm, contrapose, eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero, h.symm, lt_of_ne, zero_le_rootForm
-/
lemma rootForm_pos_of_ne_zero {x : M} (hx : x in P.rootSpan R) (h : x != 0) :
    0 < P.RootForm x x := by
  apply (P.zero_le_rootForm x).lt_of_ne
  contrapose h
  exact P.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero hx h.symm

/--
lemma `rootForm_anisotropic` / 引理 `rootForm_anisotropic`

English:
lemma rootForm_anisotropic
  given: [P.IsRootSystem]
  proof: fun x => P.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero by simp

中文:
引理 rootForm_anisotropic
  条件: [P.是RootSystem]
  证明: fun x => P.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero by simp

Depends on / 依赖: P.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero, eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero
-/
lemma rootForm_anisotropic [P.IsRootSystem] :
    P.RootForm.toQuadraticMap.Anisotropic :=
fun x => P.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero by simp

end LinearOrderedCommRing

end RootPairing
