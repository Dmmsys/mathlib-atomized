/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Ring.SumsOfSquares
public import Mathlib.LinearAlgebra.RootSystem.RootPositive

/-!
# The canonical bilinear form on a finite root pairing

Given a finite root pairing, we define a canonical map from weight space to coweight space, and the
corresponding bilinear form. This form is symmetric and Weyl-invariant, and if the base ring is
linearly ordered, then the form is root-positive, positive-semidefinite on the weight space, and
positive-definite on the span of roots.
From these facts, it is easy to show that Coxeter weights in a finite root pairing are bounded
above by 4. Thus, the pairings of roots and coroots in a crystallographic root pairing are
restricted to a small finite set of possibilities.
Another application is to the faithfulness of the Weyl group action on roots, and finiteness of the
Weyl group.

## Main definitions:
* `RootPairing.Polarization`: A distinguished linear map from the weight space to the coweight
  space.
* `RootPairing.RootForm` : The bilinear form on weight space corresponding to `Polarization`.

## Main results:
* `RootPairing.rootForm_self_sum_of_squares` : The inner product of any
  weight vector is a sum of squares.
* `RootPairing.rootForm_reflection_reflection_apply` : `RootForm` is invariant with respect
  to reflections.
* `RootPairing.rootForm_self_smul_coroot`: The inner product of a root with itself
  times the corresponding coroot is equal to two times Polarization applied to the root.
* `RootPairing.exists_ge_zero_eq_rootForm`: `RootForm` is positive semidefinite.

## References:
* [N. Bourbaki, *Lie groups and Lie algebras. Chapters 4--6*][bourbaki1968]
* [M. Demazure, *SGA III, Exposé XXI, Données Radicielles*][demazure1970]

-/

@[expose] public section

open Set Function
open Module hiding reflection
open Submodule (span)

noncomputable section

variable {ι R M N : Type*}

namespace RootPairing

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

section Fintype

variable [Fintype ι]

/--
Definition of `Polarization` / `Polarization` 的定义

English:
definition Polarization
  signature: : M ->ₗ[R] N
  body: ∑ i, LinearMap.toSpanSingleton R N (P.coroot i) ∘ₗ P.coroot' i

@[simp]

中文:
定义 Polarization
  签名: : M ->ₗ[R] N
  定义体: ∑ i, LinearMap.toSpanSingleton R N (P.coroot i) ∘ₗ P.coroot' i

@[simp]

Depends on / 依赖: LinearMap, LinearMap.toSpanSingleton, P.coroot, coroot, toSpanSingleton
-/
def Polarization : M ->ₗ[R] N :=
  ∑ i, LinearMap.toSpanSingleton R N (P.coroot i) ∘ₗ P.coroot' i

@[simp]
/--
lemma `Polarization_apply` / 引理 `Polarization_apply`

English:
lemma Polarization_apply
  given: (x : M)
  proof: by
  simp [Polarization]

中文:
引理 Polarization_apply
  条件: (x : M)
  证明: by
  simp [Polarization]

Depends on / 依赖: Polarization
-/
lemma Polarization_apply (x : M) :
    P.Polarization x = ∑ i, P.coroot' i x • P.coroot i := by
  simp [Polarization]

/--
Definition of `CoPolarization` / `CoPolarization` 的定义

English:
definition CoPolarization
  signature: : N ->ₗ[R] M
  body: P.flip.Polarization

@[simp]

中文:
定义 CoPolarization
  签名: : N ->ₗ[R] M
  定义体: P.flip.Polarization

@[simp]

Depends on / 依赖: P.flip.Polarization, Polarization
-/
def CoPolarization : N ->ₗ[R] M :=
  P.flip.Polarization

@[simp]
/--
lemma `CoPolarization_apply` / 引理 `CoPolarization_apply`

English:
lemma CoPolarization_apply
  given: (x : N)
  proof: P.flip.Polarization_apply x

中文:
引理 CoPolarization_apply
  条件: (x : N)
  证明: P.flip.Polarization_apply x

Depends on / 依赖: P.flip.Polarization_apply, Polarization_apply
-/
lemma CoPolarization_apply (x : N) :
    P.CoPolarization x = ∑ i, P.root' i x • P.root i :=
  P.flip.Polarization_apply x

/--
lemma `CoPolarization_eq` / 引理 `CoPolarization_eq`

English:
lemma CoPolarization_eq
  statement: P.CoPolarization = P.flip.Polarization
  proof: rfl

中文:
引理 CoPolarization_eq
  结论: P.CoPolarization = P.flip.Polarization
  证明: rfl
-/
lemma CoPolarization_eq : P.CoPolarization = P.flip.Polarization :=
  rfl

/--
Definition of `RootForm` / `RootForm` 的定义

English:
definition RootForm
  signature: : LinearMap.BilinForm R M
  body: ∑ i, (P.coroot' i).smulRight (P.coroot' i)

中文:
定义 RootForm
  签名: : LinearMap.BilinForm R M
  定义体: ∑ i, (P.coroot' i).smulRight (P.coroot' i)

Depends on / 依赖: P.coroot, coroot, smulRight
-/
def RootForm : LinearMap.BilinForm R M :=
  ∑ i, (P.coroot' i).smulRight (P.coroot' i)

/--
Definition of `CorootForm` / `CorootForm` 的定义

English:
definition CorootForm
  signature: : LinearMap.BilinForm R N
  body: P.flip.RootForm

中文:
定义 CorootForm
  签名: : LinearMap.BilinForm R N
  定义体: P.flip.RootForm

Depends on / 依赖: P.flip.RootForm, RootForm
-/
def CorootForm : LinearMap.BilinForm R N :=
  P.flip.RootForm

/--
lemma `rootForm_apply_apply` / 引理 `rootForm_apply_apply`

English:
lemma rootForm_apply_apply
  given: (x y : M)
  statement: P.RootForm x y =
  proof: by
  simp [RootForm]

中文:
引理 rootForm_apply_apply
  条件: (x y : M)
  结论: P.RootForm x y =
  证明: by
  simp [RootForm]

Depends on / 依赖: RootForm
-/
lemma rootForm_apply_apply (x y : M) : P.RootForm x y =
    ∑ i, P.coroot' i x * P.coroot' i y := by
  simp [RootForm]

/--
lemma `corootForm_apply_apply` / 引理 `corootForm_apply_apply`

English:
lemma corootForm_apply_apply
  given: (x y : N)
  statement: P.CorootForm x y =
  proof: P.flip.rootForm_apply_apply x y

中文:
引理 corootForm_apply_apply
  条件: (x y : N)
  结论: P.CorootForm x y =
  证明: P.flip.rootForm_apply_apply x y

Depends on / 依赖: P.flip.rootForm_apply_apply, rootForm_apply_apply
-/
lemma corootForm_apply_apply (x y : N) : P.CorootForm x y =
    ∑ i, P.root' i x * P.root' i y :=
  P.flip.rootForm_apply_apply x y

/--
lemma `toLinearMap_apply_apply_Polarization` / 引理 `toLinearMap_apply_apply_Polarization`

English:
lemma toLinearMap_apply_apply_Polarization
  given: (x y : M)
  proof: by
  simp [RootForm]

中文:
引理 toLinearMap_apply_apply_Polarization
  条件: (x y : M)
  证明: by
  simp [RootForm]

Depends on / 依赖: RootForm
-/
lemma toLinearMap_apply_apply_Polarization (x y : M) :
    P.toLinearMap y (P.Polarization x) = P.RootForm x y := by
  simp [RootForm]

/--
lemma `toLinearMap_apply_CoPolarization` / 引理 `toLinearMap_apply_CoPolarization`

English:
lemma toLinearMap_apply_CoPolarization
  given: (x : N)
  proof: by
  ext y
  exact P.flip.toLinearMap_apply_apply_Polarization x y

中文:
引理 toLinearMap_apply_CoPolarization
  条件: (x : N)
  证明: by
  ext y
  exact P.flip.toLinearMap_apply_apply_Polarization x y

Depends on / 依赖: P.flip.toLinearMap_apply_apply_Polarization, toLinearMap_apply_apply_Polarization
-/
lemma toLinearMap_apply_CoPolarization (x : N) :
    P.toLinearMap (P.CoPolarization x) = P.CorootForm x := by
  ext y
  exact P.flip.toLinearMap_apply_apply_Polarization x y

/--
lemma `flip_comp_polarization_eq_rootForm` / 引理 `flip_comp_polarization_eq_rootForm`

English:
lemma flip_comp_polarization_eq_rootForm
  proof: by
  ext; simp [rootForm_apply_apply, RootPairing.flip]

中文:
引理 flip_comp_polarization_eq_rootForm
  证明: by
  ext; simp [rootForm_apply_apply, RootPairing.flip]

Depends on / 依赖: RootPairing, RootPairing.flip, rootForm_apply_apply
-/
lemma flip_comp_polarization_eq_rootForm :
    P.flip.toLinearMap ∘ₗ P.Polarization = P.RootForm := by
  ext; simp [rootForm_apply_apply, RootPairing.flip]

/--
lemma `self_comp_coPolarization_eq_corootForm` / 引理 `self_comp_coPolarization_eq_corootForm`

English:
lemma self_comp_coPolarization_eq_corootForm
  proof: P.flip.flip_comp_polarization_eq_rootForm

中文:
引理 self_comp_coPolarization_eq_corootForm
  证明: P.flip.flip_comp_polarization_eq_rootForm

Depends on / 依赖: P.flip.flip_comp_polarization_eq_rootForm, flip_comp_polarization_eq_rootForm
-/
lemma self_comp_coPolarization_eq_corootForm :
    P.toLinearMap ∘ₗ P.CoPolarization = P.CorootForm :=
  P.flip.flip_comp_polarization_eq_rootForm

/--
lemma `polarization_apply_eq_zero_iff` / 引理 `polarization_apply_eq_zero_iff`

English:
lemma polarization_apply_eq_zero_iff
  given: (m : M)
  proof: by
  rw [← flip_comp_polarization_eq_rootForm]
  refine ⟨fun h => by simp [h], ?_⟩
  rintro (h : P.flip.toPerfPair (P.Polarization m) = 0)
  simpa only [EmbeddingLike.map_eq_zero_iff] using h

中文:
引理 polarization_apply_eq_zero_iff
  条件: (m : M)
  证明: by
  rw [← flip_comp_polarization_eq_rootForm]
  refine ⟨fun h => by simp [h], ?_⟩
  rintro (h : P.flip.toPerfPair (P.Polarization m) = 0)
  simpa only [EmbeddingLike.map_eq_zero_iff] using h

Depends on / 依赖: EmbeddingLike, EmbeddingLike.map_eq_zero_iff, P.Polarization, P.flip.toPerfPair, Polarization, flip_comp_polarization_eq_rootForm, map_eq_zero_iff, toPerfPair
-/
lemma polarization_apply_eq_zero_iff (m : M) :
    P.Polarization m = 0 ↔ P.RootForm m = 0 := by
  rw [← flip_comp_polarization_eq_rootForm]
  refine ⟨fun h => by simp [h], ?_⟩
  rintro (h : P.flip.toPerfPair (P.Polarization m) = 0)
  simpa only [EmbeddingLike.map_eq_zero_iff] using h

/--
lemma `coPolarization_apply_eq_zero_iff` / 引理 `coPolarization_apply_eq_zero_iff`

English:
lemma coPolarization_apply_eq_zero_iff
  given: (n : N)
  proof: P.flip.polarization_apply_eq_zero_iff n

中文:
引理 coPolarization_apply_eq_zero_iff
  条件: (n : N)
  证明: P.flip.polarization_apply_eq_zero_iff n

Depends on / 依赖: P.flip.polarization_apply_eq_zero_iff, polarization_apply_eq_zero_iff
-/
lemma coPolarization_apply_eq_zero_iff (n : N) :
    P.CoPolarization n = 0 ↔ P.CorootForm n = 0 :=
  P.flip.polarization_apply_eq_zero_iff n

/--
lemma `ker_polarization_eq_ker_rootForm` / 引理 `ker_polarization_eq_ker_rootForm`

English:
lemma ker_polarization_eq_ker_rootForm
  proof: by
  ext; simp only [LinearMap.mem_ker, P.polarization_apply_eq_zero_iff]

中文:
引理 ker_polarization_eq_ker_rootForm
  证明: by
  ext; simp only [LinearMap.mem_ker, P.polarization_apply_eq_zero_iff]

Depends on / 依赖: LinearMap, LinearMap.mem_ker, P.polarization_apply_eq_zero_iff, mem_ker, polarization_apply_eq_zero_iff
-/
lemma ker_polarization_eq_ker_rootForm :
    LinearMap.ker P.Polarization = LinearMap.ker P.RootForm := by
  ext; simp only [LinearMap.mem_ker, P.polarization_apply_eq_zero_iff]

/--
lemma `ker_copolarization_eq_ker_corootForm` / 引理 `ker_copolarization_eq_ker_corootForm`

English:
lemma ker_copolarization_eq_ker_corootForm
  proof: P.flip.ker_polarization_eq_ker_rootForm

中文:
引理 ker_copolarization_eq_ker_corootForm
  证明: P.flip.ker_polarization_eq_ker_rootForm

Depends on / 依赖: P.flip.ker_polarization_eq_ker_rootForm, ker_polarization_eq_ker_rootForm
-/
lemma ker_copolarization_eq_ker_corootForm :
    LinearMap.ker P.CoPolarization = LinearMap.ker P.CorootForm :=
  P.flip.ker_polarization_eq_ker_rootForm

/--
lemma `rootForm_symmetric` / 引理 `rootForm_symmetric`

English:
lemma rootForm_symmetric
  proof: by
  simp [LinearMap.isSymm_def, mul_comm, rootForm_apply_apply]

@[simp]

中文:
引理 rootForm_symmetric
  证明: by
  simp [LinearMap.isSymm_def, mul_comm, rootForm_apply_apply]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.isSymm_def, isSymm_def, mul_comm, rootForm_apply_apply
-/
lemma rootForm_symmetric :
    LinearMap.IsSymm P.RootForm := by
  simp [LinearMap.isSymm_def, mul_comm, rootForm_apply_apply]

@[simp]
/--
lemma `rootForm_reflection_reflection_apply` / 引理 `rootForm_reflection_reflection_apply`

English:
lemma rootForm_reflection_reflection_apply
  given: (i : ι) (x y : M)
  proof: by
  simp only [rootForm_apply_apply, coroot'_reflection]
  exact Fintype.sum_equiv (P.reflectionPerm i)
    (fun j => (P.coroot' (P.reflectionPerm i j) x) * (P.coroot' (P.reflectionPerm i j) y))
    (fun j => P.coroot' j x * P.coroot' j y) (congrFun rfl)

中文:
引理 rootForm_reflection_reflection_apply
  条件: (i : ι) (x y : M)
  证明: by
  simp only [rootForm_apply_apply, coroot'_reflection]
  exact Fintype.sum_equiv (P.reflectionPerm i)
    (fun j => (P.coroot' (P.reflectionPerm i j) x) * (P.coroot' (P.reflectionPerm i j) y))
    (fun j => P.coroot' j x * P.coroot' j y) (congrFun rfl)

Depends on / 依赖: Fintype, Fintype.sum_equiv, P.coroot, P.reflectionPerm, _reflection, coroot, reflectionPerm, rootForm_apply_apply, sum_equiv
-/
lemma rootForm_reflection_reflection_apply (i : ι) (x y : M) :
    P.RootForm (P.reflection i x) (P.reflection i y) = P.RootForm x y := by
  simp only [rootForm_apply_apply, coroot'_reflection]
  exact Fintype.sum_equiv (P.reflectionPerm i)
    (fun j => (P.coroot' (P.reflectionPerm i j) x) * (P.coroot' (P.reflectionPerm i j) y))
    (fun j => P.coroot' j x * P.coroot' j y) (congrFun rfl)

/--
lemma `rootForm_self_sum_of_squares` / 引理 `rootForm_self_sum_of_squares`

English:
lemma rootForm_self_sum_of_squares
  given: (x : M)
  proof: P.rootForm_apply_apply x x ▸ IsSumSq.sum_mul_self Finset.univ _

中文:
引理 rootForm_self_sum_of_squares
  条件: (x : M)
  证明: P.rootForm_apply_apply x x ▸ IsSumSq.sum_mul_self Finset.univ _

Depends on / 依赖: Finset, Finset.univ, IsSumSq, IsSumSq.sum_mul_self, P.rootForm_apply_apply, rootForm_apply_apply, sum_mul_self
-/
lemma rootForm_self_sum_of_squares (x : M) :
    IsSumSq (P.RootForm x x) :=
  P.rootForm_apply_apply x x ▸ IsSumSq.sum_mul_self Finset.univ _

/--
lemma `rootForm_root_self` / 引理 `rootForm_root_self`

English:
lemma rootForm_root_self
  given: (j : ι)
  proof: by
  simp [rootForm_apply_apply]

中文:
引理 rootForm_root_self
  条件: (j : ι)
  证明: by
  simp [rootForm_apply_apply]

Depends on / 依赖: rootForm_apply_apply
-/
lemma rootForm_root_self (j : ι) :
    P.RootForm (P.root j) (P.root j) = ∑ (i : ι), (P.pairing j i) * (P.pairing j i) := by
  simp [rootForm_apply_apply]

/--
theorem `range_polarization_domRestrict_le_span_coroot` / 定理 `range_polarization_domRestrict_le_span_coroot`

English:
theorem range_polarization_domRestrict_le_span_coroot
  proof: by
  intro y hy
  obtain ⟨x, hx⟩ := hy
  rw [← hx]; rw [LinearMap.domRestrict_apply]; rw [Polarization_apply]
  refine (Submodule.mem_span_range_iff_exists_fun R).mpr ?_
  use fun i => P.toLinearMap x (P.coroot i)
  simp

中文:
定理 range_polarization_domRestrict_le_span_coroot
  证明: by
  intro y hy
  obtain ⟨x, hx⟩ := hy
  rw [← hx]; rw [LinearMap.domRestrict_apply]; rw [Polarization_apply]
  refine (Submodule.mem_span_range_iff_exists_fun R).mpr ?_
  use fun i => P.toLinearMap x (P.coroot i)
  simp

Depends on / 依赖: LinearMap, LinearMap.domRestrict_apply, P.coroot, P.toLinearMap, Polarization_apply, Submodule, Submodule.mem_span_range_iff_exists_fun, coroot, domRestrict_apply, mem_span_range_iff_exists_fun, toLinearMap
-/
theorem range_polarization_domRestrict_le_span_coroot :
    LinearMap.range (P.Polarization.domRestrict (P.rootSpan R)) <= P.corootSpan R := by
  intro y hy
  obtain ⟨x, hx⟩ := hy
  rw [← hx]; rw [LinearMap.domRestrict_apply]; rw [Polarization_apply]
  refine (Submodule.mem_span_range_iff_exists_fun R).mpr ?_
  use fun i => P.toLinearMap x (P.coroot i)
  simp

/--
theorem `corootSpan_dualAnnihilator_le_ker_rootForm` / 定理 `corootSpan_dualAnnihilator_le_ker_rootForm`

English:
theorem corootSpan_dualAnnihilator_le_ker_rootForm
  proof: by
  rw [P.corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot']
  intro x hx
  ext y
  simp_all [coroot', rootForm_apply_apply]

中文:
定理 corootSpan_dualAnnihilator_le_ker_rootForm
  证明: by
  rw [P.corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot']
  intro x hx
  ext y
  simp_all [coroot', rootForm_apply_apply]

Depends on / 依赖: P.corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot, coroot, corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot, rootForm_apply_apply
-/
theorem corootSpan_dualAnnihilator_le_ker_rootForm :
    (P.corootSpan R).dualAnnihilator.map (P.toPerfPair.symm : Dual R N ->ₗ[R] M) <=
      P.RootForm.ker := by
  rw [P.corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot']
  intro x hx
  ext y
  simp_all [coroot', rootForm_apply_apply]

/--
theorem `rootSpan_dualAnnihilator_le_ker_rootForm` / 定理 `rootSpan_dualAnnihilator_le_ker_rootForm`

English:
theorem rootSpan_dualAnnihilator_le_ker_rootForm
  proof: P.flip.corootSpan_dualAnnihilator_le_ker_rootForm

中文:
定理 rootSpan_dualAnnihilator_le_ker_rootForm
  证明: P.flip.corootSpan_dualAnnihilator_le_ker_rootForm

Depends on / 依赖: P.flip.corootSpan_dualAnnihilator_le_ker_rootForm, corootSpan_dualAnnihilator_le_ker_rootForm
-/
theorem rootSpan_dualAnnihilator_le_ker_rootForm :
    (P.rootSpan R).dualAnnihilator.map (P.flip.toPerfPair.symm : Dual R M ->ₗ[R] N) <=
      P.CorootForm.ker :=
  P.flip.corootSpan_dualAnnihilator_le_ker_rootForm

end Fintype

section IsValuedIn

variable (S : Type*) [CommRing S] [Algebra S R] [FaithfulSMul S R] [Module S M]
  [IsScalarTower S R M] [Module S N] [IsScalarTower S R N] [P.IsValuedIn S] [Fintype ι] {i j : ι}

/--
Definition of `PolarizationIn` / `PolarizationIn` 的定义

English:
definition PolarizationIn
  signature: : P.rootSpan S ->ₗ[S] N
  body: ∑ i : ι, LinearMap.toSpanSingleton S N (P.coroot i) ∘ₗ P.coroot'In S i

omit [IsScalarTower S R N] in

中文:
定义 PolarizationIn
  签名: : P.rootSpan S ->ₗ[S] N
  定义体: ∑ i : ι, LinearMap.toSpanSingleton S N (P.coroot i) ∘ₗ P.coroot'In S i

omit [IsScalarTower S R N] in

Depends on / 依赖: LinearMap, LinearMap.toSpanSingleton, P.coroot, coroot, toSpanSingleton
-/
def PolarizationIn : P.rootSpan S ->ₗ[S] N :=
  ∑ i : ι, LinearMap.toSpanSingleton S N (P.coroot i) ∘ₗ P.coroot'In S i

omit [IsScalarTower S R N] in
/--
lemma `PolarizationIn_apply` / 引理 `PolarizationIn_apply`

English:
lemma PolarizationIn_apply
  given: (x : P.rootSpan S)
  proof: by
  simp [PolarizationIn]

中文:
引理 PolarizationIn_apply
  条件: (x : P.rootSpan S)
  证明: by
  simp [PolarizationIn]

Depends on / 依赖: PolarizationIn
-/
lemma PolarizationIn_apply (x : P.rootSpan S) :
    P.PolarizationIn S x = ∑ i, P.coroot'In S i x • P.coroot i := by
  simp [PolarizationIn]

/--
lemma `PolarizationIn_eq` / 引理 `PolarizationIn_eq`

English:
lemma PolarizationIn_eq
  given: (x : P.rootSpan S)
  proof: by
  simp only [PolarizationIn, LinearMap.coe_sum, LinearMap.coe_comp, Finset.sum_apply, comp_apply,
    LinearMap.toSpanSingleton_apply, Polarization_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [algebra_compatible_smul R (P.coroot'In S i x) (P.coroot i)]; rw [algebraMap_coroot'In_apply

中文:
引理 PolarizationIn_eq
  条件: (x : P.rootSpan S)
  证明: by
  simp only [PolarizationIn, LinearMap.coe_sum, LinearMap.coe_comp, Finset.sum_apply, comp_apply,
    LinearMap.toSpanSingleton_apply, Polarization_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [algebra_compatible_smul R (P.coroot'In S i x) (P.coroot i)]; rw [algebraMap_coroot'In_apply

Depends on / 依赖: Finset, Finset.sum_apply, Finset.sum_congr, In_apply, LinearMap, LinearMap.coe_comp, LinearMap.coe_sum, LinearMap.toSpanSingleton_apply, P.coroot, PolarizationIn, Polarization_apply, algebraMap_coroot, algebra_compatible_smul, coe_comp, coe_sum, comp_apply, coroot, sum_apply, sum_congr, toSpanSingleton_apply
-/
lemma PolarizationIn_eq (x : P.rootSpan S) :
    P.PolarizationIn S x = P.Polarization x := by
  simp only [PolarizationIn, LinearMap.coe_sum, LinearMap.coe_comp, Finset.sum_apply, comp_apply,
    LinearMap.toSpanSingleton_apply, Polarization_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [algebra_compatible_smul R (P.coroot'In S i x) (P.coroot i)]; rw [algebraMap_coroot'In_apply]

/--
lemma `range_polarizationIn` / 引理 `range_polarizationIn`

English:
lemma range_polarizationIn
  proof: by
  ext x
  simp [PolarizationIn_eq]

中文:
引理 range_polarizationIn
  证明: by
  ext x
  simp [PolarizationIn_eq]

Depends on / 依赖: PolarizationIn_eq
-/
lemma range_polarizationIn :
    Submodule.map P.Polarization (P.rootSpan R) = LinearMap.range (P.PolarizationIn R) := by
  ext x
  simp [PolarizationIn_eq]

/--
Definition of `CoPolarizationIn` / `CoPolarizationIn` 的定义

English:
definition CoPolarizationIn
  signature: : P.corootSpan S ->ₗ[S] M
  body: P.flip.PolarizationIn S

omit [IsScalarTower S R M] in

中文:
定义 CoPolarizationIn
  签名: : P.corootSpan S ->ₗ[S] M
  定义体: P.flip.PolarizationIn S

omit [IsScalarTower S R M] in

Depends on / 依赖: P.flip.PolarizationIn, PolarizationIn
-/
def CoPolarizationIn : P.corootSpan S ->ₗ[S] M :=
  P.flip.PolarizationIn S

omit [IsScalarTower S R M] in
/--
lemma `CoPolarizationIn_apply` / 引理 `CoPolarizationIn_apply`

English:
lemma CoPolarizationIn_apply
  given: (x : P.corootSpan S)
  proof: P.flip.PolarizationIn_apply S x

中文:
引理 CoPolarizationIn_apply
  条件: (x : P.corootSpan S)
  证明: P.flip.PolarizationIn_apply S x

Depends on / 依赖: P.flip.PolarizationIn_apply, PolarizationIn_apply
-/
lemma CoPolarizationIn_apply (x : P.corootSpan S) :
    P.CoPolarizationIn S x = ∑ i, P.root'In S i x • P.root i :=
  P.flip.PolarizationIn_apply S x

/--
lemma `CoPolarizationIn_eq` / 引理 `CoPolarizationIn_eq`

English:
lemma CoPolarizationIn_eq
  given: (x : P.corootSpan S)
  proof: P.flip.PolarizationIn_eq S x

中文:
引理 CoPolarizationIn_eq
  条件: (x : P.corootSpan S)
  证明: P.flip.PolarizationIn_eq S x

Depends on / 依赖: P.flip.PolarizationIn_eq, PolarizationIn_eq
-/
lemma CoPolarizationIn_eq (x : P.corootSpan S) :
    P.CoPolarizationIn S x = P.CoPolarization x :=
  P.flip.PolarizationIn_eq S x

/--
Definition of `RootFormIn` / `RootFormIn` 的定义

English:
definition RootFormIn
  signature: : LinearMap.BilinForm S (P.rootSpan S)
  body: ∑ i, (P.coroot'In S i).smulRight (P.coroot'In S i)

omit [Module S N] [IsScalarTower S R N] in

中文:
定义 RootFormIn
  签名: : LinearMap.BilinForm S (P.rootSpan S)
  定义体: ∑ i, (P.coroot'In S i).smulRight (P.coroot'In S i)

omit [Module S N] [IsScalarTower S R N] in

Depends on / 依赖: P.coroot, coroot, smulRight
-/
def RootFormIn : LinearMap.BilinForm S (P.rootSpan S) :=
  ∑ i, (P.coroot'In S i).smulRight (P.coroot'In S i)

omit [Module S N] [IsScalarTower S R N] in
/--
lemma `rootFormIn_isSymm` / 引理 `rootFormIn_isSymm`

English:
lemma rootFormIn_isSymm
  proof: by
  simp [LinearMap.isSymm_def, mul_comm, RootFormIn]

omit [Module S N] [IsScalarTower S R N] in
@[simp]

中文:
引理 rootFormIn_isSymm
  证明: by
  simp [LinearMap.isSymm_def, mul_comm, RootFormIn]

omit [Module S N] [IsScalarTower S R N] in
@[simp]

Depends on / 依赖: LinearMap, LinearMap.isSymm_def, RootFormIn, isSymm_def, mul_comm
-/
lemma rootFormIn_isSymm :
    (P.RootFormIn S).IsSymm := by
  simp [LinearMap.isSymm_def, mul_comm, RootFormIn]

omit [Module S N] [IsScalarTower S R N] in
@[simp]
/--
lemma `algebraMap_rootFormIn` / 引理 `algebraMap_rootFormIn`

English:
lemma algebraMap_rootFormIn
  given: (x y : P.rootSpan S)
  proof: by
  simp [RootFormIn, rootForm_apply_apply]

中文:
引理 algebraMap_rootFormIn
  条件: (x y : P.rootSpan S)
  证明: by
  simp [RootFormIn, rootForm_apply_apply]

Depends on / 依赖: RootFormIn, rootForm_apply_apply
-/
lemma algebraMap_rootFormIn (x y : P.rootSpan S) :
    (algebraMap S R) (P.RootFormIn S x y) = P.RootForm x y := by
  simp [RootFormIn, rootForm_apply_apply]

/--
lemma `toLinearMap_apply_PolarizationIn` / 引理 `toLinearMap_apply_PolarizationIn`

English:
lemma toLinearMap_apply_PolarizationIn
  given: (x y : P.rootSpan S)
  proof: by
  rw [PolarizationIn_eq]; rw [algebraMap_rootFormIn]
  exact toLinearMap_apply_apply_Polarization P x y

omit [IsScalarTower S R N] in

中文:
引理 toLinearMap_apply_PolarizationIn
  条件: (x y : P.rootSpan S)
  证明: by
  rw [PolarizationIn_eq]; rw [algebraMap_rootFormIn]
  exact toLinearMap_apply_apply_Polarization P x y

omit [IsScalarTower S R N] in

Depends on / 依赖: PolarizationIn_eq, algebraMap_rootFormIn, toLinearMap_apply_apply_Polarization
-/
lemma toLinearMap_apply_PolarizationIn (x y : P.rootSpan S) :
    P.toLinearMap y (P.PolarizationIn S x) =
      (algebraMap S R) (P.RootFormIn S x y) := by
  rw [PolarizationIn_eq]; rw [algebraMap_rootFormIn]
  exact toLinearMap_apply_apply_Polarization P x y

omit [IsScalarTower S R N] in
/--
lemma `range_polarizationIn_le_span_coroot` / 引理 `range_polarizationIn_le_span_coroot`

English:
lemma range_polarizationIn_le_span_coroot
  proof: by
  intro x hx
  obtain ⟨y, hy⟩ := hx
  rw [PolarizationIn_apply] at hy
  exact (Submodule.mem_span_range_iff_exists_fun S).mpr
    (Exists.intro (fun i => (P.coroot'In S i) y) hy)

中文:
引理 range_polarizationIn_le_span_coroot
  证明: by
  intro x hx
  obtain ⟨y, hy⟩ := hx
  rw [PolarizationIn_apply] at hy
  exact (Submodule.mem_span_range_iff_exists_fun S).mpr
    (Exists.intro (fun i => (P.coroot'In S i) y) hy)

Depends on / 依赖: Exists, Exists.intro, P.coroot, PolarizationIn_apply, Submodule, Submodule.mem_span_range_iff_exists_fun, coroot, mem_span_range_iff_exists_fun
-/
lemma range_polarizationIn_le_span_coroot :
    LinearMap.range (P.PolarizationIn S) <= P.corootSpan S := by
  intro x hx
  obtain ⟨y, hy⟩ := hx
  rw [PolarizationIn_apply] at hy
  exact (Submodule.mem_span_range_iff_exists_fun S).mpr
    (Exists.intro (fun i => (P.coroot'In S i) y) hy)

/--
lemma `rootFormIn_self_smul_coroot` / 引理 `rootFormIn_self_smul_coroot`

English:
lemma rootFormIn_self_smul_coroot
  given: (i : ι)
  proof: by
  have hP : P.PolarizationIn S (P.rootSpanMem S i) =
      ∑ j : ι, P.pairingIn S i (P.reflectionPerm i j) • P.coroot (P.reflectionPerm i j) := by
    simp_rw [PolarizationIn_apply, coroot'In_rootSpanMem_eq_pairingIn]
    exact (Fintype.sum_equiv (P.reflectionPerm i)
          (fun j => P.pairing

中文:
引理 rootFormIn_self_smul_coroot
  条件: (i : ι)
  证明: by
  have hP : P.PolarizationIn S (P.rootSpanMem S i) =
      ∑ j : ι, P.pairingIn S i (P.reflectionPerm i j) • P.coroot (P.reflectionPerm i j) := by
    simp_rw [PolarizationIn_apply, coroot'In_rootSpanMem_eq_pairingIn]
    exact (Fintype.sum_equiv (P.reflectionPerm i)
          (fun j => P.pairing

Depends on / 依赖: Fintype, Fintype.sum_equiv, In_rootSpanMem_eq_pairing, In_rootSpanMem_eq_pairingIn, P.PolarizationIn, P.coroot, P.pairingIn, P.reflectionPerm, P.rootSpanMem, PolarizationIn, PolarizationIn_apply, coroot, nth_rw, pairingIn, reflectionPerm, rootSpanMem, simp_rw, sum_equiv, two_nsmul
-/
lemma rootFormIn_self_smul_coroot (i : ι) :
    P.RootFormIn S (P.rootSpanMem S i) (P.rootSpanMem S i) • P.coroot i =
      2 • P.PolarizationIn S (P.rootSpanMem S i) := by
  have hP : P.PolarizationIn S (P.rootSpanMem S i) =
      ∑ j : ι, P.pairingIn S i (P.reflectionPerm i j) • P.coroot (P.reflectionPerm i j) := by
    simp_rw [PolarizationIn_apply, coroot'In_rootSpanMem_eq_pairingIn]
    exact (Fintype.sum_equiv (P.reflectionPerm i)
          (fun j => P.pairingIn S i (P.reflectionPerm i j) • P.coroot (P.reflectionPerm i j))
          (fun j => P.pairingIn S i j • P.coroot j) (congrFun rfl)).symm
  rw [two_nsmul]
  nth_rw 2 [hP]
  rw [PolarizationIn_apply]
  simp only [coroot'In_rootSpanMem_eq_pairingIn, pairingIn_reflectionPerm,
    pairingIn_reflectionPerm_self_left, ← reflectionPerm_coroot, neg_smul,
    smul_sub, sub_neg_eq_add]
  rw [Finset.sum_add_distrib]; rw [← add_assoc]; rw [← sub_eq_iff_eq_add]; rw [RootFormIn]
  simp only [LinearMap.coe_sum, LinearMap.coe_smulRight, Finset.sum_apply,
    coroot'In_rootSpanMem_eq_pairingIn, LinearMap.smul_apply, smul_eq_mul, Finset.sum_smul,
    root_coroot_eq_pairing, Finset.sum_neg_distrib, add_neg_cancel, sub_eq_zero]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [← P.algebraMap_pairingIn S]; rw [IsScalarTower.algebraMap_smul]; rw [← mul_smul]

/--
lemma `prod_rootFormIn_smul_coroot_mem_range_PolarizationIn` / 引理 `prod_rootFormIn_smul_coroot_mem_range_PolarizationIn`

English:
lemma prod_rootFormIn_smul_coroot_mem_range_PolarizationIn
  given: (i : ι)
  proof: by
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem
    (fun j => P.RootFormIn S (P.rootSpanMem S j) (P.rootSpanMem S j))
    (Finset.mem_univ i)
  rw [hc]; rw [mul_comm]; rw [mul_smul]; rw [rootFormIn_self_smul_coroot]
  refine LinearMap.mem_range.mpr ?_
  use c • 2 • (P.rootSpanMem S i)
  rw [map_smul];

中文:
引理 prod_rootFormIn_smul_coroot_mem_range_PolarizationIn
  条件: (i : ι)
  证明: by
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem
    (fun j => P.RootFormIn S (P.rootSpanMem S j) (P.rootSpanMem S j))
    (Finset.mem_univ i)
  rw [hc]; rw [mul_comm]; rw [mul_smul]; rw [rootFormIn_self_smul_coroot]
  refine LinearMap.mem_range.mpr ?_
  use c • 2 • (P.rootSpanMem S i)
  rw [map_smul];

Depends on / 依赖: Finset, Finset.dvd_prod_of_mem, Finset.mem_univ, LinearMap, LinearMap.mem_range.mpr, P.RootFormIn, P.rootSpanMem, RootFormIn, dvd_prod_of_mem, map_add, map_smul, mem_range, mem_univ, mul_comm, mul_smul, rootFormIn_self_smul_coroot, rootSpanMem, two_smul
-/
lemma prod_rootFormIn_smul_coroot_mem_range_PolarizationIn (i : ι) :
    (∏ j : ι, P.RootFormIn S (P.rootSpanMem S j) (P.rootSpanMem S j)) • P.coroot i in
      LinearMap.range (P.PolarizationIn S) := by
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem
    (fun j => P.RootFormIn S (P.rootSpanMem S j) (P.rootSpanMem S j))
    (Finset.mem_univ i)
  rw [hc]; rw [mul_comm]; rw [mul_smul]; rw [rootFormIn_self_smul_coroot]
  refine LinearMap.mem_range.mpr ?_
  use c • 2 • (P.rootSpanMem S i)
  rw [map_smul]; rw [two_smul]; rw [two_smul]; rw [map_add]

end IsValuedIn

section MoreFintype

variable [Fintype ι]

/--
lemma `rootForm_self_smul_coroot` / 引理 `rootForm_self_smul_coroot`

English:
lemma rootForm_self_smul_coroot
  given: (i : ι)
  proof: by
  have : (algebraMap R R) ((P.RootFormIn R) (P.rootSpanMem R i) (P.rootSpanMem R i)) • P.coroot i =
      2 • P.Polarization (P.root i) := by
    rw [Algebra.algebraMap_self_apply]; rw [P.rootFormIn_self_smul_coroot R i]; rw [PolarizationIn_eq]
  rw [← this]; rw [algebraMap_rootFormIn]

中文:
引理 rootForm_self_smul_coroot
  条件: (i : ι)
  证明: by
  have : (algebraMap R R) ((P.RootFormIn R) (P.rootSpanMem R i) (P.rootSpanMem R i)) • P.coroot i =
      2 • P.Polarization (P.root i) := by
    rw [Algebra.algebraMap_self_apply]; rw [P.rootFormIn_self_smul_coroot R i]; rw [PolarizationIn_eq]
  rw [← this]; rw [algebraMap_rootFormIn]

Depends on / 依赖: Algebra, Algebra.algebraMap_self_apply, P.Polarization, P.RootFormIn, P.coroot, P.root, P.rootFormIn_self_smul_coroot, P.rootSpanMem, Polarization, PolarizationIn_eq, RootFormIn, algebraMap, algebraMap_rootFormIn, algebraMap_self_apply, coroot, rootFormIn_self_smul_coroot, rootSpanMem
-/
lemma rootForm_self_smul_coroot (i : ι) :
    (P.RootForm (P.root i) (P.root i)) • P.coroot i = 2 • P.Polarization (P.root i) := by
  have : (algebraMap R R) ((P.RootFormIn R) (P.rootSpanMem R i) (P.rootSpanMem R i)) • P.coroot i =
      2 • P.Polarization (P.root i) := by
    rw [Algebra.algebraMap_self_apply]; rw [P.rootFormIn_self_smul_coroot R i]; rw [PolarizationIn_eq]
  rw [← this]; rw [algebraMap_rootFormIn]

/--
lemma `corootForm_self_smul_root` / 引理 `corootForm_self_smul_root`

English:
lemma corootForm_self_smul_root
  given: (i : ι)
  proof: rootForm_self_smul_coroot (P.flip) i

中文:
引理 corootForm_self_smul_root
  条件: (i : ι)
  证明: rootForm_self_smul_coroot (P.flip) i

Depends on / 依赖: P.flip, rootForm_self_smul_coroot
-/
lemma corootForm_self_smul_root (i : ι) :
    (P.CorootForm (P.coroot i) (P.coroot i)) • P.root i = 2 • P.CoPolarization (P.coroot i) :=
  rootForm_self_smul_coroot (P.flip) i

/--
lemma `four_nsmul_coPolarization_compl_polarization_apply_root` / 引理 `four_nsmul_coPolarization_compl_polarization_apply_root`

English:
lemma four_nsmul_coPolarization_compl_polarization_apply_root
  given: (i : ι)
  proof: by
  rw [LinearMap.smul_apply]; rw [LinearMap.comp_apply]; rw [show 4 = 2 * 2 from rfl]; rw [mul_smul]; rw [← map_nsmul]; rw [← rootForm_self_smul_coroot]; rw [map_smul]; rw [smul_comm]; rw [← corootForm_self_smul_root]; rw [smul_smul]

中文:
引理 four_nsmul_coPolarization_compl_polarization_apply_root
  条件: (i : ι)
  证明: by
  rw [LinearMap.smul_apply]; rw [LinearMap.comp_apply]; rw [show 4 = 2 * 2 from rfl]; rw [mul_smul]; rw [← map_nsmul]; rw [← rootForm_self_smul_coroot]; rw [map_smul]; rw [smul_comm]; rw [← corootForm_self_smul_root]; rw [smul_smul]

Depends on / 依赖: LinearMap, LinearMap.comp_apply, LinearMap.smul_apply, comp_apply, corootForm_self_smul_root, map_nsmul, map_smul, mul_smul, rootForm_self_smul_coroot, smul_apply, smul_comm, smul_smul
-/
lemma four_nsmul_coPolarization_compl_polarization_apply_root (i : ι) :
    (4 • P.CoPolarization ∘ₗ P.Polarization) (P.root i) =
    (P.RootForm (P.root i) (P.root i) * P.CorootForm (P.coroot i) (P.coroot i)) • P.root i := by
  rw [LinearMap.smul_apply]; rw [LinearMap.comp_apply]; rw [show 4 = 2 * 2 from rfl]; rw [mul_smul]; rw [← map_nsmul]; rw [← rootForm_self_smul_coroot]; rw [map_smul]; rw [smul_comm]; rw [← corootForm_self_smul_root]; rw [smul_smul]

/--
lemma `four_smul_rootForm_sq_eq_coxeterWeight_smul` / 引理 `four_smul_rootForm_sq_eq_coxeterWeight_smul`

English:
lemma four_smul_rootForm_sq_eq_coxeterWeight_smul
  given: (i j : ι)
  proof: by
  have hij : 4 • (P.RootForm (P.root i)) (P.root j) =
      2 • P.toLinearMap (P.root j) (2 • P.Polarization (P.root i)) := by
    rw [← toLinearMap_apply_apply_Polarization]; rw [LinearMap.map_smul_of_tower]; rw [← smul_assoc]; rw [Nat.nsmul_eq_mul]
  have hji : 2 • (P.RootForm (P.root i)) (P.ro

中文:
引理 four_smul_rootForm_sq_eq_coxeterWeight_smul
  条件: (i j : ι)
  证明: by
  have hij : 4 • (P.RootForm (P.root i)) (P.root j) =
      2 • P.toLinearMap (P.root j) (2 • P.Polarization (P.root i)) := by
    rw [← toLinearMap_apply_apply_Polarization]; rw [LinearMap.map_smul_of_tower]; rw [← smul_assoc]; rw [Nat.nsmul_eq_mul]
  have hji : 2 • (P.RootForm (P.root i)) (P.ro

Depends on / 依赖: LinearMap, LinearMap.map_smul_of_tower, Nat.nsmul_eq_mul, P.Polarization, P.RootForm, P.root, P.toLinearMap, Polarization, RootForm, map_smul_of_tower, nsmul_eq_mul, rootForm_symmetric, smul_assoc, toLinearMap, toLinearMap_apply_a, toLinearMap_apply_apply_Polarization
-/
lemma four_smul_rootForm_sq_eq_coxeterWeight_smul (i j : ι) :
    4 • (P.RootForm (P.root i) (P.root j)) ^ 2 = P.coxeterWeight i j •
      (P.RootForm (P.root i) (P.root i) * P.RootForm (P.root j) (P.root j)) := by
  have hij : 4 • (P.RootForm (P.root i)) (P.root j) =
      2 • P.toLinearMap (P.root j) (2 • P.Polarization (P.root i)) := by
    rw [← toLinearMap_apply_apply_Polarization]; rw [LinearMap.map_smul_of_tower]; rw [← smul_assoc]; rw [Nat.nsmul_eq_mul]
  have hji : 2 • (P.RootForm (P.root i)) (P.root j) =
      P.toLinearMap (P.root i) (2 • P.Polarization (P.root j)) := by
    rw [show (P.RootForm (P.root i)) (P.root j) = (P.RootForm (P.root j)) (P.root i) by
      apply (rootForm_symmetric P).eq]; rw [← toLinearMap_apply_apply_Polarization]; rw [LinearMap.map_smul_of_tower]
  rw [sq]; rw [nsmul_eq_mul]; rw [← mul_assoc]; rw [← nsmul_eq_mul]; rw [hij]; rw [← rootForm_self_smul_coroot]; rw [smul_mul_assoc 2]; rw [← mul_smul_comm]; rw [hji]; rw [← rootForm_self_smul_coroot]; rw [map_smul]; rw [← pairing]; rw [map_smul]; rw [← pairing]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [coxeterWeight]
  ring

/--
lemma `prod_rootForm_smul_coroot_mem_range_domRestrict` / 引理 `prod_rootForm_smul_coroot_mem_range_domRestrict`

English:
lemma prod_rootForm_smul_coroot_mem_range_domRestrict
  given: (i : ι)
  proof: by
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun a => P.RootForm (P.root a) (P.root a))
    (Finset.mem_univ i)
  rw [hc]; rw [mul_comm]; rw [mul_smul]; rw [rootForm_self_smul_coroot]
  refine LinearMap.mem_range.mpr ?_
  use ⟨c • 2 • P.root i, by aesop⟩
  simp

中文:
引理 prod_rootForm_smul_coroot_mem_range_domRestrict
  条件: (i : ι)
  证明: by
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun a => P.RootForm (P.root a) (P.root a))
    (Finset.mem_univ i)
  rw [hc]; rw [mul_comm]; rw [mul_smul]; rw [rootForm_self_smul_coroot]
  refine LinearMap.mem_range.mpr ?_
  use ⟨c • 2 • P.root i, by aesop⟩
  simp

Depends on / 依赖: Finset, Finset.dvd_prod_of_mem, Finset.mem_univ, LinearMap, LinearMap.mem_range.mpr, P.RootForm, P.root, RootForm, dvd_prod_of_mem, mem_range, mem_univ, mul_comm, mul_smul, rootForm_self_smul_coroot
-/
lemma prod_rootForm_smul_coroot_mem_range_domRestrict (i : ι) :
    (∏ a : ι, P.RootForm (P.root a) (P.root a)) • P.coroot i in
      LinearMap.range (P.Polarization.domRestrict (P.rootSpan R)) := by
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun a => P.RootForm (P.root a) (P.root a))
    (Finset.mem_univ i)
  rw [hc]; rw [mul_comm]; rw [mul_smul]; rw [rootForm_self_smul_coroot]
  refine LinearMap.mem_range.mpr ?_
  use ⟨c • 2 • P.root i, by aesop⟩
  simp

end MoreFintype

section IsValuedInOrdered

variable (S : Type*) [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
  [Algebra S R] [FaithfulSMul S R] [Module S M]
  [IsScalarTower S R M] [P.IsValuedIn S] [Fintype ι] {i j : ι}

/--
Definition of `posRootForm` / `posRootForm` 的定义

English:
definition posRootForm
  signature: : P.RootPositiveForm S where
  body: P.RootForm
  symm := P.rootForm_symmetric
  isOrthogonal_reflection := P.rootForm_reflection_reflection_apply
  exists_eq i j := ⟨∑ k, P.pairingIn S i k * P.pairingIn S j k, by simp [rootForm_apply_apply]⟩
  exists_pos_eq i := by
    refine ⟨∑ k, P.pairingIn S i k ^ 2, ?_, by simp [sq, rootForm_appl

中文:
定义 posRootForm
  签名: : P.RootPositiveForm S where
  定义体: P.RootForm
  symm := P.rootForm_symmetric
  isOrthogonal_reflection := P.rootForm_reflection_reflection_apply
  exists_eq i j := ⟨∑ k, P.pairingIn S i k * P.pairingIn S j k, by simp [rootForm_apply_apply]⟩
  exists_pos_eq i := by
    refine ⟨∑ k, P.pairingIn S i k ^ 2, ?_, by simp [sq, rootForm_appl

Depends on / 依赖: P.RootForm, RootForm
-/
def posRootForm : P.RootPositiveForm S where
  form := P.RootForm
  symm := P.rootForm_symmetric
  isOrthogonal_reflection := P.rootForm_reflection_reflection_apply
  exists_eq i j := ⟨∑ k, P.pairingIn S i k * P.pairingIn S j k, by simp [rootForm_apply_apply]⟩
  exists_pos_eq i := by
    refine ⟨∑ k, P.pairingIn S i k ^ 2, ?_, by simp [sq, rootForm_apply_apply]⟩
    exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, by simp⟩

/--
lemma `algebraMap_posRootForm_posForm` / 引理 `algebraMap_posRootForm_posForm`

English:
lemma algebraMap_posRootForm_posForm
  given: (x y : span S (range P.root))
  proof: by
  simp [posRootForm]

@[simp]

中文:
引理 algebraMap_posRootForm_posForm
  条件: (x y : span S (range P.root))
  证明: by
  simp [posRootForm]

@[simp]

Depends on / 依赖: posRootForm
-/
lemma algebraMap_posRootForm_posForm (x y : span S (range P.root)) :
    (algebraMap S R) ((P.posRootForm S).posForm x y) = P.RootForm x y := by
  simp [posRootForm]

@[simp]
/--
lemma `posRootForm_eq` / 引理 `posRootForm_eq`

English:
lemma posRootForm_eq
  proof: by
  ext
  apply FaithfulSMul.algebraMap_injective S R
  simp only [algebraMap_posRootForm_posForm, algebraMap_rootFormIn]

中文:
引理 posRootForm_eq
  证明: by
  ext
  apply FaithfulSMul.algebraMap_injective S R
  simp only [algebraMap_posRootForm_posForm, algebraMap_rootFormIn]

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, algebraMap_posRootForm_posForm, algebraMap_rootFormIn
-/
lemma posRootForm_eq :
    (P.posRootForm S).posForm = P.RootFormIn S := by
  ext
  apply FaithfulSMul.algebraMap_injective S R
  simp only [algebraMap_posRootForm_posForm, algebraMap_rootFormIn]

/--
theorem `exists_ge_zero_eq_rootForm` / 定理 `exists_ge_zero_eq_rootForm`

English:
theorem exists_ge_zero_eq_rootForm
  given: (x : M) (hx : x in span S (range P.root))
  proof: by
  refine ⟨(P.posRootForm S).posForm ⟨x, hx⟩ ⟨x, hx⟩, IsSumSq.nonneg ?_, by simp [posRootForm]⟩
  choose s hs using P.coroot'_apply_apply_mem_of_mem_span S hx
  suffices (P.posRootForm S).posForm ⟨x, hx⟩ ⟨x, hx⟩ = ∑ i, s i * s i from
    this ▸ IsSumSq.sum_mul_self Finset.univ s
  apply FaithfulSM

中文:
定理 exists_ge_zero_eq_rootForm
  条件: (x : M) (hx : x in span S (range P.root))
  证明: by
  refine ⟨(P.posRootForm S).posForm ⟨x, hx⟩ ⟨x, hx⟩, IsSumSq.nonneg ?_, by simp [posRootForm]⟩
  choose s hs using P.coroot'_apply_apply_mem_of_mem_span S hx
  suffices (P.posRootForm S).posForm ⟨x, hx⟩ ⟨x, hx⟩ = ∑ i, s i * s i from
    this ▸ IsSumSq.sum_mul_self Finset.univ s
  apply FaithfulSM

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, Finset, Finset.univ, IsSumSq, IsSumSq.nonneg, IsSumSq.sum_mul_self, P.coroot, P.posRootForm, RootPositiveForm, RootPositiveForm.algebraMap_posForm, _apply_apply_mem_of_mem_span, algebraMap_injective, algebraMap_posForm, coroot, map_mul, map_sum, nonneg, posForm, posRootForm
-/
theorem exists_ge_zero_eq_rootForm (x : M) (hx : x in span S (range P.root)) :
    exists s >= 0, algebraMap S R s = P.RootForm x x := by
  refine ⟨(P.posRootForm S).posForm ⟨x, hx⟩ ⟨x, hx⟩, IsSumSq.nonneg ?_, by simp [posRootForm]⟩
  choose s hs using P.coroot'_apply_apply_mem_of_mem_span S hx
  suffices (P.posRootForm S).posForm ⟨x, hx⟩ ⟨x, hx⟩ = ∑ i, s i * s i from
    this ▸ IsSumSq.sum_mul_self Finset.univ s
  apply FaithfulSMul.algebraMap_injective S R
  simp only [posRootForm, RootPositiveForm.algebraMap_posForm, map_sum, map_mul]
  simp [hs, rootForm_apply_apply]

/--
lemma `posRootForm_posForm_apply_apply` / 引理 `posRootForm_posForm_apply_apply`

English:
lemma posRootForm_posForm_apply_apply
  given: (x y : P.rootSpan S)
  statement: (P.posRootForm S).posForm x y =
  proof: by
  refine (FaithfulSMul.algebraMap_injective S R) ?_
  simp [posRootForm, rootForm_apply_apply]

中文:
引理 posRootForm_posForm_apply_apply
  条件: (x y : P.rootSpan S)
  结论: (P.posRootForm S).posForm x y =
  证明: by
  refine (FaithfulSMul.algebraMap_injective S R) ?_
  simp [posRootForm, rootForm_apply_apply]

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, posRootForm, rootForm_apply_apply
-/
lemma posRootForm_posForm_apply_apply (x y : P.rootSpan S) : (P.posRootForm S).posForm x y =
    ∑ i, P.coroot'In S i x * P.coroot'In S i y := by
  refine (FaithfulSMul.algebraMap_injective S R) ?_
  simp [posRootForm, rootForm_apply_apply]

/--
lemma `zero_le_posForm` / 引理 `zero_le_posForm`

English:
lemma zero_le_posForm
  given: (x : span S (range P.root))
  proof: by
  obtain ⟨s, _, hs⟩ := P.exists_ge_zero_eq_rootForm S x.1 x.2
  have : s = (P.posRootForm S).posForm x x :=
FaithfulSMul.algebraMap_injective S R (P.algebraMap_posRootForm_posForm S x x) ▸ hs
  rwa [← this]

omit [Fintype ι]

中文:
引理 zero_le_posForm
  条件: (x : span S (range P.root))
  证明: by
  obtain ⟨s, _, hs⟩ := P.exists_ge_zero_eq_rootForm S x.1 x.2
  have : s = (P.posRootForm S).posForm x x :=
FaithfulSMul.algebraMap_injective S R (P.algebraMap_posRootForm_posForm S x x) ▸ hs
  rwa [← this]

omit [Fintype ι]

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, P.algebraMap_posRootForm_posForm, P.exists_ge_zero_eq_rootForm, P.posRootForm, algebraMap_injective, algebraMap_posRootForm_posForm, exists_ge_zero_eq_rootForm, posForm, posRootForm
-/
lemma zero_le_posForm (x : span S (range P.root)) :
    0 <= (P.posRootForm S).posForm x x := by
  obtain ⟨s, _, hs⟩ := P.exists_ge_zero_eq_rootForm S x.1 x.2
  have : s = (P.posRootForm S).posForm x x :=
FaithfulSMul.algebraMap_injective S R (P.algebraMap_posRootForm_posForm S x x) ▸ hs
  rwa [← this]

omit [Fintype ι]
variable [Finite ι]

/--
lemma `zero_lt_pairingIn_iff'` / 引理 `zero_lt_pairingIn_iff'`

English:
lemma zero_lt_pairingIn_iff'
  proof: let _i : Fintype ι := Fintype.ofFinite ι
  zero_lt_pairingIn_iff (P.posRootForm S) i j

中文:
引理 zero_lt_pairingIn_iff'
  证明: let _i : Fintype ι := Fintype.ofFinite ι
  zero_lt_pairingIn_iff (P.posRootForm S) i j

Depends on / 依赖: Fintype, Fintype.ofFinite, P.posRootForm, ofFinite, posRootForm, zero_lt_pairingIn_iff
-/
lemma zero_lt_pairingIn_iff' :
    0 < P.pairingIn S i j ↔ 0 < P.pairingIn S j i :=
  let _i : Fintype ι := Fintype.ofFinite ι
  zero_lt_pairingIn_iff (P.posRootForm S) i j

/--
lemma `pairingIn_lt_zero_iff` / 引理 `pairingIn_lt_zero_iff`

English:
lemma pairingIn_lt_zero_iff
  proof: by
  simpa using P.zero_lt_pairingIn_iff' S (i := i) (j := P.reflectionPerm j j)

中文:
引理 pairingIn_lt_zero_iff
  证明: by
  simpa using P.zero_lt_pairingIn_iff' S (i := i) (j := P.reflectionPerm j j)

Depends on / 依赖: P.reflectionPerm, P.zero_lt_pairingIn_iff, reflectionPerm, zero_lt_pairingIn_iff
-/
lemma pairingIn_lt_zero_iff :
    P.pairingIn S i j < 0 ↔ P.pairingIn S j i < 0 := by
  simpa using P.zero_lt_pairingIn_iff' S (i := i) (j := P.reflectionPerm j j)

/--
lemma `pairingIn_le_zero_iff` / 引理 `pairingIn_le_zero_iff`

English:
lemma pairingIn_le_zero_iff
  given: [NeZero (2 : R)] [IsDomain R] [Module.IsTorsionFree R M]
  proof: by
  rcases eq_or_ne (P.pairingIn S i j) 0 with hij | hij <;>
  rcases eq_or_ne (P.pairingIn S j i) 0 with hji | hji
  · rw [hij, hji]
  · rw [hij, P.pairingIn_eq_zero_iff.mp hij]
  · rw [hji, P.pairingIn_eq_zero_iff.mp hji]
  · rw [le_iff_eq_or_lt, le_iff_eq_or_lt, or_iff_right hij, or_iff_right hj

中文:
引理 pairingIn_le_zero_iff
  条件: [NeZero (2 : R)] [IsDomain R] [Module.IsTorsionFree R M]
  证明: by
  rcases eq_or_ne (P.pairingIn S i j) 0 with hij | hij <;>
  rcases eq_or_ne (P.pairingIn S j i) 0 with hji | hji
  · rw [hij, hji]
  · rw [hij, P.pairingIn_eq_zero_iff.mp hij]
  · rw [hji, P.pairingIn_eq_zero_iff.mp hji]
  · rw [le_iff_eq_or_lt, le_iff_eq_or_lt, or_iff_right hij, or_iff_right hj

Depends on / 依赖: P.pairingIn, P.pairingIn_eq_zero_iff.mp, P.pairingIn_lt_zero_iff, eq_or_ne, le_iff_eq_or_lt, or_iff_right, pairingIn, pairingIn_eq_zero_iff, pairingIn_lt_zero_iff
-/
lemma pairingIn_le_zero_iff [NeZero (2 : R)] [IsDomain R] [Module.IsTorsionFree R M] :
    P.pairingIn S i j <= 0 ↔ P.pairingIn S j i <= 0 := by
  rcases eq_or_ne (P.pairingIn S i j) 0 with hij | hij <;>
  rcases eq_or_ne (P.pairingIn S j i) 0 with hji | hji
  · rw [hij, hji]
  · rw [hij, P.pairingIn_eq_zero_iff.mp hij]
  · rw [hji, P.pairingIn_eq_zero_iff.mp hji]
  · rw [le_iff_eq_or_lt, le_iff_eq_or_lt, or_iff_right hij, or_iff_right hji]
    exact P.pairingIn_lt_zero_iff S

end IsValuedInOrdered

end RootPairing
