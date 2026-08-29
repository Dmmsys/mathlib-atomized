/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.LinearAlgebra.RootSystem.IsValuedIn

/-!
# Invariant and root-positive bilinear forms on root pairings

This file contains basic results on Weyl-invariant inner products for root systems and root data.
Given a root pairing we define a structure which contains a bilinear form together with axioms for
reflection-invariance, symmetry, and strict positivity on all roots. We show that root-positive
forms display the same sign behavior as the canonical pairing between roots and coroots.

Root-positive forms show up naturally as the invariant forms for symmetrizable Kac-Moody Lie
algebras. In the finite case, the canonical polarization yields a root-positive form that is
positive semi-definite on weight space and positive-definite on the span of roots.

## Main definitions / results:

* `RootPairing.InvariantForm`: an invariant bilinear form on a root pairing.
* `RootPairing.RootPositiveForm`: Given a root pairing this is a structure which contains a
  bilinear form together with axioms for reflection-invariance, symmetry, and strict positivity on
  all roots.
* `RootPairing.zero_lt_pairingIn_iff`: sign relations between `RootPairing.pairingIn` and a
  root-positive form.
* `RootPairing.pairing_eq_zero_iff`: symmetric vanishing condition for `RootPairing.pairing`
* `RootPairing.coxeterWeight_nonneg`: All pairs of roots have non-negative Coxeter weight.
* `RootPairing.coxeterWeight_zero_iff_isOrthogonal` : A Coxeter weight vanishes iff the roots are
  orthogonal.

-/

@[expose] public section

noncomputable section

open FaithfulSMul Function Set Submodule

variable {ι R S M N : Type*} [CommRing S] [LinearOrder S]
  [CommRing R] [Algebra S R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing

/--
Definition of `InvariantForm` / `InvariantForm` 的定义

English:
structure InvariantForm
  parameters: (P : RootPairing ι R M N)
  axioms and operations (4):
    - form : LinearMap.BilinForm R M
    - symm : form.IsSymm
    - ne_zero((i : ι)) : form (P.root i) (P.root i) != 0
    - isOrthogonal_reflection((i : ι)) : form.IsOrthogonal (P.reflection i)

中文:
结构 不变形式
  参数: (P : RootPairing ι R M N)
  公理与运算 (4 个):
    - form : 线性映射.BilinForm R M
    - symm : form.是Symm
    - ne_zero((i : ι)) : form (P.root i) (P.root i) != 0
    - isOrthogonal_reflection((i : ι)) : form.IsOrthogonal (P.reflection i)
-/
structure InvariantForm (P : RootPairing ι R M N) where
  /-- The bilinear form bundled inside an `InvariantForm`. -/
  form : LinearMap.BilinForm R M
  symm : form.IsSymm
  ne_zero (i : ι) : form (P.root i) (P.root i) != 0
  isOrthogonal_reflection (i : ι) : form.IsOrthogonal (P.reflection i)

namespace InvariantForm

variable {P : RootPairing ι R M N} (B : P.InvariantForm) (i j : ι)

/--
lemma `apply_root_ne_zero` / 引理 `apply_root_ne_zero`

English:
lemma apply_root_ne_zero
  statement: B.form (P.root i) != 0
  proof: fun contra => B.ne_zero i by simp [contra]

中文:
引理 apply_root_ne_zero
  结论: B.form (P.root i) != 0
  证明: fun contra => B.ne_zero i by simp [contra]

Depends on / 依赖: B.ne_zero, contra, ne_zero
-/
lemma apply_root_ne_zero : B.form (P.root i) != 0 :=
fun contra => B.ne_zero i by simp [contra]

/--
lemma `two_mul_apply_root_root` / 引理 `two_mul_apply_root_root`

English:
lemma two_mul_apply_root_root
  proof: by
  rw [two_mul]; rw [← eq_sub_iff_add_eq]
  nth_rw 1 [← B.isOrthogonal_reflection j]
  rw [reflection_apply]; rw [reflection_apply_self]; rw [root_coroot'_eq_pairing]; rw [LinearMap.map_sub₂]; rw [LinearMap.map_smul₂]; rw [smul_eq_mul]; rw [map_neg]; rw [map_neg]; rw [mul_neg]; rw [neg_sub_neg]

中文:
引理 two_mul_apply_root_root
  证明: by
  rw [two_mul]; rw [← eq_sub_iff_add_eq]
  nth_rw 1 [← B.isOrthogonal_reflection j]
  rw [reflection_apply]; rw [reflection_apply_self]; rw [root_coroot'_eq_pairing]; rw [LinearMap.map_sub₂]; rw [LinearMap.map_smul₂]; rw [smul_eq_mul]; rw [map_neg]; rw [map_neg]; rw [mul_neg]; rw [neg_sub_neg]

Depends on / 依赖: B.isOrthogonal_reflection, LinearMap, LinearMap.map_smul, LinearMap.map_sub, _eq_pairing, eq_sub_iff_add_eq, isOrthogonal_reflection, map_neg, mul_neg, neg_sub_neg, nth_rw, reflection_apply, reflection_apply_self, root_coroot, smul_eq_mul, two_mul
-/
lemma two_mul_apply_root_root :
    2 * B.form (P.root i) (P.root j) = P.pairing i j * B.form (P.root j) (P.root j) := by
  rw [two_mul]; rw [← eq_sub_iff_add_eq]
  nth_rw 1 [← B.isOrthogonal_reflection j]
  rw [reflection_apply]; rw [reflection_apply_self]; rw [root_coroot'_eq_pairing]; rw [LinearMap.map_sub₂]; rw [LinearMap.map_smul₂]; rw [smul_eq_mul]; rw [map_neg]; rw [map_neg]; rw [mul_neg]; rw [neg_sub_neg]

/--
lemma `pairing_mul_eq_pairing_mul_swap` / 引理 `pairing_mul_eq_pairing_mul_swap`

English:
lemma pairing_mul_eq_pairing_mul_swap
  proof: by
  rw [← B.two_mul_apply_root_root i j]; rw [← B.two_mul_apply_root_root j i]; rw [← B.symm.eq]; rw [RingHom.id_apply]

@[simp]

中文:
引理 pairing_mul_eq_pairing_mul_swap
  证明: by
  rw [← B.two_mul_apply_root_root i j]; rw [← B.two_mul_apply_root_root j i]; rw [← B.symm.eq]; rw [RingHom.id_apply]

@[simp]

Depends on / 依赖: B.symm.eq, B.two_mul_apply_root_root, RingHom, RingHom.id_apply, id_apply, two_mul_apply_root_root
-/
lemma pairing_mul_eq_pairing_mul_swap :
    P.pairing j i * B.form (P.root i) (P.root i) =
    P.pairing i j * B.form (P.root j) (P.root j) := by
  rw [← B.two_mul_apply_root_root i j]; rw [← B.two_mul_apply_root_root j i]; rw [← B.symm.eq]; rw [RingHom.id_apply]

@[simp]
/--
lemma `apply_reflection_reflection` / 引理 `apply_reflection_reflection`

English:
lemma apply_reflection_reflection
  given: (x y : M)
  proof: B.isOrthogonal_reflection i x y

@[simp]

中文:
引理 apply_reflection_reflection
  条件: (x y : M)
  证明: B.isOrthogonal_reflection i x y

@[simp]

Depends on / 依赖: B.isOrthogonal_reflection, isOrthogonal_reflection
-/
lemma apply_reflection_reflection (x y : M) :
    B.form (P.reflection i x) (P.reflection i y) = B.form x y :=
  B.isOrthogonal_reflection i x y

@[simp]
/--
lemma `apply_root_root_zero_iff` / 引理 `apply_root_root_zero_iff`

English:
lemma apply_root_root_zero_iff
  given: [IsDomain R] [NeZero (2 : R)]
  proof: by
  calc B.form (P.root i) (P.root j) = 0
      ↔ 2 * B.form (P.root i) (P.root j) = 0 := by simp [two_ne_zero]
    _ ↔ P.pairing i j * B.form (P.root j) (P.root j) = 0 := by rw [B.two_mul_apply_root_root i j]
    _ ↔ P.pairing i j = 0 := by simp [B.ne_zero j]

中文:
引理 apply_root_root_zero_iff
  条件: [是整环 R] [NeZero (2 : R)]
  证明: by
  calc B.form (P.root i) (P.root j) = 0
      ↔ 2 * B.form (P.root i) (P.root j) = 0 := by simp [two_ne_zero]
    _ ↔ P.pairing i j * B.form (P.root j) (P.root j) = 0 := by rw [B.two_mul_apply_root_root i j]
    _ ↔ P.pairing i j = 0 := by simp [B.ne_zero j]

Depends on / 依赖: B.form, B.ne_zero, B.two_mul_apply_root_root, P.pairing, P.root, ne_zero, pairing, two_mul_apply_root_root, two_ne_zero
-/
lemma apply_root_root_zero_iff [IsDomain R] [NeZero (2 : R)] :
    B.form (P.root i) (P.root j) = 0 ↔ P.pairing i j = 0 := by
  calc B.form (P.root i) (P.root j) = 0
      ↔ 2 * B.form (P.root i) (P.root j) = 0 := by simp [two_ne_zero]
    _ ↔ P.pairing i j * B.form (P.root j) (P.root j) = 0 := by rw [B.two_mul_apply_root_root i j]
    _ ↔ P.pairing i j = 0 := by simp [B.ne_zero j]

end InvariantForm

variable (S) in
/--
Definition of `RootPositiveForm` / `RootPositiveForm` 的定义

English:
structure RootPositiveForm
  parameters: (P : RootPairing ι R M N) [P.IsValuedIn S]
  axioms and operations (5):
    - form : LinearMap.BilinForm R M
    - symm : form.IsSymm
    - isOrthogonal_reflection((i : ι)) : form.IsOrthogonal (P.reflection i)
    - exists_eq((i j : ι)) : exists s, algebraMap S R s = form (P.root i) (P.root j)
    - exists_pos_eq((i : ι)) : exists s > 0, algebraMap S R s = form (P.root i) (P.root i)

中文:
结构 RootPositiveForm
  参数: (P : RootPairing ι R M N) [P.是ValuedIn S]
  公理与运算 (5 个):
    - form : 线性映射.BilinForm R M
    - symm : form.是Symm
    - isOrthogonal_reflection((i : ι)) : form.IsOrthogonal (P.reflection i)
    - exists_eq((i j : ι)) : 存在 s, algebraMap S R s = form (P.root i) (P.root j)
    - exists_pos_eq((i : ι)) : 存在 s > 0, algebraMap S R s = form (P.root i) (P.root i)
-/
structure RootPositiveForm (P : RootPairing ι R M N) [P.IsValuedIn S] where
  /-- The bilinear form bundled inside a `RootPositiveForm`. -/
  form : LinearMap.BilinForm R M
  symm : form.IsSymm
  isOrthogonal_reflection (i : ι) : form.IsOrthogonal (P.reflection i)
  exists_eq (i j : ι) : exists s, algebraMap S R s = form (P.root i) (P.root j)
  exists_pos_eq (i : ι) : exists s > 0, algebraMap S R s = form (P.root i) (P.root i)

variable {P : RootPairing ι R M N} [P.IsValuedIn S] (B : P.RootPositiveForm S) (i j : ι)
  [FaithfulSMul S R] [Module S M] [IsScalarTower S R M]

namespace RootPositiveForm

omit [Module S M] [IsScalarTower S R M] in
/--
lemma `form_apply_root_ne_zero` / 引理 `form_apply_root_ne_zero`

English:
lemma form_apply_root_ne_zero
  given: (i : ι)
  proof: by
  obtain ⟨s, hs, hs'⟩ := B.exists_pos_eq i
  simpa [← hs'] using hs.ne'

中文:
引理 form_apply_root_ne_zero
  条件: (i : ι)
  证明: by
  obtain ⟨s, hs, hs'⟩ := B.exists_pos_eq i
  simpa [← hs'] using hs.ne'

Depends on / 依赖: B.exists_pos_eq, exists_pos_eq, hs.ne
-/
lemma form_apply_root_ne_zero (i : ι) :
    B.form (P.root i) (P.root i) != 0 := by
  obtain ⟨s, hs, hs'⟩ := B.exists_pos_eq i
  simpa [← hs'] using hs.ne'

/--
Definition of `toInvariantForm` / `toInvariantForm` 的定义

English:
definition toInvariantForm
  signature: : InvariantForm P where
  body: B.form
  symm := B.symm
  ne_zero := B.form_apply_root_ne_zero
  isOrthogonal_reflection := B.isOrthogonal_reflection

omit [Module S M] [IsScalarTower S R M] in

中文:
定义 toInvariantForm
  签名: : 不变形式 P where
  定义体: B.form
  symm := B.symm
  ne_zero := B.form_apply_root_ne_zero
  isOrthogonal_reflection := B.isOrthogonal_reflection

omit [Module S M] [IsScalarTower S R M] in
-/
@[simps] def toInvariantForm : InvariantForm P where
  form := B.form
  symm := B.symm
  ne_zero := B.form_apply_root_ne_zero
  isOrthogonal_reflection := B.isOrthogonal_reflection

omit [Module S M] [IsScalarTower S R M] in
/--
lemma `two_mul_apply_root_root` / 引理 `two_mul_apply_root_root`

English:
lemma two_mul_apply_root_root
  proof: B.toInvariantForm.two_mul_apply_root_root i j

中文:
引理 two_mul_apply_root_root
  证明: B.toInvariantForm.two_mul_apply_root_root i j

Depends on / 依赖: B.toInvariantForm.two_mul_apply_root_root, toInvariantForm, two_mul_apply_root_root
-/
lemma two_mul_apply_root_root :
    2 * B.form (P.root i) (P.root j) = P.pairing i j * B.form (P.root j) (P.root j) :=
  B.toInvariantForm.two_mul_apply_root_root i j

/--
Definition of `posForm` / `posForm` 的定义

English:
definition posForm
  signature: :
  body: LinearMap.restrictScalarsRange₂ (span S (range P.root)).subtype (span S (range P.root)).subtype
  (Algebra.linearMap S R) (FaithfulSMul.algebraMap_injective S R) B.form
  (fun ⟨x, hx⟩ ⟨y, hy⟩ => by
    apply LinearMap.BilinMap.apply_apply_mem_of_mem_span
      (s := range P.root) (t := range P.root)
      (B := (LinearMap.restrictScalarsₗ S R _ _ _).comp (B.form.restrictScalars S))
    · rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
      simpa using B.exists_eq i j
    · simpa
    · simpa)

中文:
定义 posForm
  签名: :
  定义体: LinearMap.restrictScalarsRange₂ (span S (range P.root)).subtype (span S (range P.root)).subtype
  (Algebra.linearMap S R) (FaithfulSMul.algebraMap_injective S R) B.form
  (fun ⟨x, hx⟩ ⟨y, hy⟩ => by
    apply LinearMap.BilinMap.apply_apply_mem_of_mem_span
      (s := range P.root) (t := range P.root)
      (B := (LinearMap.restrictScalarsₗ S R _ _ _).comp (B.form.restrictScalars S))
    · rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
      simpa using B.exists_eq i j
    · simpa
    · simpa)

Depends on / 依赖: Algebra, Algebra.linearMap, B.exists_eq, B.form, B.form.restrictScalars, BilinMap, FaithfulSMul, FaithfulSMul.algebraMap_injective, LinearMap, LinearMap.BilinMap.apply_apply_mem_of_mem_span, LinearMap.restrictScalars, LinearMap.restrictScalarsRange, P.root, algebraMap_injective, apply_apply_mem_of_mem_span, exists_eq, linearMap, restrictScalars, subtype
-/
def posForm :
    LinearMap.BilinForm S (span S (range P.root)) :=
  LinearMap.restrictScalarsRange₂ (span S (range P.root)).subtype (span S (range P.root)).subtype
  (Algebra.linearMap S R) (FaithfulSMul.algebraMap_injective S R) B.form
  (fun ⟨x, hx⟩ ⟨y, hy⟩ => by
    apply LinearMap.BilinMap.apply_apply_mem_of_mem_span
      (s := range P.root) (t := range P.root)
      (B := (LinearMap.restrictScalarsₗ S R _ _ _).comp (B.form.restrictScalars S))
    · rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
      simpa using B.exists_eq i j
    · simpa
    · simpa)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `algebraMap_posForm` / 引理 `algebraMap_posForm`

English:
lemma algebraMap_posForm
  given: {x y : span S (range P.root)}
  proof: by
  change Algebra.linearMap S R _ = _
  simp [posForm]

中文:
引理 algebraMap_posForm
  条件: {x y : span S (range P.root)}
  证明: by
  change Algebra.linearMap S R _ = _
  simp [posForm]
-/
@[simp] lemma algebraMap_posForm {x y : span S (range P.root)} :
    algebraMap S R (B.posForm x y) = B.form x y := by
  change Algebra.linearMap S R _ = _
  simp [posForm]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `algebraMap_apply_eq_form_iff` / 引理 `algebraMap_apply_eq_form_iff`

English:
lemma algebraMap_apply_eq_form_iff
  given: {x y : span S (range P.root)} {s : S}
  proof: by
  simp [RootPositiveForm.posForm]

中文:
引理 algebraMap_apply_eq_form_iff
  条件: {x y : span S (range P.root)} {s : S}
  证明: by
  simp [RootPositiveForm.posForm]

Depends on / 依赖: RootPositiveForm, RootPositiveForm.posForm, posForm
-/
lemma algebraMap_apply_eq_form_iff {x y : span S (range P.root)} {s : S} :
    algebraMap S R s = B.form x y ↔ s = B.posForm x y := by
  simp [RootPositiveForm.posForm]

/--
lemma `zero_lt_posForm_iff` / 引理 `zero_lt_posForm_iff`

English:
lemma zero_lt_posForm_iff
  given: {x y : span S (range P.root)}
  proof: by
  refine ⟨fun h => ⟨B.posForm x y, h, by simp⟩, fun ⟨s, h, h'⟩ => ?_⟩
  rw [← B.algebraMap_posForm] at h'
  rwa [← FaithfulSMul.algebraMap_injective S R h']

中文:
引理 zero_lt_posForm_iff
  条件: {x y : span S (range P.root)}
  证明: by
  refine ⟨fun h => ⟨B.posForm x y, h, by simp⟩, fun ⟨s, h, h'⟩ => ?_⟩
  rw [← B.algebraMap_posForm] at h'
  rwa [← FaithfulSMul.algebraMap_injective S R h']

Depends on / 依赖: B.algebraMap_posForm, B.posForm, FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, algebraMap_posForm, posForm
-/
lemma zero_lt_posForm_iff {x y : span S (range P.root)} :
    0 < B.posForm x y ↔ exists s > 0, algebraMap S R s = B.form x y := by
  refine ⟨fun h => ⟨B.posForm x y, h, by simp⟩, fun ⟨s, h, h'⟩ => ?_⟩
  rw [← B.algebraMap_posForm] at h'
  rwa [← FaithfulSMul.algebraMap_injective S R h']

/--
lemma `zero_lt_posForm_apply_root` / 引理 `zero_lt_posForm_apply_root`

English:
lemma zero_lt_posForm_apply_root
  statement: (i : ι)
  proof: by
  simpa only [zero_lt_posForm_iff] using B.exists_pos_eq i

中文:
引理 zero_lt_posForm_apply_root
  结论: (i : ι)
  证明: by
  simpa only [zero_lt_posForm_iff] using B.exists_pos_eq i

Depends on / 依赖: mem_range_self, subset_span
-/
lemma zero_lt_posForm_apply_root (i : ι)
    (hi : P.root i in span S (range P.root) := subset_span (mem_range_self i)) :
    0 < B.posForm ⟨P.root i, hi⟩ ⟨P.root i, hi⟩ := by
  simpa only [zero_lt_posForm_iff] using B.exists_pos_eq i

/--
lemma `isSymm_posForm` / 引理 `isSymm_posForm`

English:
lemma isSymm_posForm
  proof: by
    apply FaithfulSMul.algebraMap_injective S R
    simpa using B.symm.eq x y

中文:
引理 isSymm_posForm
  证明: by
    apply FaithfulSMul.algebraMap_injective S R
    simpa using B.symm.eq x y

Depends on / 依赖: B.symm.eq, FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective
-/
lemma isSymm_posForm :
    B.posForm.IsSymm where
  eq x y := by
    apply FaithfulSMul.algebraMap_injective S R
    simpa using B.symm.eq x y

/--
Definition of `rootLength` / `rootLength` 的定义

English:
definition rootLength
  signature: (i : ι)
  body: B.posForm (P.rootSpanMem S i) (P.rootSpanMem S i)

中文:
定义 rootLength
  签名: (i : ι)
  定义体: B.posForm (P.rootSpanMem S i) (P.rootSpanMem S i)

Depends on / 依赖: B.posForm, P.rootSpanMem, posForm, rootSpanMem
-/
def rootLength (i : ι) : S :=
  B.posForm (P.rootSpanMem S i) (P.rootSpanMem S i)

/--
lemma `rootLength_pos` / 引理 `rootLength_pos`

English:
lemma rootLength_pos
  given: (i : ι)
  statement: 0 < B.rootLength i
  proof: by
  simpa using! B.zero_lt_posForm_apply_root i

@[simp]

中文:
引理 rootLength_pos
  条件: (i : ι)
  结论: 0 < B.rootLength i
  证明: by
  simpa using! B.zero_lt_posForm_apply_root i

@[simp]

Depends on / 依赖: B.zero_lt_posForm_apply_root, zero_lt_posForm_apply_root
-/
lemma rootLength_pos (i : ι) : 0 < B.rootLength i := by
  simpa using! B.zero_lt_posForm_apply_root i

@[simp]
/--
lemma `rootLength_reflectionPerm_self` / 引理 `rootLength_reflectionPerm_self`

English:
lemma rootLength_reflectionPerm_self
  given: (i : ι)
  proof: by
  simp [rootLength, rootSpanMem_reflectionPerm_self]

中文:
引理 rootLength_reflectionPerm_self
  条件: (i : ι)
  证明: by
  simp [rootLength, rootSpanMem_reflectionPerm_self]

Depends on / 依赖: rootLength, rootSpanMem_reflectionPerm_self
-/
lemma rootLength_reflectionPerm_self (i : ι) :
    B.rootLength (P.reflectionPerm i i) = B.rootLength i := by
  simp [rootLength, rootSpanMem_reflectionPerm_self]

/--
lemma `algebraMap_rootLength` / 引理 `algebraMap_rootLength`

English:
lemma algebraMap_rootLength
  given: (i : ι)
  proof: by
  simp [rootLength]

中文:
引理 algebraMap_rootLength
  条件: (i : ι)
  证明: by
  simp [rootLength]
-/
@[simp] lemma algebraMap_rootLength (i : ι) :
    algebraMap S R (B.rootLength i) = B.form (P.root i) (P.root i) := by
  simp [rootLength]

/--
lemma `pairingIn_mul_eq_pairingIn_mul_swap` / 引理 `pairingIn_mul_eq_pairingIn_mul_swap`

English:
lemma pairingIn_mul_eq_pairingIn_mul_swap
  proof: by
  simpa only [← (algebraMap_injective S R).eq_iff, algebraMap_pairingIn, map_mul,
    B.algebraMap_rootLength] using! B.toInvariantForm.pairing_mul_eq_pairing_mul_swap i j

中文:
引理 pairingIn_mul_eq_pairingIn_mul_swap
  证明: by
  simpa only [← (algebraMap_injective S R).eq_iff, algebraMap_pairingIn, map_mul,
    B.algebraMap_rootLength] using! B.toInvariantForm.pairing_mul_eq_pairing_mul_swap i j

Depends on / 依赖: B.algebraMap_rootLength, B.toInvariantForm.pairing_mul_eq_pairing_mul_swap, algebraMap_injective, algebraMap_pairingIn, algebraMap_rootLength, eq_iff, map_mul, pairing_mul_eq_pairing_mul_swap, toInvariantForm
-/
lemma pairingIn_mul_eq_pairingIn_mul_swap :
    P.pairingIn S j i * B.rootLength i = P.pairingIn S i j * B.rootLength j := by
  simpa only [← (algebraMap_injective S R).eq_iff, algebraMap_pairingIn, map_mul,
    B.algebraMap_rootLength] using! B.toInvariantForm.pairing_mul_eq_pairing_mul_swap i j

set_option linter.style.whitespace false in -- manual alignment is not recognised
@[simp]
/--
lemma `zero_lt_apply_root_root_iff` / 引理 `zero_lt_apply_root_root_iff`

English:
lemma zero_lt_apply_root_root_iff
  statement: [IsStrictOrderedRing S]
  proof: by
  let ri : span S (range P.root) := ⟨P.root i, hi⟩
  let rj : span S (range P.root) := ⟨P.root j, hj⟩
  have : 2 * B.posForm ri rj = P.pairingIn S i j * B.posForm rj rj := by
    apply FaithfulSMul.algebraMap_injective S R
    simpa [map_ofNat] using B.toInvariantForm.two_mul_apply_root_root i j
  calc 0 < B.posForm ri rj
      ↔ 0 < 2 * B.posForm ri rj := by rw [mul_pos_iff_of_pos_left zero_lt_two]
    _ ↔ 0 < P.pairingIn S i j * B.posForm rj rj := by rw [this]
    _ ↔ 0 < P.pairingIn S i j := by rw [mul_pos_iff_of_pos_right (B.zero_lt_posForm_apply_root j)]

@[simp]

中文:
引理 zero_lt_apply_root_root_iff
  结论: [是StrictOrdered环 S]
  证明: by
  let ri : span S (range P.root) := ⟨P.root i, hi⟩
  let rj : span S (range P.root) := ⟨P.root j, hj⟩
  have : 2 * B.posForm ri rj = P.pairingIn S i j * B.posForm rj rj := by
    apply FaithfulSMul.algebraMap_injective S R
    simpa [map_ofNat] using B.toInvariantForm.two_mul_apply_root_root i j
  calc 0 < B.posForm ri rj
      ↔ 0 < 2 * B.posForm ri rj := by rw [mul_pos_iff_of_pos_left zero_lt_two]
    _ ↔ 0 < P.pairingIn S i j * B.posForm rj rj := by rw [this]
    _ ↔ 0 < P.pairingIn S i j := by rw [mul_pos_iff_of_pos_right (B.zero_lt_posForm_apply_root j)]

@[simp]

Depends on / 依赖: mem_range_self, subset_span
-/
lemma zero_lt_apply_root_root_iff [IsStrictOrderedRing S]
    (hi : P.root i in span S (range P.root) := subset_span (mem_range_self i))
    (hj : P.root j in span S (range P.root) := subset_span (mem_range_self j)) :
    0 < B.posForm ⟨P.root i, hi⟩ ⟨P.root j, hj⟩ ↔ 0 < P.pairingIn S i j := by
  let ri : span S (range P.root) := ⟨P.root i, hi⟩
  let rj : span S (range P.root) := ⟨P.root j, hj⟩
  have : 2 * B.posForm ri rj = P.pairingIn S i j * B.posForm rj rj := by
    apply FaithfulSMul.algebraMap_injective S R
    simpa [map_ofNat] using B.toInvariantForm.two_mul_apply_root_root i j
  calc 0 < B.posForm ri rj
      ↔ 0 < 2 * B.posForm ri rj := by rw [mul_pos_iff_of_pos_left zero_lt_two]
    _ ↔ 0 < P.pairingIn S i j * B.posForm rj rj := by rw [this]
    _ ↔ 0 < P.pairingIn S i j := by rw [mul_pos_iff_of_pos_right (B.zero_lt_posForm_apply_root j)]

@[simp]
/--
lemma `posForm_apply_root_root_le_zero_iff` / 引理 `posForm_apply_root_root_le_zero_iff`

English:
lemma posForm_apply_root_root_le_zero_iff
  statement: [IsStrictOrderedRing S]
  proof: by
  rw [← not_iff_not]; rw [not_le]; rw [not_le]; rw [zero_lt_apply_root_root_iff]

中文:
引理 posForm_apply_root_root_le_zero_iff
  结论: [是StrictOrdered环 S]
  证明: by
  rw [← not_iff_not]; rw [not_le]; rw [not_le]; rw [zero_lt_apply_root_root_iff]

Depends on / 依赖: mem_range_self, subset_span
-/
lemma posForm_apply_root_root_le_zero_iff [IsStrictOrderedRing S]
    (hi : P.root i in span S (range P.root) := subset_span (mem_range_self i))
    (hj : P.root j in span S (range P.root) := subset_span (mem_range_self j)) :
    B.posForm ⟨P.root i, hi⟩ ⟨P.root j, hj⟩ <= 0 ↔ P.pairingIn S i j <= 0 := by
  rw [← not_iff_not]; rw [not_le]; rw [not_le]; rw [zero_lt_apply_root_root_iff]

end RootPositiveForm

include B

/--
lemma `zero_lt_pairingIn_iff` / 引理 `zero_lt_pairingIn_iff`

English:
lemma zero_lt_pairingIn_iff
  given: [IsStrictOrderedRing S]
  proof: by
  rw [← B.zero_lt_apply_root_root_iff]; rw [← B.isSymm_posForm.eq]; rw [RingHom.id_apply]; rw [B.zero_lt_apply_root_root_iff]

中文:
引理 zero_lt_pairingIn_iff
  条件: [是StrictOrdered环 S]
  证明: by
  rw [← B.zero_lt_apply_root_root_iff]; rw [← B.isSymm_posForm.eq]; rw [RingHom.id_apply]; rw [B.zero_lt_apply_root_root_iff]

Depends on / 依赖: B.isSymm_posForm.eq, B.zero_lt_apply_root_root_iff, RingHom, RingHom.id_apply, id_apply, isSymm_posForm, zero_lt_apply_root_root_iff
-/
lemma zero_lt_pairingIn_iff [IsStrictOrderedRing S] :
    0 < P.pairingIn S i j ↔ 0 < P.pairingIn S j i := by
  rw [← B.zero_lt_apply_root_root_iff]; rw [← B.isSymm_posForm.eq]; rw [RingHom.id_apply]; rw [B.zero_lt_apply_root_root_iff]

/--
lemma `coxeterWeight_nonneg` / 引理 `coxeterWeight_nonneg`

English:
lemma coxeterWeight_nonneg
  given: [IsStrictOrderedRing S]
  statement: 0 <= P.coxeterWeightIn S i j
  proof: by
  dsimp [coxeterWeightIn]
  rcases lt_or_ge 0 (P.pairingIn S i j) with h | h
· exact le_of_lt mul_pos h ((zero_lt_pairingIn_iff B i j).mp h)
  · have hn : P.pairingIn S j i <= 0 := by rwa [← not_lt, ← zero_lt_pairingIn_iff B i j, not_lt]
    exact mul_nonneg_of_nonpos_of_nonpos h hn

中文:
引理 coxeterWeight_nonneg
  条件: [是StrictOrdered环 S]
  结论: 0 <= P.coxeterWeightIn S i j
  证明: by
  dsimp [coxeterWeightIn]
  rcases lt_or_ge 0 (P.pairingIn S i j) with h | h
· exact le_of_lt mul_pos h ((zero_lt_pairingIn_iff B i j).mp h)
  · have hn : P.pairingIn S j i <= 0 := by rwa [← not_lt, ← zero_lt_pairingIn_iff B i j, not_lt]
    exact mul_nonneg_of_nonpos_of_nonpos h hn

Depends on / 依赖: P.pairingIn, coxeterWeightIn, le_of_lt, lt_or_ge, mul_nonneg_of_nonpos_of_nonpos, mul_pos, not_lt, pairingIn, zero_lt_pairingIn_iff
-/
lemma coxeterWeight_nonneg [IsStrictOrderedRing S] : 0 <= P.coxeterWeightIn S i j := by
  dsimp [coxeterWeightIn]
  rcases lt_or_ge 0 (P.pairingIn S i j) with h | h
· exact le_of_lt mul_pos h ((zero_lt_pairingIn_iff B i j).mp h)
  · have hn : P.pairingIn S j i <= 0 := by rwa [← not_lt, ← zero_lt_pairingIn_iff B i j, not_lt]
    exact mul_nonneg_of_nonpos_of_nonpos h hn

end RootPairing
