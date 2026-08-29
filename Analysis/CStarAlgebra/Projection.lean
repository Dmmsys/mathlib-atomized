/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar, Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection

/-!

# Projections in C⋆-algebras

Here we collect results about projections specific to C⋆-algebras.

## Main results

+ `isStarProjection_iff_isIdempotentElem_and_isStarNormal`: star projections are precisely
  idempotent normal elements.
+ `IsStarProjection.le_tfae`: for star projections `p` and `q`, the following are equivalent:
  - `p ≤ q`
  - `q * p = p`
  - `p * q = p`
  - `q - p` is a star projection
  - `q - p` is an idempotent element

-/

public section

open scoped CStarAlgebra

section NonUnital
variable {A : Type*} [TopologicalSpace A] [NonUnitalRing A] [StarRing A]

/--
lemma `isStarProjection_iff_quasispectrum_subset_and_isSelfAdjoint` / 引理 `isStarProjection_iff_quasispectrum_subset_and_isSelfAdjoint`

English:
lemma isStarProjection_iff_quasispectrum_subset_and_isSelfAdjoint
  statement: [Module Real A] [IsScalarTower Real A A]
  proof: (isStarProjection_iff p).eq ▸
    and_congr_left_iff.mpr fun h => isIdempotentElem_iff_quasispectrum_subset Real p h

中文:
引理 isStarProjection_iff_quasispectrum_subset_and_isSelfAdjoint
  结论: [模 实数 A] [标量塔 实数 A A]
  证明: (isStarProjection_iff p).eq ▸
    and_congr_left_iff.mpr fun h => isIdempotentElem_iff_quasispectrum_subset Real p h

Depends on / 依赖: and_congr_left_iff, and_congr_left_iff.mpr, isIdempotentElem_iff_quasispectrum_subset, isStarProjection_iff
-/
lemma isStarProjection_iff_quasispectrum_subset_and_isSelfAdjoint [Module Real A] [IsScalarTower Real A A]
    [SMulCommClass Real A A] [NonUnitalContinuousFunctionalCalculus Real A IsSelfAdjoint] {p : A} :
    IsStarProjection p ↔ quasispectrum Real p subseteq {0, 1} ∧ IsSelfAdjoint p :=
  (isStarProjection_iff p).eq ▸
    and_congr_left_iff.mpr fun h => isIdempotentElem_iff_quasispectrum_subset Real p h

section Normal
variable [Module Complex A] [IsScalarTower Complex A A] [SMulCommClass Complex A A]
  [NonUnitalContinuousFunctionalCalculus Complex A IsStarNormal]

/--
theorem `IsIdempotentElem.isSelfAdjoint_iff_isStarNormal` / 定理 `IsIdempotentElem.isSelfAdjoint_iff_isStarNormal`

English:
theorem IsIdempotentElem.isSelfAdjoint_iff_isStarNormal
  given: {p : A} (hp : IsIdempotentElem p)
  proof: by
  simp only [isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts,
    QuasispectrumRestricts.real_iff, and_iff_left_iff_imp]
  intro h x hx
  rcases hp.quasispectrum_subset _ hx with (hx | hx) <;> simp [Set.mem_singleton_iff.mp hx]

中文:
定理 IsIdempotentElem.isSelfAdjoint_iff_isStarNormal
  条件: {p : A} (hp : IsIdempotentElem p)
  证明: by
  simp only [isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts,
    QuasispectrumRestricts.real_iff, and_iff_left_iff_imp]
  intro h x hx
  rcases hp.quasispectrum_subset _ hx with (hx | hx) <;> simp [Set.mem_singleton_iff.mp hx]

Depends on / 依赖: QuasispectrumRestricts, QuasispectrumRestricts.real_iff, Set.mem_singleton_iff.mp, and_iff_left_iff_imp, hp.quasispectrum_subset, isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts, mem_singleton_iff, quasispectrum_subset, real_iff
-/
theorem IsIdempotentElem.isSelfAdjoint_iff_isStarNormal {p : A} (hp : IsIdempotentElem p) :
    IsSelfAdjoint p ↔ IsStarNormal p := by
  simp only [isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts,
    QuasispectrumRestricts.real_iff, and_iff_left_iff_imp]
  intro h x hx
  rcases hp.quasispectrum_subset _ hx with (hx | hx) <;> simp [Set.mem_singleton_iff.mp hx]

/--
theorem `isStarProjection_iff_isIdempotentElem_and_isStarNormal` / 定理 `isStarProjection_iff_isIdempotentElem_and_isStarNormal`

English:
theorem isStarProjection_iff_isIdempotentElem_and_isStarNormal
  given: {p : A}
  proof: (isStarProjection_iff p).eq ▸ and_congr_right_iff.eq ▸ fun h => h.isSelfAdjoint_iff_isStarNormal

中文:
定理 isStarProjection_iff_isIdempotentElem_and_isStarNormal
  条件: {p : A}
  证明: (isStarProjection_iff p).eq ▸ and_congr_right_iff.eq ▸ fun h => h.isSelfAdjoint_iff_isStarNormal

Depends on / 依赖: and_congr_right_iff, and_congr_right_iff.eq, h.isSelfAdjoint_iff_isStarNormal, isSelfAdjoint_iff_isStarNormal, isStarProjection_iff
-/
theorem isStarProjection_iff_isIdempotentElem_and_isStarNormal {p : A} :
    IsStarProjection p ↔ IsIdempotentElem p ∧ IsStarNormal p :=
  (isStarProjection_iff p).eq ▸ and_congr_right_iff.eq ▸ fun h => h.isSelfAdjoint_iff_isStarNormal

/--
theorem `isStarProjection_iff_quasispectrum_subset_and_isStarNormal` / 定理 `isStarProjection_iff_quasispectrum_subset_and_isStarNormal`

English:
theorem isStarProjection_iff_quasispectrum_subset_and_isStarNormal
  given: {p : A}
  proof: isStarProjection_iff_isIdempotentElem_and_isStarNormal (p := p).eq ▸
    and_congr_left_iff.mpr fun h => isIdempotentElem_iff_quasispectrum_subset Complex p h

中文:
定理 isStarProjection_iff_quasispectrum_subset_and_isStarNormal
  条件: {p : A}
  证明: isStarProjection_iff_isIdempotentElem_and_isStarNormal (p := p).eq ▸
    and_congr_left_iff.mpr fun h => isIdempotentElem_iff_quasispectrum_subset Complex p h

Depends on / 依赖: and_congr_left_iff, and_congr_left_iff.mpr, isIdempotentElem_iff_quasispectrum_subset, isStarProjection_iff_isIdempotentElem_and_isStarNormal
-/
theorem isStarProjection_iff_quasispectrum_subset_and_isStarNormal {p : A} :
    IsStarProjection p ↔ quasispectrum Complex p subseteq {0, 1} ∧ IsStarNormal p :=
  isStarProjection_iff_isIdempotentElem_and_isStarNormal (p := p).eq ▸
    and_congr_left_iff.mpr fun h => isIdempotentElem_iff_quasispectrum_subset Complex p h

end Normal
end NonUnital

section Unital
variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A]

/--
lemma `isStarProjection_iff_spectrum_subset_and_isSelfAdjoint` / 引理 `isStarProjection_iff_spectrum_subset_and_isSelfAdjoint`

English:
lemma isStarProjection_iff_spectrum_subset_and_isSelfAdjoint
  statement: [Algebra Real A]
  proof: (isStarProjection_iff p).eq ▸
    and_congr_left_iff.mpr fun h => isIdempotentElem_iff_spectrum_subset Real p h

中文:
引理 isStarProjection_iff_spectrum_subset_and_isSelfAdjoint
  结论: [代数 实数 A]
  证明: (isStarProjection_iff p).eq ▸
    and_congr_left_iff.mpr fun h => isIdempotentElem_iff_spectrum_subset Real p h

Depends on / 依赖: and_congr_left_iff, and_congr_left_iff.mpr, isIdempotentElem_iff_spectrum_subset, isStarProjection_iff
-/
lemma isStarProjection_iff_spectrum_subset_and_isSelfAdjoint [Algebra Real A]
    [NonUnitalContinuousFunctionalCalculus Real A IsSelfAdjoint] {p : A} :
    IsStarProjection p ↔ spectrum Real p subseteq {0, 1} ∧ IsSelfAdjoint p :=
  (isStarProjection_iff p).eq ▸
    and_congr_left_iff.mpr fun h => isIdempotentElem_iff_spectrum_subset Real p h

/--
theorem `isStarProjection_iff_spectrum_subset_and_isStarNormal` / 定理 `isStarProjection_iff_spectrum_subset_and_isStarNormal`

English:
theorem isStarProjection_iff_spectrum_subset_and_isStarNormal
  statement: [Algebra Complex A]
  proof: isStarProjection_iff_isIdempotentElem_and_isStarNormal (p := p).eq ▸
    and_congr_left_iff.mpr fun h => isIdempotentElem_iff_spectrum_subset Complex p h

中文:
定理 isStarProjection_iff_spectrum_subset_and_isStarNormal
  结论: [代数 复形 A]
  证明: isStarProjection_iff_isIdempotentElem_and_isStarNormal (p := p).eq ▸
    and_congr_left_iff.mpr fun h => isIdempotentElem_iff_spectrum_subset Complex p h

Depends on / 依赖: and_congr_left_iff, and_congr_left_iff.mpr, isIdempotentElem_iff_spectrum_subset, isStarProjection_iff_isIdempotentElem_and_isStarNormal
-/
theorem isStarProjection_iff_spectrum_subset_and_isStarNormal [Algebra Complex A]
    [NonUnitalContinuousFunctionalCalculus Complex A IsStarNormal] {p : A} :
    IsStarProjection p ↔ spectrum Complex p subseteq {0, 1} ∧ IsStarNormal p :=
  isStarProjection_iff_isIdempotentElem_and_isStarNormal (p := p).eq ▸
    and_congr_left_iff.mpr fun h => isIdempotentElem_iff_spectrum_subset Complex p h

end Unital

namespace IsStarProjection

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {p q : A}

open CFC in
/--
lemma `le_tfae` / 引理 `le_tfae`

English:
lemma le_tfae
  given: (hp : IsStarProjection p) (hq : IsStarProjection q)
  proof: by
  tfae_have 1 -> 2 := fun h => (hq.mul_right_and_mul_left_of_nonneg_of_le hp.nonneg h).2
  tfae_have 2 -> 3 := fun h => by
    simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using congr(star $h)
  tfae_have 3 -> 4 := hp.sub_of_mul_eq_left hq
  tfae_have 4 -> 1 := fun h => by simpa using h.nonneg
  tfae_have 4 ↔ 5 := by simp [isStarProjection_iff, hq.isSelfAdjoint.sub hp.isSelfAdjoint]
  tfae_finish

中文:
引理 le_tfae
  条件: (hp : 是StarProjection p) (hq : 是StarProjection q)
  证明: by
  tfae_have 1 -> 2 := fun h => (hq.mul_right_and_mul_left_of_nonneg_of_le hp.nonneg h).2
  tfae_have 2 -> 3 := fun h => by
    simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using congr(star $h)
  tfae_have 3 -> 4 := hp.sub_of_mul_eq_left hq
  tfae_have 4 -> 1 := fun h => by simpa using h.nonneg
  tfae_have 4 ↔ 5 := by simp [isStarProjection_iff, hq.isSelfAdjoint.sub hp.isSelfAdjoint]
  tfae_finish

Depends on / 依赖: h.nonneg, hp.isSelfAdjoint, hp.isSelfAdjoint.star_eq, hp.nonneg, hp.sub_of_mul_eq_left, hq.isSelfAdjoint.star_eq, hq.isSelfAdjoint.sub, hq.mul_right_and_mul_left_of_nonneg_of_le, isSelfAdjoint, isStarProjection_iff, mul_right_and_mul_left_of_nonneg_of_le, nonneg, star_eq, sub_of_mul_eq_left, tfae_finish, tfae_have
-/
lemma le_tfae (hp : IsStarProjection p) (hq : IsStarProjection q) :
  List.TFAE
    [p <= q,
    q * p = p,
    p * q = p,
    IsStarProjection (q - p),
    IsIdempotentElem (q - p)] := by
  tfae_have 1 -> 2 := fun h => (hq.mul_right_and_mul_left_of_nonneg_of_le hp.nonneg h).2
  tfae_have 2 -> 3 := fun h => by
    simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using congr(star $h)
  tfae_have 3 -> 4 := hp.sub_of_mul_eq_left hq
  tfae_have 4 -> 1 := fun h => by simpa using h.nonneg
  tfae_have 4 ↔ 5 := by simp [isStarProjection_iff, hq.isSelfAdjoint.sub hp.isSelfAdjoint]
  tfae_finish

/--
lemma `le_iff_mul_eq_right` / 引理 `le_iff_mul_eq_right`

English:
lemma le_iff_mul_eq_right
  given: (hp : IsStarProjection p) (hq : IsStarProjection q)
  proof: .out 0 1 hp.le_tfae hq

中文:
引理 le_iff_mul_eq_right
  条件: (hp : 是StarProjection p) (hq : 是StarProjection q)
  证明: .out 0 1 hp.le_tfae hq

Depends on / 依赖: hp.le_tfae, le_tfae
-/
lemma le_iff_mul_eq_right (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p <= q ↔ q * p = p :=
.out 0 1 hp.le_tfae hq

/--
lemma `le_iff_mul_eq_left` / 引理 `le_iff_mul_eq_left`

English:
lemma le_iff_mul_eq_left
  given: (hp : IsStarProjection p) (hq : IsStarProjection q)
  proof: .out 0 2 hp.le_tfae hq

中文:
引理 le_iff_mul_eq_left
  条件: (hp : 是StarProjection p) (hq : 是StarProjection q)
  证明: .out 0 2 hp.le_tfae hq

Depends on / 依赖: hp.le_tfae, le_tfae
-/
lemma le_iff_mul_eq_left (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p <= q ↔ p * q = p :=
.out 0 2 hp.le_tfae hq

/--
lemma `le_iff_sub` / 引理 `le_iff_sub`

English:
lemma le_iff_sub
  given: (hp : IsStarProjection p) (hq : IsStarProjection q)
  proof: .out 0 3 hp.le_tfae hq

中文:
引理 le_iff_sub
  条件: (hp : 是StarProjection p) (hq : 是StarProjection q)
  证明: .out 0 3 hp.le_tfae hq

Depends on / 依赖: hp.le_tfae, le_tfae
-/
lemma le_iff_sub (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p <= q ↔ IsStarProjection (q - p) :=
.out 0 3 hp.le_tfae hq

/--
lemma `le_iff_idempotent_sub` / 引理 `le_iff_idempotent_sub`

English:
lemma le_iff_idempotent_sub
  given: (hp : IsStarProjection p) (hq : IsStarProjection q)
  proof: .out 0 4 hp.le_tfae hq

中文:
引理 le_iff_idempotent_sub
  条件: (hp : 是StarProjection p) (hq : 是StarProjection q)
  证明: .out 0 4 hp.le_tfae hq

Depends on / 依赖: hp.le_tfae, le_tfae
-/
lemma le_iff_idempotent_sub (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p <= q ↔ IsIdempotentElem (q - p) :=
.out 0 4 hp.le_tfae hq

/--
lemma `commute_of_le` / 引理 `commute_of_le`

English:
lemma commute_of_le
  given: (hp : IsStarProjection p) (hq : IsStarProjection q) (h : p <= q)
  proof: by
  rw [commute_iff_eq]; rw [hp.le_iff_mul_eq_right hq |>.mp h]; rw [hp.le_iff_mul_eq_left hq |>.mp h]

中文:
引理 commute_of_le
  条件: (hp : 是StarProjection p) (hq : 是StarProjection q) (h : p <= q)
  证明: by
  rw [commute_iff_eq]; rw [hp.le_iff_mul_eq_right hq |>.mp h]; rw [hp.le_iff_mul_eq_left hq |>.mp h]

Depends on / 依赖: commute_iff_eq, hp.le_iff_mul_eq_left, hp.le_iff_mul_eq_right, le_iff_mul_eq_left, le_iff_mul_eq_right
-/
lemma commute_of_le (hp : IsStarProjection p) (hq : IsStarProjection q) (h : p <= q) :
    Commute p q := by
  rw [commute_iff_eq]; rw [hp.le_iff_mul_eq_right hq |>.mp h]; rw [hp.le_iff_mul_eq_left hq |>.mp h]

end IsStarProjection
