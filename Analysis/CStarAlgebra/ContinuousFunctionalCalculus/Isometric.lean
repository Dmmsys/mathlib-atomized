/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-! # Isometric continuous functional calculus

This file adds a class for an *isometric* continuous functional calculus. This is separate from the
usual `ContinuousFunctionalCalculus` class because we prefer not to require a metric (or a norm) on
the algebra for reasons discussed in the module documentation for that file.

Of course, with a metric on the algebra and an isometric continuous functional calculus, the
algebra must *be* a C⋆-algebra already. As such, it may seem like this class is not useful. However,
the main purpose is to allow for the continuous functional calculus to be an isometry for the other
scalar rings `ℝ` and `ℝ≥0` too.
-/

public section

local notation "σ" => spectrum
local notation "σₙ" => quasispectrum

/-! ### Isometric continuous functional calculus for unital algebras -/
section Unital

/--
Definition of `IsometricContinuousFunctionalCalculus` / `IsometricContinuousFunctionalCalculus` 的定义

English:
class IsometricContinuousFunctionalCalculus
  parameters: (R A : Type*) (p : outParam (A -> Prop))
  extends: ContinuousFunctionalCalculus R A p
  axioms and operations (1):
    - isometric((a : A) (ha : p a)) : Isometry (cfcHom ha (R := R))

中文:
类 是ometricContinuousFunctionalCalculus
  参数: (R A : 类型) (p : outParam (A -> 命题))
  继承: 余ntinuousFunctionalCalculus R A p
  公理与运算 (1 个):
    - isometric((a : A) (ha : p a)) : 等距 (cfcHom ha (R := R))
-/
class IsometricContinuousFunctionalCalculus (R A : Type*) (p : outParam (A -> Prop))
    [CommSemiring R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
    [Ring A] [StarRing A] [MetricSpace A] [Algebra R A] : Prop
    extends ContinuousFunctionalCalculus R A p where
  isometric (a : A) (ha : p a) : Isometry (cfcHom ha (R := R))

section MetricSpace

open scoped ContinuousFunctionalCalculus

variable {R A : Type*} {p : A -> Prop} [CommSemiring R] [StarRing R]
  [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A]
  [MetricSpace A] [Algebra R A] [IsometricContinuousFunctionalCalculus R A p]

/--
lemma `isometry_cfcHom` / 引理 `isometry_cfcHom`

English:
lemma isometry_cfcHom
  given: (a : A) (ha : p a := by cfc_tac)
  proof: IsometricContinuousFunctionalCalculus.isometric a ha

中文:
引理 isometry_cfcHom
  条件: (a : A) (ha : p a := by cfc_tac)
  证明: IsometricContinuousFunctionalCalculus.isometric a ha

Depends on / 依赖: IsometricContinuousFunctionalCalculus, IsometricContinuousFunctionalCalculus.isometric, Isometry, cfcHom, cfc_tac, isometric
-/
lemma isometry_cfcHom (a : A) (ha : p a := by cfc_tac) :
    Isometry (cfcHom (show p a from ha) (R := R)) :=
  IsometricContinuousFunctionalCalculus.isometric a ha

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompleteSpace
  signature: R] : ClosedEmbeddingContinuousFunctionalCalculus R A p where
  body: (isometry_cfcHom a).isClosedEmbedding

中文:
实例 [完备空间
  签名: R] : ClosedEmbeddingContinuousFunctionalCalculus R A p where
  定义体: (isometry_cfcHom a).isClosedEmbedding

Depends on / 依赖: isClosedEmbedding, isometry_cfcHom
-/
instance [CompleteSpace R] : ClosedEmbeddingContinuousFunctionalCalculus R A p where
  isClosedEmbedding a ha := (isometry_cfcHom a).isClosedEmbedding

end MetricSpace

section NormedRing

open scoped ContinuousFunctionalCalculus

variable {𝕜 A : Type*} {p : outParam (A -> Prop)}
variable [RCLike 𝕜] [NormedRing A] [StarRing A] [NormedAlgebra 𝕜 A]
variable [IsometricContinuousFunctionalCalculus 𝕜 A p]

/--
lemma `norm_cfcHom` / 引理 `norm_cfcHom`

English:
lemma norm_cfcHom
  given: (a : A) (f : C(σ 𝕜 a, 𝕜)) (ha : p a := by cfc_tac)
  proof: by
.norm_map_of_map_zero (map_zero _) f refine isometry_cfcHom a

中文:
引理 norm_cfcHom
  条件: (a : A) (f : C(σ 𝕜 a, 𝕜)) (ha : p a := by cfc_tac)
  证明: by
.norm_map_of_map_zero (map_zero _) f refine isometry_cfcHom a

Depends on / 依赖: cfcHom, cfc_tac, isometry_cfcHom, map_zero, norm_map_of_map_zero
-/
lemma norm_cfcHom (a : A) (f : C(σ 𝕜 a, 𝕜)) (ha : p a := by cfc_tac) :
    ‖cfcHom (show p a from ha) f‖ = ‖f‖ := by
.norm_map_of_map_zero (map_zero _) f refine isometry_cfcHom a

/--
lemma `nnnorm_cfcHom` / 引理 `nnnorm_cfcHom`

English:
lemma nnnorm_cfcHom
  given: (a : A) (f : C(σ 𝕜 a, 𝕜)) (ha : p a := by cfc_tac)
  proof: Subtype.ext norm_cfcHom a f ha

中文:
引理 nnnorm_cfcHom
  条件: (a : A) (f : C(σ 𝕜 a, 𝕜)) (ha : p a := by cfc_tac)
  证明: Subtype.ext norm_cfcHom a f ha

Depends on / 依赖: Subtype, Subtype.ext, cfcHom, cfc_tac, norm_cfcHom
-/
lemma nnnorm_cfcHom (a : A) (f : C(σ 𝕜 a, 𝕜)) (ha : p a := by cfc_tac) :
    ‖cfcHom (show p a from ha) f‖₊ = ‖f‖₊ :=
Subtype.ext norm_cfcHom a f ha

/--
lemma `IsGreatest.norm_cfc` / 引理 `IsGreatest.norm_cfc`

English:
lemma IsGreatest.norm_cfc
  statement: [Nontrivial A] (f : 𝕜 -> 𝕜) (a : A)
  proof: by
  obtain ⟨x, hx⟩ := ContinuousFunctionalCalculus.isCompact_spectrum a
.exists_isGreatest .image_of_continuousOn hf.norm
    (ContinuousFunctionalCalculus.spectrum_nonempty a ha).image _
  obtain ⟨x, hx', rfl⟩ := hx.1
  convert! hx
  rw [cfc_apply f a]; rw [norm_cfcHom a _]
  apply le_antisymm
.mp

中文:
引理 IsGreatest.norm_cfc
  结论: [非平凡 A] (f : 𝕜 -> 𝕜) (a : A)
  证明: by
  obtain ⟨x, hx⟩ := ContinuousFunctionalCalculus.isCompact_spectrum a
.exists_isGreatest .image_of_continuousOn hf.norm
    (ContinuousFunctionalCalculus.spectrum_nonempty a ha).image _
  obtain ⟨x, hx', rfl⟩ := hx.1
  convert! hx
  rw [cfc_apply f a]; rw [norm_cfcHom a _]
  apply le_antisymm
.mp

Depends on / 依赖: ContinuousFunctionalCalculus, ContinuousFunctionalCalculus.isCompact_spectrum, ContinuousFunctionalCalculus.spectrum_nonempty, ContinuousMap, ContinuousMap.norm_le, IsGreatest, cfc_apply, cfc_cont_tac, cfc_tac, convert, exists_isGreatest, hf.norm, image_of_continuousOn, isCompact_spectrum, le_antisymm, le_trans, norm_cfcHom, norm_le, norm_nonneg, spectrum
-/
lemma IsGreatest.norm_cfc [Nontrivial A] (f : 𝕜 -> 𝕜) (a : A)
    (hf : ContinuousOn f (σ 𝕜 a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    IsGreatest ((fun x => ‖f x‖) '' spectrum 𝕜 a) ‖cfc f a‖ := by
  obtain ⟨x, hx⟩ := ContinuousFunctionalCalculus.isCompact_spectrum a
.exists_isGreatest .image_of_continuousOn hf.norm
    (ContinuousFunctionalCalculus.spectrum_nonempty a ha).image _
  obtain ⟨x, hx', rfl⟩ := hx.1
  convert! hx
  rw [cfc_apply f a]; rw [norm_cfcHom a _]
  apply le_antisymm
.mpr · apply ContinuousMap.norm_le _ (norm_nonneg _)
    rintro ⟨y, hy⟩
    exact hx.2 ⟨y, hy, rfl⟩
· exact le_trans (by simp) ContinuousMap.norm_coe_le_norm _ (⟨x, hx'⟩ : σ 𝕜 a)

/--
lemma `IsGreatest.nnnorm_cfc` / 引理 `IsGreatest.nnnorm_cfc`

English:
lemma IsGreatest.nnnorm_cfc
  statement: [Nontrivial A] (f : 𝕜 -> 𝕜) (a : A)
  proof: by
  convert! Real.toNNReal_monotone.map_isGreatest (.norm_cfc f a)
  all_goals simp [Set.image_image, norm_toNNReal]

中文:
引理 IsGreatest.nnnorm_cfc
  结论: [非平凡 A] (f : 𝕜 -> 𝕜) (a : A)
  证明: by
  convert! Real.toNNReal_monotone.map_isGreatest (.norm_cfc f a)
  all_goals simp [Set.image_image, norm_toNNReal]

Depends on / 依赖: IsGreatest, Real.toNNReal_monotone.map_isGreatest, Set.image_image, all_goals, cfc_cont_tac, cfc_tac, convert, image_image, map_isGreatest, norm_cfc, norm_toNNReal, toNNReal_monotone
-/
lemma IsGreatest.nnnorm_cfc [Nontrivial A] (f : 𝕜 -> 𝕜) (a : A)
    (hf : ContinuousOn f (σ 𝕜 a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    IsGreatest ((fun x => ‖f x‖₊) '' σ 𝕜 a) ‖cfc f a‖₊ := by
  convert! Real.toNNReal_monotone.map_isGreatest (.norm_cfc f a)
  all_goals simp [Set.image_image, norm_toNNReal]

/--
lemma `norm_apply_le_norm_cfc` / 引理 `norm_apply_le_norm_cfc`

English:
lemma norm_apply_le_norm_cfc
  given: (f : 𝕜 -> 𝕜) (a : A) ⦃x
  statement: 𝕜⦄ (hx : x in σ 𝕜 a)
  proof: by
  revert hx
  nontriviality A
  exact (IsGreatest.norm_cfc f a hf ha |>.2 ⟨x, ·, rfl⟩)

中文:
引理 norm_apply_le_norm_cfc
  条件: (f : 𝕜 -> 𝕜) (a : A) ⦃x
  结论: 𝕜⦄ (hx : x in σ 𝕜 a)
  证明: by
  revert hx
  nontriviality A
  exact (IsGreatest.norm_cfc f a hf ha |>.2 ⟨x, ·, rfl⟩)

Depends on / 依赖: IsGreatest, IsGreatest.norm_cfc, cfc_cont_tac, cfc_tac, nontriviality, norm_cfc, revert
-/
lemma norm_apply_le_norm_cfc (f : 𝕜 -> 𝕜) (a : A) ⦃x : 𝕜⦄ (hx : x in σ 𝕜 a)
    (hf : ContinuousOn f (σ 𝕜 a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    ‖f x‖ <= ‖cfc f a‖ := by
  revert hx
  nontriviality A
  exact (IsGreatest.norm_cfc f a hf ha |>.2 ⟨x, ·, rfl⟩)

/--
lemma `nnnorm_apply_le_nnnorm_cfc` / 引理 `nnnorm_apply_le_nnnorm_cfc`

English:
lemma nnnorm_apply_le_nnnorm_cfc
  given: (f : 𝕜 -> 𝕜) (a : A) ⦃x
  statement: 𝕜⦄ (hx : x in σ 𝕜 a)
  proof: norm_apply_le_norm_cfc f a hx

中文:
引理 nnnorm_apply_le_nnnorm_cfc
  条件: (f : 𝕜 -> 𝕜) (a : A) ⦃x
  结论: 𝕜⦄ (hx : x in σ 𝕜 a)
  证明: norm_apply_le_norm_cfc f a hx

Depends on / 依赖: cfc_cont_tac, cfc_tac, norm_apply_le_norm_cfc
-/
lemma nnnorm_apply_le_nnnorm_cfc (f : 𝕜 -> 𝕜) (a : A) ⦃x : 𝕜⦄ (hx : x in σ 𝕜 a)
    (hf : ContinuousOn f (σ 𝕜 a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    ‖f x‖₊ <= ‖cfc f a‖₊ :=
  norm_apply_le_norm_cfc f a hx

/--
lemma `norm_cfc_le` / 引理 `norm_cfc_le`

English:
lemma norm_cfc_le
  given: {f : 𝕜 -> 𝕜} {a : A} {c : Real} (hc : 0 <= c) (h : forall x in σ 𝕜 a, ‖f x‖ <= c)
  proof: by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · simpa [Subsingleton.elim (cfc f a) 0]
  · refine cfc_cases (‖·‖ <= c) a f (by simpa) fun hf ha => ?_
    simp only [← cfc_apply f a, isLUB_le_iff (IsGreatest.norm_cfc f a hf ha |>.isLUB)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx

中文:
引理 norm_cfc_le
  条件: {f : 𝕜 -> 𝕜} {a : A} {c : 实数} (hc : 0 <= c) (h : 对任意 x in σ 𝕜 a, ‖f x‖ <= c)
  证明: by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · simpa [Subsingleton.elim (cfc f a) 0]
  · refine cfc_cases (‖·‖ <= c) a f (by simpa) fun hf ha => ?_
    simp only [← cfc_apply f a, isLUB_le_iff (IsGreatest.norm_cfc f a hf ha |>.isLUB)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx

Depends on / 依赖: IsGreatest, IsGreatest.norm_cfc, Subsingleton, Subsingleton.elim, cfc_apply, cfc_cases, isLUB_le_iff, norm_cfc, subsingleton_or_nontrivial
-/
lemma norm_cfc_le {f : 𝕜 -> 𝕜} {a : A} {c : Real} (hc : 0 <= c) (h : forall x in σ 𝕜 a, ‖f x‖ <= c) :
    ‖cfc f a‖ <= c := by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · simpa [Subsingleton.elim (cfc f a) 0]
  · refine cfc_cases (‖·‖ <= c) a f (by simpa) fun hf ha => ?_
    simp only [← cfc_apply f a, isLUB_le_iff (IsGreatest.norm_cfc f a hf ha |>.isLUB)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx

/--
lemma `norm_cfc_le_iff` / 引理 `norm_cfc_le_iff`

English:
lemma norm_cfc_le_iff
  statement: (f : 𝕜 -> 𝕜) (a : A) {c : Real} (hc : 0 <= c)
  proof: .trans h, norm_cfc_le hc⟩ ⟨fun h _ hx => norm_apply_le_norm_cfc f a hx hf ha

中文:
引理 norm_cfc_le_iff
  结论: (f : 𝕜 -> 𝕜) (a : A) {c : 实数} (hc : 0 <= c)
  证明: .trans h, norm_cfc_le hc⟩ ⟨fun h _ hx => norm_apply_le_norm_cfc f a hx hf ha

Depends on / 依赖: cfc_cont_tac, cfc_tac, norm_apply_le_norm_cfc, norm_cfc_le
-/
lemma norm_cfc_le_iff (f : 𝕜 -> 𝕜) (a : A) {c : Real} (hc : 0 <= c)
    (hf : ContinuousOn f (σ 𝕜 a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) : ‖cfc f a‖ <= c ↔ forall x in σ 𝕜 a, ‖f x‖ <= c :=
.trans h, norm_cfc_le hc⟩ ⟨fun h _ hx => norm_apply_le_norm_cfc f a hx hf ha

/--
lemma `norm_cfc_lt` / 引理 `norm_cfc_lt`

English:
lemma norm_cfc_lt
  given: {f : 𝕜 -> 𝕜} {a : A} {c : Real} (hc : 0 < c) (h : forall x in σ 𝕜 a, ‖f x‖ < c)
  proof: by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · simpa [Subsingleton.elim (cfc f a) 0]
  · refine cfc_cases (‖·‖ < c) a f (by simpa) fun hf ha => ?_
    simp only [← cfc_apply f a, (IsGreatest.norm_cfc f a hf ha |>.lt_iff)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx

中文:
引理 norm_cfc_lt
  条件: {f : 𝕜 -> 𝕜} {a : A} {c : 实数} (hc : 0 < c) (h : 对任意 x in σ 𝕜 a, ‖f x‖ < c)
  证明: by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · simpa [Subsingleton.elim (cfc f a) 0]
  · refine cfc_cases (‖·‖ < c) a f (by simpa) fun hf ha => ?_
    simp only [← cfc_apply f a, (IsGreatest.norm_cfc f a hf ha |>.lt_iff)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx

Depends on / 依赖: IsGreatest, IsGreatest.norm_cfc, Subsingleton, Subsingleton.elim, cfc_apply, cfc_cases, lt_iff, norm_cfc, subsingleton_or_nontrivial
-/
lemma norm_cfc_lt {f : 𝕜 -> 𝕜} {a : A} {c : Real} (hc : 0 < c) (h : forall x in σ 𝕜 a, ‖f x‖ < c) :
    ‖cfc f a‖ < c := by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · simpa [Subsingleton.elim (cfc f a) 0]
  · refine cfc_cases (‖·‖ < c) a f (by simpa) fun hf ha => ?_
    simp only [← cfc_apply f a, (IsGreatest.norm_cfc f a hf ha |>.lt_iff)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx

/--
lemma `norm_cfc_lt_iff` / 引理 `norm_cfc_lt_iff`

English:
lemma norm_cfc_lt_iff
  statement: (f : 𝕜 -> 𝕜) (a : A) {c : Real} (hc : 0 < c)
  proof: .trans_lt h, norm_cfc_lt hc⟩ ⟨fun h _ hx => norm_apply_le_norm_cfc f a hx hf ha

中文:
引理 norm_cfc_lt_iff
  结论: (f : 𝕜 -> 𝕜) (a : A) {c : 实数} (hc : 0 < c)
  证明: .trans_lt h, norm_cfc_lt hc⟩ ⟨fun h _ hx => norm_apply_le_norm_cfc f a hx hf ha

Depends on / 依赖: cfc_cont_tac, cfc_tac, norm_apply_le_norm_cfc, norm_cfc_lt, trans_lt
-/
lemma norm_cfc_lt_iff (f : 𝕜 -> 𝕜) (a : A) {c : Real} (hc : 0 < c)
    (hf : ContinuousOn f (σ 𝕜 a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) : ‖cfc f a‖ < c ↔ forall x in σ 𝕜 a, ‖f x‖ < c :=
.trans_lt h, norm_cfc_lt hc⟩ ⟨fun h _ hx => norm_apply_le_norm_cfc f a hx hf ha

open NNReal

/--
lemma `nnnorm_cfc_le` / 引理 `nnnorm_cfc_le`

English:
lemma nnnorm_cfc_le
  given: {f : 𝕜 -> 𝕜} {a : A} (c : Real>=0) (h : forall x in σ 𝕜 a, ‖f x‖₊ <= c)
  proof: norm_cfc_le c.2 h

中文:
引理 nnnorm_cfc_le
  条件: {f : 𝕜 -> 𝕜} {a : A} (c : 实数>=0) (h : 对任意 x in σ 𝕜 a, ‖f x‖₊ <= c)
  证明: norm_cfc_le c.2 h

Depends on / 依赖: norm_cfc_le
-/
lemma nnnorm_cfc_le {f : 𝕜 -> 𝕜} {a : A} (c : Real>=0) (h : forall x in σ 𝕜 a, ‖f x‖₊ <= c) :
    ‖cfc f a‖₊ <= c :=
  norm_cfc_le c.2 h

/--
lemma `nnnorm_cfc_le_iff` / 引理 `nnnorm_cfc_le_iff`

English:
lemma nnnorm_cfc_le_iff
  statement: (f : 𝕜 -> 𝕜) (a : A) (c : Real>=0)
  proof: norm_cfc_le_iff f a c.2

中文:
引理 nnnorm_cfc_le_iff
  结论: (f : 𝕜 -> 𝕜) (a : A) (c : 实数>=0)
  证明: norm_cfc_le_iff f a c.2

Depends on / 依赖: cfc_cont_tac, cfc_tac, norm_cfc_le_iff
-/
lemma nnnorm_cfc_le_iff (f : 𝕜 -> 𝕜) (a : A) (c : Real>=0)
    (hf : ContinuousOn f (σ 𝕜 a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) : ‖cfc f a‖₊ <= c ↔ forall x in σ 𝕜 a, ‖f x‖₊ <= c :=
  norm_cfc_le_iff f a c.2

/--
lemma `nnnorm_cfc_lt` / 引理 `nnnorm_cfc_lt`

English:
lemma nnnorm_cfc_lt
  given: {f : 𝕜 -> 𝕜} {a : A} {c : Real>=0} (hc : 0 < c) (h : forall x in σ 𝕜 a, ‖f x‖₊ < c)
  proof: norm_cfc_lt hc h

中文:
引理 nnnorm_cfc_lt
  条件: {f : 𝕜 -> 𝕜} {a : A} {c : 实数>=0} (hc : 0 < c) (h : 对任意 x in σ 𝕜 a, ‖f x‖₊ < c)
  证明: norm_cfc_lt hc h

Depends on / 依赖: norm_cfc_lt
-/
lemma nnnorm_cfc_lt {f : 𝕜 -> 𝕜} {a : A} {c : Real>=0} (hc : 0 < c) (h : forall x in σ 𝕜 a, ‖f x‖₊ < c) :
    ‖cfc f a‖₊ < c :=
  norm_cfc_lt hc h

/--
lemma `nnnorm_cfc_lt_iff` / 引理 `nnnorm_cfc_lt_iff`

English:
lemma nnnorm_cfc_lt_iff
  statement: (f : 𝕜 -> 𝕜) (a : A) {c : Real>=0} (hc : 0 < c)
  proof: norm_cfc_lt_iff f a hc

中文:
引理 nnnorm_cfc_lt_iff
  结论: (f : 𝕜 -> 𝕜) (a : A) {c : 实数>=0} (hc : 0 < c)
  证明: norm_cfc_lt_iff f a hc

Depends on / 依赖: cfc_cont_tac, cfc_tac, norm_cfc_lt_iff
-/
lemma nnnorm_cfc_lt_iff (f : 𝕜 -> 𝕜) (a : A) {c : Real>=0} (hc : 0 < c)
    (hf : ContinuousOn f (σ 𝕜 a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) : ‖cfc f a‖₊ < c ↔ forall x in σ 𝕜 a, ‖f x‖₊ < c :=
  norm_cfc_lt_iff f a hc

namespace IsometricContinuousFunctionalCalculus

/--
lemma `isGreatest_norm_spectrum` / 引理 `isGreatest_norm_spectrum`

English:
lemma isGreatest_norm_spectrum
  given: [Nontrivial A] (a : A) (ha : p a := by cfc_tac)
  proof: by
  simpa only [cfc_id 𝕜 a] using! IsGreatest.norm_cfc (id : 𝕜 -> 𝕜) a

中文:
引理 isGreatest_norm_spectrum
  条件: [非平凡 A] (a : A) (ha : p a := by cfc_tac)
  证明: by
  simpa only [cfc_id 𝕜 a] using! IsGreatest.norm_cfc (id : 𝕜 -> 𝕜) a

Depends on / 依赖: IsGreatest, IsGreatest.norm_cfc, cfc_id, cfc_tac, norm_cfc, spectrum
-/
lemma isGreatest_norm_spectrum [Nontrivial A] (a : A) (ha : p a := by cfc_tac) :
    IsGreatest ((‖·‖) '' spectrum 𝕜 a) ‖a‖ := by
  simpa only [cfc_id 𝕜 a] using! IsGreatest.norm_cfc (id : 𝕜 -> 𝕜) a

/--
lemma `norm_spectrum_le` / 引理 `norm_spectrum_le`

English:
lemma norm_spectrum_le
  given: (a : A) ⦃x
  statement: 𝕜⦄ (hx : x in σ 𝕜 a) (ha : p a := by cfc_tac) :
  proof: by
  simpa only [cfc_id 𝕜 a] using! norm_apply_le_norm_cfc (id : 𝕜 -> 𝕜) a hx

中文:
引理 norm_spectrum_le
  条件: (a : A) ⦃x
  结论: 𝕜⦄ (hx : x in σ 𝕜 a) (ha : p a := by cfc_tac) :
  证明: by
  simpa only [cfc_id 𝕜 a] using! norm_apply_le_norm_cfc (id : 𝕜 -> 𝕜) a hx

Depends on / 依赖: cfc_id, cfc_tac, norm_apply_le_norm_cfc
-/
lemma norm_spectrum_le (a : A) ⦃x : 𝕜⦄ (hx : x in σ 𝕜 a) (ha : p a := by cfc_tac) :
    ‖x‖ <= ‖a‖ := by
  simpa only [cfc_id 𝕜 a] using! norm_apply_le_norm_cfc (id : 𝕜 -> 𝕜) a hx

/--
lemma `isGreatest_nnnorm_spectrum` / 引理 `isGreatest_nnnorm_spectrum`

English:
lemma isGreatest_nnnorm_spectrum
  given: [Nontrivial A] (a : A) (ha : p a := by cfc_tac)
  proof: by
  simpa only [cfc_id 𝕜 a] using! IsGreatest.nnnorm_cfc (id : 𝕜 -> 𝕜) a

中文:
引理 isGreatest_nnnorm_spectrum
  条件: [非平凡 A] (a : A) (ha : p a := by cfc_tac)
  证明: by
  simpa only [cfc_id 𝕜 a] using! IsGreatest.nnnorm_cfc (id : 𝕜 -> 𝕜) a

Depends on / 依赖: IsGreatest, IsGreatest.nnnorm_cfc, cfc_id, cfc_tac, nnnorm_cfc, spectrum
-/
lemma isGreatest_nnnorm_spectrum [Nontrivial A] (a : A) (ha : p a := by cfc_tac) :
    IsGreatest ((‖·‖₊) '' spectrum 𝕜 a) ‖a‖₊ := by
  simpa only [cfc_id 𝕜 a] using! IsGreatest.nnnorm_cfc (id : 𝕜 -> 𝕜) a

/--
lemma `nnnorm_spectrum_le` / 引理 `nnnorm_spectrum_le`

English:
lemma nnnorm_spectrum_le
  given: (a : A) ⦃x
  statement: 𝕜⦄ (hx : x in σ 𝕜 a) (ha : p a := by cfc_tac) :
  proof: by
  simpa only [cfc_id 𝕜 a] using! nnnorm_apply_le_nnnorm_cfc (id : 𝕜 -> 𝕜) a hx

中文:
引理 nnnorm_spectrum_le
  条件: (a : A) ⦃x
  结论: 𝕜⦄ (hx : x in σ 𝕜 a) (ha : p a := by cfc_tac) :
  证明: by
  simpa only [cfc_id 𝕜 a] using! nnnorm_apply_le_nnnorm_cfc (id : 𝕜 -> 𝕜) a hx

Depends on / 依赖: cfc_id, cfc_tac, nnnorm_apply_le_nnnorm_cfc
-/
lemma nnnorm_spectrum_le (a : A) ⦃x : 𝕜⦄ (hx : x in σ 𝕜 a) (ha : p a := by cfc_tac) :
    ‖x‖₊ <= ‖a‖₊ := by
  simpa only [cfc_id 𝕜 a] using! nnnorm_apply_le_nnnorm_cfc (id : 𝕜 -> 𝕜) a hx

end IsometricContinuousFunctionalCalculus

end NormedRing

namespace SpectrumRestricts

variable {R S A : Type*} {p q : A -> Prop}
variable [Semifield R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
variable [Semifield S] [StarRing S] [MetricSpace S] [IsTopologicalSemiring S] [ContinuousStar S]
variable [Ring A] [StarRing A] [Algebra S A]
variable [Algebra R S] [Algebra R A] [IsScalarTower R S A] [StarModule R S] [ContinuousSMul R S]
variable [MetricSpace A] [IsometricContinuousFunctionalCalculus S A q]
variable [CompleteSpace R] [ContinuousMap.UniqueHom R A]

set_option backward.isDefEq.respectTransparency.types false in
open scoped ContinuousFunctionalCalculus in
/--
theorem `isometric_cfc` / 定理 `isometric_cfc`

English:
theorem isometric_cfc
  statement: (f : C(S, R)) (halg : Isometry (algebraMap R S)) (h0 : p 0)
  proof: SpectrumRestricts.cfc f halg.isClosedEmbedding h0 h
  isometric a ha := by
.mp ha obtain ⟨ha', haf⟩ := h a
    have := SpectrumRestricts.cfc f halg.isClosedEmbedding h0 h
    rw [cfcHom_eq_restrict f ha ha' haf]
    refine .of_dist_eq fun g₁ g₂ => ?_
    simp only [starAlgHom_apply, isometry_cfcHom 

中文:
定理 isometric_cfc
  结论: (f : C(S, R)) (halg : 等距 (algebraMap R S)) (h0 : p 0)
  证明: SpectrumRestricts.cfc f halg.isClosedEmbedding h0 h
  isometric a ha := by
.mp ha obtain ⟨ha', haf⟩ := h a
    have := SpectrumRestricts.cfc f halg.isClosedEmbedding h0 h
    rw [cfcHom_eq_restrict f ha ha' haf]
    refine .of_dist_eq fun g₁ g₂ => ?_
    simp only [starAlgHom_apply, isometry_cfcHom 
-/
protected theorem isometric_cfc (f : C(S, R)) (halg : Isometry (algebraMap R S)) (h0 : p 0)
    (h : forall a, p a ↔ q a ∧ SpectrumRestricts a f) :
    IsometricContinuousFunctionalCalculus R A p where
  toContinuousFunctionalCalculus := SpectrumRestricts.cfc f halg.isClosedEmbedding h0 h
  isometric a ha := by
.mp ha obtain ⟨ha', haf⟩ := h a
    have := SpectrumRestricts.cfc f halg.isClosedEmbedding h0 h
    rw [cfcHom_eq_restrict f ha ha' haf]
    refine .of_dist_eq fun g₁ g₂ => ?_
    simp only [starAlgHom_apply, isometry_cfcHom a ha' |>.dist_eq]
    refine le_antisymm ?_ ?_
.mpr fun x => ?_ all_goals refine ContinuousMap.dist_le dist_nonneg
    · simpa [halg.dist_eq] using ContinuousMap.dist_apply_le_dist _
    · let x' : σ S a := Subtype.map (algebraMap R S) (fun _ => spectrum.algebraMap_mem S) x
apply le_of_eq_of_le ?_ ContinuousMap.dist_apply_le_dist x'
      simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, StarAlgHom.ofId_apply,
        halg.dist_eq, x']
      congr!
.symm all_goals ext; exact haf.left_inv _

end SpectrumRestricts

end Unital

/-! ### Isometric continuous functional calculus for non-unital algebras -/

section NonUnital

/--
Definition of `NonUnitalIsometricContinuousFunctionalCalculus` / `NonUnitalIsometricContinuousFunctionalCalculus` 的定义

English:
class NonUnitalIsometricContinuousFunctionalCalculus
  parameters: (R A : Type*) (p : outParam (A -> Prop))
  extends: NonUnitalContinuousFunctionalCalculus R A p
  axioms and operations (1):
    - isometric((a : A) (ha : p a)) : Isometry (cfcₙHom ha (R := R))

中文:
类 非幺是ometricContinuousFunctionalCalculus
  参数: (R A : 类型) (p : outParam (A -> 命题))
  继承: 非幺余ntinuousFunctionalCalculus R A p
  公理与运算 (1 个):
    - isometric((a : A) (ha : p a)) : 等距 (cfcₙHom ha (R := R))
-/
class NonUnitalIsometricContinuousFunctionalCalculus (R A : Type*) (p : outParam (A -> Prop))
    [CommSemiring R] [Nontrivial R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R]
    [ContinuousStar R] [NonUnitalRing A] [StarRing A] [MetricSpace A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : Prop
    extends NonUnitalContinuousFunctionalCalculus R A p where
  isometric (a : A) (ha : p a) : Isometry (cfcₙHom ha (R := R))

section MetricSpace

variable {R A : Type*} {p : outParam (A -> Prop)}
variable [CommSemiring R] [Nontrivial R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R]
variable [ContinuousStar R]
variable [NonUnitalRing A] [StarRing A] [MetricSpace A] [Module R A]
variable [IsScalarTower R A A] [SMulCommClass R A A]

open scoped NonUnitalContinuousFunctionalCalculus

variable [NonUnitalIsometricContinuousFunctionalCalculus R A p]

/--
lemma `isometry_cfcₙHom` / 引理 `isometry_cfcₙHom`

English:
lemma isometry_cfcₙHom
  given: (a : A) (ha : p a := by cfc_tac)
  proof: NonUnitalIsometricContinuousFunctionalCalculus.isometric a ha

中文:
引理 isometry_cfcₙHom
  条件: (a : A) (ha : p a := by cfc_tac)
  证明: NonUnitalIsometricContinuousFunctionalCalculus.isometric a ha

Depends on / 依赖: Isometry, NonUnitalIsometricContinuousFunctionalCalculus, NonUnitalIsometricContinuousFunctionalCalculus.isometric, cfc_tac, isometric
-/
lemma isometry_cfcₙHom (a : A) (ha : p a := by cfc_tac) :
    Isometry (cfcₙHom (show p a from ha) (R := R)) :=
  NonUnitalIsometricContinuousFunctionalCalculus.isometric a ha

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompleteSpace
  signature: R] : NonUnitalClosedEmbeddingContinuousFunctionalCalculus R A p where
  body: (isometry_cfcₙHom a).isClosedEmbedding

中文:
实例 [完备空间
  签名: R] : 非幺ClosedEmbeddingContinuousFunctionalCalculus R A p where
  定义体: (isometry_cfcₙHom a).isClosedEmbedding

Depends on / 依赖: isClosedEmbedding
-/
instance [CompleteSpace R] : NonUnitalClosedEmbeddingContinuousFunctionalCalculus R A p where
  isClosedEmbedding a ha := (isometry_cfcₙHom a).isClosedEmbedding

end MetricSpace

section NormedRing

variable {𝕜 A : Type*} {p : outParam (A -> Prop)}
variable [RCLike 𝕜] [NonUnitalNormedRing A] [StarRing A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A]
variable [SMulCommClass 𝕜 A A]
variable [NonUnitalIsometricContinuousFunctionalCalculus 𝕜 A p]

open NonUnitalIsometricContinuousFunctionalCalculus
open scoped ContinuousMapZero NonUnitalContinuousFunctionalCalculus

/--
lemma `norm_cfcₙHom` / 引理 `norm_cfcₙHom`

English:
lemma norm_cfcₙHom
  given: (a : A) (f : C(σₙ 𝕜 a, 𝕜)₀) (ha : p a := by cfc_tac)
  proof: by
.norm_map_of_map_zero (map_zero _) f refine isometry_cfcₙHom a

中文:
引理 norm_cfcₙHom
  条件: (a : A) (f : C(σₙ 𝕜 a, 𝕜)₀) (ha : p a := by cfc_tac)
  证明: by
.norm_map_of_map_zero (map_zero _) f refine isometry_cfcₙHom a

Depends on / 依赖: cfc_tac, map_zero, norm_map_of_map_zero
-/
lemma norm_cfcₙHom (a : A) (f : C(σₙ 𝕜 a, 𝕜)₀) (ha : p a := by cfc_tac) :
    ‖cfcₙHom (show p a from ha) f‖ = ‖f‖ := by
.norm_map_of_map_zero (map_zero _) f refine isometry_cfcₙHom a

/--
lemma `nnnorm_cfcₙHom` / 引理 `nnnorm_cfcₙHom`

English:
lemma nnnorm_cfcₙHom
  given: (a : A) (f : C(σₙ 𝕜 a, 𝕜)₀) (ha : p a := by cfc_tac)
  proof: Subtype.ext norm_cfcₙHom a f ha

中文:
引理 nnnorm_cfcₙHom
  条件: (a : A) (f : C(σₙ 𝕜 a, 𝕜)₀) (ha : p a := by cfc_tac)
  证明: Subtype.ext norm_cfcₙHom a f ha

Depends on / 依赖: Subtype, Subtype.ext, cfc_tac
-/
lemma nnnorm_cfcₙHom (a : A) (f : C(σₙ 𝕜 a, 𝕜)₀) (ha : p a := by cfc_tac) :
    ‖cfcₙHom (show p a from ha) f‖₊ = ‖f‖₊ :=
Subtype.ext norm_cfcₙHom a f ha

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `IsGreatest.norm_cfcₙ` / 引理 `IsGreatest.norm_cfcₙ`

English:
lemma IsGreatest.norm_cfcₙ
  statement: (f : 𝕜 -> 𝕜) (a : A)
  proof: by
  obtain ⟨x, hx⟩ := NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum a
.exists_isGreatest .image_of_continuousOn hf.norm
      (quasispectrum.nonempty 𝕜 a).image _
  obtain ⟨x, hx', rfl⟩ := hx.1
  convert! hx
  rw [cfcₙ_apply f a]; rw [norm_cfcₙHom a _]
  apply le_antisymm
.mpr · app

中文:
引理 IsGreatest.norm_cfcₙ
  结论: (f : 𝕜 -> 𝕜) (a : A)
  证明: by
  obtain ⟨x, hx⟩ := NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum a
.exists_isGreatest .image_of_continuousOn hf.norm
      (quasispectrum.nonempty 𝕜 a).image _
  obtain ⟨x, hx', rfl⟩ := hx.1
  convert! hx
  rw [cfcₙ_apply f a]; rw [norm_cfcₙHom a _]
  apply le_antisymm
.mpr · app

Depends on / 依赖: ContinuousMap, ContinuousMap.norm_le, IsGreatest, NonUnitalContinuousFunctionalCalculus, NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum, cfc_cont_tac, cfc_tac, cfc_zero_tac, convert, exists_isGreatest, hf.norm, image_of_continuousOn, isCompact_quasispectrum, le_antisymm, nonempty, norm_le, norm_nonneg, quasispectrum, quasispectrum.nonempty
-/
lemma IsGreatest.norm_cfcₙ (f : 𝕜 -> 𝕜) (a : A)
    (hf : ContinuousOn f (σₙ 𝕜 a) := by cfc_cont_tac) (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) : IsGreatest ((fun x => ‖f x‖) '' σₙ 𝕜 a) ‖cfcₙ f a‖ := by
  obtain ⟨x, hx⟩ := NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum a
.exists_isGreatest .image_of_continuousOn hf.norm
      (quasispectrum.nonempty 𝕜 a).image _
  obtain ⟨x, hx', rfl⟩ := hx.1
  convert! hx
  rw [cfcₙ_apply f a]; rw [norm_cfcₙHom a _]
  apply le_antisymm
.mpr · apply ContinuousMap.norm_le _ (norm_nonneg _)
    rintro ⟨y, hy⟩
    exact hx.2 ⟨y, hy, rfl⟩
· exact le_trans (by simp) ContinuousMap.norm_coe_le_norm _ (⟨x, hx'⟩ : σₙ 𝕜 a)

/--
lemma `IsGreatest.nnnorm_cfcₙ` / 引理 `IsGreatest.nnnorm_cfcₙ`

English:
lemma IsGreatest.nnnorm_cfcₙ
  statement: (f : 𝕜 -> 𝕜) (a : A)
  proof: by
  convert! Real.toNNReal_monotone.map_isGreatest (.norm_cfcₙ f a)
  all_goals simp [Set.image_image, norm_toNNReal]

中文:
引理 IsGreatest.nnnorm_cfcₙ
  结论: (f : 𝕜 -> 𝕜) (a : A)
  证明: by
  convert! Real.toNNReal_monotone.map_isGreatest (.norm_cfcₙ f a)
  all_goals simp [Set.image_image, norm_toNNReal]

Depends on / 依赖: IsGreatest, Real.toNNReal_monotone.map_isGreatest, Set.image_image, all_goals, cfc_cont_tac, cfc_tac, cfc_zero_tac, convert, image_image, map_isGreatest, norm_toNNReal, toNNReal_monotone
-/
lemma IsGreatest.nnnorm_cfcₙ (f : 𝕜 -> 𝕜) (a : A)
    (hf : ContinuousOn f (σₙ 𝕜 a) := by cfc_cont_tac) (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) : IsGreatest ((fun x => ‖f x‖₊) '' σₙ 𝕜 a) ‖cfcₙ f a‖₊ := by
  convert! Real.toNNReal_monotone.map_isGreatest (.norm_cfcₙ f a)
  all_goals simp [Set.image_image, norm_toNNReal]

/--
lemma `norm_apply_le_norm_cfcₙ` / 引理 `norm_apply_le_norm_cfcₙ`

English:
lemma norm_apply_le_norm_cfcₙ
  given: (f : 𝕜 -> 𝕜) (a : A) ⦃x
  statement: 𝕜⦄ (hx : x in σₙ 𝕜 a)
  proof: .2 ⟨x, hx, rfl⟩ IsGreatest.norm_cfcₙ f a hf hf₀ ha

中文:
引理 norm_apply_le_norm_cfcₙ
  条件: (f : 𝕜 -> 𝕜) (a : A) ⦃x
  结论: 𝕜⦄ (hx : x in σₙ 𝕜 a)
  证明: .2 ⟨x, hx, rfl⟩ IsGreatest.norm_cfcₙ f a hf hf₀ ha

Depends on / 依赖: IsGreatest, IsGreatest.norm_cfc, cfc_cont_tac, cfc_tac, cfc_zero_tac
-/
lemma norm_apply_le_norm_cfcₙ (f : 𝕜 -> 𝕜) (a : A) ⦃x : 𝕜⦄ (hx : x in σₙ 𝕜 a)
    (hf : ContinuousOn f (σₙ 𝕜 a) := by cfc_cont_tac) (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) : ‖f x‖ <= ‖cfcₙ f a‖ :=
.2 ⟨x, hx, rfl⟩ IsGreatest.norm_cfcₙ f a hf hf₀ ha

/--
lemma `nnnorm_apply_le_nnnorm_cfcₙ` / 引理 `nnnorm_apply_le_nnnorm_cfcₙ`

English:
lemma nnnorm_apply_le_nnnorm_cfcₙ
  given: (f : 𝕜 -> 𝕜) (a : A) ⦃x
  statement: 𝕜⦄ (hx : x in σₙ 𝕜 a)
  proof: .2 ⟨x, hx, rfl⟩ IsGreatest.nnnorm_cfcₙ f a hf hf₀ ha

中文:
引理 nnnorm_apply_le_nnnorm_cfcₙ
  条件: (f : 𝕜 -> 𝕜) (a : A) ⦃x
  结论: 𝕜⦄ (hx : x in σₙ 𝕜 a)
  证明: .2 ⟨x, hx, rfl⟩ IsGreatest.nnnorm_cfcₙ f a hf hf₀ ha

Depends on / 依赖: IsGreatest, IsGreatest.nnnorm_cfc, cfc_cont_tac, cfc_tac, cfc_zero_tac
-/
lemma nnnorm_apply_le_nnnorm_cfcₙ (f : 𝕜 -> 𝕜) (a : A) ⦃x : 𝕜⦄ (hx : x in σₙ 𝕜 a)
    (hf : ContinuousOn f (σₙ 𝕜 a) := by cfc_cont_tac) (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) : ‖f x‖₊ <= ‖cfcₙ f a‖₊ :=
.2 ⟨x, hx, rfl⟩ IsGreatest.nnnorm_cfcₙ f a hf hf₀ ha

/--
lemma `norm_cfcₙ_le` / 引理 `norm_cfcₙ_le`

English:
lemma norm_cfcₙ_le
  given: {f : 𝕜 -> 𝕜} {a : A} {c : Real} (h : forall x in σₙ 𝕜 a, ‖f x‖ <= c)
  proof: by
  refine cfcₙ_cases (‖·‖ <= c) a f ?_ fun hf hf0 ha => ?_
· simpa using (norm_nonneg _).trans h 0 (quasispectrum.zero_mem 𝕜 a)
  · simp only [← cfcₙ_apply f a, isLUB_le_iff (IsGreatest.norm_cfcₙ f a hf hf0 ha |>.isLUB)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx

中文:
引理 norm_cfcₙ_le
  条件: {f : 𝕜 -> 𝕜} {a : A} {c : 实数} (h : 对任意 x in σₙ 𝕜 a, ‖f x‖ <= c)
  证明: by
  refine cfcₙ_cases (‖·‖ <= c) a f ?_ fun hf hf0 ha => ?_
· simpa using (norm_nonneg _).trans h 0 (quasispectrum.zero_mem 𝕜 a)
  · simp only [← cfcₙ_apply f a, isLUB_le_iff (IsGreatest.norm_cfcₙ f a hf hf0 ha |>.isLUB)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx

Depends on / 依赖: IsGreatest, IsGreatest.norm_cfc, isLUB_le_iff, norm_nonneg, quasispectrum, quasispectrum.zero_mem, zero_mem
-/
lemma norm_cfcₙ_le {f : 𝕜 -> 𝕜} {a : A} {c : Real} (h : forall x in σₙ 𝕜 a, ‖f x‖ <= c) :
    ‖cfcₙ f a‖ <= c := by
  refine cfcₙ_cases (‖·‖ <= c) a f ?_ fun hf hf0 ha => ?_
· simpa using (norm_nonneg _).trans h 0 (quasispectrum.zero_mem 𝕜 a)
  · simp only [← cfcₙ_apply f a, isLUB_le_iff (IsGreatest.norm_cfcₙ f a hf hf0 ha |>.isLUB)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx

/--
lemma `norm_cfcₙ_le_iff` / 引理 `norm_cfcₙ_le_iff`

English:
lemma norm_cfcₙ_le_iff
  statement: (f : 𝕜 -> 𝕜) (a : A) (c : Real)
  proof: .trans h, norm_cfcₙ_le⟩ ⟨fun h _ hx => norm_apply_le_norm_cfcₙ f a hx hf hf₀ ha

中文:
引理 norm_cfcₙ_le_iff
  结论: (f : 𝕜 -> 𝕜) (a : A) (c : 实数)
  证明: .trans h, norm_cfcₙ_le⟩ ⟨fun h _ hx => norm_apply_le_norm_cfcₙ f a hx hf hf₀ ha

Depends on / 依赖: cfc_cont_tac, cfc_tac, cfc_zero_tac
-/
lemma norm_cfcₙ_le_iff (f : 𝕜 -> 𝕜) (a : A) (c : Real)
    (hf : ContinuousOn f (σₙ 𝕜 a) := by cfc_cont_tac) (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) : ‖cfcₙ f a‖ <= c ↔ forall x in σₙ 𝕜 a, ‖f x‖ <= c :=
.trans h, norm_cfcₙ_le⟩ ⟨fun h _ hx => norm_apply_le_norm_cfcₙ f a hx hf hf₀ ha

/--
lemma `norm_cfcₙ_lt` / 引理 `norm_cfcₙ_lt`

English:
lemma norm_cfcₙ_lt
  given: {f : 𝕜 -> 𝕜} {a : A} {c : Real} (h : forall x in σₙ 𝕜 a, ‖f x‖ < c)
  proof: by
  refine cfcₙ_cases (‖·‖ < c) a f ?_ fun hf hf0 ha => ?_
· simpa using (norm_nonneg _).trans_lt h 0 (quasispectrum.zero_mem 𝕜 a)
  · simp only [← cfcₙ_apply f a, (IsGreatest.norm_cfcₙ f a hf hf0 ha |>.lt_iff)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx

中文:
引理 norm_cfcₙ_lt
  条件: {f : 𝕜 -> 𝕜} {a : A} {c : 实数} (h : 对任意 x in σₙ 𝕜 a, ‖f x‖ < c)
  证明: by
  refine cfcₙ_cases (‖·‖ < c) a f ?_ fun hf hf0 ha => ?_
· simpa using (norm_nonneg _).trans_lt h 0 (quasispectrum.zero_mem 𝕜 a)
  · simp only [← cfcₙ_apply f a, (IsGreatest.norm_cfcₙ f a hf hf0 ha |>.lt_iff)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx

Depends on / 依赖: IsGreatest, IsGreatest.norm_cfc, lt_iff, norm_nonneg, quasispectrum, quasispectrum.zero_mem, trans_lt, zero_mem
-/
lemma norm_cfcₙ_lt {f : 𝕜 -> 𝕜} {a : A} {c : Real} (h : forall x in σₙ 𝕜 a, ‖f x‖ < c) :
    ‖cfcₙ f a‖ < c := by
  refine cfcₙ_cases (‖·‖ < c) a f ?_ fun hf hf0 ha => ?_
· simpa using (norm_nonneg _).trans_lt h 0 (quasispectrum.zero_mem 𝕜 a)
  · simp only [← cfcₙ_apply f a, (IsGreatest.norm_cfcₙ f a hf hf0 ha |>.lt_iff)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx

/--
lemma `norm_cfcₙ_lt_iff` / 引理 `norm_cfcₙ_lt_iff`

English:
lemma norm_cfcₙ_lt_iff
  statement: (f : 𝕜 -> 𝕜) (a : A) (c : Real)
  proof: .trans_lt h, norm_cfcₙ_lt⟩ ⟨fun h _ hx => norm_apply_le_norm_cfcₙ f a hx hf hf₀ ha

中文:
引理 norm_cfcₙ_lt_iff
  结论: (f : 𝕜 -> 𝕜) (a : A) (c : 实数)
  证明: .trans_lt h, norm_cfcₙ_lt⟩ ⟨fun h _ hx => norm_apply_le_norm_cfcₙ f a hx hf hf₀ ha

Depends on / 依赖: cfc_cont_tac, cfc_tac, cfc_zero_tac, trans_lt
-/
lemma norm_cfcₙ_lt_iff (f : 𝕜 -> 𝕜) (a : A) (c : Real)
    (hf : ContinuousOn f (σₙ 𝕜 a) := by cfc_cont_tac) (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) : ‖cfcₙ f a‖ < c ↔ forall x in σₙ 𝕜 a, ‖f x‖ < c :=
.trans_lt h, norm_cfcₙ_lt⟩ ⟨fun h _ hx => norm_apply_le_norm_cfcₙ f a hx hf hf₀ ha

open NNReal

/--
lemma `nnnorm_cfcₙ_le` / 引理 `nnnorm_cfcₙ_le`

English:
lemma nnnorm_cfcₙ_le
  given: {f : 𝕜 -> 𝕜} {a : A} {c : Real>=0} (h : forall x in σₙ 𝕜 a, ‖f x‖₊ <= c)
  proof: norm_cfcₙ_le h

中文:
引理 nnnorm_cfcₙ_le
  条件: {f : 𝕜 -> 𝕜} {a : A} {c : 实数>=0} (h : 对任意 x in σₙ 𝕜 a, ‖f x‖₊ <= c)
  证明: norm_cfcₙ_le h
-/
lemma nnnorm_cfcₙ_le {f : 𝕜 -> 𝕜} {a : A} {c : Real>=0} (h : forall x in σₙ 𝕜 a, ‖f x‖₊ <= c) :
    ‖cfcₙ f a‖₊ <= c :=
  norm_cfcₙ_le h

/--
lemma `nnnorm_cfcₙ_le_iff` / 引理 `nnnorm_cfcₙ_le_iff`

English:
lemma nnnorm_cfcₙ_le_iff
  statement: (f : 𝕜 -> 𝕜) (a : A) (c : Real>=0)
  proof: norm_cfcₙ_le_iff f a c.1 hf hf₀ ha

中文:
引理 nnnorm_cfcₙ_le_iff
  结论: (f : 𝕜 -> 𝕜) (a : A) (c : 实数>=0)
  证明: norm_cfcₙ_le_iff f a c.1 hf hf₀ ha

Depends on / 依赖: cfc_cont_tac, cfc_tac, cfc_zero_tac
-/
lemma nnnorm_cfcₙ_le_iff (f : 𝕜 -> 𝕜) (a : A) (c : Real>=0)
    (hf : ContinuousOn f (σₙ 𝕜 a) := by cfc_cont_tac) (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) : ‖cfcₙ f a‖₊ <= c ↔ forall x in σₙ 𝕜 a, ‖f x‖₊ <= c :=
  norm_cfcₙ_le_iff f a c.1 hf hf₀ ha

/--
lemma `nnnorm_cfcₙ_lt` / 引理 `nnnorm_cfcₙ_lt`

English:
lemma nnnorm_cfcₙ_lt
  given: {f : 𝕜 -> 𝕜} {a : A} {c : Real>=0} (h : forall x in σₙ 𝕜 a, ‖f x‖₊ < c)
  proof: norm_cfcₙ_lt h

中文:
引理 nnnorm_cfcₙ_lt
  条件: {f : 𝕜 -> 𝕜} {a : A} {c : 实数>=0} (h : 对任意 x in σₙ 𝕜 a, ‖f x‖₊ < c)
  证明: norm_cfcₙ_lt h
-/
lemma nnnorm_cfcₙ_lt {f : 𝕜 -> 𝕜} {a : A} {c : Real>=0} (h : forall x in σₙ 𝕜 a, ‖f x‖₊ < c) :
    ‖cfcₙ f a‖₊ < c :=
  norm_cfcₙ_lt h

/--
lemma `nnnorm_cfcₙ_lt_iff` / 引理 `nnnorm_cfcₙ_lt_iff`

English:
lemma nnnorm_cfcₙ_lt_iff
  statement: (f : 𝕜 -> 𝕜) (a : A) (c : Real>=0)
  proof: norm_cfcₙ_lt_iff f a c.1 hf hf₀ ha

中文:
引理 nnnorm_cfcₙ_lt_iff
  结论: (f : 𝕜 -> 𝕜) (a : A) (c : 实数>=0)
  证明: norm_cfcₙ_lt_iff f a c.1 hf hf₀ ha

Depends on / 依赖: cfc_cont_tac, cfc_tac, cfc_zero_tac
-/
lemma nnnorm_cfcₙ_lt_iff (f : 𝕜 -> 𝕜) (a : A) (c : Real>=0)
    (hf : ContinuousOn f (σₙ 𝕜 a) := by cfc_cont_tac) (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) : ‖cfcₙ f a‖₊ < c ↔ forall x in σₙ 𝕜 a, ‖f x‖₊ < c :=
  norm_cfcₙ_lt_iff f a c.1 hf hf₀ ha

namespace NonUnitalIsometricContinuousFunctionalCalculus

/--
lemma `isGreatest_norm_quasispectrum` / 引理 `isGreatest_norm_quasispectrum`

English:
lemma isGreatest_norm_quasispectrum
  given: (a : A) (ha : p a := by cfc_tac)
  proof: by
  simpa only [cfcₙ_id 𝕜 a] using! IsGreatest.norm_cfcₙ (id : 𝕜 -> 𝕜) a

中文:
引理 isGreatest_norm_quasispectrum
  条件: (a : A) (ha : p a := by cfc_tac)
  证明: by
  simpa only [cfcₙ_id 𝕜 a] using! IsGreatest.norm_cfcₙ (id : 𝕜 -> 𝕜) a

Depends on / 依赖: IsGreatest, IsGreatest.norm_cfc, cfc_tac
-/
lemma isGreatest_norm_quasispectrum (a : A) (ha : p a := by cfc_tac) :
    IsGreatest ((‖·‖) '' σₙ 𝕜 a) ‖a‖ := by
  simpa only [cfcₙ_id 𝕜 a] using! IsGreatest.norm_cfcₙ (id : 𝕜 -> 𝕜) a

/--
lemma `norm_quasispectrum_le` / 引理 `norm_quasispectrum_le`

English:
lemma norm_quasispectrum_le
  given: (a : A) ⦃x
  statement: 𝕜⦄ (hx : x in σₙ 𝕜 a) (ha : p a := by cfc_tac) :
  proof: by
  simpa only [cfcₙ_id 𝕜 a] using! norm_apply_le_norm_cfcₙ (id : 𝕜 -> 𝕜) a hx

中文:
引理 norm_quasispectrum_le
  条件: (a : A) ⦃x
  结论: 𝕜⦄ (hx : x in σₙ 𝕜 a) (ha : p a := by cfc_tac) :
  证明: by
  simpa only [cfcₙ_id 𝕜 a] using! norm_apply_le_norm_cfcₙ (id : 𝕜 -> 𝕜) a hx

Depends on / 依赖: cfc_tac
-/
lemma norm_quasispectrum_le (a : A) ⦃x : 𝕜⦄ (hx : x in σₙ 𝕜 a) (ha : p a := by cfc_tac) :
    ‖x‖ <= ‖a‖ := by
  simpa only [cfcₙ_id 𝕜 a] using! norm_apply_le_norm_cfcₙ (id : 𝕜 -> 𝕜) a hx

/--
lemma `isGreatest_nnnorm_quasispectrum` / 引理 `isGreatest_nnnorm_quasispectrum`

English:
lemma isGreatest_nnnorm_quasispectrum
  given: (a : A) (ha : p a := by cfc_tac)
  proof: by
  simpa only [cfcₙ_id 𝕜 a] using! IsGreatest.nnnorm_cfcₙ (id : 𝕜 -> 𝕜) a

中文:
引理 isGreatest_nnnorm_quasispectrum
  条件: (a : A) (ha : p a := by cfc_tac)
  证明: by
  simpa only [cfcₙ_id 𝕜 a] using! IsGreatest.nnnorm_cfcₙ (id : 𝕜 -> 𝕜) a

Depends on / 依赖: IsGreatest, IsGreatest.nnnorm_cfc, cfc_tac
-/
lemma isGreatest_nnnorm_quasispectrum (a : A) (ha : p a := by cfc_tac) :
    IsGreatest ((‖·‖₊) '' σₙ 𝕜 a) ‖a‖₊ := by
  simpa only [cfcₙ_id 𝕜 a] using! IsGreatest.nnnorm_cfcₙ (id : 𝕜 -> 𝕜) a

/--
lemma `nnnorm_quasispectrum_le` / 引理 `nnnorm_quasispectrum_le`

English:
lemma nnnorm_quasispectrum_le
  given: (a : A) ⦃x
  statement: 𝕜⦄ (hx : x in σₙ 𝕜 a) (ha : p a := by cfc_tac) :
  proof: by
  simpa only [cfcₙ_id 𝕜 a] using! nnnorm_apply_le_nnnorm_cfcₙ (id : 𝕜 -> 𝕜) a hx

中文:
引理 nnnorm_quasispectrum_le
  条件: (a : A) ⦃x
  结论: 𝕜⦄ (hx : x in σₙ 𝕜 a) (ha : p a := by cfc_tac) :
  证明: by
  simpa only [cfcₙ_id 𝕜 a] using! nnnorm_apply_le_nnnorm_cfcₙ (id : 𝕜 -> 𝕜) a hx

Depends on / 依赖: cfc_tac
-/
lemma nnnorm_quasispectrum_le (a : A) ⦃x : 𝕜⦄ (hx : x in σₙ 𝕜 a) (ha : p a := by cfc_tac) :
    ‖x‖₊ <= ‖a‖₊ := by
  simpa only [cfcₙ_id 𝕜 a] using! nnnorm_apply_le_nnnorm_cfcₙ (id : 𝕜 -> 𝕜) a hx

end NonUnitalIsometricContinuousFunctionalCalculus

end NormedRing

namespace QuasispectrumRestricts

open NonUnitalIsometricContinuousFunctionalCalculus

variable {R S A : Type*} {p q : A -> Prop}
variable [Semifield R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
variable [Field S] [StarRing S] [MetricSpace S] [IsTopologicalRing S] [ContinuousStar S]
variable [NonUnitalRing A] [StarRing A] [Module S A] [IsScalarTower S A A]
variable [SMulCommClass S A A]
variable [Algebra R S] [Module R A] [IsScalarTower R S A] [StarModule R S] [ContinuousSMul R S]
variable [IsScalarTower R A A] [SMulCommClass R A A]
variable [MetricSpace A] [NonUnitalIsometricContinuousFunctionalCalculus S A q]
variable [CompleteSpace R] [ContinuousMapZero.UniqueHom R A]

set_option backward.isDefEq.respectTransparency.types false in
open scoped NonUnitalContinuousFunctionalCalculus in
/--
theorem `isometric_cfc` / 定理 `isometric_cfc`

English:
theorem isometric_cfc
  statement: (f : C(S, R)) (halg : Isometry (algebraMap R S)) (h0 : p 0)
  proof: QuasispectrumRestricts.cfc f
    halg.isClosedEmbedding h0 h
  isometric a ha := by
.mp ha obtain ⟨ha', haf⟩ := h a
    have := QuasispectrumRestricts.cfc f halg.isClosedEmbedding h0 h
    rw [cfcₙHom_eq_restrict f ha ha' haf]
    refine .of_dist_eq fun g₁ g₂ => ?_
    simp only [nonUnitalStarAlgHom

中文:
定理 isometric_cfc
  结论: (f : C(S, R)) (halg : 等距 (algebraMap R S)) (h0 : p 0)
  证明: QuasispectrumRestricts.cfc f
    halg.isClosedEmbedding h0 h
  isometric a ha := by
.mp ha obtain ⟨ha', haf⟩ := h a
    have := QuasispectrumRestricts.cfc f halg.isClosedEmbedding h0 h
    rw [cfcₙHom_eq_restrict f ha ha' haf]
    refine .of_dist_eq fun g₁ g₂ => ?_
    simp only [nonUnitalStarAlgHom
-/
protected theorem isometric_cfc (f : C(S, R)) (halg : Isometry (algebraMap R S)) (h0 : p 0)
    (h : forall a, p a ↔ q a ∧ QuasispectrumRestricts a f) :
    NonUnitalIsometricContinuousFunctionalCalculus R A p where
  toNonUnitalContinuousFunctionalCalculus := QuasispectrumRestricts.cfc f
    halg.isClosedEmbedding h0 h
  isometric a ha := by
.mp ha obtain ⟨ha', haf⟩ := h a
    have := QuasispectrumRestricts.cfc f halg.isClosedEmbedding h0 h
    rw [cfcₙHom_eq_restrict f ha ha' haf]
    refine .of_dist_eq fun g₁ g₂ => ?_
    simp only [nonUnitalStarAlgHom_apply, isometry_cfcₙHom a ha' |>.dist_eq]
    refine le_antisymm ?_ ?_
.mpr fun x => ?_ all_goals refine ContinuousMap.dist_le dist_nonneg
    · simpa [halg.dist_eq] using! ContinuousMap.dist_apply_le_dist _
    · let x' : σₙ S a := Subtype.map (algebraMap R S) (fun _ => quasispectrum.algebraMap_mem S) x
apply le_of_eq_of_le ?_ ContinuousMap.dist_apply_le_dist x'
      simp only [ContinuousMapZero.comp_apply, ContinuousMapZero.coe_mk,
        ContinuousMap.coe_mk, StarAlgHom.ofId_apply, halg.dist_eq, x']
      congr! 2
.symm all_goals ext; exact haf.left_inv _

end QuasispectrumRestricts

end NonUnital

/-! ### Instances of isometric continuous functional calculi

The instances for `ℝ` and `ℂ` can be found in
`Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Basic.lean`, as those require an actual
`CStarAlgebra` instance on `A`, whereas the one for `ℝ≥0` is simply inherited from an existing
instance for `ℝ`.
-/

section Instances

section Unital

variable {A : Type*} [NormedRing A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
variable [NormedAlgebra Real A] [IsometricContinuousFunctionalCalculus Real A IsSelfAdjoint]
variable [NonnegSpectrumClass Real A]

open NNReal in
/--
Instance `Nonneg.instIsometricContinuousFunctionalCalculus` / 实例 `Nonneg.instIsometricContinuousFunctionalCalculus`

English:
instance Nonneg.instIsometricContinuousFunctionalCalculus
  signature: :
  body: SpectrumRestricts.isometric_cfc (q := IsSelfAdjoint) ContinuousMap.realToNNReal
    NNReal.isometry_coe le_rfl (fun _ => nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts)

中文:
实例 Nonneg.instIsometricContinuousFunctionalCalculus
  签名: :
  定义体: SpectrumRestricts.isometric_cfc (q := IsSelfAdjoint) ContinuousMap.realToNNReal
    NNReal.isometry_coe le_rfl (fun _ => nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts)

Depends on / 依赖: ContinuousMap, ContinuousMap.realToNNReal, IsSelfAdjoint, NNReal, NNReal.isometry_coe, SpectrumRestricts, SpectrumRestricts.isometric_cfc, isometric_cfc, isometry_coe, le_rfl, nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts, realToNNReal
-/
instance Nonneg.instIsometricContinuousFunctionalCalculus :
    IsometricContinuousFunctionalCalculus Real>=0 A (0 <= ·) :=
  SpectrumRestricts.isometric_cfc (q := IsSelfAdjoint) ContinuousMap.realToNNReal
    NNReal.isometry_coe le_rfl (fun _ => nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts)

end Unital

section NonUnital

variable {A : Type*} [NonUnitalNormedRing A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
variable [NormedSpace Real A] [IsScalarTower Real A A] [SMulCommClass Real A A]
variable [NonUnitalIsometricContinuousFunctionalCalculus Real A IsSelfAdjoint]
variable [NonnegSpectrumClass Real A]

open NNReal in
/--
Instance `Nonneg.instNonUnitalIsometricContinuousFunctionalCalculus` / 实例 `Nonneg.instNonUnitalIsometricContinuousFunctionalCalculus`

English:
instance Nonneg.instNonUnitalIsometricContinuousFunctionalCalculus
  signature: :
  body: QuasispectrumRestricts.isometric_cfc (q := IsSelfAdjoint) ContinuousMap.realToNNReal
    NNReal.isometry_coe le_rfl (fun _ => nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts)

中文:
实例 Nonneg.instNonUnitalIsometricContinuousFunctionalCalculus
  签名: :
  定义体: QuasispectrumRestricts.isometric_cfc (q := IsSelfAdjoint) ContinuousMap.realToNNReal
    NNReal.isometry_coe le_rfl (fun _ => nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts)

Depends on / 依赖: ContinuousMap, ContinuousMap.realToNNReal, IsSelfAdjoint, NNReal, NNReal.isometry_coe, QuasispectrumRestricts, QuasispectrumRestricts.isometric_cfc, isometric_cfc, isometry_coe, le_rfl, nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts, realToNNReal
-/
instance Nonneg.instNonUnitalIsometricContinuousFunctionalCalculus :
    NonUnitalIsometricContinuousFunctionalCalculus Real>=0 A (0 <= ·) :=
  QuasispectrumRestricts.isometric_cfc (q := IsSelfAdjoint) ContinuousMap.realToNNReal
    NNReal.isometry_coe le_rfl (fun _ => nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts)

end NonUnital

end Instances

/-! ### Properties specific to `ℝ≥0` -/

section NNReal

open NNReal

section Unital

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra Real A] [PartialOrder A]
variable [StarOrderedRing A] [IsometricContinuousFunctionalCalculus Real A IsSelfAdjoint]
variable [NonnegSpectrumClass Real A]

/--
lemma `IsGreatest.nnnorm_cfc_nnreal` / 引理 `IsGreatest.nnnorm_cfc_nnreal`

English:
lemma IsGreatest.nnnorm_cfc_nnreal
  statement: [Nontrivial A] (f : Real>=0 -> Real>=0) (a : A)
  proof: by
  rw [cfc_nnreal_eq_real ..]
  obtain ⟨-, ha'⟩ := nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts.mp ha
  rw [← SpectrumRestricts] at ha'
  convert! IsGreatest.nnnorm_cfc (fun x : Real => (f x.toNNReal : Real)) a ?hf_cont
case hf_cont => exact continuous_subtype_val.comp_continuousOn
Continuo

中文:
引理 IsGreatest.nnnorm_cfc_nnreal
  结论: [非平凡 A] (f : 实数>=0 -> 实数>=0) (a : A)
  证明: by
  rw [cfc_nnreal_eq_real ..]
  obtain ⟨-, ha'⟩ := nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts.mp ha
  rw [← SpectrumRestricts] at ha'
  convert! IsGreatest.nnnorm_cfc (fun x : Real => (f x.toNNReal : Real)) a ?hf_cont
case hf_cont => exact continuous_subtype_val.comp_continuousOn
Continuo

Depends on / 依赖: ContinuousOn, ContinuousOn.comp, IsGreatest, IsGreatest.nnnorm_cfc, Set.image_image, Set.mapsTo_image, SpectrumRestricts, cfc_cont_tac, cfc_nnreal_eq_real, cfc_tac, comp_continuousOn, continuousOn, continuous_real_toNNReal, continuous_real_toNNReal.continuousOn, continuous_subtype_val, continuous_subtype_val.comp_continuousOn, convert, hf_cont, image_image, mapsTo_image
-/
lemma IsGreatest.nnnorm_cfc_nnreal [Nontrivial A] (f : Real>=0 -> Real>=0) (a : A)
    (hf : ContinuousOn f (σ Real>=0 a) := by cfc_cont_tac) (ha : 0 <= a := by cfc_tac) :
    IsGreatest (f '' σ Real>=0 a) ‖cfc f a‖₊ := by
  rw [cfc_nnreal_eq_real ..]
  obtain ⟨-, ha'⟩ := nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts.mp ha
  rw [← SpectrumRestricts] at ha'
  convert! IsGreatest.nnnorm_cfc (fun x : Real => (f x.toNNReal : Real)) a ?hf_cont
case hf_cont => exact continuous_subtype_val.comp_continuousOn
ContinuousOn.comp ‹_› continuous_real_toNNReal.continuousOn ha'.image ▸ Set.mapsTo_image ..
  simp [Set.image_image, ← ha'.image]

/--
lemma `apply_le_nnnorm_cfc_nnreal` / 引理 `apply_le_nnnorm_cfc_nnreal`

English:
lemma apply_le_nnnorm_cfc_nnreal
  given: (f : Real>=0 -> Real>=0) (a : A) ⦃x
  statement: Real>=0⦄ (hx : x in σ Real>=0 a)
  proof: by
  revert hx
  nontriviality A
  exact (IsGreatest.nnnorm_cfc_nnreal f a hf ha |>.2 ⟨x, ·, rfl⟩)

中文:
引理 apply_le_nnnorm_cfc_nnreal
  条件: (f : 实数>=0 -> 实数>=0) (a : A) ⦃x
  结论: 实数>=0⦄ (hx : x in σ 实数>=0 a)
  证明: by
  revert hx
  nontriviality A
  exact (IsGreatest.nnnorm_cfc_nnreal f a hf ha |>.2 ⟨x, ·, rfl⟩)

Depends on / 依赖: IsGreatest, IsGreatest.nnnorm_cfc_nnreal, cfc_cont_tac, cfc_tac, nnnorm_cfc_nnreal, nontriviality, revert
-/
lemma apply_le_nnnorm_cfc_nnreal (f : Real>=0 -> Real>=0) (a : A) ⦃x : Real>=0⦄ (hx : x in σ Real>=0 a)
    (hf : ContinuousOn f (σ Real>=0 a) := by cfc_cont_tac) (ha : 0 <= a := by cfc_tac) :
    f x <= ‖cfc f a‖₊ := by
  revert hx
  nontriviality A
  exact (IsGreatest.nnnorm_cfc_nnreal f a hf ha |>.2 ⟨x, ·, rfl⟩)

/--
lemma `nnnorm_cfc_nnreal_le` / 引理 `nnnorm_cfc_nnreal_le`

English:
lemma nnnorm_cfc_nnreal_le
  given: {f : Real>=0 -> Real>=0} {a : A} {c : Real>=0} (h : forall x in σ Real>=0 a, f x <= c)
  proof: by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · rw [Subsingleton.elim (cfc f a) 0]
    simp
  · refine cfc_cases (‖·‖₊ <= c) a f (by simp) fun hf ha => ?_
    simp only [← cfc_apply f a, isLUB_le_iff (IsGreatest.nnnorm_cfc_nnreal f a hf ha |>.isLUB)]
    rintro - ⟨x, hx, rfl⟩
    exact h x h

中文:
引理 nnnorm_cfc_nnreal_le
  条件: {f : 实数>=0 -> 实数>=0} {a : A} {c : 实数>=0} (h : 对任意 x in σ 实数>=0 a, f x <= c)
  证明: by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · rw [Subsingleton.elim (cfc f a) 0]
    simp
  · refine cfc_cases (‖·‖₊ <= c) a f (by simp) fun hf ha => ?_
    simp only [← cfc_apply f a, isLUB_le_iff (IsGreatest.nnnorm_cfc_nnreal f a hf ha |>.isLUB)]
    rintro - ⟨x, hx, rfl⟩
    exact h x h

Depends on / 依赖: IsGreatest, IsGreatest.nnnorm_cfc_nnreal, Subsingleton, Subsingleton.elim, cfc_apply, cfc_cases, isLUB_le_iff, nnnorm_cfc_nnreal, subsingleton_or_nontrivial
-/
lemma nnnorm_cfc_nnreal_le {f : Real>=0 -> Real>=0} {a : A} {c : Real>=0} (h : forall x in σ Real>=0 a, f x <= c) :
    ‖cfc f a‖₊ <= c := by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · rw [Subsingleton.elim (cfc f a) 0]
    simp
  · refine cfc_cases (‖·‖₊ <= c) a f (by simp) fun hf ha => ?_
    simp only [← cfc_apply f a, isLUB_le_iff (IsGreatest.nnnorm_cfc_nnreal f a hf ha |>.isLUB)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx

/--
lemma `nnnorm_cfc_nnreal_le_iff` / 引理 `nnnorm_cfc_nnreal_le_iff`

English:
lemma nnnorm_cfc_nnreal_le_iff
  statement: (f : Real>=0 -> Real>=0) (a : A) (c : Real>=0)
  proof: .trans h, nnnorm_cfc_nnreal_le⟩ ⟨fun h _ hx => apply_le_nnnorm_cfc_nnreal f a hx hf ha

中文:
引理 nnnorm_cfc_nnreal_le_iff
  结论: (f : 实数>=0 -> 实数>=0) (a : A) (c : 实数>=0)
  证明: .trans h, nnnorm_cfc_nnreal_le⟩ ⟨fun h _ hx => apply_le_nnnorm_cfc_nnreal f a hx hf ha

Depends on / 依赖: apply_le_nnnorm_cfc_nnreal, cfc_cont_tac, cfc_tac, nnnorm_cfc_nnreal_le
-/
lemma nnnorm_cfc_nnreal_le_iff (f : Real>=0 -> Real>=0) (a : A) (c : Real>=0)
    (hf : ContinuousOn f (σ Real>=0 a) := by cfc_cont_tac)
    (ha : 0 <= a := by cfc_tac) : ‖cfc f a‖₊ <= c ↔ forall x in σ Real>=0 a, f x <= c :=
.trans h, nnnorm_cfc_nnreal_le⟩ ⟨fun h _ hx => apply_le_nnnorm_cfc_nnreal f a hx hf ha

/--
lemma `nnnorm_cfc_nnreal_lt` / 引理 `nnnorm_cfc_nnreal_lt`

English:
lemma nnnorm_cfc_nnreal_lt
  statement: {f : Real>=0 -> Real>=0} {a : A} {c : Real>=0} (hc : 0 < c)
  proof: by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · rw [Subsingleton.elim (cfc f a) 0]
    simpa
  · refine cfc_cases (‖·‖₊ < c) a f (by simpa) fun hf ha => ?_
    simp only [← cfc_apply f a, (IsGreatest.nnnorm_cfc_nnreal f a hf ha |>.lt_iff)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx

中文:
引理 nnnorm_cfc_nnreal_lt
  结论: {f : 实数>=0 -> 实数>=0} {a : A} {c : 实数>=0} (hc : 0 < c)
  证明: by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · rw [Subsingleton.elim (cfc f a) 0]
    simpa
  · refine cfc_cases (‖·‖₊ < c) a f (by simpa) fun hf ha => ?_
    simp only [← cfc_apply f a, (IsGreatest.nnnorm_cfc_nnreal f a hf ha |>.lt_iff)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx

Depends on / 依赖: IsGreatest, IsGreatest.nnnorm_cfc_nnreal, Subsingleton, Subsingleton.elim, cfc_apply, cfc_cases, lt_iff, nnnorm_cfc_nnreal, subsingleton_or_nontrivial
-/
lemma nnnorm_cfc_nnreal_lt {f : Real>=0 -> Real>=0} {a : A} {c : Real>=0} (hc : 0 < c)
    (h : forall x in σ Real>=0 a, f x < c) : ‖cfc f a‖₊ < c := by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · rw [Subsingleton.elim (cfc f a) 0]
    simpa
  · refine cfc_cases (‖·‖₊ < c) a f (by simpa) fun hf ha => ?_
    simp only [← cfc_apply f a, (IsGreatest.nnnorm_cfc_nnreal f a hf ha |>.lt_iff)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx

/--
lemma `nnnorm_cfc_nnreal_lt_iff` / 引理 `nnnorm_cfc_nnreal_lt_iff`

English:
lemma nnnorm_cfc_nnreal_lt_iff
  statement: (f : Real>=0 -> Real>=0) (a : A) {c : Real>=0} (hc : 0 < c)
  proof: .trans_lt h, nnnorm_cfc_nnreal_lt hc⟩ ⟨fun h _ hx => apply_le_nnnorm_cfc_nnreal f a hx hf ha

中文:
引理 nnnorm_cfc_nnreal_lt_iff
  结论: (f : 实数>=0 -> 实数>=0) (a : A) {c : 实数>=0} (hc : 0 < c)
  证明: .trans_lt h, nnnorm_cfc_nnreal_lt hc⟩ ⟨fun h _ hx => apply_le_nnnorm_cfc_nnreal f a hx hf ha

Depends on / 依赖: apply_le_nnnorm_cfc_nnreal, cfc_cont_tac, cfc_tac, nnnorm_cfc_nnreal_lt, trans_lt
-/
lemma nnnorm_cfc_nnreal_lt_iff (f : Real>=0 -> Real>=0) (a : A) {c : Real>=0} (hc : 0 < c)
    (hf : ContinuousOn f (σ Real>=0 a) := by cfc_cont_tac)
    (ha : 0 <= a := by cfc_tac) : ‖cfc f a‖₊ < c ↔ forall x in σ Real>=0 a, f x < c :=
.trans_lt h, nnnorm_cfc_nnreal_lt hc⟩ ⟨fun h _ hx => apply_le_nnnorm_cfc_nnreal f a hx hf ha

namespace IsometricContinuousFunctionalCalculus

/--
lemma `isGreatest_spectrum` / 引理 `isGreatest_spectrum`

English:
lemma isGreatest_spectrum
  given: [Nontrivial A] (a : A) (ha : 0 <= a := by cfc_tac)
  proof: by
  simpa [cfc_id Real>=0 a] using IsGreatest.nnnorm_cfc_nnreal id a

中文:
引理 isGreatest_spectrum
  条件: [非平凡 A] (a : A) (ha : 0 <= a := by cfc_tac)
  证明: by
  simpa [cfc_id Real>=0 a] using IsGreatest.nnnorm_cfc_nnreal id a

Depends on / 依赖: IsGreatest, IsGreatest.nnnorm_cfc_nnreal, cfc_id, cfc_tac, nnnorm_cfc_nnreal
-/
lemma isGreatest_spectrum [Nontrivial A] (a : A) (ha : 0 <= a := by cfc_tac) :
    IsGreatest (σ Real>=0 a) ‖a‖₊ := by
  simpa [cfc_id Real>=0 a] using IsGreatest.nnnorm_cfc_nnreal id a

/--
lemma `spectrum_le` / 引理 `spectrum_le`

English:
lemma spectrum_le
  given: (a : A) ⦃x
  statement: Real>=0⦄ (hx : x in σ Real>=0 a) (ha : 0 <= a := by cfc_tac) :
  proof: by
  simpa [cfc_id Real>=0 a] using apply_le_nnnorm_cfc_nnreal id a hx

中文:
引理 spectrum_le
  条件: (a : A) ⦃x
  结论: 实数>=0⦄ (hx : x in σ 实数>=0 a) (ha : 0 <= a := by cfc_tac) :
  证明: by
  simpa [cfc_id Real>=0 a] using apply_le_nnnorm_cfc_nnreal id a hx

Depends on / 依赖: apply_le_nnnorm_cfc_nnreal, cfc_id, cfc_tac
-/
lemma spectrum_le (a : A) ⦃x : Real>=0⦄ (hx : x in σ Real>=0 a) (ha : 0 <= a := by cfc_tac) :
    x <= ‖a‖₊ := by
  simpa [cfc_id Real>=0 a] using apply_le_nnnorm_cfc_nnreal id a hx

end IsometricContinuousFunctionalCalculus

open IsometricContinuousFunctionalCalculus in
/--
lemma `MonotoneOn.nnnorm_cfc` / 引理 `MonotoneOn.nnnorm_cfc`

English:
lemma MonotoneOn.nnnorm_cfc
  statement: [Nontrivial A] (f : Real>=0 -> Real>=0) (a : A)
  proof: .unique hf.map_isGreatest (isGreatest_spectrum a) IsGreatest.nnnorm_cfc_nnreal f a

中文:
引理 MonotoneOn.nnnorm_cfc
  结论: [非平凡 A] (f : 实数>=0 -> 实数>=0) (a : A)
  证明: .unique hf.map_isGreatest (isGreatest_spectrum a) IsGreatest.nnnorm_cfc_nnreal f a

Depends on / 依赖: IsGreatest, IsGreatest.nnnorm_cfc_nnreal, cfc_cont_tac, cfc_tac, hf.map_isGreatest, isGreatest_spectrum, map_isGreatest, nnnorm_cfc_nnreal, unique
-/
lemma MonotoneOn.nnnorm_cfc [Nontrivial A] (f : Real>=0 -> Real>=0) (a : A)
    (hf : MonotoneOn f (σ Real>=0 a)) (hf₂ : ContinuousOn f (σ Real>=0 a) := by cfc_cont_tac)
    (ha : 0 <= a := by cfc_tac) : ‖cfc f a‖₊ = f ‖a‖₊ :=
.unique hf.map_isGreatest (isGreatest_spectrum a) IsGreatest.nnnorm_cfc_nnreal f a

end Unital

section NonUnital

variable {A : Type*} [NonUnitalNormedRing A] [StarRing A] [NormedSpace Real A]
variable [IsScalarTower Real A A] [SMulCommClass Real A A] [PartialOrder A]
variable [StarOrderedRing A] [NonUnitalIsometricContinuousFunctionalCalculus Real A IsSelfAdjoint]
variable [NonnegSpectrumClass Real A]

/--
lemma `IsGreatest.nnnorm_cfcₙ_nnreal` / 引理 `IsGreatest.nnnorm_cfcₙ_nnreal`

English:
lemma IsGreatest.nnnorm_cfcₙ_nnreal
  statement: (f : Real>=0 -> Real>=0) (a : A)
  proof: by
  rw [cfcₙ_nnreal_eq_real ..]
  obtain ⟨-, ha'⟩ := nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts.mp ha
  convert! IsGreatest.nnnorm_cfcₙ (fun x : Real => (f x.toNNReal : Real)) a ?hf_cont (by simpa)
case hf_cont => exact continuous_subtype_val.comp_continuousOn
ContinuousOn.comp ‹_› continu

中文:
引理 IsGreatest.nnnorm_cfcₙ_nnreal
  结论: (f : 实数>=0 -> 实数>=0) (a : A)
  证明: by
  rw [cfcₙ_nnreal_eq_real ..]
  obtain ⟨-, ha'⟩ := nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts.mp ha
  convert! IsGreatest.nnnorm_cfcₙ (fun x : Real => (f x.toNNReal : Real)) a ?hf_cont (by simpa)
case hf_cont => exact continuous_subtype_val.comp_continuousOn
ContinuousOn.comp ‹_› continu

Depends on / 依赖: ContinuousOn, ContinuousOn.comp, IsGreatest, IsGreatest.nnnorm_cfc, Set.image, Set.mapsTo_image, cfc_cont_tac, cfc_tac, cfc_zero_tac, comp_continuousOn, continuousOn, continuous_real_toNNReal, continuous_real_toNNReal.continuousOn, continuous_subtype_val, continuous_subtype_val.comp_continuousOn, convert, hf_cont, mapsTo_image, nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts, nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts.mp
-/
lemma IsGreatest.nnnorm_cfcₙ_nnreal (f : Real>=0 -> Real>=0) (a : A)
    (hf : ContinuousOn f (σₙ Real>=0 a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (ha : 0 <= a := by cfc_tac) : IsGreatest (f '' σₙ Real>=0 a) ‖cfcₙ f a‖₊ := by
  rw [cfcₙ_nnreal_eq_real ..]
  obtain ⟨-, ha'⟩ := nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts.mp ha
  convert! IsGreatest.nnnorm_cfcₙ (fun x : Real => (f x.toNNReal : Real)) a ?hf_cont (by simpa)
case hf_cont => exact continuous_subtype_val.comp_continuousOn
ContinuousOn.comp ‹_› continuous_real_toNNReal.continuousOn ha'.image ▸ Set.mapsTo_image ..
  simp [Set.image_image, ← ha'.image]

/--
lemma `apply_le_nnnorm_cfcₙ_nnreal` / 引理 `apply_le_nnnorm_cfcₙ_nnreal`

English:
lemma apply_le_nnnorm_cfcₙ_nnreal
  given: (f : Real>=0 -> Real>=0) (a : A) ⦃x
  statement: Real>=0⦄ (hx : x in σₙ Real>=0 a)
  proof: by
  revert hx
  exact (IsGreatest.nnnorm_cfcₙ_nnreal f a hf hf0 ha |>.2 ⟨x, ·, rfl⟩)

中文:
引理 apply_le_nnnorm_cfcₙ_nnreal
  条件: (f : 实数>=0 -> 实数>=0) (a : A) ⦃x
  结论: 实数>=0⦄ (hx : x in σₙ 实数>=0 a)
  证明: by
  revert hx
  exact (IsGreatest.nnnorm_cfcₙ_nnreal f a hf hf0 ha |>.2 ⟨x, ·, rfl⟩)

Depends on / 依赖: IsGreatest, IsGreatest.nnnorm_cfc, cfc_cont_tac, cfc_tac, cfc_zero_tac, revert
-/
lemma apply_le_nnnorm_cfcₙ_nnreal (f : Real>=0 -> Real>=0) (a : A) ⦃x : Real>=0⦄ (hx : x in σₙ Real>=0 a)
    (hf : ContinuousOn f (σₙ Real>=0 a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (ha : 0 <= a := by cfc_tac) : f x <= ‖cfcₙ f a‖₊ := by
  revert hx
  exact (IsGreatest.nnnorm_cfcₙ_nnreal f a hf hf0 ha |>.2 ⟨x, ·, rfl⟩)

/--
lemma `nnnorm_cfcₙ_nnreal_le` / 引理 `nnnorm_cfcₙ_nnreal_le`

English:
lemma nnnorm_cfcₙ_nnreal_le
  given: {f : Real>=0 -> Real>=0} {a : A} {c : Real>=0} (h : forall x in σₙ Real>=0 a, f x <= c)
  proof: by
  refine cfcₙ_cases (‖·‖₊ <= c) a f (by simp) fun hf hf0 ha => ?_
  simp only [← cfcₙ_apply f a, isLUB_le_iff (IsGreatest.nnnorm_cfcₙ_nnreal f a hf hf0 ha |>.isLUB)]
  rintro - ⟨x, hx, rfl⟩
  exact h x hx

中文:
引理 nnnorm_cfcₙ_nnreal_le
  条件: {f : 实数>=0 -> 实数>=0} {a : A} {c : 实数>=0} (h : 对任意 x in σₙ 实数>=0 a, f x <= c)
  证明: by
  refine cfcₙ_cases (‖·‖₊ <= c) a f (by simp) fun hf hf0 ha => ?_
  simp only [← cfcₙ_apply f a, isLUB_le_iff (IsGreatest.nnnorm_cfcₙ_nnreal f a hf hf0 ha |>.isLUB)]
  rintro - ⟨x, hx, rfl⟩
  exact h x hx

Depends on / 依赖: IsGreatest, IsGreatest.nnnorm_cfc, isLUB_le_iff
-/
lemma nnnorm_cfcₙ_nnreal_le {f : Real>=0 -> Real>=0} {a : A} {c : Real>=0} (h : forall x in σₙ Real>=0 a, f x <= c) :
    ‖cfcₙ f a‖₊ <= c := by
  refine cfcₙ_cases (‖·‖₊ <= c) a f (by simp) fun hf hf0 ha => ?_
  simp only [← cfcₙ_apply f a, isLUB_le_iff (IsGreatest.nnnorm_cfcₙ_nnreal f a hf hf0 ha |>.isLUB)]
  rintro - ⟨x, hx, rfl⟩
  exact h x hx

/--
lemma `nnnorm_cfcₙ_nnreal_le_iff` / 引理 `nnnorm_cfcₙ_nnreal_le_iff`

English:
lemma nnnorm_cfcₙ_nnreal_le_iff
  statement: (f : Real>=0 -> Real>=0) (a : A) (c : Real>=0)
  proof: .trans h, nnnorm_cfcₙ_nnreal_le⟩ ⟨fun h _ hx => apply_le_nnnorm_cfcₙ_nnreal f a hx hf hf₀ ha

中文:
引理 nnnorm_cfcₙ_nnreal_le_iff
  结论: (f : 实数>=0 -> 实数>=0) (a : A) (c : 实数>=0)
  证明: .trans h, nnnorm_cfcₙ_nnreal_le⟩ ⟨fun h _ hx => apply_le_nnnorm_cfcₙ_nnreal f a hx hf hf₀ ha

Depends on / 依赖: cfc_cont_tac, cfc_tac, cfc_zero_tac
-/
lemma nnnorm_cfcₙ_nnreal_le_iff (f : Real>=0 -> Real>=0) (a : A) (c : Real>=0)
    (hf : ContinuousOn f (σₙ Real>=0 a) := by cfc_cont_tac) (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (ha : 0 <= a := by cfc_tac) : ‖cfcₙ f a‖₊ <= c ↔ forall x in σₙ Real>=0 a, f x <= c :=
.trans h, nnnorm_cfcₙ_nnreal_le⟩ ⟨fun h _ hx => apply_le_nnnorm_cfcₙ_nnreal f a hx hf hf₀ ha

/--
lemma `nnnorm_cfcₙ_nnreal_lt` / 引理 `nnnorm_cfcₙ_nnreal_lt`

English:
lemma nnnorm_cfcₙ_nnreal_lt
  given: {f : Real>=0 -> Real>=0} {a : A} {c : Real>=0} (h : forall x in σₙ Real>=0 a, f x < c)
  proof: by
  refine cfcₙ_cases (‖·‖₊ < c) a f ?_ fun hf hf0 ha => ?_
  · simpa using (h 0 (quasispectrum.zero_mem Real>=0 _)).pos
  · simp only [← cfcₙ_apply f a, (IsGreatest.nnnorm_cfcₙ_nnreal f a hf hf0 ha |>.lt_iff)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx

中文:
引理 nnnorm_cfcₙ_nnreal_lt
  条件: {f : 实数>=0 -> 实数>=0} {a : A} {c : 实数>=0} (h : 对任意 x in σₙ 实数>=0 a, f x < c)
  证明: by
  refine cfcₙ_cases (‖·‖₊ < c) a f ?_ fun hf hf0 ha => ?_
  · simpa using (h 0 (quasispectrum.zero_mem Real>=0 _)).pos
  · simp only [← cfcₙ_apply f a, (IsGreatest.nnnorm_cfcₙ_nnreal f a hf hf0 ha |>.lt_iff)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx

Depends on / 依赖: IsGreatest, IsGreatest.nnnorm_cfc, lt_iff, quasispectrum, quasispectrum.zero_mem, zero_mem
-/
lemma nnnorm_cfcₙ_nnreal_lt {f : Real>=0 -> Real>=0} {a : A} {c : Real>=0} (h : forall x in σₙ Real>=0 a, f x < c) :
    ‖cfcₙ f a‖₊ < c := by
  refine cfcₙ_cases (‖·‖₊ < c) a f ?_ fun hf hf0 ha => ?_
  · simpa using (h 0 (quasispectrum.zero_mem Real>=0 _)).pos
  · simp only [← cfcₙ_apply f a, (IsGreatest.nnnorm_cfcₙ_nnreal f a hf hf0 ha |>.lt_iff)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx

/--
lemma `nnnorm_cfcₙ_nnreal_lt_iff` / 引理 `nnnorm_cfcₙ_nnreal_lt_iff`

English:
lemma nnnorm_cfcₙ_nnreal_lt_iff
  statement: (f : Real>=0 -> Real>=0) (a : A) (c : Real>=0)
  proof: .trans_lt h, nnnorm_cfcₙ_nnreal_lt⟩ ⟨fun h _ hx => apply_le_nnnorm_cfcₙ_nnreal f a hx hf hf₀ ha

中文:
引理 nnnorm_cfcₙ_nnreal_lt_iff
  结论: (f : 实数>=0 -> 实数>=0) (a : A) (c : 实数>=0)
  证明: .trans_lt h, nnnorm_cfcₙ_nnreal_lt⟩ ⟨fun h _ hx => apply_le_nnnorm_cfcₙ_nnreal f a hx hf hf₀ ha

Depends on / 依赖: cfc_cont_tac, cfc_tac, cfc_zero_tac, trans_lt
-/
lemma nnnorm_cfcₙ_nnreal_lt_iff (f : Real>=0 -> Real>=0) (a : A) (c : Real>=0)
    (hf : ContinuousOn f (σₙ Real>=0 a) := by cfc_cont_tac) (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (ha : 0 <= a := by cfc_tac) : ‖cfcₙ f a‖₊ < c ↔ forall x in σₙ Real>=0 a, f x < c :=
.trans_lt h, nnnorm_cfcₙ_nnreal_lt⟩ ⟨fun h _ hx => apply_le_nnnorm_cfcₙ_nnreal f a hx hf hf₀ ha

namespace NonUnitalIsometricContinuousFunctionalCalculus

/--
lemma `isGreatest_quasispectrum` / 引理 `isGreatest_quasispectrum`

English:
lemma isGreatest_quasispectrum
  given: (a : A) (ha : 0 <= a := by cfc_tac)
  proof: by
  simpa [cfcₙ_id Real>=0 a] using IsGreatest.nnnorm_cfcₙ_nnreal id a

中文:
引理 isGreatest_quasispectrum
  条件: (a : A) (ha : 0 <= a := by cfc_tac)
  证明: by
  simpa [cfcₙ_id Real>=0 a] using IsGreatest.nnnorm_cfcₙ_nnreal id a

Depends on / 依赖: IsGreatest, IsGreatest.nnnorm_cfc, cfc_tac
-/
lemma isGreatest_quasispectrum (a : A) (ha : 0 <= a := by cfc_tac) :
    IsGreatest (σₙ Real>=0 a) ‖a‖₊ := by
  simpa [cfcₙ_id Real>=0 a] using IsGreatest.nnnorm_cfcₙ_nnreal id a

/--
lemma `quasispectrum_le` / 引理 `quasispectrum_le`

English:
lemma quasispectrum_le
  given: (a : A) ⦃x
  statement: Real>=0⦄ (hx : x in σₙ Real>=0 a) (ha : 0 <= a := by cfc_tac) :
  proof: by
  simpa [cfcₙ_id Real>=0 a] using apply_le_nnnorm_cfcₙ_nnreal id a hx

中文:
引理 quasispectrum_le
  条件: (a : A) ⦃x
  结论: 实数>=0⦄ (hx : x in σₙ 实数>=0 a) (ha : 0 <= a := by cfc_tac) :
  证明: by
  simpa [cfcₙ_id Real>=0 a] using apply_le_nnnorm_cfcₙ_nnreal id a hx

Depends on / 依赖: cfc_tac
-/
lemma quasispectrum_le (a : A) ⦃x : Real>=0⦄ (hx : x in σₙ Real>=0 a) (ha : 0 <= a := by cfc_tac) :
    x <= ‖a‖₊ := by
  simpa [cfcₙ_id Real>=0 a] using apply_le_nnnorm_cfcₙ_nnreal id a hx

end NonUnitalIsometricContinuousFunctionalCalculus

open NonUnitalIsometricContinuousFunctionalCalculus in
/--
lemma `MonotoneOn.nnnorm_cfcₙ` / 引理 `MonotoneOn.nnnorm_cfcₙ`

English:
lemma MonotoneOn.nnnorm_cfcₙ
  statement: (f : Real>=0 -> Real>=0) (a : A)
  proof: .unique hf.map_isGreatest (isGreatest_quasispectrum a) IsGreatest.nnnorm_cfcₙ_nnreal f a

中文:
引理 MonotoneOn.nnnorm_cfcₙ
  结论: (f : 实数>=0 -> 实数>=0) (a : A)
  证明: .unique hf.map_isGreatest (isGreatest_quasispectrum a) IsGreatest.nnnorm_cfcₙ_nnreal f a

Depends on / 依赖: IsGreatest, IsGreatest.nnnorm_cfc, cfc_cont_tac, cfc_tac, cfc_zero_tac, hf.map_isGreatest, isGreatest_quasispectrum, map_isGreatest, unique
-/
lemma MonotoneOn.nnnorm_cfcₙ (f : Real>=0 -> Real>=0) (a : A)
    (hf : MonotoneOn f (σₙ Real>=0 a)) (hf₂ : ContinuousOn f (σₙ Real>=0 a) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : 0 <= a := by cfc_tac) :
    ‖cfcₙ f a‖₊ = f ‖a‖₊ :=
.unique hf.map_isGreatest (isGreatest_quasispectrum a) IsGreatest.nnnorm_cfcₙ_nnreal f a

end NonUnital

end NNReal

/-! ### Non-unital instance for unital algebras -/

namespace IsometricContinuousFunctionalCalculus

variable {𝕜 A : Type*} {p : outParam (A -> Prop)}
variable [RCLike 𝕜] [NormedRing A] [StarRing A] [NormedAlgebra 𝕜 A]
variable [IsometricContinuousFunctionalCalculus 𝕜 A p]

open scoped ContinuousFunctionalCalculus in
/--
Instance `toNonUnital` / 实例 `toNonUnital`

English:
instance toNonUnital
  signature: : NonUnitalIsometricContinuousFunctionalCalculus 𝕜 A p where
  body: by
    have : CompactSpace (σₙ 𝕜 a) := by
      have h_cpct : CompactSpace (spectrum 𝕜 a) := inferInstance
      simp only [← isCompact_iff_compactSpace, quasispectrum_eq_spectrum_union_zero] at h_cpct ⊢
.union isCompact_singleton exact h_cpct
    rw [cfcₙHom_eq_cfcₙHom_of_cfcHom]; rw [cfcₙHom_of_cf

中文:
实例 toNonUnital
  签名: : 非幺是ometricContinuousFunctionalCalculus 𝕜 A p where
  定义体: by
    have : CompactSpace (σₙ 𝕜 a) := by
      have h_cpct : CompactSpace (spectrum 𝕜 a) := inferInstance
      simp only [← isCompact_iff_compactSpace, quasispectrum_eq_spectrum_union_zero] at h_cpct ⊢
.union isCompact_singleton exact h_cpct
    rw [cfcₙHom_eq_cfcₙHom_of_cfcHom]; rw [cfcₙHom_of_cf

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.isometry_of_norm, CompactSpace, MulHom, MulHom.coe_coe, NonUnitalStarAlgHom, NonUnitalStarAlgHom.coe_toNonUnitalAlgHom, coe_coe, coe_toNonUnitalAlgHom, continuous_inclusion, h_cpct, isCompact_iff_compactSpace, isCompact_singleton, isometry_cfcHom, isometry_of_norm, quasispectrum_eq_spectrum_union_zero, spectrum
-/
instance toNonUnital : NonUnitalIsometricContinuousFunctionalCalculus 𝕜 A p where
  isometric a ha := by
    have : CompactSpace (σₙ 𝕜 a) := by
      have h_cpct : CompactSpace (spectrum 𝕜 a) := inferInstance
      simp only [← isCompact_iff_compactSpace, quasispectrum_eq_spectrum_union_zero] at h_cpct ⊢
.union isCompact_singleton exact h_cpct
    rw [cfcₙHom_eq_cfcₙHom_of_cfcHom]; rw [cfcₙHom_of_cfcHom]
.comp ?_ refine isometry_cfcHom a
    simp only [MulHom.coe_coe, NonUnitalStarAlgHom.coe_toNonUnitalAlgHom]
    refine AddMonoidHomClass.isometry_of_norm _ fun f => ?_
let ι : C(σ 𝕜 a, σₙ 𝕜 a) := ⟨_, continuous_inclusion spectrum_subset_quasispectrum 𝕜 a⟩
    change ‖(f : C(σₙ 𝕜 a, 𝕜)).comp ι‖ = ‖(f : C(σₙ 𝕜 a, 𝕜))‖
    apply le_antisymm (ContinuousMap.norm_le _ (by positivity) |>.mpr ?_)
      (ContinuousMap.norm_le _ (by positivity) |>.mpr ?_)
    · rintro ⟨x, hx⟩
      exact (f : C(σₙ 𝕜 a, 𝕜)).norm_coe_le_norm ⟨x, spectrum_subset_quasispectrum 𝕜 a hx⟩
    · rintro ⟨x, hx⟩
      obtain (rfl | hx') : x = 0 ∨ x in σ 𝕜 a := by
        simpa [quasispectrum_eq_spectrum_union_zero] using hx
      · change ‖f 0‖ <= _
        simp
.norm_coe_le_norm ⟨x, hx'⟩ · exact (f : C(σₙ 𝕜 a, 𝕜)).comp ι

end IsometricContinuousFunctionalCalculus
