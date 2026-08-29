/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

import Mathlib.Algebra.Module.Torsion.Field

/-!
# Sesquilinear maps

This file provides properties about sesquilinear maps and forms. The maps considered are of the
form `M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M`, where `I₁ : R₁ →+* R` and `I₂ : R₂ →+* R` are ring homomorphisms and
`M₁` is a module over `R₁`, `M₂` is a module over `R₂` and `M` is a module over `R`.
Sesquilinear forms are the special case that `M₁ = M₂`, `M = R₁ = R₂ = R`, and `I₁ = RingHom.id R`.
Taking additionally `I₂ = RingHom.id R`, then one obtains bilinear forms.

Sesquilinear maps are a special case of the bilinear maps defined in `BilinearMap.lean`, and many
basic lemmas about construction and elementary calculations are found there.

## Main declarations

* `IsSymm`, `IsAlt`: states that a sesquilinear form is symmetric and alternating, respectively

## References

* <https://en.wikipedia.org/wiki/Sesquilinear_form#Over_arbitrary_rings>

## Tags

Sesquilinear form, Sesquilinear map
-/

@[expose] public section

open Module

variable {R R₁ R₂ R₃ M M₁ M₂ M₃ Mₗ₁ Mₗ₁' Mₗ₂ Mₗ₂' K K₁ K₂ V V₁ V₂ n : Type*}

namespace LinearMap

/-! ### Orthogonal vectors -/


section CommRing

-- the `ₗ` subscript variables are for special cases about linear (as opposed to semilinear) maps
variable [CommSemiring R] [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁] [CommSemiring R₂]
  [AddCommMonoid M₂] [Module R₂ M₂] [AddCommMonoid M] [Module R M]
  {I₁ : R₁ ->+* R} {I₂ : R₂ ->+* R} {I₁' : R₁ ->+* R}

/-- The proposition that two elements of a sesquilinear map space are orthogonal -/
@[deprecated "Use `B x y = 0`" (since := "2026-03-30")]
/--
Definition of `IsOrtho` / `IsOrtho` 的定义

English:
definition IsOrtho
  signature: (B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M) (x : M₁) (y : M₂)
  body: B x y = 0

@[deprecated "`LinearMap.IsOrtho` has been deprecated" (since := "2026-03-30")]

中文:
定义 IsOrtho
  签名: (B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M) (x : M₁) (y : M₂)
  定义体: B x y = 0

@[deprecated "`LinearMap.IsOrtho` has been deprecated" (since := "2026-03-30")]
-/
def IsOrtho (B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M) (x : M₁) (y : M₂) : Prop :=
  B x y = 0

@[deprecated "`LinearMap.IsOrtho` has been deprecated" (since := "2026-03-30")]
/--
theorem `isOrtho_def` / 定理 `isOrtho_def`

English:
theorem isOrtho_def
  given: {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} {x y}
  statement: B.IsOrtho x y ↔ B x y = 0
  proof: Iff.rfl

@[deprecated "`LinearMap.IsOrtho` has been deprecated" (since := "2026-03-30")]

中文:
定理 isOrtho_def
  条件: {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} {x y}
  结论: B.IsOrtho x y ↔ B x y = 0
  证明: Iff.rfl

@[deprecated "`LinearMap.IsOrtho` has been deprecated" (since := "2026-03-30")]

Depends on / 依赖: Iff.rfl
-/
theorem isOrtho_def {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} {x y} : B.IsOrtho x y ↔ B x y = 0 :=
  Iff.rfl

@[deprecated "`LinearMap.IsOrtho` has been deprecated" (since := "2026-03-30")]
/--
theorem `isOrtho_zero_left` / 定理 `isOrtho_zero_left`

English:
theorem isOrtho_zero_left
  given: (B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M) (x)
  statement: IsOrtho B (0 : M₁) x
  proof: by
  dsimp only [IsOrtho]
  rw [map_zero B]; rw [zero_apply]

@[deprecated "`LinearMap.IsOrtho` has been deprecated" (since := "2026-03-30")]

中文:
定理 isOrtho_zero_left
  条件: (B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M) (x)
  结论: IsOrtho B (0 : M₁) x
  证明: by
  dsimp only [IsOrtho]
  rw [map_zero B]; rw [zero_apply]

@[deprecated "`LinearMap.IsOrtho` has been deprecated" (since := "2026-03-30")]

Depends on / 依赖: IsOrtho, map_zero, zero_apply
-/
theorem isOrtho_zero_left (B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M) (x) : IsOrtho B (0 : M₁) x := by
  dsimp only [IsOrtho]
  rw [map_zero B]; rw [zero_apply]

@[deprecated "`LinearMap.IsOrtho` has been deprecated" (since := "2026-03-30")]
/--
theorem `isOrtho_zero_right` / 定理 `isOrtho_zero_right`

English:
theorem isOrtho_zero_right
  given: (B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M) (x)
  statement: IsOrtho B x (0 : M₂)
  proof: map_zero (B x)

@[deprecated "`LinearMap.IsOrtho` has been deprecated" (since := "2026-03-30")]

中文:
定理 isOrtho_zero_right
  条件: (B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M) (x)
  结论: IsOrtho B x (0 : M₂)
  证明: map_zero (B x)

@[deprecated "`LinearMap.IsOrtho` has been deprecated" (since := "2026-03-30")]

Depends on / 依赖: map_zero
-/
theorem isOrtho_zero_right (B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M) (x) : IsOrtho B x (0 : M₂) :=
  map_zero (B x)

@[deprecated "`LinearMap.IsOrtho` has been deprecated" (since := "2026-03-30")]
/--
theorem `isOrtho_flip` / 定理 `isOrtho_flip`

English:
theorem isOrtho_flip
  given: {B : M₁ ->ₛₗ[I₁] M₁ ->ₛₗ[I₁'] M} {x y}
  statement: B.IsOrtho x y ↔ B.flip.IsOrtho y x
  proof: by
  simp_rw [isOrtho_def, flip_apply]

中文:
定理 isOrtho_flip
  条件: {B : M₁ ->ₛₗ[I₁] M₁ ->ₛₗ[I₁'] M} {x y}
  结论: B.IsOrtho x y ↔ B.flip.IsOrtho y x
  证明: by
  simp_rw [isOrtho_def, flip_apply]

Depends on / 依赖: flip_apply, isOrtho_def, simp_rw
-/
theorem isOrtho_flip {B : M₁ ->ₛₗ[I₁] M₁ ->ₛₗ[I₁'] M} {x y} : B.IsOrtho x y ↔ B.flip.IsOrtho y x := by
  simp_rw [isOrtho_def, flip_apply]

open scoped Function in -- required for scoped `on` notation
/--
Definition of `IsOrthoᵢ` / `IsOrthoᵢ` 的定义

English:
definition IsOrthoᵢ
  signature: (B : M₁ ->ₛₗ[I₁] M₁ ->ₛₗ[I₁'] M) (v : n -> M₁)
  body: Pairwise ((fun n m => B n m = 0) on v)

中文:
定义 IsOrthoᵢ
  签名: (B : M₁ ->ₛₗ[I₁] M₁ ->ₛₗ[I₁'] M) (v : n -> M₁)
  定义体: Pairwise ((fun n m => B n m = 0) on v)

Depends on / 依赖: Pairwise
-/
def IsOrthoᵢ (B : M₁ ->ₛₗ[I₁] M₁ ->ₛₗ[I₁'] M) (v : n -> M₁) : Prop :=
  Pairwise ((fun n m => B n m = 0) on v)

/--
theorem `isOrthoᵢ_def` / 定理 `isOrthoᵢ_def`

English:
theorem isOrthoᵢ_def
  given: {B : M₁ ->ₛₗ[I₁] M₁ ->ₛₗ[I₁'] M} {v : n -> M₁}
  proof: Iff.rfl

中文:
定理 isOrthoᵢ_def
  条件: {B : M₁ ->ₛₗ[I₁] M₁ ->ₛₗ[I₁'] M} {v : n -> M₁}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isOrthoᵢ_def {B : M₁ ->ₛₗ[I₁] M₁ ->ₛₗ[I₁'] M} {v : n -> M₁} :
    B.IsOrthoᵢ v ↔ forall i j : n, i != j -> B (v i) (v j) = 0 :=
  Iff.rfl

/--
theorem `isOrthoᵢ_flip` / 定理 `isOrthoᵢ_flip`

English:
theorem isOrthoᵢ_flip
  given: (B : M₁ ->ₛₗ[I₁] M₁ ->ₛₗ[I₁'] M) {v : n -> M₁}
  proof: by
  simp_rw [isOrthoᵢ_def]
  constructor <;> exact fun h i j hij => h j i hij.symm

中文:
定理 isOrthoᵢ_flip
  条件: (B : M₁ ->ₛₗ[I₁] M₁ ->ₛₗ[I₁'] M) {v : n -> M₁}
  证明: by
  simp_rw [isOrthoᵢ_def]
  constructor <;> exact fun h i j hij => h j i hij.symm

Depends on / 依赖: hij.symm, simp_rw
-/
theorem isOrthoᵢ_flip (B : M₁ ->ₛₗ[I₁] M₁ ->ₛₗ[I₁'] M) {v : n -> M₁} :
    B.IsOrthoᵢ v ↔ B.flip.IsOrthoᵢ v := by
  simp_rw [isOrthoᵢ_def]
  constructor <;> exact fun h i j hij => h j i hij.symm

end CommRing

section Field

variable [Field K] [AddCommGroup V] [Module K V] [Field K₁] [AddCommGroup V₁] [Module K₁ V₁]
  [Field K₂] [AddCommGroup V₂] [Module K₂ V₂]
  {I₁ : K₁ ->+* K} {I₂ : K₂ ->+* K} {I₁' : K₁ ->+* K} {J₁ : K ->+* K} {J₂ : K ->+* K}

@[deprecated "`LinearMap.IsOrtho` has been deprecated" (since := "2026-03-30")]
/--
theorem `ortho_smul_left` / 定理 `ortho_smul_left`

English:
theorem ortho_smul_left
  given: {B : V₁ ->ₛₗ[I₁] V₂ ->ₛₗ[I₂] V} {x y} {a : K₁} (ha : a != 0)
  proof: by
  dsimp only [IsOrtho]
  constructor <;> intro H
  · rw [map_smulₛₗ₂, H, smul_zero]
  · rw [map_smulₛₗ₂, smul_eq_zero] at H
    rcases H with H | H
    · rw [map_eq_zero I₁] at H
      trivial
    · exact H

@[deprecated "`LinearMap.IsOrtho` has been deprecated" (since := "2026-03-30")]

中文:
定理 ortho_smul_left
  条件: {B : V₁ ->ₛₗ[I₁] V₂ ->ₛₗ[I₂] V} {x y} {a : K₁} (ha : a != 0)
  证明: by
  dsimp only [IsOrtho]
  constructor <;> intro H
  · rw [map_smulₛₗ₂, H, smul_zero]
  · rw [map_smulₛₗ₂, smul_eq_zero] at H
    rcases H with H | H
    · rw [map_eq_zero I₁] at H
      trivial
    · exact H

@[deprecated "`LinearMap.IsOrtho` has been deprecated" (since := "2026-03-30")]

Depends on / 依赖: IsOrtho, map_eq_zero, smul_eq_zero, smul_zero
-/
theorem ortho_smul_left {B : V₁ ->ₛₗ[I₁] V₂ ->ₛₗ[I₂] V} {x y} {a : K₁} (ha : a != 0) :
    IsOrtho B x y ↔ IsOrtho B (a • x) y := by
  dsimp only [IsOrtho]
  constructor <;> intro H
  · rw [map_smulₛₗ₂, H, smul_zero]
  · rw [map_smulₛₗ₂, smul_eq_zero] at H
    rcases H with H | H
    · rw [map_eq_zero I₁] at H
      trivial
    · exact H

@[deprecated "`LinearMap.IsOrtho` has been deprecated" (since := "2026-03-30")]
/--
theorem `ortho_smul_right` / 定理 `ortho_smul_right`

English:
theorem ortho_smul_right
  given: {B : V₁ ->ₛₗ[I₁] V₂ ->ₛₗ[I₂] V} {x y} {a : K₂} {ha : a != 0}
  proof: by
  simp_all [IsOrtho]

中文:
定理 ortho_smul_right
  条件: {B : V₁ ->ₛₗ[I₁] V₂ ->ₛₗ[I₂] V} {x y} {a : K₂} {ha : a != 0}
  证明: by
  simp_all [IsOrtho]

Depends on / 依赖: IsOrtho
-/
theorem ortho_smul_right {B : V₁ ->ₛₗ[I₁] V₂ ->ₛₗ[I₂] V} {x y} {a : K₂} {ha : a != 0} :
    IsOrtho B x y ↔ IsOrtho B x (a • y) := by
  simp_all [IsOrtho]

/--
theorem `linearIndependent_of_isOrthoᵢ` / 定理 `linearIndependent_of_isOrthoᵢ`

English:
theorem linearIndependent_of_isOrthoᵢ
  statement: {B : V₁ ->ₛₗ[I₁] V₁ ->ₛₗ[I₁'] V} {v : n -> V₁}
  proof: by
  rw [linearIndependent_iff']
  intro s w hs i hi
  have : B (s.sum fun i : n => w i • v i) (v i) = 0 := by rw [hs, map_zero, zero_apply]
  have hsum : (s.sum fun j : n => I₁ (w j) • B (v j) (v i)) = I₁ (w i) • B (v i) (v i) := by
    apply Finset.sum_eq_single_of_mem i hi
    intro j _hj hij
    rw [isOrthoᵢ_def.1 hv₁ _ _ hij]; rw [smul_zero]
  simp_rw [B.map_sum₂, map_smulₛₗ₂, hsum] at this
  apply (map_eq_zero I₁).mp
  exact (smul_eq_zero.mp this).elim _root_.id (hv₂ i · |>.elim)

中文:
定理 linearIndependent_of_isOrthoᵢ
  结论: {B : V₁ ->ₛₗ[I₁] V₁ ->ₛₗ[I₁'] V} {v : n -> V₁}
  证明: by
  rw [linearIndependent_iff']
  intro s w hs i hi
  have : B (s.sum fun i : n => w i • v i) (v i) = 0 := by rw [hs, map_zero, zero_apply]
  have hsum : (s.sum fun j : n => I₁ (w j) • B (v j) (v i)) = I₁ (w i) • B (v i) (v i) := by
    apply Finset.sum_eq_single_of_mem i hi
    intro j _hj hij
    rw [isOrthoᵢ_def.1 hv₁ _ _ hij]; rw [smul_zero]
  simp_rw [B.map_sum₂, map_smulₛₗ₂, hsum] at this
  apply (map_eq_zero I₁).mp
  exact (smul_eq_zero.mp this).elim _root_.id (hv₂ i · |>.elim)

Depends on / 依赖: B.map_sum, Finset, Finset.sum_eq_single_of_mem, _root_, _root_.id, linearIndependent_iff, map_eq_zero, map_zero, s.sum, simp_rw, smul_eq_zero, smul_eq_zero.mp, smul_zero, sum_eq_single_of_mem, zero_apply
-/
theorem linearIndependent_of_isOrthoᵢ {B : V₁ ->ₛₗ[I₁] V₁ ->ₛₗ[I₁'] V} {v : n -> V₁}
    (hv₁ : B.IsOrthoᵢ v) (hv₂ : forall i, B (v i) (v i) != 0) : LinearIndependent K₁ v := by
  rw [linearIndependent_iff']
  intro s w hs i hi
  have : B (s.sum fun i : n => w i • v i) (v i) = 0 := by rw [hs, map_zero, zero_apply]
  have hsum : (s.sum fun j : n => I₁ (w j) • B (v j) (v i)) = I₁ (w i) • B (v i) (v i) := by
    apply Finset.sum_eq_single_of_mem i hi
    intro j _hj hij
    rw [isOrthoᵢ_def.1 hv₁ _ _ hij]; rw [smul_zero]
  simp_rw [B.map_sum₂, map_smulₛₗ₂, hsum] at this
  apply (map_eq_zero I₁).mp
  exact (smul_eq_zero.mp this).elim _root_.id (hv₂ i · |>.elim)

end Field

/-! ### Reflexive bilinear maps -/

section Reflexive

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [CommSemiring R₁] [AddCommMonoid M₁]
  [Module R₁ M₁] {I₁ : R₁ ->+* R} {I₂ : R₁ ->+* R} {B : M₁ ->ₛₗ[I₁] M₁ ->ₛₗ[I₂] M}

/--
Definition of `IsRefl` / `IsRefl` 的定义

English:
definition IsRefl
  signature: (B : M₁ ->ₛₗ[I₁] M₁ ->ₛₗ[I₂] M)
  body: forall x y, B x y = 0 -> B y x = 0

中文:
定义 IsRefl
  签名: (B : M₁ ->ₛₗ[I₁] M₁ ->ₛₗ[I₂] M)
  定义体: forall x y, B x y = 0 -> B y x = 0
-/
def IsRefl (B : M₁ ->ₛₗ[I₁] M₁ ->ₛₗ[I₂] M) : Prop :=
  forall x y, B x y = 0 -> B y x = 0

namespace IsRefl

section
variable (H : B.IsRefl)
include H

/--
theorem `eq_zero` / 定理 `eq_zero`

English:
theorem eq_zero
  statement: forall {x y}, B x y = 0 -> B y x = 0
  proof: fun {x y} => H x y

中文:
定理 eq_zero
  结论: 对任意 {x y}, B x y = 0 -> B y x = 0
  证明: fun {x y} => H x y
-/
theorem eq_zero : forall {x y}, B x y = 0 -> B y x = 0 := fun {x y} => H x y

/--
theorem `eq_iff` / 定理 `eq_iff`

English:
theorem eq_iff
  given: {x y}
  statement: B x y = 0 ↔ B y x = 0
  proof: ⟨H x y, H y x⟩

@[deprecated (since := "2026-03-30")]
alias ortho_comm := eq_iff

中文:
定理 eq_iff
  条件: {x y}
  结论: B x y = 0 ↔ B y x = 0
  证明: ⟨H x y, H y x⟩

@[deprecated (since := "2026-03-30")]
alias ortho_comm := eq_iff
-/
theorem eq_iff {x y} : B x y = 0 ↔ B y x = 0 := ⟨H x y, H y x⟩

@[deprecated (since := "2026-03-30")]
alias ortho_comm := eq_iff

/--
theorem `domRestrict` / 定理 `domRestrict`

English:
theorem domRestrict
  given: (p : Submodule R₁ M₁)
  statement: (B.domRestrict₁₂ p p).IsRefl
  proof: fun _ _ => by
  simp_rw [domRestrict₁₂_apply]
  exact H _ _

中文:
定理 domRestrict
  条件: (p : 子模 R₁ M₁)
  结论: (B.domRestrict₁₂ p p).IsRefl
  证明: fun _ _ => by
  simp_rw [domRestrict₁₂_apply]
  exact H _ _

Depends on / 依赖: simp_rw
-/
theorem domRestrict (p : Submodule R₁ M₁) : (B.domRestrict₁₂ p p).IsRefl :=
  fun _ _ => by
  simp_rw [domRestrict₁₂_apply]
  exact H _ _
end

@[simp]
/--
theorem `flip_isRefl_iff` / 定理 `flip_isRefl_iff`

English:
theorem flip_isRefl_iff
  statement: B.flip.IsRefl ↔ B.IsRefl
  proof: forall_comm

中文:
定理 flip_isRefl_iff
  结论: B.flip.IsRefl ↔ B.IsRefl
  证明: forall_comm

Depends on / 依赖: forall_comm
-/
theorem flip_isRefl_iff : B.flip.IsRefl ↔ B.IsRefl :=
  forall_comm

/--
lemma `ker_flip` / 引理 `ker_flip`

English:
lemma ker_flip
  given: (H : B.IsRefl)
  statement: B.flip.ker = B.ker
  proof: by
  ext x
  simp [LinearMap.ext_iff, H.eq_iff]

中文:
引理 ker_flip
  条件: (H : B.IsRefl)
  结论: B.flip.ker = B.ker
  证明: by
  ext x
  simp [LinearMap.ext_iff, H.eq_iff]

Depends on / 依赖: H.eq_iff, LinearMap, LinearMap.ext_iff, eq_iff, ext_iff
-/
lemma ker_flip (H : B.IsRefl) : B.flip.ker = B.ker := by
  ext x
  simp [LinearMap.ext_iff, H.eq_iff]

/--
theorem `ker_flip_eq_bot` / 定理 `ker_flip_eq_bot`

English:
theorem ker_flip_eq_bot
  given: (H : B.IsRefl) (h : LinearMap.ker B = ⊥)
  statement: LinearMap.ker B.flip = ⊥
  proof: by
  rwa [H.ker_flip]

中文:
定理 ker_flip_eq_bot
  条件: (H : B.IsRefl) (h : 线性映射.ker B = ⊥)
  结论: 线性映射.ker B.flip = ⊥
  证明: by
  rwa [H.ker_flip]

Depends on / 依赖: H.ker_flip, ker_flip
-/
theorem ker_flip_eq_bot (H : B.IsRefl) (h : LinearMap.ker B = ⊥) : LinearMap.ker B.flip = ⊥ := by
  rwa [H.ker_flip]

/--
theorem `ker_eq_bot_iff_ker_flip_eq_bot` / 定理 `ker_eq_bot_iff_ker_flip_eq_bot`

English:
theorem ker_eq_bot_iff_ker_flip_eq_bot
  given: (H : B.IsRefl)
  proof: by
  rwa [ker_flip]

中文:
定理 ker_eq_bot_iff_ker_flip_eq_bot
  条件: (H : B.IsRefl)
  证明: by
  rwa [ker_flip]

Depends on / 依赖: ker_flip
-/
theorem ker_eq_bot_iff_ker_flip_eq_bot (H : B.IsRefl) :
    LinearMap.ker B = ⊥ ↔ LinearMap.ker B.flip = ⊥ := by
  rwa [ker_flip]

end IsRefl

end Reflexive

/-! ### Symmetric bilinear forms -/

section Symmetric

variable [CommSemiring R] [AddCommMonoid M] [Module R M] {I : R ->+* R} {B : M ->ₛₗ[I] M ->ₗ[R] R}

/--
Definition of `IsSymm` / `IsSymm` 的定义

English:
structure IsSymm
  parameters: (B : M ->ₛₗ[I] M ->ₗ[R] R)
  axioms and operations (1):
    - eq : forall x y, I (B x y) = B y x

中文:
结构 是Symm
  参数: (B : M ->ₛₗ[I] M ->ₗ[R] R)
  公理与运算 (1 个):
    - eq : 对任意 x y, I (B x y) = B y x
-/
structure IsSymm (B : M ->ₛₗ[I] M ->ₗ[R] R) : Prop where
  protected eq : forall x y, I (B x y) = B y x

/--
theorem `isSymm_def` / 定理 `isSymm_def`

English:
theorem isSymm_def
  given: {B : M ->ₛₗ[I] M ->ₗ[R] R}
  statement: B.IsSymm ↔ forall x y, I (B x y) = B y x
  proof: ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

中文:
定理 isSymm_def
  条件: {B : M ->ₛₗ[I] M ->ₗ[R] R}
  结论: B.是Symm ↔ 对任意 x y, I (B x y) = B y x
  证明: ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩
-/
theorem isSymm_def {B : M ->ₛₗ[I] M ->ₗ[R] R} : B.IsSymm ↔ forall x y, I (B x y) = B y x :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

namespace IsSymm

/--
theorem `isRefl` / 定理 `isRefl`

English:
theorem isRefl
  given: (H : B.IsSymm)
  statement: B.IsRefl
  proof: fun x y H1 => by
  rw [← H.eq]
  simp [H1]

中文:
定理 isRefl
  条件: (H : B.是Symm)
  结论: B.IsRefl
  证明: fun x y H1 => by
  rw [← H.eq]
  simp [H1]

Depends on / 依赖: H.eq
-/
theorem isRefl (H : B.IsSymm) : B.IsRefl := fun x y H1 => by
  rw [← H.eq]
  simp [H1]

/--
theorem `eq_iff` / 定理 `eq_iff`

English:
theorem eq_iff
  given: (H : B.IsSymm) {x y}
  statement: B x y = 0 ↔ B y x = 0
  proof: H.isRefl.eq_iff

@[deprecated (since := "2026-03-30")]
alias ortho_comm := eq_iff

中文:
定理 eq_iff
  条件: (H : B.是Symm) {x y}
  结论: B x y = 0 ↔ B y x = 0
  证明: H.isRefl.eq_iff

@[deprecated (since := "2026-03-30")]
alias ortho_comm := eq_iff

Depends on / 依赖: H.isRefl.eq_iff, eq_iff, isRefl
-/
theorem eq_iff (H : B.IsSymm) {x y} : B x y = 0 ↔ B y x = 0 := H.isRefl.eq_iff

@[deprecated (since := "2026-03-30")]
alias ortho_comm := eq_iff

/--
theorem `domRestrict` / 定理 `domRestrict`

English:
theorem domRestrict
  given: (H : B.IsSymm) (p : Submodule R M)
  statement: (B.domRestrict₁₂ p p).IsSymm where
  proof: by
    simp_rw [domRestrict₁₂_apply]
    exact H.eq _ _

中文:
定理 domRestrict
  条件: (H : B.是Symm) (p : 子模 R M)
  结论: (B.domRestrict₁₂ p p).是Symm where
  证明: by
    simp_rw [domRestrict₁₂_apply]
    exact H.eq _ _

Depends on / 依赖: H.eq, simp_rw
-/
theorem domRestrict (H : B.IsSymm) (p : Submodule R M) : (B.domRestrict₁₂ p p).IsSymm where
  eq _ _ := by
    simp_rw [domRestrict₁₂_apply]
    exact H.eq _ _

end IsSymm

@[simp]
/--
theorem `isSymm_zero` / 定理 `isSymm_zero`

English:
theorem isSymm_zero
  statement: (0 : M ->ₛₗ[I] M ->ₗ[R] R).IsSymm
  proof: ⟨fun _ _ => map_zero _⟩

中文:
定理 isSymm_zero
  结论: (0 : M ->ₛₗ[I] M ->ₗ[R] R).是Symm
  证明: ⟨fun _ _ => map_zero _⟩

Depends on / 依赖: map_zero
-/
theorem isSymm_zero : (0 : M ->ₛₗ[I] M ->ₗ[R] R).IsSymm := ⟨fun _ _ => map_zero _⟩

/--
lemma `IsSymm.add` / 引理 `IsSymm.add`

English:
lemma IsSymm.add
  given: {C : M ->ₛₗ[I] M ->ₗ[R] R} (hB : B.IsSymm) (hC : C.IsSymm)
  proof: by simp [hB.eq, hC.eq]

中文:
引理 是Symm.add
  条件: {C : M ->ₛₗ[I] M ->ₗ[R] R} (hB : B.是Symm) (hC : C.是Symm)
  证明: by simp [hB.eq, hC.eq]
-/
protected lemma IsSymm.add {C : M ->ₛₗ[I] M ->ₗ[R] R} (hB : B.IsSymm) (hC : C.IsSymm) :
    (B + C).IsSymm where
  eq x y := by simp [hB.eq, hC.eq]

/--
theorem `BilinMap.isSymm_iff_eq_flip` / 定理 `BilinMap.isSymm_iff_eq_flip`

English:
theorem BilinMap.isSymm_iff_eq_flip
  statement: {N : Type*} [AddCommMonoid N] [Module R N]
  proof: by
  simp [LinearMap.ext_iff₂]

中文:
定理 BilinMap.isSymm_iff_eq_flip
  结论: {N : 类型} [加法交换幺半群 N] [模 R N]
  证明: by
  simp [LinearMap.ext_iff₂]

Depends on / 依赖: LinearMap, LinearMap.ext_iff
-/
theorem BilinMap.isSymm_iff_eq_flip {N : Type*} [AddCommMonoid N] [Module R N]
    {B : LinearMap.BilinMap R M N} : (forall x y, B x y = B y x) ↔ B = B.flip := by
  simp [LinearMap.ext_iff₂]

/--
theorem `isSymm_iff_eq_flip` / 定理 `isSymm_iff_eq_flip`

English:
theorem isSymm_iff_eq_flip
  given: {B : LinearMap.BilinForm R M}
  statement: B.IsSymm ↔ B = B.flip
  proof: isSymm_def.trans BilinMap.isSymm_iff_eq_flip

中文:
定理 isSymm_iff_eq_flip
  条件: {B : 线性映射.BilinForm R M}
  结论: B.是Symm ↔ B = B.flip
  证明: isSymm_def.trans BilinMap.isSymm_iff_eq_flip

Depends on / 依赖: BilinMap, BilinMap.isSymm_iff_eq_flip, isSymm_def, isSymm_def.trans, isSymm_iff_eq_flip
-/
theorem isSymm_iff_eq_flip {B : LinearMap.BilinForm R M} : B.IsSymm ↔ B = B.flip :=
  isSymm_def.trans BilinMap.isSymm_iff_eq_flip

end Symmetric

/-! ### Positive semidefinite sesquilinear forms -/

section PositiveSemidefinite

variable [CommSemiring R] [AddCommMonoid M] [Module R M] {I₁ I₂ : R ->+* R}

/--
Definition of `IsNonneg` / `IsNonneg` 的定义

English:
structure IsNonneg
  parameters: [LE R] (B : M ->ₛₗ[I₁] M ->ₛₗ[I₂] R)
  axioms and operations (1):
    - nonneg : forall x, 0 <= B x x

中文:
结构 是Nonneg
  参数: [LE R] (B : M ->ₛₗ[I₁] M ->ₛₗ[I₂] R)
  公理与运算 (1 个):
    - nonneg : 对任意 x, 0 <= B x x
-/
structure IsNonneg [LE R] (B : M ->ₛₗ[I₁] M ->ₛₗ[I₂] R) where
  nonneg : forall x, 0 <= B x x

/--
lemma `isNonneg_def` / 引理 `isNonneg_def`

English:
lemma isNonneg_def
  given: [LE R] {B : M ->ₛₗ[I₁] M ->ₛₗ[I₂] R}
  statement: B.IsNonneg ↔ forall x, 0 <= B x x
  proof: ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

@[simp]

中文:
引理 isNonneg_def
  条件: [LE R] {B : M ->ₛₗ[I₁] M ->ₛₗ[I₂] R}
  结论: B.是Nonneg ↔ 对任意 x, 0 <= B x x
  证明: ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

@[simp]
-/
lemma isNonneg_def [LE R] {B : M ->ₛₗ[I₁] M ->ₛₗ[I₂] R} : B.IsNonneg ↔ forall x, 0 <= B x x :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

@[simp]
/--
lemma `isNonneg_zero` / 引理 `isNonneg_zero`

English:
lemma isNonneg_zero
  given: [Preorder R]
  statement: IsNonneg (0 : M ->ₛₗ[I₁] M ->ₛₗ[I₂] R)
  proof: ⟨fun _ => le_rfl⟩

中文:
引理 isNonneg_zero
  条件: [预序 R]
  结论: 是Nonneg (0 : M ->ₛₗ[I₁] M ->ₛₗ[I₂] R)
  证明: ⟨fun _ => le_rfl⟩

Depends on / 依赖: le_rfl
-/
lemma isNonneg_zero [Preorder R] : IsNonneg (0 : M ->ₛₗ[I₁] M ->ₛₗ[I₂] R) := ⟨fun _ => le_rfl⟩

/--
lemma `IsNonneg.add` / 引理 `IsNonneg.add`

English:
lemma IsNonneg.add
  statement: [Preorder R] [AddLeftMono R] {B C : M ->ₛₗ[I₁] M ->ₛₗ[I₂] R}
  proof: add_nonneg (hB.nonneg x) (hC.nonneg x)

中文:
引理 是Nonneg.add
  结论: [预序 R] [AddLeftMono R] {B C : M ->ₛₗ[I₁] M ->ₛₗ[I₂] R}
  证明: add_nonneg (hB.nonneg x) (hC.nonneg x)
-/
protected lemma IsNonneg.add [Preorder R] [AddLeftMono R] {B C : M ->ₛₗ[I₁] M ->ₛₗ[I₂] R}
    (hB : B.IsNonneg) (hC : C.IsNonneg) : (B + C).IsNonneg where
  nonneg x := add_nonneg (hB.nonneg x) (hC.nonneg x)

/--
lemma `IsNonneg.smul` / 引理 `IsNonneg.smul`

English:
lemma IsNonneg.smul
  statement: [Preorder R] [PosMulMono R] {B : M ->ₛₗ[I₁] M ->ₛₗ[I₂] R} {c : R}
  proof: mul_nonneg hc (hB.nonneg x)

中文:
引理 是Nonneg.smul
  结论: [预序 R] [正乘递增 R] {B : M ->ₛₗ[I₁] M ->ₛₗ[I₂] R} {c : R}
  证明: mul_nonneg hc (hB.nonneg x)
-/
protected lemma IsNonneg.smul [Preorder R] [PosMulMono R] {B : M ->ₛₗ[I₁] M ->ₛₗ[I₂] R} {c : R}
    (hB : B.IsNonneg) (hc : 0 <= c) : (c • B).IsNonneg where
  nonneg x := mul_nonneg hc (hB.nonneg x)

/--
Definition of `IsPosSemidef` / `IsPosSemidef` 的定义

English:
structure IsPosSemidef
  parameters: [LE R] (B : M ->ₛₗ[I₁] M ->ₗ[R] R)
  (no additional axioms)

中文:
结构 是PosSemidef
  参数: [LE R] (B : M ->ₛₗ[I₁] M ->ₗ[R] R)
  (无附加公理)
-/
structure IsPosSemidef [LE R] (B : M ->ₛₗ[I₁] M ->ₗ[R] R) extends
  isSymm : B.IsSymm,
  isNonneg : B.IsNonneg

/--
lemma `isPosSemidef_def` / 引理 `isPosSemidef_def`

English:
lemma isPosSemidef_def
  given: [LE R] {B : M ->ₛₗ[I₁] M ->ₗ[R] R}
  statement: B.IsPosSemidef ↔ B.IsSymm ∧ B.IsNonneg
  proof: ⟨fun h => ⟨h.isSymm, h.isNonneg⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

@[simp]

中文:
引理 isPosSemidef_def
  条件: [LE R] {B : M ->ₛₗ[I₁] M ->ₗ[R] R}
  结论: B.是PosSemidef ↔ B.是Symm ∧ B.是Nonneg
  证明: ⟨fun h => ⟨h.isSymm, h.isNonneg⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

@[simp]

Depends on / 依赖: h.isNonneg, h.isSymm, isNonneg, isSymm
-/
lemma isPosSemidef_def [LE R] {B : M ->ₛₗ[I₁] M ->ₗ[R] R} : B.IsPosSemidef ↔ B.IsSymm ∧ B.IsNonneg :=
  ⟨fun h => ⟨h.isSymm, h.isNonneg⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

@[simp]
/--
lemma `isPosSemidef_zero` / 引理 `isPosSemidef_zero`

English:
lemma isPosSemidef_zero
  given: [Preorder R]
  statement: IsPosSemidef (0 : M ->ₛₗ[I₁] M ->ₗ[R] R) where
  proof: isSymm_zero
  isNonneg := isNonneg_zero

中文:
引理 isPosSemidef_zero
  条件: [预序 R]
  结论: 是PosSemidef (0 : M ->ₛₗ[I₁] M ->ₗ[R] R) where
  证明: isSymm_zero
  isNonneg := isNonneg_zero

Depends on / 依赖: isSymm_zero
-/
lemma isPosSemidef_zero [Preorder R] : IsPosSemidef (0 : M ->ₛₗ[I₁] M ->ₗ[R] R) where
  isSymm := isSymm_zero
  isNonneg := isNonneg_zero

/--
lemma `IsPosSemidef.add` / 引理 `IsPosSemidef.add`

English:
lemma IsPosSemidef.add
  statement: [Preorder R] [AddLeftMono R] {B C : M ->ₛₗ[I₁] M ->ₗ[R] R}
  proof: isPosSemidef_def.2 ⟨hB.isSymm.add hC.isSymm, hB.isNonneg.add hC.isNonneg⟩

中文:
引理 是PosSemidef.add
  结论: [预序 R] [AddLeftMono R] {B C : M ->ₛₗ[I₁] M ->ₗ[R] R}
  证明: isPosSemidef_def.2 ⟨hB.isSymm.add hC.isSymm, hB.isNonneg.add hC.isNonneg⟩
-/
protected lemma IsPosSemidef.add [Preorder R] [AddLeftMono R] {B C : M ->ₛₗ[I₁] M ->ₗ[R] R}
    (hB : B.IsPosSemidef) (hC : C.IsPosSemidef) : (B + C).IsPosSemidef :=
  isPosSemidef_def.2 ⟨hB.isSymm.add hC.isSymm, hB.isNonneg.add hC.isNonneg⟩

end PositiveSemidefinite

/-! ### Alternating bilinear maps -/

section Alternating

section CommSemiring

section AddCommMonoid

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [CommSemiring R₁] [AddCommMonoid M₁]
  [Module R₁ M₁] {I₁ : R₁ ->+* R} {I₂ : R₁ ->+* R} {I : R₁ ->+* R} {B : M₁ ->ₛₗ[I₁] M₁ ->ₛₗ[I₂] M}

/--
Definition of `IsAlt` / `IsAlt` 的定义

English:
definition IsAlt
  signature: (B : M₁ ->ₛₗ[I₁] M₁ ->ₛₗ[I₂] M)
  body: forall x, B x x = 0

中文:
定义 IsAlt
  签名: (B : M₁ ->ₛₗ[I₁] M₁ ->ₛₗ[I₂] M)
  定义体: forall x, B x x = 0
-/
def IsAlt (B : M₁ ->ₛₗ[I₁] M₁ ->ₛₗ[I₂] M) : Prop :=
  forall x, B x x = 0

variable (H : B.IsAlt)
include H

/--
theorem `IsAlt.self_eq_zero` / 定理 `IsAlt.self_eq_zero`

English:
theorem IsAlt.self_eq_zero
  given: (x : M₁)
  statement: B x x = 0
  proof: H x

中文:
定理 IsAlt.self_eq_zero
  条件: (x : M₁)
  结论: B x x = 0
  证明: H x
-/
theorem IsAlt.self_eq_zero (x : M₁) : B x x = 0 :=
  H x

/--
theorem `IsAlt.eq_of_add_add_eq_zero` / 定理 `IsAlt.eq_of_add_add_eq_zero`

English:
theorem IsAlt.eq_of_add_add_eq_zero
  given: [IsCancelAdd M] {a b c : M₁} (hAdd : a + b + c = 0)
  proof: by
  have : B a a + B a b + B a c = B a c + B b c + B c c := by
    simp_rw [← map_add, ← map_add₂, hAdd, map_zero, LinearMap.zero_apply]
  rw [H]; rw [H]; rw [zero_add]; rw [add_zero]; rw [add_comm] at this
  exact add_left_cancel this

中文:
定理 IsAlt.eq_of_add_add_eq_zero
  条件: [是消去加法 M] {a b c : M₁} (hAdd : a + b + c = 0)
  证明: by
  have : B a a + B a b + B a c = B a c + B b c + B c c := by
    simp_rw [← map_add, ← map_add₂, hAdd, map_zero, LinearMap.zero_apply]
  rw [H]; rw [H]; rw [zero_add]; rw [add_zero]; rw [add_comm] at this
  exact add_left_cancel this

Depends on / 依赖: LinearMap, LinearMap.zero_apply, add_comm, add_left_cancel, add_zero, map_add, map_zero, simp_rw, zero_add, zero_apply
-/
theorem IsAlt.eq_of_add_add_eq_zero [IsCancelAdd M] {a b c : M₁} (hAdd : a + b + c = 0) :
    B a b = B b c := by
  have : B a a + B a b + B a c = B a c + B b c + B c c := by
    simp_rw [← map_add, ← map_add₂, hAdd, map_zero, LinearMap.zero_apply]
  rw [H]; rw [H]; rw [zero_add]; rw [add_zero]; rw [add_comm] at this
  exact add_left_cancel this

end AddCommMonoid

section AddCommGroup

namespace IsAlt

variable [CommSemiring R] [AddCommGroup M] [Module R M] [CommSemiring R₁] [AddCommMonoid M₁]
  [Module R₁ M₁] {I₁ : R₁ ->+* R} {I₂ : R₁ ->+* R} {I : R₁ ->+* R} {B : M₁ ->ₛₗ[I₁] M₁ ->ₛₗ[I₂] M}

/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  given: (H : B.IsAlt) (x y : M₁)
  statement: -B x y = B y x
  proof: by
  have H1 : B (y + x) (y + x) = 0 := self_eq_zero H (y + x)
  simpa [map_add, self_eq_zero H, add_eq_zero_iff_neg_eq] using H1

中文:
定理 neg
  条件: (H : B.IsAlt) (x y : M₁)
  结论: -B x y = B y x
  证明: by
  have H1 : B (y + x) (y + x) = 0 := self_eq_zero H (y + x)
  simpa [map_add, self_eq_zero H, add_eq_zero_iff_neg_eq] using H1

Depends on / 依赖: add_eq_zero_iff_neg_eq, map_add, self_eq_zero
-/
theorem neg (H : B.IsAlt) (x y : M₁) : -B x y = B y x := by
  have H1 : B (y + x) (y + x) = 0 := self_eq_zero H (y + x)
  simpa [map_add, self_eq_zero H, add_eq_zero_iff_neg_eq] using H1

/--
theorem `isRefl` / 定理 `isRefl`

English:
theorem isRefl
  given: (H : B.IsAlt)
  statement: B.IsRefl
  proof: by
  intro x y h
  rw [← neg H]; rw [h]; rw [neg_zero]

中文:
定理 isRefl
  条件: (H : B.IsAlt)
  结论: B.IsRefl
  证明: by
  intro x y h
  rw [← neg H]; rw [h]; rw [neg_zero]

Depends on / 依赖: neg_zero
-/
theorem isRefl (H : B.IsAlt) : B.IsRefl := by
  intro x y h
  rw [← neg H]; rw [h]; rw [neg_zero]

/--
theorem `eq_iff` / 定理 `eq_iff`

English:
theorem eq_iff
  given: (H : B.IsAlt) {x y}
  statement: B x y = 0 ↔ B y x = 0
  proof: H.isRefl.eq_iff

@[deprecated (since := "2026-03-30")]
alias ortho_comm := eq_iff

中文:
定理 eq_iff
  条件: (H : B.IsAlt) {x y}
  结论: B x y = 0 ↔ B y x = 0
  证明: H.isRefl.eq_iff

@[deprecated (since := "2026-03-30")]
alias ortho_comm := eq_iff

Depends on / 依赖: H.isRefl.eq_iff, eq_iff, isRefl
-/
theorem eq_iff (H : B.IsAlt) {x y} : B x y = 0 ↔ B y x = 0 := H.isRefl.eq_iff

@[deprecated (since := "2026-03-30")]
alias ortho_comm := eq_iff

end IsAlt

end AddCommGroup

end CommSemiring

section Semiring

variable [CommRing R] [AddCommGroup M] [Module R M] [CommSemiring R₁] [AddCommMonoid M₁]
  [Module R₁ M₁] {I : R₁ ->+* R}

/--
theorem `isAlt_iff_eq_neg_flip` / 定理 `isAlt_iff_eq_neg_flip`

English:
theorem isAlt_iff_eq_neg_flip
  given: [NoZeroDivisors R] [CharZero R] {B : M₁ ->ₛₗ[I] M₁ ->ₛₗ[I] R}
  proof: by
  constructor <;> intro h
  · ext
    simp_rw [neg_apply, flip_apply]
    exact (h.neg _ _).symm
  intro x
  let h' := congr_fun₂ h x x
  simp only [neg_apply, flip_apply, ← add_eq_zero_iff_eq_neg] at h'
  exact add_self_eq_zero.mp h'

中文:
定理 isAlt_iff_eq_neg_flip
  条件: [无零因子 R] [特征零 R] {B : M₁ ->ₛₗ[I] M₁ ->ₛₗ[I] R}
  证明: by
  constructor <;> intro h
  · ext
    simp_rw [neg_apply, flip_apply]
    exact (h.neg _ _).symm
  intro x
  let h' := congr_fun₂ h x x
  simp only [neg_apply, flip_apply, ← add_eq_zero_iff_eq_neg] at h'
  exact add_self_eq_zero.mp h'

Depends on / 依赖: add_eq_zero_iff_eq_neg, add_self_eq_zero, add_self_eq_zero.mp, flip_apply, h.neg, neg_apply, simp_rw
-/
theorem isAlt_iff_eq_neg_flip [NoZeroDivisors R] [CharZero R] {B : M₁ ->ₛₗ[I] M₁ ->ₛₗ[I] R} :
    B.IsAlt ↔ B = -B.flip := by
  constructor <;> intro h
  · ext
    simp_rw [neg_apply, flip_apply]
    exact (h.neg _ _).symm
  intro x
  let h' := congr_fun₂ h x x
  simp only [neg_apply, flip_apply, ← add_eq_zero_iff_eq_neg] at h'
  exact add_self_eq_zero.mp h'

end Semiring

end Alternating

end LinearMap

namespace LinearMap

/-! ### Adjoint pairs -/

section AdjointPair

section AddCommMonoid

variable [CommSemiring R]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid M₁] [Module R M₁]
variable [AddCommMonoid M₂] [Module R M₂]
variable [AddCommMonoid M₃] [Module R M₃]
variable {I : R ->+* R}
variable {B F : M ->ₗ[R] M ->ₛₗ[I] M₃} {B' : M₁ ->ₗ[R] M₁ ->ₛₗ[I] M₃} {B'' : M₂ ->ₗ[R] M₂ ->ₛₗ[I] M₃}
variable {f f' : M ->ₗ[R] M₁} {g g' : M₁ ->ₗ[R] M}
variable (B B' f g)

/--
Definition of `IsAdjointPair` / `IsAdjointPair` 的定义

English:
definition IsAdjointPair
  signature: (f : M -> M₁) (g : M₁ -> M)
  body: forall x y, B' (f x) y = B x (g y)

中文:
定义 IsAdjointPair
  签名: (f : M -> M₁) (g : M₁ -> M)
  定义体: forall x y, B' (f x) y = B x (g y)
-/
def IsAdjointPair (f : M -> M₁) (g : M₁ -> M) :=
  forall x y, B' (f x) y = B x (g y)

variable {B B' f g}

/--
theorem `isAdjointPair_iff_comp_eq_compl₂` / 定理 `isAdjointPair_iff_comp_eq_compl₂`

English:
theorem isAdjointPair_iff_comp_eq_compl₂
  statement: IsAdjointPair B B' f g ↔ B'.comp f = B.compl₂ g
  proof: by
  constructor <;> intro h
  · ext x y
    rw [comp_apply]; rw [compl₂_apply]
    exact h x y
  · intro _ _
    rw [← compl₂_apply]; rw [← comp_apply]; rw [h]

中文:
定理 isAdjointPair_iff_comp_eq_compl₂
  结论: IsAdjointPair B B' f g ↔ B'.comp f = B.compl₂ g
  证明: by
  constructor <;> intro h
  · ext x y
    rw [comp_apply]; rw [compl₂_apply]
    exact h x y
  · intro _ _
    rw [← compl₂_apply]; rw [← comp_apply]; rw [h]

Depends on / 依赖: comp_apply
-/
theorem isAdjointPair_iff_comp_eq_compl₂ : IsAdjointPair B B' f g ↔ B'.comp f = B.compl₂ g := by
  constructor <;> intro h
  · ext x y
    rw [comp_apply]; rw [compl₂_apply]
    exact h x y
  · intro _ _
    rw [← compl₂_apply]; rw [← comp_apply]; rw [h]

/--
theorem `isAdjointPair_zero` / 定理 `isAdjointPair_zero`

English:
theorem isAdjointPair_zero
  statement: IsAdjointPair B B' 0 0
  proof: fun _ _ => by
  simp only [Pi.zero_apply, map_zero, zero_apply]

中文:
定理 isAdjointPair_zero
  结论: IsAdjointPair B B' 0 0
  证明: fun _ _ => by
  simp only [Pi.zero_apply, map_zero, zero_apply]

Depends on / 依赖: Pi.zero_apply, map_zero, zero_apply
-/
theorem isAdjointPair_zero : IsAdjointPair B B' 0 0 := fun _ _ => by
  simp only [Pi.zero_apply, map_zero, zero_apply]

/--
theorem `isAdjointPair_id` / 定理 `isAdjointPair_id`

English:
theorem isAdjointPair_id
  statement: IsAdjointPair B B (_root_.id : M -> M) (_root_.id : M -> M)
  proof: fun _ _ => rfl

中文:
定理 isAdjointPair_id
  结论: IsAdjointPair B B (_root_.id : M -> M) (_root_.id : M -> M)
  证明: fun _ _ => rfl
-/
theorem isAdjointPair_id : IsAdjointPair B B (_root_.id : M -> M) (_root_.id : M -> M) :=
  fun _ _ => rfl

/--
theorem `isAdjointPair_one` / 定理 `isAdjointPair_one`

English:
theorem isAdjointPair_one
  statement: IsAdjointPair B B (1 : Module.End R M) (1 : Module.End R M)
  proof: isAdjointPair_id

中文:
定理 isAdjointPair_one
  结论: IsAdjointPair B B (1 : 模.End R M) (1 : 模.End R M)
  证明: isAdjointPair_id

Depends on / 依赖: isAdjointPair_id
-/
theorem isAdjointPair_one : IsAdjointPair B B (1 : Module.End R M) (1 : Module.End R M) :=
  isAdjointPair_id

/--
theorem `IsAdjointPair.add` / 定理 `IsAdjointPair.add`

English:
theorem IsAdjointPair.add
  statement: {f f' : M -> M₁} {g g' : M₁ -> M} (h : IsAdjointPair B B' f g)
  proof: fun x _ => by
  rw [Pi.add_apply]; rw [Pi.add_apply]; rw [B'.map_add₂]; rw [(B x).map_add]; rw [h]; rw [h']

中文:
定理 IsAdjointPair.add
  结论: {f f' : M -> M₁} {g g' : M₁ -> M} (h : IsAdjointPair B B' f g)
  证明: fun x _ => by
  rw [Pi.add_apply]; rw [Pi.add_apply]; rw [B'.map_add₂]; rw [(B x).map_add]; rw [h]; rw [h']

Depends on / 依赖: Pi.add_apply, add_apply, map_add
-/
theorem IsAdjointPair.add {f f' : M -> M₁} {g g' : M₁ -> M} (h : IsAdjointPair B B' f g)
    (h' : IsAdjointPair B B' f' g') :
    IsAdjointPair B B' (f + f') (g + g') := fun x _ => by
  rw [Pi.add_apply]; rw [Pi.add_apply]; rw [B'.map_add₂]; rw [(B x).map_add]; rw [h]; rw [h']

/--
theorem `IsAdjointPair.comp` / 定理 `IsAdjointPair.comp`

English:
theorem IsAdjointPair.comp
  statement: {f : M -> M₁} {g : M₁ -> M} {f' : M₁ -> M₂} {g' : M₂ -> M₁}
  proof: fun _ _ => by
  rw [Function.comp_def]; rw [Function.comp_def]; rw [h']; rw [h]

中文:
定理 IsAdjointPair.comp
  结论: {f : M -> M₁} {g : M₁ -> M} {f' : M₁ -> M₂} {g' : M₂ -> M₁}
  证明: fun _ _ => by
  rw [Function.comp_def]; rw [Function.comp_def]; rw [h']; rw [h]

Depends on / 依赖: Function, Function.comp_def, comp_def
-/
theorem IsAdjointPair.comp {f : M -> M₁} {g : M₁ -> M} {f' : M₁ -> M₂} {g' : M₂ -> M₁}
    (h : IsAdjointPair B B' f g) (h' : IsAdjointPair B' B'' f' g') :
    IsAdjointPair B B'' (f' ∘ f) (g ∘ g') := fun _ _ => by
  rw [Function.comp_def]; rw [Function.comp_def]; rw [h']; rw [h]

/--
theorem `IsAdjointPair.mul` / 定理 `IsAdjointPair.mul`

English:
theorem IsAdjointPair.mul
  statement: {f g f' g' : Module.End R M} (h : IsAdjointPair B B f g)
  proof: h'.comp h

中文:
定理 IsAdjointPair.mul
  结论: {f g f' g' : 模.End R M} (h : IsAdjointPair B B f g)
  证明: h'.comp h
-/
theorem IsAdjointPair.mul {f g f' g' : Module.End R M} (h : IsAdjointPair B B f g)
    (h' : IsAdjointPair B B f' g') : IsAdjointPair B B (f * f') (g' * g) :=
  h'.comp h

end AddCommMonoid

section AddCommGroup

variable [CommRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup M₁] [Module R M₁]
variable [AddCommGroup M₂] [Module R M₂]
variable {B F : M ->ₗ[R] M ->ₗ[R] M₂} {B' : M₁ ->ₗ[R] M₁ ->ₗ[R] M₂}
variable {f f' : M -> M₁} {g g' : M₁ -> M}

/--
theorem `IsAdjointPair.sub` / 定理 `IsAdjointPair.sub`

English:
theorem IsAdjointPair.sub
  given: (h : IsAdjointPair B B' f g) (h' : IsAdjointPair B B' f' g')
  proof: fun x _ => by
  rw [Pi.sub_apply]; rw [Pi.sub_apply]; rw [B'.map_sub₂]; rw [(B x).map_sub]; rw [h]; rw [h']

中文:
定理 IsAdjointPair.sub
  条件: (h : IsAdjointPair B B' f g) (h' : IsAdjointPair B B' f' g')
  证明: fun x _ => by
  rw [Pi.sub_apply]; rw [Pi.sub_apply]; rw [B'.map_sub₂]; rw [(B x).map_sub]; rw [h]; rw [h']

Depends on / 依赖: Pi.sub_apply, map_sub, sub_apply
-/
theorem IsAdjointPair.sub (h : IsAdjointPair B B' f g) (h' : IsAdjointPair B B' f' g') :
    IsAdjointPair B B' (f - f') (g - g') := fun x _ => by
  rw [Pi.sub_apply]; rw [Pi.sub_apply]; rw [B'.map_sub₂]; rw [(B x).map_sub]; rw [h]; rw [h']

/--
theorem `IsAdjointPair.smul` / 定理 `IsAdjointPair.smul`

English:
theorem IsAdjointPair.smul
  given: (c : R) (h : IsAdjointPair B B' f g)
  proof: fun _ _ => by
  simp [h _]

中文:
定理 IsAdjointPair.smul
  条件: (c : R) (h : IsAdjointPair B B' f g)
  证明: fun _ _ => by
  simp [h _]
-/
theorem IsAdjointPair.smul (c : R) (h : IsAdjointPair B B' f g) :
    IsAdjointPair B B' (c • f) (c • g) := fun _ _ => by
  simp [h _]

end AddCommGroup

section OrthogonalMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (B : LinearMap.BilinForm R M) (f : M -> M)

/--
Definition of `IsOrthogonal` / `IsOrthogonal` 的定义

English:
definition IsOrthogonal
  signature: : Prop
  body: forall x y, B (f x) (f y) = B x y

中文:
定义 IsOrthogonal
  签名: : 命题
  定义体: forall x y, B (f x) (f y) = B x y
-/
def IsOrthogonal : Prop :=
  forall x y, B (f x) (f y) = B x y

variable {B f}

@[simp]
/--
lemma `_root_.LinearEquiv.isAdjointPair_symm_iff` / 引理 `_root_.LinearEquiv.isAdjointPair_symm_iff`

English:
lemma _root_.LinearEquiv.isAdjointPair_symm_iff
  given: {f : M ≃ M}
  proof: ⟨fun hf x y => by simpa using hf x (f y), fun hf x y => by simpa using hf x (f.symm y)⟩

中文:
引理 _root_.线性等价.isAdjointPair_symm_iff
  条件: {f : M ≃ M}
  证明: ⟨fun hf x y => by simpa using hf x (f y), fun hf x y => by simpa using hf x (f.symm y)⟩

Depends on / 依赖: f.symm
-/
lemma _root_.LinearEquiv.isAdjointPair_symm_iff {f : M ≃ M} :
    LinearMap.IsAdjointPair B B f f.symm ↔ B.IsOrthogonal f :=
  ⟨fun hf x y => by simpa using hf x (f y), fun hf x y => by simpa using hf x (f.symm y)⟩

/--
lemma `isOrthogonal_of_forall_apply_same` / 引理 `isOrthogonal_of_forall_apply_same`

English:
lemma isOrthogonal_of_forall_apply_same
  statement: {F : Type*} [FunLike F M M] [LinearMapClass F R M M]
  proof: by
  intro x y
  suffices 2 * B (f x) (f y) = 2 * B x y from h this
  have := hf (x + y)
  simp only [map_add, LinearMap.add_apply, hf x, hf y, show B y x = B x y from hB.eq y x] at this
  rw [show B (f y) (f x) = B (f x) (f y) from hB.eq (f y) (f x)] at this
  simp only [add_assoc, add_right_inj] at this
  simp only [← add_assoc, add_left_inj] at this
  simpa only [← two_mul] using this

中文:
引理 isOrthogonal_of_对任意_apply_same
  结论: {F : 类型} [函数状 F M M] [线性映射类 F R M M]
  证明: by
  intro x y
  suffices 2 * B (f x) (f y) = 2 * B x y from h this
  have := hf (x + y)
  simp only [map_add, LinearMap.add_apply, hf x, hf y, show B y x = B x y from hB.eq y x] at this
  rw [show B (f y) (f x) = B (f x) (f y) from hB.eq (f y) (f x)] at this
  simp only [add_assoc, add_right_inj] at this
  simp only [← add_assoc, add_left_inj] at this
  simpa only [← two_mul] using this

Depends on / 依赖: LinearMap, LinearMap.add_apply, add_apply, add_assoc, add_left_inj, add_right_inj, hB.eq, map_add, two_mul
-/
lemma isOrthogonal_of_forall_apply_same {F : Type*} [FunLike F M M] [LinearMapClass F R M M]
    (f : F) (h : IsLeftRegular (2 : R)) (hB : B.IsSymm) (hf : forall x, B (f x) (f x) = B x x) :
    B.IsOrthogonal f := by
  intro x y
  suffices 2 * B (f x) (f y) = 2 * B x y from h this
  have := hf (x + y)
  simp only [map_add, LinearMap.add_apply, hf x, hf y, show B y x = B x y from hB.eq y x] at this
  rw [show B (f y) (f x) = B (f x) (f y) from hB.eq (f y) (f x)] at this
  simp only [add_assoc, add_right_inj] at this
  simp only [← add_assoc, add_left_inj] at this
  simpa only [← two_mul] using this

end OrthogonalMap

end AdjointPair

/-! ### Self-adjoint pairs -/

section SelfadjointPair

section AddCommMonoid

variable [CommSemiring R]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid M₁] [Module R M₁]
variable {I : R ->+* R}
variable (B F : M ->ₗ[R] M ->ₛₗ[I] M₁)

/--
Definition of `IsPairSelfAdjoint` / `IsPairSelfAdjoint` 的定义

English:
definition IsPairSelfAdjoint
  signature: (f : M -> M)
  body: IsAdjointPair B F f f

中文:
定义 IsPairSelfAdjoint
  签名: (f : M -> M)
  定义体: IsAdjointPair B F f f

Depends on / 依赖: IsAdjointPair
-/
def IsPairSelfAdjoint (f : M -> M) :=
  IsAdjointPair B F f f

/--
Definition of `IsSelfAdjoint` / `IsSelfAdjoint` 的定义

English:
definition IsSelfAdjoint
  signature: (f : M -> M)
  body: IsAdjointPair B B f f

中文:
定义 IsSelfAdjoint
  签名: (f : M -> M)
  定义体: IsAdjointPair B B f f
-/
protected def IsSelfAdjoint (f : M -> M) :=
  IsAdjointPair B B f f

end AddCommMonoid

section AddCommGroup

variable [CommRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup M₁] [Module R M₁]
variable [AddCommGroup M₂] [Module R M₂] (B F : M ->ₗ[R] M ->ₗ[R] M₂)

/--
Definition of `isPairSelfAdjointSubmodule` / `isPairSelfAdjointSubmodule` 的定义

English:
definition isPairSelfAdjointSubmodule
  signature: : Submodule R (Module.End R M) where
  body: { f | IsPairSelfAdjoint B F f }
  zero_mem' := isAdjointPair_zero
  add_mem' hf hg := hf.add hg
  smul_mem' c _ h := h.smul c

中文:
定义 isPairSelfAdjointSubmodule
  签名: : 子模 R (模.End R M) where
  定义体: { f | IsPairSelfAdjoint B F f }
  zero_mem' := isAdjointPair_zero
  add_mem' hf hg := hf.add hg
  smul_mem' c _ h := h.smul c

Depends on / 依赖: IsPairSelfAdjoint
-/
def isPairSelfAdjointSubmodule : Submodule R (Module.End R M) where
  carrier := { f | IsPairSelfAdjoint B F f }
  zero_mem' := isAdjointPair_zero
  add_mem' hf hg := hf.add hg
  smul_mem' c _ h := h.smul c

/--
Definition of `IsSkewAdjoint` / `IsSkewAdjoint` 的定义

English:
definition IsSkewAdjoint
  signature: (f : M -> M)
  body: IsAdjointPair B B f (-f)

中文:
定义 IsSkewAdjoint
  签名: (f : M -> M)
  定义体: IsAdjointPair B B f (-f)

Depends on / 依赖: IsAdjointPair
-/
def IsSkewAdjoint (f : M -> M) :=
  IsAdjointPair B B f (-f)

/--
Definition of `selfAdjointSubmodule` / `selfAdjointSubmodule` 的定义

English:
definition selfAdjointSubmodule
  body: isPairSelfAdjointSubmodule B B

中文:
定义 selfAdjointSubmodule
  定义体: isPairSelfAdjointSubmodule B B

Depends on / 依赖: isPairSelfAdjointSubmodule
-/
def selfAdjointSubmodule :=
  isPairSelfAdjointSubmodule B B

/--
Definition of `skewAdjointSubmodule` / `skewAdjointSubmodule` 的定义

English:
definition skewAdjointSubmodule
  body: isPairSelfAdjointSubmodule (-B) B

中文:
定义 skewAdjointSubmodule
  定义体: isPairSelfAdjointSubmodule (-B) B

Depends on / 依赖: isPairSelfAdjointSubmodule
-/
def skewAdjointSubmodule :=
  isPairSelfAdjointSubmodule (-B) B

variable {B F}

@[simp]
/--
theorem `mem_isPairSelfAdjointSubmodule` / 定理 `mem_isPairSelfAdjointSubmodule`

English:
theorem mem_isPairSelfAdjointSubmodule
  given: (f : Module.End R M)
  proof: Iff.rfl

中文:
定理 mem_isPairSelfAdjointSubmodule
  条件: (f : 模.End R M)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_isPairSelfAdjointSubmodule (f : Module.End R M) :
    f in isPairSelfAdjointSubmodule B F ↔ IsPairSelfAdjoint B F f :=
  Iff.rfl

/--
theorem `isPairSelfAdjoint_equiv` / 定理 `isPairSelfAdjoint_equiv`

English:
theorem isPairSelfAdjoint_equiv
  given: (e : M₁ ≃ₗ[R] M) (f : Module.End R M)
  proof: by
  have hₗ :
    (F.compl₁₂ (↑e : M₁ ->ₗ[R] M) (↑e : M₁ ->ₗ[R] M)).comp (e.symm.conj f) =
      (F.comp f).compl₁₂ (↑e : M₁ ->ₗ[R] M) (↑e : M₁ ->ₗ[R] M) := by
    ext
    simp only [LinearEquiv.symm_conj_apply, coe_comp, LinearEquiv.coe_coe, compl₁₂_apply,
      LinearEquiv.apply_symm_apply, Function.comp_apply]
  have hᵣ :
    (B.compl₁₂ (↑e : M₁ ->ₗ[R] M) (↑e : M₁ ->ₗ[R] M)).compl₂ (e.symm.conj f) =
      (B.compl₂ f).compl₁₂ (↑e : M₁ ->ₗ[R] M) (↑e : M₁ ->ₗ[R] M) := by
    ext
    simp only [LinearEquiv.symm_conj_apply, compl₂_apply, coe_comp, LinearEquiv.coe_coe,
      compl₁₂_apply, LinearEquiv.apply_symm_apply, Function.comp_apply]
  have he : Function.Surjective (⇑(↑e : M₁ ->ₗ[R] M) : M₁ -> M) := e.surjective
  simp_rw [IsPairSelfAdjoint, isAdjointPair_iff_comp_eq_compl₂, hₗ, hᵣ, compl₁₂_inj he he]

中文:
定理 isPairSelfAdjoint_equiv
  条件: (e : M₁ ≃ₗ[R] M) (f : 模.End R M)
  证明: by
  have hₗ :
    (F.compl₁₂ (↑e : M₁ ->ₗ[R] M) (↑e : M₁ ->ₗ[R] M)).comp (e.symm.conj f) =
      (F.comp f).compl₁₂ (↑e : M₁ ->ₗ[R] M) (↑e : M₁ ->ₗ[R] M) := by
    ext
    simp only [LinearEquiv.symm_conj_apply, coe_comp, LinearEquiv.coe_coe, compl₁₂_apply,
      LinearEquiv.apply_symm_apply, Function.comp_apply]
  have hᵣ :
    (B.compl₁₂ (↑e : M₁ ->ₗ[R] M) (↑e : M₁ ->ₗ[R] M)).compl₂ (e.symm.conj f) =
      (B.compl₂ f).compl₁₂ (↑e : M₁ ->ₗ[R] M) (↑e : M₁ ->ₗ[R] M) := by
    ext
    simp only [LinearEquiv.symm_conj_apply, compl₂_apply, coe_comp, LinearEquiv.coe_coe,
      compl₁₂_apply, LinearEquiv.apply_symm_apply, Function.comp_apply]
  have he : Function.Surjective (⇑(↑e : M₁ ->ₗ[R] M) : M₁ -> M) := e.surjective
  simp_rw [IsPairSelfAdjoint, isAdjointPair_iff_comp_eq_compl₂, hₗ, hᵣ, compl₁₂_inj he he]

Depends on / 依赖: B.compl, F.comp, F.compl, Function, Function.comp_apply, LinearEquiv, LinearEquiv.apply_symm_apply, LinearEquiv.coe_coe, LinearEquiv.symm_conj_apply, apply_symm_apply, coe_coe, coe_comp, comp_apply, e.symm.conj, symm_conj_apply
-/
theorem isPairSelfAdjoint_equiv (e : M₁ ≃ₗ[R] M) (f : Module.End R M) :
    IsPairSelfAdjoint B F f ↔
      IsPairSelfAdjoint (B.compl₁₂ e e) (F.compl₁₂ e e) (e.symm.conj f) := by
  have hₗ :
    (F.compl₁₂ (↑e : M₁ ->ₗ[R] M) (↑e : M₁ ->ₗ[R] M)).comp (e.symm.conj f) =
      (F.comp f).compl₁₂ (↑e : M₁ ->ₗ[R] M) (↑e : M₁ ->ₗ[R] M) := by
    ext
    simp only [LinearEquiv.symm_conj_apply, coe_comp, LinearEquiv.coe_coe, compl₁₂_apply,
      LinearEquiv.apply_symm_apply, Function.comp_apply]
  have hᵣ :
    (B.compl₁₂ (↑e : M₁ ->ₗ[R] M) (↑e : M₁ ->ₗ[R] M)).compl₂ (e.symm.conj f) =
      (B.compl₂ f).compl₁₂ (↑e : M₁ ->ₗ[R] M) (↑e : M₁ ->ₗ[R] M) := by
    ext
    simp only [LinearEquiv.symm_conj_apply, compl₂_apply, coe_comp, LinearEquiv.coe_coe,
      compl₁₂_apply, LinearEquiv.apply_symm_apply, Function.comp_apply]
  have he : Function.Surjective (⇑(↑e : M₁ ->ₗ[R] M) : M₁ -> M) := e.surjective
  simp_rw [IsPairSelfAdjoint, isAdjointPair_iff_comp_eq_compl₂, hₗ, hᵣ, compl₁₂_inj he he]

/--
theorem `isSkewAdjoint_iff_neg_self_adjoint` / 定理 `isSkewAdjoint_iff_neg_self_adjoint`

English:
theorem isSkewAdjoint_iff_neg_self_adjoint
  given: (f : M -> M)
  proof: show (forall x y, B (f x) y = B x ((-f) y)) ↔ forall x y, B (f x) y = (-B) x (f y) by simp

@[simp]

中文:
定理 isSkewAdjoint_iff_neg_self_adjoint
  条件: (f : M -> M)
  证明: show (forall x y, B (f x) y = B x ((-f) y)) ↔ forall x y, B (f x) y = (-B) x (f y) by simp

@[simp]
-/
theorem isSkewAdjoint_iff_neg_self_adjoint (f : M -> M) :
    B.IsSkewAdjoint f ↔ IsAdjointPair (-B) B f f :=
  show (forall x y, B (f x) y = B x ((-f) y)) ↔ forall x y, B (f x) y = (-B) x (f y) by simp

@[simp]
/--
theorem `mem_selfAdjointSubmodule` / 定理 `mem_selfAdjointSubmodule`

English:
theorem mem_selfAdjointSubmodule
  given: (f : Module.End R M)
  proof: Iff.rfl

@[simp]

中文:
定理 mem_selfAdjointSubmodule
  条件: (f : 模.End R M)
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_selfAdjointSubmodule (f : Module.End R M) :
    f in B.selfAdjointSubmodule ↔ B.IsSelfAdjoint f :=
  Iff.rfl

@[simp]
/--
theorem `mem_skewAdjointSubmodule` / 定理 `mem_skewAdjointSubmodule`

English:
theorem mem_skewAdjointSubmodule
  given: (f : Module.End R M)
  proof: by
  rw [isSkewAdjoint_iff_neg_self_adjoint]
  exact Iff.rfl

中文:
定理 mem_skewAdjointSubmodule
  条件: (f : 模.End R M)
  证明: by
  rw [isSkewAdjoint_iff_neg_self_adjoint]
  exact Iff.rfl

Depends on / 依赖: Iff.rfl, isSkewAdjoint_iff_neg_self_adjoint
-/
theorem mem_skewAdjointSubmodule (f : Module.End R M) :
    f in B.skewAdjointSubmodule ↔ B.IsSkewAdjoint f := by
  rw [isSkewAdjoint_iff_neg_self_adjoint]
  exact Iff.rfl

end AddCommGroup

end SelfadjointPair

/-! ### Nondegenerate bilinear maps -/

section Nondegenerate

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [CommSemiring R₁] [AddCommMonoid M₁]
  [Module R₁ M₁] [CommSemiring R₂] [AddCommMonoid M₂] [Module R₂ M₂]
  {I₁ : R₁ ->+* R} {I₂ : R₂ ->+* R} {I₁' : R₁ ->+* R}

/--
Definition of `SeparatingLeft` / `SeparatingLeft` 的定义

English:
definition SeparatingLeft
  signature: (B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M)
  body: forall x : M₁, (forall y : M₂, B x y = 0) -> x = 0

中文:
定义 SeparatingLeft
  签名: (B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M)
  定义体: forall x : M₁, (forall y : M₂, B x y = 0) -> x = 0
-/
def SeparatingLeft (B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M) : Prop :=
  forall x : M₁, (forall y : M₂, B x y = 0) -> x = 0

variable (M₁ M₂ I₁ I₂)

/--
theorem `not_separatingLeft_zero` / 定理 `not_separatingLeft_zero`

English:
theorem not_separatingLeft_zero
  given: [Nontrivial M₁]
  statement: ¬(0 : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M).SeparatingLeft
  proof: let ⟨m, hm⟩ := exists_ne (0 : M₁)
  fun h => hm (h m fun _n => rfl)

中文:
定理 not_separatingLeft_zero
  条件: [非平凡 M₁]
  结论: ¬(0 : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M).SeparatingLeft
  证明: let ⟨m, hm⟩ := exists_ne (0 : M₁)
  fun h => hm (h m fun _n => rfl)

Depends on / 依赖: exists_ne
-/
theorem not_separatingLeft_zero [Nontrivial M₁] : ¬(0 : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M).SeparatingLeft :=
  let ⟨m, hm⟩ := exists_ne (0 : M₁)
  fun h => hm (h m fun _n => rfl)

variable {M₁ M₂ I₁ I₂}

/--
theorem `SeparatingLeft.ne_zero` / 定理 `SeparatingLeft.ne_zero`

English:
theorem SeparatingLeft.ne_zero
  statement: [Nontrivial M₁] {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M}
  proof: fun h0 => not_separatingLeft_zero M₁ M₂ I₁ I₂ h0 ▸ h

中文:
定理 SeparatingLeft.ne_zero
  结论: [非平凡 M₁] {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M}
  证明: fun h0 => not_separatingLeft_zero M₁ M₂ I₁ I₂ h0 ▸ h

Depends on / 依赖: not_separatingLeft_zero
-/
theorem SeparatingLeft.ne_zero [Nontrivial M₁] {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M}
(h : B.SeparatingLeft) : B != 0 := fun h0 => not_separatingLeft_zero M₁ M₂ I₁ I₂ h0 ▸ h

/--
Definition of `SeparatingRight` / `SeparatingRight` 的定义

English:
definition SeparatingRight
  signature: (B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M)
  body: forall y : M₂, (forall x : M₁, B x y = 0) -> y = 0

中文:
定义 SeparatingRight
  签名: (B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M)
  定义体: forall y : M₂, (forall x : M₁, B x y = 0) -> y = 0
-/
def SeparatingRight (B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M) : Prop :=
  forall y : M₂, (forall x : M₁, B x y = 0) -> y = 0

/--
Definition of `Nondegenerate` / `Nondegenerate` 的定义

English:
definition Nondegenerate
  signature: (B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M)
  body: SeparatingLeft B ∧ SeparatingRight B

中文:
定义 非退化
  签名: (B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M)
  定义体: SeparatingLeft B ∧ SeparatingRight B

Depends on / 依赖: SeparatingLeft, SeparatingRight
-/
def Nondegenerate (B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M) : Prop :=
  SeparatingLeft B ∧ SeparatingRight B

section Linear

variable [AddCommMonoid Mₗ₁] [AddCommMonoid Mₗ₂] [AddCommMonoid Mₗ₁'] [AddCommMonoid Mₗ₂']

variable [Module R Mₗ₁] [Module R Mₗ₂] [Module R Mₗ₁'] [Module R Mₗ₂']
variable {B : Mₗ₁ ->ₗ[R] Mₗ₂ ->ₗ[R] M} (e₁ : Mₗ₁ ≃ₗ[R] Mₗ₁') (e₂ : Mₗ₂ ≃ₗ[R] Mₗ₂')

/--
theorem `SeparatingLeft.congr` / 定理 `SeparatingLeft.congr`

English:
theorem SeparatingLeft.congr
  given: (h : B.SeparatingLeft)
  proof: by
  intro x hx
  rw [← e₁.symm.map_eq_zero_iff]
  refine h (e₁.symm x) fun y => ?_
  specialize hx (e₂ y)
  simp only [LinearEquiv.arrowCongr_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.map_eq_zero_iff] at hx
  exact hx

中文:
定理 SeparatingLeft.congr
  条件: (h : B.SeparatingLeft)
  证明: by
  intro x hx
  rw [← e₁.symm.map_eq_zero_iff]
  refine h (e₁.symm x) fun y => ?_
  specialize hx (e₂ y)
  simp only [LinearEquiv.arrowCongr_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.map_eq_zero_iff] at hx
  exact hx

Depends on / 依赖: LinearEquiv, LinearEquiv.arrowCongr_apply, LinearEquiv.map_eq_zero_iff, LinearEquiv.symm_apply_apply, arrowCongr_apply, map_eq_zero_iff, specialize, symm.map_eq_zero_iff, symm_apply_apply
-/
theorem SeparatingLeft.congr (h : B.SeparatingLeft) :
    (e₁.arrowCongr (e₂.arrowCongr (LinearEquiv.refl R M)) B).SeparatingLeft := by
  intro x hx
  rw [← e₁.symm.map_eq_zero_iff]
  refine h (e₁.symm x) fun y => ?_
  specialize hx (e₂ y)
  simp only [LinearEquiv.arrowCongr_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.map_eq_zero_iff] at hx
  exact hx

/--
theorem `SeparatingRight.congr` / 定理 `SeparatingRight.congr`

English:
theorem SeparatingRight.congr
  given: (h : B.SeparatingRight)
  proof: SeparatingLeft.congr (B := B.flip) e₂ e₁ h

中文:
定理 SeparatingRight.congr
  条件: (h : B.SeparatingRight)
  证明: SeparatingLeft.congr (B := B.flip) e₂ e₁ h

Depends on / 依赖: B.flip, SeparatingLeft, SeparatingLeft.congr
-/
theorem SeparatingRight.congr (h : B.SeparatingRight) :
    (e₁.arrowCongr (e₂.arrowCongr (LinearEquiv.refl R M)) B).SeparatingRight :=
  SeparatingLeft.congr (B := B.flip) e₂ e₁ h

/--
theorem `Nondegenerate.congr` / 定理 `Nondegenerate.congr`

English:
theorem Nondegenerate.congr
  given: (h : B.Nondegenerate)
  proof: ⟨h.1.congr e₁ e₂, h.2.congr e₁ e₂⟩

@[simp]

中文:
定理 非退化.congr
  条件: (h : B.非退化)
  证明: ⟨h.1.congr e₁ e₂, h.2.congr e₁ e₂⟩

@[simp]
-/
theorem Nondegenerate.congr (h : B.Nondegenerate) :
    (e₁.arrowCongr (e₂.arrowCongr (LinearEquiv.refl R M)) B).Nondegenerate :=
  ⟨h.1.congr e₁ e₂, h.2.congr e₁ e₂⟩

@[simp]
/--
theorem `separatingLeft_congr_iff` / 定理 `separatingLeft_congr_iff`

English:
theorem separatingLeft_congr_iff
  proof: ⟨fun h => by
    convert! h.congr e₁.symm e₂.symm
    ext x y
    simp,
   SeparatingLeft.congr e₁ e₂⟩

@[simp]

中文:
定理 separatingLeft_congr_iff
  证明: ⟨fun h => by
    convert! h.congr e₁.symm e₂.symm
    ext x y
    simp,
   SeparatingLeft.congr e₁ e₂⟩

@[simp]

Depends on / 依赖: SeparatingLeft, SeparatingLeft.congr, convert, h.congr
-/
theorem separatingLeft_congr_iff :
    (e₁.arrowCongr (e₂.arrowCongr (LinearEquiv.refl R M)) B).SeparatingLeft ↔ B.SeparatingLeft :=
  ⟨fun h => by
    convert! h.congr e₁.symm e₂.symm
    ext x y
    simp,
   SeparatingLeft.congr e₁ e₂⟩

@[simp]
/--
theorem `separatingRight_congr_iff` / 定理 `separatingRight_congr_iff`

English:
theorem separatingRight_congr_iff
  statement: (e₁.arrowCongr (e₂.arrowCongr (LinearEquiv.refl R M))
  proof: separatingLeft_congr_iff (B := B.flip) e₂ e₁

@[simp]

中文:
定理 separatingRight_congr_iff
  结论: (e₁.arrowCongr (e₂.arrowCongr (线性等价.refl R M))
  证明: separatingLeft_congr_iff (B := B.flip) e₂ e₁

@[simp]

Depends on / 依赖: B.flip, separatingLeft_congr_iff
-/
theorem separatingRight_congr_iff : (e₁.arrowCongr (e₂.arrowCongr (LinearEquiv.refl R M))
      B).SeparatingRight ↔ B.SeparatingRight :=
  separatingLeft_congr_iff (B := B.flip) e₂ e₁

@[simp]
/--
theorem `nondegenerate_congr_iff` / 定理 `nondegenerate_congr_iff`

English:
theorem nondegenerate_congr_iff
  proof: .mp h.2⟩, .mp h.1, separatingRight_congr_iff e₁ e₂ ⟨fun h => ⟨separatingLeft_congr_iff e₁ e₂
    .congr e₁ e₂⟩

中文:
定理 nondegenerate_congr_iff
  证明: .mp h.2⟩, .mp h.1, separatingRight_congr_iff e₁ e₂ ⟨fun h => ⟨separatingLeft_congr_iff e₁ e₂
    .congr e₁ e₂⟩

Depends on / 依赖: separatingLeft_congr_iff, separatingRight_congr_iff
-/
theorem nondegenerate_congr_iff :
    (e₁.arrowCongr (e₂.arrowCongr (LinearEquiv.refl R M)) B).Nondegenerate ↔ B.Nondegenerate :=
.mp h.2⟩, .mp h.1, separatingRight_congr_iff e₁ e₂ ⟨fun h => ⟨separatingLeft_congr_iff e₁ e₂
    .congr e₁ e₂⟩

end Linear

@[simp]
/--
theorem `flip_separatingRight` / 定理 `flip_separatingRight`

English:
theorem flip_separatingRight
  given: {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M}
  proof: ⟨fun hB x hy => hB x hy, fun hB x hy => hB x hy⟩

@[simp]

中文:
定理 flip_separatingRight
  条件: {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M}
  证明: ⟨fun hB x hy => hB x hy, fun hB x hy => hB x hy⟩

@[simp]
-/
theorem flip_separatingRight {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} :
    B.flip.SeparatingRight ↔ B.SeparatingLeft :=
  ⟨fun hB x hy => hB x hy, fun hB x hy => hB x hy⟩

@[simp]
/--
theorem `flip_separatingLeft` / 定理 `flip_separatingLeft`

English:
theorem flip_separatingLeft
  given: {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M}
  proof: by rw [← flip_separatingRight, flip_flip]

@[simp]

中文:
定理 flip_separatingLeft
  条件: {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M}
  证明: by rw [← flip_separatingRight, flip_flip]

@[simp]

Depends on / 依赖: flip_flip, flip_separatingRight
-/
theorem flip_separatingLeft {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} :
    B.flip.SeparatingLeft ↔ SeparatingRight B := by rw [← flip_separatingRight, flip_flip]

@[simp]
/--
theorem `flip_nondegenerate` / 定理 `flip_nondegenerate`

English:
theorem flip_nondegenerate
  given: {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M}
  statement: B.flip.Nondegenerate ↔ B.Nondegenerate
  proof: Iff.trans and_comm (and_congr flip_separatingRight flip_separatingLeft)

中文:
定理 flip_nondegenerate
  条件: {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M}
  结论: B.flip.非退化 ↔ B.非退化
  证明: Iff.trans and_comm (and_congr flip_separatingRight flip_separatingLeft)

Depends on / 依赖: Iff.trans, and_comm, and_congr, flip_separatingLeft, flip_separatingRight
-/
theorem flip_nondegenerate {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} : B.flip.Nondegenerate ↔ B.Nondegenerate :=
  Iff.trans and_comm (and_congr flip_separatingRight flip_separatingLeft)

/--
theorem `separatingLeft_iff_linear_nontrivial` / 定理 `separatingLeft_iff_linear_nontrivial`

English:
theorem separatingLeft_iff_linear_nontrivial
  given: {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M}
  proof: by
  constructor <;> intro h x hB
  · simpa only [hB, zero_apply, eq_self_iff_true, forall_const] using h x
  have h' : B x = 0 := by
    ext
    rw [zero_apply]
    exact hB _
  exact h x h'

中文:
定理 separatingLeft_iff_linear_nontrivial
  条件: {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M}
  证明: by
  constructor <;> intro h x hB
  · simpa only [hB, zero_apply, eq_self_iff_true, forall_const] using h x
  have h' : B x = 0 := by
    ext
    rw [zero_apply]
    exact hB _
  exact h x h'

Depends on / 依赖: eq_self_iff_true, forall_const, zero_apply
-/
theorem separatingLeft_iff_linear_nontrivial {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} :
    B.SeparatingLeft ↔ forall x : M₁, B x = 0 -> x = 0 := by
  constructor <;> intro h x hB
  · simpa only [hB, zero_apply, eq_self_iff_true, forall_const] using h x
  have h' : B x = 0 := by
    ext
    rw [zero_apply]
    exact hB _
  exact h x h'

/--
theorem `separatingRight_iff_linear_flip_nontrivial` / 定理 `separatingRight_iff_linear_flip_nontrivial`

English:
theorem separatingRight_iff_linear_flip_nontrivial
  given: {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M}
  proof: by
  rw [← flip_separatingLeft]; rw [separatingLeft_iff_linear_nontrivial]

中文:
定理 separatingRight_iff_linear_flip_nontrivial
  条件: {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M}
  证明: by
  rw [← flip_separatingLeft]; rw [separatingLeft_iff_linear_nontrivial]

Depends on / 依赖: flip_separatingLeft, separatingLeft_iff_linear_nontrivial
-/
theorem separatingRight_iff_linear_flip_nontrivial {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} :
    B.SeparatingRight ↔ forall y : M₂, B.flip y = 0 -> y = 0 := by
  rw [← flip_separatingLeft]; rw [separatingLeft_iff_linear_nontrivial]

/--
theorem `separatingLeft_iff_ker_eq_bot` / 定理 `separatingLeft_iff_ker_eq_bot`

English:
theorem separatingLeft_iff_ker_eq_bot
  given: {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M}
  proof: Iff.trans separatingLeft_iff_linear_nontrivial LinearMap.ker_eq_bot'.symm

中文:
定理 separatingLeft_iff_ker_eq_bot
  条件: {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M}
  证明: Iff.trans separatingLeft_iff_linear_nontrivial LinearMap.ker_eq_bot'.symm

Depends on / 依赖: Iff.trans, LinearMap, LinearMap.ker_eq_bot, ker_eq_bot, separatingLeft_iff_linear_nontrivial
-/
theorem separatingLeft_iff_ker_eq_bot {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} :
    B.SeparatingLeft ↔ LinearMap.ker B = ⊥ :=
  Iff.trans separatingLeft_iff_linear_nontrivial LinearMap.ker_eq_bot'.symm

/--
theorem `separatingRight_iff_flip_ker_eq_bot` / 定理 `separatingRight_iff_flip_ker_eq_bot`

English:
theorem separatingRight_iff_flip_ker_eq_bot
  given: {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M}
  proof: by
  rw [← flip_separatingLeft]; rw [separatingLeft_iff_ker_eq_bot]

中文:
定理 separatingRight_iff_flip_ker_eq_bot
  条件: {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M}
  证明: by
  rw [← flip_separatingLeft]; rw [separatingLeft_iff_ker_eq_bot]

Depends on / 依赖: flip_separatingLeft, separatingLeft_iff_ker_eq_bot
-/
theorem separatingRight_iff_flip_ker_eq_bot {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} :
    B.SeparatingRight ↔ LinearMap.ker B.flip = ⊥ := by
  rw [← flip_separatingLeft]; rw [separatingLeft_iff_ker_eq_bot]

end CommSemiring

section CommRing

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M₁] [Module R M₁] {I I' : R ->+* R}

/--
theorem `IsRefl.nondegenerate_iff_separatingLeft` / 定理 `IsRefl.nondegenerate_iff_separatingLeft`

English:
theorem IsRefl.nondegenerate_iff_separatingLeft
  given: {B : M ->ₗ[R] M ->ₗ[R] M₁} (hB : B.IsRefl)
  proof: by
  refine ⟨fun h => h.1, fun hB' => ⟨hB', ?_⟩⟩
  rw [separatingRight_iff_flip_ker_eq_bot]; rw [hB.ker_eq_bot_iff_ker_flip_eq_bot.mp]
  rwa [← separatingLeft_iff_ker_eq_bot]

中文:
定理 IsRefl.nondegenerate_iff_separatingLeft
  条件: {B : M ->ₗ[R] M ->ₗ[R] M₁} (hB : B.IsRefl)
  证明: by
  refine ⟨fun h => h.1, fun hB' => ⟨hB', ?_⟩⟩
  rw [separatingRight_iff_flip_ker_eq_bot]; rw [hB.ker_eq_bot_iff_ker_flip_eq_bot.mp]
  rwa [← separatingLeft_iff_ker_eq_bot]

Depends on / 依赖: hB.ker_eq_bot_iff_ker_flip_eq_bot.mp, ker_eq_bot_iff_ker_flip_eq_bot, separatingLeft_iff_ker_eq_bot, separatingRight_iff_flip_ker_eq_bot
-/
theorem IsRefl.nondegenerate_iff_separatingLeft {B : M ->ₗ[R] M ->ₗ[R] M₁} (hB : B.IsRefl) :
    B.Nondegenerate ↔ B.SeparatingLeft := by
  refine ⟨fun h => h.1, fun hB' => ⟨hB', ?_⟩⟩
  rw [separatingRight_iff_flip_ker_eq_bot]; rw [hB.ker_eq_bot_iff_ker_flip_eq_bot.mp]
  rwa [← separatingLeft_iff_ker_eq_bot]

/--
theorem `IsRefl.nondegenerate_iff_separatingRight` / 定理 `IsRefl.nondegenerate_iff_separatingRight`

English:
theorem IsRefl.nondegenerate_iff_separatingRight
  given: {B : M ->ₗ[R] M ->ₗ[R] M₁} (hB : B.IsRefl)
  proof: by
  refine ⟨fun h => h.2, fun hB' => ⟨?_, hB'⟩⟩
  rw [separatingLeft_iff_ker_eq_bot]; rw [hB.ker_eq_bot_iff_ker_flip_eq_bot.mpr]
  rwa [← separatingRight_iff_flip_ker_eq_bot]

中文:
定理 IsRefl.nondegenerate_iff_separatingRight
  条件: {B : M ->ₗ[R] M ->ₗ[R] M₁} (hB : B.IsRefl)
  证明: by
  refine ⟨fun h => h.2, fun hB' => ⟨?_, hB'⟩⟩
  rw [separatingLeft_iff_ker_eq_bot]; rw [hB.ker_eq_bot_iff_ker_flip_eq_bot.mpr]
  rwa [← separatingRight_iff_flip_ker_eq_bot]

Depends on / 依赖: hB.ker_eq_bot_iff_ker_flip_eq_bot.mpr, ker_eq_bot_iff_ker_flip_eq_bot, separatingLeft_iff_ker_eq_bot, separatingRight_iff_flip_ker_eq_bot
-/
theorem IsRefl.nondegenerate_iff_separatingRight {B : M ->ₗ[R] M ->ₗ[R] M₁} (hB : B.IsRefl) :
    B.Nondegenerate ↔ B.SeparatingRight := by
  refine ⟨fun h => h.2, fun hB' => ⟨?_, hB'⟩⟩
  rw [separatingLeft_iff_ker_eq_bot]; rw [hB.ker_eq_bot_iff_ker_flip_eq_bot.mpr]
  rwa [← separatingRight_iff_flip_ker_eq_bot]

/--
lemma `disjoint_ker_of_nondegenerate_restrict` / 引理 `disjoint_ker_of_nondegenerate_restrict`

English:
lemma disjoint_ker_of_nondegenerate_restrict
  statement: {B : M ->ₗ[R] M ->ₗ[R] M₁} {W : Submodule R M}
  proof: by
  refine Submodule.disjoint_def.mpr fun x hx hx' => ?_
  let x' : W := ⟨x, hx⟩
  suffices x' = 0 by simpa [x']
  apply hW.1 x'
  simp_rw [Subtype.forall, domRestrict₁₂_apply]
  intro y hy
  rw [mem_ker] at hx'
  simp [x', hx']

中文:
引理 disjoint_ker_of_nondegenerate_restrict
  结论: {B : M ->ₗ[R] M ->ₗ[R] M₁} {W : 子模 R M}
  证明: by
  refine Submodule.disjoint_def.mpr fun x hx hx' => ?_
  let x' : W := ⟨x, hx⟩
  suffices x' = 0 by simpa [x']
  apply hW.1 x'
  simp_rw [Subtype.forall, domRestrict₁₂_apply]
  intro y hy
  rw [mem_ker] at hx'
  simp [x', hx']

Depends on / 依赖: Submodule, Submodule.disjoint_def.mpr, Subtype, Subtype.forall, disjoint_def, mem_ker, simp_rw
-/
lemma disjoint_ker_of_nondegenerate_restrict {B : M ->ₗ[R] M ->ₗ[R] M₁} {W : Submodule R M}
    (hW : (B.domRestrict₁₂ W W).Nondegenerate) :
    Disjoint W (LinearMap.ker B) := by
  refine Submodule.disjoint_def.mpr fun x hx hx' => ?_
  let x' : W := ⟨x, hx⟩
  suffices x' = 0 by simpa [x']
  apply hW.1 x'
  simp_rw [Subtype.forall, domRestrict₁₂_apply]
  intro y hy
  rw [mem_ker] at hx'
  simp [x', hx']

/--
lemma `IsSymm.nondegenerate_restrict_of_isCompl_ker` / 引理 `IsSymm.nondegenerate_restrict_of_isCompl_ker`

English:
lemma IsSymm.nondegenerate_restrict_of_isCompl_ker
  statement: {B : M ->ₗ[R] M ->ₗ[R] R} (hB : B.IsSymm)
  proof: by
  have hB' : (B.domRestrict₁₂ W W).IsRefl := fun x y => hB.isRefl (W.subtype x) (W.subtype y)
  rw [LinearMap.IsRefl.nondegenerate_iff_separatingLeft hB']
  intro ⟨x, hx⟩ hx'
  simp only [Submodule.mk_eq_zero]
  replace hx' : forall y in W, B x y = 0 := by simpa [Subtype.forall] using! hx'
  replace hx' : x in W ⊓ ker B := by
    refine ⟨hx, ?_⟩
    ext y
    obtain ⟨u, hu, v, hv, rfl⟩ : exists u in W, exists v in ker B, u + v = y := by
      rw [← Submodule.mem_sup]; rw [hW.sup_eq_top]; exact Submodule.mem_top
    suffices B x u = 0 by rw [mem_ker] at hv; simpa [← hB.eq v, hv]
    exact hx' u hu
  simpa [hW.inf_eq_bot] using! hx'

中文:
引理 是Symm.nondegenerate_restrict_of_isCompl_ker
  结论: {B : M ->ₗ[R] M ->ₗ[R] R} (hB : B.是Symm)
  证明: by
  have hB' : (B.domRestrict₁₂ W W).IsRefl := fun x y => hB.isRefl (W.subtype x) (W.subtype y)
  rw [LinearMap.IsRefl.nondegenerate_iff_separatingLeft hB']
  intro ⟨x, hx⟩ hx'
  simp only [Submodule.mk_eq_zero]
  replace hx' : forall y in W, B x y = 0 := by simpa [Subtype.forall] using! hx'
  replace hx' : x in W ⊓ ker B := by
    refine ⟨hx, ?_⟩
    ext y
    obtain ⟨u, hu, v, hv, rfl⟩ : exists u in W, exists v in ker B, u + v = y := by
      rw [← Submodule.mem_sup]; rw [hW.sup_eq_top]; exact Submodule.mem_top
    suffices B x u = 0 by rw [mem_ker] at hv; simpa [← hB.eq v, hv]
    exact hx' u hu
  simpa [hW.inf_eq_bot] using! hx'

Depends on / 依赖: B.domRestrict, IsRefl, LinearMap, LinearMap.IsRefl.nondegenerate_iff_separatingLeft, Submodule, Submodule.mem_sup, Submodule.mem_top, Submodule.mk_eq_zero, Subtype, Subtype.forall, W.subtype, hB.isRefl, hW.sup_eq_top, isRefl, mem_sup, mem_top, mk_eq_zero, nondegenerate_iff_separatingLeft, replace, subtype
-/
lemma IsSymm.nondegenerate_restrict_of_isCompl_ker {B : M ->ₗ[R] M ->ₗ[R] R} (hB : B.IsSymm)
    {W : Submodule R M} (hW : IsCompl W (LinearMap.ker B)) :
    (B.domRestrict₁₂ W W).Nondegenerate := by
  have hB' : (B.domRestrict₁₂ W W).IsRefl := fun x y => hB.isRefl (W.subtype x) (W.subtype y)
  rw [LinearMap.IsRefl.nondegenerate_iff_separatingLeft hB']
  intro ⟨x, hx⟩ hx'
  simp only [Submodule.mk_eq_zero]
  replace hx' : forall y in W, B x y = 0 := by simpa [Subtype.forall] using! hx'
  replace hx' : x in W ⊓ ker B := by
    refine ⟨hx, ?_⟩
    ext y
    obtain ⟨u, hu, v, hv, rfl⟩ : exists u in W, exists v in ker B, u + v = y := by
      rw [← Submodule.mem_sup]; rw [hW.sup_eq_top]; exact Submodule.mem_top
    suffices B x u = 0 by rw [mem_ker] at hv; simpa [← hB.eq v, hv]
    exact hx' u hu
  simpa [hW.inf_eq_bot] using! hx'

end CommRing

section IsOrthoᵢ

variable {R M M₁ : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M₁]
    [Module R M] [Module R M₁] {I I' : R ->+* R} {B : M ->ₛₗ[I] M ->ₛₗ[I'] M₁}

/--
theorem `IsOrthoᵢ.not_isOrtho_basis_self_of_separatingLeft` / 定理 `IsOrthoᵢ.not_isOrtho_basis_self_of_separatingLeft`

English:
theorem IsOrthoᵢ.not_isOrtho_basis_self_of_separatingLeft
  statement: [Nontrivial R]
  proof: by
  intro ho
  refine v.ne_zero i (hB (v i) fun m => ?_)
  obtain ⟨vi, rfl⟩ := v.repr.symm.surjective m
  rw [Basis.repr_symm_apply]; rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum]; rw [map_sum]
  apply Finset.sum_eq_zero
  rintro j -
  rw [map_smulₛₗ]
  suffices B (v i) (v j) = 0 by rw [this, smul_zero]
  obtain rfl | hij := eq_or_ne i j
  · exact ho
  · exact h hij

中文:
定理 IsOrthoᵢ.not_isOrtho_basis_self_of_separatingLeft
  结论: [非平凡 R]
  证明: by
  intro ho
  refine v.ne_zero i (hB (v i) fun m => ?_)
  obtain ⟨vi, rfl⟩ := v.repr.symm.surjective m
  rw [Basis.repr_symm_apply]; rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum]; rw [map_sum]
  apply Finset.sum_eq_zero
  rintro j -
  rw [map_smulₛₗ]
  suffices B (v i) (v j) = 0 by rw [this, smul_zero]
  obtain rfl | hij := eq_or_ne i j
  · exact ho
  · exact h hij

Depends on / 依赖: Basis.repr_symm_apply, Finset, Finset.sum_eq_zero, Finsupp, Finsupp.linearCombination_apply, Finsupp.sum, eq_or_ne, linearCombination_apply, map_sum, ne_zero, repr_symm_apply, smul_zero, sum_eq_zero, surjective, v.ne_zero, v.repr.symm.surjective
-/
theorem IsOrthoᵢ.not_isOrtho_basis_self_of_separatingLeft [Nontrivial R]
    {v : Basis n R M} (h : B.IsOrthoᵢ v) (hB : B.SeparatingLeft)
    (i : n) : B (v i) (v i) != 0 := by
  intro ho
  refine v.ne_zero i (hB (v i) fun m => ?_)
  obtain ⟨vi, rfl⟩ := v.repr.symm.surjective m
  rw [Basis.repr_symm_apply]; rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum]; rw [map_sum]
  apply Finset.sum_eq_zero
  rintro j -
  rw [map_smulₛₗ]
  suffices B (v i) (v j) = 0 by rw [this, smul_zero]
  obtain rfl | hij := eq_or_ne i j
  · exact ho
  · exact h hij

/--
theorem `IsOrthoᵢ.not_isOrtho_basis_self_of_separatingRight` / 定理 `IsOrthoᵢ.not_isOrtho_basis_self_of_separatingRight`

English:
theorem IsOrthoᵢ.not_isOrtho_basis_self_of_separatingRight
  statement: [Nontrivial R]
  proof: by
  rw [isOrthoᵢ_flip] at h
  exact h.not_isOrtho_basis_self_of_separatingLeft (flip_separatingLeft.mpr hB) i

中文:
定理 IsOrthoᵢ.not_isOrtho_basis_self_of_separatingRight
  结论: [非平凡 R]
  证明: by
  rw [isOrthoᵢ_flip] at h
  exact h.not_isOrtho_basis_self_of_separatingLeft (flip_separatingLeft.mpr hB) i

Depends on / 依赖: flip_separatingLeft, flip_separatingLeft.mpr, h.not_isOrtho_basis_self_of_separatingLeft, not_isOrtho_basis_self_of_separatingLeft
-/
theorem IsOrthoᵢ.not_isOrtho_basis_self_of_separatingRight [Nontrivial R]
    {v : Basis n R M} (h : B.IsOrthoᵢ v) (hB : B.SeparatingRight)
    (i : n) : B (v i) (v i) != 0 := by
  rw [isOrthoᵢ_flip] at h
  exact h.not_isOrtho_basis_self_of_separatingLeft (flip_separatingLeft.mpr hB) i

variable [IsDomain R] [IsTorsionFree R M₁]

/--
theorem `IsOrthoᵢ.separatingLeft_of_not_isOrtho_basis_self` / 定理 `IsOrthoᵢ.separatingLeft_of_not_isOrtho_basis_self`

English:
theorem IsOrthoᵢ.separatingLeft_of_not_isOrtho_basis_self
  statement: {B : M ->ₗ[R] M ->ₗ[R] M₁} (v : Basis n R M)
  proof: by
  intro m hB
  obtain ⟨vi, rfl⟩ := v.repr.symm.surjective m
  rw [LinearEquiv.map_eq_zero_iff]
  ext i
  rw [Finsupp.zero_apply]
  specialize hB (v i)
  simp_rw [Basis.repr_symm_apply, Finsupp.linearCombination_apply, Finsupp.sum, map_sum₂,
           map_smulₛₗ₂] at hB
  rw [Finset.sum_eq_single i] at hB
  · cases smul_eq_zero.mp hB
    · assumption
    · specialize h i
      contradiction
  · intro j _hj hij
    replace hij : B (v j) (v i) = 0 := hO hij
    rw [hij]; rw [RingHom.id_apply]; rw [smul_zero]
  · intro hi
    replace hi : vi i = 0 := Finsupp.notMem_support_iff.mp hi
    rw [hi]; rw [RingHom.id_apply]; rw [zero_smul]

中文:
定理 IsOrthoᵢ.separatingLeft_of_not_isOrtho_basis_self
  结论: {B : M ->ₗ[R] M ->ₗ[R] M₁} (v : 基 n R M)
  证明: by
  intro m hB
  obtain ⟨vi, rfl⟩ := v.repr.symm.surjective m
  rw [LinearEquiv.map_eq_zero_iff]
  ext i
  rw [Finsupp.zero_apply]
  specialize hB (v i)
  simp_rw [Basis.repr_symm_apply, Finsupp.linearCombination_apply, Finsupp.sum, map_sum₂,
           map_smulₛₗ₂] at hB
  rw [Finset.sum_eq_single i] at hB
  · cases smul_eq_zero.mp hB
    · assumption
    · specialize h i
      contradiction
  · intro j _hj hij
    replace hij : B (v j) (v i) = 0 := hO hij
    rw [hij]; rw [RingHom.id_apply]; rw [smul_zero]
  · intro hi
    replace hi : vi i = 0 := Finsupp.notMem_support_iff.mp hi
    rw [hi]; rw [RingHom.id_apply]; rw [zero_smul]

Depends on / 依赖: Basis.repr_symm_apply, Finset, Finset.sum_eq_single, Finsupp, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.zero_apply, LinearEquiv, LinearEquiv.map_eq_zero_iff, RingHom, RingHom.id_apply, id_apply, linearCombination_apply, map_eq_zero_iff, replace, repr_symm_apply, simp_rw, smul_eq_zero, smul_eq_zero.mp, smul_zero
-/
theorem IsOrthoᵢ.separatingLeft_of_not_isOrtho_basis_self {B : M ->ₗ[R] M ->ₗ[R] M₁} (v : Basis n R M)
    (hO : B.IsOrthoᵢ v) (h : forall i, B (v i) (v i) != 0) : B.SeparatingLeft := by
  intro m hB
  obtain ⟨vi, rfl⟩ := v.repr.symm.surjective m
  rw [LinearEquiv.map_eq_zero_iff]
  ext i
  rw [Finsupp.zero_apply]
  specialize hB (v i)
  simp_rw [Basis.repr_symm_apply, Finsupp.linearCombination_apply, Finsupp.sum, map_sum₂,
           map_smulₛₗ₂] at hB
  rw [Finset.sum_eq_single i] at hB
  · cases smul_eq_zero.mp hB
    · assumption
    · specialize h i
      contradiction
  · intro j _hj hij
    replace hij : B (v j) (v i) = 0 := hO hij
    rw [hij]; rw [RingHom.id_apply]; rw [smul_zero]
  · intro hi
    replace hi : vi i = 0 := Finsupp.notMem_support_iff.mp hi
    rw [hi]; rw [RingHom.id_apply]; rw [zero_smul]

/--
lemma `IsOrthoᵢ.separatingRight_iff_not_isOrtho_basis_self` / 引理 `IsOrthoᵢ.separatingRight_iff_not_isOrtho_basis_self`

English:
lemma IsOrthoᵢ.separatingRight_iff_not_isOrtho_basis_self
  statement: {B : M ->ₗ[R] M ->ₗ[R] M₁} (v : Basis n R M)
  proof: by
  rw [isOrthoᵢ_flip] at hO
  rw [← flip_separatingLeft]
  refine IsOrthoᵢ.separatingLeft_of_not_isOrtho_basis_self v hO fun i => ?_
  exact h i

中文:
引理 IsOrthoᵢ.separatingRight_iff_not_isOrtho_basis_self
  结论: {B : M ->ₗ[R] M ->ₗ[R] M₁} (v : 基 n R M)
  证明: by
  rw [isOrthoᵢ_flip] at hO
  rw [← flip_separatingLeft]
  refine IsOrthoᵢ.separatingLeft_of_not_isOrtho_basis_self v hO fun i => ?_
  exact h i

Depends on / 依赖: flip_separatingLeft, separatingLeft_of_not_isOrtho_basis_self
-/
lemma IsOrthoᵢ.separatingRight_iff_not_isOrtho_basis_self {B : M ->ₗ[R] M ->ₗ[R] M₁} (v : Basis n R M)
    (hO : B.IsOrthoᵢ v) (h : forall i, B (v i) (v i) != 0) : B.SeparatingRight := by
  rw [isOrthoᵢ_flip] at hO
  rw [← flip_separatingLeft]
  refine IsOrthoᵢ.separatingLeft_of_not_isOrtho_basis_self v hO fun i => ?_
  exact h i

/--
theorem `IsOrthoᵢ.nondegenerate_of_not_isOrtho_basis_self` / 定理 `IsOrthoᵢ.nondegenerate_of_not_isOrtho_basis_self`

English:
theorem IsOrthoᵢ.nondegenerate_of_not_isOrtho_basis_self
  statement: {B : M ->ₗ[R] M ->ₗ[R] M₁} (v : Basis n R M)
  proof: ⟨IsOrthoᵢ.separatingLeft_of_not_isOrtho_basis_self v hO h,
    IsOrthoᵢ.separatingRight_iff_not_isOrtho_basis_self v hO h⟩

中文:
定理 IsOrthoᵢ.nondegenerate_of_not_isOrtho_basis_self
  结论: {B : M ->ₗ[R] M ->ₗ[R] M₁} (v : 基 n R M)
  证明: ⟨IsOrthoᵢ.separatingLeft_of_not_isOrtho_basis_self v hO h,
    IsOrthoᵢ.separatingRight_iff_not_isOrtho_basis_self v hO h⟩

Depends on / 依赖: separatingLeft_of_not_isOrtho_basis_self, separatingRight_iff_not_isOrtho_basis_self
-/
theorem IsOrthoᵢ.nondegenerate_of_not_isOrtho_basis_self {B : M ->ₗ[R] M ->ₗ[R] M₁} (v : Basis n R M)
    (hO : B.IsOrthoᵢ v) (h : forall i, B (v i) (v i) != 0) : B.Nondegenerate :=
  ⟨IsOrthoᵢ.separatingLeft_of_not_isOrtho_basis_self v hO h,
    IsOrthoᵢ.separatingRight_iff_not_isOrtho_basis_self v hO h⟩

end IsOrthoᵢ

end Nondegenerate

namespace BilinForm

set_option backward.isDefEq.respectTransparency false in
/--
lemma `apply_smul_sub_smul_sub_eq` / 引理 `apply_smul_sub_smul_sub_eq`

English:
lemma apply_smul_sub_smul_sub_eq
  statement: [CommRing R] [AddCommGroup M] [Module R M]
  proof: by
  simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul, mul_sub,
    mul_comm (B x y) (B x x), mul_left_comm (B x y) (B x x)]
  abel

中文:
引理 apply_smul_sub_smul_sub_eq
  结论: [交换环 R] [加法交换群 M] [模 R M]
  证明: by
  simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul, mul_sub,
    mul_comm (B x y) (B x x), mul_left_comm (B x y) (B x x)]
  abel

Depends on / 依赖: map_smul, map_sub, mul_comm, mul_left_comm, mul_sub, smul_apply, smul_eq_mul, sub_apply
-/
lemma apply_smul_sub_smul_sub_eq [CommRing R] [AddCommGroup M] [Module R M]
    (B : LinearMap.BilinForm R M) (x y : M) :
    B ((B x y) • x - (B x x) • y) ((B x y) • x - (B x x) • y) =
      (B x x) * ((B x x) * (B y y) - (B x y) * (B y x)) := by
  simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul, mul_sub,
    mul_comm (B x y) (B x x), mul_left_comm (B x y) (B x x)]
  abel

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M] (B : LinearMap.BilinForm R M)

/-- The **Cauchy-Schwarz inequality** for positive semidefinite forms. -/
@[wikidata Q190546]
/--
lemma `apply_mul_apply_le_of_forall_zero_le` / 引理 `apply_mul_apply_le_of_forall_zero_le`

English:
lemma apply_mul_apply_le_of_forall_zero_le
  given: (hs : forall x, 0 <= B x x) (x y : M)
  proof: by
  have aux (x y : M) : 0 <= (B x x) * ((B x x) * (B y y) - (B x y) * (B y x)) := by
    rw [← apply_smul_sub_smul_sub_eq B x y]
    exact hs (B x y • x - B x x • y)
  rcases lt_or_ge 0 (B x x) with hx | hx
· exact sub_nonneg.mp nonneg_of_mul_nonneg_right (aux x y) hx
  · replace hx : B x x = 0 := le_antisymm hx (hs x)
    rcases lt_or_ge 0 (B y y) with hy | hy
    · rw [mul_comm (B x y), mul_comm (B x x)]
exact sub_nonneg.mp nonneg_of_mul_nonneg_right (aux y x) hy
    · replace hy : B y y = 0 := le_antisymm hy (hs y)
      suffices B x y = - B y x by simpa [this, hx, hy] using mul_self_nonneg (B y x)
      rw [eq_neg_iff_add_eq_zero]
      apply le_antisymm
      · simpa [hx, hy, le_neg_iff_add_nonpos_left] using hs (x - y)
      · simpa [hx, hy] using hs (x + y)

中文:
引理 apply_mul_apply_le_of_对任意_zero_le
  条件: (hs : 对任意 x, 0 <= B x x) (x y : M)
  证明: by
  have aux (x y : M) : 0 <= (B x x) * ((B x x) * (B y y) - (B x y) * (B y x)) := by
    rw [← apply_smul_sub_smul_sub_eq B x y]
    exact hs (B x y • x - B x x • y)
  rcases lt_or_ge 0 (B x x) with hx | hx
· exact sub_nonneg.mp nonneg_of_mul_nonneg_right (aux x y) hx
  · replace hx : B x x = 0 := le_antisymm hx (hs x)
    rcases lt_or_ge 0 (B y y) with hy | hy
    · rw [mul_comm (B x y), mul_comm (B x x)]
exact sub_nonneg.mp nonneg_of_mul_nonneg_right (aux y x) hy
    · replace hy : B y y = 0 := le_antisymm hy (hs y)
      suffices B x y = - B y x by simpa [this, hx, hy] using mul_self_nonneg (B y x)
      rw [eq_neg_iff_add_eq_zero]
      apply le_antisymm
      · simpa [hx, hy, le_neg_iff_add_nonpos_left] using hs (x - y)
      · simpa [hx, hy] using hs (x + y)

Depends on / 依赖: apply_smul_sub_smul_sub_eq, le_antisymm, lt_or_ge, mul_comm, nonneg_of_mul_nonneg_right, replace, sub_nonneg, sub_nonneg.mp
-/
lemma apply_mul_apply_le_of_forall_zero_le (hs : forall x, 0 <= B x x) (x y : M) :
    (B x y) * (B y x) <= (B x x) * (B y y) := by
  have aux (x y : M) : 0 <= (B x x) * ((B x x) * (B y y) - (B x y) * (B y x)) := by
    rw [← apply_smul_sub_smul_sub_eq B x y]
    exact hs (B x y • x - B x x • y)
  rcases lt_or_ge 0 (B x x) with hx | hx
· exact sub_nonneg.mp nonneg_of_mul_nonneg_right (aux x y) hx
  · replace hx : B x x = 0 := le_antisymm hx (hs x)
    rcases lt_or_ge 0 (B y y) with hy | hy
    · rw [mul_comm (B x y), mul_comm (B x x)]
exact sub_nonneg.mp nonneg_of_mul_nonneg_right (aux y x) hy
    · replace hy : B y y = 0 := le_antisymm hy (hs y)
      suffices B x y = - B y x by simpa [this, hx, hy] using mul_self_nonneg (B y x)
      rw [eq_neg_iff_add_eq_zero]
      apply le_antisymm
      · simpa [hx, hy, le_neg_iff_add_nonpos_left] using hs (x - y)
      · simpa [hx, hy] using hs (x + y)

/--
lemma `apply_sq_le_of_symm` / 引理 `apply_sq_le_of_symm`

English:
lemma apply_sq_le_of_symm
  given: (hs : forall x, 0 <= B x x) (hB : B.IsSymm) (x y : M)
  proof: by
  rw [show (B x y) ^ 2 = (B x y) * (B y x) by rw [sq]; rw [← hB.eq]; rw [RingHom.id_apply]]
  exact apply_mul_apply_le_of_forall_zero_le B hs x y

中文:
引理 apply_sq_le_of_symm
  条件: (hs : 对任意 x, 0 <= B x x) (hB : B.是Symm) (x y : M)
  证明: by
  rw [show (B x y) ^ 2 = (B x y) * (B y x) by rw [sq]; rw [← hB.eq]; rw [RingHom.id_apply]]
  exact apply_mul_apply_le_of_forall_zero_le B hs x y

Depends on / 依赖: RingHom, RingHom.id_apply, apply_mul_apply_le_of_forall_zero_le, hB.eq, id_apply
-/
lemma apply_sq_le_of_symm (hs : forall x, 0 <= B x x) (hB : B.IsSymm) (x y : M) :
    (B x y) ^ 2 <= (B x x) * (B y y) := by
  rw [show (B x y) ^ 2 = (B x y) * (B y x) by rw [sq]; rw [← hB.eq]; rw [RingHom.id_apply]]
  exact apply_mul_apply_le_of_forall_zero_le B hs x y

/--
lemma `not_linearIndependent_of_apply_mul_apply_eq` / 引理 `not_linearIndependent_of_apply_mul_apply_eq`

English:
lemma not_linearIndependent_of_apply_mul_apply_eq
  statement: (hp : forall x, x != 0 -> 0 < B x x)
  proof: by
  have hz : (B x y) • x - (B x x) • y = 0 := by
    by_contra hc
exact (ne_of_lt (hp ((B x) y • x - (B x) x • y) hc)).symm
      (apply_smul_sub_smul_sub_eq B x y).symm ▸ (mul_eq_zero_of_right ((B x) x)
      (sub_eq_zero_of_eq he.symm))
  by_contra hL
  by_cases hx : x = 0
  · simpa [hx] using LinearIndependent.ne_zero 0 hL
  · have h := sub_eq_zero.mpr (sub_eq_zero.mp hz).symm
    rw [sub_eq_add_neg]; rw [← neg_smul]; rw [add_comm] at h
    exact (Ne.symm (ne_of_lt (hp x hx))) (LinearIndependent.eq_zero_of_pair hL h).2

中文:
引理 not_linearIndependent_of_apply_mul_apply_eq
  结论: (hp : 对任意 x, x != 0 -> 0 < B x x)
  证明: by
  have hz : (B x y) • x - (B x x) • y = 0 := by
    by_contra hc
exact (ne_of_lt (hp ((B x) y • x - (B x) x • y) hc)).symm
      (apply_smul_sub_smul_sub_eq B x y).symm ▸ (mul_eq_zero_of_right ((B x) x)
      (sub_eq_zero_of_eq he.symm))
  by_contra hL
  by_cases hx : x = 0
  · simpa [hx] using LinearIndependent.ne_zero 0 hL
  · have h := sub_eq_zero.mpr (sub_eq_zero.mp hz).symm
    rw [sub_eq_add_neg]; rw [← neg_smul]; rw [add_comm] at h
    exact (Ne.symm (ne_of_lt (hp x hx))) (LinearIndependent.eq_zero_of_pair hL h).2

Depends on / 依赖: LinearIndependent, LinearIndependent.eq_zero_of_pair, LinearIndependent.ne_zero, Ne.symm, add_comm, apply_smul_sub_smul_sub_eq, eq_zero_of_pair, he.symm, mul_eq_zero_of_right, ne_of_lt, ne_zero, neg_smul, sub_eq_add_neg, sub_eq_zero, sub_eq_zero.mp, sub_eq_zero.mpr, sub_eq_zero_of_eq
-/
lemma not_linearIndependent_of_apply_mul_apply_eq (hp : forall x, x != 0 -> 0 < B x x)
    (x y : M) (he : (B x y) * (B y x) = (B x x) * (B y y)) :
    ¬ LinearIndependent R ![x, y] := by
  have hz : (B x y) • x - (B x x) • y = 0 := by
    by_contra hc
exact (ne_of_lt (hp ((B x) y • x - (B x) x • y) hc)).symm
      (apply_smul_sub_smul_sub_eq B x y).symm ▸ (mul_eq_zero_of_right ((B x) x)
      (sub_eq_zero_of_eq he.symm))
  by_contra hL
  by_cases hx : x = 0
  · simpa [hx] using LinearIndependent.ne_zero 0 hL
  · have h := sub_eq_zero.mpr (sub_eq_zero.mp hz).symm
    rw [sub_eq_add_neg]; rw [← neg_smul]; rw [add_comm] at h
    exact (Ne.symm (ne_of_lt (hp x hx))) (LinearIndependent.eq_zero_of_pair hL h).2

/--
lemma `apply_apply_same_eq_zero_iff` / 引理 `apply_apply_same_eq_zero_iff`

English:
lemma apply_apply_same_eq_zero_iff
  given: (hs : forall x, 0 <= B x x) (hB : B.IsSymm) {x : M}
  proof: by
  rw [LinearMap.mem_ker]
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  ext y
  have := B.apply_sq_le_of_symm hs hB x y
  simp only [h, zero_mul] at this
exact eq_zero_of_pow_eq_zero le_antisymm this (sq_nonneg (B x y))

中文:
引理 apply_apply_same_eq_zero_iff
  条件: (hs : 对任意 x, 0 <= B x x) (hB : B.是Symm) {x : M}
  证明: by
  rw [LinearMap.mem_ker]
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  ext y
  have := B.apply_sq_le_of_symm hs hB x y
  simp only [h, zero_mul] at this
exact eq_zero_of_pow_eq_zero le_antisymm this (sq_nonneg (B x y))

Depends on / 依赖: B.apply_sq_le_of_symm, LinearMap, LinearMap.mem_ker, apply_sq_le_of_symm, eq_zero_of_pow_eq_zero, le_antisymm, mem_ker, sq_nonneg, zero_mul
-/
lemma apply_apply_same_eq_zero_iff (hs : forall x, 0 <= B x x) (hB : B.IsSymm) {x : M} :
    B x x = 0 ↔ x in LinearMap.ker B := by
  rw [LinearMap.mem_ker]
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  ext y
  have := B.apply_sq_le_of_symm hs hB x y
  simp only [h, zero_mul] at this
exact eq_zero_of_pow_eq_zero le_antisymm this (sq_nonneg (B x y))

/--
lemma `nondegenerate_iff` / 引理 `nondegenerate_iff`

English:
lemma nondegenerate_iff
  given: (hs : forall x, 0 <= B x x) (hB : B.IsSymm)
  proof: by
  simp_rw [hB.isRefl.nondegenerate_iff_separatingLeft, separatingLeft_iff_ker_eq_bot,
    Submodule.eq_bot_iff, B.apply_apply_same_eq_zero_iff hs hB, mem_ker]
  exact forall_congr' fun x => by aesop

中文:
引理 nondegenerate_iff
  条件: (hs : 对任意 x, 0 <= B x x) (hB : B.是Symm)
  证明: by
  simp_rw [hB.isRefl.nondegenerate_iff_separatingLeft, separatingLeft_iff_ker_eq_bot,
    Submodule.eq_bot_iff, B.apply_apply_same_eq_zero_iff hs hB, mem_ker]
  exact forall_congr' fun x => by aesop

Depends on / 依赖: B.apply_apply_same_eq_zero_iff, Submodule, Submodule.eq_bot_iff, apply_apply_same_eq_zero_iff, eq_bot_iff, forall_congr, hB.isRefl.nondegenerate_iff_separatingLeft, isRefl, mem_ker, nondegenerate_iff_separatingLeft, separatingLeft_iff_ker_eq_bot, simp_rw
-/
lemma nondegenerate_iff (hs : forall x, 0 <= B x x) (hB : B.IsSymm) :
    B.Nondegenerate ↔ forall x, B x x = 0 ↔ x = 0 := by
  simp_rw [hB.isRefl.nondegenerate_iff_separatingLeft, separatingLeft_iff_ker_eq_bot,
    Submodule.eq_bot_iff, B.apply_apply_same_eq_zero_iff hs hB, mem_ker]
  exact forall_congr' fun x => by aesop

/--
lemma `nondegenerate_iff'` / 引理 `nondegenerate_iff'`

English:
lemma nondegenerate_iff'
  given: (hs : forall x, 0 <= B x x) (hB : B.IsSymm)
  proof: by
  rw [B.nondegenerate_iff hs hB]
  contrapose!
  exact exists_congr fun x => ⟨by aesop, fun ⟨h₀, h⟩ => Or.inl ⟨le_antisymm h (hs x), h₀⟩⟩

中文:
引理 nondegenerate_iff'
  条件: (hs : 对任意 x, 0 <= B x x) (hB : B.是Symm)
  证明: by
  rw [B.nondegenerate_iff hs hB]
  contrapose!
  exact exists_congr fun x => ⟨by aesop, fun ⟨h₀, h⟩ => Or.inl ⟨le_antisymm h (hs x), h₀⟩⟩

Depends on / 依赖: B.nondegenerate_iff, Or.inl, contrapose, exists_congr, le_antisymm, nondegenerate_iff
-/
lemma nondegenerate_iff' (hs : forall x, 0 <= B x x) (hB : B.IsSymm) :
    B.Nondegenerate ↔ forall x, x != 0 -> 0 < B x x := by
  rw [B.nondegenerate_iff hs hB]
  contrapose!
  exact exists_congr fun x => ⟨by aesop, fun ⟨h₀, h⟩ => Or.inl ⟨le_antisymm h (hs x), h₀⟩⟩

/--
lemma `nondegenerate_restrict_iff_disjoint_ker` / 引理 `nondegenerate_restrict_iff_disjoint_ker`

English:
lemma nondegenerate_restrict_iff_disjoint_ker
  statement: (hs : forall x, 0 <= B x x) (hB : B.IsSymm)
  proof: by
  refine ⟨disjoint_ker_of_nondegenerate_restrict, fun hW => ?_⟩
  have hB' : (B.domRestrict₁₂ W W).IsRefl := fun x y => hB.isRefl (W.subtype x) (W.subtype y)
  rw [IsRefl.nondegenerate_iff_separatingLeft hB']
  intro ⟨x, hx⟩ h
  simp_rw [Subtype.forall, domRestrict₁₂_apply] at h
  specialize h x hx
  rw [B.apply_apply_same_eq_zero_iff hs hB] at h
  have key : x in W ⊓ LinearMap.ker B := ⟨hx, h⟩
  simpa [hW.eq_bot] using key

中文:
引理 nondegenerate_restrict_iff_disjoint_ker
  结论: (hs : 对任意 x, 0 <= B x x) (hB : B.是Symm)
  证明: by
  refine ⟨disjoint_ker_of_nondegenerate_restrict, fun hW => ?_⟩
  have hB' : (B.domRestrict₁₂ W W).IsRefl := fun x y => hB.isRefl (W.subtype x) (W.subtype y)
  rw [IsRefl.nondegenerate_iff_separatingLeft hB']
  intro ⟨x, hx⟩ h
  simp_rw [Subtype.forall, domRestrict₁₂_apply] at h
  specialize h x hx
  rw [B.apply_apply_same_eq_zero_iff hs hB] at h
  have key : x in W ⊓ LinearMap.ker B := ⟨hx, h⟩
  simpa [hW.eq_bot] using key

Depends on / 依赖: B.apply_apply_same_eq_zero_iff, B.domRestrict, IsRefl, IsRefl.nondegenerate_iff_separatingLeft, LinearMap, LinearMap.ker, Subtype, Subtype.forall, W.subtype, apply_apply_same_eq_zero_iff, disjoint_ker_of_nondegenerate_restrict, eq_bot, hB.isRefl, hW.eq_bot, isRefl, nondegenerate_iff_separatingLeft, simp_rw, specialize, subtype
-/
lemma nondegenerate_restrict_iff_disjoint_ker (hs : forall x, 0 <= B x x) (hB : B.IsSymm)
    {W : Submodule R M} :
    (B.domRestrict₁₂ W W).Nondegenerate ↔ Disjoint W (LinearMap.ker B) := by
  refine ⟨disjoint_ker_of_nondegenerate_restrict, fun hW => ?_⟩
  have hB' : (B.domRestrict₁₂ W W).IsRefl := fun x y => hB.isRefl (W.subtype x) (W.subtype y)
  rw [IsRefl.nondegenerate_iff_separatingLeft hB']
  intro ⟨x, hx⟩ h
  simp_rw [Subtype.forall, domRestrict₁₂_apply] at h
  specialize h x hx
  rw [B.apply_apply_same_eq_zero_iff hs hB] at h
  have key : x in W ⊓ LinearMap.ker B := ⟨hx, h⟩
  simpa [hW.eq_bot] using key

variable [IsTorsionFree R M]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `apply_mul_apply_lt_iff_linearIndependent` / 引理 `apply_mul_apply_lt_iff_linearIndependent`

English:
lemma apply_mul_apply_lt_iff_linearIndependent
  given: (hp : forall x, x != 0 -> 0 < B x x) (x y : M)
  proof: by
  have hle z : 0 <= B z z := by obtain rfl | hz := eq_or_ne z 0 <;> simp [le_of_lt, *]
  constructor
  · contrapose!
    intro h
    rw [LinearIndependent.pair_iff] at h
    push Not at h
    obtain ⟨r, s, hl, h0⟩ := h
    by_cases hr : r = 0; · simp_all
    by_cases hs : s = 0; · simp_all
    suffices
        (B (r • x) (r • x)) * (B (s • y) (s • y)) = (B (r • x) (s • y)) * (B (s • y) (r • x)) by
      simp only [map_smul, smul_apply, smul_eq_mul] at this
      rw [show r * (r * (B x) x) * (s * (s * (B y) y)) = (r * r * s * s) * ((B x) x * (B y) y) by
        ring]; rw [show s * (r * (B x) y) * (r * (s * (B y) x)) = (r * r * s * s) * ((B x) y * (B y) x)
        by ring] at this
      have hrs : r * r * s * s != 0 := by simp [hr, hs]
exact le_of_eq mul_right_injective₀ hrs this
    simp [show s • y = - r • x by rwa [neg_smul, ← add_eq_zero_iff_eq_neg']]
  · contrapose!
    intro h
    exact not_linearIndependent_of_apply_mul_apply_eq B hp x y (le_antisymm
      (apply_mul_apply_le_of_forall_zero_le B hle x y) h)

中文:
引理 apply_mul_apply_lt_iff_linearIndependent
  条件: (hp : 对任意 x, x != 0 -> 0 < B x x) (x y : M)
  证明: by
  have hle z : 0 <= B z z := by obtain rfl | hz := eq_or_ne z 0 <;> simp [le_of_lt, *]
  constructor
  · contrapose!
    intro h
    rw [LinearIndependent.pair_iff] at h
    push Not at h
    obtain ⟨r, s, hl, h0⟩ := h
    by_cases hr : r = 0; · simp_all
    by_cases hs : s = 0; · simp_all
    suffices
        (B (r • x) (r • x)) * (B (s • y) (s • y)) = (B (r • x) (s • y)) * (B (s • y) (r • x)) by
      simp only [map_smul, smul_apply, smul_eq_mul] at this
      rw [show r * (r * (B x) x) * (s * (s * (B y) y)) = (r * r * s * s) * ((B x) x * (B y) y) by
        ring]; rw [show s * (r * (B x) y) * (r * (s * (B y) x)) = (r * r * s * s) * ((B x) y * (B y) x)
        by ring] at this
      have hrs : r * r * s * s != 0 := by simp [hr, hs]
exact le_of_eq mul_right_injective₀ hrs this
    simp [show s • y = - r • x by rwa [neg_smul, ← add_eq_zero_iff_eq_neg']]
  · contrapose!
    intro h
    exact not_linearIndependent_of_apply_mul_apply_eq B hp x y (le_antisymm
      (apply_mul_apply_le_of_forall_zero_le B hle x y) h)

Depends on / 依赖: LinearIndependent, LinearIndependent.pair_iff, contrapose, eq_or_ne, le_of_lt, map_smul, pair_iff, smul_apply, smul_eq_mul
-/
lemma apply_mul_apply_lt_iff_linearIndependent (hp : forall x, x != 0 -> 0 < B x x) (x y : M) :
    B x y * B y x < B x x * B y y ↔ LinearIndependent R ![x, y] := by
  have hle z : 0 <= B z z := by obtain rfl | hz := eq_or_ne z 0 <;> simp [le_of_lt, *]
  constructor
  · contrapose!
    intro h
    rw [LinearIndependent.pair_iff] at h
    push Not at h
    obtain ⟨r, s, hl, h0⟩ := h
    by_cases hr : r = 0; · simp_all
    by_cases hs : s = 0; · simp_all
    suffices
        (B (r • x) (r • x)) * (B (s • y) (s • y)) = (B (r • x) (s • y)) * (B (s • y) (r • x)) by
      simp only [map_smul, smul_apply, smul_eq_mul] at this
      rw [show r * (r * (B x) x) * (s * (s * (B y) y)) = (r * r * s * s) * ((B x) x * (B y) y) by
        ring]; rw [show s * (r * (B x) y) * (r * (s * (B y) x)) = (r * r * s * s) * ((B x) y * (B y) x)
        by ring] at this
      have hrs : r * r * s * s != 0 := by simp [hr, hs]
exact le_of_eq mul_right_injective₀ hrs this
    simp [show s • y = - r • x by rwa [neg_smul, ← add_eq_zero_iff_eq_neg']]
  · contrapose!
    intro h
    exact not_linearIndependent_of_apply_mul_apply_eq B hp x y (le_antisymm
      (apply_mul_apply_le_of_forall_zero_le B hle x y) h)

/--
lemma `apply_sq_lt_iff_linearIndependent_of_symm` / 引理 `apply_sq_lt_iff_linearIndependent_of_symm`

English:
lemma apply_sq_lt_iff_linearIndependent_of_symm
  statement: (hp : forall x, x != 0 -> 0 < B x x) (hB : B.IsSymm)
  proof: by
  rw [show B x y ^ 2 = B x y * B y x by rw [sq]; rw [← hB.eq]; rw [RingHom.id_apply]]
  exact apply_mul_apply_lt_iff_linearIndependent B hp x y

中文:
引理 apply_sq_lt_iff_linearIndependent_of_symm
  结论: (hp : 对任意 x, x != 0 -> 0 < B x x) (hB : B.是Symm)
  证明: by
  rw [show B x y ^ 2 = B x y * B y x by rw [sq]; rw [← hB.eq]; rw [RingHom.id_apply]]
  exact apply_mul_apply_lt_iff_linearIndependent B hp x y

Depends on / 依赖: RingHom, RingHom.id_apply, apply_mul_apply_lt_iff_linearIndependent, hB.eq, id_apply
-/
lemma apply_sq_lt_iff_linearIndependent_of_symm (hp : forall x, x != 0 -> 0 < B x x) (hB : B.IsSymm)
    (x y : M) : B x y ^ 2 < B x x * B y y ↔ LinearIndependent R ![x, y] := by
  rw [show B x y ^ 2 = B x y * B y x by rw [sq]; rw [← hB.eq]; rw [RingHom.id_apply]]
  exact apply_mul_apply_lt_iff_linearIndependent B hp x y

end BilinForm

end LinearMap
