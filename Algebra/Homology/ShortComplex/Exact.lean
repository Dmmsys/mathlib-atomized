/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.QuasiIso
public import Mathlib.CategoryTheory.Abelian.Opposite
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Exact short complexes

When `S : ShortComplex C`, this file defines a structure
`S.Exact` which expresses the exactness of `S`, i.e. there
exists a homology data `h : S.HomologyData` such that
`h.left.H` is zero. When `[S.HasHomology]`, it is equivalent
to the assertion `IsZero S.homology`.

Almost by construction, this notion of exactness is self dual,
see `Exact.op` and `Exact.unop`.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits ZeroObject Preadditive

variable {C D : Type*} [Category* C] [Category* D]

namespace ShortComplex

section

variable
  [HasZeroMorphisms C] [HasZeroMorphisms D] (S : ShortComplex C) {S₁ S₂ : ShortComplex C}

/--
Definition of `Exact` / `Exact` 的定义

English:
structure Exact
  parameters: : Prop where
  axioms and operations (1):
    - condition : exists (h : S.HomologyData), IsZero h.left.H

中文:
结构 正合
  参数: : 命题 where
  公理与运算 (1 个):
    - condition : 存在 (h : S.同调数据), 是零 h.left.H
-/
structure Exact : Prop where
  /-- the condition that there exists a homology data whose `left.H` field is zero -/
  condition : exists (h : S.HomologyData), IsZero h.left.H

variable {S}

/--
lemma `Exact.hasHomology` / 引理 `Exact.hasHomology`

English:
lemma Exact.hasHomology
  given: (h : S.Exact)
  statement: S.HasHomology
  proof: HasHomology.mk' h.condition.choose

中文:
引理 正合.hasHomology
  条件: (h : S.正合)
  结论: S.有同调
  证明: HasHomology.mk' h.condition.choose

Depends on / 依赖: HasHomology, HasHomology.mk, condition, h.condition.choose
-/
lemma Exact.hasHomology (h : S.Exact) : S.HasHomology :=
  HasHomology.mk' h.condition.choose

/--
lemma `Exact.hasZeroObject` / 引理 `Exact.hasZeroObject`

English:
lemma Exact.hasZeroObject
  given: (h : S.Exact)
  statement: HasZeroObject C
  proof: ⟨h.condition.choose.left.H, h.condition.choose_spec⟩

中文:
引理 正合.hasZeroObject
  条件: (h : S.正合)
  结论: 有ZeroObject C
  证明: ⟨h.condition.choose.left.H, h.condition.choose_spec⟩

Depends on / 依赖: choose_spec, condition, h.condition.choose.left.H, h.condition.choose_spec
-/
lemma Exact.hasZeroObject (h : S.Exact) : HasZeroObject C :=
  ⟨h.condition.choose.left.H, h.condition.choose_spec⟩

variable (S)

/--
lemma `exact_iff_isZero_homology` / 引理 `exact_iff_isZero_homology`

English:
lemma exact_iff_isZero_homology
  given: [S.HasHomology]
  proof: by
  constructor
  · rintro ⟨⟨h', z⟩⟩
    exact IsZero.of_iso z h'.left.homologyIso
  · intro h
    exact ⟨⟨_, h⟩⟩

中文:
引理 exact_iff_isZero_homology
  条件: [S.有同调]
  证明: by
  constructor
  · rintro ⟨⟨h', z⟩⟩
    exact IsZero.of_iso z h'.left.homologyIso
  · intro h
    exact ⟨⟨_, h⟩⟩

Depends on / 依赖: IsZero, IsZero.of_iso, homologyIso, left.homologyIso, of_iso
-/
lemma exact_iff_isZero_homology [S.HasHomology] :
    S.Exact ↔ IsZero S.homology := by
  constructor
  · rintro ⟨⟨h', z⟩⟩
    exact IsZero.of_iso z h'.left.homologyIso
  · intro h
    exact ⟨⟨_, h⟩⟩

variable {S}

/--
lemma `LeftHomologyData.exact_iff` / 引理 `LeftHomologyData.exact_iff`

English:
lemma LeftHomologyData.exact_iff
  statement: [S.HasHomology]
  proof: by
  rw [S.exact_iff_isZero_homology]
  exact Iso.isZero_iff h.homologyIso

中文:
引理 LeftHomologyData.exact_iff
  结论: [S.有同调]
  证明: by
  rw [S.exact_iff_isZero_homology]
  exact Iso.isZero_iff h.homologyIso

Depends on / 依赖: Iso.isZero_iff, S.exact_iff_isZero_homology, exact_iff_isZero_homology, h.homologyIso, homologyIso, isZero_iff
-/
lemma LeftHomologyData.exact_iff [S.HasHomology]
    (h : S.LeftHomologyData) :
    S.Exact ↔ IsZero h.H := by
  rw [S.exact_iff_isZero_homology]
  exact Iso.isZero_iff h.homologyIso

/--
lemma `RightHomologyData.exact_iff` / 引理 `RightHomologyData.exact_iff`

English:
lemma RightHomologyData.exact_iff
  statement: [S.HasHomology]
  proof: by
  rw [S.exact_iff_isZero_homology]
  exact Iso.isZero_iff h.homologyIso

中文:
引理 RightHomologyData.exact_iff
  结论: [S.有同调]
  证明: by
  rw [S.exact_iff_isZero_homology]
  exact Iso.isZero_iff h.homologyIso

Depends on / 依赖: Iso.isZero_iff, S.exact_iff_isZero_homology, exact_iff_isZero_homology, h.homologyIso, homologyIso, isZero_iff
-/
lemma RightHomologyData.exact_iff [S.HasHomology]
    (h : S.RightHomologyData) :
    S.Exact ↔ IsZero h.H := by
  rw [S.exact_iff_isZero_homology]
  exact Iso.isZero_iff h.homologyIso

variable (S)

/--
lemma `exact_iff_isZero_leftHomology` / 引理 `exact_iff_isZero_leftHomology`

English:
lemma exact_iff_isZero_leftHomology
  given: [S.HasHomology]
  proof: LeftHomologyData.exact_iff _

中文:
引理 exact_iff_isZero_leftHomology
  条件: [S.有同调]
  证明: LeftHomologyData.exact_iff _

Depends on / 依赖: LeftHomologyData, LeftHomologyData.exact_iff, exact_iff
-/
lemma exact_iff_isZero_leftHomology [S.HasHomology] :
    S.Exact ↔ IsZero S.leftHomology :=
  LeftHomologyData.exact_iff _

/--
lemma `exact_iff_isZero_rightHomology` / 引理 `exact_iff_isZero_rightHomology`

English:
lemma exact_iff_isZero_rightHomology
  given: [S.HasHomology]
  proof: RightHomologyData.exact_iff _

中文:
引理 exact_iff_isZero_rightHomology
  条件: [S.有同调]
  证明: RightHomologyData.exact_iff _

Depends on / 依赖: RightHomologyData, RightHomologyData.exact_iff, exact_iff
-/
lemma exact_iff_isZero_rightHomology [S.HasHomology] :
    S.Exact ↔ IsZero S.rightHomology :=
  RightHomologyData.exact_iff _

variable {S}

/--
lemma `HomologyData.exact_iff` / 引理 `HomologyData.exact_iff`

English:
lemma HomologyData.exact_iff
  given: (h : S.HomologyData)
  proof: by
  have := HasHomology.mk' h
  exact LeftHomologyData.exact_iff h.left

中文:
引理 同调数据.exact_iff
  条件: (h : S.同调数据)
  证明: by
  have := HasHomology.mk' h
  exact LeftHomologyData.exact_iff h.left

Depends on / 依赖: HasHomology, HasHomology.mk, LeftHomologyData, LeftHomologyData.exact_iff, exact_iff, h.left
-/
lemma HomologyData.exact_iff (h : S.HomologyData) :
    S.Exact ↔ IsZero h.left.H := by
  have := HasHomology.mk' h
  exact LeftHomologyData.exact_iff h.left

/--
lemma `HomologyData.exact_iff'` / 引理 `HomologyData.exact_iff'`

English:
lemma HomologyData.exact_iff'
  given: (h : S.HomologyData)
  proof: by
  have := HasHomology.mk' h
  exact RightHomologyData.exact_iff h.right

中文:
引理 同调数据.exact_iff'
  条件: (h : S.同调数据)
  证明: by
  have := HasHomology.mk' h
  exact RightHomologyData.exact_iff h.right

Depends on / 依赖: HasHomology, HasHomology.mk, RightHomologyData, RightHomologyData.exact_iff, exact_iff, h.right
-/
lemma HomologyData.exact_iff' (h : S.HomologyData) :
    S.Exact ↔ IsZero h.right.H := by
  have := HasHomology.mk' h
  exact RightHomologyData.exact_iff h.right

variable (S)

/--
lemma `exact_iff_homology_iso_zero` / 引理 `exact_iff_homology_iso_zero`

English:
lemma exact_iff_homology_iso_zero
  given: [S.HasHomology] [HasZeroObject C]
  proof: by
  rw [exact_iff_isZero_homology]
  constructor
  · intro h
    exact ⟨h.isoZero⟩
  · rintro ⟨e⟩
    exact IsZero.of_iso (isZero_zero C) e

中文:
引理 exact_iff_homology_iso_zero
  条件: [S.有同调] [有ZeroObject C]
  证明: by
  rw [exact_iff_isZero_homology]
  constructor
  · intro h
    exact ⟨h.isoZero⟩
  · rintro ⟨e⟩
    exact IsZero.of_iso (isZero_zero C) e

Depends on / 依赖: IsZero, IsZero.of_iso, exact_iff_isZero_homology, h.isoZero, isZero_zero, isoZero, of_iso
-/
lemma exact_iff_homology_iso_zero [S.HasHomology] [HasZeroObject C] :
    S.Exact ↔ Nonempty (S.homology ≅ 0) := by
  rw [exact_iff_isZero_homology]
  constructor
  · intro h
    exact ⟨h.isoZero⟩
  · rintro ⟨e⟩
    exact IsZero.of_iso (isZero_zero C) e

/--
lemma `exact_of_iso` / 引理 `exact_of_iso`

English:
lemma exact_of_iso
  given: (e : S₁ ≅ S₂) (h : S₁.Exact)
  statement: S₂.Exact
  proof: by
  obtain ⟨⟨h, z⟩⟩ := h
  exact ⟨⟨HomologyData.ofIso e h, z⟩⟩

中文:
引理 exact_of_iso
  条件: (e : S₁ ≅ S₂) (h : S₁.正合)
  结论: S₂.正合
  证明: by
  obtain ⟨⟨h, z⟩⟩ := h
  exact ⟨⟨HomologyData.ofIso e h, z⟩⟩

Depends on / 依赖: HomologyData, HomologyData.ofIso
-/
lemma exact_of_iso (e : S₁ ≅ S₂) (h : S₁.Exact) : S₂.Exact := by
  obtain ⟨⟨h, z⟩⟩ := h
  exact ⟨⟨HomologyData.ofIso e h, z⟩⟩

/--
lemma `exact_iff_of_iso` / 引理 `exact_iff_of_iso`

English:
lemma exact_iff_of_iso
  given: (e : S₁ ≅ S₂)
  statement: S₁.Exact ↔ S₂.Exact
  proof: ⟨exact_of_iso e, exact_of_iso e.symm⟩

中文:
引理 exact_iff_of_iso
  条件: (e : S₁ ≅ S₂)
  结论: S₁.正合 ↔ S₂.正合
  证明: ⟨exact_of_iso e, exact_of_iso e.symm⟩

Depends on / 依赖: e.symm, exact_of_iso
-/
lemma exact_iff_of_iso (e : S₁ ≅ S₂) : S₁.Exact ↔ S₂.Exact :=
  ⟨exact_of_iso e, exact_of_iso e.symm⟩

/--
lemma `exact_and_mono_f_iff_of_iso` / 引理 `exact_and_mono_f_iff_of_iso`

English:
lemma exact_and_mono_f_iff_of_iso
  given: (e : S₁ ≅ S₂)
  proof: by
  have : Mono S₁.f ↔ Mono S₂.f :=
    (MorphismProperty.monomorphisms C).arrow_mk_iso_iff
      (Arrow.isoMk (ShortComplex.π₁.mapIso e) (ShortComplex.π₂.mapIso e) e.hom.comm₁₂)
  rw [exact_iff_of_iso e]; rw [this]

中文:
引理 exact_and_mono_f_iff_of_iso
  条件: (e : S₁ ≅ S₂)
  证明: by
  have : Mono S₁.f ↔ Mono S₂.f :=
    (MorphismProperty.monomorphisms C).arrow_mk_iso_iff
      (Arrow.isoMk (ShortComplex.π₁.mapIso e) (ShortComplex.π₂.mapIso e) e.hom.comm₁₂)
  rw [exact_iff_of_iso e]; rw [this]

Depends on / 依赖: Arrow.isoMk, MorphismProperty, MorphismProperty.monomorphisms, ShortComplex, arrow_mk_iso_iff, e.hom.comm, exact_iff_of_iso, mapIso, monomorphisms
-/
lemma exact_and_mono_f_iff_of_iso (e : S₁ ≅ S₂) :
    S₁.Exact ∧ Mono S₁.f ↔ S₂.Exact ∧ Mono S₂.f := by
  have : Mono S₁.f ↔ Mono S₂.f :=
    (MorphismProperty.monomorphisms C).arrow_mk_iso_iff
      (Arrow.isoMk (ShortComplex.π₁.mapIso e) (ShortComplex.π₂.mapIso e) e.hom.comm₁₂)
  rw [exact_iff_of_iso e]; rw [this]

/--
lemma `exact_and_epi_g_iff_of_iso` / 引理 `exact_and_epi_g_iff_of_iso`

English:
lemma exact_and_epi_g_iff_of_iso
  given: (e : S₁ ≅ S₂)
  proof: by
  have : Epi S₁.g ↔ Epi S₂.g :=
    (MorphismProperty.epimorphisms C).arrow_mk_iso_iff
      (Arrow.isoMk (ShortComplex.π₂.mapIso e) (ShortComplex.π₃.mapIso e) e.hom.comm₂₃)
  rw [exact_iff_of_iso e]; rw [this]

中文:
引理 exact_and_epi_g_iff_of_iso
  条件: (e : S₁ ≅ S₂)
  证明: by
  have : Epi S₁.g ↔ Epi S₂.g :=
    (MorphismProperty.epimorphisms C).arrow_mk_iso_iff
      (Arrow.isoMk (ShortComplex.π₂.mapIso e) (ShortComplex.π₃.mapIso e) e.hom.comm₂₃)
  rw [exact_iff_of_iso e]; rw [this]

Depends on / 依赖: Arrow.isoMk, MorphismProperty, MorphismProperty.epimorphisms, ShortComplex, arrow_mk_iso_iff, e.hom.comm, epimorphisms, exact_iff_of_iso, mapIso
-/
lemma exact_and_epi_g_iff_of_iso (e : S₁ ≅ S₂) :
    S₁.Exact ∧ Epi S₁.g ↔ S₂.Exact ∧ Epi S₂.g := by
  have : Epi S₁.g ↔ Epi S₂.g :=
    (MorphismProperty.epimorphisms C).arrow_mk_iso_iff
      (Arrow.isoMk (ShortComplex.π₂.mapIso e) (ShortComplex.π₃.mapIso e) e.hom.comm₂₃)
  rw [exact_iff_of_iso e]; rw [this]

/--
lemma `exact_of_isZero_X₂` / 引理 `exact_of_isZero_X₂`

English:
lemma exact_of_isZero_X₂
  given: (h : IsZero S.X₂)
  statement: S.Exact
  proof: by
  rw [(HomologyData.ofZeros S (IsZero.eq_of_tgt h _ _) (IsZero.eq_of_src h _ _)).exact_iff]
  exact h

中文:
引理 exact_of_isZero_X₂
  条件: (h : 是零 S.X₂)
  结论: S.正合
  证明: by
  rw [(HomologyData.ofZeros S (IsZero.eq_of_tgt h _ _) (IsZero.eq_of_src h _ _)).exact_iff]
  exact h

Depends on / 依赖: HomologyData, HomologyData.ofZeros, IsZero, IsZero.eq_of_src, IsZero.eq_of_tgt, eq_of_src, eq_of_tgt, exact_iff, ofZeros
-/
lemma exact_of_isZero_X₂ (h : IsZero S.X₂) : S.Exact := by
  rw [(HomologyData.ofZeros S (IsZero.eq_of_tgt h _ _) (IsZero.eq_of_src h _ _)).exact_iff]
  exact h

/--
lemma `exact_iff_of_epi_of_isIso_of_mono` / 引理 `exact_iff_of_epi_of_isIso_of_mono`

English:
lemma exact_iff_of_epi_of_isIso_of_mono
  given: (φ : S₁ ⟶ S₂) [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃]
  proof: by
  constructor
  · rintro ⟨h₁, z₁⟩
    exact ⟨HomologyData.ofEpiOfIsIsoOfMono φ h₁, z₁⟩
  · rintro ⟨h₂, z₂⟩
    exact ⟨HomologyData.ofEpiOfIsIsoOfMono' φ h₂, z₂⟩

中文:
引理 exact_iff_of_epi_of_isIso_of_mono
  条件: (φ : S₁ ⟶ S₂) [满态射 φ.τ₁] [是同构 φ.τ₂] [单态射 φ.τ₃]
  证明: by
  constructor
  · rintro ⟨h₁, z₁⟩
    exact ⟨HomologyData.ofEpiOfIsIsoOfMono φ h₁, z₁⟩
  · rintro ⟨h₂, z₂⟩
    exact ⟨HomologyData.ofEpiOfIsIsoOfMono' φ h₂, z₂⟩

Depends on / 依赖: HomologyData, HomologyData.ofEpiOfIsIsoOfMono, ofEpiOfIsIsoOfMono
-/
lemma exact_iff_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    S₁.Exact ↔ S₂.Exact := by
  constructor
  · rintro ⟨h₁, z₁⟩
    exact ⟨HomologyData.ofEpiOfIsIsoOfMono φ h₁, z₁⟩
  · rintro ⟨h₂, z₂⟩
    exact ⟨HomologyData.ofEpiOfIsIsoOfMono' φ h₂, z₂⟩

variable {S}

/--
lemma `HomologyData.exact_iff_i_p_zero` / 引理 `HomologyData.exact_iff_i_p_zero`

English:
lemma HomologyData.exact_iff_i_p_zero
  given: (h : S.HomologyData)
  proof: by
  have := HasHomology.mk' h
  rw [h.left.exact_iff]; rw [← h.comm]
  constructor
  · intro z
    rw [IsZero.eq_of_src z h.iso.hom 0]; rw [zero_comp]; rw [comp_zero]
  · intro eq
    simp only [IsZero.iff_id_eq_zero, ← cancel_mono h.iso.hom, id_comp, ← cancel_mono h.right.ι,
      ← cancel_epi h.left.π, eq, zero_comp, comp_zero]

中文:
引理 同调数据.exact_iff_i_p_zero
  条件: (h : S.同调数据)
  证明: by
  have := HasHomology.mk' h
  rw [h.left.exact_iff]; rw [← h.comm]
  constructor
  · intro z
    rw [IsZero.eq_of_src z h.iso.hom 0]; rw [zero_comp]; rw [comp_zero]
  · intro eq
    simp only [IsZero.iff_id_eq_zero, ← cancel_mono h.iso.hom, id_comp, ← cancel_mono h.right.ι,
      ← cancel_epi h.left.π, eq, zero_comp, comp_zero]

Depends on / 依赖: HasHomology, HasHomology.mk, IsZero, IsZero.eq_of_src, IsZero.iff_id_eq_zero, cancel_epi, cancel_mono, comp_zero, eq_of_src, exact_iff, h.comm, h.iso.hom, h.left, h.left.exact_iff, h.right, id_comp, iff_id_eq_zero, zero_comp
-/
lemma HomologyData.exact_iff_i_p_zero (h : S.HomologyData) :
    S.Exact ↔ h.left.i ≫ h.right.p = 0 := by
  have := HasHomology.mk' h
  rw [h.left.exact_iff]; rw [← h.comm]
  constructor
  · intro z
    rw [IsZero.eq_of_src z h.iso.hom 0]; rw [zero_comp]; rw [comp_zero]
  · intro eq
    simp only [IsZero.iff_id_eq_zero, ← cancel_mono h.iso.hom, id_comp, ← cancel_mono h.right.ι,
      ← cancel_epi h.left.π, eq, zero_comp, comp_zero]

variable (S)

/--
lemma `exact_iff_i_p_zero` / 引理 `exact_iff_i_p_zero`

English:
lemma exact_iff_i_p_zero
  statement: [S.HasHomology] (h₁ : S.LeftHomologyData)
  proof: (HomologyData.ofIsIsoLeftRightHomologyComparison' h₁ h₂).exact_iff_i_p_zero

中文:
引理 exact_iff_i_p_zero
  结论: [S.有同调] (h₁ : S.LeftHomologyData)
  证明: (HomologyData.ofIsIsoLeftRightHomologyComparison' h₁ h₂).exact_iff_i_p_zero

Depends on / 依赖: HomologyData, HomologyData.ofIsIsoLeftRightHomologyComparison, exact_iff_i_p_zero, ofIsIsoLeftRightHomologyComparison
-/
lemma exact_iff_i_p_zero [S.HasHomology] (h₁ : S.LeftHomologyData)
    (h₂ : S.RightHomologyData) :
    S.Exact ↔ h₁.i ≫ h₂.p = 0 :=
  (HomologyData.ofIsIsoLeftRightHomologyComparison' h₁ h₂).exact_iff_i_p_zero

/--
lemma `exact_iff_iCycles_pOpcycles_zero` / 引理 `exact_iff_iCycles_pOpcycles_zero`

English:
lemma exact_iff_iCycles_pOpcycles_zero
  given: [S.HasHomology]
  proof: S.exact_iff_i_p_zero _ _

中文:
引理 exact_iff_iCycles_pOpcycles_zero
  条件: [S.有同调]
  证明: S.exact_iff_i_p_zero _ _

Depends on / 依赖: S.exact_iff_i_p_zero, exact_iff_i_p_zero
-/
lemma exact_iff_iCycles_pOpcycles_zero [S.HasHomology] :
    S.Exact ↔ S.iCycles ≫ S.pOpcycles = 0 :=
  S.exact_iff_i_p_zero _ _

/--
lemma `exact_iff_kernel_ι_comp_cokernel_π_zero` / 引理 `exact_iff_kernel_ι_comp_cokernel_π_zero`

English:
lemma exact_iff_kernel_ι_comp_cokernel_π_zero
  statement: [S.HasHomology]
  proof: by
  have := HasLeftHomology.hasCokernel S
  have := HasRightHomology.hasKernel S
  exact S.exact_iff_i_p_zero (LeftHomologyData.ofHasKernelOfHasCokernel S)
    (RightHomologyData.ofHasCokernelOfHasKernel S)

中文:
引理 exact_iff_kernel_ι_comp_cokernel_π_zero
  结论: [S.有同调]
  证明: by
  have := HasLeftHomology.hasCokernel S
  have := HasRightHomology.hasKernel S
  exact S.exact_iff_i_p_zero (LeftHomologyData.ofHasKernelOfHasCokernel S)
    (RightHomologyData.ofHasCokernelOfHasKernel S)

Depends on / 依赖: HasLeftHomology, HasLeftHomology.hasCokernel, HasRightHomology, HasRightHomology.hasKernel, LeftHomologyData, LeftHomologyData.ofHasKernelOfHasCokernel, RightHomologyData, RightHomologyData.ofHasCokernelOfHasKernel, S.exact_iff_i_p_zero, exact_iff_i_p_zero, hasCokernel, hasKernel, ofHasCokernelOfHasKernel, ofHasKernelOfHasCokernel
-/
lemma exact_iff_kernel_ι_comp_cokernel_π_zero [S.HasHomology]
    [HasKernel S.g] [HasCokernel S.f] :
    S.Exact ↔ kernel.ι S.g ≫ cokernel.π S.f = 0 := by
  have := HasLeftHomology.hasCokernel S
  have := HasRightHomology.hasKernel S
  exact S.exact_iff_i_p_zero (LeftHomologyData.ofHasKernelOfHasCokernel S)
    (RightHomologyData.ofHasCokernelOfHasKernel S)

variable {S}

/--
lemma `Exact.op` / 引理 `Exact.op`

English:
lemma Exact.op
  given: (h : S.Exact)
  statement: S.op.Exact
  proof: by
  obtain ⟨h, z⟩ := h
  exact ⟨⟨h.op, (IsZero.of_iso z h.iso.symm).op⟩⟩

中文:
引理 正合.op
  条件: (h : S.正合)
  结论: S.op.正合
  证明: by
  obtain ⟨h, z⟩ := h
  exact ⟨⟨h.op, (IsZero.of_iso z h.iso.symm).op⟩⟩

Depends on / 依赖: IsZero, IsZero.of_iso, h.iso.symm, h.op, of_iso
-/
lemma Exact.op (h : S.Exact) : S.op.Exact := by
  obtain ⟨h, z⟩ := h
  exact ⟨⟨h.op, (IsZero.of_iso z h.iso.symm).op⟩⟩

/--
lemma `Exact.unop` / 引理 `Exact.unop`

English:
lemma Exact.unop
  given: {S : ShortComplex Cᵒᵖ} (h : S.Exact)
  statement: S.unop.Exact
  proof: by
  obtain ⟨h, z⟩ := h
  exact ⟨⟨h.unop, (IsZero.of_iso z h.iso.symm).unop⟩⟩

中文:
引理 正合.unop
  条件: {S : 短复形 Cᵒᵖ} (h : S.正合)
  结论: S.unop.正合
  证明: by
  obtain ⟨h, z⟩ := h
  exact ⟨⟨h.unop, (IsZero.of_iso z h.iso.symm).unop⟩⟩

Depends on / 依赖: IsZero, IsZero.of_iso, h.iso.symm, h.unop, of_iso
-/
lemma Exact.unop {S : ShortComplex Cᵒᵖ} (h : S.Exact) : S.unop.Exact := by
  obtain ⟨h, z⟩ := h
  exact ⟨⟨h.unop, (IsZero.of_iso z h.iso.symm).unop⟩⟩

variable (S)

@[simp]
/--
lemma `exact_op_iff` / 引理 `exact_op_iff`

English:
lemma exact_op_iff
  statement: S.op.Exact ↔ S.Exact
  proof: ⟨Exact.unop, Exact.op⟩

@[simp]

中文:
引理 exact_op_iff
  结论: S.op.正合 ↔ S.正合
  证明: ⟨Exact.unop, Exact.op⟩

@[simp]

Depends on / 依赖: Exact.op, Exact.unop
-/
lemma exact_op_iff : S.op.Exact ↔ S.Exact :=
  ⟨Exact.unop, Exact.op⟩

@[simp]
/--
lemma `exact_unop_iff` / 引理 `exact_unop_iff`

English:
lemma exact_unop_iff
  given: (S : ShortComplex Cᵒᵖ)
  statement: S.unop.Exact ↔ S.Exact
  proof: S.unop.exact_op_iff.symm

中文:
引理 exact_unop_iff
  条件: (S : 短复形 Cᵒᵖ)
  结论: S.unop.正合 ↔ S.正合
  证明: S.unop.exact_op_iff.symm

Depends on / 依赖: S.unop.exact_op_iff.symm, exact_op_iff
-/
lemma exact_unop_iff (S : ShortComplex Cᵒᵖ) : S.unop.Exact ↔ S.Exact :=
  S.unop.exact_op_iff.symm

variable {S}

/--
lemma `LeftHomologyData.exact_map_iff` / 引理 `LeftHomologyData.exact_map_iff`

English:
lemma LeftHomologyData.exact_map_iff
  statement: (h : S.LeftHomologyData) (F : C ⥤ D)
  proof: (h.map F).exact_iff

中文:
引理 LeftHomologyData.exact_map_iff
  结论: (h : S.LeftHomologyData) (F : C ⥤ D)
  证明: (h.map F).exact_iff

Depends on / 依赖: exact_iff, h.map
-/
lemma LeftHomologyData.exact_map_iff (h : S.LeftHomologyData) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [h.IsPreservedBy F] [(S.map F).HasHomology] :
    (S.map F).Exact ↔ IsZero (F.obj h.H) :=
  (h.map F).exact_iff

/--
lemma `RightHomologyData.exact_map_iff` / 引理 `RightHomologyData.exact_map_iff`

English:
lemma RightHomologyData.exact_map_iff
  statement: (h : S.RightHomologyData) (F : C ⥤ D)
  proof: (h.map F).exact_iff

中文:
引理 RightHomologyData.exact_map_iff
  结论: (h : S.RightHomologyData) (F : C ⥤ D)
  证明: (h.map F).exact_iff

Depends on / 依赖: exact_iff, h.map
-/
lemma RightHomologyData.exact_map_iff (h : S.RightHomologyData) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [h.IsPreservedBy F] [(S.map F).HasHomology] :
    (S.map F).Exact ↔ IsZero (F.obj h.H) :=
  (h.map F).exact_iff

/--
lemma `Exact.map_of_preservesLeftHomologyOf` / 引理 `Exact.map_of_preservesLeftHomologyOf`

English:
lemma Exact.map_of_preservesLeftHomologyOf
  statement: (h : S.Exact) (F : C ⥤ D)
  proof: by
  have := h.hasHomology
  rw [S.leftHomologyData.exact_iff]; rw [IsZero.iff_id_eq_zero] at h
  rw [S.leftHomologyData.exact_map_iff F]; rw [IsZero.iff_id_eq_zero]; rw [← F.map_id]; rw [h]; rw [F.map_zero]

中文:
引理 正合.map_of_preservesLeftHomologyOf
  结论: (h : S.正合) (F : C ⥤ D)
  证明: by
  have := h.hasHomology
  rw [S.leftHomologyData.exact_iff]; rw [IsZero.iff_id_eq_zero] at h
  rw [S.leftHomologyData.exact_map_iff F]; rw [IsZero.iff_id_eq_zero]; rw [← F.map_id]; rw [h]; rw [F.map_zero]

Depends on / 依赖: F.map_id, F.map_zero, IsZero, IsZero.iff_id_eq_zero, S.leftHomologyData.exact_iff, S.leftHomologyData.exact_map_iff, exact_iff, exact_map_iff, h.hasHomology, hasHomology, iff_id_eq_zero, leftHomologyData, map_id, map_zero
-/
lemma Exact.map_of_preservesLeftHomologyOf (h : S.Exact) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [F.PreservesLeftHomologyOf S]
    [(S.map F).HasHomology] : (S.map F).Exact := by
  have := h.hasHomology
  rw [S.leftHomologyData.exact_iff]; rw [IsZero.iff_id_eq_zero] at h
  rw [S.leftHomologyData.exact_map_iff F]; rw [IsZero.iff_id_eq_zero]; rw [← F.map_id]; rw [h]; rw [F.map_zero]

/--
lemma `Exact.map_of_preservesRightHomologyOf` / 引理 `Exact.map_of_preservesRightHomologyOf`

English:
lemma Exact.map_of_preservesRightHomologyOf
  statement: (h : S.Exact) (F : C ⥤ D)
  proof: by
  have : S.HasHomology := h.hasHomology
  rw [S.rightHomologyData.exact_iff]; rw [IsZero.iff_id_eq_zero] at h
  rw [S.rightHomologyData.exact_map_iff F]; rw [IsZero.iff_id_eq_zero]; rw [← F.map_id]; rw [h]; rw [F.map_zero]

中文:
引理 正合.map_of_preservesRightHomologyOf
  结论: (h : S.正合) (F : C ⥤ D)
  证明: by
  have : S.HasHomology := h.hasHomology
  rw [S.rightHomologyData.exact_iff]; rw [IsZero.iff_id_eq_zero] at h
  rw [S.rightHomologyData.exact_map_iff F]; rw [IsZero.iff_id_eq_zero]; rw [← F.map_id]; rw [h]; rw [F.map_zero]

Depends on / 依赖: F.map_id, F.map_zero, HasHomology, IsZero, IsZero.iff_id_eq_zero, S.HasHomology, S.rightHomologyData.exact_iff, S.rightHomologyData.exact_map_iff, exact_iff, exact_map_iff, h.hasHomology, hasHomology, iff_id_eq_zero, map_id, map_zero, rightHomologyData
-/
lemma Exact.map_of_preservesRightHomologyOf (h : S.Exact) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [F.PreservesRightHomologyOf S]
    [(S.map F).HasHomology] : (S.map F).Exact := by
  have : S.HasHomology := h.hasHomology
  rw [S.rightHomologyData.exact_iff]; rw [IsZero.iff_id_eq_zero] at h
  rw [S.rightHomologyData.exact_map_iff F]; rw [IsZero.iff_id_eq_zero]; rw [← F.map_id]; rw [h]; rw [F.map_zero]

/--
lemma `Exact.map` / 引理 `Exact.map`

English:
lemma Exact.map
  statement: (h : S.Exact) (F : C ⥤ D)
  proof: by
  have := h.hasHomology
  exact h.map_of_preservesLeftHomologyOf F

中文:
引理 正合.map
  结论: (h : S.正合) (F : C ⥤ D)
  证明: by
  have := h.hasHomology
  exact h.map_of_preservesLeftHomologyOf F

Depends on / 依赖: h.hasHomology, h.map_of_preservesLeftHomologyOf, hasHomology, map_of_preservesLeftHomologyOf
-/
lemma Exact.map (h : S.Exact) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [F.PreservesLeftHomologyOf S]
    [F.PreservesRightHomologyOf S] : (S.map F).Exact := by
  have := h.hasHomology
  exact h.map_of_preservesLeftHomologyOf F

variable (S)

/--
lemma `exact_map_iff_of_faithful` / 引理 `exact_map_iff_of_faithful`

English:
lemma exact_map_iff_of_faithful
  statement: [S.HasHomology]
  proof: by
  constructor
  · intro h
    rw [S.leftHomologyData.exact_iff]; rw [IsZero.iff_id_eq_zero]
    rw [(S.leftHomologyData.map F).exact_iff]; rw [IsZero.iff_id_eq_zero]; rw [LeftHomologyData.map_H] at h
    apply F.map_injective
    rw [F.map_id]; rw [F.map_zero]; rw [h]
  · intro h
    exact h.map F

中文:
引理 exact_map_iff_of_faithful
  结论: [S.有同调]
  证明: by
  constructor
  · intro h
    rw [S.leftHomologyData.exact_iff]; rw [IsZero.iff_id_eq_zero]
    rw [(S.leftHomologyData.map F).exact_iff]; rw [IsZero.iff_id_eq_zero]; rw [LeftHomologyData.map_H] at h
    apply F.map_injective
    rw [F.map_id]; rw [F.map_zero]; rw [h]
  · intro h
    exact h.map F

Depends on / 依赖: F.map_id, F.map_injective, F.map_zero, IsZero, IsZero.iff_id_eq_zero, LeftHomologyData, LeftHomologyData.map_H, S.leftHomologyData.exact_iff, S.leftHomologyData.map, exact_iff, h.map, iff_id_eq_zero, leftHomologyData, map_H, map_id, map_injective, map_zero
-/
lemma exact_map_iff_of_faithful [S.HasHomology]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.PreservesLeftHomologyOf S]
    [F.PreservesRightHomologyOf S] [F.Faithful] :
    (S.map F).Exact ↔ S.Exact := by
  constructor
  · intro h
    rw [S.leftHomologyData.exact_iff]; rw [IsZero.iff_id_eq_zero]
    rw [(S.leftHomologyData.map F).exact_iff]; rw [IsZero.iff_id_eq_zero]; rw [LeftHomologyData.map_H] at h
    apply F.map_injective
    rw [F.map_id]; rw [F.map_zero]; rw [h]
  · intro h
    exact h.map F

variable {S}

@[reassoc]
/--
lemma `Exact.comp_eq_zero` / 引理 `Exact.comp_eq_zero`

English:
lemma Exact.comp_eq_zero
  statement: (h : S.Exact) {X Y : C} {a : X ⟶ S.X₂} (ha : a ≫ S.g = 0)
  proof: by
  have := h.hasHomology
  have eq := h
  rw [exact_iff_iCycles_pOpcycles_zero] at eq
  rw [← S.liftCycles_i a ha]; rw [← S.p_descOpcycles b hb]; rw [assoc]; rw [reassoc_of% eq]; rw [zero_comp]; rw [comp_zero]

中文:
引理 正合.comp_eq_zero
  结论: (h : S.正合) {X Y : C} {a : X ⟶ S.X₂} (ha : a ≫ S.g = 0)
  证明: by
  have := h.hasHomology
  have eq := h
  rw [exact_iff_iCycles_pOpcycles_zero] at eq
  rw [← S.liftCycles_i a ha]; rw [← S.p_descOpcycles b hb]; rw [assoc]; rw [reassoc_of% eq]; rw [zero_comp]; rw [comp_zero]

Depends on / 依赖: S.liftCycles_i, S.p_descOpcycles, comp_zero, exact_iff_iCycles_pOpcycles_zero, h.hasHomology, hasHomology, liftCycles_i, p_descOpcycles, reassoc_of, zero_comp
-/
lemma Exact.comp_eq_zero (h : S.Exact) {X Y : C} {a : X ⟶ S.X₂} (ha : a ≫ S.g = 0)
    {b : S.X₂ ⟶ Y} (hb : S.f ≫ b = 0) : a ≫ b = 0 := by
  have := h.hasHomology
  have eq := h
  rw [exact_iff_iCycles_pOpcycles_zero] at eq
  rw [← S.liftCycles_i a ha]; rw [← S.p_descOpcycles b hb]; rw [assoc]; rw [reassoc_of% eq]; rw [zero_comp]; rw [comp_zero]

/--
lemma `Exact.isZero_of_both_zeros` / 引理 `Exact.isZero_of_both_zeros`

English:
lemma Exact.isZero_of_both_zeros
  given: (ex : S.Exact) (hf : S.f = 0) (hg : S.g = 0)
  proof: (ShortComplex.HomologyData.ofZeros S hf hg).exact_iff.1 ex

中文:
引理 正合.isZero_of_both_zeros
  条件: (ex : S.正合) (hf : S.f = 0) (hg : S.g = 0)
  证明: (ShortComplex.HomologyData.ofZeros S hf hg).exact_iff.1 ex

Depends on / 依赖: HomologyData, ShortComplex, ShortComplex.HomologyData.ofZeros, exact_iff, ofZeros
-/
lemma Exact.isZero_of_both_zeros (ex : S.Exact) (hf : S.f = 0) (hg : S.g = 0) :
    IsZero S.X₂ :=
  (ShortComplex.HomologyData.ofZeros S hf hg).exact_iff.1 ex

/--
lemma `Exact.isZero_of_both_isZero` / 引理 `Exact.isZero_of_both_isZero`

English:
lemma Exact.isZero_of_both_isZero
  given: (ex : S.Exact) (hX₁ : IsZero S.X₁) (hX₃ : IsZero S.X₃)
  proof: ex.isZero_of_both_zeros (hX₁.eq_zero_of_src _) (hX₃.eq_zero_of_tgt _)

中文:
引理 正合.isZero_of_both_isZero
  条件: (ex : S.正合) (hX₁ : 是零 S.X₁) (hX₃ : 是零 S.X₃)
  证明: ex.isZero_of_both_zeros (hX₁.eq_zero_of_src _) (hX₃.eq_zero_of_tgt _)

Depends on / 依赖: eq_zero_of_src, eq_zero_of_tgt, ex.isZero_of_both_zeros, isZero_of_both_zeros
-/
lemma Exact.isZero_of_both_isZero (ex : S.Exact) (hX₁ : IsZero S.X₁) (hX₃ : IsZero S.X₃) :
    IsZero S.X₂ :=
  ex.isZero_of_both_zeros (hX₁.eq_zero_of_src _) (hX₃.eq_zero_of_tgt _)

end

section Preadditive

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

/--
lemma `exact_iff_mono` / 引理 `exact_iff_mono`

English:
lemma exact_iff_mono
  given: [HasZeroObject C] (hf : S.f = 0)
  proof: by
  constructor
  · intro h
    have := h.hasHomology
    simp only [exact_iff_isZero_homology] at h
    have := S.isIso_pOpcycles hf
    have := mono_of_isZero_kernel' _ S.homologyIsKernel h
    rw [← S.p_fromOpcycles]
    apply mono_comp
  · intro
    rw [(HomologyData.ofIsLimitKernelFork S hf _
      (KernelFork.IsLimit.ofMonoOfIsZero (KernelFork.ofι (0 : 0 ⟶ S.X₂) zero_comp)
        inferInstance (isZero_zero C))).exact_iff]
    exact isZero_zero C

中文:
引理 exact_iff_mono
  条件: [有ZeroObject C] (hf : S.f = 0)
  证明: by
  constructor
  · intro h
    have := h.hasHomology
    simp only [exact_iff_isZero_homology] at h
    have := S.isIso_pOpcycles hf
    have := mono_of_isZero_kernel' _ S.homologyIsKernel h
    rw [← S.p_fromOpcycles]
    apply mono_comp
  · intro
    rw [(HomologyData.ofIsLimitKernelFork S hf _
      (KernelFork.IsLimit.ofMonoOfIsZero (KernelFork.ofι (0 : 0 ⟶ S.X₂) zero_comp)
        inferInstance (isZero_zero C))).exact_iff]
    exact isZero_zero C

Depends on / 依赖: HomologyData, HomologyData.ofIsLimitKernelFork, IsLimit, KernelFork, KernelFork.IsLimit.ofMonoOfIsZero, KernelFork.of, S.homologyIsKernel, S.isIso_pOpcycles, S.p_fromOpcycles, exact_iff, exact_iff_isZero_homology, h.hasHomology, hasHomology, homologyIsKernel, isIso_pOpcycles, isZero_zero, mono_comp, mono_of_isZero_kernel, ofIsLimitKernelFork, ofMonoOfIsZero
-/
lemma exact_iff_mono [HasZeroObject C] (hf : S.f = 0) :
    S.Exact ↔ Mono S.g := by
  constructor
  · intro h
    have := h.hasHomology
    simp only [exact_iff_isZero_homology] at h
    have := S.isIso_pOpcycles hf
    have := mono_of_isZero_kernel' _ S.homologyIsKernel h
    rw [← S.p_fromOpcycles]
    apply mono_comp
  · intro
    rw [(HomologyData.ofIsLimitKernelFork S hf _
      (KernelFork.IsLimit.ofMonoOfIsZero (KernelFork.ofι (0 : 0 ⟶ S.X₂) zero_comp)
        inferInstance (isZero_zero C))).exact_iff]
    exact isZero_zero C

/--
lemma `exact_iff_epi` / 引理 `exact_iff_epi`

English:
lemma exact_iff_epi
  given: [HasZeroObject C] (hg : S.g = 0)
  proof: by
  constructor
  · intro h
    have := h.hasHomology
    simp only [exact_iff_isZero_homology] at h
    have := S.isIso_iCycles hg
    have : Epi S.toCycles := epi_of_isZero_cokernel' _ S.homologyIsCokernel h
    rw [← S.toCycles_i]
    apply epi_comp
  · intro
    rw [(HomologyData.ofIsColimitCokernelCofork S hg _
      (CokernelCofork.IsColimit.ofEpiOfIsZero (CokernelCofork.ofπ (0 : S.X₂ ⟶ 0) comp_zero)
        inferInstance (isZero_zero C))).exact_iff]
    exact isZero_zero C

中文:
引理 exact_iff_epi
  条件: [有ZeroObject C] (hg : S.g = 0)
  证明: by
  constructor
  · intro h
    have := h.hasHomology
    simp only [exact_iff_isZero_homology] at h
    have := S.isIso_iCycles hg
    have : Epi S.toCycles := epi_of_isZero_cokernel' _ S.homologyIsCokernel h
    rw [← S.toCycles_i]
    apply epi_comp
  · intro
    rw [(HomologyData.ofIsColimitCokernelCofork S hg _
      (CokernelCofork.IsColimit.ofEpiOfIsZero (CokernelCofork.ofπ (0 : S.X₂ ⟶ 0) comp_zero)
        inferInstance (isZero_zero C))).exact_iff]
    exact isZero_zero C

Depends on / 依赖: CokernelCofork, CokernelCofork.IsColimit.ofEpiOfIsZero, CokernelCofork.of, HomologyData, HomologyData.ofIsColimitCokernelCofork, IsColimit, S.homologyIsCokernel, S.isIso_iCycles, S.toCycles, S.toCycles_i, comp_zero, epi_comp, epi_of_isZero_cokernel, exact_iff, exact_iff_isZero_homology, h.hasHomology, hasHomology, homologyIsCokernel, isIso_iCycles, isZero_zero
-/
lemma exact_iff_epi [HasZeroObject C] (hg : S.g = 0) :
    S.Exact ↔ Epi S.f := by
  constructor
  · intro h
    have := h.hasHomology
    simp only [exact_iff_isZero_homology] at h
    have := S.isIso_iCycles hg
    have : Epi S.toCycles := epi_of_isZero_cokernel' _ S.homologyIsCokernel h
    rw [← S.toCycles_i]
    apply epi_comp
  · intro
    rw [(HomologyData.ofIsColimitCokernelCofork S hg _
      (CokernelCofork.IsColimit.ofEpiOfIsZero (CokernelCofork.ofπ (0 : S.X₂ ⟶ 0) comp_zero)
        inferInstance (isZero_zero C))).exact_iff]
    exact isZero_zero C

variable {S}

set_option backward.defeqAttrib.useBackward true in
/--
lemma `Exact.epi_f'` / 引理 `Exact.epi_f'`

English:
lemma Exact.epi_f'
  given: (hS : S.Exact) (h : LeftHomologyData S)
  statement: Epi h.f'
  proof: epi_of_isZero_cokernel' _ h.hπ (by
    have := hS.hasHomology
    dsimp
    simpa only [← h.exact_iff] using hS)

中文:
引理 正合.epi_f'
  条件: (hS : S.正合) (h : LeftHomologyData S)
  结论: 满态射 h.f'
  证明: epi_of_isZero_cokernel' _ h.hπ (by
    have := hS.hasHomology
    dsimp
    simpa only [← h.exact_iff] using hS)

Depends on / 依赖: epi_of_isZero_cokernel, exact_iff, h.exact_iff, hS.hasHomology, hasHomology
-/
lemma Exact.epi_f' (hS : S.Exact) (h : LeftHomologyData S) : Epi h.f' :=
  epi_of_isZero_cokernel' _ h.hπ (by
    have := hS.hasHomology
    dsimp
    simpa only [← h.exact_iff] using hS)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `Exact.mono_g'` / 引理 `Exact.mono_g'`

English:
lemma Exact.mono_g'
  given: (hS : S.Exact) (h : RightHomologyData S)
  statement: Mono h.g'
  proof: mono_of_isZero_kernel' _ h.hι (by
    have := hS.hasHomology
    dsimp
    simpa only [← h.exact_iff] using hS)

中文:
引理 正合.mono_g'
  条件: (hS : S.正合) (h : RightHomologyData S)
  结论: 单态射 h.g'
  证明: mono_of_isZero_kernel' _ h.hι (by
    have := hS.hasHomology
    dsimp
    simpa only [← h.exact_iff] using hS)

Depends on / 依赖: exact_iff, h.exact_iff, hS.hasHomology, hasHomology, mono_of_isZero_kernel
-/
lemma Exact.mono_g' (hS : S.Exact) (h : RightHomologyData S) : Mono h.g' :=
  mono_of_isZero_kernel' _ h.hι (by
    have := hS.hasHomology
    dsimp
    simpa only [← h.exact_iff] using hS)

/--
lemma `Exact.epi_toCycles` / 引理 `Exact.epi_toCycles`

English:
lemma Exact.epi_toCycles
  given: (hS : S.Exact) [S.HasLeftHomology]
  statement: Epi S.toCycles
  proof: hS.epi_f' _

中文:
引理 正合.epi_toCycles
  条件: (hS : S.正合) [S.有LeftHomology]
  结论: 满态射 S.toCycles
  证明: hS.epi_f' _

Depends on / 依赖: epi_f, hS.epi_f
-/
lemma Exact.epi_toCycles (hS : S.Exact) [S.HasLeftHomology] : Epi S.toCycles :=
  hS.epi_f' _

/--
lemma `Exact.mono_fromOpcycles` / 引理 `Exact.mono_fromOpcycles`

English:
lemma Exact.mono_fromOpcycles
  given: (hS : S.Exact) [S.HasRightHomology]
  statement: Mono S.fromOpcycles
  proof: hS.mono_g' _

中文:
引理 正合.mono_fromOpcycles
  条件: (hS : S.正合) [S.有RightHomology]
  结论: 单态射 S.fromOpcycles
  证明: hS.mono_g' _

Depends on / 依赖: hS.mono_g, mono_g
-/
lemma Exact.mono_fromOpcycles (hS : S.Exact) [S.HasRightHomology] : Mono S.fromOpcycles :=
  hS.mono_g' _

/--
lemma `LeftHomologyData.exact_iff_epi_f'` / 引理 `LeftHomologyData.exact_iff_epi_f'`

English:
lemma LeftHomologyData.exact_iff_epi_f'
  given: [S.HasHomology] (h : LeftHomologyData S)
  proof: by
  constructor
  · intro hS
    exact hS.epi_f' h
  · intro
    simp only [h.exact_iff, IsZero.iff_id_eq_zero, ← cancel_epi h.π, ← cancel_epi h.f',
      comp_id, h.f'_π, comp_zero]

中文:
引理 LeftHomologyData.exact_iff_epi_f'
  条件: [S.有同调] (h : LeftHomologyData S)
  证明: by
  constructor
  · intro hS
    exact hS.epi_f' h
  · intro
    simp only [h.exact_iff, IsZero.iff_id_eq_zero, ← cancel_epi h.π, ← cancel_epi h.f',
      comp_id, h.f'_π, comp_zero]

Depends on / 依赖: IsZero, IsZero.iff_id_eq_zero, cancel_epi, comp_id, comp_zero, epi_f, exact_iff, h.exact_iff, hS.epi_f, iff_id_eq_zero
-/
lemma LeftHomologyData.exact_iff_epi_f' [S.HasHomology] (h : LeftHomologyData S) :
    S.Exact ↔ Epi h.f' := by
  constructor
  · intro hS
    exact hS.epi_f' h
  · intro
    simp only [h.exact_iff, IsZero.iff_id_eq_zero, ← cancel_epi h.π, ← cancel_epi h.f',
      comp_id, h.f'_π, comp_zero]

/--
lemma `RightHomologyData.exact_iff_mono_g'` / 引理 `RightHomologyData.exact_iff_mono_g'`

English:
lemma RightHomologyData.exact_iff_mono_g'
  given: [S.HasHomology] (h : RightHomologyData S)
  proof: by
  constructor
  · intro hS
    exact hS.mono_g' h
  · intro
    simp only [h.exact_iff, IsZero.iff_id_eq_zero, ← cancel_mono h.ι, ← cancel_mono h.g',
      id_comp, h.ι_g', zero_comp]

中文:
引理 RightHomologyData.exact_iff_mono_g'
  条件: [S.有同调] (h : RightHomologyData S)
  证明: by
  constructor
  · intro hS
    exact hS.mono_g' h
  · intro
    simp only [h.exact_iff, IsZero.iff_id_eq_zero, ← cancel_mono h.ι, ← cancel_mono h.g',
      id_comp, h.ι_g', zero_comp]

Depends on / 依赖: IsZero, IsZero.iff_id_eq_zero, cancel_mono, exact_iff, h.exact_iff, hS.mono_g, id_comp, iff_id_eq_zero, mono_g, zero_comp
-/
lemma RightHomologyData.exact_iff_mono_g' [S.HasHomology] (h : RightHomologyData S) :
    S.Exact ↔ Mono h.g' := by
  constructor
  · intro hS
    exact hS.mono_g' h
  · intro
    simp only [h.exact_iff, IsZero.iff_id_eq_zero, ← cancel_mono h.ι, ← cancel_mono h.g',
      id_comp, h.ι_g', zero_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Given an exact short complex `S` and a limit kernel fork `kf` for `S.g`, this is the
left homology data for `S` with `K := kf.pt` and `H := 0`. -/
@[simps]
/--
Definition of `Exact.leftHomologyDataOfIsLimitKernelFork` / `Exact.leftHomologyDataOfIsLimitKernelFork` 的定义

English:
definition Exact.leftHomologyDataOfIsLimitKernelFork
  body: kf.pt
  H := 0
  i := kf.ι
  π := 0
  wi := kf.condition
  hi := IsLimit.ofIsoLimit hkf (Fork.ext (Iso.refl _) (by simp))
  wπ := comp_zero
  hπ := CokernelCofork.IsColimit.ofEpiOfIsZero _ (by
    have := hS.hasHomology
    refine ((MorphismProperty.epimorphisms C).arrow_mk_iso_iff ?_).1
      hS.epi_toCycles
    refine Arrow.isoMk (Iso.refl _)
      (IsLimit.conePointUniqueUpToIso S.cyclesIsKernel hkf) ?_
    apply Fork.IsLimit.hom_ext hkf
    simp [IsLimit.conePointUniqueUpToIso]) (isZero_zero C)

中文:
定义 正合.leftHomologyDataOfIsLimitKernelFork
  定义体: kf.pt
  H := 0
  i := kf.ι
  π := 0
  wi := kf.condition
  hi := IsLimit.ofIsoLimit hkf (Fork.ext (Iso.refl _) (by simp))
  wπ := comp_zero
  hπ := CokernelCofork.IsColimit.ofEpiOfIsZero _ (by
    have := hS.hasHomology
    refine ((MorphismProperty.epimorphisms C).arrow_mk_iso_iff ?_).1
      hS.epi_toCycles
    refine Arrow.isoMk (Iso.refl _)
      (IsLimit.conePointUniqueUpToIso S.cyclesIsKernel hkf) ?_
    apply Fork.IsLimit.hom_ext hkf
    simp [IsLimit.conePointUniqueUpToIso]) (isZero_zero C)

Depends on / 依赖: kf.pt
-/
noncomputable def Exact.leftHomologyDataOfIsLimitKernelFork
    (hS : S.Exact) [HasZeroObject C] (kf : KernelFork S.g) (hkf : IsLimit kf) :
    S.LeftHomologyData where
  K := kf.pt
  H := 0
  i := kf.ι
  π := 0
  wi := kf.condition
  hi := IsLimit.ofIsoLimit hkf (Fork.ext (Iso.refl _) (by simp))
  wπ := comp_zero
  hπ := CokernelCofork.IsColimit.ofEpiOfIsZero _ (by
    have := hS.hasHomology
    refine ((MorphismProperty.epimorphisms C).arrow_mk_iso_iff ?_).1
      hS.epi_toCycles
    refine Arrow.isoMk (Iso.refl _)
      (IsLimit.conePointUniqueUpToIso S.cyclesIsKernel hkf) ?_
    apply Fork.IsLimit.hom_ext hkf
    simp [IsLimit.conePointUniqueUpToIso]) (isZero_zero C)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given an exact short complex `S` and a colimit cokernel cofork `cc` for `S.f`, this is the
right homology data for `S` with `Q := cc.pt` and `H := 0`. -/
@[simps]
/--
Definition of `Exact.rightHomologyDataOfIsColimitCokernelCofork` / `Exact.rightHomologyDataOfIsColimitCokernelCofork` 的定义

English:
definition Exact.rightHomologyDataOfIsColimitCokernelCofork
  body: cc.pt
  H := 0
  p := cc.π
  ι := 0
  wp := cc.condition
  hp := IsColimit.ofIsoColimit hcc (Cofork.ext (Iso.refl _) (by simp))
  wι := zero_comp
  hι := KernelFork.IsLimit.ofMonoOfIsZero _ (by
    have := hS.hasHomology
    refine ((MorphismProperty.monomorphisms C).arrow_mk_iso_iff ?_).2
      hS.mono_fromOpcycles
    refine Arrow.isoMk (IsColimit.coconePointUniqueUpToIso hcc S.opcyclesIsCokernel)
      (Iso.refl _) ?_
    apply Cofork.IsColimit.hom_ext hcc
    simp [IsColimit.coconePointUniqueUpToIso]) (isZero_zero C)

中文:
定义 正合.rightHomologyDataOfIsColimitCokernelCofork
  定义体: cc.pt
  H := 0
  p := cc.π
  ι := 0
  wp := cc.condition
  hp := IsColimit.ofIsoColimit hcc (Cofork.ext (Iso.refl _) (by simp))
  wι := zero_comp
  hι := KernelFork.IsLimit.ofMonoOfIsZero _ (by
    have := hS.hasHomology
    refine ((MorphismProperty.monomorphisms C).arrow_mk_iso_iff ?_).2
      hS.mono_fromOpcycles
    refine Arrow.isoMk (IsColimit.coconePointUniqueUpToIso hcc S.opcyclesIsCokernel)
      (Iso.refl _) ?_
    apply Cofork.IsColimit.hom_ext hcc
    simp [IsColimit.coconePointUniqueUpToIso]) (isZero_zero C)

Depends on / 依赖: cc.pt
-/
noncomputable def Exact.rightHomologyDataOfIsColimitCokernelCofork
    (hS : S.Exact) [HasZeroObject C] (cc : CokernelCofork S.f) (hcc : IsColimit cc) :
    S.RightHomologyData where
  Q := cc.pt
  H := 0
  p := cc.π
  ι := 0
  wp := cc.condition
  hp := IsColimit.ofIsoColimit hcc (Cofork.ext (Iso.refl _) (by simp))
  wι := zero_comp
  hι := KernelFork.IsLimit.ofMonoOfIsZero _ (by
    have := hS.hasHomology
    refine ((MorphismProperty.monomorphisms C).arrow_mk_iso_iff ?_).2
      hS.mono_fromOpcycles
    refine Arrow.isoMk (IsColimit.coconePointUniqueUpToIso hcc S.opcyclesIsCokernel)
      (Iso.refl _) ?_
    apply Cofork.IsColimit.hom_ext hcc
    simp [IsColimit.coconePointUniqueUpToIso]) (isZero_zero C)

variable (S)

/--
lemma `exact_iff_epi_toCycles` / 引理 `exact_iff_epi_toCycles`

English:
lemma exact_iff_epi_toCycles
  given: [S.HasHomology]
  statement: S.Exact ↔ Epi S.toCycles
  proof: S.leftHomologyData.exact_iff_epi_f'

中文:
引理 exact_iff_epi_toCycles
  条件: [S.有同调]
  结论: S.正合 ↔ 满态射 S.toCycles
  证明: S.leftHomologyData.exact_iff_epi_f'

Depends on / 依赖: S.leftHomologyData.exact_iff_epi_f, exact_iff_epi_f, leftHomologyData
-/
lemma exact_iff_epi_toCycles [S.HasHomology] : S.Exact ↔ Epi S.toCycles :=
  S.leftHomologyData.exact_iff_epi_f'

/--
lemma `exact_iff_mono_fromOpcycles` / 引理 `exact_iff_mono_fromOpcycles`

English:
lemma exact_iff_mono_fromOpcycles
  given: [S.HasHomology]
  statement: S.Exact ↔ Mono S.fromOpcycles
  proof: S.rightHomologyData.exact_iff_mono_g'

中文:
引理 exact_iff_mono_fromOpcycles
  条件: [S.有同调]
  结论: S.正合 ↔ 单态射 S.fromOpcycles
  证明: S.rightHomologyData.exact_iff_mono_g'

Depends on / 依赖: S.rightHomologyData.exact_iff_mono_g, exact_iff_mono_g, rightHomologyData
-/
lemma exact_iff_mono_fromOpcycles [S.HasHomology] : S.Exact ↔ Mono S.fromOpcycles :=
  S.rightHomologyData.exact_iff_mono_g'

set_option backward.defeqAttrib.useBackward true in
/--
lemma `exact_iff_epi_kernel_lift` / 引理 `exact_iff_epi_kernel_lift`

English:
lemma exact_iff_epi_kernel_lift
  given: [S.HasHomology] [HasKernel S.g]
  proof: by
  rw [exact_iff_epi_toCycles]
  apply (MorphismProperty.epimorphisms C).arrow_mk_iso_iff
  exact Arrow.isoMk (Iso.refl _) S.cyclesIsoKernel (by cat_disch)

中文:
引理 exact_iff_epi_kernel_lift
  条件: [S.有同调] [HasKernel S.g]
  证明: by
  rw [exact_iff_epi_toCycles]
  apply (MorphismProperty.epimorphisms C).arrow_mk_iso_iff
  exact Arrow.isoMk (Iso.refl _) S.cyclesIsoKernel (by cat_disch)

Depends on / 依赖: Arrow.isoMk, Iso.refl, MorphismProperty, MorphismProperty.epimorphisms, S.cyclesIsoKernel, arrow_mk_iso_iff, cat_disch, cyclesIsoKernel, epimorphisms, exact_iff_epi_toCycles, infer_instance
-/
lemma exact_iff_epi_kernel_lift [S.HasHomology] [HasKernel S.g] :
    S.Exact ↔ Epi (kernel.lift S.g S.f S.zero) := by
  rw [exact_iff_epi_toCycles]
  apply (MorphismProperty.epimorphisms C).arrow_mk_iso_iff
  exact Arrow.isoMk (Iso.refl _) S.cyclesIsoKernel (by cat_disch)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `exact_iff_mono_cokernel_desc` / 引理 `exact_iff_mono_cokernel_desc`

English:
lemma exact_iff_mono_cokernel_desc
  given: [S.HasHomology] [HasCokernel S.f]
  proof: by
  rw [exact_iff_mono_fromOpcycles]
  refine (MorphismProperty.monomorphisms C).arrow_mk_iso_iff (Iso.symm ?_)
  exact Arrow.isoMk S.opcyclesIsoCokernel.symm (Iso.refl _) (by cat_disch)

中文:
引理 exact_iff_mono_cokernel_desc
  条件: [S.有同调] [HasCokernel S.f]
  证明: by
  rw [exact_iff_mono_fromOpcycles]
  refine (MorphismProperty.monomorphisms C).arrow_mk_iso_iff (Iso.symm ?_)
  exact Arrow.isoMk S.opcyclesIsoCokernel.symm (Iso.refl _) (by cat_disch)

Depends on / 依赖: Arrow.isoMk, Iso.refl, Iso.symm, MorphismProperty, MorphismProperty.monomorphisms, S.opcyclesIsoCokernel.symm, arrow_mk_iso_iff, cat_disch, exact_iff_mono_fromOpcycles, infer_instance, monomorphisms, opcyclesIsoCokernel
-/
lemma exact_iff_mono_cokernel_desc [S.HasHomology] [HasCokernel S.f] :
    S.Exact ↔ Mono (cokernel.desc S.f S.g S.zero) := by
  rw [exact_iff_mono_fromOpcycles]
  refine (MorphismProperty.monomorphisms C).arrow_mk_iso_iff (Iso.symm ?_)
  exact Arrow.isoMk S.opcyclesIsoCokernel.symm (Iso.refl _) (by cat_disch)

variable {S} in
/--
lemma `Exact.mono_cokernelDesc` / 引理 `Exact.mono_cokernelDesc`

English:
lemma Exact.mono_cokernelDesc
  given: [S.HasHomology] [HasCokernel S.f] (hS : S.Exact)
  proof: S.exact_iff_mono_cokernel_desc.1 hS

中文:
引理 正合.mono_cokernelDesc
  条件: [S.有同调] [HasCokernel S.f] (hS : S.正合)
  证明: S.exact_iff_mono_cokernel_desc.1 hS

Depends on / 依赖: S.exact_iff_mono_cokernel_desc, exact_iff_mono_cokernel_desc
-/
lemma Exact.mono_cokernelDesc [S.HasHomology] [HasCokernel S.f] (hS : S.Exact) :
    Mono (Limits.cokernel.desc S.f S.g S.zero) :=
  S.exact_iff_mono_cokernel_desc.1 hS

variable {S} in
/--
lemma `Exact.epi_kernelLift` / 引理 `Exact.epi_kernelLift`

English:
lemma Exact.epi_kernelLift
  given: [S.HasHomology] [HasKernel S.g] (hS : S.Exact)
  proof: S.exact_iff_epi_kernel_lift.1 hS

中文:
引理 正合.epi_kernelLift
  条件: [S.有同调] [HasKernel S.g] (hS : S.正合)
  证明: S.exact_iff_epi_kernel_lift.1 hS

Depends on / 依赖: S.exact_iff_epi_kernel_lift, exact_iff_epi_kernel_lift
-/
lemma Exact.epi_kernelLift [S.HasHomology] [HasKernel S.g] (hS : S.Exact) :
    Epi (Limits.kernel.lift S.g S.f S.zero) :=
  S.exact_iff_epi_kernel_lift.1 hS

/--
lemma `QuasiIso.exact_iff` / 引理 `QuasiIso.exact_iff`

English:
lemma QuasiIso.exact_iff
  statement: {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
  proof: by
  simp only [exact_iff_isZero_homology]
  exact Iso.isZero_iff (asIso (homologyMap φ))

中文:
引理 拟同构.exact_iff
  结论: {S₁ S₂ : 短复形 C} (φ : S₁ ⟶ S₂)
  证明: by
  simp only [exact_iff_isZero_homology]
  exact Iso.isZero_iff (asIso (homologyMap φ))

Depends on / 依赖: Iso.isZero_iff, exact_iff_isZero_homology, homologyMap, isZero_iff
-/
lemma QuasiIso.exact_iff {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    [S₁.HasHomology] [S₂.HasHomology] [QuasiIso φ] : S₁.Exact ↔ S₂.Exact := by
  simp only [exact_iff_isZero_homology]
  exact Iso.isZero_iff (asIso (homologyMap φ))

/--
lemma `exact_of_f_is_kernel` / 引理 `exact_of_f_is_kernel`

English:
lemma exact_of_f_is_kernel
  statement: (hS : IsLimit (KernelFork.ofι S.f S.zero))
  proof: by
  rw [exact_iff_epi_toCycles]
  have : IsSplitEpi S.toCycles :=
    ⟨⟨{ section_ := hS.lift (KernelFork.ofι S.iCycles S.iCycles_g)
        id := by
          rw [← cancel_mono S.iCycles]; rw [assoc]; rw [toCycles_i]; rw [id_comp]
          exact Fork.IsLimit.lift_ι hS }⟩⟩
  infer_instance

中文:
引理 exact_of_f_is_kernel
  结论: (hS : 是极限 (核叉.ofι S.f S.zero))
  证明: by
  rw [exact_iff_epi_toCycles]
  have : IsSplitEpi S.toCycles :=
    ⟨⟨{ section_ := hS.lift (KernelFork.ofι S.iCycles S.iCycles_g)
        id := by
          rw [← cancel_mono S.iCycles]; rw [assoc]; rw [toCycles_i]; rw [id_comp]
          exact Fork.IsLimit.lift_ι hS }⟩⟩
  infer_instance

Depends on / 依赖: Fork.IsLimit.lift_, IsLimit, IsSplitEpi, KernelFork, KernelFork.of, S.iCycles, S.iCycles_g, S.toCycles, cancel_mono, exact_iff_epi_toCycles, hS.lift, iCycles, iCycles_g, id_comp, infer_instance, section_, toCycles, toCycles_i
-/
lemma exact_of_f_is_kernel (hS : IsLimit (KernelFork.ofι S.f S.zero))
    [S.HasHomology] : S.Exact := by
  rw [exact_iff_epi_toCycles]
  have : IsSplitEpi S.toCycles :=
    ⟨⟨{ section_ := hS.lift (KernelFork.ofι S.iCycles S.iCycles_g)
        id := by
          rw [← cancel_mono S.iCycles]; rw [assoc]; rw [toCycles_i]; rw [id_comp]
          exact Fork.IsLimit.lift_ι hS }⟩⟩
  infer_instance

/--
lemma `exact_of_g_is_cokernel` / 引理 `exact_of_g_is_cokernel`

English:
lemma exact_of_g_is_cokernel
  statement: (hS : IsColimit (CokernelCofork.ofπ S.g S.zero))
  proof: by
  rw [exact_iff_mono_fromOpcycles]
  have : IsSplitMono S.fromOpcycles :=
    ⟨⟨{ retraction := hS.desc (CokernelCofork.ofπ S.pOpcycles S.f_pOpcycles)
        id := by
          rw [← cancel_epi S.pOpcycles]; rw [p_fromOpcycles_assoc]; rw [comp_id]
          exact Cofork.IsColimit.π_desc hS }⟩⟩
  infer_instance

中文:
引理 exact_of_g_is_cokernel
  结论: (hS : 是余极限 (余核余叉.ofπ S.g S.zero))
  证明: by
  rw [exact_iff_mono_fromOpcycles]
  have : IsSplitMono S.fromOpcycles :=
    ⟨⟨{ retraction := hS.desc (CokernelCofork.ofπ S.pOpcycles S.f_pOpcycles)
        id := by
          rw [← cancel_epi S.pOpcycles]; rw [p_fromOpcycles_assoc]; rw [comp_id]
          exact Cofork.IsColimit.π_desc hS }⟩⟩
  infer_instance

Depends on / 依赖: Cofork, Cofork.IsColimit, CokernelCofork, CokernelCofork.of, IsColimit, IsSplitMono, S.f_pOpcycles, S.fromOpcycles, S.pOpcycles, cancel_epi, comp_id, exact_iff_mono_fromOpcycles, f_pOpcycles, fromOpcycles, hS.desc, infer_instance, pOpcycles, p_fromOpcycles_assoc, retraction
-/
lemma exact_of_g_is_cokernel (hS : IsColimit (CokernelCofork.ofπ S.g S.zero))
    [S.HasHomology] : S.Exact := by
  rw [exact_iff_mono_fromOpcycles]
  have : IsSplitMono S.fromOpcycles :=
    ⟨⟨{ retraction := hS.desc (CokernelCofork.ofπ S.pOpcycles S.f_pOpcycles)
        id := by
          rw [← cancel_epi S.pOpcycles]; rw [p_fromOpcycles_assoc]; rw [comp_id]
          exact Cofork.IsColimit.π_desc hS }⟩⟩
  infer_instance

variable {S}

/--
lemma `Exact.mono_g` / 引理 `Exact.mono_g`

English:
lemma Exact.mono_g
  given: (hS : S.Exact) (hf : S.f = 0)
  statement: Mono S.g
  proof: by
  have := hS.hasHomology
  have := hS.epi_toCycles
  have : S.iCycles = 0 := by rw [← cancel_epi S.toCycles, comp_zero, toCycles_i, hf]
  apply Preadditive.mono_of_cancel_zero
  intro A x₂ hx₂
  rw [← S.liftCycles_i x₂ hx₂]; rw [this]; rw [comp_zero]

中文:
引理 正合.mono_g
  条件: (hS : S.正合) (hf : S.f = 0)
  结论: 单态射 S.g
  证明: by
  have := hS.hasHomology
  have := hS.epi_toCycles
  have : S.iCycles = 0 := by rw [← cancel_epi S.toCycles, comp_zero, toCycles_i, hf]
  apply Preadditive.mono_of_cancel_zero
  intro A x₂ hx₂
  rw [← S.liftCycles_i x₂ hx₂]; rw [this]; rw [comp_zero]

Depends on / 依赖: Preadditive, Preadditive.mono_of_cancel_zero, S.iCycles, S.liftCycles_i, S.toCycles, cancel_epi, comp_zero, epi_toCycles, hS.epi_toCycles, hS.hasHomology, hasHomology, iCycles, liftCycles_i, mono_of_cancel_zero, toCycles, toCycles_i
-/
lemma Exact.mono_g (hS : S.Exact) (hf : S.f = 0) : Mono S.g := by
  have := hS.hasHomology
  have := hS.epi_toCycles
  have : S.iCycles = 0 := by rw [← cancel_epi S.toCycles, comp_zero, toCycles_i, hf]
  apply Preadditive.mono_of_cancel_zero
  intro A x₂ hx₂
  rw [← S.liftCycles_i x₂ hx₂]; rw [this]; rw [comp_zero]

/--
lemma `Exact.epi_f` / 引理 `Exact.epi_f`

English:
lemma Exact.epi_f
  given: (hS : S.Exact) (hg : S.g = 0)
  statement: Epi S.f
  proof: by
  have := hS.hasHomology
  have := hS.mono_fromOpcycles
  have : S.pOpcycles = 0 := by rw [← cancel_mono S.fromOpcycles, zero_comp, p_fromOpcycles, hg]
  apply Preadditive.epi_of_cancel_zero
  intro A x₂ hx₂
  rw [← S.p_descOpcycles x₂ hx₂]; rw [this]; rw [zero_comp]

中文:
引理 正合.epi_f
  条件: (hS : S.正合) (hg : S.g = 0)
  结论: 满态射 S.f
  证明: by
  have := hS.hasHomology
  have := hS.mono_fromOpcycles
  have : S.pOpcycles = 0 := by rw [← cancel_mono S.fromOpcycles, zero_comp, p_fromOpcycles, hg]
  apply Preadditive.epi_of_cancel_zero
  intro A x₂ hx₂
  rw [← S.p_descOpcycles x₂ hx₂]; rw [this]; rw [zero_comp]

Depends on / 依赖: Preadditive, Preadditive.epi_of_cancel_zero, S.fromOpcycles, S.pOpcycles, S.p_descOpcycles, cancel_mono, epi_of_cancel_zero, fromOpcycles, hS.hasHomology, hS.mono_fromOpcycles, hasHomology, mono_fromOpcycles, pOpcycles, p_descOpcycles, p_fromOpcycles, zero_comp
-/
lemma Exact.epi_f (hS : S.Exact) (hg : S.g = 0) : Epi S.f := by
  have := hS.hasHomology
  have := hS.mono_fromOpcycles
  have : S.pOpcycles = 0 := by rw [← cancel_mono S.fromOpcycles, zero_comp, p_fromOpcycles, hg]
  apply Preadditive.epi_of_cancel_zero
  intro A x₂ hx₂
  rw [← S.p_descOpcycles x₂ hx₂]; rw [this]; rw [zero_comp]

/--
lemma `Exact.mono_g_iff` / 引理 `Exact.mono_g_iff`

English:
lemma Exact.mono_g_iff
  given: (hS : S.Exact)
  statement: Mono S.g ↔ S.f = 0
  proof: by
  constructor
  · intro
    rw [← cancel_mono S.g]; rw [zero]; rw [zero_comp]
  · exact hS.mono_g

中文:
引理 正合.mono_g_iff
  条件: (hS : S.正合)
  结论: 单态射 S.g ↔ S.f = 0
  证明: by
  constructor
  · intro
    rw [← cancel_mono S.g]; rw [zero]; rw [zero_comp]
  · exact hS.mono_g

Depends on / 依赖: cancel_mono, hS.mono_g, mono_g, zero_comp
-/
lemma Exact.mono_g_iff (hS : S.Exact) : Mono S.g ↔ S.f = 0 := by
  constructor
  · intro
    rw [← cancel_mono S.g]; rw [zero]; rw [zero_comp]
  · exact hS.mono_g

/--
lemma `Exact.epi_f_iff` / 引理 `Exact.epi_f_iff`

English:
lemma Exact.epi_f_iff
  given: (hS : S.Exact)
  statement: Epi S.f ↔ S.g = 0
  proof: by
  constructor
  · intro
    rw [← cancel_epi S.f]; rw [zero]; rw [comp_zero]
  · exact hS.epi_f

中文:
引理 正合.epi_f_iff
  条件: (hS : S.正合)
  结论: 满态射 S.f ↔ S.g = 0
  证明: by
  constructor
  · intro
    rw [← cancel_epi S.f]; rw [zero]; rw [comp_zero]
  · exact hS.epi_f

Depends on / 依赖: cancel_epi, comp_zero, epi_f, hS.epi_f
-/
lemma Exact.epi_f_iff (hS : S.Exact) : Epi S.f ↔ S.g = 0 := by
  constructor
  · intro
    rw [← cancel_epi S.f]; rw [zero]; rw [comp_zero]
  · exact hS.epi_f

/--
lemma `Exact.isZero_X₂` / 引理 `Exact.isZero_X₂`

English:
lemma Exact.isZero_X₂
  given: (hS : S.Exact) (hf : S.f = 0) (hg : S.g = 0)
  statement: IsZero S.X₂
  proof: by
  have := hS.mono_g hf
  rw [IsZero.iff_id_eq_zero]; rw [← cancel_mono S.g]; rw [hg]; rw [comp_zero]; rw [comp_zero]

中文:
引理 正合.isZero_X₂
  条件: (hS : S.正合) (hf : S.f = 0) (hg : S.g = 0)
  结论: 是零 S.X₂
  证明: by
  have := hS.mono_g hf
  rw [IsZero.iff_id_eq_zero]; rw [← cancel_mono S.g]; rw [hg]; rw [comp_zero]; rw [comp_zero]

Depends on / 依赖: IsZero, IsZero.iff_id_eq_zero, cancel_mono, comp_zero, hS.mono_g, iff_id_eq_zero, mono_g
-/
lemma Exact.isZero_X₂ (hS : S.Exact) (hf : S.f = 0) (hg : S.g = 0) : IsZero S.X₂ := by
  have := hS.mono_g hf
  rw [IsZero.iff_id_eq_zero]; rw [← cancel_mono S.g]; rw [hg]; rw [comp_zero]; rw [comp_zero]

/--
lemma `Exact.isZero_X₂_iff` / 引理 `Exact.isZero_X₂_iff`

English:
lemma Exact.isZero_X₂_iff
  given: (hS : S.Exact)
  statement: IsZero S.X₂ ↔ S.f = 0 ∧ S.g = 0
  proof: by
  constructor
  · intro h
    exact ⟨h.eq_of_tgt _ _, h.eq_of_src _ _⟩
  · rintro ⟨hf, hg⟩
    exact hS.isZero_X₂ hf hg

中文:
引理 正合.isZero_X₂_iff
  条件: (hS : S.正合)
  结论: 是零 S.X₂ ↔ S.f = 0 ∧ S.g = 0
  证明: by
  constructor
  · intro h
    exact ⟨h.eq_of_tgt _ _, h.eq_of_src _ _⟩
  · rintro ⟨hf, hg⟩
    exact hS.isZero_X₂ hf hg

Depends on / 依赖: eq_of_src, eq_of_tgt, h.eq_of_src, h.eq_of_tgt, hS.isZero_X
-/
lemma Exact.isZero_X₂_iff (hS : S.Exact) : IsZero S.X₂ ↔ S.f = 0 ∧ S.g = 0 := by
  constructor
  · intro h
    exact ⟨h.eq_of_tgt _ _, h.eq_of_src _ _⟩
  · rintro ⟨hf, hg⟩
    exact hS.isZero_X₂ hf hg

variable (S)

/--
Definition of `Splitting` / `Splitting` 的定义

English:
structure Splitting
  parameters: (S : ShortComplex C)
  axioms and operations (5):
    - r : S.X₂ ⟶ S.X₁
    - s : S.X₃ ⟶ S.X₂
    - f_r : S.f ≫ r = 𝟙 _  [default: by cat_disch]
    - s_g : s ≫ S.g = 𝟙 _  [default: by cat_disch]
    - id : r ≫ S.f + S.g ≫ s = 𝟙 _  [default: by cat_disch]

中文:
结构 Splitting
  参数: (S : 短复形 C)
  公理与运算 (5 个):
    - r : S.X₂ ⟶ S.X₁
    - s : S.X₃ ⟶ S.X₂
    - f_r : S.f ≫ r = 𝟙 _  [默认: by cat_disch]
    - s_g : s ≫ S.g = 𝟙 _  [默认: by cat_disch]
    - id : r ≫ S.f + S.g ≫ s = 𝟙 _  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Splitting (S : ShortComplex C) where
  /-- a retraction of `S.f` -/
  r : S.X₂ ⟶ S.X₁
  /-- a section of `S.g` -/
  s : S.X₃ ⟶ S.X₂
  /-- the condition that `r` is a retraction of `S.f` -/
  f_r : S.f ≫ r = 𝟙 _ := by cat_disch
  /-- the condition that `s` is a section of `S.g` -/
  s_g : s ≫ S.g = 𝟙 _ := by cat_disch
  /-- the compatibility between the given section and retraction -/
  id : r ≫ S.f + S.g ≫ s = 𝟙 _ := by cat_disch

namespace Splitting

attribute [reassoc (attr := simp)] f_r s_g

variable {S}

@[reassoc]
/--
lemma `r_f` / 引理 `r_f`

English:
lemma r_f
  given: (s : S.Splitting)
  statement: s.r ≫ S.f = 𝟙 _ - S.g ≫ s.s
  proof: by rw [← s.id, add_sub_cancel_right]

@[reassoc]

中文:
引理 r_f
  条件: (s : S.Splitting)
  结论: s.r ≫ S.f = 𝟙 _ - S.g ≫ s.s
  证明: by rw [← s.id, add_sub_cancel_right]

@[reassoc]

Depends on / 依赖: add_sub_cancel_right, s.id
-/
lemma r_f (s : S.Splitting) : s.r ≫ S.f = 𝟙 _ - S.g ≫ s.s := by rw [← s.id, add_sub_cancel_right]

@[reassoc]
/--
lemma `g_s` / 引理 `g_s`

English:
lemma g_s
  given: (s : S.Splitting)
  statement: S.g ≫ s.s = 𝟙 _ - s.r ≫ S.f
  proof: by rw [← s.id, add_sub_cancel_left]

中文:
引理 g_s
  条件: (s : S.Splitting)
  结论: S.g ≫ s.s = 𝟙 _ - s.r ≫ S.f
  证明: by rw [← s.id, add_sub_cancel_left]

Depends on / 依赖: add_sub_cancel_left, s.id
-/
lemma g_s (s : S.Splitting) : S.g ≫ s.s = 𝟙 _ - s.r ≫ S.f := by rw [← s.id, add_sub_cancel_left]

/--
Definition of `splitMono_f` / `splitMono_f` 的定义

English:
definition splitMono_f
  signature: (s : S.Splitting)
  body: ⟨s.r, s.f_r⟩

中文:
定义 splitMono_f
  签名: (s : S.Splitting)
  定义体: ⟨s.r, s.f_r⟩
-/
@[simps] def splitMono_f (s : S.Splitting) : SplitMono S.f := ⟨s.r, s.f_r⟩

/--
lemma `isSplitMono_f` / 引理 `isSplitMono_f`

English:
lemma isSplitMono_f
  given: (s : S.Splitting)
  statement: IsSplitMono S.f
  proof: ⟨⟨s.splitMono_f⟩⟩

中文:
引理 isSplitMono_f
  条件: (s : S.Splitting)
  结论: 是分裂单态射 S.f
  证明: ⟨⟨s.splitMono_f⟩⟩

Depends on / 依赖: s.splitMono_f, splitMono_f
-/
lemma isSplitMono_f (s : S.Splitting) : IsSplitMono S.f := ⟨⟨s.splitMono_f⟩⟩

/--
lemma `mono_f` / 引理 `mono_f`

English:
lemma mono_f
  given: (s : S.Splitting)
  statement: Mono S.f
  proof: by
  have := s.isSplitMono_f
  infer_instance

中文:
引理 mono_f
  条件: (s : S.Splitting)
  结论: 单态射 S.f
  证明: by
  have := s.isSplitMono_f
  infer_instance

Depends on / 依赖: infer_instance, isSplitMono_f, s.isSplitMono_f
-/
lemma mono_f (s : S.Splitting) : Mono S.f := by
  have := s.isSplitMono_f
  infer_instance

/--
Definition of `splitEpi_g` / `splitEpi_g` 的定义

English:
definition splitEpi_g
  signature: (s : S.Splitting)
  body: ⟨s.s, s.s_g⟩

中文:
定义 splitEpi_g
  签名: (s : S.Splitting)
  定义体: ⟨s.s, s.s_g⟩
-/
@[simps] def splitEpi_g (s : S.Splitting) : SplitEpi S.g := ⟨s.s, s.s_g⟩

/--
lemma `isSplitEpi_g` / 引理 `isSplitEpi_g`

English:
lemma isSplitEpi_g
  given: (s : S.Splitting)
  statement: IsSplitEpi S.g
  proof: ⟨⟨s.splitEpi_g⟩⟩

中文:
引理 isSplitEpi_g
  条件: (s : S.Splitting)
  结论: 是分裂满态射 S.g
  证明: ⟨⟨s.splitEpi_g⟩⟩

Depends on / 依赖: s.splitEpi_g, splitEpi_g
-/
lemma isSplitEpi_g (s : S.Splitting) : IsSplitEpi S.g := ⟨⟨s.splitEpi_g⟩⟩

/--
lemma `epi_g` / 引理 `epi_g`

English:
lemma epi_g
  given: (s : S.Splitting)
  statement: Epi S.g
  proof: by
  have := s.isSplitEpi_g
  infer_instance

@[reassoc (attr := simp)]

中文:
引理 epi_g
  条件: (s : S.Splitting)
  结论: 满态射 S.g
  证明: by
  have := s.isSplitEpi_g
  infer_instance

@[reassoc (attr := simp)]

Depends on / 依赖: ShortComplex, ShortComplex.exact_iff_epi_kernel_lift, X.exact, exact_iff_epi_kernel_lift, infer_instance, isSplitEpi_g, s.isSplitEpi_g
-/
lemma epi_g (s : S.Splitting) : Epi S.g := by
  have := s.isSplitEpi_g
  infer_instance

@[reassoc (attr := simp)]
/--
lemma `s_r` / 引理 `s_r`

English:
lemma s_r
  given: (s : S.Splitting)
  statement: s.s ≫ s.r = 0
  proof: by
  have := s.epi_g
  simp only [← cancel_epi S.g, comp_zero, g_s_assoc, sub_comp, id_comp,
    assoc, f_r, comp_id, sub_self]

中文:
引理 s_r
  条件: (s : S.Splitting)
  结论: s.s ≫ s.r = 0
  证明: by
  have := s.epi_g
  simp only [← cancel_epi S.g, comp_zero, g_s_assoc, sub_comp, id_comp,
    assoc, f_r, comp_id, sub_self]

Depends on / 依赖: cancel_epi, comp_id, comp_zero, epi_g, g_s_assoc, id_comp, s.epi_g, sub_comp, sub_self
-/
lemma s_r (s : S.Splitting) : s.s ≫ s.r = 0 := by
  have := s.epi_g
  simp only [← cancel_epi S.g, comp_zero, g_s_assoc, sub_comp, id_comp,
    assoc, f_r, comp_id, sub_self]

/--
lemma `ext_r` / 引理 `ext_r`

English:
lemma ext_r
  given: (s s' : S.Splitting) (h : s.r = s'.r)
  statement: s = s'
  proof: by
  have := s.epi_g
  have eq := s.id
  rw [← s'.id]; rw [h]; rw [add_right_inj]; rw [cancel_epi S.g] at eq
  cases s
  congr

中文:
引理 ext_r
  条件: (s s' : S.Splitting) (h : s.r = s'.r)
  结论: s = s'
  证明: by
  have := s.epi_g
  have eq := s.id
  rw [← s'.id]; rw [h]; rw [add_right_inj]; rw [cancel_epi S.g] at eq
  cases s
  congr

Depends on / 依赖: add_right_inj, cancel_epi, epi_g, s.epi_g, s.id
-/
lemma ext_r (s s' : S.Splitting) (h : s.r = s'.r) : s = s' := by
  have := s.epi_g
  have eq := s.id
  rw [← s'.id]; rw [h]; rw [add_right_inj]; rw [cancel_epi S.g] at eq
  cases s
  congr

/--
lemma `ext_s` / 引理 `ext_s`

English:
lemma ext_s
  given: (s s' : S.Splitting) (h : s.s = s'.s)
  statement: s = s'
  proof: by
  have := s.mono_f
  have eq := s.id
  rw [← s'.id]; rw [h]; rw [add_left_inj]; rw [cancel_mono S.f] at eq
  cases s
  congr

中文:
引理 ext_s
  条件: (s s' : S.Splitting) (h : s.s = s'.s)
  结论: s = s'
  证明: by
  have := s.mono_f
  have eq := s.id
  rw [← s'.id]; rw [h]; rw [add_left_inj]; rw [cancel_mono S.f] at eq
  cases s
  congr

Depends on / 依赖: add_left_inj, cancel_mono, mono_f, s.id, s.mono_f
-/
lemma ext_s (s s' : S.Splitting) (h : s.s = s'.s) : s = s' := by
  have := s.mono_f
  have eq := s.id
  rw [← s'.id]; rw [h]; rw [add_left_inj]; rw [cancel_mono S.f] at eq
  cases s
  congr

/-- The left homology data on a short complex equipped with a splitting. -/
@[simps]
/--
Definition of `leftHomologyData` / `leftHomologyData` 的定义

English:
definition leftHomologyData
  signature: [HasZeroObject C] (s : S.Splitting)
  body: by
  have hi := KernelFork.IsLimit.ofι S.f S.zero
    (fun x _ => x ≫ s.r)
    (fun x hx => by simp only [assoc, s.r_f, comp_sub, comp_id,
      sub_eq_self, reassoc_of% hx, zero_comp])
    (fun x _ b hb => by simp only [← hb, assoc, f_r, comp_id])
  let f' := hi.lift (KernelFork.ofι S.f S.zero)
  have hf' : f' = 𝟙 _ := by simp [f']
  have wπ : f' ≫ (0 : S.X₁ ⟶ 0) = 0 := comp_zero
  have hπ : IsColimit (CokernelCofork.ofπ 0 wπ) := CokernelCofork.IsColimit.ofEpiOfIsZero _
      (by rw [hf']; infer_instance) (isZero_zero _)
  exact
    { K := S.X₁
      H := 0
      i := S.f
      wi := S.zero
      hi := hi
      π := 0
      wπ := wπ
      hπ := hπ }

中文:
定义 leftHomologyData
  签名: [有ZeroObject C] (s : S.Splitting)
  定义体: by
  have hi := KernelFork.IsLimit.ofι S.f S.zero
    (fun x _ => x ≫ s.r)
    (fun x hx => by simp only [assoc, s.r_f, comp_sub, comp_id,
      sub_eq_self, reassoc_of% hx, zero_comp])
    (fun x _ b hb => by simp only [← hb, assoc, f_r, comp_id])
  let f' := hi.lift (KernelFork.ofι S.f S.zero)
  have hf' : f' = 𝟙 _ := by simp [f']
  have wπ : f' ≫ (0 : S.X₁ ⟶ 0) = 0 := comp_zero
  have hπ : IsColimit (CokernelCofork.ofπ 0 wπ) := CokernelCofork.IsColimit.ofEpiOfIsZero _
      (by rw [hf']; infer_instance) (isZero_zero _)
  exact
    { K := S.X₁
      H := 0
      i := S.f
      wi := S.zero
      hi := hi
      π := 0
      wπ := wπ
      hπ := hπ }

Depends on / 依赖: CokernelCofork, CokernelCofork.IsColimit.ofEpiOfIsZero, CokernelCofork.of, IsColimit, IsLimit, KernelFork, KernelFork.IsLimit.of, KernelFork.of, S.zero, ShortComplex, ShortComplex.exact_iff_mono_cokernel_desc, X.exact, comp_id, comp_sub, comp_zero, exact_iff_mono_cokernel_desc, hi.lift, infer_instance, isZero_zero, ofEpiOfIsZero
-/
noncomputable def leftHomologyData [HasZeroObject C] (s : S.Splitting) :
    LeftHomologyData S := by
  have hi := KernelFork.IsLimit.ofι S.f S.zero
    (fun x _ => x ≫ s.r)
    (fun x hx => by simp only [assoc, s.r_f, comp_sub, comp_id,
      sub_eq_self, reassoc_of% hx, zero_comp])
    (fun x _ b hb => by simp only [← hb, assoc, f_r, comp_id])
  let f' := hi.lift (KernelFork.ofι S.f S.zero)
  have hf' : f' = 𝟙 _ := by simp [f']
  have wπ : f' ≫ (0 : S.X₁ ⟶ 0) = 0 := comp_zero
  have hπ : IsColimit (CokernelCofork.ofπ 0 wπ) := CokernelCofork.IsColimit.ofEpiOfIsZero _
      (by rw [hf']; infer_instance) (isZero_zero _)
  exact
    { K := S.X₁
      H := 0
      i := S.f
      wi := S.zero
      hi := hi
      π := 0
      wπ := wπ
      hπ := hπ }

set_option backward.defeqAttrib.useBackward true in
/-- The right homology data on a short complex equipped with a splitting. -/
@[simps]
/--
Definition of `rightHomologyData` / `rightHomologyData` 的定义

English:
definition rightHomologyData
  signature: [HasZeroObject C] (s : S.Splitting)
  body: by
  have hp := CokernelCofork.IsColimit.ofπ S.g S.zero
    (fun x _ => s.s ≫ x)
    (fun x hx => by simp only [s.g_s_assoc, sub_comp, id_comp, sub_eq_self, assoc, hx, comp_zero])
    (fun x _ b hb => by simp only [← hb, s.s_g_assoc])
  let g' := hp.desc (CokernelCofork.ofπ S.g S.zero)
  have hg' : g' = 𝟙 _ := by simp [g']
  have wι : (0 : 0 ⟶ S.X₃) ≫ g' = 0 := zero_comp
  have hι : IsLimit (KernelFork.ofι 0 wι) := KernelFork.IsLimit.ofMonoOfIsZero _
      (by rw [hg']; dsimp; infer_instance) (isZero_zero _)
  exact
    { Q := S.X₃
      H := 0
      p := S.g
      wp := S.zero
      hp := hp
      ι := 0
      wι := wι
      hι := hι }

中文:
定义 rightHomologyData
  签名: [有ZeroObject C] (s : S.Splitting)
  定义体: by
  have hp := CokernelCofork.IsColimit.ofπ S.g S.zero
    (fun x _ => s.s ≫ x)
    (fun x hx => by simp only [s.g_s_assoc, sub_comp, id_comp, sub_eq_self, assoc, hx, comp_zero])
    (fun x _ b hb => by simp only [← hb, s.s_g_assoc])
  let g' := hp.desc (CokernelCofork.ofπ S.g S.zero)
  have hg' : g' = 𝟙 _ := by simp [g']
  have wι : (0 : 0 ⟶ S.X₃) ≫ g' = 0 := zero_comp
  have hι : IsLimit (KernelFork.ofι 0 wι) := KernelFork.IsLimit.ofMonoOfIsZero _
      (by rw [hg']; dsimp; infer_instance) (isZero_zero _)
  exact
    { Q := S.X₃
      H := 0
      p := S.g
      wp := S.zero
      hp := hp
      ι := 0
      wι := wι
      hι := hι }

Depends on / 依赖: CokernelCofork, CokernelCofork.IsColimit.of, CokernelCofork.of, IsColimit, IsLimit, KernelFork, KernelFork.IsLimit.ofMonoOfIsZero, KernelFork.of, S.zero, comp_zero, g_s_assoc, hp.desc, id_comp, infer_instance, isZero_zero, ofMonoOfIsZero, s.g_s_assoc, s.s_g_assoc, s_g_assoc, sub_comp
-/
noncomputable def rightHomologyData [HasZeroObject C] (s : S.Splitting) :
    RightHomologyData S := by
  have hp := CokernelCofork.IsColimit.ofπ S.g S.zero
    (fun x _ => s.s ≫ x)
    (fun x hx => by simp only [s.g_s_assoc, sub_comp, id_comp, sub_eq_self, assoc, hx, comp_zero])
    (fun x _ b hb => by simp only [← hb, s.s_g_assoc])
  let g' := hp.desc (CokernelCofork.ofπ S.g S.zero)
  have hg' : g' = 𝟙 _ := by simp [g']
  have wι : (0 : 0 ⟶ S.X₃) ≫ g' = 0 := zero_comp
  have hι : IsLimit (KernelFork.ofι 0 wι) := KernelFork.IsLimit.ofMonoOfIsZero _
      (by rw [hg']; dsimp; infer_instance) (isZero_zero _)
  exact
    { Q := S.X₃
      H := 0
      p := S.g
      wp := S.zero
      hp := hp
      ι := 0
      wι := wι
      hι := hι }

set_option backward.defeqAttrib.useBackward true in
/-- The homology data on a short complex equipped with a splitting. -/
@[simps]
/--
Definition of `homologyData` / `homologyData` 的定义

English:
definition homologyData
  signature: [HasZeroObject C] (s : S.Splitting)
  body: s.leftHomologyData
  right := s.rightHomologyData
  iso := Iso.refl 0

中文:
定义 homologyData
  签名: [有ZeroObject C] (s : S.Splitting)
  定义体: s.leftHomologyData
  right := s.rightHomologyData
  iso := Iso.refl 0

Depends on / 依赖: leftHomologyData, s.leftHomologyData
-/
noncomputable def homologyData [HasZeroObject C] (s : S.Splitting) : S.HomologyData where
  left := s.leftHomologyData
  right := s.rightHomologyData
  iso := Iso.refl 0

/--
lemma `exact` / 引理 `exact`

English:
lemma exact
  given: [HasZeroObject C] (s : S.Splitting)
  statement: S.Exact
  proof: ⟨s.homologyData, isZero_zero _⟩

中文:
引理 exact
  条件: [有ZeroObject C] (s : S.Splitting)
  结论: S.正合
  证明: ⟨s.homologyData, isZero_zero _⟩

Depends on / 依赖: homologyData, isZero_zero, s.homologyData
-/
lemma exact [HasZeroObject C] (s : S.Splitting) : S.Exact :=
  ⟨s.homologyData, isZero_zero _⟩

/--
Definition of `fIsKernel` / `fIsKernel` 的定义

English:
definition fIsKernel
  signature: [HasZeroObject C] (s : S.Splitting)
  body: s.homologyData.left.hi

中文:
定义 fIsKernel
  签名: [有ZeroObject C] (s : S.Splitting)
  定义体: s.homologyData.left.hi

Depends on / 依赖: homologyData, s.homologyData.left.hi
-/
noncomputable def fIsKernel [HasZeroObject C] (s : S.Splitting) :
    IsLimit (KernelFork.ofι S.f S.zero) :=
  s.homologyData.left.hi

/--
Definition of `gIsCokernel` / `gIsCokernel` 的定义

English:
definition gIsCokernel
  signature: [HasZeroObject C] (s : S.Splitting)
  body: s.homologyData.right.hp

中文:
定义 gIsCokernel
  签名: [有ZeroObject C] (s : S.Splitting)
  定义体: s.homologyData.right.hp

Depends on / 依赖: homologyData, s.homologyData.right.hp
-/
noncomputable def gIsCokernel [HasZeroObject C] (s : S.Splitting) :
    IsColimit (CokernelCofork.ofπ S.g S.zero) :=
  s.homologyData.right.hp

set_option backward.isDefEq.respectTransparency false in
/-- If a short complex `S` has a splitting and `F` is an additive functor, then
`S.map F` also has a splitting. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (s : S.Splitting) (F : C ⥤ D) [F.Additive]
  body: F.map s.r
  s := F.map s.s
  f_r := by
    dsimp [ShortComplex.map]
    rw [← F.map_comp]; rw [f_r]; rw [F.map_id]
  s_g := by
    dsimp [ShortComplex.map]
    simp only [← F.map_comp, s_g, F.map_id]
  id := by
    dsimp [ShortComplex.map]
    simp only [← F.map_id, ← s.id, Functor.map_comp, Functor.map_add]

中文:
定义 map
  签名: (s : S.Splitting) (F : C ⥤ D) [F.加性]
  定义体: F.map s.r
  s := F.map s.s
  f_r := by
    dsimp [ShortComplex.map]
    rw [← F.map_comp]; rw [f_r]; rw [F.map_id]
  s_g := by
    dsimp [ShortComplex.map]
    simp only [← F.map_comp, s_g, F.map_id]
  id := by
    dsimp [ShortComplex.map]
    simp only [← F.map_id, ← s.id, Functor.map_comp, Functor.map_add]

Depends on / 依赖: F.map
-/
def map (s : S.Splitting) (F : C ⥤ D) [F.Additive] : (S.map F).Splitting where
  r := F.map s.r
  s := F.map s.s
  f_r := by
    dsimp [ShortComplex.map]
    rw [← F.map_comp]; rw [f_r]; rw [F.map_id]
  s_g := by
    dsimp [ShortComplex.map]
    simp only [← F.map_comp, s_g, F.map_id]
  id := by
    dsimp [ShortComplex.map]
    simp only [← F.map_id, ← s.id, Functor.map_comp, Functor.map_add]

/-- A splitting on a short complex induces splittings on isomorphic short complexes. -/
@[simps]
/--
Definition of `ofIso` / `ofIso` 的定义

English:
definition ofIso
  signature: {S₁ S₂ : ShortComplex C} (s : S₁.Splitting) (e : S₁ ≅ S₂)
  body: e.inv.τ₂ ≫ s.r ≫ e.hom.τ₁
  s := e.inv.τ₃ ≫ s.s ≫ e.hom.τ₂
  f_r := by rw [← e.inv.comm₁₂_assoc, s.f_r_assoc, ← comp_τ₁, e.inv_hom_id, id_τ₁]
  s_g := by rw [assoc, assoc, e.hom.comm₂₃, s.s_g_assoc, ← comp_τ₃, e.inv_hom_id, id_τ₃]
  id := by
    have eq := e.inv.τ₂ ≫= s.id =≫ e.hom.τ₂
    rw [id_comp]; rw [← comp_τ₂]; rw [e.inv_hom_id]; rw [id_τ₂] at eq
    rw [← eq]; rw [assoc]; rw [assoc]; rw [add_comp]; rw [assoc]; rw [assoc]; rw [comp_add]; rw [e.hom.comm₁₂]; rw [e.inv.comm₂₃_assoc]

中文:
定义 ofIso
  签名: {S₁ S₂ : 短复形 C} (s : S₁.Splitting) (e : S₁ ≅ S₂)
  定义体: e.inv.τ₂ ≫ s.r ≫ e.hom.τ₁
  s := e.inv.τ₃ ≫ s.s ≫ e.hom.τ₂
  f_r := by rw [← e.inv.comm₁₂_assoc, s.f_r_assoc, ← comp_τ₁, e.inv_hom_id, id_τ₁]
  s_g := by rw [assoc, assoc, e.hom.comm₂₃, s.s_g_assoc, ← comp_τ₃, e.inv_hom_id, id_τ₃]
  id := by
    have eq := e.inv.τ₂ ≫= s.id =≫ e.hom.τ₂
    rw [id_comp]; rw [← comp_τ₂]; rw [e.inv_hom_id]; rw [id_τ₂] at eq
    rw [← eq]; rw [assoc]; rw [assoc]; rw [add_comp]; rw [assoc]; rw [assoc]; rw [comp_add]; rw [e.hom.comm₁₂]; rw [e.inv.comm₂₃_assoc]

Depends on / 依赖: e.hom, e.inv, infer_instance
-/
def ofIso {S₁ S₂ : ShortComplex C} (s : S₁.Splitting) (e : S₁ ≅ S₂) : S₂.Splitting where
  r := e.inv.τ₂ ≫ s.r ≫ e.hom.τ₁
  s := e.inv.τ₃ ≫ s.s ≫ e.hom.τ₂
  f_r := by rw [← e.inv.comm₁₂_assoc, s.f_r_assoc, ← comp_τ₁, e.inv_hom_id, id_τ₁]
  s_g := by rw [assoc, assoc, e.hom.comm₂₃, s.s_g_assoc, ← comp_τ₃, e.inv_hom_id, id_τ₃]
  id := by
    have eq := e.inv.τ₂ ≫= s.id =≫ e.hom.τ₂
    rw [id_comp]; rw [← comp_τ₂]; rw [e.inv_hom_id]; rw [id_τ₂] at eq
    rw [← eq]; rw [assoc]; rw [assoc]; rw [add_comp]; rw [assoc]; rw [assoc]; rw [comp_add]; rw [e.hom.comm₁₂]; rw [e.inv.comm₂₃_assoc]

/--
Definition of `ofHasBinaryBiproduct` / `ofHasBinaryBiproduct` 的定义

English:
definition ofHasBinaryBiproduct
  signature: (X₁ X₂ : C) [HasBinaryBiproduct X₁ X₂]
  body: biprod.fst
  s := biprod.inr

中文:
定义 ofHasBinaryBiproduct
  签名: (X₁ X₂ : C) [有BinaryBiproduct X₁ X₂]
  定义体: biprod.fst
  s := biprod.inr

Depends on / 依赖: biprod, biprod.fst, infer_instance
-/
noncomputable def ofHasBinaryBiproduct (X₁ X₂ : C) [HasBinaryBiproduct X₁ X₂] :
    Splitting (ShortComplex.mk (biprod.inl : X₁ ⟶ _) (biprod.snd : _ ⟶ X₂) (by simp)) where
  r := biprod.fst
  s := biprod.inr

variable (S)

/--
Definition of `ofIsZeroOfIsIso` / `ofIsZeroOfIsIso` 的定义

English:
definition ofIsZeroOfIsIso
  signature: (hf : IsZero S.X₁) (hg : IsIso S.g)
  body: 0
  s := inv S.g
  f_r := hf.eq_of_src _ _

中文:
定义 ofIsZeroOfIsIso
  签名: (hf : 是零 S.X₁) (hg : 是同构 S.g)
  定义体: 0
  s := inv S.g
  f_r := hf.eq_of_src _ _
-/
noncomputable def ofIsZeroOfIsIso (hf : IsZero S.X₁) (hg : IsIso S.g) : Splitting S where
  r := 0
  s := inv S.g
  f_r := hf.eq_of_src _ _

/--
Definition of `ofIsIsoOfIsZero` / `ofIsIsoOfIsZero` 的定义

English:
definition ofIsIsoOfIsZero
  signature: (hf : IsIso S.f) (hg : IsZero S.X₃)
  body: inv S.f
  s := 0
  s_g := hg.eq_of_src _ _

中文:
定义 ofIsIsoOfIsZero
  签名: (hf : 是同构 S.f) (hg : 是零 S.X₃)
  定义体: inv S.f
  s := 0
  s_g := hg.eq_of_src _ _
-/
noncomputable def ofIsIsoOfIsZero (hf : IsIso S.f) (hg : IsZero S.X₃) : Splitting S where
  r := inv S.f
  s := 0
  s_g := hg.eq_of_src _ _

variable {S}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The splitting of the short complex `S.op` deduced from a splitting of `S`. -/
@[simps]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: (h : Splitting S)
  body: h.s.op
  s := h.r.op
  f_r := Quiver.Hom.unop_inj (by simp)
  s_g := Quiver.Hom.unop_inj (by simp)
  id := Quiver.Hom.unop_inj (by
    simp only [op_X₂, Opposite.unop_op, op_X₁, op_f, op_X₃, op_g, unop_add, unop_comp,
      Quiver.Hom.unop_op, unop_id, ← h.id]
    abel)

中文:
定义 op
  签名: (h : Splitting S)
  定义体: h.s.op
  s := h.r.op
  f_r := Quiver.Hom.unop_inj (by simp)
  s_g := Quiver.Hom.unop_inj (by simp)
  id := Quiver.Hom.unop_inj (by
    simp only [op_X₂, Opposite.unop_op, op_X₁, op_f, op_X₃, op_g, unop_add, unop_comp,
      Quiver.Hom.unop_op, unop_id, ← h.id]
    abel)

Depends on / 依赖: h.s.op
-/
def op (h : Splitting S) : Splitting S.op where
  r := h.s.op
  s := h.r.op
  f_r := Quiver.Hom.unop_inj (by simp)
  s_g := Quiver.Hom.unop_inj (by simp)
  id := Quiver.Hom.unop_inj (by
    simp only [op_X₂, Opposite.unop_op, op_X₁, op_f, op_X₃, op_g, unop_add, unop_comp,
      Quiver.Hom.unop_op, unop_id, ← h.id]
    abel)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The splitting of the short complex `S.unop` deduced from a splitting of `S`. -/
@[simps]
/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: {S : ShortComplex Cᵒᵖ} (h : Splitting S)
  body: h.s.unop
  s := h.r.unop
  f_r := Quiver.Hom.op_inj (by simp)
  s_g := Quiver.Hom.op_inj (by simp)
  id := Quiver.Hom.op_inj (by
    simp only [unop_X₂, Opposite.op_unop, unop_X₁, unop_f, unop_X₃, unop_g, op_add,
      op_comp, Quiver.Hom.op_unop, op_id, ← h.id]
    abel)

中文:
定义 unop
  签名: {S : 短复形 Cᵒᵖ} (h : Splitting S)
  定义体: h.s.unop
  s := h.r.unop
  f_r := Quiver.Hom.op_inj (by simp)
  s_g := Quiver.Hom.op_inj (by simp)
  id := Quiver.Hom.op_inj (by
    simp only [unop_X₂, Opposite.op_unop, unop_X₁, unop_f, unop_X₃, unop_g, op_add,
      op_comp, Quiver.Hom.op_unop, op_id, ← h.id]
    abel)

Depends on / 依赖: h.s.unop
-/
def unop {S : ShortComplex Cᵒᵖ} (h : Splitting S) : Splitting S.unop where
  r := h.s.unop
  s := h.r.unop
  f_r := Quiver.Hom.op_inj (by simp)
  s_g := Quiver.Hom.op_inj (by simp)
  id := Quiver.Hom.op_inj (by
    simp only [unop_X₂, Opposite.op_unop, unop_X₁, unop_f, unop_X₃, unop_g, op_add,
      op_comp, Quiver.Hom.op_unop, op_id, ← h.id]
    abel)

/-- The isomorphism `S.X₂ ≅ S.X₁ ⊞ S.X₃` induced by a splitting of the short complex `S`. -/
@[simps]
/--
Definition of `isoBinaryBiproduct` / `isoBinaryBiproduct` 的定义

English:
definition isoBinaryBiproduct
  signature: (h : Splitting S) [HasBinaryBiproduct S.X₁ S.X₃]
  body: biprod.lift h.r S.g
  inv := biprod.desc S.f h.s
  hom_inv_id := by simp [h.id]

中文:
定义 isoBinaryBiproduct
  签名: (h : Splitting S) [有BinaryBiproduct S.X₁ S.X₃]
  定义体: biprod.lift h.r S.g
  inv := biprod.desc S.f h.s
  hom_inv_id := by simp [h.id]

Depends on / 依赖: biprod, biprod.lift
-/
noncomputable def isoBinaryBiproduct (h : Splitting S) [HasBinaryBiproduct S.X₁ S.X₃] :
    S.X₂ ≅ S.X₁ ⊞ S.X₃ where
  hom := biprod.lift h.r S.g
  inv := biprod.desc S.f h.s
  hom_inv_id := by simp [h.id]

end Splitting

section Balanced

variable {S}
variable [Balanced C]

namespace Exact

/--
lemma `isIso_f'` / 引理 `isIso_f'`

English:
lemma isIso_f'
  given: (hS : S.Exact) (h : S.LeftHomologyData) [Mono S.f]
  proof: by
  have := hS.epi_f' h
  have := mono_of_mono_fac h.f'_i
  exact isIso_of_mono_of_epi h.f'

中文:
引理 isIso_f'
  条件: (hS : S.正合) (h : S.LeftHomologyData) [单态射 S.f]
  证明: by
  have := hS.epi_f' h
  have := mono_of_mono_fac h.f'_i
  exact isIso_of_mono_of_epi h.f'

Depends on / 依赖: epi_f, hS.epi_f, isIso_of_mono_of_epi, mono_of_mono_fac
-/
lemma isIso_f' (hS : S.Exact) (h : S.LeftHomologyData) [Mono S.f] :
    IsIso h.f' := by
  have := hS.epi_f' h
  have := mono_of_mono_fac h.f'_i
  exact isIso_of_mono_of_epi h.f'

/--
lemma `isIso_toCycles` / 引理 `isIso_toCycles`

English:
lemma isIso_toCycles
  given: (hS : S.Exact) [Mono S.f] [S.HasLeftHomology]
  proof: hS.isIso_f' _

中文:
引理 isIso_toCycles
  条件: (hS : S.正合) [单态射 S.f] [S.有LeftHomology]
  证明: hS.isIso_f' _

Depends on / 依赖: hS.isIso_f, isIso_f
-/
lemma isIso_toCycles (hS : S.Exact) [Mono S.f] [S.HasLeftHomology] :
    IsIso S.toCycles :=
  hS.isIso_f' _

/--
lemma `isIso_g'` / 引理 `isIso_g'`

English:
lemma isIso_g'
  given: (hS : S.Exact) (h : S.RightHomologyData) [Epi S.g]
  proof: by
  have := hS.mono_g' h
  have := epi_of_epi_fac h.p_g'
  exact isIso_of_mono_of_epi h.g'

中文:
引理 isIso_g'
  条件: (hS : S.正合) (h : S.RightHomologyData) [满态射 S.g]
  证明: by
  have := hS.mono_g' h
  have := epi_of_epi_fac h.p_g'
  exact isIso_of_mono_of_epi h.g'

Depends on / 依赖: epi_of_epi_fac, h.p_g, hS.mono_g, isIso_of_mono_of_epi, mono_g
-/
lemma isIso_g' (hS : S.Exact) (h : S.RightHomologyData) [Epi S.g] :
    IsIso h.g' := by
  have := hS.mono_g' h
  have := epi_of_epi_fac h.p_g'
  exact isIso_of_mono_of_epi h.g'

/--
lemma `isIso_fromOpcycles` / 引理 `isIso_fromOpcycles`

English:
lemma isIso_fromOpcycles
  given: (hS : S.Exact) [Epi S.g] [S.HasRightHomology]
  proof: hS.isIso_g' _

中文:
引理 isIso_fromOpcycles
  条件: (hS : S.正合) [满态射 S.g] [S.有RightHomology]
  证明: hS.isIso_g' _

Depends on / 依赖: hS.isIso_g, isIso_g
-/
lemma isIso_fromOpcycles (hS : S.Exact) [Epi S.g] [S.HasRightHomology] :
    IsIso S.fromOpcycles :=
  hS.isIso_g' _

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `fIsKernel` / `fIsKernel` 的定义

English:
definition fIsKernel
  signature: (hS : S.Exact) [Mono S.f]
  body: by
  have := hS.hasHomology
  have := hS.isIso_toCycles
  exact IsLimit.ofIsoLimit S.cyclesIsKernel
    (Fork.ext (asIso S.toCycles).symm (by simp))

中文:
定义 fIsKernel
  签名: (hS : S.正合) [单态射 S.f]
  定义体: by
  have := hS.hasHomology
  have := hS.isIso_toCycles
  exact IsLimit.ofIsoLimit S.cyclesIsKernel
    (Fork.ext (asIso S.toCycles).symm (by simp))

Depends on / 依赖: Fork.ext, IsLimit, IsLimit.ofIsoLimit, S.cyclesIsKernel, S.toCycles, cyclesIsKernel, hS.hasHomology, hS.isIso_toCycles, hasHomology, isIso_toCycles, ofIsoLimit, toCycles
-/
noncomputable def fIsKernel (hS : S.Exact) [Mono S.f] : IsLimit (KernelFork.ofι S.f S.zero) := by
  have := hS.hasHomology
  have := hS.isIso_toCycles
  exact IsLimit.ofIsoLimit S.cyclesIsKernel
    (Fork.ext (asIso S.toCycles).symm (by simp))

/--
lemma `map_of_mono_of_preservesKernel` / 引理 `map_of_mono_of_preservesKernel`

English:
lemma map_of_mono_of_preservesKernel
  statement: (hS : S.Exact) (F : C ⥤ D)
  proof: exact_of_f_is_kernel _ (KernelFork.mapIsLimit _ hS.fIsKernel F)

中文:
引理 map_of_mono_of_preservesKernel
  结论: (hS : S.正合) (F : C ⥤ D)
  证明: exact_of_f_is_kernel _ (KernelFork.mapIsLimit _ hS.fIsKernel F)

Depends on / 依赖: KernelFork, KernelFork.mapIsLimit, exact_of_f_is_kernel, fIsKernel, hS.fIsKernel, mapIsLimit
-/
lemma map_of_mono_of_preservesKernel (hS : S.Exact) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [(S.map F).HasHomology] (_ : Mono S.f)
    (_ : PreservesLimit (parallelPair S.g 0) F) :
    (S.map F).Exact :=
  exact_of_f_is_kernel _ (KernelFork.mapIsLimit _ hS.fIsKernel F)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `gIsCokernel` / `gIsCokernel` 的定义

English:
definition gIsCokernel
  signature: (hS : S.Exact) [Epi S.g]
  body: by
  have := hS.hasHomology
  have := hS.isIso_fromOpcycles
  exact IsColimit.ofIsoColimit S.opcyclesIsCokernel
    (Cofork.ext (asIso S.fromOpcycles) (by simp))

中文:
定义 gIsCokernel
  签名: (hS : S.正合) [满态射 S.g]
  定义体: by
  have := hS.hasHomology
  have := hS.isIso_fromOpcycles
  exact IsColimit.ofIsoColimit S.opcyclesIsCokernel
    (Cofork.ext (asIso S.fromOpcycles) (by simp))

Depends on / 依赖: Cofork, Cofork.ext, IsColimit, IsColimit.ofIsoColimit, S.fromOpcycles, S.opcyclesIsCokernel, fromOpcycles, hS.hasHomology, hS.isIso_fromOpcycles, hasHomology, isIso_fromOpcycles, ofIsoColimit, opcyclesIsCokernel
-/
noncomputable def gIsCokernel (hS : S.Exact) [Epi S.g] :
    IsColimit (CokernelCofork.ofπ S.g S.zero) := by
  have := hS.hasHomology
  have := hS.isIso_fromOpcycles
  exact IsColimit.ofIsoColimit S.opcyclesIsCokernel
    (Cofork.ext (asIso S.fromOpcycles) (by simp))

/--
lemma `map_of_epi_of_preservesCokernel` / 引理 `map_of_epi_of_preservesCokernel`

English:
lemma map_of_epi_of_preservesCokernel
  statement: (hS : S.Exact) (F : C ⥤ D)
  proof: exact_of_g_is_cokernel _ (CokernelCofork.mapIsColimit _ hS.gIsCokernel F)

中文:
引理 map_of_epi_of_preservesCokernel
  结论: (hS : S.正合) (F : C ⥤ D)
  证明: exact_of_g_is_cokernel _ (CokernelCofork.mapIsColimit _ hS.gIsCokernel F)

Depends on / 依赖: CokernelCofork, CokernelCofork.mapIsColimit, exact_of_g_is_cokernel, gIsCokernel, hS.gIsCokernel, mapIsColimit
-/
lemma map_of_epi_of_preservesCokernel (hS : S.Exact) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [(S.map F).HasHomology] (_ : Epi S.g)
    (_ : PreservesColimit (parallelPair S.f 0) F) :
    (S.map F).Exact :=
  exact_of_g_is_cokernel _ (CokernelCofork.mapIsColimit _ hS.gIsCokernel F)

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (hS : S.Exact) {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) [Mono S.f]
  body: hS.fIsKernel.lift (KernelFork.ofι k hk)

@[reassoc (attr := simp)]

中文:
定义 lift
  签名: (hS : S.正合) {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) [单态射 S.f]
  定义体: hS.fIsKernel.lift (KernelFork.ofι k hk)

@[reassoc (attr := simp)]

Depends on / 依赖: KernelFork, KernelFork.of, fIsKernel, hS.fIsKernel.lift
-/
noncomputable def lift (hS : S.Exact) {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) [Mono S.f] :
    A ⟶ S.X₁ := hS.fIsKernel.lift (KernelFork.ofι k hk)

@[reassoc (attr := simp)]
/--
lemma `lift_f` / 引理 `lift_f`

English:
lemma lift_f
  given: (hS : S.Exact) {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) [Mono S.f]
  proof: Fork.IsLimit.lift_ι _

中文:
引理 lift_f
  条件: (hS : S.正合) {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) [单态射 S.f]
  证明: Fork.IsLimit.lift_ι _

Depends on / 依赖: Fork.IsLimit.lift_, IsLimit
-/
lemma lift_f (hS : S.Exact) {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) [Mono S.f] :
    hS.lift k hk ≫ S.f = k :=
  Fork.IsLimit.lift_ι _

/--
lemma `lift'` / 引理 `lift'`

English:
lemma lift'
  given: (hS : S.Exact) {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) [Mono S.f]
  proof: ⟨hS.lift k hk, by simp⟩

中文:
引理 lift'
  条件: (hS : S.正合) {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) [单态射 S.f]
  证明: ⟨hS.lift k hk, by simp⟩

Depends on / 依赖: hS.lift
-/
lemma lift' (hS : S.Exact) {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) [Mono S.f] :
    exists (l : A ⟶ S.X₁), l ≫ S.f = k :=
  ⟨hS.lift k hk, by simp⟩

/--
Definition of `desc` / `desc` 的定义

English:
definition desc
  signature: (hS : S.Exact) {A : C} (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [Epi S.g]
  body: hS.gIsCokernel.desc (CokernelCofork.ofπ k hk)

@[reassoc (attr := simp)]

中文:
定义 desc
  签名: (hS : S.正合) {A : C} (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [满态射 S.g]
  定义体: hS.gIsCokernel.desc (CokernelCofork.ofπ k hk)

@[reassoc (attr := simp)]

Depends on / 依赖: CokernelCofork, CokernelCofork.of, gIsCokernel, hS.gIsCokernel.desc
-/
noncomputable def desc (hS : S.Exact) {A : C} (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [Epi S.g] :
    S.X₃ ⟶ A := hS.gIsCokernel.desc (CokernelCofork.ofπ k hk)

@[reassoc (attr := simp)]
/--
lemma `g_desc` / 引理 `g_desc`

English:
lemma g_desc
  given: (hS : S.Exact) {A : C} (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [Epi S.g]
  proof: Cofork.IsColimit.π_desc (hS.gIsCokernel)

中文:
引理 g_desc
  条件: (hS : S.正合) {A : C} (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [满态射 S.g]
  证明: Cofork.IsColimit.π_desc (hS.gIsCokernel)

Depends on / 依赖: Cofork, Cofork.IsColimit, IsColimit, gIsCokernel, hS.gIsCokernel
-/
lemma g_desc (hS : S.Exact) {A : C} (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [Epi S.g] :
    S.g ≫ hS.desc k hk = k :=
  Cofork.IsColimit.π_desc (hS.gIsCokernel)

/--
lemma `desc'` / 引理 `desc'`

English:
lemma desc'
  given: (hS : S.Exact) {A : C} (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [Epi S.g]
  proof: ⟨hS.desc k hk, by simp⟩

中文:
引理 desc'
  条件: (hS : S.正合) {A : C} (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [满态射 S.g]
  证明: ⟨hS.desc k hk, by simp⟩

Depends on / 依赖: hS.desc
-/
lemma desc' (hS : S.Exact) {A : C} (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [Epi S.g] :
    exists (l : S.X₃ ⟶ A), S.g ≫ l = k :=
  ⟨hS.desc k hk, by simp⟩

end Exact

/--
lemma `mono_τ₂_of_exact_of_mono` / 引理 `mono_τ₂_of_exact_of_mono`

English:
lemma mono_τ₂_of_exact_of_mono
  statement: {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
  proof: by
  rw [mono_iff_cancel_zero]
  intro A x₂ hx₂
  obtain ⟨x₁, hx₁⟩ : exists x₁, x₁ ≫ S₁.f = x₂ := ⟨_, h₁.lift_f x₂
    (by simp only [← cancel_mono φ.τ₃, assoc, zero_comp, ← φ.comm₂₃, reassoc_of% hx₂])⟩
  suffices x₁ = 0 by rw [← hx₁, this, zero_comp]
  simp only [← cancel_mono φ.τ₁, ← cancel_mono S₂.f, assoc, φ.comm₁₂, zero_comp,
    reassoc_of% hx₁, hx₂]

中文:
引理 mono_τ₂_of_exact_of_mono
  结论: {S₁ S₂ : 短复形 C} (φ : S₁ ⟶ S₂)
  证明: by
  rw [mono_iff_cancel_zero]
  intro A x₂ hx₂
  obtain ⟨x₁, hx₁⟩ : exists x₁, x₁ ≫ S₁.f = x₂ := ⟨_, h₁.lift_f x₂
    (by simp only [← cancel_mono φ.τ₃, assoc, zero_comp, ← φ.comm₂₃, reassoc_of% hx₂])⟩
  suffices x₁ = 0 by rw [← hx₁, this, zero_comp]
  simp only [← cancel_mono φ.τ₁, ← cancel_mono S₂.f, assoc, φ.comm₁₂, zero_comp,
    reassoc_of% hx₁, hx₂]

Depends on / 依赖: cancel_mono, lift_f, mono_iff_cancel_zero, reassoc_of, zero_comp
-/
lemma mono_τ₂_of_exact_of_mono {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (h₁ : S₁.Exact) [Mono S₁.f] [Mono S₂.f] [Mono φ.τ₁] [Mono φ.τ₃] : Mono φ.τ₂ := by
  rw [mono_iff_cancel_zero]
  intro A x₂ hx₂
  obtain ⟨x₁, hx₁⟩ : exists x₁, x₁ ≫ S₁.f = x₂ := ⟨_, h₁.lift_f x₂
    (by simp only [← cancel_mono φ.τ₃, assoc, zero_comp, ← φ.comm₂₃, reassoc_of% hx₂])⟩
  suffices x₁ = 0 by rw [← hx₁, this, zero_comp]
  simp only [← cancel_mono φ.τ₁, ← cancel_mono S₂.f, assoc, φ.comm₁₂, zero_comp,
    reassoc_of% hx₁, hx₂]

attribute [local instance] balanced_opposite

set_option backward.defeqAttrib.useBackward true in
/--
lemma `epi_τ₂_of_exact_of_epi` / 引理 `epi_τ₂_of_exact_of_epi`

English:
lemma epi_τ₂_of_exact_of_epi
  statement: {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
  proof: by
  have : Mono S₁.op.f := by dsimp; infer_instance
  have : Mono S₂.op.f := by dsimp; infer_instance
  have : Mono (opMap φ).τ₁ := by dsimp; infer_instance
  have : Mono (opMap φ).τ₃ := by dsimp; infer_instance
  have := mono_τ₂_of_exact_of_mono (opMap φ) h₂.op
  exact unop_epi_of_mono (opMap φ).τ₂

中文:
引理 epi_τ₂_of_exact_of_epi
  结论: {S₁ S₂ : 短复形 C} (φ : S₁ ⟶ S₂)
  证明: by
  have : Mono S₁.op.f := by dsimp; infer_instance
  have : Mono S₂.op.f := by dsimp; infer_instance
  have : Mono (opMap φ).τ₁ := by dsimp; infer_instance
  have : Mono (opMap φ).τ₃ := by dsimp; infer_instance
  have := mono_τ₂_of_exact_of_mono (opMap φ) h₂.op
  exact unop_epi_of_mono (opMap φ).τ₂

Depends on / 依赖: infer_instance, op.f, unop_epi_of_mono
-/
lemma epi_τ₂_of_exact_of_epi {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (h₂ : S₂.Exact) [Epi S₁.g] [Epi S₂.g] [Epi φ.τ₁] [Epi φ.τ₃] : Epi φ.τ₂ := by
  have : Mono S₁.op.f := by dsimp; infer_instance
  have : Mono S₂.op.f := by dsimp; infer_instance
  have : Mono (opMap φ).τ₁ := by dsimp; infer_instance
  have : Mono (opMap φ).τ₃ := by dsimp; infer_instance
  have := mono_τ₂_of_exact_of_mono (opMap φ) h₂.op
  exact unop_epi_of_mono (opMap φ).τ₂

variable (S)

/--
lemma `exact_and_mono_f_iff_f_is_kernel` / 引理 `exact_and_mono_f_iff_f_is_kernel`

English:
lemma exact_and_mono_f_iff_f_is_kernel
  given: [S.HasHomology]
  proof: by
  constructor
  · intro ⟨hS, _⟩
    exact ⟨hS.fIsKernel⟩
  · intro ⟨hS⟩
    exact ⟨S.exact_of_f_is_kernel hS, mono_of_isLimit_fork hS⟩

中文:
引理 exact_and_mono_f_iff_f_is_kernel
  条件: [S.有同调]
  证明: by
  constructor
  · intro ⟨hS, _⟩
    exact ⟨hS.fIsKernel⟩
  · intro ⟨hS⟩
    exact ⟨S.exact_of_f_is_kernel hS, mono_of_isLimit_fork hS⟩

Depends on / 依赖: S.exact_of_f_is_kernel, exact_of_f_is_kernel, fIsKernel, hS.fIsKernel, mono_of_isLimit_fork
-/
lemma exact_and_mono_f_iff_f_is_kernel [S.HasHomology] :
    S.Exact ∧ Mono S.f ↔ Nonempty (IsLimit (KernelFork.ofι S.f S.zero)) := by
  constructor
  · intro ⟨hS, _⟩
    exact ⟨hS.fIsKernel⟩
  · intro ⟨hS⟩
    exact ⟨S.exact_of_f_is_kernel hS, mono_of_isLimit_fork hS⟩

/--
lemma `exact_and_epi_g_iff_g_is_cokernel` / 引理 `exact_and_epi_g_iff_g_is_cokernel`

English:
lemma exact_and_epi_g_iff_g_is_cokernel
  given: [S.HasHomology]
  proof: by
  constructor
  · intro ⟨hS, _⟩
    exact ⟨hS.gIsCokernel⟩
  · intro ⟨hS⟩
    exact ⟨S.exact_of_g_is_cokernel hS, epi_of_isColimit_cofork hS⟩

中文:
引理 exact_and_epi_g_iff_g_is_cokernel
  条件: [S.有同调]
  证明: by
  constructor
  · intro ⟨hS, _⟩
    exact ⟨hS.gIsCokernel⟩
  · intro ⟨hS⟩
    exact ⟨S.exact_of_g_is_cokernel hS, epi_of_isColimit_cofork hS⟩

Depends on / 依赖: S.exact_of_g_is_cokernel, epi_of_isColimit_cofork, exact_of_g_is_cokernel, gIsCokernel, hS.gIsCokernel
-/
lemma exact_and_epi_g_iff_g_is_cokernel [S.HasHomology] :
    S.Exact ∧ Epi S.g ↔ Nonempty (IsColimit (CokernelCofork.ofπ S.g S.zero)) := by
  constructor
  · intro ⟨hS, _⟩
    exact ⟨hS.gIsCokernel⟩
  · intro ⟨hS⟩
    exact ⟨S.exact_of_g_is_cokernel hS, epi_of_isColimit_cofork hS⟩

end Balanced

end Preadditive

section Abelian

variable [Abelian C]

section

variable {X Y : C} (f : X ⟶ Y)

/-- The exact short complex `kernel f ⟶ X ⟶ Y` for any morphism `f : X ⟶ Y`. -/
@[simps]
/--
Definition of `kernelSequence` / `kernelSequence` 的定义

English:
definition kernelSequence
  signature: : ShortComplex C
  body: ShortComplex.mk _ _ (kernel.condition f)

中文:
定义 kernelSequence
  签名: : 短复形 C
  定义体: ShortComplex.mk _ _ (kernel.condition f)

Depends on / 依赖: ShortComplex, ShortComplex.mk, condition, kernel, kernel.condition
-/
noncomputable def kernelSequence : ShortComplex C :=
  ShortComplex.mk _ _ (kernel.condition f)

/-- The exact short complex `X ⟶ Y ⟶ cokernel f` for any morphism `f : X ⟶ Y`. -/
@[simps]
/--
Definition of `cokernelSequence` / `cokernelSequence` 的定义

English:
definition cokernelSequence
  signature: : ShortComplex C
  body: ShortComplex.mk _ _ (cokernel.condition f)

中文:
定义 cokernelSequence
  签名: : 短复形 C
  定义体: ShortComplex.mk _ _ (cokernel.condition f)

Depends on / 依赖: ShortComplex, ShortComplex.mk, cokernel, cokernel.condition, condition
-/
noncomputable def cokernelSequence : ShortComplex C :=
  ShortComplex.mk _ _ (cokernel.condition f)

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono (kernelSequence f).f
  body: by
  dsimp
  infer_instance

中文:
实例 :
  签名: 单态射 (kernelSequence f).f
  定义体: by
  dsimp
  infer_instance

Depends on / 依赖: infer_instance
-/
instance : Mono (kernelSequence f).f := by
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi (cokernelSequence f).g
  body: by
  dsimp
  infer_instance

中文:
实例 :
  签名: 满态射 (cokernelSequence f).g
  定义体: by
  dsimp
  infer_instance

Depends on / 依赖: infer_instance
-/
instance : Epi (cokernelSequence f).g := by
  dsimp
  infer_instance

/--
lemma `kernelSequence_exact` / 引理 `kernelSequence_exact`

English:
lemma kernelSequence_exact
  statement: (kernelSequence f).Exact
  proof: exact_of_f_is_kernel _ (kernelIsKernel f)

中文:
引理 kernelSequence_exact
  结论: (kernelSequence f).正合
  证明: exact_of_f_is_kernel _ (kernelIsKernel f)

Depends on / 依赖: exact_of_f_is_kernel, kernelIsKernel
-/
lemma kernelSequence_exact : (kernelSequence f).Exact :=
  exact_of_f_is_kernel _ (kernelIsKernel f)

/--
lemma `cokernelSequence_exact` / 引理 `cokernelSequence_exact`

English:
lemma cokernelSequence_exact
  statement: (cokernelSequence f).Exact
  proof: exact_of_g_is_cokernel _ (cokernelIsCokernel f)

中文:
引理 cokernelSequence_exact
  结论: (cokernelSequence f).正合
  证明: exact_of_g_is_cokernel _ (cokernelIsCokernel f)

Depends on / 依赖: cokernelIsCokernel, exact_of_g_is_cokernel
-/
lemma cokernelSequence_exact : (cokernelSequence f).Exact :=
  exact_of_g_is_cokernel _ (cokernelIsCokernel f)

end

set_option backward.defeqAttrib.useBackward true in
/--
lemma `quasiIso_iff_of_zeros` / 引理 `quasiIso_iff_of_zeros`

English:
lemma quasiIso_iff_of_zeros
  statement: {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
  proof: by
  have w : φ.τ₂ ≫ S₂.g = 0 := by rw [φ.comm₂₃, hg₁, zero_comp]
  rw [quasiIso_iff_isIso_liftCycles φ hf₁ hg₁ hf₂]
  constructor
  · intro h
    have : Mono φ.τ₂ := by
      rw [← S₂.liftCycles_i φ.τ₂ w]
      apply mono_comp
    refine ⟨?_, this⟩
    apply exact_of_f_is_kernel
    exact IsLimit.ofIsoLimit S₂.cyclesIsKernel
      (Fork.ext (asIso (S₂.liftCycles φ.τ₂ w)).symm (by simp))
  · rintro ⟨h₁, h₂⟩
    refine ⟨⟨h₁.lift S₂.iCycles (by simp), ?_, ?_⟩⟩
    · rw [← cancel_mono φ.τ₂, assoc, h₁.lift_f, liftCycles_i, id_comp]
    · rw [← cancel_mono S₂.iCycles, assoc, liftCycles_i, h₁.lift_f, id_comp]

中文:
引理 quasiIso_iff_of_zeros
  结论: {S₁ S₂ : 短复形 C} (φ : S₁ ⟶ S₂)
  证明: by
  have w : φ.τ₂ ≫ S₂.g = 0 := by rw [φ.comm₂₃, hg₁, zero_comp]
  rw [quasiIso_iff_isIso_liftCycles φ hf₁ hg₁ hf₂]
  constructor
  · intro h
    have : Mono φ.τ₂ := by
      rw [← S₂.liftCycles_i φ.τ₂ w]
      apply mono_comp
    refine ⟨?_, this⟩
    apply exact_of_f_is_kernel
    exact IsLimit.ofIsoLimit S₂.cyclesIsKernel
      (Fork.ext (asIso (S₂.liftCycles φ.τ₂ w)).symm (by simp))
  · rintro ⟨h₁, h₂⟩
    refine ⟨⟨h₁.lift S₂.iCycles (by simp), ?_, ?_⟩⟩
    · rw [← cancel_mono φ.τ₂, assoc, h₁.lift_f, liftCycles_i, id_comp]
    · rw [← cancel_mono S₂.iCycles, assoc, liftCycles_i, h₁.lift_f, id_comp]

Depends on / 依赖: Fork.ext, IsLimit, IsLimit.ofIsoLimit, cancel_mon, cancel_mono, cyclesIsKernel, exact_of_f_is_kernel, iCycles, id_comp, liftCycles, liftCycles_i, lift_f, mono_comp, ofIsoLimit, quasiIso_iff_isIso_liftCycles, zero_comp
-/
lemma quasiIso_iff_of_zeros {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (hf₁ : S₁.f = 0) (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) :
    QuasiIso φ ↔
      (ShortComplex.mk φ.τ₂ S₂.g (by rw [φ.comm₂₃, hg₁, zero_comp])).Exact ∧ Mono φ.τ₂ := by
  have w : φ.τ₂ ≫ S₂.g = 0 := by rw [φ.comm₂₃, hg₁, zero_comp]
  rw [quasiIso_iff_isIso_liftCycles φ hf₁ hg₁ hf₂]
  constructor
  · intro h
    have : Mono φ.τ₂ := by
      rw [← S₂.liftCycles_i φ.τ₂ w]
      apply mono_comp
    refine ⟨?_, this⟩
    apply exact_of_f_is_kernel
    exact IsLimit.ofIsoLimit S₂.cyclesIsKernel
      (Fork.ext (asIso (S₂.liftCycles φ.τ₂ w)).symm (by simp))
  · rintro ⟨h₁, h₂⟩
    refine ⟨⟨h₁.lift S₂.iCycles (by simp), ?_, ?_⟩⟩
    · rw [← cancel_mono φ.τ₂, assoc, h₁.lift_f, liftCycles_i, id_comp]
    · rw [← cancel_mono S₂.iCycles, assoc, liftCycles_i, h₁.lift_f, id_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `quasiIso_iff_of_zeros'` / 引理 `quasiIso_iff_of_zeros'`

English:
lemma quasiIso_iff_of_zeros'
  statement: {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
  proof: by
  rw [← quasiIso_opMap_iff]; rw [quasiIso_iff_of_zeros]
  rotate_left
  · dsimp
    rw [hg₂]; rw [op_zero]
  · dsimp
    rw [hf₂]; rw [op_zero]
  · dsimp
    rw [hg₁]; rw [op_zero]
  rw [← exact_unop_iff]
  have : Mono φ.τ₂.op ↔ Epi φ.τ₂ :=
    ⟨fun _ => unop_epi_of_mono φ.τ₂.op, fun _ => op_mono_of_epi _⟩
  tauto

中文:
引理 quasiIso_iff_of_zeros'
  结论: {S₁ S₂ : 短复形 C} (φ : S₁ ⟶ S₂)
  证明: by
  rw [← quasiIso_opMap_iff]; rw [quasiIso_iff_of_zeros]
  rotate_left
  · dsimp
    rw [hg₂]; rw [op_zero]
  · dsimp
    rw [hf₂]; rw [op_zero]
  · dsimp
    rw [hg₁]; rw [op_zero]
  rw [← exact_unop_iff]
  have : Mono φ.τ₂.op ↔ Epi φ.τ₂ :=
    ⟨fun _ => unop_epi_of_mono φ.τ₂.op, fun _ => op_mono_of_epi _⟩
  tauto

Depends on / 依赖: exact_unop_iff, op_mono_of_epi, op_zero, quasiIso_iff_of_zeros, quasiIso_opMap_iff, rotate_left, unop_epi_of_mono
-/
lemma quasiIso_iff_of_zeros' {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) (hg₂ : S₂.g = 0) :
    QuasiIso φ ↔
      (ShortComplex.mk S₁.f φ.τ₂ (by rw [← φ.comm₁₂, hf₂, comp_zero])).Exact ∧ Epi φ.τ₂ := by
  rw [← quasiIso_opMap_iff]; rw [quasiIso_iff_of_zeros]
  rotate_left
  · dsimp
    rw [hg₂]; rw [op_zero]
  · dsimp
    rw [hf₂]; rw [op_zero]
  · dsimp
    rw [hg₁]; rw [op_zero]
  rw [← exact_unop_iff]
  have : Mono φ.τ₂.op ↔ Epi φ.τ₂ :=
    ⟨fun _ => unop_epi_of_mono φ.τ₂.op, fun _ => op_mono_of_epi _⟩
  tauto

variable {S : ShortComplex C}

/--
Definition of `Exact.descToInjective` / `Exact.descToInjective` 的定义

English:
definition Exact.descToInjective
  body: by
  have := hS.mono_fromOpcycles
  exact Injective.factorThru (S.descOpcycles f hf) S.fromOpcycles

@[reassoc (attr := simp, nolint unusedHavesSuffices)]

中文:
定义 正合.descToInjective
  定义体: by
  have := hS.mono_fromOpcycles
  exact Injective.factorThru (S.descOpcycles f hf) S.fromOpcycles

@[reassoc (attr := simp, nolint unusedHavesSuffices)]

Depends on / 依赖: Injective, Injective.factorThru, S.descOpcycles, S.fromOpcycles, descOpcycles, factorThru, fromOpcycles, hS.mono_fromOpcycles, mono_fromOpcycles
-/
noncomputable def Exact.descToInjective
    (hS : S.Exact) {J : C} (f : S.X₂ ⟶ J) [Injective J] (hf : S.f ≫ f = 0) :
    S.X₃ ⟶ J := by
  have := hS.mono_fromOpcycles
  exact Injective.factorThru (S.descOpcycles f hf) S.fromOpcycles

@[reassoc (attr := simp, nolint unusedHavesSuffices)]
/--
lemma `Exact.comp_descToInjective` / 引理 `Exact.comp_descToInjective`

English:
lemma Exact.comp_descToInjective
  proof: by
  dsimp [descToInjective]
  simp only [← p_fromOpcycles, assoc, Injective.comp_factorThru, p_descOpcycles]

中文:
引理 正合.comp_descToInjective
  证明: by
  dsimp [descToInjective]
  simp only [← p_fromOpcycles, assoc, Injective.comp_factorThru, p_descOpcycles]

Depends on / 依赖: Injective, Injective.comp_factorThru, comp_factorThru, descToInjective, p_descOpcycles, p_fromOpcycles
-/
lemma Exact.comp_descToInjective
    (hS : S.Exact) {J : C} (f : S.X₂ ⟶ J) [Injective J] (hf : S.f ≫ f = 0) :
    S.g ≫ hS.descToInjective f hf = f := by
  dsimp [descToInjective]
  simp only [← p_fromOpcycles, assoc, Injective.comp_factorThru, p_descOpcycles]

/--
Definition of `Exact.liftFromProjective` / `Exact.liftFromProjective` 的定义

English:
definition Exact.liftFromProjective
  body: by
  have := hS.epi_toCycles
  exact Projective.factorThru (S.liftCycles f hf) S.toCycles

@[reassoc (attr := simp, nolint unusedHavesSuffices)]

中文:
定义 正合.liftFromProjective
  定义体: by
  have := hS.epi_toCycles
  exact Projective.factorThru (S.liftCycles f hf) S.toCycles

@[reassoc (attr := simp, nolint unusedHavesSuffices)]

Depends on / 依赖: Projective, Projective.factorThru, S.liftCycles, S.toCycles, X.epi_map, epi_map, epi_toCycles, factorThru, hS.epi_toCycles, liftCycles, toCycles
-/
noncomputable def Exact.liftFromProjective
    (hS : S.Exact) {P : C} (f : P ⟶ S.X₂) [Projective P] (hf : f ≫ S.g = 0) :
    P ⟶ S.X₁ := by
  have := hS.epi_toCycles
  exact Projective.factorThru (S.liftCycles f hf) S.toCycles

@[reassoc (attr := simp, nolint unusedHavesSuffices)]
/--
lemma `Exact.liftFromProjective_comp` / 引理 `Exact.liftFromProjective_comp`

English:
lemma Exact.liftFromProjective_comp
  proof: by
  dsimp [liftFromProjective]
  rw [← toCycles_i]; rw [Projective.factorThru_comp_assoc]; rw [liftCycles_i]

中文:
引理 正合.liftFromProjective_comp
  证明: by
  dsimp [liftFromProjective]
  rw [← toCycles_i]; rw [Projective.factorThru_comp_assoc]; rw [liftCycles_i]

Depends on / 依赖: Projective, Projective.factorThru_comp_assoc, factorThru_comp_assoc, liftCycles_i, liftFromProjective, toCycles_i
-/
lemma Exact.liftFromProjective_comp
    (hS : S.Exact) {P : C} (f : P ⟶ S.X₂) [Projective P] (hf : f ≫ S.g = 0) :
    hS.liftFromProjective f hf ≫ S.f = f := by
  dsimp [liftFromProjective]
  rw [← toCycles_i]; rw [Projective.factorThru_comp_assoc]; rw [liftCycles_i]


end Abelian

end ShortComplex

namespace Functor

variable (F : C ⥤ D) [Preadditive C] [Preadditive D] [HasZeroObject C]
  [HasZeroObject D] [F.PreservesZeroMorphisms] [F.PreservesHomology]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: F.PreservesMonomorphisms
  body: by
    let S := ShortComplex.mk (0 : X ⟶ X) f zero_comp
    exact ((S.map F).exact_iff_mono (by simp [S])).1
      (((S.exact_iff_mono rfl).2 hf).map F)

中文:
实例 :
  签名: F.保持Monomorphisms
  定义体: by
    let S := ShortComplex.mk (0 : X ⟶ X) f zero_comp
    exact ((S.map F).exact_iff_mono (by simp [S])).1
      (((S.exact_iff_mono rfl).2 hf).map F)

Depends on / 依赖: S.exact_iff_mono, S.map, ShortComplex, ShortComplex.mk, exact_iff_mono, zero_comp
-/
instance : F.PreservesMonomorphisms where
  preserves {X Y} f hf := by
    let S := ShortComplex.mk (0 : X ⟶ X) f zero_comp
    exact ((S.map F).exact_iff_mono (by simp [S])).1
      (((S.exact_iff_mono rfl).2 hf).map F)


set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: F.PreservesEpimorphisms
  body: by
    let S := ShortComplex.mk f (0 : Y ⟶ Y) comp_zero
    exact ((S.map F).exact_iff_epi (by simp [S])).1
      (((S.exact_iff_epi rfl).2 hf).map F)

中文:
实例 :
  签名: F.保持Epimorphisms
  定义体: by
    let S := ShortComplex.mk f (0 : Y ⟶ Y) comp_zero
    exact ((S.map F).exact_iff_epi (by simp [S])).1
      (((S.exact_iff_epi rfl).2 hf).map F)

Depends on / 依赖: S.exact_iff_epi, S.map, ShortComplex, ShortComplex.mk, comp_zero, exact_iff_epi
-/
instance : F.PreservesEpimorphisms where
  preserves {X Y} f hf := by
    let S := ShortComplex.mk f (0 : Y ⟶ Y) comp_zero
    exact ((S.map F).exact_iff_epi (by simp [S])).1
      (((S.exact_iff_epi rfl).2 hf).map F)


end Functor

namespace ShortComplex

namespace Splitting

variable [Preadditive C] [Balanced C]

/--
Definition of `ofExactOfSection` / `ofExactOfSection` 的定义

English:
definition ofExactOfSection
  signature: (S : ShortComplex C) (hS : S.Exact) (s : S.X₃ ⟶ S.X₂)
  body: hS.lift (𝟙 S.X₂ - S.g ≫ s) (by simp [s_g])
  s := s
  f_r := by rw [← cancel_mono S.f, assoc, Exact.lift_f, comp_sub, comp_id,
    zero_assoc, zero_comp, sub_zero, id_comp]
  s_g := s_g

中文:
定义 ofExactOfSection
  签名: (S : 短复形 C) (hS : S.正合) (s : S.X₃ ⟶ S.X₂)
  定义体: hS.lift (𝟙 S.X₂ - S.g ≫ s) (by simp [s_g])
  s := s
  f_r := by rw [← cancel_mono S.f, assoc, Exact.lift_f, comp_sub, comp_id,
    zero_assoc, zero_comp, sub_zero, id_comp]
  s_g := s_g

Depends on / 依赖: X.mono_map, hS.lift, mono_map
-/
noncomputable def ofExactOfSection (S : ShortComplex C) (hS : S.Exact) (s : S.X₃ ⟶ S.X₂)
    (s_g : s ≫ S.g = 𝟙 S.X₃) (hf : Mono S.f) :
    S.Splitting where
  r := hS.lift (𝟙 S.X₂ - S.g ≫ s) (by simp [s_g])
  s := s
  f_r := by rw [← cancel_mono S.f, assoc, Exact.lift_f, comp_sub, comp_id,
    zero_assoc, zero_comp, sub_zero, id_comp]
  s_g := s_g

/--
Definition of `ofExactOfRetraction` / `ofExactOfRetraction` 的定义

English:
definition ofExactOfRetraction
  signature: (S : ShortComplex C) (hS : S.Exact) (r : S.X₂ ⟶ S.X₁)
  body: r
  s := hS.desc (𝟙 S.X₂ - r ≫ S.f) (by simp [reassoc_of% f_r])
  f_r := f_r
  s_g := by
    rw [← cancel_epi S.g]; rw [Exact.g_desc_assoc]; rw [sub_comp]; rw [id_comp]; rw [assoc]; rw [zero]; rw [comp_zero]; rw [sub_zero]; rw [comp_id]

中文:
定义 ofExactOfRetraction
  签名: (S : 短复形 C) (hS : S.正合) (r : S.X₂ ⟶ S.X₁)
  定义体: r
  s := hS.desc (𝟙 S.X₂ - r ≫ S.f) (by simp [reassoc_of% f_r])
  f_r := f_r
  s_g := by
    rw [← cancel_epi S.g]; rw [Exact.g_desc_assoc]; rw [sub_comp]; rw [id_comp]; rw [assoc]; rw [zero]; rw [comp_zero]; rw [sub_zero]; rw [comp_id]
-/
noncomputable def ofExactOfRetraction (S : ShortComplex C) (hS : S.Exact) (r : S.X₂ ⟶ S.X₁)
    (f_r : S.f ≫ r = 𝟙 S.X₁) (hg : Epi S.g) :
    S.Splitting where
  r := r
  s := hS.desc (𝟙 S.X₂ - r ≫ S.f) (by simp [reassoc_of% f_r])
  f_r := f_r
  s_g := by
    rw [← cancel_epi S.g]; rw [Exact.g_desc_assoc]; rw [sub_comp]; rw [id_comp]; rw [assoc]; rw [zero]; rw [comp_zero]; rw [sub_zero]; rw [comp_id]

end Splitting

end ShortComplex

end CategoryTheory
