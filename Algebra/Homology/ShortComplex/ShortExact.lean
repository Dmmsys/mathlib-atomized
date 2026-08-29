/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Short exact short complexes

A short complex `S : ShortComplex C` is short exact (`S.ShortExact`) when it is exact,
`S.f` is a mono and `S.g` is an epi.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits ZeroObject

variable {C D : Type*} [Category* C] [Category* D]

namespace ShortComplex

section

variable [HasZeroMorphisms C] [HasZeroMorphisms D]
  (S : ShortComplex C) {S₁ S₂ : ShortComplex C}

/--
Definition of `ShortExact` / `ShortExact` 的定义

English:
structure ShortExact
  parameters: : Prop where
  axioms and operations (3):
    - exact : S.Exact
    - [mono_f : Mono S.f]
    - [epi_g : Epi S.g]

中文:
结构 短正合
  参数: : 命题 where
  公理与运算 (3 个):
    - exact : S.正合
    - [mono_f : 单态射 S.f]
    - [epi_g : 满态射 S.g]
-/
structure ShortExact : Prop where
  exact : S.Exact
  [mono_f : Mono S.f]
  [epi_g : Epi S.g]

variable {S}

/--
lemma `ShortExact.mk'` / 引理 `ShortExact.mk'`

English:
lemma ShortExact.mk'
  given: (h : S.Exact) (_ : Mono S.f) (_ : Epi S.g)
  statement: S.ShortExact where
  proof: h

中文:
引理 短正合.mk'
  条件: (h : S.正合) (_ : 单态射 S.f) (_ : 满态射 S.g)
  结论: S.短正合 where
  证明: h
-/
lemma ShortExact.mk' (h : S.Exact) (_ : Mono S.f) (_ : Epi S.g) : S.ShortExact where
  exact := h

/--
lemma `shortExact_of_iso` / 引理 `shortExact_of_iso`

English:
lemma shortExact_of_iso
  given: (e : S₁ ≅ S₂) (h : S₁.ShortExact)
  statement: S₂.ShortExact where
  proof: exact_of_iso e h.exact
  mono_f := by
    suffices Mono (S₂.f ≫ e.inv.τ₂) by
      exact mono_of_mono _ e.inv.τ₂
    have := h.mono_f
    rw [← e.inv.comm₁₂]
    apply mono_comp
  epi_g := by
    suffices Epi (e.hom.τ₂ ≫ S₂.g) by
      exact epi_of_epi e.hom.τ₂ _
    have := h.epi_g
    rw [e.hom.co

中文:
引理 shortExact_of_iso
  条件: (e : S₁ ≅ S₂) (h : S₁.短正合)
  结论: S₂.短正合 where
  证明: exact_of_iso e h.exact
  mono_f := by
    suffices Mono (S₂.f ≫ e.inv.τ₂) by
      exact mono_of_mono _ e.inv.τ₂
    have := h.mono_f
    rw [← e.inv.comm₁₂]
    apply mono_comp
  epi_g := by
    suffices Epi (e.hom.τ₂ ≫ S₂.g) by
      exact epi_of_epi e.hom.τ₂ _
    have := h.epi_g
    rw [e.hom.co

Depends on / 依赖: exact_of_iso, h.exact
-/
lemma shortExact_of_iso (e : S₁ ≅ S₂) (h : S₁.ShortExact) : S₂.ShortExact where
  exact := exact_of_iso e h.exact
  mono_f := by
    suffices Mono (S₂.f ≫ e.inv.τ₂) by
      exact mono_of_mono _ e.inv.τ₂
    have := h.mono_f
    rw [← e.inv.comm₁₂]
    apply mono_comp
  epi_g := by
    suffices Epi (e.hom.τ₂ ≫ S₂.g) by
      exact epi_of_epi e.hom.τ₂ _
    have := h.epi_g
    rw [e.hom.comm₂₃]
    apply epi_comp

/--
lemma `shortExact_iff_of_iso` / 引理 `shortExact_iff_of_iso`

English:
lemma shortExact_iff_of_iso
  given: (e : S₁ ≅ S₂)
  statement: S₁.ShortExact ↔ S₂.ShortExact
  proof: by
  constructor
  · exact shortExact_of_iso e
  · exact shortExact_of_iso e.symm

中文:
引理 shortExact_iff_of_iso
  条件: (e : S₁ ≅ S₂)
  结论: S₁.短正合 ↔ S₂.短正合
  证明: by
  constructor
  · exact shortExact_of_iso e
  · exact shortExact_of_iso e.symm

Depends on / 依赖: e.symm, shortExact_of_iso
-/
lemma shortExact_iff_of_iso (e : S₁ ≅ S₂) : S₁.ShortExact ↔ S₂.ShortExact := by
  constructor
  · exact shortExact_of_iso e
  · exact shortExact_of_iso e.symm

set_option backward.defeqAttrib.useBackward true in
/--
lemma `ShortExact.op` / 引理 `ShortExact.op`

English:
lemma ShortExact.op
  given: (h : S.ShortExact)
  statement: S.op.ShortExact where
  proof: h.exact.op
  mono_f := by
    have := h.epi_g
    dsimp
    infer_instance
  epi_g := by
    have := h.mono_f
    dsimp
    infer_instance

中文:
引理 短正合.op
  条件: (h : S.短正合)
  结论: S.op.短正合 where
  证明: h.exact.op
  mono_f := by
    have := h.epi_g
    dsimp
    infer_instance
  epi_g := by
    have := h.mono_f
    dsimp
    infer_instance

Depends on / 依赖: h.exact.op
-/
lemma ShortExact.op (h : S.ShortExact) : S.op.ShortExact where
  exact := h.exact.op
  mono_f := by
    have := h.epi_g
    dsimp
    infer_instance
  epi_g := by
    have := h.mono_f
    dsimp
    infer_instance

set_option backward.defeqAttrib.useBackward true in
/--
lemma `ShortExact.unop` / 引理 `ShortExact.unop`

English:
lemma ShortExact.unop
  given: {S : ShortComplex Cᵒᵖ} (h : S.ShortExact)
  statement: S.unop.ShortExact where
  proof: h.exact.unop
  mono_f := by
    have := h.epi_g
    dsimp
    infer_instance
  epi_g := by
    have := h.mono_f
    dsimp
    infer_instance

中文:
引理 短正合.unop
  条件: {S : 短复形 Cᵒᵖ} (h : S.短正合)
  结论: S.unop.短正合 where
  证明: h.exact.unop
  mono_f := by
    have := h.epi_g
    dsimp
    infer_instance
  epi_g := by
    have := h.mono_f
    dsimp
    infer_instance

Depends on / 依赖: h.exact.unop
-/
lemma ShortExact.unop {S : ShortComplex Cᵒᵖ} (h : S.ShortExact) : S.unop.ShortExact where
  exact := h.exact.unop
  mono_f := by
    have := h.epi_g
    dsimp
    infer_instance
  epi_g := by
    have := h.mono_f
    dsimp
    infer_instance

variable (S)

/--
lemma `shortExact_iff_op` / 引理 `shortExact_iff_op`

English:
lemma shortExact_iff_op
  statement: S.ShortExact ↔ S.op.ShortExact
  proof: ⟨ShortExact.op, ShortExact.unop⟩

中文:
引理 shortExact_iff_op
  结论: S.短正合 ↔ S.op.短正合
  证明: ⟨ShortExact.op, ShortExact.unop⟩

Depends on / 依赖: ShortExact, ShortExact.op, ShortExact.unop
-/
lemma shortExact_iff_op : S.ShortExact ↔ S.op.ShortExact :=
  ⟨ShortExact.op, ShortExact.unop⟩

/--
lemma `shortExact_iff_unop` / 引理 `shortExact_iff_unop`

English:
lemma shortExact_iff_unop
  given: (S : ShortComplex Cᵒᵖ)
  statement: S.ShortExact ↔ S.unop.ShortExact
  proof: S.unop.shortExact_iff_op.symm

中文:
引理 shortExact_iff_unop
  条件: (S : 短复形 Cᵒᵖ)
  结论: S.短正合 ↔ S.unop.短正合
  证明: S.unop.shortExact_iff_op.symm

Depends on / 依赖: S.unop.shortExact_iff_op.symm, shortExact_iff_op
-/
lemma shortExact_iff_unop (S : ShortComplex Cᵒᵖ) : S.ShortExact ↔ S.unop.ShortExact :=
  S.unop.shortExact_iff_op.symm

variable {S}

/--
lemma `ShortExact.map` / 引理 `ShortExact.map`

English:
lemma ShortExact.map
  statement: (h : S.ShortExact) (F : C ⥤ D)
  proof: h.exact.map F
  mono_f := (inferInstance : Mono (F.map S.f))
  epi_g := (inferInstance : Epi (F.map S.g))

中文:
引理 短正合.map
  结论: (h : S.短正合) (F : C ⥤ D)
  证明: h.exact.map F
  mono_f := (inferInstance : Mono (F.map S.f))
  epi_g := (inferInstance : Epi (F.map S.g))

Depends on / 依赖: h.exact.map
-/
lemma ShortExact.map (h : S.ShortExact) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [F.PreservesLeftHomologyOf S]
    [F.PreservesRightHomologyOf S] [Mono (F.map S.f)] [Epi (F.map S.g)] :
    (S.map F).ShortExact where
  exact := h.exact.map F
  mono_f := (inferInstance : Mono (F.map S.f))
  epi_g := (inferInstance : Epi (F.map S.g))

/--
lemma `ShortExact.map_of_exact` / 引理 `ShortExact.map_of_exact`

English:
lemma ShortExact.map_of_exact
  statement: (hS : S.ShortExact)
  proof: by
  have := hS.mono_f
  have := hS.epi_g
  exact hS.map F

中文:
引理 短正合.map_of_exact
  结论: (hS : S.短正合)
  证明: by
  have := hS.mono_f
  have := hS.epi_g
  exact hS.map F

Depends on / 依赖: epi_g, hS.epi_g, hS.map, hS.mono_f, mono_f
-/
lemma ShortExact.map_of_exact (hS : S.ShortExact)
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] : (S.map F).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  exact hS.map F

end

section Preadditive

variable [Preadditive C]

/--
lemma `ShortExact.isIso_f_iff` / 引理 `ShortExact.isIso_f_iff`

English:
lemma ShortExact.isIso_f_iff
  given: {S : ShortComplex C} (hS : S.ShortExact) [Balanced C]
  proof: by
  have := hS.exact.hasZeroObject
  have := hS.mono_f
  have := hS.epi_g
  constructor
  · intro hf
    simp only [IsZero.iff_id_eq_zero, ← cancel_epi S.g, ← cancel_epi S.f,
      S.zero_assoc, zero_comp]
  · intro hX₃
    have : Epi S.f := (S.exact_iff_epi (hX₃.eq_of_tgt _ _)).1 hS.exact
    appl

中文:
引理 短正合.isIso_f_iff
  条件: {S : 短复形 C} (hS : S.短正合) [Balanced C]
  证明: by
  have := hS.exact.hasZeroObject
  have := hS.mono_f
  have := hS.epi_g
  constructor
  · intro hf
    simp only [IsZero.iff_id_eq_zero, ← cancel_epi S.g, ← cancel_epi S.f,
      S.zero_assoc, zero_comp]
  · intro hX₃
    have : Epi S.f := (S.exact_iff_epi (hX₃.eq_of_tgt _ _)).1 hS.exact
    appl

Depends on / 依赖: IsZero, IsZero.iff_id_eq_zero, S.exact_iff_epi, S.zero_assoc, cancel_epi, epi_g, eq_of_tgt, exact_iff_epi, hS.epi_g, hS.exact, hS.exact.hasZeroObject, hS.mono_f, hasZeroObject, iff_id_eq_zero, isIso_of_mono_of_epi, mono_f, zero_assoc, zero_comp
-/
lemma ShortExact.isIso_f_iff {S : ShortComplex C} (hS : S.ShortExact) [Balanced C] :
    IsIso S.f ↔ IsZero S.X₃ := by
  have := hS.exact.hasZeroObject
  have := hS.mono_f
  have := hS.epi_g
  constructor
  · intro hf
    simp only [IsZero.iff_id_eq_zero, ← cancel_epi S.g, ← cancel_epi S.f,
      S.zero_assoc, zero_comp]
  · intro hX₃
    have : Epi S.f := (S.exact_iff_epi (hX₃.eq_of_tgt _ _)).1 hS.exact
    apply isIso_of_mono_of_epi

/--
lemma `ShortExact.isIso_g_iff` / 引理 `ShortExact.isIso_g_iff`

English:
lemma ShortExact.isIso_g_iff
  given: {S : ShortComplex C} (hS : S.ShortExact) [Balanced C]
  proof: by
  have := hS.exact.hasZeroObject
  have := hS.mono_f
  have := hS.epi_g
  constructor
  · intro hf
    simp only [IsZero.iff_id_eq_zero, ← cancel_mono S.f, ← cancel_mono S.g,
      S.zero, zero_comp, assoc, comp_zero]
  · intro hX₁
    have : Mono S.g := (S.exact_iff_mono (hX₁.eq_of_src _ _)).1 h

中文:
引理 短正合.isIso_g_iff
  条件: {S : 短复形 C} (hS : S.短正合) [Balanced C]
  证明: by
  have := hS.exact.hasZeroObject
  have := hS.mono_f
  have := hS.epi_g
  constructor
  · intro hf
    simp only [IsZero.iff_id_eq_zero, ← cancel_mono S.f, ← cancel_mono S.g,
      S.zero, zero_comp, assoc, comp_zero]
  · intro hX₁
    have : Mono S.g := (S.exact_iff_mono (hX₁.eq_of_src _ _)).1 h

Depends on / 依赖: IsZero, IsZero.iff_id_eq_zero, S.exact_iff_mono, S.zero, cancel_mono, comp_zero, epi_g, eq_of_src, exact_iff_mono, hS.epi_g, hS.exact, hS.exact.hasZeroObject, hS.mono_f, hasZeroObject, iff_id_eq_zero, isIso_of_mono_of_epi, mono_f, zero_comp
-/
lemma ShortExact.isIso_g_iff {S : ShortComplex C} (hS : S.ShortExact) [Balanced C] :
    IsIso S.g ↔ IsZero S.X₁ := by
  have := hS.exact.hasZeroObject
  have := hS.mono_f
  have := hS.epi_g
  constructor
  · intro hf
    simp only [IsZero.iff_id_eq_zero, ← cancel_mono S.f, ← cancel_mono S.g,
      S.zero, zero_comp, assoc, comp_zero]
  · intro hX₁
    have : Mono S.g := (S.exact_iff_mono (hX₁.eq_of_src _ _)).1 hS.exact
    apply isIso_of_mono_of_epi

/--
lemma `isIso₂_of_shortExact_of_isIso₁₃` / 引理 `isIso₂_of_shortExact_of_isIso₁₃`

English:
lemma isIso₂_of_shortExact_of_isIso₁₃
  statement: [Balanced C] {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
  proof: by
  have := h₁.mono_f
  have := h₂.mono_f
  have := h₁.epi_g
  have := h₂.epi_g
  have := mono_τ₂_of_exact_of_mono φ h₁.exact
  have := epi_τ₂_of_exact_of_epi φ h₂.exact
  apply isIso_of_mono_of_epi

中文:
引理 isIso₂_of_shortExact_of_isIso₁₃
  结论: [Balanced C] {S₁ S₂ : 短复形 C} (φ : S₁ ⟶ S₂)
  证明: by
  have := h₁.mono_f
  have := h₂.mono_f
  have := h₁.epi_g
  have := h₂.epi_g
  have := mono_τ₂_of_exact_of_mono φ h₁.exact
  have := epi_τ₂_of_exact_of_epi φ h₂.exact
  apply isIso_of_mono_of_epi

Depends on / 依赖: epi_g, isIso_of_mono_of_epi, mono_f
-/
lemma isIso₂_of_shortExact_of_isIso₁₃ [Balanced C] {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) [IsIso φ.τ₁] [IsIso φ.τ₃] : IsIso φ.τ₂ := by
  have := h₁.mono_f
  have := h₂.mono_f
  have := h₁.epi_g
  have := h₂.epi_g
  have := mono_τ₂_of_exact_of_mono φ h₁.exact
  have := epi_τ₂_of_exact_of_epi φ h₂.exact
  apply isIso_of_mono_of_epi

/--
lemma `isIso₂_of_shortExact_of_isIso₁₃'` / 引理 `isIso₂_of_shortExact_of_isIso₁₃'`

English:
lemma isIso₂_of_shortExact_of_isIso₁₃'
  statement: [Balanced C] {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
  proof: isIso₂_of_shortExact_of_isIso₁₃ φ h₁ h₂

中文:
引理 isIso₂_of_shortExact_of_isIso₁₃'
  结论: [Balanced C] {S₁ S₂ : 短复形 C} (φ : S₁ ⟶ S₂)
  证明: isIso₂_of_shortExact_of_isIso₁₃ φ h₁ h₂
-/
lemma isIso₂_of_shortExact_of_isIso₁₃' [Balanced C] {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (_ : IsIso φ.τ₁) (_ : IsIso φ.τ₃) : IsIso φ.τ₂ :=
  isIso₂_of_shortExact_of_isIso₁₃ φ h₁ h₂

/--
Definition of `ShortExact.fIsKernel` / `ShortExact.fIsKernel` 的定义

English:
definition ShortExact.fIsKernel
  signature: [Balanced C] {S : ShortComplex C} (hS : S.ShortExact)
  body: by
  have := hS.mono_f
  exact hS.exact.fIsKernel

中文:
定义 短正合.fIsKernel
  签名: [Balanced C] {S : 短复形 C} (hS : S.短正合)
  定义体: by
  have := hS.mono_f
  exact hS.exact.fIsKernel

Depends on / 依赖: fIsKernel, hS.exact.fIsKernel, hS.mono_f, mono_f
-/
noncomputable def ShortExact.fIsKernel [Balanced C] {S : ShortComplex C} (hS : S.ShortExact) :
    IsLimit (KernelFork.ofι S.f S.zero) := by
  have := hS.mono_f
  exact hS.exact.fIsKernel

/--
Definition of `ShortExact.gIsCokernel` / `ShortExact.gIsCokernel` 的定义

English:
definition ShortExact.gIsCokernel
  signature: [Balanced C] {S : ShortComplex C} (hS : S.ShortExact)
  body: by
  have := hS.epi_g
  exact hS.exact.gIsCokernel

中文:
定义 短正合.gIsCokernel
  签名: [Balanced C] {S : 短复形 C} (hS : S.短正合)
  定义体: by
  have := hS.epi_g
  exact hS.exact.gIsCokernel

Depends on / 依赖: epi_g, gIsCokernel, hS.epi_g, hS.exact.gIsCokernel
-/
noncomputable def ShortExact.gIsCokernel [Balanced C] {S : ShortComplex C} (hS : S.ShortExact) :
    IsColimit (CokernelCofork.ofπ S.g S.zero) := by
  have := hS.epi_g
  exact hS.exact.gIsCokernel

/--
lemma `Exact.shortExact` / 引理 `Exact.shortExact`

English:
lemma Exact.shortExact
  given: {S : ShortComplex C} (hS : S.Exact) (h : S.HomologyData)
  proof: by
    have := hS.epi_f' h.left
    have := hS.mono_g' h.right
    let S' := ShortComplex.mk h.left.i S.g (by simp)
    let S'' := ShortComplex.mk _ _ (h.exact_iff_i_p_zero.1 hS)
    let a : S ⟶ S' :=
      { τ₁ := h.left.f'
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _ }
    let b : S'' ⟶ S' :=
      { τ₁ :=

中文:
引理 正合.shortExact
  条件: {S : 短复形 C} (hS : S.正合) (h : S.同调数据)
  证明: by
    have := hS.epi_f' h.left
    have := hS.mono_g' h.right
    let S' := ShortComplex.mk h.left.i S.g (by simp)
    let S'' := ShortComplex.mk _ _ (h.exact_iff_i_p_zero.1 hS)
    let a : S ⟶ S' :=
      { τ₁ := h.left.f'
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _ }
    let b : S'' ⟶ S' :=
      { τ₁ :=

Depends on / 依赖: ShortComplex, ShortComplex.exact_iff_of_epi_of_isIso_of_mono, ShortComplex.mk, epi_f, exact_iff_i_p_zero, exact_iff_of_epi_of_isIso_of_mono, h.exact_iff_i_p_zero, h.left, h.left.f, h.left.i, h.right, h.right.g, hS.epi_f, hS.mono_g, mono_g
-/
lemma Exact.shortExact {S : ShortComplex C} (hS : S.Exact) (h : S.HomologyData) :
    (ShortComplex.mk _ _ (h.exact_iff_i_p_zero.1 hS)).ShortExact where
  exact := by
    have := hS.epi_f' h.left
    have := hS.mono_g' h.right
    let S' := ShortComplex.mk h.left.i S.g (by simp)
    let S'' := ShortComplex.mk _ _ (h.exact_iff_i_p_zero.1 hS)
    let a : S ⟶ S' :=
      { τ₁ := h.left.f'
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _ }
    let b : S'' ⟶ S' :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := h.right.g' }
    rwa [ShortComplex.exact_iff_of_epi_of_isIso_of_mono b,
      ← ShortComplex.exact_iff_of_epi_of_isIso_of_mono a]

/--
lemma `Splitting.shortExact` / 引理 `Splitting.shortExact`

English:
lemma Splitting.shortExact
  given: {S : ShortComplex C} [HasZeroObject C] (s : S.Splitting)
  proof: s.exact
  mono_f := s.mono_f
  epi_g := s.epi_g

中文:
引理 Splitting.shortExact
  条件: {S : 短复形 C} [有ZeroObject C] (s : S.Splitting)
  证明: s.exact
  mono_f := s.mono_f
  epi_g := s.epi_g

Depends on / 依赖: s.exact
-/
lemma Splitting.shortExact {S : ShortComplex C} [HasZeroObject C] (s : S.Splitting) :
    S.ShortExact where
  exact := s.exact
  mono_f := s.mono_f
  epi_g := s.epi_g

namespace ShortExact

/--
Definition of `splittingOfInjective` / `splittingOfInjective` 的定义

English:
definition splittingOfInjective
  signature: {S : ShortComplex C} (hS : S.ShortExact)
  body: have := hS.mono_f
  Splitting.ofExactOfRetraction S hS.exact (Injective.factorThru (𝟙 S.X₁) S.f) (by simp) hS.epi_g

中文:
定义 splittingOfInjective
  签名: {S : 短复形 C} (hS : S.短正合)
  定义体: have := hS.mono_f
  Splitting.ofExactOfRetraction S hS.exact (Injective.factorThru (𝟙 S.X₁) S.f) (by simp) hS.epi_g

Depends on / 依赖: Injective, Injective.factorThru, Splitting, Splitting.ofExactOfRetraction, epi_g, factorThru, hS.epi_g, hS.exact, hS.mono_f, mono_f, ofExactOfRetraction
-/
noncomputable def splittingOfInjective {S : ShortComplex C} (hS : S.ShortExact)
    [Injective S.X₁] [Balanced C] :
    S.Splitting :=
  have := hS.mono_f
  Splitting.ofExactOfRetraction S hS.exact (Injective.factorThru (𝟙 S.X₁) S.f) (by simp) hS.epi_g

/--
Definition of `splittingOfProjective` / `splittingOfProjective` 的定义

English:
definition splittingOfProjective
  signature: {S : ShortComplex C} (hS : S.ShortExact)
  body: have := hS.epi_g
  Splitting.ofExactOfSection S hS.exact (Projective.factorThru (𝟙 S.X₃) S.g) (by simp) hS.mono_f

中文:
定义 splittingOfProjective
  签名: {S : 短复形 C} (hS : S.短正合)
  定义体: have := hS.epi_g
  Splitting.ofExactOfSection S hS.exact (Projective.factorThru (𝟙 S.X₃) S.g) (by simp) hS.mono_f

Depends on / 依赖: Projective, Projective.factorThru, Splitting, Splitting.ofExactOfSection, epi_g, factorThru, hS.epi_g, hS.exact, hS.mono_f, mono_f, ofExactOfSection
-/
noncomputable def splittingOfProjective {S : ShortComplex C} (hS : S.ShortExact)
    [Projective S.X₃] [Balanced C] :
    S.Splitting :=
  have := hS.epi_g
  Splitting.ofExactOfSection S hS.exact (Projective.factorThru (𝟙 S.X₃) S.g) (by simp) hS.mono_f

end ShortExact

end Preadditive

end ShortComplex

end CategoryTheory
