/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equalizer
public import Mathlib.Topology.QuasiSeparated
public import Mathlib.Topology.Sheaves.CommRingCat

/-!
# Quasi-separated morphisms

A morphism of schemes `f : X ⟶ Y` is quasi-separated if the diagonal morphism `X ⟶ X ×[Y] X` is
quasi-compact.

A scheme is quasi-separated if the intersections of any two affine open sets is quasi-compact.
(`AlgebraicGeometry.quasiSeparatedSpace_iff_affine`)

We show that a morphism is quasi-separated if the preimage of every affine open is quasi-separated.

We also show that this property is local at the target,
and is stable under compositions and base-changes.

## Main result
- `AlgebraicGeometry.isLocalization_basicOpen_of_qcqs` (**Qcqs lemma**):
  If `U` is qcqs, then `Γ(X, D(f)) ≃ Γ(X, U)_f` for every `f : Γ(X, U)`.

-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

open scoped AlgebraicGeometry

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism is `QuasiSeparated` if diagonal map is quasi-compact. -/
@[mk_iff]
/--
Definition of `QuasiSeparated` / `QuasiSeparated` 的定义

English:
class QuasiSeparated
  parameters: (f : X ⟶ Y)
  axioms and operations (1):
    - quasiCompact_diagonal : QuasiCompact (pullback.diagonal f)  [default: by infer_instance]

中文:
类 QuasiSeparated
  参数: (f : X ⟶ Y)
  公理与运算 (1 个):
    - quasiCompact_diagonal : QuasiCompact (pullback.diagonal f)  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class QuasiSeparated (f : X ⟶ Y) : Prop where
  /-- A morphism is `QuasiSeparated` if diagonal map is quasi-compact. -/
  quasiCompact_diagonal : QuasiCompact (pullback.diagonal f) := by infer_instance

attribute [instance] QuasiSeparated.quasiCompact_diagonal

/--
theorem `quasiSeparatedSpace_iff_forall_affineOpens` / 定理 `quasiSeparatedSpace_iff_forall_affineOpens`

English:
theorem quasiSeparatedSpace_iff_forall_affineOpens
  given: {X : Scheme}
  proof: by
  rw [quasiSeparatedSpace_iff]
  constructor
  · intro H U V; exact H U V U.1.2 U.2.isCompact V.1.2 V.2.isCompact
  · intro H
    suffices
      forall (U : X.Opens) (_ : IsCompact U.1) (V : X.Opens) (_ : IsCompact V.1),
        IsCompact (U ⊓ V).1
      by intro U V hU hU' hV hV'; exact this ⟨U,

中文:
定理 quasiSeparatedSpace_iff_forall_affineOpens
  条件: {X : Scheme}
  证明: by
  rw [quasiSeparatedSpace_iff]
  constructor
  · intro H U V; exact H U V U.1.2 U.2.isCompact V.1.2 V.2.isCompact
  · intro H
    suffices
      forall (U : X.Opens) (_ : IsCompact U.1) (V : X.Opens) (_ : IsCompact V.1),
        IsCompact (U ⊓ V).1
      by intro U V hU hU' hV hV'; exact this ⟨U,

Depends on / 依赖: IsCompact, Set.inter_union_distrib_left, X.Opens, compact_open_indu, compact_open_induction_on, hV.union, inter_union_distrib_left, isCompact, quasiSeparatedSpace_iff
-/
theorem quasiSeparatedSpace_iff_forall_affineOpens {X : Scheme} :
    QuasiSeparatedSpace X ↔ forall U V : X.affineOpens, IsCompact (U inter V : Set X) := by
  rw [quasiSeparatedSpace_iff]
  constructor
  · intro H U V; exact H U V U.1.2 U.2.isCompact V.1.2 V.2.isCompact
  · intro H
    suffices
      forall (U : X.Opens) (_ : IsCompact U.1) (V : X.Opens) (_ : IsCompact V.1),
        IsCompact (U ⊓ V).1
      by intro U V hU hU' hV hV'; exact this ⟨U, hU⟩ hU' ⟨V, hV⟩ hV'
    intro U hU V hV
    refine compact_open_induction_on V hV ?_ ?_
    · simp
    · intro S _ V hV
      change IsCompact (U.1 inter (S.1 union V.1))
      rw [Set.inter_union_distrib_left]
      apply hV.union
      clear hV
      refine compact_open_induction_on U hU ?_ ?_
      · simp
      · intro S _ W hW
        change IsCompact ((S.1 union W.1) inter V.1)
        rw [Set.union_inter_distrib_right]
        apply hW.union
        apply H

/--
theorem `quasiCompact_affineProperty_iff_quasiSeparatedSpace` / 定理 `quasiCompact_affineProperty_iff_quasiSeparatedSpace`

English:
theorem quasiCompact_affineProperty_iff_quasiSeparatedSpace
  given: [IsAffine Y] (f : X ⟶ Y)
  proof: by
  delta AffineTargetMorphismProperty.diagonal
  rw [quasiSeparatedSpace_iff_forall_affineOpens]
  constructor
  · intro H U V
    let g : pullback U.1.ι V.1.ι ⟶ X := pullback.fst _ _ ≫ U.1.ι
    have e := g.isOpenEmbedding.isEmbedding.toHomeomorph
    rw [IsOpenImmersion.range_pullback_to_base_of

中文:
定理 quasiCompact_affineProperty_iff_quasiSeparatedSpace
  条件: [IsAffine Y] (f : X ⟶ Y)
  证明: by
  delta AffineTargetMorphismProperty.diagonal
  rw [quasiSeparatedSpace_iff_forall_affineOpens]
  constructor
  · intro H U V
    let g : pullback U.1.ι V.1.ι ⟶ X := pullback.fst _ _ ≫ U.1.ι
    have e := g.isOpenEmbedding.isEmbedding.toHomeomorph
    rw [IsOpenImmersion.range_pullback_to_base_of

Depends on / 依赖: AffineTargetMorphismProperty, AffineTargetMorphismProperty.diagonal, Homeomorph, Homeomorph.compactSpace, IsOpenImmersion, IsOpenImmersion.range_pullback_to_base_of_left, Scheme, Scheme.Opens.range_, compactSpace, diagonal, g.isOpenEmbedding.isEmbedding.toHomeomorph, introv, isCompact_iff_compactSpace, isEmbedding, isOpenEmbedding, pullback, pullback.fst, quasiSeparatedSpace_iff_forall_affineOpens, range_pullback_to_base_of_left, toHomeomorph
-/
theorem quasiCompact_affineProperty_iff_quasiSeparatedSpace [IsAffine Y] (f : X ⟶ Y) :
    AffineTargetMorphismProperty.diagonal (fun X _ _ _ => CompactSpace X) f ↔
      QuasiSeparatedSpace X := by
  delta AffineTargetMorphismProperty.diagonal
  rw [quasiSeparatedSpace_iff_forall_affineOpens]
  constructor
  · intro H U V
    let g : pullback U.1.ι V.1.ι ⟶ X := pullback.fst _ _ ≫ U.1.ι
    have e := g.isOpenEmbedding.isEmbedding.toHomeomorph
    rw [IsOpenImmersion.range_pullback_to_base_of_left]; rw [Scheme.Opens.range_ι]; rw [Scheme.Opens.range_ι]
      at e
    rw [isCompact_iff_compactSpace]
    exact @Homeomorph.compactSpace _ _ _ _ (H _ _) e
  · introv H h₁ h₂
    let g : pullback f₁ f₂ ⟶ X := pullback.fst _ _ ≫ f₁
    have e := g.isOpenEmbedding.isEmbedding.toHomeomorph
    rw [IsOpenImmersion.range_pullback_to_base_of_left] at e
    simp_rw [isCompact_iff_compactSpace] at H
    exact @Homeomorph.compactSpace _ _ _ _
        (H ⟨_, isAffineOpen_opensRange f₁⟩ ⟨_, isAffineOpen_opensRange f₂⟩) e.symm

/--
theorem `quasiSeparated_eq_diagonal_is_quasiCompact` / 定理 `quasiSeparated_eq_diagonal_is_quasiCompact`

English:
theorem quasiSeparated_eq_diagonal_is_quasiCompact
  proof: by ext; exact quasiSeparated_iff _

中文:
定理 quasiSeparated_eq_diagonal_is_quasiCompact
  证明: by ext; exact quasiSeparated_iff _

Depends on / 依赖: quasiSeparated_iff
-/
theorem quasiSeparated_eq_diagonal_is_quasiCompact :
    @QuasiSeparated = MorphismProperty.diagonal @QuasiCompact := by ext; exact quasiSeparated_iff _

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasAffineProperty @QuasiSeparated (fun X _ _ _ => QuasiSeparatedSpace X)
  body: HasAffineProperty.copy
    quasiSeparated_eq_diagonal_is_quasiCompact.symm
    (by ext; exact quasiCompact_affineProperty_iff_quasiSeparatedSpace _)

中文:
实例 :
  签名: HasAffine命题erty @QuasiSeparated (fun X _ _ _ => QuasiSeparatedSpace X)
  定义体: HasAffineProperty.copy
    quasiSeparated_eq_diagonal_is_quasiCompact.symm
    (by ext; exact quasiCompact_affineProperty_iff_quasiSeparatedSpace _)

Depends on / 依赖: HasAffineProperty, HasAffineProperty.copy
-/
instance : HasAffineProperty @QuasiSeparated (fun X _ _ _ => QuasiSeparatedSpace X) where
  __ := HasAffineProperty.copy
    quasiSeparated_eq_diagonal_is_quasiCompact.symm
    (by ext; exact quasiCompact_affineProperty_iff_quasiSeparatedSpace _)

instance (priority := 900) (f : X ⟶ Y) [Mono f] :
    QuasiSeparated f where

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `quasiSeparated_isStableUnderComposition` / 实例 `quasiSeparated_isStableUnderComposition`

English:
instance quasiSeparated_isStableUnderComposition
  signature: :
  body: quasiSeparated_eq_diagonal_is_quasiCompact.symm ▸ inferInstance

中文:
实例 quasiSeparated_isStableUnderComposition
  签名: :
  定义体: quasiSeparated_eq_diagonal_is_quasiCompact.symm ▸ inferInstance

Depends on / 依赖: quasiSeparated_eq_diagonal_is_quasiCompact, quasiSeparated_eq_diagonal_is_quasiCompact.symm
-/
instance quasiSeparated_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition @QuasiSeparated :=
  quasiSeparated_eq_diagonal_is_quasiCompact.symm ▸ inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsMultiplicative @QuasiSeparated
  body: inferInstance

中文:
实例 :
  签名: Morphism命题erty.IsMultiplicative @QuasiSeparated
  定义体: inferInstance
-/
instance : MorphismProperty.IsMultiplicative @QuasiSeparated where
  id_mem _ := inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `quasiSeparated_isStableUnderBaseChange` / 实例 `quasiSeparated_isStableUnderBaseChange`

English:
instance quasiSeparated_isStableUnderBaseChange
  signature: :
  body: quasiSeparated_eq_diagonal_is_quasiCompact.symm ▸ inferInstance

中文:
实例 quasiSeparated_isStableUnderBaseChange
  签名: :
  定义体: quasiSeparated_eq_diagonal_is_quasiCompact.symm ▸ inferInstance

Depends on / 依赖: quasiSeparated_eq_diagonal_is_quasiCompact, quasiSeparated_eq_diagonal_is_quasiCompact.symm
-/
instance quasiSeparated_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @QuasiSeparated :=
  quasiSeparated_eq_diagonal_is_quasiCompact.symm ▸ inferInstance

/--
Instance `quasiSeparated_comp` / 实例 `quasiSeparated_comp`

English:
instance quasiSeparated_comp
  signature: (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiSeparated f]
  body: MorphismProperty.comp_mem _ f g inferInstance inferInstance

中文:
实例 quasiSeparated_comp
  签名: (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiSeparated f]
  定义体: MorphismProperty.comp_mem _ f g inferInstance inferInstance

Depends on / 依赖: MorphismProperty, MorphismProperty.comp_mem, comp_mem
-/
instance quasiSeparated_comp (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiSeparated f]
    [QuasiSeparated g] : QuasiSeparated (f ≫ g) :=
  MorphismProperty.comp_mem _ f g inferInstance inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `quasiSeparatedSpace_iff_quasiSeparated` / 定理 `quasiSeparatedSpace_iff_quasiSeparated`

English:
theorem quasiSeparatedSpace_iff_quasiSeparated
  given: (X : Scheme)
  proof: (HasAffineProperty.iff_of_isAffine (P := @QuasiSeparated)).symm

中文:
定理 quasiSeparatedSpace_iff_quasiSeparated
  条件: (X : Scheme)
  证明: (HasAffineProperty.iff_of_isAffine (P := @QuasiSeparated)).symm

Depends on / 依赖: HasAffineProperty, HasAffineProperty.iff_of_isAffine, QuasiSeparated, choose_spec, exists.choose_spec, iff_of_isAffine
-/
theorem quasiSeparatedSpace_iff_quasiSeparated (X : Scheme) :
    QuasiSeparatedSpace X ↔ QuasiSeparated (terminal.from X) :=
  (HasAffineProperty.iff_of_isAffine (P := @QuasiSeparated)).symm

set_option backward.isDefEq.respectTransparency.types false in
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [QuasiSeparated g] :
    QuasiSeparated (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [QuasiSeparated f] :
    QuasiSeparated (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance (f : X ⟶ Y) (V : Y.Opens) [QuasiSeparated f] : QuasiSeparated (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

instance (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e) [QuasiSeparated f] :
    QuasiSeparated (f.resLE V U e) := by
  delta Scheme.Hom.resLE; infer_instance

/--
theorem `quasiSeparatedSpace_of_quasiSeparated` / 定理 `quasiSeparatedSpace_of_quasiSeparated`

English:
theorem quasiSeparatedSpace_of_quasiSeparated
  statement: (f : X ⟶ Y)
  proof: by
  rw [quasiSeparatedSpace_iff_quasiSeparated] at hY ⊢
  rw [← terminalIsTerminal.hom_ext (f ≫ terminal.from Y) (terminal.from X)]
  infer_instance

中文:
定理 quasiSeparatedSpace_of_quasiSeparated
  结论: (f : X ⟶ Y)
  证明: by
  rw [quasiSeparatedSpace_iff_quasiSeparated] at hY ⊢
  rw [← terminalIsTerminal.hom_ext (f ≫ terminal.from Y) (terminal.from X)]
  infer_instance

Depends on / 依赖: hom_ext, infer_instance, quasiSeparatedSpace_iff_quasiSeparated, terminal, terminal.from, terminalIsTerminal, terminalIsTerminal.hom_ext
-/
theorem quasiSeparatedSpace_of_quasiSeparated (f : X ⟶ Y)
    [hY : QuasiSeparatedSpace Y] [QuasiSeparated f] : QuasiSeparatedSpace X := by
  rw [quasiSeparatedSpace_iff_quasiSeparated] at hY ⊢
  rw [← terminalIsTerminal.hom_ext (f ≫ terminal.from Y) (terminal.from X)]
  infer_instance

/--
lemma `Scheme.Hom.isQuasiSeparated_preimage` / 引理 `Scheme.Hom.isQuasiSeparated_preimage`

English:
lemma Scheme.Hom.isQuasiSeparated_preimage
  statement: [QuasiSeparated f] {U : Opens Y}
  proof: by
  have : QuasiSeparatedSpace U := (isQuasiSeparated_iff_quasiSeparatedSpace _ U.2).mp hU
  exact (isQuasiSeparated_iff_quasiSeparatedSpace _ (f ⁻¹ᵁ U).2).mpr
    (quasiSeparatedSpace_of_quasiSeparated (f ∣_ U))

中文:
引理 Scheme.Hom.isQuasiSeparated_preimage
  结论: [QuasiSeparated f] {U : Opens Y}
  证明: by
  have : QuasiSeparatedSpace U := (isQuasiSeparated_iff_quasiSeparatedSpace _ U.2).mp hU
  exact (isQuasiSeparated_iff_quasiSeparatedSpace _ (f ⁻¹ᵁ U).2).mpr
    (quasiSeparatedSpace_of_quasiSeparated (f ∣_ U))

Depends on / 依赖: QuasiSeparatedSpace, isQuasiSeparated_iff_quasiSeparatedSpace, quasiSeparatedSpace_of_quasiSeparated
-/
lemma Scheme.Hom.isQuasiSeparated_preimage [QuasiSeparated f] {U : Opens Y}
    (hU : IsQuasiSeparated (U : Set Y)) : IsQuasiSeparated (f ⁻¹ᵁ U : Set X) := by
  have : QuasiSeparatedSpace U := (isQuasiSeparated_iff_quasiSeparatedSpace _ U.2).mp hU
  exact (isQuasiSeparated_iff_quasiSeparatedSpace _ (f ⁻¹ᵁ U).2).mpr
    (quasiSeparatedSpace_of_quasiSeparated (f ∣_ U))

/--
Instance `quasiSeparatedSpace_of_isAffine` / 实例 `quasiSeparatedSpace_of_isAffine`

English:
instance quasiSeparatedSpace_of_isAffine
  signature: (X : Scheme) [IsAffine X]
  body: (quasiSeparatedSpace_congr X.isoSpec.hom.homeomorph).2 PrimeSpectrum.instQuasiSeparatedSpace

中文:
实例 quasiSeparatedSpace_of_isAffine
  签名: (X : Scheme) [IsAffine X]
  定义体: (quasiSeparatedSpace_congr X.isoSpec.hom.homeomorph).2 PrimeSpectrum.instQuasiSeparatedSpace

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.instQuasiSeparatedSpace, X.isoSpec.hom.homeomorph, homeomorph, instQuasiSeparatedSpace, isoSpec, quasiSeparatedSpace_congr
-/
instance quasiSeparatedSpace_of_isAffine (X : Scheme) [IsAffine X] : QuasiSeparatedSpace X :=
  (quasiSeparatedSpace_congr X.isoSpec.hom.homeomorph).2 PrimeSpectrum.instQuasiSeparatedSpace

/--
theorem `IsAffineOpen.isQuasiSeparated` / 定理 `IsAffineOpen.isQuasiSeparated`

English:
theorem IsAffineOpen.isQuasiSeparated
  given: {U : X.Opens} (hU : IsAffineOpen U)
  proof: by
  rw [isQuasiSeparated_iff_quasiSeparatedSpace]
  exacts [@AlgebraicGeometry.quasiSeparatedSpace_of_isAffine _ hU, U.isOpen]

中文:
定理 IsAffineOpen.isQuasiSeparated
  条件: {U : X.Opens} (hU : IsAffineOpen U)
  证明: by
  rw [isQuasiSeparated_iff_quasiSeparatedSpace]
  exacts [@AlgebraicGeometry.quasiSeparatedSpace_of_isAffine _ hU, U.isOpen]

Depends on / 依赖: AlgebraicGeometry, AlgebraicGeometry.quasiSeparatedSpace_of_isAffine, U.isOpen, exacts, isOpen, isQuasiSeparated_iff_quasiSeparatedSpace, quasiSeparatedSpace_of_isAffine
-/
theorem IsAffineOpen.isQuasiSeparated {U : X.Opens} (hU : IsAffineOpen U) :
    IsQuasiSeparated (U : Set X) := by
  rw [isQuasiSeparated_iff_quasiSeparatedSpace]
  exacts [@AlgebraicGeometry.quasiSeparatedSpace_of_isAffine _ hU, U.isOpen]

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [QuasiSeparatedSpace
  signature: X] : QuasiSeparated X.toSpecΓ
  body: HasAffineProperty.iff_of_isAffine.mpr ‹_›

中文:
实例 [QuasiSeparatedSpace
  签名: X] : QuasiSeparated X.toSpecΓ
  定义体: HasAffineProperty.iff_of_isAffine.mpr ‹_›

Depends on / 依赖: HasAffineProperty, HasAffineProperty.iff_of_isAffine.mpr, iff_of_isAffine
-/
instance [QuasiSeparatedSpace X] : QuasiSeparated X.toSpecΓ :=
  HasAffineProperty.iff_of_isAffine.mpr ‹_›

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `Scheme.quasiSeparatedSpace_of_isOpenCover` / 定理 `Scheme.quasiSeparatedSpace_of_isOpenCover`

English:
theorem Scheme.quasiSeparatedSpace_of_isOpenCover
  proof: by
  let := HasAffineProperty.isLocal_affineProperty @QuasiCompact
  rw [← quasiCompact_affineProperty_iff_quasiSeparatedSpace X.toSpecΓ]
  have : forall i, IsAffine ((X.openCoverOfIsOpenCover U hU).X i) := hU₁
  refine AffineTargetMorphismProperty.diagonal_of_openCover_source _
    (Scheme.openCove

中文:
定理 Scheme.quasiSeparatedSpace_of_isOpenCover
  证明: by
  let := HasAffineProperty.isLocal_affineProperty @QuasiCompact
  rw [← quasiCompact_affineProperty_iff_quasiSeparatedSpace X.toSpecΓ]
  have : forall i, IsAffine ((X.openCoverOfIsOpenCover U hU).X i) := hU₁
  refine AffineTargetMorphismProperty.diagonal_of_openCover_source _
    (Scheme.openCove
-/
theorem Scheme.quasiSeparatedSpace_of_isOpenCover
    {I : Type*} (U : I -> X.Opens) (hU : IsOpenCover U)
    (hU₁ : forall i, IsAffineOpen (U i)) (hU₂ : forall i j, IsCompact (X := X) (U i inter U j)) :
    QuasiSeparatedSpace X := by
  let := HasAffineProperty.isLocal_affineProperty @QuasiCompact
  rw [← quasiCompact_affineProperty_iff_quasiSeparatedSpace X.toSpecΓ]
  have : forall i, IsAffine ((X.openCoverOfIsOpenCover U hU).X i) := hU₁
  refine AffineTargetMorphismProperty.diagonal_of_openCover_source _
    (Scheme.openCoverOfIsOpenCover _ _ hU) fun i j => ?_
  rw [← isCompact_univ_iff]; rw [(pullback.fst ((X.openCoverOfIsOpenCover U hU).f i)
    ((X.openCoverOfIsOpenCover U hU).f j) ≫
    (X.openCoverOfIsOpenCover U hU).f i).isOpenEmbedding.isCompact_iff]; rw [Set.image_univ]; rw [IsOpenImmersion.range_pullback_to_base_of_left]
  simpa using hU₂ i j

set_option backward.isDefEq.respectTransparency false in
/--
lemma `quasiSeparatedSpace_iff_quasiCompact_prod_lift` / 引理 `quasiSeparatedSpace_iff_quasiCompact_prod_lift`

English:
lemma quasiSeparatedSpace_iff_quasiCompact_prod_lift
  proof: by
  rw [← MorphismProperty.cancel_right_of_respectsIso @QuasiCompact _ (prodIsoPullback X X).hom]; rw [← HasAffineProperty.iff_of_isAffine (f := terminal.from X) (P := @QuasiSeparated)]; rw [quasiSeparated_iff]
  congr!
  ext : 1 <;> simp

中文:
引理 quasiSeparatedSpace_iff_quasiCompact_prod_lift
  证明: by
  rw [← MorphismProperty.cancel_right_of_respectsIso @QuasiCompact _ (prodIsoPullback X X).hom]; rw [← HasAffineProperty.iff_of_isAffine (f := terminal.from X) (P := @QuasiSeparated)]; rw [quasiSeparated_iff]
  congr!
  ext : 1 <;> simp

Depends on / 依赖: HasAffineProperty, HasAffineProperty.iff_of_isAffine, MorphismProperty, MorphismProperty.cancel_right_of_respectsIso, QuasiCompact, QuasiSeparated, cancel_right_of_respectsIso, iff_of_isAffine, prodIsoPullback, quasiSeparated_iff, terminal, terminal.from
-/
lemma quasiSeparatedSpace_iff_quasiCompact_prod_lift :
    QuasiSeparatedSpace X ↔ QuasiCompact (prod.lift (𝟙 X) (𝟙 X)) := by
  rw [← MorphismProperty.cancel_right_of_respectsIso @QuasiCompact _ (prodIsoPullback X X).hom]; rw [← HasAffineProperty.iff_of_isAffine (f := terminal.from X) (P := @QuasiSeparated)]; rw [quasiSeparated_iff]
  congr!
  ext : 1 <;> simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [QuasiSeparatedSpace
  signature: X] : QuasiCompact (prod.lift (𝟙 X) (𝟙 X))
  body: by
  rwa [← quasiSeparatedSpace_iff_quasiCompact_prod_lift]

中文:
实例 [QuasiSeparatedSpace
  签名: X] : QuasiCompact (prod.lift (𝟙 X) (𝟙 X))
  定义体: by
  rwa [← quasiSeparatedSpace_iff_quasiCompact_prod_lift]

Depends on / 依赖: quasiSeparatedSpace_iff_quasiCompact_prod_lift
-/
instance [QuasiSeparatedSpace X] : QuasiCompact (prod.lift (𝟙 X) (𝟙 X)) := by
  rwa [← quasiSeparatedSpace_iff_quasiCompact_prod_lift]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [QuasiSeparatedSpace
  signature: Y] (f g
  body: MorphismProperty.of_isPullback (P := @QuasiCompact)
    (isPullback_equalizer_prod f g).flip inferInstance

中文:
实例 [QuasiSeparatedSpace
  签名: Y] (f g
  定义体: MorphismProperty.of_isPullback (P := @QuasiCompact)
    (isPullback_equalizer_prod f g).flip inferInstance

Depends on / 依赖: MorphismProperty, MorphismProperty.of_isPullback, QuasiCompact, isPullback_equalizer_prod, of_isPullback
-/
instance [QuasiSeparatedSpace Y] (f g : X ⟶ Y) : QuasiCompact (equalizer.ι f g) :=
  MorphismProperty.of_isPullback (P := @QuasiCompact)
    (isPullback_equalizer_prod f g).flip inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompactSpace
  signature: X] [QuasiSeparatedSpace Y] (f g
  body: by
  constructor
  simpa using QuasiCompact.isCompact_preimage (f := equalizer.ι f g) _ isOpen_univ isCompact_univ

中文:
实例 [CompactSpace
  签名: X] [QuasiSeparatedSpace Y] (f g
  定义体: by
  constructor
  simpa using QuasiCompact.isCompact_preimage (f := equalizer.ι f g) _ isOpen_univ isCompact_univ

Depends on / 依赖: QuasiCompact, QuasiCompact.isCompact_preimage, equalizer, isCompact_preimage, isCompact_univ, isOpen_univ
-/
instance [CompactSpace X] [QuasiSeparatedSpace Y] (f g : X ⟶ Y) :
    CompactSpace (equalizer f g).carrier := by
  constructor
  simpa using QuasiCompact.isCompact_preimage (f := equalizer.ι f g) _ isOpen_univ isCompact_univ

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `QuasiSeparated.of_comp` / 定理 `QuasiSeparated.of_comp`

English:
theorem QuasiSeparated.of_comp
  given: (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiSeparated (f ≫ g)]
  proof: by
  let 𝒰 := (Z.affineCover.pullback₁ g).bind fun x => Scheme.affineCover _
  have (i : _) : IsAffine (𝒰.X i) := by dsimp [𝒰]; infer_instance
  apply HasAffineProperty.of_openCover
    ((Z.affineCover.pullback₁ g).bind fun x => Scheme.affineCover _)
  rintro ⟨i, j⟩; dsimp at i j
  refine @quasiSepa

中文:
定理 QuasiSeparated.of_comp
  条件: (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiSeparated (f ≫ g)]
  证明: by
  let 𝒰 := (Z.affineCover.pullback₁ g).bind fun x => Scheme.affineCover _
  have (i : _) : IsAffine (𝒰.X i) := by dsimp [𝒰]; infer_instance
  apply HasAffineProperty.of_openCover
    ((Z.affineCover.pullback₁ g).bind fun x => Scheme.affineCover _)
  rintro ⟨i, j⟩; dsimp at i j
  refine @quasiSepa

Depends on / 依赖: Category, Category.comp_id, HasAffineProperty, HasAffineProperty.of_isPullback, HasAffineProperty.of_openCover, IsAffine, Scheme, Scheme.affineCover, Z.affineCover.f, Z.affineCover.pullback, affineCover, comp_id, infer_instance, of_hasPullback, of_isPullback, of_openCover, pullback, pullback.map, pullbackRightPullbackFst, quasiSeparatedSpace_of_quasiSeparated
-/
theorem QuasiSeparated.of_comp (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiSeparated (f ≫ g)] :
    QuasiSeparated f := by
  let 𝒰 := (Z.affineCover.pullback₁ g).bind fun x => Scheme.affineCover _
  have (i : _) : IsAffine (𝒰.X i) := by dsimp [𝒰]; infer_instance
  apply HasAffineProperty.of_openCover
    ((Z.affineCover.pullback₁ g).bind fun x => Scheme.affineCover _)
  rintro ⟨i, j⟩; dsimp at i j
  refine @quasiSeparatedSpace_of_quasiSeparated _ _ ?_
    (HasAffineProperty.of_isPullback (.of_hasPullback _ (Z.affineCover.f i)) ‹_›) ?_
  · exact pullback.map _ _ _ _ (𝟙 _) _ _ (by simp) (Category.comp_id _) ≫
      (pullbackRightPullbackFstIso g (Z.affineCover.f i) f).hom
  · exact inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance (priority := low) QuasiSeparated.of_quasiSeparatedSpace
    (f : X ⟶ Y) [QuasiSeparatedSpace X] : QuasiSeparated f :=
  have : QuasiSeparated (f ≫ Y.toSpecΓ) :=
    (HasAffineProperty.iff_of_isAffine (P := @QuasiSeparated)).mpr ‹_›
  .of_comp f Y.toSpecΓ

/--
theorem `quasiSeparated_iff_quasiSeparatedSpace` / 定理 `quasiSeparated_iff_quasiSeparatedSpace`

English:
theorem quasiSeparated_iff_quasiSeparatedSpace
  given: (f : X ⟶ Y) [QuasiSeparatedSpace Y]
  proof: ⟨fun _ => quasiSeparatedSpace_of_quasiSeparated f, fun _ => inferInstance⟩

中文:
定理 quasiSeparated_iff_quasiSeparatedSpace
  条件: (f : X ⟶ Y) [QuasiSeparatedSpace Y]
  证明: ⟨fun _ => quasiSeparatedSpace_of_quasiSeparated f, fun _ => inferInstance⟩

Depends on / 依赖: quasiSeparatedSpace_of_quasiSeparated
-/
theorem quasiSeparated_iff_quasiSeparatedSpace (f : X ⟶ Y) [QuasiSeparatedSpace Y] :
    QuasiSeparated f ↔ QuasiSeparatedSpace X :=
  ⟨fun _ => quasiSeparatedSpace_of_quasiSeparated f, fun _ => inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.HasOfPostcompProperty @QuasiSeparated ⊤
  body: .of_comp f g

中文:
实例 :
  签名: Morphism命题erty.HasOfPostcomp命题erty @QuasiSeparated ⊤
  定义体: .of_comp f g

Depends on / 依赖: of_comp
-/
instance : MorphismProperty.HasOfPostcompProperty @QuasiSeparated ⊤ where
  of_postcomp f g _ _ := .of_comp f g

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.HasOfPostcompProperty @QuasiCompact @QuasiSeparated
  body: MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    (by rw [quasiSeparated_eq_diagonal_is_quasiCompact])

中文:
实例 :
  签名: Morphism命题erty.HasOfPostcomp命题erty @QuasiCompact @QuasiSeparated
  定义体: MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    (by rw [quasiSeparated_eq_diagonal_is_quasiCompact])

Depends on / 依赖: MorphismProperty, MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr, hasOfPostcompProperty_iff_le_diagonal, quasiSeparated_eq_diagonal_is_quasiCompact
-/
instance : MorphismProperty.HasOfPostcompProperty @QuasiCompact @QuasiSeparated :=
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    (by rw [quasiSeparated_eq_diagonal_is_quasiCompact])

/--
lemma `QuasiCompact.of_comp` / 引理 `QuasiCompact.of_comp`

English:
lemma QuasiCompact.of_comp
  given: (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact (f ≫ g)] [QuasiSeparated g]
  proof: MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

中文:
引理 QuasiCompact.of_comp
  条件: (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact (f ≫ g)] [QuasiSeparated g]
  证明: MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

Depends on / 依赖: MorphismProperty, MorphismProperty.of_postcomp, of_postcomp
-/
lemma QuasiCompact.of_comp (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact (f ≫ g)] [QuasiSeparated g] :
    QuasiCompact f :=
  MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

set_option backward.isDefEq.respectTransparency.types false in
instance (priority := low) quasiCompact_of_compactSpace {X Y : Scheme} (f : X ⟶ Y)
    [CompactSpace X] [QuasiSeparatedSpace Y] : QuasiCompact f :=
  have : QuasiCompact (f ≫ Y.toSpecΓ) := HasAffineProperty.iff_of_isAffine.mpr ‹_›
  .of_comp f Y.toSpecΓ

/--
theorem `quasiCompact_iff_compactSpace` / 定理 `quasiCompact_iff_compactSpace`

English:
theorem quasiCompact_iff_compactSpace
  given: (f : X ⟶ Y) [QuasiSeparatedSpace Y] [CompactSpace Y]
  proof: ⟨fun _ => QuasiCompact.compactSpace_of_compactSpace f, fun _ => inferInstance⟩

中文:
定理 quasiCompact_iff_compactSpace
  条件: (f : X ⟶ Y) [QuasiSeparatedSpace Y] [CompactSpace Y]
  证明: ⟨fun _ => QuasiCompact.compactSpace_of_compactSpace f, fun _ => inferInstance⟩

Depends on / 依赖: QuasiCompact, QuasiCompact.compactSpace_of_compactSpace, compactSpace_of_compactSpace
-/
theorem quasiCompact_iff_compactSpace (f : X ⟶ Y) [QuasiSeparatedSpace Y] [CompactSpace Y] :
    QuasiCompact f ↔ CompactSpace X :=
  ⟨fun _ => QuasiCompact.compactSpace_of_compactSpace f, fun _ => inferInstance⟩

/--
theorem `exists_eq_pow_mul_of_isAffineOpen` / 定理 `exists_eq_pow_mul_of_isAffineOpen`

English:
theorem exists_eq_pow_mul_of_isAffineOpen
  statement: (X : Scheme) (U : X.Opens) (hU : IsAffineOpen U)
  proof: by
  have := (hU.isLocalization_basicOpen f).1.2
  obtain ⟨⟨y, _, n, rfl⟩, d⟩ := this x
  use n, y
  simpa [mul_comm x] using! d.symm

中文:
定理 exists_eq_pow_mul_of_isAffineOpen
  结论: (X : Scheme) (U : X.Opens) (hU : IsAffineOpen U)
  证明: by
  have := (hU.isLocalization_basicOpen f).1.2
  obtain ⟨⟨y, _, n, rfl⟩, d⟩ := this x
  use n, y
  simpa [mul_comm x] using! d.symm

Depends on / 依赖: d.symm, hU.isLocalization_basicOpen, isLocalization_basicOpen, mul_comm
-/
theorem exists_eq_pow_mul_of_isAffineOpen (X : Scheme) (U : X.Opens) (hU : IsAffineOpen U)
    (f : Γ(X, U)) (x : Γ(X, X.basicOpen f)) :
    exists (n : Nat) (y : Γ(X, U)), y |_ X.basicOpen f = (f |_ X.basicOpen f) ^ n * x := by
  have := (hU.isLocalization_basicOpen f).1.2
  obtain ⟨⟨y, _, n, rfl⟩, d⟩ := this x
  use n, y
  simpa [mul_comm x] using! d.symm

/--
theorem `exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux_aux` / 定理 `exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux_aux`

English:
theorem exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux_aux
  statement: {X : TopCat.{u}}
  proof: by
  apply_fun (fun x : F.obj (op U₅) => x |_ U₇) at e₁
  apply_fun (fun x : F.obj (op U₆) => x |_ U₇) at e₂
  dsimp only [TopCat.Presheaf.restrictOpenCommRingCat_apply] at e₁ e₂ ⊢
  simp only [map_mul, map_pow, ← op_comp, ← F.map_comp, homOfLE_comp, ← CommRingCat.comp_apply]
    at e₁ e₂ ⊢
  rw [e₁

中文:
定理 exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux_aux
  结论: {X : TopCat.{u}}
  证明: by
  apply_fun (fun x : F.obj (op U₅) => x |_ U₇) at e₁
  apply_fun (fun x : F.obj (op U₆) => x |_ U₇) at e₂
  dsimp only [TopCat.Presheaf.restrictOpenCommRingCat_apply] at e₁ e₂ ⊢
  simp only [map_mul, map_pow, ← op_comp, ← F.map_comp, homOfLE_comp, ← CommRingCat.comp_apply]
    at e₁ e₂ ⊢
  rw [e₁

Depends on / 依赖: CommRingCat, CommRingCat.comp_apply, F.map_comp, F.obj, Presheaf, TopCat, TopCat.Presheaf.restrictOpenCommRingCat_apply, apply_fun, comp_apply, homOfLE_comp, map_comp, map_mul, map_pow, mul_left_comm, op_comp, restrictOpenCommRingCat_apply
-/
theorem exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux_aux {X : TopCat.{u}}
    (F : X.Presheaf CommRingCat) {U₁ U₂ U₃ U₄ U₅ U₆ U₇ : Opens X} {n₁ n₂ : Nat}
    {y₁ : F.obj (op U₁)} {y₂ : F.obj (op U₂)} {f : F.obj (op <| U₁ ⊔ U₂)}
    {x : F.obj (op U₃)} (h₄₁ : U₄ <= U₁) (h₄₂ : U₄ <= U₂) (h₅₁ : U₅ <= U₁) (h₅₃ : U₅ <= U₃)
    (h₆₂ : U₆ <= U₂) (h₆₃ : U₆ <= U₃) (h₇₄ : U₇ <= U₄) (h₇₅ : U₇ <= U₅) (h₇₆ : U₇ <= U₆)
    (e₁ : y₁ |_ U₅ = (f |_ U₁ |_ U₅) ^ n₁ * x |_ U₅)
    (e₂ : y₂ |_ U₆ = (f |_ U₂ |_ U₆) ^ n₂ * x |_ U₆) :
    (((f |_ U₁) ^ n₂ * y₁) |_ U₄) |_ U₇ = (((f |_ U₂) ^ n₁ * y₂) |_ U₄) |_ U₇ := by
  apply_fun (fun x : F.obj (op U₅) => x |_ U₇) at e₁
  apply_fun (fun x : F.obj (op U₆) => x |_ U₇) at e₂
  dsimp only [TopCat.Presheaf.restrictOpenCommRingCat_apply] at e₁ e₂ ⊢
  simp only [map_mul, map_pow, ← op_comp, ← F.map_comp, homOfLE_comp, ← CommRingCat.comp_apply]
    at e₁ e₂ ⊢
  rw [e₁]; rw [e₂]; rw [mul_left_comm]

/--
theorem `exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux` / 定理 `exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux`

English:
theorem exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux
  statement: (X : Scheme)
  proof: by
  obtain ⟨⟨_, n, rfl⟩, e⟩ :=
    (@IsLocalization.eq_iff_exists _ _ _ _ _ _
      (S.2.isLocalization_basicOpen (f |_ S.1))
        (((f |_ U₁) ^ n₂ * y₁) |_ S.1)
        (((f |_ U₂) ^ n₁ * y₂) |_ S.1)).mp <| by
    apply exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux_aux (e₁ := e₁)

中文:
定理 exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux
  结论: (X : Scheme)
  证明: by
  obtain ⟨⟨_, n, rfl⟩, e⟩ :=
    (@IsLocalization.eq_iff_exists _ _ _ _ _ _
      (S.2.isLocalization_basicOpen (f |_ S.1))
        (((f |_ U₁) ^ n₂ * y₁) |_ S.1)
        (((f |_ U₂) ^ n₁ * y₂) |_ S.1)).mp <| by
    apply exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux_aux (e₁ := e₁)

Depends on / 依赖: IsLocalization, IsLocalization.eq_iff_exists, Presheaf, Scheme, Scheme.basicOpen_res, TopCat, TopCat.Presheaf.restrictOpenCommRingCat_apply, X.basicOpen, basicOpen, basicOpen_res, eq_iff_exists, exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux_aux, inf_le_inf, isLocalization_basicOpen, le_rfl, restrictOpenCommRingCat_apply
-/
theorem exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux (X : Scheme)
    (S : X.affineOpens) (U₁ U₂ : X.Opens) {n₁ n₂ : Nat} {y₁ : Γ(X, U₁)}
    {y₂ : Γ(X, U₂)} {f : Γ(X, U₁ ⊔ U₂)}
    {x : Γ(X, X.basicOpen f)} (h₁ : S.1 <= U₁) (h₂ : S.1 <= U₂)
    (e₁ : y₁ |_ X.basicOpen (f |_ U₁) =
      ((f |_ U₁ |_ X.basicOpen _) ^ n₁) * x |_ X.basicOpen _)
    (e₂ : y₂ |_ X.basicOpen (f |_ U₂) =
      ((f |_ U₂ |_ X.basicOpen _) ^ n₂) * x |_ X.basicOpen _) :
    exists n : Nat, forall m, n <= m ->
      ((f |_ U₁) ^ (m + n₂) * y₁) |_ S.1 = ((f |_ U₂) ^ (m + n₁) * y₂) |_ S.1 := by
  obtain ⟨⟨_, n, rfl⟩, e⟩ :=
    (@IsLocalization.eq_iff_exists _ _ _ _ _ _
      (S.2.isLocalization_basicOpen (f |_ S.1))
        (((f |_ U₁) ^ n₂ * y₁) |_ S.1)
        (((f |_ U₂) ^ n₁ * y₂) |_ S.1)).mp <| by
    apply exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux_aux (e₁ := e₁) (e₂ := e₂)
    · change X.basicOpen _ <= _
      simp only [TopCat.Presheaf.restrictOpenCommRingCat_apply, Scheme.basicOpen_res]
      exact inf_le_inf h₁ le_rfl
    · change X.basicOpen _ <= _
      simp only [TopCat.Presheaf.restrictOpenCommRingCat_apply, Scheme.basicOpen_res]
      exact inf_le_inf h₂ le_rfl
  use n
  intro m hm
  rw [← tsub_add_cancel_of_le hm]
  simp only [TopCat.Presheaf.restrictOpenCommRingCat_apply,
    pow_add, map_pow, map_mul, mul_assoc, ← Functor.map_comp, ← op_comp, homOfLE_comp,
    ← CommRingCat.comp_apply] at e ⊢
  rw [e]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated` / 定理 `exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated`

English:
theorem exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated
  statement: (X : Scheme.{u}) (U : X.Opens)
  proof: by
  dsimp only [TopCat.Presheaf.restrictOpenCommRingCat_apply]
  revert hU' f x
  refine compact_open_induction_on U hU ?_ ?_
  · intro _ f x
    use 0, f
    refine @Subsingleton.elim _
      (CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty ?_)) _ _
    rw [eq_bot_iff]
    exac

中文:
定理 exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated
  结论: (X : Scheme.{u}) (U : X.Opens)
  证明: by
  dsimp only [TopCat.Presheaf.restrictOpenCommRingCat_apply]
  revert hU' f x
  refine compact_open_induction_on U hU ?_ ?_
  · intro _ f x
    use 0, f
    refine @Subsingleton.elim _
      (CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty ?_)) _ _
    rw [eq_bot_iff]
    exac

Depends on / 依赖: Classical, Classical.arbitrary, CommRingCat, CommRingCat.subsingleton_of_isTerminal, Presheaf, SimplexCategory, SimplexCategory.const, Subsingleton, Subsingleton.elim, TopCat, TopCat.Presheaf.restrictOpenCommRingCat_apply, X.basicOpen_le, X.map, X.sheaf.isTerminalOfEqEmpty, arbitrary, basicOpen_le, compact_open_induction_on, eq_bot_iff, isTerminalOfEqEmpty, n.unop
-/
theorem exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated (X : Scheme.{u}) (U : X.Opens)
    (hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1) (f : Γ(X, U)) (x : Γ(X, X.basicOpen f)) :
    exists (n : Nat) (y : Γ(X, U)), y |_ X.basicOpen f = (f |_ X.basicOpen f) ^ n * x := by
  dsimp only [TopCat.Presheaf.restrictOpenCommRingCat_apply]
  revert hU' f x
  refine compact_open_induction_on U hU ?_ ?_
  · intro _ f x
    use 0, f
    refine @Subsingleton.elim _
      (CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty ?_)) _ _
    rw [eq_bot_iff]
    exact X.basicOpen_le f
  · -- Given `f : 𝒪(S ∪ U), x : 𝒪(X_f)`, we need to show that `f ^ n * x` is the restriction of
    -- some `y : 𝒪(S ∪ U)` for some `n : ℕ`.
    intro S hS U hU hSU f x
    -- We know that such `y₁, n₁` exists on `S` by the induction hypothesis.
    obtain ⟨n₁, y₁, hy₁⟩ :=
      hU (hSU.of_subset Set.subset_union_left) (X.presheaf.map (homOfLE le_sup_left).op f)
        (X.presheaf.map (homOfLE _).op x)
    -- · rw [X.basicOpen_res]; exact inf_le_right
    -- We know that such `y₂, n₂` exists on `U` since `U` is affine.
    obtain ⟨n₂, y₂, hy₂⟩ :=
      exists_eq_pow_mul_of_isAffineOpen X _ U.2 (X.presheaf.map (homOfLE le_sup_right).op f)
        (X.presheaf.map (homOfLE _).op x)
    dsimp only [TopCat.Presheaf.restrictOpenCommRingCat_apply] at hy₂
    -- swap; · rw [X.basicOpen_res]; exact inf_le_right
    -- Since `S ∪ U` is quasi-separated, `S ∩ U` can be covered by finite affine opens.
    obtain ⟨s, hs', hs⟩ :=
      isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
        ⟨hSU _ _ Set.subset_union_left S.2 hS Set.subset_union_right U.1.2
            U.2.isCompact,
          (S ⊓ U.1).2⟩
    have := hs'.to_subtype
    cases nonempty_fintype s
    replace hs : S ⊓ U.1 = iSup fun i : s => (i : X.Opens) := by ext1; simpa using hs
    have hs₁ (i : s) : i.1.1 <= S := by
      refine le_trans ?_ (inf_le_left (b := U.1))
      rw [hs]
      exact le_iSup (fun (i : s) => (i : X.Opens)) i
    have hs₂ (i : s) : i.1.1 <= U.1 := by
      refine le_trans ?_ (inf_le_right (a := S))
      rw [hs]
      exact le_iSup (fun (i : s) => (i : X.Opens)) i
    -- On each affine open in the intersection, we have `f ^ (n + n₂) * y₁ = f ^ (n + n₁) * y₂`
    -- for some `n` since `f ^ n₂ * y₁ = f ^ (n₁ + n₂) * x = f ^ n₁ * y₂` on `X_f`.
    have := fun i => exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux
      X i.1 S U (hs₁ i) (hs₂ i) hy₁ hy₂
    choose n hn using this
    -- We can thus choose a big enough `n` such that `f ^ (n + n₂) * y₁ = f ^ (n + n₁) * y₂`
    -- on `S ∩ U`.
    have :
      X.presheaf.map (homOfLE <| inf_le_left).op
          (X.presheaf.map (homOfLE le_sup_left).op f ^ (Finset.univ.sup n + n₂) * y₁) =
        X.presheaf.map (homOfLE <| inf_le_right).op
          (X.presheaf.map (homOfLE le_sup_right).op f ^ (Finset.univ.sup n + n₁) * y₂) := by
      fapply X.sheaf.eq_of_locally_eq' fun i : s => i.1.1
      · refine fun i => homOfLE ?_; rw [hs]
        exact le_iSup (fun (i : s) => (i : X.Opens)) i
      · exact le_of_eq hs
      · intro i
        -- This unfolds `X.sheaf`
        change (X.presheaf.map _) _ = (X.presheaf.map _) _
        simp only [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp]
        apply hn
        exact Finset.le_sup (Finset.mem_univ _)
    use Finset.univ.sup n + n₁ + n₂
    -- By the sheaf condition, since `f ^ (n + n₂) * y₁ = f ^ (n + n₁) * y₂`, it can be glued into
    -- the desired section on `S ∪ U`.
    use (X.sheaf.objSupIsoProdEqLocus S U.1).inv ⟨⟨_ * _, _ * _⟩, this⟩
    refine (X.sheaf.objSupIsoProdEqLocus_inv_eq_iff _ _ _ (X.basicOpen_res _
      (homOfLE le_sup_left).op) (X.basicOpen_res _ (homOfLE le_sup_right).op)).mpr ⟨?_, ?_⟩
    · -- This unfolds `X.sheaf`
      change (X.presheaf.map _) _ = (X.presheaf.map _) _
      rw [add_assoc]; rw [add_comm n₁]
      simp only [pow_add, map_pow, map_mul, hy₁, ← CommRingCat.comp_apply, ← mul_assoc,
        ← Functor.map_comp, ← op_comp, homOfLE_comp]
    · -- This unfolds `X.sheaf`
      change (X.presheaf.map _) _ = (X.presheaf.map _) _
      simp only [pow_add, map_pow, map_mul, hy₂, ← CommRingCat.comp_apply, ← mul_assoc,
        ← Functor.map_comp, ← op_comp, homOfLE_comp]

/--
theorem `isLocalization_basicOpen_of_qcqs` / 定理 `isLocalization_basicOpen_of_qcqs`

English:
theorem isLocalization_basicOpen_of_qcqs
  statement: {X : Scheme} {U : X.Opens} (hU : IsCompact U.1)
  proof: by
  constructor; constructor
  · rintro ⟨_, n, rfl⟩
    simp only [map_pow, RingHom.algebraMap_toAlgebra]
    exact IsUnit.pow _ (RingedSpace.isUnit_res_basicOpen _ f)
  · intro z
    obtain ⟨n, y, e⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X U hU hU' f z
    refine ⟨⟨y, _, n, rfl⟩, ?

中文:
定理 isLocalization_basicOpen_of_qcqs
  结论: {X : Scheme} {U : X.Opens} (hU : IsCompact U.1)
  证明: by
  constructor; constructor
  · rintro ⟨_, n, rfl⟩
    simp only [map_pow, RingHom.algebraMap_toAlgebra]
    exact IsUnit.pow _ (RingedSpace.isUnit_res_basicOpen _ f)
  · intro z
    obtain ⟨n, y, e⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X U hU hU' f z
    refine ⟨⟨y, _, n, rfl⟩, ?

Depends on / 依赖: IsUnit, IsUnit.pow, RingHom, RingHom.algebraMap_toAlgebra, RingedSpace, RingedSpace.isUnit_res_basicOpen, Subtype, Subtype.coe_mk, algebraMap_toAlgebra, coe_mk, e.symm, exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated, isUnit_res_basicOpen, map_pow, map_sub, mul_comm, simp_rw, sub_eq_zero
-/
theorem isLocalization_basicOpen_of_qcqs {X : Scheme} {U : X.Opens} (hU : IsCompact U.1)
    (hU' : IsQuasiSeparated U.1) (f : Γ(X, U)) :
    IsLocalization.Away f (Γ(X, X.basicOpen f)) := by
  constructor; constructor
  · rintro ⟨_, n, rfl⟩
    simp only [map_pow, RingHom.algebraMap_toAlgebra]
    exact IsUnit.pow _ (RingedSpace.isUnit_res_basicOpen _ f)
  · intro z
    obtain ⟨n, y, e⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X U hU hU' f z
    refine ⟨⟨y, _, n, rfl⟩, ?_⟩
    simpa only [map_pow, Subtype.coe_mk, RingHom.algebraMap_toAlgebra, mul_comm z] using! e.symm
  · intro x y
    rw [← sub_eq_zero]; rw [← map_sub]; rw [RingHom.algebraMap_toAlgebra]
    simp_rw [← @sub_eq_zero _ _ (_ * x) (_ * y), ← mul_sub]
    generalize x - y = z
    intro H
    obtain ⟨n, e⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hU _ _ H
    refine ⟨⟨_, n, rfl⟩, ?_⟩
    simpa [mul_comm z] using! e

/--
lemma `exists_of_res_eq_of_qcqs` / 引理 `exists_of_res_eq_of_qcqs`

English:
lemma exists_of_res_eq_of_qcqs
  statement: {X : Scheme.{u}} {U : TopologicalSpace.Opens X}
  proof: by
  obtain ⟨n, hc⟩ := (isLocalization_basicOpen_of_qcqs hU hU' s).exists_of_eq s hfg
  use n

中文:
引理 exists_of_res_eq_of_qcqs
  结论: {X : Scheme.{u}} {U : TopologicalSpace.Opens X}
  证明: by
  obtain ⟨n, hc⟩ := (isLocalization_basicOpen_of_qcqs hU hU' s).exists_of_eq s hfg
  use n

Depends on / 依赖: exists_of_eq, isLocalization_basicOpen_of_qcqs
-/
lemma exists_of_res_eq_of_qcqs {X : Scheme.{u}} {U : TopologicalSpace.Opens X}
    (hU : IsCompact U.carrier) (hU' : IsQuasiSeparated U.carrier)
    {f g s : Γ(X, U)} (hfg : f |_ X.basicOpen s = g |_ X.basicOpen s) :
    exists n, s ^ n * f = s ^ n * g := by
  obtain ⟨n, hc⟩ := (isLocalization_basicOpen_of_qcqs hU hU' s).exists_of_eq s hfg
  use n

/--
lemma `exists_of_res_eq_of_qcqs_of_top` / 引理 `exists_of_res_eq_of_qcqs_of_top`

English:
lemma exists_of_res_eq_of_qcqs_of_top
  statement: {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  proof: exists_of_res_eq_of_qcqs (U := ⊤) CompactSpace.isCompact_univ isQuasiSeparated_univ hfg

中文:
引理 exists_of_res_eq_of_qcqs_of_top
  结论: {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  证明: exists_of_res_eq_of_qcqs (U := ⊤) CompactSpace.isCompact_univ isQuasiSeparated_univ hfg

Depends on / 依赖: Classical, Classical.arbitrary, CompactSpace, CompactSpace.isCompact_univ, arbitrary, exists_of_res_eq_of_qcqs, isCompact_univ, isQuasiSeparated_univ
-/
lemma exists_of_res_eq_of_qcqs_of_top {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {f g s : Γ(X, ⊤)} (hfg : f |_ X.basicOpen s = g |_ X.basicOpen s) :
    exists n, s ^ n * f = s ^ n * g :=
  exists_of_res_eq_of_qcqs (U := ⊤) CompactSpace.isCompact_univ isQuasiSeparated_univ hfg

/--
lemma `exists_of_res_zero_of_qcqs` / 引理 `exists_of_res_zero_of_qcqs`

English:
lemma exists_of_res_zero_of_qcqs
  statement: {X : Scheme.{u}} {U : TopologicalSpace.Opens X}
  proof: by
  suffices h : exists n, s ^ n * f = s ^ n * 0 by
    simpa using h
  apply exists_of_res_eq_of_qcqs hU hU'
  simpa

中文:
引理 exists_of_res_zero_of_qcqs
  结论: {X : Scheme.{u}} {U : TopologicalSpace.Opens X}
  证明: by
  suffices h : exists n, s ^ n * f = s ^ n * 0 by
    simpa using h
  apply exists_of_res_eq_of_qcqs hU hU'
  simpa

Depends on / 依赖: SimplexCategory, SimplexCategory.const, exists_of_res_eq_of_qcqs, objEquiv, stdSimplex, stdSimplex.objEquiv.symm
-/
lemma exists_of_res_zero_of_qcqs {X : Scheme.{u}} {U : TopologicalSpace.Opens X}
    (hU : IsCompact U.carrier) (hU' : IsQuasiSeparated U.carrier)
    {f s : Γ(X, U)} (hf : f |_ X.basicOpen s = 0) :
    exists n, s ^ n * f = 0 := by
  suffices h : exists n, s ^ n * f = s ^ n * 0 by
    simpa using h
  apply exists_of_res_eq_of_qcqs hU hU'
  simpa

/--
lemma `exists_of_res_zero_of_qcqs_of_top` / 引理 `exists_of_res_zero_of_qcqs_of_top`

English:
lemma exists_of_res_zero_of_qcqs_of_top
  statement: {X : Scheme} [CompactSpace X] [QuasiSeparatedSpace X]
  proof: exists_of_res_zero_of_qcqs (U := ⊤) CompactSpace.isCompact_univ isQuasiSeparated_univ hf

中文:
引理 exists_of_res_zero_of_qcqs_of_top
  结论: {X : Scheme} [CompactSpace X] [QuasiSeparatedSpace X]
  证明: exists_of_res_zero_of_qcqs (U := ⊤) CompactSpace.isCompact_univ isQuasiSeparated_univ hf

Depends on / 依赖: CompactSpace, CompactSpace.isCompact_univ, exists_of_res_zero_of_qcqs, isCompact_univ, isQuasiSeparated_univ
-/
lemma exists_of_res_zero_of_qcqs_of_top {X : Scheme} [CompactSpace X] [QuasiSeparatedSpace X]
    {f s : Γ(X, ⊤)} (hf : f |_ X.basicOpen s = 0) :
    exists n, s ^ n * f = 0 :=
  exists_of_res_zero_of_qcqs (U := ⊤) CompactSpace.isCompact_univ isQuasiSeparated_univ hf

set_option backward.isDefEq.respectTransparency false in
/--
Instance `isIso_ΓSpec_adjunction_unit_app_basicOpen` / 实例 `isIso_ΓSpec_adjunction_unit_app_basicOpen`

English:
instance isIso_ΓSpec_adjunction_unit_app_basicOpen
  body: by
  refine @IsIso.of_isIso_comp_right _ _ _ _ _ _ (X.presheaf.map
    (eqToHom (Scheme.toSpecΓ_preimage_basicOpen _ _).symm).op) _ ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  apply +allowSynthFailures IsLocalization.bijective
  · exact StructureSheaf.IsLocalization.to_basicOpen _ _
  · refine 

中文:
实例 isIso_ΓSpec_adjunction_unit_app_basicOpen
  定义体: by
  refine @IsIso.of_isIso_comp_right _ _ _ _ _ _ (X.presheaf.map
    (eqToHom (Scheme.toSpecΓ_preimage_basicOpen _ _).symm).op) _ ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  apply +allowSynthFailures IsLocalization.bijective
  · exact StructureSheaf.IsLocalization.to_basicOpen _ _
  · refine 

Depends on / 依赖: CommRingCat, CommRingCat.hom_comp, ConcreteCategory, ConcreteCategory.isIso_iff_bijective, Functor, Functor.map_comp, IsIso.of_isIso_comp_right, IsLocalization, IsLocalization.bijective, RingHom, RingHom.algebraMap_toAlgebra, Scheme, Scheme.toSpec, StructureSheaf, StructureSheaf.IsLocalization.to_basicOpen, X.presheaf.map, algebraMap_toAlgebra, allowSynthFailures, bijective, eqToHom
-/
instance isIso_ΓSpec_adjunction_unit_app_basicOpen
    [CompactSpace X] [QuasiSeparatedSpace X] (f : Γ(X, ⊤)) :
    IsIso (X.toSpecΓ.app (PrimeSpectrum.basicOpen f)) := by
  refine @IsIso.of_isIso_comp_right _ _ _ _ _ _ (X.presheaf.map
    (eqToHom (Scheme.toSpecΓ_preimage_basicOpen _ _).symm).op) _ ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  apply +allowSynthFailures IsLocalization.bijective
  · exact StructureSheaf.IsLocalization.to_basicOpen _ _
  · refine isLocalization_basicOpen_of_qcqs ?_ ?_ _
    · exact isCompact_univ
    · exact isQuasiSeparated_univ
  · simp [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, RingHom.algebraMap_toAlgebra,
      ← Functor.map_comp]

end AlgebraicGeometry
