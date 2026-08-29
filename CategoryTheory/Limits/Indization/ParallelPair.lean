/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Comma.Final
public import Mathlib.CategoryTheory.Limits.Indization.IndObject

/-!
# Parallel pairs of natural transformations between ind-objects

We show that if `A` and `B` are ind-objects and `f` and `g` are natural transformations between
`A` and `B`, then there is a small filtered category `I` such that `A`, `B`, `f` and `g` are
commonly presented by diagrams and natural transformations in `I ⥤ C`.


## References
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Proposition 6.1.15 (though
  our proof is more direct).
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]

/--
Definition of `IndParallelPairPresentation` / `IndParallelPairPresentation` 的定义

English:
structure IndParallelPairPresentation
  parameters: {A B : Cᵒᵖ ⥤ Type v₁} (f g : A ⟶ B)
  axioms and operations (13):
    - I : Type v₁
    - [ℐ : SmallCategory I]
    - [hI : IsFiltered I]
    - F₁ : I ⥤ C
    - F₂ : I ⥤ C
    - ι₁ : F₁ ⋙ yoneda ⟶ (Functor.const I).obj A
    - isColimit₁ : IsColimit (Cocone.mk A ι₁)
    - ι₂ : F₂ ⋙ yoneda ⟶ (Functor.const I).obj B
    - isColimit₂ : IsColimit (Cocone.mk B ι₂)
    - φ : F₁ ⟶ F₂
    - ψ : F₁ ⟶ F₂
    - hf : f = IsColimit.map isColimit₁ (Cocone.mk B ι₂) (whiskerRight φ yoneda)
    - hg : g = IsColimit.map isColimit₁ (Cocone.mk B ι₂) (whiskerRight ψ yoneda)

中文:
结构 IndParallelPairPresentation
  参数: {A B : Cᵒᵖ ⥤ 类型v₁} (f g : A ⟶ B)
  公理与运算 (13 个):
    - I : 类型v₁
    - [ℐ : 小范畴 I]
    - [hI : 是Filtered I]
    - F₁ : I ⥤ C
    - F₂ : I ⥤ C
    - ι₁ : F₁ ⋙ yoneda ⟶ (函子.const I).obj A
    - isColimit₁ : 是余极限 (余锥.mk A ι₁)
    - ι₂ : F₂ ⋙ yoneda ⟶ (函子.const I).obj B
    - isColimit₂ : 是余极限 (余锥.mk B ι₂)
    - φ : F₁ ⟶ F₂
    - ψ : F₁ ⟶ F₂
    - hf : f = 是余极限.map isColimit₁ (余锥.mk B ι₂) (whiskerRight φ yoneda)
    - hg : g = 是余极限.map isColimit₁ (余锥.mk B ι₂) (whiskerRight ψ yoneda)
-/
structure IndParallelPairPresentation {A B : Cᵒᵖ ⥤ Type v₁} (f g : A ⟶ B) where
  /-- The indexing category. -/
  I : Type v₁
  /-- Category instance on the indexing category. -/
  [ℐ : SmallCategory I]
  [hI : IsFiltered I]
  /-- The diagram presenting `A`. -/
  F₁ : I ⥤ C
  /-- The diagram presenting `B`. -/
  F₂ : I ⥤ C
  /-- The cocone on `F₁` with apex `A`. -/
  ι₁ : F₁ ⋙ yoneda ⟶ (Functor.const I).obj A
  /-- The cocone on `F₁` with apex `A` is a colimit cocone. -/
  isColimit₁ : IsColimit (Cocone.mk A ι₁)
  /-- The cocone on `F₂` with apex `B`. -/
  ι₂ : F₂ ⋙ yoneda ⟶ (Functor.const I).obj B
  /-- The cocone on `F₂` with apex `B` is a colimit cocone. -/
  isColimit₂ : IsColimit (Cocone.mk B ι₂)
  /-- The natural transformation presenting `f`. -/
  φ : F₁ ⟶ F₂
  /-- The natural transformation presenting `g`. -/
  ψ : F₁ ⟶ F₂
  /-- `f` is in fact presented by `φ`. -/
  hf : f = IsColimit.map isColimit₁ (Cocone.mk B ι₂) (whiskerRight φ yoneda)
  /-- `g` is in fact presented by `ψ`. -/
  hg : g = IsColimit.map isColimit₁ (Cocone.mk B ι₂) (whiskerRight ψ yoneda)

instance {A B : Cᵒᵖ ⥤ Type v₁} {f g : A ⟶ B} (P : IndParallelPairPresentation f g) :
    SmallCategory P.I := P.ℐ
instance {A B : Cᵒᵖ ⥤ Type v₁} {f g : A ⟶ B} (P : IndParallelPairPresentation f g) :
    IsFiltered P.I := P.hI

namespace NonemptyParallelPairPresentationAux

variable {A B : Cᵒᵖ ⥤ Type v₁} (f g : A ⟶ B) (P₁ : IndObjectPresentation A)
  (P₂ : IndObjectPresentation B)

/--
Definition of `K` / `K` 的定义

English:
abbreviation K
  signature: : Type v₁
  body: Comma ((P₁.toCostructuredArrow ⋙ CostructuredArrow.map f).prod'
    (P₁.toCostructuredArrow ⋙ CostructuredArrow.map g))
    (P₂.toCostructuredArrow.prod' P₂.toCostructuredArrow)

中文:
缩写 K
  签名: : 类型v₁
  定义体: Comma ((P₁.toCostructuredArrow ⋙ CostructuredArrow.map f).prod'
    (P₁.toCostructuredArrow ⋙ CostructuredArrow.map g))
    (P₂.toCostructuredArrow.prod' P₂.toCostructuredArrow)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.map, toCostructuredArrow, toCostructuredArrow.prod
-/
abbrev K : Type v₁ :=
  Comma ((P₁.toCostructuredArrow ⋙ CostructuredArrow.map f).prod'
    (P₁.toCostructuredArrow ⋙ CostructuredArrow.map g))
    (P₂.toCostructuredArrow.prod' P₂.toCostructuredArrow)

/--
Definition of `F₁` / `F₁` 的定义

English:
abbreviation F₁
  signature: : K f g P₁ P₂ ⥤ C
  body: Comma.fst _ _ ⋙ P₁.F

中文:
缩写 F₁
  签名: : K f g P₁ P₂ ⥤ C
  定义体: Comma.fst _ _ ⋙ P₁.F

Depends on / 依赖: Comma.fst
-/
abbrev F₁ : K f g P₁ P₂ ⥤ C := Comma.fst _ _ ⋙ P₁.F
/--
Definition of `F₂` / `F₂` 的定义

English:
abbreviation F₂
  signature: : K f g P₁ P₂ ⥤ C
  body: Comma.snd _ _ ⋙ P₂.F

中文:
缩写 F₂
  签名: : K f g P₁ P₂ ⥤ C
  定义体: Comma.snd _ _ ⋙ P₂.F

Depends on / 依赖: Comma.snd
-/
abbrev F₂ : K f g P₁ P₂ ⥤ C := Comma.snd _ _ ⋙ P₂.F

/--
Definition of `ι₁` / `ι₁` 的定义

English:
abbreviation ι₁
  signature: : F₁ f g P₁ P₂ ⋙ yoneda ⟶ (Functor.const (K f g P₁ P₂)).obj A
  body: whiskerLeft (Comma.fst _ _) P₁.ι

中文:
缩写 ι₁
  签名: : F₁ f g P₁ P₂ ⋙ yoneda ⟶ (函子.const (K f g P₁ P₂)).obj A
  定义体: whiskerLeft (Comma.fst _ _) P₁.ι

Depends on / 依赖: Comma.fst, Iso.refl, hasSmallLocalizedHom_iff_of_isos, shiftFunctorZero, whiskerLeft
-/
abbrev ι₁ : F₁ f g P₁ P₂ ⋙ yoneda ⟶ (Functor.const (K f g P₁ P₂)).obj A :=
  whiskerLeft (Comma.fst _ _) P₁.ι

/--
Definition of `isColimit₁` / `isColimit₁` 的定义

English:
abbreviation isColimit₁
  signature: : IsColimit (Cocone.mk A (ι₁ f g P₁ P₂))
  body: (Functor.Final.isColimitWhiskerEquiv _ _).symm P₁.isColimit

中文:
缩写 isColimit₁
  签名: : 是余极限 (余锥.mk A (ι₁ f g P₁ P₂))
  定义体: (Functor.Final.isColimitWhiskerEquiv _ _).symm P₁.isColimit

Depends on / 依赖: Functor, Functor.Final.isColimitWhiskerEquiv, Iso.refl, hasSmallLocalizedHom_iff_of_isos, isColimit, isColimitWhiskerEquiv, shiftFunctorZero
-/
noncomputable abbrev isColimit₁ : IsColimit (Cocone.mk A (ι₁ f g P₁ P₂)) :=
  (Functor.Final.isColimitWhiskerEquiv _ _).symm P₁.isColimit

/--
Definition of `ι₂` / `ι₂` 的定义

English:
abbreviation ι₂
  signature: : F₂ f g P₁ P₂ ⋙ yoneda ⟶ (Functor.const (K f g P₁ P₂)).obj B
  body: whiskerLeft (Comma.snd _ _) P₂.ι

中文:
缩写 ι₂
  签名: : F₂ f g P₁ P₂ ⋙ yoneda ⟶ (函子.const (K f g P₁ P₂)).obj B
  定义体: whiskerLeft (Comma.snd _ _) P₂.ι

Depends on / 依赖: Comma.snd, Iso.refl, hasSmallLocalizedHom_iff_of_isos, shiftFunctorAdd, whiskerLeft
-/
abbrev ι₂ : F₂ f g P₁ P₂ ⋙ yoneda ⟶ (Functor.const (K f g P₁ P₂)).obj B :=
  whiskerLeft (Comma.snd _ _) P₂.ι

/--
Definition of `isColimit₂` / `isColimit₂` 的定义

English:
abbreviation isColimit₂
  signature: : IsColimit (Cocone.mk B (ι₂ f g P₁ P₂))
  body: (Functor.Final.isColimitWhiskerEquiv _ _).symm P₂.isColimit

中文:
缩写 isColimit₂
  签名: : 是余极限 (余锥.mk B (ι₂ f g P₁ P₂))
  定义体: (Functor.Final.isColimitWhiskerEquiv _ _).symm P₂.isColimit

Depends on / 依赖: Functor, Functor.Final.isColimitWhiskerEquiv, Iso.refl, hasSmallLocalizedHom_iff_of_isos, isColimit, isColimitWhiskerEquiv, shiftFunctorAdd
-/
noncomputable abbrev isColimit₂ : IsColimit (Cocone.mk B (ι₂ f g P₁ P₂)) :=
  (Functor.Final.isColimitWhiskerEquiv _ _).symm P₂.isColimit

/--
Definition of `ϕ` / `ϕ` 的定义

English:
definition ϕ
  signature: : F₁ f g P₁ P₂ ⟶ F₂ f g P₁ P₂ where
  body: h.hom.1.left
  naturality _ _ h := by
    have := h.w
    simp only [prod'_map, Functor.comp_map, Prod.hom_ext_iff,
      CostructuredArrow.hom_eq_iff] at this
    exact this.1

中文:
定义 ϕ
  签名: : F₁ f g P₁ P₂ ⟶ F₂ f g P₁ P₂ where
  定义体: h.hom.1.left
  naturality _ _ h := by
    have := h.w
    simp only [prod'_map, Functor.comp_map, Prod.hom_ext_iff,
      CostructuredArrow.hom_eq_iff] at this
    exact this.1

Depends on / 依赖: h.hom
-/
def ϕ : F₁ f g P₁ P₂ ⟶ F₂ f g P₁ P₂ where
  app h := h.hom.1.left
  naturality _ _ h := by
    have := h.w
    simp only [prod'_map, Functor.comp_map, Prod.hom_ext_iff,
      CostructuredArrow.hom_eq_iff] at this
    exact this.1

set_option backward.defeqAttrib.useBackward true in
/--
theorem `hf` / 定理 `hf`

English:
theorem hf
  statement: f = IsColimit.map (isColimit₁ f g P₁ P₂)
  proof: by
  refine (isColimit₁ f g P₁ P₂).hom_ext (fun i => ?_)
  rw [IsColimit.ι_map]
  simpa using! i.hom.1.w.symm

中文:
定理 hf
  结论: f = 是余极限.map (isColimit₁ f g P₁ P₂)
  证明: by
  refine (isColimit₁ f g P₁ P₂).hom_ext (fun i => ?_)
  rw [IsColimit.ι_map]
  simpa using! i.hom.1.w.symm

Depends on / 依赖: IsColimit, hom_ext, i.hom, w.symm
-/
theorem hf : f = IsColimit.map (isColimit₁ f g P₁ P₂)
    (Cocone.mk B (ι₂ f g P₁ P₂)) (whiskerRight (ϕ f g P₁ P₂) yoneda) := by
  refine (isColimit₁ f g P₁ P₂).hom_ext (fun i => ?_)
  rw [IsColimit.ι_map]
  simpa using! i.hom.1.w.symm

/--
Definition of `ψ` / `ψ` 的定义

English:
definition ψ
  signature: : F₁ f g P₁ P₂ ⟶ F₂ f g P₁ P₂ where
  body: h.hom.2.left
  naturality _ _ h := by
    have := h.w
    simp only [prod'_map, Functor.comp_map, Prod.hom_ext_iff,
      CostructuredArrow.hom_eq_iff] at this
    exact this.2

中文:
定义 ψ
  签名: : F₁ f g P₁ P₂ ⟶ F₂ f g P₁ P₂ where
  定义体: h.hom.2.left
  naturality _ _ h := by
    have := h.w
    simp only [prod'_map, Functor.comp_map, Prod.hom_ext_iff,
      CostructuredArrow.hom_eq_iff] at this
    exact this.2

Depends on / 依赖: h.hom
-/
def ψ : F₁ f g P₁ P₂ ⟶ F₂ f g P₁ P₂ where
  app h := h.hom.2.left
  naturality _ _ h := by
    have := h.w
    simp only [prod'_map, Functor.comp_map, Prod.hom_ext_iff,
      CostructuredArrow.hom_eq_iff] at this
    exact this.2

set_option backward.defeqAttrib.useBackward true in
/--
theorem `hg` / 定理 `hg`

English:
theorem hg
  statement: g = IsColimit.map (isColimit₁ f g P₁ P₂)
  proof: by
  refine (isColimit₁ f g P₁ P₂).hom_ext (fun i => ?_)
  rw [IsColimit.ι_map]
  simpa using! i.hom.2.w.symm

中文:
定理 hg
  结论: g = 是余极限.map (isColimit₁ f g P₁ P₂)
  证明: by
  refine (isColimit₁ f g P₁ P₂).hom_ext (fun i => ?_)
  rw [IsColimit.ι_map]
  simpa using! i.hom.2.w.symm

Depends on / 依赖: IsColimit, hom_ext, i.hom, w.symm
-/
theorem hg : g = IsColimit.map (isColimit₁ f g P₁ P₂)
    (Cocone.mk B (ι₂ f g P₁ P₂)) (whiskerRight (ψ f g P₁ P₂) yoneda) := by
  refine (isColimit₁ f g P₁ P₂).hom_ext (fun i => ?_)
  rw [IsColimit.ι_map]
  simpa using! i.hom.2.w.symm

attribute [local instance] Comma.isFiltered_of_final in
/--
Definition of `presentation` / `presentation` 的定义

English:
definition presentation
  signature: : IndParallelPairPresentation f g where
  body: K f g P₁ P₂
  F₁ := F₁ f g P₁ P₂
  F₂ := F₂ f g P₁ P₂
  ι₁ := ι₁ f g P₁ P₂
  isColimit₁ := isColimit₁ f g P₁ P₂
  ι₂ := ι₂ f g P₁ P₂
  isColimit₂ := isColimit₂ f g P₁ P₂
  φ := ϕ f g P₁ P₂
  ψ := ψ f g P₁ P₂
  hf := hf f g P₁ P₂
  hg := hg f g P₁ P₂

中文:
定义 presentation
  签名: : IndParallelPairPresentation f g where
  定义体: K f g P₁ P₂
  F₁ := F₁ f g P₁ P₂
  F₂ := F₂ f g P₁ P₂
  ι₁ := ι₁ f g P₁ P₂
  isColimit₁ := isColimit₁ f g P₁ P₂
  ι₂ := ι₂ f g P₁ P₂
  isColimit₂ := isColimit₂ f g P₁ P₂
  φ := ϕ f g P₁ P₂
  ψ := ψ f g P₁ P₂
  hf := hf f g P₁ P₂
  hg := hg f g P₁ P₂
-/
noncomputable def presentation : IndParallelPairPresentation f g where
  I := K f g P₁ P₂
  F₁ := F₁ f g P₁ P₂
  F₂ := F₂ f g P₁ P₂
  ι₁ := ι₁ f g P₁ P₂
  isColimit₁ := isColimit₁ f g P₁ P₂
  ι₂ := ι₂ f g P₁ P₂
  isColimit₂ := isColimit₂ f g P₁ P₂
  φ := ϕ f g P₁ P₂
  ψ := ψ f g P₁ P₂
  hf := hf f g P₁ P₂
  hg := hg f g P₁ P₂

end NonemptyParallelPairPresentationAux

/--
theorem `nonempty_indParallelPairPresentation` / 定理 `nonempty_indParallelPairPresentation`

English:
theorem nonempty_indParallelPairPresentation
  statement: {A B : Cᵒᵖ ⥤ Type v₁} (hA : IsIndObject A)
  proof: ⟨NonemptyParallelPairPresentationAux.presentation f g hA.presentation hB.presentation⟩

中文:
定理 nonempty_indParallelPairPresentation
  结论: {A B : Cᵒᵖ ⥤ 类型v₁} (hA : 是IndObject A)
  证明: ⟨NonemptyParallelPairPresentationAux.presentation f g hA.presentation hB.presentation⟩

Depends on / 依赖: NonemptyParallelPairPresentationAux, NonemptyParallelPairPresentationAux.presentation, hA.presentation, hB.presentation, presentation
-/
theorem nonempty_indParallelPairPresentation {A B : Cᵒᵖ ⥤ Type v₁} (hA : IsIndObject A)
    (hB : IsIndObject B) (f g : A ⟶ B) : Nonempty (IndParallelPairPresentation f g) :=
  ⟨NonemptyParallelPairPresentationAux.presentation f g hA.presentation hB.presentation⟩

namespace IndParallelPairPresentation

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `parallelPairIsoParallelPairCompYoneda` / `parallelPairIsoParallelPairCompYoneda` 的定义

English:
definition parallelPairIsoParallelPairCompYoneda
  signature: {A B : Cᵒᵖ ⥤ Type v₁} {f g : A ⟶ B}
  body: parallelPair.ext
    (P.isColimit₁.coconePointUniqueUpToIso (colimit.isColimit _))
    (P.isColimit₂.coconePointUniqueUpToIso (colimit.isColimit _))
    (P.isColimit₁.hom_ext (fun j => by
      simp [P.hf, P.isColimit₁.ι_map_assoc, P.isColimit₁.comp_coconePointUniqueUpToIso_hom_assoc,
        P.isCo

中文:
定义 parallelPairIsoParallelPairCompYoneda
  签名: {A B : Cᵒᵖ ⥤ 类型v₁} {f g : A ⟶ B}
  定义体: parallelPair.ext
    (P.isColimit₁.coconePointUniqueUpToIso (colimit.isColimit _))
    (P.isColimit₂.coconePointUniqueUpToIso (colimit.isColimit _))
    (P.isColimit₁.hom_ext (fun j => by
      simp [P.hf, P.isColimit₁.ι_map_assoc, P.isColimit₁.comp_coconePointUniqueUpToIso_hom_assoc,
        P.isCo

Depends on / 依赖: P.hf, P.hg, P.isColimit, coconePointUniqueUpToIso, colimit, colimit.isColimit, comp_coconePointUniqueUpToIso_hom, comp_coconePointUniqueUpToIso_hom_assoc, hom_ext, isColimit, parallelPair, parallelPair.ext
-/
noncomputable def parallelPairIsoParallelPairCompYoneda {A B : Cᵒᵖ ⥤ Type v₁} {f g : A ⟶ B}
    (P : IndParallelPairPresentation f g) :
    parallelPair f g ≅ parallelPair P.φ P.ψ ⋙ (whiskeringRight _ _ _).obj yoneda ⋙ colim :=
  parallelPair.ext
    (P.isColimit₁.coconePointUniqueUpToIso (colimit.isColimit _))
    (P.isColimit₂.coconePointUniqueUpToIso (colimit.isColimit _))
    (P.isColimit₁.hom_ext (fun j => by
      simp [P.hf, P.isColimit₁.ι_map_assoc, P.isColimit₁.comp_coconePointUniqueUpToIso_hom_assoc,
        P.isColimit₂.comp_coconePointUniqueUpToIso_hom]))
    (P.isColimit₁.hom_ext (fun j => by
      simp [P.hg, P.isColimit₁.ι_map_assoc, P.isColimit₁.comp_coconePointUniqueUpToIso_hom_assoc,
        P.isColimit₂.comp_coconePointUniqueUpToIso_hom]))

end IndParallelPairPresentation

end CategoryTheory
