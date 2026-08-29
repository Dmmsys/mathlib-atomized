/-
Copyright (c) 2026 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module

public import Mathlib.CategoryTheory.Abelian.Preradical.Basic
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Square

/-!
# The colon construction on preradicals

Given preradicals `Φ` and `Ψ` on an abelian category `C`, this file defines their **colon** `Φ : Ψ`
in the sense of Stenström. Following Stenström, one can realize the colon object `r : s` evaluated
at `X : C` as the pullback of `X ⟶ X / r X` along `s (X / r X) ⟶ X / r X`. We encode this
categorically by constructing `Φ : Ψ` as a pullback in the category of endofunctors of the canonical
projection `Φ.π : 𝟭 C ⟶ Φ.quotient` along
`Φ.quotient.whiskerLeft Ψ.ι ≫ Φ.quotient.rightUnitor.hom : Φ.quotient ⋙ Ψ.r ⟶ Φ.quotient`.

## Main definitions

* `Preradical.colon Φ Ψ : Preradical C` : The colon preradical `Φ : Ψ` of Stenström.
* `toColon Φ Ψ : Φ ⟶ Φ.colon Ψ` : The canonical inclusion of the left preradical into the colon.

## Main results

* `isIso_toColon_iff` : The morphism `toColon Φ Ψ` is an isomorphism if and only if `Ψ` kills
quotients in the sense that `Φ.quotient ⋙ Ψ.r` is the zero object.

## References

* [Bo Stenström, Rings and Modules of Quotients][stenstrom1971]
* [Bo Stenström, *Rings of Quotients*][stenstrom1975]

## Tags

category theory, preradical, colon, pullback, torsion theory
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory.Abelian

open CategoryTheory.Limits

variable {C : Type*} [Category C] [Abelian C]

namespace Preradical

variable (Φ Ψ : Preradical C)

/--
Definition of `quotient` / `quotient` 的定义

English:
abbreviation quotient
  signature: : C ⥤ C
  body: cokernel Φ.ι

中文:
缩写 quotient
  签名: : C ⥤ C
  定义体: cokernel Φ.ι

Depends on / 依赖: cokernel
-/
noncomputable abbrev quotient : C ⥤ C := cokernel Φ.ι

/--
Definition of `π` / `π` 的定义

English:
definition π
  signature: : 𝟭 C ⟶ Φ.quotient
  body: cokernel.π Φ.ι
  deriving Epi

@[reassoc (attr := simp)]

中文:
定义 π
  签名: : 𝟭 C ⟶ Φ.quotient
  定义体: cokernel.π Φ.ι
  deriving Epi

@[reassoc (attr := simp)]

Depends on / 依赖: cokernel
-/
noncomputable def π : 𝟭 C ⟶ Φ.quotient := cokernel.π Φ.ι
  deriving Epi

@[reassoc (attr := simp)]
/--
lemma `ι_π` / 引理 `ι_π`

English:
lemma ι_π
  statement: Φ.ι ≫ Φ.π = 0
  proof: cokernel.condition _

中文:
引理 ι_π
  结论: Φ.ι ≫ Φ.π = 0
  证明: cokernel.condition _

Depends on / 依赖: cokernel, cokernel.condition, condition
-/
lemma ι_π : Φ.ι ≫ Φ.π = 0 := cokernel.condition _

/--
Definition of `isColimitCokernelCofork` / `isColimitCokernelCofork` 的定义

English:
definition isColimitCokernelCofork
  signature: : IsColimit (CokernelCofork.ofπ _ Φ.ι_π)
  body: cokernelIsCokernel _

中文:
定义 isColimitCokernelCofork
  签名: : IsColimit (CokernelCofork.ofπ _ Φ.ι_π)
  定义体: cokernelIsCokernel _

Depends on / 依赖: cokernelIsCokernel
-/
noncomputable def isColimitCokernelCofork : IsColimit (CokernelCofork.ofπ _ Φ.ι_π) :=
  cokernelIsCokernel _

/-- The short complex `Φ.r ⟶ 𝟭 C ⟶ Φ.quotient` in the functor category associated to a preradical
`Φ`. -/
@[simps]
/--
Definition of `shortComplex` / `shortComplex` 的定义

English:
definition shortComplex
  signature: : ShortComplex (C ⥤ C) where
  body: Φ.ι
  g := Φ.π

中文:
定义 shortComplex
  签名: : ShortComplex (C ⥤ C) where
  定义体: Φ.ι
  g := Φ.π
-/
noncomputable def shortComplex : ShortComplex (C ⥤ C) where
  f := Φ.ι
  g := Φ.π

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono Φ.shortComplex.f
  body: by dsimp; infer_instance

中文:
实例 :
  签名: Mono Φ.shortComplex.f
  定义体: by dsimp; infer_instance

Depends on / 依赖: L.obj, infer_instance, isIso_hom_app, isPointwiseRightKanExtensionRanCounit
-/
instance : Mono Φ.shortComplex.f := by dsimp; infer_instance
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi Φ.shortComplex.g
  body: by dsimp; infer_instance

中文:
实例 :
  签名: Epi Φ.shortComplex.g
  定义体: by dsimp; infer_instance

Depends on / 依赖: NatIso, NatIso.isIso_of_isIso_app, infer_instance, isIso_of_isIso_app
-/
instance : Epi Φ.shortComplex.g := by dsimp; infer_instance

/--
lemma `shortExact_shortComplex` / 引理 `shortExact_shortComplex`

English:
lemma shortExact_shortComplex
  statement: Φ.shortComplex.ShortExact where
  proof: ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)

中文:
引理 shortExact_shortComplex
  结论: Φ.shortComplex.ShortExact where
  证明: ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)

Depends on / 依赖: ShortComplex, ShortComplex.exact_of_g_is_cokernel, cokernelIsCokernel, exact_of_g_is_cokernel
-/
lemma shortExact_shortComplex : Φ.shortComplex.ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)

/--
Definition of `isLimitKernelFork` / `isLimitKernelFork` 的定义

English:
definition isLimitKernelFork
  signature: : IsLimit (KernelFork.ofι _ Φ.ι_π)
  body: Φ.shortExact_shortComplex.fIsKernel

@[reassoc (attr := simp)]

中文:
定义 isLimitKernelFork
  签名: : IsLimit (KernelFork.ofι _ Φ.ι_π)
  定义体: Φ.shortExact_shortComplex.fIsKernel

@[reassoc (attr := simp)]

Depends on / 依赖: fIsKernel, infer_instance, ranAdjunction_counit, shortExact_shortComplex, shortExact_shortComplex.fIsKernel
-/
noncomputable def isLimitKernelFork : IsLimit (KernelFork.ofι _ Φ.ι_π) :=
  Φ.shortExact_shortComplex.fIsKernel

@[reassoc (attr := simp)]
/--
lemma `ι_π_app` / 引理 `ι_π_app`

English:
lemma ι_π_app
  given: (X : C)
  statement: Φ.ι.app X ≫ Φ.π.app X = 0
  proof: by
  simp [← NatTrans.comp_app]

中文:
引理 ι_π_app
  条件: (X : C)
  结论: Φ.ι.app X ≫ Φ.π.app X = 0
  证明: by
  simp [← NatTrans.comp_app]

Depends on / 依赖: NatTrans, NatTrans.comp_app, comp_app
-/
lemma ι_π_app (X : C) : Φ.ι.app X ≫ Φ.π.app X = 0 := by
  simp [← NatTrans.comp_app]

/-- For `X : C`, the short complex `Φ.r.obj X ⟶ X ⟶ Φ.quotient.obj X` obtained by evaluating
`Φ.shortComplex` at `X`. -/
@[simps]
/--
Definition of `shortComplexObj` / `shortComplexObj` 的定义

English:
definition shortComplexObj
  signature: (X : C)
  body: Φ.ι.app X
  g := Φ.π.app X

中文:
定义 shortComplexObj
  签名: (X : C)
  定义体: Φ.ι.app X
  g := Φ.π.app X
-/
noncomputable def shortComplexObj (X : C) : ShortComplex C where
  f := Φ.ι.app X
  g := Φ.π.app X

instance (X : C) : Mono (Φ.shortComplexObj X).f := by dsimp; infer_instance

instance (X : C) : Epi (Φ.shortComplexObj X).g := by dsimp; infer_instance

/--
lemma `shortExact_shortComplexObj` / 引理 `shortExact_shortComplexObj`

English:
lemma shortExact_shortComplexObj
  given: (X : C)
  statement: (Φ.shortComplexObj X).ShortExact where
  proof: (ShortComplex.ShortExact.map_of_exact Φ.shortExact_shortComplex ((evaluation C C).obj X)).exact

中文:
引理 shortExact_shortComplexObj
  条件: (X : C)
  结论: (Φ.shortComplexObj X).ShortExact where
  证明: (ShortComplex.ShortExact.map_of_exact Φ.shortExact_shortComplex ((evaluation C C).obj X)).exact

Depends on / 依赖: ShortComplex, ShortComplex.ShortExact.map_of_exact, ShortExact, evaluation, map_of_exact, shortExact_shortComplex
-/
lemma shortExact_shortComplexObj (X : C) : (Φ.shortComplexObj X).ShortExact where
  exact :=
    (ShortComplex.ShortExact.map_of_exact Φ.shortExact_shortComplex ((evaluation C C).obj X)).exact

/--
Definition of `isLimitKernelForkObj` / `isLimitKernelForkObj` 的定义

English:
definition isLimitKernelForkObj
  signature: (X : C)
  body: (Φ.shortExact_shortComplexObj X).fIsKernel

中文:
定义 isLimitKernelForkObj
  签名: (X : C)
  定义体: (Φ.shortExact_shortComplexObj X).fIsKernel

Depends on / 依赖: fIsKernel, shortExact_shortComplexObj
-/
noncomputable def isLimitKernelForkObj (X : C) : IsLimit (KernelFork.ofι _ (Φ.ι_π_app X)) :=
  (Φ.shortExact_shortComplexObj X).fIsKernel

/--
Definition of `isColimitCokernelCoforkObj` / `isColimitCokernelCoforkObj` 的定义

English:
definition isColimitCokernelCoforkObj
  signature: (X : C)
  body: (Φ.shortExact_shortComplexObj X).gIsCokernel

中文:
定义 isColimitCokernelCoforkObj
  签名: (X : C)
  定义体: (Φ.shortExact_shortComplexObj X).gIsCokernel

Depends on / 依赖: gIsCokernel, shortExact_shortComplexObj
-/
noncomputable def isColimitCokernelCoforkObj (X : C) :
    IsColimit (CokernelCofork.ofπ _ (Φ.ι_π_app X)) :=
  (Φ.shortExact_shortComplexObj X).gIsCokernel

open CategoryTheory.Functor

/--
Definition of `colon` / `colon` 的定义

English:
definition colon
  signature: : Preradical C
  body: MonoOver.mk
    (pullback.fst Φ.π (whiskerLeft Φ.quotient Ψ.ι ≫ (rightUnitor _).hom))

中文:
定义 colon
  签名: : Preradical C
  定义体: MonoOver.mk
    (pullback.fst Φ.π (whiskerLeft Φ.quotient Ψ.ι ≫ (rightUnitor _).hom))

Depends on / 依赖: MonoOver, MonoOver.mk, pullback, pullback.fst, quotient, rightUnitor, whiskerLeft
-/
noncomputable def colon : Preradical C :=
  MonoOver.mk
    (pullback.fst Φ.π (whiskerLeft Φ.quotient Ψ.ι ≫ (rightUnitor _).hom))

/--
Definition of `colonπ` / `colonπ` 的定义

English:
definition colonπ
  signature: : (colon Φ Ψ).r ⟶ Φ.quotient ⋙ Ψ.r
  body: pullback.snd _ _

中文:
定义 colonπ
  签名: : (colon Φ Ψ).r ⟶ Φ.quotient ⋙ Ψ.r
  定义体: pullback.snd _ _

Depends on / 依赖: pullback, pullback.snd
-/
noncomputable def colonπ : (colon Φ Ψ).r ⟶ Φ.quotient ⋙ Ψ.r := pullback.snd _ _

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi (colonπ Φ Ψ)
  body: by dsimp [colonπ]; infer_instance

中文:
实例 :
  签名: Epi (colonπ Φ Ψ)
  定义体: by dsimp [colonπ]; infer_instance

Depends on / 依赖: infer_instance
-/
instance : Epi (colonπ Φ Ψ) := by dsimp [colonπ]; infer_instance

instance (X : C) : Epi ((colonπ Φ Ψ).app X) := instEpiAppOfFunctor (Φ.colonπ Ψ) X

/--
lemma `isPullback_colon` / 引理 `isPullback_colon`

English:
lemma isPullback_colon
  proof: .of_hasPullback _ _

中文:
引理 isPullback_colon
  证明: .of_hasPullback _ _

Depends on / 依赖: of_hasPullback
-/
lemma isPullback_colon :
    IsPullback (colon Φ Ψ).ι (colonπ Φ Ψ) Φ.π
      (whiskerLeft Φ.quotient Ψ.ι ≫ (rightUnitor _).hom) :=
  .of_hasPullback _ _

/--
lemma `isPullback_colon_obj` / 引理 `isPullback_colon_obj`

English:
lemma isPullback_colon_obj
  given: (Φ Ψ : Preradical C) (X : C)
  proof: by
  simpa using (isPullback_colon Φ Ψ).map ((evaluation _ _).obj X)

@[reassoc]

中文:
引理 isPullback_colon_obj
  条件: (Φ Ψ : Preradical C) (X : C)
  证明: by
  simpa using (isPullback_colon Φ Ψ).map ((evaluation _ _).obj X)

@[reassoc]

Depends on / 依赖: evaluation, isPullback_colon
-/
lemma isPullback_colon_obj (Φ Ψ : Preradical C) (X : C) :
    IsPullback ((Φ.colon Ψ).ι.app X) ((Φ.colonπ Ψ).app X)
      (Φ.π.app X) (Ψ.ι.app (Φ.quotient.obj X)) := by
  simpa using (isPullback_colon Φ Ψ).map ((evaluation _ _).obj X)

@[reassoc]
/--
lemma `colon_ι_app_π_app` / 引理 `colon_ι_app_π_app`

English:
lemma colon_ι_app_π_app
  given: (Φ Ψ : Preradical C) (X : C)
  proof: (isPullback_colon_obj Φ Ψ X).w

中文:
引理 colon_ι_app_π_app
  条件: (Φ Ψ : Preradical C) (X : C)
  证明: (isPullback_colon_obj Φ Ψ X).w

Depends on / 依赖: isPullback_colon_obj
-/
lemma colon_ι_app_π_app (Φ Ψ : Preradical C) (X : C) :
    (Φ.colon Ψ).ι.app X ≫ Φ.π.app X = (Φ.colonπ Ψ).app X ≫ Ψ.ι.app (Φ.quotient.obj X) :=
  (isPullback_colon_obj Φ Ψ X).w

/--
Definition of `toColon` / `toColon` 的定义

English:
definition toColon
  signature: : Φ ⟶ Φ.colon Ψ
  body: MonoOver.homMk ((isPullback_colon Φ Ψ).lift Φ.ι 0 (by simp))

中文:
定义 toColon
  签名: : Φ ⟶ Φ.colon Ψ
  定义体: MonoOver.homMk ((isPullback_colon Φ Ψ).lift Φ.ι 0 (by simp))

Depends on / 依赖: MonoOver, MonoOver.homMk, isPullback_colon
-/
noncomputable def toColon : Φ ⟶ Φ.colon Ψ :=
  MonoOver.homMk ((isPullback_colon Φ Ψ).lift Φ.ι 0 (by simp))

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `toColon_hom_left_colonπ` / 引理 `toColon_hom_left_colonπ`

English:
lemma toColon_hom_left_colonπ
  proof: by
  simp [toColon]

@[reassoc (attr := simp)]

中文:
引理 toColon_hom_left_colonπ
  证明: by
  simp [toColon]

@[reassoc (attr := simp)]

Depends on / 依赖: toColon
-/
lemma toColon_hom_left_colonπ :
    (toColon Φ Ψ).hom.left ≫ colonπ Φ Ψ = 0 := by
  simp [toColon]

@[reassoc (attr := simp)]
/--
lemma `toColon_hom_left_app_colonπ_app` / 引理 `toColon_hom_left_app_colonπ_app`

English:
lemma toColon_hom_left_app_colonπ_app
  given: (X : C)
  proof: NatTrans.congr_app (toColon_hom_left_colonπ Φ Ψ) X

@[reassoc (attr := simp)]

中文:
引理 toColon_hom_left_app_colonπ_app
  条件: (X : C)
  证明: NatTrans.congr_app (toColon_hom_left_colonπ Φ Ψ) X

@[reassoc (attr := simp)]

Depends on / 依赖: NatTrans, NatTrans.congr_app, congr_app
-/
lemma toColon_hom_left_app_colonπ_app (X : C) :
    (toColon Φ Ψ).hom.left.app X ≫ (colonπ Φ Ψ).app X = 0 :=
  NatTrans.congr_app (toColon_hom_left_colonπ Φ Ψ) X

@[reassoc (attr := simp)]
/--
lemma `toColon_hom_left_app_colon_ι_app` / 引理 `toColon_hom_left_app_colon_ι_app`

English:
lemma toColon_hom_left_app_colon_ι_app
  given: (X : C)
  proof: by
  rw [← NatTrans.comp_app]; rw [Over.w]

中文:
引理 toColon_hom_left_app_colon_ι_app
  条件: (X : C)
  证明: by
  rw [← NatTrans.comp_app]; rw [Over.w]

Depends on / 依赖: NatTrans, NatTrans.comp_app, Over.w, comp_app
-/
lemma toColon_hom_left_app_colon_ι_app (X : C) :
    (Φ.toColon Ψ).hom.left.app X ≫ (Φ.colon Ψ).ι.app X = Φ.ι.app X := by
  rw [← NatTrans.comp_app]; rw [Over.w]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isIso_toColon_hom_left_app_iff` / 定理 `isIso_toColon_hom_left_app_iff`

English:
theorem isIso_toColon_hom_left_app_iff
  given: {Φ Ψ : Preradical C} {X : C}
  proof: by
  constructor <;> intro h
  · exact IsZero.of_epi_eq_zero ((colonπ Φ Ψ).app X)
      (zero_of_epi_comp ((toColon Φ Ψ).hom.left.app X) (by simp))
  · obtain ⟨inv, hinv⟩ :=
      KernelFork.IsLimit.lift' (Φ.isLimitKernelForkObj X) ((colon Φ Ψ).ι.app X) (by
        rw [colon_ι_app_π_app]; rw [h.eq_z

中文:
定理 isIso_toColon_hom_left_app_iff
  条件: {Φ Ψ : Preradical C} {X : C}
  证明: by
  constructor <;> intro h
  · exact IsZero.of_epi_eq_zero ((colonπ Φ Ψ).app X)
      (zero_of_epi_comp ((toColon Φ Ψ).hom.left.app X) (by simp))
  · obtain ⟨inv, hinv⟩ :=
      KernelFork.IsLimit.lift' (Φ.isLimitKernelForkObj X) ((colon Φ Ψ).ι.app X) (by
        rw [colon_ι_app_π_app]; rw [h.eq_z

Depends on / 依赖: IsLimit, IsZero, IsZero.of_epi_eq_zero, KernelFork, KernelFork.IsLimit.lift, cancel_mono, eq_zero_of_tgt, h.eq_zero_of_tgt, hom.left.app, isLimitKernelForkObj, of_epi_eq_zero, toColon, zero_comp, zero_of_epi_comp
-/
theorem isIso_toColon_hom_left_app_iff {Φ Ψ : Preradical C} {X : C} :
    IsIso ((toColon Φ Ψ).hom.left.app X) ↔ IsZero (Ψ.r.obj (Φ.quotient.obj X)) := by
  constructor <;> intro h
  · exact IsZero.of_epi_eq_zero ((colonπ Φ Ψ).app X)
      (zero_of_epi_comp ((toColon Φ Ψ).hom.left.app X) (by simp))
  · obtain ⟨inv, hinv⟩ :=
      KernelFork.IsLimit.lift' (Φ.isLimitKernelForkObj X) ((colon Φ Ψ).ι.app X) (by
        rw [colon_ι_app_π_app]; rw [h.eq_zero_of_tgt ((colonπ Φ Ψ).app X)]; rw [zero_comp])
    dsimp at hinv
    refine ⟨inv, ?_, ?_⟩
    · simp [← cancel_mono (Φ.ι.app X), hinv]
    · simp [← cancel_mono ((Φ.colon Ψ).ι.app X), hinv]

/--
theorem `isIso_toColon_iff` / 定理 `isIso_toColon_iff`

English:
theorem isIso_toColon_iff
  given: {Φ Ψ : Preradical C}
  proof: by
  simpa [MonoOver.isIso_iff_isIso_hom_left, isZero_iff (Φ.quotient ⋙ Ψ.r),
    NatTrans.isIso_iff_isIso_app] using forall_congr' fun x => isIso_toColon_hom_left_app_iff

中文:
定理 isIso_toColon_iff
  条件: {Φ Ψ : Preradical C}
  证明: by
  simpa [MonoOver.isIso_iff_isIso_hom_left, isZero_iff (Φ.quotient ⋙ Ψ.r),
    NatTrans.isIso_iff_isIso_app] using forall_congr' fun x => isIso_toColon_hom_left_app_iff

Depends on / 依赖: MonoOver, MonoOver.isIso_iff_isIso_hom_left, NatTrans, NatTrans.isIso_iff_isIso_app, forall_congr, isIso_iff_isIso_app, isIso_iff_isIso_hom_left, isIso_toColon_hom_left_app_iff, isZero_iff, quotient
-/
theorem isIso_toColon_iff {Φ Ψ : Preradical C} :
    IsIso (toColon Φ Ψ) ↔ IsZero (Φ.quotient ⋙ Ψ.r) := by
  simpa [MonoOver.isIso_iff_isIso_hom_left, isZero_iff (Φ.quotient ⋙ Ψ.r),
    NatTrans.isIso_iff_isIso_app] using forall_congr' fun x => isIso_toColon_hom_left_app_iff

end Preradical

end CategoryTheory.Abelian
