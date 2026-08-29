/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Triangulated.Triangulated

/-!
# Abelian subcategories of triangulated categories

Let `ι : A ⥤ C` be a fully faithful additive functor where `A` is
an additive category and `C` is a triangulated category. We show that `A`
is an abelian category if the following conditions are satisfied:
* For any object `X` and `Y` in `A`, there is no nonzero morphism
  `ι.obj X ⟶ (ι.obj Y)⟦n⟧` when `n < 0`.
* Any morphism `f₁ : X₁ ⟶ X₂` in `A` is admissible, i.e. when
  we complete `ι.obj f₁` in a distinguished triangle
  `ι.obj X₁ ⟶ ι.obj X₂ ⟶ X₃ ⟶ (ι.obj X₁)⟦1⟧`, there exists objects `K`
  and `Q`, and a distinguished triangle `(ι.obj K)⟦1⟧ ⟶ X₃ ⟶ (ι.obj Q) ⟶ ...`.

## References
* [Beilinson, Bernstein, Deligne, Gabber, *Faisceaux pervers*, 1.2][bbd-1982]

-/

@[expose] public section

namespace CategoryTheory

open Category Limits Preadditive ZeroObject Pretriangulated ZeroObject

namespace Triangulated

variable {C A : Type*} [Category* C] [HasZeroObject C] [Preadditive C] [HasShift C Int]
  [forall (n : Int), (shiftFunctor C n).Additive] [Pretriangulated C]
  [Category* A] {ι : A ⥤ C}

namespace AbelianSubcategory

variable (hι : forall ⦃X Y : A⦄ ⦃n : Int⦄ (f : ι.obj X ⟶ (ι.obj Y)⟦n⟧), n < 0 -> f = 0)

set_option backward.isDefEq.respectTransparency false in
include hι in
omit [HasZeroObject C] [Pretriangulated C] in
/--
lemma `eq_zero_of_hom_shift_pos` / 引理 `eq_zero_of_hom_shift_pos`

English:
lemma eq_zero_of_hom_shift_pos
  proof: (shiftFunctor C (-n)).map_injective (by
    rw [← cancel_epi ((shiftEquiv C n).unitIso.hom.app _)]; rw [Functor.map_zero]; rw [comp_zero]
    exact hι _ (by lia))

中文:
引理 eq_zero_of_hom_shift_pos
  证明: (shiftFunctor C (-n)).map_injective (by
    rw [← cancel_epi ((shiftEquiv C n).unitIso.hom.app _)]; rw [Functor.map_zero]; rw [comp_zero]
    exact hι _ (by lia))

Depends on / 依赖: Functor, Functor.map_zero, cancel_epi, comp_zero, map_injective, map_zero, shiftEquiv, shiftFunctor, unitIso, unitIso.hom.app
-/
lemma eq_zero_of_hom_shift_pos
    {X Y : A} {n : Int} (f : (ι.obj X)⟦n⟧ ⟶ ι.obj Y) (hn : 0 < n) :
    f = 0 :=
  (shiftFunctor C (-n)).map_injective (by
    rw [← cancel_epi ((shiftEquiv C n).unitIso.hom.app _)]; rw [Functor.map_zero]; rw [comp_zero]
    exact hι _ (by lia))

section

variable {X₁ X₂ : A} {f₁ : X₁ ⟶ X₂} {X₃ : C} (f₂ : ι.obj X₂ ⟶ X₃) (f₃ : X₃ ⟶ (ι.obj X₁)⟦(1 : Int)⟧)
  (hT : Triangle.mk (ι.map f₁) f₂ f₃ in distTriang C) {K Q : A}
  (α : (ι.obj K)⟦(1 : Int)⟧ ⟶ X₃) (β : X₃ ⟶ (ι.obj Q)) {γ : ι.obj Q ⟶ (ι.obj K)⟦(1 : Int)⟧⟦(1 : Int)⟧}
  (hT' : Triangle.mk α β γ in distTriang C)

variable [ι.Full]

/--
Definition of `ιK` / `ιK` 的定义

English:
definition ιK
  signature: : K ⟶ X₁
  body: (ι ⋙ shiftFunctor C (1 : Int)).preimage (α ≫ f₃)

中文:
定义 ιK
  签名: : K ⟶ X₁
  定义体: (ι ⋙ shiftFunctor C (1 : Int)).preimage (α ≫ f₃)

Depends on / 依赖: preimage, shiftFunctor
-/
noncomputable def ιK : K ⟶ X₁ := (ι ⋙ shiftFunctor C (1 : Int)).preimage (α ≫ f₃)

/--
Definition of `πQ` / `πQ` 的定义

English:
definition πQ
  signature: : X₂ ⟶ Q
  body: ι.preimage (f₂ ≫ β)

omit [Preadditive C] [HasZeroObject C] [forall (n : Int), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
@[simp, reassoc]

中文:
定义 πQ
  签名: : X₂ ⟶ Q
  定义体: ι.preimage (f₂ ≫ β)

omit [Preadditive C] [HasZeroObject C] [forall (n : Int), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
@[simp, reassoc]

Depends on / 依赖: preimage
-/
noncomputable def πQ : X₂ ⟶ Q := ι.preimage (f₂ ≫ β)

omit [Preadditive C] [HasZeroObject C] [forall (n : Int), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
@[simp, reassoc]
/--
lemma `shift_ι_map_ιK` / 引理 `shift_ι_map_ιK`

English:
lemma shift_ι_map_ιK
  proof: (ι ⋙ shiftFunctor C (1 : Int)).map_preimage _

omit [Preadditive C] [HasZeroObject C] [forall (n : Int), (shiftFunctor C n).Additive]
  [Pretriangulated C] [HasShift C Int] in
@[simp, reassoc]

中文:
引理 shift_ι_map_ιK
  证明: (ι ⋙ shiftFunctor C (1 : Int)).map_preimage _

omit [Preadditive C] [HasZeroObject C] [forall (n : Int), (shiftFunctor C n).Additive]
  [Pretriangulated C] [HasShift C Int] in
@[simp, reassoc]

Depends on / 依赖: map_preimage, shiftFunctor
-/
lemma shift_ι_map_ιK :
    (ι.map (ιK f₃ α))⟦(1 : Int)⟧' = α ≫ f₃ :=
  (ι ⋙ shiftFunctor C (1 : Int)).map_preimage _

omit [Preadditive C] [HasZeroObject C] [forall (n : Int), (shiftFunctor C n).Additive]
  [Pretriangulated C] [HasShift C Int] in
@[simp, reassoc]
/--
lemma `ι_map_πQ` / 引理 `ι_map_πQ`

English:
lemma ι_map_πQ
  statement: ι.map (πQ f₂ β) = f₂ ≫ β
  proof: ι.map_preimage _

中文:
引理 ι_map_πQ
  结论: ι.map (πQ f₂ β) = f₂ ≫ β
  证明: ι.map_preimage _

Depends on / 依赖: map_preimage
-/
lemma ι_map_πQ : ι.map (πQ f₂ β) = f₂ ≫ β :=
  ι.map_preimage _

variable {f₂ f₃} [Preadditive A] [ι.Faithful]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hT in
@[reassoc]
/--
lemma `ιK_mor₁` / 引理 `ιK_mor₁`

English:
lemma ιK_mor₁
  statement: ιK f₃ α ≫ f₁ = 0
  proof: (ι ⋙ shiftFunctor C (1 : Int)).map_injective (by
    have := comp_distTriang_mor_zero₃₁ _ hT
    dsimp at this
    simp [this])

中文:
引理 ιK_mor₁
  结论: ιK f₃ α ≫ f₁ = 0
  证明: (ι ⋙ shiftFunctor C (1 : Int)).map_injective (by
    have := comp_distTriang_mor_zero₃₁ _ hT
    dsimp at this
    simp [this])

Depends on / 依赖: map_injective, shiftFunctor
-/
lemma ιK_mor₁ : ιK f₃ α ≫ f₁ = 0 :=
  (ι ⋙ shiftFunctor C (1 : Int)).map_injective (by
    have := comp_distTriang_mor_zero₃₁ _ hT
    dsimp at this
    simp [this])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hT in
@[reassoc]
/--
lemma `mor₁_πQ` / 引理 `mor₁_πQ`

English:
lemma mor₁_πQ
  statement: f₁ ≫ πQ f₂ β = 0
  proof: ι.map_injective (by
    have := comp_distTriang_mor_zero₁₂ _ hT
    dsimp at this
    simp [reassoc_of% this])

中文:
引理 mor₁_πQ
  结论: f₁ ≫ πQ f₂ β = 0
  证明: ι.map_injective (by
    have := comp_distTriang_mor_zero₁₂ _ hT
    dsimp at this
    simp [reassoc_of% this])

Depends on / 依赖: map_injective, reassoc_of
-/
lemma mor₁_πQ : f₁ ≫ πQ f₂ β = 0 :=
  ι.map_injective (by
    have := comp_distTriang_mor_zero₁₂ _ hT
    dsimp at this
    simp [reassoc_of% this])

variable {α β}

include hT hT' hι

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mono_ιK` / 引理 `mono_ιK`

English:
lemma mono_ιK
  statement: Mono (ιK f₃ α)
  proof: by
  rw [mono_iff_cancel_zero]
  intro B k hk
  replace hk := (ι ⋙ shiftFunctor C (1 : Int)).congr_map hk
  apply (ι ⋙ shiftFunctor C (1 : Int)).map_injective
  simp only [Functor.comp_map, Functor.map_comp,
    shift_ι_map_ιK, Functor.map_zero, ← assoc] at hk ⊢
  obtain ⟨l, hl⟩ := Triangle.coyoneda

中文:
引理 mono_ιK
  结论: Mono (ιK f₃ α)
  证明: by
  rw [mono_iff_cancel_zero]
  intro B k hk
  replace hk := (ι ⋙ shiftFunctor C (1 : Int)).congr_map hk
  apply (ι ⋙ shiftFunctor C (1 : Int)).map_injective
  simp only [Functor.comp_map, Functor.map_comp,
    shift_ι_map_ιK, Functor.map_zero, ← assoc] at hk ⊢
  obtain ⟨l, hl⟩ := Triangle.coyoneda

Depends on / 依赖: Functor, Functor.comp_map, Functor.map_comp, Functor.map_zero, Triangle, Triangle.coyoneda_exact, comp_map, congr_map, eq_zero_of_hom_shift_pos, map_comp, map_injective, map_zero, mono_iff_cancel_zero, replace, shiftFunctor, zero_comp
-/
lemma mono_ιK : Mono (ιK f₃ α) := by
  rw [mono_iff_cancel_zero]
  intro B k hk
  replace hk := (ι ⋙ shiftFunctor C (1 : Int)).congr_map hk
  apply (ι ⋙ shiftFunctor C (1 : Int)).map_injective
  simp only [Functor.comp_map, Functor.map_comp,
    shift_ι_map_ιK, Functor.map_zero, ← assoc] at hk ⊢
  obtain ⟨l, hl⟩ := Triangle.coyoneda_exact₃ _ hT _ hk
  rw [eq_zero_of_hom_shift_pos hι l (by lia)]; rw [zero_comp] at hl
  obtain ⟨m, hm⟩ := Triangle.coyoneda_exact₁ _ hT' ((ι.map k)⟦(1 : Int)⟧'⟦(1 : Int)⟧')
    (by simp [← Functor.map_comp, hl])
  obtain rfl : m = 0 := by
    rw [← cancel_epi ((shiftFunctorAdd' C (1 : Int) 1 2 (by lia)).hom.app _)]; rw [comp_zero]
    exact eq_zero_of_hom_shift_pos hι _ (by lia)
  rw [zero_comp] at hm
  exact (shiftFunctor C (1 : Int)).map_injective (by rw [hm, Functor.map_zero])

set_option backward.isDefEq.respectTransparency false in
/--
lemma `epi_πQ` / 引理 `epi_πQ`

English:
lemma epi_πQ
  statement: Epi (πQ f₂ β)
  proof: by
  rw [epi_iff_cancel_zero]
  intro B k hk
  replace hk := ι.congr_map hk
  simp only [Functor.map_comp, ι_map_πQ, assoc, Functor.map_zero] at hk
  obtain ⟨l, hl⟩ := Triangle.yoneda_exact₃ _ hT _ hk
  rw [eq_zero_of_hom_shift_pos hι l (by lia)]; rw [comp_zero] at hl
  obtain ⟨m, hm⟩ := Triangle.yo

中文:
引理 epi_πQ
  结论: Epi (πQ f₂ β)
  证明: by
  rw [epi_iff_cancel_zero]
  intro B k hk
  replace hk := ι.congr_map hk
  simp only [Functor.map_comp, ι_map_πQ, assoc, Functor.map_zero] at hk
  obtain ⟨l, hl⟩ := Triangle.yoneda_exact₃ _ hT _ hk
  rw [eq_zero_of_hom_shift_pos hι l (by lia)]; rw [comp_zero] at hl
  obtain ⟨m, hm⟩ := Triangle.yo

Depends on / 依赖: Functor, Functor.map_comp, Functor.map_zero, Triangle, Triangle.yoneda_exact, cancel_epi, comp_zero, congr_map, epi_iff_cancel_zero, eq_zero_of_hom_shift_pos, hom.app, map_comp, map_injective, map_zero, replace, shiftFunctorAdd
-/
lemma epi_πQ : Epi (πQ f₂ β) := by
  rw [epi_iff_cancel_zero]
  intro B k hk
  replace hk := ι.congr_map hk
  simp only [Functor.map_comp, ι_map_πQ, assoc, Functor.map_zero] at hk
  obtain ⟨l, hl⟩ := Triangle.yoneda_exact₃ _ hT _ hk
  rw [eq_zero_of_hom_shift_pos hι l (by lia)]; rw [comp_zero] at hl
  obtain ⟨m, hm⟩ := Triangle.yoneda_exact₃ _ hT' (ι.map k) hl
  obtain rfl : m = 0 := by
    rw [← cancel_epi ((shiftFunctorAdd' C (1 : Int) 1 2 (by lia)).hom.app _)]; rw [comp_zero]
    exact eq_zero_of_hom_shift_pos hι _ (by lia)
  exact ι.map_injective (by rw [hm, comp_zero, ι.map_zero])

set_option backward.isDefEq.respectTransparency false in
/--
lemma `exists_lift_ιK` / 引理 `exists_lift_ιK`

English:
lemma exists_lift_ιK
  given: {B : A} (x₁ : B ⟶ X₁) (hx₁ : x₁ ≫ f₁ = 0)
  proof: by
  suffices exists (k' : (ι.obj B)⟦(1 : Int)⟧ ⟶ (ι.obj K)⟦(1 : Int)⟧),
      (ι.map x₁)⟦(1 : Int)⟧' = k' ≫ α ≫ f₃ by
    obtain ⟨k', hk'⟩ := this
    refine ⟨(ι ⋙ shiftFunctor C (1 : Int)).preimage k',
      (ι ⋙ shiftFunctor C (1 : Int)).map_injective ?_⟩
    rw [Functor.map_comp]; rw [Functor.ma

中文:
引理 exists_lift_ιK
  条件: {B : A} (x₁ : B ⟶ X₁) (hx₁ : x₁ ≫ f₁ = 0)
  证明: by
  suffices exists (k' : (ι.obj B)⟦(1 : Int)⟧ ⟶ (ι.obj K)⟦(1 : Int)⟧),
      (ι.map x₁)⟦(1 : Int)⟧' = k' ≫ α ≫ f₃ by
    obtain ⟨k', hk'⟩ := this
    refine ⟨(ι ⋙ shiftFunctor C (1 : Int)).preimage k',
      (ι ⋙ shiftFunctor C (1 : Int)).map_injective ?_⟩
    rw [Functor.map_comp]; rw [Functor.ma

Depends on / 依赖: Functor, Functor.comp_map, Functor.map_comp, Functor.map_preimage, Triang, Triangle, Triangle.coyoneda_exact, comp_map, map_comp, map_injective, map_preimage, preimage, shiftFunctor
-/
lemma exists_lift_ιK {B : A} (x₁ : B ⟶ X₁) (hx₁ : x₁ ≫ f₁ = 0) :
    exists (k : B ⟶ K), k ≫ ιK f₃ α = x₁ := by
  suffices exists (k' : (ι.obj B)⟦(1 : Int)⟧ ⟶ (ι.obj K)⟦(1 : Int)⟧),
      (ι.map x₁)⟦(1 : Int)⟧' = k' ≫ α ≫ f₃ by
    obtain ⟨k', hk'⟩ := this
    refine ⟨(ι ⋙ shiftFunctor C (1 : Int)).preimage k',
      (ι ⋙ shiftFunctor C (1 : Int)).map_injective ?_⟩
    rw [Functor.map_comp]; rw [Functor.map_preimage]; rw [Functor.comp_map]; rw [shift_ι_map_ιK]; rw [Functor.comp_map]; rw [hk']
  obtain ⟨x₃, hx₃⟩ := Triangle.coyoneda_exact₁ _ hT ((ι.map x₁)⟦(1 : Int)⟧')
    (by simp [← Functor.map_comp, hx₁])
  obtain ⟨k', hk'⟩ := Triangle.coyoneda_exact₂ _ hT' x₃
    (eq_zero_of_hom_shift_pos hι _ (by lia))
  exact ⟨k', by cat_disch⟩

/--
Definition of `isLimitKernelFork` / `isLimitKernelFork` 的定义

English:
definition isLimitKernelFork
  signature: : IsLimit (KernelFork.ofι _ (ιK_mor₁ hT α))
  body: KernelFork.IsLimit.ofι _ _ _
    (fun x₁ hx₁ => (exists_lift_ιK hι hT hT' x₁ hx₁).choose_spec)
    (fun x₁ hx₁ m hm => by
      have := mono_ιK hι hT hT'
      rw [← cancel_mono (ιK f₃ α)]; rw [(exists_lift_ιK hι hT hT' x₁ hx₁).choose_spec]; rw [hm])

中文:
定义 isLimitKernelFork
  签名: : IsLimit (KernelFork.ofι _ (ιK_mor₁ hT α))
  定义体: KernelFork.IsLimit.ofι _ _ _
    (fun x₁ hx₁ => (exists_lift_ιK hι hT hT' x₁ hx₁).choose_spec)
    (fun x₁ hx₁ m hm => by
      have := mono_ιK hι hT hT'
      rw [← cancel_mono (ιK f₃ α)]; rw [(exists_lift_ιK hι hT hT' x₁ hx₁).choose_spec]; rw [hm])

Depends on / 依赖: IsLimit, KernelFork, KernelFork.IsLimit.of, cancel_mono, choose_spec
-/
noncomputable def isLimitKernelFork : IsLimit (KernelFork.ofι _ (ιK_mor₁ hT α)) :=
  KernelFork.IsLimit.ofι _ _ _
    (fun x₁ hx₁ => (exists_lift_ιK hι hT hT' x₁ hx₁).choose_spec)
    (fun x₁ hx₁ m hm => by
      have := mono_ιK hι hT hT'
      rw [← cancel_mono (ιK f₃ α)]; rw [(exists_lift_ιK hι hT hT' x₁ hx₁).choose_spec]; rw [hm])

set_option backward.isDefEq.respectTransparency false in
/--
lemma `exists_desc_πQ` / 引理 `exists_desc_πQ`

English:
lemma exists_desc_πQ
  given: {B : A} (x₂ : X₂ ⟶ B) (hx₂ : f₁ ≫ x₂ = 0)
  proof: by
  obtain ⟨x₁, hx₁⟩ := Triangle.yoneda_exact₂ _ hT (ι.map x₂) (by simp [← ι.map_comp, hx₂])
  obtain ⟨k, hk⟩ := Triangle.yoneda_exact₂ _ hT' x₁
    (eq_zero_of_hom_shift_pos hι _ (by lia))
  exact ⟨ι.preimage k, ι.map_injective (by cat_disch)⟩

中文:
引理 exists_desc_πQ
  条件: {B : A} (x₂ : X₂ ⟶ B) (hx₂ : f₁ ≫ x₂ = 0)
  证明: by
  obtain ⟨x₁, hx₁⟩ := Triangle.yoneda_exact₂ _ hT (ι.map x₂) (by simp [← ι.map_comp, hx₂])
  obtain ⟨k, hk⟩ := Triangle.yoneda_exact₂ _ hT' x₁
    (eq_zero_of_hom_shift_pos hι _ (by lia))
  exact ⟨ι.preimage k, ι.map_injective (by cat_disch)⟩

Depends on / 依赖: Triangle, Triangle.yoneda_exact, cat_disch, eq_zero_of_hom_shift_pos, map_comp, map_injective, preimage
-/
lemma exists_desc_πQ {B : A} (x₂ : X₂ ⟶ B) (hx₂ : f₁ ≫ x₂ = 0) :
    exists (k : Q ⟶ B), πQ f₂ β ≫ k = x₂ := by
  obtain ⟨x₁, hx₁⟩ := Triangle.yoneda_exact₂ _ hT (ι.map x₂) (by simp [← ι.map_comp, hx₂])
  obtain ⟨k, hk⟩ := Triangle.yoneda_exact₂ _ hT' x₁
    (eq_zero_of_hom_shift_pos hι _ (by lia))
  exact ⟨ι.preimage k, ι.map_injective (by cat_disch)⟩

/--
Definition of `isColimitCokernelCofork` / `isColimitCokernelCofork` 的定义

English:
definition isColimitCokernelCofork
  signature: : IsColimit (CokernelCofork.ofπ _ (mor₁_πQ hT β))
  body: CokernelCofork.IsColimit.ofπ _ _ _
    (fun x₂ hx₂ => (exists_desc_πQ hι hT hT' x₂ hx₂).choose_spec)
    (fun x₂ hx₂ m hm => by
      have := epi_πQ hι hT hT'
      rw [← cancel_epi (πQ f₂ β)]; rw [(exists_desc_πQ hι hT hT' x₂ hx₂).choose_spec]; rw [hm])

中文:
定义 isColimitCokernelCofork
  签名: : IsColimit (CokernelCofork.ofπ _ (mor₁_πQ hT β))
  定义体: CokernelCofork.IsColimit.ofπ _ _ _
    (fun x₂ hx₂ => (exists_desc_πQ hι hT hT' x₂ hx₂).choose_spec)
    (fun x₂ hx₂ m hm => by
      have := epi_πQ hι hT hT'
      rw [← cancel_epi (πQ f₂ β)]; rw [(exists_desc_πQ hι hT hT' x₂ hx₂).choose_spec]; rw [hm])

Depends on / 依赖: CokernelCofork, CokernelCofork.IsColimit.of, IsColimit, cancel_epi, choose_spec
-/
noncomputable def isColimitCokernelCofork : IsColimit (CokernelCofork.ofπ _ (mor₁_πQ hT β)) :=
  CokernelCofork.IsColimit.ofπ _ _ _
    (fun x₂ hx₂ => (exists_desc_πQ hι hT hT' x₂ hx₂).choose_spec)
    (fun x₂ hx₂ m hm => by
      have := epi_πQ hι hT hT'
      rw [← cancel_epi (πQ f₂ β)]; rw [(exists_desc_πQ hι hT hT' x₂ hx₂).choose_spec]; rw [hm])

/--
lemma `hasKernel` / 引理 `hasKernel`

English:
lemma hasKernel
  statement: HasKernel f₁
  proof: ⟨_, isLimitKernelFork hι hT hT'⟩

中文:
引理 hasKernel
  结论: HasKernel f₁
  证明: ⟨_, isLimitKernelFork hι hT hT'⟩

Depends on / 依赖: isLimitKernelFork
-/
lemma hasKernel : HasKernel f₁ := ⟨_, isLimitKernelFork hι hT hT'⟩

/--
lemma `hasCokernel` / 引理 `hasCokernel`

English:
lemma hasCokernel
  statement: HasCokernel f₁
  proof: ⟨_, isColimitCokernelCofork hι hT hT'⟩

中文:
引理 hasCokernel
  结论: HasCokernel f₁
  证明: ⟨_, isColimitCokernelCofork hι hT hT'⟩

Depends on / 依赖: isColimitCokernelCofork
-/
lemma hasCokernel : HasCokernel f₁ := ⟨_, isColimitCokernelCofork hι hT hT'⟩

end

variable (ι) in
/--
Definition of `admissibleMorphism` / `admissibleMorphism` 的定义

English:
definition admissibleMorphism
  signature: : MorphismProperty A
  body: fun X₁ X₂ f₁ =>
    forall ⦃X₃ : C⦄ (f₂ : ι.obj X₂ ⟶ X₃) (f₃ : X₃ ⟶ (ι.obj X₁)⟦(1 : Int)⟧)
      (_ : Triangle.mk (ι.map f₁) f₂ f₃ in distTriang C),
    exists (K Q : A) (α : (ι.obj K)⟦(1 : Int)⟧ ⟶ X₃) (β : X₃ ⟶ ι.obj Q)
      (γ : ι.obj Q ⟶ (ι.obj K)⟦(1 : Int)⟧⟦(1 : Int)⟧), Triangle.mk α β γ in dis

中文:
定义 admissibleMorphism
  签名: : Morphism命题erty A
  定义体: fun X₁ X₂ f₁ =>
    forall ⦃X₃ : C⦄ (f₂ : ι.obj X₂ ⟶ X₃) (f₃ : X₃ ⟶ (ι.obj X₁)⟦(1 : Int)⟧)
      (_ : Triangle.mk (ι.map f₁) f₂ f₃ in distTriang C),
    exists (K Q : A) (α : (ι.obj K)⟦(1 : Int)⟧ ⟶ X₃) (β : X₃ ⟶ ι.obj Q)
      (γ : ι.obj Q ⟶ (ι.obj K)⟦(1 : Int)⟧⟦(1 : Int)⟧), Triangle.mk α β γ in dis

Depends on / 依赖: Triangle, Triangle.mk, distTriang
-/
def admissibleMorphism : MorphismProperty A :=
  fun X₁ X₂ f₁ =>
    forall ⦃X₃ : C⦄ (f₂ : ι.obj X₂ ⟶ X₃) (f₃ : X₃ ⟶ (ι.obj X₁)⟦(1 : Int)⟧)
      (_ : Triangle.mk (ι.map f₁) f₂ f₃ in distTriang C),
    exists (K Q : A) (α : (ι.obj K)⟦(1 : Int)⟧ ⟶ X₃) (β : X₃ ⟶ ι.obj Q)
      (γ : ι.obj Q ⟶ (ι.obj K)⟦(1 : Int)⟧⟦(1 : Int)⟧), Triangle.mk α β γ in distTriang C

variable [Preadditive A] [ι.Full] [ι.Faithful]

include hι in
/--
lemma `hasKernel_of_admissibleMorphism` / 引理 `hasKernel_of_admissibleMorphism`

English:
lemma hasKernel_of_admissibleMorphism
  statement: {X₁ X₂ : A} (f₁ : X₁ ⟶ X₂)
  proof: by
  obtain ⟨X₃, f₂, f₃, hT⟩ := distinguished_cocone_triangle (ι.map f₁)
  obtain ⟨K, Q, α, β, γ, hT'⟩ := hf₁ f₂ f₃ hT
  exact hasKernel hι hT hT'

include hι in

中文:
引理 hasKernel_of_admissibleMorphism
  结论: {X₁ X₂ : A} (f₁ : X₁ ⟶ X₂)
  证明: by
  obtain ⟨X₃, f₂, f₃, hT⟩ := distinguished_cocone_triangle (ι.map f₁)
  obtain ⟨K, Q, α, β, γ, hT'⟩ := hf₁ f₂ f₃ hT
  exact hasKernel hι hT hT'

include hι in

Depends on / 依赖: distinguished_cocone_triangle, hasKernel
-/
lemma hasKernel_of_admissibleMorphism {X₁ X₂ : A} (f₁ : X₁ ⟶ X₂)
    (hf₁ : admissibleMorphism ι f₁) :
    HasKernel f₁ := by
  obtain ⟨X₃, f₂, f₃, hT⟩ := distinguished_cocone_triangle (ι.map f₁)
  obtain ⟨K, Q, α, β, γ, hT'⟩ := hf₁ f₂ f₃ hT
  exact hasKernel hι hT hT'

include hι in
/--
lemma `hasCokernel_of_admissibleMorphism` / 引理 `hasCokernel_of_admissibleMorphism`

English:
lemma hasCokernel_of_admissibleMorphism
  statement: {X₁ X₂ : A} (f₁ : X₁ ⟶ X₂)
  proof: by
  obtain ⟨X₃, f₂, f₃, hT⟩ := distinguished_cocone_triangle (ι.map f₁)
  obtain ⟨K, Q, α, β, γ, hT'⟩ := hf₁ f₂ f₃ hT
  exact hasCokernel hι hT hT'

中文:
引理 hasCokernel_of_admissibleMorphism
  结论: {X₁ X₂ : A} (f₁ : X₁ ⟶ X₂)
  证明: by
  obtain ⟨X₃, f₂, f₃, hT⟩ := distinguished_cocone_triangle (ι.map f₁)
  obtain ⟨K, Q, α, β, γ, hT'⟩ := hf₁ f₂ f₃ hT
  exact hasCokernel hι hT hT'

Depends on / 依赖: distinguished_cocone_triangle, hasCokernel
-/
lemma hasCokernel_of_admissibleMorphism {X₁ X₂ : A} (f₁ : X₁ ⟶ X₂)
    (hf₁ : admissibleMorphism ι f₁) :
    HasCokernel f₁ := by
  obtain ⟨X₃, f₂, f₃, hT⟩ := distinguished_cocone_triangle (ι.map f₁)
  obtain ⟨K, Q, α, β, γ, hT'⟩ := hf₁ f₂ f₃ hT
  exact hasCokernel hι hT hT'

section

attribute [local instance] hasZeroObject_of_hasTerminal_object

variable [HasFiniteProducts A] [ι.Additive]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isLimitKernelForkOfDistTriang` / `isLimitKernelForkOfDistTriang` 的定义

English:
definition isLimitKernelForkOfDistTriang
  signature: {X₁ X₂ X₃ : A}
  body: by
  have hT' : Triangle.mk (𝟙 ((ι.obj X₁)⟦(1 : Int)⟧)) (0 : _ ⟶ ι.obj 0) 0 in distTriang C := by
    refine isomorphic_distinguished _ (contractible_distinguished
      (((ι ⋙ shiftFunctor C (1 : Int)).obj X₁))) _ ?_
    exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (IsZero.iso (by
      dsimp

中文:
定义 isLimitKernelForkOfDistTriang
  签名: {X₁ X₂ X₃ : A}
  定义体: by
  have hT' : Triangle.mk (𝟙 ((ι.obj X₁)⟦(1 : Int)⟧)) (0 : _ ⟶ ι.obj 0) 0 in distTriang C := by
    refine isomorphic_distinguished _ (contractible_distinguished
      (((ι ⋙ shiftFunctor C (1 : Int)).obj X₁))) _ ?_
    exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (IsZero.iso (by
      dsimp
-/
noncomputable def isLimitKernelForkOfDistTriang {X₁ X₂ X₃ : A}
    (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) (f₃ : ι.obj X₃ ⟶ (ι.obj X₁)⟦(1 : Int)⟧)
    (hT : Triangle.mk (ι.map f₁) (ι.map f₂) f₃ in distTriang C) :
    IsLimit (KernelFork.ofι f₁ (show f₁ ≫ f₂ = 0 from ι.map_injective (by
      have := comp_distTriang_mor_zero₁₂ _ hT
      dsimp at this
      cat_disch))) := by
  have hT' : Triangle.mk (𝟙 ((ι.obj X₁)⟦(1 : Int)⟧)) (0 : _ ⟶ ι.obj 0) 0 in distTriang C := by
    refine isomorphic_distinguished _ (contractible_distinguished
      (((ι ⋙ shiftFunctor C (1 : Int)).obj X₁))) _ ?_
    exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (IsZero.iso (by
      dsimp
      rw [IsZero.iff_id_eq_zero]; rw [← ι.map_id]; rw [id_zero]; rw [ι.map_zero]) (isZero_zero C))
  refine IsLimit.ofIsoLimit (AbelianSubcategory.isLimitKernelFork hι
    (rot_of_distTriang _ hT) hT') ?_
  exact Fork.ext (-(Iso.refl _)) ((ι ⋙ shiftFunctor C (1 : Int)).map_injective
    (by simp))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimitCokernelCoforkOfDistTriang` / `isColimitCokernelCoforkOfDistTriang` 的定义

English:
definition isColimitCokernelCoforkOfDistTriang
  signature: {X₁ X₂ X₃ : A}
  body: by
  have hT' : Triangle.mk (0 : ((ι ⋙ shiftFunctor C (1 : Int)).obj 0) ⟶ _) (𝟙 (ι.obj X₃)) 0 in
      distTriang C := by
    refine isomorphic_distinguished _ (inv_rot_of_distTriang _
      (contractible_distinguished (ι.obj X₃))) _ ?_
    refine Triangle.isoMk _ _ (IsZero.iso ?_ ?_) (Iso.refl _) (

中文:
定义 isColimitCokernelCoforkOfDistTriang
  签名: {X₁ X₂ X₃ : A}
  定义体: by
  have hT' : Triangle.mk (0 : ((ι ⋙ shiftFunctor C (1 : Int)).obj 0) ⟶ _) (𝟙 (ι.obj X₃)) 0 in
      distTriang C := by
    refine isomorphic_distinguished _ (inv_rot_of_distTriang _
      (contractible_distinguished (ι.obj X₃))) _ ?_
    refine Triangle.isoMk _ _ (IsZero.iso ?_ ?_) (Iso.refl _) (
-/
noncomputable def isColimitCokernelCoforkOfDistTriang {X₁ X₂ X₃ : A}
    (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) (f₃ : ι.obj X₃ ⟶ (ι.obj X₁)⟦(1 : Int)⟧)
    (hT : Triangle.mk (ι.map f₁) (ι.map f₂) f₃ in distTriang C) :
    IsColimit (CokernelCofork.ofπ f₂ (show f₁ ≫ f₂ = 0 from ι.map_injective (by
      have := comp_distTriang_mor_zero₁₂ _ hT
      dsimp at this
      cat_disch))) := by
  have hT' : Triangle.mk (0 : ((ι ⋙ shiftFunctor C (1 : Int)).obj 0) ⟶ _) (𝟙 (ι.obj X₃)) 0 in
      distTriang C := by
    refine isomorphic_distinguished _ (inv_rot_of_distTriang _
      (contractible_distinguished (ι.obj X₃))) _ ?_
    refine Triangle.isoMk _ _ (IsZero.iso ?_ ?_) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
    · dsimp
      rw [IsZero.iff_id_eq_zero]; rw [← Functor.map_id]; rw [← Functor.map_id]; rw [id_zero]; rw [Functor.map_zero]; rw [Functor.map_zero]
    · dsimp
      rw [IsZero.iff_id_eq_zero]; rw [← Functor.map_id]; rw [id_zero]; rw [Functor.map_zero]
    all_goals simp
  refine IsColimit.ofIsoColimit (AbelianSubcategory.isColimitCokernelCofork hι hT hT') ?_
  exact Cofork.ext (Iso.refl _) (ι.map_injective (by simp))

variable (hA : admissibleMorphism ι = ⊤)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hι hA in
omit [HasFiniteProducts A] in
/--
lemma `exists_distinguished_triangle_of_epi` / 引理 `exists_distinguished_triangle_of_epi`

English:
lemma exists_distinguished_triangle_of_epi
  given: {X₂ X₃ : A} (π : X₂ ⟶ X₃) [Epi π]
  proof: by
  obtain ⟨X₁, f₂, f₃, hT⟩ := distinguished_cocone_triangle (ι.map π)
  have : admissibleMorphism ι π := by simp [hA]
  obtain ⟨K, Q, α, β, γ, hT'⟩ := this f₂ f₃ hT
  have hQ : 𝟙 Q = 0 :=
    Cofork.IsColimit.hom_ext (isColimitCokernelCofork hι hT hT') (by
      dsimp
      rw [comp_id]; rw [comp_

中文:
引理 exists_distinguished_triangle_of_epi
  条件: {X₂ X₃ : A} (π : X₂ ⟶ X₃) [Epi π]
  证明: by
  obtain ⟨X₁, f₂, f₃, hT⟩ := distinguished_cocone_triangle (ι.map π)
  have : admissibleMorphism ι π := by simp [hA]
  obtain ⟨K, Q, α, β, γ, hT'⟩ := this f₂ f₃ hT
  have hQ : 𝟙 Q = 0 :=
    Cofork.IsColimit.hom_ext (isColimitCokernelCofork hι hT hT') (by
      dsimp
      rw [comp_id]; rw [comp_

Depends on / 依赖: Cofork, Cofork.IsColimit.hom_ext, IsColimit, IsZero, IsZero.iff_id_eq_zero, Triangle, Triangle.isZero, admissibleMorphism, cancel_epi, comp_id, comp_zero, distinguished_cocone_triangle, hom_ext, iff_id_eq_zero, isColimitCokernelCofork, map_id, map_zero
-/
lemma exists_distinguished_triangle_of_epi {X₂ X₃ : A} (π : X₂ ⟶ X₃) [Epi π] :
    exists (X₁ : A) (i : X₁ ⟶ X₂) (δ : ι.obj X₃ ⟶ (ι.obj X₁)⟦(1 : Int)⟧),
      Triangle.mk (ι.map i) (ι.map π) δ in distTriang C := by
  obtain ⟨X₁, f₂, f₃, hT⟩ := distinguished_cocone_triangle (ι.map π)
  have : admissibleMorphism ι π := by simp [hA]
  obtain ⟨K, Q, α, β, γ, hT'⟩ := this f₂ f₃ hT
  have hQ : 𝟙 Q = 0 :=
    Cofork.IsColimit.hom_ext (isColimitCokernelCofork hι hT hT') (by
      dsimp
      rw [comp_id]; rw [comp_zero]; rw [← cancel_epi π]; rw [comp_zero]; rw [mor₁_πQ hT β])
  have : IsIso α := (Triangle.isZero₃_iff_isIso₁ _ hT').1 (by
    dsimp
    rw [IsZero.iff_id_eq_zero]; rw [← ι.map_id]; rw [hQ]; rw [ι.map_zero])
  refine ⟨K, -ιK f₃ α, f₂ ≫ inv α, ?_⟩
  rw [rotate_distinguished_triangle]
  refine isomorphic_distinguished _ hT _ ?_
  exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (asIso α)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (ι) in
/-- Let `ι : A ⥤ C` be a fully faithful additive functor where `A` is
an additive category and `C` is a triangulated category. The category `A`
is abelian if the following conditions are satisfied:
* For any object `X` and `Y` in `A`, there is no nonzero morphism
  `ι.obj X ⟶ (ι.obj Y)⟦n⟧` when `n < 0`.
* Any morphism `f₁ : X₁ ⟶ X₂` in `A` is admissible, i.e. when
  we complete `ι.obj f₁` in a distinguished triangle
  `ι.obj X₁ ⟶ ι.obj X₂ ⟶ X₃ ⟶ (ι.obj X₁)⟦1⟧`, there exists objects `K`
  and `Q`, and a distinguished triangle `(ι.obj K)⟦1⟧ ⟶ X₃ ⟶ (ι.obj Q) ⟶ ...`. -/
@[instance_reducible]
/--
Definition of `abelian` / `abelian` 的定义

English:
definition abelian
  signature: [IsTriangulated C]
  body: Abelian.mk' (fun X₁ X₂ f₁ => by
    obtain ⟨X₃, f₂, f₃, hT⟩ := distinguished_cocone_triangle (ι.map f₁)
    have : admissibleMorphism ι f₁ := by simp [hA]
    obtain ⟨K, Q, α, β, γ, hT'⟩ := this f₂ f₃ hT
    have := epi_πQ hι hT hT'
    obtain ⟨I, i, δ, hI⟩ := exists_distinguished_triangle_of_epi hι

中文:
定义 abelian
  签名: [IsTriangulated C]
  定义体: Abelian.mk' (fun X₁ X₂ f₁ => by
    obtain ⟨X₃, f₂, f₃, hT⟩ := distinguished_cocone_triangle (ι.map f₁)
    have : admissibleMorphism ι f₁ := by simp [hA]
    obtain ⟨K, Q, α, β, γ, hT'⟩ := this f₂ f₃ hT
    have := epi_πQ hι hT hT'
    obtain ⟨I, i, δ, hI⟩ := exists_distinguished_triangle_of_epi hι

Depends on / 依赖: Abelian, Abelian.mk, admissibleMorphism, distinguished_cocone_triangle, exists_distinguished_triangle_of_epi, rot_of_distTriang, shiftFunctor, someOctahedron
-/
noncomputable def abelian [IsTriangulated C] : Abelian A :=
  Abelian.mk' (fun X₁ X₂ f₁ => by
    obtain ⟨X₃, f₂, f₃, hT⟩ := distinguished_cocone_triangle (ι.map f₁)
    have : admissibleMorphism ι f₁ := by simp [hA]
    obtain ⟨K, Q, α, β, γ, hT'⟩ := this f₂ f₃ hT
    have := epi_πQ hι hT hT'
    obtain ⟨I, i, δ, hI⟩ := exists_distinguished_triangle_of_epi hι hA (πQ f₂ β)
    have H := someOctahedron (show f₂ ≫ β = ι.map (πQ f₂ β) by simp)
      (rot_of_distTriang _ hT) (rot_of_distTriang _ hT')
      (rot_of_distTriang _ hI)
    obtain ⟨m₁, hm₁⟩ : exists (m₁ : X₁ ⟶ I), (shiftFunctor C (1 : Int)).map (ι.map m₁) = H.m₁ :=
      ⟨(ι ⋙ shiftFunctor C (1 : Int)).preimage H.m₁, Functor.map_preimage (ι ⋙ _) _⟩
    obtain ⟨m₃ : ι.obj I ⟶ (ι.obj K)⟦(1 : Int)⟧, hm₃⟩ :
        exists m₃, (shiftFunctor C (1 : Int)).map m₃ = H.m₃ :=
      ⟨(shiftFunctor C (1 : Int)).preimage H.m₃, Functor.map_preimage _ _⟩
    have Hmem : Triangle.mk (ι.map (ιK f₃ α)) (ι.map m₁) (-m₃) in distTriang C := by
      rw [rotate_distinguished_triangle]; rw [← Triangle.shift_distinguished_iff _ 1]
      refine isomorphic_distinguished _ H.mem _ ?_
      exact Triangle.isoMk _ _ (-(Iso.refl _)) (Iso.refl _) (Iso.refl _)
    exact ⟨{
      kernelFork := _
      isLimitKernelFork := isLimitKernelFork hι hT hT'
      cokernelCofork := _
      isColimitCokernelCofork := isColimitCokernelCofork hι hT hT'
      image := _
      imageι := _
      imageπ := _
      ι_imageπ := _
      imageι_π := _
      imageIsCokernel := isColimitCokernelCoforkOfDistTriang hι _ _ _ Hmem
      imageIsKernel := isLimitKernelForkOfDistTriang hι _ _ _ hI
      fac := (ι ⋙ shiftFunctor C (1 : Int)).map_injective (by simpa [hm₁] using H.comm₂) }⟩)

end

end AbelianSubcategory

end Triangulated

end CategoryTheory
