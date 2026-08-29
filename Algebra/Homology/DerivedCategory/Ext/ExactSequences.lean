/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.CategoryTheory.Triangulated.Yoneda

/-!
# Long exact sequences of `Ext`-groups

In this file, we obtain the covariant long exact sequence of `Ext` when `n₀ + 1 = n₁`:
`Ext X S.X₁ n₀ → Ext X S.X₂ n₀ → Ext X S.X₃ n₀ → Ext X S.X₁ n₁ → Ext X S.X₂ n₁ → Ext X S.X₃ n₁`
when `S` is a short exact short complex in an abelian category `C`, `n₀ + 1 = n₁` and `X : C`.
Similarly, if `Y : C`, there is a contravariant long exact sequence :
`Ext S.X₃ Y n₀ → Ext S.X₂ Y n₀ → Ext S.X₁ Y n₀ → Ext S.X₃ Y n₁ → Ext S.X₂ Y n₁ → Ext S.X₁ Y n₁`.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

universe w' w v u

namespace CategoryTheory

open Opposite DerivedCategory Pretriangulated Pretriangulated.Opposite

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

namespace Abelian

namespace Ext

section CovariantSequence

/--
lemma `hom_comp_singleFunctor_map_shift` / 引理 `hom_comp_singleFunctor_map_shift`

English:
lemma hom_comp_singleFunctor_map_shift
  statement: [HasDerivedCategory.{w'} C]
  proof: by
  simp only [comp_hom, mk₀_hom, ShiftedHom.comp_mk₀]

中文:
引理 hom_comp_singleFunctor_map_shift
  结论: [HasDerivedCategory.{w'} C]
  证明: by
  simp only [comp_hom, mk₀_hom, ShiftedHom.comp_mk₀]

Depends on / 依赖: ShiftedHom, ShiftedHom.comp_mk, comp_hom
-/
lemma hom_comp_singleFunctor_map_shift [HasDerivedCategory.{w'} C]
    {X Y Z : C} {n : Nat} (x : Ext X Y n) (f : Y ⟶ Z) :
    x.hom ≫ ((DerivedCategory.singleFunctor C 0).map f)⟦(n : Int)⟧' =
      (x.comp (mk₀ f) (add_zero n)).hom := by
  simp only [comp_hom, mk₀_hom, ShiftedHom.comp_mk₀]

variable {X : C} {S : ShortComplex C} (hS : S.ShortExact)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply` / 引理 `preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply`

English:
lemma preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply
  proof: by
  rw [Pretriangulated.preadditiveCoyoneda_homologySequenceδ_apply]; rw [comp_hom]; rw [hS.extClass_hom]; rw [ShiftedHom.comp]
  rfl

中文:
引理 preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply
  证明: by
  rw [Pretriangulated.preadditiveCoyoneda_homologySequenceδ_apply]; rw [comp_hom]; rw [hS.extClass_hom]; rw [ShiftedHom.comp]
  rfl

Depends on / 依赖: Pretriangulated, Pretriangulated.preadditiveCoyoneda_homologySequence, ShiftedHom, ShiftedHom.comp, comp_hom, extClass_hom, hS.extClass_hom
-/
lemma preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply
    [HasDerivedCategory.{w'} C] {X : C} {n₀ : Nat} (x : Ext X S.X₃ n₀)
    {n₁ : Nat} (h : n₀ + 1 = n₁) :
    (preadditiveCoyoneda.obj (op ((singleFunctor C 0).obj X))).homologySequenceδ
      hS.singleTriangle n₀ n₁ (by lia) x.hom =
        (x.comp hS.extClass h).hom := by
  rw [Pretriangulated.preadditiveCoyoneda_homologySequenceδ_apply]; rw [comp_hom]; rw [hS.extClass_hom]; rw [ShiftedHom.comp]
  rfl

variable (X)

set_option backward.defeqAttrib.useBackward true in
include hS in
/--
lemma `covariant_sequence_exact₂'` / 引理 `covariant_sequence_exact₂'`

English:
lemma covariant_sequence_exact₂'
  given: (n : Nat)
  proof: by
  let := HasDerivedCategory.standard C
  have := (preadditiveCoyoneda.obj (op ((singleFunctor C 0).obj X))).homologySequence_exact₂ _
    (hS.singleTriangle_distinguished) n
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (H := this)
  all_goals ext x; apply hom_comp_singleFunctor_map_shift (C := C)

中文:
引理 covariant_sequence_exact₂'
  条件: (n : 自然数)
  证明: by
  let := HasDerivedCategory.standard C
  have := (preadditiveCoyoneda.obj (op ((singleFunctor C 0).obj X))).homologySequence_exact₂ _
    (hS.singleTriangle_distinguished) n
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (H := this)
  all_goals ext x; apply hom_comp_singleFunctor_map_shift (C := C)

Depends on / 依赖: Ext.homAddEquiv, Function, Function.Exact.of_ladder_addEquiv_of_exact, HasDerivedCategory, HasDerivedCategory.standard, ShortComplex, ShortComplex.ab_exact_iff_function_exact, ab_exact_iff_function_exact, all_goals, hS.singleTriangle_distinguished, homAddEquiv, hom_comp_singleFunctor_map_shift, of_ladder_addEquiv_of_exact, preadditiveCoyoneda, preadditiveCoyoneda.obj, singleFunctor, singleTriangle_distinguished, standard
-/
lemma covariant_sequence_exact₂' (n : Nat) :
    (ShortComplex.mk (AddCommGrpCat.ofHom ((mk₀ S.f).postcomp X (add_zero n)))
      (AddCommGrpCat.ofHom ((mk₀ S.g).postcomp X (add_zero n))) (by
        ext x
        dsimp
        simp only [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, ShortComplex.zero, mk₀_zero,
          comp_zero])).Exact := by
  let := HasDerivedCategory.standard C
  have := (preadditiveCoyoneda.obj (op ((singleFunctor C 0).obj X))).homologySequence_exact₂ _
    (hS.singleTriangle_distinguished) n
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (H := this)
  all_goals ext x; apply hom_comp_singleFunctor_map_shift (C := C)

section

variable (n₀ n₁ : Nat) (h : n₀ + 1 = n₁)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `covariant_sequence_exact₃'` / 引理 `covariant_sequence_exact₃'`

English:
lemma covariant_sequence_exact₃'
  proof: by
  let := HasDerivedCategory.standard C
  have := (preadditiveCoyoneda.obj (op ((singleFunctor C 0).obj X))).homologySequence_exact₃ _
    (hS.singleTriangle_distinguished) n₀ n₁ (by lia)
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (H := this)
  · ext x; apply hom_comp_singleFunctor_map_shift (C := C)
  · ext x
    exact preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply hS x h

中文:
引理 covariant_sequence_exact₃'
  证明: by
  let := HasDerivedCategory.standard C
  have := (preadditiveCoyoneda.obj (op ((singleFunctor C 0).obj X))).homologySequence_exact₃ _
    (hS.singleTriangle_distinguished) n₀ n₁ (by lia)
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (H := this)
  · ext x; apply hom_comp_singleFunctor_map_shift (C := C)
  · ext x
    exact preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply hS x h

Depends on / 依赖: Ext.homAddEquiv, Function, Function.Exact.of_ladder_addEquiv_of_exact, HasDerivedCategory, HasDerivedCategory.standard, ShortComplex, ShortComplex.ab_exact_iff_function_exact, ab_exact_iff_function_exact, hS.singleTriangle_distinguished, homAddEquiv, hom_comp_singleFunctor_map_shift, of_ladder_addEquiv_of_exact, preadditiveCoyoneda, preadditiveCoyoneda.obj, singleFunctor, singleTriangle_distinguished, standard
-/
lemma covariant_sequence_exact₃' :
    (ShortComplex.mk (AddCommGrpCat.ofHom ((mk₀ S.g).postcomp X (add_zero n₀)))
      (AddCommGrpCat.ofHom (hS.extClass.postcomp X h)) (by
        ext x
        dsimp
        simp only [comp_assoc_of_second_deg_zero, ShortComplex.ShortExact.comp_extClass,
          comp_zero])).Exact := by
  let := HasDerivedCategory.standard C
  have := (preadditiveCoyoneda.obj (op ((singleFunctor C 0).obj X))).homologySequence_exact₃ _
    (hS.singleTriangle_distinguished) n₀ n₁ (by lia)
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (H := this)
  · ext x; apply hom_comp_singleFunctor_map_shift (C := C)
  · ext x
    exact preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply hS x h

set_option backward.defeqAttrib.useBackward true in
/--
lemma `covariant_sequence_exact₁'` / 引理 `covariant_sequence_exact₁'`

English:
lemma covariant_sequence_exact₁'
  proof: by
  let := HasDerivedCategory.standard C
  have := (preadditiveCoyoneda.obj (op ((singleFunctor C 0).obj X))).homologySequence_exact₁ _
    (hS.singleTriangle_distinguished) n₀ n₁ (by lia)
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (H := this)
  · ext x
    exact preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply hS x h
  · ext x; apply hom_comp_singleFunctor_map_shift (C := C)

中文:
引理 covariant_sequence_exact₁'
  证明: by
  let := HasDerivedCategory.standard C
  have := (preadditiveCoyoneda.obj (op ((singleFunctor C 0).obj X))).homologySequence_exact₁ _
    (hS.singleTriangle_distinguished) n₀ n₁ (by lia)
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (H := this)
  · ext x
    exact preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply hS x h
  · ext x; apply hom_comp_singleFunctor_map_shift (C := C)

Depends on / 依赖: Ext.homAddEquiv, Function, Function.Exact.of_ladder_addEquiv_of_exact, HasDerivedCategory, HasDerivedCategory.standard, ShortComplex, ShortComplex.ab_exact_iff_function_exact, ab_exact_iff_function_exact, hS.singleTriangle_distinguished, homAddEquiv, hom_comp_singleFunctor_map_shift, of_ladder_addEquiv_of_exact, preadditiveCoyoneda, preadditiveCoyoneda.obj, singleFunctor, singleTriangle_distinguished, standard
-/
lemma covariant_sequence_exact₁' :
    (ShortComplex.mk
      (AddCommGrpCat.ofHom (hS.extClass.postcomp X h))
      (AddCommGrpCat.ofHom ((mk₀ S.f).postcomp X (add_zero n₁))) (by
        ext x
        dsimp
        simp only [comp_assoc_of_third_deg_zero, ShortComplex.ShortExact.extClass_comp,
          comp_zero])).Exact := by
  let := HasDerivedCategory.standard C
  have := (preadditiveCoyoneda.obj (op ((singleFunctor C 0).obj X))).homologySequence_exact₁ _
    (hS.singleTriangle_distinguished) n₀ n₁ (by lia)
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (H := this)
  · ext x
    exact preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply hS x h
  · ext x; apply hom_comp_singleFunctor_map_shift (C := C)

open ComposableArrows

/--
Definition of `covariantSequence` / `covariantSequence` 的定义

English:
definition covariantSequence
  signature: : ComposableArrows AddCommGrpCat.{w} 5
  body: mk₅ (AddCommGrpCat.ofHom ((mk₀ S.f).postcomp X (add_zero n₀)))
    (AddCommGrpCat.ofHom ((mk₀ S.g).postcomp X (add_zero n₀)))
    (AddCommGrpCat.ofHom (hS.extClass.postcomp X h))
    (AddCommGrpCat.ofHom ((mk₀ S.f).postcomp X (add_zero n₁)))
    (AddCommGrpCat.ofHom ((mk₀ S.g).postcomp X (add_zero n₁)))

中文:
定义 covariantSequence
  签名: : ComposableArrows 加法交换群范畴.{w} 5
  定义体: mk₅ (AddCommGrpCat.ofHom ((mk₀ S.f).postcomp X (add_zero n₀)))
    (AddCommGrpCat.ofHom ((mk₀ S.g).postcomp X (add_zero n₀)))
    (AddCommGrpCat.ofHom (hS.extClass.postcomp X h))
    (AddCommGrpCat.ofHom ((mk₀ S.f).postcomp X (add_zero n₁)))
    (AddCommGrpCat.ofHom ((mk₀ S.g).postcomp X (add_zero n₁)))

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.ofHom, add_zero, extClass, hS.extClass.postcomp, postcomp
-/
noncomputable def covariantSequence : ComposableArrows AddCommGrpCat.{w} 5 :=
  mk₅ (AddCommGrpCat.ofHom ((mk₀ S.f).postcomp X (add_zero n₀)))
    (AddCommGrpCat.ofHom ((mk₀ S.g).postcomp X (add_zero n₀)))
    (AddCommGrpCat.ofHom (hS.extClass.postcomp X h))
    (AddCommGrpCat.ofHom ((mk₀ S.f).postcomp X (add_zero n₁)))
    (AddCommGrpCat.ofHom ((mk₀ S.g).postcomp X (add_zero n₁)))

/--
lemma `covariantSequence_exact` / 引理 `covariantSequence_exact`

English:
lemma covariantSequence_exact
  proof: exact_of_δ₀ (covariant_sequence_exact₂' X hS n₀).exact_toComposableArrows
    (exact_of_δ₀ (covariant_sequence_exact₃' X hS n₀ n₁ h).exact_toComposableArrows
      (exact_of_δ₀ (covariant_sequence_exact₁' X hS n₀ n₁ h).exact_toComposableArrows
        (covariant_sequence_exact₂' X hS n₁).exact_toComposableArrows))

中文:
引理 covariantSequence_exact
  证明: exact_of_δ₀ (covariant_sequence_exact₂' X hS n₀).exact_toComposableArrows
    (exact_of_δ₀ (covariant_sequence_exact₃' X hS n₀ n₁ h).exact_toComposableArrows
      (exact_of_δ₀ (covariant_sequence_exact₁' X hS n₀ n₁ h).exact_toComposableArrows
        (covariant_sequence_exact₂' X hS n₁).exact_toComposableArrows))

Depends on / 依赖: exact_toComposableArrows
-/
lemma covariantSequence_exact :
    (covariantSequence X hS n₀ n₁ h).Exact :=
  exact_of_δ₀ (covariant_sequence_exact₂' X hS n₀).exact_toComposableArrows
    (exact_of_δ₀ (covariant_sequence_exact₃' X hS n₀ n₁ h).exact_toComposableArrows
      (exact_of_δ₀ (covariant_sequence_exact₁' X hS n₀ n₁ h).exact_toComposableArrows
        (covariant_sequence_exact₂' X hS n₁).exact_toComposableArrows))

end

/--
lemma `covariant_sequence_exact₁` / 引理 `covariant_sequence_exact₁`

English:
lemma covariant_sequence_exact₁
  statement: {n₁ : Nat} (x₁ : Ext X S.X₁ n₁)
  proof: by
  have := covariant_sequence_exact₁' X hS n₀ n₁ hn₀
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₁ hx₁

include hS in

中文:
引理 covariant_sequence_exact₁
  结论: {n₁ : 自然数} (x₁ : Ext X S.X₁ n₁)
  证明: by
  have := covariant_sequence_exact₁' X hS n₀ n₁ hn₀
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₁ hx₁

include hS in

Depends on / 依赖: ShortComplex, ShortComplex.ab_exact_iff, ab_exact_iff
-/
lemma covariant_sequence_exact₁ {n₁ : Nat} (x₁ : Ext X S.X₁ n₁)
    (hx₁ : x₁.comp (mk₀ S.f) (add_zero n₁) = 0) {n₀ : Nat} (hn₀ : n₀ + 1 = n₁) :
    exists (x₃ : Ext X S.X₃ n₀), x₃.comp hS.extClass hn₀ = x₁ := by
  have := covariant_sequence_exact₁' X hS n₀ n₁ hn₀
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₁ hx₁

include hS in
/--
lemma `covariant_sequence_exact₂` / 引理 `covariant_sequence_exact₂`

English:
lemma covariant_sequence_exact₂
  statement: {n : Nat} (x₂ : Ext X S.X₂ n)
  proof: by
  have := covariant_sequence_exact₂' X hS n
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₂ hx₂

中文:
引理 covariant_sequence_exact₂
  结论: {n : 自然数} (x₂ : Ext X S.X₂ n)
  证明: by
  have := covariant_sequence_exact₂' X hS n
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₂ hx₂

Depends on / 依赖: ShortComplex, ShortComplex.ab_exact_iff, ab_exact_iff
-/
lemma covariant_sequence_exact₂ {n : Nat} (x₂ : Ext X S.X₂ n)
    (hx₂ : x₂.comp (mk₀ S.g) (add_zero n) = 0) :
    exists (x₁ : Ext X S.X₁ n), x₁.comp (mk₀ S.f) (add_zero n) = x₂ := by
  have := covariant_sequence_exact₂' X hS n
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₂ hx₂

/--
lemma `covariant_sequence_exact₃` / 引理 `covariant_sequence_exact₃`

English:
lemma covariant_sequence_exact₃
  statement: {n₀ : Nat} (x₃ : Ext X S.X₃ n₀) {n₁ : Nat} (hn₁ : n₀ + 1 = n₁)
  proof: by
  have := covariant_sequence_exact₃' X hS n₀ n₁ hn₁
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₃ hx₃

中文:
引理 covariant_sequence_exact₃
  结论: {n₀ : 自然数} (x₃ : Ext X S.X₃ n₀) {n₁ : 自然数} (hn₁ : n₀ + 1 = n₁)
  证明: by
  have := covariant_sequence_exact₃' X hS n₀ n₁ hn₁
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₃ hx₃

Depends on / 依赖: ShortComplex, ShortComplex.ab_exact_iff, ab_exact_iff
-/
lemma covariant_sequence_exact₃ {n₀ : Nat} (x₃ : Ext X S.X₃ n₀) {n₁ : Nat} (hn₁ : n₀ + 1 = n₁)
    (hx₃ : x₃.comp hS.extClass hn₁ = 0) :
    exists (x₂ : Ext X S.X₂ n₀), x₂.comp (mk₀ S.g) (add_zero n₀) = x₃ := by
  have := covariant_sequence_exact₃' X hS n₀ n₁ hn₁
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₃ hx₃

/--
lemma `postcomp_mk₀_injective_of_mono` / 引理 `postcomp_mk₀_injective_of_mono`

English:
lemma postcomp_mk₀_injective_of_mono
  given: (L : C) {M N : C} (f : M ⟶ N) [hf : Mono f]
  proof: by
  rw [← AddMonoidHom.ker_eq_bot_iff]; rw [AddSubgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨g, rfl⟩ := Ext.addEquiv₀.symm.surjective x
  simpa [← cancel_mono f] using hx

中文:
引理 postcomp_mk₀_injective_of_mono
  条件: (L : C) {M N : C} (f : M ⟶ N) [hf : 单态射 f]
  证明: by
  rw [← AddMonoidHom.ker_eq_bot_iff]; rw [AddSubgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨g, rfl⟩ := Ext.addEquiv₀.symm.surjective x
  simpa [← cancel_mono f] using hx

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ker_eq_bot_iff, AddSubgroup, AddSubgroup.eq_bot_iff_forall, Ext.addEquiv, cancel_mono, eq_bot_iff_forall, ker_eq_bot_iff, surjective, symm.surjective
-/
lemma postcomp_mk₀_injective_of_mono (L : C) {M N : C} (f : M ⟶ N) [hf : Mono f] :
    Function.Injective ((Ext.mk₀ f).postcomp L (add_zero 0)) := by
  rw [← AddMonoidHom.ker_eq_bot_iff]; rw [AddSubgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨g, rfl⟩ := Ext.addEquiv₀.symm.surjective x
  simpa [← cancel_mono f] using hx

/--
lemma `mono_postcomp_mk₀_of_mono` / 引理 `mono_postcomp_mk₀_of_mono`

English:
lemma mono_postcomp_mk₀_of_mono
  given: (L : C) {M N : C} (f : M ⟶ N) [hf : Mono f]
  proof: (AddCommGrpCat.mono_iff_injective _).mpr (postcomp_mk₀_injective_of_mono L f)

中文:
引理 mono_postcomp_mk₀_of_mono
  条件: (L : C) {M N : C} (f : M ⟶ N) [hf : 单态射 f]
  证明: (AddCommGrpCat.mono_iff_injective _).mpr (postcomp_mk₀_injective_of_mono L f)

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.mono_iff_injective, mono_iff_injective
-/
lemma mono_postcomp_mk₀_of_mono (L : C) {M N : C} (f : M ⟶ N) [hf : Mono f] :
    Mono (AddCommGrpCat.ofHom <| (Ext.mk₀ f).postcomp L (add_zero 0)) :=
  (AddCommGrpCat.mono_iff_injective _).mpr (postcomp_mk₀_injective_of_mono L f)

end CovariantSequence

section ContravariantSequence

variable {S : ShortComplex C} (hS : S.ShortExact) (Y : C)

/--
lemma `singleFunctor_map_comp_hom` / 引理 `singleFunctor_map_comp_hom`

English:
lemma singleFunctor_map_comp_hom
  statement: [HasDerivedCategory.{w'} C]
  proof: by
  simp only [comp_hom, mk₀_hom, ShiftedHom.mk₀_comp]

中文:
引理 singleFunctor_map_comp_hom
  结论: [HasDerivedCategory.{w'} C]
  证明: by
  simp only [comp_hom, mk₀_hom, ShiftedHom.mk₀_comp]

Depends on / 依赖: ShiftedHom, ShiftedHom.mk, comp_hom
-/
lemma singleFunctor_map_comp_hom [HasDerivedCategory.{w'} C]
    {X Y Z : C} (f : X ⟶ Y) {n : Nat} (x : Ext Y Z n) :
    (DerivedCategory.singleFunctor C 0).map f ≫ x.hom =
      ((mk₀ f).comp x (zero_add n)).hom := by
  simp only [comp_hom, mk₀_hom, ShiftedHom.mk₀_comp]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `preadditiveYoneda_homologySequenceδ_singleTriangle_apply` / 引理 `preadditiveYoneda_homologySequenceδ_singleTriangle_apply`

English:
lemma preadditiveYoneda_homologySequenceδ_singleTriangle_apply
  proof: by
  rw [preadditiveYoneda_homologySequenceδ_apply]; rw [comp_hom]; rw [hS.extClass_hom]; rw [ShiftedHom.comp]
  rfl

中文:
引理 preadditiveYoneda_homologySequenceδ_singleTriangle_apply
  证明: by
  rw [preadditiveYoneda_homologySequenceδ_apply]; rw [comp_hom]; rw [hS.extClass_hom]; rw [ShiftedHom.comp]
  rfl

Depends on / 依赖: ShiftedHom, ShiftedHom.comp, comp_hom, extClass_hom, hS.extClass_hom
-/
lemma preadditiveYoneda_homologySequenceδ_singleTriangle_apply
    [HasDerivedCategory.{w'} C] {Y : C} {n₀ : Nat} (x : Ext S.X₁ Y n₀)
    {n₁ : Nat} (h : 1 + n₀ = n₁) :
    (preadditiveYoneda.obj ((singleFunctor C 0).obj Y)).homologySequenceδ
      ((triangleOpEquivalence _).functor.obj (op hS.singleTriangle)) n₀ n₁ (by lia) x.hom =
      (hS.extClass.comp x h).hom := by
  rw [preadditiveYoneda_homologySequenceδ_apply]; rw [comp_hom]; rw [hS.extClass_hom]; rw [ShiftedHom.comp]
  rfl

set_option backward.defeqAttrib.useBackward true in
include hS in
/--
lemma `contravariant_sequence_exact₂'` / 引理 `contravariant_sequence_exact₂'`

English:
lemma contravariant_sequence_exact₂'
  given: (n : Nat)
  proof: by
  let := HasDerivedCategory.standard C
  have := (preadditiveYoneda.obj ((singleFunctor C 0).obj Y)).homologySequence_exact₂ _
    (op_distinguished _ hS.singleTriangle_distinguished) n
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (H := this)
  all_goals ext; apply singleFunctor_map_comp_hom (C := C)

中文:
引理 contravariant_sequence_exact₂'
  条件: (n : 自然数)
  证明: by
  let := HasDerivedCategory.standard C
  have := (preadditiveYoneda.obj ((singleFunctor C 0).obj Y)).homologySequence_exact₂ _
    (op_distinguished _ hS.singleTriangle_distinguished) n
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (H := this)
  all_goals ext; apply singleFunctor_map_comp_hom (C := C)

Depends on / 依赖: Ext.homAddEquiv, Function, Function.Exact.of_ladder_addEquiv_of_exact, HasDerivedCategory, HasDerivedCategory.standard, ShortComplex, ShortComplex.ab_exact_iff_function_exact, ab_exact_iff_function_exact, all_goals, hS.singleTriangle_distinguished, homAddEquiv, of_ladder_addEquiv_of_exact, op_distinguished, preadditiveYoneda, preadditiveYoneda.obj, singleFunctor, singleFunctor_map_comp_hom, singleTriangle_distinguished, standard
-/
lemma contravariant_sequence_exact₂' (n : Nat) :
    (ShortComplex.mk (AddCommGrpCat.ofHom ((mk₀ S.g).precomp Y (zero_add n)))
      (AddCommGrpCat.ofHom ((mk₀ S.f).precomp Y (zero_add n))) (by
        ext
        dsimp
        simp only [mk₀_comp_mk₀_assoc, ShortComplex.zero, mk₀_zero, zero_comp])).Exact := by
  let := HasDerivedCategory.standard C
  have := (preadditiveYoneda.obj ((singleFunctor C 0).obj Y)).homologySequence_exact₂ _
    (op_distinguished _ hS.singleTriangle_distinguished) n
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (H := this)
  all_goals ext; apply singleFunctor_map_comp_hom (C := C)

section

variable (n₀ n₁ : Nat) (h : 1 + n₀ = n₁)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `contravariant_sequence_exact₁'` / 引理 `contravariant_sequence_exact₁'`

English:
lemma contravariant_sequence_exact₁'
  proof: by
  let := HasDerivedCategory.standard C
  have := (preadditiveYoneda.obj ((singleFunctor C 0).obj Y)).homologySequence_exact₃ _
    (op_distinguished _ hS.singleTriangle_distinguished) n₀ n₁ (by lia)
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (H := this)
  · ext; apply singleFunctor_map_comp_hom (C := C)
  · ext; dsimp; apply preadditiveYoneda_homologySequenceδ_singleTriangle_apply

中文:
引理 contravariant_sequence_exact₁'
  证明: by
  let := HasDerivedCategory.standard C
  have := (preadditiveYoneda.obj ((singleFunctor C 0).obj Y)).homologySequence_exact₃ _
    (op_distinguished _ hS.singleTriangle_distinguished) n₀ n₁ (by lia)
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (H := this)
  · ext; apply singleFunctor_map_comp_hom (C := C)
  · ext; dsimp; apply preadditiveYoneda_homologySequenceδ_singleTriangle_apply

Depends on / 依赖: Ext.homAddEquiv, Function, Function.Exact.of_ladder_addEquiv_of_exact, HasDerivedCategory, HasDerivedCategory.standard, ShortComplex, ShortComplex.ab_exact_iff_function_exact, ab_exact_iff_function_exact, hS.singleTriangle_distinguished, homAddEquiv, of_ladder_addEquiv_of_exact, op_distinguished, preadditiveYoneda, preadditiveYoneda.obj, singleFunctor, singleFunctor_map_comp_hom, singleTriangle_distinguished, standard
-/
lemma contravariant_sequence_exact₁' :
    (ShortComplex.mk (AddCommGrpCat.ofHom (((mk₀ S.f).precomp Y (zero_add n₀))))
      (AddCommGrpCat.ofHom (hS.extClass.precomp Y h)) (by
        ext
        dsimp
        simp only [ShortComplex.ShortExact.extClass_comp_assoc])).Exact := by
  let := HasDerivedCategory.standard C
  have := (preadditiveYoneda.obj ((singleFunctor C 0).obj Y)).homologySequence_exact₃ _
    (op_distinguished _ hS.singleTriangle_distinguished) n₀ n₁ (by lia)
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (H := this)
  · ext; apply singleFunctor_map_comp_hom (C := C)
  · ext; dsimp; apply preadditiveYoneda_homologySequenceδ_singleTriangle_apply

set_option backward.defeqAttrib.useBackward true in
/--
lemma `contravariant_sequence_exact₃'` / 引理 `contravariant_sequence_exact₃'`

English:
lemma contravariant_sequence_exact₃'
  proof: by
  let := HasDerivedCategory.standard C
  have := (preadditiveYoneda.obj ((singleFunctor C 0).obj Y)).homologySequence_exact₁ _
    (op_distinguished _ hS.singleTriangle_distinguished) n₀ n₁ (by lia)
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (H := this)
  · ext; dsimp; apply preadditiveYoneda_homologySequenceδ_singleTriangle_apply
  · ext; apply singleFunctor_map_comp_hom (C := C)

中文:
引理 contravariant_sequence_exact₃'
  证明: by
  let := HasDerivedCategory.standard C
  have := (preadditiveYoneda.obj ((singleFunctor C 0).obj Y)).homologySequence_exact₁ _
    (op_distinguished _ hS.singleTriangle_distinguished) n₀ n₁ (by lia)
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (H := this)
  · ext; dsimp; apply preadditiveYoneda_homologySequenceδ_singleTriangle_apply
  · ext; apply singleFunctor_map_comp_hom (C := C)

Depends on / 依赖: Ext.homAddEquiv, Function, Function.Exact.of_ladder_addEquiv_of_exact, HasDerivedCategory, HasDerivedCategory.standard, ShortComplex, ShortComplex.ab_exact_iff_function_exact, ab_exact_iff_function_exact, hS.singleTriangle_distinguished, homAddEquiv, of_ladder_addEquiv_of_exact, op_distinguished, preadditiveYoneda, preadditiveYoneda.obj, singleFunctor, singleFunctor_map_comp_hom, singleTriangle_distinguished, standard
-/
lemma contravariant_sequence_exact₃' :
    (ShortComplex.mk (AddCommGrpCat.ofHom (hS.extClass.precomp Y h))
      (AddCommGrpCat.ofHom (((mk₀ S.g).precomp Y (zero_add n₁)))) (by
        ext
        dsimp
        simp only [ShortComplex.ShortExact.comp_extClass_assoc])).Exact := by
  let := HasDerivedCategory.standard C
  have := (preadditiveYoneda.obj ((singleFunctor C 0).obj Y)).homologySequence_exact₁ _
    (op_distinguished _ hS.singleTriangle_distinguished) n₀ n₁ (by lia)
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (H := this)
  · ext; dsimp; apply preadditiveYoneda_homologySequenceδ_singleTriangle_apply
  · ext; apply singleFunctor_map_comp_hom (C := C)

open ComposableArrows

/--
Definition of `contravariantSequence` / `contravariantSequence` 的定义

English:
definition contravariantSequence
  signature: : ComposableArrows AddCommGrpCat.{w} 5
  body: mk₅ (AddCommGrpCat.ofHom ((mk₀ S.g).precomp Y (zero_add n₀)))
    (AddCommGrpCat.ofHom ((mk₀ S.f).precomp Y (zero_add n₀)))
    (AddCommGrpCat.ofHom (hS.extClass.precomp Y h))
    (AddCommGrpCat.ofHom ((mk₀ S.g).precomp Y (zero_add n₁)))
    (AddCommGrpCat.ofHom ((mk₀ S.f).precomp Y (zero_add n₁)))

中文:
定义 contravariantSequence
  签名: : ComposableArrows 加法交换群范畴.{w} 5
  定义体: mk₅ (AddCommGrpCat.ofHom ((mk₀ S.g).precomp Y (zero_add n₀)))
    (AddCommGrpCat.ofHom ((mk₀ S.f).precomp Y (zero_add n₀)))
    (AddCommGrpCat.ofHom (hS.extClass.precomp Y h))
    (AddCommGrpCat.ofHom ((mk₀ S.g).precomp Y (zero_add n₁)))
    (AddCommGrpCat.ofHom ((mk₀ S.f).precomp Y (zero_add n₁)))

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.ofHom, extClass, hS.extClass.precomp, precomp, zero_add
-/
noncomputable def contravariantSequence : ComposableArrows AddCommGrpCat.{w} 5 :=
  mk₅ (AddCommGrpCat.ofHom ((mk₀ S.g).precomp Y (zero_add n₀)))
    (AddCommGrpCat.ofHom ((mk₀ S.f).precomp Y (zero_add n₀)))
    (AddCommGrpCat.ofHom (hS.extClass.precomp Y h))
    (AddCommGrpCat.ofHom ((mk₀ S.g).precomp Y (zero_add n₁)))
    (AddCommGrpCat.ofHom ((mk₀ S.f).precomp Y (zero_add n₁)))

/--
lemma `contravariantSequence_exact` / 引理 `contravariantSequence_exact`

English:
lemma contravariantSequence_exact
  proof: exact_of_δ₀ (contravariant_sequence_exact₂' hS Y n₀).exact_toComposableArrows
    (exact_of_δ₀ (contravariant_sequence_exact₁' hS Y n₀ n₁ h).exact_toComposableArrows
      (exact_of_δ₀ (contravariant_sequence_exact₃' hS Y n₀ n₁ h).exact_toComposableArrows
        (contravariant_sequence_exact₂' hS Y n₁).exact_toComposableArrows))

中文:
引理 contravariantSequence_exact
  证明: exact_of_δ₀ (contravariant_sequence_exact₂' hS Y n₀).exact_toComposableArrows
    (exact_of_δ₀ (contravariant_sequence_exact₁' hS Y n₀ n₁ h).exact_toComposableArrows
      (exact_of_δ₀ (contravariant_sequence_exact₃' hS Y n₀ n₁ h).exact_toComposableArrows
        (contravariant_sequence_exact₂' hS Y n₁).exact_toComposableArrows))

Depends on / 依赖: exact_toComposableArrows
-/
lemma contravariantSequence_exact :
    (contravariantSequence hS Y n₀ n₁ h).Exact :=
  exact_of_δ₀ (contravariant_sequence_exact₂' hS Y n₀).exact_toComposableArrows
    (exact_of_δ₀ (contravariant_sequence_exact₁' hS Y n₀ n₁ h).exact_toComposableArrows
      (exact_of_δ₀ (contravariant_sequence_exact₃' hS Y n₀ n₁ h).exact_toComposableArrows
        (contravariant_sequence_exact₂' hS Y n₁).exact_toComposableArrows))

end

/--
lemma `contravariant_sequence_exact₁` / 引理 `contravariant_sequence_exact₁`

English:
lemma contravariant_sequence_exact₁
  statement: {n₀ : Nat} (x₁ : Ext S.X₁ Y n₀) {n₁ : Nat} (hn₁ : 1 + n₀ = n₁)
  proof: by
  have := contravariant_sequence_exact₁' hS Y n₀ n₁ hn₁
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₁ hx₁

include hS in

中文:
引理 contravariant_sequence_exact₁
  结论: {n₀ : 自然数} (x₁ : Ext S.X₁ Y n₀) {n₁ : 自然数} (hn₁ : 1 + n₀ = n₁)
  证明: by
  have := contravariant_sequence_exact₁' hS Y n₀ n₁ hn₁
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₁ hx₁

include hS in

Depends on / 依赖: ShortComplex, ShortComplex.ab_exact_iff, ab_exact_iff, embeddingUp, infer_instance
-/
lemma contravariant_sequence_exact₁ {n₀ : Nat} (x₁ : Ext S.X₁ Y n₀) {n₁ : Nat} (hn₁ : 1 + n₀ = n₁)
    (hx₁ : hS.extClass.comp x₁ hn₁ = 0) :
    exists (x₂ : Ext S.X₂ Y n₀), (mk₀ S.f).comp x₂ (zero_add n₀) = x₁ := by
  have := contravariant_sequence_exact₁' hS Y n₀ n₁ hn₁
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₁ hx₁

include hS in
/--
lemma `contravariant_sequence_exact₂` / 引理 `contravariant_sequence_exact₂`

English:
lemma contravariant_sequence_exact₂
  statement: {n : Nat} (x₂ : Ext S.X₂ Y n)
  proof: by
  have := contravariant_sequence_exact₂' hS Y n
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₂ hx₂

中文:
引理 contravariant_sequence_exact₂
  结论: {n : 自然数} (x₂ : Ext S.X₂ Y n)
  证明: by
  have := contravariant_sequence_exact₂' hS Y n
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₂ hx₂

Depends on / 依赖: ShortComplex, ShortComplex.ab_exact_iff, ab_exact_iff, add_right_comm
-/
lemma contravariant_sequence_exact₂ {n : Nat} (x₂ : Ext S.X₂ Y n)
    (hx₂ : (mk₀ S.f).comp x₂ (zero_add n) = 0) :
    exists (x₁ : Ext S.X₃ Y n), (mk₀ S.g).comp x₁ (zero_add n) = x₂ := by
  have := contravariant_sequence_exact₂' hS Y n
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₂ hx₂

/--
lemma `contravariant_sequence_exact₃` / 引理 `contravariant_sequence_exact₃`

English:
lemma contravariant_sequence_exact₃
  statement: {n₁ : Nat} (x₃ : Ext S.X₃ Y n₁)
  proof: by
  have := contravariant_sequence_exact₃' hS Y n₀ n₁ hn₀
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₃ hx₃

中文:
引理 contravariant_sequence_exact₃
  结论: {n₁ : 自然数} (x₃ : Ext S.X₃ Y n₁)
  证明: by
  have := contravariant_sequence_exact₃' hS Y n₀ n₁ hn₀
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₃ hx₃

Depends on / 依赖: ShortComplex, ShortComplex.ab_exact_iff, ab_exact_iff
-/
lemma contravariant_sequence_exact₃ {n₁ : Nat} (x₃ : Ext S.X₃ Y n₁)
    (hx₃ : (mk₀ S.g).comp x₃ (zero_add n₁) = 0) {n₀ : Nat} (hn₀ : 1 + n₀ = n₁) :
    exists (x₁ : Ext S.X₁ Y n₀), hS.extClass.comp x₁ hn₀ = x₃ := by
  have := contravariant_sequence_exact₃' hS Y n₀ n₁ hn₀
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₃ hx₃

/--
lemma `precomp_mk₀_injective_of_epi` / 引理 `precomp_mk₀_injective_of_epi`

English:
lemma precomp_mk₀_injective_of_epi
  given: (L : C) {M N : C} (g : M ⟶ N) [hg : Epi g]
  proof: by
  rw [← AddMonoidHom.ker_eq_bot_iff]; rw [AddSubgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨f, rfl⟩ := Ext.addEquiv₀.symm.surjective x
  simpa [← cancel_epi g] using hx

中文:
引理 precomp_mk₀_injective_of_epi
  条件: (L : C) {M N : C} (g : M ⟶ N) [hg : 满态射 g]
  证明: by
  rw [← AddMonoidHom.ker_eq_bot_iff]; rw [AddSubgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨f, rfl⟩ := Ext.addEquiv₀.symm.surjective x
  simpa [← cancel_epi g] using hx

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ker_eq_bot_iff, AddSubgroup, AddSubgroup.eq_bot_iff_forall, Ext.addEquiv, cancel_epi, embeddingDown, eq_bot_iff_forall, infer_instance, ker_eq_bot_iff, surjective, symm.surjective
-/
lemma precomp_mk₀_injective_of_epi (L : C) {M N : C} (g : M ⟶ N) [hg : Epi g] :
    Function.Injective ((Ext.mk₀ g).precomp L (zero_add 0)) := by
  rw [← AddMonoidHom.ker_eq_bot_iff]; rw [AddSubgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨f, rfl⟩ := Ext.addEquiv₀.symm.surjective x
  simpa [← cancel_epi g] using hx

/--
lemma `mono_precomp_mk₀_of_epi` / 引理 `mono_precomp_mk₀_of_epi`

English:
lemma mono_precomp_mk₀_of_epi
  given: (L : C) {M N : C} (g : M ⟶ N) [hg : Epi g]
  proof: (AddCommGrpCat.mono_iff_injective _).mpr (precomp_mk₀_injective_of_epi L g)

中文:
引理 mono_precomp_mk₀_of_epi
  条件: (L : C) {M N : C} (g : M ⟶ N) [hg : 满态射 g]
  证明: (AddCommGrpCat.mono_iff_injective _).mpr (precomp_mk₀_injective_of_epi L g)

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.mono_iff_injective, add_right_comm, mono_iff_injective
-/
lemma mono_precomp_mk₀_of_epi (L : C) {M N : C} (g : M ⟶ N) [hg : Epi g] :
    Mono (AddCommGrpCat.ofHom <| (Ext.mk₀ g).precomp L (zero_add 0)) :=
  (AddCommGrpCat.mono_iff_injective _).mpr (precomp_mk₀_injective_of_epi L g)

end ContravariantSequence

end Ext

end Abelian

end CategoryTheory
