/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!
# Localization of natural transformations to preadditive categories

-/

public section

namespace CategoryTheory

open Limits

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]

namespace Localization

variable (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `liftNatTrans_zero` / 引理 `liftNatTrans_zero`

English:
lemma liftNatTrans_zero
  statement: (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E)
  proof: natTrans_ext L W (by simp)

中文:
引理 lift自然数Trans_zero
  结论: (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E)
  证明: natTrans_ext L W (by simp)

Depends on / 依赖: natTrans_ext
-/
lemma liftNatTrans_zero (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E)
    [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂']
    [HasZeroMorphisms E] :
    liftNatTrans L W F₁ F₂ F₁' F₂' 0 = 0 :=
  natTrans_ext L W (by simp)

variable [Preadditive E]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `liftNatTrans_add` / 引理 `liftNatTrans_add`

English:
lemma liftNatTrans_add
  statement: (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E)
  proof: natTrans_ext L W (by simp)

中文:
引理 lift自然数Trans_add
  结论: (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E)
  证明: natTrans_ext L W (by simp)

Depends on / 依赖: natTrans_ext
-/
lemma liftNatTrans_add (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E)
    [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂']
    (τ τ' : F₁ ⟶ F₂) :
    liftNatTrans L W F₁ F₂ F₁' F₂' (τ + τ') =
      liftNatTrans L W F₁ F₂ F₁' F₂' τ + liftNatTrans L W F₁ F₂ F₁' F₂' τ' :=
  natTrans_ext L W (by simp)

end Localization

end CategoryTheory
