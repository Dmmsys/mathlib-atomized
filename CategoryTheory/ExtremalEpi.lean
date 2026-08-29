/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Limits.Shapes.StrongEpi

/-!
# Extremal epimorphisms

An extremal epimorphism `p : X ⟶ Y` is an epimorphism which does not factor
through any proper subobject of `Y`. In case the category has equalizers,
we show that a morphism `p : X ⟶ Y` which does not factor through
any proper subobject of `Y` is automatically an epimorphism, and also
an extremal epimorphism. We also show that a strong epimorphism
is an extremal epimorphism, and that both notions coincide when
the category has pullbacks.

## References

* https://ncatlab.org/nlab/show/extremal+epimorphism

-/

public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {X Y : C}

/--
Definition of `ExtremalEpi` / `ExtremalEpi` 的定义

English:
class ExtremalEpi
  parameters: (f : X ⟶ Y)
  extends: Epi f
  axioms and operations (1):
    - isIso((f) {Z : C} (p : X ⟶ Z) (i : Z ⟶ Y) (fac : p ≫ i = f) [Mono i]) : IsIso i

中文:
类 极端满态射
  参数: (f : X ⟶ Y)
  继承: 满态射 f
  公理与运算 (1 个):
    - isIso((f) {Z : C} (p : X ⟶ Z) (i : Z ⟶ Y) (fac : p ≫ i = f) [单态射 i]) : 是同构 i
-/
class ExtremalEpi (f : X ⟶ Y) : Prop extends Epi f where
  isIso (f) {Z : C} (p : X ⟶ Z) (i : Z ⟶ Y) (fac : p ≫ i = f) [Mono i] : IsIso i

variable (f : X ⟶ Y)

/--
lemma `ExtremalEpi.subobject_eq_top` / 引理 `ExtremalEpi.subobject_eq_top`

English:
lemma ExtremalEpi.subobject_eq_top
  statement: [ExtremalEpi f]
  proof: by
  rw [← Subobject.isIso_arrow_iff_eq_top]
  exact isIso f (Subobject.factorThru A f hA) _ (by simp)

中文:
引理 极端满态射.subobject_eq_top
  结论: [极端满态射 f]
  证明: by
  rw [← Subobject.isIso_arrow_iff_eq_top]
  exact isIso f (Subobject.factorThru A f hA) _ (by simp)

Depends on / 依赖: Subobject, Subobject.factorThru, Subobject.isIso_arrow_iff_eq_top, factorThru, isIso_arrow_iff_eq_top
-/
lemma ExtremalEpi.subobject_eq_top [ExtremalEpi f]
    {A : Subobject Y} (hA : Subobject.Factors A f) : A = ⊤ := by
  rw [← Subobject.isIso_arrow_iff_eq_top]
  exact isIso f (Subobject.factorThru A f hA) _ (by simp)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `ExtremalEpi.mk_of_hasEqualizers` / 引理 `ExtremalEpi.mk_of_hasEqualizers`

English:
lemma ExtremalEpi.mk_of_hasEqualizers
  statement: [HasEqualizers C]
  proof: by
    have := hf (equalizer.lift f h) (equalizer.ι p q) (by simp)
    rw [← cancel_epi (equalizer.ι p q)]; rw [equalizer.condition]
  isIso := by tauto

中文:
引理 极端满态射.mk_of_hasEqualizers
  结论: [HasEqualizers C]
  证明: by
    have := hf (equalizer.lift f h) (equalizer.ι p q) (by simp)
    rw [← cancel_epi (equalizer.ι p q)]; rw [equalizer.condition]
  isIso := by tauto

Depends on / 依赖: cancel_epi, condition, equalizer, equalizer.condition, equalizer.lift
-/
lemma ExtremalEpi.mk_of_hasEqualizers [HasEqualizers C]
    (hf : forall ⦃Z : C⦄ (p : X ⟶ Z) (i : Z ⟶ Y) (_ : p ≫ i = f) [Mono i], IsIso i) :
    ExtremalEpi f where
  left_cancellation {Z} p q h := by
    have := hf (equalizer.lift f h) (equalizer.ι p q) (by simp)
    rw [← cancel_epi (equalizer.ι p q)]; rw [equalizer.condition]
  isIso := by tauto

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [StrongEpi
  signature: f] : ExtremalEpi f where
  body: by
    have sq : CommSq p f i (𝟙 Y) := { }
    exact ⟨sq.lift, by simp [← cancel_mono i], by simp⟩

中文:
实例 [强满态射
  签名: f] : 极端满态射 f where
  定义体: by
    have sq : CommSq p f i (𝟙 Y) := { }
    exact ⟨sq.lift, by simp [← cancel_mono i], by simp⟩

Depends on / 依赖: CommSq, cancel_mono, sq.lift
-/
instance [StrongEpi f] : ExtremalEpi f where
  isIso {Z} p i fac _ := by
    have sq : CommSq p f i (𝟙 Y) := { }
    exact ⟨sq.lift, by simp [← cancel_mono i], by simp⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `extremalEpi_iff_strongEpi_of_hasPullbacks` / 引理 `extremalEpi_iff_strongEpi_of_hasPullbacks`

English:
lemma extremalEpi_iff_strongEpi_of_hasPullbacks
  given: [HasPullbacks C]
  proof: by
  refine ⟨fun _ => ⟨inferInstance, fun A B i _ => ⟨fun {t b} sq => ⟨⟨?_⟩⟩⟩⟩,
    fun _ => inferInstance⟩
  have := ExtremalEpi.isIso f (pullback.lift _ _ sq.w)
    (pullback.snd _ _) (by simp)
  exact
    { l := inv (pullback.snd i b) ≫ pullback.fst _ _
      fac_left := by
        rw [← cancel_m

中文:
引理 extremalEpi_iff_strongEpi_of_hasPullbacks
  条件: [有Pullbacks C]
  证明: by
  refine ⟨fun _ => ⟨inferInstance, fun A B i _ => ⟨fun {t b} sq => ⟨⟨?_⟩⟩⟩⟩,
    fun _ => inferInstance⟩
  have := ExtremalEpi.isIso f (pullback.lift _ _ sq.w)
    (pullback.snd _ _) (by simp)
  exact
    { l := inv (pullback.snd i b) ≫ pullback.fst _ _
      fac_left := by
        rw [← cancel_m

Depends on / 依赖: Category, Category.assoc, ExtremalEpi, ExtremalEpi.isIso, IsIso.hom_inv_id_assoc, cancel_epi, cancel_mono, condition, fac_left, fac_right, hom_inv_id_assoc, pullback, pullback.condition, pullback.fst, pullback.lift, pullback.snd, sq.w
-/
lemma extremalEpi_iff_strongEpi_of_hasPullbacks [HasPullbacks C] :
    ExtremalEpi f ↔ StrongEpi f := by
  refine ⟨fun _ => ⟨inferInstance, fun A B i _ => ⟨fun {t b} sq => ⟨⟨?_⟩⟩⟩⟩,
    fun _ => inferInstance⟩
  have := ExtremalEpi.isIso f (pullback.lift _ _ sq.w)
    (pullback.snd _ _) (by simp)
  exact
    { l := inv (pullback.snd i b) ≫ pullback.fst _ _
      fac_left := by
        rw [← cancel_mono i]; rw [sq.w]; rw [Category.assoc]; rw [Category.assoc]
        congr 1
        rw [← cancel_epi (pullback.snd i b)]; rw [IsIso.hom_inv_id_assoc]; rw [pullback.condition]
      fac_right := by simp [pullback.condition] }

end CategoryTheory
