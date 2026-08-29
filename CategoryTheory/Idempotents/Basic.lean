/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Idempotent complete categories

In this file, we define the notion of idempotent complete categories
(also known as Karoubian categories, or pseudoabelian in the case of
preadditive categories).

## Main definitions

- `IsIdempotentComplete C` expresses that `C` is idempotent complete, i.e.
  all idempotents in `C` split. Other characterisations of idempotent completeness are given
  by `isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent` and
  `isIdempotentComplete_iff_idempotents_have_kernels`.
- `isIdempotentComplete_of_abelian` expresses that abelian categories are
  idempotent complete.
- `isIdempotentComplete_iff_ofEquivalence` expresses that if two categories `C` and `D`
  are equivalent, then `C` is idempotent complete iff `D` is.
- `isIdempotentComplete_iff_opposite` expresses that `Cᵒᵖ` is idempotent complete
  iff `C` is.

## References
* [Stacks: Karoubian categories] https://stacks.math.columbia.edu/tag/09SF

-/

public section


open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Limits

open CategoryTheory.Preadditive

open Opposite

namespace CategoryTheory

variable (C : Type*) [Category* C]

/--
Definition of `IsIdempotentComplete` / `IsIdempotentComplete` 的定义

English:
class IsIdempotentComplete
  parameters: : Prop where
  axioms and operations (1):
    - idempotents_split : forall (X : C) (p : X ⟶ X), p ≫ p = p -> exists (Y : C) (i : Y ⟶ X) (e : X ⟶ Y), i ≫ e = 𝟙 Y ∧ e ≫ i = p

中文:
类 IsIdempotentComplete
  参数: : 命题 where
  公理与运算 (1 个):
    - idempotents_split : 对任意 (X : C) (p : X ⟶ X), p ≫ p = p -> 存在 (Y : C) (i : Y ⟶ X) (e : X ⟶ Y), i ≫ e = 𝟙 Y ∧ e ≫ i = p
-/
class IsIdempotentComplete : Prop where
  /-- A category is idempotent complete iff all idempotent endomorphisms `p`
  split as a composition `p = e ≫ i` with `i ≫ e = 𝟙 _` -/
  idempotents_split :
    forall (X : C) (p : X ⟶ X), p ≫ p = p -> exists (Y : C) (i : Y ⟶ X) (e : X ⟶ Y), i ≫ e = 𝟙 Y ∧ e ≫ i = p

namespace Idempotents

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent` / 定理 `isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent`

English:
theorem isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent
  proof: by
  constructor
  · intro _ X p hp
    rcases IsIdempotentComplete.idempotents_split X p hp with ⟨Y, i, e, ⟨h₁, h₂⟩⟩
    exact
      ⟨Nonempty.intro
          { cone := Fork.ofι i (show i ≫ 𝟙 X = i ≫ p by rw [comp_id, ← h₂, ← assoc, h₁, id_comp])
            isLimit := by
              apply Fork.I

中文:
定理 isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent
  证明: by
  constructor
  · intro _ X p hp
    rcases IsIdempotentComplete.idempotents_split X p hp with ⟨Y, i, e, ⟨h₁, h₂⟩⟩
    exact
      ⟨Nonempty.intro
          { cone := Fork.ofι i (show i ≫ 𝟙 X = i ≫ p by rw [comp_id, ← h₂, ← assoc, h₁, id_comp])
            isLimit := by
              apply Fork.I

Depends on / 依赖: Fork.IsLimit.mk, Fork.of, HasEqualizer, IsIdempotentComplete, IsIdempotentComplete.idempotents_split, IsLimit, Limits, Limits.Fork.condition, Nonempty, Nonempty.intro, comp_id, condition, id_comp, idempotents_split, isLimit
-/
theorem isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent :
    IsIdempotentComplete C ↔ forall (X : C) (p : X ⟶ X), p ≫ p = p -> HasEqualizer (𝟙 X) p := by
  constructor
  · intro _ X p hp
    rcases IsIdempotentComplete.idempotents_split X p hp with ⟨Y, i, e, ⟨h₁, h₂⟩⟩
    exact
      ⟨Nonempty.intro
          { cone := Fork.ofι i (show i ≫ 𝟙 X = i ≫ p by rw [comp_id, ← h₂, ← assoc, h₁, id_comp])
            isLimit := by
              apply Fork.IsLimit.mk'
              intro s
              refine ⟨s.ι ≫ e, ?_⟩
              constructor
              · simp [h₂, ← Limits.Fork.condition s]
              · intro m hm
                rw [Fork.ι_ofι] at hm
                rw [← hm]
                simp only [assoc, h₁]
                exact (comp_id m).symm }⟩
  · intro h
    refine ⟨?_⟩
    intro X p hp
    have : HasEqualizer (𝟙 X) p := h X p hp
    refine ⟨equalizer (𝟙 X) p, equalizer.ι (𝟙 X) p,
      equalizer.lift p (show p ≫ 𝟙 X = p ≫ p by rw [hp, comp_id]), ?_, equalizer.lift_ι _ _⟩
    ext
    simp only [assoc, limit.lift_π,
      Fork.ofι_π_app, id_comp]
    rw [← equalizer.condition]; rw [comp_id]

variable {C} in
/--
theorem `idem_of_id_sub_idem` / 定理 `idem_of_id_sub_idem`

English:
theorem idem_of_id_sub_idem
  given: [Preadditive C] {X : C} (p : X ⟶ X) (hp : p ≫ p = p)
  proof: by
  simp only [comp_sub, sub_comp, id_comp, comp_id, hp, sub_self, sub_zero]

中文:
定理 idem_of_id_sub_idem
  条件: [Preadditive C] {X : C} (p : X ⟶ X) (hp : p ≫ p = p)
  证明: by
  simp only [comp_sub, sub_comp, id_comp, comp_id, hp, sub_self, sub_zero]

Depends on / 依赖: comp_id, comp_sub, id_comp, sub_comp, sub_self, sub_zero
-/
theorem idem_of_id_sub_idem [Preadditive C] {X : C} (p : X ⟶ X) (hp : p ≫ p = p) :
    (𝟙 _ - p) ≫ (𝟙 _ - p) = 𝟙 _ - p := by
  simp only [comp_sub, sub_comp, id_comp, comp_id, hp, sub_self, sub_zero]

/--
theorem `isIdempotentComplete_iff_idempotents_have_kernels` / 定理 `isIdempotentComplete_iff_idempotents_have_kernels`

English:
theorem isIdempotentComplete_iff_idempotents_have_kernels
  given: [Preadditive C]
  proof: by
  rw [isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent]
  constructor
  · intro h X p hp
    have : HasEqualizer (𝟙 X) (𝟙 X - p) := h X (𝟙 _ - p) (idem_of_id_sub_idem p hp)
    convert! hasKernel_of_hasEqualizer (𝟙 X) (𝟙 X - p)
    rw [sub_sub_cancel]
  · intro h X p hp
    have : HasKe

中文:
定理 isIdempotentComplete_iff_idempotents_have_kernels
  条件: [Preadditive C]
  证明: by
  rw [isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent]
  constructor
  · intro h X p hp
    have : HasEqualizer (𝟙 X) (𝟙 X - p) := h X (𝟙 _ - p) (idem_of_id_sub_idem p hp)
    convert! hasKernel_of_hasEqualizer (𝟙 X) (𝟙 X - p)
    rw [sub_sub_cancel]
  · intro h X p hp
    have : HasKe

Depends on / 依赖: HasEqualizer, HasKernel, Preadditive, Preadditive.hasEqualizer_of_hasKernel, convert, hasEqualizer_of_hasKernel, hasKernel_of_hasEqualizer, idem_of_id_sub_idem, isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent, sub_sub_cancel
-/
theorem isIdempotentComplete_iff_idempotents_have_kernels [Preadditive C] :
    IsIdempotentComplete C ↔ forall (X : C) (p : X ⟶ X), p ≫ p = p -> HasKernel p := by
  rw [isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent]
  constructor
  · intro h X p hp
    have : HasEqualizer (𝟙 X) (𝟙 X - p) := h X (𝟙 _ - p) (idem_of_id_sub_idem p hp)
    convert! hasKernel_of_hasEqualizer (𝟙 X) (𝟙 X - p)
    rw [sub_sub_cancel]
  · intro h X p hp
    have : HasKernel (𝟙 _ - p) := h X (𝟙 _ - p) (idem_of_id_sub_idem p hp)
    apply Preadditive.hasEqualizer_of_hasKernel

/-- An abelian category is idempotent complete. -/
instance (priority := 100) isIdempotentComplete_of_abelian (D : Type*) [Category* D] [Abelian D] :
    IsIdempotentComplete D := by
  rw [isIdempotentComplete_iff_idempotents_have_kernels]
  intros
  infer_instance

variable {C}

/--
theorem `split_imp_of_iso` / 定理 `split_imp_of_iso`

English:
theorem split_imp_of_iso
  statement: {X X' : C} (φ : X ≅ X') (p : X ⟶ X) (p' : X' ⟶ X')
  proof: by
  rcases h with ⟨Y, i, e, ⟨h₁, h₂⟩⟩
  use Y, i ≫ φ.hom, φ.inv ≫ e
  grind

中文:
定理 split_imp_of_iso
  结论: {X X' : C} (φ : X ≅ X') (p : X ⟶ X) (p' : X' ⟶ X')
  证明: by
  rcases h with ⟨Y, i, e, ⟨h₁, h₂⟩⟩
  use Y, i ≫ φ.hom, φ.inv ≫ e
  grind
-/
theorem split_imp_of_iso {X X' : C} (φ : X ≅ X') (p : X ⟶ X) (p' : X' ⟶ X')
    (hpp' : p ≫ φ.hom = φ.hom ≫ p')
    (h : exists (Y : C) (i : Y ⟶ X) (e : X ⟶ Y), i ≫ e = 𝟙 Y ∧ e ≫ i = p) :
    exists (Y' : C) (i' : Y' ⟶ X') (e' : X' ⟶ Y'), i' ≫ e' = 𝟙 Y' ∧ e' ≫ i' = p' := by
  rcases h with ⟨Y, i, e, ⟨h₁, h₂⟩⟩
  use Y, i ≫ φ.hom, φ.inv ≫ e
  grind

/--
theorem `split_iff_of_iso` / 定理 `split_iff_of_iso`

English:
theorem split_iff_of_iso
  statement: {X X' : C} (φ : X ≅ X') (p : X ⟶ X) (p' : X' ⟶ X')
  proof: by
  constructor
  · exact split_imp_of_iso φ p p' hpp'
  · apply split_imp_of_iso φ.symm p' p
    rw [← comp_id p]; rw [← φ.hom_inv_id]
    slice_rhs 2 3 => rw [hpp']
    simp

中文:
定理 split_iff_of_iso
  结论: {X X' : C} (φ : X ≅ X') (p : X ⟶ X) (p' : X' ⟶ X')
  证明: by
  constructor
  · exact split_imp_of_iso φ p p' hpp'
  · apply split_imp_of_iso φ.symm p' p
    rw [← comp_id p]; rw [← φ.hom_inv_id]
    slice_rhs 2 3 => rw [hpp']
    simp

Depends on / 依赖: comp_id, hom_inv_id, slice_rhs, split_imp_of_iso
-/
theorem split_iff_of_iso {X X' : C} (φ : X ≅ X') (p : X ⟶ X) (p' : X' ⟶ X')
    (hpp' : p ≫ φ.hom = φ.hom ≫ p') :
    (exists (Y : C) (i : Y ⟶ X) (e : X ⟶ Y), i ≫ e = 𝟙 Y ∧ e ≫ i = p) ↔
      exists (Y' : C) (i' : Y' ⟶ X') (e' : X' ⟶ Y'), i' ≫ e' = 𝟙 Y' ∧ e' ≫ i' = p' := by
  constructor
  · exact split_imp_of_iso φ p p' hpp'
  · apply split_imp_of_iso φ.symm p' p
    rw [← comp_id p]; rw [← φ.hom_inv_id]
    slice_rhs 2 3 => rw [hpp']
    simp

/--
theorem `Equivalence.isIdempotentComplete` / 定理 `Equivalence.isIdempotentComplete`

English:
theorem Equivalence.isIdempotentComplete
  statement: {D : Type*} [Category* D] (ε : C ≌ D)
  proof: by
  refine ⟨?_⟩
  intro X' p hp
  let φ := ε.counitIso.symm.app X'
  simp only [Functor.id_obj] at φ
  rw [split_iff_of_iso φ p (φ.inv ≫ p ≫ φ.hom)
      (by
        slice_rhs 1 2 => rw [φ.hom_inv_id]
        rw [id_comp])]
  rcases IsIdempotentComplete.idempotents_split (ε.inverse.obj X') (ε.inver

中文:
定理 Equivalence.isIdempotentComplete
  结论: {D : 类型} [Category* D] (ε : C ≌ D)
  证明: by
  refine ⟨?_⟩
  intro X' p hp
  let φ := ε.counitIso.symm.app X'
  simp only [Functor.id_obj] at φ
  rw [split_iff_of_iso φ p (φ.inv ≫ p ≫ φ.hom)
      (by
        slice_rhs 1 2 => rw [φ.hom_inv_id]
        rw [id_comp])]
  rcases IsIdempotentComplete.idempotents_split (ε.inverse.obj X') (ε.inver

Depends on / 依赖: Equivalen, Functor, Functor.id_obj, IsIdempotentComplete, IsIdempotentComplete.idempotents_split, counitIso, counitIso.symm.app, functor, functor.map, functor.map_comp, functor.map_id, functor.obj, hom_inv_id, id_comp, id_obj, idempotents_split, inverse, inverse.map, inverse.map_comp, inverse.obj
-/
theorem Equivalence.isIdempotentComplete {D : Type*} [Category* D] (ε : C ≌ D)
    (h : IsIdempotentComplete C) : IsIdempotentComplete D := by
  refine ⟨?_⟩
  intro X' p hp
  let φ := ε.counitIso.symm.app X'
  simp only [Functor.id_obj] at φ
  rw [split_iff_of_iso φ p (φ.inv ≫ p ≫ φ.hom)
      (by
        slice_rhs 1 2 => rw [φ.hom_inv_id]
        rw [id_comp])]
  rcases IsIdempotentComplete.idempotents_split (ε.inverse.obj X') (ε.inverse.map p)
      (by rw [← ε.inverse.map_comp, hp]) with
    ⟨Y, i, e, ⟨h₁, h₂⟩⟩
  use ε.functor.obj Y, ε.functor.map i, ε.functor.map e
  constructor
  · rw [← ε.functor.map_comp, h₁, ε.functor.map_id]
  · simp only [← ε.functor.map_comp, h₂, Equivalence.fun_inv_map]
    rfl

/--
theorem `isIdempotentComplete_iff_of_equivalence` / 定理 `isIdempotentComplete_iff_of_equivalence`

English:
theorem isIdempotentComplete_iff_of_equivalence
  given: {D : Type*} [Category* D] (ε : C ≌ D)
  proof: by
  constructor
  · exact Equivalence.isIdempotentComplete ε
  · exact Equivalence.isIdempotentComplete ε.symm

中文:
定理 isIdempotentComplete_iff_of_equivalence
  条件: {D : 类型} [Category* D] (ε : C ≌ D)
  证明: by
  constructor
  · exact Equivalence.isIdempotentComplete ε
  · exact Equivalence.isIdempotentComplete ε.symm

Depends on / 依赖: Equivalence, Equivalence.isIdempotentComplete, isIdempotentComplete
-/
theorem isIdempotentComplete_iff_of_equivalence {D : Type*} [Category* D] (ε : C ≌ D) :
    IsIdempotentComplete C ↔ IsIdempotentComplete D := by
  constructor
  · exact Equivalence.isIdempotentComplete ε
  · exact Equivalence.isIdempotentComplete ε.symm

/--
theorem `isIdempotentComplete_of_isIdempotentComplete_opposite` / 定理 `isIdempotentComplete_of_isIdempotentComplete_opposite`

English:
theorem isIdempotentComplete_of_isIdempotentComplete_opposite
  given: (h : IsIdempotentComplete Cᵒᵖ)
  proof: by
  refine ⟨?_⟩
  intro X p hp
  rcases IsIdempotentComplete.idempotents_split (op X) p.op (by rw [← op_comp, hp]) with
    ⟨Y, i, e, ⟨h₁, h₂⟩⟩
  use Y.unop, e.unop, i.unop
  constructor
  · simp only [← unop_comp, h₁]
    rfl
  · simp only [← unop_comp, h₂]
    rfl

中文:
定理 isIdempotentComplete_of_isIdempotentComplete_opposite
  条件: (h : IsIdempotentComplete Cᵒᵖ)
  证明: by
  refine ⟨?_⟩
  intro X p hp
  rcases IsIdempotentComplete.idempotents_split (op X) p.op (by rw [← op_comp, hp]) with
    ⟨Y, i, e, ⟨h₁, h₂⟩⟩
  use Y.unop, e.unop, i.unop
  constructor
  · simp only [← unop_comp, h₁]
    rfl
  · simp only [← unop_comp, h₂]
    rfl

Depends on / 依赖: IsIdempotentComplete, IsIdempotentComplete.idempotents_split, Y.unop, e.unop, i.unop, idempotents_split, op_comp, p.op, unop_comp
-/
theorem isIdempotentComplete_of_isIdempotentComplete_opposite (h : IsIdempotentComplete Cᵒᵖ) :
    IsIdempotentComplete C := by
  refine ⟨?_⟩
  intro X p hp
  rcases IsIdempotentComplete.idempotents_split (op X) p.op (by rw [← op_comp, hp]) with
    ⟨Y, i, e, ⟨h₁, h₂⟩⟩
  use Y.unop, e.unop, i.unop
  constructor
  · simp only [← unop_comp, h₁]
    rfl
  · simp only [← unop_comp, h₂]
    rfl

/--
theorem `isIdempotentComplete_iff_opposite` / 定理 `isIdempotentComplete_iff_opposite`

English:
theorem isIdempotentComplete_iff_opposite
  statement: IsIdempotentComplete Cᵒᵖ ↔ IsIdempotentComplete C
  proof: by
  constructor
  · exact isIdempotentComplete_of_isIdempotentComplete_opposite
  · intro h
    apply isIdempotentComplete_of_isIdempotentComplete_opposite
    rw [isIdempotentComplete_iff_of_equivalence (opOpEquivalence C)]
    exact h

中文:
定理 isIdempotentComplete_iff_opposite
  结论: IsIdempotentComplete Cᵒᵖ ↔ IsIdempotentComplete C
  证明: by
  constructor
  · exact isIdempotentComplete_of_isIdempotentComplete_opposite
  · intro h
    apply isIdempotentComplete_of_isIdempotentComplete_opposite
    rw [isIdempotentComplete_iff_of_equivalence (opOpEquivalence C)]
    exact h

Depends on / 依赖: isIdempotentComplete_iff_of_equivalence, isIdempotentComplete_of_isIdempotentComplete_opposite, opOpEquivalence
-/
theorem isIdempotentComplete_iff_opposite : IsIdempotentComplete Cᵒᵖ ↔ IsIdempotentComplete C := by
  constructor
  · exact isIdempotentComplete_of_isIdempotentComplete_opposite
  · intro h
    apply isIdempotentComplete_of_isIdempotentComplete_opposite
    rw [isIdempotentComplete_iff_of_equivalence (opOpEquivalence C)]
    exact h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsIdempotentComplete
  signature: C] : IsIdempotentComplete Cᵒᵖ
  body: by
  rwa [isIdempotentComplete_iff_opposite]

中文:
实例 [IsIdempotentComplete
  签名: C] : IsIdempotentComplete Cᵒᵖ
  定义体: by
  rwa [isIdempotentComplete_iff_opposite]

Depends on / 依赖: Order.not_isSuccLimit_of_isSuccArchimedean, isIdempotentComplete_iff_opposite, not_isSuccLimit_of_isSuccArchimedean
-/
instance [IsIdempotentComplete C] : IsIdempotentComplete Cᵒᵖ := by
  rwa [isIdempotentComplete_iff_opposite]

end Idempotents

end CategoryTheory
