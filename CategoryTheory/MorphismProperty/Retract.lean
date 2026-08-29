/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Retract
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Stability under retracts

Given `P : MorphismProperty C`, we introduce a typeclass `P.IsStableUnderRetracts` which
is the property that `P` is stable under retracts.

-/

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

/-- A class of morphisms is stable under retracts if a retract of such a morphism still
lies in the class. -/
@[mk_iff]
/--
Definition of `IsStableUnderRetracts` / `IsStableUnderRetracts` 的定义

English:
class IsStableUnderRetracts
  parameters: (P : MorphismProperty C)
  axioms and operations (1):
    - of_retract({X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W} (h : RetractArrow f g) (hg : P g)) : P f

中文:
类 IsStableUnderRetracts
  参数: (P : Morphism命题erty C)
  公理与运算 (1 个):
    - of_retract({X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W} (h : RetractArrow f g) (hg : P g)) : P f
-/
class IsStableUnderRetracts (P : MorphismProperty C) : Prop where
  of_retract {X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W} (h : RetractArrow f g) (hg : P g) : P f

/--
lemma `of_retract` / 引理 `of_retract`

English:
lemma of_retract
  statement: {P : MorphismProperty C} [P.IsStableUnderRetracts]
  proof: IsStableUnderRetracts.of_retract h hg

中文:
引理 of_retract
  结论: {P : Morphism命题erty C} [P.IsStableUnderRetracts]
  证明: IsStableUnderRetracts.of_retract h hg

Depends on / 依赖: IsStableUnderRetracts, IsStableUnderRetracts.of_retract, of_retract
-/
lemma of_retract {P : MorphismProperty C} [P.IsStableUnderRetracts]
    {X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W} (h : RetractArrow f g) (hg : P g) : P f :=
  IsStableUnderRetracts.of_retract h hg

instance {D : Type*} [Category* D] (F : C ⥤ D) (P : MorphismProperty D)
    [P.IsStableUnderRetracts] :
    (P.inverseImage F).IsStableUnderRetracts where
  of_retract h₁ h₂ := of_retract (P := P) (h₁.map F) h₂

set_option backward.isDefEq.respectTransparency false in
/--
Instance `IsStableUnderRetracts.monomorphisms` / 实例 `IsStableUnderRetracts.monomorphisms`

English:
instance IsStableUnderRetracts.monomorphisms
  signature: : (monomorphisms C).IsStableUnderRetracts where
  body: ⟨fun α β w => by
    rw [← cancel_mono h.i.left]; rw [← cancel_mono g]; rw [Category.assoc]; rw [Category.assoc]; rw [h.i_w]; rw [reassoc_of% w]⟩

中文:
实例 IsStableUnderRetracts.monomorphisms
  签名: : (monomorphisms C).IsStableUnderRetracts where
  定义体: ⟨fun α β w => by
    rw [← cancel_mono h.i.left]; rw [← cancel_mono g]; rw [Category.assoc]; rw [Category.assoc]; rw [h.i_w]; rw [reassoc_of% w]⟩

Depends on / 依赖: Category, Category.assoc, cancel_mono, h.i.left, h.i_w, reassoc_of
-/
instance IsStableUnderRetracts.monomorphisms : (monomorphisms C).IsStableUnderRetracts where
  of_retract {_ _ _ _ f g} h (hg : Mono g) := ⟨fun α β w => by
    rw [← cancel_mono h.i.left]; rw [← cancel_mono g]; rw [Category.assoc]; rw [Category.assoc]; rw [h.i_w]; rw [reassoc_of% w]⟩

set_option backward.isDefEq.respectTransparency false in
/--
Instance `IsStableUnderRetracts.epimorphisms` / 实例 `IsStableUnderRetracts.epimorphisms`

English:
instance IsStableUnderRetracts.epimorphisms
  signature: : (epimorphisms C).IsStableUnderRetracts where
  body: ⟨fun α β w => by
    rw [← cancel_epi h.r.right]; rw [← cancel_epi g]; rw [← Category.assoc]; rw [← Category.assoc]; rw [← h.r_w]; rw [Category.assoc]; rw [Category.assoc]; rw [w]⟩

中文:
实例 IsStableUnderRetracts.epimorphisms
  签名: : (epimorphisms C).IsStableUnderRetracts where
  定义体: ⟨fun α β w => by
    rw [← cancel_epi h.r.right]; rw [← cancel_epi g]; rw [← Category.assoc]; rw [← Category.assoc]; rw [← h.r_w]; rw [Category.assoc]; rw [Category.assoc]; rw [w]⟩

Depends on / 依赖: Category, Category.assoc, cancel_epi, h.r.right, h.r_w
-/
instance IsStableUnderRetracts.epimorphisms : (epimorphisms C).IsStableUnderRetracts where
  of_retract {_ _ _ _ f g} h (hg : Epi g) := ⟨fun α β w => by
    rw [← cancel_epi h.r.right]; rw [← cancel_epi g]; rw [← Category.assoc]; rw [← Category.assoc]; rw [← h.r_w]; rw [Category.assoc]; rw [Category.assoc]; rw [w]⟩

set_option backward.isDefEq.respectTransparency false in
/--
Instance `IsStableUnderRetracts.isomorphisms` / 实例 `IsStableUnderRetracts.isomorphisms`

English:
instance IsStableUnderRetracts.isomorphisms
  signature: : (isomorphisms C).IsStableUnderRetracts where
  body: by
    refine ⟨h.i.right ≫ inv g ≫ h.r.left, ?_, ?_⟩
    · rw [← h.i_w_assoc, IsIso.hom_inv_id_assoc, h.retract_left]
    · rw [Category.assoc, Category.assoc, h.r_w, IsIso.inv_hom_id_assoc, h.retract_right]

中文:
实例 IsStableUnderRetracts.isomorphisms
  签名: : (isomorphisms C).IsStableUnderRetracts where
  定义体: by
    refine ⟨h.i.right ≫ inv g ≫ h.r.left, ?_, ?_⟩
    · rw [← h.i_w_assoc, IsIso.hom_inv_id_assoc, h.retract_left]
    · rw [Category.assoc, Category.assoc, h.r_w, IsIso.inv_hom_id_assoc, h.retract_right]

Depends on / 依赖: Category, Category.assoc, IsIso.hom_inv_id_assoc, IsIso.inv_hom_id_assoc, h.i.right, h.i_w_assoc, h.r.left, h.r_w, h.retract_left, h.retract_right, hom_inv_id_assoc, i_w_assoc, inv_hom_id_assoc, retract_left, retract_right
-/
instance IsStableUnderRetracts.isomorphisms : (isomorphisms C).IsStableUnderRetracts where
  of_retract {X Y Z W f g} h (_ : IsIso _) := by
    refine ⟨h.i.right ≫ inv g ≫ h.r.left, ?_, ?_⟩
    · rw [← h.i_w_assoc, IsIso.hom_inv_id_assoc, h.retract_left]
    · rw [Category.assoc, Category.assoc, h.r_w, IsIso.inv_hom_id_assoc, h.retract_right]

instance (P : MorphismProperty C) [P.IsStableUnderRetracts] :
    P.op.IsStableUnderRetracts where
  of_retract h₁ h₂ := P.of_retract h₁.unop h₂

instance (P : MorphismProperty Cᵒᵖ) [P.IsStableUnderRetracts] :
    P.unop.IsStableUnderRetracts where
  of_retract h₁ h₂ := P.of_retract h₁.op h₂

instance (P₁ P₂ : MorphismProperty C)
    [P₁.IsStableUnderRetracts] [P₂.IsStableUnderRetracts] :
    (P₁ ⊓ P₂).IsStableUnderRetracts where
  of_retract := fun h ⟨h₁, h₂⟩ => ⟨of_retract h h₁, of_retract h h₂⟩

/--
Definition of `retracts` / `retracts` 的定义

English:
definition retracts
  signature: (P : MorphismProperty C)
  body: fun _ _ f => exists (Z W : C) (g : Z ⟶ W) (_ : RetractArrow f g), P g

中文:
定义 retracts
  签名: (P : Morphism命题erty C)
  定义体: fun _ _ f => exists (Z W : C) (g : Z ⟶ W) (_ : RetractArrow f g), P g

Depends on / 依赖: RetractArrow
-/
def retracts (P : MorphismProperty C) : MorphismProperty C :=
  fun _ _ f => exists (Z W : C) (g : Z ⟶ W) (_ : RetractArrow f g), P g

/--
lemma `le_retracts` / 引理 `le_retracts`

English:
lemma le_retracts
  given: (P : MorphismProperty C)
  statement: P <= P.retracts
  proof: by
  intro X Y f hf
  exact ⟨_, _, f, { i := 𝟙 _, r := 𝟙 _}, hf⟩

中文:
引理 le_retracts
  条件: (P : Morphism命题erty C)
  结论: P <= P.retracts
  证明: by
  intro X Y f hf
  exact ⟨_, _, f, { i := 𝟙 _, r := 𝟙 _}, hf⟩
-/
lemma le_retracts (P : MorphismProperty C) : P <= P.retracts := by
  intro X Y f hf
  exact ⟨_, _, f, { i := 𝟙 _, r := 𝟙 _}, hf⟩

/--
lemma `retracts_monotone` / 引理 `retracts_monotone`

English:
lemma retracts_monotone
  statement: Monotone (retracts (C := C))
  proof: by
  intro _ _ h _ _ _ ⟨_, _, _, hg, hg'⟩
  exact ⟨_, _, _, hg, h _ hg'⟩

中文:
引理 retracts_monotone
  结论: Monotone (retracts (C := C))
  证明: by
  intro _ _ h _ _ _ ⟨_, _, _, hg, hg'⟩
  exact ⟨_, _, _, hg, h _ hg'⟩
-/
lemma retracts_monotone : Monotone (retracts (C := C)) := by
  intro _ _ h _ _ _ ⟨_, _, _, hg, hg'⟩
  exact ⟨_, _, _, hg, h _ hg'⟩

/--
lemma `isStableUnderRetracts_iff_retracts_le` / 引理 `isStableUnderRetracts_iff_retracts_le`

English:
lemma isStableUnderRetracts_iff_retracts_le
  given: (P : MorphismProperty C)
  proof: by
  rw [isStableUnderRetracts_iff]
  constructor
  · intro h₁ X Y f ⟨_, _, _, h₂, h₃⟩
    exact h₁ h₂ h₃
  · intro h₁ _ _ _ _ _ _ h₂ h₃
    exact h₁ _ ⟨_, _, _, h₂, h₃⟩

中文:
引理 isStableUnderRetracts_iff_retracts_le
  条件: (P : Morphism命题erty C)
  证明: by
  rw [isStableUnderRetracts_iff]
  constructor
  · intro h₁ X Y f ⟨_, _, _, h₂, h₃⟩
    exact h₁ h₂ h₃
  · intro h₁ _ _ _ _ _ _ h₂ h₃
    exact h₁ _ ⟨_, _, _, h₂, h₃⟩

Depends on / 依赖: isLE_of_iso, isStableUnderRetracts_iff, le_iff_isLE, t.isLE_of_iso
-/
lemma isStableUnderRetracts_iff_retracts_le (P : MorphismProperty C) :
    P.IsStableUnderRetracts ↔ P.retracts <= P := by
  rw [isStableUnderRetracts_iff]
  constructor
  · intro h₁ X Y f ⟨_, _, _, h₂, h₃⟩
    exact h₁ h₂ h₃
  · intro h₁ _ _ _ _ _ _ h₂ h₃
    exact h₁ _ ⟨_, _, _, h₂, h₃⟩

/--
lemma `retracts_le` / 引理 `retracts_le`

English:
lemma retracts_le
  given: (P : MorphismProperty C) [P.IsStableUnderRetracts]
  proof: by
  rwa [← isStableUnderRetracts_iff_retracts_le]

@[simp]

中文:
引理 retracts_le
  条件: (P : Morphism命题erty C) [P.IsStableUnderRetracts]
  证明: by
  rwa [← isStableUnderRetracts_iff_retracts_le]

@[simp]

Depends on / 依赖: ge_iff_isGE, isGE_of_iso, isStableUnderRetracts_iff_retracts_le, t.isGE_of_iso
-/
lemma retracts_le (P : MorphismProperty C) [P.IsStableUnderRetracts] :
    P.retracts <= P := by
  rwa [← isStableUnderRetracts_iff_retracts_le]

@[simp]
/--
lemma `retracts_le_iff` / 引理 `retracts_le_iff`

English:
lemma retracts_le_iff
  given: {P Q : MorphismProperty C} [Q.IsStableUnderRetracts]
  proof: by
  constructor
  · exact le_trans P.le_retracts
  · intro h
    exact le_trans (retracts_monotone h) Q.retracts_le

中文:
引理 retracts_le_iff
  条件: {P Q : Morphism命题erty C} [Q.IsStableUnderRetracts]
  证明: by
  constructor
  · exact le_trans P.le_retracts
  · intro h
    exact le_trans (retracts_monotone h) Q.retracts_le

Depends on / 依赖: P.le_retracts, Q.retracts_le, le_retracts, le_trans, retracts_le, retracts_monotone
-/
lemma retracts_le_iff {P Q : MorphismProperty C} [Q.IsStableUnderRetracts] :
    P.retracts <= Q ↔ P <= Q := by
  constructor
  · exact le_trans P.le_retracts
  · intro h
    exact le_trans (retracts_monotone h) Q.retracts_le

instance {P : MorphismProperty C} [P.IsStableUnderRetracts] :
    P.RespectsIso :=
  RespectsIso.of_respects_arrow_iso _
    (fun _ _ e => of_retract (Retract.ofIso e.symm))

end MorphismProperty

end CategoryTheory
