/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

/-!
# Induced t-structures

Let `t` be a t-structure on a pretriangulated category `C`.
If `P` is a triangulated subcategory of `C`, we introduce a typeclass
`P.HasInducedTStructure t` which essentially says that up to isomorphisms
`P` is stable by the application of the truncation functors.

In particular, we show that the triangulated subcategory `t.plus`
of `t`-bounded above objects can be endowed with a t-structure `t.onPlus`,
and the same applies to `t.minus` and `t.bounded`.

-/

@[expose] public section

namespace CategoryTheory

open Limits Pretriangulated Triangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C Int]
  [forall (n : Int), (shiftFunctor C n).Additive] [Pretriangulated C]
  (P : ObjectProperty C) (t : TStructure C)

namespace ObjectProperty

/-- The property that a full subcategory of a pretriangulated category
equipped with a t-structure can be endowed with an induced t-structure. -/
@[mk_iff]
/--
Definition of `HasInducedTStructure` / `HasInducedTStructure` 的定义

English:
class HasInducedTStructure
  parameters: [P.IsTriangulated]
  axioms and operations (1):
    - exists_triangle_zero_one((A : C) (hA : P A)) : exists (X Y : C) (_ : t.IsLE X 0) (_ : t.IsGE Y 1) (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : Int)⟧) (_ : Triangle.mk f g h in distTriang C), P.isoClosure X ∧ P.isoClosure Y

中文:
类 HasInducedTStructure
  参数: [P.IsTriangulated]
  公理与运算 (1 个):
    - exists_triangle_zero_one((A : C) (hA : P A)) : 存在 (X Y : C) (_ : t.IsLE X 0) (_ : t.IsGE Y 1) (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : 整数)⟧) (_ : Triangle.mk f g h in distTriang C), P.isoClosure X ∧ P.isoClosure Y
-/
class HasInducedTStructure [P.IsTriangulated] : Prop where
  exists_triangle_zero_one (A : C) (hA : P A) :
    exists (X Y : C) (_ : t.IsLE X 0) (_ : t.IsGE Y 1)
      (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : Int)⟧) (_ : Triangle.mk f g h in distTriang C),
    P.isoClosure X ∧ P.isoClosure Y

variable [P.IsTriangulated] [h : P.HasInducedTStructure t]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `tStructure` / `tStructure` 的定义

English:
definition tStructure
  signature: : TStructure P.FullSubcategory where
  body: t.le n X.obj
  ge n X := t.ge n X.obj
  le_isClosedUnderIsomorphisms n := ⟨fun {X Y} e hX => (t.le n).prop_of_iso (P.ι.mapIso e) hX⟩
  ge_isClosedUnderIsomorphisms n := ⟨fun {X Y} e hX => (t.ge n).prop_of_iso (P.ι.mapIso e) hX⟩
  le_shift n a n' h X hX := (t.le n').prop_of_iso ((P.ι.commShiftIso a).

中文:
定义 tStructure
  签名: : TStructure P.FullSubcategory where
  定义体: t.le n X.obj
  ge n X := t.ge n X.obj
  le_isClosedUnderIsomorphisms n := ⟨fun {X Y} e hX => (t.le n).prop_of_iso (P.ι.mapIso e) hX⟩
  ge_isClosedUnderIsomorphisms n := ⟨fun {X Y} e hX => (t.ge n).prop_of_iso (P.ι.mapIso e) hX⟩
  le_shift n a n' h X hX := (t.le n').prop_of_iso ((P.ι.commShiftIso a).

Depends on / 依赖: X.obj, t.le
-/
noncomputable def tStructure : TStructure P.FullSubcategory where
  le n X := t.le n X.obj
  ge n X := t.ge n X.obj
  le_isClosedUnderIsomorphisms n := ⟨fun {X Y} e hX => (t.le n).prop_of_iso (P.ι.mapIso e) hX⟩
  ge_isClosedUnderIsomorphisms n := ⟨fun {X Y} e hX => (t.ge n).prop_of_iso (P.ι.mapIso e) hX⟩
  le_shift n a n' h X hX := (t.le n').prop_of_iso ((P.ι.commShiftIso a).symm.app X)
      (t.le_shift n a n' h X.obj hX)
  ge_shift n a n' h X hX := (t.ge n').prop_of_iso ((P.ι.commShiftIso a).symm.app X)
    (t.ge_shift n a n' h X.obj hX)
  zero' {X Y} f hX hY := P.ι.map_injective (by
    rw [Functor.map_zero]
    exact t.zero' (P.ι.map f) hX hY)
  le_zero_le X hX := t.le_zero_le _ hX
  ge_one_le X hX := t.ge_one_le _ hX
  exists_triangle_zero_one A := by
    obtain ⟨X, Y, hX, hY, f, g, h, hT, ⟨X', hX', ⟨e⟩⟩, ⟨Y', hY', ⟨e'⟩⟩⟩ :=
      h.exists_triangle_zero_one A.1 A.2
    exact ⟨⟨X', hX'⟩, ⟨Y', hY'⟩, (t.le 0).prop_of_iso e hX.le,
      (t.ge 1).prop_of_iso e' hY.ge,
      P.fullyFaithfulι.preimage (e.inv ≫ f),
      P.fullyFaithfulι.preimage (g ≫ e'.hom),
      P.fullyFaithfulι.preimage (e'.inv ≫ h ≫ e.hom⟦(1 : Int)⟧' ≫
          (P.ι.commShiftIso (1 : Int)).inv.app ⟨X', hX'⟩),
      isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ e.symm (Iso.refl _) e'.symm)⟩

/--
lemma `tStructure_isLE_iff` / 引理 `tStructure_isLE_iff`

English:
lemma tStructure_isLE_iff
  given: (X : P.FullSubcategory) (n : Int)
  proof: ⟨fun h => ⟨h.1⟩, fun h => ⟨h.1⟩⟩

中文:
引理 tStructure_isLE_iff
  条件: (X : P.FullSubcategory) (n : 整数)
  证明: ⟨fun h => ⟨h.1⟩, fun h => ⟨h.1⟩⟩
-/
lemma tStructure_isLE_iff (X : P.FullSubcategory) (n : Int) :
    (P.tStructure t).IsLE X n ↔ t.IsLE X.obj n :=
  ⟨fun h => ⟨h.1⟩, fun h => ⟨h.1⟩⟩

/--
lemma `tStructure_isGE_iff` / 引理 `tStructure_isGE_iff`

English:
lemma tStructure_isGE_iff
  given: (X : P.FullSubcategory) (n : Int)
  proof: ⟨fun h => ⟨h.1⟩, fun h => ⟨h.1⟩⟩

中文:
引理 tStructure_isGE_iff
  条件: (X : P.FullSubcategory) (n : 整数)
  证明: ⟨fun h => ⟨h.1⟩, fun h => ⟨h.1⟩⟩
-/
lemma tStructure_isGE_iff (X : P.FullSubcategory) (n : Int) :
    (P.tStructure t).IsGE X n ↔ t.IsGE X.obj n :=
  ⟨fun h => ⟨h.1⟩, fun h => ⟨h.1⟩⟩

/--
lemma `HasInducedTStructure.mk'` / 引理 `HasInducedTStructure.mk'`

English:
lemma HasInducedTStructure.mk'
  statement: {P : ObjectProperty C} [P.IsTriangulated] {t : TStructure C}
  proof: ⟨_, _, inferInstance, inferInstance, _, _, _,
      t.triangleLEGE_distinguished 0 1 (by lia) X,
        P.le_isoClosure _ ((h X hX _).1), P.le_isoClosure _ ((h X hX _).2)⟩

中文:
引理 HasInducedTStructure.mk'
  结论: {P : Object命题erty C} [P.IsTriangulated] {t : TStructure C}
  证明: ⟨_, _, inferInstance, inferInstance, _, _, _,
      t.triangleLEGE_distinguished 0 1 (by lia) X,
        P.le_isoClosure _ ((h X hX _).1), P.le_isoClosure _ ((h X hX _).2)⟩

Depends on / 依赖: P.le_isoClosure, le_isoClosure, t.triangleLEGE_distinguished, triangleLEGE_distinguished
-/
lemma HasInducedTStructure.mk' {P : ObjectProperty C} [P.IsTriangulated] {t : TStructure C}
    (h : forall (X : C) (_ : P X) (n : Int), P ((t.truncLE n).obj X) ∧ P ((t.truncGE n).obj X)) :
    P.HasInducedTStructure t where
  exists_triangle_zero_one X hX :=
    ⟨_, _, inferInstance, inferInstance, _, _, _,
      t.triangleLEGE_distinguished 0 1 (by lia) X,
        P.le_isoClosure _ ((h X hX _).1), P.le_isoClosure _ ((h X hX _).2)⟩

set_option backward.defeqAttrib.useBackward true in
/--
lemma `mem_of_hasInductedTStructure` / 引理 `mem_of_hasInductedTStructure`

English:
lemma mem_of_hasInductedTStructure
  statement: (P : ObjectProperty C) [P.IsTriangulated] (t : TStructure C)
  proof: by
  obtain ⟨e, _⟩ := t.triangle_iso_exists hT
    (P.ι.map_distinguished _ ((P.tStructure t).triangleLEGE_distinguished n₀ n₁ h ⟨_, h₂⟩))
    (Iso.refl _) n₀ n₁ inferInstance inferInstance
      (by dsimp; rw [← P.tStructure_isLE_iff]; infer_instance)
      (by dsimp; rw [← P.tStructure_isGE_iff]; 

中文:
引理 mem_of_hasInductedTStructure
  结论: (P : Object命题erty C) [P.IsTriangulated] (t : TStructure C)
  证明: by
  obtain ⟨e, _⟩ := t.triangle_iso_exists hT
    (P.ι.map_distinguished _ ((P.tStructure t).triangleLEGE_distinguished n₀ n₁ h ⟨_, h₂⟩))
    (Iso.refl _) n₀ n₁ inferInstance inferInstance
      (by dsimp; rw [← P.tStructure_isLE_iff]; infer_instance)
      (by dsimp; rw [← P.tStructure_isGE_iff]; 

Depends on / 依赖: Iso.refl, P.prop_, P.prop_iff_of_iso, P.tStructure, P.tStructure_isGE_iff, P.tStructure_isLE_iff, Triangle, infer_instance, mapIso, map_distinguished, prop_iff_of_iso, t.triangle_iso_exists, tStructure, tStructure_isGE_iff, tStructure_isLE_iff, triangleLEGE_distinguished, triangle_iso_exists
-/
lemma mem_of_hasInductedTStructure (P : ObjectProperty C) [P.IsTriangulated] (t : TStructure C)
    [P.IsClosedUnderIsomorphisms] [P.HasInducedTStructure t]
    (T : Triangle C) (hT : T in distTriang C)
    (n₀ n₁ : Int) (h : n₀ + 1 = n₁) (h₁ : t.IsLE T.obj₁ n₀) (h₂ : P T.obj₂)
    (h₃ : t.IsGE T.obj₃ n₁) :
    P T.obj₁ ∧ P T.obj₃ := by
  obtain ⟨e, _⟩ := t.triangle_iso_exists hT
    (P.ι.map_distinguished _ ((P.tStructure t).triangleLEGE_distinguished n₀ n₁ h ⟨_, h₂⟩))
    (Iso.refl _) n₀ n₁ inferInstance inferInstance
      (by dsimp; rw [← P.tStructure_isLE_iff]; infer_instance)
      (by dsimp; rw [← P.tStructure_isGE_iff]; infer_instance)
  exact ⟨(P.prop_iff_of_iso (Triangle.π₁.mapIso e)).2 (P.prop_ι_obj _),
    (P.prop_iff_of_iso (Triangle.π₃.mapIso e)).2 (P.prop_ι_obj _)⟩

set_option backward.defeqAttrib.useBackward true in
instance (P P' : ObjectProperty C) [P.IsTriangulated] [P'.IsTriangulated] (t : TStructure C)
    [P.HasInducedTStructure t] [P'.HasInducedTStructure t]
    [P.IsClosedUnderIsomorphisms] [P'.IsClosedUnderIsomorphisms] :
    (P ⊓ P').HasInducedTStructure t :=
  .mk' (by
    rintro X ⟨hX, hX'⟩ n
    exact
      ⟨⟨(P.mem_of_hasInductedTStructure t _ (t.triangleLEGE_distinguished n _ rfl X) n _ rfl
          (by dsimp; infer_instance) hX (by dsimp; infer_instance)).1,
        (P'.mem_of_hasInductedTStructure t _ (t.triangleLEGE_distinguished n _ rfl X) n _ rfl
          (by dsimp; infer_instance) hX' (by dsimp; infer_instance)).1⟩,
          ⟨(P.mem_of_hasInductedTStructure t _ (t.triangleLEGE_distinguished (n - 1) n (by lia) X)
          (n - 1) n (by lia) (by dsimp; infer_instance) hX (by dsimp; infer_instance)).2,
        (P'.mem_of_hasInductedTStructure t _ (t.triangleLEGE_distinguished (n - 1) n (by lia) X)
          (n - 1) n (by lia) (by dsimp; infer_instance) hX' (by dsimp; infer_instance)).2⟩⟩)

end ObjectProperty

namespace Triangulated.TStructure

variable [IsTriangulated C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: t.plus.HasInducedTStructure t
  body: .mk' (by rintro X ⟨a, _⟩ n; exact ⟨⟨a, inferInstance⟩, ⟨a, inferInstance⟩⟩)

中文:
实例 :
  签名: t.plus.HasInducedTStructure t
  定义体: .mk' (by rintro X ⟨a, _⟩ n; exact ⟨⟨a, inferInstance⟩, ⟨a, inferInstance⟩⟩)
-/
instance : t.plus.HasInducedTStructure t :=
  .mk' (by rintro X ⟨a, _⟩ n; exact ⟨⟨a, inferInstance⟩, ⟨a, inferInstance⟩⟩)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: t.minus.HasInducedTStructure t
  body: .mk' (by rintro X ⟨a, _⟩ n; exact ⟨⟨a, inferInstance⟩, ⟨a, inferInstance⟩⟩)

中文:
实例 :
  签名: t.minus.HasInducedTStructure t
  定义体: .mk' (by rintro X ⟨a, _⟩ n; exact ⟨⟨a, inferInstance⟩, ⟨a, inferInstance⟩⟩)
-/
instance : t.minus.HasInducedTStructure t :=
  .mk' (by rintro X ⟨a, _⟩ n; exact ⟨⟨a, inferInstance⟩, ⟨a, inferInstance⟩⟩)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: t.bounded.HasInducedTStructure t
  body: by
  dsimp [bounded]
  infer_instance

中文:
实例 :
  签名: t.bounded.HasInducedTStructure t
  定义体: by
  dsimp [bounded]
  infer_instance

Depends on / 依赖: bounded, infer_instance
-/
instance : t.bounded.HasInducedTStructure t := by
  dsimp [bounded]
  infer_instance

/--
Definition of `onPlus` / `onPlus` 的定义

English:
abbreviation onPlus
  signature: : TStructure t.plus.FullSubcategory
  body: t.plus.tStructure t

中文:
缩写 onPlus
  签名: : TStructure t.plus.FullSubcategory
  定义体: t.plus.tStructure t

Depends on / 依赖: t.plus.tStructure, tStructure
-/
noncomputable abbrev onPlus : TStructure t.plus.FullSubcategory := t.plus.tStructure t

/--
Definition of `onMinus` / `onMinus` 的定义

English:
abbreviation onMinus
  signature: : TStructure t.minus.FullSubcategory
  body: t.minus.tStructure t

中文:
缩写 onMinus
  签名: : TStructure t.minus.FullSubcategory
  定义体: t.minus.tStructure t

Depends on / 依赖: t.minus.tStructure, tStructure
-/
noncomputable abbrev onMinus : TStructure t.minus.FullSubcategory := t.minus.tStructure t

/--
Definition of `onBounded` / `onBounded` 的定义

English:
abbreviation onBounded
  signature: : TStructure t.bounded.FullSubcategory
  body: t.bounded.tStructure t

中文:
缩写 onBounded
  签名: : TStructure t.bounded.FullSubcategory
  定义体: t.bounded.tStructure t

Depends on / 依赖: bounded, t.bounded.tStructure, tStructure
-/
noncomputable abbrev onBounded : TStructure t.bounded.FullSubcategory := t.bounded.tStructure t

end Triangulated.TStructure

end CategoryTheory
