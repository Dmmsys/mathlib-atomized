/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Basic

/-!
# Constructor for derivability structures

In this file, we provide a constructor for right and left derivability structures.
Assume that `W₁` and `W₂` are classes of morphisms in categories `C₁` and `C₂`,
and that we have a localizer morphism `Φ : LocalizerMorphism W₁ W₂` that is
a localized equivalence, i.e. `Φ.functor` induces an equivalence of categories
between the localized categories. Assume moreover that `W₂` contains identities.
Then, `Φ` is a right derivability structure
(`LocalizerMorphism.IsRightDerivabilityStructure.mk'`) if it satisfies the
two following conditions:
* for any `X₂ : C₂`, the category `Φ.RightResolution X₂` of resolutions of `X₂` is connected
* any arrow in `C₂` admits a resolution (i.e. `Φ.arrow.HasRightResolutions` holds, where
  `Φ.arrow` is the induced localizer morphism on categories of arrows in `C₁` and `C₂`)

(The dual statement for left derivability structures is also obtained.)

This statement is essentially Lemme 6.5 in
[the paper by Kahn and Maltsiniotis][KahnMaltsiniotis2008].

## References

* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]

-/

@[expose] public section

namespace CategoryTheory

open Category Localization

variable {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism
namespace IsRightDerivabilityStructure

section

variable (Φ : LocalizerMorphism W₁ W₂)
  [forall X₂, IsConnected (Φ.RightResolution X₂)]
  [Φ.arrow.HasRightResolutions] [W₂.ContainsIdentities]

namespace Constructor

variable {D : Type*} [Category* D] (L : C₂ ⥤ D) [L.IsLocalization W₂]
  {X₂ : C₂} {X₃ : D} (y : L.obj X₂ ⟶ X₃)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given `Φ : LocalizerMorphism W₁ W₂`, `L : C₂ ⥤ D` a localization functor for `W₂` and
a morphism `y : L.obj X₂ ⟶ X₃`, this is the functor which sends `R : Φ.RightResolution d` to
`(isoOfHom L W₂ R.w R.hw).inv ≫ y` in the category `w.CostructuredArrowDownwards y`
where `w` is `TwoSquare.mk Φ.functor (Φ.functor ⋙ L) L (𝟭 _) (Functor.rightUnitor _).inv`. -/
@[simps]
/--
Definition of `fromRightResolution` / `fromRightResolution` 的定义

English:
definition fromRightResolution
  signature: :
  body: CostructuredArrow.mk (Y := StructuredArrow.mk R.w)
    (StructuredArrow.homMk ((isoOfHom L W₂ R.w R.hw).inv ≫ y))
  map {R R'} φ := CostructuredArrow.homMk (StructuredArrow.homMk φ.f) (by
    ext
    dsimp
    rw [← assoc]; rw [← cancel_epi (isoOfHom L W₂ R.w R.hw).hom]; rw [isoOfHom_hom]; rw [isoOfHom_hom_inv_id_assoc]; rw [assoc]; rw [← L.map_comp_assoc]; rw [φ.comm]; rw [isoOfHom_hom_inv_id_assoc])

中文:
定义 fromRightResolution
  签名: :
  定义体: CostructuredArrow.mk (Y := StructuredArrow.mk R.w)
    (StructuredArrow.homMk ((isoOfHom L W₂ R.w R.hw).inv ≫ y))
  map {R R'} φ := CostructuredArrow.homMk (StructuredArrow.homMk φ.f) (by
    ext
    dsimp
    rw [← assoc]; rw [← cancel_epi (isoOfHom L W₂ R.w R.hw).hom]; rw [isoOfHom_hom]; rw [isoOfHom_hom_inv_id_assoc]; rw [assoc]; rw [← L.map_comp_assoc]; rw [φ.comm]; rw [isoOfHom_hom_inv_id_assoc])

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk, StructuredArrow, StructuredArrow.mk
-/
noncomputable def fromRightResolution :
    Φ.RightResolution X₂ ⥤ (TwoSquare.mk Φ.functor (Φ.functor ⋙ L) L (𝟭 _)
      (Functor.rightUnitor _).inv).CostructuredArrowDownwards y where
  obj R := CostructuredArrow.mk (Y := StructuredArrow.mk R.w)
    (StructuredArrow.homMk ((isoOfHom L W₂ R.w R.hw).inv ≫ y))
  map {R R'} φ := CostructuredArrow.homMk (StructuredArrow.homMk φ.f) (by
    ext
    dsimp
    rw [← assoc]; rw [← cancel_epi (isoOfHom L W₂ R.w R.hw).hom]; rw [isoOfHom_hom]; rw [isoOfHom_hom_inv_id_assoc]; rw [assoc]; rw [← L.map_comp_assoc]; rw [φ.comm]; rw [isoOfHom_hom_inv_id_assoc])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `isConnected` / 引理 `isConnected`

English:
lemma isConnected
  proof: by
  let w := (TwoSquare.mk Φ.functor (Φ.functor ⋙ L) L (𝟭 _) (Functor.rightUnitor _).inv)
  have : Nonempty (w.CostructuredArrowDownwards y) :=
    ⟨(fromRightResolution Φ L y).obj (Classical.arbitrary _)⟩
  suffices forall (X : w.CostructuredArrowDownwards y),
      exists Y, Zigzag X ((fromRightResolution Φ L y).obj Y) by
    refine zigzag_isConnected (fun X X' => ?_)
    obtain ⟨Y, hX⟩ := this X
    obtain ⟨Y', hX'⟩ := this X'
    exact hX.trans ((zigzag_obj_of_zigzag _ (isPreconnected_zigzag Y Y')).trans hX'.symm)
  intro X
  obtain ⟨c, g, x, fac, rfl⟩ := TwoSquare.CostructuredArrowDownwards.mk_surjective X
  dsimp [w] at x fac
  rw [id_comp] at fac
  let ρ : Φ.arrow.RightResolution (Arrow.mk g) := Classical.arbitrary _
  refine ⟨RightResolution.mk ρ.w.left ρ.hw.1, ?_⟩
  have := zigzag_obj_of_zigzag
    (fromRightResolution Φ L x ⋙ w.costructuredArrowDownwardsPrecomp x y g fac)
      (isPreconnected_zigzag (RightResolution.mk (𝟙 _) (W₂.id_mem _))
        (RightResolution.mk ρ.w.right ρ.hw.2))
  refine Zigzag.trans ?_ (Zigzag.trans this ?_)
  · exact Zigzag.of_hom (eqToHom (by simp))
  · apply Zigzag.of_inv
    refine CostructuredArrow.homMk (StructuredArrow.homMk ρ.X₁.hom (by simp)) ?_
    ext
    simp [← cancel_epi (isoOfHom L W₂ ρ.w.left ρ.hw.1).hom, ← L.map_comp_assoc, fac]

中文:
引理 isConnected
  证明: by
  let w := (TwoSquare.mk Φ.functor (Φ.functor ⋙ L) L (𝟭 _) (Functor.rightUnitor _).inv)
  have : Nonempty (w.CostructuredArrowDownwards y) :=
    ⟨(fromRightResolution Φ L y).obj (Classical.arbitrary _)⟩
  suffices forall (X : w.CostructuredArrowDownwards y),
      exists Y, Zigzag X ((fromRightResolution Φ L y).obj Y) by
    refine zigzag_isConnected (fun X X' => ?_)
    obtain ⟨Y, hX⟩ := this X
    obtain ⟨Y', hX'⟩ := this X'
    exact hX.trans ((zigzag_obj_of_zigzag _ (isPreconnected_zigzag Y Y')).trans hX'.symm)
  intro X
  obtain ⟨c, g, x, fac, rfl⟩ := TwoSquare.CostructuredArrowDownwards.mk_surjective X
  dsimp [w] at x fac
  rw [id_comp] at fac
  let ρ : Φ.arrow.RightResolution (Arrow.mk g) := Classical.arbitrary _
  refine ⟨RightResolution.mk ρ.w.left ρ.hw.1, ?_⟩
  have := zigzag_obj_of_zigzag
    (fromRightResolution Φ L x ⋙ w.costructuredArrowDownwardsPrecomp x y g fac)
      (isPreconnected_zigzag (RightResolution.mk (𝟙 _) (W₂.id_mem _))
        (RightResolution.mk ρ.w.right ρ.hw.2))
  refine Zigzag.trans ?_ (Zigzag.trans this ?_)
  · exact Zigzag.of_hom (eqToHom (by simp))
  · apply Zigzag.of_inv
    refine CostructuredArrow.homMk (StructuredArrow.homMk ρ.X₁.hom (by simp)) ?_
    ext
    simp [← cancel_epi (isoOfHom L W₂ ρ.w.left ρ.hw.1).hom, ← L.map_comp_assoc, fac]

Depends on / 依赖: Classical, Classical.arbitrary, CostructuredArrowDownwards, Functor, Functor.rightUnitor, Nonempty, TwoSquare, TwoSquare.mk, Zigzag, arbitrary, fromRightResolution, functor, hX.trans, isPreconnected_zigzag, rightUnitor, w.CostructuredArrowDownwards, zigzag_isConnected, zigzag_obj_of_zigzag
-/
lemma isConnected :
    IsConnected ((TwoSquare.mk Φ.functor (Φ.functor ⋙ L) L (𝟭 _)
      (Functor.rightUnitor _).inv).CostructuredArrowDownwards y) := by
  let w := (TwoSquare.mk Φ.functor (Φ.functor ⋙ L) L (𝟭 _) (Functor.rightUnitor _).inv)
  have : Nonempty (w.CostructuredArrowDownwards y) :=
    ⟨(fromRightResolution Φ L y).obj (Classical.arbitrary _)⟩
  suffices forall (X : w.CostructuredArrowDownwards y),
      exists Y, Zigzag X ((fromRightResolution Φ L y).obj Y) by
    refine zigzag_isConnected (fun X X' => ?_)
    obtain ⟨Y, hX⟩ := this X
    obtain ⟨Y', hX'⟩ := this X'
    exact hX.trans ((zigzag_obj_of_zigzag _ (isPreconnected_zigzag Y Y')).trans hX'.symm)
  intro X
  obtain ⟨c, g, x, fac, rfl⟩ := TwoSquare.CostructuredArrowDownwards.mk_surjective X
  dsimp [w] at x fac
  rw [id_comp] at fac
  let ρ : Φ.arrow.RightResolution (Arrow.mk g) := Classical.arbitrary _
  refine ⟨RightResolution.mk ρ.w.left ρ.hw.1, ?_⟩
  have := zigzag_obj_of_zigzag
    (fromRightResolution Φ L x ⋙ w.costructuredArrowDownwardsPrecomp x y g fac)
      (isPreconnected_zigzag (RightResolution.mk (𝟙 _) (W₂.id_mem _))
        (RightResolution.mk ρ.w.right ρ.hw.2))
  refine Zigzag.trans ?_ (Zigzag.trans this ?_)
  · exact Zigzag.of_hom (eqToHom (by simp))
  · apply Zigzag.of_inv
    refine CostructuredArrow.homMk (StructuredArrow.homMk ρ.X₁.hom (by simp)) ?_
    ext
    simp [← cancel_epi (isoOfHom L W₂ ρ.w.left ρ.hw.1).hom, ← L.map_comp_assoc, fac]

end Constructor

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mk'` / 引理 `mk'`

English:
lemma mk'
  given: [Φ.IsLocalizedEquivalence]
  statement: Φ.IsRightDerivabilityStructure
  proof: by
  rw [Φ.isRightDerivabilityStructure_iff (Φ.functor ⋙ W₂.Q) W₂.Q (𝟭 _)
    (Functor.rightUnitor _).symm]; rw [TwoSquare.guitartExact_iff_isConnected_downwards]
  apply Constructor.isConnected

中文:
引理 mk'
  条件: [Φ.是LocalizedEquivalence]
  结论: Φ.是RightDerivabilityStructure
  证明: by
  rw [Φ.isRightDerivabilityStructure_iff (Φ.functor ⋙ W₂.Q) W₂.Q (𝟭 _)
    (Functor.rightUnitor _).symm]; rw [TwoSquare.guitartExact_iff_isConnected_downwards]
  apply Constructor.isConnected

Depends on / 依赖: Constructor, Constructor.isConnected, Functor, Functor.rightUnitor, TwoSquare, TwoSquare.guitartExact_iff_isConnected_downwards, functor, guitartExact_iff_isConnected_downwards, isConnected, isRightDerivabilityStructure_iff, rightUnitor
-/
lemma mk' [Φ.IsLocalizedEquivalence] : Φ.IsRightDerivabilityStructure := by
  rw [Φ.isRightDerivabilityStructure_iff (Φ.functor ⋙ W₂.Q) W₂.Q (𝟭 _)
    (Functor.rightUnitor _).symm]; rw [TwoSquare.guitartExact_iff_isConnected_downwards]
  apply Constructor.isConnected

end

end IsRightDerivabilityStructure

/--
lemma `IsLeftDerivabilityStructure.mk'` / 引理 `IsLeftDerivabilityStructure.mk'`

English:
lemma IsLeftDerivabilityStructure.mk'
  statement: (Φ : LocalizerMorphism W₁ W₂)
  proof: by
  rw [isLeftDerivabilityStructure_iff_op]
  have : Φ.op.arrow.HasRightResolutions := fun f => by
    let R : Φ.arrow.LeftResolution (Arrow.mk f.hom.unop) := Classical.arbitrary _
    exact ⟨{
      X₁ := Arrow.mk R.X₁.hom.op
      w := Arrow.homMk R.w.right.op R.w.left.op (Quiver.Hom.unop_inj R.w.w.symm)
      hw := ⟨R.hw.right, R.hw.left⟩ }⟩
  have (X₂ : C₂ᵒᵖ) : IsConnected (Φ.op.RightResolution X₂) :=
    isConnected_of_equivalent (LeftResolution.opEquivalence Φ X₂.unop)
  exact IsRightDerivabilityStructure.mk' _

中文:
引理 是LeftDerivabilityStructure.mk'
  结论: (Φ : Localizer态射 W₁ W₂)
  证明: by
  rw [isLeftDerivabilityStructure_iff_op]
  have : Φ.op.arrow.HasRightResolutions := fun f => by
    let R : Φ.arrow.LeftResolution (Arrow.mk f.hom.unop) := Classical.arbitrary _
    exact ⟨{
      X₁ := Arrow.mk R.X₁.hom.op
      w := Arrow.homMk R.w.right.op R.w.left.op (Quiver.Hom.unop_inj R.w.w.symm)
      hw := ⟨R.hw.right, R.hw.left⟩ }⟩
  have (X₂ : C₂ᵒᵖ) : IsConnected (Φ.op.RightResolution X₂) :=
    isConnected_of_equivalent (LeftResolution.opEquivalence Φ X₂.unop)
  exact IsRightDerivabilityStructure.mk' _

Depends on / 依赖: Arrow.homMk, Arrow.mk, Classical, Classical.arbitrary, HasRightResolutions, IsConnected, IsRightDerivabilityStructure, IsRightDerivabilityStructure.mk, LeftResolution, LeftResolution.opEquivalence, Quiver, Quiver.Hom.unop_inj, R.hw.left, R.hw.right, R.w.left.op, R.w.right.op, R.w.w.symm, RightResolution, arbitrary, arrow.LeftResolution
-/
lemma IsLeftDerivabilityStructure.mk' (Φ : LocalizerMorphism W₁ W₂)
    [forall X₂, IsConnected (Φ.LeftResolution X₂)]
    [Φ.arrow.HasLeftResolutions] [W₂.ContainsIdentities]
    [Φ.IsLocalizedEquivalence] :
    Φ.IsLeftDerivabilityStructure := by
  rw [isLeftDerivabilityStructure_iff_op]
  have : Φ.op.arrow.HasRightResolutions := fun f => by
    let R : Φ.arrow.LeftResolution (Arrow.mk f.hom.unop) := Classical.arbitrary _
    exact ⟨{
      X₁ := Arrow.mk R.X₁.hom.op
      w := Arrow.homMk R.w.right.op R.w.left.op (Quiver.Hom.unop_inj R.w.w.symm)
      hw := ⟨R.hw.right, R.hw.left⟩ }⟩
  have (X₂ : C₂ᵒᵖ) : IsConnected (Φ.op.RightResolution X₂) :=
    isConnected_of_equivalent (LeftResolution.opEquivalence Φ X₂.unop)
  exact IsRightDerivabilityStructure.mk' _

end LocalizerMorphism

end CategoryTheory
