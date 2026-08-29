/-
Copyright (c) 2024 Andrew Yang, Qi Ge, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Qi Ge, Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.RingHom.Injective
public import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Valuative criterion

## Main results

- `AlgebraicGeometry.UniversallyClosed.eq_valuativeCriterion`:
  A morphism is universally closed if and only if
  it is quasi-compact and satisfies the existence part of the valuative criterion.
- `AlgebraicGeometry.IsSeparated.eq_valuativeCriterion`:
  A morphism is separated if and only if
  it is quasi-separated and satisfies the uniqueness part of the valuative criterion.
- `AlgebraicGeometry.IsProper.eq_valuativeCriterion`:
  A morphism is proper if and only if
  it is qcqs and of finite type and satisfies the valuative criterion.

## Future projects
Show that it suffices to check discrete valuation rings when the base is Noetherian.

-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/--
Definition of `ValuativeCommSq` / `ValuativeCommSq` 的定义

English:
structure ValuativeCommSq
  parameters: {X Y : Scheme.{u}} (f : X ⟶ Y)
  axioms and operations (11):
    - R : Type u
    - [commRing : CommRing R]
    - [domain : IsDomain R]
    - [valuationRing : ValuationRing R]
    - K : Type u
    - [field : Field K]
    - [algebra : Algebra R K]
    - [isFractionRing : IsFractionRing R K]
    - (i₁ : Spec (.of K) ⟶ X)
    - (i₂ : Spec (.of R) ⟶ Y)
    - (commSq : CommSq i₁ (Spec.map (CommRingCat.ofHom (algebraMap R K))) f i₂)

中文:
结构 ValuativeCommSq
  参数: {X Y : Scheme.{u}} (f : X ⟶ Y)
  公理与运算 (11 个):
    - R : 类型u
    - [commRing : CommRing R]
    - [domain : IsDomain R]
    - [valuationRing : ValuationRing R]
    - K : 类型u
    - [field : Field K]
    - [algebra : Algebra R K]
    - [isFractionRing : IsFractionRing R K]
    - (i₁ : Spec (.of K) ⟶ X)
    - (i₂ : Spec (.of R) ⟶ Y)
    - (commSq : CommSq i₁ (Spec.map (CommRingCat.ofHom (algebraMap R K))) f i₂)
-/
structure ValuativeCommSq {X Y : Scheme.{u}} (f : X ⟶ Y) where
  /-- The valuation ring of a valuative commutative square. -/
  R : Type u
  [commRing : CommRing R]
  [domain : IsDomain R]
  [valuationRing : ValuationRing R]
  /-- The field of fractions of a valuative commutative square. -/
  K : Type u
  [field : Field K]
  [algebra : Algebra R K]
  [isFractionRing : IsFractionRing R K]
  /-- The top map in a valuative commutative map. -/
  (i₁ : Spec (.of K) ⟶ X)
  /-- The bottom map in a valuative commutative map. -/
  (i₂ : Spec (.of R) ⟶ Y)
  (commSq : CommSq i₁ (Spec.map (CommRingCat.ofHom (algebraMap R K))) f i₂)

namespace ValuativeCommSq

attribute [instance] commRing domain valuationRing field algebra isFractionRing

end ValuativeCommSq

/--
Definition of `ValuativeCriterion.Existence` / `ValuativeCriterion.Existence` 的定义

English:
definition ValuativeCriterion.Existence
  signature: : MorphismProperty Scheme
  body: fun _ _ f => forall S : ValuativeCommSq f, S.commSq.HasLift

中文:
定义 ValuativeCriterion.Existence
  签名: : Morphism命题erty Scheme
  定义体: fun _ _ f => forall S : ValuativeCommSq f, S.commSq.HasLift

Depends on / 依赖: HasLift, S.commSq.HasLift, ValuativeCommSq, commSq
-/
def ValuativeCriterion.Existence : MorphismProperty Scheme :=
  fun _ _ f => forall S : ValuativeCommSq f, S.commSq.HasLift

/--
Definition of `ValuativeCriterion.Uniqueness` / `ValuativeCriterion.Uniqueness` 的定义

English:
definition ValuativeCriterion.Uniqueness
  signature: : MorphismProperty Scheme
  body: fun _ _ f => forall S : ValuativeCommSq f, Subsingleton S.commSq.LiftStruct

中文:
定义 ValuativeCriterion.Uniqueness
  签名: : Morphism命题erty Scheme
  定义体: fun _ _ f => forall S : ValuativeCommSq f, Subsingleton S.commSq.LiftStruct

Depends on / 依赖: LiftStruct, S.commSq.LiftStruct, Subsingleton, ValuativeCommSq, commSq
-/
def ValuativeCriterion.Uniqueness : MorphismProperty Scheme :=
  fun _ _ f => forall S : ValuativeCommSq f, Subsingleton S.commSq.LiftStruct

/--
Definition of `ValuativeCriterion` / `ValuativeCriterion` 的定义

English:
definition ValuativeCriterion
  signature: : MorphismProperty Scheme
  body: fun _ _ f => forall S : ValuativeCommSq f, Nonempty (Unique (S.commSq.LiftStruct))

中文:
定义 ValuativeCriterion
  签名: : Morphism命题erty Scheme
  定义体: fun _ _ f => forall S : ValuativeCommSq f, Nonempty (Unique (S.commSq.LiftStruct))

Depends on / 依赖: LiftStruct, Nonempty, S.commSq.LiftStruct, Unique, ValuativeCommSq, commSq
-/
def ValuativeCriterion : MorphismProperty Scheme :=
  fun _ _ f => forall S : ValuativeCommSq f, Nonempty (Unique (S.commSq.LiftStruct))

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/--
lemma `ValuativeCriterion.iff` / 引理 `ValuativeCriterion.iff`

English:
lemma ValuativeCriterion.iff
  given: {f : X ⟶ Y}
  proof: by
  change (forall _, _) ↔ (forall _, _) ∧ (forall _, _)
  simp_rw [← forall_and, unique_iff_subsingleton_and_nonempty, and_comm, CommSq.HasLift.iff]

中文:
引理 ValuativeCriterion.iff
  条件: {f : X ⟶ Y}
  证明: by
  change (forall _, _) ↔ (forall _, _) ∧ (forall _, _)
  simp_rw [← forall_and, unique_iff_subsingleton_and_nonempty, and_comm, CommSq.HasLift.iff]

Depends on / 依赖: CommSq, CommSq.HasLift.iff, HasLift, and_comm, forall_and, simp_rw, unique_iff_subsingleton_and_nonempty
-/
lemma ValuativeCriterion.iff {f : X ⟶ Y} :
    ValuativeCriterion f ↔ Existence f ∧ Uniqueness f := by
  change (forall _, _) ↔ (forall _, _) ∧ (forall _, _)
  simp_rw [← forall_and, unique_iff_subsingleton_and_nonempty, and_comm, CommSq.HasLift.iff]

/--
lemma `ValuativeCriterion.eq` / 引理 `ValuativeCriterion.eq`

English:
lemma ValuativeCriterion.eq
  proof: by
  ext X Y f
  exact iff

中文:
引理 ValuativeCriterion.eq
  证明: by
  ext X Y f
  exact iff
-/
lemma ValuativeCriterion.eq :
    ValuativeCriterion = Existence ⊓ Uniqueness := by
  ext X Y f
  exact iff

/--
lemma `ValuativeCriterion.existence` / 引理 `ValuativeCriterion.existence`

English:
lemma ValuativeCriterion.existence
  given: {f : X ⟶ Y} (h : ValuativeCriterion f)
  proof: (iff.mp h).1

中文:
引理 ValuativeCriterion.existence
  条件: {f : X ⟶ Y} (h : ValuativeCriterion f)
  证明: (iff.mp h).1

Depends on / 依赖: iff.mp
-/
lemma ValuativeCriterion.existence {f : X ⟶ Y} (h : ValuativeCriterion f) :
    ValuativeCriterion.Existence f := (iff.mp h).1

/--
lemma `ValuativeCriterion.uniqueness` / 引理 `ValuativeCriterion.uniqueness`

English:
lemma ValuativeCriterion.uniqueness
  given: {f : X ⟶ Y} (h : ValuativeCriterion f)
  proof: (iff.mp h).2

中文:
引理 ValuativeCriterion.uniqueness
  条件: {f : X ⟶ Y} (h : ValuativeCriterion f)
  证明: (iff.mp h).2

Depends on / 依赖: iff.mp
-/
lemma ValuativeCriterion.uniqueness {f : X ⟶ Y} (h : ValuativeCriterion f) :
    ValuativeCriterion.Uniqueness f := (iff.mp h).2

namespace ValuativeCriterion.Existence

open IsLocalRing

set_option backward.isDefEq.respectTransparency.types false in
@[stacks 01KE]
/--
lemma `specializingMap` / 引理 `specializingMap`

English:
lemma specializingMap
  given: (H : ValuativeCriterion.Existence f)
  proof: by
  intro x' y h
  let stalk_y_to_residue_x' : Y.presheaf.stalk y ⟶ X.residueField x' :=
    Y.presheaf.stalkSpecializes h ≫ f.stalkMap x' ≫ X.residue x'
  obtain ⟨A, hA, hA_local⟩ := exists_factor_valuationRing stalk_y_to_residue_x'.hom
  let stalk_y_to_A : Y.presheaf.stalk y ⟶ .of A :=
    CommRi

中文:
引理 specializingMap
  条件: (H : ValuativeCriterion.Existence f)
  证明: by
  intro x' y h
  let stalk_y_to_residue_x' : Y.presheaf.stalk y ⟶ X.residueField x' :=
    Y.presheaf.stalkSpecializes h ≫ f.stalkMap x' ≫ X.residue x'
  obtain ⟨A, hA, hA_local⟩ := exists_factor_valuationRing stalk_y_to_residue_x'.hom
  let stalk_y_to_A : Y.presheaf.stalk y ⟶ .of A :=
    CommRi

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, Spec.map, X.fromSpecResidueField, X.residue, X.residueField, Y.fromSpecStalk, Y.presheaf.stalk, Y.presheaf.stalkSpecializes, algebraMap, codRestrict, exists_factor_valuationRing, f.stalkMap, fromSpecResidueField, fromSpecStalk, hA_local, hom.codRestrict, presheaf, residue, residueField
-/
lemma specializingMap (H : ValuativeCriterion.Existence f) :
    SpecializingMap f := by
  intro x' y h
  let stalk_y_to_residue_x' : Y.presheaf.stalk y ⟶ X.residueField x' :=
    Y.presheaf.stalkSpecializes h ≫ f.stalkMap x' ≫ X.residue x'
  obtain ⟨A, hA, hA_local⟩ := exists_factor_valuationRing stalk_y_to_residue_x'.hom
  let stalk_y_to_A : Y.presheaf.stalk y ⟶ .of A :=
    CommRingCat.ofHom (stalk_y_to_residue_x'.hom.codRestrict _ hA)
  have w : X.fromSpecResidueField x' ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap A (X.residueField x'))) ≫
        Spec.map stalk_y_to_A ≫ Y.fromSpecStalk y := by
    rw [Scheme.fromSpecResidueField]; rw [Category.assoc]; rw [← Scheme.SpecMap_stalkMap_fromSpecStalk]; rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk h]
    simp_rw [← Spec.map_comp_assoc]
    rfl
  obtain ⟨l, hl₁, hl₂⟩ := (H { R := A, K := X.residueField x', commSq := ⟨w⟩, .. }).exists_lift
  dsimp only at hl₁ hl₂
  refine ⟨l (closedPoint A), ?_, ?_⟩
  · simp_rw [← Scheme.fromSpecResidueField_apply x' (closedPoint (X.residueField x')), ← hl₁]
    exact (specializes_closedPoint _).map l.continuous
  · rw [← Scheme.Hom.comp_apply, hl₂]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
    have : Spec.map stalk_y_to_A (closedPoint A) = closedPoint (Y.presheaf.stalk y) :=
      comap_closedPoint (S := A) (stalk_y_to_residue_x'.hom.codRestrict A.toSubring hA)
    rw [this]; rw [Y.fromSpecStalk_closedPoint]

instance {R S : CommRingCat} (e : R ≅ S) : IsLocalHom e.hom.hom :=
  isLocalHom_of_isIso _

set_option backward.isDefEq.respectTransparency false in
/--
lemma `of_specializingMap` / 引理 `of_specializingMap`

English:
lemma of_specializingMap
  given: (H : (topologically @SpecializingMap).universally f)
  proof: by
  rintro ⟨R, K, i₁, i₂, ⟨w⟩⟩
  have : IsDomain (CommRingCat.of R) := ‹_›
  have : ValuationRing (CommRingCat.of R) := ‹_›
  let : Field (CommRingCat.of K) := ‹_›
  replace H := H (pullback.snd i₂ f) i₂ (pullback.fst i₂ f) (.of_hasPullback i₂ f)
  let lft := pullback.lift (Spec.map (CommRingCat.of

中文:
引理 of_specializingMap
  条件: (H : (topologically @SpecializingMap).universally f)
  证明: by
  rintro ⟨R, K, i₁, i₂, ⟨w⟩⟩
  have : IsDomain (CommRingCat.of R) := ‹_›
  have : ValuationRing (CommRingCat.of R) := ‹_›
  let : Field (CommRingCat.of K) := ‹_›
  replace H := H (pullback.snd i₂ f) i₂ (pullback.fst i₂ f) (.of_hasPullback i₂ f)
  let lft := pullback.lift (Spec.map (CommRingCat.of

Depends on / 依赖: CommRingCat, CommRingCat.of, CommRingCat.ofHom, IsDomain, Spec.map, ValuationRing, algebraMap, closedPoint, of_hasPullback, presheaf, presheaf.stalk, pullback, pullback.fst, pullback.lift, pullback.snd, replace, specializes_closedPoint, stalkClos, w.symm
-/
lemma of_specializingMap (H : (topologically @SpecializingMap).universally f) :
    ValuativeCriterion.Existence f := by
  rintro ⟨R, K, i₁, i₂, ⟨w⟩⟩
  have : IsDomain (CommRingCat.of R) := ‹_›
  have : ValuationRing (CommRingCat.of R) := ‹_›
  let : Field (CommRingCat.of K) := ‹_›
  replace H := H (pullback.snd i₂ f) i₂ (pullback.fst i₂ f) (.of_hasPullback i₂ f)
  let lft := pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap R K))) i₁ w.symm
  obtain ⟨x, h₁, h₂⟩ := @H (lft (closedPoint _)) _ (specializes_closedPoint (R := R) _)
  let e : CommRingCat.of R ≅ (Spec <| .of R).presheaf.stalk (pullback.fst i₂ f x) :=
    (stalkClosedPointIso (.of R)).symm ≪≫
      (Spec <| .of R).presheaf.stalkCongr (.of_eq h₂.symm)
  let α := e.hom ≫ (pullback.fst i₂ f).stalkMap x
  have : IsLocalHom e.hom.hom := isLocalHom_of_isIso e.hom
  have : IsLocalHom α.hom := inferInstanceAs
    (IsLocalHom (((pullback.fst i₂ f).stalkMap x).hom.comp e.hom.hom))
  let β := (pullback i₂ f).presheaf.stalkSpecializes h₁ ≫ Scheme.stalkClosedPointTo lft
  have hαβ : α ≫ β = CommRingCat.ofHom (algebraMap R K) := by
    simp only [CommRingCat.coe_of, Iso.trans_hom, Iso.symm_hom, TopCat.Presheaf.stalkCongr_hom,
      Category.assoc, α, e, β, stalkClosedPointIso_inv, StructureSheaf.toStalk]
    change (Scheme.ΓSpecIso (.of R)).inv ≫ (Spec <| .of R).presheaf.germ _ _ _ ≫ _ = _
    simp only [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap_assoc]
    -- `map_top` introduces defeq problems, according to `check_compositions`.
    -- This is probably the cause of the `erw` needed below.
    simp only [TopologicalSpace.Opens.map_top]
    rw [Scheme.germ_stalkClosedPointTo lft ⊤ trivial]
    erw [← Scheme.Hom.comp_app_assoc lft (pullback.fst i₂ f)]
    rw [pullback.lift_fst]
    simp
  have hbij := (bijective_rangeRestrict_comp_of_valuationRing (R := R) (K := K) α.hom β.hom
    (CommRingCat.hom_ext_iff.mp hαβ))
let φ : (pullback i₂ f).presheaf.stalk x ⟶ CommRingCat.of R := CommRingCat.ofHom
    (RingEquiv.ofBijective _ hbij).symm.toRingHom.comp β.hom.rangeRestrict
  have hαφ : α ≫ φ = 𝟙 _ := by ext x; exact (RingEquiv.ofBijective _ hbij).symm_apply_apply x
  have hαφ' : (pullback.fst i₂ f).stalkMap x ≫ φ = e.inv := by
    rw [← cancel_epi e.hom]; rw [← Category.assoc]; rw [hαφ]; rw [e.hom_inv_id]
  have hφβ : φ ≫ CommRingCat.ofHom (algebraMap R K) = β :=
    hαβ ▸ CommRingCat.hom_ext (RingHom.ext fun x => congr_arg Subtype.val
      ((RingEquiv.ofBijective _ hbij).apply_symm_apply (β.hom.rangeRestrict x)))
  refine ⟨⟨⟨Spec.map ((pullback.snd i₂ f).stalkMap x ≫ φ) ≫ X.fromSpecStalk _, ?_, ?_⟩⟩⟩
  · simp only [← Spec.map_comp_assoc, Category.assoc, hφβ]
    simp only [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, β]
    -- This next line only fires as `rw`, not `simp`:
    rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc]
    simp [lft]
  · simp only [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← pullback.condition]
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk_assoc]; rw [← Spec.map_comp_assoc]; rw [hαφ']
    simp only [Iso.trans_inv, TopCat.Presheaf.stalkCongr_inv, Iso.symm_inv, Spec.map_comp,
      Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, e]
    rw [← Spec_stalkClosedPointIso]; rw [← Spec.map_comp_assoc]; rw [Iso.inv_hom_id]; rw [Spec.map_id]; rw [Category.id_comp]

/--
Instance `stableUnderBaseChange` / 实例 `stableUnderBaseChange`

English:
instance stableUnderBaseChange
  signature: : ValuativeCriterion.Existence.IsStableUnderBaseChange
  body: by
  constructor
  intro Y' X X' Y Y'_to_Y f X'_to_X f' hP hf commSq
  let commSq' : ValuativeCommSq f :=
  { R := commSq.R
    K := commSq.K
    i₁ := commSq.i₁ ≫ X'_to_X
    i₂ := commSq.i₂ ≫ Y'_to_Y
    commSq := ⟨by simp only [Category.assoc, hP.w, reassoc_of% commSq.commSq.w]⟩ }
  obtain ⟨l₀, h

中文:
实例 stableUnderBaseChange
  签名: : ValuativeCriterion.Existence.IsStableUnderBaseChange
  定义体: by
  constructor
  intro Y' X X' Y Y'_to_Y f X'_to_X f' hP hf commSq
  let commSq' : ValuativeCommSq f :=
  { R := commSq.R
    K := commSq.K
    i₁ := commSq.i₁ ≫ X'_to_X
    i₂ := commSq.i₂ ≫ Y'_to_Y
    commSq := ⟨by simp only [Category.assoc, hP.w, reassoc_of% commSq.commSq.w]⟩ }
  obtain ⟨l₀, h

Depends on / 依赖: Category, Category.assoc, ValuativeCommSq, _to_X, _to_Y, commSq, commSq.K, commSq.R, commSq.commSq.w, commSq.i, exists_lift, hP.hom_ext, hP.lift, hP.lift_snd, hP.w, hom_ext, lift_snd, reassoc_of
-/
instance stableUnderBaseChange : ValuativeCriterion.Existence.IsStableUnderBaseChange := by
  constructor
  intro Y' X X' Y Y'_to_Y f X'_to_X f' hP hf commSq
  let commSq' : ValuativeCommSq f :=
  { R := commSq.R
    K := commSq.K
    i₁ := commSq.i₁ ≫ X'_to_X
    i₂ := commSq.i₂ ≫ Y'_to_Y
    commSq := ⟨by simp only [Category.assoc, hP.w, reassoc_of% commSq.commSq.w]⟩ }
  obtain ⟨l₀, hl₁, hl₂⟩ := (hf commSq').exists_lift
  refine ⟨⟨⟨hP.lift l₀ commSq.i₂ (by simp_all only [commSq']), ?_, hP.lift_snd _ _ _⟩⟩⟩
  apply hP.hom_ext
  · simpa
  · simp only [Category.assoc]
    rw [hP.lift_snd]
    rw [commSq.commSq.w]

@[stacks 01KE]
/--
lemma `eq` / 引理 `eq`

English:
lemma eq
  proof: by
  ext
  constructor
  · intro _
    apply MorphismProperty.universally_mono
    · apply specializingMap
    · rwa [MorphismProperty.IsStableUnderBaseChange.universally_eq]
  · apply of_specializingMap

中文:
引理 eq
  证明: by
  ext
  constructor
  · intro _
    apply MorphismProperty.universally_mono
    · apply specializingMap
    · rwa [MorphismProperty.IsStableUnderBaseChange.universally_eq]
  · apply of_specializingMap
-/
protected lemma eq :
    ValuativeCriterion.Existence = (topologically @SpecializingMap).universally := by
  ext
  constructor
  · intro _
    apply MorphismProperty.universally_mono
    · apply specializingMap
    · rwa [MorphismProperty.IsStableUnderBaseChange.universally_eq]
  · apply of_specializingMap

end ValuativeCriterion.Existence

/-- The **valuative criterion** for universally closed morphisms. -/
@[stacks 01KF]
/--
lemma `UniversallyClosed.eq_valuativeCriterion` / 引理 `UniversallyClosed.eq_valuativeCriterion`

English:
lemma UniversallyClosed.eq_valuativeCriterion
  proof: by
  rw [universallyClosed_eq_universallySpecializing]; rw [ValuativeCriterion.Existence.eq]

中文:
引理 UniversallyClosed.eq_valuativeCriterion
  证明: by
  rw [universallyClosed_eq_universallySpecializing]; rw [ValuativeCriterion.Existence.eq]

Depends on / 依赖: Existence, ValuativeCriterion, ValuativeCriterion.Existence.eq, universallyClosed_eq_universallySpecializing
-/
lemma UniversallyClosed.eq_valuativeCriterion :
    @UniversallyClosed = ValuativeCriterion.Existence ⊓ @QuasiCompact := by
  rw [universallyClosed_eq_universallySpecializing]; rw [ValuativeCriterion.Existence.eq]

/-- The **valuative criterion** for universally closed morphisms. -/
@[stacks 01KF]
/--
lemma `UniversallyClosed.of_valuativeCriterion` / 引理 `UniversallyClosed.of_valuativeCriterion`

English:
lemma UniversallyClosed.of_valuativeCriterion
  statement: [QuasiCompact f]
  proof: by
  rw [eq_valuativeCriterion]
  exact ⟨hf, ‹_›⟩

中文:
引理 UniversallyClosed.of_valuativeCriterion
  结论: [QuasiCompact f]
  证明: by
  rw [eq_valuativeCriterion]
  exact ⟨hf, ‹_›⟩

Depends on / 依赖: eq_valuativeCriterion
-/
lemma UniversallyClosed.of_valuativeCriterion [QuasiCompact f]
    (hf : ValuativeCriterion.Existence f) : UniversallyClosed f := by
  rw [eq_valuativeCriterion]
  exact ⟨hf, ‹_›⟩

section Uniqueness

/-- The **valuative criterion** for separated morphisms. -/
@[stacks 01L0]
/--
lemma `IsSeparated.of_valuativeCriterion` / 引理 `IsSeparated.of_valuativeCriterion`

English:
lemma IsSeparated.of_valuativeCriterion
  statement: [QuasiSeparated f]
  proof: by
    suffices h : ValuativeCriterion.Existence (pullback.diagonal f) by
      have := UniversallyClosed.of_valuativeCriterion (pullback.diagonal f) h
      exact .of_isPreimmersion _ (pullback.diagonal f).isClosedMap.isClosed_range
    intro S
    have hc : CommSq S.i₁ (Spec.map (CommRingCat.ofHom

中文:
引理 IsSeparated.of_valuativeCriterion
  结论: [QuasiSeparated f]
  证明: by
    suffices h : ValuativeCriterion.Existence (pullback.diagonal f) by
      have := UniversallyClosed.of_valuativeCriterion (pullback.diagonal f) h
      exact .of_isPreimmersion _ (pullback.diagonal f).isClosedMap.isClosed_range
    intro S
    have hc : CommSq S.i₁ (Spec.map (CommRingCat.ofHom

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, CommSq, Existence, LiftStruct, S.commSq.w_assoc, Spec.map, Subsingleton, UniversallyClosed, UniversallyClosed.of_valuativeCriterion, ValuativeCommSq, ValuativeCriterion, ValuativeCriterion.Existence, algebraMap, commSq, commSq.LiftStruct, diagonal, isClosedMap, isClosedMap.isClosed_range, isClosed_range
-/
lemma IsSeparated.of_valuativeCriterion [QuasiSeparated f]
    (hf : ValuativeCriterion.Uniqueness f) : IsSeparated f where
  isClosedImmersion_diagonal := by
    suffices h : ValuativeCriterion.Existence (pullback.diagonal f) by
      have := UniversallyClosed.of_valuativeCriterion (pullback.diagonal f) h
      exact .of_isPreimmersion _ (pullback.diagonal f).isClosedMap.isClosed_range
    intro S
    have hc : CommSq S.i₁ (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)))
        f (S.i₂ ≫ pullback.fst f f ≫ f) := ⟨by simp [← S.commSq.w_assoc]⟩
    let S' : ValuativeCommSq f := ⟨S.R, S.K, S.i₁, S.i₂ ≫ pullback.fst f f ≫ f, hc⟩
    have : Subsingleton S'.commSq.LiftStruct := hf S'
    let S'l₁ : S'.commSq.LiftStruct := ⟨S.i₂ ≫ pullback.fst f f,
      by simp [S', ← S.commSq.w_assoc], by simp [S']⟩
    let S'l₂ : S'.commSq.LiftStruct := ⟨S.i₂ ≫ pullback.snd f f,
      by simp [S', ← S.commSq.w_assoc], by simp [S', pullback.condition]⟩
    have h₁₂ : S'l₁ = S'l₂ := Subsingleton.elim _ _
    constructor
    constructor
    refine ⟨S.i₂ ≫ pullback.fst _ _, ?_, ?_⟩
    · simp [← S.commSq.w_assoc]
    · simp only [Category.assoc]
      apply IsPullback.hom_ext (IsPullback.of_hasPullback _ _)
      · simp
      · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id]
        exact congrArg CommSq.LiftStruct.l h₁₂

set_option backward.isDefEq.respectTransparency false in
@[stacks 01KZ]
/--
lemma `IsSeparated.valuativeCriterion` / 引理 `IsSeparated.valuativeCriterion`

English:
lemma IsSeparated.valuativeCriterion
  given: [IsSeparated f]
  statement: ValuativeCriterion.Uniqueness f
  proof: by
  intro S
  constructor
  rintro ⟨l₁, hl₁, hl₁'⟩ ⟨l₂, hl₂, hl₂'⟩
  ext : 1
  dsimp at *
  have h := hl₁'.trans hl₂'.symm
  let Z := pullback (pullback.diagonal f) (pullback.lift l₁ l₂ h)
  let g : Z ⟶ Spec (.of S.R) := pullback.snd _ _
  have : IsClosedImmersion g := MorphismProperty.pullback_snd

中文:
引理 IsSeparated.valuativeCriterion
  条件: [IsSeparated f]
  结论: ValuativeCriterion.Uniqueness f
  证明: by
  intro S
  constructor
  rintro ⟨l₁, hl₁, hl₁'⟩ ⟨l₂, hl₂, hl₂'⟩
  ext : 1
  dsimp at *
  have h := hl₁'.trans hl₂'.symm
  let Z := pullback (pullback.diagonal f) (pullback.lift l₁ l₂ h)
  let g : Z ⟶ Spec (.of S.R) := pullback.snd _ _
  have : IsClosedImmersion g := MorphismProperty.pullback_snd

Depends on / 依赖: HasAffineProperty, HasAffineProperty.iff_of_isAffine, IsAffine, IsClosedImmersion, MorphismProperty, MorphismProperty.pullback_snd, cancel_epi, conv_lhs, diagonal, iff_of_isAffine, lift_fst, pullback, pullback.diagonal, pullback.lift, pullback.lift_fst, pullback.snd, pullback_snd, this.left
-/
lemma IsSeparated.valuativeCriterion [IsSeparated f] : ValuativeCriterion.Uniqueness f := by
  intro S
  constructor
  rintro ⟨l₁, hl₁, hl₁'⟩ ⟨l₂, hl₂, hl₂'⟩
  ext : 1
  dsimp at *
  have h := hl₁'.trans hl₂'.symm
  let Z := pullback (pullback.diagonal f) (pullback.lift l₁ l₂ h)
  let g : Z ⟶ Spec (.of S.R) := pullback.snd _ _
  have : IsClosedImmersion g := MorphismProperty.pullback_snd _ _ inferInstance
  have hZ : IsAffine Z := by
    rw [@HasAffineProperty.iff_of_isAffine @IsClosedImmersion] at this
    exact this.left
  suffices IsIso g by
    rw [← cancel_epi g]
    conv_lhs => rw [← pullback.lift_fst l₁ l₂ h, ← pullback.condition_assoc]
    conv_rhs => rw [← pullback.lift_snd l₁ l₂ h, ← pullback.condition_assoc]
    simp
  suffices h : Function.Bijective (g.appTop) by
    refine (HasAffineProperty.iff_of_isAffine (P := MorphismProperty.isomorphisms Scheme)).mpr ?_
    exact ⟨hZ, (ConcreteCategory.isIso_iff_bijective _).mpr h⟩
  constructor
  · let l : Spec (.of S.K) ⟶ Z :=
      pullback.lift S.i₁ (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))) (by
        apply IsPullback.hom_ext (IsPullback.of_hasPullback _ _)
        · simpa using hl₁.symm
        · simpa using hl₂.symm)
    have hg : l ≫ g = Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) :=
      pullback.lift_snd _ _ _
    have : Function.Injective ((l ≫ g).appTop) := by
      rw [hg]
      let e := arrowIsoΓSpecOfIsAffine (CommRingCat.ofHom <| algebraMap S.R S.K)
      let P : MorphismProperty CommRingCat :=
RingHom.toMorphismProperty fun f => Function.Injective f
      have : (RingHom.toMorphismProperty <| fun f => Function.Injective f).RespectsIso :=
        RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.injective_respectsIso
      change P _
      rw [← MorphismProperty.arrow_mk_iso_iff (P := P) e]
      exact FaithfulSMul.algebraMap_injective S.R S.K
    rw [Scheme.Hom.comp_appTop] at this
    exact Function.Injective.of_comp this
  · rw [@HasAffineProperty.iff_of_isAffine @IsClosedImmersion] at this
    exact this.right

/--
lemma `IsSeparated.eq_valuativeCriterion` / 引理 `IsSeparated.eq_valuativeCriterion`

English:
lemma IsSeparated.eq_valuativeCriterion
  proof: by
  ext X Y f
  exact ⟨fun _ => ⟨IsSeparated.valuativeCriterion f, inferInstance⟩,
    fun ⟨H, _⟩ => .of_valuativeCriterion f H⟩

中文:
引理 IsSeparated.eq_valuativeCriterion
  证明: by
  ext X Y f
  exact ⟨fun _ => ⟨IsSeparated.valuativeCriterion f, inferInstance⟩,
    fun ⟨H, _⟩ => .of_valuativeCriterion f H⟩

Depends on / 依赖: IsSeparated, IsSeparated.valuativeCriterion, of_valuativeCriterion, valuativeCriterion
-/
lemma IsSeparated.eq_valuativeCriterion :
    @IsSeparated = ValuativeCriterion.Uniqueness ⊓ @QuasiSeparated := by
  ext X Y f
  exact ⟨fun _ => ⟨IsSeparated.valuativeCriterion f, inferInstance⟩,
    fun ⟨H, _⟩ => .of_valuativeCriterion f H⟩

end Uniqueness

set_option backward.isDefEq.respectTransparency.types false in
/-- The **valuative criterion** for proper morphisms. -/
@[stacks 0BX5]
/--
lemma `IsProper.eq_valuativeCriterion` / 引理 `IsProper.eq_valuativeCriterion`

English:
lemma IsProper.eq_valuativeCriterion
  proof: by
  rw [isProper_eq]; rw [IsSeparated.eq_valuativeCriterion]; rw [ValuativeCriterion.eq]; rw [UniversallyClosed.eq_valuativeCriterion]
  simp_rw [inf_assoc]
  ext X Y f
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ↔ _ ∧ _ ∧ _ ∧ _ ∧ _
  tauto

中文:
引理 IsProper.eq_valuativeCriterion
  证明: by
  rw [isProper_eq]; rw [IsSeparated.eq_valuativeCriterion]; rw [ValuativeCriterion.eq]; rw [UniversallyClosed.eq_valuativeCriterion]
  simp_rw [inf_assoc]
  ext X Y f
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ↔ _ ∧ _ ∧ _ ∧ _ ∧ _
  tauto

Depends on / 依赖: IsSeparated, IsSeparated.eq_valuativeCriterion, UniversallyClosed, UniversallyClosed.eq_valuativeCriterion, ValuativeCriterion, ValuativeCriterion.eq, eq_valuativeCriterion, inf_assoc, isProper_eq, simp_rw
-/
lemma IsProper.eq_valuativeCriterion :
    @IsProper = ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType := by
  rw [isProper_eq]; rw [IsSeparated.eq_valuativeCriterion]; rw [ValuativeCriterion.eq]; rw [UniversallyClosed.eq_valuativeCriterion]
  simp_rw [inf_assoc]
  ext X Y f
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ↔ _ ∧ _ ∧ _ ∧ _ ∧ _
  tauto

/-- The **valuative criterion** for proper morphisms. -/
@[stacks 0BX5]
/--
lemma `IsProper.of_valuativeCriterion` / 引理 `IsProper.of_valuativeCriterion`

English:
lemma IsProper.of_valuativeCriterion
  statement: [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
  proof: by
  rw [eq_valuativeCriterion]
  exact ⟨⟨⟨‹_›, ‹_›⟩, ‹_›⟩, ‹_›⟩

中文:
引理 IsProper.of_valuativeCriterion
  结论: [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
  证明: by
  rw [eq_valuativeCriterion]
  exact ⟨⟨⟨‹_›, ‹_›⟩, ‹_›⟩, ‹_›⟩

Depends on / 依赖: eq_valuativeCriterion
-/
lemma IsProper.of_valuativeCriterion [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    (H : ValuativeCriterion f) : IsProper f := by
  rw [eq_valuativeCriterion]
  exact ⟨⟨⟨‹_›, ‹_›⟩, ‹_›⟩, ‹_›⟩

end AlgebraicGeometry
