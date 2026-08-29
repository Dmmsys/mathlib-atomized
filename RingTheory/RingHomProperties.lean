/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Properties of ring homomorphisms

We provide the basic framework for talking about properties of ring homomorphisms.
The following meta-properties of predicates on ring homomorphisms are defined

* `RingHom.RespectsIso`: `P` respects isomorphisms if `P f → P (e ≫ f)` and
  `P f → P (f ≫ e)`, where `e` is an isomorphism.
* `RingHom.StableUnderComposition`: `P` is stable under composition if `P f → P g → P (f ≫ g)`.
* `RingHom.IsStableUnderBaseChange`: `P` is stable under base change if `P (S ⟶ Y)`
  implies `P (X ⟶ X ⊗[S] Y)`.

-/

@[expose] public section


universe u

open CategoryTheory Opposite CategoryTheory.Limits TensorProduct

namespace RingHom

variable {P Q : forall {R S : Type u} [CommRing R] [CommRing S] (_ : R ->+* S), Prop}

section RespectsIso

variable (P) in
/--
Definition of `RespectsIso` / `RespectsIso` 的定义

English:
definition RespectsIso
  signature: : Prop
  body: (forall {R S T : Type u} [CommRing R] [CommRing S] [CommRing T],
      forall (f : R ->+* S) (e : S ≃+* T) (_ : P f), P (e.toRingHom.comp f)) ∧
    forall {R S T : Type u} [CommRing R] [CommRing S] [CommRing T],
      forall (f : S ->+* T) (e : R ≃+* S) (_ : P f), P (f.comp e.toRingHom)

中文:
定义 RespectsIso
  签名: : 命题
  定义体: (forall {R S T : Type u} [CommRing R] [CommRing S] [CommRing T],
      forall (f : R ->+* S) (e : S ≃+* T) (_ : P f), P (e.toRingHom.comp f)) ∧
    forall {R S T : Type u} [CommRing R] [CommRing S] [CommRing T],
      forall (f : S ->+* T) (e : R ≃+* S) (_ : P f), P (f.comp e.toRingHom)

Depends on / 依赖: CommRing, e.toRingHom, e.toRingHom.comp, f.comp, toRingHom
-/
def RespectsIso : Prop :=
  (forall {R S T : Type u} [CommRing R] [CommRing S] [CommRing T],
      forall (f : R ->+* S) (e : S ≃+* T) (_ : P f), P (e.toRingHom.comp f)) ∧
    forall {R S T : Type u} [CommRing R] [CommRing S] [CommRing T],
      forall (f : S ->+* T) (e : R ≃+* S) (_ : P f), P (f.comp e.toRingHom)

/--
theorem `RespectsIso.cancel_left_isIso` / 定理 `RespectsIso.cancel_left_isIso`

English:
theorem RespectsIso.cancel_left_isIso
  statement: (hP : RespectsIso @P) {R S T : CommRingCat} (f : R ⟶ S)
  proof: ⟨fun H => by
    convert! hP.2 (f ≫ g).hom (asIso f).symm.commRingCatIsoToRingEquiv H
    simp [← CommRingCat.hom_comp], hP.2 g.hom (asIso f).commRingCatIsoToRingEquiv⟩

中文:
定理 RespectsIso.cancel_left_isIso
  结论: (hP : RespectsIso @P) {R S T : 交换环范畴} (f : R ⟶ S)
  证明: ⟨fun H => by
    convert! hP.2 (f ≫ g).hom (asIso f).symm.commRingCatIsoToRingEquiv H
    simp [← CommRingCat.hom_comp], hP.2 g.hom (asIso f).commRingCatIsoToRingEquiv⟩

Depends on / 依赖: CommRingCat, CommRingCat.hom_comp, commRingCatIsoToRingEquiv, convert, g.hom, hom_comp, symm.commRingCatIsoToRingEquiv
-/
theorem RespectsIso.cancel_left_isIso (hP : RespectsIso @P) {R S T : CommRingCat} (f : R ⟶ S)
    (g : S ⟶ T) [IsIso f] : P (g.hom.comp f.hom) ↔ P g.hom :=
  ⟨fun H => by
    convert! hP.2 (f ≫ g).hom (asIso f).symm.commRingCatIsoToRingEquiv H
    simp [← CommRingCat.hom_comp], hP.2 g.hom (asIso f).commRingCatIsoToRingEquiv⟩

/--
theorem `RespectsIso.cancel_right_isIso` / 定理 `RespectsIso.cancel_right_isIso`

English:
theorem RespectsIso.cancel_right_isIso
  statement: (hP : RespectsIso @P) {R S T : CommRingCat} (f : R ⟶ S)
  proof: ⟨fun H => by
    convert! hP.1 (f ≫ g).hom (asIso g).symm.commRingCatIsoToRingEquiv H
    simp [← CommRingCat.hom_comp],
   hP.1 f.hom (asIso g).commRingCatIsoToRingEquiv⟩

中文:
定理 RespectsIso.cancel_right_isIso
  结论: (hP : RespectsIso @P) {R S T : 交换环范畴} (f : R ⟶ S)
  证明: ⟨fun H => by
    convert! hP.1 (f ≫ g).hom (asIso g).symm.commRingCatIsoToRingEquiv H
    simp [← CommRingCat.hom_comp],
   hP.1 f.hom (asIso g).commRingCatIsoToRingEquiv⟩

Depends on / 依赖: CommRingCat, CommRingCat.hom_comp, commRingCatIsoToRingEquiv, convert, f.hom, hom_comp, symm.commRingCatIsoToRingEquiv
-/
theorem RespectsIso.cancel_right_isIso (hP : RespectsIso @P) {R S T : CommRingCat} (f : R ⟶ S)
    (g : S ⟶ T) [IsIso g] : P (g.hom.comp f.hom) ↔ P f.hom :=
  ⟨fun H => by
    convert! hP.1 (f ≫ g).hom (asIso g).symm.commRingCatIsoToRingEquiv H
    simp [← CommRingCat.hom_comp],
   hP.1 f.hom (asIso g).commRingCatIsoToRingEquiv⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `RespectsIso.isLocalization_away_iff` / 定理 `RespectsIso.isLocalization_away_iff`

English:
theorem RespectsIso.isLocalization_away_iff
  statement: (hP : RingHom.RespectsIso @P) {R S : Type u}
  proof: by
  let e₁ : R' ≃+* Localization.Away r :=
    (IsLocalization.algEquiv (Submonoid.powers r) _ _).toRingEquiv
  let e₂ : Localization.Away (f r) ≃+* S' :=
    (IsLocalization.algEquiv (Submonoid.powers (f r)) _ _).toRingEquiv
  refine (hP.cancel_left_isIso e₁.toCommRingCatIso.hom (CommRingCat.ofHom

中文:
定理 RespectsIso.isLocalization_away_iff
  结论: (hP : 环态射.RespectsIso @P) {R S : 类型u}
  证明: by
  let e₁ : R' ≃+* Localization.Away r :=
    (IsLocalization.algEquiv (Submonoid.powers r) _ _).toRingEquiv
  let e₂ : Localization.Away (f r) ≃+* S' :=
    (IsLocalization.algEquiv (Submonoid.powers (f r)) _ _).toRingEquiv
  refine (hP.cancel_left_isIso e₁.toCommRingCatIso.hom (CommRingCat.ofHom

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, IsLocalization, IsLocalization.algEquiv, Localization, Localization.Away, Submonoid, Submonoid.powers, algEquiv, cancel_left_isIso, cancel_right_isIso, eq_iff_iff, hP.cancel_left_isIso, hP.cancel_right_isIso, powers, symm.trans, toCommRingCatIso, toCommRingCatIso.hom, toRingEquiv
-/
theorem RespectsIso.isLocalization_away_iff (hP : RingHom.RespectsIso @P) {R S : Type u}
    (R' S' : Type u) [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] [Algebra R R']
    [Algebra S S'] (f : R ->+* S) (r : R) [IsLocalization.Away r R'] [IsLocalization.Away (f r) S'] :
    P (Localization.awayMap f r) ↔ P (IsLocalization.Away.map R' S' f r) := by
  let e₁ : R' ≃+* Localization.Away r :=
    (IsLocalization.algEquiv (Submonoid.powers r) _ _).toRingEquiv
  let e₂ : Localization.Away (f r) ≃+* S' :=
    (IsLocalization.algEquiv (Submonoid.powers (f r)) _ _).toRingEquiv
  refine (hP.cancel_left_isIso e₁.toCommRingCatIso.hom (CommRingCat.ofHom _)).symm.trans ?_
  refine (hP.cancel_right_isIso (CommRingCat.ofHom _) e₂.toCommRingCatIso.hom).symm.trans ?_
  rw [← eq_iff_iff]
  congr 1
  -- Porting note: Here, the proof used to have a huge `simp` involving `[anonymous]`, which didn't
  -- work out anymore. The issue seemed to be that it couldn't handle a term in which Ring
  -- homomorphisms were repeatedly casted to the bundled category and back. Here we resolve the
  -- problem by converting the goal to a more straightforward form.
  let e := (e₂ : Localization.Away (f r) ->+* S').comp
      (((IsLocalization.map (Localization.Away (f r)) f
            (by rintro x ⟨n, rfl⟩; use n; simp : Submonoid.powers r <= Submonoid.comap f
                (Submonoid.powers (f r)))) : Localization.Away r ->+* Localization.Away (f r)).comp
                (e₁ : R' ->+* Localization.Away r))
  suffices e = IsLocalization.Away.map R' S' f r by
    convert! this
  apply IsLocalization.ringHom_ext (Submonoid.powers r) _
  ext1 x
  dsimp [e, e₁, e₂, IsLocalization.Away.map]
  simp only [IsLocalization.map_eq, id_apply, RingHomCompTriple.comp_apply]

/--
lemma `RespectsIso.and` / 引理 `RespectsIso.and`

English:
lemma RespectsIso.and
  given: (hP : RespectsIso P) (hQ : RespectsIso Q)
  proof: by
  refine ⟨?_, ?_⟩
  · introv hf
    exact ⟨hP.1 f e hf.1, hQ.1 f e hf.2⟩
  · introv hf
    exact ⟨hP.2 f e hf.1, hQ.2 f e hf.2⟩

中文:
引理 RespectsIso.and
  条件: (hP : RespectsIso P) (hQ : RespectsIso Q)
  证明: by
  refine ⟨?_, ?_⟩
  · introv hf
    exact ⟨hP.1 f e hf.1, hQ.1 f e hf.2⟩
  · introv hf
    exact ⟨hP.2 f e hf.1, hQ.2 f e hf.2⟩

Depends on / 依赖: introv
-/
lemma RespectsIso.and (hP : RespectsIso P) (hQ : RespectsIso Q) :
    RespectsIso (fun f => P f ∧ Q f) := by
  refine ⟨?_, ?_⟩
  · introv hf
    exact ⟨hP.1 f e hf.1, hQ.1 f e hf.2⟩
  · introv hf
    exact ⟨hP.2 f e hf.1, hQ.2 f e hf.2⟩

end RespectsIso

section StableUnderComposition

variable (P) in
/--
Definition of `StableUnderComposition` / `StableUnderComposition` 的定义

English:
definition StableUnderComposition
  signature: : Prop
  body: forall ⦃R S T⦄ [CommRing R] [CommRing S] [CommRing T],
    forall (f : R ->+* S) (g : S ->+* T) (_ : P f) (_ : P g), P (g.comp f)

中文:
定义 StableUnderComposition
  签名: : 命题
  定义体: forall ⦃R S T⦄ [CommRing R] [CommRing S] [CommRing T],
    forall (f : R ->+* S) (g : S ->+* T) (_ : P f) (_ : P g), P (g.comp f)

Depends on / 依赖: CommRing, g.comp
-/
def StableUnderComposition : Prop :=
  forall ⦃R S T⦄ [CommRing R] [CommRing S] [CommRing T],
    forall (f : R ->+* S) (g : S ->+* T) (_ : P f) (_ : P g), P (g.comp f)

/--
theorem `StableUnderComposition.respectsIso` / 定理 `StableUnderComposition.respectsIso`

English:
theorem StableUnderComposition.respectsIso
  statement: (hP : RingHom.StableUnderComposition @P)
  proof: by
  constructor
  · introv H
    apply hP
    exacts [H, hP' e]
  · introv H
    apply hP
    exacts [hP' e, H]

中文:
定理 StableUnderComposition.respectsIso
  结论: (hP : 环态射.StableUnderComposition @P)
  证明: by
  constructor
  · introv H
    apply hP
    exacts [H, hP' e]
  · introv H
    apply hP
    exacts [hP' e, H]

Depends on / 依赖: exacts, introv
-/
theorem StableUnderComposition.respectsIso (hP : RingHom.StableUnderComposition @P)
    (hP' : forall {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S), P e.toRingHom) :
    RingHom.RespectsIso @P := by
  constructor
  · introv H
    apply hP
    exacts [H, hP' e]
  · introv H
    apply hP
    exacts [hP' e, H]

/--
lemma `StableUnderComposition.and` / 引理 `StableUnderComposition.and`

English:
lemma StableUnderComposition.and
  given: (hP : StableUnderComposition P) (hQ : StableUnderComposition Q)
  proof: by
  introv R hf hg
  exact ⟨hP f g hf.1 hg.1, hQ f g hf.2 hg.2⟩

中文:
引理 StableUnderComposition.and
  条件: (hP : StableUnderComposition P) (hQ : StableUnderComposition Q)
  证明: by
  introv R hf hg
  exact ⟨hP f g hf.1 hg.1, hQ f g hf.2 hg.2⟩

Depends on / 依赖: introv
-/
lemma StableUnderComposition.and (hP : StableUnderComposition P) (hQ : StableUnderComposition Q) :
    StableUnderComposition (fun f => P f ∧ Q f) := by
  introv R hf hg
  exact ⟨hP f g hf.1 hg.1, hQ f g hf.2 hg.2⟩

end StableUnderComposition

section IsStableUnderBaseChange

variable (P) in
/--
Definition of `IsStableUnderBaseChange` / `IsStableUnderBaseChange` 的定义

English:
definition IsStableUnderBaseChange
  signature: : Prop
  body: forall (R S R' S') [CommRing R] [CommRing S] [CommRing R'] [CommRing S'],
    forall [Algebra R S] [Algebra R R'] [Algebra R S'] [Algebra S S'] [Algebra R' S'],
      forall [IsScalarTower R S S'] [IsScalarTower R R' S'],
        forall [Algebra.IsPushout R S R' S'], P (algebraMap R S) -> P (algebra

中文:
定义 是StableUnderBaseChange
  签名: : 命题
  定义体: forall (R S R' S') [CommRing R] [CommRing S] [CommRing R'] [CommRing S'],
    forall [Algebra R S] [Algebra R R'] [Algebra R S'] [Algebra S S'] [Algebra R' S'],
      forall [IsScalarTower R S S'] [IsScalarTower R R' S'],
        forall [Algebra.IsPushout R S R' S'], P (algebraMap R S) -> P (algebra

Depends on / 依赖: Algebra, Algebra.IsPushout, CommRing, IsPushout, IsScalarTower, algebraMap
-/
def IsStableUnderBaseChange : Prop :=
  forall (R S R' S') [CommRing R] [CommRing S] [CommRing R'] [CommRing S'],
    forall [Algebra R S] [Algebra R R'] [Algebra R S'] [Algebra S S'] [Algebra R' S'],
      forall [IsScalarTower R S S'] [IsScalarTower R R' S'],
        forall [Algebra.IsPushout R S R' S'], P (algebraMap R S) -> P (algebraMap R' S')

/--
theorem `IsStableUnderBaseChange.mk` / 定理 `IsStableUnderBaseChange.mk`

English:
theorem IsStableUnderBaseChange.mk
  statement: (h₁ : RespectsIso @P)
  proof: by
  introv R h H
  let e := h.symm.1.equiv
  let f' := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom R R' S')
    (IsScalarTower.toAlgHom R S S')
  have hef (x : _) : e x = f' x := by
    suffices e.toLinearMap.restrictScalars R = f'.toLinearMap from congr($this x)
    exact ext' fun x y

中文:
定理 是StableUnderBaseChange.mk
  结论: (h₁ : RespectsIso @P)
  证明: by
  introv R h H
  let e := h.symm.1.equiv
  let f' := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom R R' S')
    (IsScalarTower.toAlgHom R S S')
  have hef (x : _) : e x = f' x := by
    suffices e.toLinearMap.restrictScalars R = f'.toLinearMap from congr($this x)
    exact ext' fun x y
-/
theorem IsStableUnderBaseChange.mk (h₁ : RespectsIso @P)
    (h₂ : forall ⦃R S T⦄ [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T],
      P (algebraMap R T) -> P (algebraMap S (S otimes[R] T))) :
    IsStableUnderBaseChange @P := by
  introv R h H
  let e := h.symm.1.equiv
  let f' := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom R R' S')
    (IsScalarTower.toAlgHom R S S')
  have hef (x : _) : e x = f' x := by
    suffices e.toLinearMap.restrictScalars R = f'.toLinearMap from congr($this x)
    exact ext' fun x y => by simp [e, f', IsBaseChange.equiv_tmul, Algebra.smul_def]
  have hemul (x y : _) : e (x * y) = e x * e y := by simp_rw [hef, map_mul]
  convert! h₁.1 _ { e with map_mul' := hemul } (h₂ H)
  ext x
  simp [e, h.symm.1.equiv_tmul, Algebra.smul_def]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/--
lemma `IsStableUnderBaseChange.tensorProduct` / 引理 `IsStableUnderBaseChange.tensorProduct`

English:
lemma IsStableUnderBaseChange.tensorProduct
  statement: (hP : RingHom.IsStableUnderBaseChange P)
  proof: -- This only works because the `Algebra.TensorProduct.rightAlgebra` instance is present here.
  hP _ _ _ _ h

中文:
引理 是StableUnderBaseChange.tensorProduct
  结论: (hP : 环态射.是StableUnderBaseChange P)
  证明: -- This only works because the `Algebra.TensorProduct.rightAlgebra` instance is present here.
  hP _ _ _ _ h

Depends on / 依赖: OnePoint, OnePoint.isOpen_iff_of_notMem, Option.some_ne_none, compl_union_self, disjoint_compl_left, disjoint_compl_right, exacts, hxy.symm, isOpen_compl_singleton, isOpen_discrete, isOpen_iff_of_notMem, some_ne_none, subset, symm.subset
-/
lemma IsStableUnderBaseChange.tensorProduct (hP : RingHom.IsStableUnderBaseChange P)
    {R S : Type u} (T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (h : P (algebraMap R S)) :
    P (algebraMap T (T otimes[R] S)) :=
  -- This only works because the `Algebra.TensorProduct.rightAlgebra` instance is present here.
  hP _ _ _ _ h

set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsStableUnderBaseChange.pushout_inl` / 定理 `IsStableUnderBaseChange.pushout_inl`

English:
theorem IsStableUnderBaseChange.pushout_inl
  statement: (hP : RingHom.IsStableUnderBaseChange @P)
  proof: by
  let := f.hom.toAlgebra
  let := g.hom.toAlgebra
  rw [← show _ = pushout.inl f g from
      colimit.isoColimitCocone_ι_inv ⟨_]; rw [CommRingCat.pushoutCoconeIsColimit R S T⟩ WalkingSpan.left]; rw [CommRingCat.hom_comp]; rw [hP'.cancel_right_isIso]
  dsimp only [CommRingCat.pushoutCocone_inl, Pu

中文:
定理 是StableUnderBaseChange.pushout_inl
  结论: (hP : 环态射.是StableUnderBaseChange @P)
  证明: by
  let := f.hom.toAlgebra
  let := g.hom.toAlgebra
  rw [← show _ = pushout.inl f g from
      colimit.isoColimitCocone_ι_inv ⟨_]; rw [CommRingCat.pushoutCoconeIsColimit R S T⟩ WalkingSpan.left]; rw [CommRingCat.hom_comp]; rw [hP'.cancel_right_isIso]
  dsimp only [CommRingCat.pushoutCocone_inl, Pu

Depends on / 依赖: CommRingCat, CommRingCat.hom_comp, CommRingCat.pushoutCoconeIsColimit, CommRingCat.pushoutCocone_inl, PushoutCocone, WalkingSpan, WalkingSpan.left, cancel_right_isIso, colimit, colimit.isoColimitCocone_, f.hom.toAlgebra, g.hom.toAlgebra, hom_comp, otimes, pushout, pushout.inl, pushoutCoconeIsColimit, pushoutCocone_inl, toAlgebra
-/
theorem IsStableUnderBaseChange.pushout_inl (hP : RingHom.IsStableUnderBaseChange @P)
    (hP' : RingHom.RespectsIso @P) {R S T : CommRingCat} (f : R ⟶ S) (g : R ⟶ T) (H : P g.hom) :
    P (pushout.inl _ _ : S ⟶ pushout f g).hom := by
  let := f.hom.toAlgebra
  let := g.hom.toAlgebra
  rw [← show _ = pushout.inl f g from
      colimit.isoColimitCocone_ι_inv ⟨_]; rw [CommRingCat.pushoutCoconeIsColimit R S T⟩ WalkingSpan.left]; rw [CommRingCat.hom_comp]; rw [hP'.cancel_right_isIso]
  dsimp only [CommRingCat.pushoutCocone_inl, PushoutCocone.ι_app_left]
  apply hP R T S (S otimes[R] T)
  exact H

/--
lemma `IsStableUnderBaseChange.and` / 引理 `IsStableUnderBaseChange.and`

English:
lemma IsStableUnderBaseChange.and
  statement: (hP : IsStableUnderBaseChange P)
  proof: by
  introv R _ h
  exact ⟨hP R S R' S' h.1, hQ R S R' S' h.2⟩

中文:
引理 是StableUnderBaseChange.and
  结论: (hP : 是StableUnderBaseChange P)
  证明: by
  introv R _ h
  exact ⟨hP R S R' S' h.1, hQ R S R' S' h.2⟩

Depends on / 依赖: introv
-/
lemma IsStableUnderBaseChange.and (hP : IsStableUnderBaseChange P)
    (hQ : IsStableUnderBaseChange Q) :
    IsStableUnderBaseChange (fun f => P f ∧ Q f) := by
  introv R _ h
  exact ⟨hP R S R' S' h.1, hQ R S R' S' h.2⟩

end IsStableUnderBaseChange

section ToMorphismProperty

variable (P) in
/--
Definition of `toMorphismProperty` / `toMorphismProperty` 的定义

English:
definition toMorphismProperty
  signature: : MorphismProperty CommRingCat
  body: fun _ _ f => P f.hom

中文:
定义 toMorphismProperty
  签名: : MorphismProperty 交换环范畴
  定义体: fun _ _ f => P f.hom

Depends on / 依赖: f.hom
-/
def toMorphismProperty : MorphismProperty CommRingCat := fun _ _ f => P f.hom

/--
lemma `toMorphismProperty_respectsIso_iff` / 引理 `toMorphismProperty_respectsIso_iff`

English:
lemma toMorphismProperty_respectsIso_iff
  proof: by
  refine ⟨fun h => MorphismProperty.RespectsIso.mk _ ?_ ?_, fun h => ⟨?_, ?_⟩⟩
  · intro X Y Z e f hf
    exact h.right f.hom e.commRingCatIsoToRingEquiv hf
  · intro X Y Z e f hf
    exact h.left f.hom e.commRingCatIsoToRingEquiv hf
  · intro X Y Z _ _ _ f e hf
    exact MorphismProperty.Respect

中文:
引理 toMorphismProperty_respectsIso_iff
  证明: by
  refine ⟨fun h => MorphismProperty.RespectsIso.mk _ ?_ ?_, fun h => ⟨?_, ?_⟩⟩
  · intro X Y Z e f hf
    exact h.right f.hom e.commRingCatIsoToRingEquiv hf
  · intro X Y Z e f hf
    exact h.left f.hom e.commRingCatIsoToRingEquiv hf
  · intro X Y Z _ _ _ f e hf
    exact MorphismProperty.Respect

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, MorphismProperty, MorphismProperty.RespectsIso.mk, MorphismProperty.RespectsIso.postcomp, MorphismProperty.RespectsIso.precomp, RespectsIso, commRingCatIsoToRingEquiv, e.commRingCatIsoToRingEquiv, e.toCommRingCatIso.hom, f.hom, h.left, h.right, postcomp, precomp, toCommRingCatIso, toMorphismProperty
-/
lemma toMorphismProperty_respectsIso_iff :
    RespectsIso P ↔ (toMorphismProperty P).RespectsIso := by
  refine ⟨fun h => MorphismProperty.RespectsIso.mk _ ?_ ?_, fun h => ⟨?_, ?_⟩⟩
  · intro X Y Z e f hf
    exact h.right f.hom e.commRingCatIsoToRingEquiv hf
  · intro X Y Z e f hf
    exact h.left f.hom e.commRingCatIsoToRingEquiv hf
  · intro X Y Z _ _ _ f e hf
    exact MorphismProperty.RespectsIso.postcomp (toMorphismProperty P)
      e.toCommRingCatIso.hom (CommRingCat.ofHom f) hf
  · intro X Y Z _ _ _ f e
    exact MorphismProperty.RespectsIso.precomp (toMorphismProperty P)
      e.toCommRingCatIso.hom (CommRingCat.ofHom f)

/--
lemma `isStableUnderCobaseChange_toMorphismProperty_iff` / 引理 `isStableUnderCobaseChange_toMorphismProperty_iff`

English:
lemma isStableUnderCobaseChange_toMorphismProperty_iff
  proof: by
  refine ⟨fun h R S R' S' _ _ _ _ _ _ _ _ _ _ _ hsq hRS => ?_,
      fun h => ⟨fun {R} S R' S' f g f' g' hsq hf => ?_⟩⟩
  · rw [← CommRingCat.isPushout_iff_isPushout] at hsq
    exact h.1 (f := CommRingCat.ofHom (algebraMap R S)) hsq.flip hRS
  · algebraize [f.hom, g.hom, f'.hom, g'.hom, f'.hom.c

中文:
引理 isStableUnderCobaseChange_toMorphismProperty_iff
  证明: by
  refine ⟨fun h R S R' S' _ _ _ _ _ _ _ _ _ _ _ hsq hRS => ?_,
      fun h => ⟨fun {R} S R' S' f g f' g' hsq hf => ?_⟩⟩
  · rw [← CommRingCat.isPushout_iff_isPushout] at hsq
    exact h.1 (f := CommRingCat.ofHom (algebraMap R S)) hsq.flip hRS
  · algebraize [f.hom, g.hom, f'.hom, g'.hom, f'.hom.c

Depends on / 依赖: Algebra, Algebra.IsPushout, CommRingCat, CommRingCat.isPushout_iff_isPushout, CommRingCat.isPushout_iff_isPushout.mp, CommRingCat.ofHom, IsPushout, IsScalarTower, algebraMap, algebraize, f.hom, g.hom, hom.comp, hsq.flip, isPushout_iff_isPushout, of_algebraMap_eq
-/
lemma isStableUnderCobaseChange_toMorphismProperty_iff :
    (toMorphismProperty P).IsStableUnderCobaseChange ↔ IsStableUnderBaseChange P := by
  refine ⟨fun h R S R' S' _ _ _ _ _ _ _ _ _ _ _ hsq hRS => ?_,
      fun h => ⟨fun {R} S R' S' f g f' g' hsq hf => ?_⟩⟩
  · rw [← CommRingCat.isPushout_iff_isPushout] at hsq
    exact h.1 (f := CommRingCat.ofHom (algebraMap R S)) hsq.flip hRS
  · algebraize [f.hom, g.hom, f'.hom, g'.hom, f'.hom.comp g.hom]
    have : IsScalarTower R S S' := .of_algebraMap_eq fun x => congr($(hsq.1.1).hom x)
    have : Algebra.IsPushout R S R' S' := (CommRingCat.isPushout_iff_isPushout.mp hsq).symm
    exact h (R := R) (S := S) _ _ hf

/--
lemma `RespectsIso.arrow_mk_iso_iff` / 引理 `RespectsIso.arrow_mk_iso_iff`

English:
lemma RespectsIso.arrow_mk_iso_iff
  statement: (hQ : RingHom.RespectsIso P) {A B A' B' : CommRingCat}
  proof: by
  have : (toMorphismProperty P).RespectsIso := by
    rwa [← toMorphismProperty_respectsIso_iff]
  change toMorphismProperty P _ ↔ toMorphismProperty P _
  rw [MorphismProperty.arrow_mk_iso_iff (toMorphismProperty P) e]

中文:
引理 RespectsIso.arrow_mk_iso_iff
  结论: (hQ : 环态射.RespectsIso P) {A B A' B' : 交换环范畴}
  证明: by
  have : (toMorphismProperty P).RespectsIso := by
    rwa [← toMorphismProperty_respectsIso_iff]
  change toMorphismProperty P _ ↔ toMorphismProperty P _
  rw [MorphismProperty.arrow_mk_iso_iff (toMorphismProperty P) e]

Depends on / 依赖: MorphismProperty, MorphismProperty.arrow_mk_iso_iff, RespectsIso, arrow_mk_iso_iff, toMorphismProperty, toMorphismProperty_respectsIso_iff
-/
lemma RespectsIso.arrow_mk_iso_iff (hQ : RingHom.RespectsIso P) {A B A' B' : CommRingCat}
    {f : A ⟶ B} {g : A' ⟶ B'} (e : Arrow.mk f ≅ Arrow.mk g) :
    P f.hom ↔ P g.hom := by
  have : (toMorphismProperty P).RespectsIso := by
    rwa [← toMorphismProperty_respectsIso_iff]
  change toMorphismProperty P _ ↔ toMorphismProperty P _
  rw [MorphismProperty.arrow_mk_iso_iff (toMorphismProperty P) e]

end ToMorphismProperty

section Descent

variable (Q : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> Prop)

variable (R S T : Type u) [CommRing R] [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

variable (P) in
/--
Definition of `CodescendsAlong` / `CodescendsAlong` 的定义

English:
definition CodescendsAlong
  signature: : Prop
  body: forall ⦃R S R' S' : Type u⦄ [CommRing R] [CommRing S] [CommRing R'] [CommRing S'],
  forall [Algebra R S] [Algebra R R'] [Algebra R S'] [Algebra S S'] [Algebra R' S'],
    forall [IsScalarTower R S S'] [IsScalarTower R R' S'],
      forall [Algebra.IsPushout R S R' S'],
        Q (algebraMap R R') -

中文:
定义 余descendsAlong
  签名: : 命题
  定义体: forall ⦃R S R' S' : Type u⦄ [CommRing R] [CommRing S] [CommRing R'] [CommRing S'],
  forall [Algebra R S] [Algebra R R'] [Algebra R S'] [Algebra S S'] [Algebra R' S'],
    forall [IsScalarTower R S S'] [IsScalarTower R R' S'],
      forall [Algebra.IsPushout R S R' S'],
        Q (algebraMap R R') -

Depends on / 依赖: Algebra, Algebra.IsPushout, CommRing, IsPushout, IsScalarTower, LinearEquiv, LinearEquiv.finTwoArrow, algebraMap, finTwoArrow, smulCommClass, symm.smulCommClass
-/
def CodescendsAlong : Prop :=
  forall ⦃R S R' S' : Type u⦄ [CommRing R] [CommRing S] [CommRing R'] [CommRing S'],
  forall [Algebra R S] [Algebra R R'] [Algebra R S'] [Algebra S S'] [Algebra R' S'],
    forall [IsScalarTower R S S'] [IsScalarTower R R' S'],
      forall [Algebra.IsPushout R S R' S'],
        Q (algebraMap R R') -> P (algebraMap R' S') -> P (algebraMap R S)

/--
lemma `CodescendsAlong.mk` / 引理 `CodescendsAlong.mk`

English:
lemma CodescendsAlong.mk
  statement: (h₁ : RespectsIso P)
  proof: by
  introv R h hQ H
  let e := h.symm.equiv
  have : (e.symm : _ ->+* _).comp (algebraMap R' S') = algebraMap R' (R' otimes[R] S) := by
    ext r
    simp [e]
  apply h₂ hQ
  rw [← this]
  exact h₁.1 _ _ H

中文:
引理 余descendsAlong.mk
  结论: (h₁ : RespectsIso P)
  证明: by
  introv R h hQ H
  let e := h.symm.equiv
  have : (e.symm : _ ->+* _).comp (algebraMap R' S') = algebraMap R' (R' otimes[R] S) := by
    ext r
    simp [e]
  apply h₂ hQ
  rw [← this]
  exact h₁.1 _ _ H

Depends on / 依赖: algebraMap, e.symm, h.symm.equiv, introv, otimes
-/
lemma CodescendsAlong.mk (h₁ : RespectsIso P)
    (h₂ : forall ⦃R S T⦄ [CommRing R] [CommRing S] [CommRing T],
      forall [Algebra R S] [Algebra R T],
        Q (algebraMap R S) -> P (algebraMap S (S otimes[R] T)) -> P (algebraMap R T)) :
    CodescendsAlong P Q := by
  introv R h hQ H
  let e := h.symm.equiv
  have : (e.symm : _ ->+* _).comp (algebraMap R' S') = algebraMap R' (R' otimes[R] S) := by
    ext r
    simp [e]
  apply h₂ hQ
  rw [← this]
  exact h₁.1 _ _ H

/--
lemma `CodescendsAlong.algebraMap_tensorProduct` / 引理 `CodescendsAlong.algebraMap_tensorProduct`

English:
lemma CodescendsAlong.algebraMap_tensorProduct
  statement: (hPQ : CodescendsAlong P Q)
  proof: let _ : Algebra T (S otimes[R] T) := Algebra.TensorProduct.rightAlgebra
  hPQ h H

中文:
引理 余descendsAlong.algebraMap_tensorProduct
  结论: (hPQ : 余descendsAlong P Q)
  证明: let _ : Algebra T (S otimes[R] T) := Algebra.TensorProduct.rightAlgebra
  hPQ h H

Depends on / 依赖: Algebra, Algebra.TensorProduct.rightAlgebra, TensorProduct, otimes, rightAlgebra
-/
lemma CodescendsAlong.algebraMap_tensorProduct (hPQ : CodescendsAlong P Q)
    (h : Q (algebraMap R S)) (H : P (algebraMap S (S otimes[R] T))) :
    P (algebraMap R T) :=
  let _ : Algebra T (S otimes[R] T) := Algebra.TensorProduct.rightAlgebra
  hPQ h H

/--
lemma `CodescendsAlong.includeRight` / 引理 `CodescendsAlong.includeRight`

English:
lemma CodescendsAlong.includeRight
  statement: (hPQ : CodescendsAlong P Q) (h : Q (algebraMap R T))
  proof: by
  let _ : Algebra T (S otimes[R] T) := Algebra.TensorProduct.rightAlgebra
  apply hPQ h H

中文:
引理 余descendsAlong.includeRight
  结论: (hPQ : 余descendsAlong P Q) (h : Q (algebraMap R T))
  证明: by
  let _ : Algebra T (S otimes[R] T) := Algebra.TensorProduct.rightAlgebra
  apply hPQ h H

Depends on / 依赖: Algebra, Algebra.TensorProduct.rightAlgebra, TensorProduct, otimes, rightAlgebra
-/
lemma CodescendsAlong.includeRight (hPQ : CodescendsAlong P Q) (h : Q (algebraMap R T))
    (H : P ((Algebra.TensorProduct.includeRight.toRingHom : T ->+* S otimes[R] T))) :
    P (algebraMap R S) := by
  let _ : Algebra T (S otimes[R] T) := Algebra.TensorProduct.rightAlgebra
  apply hPQ h H

variable {Q} {P' : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> Prop}

/--
lemma `CodescendsAlong.and` / 引理 `CodescendsAlong.and`

English:
lemma CodescendsAlong.and
  given: (hP : CodescendsAlong P Q) (hP' : CodescendsAlong P' Q)
  proof: fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ => ⟨hP h₁ h₂.1, hP' h₁ h₂.2⟩

中文:
引理 余descendsAlong.and
  条件: (hP : 余descendsAlong P Q) (hP' : 余descendsAlong P' Q)
  证明: fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ => ⟨hP h₁ h₂.1, hP' h₁ h₂.2⟩
-/
lemma CodescendsAlong.and (hP : CodescendsAlong P Q) (hP' : CodescendsAlong P' Q) :
    CodescendsAlong (fun f => P f ∧ P' f) Q :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ => ⟨hP h₁ h₂.1, hP' h₁ h₂.2⟩

end Descent

/--
Definition of `HasEqualizers` / `HasEqualizers` 的定义

English:
definition HasEqualizers
  signature: (P : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> Prop)
  body: forall {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f g : S ->ₐ[R] T), P (algebraMap R S) -> P (algebraMap R T) ->
      P (algebraMap R (AlgHom.equalizer f g))

中文:
定义 HasEqualizers
  签名: (P : 对任意 {R S : 类型u} [交换环 R] [交换环 S], (R ->+* S) -> 命题)
  定义体: forall {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f g : S ->ₐ[R] T), P (algebraMap R S) -> P (algebraMap R T) ->
      P (algebraMap R (AlgHom.equalizer f g))

Depends on / 依赖: AlgHom, AlgHom.equalizer, Algebra, CommRing, algebraMap, equalizer
-/
def HasEqualizers (P : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> Prop) : Prop :=
  forall {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f g : S ->ₐ[R] T), P (algebraMap R S) -> P (algebraMap R T) ->
      P (algebraMap R (AlgHom.equalizer f g))

/--
lemma `HasEqualizers.and` / 引理 `HasEqualizers.and`

English:
lemma HasEqualizers.and
  given: (hP : HasEqualizers P) (hQ : HasEqualizers Q)
  proof: fun f g hf hg => ⟨hP f g hf.1 hg.1, hQ f g hf.2 hg.2⟩

中文:
引理 HasEqualizers.and
  条件: (hP : HasEqualizers P) (hQ : HasEqualizers Q)
  证明: fun f g hf hg => ⟨hP f g hf.1 hg.1, hQ f g hf.2 hg.2⟩
-/
lemma HasEqualizers.and (hP : HasEqualizers P) (hQ : HasEqualizers Q) :
    HasEqualizers (fun f => P f ∧ Q f) :=
  fun f g hf hg => ⟨hP f g hf.1 hg.1, hQ f g hf.2 hg.2⟩

/--
Definition of `HasFiniteProducts` / `HasFiniteProducts` 的定义

English:
definition HasFiniteProducts
  signature: (P : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> Prop)
  body: forall {R : Type u} [CommRing R] {ι : Type u} [_root_.Finite ι] (S : ι -> Type u) [forall i, CommRing (S i)]
    [forall i, Algebra R (S i)],
    (forall i, P (algebraMap R (S i))) -> P (algebraMap R (Π i, S i))

中文:
定义 有FiniteProducts
  签名: (P : 对任意 {R S : 类型u} [交换环 R] [交换环 S], (R ->+* S) -> 命题)
  定义体: forall {R : Type u} [CommRing R] {ι : Type u} [_root_.Finite ι] (S : ι -> Type u) [forall i, CommRing (S i)]
    [forall i, Algebra R (S i)],
    (forall i, P (algebraMap R (S i))) -> P (algebraMap R (Π i, S i))

Depends on / 依赖: Algebra, CommRing, Finite, _root_, _root_.Finite, algebraMap
-/
def HasFiniteProducts (P : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> Prop) : Prop :=
  forall {R : Type u} [CommRing R] {ι : Type u} [_root_.Finite ι] (S : ι -> Type u) [forall i, CommRing (S i)]
    [forall i, Algebra R (S i)],
    (forall i, P (algebraMap R (S i))) -> P (algebraMap R (Π i, S i))

/--
lemma `HasFiniteProducts.and` / 引理 `HasFiniteProducts.and`

English:
lemma HasFiniteProducts.and
  given: (hP : HasFiniteProducts P) (hQ : HasFiniteProducts Q)
  proof: fun _ _ _ hS => ⟨hP _ fun i => (hS i).1, hQ _ fun i => (hS i).2⟩

中文:
引理 有FiniteProducts.and
  条件: (hP : 有FiniteProducts P) (hQ : 有FiniteProducts Q)
  证明: fun _ _ _ hS => ⟨hP _ fun i => (hS i).1, hQ _ fun i => (hS i).2⟩
-/
lemma HasFiniteProducts.and (hP : HasFiniteProducts P) (hQ : HasFiniteProducts Q) :
    HasFiniteProducts (fun f => P f ∧ Q f) :=
  fun _ _ _ hS => ⟨hP _ fun i => (hS i).1, hQ _ fun i => (hS i).2⟩

end RingHom
