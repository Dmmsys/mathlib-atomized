/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.BifibrantObjectHomotopy

/-!
# The fundamental lemma of homotopical algebra

Let `C` be a model category. Let `L : C ⥤ H` be a localization functor
with respect to weak equivalences in `C`. We obtain the fundamental
lemma of homotopical algebra: if `X` is cofibrant and `Y` fibrant,
the map `(X ⟶ Y) → (L.obj X ⟶ L.obj Y)` identifies `L.obj X ⟶ L.obj Y`
to the quotient of `X ⟶ Y` by the homotopy relation (in this case,
the left and right homotopy relations coincide).

## References
* [Daniel G. Quillen, Homotopical algebra, I.1][Quillen1967]

-/

@[expose] public section

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type*} [Category* C] [ModelCategory C] {H : Type*} [Category* H]
  (L : C ⥤ H) [L.IsLocalization (weakEquivalences _)]
  {X Y : C}

/--
Definition of `leftHomotopyClassToHom` / `leftHomotopyClassToHom` 的定义

English:
definition leftHomotopyClassToHom
  signature: : LeftHomotopyClass X Y -> (L.obj X ⟶ L.obj Y)
  body: Quot.lift L.map (fun _ _ h => h.factorsThroughLocalization.map_eq _)

@[simp]

中文:
定义 leftHomotopyClassToHom
  签名: : LeftHomotopyClass X Y -> (L.obj X ⟶ L.obj Y)
  定义体: Quot.lift L.map (fun _ _ h => h.factorsThroughLocalization.map_eq _)

@[simp]

Depends on / 依赖: L.map, Quot.lift, factorsThroughLocalization, h.factorsThroughLocalization.map_eq, map_eq
-/
def leftHomotopyClassToHom : LeftHomotopyClass X Y -> (L.obj X ⟶ L.obj Y) :=
  Quot.lift L.map (fun _ _ h => h.factorsThroughLocalization.map_eq _)

@[simp]
/--
lemma `leftHomotopyClassToHom_mk` / 引理 `leftHomotopyClassToHom_mk`

English:
lemma leftHomotopyClassToHom_mk
  given: (f : X ⟶ Y)
  proof: rfl

中文:
引理 leftHomotopyClassToHom_mk
  条件: (f : X ⟶ Y)
  证明: rfl
-/
lemma leftHomotopyClassToHom_mk (f : X ⟶ Y) :
    leftHomotopyClassToHom L (.mk f) = L.map f := rfl

/--
Definition of `rightHomotopyClassToHom` / `rightHomotopyClassToHom` 的定义

English:
definition rightHomotopyClassToHom
  signature: : RightHomotopyClass X Y -> (L.obj X ⟶ L.obj Y)
  body: Quot.lift L.map (fun _ _ h => h.factorsThroughLocalization.map_eq _)

@[simp]

中文:
定义 rightHomotopyClassToHom
  签名: : RightHomotopyClass X Y -> (L.obj X ⟶ L.obj Y)
  定义体: Quot.lift L.map (fun _ _ h => h.factorsThroughLocalization.map_eq _)

@[simp]

Depends on / 依赖: L.map, Quot.lift, factorsThroughLocalization, h.factorsThroughLocalization.map_eq, map_eq
-/
def rightHomotopyClassToHom : RightHomotopyClass X Y -> (L.obj X ⟶ L.obj Y) :=
  Quot.lift L.map (fun _ _ h => h.factorsThroughLocalization.map_eq _)

@[simp]
/--
lemma `rightHomotopyClassToHom_mk` / 引理 `rightHomotopyClassToHom_mk`

English:
lemma rightHomotopyClassToHom_mk
  given: (f : X ⟶ Y)
  proof: rfl

中文:
引理 rightHomotopyClassToHom_mk
  条件: (f : X ⟶ Y)
  证明: rfl
-/
lemma rightHomotopyClassToHom_mk (f : X ⟶ Y) :
    rightHomotopyClassToHom L (.mk f) = L.map f := rfl

variable (X Y)
/--
lemma `bijective_leftHomotopyClassToHom_iff_bijective_rightHomotopyClassToHom` / 引理 `bijective_leftHomotopyClassToHom_iff_bijective_rightHomotopyClassToHom`

English:
lemma bijective_leftHomotopyClassToHom_iff_bijective_rightHomotopyClassToHom
  proof: by
  have : (leftHomotopyClassToHom L : LeftHomotopyClass X Y -> _) =
      rightHomotopyClassToHom L ∘ leftHomotopyClassEquivRightHomotopyClass := by
    ext f
    obtain ⟨f, rfl⟩ := f.mk_surjective
    simp
  simp [this]

中文:
引理 bijective_leftHomotopyClassToHom_iff_bijective_rightHomotopyClassToHom
  证明: by
  have : (leftHomotopyClassToHom L : LeftHomotopyClass X Y -> _) =
      rightHomotopyClassToHom L ∘ leftHomotopyClassEquivRightHomotopyClass := by
    ext f
    obtain ⟨f, rfl⟩ := f.mk_surjective
    simp
  simp [this]

Depends on / 依赖: LeftHomotopyClass, f.mk_surjective, leftHomotopyClassEquivRightHomotopyClass, leftHomotopyClassToHom, mk_surjective, rightHomotopyClassToHom
-/
lemma bijective_leftHomotopyClassToHom_iff_bijective_rightHomotopyClassToHom
    [IsCofibrant X] [IsFibrant Y] :
    Function.Bijective (leftHomotopyClassToHom L : LeftHomotopyClass X Y -> _) ↔
    Function.Bijective (rightHomotopyClassToHom L : RightHomotopyClass X Y -> _) := by
  have : (leftHomotopyClassToHom L : LeftHomotopyClass X Y -> _) =
      rightHomotopyClassToHom L ∘ leftHomotopyClassEquivRightHomotopyClass := by
    ext f
    obtain ⟨f, rfl⟩ := f.mk_surjective
    simp
  simp [this]

section

variable [IsCofibrant X] [IsFibrant Y]

/--
lemma `bijective_rightHomotopyClassToHom` / 引理 `bijective_rightHomotopyClassToHom`

English:
lemma bijective_rightHomotopyClassToHom
  proof: by
  wlog _ : IsCofibrant Y generalizing Y
  · obtain ⟨Y', _, p, _, _⟩ := CofibrantObject.HoCat.exists_resolution Y
    have _ : IsFibrant Y' := isFibrant_of_fibration p
    have hY' := this Y' inferInstance
    simp only [← bijective_leftHomotopyClassToHom_iff_bijective_rightHomotopyClassToHom] at 

中文:
引理 bijective_rightHomotopyClassToHom
  证明: by
  wlog _ : IsCofibrant Y generalizing Y
  · obtain ⟨Y', _, p, _, _⟩ := CofibrantObject.HoCat.exists_resolution Y
    have _ : IsFibrant Y' := isFibrant_of_fibration p
    have hY' := this Y' inferInstance
    simp only [← bijective_leftHomotopyClassToHom_iff_bijective_rightHomotopyClassToHom] at 

Depends on / 依赖: Bijective, CofibrantObject, CofibrantObject.HoCat.exists_resolution, Function, Function.Bijective.of_comp_iff, IsCofibrant, IsFibrant, LeftHomotopyClass, LeftHomotopyClass.postcomp_bijective_of_fibration_of_weakEquivalence, Localization, Localization.inverts, bijective_leftHomotopyClassToHom_iff_bijective_rightHomotopyClassToHom, convert, exists_resolution, generalizing, inverts, isFibrant_of_fibration, of_comp_iff, postcomp_bijective_of_fibration_of_weakEquivalence, weakEquivalence_iff
-/
lemma bijective_rightHomotopyClassToHom :
    Function.Bijective (rightHomotopyClassToHom L : RightHomotopyClass X Y -> _) := by
  wlog _ : IsCofibrant Y generalizing Y
  · obtain ⟨Y', _, p, _, _⟩ := CofibrantObject.HoCat.exists_resolution Y
    have _ : IsFibrant Y' := isFibrant_of_fibration p
    have hY' := this Y' inferInstance
    simp only [← bijective_leftHomotopyClassToHom_iff_bijective_rightHomotopyClassToHom] at hY' ⊢
    have := Localization.inverts L (weakEquivalences _) p
      (by rwa [← weakEquivalence_iff])
    rw [← Function.Bijective.of_comp_iff _
      (LeftHomotopyClass.postcomp_bijective_of_fibration_of_weakEquivalence _ p)]
    convert! (Iso.homCongr (Iso.refl (L.obj X)) (asIso (L.map p))).bijective.comp hY'
    ext f
    obtain ⟨f, rfl⟩ := f.mk_surjective
    simp
  wlog _ : IsFibrant X generalizing X
  · obtain ⟨X', i, _, _, _⟩ : exists (X' : C) (i : X ⟶ X'), Cofibration i ∧ WeakEquivalence i ∧
        IsFibrant X' :=
      ⟨_, FibrantObject.HoCat.iResolutionObj X, inferInstance, inferInstance, inferInstance⟩
    have _ := isCofibrant_of_cofibration i
    have hX' := this X' inferInstance
    have := Localization.inverts L (weakEquivalences _) i
      (by rwa [← weakEquivalence_iff])
    rw [← Function.Bijective.of_comp_iff _
      (RightHomotopyClass.precomp_bijective_of_cofibration_of_weakEquivalence Y i)]
    convert! (Iso.homCongr (asIso (L.map i)) (Iso.refl (L.obj Y))).symm.bijective.comp hX'
    ext f
    obtain ⟨f, rfl⟩ := f.mk_surjective
    simp
  let E := Localization.uniq BifibrantObject.toHoCat (BifibrantObject.ι ⋙ L) (weakEquivalences _)
  let e : BifibrantObject.toHoCat ⋙ E.functor ≅ BifibrantObject.ι ⋙ L :=
    Localization.compUniqFunctor BifibrantObject.toHoCat (BifibrantObject.ι ⋙ L)
      (weakEquivalences _)
  have : rightHomotopyClassToHom L =
      (BifibrantObject.HoCat.homEquivRight.trans (E.fullyFaithfulFunctor.homEquiv.trans
        (Iso.homCongr (e.app (.mk X)) (e.app (.mk Y))))) := by
    ext f
    obtain ⟨f, rfl⟩ := RightHomotopyClass.mk_surjective f
    exact (NatIso.naturality_1 e (BifibrantObject.homMk f)).symm
  rw [this]
  exact Equiv.bijective _

/--
lemma `bijective_leftHomotopyClassToHom` / 引理 `bijective_leftHomotopyClassToHom`

English:
lemma bijective_leftHomotopyClassToHom
  proof: by
  rw [bijective_leftHomotopyClassToHom_iff_bijective_rightHomotopyClassToHom]
  exact bijective_rightHomotopyClassToHom L X Y

中文:
引理 bijective_leftHomotopyClassToHom
  证明: by
  rw [bijective_leftHomotopyClassToHom_iff_bijective_rightHomotopyClassToHom]
  exact bijective_rightHomotopyClassToHom L X Y

Depends on / 依赖: bijective_leftHomotopyClassToHom_iff_bijective_rightHomotopyClassToHom, bijective_rightHomotopyClassToHom
-/
lemma bijective_leftHomotopyClassToHom :
    Function.Bijective (leftHomotopyClassToHom L : LeftHomotopyClass X Y -> _) := by
  rw [bijective_leftHomotopyClassToHom_iff_bijective_rightHomotopyClassToHom]
  exact bijective_rightHomotopyClassToHom L X Y

/--
lemma `map_surjective_of_isLocalization` / 引理 `map_surjective_of_isLocalization`

English:
lemma map_surjective_of_isLocalization
  proof: by
  intro f
  obtain ⟨⟨f⟩, rfl⟩ := (bijective_leftHomotopyClassToHom L X Y).2 f
  exact ⟨f, rfl⟩

中文:
引理 map_surjective_of_isLocalization
  证明: by
  intro f
  obtain ⟨⟨f⟩, rfl⟩ := (bijective_leftHomotopyClassToHom L X Y).2 f
  exact ⟨f, rfl⟩

Depends on / 依赖: bijective_leftHomotopyClassToHom
-/
lemma map_surjective_of_isLocalization :
    Function.Surjective (L.map : (X ⟶ Y) -> _) := by
  intro f
  obtain ⟨⟨f⟩, rfl⟩ := (bijective_leftHomotopyClassToHom L X Y).2 f
  exact ⟨f, rfl⟩

/--
lemma `RightHomotopyRel.iff_map_eq` / 引理 `RightHomotopyRel.iff_map_eq`

English:
lemma RightHomotopyRel.iff_map_eq
  given: {f g : X ⟶ Y}
  proof: by
  refine ⟨fun h => (RightHomotopyRel.factorsThroughLocalization C h).map_eq L,
    fun h => ?_⟩
  rw [← RightHomotopyClass.mk_eq_mk_iff]
  exact (bijective_rightHomotopyClassToHom L X Y).1 (by simpa)

中文:
引理 RightHomotopyRel.iff_map_eq
  条件: {f g : X ⟶ Y}
  证明: by
  refine ⟨fun h => (RightHomotopyRel.factorsThroughLocalization C h).map_eq L,
    fun h => ?_⟩
  rw [← RightHomotopyClass.mk_eq_mk_iff]
  exact (bijective_rightHomotopyClassToHom L X Y).1 (by simpa)

Depends on / 依赖: RightHomotopyClass, RightHomotopyClass.mk_eq_mk_iff, RightHomotopyRel, RightHomotopyRel.factorsThroughLocalization, bijective_rightHomotopyClassToHom, factorsThroughLocalization, map_eq, mk_eq_mk_iff
-/
lemma RightHomotopyRel.iff_map_eq {f g : X ⟶ Y} :
    RightHomotopyRel f g ↔ L.map f = L.map g := by
  refine ⟨fun h => (RightHomotopyRel.factorsThroughLocalization C h).map_eq L,
    fun h => ?_⟩
  rw [← RightHomotopyClass.mk_eq_mk_iff]
  exact (bijective_rightHomotopyClassToHom L X Y).1 (by simpa)

/--
lemma `LeftHomotopyRel.iff_map_eq` / 引理 `LeftHomotopyRel.iff_map_eq`

English:
lemma LeftHomotopyRel.iff_map_eq
  given: {f g : X ⟶ Y}
  proof: by
  refine ⟨fun h => (LeftHomotopyRel.factorsThroughLocalization C h).map_eq L,
    fun h => ?_⟩
  rw [← LeftHomotopyClass.mk_eq_mk_iff]
  exact (bijective_leftHomotopyClassToHom L X Y).1 (by simpa)

中文:
引理 LeftHomotopyRel.iff_map_eq
  条件: {f g : X ⟶ Y}
  证明: by
  refine ⟨fun h => (LeftHomotopyRel.factorsThroughLocalization C h).map_eq L,
    fun h => ?_⟩
  rw [← LeftHomotopyClass.mk_eq_mk_iff]
  exact (bijective_leftHomotopyClassToHom L X Y).1 (by simpa)

Depends on / 依赖: LeftHomotopyClass, LeftHomotopyClass.mk_eq_mk_iff, LeftHomotopyRel, LeftHomotopyRel.factorsThroughLocalization, bijective_leftHomotopyClassToHom, factorsThroughLocalization, map_eq, mk_eq_mk_iff
-/
lemma LeftHomotopyRel.iff_map_eq {f g : X ⟶ Y} :
    LeftHomotopyRel f g ↔ L.map f = L.map g := by
  refine ⟨fun h => (LeftHomotopyRel.factorsThroughLocalization C h).map_eq L,
    fun h => ?_⟩
  rw [← LeftHomotopyClass.mk_eq_mk_iff]
  exact (bijective_leftHomotopyClassToHom L X Y).1 (by simpa)

end

end HomotopicalAlgebra
