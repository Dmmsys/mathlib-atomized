/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Nikolas Kuhn
-/
module

public import Mathlib.CategoryTheory.Sites.Coherent.CoherentSheaves
public import Mathlib.Data.Finite.Sigma

/-!
# Description of the covering sieves of the coherent topology

This file characterises the covering sieves of the coherent topology.

## Main result

* `coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily`: a sieve is a covering sieve for the
  coherent topology if and only if it contains a finite effective epimorphic family.

-/

public section

namespace CategoryTheory

variable {C : Type*} [Category* C] [Precoherent C] {X : C}

/--
theorem `coherentTopology.mem_sieves_of_hasEffectiveEpiFamily` / 定理 `coherentTopology.mem_sieves_of_hasEffectiveEpiFamily`

English:
theorem coherentTopology.mem_sieves_of_hasEffectiveEpiFamily
  given: (S : Sieve X)
  proof: by
  intro ⟨α, _, Y, π, hπ⟩
  apply (coherentCoverage C).mem_toGrothendieck_sieves_of_superset (R := Presieve.ofArrows Y π)
  · exact fun _ _ h => by cases h; exact hπ.2 _
  · exact ⟨_, inferInstance, Y, π, rfl, hπ.1⟩

中文:
定理 coherentTopology.mem_sieves_of_hasEffectiveEpiFamily
  条件: (S : Sieve X)
  证明: by
  intro ⟨α, _, Y, π, hπ⟩
  apply (coherentCoverage C).mem_toGrothendieck_sieves_of_superset (R := Presieve.ofArrows Y π)
  · exact fun _ _ h => by cases h; exact hπ.2 _
  · exact ⟨_, inferInstance, Y, π, rfl, hπ.1⟩

Depends on / 依赖: Presieve, Presieve.ofArrows, coherentCoverage, mem_toGrothendieck_sieves_of_superset, ofArrows
-/
theorem coherentTopology.mem_sieves_of_hasEffectiveEpiFamily (S : Sieve X) :
    (exists (α : Type) (_ : Finite α) (Y : α -> C) (π : (a : α) -> (Y a ⟶ X)),
      EffectiveEpiFamily Y π ∧ (forall a : α, (S.arrows) (π a))) ->
        (S in (coherentTopology C) X) := by
  intro ⟨α, _, Y, π, hπ⟩
  apply (coherentCoverage C).mem_toGrothendieck_sieves_of_superset (R := Presieve.ofArrows Y π)
  · exact fun _ _ h => by cases h; exact hπ.2 _
  · exact ⟨_, inferInstance, Y, π, rfl, hπ.1⟩

/--
theorem `EffectiveEpiFamily.transitive_of_finite` / 定理 `EffectiveEpiFamily.transitive_of_finite`

English:
theorem EffectiveEpiFamily.transitive_of_finite
  statement: {α : Type} [Finite α] {Y : α -> C}
  proof: by
  rw [← Sieve.effectiveEpimorphic_family]
  suffices h₂ : (Sieve.generate (Presieve.ofArrows (fun (⟨a, b⟩ : Σ _, β _) => Y_n a b)
        (fun ⟨a,b⟩ => π_n a b ≫ π a))) in (coherentTopology C) X by
    change Nonempty _
    rw [← Sieve.forallYonedaIsSheaf_iff_colimit]
    exact fun W => coherentT

中文:
定理 EffectiveEpiFamily.transitive_of_finite
  结论: {α : Type} [Finite α] {Y : α -> C}
  证明: by
  rw [← Sieve.effectiveEpimorphic_family]
  suffices h₂ : (Sieve.generate (Presieve.ofArrows (fun (⟨a, b⟩ : Σ _, β _) => Y_n a b)
        (fun ⟨a,b⟩ => π_n a b ≫ π a))) in (coherentTopology C) X by
    change Nonempty _
    rw [← Sieve.forallYonedaIsSheaf_iff_colimit]
    exact fun W => coherentT

Depends on / 依赖: Nonempty, Presieve, Presieve.ofArrows, Sieve.effectiveEpimorphic_family, Sieve.forallYonedaIsSheaf_iff_colimit, Sieve.generate, coherentTopology, coherentTopology.isSheaf_yoneda_obj, effectiveEpimorphic_family, forallYonedaIsSheaf_iff_colimit, generate, isSheaf_yoneda_obj, ofArrows
-/
theorem EffectiveEpiFamily.transitive_of_finite {α : Type} [Finite α] {Y : α -> C}
    (π : (a : α) -> (Y a ⟶ X)) (h : EffectiveEpiFamily Y π) {β : α -> Type} [forall (a : α), Finite (β a)]
    {Y_n : (a : α) -> β a -> C} (π_n : (a : α) -> (b : β a) -> (Y_n a b ⟶ Y a))
    (H : forall a, EffectiveEpiFamily (Y_n a) (π_n a)) :
    EffectiveEpiFamily
      (fun (c : Σ a, β a) => Y_n c.fst c.snd) (fun c => π_n c.fst c.snd ≫ π c.fst) := by
  rw [← Sieve.effectiveEpimorphic_family]
  suffices h₂ : (Sieve.generate (Presieve.ofArrows (fun (⟨a, b⟩ : Σ _, β _) => Y_n a b)
        (fun ⟨a,b⟩ => π_n a b ≫ π a))) in (coherentTopology C) X by
    change Nonempty _
    rw [← Sieve.forallYonedaIsSheaf_iff_colimit]
    exact fun W => coherentTopology.isSheaf_yoneda_obj W _ h₂
  -- Show that a covering sieve is a colimit, which implies the original set of arrows is regular
  -- epimorphic. We use the transitivity property of saturation
  apply Coverage.Saturate.transitive X (Sieve.generate (Presieve.ofArrows Y π))
  · apply Coverage.Saturate.of
    use α, inferInstance, Y, π
  · intro V f ⟨Y₁, h, g, ⟨hY, hf⟩⟩
    rw [← hf]; rw [Sieve.pullback_comp]
    apply (coherentTopology C).pullback_stable'
    apply coherentTopology.mem_sieves_of_hasEffectiveEpiFamily
    -- Need to show that the pullback of the family `π_n` to a given `Y i` is effective epimorphic
    obtain ⟨i⟩ := hY
    exact ⟨β i, inferInstance, Y_n i, π_n i, H i, fun b =>
      ⟨Y_n i b, (𝟙 _), π_n i b ≫ π i, ⟨(⟨i, b⟩ : Σ (i : α), β i)⟩, by simp⟩⟩

/--
Instance `precoherentEffectiveEpiFamilyCompEffectiveEpis` / 实例 `precoherentEffectiveEpiFamilyCompEffectiveEpis`

English:
instance precoherentEffectiveEpiFamilyCompEffectiveEpis
  body: by
  simp_rw [effectiveEpi_iff_effectiveEpiFamily] at h
  exact EffectiveEpiFamily.reindex (e := Equiv.sigmaPUnit α) _ _
    (EffectiveEpiFamily.transitive_of_finite (β := fun _ => Unit) _ inferInstance _ h)

中文:
实例 precoherentEffectiveEpiFamilyCompEffectiveEpis
  定义体: by
  simp_rw [effectiveEpi_iff_effectiveEpiFamily] at h
  exact EffectiveEpiFamily.reindex (e := Equiv.sigmaPUnit α) _ _
    (EffectiveEpiFamily.transitive_of_finite (β := fun _ => Unit) _ inferInstance _ h)

Depends on / 依赖: EffectiveEpiFamily, EffectiveEpiFamily.reindex, EffectiveEpiFamily.transitive_of_finite, Equiv.sigmaPUnit, effectiveEpi_iff_effectiveEpiFamily, reindex, sigmaPUnit, simp_rw, transitive_of_finite
-/
instance precoherentEffectiveEpiFamilyCompEffectiveEpis
    {α : Type} [Finite α] {Y Z : α -> C} (π : (a : α) -> (Y a ⟶ X)) [EffectiveEpiFamily Y π]
    (f : (a : α) -> Z a ⟶ Y a) [h : forall a, EffectiveEpi (f a)] :
    EffectiveEpiFamily _ fun a => f a ≫ π a := by
  simp_rw [effectiveEpi_iff_effectiveEpiFamily] at h
  exact EffectiveEpiFamily.reindex (e := Equiv.sigmaPUnit α) _ _
    (EffectiveEpiFamily.transitive_of_finite (β := fun _ => Unit) _ inferInstance _ h)

/--
theorem `coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily` / 定理 `coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily`

English:
theorem coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily
  given: (S : Sieve X)
  proof: by
  constructor
  · intro h
    induction h with
    | of Y T hS =>
      obtain ⟨a, h, Y', π, h', _⟩ := hS
      refine ⟨a, h, Y', π, inferInstance, fun a' => ?_⟩
      obtain ⟨rfl, _⟩ := h'
      exact ⟨Y' a', 𝟙 Y' a', π a', Presieve.ofArrows.mk a', by simp⟩
    | top Y =>
      exact ⟨Unit, infe

中文:
定理 coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily
  条件: (S : Sieve X)
  证明: by
  constructor
  · intro h
    induction h with
    | of Y T hS =>
      obtain ⟨a, h, Y', π, h', _⟩ := hS
      refine ⟨a, h, Y', π, inferInstance, fun a' => ?_⟩
      obtain ⟨rfl, _⟩ := h'
      exact ⟨Y' a', 𝟙 Y' a', π a', Presieve.ofArrows.mk a', by simp⟩
    | top Y =>
      exact ⟨Unit, infe

Depends on / 依赖: Presieve, Presieve.ofArrows.mk, ofArrows, transitive
-/
theorem coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily (S : Sieve X) :
    (S in (coherentTopology C) X) ↔
    (exists (α : Type) (_ : Finite α) (Y : α -> C) (π : (a : α) -> (Y a ⟶ X)),
        EffectiveEpiFamily Y π ∧ (forall a : α, (S.arrows) (π a))) := by
  constructor
  · intro h
    induction h with
    | of Y T hS =>
      obtain ⟨a, h, Y', π, h', _⟩ := hS
      refine ⟨a, h, Y', π, inferInstance, fun a' => ?_⟩
      obtain ⟨rfl, _⟩ := h'
      exact ⟨Y' a', 𝟙 Y' a', π a', Presieve.ofArrows.mk a', by simp⟩
    | top Y =>
      exact ⟨Unit, inferInstance, fun _ => Y, fun _ => (𝟙 Y), inferInstance, by simp⟩
    | transitive Y R S _ _ a b =>
      obtain ⟨α, w, Y₁, π, ⟨h₁, h₂⟩⟩ := a
      choose β _ Y_n π_n H using fun a => b (h₂ a)
      exact ⟨(Σ a, β a), inferInstance, fun ⟨a,b⟩ => Y_n a b, fun ⟨a, b⟩ => (π_n a b) ≫ (π a),
        EffectiveEpiFamily.transitive_of_finite _ h₁ _ (fun a => (H a).1),
        fun c => (H c.fst).2 c.snd⟩
  · exact coherentTopology.mem_sieves_of_hasEffectiveEpiFamily S

end CategoryTheory
