/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.CoverPreserving

/-!
# Induced topologies

In this file we study various topologies induced by a functor. Let `F : C ⥤ D` be a functor,
`J` a Grothendieck topology on `C` and `K` a Grothendieck topology on `D`.

- `CategoryTheory.Functor.inducedTopology F K`: The finest topology on `C` making `F` continuous.
- `CategoryTheory.Functor.restrictedTopology F K`: The coarsest topology on `C` containing
  all sieves whose image generate a covering sieve of `K`. In general, this does not make `F` cover
  preserving.

## TODOs

- Define the finest topology on the codomain making a functor cocontinuous
  (@chrisflav).

## References

- [SGA4, III, 3][sga-4-tome-1]
-/

@[expose] public section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

variable {F : C ⥤ D} {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace Functor

/--
Definition of `inducedTopology` / `inducedTopology` 的定义

English:
definition inducedTopology
  signature: (F : C ⥤ D) (K : GrothendieckTopology D)
  body: Sheaf.finestTopology Set.range fun G : Sheaf K (Type max u₁ v₁ u₂ v₂) => F.op ⋙ G.obj

中文:
定义 inducedTopology
  签名: (F : C ⥤ D) (K : GrothendieckTopology D)
  定义体: Sheaf.finestTopology Set.range fun G : Sheaf K (Type max u₁ v₁ u₂ v₂) => F.op ⋙ G.obj

Depends on / 依赖: F.op, G.obj, Set.range, Sheaf.finestTopology, finestTopology
-/
def inducedTopology (F : C ⥤ D) (K : GrothendieckTopology D) :
    GrothendieckTopology C :=
Sheaf.finestTopology Set.range fun G : Sheaf K (Type max u₁ v₁ u₂ v₂) => F.op ⋙ G.obj

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: F.IsContinuous (F.inducedTopology K) K
  body: by
    apply Sheaf.sheaf_for_finestTopology
    use G

@[simp]

中文:
实例 :
  签名: F.IsContinuous (F.inducedTopology K) K
  定义体: by
    apply Sheaf.sheaf_for_finestTopology
    use G

@[simp]

Depends on / 依赖: Sheaf.sheaf_for_finestTopology, sheaf_for_finestTopology
-/
instance : F.IsContinuous (F.inducedTopology K) K where
  op_comp_isSheaf_of_types G := by
    apply Sheaf.sheaf_for_finestTopology
    use G

@[simp]
/--
lemma `le_inducedTopology_iff` / 引理 `le_inducedTopology_iff`

English:
lemma le_inducedTopology_iff
  given: {J : GrothendieckTopology C}
  proof: by
  refine ⟨fun h => ⟨fun G => ?_⟩, fun h => ?_⟩
  · apply Presieve.isSheaf_of_le _ h
    exact Functor.op_comp_isSheaf_of_types F (F.inducedTopology K) K G
  · apply Sheaf.le_finestTopology
    rintro _ ⟨P, rfl⟩
    exact Functor.op_comp_isSheaf_of_types F J K P

中文:
引理 le_inducedTopology_iff
  条件: {J : GrothendieckTopology C}
  证明: by
  refine ⟨fun h => ⟨fun G => ?_⟩, fun h => ?_⟩
  · apply Presieve.isSheaf_of_le _ h
    exact Functor.op_comp_isSheaf_of_types F (F.inducedTopology K) K G
  · apply Sheaf.le_finestTopology
    rintro _ ⟨P, rfl⟩
    exact Functor.op_comp_isSheaf_of_types F J K P

Depends on / 依赖: F.inducedTopology, Functor, Functor.op_comp_isSheaf_of_types, Presieve, Presieve.isSheaf_of_le, Sheaf.le_finestTopology, inducedTopology, isSheaf_of_le, le_finestTopology, op_comp_isSheaf_of_types
-/
lemma le_inducedTopology_iff {J : GrothendieckTopology C} :
    J <= F.inducedTopology K ↔ F.IsContinuous J K := by
  refine ⟨fun h => ⟨fun G => ?_⟩, fun h => ?_⟩
  · apply Presieve.isSheaf_of_le _ h
    exact Functor.op_comp_isSheaf_of_types F (F.inducedTopology K) K G
  · apply Sheaf.le_finestTopology
    rintro _ ⟨P, rfl⟩
    exact Functor.op_comp_isSheaf_of_types F J K P

/--
lemma `mem_inducedTopology_iff` / 引理 `mem_inducedTopology_iff`

English:
lemma mem_inducedTopology_iff
  statement: [LocallySmall.{max u₁ v₁ u₂ v₂} C] (X : C) (S : Sieve X)
  proof: by
  refine ⟨?_, ?_⟩
  · intro hS Y f
    apply Functor.W_map_of_adjunction_of_isContinuous (F.inducedTopology K) K _ G adj
    refine Sieve.W_shrinkFunctor_ι_of_mem (F.inducedTopology K) (Sieve.pullback f S) ?_
    exact GrothendieckTopology.pullback_stable (F.inducedTopology K) f hS
  · intro H
  

中文:
引理 mem_inducedTopology_iff
  结论: [LocallySmall.{max u₁ v₁ u₂ v₂} C] (X : C) (S : Sieve X)
  证明: by
  refine ⟨?_, ?_⟩
  · intro hS Y f
    apply Functor.W_map_of_adjunction_of_isContinuous (F.inducedTopology K) K _ G adj
    refine Sieve.W_shrinkFunctor_ι_of_mem (F.inducedTopology K) (Sieve.pullback f S) ?_
    exact GrothendieckTopology.pullback_stable (F.inducedTopology K) f hS
  · intro H
  

Depends on / 依赖: F.inducedTopology, Functor, Functor.W_map_of_adjunction_of_isContinuous, GrothendieckTopology, GrothendieckTopology.pullback_stable, P.property, Presieve, Presieve.isSheafFor_iff_bijective_shrinkFunctor_, Sheaf.mem_finestTopology_of_forall_isSheafFor, Sieve.W_shrinkFunctor_, Sieve.pullback, W_map_of_adjunction_of_isContinuous, adj.map_comp_bijective_iff, inducedTopology, map_comp_bijective_iff, mem_finestTopology_of_forall_isSheafFor, property, pullback, pullback_stable
-/
lemma mem_inducedTopology_iff [LocallySmall.{max u₁ v₁ u₂ v₂} C] (X : C) (S : Sieve X)
    (G : (Cᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂) ⥤ (Dᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂))
    (adj : G ⊣ (Functor.whiskeringLeft _ _ _).obj F.op) :
    S in F.inducedTopology K X ↔
      forall ⦃Y : C⦄ (f : Y ⟶ X),
        K.W (G.map (Sieve.shrinkFunctor.{max u₁ v₁ u₂ v₂} (S.pullback f)).ι) := by
  refine ⟨?_, ?_⟩
  · intro hS Y f
    apply Functor.W_map_of_adjunction_of_isContinuous (F.inducedTopology K) K _ G adj
    refine Sieve.W_shrinkFunctor_ι_of_mem (F.inducedTopology K) (Sieve.pullback f S) ?_
    exact GrothendieckTopology.pullback_stable (F.inducedTopology K) f hS
  · intro H
    apply Sheaf.mem_finestTopology_of_forall_isSheafFor
    rintro - ⟨P, rfl⟩ Y f
    dsimp
    rw [Presieve.isSheafFor_iff_bijective_shrinkFunctor_ι_comp]
    exact (adj.map_comp_bijective_iff _ _).mp (H f _ P.property)

/--
lemma `induced_induced_le` / 引理 `induced_induced_le`

English:
lemma induced_induced_le
  given: (G : D ⥤ E) (J : GrothendieckTopology E)
  proof: by
  rw [le_inducedTopology_iff]
  exact Functor.isContinuous_comp _ _ _ (G.inducedTopology J) _

中文:
引理 induced_induced_le
  条件: (G : D ⥤ E) (J : GrothendieckTopology E)
  证明: by
  rw [le_inducedTopology_iff]
  exact Functor.isContinuous_comp _ _ _ (G.inducedTopology J) _

Depends on / 依赖: Functor, Functor.isContinuous_comp, G.inducedTopology, inducedTopology, isContinuous_comp, le_inducedTopology_iff
-/
lemma induced_induced_le (G : D ⥤ E) (J : GrothendieckTopology E) :
    F.inducedTopology (G.inducedTopology J) <= (F ⋙ G).inducedTopology J := by
  rw [le_inducedTopology_iff]
  exact Functor.isContinuous_comp _ _ _ (G.inducedTopology J) _

/--
lemma `inducedTopology_eq_of_iso` / 引理 `inducedTopology_eq_of_iso`

English:
lemma inducedTopology_eq_of_iso
  given: {F G : C ⥤ D} (e : F ≅ G)
  proof: by
  refine le_antisymm ?_ ?_ <;> rw [le_inducedTopology_iff]
  · apply Functor.isContinuous_of_iso e
  · apply Functor.isContinuous_of_iso e.symm

中文:
引理 inducedTopology_eq_of_iso
  条件: {F G : C ⥤ D} (e : F ≅ G)
  证明: by
  refine le_antisymm ?_ ?_ <;> rw [le_inducedTopology_iff]
  · apply Functor.isContinuous_of_iso e
  · apply Functor.isContinuous_of_iso e.symm

Depends on / 依赖: Functor, Functor.isContinuous_of_iso, e.symm, isContinuous_of_iso, le_antisymm, le_inducedTopology_iff
-/
lemma inducedTopology_eq_of_iso {F G : C ⥤ D} (e : F ≅ G) :
    F.inducedTopology K = G.inducedTopology K := by
  refine le_antisymm ?_ ?_ <;> rw [le_inducedTopology_iff]
  · apply Functor.isContinuous_of_iso e
  · apply Functor.isContinuous_of_iso e.symm

/--
Definition of `restrictedTopology` / `restrictedTopology` 的定义

English:
definition restrictedTopology
  signature: (F : C ⥤ D) (K : GrothendieckTopology D)
  body: Precoverage.toGrothendieck (Precoverage.comap F K.toPrecoverage)

中文:
定义 restrictedTopology
  签名: (F : C ⥤ D) (K : GrothendieckTopology D)
  定义体: Precoverage.toGrothendieck (Precoverage.comap F K.toPrecoverage)

Depends on / 依赖: K.toPrecoverage, Precoverage, Precoverage.comap, Precoverage.toGrothendieck, toGrothendieck, toPrecoverage
-/
def restrictedTopology (F : C ⥤ D) (K : GrothendieckTopology D) : GrothendieckTopology C :=
  Precoverage.toGrothendieck (Precoverage.comap F K.toPrecoverage)

/--
lemma `mem_restrictedTopology_of_functorPushforward_mem` / 引理 `mem_restrictedTopology_of_functorPushforward_mem`

English:
lemma mem_restrictedTopology_of_functorPushforward_mem
  statement: {X : C} {S : Sieve X}
  proof: by
  rw [← Sieve.generate_sieve S]
  apply Precoverage.generate_mem_toGrothendieck
  simpa [GrothendieckTopology.mem_toPrecoverage_iff, Sieve.generate_map_eq_functorPushforward]

中文:
引理 mem_restrictedTopology_of_functorPushforward_mem
  结论: {X : C} {S : Sieve X}
  证明: by
  rw [← Sieve.generate_sieve S]
  apply Precoverage.generate_mem_toGrothendieck
  simpa [GrothendieckTopology.mem_toPrecoverage_iff, Sieve.generate_map_eq_functorPushforward]

Depends on / 依赖: GrothendieckTopology, GrothendieckTopology.mem_toPrecoverage_iff, Precoverage, Precoverage.generate_mem_toGrothendieck, Sieve.generate_map_eq_functorPushforward, Sieve.generate_sieve, generate_map_eq_functorPushforward, generate_mem_toGrothendieck, generate_sieve, mem_toPrecoverage_iff
-/
lemma mem_restrictedTopology_of_functorPushforward_mem {X : C} {S : Sieve X}
    (hS : S.functorPushforward F in K _) :
    S in F.restrictedTopology K X := by
  rw [← Sieve.generate_sieve S]
  apply Precoverage.generate_mem_toGrothendieck
  simpa [GrothendieckTopology.mem_toPrecoverage_iff, Sieve.generate_map_eq_functorPushforward]

/--
lemma `inducedTopology_le_restrictedTopology` / 引理 `inducedTopology_le_restrictedTopology`

English:
lemma inducedTopology_le_restrictedTopology
  statement: F.inducedTopology K <= F.restrictedTopology K
  proof: fun _ _ hS => mem_restrictedTopology_of_functorPushforward_mem
    (CoverPreserving.of_isContinuous F _ _).cover_preserve hS

中文:
引理 inducedTopology_le_restrictedTopology
  结论: F.inducedTopology K <= F.restrictedTopology K
  证明: fun _ _ hS => mem_restrictedTopology_of_functorPushforward_mem
    (CoverPreserving.of_isContinuous F _ _).cover_preserve hS

Depends on / 依赖: CoverPreserving, CoverPreserving.of_isContinuous, cover_preserve, mem_restrictedTopology_of_functorPushforward_mem, of_isContinuous
-/
lemma inducedTopology_le_restrictedTopology : F.inducedTopology K <= F.restrictedTopology K :=
fun _ _ hS => mem_restrictedTopology_of_functorPushforward_mem
    (CoverPreserving.of_isContinuous F _ _).cover_preserve hS

/--
lemma `restrictedTopology_eq_inducedTopology` / 引理 `restrictedTopology_eq_inducedTopology`

English:
lemma restrictedTopology_eq_inducedTopology
  given: [F.IsContinuous (F.restrictedTopology K) K]
  proof: by
  refine le_antisymm ?_ inducedTopology_le_restrictedTopology
  rw [le_inducedTopology_iff]
  infer_instance

中文:
引理 restrictedTopology_eq_inducedTopology
  条件: [F.IsContinuous (F.restrictedTopology K) K]
  证明: by
  refine le_antisymm ?_ inducedTopology_le_restrictedTopology
  rw [le_inducedTopology_iff]
  infer_instance

Depends on / 依赖: inducedTopology_le_restrictedTopology, infer_instance, le_antisymm, le_inducedTopology_iff
-/
lemma restrictedTopology_eq_inducedTopology [F.IsContinuous (F.restrictedTopology K) K] :
    F.restrictedTopology K = F.inducedTopology K := by
  refine le_antisymm ?_ inducedTopology_le_restrictedTopology
  rw [le_inducedTopology_iff]
  infer_instance

/--
lemma `restrictedTopology_eq_inducedTopology_of_isContinuous` / 引理 `restrictedTopology_eq_inducedTopology_of_isContinuous`

English:
lemma restrictedTopology_eq_inducedTopology_of_isContinuous
  statement: [F.IsContinuous J K]
  proof: by
  subst h
  rw [restrictedTopology_eq_inducedTopology]

中文:
引理 restrictedTopology_eq_inducedTopology_of_isContinuous
  结论: [F.IsContinuous J K]
  证明: by
  subst h
  rw [restrictedTopology_eq_inducedTopology]

Depends on / 依赖: restrictedTopology_eq_inducedTopology
-/
lemma restrictedTopology_eq_inducedTopology_of_isContinuous [F.IsContinuous J K]
    (h : F.restrictedTopology K = J) : F.inducedTopology K = J := by
  subst h
  rw [restrictedTopology_eq_inducedTopology]

end Functor

/--
lemma `Precoverage.toGrothendieck_comap_le_restrictedTopology` / 引理 `Precoverage.toGrothendieck_comap_le_restrictedTopology`

English:
lemma Precoverage.toGrothendieck_comap_le_restrictedTopology
  given: (K : Precoverage D)
  proof: by
  rw [Functor.restrictedTopology]
  grw [← K.le_toPrecoverage_toGrothendieck]

中文:
引理 Precoverage.toGrothendieck_comap_le_restrictedTopology
  条件: (K : Precoverage D)
  证明: by
  rw [Functor.restrictedTopology]
  grw [← K.le_toPrecoverage_toGrothendieck]

Depends on / 依赖: Functor, Functor.restrictedTopology, K.le_toPrecoverage_toGrothendieck, le_toPrecoverage_toGrothendieck, restrictedTopology
-/
lemma Precoverage.toGrothendieck_comap_le_restrictedTopology (K : Precoverage D) :
    (K.comap F).toGrothendieck <= F.restrictedTopology K.toGrothendieck := by
  rw [Functor.restrictedTopology]
  grw [← K.le_toPrecoverage_toGrothendieck]

end CategoryTheory
