/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.InducedTopology

/-!
# Induced Topology

We say that a functor `G : C ⥤ (D, K)` is locally dense if for each covering sieve `T` in `D` of
some `X : C`, `T ∩ mor(C)` generates a covering sieve of `X` in `D`. A locally dense fully faithful
functor then induces a topology on `C` via `{ T ∩ mor(C) | T ∈ K }`. Note that this is equal to
the collection of sieves on `C` whose image generates a covering sieve. This construction would
make `C` both cover-lifting and cover-preserving.

Some typical examples are full and cover-dense functors (for example the functor from a basis of a
topological space `X` into `Opens X`). The functor `Over X ⥤ C` is also locally dense, and the
induced topology can then be used to construct the big sites associated to a scheme.

Given a fully faithful cover-dense functor `G : C ⥤ (D, K)` between small sites, we then have
`Sheaf (H.inducedTopology) A ≌ Sheaf K A`. This is known as the comparison lemma.

## References

* [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.2.
* https://ncatlab.org/nlab/show/dense+sub-site
* https://ncatlab.org/nlab/show/comparison+lemma

-/

@[expose] public section

namespace CategoryTheory

universe v u

open Limits Opposite Presieve CategoryTheory

variable {C : Type*} [Category* C] {D : Type*} [Category* D] (G : C ⥤ D)
variable {J : GrothendieckTopology C} (K : GrothendieckTopology D)
variable (A : Type v) [Category.{u} A]

namespace Functor

-- variables (A) [full G] [faithful G]
/--
Definition of `LocallyCoverDense` / `LocallyCoverDense` 的定义

English:
class LocallyCoverDense
  parameters: : Prop where
  axioms and operations (1):
    - functorPushforward_functorPullback_mem : forall ⦃X : C⦄ (T : K (G.obj X)), (T.val.functorPullback G).functorPushforward G in K (G.obj X)

中文:
类 LocallyCoverDense
  参数: : 命题 where
  公理与运算 (1 个):
    - functorPushforward_functorPullback_mem : 对任意 ⦃X : C⦄ (T : K (G.obj X)), (T.val.functorPullback G).functorPushforward G in K (G.obj X)
-/
class LocallyCoverDense : Prop where
  functorPushforward_functorPullback_mem :
    forall ⦃X : C⦄ (T : K (G.obj X)), (T.val.functorPullback G).functorPushforward G in K (G.obj X)

variable [G.LocallyCoverDense K]

/--
theorem `pushforward_cover_iff_cover_pullback` / 定理 `pushforward_cover_iff_cover_pullback`

English:
theorem pushforward_cover_iff_cover_pullback
  given: [G.Full] [G.Faithful] {X : C} (S : Sieve X)
  proof: by
  constructor
  · intro hS
    exact ⟨⟨_, hS⟩, (Sieve.fullyFaithfulFunctorGaloisCoinsertion G X).u_l_eq S⟩
  · rintro ⟨T, rfl⟩
    exact LocallyCoverDense.functorPushforward_functorPullback_mem T

中文:
定理 pushforward_cover_iff_cover_pullback
  条件: [G.满] [G.忠实] {X : C} (S : 筛 X)
  证明: by
  constructor
  · intro hS
    exact ⟨⟨_, hS⟩, (Sieve.fullyFaithfulFunctorGaloisCoinsertion G X).u_l_eq S⟩
  · rintro ⟨T, rfl⟩
    exact LocallyCoverDense.functorPushforward_functorPullback_mem T

Depends on / 依赖: LocallyCoverDense, LocallyCoverDense.functorPushforward_functorPullback_mem, Sieve.fullyFaithfulFunctorGaloisCoinsertion, fullyFaithfulFunctorGaloisCoinsertion, functorPushforward_functorPullback_mem, u_l_eq
-/
theorem pushforward_cover_iff_cover_pullback [G.Full] [G.Faithful] {X : C} (S : Sieve X) :
    S.functorPushforward G in K (G.obj X) ↔ exists T : K (G.obj X), T.val.functorPullback G = S := by
  constructor
  · intro hS
    exact ⟨⟨_, hS⟩, (Sieve.fullyFaithfulFunctorGaloisCoinsertion G X).u_l_eq S⟩
  · rintro ⟨T, rfl⟩
    exact LocallyCoverDense.functorPushforward_functorPullback_mem T

variable [G.IsLocallyFull K] [G.IsLocallyFaithful K]

/--
theorem `coverPreserving_restrictedTopology` / 定理 `coverPreserving_restrictedTopology`

English:
theorem coverPreserving_restrictedTopology
  statement: CoverPreserving (G.restrictedTopology K) K G where
  proof: by
    rw [Functor.restrictedTopology] at hS
    induction hS with
    | of X S hS => rwa [← Sieve.generate_map_eq_functorPushforward]
    | top X => simp
    | pullback X S _ Y f ih =>
      apply K.transitive (LocallyCoverDense.functorPushforward_functorPullback_mem
        ⟨_, K.pullback_stable (

中文:
定理 coverPreserving_restrictedTopology
  结论: 余verPreserving (G.restrictedTopology K) K G where
  证明: by
    rw [Functor.restrictedTopology] at hS
    induction hS with
    | of X S hS => rwa [← Sieve.generate_map_eq_functorPushforward]
    | top X => simp
    | pullback X S _ Y f ih =>
      apply K.transitive (LocallyCoverDense.functorPushforward_functorPullback_mem
        ⟨_, K.pullback_stable (

Depends on / 依赖: Functor, Functor.restrictedTopology, G.functorPushforward_imageSieve_mem, G.map, K.pullback_stable, K.transitive, LocallyCoverDense, LocallyCoverDense.functorPushforward_functorPullback_mem, Sieve.generate_map_eq_functorPushforward, Sieve.pullback_comp, functorPushforward_functorPullback_mem, functorPushforward_imageSieve_mem, generate_map_eq_functorPushforward, pullback, pullback_comp, pullback_stable, restrictedTopology, transitive
-/
theorem coverPreserving_restrictedTopology : CoverPreserving (G.restrictedTopology K) K G where
  cover_preserve hS := by
    rw [Functor.restrictedTopology] at hS
    induction hS with
    | of X S hS => rwa [← Sieve.generate_map_eq_functorPushforward]
    | top X => simp
    | pullback X S _ Y f ih =>
      apply K.transitive (LocallyCoverDense.functorPushforward_functorPullback_mem
        ⟨_, K.pullback_stable (G.map f) ih⟩)
      rintro Z _ ⟨U, iUY, iZU, ⟨W, iWX, iUW, hiWX, e₁⟩, rfl⟩
      rw [Sieve.pullback_comp]
      apply K.pullback_stable
      clear iZU Z
      apply K.transitive (G.functorPushforward_imageSieve_mem _ iUW)
      rintro Z _ ⟨U₁, iU₁U, iZU₁, ⟨iU₁W, e₂⟩, rfl⟩
      rw [Sieve.pullback_comp]
      apply K.pullback_stable
      clear iZU₁ Z
      apply K.superset_covering ?_ (G.functorPushforward_equalizer_mem _
        (iU₁U ≫ iUY ≫ f) (iU₁W ≫ iWX) (by simp [e₁, e₂]))
      rintro Z _ ⟨U₂, iU₂U₁, iZU₂, e₃ : _ = _, rfl⟩
      refine ⟨_, iU₂U₁ ≫ iU₁U ≫ iUY, iZU₂, ?_, by simp⟩
      simpa [e₃] using S.downward_closed hiWX (iU₂U₁ ≫ iU₁W)
    | transitive X S R _ _ hS H' =>
      apply K.transitive hS
      rintro Y _ ⟨Z, g, i, hg, rfl⟩
      rw [Sieve.pullback_comp]
      apply K.pullback_stable i
      refine K.superset_covering ?_ (H' hg)
      rintro W _ ⟨Z', g', i', hg, rfl⟩
      refine ⟨Z', g' ≫ g, i', hg, ?_⟩
      simp

@[deprecated (since := "2026-05-28")]
alias inducedTopology_coverPreserving := coverPreserving_restrictedTopology

variable {G K} in
/-- If a functor `G : C ⥤ (D, K)` is locally fully faithful and locally dense, `S` is
a covering in the restricted topology on `C` if its image generates a `K`-cover. -/
@[simp]
/--
lemma `mem_restrictedTopology_iff` / 引理 `mem_restrictedTopology_iff`

English:
lemma mem_restrictedTopology_iff
  given: {X : C} {S : Sieve X}
  proof: ⟨fun hS => (G.coverPreserving_restrictedTopology K).cover_preserve hS,
    G.mem_restrictedTopology_of_functorPushforward_mem⟩

@[deprecated (since := "2026-05-28")]
alias mem_inducedTopology_sieves_iff := mem_restrictedTopology_iff

中文:
引理 mem_restrictedTopology_iff
  条件: {X : C} {S : 筛 X}
  证明: ⟨fun hS => (G.coverPreserving_restrictedTopology K).cover_preserve hS,
    G.mem_restrictedTopology_of_functorPushforward_mem⟩

@[deprecated (since := "2026-05-28")]
alias mem_inducedTopology_sieves_iff := mem_restrictedTopology_iff

Depends on / 依赖: G.coverPreserving_restrictedTopology, G.mem_restrictedTopology_of_functorPushforward_mem, coverPreserving_restrictedTopology, cover_preserve, mem_restrictedTopology_of_functorPushforward_mem
-/
lemma mem_restrictedTopology_iff {X : C} {S : Sieve X} :
    S in G.restrictedTopology K X ↔ S.functorPushforward G in K (G.obj X) :=
  ⟨fun hS => (G.coverPreserving_restrictedTopology K).cover_preserve hS,
    G.mem_restrictedTopology_of_functorPushforward_mem⟩

@[deprecated (since := "2026-05-28")]
alias mem_inducedTopology_sieves_iff := mem_restrictedTopology_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: G.IsCocontinuous (G.restrictedTopology K) K
  body: by
    apply G.mem_restrictedTopology_of_functorPushforward_mem
    exact LocallyCoverDense.functorPushforward_functorPullback_mem ⟨_, hS⟩

中文:
实例 :
  签名: G.是余continuous (G.restrictedTopology K) K
  定义体: by
    apply G.mem_restrictedTopology_of_functorPushforward_mem
    exact LocallyCoverDense.functorPushforward_functorPullback_mem ⟨_, hS⟩

Depends on / 依赖: G.mem_restrictedTopology_of_functorPushforward_mem, LocallyCoverDense, LocallyCoverDense.functorPushforward_functorPullback_mem, functorPushforward_functorPullback_mem, mem_restrictedTopology_of_functorPushforward_mem
-/
instance : G.IsCocontinuous (G.restrictedTopology K) K where
  cover_lift hS := by
    apply G.mem_restrictedTopology_of_functorPushforward_mem
    exact LocallyCoverDense.functorPushforward_functorPullback_mem ⟨_, hS⟩

instance (priority := 900) locallyCoverDense_of_isCoverDense [G.IsCoverDense K] :
    G.LocallyCoverDense K where
  functorPushforward_functorPullback_mem _ _ :=
    IsCoverDense.functorPullback_pushforward_covering _

instance (priority := 900) [G.IsCoverDense K] : G.IsDenseSubsite (G.restrictedTopology K) K where
  functorPushforward_mem_iff := mem_restrictedTopology_iff.symm

instance (priority := 900) [G.IsCoverDense K] : G.IsDenseSubsite (G.inducedTopology K) K := by
  rw [← restrictedTopology_eq_inducedTopology]
  infer_instance

@[simp]
/--
lemma `mem_inducedTopology_iff_of_isCoverDense` / 引理 `mem_inducedTopology_iff_of_isCoverDense`

English:
lemma mem_inducedTopology_iff_of_isCoverDense
  given: [G.IsCoverDense K] {X : C} (S : Sieve X)
  proof: by
  simp [← restrictedTopology_eq_inducedTopology]

中文:
引理 mem_inducedTopology_iff_of_isCoverDense
  条件: [G.是余verDense K] {X : C} (S : 筛 X)
  证明: by
  simp [← restrictedTopology_eq_inducedTopology]

Depends on / 依赖: restrictedTopology_eq_inducedTopology
-/
lemma mem_inducedTopology_iff_of_isCoverDense [G.IsCoverDense K] {X : C} (S : Sieve X) :
    S in G.inducedTopology K X ↔ S.functorPushforward G in K (G.obj X) := by
  simp [← restrictedTopology_eq_inducedTopology]

variable (J)

/--
Instance `over_forget_locallyCoverDense` / 实例 `over_forget_locallyCoverDense`

English:
instance over_forget_locallyCoverDense
  signature: (X : C)
  body: by
    convert! T.property
    ext Z f
    constructor
    · rintro ⟨_, _, g', hg, rfl⟩
      exact T.val.downward_closed hg g'
    · intro hf
      exact ⟨Over.mk (f ≫ Y.hom), Over.homMk f, 𝟙 _, hf, (Category.id_comp _).symm⟩

中文:
实例 over_forget_locallyCoverDense
  签名: (X : C)
  定义体: by
    convert! T.property
    ext Z f
    constructor
    · rintro ⟨_, _, g', hg, rfl⟩
      exact T.val.downward_closed hg g'
    · intro hf
      exact ⟨Over.mk (f ≫ Y.hom), Over.homMk f, 𝟙 _, hf, (Category.id_comp _).symm⟩

Depends on / 依赖: Category, Category.id_comp, Over.homMk, Over.mk, T.property, T.val.downward_closed, Y.hom, convert, downward_closed, id_comp, property
-/
instance over_forget_locallyCoverDense (X : C) : (Over.forget X).LocallyCoverDense J where
  functorPushforward_functorPullback_mem Y T := by
    convert! T.property
    ext Z f
    constructor
    · rintro ⟨_, _, g', hg, rfl⟩
      exact T.val.downward_closed hg g'
    · intro hf
      exact ⟨Over.mk (f ≫ Y.hom), Over.homMk f, 𝟙 _, hf, (Category.id_comp _).symm⟩

/--
Definition of `sheafInducedTopologyEquivOfIsCoverDense` / `sheafInducedTopologyEquivOfIsCoverDense` 的定义

English:
definition sheafInducedTopologyEquivOfIsCoverDense
  body: Functor.IsDenseSubsite.sheafEquiv (G.inducedTopology K) K G A

中文:
定义 sheafInducedTopologyEquivOfIsCoverDense
  定义体: Functor.IsDenseSubsite.sheafEquiv (G.inducedTopology K) K G A

Depends on / 依赖: Functor, Functor.IsDenseSubsite.sheafEquiv, G.inducedTopology, IsDenseSubsite, inducedTopology, sheafEquiv
-/
noncomputable def sheafInducedTopologyEquivOfIsCoverDense
    [G.IsCoverDense K] [forall (X : Dᵒᵖ), HasLimitsOfShape (StructuredArrow X G.op) A] :
    Sheaf (G.inducedTopology K) A ≌ Sheaf K A :=
  Functor.IsDenseSubsite.sheafEquiv (G.inducedTopology K) K G A

end Functor

namespace Precoverage

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) (K : Precoverage D)

variable [K.HasIsos] [K.IsStableUnderBaseChange] [K.IsStableUnderComposition]
  [K.HasPullbacks]

/--
lemma `locallyCoverDense_of_map_functorPullback_mem` / 引理 `locallyCoverDense_of_map_functorPullback_mem`

English:
lemma locallyCoverDense_of_map_functorPullback_mem
  proof: fun ⟨T, hT⟩ => by
    rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hT ⊢
    obtain ⟨R, hR, hle⟩ := hT
    refine ⟨_, H hR, ?_⟩
    refine le_trans ?_
      (Presieve.functorPushforward_monotone (Presieve.functorPullback_monotone hle))
    rw [← Sieve.arrows_generate_map_eq_

中文:
引理 locallyCoverDense_of_map_functorPullback_mem
  证明: fun ⟨T, hT⟩ => by
    rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hT ⊢
    obtain ⟨R, hR, hle⟩ := hT
    refine ⟨_, H hR, ?_⟩
    refine le_trans ?_
      (Presieve.functorPushforward_monotone (Presieve.functorPullback_monotone hle))
    rw [← Sieve.arrows_generate_map_eq_

Depends on / 依赖: Precoverage, Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition, Presieve, Presieve.functorPullback_monotone, Presieve.functorPushforward_monotone, Sieve.arrows_generate_map_eq_functorPushforward, Sieve.le_generate, arrows_generate_map_eq_functorPushforward, functorPullback_monotone, functorPushforward_monotone, le_generate, le_trans, mem_toGrothendieck_iff_of_isStableUnderComposition
-/
lemma locallyCoverDense_of_map_functorPullback_mem
    (H : forall {S : C} {R : Presieve (F.obj S)}, R in K (F.obj S) ->
      Presieve.map F (Presieve.functorPullback F R) in K (F.obj S)) :
    F.LocallyCoverDense K.toGrothendieck where
  functorPushforward_functorPullback_mem U := fun ⟨T, hT⟩ => by
    rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hT ⊢
    obtain ⟨R, hR, hle⟩ := hT
    refine ⟨_, H hR, ?_⟩
    refine le_trans ?_
      (Presieve.functorPushforward_monotone (Presieve.functorPullback_monotone hle))
    rw [← Sieve.arrows_generate_map_eq_functorPushforward]
    exact Sieve.le_generate _

/--
lemma `toGrothendieck_comap_eq_restrictedTopology` / 引理 `toGrothendieck_comap_eq_restrictedTopology`

English:
lemma toGrothendieck_comap_eq_restrictedTopology
  statement: [F.Faithful] [F.Full]
  proof: by
  have : F.LocallyCoverDense K.toGrothendieck :=
    K.locallyCoverDense_of_map_functorPullback_mem F H
  refine le_antisymm ?_ fun X T hT => ?_
  · apply toGrothendieck_comap_le_restrictedTopology
  · rw [Functor.mem_restrictedTopology_iff] at hT
    rw [Precoverage.mem_toGrothendieck_iff_of_isS

中文:
引理 toGrothendieck_comap_eq_restrictedTopology
  结论: [F.忠实] [F.满]
  证明: by
  have : F.LocallyCoverDense K.toGrothendieck :=
    K.locallyCoverDense_of_map_functorPullback_mem F H
  refine le_antisymm ?_ fun X T hT => ?_
  · apply toGrothendieck_comap_le_restrictedTopology
  · rw [Functor.mem_restrictedTopology_iff] at hT
    rw [Precoverage.mem_toGrothendieck_iff_of_isS

Depends on / 依赖: F.LocallyCoverDense, Functor, Functor.mem_restrictedTopology_iff, GrothendieckTopology, GrothendieckTopology.superset_covering, K.locallyCoverDense_of_map_functorPullback_mem, K.toGrothendieck, LocallyCoverDense, Precoverage, Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition, Presieve, Presieve.functorPullback, Sieve.generate, Sieve.generate_functorPul, functorPullback, generate, generate_functorPul, le_antisymm, le_trans, locallyCoverDense_of_map_functorPullback_mem
-/
lemma toGrothendieck_comap_eq_restrictedTopology [F.Faithful] [F.Full]
    (H : forall {S : C} {R : Presieve (F.obj S)}, R in K (F.obj S) ->
      Presieve.map F (Presieve.functorPullback F R) in K (F.obj S)) :
    (K.comap F).toGrothendieck = F.restrictedTopology K.toGrothendieck := by
  have : F.LocallyCoverDense K.toGrothendieck :=
    K.locallyCoverDense_of_map_functorPullback_mem F H
  refine le_antisymm ?_ fun X T hT => ?_
  · apply toGrothendieck_comap_le_restrictedTopology
  · rw [Functor.mem_restrictedTopology_iff] at hT
    rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hT
    obtain ⟨R, hR, hle⟩ := hT
    refine GrothendieckTopology.superset_covering
        (S := Sieve.generate (Presieve.functorPullback F R)) _ ?_ ?_
    · refine le_trans (le_trans (Sieve.generate_functorPullback_le F R)
        (Sieve.functorPullback_monotone _ _ (Sieve.generate_mono hle))) ?_
      rw [Sieve.generate_sieve]; rw [Sieve.functorPullback_functorPushforward_eq]
    · exact Precoverage.generate_mem_toGrothendieck (H hR)

@[deprecated (since := "2026-05-28")]
alias toGrothendieck_comap_eq_inducedTopology := toGrothendieck_comap_eq_restrictedTopology

@[deprecated (since := "2026-05-28")]
alias toGrothendieck_comap_le_inducedTopology := toGrothendieck_comap_le_restrictedTopology

end Precoverage

end CategoryTheory
