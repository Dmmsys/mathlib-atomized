/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.CategoryTheory.Sites.Precoverage

/-!
# Grothendieck pretopologies

Definition and lemmas about Grothendieck pretopologies.
A Grothendieck pretopology for a category `C` is a set of families of morphisms with fixed codomain,
satisfying certain closure conditions.

We show that a pretopology generates a genuine Grothendieck topology, and every topology has
a maximal pretopology which generates it.

The pretopology associated to a topological space is defined in `Spaces.lean`.

## Tags

coverage, pretopology, site

## References

* [nLab, *Grothendieck pretopology*](https://ncatlab.org/nlab/show/Grothendieck+pretopology)
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
* [Stacks, *00VG*](https://stacks.math.columbia.edu/tag/00VG)
-/

@[expose] public section


universe v u

noncomputable section

namespace CategoryTheory

open Category Limits Presieve

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable (C)

/--
A (Grothendieck) pretopology on `C` consists of a collection of families of morphisms with a fixed
target `X` for every object `X` in `C`, called "coverings" of `X`, which satisfies the following
three axioms:
1. Every family consisting of a single isomorphism is a covering family.
2. The collection of covering families is stable under pullback.
3. Given a covering family, and a covering family on each domain of the former, the composition
   is a covering family.

In some sense, a pretopology can be seen as Grothendieck topology with weaker saturation conditions,
in that each covering is not necessarily downward closed.

See: https://ncatlab.org/nlab/show/Grothendieck+pretopology or [MM92] Chapter III,
Section 2, Definition 2. -/
@[ext, stacks 00VH "Note that Stacks calls a category together with a pretopology a site,
and [MM92] calls this a basis for a topology."]
/--
Definition of `Pretopology` / `Pretopology` 的定义

English:
structure Pretopology
  parameters: extends Precoverage C
  extends: Precoverage C
  axioms and operations (3):
    - has_isos : forall ⦃X Y⦄ (f : Y ⟶ X) [IsIso f], Presieve.singleton f in coverings X
    - pullbacks : forall ⦃X Y⦄ (f : Y ⟶ X) (S), S in coverings X -> pullbackArrows f S in coverings Y
    - transitive : forall ⦃X : C⦄ (S : Presieve X) (Ti : forall ⦃Y⦄ (f : Y ⟶ X), S f -> Presieve Y), S in coverings X -> (forall ⦃Y⦄ (f) (H : S f), Ti f H in coverings Y) -> S.bind Ti in coverings X

中文:
结构 Pretopology
  参数: extends Precoverage C
  继承: Precoverage C
  公理与运算 (3 个):
    - has_isos : 对任意 ⦃X Y⦄ (f : Y ⟶ X) [是同构 f], Presieve.singleton f in coverings X
    - pullbacks : 对任意 ⦃X Y⦄ (f : Y ⟶ X) (S), S in coverings X -> pullbackArrows f S in coverings Y
    - transitive : 对任意 ⦃X : C⦄ (S : Presieve X) (Ti : 对任意 ⦃Y⦄ (f : Y ⟶ X), S f -> Presieve Y), S in coverings X -> (对任意 ⦃Y⦄ (f) (H : S f), Ti f H in coverings Y) -> S.bind Ti in coverings X
-/
structure Pretopology extends Precoverage C where
  /-- For all `X : C`, the coverings of `X` (sets of families of morphisms with target `X`) -/
  has_isos : forall ⦃X Y⦄ (f : Y ⟶ X) [IsIso f], Presieve.singleton f in coverings X
  pullbacks : forall ⦃X Y⦄ (f : Y ⟶ X) (S), S in coverings X -> pullbackArrows f S in coverings Y
  transitive :
    forall ⦃X : C⦄ (S : Presieve X) (Ti : forall ⦃Y⦄ (f : Y ⟶ X), S f -> Presieve Y),
      S in coverings X -> (forall ⦃Y⦄ (f) (H : S f), Ti f H in coverings Y) -> S.bind Ti in coverings X

namespace Pretopology

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (Pretopology C) fun _ => forall X
  body: ⟨fun J => J.coverings⟩

中文:
实例 :
  签名: CoeFun (Pretopology C) fun _ => 对任意 X
  定义体: ⟨fun J => J.coverings⟩

Depends on / 依赖: J.coverings, coverings
-/
instance : CoeFun (Pretopology C) fun _ => forall X : C, Set (Presieve X) :=
  ⟨fun J => J.coverings⟩

variable {C}

/--
Instance `LE` / 实例 `LE`

English:
instance LE
  signature: : LE (Pretopology C) where
  body: (K₁ : forall X : C, Set (Presieve X)) <= K₂

中文:
实例 LE
  签名: : LE (Pretopology C) where
  定义体: (K₁ : forall X : C, Set (Presieve X)) <= K₂

Depends on / 依赖: Presieve
-/
instance LE : LE (Pretopology C) where
  le K₁ K₂ := (K₁ : forall X : C, Set (Presieve X)) <= K₂

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  given: {K₁ K₂ : Pretopology C}
  statement: K₁ <= K₂ ↔ (K₁ : forall X : C, Set (Presieve X)) <= K₂
  proof: Iff.rfl

中文:
定理 le_def
  条件: {K₁ K₂ : Pretopology C}
  结论: K₁ <= K₂ ↔ (K₁ : 对任意 X : C, 集合 (Presieve X)) <= K₂
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem le_def {K₁ K₂ : Pretopology C} : K₁ <= K₂ ↔ (K₁ : forall X : C, Set (Presieve X)) <= K₂ :=
  Iff.rfl

variable (C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Pretopology C)
  body: { Pretopology.LE with
    le_refl := fun _ => le_def.mpr le_rfl
    le_trans := fun _ _ _ h₁₂ h₂₃ => le_def.mpr (le_trans h₁₂ h₂₃)
    le_antisymm := fun _ _ h₁₂ h₂₁ => Pretopology.ext (le_antisymm h₁₂ h₂₁) }

中文:
实例 :
  签名: 偏序 (Pretopology C)
  定义体: { Pretopology.LE with
    le_refl := fun _ => le_def.mpr le_rfl
    le_trans := fun _ _ _ h₁₂ h₂₃ => le_def.mpr (le_trans h₁₂ h₂₃)
    le_antisymm := fun _ _ h₁₂ h₂₁ => Pretopology.ext (le_antisymm h₁₂ h₂₁) }

Depends on / 依赖: Pretopology, Pretopology.LE, Pretopology.ext, le_antisymm, le_def, le_def.mpr, le_refl, le_rfl, le_trans
-/
instance : PartialOrder (Pretopology C) :=
  { Pretopology.LE with
    le_refl := fun _ => le_def.mpr le_rfl
    le_trans := fun _ _ _ h₁₂ h₂₃ => le_def.mpr (le_trans h₁₂ h₂₃)
    le_antisymm := fun _ _ h₁₂ h₂₁ => Pretopology.ext (le_antisymm h₁₂ h₂₁) }

/--
Instance `orderTop` / 实例 `orderTop`

English:
instance orderTop
  signature: : OrderTop (Pretopology C) where
  body: { coverings := fun _ => Set.univ
      has_isos := fun _ _ _ _ => Set.mem_univ _
      pullbacks := fun _ _ _ _ _ => Set.mem_univ _
      transitive := fun _ _ _ _ _ => Set.mem_univ _ }
  le_top _ _ _ _ := Set.mem_univ _

中文:
实例 orderTop
  签名: : 有顶序 (Pretopology C) where
  定义体: { coverings := fun _ => Set.univ
      has_isos := fun _ _ _ _ => Set.mem_univ _
      pullbacks := fun _ _ _ _ _ => Set.mem_univ _
      transitive := fun _ _ _ _ _ => Set.mem_univ _ }
  le_top _ _ _ _ := Set.mem_univ _

Depends on / 依赖: Set.mem_univ, Set.univ, coverings, has_isos, le_top, mem_univ, pullbacks, transitive
-/
instance orderTop : OrderTop (Pretopology C) where
  top :=
    { coverings := fun _ => Set.univ
      has_isos := fun _ _ _ _ => Set.mem_univ _
      pullbacks := fun _ _ _ _ _ => Set.mem_univ _
      transitive := fun _ _ _ _ _ => Set.mem_univ _ }
  le_top _ _ _ _ := Set.mem_univ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Pretopology C)
  body: ⟨⊤⟩

中文:
实例 :
  签名: 可居 (Pretopology C)
  定义体: ⟨⊤⟩
-/
instance : Inhabited (Pretopology C) :=
  ⟨⊤⟩

variable {C}

/-- A pretopology `K` can be completed to a Grothendieck topology `J` by declaring a sieve to be
`J`-covering if it contains a family in `K`.

See also [MM92] Chapter III, Section 2, Equation (2).
-/
@[stacks 00ZC]
/--
Definition of `toGrothendieck` / `toGrothendieck` 的定义

English:
definition toGrothendieck
  signature: (K : Pretopology C)
  body: {S | exists R in K X, R <= (S : Presieve _)}
  top_mem' _ := ⟨Presieve.singleton (𝟙 _), K.has_isos _, fun _ _ _ => ⟨⟩⟩
  pullback_stable' X Y S g := by
    rintro ⟨R, hR, RS⟩
    refine ⟨_, K.pullbacks g _ hR, ?_⟩
    rw [← Sieve.generate_le_iff]; rw [Sieve.pullbackArrows_comm]
    apply Sieve.pullb

中文:
定义 toGrothendieck
  签名: (K : Pretopology C)
  定义体: {S | exists R in K X, R <= (S : Presieve _)}
  top_mem' _ := ⟨Presieve.singleton (𝟙 _), K.has_isos _, fun _ _ _ => ⟨⟩⟩
  pullback_stable' X Y S g := by
    rintro ⟨R, hR, RS⟩
    refine ⟨_, K.pullbacks g _ hR, ?_⟩
    rw [← Sieve.generate_le_iff]; rw [Sieve.pullbackArrows_comm]
    apply Sieve.pullb

Depends on / 依赖: Presieve
-/
def toGrothendieck (K : Pretopology C) : GrothendieckTopology C where
  sieves X := {S | exists R in K X, R <= (S : Presieve _)}
  top_mem' _ := ⟨Presieve.singleton (𝟙 _), K.has_isos _, fun _ _ _ => ⟨⟩⟩
  pullback_stable' X Y S g := by
    rintro ⟨R, hR, RS⟩
    refine ⟨_, K.pullbacks g _ hR, ?_⟩
    rw [← Sieve.generate_le_iff]; rw [Sieve.pullbackArrows_comm]
    apply Sieve.pullback_monotone
    rwa [Sieve.giGenerate.gc]
  transitive' := by
    rintro X S ⟨R', hR', RS⟩ R t
    choose t₁ t₂ t₃ using t
    refine ⟨_, K.transitive _ _ hR' fun _ f hf => t₂ (RS _ _ hf), ?_⟩
    rintro Y _ ⟨Z, g, f, hg, hf, rfl⟩
    apply t₃ (RS _ _ hg) _ _ hf

/--
theorem `mem_toGrothendieck` / 定理 `mem_toGrothendieck`

English:
theorem mem_toGrothendieck
  given: (K : Pretopology C) (X S)
  proof: Iff.rfl

中文:
定理 mem_toGrothendieck
  条件: (K : Pretopology C) (X S)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_toGrothendieck (K : Pretopology C) (X S) :
    S in toGrothendieck K X ↔ exists R in K X, R <= (S : Presieve X) :=
  Iff.rfl

end Pretopology

variable {C} in
/--
Definition of `GrothendieckTopology.toPretopology` / `GrothendieckTopology.toPretopology` 的定义

English:
definition GrothendieckTopology.toPretopology
  signature: (J : GrothendieckTopology C)
  body: {R | Sieve.generate R in J X}
  has_isos X Y f i := J.covering_of_eq_top (by simp)
  pullbacks X Y f R hR := by simpa [Sieve.pullbackArrows_comm] using J.pullback_stable f hR
  transitive X S Ti hS hTi := by
    apply J.transitive hS
    intro Y f
    rintro ⟨Z, g, f, hf, rfl⟩
    rw [Sieve.pullback

中文:
定义 Grothendieck拓扑.toPretopology
  签名: (J : Grothendieck拓扑 C)
  定义体: {R | Sieve.generate R in J X}
  has_isos X Y f i := J.covering_of_eq_top (by simp)
  pullbacks X Y f R hR := by simpa [Sieve.pullbackArrows_comm] using J.pullback_stable f hR
  transitive X S Ti hS hTi := by
    apply J.transitive hS
    intro Y f
    rintro ⟨Z, g, f, hf, rfl⟩
    rw [Sieve.pullback

Depends on / 依赖: Sieve.generate, generate
-/
def GrothendieckTopology.toPretopology (J : GrothendieckTopology C) : Pretopology C where
  coverings X := {R | Sieve.generate R in J X}
  has_isos X Y f i := J.covering_of_eq_top (by simp)
  pullbacks X Y f R hR := by simpa [Sieve.pullbackArrows_comm] using J.pullback_stable f hR
  transitive X S Ti hS hTi := by
    apply J.transitive hS
    intro Y f
    rintro ⟨Z, g, f, hf, rfl⟩
    rw [Sieve.pullback_comp]
    apply J.pullback_stable g
    apply J.superset_covering _ (hTi _ hf)
    rintro Y g ⟨W, h, g, hg, rfl⟩
    exact ⟨_, h, _, ⟨_, _, _, hf, hg, rfl⟩, by simp⟩

/--
Definition of `Pretopology.gi` / `Pretopology.gi` 的定义

English:
definition Pretopology.gi
  signature: : GaloisInsertion
  body: by
    constructor
    · intro h X R hR
      exact h _ ⟨_, hR, Sieve.le_generate R⟩
    · rintro h X S ⟨R, hR, RS⟩
      apply J.superset_covering _ (h _ hR)
      rwa [Sieve.giGenerate.gc]
  le_l_u J _ S hS := ⟨S, J.superset_covering (Sieve.le_generate S.arrows) hS, le_rfl⟩
  choice x _ := toGroth

中文:
定义 Pretopology.gi
  签名: : Galois嵌入
  定义体: by
    constructor
    · intro h X R hR
      exact h _ ⟨_, hR, Sieve.le_generate R⟩
    · rintro h X S ⟨R, hR, RS⟩
      apply J.superset_covering _ (h _ hR)
      rwa [Sieve.giGenerate.gc]
  le_l_u J _ S hS := ⟨S, J.superset_covering (Sieve.le_generate S.arrows) hS, le_rfl⟩
  choice x _ := toGroth

Depends on / 依赖: GrothendieckTopology, GrothendieckTopology.toPretopology, toPretopology
-/
def Pretopology.gi : GaloisInsertion
    (toGrothendieck (C := C)) (GrothendieckTopology.toPretopology (C := C)) where
  gc K J := by
    constructor
    · intro h X R hR
      exact h _ ⟨_, hR, Sieve.le_generate R⟩
    · rintro h X S ⟨R, hR, RS⟩
      apply J.superset_covering _ (h _ hR)
      rwa [Sieve.giGenerate.gc]
  le_l_u J _ S hS := ⟨S, J.superset_covering (Sieve.le_generate S.arrows) hS, le_rfl⟩
  choice x _ := toGrothendieck x
  choice_eq _ _ := rfl

/--
lemma `GrothendieckTopology.mem_toPretopology` / 引理 `GrothendieckTopology.mem_toPretopology`

English:
lemma GrothendieckTopology.mem_toPretopology
  given: (t : GrothendieckTopology C) {X : C} (S : Presieve X)
  proof: Iff.rfl

中文:
引理 Grothendieck拓扑.mem_toPretopology
  条件: (t : Grothendieck拓扑 C) {X : C} (S : Presieve X)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma GrothendieckTopology.mem_toPretopology (t : GrothendieckTopology C) {X : C} (S : Presieve X) :
    S in t.toPretopology X ↔ Sieve.generate S in t X :=
  Iff.rfl

namespace Pretopology

set_option backward.isDefEq.respectTransparency false in
/--
The trivial pretopology, in which the coverings are exactly singleton isomorphisms. This topology is
also known as the indiscrete, coarse, or chaotic topology. -/
@[stacks 07GE]
/--
Definition of `trivial` / `trivial` 的定义

English:
definition trivial
  signature: : Pretopology C where
  body: {S | exists (Y : _) (f : Y ⟶ X) (_ : IsIso f), S = Presieve.singleton f}
  has_isos _ _ _ i := ⟨_, _, i, rfl⟩
  pullbacks X Y f S := by
    rintro ⟨Z, g, i, rfl⟩
    refine ⟨pullback g f, pullback.snd _ _, ?_, ?_⟩
    · refine ⟨⟨pullback.lift (f ≫ inv g) (𝟙 _) (by simp), ⟨?_, by simp⟩⟩⟩
      ext
  

中文:
定义 trivial
  签名: : Pretopology C where
  定义体: {S | exists (Y : _) (f : Y ⟶ X) (_ : IsIso f), S = Presieve.singleton f}
  has_isos _ _ _ i := ⟨_, _, i, rfl⟩
  pullbacks X Y f S := by
    rintro ⟨Z, g, i, rfl⟩
    refine ⟨pullback g f, pullback.snd _ _, ?_, ?_⟩
    · refine ⟨⟨pullback.lift (f ≫ inv g) (𝟙 _) (by simp), ⟨?_, by simp⟩⟩⟩
      ext
  

Depends on / 依赖: Presieve, Presieve.singleton, singleton
-/
def trivial : Pretopology C where
  coverings X := {S | exists (Y : _) (f : Y ⟶ X) (_ : IsIso f), S = Presieve.singleton f}
  has_isos _ _ _ i := ⟨_, _, i, rfl⟩
  pullbacks X Y f S := by
    rintro ⟨Z, g, i, rfl⟩
    refine ⟨pullback g f, pullback.snd _ _, ?_, ?_⟩
    · refine ⟨⟨pullback.lift (f ≫ inv g) (𝟙 _) (by simp), ⟨?_, by simp⟩⟩⟩
      ext
      · rw [assoc, pullback.lift_fst, ← pullback.condition_assoc]
        simp
      · simp
    · apply pullback_singleton
  transitive := by
    rintro X S Ti ⟨Z, g, i, rfl⟩ hS
    rcases hS g (singleton_self g) with ⟨Y, f, i, hTi⟩
    refine ⟨_, f ≫ g, ?_, ?_⟩
    · infer_instance
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): the next four lines were just "ext (W k)"
    apply funext
    intro W
    ext K
    constructor
    · rintro ⟨V, h, k, ⟨_⟩, hh, rfl⟩
      rw [hTi] at hh
      cases hh
      apply singleton.mk
    · rintro ⟨_⟩
      refine bind_comp g singleton.mk ?_
      rw [hTi]
      apply singleton.mk

/--
Instance `orderBot` / 实例 `orderBot`

English:
instance orderBot
  signature: : OrderBot (Pretopology C) where
  body: trivial C
  bot_le K X R := by
    rintro ⟨Y, f, hf, rfl⟩
    exact K.has_isos f

中文:
实例 orderBot
  签名: : 有底序 (Pretopology C) where
  定义体: trivial C
  bot_le K X R := by
    rintro ⟨Y, f, hf, rfl⟩
    exact K.has_isos f
-/
instance orderBot : OrderBot (Pretopology C) where
  bot := trivial C
  bot_le K X R := by
    rintro ⟨Y, f, hf, rfl⟩
    exact K.has_isos f

/--
theorem `toGrothendieck_bot` / 定理 `toGrothendieck_bot`

English:
theorem toGrothendieck_bot
  statement: toGrothendieck (C := C) ⊥ = ⊥
  proof: (gi C).gc.l_bot

@[gcongr]

中文:
定理 toGrothendieck_bot
  结论: toGrothendieck (C := C) ⊥ = ⊥
  证明: (gi C).gc.l_bot

@[gcongr]
-/
theorem toGrothendieck_bot : toGrothendieck (C := C) ⊥ = ⊥ :=
  (gi C).gc.l_bot

@[gcongr]
/--
lemma `toGrothendieck_mono` / 引理 `toGrothendieck_mono`

English:
lemma toGrothendieck_mono
  given: {J K : Pretopology C} (h : J <= K)
  statement: J.toGrothendieck <= K.toGrothendieck
  proof: fun _ _ ⟨R, hR, hle⟩ => ⟨R, h _ hR, hle⟩

中文:
引理 toGrothendieck_mono
  条件: {J K : Pretopology C} (h : J <= K)
  结论: J.toGrothendieck <= K.toGrothendieck
  证明: fun _ _ ⟨R, hR, hle⟩ => ⟨R, h _ hR, hle⟩
-/
lemma toGrothendieck_mono {J K : Pretopology C} (h : J <= K) : J.toGrothendieck <= K.toGrothendieck :=
  fun _ _ ⟨R, hR, hle⟩ => ⟨R, h _ hR, hle⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (Pretopology C)
  body: {
    coverings := sInf ((fun J => J.coverings) '' T)
    has_isos := fun X Y f _ => by
      simp only [sInf_apply, Set.iInf_eq_iInter, Set.iInter_coe_set, Set.mem_image,
        Set.iInter_exists,
        Set.biInter_and', Set.iInter_iInter_eq_right, Set.mem_iInter]
      intro t _
      exact t.h

中文:
实例 :
  签名: 下确界集 (Pretopology C)
  定义体: {
    coverings := sInf ((fun J => J.coverings) '' T)
    has_isos := fun X Y f _ => by
      simp only [sInf_apply, Set.iInf_eq_iInter, Set.iInter_coe_set, Set.mem_image,
        Set.iInter_exists,
        Set.biInter_and', Set.iInter_iInter_eq_right, Set.mem_iInter]
      intro t _
      exact t.h
-/
instance : InfSet (Pretopology C) where
  sInf T := {
    coverings := sInf ((fun J => J.coverings) '' T)
    has_isos := fun X Y f _ => by
      simp only [sInf_apply, Set.iInf_eq_iInter, Set.iInter_coe_set, Set.mem_image,
        Set.iInter_exists,
        Set.biInter_and', Set.iInter_iInter_eq_right, Set.mem_iInter]
      intro t _
      exact t.has_isos f
    pullbacks := fun X Y f S hS => by
      simp only [sInf_apply, Set.iInf_eq_iInter, Set.iInter_coe_set, Set.mem_image,
        Set.iInter_exists, Set.biInter_and', Set.iInter_iInter_eq_right, Set.mem_iInter] at hS ⊢
      intro t ht
      exact t.pullbacks f S (hS t ht)
    transitive := fun X S Ti hS hTi => by
      simp only [sInf_apply, Set.iInf_eq_iInter, Set.iInter_coe_set, Set.mem_image,
        Set.iInter_exists, Set.biInter_and', Set.iInter_iInter_eq_right, Set.mem_iInter] at hS hTi ⊢
      intro t ht
      exact t.transitive S Ti (hS t ht) (fun Y f H => hTi f H t ht)
  }

/--
lemma `mem_sInf` / 引理 `mem_sInf`

English:
lemma mem_sInf
  given: (T : Set (Pretopology C)) {X : C} (S : Presieve X)
  proof: by
  change S in sInf ((fun J : Pretopology C => J.coverings) '' T) X ↔ _
  simp

中文:
引理 mem_sInf
  条件: (T : 集合 (Pretopology C)) {X : C} (S : Presieve X)
  证明: by
  change S in sInf ((fun J : Pretopology C => J.coverings) '' T) X ↔ _
  simp

Depends on / 依赖: J.coverings, Pretopology, coverings
-/
lemma mem_sInf (T : Set (Pretopology C)) {X : C} (S : Presieve X) :
    S in sInf T X ↔ forall t in T, S in t X := by
  change S in sInf ((fun J : Pretopology C => J.coverings) '' T) X ↔ _
  simp

/--
lemma `sInf_ofGrothendieck` / 引理 `sInf_ofGrothendieck`

English:
lemma sInf_ofGrothendieck
  given: (T : Set (GrothendieckTopology C))
  proof: by
  ext X S
  simp [mem_sInf, GrothendieckTopology.mem_toPretopology, GrothendieckTopology.mem_sInf]

中文:
引理 sInf_ofGrothendieck
  条件: (T : 集合 (Grothendieck拓扑 C))
  证明: by
  ext X S
  simp [mem_sInf, GrothendieckTopology.mem_toPretopology, GrothendieckTopology.mem_sInf]

Depends on / 依赖: GrothendieckTopology, GrothendieckTopology.mem_sInf, GrothendieckTopology.mem_toPretopology, mem_sInf, mem_toPretopology
-/
lemma sInf_ofGrothendieck (T : Set (GrothendieckTopology C)) :
    (sInf T).toPretopology = sInf (GrothendieckTopology.toPretopology '' T) := by
  ext X S
  simp [mem_sInf, GrothendieckTopology.mem_toPretopology, GrothendieckTopology.mem_sInf]

/--
lemma `isGLB_sInf` / 引理 `isGLB_sInf`

English:
lemma isGLB_sInf
  given: (T : Set (Pretopology C))
  statement: IsGLB T (sInf T)
  proof: IsGLB.of_image (f := fun J => J.coverings) Iff.rfl (_root_.isGLB_sInf _)

中文:
引理 isGLB_sInf
  条件: (T : 集合 (Pretopology C))
  结论: IsGLB T (sInf T)
  证明: IsGLB.of_image (f := fun J => J.coverings) Iff.rfl (_root_.isGLB_sInf _)

Depends on / 依赖: Iff.rfl, IsGLB.of_image, J.coverings, _root_, _root_.isGLB_sInf, coverings, isGLB_sInf, of_image
-/
lemma isGLB_sInf (T : Set (Pretopology C)) : IsGLB T (sInf T) :=
  IsGLB.of_image (f := fun J => J.coverings) Iff.rfl (_root_.isGLB_sInf _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (Pretopology C)
  body: orderBot C
  __ := orderTop C
  inf t₁ t₂ := {
    coverings := fun X => t₁.coverings X inter t₂.coverings X
    has_isos := fun _ _ f _ =>
      ⟨t₁.has_isos f, t₂.has_isos f⟩
    pullbacks := fun _ _ f S hS =>
      ⟨t₁.pullbacks f S hS.left, t₂.pullbacks f S hS.right⟩
    transitive := fun _ S Ti

中文:
实例 :
  签名: 完备格 (Pretopology C)
  定义体: orderBot C
  __ := orderTop C
  inf t₁ t₂ := {
    coverings := fun X => t₁.coverings X inter t₂.coverings X
    has_isos := fun _ _ f _ =>
      ⟨t₁.has_isos f, t₂.has_isos f⟩
    pullbacks := fun _ _ f S hS =>
      ⟨t₁.pullbacks f S hS.left, t₂.pullbacks f S hS.right⟩
    transitive := fun _ S Ti

Depends on / 依赖: orderBot
-/
instance : CompleteLattice (Pretopology C) where
  __ := orderBot C
  __ := orderTop C
  inf t₁ t₂ := {
    coverings := fun X => t₁.coverings X inter t₂.coverings X
    has_isos := fun _ _ f _ =>
      ⟨t₁.has_isos f, t₂.has_isos f⟩
    pullbacks := fun _ _ f S hS =>
      ⟨t₁.pullbacks f S hS.left, t₂.pullbacks f S hS.right⟩
    transitive := fun _ S Ti hS hTi =>
      ⟨t₁.transitive S Ti hS.left (fun _ f H => (hTi f H).left),
        t₂.transitive S Ti hS.right (fun _ f H => (hTi f H).right)⟩
  }
  inf_le_left _ _ _ _ hS := hS.left
  inf_le_right _ _ _ _ hS := hS.right
  le_inf _ _ _ hts htr X _ hS := ⟨hts X hS, htr X hS⟩
  __ := completeLatticeOfInf _ (isGLB_sInf C)

/--
lemma `mem_inf` / 引理 `mem_inf`

English:
lemma mem_inf
  given: (t₁ t₂ : Pretopology C) {X : C} (S : Presieve X)
  proof: Iff.rfl

中文:
引理 mem_inf
  条件: (t₁ t₂ : Pretopology C) {X : C} (S : Presieve X)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_inf (t₁ t₂ : Pretopology C) {X : C} (S : Presieve X) :
    S in (t₁ ⊓ t₂) X ↔ S in t₁ X ∧ S in t₂ X :=
  Iff.rfl

end Pretopology

/-- If `J` is a precoverage that has isomorphisms and is stable under composition and
base change, it defines a pretopology. -/
@[simps toPrecoverage]
/--
Definition of `Precoverage.toPretopology` / `Precoverage.toPretopology` 的定义

English:
definition Precoverage.toPretopology
  signature: [Limits.HasPullbacks C] (J : Precoverage C) [J.HasIsos]
  body: J
  has_isos X Y f hf := mem_coverings_of_isIso f
  pullbacks X Y f R hR := J.pullbackArrows_mem f hR
  transitive X R Ti hR hTi := by
    obtain ⟨ι, Z, g, rfl⟩ := R.exists_eq_ofArrows
    choose κ W p hp using fun ⦃Y⦄ (f : Y ⟶ X) hf => (Ti f hf).exists_eq_ofArrows
    have : (Presieve.ofArrows Z g)

中文:
定义 Precoverage.toPretopology
  签名: [Limits.有Pullbacks C] (J : Precoverage C) [J.有是os]
  定义体: J
  has_isos X Y f hf := mem_coverings_of_isIso f
  pullbacks X Y f R hR := J.pullbackArrows_mem f hR
  transitive X R Ti hR hTi := by
    obtain ⟨ι, Z, g, rfl⟩ := R.exists_eq_ofArrows
    choose κ W p hp using fun ⦃Y⦄ (f : Y ⟶ X) hf => (Ti f hf).exists_eq_ofArrows
    have : (Presieve.ofArrows Z g)
-/
def Precoverage.toPretopology [Limits.HasPullbacks C] (J : Precoverage C) [J.HasIsos]
    [J.IsStableUnderBaseChange] [J.IsStableUnderComposition] : Pretopology C where
  __ := J
  has_isos X Y f hf := mem_coverings_of_isIso f
  pullbacks X Y f R hR := J.pullbackArrows_mem f hR
  transitive X R Ti hR hTi := by
    obtain ⟨ι, Z, g, rfl⟩ := R.exists_eq_ofArrows
    choose κ W p hp using fun ⦃Y⦄ (f : Y ⟶ X) hf => (Ti f hf).exists_eq_ofArrows
    have : (Presieve.ofArrows Z g).bind Ti =
        .ofArrows (fun ij : Σ i, κ (g i) ⟨i⟩ => W _ _ ij.2) (fun ij => p _ _ ij.2 ≫ g ij.1) := by
      apply le_antisymm
      · rintro T u ⟨S, v, w, ⟨i⟩, hv, rfl⟩
        rw [hp] at hv
        obtain ⟨j⟩ := hv
exact .mk Sigma.mk (β := fun i : ι => κ (g i) ⟨i⟩) i j
      · rintro T u ⟨ij⟩
        use Z ij.1, p (g ij.1) ⟨ij.1⟩ ij.2, g ij.1, ⟨ij.1⟩
        rw [hp]
        exact ⟨⟨_⟩, rfl⟩
    rw [this]
    refine J.comp_mem_coverings (Y := fun (i : ι) (j : κ (g i) ⟨i⟩) => W _ _ j)
      (g := fun i j => p _ _ j) _ hR fun i => ?_
    rw [← hp]
    exact hTi _ _

end CategoryTheory
