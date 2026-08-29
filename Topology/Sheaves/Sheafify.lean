/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Topology.Sheaves.LocalPredicate
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Sheafification of `Type`-valued presheaves

We construct the sheafification of a `Type`-valued presheaf,
as the subsheaf of dependent functions into the stalks
consisting of functions which are locally germs.

We show that the stalks of the sheafification are isomorphic to the original stalks,
via `stalkToFiber` which evaluates a germ of a dependent function at a point.

We construct a morphism `toSheafify` from a presheaf to (the underlying presheaf of)
its sheafification, given by sending a section to its collection of germs.

## Future work
Show that the map induced on stalks by `toSheafify` is the inverse of `stalkToFiber`.

Show sheafification is a functor from presheaves to sheaves,
and that it is the left adjoint of the forgetful functor,
following <https://stacks.math.columbia.edu/tag/007X>.
-/

@[expose] public section

assert_not_exists CommRingCat


universe v u

noncomputable section

open TopCat Opposite TopologicalSpace CategoryTheory

variable {X : TopCat.{v}} (F : Presheaf (Type v) X)

namespace TopCat.Presheaf

namespace Sheafify

/--
Definition of `isGerm` / `isGerm` 的定义

English:
definition isGerm
  signature: : PrelocalPredicate fun x => F.stalk x where
  body: exists g : F.obj (op U), forall x : U, f x = F.germ U x.1 x.2 g
  res := fun i _ ⟨g, p⟩ => ⟨F.map i.op g, fun x => (p (i x)).trans (F.germ_res_apply i x x.2 g).symm⟩

中文:
定义 isGerm
  签名: : PrelocalPredicate fun x => F.stalk x where
  定义体: exists g : F.obj (op U), forall x : U, f x = F.germ U x.1 x.2 g
  res := fun i _ ⟨g, p⟩ => ⟨F.map i.op g, fun x => (p (i x)).trans (F.germ_res_apply i x x.2 g).symm⟩

Depends on / 依赖: F.germ, F.obj
-/
def isGerm : PrelocalPredicate fun x => F.stalk x where
  pred {U} f := exists g : F.obj (op U), forall x : U, f x = F.germ U x.1 x.2 g
  res := fun i _ ⟨g, p⟩ => ⟨F.map i.op g, fun x => (p (i x)).trans (F.germ_res_apply i x x.2 g).symm⟩

/--
Definition of `isLocallyGerm` / `isLocallyGerm` 的定义

English:
definition isLocallyGerm
  signature: : LocalPredicate fun x => F.stalk x
  body: (isGerm F).sheafify

中文:
定义 isLocallyGerm
  签名: : LocalPredicate fun x => F.stalk x
  定义体: (isGerm F).sheafify

Depends on / 依赖: isGerm, sheafify
-/
def isLocallyGerm : LocalPredicate fun x => F.stalk x :=
  (isGerm F).sheafify

end Sheafify

/--
Definition of `sheafify` / `sheafify` 的定义

English:
definition sheafify
  signature: : Sheaf (Type v) X
  body: subsheafToTypes (Sheafify.isLocallyGerm F)

中文:
定义 sheafify
  签名: : Sheaf (类型v) X
  定义体: subsheafToTypes (Sheafify.isLocallyGerm F)

Depends on / 依赖: Sheafify, Sheafify.isLocallyGerm, isLocallyGerm, subsheafToTypes
-/
def sheafify : Sheaf (Type v) X :=
  subsheafToTypes (Sheafify.isLocallyGerm F)

/--
Definition of `toSheafify` / `toSheafify` 的定义

English:
definition toSheafify
  signature: : F ⟶ F.sheafify.1 where
  body: ↾fun f => ⟨fun x => F.germ _ x x.2 f, PrelocalPredicate.sheafifyOf
    ⟨f, fun x => rfl⟩⟩
  naturality U U' f := by
    ext x
    apply Subtype.ext -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Added `apply`
    ext ⟨u, m⟩
    exact germ_res_apply F f.unop u m x

中文:
定义 toSheafify
  签名: : F ⟶ F.sheafify.1 where
  定义体: ↾fun f => ⟨fun x => F.germ _ x x.2 f, PrelocalPredicate.sheafifyOf
    ⟨f, fun x => rfl⟩⟩
  naturality U U' f := by
    ext x
    apply Subtype.ext -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Added `apply`
    ext ⟨u, m⟩
    exact germ_res_apply F f.unop u m x

Depends on / 依赖: F.germ, PrelocalPredicate, PrelocalPredicate.sheafifyOf, sheafifyOf
-/
def toSheafify : F ⟶ F.sheafify.1 where
  app U := ↾fun f => ⟨fun x => F.germ _ x x.2 f, PrelocalPredicate.sheafifyOf
    ⟨f, fun x => rfl⟩⟩
  naturality U U' f := by
    ext x
    apply Subtype.ext -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Added `apply`
    ext ⟨u, m⟩
    exact germ_res_apply F f.unop u m x

/--
Definition of `stalkToFiber` / `stalkToFiber` 的定义

English:
definition stalkToFiber
  signature: (x : X)
  body: TopCat.stalkToFiber (Sheafify.isLocallyGerm F) x

中文:
定义 stalkToFiber
  签名: (x : X)
  定义体: TopCat.stalkToFiber (Sheafify.isLocallyGerm F) x

Depends on / 依赖: Sheafify, Sheafify.isLocallyGerm, TopCat, TopCat.stalkToFiber, isLocallyGerm, stalkToFiber
-/
def stalkToFiber (x : X) : F.sheafify.presheaf.stalk x ⟶ F.stalk x :=
  TopCat.stalkToFiber (Sheafify.isLocallyGerm F) x

/--
theorem `stalkToFiber_surjective` / 定理 `stalkToFiber_surjective`

English:
theorem stalkToFiber_surjective
  given: (x : X)
  statement: Function.Surjective (F.stalkToFiber x)
  proof: by
  apply TopCat.stalkToFiber_surjective
  intro t
  obtain ⟨U, m, s, rfl⟩ := F.exists_germ_eq t
  use ⟨U, m⟩
  fconstructor
  · exact fun y => F.germ _ _ y.2 s
  · exact ⟨PrelocalPredicate.sheafifyOf ⟨s, fun _ => rfl⟩, rfl⟩

中文:
定理 stalkToFiber_surjective
  条件: (x : X)
  结论: Function.Surjective (F.stalkToFiber x)
  证明: by
  apply TopCat.stalkToFiber_surjective
  intro t
  obtain ⟨U, m, s, rfl⟩ := F.exists_germ_eq t
  use ⟨U, m⟩
  fconstructor
  · exact fun y => F.germ _ _ y.2 s
  · exact ⟨PrelocalPredicate.sheafifyOf ⟨s, fun _ => rfl⟩, rfl⟩

Depends on / 依赖: F.exists_germ_eq, F.germ, PrelocalPredicate, PrelocalPredicate.sheafifyOf, TopCat, TopCat.stalkToFiber_surjective, exists_germ_eq, fconstructor, sheafifyOf, stalkToFiber_surjective
-/
theorem stalkToFiber_surjective (x : X) : Function.Surjective (F.stalkToFiber x) := by
  apply TopCat.stalkToFiber_surjective
  intro t
  obtain ⟨U, m, s, rfl⟩ := F.exists_germ_eq t
  use ⟨U, m⟩
  fconstructor
  · exact fun y => F.germ _ _ y.2 s
  · exact ⟨PrelocalPredicate.sheafifyOf ⟨s, fun _ => rfl⟩, rfl⟩

/--
theorem `stalkToFiber_injective` / 定理 `stalkToFiber_injective`

English:
theorem stalkToFiber_injective
  given: (x : X)
  statement: Function.Injective (F.stalkToFiber x)
  proof: by
  apply TopCat.stalkToFiber_injective
  intro U V fU hU fV hV e
  rcases hU ⟨x, U.2⟩ with ⟨U', mU, iU, gU, wU⟩
  rcases hV ⟨x, V.2⟩ with ⟨V', mV, iV, gV, wV⟩
  have wUx := wU ⟨x, mU⟩
  dsimp at wUx; rw [wUx] at e; clear wUx
  have wVx := wV ⟨x, mV⟩
  dsimp at wVx; rw [wVx] at e; clear wVx
  rcase

中文:
定理 stalkToFiber_injective
  条件: (x : X)
  结论: Function.Injective (F.stalkToFiber x)
  证明: by
  apply TopCat.stalkToFiber_injective
  intro U V fU hU fV hV e
  rcases hU ⟨x, U.2⟩ with ⟨U', mU, iU, gU, wU⟩
  rcases hV ⟨x, V.2⟩ with ⟨V', mV, iV, gV, wV⟩
  have wUx := wU ⟨x, mU⟩
  dsimp at wUx; rw [wUx] at e; clear wUx
  have wVx := wV ⟨x, mV⟩
  dsimp at wVx; rw [wVx] at e; clear wVx
  rcase

Depends on / 依赖: F.germ_eq, F.map, Opens.infLE, Opens.infLERight, TopCat, TopCat.stalkToFiber_injective, U.val, germ_eq, infLERight, stalkToFiber_injective
-/
theorem stalkToFiber_injective (x : X) : Function.Injective (F.stalkToFiber x) := by
  apply TopCat.stalkToFiber_injective
  intro U V fU hU fV hV e
  rcases hU ⟨x, U.2⟩ with ⟨U', mU, iU, gU, wU⟩
  rcases hV ⟨x, V.2⟩ with ⟨V', mV, iV, gV, wV⟩
  have wUx := wU ⟨x, mU⟩
  dsimp at wUx; rw [wUx] at e; clear wUx
  have wVx := wV ⟨x, mV⟩
  dsimp at wVx; rw [wVx] at e; clear wVx
  rcases F.germ_eq x mU mV gU gV e with ⟨W, mW, iU', iV', (e' : F.map iU'.op gU = F.map iV'.op gV)⟩
  use ⟨W ⊓ (U' ⊓ V'), ⟨mW, mU, mV⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · change W ⊓ (U' ⊓ V') ⟶ U.val
    exact Opens.infLERight _ _ ≫ Opens.infLELeft _ _ ≫ iU
  · change W ⊓ (U' ⊓ V') ⟶ V.val
    exact Opens.infLERight _ _ ≫ Opens.infLERight _ _ ≫ iV
  · intro w
    specialize wU ⟨w.1, w.2.2.1⟩
    specialize wV ⟨w.1, w.2.2.2⟩
refine wU.trans .trans ?_ wV.symm
    rw [← F.germ_res iU' w w.2.1]; rw [← F.germ_res iV' w w.2.1]; rw [CategoryTheory.types_comp_apply]; rw [CategoryTheory.types_comp_apply]; rw [e']

/--
Definition of `sheafifyStalkIso` / `sheafifyStalkIso` 的定义

English:
definition sheafifyStalkIso
  signature: (x : X)
  body: (Equiv.ofBijective _ ⟨stalkToFiber_injective _ _, stalkToFiber_surjective _ _⟩).toIso

中文:
定义 sheafifyStalkIso
  签名: (x : X)
  定义体: (Equiv.ofBijective _ ⟨stalkToFiber_injective _ _, stalkToFiber_surjective _ _⟩).toIso

Depends on / 依赖: Equiv.ofBijective, ofBijective, stalkToFiber_injective, stalkToFiber_surjective
-/
def sheafifyStalkIso (x : X) : F.sheafify.presheaf.stalk x ≅ F.stalk x :=
  (Equiv.ofBijective _ ⟨stalkToFiber_injective _ _, stalkToFiber_surjective _ _⟩).toIso

-- PROJECT functoriality, and that sheafification is the left adjoint of the forgetful functor.
end TopCat.Presheaf

namespace TopCat.Presheaf

variable (p₀ : X) (C : Type u) [Category.{v} C] [Limits.HasColimits C]
  [Limits.HasTerminal C] (𝓕 : Presheaf C X) [HasWeakSheafify (Opens.grothendieckTopology X) C]

/--
theorem `stalkFunctor_map_unit_toSheafify_isIso` / 定理 `stalkFunctor_map_unit_toSheafify_isIso`

English:
theorem stalkFunctor_map_unit_toSheafify_isIso
  statement: IsIso ((Presheaf.stalkFunctor C p₀).map
  proof: by
  classical
  exact Adjunction.isIso_map_unit_of_isLeftAdjoint_comp (sheafificationAdjunction _ C)
    (skyscraperSheafForgetAdjunction p₀)

中文:
定理 stalkFunctor_map_unit_toSheafify_isIso
  结论: IsIso ((Presheaf.stalkFunctor C p₀).map
  证明: by
  classical
  exact Adjunction.isIso_map_unit_of_isLeftAdjoint_comp (sheafificationAdjunction _ C)
    (skyscraperSheafForgetAdjunction p₀)

Depends on / 依赖: Adjunction, Adjunction.isIso_map_unit_of_isLeftAdjoint_comp, classical, isIso_map_unit_of_isLeftAdjoint_comp, sheafificationAdjunction, skyscraperSheafForgetAdjunction
-/
theorem stalkFunctor_map_unit_toSheafify_isIso : IsIso ((Presheaf.stalkFunctor C p₀).map
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) 𝓕)) := by
  classical
  exact Adjunction.isIso_map_unit_of_isLeftAdjoint_comp (sheafificationAdjunction _ C)
    (skyscraperSheafForgetAdjunction p₀)

end TopCat.Presheaf
