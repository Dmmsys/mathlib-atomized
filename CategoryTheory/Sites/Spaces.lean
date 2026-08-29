/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.Pretopology
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.Topology.Sets.OpenCover

/-!
# Grothendieck topology on a topological space

Define the Grothendieck topology and the pretopology associated to a topological space, and show
that the pretopology induces the topology.

The covering (pre)sieves on `X` are those for which the union of domains contains `X`.

## Tags

site, Grothendieck topology, space

## References

* [nLab, *Grothendieck topology*](https://ncatlab.org/nlab/show/Grothendieck+topology)
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]

## Implementation notes

We define the two separately, rather than defining the Grothendieck topology as that generated
by the pretopology for the purpose of having nice definitional properties for the sieves.
-/

@[expose] public section


universe u

namespace Opens

variable (T : Type u) [TopologicalSpace T]

open CategoryTheory TopologicalSpace CategoryTheory.Limits

/--
Definition of `grothendieckTopology` / `grothendieckTopology` 的定义

English:
definition grothendieckTopology
  signature: : GrothendieckTopology (Opens T) where
  body: {S | forall x in X, exists (U : Opens T) (f : U ⟶ X), S f ∧ x in U}
  top_mem' _ _ hx := ⟨_, 𝟙 _, trivial, hx⟩
  pullback_stable' X Y S f hf y hy := by
    rcases hf y (f.le hy) with ⟨U, g, hg, hU⟩
    refine ⟨U ⊓ Y, homOfLE inf_le_right, ?_, hU, hy⟩
    apply S.downward_closed hg (homOfLE inf_le_left)
  transitive' X S hS R hR x hx := by
    rcases hS x hx with ⟨U, f, hf, hU⟩
    rcases hR hf _ hU with ⟨V, g, hg, hV⟩
    exact ⟨_, g ≫ f, hg, hV⟩

中文:
定义 grothendieckTopology
  签名: : Grothendieck拓扑 (Opens T) where
  定义体: {S | forall x in X, exists (U : Opens T) (f : U ⟶ X), S f ∧ x in U}
  top_mem' _ _ hx := ⟨_, 𝟙 _, trivial, hx⟩
  pullback_stable' X Y S f hf y hy := by
    rcases hf y (f.le hy) with ⟨U, g, hg, hU⟩
    refine ⟨U ⊓ Y, homOfLE inf_le_right, ?_, hU, hy⟩
    apply S.downward_closed hg (homOfLE inf_le_left)
  transitive' X S hS R hR x hx := by
    rcases hS x hx with ⟨U, f, hf, hU⟩
    rcases hR hf _ hU with ⟨V, g, hg, hV⟩
    exact ⟨_, g ≫ f, hg, hV⟩
-/
def grothendieckTopology : GrothendieckTopology (Opens T) where
  sieves X := {S | forall x in X, exists (U : Opens T) (f : U ⟶ X), S f ∧ x in U}
  top_mem' _ _ hx := ⟨_, 𝟙 _, trivial, hx⟩
  pullback_stable' X Y S f hf y hy := by
    rcases hf y (f.le hy) with ⟨U, g, hg, hU⟩
    refine ⟨U ⊓ Y, homOfLE inf_le_right, ?_, hU, hy⟩
    apply S.downward_closed hg (homOfLE inf_le_left)
  transitive' X S hS R hR x hx := by
    rcases hS x hx with ⟨U, f, hf, hU⟩
    rcases hR hf _ hU with ⟨V, g, hg, hV⟩
    exact ⟨_, g ≫ f, hg, hV⟩

/--
lemma `mem_grothendieckTopology` / 引理 `mem_grothendieckTopology`

English:
lemma mem_grothendieckTopology
  given: {U : Opens T} {S : Sieve U}
  proof: .rfl

中文:
引理 mem_grothendieckTopology
  条件: {U : Opens T} {S : 筛 U}
  证明: .rfl
-/
lemma mem_grothendieckTopology {U : Opens T} {S : Sieve U} :
    S in Opens.grothendieckTopology T U ↔ forall x in U, exists (V : _) (f : V ⟶ U), S f ∧ x in V := .rfl

/--
Definition of `pretopology` / `pretopology` 的定义

English:
definition pretopology
  signature: : Pretopology (Opens T) where
  body: {R | forall x in X, exists (U : _) (f : U ⟶ X), R f ∧ x in U}
  has_isos _ _ f _ _ hx := ⟨_, _, Presieve.singleton_self _, (inv f).le hx⟩
  pullbacks X Y f S hS x hx := by
    rcases hS _ (f.le hx) with ⟨U, g, hg, hU⟩
    refine ⟨_, _, Presieve.pullbackArrows.mk _ _ hg, ?_⟩
    have : U ⊓ Y <= pullback g f :=
      leOfHom (pullback.lift (homOfLE inf_le_left) (homOfLE inf_le_right) rfl)
    apply this ⟨hU, hx⟩
  transitive X S Ti hS hTi x hx := by
    rcases hS x hx with ⟨U, f, hf, hU⟩
    rcases hTi f hf x hU with ⟨V, g, hg, hV⟩
    exact ⟨_, _, ⟨_, g, f, hf, hg, rfl⟩, hV⟩

中文:
定义 pretopology
  签名: : Pretopology (Opens T) where
  定义体: {R | forall x in X, exists (U : _) (f : U ⟶ X), R f ∧ x in U}
  has_isos _ _ f _ _ hx := ⟨_, _, Presieve.singleton_self _, (inv f).le hx⟩
  pullbacks X Y f S hS x hx := by
    rcases hS _ (f.le hx) with ⟨U, g, hg, hU⟩
    refine ⟨_, _, Presieve.pullbackArrows.mk _ _ hg, ?_⟩
    have : U ⊓ Y <= pullback g f :=
      leOfHom (pullback.lift (homOfLE inf_le_left) (homOfLE inf_le_right) rfl)
    apply this ⟨hU, hx⟩
  transitive X S Ti hS hTi x hx := by
    rcases hS x hx with ⟨U, f, hf, hU⟩
    rcases hTi f hf x hU with ⟨V, g, hg, hV⟩
    exact ⟨_, _, ⟨_, g, f, hf, hg, rfl⟩, hV⟩
-/
def pretopology : Pretopology (Opens T) where
  coverings X := {R | forall x in X, exists (U : _) (f : U ⟶ X), R f ∧ x in U}
  has_isos _ _ f _ _ hx := ⟨_, _, Presieve.singleton_self _, (inv f).le hx⟩
  pullbacks X Y f S hS x hx := by
    rcases hS _ (f.le hx) with ⟨U, g, hg, hU⟩
    refine ⟨_, _, Presieve.pullbackArrows.mk _ _ hg, ?_⟩
    have : U ⊓ Y <= pullback g f :=
      leOfHom (pullback.lift (homOfLE inf_le_left) (homOfLE inf_le_right) rfl)
    apply this ⟨hU, hx⟩
  transitive X S Ti hS hTi x hx := by
    rcases hS x hx with ⟨U, f, hf, hU⟩
    rcases hTi f hf x hU with ⟨V, g, hg, hV⟩
    exact ⟨_, _, ⟨_, g, f, hf, hg, rfl⟩, hV⟩

/-- The pretopology associated to a space is the largest pretopology that
generates the Grothendieck topology associated to the space. -/
@[simp]
/--
theorem `toPretopology_grothendieckTopology` / 定理 `toPretopology_grothendieckTopology`

English:
theorem toPretopology_grothendieckTopology
  proof: by
  apply le_antisymm
  · intro X R hR x hx
    rcases hR x hx with ⟨U, f, ⟨V, g₁, g₂, hg₂, _⟩, hU⟩
    exact ⟨V, g₂, hg₂, g₁.le hU⟩
  · intro X R hR x hx
    rcases hR x hx with ⟨U, f, hf, hU⟩
    exact ⟨U, f, Sieve.le_generate R U _ hf, hU⟩

中文:
定理 toPretopology_grothendieckTopology
  证明: by
  apply le_antisymm
  · intro X R hR x hx
    rcases hR x hx with ⟨U, f, ⟨V, g₁, g₂, hg₂, _⟩, hU⟩
    exact ⟨V, g₂, hg₂, g₁.le hU⟩
  · intro X R hR x hx
    rcases hR x hx with ⟨U, f, hf, hU⟩
    exact ⟨U, f, Sieve.le_generate R U _ hf, hU⟩

Depends on / 依赖: Sieve.le_generate, le_antisymm, le_generate
-/
theorem toPretopology_grothendieckTopology :
    (Opens.grothendieckTopology T).toPretopology = Opens.pretopology T := by
  apply le_antisymm
  · intro X R hR x hx
    rcases hR x hx with ⟨U, f, ⟨V, g₁, g₂, hg₂, _⟩, hU⟩
    exact ⟨V, g₂, hg₂, g₁.le hU⟩
  · intro X R hR x hx
    rcases hR x hx with ⟨U, f, hf, hU⟩
    exact ⟨U, f, Sieve.le_generate R U _ hf, hU⟩

/-- The pretopology associated to a space induces the Grothendieck topology associated to the space.
-/
@[simp]
/--
theorem `pretopology_toGrothendieck` / 定理 `pretopology_toGrothendieck`

English:
theorem pretopology_toGrothendieck
  proof: by
  rw [← toPretopology_grothendieckTopology]
  apply (Pretopology.gi (Opens T)).l_u_eq

中文:
定理 pretopology_toGrothendieck
  证明: by
  rw [← toPretopology_grothendieckTopology]
  apply (Pretopology.gi (Opens T)).l_u_eq

Depends on / 依赖: Pretopology, Pretopology.gi, l_u_eq, toPretopology_grothendieckTopology
-/
theorem pretopology_toGrothendieck :
    (Opens.pretopology T).toGrothendieck = Opens.grothendieckTopology T := by
  rw [← toPretopology_grothendieckTopology]
  apply (Pretopology.gi (Opens T)).l_u_eq

/--
lemma `coversTop_iff` / 引理 `coversTop_iff`

English:
lemma coversTop_iff
  given: {ι : Type*} (U : ι -> Opens T)
  proof: by
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ ⊤ isTerminalTop]
  dsimp [Opens.grothendieckTopology]
  simp only [IsOpenCover, eq_top_iff, SetLike.le_def, exists_and_right, Opens.mem_top,
    Opens.mem_iSup, forall_const]
  refine ⟨fun h x => ?_, fun hU x hx => ?_⟩
  · obtain ⟨V, ⟨u, ⟨i, ⟨hi⟩⟩⟩, hx⟩ := h x trivial
    use i, leOfHom hi hx
  · obtain ⟨i, hi⟩ := hU (x := x)
    exact ⟨U i, ⟨homOfLE le_top, ⟨i, ⟨𝟙 _⟩⟩⟩, hi⟩

中文:
引理 coversTop_iff
  条件: {ι : 类型} (U : ι -> Opens T)
  证明: by
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ ⊤ isTerminalTop]
  dsimp [Opens.grothendieckTopology]
  simp only [IsOpenCover, eq_top_iff, SetLike.le_def, exists_and_right, Opens.mem_top,
    Opens.mem_iSup, forall_const]
  refine ⟨fun h x => ?_, fun hU x hx => ?_⟩
  · obtain ⟨V, ⟨u, ⟨i, ⟨hi⟩⟩⟩, hx⟩ := h x trivial
    use i, leOfHom hi hx
  · obtain ⟨i, hi⟩ := hU (x := x)
    exact ⟨U i, ⟨homOfLE le_top, ⟨i, ⟨𝟙 _⟩⟩⟩, hi⟩

Depends on / 依赖: GrothendieckTopology, GrothendieckTopology.coversTop_iff_of_isTerminal, IsOpenCover, Opens.grothendieckTopology, Opens.mem_iSup, Opens.mem_top, SetLike, SetLike.le_def, coversTop_iff_of_isTerminal, eq_top_iff, exists_and_right, forall_const, grothendieckTopology, homOfLE, isTerminalTop, leOfHom, le_def, le_top, mem_iSup, mem_top
-/
lemma coversTop_iff {ι : Type*} (U : ι -> Opens T) :
    (grothendieckTopology T).CoversTop U ↔ IsOpenCover U := by
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ ⊤ isTerminalTop]
  dsimp [Opens.grothendieckTopology]
  simp only [IsOpenCover, eq_top_iff, SetLike.le_def, exists_and_right, Opens.mem_top,
    Opens.mem_iSup, forall_const]
  refine ⟨fun h x => ?_, fun hU x hx => ?_⟩
  · obtain ⟨V, ⟨u, ⟨i, ⟨hi⟩⟩⟩, hx⟩ := h x trivial
    use i, leOfHom hi hx
  · obtain ⟨i, hi⟩ := hU (x := x)
    exact ⟨U i, ⟨homOfLE le_top, ⟨i, ⟨𝟙 _⟩⟩⟩, hi⟩

end Opens
