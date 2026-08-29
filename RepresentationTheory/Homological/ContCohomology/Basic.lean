/-
Copyright (c) 2026 Richard Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Hill, Andrew Yang, Edison Xie
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Topology.Homology
public import Mathlib.RepresentationTheory.Continuous.TopRep

/-!

# Continuous cohomology

We define continuous cohomology as the homology of the homogeneous cochain complex.

## Implementation details

We define homogeneous cochains as `g`-invariant continuous function in `C(G, C(G,...,C(G, M)))`
instead of the usual `C(Gⁿ, M)` to allow more general topological groups other than locally compact
ones. For this to work, we also work in `TopRep k G`, where the `G` action on `M`
is only continuous on `M`, and not necessarily continuous in both variables, because the `G` action
on `C(G, M)` might not be continuous on both variables even if it is on `M`.

For the differential map, instead of a finite sum we use the inductive definition
`d₋₁ : M → C(G, M) := const : m ↦ g ↦ m` and
`dₙ₊₁ : C(G, _) → C(G, C(G, _)) := const - C(G, dₙ) : f ↦ g ↦ f - dₙ (f (g))`
See `TopRep.d`.

## Main definition
- `TopRep.homogeneousCochains`:
  The functor taking an `R`-linear `G`-representation to the complex of homogeneous cochains.
- `continuousCohomology`:
  The functor taking an `R`-linear `G`-representation to its `n`-th continuous cohomology.

## TODO
- Show that it coincides with `groupCohomology` for discrete groups.
- Give the usual description of cochains in terms of `n`-ary functions for locally compact groups.
- Show that short exact sequences induce long exact sequences in certain scenarios.
-/

@[expose] public section

variable {k G : Type*} [Ring k] [Group G] [TopologicalSpace k]
  [TopologicalSpace G] [IsTopologicalGroup G]

open CategoryTheory ContRepresentation Limits

namespace TopRep

/--
Definition of `resolutionX` / `resolutionX` 的定义

English:
abbreviation resolutionX
  signature: (X : TopRep k G)

中文:
缩写 resolutionX
  签名: (X : TopRep k G)
-/
abbrev resolutionX (X : TopRep k G) : Nat -> TopRep k G
  | 0 => X
  | n + 1 => (resolutionX X n).coind₁

/--
Definition of `d` / `d` 的定义

English:
definition d
  signature: (X : TopRep k G)

中文:
定义 d
  签名: (X : TopRep k G)
-/
def d (X : TopRep k G) : (n : Nat) -> resolutionX X n ⟶ resolutionX X (n + 1)
  | 0 => ofHom X.ρ.coind₁ι
  | n + 1 => ofHom (resolutionX X (n + 1)).ρ.coind₁ι - (coind₁Functor k G).map (d X n)

/--
lemma `d_zero` / 引理 `d_zero`

English:
lemma d_zero
  given: (X : TopRep k G)
  statement: d X 0 = ofHom X.ρ.coind₁ι
  proof: rfl

中文:
引理 d_zero
  条件: (X : TopRep k G)
  结论: d X 0 = ofHom X.ρ.coind₁ι
  证明: rfl
-/
lemma d_zero (X : TopRep k G) : d X 0 = ofHom X.ρ.coind₁ι := rfl

/--
lemma `d_succ` / 引理 `d_succ`

English:
lemma d_succ
  given: (X : TopRep k G) (n : Nat)
  proof: rfl

中文:
引理 d_succ
  条件: (X : TopRep k G) (n : 自然数)
  证明: rfl
-/
lemma d_succ (X : TopRep k G) (n : Nat) :
    d X (n + 1) = ofHom (resolutionX X (n + 1)).ρ.coind₁ι - (coind₁Functor k G).map (d X n) :=
  rfl

/--
lemma `hom_d_succ` / 引理 `hom_d_succ`

English:
lemma hom_d_succ
  given: (X : TopRep k G) (n : Nat)
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 hom_d_succ
  条件: (X : TopRep k G) (n : 自然数)
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma hom_d_succ (X : TopRep k G) (n : Nat) :
    (d X (n + 1)).hom = (resolutionX X (n + 1)).ρ.coind₁ι -
      ContRepresentation.coind₁Map (d X n).hom :=
  rfl

@[reassoc (attr := simp)]
/--
lemma `d_comp_d` / 引理 `d_comp_d`

English:
lemma d_comp_d
  given: (X : TopRep k G) (n : Nat)
  statement: d X n ≫ d X (n + 1) = 0
  proof: by
  induction n with
  | zero =>
    ext
    simp [d_succ, ContIntertwiningMap.toContinuousLinearMap_apply, d_zero, hom_sub]
  | succ n ih =>
    rw [d_succ _ (n + 1)]; rw [Preadditive.comp_sub]
    nth_rw 2 [d_succ]
    rw [Preadditive.sub_comp]; rw [← Functor.map_comp]; rw [ih]; rw [Functor.map_zero]; rw [sub_zero]; rw [sub_eq_zero]
    rfl

中文:
引理 d_comp_d
  条件: (X : TopRep k G) (n : 自然数)
  结论: d X n ≫ d X (n + 1) = 0
  证明: by
  induction n with
  | zero =>
    ext
    simp [d_succ, ContIntertwiningMap.toContinuousLinearMap_apply, d_zero, hom_sub]
  | succ n ih =>
    rw [d_succ _ (n + 1)]; rw [Preadditive.comp_sub]
    nth_rw 2 [d_succ]
    rw [Preadditive.sub_comp]; rw [← Functor.map_comp]; rw [ih]; rw [Functor.map_zero]; rw [sub_zero]; rw [sub_eq_zero]
    rfl

Depends on / 依赖: ContIntertwiningMap, ContIntertwiningMap.toContinuousLinearMap_apply, Functor, Functor.map_comp, Functor.map_zero, Preadditive, Preadditive.comp_sub, Preadditive.sub_comp, comp_sub, d_succ, d_zero, hom_sub, map_comp, map_zero, nth_rw, sub_comp, sub_eq_zero, sub_zero, toContinuousLinearMap_apply
-/
lemma d_comp_d (X : TopRep k G) (n : Nat) : d X n ≫ d X (n + 1) = 0 := by
  induction n with
  | zero =>
    ext
    simp [d_succ, ContIntertwiningMap.toContinuousLinearMap_apply, d_zero, hom_sub]
  | succ n ih =>
    rw [d_succ _ (n + 1)]; rw [Preadditive.comp_sub]
    nth_rw 2 [d_succ]
    rw [Preadditive.sub_comp]; rw [← Functor.map_comp]; rw [ih]; rw [Functor.map_zero]; rw [sub_zero]; rw [sub_eq_zero]
    rfl

/--
Definition of `resolution` / `resolution` 的定义

English:
abbreviation resolution
  signature: (X : TopRep k G)
  body: CochainComplex.of (resolutionX X) (d X) (d_comp_d X)

中文:
缩写 resolution
  签名: (X : TopRep k G)
  定义体: CochainComplex.of (resolutionX X) (d X) (d_comp_d X)

Depends on / 依赖: CochainComplex, CochainComplex.of, d_comp_d, resolutionX
-/
abbrev resolution (X : TopRep k G) : CochainComplex (TopRep k G) Nat :=
  CochainComplex.of (resolutionX X) (d X) (d_comp_d X)

/--
Definition of `resolution'X` / `resolution'X` 的定义

English:
abbreviation resolution'X
  signature: (X : TopRep k G) (n : Nat)
  body: resolutionX X (n + 1)

中文:
缩写 resolution'X
  签名: (X : TopRep k G) (n : 自然数)
  定义体: resolutionX X (n + 1)

Depends on / 依赖: resolutionX
-/
abbrev resolution'X (X : TopRep k G) (n : Nat) : TopRep k G := resolutionX X (n + 1)

/-- The shifted boundary map of the resolution. -/
@[implicit_reducible]
/--
Definition of `resolution'd` / `resolution'd` 的定义

English:
definition resolution'd
  signature: (X : TopRep k G) (n : Nat)
  body: d X (n + 1)

中文:
定义 resolution'd
  签名: (X : TopRep k G) (n : 自然数)
  定义体: d X (n + 1)
-/
def resolution'd (X : TopRep k G) (n : Nat) :
    resolution'X X n ⟶ resolution'X X (n + 1) := d X (n + 1)

/--
lemma `resolution'd_eq` / 引理 `resolution'd_eq`

English:
lemma resolution'd_eq
  given: (X : TopRep k G) (n : Nat)
  proof: rfl

中文:
引理 resolution'd_eq
  条件: (X : TopRep k G) (n : 自然数)
  证明: rfl
-/
lemma resolution'd_eq (X : TopRep k G) (n : Nat) :
    resolution'd X n = d X (n + 1) := rfl

/--
Definition of `resolution'` / `resolution'` 的定义

English:
abbreviation resolution'
  signature: (X : TopRep k G)
  body: CochainComplex.of (resolution'X X)
    (resolution'd X) (fun n => d_comp_d X (n + 1))

中文:
缩写 resolution'
  签名: (X : TopRep k G)
  定义体: CochainComplex.of (resolution'X X)
    (resolution'd X) (fun n => d_comp_d X (n + 1))
-/
abbrev resolution' (X : TopRep k G) : CochainComplex (TopRep k G) Nat :=
  CochainComplex.of (resolution'X X)
    (resolution'd X) (fun n => d_comp_d X (n + 1))

set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Functor.mapHomologicalComplex

/--
Definition of `homogeneousCochains` / `homogeneousCochains` 的定义

English:
abbreviation homogeneousCochains
  signature: (X : TopRep k G)
  body: ((invariantsFunctor k G).mapHomologicalComplex _).obj (resolution' X)

中文:
缩写 homogeneousCochains
  签名: (X : TopRep k G)
  定义体: ((invariantsFunctor k G).mapHomologicalComplex _).obj (resolution' X)

Depends on / 依赖: invariantsFunctor, mapHomologicalComplex, resolution
-/
abbrev homogeneousCochains (X : TopRep k G) :
    CochainComplex (TopModuleCat k) Nat :=
  ((invariantsFunctor k G).mapHomologicalComplex _).obj (resolution' X)

/--
lemma `homogeneousCochains.d_eq` / 引理 `homogeneousCochains.d_eq`

English:
lemma homogeneousCochains.d_eq
  given: (X : TopRep k G) (i : Nat)
  proof: by
  dsimp only
  rw [← resolution'd_eq]; rw [CochainComplex.of_d]

中文:
引理 homogeneousCochains.d_eq
  条件: (X : TopRep k G) (i : 自然数)
  证明: by
  dsimp only
  rw [← resolution'd_eq]; rw [CochainComplex.of_d]

Depends on / 依赖: CochainComplex, CochainComplex.of_d, d_eq, of_d, resolution
-/
lemma homogeneousCochains.d_eq (X : TopRep k G) (i : Nat) :
    (homogeneousCochains X).d i (i + 1) =
      (invariantsFunctor k G).map (d X (i + 1)) := by
  dsimp only
  rw [← resolution'd_eq]; rw [CochainComplex.of_d]

/--
lemma `homogeneousCochains.d_apply` / 引理 `homogeneousCochains.d_apply`

English:
lemma homogeneousCochains.d_apply
  statement: (X : TopRep k G) (i : Nat)
  proof: by
  rw [homogeneousCochains.d_eq]
  dsimp [ContIntertwiningMap.mapInvariants_apply]

中文:
引理 homogeneousCochains.d_apply
  结论: (X : TopRep k G) (i : 自然数)
  证明: by
  rw [homogeneousCochains.d_eq]
  dsimp [ContIntertwiningMap.mapInvariants_apply]

Depends on / 依赖: ContIntertwiningMap, ContIntertwiningMap.mapInvariants_apply, d_eq, homogeneousCochains, homogeneousCochains.d_eq, mapInvariants_apply
-/
lemma homogeneousCochains.d_apply (X : TopRep k G) (i : Nat)
    (σ : (homogeneousCochains X).X i) :
    ((homogeneousCochains X).d i (i + 1)).hom σ = (d X (i + 1)).hom σ := by
  rw [homogeneousCochains.d_eq]
  dsimp [ContIntertwiningMap.mapInvariants_apply]

/--
Definition of `_root_.continuousCohomology` / `_root_.continuousCohomology` 的定义

English:
abbreviation _root_.continuousCohomology
  signature: (n : Nat) (A : TopRep k G)
  body: (homogeneousCochains A).homology n

中文:
缩写 _root_.continuousCohomology
  签名: (n : 自然数) (A : TopRep k G)
  定义体: (homogeneousCochains A).homology n

Depends on / 依赖: homogeneousCochains, homology, map_add_le_max, map_mul, map_one, map_zero
-/
noncomputable abbrev _root_.continuousCohomology (n : Nat) (A : TopRep k G) :
    TopModuleCat k := (homogeneousCochains A).homology n

end TopRep

namespace ContinuousCohomology

open TopRep

/--
Definition of `cocycles` / `cocycles` 的定义

English:
abbreviation cocycles
  signature: (A : TopRep k G) (n : Nat)
  body: (homogeneousCochains A).cycles n

中文:
缩写 cocycles
  签名: (A : TopRep k G) (n : 自然数)
  定义体: (homogeneousCochains A).cycles n

Depends on / 依赖: cycles, homogeneousCochains
-/
noncomputable abbrev cocycles (A : TopRep k G) (n : Nat) :
    TopModuleCat k := (homogeneousCochains A).cycles n

/--
Definition of `π` / `π` 的定义

English:
abbreviation π
  signature: (A : TopRep k G) (n : Nat)
  body: (homogeneousCochains A).homologyπ n

中文:
缩写 π
  签名: (A : TopRep k G) (n : 自然数)
  定义体: (homogeneousCochains A).homologyπ n

Depends on / 依赖: homogeneousCochains
-/
noncomputable abbrev π (A : TopRep k G) (n : Nat) := (homogeneousCochains A).homologyπ n

end ContinuousCohomology
