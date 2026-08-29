/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, Richard Hill
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic

/-!
# Functoriality of continuous cohomology

Given topological groups `G` and `H`, a continuous group homomorphism `φ : H →ₜ* G`, a topological
representation `X` of `G`, a topological representation `Y` of `H`, and a morphism of topological
`H`-representations `f : res φ X ⟶ Y`, we construct a cochain map
`homogeneousCochains X ⟶ homogeneousCochains Y` and hence maps on continuous cohomology
`Hⁿ(G, X) ⟶ Hⁿ(H, Y)`.

## Main definitions

* `ContinuousCohomology.cochainsMap φ f` : the cochain map
  `homogeneousCochains X ⟶ homogeneousCochains Y` induced by `φ : H →ₜ* G` and
  `f : res φ X ⟶ Y`, sending an invariant function `σ : C(G, C(G, ⋯))` to `f ∘ σ ∘ φ`.
* `ContinuousCohomology.map φ f n` : the induced map `Hⁿ(G, X) ⟶ Hⁿ(H, Y)` on continuous
  cohomology.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace ContinuousCohomology

open TopRep ContRepresentation

variable {k : Type u} {G H K : Type v} [Ring k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  {X : TopRep k G} {Y : TopRep k H} {Z : TopRep k K}

set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Functor.mapHomologicalComplex

/--
Definition of `resolutionMap` / `resolutionMap` 的定义

English:
definition resolutionMap
  signature: (φ : H ->ₜ* G) (f : res φ X ⟶ Y)

中文:
定义 resolutionMap
  签名: (φ : H ->ₜ* G) (f : res φ X ⟶ Y)
-/
def resolutionMap (φ : H ->ₜ* G) (f : res φ X ⟶ Y) :
    (i : Nat) -> res φ (resolutionX X i) ⟶ resolutionX Y i
  | 0 => f
  | i + 1 => ofHom (coind₁ResMap φ (resolutionMap φ f i).hom)

@[simp]
/--
lemma `resolutionMap_zero` / 引理 `resolutionMap_zero`

English:
lemma resolutionMap_zero
  given: (φ : H ->ₜ* G) (f : res φ X ⟶ Y)
  proof: rfl

中文:
引理 resolutionMap_zero
  条件: (φ : H ->ₜ* G) (f : res φ X ⟶ Y)
  证明: rfl
-/
lemma resolutionMap_zero (φ : H ->ₜ* G) (f : res φ X ⟶ Y) :
    resolutionMap φ f 0 = f := rfl

/--
lemma `resolutionMap_succ` / 引理 `resolutionMap_succ`

English:
lemma resolutionMap_succ
  given: (φ : H ->ₜ* G) (f : res φ X ⟶ Y) (i : Nat)
  proof: rfl

中文:
引理 resolutionMap_succ
  条件: (φ : H ->ₜ* G) (f : res φ X ⟶ Y) (i : 自然数)
  证明: rfl
-/
lemma resolutionMap_succ (φ : H ->ₜ* G) (f : res φ X ⟶ Y) (i : Nat) :
    resolutionMap φ f (i + 1) = ofHom (coind₁ResMap φ (resolutionMap φ f i).hom) := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `resolutionMap_id` / 引理 `resolutionMap_id`

English:
lemma resolutionMap_id
  given: (X : TopRep k G) (i : Nat)
  proof: by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [resolutionMap_succ]; rw [ih]
    ext F x
    rfl

中文:
引理 resolutionMap_id
  条件: (X : TopRep k G) (i : 自然数)
  证明: by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [resolutionMap_succ]; rw [ih]
    ext F x
    rfl

Depends on / 依赖: resolutionMap_succ
-/
lemma resolutionMap_id (X : TopRep k G) (i : Nat) :
    resolutionMap (ContinuousMonoidHom.id G) (𝟙 X) i = 𝟙 (resolutionX X i) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [resolutionMap_succ]; rw [ih]
    ext F x
    rfl

/--
lemma `resolutionMap_comp` / 引理 `resolutionMap_comp`

English:
lemma resolutionMap_comp
  statement: (φ : H ->ₜ* G) (ψ : K ->ₜ* H) (f : res φ X ⟶ Y) (g : res ψ Y ⟶ Z)
  proof: by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [resolutionMap_succ]; rw [resolutionMap_succ]; rw [resolutionMap_succ]; rw [ih]
    ext F x
    rfl

中文:
引理 resolutionMap_comp
  结论: (φ : H ->ₜ* G) (ψ : K ->ₜ* H) (f : res φ X ⟶ Y) (g : res ψ Y ⟶ Z)
  证明: by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [resolutionMap_succ]; rw [resolutionMap_succ]; rw [resolutionMap_succ]; rw [ih]
    ext F x
    rfl

Depends on / 依赖: resFunctor
-/
lemma resolutionMap_comp (φ : H ->ₜ* G) (ψ : K ->ₜ* H) (f : res φ X ⟶ Y) (g : res ψ Y ⟶ Z)
    (i : Nat) :
    resolutionMap (φ.comp ψ) (X := X) ((resFunctor (ψ : K ->* H)).map f ≫ g) i =
      (resFunctor (ψ : K ->* H)).map (resolutionMap φ f i) ≫ resolutionMap ψ g i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [resolutionMap_succ]; rw [resolutionMap_succ]; rw [resolutionMap_succ]; rw [ih]
    ext F x
    rfl

/--
lemma `resolutionMap_comp_d` / 引理 `resolutionMap_comp_d`

English:
lemma resolutionMap_comp_d
  given: (φ : H ->ₜ* G) (f : res φ X ⟶ Y) (i : Nat)
  proof: by
  induction i with
  | zero => rfl
  | succ i ih =>
    ext : 1
    replace ih := congr($(ih).hom)
    simp only [TopRep.hom_comp, resolutionMap_succ, TopRep.hom_ofHom, hom_d_succ,
      ContIntertwiningMap.restrict_sub, ContIntertwiningMap.sub_comp,
      ContIntertwiningMap.comp_sub, coind₁Map_comp_coind₁ResMap,
      coind₁ResMap_comp_coind₁Map_restrict] at ih ⊢
    rw [ih]; rw [← coind₁ResMap_comp_coind₁ι_restrict]

中文:
引理 resolutionMap_comp_d
  条件: (φ : H ->ₜ* G) (f : res φ X ⟶ Y) (i : 自然数)
  证明: by
  induction i with
  | zero => rfl
  | succ i ih =>
    ext : 1
    replace ih := congr($(ih).hom)
    simp only [TopRep.hom_comp, resolutionMap_succ, TopRep.hom_ofHom, hom_d_succ,
      ContIntertwiningMap.restrict_sub, ContIntertwiningMap.sub_comp,
      ContIntertwiningMap.comp_sub, coind₁Map_comp_coind₁ResMap,
      coind₁ResMap_comp_coind₁Map_restrict] at ih ⊢
    rw [ih]; rw [← coind₁ResMap_comp_coind₁ι_restrict]

Depends on / 依赖: ContIntertwiningMap, ContIntertwiningMap.comp_sub, ContIntertwiningMap.restrict_sub, ContIntertwiningMap.sub_comp, TopRep, TopRep.hom_comp, TopRep.hom_ofHom, comp_sub, hom_comp, hom_d_succ, hom_ofHom, replace, resolutionMap_succ, restrict_sub, sub_comp
-/
lemma resolutionMap_comp_d (φ : H ->ₜ* G) (f : res φ X ⟶ Y) (i : Nat) :
    resolutionMap φ f i ≫ d Y i =
      (resFunctor (φ : H ->* G)).map (d X i) ≫ resolutionMap φ f (i + 1) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    ext : 1
    replace ih := congr($(ih).hom)
    simp only [TopRep.hom_comp, resolutionMap_succ, TopRep.hom_ofHom, hom_d_succ,
      ContIntertwiningMap.restrict_sub, ContIntertwiningMap.sub_comp,
      ContIntertwiningMap.comp_sub, coind₁Map_comp_coind₁ResMap,
      coind₁ResMap_comp_coind₁Map_restrict] at ih ⊢
    rw [ih]; rw [← coind₁ResMap_comp_coind₁ι_restrict]

/-- The cochain map `homogeneousCochains X ⟶ homogeneousCochains Y` induced by a continuous
group homomorphism `φ : H →ₜ* G` and a morphism of topological `H`-representations
`f : res φ X ⟶ Y`, sending an invariant function `σ : C(G, C(G, ⋯))` to `f ∘ σ ∘ φ`. -/
@[simps! -isSimp f f_hom]
/--
Definition of `cochainsMap` / `cochainsMap` 的定义

English:
definition cochainsMap
  signature: (φ : H ->ₜ* G) (f : res φ X ⟶ Y)
  body: invariantsResMap φ (resolutionMap φ f (i + 1))
  comm' i j (hij : _ = _) := by
    subst hij
    rw [homogeneousCochains.d_eq]; rw [homogeneousCochains.d_eq]; rw [← invariantsResMap_comp]; rw [resolutionMap_comp_d]; rw [invariantsResMap_map_comp]

中文:
定义 cochainsMap
  签名: (φ : H ->ₜ* G) (f : res φ X ⟶ Y)
  定义体: invariantsResMap φ (resolutionMap φ f (i + 1))
  comm' i j (hij : _ = _) := by
    subst hij
    rw [homogeneousCochains.d_eq]; rw [homogeneousCochains.d_eq]; rw [← invariantsResMap_comp]; rw [resolutionMap_comp_d]; rw [invariantsResMap_map_comp]

Depends on / 依赖: invariantsResMap, resolutionMap
-/
def cochainsMap (φ : H ->ₜ* G) (f : res φ X ⟶ Y) :
    homogeneousCochains X ⟶ homogeneousCochains Y where
  f i := invariantsResMap φ (resolutionMap φ f (i + 1))
  comm' i j (hij : _ = _) := by
    subst hij
    rw [homogeneousCochains.d_eq]; rw [homogeneousCochains.d_eq]; rw [← invariantsResMap_comp]; rw [resolutionMap_comp_d]; rw [invariantsResMap_map_comp]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `cochainsMap_id` / 引理 `cochainsMap_id`

English:
lemma cochainsMap_id
  given: (X : TopRep k G)
  proof: by
  ext i : 1
  rw [cochainsMap_f]; rw [resolutionMap_id]
  ext v
  rfl

@[reassoc]

中文:
引理 cochainsMap_id
  条件: (X : TopRep k G)
  证明: by
  ext i : 1
  rw [cochainsMap_f]; rw [resolutionMap_id]
  ext v
  rfl

@[reassoc]

Depends on / 依赖: cochainsMap_f, resolutionMap_id
-/
lemma cochainsMap_id (X : TopRep k G) :
    cochainsMap (ContinuousMonoidHom.id G) (𝟙 X) = 𝟙 (homogeneousCochains X) := by
  ext i : 1
  rw [cochainsMap_f]; rw [resolutionMap_id]
  ext v
  rfl

@[reassoc]
/--
lemma `cochainsMap_comp` / 引理 `cochainsMap_comp`

English:
lemma cochainsMap_comp
  given: (φ : H ->ₜ* G) (ψ : K ->ₜ* H) (f : res φ X ⟶ Y) (g : res ψ Y ⟶ Z)
  proof: by
  ext i v x
  exact congr($(resolutionMap_comp φ ψ f g (i + 1)).hom v.1 x)

中文:
引理 cochainsMap_comp
  条件: (φ : H ->ₜ* G) (ψ : K ->ₜ* H) (f : res φ X ⟶ Y) (g : res ψ Y ⟶ Z)
  证明: by
  ext i v x
  exact congr($(resolutionMap_comp φ ψ f g (i + 1)).hom v.1 x)

Depends on / 依赖: resFunctor
-/
lemma cochainsMap_comp (φ : H ->ₜ* G) (ψ : K ->ₜ* H) (f : res φ X ⟶ Y) (g : res ψ Y ⟶ Z) :
    cochainsMap (φ.comp ψ) (X := X) ((resFunctor (ψ : K ->* H)).map f ≫ g) =
      cochainsMap φ f ≫ cochainsMap ψ g := by
  ext i v x
  exact congr($(resolutionMap_comp φ ψ f g (i + 1)).hom v.1 x)

/--
Definition of `cocyclesMap` / `cocyclesMap` 的定义

English:
abbreviation cocyclesMap
  signature: (φ : H ->ₜ* G) (f : res φ X ⟶ Y) (n : Nat)
  body: HomologicalComplex.cyclesMap (cochainsMap φ f) n

@[simp]

中文:
缩写 cocyclesMap
  签名: (φ : H ->ₜ* G) (f : res φ X ⟶ Y) (n : 自然数)
  定义体: HomologicalComplex.cyclesMap (cochainsMap φ f) n

@[simp]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.cyclesMap, cochainsMap, cyclesMap
-/
noncomputable abbrev cocyclesMap (φ : H ->ₜ* G) (f : res φ X ⟶ Y) (n : Nat) :
    cocycles X n ⟶ cocycles Y n :=
  HomologicalComplex.cyclesMap (cochainsMap φ f) n

@[simp]
/--
lemma `cocyclesMap_id` / 引理 `cocyclesMap_id`

English:
lemma cocyclesMap_id
  given: (X : TopRep k G) (n : Nat)
  proof: by
  simp [cocyclesMap]

@[reassoc]

中文:
引理 cocyclesMap_id
  条件: (X : TopRep k G) (n : 自然数)
  证明: by
  simp [cocyclesMap]

@[reassoc]

Depends on / 依赖: cocyclesMap
-/
lemma cocyclesMap_id (X : TopRep k G) (n : Nat) :
    cocyclesMap (ContinuousMonoidHom.id G) (𝟙 X) n = 𝟙 _ := by
  simp [cocyclesMap]

@[reassoc]
/--
lemma `cocyclesMap_comp` / 引理 `cocyclesMap_comp`

English:
lemma cocyclesMap_comp
  statement: (φ : H ->ₜ* G) (ψ : K ->ₜ* H) (f : res φ X ⟶ Y) (g : res ψ Y ⟶ Z)
  proof: by
  simp [cocyclesMap, ← HomologicalComplex.cyclesMap_comp, ← cochainsMap_comp]

中文:
引理 cocyclesMap_comp
  结论: (φ : H ->ₜ* G) (ψ : K ->ₜ* H) (f : res φ X ⟶ Y) (g : res ψ Y ⟶ Z)
  证明: by
  simp [cocyclesMap, ← HomologicalComplex.cyclesMap_comp, ← cochainsMap_comp]

Depends on / 依赖: resFunctor
-/
lemma cocyclesMap_comp (φ : H ->ₜ* G) (ψ : K ->ₜ* H) (f : res φ X ⟶ Y) (g : res ψ Y ⟶ Z)
    (n : Nat) :
    cocyclesMap (φ.comp ψ) (X := X) ((resFunctor (ψ : K ->* H)).map f ≫ g) n =
      cocyclesMap φ f n ≫ cocyclesMap ψ g n := by
  simp [cocyclesMap, ← HomologicalComplex.cyclesMap_comp, ← cochainsMap_comp]

/--
Definition of `map` / `map` 的定义

English:
abbreviation map
  signature: (φ : H ->ₜ* G) (f : res φ X ⟶ Y) (n : Nat)
  body: HomologicalComplex.homologyMap (cochainsMap φ f) n

@[reassoc]

中文:
缩写 map
  签名: (φ : H ->ₜ* G) (f : res φ X ⟶ Y) (n : 自然数)
  定义体: HomologicalComplex.homologyMap (cochainsMap φ f) n

@[reassoc]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.homologyMap, cochainsMap, homologyMap
-/
noncomputable abbrev map (φ : H ->ₜ* G) (f : res φ X ⟶ Y) (n : Nat) :
    continuousCohomology n X ⟶ continuousCohomology n Y :=
  HomologicalComplex.homologyMap (cochainsMap φ f) n

@[reassoc]
/--
theorem `π_map` / 定理 `π_map`

English:
theorem π_map
  given: (φ : H ->ₜ* G) (f : res φ X ⟶ Y) (n : Nat)
  proof: by
  simp [map, cocyclesMap]

@[simp]

中文:
定理 π_map
  条件: (φ : H ->ₜ* G) (f : res φ X ⟶ Y) (n : 自然数)
  证明: by
  simp [map, cocyclesMap]

@[simp]

Depends on / 依赖: cocyclesMap
-/
theorem π_map (φ : H ->ₜ* G) (f : res φ X ⟶ Y) (n : Nat) :
    π X n ≫ map φ f n = cocyclesMap φ f n ≫ π Y n := by
  simp [map, cocyclesMap]

@[simp]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  given: (X : TopRep k G) (n : Nat)
  proof: by
  simp [map]

@[reassoc]

中文:
引理 map_id
  条件: (X : TopRep k G) (n : 自然数)
  证明: by
  simp [map]

@[reassoc]
-/
lemma map_id (X : TopRep k G) (n : Nat) :
    map (ContinuousMonoidHom.id G) (𝟙 X) n = 𝟙 _ := by
  simp [map]

@[reassoc]
/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  given: (φ : H ->ₜ* G) (ψ : K ->ₜ* H) (f : res φ X ⟶ Y) (g : res ψ Y ⟶ Z) (n : Nat)
  proof: by
  simp [map, ← HomologicalComplex.homologyMap_comp, ← cochainsMap_comp]

中文:
引理 map_comp
  条件: (φ : H ->ₜ* G) (ψ : K ->ₜ* H) (f : res φ X ⟶ Y) (g : res ψ Y ⟶ Z) (n : 自然数)
  证明: by
  simp [map, ← HomologicalComplex.homologyMap_comp, ← cochainsMap_comp]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.homologyMap_comp, cochainsMap_comp, homologyMap_comp, resFunctor
-/
lemma map_comp (φ : H ->ₜ* G) (ψ : K ->ₜ* H) (f : res φ X ⟶ Y) (g : res ψ Y ⟶ Z) (n : Nat) :
    map (φ.comp ψ) (X := X) ((resFunctor (ψ : K ->* H)).map f ≫ g) n = map φ f n ≫ map ψ g n := by
  simp [map, ← HomologicalComplex.homologyMap_comp, ← cochainsMap_comp]

end ContinuousCohomology
