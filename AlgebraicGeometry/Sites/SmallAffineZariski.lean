/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology

/-!

# The small affine Zariski site

`X.AffineZariskiSite` is the small affine Zariski site of `X`, whose elements are affine open
sets of `X`, and whose arrows are basic open sets `D(f) ⟶ U` for any `f : Γ(X, U)`.

Every presieve on `U` is then given by a `Set Γ(X, U)` (`presieveOfSections_surjective`), and
we endow `X.AffineZariskiSite` with `grothendieckTopology X`, such that `s : Set Γ(X, U)` is
a cover if and only if `Ideal.span s = ⊤` (`generate_presieveOfSections_mem_grothendieckTopology`).

This is a dense subsite of `X.Opens` (with respect to `Opens.grothendieckTopology X`) via the
inclusion functor `toOpensFunctor X`,
which gives an equivalence of categories of sheaves (`sheafEquiv`).

Note that this differs from the definition on stacks project where the arrows in the small affine
Zariski site are arbitrary inclusions.

-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/--
Definition of `Scheme.AffineZariskiSite` / `Scheme.AffineZariskiSite` 的定义

English:
definition Scheme.AffineZariskiSite
  signature: (X : Scheme.{u})
  body: { U : X.Opens // IsAffineOpen U }

中文:
定义 概形.AffineZariskiSite
  签名: (X : 概形.{u})
  定义体: { U : X.Opens // IsAffineOpen U }

Depends on / 依赖: IsAffineOpen, X.Opens
-/
def Scheme.AffineZariskiSite (X : Scheme.{u}) : Type u := { U : X.Opens // IsAffineOpen U }

namespace Scheme.AffineZariskiSite

/--
Definition of `toOpens` / `toOpens` 的定义

English:
abbreviation toOpens
  signature: (U : X.AffineZariskiSite)
  body: U.1

中文:
缩写 toOpens
  签名: (U : X.AffineZariskiSite)
  定义体: U.1
-/
abbrev toOpens (U : X.AffineZariskiSite) : X.Opens := U.1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preorder X.AffineZariskiSite
  body: exists f : Γ(X, V.toOpens), X.basicOpen f = U.toOpens
  le_refl U := ⟨1, Scheme.basicOpen_of_isUnit _ isUnit_one⟩
  le_trans := by
    rintro ⟨U, hU⟩ ⟨V, hV⟩ ⟨W, hW⟩ ⟨f, rfl⟩ ⟨g, rfl⟩
    exact hW.basicOpen_basicOpen_is_basicOpen g f

中文:
实例 :
  签名: 预序 X.AffineZariskiSite
  定义体: exists f : Γ(X, V.toOpens), X.basicOpen f = U.toOpens
  le_refl U := ⟨1, Scheme.basicOpen_of_isUnit _ isUnit_one⟩
  le_trans := by
    rintro ⟨U, hU⟩ ⟨V, hV⟩ ⟨W, hW⟩ ⟨f, rfl⟩ ⟨g, rfl⟩
    exact hW.basicOpen_basicOpen_is_basicOpen g f

Depends on / 依赖: U.toOpens, V.toOpens, X.basicOpen, basicOpen, toOpens
-/
instance : Preorder X.AffineZariskiSite where
  le U V := exists f : Γ(X, V.toOpens), X.basicOpen f = U.toOpens
  le_refl U := ⟨1, Scheme.basicOpen_of_isUnit _ isUnit_one⟩
  le_trans := by
    rintro ⟨U, hU⟩ ⟨V, hV⟩ ⟨W, hW⟩ ⟨f, rfl⟩ ⟨g, rfl⟩
    exact hW.basicOpen_basicOpen_is_basicOpen g f

/--
lemma `toOpens_mono` / 引理 `toOpens_mono`

English:
lemma toOpens_mono
  proof: by
  rintro ⟨U, hU⟩ ⟨V, hV⟩ ⟨f, rfl⟩
  exact X.basicOpen_le _

中文:
引理 toOpens_mono
  证明: by
  rintro ⟨U, hU⟩ ⟨V, hV⟩ ⟨f, rfl⟩
  exact X.basicOpen_le _

Depends on / 依赖: X.basicOpen_le, basicOpen_le
-/
lemma toOpens_mono :
    Monotone (toOpens (X := X)) := by
  rintro ⟨U, hU⟩ ⟨V, hV⟩ ⟨f, rfl⟩
  exact X.basicOpen_le _

/--
lemma `toOpens_injective` / 引理 `toOpens_injective`

English:
lemma toOpens_injective
  statement: Function.Injective (toOpens (X := X))
  proof: Subtype.val_injective

中文:
引理 toOpens_injective
  结论: 函数.单射 (toOpens (X := X))
  证明: Subtype.val_injective

Depends on / 依赖: Subtype, Subtype.val_injective, val_injective
-/
lemma toOpens_injective : Function.Injective (toOpens (X := X)) := Subtype.val_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder X.AffineZariskiSite
  body: Subtype.ext ((toOpens_mono hUV).antisymm (toOpens_mono hVU))

中文:
实例 :
  签名: 偏序 X.AffineZariskiSite
  定义体: Subtype.ext ((toOpens_mono hUV).antisymm (toOpens_mono hVU))

Depends on / 依赖: Subtype, Subtype.ext, antisymm, toOpens_mono
-/
instance : PartialOrder X.AffineZariskiSite where
  le_antisymm _ _ hUV hVU := Subtype.ext ((toOpens_mono hUV).antisymm (toOpens_mono hVU))

/--
Definition of `basicOpen` / `basicOpen` 的定义

English:
definition basicOpen
  signature: (U : X.AffineZariskiSite) (f : Γ(X, U.toOpens))
  body: ⟨X.basicOpen f, U.2.basicOpen f⟩

中文:
定义 basicOpen
  签名: (U : X.AffineZariskiSite) (f : Γ(X, U.toOpens))
  定义体: ⟨X.basicOpen f, U.2.basicOpen f⟩
-/
@[simps] def basicOpen (U : X.AffineZariskiSite) (f : Γ(X, U.toOpens)) : X.AffineZariskiSite :=
  ⟨X.basicOpen f, U.2.basicOpen f⟩

/--
lemma `basicOpen_le` / 引理 `basicOpen_le`

English:
lemma basicOpen_le
  given: (U : X.AffineZariskiSite) (f : Γ(X, U.toOpens))
  statement: U.basicOpen f <= U
  proof: ⟨f, rfl⟩

中文:
引理 basicOpen_le
  条件: (U : X.AffineZariskiSite) (f : Γ(X, U.toOpens))
  结论: U.basicOpen f <= U
  证明: ⟨f, rfl⟩
-/
lemma basicOpen_le (U : X.AffineZariskiSite) (f : Γ(X, U.toOpens)) : U.basicOpen f <= U :=
  ⟨f, rfl⟩

variable (X) in
/-- The inclusion functor from `X.AffineZariskiSite` to `X.Opens`. -/
@[simps! obj]
/--
Definition of `toOpensFunctor` / `toOpensFunctor` 的定义

English:
definition toOpensFunctor
  signature: : X.AffineZariskiSite ⥤ X.Opens
  body: toOpens_mono.functor

中文:
定义 toOpensFunctor
  签名: : X.AffineZariskiSite ⥤ X.Opens
  定义体: toOpens_mono.functor

Depends on / 依赖: functor, toOpens_mono, toOpens_mono.functor
-/
def toOpensFunctor : X.AffineZariskiSite ⥤ X.Opens := toOpens_mono.functor

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (toOpensFunctor X).Faithful

中文:
实例 :
  签名: (toOpensFunctor X).忠实
-/
instance : (toOpensFunctor X).Faithful where

variable (X) in
/-- The forgetful functor from `X.AffineZariskiSite` to `Scheme` is isomorphic to `Spec Γ(X, -)`. -/
@[simps! hom_app inv_app]
/--
Definition of `restrictIsoSpec` / `restrictIsoSpec` 的定义

English:
definition restrictIsoSpec
  signature: : toOpensFunctor X ⋙ X.restrictFunctor ⋙ Over.forget _ ≅
  body: NatIso.ofComponents (fun U => U.2.isoSpec)
    fun _ => (Scheme.Opens.toSpecΓ_SpecMap_presheaf_map ..).symm

中文:
定义 restrictIsoSpec
  签名: : toOpensFunctor X ⋙ X.restrictFunctor ⋙ Over.forget _ ≅
  定义体: NatIso.ofComponents (fun U => U.2.isoSpec)
    fun _ => (Scheme.Opens.toSpecΓ_SpecMap_presheaf_map ..).symm

Depends on / 依赖: NatIso, NatIso.ofComponents, Scheme, Scheme.Opens.toSpec, isoSpec, ofComponents
-/
def restrictIsoSpec : toOpensFunctor X ⋙ X.restrictFunctor ⋙ Over.forget _ ≅
    toOpensFunctor X ⋙ X.presheaf.rightOp ⋙ Scheme.Spec :=
  NatIso.ofComponents (fun U => U.2.isoSpec)
    fun _ => (Scheme.Opens.toSpecΓ_SpecMap_presheaf_map ..).symm

section GrothendieckTopology

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (toOpensFunctor X).IsLocallyFull (Opens.grothendieckTopology X)
  body: by
    intro U V h x hx
    obtain ⟨f, hfU, hxf⟩ := V.2.exists_basicOpen_le ⟨x, hx⟩ (h.le hx)
    exact ⟨X.basicOpen f, homOfLE hfU, ⟨V.basicOpen f,
      ⟨_, (X.basicOpen_res f h.op).trans (inf_eq_right.mpr hfU)⟩, 𝟙 _,
      ⟨⟨f, rfl⟩, rfl⟩, rfl⟩, hxf⟩

中文:
实例 :
  签名: (toOpensFunctor X).是LocallyFull (Opens.grothendieckTopology X)
  定义体: by
    intro U V h x hx
    obtain ⟨f, hfU, hxf⟩ := V.2.exists_basicOpen_le ⟨x, hx⟩ (h.le hx)
    exact ⟨X.basicOpen f, homOfLE hfU, ⟨V.basicOpen f,
      ⟨_, (X.basicOpen_res f h.op).trans (inf_eq_right.mpr hfU)⟩, 𝟙 _,
      ⟨⟨f, rfl⟩, rfl⟩, rfl⟩, hxf⟩

Depends on / 依赖: V.basicOpen, X.basicOpen, X.basicOpen_res, basicOpen, basicOpen_res, exists_basicOpen_le, h.le, h.op, homOfLE, inf_eq_right, inf_eq_right.mpr
-/
instance : (toOpensFunctor X).IsLocallyFull (Opens.grothendieckTopology X) where
  functorPushforward_imageSieve_mem := by
    intro U V h x hx
    obtain ⟨f, hfU, hxf⟩ := V.2.exists_basicOpen_le ⟨x, hx⟩ (h.le hx)
    exact ⟨X.basicOpen f, homOfLE hfU, ⟨V.basicOpen f,
      ⟨_, (X.basicOpen_res f h.op).trans (inf_eq_right.mpr hfU)⟩, 𝟙 _,
      ⟨⟨f, rfl⟩, rfl⟩, rfl⟩, hxf⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (toOpensFunctor X).IsCoverDense (Opens.grothendieckTopology X)
  body: by
    intro U x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
    exact ⟨V, homOfLE hVU, ⟨⟨V, hV⟩, 𝟙 _, homOfLE hVU, rfl⟩, hxV⟩

中文:
实例 :
  签名: (toOpensFunctor X).是余verDense (Opens.grothendieckTopology X)
  定义体: by
    intro U x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
    exact ⟨V, homOfLE hVU, ⟨⟨V, hV⟩, 𝟙 _, homOfLE hVU, rfl⟩, hxV⟩

Depends on / 依赖: X.isBasis_affineOpens.exists_subset_of_mem_open, exists_subset_of_mem_open, homOfLE, isBasis_affineOpens
-/
instance : (toOpensFunctor X).IsCoverDense (Opens.grothendieckTopology X) where
  is_cover := by
    intro U x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
    exact ⟨V, homOfLE hVU, ⟨⟨V, hV⟩, 𝟙 _, homOfLE hVU, rfl⟩, hxV⟩

variable (X) in
/--
Definition of `grothendieckTopology` / `grothendieckTopology` 的定义

English:
definition grothendieckTopology
  signature: : GrothendieckTopology X.AffineZariskiSite
  body: (toOpensFunctor X).inducedTopology (Opens.grothendieckTopology X)

中文:
定义 grothendieckTopology
  签名: : Grothendieck拓扑 X.AffineZariskiSite
  定义体: (toOpensFunctor X).inducedTopology (Opens.grothendieckTopology X)

Depends on / 依赖: Opens.grothendieckTopology, grothendieckTopology, inducedTopology, toOpensFunctor
-/
def grothendieckTopology : GrothendieckTopology X.AffineZariskiSite :=
  (toOpensFunctor X).inducedTopology (Opens.grothendieckTopology X)

/--
lemma `mem_grothendieckTopology` / 引理 `mem_grothendieckTopology`

English:
lemma mem_grothendieckTopology
  given: {U : X.AffineZariskiSite} {S : Sieve U}
  proof: by
  rw [grothendieckTopology]; rw [Functor.mem_inducedTopology_iff_of_isCoverDense]
  apply forall₂_congr fun x hxU => ⟨?_, ?_⟩
  · rintro ⟨V, f, ⟨W, g, h, hg, rfl⟩, hxV⟩
    exact ⟨W, g, hg, h.le hxV⟩
  · rintro ⟨W, g, hg, hxW⟩
    exact ⟨W.toOpens, homOfLE (toOpens_mono g.le), ⟨W, g, 𝟙 _, hg, rfl

中文:
引理 mem_grothendieckTopology
  条件: {U : X.AffineZariskiSite} {S : 筛 U}
  证明: by
  rw [grothendieckTopology]; rw [Functor.mem_inducedTopology_iff_of_isCoverDense]
  apply forall₂_congr fun x hxU => ⟨?_, ?_⟩
  · rintro ⟨V, f, ⟨W, g, h, hg, rfl⟩, hxV⟩
    exact ⟨W, g, hg, h.le hxV⟩
  · rintro ⟨W, g, hg, hxW⟩
    exact ⟨W.toOpens, homOfLE (toOpens_mono g.le), ⟨W, g, 𝟙 _, hg, rfl

Depends on / 依赖: Functor, Functor.mem_inducedTopology_iff_of_isCoverDense, W.toOpens, g.le, grothendieckTopology, h.le, homOfLE, mem_inducedTopology_iff_of_isCoverDense, toOpens, toOpens_mono
-/
lemma mem_grothendieckTopology {U : X.AffineZariskiSite} {S : Sieve U} :
    S in grothendieckTopology X U ↔
      forall x in U.toOpens, exists (V : _) (f : V ⟶ U), S.arrows f ∧ x in V.toOpens := by
  rw [grothendieckTopology]; rw [Functor.mem_inducedTopology_iff_of_isCoverDense]
  apply forall₂_congr fun x hxU => ⟨?_, ?_⟩
  · rintro ⟨V, f, ⟨W, g, h, hg, rfl⟩, hxV⟩
    exact ⟨W, g, hg, h.le hxV⟩
  · rintro ⟨W, g, hg, hxW⟩
    exact ⟨W.toOpens, homOfLE (toOpens_mono g.le), ⟨W, g, 𝟙 _, hg, rfl⟩, hxW⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (toOpensFunctor X).IsDenseSubsite
  body: by simp [grothendieckTopology]

中文:
实例 :
  签名: (toOpensFunctor X).是DenseSubsite
  定义体: by simp [grothendieckTopology]

Depends on / 依赖: grothendieckTopology
-/
instance : (toOpensFunctor X).IsDenseSubsite
    (grothendieckTopology X) (Opens.grothendieckTopology X) where
  functorPushforward_mem_iff := by simp [grothendieckTopology]

/--
Definition of `presieveOfSections` / `presieveOfSections` 的定义

English:
definition presieveOfSections
  signature: (U : X.AffineZariskiSite) (s : Set Γ(X, U.toOpens))
  body: fun V _ => exists f in s, X.basicOpen f = V.toOpens

中文:
定义 presieveOfSections
  签名: (U : X.AffineZariskiSite) (s : 集合 Γ(X, U.toOpens))
  定义体: fun V _ => exists f in s, X.basicOpen f = V.toOpens

Depends on / 依赖: V.toOpens, X.basicOpen, basicOpen, toOpens
-/
def presieveOfSections (U : X.AffineZariskiSite) (s : Set Γ(X, U.toOpens)) : Presieve U :=
  fun V _ => exists f in s, X.basicOpen f = V.toOpens

/--
Definition of `sectionsOfPresieve` / `sectionsOfPresieve` 的定义

English:
definition sectionsOfPresieve
  signature: {U : X.AffineZariskiSite} (P : Presieve U)
  body: { f | P (homOfLE (U.basicOpen_le f)) }

中文:
定义 sectionsOfPresieve
  签名: {U : X.AffineZariskiSite} (P : Presieve U)
  定义体: { f | P (homOfLE (U.basicOpen_le f)) }

Depends on / 依赖: U.basicOpen_le, basicOpen_le, homOfLE
-/
def sectionsOfPresieve {U : X.AffineZariskiSite} (P : Presieve U) : Set Γ(X, U.toOpens) :=
  { f | P (homOfLE (U.basicOpen_le f)) }

/--
lemma `presieveOfSections_sectionsOfPresieve` / 引理 `presieveOfSections_sectionsOfPresieve`

English:
lemma presieveOfSections_sectionsOfPresieve
  given: {U : X.AffineZariskiSite} (P : Presieve U)
  proof: by
  refine funext₂ fun ⟨V, hV⟩ ⟨f, hf⟩ => eq_iff_iff.mpr ⟨?_, ?_⟩
  · rintro ⟨_, H, rfl⟩
    exact H
  · intro H
    obtain rfl : _ = V := hf
    exact ⟨_, H, rfl⟩

中文:
引理 presieveOfSections_sectionsOfPresieve
  条件: {U : X.AffineZariskiSite} (P : Presieve U)
  证明: by
  refine funext₂ fun ⟨V, hV⟩ ⟨f, hf⟩ => eq_iff_iff.mpr ⟨?_, ?_⟩
  · rintro ⟨_, H, rfl⟩
    exact H
  · intro H
    obtain rfl : _ = V := hf
    exact ⟨_, H, rfl⟩

Depends on / 依赖: eq_iff_iff, eq_iff_iff.mpr
-/
lemma presieveOfSections_sectionsOfPresieve {U : X.AffineZariskiSite} (P : Presieve U) :
    presieveOfSections U (sectionsOfPresieve P) = P := by
  refine funext₂ fun ⟨V, hV⟩ ⟨f, hf⟩ => eq_iff_iff.mpr ⟨?_, ?_⟩
  · rintro ⟨_, H, rfl⟩
    exact H
  · intro H
    obtain rfl : _ = V := hf
    exact ⟨_, H, rfl⟩

/--
lemma `presieveOfSections_surjective` / 引理 `presieveOfSections_surjective`

English:
lemma presieveOfSections_surjective
  given: {U : X.AffineZariskiSite}
  proof: fun _ => ⟨_, presieveOfSections_sectionsOfPresieve _⟩

中文:
引理 presieveOfSections_surjective
  条件: {U : X.AffineZariskiSite}
  证明: fun _ => ⟨_, presieveOfSections_sectionsOfPresieve _⟩

Depends on / 依赖: presieveOfSections_sectionsOfPresieve
-/
lemma presieveOfSections_surjective {U : X.AffineZariskiSite} :
    Function.Surjective (presieveOfSections U) :=
  fun _ => ⟨_, presieveOfSections_sectionsOfPresieve _⟩

/--
lemma `presieveOfSections_eq_ofArrows` / 引理 `presieveOfSections_eq_ofArrows`

English:
lemma presieveOfSections_eq_ofArrows
  given: (U : X.AffineZariskiSite) (s : Set Γ(X, U.toOpens))
  proof: by
  refine funext₂ fun ⟨V, hV⟩ ⟨f, hf⟩ => eq_iff_iff.mpr ⟨?_, ?_⟩
  · rintro ⟨f, hfs, rfl⟩
    exact .mk (ι := s) ⟨f, hfs⟩
  · rintro ⟨⟨f, hfs⟩⟩
    exact ⟨f, hfs, rfl⟩

中文:
引理 presieveOfSections_eq_ofArrows
  条件: (U : X.AffineZariskiSite) (s : 集合 Γ(X, U.toOpens))
  证明: by
  refine funext₂ fun ⟨V, hV⟩ ⟨f, hf⟩ => eq_iff_iff.mpr ⟨?_, ?_⟩
  · rintro ⟨f, hfs, rfl⟩
    exact .mk (ι := s) ⟨f, hfs⟩
  · rintro ⟨⟨f, hfs⟩⟩
    exact ⟨f, hfs, rfl⟩

Depends on / 依赖: eq_iff_iff, eq_iff_iff.mpr
-/
lemma presieveOfSections_eq_ofArrows (U : X.AffineZariskiSite) (s : Set Γ(X, U.toOpens)) :
    presieveOfSections U s = .ofArrows _ (fun i : s => homOfLE (U.basicOpen_le i.1)) := by
  refine funext₂ fun ⟨V, hV⟩ ⟨f, hf⟩ => eq_iff_iff.mpr ⟨?_, ?_⟩
  · rintro ⟨f, hfs, rfl⟩
    exact .mk (ι := s) ⟨f, hfs⟩
  · rintro ⟨⟨f, hfs⟩⟩
    exact ⟨f, hfs, rfl⟩

/--
lemma `generate_presieveOfSections` / 引理 `generate_presieveOfSections`

English:
lemma generate_presieveOfSections
  proof: by
  obtain ⟨V, hV⟩ := V
  constructor
  · rintro ⟨⟨W, hW⟩, ⟨f₁, hf₁⟩, -, ⟨f₂, hf₂s, rfl⟩, rfl⟩
    subst hf₁
    obtain ⟨f₃, hf₃⟩ := U.2.basicOpen_basicOpen_is_basicOpen f₂ f₁
    refine ⟨f₂, hf₂s, f₃, ?_⟩
    rw [X.basicOpen_mul]; rw [hf₃]; rw [inf_eq_right]
    exact X.basicOpen_le _
  · rintro ⟨

中文:
引理 generate_presieveOfSections
  证明: by
  obtain ⟨V, hV⟩ := V
  constructor
  · rintro ⟨⟨W, hW⟩, ⟨f₁, hf₁⟩, -, ⟨f₂, hf₂s, rfl⟩, rfl⟩
    subst hf₁
    obtain ⟨f₃, hf₃⟩ := U.2.basicOpen_basicOpen_is_basicOpen f₂ f₁
    refine ⟨f₂, hf₂s, f₃, ?_⟩
    rw [X.basicOpen_mul]; rw [hf₃]; rw [inf_eq_right]
    exact X.basicOpen_le _
  · rintro ⟨

Depends on / 依赖: U.basicOpen, X.basicOpen_le, X.basicOpen_mul, X.basicOpen_res, basicOpen, basicOpen_basicOpen_is_basicOpen, basicOpen_le, basicOpen_mul, basicOpen_res, inf_eq_right
-/
lemma generate_presieveOfSections
    {U V : X.AffineZariskiSite} {s : Set Γ(X, U.toOpens)} {f : V ⟶ U} :
    Sieve.generate (presieveOfSections U s) f ↔ exists f in s, exists g, X.basicOpen (f * g) = V.toOpens := by
  obtain ⟨V, hV⟩ := V
  constructor
  · rintro ⟨⟨W, hW⟩, ⟨f₁, hf₁⟩, -, ⟨f₂, hf₂s, rfl⟩, rfl⟩
    subst hf₁
    obtain ⟨f₃, hf₃⟩ := U.2.basicOpen_basicOpen_is_basicOpen f₂ f₁
    refine ⟨f₂, hf₂s, f₃, ?_⟩
    rw [X.basicOpen_mul]; rw [hf₃]; rw [inf_eq_right]
    exact X.basicOpen_le _
  · rintro ⟨f₁, hf₁s, f₂, rfl⟩
    refine ⟨U.basicOpen f₁, ⟨f₂ |_ _, ?_⟩, ⟨f₁, rfl⟩, ⟨f₁, hf₁s, rfl⟩, rfl⟩
    exact (X.basicOpen_res _ _).trans (X.basicOpen_mul _ _).symm

/--
lemma `generate_presieveOfSections_mem_grothendieckTopology` / 引理 `generate_presieveOfSections_mem_grothendieckTopology`

English:
lemma generate_presieveOfSections_mem_grothendieckTopology
  proof: by
  rw [← U.2.self_le_iSup_basicOpen_iff]; rw [mem_grothendieckTopology]; rw [SetLike.le_def]
  refine forall₂_congr fun x hx => ?_
  simp only [exists_and_left, TopologicalSpace.Opens.iSup_mk,
    TopologicalSpace.Opens.carrier_eq_coe, Set.iUnion_coe_set, TopologicalSpace.Opens.mem_mk,
    Set.mem

中文:
引理 generate_presieveOfSections_mem_grothendieckTopology
  证明: by
  rw [← U.2.self_le_iSup_basicOpen_iff]; rw [mem_grothendieckTopology]; rw [SetLike.le_def]
  refine forall₂_congr fun x hx => ?_
  simp only [exists_and_left, TopologicalSpace.Opens.iSup_mk,
    TopologicalSpace.Opens.carrier_eq_coe, Set.iUnion_coe_set, TopologicalSpace.Opens.mem_mk,
    Set.mem

Depends on / 依赖: Set.iUnion_coe_set, Set.mem_iUnion, SetLike, SetLike.le_def, SetLike.mem_coe, TopologicalSpace, TopologicalSpace.Opens.carrier_eq_coe, TopologicalSpace.Opens.iSup_mk, TopologicalSpace.Opens.mem_mk, U.basicOpe, basicOpe, basicOpen_mul, carrier_eq_coe, exists_and_left, exists_prop, generate_presieveOfSections, iSup_mk, iUnion_coe_set, le_def, mem_coe
-/
lemma generate_presieveOfSections_mem_grothendieckTopology
    {U : X.AffineZariskiSite} {s : Set Γ(X, U.toOpens)} :
    Sieve.generate (presieveOfSections U s) in grothendieckTopology X U ↔ Ideal.span s = ⊤ := by
  rw [← U.2.self_le_iSup_basicOpen_iff]; rw [mem_grothendieckTopology]; rw [SetLike.le_def]
  refine forall₂_congr fun x hx => ?_
  simp only [exists_and_left, TopologicalSpace.Opens.iSup_mk,
    TopologicalSpace.Opens.carrier_eq_coe, Set.iUnion_coe_set, TopologicalSpace.Opens.mem_mk,
    Set.mem_iUnion, SetLike.mem_coe, exists_prop, generate_presieveOfSections]
  constructor
  · simp only [basicOpen_mul]
    rintro ⟨⟨V, hV⟩, ⟨f, hfs, g, rfl⟩, -, hxV⟩
    exact ⟨f, hfs, hxV.1⟩
  · rintro ⟨f, hfs, hxf⟩
    refine ⟨U.basicOpen _, ⟨f, hfs, 1, rfl⟩, ⟨_, rfl⟩, by simpa using hxf⟩

/--
lemma `mem_grothendieckTopology_iff_sectionsOfPresieve` / 引理 `mem_grothendieckTopology_iff_sectionsOfPresieve`

English:
lemma mem_grothendieckTopology_iff_sectionsOfPresieve
  proof: by
  rw [← generate_presieveOfSections_mem_grothendieckTopology]; rw [presieveOfSections_sectionsOfPresieve]; rw [Sieve.generate_sieve]

中文:
引理 mem_grothendieckTopology_iff_sectionsOfPresieve
  证明: by
  rw [← generate_presieveOfSections_mem_grothendieckTopology]; rw [presieveOfSections_sectionsOfPresieve]; rw [Sieve.generate_sieve]

Depends on / 依赖: Sieve.generate_sieve, generate_presieveOfSections_mem_grothendieckTopology, generate_sieve, presieveOfSections_sectionsOfPresieve
-/
lemma mem_grothendieckTopology_iff_sectionsOfPresieve
    {U : X.AffineZariskiSite} {S : Sieve U} :
    S in grothendieckTopology X U ↔ Ideal.span (sectionsOfPresieve S.1) = ⊤ := by
  rw [← generate_presieveOfSections_mem_grothendieckTopology]; rw [presieveOfSections_sectionsOfPresieve]; rw [Sieve.generate_sieve]

variable {A} [Category* A]
variable [forall (U : X.Opensᵒᵖ), Limits.HasLimitsOfShape (StructuredArrow U (toOpensFunctor X).op) A]

/--
Definition of `sheafEquiv` / `sheafEquiv` 的定义

English:
abbreviation sheafEquiv
  signature: : Sheaf (grothendieckTopology X) A ≌ TopCat.Sheaf A X
  body: (toOpensFunctor X).sheafInducedTopologyEquivOfIsCoverDense _ _

中文:
缩写 sheafEquiv
  签名: : 层 (grothendieckTopology X) A ≌ 顶元素范畴.层 A X
  定义体: (toOpensFunctor X).sheafInducedTopologyEquivOfIsCoverDense _ _

Depends on / 依赖: sheafInducedTopologyEquivOfIsCoverDense, toOpensFunctor
-/
abbrev sheafEquiv : Sheaf (grothendieckTopology X) A ≌ TopCat.Sheaf A X :=
    (toOpensFunctor X).sheafInducedTopologyEquivOfIsCoverDense _ _

end GrothendieckTopology

variable (X) in
/--
Definition of `directedCover` / `directedCover` 的定义

English:
abbreviation directedCover
  signature: : X.OpenCover where
  body: X.AffineZariskiSite
  X U := U.1
  f U := U.1.ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))
    exact ⟨U, ⟨x, hxU⟩, rfl⟩

中文:
缩写 directedCover
  签名: : X.OpenCover where
  定义体: X.AffineZariskiSite
  X U := U.1
  f U := U.1.ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))
    exact ⟨U, ⟨x, hxU⟩, rfl⟩
-/
@[simps] abbrev directedCover : X.OpenCover where
  I₀ := X.AffineZariskiSite
  X U := U.1
  f U := U.1.ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))
    exact ⟨U, ⟨x, hxU⟩, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Scheme.AffineZariskiSite.directedCover X).LocallyDirected
  body: X.homOfLE (((Scheme.AffineZariskiSite.toOpensFunctor _).map f).le)
  directed {U V} x := by
    let a := (pullback.fst _ _ ≫ U.1.ι) x
    have haU : a in U.1 := (pullback.fst U.1.ι V.1.ι x).2
    have haV : a in V.1 := by unfold a; rw [pullback.condition]; exact (pullback.snd U.1.ι V.1.ι x).2
    ob

中文:
实例 :
  签名: (概形.AffineZariskiSite.directedCover X).LocallyDirected
  定义体: X.homOfLE (((Scheme.AffineZariskiSite.toOpensFunctor _).map f).le)
  directed {U V} x := by
    let a := (pullback.fst _ _ ≫ U.1.ι) x
    have haU : a in U.1 := (pullback.fst U.1.ι V.1.ι x).2
    have haV : a in V.1 := by unfold a; rw [pullback.condition]; exact (pullback.snd U.1.ι V.1.ι x).2
    ob

Depends on / 依赖: AffineZariskiSite, Scheme, Scheme.AffineZariskiSite.toOpensFunctor, X.homOfLE, homOfLE, toOpensFunctor
-/
noncomputable instance : (Scheme.AffineZariskiSite.directedCover X).LocallyDirected where
  trans f := X.homOfLE (((Scheme.AffineZariskiSite.toOpensFunctor _).map f).le)
  directed {U V} x := by
    let a := (pullback.fst _ _ ≫ U.1.ι) x
    have haU : a in U.1 := (pullback.fst U.1.ι V.1.ι x).2
    have haV : a in V.1 := by unfold a; rw [pullback.condition]; exact (pullback.snd U.1.ι V.1.ι x).2
    obtain ⟨f, g, e, hxf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 _ ⟨haU, haV⟩
    refine ⟨U.basicOpen f, homOfLE (U.basicOpen_le f), eqToHom (Subtype.ext (by exact e)) ≫
      homOfLE (V.basicOpen_le g), ⟨a, hxf⟩, ?_⟩
    apply (pullback.fst _ _ ≫ U.1.ι).isOpenEmbedding.injective
    dsimp
    change (pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ U.1.ι) _ = _
    simp only [pullback.lift_fst_assoc, homOfLE_ι, Opens.ι_apply]
    rfl

section PreservesLocalization

/-!
## "Quasi-coherent `𝒪ₓ`-algebras"

A presheaf `F` of rings on `X.AffineZariskiSite` with a structural morphism `α : 𝒪ₓ ⟶ F`
is said to be `Coequifibered` if `F(D(f)) = F(U)[1/f]`
for every open `U` and any section `f : Γ(X, U)`.
(See `coequifibered_iff_forall_isLocalizationAway`)

Under this condition we can construct a family of gluing data (See `relativeGluingData`) and glue
`F` into a scheme over `X` via `(relativeGluingData _).glued`,
Also see the relative gluing API in `Mathlib/AlgebraicGeometry/RelativeGluing.lean`.

This is closely related to the notion of quasi-coherent `𝒪ₓ`-algebras, and we shall link them
together once the theory of quasi-coherent `𝒪ₓ`-algebras are developed.
-/

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable (X) in
/--
Definition of `cocone` / `cocone` 的定义

English:
definition cocone
  signature: :
  body: X
  ι.app U := U.2.fromSpec
  ι.naturality {U V} f := by dsimp; rw [V.2.map_fromSpec U.2]; simp

中文:
定义 cocone
  签名: :
  定义体: X
  ι.app U := U.2.fromSpec
  ι.naturality {U V} f := by dsimp; rw [V.2.map_fromSpec U.2]; simp
-/
@[simps] noncomputable def cocone :
    Limits.Cocone (toOpensFunctor X ⋙ X.presheaf.rightOp ⋙ Scheme.Spec) where
  pt := X
  ι.app U := U.2.fromSpec
  ι.naturality {U V} f := by dsimp; rw [V.2.map_fromSpec U.2]; simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `coequifibered_iff_forall_isLocalizationAway` / 引理 `coequifibered_iff_forall_isLocalizationAway`

English:
lemma coequifibered_iff_forall_isLocalizationAway
  statement: {F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat}
  proof: (F.map (homOfLE (U.basicOpen_le f)).op).hom.toAlgebra
      IsLocalization.Away (α.app (.op U) f) (F.obj (.op (U.basicOpen f))) := by
  trans forall (U : X.AffineZariskiSite) (f : Γ(X, U.1)),
    IsPushout (X.presheaf.map (homOfLE (X.basicOpen_le f)).op)
      (α.app _) (α.app (.op (U.basicOpen f)))

中文:
引理 coequifibered_iff_对任意_isLocalizationAway
  结论: {F : X.AffineZariskiSiteᵒᵖ ⥤ 交换环范畴}
  证明: (F.map (homOfLE (U.basicOpen_le f)).op).hom.toAlgebra
      IsLocalization.Away (α.app (.op U) f) (F.obj (.op (U.basicOpen f))) := by
  trans forall (U : X.AffineZariskiSite) (f : Γ(X, U.1)),
    IsPushout (X.presheaf.map (homOfLE (X.basicOpen_le f)).op)
      (α.app _) (α.app (.op (U.basicOpen f)))

Depends on / 依赖: F.map, U.basicOpen_le, basicOpen_le, hom.toAlgebra, homOfLE, toAlgebra
-/
lemma coequifibered_iff_forall_isLocalizationAway {F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat}
    {α : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F} :
    α.Coequifibered ↔ forall (U : X.AffineZariskiSite) (f : Γ(X, U.1)),
      letI := (F.map (homOfLE (U.basicOpen_le f)).op).hom.toAlgebra
      IsLocalization.Away (α.app (.op U) f) (F.obj (.op (U.basicOpen f))) := by
  trans forall (U : X.AffineZariskiSite) (f : Γ(X, U.1)),
    IsPushout (X.presheaf.map (homOfLE (X.basicOpen_le f)).op)
      (α.app _) (α.app (.op (U.basicOpen f))) (F.map (homOfLE (U.basicOpen_le f)).op)
  · refine ⟨fun H U f => H (homOfLE (U.basicOpen_le f)).op, fun H ⟨V⟩ ⟨U⟩ ⟨f, hf⟩ => ?_⟩
    obtain rfl : V.basicOpen f = U := Subtype.ext hf
    exact H V f
  refine forall₂_congr fun U f => ?_
  set αU : Γ(X, U.toOpens) ⟶ F.obj (.op U) := α.app (.op U)
  set αUf : Γ(X, X.basicOpen f) ⟶ F.obj (.op (U.basicOpen f)) := α.app (.op (U.basicOpen f))
  algebraize [(X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom, αU.hom, αUf.hom,
    (F.map (U.basicOpen_le f).hom.op).hom, (F.map (U.basicOpen_le f).hom.op).hom.comp αU.hom]
  have : IsScalarTower Γ(X, U.toOpens) Γ(X, X.basicOpen f) (F.obj (.op (U.basicOpen f))) :=
    .of_algebraMap_eq' congr($(α.naturality (U.basicOpen_le f).hom.op).hom).symm
  have : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_basicOpen _
  refine (CommRingCat.isPushout_iff_isPushout ..).trans ?_
  rw [Algebra.IsPushout.comm]
  refine (Algebra.isLocalization_iff_isPushout (.powers f) Γ(X, X.basicOpen f)).symm.trans ?_
  simp [RingHom.algebraMap_toAlgebra]

@[deprecated (since := "2026-02-01")] alias PreservesLocalization := NatTrans.Coequifibered

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `relativeGluingData` / `relativeGluingData` 的定义

English:
definition relativeGluingData
  signature: {F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat}
  body: F.rightOp ⋙ Scheme.Spec
  natTrans := Functor.whiskerRight α.rightOp Scheme.Spec ≫ (restrictIsoSpec X).inv
  equifibered := (H.rightOp.whiskerRight _).comp (.of_isIso _)

@[deprecated "By `inferInstance`." (since := "2026-02-01")]

中文:
定义 relativeGluingData
  签名: {F : X.AffineZariskiSiteᵒᵖ ⥤ 交换环范畴}
  定义体: F.rightOp ⋙ Scheme.Spec
  natTrans := Functor.whiskerRight α.rightOp Scheme.Spec ≫ (restrictIsoSpec X).inv
  equifibered := (H.rightOp.whiskerRight _).comp (.of_isIso _)

@[deprecated "By `inferInstance`." (since := "2026-02-01")]

Depends on / 依赖: F.rightOp, Scheme, Scheme.Spec, rightOp
-/
def relativeGluingData {F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat}
    {α : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F}
    (H : α.Coequifibered) :
    (AffineZariskiSite.directedCover X).RelativeGluingData where
  functor := F.rightOp ⋙ Scheme.Spec
  natTrans := Functor.whiskerRight α.rightOp Scheme.Spec ≫ (restrictIsoSpec X).inv
  equifibered := (H.rightOp.whiskerRight _).comp (.of_isIso _)

@[deprecated "By `inferInstance`." (since := "2026-02-01")]
/--
lemma `PreservesLocalization.isLocallyDirected` / 引理 `PreservesLocalization.isLocallyDirected`

English:
lemma PreservesLocalization.isLocallyDirected
  statement: (F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
  proof: (relativeGluingData H).instIsLocallyDirectedI₀CompFunctorForgetOfIsThin

@[deprecated "By `inferInstance`." (since := "2026-02-01")]

中文:
引理 PreservesLocalization.isLocallyDirected
  结论: (F : X.AffineZariskiSiteᵒᵖ ⥤ 交换环范畴)
  证明: (relativeGluingData H).instIsLocallyDirectedI₀CompFunctorForgetOfIsThin

@[deprecated "By `inferInstance`." (since := "2026-02-01")]

Depends on / 依赖: relativeGluingData
-/
lemma PreservesLocalization.isLocallyDirected (F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F)
    (H : α.Coequifibered) :
    ((F.rightOp ⋙ Scheme.Spec) ⋙ Scheme.forget).IsLocallyDirected :=
  (relativeGluingData H).instIsLocallyDirectedI₀CompFunctorForgetOfIsThin

@[deprecated "By `inferInstance`." (since := "2026-02-01")]
/--
lemma `PreservesLocalization.isOpenImmersion` / 引理 `PreservesLocalization.isOpenImmersion`

English:
lemma PreservesLocalization.isOpenImmersion
  statement: (F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
  proof: by
  exact fun U V => (relativeGluingData H).instIsOpenImmersionMapI₀Functor

中文:
引理 PreservesLocalization.isOpenImmersion
  结论: (F : X.AffineZariskiSiteᵒᵖ ⥤ 交换环范畴)
  证明: by
  exact fun U V => (relativeGluingData H).instIsOpenImmersionMapI₀Functor

Depends on / 依赖: relativeGluingData
-/
lemma PreservesLocalization.isOpenImmersion (F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F)
    (H : α.Coequifibered) :
    forall ⦃U V⦄ (f : U ⟶ V), IsOpenImmersion ((F.rightOp ⋙ Scheme.Spec).map f) := by
  exact fun U V => (relativeGluingData H).instIsOpenImmersionMapI₀Functor

/--
lemma `opensRange_relativeGluingData_map` / 引理 `opensRange_relativeGluingData_map`

English:
lemma opensRange_relativeGluingData_map
  statement: (F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
  proof: by
  have := coequifibered_iff_forall_isLocalizationAway.mp H U r
  let := (F.map (homOfLE (U.basicOpen_le r)).op).hom.toAlgebra
  apply TopologicalSpace.Opens.coe_inj.mp ?_
  refine PrimeSpectrum.localization_away_comap_range (F.obj (.op <| U.basicOpen r))
    (α.app (.op U) r)

@[deprecated (since

中文:
引理 opensRange_relativeGluingData_map
  结论: (F : X.AffineZariskiSiteᵒᵖ ⥤ 交换环范畴)
  证明: by
  have := coequifibered_iff_forall_isLocalizationAway.mp H U r
  let := (F.map (homOfLE (U.basicOpen_le r)).op).hom.toAlgebra
  apply TopologicalSpace.Opens.coe_inj.mp ?_
  refine PrimeSpectrum.localization_away_comap_range (F.obj (.op <| U.basicOpen r))
    (α.app (.op U) r)

@[deprecated (since

Depends on / 依赖: F.map, F.obj, PrimeSpectrum, PrimeSpectrum.localization_away_comap_range, TopologicalSpace, TopologicalSpace.Opens.coe_inj.mp, U.basicOpen, U.basicOpen_le, basicOpen, basicOpen_le, coe_inj, coequifibered_iff_forall_isLocalizationAway, coequifibered_iff_forall_isLocalizationAway.mp, hom.toAlgebra, homOfLE, localization_away_comap_range, toAlgebra
-/
lemma opensRange_relativeGluingData_map (F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F)
    (H : α.Coequifibered) {U : X.AffineZariskiSite} (r : Γ(X, U.1)) :
    ((relativeGluingData H).functor.map (homOfLE (U.basicOpen_le r))).opensRange =
      PrimeSpectrum.basicOpen (α.app (.op U) r) := by
  have := coequifibered_iff_forall_isLocalizationAway.mp H U r
  let := (F.map (homOfLE (U.basicOpen_le r)).op).hom.toAlgebra
  apply TopologicalSpace.Opens.coe_inj.mp ?_
  refine PrimeSpectrum.localization_away_comap_range (F.obj (.op <| U.basicOpen r))
    (α.app (.op U) r)

@[deprecated (since := "2026-02-01")]
alias PreservesLocalization.opensRange_map := opensRange_relativeGluingData_map

set_option backward.isDefEq.respectTransparency.types false in
@[deprecated Cover.RelativeGluingData.toBase_preimage_eq_opensRange_ι (since := "2026-02-01")]
/--
lemma `PreservesLocalization.colimitDesc_preimage` / 引理 `PreservesLocalization.colimitDesc_preimage`

English:
lemma PreservesLocalization.colimitDesc_preimage
  statement: (F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
  proof: by
  simpa using! (relativeGluingData H).toBase_preimage_eq_opensRange_ι U

@[deprecated (since := "2026-02-01")]
alias _root_.AlgebraicGeometry.Scheme.preservesLocalization_toOpensFunctor :=
  NatTrans.Coequifibered.of_isIso

中文:
引理 PreservesLocalization.colimitDesc_preimage
  结论: (F : X.AffineZariskiSiteᵒᵖ ⥤ 交换环范畴)
  证明: by
  simpa using! (relativeGluingData H).toBase_preimage_eq_opensRange_ι U

@[deprecated (since := "2026-02-01")]
alias _root_.AlgebraicGeometry.Scheme.preservesLocalization_toOpensFunctor :=
  NatTrans.Coequifibered.of_isIso

Depends on / 依赖: relativeGluingData
-/
lemma PreservesLocalization.colimitDesc_preimage (F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F)
    (H : α.Coequifibered) (U : X.AffineZariskiSite) :
    (relativeGluingData H).toBase ⁻¹ᵁ U.1 = ((relativeGluingData H).cover.f U).opensRange := by
  simpa using! (relativeGluingData H).toBase_preimage_eq_opensRange_ι U

@[deprecated (since := "2026-02-01")]
alias _root_.AlgebraicGeometry.Scheme.preservesLocalization_toOpensFunctor :=
  NatTrans.Coequifibered.of_isIso

set_option backward.isDefEq.respectTransparency false in
variable (X) in
/--
Definition of `isColimitCocone` / `isColimitCocone` 的定义

English:
definition isColimitCocone
  signature: : IsColimit (cocone X)
  body: letI D := relativeGluingData (X := X) (.of_isIso (𝟙 _))
  letI F := D.functor
  -- Why doesn't typeclass synthesis work here?
  -- It does fire if one adds `(C := no_index(_))` to the composition in the instance.
  haveI : (D.functor ⋙ forget).IsLocallyDirected :=
    Cover.RelativeGluingData.instIs

中文:
定义 isColimitCocone
  签名: : 是余极限 (cocone X)
  定义体: letI D := relativeGluingData (X := X) (.of_isIso (𝟙 _))
  letI F := D.functor
  -- Why doesn't typeclass synthesis work here?
  -- It does fire if one adds `(C := no_index(_))` to the composition in the instance.
  haveI : (D.functor ⋙ forget).IsLocallyDirected :=
    Cover.RelativeGluingData.instIs

Depends on / 依赖: D.functor, functor, of_isIso, relativeGluingData
-/
noncomputable def isColimitCocone : IsColimit (cocone X) :=
  letI D := relativeGluingData (X := X) (.of_isIso (𝟙 _))
  letI F := D.functor
  -- Why doesn't typeclass synthesis work here?
  -- It does fire if one adds `(C := no_index(_))` to the composition in the instance.
  haveI : (D.functor ⋙ forget).IsLocallyDirected :=
    Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  haveI : IsIso ((colimit.isColimit F).desc (cocone X:)) := by
    refine (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _)
      (X.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top X))).mpr fun U => ?_
    change IsIso (pullback.snd (colimit.desc F (cocone X)) U.1.ι)
    let e := IsOpenImmersion.isoOfRangeEq (pullback.fst (colimit.desc F (cocone X)) U.1.ι)
(U.2.isoSpec.hom ≫ colimit.ι F U) by
      rw [Pullback.range_fst]; rw [Opens.range_ι]; rw [← Hom.coe_opensRange]; rw [Hom.opensRange_comp_of_isIso]; rw [← Scheme.Hom.coe_preimage]
      convert! congr($(D.toBase_preimage_eq_opensRange_ι U).1)
      · delta cocone
        congr with U
        simp [D, relativeGluingData, restrictIsoSpec]
      · simp
    convert! (inferInstance : IsIso e.hom)
    rw [← cancel_mono U.1.ι]; rw [← Iso.inv_comp_eq]
    simp [e, ← pullback.condition, IsAffineOpen.isoSpec_hom]
  .ofPointIso (colimit.isColimit F)

end PreservesLocalization

end Scheme.AffineZariskiSite

end AlgebraicGeometry
