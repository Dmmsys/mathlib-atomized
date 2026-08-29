/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Data.Finite.Prod
public import Mathlib.GroupTheory.MonoidLocalization.MonoidWithZero
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.OreLocalization.Ring

/-!
# Localizations of commutative rings

This file contains various basic results on localizations.

We characterize the localization of a commutative ring `R` at a submonoid `M` up to
isomorphism; that is, a commutative ring `S` is the localization of `R` at `M` iff we can find a
ring homomorphism `f : R →+* S` satisfying 3 properties:
1. For all `y ∈ M`, `f y` is a unit;
2. For all `z : S`, there exists `(x, y) : R × M` such that `z * f y = f x`;
3. For all `x, y : R` such that `f x = f y`, there exists `c ∈ M` such that `x * c = y * c`.
   (The converse is a consequence of 1.)

In the following, let `R, P` be commutative rings, `S, Q` be `R`- and `P`-algebras
and `M, T` be submonoids of `R` and `P` respectively, e.g.:
```
variable (R S P Q : Type*) [CommRing R] [CommRing S] [CommRing P] [CommRing Q]
variable [Algebra R S] [Algebra P Q] (M : Submonoid R) (T : Submonoid P)
```

## Main definitions

* `IsLocalization.algEquiv`: if `Q` is another localization of `R` at `M`, then `S` and `Q`
  are isomorphic as `R`-algebras

## Implementation notes

In maths it is natural to reason up to isomorphism, but in Lean we cannot naturally `rewrite` one
structure with an isomorphic one; one way around this is to isolate a predicate characterizing
a structure up to isomorphism, and reason about things that satisfy the predicate.

A previous version of this file used a fully bundled type of ring localization maps,
then used a type synonym `f.codomain` for `f : LocalizationMap M S` to instantiate the
`R`-algebra structure on `S`. This results in defining ad-hoc copies for everything already
defined on `S`. By making `IsLocalization` a predicate on the `algebraMap R S`,
we can ensure the localization map commutes nicely with other `algebraMap`s.

To prove most lemmas about a localization map `algebraMap R S` in this file we invoke the
corresponding proof for the underlying `CommMonoid` localization map
`IsLocalization.toLocalizationMap M S`, which can be found in `GroupTheory.MonoidLocalization`
and the namespace `Submonoid.LocalizationMap`.

To reason about the localization as a quotient type, use `mk_eq_of_mk'` and associated lemmas.
These show the quotient map `mk : R → M → Localization M` equals the surjection
`LocalizationMap.mk'` induced by the map `algebraMap : R →+* Localization M`.
The lemma `mk_eq_of_mk'` hence gives you access to the results in the rest of the file,
which are about the `LocalizationMap.mk'` induced by any localization map.

The proof that "a `CommRing` `K` which is the localization of an integral domain `R` at `R \ {0}`
is a field" is a `def` rather than an `instance`, so if you want to reason about a field of
fractions `K`, assume `[Field K]` instead of just `[CommRing K]`.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

@[expose] public section

assert_not_exists Ideal

open Function

namespace Localization

open IsLocalization

variable {ι : Type*} {R : ι -> Type*} [forall i, CommSemiring (R i)]
variable {i : ι} (S : Submonoid (R i))

/--
Definition of `mapPiEvalRingHom` / `mapPiEvalRingHom` 的定义

English:
abbreviation mapPiEvalRingHom
  signature: :
  body: map (T := S) _ (Pi.evalRingHom R i) le_rfl

中文:
缩写 mapPiEvalRingHom
  签名: :
  定义体: map (T := S) _ (Pi.evalRingHom R i) le_rfl

Depends on / 依赖: Pi.evalRingHom, evalRingHom, le_rfl
-/
noncomputable abbrev mapPiEvalRingHom :
    Localization (S.comap <| Pi.evalRingHom R i) ->+* Localization S :=
  map (T := S) _ (Pi.evalRingHom R i) le_rfl

open Function in
/--
theorem `mapPiEvalRingHom_bijective` / 定理 `mapPiEvalRingHom_bijective`

English:
theorem mapPiEvalRingHom_bijective
  statement: Bijective (mapPiEvalRingHom S)
  proof: by
  let T := S.comap (Pi.evalRingHom R i)
  classical
  refine ⟨fun x₁ x₂ eq => ?_, fun x => ?_⟩
  · obtain ⟨r₁, s₁, rfl⟩ := exists_mk'_eq T x₁
    obtain ⟨r₂, s₂, rfl⟩ := exists_mk'_eq T x₂
    simp_rw [map_mk'] at eq
    rw [IsLocalization.eq] at eq ⊢
    obtain ⟨s, hs⟩ := eq
    refine ⟨⟨update 0 i s, by apply update_self i s.1 0 ▸ s.2⟩, funext fun j => ?_⟩
    obtain rfl | ne := eq_or_ne j i
    · simpa using hs
    · simp [update_of_ne ne]
  · obtain ⟨r, s, rfl⟩ := exists_mk'_eq S x
    exact ⟨mk' (M := T) _ (update 0 i r) ⟨update 0 i s, by apply update_self i s.1 0 ▸ s.2⟩,
      by simp [map_mk']⟩

中文:
定理 mapPiEvalRingHom_bijective
  结论: 双射 (mapPiEvalRingHom S)
  证明: by
  let T := S.comap (Pi.evalRingHom R i)
  classical
  refine ⟨fun x₁ x₂ eq => ?_, fun x => ?_⟩
  · obtain ⟨r₁, s₁, rfl⟩ := exists_mk'_eq T x₁
    obtain ⟨r₂, s₂, rfl⟩ := exists_mk'_eq T x₂
    simp_rw [map_mk'] at eq
    rw [IsLocalization.eq] at eq ⊢
    obtain ⟨s, hs⟩ := eq
    refine ⟨⟨update 0 i s, by apply update_self i s.1 0 ▸ s.2⟩, funext fun j => ?_⟩
    obtain rfl | ne := eq_or_ne j i
    · simpa using hs
    · simp [update_of_ne ne]
  · obtain ⟨r, s, rfl⟩ := exists_mk'_eq S x
    exact ⟨mk' (M := T) _ (update 0 i r) ⟨update 0 i s, by apply update_self i s.1 0 ▸ s.2⟩,
      by simp [map_mk']⟩

Depends on / 依赖: IsLocalization, IsLocalization.eq, Pi.evalRingHom, S.comap, classical, eq_or_ne, evalRingHom, exists_mk, map_mk, simp_rw, update, update_of_ne, update_self
-/
theorem mapPiEvalRingHom_bijective : Bijective (mapPiEvalRingHom S) := by
  let T := S.comap (Pi.evalRingHom R i)
  classical
  refine ⟨fun x₁ x₂ eq => ?_, fun x => ?_⟩
  · obtain ⟨r₁, s₁, rfl⟩ := exists_mk'_eq T x₁
    obtain ⟨r₂, s₂, rfl⟩ := exists_mk'_eq T x₂
    simp_rw [map_mk'] at eq
    rw [IsLocalization.eq] at eq ⊢
    obtain ⟨s, hs⟩ := eq
    refine ⟨⟨update 0 i s, by apply update_self i s.1 0 ▸ s.2⟩, funext fun j => ?_⟩
    obtain rfl | ne := eq_or_ne j i
    · simpa using hs
    · simp [update_of_ne ne]
  · obtain ⟨r, s, rfl⟩ := exists_mk'_eq S x
    exact ⟨mk' (M := T) _ (update 0 i r) ⟨update 0 i s, by apply update_self i s.1 0 ▸ s.2⟩,
      by simp [map_mk']⟩

end Localization

section CommSemiring

variable {R : Type*} [CommSemiring R] {M N : Submonoid R} {S : Type*} [CommSemiring S]
variable [Algebra R S] {P : Type*} [CommSemiring P]

namespace IsLocalization

section IsLocalization

variable [IsLocalization M S]

include M in
variable (R M) in
/--
lemma `finite` / 引理 `finite`

English:
lemma finite
  given: [Finite R]
  statement: Finite S
  proof: by
  have : Function.Surjective (Function.uncurry (mk' (M := M) S)) := fun x => by
    simpa using IsLocalization.exists_mk'_eq M x
  exact .of_surjective _ this

中文:
引理 finite
  条件: [有限 R]
  结论: 有限 S
  证明: by
  have : Function.Surjective (Function.uncurry (mk' (M := M) S)) := fun x => by
    simpa using IsLocalization.exists_mk'_eq M x
  exact .of_surjective _ this
-/
protected lemma finite [Finite R] : Finite S := by
  have : Function.Surjective (Function.uncurry (mk' (M := M) S)) := fun x => by
    simpa using IsLocalization.exists_mk'_eq M x
  exact .of_surjective _ this

section CompatibleSMul

variable (N₁ N₂ : Type*) [AddCommMonoid N₁] [AddCommMonoid N₂] [Module R N₁] [Module R N₂]

set_option backward.isDefEq.respectTransparency false in
variable (M S) in
include M in
/--
theorem `linearMap_compatibleSMul` / 定理 `linearMap_compatibleSMul`

English:
theorem linearMap_compatibleSMul
  statement: [Module S N₁] [Module S N₂]
  proof: by
    obtain ⟨r, m, rfl⟩ := exists_mk'_eq M s
    rw [← (map_units S m).smul_left_cancel]
    simp_rw [algebraMap_smul, ← map_smul, ← smul_assoc, smul_mk'_self, algebraMap_smul, map_smul]

中文:
定理 linearMap_compatibleSMul
  结论: [模 S N₁] [模 S N₂]
  证明: by
    obtain ⟨r, m, rfl⟩ := exists_mk'_eq M s
    rw [← (map_units S m).smul_left_cancel]
    simp_rw [algebraMap_smul, ← map_smul, ← smul_assoc, smul_mk'_self, algebraMap_smul, map_smul]

Depends on / 依赖: _self, algebraMap_smul, exists_mk, map_smul, map_units, simp_rw, smul_assoc, smul_left_cancel, smul_mk
-/
theorem linearMap_compatibleSMul [Module S N₁] [Module S N₂]
    [IsScalarTower R S N₁] [IsScalarTower R S N₂] :
    LinearMap.CompatibleSMul N₁ N₂ S R where
  map_smul f s s' := by
    obtain ⟨r, m, rfl⟩ := exists_mk'_eq M s
    rw [← (map_units S m).smul_left_cancel]
    simp_rw [algebraMap_smul, ← map_smul, ← smul_assoc, smul_mk'_self, algebraMap_smul, map_smul]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Module
  signature: (Localization M) N₁] [Module (Localization M) N₂]
  body: linearMap_compatibleSMul M ..

中文:
实例 [模
  签名: (Localization M) N₁] [模 (Localization M) N₂]
  定义体: linearMap_compatibleSMul M ..

Depends on / 依赖: linearMap_compatibleSMul
-/
instance [Module (Localization M) N₁] [Module (Localization M) N₂]
    [IsScalarTower R (Localization M) N₁] [IsScalarTower R (Localization M) N₂] :
    LinearMap.CompatibleSMul N₁ N₂ (Localization M) R :=
  linearMap_compatibleSMul M ..

end CompatibleSMul

variable {g : R ->+* P} (hg : forall y : M, IsUnit (g y))

variable (M) in
include M in
-- This is not an instance since the submonoid `M` would become a metavariable in typeclass search.
/--
theorem `algHom_subsingleton` / 定理 `algHom_subsingleton`

English:
theorem algHom_subsingleton
  given: [Algebra R P]
  statement: Subsingleton (S ->ₐ[R] P)
  proof: ⟨fun f g =>
AlgHom.coe_ringHom_injective
IsLocalization.ringHom_ext M by rw [f.comp_algebraMap, g.comp_algebraMap]⟩

中文:
定理 algHom_subsingleton
  条件: [代数 R P]
  结论: 子单例 (S ->ₐ[R] P)
  证明: ⟨fun f g =>
AlgHom.coe_ringHom_injective
IsLocalization.ringHom_ext M by rw [f.comp_algebraMap, g.comp_algebraMap]⟩

Depends on / 依赖: AlgHom, AlgHom.coe_ringHom_injective, IsLocalization, IsLocalization.ringHom_ext, coe_ringHom_injective, comp_algebraMap, f.comp_algebraMap, g.comp_algebraMap, ringHom_ext
-/
theorem algHom_subsingleton [Algebra R P] : Subsingleton (S ->ₐ[R] P) :=
  ⟨fun f g =>
AlgHom.coe_ringHom_injective
IsLocalization.ringHom_ext M by rw [f.comp_algebraMap, g.comp_algebraMap]⟩

section AlgEquiv

variable {Q : Type*} [CommSemiring Q] [Algebra R Q] [IsLocalization M Q]

section

variable (M S Q)

/-- If `S`, `Q` are localizations of `R` at the submonoid `M` respectively,
there is an isomorphism of localizations `S ≃ₐ[R] Q`. -/
@[simps!]
/--
Definition of `algEquiv` / `algEquiv` 的定义

English:
definition algEquiv
  signature: : S ≃ₐ[R] Q
  body: { ringEquivOfRingEquiv S Q (RingEquiv.refl R) M.map_id with
    commutes' := ringEquivOfRingEquiv_eq _ }

中文:
定义 algEquiv
  签名: : S ≃ₐ[R] Q
  定义体: { ringEquivOfRingEquiv S Q (RingEquiv.refl R) M.map_id with
    commutes' := ringEquivOfRingEquiv_eq _ }

Depends on / 依赖: M.map_id, RingEquiv, RingEquiv.refl, commutes, map_id, ringEquivOfRingEquiv, ringEquivOfRingEquiv_eq
-/
noncomputable def algEquiv : S ≃ₐ[R] Q :=
  { ringEquivOfRingEquiv S Q (RingEquiv.refl R) M.map_id with
    commutes' := ringEquivOfRingEquiv_eq _ }

end

/--
theorem `algEquiv_mk'` / 定理 `algEquiv_mk'`

English:
theorem algEquiv_mk'
  given: (x : R) (y : M)
  statement: algEquiv M S Q (mk' S x y) = mk' Q x y
  proof: by
  simp

中文:
定理 algEquiv_mk'
  条件: (x : R) (y : M)
  结论: algEquiv M S Q (mk' S x y) = mk' Q x y
  证明: by
  simp

Depends on / 依赖: const_smul, continuous_apply, continuous_pi
-/
theorem algEquiv_mk' (x : R) (y : M) : algEquiv M S Q (mk' S x y) = mk' Q x y := by
  simp

/--
theorem `algEquiv_symm_mk'` / 定理 `algEquiv_symm_mk'`

English:
theorem algEquiv_symm_mk'
  given: (x : R) (y : M)
  statement: (algEquiv M S Q).symm (mk' Q x y) = mk' S x y
  proof: by simp

中文:
定理 algEquiv_symm_mk'
  条件: (x : R) (y : M)
  结论: (algEquiv M S Q).symm (mk' Q x y) = mk' S x y
  证明: by simp
-/
theorem algEquiv_symm_mk' (x : R) (y : M) : (algEquiv M S Q).symm (mk' Q x y) = mk' S x y := by simp

variable (M) in
include M in
/--
lemma `bijective` / 引理 `bijective`

English:
lemma bijective
  given: (f : S ->+* Q) (hf : f.comp (algebraMap R S) = algebraMap R Q)
  proof: (show f = IsLocalization.algEquiv M S Q by
    apply IsLocalization.ringHom_ext M; rw [hf]; ext; simp) ▸
    (IsLocalization.algEquiv M S Q).toEquiv.bijective

中文:
引理 bijective
  条件: (f : S ->+* Q) (hf : f.comp (algebraMap R S) = algebraMap R Q)
  证明: (show f = IsLocalization.algEquiv M S Q by
    apply IsLocalization.ringHom_ext M; rw [hf]; ext; simp) ▸
    (IsLocalization.algEquiv M S Q).toEquiv.bijective
-/
protected lemma bijective (f : S ->+* Q) (hf : f.comp (algebraMap R S) = algebraMap R Q) :
    Function.Bijective f :=
  (show f = IsLocalization.algEquiv M S Q by
    apply IsLocalization.ringHom_ext M; rw [hf]; ext; simp) ▸
    (IsLocalization.algEquiv M S Q).toEquiv.bijective

end AlgEquiv

section liftAlgHom

variable {A : Type*} [CommSemiring A]
  {R : Type*} [CommSemiring R] [Algebra A R] {M : Submonoid R}
  {S : Type*} [CommSemiring S] [Algebra A S] [Algebra R S] [IsScalarTower A R S]
  {P : Type*} [CommSemiring P] [Algebra A P] [IsLocalization M S]
  {f : R ->ₐ[A] P} (hf : forall y : M, IsUnit (f y)) (x : S)
include hf

/--
Definition of `liftAlgHom` / `liftAlgHom` 的定义

English:
definition liftAlgHom
  signature: : S ->ₐ[A] P where
  body: lift hf
  commutes' r := by simp [IsScalarTower.algebraMap_apply A R S]

中文:
定义 liftAlgHom
  签名: : S ->ₐ[A] P where
  定义体: lift hf
  commutes' r := by simp [IsScalarTower.algebraMap_apply A R S]
-/
noncomputable def liftAlgHom : S ->ₐ[A] P where
  __ := lift hf
  commutes' r := by simp [IsScalarTower.algebraMap_apply A R S]

/--
theorem `liftAlgHom_toRingHom` / 定理 `liftAlgHom_toRingHom`

English:
theorem liftAlgHom_toRingHom
  statement: (liftAlgHom hf : S ->ₐ[A] P).toRingHom = lift hf
  proof: rfl

@[simp]

中文:
定理 liftAlgHom_toRingHom
  结论: (liftAlgHom hf : S ->ₐ[A] P).toRingHom = lift hf
  证明: rfl

@[simp]
-/
theorem liftAlgHom_toRingHom : (liftAlgHom hf : S ->ₐ[A] P).toRingHom = lift hf := rfl

@[simp]
/--
theorem `coe_liftAlgHom` / 定理 `coe_liftAlgHom`

English:
theorem coe_liftAlgHom
  statement: ⇑(liftAlgHom hf : S ->ₐ[A] P) = lift hf
  proof: rfl

中文:
定理 coe_liftAlgHom
  结论: ⇑(liftAlgHom hf : S ->ₐ[A] P) = lift hf
  证明: rfl
-/
theorem coe_liftAlgHom : ⇑(liftAlgHom hf : S ->ₐ[A] P) = lift hf := rfl

/--
theorem `liftAlgHom_apply` / 定理 `liftAlgHom_apply`

English:
theorem liftAlgHom_apply
  statement: liftAlgHom hf x = lift hf x
  proof: rfl

中文:
定理 liftAlgHom_apply
  结论: liftAlgHom hf x = lift hf x
  证明: rfl
-/
theorem liftAlgHom_apply : liftAlgHom hf x = lift hf x := rfl

end liftAlgHom

section AlgEquivOfAlgEquiv

variable {A : Type*} [CommSemiring A]
  {R : Type*} [CommSemiring R] [Algebra A R] {M : Submonoid R} (S : Type*)
  [CommSemiring S] [Algebra A S] [Algebra R S] [IsScalarTower A R S] [IsLocalization M S]
  {P : Type*} [CommSemiring P] [Algebra A P] {T : Submonoid P} (Q : Type*)
  [CommSemiring Q] [Algebra A Q] [Algebra P Q] [IsScalarTower A P Q] [IsLocalization T Q]
  (h : R ≃ₐ[A] P) (H : Submonoid.map h M = T)

include H

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `S`, `Q` are localizations of `R` and `P` at submonoids `M`, `T` respectively,
an isomorphism `h : R ≃ₐ[A] P` such that `h(M) = T` induces an isomorphism of localizations
`S ≃ₐ[A] Q`. -/
@[simps!]
/--
Definition of `algEquivOfAlgEquiv` / `algEquivOfAlgEquiv` 的定义

English:
definition algEquivOfAlgEquiv
  signature: : S ≃ₐ[A] Q where
  body: ringEquivOfRingEquiv S Q h.toRingEquiv H
  commutes' _ := by dsimp; rw [IsScalarTower.algebraMap_apply A R S, map_eq,
    RingHom.coe_coe, AlgEquiv.commutes, IsScalarTower.algebraMap_apply A P Q]

中文:
定义 algEquivOfAlgEquiv
  签名: : S ≃ₐ[A] Q where
  定义体: ringEquivOfRingEquiv S Q h.toRingEquiv H
  commutes' _ := by dsimp; rw [IsScalarTower.algebraMap_apply A R S, map_eq,
    RingHom.coe_coe, AlgEquiv.commutes, IsScalarTower.algebraMap_apply A P Q]

Depends on / 依赖: h.toRingEquiv, ringEquivOfRingEquiv, toRingEquiv
-/
noncomputable def algEquivOfAlgEquiv : S ≃ₐ[A] Q where
  __ := ringEquivOfRingEquiv S Q h.toRingEquiv H
  commutes' _ := by dsimp; rw [IsScalarTower.algebraMap_apply A R S, map_eq,
    RingHom.coe_coe, AlgEquiv.commutes, IsScalarTower.algebraMap_apply A P Q]

variable {S Q h}

/--
theorem `algEquivOfAlgEquiv_eq_map` / 定理 `algEquivOfAlgEquiv_eq_map`

English:
theorem algEquivOfAlgEquiv_eq_map
  proof: rfl

中文:
定理 algEquivOfAlgEquiv_eq_map
  证明: rfl
-/
theorem algEquivOfAlgEquiv_eq_map :
    (algEquivOfAlgEquiv S Q h H : S ->+* Q) =
      map Q (h : R ->+* P) (M.le_comap_of_map_le (le_of_eq H)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `algEquivOfAlgEquiv_eq` / 定理 `algEquivOfAlgEquiv_eq`

English:
theorem algEquivOfAlgEquiv_eq
  given: (x : R)
  proof: by
  simp

中文:
定理 algEquivOfAlgEquiv_eq
  条件: (x : R)
  证明: by
  simp
-/
theorem algEquivOfAlgEquiv_eq (x : R) :
    algEquivOfAlgEquiv S Q h H ((algebraMap R S) x) = algebraMap P Q (h x) := by
  simp

set_option backward.isDefEq.respectTransparency false in
set_option linter.docPrime false in
/--
theorem `algEquivOfAlgEquiv_mk'` / 定理 `algEquivOfAlgEquiv_mk'`

English:
theorem algEquivOfAlgEquiv_mk'
  given: (x : R) (y : M)
  proof: by
  simp [map_mk']

中文:
定理 algEquivOfAlgEquiv_mk'
  条件: (x : R) (y : M)
  证明: by
  simp [map_mk']

Depends on / 依赖: map_mk
-/
theorem algEquivOfAlgEquiv_mk' (x : R) (y : M) :
    algEquivOfAlgEquiv S Q h H (mk' S x y) =
      mk' Q (h x) ⟨h y, show h y in T from H ▸ Set.mem_image_of_mem h y.2⟩ := by
  simp [map_mk']

/--
theorem `algEquivOfAlgEquiv_symm` / 定理 `algEquivOfAlgEquiv_symm`

English:
theorem algEquivOfAlgEquiv_symm
  statement: (algEquivOfAlgEquiv S Q h H).symm =
  proof: rfl

中文:
定理 algEquivOfAlgEquiv_symm
  结论: (algEquivOfAlgEquiv S Q h H).symm =
  证明: rfl
-/
theorem algEquivOfAlgEquiv_symm : (algEquivOfAlgEquiv S Q h H).symm =
    algEquivOfAlgEquiv Q S h.symm (show Submonoid.map h.symm T = M by
      rw [← H]; rw [← Submonoid.map_coe_toMulEquiv]; rw [AlgEquiv.symm_toMulEquiv]; rw [← Submonoid.comap_equiv_eq_map_symm]; rw [← Submonoid.map_coe_toMulEquiv]; rw [Submonoid.comap_map_eq_of_injective (h : R ≃* P).injective]) := rfl

end AlgEquivOfAlgEquiv

section smul

variable {R : Type*} [CommSemiring R] {S : Submonoid R}
variable {R' : Type*} [CommSemiring R'] [Algebra R R'] [IsLocalization S R']
variable {M' : Type*} [AddCommMonoid M'] [Module R' M'] [Module R M'] [IsScalarTower R R' M']

/--
lemma `smul_mem_iff` / 引理 `smul_mem_iff`

English:
lemma smul_mem_iff
  given: {N' : Submodule R' M'} {x : M'} {s : S}
  proof: by
  refine ⟨fun h => ?_, fun h => Submodule.smul_of_tower_mem N' s h⟩
  rwa [← Submodule.smul_mem_iff_of_isUnit (r := algebraMap R R' s) N' (map_units R' s),
    algebraMap_smul]

中文:
引理 smul_mem_iff
  条件: {N' : 子模 R' M'} {x : M'} {s : S}
  证明: by
  refine ⟨fun h => ?_, fun h => Submodule.smul_of_tower_mem N' s h⟩
  rwa [← Submodule.smul_mem_iff_of_isUnit (r := algebraMap R R' s) N' (map_units R' s),
    algebraMap_smul]

Depends on / 依赖: Submodule, Submodule.smul_mem_iff_of_isUnit, Submodule.smul_of_tower_mem, algebraMap, algebraMap_smul, map_units, smul_mem_iff_of_isUnit, smul_of_tower_mem
-/
lemma smul_mem_iff {N' : Submodule R' M'} {x : M'} {s : S} :
    s • x in N' ↔ x in N' := by
  refine ⟨fun h => ?_, fun h => Submodule.smul_of_tower_mem N' s h⟩
  rwa [← Submodule.smul_mem_iff_of_isUnit (r := algebraMap R R' s) N' (map_units R' s),
    algebraMap_smul]

end smul

section Units

/--
lemma `of_le_isUnit_of_bijective` / 引理 `of_le_isUnit_of_bijective`

English:
lemma of_le_isUnit_of_bijective
  statement: {M : Submonoid R}
  proof: hM ⟨_, y.prop, rfl⟩
  surj y := by
    obtain ⟨x, rfl⟩ := h.surjective y
    use ⟨x, 1⟩
    simp
  exists_of_eq {x y} hxy := ⟨1, by simp [h.injective hxy]⟩

中文:
引理 of_le_isUnit_of_bijective
  结论: {M : 子幺半群 R}
  证明: hM ⟨_, y.prop, rfl⟩
  surj y := by
    obtain ⟨x, rfl⟩ := h.surjective y
    use ⟨x, 1⟩
    simp
  exists_of_eq {x y} hxy := ⟨1, by simp [h.injective hxy]⟩

Depends on / 依赖: y.prop
-/
lemma of_le_isUnit_of_bijective {M : Submonoid R}
    (hM : Algebra.algebraMapSubmonoid S M <= IsUnit.submonoid S)
    (h : Function.Bijective (algebraMap R S)) :
    IsLocalization M S where
  map_units y := hM ⟨_, y.prop, rfl⟩
  surj y := by
    obtain ⟨x, rfl⟩ := h.surjective y
    use ⟨x, 1⟩
    simp
  exists_of_eq {x y} hxy := ⟨1, by simp [h.injective hxy]⟩

/--
lemma `of_le_isUnit` / 引理 `of_le_isUnit`

English:
lemma of_le_isUnit
  given: {S : Submonoid R} (hS : S <= IsUnit.submonoid R)
  statement: IsLocalization S R
  proof: of_le_isUnit_of_bijective (by simpa) Function.bijective_id

@[deprecated (since := "2026-04-15")]
alias at_units := of_le_isUnit

中文:
引理 of_le_isUnit
  条件: {S : 子幺半群 R} (hS : S <= 是单位.submonoid R)
  结论: 是Localization S R
  证明: of_le_isUnit_of_bijective (by simpa) Function.bijective_id

@[deprecated (since := "2026-04-15")]
alias at_units := of_le_isUnit

Depends on / 依赖: Function, Function.bijective_id, bijective_id, of_le_isUnit_of_bijective
-/
lemma of_le_isUnit {S : Submonoid R} (hS : S <= IsUnit.submonoid R) : IsLocalization S R :=
  of_le_isUnit_of_bijective (by simpa) Function.bijective_id

@[deprecated (since := "2026-04-15")]
alias at_units := of_le_isUnit

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocalization (IsUnit.submonoid R) R
  body: of_le_isUnit le_rfl

中文:
实例 :
  签名: 是Localization (是单位.submonoid R) R
  定义体: of_le_isUnit le_rfl

Depends on / 依赖: le_rfl, of_le_isUnit
-/
instance : IsLocalization (IsUnit.submonoid R) R := of_le_isUnit le_rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocalization (Algebra.algebraMapSubmonoid S (IsUnit.submonoid R)) S
  body: IsLocalization.of_le_isUnit Algebra.algebraMapSubmonoid_isUnit_le

中文:
实例 :
  签名: 是Localization (代数.algebraMapSubmonoid S (是单位.submonoid R)) S
  定义体: IsLocalization.of_le_isUnit Algebra.algebraMapSubmonoid_isUnit_le

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid_isUnit_le, IsLocalization, IsLocalization.of_le_isUnit, algebraMapSubmonoid_isUnit_le, of_le_isUnit
-/
instance : IsLocalization (Algebra.algebraMapSubmonoid S (IsUnit.submonoid R)) S :=
  IsLocalization.of_le_isUnit Algebra.algebraMapSubmonoid_isUnit_le

variable (R M)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `atUnits` / `atUnits` 的定义

English:
definition atUnits
  signature: (H : M <= IsUnit.submonoid R)
  body: by
  refine AlgEquiv.ofBijective (Algebra.ofId R S) ⟨?_, ?_⟩
  · intro x y hxy
    obtain ⟨c, eq⟩ := (IsLocalization.eq_iff_exists M S).mp hxy
    obtain ⟨u, hu⟩ := H c.prop
    rwa [← hu, Units.mul_right_inj] at eq
  · intro y
    obtain ⟨⟨x, s⟩, eq⟩ := IsLocalization.surj M y
    obtain ⟨u, hu⟩ := H s.prop
    use x * u.inv
    dsimp [Algebra.ofId, RingHom.toFun_eq_coe, AlgHom.coe_mks]
    rw [map_mul]; rw [← eq]; rw [← hu]; rw [mul_assoc]; rw [← map_mul]
    simp

中文:
定义 atUnits
  签名: (H : M <= 是单位.submonoid R)
  定义体: by
  refine AlgEquiv.ofBijective (Algebra.ofId R S) ⟨?_, ?_⟩
  · intro x y hxy
    obtain ⟨c, eq⟩ := (IsLocalization.eq_iff_exists M S).mp hxy
    obtain ⟨u, hu⟩ := H c.prop
    rwa [← hu, Units.mul_right_inj] at eq
  · intro y
    obtain ⟨⟨x, s⟩, eq⟩ := IsLocalization.surj M y
    obtain ⟨u, hu⟩ := H s.prop
    use x * u.inv
    dsimp [Algebra.ofId, RingHom.toFun_eq_coe, AlgHom.coe_mks]
    rw [map_mul]; rw [← eq]; rw [← hu]; rw [mul_assoc]; rw [← map_mul]
    simp

Depends on / 依赖: AlgEquiv, AlgEquiv.ofBijective, AlgHom, AlgHom.coe_mks, Algebra, Algebra.ofId, IsLocalization, IsLocalization.eq_iff_exists, IsLocalization.surj, RingHom, RingHom.toFun_eq_coe, Units.mul_right_inj, c.prop, coe_mks, eq_iff_exists, map_mul, mul_assoc, mul_right_inj, ofBijective, s.prop
-/
noncomputable def atUnits (H : M <= IsUnit.submonoid R) : R ≃ₐ[R] S := by
  refine AlgEquiv.ofBijective (Algebra.ofId R S) ⟨?_, ?_⟩
  · intro x y hxy
    obtain ⟨c, eq⟩ := (IsLocalization.eq_iff_exists M S).mp hxy
    obtain ⟨u, hu⟩ := H c.prop
    rwa [← hu, Units.mul_right_inj] at eq
  · intro y
    obtain ⟨⟨x, s⟩, eq⟩ := IsLocalization.surj M y
    obtain ⟨u, hu⟩ := H s.prop
    use x * u.inv
    dsimp [Algebra.ofId, RingHom.toFun_eq_coe, AlgHom.coe_mks]
    rw [map_mul]; rw [← eq]; rw [← hu]; rw [mul_assoc]; rw [← map_mul]
    simp

end Units

end IsLocalization

section

variable (M N)

/--
theorem `isLocalization_of_algEquiv` / 定理 `isLocalization_of_algEquiv`

English:
theorem isLocalization_of_algEquiv
  given: [Algebra R P] [IsLocalization M S] (h : S ≃ₐ[R] P)
  proof: by
  constructor; constructor
  · intro y
    convert! (IsLocalization.map_units S y).map h.toAlgHom.toRingHom.toMonoidHom
    exact (h.commutes y).symm
  · intro y
    obtain ⟨⟨x, s⟩, e⟩ := IsLocalization.surj M (h.symm y)
    apply_fun (show S -> P from h) at e
    simp only [map_mul, h.apply_symm_apply, h.commutes] at e
    exact ⟨⟨x, s⟩, e⟩
  · intro x y
    rw [← h.symm.toEquiv.injective.eq_iff]; rw [← IsLocalization.eq_iff_exists M S]; rw [← h.symm.commutes]; rw [←
      h.symm.commutes]
    exact id

中文:
定理 isLocalization_of_algEquiv
  条件: [代数 R P] [是Localization M S] (h : S ≃ₐ[R] P)
  证明: by
  constructor; constructor
  · intro y
    convert! (IsLocalization.map_units S y).map h.toAlgHom.toRingHom.toMonoidHom
    exact (h.commutes y).symm
  · intro y
    obtain ⟨⟨x, s⟩, e⟩ := IsLocalization.surj M (h.symm y)
    apply_fun (show S -> P from h) at e
    simp only [map_mul, h.apply_symm_apply, h.commutes] at e
    exact ⟨⟨x, s⟩, e⟩
  · intro x y
    rw [← h.symm.toEquiv.injective.eq_iff]; rw [← IsLocalization.eq_iff_exists M S]; rw [← h.symm.commutes]; rw [←
      h.symm.commutes]
    exact id

Depends on / 依赖: IsLocalization, IsLocalization.eq_iff_exists, IsLocalization.map_units, IsLocalization.surj, apply_fun, apply_symm_apply, commutes, convert, eq_iff, eq_iff_exists, h.apply_symm_apply, h.commutes, h.symm, h.symm.commutes, h.symm.toEquiv.injective.eq_iff, h.toAlgHom.toRingHom.toMonoidHom, injective, map_mul, map_units, toAlgHom
-/
theorem isLocalization_of_algEquiv [Algebra R P] [IsLocalization M S] (h : S ≃ₐ[R] P) :
    IsLocalization M P := by
  constructor; constructor
  · intro y
    convert! (IsLocalization.map_units S y).map h.toAlgHom.toRingHom.toMonoidHom
    exact (h.commutes y).symm
  · intro y
    obtain ⟨⟨x, s⟩, e⟩ := IsLocalization.surj M (h.symm y)
    apply_fun (show S -> P from h) at e
    simp only [map_mul, h.apply_symm_apply, h.commutes] at e
    exact ⟨⟨x, s⟩, e⟩
  · intro x y
    rw [← h.symm.toEquiv.injective.eq_iff]; rw [← IsLocalization.eq_iff_exists M S]; rw [← h.symm.commutes]; rw [←
      h.symm.commutes]
    exact id

variable {M} in
/--
theorem `self` / 定理 `self`

English:
theorem self
  given: (H : M <= IsUnit.submonoid R)
  statement: IsLocalization M R
  proof: isLocalization_of_algEquiv _ (atUnits _ _ (S := Localization M) H).symm

中文:
定理 self
  条件: (H : M <= 是单位.submonoid R)
  结论: 是Localization M R
  证明: isLocalization_of_algEquiv _ (atUnits _ _ (S := Localization M) H).symm
-/
protected theorem self (H : M <= IsUnit.submonoid R) : IsLocalization M R :=
  isLocalization_of_algEquiv _ (atUnits _ _ (S := Localization M) H).symm

/--
theorem `isLocalization_iff_of_algEquiv` / 定理 `isLocalization_iff_of_algEquiv`

English:
theorem isLocalization_iff_of_algEquiv
  given: [Algebra R P] (h : S ≃ₐ[R] P)
  proof: ⟨fun _ => isLocalization_of_algEquiv M h, fun _ => isLocalization_of_algEquiv M h.symm⟩

中文:
定理 isLocalization_iff_of_algEquiv
  条件: [代数 R P] (h : S ≃ₐ[R] P)
  证明: ⟨fun _ => isLocalization_of_algEquiv M h, fun _ => isLocalization_of_algEquiv M h.symm⟩

Depends on / 依赖: h.symm, isLocalization_of_algEquiv
-/
theorem isLocalization_iff_of_algEquiv [Algebra R P] (h : S ≃ₐ[R] P) :
    IsLocalization M S ↔ IsLocalization M P :=
  ⟨fun _ => isLocalization_of_algEquiv M h, fun _ => isLocalization_of_algEquiv M h.symm⟩

/--
theorem `isLocalization_iff_of_ringEquiv` / 定理 `isLocalization_iff_of_ringEquiv`

English:
theorem isLocalization_iff_of_ringEquiv
  given: (h : S ≃+* P)
  proof: (h.toRingHom.comp <| algebraMap R S).toAlgebra; IsLocalization M P :=
  letI := (h.toRingHom.comp <| algebraMap R S).toAlgebra
  isLocalization_iff_of_algEquiv M { h with commutes' := fun _ => rfl }

中文:
定理 isLocalization_iff_of_ringEquiv
  条件: (h : S ≃+* P)
  证明: (h.toRingHom.comp <| algebraMap R S).toAlgebra; IsLocalization M P :=
  letI := (h.toRingHom.comp <| algebraMap R S).toAlgebra
  isLocalization_iff_of_algEquiv M { h with commutes' := fun _ => rfl }

Depends on / 依赖: IsLocalization, algebraMap, h.toRingHom.comp, toAlgebra, toRingHom
-/
theorem isLocalization_iff_of_ringEquiv (h : S ≃+* P) :
    IsLocalization M S ↔
      haveI := (h.toRingHom.comp <| algebraMap R S).toAlgebra; IsLocalization M P :=
  letI := (h.toRingHom.comp <| algebraMap R S).toAlgebra
  isLocalization_iff_of_algEquiv M { h with commutes' := fun _ => rfl }

variable (S) in
/--
theorem `isLocalization_iff_of_isLocalization` / 定理 `isLocalization_iff_of_isLocalization`

English:
theorem isLocalization_iff_of_isLocalization
  statement: [IsLocalization M S] [IsLocalization N S]
  proof: ⟨fun _ => isLocalization_of_algEquiv N (algEquiv M S P),
    fun _ => isLocalization_of_algEquiv M (algEquiv N S P)⟩

中文:
定理 isLocalization_iff_of_isLocalization
  结论: [是Localization M S] [是Localization N S]
  证明: ⟨fun _ => isLocalization_of_algEquiv N (algEquiv M S P),
    fun _ => isLocalization_of_algEquiv M (algEquiv N S P)⟩

Depends on / 依赖: algEquiv, isLocalization_of_algEquiv
-/
theorem isLocalization_iff_of_isLocalization [IsLocalization M S] [IsLocalization N S]
    [Algebra R P] : IsLocalization M P ↔ IsLocalization N P :=
  ⟨fun _ => isLocalization_of_algEquiv N (algEquiv M S P),
    fun _ => isLocalization_of_algEquiv M (algEquiv N S P)⟩

/--
theorem `iff_of_le_of_exists_dvd` / 定理 `iff_of_le_of_exists_dvd`

English:
theorem iff_of_le_of_exists_dvd
  given: (N : Submonoid R) (h₁ : M <= N) (h₂ : forall n in N, exists m in M, n ∣ m)
  proof: have : IsLocalization N (Localization M) := of_le_of_exists_dvd _ _ h₁ h₂
  isLocalization_iff_of_isLocalization _ _ (Localization M)

中文:
定理 iff_of_le_of_存在_dvd
  条件: (N : 子幺半群 R) (h₁ : M <= N) (h₂ : 对任意 n in N, 存在 m in M, n ∣ m)
  证明: have : IsLocalization N (Localization M) := of_le_of_exists_dvd _ _ h₁ h₂
  isLocalization_iff_of_isLocalization _ _ (Localization M)

Depends on / 依赖: IsLocalization, Localization, isLocalization_iff_of_isLocalization, of_le_of_exists_dvd
-/
theorem iff_of_le_of_exists_dvd (N : Submonoid R) (h₁ : M <= N) (h₂ : forall n in N, exists m in M, n ∣ m) :
    IsLocalization M S ↔ IsLocalization N S :=
  have : IsLocalization N (Localization M) := of_le_of_exists_dvd _ _ h₁ h₂
  isLocalization_iff_of_isLocalization _ _ (Localization M)

end

variable (M)

/--
lemma `commutes` / 引理 `commutes`

English:
lemma commutes
  statement: (S₁ S₂ T : Type*) [CommSemiring S₁]
  proof: by
    rintro ⟨m, ⟨a, ha, rfl⟩⟩
    rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply R S₂ T]
    exact IsUnit.map _ (IsLocalization.map_units _ ⟨a, ha⟩)
  surj a := by
    obtain ⟨⟨y, -, m, hm, rfl⟩, hy⟩ := surj (M := Algebra.algebraMapSubmonoid S₂ M₁) a
    rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply R S₁ T] at hy
    obtain ⟨⟨z, n, hn⟩, hz⟩ := IsLocalization.surj (M := M₂) y
    have hunit : IsUnit (algebraMap R S₁ m) := map_units _ ⟨m, hm⟩
    use ⟨algebraMap R S₁ z * hunit.unit⁻¹, ⟨algebraMap R S₁ n, n, hn, rfl⟩⟩
    rw [map_mul]; rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply R S₂ T]
    conv_rhs => rw [← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply R S₂ T]; rw [← hz]; rw [map_mul]; rw [← hy]
    convert_to _ = a * (algebraMap S₂ T) ((algebraMap R S₂) n) *
        (algebraMap S₁ T) (((algebraMap R S₁) m) * hunit.unit⁻¹.val)
    · rw [map_mul]
      ring
    simp
  exists_of_eq {x y} hxy := by
    obtain ⟨r, s, d, hr, hs⟩ := IsLocalization.surj₂ M₁ S₁ x y
    apply_fun (· * algebraMap S₁ T (algebraMap R S₁ d)) at hxy
    simp_rw [← map_mul, hr, hs, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R S₂ T] at hxy
    obtain ⟨⟨-, c, hmc, rfl⟩, hc⟩ := exists_of_eq (M := Algebra.algebraMapSubmonoid S₂ M₁) hxy
    simp_rw [← map_mul] at hc
    obtain ⟨a, ha⟩ := IsLocalization.exists_of_eq (M := M₂) hc
    use ⟨algebraMap R S₁ a, a, a.property, rfl⟩
    apply (map_units S₁ d).mul_right_cancel
    rw [mul_assoc]; rw [hr]; rw [mul_assoc]; rw [hs]
    apply (map_units S₁ ⟨c, hmc⟩).mul_right_cancel
    rw [← map_mul]; rw [← map_mul]; rw [mul_assoc]; rw [mul_comm _ c]; rw [ha]; rw [map_mul]; rw [map_mul]
    ring

中文:
引理 commutes
  结论: (S₁ S₂ T : 类型) [交换半环 S₁]
  证明: by
    rintro ⟨m, ⟨a, ha, rfl⟩⟩
    rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply R S₂ T]
    exact IsUnit.map _ (IsLocalization.map_units _ ⟨a, ha⟩)
  surj a := by
    obtain ⟨⟨y, -, m, hm, rfl⟩, hy⟩ := surj (M := Algebra.algebraMapSubmonoid S₂ M₁) a
    rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply R S₁ T] at hy
    obtain ⟨⟨z, n, hn⟩, hz⟩ := IsLocalization.surj (M := M₂) y
    have hunit : IsUnit (algebraMap R S₁ m) := map_units _ ⟨m, hm⟩
    use ⟨algebraMap R S₁ z * hunit.unit⁻¹, ⟨algebraMap R S₁ n, n, hn, rfl⟩⟩
    rw [map_mul]; rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply R S₂ T]
    conv_rhs => rw [← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply R S₂ T]; rw [← hz]; rw [map_mul]; rw [← hy]
    convert_to _ = a * (algebraMap S₂ T) ((algebraMap R S₂) n) *
        (algebraMap S₁ T) (((algebraMap R S₁) m) * hunit.unit⁻¹.val)
    · rw [map_mul]
      ring
    simp
  exists_of_eq {x y} hxy := by
    obtain ⟨r, s, d, hr, hs⟩ := IsLocalization.surj₂ M₁ S₁ x y
    apply_fun (· * algebraMap S₁ T (algebraMap R S₁ d)) at hxy
    simp_rw [← map_mul, hr, hs, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R S₂ T] at hxy
    obtain ⟨⟨-, c, hmc, rfl⟩, hc⟩ := exists_of_eq (M := Algebra.algebraMapSubmonoid S₂ M₁) hxy
    simp_rw [← map_mul] at hc
    obtain ⟨a, ha⟩ := IsLocalization.exists_of_eq (M := M₂) hc
    use ⟨algebraMap R S₁ a, a, a.property, rfl⟩
    apply (map_units S₁ d).mul_right_cancel
    rw [mul_assoc]; rw [hr]; rw [mul_assoc]; rw [hs]
    apply (map_units S₁ ⟨c, hmc⟩).mul_right_cancel
    rw [← map_mul]; rw [← map_mul]; rw [mul_assoc]; rw [mul_comm _ c]; rw [ha]; rw [map_mul]; rw [map_mul]
    ring

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid, IsLocalization, IsLocalization.map_units, IsLocalization.surj, IsScalarTower, IsScalarTower.algebraMap_apply, IsUnit, IsUnit.map, algebraMap, algebraMapSubmonoid, algebraMap_apply, map_units
-/
lemma commutes (S₁ S₂ T : Type*) [CommSemiring S₁]
    [CommSemiring S₂] [CommSemiring T] [Algebra R S₁] [Algebra R S₂] [Algebra R T] [Algebra S₁ T]
    [Algebra S₂ T] [IsScalarTower R S₁ T] [IsScalarTower R S₂ T] (M₁ M₂ : Submonoid R)
    [IsLocalization M₁ S₁] [IsLocalization M₂ S₂]
    [IsLocalization (Algebra.algebraMapSubmonoid S₂ M₁) T] :
    IsLocalization (Algebra.algebraMapSubmonoid S₁ M₂) T where
  map_units := by
    rintro ⟨m, ⟨a, ha, rfl⟩⟩
    rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply R S₂ T]
    exact IsUnit.map _ (IsLocalization.map_units _ ⟨a, ha⟩)
  surj a := by
    obtain ⟨⟨y, -, m, hm, rfl⟩, hy⟩ := surj (M := Algebra.algebraMapSubmonoid S₂ M₁) a
    rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply R S₁ T] at hy
    obtain ⟨⟨z, n, hn⟩, hz⟩ := IsLocalization.surj (M := M₂) y
    have hunit : IsUnit (algebraMap R S₁ m) := map_units _ ⟨m, hm⟩
    use ⟨algebraMap R S₁ z * hunit.unit⁻¹, ⟨algebraMap R S₁ n, n, hn, rfl⟩⟩
    rw [map_mul]; rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply R S₂ T]
    conv_rhs => rw [← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply R S₂ T]; rw [← hz]; rw [map_mul]; rw [← hy]
    convert_to _ = a * (algebraMap S₂ T) ((algebraMap R S₂) n) *
        (algebraMap S₁ T) (((algebraMap R S₁) m) * hunit.unit⁻¹.val)
    · rw [map_mul]
      ring
    simp
  exists_of_eq {x y} hxy := by
    obtain ⟨r, s, d, hr, hs⟩ := IsLocalization.surj₂ M₁ S₁ x y
    apply_fun (· * algebraMap S₁ T (algebraMap R S₁ d)) at hxy
    simp_rw [← map_mul, hr, hs, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R S₂ T] at hxy
    obtain ⟨⟨-, c, hmc, rfl⟩, hc⟩ := exists_of_eq (M := Algebra.algebraMapSubmonoid S₂ M₁) hxy
    simp_rw [← map_mul] at hc
    obtain ⟨a, ha⟩ := IsLocalization.exists_of_eq (M := M₂) hc
    use ⟨algebraMap R S₁ a, a, a.property, rfl⟩
    apply (map_units S₁ d).mul_right_cancel
    rw [mul_assoc]; rw [hr]; rw [mul_assoc]; rw [hs]
    apply (map_units S₁ ⟨c, hmc⟩).mul_right_cancel
    rw [← map_mul]; rw [← map_mul]; rw [mul_assoc]; rw [mul_comm _ c]; rw [ha]; rw [map_mul]; rw [map_mul]
    ring

variable (Rₘ Sₙ Rₘ' Sₙ' : Type*) [CommSemiring Rₘ] [CommSemiring Sₙ] [CommSemiring Rₘ']
  [CommSemiring Sₙ'] [Algebra R Rₘ] [Algebra S Sₙ] [Algebra R Rₘ'] [Algebra S Sₙ'] [Algebra R Sₙ]
  [Algebra Rₘ Sₙ] [Algebra Rₘ' Sₙ'] [Algebra R Sₙ'] (N : Submonoid S) [IsLocalization M Rₘ]
  [IsLocalization N Sₙ] [IsLocalization M Rₘ'] [IsLocalization N Sₙ'] [IsScalarTower R Rₘ Sₙ]
  [IsScalarTower R S Sₙ] [IsScalarTower R Rₘ' Sₙ'] [IsScalarTower R S Sₙ']

/--
theorem `algEquiv_comp_algebraMap` / 定理 `algEquiv_comp_algebraMap`

English:
theorem algEquiv_comp_algebraMap
  statement: (algEquiv N Sₙ Sₙ' : _ ->+* Sₙ').comp (algebraMap Rₘ Sₙ) =
  proof: by
  refine IsLocalization.ringHom_ext M (RingHom.ext fun x => ?_)
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, AlgEquiv.commutes]
  rw [← IsScalarTower.algebraMap_apply]; rw [← IsScalarTower.algebraMap_apply]; rw [← AlgEquiv.restrictScalars_apply R]; rw [AlgEquiv.commutes]

中文:
定理 algEquiv_comp_algebraMap
  结论: (algEquiv N Sₙ Sₙ' : _ ->+* Sₙ').comp (algebraMap Rₘ Sₙ) =
  证明: by
  refine IsLocalization.ringHom_ext M (RingHom.ext fun x => ?_)
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, AlgEquiv.commutes]
  rw [← IsScalarTower.algebraMap_apply]; rw [← IsScalarTower.algebraMap_apply]; rw [← AlgEquiv.restrictScalars_apply R]; rw [AlgEquiv.commutes]

Depends on / 依赖: AlgEquiv, AlgEquiv.commutes, AlgEquiv.restrictScalars_apply, Function, Function.comp_apply, IsLocalization, IsLocalization.ringHom_ext, IsScalarTower, IsScalarTower.algebraMap_apply, RingHom, RingHom.coe_coe, RingHom.coe_comp, RingHom.ext, algebraMap_apply, coe_coe, coe_comp, commutes, comp_apply, restrictScalars_apply, ringHom_ext
-/
theorem algEquiv_comp_algebraMap : (algEquiv N Sₙ Sₙ' : _ ->+* Sₙ').comp (algebraMap Rₘ Sₙ) =
      (algebraMap Rₘ' Sₙ').comp (algEquiv M Rₘ Rₘ') := by
  refine IsLocalization.ringHom_ext M (RingHom.ext fun x => ?_)
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, AlgEquiv.commutes]
  rw [← IsScalarTower.algebraMap_apply]; rw [← IsScalarTower.algebraMap_apply]; rw [← AlgEquiv.restrictScalars_apply R]; rw [AlgEquiv.commutes]

variable {Rₘ} in
/--
theorem `algEquiv_comp_algebraMap_apply` / 定理 `algEquiv_comp_algebraMap_apply`

English:
theorem algEquiv_comp_algebraMap_apply
  given: (x : Rₘ)
  proof: by
  rw [algEquiv_comp_algebraMap M Rₘ Sₙ Rₘ']

中文:
定理 algEquiv_comp_algebraMap_apply
  条件: (x : Rₘ)
  证明: by
  rw [algEquiv_comp_algebraMap M Rₘ Sₙ Rₘ']

Depends on / 依赖: algEquiv_comp_algebraMap
-/
theorem algEquiv_comp_algebraMap_apply (x : Rₘ) :
    (algEquiv N Sₙ Sₙ' : _ ->+* Sₙ').comp (algebraMap Rₘ Sₙ) x =
    (algebraMap Rₘ' Sₙ').comp (algEquiv M Rₘ Rₘ') x := by
  rw [algEquiv_comp_algebraMap M Rₘ Sₙ Rₘ']


end IsLocalization

namespace Localization

open IsLocalization

/--
theorem `mk_natCast` / 定理 `mk_natCast`

English:
theorem mk_natCast
  given: (m : Nat)
  statement: (mk m 1 : Localization M) = m
  proof: by
  simpa using mk_algebraMap (R := R) (A := Nat) _

中文:
定理 mk_natCast
  条件: (m : 自然数)
  结论: (mk m 1 : Localization M) = m
  证明: by
  simpa using mk_algebraMap (R := R) (A := Nat) _

Depends on / 依赖: mk_algebraMap
-/
theorem mk_natCast (m : Nat) : (mk m 1 : Localization M) = m := by
  simpa using mk_algebraMap (R := R) (A := Nat) _

variable [IsLocalization M S]

section

variable (S) (M)

/-- The localization of `R` at `M` as a quotient type is isomorphic to any other localization. -/
@[simps!]
/--
Definition of `algEquiv` / `algEquiv` 的定义

English:
definition algEquiv
  signature: : Localization M ≃ₐ[R] S
  body: IsLocalization.algEquiv M _ _

中文:
定义 algEquiv
  签名: : Localization M ≃ₐ[R] S
  定义体: IsLocalization.algEquiv M _ _

Depends on / 依赖: IsLocalization, IsLocalization.algEquiv, algEquiv
-/
noncomputable def algEquiv : Localization M ≃ₐ[R] S :=
  IsLocalization.algEquiv M _ _

/-- The localization of a singleton is a singleton. Cannot be an instance due to metavariables. -/
@[instance_reducible]
/--
Definition of `_root_.IsLocalization.unique` / `_root_.IsLocalization.unique` 的定义

English:
definition _root_.IsLocalization.unique
  signature: (R Rₘ) [CommSemiring R] [CommSemiring Rₘ]
  body: have : Inhabited Rₘ := ⟨1⟩
  (algEquiv M Rₘ).symm.injective.unique

中文:
定义 _root_.是Localization.unique
  签名: (R Rₘ) [交换半环 R] [交换半环 Rₘ]
  定义体: have : Inhabited Rₘ := ⟨1⟩
  (algEquiv M Rₘ).symm.injective.unique

Depends on / 依赖: Inhabited, algEquiv, injective, symm.injective.unique, unique
-/
noncomputable def _root_.IsLocalization.unique (R Rₘ) [CommSemiring R] [CommSemiring Rₘ]
    (M : Submonoid R) [Subsingleton R] [Algebra R Rₘ] [IsLocalization M Rₘ] : Unique Rₘ :=
  have : Inhabited Rₘ := ⟨1⟩
  (algEquiv M Rₘ).symm.injective.unique

end

nonrec theorem algEquiv_mk' (x : R) (y : M) : algEquiv M S (mk' (Localization M) x y) = mk' S x y :=
  algEquiv_mk' _ _

nonrec theorem algEquiv_symm_mk' (x : R) (y : M) :
    (algEquiv M S).symm (mk' S x y) = mk' (Localization M) x y :=
  algEquiv_symm_mk' _ _

/--
theorem `algEquiv_mk` / 定理 `algEquiv_mk`

English:
theorem algEquiv_mk
  given: (x y)
  statement: algEquiv M S (mk x y) = mk' S x y
  proof: by rw [mk_eq_mk', algEquiv_mk']

中文:
定理 algEquiv_mk
  条件: (x y)
  结论: algEquiv M S (mk x y) = mk' S x y
  证明: by rw [mk_eq_mk', algEquiv_mk']

Depends on / 依赖: algEquiv_mk, mk_eq_mk
-/
theorem algEquiv_mk (x y) : algEquiv M S (mk x y) = mk' S x y := by rw [mk_eq_mk', algEquiv_mk']

/--
theorem `algEquiv_symm_mk` / 定理 `algEquiv_symm_mk`

English:
theorem algEquiv_symm_mk
  given: (x : R) (y : M)
  statement: (algEquiv M S).symm (mk' S x y) = mk x y
  proof: by
  rw [mk_eq_mk']; rw [algEquiv_symm_mk']

中文:
定理 algEquiv_symm_mk
  条件: (x : R) (y : M)
  结论: (algEquiv M S).symm (mk' S x y) = mk x y
  证明: by
  rw [mk_eq_mk']; rw [algEquiv_symm_mk']

Depends on / 依赖: algEquiv_symm_mk, mk_eq_mk
-/
theorem algEquiv_symm_mk (x : R) (y : M) : (algEquiv M S).symm (mk' S x y) = mk x y := by
  rw [mk_eq_mk']; rw [algEquiv_symm_mk']

/--
lemma `coe_algEquiv` / 引理 `coe_algEquiv`

English:
lemma coe_algEquiv
  proof: rfl

中文:
引理 coe_algEquiv
  证明: rfl

Depends on / 依赖: RingHom, RingHom.id, le_rfl
-/
lemma coe_algEquiv :
    (Localization.algEquiv M S : Localization M ->+* S) =
    IsLocalization.map (M := M) (T := M) _ (RingHom.id R) le_rfl := rfl

/--
lemma `coe_algEquiv_symm` / 引理 `coe_algEquiv_symm`

English:
lemma coe_algEquiv_symm
  proof: rfl

中文:
引理 coe_algEquiv_symm
  证明: rfl

Depends on / 依赖: RingHom, RingHom.id, le_rfl
-/
lemma coe_algEquiv_symm :
    ((Localization.algEquiv M S).symm : S ->+* Localization M) =
    IsLocalization.map (M := M) (T := M) _ (RingHom.id R) le_rfl := rfl

end Localization

open IsLocalization

/--
theorem `IsField.localization_map_bijective` / 定理 `IsField.localization_map_bijective`

English:
theorem IsField.localization_map_bijective
  statement: {R Rₘ : Type*} [CommRing R] [CommRing Rₘ]
  proof: by
  let := hR.toField
  replace hM := le_nonZeroDivisors_of_noZeroDivisors hM
  refine ⟨IsLocalization.injective _ hM, fun x => ?_⟩
  obtain ⟨r, ⟨m, hm⟩, rfl⟩ := exists_mk'_eq M x
  obtain ⟨n, hn⟩ := hR.mul_inv_cancel (nonZeroDivisors.ne_zero <| hM hm)
  exact ⟨r * n, by rw [eq_mk'_iff_mul_eq, ← map_mul, mul_assoc, _root_.mul_comm n, hn, mul_one]⟩

中文:
定理 是域.localization_map_bijective
  结论: {R Rₘ : 类型} [交换环 R] [交换环 Rₘ]
  证明: by
  let := hR.toField
  replace hM := le_nonZeroDivisors_of_noZeroDivisors hM
  refine ⟨IsLocalization.injective _ hM, fun x => ?_⟩
  obtain ⟨r, ⟨m, hm⟩, rfl⟩ := exists_mk'_eq M x
  obtain ⟨n, hn⟩ := hR.mul_inv_cancel (nonZeroDivisors.ne_zero <| hM hm)
  exact ⟨r * n, by rw [eq_mk'_iff_mul_eq, ← map_mul, mul_assoc, _root_.mul_comm n, hn, mul_one]⟩

Depends on / 依赖: IsLocalization, IsLocalization.injective, _iff_mul_eq, _root_, _root_.mul_comm, eq_mk, exists_mk, hR.mul_inv_cancel, hR.toField, injective, le_nonZeroDivisors_of_noZeroDivisors, map_mul, mul_assoc, mul_comm, mul_inv_cancel, mul_one, ne_zero, nonZeroDivisors, nonZeroDivisors.ne_zero, replace
-/
theorem IsField.localization_map_bijective {R Rₘ : Type*} [CommRing R] [CommRing Rₘ]
    {M : Submonoid R} (hM : (0 : R) ∉ M) (hR : IsField R) [Algebra R Rₘ] [IsLocalization M Rₘ] :
    Function.Bijective (algebraMap R Rₘ) := by
  let := hR.toField
  replace hM := le_nonZeroDivisors_of_noZeroDivisors hM
  refine ⟨IsLocalization.injective _ hM, fun x => ?_⟩
  obtain ⟨r, ⟨m, hm⟩, rfl⟩ := exists_mk'_eq M x
  obtain ⟨n, hn⟩ := hR.mul_inv_cancel (nonZeroDivisors.ne_zero <| hM hm)
  exact ⟨r * n, by rw [eq_mk'_iff_mul_eq, ← map_mul, mul_assoc, _root_.mul_comm n, hn, mul_one]⟩

/--
theorem `Field.localization_map_bijective` / 定理 `Field.localization_map_bijective`

English:
theorem Field.localization_map_bijective
  statement: {K Kₘ : Type*} [Field K] [CommRing Kₘ] {M : Submonoid K}
  proof: (Field.toIsField K).localization_map_bijective hM

中文:
定理 域.localization_map_bijective
  结论: {K Kₘ : 类型} [域 K] [交换环 Kₘ] {M : 子幺半群 K}
  证明: (Field.toIsField K).localization_map_bijective hM

Depends on / 依赖: Field.toIsField, localization_map_bijective, toIsField
-/
theorem Field.localization_map_bijective {K Kₘ : Type*} [Field K] [CommRing Kₘ] {M : Submonoid K}
    (hM : (0 : K) ∉ M) [Algebra K Kₘ] [IsLocalization M Kₘ] :
    Function.Bijective (algebraMap K Kₘ) :=
  (Field.toIsField K).localization_map_bijective hM

-- this looks weird due to the `letI` inside the above lemma, but trying to do it the other
-- way round causes issues with defeq of instances, so this is actually easier.
section Algebra

variable {Rₘ Sₘ : Type*} [CommSemiring Rₘ] [CommSemiring Sₘ]
variable [Algebra R Rₘ] [IsLocalization M Rₘ]
variable [Algebra S Sₘ] [i : IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]
include S
section

variable (S M)

/-- Definition of the natural algebra induced by the localization of an algebra.
Given an algebra `R → S`, a submonoid `R` of `M`, and a localization `Rₘ` for `M`,
let `Sₘ` be the localization of `S` to the image of `M` under `algebraMap R S`.
Then this is the natural algebra structure on `Rₘ → Sₘ`, such that the entire square commutes,
where `localization_map.map_comp` gives the commutativity of the underlying maps.

This instance can be helpful if you define `Sₘ := Localization (Algebra.algebraMapSubmonoid S M)`,
however we will instead use the hypotheses `[Algebra Rₘ Sₘ] [IsScalarTower R Rₘ Sₘ]` in lemmas
since the algebra structure may arise in different ways.
-/
@[instance_reducible]
/--
Definition of `localizationAlgebra` / `localizationAlgebra` 的定义

English:
definition localizationAlgebra
  signature: : Algebra Rₘ Sₘ
  body: (map Sₘ (algebraMap R S)
        (show _ <= (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :
      Rₘ ->+* Sₘ).toAlgebra

中文:
定义 localizationAlgebra
  签名: : 代数 Rₘ Sₘ
  定义体: (map Sₘ (algebraMap R S)
        (show _ <= (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :
      Rₘ ->+* Sₘ).toAlgebra

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid, M.le_comap_map, algebraMap, algebraMapSubmonoid, le_comap_map, toAlgebra
-/
noncomputable def localizationAlgebra : Algebra Rₘ Sₘ :=
  (map Sₘ (algebraMap R S)
        (show _ <= (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :
      Rₘ ->+* Sₘ).toAlgebra

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra (Localization M)
  body: localizationAlgebra M S

中文:
实例 :
  签名: 代数 (Localization M)
  定义体: localizationAlgebra M S

Depends on / 依赖: localizationAlgebra
-/
noncomputable instance : Algebra (Localization M)
    (Localization (Algebra.algebraMapSubmonoid S M)) := localizationAlgebra M S

-- This is not an instance, because the discrimination tree key is `IsScalarTower _ _ _ _ _ _`, so
-- it would cause significant slowdowns.
/--
lemma `isScalarTower_localizationAlgebra` / 引理 `isScalarTower_localizationAlgebra`

English:
lemma isScalarTower_localizationAlgebra
  given: [Algebra R Sₘ] [IsScalarTower R S Sₘ]
  proof: localizationAlgebra M S
    IsScalarTower R Rₘ Sₘ :=
  letI : Algebra Rₘ Sₘ := localizationAlgebra M S
.of_algebraMap_eq' by
    simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_eq R S Sₘ]

中文:
引理 isScalarTower_localizationAlgebra
  条件: [代数 R Sₘ] [标量塔 R S Sₘ]
  证明: localizationAlgebra M S
    IsScalarTower R Rₘ Sₘ :=
  letI : Algebra Rₘ Sₘ := localizationAlgebra M S
.of_algebraMap_eq' by
    simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_eq R S Sₘ]

Depends on / 依赖: localizationAlgebra
-/
lemma isScalarTower_localizationAlgebra [Algebra R Sₘ] [IsScalarTower R S Sₘ] :
    letI : Algebra Rₘ Sₘ := localizationAlgebra M S
    IsScalarTower R Rₘ Sₘ :=
  letI : Algebra Rₘ Sₘ := localizationAlgebra M S
.of_algebraMap_eq' by
    simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_eq R S Sₘ]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower R (Localization M) (Localization (Algebra.algebraMapSubmonoid S M))
  body: isScalarTower_localizationAlgebra _ _

中文:
实例 :
  签名: 标量塔 R (Localization M) (Localization (代数.algebraMapSubmonoid S M))
  定义体: isScalarTower_localizationAlgebra _ _
-/
instance : IsScalarTower R (Localization M) (Localization (Algebra.algebraMapSubmonoid S M)) :=
  isScalarTower_localizationAlgebra _ _

end

section

variable [Algebra Rₘ Sₘ] [Algebra R Sₘ] [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
variable (S Rₘ Sₘ)

/--
theorem `IsLocalization.map_units_map_submonoid` / 定理 `IsLocalization.map_units_map_submonoid`

English:
theorem IsLocalization.map_units_map_submonoid
  given: (y : M)
  statement: IsUnit (algebraMap R Sₘ y)
  proof: by
  rw [IsScalarTower.algebraMap_apply _ S]
  exact IsLocalization.map_units Sₘ ⟨algebraMap R S y, Algebra.mem_algebraMapSubmonoid_of_mem y⟩

中文:
定理 是Localization.map_units_map_submonoid
  条件: (y : M)
  结论: 是单位 (algebraMap R Sₘ y)
  证明: by
  rw [IsScalarTower.algebraMap_apply _ S]
  exact IsLocalization.map_units Sₘ ⟨algebraMap R S y, Algebra.mem_algebraMapSubmonoid_of_mem y⟩

Depends on / 依赖: Algebra, Algebra.mem_algebraMapSubmonoid_of_mem, IsLocalization, IsLocalization.map_units, IsScalarTower, IsScalarTower.algebraMap_apply, algebraMap, algebraMap_apply, map_units, mem_algebraMapSubmonoid_of_mem
-/
theorem IsLocalization.map_units_map_submonoid (y : M) : IsUnit (algebraMap R Sₘ y) := by
  rw [IsScalarTower.algebraMap_apply _ S]
  exact IsLocalization.map_units Sₘ ⟨algebraMap R S y, Algebra.mem_algebraMapSubmonoid_of_mem y⟩

-- can't be simp, as `S` only appears on the RHS
/--
theorem `IsLocalization.algebraMap_mk'` / 定理 `IsLocalization.algebraMap_mk'`

English:
theorem IsLocalization.algebraMap_mk'
  given: (x : R) (y : M)
  proof: by
  rw [IsLocalization.eq_mk'_iff_mul_eq]; rw [Subtype.coe_mk]; rw [← IsScalarTower.algebraMap_apply]; rw [←
    IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply R Rₘ Sₘ]; rw [IsScalarTower.algebraMap_apply R Rₘ Sₘ]; rw [← map_mul]; rw [mul_comm]; rw [IsLocalization.mul_mk'_eq_mk'_of_mul]
  exact congr_arg (algebraMap Rₘ Sₘ) (IsLocalization.mk'_mul_cancel_left x y)

中文:
定理 是Localization.algebraMap_mk'
  条件: (x : R) (y : M)
  证明: by
  rw [IsLocalization.eq_mk'_iff_mul_eq]; rw [Subtype.coe_mk]; rw [← IsScalarTower.algebraMap_apply]; rw [←
    IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply R Rₘ Sₘ]; rw [IsScalarTower.algebraMap_apply R Rₘ Sₘ]; rw [← map_mul]; rw [mul_comm]; rw [IsLocalization.mul_mk'_eq_mk'_of_mul]
  exact congr_arg (algebraMap Rₘ Sₘ) (IsLocalization.mk'_mul_cancel_left x y)

Depends on / 依赖: IsLocalization, IsLocalization.eq_mk, IsLocalization.mk, IsLocalization.mul_mk, IsScalarTower, IsScalarTower.algebraMap_apply, Subtype, Subtype.coe_mk, _eq_mk, _iff_mul_eq, _mul_cancel_left, _of_mul, algebraMap, algebraMap_apply, coe_mk, congr_arg, eq_mk, map_mul, mul_comm, mul_mk
-/
theorem IsLocalization.algebraMap_mk' (x : R) (y : M) :
    algebraMap Rₘ Sₘ (IsLocalization.mk' Rₘ x y) =
      IsLocalization.mk' Sₘ (algebraMap R S x)
        ⟨algebraMap R S y, Algebra.mem_algebraMapSubmonoid_of_mem y⟩ := by
  rw [IsLocalization.eq_mk'_iff_mul_eq]; rw [Subtype.coe_mk]; rw [← IsScalarTower.algebraMap_apply]; rw [←
    IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply R Rₘ Sₘ]; rw [IsScalarTower.algebraMap_apply R Rₘ Sₘ]; rw [← map_mul]; rw [mul_comm]; rw [IsLocalization.mul_mk'_eq_mk'_of_mul]
  exact congr_arg (algebraMap Rₘ Sₘ) (IsLocalization.mk'_mul_cancel_left x y)

variable (M)

/--
theorem `IsLocalization.algebraMap_eq_map_map_submonoid` / 定理 `IsLocalization.algebraMap_eq_map_map_submonoid`

English:
theorem IsLocalization.algebraMap_eq_map_map_submonoid
  proof: Eq.symm
    IsLocalization.map_unique _ (algebraMap Rₘ Sₘ) fun x => by
      rw [← IsScalarTower.algebraMap_apply R S Sₘ]; rw [← IsScalarTower.algebraMap_apply R Rₘ Sₘ]

中文:
定理 是Localization.algebraMap_eq_map_map_submonoid
  证明: Eq.symm
    IsLocalization.map_unique _ (algebraMap Rₘ Sₘ) fun x => by
      rw [← IsScalarTower.algebraMap_apply R S Sₘ]; rw [← IsScalarTower.algebraMap_apply R Rₘ Sₘ]

Depends on / 依赖: Eq.symm, IsLocalization, IsLocalization.map_unique, IsScalarTower, IsScalarTower.algebraMap_apply, algebraMap, algebraMap_apply, map_unique
-/
theorem IsLocalization.algebraMap_eq_map_map_submonoid :
    algebraMap Rₘ Sₘ =
      map Sₘ (algebraMap R S)
        (show _ <= (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :=
Eq.symm
    IsLocalization.map_unique _ (algebraMap Rₘ Sₘ) fun x => by
      rw [← IsScalarTower.algebraMap_apply R S Sₘ]; rw [← IsScalarTower.algebraMap_apply R Rₘ Sₘ]

/--
theorem `IsLocalization.algebraMap_apply_eq_map_map_submonoid` / 定理 `IsLocalization.algebraMap_apply_eq_map_map_submonoid`

English:
theorem IsLocalization.algebraMap_apply_eq_map_map_submonoid
  given: (x)
  proof: DFunLike.congr_fun (IsLocalization.algebraMap_eq_map_map_submonoid _ _ _ _) x

中文:
定理 是Localization.algebraMap_apply_eq_map_map_submonoid
  条件: (x)
  证明: DFunLike.congr_fun (IsLocalization.algebraMap_eq_map_map_submonoid _ _ _ _) x

Depends on / 依赖: DFunLike, DFunLike.congr_fun, IsLocalization, IsLocalization.algebraMap_eq_map_map_submonoid, algebraMap_eq_map_map_submonoid, congr_fun
-/
theorem IsLocalization.algebraMap_apply_eq_map_map_submonoid (x) :
    algebraMap Rₘ Sₘ x =
      map Sₘ (algebraMap R S)
        (show _ <= (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) x :=
  DFunLike.congr_fun (IsLocalization.algebraMap_eq_map_map_submonoid _ _ _ _) x

/--
theorem `IsLocalization.lift_algebraMap_eq_algebraMap` / 定理 `IsLocalization.lift_algebraMap_eq_algebraMap`

English:
theorem IsLocalization.lift_algebraMap_eq_algebraMap
  proof: IsLocalization.lift_unique _ fun _ => (IsScalarTower.algebraMap_apply _ _ _ _).symm

中文:
定理 是Localization.lift_algebraMap_eq_algebraMap
  证明: IsLocalization.lift_unique _ fun _ => (IsScalarTower.algebraMap_apply _ _ _ _).symm

Depends on / 依赖: IsLocalization, IsLocalization.map_units_map_submonoid, map_units_map_submonoid
-/
theorem IsLocalization.lift_algebraMap_eq_algebraMap :
    IsLocalization.lift (M := M) (IsLocalization.map_units_map_submonoid S Sₘ) =
      algebraMap Rₘ Sₘ :=
  IsLocalization.lift_unique _ fun _ => (IsScalarTower.algebraMap_apply _ _ _ _).symm

end

variable (Rₘ Sₘ)

/--
theorem `localizationAlgebraMap_def` / 定理 `localizationAlgebraMap_def`

English:
theorem localizationAlgebraMap_def
  proof: rfl

中文:
定理 localizationAlgebraMap_def
  证明: rfl
-/
theorem localizationAlgebraMap_def :
    @algebraMap Rₘ Sₘ _ _ (localizationAlgebra M S) =
      map Sₘ (algebraMap R S)
        (show _ <= (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :=
  rfl

/--
theorem `localizationAlgebra_injective` / 定理 `localizationAlgebra_injective`

English:
theorem localizationAlgebra_injective
  given: (hRS : Function.Injective (algebraMap R S))
  proof: have : IsLocalization (M.map (algebraMap R S)) Sₘ := i
  IsLocalization.map_injective_of_injective _ _ _ hRS

中文:
定理 localizationAlgebra_injective
  条件: (hRS : 函数.单射 (algebraMap R S))
  证明: have : IsLocalization (M.map (algebraMap R S)) Sₘ := i
  IsLocalization.map_injective_of_injective _ _ _ hRS

Depends on / 依赖: IsLocalization, IsLocalization.map_injective_of_injective, M.map, algebraMap, map_injective_of_injective
-/
theorem localizationAlgebra_injective (hRS : Function.Injective (algebraMap R S)) :
    Function.Injective (@algebraMap Rₘ Sₘ _ _ (localizationAlgebra M S)) :=
  have : IsLocalization (M.map (algebraMap R S)) Sₘ := i
  IsLocalization.map_injective_of_injective _ _ _ hRS

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocalization (Algebra.algebraMapSubmonoid R M) Rₘ
  body: by
  simpa

中文:
实例 :
  签名: 是Localization (代数.algebraMapSubmonoid R M) Rₘ
  定义体: by
  simpa
-/
instance : IsLocalization (Algebra.algebraMapSubmonoid R M) Rₘ := by
  simpa

end Algebra

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] {M : Submonoid R} (S : Type*) [CommRing S]

namespace IsLocalization

variable (M) in
/--
theorem `map_injective_of_injective'` / 定理 `map_injective_of_injective'`

English:
theorem map_injective_of_injective'
  statement: {f : R ->+* S} {Rₘ : Type*} [CommRing Rₘ] [Algebra R Rₘ]
  proof: by
  refine (injective_iff_map_eq_zero (map Sₘ f hf)).mpr fun x h => ?_
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
  aesop (add simp [map_mk', mk'_eq_zero_iff])

中文:
定理 map_injective_of_injective'
  结论: {f : R ->+* S} {Rₘ : 类型} [交换环 Rₘ] [代数 R Rₘ]
  证明: by
  refine (injective_iff_map_eq_zero (map Sₘ f hf)).mpr fun x h => ?_
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
  aesop (add simp [map_mk', mk'_eq_zero_iff])

Depends on / 依赖: IsLocalization, IsLocalization.exists_mk, _eq_zero_iff, exists_mk, injective_iff_map_eq_zero, map_mk
-/
theorem map_injective_of_injective' {f : R ->+* S} {Rₘ : Type*} [CommRing Rₘ] [Algebra R Rₘ]
    [IsLocalization M Rₘ] (Sₘ : Type*) {N : Submonoid S} [CommRing Sₘ] [Algebra S Sₘ]
    [IsLocalization N Sₘ] (hf : M <= Submonoid.comap f N) (hN : 0 ∉ N) [IsDomain S]
    (hf' : Function.Injective f) :
    Function.Injective (map Sₘ f hf : Rₘ ->+* Sₘ) := by
  refine (injective_iff_map_eq_zero (map Sₘ f hf)).mpr fun x h => ?_
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
  aesop (add simp [map_mk', mk'_eq_zero_iff])

end IsLocalization

/--
theorem `Localization.mk_intCast` / 定理 `Localization.mk_intCast`

English:
theorem Localization.mk_intCast
  given: (m : Int)
  statement: (mk m 1 : Localization M) = m
  proof: by
  simpa using mk_algebraMap (R := R) (A := Int) _

中文:
定理 Localization.mk_intCast
  条件: (m : 整数)
  结论: (mk m 1 : Localization M) = m
  证明: by
  simpa using mk_algebraMap (R := R) (A := Int) _

Depends on / 依赖: mk_algebraMap
-/
theorem Localization.mk_intCast (m : Int) : (mk m 1 : Localization M) = m := by
  simpa using mk_algebraMap (R := R) (A := Int) _

/--
theorem `Localization.r_iff_of_le_nonZeroDivisors` / 定理 `Localization.r_iff_of_le_nonZeroDivisors`

English:
theorem Localization.r_iff_of_le_nonZeroDivisors
  given: (hM : M <= nonZeroDivisors R) (a c : R) (b d : M)
  proof: by
  simp only [Localization.r_eq_r', Localization.r', Subtype.exists, exists_prop, Con.rel_mk]
  refine ⟨fun ⟨u, hu, h⟩ => ?_,
    fun h => ⟨1, Submonoid.one_mem M, by simpa only [one_mul, mul_comm a] using h⟩⟩
  have hu' : u in nonZeroDivisors R := hM hu
  simp only [mem_nonZeroDivisors_iff, mul_comm, and_self] at hu'
  rw [← sub_eq_zero]
  apply hu'
  rwa [mul_sub, sub_eq_zero, mul_comm a]

中文:
定理 Localization.r_iff_of_le_nonZeroDivisors
  条件: (hM : M <= nonZeroDivisors R) (a c : R) (b d : M)
  证明: by
  simp only [Localization.r_eq_r', Localization.r', Subtype.exists, exists_prop, Con.rel_mk]
  refine ⟨fun ⟨u, hu, h⟩ => ?_,
    fun h => ⟨1, Submonoid.one_mem M, by simpa only [one_mul, mul_comm a] using h⟩⟩
  have hu' : u in nonZeroDivisors R := hM hu
  simp only [mem_nonZeroDivisors_iff, mul_comm, and_self] at hu'
  rw [← sub_eq_zero]
  apply hu'
  rwa [mul_sub, sub_eq_zero, mul_comm a]

Depends on / 依赖: Con.rel_mk, Localization, Localization.r, Localization.r_eq_r, Submonoid, Submonoid.one_mem, Subtype, Subtype.exists, and_self, exists_prop, mem_nonZeroDivisors_iff, mul_comm, mul_sub, nonZeroDivisors, one_mem, one_mul, r_eq_r, rel_mk, sub_eq_zero
-/
theorem Localization.r_iff_of_le_nonZeroDivisors (hM : M <= nonZeroDivisors R) (a c : R) (b d : M) :
    Localization.r _ (a, b) (c, d) ↔ a * d = b * c := by
  simp only [Localization.r_eq_r', Localization.r', Subtype.exists, exists_prop, Con.rel_mk]
  refine ⟨fun ⟨u, hu, h⟩ => ?_,
    fun h => ⟨1, Submonoid.one_mem M, by simpa only [one_mul, mul_comm a] using h⟩⟩
  have hu' : u in nonZeroDivisors R := hM hu
  simp only [mem_nonZeroDivisors_iff, mul_comm, and_self] at hu'
  rw [← sub_eq_zero]
  apply hu'
  rwa [mul_sub, sub_eq_zero, mul_comm a]

end CommRing

section Algebra

-- This is not tagged with `@[ext]` because `A` and `W` cannot be inferred.
/--
theorem `IsLocalization.algHom_ext` / 定理 `IsLocalization.algHom_ext`

English:
theorem IsLocalization.algHom_ext
  statement: {R A L B : Type*}
  proof: AlgHom.coe_ringHom_injective IsLocalization.ringHom_ext W RingHom.ext AlgHom.ext_iff.mp h

中文:
定理 是Localization.algHom_ext
  结论: {R A L B : 类型}
  证明: AlgHom.coe_ringHom_injective IsLocalization.ringHom_ext W RingHom.ext AlgHom.ext_iff.mp h

Depends on / 依赖: AlgHom, AlgHom.coe_ringHom_injective, AlgHom.ext_iff.mp, IsLocalization, IsLocalization.ringHom_ext, RingHom, RingHom.ext, coe_ringHom_injective, ext_iff, ringHom_ext
-/
theorem IsLocalization.algHom_ext {R A L B : Type*}
    [CommSemiring R] [CommSemiring A] [CommSemiring L] [Semiring B]
    (W : Submonoid A) [Algebra A L] [IsLocalization W L]
    [Algebra R A] [Algebra R L] [IsScalarTower R A L] [Algebra R B]
    {f g : L ->ₐ[R] B} (h : f.comp (Algebra.algHom R A L) = g.comp (Algebra.algHom R A L)) :
    f = g :=
AlgHom.coe_ringHom_injective IsLocalization.ringHom_ext W RingHom.ext AlgHom.ext_iff.mp h

-- This is a more specific case where the domain is `Localization W`, so this is tagged
-- `@[ext high]` so that it will be automatically applied before the default extensionality lemmas
-- which compare every element.
/--
theorem `Localization.algHom_ext` / 定理 `Localization.algHom_ext`

English:
theorem Localization.algHom_ext
  statement: {R A B : Type*}
  proof: IsLocalization.algHom_ext W h

中文:
定理 Localization.algHom_ext
  结论: {R A B : 类型}
  证明: IsLocalization.algHom_ext W h
-/
@[ext high] theorem Localization.algHom_ext {R A B : Type*}
    [CommSemiring R] [CommSemiring A] [Semiring B] [Algebra R A] [Algebra R B] (W : Submonoid A)
    {f g : Localization W ->ₐ[R] B}
    (h : f.comp (Algebra.algHom R A _) = g.comp (Algebra.algHom R A _)) :
    f = g :=
  IsLocalization.algHom_ext W h

section extend

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  (S : Type*) [CommSemiring S] [Algebra R S] (M : Submonoid R) [IsLocalization M S]
  [Algebra R A] [Algebra S A] [IsScalarTower R S A]
  [Algebra R B] [Algebra S B] [IsScalarTower R S B]

/--
Definition of `AlgHom.extendScalarsOfIsLocalization` / `AlgHom.extendScalarsOfIsLocalization` 的定义

English:
definition AlgHom.extendScalarsOfIsLocalization
  signature: (f : A ->ₐ[R] B)
  body: f
  commutes' := by
    let f := f.comp (IsScalarTower.toAlgHom R S A)
    let g := IsScalarTower.toAlgHom R S B
    have : f.toRingHom.comp (algebraMap R S) = g.toRingHom.comp (algebraMap R S) := by simp
    suffices f = g by rwa [DFunLike.ext_iff] at this
    apply IsLocalization.algHom_ext M
    rwa [DFunLike.ext_iff] at this ⊢

@[simp]

中文:
定义 代数态射.extendScalarsOfIsLocalization
  签名: (f : A ->ₐ[R] B)
  定义体: f
  commutes' := by
    let f := f.comp (IsScalarTower.toAlgHom R S A)
    let g := IsScalarTower.toAlgHom R S B
    have : f.toRingHom.comp (algebraMap R S) = g.toRingHom.comp (algebraMap R S) := by simp
    suffices f = g by rwa [DFunLike.ext_iff] at this
    apply IsLocalization.algHom_ext M
    rwa [DFunLike.ext_iff] at this ⊢

@[simp]
-/
def AlgHom.extendScalarsOfIsLocalization (f : A ->ₐ[R] B) : A ->ₐ[S] B where
  __ := f
  commutes' := by
    let f := f.comp (IsScalarTower.toAlgHom R S A)
    let g := IsScalarTower.toAlgHom R S B
    have : f.toRingHom.comp (algebraMap R S) = g.toRingHom.comp (algebraMap R S) := by simp
    suffices f = g by rwa [DFunLike.ext_iff] at this
    apply IsLocalization.algHom_ext M
    rwa [DFunLike.ext_iff] at this ⊢

@[simp]
/--
theorem `AlgHom.extendScalarsOfIsLocalization_apply` / 定理 `AlgHom.extendScalarsOfIsLocalization_apply`

English:
theorem AlgHom.extendScalarsOfIsLocalization_apply
  given: (f : A ->ₐ[R] B) (a : A)
  proof: rfl

中文:
定理 代数态射.extendScalarsOfIsLocalization_apply
  条件: (f : A ->ₐ[R] B) (a : A)
  证明: rfl
-/
theorem AlgHom.extendScalarsOfIsLocalization_apply (f : A ->ₐ[R] B) (a : A) :
    f.extendScalarsOfIsLocalization S M a = f a :=
  rfl

/-- For an algebra isomorphism `f : A ≃ₐ[R] B`, if `A` and `B` are algebras over a localization
`S` of `R`, then `f` is automatically an `S`-algebra isomorphism. -/
@[simps]
/--
Definition of `AlgEquiv.extendScalarsOfIsLocalization` / `AlgEquiv.extendScalarsOfIsLocalization` 的定义

English:
definition AlgEquiv.extendScalarsOfIsLocalization
  signature: (f : A ≃ₐ[R] B)
  body: f.toAlgHom.extendScalarsOfIsLocalization S M
  __ := f

中文:
定义 代数等价.extendScalarsOfIsLocalization
  签名: (f : A ≃ₐ[R] B)
  定义体: f.toAlgHom.extendScalarsOfIsLocalization S M
  __ := f

Depends on / 依赖: extendScalarsOfIsLocalization, f.toAlgHom.extendScalarsOfIsLocalization, toAlgHom
-/
def AlgEquiv.extendScalarsOfIsLocalization (f : A ≃ₐ[R] B) : A ≃ₐ[S] B where
  __ := f.toAlgHom.extendScalarsOfIsLocalization S M
  __ := f

end extend

end Algebra
