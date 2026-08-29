/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
module

public import Mathlib.GroupTheory.Submonoid.Inverses
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Defs

/-!
# Submonoid of inverses

## Main definitions

* `IsLocalization.invSubmonoid M S` is the submonoid of `S = M⁻¹R` consisting of inverses of
  each element `x ∈ M`

## Implementation notes

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

@[expose] public section


variable {R : Type*} [CommRing R] (M : Submonoid R) (S : Type*) [CommRing S]
variable [Algebra R S]

open Function

namespace IsLocalization

section InvSubmonoid

/--
Definition of `invSubmonoid` / `invSubmonoid` 的定义

English:
definition invSubmonoid
  signature: : Submonoid S
  body: (M.map (algebraMap R S)).leftInv

中文:
定义 invSubmonoid
  签名: : Submonoid S
  定义体: (M.map (algebraMap R S)).leftInv

Depends on / 依赖: M.map, algebraMap, leftInv
-/
def invSubmonoid : Submonoid S :=
  (M.map (algebraMap R S)).leftInv

variable [IsLocalization M S]

/--
theorem `submonoid_map_le_is_unit` / 定理 `submonoid_map_le_is_unit`

English:
theorem submonoid_map_le_is_unit
  statement: M.map (algebraMap R S) <= IsUnit.submonoid S
  proof: by
  rintro _ ⟨a, ha, rfl⟩
  exact IsLocalization.map_units S ⟨_, ha⟩

中文:
定理 submonoid_map_le_is_unit
  结论: M.map (algebraMap R S) <= IsUnit.submonoid S
  证明: by
  rintro _ ⟨a, ha, rfl⟩
  exact IsLocalization.map_units S ⟨_, ha⟩

Depends on / 依赖: IsLocalization, IsLocalization.map_units, IsTopologicalRing, continuousSMul, map_units
-/
theorem submonoid_map_le_is_unit : M.map (algebraMap R S) <= IsUnit.submonoid S := by
  rintro _ ⟨a, ha, rfl⟩
  exact IsLocalization.map_units S ⟨_, ha⟩

/--
Definition of `equivInvSubmonoid` / `equivInvSubmonoid` 的定义

English:
abbreviation equivInvSubmonoid
  signature: : M.map (algebraMap R S) ≃* invSubmonoid M S
  body: ((M.map (algebraMap R S)).leftInvEquiv (submonoid_map_le_is_unit M S)).symm

中文:
缩写 equivInvSubmonoid
  签名: : M.map (algebraMap R S) ≃* invSubmonoid M S
  定义体: ((M.map (algebraMap R S)).leftInvEquiv (submonoid_map_le_is_unit M S)).symm

Depends on / 依赖: M.map, algebraMap, leftInvEquiv, submonoid_map_le_is_unit
-/
noncomputable abbrev equivInvSubmonoid : M.map (algebraMap R S) ≃* invSubmonoid M S :=
  ((M.map (algebraMap R S)).leftInvEquiv (submonoid_map_le_is_unit M S)).symm

/--
Definition of `toInvSubmonoid` / `toInvSubmonoid` 的定义

English:
definition toInvSubmonoid
  signature: : M ->* invSubmonoid M S
  body: (equivInvSubmonoid M S).toMonoidHom.comp ((algebraMap R S : R ->* S).submonoidMap M)

中文:
定义 toInvSubmonoid
  签名: : M ->* invSubmonoid M S
  定义体: (equivInvSubmonoid M S).toMonoidHom.comp ((algebraMap R S : R ->* S).submonoidMap M)

Depends on / 依赖: algebraMap, equivInvSubmonoid, submonoidMap, toMonoidHom, toMonoidHom.comp
-/
noncomputable def toInvSubmonoid : M ->* invSubmonoid M S :=
  (equivInvSubmonoid M S).toMonoidHom.comp ((algebraMap R S : R ->* S).submonoidMap M)

/--
theorem `toInvSubmonoid_surjective` / 定理 `toInvSubmonoid_surjective`

English:
theorem toInvSubmonoid_surjective
  statement: Function.Surjective (toInvSubmonoid M S)
  proof: Function.Surjective.comp (β := M.map (algebraMap R S))
    (Equiv.surjective (equivInvSubmonoid _ _).toEquiv) (MonoidHom.submonoidMap_surjective _ _)

@[simp]

中文:
定理 toInvSubmonoid_surjective
  结论: Function.Surjective (toInvSubmonoid M S)
  证明: Function.Surjective.comp (β := M.map (algebraMap R S))
    (Equiv.surjective (equivInvSubmonoid _ _).toEquiv) (MonoidHom.submonoidMap_surjective _ _)

@[simp]

Depends on / 依赖: Equiv.surjective, Function, Function.Surjective.comp, M.map, MonoidHom, MonoidHom.submonoidMap_surjective, Surjective, algebraMap, equivInvSubmonoid, submonoidMap_surjective, surjective, toEquiv
-/
theorem toInvSubmonoid_surjective : Function.Surjective (toInvSubmonoid M S) :=
  Function.Surjective.comp (β := M.map (algebraMap R S))
    (Equiv.surjective (equivInvSubmonoid _ _).toEquiv) (MonoidHom.submonoidMap_surjective _ _)

@[simp]
/--
theorem `toInvSubmonoid_mul` / 定理 `toInvSubmonoid_mul`

English:
theorem toInvSubmonoid_mul
  given: (m : M)
  statement: (toInvSubmonoid M S m : S) * algebraMap R S m = 1
  proof: Submonoid.leftInvEquiv_symm_mul _ (submonoid_map_le_is_unit _ _) _

@[simp]

中文:
定理 toInvSubmonoid_mul
  条件: (m : M)
  结论: (toInvSubmonoid M S m : S) * algebraMap R S m = 1
  证明: Submonoid.leftInvEquiv_symm_mul _ (submonoid_map_le_is_unit _ _) _

@[simp]

Depends on / 依赖: Submonoid, Submonoid.leftInvEquiv_symm_mul, leftInvEquiv_symm_mul, submonoid_map_le_is_unit
-/
theorem toInvSubmonoid_mul (m : M) : (toInvSubmonoid M S m : S) * algebraMap R S m = 1 :=
  Submonoid.leftInvEquiv_symm_mul _ (submonoid_map_le_is_unit _ _) _

@[simp]
/--
theorem `mul_toInvSubmonoid` / 定理 `mul_toInvSubmonoid`

English:
theorem mul_toInvSubmonoid
  given: (m : M)
  statement: algebraMap R S m * (toInvSubmonoid M S m : S) = 1
  proof: Submonoid.mul_leftInvEquiv_symm _ (submonoid_map_le_is_unit _ _) ⟨_, _⟩

@[simp]

中文:
定理 mul_toInvSubmonoid
  条件: (m : M)
  结论: algebraMap R S m * (toInvSubmonoid M S m : S) = 1
  证明: Submonoid.mul_leftInvEquiv_symm _ (submonoid_map_le_is_unit _ _) ⟨_, _⟩

@[simp]

Depends on / 依赖: Submonoid, Submonoid.mul_leftInvEquiv_symm, mul_leftInvEquiv_symm, submonoid_map_le_is_unit
-/
theorem mul_toInvSubmonoid (m : M) : algebraMap R S m * (toInvSubmonoid M S m : S) = 1 :=
  Submonoid.mul_leftInvEquiv_symm _ (submonoid_map_le_is_unit _ _) ⟨_, _⟩

@[simp]
/--
theorem `smul_toInvSubmonoid` / 定理 `smul_toInvSubmonoid`

English:
theorem smul_toInvSubmonoid
  given: (m : M)
  statement: m • (toInvSubmonoid M S m : S) = 1
  proof: by
  convert! mul_toInvSubmonoid M S m
  ext
  rw [← Algebra.smul_def]
  rfl

中文:
定理 smul_toInvSubmonoid
  条件: (m : M)
  结论: m • (toInvSubmonoid M S m : S) = 1
  证明: by
  convert! mul_toInvSubmonoid M S m
  ext
  rw [← Algebra.smul_def]
  rfl

Depends on / 依赖: Algebra, Algebra.smul_def, convert, mul_toInvSubmonoid, smul_def
-/
theorem smul_toInvSubmonoid (m : M) : m • (toInvSubmonoid M S m : S) = 1 := by
  convert! mul_toInvSubmonoid M S m
  ext
  rw [← Algebra.smul_def]
  rfl

variable {S}

-- `surj'` was taken, so use `surj''` instead
-- TODO: this can be fixed after the deprecations of 2025-09-04 are removed.
/--
theorem `surj''` / 定理 `surj''`

English:
theorem surj''
  given: (z : S)
  statement: exists (r : R) (m : M), z = r • (toInvSubmonoid M S m : S)
  proof: by
  rcases IsLocalization.surj M z with ⟨⟨r, m⟩, e : z * _ = algebraMap R S r⟩
  refine ⟨r, m, ?_⟩
  rw [Algebra.smul_def]; rw [← e]; rw [mul_assoc]
  simp

中文:
定理 surj''
  条件: (z : S)
  结论: 存在 (r : R) (m : M), z = r • (toInvSubmonoid M S m : S)
  证明: by
  rcases IsLocalization.surj M z with ⟨⟨r, m⟩, e : z * _ = algebraMap R S r⟩
  refine ⟨r, m, ?_⟩
  rw [Algebra.smul_def]; rw [← e]; rw [mul_assoc]
  simp

Depends on / 依赖: Algebra, Algebra.smul_def, IsLocalization, IsLocalization.surj, algebraMap, mul_assoc, smul_def
-/
theorem surj'' (z : S) : exists (r : R) (m : M), z = r • (toInvSubmonoid M S m : S) := by
  rcases IsLocalization.surj M z with ⟨⟨r, m⟩, e : z * _ = algebraMap R S r⟩
  refine ⟨r, m, ?_⟩
  rw [Algebra.smul_def]; rw [← e]; rw [mul_assoc]
  simp

/--
theorem `toInvSubmonoid_eq_mk'` / 定理 `toInvSubmonoid_eq_mk'`

English:
theorem toInvSubmonoid_eq_mk'
  given: (x : M)
  statement: (toInvSubmonoid M S x : S) = mk' S 1 x
  proof: by
  rw [← (IsLocalization.map_units S x).mul_left_inj]
  simp

中文:
定理 toInvSubmonoid_eq_mk'
  条件: (x : M)
  结论: (toInvSubmonoid M S x : S) = mk' S 1 x
  证明: by
  rw [← (IsLocalization.map_units S x).mul_left_inj]
  simp

Depends on / 依赖: IsLocalization, IsLocalization.map_units, map_units, mul_left_inj
-/
theorem toInvSubmonoid_eq_mk' (x : M) : (toInvSubmonoid M S x : S) = mk' S 1 x := by
  rw [← (IsLocalization.map_units S x).mul_left_inj]
  simp

/--
theorem `mem_invSubmonoid_iff_exists_mk'` / 定理 `mem_invSubmonoid_iff_exists_mk'`

English:
theorem mem_invSubmonoid_iff_exists_mk'
  given: (x : S)
  proof: by
  simp_rw [← toInvSubmonoid_eq_mk']
  exact ⟨fun h => ⟨_, congr_arg Subtype.val (toInvSubmonoid_surjective M S ⟨x, h⟩).choose_spec⟩,
    fun h => h.choose_spec ▸ (toInvSubmonoid M S h.choose).prop⟩

中文:
定理 mem_invSubmonoid_iff_exists_mk'
  条件: (x : S)
  证明: by
  simp_rw [← toInvSubmonoid_eq_mk']
  exact ⟨fun h => ⟨_, congr_arg Subtype.val (toInvSubmonoid_surjective M S ⟨x, h⟩).choose_spec⟩,
    fun h => h.choose_spec ▸ (toInvSubmonoid M S h.choose).prop⟩

Depends on / 依赖: Subtype, Subtype.val, choose_spec, congr_arg, h.choose, h.choose_spec, simp_rw, toInvSubmonoid, toInvSubmonoid_eq_mk, toInvSubmonoid_surjective
-/
theorem mem_invSubmonoid_iff_exists_mk' (x : S) :
    x in invSubmonoid M S ↔ exists m : M, mk' S 1 m = x := by
  simp_rw [← toInvSubmonoid_eq_mk']
  exact ⟨fun h => ⟨_, congr_arg Subtype.val (toInvSubmonoid_surjective M S ⟨x, h⟩).choose_spec⟩,
    fun h => h.choose_spec ▸ (toInvSubmonoid M S h.choose).prop⟩

variable (S)

/--
theorem `span_invSubmonoid` / 定理 `span_invSubmonoid`

English:
theorem span_invSubmonoid
  statement: Submodule.span R (invSubmonoid M S : Set S) = ⊤
  proof: by
  rw [eq_top_iff]
  rintro x -
  rcases IsLocalization.surj'' M x with ⟨r, m, rfl⟩
  exact Submodule.smul_mem _ _ (Submodule.subset_span (toInvSubmonoid M S m).prop)

中文:
定理 span_invSubmonoid
  结论: Submodule.span R (invSubmonoid M S : Set S) = ⊤
  证明: by
  rw [eq_top_iff]
  rintro x -
  rcases IsLocalization.surj'' M x with ⟨r, m, rfl⟩
  exact Submodule.smul_mem _ _ (Submodule.subset_span (toInvSubmonoid M S m).prop)

Depends on / 依赖: IsLocalization, IsLocalization.surj, Submodule, Submodule.smul_mem, Submodule.subset_span, eq_top_iff, smul_mem, subset_span, toInvSubmonoid
-/
theorem span_invSubmonoid : Submodule.span R (invSubmonoid M S : Set S) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  rcases IsLocalization.surj'' M x with ⟨r, m, rfl⟩
  exact Submodule.smul_mem _ _ (Submodule.subset_span (toInvSubmonoid M S m).prop)

/--
theorem `finiteType_of_monoid_fg` / 定理 `finiteType_of_monoid_fg`

English:
theorem finiteType_of_monoid_fg
  given: [Monoid.FG M]
  statement: Algebra.FiniteType R S
  proof: by
  have := Monoid.fg_of_surjective _ (toInvSubmonoid_surjective M S)
  rw [Monoid.fg_iff_submonoid_fg] at this
  rcases this with ⟨s, hs⟩
  refine ⟨⟨s, ?_⟩⟩
  rw [eq_top_iff]
  rintro x -
  change x in (Subalgebra.toSubmodule (Algebra.adjoin R _ : Subalgebra R S) : Set S)
  rw [Algebra.adjoin_eq_s

中文:
定理 finiteType_of_monoid_fg
  条件: [Monoid.FG M]
  结论: Algebra.FiniteType R S
  证明: by
  have := Monoid.fg_of_surjective _ (toInvSubmonoid_surjective M S)
  rw [Monoid.fg_iff_submonoid_fg] at this
  rcases this with ⟨s, hs⟩
  refine ⟨⟨s, ?_⟩⟩
  rw [eq_top_iff]
  rintro x -
  change x in (Subalgebra.toSubmodule (Algebra.adjoin R _ : Subalgebra R S) : Set S)
  rw [Algebra.adjoin_eq_s

Depends on / 依赖: Algebra, Algebra.adjoin, Algebra.adjoin_eq_span, Monoid, Monoid.fg_iff_submonoid_fg, Monoid.fg_of_surjective, Subalgebra, Subalgebra.toSubmodule, adjoin, adjoin_eq_span, eq_top_iff, fg_iff_submonoid_fg, fg_of_surjective, span_invSubmonoid, toInvSubmonoid_surjective, toSubmodule
-/
theorem finiteType_of_monoid_fg [Monoid.FG M] : Algebra.FiniteType R S := by
  have := Monoid.fg_of_surjective _ (toInvSubmonoid_surjective M S)
  rw [Monoid.fg_iff_submonoid_fg] at this
  rcases this with ⟨s, hs⟩
  refine ⟨⟨s, ?_⟩⟩
  rw [eq_top_iff]
  rintro x -
  change x in (Subalgebra.toSubmodule (Algebra.adjoin R _ : Subalgebra R S) : Set S)
  rw [Algebra.adjoin_eq_span]; rw [hs]; rw [span_invSubmonoid]
  trivial

instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (M : Submonoid S) [Monoid.FG M] : Algebra.FiniteType R (Localization M) :=
  .trans ‹_› (IsLocalization.finiteType_of_monoid_fg M _)

end InvSubmonoid

end IsLocalization
